//--------------------------------------------------------------------//
//--- deadstores: find redundant loads/stores.           ds_main.c ---//
//--------------------------------------------------------------------//

/*
   Copyright (C) 2020 Krister Walfridsson
      krister.walfridsson@gmail.com

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
   02111-1307, USA.

   The GNU General Public License is contained in the file COPYING.
*/

#include "pub_tool_basics.h"
#include "pub_tool_clientstate.h"
#include "pub_tool_hashtable.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_machine.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_options.h"
#include "pub_tool_replacemalloc.h"
#include "pub_tool_stacktrace.h"
#include "pub_tool_threadstate.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_vki.h"


//------------------------------------------------------------//
//--- Command line args                                    ---//
//------------------------------------------------------------//

static Bool use_stack_trace = False;
static const HChar *deadstores_out_file = "deadstores.out.%p";
static HChar *cmd_line;

static Bool ds_process_cmd_line_options(const HChar *arg)
{
  if VG_BOOL_CLO(arg, "--use-stack-trace", use_stack_trace) {
    return True;
  }
  if VG_STR_CLO(arg, "--deadstores-out-file", deadstores_out_file) {
    return True;
  }
  return False;
}

static void ds_print_usage(void)
{
   VG_(printf)(
"    --use-stack-trace=yes|no      capture load/store stack traces [no]\n"
"    --deadstores-out-file=<file>  output file name [deadstores.out.%%p]\n"
   );
}

static void ds_print_debug_usage(void)
{  
   VG_(printf)("    (none)\n");
}

// Copy the client command line (as it may change during run time).
static void save_cmd_line(void)
{
  SizeT size = VG_(strlen)(VG_(args_the_exename));
  for (Word i = 0; i < VG_(sizeXA)(VG_(args_for_client)); i++) {
    size += 1;
    size += VG_(strlen)(*(HChar**)VG_(indexXA)(VG_(args_for_client), i));
  }

  cmd_line = VG_(malloc)("cmd_line", size + 1);

  size = VG_(sprintf)(cmd_line, "%s", VG_(args_the_exename));
  for (Word i = 0; i < VG_(sizeXA)(VG_(args_for_client)); i++) {
    size += VG_(sprintf)(cmd_line + size, " %s",
                         *(HChar**)VG_(indexXA)(VG_(args_for_client), i));
  }
  cmd_line[size] = '\0';
}


//------------------------------------------------------------//
//--- Tracking of the load/store instructions' status         //
//------------------------------------------------------------//

// The usage of each load/store instruction is tracked in a
// node structure. These are organized as a red-black tree
// key:ed on the instruction's address (or by the stack trace
// at the instruction's execution in case the user has requested
// --use-stack-trace=yes).

#define NOF_STACK_TRACE_IPS 5

enum color { BLACK, RED };

struct key {
  UInt nof_ips;
  Addr ips[NOF_STACK_TRACE_IPS];
};

typedef unsigned handle;

struct node {
  handle parent;
  handle left;
  handle right;
  enum color color;
  struct key key;

  // Store
  Long bytes_written;
  Long bytes_read;
  Long nof_stores;
  Long nof_silent_stores;

  // Load
  Long nof_loads;
  Long nof_silent_loads;
};

static struct node *nodes = NULL;
static handle tree_root = 0;

// We limit the number of tracked load/store instructions so that
// we can store all info about an address in 32 bits.
#define MAX_HANDLE 0x7fffffff

// The number of nodes that fit in the currently allocated space.
static Long max_nodes = 0;

// Number of nodes
static Long nof_nodes = 0;

#define INITIAL_TREE_SIZE 100000

static void init_tree(void)
{
  tl_assert(nodes == NULL);
  max_nodes = INITIAL_TREE_SIZE;
  nodes = VG_(malloc)("nodes", max_nodes * sizeof(*nodes));
  VG_(memset)(nodes, 0, max_nodes * sizeof(*nodes));

  // The read-black tree is using the first node as a NIL element.
  nodes[0].color = BLACK;
  nof_nodes = 1;
}

static Int compare_key(struct key *key1, struct key *key2)
{
  UInt min_nof_ips =
      key1->nof_ips < key2->nof_ips ? key1->nof_ips : key2->nof_ips;
  for (UInt i = 0; i < min_nof_ips; i++) {
    if (key1->ips[i] < key2->ips[i])
      return -1;
    if (key1->ips[i] > key2->ips[i])
      return 1;
  }

  if (key1->nof_ips < key2->nof_ips)
    return -1;
  if (key1->nof_ips > key2->nof_ips)
    return 1;
  return 0;
}

static void left_rotate(handle x)
{
  tl_assert(nodes[x].right != 0);
  handle y = nodes[x].right;
  nodes[x].right = nodes[y].left;
  if (nodes[y].left != 0) {
    nodes[nodes[y].left].parent = x;
  }
  nodes[y].parent = nodes[x].parent;
  if (nodes[x].parent == 0) {
    tree_root = y;
  } else {
    if (x == nodes[nodes[x].parent].left) {
      nodes[nodes[x].parent].left = y;
    } else {
      nodes[nodes[x].parent].right = y;
    }
  }
  nodes[y].left = x;
  nodes[x].parent = y;
}

static void right_rotate(handle x)
{
  tl_assert(nodes[x].left != 0);
  handle y = nodes[x].left;
  nodes[x].left = nodes[y].right;
  if (nodes[y].right != 0) {
    nodes[nodes[y].right].parent = x;
  }
  nodes[y].parent = nodes[x].parent;
  if (nodes[x].parent == 0) {
    tree_root = y;
  } else {
    if (x == nodes[nodes[x].parent].right) {
      nodes[nodes[x].parent].right = y;
    } else {
      nodes[nodes[x].parent].left = y;
    }
  }
  nodes[y].right = x;
  nodes[x].parent = y;
}

static void tree_insert(handle z)
{
  handle y = 0;
  handle x = tree_root;
  while (x != 0) {
    y = x;
    Int c = compare_key(&nodes[z].key, &nodes[x].key);
    tl_assert(c != 0);
    if (c < 0)
      x = nodes[x].left;
    else
      x = nodes[x].right;
  }
  nodes[z].parent = y;
  if (y == 0) {
    tree_root = z;
  } else {
    Int c = compare_key(&nodes[z].key, &nodes[y].key);
    if (c < 0)
      nodes[y].left = z;
    else
      nodes[y].right = z;
  }
}

static handle new_node(struct key key)
{
  if (max_nodes == nof_nodes) {
    max_nodes = max_nodes * 2;
    nodes = VG_(realloc("nodes", nodes, max_nodes * sizeof(*nodes)));
    VG_(memset)(&nodes[nof_nodes], 0, (max_nodes - nof_nodes) * sizeof(*nodes));
  }

  handle new_handle = nof_nodes++;
  nodes[new_handle].parent = 0;
  nodes[new_handle].left = 0;
  nodes[new_handle].right = 0;
  nodes[new_handle].color = RED;
  nodes[new_handle].key = key;

  handle x = new_handle;
  tree_insert(x);

  while (x != tree_root && nodes[nodes[x].parent].color == RED) {
    if (nodes[x].parent == nodes[nodes[nodes[x].parent].parent].left) {
      handle y = nodes[nodes[nodes[x].parent].parent].right;
      if (nodes[y].color == RED) {
        nodes[nodes[x].parent].color = BLACK;
        nodes[y].color = BLACK;
        nodes[nodes[nodes[x].parent].parent].color = RED;
        x = nodes[nodes[x].parent].parent;
      } else {
        if (x == nodes[nodes[x].parent].right) {
          x = nodes[x].parent;
          left_rotate(x);
        }
        nodes[nodes[x].parent].color = BLACK;
        nodes[nodes[nodes[x].parent].parent].color = RED;
        right_rotate(nodes[nodes[x].parent].parent);
      }
    } else {
      handle y = nodes[nodes[nodes[x].parent].parent].left;
      if (nodes[y].color == RED) {
        nodes[nodes[x].parent].color = BLACK;
        nodes[y].color = BLACK;
        nodes[nodes[nodes[x].parent].parent].color = RED;
        x = nodes[nodes[x].parent].parent;
      } else {
        if (x == nodes[nodes[x].parent].left) {
          x = nodes[x].parent;
          right_rotate(x);
        }
        nodes[nodes[x].parent].color = BLACK;
        nodes[nodes[nodes[x].parent].parent].color = RED;
        left_rotate(nodes[nodes[x].parent].parent);
      }
    }
  }
  nodes[tree_root].color = BLACK;

  // Verify that the NIL element has not been modified.
  tl_assert(nodes[0].color == BLACK);
  tl_assert(nodes[0].parent == 0);
  tl_assert(nodes[0].left == 0);
  tl_assert(nodes[0].right == 0);

  return new_handle;
}

static handle find_node(struct key *key)
{
  handle current = tree_root;
  while (current != 0) {
    Int c = compare_key(key, &nodes[current].key);
    if (c == 0)
      return current;
    if (c < 0) {
      current = nodes[current].left;
    } else {
      current = nodes[current].right;
    }
  }
  return 0;
}

static handle iaddr2handle(ThreadId tid, Addr iaddr)
{
  struct key k;
  k.nof_ips = 1;
  if (use_stack_trace) {
    k.nof_ips =
        VG_(get_StackTrace)(tid, k.ips, NOF_STACK_TRACE_IPS, NULL, NULL, 0);
  }

  // Use the original address for the program counter -- JIT optimization
  // may have made the current value slightly different when instructions
  // have been merged.
  k.ips[0] = iaddr;

  tl_assert(k.nof_ips >= 1);
  handle h = find_node(&k);
  if (h == 0) {
    h = new_node(k);
  }

  if (h > MAX_HANDLE) {
    VG_(tool_panic)("Too many load/store instructions\n");
  }

  return h;
}


//------------------------------------------------------------//
//--- Tracking of memory status                            ---//
//------------------------------------------------------------//

// We track the status of each byte in order to detect dead and
//  silent stores:
// - If this byte has been written
//   If it has been written, then we should check if the
//   following store instruction writes the same value.
// - A handle to the last store instruction writing it
//   This is set to 0 when the byte is read (as the store
//   is then not dead).
// The status is reset when the memory is free:ed, etc.
struct addr_info {
  unsigned store_instr_h : 31;
  unsigned is_written : 1;
};

// We allocate the addr_info in blocks of BLOCK_SIZE addresses.
#define BLOCK_SIZE ((Addr)(1 << 20))

struct addr_info_block {
  // Note: This must match VgHashNode from pub_tool_hashteble.h
  struct addr_info_block *next;
  Addr key;

  // Payload
  struct addr_info ai[BLOCK_SIZE];
};

static VgHashTable *addr_info_table = NULL;

static void init_addr_info(void)
{
  addr_info_table = VG_(HT_construct)("addr_info_table");
}

static struct addr_info *addr2addr_info(Addr addr)
{
  Addr key = addr & ~(BLOCK_SIZE - 1);
  struct addr_info_block *pi = VG_(HT_lookup)(addr_info_table, key);
  if (pi == NULL) {
    pi = VG_(malloc)("addr_info_block", sizeof(struct addr_info_block));
    VG_(memset)(pi, 0, sizeof(*pi));
    pi->key = key;
    VG_(HT_add_node)(addr_info_table, pi);
  }
  return &pi->ai[addr & (BLOCK_SIZE - 1)];
}

static void mark_read(Addr addr, SizeT size)
{
  for (SizeT i = 0; i < size; i++) {
    struct addr_info *ai = addr2addr_info(addr + i);
    if (ai->store_instr_h != 0) {
      tl_assert(nodes[ai->store_instr_h].bytes_written != 0);
      nodes[ai->store_instr_h].bytes_read++;
      ai->store_instr_h = 0;
    }
  }
}

static void mark_invalid(Addr addr, SizeT size)
{
  for (SizeT i = 0; i < size; i++) {
    struct addr_info *ai = addr2addr_info(addr + i);
    ai->store_instr_h = 0;
    ai->is_written = False;
  }
}

static void mark_written(Addr addr, SizeT size, handle h)
{
  for (SizeT i = 0; i < size; i++) {
    struct addr_info *ai = addr2addr_info(addr + i);
    ai->store_instr_h = h;
    ai->is_written = True;
  }
}


//------------------------------------------------------------//
//--- Instrumentation                                      ---//
//------------------------------------------------------------//

#ifdef VG_LITTLEENDIAN
#define ENDIAN Iend_LE
#else
#define ENDIAN Iend_BE
#endif

static VG_REGPARM(3) void load_tracker(Addr addr, SizeT size, Addr iaddr)
{
  SizeT silent_load = 0;
  for (SizeT i = 0; i < size; i++) {
    struct addr_info *ai = addr2addr_info(addr + i);
    if (ai->store_instr_h != 0) {
      tl_assert(nodes[ai->store_instr_h].bytes_written != 0);
      nodes[ai->store_instr_h].bytes_read++;
      ai->store_instr_h = 0;
    } else if (ai->is_written) {
      silent_load += 1;
    }
  }

  if (iaddr != 0) {
    ThreadId tid = VG_(get_running_tid)();
    handle h = iaddr2handle(tid, iaddr);
    nodes[h].nof_loads += 1;
    if (silent_load == size) {
      nodes[h].nof_silent_loads += 1;
    }
  }
}

static VG_REGPARM(3) void dead_store_tracker(Addr addr, SizeT size, Addr iaddr)
{
  ThreadId tid = VG_(get_running_tid)();
#if defined(VGA_x86) || defined(VGA_amd64)
  // Valgrind emulates "bt reg, reg" by subtracting 288 from the stack
  // pointer, writing the register to the stack, reading back one byte
  // of the value, and restoring the stack pointer. This makes us
  // incorrectly report dead stores...
  // But programs do in general not write to 0(%RSP), so we can just
  // ignore such writes.
  Addr sp = VG_(get_SP(tid));
  if (sp == addr) {
    mark_invalid(addr, size);
    return;
  }
#endif
  handle h = 0;
  if (iaddr != 0) {
    h = iaddr2handle(tid, iaddr);
    nodes[h].bytes_written += size;
    nodes[h].nof_stores += 1;
  }
  mark_written(addr, size, h);
}

static VG_REGPARM(3) void silent_store_tracker(Addr addr, SizeT size,
                                               Addr iaddr)
{
  tl_assert(iaddr != 0);
  Bool is_written = True;
  for (SizeT i = 0; i < size; i++) {
    struct addr_info *ai = addr2addr_info(addr + i);
    is_written = is_written && ai->is_written;
  }
  if (is_written) {
    ThreadId tid = VG_(get_running_tid)();
    handle h = iaddr2handle(tid, iaddr);
    nodes[h].nof_silent_stores += 1;
  }
}

static IRExpr *emit_unop(IRSB *sb, IROp op_code, IRExpr *arg)
{
  IRType resultType;
  IRType argTypes[4];
  typeOfPrimop(op_code, &resultType, &(argTypes[0]), &(argTypes[1]),
               &(argTypes[2]), &(argTypes[3]));
  IRTemp result = newIRTemp(sb->tyenv, resultType);
  addStmtToIRSB(sb, IRStmt_WrTmp(result, IRExpr_Unop(op_code, arg)));
  return IRExpr_RdTmp(result);
}

static IRExpr *emit_binop(IRSB *sb, IROp op_code, IRExpr *arg1, IRExpr *arg2)
{
  IRType resultType;
  IRType argTypes[4];
  typeOfPrimop(op_code, &resultType, &(argTypes[0]), &(argTypes[1]),
               &(argTypes[2]), &(argTypes[3]));
  IRTemp result = newIRTemp(sb->tyenv, resultType);
  addStmtToIRSB(sb, IRStmt_WrTmp(result, IRExpr_Binop(op_code, arg1, arg2)));
  return IRExpr_RdTmp(result);
}

static IRExpr *emit_load(IRSB *sb, IRType ty, IRExpr *addr)
{
  IRTemp dest = newIRTemp(sb->tyenv, ty);
  addStmtToIRSB(sb, IRStmt_WrTmp(dest, IRExpr_Load(ENDIAN, ty, addr)));
  return IRExpr_RdTmp(dest);
}

static IRExpr *emit_and1(IRSB *sb, IRExpr *arg1, IRExpr *arg2)
{
  // There does not seem to be any way to 'and' two 1-bit values, so
  // we extend them to a wider type and use a normal 'bitwise and'.
  IRExpr *zext1 = emit_unop(sb, Iop_1Uto32, arg1);
  IRExpr *zext2 = emit_unop(sb, Iop_1Uto32, arg2);
  IRExpr *and32 = emit_binop(sb, Iop_And32, zext1, zext2);
  return emit_unop(sb, Iop_32to1, and32);
}

static IRExpr *emit_cmpEQ128(IRSB *sb, IRExpr *arg1, IRExpr *arg2)
{
  // Compare high part.
  IRExpr *arg1_hi = emit_unop(sb, Iop_V128HIto64, arg1);
  IRExpr *arg2_hi = emit_unop(sb, Iop_V128HIto64, arg2);
  IRExpr *cmp_hi = emit_binop(sb, Iop_CmpEQ64, arg1_hi, arg2_hi);

  // Compare low part.
  IRExpr *arg1_lo = emit_unop(sb, Iop_V128to64, arg1);
  IRExpr *arg2_lo = emit_unop(sb, Iop_V128to64, arg2);
  IRExpr *cmp_lo = emit_binop(sb, Iop_CmpEQ64, arg1_lo, arg2_lo);

  // Combine the result.
  return emit_and1(sb, cmp_hi, cmp_lo);
}

static IRExpr *emit_cmpEQ256(IRSB *sb, IRExpr *arg1, IRExpr *arg2)
{
  // Compare high part.
  IRExpr *arg1_hi = emit_unop(sb, Iop_V256toV128_1, arg1);
  IRExpr *arg2_hi = emit_unop(sb, Iop_V256toV128_1, arg2);
  IRExpr *cmp_hi = emit_cmpEQ128(sb, arg1_hi, arg2_hi);

  // Compare low part.
  IRExpr *arg1_lo = emit_unop(sb, Iop_V256toV128_0, arg1);
  IRExpr *arg2_lo = emit_unop(sb, Iop_V256toV128_0, arg2);
  IRExpr *cmp_lo = emit_cmpEQ128(sb, arg1_lo, arg2_lo);

  // Combine the result.
  return emit_and1(sb, cmp_hi, cmp_lo);
}

static void emit_silent_store_instrumentation(IRSB *sb, IRExpr *addr,
                                              IRType type, IRExpr *data,
                                              IRExpr *orig_guard, Addr iaddr)
{
  IRExpr *guard;
  switch (type) {
  case Ity_I8: {
    IRExpr *load = emit_load(sb, type, addr);
    guard = emit_binop(sb, Iop_CmpEQ8, data, load);
  } break;
  case Ity_I16: {
    IRExpr *load = emit_load(sb, type, addr);
    guard = emit_binop(sb, Iop_CmpEQ16, data, load);
  } break;
  case Ity_I32: {
    IRExpr *load = emit_load(sb, type, addr);
    guard = emit_binop(sb, Iop_CmpEQ32, data, load);
  } break;
  case Ity_I64: {
    IRExpr *load = emit_load(sb, type, addr);
    guard = emit_binop(sb, Iop_CmpEQ64, data, load);
  } break;

  case Ity_V128: {
    IRExpr *load = emit_load(sb, type, addr);
    guard = emit_cmpEQ128(sb, data, load);
  } break;

  case Ity_V256: {
    IRExpr *load = emit_load(sb, type, addr);
    guard = emit_cmpEQ256(sb, data, load);
  } break;

  default:
    VG_(message)
    (Vg_DebugMsg, "warning: Cannot track silent stores to type 0x%x\n",
     (unsigned)type);
    return;
  }

  if (orig_guard != NULL) {
    guard = emit_and1(sb, guard, orig_guard);
  }

  tl_assert(isIRAtom(addr));
  IRExpr **argv = mkIRExprVec_3(addr, mkIRExpr_HWord(sizeofIRType(type)),
                                mkIRExpr_HWord(iaddr));
  IRDirty *di =
      unsafeIRDirty_0_N(3, "silent_store_tracker",
                        VG_(fnptr_to_fnentry)(silent_store_tracker), argv);
  di->guard = guard;
  di->mFx = Ifx_Read;
  di->mAddr = addr;
  di->mSize = sizeofIRType(type);
  addStmtToIRSB(sb, IRStmt_Dirty(di));
}

static void emit_dead_store_instrumentation(IRSB *sb, IRExpr *addr, Int size,
                                            IRExpr *guard, Addr iaddr,
                                            const VexGuestLayout *layout)
{
  IRExpr **argv =
      mkIRExprVec_3(addr, mkIRExpr_HWord(size), mkIRExpr_HWord(iaddr));
  IRDirty *di =
      unsafeIRDirty_0_N(3, "dead_store_tracker",
                        VG_(fnptr_to_fnentry)(dead_store_tracker), argv);
  if (guard != NULL)
    di->guard = guard;
#if defined(VGA_x86) || defined(VGA_amd64)
  di->nFxState = 1;
  di->fxState[0].fx = Ifx_Read;
  di->fxState[0].offset = layout->offset_SP;
  di->fxState[0].size = layout->sizeof_SP;
  di->fxState[0].nRepeats = 0;
  di->fxState[0].repeatLen = 0;
#endif
  addStmtToIRSB(sb, IRStmt_Dirty(di));
}

static void emit_store_instrumentation(IRSB *sb, IRExpr *addr, IRType type,
                                       IRExpr *data, IRExpr *guard, Addr iaddr,
                                       const VexGuestLayout *layout)
{
  emit_silent_store_instrumentation(sb, addr, type, data, guard, iaddr);
  emit_dead_store_instrumentation(sb, addr, sizeofIRType(type), guard, iaddr,
                                  layout);
}

static void emit_load_instrumentation(IRSB *sb, IRExpr *addr, Int size,
                                      IRExpr *guard, Addr iaddr)
{
  IRExpr **argv =
      mkIRExprVec_3(addr, mkIRExpr_HWord(size), mkIRExpr_HWord(iaddr));
  IRDirty *di = unsafeIRDirty_0_N(3, "load_tracker",
                                  VG_(fnptr_to_fnentry)(load_tracker), argv);
  if (guard != NULL)
    di->guard = guard;
  addStmtToIRSB(sb, IRStmt_Dirty(di));
}

static IRSB *ds_instrument(VgCallbackClosure *closure, IRSB *sbIn,
                           const VexGuestLayout *layout,
                           const VexGuestExtents *vge,
                           const VexArchInfo *archinfo_host, IRType gWordTy,
                           IRType hWordTy)
{
  if (gWordTy != hWordTy) {
    // We don't support this case.
    VG_(tool_panic)("host/guest word size mismatch");
  }

  // Set up SB
  IRSB *sbOut = deepCopyIRSBExceptStmts(sbIn);

  // Copy verbatim any IR preamble preceding the first IMark
  Int i = 0;
  while (i < sbIn->stmts_used && sbIn->stmts[i]->tag != Ist_IMark) {
    addStmtToIRSB(sbOut, sbIn->stmts[i]);
    i++;
  }

  IRTypeEnv *tyenv = sbIn->tyenv;
  Addr current_instr_addr = 0;
  for (; i < sbIn->stmts_used; i++) {
    IRStmt *st = sbIn->stmts[i];
    if (!st)
      continue;

    switch (st->tag) {
    case Ist_NoOp:
      break;

    case Ist_AbiHint:
    case Ist_Put:
    case Ist_PutI:
    case Ist_MBE:
    case Ist_Exit:
      addStmtToIRSB(sbOut, st);
      break;

    case Ist_IMark:
      current_instr_addr = st->Ist.IMark.addr;
      addStmtToIRSB(sbOut, st);
      break;

    case Ist_WrTmp: {
      IRExpr *data = st->Ist.WrTmp.data;
      if (data->tag == Iex_Load) {
        emit_load_instrumentation(sbOut, data->Iex.Load.addr,
                                  sizeofIRType(data->Iex.Load.ty), NULL,
                                  current_instr_addr);
      }
      addStmtToIRSB(sbOut, st);
      break;
    }

    case Ist_Store: {
      IRExpr *data = st->Ist.Store.data;
      IRType type = typeOfIRExpr(tyenv, data);
      tl_assert(type != Ity_INVALID);
      emit_store_instrumentation(sbOut, st->Ist.Store.addr, type, data, NULL,
                                 current_instr_addr, layout);
      addStmtToIRSB(sbOut, st);
      break;
    }

    case Ist_StoreG: {
      IRStoreG *sg = st->Ist.StoreG.details;
      IRExpr *data = sg->data;
      IRType type = typeOfIRExpr(tyenv, data);
      tl_assert(type != Ity_INVALID);
      emit_store_instrumentation(sbOut, st->Ist.Store.addr, type, data,
                                 sg->guard, current_instr_addr, layout);
      addStmtToIRSB(sbOut, st);
      break;
    }

    case Ist_LoadG: {
      IRLoadG *lg = st->Ist.LoadG.details;
      IRType type = Ity_INVALID;     // Loaded type
      IRType typeWide = Ity_INVALID; // After implicit widening
      typeOfIRLoadGOp(lg->cvt, &typeWide, &type);
      tl_assert(type != Ity_INVALID);
      emit_load_instrumentation(sbOut, lg->addr, sizeofIRType(type), lg->guard,
                                current_instr_addr);
      addStmtToIRSB(sbOut, st);
      break;
    }

    case Ist_Dirty: {
      // Dirty calls are only used for some functionality (such as
      // managing loading of shared libraries) that is not relevant
      // for the dead/silent load/store tracking. We just mark the
      // memory range as read/written in order to eliminate noise
      // from other stores to that range that may incorrectly be
      // marked as used/unused.
      IRDirty *d = st->Ist.Dirty.details;
      if (d->mFx != Ifx_None) {
        tl_assert(d->mAddr != NULL);
        tl_assert(d->mSize != 0);
        if (d->mFx == Ifx_Read || d->mFx == Ifx_Modify) {
          emit_load_instrumentation(sbOut, d->mAddr, d->mSize, d->guard, 0);
        }
        if (d->mFx == Ifx_Write || d->mFx == Ifx_Modify) {
          emit_dead_store_instrumentation(sbOut, d->mAddr, d->mSize, d->guard,
                                          0, layout);
        }
      }

      addStmtToIRSB(sbOut, st);
      break;
    }

    case Ist_CAS: {
      // Atomic compare-and-swap operations are not relevant for
      // the dead/silent load/store tracking. We just mark the
      // memory range as read in order to eliminate noise from
      // stores to that range that may look unused.
      IRCAS *cas = st->Ist.CAS.details;
      tl_assert(cas->addr != NULL);
      tl_assert(cas->dataLo != NULL);
      IRType dataTy = typeOfIRExpr(tyenv, cas->dataLo);
      Int dataSize = sizeofIRType(dataTy);
      if (cas->dataHi != NULL)
        dataSize *= 2; // Since it's a double-word CAS.
      emit_load_instrumentation(sbOut, cas->addr, dataSize, NULL, 0);

      addStmtToIRSB(sbOut, st);
      break;
    }

    case Ist_LLSC: {
      if (st->Ist.LLSC.storedata == NULL) {
        IRType dataTy = typeOfIRTemp(tyenv, st->Ist.LLSC.result);
        emit_load_instrumentation(sbOut, st->Ist.LLSC.addr,
                                  sizeofIRType(dataTy), NULL,
                                  current_instr_addr);
      } else {
        IRType dataTy = typeOfIRExpr(tyenv, st->Ist.LLSC.storedata);
        emit_store_instrumentation(sbOut, st->Ist.LLSC.addr, dataTy,
                                   st->Ist.LLSC.storedata, NULL,
                                   current_instr_addr, layout);
      }
      addStmtToIRSB(sbOut, st);
      break;
    }

    default:
      ppIRStmt(st);
      tl_assert(0);
    }
  }

  return sbOut;
}

static void ds_new_mem_stack(Addr addr, SizeT size)
{
  mark_invalid(addr, size);
}

static void ds_die_mem_stack(Addr addr, SizeT size)
{
  mark_invalid(addr, size);
}

static void ds_pre_mem_read(CorePart part, ThreadId tid, const HChar *s,
                            Addr addr, SizeT size)
{
  mark_read(addr, size);
}

static void ds_post_mem_write(CorePart part, ThreadId tid, Addr addr,
                              SizeT size)
{
  handle h = iaddr2handle(tid, VG_(get_IP(tid)));
  nodes[h].bytes_written += size;
  nodes[h].nof_stores += 1;
  mark_written(addr, size, h);
}


//------------------------------------------------------------//
//--- malloc() et al. replacement wrappers                 ---//
//------------------------------------------------------------//

static SizeT ds_malloc_usable_size(ThreadId tid, void *p)
{
  return VG_(cli_malloc_usable_size)(p);
}

static void *ds_memalign(ThreadId tid, SizeT alignment, SizeT size)
{
  void *p = VG_(cli_malloc)(alignment, size);
  if (!p) {
    return NULL;
  }

  // Mark the address range as not written.
  mark_invalid((Addr)p, size);

  return p;
}

static void *ds_malloc(ThreadId tid, SizeT size)
{
  return ds_memalign(tid, VG_(clo_alignment), size);
}

static void *ds___builtin_new(ThreadId tid, SizeT size)
{
  return ds_memalign(tid, VG_(clo_alignment), size);
}

static void *ds___builtin_vec_new(ThreadId tid, SizeT size)
{
  return ds_memalign(tid, VG_(clo_alignment), size);
}

static void *ds_calloc(ThreadId tid, SizeT nmemb, SizeT size)
{
  SizeT real_size = nmemb * size;
  void *p = ds_memalign(tid, VG_(clo_alignment), real_size);
  if (!p) {
    return NULL;
  }
  VG_(memset)(p, 0, real_size);

  // The memory is cleared -- mark it as written.
  handle h = iaddr2handle(tid, VG_(get_IP(tid)));
  nodes[h].bytes_written += real_size;
  nodes[h].nof_stores += 1;
  mark_written((Addr)p, real_size, h);

  return p;
}

static void ds_free(ThreadId tid, void *p)
{
  mark_invalid((Addr)p, ds_malloc_usable_size(tid, p));
  VG_(cli_free)(p);
}

static void ds___builtin_delete(ThreadId tid, void *p)
{
  ds_free(tid, p);
}

static void ds___builtin_vec_delete(ThreadId tid, void *p)
{
  ds_free(tid, p);
}

static void *ds_realloc(ThreadId tid, void *p_old, SizeT size_new)
{
  SizeT old_usable_size = ds_malloc_usable_size(tid, p_old);
  if (old_usable_size >= size_new) {
    // Mark the address range after the new size as not written.
    // We need to do this in order to get the correct validity
    // for cases such as
    //    p = malloc(100);
    //    memset(p, 0, 100);
    //    p = realloc(p, 10);
    //    p = realloc(p, 50);
    // that otherwise would have the bytes p[10], ... , p[49]
    // marked as valid.
    mark_invalid(((Addr)p_old) + size_new, old_usable_size - size_new);

    return p_old;
  }

  void *p_new = ds_memalign(tid, VG_(clo_alignment), size_new);
  if (!p_new) {
    return NULL;
  }
  VG_(memcpy)(p_new, p_old, old_usable_size);

  // Copy the status of the individual bytes to the new place.
  Addr addr_old = (Addr)p_old;
  Addr addr_new = (Addr)p_new;
  for (SizeT i = size_new; i < old_usable_size; i++) {
    struct addr_info *ai_old = addr2addr_info(addr_old + i);
    struct addr_info *ai_new = addr2addr_info(addr_new + i);
    *ai_new = *ai_old;
  }

  ds_free(tid, p_old);

  return p_new;
}


//------------------------------------------------------------//
//--- Write the result                                     ---//
//------------------------------------------------------------//

enum instr_kind { LOAD, STORE };

static Bool print_inst(VgFile *fp, handle h, enum instr_kind instr_kind,
                       Bool is_first)
{
  Bool should_print = False;
  if (instr_kind == LOAD) {
    should_print = nodes[h].nof_loads != 0;
  }
  if (instr_kind == STORE) {
    should_print = nodes[h].nof_stores != 0;
  }

  if (should_print) {
    if (!is_first)
      VG_(fprintf)(fp, ",\n");
    VG_(fprintf)(fp, "    {\n");

    DiEpoch ep = VG_(current_DiEpoch)();
    Bool found_file_line, found_fn;
    const HChar *fn_name;
    const HChar *file;
    const HChar *dir;
    UInt line;

    VG_(fprintf)(fp, "      \"ips\": [\n");
    for (UInt i = 0; i < nodes[h].key.nof_ips; i++) {
      found_fn = VG_(get_fnname)(ep, nodes[h].key.ips[i], &fn_name);
      found_file_line =
        VG_(get_filename_linenum)(ep, nodes[h].key.ips[i], &file, &dir, &line);

      VG_(fprintf)(fp, "        {\n");
      Bool need_comma = found_fn || found_file_line;
      VG_(fprintf)(fp, "          \"address\": %lu%c\n",
                   nodes[h].key.ips[i], need_comma ? ',' : ' ');

      need_comma = found_file_line;
      if (found_fn) {
        VG_(fprintf)(fp, "          \"function\": \"%s\"%c\n", fn_name,
                     need_comma ? ',' : ' ');
      }

      if (found_file_line) {
        VG_(fprintf)(fp, "          \"file\": \"%s/%s\",\n", dir, file);
        VG_(fprintf)(fp, "          \"line\": %u\n", line);
      }

      need_comma = (i + 1) != nodes[h].key.nof_ips;
      VG_(fprintf)(fp, "        }%c\n", need_comma ? ',' : ' ');
    }
    VG_(fprintf)(fp, "      ],\n");

    if (instr_kind == STORE) {
      VG_(fprintf)(fp, "      \"bytes_written\": %lld,\n",
                   nodes[h].bytes_written);
      VG_(fprintf)(fp, "      \"bytes_read\": %lld,\n", nodes[h].bytes_read);
      VG_(fprintf)(fp, "      \"nof_stores\": %lld,\n", nodes[h].nof_stores);
      VG_(fprintf)(fp, "      \"nof_silent\": %lld\n",
                   nodes[h].nof_silent_stores);
    }
    if (instr_kind == LOAD) {
      VG_(fprintf)(fp, "      \"nof_loads\": %lld,\n", nodes[h].nof_loads);
      VG_(fprintf)(fp, "      \"nof_silent\": %lld\n",
                   nodes[h].nof_silent_loads);
    }

    VG_(fprintf)(fp, "    }");

    is_first = False;
  }

  return is_first;
}

static Bool print_tree(VgFile *fp, handle h, enum instr_kind instr_kind,
                       Bool is_first)
{
  // Print tree recursively to get the output sorted by address (not really
  // needed, but it simplifies debugging...)

  if (h == 0)
    return is_first;

  is_first = print_tree(fp, nodes[h].left, instr_kind, is_first);
  is_first = print_inst(fp, h, instr_kind, is_first);
  is_first = print_tree(fp, nodes[h].right, instr_kind, is_first);

  return is_first;
}

static void ds_fini(Int exitcode)
{
  HChar *file_name =
      VG_(expand_file_name)("--deadstores-out-file", deadstores_out_file);
  VgFile *fp = VG_(fopen)(file_name, VKI_O_CREAT | VKI_O_TRUNC | VKI_O_WRONLY,
                          VKI_S_IRUSR | VKI_S_IWUSR);
  if (fp == NULL) {
    VG_(umsg)("Error: cannot open output file '%s'\n", file_name);
    VG_(exit)(1);
  }
  VG_(free)(file_name);

  VG_(fprintf)(fp, "{\n");
  VG_(fprintf)(fp, "  \"command\": \"");
  for (HChar *p = cmd_line; *p != 0; p++) {
    switch (*p) {
    case '\n':
      VG_(fprintf)(fp, "\\\n");
      break;
    case '"':
      VG_(fprintf)(fp, "\\\"");
      break;
    default:
      VG_(fprintf)(fp, "%c", *p);
      break;
    }
  }
  VG_(fprintf)(fp, "\",\n");
  VG_(fprintf)(fp, "  \"stores\": [\n");
  Bool is_first = print_tree(fp, tree_root, STORE, True);
  if (!is_first)
    VG_(fprintf)(fp, "\n");
  VG_(fprintf)(fp, "  ],\n");
  VG_(fprintf)(fp, "  \"loads\": [\n");
  is_first = print_tree(fp, tree_root, LOAD, True);
  if (!is_first)
    VG_(fprintf)(fp, "\n");
  VG_(fprintf)(fp, "  ]\n");
  VG_(fprintf)(fp, "}\n");
  VG_(fclose)(fp);
}


//------------------------------------------------------------//
//--- Initialization                                       ---//
//------------------------------------------------------------//

static void ds_post_clo_init(void)
{
  save_cmd_line();
  init_tree();
  init_addr_info();
}

static void ds_pre_clo_init(void)
{
  VG_(details_name)               ("DeadStores");
  VG_(details_version)            (NULL);
  VG_(details_description)        ("find redundant loads/stores");
  VG_(details_copyright_author)   (
     "Copyright (C) 2020, and GNU GPL'd, by Krister Walfridsson");
  VG_(details_bug_reports_to)     ("github.com/kristerw/deadstores");

  VG_(basic_tool_funcs)           (ds_post_clo_init,
                                   ds_instrument,
                                   ds_fini);
  VG_(needs_command_line_options) (ds_process_cmd_line_options,
                                   ds_print_usage,
                                   ds_print_debug_usage);

  VG_(track_new_mem_stack)        (ds_new_mem_stack);
  VG_(track_die_mem_stack)        (ds_die_mem_stack);
  VG_(track_pre_mem_read)         (ds_pre_mem_read);
  VG_(track_post_mem_write)       (ds_post_mem_write);

  VG_(needs_malloc_replacement)   (ds_malloc,
                                   ds___builtin_new,
                                   ds___builtin_vec_new,
                                   ds_memalign,
                                   ds_calloc,
                                   ds_free,
                                   ds___builtin_delete,
                                   ds___builtin_vec_delete,
                                   ds_realloc,
                                   ds_malloc_usable_size,
                                   0);
}

VG_DETERMINE_INTERFACE_VERSION(ds_pre_clo_init)

//--------------------------------------------------------------------//
//--- end                                                ds_main.c ---//
//--------------------------------------------------------------------//
