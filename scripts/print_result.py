#!/usr/bin/env python3

import argparse
import json
import sys

def output_stack_trace(instr):
    for ip in instr['ips']:
        addr = ip['address']
        if 'function' in ip:
            function = ip['function']
        else:
            function = '???'
        if 'file' in ip:
            file = ip['file'] + ':' + str(ip['line'])
        else:
            file = ''
        if ip is instr['ips'][0]:
            s = '    at '
        else:
            s = '    by '
        s = s + '0x{0:08x}:'.format(addr) + ' ' + function
        if file:
            s = s + ' (in ' + file + ')'
        print(s)

def output_load(instr):
    print('0x{0:08x}:'.format(instr['ips'][0]['address']))
    print('  nof_loads:     {0:8d}'.format(instr['nof_loads']))
    print('  nof_silent:    {0:8d}'.format(instr['nof_silent']))
    output_stack_trace(instr)

def output_store(instr):
    print('0x{0:08x}:'.format(instr['ips'][0]['address']))
    print('  bytes_written: {0:8d}'.format(instr['bytes_written']))
    print('  bytes_read:    {0:8d}'.format(instr['bytes_read']))
    print('  bytes_dead:    {0:8d}'.format(instr['bytes_dead']))
    print('  nof_stores:    {0:8d}'.format(instr['nof_stores']))
    print('  nof_silent:    {0:8d}'.format(instr['nof_silent']))
    output_stack_trace(instr)

def output_stores(stores, nof_output_elements):
    print('Dead stores')
    print('-----------')
    stores.sort(key=lambda instr: instr['bytes_dead'], reverse=True)
    is_first = True
    for instr in stores[:nof_output_elements]:
        if instr['bytes_dead'] != 0:
            if not is_first:
                print('')
            else:
                is_first = False
            output_store(instr)
    print('')
    print('')
    print('Silent stores')
    print('-------------')
    stores.sort(key=lambda instr: instr['nof_silent'], reverse=True)
    is_first = True
    for instr in stores[:nof_output_elements]:
        if instr['nof_silent'] != 0:
            if not is_first:
                print('')
            else:
                is_first = False
            output_store(instr)

def output_loads(loads, nof_output_elements):
    print('')
    print('')
    print('Silent loads')
    print('------------')
    loads.sort(key=lambda instr: instr['nof_silent'], reverse=True)
    is_first = True
    for instr in loads[:nof_output_elements]:
        if instr['nof_silent'] != 0:
            if not is_first:
                print('')
            else:
                is_first = False
            output_load(instr)

def uint(string):
    value = int(string)
    if value < 0:
        raise ValueError
    return value

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('-n', type=uint, default=5, help='output num entries')
    parser.add_argument('filename', help='intput file name')

    args = parser.parse_args()

    try:
        with open(args.filename, 'r') as stream:
            data = json.load(stream)
            loads = data['loads']
            stores = data['stores']
            command = data['command']
            for instr in stores:
                bytes_dead = instr['bytes_written'] - instr['bytes_read']
                instr['bytes_dead'] = bytes_dead
            print('Command: ' + command)
            print('')
            output_stores(stores, args.n)
            output_loads(loads, args.n)
    except (IOError, OSError) as err:
        sys.stderr.write(str(err) + '\n')
        sys.exit(1)

if __name__ == '__main__':
    main()
