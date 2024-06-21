/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    heap.h

Abstract:

    A heap of integers.

Author:

    Leonardo de Moura (leonardo) 2006-09-14.

Revision History:

--*/
#pragma once

#include "util/vector.h"
#include "util/debug.h"
#include <cstring>

template<typename LT>
class heap : private LT {
    int_vector      m_keys;
    int_vector      m_indices;

    static int left(int i) { 
        return i << 1; 
    }

    static int right(int i) { 
        return (i << 1) + 1; 
    }

    static int parent(int i) { 
        return i >> 1; 
    }

    void display(std::ostream& out, unsigned indent, int idx) const {
        if (idx < static_cast<int>(m_keys.size())) {
            for (unsigned i = 0; i < indent; ++i) out << " ";
            out << m_keys[idx] << "\n";
            display(out, indent + 1, left(idx));
            display(out, indent + 1, right(idx));
        }
    }

    // Return true if the value can be inserted in the heap. That is, the vector m_indices is big enough to store this value.
    bool is_valid_value(int v) const { 
        SASSERT(v >= 0 && v < static_cast<int>(m_indices.size())); 
        return true; 
    }

    bool check_invariant_core(int idx) const {
        if (idx < static_cast<int>(m_keys.size())) {
            SASSERT(m_indices[m_keys[idx]] == idx);
            SASSERT(parent(idx) == 0 || !less_than(m_keys[idx], m_keys[parent(idx)]));
            SASSERT(check_invariant_core(left(idx)));
            SASSERT(check_invariant_core(right(idx)));
        }
        return true;
    }


public:
    bool check_invariant() const { 
        return check_invariant_core(1); 
    }

private:
    // index : 메모리에서의 위치. 1이면 제일 상위노드, 2~3 은 1의 child, 4~5는 2의 child....
    // key : z3에서는 literal의 넘버를 지정하는데 쓰임.
    // value : literal의 넘버는 고정되어 있으므로, 새롭게 sort를 하기 위해서 도입한 변수
    //         초기 값을 선정할 때 매우 중요하게 작용한다.

    void move_up(int idx) {
        int key = m_keys[idx];

        while (true) {
            int parent_idx = parent(idx);
            int parent_key = m_keys[parent_idx];

            if (parent_idx == 0 || !less_than(key, parent_key))
                break;

            m_keys[idx]               = parent_key;
            m_indices[parent_key]        = idx;
            idx                            = parent_idx;
        }
        m_keys[idx]        = key;
        m_indices[key]        = idx;

        CASSERT("heap", check_invariant());
    }

    void move_down(int idx) {
        int key = m_keys[idx];
        int sz  = static_cast<int>(m_keys.size());

        while (true) {
            int left_idx  = left(idx);
            if (left_idx >= sz) // Child가 없는 경우
                break;
            int left_key = m_keys[left_idx];

            int min_idx = left_idx;

            int right_idx = right(idx);
            if (right_idx < sz) { // Child가 둘 다 있는 경우
                int right_key = m_keys[right_idx];
                
                if (less_than(right_key, left_key))
                    min_idx = right_idx;
            }
            SASSERT(parent(min_idx) == idx);

            int min_key = m_keys[min_idx];
            
            if (less_than(key, min_key)) // 현재 데이터의 값이 child보다 작은 경우는 스왑할 필요 없음
                break;

            m_keys[idx]        = min_key;
            m_indices[min_key]    = idx;
            idx                     = min_idx;
        }
        m_keys[idx]        = key;
        m_indices[key]        = idx;
        CASSERT("heap", check_invariant());
    }

public:
    typedef int * iterator;
    typedef const int * const_iterator;

    heap(int s, const LT & lt = LT()):LT(lt) {
        m_keys.push_back(-1);
        set_bounds(s);
        CASSERT("heap", check_invariant());
    }

    bool less_than(int v1, int v2) const { 
        return LT::operator()(v1, v2); 
    }

    const int get_key(int index){
        return m_keys[index];
    }

    const int get_index(int key){
        return m_indices[key];
    }

    bool empty() const { 
        return m_keys.size() == 1; 
    }

    bool contains(int key) const { 
        return key < static_cast<int>(m_indices.size()) && m_indices[key] != 0; 
    }

    void reset() {
        CASSERT("heap", check_invariant());
        if (empty()) {
            return;
        }
        memset(m_indices.data(), 0, sizeof(int) * m_indices.size());
        m_keys.reset();
        m_keys.push_back(-1);
        CASSERT("heap", check_invariant());
    }

    void clear() { 
        reset(); 
    }

    void heapify() {
        int n = static_cast<int>(m_keys.size()) - 1; 
        for (int i = n / 2; i > 0; --i) { 
            move_down(i);
        }
        CASSERT("heap", check_invariant());
    }

    void set_bounds(int s) { 
        m_indices.resize(s, 0); 
        CASSERT("heap", check_invariant());
    }
    
    unsigned get_bounds() const {
        return m_indices.size();
    }

    unsigned size() const {
        return m_indices.size();
    }

    void reserve(int s) {
        CASSERT("heap", check_invariant());
        if (s > static_cast<int>(m_indices.size()))
            set_bounds(s);
        CASSERT("heap", check_invariant());
    }

    int min_value() const {
        SASSERT(!empty());
        return m_keys[1];
    }

    int erase_min() {
        CASSERT("heap", check_invariant());
        SASSERT(!empty());
        SASSERT(m_keys.size() >= 2);
        int result                  = m_keys[1];
        if (m_keys.size() == 2) {
            m_indices[result] = 0;
            m_keys.pop_back();
            SASSERT(empty());
        }
        else {
            int last_key              = m_keys.back();
            m_keys[1]               = last_key;
            m_indices[last_key] = 1;
            m_indices[result]   = 0;
            m_keys.pop_back();
            move_down(1);
        }
        CASSERT("heap", check_invariant());
        return result;
    }

    void erase(int key) {
        CASSERT("heap", check_invariant());
        SASSERT(contains(key));
        int idx      = m_indices[key];
        if (idx == static_cast<int>(m_keys.size()) - 1) {
            m_indices[key] = 0;
            m_keys.pop_back();
        }
        else {
            int last_key              = m_keys.back();
            m_keys[idx]             = last_key;
            m_indices[last_key] = idx;
            m_indices[key]      = 0;
            m_keys.pop_back();
            int parent_idx            = parent(idx);
            if (parent_idx != 0 && less_than(last_key, m_keys[parent(idx)])) {
                move_up(idx);
            } else {
                move_down(idx);
            }
        }
        CASSERT("heap", check_invariant());
    }

    void decreased(int key) { 
        SASSERT(contains(key)); 
        move_up(m_indices[key]); 
    }

    void increased(int key) { 
        SASSERT(contains(key)); 
        move_down(m_indices[key]); 
    }

    void insert(int key) {
        CASSERT("heap", check_invariant());
        CASSERT("heap", !contains(key));
        SASSERT(is_valid_value(key));
        int idx              = static_cast<int>(m_keys.size());
        m_indices[key] = idx;
        m_keys.push_back(key);
        SASSERT(idx == static_cast<int>(m_keys.size()) - 1);
        move_up(idx);
        CASSERT("heap", check_invariant());
    }

    iterator begin() { 
        return m_keys.data() + 1; 
    }

    iterator end() { 
        return m_keys.data() + m_keys.size(); 
    }

    const_iterator begin() const { 
        return m_keys.begin() + 1; 
    }

    const_iterator end() const { 
        return m_keys.end(); 
    }

    void swap(heap & other) {
        if (this != &other) {
            CASSERT("heap", other.check_invariant());
            CASSERT("heap", check_invariant());
            m_keys.swap(other.m_keys);
            m_indices.swap(other.m_indices);
            CASSERT("heap", other.check_invariant());
            CASSERT("heap", check_invariant());
        }
    }

    /**
       \brief return set of values in heap that are less or equal to val.
     */
    void find_le(int key, int_vector& result) {
        int_vector todo;
        todo.push_back(1);
        while (!todo.empty()) {
            int index = todo.back();
            todo.pop_back();
            if (index < static_cast<int>(m_keys.size()) &&
                !less_than(key, m_keys[index])) {
                result.push_back(m_keys[index]);
                todo.push_back(left(index));
                todo.push_back(right(index));
            }
        }
    }

    void display(std::ostream& out) const {
        display(out, 0, 1);
    }
};
