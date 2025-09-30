# Name: Prajwal D C
# Class: CS 456 – Analysis of Algorithms
# Assignment: Coding Assignment 3 with extra credit

import random
import time
import tracemalloc
from itertools import combinations

GRANDCHILDREN = ["camila", "selena", "melanie"]

# ---------------------------------------------------------
# Helper Functions
# ---------------------------------------------------------

def favorite_from_initials(first_initial: str, last_initial: str, *extra_initials: str) -> str:
    def pos(ch: str) -> int:
        ch = ch.strip().upper()
        return ord(ch) - ord('A') + 1
    s = pos(first_initial) + pos(last_initial) + sum(pos(i) for i in extra_initials)
    idx = s % 3  # 0->Camila, 1->Selena, 2->Melanie
    return GRANDCHILDREN[idx]

def pick_second_favorite(fav: str) -> str:
    order = GRANDCHILDREN[:]  # ["camila","selena","melanie"]
    i = order.index(fav)
    return order[(i + 1) % 3]  # deterministic

# My initials: P + D + C = 23 -> 23 % 3 = 2 -> Melanie
MY_FAVORITE = favorite_from_initials("P", "D", "C")
YOUR_SECOND_FAVORITE = pick_second_favorite(MY_FAVORITE)

# ---------------------------------------------------------
# Dynamic Programming core: tabulation 
# ---------------------------------------------------------

def subset_sum_indices(values, target):
    """
    Tabulation (bottom-up) over reachable sums.
    Find subset of indices whose sum is the largest <= target.
    Returns: (picked_indices, achieved_sum)
    Uses a map parent[sum] = (prev_sum, idx_used) to reconstruct.
    """
    parent = {0: None}
    current_sums = {0}
    best = 0

    for idx, v in enumerate(values):
        new_sums = []
        for s in list(current_sums):
            ns = s + v
            if ns <= target and ns not in parent:
                parent[ns] = (s, idx)
                new_sums.append(ns)
                if ns > best:
                    best = ns
        current_sums.update(new_sums)
        if best == target:
            break

    # Reconstruct
    picked = []
    s = best
    while s != 0:
        ps, idx = parent[s]
        picked.append(idx)
        s = ps
    picked.reverse()
    return picked, best

def partition_two_way(values):
    """Return two lists of indices (L, R) forming a near-equal partition by sum."""
    total = sum(values)
    left_idxs, _ = subset_sum_indices(values, total // 2)
    left_set = set(left_idxs)
    right = [i for i in range(len(values)) if i not in left_set]
    return left_idxs, right

def exact_discard_from_larger(values, left_idxs, right_idxs):
    """
    Try to discard from the larger pile so the two piles become exactly equal.
    First try: discard a subset from the larger pile whose sum equals the current diff.
    If that fails, try discarding from BOTH piles: find t reachable from the smaller,
    and check if diff + t is reachable from the larger; discard those from each side.
    Returns: (new_left, new_right, discards_global_indices)
    """
    sum_left = sum(values[i] for i in left_idxs)
    sum_right = sum(values[i] for i in right_idxs)
    if sum_left == sum_right:
        return left_idxs, right_idxs, []

    # Normalize: "larger" & "smaller"
    if sum_left >= sum_right:
        larger, smaller, larger_name = left_idxs[:], right_idxs[:], "left"
        diff = sum_left - sum_right
    else:
        larger, smaller, larger_name = right_idxs[:], left_idxs[:], "right"
        diff = sum_right - sum_left

    # ---- Try 1: discard only from larger, sum == diff
    larger_vals = [values[i] for i in larger]
    picked_l_rel, achieved = subset_sum_indices(larger_vals, diff)
    if achieved == diff and picked_l_rel:
        discard_from_larger = {larger[j] for j in picked_l_rel}
        if larger_name == "left":
            new_left = [i for i in larger if i not in discard_from_larger]
            new_right = smaller
        else:
            new_left = smaller
            new_right = [i for i in larger if i not in discard_from_larger]
        return new_left, new_right, sorted(discard_from_larger)

    # ---- Try 2: discard from BOTH sides to hit exact equality
    reachable_small = {0}
    sumL = sum(values[i] for i in left_idxs)
    sumR = sum(values[i] for i in right_idxs)
    for i in range(len(smaller)):
        v = values[smaller[i]]
        limit = sumR if larger_name == "left" else sumL
        new = {s + v for s in reachable_small if s + v <= limit}
        reachable_small |= new

    max_t = sum(values[i] for i in smaller)
    for t in range(max_t + 1):
        if t not in reachable_small:
            continue
        target_large = diff + t
        if target_large < 0:
            continue
        picked_l_rel2, achieved2 = subset_sum_indices(larger_vals, target_large)
        if achieved2 == target_large:
            smaller_vals = [values[i] for i in smaller]
            picked_s_rel, achieved_s = subset_sum_indices(smaller_vals, t)
            if achieved_s == t:
                discard_from_larger = {larger[j] for j in picked_l_rel2}
                discard_from_smaller = {smaller[j] for j in picked_s_rel}
                discards = sorted(discard_from_larger | discard_from_smaller)
                if larger_name == "left":
                    new_left = [i for i in larger if i not in discard_from_larger]
                    new_right = [i for i in smaller if i not in discard_from_smaller]
                else:
                    new_left = [i for i in smaller if i not in discard_from_smaller]
                    new_right = [i for i in larger if i not in discard_from_larger]
                if sum(values[i] for i in new_left) == sum(values[i] for i in new_right):
                    return new_left, new_right, discards

    # If we reach here, exact equality by local discards failed.
    return left_idxs, right_idxs, []

