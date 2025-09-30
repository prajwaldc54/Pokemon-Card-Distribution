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

def fallback_equalize_globally(values):
    """
    Always-produce-equality fallback for the G=2 no-favorite case.
    Uses the full deck to create two exactly equal piles by discarding as needed.
    Strategy:
      1) Choose subset S close to total//2 using DP on ALL items.
      2) Let R = complement. If sum(R) == sum(S), done.
      3) Otherwise discard from R a subset that equals (sum(R) - sum(S)).
      4) If even that is impossible (very rare), discard everything so both are 0.
    Returns: (pileA, pileB, discards) as lists of global indices.
    """
    n = len(values)
    total = sum(values)
    target = total // 2
    S_rel, sS = subset_sum_indices(values, target)
    S_set = set(S_rel)
    R = [i for i in range(n) if i not in S_set]
    sR = sum(values[i] for i in R)
    if sR == sS:
        return S_rel, R, []

    diff = sR - sS  # >= 0 because sS is <= total//2
    R_vals = [values[i] for i in R]
    pick_rel, got = subset_sum_indices(R_vals, diff)
    if got == diff:
        discard_from_R = {R[j] for j in pick_rel}
        new_R = [i for i in R if i not in discard_from_R]
        return S_rel, new_R, sorted(discard_from_R)

    # Last-resort equality: both get 0 (discard all).
    return [], [], list(range(n))

def three_way_partition(values):
    """
    Heuristic DP for k=3:
      - pick T1 ~ S/3 via subset-sum on all items,
      - from the remainder pick T2 ~ S/3 via subset-sum,
      - T3 is the rest.
    Returns three lists of indices (relative to 'values').
    """
    n = len(values)
    total = sum(values)
    target = total // 3

    # T1
    T1_rel, _ = subset_sum_indices(values, target)
    T1_set = set(T1_rel)
    rem1 = [i for i in range(n) if i not in T1_set]
    rem_vals = [values[i] for i in rem1]

    # T2 on remaining
    T2_rel_in_rem, _ = subset_sum_indices(rem_vals, target)
    T2 = [rem1[j] for j in T2_rel_in_rem]

    T2_set = set(T2)
    T3 = [i for i in range(n) if i not in T1_set and i not in T2_set]
    return T1_rel, T2, T3

# ---------------------------------------------------------
# Main assignment (PDC_ca3)
# ---------------------------------------------------------

def PDC_ca3(A, G, fav_name=None, random_seed=None, verbose=True):
    """
    A: list[int] (1..4096 length, values 1..50)
    G: 1, 2, or 3
    fav_name: optional override for favorite; default uses initials (Melanie for you)
    random_seed: to reproduce random scenario selection
    verbose: print human-readable output if True (silence for experiments)
    """
    if random_seed is not None:
        random.seed(random_seed)

    n = len(A)
    fav = (fav_name or MY_FAVORITE).lower()
    second_fav = pick_second_favorite(fav) if G == 3 else None

    if verbose:
        print("\n\n*** Main Assignment ***\n")
        print(f"Grandma Rosa has a deck of {n} cards and wants to distribute it to {G} grandchild(ren).")
        print(f"When she passed, her favorite grandchild was {fav.capitalize()}.")

    # Randomly select G grandchildren per spec
    choices = list(combinations(GRANDCHILDREN, G))
    scenario = random.choice(choices)
    scenario_set = set(scenario)
    if verbose:
        print(f"\nScenario – Randomly selected: {', '.join(nm.capitalize() for nm in scenario)}")
        print(f"Favorite included? {'Yes' if fav in scenario_set else 'No'}")
        if G == 3:
            print(f"Second favorite (policy): {second_fav.capitalize()}")

    # Prepare allocations (indices into A)
    allocations = {name: [] for name in GRANDCHILDREN}
    discards = []

    all_idx = list(range(n))

    if G == 1:
        only = list(scenario_set)[0]
        allocations[only] = all_idx[:]

    elif G == 2:
        a, b = scenario
        L, R = partition_two_way([A[i] for i in all_idx])
        sumL = sum(A[i] for i in L)
        sumR = sum(A[i] for i in R)

        if fav in scenario_set:
            other = b if a == fav else a
            if sumL >= sumR:
                allocations[fav] = L
                allocations[other] = R
            else:
                allocations[fav] = R
                allocations[other] = L
        else:
            # Must equalize exactly by discarding if possible
            newL, newR, discard_idxs = exact_discard_from_larger(A, L, R)

            # If still not exactly equal, enforce equality via global fallback
            if sum(A[i] for i in newL) != sum(A[i] for i in newR):
                eqL, eqR, extra_discards = fallback_equalize_globally(A)
                allocations[a] = eqL
                allocations[b] = eqR
                discards.extend(extra_discards)
            else:
                allocations[a] = newL
                allocations[b] = newR
                discards.extend(discard_idxs)

    else:  # G == 3
        T1, T2, T3 = three_way_partition([A[i] for i in all_idx])
        triple = [T1, T2, T3]
        sums = [sum(A[i] for i in part) for part in triple]

        if fav in scenario_set:
            # Priority order: favorite -> second favorite -> remaining
            pri = [fav, second_fav] + [x for x in GRANDCHILDREN if x not in (fav, second_fav)]
            pri = [x for x in pri if x in scenario_set]
        else:
            # No favorite in scenario: assign largest->first listed, etc. (deterministic)
            pri = list(scenario)

        order = sorted(range(3), key=lambda k: sums[k], reverse=True)
        for i, child in enumerate(pri):
            allocations[child] = triple[order[i]]

    # Print allocations for all three grandchildren
    if verbose:
        for child in GRANDCHILDREN:
            cards_allocated = sorted(allocations[child])
            value_sum = sum(A[i] for i in cards_allocated)
            card_list_str = ", ".join(str(i + 1) for i in cards_allocated) if cards_allocated else "0"
            print(f">> {child.capitalize()} would get cards {card_list_str} with a total value of ${value_sum}")

        # Discards
        if discards:
            discards = sorted(set(discards))
            print(f">> Card(s) discarded: {', '.join(str(i + 1) for i in discards)}")
        else:
            print(">> No cards were excluded")

    return allocations

