-- Prove2me | Definitions.Def_MITMSynthesis_searchC
-- name    : MITMSynthesis_searchC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:03:58.332617+00:00
-- url     : https://prove2.me/theorems/44eeba44-044c-4235-bd60-d454daaf01a0
-- title:
--   Binary search with counted probes
-- statement:
--   Binary search in an array sorted by a key, written in the cost monad.
--
--   1. `bsearchC` searches the index window $[lo, hi)$: if it is empty it costs one step and reports no hit; otherwise it reads the middle element (index $\lfloor (lo+hi)/2 \rfloor$), compares the query with its key at one step, and either returns the element (equal keys) or continues in the left or right half.
--   2. `searchC` searches the whole array.
--   3. `searchAllC` takes a list of queries (key, payload), searches them in order at one step each plus the binary search, and returns the payload of the first query found together with the matching array element.
--
--   This is the collision search of MITM-factor, which looks up every element of $S_{i-1}^\dagger U$ and $S_i^\dagger U$ in the sorted $S_i$.
--
--   **Formalization Note** An out-of-range read (which cannot happen for windows inside the array) costs one step and reports no hit.
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, §3, p. 6 ("searching for each element of S_{i−1}†U and S_i†U in S_i")

import Mathlib
import Definitions.Def_MITMSynthesis_Timed

namespace MITMSynthesis


variable {β : Type} {κ : Type} [LinearOrder κ]

/-- Binary search for the key `q` in the index window `[lo, hi)` of an array sorted by `key`.
Every probe (one array read and one three-way comparison) costs one step; an empty window costs
one step. Returns an element whose key is `q`, if one is found. -/
def bsearchC (key : β → κ) (arr : Array β) (q : κ) (lo hi : ℕ) : Timed (Option β) :=
  if _h : lo < hi then
    match arr[(lo + hi) / 2]? with
    | none => do tick; pure none
    | some b => do
        let o ← cmpC q (key b)
        match o with
        | .lt => bsearchC key arr q lo ((lo + hi) / 2)
        | .gt => bsearchC key arr q ((lo + hi) / 2 + 1) hi
        | .eq => pure (some b)
  else do tick; pure none
termination_by hi - lo
decreasing_by all_goals omega

/-- Binary search for `q` in the whole array. -/
def searchC (key : β → κ) (arr : Array β) (q : κ) : Timed (Option β) :=
  bsearchC key arr q 0 arr.size

/-- **Search every query in a sorted array.** The queries are pairs (key, payload); they are
searched in order, each costing one step plus its binary search. The first query found returns
its payload together with the matching array element. -/
def searchAllC {γ : Type} (key : β → κ) (arr : Array β) : List (κ × γ) → Timed (Option (γ × β))
  | [] => pure none
  | (q, c) :: rest => do
      tick
      let r ← searchC key arr q
      match r with
      | some b => pure (some (c, b))
      | none => searchAllC key arr rest

end MITMSynthesis


