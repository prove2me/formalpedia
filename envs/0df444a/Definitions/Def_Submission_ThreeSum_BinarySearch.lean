-- Prove2me | Definitions.Def_Submission_ThreeSum_BinarySearch
-- name    : Submission_ThreeSum_BinarySearch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:23:53.212021+00:00
-- url     : https://prove2.me/theorems/cc68c18a-0ffc-4c0a-a2bc-dfdf6dfb9b34
-- title:
--   Binary Search
-- statement:
--   Definitions and structural lemmas for Binary Search, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinarySearch.lean

import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Basic
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
namespace ThreeSum.BinarySearch
def upperSearch (f : ℕ → ℤ) (x : ℤ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi) / 2
        if f mid ≤ x then upperSearch f x fuel (mid + 1) hi
        else upperSearch f x fuel lo mid
      else lo
def comparisons (f : ℕ → ℤ) (x : ℤ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi) / 2
        1 + if f mid ≤ x then comparisons f x fuel (mid + 1) hi
            else comparisons f x fuel lo mid
      else 0
def Partition (f : ℕ → ℤ) (x : ℤ) (n k : ℕ) : Prop :=
  k ≤ n ∧ (∀ i < k, f i ≤ x) ∧ (∀ i, k ≤ i → i < n → x < f i)
def upperBound (f : ℕ → ℤ) (n : ℕ) (x : ℤ) : ℕ :=
  upperSearch f x (Nat.log 2 n + 1) 0 n
def locate (lo hi : ℕ → ℤ) (n : ℕ) (x : ℤ) : Option ℕ :=
  let k := upperBound lo n x
  if 0 < k then
    if x ≤ hi (k - 1) then some (k - 1) else none
  else none
end ThreeSum.BinarySearch


