-- Prove2me | Definitions.Def_Submission_ThreeSum_BandPartition
-- name    : Submission_ThreeSum_BandPartition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:53:21.28661+00:00
-- url     : https://prove2.me/theorems/50484e9e-814a-44e5-861d-c065673d1882
-- title:
--   Band Partition
-- statement:
--   Definitions and structural lemmas for Band Partition, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPartition.lean

import Definitions.Def_Submission_ThreeSum_BandEnumeration
set_option autoImplicit false
namespace ThreeSum.BandPartition
def size (n g : ℕ) : ℕ := if n = 0 then 0 else (n-1)/g+1
def start (g i : ℕ) : ℕ := i*g
def stop (n g i : ℕ) : ℕ := min n ((i+1)*g)
theorem start_lt {n g i : ℕ} (hg : 0 < g) (hi : i < size n g) : start g i < n := by
  unfold size at hi
  split_ifs at hi with hn
  · omega
  · have hid : i ≤ (n-1)/g := by omega
    have hm := (Nat.le_div_iff_mul_le hg).mp hid
    unfold start
    omega
theorem start_lt_stop {n g i : ℕ} (hg : 0 < g) (hi : i < size n g) :
    start g i < stop n g i := by
  have hn := start_lt hg hi
  unfold start stop at *
  have hprod : i*g < (i+1)*g := Nat.mul_lt_mul_of_pos_right (by omega) hg
  omega
theorem stop_le (n g i : ℕ) : stop n g i ≤ n := min_le_left _ _
theorem stop_sub_one_lt {n g i : ℕ} (hg : 0 < g) (hi : i < size n g) :
    stop n g i-1 < n := by
  have hp := start_lt_stop hg hi
  have hs := stop_le n g i
  omega
theorem monotone_of_strict {f : ℕ → ℤ} {n i j : ℕ}
    (hs : ∀ i j, i < j → j < n → f i < f j) (hij : i ≤ j) (hj : j < n) :
    f i ≤ f j := by
  rcases lt_or_eq_of_le hij with h | rfl
  · exact (hs i j h hj).le
  · rfl
def family (f : ℕ → ℤ) (n g : ℕ) (hg : 0 < g)
    (hs : ∀ i j, i < j → j < n → f i < f j) : BandEnumeration.Family where
  size := size n g
  lower i := f (start g i)
  upper i := f (stop n g i-1)
  nonempty i hi := monotone_of_strict hs (by have := start_lt_stop hg hi; omega)
    (stop_sub_one_lt hg hi)
  sorted i j hij hj := monotone_of_strict hs (Nat.mul_le_mul_right g hij) (start_lt hg hj)
  separated i j hij hj := by
    have hstop : stop n g i ≤ (i+1)*g := min_le_right _ _
    have hprod : (i+1)*g ≤ j*g := Nat.mul_le_mul_right g (by omega)
    have hpositive : 0 < j*g := by
      have hjpos : 0 < j := by omega
      exact Nat.mul_pos hjpos hg
    apply hs _ _ (by unfold start; omega) (start_lt hg hj)
end ThreeSum.BandPartition


