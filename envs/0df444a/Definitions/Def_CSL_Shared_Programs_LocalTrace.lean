-- Prove2me | Definitions.Def_CSL_Shared_Programs_LocalTrace
-- name    : CSL_Shared_Programs_LocalTrace
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:44:23.262988+00:00
-- url     : https://prove2.me/theorems/dfb2c605-2c38-4743-9793-af45983e22a4
-- title:
--   Coded sorting library: Shared / Programs / LocalTrace
-- statement:
--   Module `CodedSorting.Shared.Programs.LocalTrace` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   The actual power-of-two shape chosen by recursive local Columnsort.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Programs.LocalTrace

import Definitions.Def_CSL_Compat
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_CSL_Sorting_Bounds_RecursiveSortBase

section LocalShape
/-! The actual power-of-two shape chosen by recursive local Columnsort. -/
namespace CSL.LocalShape

/-- ceil(log₂ n/4), expressed as the natural ceiling logarithm to base 16. -/
def sizeExponent (n : ℕ) : ℕ := Nat.clog 16 n

def sizeChoice (n : ℕ) : ℕ := 2 ^ sizeExponent n

def columnLength (n : ℕ) : ℕ := sizeChoice n ^ 3

theorem padding_identity (n : ℕ) : sizeChoice n ^ 4 = 16 ^ sizeExponent n := by
  unfold sizeChoice
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

theorem padding_ge (n : ℕ) : n ≤ sizeChoice n ^ 4 := by
  rw [padding_identity]
  exact Nat.le_pow_clog (by norm_num) n

theorem padding_lt (n : ℕ) (hn : 1 < n) : sizeChoice n ^ 4 < 16 * n := by
  have he : 0 < sizeExponent n := Nat.clog_pos (by norm_num) (by omega)
  have hp := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 16) hn
  change 16 ^ (sizeExponent n - 1) < n at hp
  rw [padding_identity, show sizeExponent n = (sizeExponent n - 1) + 1 by omega, pow_succ]
  nlinarith

theorem exponent_ge_three (n : ℕ) (hn : 512 < n) : 3 ≤ sizeExponent n := by
  have h : 16 ^ 2 < n := by norm_num; omega
  have hl := (Nat.pow_lt_iff_lt_clog (by norm_num : 1 < 16)).mp h
  exact hl

theorem column_lt (n : ℕ) (hn : 512 < n) : columnLength n < n := by
  by_cases he : sizeExponent n ≤ 3
  · have hm := Nat.pow_le_pow_right (by omega : 0 < 2) (Nat.mul_le_mul_right 3 he)
    change 2 ^ (sizeExponent n * 3) ≤ 2 ^ (3 * 3) at hm
    norm_num at hm
    unfold columnLength sizeChoice
    rw [← pow_mul]
    omega
  · have hp := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 16) (show 1 < n by omega)
    have hexp : sizeExponent n * 3 ≤ (sizeExponent n - 1) * 4 := by omega
    have hm := Nat.pow_le_pow_right (by omega : 0 < 2) hexp
    have h16 : 2 ^ ((sizeExponent n - 1) * 4) = 16 ^ (sizeExponent n - 1) := by
      rw [Nat.mul_comm, pow_mul]
      norm_num
    rw [h16] at hm
    unfold columnLength sizeChoice
    rw [← pow_mul]
    exact lt_of_le_of_lt hm hp

theorem shape_bound (n H : ℕ) (hH : 0 < H) (hn : 512 * H < n) :
    3 ≤ sizeExponent n ∧ 8 ≤ sizeChoice n ∧ n ≤ sizeChoice n ^ 4 ∧
      sizeChoice n ^ 4 < 16 * n ∧ columnLength n < n := by
  have h512 : 512 < n := by nlinarith
  have he := exponent_ge_three n h512
  have hs := Nat.pow_le_pow_right (by omega : 0 < 2) he
  refine ⟨he, ?_, padding_ge n, padding_lt n (by omega), column_lt n h512⟩
  simpa [sizeChoice] using hs

/-- All four rounds together contain 4s+1 columns, including the extra
sentinel column in the shifted round. -/
theorem child_volume (n : ℕ) (hn : 1 < n) :
    (4 * sizeChoice n + 1) * columnLength n < 80 * n := by
  have hp := padding_lt n hn
  have hs : 1 ≤ sizeChoice n := Nat.one_le_pow _ _ (by norm_num)
  unfold columnLength
  have hid : sizeChoice n ^ 4 = sizeChoice n * sizeChoice n ^ 3 := by ring
  nlinarith

/-- Integer ceiling-log estimate; no real logarithms or asymptotics. -/
theorem exponent_of_power_le (n k : ℕ) (hn : n ≤ 2 ^ k) :
    sizeExponent n ≤ (k + 3) / 4 := by
  apply (Nat.le_pow_iff_clog_le (by norm_num : 1 < 16)).mp
  calc
    n ≤ 2 ^ k := hn
    _ ≤ 2 ^ (((k + 3) / 4) * 4) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = 16 ^ ((k + 3) / 4) := by rw [Nat.mul_comm, pow_mul]; norm_num

theorem column_exponent_bound (n : ℕ) :
    4 * sizeExponent (columnLength n) ≤ 3 * sizeExponent n + 3 := by
  have he := exponent_of_power_le (columnLength n) (3 * sizeExponent n) (by
    unfold columnLength sizeChoice
    rw [← pow_mul, Nat.mul_comm])
  omega

/-- The actual rounded column lengths reach the in-memory cutoff after at
most three levels for n≤H². This includes all rounding factors. -/
theorem three_levels_fit (n H : ℕ) (hH : 0 < H) (hn : n ≤ H ^ 2) :
    columnLength (columnLength (columnLength n)) ≤ 128 * H := by
  let L := Nat.log 2 H
  have hh : H < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) H
  have hnPow : n ≤ 2 ^ (2 * (L + 1)) := by
    calc
      n ≤ H ^ 2 := hn
      _ ≤ (2 ^ (L + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ (2 * (L + 1)) := by rw [← pow_mul, Nat.mul_comm]
  have he0 := exponent_of_power_le n (2 * (L + 1)) hnPow
  have he1 := column_exponent_bound n
  have he2 := column_exponent_bound (columnLength n)
  have hexp : 3 * sizeExponent (columnLength (columnLength n)) ≤ L + 7 := by omega
  have hpow := Nat.pow_le_pow_right (by omega : 0 < 2) hexp
  have hL : 2 ^ L ≤ H := Nat.pow_log_le_self 2 (by omega)
  unfold columnLength sizeChoice at hpow ⊢
  rw [← pow_mul, Nat.mul_comm]
  calc
    2 ^ (3 * sizeExponent ((2 ^ sizeExponent ((2 ^ sizeExponent n) ^ 3)) ^ 3)) ≤ 2 ^ (L + 7) := hpow
    _ = 128 * 2 ^ L := by rw [pow_add]; norm_num; ring
    _ ≤ 128 * H := Nat.mul_le_mul_left _ hL

end CSL.LocalShape
end LocalShape

section LocalTrace
/-! Structural invariant of the actual recursive Columnsort call trace.
There are no I/O inequalities in this predicate. -/
namespace CSL.LocalTrace
open RecursiveColumnsort LocalShape

inductive Fits (H : ℕ) : ℕ → ℕ → CallTree → Prop
  | leaf (fuel n : ℕ) (hleaf : fuel = 0 ∨ n ≤ 512 * H) :
      Fits H fuel n (.leaf n)
  | node {fuel n : ℕ} {first second third fourth : List CallTree}
      (hlarge : 512 * H < n)
      (hfirst : first.length = sizeChoice n)
      (hsecond : second.length = sizeChoice n)
      (hthird : third.length = sizeChoice n)
      (hfourth : fourth.length = sizeChoice n + 1)
      (firstFits : ∀ child ∈ first, Fits H fuel (columnLength n) child)
      (secondFits : ∀ child ∈ second, Fits H fuel (columnLength n) child)
      (thirdFits : ∀ child ∈ third, Fits H fuel (columnLength n) child)
      (fourthFits : ∀ child ∈ fourth, Fits H fuel (columnLength n) child) :
      Fits H (fuel + 1) n (.node n (sizeChoice n) first second third fourth)

theorem Fits.leaf_of_small {H fuel n : ℕ} {tree : CallTree}
    (h : Fits H fuel n tree) (hn : n ≤ 512 * H) : tree = .leaf n := by
  cases h with
  | leaf => rfl
  | node hlarge => omega

theorem Fits.leaf_of_zero {H n : ℕ} {tree : CallTree}
    (h : Fits H 0 n tree) : tree = .leaf n := by
  cases h
  rfl

end CSL.LocalTrace
end LocalTrace


