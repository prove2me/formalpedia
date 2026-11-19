-- Prove2me | Definitions.Def_LevyStochCalc_Analysis_DyadicGrid_F000
-- name    : LevyStochCalc_Analysis_DyadicGrid_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T21:56:03.077984+00:00
-- url     : https://prove2.me/theorems/cb4b180b-0893-420d-989d-13f07c65c7d9
-- title:
--   Source declarations: LevyStochCalc.Analysis.DyadicGrid
-- statement:
--   Source-preserving Lean declaration bundle from LevyStochCalc.Analysis.DyadicGrid, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Fin.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The dyadic partition of an interval

The dyadic partition of `[0, t]` of level `n`, its strict monotonicity, and the left endpoint
`leftPt t n s` of the cell containing a time `s ∈ (0, t]`, which tends to `s` from below.
-/

open Filter
open scoped Topology

namespace LevyStochCalc.Analysis

section Grid

/-- The dyadic partition of `[0, t]` of level `n`. -/
noncomputable def dyadicPartition (t : ℝ) (n : ℕ) (k : Fin (2 ^ n + 1)) : ℝ :=
  ((k : ℕ) : ℝ) * t / 2 ^ n
theorem dyadicPartition_zero (t : ℝ) (n : ℕ) : dyadicPartition t n 0 = 0 := by
  simp [dyadicPartition]
theorem dyadicPartition_last (t : ℝ) (n : ℕ) :
    dyadicPartition t n (Fin.last (2 ^ n)) = t := by
  rw [dyadicPartition, Fin.val_last, Nat.cast_pow, Nat.cast_ofNat, mul_comm, mul_div_assoc,
    div_self (by positivity), mul_one]
theorem dyadicPartition_strictMono {t : ℝ} (ht : 0 < t) (n : ℕ) :
    StrictMono (dyadicPartition t n) := by
  intro i j hij
  unfold dyadicPartition
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right (by exact_mod_cast hij) ht) h2
theorem dyadicPartition_le {t : ℝ} (ht : 0 < t) (n : ℕ) (j : Fin (2 ^ n + 1)) :
    dyadicPartition t n j ≤ t :=
  ((dyadicPartition_strictMono ht n).monotone (Fin.le_last j)).trans
    (dyadicPartition_last t n).le
theorem dyadicPartition_succ (t : ℝ) (n : ℕ) (k : Fin (2 ^ n)) :
    dyadicPartition t n k.succ = dyadicPartition t n k.castSucc + t / 2 ^ n := by
  simp only [dyadicPartition, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring
/-- The index of the cell of the dyadic partition of level `n` containing `s`. -/
noncomputable def leftIdx (t : ℝ) (n : ℕ) (s : ℝ) : ℕ := ⌈s * 2 ^ n / t⌉₊ - 1
/-- The left endpoint of the cell of the dyadic partition of level `n` containing `s`. -/
noncomputable def leftPt (t : ℝ) (n : ℕ) (s : ℝ) : ℝ := ((leftIdx t n s : ℕ) : ℝ) * t / 2 ^ n
theorem one_le_ceil {t : ℝ} (ht : 0 < t) (n : ℕ) {s : ℝ} (hs : 0 < s) :
    1 ≤ ⌈s * 2 ^ n / t⌉₊ :=
  Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
theorem leftPt_lt {t : ℝ} (ht : 0 < t) (n : ℕ) {s : ℝ} (hs : 0 < s) : leftPt t n s < s := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hx : 0 < s * 2 ^ n / t := by positivity
  have hlt : ((leftIdx t n s : ℕ) : ℝ) < s * 2 ^ n / t := by
    rw [leftIdx, Nat.cast_sub (one_le_ceil ht n hs), Nat.cast_one]
    linarith [Nat.ceil_lt_add_one hx.le]
  rw [leftPt, div_lt_iff₀ h2]
  calc ((leftIdx t n s : ℕ) : ℝ) * t < (s * 2 ^ n / t) * t := mul_lt_mul_of_pos_right hlt ht
    _ = s * 2 ^ n := by field_simp
theorem le_leftPt_add {t : ℝ} (ht : 0 < t) (n : ℕ) {s : ℝ} (hs : 0 < s) :
    s ≤ leftPt t n s + t / 2 ^ n := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hle : s * 2 ^ n / t ≤ ((leftIdx t n s : ℕ) : ℝ) + 1 := by
    rw [leftIdx, Nat.cast_sub (one_le_ceil ht n hs), Nat.cast_one, sub_add_cancel]
    exact Nat.le_ceil _
  rw [leftPt, ← add_div, ← add_one_mul, le_div_iff₀ h2]
  calc s * 2 ^ n = (s * 2 ^ n / t) * t := by field_simp
    _ ≤ (((leftIdx t n s : ℕ) : ℝ) + 1) * t := mul_le_mul_of_nonneg_right hle ht.le
theorem leftPt_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) (s : ℝ) : 0 ≤ leftPt t n s := by
  unfold leftPt
  positivity
theorem leftIdx_lt {t : ℝ} (ht : 0 < t) (n : ℕ) {s : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    leftIdx t n s < 2 ^ n := by
  have hceil : ⌈s * 2 ^ n / t⌉₊ ≤ 2 ^ n := by
    refine Nat.ceil_le.mpr ?_
    rw [Nat.cast_pow, Nat.cast_ofNat, div_le_iff₀ ht]
    calc s * 2 ^ n ≤ t * 2 ^ n := mul_le_mul_of_nonneg_right hst (by positivity)
      _ = 2 ^ n * t := mul_comm _ _
  exact lt_of_lt_of_le (Nat.sub_lt (one_le_ceil ht n hs) Nat.one_pos) hceil
end Grid

end LevyStochCalc.Analysis


