-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_OrthonormalMarkProfile_F000
-- name    : LevyStochCalc_Poisson_OrthonormalMarkProfile_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T21:59:24.300297+00:00
-- url     : https://prove2.me/theorems/b7970557-7e32-4b88-b85b-01f3b6e5910f
-- title:
--   Source declarations: LevyStochCalc.Poisson.OrthonormalMarkProfile
-- statement:
--   Source-preserving Lean declaration bundle from LevyStochCalc.Poisson.OrthonormalMarkProfile, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Bounded orthonormal mark profiles from disjoint mark sets

The indicator of a mark set `B` of nonzero finite intensity, scaled by `ν(B)^{-1/2}`, is bounded,
square integrable and of unit norm in `L²(ν)`, and the scaled indicators of pairwise-disjoint mark
sets are orthogonal. Pairwise-disjoint mark sets of nonzero finite intensity therefore give a
bounded square-integrable family of mark profiles orthonormal in `L²(ν)`. On the real line with
Lebesgue intensity the unit intervals `(r, r + 1]` are such sets, so a family of `q` such profiles
exists for every `q`.

## Main definitions

* `LevyStochCalc.Poisson.normalisedIndicator`: the indicator of a mark set scaled by the inverse
  square root of its intensity.

## Main statements

* `LevyStochCalc.Poisson.integral_normalisedIndicator_mul`: the scaled indicators of
  pairwise-disjoint mark sets are orthonormal in `L²(ν)`.
* `LevyStochCalc.Poisson.exists_orthonormal_profile_of_disjoint`: pairwise-disjoint mark sets of
  nonzero finite intensity give a bounded square-integrable orthonormal family.
* `LevyStochCalc.Poisson.exists_orthonormal_profile_volume`: for Lebesgue intensity on the real
  line such a family exists in every size.
-/

universe v

namespace LevyStochCalc.Poisson

open MeasureTheory
open scoped ENNReal

section Indicator

variable {E : Type v} [MeasurableSpace E] {ν : Measure E}

/-- The indicator of a mark set `B` scaled by `ν(B)^{-1/2}`. -/
noncomputable def normalisedIndicator (ν : Measure E) (B : Set E) : E → ℝ :=
  B.indicator fun _ => (Real.sqrt (ν B).toReal)⁻¹
/-- The scaled indicator of a measurable mark set of finite intensity is square-integrable. -/
theorem memLp_normalisedIndicator {B : Set E} (hB : MeasurableSet B) (hBν : ν B ≠ ⊤) :
    MemLp (normalisedIndicator ν B) 2 ν :=
  memLp_indicator_const 2 hB _ (Or.inr hBν)
/-- The scaled indicator of a mark set `B` is bounded by `ν(B)^{-1/2}`. -/
theorem abs_normalisedIndicator_le (ν : Measure E) (B : Set E) (e : E) :
    |normalisedIndicator ν B e| ≤ (Real.sqrt (ν B).toReal)⁻¹ := by
  have h0 : 0 ≤ (Real.sqrt (ν B).toReal)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  unfold normalisedIndicator
  by_cases he : e ∈ B
  · rw [Set.indicator_of_mem he, abs_of_nonneg h0]
  · rw [Set.indicator_of_notMem he, abs_zero]
    exact h0
/-- **The scaled indicators of pairwise-disjoint mark sets of nonzero finite intensity are
orthonormal in `L²(ν)`.** -/
theorem integral_normalisedIndicator_mul {q : ℕ} (B : Fin q → Set E)
    (hBm : ∀ r, MeasurableSet (B r)) (hBd : Pairwise fun r r' => Disjoint (B r) (B r'))
    (hB0 : ∀ r, ν (B r) ≠ 0) (hBν : ∀ r, ν (B r) ≠ ⊤) (r r' : Fin q) :
    ∫ e, normalisedIndicator ν (B r) e * normalisedIndicator ν (B r') e ∂ν
      = if r = r' then 1 else 0 := by
  split_ifs with h
  · subst h
    have hsq : (fun e => normalisedIndicator ν (B r) e * normalisedIndicator ν (B r) e)
        = (B r).indicator fun _ => ((ν (B r)).toReal)⁻¹ := by
      funext e
      unfold normalisedIndicator
      by_cases he : e ∈ B r
      · rw [Set.indicator_of_mem he, Set.indicator_of_mem he, ← mul_inv,
          Real.mul_self_sqrt ENNReal.toReal_nonneg]
      · rw [Set.indicator_of_notMem he, Set.indicator_of_notMem he, mul_zero]
    rw [hsq, integral_indicator_const _ (hBm r), smul_eq_mul, measureReal_def,
      mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hB0 r, hBν r⟩)]
  · have hzero : (fun e => normalisedIndicator ν (B r) e * normalisedIndicator ν (B r') e)
        = fun _ => (0 : ℝ) := by
      funext e
      unfold normalisedIndicator
      by_cases he : e ∈ B r
      · rw [Set.indicator_of_notMem (Set.disjoint_left.mp (hBd h) he), mul_zero]
      · rw [Set.indicator_of_notMem he, zero_mul]
    rw [hzero, integral_zero]
/-- **Pairwise-disjoint mark sets of nonzero finite intensity give a bounded square-integrable
family of mark profiles orthonormal in `L²(ν)`.** -/
theorem exists_orthonormal_profile_of_disjoint {q : ℕ} (B : Fin q → Set E)
    (hBm : ∀ r, MeasurableSet (B r)) (hBd : Pairwise fun r r' => Disjoint (B r) (B r'))
    (hB0 : ∀ r, ν (B r) ≠ 0) (hBν : ∀ r, ν (B r) ≠ ⊤) :
    ∃ ζ : Fin q → E → ℝ, (∀ r, MemLp (ζ r) 2 ν) ∧ (∀ r, ∃ C, ∀ e, |ζ r e| ≤ C) ∧
      ∀ r r', ∫ e, ζ r e * ζ r' e ∂ν = if r = r' then 1 else 0 :=
  ⟨fun r => normalisedIndicator ν (B r), fun r => memLp_normalisedIndicator (hBm r) (hBν r),
    fun r => ⟨_, abs_normalisedIndicator_le ν (B r)⟩,
    integral_normalisedIndicator_mul B hBm hBd hB0 hBν⟩
end Indicator

/-- **For Lebesgue intensity on the real line, a bounded square-integrable family of `q` mark
profiles orthonormal in `L²` exists for every `q`**: the scaled indicators of the unit intervals
`(r, r + 1]`. -/
theorem exists_orthonormal_profile_volume (q : ℕ) :
    ∃ ζ : Fin q → ℝ → ℝ, (∀ r, MemLp (ζ r) 2 volume) ∧ (∀ r, ∃ C, ∀ e, |ζ r e| ≤ C) ∧
      ∀ r r', ∫ e, ζ r e * ζ r' e = if r = r' then 1 else 0 := by
  set B : Fin q → Set ℝ := fun r => Set.Ioc (((r : ℕ) : ℤ) : ℝ) ((((r : ℕ) : ℤ) : ℝ) + 1)
    with hB
  have hvol : ∀ r, volume (B r) = 1 := fun r => by
    rw [hB, Real.volume_Ioc, add_sub_cancel_left, ENNReal.ofReal_one]
  refine exists_orthonormal_profile_of_disjoint B (fun _ => measurableSet_Ioc) ?_
    (fun r => by rw [hvol r]; exact one_ne_zero) (fun r => by rw [hvol r]; exact ENNReal.one_ne_top)
  have hinj : Function.Injective fun r : Fin q => ((r : ℕ) : ℤ) := fun r r' h =>
    Fin.ext (Int.ofNat_inj.mp h)
  exact (Set.pairwise_disjoint_Ioc_intCast ℝ).comp_of_injective hinj
end LevyStochCalc.Poisson


