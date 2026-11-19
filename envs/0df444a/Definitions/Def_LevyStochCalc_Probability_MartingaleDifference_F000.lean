-- Prove2me | Definitions.Def_LevyStochCalc_Probability_MartingaleDifference_F000
-- name    : LevyStochCalc_Probability_MartingaleDifference_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:06:28.763206+00:00
-- url     : https://prove2.me/theorems/a35754b6-37e3-43eb-bec3-dfbfc38cc667
-- title:
--   Source declarations: LevyStochCalc.Probability.MartingaleDifference
-- statement:
--   Source-preserving Lean declaration bundle from LevyStochCalc.Probability.MartingaleDifference, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Probability.Martingale.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Orthogonality of martingale differences

A finite family `Y 0, …, Y (n-1)` in `L²` with `Y k` measurable for `𝒢 (k+1)` and
`𝔼[Y k | 𝒢 k] = 0` is orthogonal, so the second moment of the sum is the sum of the second
moments.

## Main statements

* `LevyStochCalc.Probability.integral_sum_mul_of_condExp_eq_zero` — a partial sum is orthogonal
  to the next difference.
* `LevyStochCalc.Probability.integral_sq_sum_of_condExp_eq_zero` — the second moment of a sum of
  martingale differences is the sum of the second moments.
-/

namespace LevyStochCalc.Probability

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

section MartingaleDifference

variable (𝒢 : ℕ → MeasurableSpace Ω) (h𝒢le : ∀ k, 𝒢 k ≤ mΩ) (h𝒢mono : Monotone 𝒢)
  (Y : ℕ → Ω → ℝ) (hY : ∀ k, MemLp (Y k) 2 P)
  (hYmeas : ∀ k, StronglyMeasurable[𝒢 (k + 1)] (Y k))
  (hYcond : ∀ k, P[Y k | 𝒢 k] =ᵐ[P] 0)

include hY in
omit [IsProbabilityMeasure P] in
/-- A partial sum of martingale differences lies in `L²`. -/
theorem memLp_sum_range (n : ℕ) : MemLp (fun ω => ∑ i ∈ Finset.range n, Y i ω) 2 P :=
  memLp_finsetSum _ fun i _ => hY i
include h𝒢mono hYmeas in
/-- A partial sum of martingale differences is measurable for the σ-algebra at its top index. -/
theorem stronglyMeasurable_sum_range (n : ℕ) :
    StronglyMeasurable[𝒢 n] (fun ω => ∑ i ∈ Finset.range n, Y i ω) := by
  refine @Finset.stronglyMeasurable_fun_sum Ω ℝ _ _ _ (𝒢 n) _ _ _ fun i hi => ?_
  rw [Finset.mem_range] at hi
  exact (hYmeas i).mono (h𝒢mono hi)
include h𝒢le h𝒢mono hY hYmeas hYcond in
/-- A partial sum of martingale differences is orthogonal to the next difference. -/
theorem integral_sum_mul_of_condExp_eq_zero (n : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range n, Y i ω) * Y n ω ∂P = 0 := by
  haveI : SigmaFinite (P.trim (h𝒢le n)) := by
    haveI : IsFiniteMeasure (P.trim (h𝒢le n)) :=
      ⟨by rw [MeasureTheory.trim_measurableSet_eq (h𝒢le n) MeasurableSet.univ]
          exact measure_lt_top P Set.univ⟩
    infer_instance
  have hSmem := memLp_sum_range Y hY n
  have hSmeas := stronglyMeasurable_sum_range 𝒢 h𝒢mono Y hYmeas n
  have hprod : Integrable
      ((fun ω => ∑ i ∈ Finset.range n, Y i ω) * Y n) P := hSmem.integrable_mul (hY n)
  have hkey := MeasureTheory.condExp_mul_of_stronglyMeasurable_left (m := 𝒢 n) hSmeas hprod
    ((hY n).integrable (by norm_num))
  have hzero : P[(fun ω => ∑ i ∈ Finset.range n, Y i ω) * Y n | 𝒢 n] =ᵐ[P] 0 := by
    filter_upwards [hkey, hYcond n] with ω hω hω'
    rw [hω, Pi.mul_apply, hω', Pi.zero_apply, mul_zero]
  calc ∫ ω, (∑ i ∈ Finset.range n, Y i ω) * Y n ω ∂P
      = ∫ ω, ((fun ω => ∑ i ∈ Finset.range n, Y i ω) * Y n) ω ∂P := rfl
    _ = ∫ ω, (P[(fun ω => ∑ i ∈ Finset.range n, Y i ω) * Y n | 𝒢 n]) ω ∂P :=
        (MeasureTheory.integral_condExp (h𝒢le n)).symm
    _ = 0 := by rw [integral_congr_ae hzero]; simp
end MartingaleDifference

end LevyStochCalc.Probability


