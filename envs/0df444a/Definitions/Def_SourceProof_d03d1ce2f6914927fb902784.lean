-- Prove2me | Definitions.Def_SourceProof_d03d1ce2f6914927fb902784
-- name    : SourceProof_d03d1ce2f6914927fb902784
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:07:10.843212+00:00
-- url     : https://prove2.me/theorems/404ee70b-8e8b-490b-89d4-078fb63b3390
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.integral_sq_sum_of_condExp_eq_zero
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_MartingaleDifference_F000

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

include h𝒢le h𝒢mono hY hYmeas hYcond in

theorem _root_.Prove2MeSourceProof.h_d03d1ce2f6914927fb902784 (n : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P
      = ∑ i ∈ Finset.range n, ∫ ω, (Y i ω) ^ 2 ∂P := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hSmem := LevyStochCalc.Probability.memLp_sum_range Y hY n
    have hSint : Integrable (fun ω => (∑ i ∈ Finset.range n, Y i ω) ^ 2) P := by
      have hfun : (fun ω => (∑ i ∈ Finset.range n, Y i ω) ^ 2)
          = (fun ω => ∑ i ∈ Finset.range n, Y i ω)
            * (fun ω => ∑ i ∈ Finset.range n, Y i ω) := by
        funext ω; rw [pow_two]; rfl
      rw [hfun]
      exact hSmem.integrable_mul hSmem
    have hYint : Integrable (fun ω => (Y n ω) ^ 2) P := by
      have hfun : (fun ω => (Y n ω) ^ 2) = Y n * Y n := by
        funext ω; rw [pow_two]; rfl
      rw [hfun]
      exact (hY n).integrable_mul (hY n)
    have hcross : Integrable (fun ω => (∑ i ∈ Finset.range n, Y i ω) * Y n ω) P :=
      hSmem.integrable_mul (hY n)
    have hexp : ∀ ω, (∑ i ∈ Finset.range (n + 1), Y i ω) ^ 2
        = (∑ i ∈ Finset.range n, Y i ω) ^ 2
          + 2 * ((∑ i ∈ Finset.range n, Y i ω) * Y n ω) + (Y n ω) ^ 2 := by
      intro ω
      rw [Finset.sum_range_succ]
      ring
    have hsum2 : Integrable
        (fun ω => (∑ i ∈ Finset.range n, Y i ω) ^ 2
          + 2 * ((∑ i ∈ Finset.range n, Y i ω) * Y n ω)) P :=
      hSint.add (hcross.const_mul 2)
    simp_rw [hexp]
    rw [integral_add hsum2 hYint, integral_add hSint (hcross.const_mul 2),
      integral_const_mul, LevyStochCalc.Probability.integral_sum_mul_of_condExp_eq_zero 𝒢 h𝒢le h𝒢mono Y hY hYmeas hYcond n,
      Finset.sum_range_succ, ih]
    ring
end MartingaleDifference

end LevyStochCalc.Probability


