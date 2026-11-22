-- Prove2me | Definitions.Def_SourceProof_190b24feee30508af1f5a5e6
-- name    : SourceProof_190b24feee30508af1f5a5e6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T10:12:09.711731+00:00
-- url     : https://prove2.me/theorems/c961f8ed-d068-4e95-80e2-9d4c819f45a0
-- title:
--   LevyStochCalc source module: SourceProof_190b24feee30508af1f5a5e6
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.abs_mixedDriftIntegrand_le` comes from the `LevyStochCalc.Ito.ItoLevyMixedBounds` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_BigJumpPathBridge_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaContinuity_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaMixed_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaTaylorBounds_F000
import Definitions.Def_LevyStochCalc_Ito_LeftLimIntegrandRegularity_F001
import Definitions.Def_LevyStochCalc_Ito_SubsequenceBookkeeping_F000
import Definitions.Def_LevyStochCalc_Ito_TruncatedContinuousPart_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Bounds and admissibility of the mixed integrands

Energy bounds on a bounded window for integrands dominated by finitely many square-integrable
ones, the bounds on the four mixed integrands through the bounded derivatives of the state
function, their continuity in the state, and the progressive measurability of a marked integrand
read at a progressively measurable state.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.lintegral_window_sq_le_of_abs_le`,
  `LevyStochCalc.Ito.JumpFormula.lintegral_window_mark_sq_le_of_abs_le` — energy bounds for
  dominated integrands.
* `LevyStochCalc.Ito.JumpFormula.abs_mixedDriftIntegrand_le`,
  `LevyStochCalc.Ito.JumpFormula.abs_mixedJumpIncrement_le` — bounds on the mixed integrands.
* `LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_time_state_jump` — the triple of
  the time, a progressively measurable state and the jump coefficient along a path is marked
  progressively measurable.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section Norms

end Norms

section Energies

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

end Energies

section MixedBounds

variable {n d : ℕ} {E : Type v} {u : ℝ → (Fin n → ℝ) → ℝ}


theorem _root_.Prove2MeSourceProof.h_190b24feee30508af1f5a5e6 (coeffs : JumpDiffusionCoeffs n d E) {K₀ K₁ K₂ : ℝ}
    (hK₂0 : 0 ≤ K₂) (hK₀ : ∀ s x, |timeDeriv u s x| ≤ K₀)
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁) (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (s : ℝ) (y x : Fin n → ℝ) :
    |mixedDriftIntegrand u coeffs s y x|
      ≤ K₀ + K₁ * ∑ p, |coeffs.μ s x p|
        + (1 / 2) * K₂ * ∑ p, ∑ q, ∑ j, (coeffs.σ s x p j ^ 2 + coeffs.σ s x q j ^ 2) / 2 := by
  unfold LevyStochCalc.Ito.JumpFormula.mixedDriftIntegrand
  have h1 : |∑ p, coeffs.μ s x p * LevyStochCalc.Ito.JumpFormula.gradient u s y p| ≤ K₁ * ∑ p, |coeffs.μ s x p| := by
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hK₁ s y p) (abs_nonneg _)
  have h2 : |(1 / 2) * ∑ p, ∑ q, ∑ j, coeffs.σ s x p j * coeffs.σ s x q j * LevyStochCalc.Ito.JumpFormula.hessian u s y p q|
      ≤ (1 / 2) * K₂ * ∑ p, ∑ q, ∑ j, (coeffs.σ s x p j ^ 2 + coeffs.σ s x q j ^ 2) / 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    have hsq : |coeffs.σ s x p j * coeffs.σ s x q j|
        ≤ (coeffs.σ s x p j ^ 2 + coeffs.σ s x q j ^ 2) / 2 := by
      rw [abs_mul]
      have := two_mul_le_add_sq |coeffs.σ s x p j| |coeffs.σ s x q j|
      rw [sq_abs, sq_abs] at this
      linarith
    calc |coeffs.σ s x p j * coeffs.σ s x q j| * |LevyStochCalc.Ito.JumpFormula.hessian u s y p q|
        ≤ |coeffs.σ s x p j * coeffs.σ s x q j| * K₂ :=
          mul_le_mul_of_nonneg_left (hK₂ s y p q) (abs_nonneg _)
      _ ≤ (coeffs.σ s x p j ^ 2 + coeffs.σ s x q j ^ 2) / 2 * K₂ :=
          mul_le_mul_of_nonneg_right hsq hK₂0
      _ = K₂ * ((coeffs.σ s x p j ^ 2 + coeffs.σ s x q j ^ 2) / 2) := mul_comm _ _
  calc |LevyStochCalc.Ito.JumpFormula.timeDeriv u s y + (∑ p, coeffs.μ s x p * LevyStochCalc.Ito.JumpFormula.gradient u s y p
          + (1 / 2) * ∑ p, ∑ q, ∑ j, coeffs.σ s x p j * coeffs.σ s x q j * LevyStochCalc.Ito.JumpFormula.hessian u s y p q)|
      ≤ |LevyStochCalc.Ito.JumpFormula.timeDeriv u s y| + (|∑ p, coeffs.μ s x p * LevyStochCalc.Ito.JumpFormula.gradient u s y p|
          + |(1 / 2) * ∑ p, ∑ q, ∑ j,
              coeffs.σ s x p j * coeffs.σ s x q j * LevyStochCalc.Ito.JumpFormula.hessian u s y p q|) :=
        (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))
    _ ≤ K₀ + (K₁ * ∑ p, |coeffs.μ s x p|
          + (1 / 2) * K₂ * ∑ p, ∑ q, ∑ j, (coeffs.σ s x p j ^ 2 + coeffs.σ s x q j ^ 2) / 2) :=
        add_le_add (hK₀ s y) (add_le_add h1 h2)
    _ = _ := by ring
end MixedBounds

section MixedContinuity

variable {n d : ℕ} {E : Type v} {u : ℝ → (Fin n → ℝ) → ℝ} {z : ℕ → Fin n → ℝ} {w : Fin n → ℝ}

end MixedContinuity

section Progressive

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]

end Progressive

end LevyStochCalc.Ito.JumpFormula


