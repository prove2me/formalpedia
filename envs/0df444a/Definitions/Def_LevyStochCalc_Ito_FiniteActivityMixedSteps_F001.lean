-- Prove2me | Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedSteps_F001
-- name    : LevyStochCalc_Ito_FiniteActivityMixedSteps_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:34:37.862684+00:00
-- url     : https://prove2.me/theorems/90f7184f-4f5f-4fd4-a971-92296db17f5d
-- title:
--   Source declarations: LevyStochCalc.Ito.FiniteActivityMixedSteps
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.FiniteActivityMixedSteps. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedPrelims_F000
import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedPrelims_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaMeasurableShift_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyMixedBounds_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaChainStopped_F000
import Definitions.Def_LevyStochCalc_Probability_MarkedPredictableComp_F000
import Definitions.Def_LevyStochCalc_Probability_MarkedPredictableComp_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Steps of the finite-activity Itô–Lévy identity in the mixed form

Regularity of the time-augmented path, window integrability of the mixed integrands, the
dictionary identifying the time-augmented drift and quadratic terms with the mixed drift
integrand, and the predictability and admissibility of the mixed jump increment read at the
left limits.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.measurable_uncurry_timeAugProcess`
* `LevyStochCalc.Ito.JumpFormula.measurable_timeAugProcess_adapted`
* `LevyStochCalc.Ito.JumpFormula.tendsto_timeAugProcess_nhdsWithin_gt`
* `LevyStochCalc.Ito.JumpFormula.ae_integrableOn_mixed_window`
* `LevyStochCalc.Ito.JumpFormula.ae_setIntegral_timeAug_eq_mixedDrift`
* `LevyStochCalc.Ito.JumpFormula.admissible_mixedJumpIncrement_leftLim`
* `LevyStochCalc.Ito.JumpFormula.ae_countable_setOf_leftLim_ne_pair`
* `LevyStochCalc.Ito.JumpFormula.markedPredictable_zeroExtPos_mixedJumpIncrement_leftLim`
* `LevyStochCalc.Ito.JumpFormula.lintegral_referenceIntensity_window_ne_top`
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability
open LevyStochCalc.Brownian.Ito LevyStochCalc.Brownian.Multidim LevyStochCalc.Ito.BigJump
open LevyStochCalc.Ito.JumpSplitting

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section TimeAug

variable {Ω : Type u} [MeasurableSpace Ω] {n : ℕ} {y : ℝ → Ω → Fin n → ℝ}

end TimeAug

section Mixed

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : MultidimBrownianMotion P d} {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}

/-- Away from a countable set of times the path and its left limit agree, jointly for a
càdlàg jump diffusion and a càdlàg path with left limits. -/
theorem ae_countable_setOf_leftLim_ne_pair {y : ℝ → Ω → Fin n → ℝ}
    (hy_rc : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => y s ω) (𝓝[>] t) (𝓝 (y t ω)))
    (hy_left : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => y s ω j) (𝓝[<] t) (𝓝 L)) :
    ∀ᵐ ω ∂P, {s : ℝ | 0 < s ∧
      ((leftLimPathAt y s ω, leftLimPathAt X.X s ω) : (Fin n → ℝ) × (Fin n → ℝ))
        ≠ (y s ω, X.X s ω)}.Countable := by
  filter_upwards [X.cadlag_paths] with ω hcad
  exact countable_setOf_pos_ne_pair (Y₁ := leftLimPathAt y) (Z₁ := y)
    (Y₂ := leftLimPathAt X.X) (Z₂ := X.X)
    (countable_setOf_pos_leftLimPathAt_ne (fun t _ => hy_rc ω t) (fun t _ i => hy_left ω t i))
    (countable_setOf_pos_leftLimPathAt_ne (fun t ht => (hcad t ht).1)
      (fun t ht i => (hcad t ht.le).2 i))
end Mixed

end LevyStochCalc.Ito.JumpFormula


