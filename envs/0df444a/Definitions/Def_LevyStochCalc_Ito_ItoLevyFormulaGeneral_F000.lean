-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoLevyFormulaGeneral_F000
-- name    : LevyStochCalc_Ito_ItoLevyFormulaGeneral_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T13:20:21.283297+00:00
-- url     : https://prove2.me/theorems/f2241793-6528-4e1f-b72a-f4e2793b7117
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoLevyFormulaGeneral
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoLevyFormulaGeneral. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CutoffGlobalBounds_F000
import Definitions.Def_LevyStochCalc_Ito_CutoffJumpTransfer_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionIntegrands_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionMain_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionRepresentative_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionRepresentative_F001
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingRemainderVanishing_F000
import Definitions.Def_LevyStochCalc_Ito_PicardWellPosed_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.MeasurableIntegral

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô–Lévy formula for a jump diffusion

The Itô–Lévy formula for a jointly `C²` state function of a jump diffusion, relative to the
filtration of the solution's SDE data, with no bound on the derivatives of the state function:
the only hypotheses beyond the SDE data are the joint measurability of the coefficients, the
window energy of the drift along the path, and the admissibility of the two derived integrands
`(∇u)ᵀσ` and `u(x + γ) − u(x)` together with the integrability of the compensator drift.

The proof cuts the state function off outside a ball, applies the bounded-derivative formula to
the cut-off, and transfers every term back on the event that the path stays in the ball over the
window: the continuous side term by term, the jump side as a sum, through the arrival-time jump
relation of the solution. Almost every path stays in some ball.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_sdeData_general_of_leftLim` —
  the residual form along a solution with càdlàg paths at every sample point.
* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_sdeData_general` — the residual
  form along any jump diffusion, through its càdlàg representative.
* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_general` — the four-term form.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpFormula

open LevyStochCalc.Probability LevyStochCalc.Ito.Setting LevyStochCalc.Ito.JumpSplitting
open LevyStochCalc.Ito.CutoffPath LevyStochCalc.Poisson.Compensated

universe u v

section Transfers

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} {n : ℕ}

/-- A marked integrand read along the left limits of an almost surely càdlàg path has the same
window energy as read along the path. -/
theorem lintegral_sq_marked_leftLimPathAt_eq {X : ℝ → Ω → Fin n → ℝ}
    (hcad : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => X s ω i) (𝓝[<] t) (𝓝 L))
    (F : ℝ → (Fin n → ℝ) → E → ℝ) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖F s (leftLimPathAt X s ω) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖F s (X s ω) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_countable_setOf_pos_ne_leftLimPathAt X hcad] with ω hω
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_eq_of_countable_ne hω T] with s hs
  rw [hs]
/-- An integrand of the time and the state read along the left limits of an almost surely càdlàg
path has the same window energy as read along the path. -/
theorem lintegral_sq_leftLimPathAt_eq {X : ℝ → Ω → Fin n → ℝ}
    (hcad : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => X s ω i) (𝓝[<] t) (𝓝 L))
    (f : ℝ → (Fin n → ℝ) → ℝ) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s (leftLimPathAt X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s (X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_countable_setOf_pos_ne_leftLimPathAt X hcad] with ω hω
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_eq_of_countable_ne hω T] with s hs
  rw [hs]
variable [SigmaFinite ν]

end Transfers

section Main

open LevyStochCalc.Brownian.Multidim LevyStochCalc.Ito.JumpFormulaCutoff
open LevyStochCalc.Ito.Picard (SolvesOn solvesOn_of_eqn jumpDiffusionOfSolvesOn
  )

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (coeffs : JumpDiffusionCoeffs n d E)

end Main

end LevyStochCalc.Ito.JumpFormula


