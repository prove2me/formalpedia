-- Prove2me | Definitions.Def_SourceProof_5139a599a00e1c333b4d5e92
-- name    : SourceProof_5139a599a00e1c333b4d5e92
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T13:20:53.076571+00:00
-- url     : https://prove2.me/theorems/cf4913da-31ea-4c95-a396-74ce65bc2d3b
-- title:
--   LevyStochCalc source module: SourceProof_5139a599a00e1c333b4d5e92
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.integrableOn_window_univ_of_lintegral_lt_top` comes from the `LevyStochCalc.Ito.ItoLevyFormulaGeneral` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CutoffGlobalBounds_F000
import Definitions.Def_LevyStochCalc_Ito_CutoffJumpTransfer_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionMain_F000
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingRemainderVanishing_F000

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

variable [SigmaFinite ν]


theorem _root_.Prove2MeSourceProof.h_5139a599a00e1c333b4d5e92 {g : ℝ × E → ℝ} (hg : Measurable g) {T : ℝ}
    (hfin : ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖g (s, e)‖₊ : ℝ≥0∞) ∂ν ∂volume < ⊤) :
    IntegrableOn g (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E))
      (LevyStochCalc.Poisson.referenceIntensity ν) := by
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have hm : Measurable fun q : ℝ × E => (‖g q‖₊ : ℝ≥0∞) :=
    hg.nnnorm.coe_nnreal_ennreal
  calc ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E), ‖g q‖ₑ
          ∂(LevyStochCalc.Poisson.referenceIntensity ν)
        = ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E), (‖g q‖₊ : ℝ≥0∞)
          ∂(LevyStochCalc.Poisson.referenceIntensity ν) := by
          simp only [enorm_eq_nnnorm]
      _ = ∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e in Set.univ, (‖g (s, e)‖₊ : ℝ≥0∞) ∂ν ∂volume :=
          LevyStochCalc.Poisson.lintegral_referenceIntensity_window hm Set.univ T
      _ = ∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e, (‖g (s, e)‖₊ : ℝ≥0∞) ∂ν ∂volume := by
          simp only [Measure.restrict_univ]
      _ ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖g (s, e)‖₊ : ℝ≥0∞) ∂ν ∂volume :=
          lintegral_mono_set Set.Ioc_subset_Icc_self
      _ < ⊤ := hfin
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


