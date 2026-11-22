-- Prove2me | Definitions.Def_SourceProof_fc92219c61092a0b1afac4f9
-- name    : SourceProof_fc92219c61092a0b1afac4f9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T14:03:19.375982+00:00
-- url     : https://prove2.me/theorems/c3e41010-5a81-41f9-8238-11bca047edf9
-- title:
--   LevyStochCalc source module: SourceProof_fc92219c61092a0b1afac4f9
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_general` comes from the `LevyStochCalc.Ito.ItoLevyFormulaGeneral` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CutoffGlobalBounds_F000
import Definitions.Def_LevyStochCalc_Ito_CutoffJumpTransfer_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionMain_F000
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingRemainderVanishing_F000
import Definitions.Def_SourceProof_2a6cbb70b9f9168f8674d298

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


theorem _root_.Prove2MeSourceProof.h_fc92219c61092a0b1afac4f9 (x₀ : Fin n → ℝ)
    (X : JumpDiffusion W N coeffs x₀) (S : LevyStochCalc.Ito.BigJump.SdeData X)
    [S.ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ 0 ≤ S.ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    (hμmeas : Measurable (Function.uncurry coeffs.μ))
    (hσmeas : Measurable (Function.uncurry coeffs.σ))
    (hγmeas : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (u : ℝ → (Fin n → ℝ) → ℝ) (hu : ContDiff ℝ 2 (Function.uncurry u))
    (T : ℝ) (hT : 0 < T)
    (h_sigmaGrad_sq : ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖diffusionIntegrand u coeffs.σ s (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_jumpInt_sq : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖u s (X.X s ω + coeffs.γ s (X.X s ω) e) - u s (X.X s ω)‖₊ : ℝ≥0∞) ^ 2
          ∂ν ∂volume ∂P < ⊤)
    (h_compDrift_int : ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e‖₊ : ℝ≥0∞) ∂ν ∂volume < ⊤) :
    ∀ᵐ ω ∂P,
      u T (X.X T ω) - u 0 (X.X 0 ω)
        = (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
          + MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
              (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
              (fun j => measurable_diffusionIntegrand_path hu hσmeas X.measurable_path j)
              (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hσmeas S.X_prog j)
              h_sigmaGrad_sq T ω
          + LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
              (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
              (measurable_jumpIncrement_path hu hγmeas X.measurable_path)
              (markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog)
              h_jumpInt_sq T ω
          + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
              compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν := by
  filter_upwards [_root_.Prove2MeSourceProof.h_2a6cbb70b9f9168f8674d298 W N coeffs x₀ X S hℱ0 hnull
    hμmeas hσmeas hγmeas hμq u hu T hT h_sigmaGrad_sq h_jumpInt_sq h_compDrift_int] with ω hω
  linarith
end Main

end LevyStochCalc.Ito.JumpFormula


