-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionMain_F000
-- name    : LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionMain_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T13:13:32.236362+00:00
-- url     : https://prove2.me/theorems/01492e41-204b-4035-950e-f9041ab22330
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionMain
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionMain. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionIntegrands_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionRepresentative_F001
import Definitions.Def_SourceProof_0049bb13353649b49b0f3d6d

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô–Lévy formula at bounded derivatives, from the solution data

For regular Lipschitz coefficients and a filtration satisfying the usual conditions, a `C²` state
function with bounded time derivative, gradient and Hessian satisfies the Itô–Lévy formula along
a jump diffusion that solves the equation on every window, that carries SDE data and has left
limits at every sample point and every time, or that carries SDE data alone: its increment is the
drift integral, the Brownian integral of `(∇u)ᵀσ`, the compensated integral of `u(x + γ) − u(x)`
and the compensator-drift integral. Every admissibility input of the two stochastic integrals is
derived from the solution data and the coefficient regularity; `multidimIntegral_congr_ae`
transports the Brownian integral between vector integrands agreeing almost everywhere on a
window.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.Picard LevyStochCalc.Ito.BigJump
  LevyStochCalc.Probability

universe u v

section Main

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (coeffs : JumpDiffusionCoeffs n d E)

/-- The Itô–Lévy formula for a jump diffusion and a jointly `C²` state function with bounded
first and second derivatives, relative to the filtration of the solution's SDE data:
`u(T, X_T) − u(0, X_0)` is the drift integral of `∂ₜu + 𝓛u`, plus the Brownian integral of
`(∇u)ᵀσ`, plus the compensated-Poisson integral of `u(x + γ) − u(x)`, plus the compensator-drift
integral of `u(x + γ) − u(x) − γᵀ∇u`, all along the path. -/
theorem itoLevyFormula_of_boundedDerivs (x₀ : Fin n → ℝ)
    (X : JumpDiffusion W N coeffs x₀) (S : LevyStochCalc.Ito.BigJump.SdeData X)
    [S.ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ 0 ≤ S.ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    (hReg : coeffs.IsRegular ν) {L : ℝ} (hLip : coeffs.IsLipschitz ν L)
    (u : ℝ → (Fin n → ℝ) → ℝ) (hu : ContDiff ℝ 2 (Function.uncurry u))
    {K₀ K₁ K₂ : ℝ} (hK₀ : ∀ s x, |timeDeriv u s x| ≤ K₀)
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁) (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (T : ℝ) (hT : 0 < T) :
    ∀ᵐ ω ∂P,
      u T (X.X T ω) - u 0 (X.X 0 ω)
        = (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
          + MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
              (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
              (fun j => measurable_diffusionIntegrand_path hu hReg.2.1 X.measurable_path j)
              (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hReg.2.1 S.X_prog j)
              (fun j _ hT' => lintegral_sq_diffusionIntegrand_path_lt_top hK₁
                S.σ_meas S.σ_sq j hT') T ω
          + LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
              (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
              (measurable_jumpIncrement_path hu hReg.2.2.1 X.measurable_path)
              (markedProgressivelyMeasurable_jumpIncrement_path hu hReg.2.2.1 S.X_prog)
              (fun _ hT' => lintegral_sq_jumpIncrement_path_lt_top hu hK₁ S.γ_meas S.γ_sq hT')
              T ω
          + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
              compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν := by
  filter_upwards [_root_.Prove2MeSourceProof.h_0049bb13353649b49b0f3d6d W N coeffs x₀ X S hℱ0 hnull hReg.1
    hReg.2.1 hReg.2.2.1 (fun i T' hT' => _root_.Prove2MeSourceProof.h_946b446a671aae16e8dcf40a coeffs hReg hLip
      (fun b => _root_.Prove2MeSourceProof.h_1cfc3aa11ae6a425fc4b5453 X.sup_L2 b) i hT')
    u hu hK₀ hK₁ hK₂ T hT] with ω hω
  linarith
end Main

end LevyStochCalc.Ito.JumpFormula


