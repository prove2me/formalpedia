-- Prove2me | Definitions.Def_SourceProof_e426349f57887b0a338e40ab
-- name    : SourceProof_e426349f57887b0a338e40ab
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T13:02:26.692751+00:00
-- url     : https://prove2.me/theorems/5d8f4c0a-4bed-4d5d-92a7-a902e02f5f15
-- title:
--   LevyStochCalc source module: SourceProof_e426349f57887b0a338e40ab
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_sdeData_of_leftLim` comes from the `LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionMain` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionIntegrands_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionRepresentative_F001
import Definitions.Def_SourceProof_55ca53eaccae9591a8954d60
import Definitions.Def_SourceProof_68143de6ea16052afb9e9c57

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


theorem _root_.Prove2MeSourceProof.h_e426349f57887b0a338e40ab (x₀ : Fin n → ℝ)
    (X : JumpDiffusion W N coeffs x₀) (S : LevyStochCalc.Ito.BigJump.SdeData X)
    [S.ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ 0 ≤ S.ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    (hXleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
    (hμmeas : Measurable (Function.uncurry coeffs.μ))
    (hσmeas : Measurable (Function.uncurry coeffs.σ))
    (hγmeas : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (u : ℝ → (Fin n → ℝ) → ℝ) (hu : ContDiff ℝ 2 (Function.uncurry u))
    {K₀ K₁ K₂ : ℝ} (hK₀ : ∀ s x, |timeDeriv u s x| ≤ K₀)
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁) (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (T : ℝ) (hT : 0 < T) :
    ∀ᵐ ω ∂P,
      (u T (X.X T ω) - u 0 (X.X 0 ω)
        - (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
        - MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
            (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
            (fun j => measurable_diffusionIntegrand_path hu hσmeas X.measurable_path j)
            (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hσmeas S.X_prog j)
            (fun j _ hT' => lintegral_sq_diffusionIntegrand_path_lt_top hK₁
              S.σ_meas S.σ_sq j hT') T ω)
      = LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
          (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
          (measurable_jumpIncrement_path hu hγmeas X.measurable_path)
          (markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog)
          (fun _ hT' => lintegral_sq_jumpIncrement_path_lt_top hu hK₁ S.γ_meas S.γ_sq hT') T ω
        + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
            compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν := by
  have hrc : S.ℱ.rightCont = S.ℱ := Filtration.IsRightContinuous.eq
  have hℱ0' : ∀ t : ℝ, t ≤ 0 → S.ℱ.rightCont 0 ≤ S.ℱ.rightCont t := by
    intro t ht
    rw [hrc]
    exact hℱ0 t ht
  have hXm : Measurable (Function.uncurry X.X) := X.measurable_path
  have hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i) :=
    fun i => ((measurable_pi_apply i).comp hμmeas).comp
      (measurable_snd.prodMk (hXm.comp (measurable_snd.prodMk measurable_fst)))
  have hμp : ∀ i : Fin n,
      LevyStochCalc.Probability.ProgressivelyMeasurable S.ℱ fun ω s => coeffs.μ s (X.X s ω) i :=
    fun i => LevyStochCalc.Ito.Picard.progressivelyMeasurable_comp_state S.X_prog (f := fun s x => coeffs.μ s x i)
      ((measurable_pi_apply i).comp hμmeas)
  exact _root_.Prove2MeSourceProof.h_68143de6ea16052afb9e9c57 W N coeffs x₀ X S hℱ0' hnull
    (fun t => LevyStochCalc.Ito.JumpFormula.measurable_of_progressivelyMeasurable S.ℱ S.X_prog t) hXleft
    hμm hμp hμq hγmeas u hu hK₀ hK₁ hK₂ T hT (LevyStochCalc.Ito.JumpFormula.ae_integrableOn_drift_path hμm hμq T)
    (fun j => LevyStochCalc.Ito.JumpFormula.measurable_diffusionIntegrand_path hu hσmeas hXm j)
    (fun j => LevyStochCalc.Ito.JumpFormula.progressivelyMeasurable_diffusionIntegrand_path hu hσmeas S.X_prog j)
    (fun j _ hT' => LevyStochCalc.Ito.JumpFormula.lintegral_sq_diffusionIntegrand_path_lt_top hK₁ S.σ_meas S.σ_sq j hT')
    (LevyStochCalc.Ito.JumpFormula.measurable_jumpIncrement_path hu hγmeas hXm)
    (LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog)
    (fun _ hT' => LevyStochCalc.Ito.JumpFormula.lintegral_sq_jumpIncrement_path_lt_top hu hK₁ S.γ_meas S.γ_sq hT')
    (_root_.Prove2MeSourceProof.h_55ca53eaccae9591a8954d60 hu hK₂ hγmeas hXm S.γ_meas S.γ_sq hT)
end Main

end LevyStochCalc.Ito.JumpFormula


