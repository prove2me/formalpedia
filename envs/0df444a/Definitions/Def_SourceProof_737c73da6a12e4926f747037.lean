-- Prove2me | Definitions.Def_SourceProof_737c73da6a12e4926f747037
-- name    : SourceProof_737c73da6a12e4926f747037
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T13:24:27.592874+00:00
-- url     : https://prove2.me/theorems/706192ce-d14d-4dba-8df6-76cf942bd01d
-- title:
--   LevyStochCalc source module: SourceProof_737c73da6a12e4926f747037
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_sdeData_c12` comes from the `LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionMainC12` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionIntegrandsC12_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionMain_F000
import Definitions.Def_SourceProof_5480422f0c02d5366a6c8d44
import Definitions.Def_SourceProof_a6b2c2d1839ed980865a4dc9
import Definitions.Def_SourceProof_a73d9c684890e7b4cda92e32
import Definitions.Def_SourceProof_c4b9c85226b52e46def25c68

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô–Lévy formula at bounded derivatives from the solution data, for `C^{1,2}` state
functions

For regular Lipschitz coefficients and a filtration satisfying the usual conditions, a `C^{1,2}`
state function with bounded time derivative, gradient and Hessian satisfies the Itô–Lévy formula
along a jump diffusion that solves the equation on every window, that carries SDE data and has
left limits at every sample point and every time, or that carries SDE data alone: its increment
is the drift integral, the Brownian integral of `(∇u)ᵀσ`, the compensated integral of
`u(x + γ) − u(x)` and the compensator-drift integral. Every admissibility input of the two
stochastic integrals is derived from the solution data and the coefficient regularity.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_solvesOn_c12` — the residual
  form along a solution of the equation on every window, for a `C^{1,2}` state function.
* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_sdeData_of_leftLim_c12` — the
  residual form along a solution with left limits at every sample point and every time.
* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_sdeData_c12` — the residual form
  along any jump diffusion carrying SDE data.
* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_of_boundedDerivs_c12` — the four-term form.
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


theorem _root_.Prove2MeSourceProof.h_737c73da6a12e4926f747037 (x₀ : Fin n → ℝ)
    (X : JumpDiffusion W N coeffs x₀) (S : LevyStochCalc.Ito.BigJump.SdeData X)
    [S.ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ 0 ≤ S.ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    (hμmeas : Measurable (Function.uncurry coeffs.μ))
    (hσmeas : Measurable (Function.uncurry coeffs.σ))
    (hγmeas : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (u : ℝ → (Fin n → ℝ) → ℝ) (hu : IsC12 u)
    {K₀ K₁ K₂ : ℝ} (hK₀ : ∀ s x, |timeDeriv u s x| ≤ K₀)
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁) (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (T : ℝ) (hT : 0 < T) :
    ∀ᵐ ω ∂P,
      (u T (X.X T ω) - u 0 (X.X 0 ω)
        - (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
        - MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
            (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
            (fun j => measurable_diffusionIntegrand_path_c12 hu hσmeas X.measurable_path j)
            (fun j => progressivelyMeasurable_diffusionIntegrand_path_c12 hu hσmeas S.X_prog j)
            (fun j _ hT' => lintegral_sq_diffusionIntegrand_path_lt_top hK₁
              S.σ_meas S.σ_sq j hT') T ω)
      = LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
          (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
          (measurable_jumpIncrement_path_c12 hu hγmeas X.measurable_path)
          (markedProgressivelyMeasurable_jumpIncrement_path_c12 hu hγmeas S.X_prog)
          (fun _ hT' => lintegral_sq_jumpIncrement_path_lt_top_c12 hu hK₁ S.γ_meas S.γ_sq hT') T ω
        + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
            compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν := by
  classical
  -- the good set, on which the paths of the jump diffusion are càdlàg
  obtain ⟨G, hGm, hG0, hGp⟩ := LevyStochCalc.Ito.JumpFormula.exists_measurable_full_of_ae (P := P) X.cadlag_paths
  have hG : MeasurableSet[S.ℱ 0] G := by
    simpa using (hnull Gᶜ hGm.compl hG0).compl
  have hXm : Measurable (Function.uncurry X.X) := X.measurable_path
  have hXad : ∀ t : ℝ, Measurable[S.ℱ t] (X.X t) :=
    LevyStochCalc.Ito.JumpFormula.measurable_of_progressivelyMeasurable S.ℱ S.X_prog
  have hXsol : ∀ T' : ℝ,
      LevyStochCalc.Ito.Picard.SolvesOn W N S.ℱ S.isBrownian S.isPoisson coeffs x₀ X.X T' := fun T' =>
    LevyStochCalc.Ito.Picard.solvesOn_of_eqn W N S.ℱ S.isBrownian S.isPoisson coeffs x₀ S.σ_meas S.σ_prog S.σ_sq
      S.γ_meas S.γ_prog S.γ_sq S.sde T'
  -- the representative with left limits at every sample point and every time
  set Y : ℝ → Ω → Fin n → ℝ := LevyStochCalc.Ito.JumpFormula.cadlagRep G X.X with hYdef
  have hYm : Measurable (Function.uncurry Y) := _root_.Prove2MeSourceProof.h_a73d9c684890e7b4cda92e32 hGm hXm
  have hYa : ∀ i : Fin n, LevyStochCalc.Probability.ProgressivelyMeasurable S.ℱ fun ω s => Y s ω i :=
    fun i => LevyStochCalc.Ito.JumpFormula.progressivelyMeasurable_cadlagRep hGp hG hXad i
  have hY0 : ∀ᵐ ω ∂P, Y 0 ω = x₀ := LevyStochCalc.Ito.JumpFormula.ae_cadlagRep_zero hG0 X.initial_value
  have hYcad : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => Y s ω) (𝓝[>] t) (𝓝 (Y t ω))
      ∧ ∀ i : Fin n, ∃ ℓ : ℝ, Tendsto (fun s => Y s ω i) (𝓝[<] t) (𝓝 ℓ) :=
    fun ω t => LevyStochCalc.Ito.JumpFormula.cadlagRep_cadlag hGp ω t
  have hYS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ :=
    fun T' hT' => by
      rw [hYdef, LevyStochCalc.Ito.JumpFormula.lintegral_iSup_cadlagRep hG0]
      exact X.sup_L2 T' hT'
  have hYsol : ∀ T' : ℝ, LevyStochCalc.Ito.Picard.SolvesOn W N S.ℱ S.isBrownian S.isPoisson coeffs x₀ Y T' := fun T' =>
    _root_.Prove2MeSourceProof.h_5480422f0c02d5366a6c8d44 W N S.ℱ S.isBrownian S.isPoisson coeffs hGm hG0 hnull hσmeas hγmeas
      S.σ_sq S.γ_sq hXm S.X_prog X.initial_value hGp hXsol T'
  have hpe : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → Y s ω = X.X s ω :=
    LevyStochCalc.Ito.JumpFormula.ae_forall_cadlagRep_eq (P := P) hG0
  have hYX : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), Y s ω = X.X s ω := by
    filter_upwards [hpe] with ω hω
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hω s hs.1
  -- the formula along the representative
  let XY : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀ :=
    LevyStochCalc.Ito.Picard.jumpDiffusionOfSolvesOn W N S.ℱ S.isBrownian S.isPoisson coeffs x₀ hYm hY0
      (Eventually.of_forall fun ω t _ => hYcad ω t) hYS hYsol
  let SY : LevyStochCalc.Ito.BigJump.SdeData XY :=
    LevyStochCalc.Ito.BigJump.SdeData.ofSolvesOn XY S.ℱ S.isBrownian S.isPoisson hYa hYsol
  haveI : SY.ℱ.IsRightContinuous := ‹S.ℱ.IsRightContinuous›
  have hmain := _root_.Prove2MeSourceProof.h_c4b9c85226b52e46def25c68 W N coeffs x₀ XY SY
    hℱ0 hnull (fun ω t j => (hYcad ω t).2 j) hμmeas hσmeas hγmeas
    (fun i T' hT' => (LevyStochCalc.Ito.JumpFormula.lintegral_sq_comp_cadlagRep hG0 (fun s x => coeffs.μ s x i) T').trans_lt
      (hμq i T' hT')) u hu hK₀ hK₁ hK₂ T hT
  -- the four terms read the path only up to a null set
  have hBro := _root_.Prove2MeSourceProof.h_a6b2c2d1839ed980865a4dc9 W S.ℱ S.isBrownian
    (fun s ω => LevyStochCalc.Ito.JumpFormula.diffusionIntegrand u coeffs.σ s (Y s ω))
    (fun s ω => LevyStochCalc.Ito.JumpFormula.diffusionIntegrand u coeffs.σ s (X.X s ω))
    (fun j => LevyStochCalc.Ito.JumpFormula.measurable_diffusionIntegrand_path_c12 hu hσmeas hYm j)
    (fun j => LevyStochCalc.Ito.JumpFormula.progressivelyMeasurable_diffusionIntegrand_path_c12 hu hσmeas hYa j)
    (fun j _ hT' => LevyStochCalc.Ito.JumpFormula.lintegral_sq_diffusionIntegrand_path_lt_top hK₁
      (hYsol 0).h_σ_meas (hYsol 0).h_σ_sq j hT')
    (fun j => LevyStochCalc.Ito.JumpFormula.measurable_diffusionIntegrand_path_c12 hu hσmeas X.measurable_path j)
    (fun j => LevyStochCalc.Ito.JumpFormula.progressivelyMeasurable_diffusionIntegrand_path_c12 hu hσmeas S.X_prog j)
    (fun j _ hT' => LevyStochCalc.Ito.JumpFormula.lintegral_sq_diffusionIntegrand_path_lt_top hK₁ S.σ_meas S.σ_sq j hT')
    hT (by
      filter_upwards [hYX] with ω hω
      filter_upwards [hω] with s hs
      exact congrArg (LevyStochCalc.Ito.JumpFormula.diffusionIntegrand u coeffs.σ s) hs)
  have hCmp := _root_.Prove2MeSourceProof.h_cda07e33f55ed24b65eb1212 N S.ℱ S.isPoisson
    (fun ω' s e => u s (Y s ω' + coeffs.γ s (Y s ω') e) - u s (Y s ω'))
    (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
    (LevyStochCalc.Ito.JumpFormula.measurable_jumpIncrement_path_c12 hu hγmeas hYm)
    (LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_jumpIncrement_path_c12 hu hγmeas hYa)
    (fun _ hT' => LevyStochCalc.Ito.JumpFormula.lintegral_sq_jumpIncrement_path_lt_top_c12 hu hK₁ (hYsol 0).h_γ_meas
      (hYsol 0).h_γ_sq hT')
    (LevyStochCalc.Ito.JumpFormula.measurable_jumpIncrement_path_c12 hu hγmeas X.measurable_path)
    (LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_jumpIncrement_path_c12 hu hγmeas S.X_prog)
    (fun _ hT' => LevyStochCalc.Ito.JumpFormula.lintegral_sq_jumpIncrement_path_lt_top_c12 hu hK₁ S.γ_meas S.γ_sq hT')
    hT (by
      filter_upwards [hYX] with ω hω
      filter_upwards [hω] with s hs
      exact congrArg (fun x => fun e => u s (x + coeffs.γ s x e) - u s x) hs)
  filter_upwards [hmain, hBro, hCmp, hpe] with ω hω hbro hcmp hag
  have hdr : (∫ s in Set.Icc (0 : ℝ) T, LevyStochCalc.Ito.JumpFormula.driftIntegrand u coeffs s (Y s ω))
      = ∫ s in Set.Icc (0 : ℝ) T, LevyStochCalc.Ito.JumpFormula.driftIntegrand u coeffs s (X.X s ω) :=
    setIntegral_congr_fun measurableSet_Icc fun s hs =>
      congrArg (LevyStochCalc.Ito.JumpFormula.driftIntegrand u coeffs s) (hag s hs.1)
  have hcd : (∫ s in Set.Icc (0 : ℝ) T, ∫ e, LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ s (Y s ω) e ∂ν)
      = ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
          LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν :=
    setIntegral_congr_fun measurableSet_Icc fun s hs =>
      congrArg (fun x => ∫ e, LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ s x e ∂ν) (hag s hs.1)
  rw [← hdr, ← hbro, ← hcmp, ← hcd, ← hag T hT.le, ← hag 0 le_rfl]
  exact hω
end Main

end LevyStochCalc.Ito.JumpFormula


