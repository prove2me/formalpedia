-- Prove2me | Definitions.Def_SourceProof_01e40aeca919e8d6949db16a
-- name    : SourceProof_01e40aeca919e8d6949db16a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T14:17:45.440889+00:00
-- url     : https://prove2.me/theorems/ec3e068b-b5d9-46a9-a86b-547ef5bff159
-- title:
--   LevyStochCalc source module: SourceProof_01e40aeca919e8d6949db16a
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_sdeData_general_c12` comes from the `LevyStochCalc.Ito.ItoLevyFormulaGeneralC12` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionMainC12_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyFormulaGeneral_F000
import Definitions.Def_SourceProof_5480422f0c02d5366a6c8d44
import Definitions.Def_SourceProof_a1d9b7fbb2e54400e9c93d64
import Definitions.Def_SourceProof_a6b2c2d1839ed980865a4dc9
import Definitions.Def_SourceProof_a73d9c684890e7b4cda92e32

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô–Lévy formula for a jump diffusion and a `C^{1,2}` state function

The Itô–Lévy formula for a state function of class `C^{1,2}` along a jump diffusion, relative to
the filtration of the solution's SDE data, with no bound on the derivatives of the state
function: the only hypotheses beyond the SDE data are the joint measurability of the
coefficients, the window energy of the drift along the path, and the admissibility of the two
derived integrands `(∇u)ᵀσ` and `u(x + γ) − u(x)` together with the integrability of the
compensator drift.

The state function is cut off outside a ball, the bounded-derivative formula for a `C^{1,2}`
state function applies to the cut-off, and every term transfers back on the event that the path
stays in the ball over the window: the continuous side term by term, the jump side as a sum,
through the arrival-time jump relation of the solution. Almost every path stays in some ball.
Since a function that is `C²` jointly in time and state is of class `C^{1,2}`, the formula for a
jointly `C²` state function is a case of the one for a `C^{1,2}` state function.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_sdeData_general_of_leftLim_c12` —
  the residual form along a solution with càdlàg paths at every sample point.
* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_sdeData_general_c12` — the
  residual form along any jump diffusion, through its càdlàg representative.
* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_general_c12` — the four-term form for a
  `C^{1,2}` state function.
* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_general_of_c12` — the four-term form for a
  jointly `C²` state function.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpFormula

open LevyStochCalc.Probability LevyStochCalc.Ito.Setting LevyStochCalc.Ito.JumpSplitting
open LevyStochCalc.Ito.CutoffPath LevyStochCalc.Poisson.Compensated

universe u v

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


theorem _root_.Prove2MeSourceProof.h_01e40aeca919e8d6949db16a (x₀ : Fin n → ℝ)
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
      (u T (X.X T ω) - u 0 (X.X 0 ω)
        - (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
        - MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
            (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
            (fun j => measurable_diffusionIntegrand_path_c12 hu hσmeas X.measurable_path j)
            (fun j => progressivelyMeasurable_diffusionIntegrand_path_c12 hu hσmeas S.X_prog j)
            h_sigmaGrad_sq T ω)
      = LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
          (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
          (measurable_jumpIncrement_path_c12 hu hγmeas X.measurable_path)
          (markedProgressivelyMeasurable_jumpIncrement_path_c12 hu hγmeas S.X_prog)
          h_jumpInt_sq T ω
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
  -- the representative with càdlàg paths at every sample point
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
  -- the admissibility inputs transported to the representative
  have hσY : ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖LevyStochCalc.Ito.JumpFormula.diffusionIntegrand u coeffs.σ s (Y s ω) j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun j T' hT' => (LevyStochCalc.Ito.JumpFormula.lintegral_sq_comp_cadlagRep hG0
      (fun s x => LevyStochCalc.Ito.JumpFormula.diffusionIntegrand u coeffs.σ s x j) T').trans_lt (h_sigmaGrad_sq j T' hT')
  have hγY : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖u s (Y s ω + coeffs.γ s (Y s ω) e) - u s (Y s ω)‖₊ : ℝ≥0∞) ^ 2
          ∂ν ∂volume ∂P < ⊤ :=
    fun T' hT' => (LevyStochCalc.Ito.JumpFormula.lintegral_sq_marked_comp_cadlagRep hG0
      (fun s x e => u s (x + coeffs.γ s x e) - u s x) T').trans_lt (h_jumpInt_sq T' hT')
  have hcdY : ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ s (Y s ω) e‖₊ : ℝ≥0∞) ∂ν ∂volume < ⊤ := by
    filter_upwards [h_compDrift_int, hpe] with ω hω hag
    have hrw : (∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ s (Y s ω) e‖₊ : ℝ≥0∞) ∂ν ∂volume)
        = ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e‖₊ : ℝ≥0∞) ∂ν ∂volume :=
      setLIntegral_congr_fun measurableSet_Icc fun s hs => by rw [hag s hs.1]
    rw [hrw]
    exact hω
  -- the formula along the representative
  let XY : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀ :=
    LevyStochCalc.Ito.Picard.jumpDiffusionOfSolvesOn W N S.ℱ S.isBrownian S.isPoisson coeffs x₀ hYm hY0
      (Eventually.of_forall fun ω t _ => hYcad ω t) hYS hYsol
  let SY : LevyStochCalc.Ito.BigJump.SdeData XY :=
    LevyStochCalc.Ito.BigJump.SdeData.ofSolvesOn XY S.ℱ S.isBrownian S.isPoisson hYa hYsol
  haveI : SY.ℱ.IsRightContinuous := ‹S.ℱ.IsRightContinuous›
  have hmain := _root_.Prove2MeSourceProof.h_a1d9b7fbb2e54400e9c93d64 W N coeffs x₀ XY SY
    hℱ0 hnull (fun ω t => (hYcad ω t).1) (fun ω t j => (hYcad ω t).2 j) hμmeas hσmeas hγmeas
    (fun i T' hT' => (LevyStochCalc.Ito.JumpFormula.lintegral_sq_comp_cadlagRep hG0 (fun s x => coeffs.μ s x i) T').trans_lt
      (hμq i T' hT')) u hu T hT hσY hγY hcdY
  -- the four terms read the path only up to a null set
  have hBro := _root_.Prove2MeSourceProof.h_a6b2c2d1839ed980865a4dc9 W S.ℱ S.isBrownian
    (fun s ω => LevyStochCalc.Ito.JumpFormula.diffusionIntegrand u coeffs.σ s (Y s ω))
    (fun s ω => LevyStochCalc.Ito.JumpFormula.diffusionIntegrand u coeffs.σ s (X.X s ω))
    (fun j => LevyStochCalc.Ito.JumpFormula.measurable_diffusionIntegrand_path_c12 hu hσmeas hYm j)
    (fun j => LevyStochCalc.Ito.JumpFormula.progressivelyMeasurable_diffusionIntegrand_path_c12 hu hσmeas hYa j)
    hσY
    (fun j => LevyStochCalc.Ito.JumpFormula.measurable_diffusionIntegrand_path_c12 hu hσmeas X.measurable_path j)
    (fun j => LevyStochCalc.Ito.JumpFormula.progressivelyMeasurable_diffusionIntegrand_path_c12 hu hσmeas S.X_prog j)
    h_sigmaGrad_sq
    hT (by
      filter_upwards [hYX] with ω hω
      filter_upwards [hω] with s hs
      exact congrArg (LevyStochCalc.Ito.JumpFormula.diffusionIntegrand u coeffs.σ s) hs)
  have hCmp := _root_.Prove2MeSourceProof.h_cda07e33f55ed24b65eb1212 N S.ℱ S.isPoisson
    (fun ω' s e => u s (Y s ω' + coeffs.γ s (Y s ω') e) - u s (Y s ω'))
    (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
    (LevyStochCalc.Ito.JumpFormula.measurable_jumpIncrement_path_c12 hu hγmeas hYm)
    (LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_jumpIncrement_path_c12 hu hγmeas hYa)
    hγY
    (LevyStochCalc.Ito.JumpFormula.measurable_jumpIncrement_path_c12 hu hγmeas X.measurable_path)
    (LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_jumpIncrement_path_c12 hu hγmeas S.X_prog)
    h_jumpInt_sq
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


