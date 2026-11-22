-- Prove2me | Definitions.Def_SourceProof_e96d99bc7b0b8d11653fb128
-- name    : SourceProof_e96d99bc7b0b8d11653fb128
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T13:27:57.582165+00:00
-- url     : https://prove2.me/theorems/7f054c78-0857-47ea-a48c-e0488a6ca70f
-- title:
--   LevyStochCalc source module: SourceProof_e96d99bc7b0b8d11653fb128
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_sdeData_general_of_leftLim` comes from the `LevyStochCalc.Ito.ItoLevyFormulaGeneral` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyFormulaGeneral_F000
import Definitions.Def_SourceProof_496c4ae1aa7bbf54a2f228c6
import Definitions.Def_SourceProof_5139a599a00e1c333b4d5e92
import Definitions.Def_SourceProof_55ca53eaccae9591a8954d60
import Definitions.Def_SourceProof_603587851148bdb09758c484
import Definitions.Def_SourceProof_749cad79fcd6f296f70d2bbd
import Definitions.Def_SourceProof_78fb938706430c33723b814c
import Definitions.Def_SourceProof_e426349f57887b0a338e40ab

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


theorem _root_.Prove2MeSourceProof.h_e96d99bc7b0b8d11653fb128 (x₀ : Fin n → ℝ)
    (X : JumpDiffusion W N coeffs x₀) (S : LevyStochCalc.Ito.BigJump.SdeData X)
    [S.ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ 0 ≤ S.ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    (hXright : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => X.X s ω) (𝓝[>] t) (𝓝 (X.X t ω)))
    (hXleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
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
      (u T (X.X T ω) - u 0 (X.X 0 ω)
        - (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
        - MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
            (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
            (fun j => measurable_diffusionIntegrand_path hu hσmeas X.measurable_path j)
            (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hσmeas S.X_prog j)
            h_sigmaGrad_sq T ω)
      = LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
          (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
          (measurable_jumpIncrement_path hu hγmeas X.measurable_path)
          (markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog)
          h_jumpInt_sq T ω
        + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
            compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν := by
  classical
  have hXm : Measurable (Function.uncurry X.X) := X.measurable_path
  have hXm' : Measurable fun q : ℝ × Ω => X.X q.1 q.2 := hXm
  have hXadapt : ∀ t : ℝ, Measurable[S.ℱ t] (X.X t) :=
    LevyStochCalc.Ito.JumpFormula.measurable_of_progressivelyMeasurable S.ℱ S.X_prog
  have hadapt : Adapted S.ℱ X.X := hXadapt
  have hXcad := X.cadlag_paths
  have hcount := LevyStochCalc.Ito.JumpSplitting.ae_countable_setOf_pos_ne_leftLimPathAt X.X hXcad
  -- the left-limit path
  have hΛm : Measurable fun q : ℝ × Ω => LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X q.1 q.2 :=
    LevyStochCalc.Ito.JumpSplitting.measurable_uncurry_leftLimPathAt hXm' hXleft
  have hΛp : ∀ i : Fin n, LevyStochCalc.Probability.ProgressivelyMeasurable S.ℱ fun ω s => LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X s ω i :=
    fun i => LevyStochCalc.Ito.JumpSplitting.progressivelyMeasurable_leftLimPathAt hℱ0 hXadapt hXleft i
  -- the drift along the path
  have hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i) :=
    fun i => ((measurable_pi_apply i).comp hμmeas).comp
      (measurable_snd.prodMk (hXm.comp (measurable_snd.prodMk measurable_fst)))
  have hμp : ∀ i : Fin n, LevyStochCalc.Probability.ProgressivelyMeasurable S.ℱ fun ω s => coeffs.μ s (X.X s ω) i :=
    fun i => LevyStochCalc.Ito.Picard.progressivelyMeasurable_comp_state S.X_prog
      (f := fun s x => coeffs.μ s x i) ((measurable_pi_apply i).comp hμmeas)
  -- the jump coefficient along the left limits
  have hγmL : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E =>
      coeffs.γ p.2.1 (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X p.2.1 p.1) p.2.2 i :=
    fun i => ((measurable_pi_apply i).comp hγmeas).comp
      ((measurable_fst.comp measurable_snd).prodMk
        ((hΛm.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)).prodMk
          (measurable_snd.comp measurable_snd)))
  have hγpL : ∀ i : Fin n, LevyStochCalc.Probability.MarkedProgressivelyMeasurable S.ℱ
      fun ω s e => coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X s ω) e i :=
    fun i => _root_.Prove2MeSourceProof.h_e745eea003d521dc58279648 hΛp
      (F := fun s x e => coeffs.γ s x e i) ((measurable_pi_apply i).comp hγmeas)
  have hγqL : ∀ (i : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
    fun i T' hT' => (LevyStochCalc.Ito.JumpFormula.lintegral_sq_marked_leftLimPathAt_eq hXcad
      (fun s x e => coeffs.γ s x e i) T').trans_lt (S.γ_sq i T' hT')
  have hpredL : ∀ i : Fin n, LevyStochCalc.Probability.MarkedPredictable S.ℱ ν
      (LevyStochCalc.Ito.JumpFormula.zeroExtPos fun ω s e => coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X s ω) e i) :=
    fun i => _root_.Prove2MeSourceProof.h_5650dc54a894019ea9a2b291 X.X S.ℱ hXadapt
      (fun ω t _ j => hXleft ω t j) (ν := ν) (F := fun s x e => coeffs.γ s x e i)
      ((measurable_pi_apply i).comp hγmeas)
  -- the arrival-time jump relation at every level of the spanning sequence
  have hjump : ∀ j : ℕ, ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E), StrictMono θ ∧
      (∀ k, θ k ∈ Set.Ioc (0 : ℝ) T ∧ ε k ∈ spanningSets ν j) ∧
      (∀ g : ℝ × E → ℝ, ∫ p in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν j, g p ∂(N.N ω)
        = ∑ k : Fin K, g (θ k, ε k)) ∧
      ∀ k : Fin K,
        X.X (θ k) ω
          = LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X (θ k) ω
            + coeffs.γ (θ k) (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X (θ k) ω) (ε k) :=
    fun j => _root_.Prove2MeSourceProof.h_603587851148bdb09758c484 S hℱ0 hnull hμm hμp hμq hγmL hγpL hγqL
      hpredL j hT
  -- the left-limit jump increment of `u`
  have hmu : Measurable fun p : Ω × ℝ × E => LevyStochCalc.Ito.CutoffPath.jumpIncrLeft u coeffs X.X p.1 p.2.1 p.2.2 :=
    LevyStochCalc.Ito.CutoffPath.measurable_jumpIncrLeft hu.continuous hγmeas hXm' hXleft
  have hpu : LevyStochCalc.Probability.MarkedProgressivelyMeasurable S.ℱ (LevyStochCalc.Ito.CutoffPath.jumpIncrLeft u coeffs X.X) :=
    LevyStochCalc.Ito.CutoffPath.markedProgressivelyMeasurable_jumpIncrLeft hu.continuous hγmeas hℱ0 hXadapt hXleft
  have hqu : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖LevyStochCalc.Ito.CutoffPath.jumpIncrLeft u coeffs X.X ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
    fun T' hT' => (LevyStochCalc.Ito.JumpFormula.lintegral_sq_marked_leftLimPathAt_eq hXcad
      (fun s x e => u s (x + coeffs.γ s x e) - u s x) T').trans_lt (h_jumpInt_sq T' hT')
  -- the compensator drift of `u` along the left limits, in the reference-intensity form
  have hCdu : ∀ᵐ ω ∂P, IntegrableOn (fun q : ℝ × E =>
      LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ q.1 (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X q.1 ω) q.2)
      (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E)) (LevyStochCalc.Poisson.referenceIntensity ν) := by
    filter_upwards [h_compDrift_int, hcount] with ω hω hcω
    refine _root_.Prove2MeSourceProof.h_5139a599a00e1c333b4d5e92
      ((_root_.Prove2MeSourceProof.h_3c18bbf1d33e9f6a14989002 hu hγmeas hΛm).comp measurable_prodMk_left) ?_
    calc ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X s ω) e‖₊ : ℝ≥0∞)
            ∂ν ∂volume
        = ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e‖₊ : ℝ≥0∞) ∂ν ∂volume := by
          refine lintegral_congr_ae ?_
          filter_upwards [LevyStochCalc.Ito.ae_restrict_eq_of_countable_ne hcω T] with s hs
          rw [hs]
      _ < ⊤ := hω
  -- the identity on the event that the path stays in the ball of radius `m`
  have hmain : ∀ m : ℕ, ∀ᵐ ω ∂P, (0 < m ∧ T < 3 * (m : ℝ)) →
      ω ∈ LevyStochCalc.Brownian.Ito.boundedPathSet X.X T m →
      (u T (X.X T ω) - u 0 (X.X 0 ω)
        - (∫ s in Set.Icc (0 : ℝ) T, LevyStochCalc.Ito.JumpFormula.driftIntegrand u coeffs s (X.X s ω))
        - LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
            (fun s ω => LevyStochCalc.Ito.JumpFormula.diffusionIntegrand u coeffs.σ s (X.X s ω))
            (fun j => LevyStochCalc.Ito.JumpFormula.measurable_diffusionIntegrand_path hu hσmeas X.measurable_path j)
            (fun j => LevyStochCalc.Ito.JumpFormula.progressivelyMeasurable_diffusionIntegrand_path hu hσmeas S.X_prog j)
            h_sigmaGrad_sq T ω)
      = LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
          (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
          (LevyStochCalc.Ito.JumpFormula.measurable_jumpIncrement_path hu hγmeas X.measurable_path)
          (LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog)
          h_jumpInt_sq T ω
        + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
            LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν := by
    intro m
    by_cases hmT : 0 < m ∧ T < 3 * (m : ℝ)
    swap
    · exact Filter.Eventually.of_forall fun ω h => absurd h hmT
    obtain ⟨hm, hTm⟩ := hmT
    have hR : (0 : ℝ) < 2 * (m : ℝ) := by positivity
    have hv : ContDiff ℝ 2 (Function.uncurry (LevyStochCalc.Ito.JumpFormulaCutoff.cutoffFun₂ u (2 * (m : ℝ)))) :=
      LevyStochCalc.Ito.JumpFormulaCutoff.contDiff_uncurry_cutoffFun₂ hu _
    obtain ⟨K, -, hK₀, hK₁, hK₂⟩ := _root_.Prove2MeSourceProof.h_749cad79fcd6f296f70d2bbd hu hR
    -- the bounded-derivative formula for the cut-off
    have hM16 := _root_.Prove2MeSourceProof.h_e426349f57887b0a338e40ab W N coeffs x₀ X S hℱ0 hnull
      hXleft hμmeas hσmeas hγmeas hμq (LevyStochCalc.Ito.JumpFormulaCutoff.cutoffFun₂ u (2 * (m : ℝ))) hv hK₀ hK₁ hK₂ T hT
    -- the continuous side transfers term by term
    have hcont := _root_.Prove2MeSourceProof.h_496c4ae1aa7bbf54a2f228c6 W S.ℱ S.isBrownian u hm hTm hT hadapt hXright
      (fun j => LevyStochCalc.Ito.JumpFormula.measurable_diffusionIntegrand_path hv hσmeas X.measurable_path j)
      (fun j => LevyStochCalc.Ito.JumpFormula.progressivelyMeasurable_diffusionIntegrand_path hv hσmeas S.X_prog j)
      (fun j _ hT' => LevyStochCalc.Ito.JumpFormula.lintegral_sq_diffusionIntegrand_path_lt_top hK₁ S.σ_meas S.σ_sq j hT')
      (fun j => LevyStochCalc.Ito.JumpFormula.measurable_diffusionIntegrand_path hu hσmeas X.measurable_path j)
      (fun j => LevyStochCalc.Ito.JumpFormula.progressivelyMeasurable_diffusionIntegrand_path hu hσmeas S.X_prog j)
      h_sigmaGrad_sq
    -- the left-limit jump increment of the cut-off
    have hmv : Measurable fun p : Ω × ℝ × E =>
        LevyStochCalc.Ito.CutoffPath.jumpIncrLeft (LevyStochCalc.Ito.JumpFormulaCutoff.cutoffFun₂ u (2 * (m : ℝ))) coeffs X.X p.1 p.2.1 p.2.2 :=
      LevyStochCalc.Ito.CutoffPath.measurable_jumpIncrLeft hv.continuous hγmeas hXm' hXleft
    have hpv : LevyStochCalc.Probability.MarkedProgressivelyMeasurable S.ℱ
        (LevyStochCalc.Ito.CutoffPath.jumpIncrLeft (LevyStochCalc.Ito.JumpFormulaCutoff.cutoffFun₂ u (2 * (m : ℝ))) coeffs X.X) :=
      LevyStochCalc.Ito.CutoffPath.markedProgressivelyMeasurable_jumpIncrLeft hv.continuous hγmeas hℱ0 hXadapt hXleft
    have hqv : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖LevyStochCalc.Ito.CutoffPath.jumpIncrLeft (LevyStochCalc.Ito.JumpFormulaCutoff.cutoffFun₂ u (2 * (m : ℝ))) coeffs X.X ω s e‖₊ : ℝ≥0∞) ^ 2
          ∂ν ∂volume ∂P < ⊤ :=
      fun T' hT' => LevyStochCalc.Ito.JumpFormula.lintegral_sq_jumpIncrement_path_lt_top hv hK₁ hγmL hγqL hT'
    have hCdv : ∀ᵐ ω ∂P, ω ∈ LevyStochCalc.Brownian.Ito.boundedPathSet X.X T m →
        IntegrableOn (fun q : ℝ × E => LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand (LevyStochCalc.Ito.JumpFormulaCutoff.cutoffFun₂ u (2 * (m : ℝ)))
            coeffs.γ q.1 (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X q.1 ω) q.2)
          (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E))
          (LevyStochCalc.Poisson.referenceIntensity ν) := by
      filter_upwards [_root_.Prove2MeSourceProof.h_55ca53eaccae9591a8954d60 hv hK₂ hγmeas hΛm hγmL hγqL
        hT] with ω hω _
      exact _root_.Prove2MeSourceProof.h_5139a599a00e1c333b4d5e92
        ((_root_.Prove2MeSourceProof.h_3c18bbf1d33e9f6a14989002 hv hγmeas hΛm).comp measurable_prodMk_left)
        hω
    -- the jump side transfers as a sum
    have hjs := _root_.Prove2MeSourceProof.h_78fb938706430c33723b814c N S.ℱ S.isPoisson u hu hγmeas hT hm hTm hXadapt hXleft
      hmv hpv hqv hmu hpu hqu hCdv (by filter_upwards [hCdu] with ω hω _; exact hω) hjump
    -- the compensated integrals in the point-value convention
    have hcmpv : ∀ᵐ ω ∂P,
        LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
            (LevyStochCalc.Ito.CutoffPath.jumpIncrLeft (LevyStochCalc.Ito.JumpFormulaCutoff.cutoffFun₂ u (2 * (m : ℝ))) coeffs X.X) hmv hpv hqv T ω
          = LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
            (fun ω' s e => LevyStochCalc.Ito.JumpFormulaCutoff.cutoffFun₂ u (2 * (m : ℝ)) s
                (X.X s ω' + coeffs.γ s (X.X s ω') e) - LevyStochCalc.Ito.JumpFormulaCutoff.cutoffFun₂ u (2 * (m : ℝ)) s (X.X s ω'))
            (LevyStochCalc.Ito.JumpFormula.measurable_jumpIncrement_path hv hγmeas X.measurable_path)
            (LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_jumpIncrement_path hv hγmeas S.X_prog)
            (fun _ hT' => LevyStochCalc.Ito.JumpFormula.lintegral_sq_jumpIncrement_path_lt_top hv hK₁ S.γ_meas S.γ_sq hT')
            T ω :=
      LevyStochCalc.Ito.compensatedIntegral_congr_of_countable_ne N S.isPoisson
        (fun s x e => LevyStochCalc.Ito.JumpFormulaCutoff.cutoffFun₂ u (2 * (m : ℝ)) s (x + coeffs.γ s x e)
          - LevyStochCalc.Ito.JumpFormulaCutoff.cutoffFun₂ u (2 * (m : ℝ)) s x) hcount hmv
        (LevyStochCalc.Ito.JumpFormula.measurable_jumpIncrement_path hv hγmeas X.measurable_path) hpv
        (LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_jumpIncrement_path hv hγmeas S.X_prog) hqv
        (fun _ hT' => LevyStochCalc.Ito.JumpFormula.lintegral_sq_jumpIncrement_path_lt_top hv hK₁ S.γ_meas S.γ_sq hT') hT
    have hcmpu : ∀ᵐ ω ∂P,
        LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
            (LevyStochCalc.Ito.CutoffPath.jumpIncrLeft u coeffs X.X) hmu hpu hqu T ω
          = LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
            (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
            (LevyStochCalc.Ito.JumpFormula.measurable_jumpIncrement_path hu hγmeas X.measurable_path)
            (LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog)
            h_jumpInt_sq T ω :=
      LevyStochCalc.Ito.compensatedIntegral_congr_of_countable_ne N S.isPoisson
        (fun s x e => u s (x + coeffs.γ s x e) - u s x) hcount hmu
        (LevyStochCalc.Ito.JumpFormula.measurable_jumpIncrement_path hu hγmeas X.measurable_path) hpu
        (LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog) hqu
        h_jumpInt_sq hT
    filter_upwards [hM16, hcont, hjs, hcmpv, hcmpu, hCdv, hCdu, hcount]
      with ω h16 hc hj hcv hcu hCv hCu hcω
    intro _ hb
    -- the compensator drifts in the iterated point-value convention
    have hcdv : (∫ s in Set.Icc (0 : ℝ) T, ∫ e,
          LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand (LevyStochCalc.Ito.JumpFormulaCutoff.cutoffFun₂ u (2 * (m : ℝ))) coeffs.γ s (X.X s ω) e ∂ν)
        = ∫ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E),
            LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand (LevyStochCalc.Ito.JumpFormulaCutoff.cutoffFun₂ u (2 * (m : ℝ))) coeffs.γ q.1
              (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X q.1 ω) q.2 ∂(LevyStochCalc.Poisson.referenceIntensity ν) := by
      rw [← LevyStochCalc.Ito.setIntegral_congr_of_countable_ne
        (fun s x e => LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand (LevyStochCalc.Ito.JumpFormulaCutoff.cutoffFun₂ u (2 * (m : ℝ))) coeffs.γ s x e) ν
        hcω T, (LevyStochCalc.Ito.JumpSplitting.integral_window_eq_and_integrableOn
        (fun s e => LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand (LevyStochCalc.Ito.JumpFormulaCutoff.cutoffFun₂ u (2 * (m : ℝ))) coeffs.γ s
          (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X s ω) e) (hCv hb)).1]
      simp only [Measure.restrict_univ]
    have hcdu : (∫ s in Set.Icc (0 : ℝ) T, ∫ e,
          LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν)
        = ∫ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E),
            LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ q.1 (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X q.1 ω) q.2
              ∂(LevyStochCalc.Poisson.referenceIntensity ν) := by
      rw [← LevyStochCalc.Ito.setIntegral_congr_of_countable_ne
        (fun s x e => LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ s x e) ν hcω T,
        (LevyStochCalc.Ito.JumpSplitting.integral_window_eq_and_integrableOn
        (fun s e => LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X s ω) e) hCu).1]
      simp only [Measure.restrict_univ]
    have hc' := hc hb
    have hj' := hj hb
    rw [hcv, hcu, ← hcdv, ← hcdu] at hj'
    rw [← hc', h16, hj']
  -- almost every path stays in some ball of a radius exceeding the horizon
  have hex : ∀ᵐ ω ∂P, ∃ m : ℕ, (0 < m ∧ T < 3 * (m : ℝ)) ∧
      ω ∈ LevyStochCalc.Brownian.Ito.boundedPathSet X.X T m := by
    filter_upwards [LevyStochCalc.Ito.JumpFormulaCutoff.ae_exists_mem_boundedPathSet X T] with ω hω
    obtain ⟨m, hm⟩ := hω
    refine ⟨m + ⌈T⌉₊ + 1, ⟨by omega, ?_⟩,
      LevyStochCalc.Brownian.Ito.boundedPathSet_mono X.X T (by omega) hm⟩
    have h1 : T ≤ ⌈T⌉₊ := Nat.le_ceil T
    have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast
    linarith
  filter_upwards [MeasureTheory.ae_all_iff.mpr hmain, hex] with ω hω hex
  obtain ⟨m, hmT, hb⟩ := hex
  exact hω m hmT hb
end Main

end LevyStochCalc.Ito.JumpFormula


