-- Prove2me | Definitions.Def_SourceProof_5cfe7b4902f3eabc1003b630
-- name    : SourceProof_5cfe7b4902f3eabc1003b630
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:47:59.887196+00:00
-- url     : https://prove2.me/theorems/84aabf88-a2b3-4501-b2bb-7b209d449886
-- title:
--   LevyStochCalc source module: SourceProof_5cfe7b4902f3eabc1003b630
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.itoLevy_finiteActivity_mixed` comes from the `LevyStochCalc.Ito.FiniteActivityMixed` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedSteps_F000
import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedSteps_F001
import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedSteps_F002
import Definitions.Def_SourceProof_48bb348bd252ccd46dd07812
import Definitions.Def_SourceProof_4cc3118091326cb1a3e18e2a
import Definitions.Def_SourceProof_60c6ff49320d94ec8490b751
import Definitions.Def_SourceProof_6ec651d06dfccf2636413f7c
import Definitions.Def_SourceProof_ad7cd6828ba649577ff8e72a
import Definitions.Def_SourceProof_da5e9c21250bfddff79e9986
import Definitions.Def_SourceProof_dd91edc67b4af6ac0e71ae61
import Definitions.Def_SourceProof_ea1aee2934b22cbbbf5bfc36
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability
open LevyStochCalc.Brownian.Ito LevyStochCalc.Brownian.Multidim LevyStochCalc.Ito.BigJump
open LevyStochCalc.Ito.JumpSplitting
namespace LevyStochCalc.Ito.JumpFormula
universe u v
section BrownianSum
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
end BrownianSum
section Main
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : MultidimBrownianMotion P d} {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}
theorem _root_.Prove2MeSourceProof.h_5cfe7b4902f3eabc1003b630
    (S : SdeData X)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ 0 ≤ S.ℱ t)
    (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    (hXadapt : ∀ t : ℝ, Measurable[S.ℱ t] (X.X t))
    (hXleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμp : ∀ i : Fin n,
      Probability.ProgressivelyMeasurable S.ℱ fun ω s => coeffs.μ s (X.X s ω) i)
    (hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hγmeas : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (u : ℝ → (Fin n → ℝ) → ℝ) (hu : ContDiff ℝ 2 (Function.uncurry u))
    {K₀ K₁ K₂ : ℝ}
    (hK₀ : ∀ s x, |timeDeriv u s x| ≤ K₀)
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁)
    (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (T : ℝ) (hT : 0 < T)
    {B : Set E} (hB : MeasurableSet B) (hBν : ν B ≠ ⊤)
    (y : ℝ → Ω → Fin n → ℝ)
    (hy_m : Measurable (Function.uncurry y))
    (hy_rc : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => y s ω) (𝓝[>] t) (𝓝 (y t ω)))
    (hy_ad : ∀ t : ℝ, Measurable[S.ℱ t] (y t))
    (hy_left : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => y s ω j) (𝓝[<] t) (𝓝 L))
    (V : ℝ → Ω → Fin n → ℝ)
    (hV : IsVectorItoVersion W S.ℱ S.isBrownian
      (fun i j ω s => coeffs.σ s (X.X s ω) i j) S.σ_meas S.σ_prog S.σ_sq (fun _ => x₀)
      (continuousDriftLeftAt coeffs ν X.X B) V)
    (hsplit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      y t ω i = V t ω i + jumpSumLeftAt (coeffs.markCutγ B) N X.X B t ω i)
    (hBm : ∀ j : Fin d, Measurable (Function.uncurry
      fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j))
    (hBp : ∀ j : Fin d, Probability.ProgressivelyMeasurable S.ℱ
      fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j)
    (hBq : ∀ (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hCm : Measurable fun p : Ω × ℝ × E => markCut B
      (fun ω s e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e) p.1 p.2.1 p.2.2)
    (hCp : Probability.MarkedProgressivelyMeasurable S.ℱ (markCut B
      fun ω s e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e))
    (hCq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖markCut B (fun ω s e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e) ω s e‖₊ :
        ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P,
      u T (y T ω) - u 0 (y 0 ω)
        - (∫ s in Set.Icc (0 : ℝ) T, mixedDriftIntegrand u coeffs s (y s ω) (X.X s ω))
        - MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
            (fun s ω => mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω)) hBm hBp hBq T ω
        = stochasticIntegral N S.ℱ S.isPoisson
            (markCut B fun ω s e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e)
            hCm hCp hCq T ω
          + ∫ s in Set.Icc (0 : ℝ) T, ∫ e in B,
              mixedCompensatorDriftIntegrand u coeffs.γ s (y s ω) (X.X s ω) e ∂ν := by
  classical
  set H : Fin n → Fin d → Ω → ℝ → ℝ := fun i j ω s => coeffs.σ s (X.X s ω) i j with hHdef
  set bdr : Fin n → Ω → ℝ → ℝ := LevyStochCalc.Ito.JumpSplitting.continuousDriftLeftAt coeffs ν X.X B with hbdrdef
  set f : (Fin (n + 1) → ℝ) → ℝ := LevyStochCalc.Ito.JumpFormula.timeAugFun u with hfdef
  have hfu : ∀ z, f z = LevyStochCalc.Ito.JumpFormula.timeAugFun u z := fun _ => rfl
  have hfC : ContDiff ℝ 2 f := LevyStochCalc.Ito.JumpFormula.contDiff_timeAugFun hu
  set f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ := fderiv ℝ f with hf'def
  set f'' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
    fderiv ℝ f' with hf''def
  have hf : ∀ z, HasFDerivAt f (f' z) z :=
    fun z => (hfC.differentiable (by norm_num) z).hasFDerivAt
  have hf' : ∀ z, HasFDerivAt f' (f'' z) z := fun z =>
    ((hfC.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z).hasFDerivAt
  have hf'c : Continuous f' := Differentiable.continuous fun z => (hf' z).differentiableAt
  have hf''c : Continuous f'' :=
    ((hfC.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuous
  have hK₁' : ∀ (p : Fin (n + 1)) (z : Fin (n + 1) → ℝ), |LevyStochCalc.coordDeriv f' p z| ≤ max K₀ K₁ :=
    LevyStochCalc.Ito.JumpFormula.abs_coordDeriv_timeAug_le hfu hf hK₀ hK₁
  have hK₁0 : (0 : ℝ) ≤ max K₀ K₁ := le_trans (abs_nonneg _) (hK₁' 0 0)
  have hK₂' := LevyStochCalc.Ito.JumpFormula.abs_coordDeriv₂_timeAug_mul_le hfu hf hf' hK₂ H
  set V' : ℝ → Ω → Fin (n + 1) → ℝ := LevyStochCalc.Brownian.Ito.timeAugProcess V with hV'def
  set Y' : ℝ → Ω → Fin (n + 1) → ℝ := LevyStochCalc.Brownian.Ito.timeAugProcess y with hY'def
  set H' : Fin (n + 1) → Fin d → Ω → ℝ → ℝ := LevyStochCalc.Brownian.Ito.timeAugDiffusion H with hH'def
  set b' : Fin (n + 1) → Ω → ℝ → ℝ := LevyStochCalc.Brownian.Ito.timeAugDrift bdr with hb'def
  have hV' := (_root_.Prove2MeSourceProof.h_48bb348bd252ccd46dd07812 hV)
  have hH'm : ∀ p j, Measurable (Function.uncurry (H' p j)) :=
    LevyStochCalc.Brownian.Ito.measurable_timeAugDiffusion H S.σ_meas
  have hH'p : ∀ p j, LevyStochCalc.Probability.ProgressivelyMeasurable S.ℱ (H' p j) :=
    LevyStochCalc.Brownian.Ito.progressivelyMeasurable_timeAugDiffusion H S.ℱ S.σ_prog
  have hH'q : ∀ (p : Fin (n + 1)) (j : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖H' p j ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    LevyStochCalc.Brownian.Ito.sq_timeAugDiffusion H S.σ_sq
  have hγmeasi : ∀ i : Fin n,
      Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2 i :=
    fun i => (measurable_pi_apply i).comp hγmeas
  have hXm : Measurable fun q : ℝ × Ω => X.X q.1 q.2 := X.measurable_path
  have hγmL : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E =>
      coeffs.γ p.2.1 (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X p.2.1 p.1) p.2.2 i :=
    fun i => LevyStochCalc.Ito.JumpSplitting.measurable_jumpCoeff_leftLimPathAt hXm hXleft i (hγmeasi i)
  have hγpL : ∀ i : Fin n, LevyStochCalc.Probability.MarkedProgressivelyMeasurable S.ℱ
      fun ω s e => coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X s ω) e i :=
    fun i => LevyStochCalc.Ito.JumpSplitting.markedProgressivelyMeasurable_jumpCoeff_leftLimPathAt hℱ0 hXadapt hXleft i
      (hγmeasi i)
  have hγqL : ∀ (i : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
    intro i T' hT'
    rw [LevyStochCalc.Ito.JumpSplitting.lintegral_sq_jumpCoeff_leftLimPathAt_eq X.cadlag_paths i T']
    exact S.γ_sq i T' hT'
  have hbdrm : ∀ i, Measurable (Function.uncurry (bdr i)) :=
    fun i => LevyStochCalc.Ito.JumpSplitting.measurable_uncurry_continuousDriftLeftAt B i (hμm i) (hγmL i)
  have hbdrp : ∀ i, LevyStochCalc.Probability.ProgressivelyMeasurable S.ℱ (bdr i) :=
    fun i => LevyStochCalc.Ito.JumpSplitting.progressivelyMeasurable_continuousDriftLeftAt B i S.ℱ (hμp i) (hγpL i)
  have hbdrq : ∀ (i : Fin n) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖bdr i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun i T' hT' => LevyStochCalc.Ito.JumpSplitting.lintegral_sq_continuousDriftLeftAt_lt_top hBν i (hμm i) (hμq i) (hγmL i)
      (hγqL i) T' hT'
  have hb'm : ∀ p, Measurable (Function.uncurry (b' p)) := LevyStochCalc.Brownian.Ito.measurable_timeAugDrift bdr hbdrm
  have hb'p : ∀ p, LevyStochCalc.Probability.ProgressivelyMeasurable S.ℱ (b' p) :=
    LevyStochCalc.Brownian.Ito.progressivelyMeasurable_timeAugDrift bdr S.ℱ hbdrp
  have hb'q : ∀ (p : Fin (n + 1)) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖b' p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro p
    induction p using Fin.cases with
    | zero =>
      intro T' hT'
      simp [b', LevyStochCalc.Brownian.Ito.timeAugDrift, Real.volume_Icc]
    | succ q => simpa [b', LevyStochCalc.Brownian.Ito.timeAugDrift] using hbdrq q
  have hY'm : Measurable (Function.uncurry fun ω s => Y' s ω) :=
    LevyStochCalc.Ito.JumpFormula.measurable_uncurry_timeAugProcess hy_m
  have hY'ad : ∀ t : ℝ, Measurable[S.ℱ t] (Y' t) :=
    LevyStochCalc.Ito.JumpFormula.measurable_timeAugProcess_adapted S.ℱ hy_ad
  have hY'rc : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => Y' s ω) (𝓝[>] t) (𝓝 (Y' t ω)) :=
    LevyStochCalc.Ito.JumpFormula.tendsto_timeAugProcess_nhdsWithin_gt hy_rc
  have hY'comp : ∀ {φ : (Fin (n + 1) → ℝ) → ℝ}, Continuous φ →
      LevyStochCalc.Probability.ProgressivelyMeasurable S.ℱ fun ω s => φ (Y' s ω) := fun {φ} hφ =>
    _root_.Prove2MeSourceProof.h_845c55972b82cdb43dfb6421 (X := fun s ω => φ (Y' s ω))
      (fun t => hφ.measurable.comp (hY'ad t)) (fun ω t => (hφ.tendsto _).comp (hY'rc ω t))
  have hmG : ∀ (p : Fin (n + 1)) (j : Fin d), Measurable (Function.uncurry
      fun ω s => LevyStochCalc.coordDeriv f' p (Y' s ω) * H' p j ω s) :=
    LevyStochCalc.Brownian.Ito.measurable_timeAugWeight f' y H
      (fun q k => ((LevyStochCalc.continuous_coordDeriv hf'c q.succ).measurable.comp hY'm).mul (S.σ_meas q k))
  have hpG : ∀ (p : Fin (n + 1)) (j : Fin d), LevyStochCalc.Probability.ProgressivelyMeasurable S.ℱ
      fun ω s => LevyStochCalc.coordDeriv f' p (Y' s ω) * H' p j ω s :=
    LevyStochCalc.Brownian.Ito.progressivelyMeasurable_timeAugWeight f' y H S.ℱ
      (fun q k => (hY'comp (LevyStochCalc.continuous_coordDeriv hf'c q.succ)).mul (S.σ_prog q k))
  have hqG : ∀ (p : Fin (n + 1)) (j : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖LevyStochCalc.coordDeriv f' p (Y' s ω) * H' p j ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    LevyStochCalc.Brownian.Ito.sq_timeAugWeight f' y H (fun q k => LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le_mul hK₁0
      (fun ω s => by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hK₁' _ _) (abs_nonneg _))
      (S.σ_sq q k))
  have hmD : ∀ p : Fin (n + 1), Measurable (Function.uncurry
      fun ω s => LevyStochCalc.coordDeriv f' p (Y' s ω) * b' p ω s) := fun p =>
    ((LevyStochCalc.continuous_coordDeriv hf'c p).measurable.comp hY'm).mul (hb'm p)
  have hqD : ∀ (p : Fin (n + 1)) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖LevyStochCalc.coordDeriv f' p (Y' s ω) * b' p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun p =>
    LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le_mul hK₁0
      (fun ω s => by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hK₁' _ _) (abs_nonneg _))
      (hb'q p)
  have hmQ : ∀ p q : Fin (n + 1), Measurable (Function.uncurry
      fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (Y' s ω) * ∑ j : Fin d, H' p j ω s * H' q j ω s) :=
    fun p q => ((LevyStochCalc.continuous_coordDeriv₂ hf''c p q).measurable.comp hY'm).mul
      (Finset.measurable_sum _ fun j _ => (hH'm p j).mul (hH'm q j))
  have hQint : ∀ᵐ ω ∂P, ∀ p q : Fin (n + 1), IntegrableOn
      (fun s => LevyStochCalc.coordDeriv₂ f'' p q (Y' s ω) * ∑ j : Fin d, H' p j ω s * H' q j ω s)
      (Set.Ioc (0 : ℝ) T) volume := by
    filter_upwards [_root_.Prove2MeSourceProof.h_065e60a1696464e96f1fa2c5 hH'm (fun p j => hH'q p j T hT)] with ω hω p q
    refine Integrable.mono' ((hω p q).abs.const_mul |K₂|)
      (Measurable.of_uncurry_left (hmQ p q)).aestronglyMeasurable ?_
    filter_upwards with s
    rw [Real.norm_eq_abs, abs_mul]
    exact (hK₂' p q _ ω s).trans (mul_le_mul_of_nonneg_right (le_abs_self K₂) (abs_nonneg _))
  set σ : ℕ → Ω → WithTop ℝ := LevyStochCalc.Ito.JumpFormula.cappedJumpTime N B T with hσdef
  obtain ⟨hσ, hmono, h0⟩ := LevyStochCalc.Ito.JumpFormula.cappedJumpTime_chain_of_complete N B S.isPoisson hB hBν hnull0 hT.le
  have hσ0 : ∀ (k : ℕ) (ω : Ω), ((0 : ℝ) : WithTop ℝ) ≤ σ k ω := fun k ω =>
    le_min (by
      rw [← LevyStochCalc.Poisson.jumpTime_zero N B ω]
      exact LevyStochCalc.Poisson.jumpTime_mono N B (Nat.zero_le k) ω) (by exact_mod_cast hT.le)
  have hσne : ∀ (k : ℕ) (ω : Ω), σ k ω ≠ ⊤ := fun k ω =>
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)
  set c : ℕ → Ω → Fin n → ℝ := fun k ω => y (σ k ω).untopA ω - V (σ k ω).untopA ω with hcdef
  set c' : ℕ → Ω → Fin (n + 1) → ℝ := fun k ω => Fin.cons 0 (c k ω) with hc'def
  have hyprog : ∀ i : Fin n, LevyStochCalc.Probability.ProgressivelyMeasurable S.ℱ fun ω s => y s ω i :=
    fun i => _root_.Prove2MeSourceProof.h_845c55972b82cdb43dfb6421 (X := fun s ω => y s ω i)
      (fun t => (measurable_pi_apply i).comp (hy_ad t))
      (fun ω t => ((continuous_apply i).tendsto _).comp (hy_rc ω t))
  have hVprog : ∀ i : Fin n, LevyStochCalc.Probability.ProgressivelyMeasurable S.ℱ fun ω s => V s ω i :=
    fun i => hV.progressivelyMeasurable_comp (continuous_apply i)
  have hc : ∀ k, Measurable[(hσ k).measurableSpace] (c k) := fun k =>
    LevyStochCalc.Ito.JumpFormula.measurable_stoppingTime_eval_untopA (Y := fun s ω => y s ω - V s ω)
      (fun i => (hyprog i).sub (hVprog i)) (hσ k)
  have hc' : ∀ k, Measurable[(hσ k).measurableSpace] (c' k) := fun k =>
    LevyStochCalc.Ito.JumpFormula.Measurable.finCons_zero (hc k)
  have hcm : ∀ k, Measurable (c' k) := fun k => (hc' k).mono (hσ k).measurableSpace_le le_rfl
  have hsplit' : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      y t ω i = V t ω i + LevyStochCalc.Ito.JumpSplitting.jumpSumLeft X B t ω i := by
    filter_upwards [hsplit] with ω hω t ht i
    rw [hω t ht i, LevyStochCalc.Ito.JumpFormula.jumpSumLeftAt_markCutγ_eq_jumpSumAt_leftLimPath X hB]
    rfl
  have hcap := LevyStochCalc.Ito.JumpFormula.ae_forall_add_cappedJumpSumLeft_eq_of_path (Z := y) hsplit' hB hBν hT.le
  have hceq : ∀ᵐ ω ∂P, ∀ k : ℕ, c k ω = LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt X (LevyStochCalc.Ito.JumpSplitting.leftLimPath X) B T k ω := by
    filter_upwards [hsplit] with ω hω k
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (hσne k ω)
    have hr0 : 0 ≤ r := by
      have := hσ0 k ω
      rw [← hr] at this
      exact_mod_cast this
    have hunt : (σ k ω).untopA = r := by rw [← hr]; rfl
    have hclip : LevyStochCalc.Brownian.Ito.clipTime (LevyStochCalc.Poisson.jumpTime N B k) T ω = r := by
      rw [LevyStochCalc.Ito.JumpFormula.clipTime_jumpTime_eq_untopA]
      exact hunt
    funext i
    simp only [c, hunt, LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt, hclip, Pi.sub_apply]
    rw [hω r hr0 i, LevyStochCalc.Ito.JumpFormula.jumpSumLeftAt_markCutγ_eq_jumpSumAt_leftLimPath X hB]
    ring
  have hshift : ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), σ k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < σ (k + 1) ω → V' s ω + c' k ω = Y' s ω := by
    filter_upwards [hcap, hceq] with ω hω hcω k s h1 h2
    have hks := hω k s h1 h2
    rw [← hcω k] at hks
    simp only [V', c', Y', LevyStochCalc.Brownian.Ito.timeAugProcess]
    rw [LevyStochCalc.Ito.JumpFormula.cons_add_cons_zero, hks]
  have hV'm : Measurable (Function.uncurry fun ω s => V' s ω) := hV'.measurable_uncurry
  have hV'prog : LevyStochCalc.Probability.ProgressivelyMeasurable S.ℱ fun ω s => V' s ω :=
    _root_.Prove2MeSourceProof.h_35d8365844de2771203e553f
      (StronglyAdapted.isStronglyProgressive_of_continuous hV'.adapted hV'.continuous_path)
  have hmVun : ∀ (k : ℕ) (p : Fin (n + 1)) (j : Fin d), Measurable (Function.uncurry
      fun ω s => LevyStochCalc.coordDeriv f' p (V' s ω + c' k ω) * H' p j ω s) := fun k p j =>
    ((LevyStochCalc.continuous_coordDeriv hf'c p).measurable.comp
      (hV'm.add ((hcm k).comp measurable_fst))).mul (hH'm p j)
  have hqVun : ∀ (k : ℕ) (p : Fin (n + 1)) (j : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖LevyStochCalc.coordDeriv f' p (V' s ω + c' k ω) * H' p j ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun k p j => LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le_mul hK₁0
      (fun ω s => by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hK₁' _ _) (abs_nonneg _))
      (hH'q p j)
  have hmV : ∀ (k : ℕ) (p : Fin (n + 1)) (j : Fin d), Measurable (Function.uncurry fun ω s =>
      LevyStochCalc.Probability.stopped (σ (k + 1))
          (fun ω s => LevyStochCalc.coordDeriv f' p (V' s ω + c' k ω) * H' p j ω s) ω s
        - LevyStochCalc.Probability.stopped (σ k)
            (fun ω s => LevyStochCalc.coordDeriv f' p (V' s ω + c' k ω) * H' p j ω s) ω s) := fun k p j =>
    LevyStochCalc.Brownian.Ito.measurable_uncurry_stopped_sub_shift (hσ k) (hσ (k + 1)) (hcm k) hV'm
      (LevyStochCalc.continuous_coordDeriv hf'c p) (hH'm p j) (fun _ _ => rfl)
  have hpV : ∀ (k : ℕ) (p : Fin (n + 1)) (j : Fin d),
      LevyStochCalc.Probability.ProgressivelyMeasurable S.ℱ fun ω s =>
      LevyStochCalc.Probability.stopped (σ (k + 1))
          (fun ω s => LevyStochCalc.coordDeriv f' p (V' s ω + c' k ω) * H' p j ω s) ω s
        - LevyStochCalc.Probability.stopped (σ k)
            (fun ω s => LevyStochCalc.coordDeriv f' p (V' s ω + c' k ω) * H' p j ω s) ω s := fun k p j =>
    _root_.Prove2MeSourceProof.h_1c19127385342f00e6ef4903 (hσ k) (hσ (k + 1)) (hmono k) (hc' k) hV'prog
      (LevyStochCalc.continuous_coordDeriv hf'c p) (hH'p p j) (fun _ _ => rfl)
  have hqV : ∀ (k : ℕ) (p : Fin (n + 1)) (j : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖LevyStochCalc.Probability.stopped (σ (k + 1))
              (fun ω s => LevyStochCalc.coordDeriv f' p (V' s ω + c' k ω) * H' p j ω s) ω s
            - LevyStochCalc.Probability.stopped (σ k)
                (fun ω s => LevyStochCalc.coordDeriv f' p (V' s ω + c' k ω) * H' p j ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤ := fun k p j =>
    LevyStochCalc.Brownian.Ito.energy_stopped_sub_lt_top (hσ k) (hσ (k + 1)) (hmVun k p j) (hqVun k p j)
  have hX₀ : ∀ p : Fin (n + 1), Measurable[S.ℱ 0] fun ω => LevyStochCalc.Brownian.Ito.timeAugInit (fun _ : Ω => x₀) ω p :=
    fun p => measurable_const
  have hcont := fun k : ℕ => _root_.Prove2MeSourceProof.h_ea1aee2934b22cbbbf5bfc36 W S.ℱ S.isBrownian hV' hℱ0
    hnull0 hX₀ hb'm hb'p hb'q (hσ k) (hσ (k + 1)) (hmono k) (hσ0 k) (hσ0 (k + 1)) hfC hf hf'
    hK₁' hK₂' hT (hc' k) (hmV k) (hpV k) (hqV k)
  have hchain := fun m : ℕ => _root_.Prove2MeSourceProof.h_8f233afb059158cd609f4547 W S.ℱ S.isBrownian hσ hmono hmG hpG hqG hmD hqD
    hmQ hmV hpV hqV hT hQint (m := m) h0 hshift (fun k _ => hcont k)
  have hBro : ∀ᵐ ω ∂P, (∑ p : Fin (n + 1), ∑ j : Fin d,
        LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) S.ℱ (S.isBrownian j)
          (fun ω s => LevyStochCalc.coordDeriv f' p (Y' s ω) * H' p j ω s) (hmG p j) (hpG p j) (hqG p j) T ω)
      = LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
          (fun s ω => LevyStochCalc.Ito.JumpFormula.mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω)) hBm hBp hBq T ω := by
    have hrow : ∀ j : Fin d, (fun ω s => ∑ p : Fin (n + 1), LevyStochCalc.coordDeriv f' p (Y' s ω) * H' p j ω s)
        = fun ω s => LevyStochCalc.Ito.JumpFormula.mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j := by
      intro j
      funext ω s
      rw [Fin.sum_univ_succ]
      simp only [H', LevyStochCalc.Brownian.Ito.timeAugDiffusion, Fin.cons_zero, Fin.cons_succ, mul_zero, zero_add,
        LevyStochCalc.Ito.JumpFormula.mixedDiffusionIntegrand, Y', LevyStochCalc.Brownian.Ito.timeAugProcess, H]
      exact Finset.sum_congr rfl fun i _ => by
        rw [LevyStochCalc.Ito.JumpFormula.coordDeriv_succ_cons_eq_gradient hfu hf]
    have hj : ∀ j : Fin d, (fun ω => ∑ p : Fin (n + 1),
        LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) S.ℱ (S.isBrownian j)
          (fun ω s => LevyStochCalc.coordDeriv f' p (Y' s ω) * H' p j ω s) (hmG p j) (hpG p j) (hqG p j) T ω)
        =ᵐ[P] LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) S.ℱ (S.isBrownian j)
          (fun ω s => LevyStochCalc.Ito.JumpFormula.mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j)
          (hBm j) (hBp j) (hBq j) T := by
      intro j
      have hms : Measurable (Function.uncurry
          fun ω s => ∑ p : Fin (n + 1), LevyStochCalc.coordDeriv f' p (Y' s ω) * H' p j ω s) := by
        rw [hrow j]; exact hBm j
      have hps : LevyStochCalc.Probability.ProgressivelyMeasurable S.ℱ
          fun ω s => ∑ p : Fin (n + 1), LevyStochCalc.coordDeriv f' p (Y' s ω) * H' p j ω s := by
        rw [hrow j]; exact hBp j
      have hqs : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          (‖∑ p : Fin (n + 1), LevyStochCalc.coordDeriv f' p (Y' s ω) * H' p j ω s‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P < ⊤ := by
        intro T' hT'
        have hrow' : ∀ ω s, (∑ p : Fin (n + 1), LevyStochCalc.coordDeriv f' p (Y' s ω) * H' p j ω s)
            = LevyStochCalc.Ito.JumpFormula.mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j :=
          fun ω s => congrFun (congrFun (hrow j) ω) s
        simp only [hrow']
        exact hBq j T' hT'
      filter_upwards [_root_.Prove2MeSourceProof.h_4cc3118091326cb1a3e18e2a (W.W j) S.ℱ (S.isBrownian j) hT
        (fun p ω s => LevyStochCalc.coordDeriv f' p (Y' s ω) * H' p j ω s) (fun p => hmG p j)
        (fun p => hpG p j) (fun p => hqG p j) hms hps hqs] with ω hω
      rw [← hω, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun (W.W j) S.ℱ (S.isBrownian j) (hrow j) hms
        hps hqs (hBm j) (hBp j) (hBq j) T]
    filter_upwards [MeasureTheory.ae_all_iff.mpr hj] with ω hω
    rw [LevyStochCalc.Ito.JumpFormula.multidimStochasticIntegral_eq_sum, Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => hω j
  set φm : Ω → ℝ → E → ℝ := fun ω s e =>
    LevyStochCalc.Ito.JumpFormula.mixedJumpIncrement u coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt y s ω) (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X s ω) e with hφmdef
  have hCmp : ∀ᵐ ω ∂P, LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
        (LevyStochCalc.Poisson.Compensated.markCut B fun ω s e => LevyStochCalc.Ito.JumpFormula.mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e)
        hCm hCp hCq T ω
      = (∫ q in Set.Ioc (0 : ℝ) T ×ˢ B, LevyStochCalc.Poisson.Compensated.markCut B φm ω q.1 q.2 ∂(N.N ω))
        - ∫ s in Set.Icc (0 : ℝ) T, ∫ e in B,
            LevyStochCalc.Ito.JumpFormula.mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e ∂ν := by
    obtain ⟨hφmm, hφmp, hφmq⟩ := _root_.Prove2MeSourceProof.h_6ec651d06dfccf2636413f7c S hℱ0 hu hK₁ hy_m hy_ad
      hy_left hγmL hγpL hγqL
    have hCmm : Measurable fun p : Ω × ℝ × E => LevyStochCalc.Poisson.Compensated.markCut B φm p.1 p.2.1 p.2.2 :=
      LevyStochCalc.Poisson.Compensated.measurable_markCut hφmm hB
    have hCmp' : LevyStochCalc.Probability.MarkedProgressivelyMeasurable S.ℱ (LevyStochCalc.Poisson.Compensated.markCut B φm) :=
      (_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b hφmp) hB
    have hCmq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖LevyStochCalc.Poisson.Compensated.markCut B φm ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
      fun T' hT' => LevyStochCalc.Poisson.Compensated.sq_markCut hφmq B T' hT'
    have hcount := LevyStochCalc.Ito.JumpFormula.ae_countable_setOf_leftLim_ne_pair (X := X) hy_rc hy_left
    have hcongr : LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson (LevyStochCalc.Poisson.Compensated.markCut B φm) hCmm hCmp' hCmq T
        =ᵐ[P] LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
          (LevyStochCalc.Poisson.Compensated.markCut B fun ω s e => LevyStochCalc.Ito.JumpFormula.mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e)
          hCm hCp hCq T :=
      LevyStochCalc.Ito.compensatedIntegral_congr_of_countable_ne N S.isPoisson
        (X := fun s ω => ((y s ω, X.X s ω) : (Fin n → ℝ) × (Fin n → ℝ)))
        (Xm := fun s ω => ((LevyStochCalc.Ito.JumpSplitting.leftLimPathAt y s ω, LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X s ω) :
          (Fin n → ℝ) × (Fin n → ℝ)))
        (fun s v e => B.indicator (fun _ => LevyStochCalc.Ito.JumpFormula.mixedJumpIncrement u coeffs.γ s v.1 v.2 e) e)
        hcount hCmm hCm hCmp' hCp hCmq hCq hT
    have hpred : LevyStochCalc.Probability.MarkedPredictable S.ℱ ν (LevyStochCalc.Ito.JumpFormula.zeroExtPos φm) :=
      _root_.Prove2MeSourceProof.h_60c6ff49320d94ec8490b751 S hXadapt hXleft hγmeasi hu hy_ad
        hy_left
    have hpredM : LevyStochCalc.Probability.MarkedPredictable S.ℱ ν (LevyStochCalc.Ito.JumpFormula.zeroExtPos (LevyStochCalc.Poisson.Compensated.markCut B φm)) :=
      LevyStochCalc.Ito.JumpFormula.markedPredictable_zeroExtPos_markCut hpred hB
    have hpath := LevyStochCalc.Ito.JumpFormula.stochasticIntegral_ae_eq_pathwise_of_zeroExtPos N S.ℱ S.isPoisson (LevyStochCalc.Poisson.Compensated.markCut B φm)
      hCmm hCmp' hCmq hB hpredM hBν (fun ω s e he => Set.indicator_of_notMem he _) hT
    have hen := LevyStochCalc.Ito.JumpFormula.lintegral_referenceIntensity_window_ne_top hφmm hφmq B T hT
    have hwin := LevyStochCalc.Ito.JumpFormula.ae_integrableOn_window_of_zeroExtPos N S.isPoisson hB hBν T hpred hφmm hen
    filter_upwards [hcongr, hpath, hwin, hcount] with ω h1 h2 h3 h4
    rw [← h1, h2]
    congr 1
    have hmc : Set.EqOn (fun q : ℝ × E => LevyStochCalc.Poisson.Compensated.markCut B φm ω q.1 q.2) (fun q => φm ω q.1 q.2)
        (Set.Ioc (0 : ℝ) T ×ˢ B) := fun q hq => Set.indicator_of_mem hq.2 _
    rw [setIntegral_congr_fun (measurableSet_Ioc.prod hB) hmc,
      (LevyStochCalc.Ito.JumpSplitting.integral_window_eq_and_integrableOn (fun s e => φm ω s e) h3.2).1]
    exact LevyStochCalc.Ito.setIntegral_congr_of_countable_ne
      (X := fun s ω => ((y s ω, X.X s ω) : (Fin n → ℝ) × (Fin n → ℝ)))
      (Xm := fun s ω => ((LevyStochCalc.Ito.JumpSplitting.leftLimPathAt y s ω, LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X s ω) :
        (Fin n → ℝ) × (Fin n → ℝ)))
      (fun s v e => LevyStochCalc.Ito.JumpFormula.mixedJumpIncrement u coeffs.γ s v.1 v.2 e) (ν.restrict B) h4 T
  have hdict : ∀ᵐ ω ∂P, (∑ p : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
          LevyStochCalc.coordDeriv f' p (Y' s ω) * b' p ω s ∂volume)
        + 1 / 2 * ∑ p : Fin (n + 1), ∑ q : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
            LevyStochCalc.coordDeriv₂ f'' p q (Y' s ω) * (∑ j : Fin d, H' p j ω s * H' q j ω s) ∂volume
      = ∫ s in Set.Icc (0 : ℝ) T, (LevyStochCalc.Ito.JumpFormula.mixedDriftIntegrand u coeffs s (y s ω) (X.X s ω)
          - ∑ i : Fin n, LevyStochCalc.Ito.JumpFormula.gradient u s (y s ω) i * ∫ e in B, coeffs.γ s (X.X s ω) e i ∂ν) :=
    _root_.Prove2MeSourceProof.h_dd91edc67b4af6ac0e71ae61 hfu hf hf' B T hT y bdr (fun _ _ _ => rfl) H
      (fun _ _ _ _ => rfl) hmD hqD hQint
  have hint := _root_.Prove2MeSourceProof.h_da5e9c21250bfddff79e9986 S hμm hμq hγmeas u hu hK₀ hK₁ hK₂ T hT hBν y hy_m
  filter_upwards [MeasureTheory.ae_all_iff.mpr hchain,
    _root_.Prove2MeSourceProof.h_2d73a2b6df3c10b500c2eec5 N B hB hBν T,
    _root_.Prove2MeSourceProof.h_3b4c8aaeb3983333d32ff10f N B hB hBν T,
    LevyStochCalc.Ito.JumpFormula.ae_exists_le_jumpTime N B hB hBν T, hshift, hceq, hBro, hCmp, hdict, hint]
    with ω hchainω hatomω hstrictω hm'ω hshiftω hceqω hBroω hCmpω hdictω hintω
  obtain ⟨m, hm⟩ := hm'ω
  obtain ⟨K, θ, ε, hmonoθ, hrange, hmem, hsum⟩ := hatomω
  have hm' : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N B m ω := hm
  have hchainm := hchainω m ((LevyStochCalc.Ito.JumpFormula.le_cappedJumpTime_iff N B T m ω).mpr hm')
  have hend1 : f (V' T ω + c' m ω) = u T (y T ω) := by
    have hσm : σ m ω = ((T : ℝ) : WithTop ℝ) := min_eq_right hm'
    have hunt : (σ m ω).untopA = T := by rw [hσm]; rfl
    simp only [V', c', c, hunt, LevyStochCalc.Brownian.Ito.timeAugProcess, hfdef]
    rw [LevyStochCalc.Ito.JumpFormula.timeAugFun_cons_add_cons_zero, add_sub_cancel]
  have hend0 : f (V' 0 ω + c' 0 ω) = u 0 (y 0 ω) := by
    have hσ00 : σ 0 ω = ((0 : ℝ) : WithTop ℝ) := h0 ω
    have hunt : (σ 0 ω).untopA = 0 := by rw [hσ00]; rfl
    simp only [V', c', c, hunt, LevyStochCalc.Brownian.Ito.timeAugProcess, hfdef]
    rw [LevyStochCalc.Ito.JumpFormula.timeAugFun_cons_add_cons_zero, add_sub_cancel]
  have hjump : (∑ k ∈ Finset.range m, (f (V' (LevyStochCalc.Brownian.Ito.clipTime (σ (k + 1)) T ω) ω + c' (k + 1) ω)
        - f (V' (LevyStochCalc.Brownian.Ito.clipTime (σ (k + 1)) T ω) ω + c' k ω)))
      = ∑ j : Fin K, LevyStochCalc.Poisson.Compensated.markCut B φm ω (θ j) (ε j) := by
    rw [_root_.Prove2MeSourceProof.h_0d088112759d60f13f10d2df (A := B) f (V := V') (Y := Y') (c := c')
      (jump := fun j => Fin.cons 0 (coeffs.γ (θ j) (LevyStochCalc.Ito.JumpSplitting.leftLimPath X (θ j) ω) (ε j)))
      hmonoθ (fun j => (hmem j).1) hrange (hV'.continuous_path ω) hstrictω
      (fun k s h1 h2 => hshiftω k s h1 h2) ?_ ?_ hm']
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [LevyStochCalc.Ito.JumpFormula.leftLim_timeAugProcess_eq_cons y (fun i => hy_left ω (θ j) i)]
      simp only [hfdef, markCut_apply, Set.indicator_of_mem (hmem j).2, φm,
        LevyStochCalc.Ito.JumpFormula.mixedJumpIncrement]
      rw [LevyStochCalc.Ito.JumpFormula.timeAugFun_cons_add_cons_zero, LevyStochCalc.Ito.JumpFormula.timeAugFun_cons]
      rfl
    · intro k hk
      simp only [c']
      rw [hceqω, hceqω,
        _root_.Prove2MeSourceProof.h_b233f14b4b88a4af49762008 X (LevyStochCalc.Ito.JumpSplitting.leftLimPath X) hB hmem hsum hrange hk]
    · intro k hk
      obtain ⟨j, hj, hinc⟩ := _root_.Prove2MeSourceProof.h_5ffe5f6881eccb3f8509bfdc X (LevyStochCalc.Ito.JumpSplitting.leftLimPath X) hB hmem hsum
        hmonoθ.injective hrange (hstrictω k hk) hk
      refine ⟨j, hj, ?_⟩
      simp only [c']
      rw [hceqω, hceqω, hinc, LevyStochCalc.Ito.JumpFormula.cons_add_cons_zero]
  have hjump' : (∑ j : Fin K, LevyStochCalc.Poisson.Compensated.markCut B φm ω (θ j) (ε j))
      = LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
          (LevyStochCalc.Poisson.Compensated.markCut B fun ω s e => LevyStochCalc.Ito.JumpFormula.mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e)
          hCm hCp hCq T ω
        + ∫ s in Set.Icc (0 : ℝ) T, ∫ e in B,
            LevyStochCalc.Ito.JumpFormula.mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e ∂ν := by
    rw [hCmpω, ← hsum (fun q => LevyStochCalc.Poisson.Compensated.markCut B φm ω q.1 q.2)]
    ring
  rw [hend1, hend0, hjump] at hchainm
  obtain ⟨hγi, hΔi, hΔt, hgt, hdt⟩ := hintω
  have hkey := _root_.Prove2MeSourceProof.h_ad7cd6828ba649577ff8e72a (u := u) (coeffs := coeffs) (ν := ν)
    (A := B) (y := fun s => y s ω) (x := fun s => X.X s ω) (T := T)
    (Dm := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
      (fun s ω => LevyStochCalc.Ito.JumpFormula.mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω)) hBm hBp hBq T ω)
    hγi hΔi hΔt hgt hdt (by linarith [hchainm, hdictω, hBroω]) hjump'
  beta_reduce at hkey
  linarith
end Main
end LevyStochCalc.Ito.JumpFormula


