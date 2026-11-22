-- Prove2me | Definitions.Def_SourceProof_f631eb99340a9e8c76355a4c
-- name    : SourceProof_f631eb99340a9e8c76355a4c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T10:13:17.644184+00:00
-- url     : https://prove2.me/theorems/ff399deb-f169-46f4-a26d-01e65a169115
-- title:
--   LevyStochCalc source module: SourceProof_f631eb99340a9e8c76355a4c
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpSplitting.eq_vectorItoProcess_add_jumpSumLeftAt_add_remainder_of_path` comes from the `LevyStochCalc.Ito.JumpSplittingRemainderDecomposition` module. The staged Lean declaration includes its source proof and dependency references. Some theorem-statement references have been redirected to generated helpers; formal type equivalence still requires certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_AtomJumpRelation_F001
import Definitions.Def_LevyStochCalc_Ito_TruncatedContinuousPart_F001
import Definitions.Def_SourceProof_c1b36e8cddd2b346f7818b69

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The splitting of a path with remainder

A path satisfying the jump-diffusion integral equation is, at every nonnegative time, the sum of
a vector Itô process with diffusion `σ` and drift `continuousDriftLeftAt`, the pathwise sum of
the jumps carried by a mark set of finite intensity and the compensated integral of the
left-limit jump coefficient cut to the complement of that set — the *remainder* — so that across
an arrival time carrying a mark of the set the path jumps by the jump coefficient read at its
left limit plus the jump of the remainder.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.eq_vectorItoProcess_add_jumpSumLeftAt_add_remainder_of_path`
  — the splitting with remainder at a fixed nonnegative time.
* `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_add_jumpSumLeftAt_add_remainder_of_path` — the
  same identity almost surely at all nonnegative times.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, step (II).
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpSplitting

open LevyStochCalc.Poisson.Compensated

universe u v

section Remainder

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  (coeffs : Setting.JumpDiffusionCoeffs n d E)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (Xp : ℝ → Ω → Fin n → ℝ)
  (x₀ : Fin n → ℝ) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
  (hσm : ∀ (i : Fin n) (j : Fin d),
    Measurable (Function.uncurry fun ω s => coeffs.σ s (Xp s ω) i j))
  (hσp : ∀ (i : Fin n) (j : Fin d),
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (Xp s ω) i j)
  (hσq : ∀ (i : Fin n) (j : Fin d) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.σ s (Xp s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (hγm : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Xp p.2.1 p.1) p.2.2 i)
  (hγp : ∀ i : Fin n,
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (Xp s ω) e i)
  (hγq : ∀ (i : Fin n) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (Xp s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  (hγmL : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E =>
    coeffs.γ p.2.1 (leftLimPathAt Xp p.2.1 p.1) p.2.2 i)
  (hγpL : ∀ i : Fin n, Probability.MarkedProgressivelyMeasurable ℱ
    fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i)
  (hγqL : ∀ (i : Fin n) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (leftLimPathAt Xp s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hγmL hγpL hγqL in

theorem _root_.Prove2MeSourceProof.h_f631eb99340a9e8c76355a4c (Z : ℝ → Ω → Fin n → ℝ)
    (hXpcadlag : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => Xp s ω) (𝓝[>] t) (𝓝 (Xp t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => Xp s ω i) (𝓝[<] t) (𝓝 L))
    (hSDE : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      Z t ω i = x₀ i
        + (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (Xp s ω) i)
        + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
            (fun s ω => coeffs.σ s (Xp s ω) i) (fun j => hσm i j) (fun j => hσp i j)
            (fun j => hσq i j) t ω
        + stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (Xp s ω) e i) (hγm i) (hγp i) (hγq i) t ω)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hpredL : ∀ i : Fin n, Probability.MarkedPredictable ℱ ν
      (JumpFormula.zeroExtPos fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i))
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (Xp s ω) i))
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.μ s (Xp s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ∀ i : Fin n,
      Z t ω i
        = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
            (fun i j ω s => coeffs.σ s (Xp s ω) i j) hσm hσp hσq (fun _ => x₀)
            (continuousDriftLeftAt coeffs ν Xp A) t ω i
          + jumpSumLeftAt coeffs N Xp A t ω i
          + stochasticIntegral N ℱ hℱN
              (markCut Aᶜ fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i)
              (measurable_markCut (hγmL i) hA.compl) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (hγpL i)) hA.compl)
              (fun T' hT' => sq_markCut (hγqL i) Aᶜ T' hT') t ω := by
  classical
  have hzeroCI : ∀ (ψ : Ω → ℝ → E → ℝ)
      (h1 : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
      (h2 : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ ψ)
      (h3 : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤),
      ∀ᵐ ω ∂P, LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN ψ h1 h2 h3 0 ω = 0 := fun ψ h1 h2 h3 => by
    filter_upwards [LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process N ℱ hℱN ψ h1 h2 h3 0,
      _root_.Prove2MeSourceProof.h_2c4e2697eef458aa9c0dbb56 N ℱ hℱN ψ h1 h2 h3 (le_refl (0 : ℝ))] with ω h1 h2
    rw [h1, h2]
    rfl
  rcases eq_or_lt_of_le ht with h0 | hpos
  · subst h0
    filter_upwards [hSDE 0 le_rfl,
      MeasureTheory.ae_all_iff.mpr fun i => hzeroCI _ (hγm i) (hγp i) (hγq i),
      MeasureTheory.ae_all_iff.mpr fun i => hzeroCI _ (LevyStochCalc.Poisson.Compensated.measurable_markCut (hγmL i) hA.compl)
        ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (hγpL i)) hA.compl) (fun T' hT' => LevyStochCalc.Poisson.Compensated.sq_markCut (hγqL i) Aᶜ T' hT')]
      with ω hω hz hzR
    intro i
    rw [hω i, hz i, hzR i,
      LevyStochCalc.Ito.JumpSplitting.multidimIntegral_eq_vectorItoMartingaleAt coeffs Xp ℱ hℱW hσm hσp hσq i 0 ω]
    simp [LevyStochCalc.Brownian.Ito.vectorItoProcess, LevyStochCalc.Ito.JumpSplitting.jumpSumLeftAt_zero]
  · have hcong : ∀ i : Fin n, ∀ᵐ ω ∂P,
        LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN (fun ω s e => coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp s ω) e i)
            (hγmL i) (hγpL i) (hγqL i) t ω
          = LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN (fun ω s e => coeffs.γ s (Xp s ω) e i)
            (hγm i) (hγp i) (hγq i) t ω := fun i =>
      LevyStochCalc.Ito.compensatedIntegral_congr_of_countable_ne N hℱN (fun s x e => coeffs.γ s x e i)
        (LevyStochCalc.Ito.JumpSplitting.ae_countable_setOf_pos_ne_leftLimPathAt Xp hXpcadlag) (hγmL i) (hγm i) (hγpL i)
        (hγp i) (hγqL i) (hγq i) hpos
    have hsplitCI : ∀ i : Fin n, ∀ᵐ ω ∂P,
        LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN (fun ω s e => coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp s ω) e i)
            (hγmL i) (hγpL i) (hγqL i) t ω
          = LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
              (LevyStochCalc.Poisson.Compensated.markCut A fun ω s e => coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp s ω) e i)
              (LevyStochCalc.Poisson.Compensated.measurable_markCut (hγmL i) hA) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (hγpL i)) hA)
              (fun T' hT' => LevyStochCalc.Poisson.Compensated.sq_markCut (hγqL i) A T' hT') t ω
            + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
              (LevyStochCalc.Poisson.Compensated.markCut Aᶜ fun ω s e => coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp s ω) e i)
              (LevyStochCalc.Poisson.Compensated.measurable_markCut (hγmL i) hA.compl) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (hγpL i)) hA.compl)
              (fun T' hT' => LevyStochCalc.Poisson.Compensated.sq_markCut (hγqL i) Aᶜ T' hT') t ω := fun i =>
      _root_.Prove2MeSourceProof.h_c1b36e8cddd2b346f7818b69 N ℱ hℱN _ (hγmL i)
        (hγpL i) (hγqL i) hA t
    have hpathA : ∀ i : Fin n, ∀ᵐ ω ∂P,
        LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (LevyStochCalc.Poisson.Compensated.markCut A fun ω s e => coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp s ω) e i)
            (LevyStochCalc.Poisson.Compensated.measurable_markCut (hγmL i) hA) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (hγpL i)) hA)
            (fun T' hT' => LevyStochCalc.Poisson.Compensated.sq_markCut (hγqL i) A T' hT') t ω
          = LevyStochCalc.Ito.JumpSplitting.jumpSumLeftAt coeffs N Xp A t ω i
            - ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, coeffs.γ q.1 (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp q.1 ω) q.2 i
                ∂(LevyStochCalc.Poisson.referenceIntensity ν) := by
      intro i
      filter_upwards [LevyStochCalc.Ito.JumpFormula.stochasticIntegral_ae_eq_pathwise_of_zeroExtPos N ℱ hℱN
        (LevyStochCalc.Poisson.Compensated.markCut A fun ω s e => coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp s ω) e i)
        (LevyStochCalc.Poisson.Compensated.measurable_markCut (hγmL i) hA) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (hγpL i)) hA)
        (fun T' hT' => LevyStochCalc.Poisson.Compensated.sq_markCut (hγqL i) A T' hT') hA
        (LevyStochCalc.Ito.JumpFormula.markedPredictable_zeroExtPos_markCut (hpredL i) hA) hAν
        (fun ω s e he => by simp [LevyStochCalc.Poisson.Compensated.markCut, he]) hpos] with ω hω
      rw [hω]
      have h1 : ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
          LevyStochCalc.Poisson.Compensated.markCut A (fun ω s e => coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp s ω) e i) ω q.1 q.2 ∂(N.N ω)
          = LevyStochCalc.Ito.JumpSplitting.jumpSumLeftAt coeffs N Xp A t ω i :=
        setIntegral_congr_fun (measurableSet_Ioc.prod hA) fun q hq => by
          simp [LevyStochCalc.Poisson.Compensated.markCut, hq.2]
      have h2 : ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
          LevyStochCalc.Poisson.Compensated.markCut A (fun ω s e => coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp s ω) e i) ω q.1 q.2
            ∂(LevyStochCalc.Poisson.referenceIntensity ν)
          = ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, coeffs.γ q.1 (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp q.1 ω) q.2 i
              ∂(LevyStochCalc.Poisson.referenceIntensity ν) :=
        setIntegral_congr_fun (measurableSet_Ioc.prod hA) fun q hq => by
          simp [LevyStochCalc.Poisson.Compensated.markCut, hq.2]
      rw [h1, h2]
    have hwinL : ∀ i : Fin n, ∀ᵐ ω ∂P,
        IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp q.1 ω) q.2 i)
          (Set.Ioc (0 : ℝ) t ×ˢ A) (LevyStochCalc.Poisson.referenceIntensity ν) := by
      intro i
      filter_upwards [LevyStochCalc.Ito.JumpFormula.ae_integrableOn_window_of_zeroExtPos N hℱN hA hAν t (hpredL i)
        (hγmL i) (LevyStochCalc.Poisson.Compensated.window_energy_ne_top
          (fun ω s e => coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp s ω) e i) (hγmL i) (hγqL i)
          (A := A) hpos)] with ω hω
      exact hω.2
    have hμint : ∀ i : Fin n, ∀ᵐ ω ∂P,
        IntegrableOn (fun s => coeffs.μ s (Xp s ω) i) (Set.Icc (0 : ℝ) t) volume := by
      intro i
      have hmeas : Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖coeffs.μ s (Xp s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
        ((ENNReal.continuous_coe.measurable.comp (hμm i).nnnorm).pow_const
          2).lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) t))
      filter_upwards [ae_lt_top' hmeas.aemeasurable (hμq i t hpos).ne] with ω hω
      exact LevyStochCalc.Ito.JumpSplitting.integrableOn_Icc_of_lintegral_sq_lt_top
        ((hμm i).comp measurable_prodMk_left).aestronglyMeasurable hω
    refine MeasureTheory.ae_all_iff.mpr fun i => ?_
    filter_upwards [hSDE t ht, hcong i, hsplitCI i, hpathA i, hwinL i, hμint i]
      with ω hω hc hs hp hw hm
    obtain ⟨heq, hcint⟩ :=
      LevyStochCalc.Ito.JumpSplitting.integral_window_eq_and_integrableOn
        (fun s e => coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp s ω) e i) hw
    have hd : ∫ s in Set.Icc (0 : ℝ) t, LevyStochCalc.Ito.JumpSplitting.continuousDriftLeftAt coeffs ν Xp A i ω s ∂volume
        = (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (Xp s ω) i ∂volume)
          - ∫ s in Set.Icc (0 : ℝ) t,
              (∫ e in A, coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp s ω) e i ∂ν) ∂volume :=
      integral_sub hm hcint
    rw [hω i, ← hc, hs, hp,
      LevyStochCalc.Ito.JumpSplitting.multidimIntegral_eq_vectorItoMartingaleAt coeffs Xp ℱ hℱW hσm hσp hσq i t ω]
    simp only [LevyStochCalc.Brownian.Ito.vectorItoProcess]
    rw [hd, heq]
    ring
end Remainder

section JumpWithRemainder

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}

end JumpWithRemainder

end LevyStochCalc.Ito.JumpSplitting


