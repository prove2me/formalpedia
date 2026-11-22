-- Prove2me | Definitions.Def_SourceProof_7eb93313fc9473428879f9ec
-- name    : SourceProof_7eb93313fc9473428879f9ec
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T10:19:21.68166+00:00
-- url     : https://prove2.me/theorems/f471137e-8643-4af5-9fa1-bfb9cd23a2f3
-- title:
--   LevyStochCalc source module: SourceProof_7eb93313fc9473428879f9ec
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_add_jumpSumLeftAt_add_remainder_of_path` comes from the `LevyStochCalc.Ito.JumpSplittingRemainderDecomposition` module. The staged Lean declaration includes its source proof and dependency references. Some theorem-statement references have been redirected to generated helpers; formal type equivalence still requires certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_AtomJumpRelation_F001
import Definitions.Def_LevyStochCalc_Ito_TruncatedContinuousPart_F001
import Definitions.Def_SourceProof_f631eb99340a9e8c76355a4c

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

theorem _root_.Prove2MeSourceProof.h_7eb93313fc9473428879f9ec (Z : ℝ → Ω → Fin n → ℝ)
    (hXpcadlag : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => Xp s ω) (𝓝[>] t) (𝓝 (Xp t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => Xp s ω i) (𝓝[<] t) (𝓝 L))
    (hZright : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => Z s ω) (𝓝[>] t) (𝓝 (Z t ω)))
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
    (V : ℝ → Ω → Fin n → ℝ)
    (hVae : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      V t ω i = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
        (fun i j ω s => coeffs.σ s (Xp s ω) i j) hσm hσp hσq (fun _ => x₀)
        (continuousDriftLeftAt coeffs ν Xp A) t ω i)
    (hVright : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Tendsto (fun s => V s ω i) (𝓝[>] t) (𝓝 (V t ω i))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Z t ω i = V t ω i + jumpSumLeftAt coeffs N Xp A t ω i
        + stochasticIntegral N ℱ hℱN
            (markCut Aᶜ fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i)
            (measurable_markCut (hγmL i) hA.compl) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (hγpL i)) hA.compl)
            (fun T' hT' => sq_markCut (hγqL i) Aᶜ T' hT') t ω := by
  have hwin := _root_.Prove2MeSourceProof.h_aef3a69ee291c75edeeec8a2 coeffs N Xp ℱ hℱN hA hAν hpredL hγmL hγqL
  have hRcad : ∀ i : Fin n, ∀ᵐ ω ∂P, ∀ t : ℝ,
      Tendsto (fun s => LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
          (LevyStochCalc.Poisson.Compensated.markCut Aᶜ fun ω s e => coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp s ω) e i)
          (LevyStochCalc.Poisson.Compensated.measurable_markCut (hγmL i) hA.compl) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (hγpL i)) hA.compl)
          (fun T' hT' => LevyStochCalc.Poisson.Compensated.sq_markCut (hγqL i) Aᶜ T' hT') s ω) (𝓝[>] t)
        (𝓝 (LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
          (LevyStochCalc.Poisson.Compensated.markCut Aᶜ fun ω s e => coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp s ω) e i)
          (LevyStochCalc.Poisson.Compensated.measurable_markCut (hγmL i) hA.compl) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (hγpL i)) hA.compl)
          (fun T' hT' => LevyStochCalc.Poisson.Compensated.sq_markCut (hγqL i) Aᶜ T' hT') t ω)) := by
    intro i
    filter_upwards [LevyStochCalc.Poisson.Compensated.stochasticIntegral_cadlag N ℱ hℱN
      (LevyStochCalc.Poisson.Compensated.markCut Aᶜ fun ω s e => coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp s ω) e i)
      (LevyStochCalc.Poisson.Compensated.measurable_markCut (hγmL i) hA.compl) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (hγpL i)) hA.compl)
      (fun T' hT' => LevyStochCalc.Poisson.Compensated.sq_markCut (hγqL i) Aᶜ T' hT')] with ω hω t
    exact (hω t).1
  have key : ∀ᵐ ω ∂P, ∀ (i : Fin n) (t : ℝ), 0 ≤ t →
      Z t ω i = V t ω i + LevyStochCalc.Ito.JumpSplitting.jumpSumLeftAt coeffs N Xp A t ω i
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (LevyStochCalc.Poisson.Compensated.markCut Aᶜ fun ω s e => coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp s ω) e i)
            (LevyStochCalc.Poisson.Compensated.measurable_markCut (hγmL i) hA.compl) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (hγpL i)) hA.compl)
            (fun T' hT' => LevyStochCalc.Poisson.Compensated.sq_markCut (hγqL i) Aᶜ T' hT') t ω := by
    refine MeasureTheory.ae_all_iff.mpr fun i => ?_
    refine _root_.Prove2MeSourceProof.h_231d4b01442d4e78331883f1 (P := P) (Y := fun s ω => Z s ω i)
      (Z := fun s ω => V s ω i + LevyStochCalc.Ito.JumpSplitting.jumpSumLeftAt coeffs N Xp A s ω i
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (LevyStochCalc.Poisson.Compensated.markCut Aᶜ fun ω s e => coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp s ω) e i)
            (LevyStochCalc.Poisson.Compensated.measurable_markCut (hγmL i) hA.compl) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (hγpL i)) hA.compl)
            (fun T' hT' => LevyStochCalc.Poisson.Compensated.sq_markCut (hγqL i) Aᶜ T' hT') s ω) ?_ ?_ ?_
    · intro q hq
      filter_upwards [_root_.Prove2MeSourceProof.h_f631eb99340a9e8c76355a4c coeffs N Xp x₀
        ℱ hℱW hσm hσp hσq hℱN hγm hγp hγq hγmL hγpL hγqL Z hXpcadlag hSDE hA hAν hpredL hμm hμq
        hq, hVae (q : ℝ) hq] with ω h1 h2
      rw [h1 i, h2 i]
    · filter_upwards [hZright] with ω hω t ht
      exact ((continuous_apply i).tendsto (Z t ω)).comp (hω t ht)
    · filter_upwards [hVright, hwin, hRcad i] with ω hVω hwω hRω t ht
      exact ((hVω t ht i).add (LevyStochCalc.Ito.JumpSplitting.tendsto_jumpSumLeftAt_nhdsWithin_Ioi coeffs N Xp hA (hγmL i)
        (fun T => hwω T i) t)).add (hRω t)
  filter_upwards [key] with ω hω t ht i
  exact hω i t ht
end Remainder

section JumpWithRemainder

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}

end JumpWithRemainder

end LevyStochCalc.Ito.JumpSplitting


