-- Prove2me | Definitions.Def_SourceProof_939e239754a30a8726cdafe7
-- name    : SourceProof_939e239754a30a8726cdafe7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T10:16:42.327177+00:00
-- url     : https://prove2.me/theorems/80966a15-584b-48d1-a96b-3b9d88339d43
-- title:
--   LevyStochCalc source module: SourceProof_939e239754a30a8726cdafe7
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpSplitting.ae_exists_atomEnum_jump_eq_gamma_add_remainder` comes from the `LevyStochCalc.Ito.JumpSplittingRemainderDecomposition` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_AtomJumpRelation_F001
import Definitions.Def_LevyStochCalc_Ito_TruncatedContinuousPart_F001

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

end Remainder

section JumpWithRemainder

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}


theorem _root_.Prove2MeSourceProof.h_939e239754a30a8726cdafe7
    (coeffs : Setting.JumpDiffusionCoeffs n d E)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (Xp : ℝ → Ω → Fin n → ℝ) (A : Set E) (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ)
    (V : ℝ → Ω → Fin n → ℝ) (hVc : ∀ᵐ ω ∂P, Continuous fun t => V t ω)
    (R : Fin n → ℝ → Ω → ℝ)
    (hRl : ∀ᵐ ω ∂P, ∀ (i : Fin n) (t : ℝ), ∃ L : ℝ, Tendsto (fun s => R i s ω) (𝓝[<] t) (𝓝 L))
    (hsplit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Xp t ω i = V t ω i + jumpSumLeftAt coeffs N Xp A t ω i + R i t ω) :
    ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E), StrictMono θ ∧
      (∀ j, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A) ∧
      (∀ g : ℝ × E → ℝ,
        ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j)) ∧
      ∀ (j : Fin K) (i : Fin n),
        Xp (θ j) ω i
          = leftLimPathAt Xp (θ j) ω i + coeffs.γ (θ j) (leftLimPathAt Xp (θ j) ω) (ε j) i
            + (R i (θ j) ω - Function.leftLim (fun s => R i s ω) (θ j)) := by
  classical
  filter_upwards [LevyStochCalc.Ito.JumpSplitting.ae_exists_atomEnum_jumpSumLeftAt_eq_sum coeffs N Xp A hA hAν T, hVc, hRl,
    hsplit] with ω hstep hVω hRω hsp
  obtain ⟨K, θ, ε, hmono, hmem, hg, hsum⟩ := hstep
  refine ⟨K, θ, ε, hmono, hmem, hg, fun j i => ?_⟩
  -- each remainder converges to its left limit
  have hRlim : ∀ i' : Fin n, Tendsto (fun s => R i' s ω) (𝓝[<] (θ j))
      (𝓝 (Function.leftLim (fun s => R i' s ω) (θ j))) := by
    intro i'
    obtain ⟨L, hL⟩ := hRω i' (θ j)
    rw [leftLim_eq_of_tendsto hL]
    exact hL
  -- the left limit of the path at the arrival time
  have hlim : ∀ i' : Fin n, Tendsto (fun t => Xp t ω i') (𝓝[<] (θ j))
      (𝓝 (V (θ j) ω i' + ∑ k ∈ Finset.univ.filter fun k => θ k < θ j,
        coeffs.γ (θ k) (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp (θ k) ω) (ε k) i'
        + Function.leftLim (fun s => R i' s ω) (θ j))) := by
    intro i'
    have hVlim : Tendsto (fun t => V t ω i') (𝓝[<] (θ j)) (𝓝 (V (θ j) ω i')) :=
      (((continuous_apply i').comp hVω).tendsto (θ j)).mono_left nhdsWithin_le_nhds
    have hstepl := _root_.Prove2MeSourceProof.h_703991d88a6fb30ce9f631df θ
      (fun k => coeffs.γ (θ k) (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp (θ k) ω) (ε k) i') (θ j)
    refine ((hVlim.add hstepl).add (hRlim i')).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (hmem j).1.1] with t ht
    rw [hsp t ht.1.le i', hsum t (le_trans ht.2.le (hmem j).1.2) i']
  have hleft : LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp (θ j) ω
      = fun i' => V (θ j) ω i' + ∑ k ∈ Finset.univ.filter fun k => θ k < θ j,
          coeffs.γ (θ k) (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp (θ k) ω) (ε k) i'
          + Function.leftLim (fun s => R i' s ω) (θ j) :=
    LevyStochCalc.Ito.JumpSplitting.leftLimPathAt_eq_of_tendsto hlim
  have hsplitj : (Finset.univ.filter fun k => θ k ≤ θ j)
      = insert j (Finset.univ.filter fun k => θ k < θ j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      hmono.le_iff_le, hmono.lt_iff_lt]
    exact le_iff_eq_or_lt
  have hnotmem : j ∉ Finset.univ.filter fun k => θ k < θ j := by simp
  have hleft_i : LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp (θ j) ω i
      = V (θ j) ω i + ∑ k ∈ Finset.univ.filter fun k => θ k < θ j,
          coeffs.γ (θ k) (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt Xp (θ k) ω) (ε k) i
          + Function.leftLim (fun s => R i s ω) (θ j) := by
    rw [hleft]
  rw [hsp (θ j) (hmem j).1.1.le i, hsum (θ j) (hmem j).1.2 i, hsplitj,
    Finset.sum_insert hnotmem, hleft_i]
  ring
end JumpWithRemainder

end LevyStochCalc.Ito.JumpSplitting


