-- Prove2me | Definitions.Def_SourceProof_35da2440c6c558bf9e0bd5fa
-- name    : SourceProof_35da2440c6c558bf9e0bd5fa
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:28:53.438915+00:00
-- url     : https://prove2.me/theorems/9df4b81a-8eb5-4bb7-8b59-62c7ca8fc4ca
-- title:
--   LevyStochCalc source module: SourceProof_35da2440c6c558bf9e0bd5fa
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Generator.progressive_generator_along_markStep` comes from the `LevyStochCalc.BSDEJ.GeneratorAlongMarkStep` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_GeneratorAlongMarkStep_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The generator of a BSDEJ along a mark-step jump integrand

A generator `f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ` that is measurable in `(s, y, z)` for each
fixed jump variable and Lipschitz in `(y, z, u)` for the `L²(ν)` distance on the jump variable
depends on a finite combination `∑ₖ cₖ 1_{Bₖ}` of mark sets of finite measure only through the
coefficient vector `c`, continuously, so `(p, c) ↦ f p.1 p.2.1 p.2.2 (∑ₖ cₖ 1_{Bₖ})` is jointly
measurable.

A mark-step integrand `G` is such a combination at every `(ω, s)`, with coefficient vector
`markStepCoeff G ω s`; consequently the composite process
`(ω, s) ↦ f s (Y s ω) (Z s ω) (fun e => G.eval s e ω)` is jointly measurable, and progressively
measurable for a filtration to which `Y`, `Z` and the coefficients of `G` are adapted.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Generator

open LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {ν : Measure E} {d : ℕ}

/-! ### Finite combinations of mark sets -/

/-! ### The generator along a mark-step integrand -/

section MarkStep

variable [SigmaFinite ν] {g : TimeGrid}


theorem _root_.Prove2MeSourceProof.h_35da2440c6c558bf9e0bd5fa {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ}
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u) {L : ℝ}
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    {ℱ : Filtration ℝ mΩ} (G : MarkStep Ω E ν g) (hG : G.Adapted ℱ) {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)}
    (hYp : Probability.ProgressivelyMeasurable ℱ fun ω s => Y s ω)
    (hZp : ∀ i, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i) :
    Probability.ProgressivelyMeasurable ℱ
      fun ω s => f s (Y s ω) (Z s ω) (fun e => G.eval s e ω) := by
  intro t
  obtain ⟨K, B, ξ, c, hBm, hBf, hξ, hcform, hev⟩ :
      ∃ (K : ℕ) (B : Fin K → Set E) (ξ : ℕ → Fin K → Ω → ℝ) (c : Ω → ℝ → Fin K → ℝ),
        (∀ k, MeasurableSet (B k)) ∧ (∀ k, ν (B k) ≠ ⊤) ∧
          (∀ i, i < g.N₀ → ∀ k, StronglyMeasurable[ℱ (g.p i)] (ξ i k)) ∧
          (∀ ω s k, c ω s k = ∑ i ∈ Finset.range g.N₀,
            (Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) s * ξ i k ω) ∧
          ∀ s e ω, G.eval s e ω = ∑ k, c ω s k * (B k).indicator (fun _ => (1 : ℝ)) e :=
    ⟨G.K, G.B, G.ξ, LevyStochCalc.BSDEJ.Generator.markStepCoeff G, G.B_measurable, G.B_finite, hG, fun _ _ _ => rfl,
      LevyStochCalc.BSDEJ.Generator.eval_eq_finsetCombination G⟩
  simp only [hev]
  letI : MeasurableSpace Ω := ℱ t
  have hY : Measurable fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => Y s p.1) p.2 :=
    (hYp t).measurable
  have hZ : ∀ i, Measurable fun p : Ω × ℝ =>
      (Set.Iic t).indicator (fun s => Z s p.1 i) p.2 := fun i => (hZp i t).measurable
  have hc : ∀ k, Measurable fun p : Ω × ℝ =>
      (Set.Iic t).indicator (fun s => c p.1 s k) p.2 := by
    intro k
    have hEq : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => c p.1 s k) p.2)
        = fun p : Ω × ℝ => ∑ i ∈ Finset.range g.N₀,
          (Set.Iic t ∩ Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) p.2
            * ξ i k p.1 := by
      funext p
      by_cases hp : p.2 ∈ Set.Iic t
      · rw [Set.indicator_of_mem hp, hcform]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : p.2 ∈ Set.Ioc (g.p i) (g.p (i + 1))
        · rw [Set.indicator_of_mem hi, Set.indicator_of_mem (Set.mem_inter hp hi)]
        · rw [Set.indicator_of_notMem hi,
            Set.indicator_of_notMem (fun h => hi (Set.mem_of_mem_inter_right h))]
      · rw [Set.indicator_of_notMem hp]
        exact (Finset.sum_eq_zero fun i _ => by
          rw [Set.indicator_of_notMem (fun h => hp (Set.mem_of_mem_inter_left h)), zero_mul]).symm
    rw [hEq]
    refine Finset.measurable_sum _ fun i hi => ?_
    by_cases hti : g.p i ≤ t
    · have hm : Measurable[ℱ t] (ξ i k) :=
        ((hξ i (Finset.mem_range.1 hi) k).mono (ℱ.mono hti)).measurable
      exact ((measurable_const.indicator
        (measurableSet_Iic.inter measurableSet_Ioc)).comp measurable_snd).mul
        (hm.comp measurable_fst)
    · have hzero : (fun p : Ω × ℝ =>
          (Set.Iic t ∩ Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) p.2
            * ξ i k p.1) = fun _ => 0 := by
        funext p
        rw [Set.indicator_of_notMem, zero_mul]
        rintro ⟨h1, h2⟩
        exact hti (h2.1.le.trans h1)
      rw [hzero]
      exact measurable_const
  have hmain : Measurable fun p : Ω × ℝ =>
      f p.2 ((Set.Iic t).indicator (fun s => Y s p.1) p.2)
        (fun i => (Set.Iic t).indicator (fun s => Z s p.1 i) p.2)
        (fun e => ∑ k, (Set.Iic t).indicator (fun s => c p.1 s k) p.2
          * (B k).indicator (fun _ => (1 : ℝ)) e) :=
    (LevyStochCalc.BSDEJ.Generator.measurable_generator_finsetCombination hf hlip hBm hBf).comp
      ((measurable_snd.prodMk (hY.prodMk (measurable_pi_iff.2 hZ))).prodMk
        (measurable_pi_iff.2 hc))
  have heq : (fun p : Ω × ℝ => (Set.Iic t).indicator
        (fun s => f s (Y s p.1) (Z s p.1)
          (fun e => ∑ k, c p.1 s k * (B k).indicator (fun _ => (1 : ℝ)) e)) p.2)
      = {p : Ω × ℝ | p.2 ∈ Set.Iic t}.indicator (fun p : Ω × ℝ =>
        f p.2 ((Set.Iic t).indicator (fun s => Y s p.1) p.2)
          (fun i => (Set.Iic t).indicator (fun s => Z s p.1 i) p.2)
          (fun e => ∑ k, (Set.Iic t).indicator (fun s => c p.1 s k) p.2
            * (B k).indicator (fun _ => (1 : ℝ)) e)) := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · rw [Set.indicator_of_mem hp,
        Set.indicator_of_mem (show p ∈ {q : Ω × ℝ | q.2 ∈ Set.Iic t} from hp)]
      simp only [Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem
        (show p ∉ {q : Ω × ℝ | q.2 ∈ Set.Iic t} from hp)]
  have final : StronglyMeasurable fun p : Ω × ℝ => (Set.Iic t).indicator
      (fun s => f s (Y s p.1) (Z s p.1)
        (fun e => ∑ k, c p.1 s k * (B k).indicator (fun _ => (1 : ℝ)) e)) p.2 := by
    rw [heq]
    exact (stronglyMeasurable_iff_measurable.2 hmain).indicator (measurable_snd measurableSet_Iic)
  exact final
end MarkStep

end LevyStochCalc.BSDEJ.Generator


