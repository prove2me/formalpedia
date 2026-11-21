-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_GeneratorAlongMarkStep_F000
-- name    : LevyStochCalc_BSDEJ_GeneratorAlongMarkStep_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:25:58.414573+00:00
-- url     : https://prove2.me/theorems/1646ff83-6286-4e58-a8b9-07e3fb13164b
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.GeneratorAlongMarkStep
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.GeneratorAlongMarkStep. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_Existence_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoIntegrandComplete_F001
import Definitions.Def_LevyStochCalc_Poisson_MarkStepIncrement_F003

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

/-- The `L²(ν)` norm of a finite combination `∑ₖ cₖ 1_{Bₖ}` of mark sets is at most
`∑ₖ ‖cₖ‖ ν(Bₖ)^{1/2}`. -/
theorem lintegral_sq_finsetCombination_le {K : ℕ} {B : Fin K → Set E}
    (hB : ∀ k, MeasurableSet (B k)) (c : Fin K → ℝ) :
    (∫⁻ e, (‖∑ k, c k * (B k).indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)
      ≤ ∑ k, (‖c k‖₊ : ℝ≥0∞) * ν (B k) ^ (1 / 2 : ℝ) := by
  have hfun : (fun e => ∑ k, c k * (B k).indicator (fun _ => (1 : ℝ)) e)
      = ∑ k, ((B k).indicator (fun _ => c k)) := by
    funext e
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : e ∈ B k <;> simp [h]
  have hsq : (∫⁻ e, (‖∑ k, c k * (B k).indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
      = eLpNorm (∑ k, ((B k).indicator (fun _ => c k))) 2 ν ^ 2 := by
    rw [LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral ν
      (∑ k, ((B k).indicator (fun _ => c k)))]
    exact congrArg (fun F : E → ℝ => ∫⁻ e, (‖F e‖₊ : ℝ≥0∞) ^ 2 ∂ν) hfun
  rw [hsq, ← ENNReal.rpow_natCast (eLpNorm (∑ k, ((B k).indicator (fun _ => c k))) 2 ν) 2,
    ← ENNReal.rpow_mul]
  norm_num
  refine (eLpNorm_sum_le (fun k _ =>
    ((measurable_const.indicator (hB k)).aestronglyMeasurable)) (by norm_num)).trans ?_
  refine Finset.sum_le_sum fun k _ => ?_
  rw [eLpNorm_indicator_const (hB k) (by norm_num) (by norm_num)]
  norm_num [enorm_eq_nnnorm]
/-- A Lipschitz generator is continuous in the coefficient vector of a finite combination of
mark sets of finite measure. -/
theorem continuous_generator_finsetCombination {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ}
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    {K : ℕ} {B : Fin K → Set E} (hB : ∀ k, MeasurableSet (B k)) (hBν : ∀ k, ν (B k) ≠ ⊤)
    (s y : ℝ) (z : Fin d → ℝ) :
    Continuous fun c : Fin K → ℝ =>
      f s y z (fun e => ∑ k, c k * (B k).indicator (fun _ => (1 : ℝ)) e) := by
  have hCν : (∑ k, ν (B k) ^ (1 / 2 : ℝ)) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun k _ => ENNReal.rpow_ne_top_of_nonneg (by norm_num) (hBν k)
  have hfin : ENNReal.ofReal L * (∑ k, ν (B k) ^ (1 / 2 : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCν
  refine LipschitzWith.continuous
    (K := (ENNReal.ofReal L * (∑ k, ν (B k) ^ (1 / 2 : ℝ))).toNNReal) ?_
  intro c c'
  rw [ENNReal.coe_toNNReal hfin, edist_eq_enorm_sub, enorm_eq_nnnorm]
  have hsub : ∀ e : E, (∑ k, c k * (B k).indicator (fun _ => (1 : ℝ)) e)
      - (∑ k, c' k * (B k).indicator (fun _ => (1 : ℝ)) e)
      = ∑ k, (c k - c' k) * (B k).indicator (fun _ => (1 : ℝ)) e := by
    intro e
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => (sub_mul _ _ _).symm
  have key := hlip s y y z z (fun e => ∑ k, c k * (B k).indicator (fun _ => (1 : ℝ)) e)
    (fun e => ∑ k, c' k * (B k).indicator (fun _ => (1 : ℝ)) e)
  simp only [sub_self, nnnorm_zero, ENNReal.coe_zero, zero_add] at key
  refine key.trans ?_
  have hrw : (∫⁻ e, (‖(∑ k, c k * (B k).indicator (fun _ => (1 : ℝ)) e)
        - (∑ k, c' k * (B k).indicator (fun _ => (1 : ℝ)) e)‖₊ : ℝ≥0∞) ^ 2 ∂ν)
      = ∫⁻ e, (‖∑ k, (c k - c' k) * (B k).indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2 ∂ν :=
    lintegral_congr fun e => by rw [hsub e]
  rw [hrw]
  refine (mul_le_mul_right (lintegral_sq_finsetCombination_le hB fun k => c k - c' k) _).trans ?_
  have hb : ∀ k : Fin K, (‖c k - c' k‖₊ : ℝ≥0∞) * ν (B k) ^ (1 / 2 : ℝ)
      ≤ edist c c' * ν (B k) ^ (1 / 2 : ℝ) := by
    intro k
    refine mul_le_mul_left ?_ _
    calc (‖c k - c' k‖₊ : ℝ≥0∞) = edist (c k) (c' k) := by
          rw [edist_eq_enorm_sub, enorm_eq_nnnorm]
      _ ≤ edist c c' := edist_le_pi_edist c c' k
  refine (mul_le_mul_right (Finset.sum_le_sum fun k _ => hb k) _).trans ?_
  rw [← Finset.mul_sum]
  exact le_of_eq (by ring)
/-- A generator measurable in `(s, y, z)` for each jump variable and Lipschitz in `(y, z, u)` is
jointly measurable in `(s, y, z)` and in the coefficient vector of a finite combination of mark
sets of finite measure. -/
theorem measurable_generator_finsetCombination {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ}
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u) {L : ℝ}
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    {K : ℕ} {B : Fin K → Set E} (hB : ∀ k, MeasurableSet (B k)) (hBν : ∀ k, ν (B k) ≠ ⊤) :
    Measurable fun q : (ℝ × ℝ × (Fin d → ℝ)) × (Fin K → ℝ) =>
      f q.1.1 q.1.2.1 q.1.2.2 (fun e => ∑ k, q.2 k * (B k).indicator (fun _ => (1 : ℝ)) e) := by
  have hu : Measurable (Function.uncurry fun (c : Fin K → ℝ) (p : ℝ × ℝ × (Fin d → ℝ)) =>
      f p.1 p.2.1 p.2.2 (fun e => ∑ k, c k * (B k).indicator (fun _ => (1 : ℝ)) e)) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun p => continuous_generator_finsetCombination hlip hB hBν p.1 p.2.1 p.2.2)
      (fun c => hf _)
  exact hu.comp measurable_swap
/-! ### The generator along a mark-step integrand -/

section MarkStep

variable [SigmaFinite ν] {g : TimeGrid}

/-- The coefficient vector of a mark-step integrand at a sample point and a time: the mark set
`Bₖ` carries the weight `∑ᵢ 1_{(pᵢ, pᵢ₊₁]}(s) ξᵢₖ(ω)`. -/
noncomputable def markStepCoeff (G : MarkStep Ω E ν g) (ω : Ω) (s : ℝ) : Fin G.K → ℝ :=
  fun k => ∑ i ∈ Finset.range g.N₀,
    (Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) s * G.ξ i k ω
/-- The coefficient vector of a mark-step integrand is jointly measurable in sample point and
time. -/
lemma measurable_markStepCoeff (G : MarkStep Ω E ν g) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => markStepCoeff G ω s) := by
  have hrw : (Function.uncurry fun (ω : Ω) (s : ℝ) => markStepCoeff G ω s)
      = fun p : Ω × ℝ => fun k => ∑ i ∈ Finset.range g.N₀,
        (Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) p.2 * G.ξ i k p.1 := rfl
  rw [hrw]
  refine measurable_pi_iff.2 fun k => Finset.measurable_sum _ fun i _ => ?_
  exact ((measurable_const.indicator measurableSet_Ioc).comp measurable_snd).mul
    ((G.ξ_measurable i k).comp measurable_fst)
/-- A mark-step integrand is, at each sample point and time, the finite combination of its mark
sets with coefficient vector `markStepCoeff`. -/
lemma eval_eq_finsetCombination (G : MarkStep Ω E ν g) (s : ℝ) (e : E) (ω : Ω) :
    G.eval s e ω = ∑ k, markStepCoeff G ω s k * (G.B k).indicator (fun _ => (1 : ℝ)) e := by
  simp only [MarkStep.eval, markStepCoeff, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
end MarkStep

end LevyStochCalc.BSDEJ.Generator


