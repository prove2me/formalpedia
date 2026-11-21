-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_MarkStepIsometry_F001
-- name    : LevyStochCalc_Poisson_MarkStepIsometry_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:36:40.757947+00:00
-- url     : https://prove2.me/theorems/21850cd4-cbdd-4c53-9d60-bbeb9eb54d04
-- title:
--   Source declarations: LevyStochCalc.Poisson.MarkStepIsometry
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.MarkStepIsometry. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityLimit_F000
import Definitions.Def_LevyStochCalc_Poisson_MarkStepIsometry_F000
import Definitions.Def_SourceProof_24d7e98c77e2168bb8fc8995
import Definitions.Def_SourceProof_a7deec5abe53c22fffa52848
import Definitions.Def_SourceProof_c795c860ec71dd220bc36203

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Mark-step integrands, their compensated integrals and the `L²` isometry

A *mark-step integrand* is a finite sum `∑ᵢ 𝟙_{(pᵢ, pᵢ₊₁]}(s) ∑ₖ ξᵢₖ(ω) 𝟙_{Bₖ}(e)` over a
time grid `0 = p₀ < ⋯ < p_{N₀}` (`TimeGrid`) and finitely many mark sets `Bₖ` of finite
`ν`-measure, with bounded coefficients `ξᵢₖ`. Its compensated integral up to time `t` is
`∑ᵢ ∑ₖ ξᵢₖ Ñ((pᵢ ∧ t, pᵢ₊₁ ∧ t] × Bₖ)`. Clamping a grid at a time `t` (`TimeGrid.clamp`)
expresses that integral as the integral over the whole clamped horizon, which carries the
`L²` isometry from the horizon to every time, in both real and `ℝ≥0∞` form.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace TimeGrid

variable (g : TimeGrid)

end TimeGrid

namespace MarkStep

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν g)

end MarkStep

namespace TimeGrid

variable (g : TimeGrid)

end TimeGrid

namespace MarkStep

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid} {N : PoissonRandomMeasure P ν} {G : MarkStep Ω E ν g}
variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

lemma Adapted.clamp (hG : G.Adapted ℱ) (t : ℝ) (ht : 0 ≤ t) :
    (G.clamp t ht).Adapted ℱ := by
  intro i hi k
  have h := hG i (g.lt_of_lt_clampIndex hi).1 k
  change @StronglyMeasurable Ω ℝ _ (ℱ (min (g.p i) t)) (G.ξ i k)
  rwa [min_eq_left (g.lt_of_lt_clampIndex hi).2.le]
/-- The `L²` isometry of the compensated integral up to any time `t ≥ 0`. -/
theorem integral_sq_at (N : PoissonRandomMeasure P ν)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ : IsPoissonFiltration N ℱ)
    (G : MarkStep Ω E ν g)
    (hG : G.Adapted ℱ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, (G.integral N t ω) ^ 2 ∂P
      = ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) t, (G.eval s e ω) ^ 2 ∂volume ∂ν) ∂P := by
  simp_rw [(fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_a7deec5abe53c22fffa52848 p2mMethodArg0 G) N t ht]
  rw [(G.clamp t ht).integral_full_sq N hℱ (hG.clamp t ht) (g.clamp_horizon_le t ht)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  rw [(_root_.Prove2MeSourceProof.h_24d7e98c77e2168bb8fc8995 G) t ht, if_pos hs.2]
section Eval

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid} (G : MarkStep Ω E ν g)

lemma abs_indicator_one_le {α : Type*} (s : Set α) (x : α) :
    |s.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
  by_cases h : x ∈ s <;> simp [h]
/-- The integrand is jointly measurable in sample point, time and mark. -/
lemma eval_measurable : Measurable (fun q : Ω × ℝ × E => G.eval q.2.1 q.2.2 q.1) := by
  unfold eval
  refine Finset.measurable_sum _ fun i _ => Measurable.mul ?_ (Finset.measurable_sum _ fun k _ =>
    Measurable.mul ?_ ?_)
  · exact (measurable_const.indicator measurableSet_Ioc).comp (measurable_fst.comp measurable_snd)
  · exact (G.ξ_measurable i k).comp measurable_fst
  · exact (measurable_const.indicator (G.B_measurable k)).comp (measurable_snd.comp measurable_snd)
/-- The integrand is bounded. -/
lemma eval_bounded : ∃ C : ℝ, ∀ ω s e, |G.eval s e ω| ≤ C := by
  choose M hM using G.ξ_bounded
  refine ⟨∑ i ∈ Finset.range g.N₀, ∑ k, |M i k|, fun ω s e => ?_⟩
  unfold eval
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  refine (mul_le_of_le_one_left (abs_nonneg _) (abs_indicator_one_le _ _)).trans ?_
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) (abs_indicator_one_le _ _)).trans
    ((hM i k ω).trans (le_abs_self _))
/-- The integrand vanishes off the union of the mark sets. -/
lemma eval_support (ω : Ω) (s : ℝ) (e : E) (he : e ∉ ⋃ k, G.B k) : G.eval s e ω = 0 := by
  unfold eval
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finset.sum_eq_zero fun k _ => ?_, mul_zero]
  rw [Set.indicator_of_notMem (fun hk => he (Set.mem_iUnion.2 ⟨k, hk⟩)), mul_zero]
lemma measurableSet_iUnion_B : MeasurableSet (⋃ k, G.B k) :=
  MeasurableSet.iUnion fun k => G.B_measurable k
lemma measure_iUnion_B_ne_top : ν (⋃ k, G.B k) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun k _ => G.B_finite k)
    (measure_iUnion_fintype_le ν G.B)
variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ)

include hℱ in
/-- The `L²` isometry over the whole horizon, in `ℝ≥0∞` form. -/
theorem lintegral_full_sq (hG : G.Adapted ℱ) {T : ℝ} (hT : g.horizon ≤ T) :
    ∫⁻ ω, (‖G.full N ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν ∂P := by
  obtain ⟨C, hC⟩ := G.eval_bounded
  rw [lintegral_sq_eq_ofReal_integral (G.memLp_full N), G.integral_full_sq N hℱ hG hT]
  exact _root_.Prove2MeSourceProof.h_c795c860ec71dd220bc36203 (fun ω s e => G.eval s e ω) G.eval_measurable hC
    G.measurableSet_iUnion_B G.measure_iUnion_B_ne_top (fun ω s e he => G.eval_support ω s e he)
include hℱ in
/-- The `L²` isometry up to any time `t ≥ 0`, in `ℝ≥0∞` form. -/
theorem lintegral_integral_sq_at (hG : G.Adapted ℱ) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (‖G.integral N t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν ∂P := by
  simp_rw [(fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_a7deec5abe53c22fffa52848 p2mMethodArg0 G) N t ht]
  rw [(G.clamp t ht).lintegral_full_sq N hℱ (hG.clamp t ht) (g.clamp_horizon_le t ht)]
  refine lintegral_congr fun ω => lintegral_congr fun e => ?_
  refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  rw [(_root_.Prove2MeSourceProof.h_24d7e98c77e2168bb8fc8995 G) t ht, if_pos hs.2]
end Eval

end MarkStep

end LevyStochCalc.Poisson.Compensated


