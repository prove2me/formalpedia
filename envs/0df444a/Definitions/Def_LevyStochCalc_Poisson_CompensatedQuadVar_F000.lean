-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedQuadVar_F000
-- name    : LevyStochCalc_Poisson_CompensatedQuadVar_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:37:01.987335+00:00
-- url     : https://prove2.me/theorems/ed172568-0748-4618-91b3-611d7368284f
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedQuadVar
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedQuadVar. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Martingale_SquareCompensator_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedProcess_F002
import Definitions.Def_LevyStochCalc_Poisson_CompensatedProcess_F003
import Definitions.Def_LevyStochCalc_Poisson_CompensatedProcess_F004

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The quadratic-variation martingale of the compensated integral

For an adapted mark-step integrand `G`, the compensated square
`t ↦ (∫_0^t ∫_E G dÑ)² − ∫_0^t ∫_E G(u, e)² ν(de) du` is a martingale on the natural
filtration: the increment isometries of `MarkStep` give the set-level identity required by
`LevyStochCalc.Martingale.martingale_sq_sub_of_setIntegral`. The compensated square of the
`L²` integral process is then the `L¹`-limit of the stage compensated squares.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace MarkStep

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid} (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g)
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ : IsPoissonFiltration N ℱ)

/-- The compensator `∫_0^t ∫_E G(u, e)² ν(de) du` of a mark-step integrand. -/
noncomputable def compensator (t : ℝ) (ω : Ω) : ℝ :=
  ∫ u in Set.Icc (0 : ℝ) t, ∫ e, (G.eval u e ω) ^ 2 ∂ν ∂volume
omit [IsProbabilityMeasure P] in
/-- The mark integral of the squared integrand is bounded, uniformly in time and sample. -/
lemma integral_eval_sq_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ u ω, ∫ e, (G.eval u e ω) ^ 2 ∂ν ≤ C := by
  obtain ⟨C, hC⟩ := G.eval_bounded
  refine ⟨C ^ 2 * (ν (⋃ k, G.B k)).toReal, by positivity, fun u ω => ?_⟩
  have hint : IntegrableOn (fun _ : E => C ^ 2) (⋃ k, G.B k) ν :=
    integrableOn_const G.measure_iUnion_B_ne_top
  calc ∫ e, (G.eval u e ω) ^ 2 ∂ν
      = ∫ e in ⋃ k, G.B k, (G.eval u e ω) ^ 2 ∂ν := by
        rw [← integral_indicator G.measurableSet_iUnion_B]
        refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
        by_cases he : e ∈ ⋃ k, G.B k
        · rw [Set.indicator_of_mem he]
        · rw [Set.indicator_of_notMem he]
          change (G.eval u e ω) ^ 2 = 0
          rw [G.eval_support ω u e he]
          ring
    _ ≤ ∫ _ in ⋃ k, G.B k, C ^ 2 ∂ν := by
        refine setIntegral_mono_on ?_ hint G.measurableSet_iUnion_B fun e _ => ?_
        · refine hint.mono' ?_ (Filter.Eventually.of_forall fun e => ?_)
          · exact ((G.eval_measurable.comp (by fun_prop :
                Measurable fun e : E => ((ω, u, e) : Ω × ℝ × E))).pow_const 2).aestronglyMeasurable
          · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            nlinarith [hC ω u e, abs_nonneg (G.eval u e ω), sq_abs (G.eval u e ω)]
        · nlinarith [hC ω u e, abs_nonneg (G.eval u e ω), sq_abs (G.eval u e ω)]
    _ = C ^ 2 * (ν (⋃ k, G.B k)).toReal := by
        rw [setIntegral_const, smul_eq_mul, mul_comm, measureReal_def]
omit [IsProbabilityMeasure P] in
lemma integral_eval_sq_nonneg (u : ℝ) (ω : Ω) : 0 ≤ ∫ e, (G.eval u e ω) ^ 2 ∂ν :=
  integral_nonneg fun _ => sq_nonneg _
omit [IsProbabilityMeasure P] in
lemma measurable_integral_eval_sq :
    Measurable (fun q : Ω × ℝ => ∫ e, (G.eval q.2 e q.1) ^ 2 ∂ν) := by
  have h : Measurable (fun r : (Ω × ℝ) × E => (G.eval r.1.2 r.2 r.1.1) ^ 2) :=
    (G.eval_measurable.comp (by fun_prop :
      Measurable fun r : (Ω × ℝ) × E => ((r.1.1, r.1.2, r.2) : Ω × ℝ × E))).pow_const 2
  exact h.stronglyMeasurable.integral_prod_right'.measurable
omit [IsProbabilityMeasure P] in
lemma compensator_nonneg (t : ℝ) (ω : Ω) : 0 ≤ G.compensator t ω :=
  integral_nonneg fun u => G.integral_eval_sq_nonneg u ω
omit [IsProbabilityMeasure P] in
/-- The compensator vanishes at nonpositive times. -/
lemma compensator_of_nonpos {t : ℝ} (ht : t ≤ 0) (ω : Ω) : G.compensator t ω = 0 := by
  unfold compensator
  rw [Measure.restrict_eq_zero.2 (by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_of_nonpos (by linarith)), integral_zero_measure]
omit [IsProbabilityMeasure P] in
/-- The mark integral of the squared integrand is integrable in time over any set of finite
Lebesgue measure. -/
lemma integrableOn_integral_eval_sq {S : Set ℝ} (hS : volume S ≠ ⊤) (ω : Ω) :
    IntegrableOn (fun u => ∫ e, (G.eval u e ω) ^ 2 ∂ν) S volume := by
  obtain ⟨_, hC⟩ := Classical.choose_spec G.integral_eval_sq_le
  have hint : IntegrableOn (fun _ : ℝ => Classical.choose G.integral_eval_sq_le) S volume :=
    integrableOn_const hS
  have hmeas : AEStronglyMeasurable (fun u => ∫ e, (G.eval u e ω) ^ 2 ∂ν)
      (volume.restrict S) :=
    ((G.measurable_integral_eval_sq).comp (measurable_prodMk_left (x := ω))).aestronglyMeasurable
  exact hint.mono' hmeas (Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg (G.integral_eval_sq_nonneg u ω)]
    exact hC u ω)
omit [IsProbabilityMeasure P] in
lemma compensator_le {t : ℝ} (ht : 0 ≤ t) (ω : Ω) :
    G.compensator t ω ≤ (Classical.choose G.integral_eval_sq_le) * t := by
  obtain ⟨_, hC⟩ := Classical.choose_spec G.integral_eval_sq_le
  set C := Classical.choose G.integral_eval_sq_le
  have hint : IntegrableOn (fun _ : ℝ => C) (Set.Icc (0 : ℝ) t) volume :=
    integrableOn_const measure_Icc_lt_top.ne
  calc G.compensator t ω ≤ ∫ _ in Set.Icc (0 : ℝ) t, C ∂volume :=
        setIntegral_mono_on (G.integrableOn_integral_eval_sq measure_Icc_lt_top.ne ω) hint
          measurableSet_Icc fun u _ => hC u ω
    _ = C * t := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Icc, sub_zero,
          ENNReal.toReal_ofReal ht, mul_comm]
omit [IsProbabilityMeasure P] in
/-- The compensator increment between two nonnegative times is the integral of the squared
integrand over the intervening interval. -/
lemma compensator_sub {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ω : Ω) :
    G.compensator t ω - G.compensator s ω
      = ∫ u in Set.Ioc s t, ∫ e, (G.eval u e ω) ^ 2 ∂ν ∂volume := by
  unfold compensator
  rw [← Set.Icc_union_Ioc_eq_Icc hs hst, setIntegral_union
    (Set.disjoint_left.2 fun x hx hx' => not_le.2 hx'.1 hx.2) measurableSet_Ioc
    (G.integrableOn_integral_eval_sq measure_Icc_lt_top.ne ω)
    (G.integrableOn_integral_eval_sq measure_Ioc_lt_top.ne ω)]
  ring
omit [IsProbabilityMeasure P] in
/-- Fubini for the squared integrand over a time set of finite Lebesgue measure. -/
lemma integral_integral_eval_sq_swap {S : Set ℝ} (hSfin : volume S ≠ ⊤) (ω : Ω) :
    ∫ e, ∫ σ in S, (G.eval σ e ω) ^ 2 ∂volume ∂ν
      = ∫ σ in S, ∫ e, (G.eval σ e ω) ^ 2 ∂ν ∂volume := by
  obtain ⟨C, hC⟩ := G.eval_bounded
  refine integral_integral_swap ?_
  have hmeas : Measurable (fun q : E × ℝ => (G.eval q.2 q.1 ω) ^ 2) :=
    (G.eval_measurable.comp (by fun_prop :
      Measurable fun q : E × ℝ => ((ω, q.2, q.1) : Ω × ℝ × E))).pow_const 2
  have hind : Integrable (((⋃ k, G.B k) ×ˢ (Set.univ : Set ℝ)).indicator (fun _ => C ^ 2))
      (ν.prod (volume.restrict S)) := by
    rw [integrable_indicator_iff (G.measurableSet_iUnion_B.prod MeasurableSet.univ)]
    refine integrableOn_const ?_
    rw [Measure.prod_prod, Measure.restrict_apply_univ]
    exact ENNReal.mul_ne_top G.measure_iUnion_B_ne_top hSfin
  refine hind.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun q => ?_)
  change ‖(G.eval q.2 q.1 ω) ^ 2‖ ≤ _
  by_cases hq : q.1 ∈ ⋃ k, G.B k
  · rw [Set.indicator_of_mem (Set.mem_prod.2 ⟨hq, Set.mem_univ _⟩), Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
    nlinarith [hC ω q.2 q.1, abs_nonneg (G.eval q.2 q.1 ω), sq_abs (G.eval q.2 q.1 ω)]
  · rw [Set.indicator_of_notMem (fun h => hq h.1), G.eval_support ω q.2 q.1 hq]
    simp
lemma measurable_compensator (t : ℝ) : Measurable (G.compensator t) :=
  G.measurable_integral_eval_sq.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Set.Icc (0 : ℝ) t)) |>.measurable
lemma integrable_compensator (t : ℝ) : Integrable (G.compensator t) P := by
  rcases le_or_gt 0 t with ht | ht
  · refine Integrable.mono' (integrable_const (Classical.choose G.integral_eval_sq_le * t))
      (G.measurable_compensator t).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (G.compensator_nonneg t ω)]
    exact G.compensator_le ht ω
  · have h : G.compensator t = fun _ => 0 := funext fun ω => G.compensator_of_nonpos ht.le ω
    rw [h]
    exact integrable_const 0
end MarkStep

end LevyStochCalc.Poisson.Compensated


