-- Prove2me | Definitions.Def_NonvacuityContract_F000
-- name    : NonvacuityContract_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:37:55.432669+00:00
-- url     : https://prove2.me/theorems/18f80a83-a2d9-4baa-8f76-a6de695c9453
-- title:
--   Source declarations: NonvacuityContract
-- statement:
--   Source-preserving extracted declarations from NonvacuityContract. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionApi_F000
import Definitions.Def_LevyStochCalc_Driver_Existence_F000
import Definitions.Def_LevyStochCalc_Driver_VectorIncrement_F000
import Definitions.Def_LevyStochCalc_Ito_PicardStochasticLipschitz_F000
import Definitions.Def_NonvacuityDrivers_F002
import Definitions.Def_SourceProof_b5912c738affc5f69d2adbcb
import Definitions.Def_SourceProof_c83c751666c401b491a738db
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc.Examples.Nonvacuity
universe u v w
section Gaussian
theorem gaussianReal_Ioi_zero : gaussianReal 0 1 (Set.Ioi (0 : ℝ)) = 1 / 2 := by
  haveI := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) one_ne_zero
  have hneg : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    simpa using gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
  have hIio : gaussianReal 0 1 (Set.Iio (0 : ℝ)) = gaussianReal 0 1 (Set.Ioi (0 : ℝ)) := by
    conv_lhs => rw [← hneg]
    rw [Measure.map_apply measurable_neg measurableSet_Iio]
    congr 1
    ext x
    simp
  have hIic : gaussianReal 0 1 (Set.Iic (0 : ℝ)) = gaussianReal 0 1 (Set.Iio (0 : ℝ)) := by
    rw [← Set.Iio_union_right (a := (0 : ℝ)), measure_union (by simp) (measurableSet_singleton _)]
    simp
  have hsum : gaussianReal 0 1 (Set.Ioi (0 : ℝ)) + gaussianReal 0 1 (Set.Iic (0 : ℝ)) = 1 := by
    rw [← Set.compl_Iic (a := (0 : ℝ)), measure_compl measurableSet_Iic (measure_ne_top _ _),
      measure_univ]
    exact tsub_add_cancel_of_le (prob_le_one (μ := gaussianReal 0 1) (s := Set.Iic (0 : ℝ)))
  rw [hIic, hIio] at hsum
  rw [ENNReal.eq_div_iff (by norm_num) (by norm_num), two_mul]
  exact hsum
end Gaussian
section BrownianIncrement
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
theorem map_increment_unit (W : Brownian.BrownianMotion P) :
    P.map (fun ω => W.W 1 ω - W.W 0 ω) = gaussianReal 0 1 := by
  refine (W.increment_gaussian (s := 0) (t := 1) le_rfl zero_lt_one).trans ?_
  congr 1
  exact Subtype.ext (by norm_num)
theorem variance_increment_unit (W : Brownian.BrownianMotion P) :
    Var[fun x : ℝ => x; P.map (fun ω => W.W 1 ω - W.W 0 ω)] = 1 := by
  rw [map_increment_unit W, variance_fun_id_gaussianReal]
  simp
theorem increment_unit_not_ae_const (W : Brownian.BrownianMotion P) (c : ℝ) :
    ¬ (fun ω => W.W 1 ω - W.W 0 ω) =ᵐ[P] fun _ => c := by
  intro h
  haveI := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) one_ne_zero
  have hmap : P.map (fun ω => W.W 1 ω - W.W 0 ω) = P.map (fun _ : Ω => c) :=
    Measure.map_congr h
  rw [map_increment_unit W, Measure.map_const] at hmap
  have h0 : gaussianReal 0 1 {c} = 0 := measure_singleton c
  rw [hmap] at h0
  simp at h0
theorem prob_increment_unit_pos (W : Brownian.BrownianMotion P) :
    P {ω | 0 < W.W 1 ω - W.W 0 ω} = 1 / 2 := by
  have hmeas : Measurable fun ω => W.W 1 ω - W.W 0 ω :=
    (W.measurable_eval 1).sub (W.measurable_eval 0)
  have hset : {ω | 0 < W.W 1 ω - W.W 0 ω} = (fun ω => W.W 1 ω - W.W 0 ω) ⁻¹' Set.Ioi 0 := rfl
  rw [hset, ← Measure.map_apply hmeas measurableSet_Ioi, map_increment_unit W,
    gaussianReal_Ioi_zero]
theorem measurableSet_increment_unit_pos (W : Brownian.BrownianMotion P) :
    MeasurableSet[MeasurableSpace.comap (fun ω => W.W 1 ω - W.W 0 ω) inferInstance]
      {ω | 0 < W.W 1 ω - W.W 0 ω} :=
  ⟨Set.Ioi 0, measurableSet_Ioi, rfl⟩
theorem comap_increment_unit_ne_bot (W : Brownian.BrownianMotion P) :
    MeasurableSpace.comap (fun ω => W.W 1 ω - W.W 0 ω) inferInstance ≠ ⊥ := by
  intro h
  have hS := measurableSet_increment_unit_pos W
  rw [h] at hS
  have hP := prob_increment_unit_pos W
  rcases MeasurableSpace.measurableSet_bot_iff.mp hS with h0 | h1
  · rw [h0, measure_empty, one_div] at hP
    exact (ENNReal.inv_ne_zero.mpr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)) hP.symm
  · rw [h1, measure_univ, one_div, eq_comm, ENNReal.inv_eq_one] at hP
    norm_num at hP
theorem sigmaBrownian_ne_bot (W : Brownian.BrownianMotion P) :
    Brownian.sigmaBrownian W ≠ ⊥ := by
  intro h
  refine comap_increment_unit_ne_bot W (le_bot_iff.mp ?_)
  rw [← h]
  exact Brownian.comap_increment_le_sigmaBrownian W 0 1
end BrownianIncrement
section DriverIncrement
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
theorem incrementSigma_le_sigmaBrownian (D : Driver.LevyDriver.{u, v, w} P d ν) (j : Fin d) :
    D.incrementSigma j 0 1 ≤ Brownian.sigmaBrownian (D.W.W j) :=
  Brownian.comap_increment_le_sigmaBrownian (D.W.W j) 0 1
theorem prob_driver_increment_unit_pos (D : Driver.LevyDriver.{u, v, w} P d ν) (j : Fin d) :
    P {ω | 0 < (D.W.W j).W 1 ω - (D.W.W j).W 0 ω} = 1 / 2 :=
  prob_increment_unit_pos (D.W.W j)
theorem measurableSet_driver_increment_unit_pos (D : Driver.LevyDriver.{u, v, w} P d ν)
    (j : Fin d) :
    MeasurableSet[D.incrementSigma j 0 1] {ω | 0 < (D.W.W j).W 1 ω - (D.W.W j).W 0 ω} :=
  measurableSet_increment_unit_pos (D.W.W j)
theorem incrementSigma_unit_ne_bot (D : Driver.LevyDriver.{u, v, w} P d ν) (j : Fin d) :
    D.incrementSigma j 0 1 ≠ ⊥ :=
  comap_increment_unit_ne_bot (D.W.W j)
theorem iSup_incrementSigma_unit_ne_bot (D : Driver.LevyDriver.{u, v, w} P d ν) (j : Fin d) :
    (⨆ i : Fin d, D.incrementSigma i 0 1) ≠ ⊥ := by
  intro h
  refine incrementSigma_unit_ne_bot D j (le_bot_iff.mp ?_)
  rw [← h]
  exact le_iSup (fun i : Fin d => D.incrementSigma i 0 1) j
end DriverIncrement
section PoissonRegion
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
theorem prob_count_eq_zero (N : Poisson.PoissonRandomMeasure.{u, v, w} P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : Poisson.referenceIntensity ν B ≠ ⊤) :
    P {ω | N.N ω B = 0}
      = ENNReal.ofReal (Real.exp (-(Poisson.referenceIntensity ν B).toReal)) := by
  have hset : {ω | N.N ω B = 0} = (fun ω => N.N ω B) ⁻¹' {0} := rfl
  rw [hset, ← Measure.map_apply (N.measurable_eval hB) (measurableSet_singleton 0),
    N.poisson_law hB hfin, Poisson.poissonMeasureENN,
    Measure.map_apply measurable_from_nat (measurableSet_singleton _)]
  have hpre : (fun n : ℕ => (n : ℝ≥0∞)) ⁻¹' {(0 : ℝ≥0∞)} = {0} := by
    ext n
    simp
  rw [hpre, poissonMeasure_singleton]
  norm_num [ENNReal.coe_toNNReal_eq_toReal]
theorem measurableSet_regionSigma_count_zero (D : Driver.LevyDriver.{u, v, w} P d ν)
    (C : Set (ℝ × E)) :
    MeasurableSet[D.regionSigma C] {ω | D.N.N ω C = 0} :=
  ⟨{0}, measurableSet_singleton 0, rfl⟩
end PoissonRegion
section Model
noncomputable def markIntensity : Measure ℝ := Measure.dirac 1
instance : IsProbabilityMeasure markIntensity := by
  unfold markIntensity
  infer_instance
theorem markIntensity_univ : markIntensity Set.univ = 1 := measure_univ
def stepRegion : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)
theorem measurableSet_stepRegion : MeasurableSet stepRegion :=
  measurableSet_Ioc.prod MeasurableSet.univ
theorem stepRegion_subset_Ioi : stepRegion ⊆ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ) :=
  Set.prod_mono Set.Ioc_subset_Ioi_self le_rfl
theorem referenceIntensity_stepRegion :
    Poisson.referenceIntensity markIntensity stepRegion = 1 := by
  rw [stepRegion, referenceIntensity_box markIntensity Set.univ 1, markIntensity_univ]
  simp
theorem referenceIntensity_stepRegion_ne_top :
    Poisson.referenceIntensity markIntensity stepRegion ≠ ⊤ := by
  rw [referenceIntensity_stepRegion]
  exact ENNReal.one_ne_top
end Model
section ModelDriver
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
theorem ofReal_exp_neg_one_ne_zero : ENNReal.ofReal (Real.exp (-1)) ≠ 0 := by
  simp [ENNReal.ofReal_eq_zero, not_le, Real.exp_pos]
theorem ofReal_exp_neg_one_ne_one : ENNReal.ofReal (Real.exp (-1)) ≠ 1 := by
  rw [Ne, ENNReal.ofReal_eq_one, Real.exp_eq_one_iff]
  norm_num
theorem prob_count_stepRegion_eq_zero
    (N : Poisson.PoissonRandomMeasure.{u, 0, w} P markIntensity) :
    P {ω | N.N ω stepRegion = 0} = ENNReal.ofReal (Real.exp (-1)) := by
  rw [prob_count_eq_zero N measurableSet_stepRegion referenceIntensity_stepRegion_ne_top,
    referenceIntensity_stepRegion]
  norm_num
theorem regionSigma_stepRegion_ne_bot
    (D : Driver.LevyDriver.{u, 0, w} P d markIntensity) :
    D.regionSigma stepRegion ≠ ⊥ := by
  intro h
  have hS := measurableSet_regionSigma_count_zero D stepRegion
  rw [h] at hS
  have hP := prob_count_stepRegion_eq_zero D.N
  rcases MeasurableSpace.measurableSet_bot_iff.mp hS with h0 | h1
  · rw [h0, measure_empty] at hP
    exact ofReal_exp_neg_one_ne_zero hP.symm
  · rw [h1, measure_univ] at hP
    exact ofReal_exp_neg_one_ne_one hP.symm
theorem iSup_regionSigma_stepRegion_ne_bot
    (D : Driver.LevyDriver.{u, 0, w} P d markIntensity) :
    (⨆ _k : Fin 1, D.regionSigma stepRegion) ≠ ⊥ := by
  intro h
  refine regionSigma_stepRegion_ne_bot D (le_bot_iff.mp ?_)
  rw [← h]
  exact le_iSup (fun _ : Fin 1 => D.regionSigma stepRegion) 0
theorem indep_stepSigma_unit (D : Driver.LevyDriver.{u, 0, w} P d markIntensity) :
    ProbabilityTheory.Indep (D.stepSigma (fun _ : Fin 1 => stepRegion) 0 1) (D.filtration 0) P :=
  (_root_.Prove2MeSourceProof.h_b5912c738affc5f69d2adbcb D) _ (fun _ => measurableSet_stepRegion) le_rfl zero_lt_one
    (fun _ => stepRegion_subset_Ioi)
theorem stepSigma_unit_ne_bot (D : Driver.LevyDriver.{u, 0, w} P d markIntensity) :
    D.stepSigma (fun _ : Fin 1 => stepRegion) 0 1 ≠ ⊥ := by
  intro h
  refine iSup_regionSigma_stepRegion_ne_bot D (le_bot_iff.mp ?_)
  rw [← h]
  exact le_sup_right
end ModelDriver
section Compensated
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
variable (D : Driver.LevyDriver.{u, 0, w} P d markIntensity)
theorem compensated_stepRegion_mean_zero :
    ∫ ω, D.N.compensated stepRegion ω ∂P = 0 :=
  _root_.Prove2MeSourceProof.h_bed7648bbf21e6d2454c31ed D.N measurableSet_stepRegion
    referenceIntensity_stepRegion_ne_top
theorem compensated_stepRegion_second_moment :
    ∫ ω, (D.N.compensated stepRegion ω) ^ 2 ∂P = 1 := by
  rw [_root_.Prove2MeSourceProof.h_b329aafcf3facb3fc4e13667 D.N measurableSet_stepRegion
      referenceIntensity_stepRegion_ne_top, referenceIntensity_stepRegion]
  simp
theorem compensated_stepRegion_sq_integrable :
    Integrable (fun ω => (D.N.compensated stepRegion ω) ^ 2) P :=
  _root_.Prove2MeSourceProof.h_e0e24eaf49ef31dab57f4745 D.N measurableSet_stepRegion
    referenceIntensity_stepRegion_ne_top
theorem compensated_stepRegion_not_ae_const (c : ℝ) :
    ¬ (fun ω => D.N.compensated stepRegion ω) =ᵐ[P] fun _ => c := by
  intro h
  have h1 : (0 : ℝ) = c := by
    rw [← compensated_stepRegion_mean_zero D, integral_congr_ae h, integral_const]
    simp
  have h2 : (1 : ℝ) = c ^ 2 := by
    rw [← compensated_stepRegion_second_moment D]
    have hsq : (fun ω => (D.N.compensated stepRegion ω) ^ 2) =ᵐ[P] fun _ => c ^ 2 := by
      filter_upwards [h] with ω hω
      rw [hω]
    rw [integral_congr_ae hsq, integral_const]
    simp
  rw [← h1] at h2
  norm_num at h2
end Compensated
section ItoConstant
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
theorem lintegral_sq_const (P : Measure Ω) [IsProbabilityMeasure P] (c T : ℝ) :
    ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) T, (‖c‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = (‖c‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal T := by
  simp [Real.volume_Icc]
theorem lintegral_sq_const_lt_top' (P : Measure Ω) [IsProbabilityMeasure P] (c : ℝ) :
    ∀ T : ℝ, 0 < T →
      ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) T, (‖c‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  intro T _
  rw [lintegral_sq_const P c T]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) ENNReal.ofReal_lt_top
variable (W : Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : Brownian.IsBrownianFiltration W ℱ)
noncomputable def itoConst (c : ℝ) : ℝ → Ω → ℝ :=
  Brownian.Ito.stochasticIntegral W ℱ hℱ (fun _ _ => c) measurable_const
    (Probability.progressivelyMeasurable_const ℱ c) (lintegral_sq_const_lt_top' P c)
include hℱ in
theorem exists_itoIntegral_one_unified :
    ∃ (F : ℝ → Ω → ℝ) (Filt : Filtration ℝ ‹MeasurableSpace Ω›),
      Filt = ℱ.rightCont ∧
      Martingale F Filt P ∧
      Martingale (fun t ω => (F t ω) ^ 2 - ∫ _s in Set.Icc (0 : ℝ) t, (1 : ℝ) ^ 2) Filt P ∧
      ∀ T : ℝ, 0 < T → ∫⁻ ω, (‖F T ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ENNReal.ofReal T := by
  obtain ⟨F, Filt, hFilt, hmart, hquad, hiso⟩ :=
    Brownian.Ito.itoIsometry_brownian_unified_existence W ℱ hℱ (fun _ _ => (1 : ℝ))
      measurable_const (Probability.progressivelyMeasurable_const ℱ (1 : ℝ))
      (lintegral_sq_const_lt_top' P 1)
  refine ⟨F, Filt, hFilt, hmart, hquad, fun T hT => ?_⟩
  rw [hiso T hT, lintegral_sq_const P 1 T]
  simp
theorem lintegral_sq_itoConst_sub {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖itoConst W ℱ hℱ 1 T ω - itoConst W ℱ hℱ 2 T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ENNReal.ofReal T := by
  rw [itoConst, itoConst, Brownian.Ito.itoIsometry_diff_brownian W ℱ hℱ
    (fun _ _ => (1 : ℝ)) (fun _ _ => (2 : ℝ)) measurable_const measurable_const
    (Probability.progressivelyMeasurable_const ℱ (1 : ℝ))
    (Probability.progressivelyMeasurable_const ℱ (2 : ℝ))
    (lintegral_sq_const_lt_top' P 1) (lintegral_sq_const_lt_top' P 2) T hT]
  simp [Real.volume_Icc, show (1 : ℝ) - 2 = -1 by norm_num]
end ItoConstant
section ItoLevyIndicator
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
theorem measurable_indicator_const {A : Set E} (hA : MeasurableSet A) (c : ℝ) :
    Measurable fun p : Ω × ℝ × E => A.indicator (fun _ => c) p.2.2 :=
  (measurable_const.indicator hA).comp measurable_snd.snd
theorem markedProgressivelyMeasurable_indicator_const (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {A : Set E} (hA : MeasurableSet A) (c : ℝ) :
    Probability.MarkedProgressivelyMeasurable ℱ
      fun (_ : Ω) (_ : ℝ) (e : E) => A.indicator (fun _ => c) e := by
  have h : Probability.MarkedProgressivelyMeasurable ℱ
      fun (_ : Ω) (_ : ℝ) (e : E) => c * A.indicator (fun _ => (1 : ℝ)) e :=
    (continuous_const_mul c).comp_markedProgressivelyMeasurable (by simp)
      (_root_.Prove2MeSourceProof.h_d5966f17bb5aa768e87c164d ℱ hA)
  have hfun : (fun (_ : Ω) (_ : ℝ) (e : E) => c * A.indicator (fun _ => (1 : ℝ)) e)
      = fun (_ : Ω) (_ : ℝ) (e : E) => A.indicator (fun _ => c) e := by
    funext _ _ e
    by_cases he : e ∈ A <;> simp [he]
  rwa [hfun] at h
omit [SigmaFinite ν] in
theorem lintegral_sq_indicator_const {A : Set E} (hA : MeasurableSet A) (c T : ℝ) :
    ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖A.indicator (fun _ => c) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
      = (‖c‖₊ : ℝ≥0∞) ^ 2 * ν A * ENNReal.ofReal T := by
  have hpt : (fun e : E => (‖A.indicator (fun _ => c) e‖₊ : ℝ≥0∞) ^ 2)
      = A.indicator fun _ => (‖c‖₊ : ℝ≥0∞) ^ 2 := by
    funext e
    by_cases he : e ∈ A <;> simp [he]
  have hinner : ∫⁻ e, (‖A.indicator (fun _ => c) e‖₊ : ℝ≥0∞) ^ 2 ∂ν
      = (‖c‖₊ : ℝ≥0∞) ^ 2 * ν A := by
    rw [hpt, lintegral_indicator hA]
    simp
  simp [hinner, Real.volume_Icc]
omit [SigmaFinite ν] in
theorem lintegral_sq_indicator_const_lt_top {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (c : ℝ) :
    ∀ T : ℝ, 0 < T →
      ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖A.indicator (fun _ => c) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  intro T _
  rw [lintegral_sq_indicator_const (P := P) hA c T]
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hAν.lt_top)
    ENNReal.ofReal_lt_top
variable (N : Poisson.PoissonRandomMeasure.{u, v, w} P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : Poisson.IsPoissonFiltration N ℱ)
noncomputable def itoLevyIndicator {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (c : ℝ) :
    ℝ → Ω → ℝ :=
  Poisson.Compensated.stochasticIntegral N ℱ hℱ (fun _ _ e => A.indicator (fun _ => c) e)
    (measurable_indicator_const hA c) (markedProgressivelyMeasurable_indicator_const ℱ hA c)
    (lintegral_sq_indicator_const_lt_top hA hAν c)
include hℱ in
theorem exists_itoLevyIntegral_indicator_unified {A : Set E} (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) :
    ∃ (F : ℝ → Ω → ℝ) (Filt : Filtration ℝ ‹MeasurableSpace Ω›),
      Filt = ℱ.rightCont ∧
      Martingale F Filt P ∧
      Martingale (fun t ω => (F t ω) ^ 2
        - ∫ _s in Set.Icc (0 : ℝ) t, ∫ e, (A.indicator (fun _ => (1 : ℝ)) e) ^ 2 ∂ν) Filt P ∧
      (∀ T : ℝ, 0 < T →
        ∫⁻ ω, (‖F T ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ν A * ENNReal.ofReal T) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ,
        Filter.Tendsto (fun s => F s ω) (nhdsWithin t (Set.Ioi t)) (nhds (F t ω))
          ∧ ∃ L : ℝ, Filter.Tendsto (fun s => F s ω) (nhdsWithin t (Set.Iio t)) (nhds L)) := by
  obtain ⟨F, Filt, hFilt, hmart, hquad, hiso, hcadlag⟩ :=
    Poisson.Compensated.itoIsometry_compensated_unified_existence N ℱ hℱ
      (fun _ _ e => A.indicator (fun _ => (1 : ℝ)) e) (measurable_indicator_const hA 1)
      (markedProgressivelyMeasurable_indicator_const ℱ hA 1)
      (lintegral_sq_indicator_const_lt_top hA hAν 1)
  refine ⟨F, Filt, hFilt, hmart, hquad, fun T hT => ?_, hcadlag⟩
  rw [hiso T hT, lintegral_sq_indicator_const (P := P) hA 1 T]
  simp
include hℱ in
theorem lintegral_sq_itoLevyIndicator_sub {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖itoLevyIndicator N ℱ hℱ hA hAν 1 T ω
          - itoLevyIndicator N ℱ hℱ hA hAν 2 T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ν A * ENNReal.ofReal T := by
  rw [itoLevyIndicator, itoLevyIndicator, Poisson.Compensated.itoIsometry_diff_compensated N ℱ hℱ
    (fun _ _ e => A.indicator (fun _ => (1 : ℝ)) e) (fun _ _ e => A.indicator (fun _ => (2 : ℝ)) e)
    (measurable_indicator_const hA 1) (measurable_indicator_const hA 2)
    (markedProgressivelyMeasurable_indicator_const ℱ hA 1)
    (markedProgressivelyMeasurable_indicator_const ℱ hA 2)
    (lintegral_sq_indicator_const_lt_top hA hAν 1) (lintegral_sq_indicator_const_lt_top hA hAν 2)
    T hT]
  have hpt : ∀ e : E, A.indicator (fun _ => (1 : ℝ)) e - A.indicator (fun _ => (2 : ℝ)) e
      = A.indicator (fun _ => (-1 : ℝ)) e := by
    intro e
    by_cases he : e ∈ A
    · simp only [Set.indicator_of_mem he]
      norm_num
    · simp [he]
  simp only [hpt]
  rw [lintegral_sq_indicator_const (P := P) hA (-1) T]
  simp
end ItoLevyIndicator
section Existence
theorem markIntensity_univ_ne_top : markIntensity Set.univ ≠ ⊤ := by
  rw [markIntensity_univ]
  exact ENNReal.one_ne_top
theorem markIntensity_univ_pos : 0 < markIntensity Set.univ := by
  rw [markIntensity_univ]
  norm_num
theorem exists_brownianMotion_not_ae_zero :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (W : Brownian.BrownianMotion P),
      ∫⁻ ω, (‖W.W 1 ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 1 ∧
        ¬ (fun ω => W.W 1 ω) =ᵐ[P] fun _ => (0 : ℝ) := by
  obtain ⟨Ω, _, P, _, ⟨W⟩⟩ := _root_.Prove2MeSourceProof.h_c83c751666c401b491a738db.{0}
  refine ⟨Ω, inferInstance, P, inferInstance, W, ?_, brownian_not_ae_zero W zero_lt_one⟩
  rw [_root_.Prove2MeSourceProof.h_bfc6836a0f0c399780ee75a6 W zero_lt_one]
  simp
theorem exists_poissonRandomMeasure_count_not_ae_zero :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (N : Poisson.PoissonRandomMeasure P markIntensity),
      ∫⁻ ω, N.N ω stepRegion ∂P = 1 ∧ ¬ ∀ᵐ ω ∂P, N.N ω stepRegion = 0 := by
  obtain ⟨Ω, _, P, _, ⟨N⟩⟩ := _root_.Prove2MeSourceProof.h_d3bf983a7485d4d78e4c97f0 ℝ markIntensity
  refine ⟨Ω, inferInstance, P, inferInstance, N, ?_,
    count_not_ae_zero N MeasurableSet.univ markIntensity_univ_ne_top markIntensity_univ_pos
      zero_lt_one⟩
  rw [stepRegion, lintegral_count_box N MeasurableSet.univ markIntensity_univ_ne_top 1,
    markIntensity_univ]
  simp
theorem exists_levyDriver_step_nontrivial :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : Driver.LevyDriver P 1 markIntensity),
      ProbabilityTheory.Indep (D.stepSigma (fun _ : Fin 1 => stepRegion) 0 1)
          (D.filtration 0) P ∧
        D.stepSigma (fun _ : Fin 1 => stepRegion) 0 1 ≠ ⊥ ∧
        (⨆ j : Fin 1, D.incrementSigma j 0 1) ≠ ⊥ ∧
        (⨆ _k : Fin 1, D.regionSigma stepRegion) ≠ ⊥ := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := Driver.LevyDriver.exists 1 ℝ markIntensity
  exact ⟨Ω, inferInstance, P, inferInstance, D, indep_stepSigma_unit D, stepSigma_unit_ne_bot D,
    iSup_incrementSigma_unit_ne_bot D 0, iSup_regionSigma_stepRegion_ne_bot D⟩
end Existence
section ModelIntegrals
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable (D : Driver.LevyDriver.{u, 0, w} P 1 markIntensity)
noncomputable def modelIto (c : ℝ) : ℝ → Ω → ℝ :=
  itoConst (D.W.W 0) D.filtration (D.isBrownianFiltration 0) c
noncomputable def modelItoLevy (c : ℝ) : ℝ → Ω → ℝ :=
  itoLevyIndicator D.N D.filtration (_root_.Prove2MeSourceProof.h_98d5b80f0fbd482e08c8d6f3 D) MeasurableSet.univ
    markIntensity_univ_ne_top c
theorem lintegral_sq_modelIto_sub :
    ∫⁻ ω, (‖modelIto D 1 1 ω - modelIto D 2 1 ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 1 := by
  rw [modelIto, modelIto,
    lintegral_sq_itoConst_sub (D.W.W 0) D.filtration (D.isBrownianFiltration 0) zero_lt_one]
  simp
theorem lintegral_sq_modelItoLevy_sub :
    ∫⁻ ω, (‖modelItoLevy D 1 1 ω - modelItoLevy D 2 1 ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 1 := by
  rw [modelItoLevy, modelItoLevy, lintegral_sq_itoLevyIndicator_sub D.N D.filtration
    (_root_.Prove2MeSourceProof.h_98d5b80f0fbd482e08c8d6f3 D) MeasurableSet.univ markIntensity_univ_ne_top zero_lt_one,
    markIntensity_univ]
  simp
end ModelIntegrals
section Capstone
theorem exists_levyDriver_integral_energies :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : Driver.LevyDriver P 1 markIntensity) (F G : ℝ → Ω → ℝ),
      Martingale F D.filtration.rightCont P ∧
      Martingale G D.filtration.rightCont P ∧
      ∫⁻ ω, (‖F 1 ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 1 ∧
      ∫⁻ ω, (‖G 1 ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 1 ∧
      ∫⁻ ω, (‖modelIto D 1 1 ω - modelIto D 2 1 ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 1 ∧
      ∫⁻ ω, (‖modelItoLevy D 1 1 ω - modelItoLevy D 2 1 ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 1 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := Driver.LevyDriver.exists 1 ℝ markIntensity
  obtain ⟨F, FiltF, hFiltF, hmartF, -, hisoF⟩ :=
    exists_itoIntegral_one_unified (D.W.W 0) D.filtration (D.isBrownianFiltration 0)
  obtain ⟨G, FiltG, hFiltG, hmartG, -, hisoG, -⟩ :=
    exists_itoLevyIntegral_indicator_unified D.N D.filtration (_root_.Prove2MeSourceProof.h_98d5b80f0fbd482e08c8d6f3 D)
      MeasurableSet.univ markIntensity_univ_ne_top
  subst hFiltF
  subst hFiltG
  refine ⟨Ω, inferInstance, P, inferInstance, D, F, G, hmartF, hmartG, ?_, ?_,
    lintegral_sq_modelIto_sub D, lintegral_sq_modelItoLevy_sub D⟩
  · rw [hisoF 1 zero_lt_one]
    simp
  · rw [hisoG 1 zero_lt_one, markIntensity_univ]
    simp
end Capstone
end LevyStochCalc.Examples.Nonvacuity


