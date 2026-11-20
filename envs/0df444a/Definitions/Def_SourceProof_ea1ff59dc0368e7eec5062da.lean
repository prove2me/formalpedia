-- Prove2me | Definitions.Def_SourceProof_ea1ff59dc0368e7eec5062da
-- name    : SourceProof_ea1ff59dc0368e7eec5062da
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:27:45.573315+00:00
-- url     : https://prove2.me/theorems/66ffbbe4-b051-450a-8099-09eeb4026dda
-- title:
--   LevyStochCalc source module: SourceProof_ea1ff59dc0368e7eec5062da
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.simpleIntegral_offDiagonal` comes from the `LevyStochCalc.Poisson.CompensatedIsometryOrthogonality` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F001
import Definitions.Def_SourceProof_bed7648bbf21e6d2454c31ed

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Orthogonality of compensated-Poisson increments along a simple integrand

For a simple predictable integrand `φ` adapted to a filtration carrying the Poisson random
measure `N`, with boxes `B_i = (t_i, t_{i+1}] × A_i`: the diagonal identity
`∫⁻ ‖ξ_i · Ñ(B_i)‖² ∂P = ν̂(B_i) · ∫⁻ ‖ξ_i‖² ∂P` and the off-diagonal vanishing
`∫ (ξ_i · Ñ(B_i)) · (ξ_j · Ñ(B_j)) ∂P = 0` for `i < j`, both coming from the independence
of the past at `t_i` from the increment over `(t_i, t_{i+1}]`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]


theorem _root_.Prove2MeSourceProof.h_ea1ff59dc0368e7eec5062da
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) {i j : Fin φ.N} (hij : i < j)
    (h_adapt_i : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i))
    (h_adapt_j : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition j.castSucc)) (φ.ξ j)) :
    ∫ ω, (φ.ξ i ω * N.compensated (φ.timeRect i T) ω) *
         (φ.ξ j ω * N.compensated (φ.timeRect j T) ω) ∂P = 0 := by
  set t_i_pre : ℝ := φ.partition i.castSucc with hti0_def
  set t_i : ℝ := φ.partition i.succ with hti_def
  set t_j_pre : ℝ := φ.partition j.castSucc with htj0_def
  set t_j : ℝ := φ.partition j.succ with htj_def
  set A_i := φ.A i with hAi_def
  set A_j := φ.A j with hAj_def
  -- Partition monotonicity
  have h_part_zero_le_i_pre : 0 ≤ t_i_pre := by
    have : φ.partition 0 ≤ φ.partition i.castSucc :=
      φ.partition_strictMono.monotone (Fin.zero_le _)
    rw [φ.partition_zero] at this; exact this
  have h_i_pre_lt : t_i_pre < t_i := φ.partition_strictMono Fin.castSucc_lt_succ
  have h_i_le_j_pre : t_i ≤ t_j_pre :=
    φ.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hij)
  have h_j_pre_lt : t_j_pre < t_j := φ.partition_strictMono Fin.castSucc_lt_succ
  have h_j_pre_nn : 0 ≤ t_j_pre :=
    h_part_zero_le_i_pre.trans ((le_of_lt h_i_pre_lt).trans h_i_le_j_pre)
  have h_t_i_pre_le_t_j_pre : t_i_pre ≤ t_j_pre :=
    (le_of_lt h_i_pre_lt).trans h_i_le_j_pre
  -- Reduce timeRect to (t_i_pre, t_i] × A_i and (t_j_pre, t_j] × A_j.
  have h_t_i_le_T : t_i ≤ T := by
    refine le_trans ?_ φ.partition_le_T
    exact φ.partition_strictMono.monotone (Fin.le_last _)
  have h_t_i_pre_le_T : t_i_pre ≤ T := le_of_lt (h_i_pre_lt.trans_le h_t_i_le_T)
  have h_t_j_le_T : t_j ≤ T := by
    refine le_trans ?_ φ.partition_le_T
    exact φ.partition_strictMono.monotone (Fin.le_last _)
  have h_t_j_pre_le_T : t_j_pre ≤ T := le_of_lt (h_j_pre_lt.trans_le h_t_j_le_T)
  have h_timeRect_i : φ.timeRect i T = Set.Ioc t_i_pre t_i ×ˢ A_i := by
    unfold LevyStochCalc.Poisson.Compensated.SimplePredictable.timeRect
    rw [min_eq_left h_t_i_pre_le_T, min_eq_left h_t_i_le_T]
  have h_timeRect_j : φ.timeRect j T = Set.Ioc t_j_pre t_j ×ˢ A_j := by
    unfold LevyStochCalc.Poisson.Compensated.SimplePredictable.timeRect
    rw [min_eq_left h_t_j_pre_le_T, min_eq_left h_t_j_le_T]
  rw [h_timeRect_i, h_timeRect_j]
  set B_i : Set (ℝ × E) := Set.Ioc t_i_pre t_i ×ˢ A_i with hBi_def
  set B_j : Set (ℝ × E) := Set.Ioc t_j_pre t_j ×ˢ A_j with hBj_def
  set ÑB_i : Ω → ℝ := fun ω => N.compensated B_i ω with hÑBi_def
  set ÑB_j : Ω → ℝ := fun ω => N.compensated B_j ω with hÑBj_def
  set ξi : Ω → ℝ := φ.ξ i with hξi_def
  set ξj : Ω → ℝ := φ.ξ j with hξj_def
  -- Box measurability
  have h_B_i_meas : MeasurableSet B_i := measurableSet_Ioc.prod (φ.A_measurable i)
  have h_B_j_meas : MeasurableSet B_j := measurableSet_Ioc.prod (φ.A_measurable j)
  -- Standard-σ-algebra measurability of the building blocks
  have h_ξi_meas : Measurable ξi := φ.ξ_measurable i
  have h_ξj_meas : Measurable ξj := φ.ξ_measurable j
  have h_ÑB_i_meas : Measurable ÑB_i := by
    change Measurable (fun ω => (N.N ω B_i).toReal -
      (LevyStochCalc.Poisson.referenceIntensity ν B_i).toReal)
    exact (ENNReal.measurable_toReal.comp (N.measurable_eval h_B_i_meas)).sub_const _
  have h_ÑB_j_meas : Measurable ÑB_j := by
    change Measurable (fun ω => (N.N ω B_j).toReal -
      (LevyStochCalc.Poisson.referenceIntensity ν B_j).toReal)
    exact (ENNReal.measurable_toReal.comp (N.measurable_eval h_B_j_meas)).sub_const _
  -- B_i ⊆ Set.Iic t_j_pre × Set.univ (since t_i ≤ t_j_pre)
  have h_B_i_in_past_j : B_i ⊆ Set.Iic t_j_pre ×ˢ Set.univ := by
    intro x hx
    obtain ⟨hx_time, _⟩ := Set.mem_prod.mp hx
    exact Set.mem_prod.mpr ⟨(Set.mem_Ioc.mp hx_time).2.trans h_i_le_j_pre, Set.mem_univ _⟩
  -- past-at-t_i_pre ≤ past-at-t_j_pre (since t_i_pre ≤ t_j_pre)
  have h_pastIp_le_pastJp : (ℱ t_i_pre) ≤ (ℱ t_j_pre) := ℱ.mono h_t_i_pre_le_t_j_pre
  -- ξi is past-at-t_j_pre measurable (lift h_adapt_i via .mono)
  have h_ξi_pastJp : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ t_j_pre) ξi :=
    h_adapt_i.mono h_pastIp_le_pastJp
  -- σ(N(B_i)) ≤ past-at-t_j_pre (since B_i is in the past family)
  have h_NBi_in_pastJp :
      MeasurableSpace.comap (fun ω => N.N ω B_i) inferInstance ≤
      (ℱ t_j_pre) :=
    (hℱ.measurable h_B_i_in_past_j h_B_i_meas).comap_le
  -- N(B_i) is past-at-t_j_pre measurable
  have h_NBi_self : @Measurable Ω ℝ≥0∞
      (MeasurableSpace.comap (fun ω => N.N ω B_i) inferInstance) _
      (fun ω => N.N ω B_i) := fun u hu => ⟨u, hu, rfl⟩
  have h_NBi_pastJp_meas : @Measurable Ω ℝ≥0∞
      (ℱ t_j_pre) _
      (fun ω => N.N ω B_i) :=
    h_NBi_self.mono h_NBi_in_pastJp le_rfl
  -- ÑB_i = (N(B_i)).toReal - c is past-at-t_j_pre measurable
  -- Stated in unfolded form to avoid `show` σ-algebra inference issues.
  have h_ÑB_i_pastJp_meas_unfolded : @Measurable Ω ℝ
      (ℱ t_j_pre) _
      (fun ω => (N.N ω B_i).toReal -
        (LevyStochCalc.Poisson.referenceIntensity ν B_i).toReal) :=
    (ENNReal.measurable_toReal.sub_const _).comp h_NBi_pastJp_meas
  have h_ÑB_i_pastJp : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ t_j_pre) ÑB_i :=
    h_ÑB_i_pastJp_meas_unfolded.stronglyMeasurable
  -- ξj is past-at-t_j_pre measurable directly
  have h_ξj_pastJp : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ t_j_pre) ξj :=
    h_adapt_j
  -- f := ξi · ÑB_i · ξj is past-at-t_j_pre measurable
  set f : Ω → ℝ := fun ω => ξi ω * ÑB_i ω * ξj ω with hf_def
  have h_f_pastJp : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ t_j_pre) f :=
    (h_ξi_pastJp.mul h_ÑB_i_pastJp).mul h_ξj_pastJp
  -- Factor (ξi · ÑB_i)(ξj · ÑB_j) = f · ÑB_j
  have h_factored : (fun ω => (ξi ω * ÑB_i ω) * (ξj ω * ÑB_j ω))
      = fun ω => f ω * ÑB_j ω := by
    funext ω
    change (ξi ω * ÑB_i ω) * (ξj ω * ÑB_j ω) = ξi ω * ÑB_i ω * ξj ω * ÑB_j ω
    ring
  rw [show (fun ω => (φ.ξ i ω * N.compensated (Set.Ioc t_i_pre t_i ×ˢ A_i) ω) *
              (φ.ξ j ω * N.compensated (Set.Ioc t_j_pre t_j ×ˢ A_j) ω))
        = fun ω => f ω * ÑB_j ω from h_factored]
  -- Step: σ(f) ⊥ σ(ÑB_j) under P (joint past/future independence)
  have h_indep_struct := hℱ.indep h_j_pre_nn h_j_pre_lt
    (φ.A_measurable j) (φ.A_finite j)
  have h_f_meas : Measurable f :=
    (h_ξi_meas.mul h_ÑB_i_meas).mul h_ξj_meas
  have h_f_comap_le : MeasurableSpace.comap f inferInstance ≤ ℱ t_j_pre :=
    h_f_pastJp.measurable.comap_le
  have h_ÑB_j_comap_le :
      MeasurableSpace.comap ÑB_j inferInstance ≤
        MeasurableSpace.comap (fun ω => N.N ω (Set.Ioc t_j_pre t_j ×ˢ A_j)) inferInstance := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := hu
    refine ⟨(fun x : ℝ≥0∞ => x.toReal -
      (LevyStochCalc.Poisson.referenceIntensity ν B_j).toReal) ⁻¹' v, ?_, ?_⟩
    · exact (ENNReal.measurable_toReal.sub_const _) hv
    · ext ω; rfl
  have h_indep_f_ÑB_j : ProbabilityTheory.IndepFun f ÑB_j P := by
    rw [ProbabilityTheory.IndepFun_iff]
    intro u v hu hv
    have hu_F : MeasurableSet[ℱ t_j_pre] u := h_f_comap_le u hu
    have hv_F : @MeasurableSet Ω
        (MeasurableSpace.comap (fun ω => N.N ω (Set.Ioc t_j_pre t_j ×ˢ A_j)) inferInstance) v :=
      h_ÑB_j_comap_le v hv
    rw [ProbabilityTheory.Indep_iff] at h_indep_struct
    exact h_indep_struct u v hu_F hv_F
  -- ν̂(B_j) ≠ ⊤ (needed for compensated_mean_zero)
  have h_finite_j : LevyStochCalc.Poisson.referenceIntensity ν B_j ≠ ⊤ := by
    unfold LevyStochCalc.Poisson.referenceIntensity
    rw [MeasureTheory.Measure.prod_prod]
    refine ENNReal.mul_ne_top ?_ (φ.A_finite j)
    refine ne_top_of_le_ne_top ?_ (MeasureTheory.Measure.restrict_le_self _)
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  -- E[ÑB_j] = 0 via compensated_mean_zero
  have h_ÑB_j_mean : ∫ ω, ÑB_j ω ∂P = 0 :=
    _root_.Prove2MeSourceProof.h_bed7648bbf21e6d2454c31ed N h_B_j_meas h_finite_j
  -- E[f · ÑB_j] = E[f] · E[ÑB_j] = E[f] · 0 = 0
  rw [show (fun ω => f ω * ÑB_j ω) = f * ÑB_j from rfl]
  rw [h_indep_f_ÑB_j.integral_mul_eq_mul_integral h_f_meas.aestronglyMeasurable
    h_ÑB_j_meas.aestronglyMeasurable]
  rw [h_ÑB_j_mean, mul_zero]
end LevyStochCalc.Poisson.Compensated


