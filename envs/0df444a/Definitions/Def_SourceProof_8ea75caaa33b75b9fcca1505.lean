-- Prove2me | Definitions.Def_SourceProof_8ea75caaa33b75b9fcca1505
-- name    : SourceProof_8ea75caaa33b75b9fcca1505
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:48:21.185176+00:00
-- url     : https://prove2.me/theorems/f1fb2d3d-270f-40c3-842b-d9e682772678
-- title:
--   LevyStochCalc source module: SourceProof_8ea75caaa33b75b9fcca1505
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.simpleIntegral_diagonal` comes from the `LevyStochCalc.Poisson.CompensatedIsometryOrthogonality` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_b329aafcf3facb3fc4e13667
import Definitions.Def_SourceProof_e0e24eaf49ef31dab57f4745

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


theorem _root_.Prove2MeSourceProof.h_8ea75caaa33b75b9fcca1505
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (i : Fin φ.N)
    (h_part_nn : 0 ≤ φ.partition i.castSucc)
    (h_adapt : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i)) :
    ∫⁻ ω, (‖φ.ξ i ω * N.compensated (φ.timeRect i T) ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i T)
          * ∫⁻ ω, (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  set s := φ.partition i.castSucc with hs_def
  set t := φ.partition i.succ with ht_def
  set A := φ.A i with hA_def
  -- Reduce timeRect to (s, t] × A using partition_le_T.
  have h_t_le_T : t ≤ T := by
    refine le_trans ?_ φ.partition_le_T
    exact φ.partition_strictMono.monotone (Fin.le_last _)
  have h_s_le_T : s ≤ T := by
    refine le_trans ?_ φ.partition_le_T
    exact φ.partition_strictMono.monotone (Fin.le_last _)
  have h_timeRect_eq : φ.timeRect i T = Set.Ioc s t ×ˢ A := by
    unfold LevyStochCalc.Poisson.Compensated.SimplePredictable.timeRect
    rw [min_eq_left h_s_le_T, min_eq_left h_t_le_T]
  rw [h_timeRect_eq]
  set B : Set (ℝ × E) := Set.Ioc s t ×ˢ A with hB_def
  set ÑB : Ω → ℝ := fun ω => N.compensated B ω with hÑB_def
  set ξi : Ω → ℝ := φ.ξ i with hξi_def
  have hst : s < t := φ.partition_strictMono Fin.castSucc_lt_succ
  have h_B_meas : MeasurableSet B :=
    measurableSet_Ioc.prod (φ.A_measurable i)
  have h_ξi_meas : Measurable ξi := φ.ξ_measurable i
  have h_ÑB_meas : Measurable ÑB := by
    change Measurable (fun ω => (N.N ω B).toReal -
      (LevyStochCalc.Poisson.referenceIntensity ν B).toReal)
    refine Measurable.sub ?_ ?_
    · exact ENNReal.measurable_toReal.comp (N.measurable_eval h_B_meas)
    · exact measurable_const
  -- Step 1: Show IndepFun ξi ÑB.
  -- B = Set.Ioc s t ×ˢ A, so B ⊆ (s, t] × E type set.
  have h_indep_struct := hℱ.indep h_part_nn hst
    (φ.A_measurable i) (φ.A_finite i)
  have h_ξi_comap_le : MeasurableSpace.comap ξi inferInstance ≤ ℱ s :=
    h_adapt.measurable.comap_le
  have h_ÑB_comap_le :
      MeasurableSpace.comap ÑB inferInstance ≤
        MeasurableSpace.comap (fun ω => N.N ω (Set.Ioc s t ×ˢ A)) inferInstance := by
    -- ÑB is a measurable function of N(B), so its σ-algebra is contained in σ(N(B)).
    intro u hu
    obtain ⟨v, hv, rfl⟩ := hu
    -- ÑB = N(B).toReal - ν̂(B).toReal, so ÑB⁻¹(v) = N(B)⁻¹((·.toReal - c)⁻¹(v))
    -- for c = ν̂(B).toReal
    refine ⟨(fun x : ℝ≥0∞ =>
        x.toReal - (LevyStochCalc.Poisson.referenceIntensity ν B).toReal) ⁻¹' v,
      ?_, ?_⟩
    · exact (ENNReal.measurable_toReal.sub_const _) hv
    · ext ω; rfl
  have h_indep_ξ_ÑB : ProbabilityTheory.IndepFun ξi ÑB P := by
    rw [ProbabilityTheory.IndepFun_iff]
    intro u v hu hv
    have hu_F : MeasurableSet[ℱ s] u := h_ξi_comap_le u hu
    have hv_F : @MeasurableSet Ω
        (MeasurableSpace.comap (fun ω => N.N ω (Set.Ioc s t ×ˢ A)) inferInstance) v :=
      h_ÑB_comap_le v hv
    rw [ProbabilityTheory.Indep_iff] at h_indep_struct
    exact h_indep_struct u v hu_F hv_F
  -- Step 2: Compose with norm² to get IndepFun on ENNReal.
  have h_nn_meas : Measurable (fun x : ℝ => (‖x‖₊ : ℝ≥0∞)^2) := by fun_prop
  have h_indep_norm_sq :
      ProbabilityTheory.IndepFun
        (fun ω => (‖ξi ω‖₊ : ℝ≥0∞)^2)
        (fun ω => (‖ÑB ω‖₊ : ℝ≥0∞)^2) P := by
    have := h_indep_ξ_ÑB.comp h_nn_meas h_nn_meas
    simpa [Function.comp_def] using this
  -- Step 3: ‖ξ · ÑB‖² = ‖ξ‖² · ‖ÑB‖² pointwise.
  have h_norm_mul : ∀ ω, (‖ξi ω * ÑB ω‖₊ : ℝ≥0∞)^2
      = (‖ξi ω‖₊ : ℝ≥0∞)^2 * (‖ÑB ω‖₊ : ℝ≥0∞)^2 := by
    intro ω
    rw [show (‖ξi ω * ÑB ω‖₊ : ℝ≥0∞)
        = (‖ξi ω‖₊ : ℝ≥0∞) * (‖ÑB ω‖₊ : ℝ≥0∞) from by
      rw [show (‖ξi ω * ÑB ω‖₊ : ℝ≥0∞)
          = ((‖ξi ω * ÑB ω‖₊ : ℝ≥0) : ℝ≥0∞) from rfl]
      rw [show (‖ξi ω * ÑB ω‖₊ : ℝ≥0)
          = ‖ξi ω‖₊ * ‖ÑB ω‖₊ from nnnorm_mul _ _]
      push_cast; rfl]
    ring
  -- Step 4: Apply lintegral_mul.
  rw [show (∫⁻ ω, (‖ξi ω * ÑB ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      = ∫⁻ ω, (‖ξi ω‖₊ : ℝ≥0∞)^2 * (‖ÑB ω‖₊ : ℝ≥0∞)^2 ∂P from
    MeasureTheory.lintegral_congr h_norm_mul]
  rw [show (fun ω => (‖ξi ω‖₊ : ℝ≥0∞)^2 * (‖ÑB ω‖₊ : ℝ≥0∞)^2)
      = (fun ω => (‖ξi ω‖₊ : ℝ≥0∞)^2)
        * (fun ω => (‖ÑB ω‖₊ : ℝ≥0∞)^2) from rfl]
  have h_ξi_norm_sq_meas : Measurable (fun ω => (‖ξi ω‖₊ : ℝ≥0∞)^2) := by fun_prop
  have h_ÑB_norm_sq_meas : Measurable (fun ω => (‖ÑB ω‖₊ : ℝ≥0∞)^2) := by fun_prop
  rw [ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
      h_ξi_norm_sq_meas h_ÑB_norm_sq_meas h_indep_norm_sq]
  -- Step 5: Compute ∫⁻ ‖ÑB‖² ∂P = referenceIntensity ν B.
  have h_finite : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤ := by
    -- referenceIntensity ν B = (volume.restrict (Ici 0)).prod ν (Ioc s t ×ˢ A)
    --                       = volume.restrict (Ici 0) (Ioc s t) * ν A
    -- Both finite: time interval has length ≤ t-s < ⊤; ν A < ⊤ by hypothesis.
    unfold LevyStochCalc.Poisson.referenceIntensity
    rw [MeasureTheory.Measure.prod_prod]
    refine ENNReal.mul_ne_top ?_ (φ.A_finite i)
    -- volume.restrict (Ici 0) (Ioc s t) ≤ volume (Ioc s t) = ENNReal.ofReal (t - s) < ⊤
    refine ne_top_of_le_ne_top ?_ (MeasureTheory.Measure.restrict_le_self _)
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  rw [show (∫⁻ ω, (‖ÑB ω‖₊ : ℝ≥0∞)^2 ∂P)
        = LevyStochCalc.Poisson.referenceIntensity ν B from ?_]
  · ring
  · -- ∫⁻ ‖ÑB‖² = ENNReal.ofReal(∫ ÑB²) = ENNReal.ofReal(ν̂(B).toReal) = ν̂(B).
    have h_ÑB_int : MeasureTheory.Integrable (fun ω => (ÑB ω)^2) P :=
      _root_.Prove2MeSourceProof.h_e0e24eaf49ef31dab57f4745 N h_B_meas h_finite
    have h_nn_sq : 0 ≤ᵐ[P] fun ω => (ÑB ω)^2 := by
      filter_upwards with ω
      positivity
    have h_norm_eq : ∀ ω, (‖ÑB ω‖₊ : ℝ≥0∞)^2 = ENNReal.ofReal ((ÑB ω)^2) := by
      intro ω
      rw [show (‖ÑB ω‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖ÑB ω‖ from
        ofReal_norm (ÑB ω) |>.symm]
      rw [← ENNReal.ofReal_pow (norm_nonneg _)]
      rw [show ‖ÑB ω‖^2 = (ÑB ω)^2 from by rw [Real.norm_eq_abs, sq_abs]]
    rw [show (∫⁻ ω, (‖ÑB ω‖₊ : ℝ≥0∞)^2 ∂P)
            = ∫⁻ ω, ENNReal.ofReal ((ÑB ω)^2) ∂P from
      MeasureTheory.lintegral_congr (fun ω => h_norm_eq ω)]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_ÑB_int h_nn_sq]
    rw [_root_.Prove2MeSourceProof.h_b329aafcf3facb3fc4e13667 N h_B_meas h_finite]
    -- ENNReal.ofReal((ν̂ B).toReal) = ν̂ B (when ν̂ B is finite).
    exact ENNReal.ofReal_toReal h_finite
end LevyStochCalc.Poisson.Compensated


