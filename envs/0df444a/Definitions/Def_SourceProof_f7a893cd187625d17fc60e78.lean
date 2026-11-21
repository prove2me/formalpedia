-- Prove2me | Definitions.Def_SourceProof_f7a893cd187625d17fc60e78
-- name    : SourceProof_f7a893cd187625d17fc60e78
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T07:11:08.29609+00:00
-- url     : https://prove2.me/theorems/54684487-e73d-4c5a-846a-502066cb0c98
-- title:
--   LevyStochCalc source module: SourceProof_f7a893cd187625d17fc60e78
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.simpleIntegral_offDiagonal` comes from the `LevyStochCalc.Brownian.ItoSimpleMoments` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_Filtered_F001
import Definitions.Def_LevyStochCalc_Brownian_Filtered_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIntegrand_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Second moments of the terms of the elementary Brownian integral

For an adapted simple predictable integrand the diagonal term satisfies
`E[(ξ_i · ΔW_i) ^ 2] = (t_{i+1} - t_i) · E[ξ_i ^ 2]`, where
`ΔW_i = W_{t_{i+1}} - W_{t_i}`, since `ΔW_i` is independent of `ℱ_{t_i}` and centred Gaussian
with variance `t_{i+1} - t_i`, while for `i < j` the off-diagonal term vanishes,
`E[(ξ_i · ΔW_i) · (ξ_j · ΔW_j)] = 0`. Both rest on the integrability of the squared increments
and of the cross products.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_f7a893cd187625d17fc60e78
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T) {i j : Fin H.N} (hij : i < j)
    (h_adapt_i : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i))
    (h_adapt_j : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition j.castSucc)) (H.ξ j)) :
    ∫ ω, (H.ξ i ω * (W.W (H.partition i.succ) ω
                    - W.W (H.partition i.castSucc) ω)) *
         (H.ξ j ω * (W.W (H.partition j.succ) ω
                    - W.W (H.partition j.castSucc) ω)) ∂P = 0 := by
  set t_i_pre : ℝ := H.partition i.castSucc with hti0_def
  set t_i : ℝ := H.partition i.succ with hti_def
  set t_j_pre : ℝ := H.partition j.castSucc with htj0_def
  set t_j : ℝ := H.partition j.succ with htj_def
  set ΔW_i : Ω → ℝ := fun ω => W.W t_i ω - W.W t_i_pre ω
  set ΔW_j : Ω → ℝ := fun ω => W.W t_j ω - W.W t_j_pre ω
  set ξ_i : Ω → ℝ := H.ξ i
  set ξ_j : Ω → ℝ := H.ξ j
  -- Partition monotonicity
  have h_part_zero_le_i_pre : 0 ≤ t_i_pre := by
    have : H.partition 0 ≤ H.partition i.castSucc :=
      H.partition_strictMono.monotone (Fin.zero_le _)
    rw [H.partition_zero] at this; exact this
  have h_i_pre_lt : t_i_pre < t_i := H.partition_strictMono Fin.castSucc_lt_succ
  have h_i_le_j_pre : t_i ≤ t_j_pre := by
    apply H.partition_strictMono.monotone
    exact Fin.succ_le_castSucc_iff.mpr hij
  have h_j_pre_lt : t_j_pre < t_j := H.partition_strictMono Fin.castSucc_lt_succ
  have h_j_pre_nn : 0 ≤ t_j_pre := h_part_zero_le_i_pre.trans (le_of_lt h_i_pre_lt)
    |>.trans h_i_le_j_pre
  -- The integrand factors as f · ΔW_j where f := ξ_i · ΔW_i · ξ_j.
  -- f is F_{t_j_pre}-measurable.
  set f : Ω → ℝ := fun ω => ξ_i ω * ΔW_i ω * ξ_j ω
  have h_factored : (fun ω => (ξ_i ω * ΔW_i ω) * (ξ_j ω * ΔW_j ω))
      = fun ω => f ω * ΔW_j ω := by
    funext ω
    change (ξ_i ω * ΔW_i ω) * (ξ_j ω * ΔW_j ω)
      = ξ_i ω * ΔW_i ω * ξ_j ω * ΔW_j ω
    ring
  rw [show (fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                      - W.W (H.partition i.castSucc) ω))
              * (H.ξ j ω * (W.W (H.partition j.succ) ω
                          - W.W (H.partition j.castSucc) ω)))
        = fun ω => f ω * ΔW_j ω from h_factored]
  -- Step 1: f is F_{t_j_pre}-measurable.
  have h_t_i_pre_le_t_j_pre : t_i_pre ≤ t_j_pre :=
    (le_of_lt h_i_pre_lt).trans h_i_le_j_pre
  have h_F_i_pre_le_j_pre :
      ℱ t_i_pre
        ≤ ℱ t_j_pre :=
    ℱ.mono h_t_i_pre_le_t_j_pre
  -- Use the σ-algebra independence: σ(f) ⊆ F_{t_j_pre}; σ(ΔW_j) ⊥ F_{t_j_pre}.
  -- Then E[f * ΔW_j] = E[f] * E[ΔW_j] = E[f] * 0 = 0.
  -- Setup: F-measurability of pieces.
  have h_W_t_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ t_j_pre) (W.W t_i) :=
    (hℱ.measurable t_i).stronglyMeasurable.mono (ℱ.mono h_i_le_j_pre)
  have h_W_t_pre_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ t_j_pre) (W.W t_i_pre) :=
    (hℱ.measurable t_i_pre).stronglyMeasurable.mono
      (ℱ.mono ((le_of_lt h_i_pre_lt).trans h_i_le_j_pre))
  have h_ΔW_i_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ t_j_pre) ΔW_i :=
    h_W_t_meas.sub h_W_t_pre_meas
  have h_ξ_i_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ t_j_pre) ξ_i :=
    h_adapt_i.mono h_F_i_pre_le_j_pre
  have h_f_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ t_j_pre) f :=
    (h_ξ_i_F_meas.mul h_ΔW_i_F_meas).mul h_adapt_j
  -- Step 2: IndepFun f ΔW_j
  have h_indep_F_ΔW_j := hℱ.indep h_j_pre_nn h_j_pre_lt
  have h_f_meas : Measurable f :=
    ((H.ξ_measurable i).mul ((W.measurable_eval t_i).sub
      (W.measurable_eval t_i_pre))).mul (H.ξ_measurable j)
  have h_ΔW_j_meas : Measurable ΔW_j :=
    (W.measurable_eval t_j).sub (W.measurable_eval t_j_pre)
  have h_f_comap_le : MeasurableSpace.comap f inferInstance ≤ ℱ t_j_pre :=
    h_f_F_meas.measurable.comap_le
  have h_indep_f_ΔW_j : ProbabilityTheory.IndepFun f ΔW_j P := by
    rw [ProbabilityTheory.IndepFun_iff]
    intro u v hu hv
    have hu_F : MeasurableSet[ℱ t_j_pre] u := h_f_comap_le u hu
    rw [ProbabilityTheory.Indep_iff] at h_indep_F_ΔW_j
    exact h_indep_F_ΔW_j u v hu_F hv
  -- Step 3: ∫ ΔW_j = 0 (Gaussian mean).
  have h_ΔW_j_mean : ∫ ω, ΔW_j ω ∂P = 0 := by
    rw [show ∫ ω, ΔW_j ω ∂P = ∫ x, x ∂(P.map ΔW_j) from
      (MeasureTheory.integral_map h_ΔW_j_meas.aemeasurable
        (by fun_prop : MeasureTheory.AEStronglyMeasurable (id : ℝ → ℝ) _)).symm]
    rw [W.increment_gaussian h_j_pre_nn h_j_pre_lt]
    exact ProbabilityTheory.integral_id_gaussianReal
  -- Step 4: E[f · ΔW_j] = E[f] · E[ΔW_j] = E[f] · 0 = 0.
  rw [show (fun ω => f ω * ΔW_j ω) = f * ΔW_j from rfl]
  rw [h_indep_f_ΔW_j.integral_mul_eq_mul_integral h_f_meas.aestronglyMeasurable
    h_ΔW_j_meas.aestronglyMeasurable]
  rw [h_ΔW_j_mean, mul_zero]
end LevyStochCalc.Brownian.Ito


