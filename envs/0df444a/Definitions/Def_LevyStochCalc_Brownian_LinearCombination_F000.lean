-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_LinearCombination_F000
-- name    : LevyStochCalc_Brownian_LinearCombination_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T22:28:30.610469+00:00
-- url     : https://prove2.me/theorems/06319430-a32b-4b4a-bebb-dfe249bb22af
-- title:
--   Source declarations: LevyStochCalc.Brownian.LinearCombination
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.LinearCombination. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_MultidimFiltered_F000
import Definitions.Def_LevyStochCalc_Probability_IndepBlocks_F000
import Definitions.Def_SourceProof_44cfdcf46326c3da0f7081a4

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A unit linear combination of the coordinates of a multidimensional Brownian motion

For a unit vector `u`, the process `∑ i, uⁱ Wⁱ` is again a Brownian motion: its increments are
sums of independent centred Gaussians whose variances add to the length of the time interval, and
the joins of the coordinates' pasts and increments are independent because the coordinates are.
-/

namespace LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- The linear combination `∑ i, cⁱ Wⁱ` of the coordinates of `W`. -/
noncomputable def combine (W : MultidimBrownianMotion P d) (c : Fin d → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ i, c i * (W.W i).W t ω
theorem measurable_combine (W : MultidimBrownianMotion P d) (c : Fin d → ℝ) (t : ℝ) :
    Measurable (combine W c t) :=
  Finset.measurable_sum _ fun i _ => ((W.W i).measurable_eval t).const_mul _
theorem measurable_uncurry_combine (W : MultidimBrownianMotion P d) (c : Fin d → ℝ) :
    Measurable (Function.uncurry (combine W c)) := by
  have hrw : Function.uncurry (combine W c)
      = fun p : ℝ × Ω => ∑ i, c i * (W.W i).W p.1 p.2 := rfl
  rw [hrw]
  exact Finset.measurable_sum _ fun i _ => ((W.W i).joint_measurable).const_mul _
theorem combine_sub (W : MultidimBrownianMotion P d) (c : Fin d → ℝ) (s t : ℝ) (ω : Ω) :
    combine W c t ω - combine W c s ω
      = ∑ i, c i * ((W.W i).W t ω - (W.W i).W s ω) := by
  rw [combine, combine, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring
/-- The increments of the coordinates are independent after scaling. -/
theorem iIndepFun_scaled_increment (W : MultidimBrownianMotion P d) (c : Fin d → ℝ) (s t : ℝ) :
    iIndepFun (fun (i : Fin d) (ω : Ω) => c i * ((W.W i).W t ω - (W.W i).W s ω)) P := by
  have hg : ∀ i : Fin d, Measurable fun f : ℝ → ℝ => c i * (f t - f s) := by
    intro i
    have h1 : Measurable fun f : ℝ → ℝ => f t - f s :=
      (measurable_pi_apply t).sub (measurable_pi_apply s)
    exact h1.const_mul (c i)
  exact W.components_independent.comp _ hg
/-- The increment of a unit linear combination is centred Gaussian with the interval's length as
variance. -/
theorem map_combine_sub (W : MultidimBrownianMotion P d) {c : Fin d → ℝ}
    (hc : ∑ i, c i ^ 2 = 1) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    P.map (fun ω => combine W c t ω - combine W c s ω)
      = gaussianReal 0 (t - s).toNNReal := by
  have hts0 : (0 : ℝ) ≤ t - s := by linarith
  have hmeas : ∀ i : Fin d, Measurable fun ω => c i * ((W.W i).W t ω - (W.W i).W s ω) :=
    fun i => (((W.W i).measurable_eval t).sub ((W.W i).measurable_eval s)).const_mul _
  have hlaw : ∀ i : Fin d,
      P.map (fun ω => c i * ((W.W i).W t ω - (W.W i).W s ω))
        = gaussianReal 0 ((c i ^ 2).toNNReal * (t - s).toNNReal) := by
    intro i
    have hbase : P.map (fun ω => (W.W i).W t ω - (W.W i).W s ω)
        = gaussianReal 0 (t - s).toNNReal := by
      rw [Real.toNNReal_of_nonneg hts0]
      exact (W.W i).increment_gaussian hs hst
    have hΔ : HasLaw (fun ω => (W.W i).W t ω - (W.W i).W s ω)
        (gaussianReal 0 (t - s).toNNReal) P :=
      ⟨(((W.W i).measurable_eval t).sub ((W.W i).measurable_eval s)).aemeasurable, hbase⟩
    have hmul := (gaussianReal_const_mul hΔ (c i)).map_eq
    rw [mul_zero] at hmul
    rw [hmul]
    congr 2
    rw [Real.toNNReal_of_nonneg (sq_nonneg (c i))]
  have hsum := _root_.Prove2MeSourceProof.h_44cfdcf46326c3da0f7081a4 hmeas
    (iIndepFun_scaled_increment W c s t) hlaw Finset.univ
  have hfun : (fun ω => combine W c t ω - combine W c s ω)
      = fun ω => ∑ i, c i * ((W.W i).W t ω - (W.W i).W s ω) := by
    funext ω; exact combine_sub W c s t ω
  have hvar : (∑ i : Fin d, (c i ^ 2).toNNReal * (t - s).toNNReal) = (t - s).toNNReal := by
    rw [← Finset.sum_mul]
    have hone : (∑ i : Fin d, (c i ^ 2).toNNReal) = 1 := by
      refine NNReal.coe_injective ?_
      push_cast
      rw [Finset.sum_congr rfl fun i _ => Real.coe_toNNReal _ (sq_nonneg (c i)), hc]
    rw [hone, one_mul]
  rw [hfun, hsum, hvar]
/-- Every value of the combination before `s` is measurable for the join of the coordinates'
natural filtrations at `s`. -/
theorem comap_combine_le (W : MultidimBrownianMotion P d) (c : Fin d → ℝ) {s j : ℝ} (hj : j ≤ s) :
    MeasurableSpace.comap (combine W c j) inferInstance
      ≤ ⨆ i, Martingale.naturalFiltration (W.W i) s := by
  refine Measurable.comap_le ?_
  refine Finset.measurable_sum _ fun i _ => Measurable.const_mul ?_ _
  refine measurable_iff_comap_le.mpr (le_trans ?_ (le_iSup _ i))
  exact le_iSup₂_of_le j hj le_rfl
/-- The increment of the combination is measurable for the join of the coordinates'
increments. -/
theorem comap_combine_sub_le (W : MultidimBrownianMotion P d) (c : Fin d → ℝ) (s t : ℝ) :
    MeasurableSpace.comap (fun ω => combine W c t ω - combine W c s ω) inferInstance
      ≤ ⨆ i, MeasurableSpace.comap
        (fun ω => (W.W i).W t ω - (W.W i).W s ω) inferInstance := by
  have hfun : (fun ω => combine W c t ω - combine W c s ω)
      = fun ω => ∑ i, c i * ((W.W i).W t ω - (W.W i).W s ω) :=
    funext fun ω => combine_sub W c s t ω
  rw [hfun]
  refine Measurable.comap_le ?_
  refine Finset.measurable_sum _ fun i _ => Measurable.const_mul ?_ _
  exact measurable_iff_comap_le.mpr
    (le_iSup (fun j : Fin d => MeasurableSpace.comap
      (fun ω => (W.W j).W t ω - (W.W j).W s ω) inferInstance) i)
/-- **The joint natural filtration is independent of the combination's increment.** -/
theorem indep_naturalFiltration_combine_sub (W : MultidimBrownianMotion P d) (c : Fin d → ℝ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    Indep (W.naturalFiltration s)
      (MeasurableSpace.comap (fun ω => combine W c t ω - combine W c s ω) inferInstance) P := by
  have hcoord : ∀ i : Fin d, Indep (Martingale.naturalFiltration (W.W i) s)
      (MeasurableSpace.comap (fun ω => (W.W i).W t ω - (W.W i).W s ω) inferInstance) P := by
    intro i
    have h := (W.W i).joint_increment_independent hs hst
    have heq : (⨆ j ∈ Set.Iic s, MeasurableSpace.comap ((W.W i).W j) inferInstance)
        = Martingale.naturalFiltration (W.W i) s := by
      simp only [Set.mem_Iic]
      rfl
    rwa [heq] at h
  have hblocks := LevyStochCalc.Probability.indep_iSup_of_indep_blocks
    (m := fun i => sigmaBrownian (W.W i))
    (a := fun i => Martingale.naturalFiltration (W.W i) s)
    (b := fun i => MeasurableSpace.comap
      (fun ω => (W.W i).W t ω - (W.W i).W s ω) inferInstance)
    (fun i => naturalFiltration_le_sigmaBrownian (W.W i) s)
    (fun i => comap_increment_le_sigmaBrownian (W.W i) s t)
    (fun i => sigmaBrownian_le (W.W i)) (iIndep_sigmaBrownian W) hcoord
  rw [naturalFiltration_apply]
  exact indep_of_indep_of_le_right hblocks (comap_combine_sub_le W c s t)
/-- **The past of the combination is independent of its increment.** -/
theorem indep_combine (W : MultidimBrownianMotion P d) (c : Fin d → ℝ) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s < t) :
    Indep (⨆ j ∈ Set.Iic s, MeasurableSpace.comap (combine W c j) inferInstance)
      (MeasurableSpace.comap (fun ω => combine W c t ω - combine W c s ω) inferInstance) P := by
  refine indep_of_indep_of_le_left (indep_naturalFiltration_combine_sub W c hs hst) ?_
  refine iSup₂_le fun j hj => ?_
  rw [naturalFiltration_apply]
  exact comap_combine_le W c (Set.mem_Iic.mp hj)
/-- **A unit linear combination of the coordinates is a Brownian motion.** -/
noncomputable def combineBM (W : MultidimBrownianMotion P d) {c : Fin d → ℝ}
    (hc : ∑ i, c i ^ 2 = 1) : LevyStochCalc.Brownian.BrownianMotion P where
  W := combine W c
  measurable_eval := measurable_combine W c
  joint_measurable := measurable_uncurry_combine W c
  initial_zero := by
    have h : ∀ᵐ ω ∂P, ∀ i : Fin d, (W.W i).W 0 ω = 0 :=
      ae_all_iff.mpr fun i => (W.W i).initial_zero
    filter_upwards [h] with ω hω
    simp [combine, hω]
  increment_gaussian := fun {s t} hs hst => by
    have h := map_combine_sub W hc hs hst
    rwa [Real.toNNReal_of_nonneg (by linarith : (0 : ℝ) ≤ t - s)] at h
  continuous_paths := by
    filter_upwards [W.joint_continuous_paths] with ω hω
    exact continuous_finsetSum _ fun i _ =>
      continuous_const.mul ((continuous_apply i).comp hω)
  negative_zero := fun s hs => by
    have h : ∀ᵐ ω ∂P, ∀ i : Fin d, (W.W i).W s ω = 0 :=
      ae_all_iff.mpr fun i => (W.W i).negative_zero s hs
    filter_upwards [h] with ω hω
    simp [combine, hω]
  joint_increment_independent := fun {s t} hs hst => indep_combine W c hs hst
/-- **The joint natural filtration is independent of the coordinates' future increments.** For
`0 ≤ s` the σ-algebra `⨆ i, ℱ^{Wⁱ} s` is independent of the σ-algebra generated by all the
increments `Wⁱ t − Wⁱ s`, `t > s`, of all the coordinates. -/
theorem indep_naturalFiltration_iSup_future (W : MultidimBrownianMotion P d) {s : ℝ}
    (hs : 0 ≤ s) :
    Indep (W.naturalFiltration s)
      (⨆ i : Fin d, ⨆ t ∈ Set.Ioi s,
        MeasurableSpace.comap (fun ω => (W.W i).W t ω - (W.W i).W s ω) inferInstance) P := by
  have hblocks := LevyStochCalc.Probability.indep_iSup_of_indep_blocks
    (m := fun i => sigmaBrownian (W.W i))
    (a := fun i => Martingale.naturalFiltration (W.W i) s)
    (b := fun i => ⨆ t ∈ Set.Ioi s,
      MeasurableSpace.comap (fun ω => (W.W i).W t ω - (W.W i).W s ω) inferInstance)
    (fun i => naturalFiltration_le_sigmaBrownian (W.W i) s)
    (fun i => iSup₂_le fun t _ => comap_increment_le_sigmaBrownian (W.W i) s t)
    (fun i => sigmaBrownian_le (W.W i)) (iIndep_sigmaBrownian W)
    (fun i => (_root_.Prove2MeSourceProof.h_1c75026a4865aa7c8b24ff1d (W.W i)) hs)
  rw [naturalFiltration_apply]
  exact hblocks
/-- **The combination is a Brownian motion for the joint natural filtration.** -/
theorem isBrownianFiltration_combineBM (W : MultidimBrownianMotion P d) {c : Fin d → ℝ}
    (hc : ∑ i, c i ^ 2 = 1) :
    IsBrownianFiltration (combineBM W hc) W.naturalFiltration where
  measurable t := by
    refine measurable_iff_comap_le.mpr ?_
    rw [naturalFiltration_apply]
    exact comap_combine_le W c (le_refl t)
  indep_future s hs :=
    indep_of_indep_of_le_right (indep_naturalFiltration_iSup_future W hs)
      (iSup₂_le fun t ht => (comap_combine_sub_le W c s t).trans
        (iSup_le fun i => le_iSup_of_le i (le_iSup₂_of_le t ht le_rfl)))
end LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion


