-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_4_F002
-- name    : ProbabilityTheory_chapter_01_thm_1_4_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T15:25:36.883372+00:00
-- url     : https://prove2.me/theorems/f6bd205d-41a2-450c-8c1e-2ae5cb4e4974
-- title:
--   Chapter 1, thm_1_4: supporting Lean bundle F002
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_4`: `sourceHypotheses_of_continuous_derivative_integrator`, `derivative_integrand_continuousOn`, `exists_pos_abs_bound_of_continuousOn`, `tag_mem_Icc`, `exists_cell_deriv_eq_increment_slope`, and 8 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_4.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F005
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_4_F001
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

open Set MeasureTheory
open scoped BigOperators Pointwise Interval

noncomputable section

namespace Thm_1_4

theorem sourceHypotheses_of_continuous_derivative_integrator {f α : ℝ → ℝ}
    {a b : ℝ}
    (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hαmono : MonotoneOn α (Set.Icc a b)) :
    SourceHypotheses a b f α := by
  refine ⟨hab, ?_, ?_, ?_⟩
  · exact (isCompact_Icc.image_of_continuousOn hf).bddAbove
  · exact (isCompact_Icc.image_of_continuousOn hf).bddBelow
  · exact hαmono

theorem derivative_integrand_continuousOn {f α' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b))
    (hα'cont : ContinuousOn α' (Set.Icc a b)) :
    ContinuousOn (fun x => f x * α' x) (Set.Icc a b) :=
  hf.mul hα'cont

theorem exists_pos_abs_bound_of_continuousOn {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, x ∈ Set.Icc a b → |f x| ≤ C := by
  exact exists_pos_abs_bound_on_Icc_of_bddAbove_bddBelow
    (isCompact_Icc.image_of_continuousOn hf).bddAbove
    (isCompact_Icc.image_of_continuousOn hf).bddBelow

lemma tag_mem_Icc {a b : ℝ} (P : Partition a b)
    {tags : Fin P.n → ℝ} (htags : tagsInPartition P tags)
    (i : Fin P.n) :
    tags i ∈ Set.Icc a b :=
  DarbouxRS.tag_mem_Icc_of_tagsInPartition_core P htags i

theorem exists_cell_deriv_eq_increment_slope {α α' : ℝ → ℝ} {a b u v : ℝ}
    (huv : u < v)
    (hsub : Set.Icc u v ⊆ Set.Icc a b)
    (hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x) :
    ∃ c ∈ Set.Ioo u v, α' c = (α v - α u) / (v - u) := by
  refine exists_hasDerivAt_eq_slope α α' huv ?_ ?_
  · intro x hx
    exact (hderiv x (hsub hx)).continuousAt.continuousWithinAt
  · intro x hx
    exact hderiv x (hsub (Set.Ioo_subset_Icc_self hx))

theorem exists_cell_increment_eq_deriv_mul_length {α α' : ℝ → ℝ} {a b u v : ℝ}
    (huv : u < v)
    (hsub : Set.Icc u v ⊆ Set.Icc a b)
    (hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x) :
    ∃ c ∈ Set.Ioo u v, α v - α u = α' c * (v - u) := by
  rcases exists_cell_deriv_eq_increment_slope huv hsub hderiv with
    ⟨c, hc, hcslope⟩
  refine ⟨c, hc, ?_⟩
  rw [hcslope]
  exact (div_mul_cancel₀ (α v - α u) (sub_ne_zero.mpr huv.ne')).symm

theorem cell_mvt_point {α α' : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b) (i : Fin P.n)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x) :
    ∃ c ∈ Set.Ioo (P.pts i.castSucc) (P.pts i.succ),
      α (P.pts i.succ) - α (P.pts i.castSucc) =
        α' c * (P.pts i.succ - P.pts i.castSucc) := by
  exact exists_cell_increment_eq_deriv_mul_length
    (P.strict_mono Fin.castSucc_lt_succ)
    (DarbouxRS.subinterval_subset_Icc_core P (i := i))
    hαderiv

noncomputable def cellMVTTag {α α' : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (i : Fin P.n) : ℝ :=
  Classical.choose (cell_mvt_point P i hαderiv)
theorem cellMVTTag_mem_Ioo {α α' : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (i : Fin P.n) :
    cellMVTTag P hαderiv i ∈
      Set.Ioo (P.pts i.castSucc) (P.pts i.succ) := by
  unfold cellMVTTag
  exact (Classical.choose_spec (cell_mvt_point P i hαderiv)).1
theorem cellMVTTag_increment_eq {α α' : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (i : Fin P.n) :
    α (P.pts i.succ) - α (P.pts i.castSucc) =
      α' (cellMVTTag P hαderiv i) *
        (P.pts i.succ - P.pts i.castSucc) := by
  unfold cellMVTTag
  exact (Classical.choose_spec (cell_mvt_point P i hαderiv)).2
theorem cellMVTTag_mem_subinterval {α α' : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (i : Fin P.n) :
    cellMVTTag P hαderiv i ∈ Partition.subinterval P i := by
  exact Set.Ioo_subset_Icc_self (cellMVTTag_mem_Ioo P hαderiv i)
theorem cellMVTTag_mem_Icc {α α' : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (i : Fin P.n) :
    cellMVTTag P hαderiv i ∈ Set.Icc a b :=
  DarbouxRS.subinterval_subset_Icc_core P
    (cellMVTTag_mem_subinterval P hαderiv i)
theorem tag_mvt_distance_le_mesh {α α' : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b) {tags : Fin P.n → ℝ}
    (htags : tagsInPartition P tags)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (i : Fin P.n) :
    |cellMVTTag P hαderiv i - tags i| ≤ P.mesh := by
  have hcell :
      |cellMVTTag P hαderiv i - tags i| ≤
        P.pts i.succ - P.pts i.castSucc :=
    abs_sub_le_cell_length_of_mem_subinterval P
      (cellMVTTag_mem_subinterval P hαderiv i)
      (htags i)
  exact le_trans hcell (partition_length_le_mesh_core P i)

end Thm_1_4


