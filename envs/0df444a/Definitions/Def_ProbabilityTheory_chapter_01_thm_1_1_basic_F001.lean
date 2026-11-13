-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_basic_F001
-- name    : ProbabilityTheory_chapter_01_thm_1_1_basic_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T22:19:05.276293+00:00
-- url     : https://prove2.me/theorems/3337e6ea-d7ab-463c-984f-08e484e008a1
-- title:
--   Chapter 1, thm_1_1_basic: supporting Lean bundle F001
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_1_basic`: `no_source_route_for_current_le_interval_claim`, `sourceHypotheses_of_strict_task_hypotheses`, `discontinuitySetOn_empty_of_forall_continuousWithinAt`, `finite_discontinuitySetOn_of_forall_continuousWithinAt`, `common_limits_iff_rsIntegrable`, and 10 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_basic.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_basic_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F006
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F007
import Mathlib.Tactic

open Finset BigOperators
open Set Topology

noncomputable section

namespace DarbouxRS
/--
The integrator function `alpha` does not decrease across any subinterval of the partition.

Because `alpha` is assumed to be monotonic on `[a, b]` (via `SourceHypotheses`), and the
partition points strictly increase (`x_i < x_{i+1}`), the difference `alpha(x_{i+1}) - alpha(x_i)`
is always non-negative. This guarantees that the width/weights in the Riemann-Stieltjes sum
are non-negative.
-/
private lemma partition_increment_nonneg_of_source_core_local {a b : ℝ} (P : Partition a b)
    {f alpha : ℝ → ℝ} (hs : SourceHypotheses a b f alpha) {i : Fin P.n} :
    0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) := by
  -- Unpack the SourceHypotheses to get the monotonicity of alpha
  rcases hs with ⟨_hab, _hAbove, _hBelow, hmono⟩

  -- The endpoints of the subinterval are in [a, b]
  have hleft : P.pts i.castSucc ∈ Set.Icc a b := partition_pts_mem_Icc_core P
  have hright : P.pts i.succ ∈ Set.Icc a b := partition_pts_mem_Icc_core P

  -- Because x_i < x_{i+1}, monotonicity implies alpha(x_i) ≤ alpha(x_{i+1})
  have h_pts_lt : P.pts i.castSucc < P.pts i.succ :=
    P.strict_mono (Fin.castSucc_lt_succ)

  exact sub_nonneg.mpr (hmono hleft hright (le_of_lt h_pts_lt))

/--
For a fixed partition, every lower Riemann--Stieltjes sum is bounded above by
every tagged Riemann--Stieltjes sum whose tags are chosen in the corresponding
subintervals.

This is the finite-sum comparison

`L(P,f,α) ≤ S(P,tags,f,α)`.

The proof is pointwise on each subinterval:

* `lowerStep P f i ≤ f (tags i)`;
* `α(xᵢ₊₁) - α(xᵢ) ≥ 0`;
* hence the corresponding products are ordered;
* summing preserves the inequality.
-/
private lemma lowerSum_le_taggedSum_local {a b : ℝ} {f alpha : ℝ → ℝ}
    (hs : SourceHypotheses a b f alpha)
    (P : Partition a b)
    (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) :
    lowerSum P f alpha ≤ taggedSum P tags f alpha := by
  rcases hs with ⟨hab, hfAbove, hfBelow, hmono⟩

  unfold lowerSum taggedSum

  refine Finset.sum_le_sum ?_
  intro i _hi

  have hstep :
      lowerStep P f i ≤ f (tags i) :=
    lowerStep_le_tag P i hfBelow (htags i)

  have hinc :
      0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) :=
    partition_increment_nonneg_of_source_core_local P
      ⟨hab, hfAbove, hfBelow, hmono⟩

  exact mul_le_mul_of_nonneg_right hstep hinc

/--
For a fixed partition, every tagged Riemann--Stieltjes sum is bounded above by
the corresponding upper Riemann--Stieltjes sum, provided the tags are chosen in
the corresponding subintervals.

This is the finite-sum comparison

`S(P,tags,f,α) ≤ U(P,f,α)`.

The proof is pointwise on each subinterval:

* `f (tags i) ≤ upperStep P f i`;
* `α(xᵢ₊₁) - α(xᵢ) ≥ 0`;
* hence the corresponding products are ordered;
* summing preserves the inequality.
-/
private lemma taggedSum_le_upperSum_local {a b : ℝ} {f alpha : ℝ → ℝ}
    (hs : SourceHypotheses a b f alpha)
    (P : Partition a b)
    (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) :
    taggedSum P tags f alpha ≤ upperSum P f alpha := by
  rcases hs with ⟨hab, hfAbove, hfBelow, hmono⟩

  unfold taggedSum upperSum

  refine Finset.sum_le_sum ?_
  intro i _hi

  have hstep :
      f (tags i) ≤ upperStep P f i :=
    tag_le_upperStep P i hfAbove (htags i)

  have hinc :
      0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) :=
    partition_increment_nonneg_of_source_core_local P
      ⟨hab, hfAbove, hfBelow, hmono⟩

  exact mul_le_mul_of_nonneg_right hstep hinc
end DarbouxRS

namespace Thm11SourceRoute
/--
A lower Riemann--Stieltjes sum is bounded above by any tagged sum over the same
partition, provided the tags are chosen in the corresponding subintervals.
-/
private theorem lowerSum_le_taggedSum_local {a b : ℝ} {f alpha : ℝ → ℝ}
    (hs : SourceHypotheses a b f alpha)
    (P : Partition a b)
    (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) :
    lowerSum P f alpha ≤ taggedSum P tags f alpha :=
  DarbouxRS.lowerSum_le_taggedSum_local hs P tags htags

/--
A tagged Riemann--Stieltjes sum is bounded above by the upper sum over the same
partition, provided the tags are chosen in the corresponding subintervals.
-/
private theorem taggedSum_le_upperSum_local {a b : ℝ} {f alpha : ℝ → ℝ}
    (hs : SourceHypotheses a b f alpha)
    (P : Partition a b)
    (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) :
    taggedSum P tags f alpha ≤ upperSum P f alpha :=
  DarbouxRS.taggedSum_le_upperSum_local hs P tags htags

/--
If the upper and lower Riemann--Stieltjes sums have the same fine-partition
limit `L`, then every tagged Riemann--Stieltjes sum also converges to `L`.

The proof is a squeeze argument:

`lowerSum P f α ≤ taggedSum P tags f α ≤ upperSum P f α`.

Since both lower and upper sums are within `eps` of `L` for sufficiently small
mesh, the tagged sum is also within `eps` of `L`.
-/
private theorem rsTaggedCommonLimit_of_rsUpperLowerCommonLimit_local
    {a b : ℝ} {f alpha : ℝ → ℝ} {L : ℝ}
    (h : rsUpperLowerCommonLimit a b f alpha L) :
    rsTaggedCommonLimit a b f alpha L := by
  -- Unfold the exported aliases.
  unfold rsUpperLowerCommonLimit at h
  unfold rsTaggedCommonLimit

  rcases h with ⟨hs, hlim⟩

  refine ⟨hs, ?_⟩

  intro eps heps

  rcases hlim eps heps with ⟨δ, hδ, Hδ⟩

  refine ⟨δ, hδ, ?_⟩

  intro P tags htags hmesh

  have hP :
      |upperSum P f alpha - L| < eps ∧
      |lowerSum P f alpha - L| < eps :=
    Hδ P hmesh

  have h_lower :
      lowerSum P f alpha ≤ taggedSum P tags f alpha :=
    DarbouxRS.lowerSum_le_taggedSum_local hs P tags htags

  have h_upper :
      taggedSum P tags f alpha ≤ upperSum P f alpha :=
    DarbouxRS.taggedSum_le_upperSum_local hs P tags htags

  have h_upper_abs :
      |upperSum P f alpha - L| < eps :=
    hP.1

  have h_lower_abs :
      |lowerSum P f alpha - L| < eps :=
    hP.2

  apply abs_lt.mpr
  constructor
  · -- lower side: `-eps < taggedSum P tags f alpha - L`
    have h_lower_left :
        -eps < lowerSum P f alpha - L :=
      (abs_lt.mp h_lower_abs).1
    linarith

  · -- upper side: `taggedSum P tags f alpha - L < eps`
    have h_upper_right :
        upperSum P f alpha - L < eps :=
      (abs_lt.mp h_upper_abs).2
    linarith


/-- Constant functions have no discontinuities on a degenerate interval. This
keeps the counterexample to the current non-strict theorem shape explicit. -/
private lemma discontinuitySetOn_const_refl_empty_local (c a : ℝ) :
    discontinuitySetOn (fun _ : ℝ => c) a a = ∅ := by
  ext x
  constructor
  · intro hx
    exact hx.2 (by
      simpa using
        (continuousAt_const.continuousWithinAt :
          ContinuousWithinAt (fun _ : ℝ => c) (Icc a a) x))
  · intro hx
    cases hx

/-- Any proof of the current universal `a ≤ b` theorem shape would apply to
the constant zero integrand and integrator on `[0,0]`, producing a degenerate
`RSIntegrable` witness. -/
private theorem current_le_interval_claim_creates_degenerate_witness_local
    (hclaim :
      ∀ {f α : ℝ → ℝ} {a b : ℝ},
        a ≤ b →
        Monotone α →
        BddAbove (f '' Icc a b) →
        BddBelow (f '' Icc a b) →
        (discontinuitySetOn f a b).Finite →
        (∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x) →
        RSIntegrable f α a b) :
    RSIntegrable (fun _ : ℝ => 0) (fun _ : ℝ => 0) 0 0 := by
  refine hclaim (f := fun _ : ℝ => 0) (α := fun _ : ℝ => 0)
    (a := 0) (b := 0) le_rfl ?_ ?_ ?_ ?_ ?_
  · intro x y hxy
    simp
  · refine ⟨0, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    simp
  · refine ⟨0, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    simp
  · rw [discontinuitySetOn_const_refl_empty_local]
    exact Set.finite_empty
  · intro x hx
    simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) x)


theorem no_source_route_for_current_le_interval_claim :
    ¬ (∀ {f α : ℝ → ℝ} {a b : ℝ},
      a ≤ b →
      Monotone α →
      BddAbove (f '' Icc a b) →
      BddBelow (f '' Icc a b) →
      (discontinuitySetOn f a b).Finite →
      (∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x) →
      RSIntegrable f α a b) := by
  intro hclaim
  exact not_rsIntegrable_refl (fun _ : ℝ => 0) (fun _ : ℝ => 0) 0
    (current_le_interval_claim_creates_degenerate_witness_local hclaim)

lemma sourceHypotheses_of_strict_task_hypotheses {f α : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hα_mono : Monotone α)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b)) :
    SourceHypotheses a b f α := by
  refine ⟨hab, hAbove, hBelow, ?_⟩
  intro x _hx y _hy hxy
  exact hα_mono hxy

lemma discontinuitySetOn_empty_of_forall_continuousWithinAt
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x, x ∈ Icc a b → ContinuousWithinAt f (Icc a b) x) :
    discontinuitySetOn f a b = ∅ := by
  ext x
  constructor
  · intro hx
    exact False.elim (hx.2 (hf x hx.1))
  · intro hx
    cases hx

lemma finite_discontinuitySetOn_of_forall_continuousWithinAt
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x, x ∈ Icc a b → ContinuousWithinAt f (Icc a b) x) :
    (discontinuitySetOn f a b).Finite := by
  rw [discontinuitySetOn_empty_of_forall_continuousWithinAt hf]
  exact Set.finite_empty

theorem common_limits_iff_rsIntegrable {f α : ℝ → ℝ} {a b : ℝ} :
    (∃ L, rsUpperLowerCommonLimit a b f α L ∧ rsTaggedCommonLimit a b f α L) ↔
      RSIntegrable f α a b := by
  constructor
  · rintro ⟨L, hSource, hTagged⟩
    exact ⟨{
      value := L
      source_limit := hSource
      tagged_limit := hTagged
    }⟩
  · intro h
    rcases h with ⟨w⟩
    exact ⟨w.value, w.source_limit, w.tagged_limit⟩
private lemma upperSum_eq_of_integrator_eqOn_Icc
    {f α β : ℝ → ℝ} {a b : ℝ}
    (hEq : Set.EqOn β α (Icc a b)) (P : Partition a b) :
    upperSum P f β = upperSum P f α := by
  unfold upperSum
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [hEq (DarbouxRS.partition_pts_mem_Icc_core P (i := i.succ)),
    hEq (DarbouxRS.partition_pts_mem_Icc_core P (i := i.castSucc))]
private lemma lowerSum_eq_of_integrator_eqOn_Icc
    {f α β : ℝ → ℝ} {a b : ℝ}
    (hEq : Set.EqOn β α (Icc a b)) (P : Partition a b) :
    lowerSum P f β = lowerSum P f α := by
  unfold lowerSum
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [hEq (DarbouxRS.partition_pts_mem_Icc_core P (i := i.succ)),
    hEq (DarbouxRS.partition_pts_mem_Icc_core P (i := i.castSucc))]
private lemma taggedSum_eq_of_integrator_eqOn_Icc
    {f α β : ℝ → ℝ} {a b : ℝ}
    (hEq : Set.EqOn β α (Icc a b)) (P : Partition a b)
    (tags : Fin P.n → ℝ) :
    taggedSum P tags f β = taggedSum P tags f α := by
  unfold taggedSum
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [hEq (DarbouxRS.partition_pts_mem_Icc_core P (i := i.succ)),
    hEq (DarbouxRS.partition_pts_mem_Icc_core P (i := i.castSucc))]
private lemma sourceHypotheses_of_integrator_eqOn_Icc
    {f α β : ℝ → ℝ} {a b : ℝ}
    (hEq : Set.EqOn β α (Icc a b))
    (hs : SourceHypotheses a b f β) :
    SourceHypotheses a b f α := by
  rcases hs with ⟨hab, hAbove, hBelow, hβmono⟩
  refine ⟨hab, hAbove, hBelow, ?_⟩
  intro x hx y hy hxy
  rw [← hEq hx, ← hEq hy]
  exact hβmono hx hy hxy
private lemma upperLowerCommonLimit_of_integrator_eqOn_Icc
    {f α β : ℝ → ℝ} {a b L : ℝ}
    (hEq : Set.EqOn β α (Icc a b))
    (hβ : rsUpperLowerCommonLimit a b f β L) :
    rsUpperLowerCommonLimit a b f α L := by
  rcases hβ with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_of_integrator_eqOn_Icc hEq hs, ?_⟩
  intro eps heps
  rcases hlim eps heps with ⟨delta, hdelta, Hdelta⟩
  refine ⟨delta, hdelta, ?_⟩
  intro P hmesh
  have hP := Hdelta P hmesh
  rw [← upperSum_eq_of_integrator_eqOn_Icc hEq P,
    ← lowerSum_eq_of_integrator_eqOn_Icc hEq P]
  exact hP
private lemma taggedCommonLimit_of_integrator_eqOn_Icc
    {f α β : ℝ → ℝ} {a b L : ℝ}
    (hEq : Set.EqOn β α (Icc a b))
    (hβ : rsTaggedCommonLimit a b f β L) :
    rsTaggedCommonLimit a b f α L := by
  rcases hβ with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_of_integrator_eqOn_Icc hEq hs, ?_⟩
  intro eps heps
  rcases hlim eps heps with ⟨delta, hdelta, Hdelta⟩
  refine ⟨delta, hdelta, ?_⟩
  intro P tags htags hmesh
  have hP := Hdelta P tags htags hmesh
  rw [← taggedSum_eq_of_integrator_eqOn_Icc hEq P tags]
  exact hP

theorem _root_.RSIntegrable.congr_integrator_on_Icc
    {f α β : ℝ → ℝ} {a b : ℝ}
    (hEq : Set.EqOn β α (Icc a b)) :
    RSIntegrable f β a b → RSIntegrable f α a b := by
  rintro ⟨w⟩
  refine ⟨{
    value := w.value
    source_limit := upperLowerCommonLimit_of_integrator_eqOn_Icc hEq w.source_limit
    tagged_limit := taggedCommonLimit_of_integrator_eqOn_Icc hEq w.tagged_limit
  }⟩

lemma taggedSum_between_lower_upper {f α : ℝ → ℝ} {a b : ℝ}
    (hs : SourceHypotheses a b f α)
    (P : Partition a b) (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) :
    lowerSum P f α ≤ taggedSum P tags f α ∧
      taggedSum P tags f α ≤ upperSum P f α :=
  ⟨lowerSum_le_taggedSum_local hs P tags htags,
    taggedSum_le_upperSum_local hs P tags htags⟩

theorem taggedCommonLimit_of_upperLowerCommonLimit {f α : ℝ → ℝ} {a b L : ℝ}
    (hUL : rsUpperLowerCommonLimit a b f α L) :
    rsTaggedCommonLimit a b f α L :=
  rsTaggedCommonLimit_of_rsUpperLowerCommonLimit_local hUL

def StrictFiniteDiscontinuityUpperLowerCriterion : Prop :=
  ∀ {f α : ℝ → ℝ} {a b : ℝ},
    a < b →
    Monotone α →
    BddAbove (f '' Icc a b) →
    BddBelow (f '' Icc a b) →
    (discontinuitySetOn f a b).Finite →
    (∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x) →
    ∃ L, rsUpperLowerCommonLimit a b f α L
end Thm11SourceRoute


