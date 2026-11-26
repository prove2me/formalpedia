-- Prove2me | Definitions.Def_Operator_Crouzeix_SmoothJordanOuterApproximation
-- name    : Operator_Crouzeix_SmoothJordanOuterApproximation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:52:38.287813+00:00
-- url     : https://prove2.me/theorems/4c992d41-1b11-49ff-b360-12584f99b579
-- title:
--   Smooth Jordan Outer Approximation
-- statement:
--   Definitions and structural lemmas for Smooth Jordan Outer Approximation, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanOuterApproximation.lean

import Definitions.Def_Operator_Crouzeix_SmoothJordanMergelyanAssembly
import Theorems.Thm_convexThickeningApprox_spec

set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
def HasSmoothJordanOuterApproximation (K : Set ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ Omega : SmoothJordanDomain,
    K ⊆ Omega.carrier ∧
      closure Omega.carrier ⊆ Metric.thickening ε K
noncomputable def chooseSmoothJordanOuter
    {K : Set ℂ} (houter : HasSmoothJordanOuterApproximation K)
    (ε : ℝ) (hε : 0 < ε) : SmoothJordanDomain :=
  Classical.choose (houter ε hε)
theorem target_subset_chooseSmoothJordanOuter
    {K : Set ℂ} (houter : HasSmoothJordanOuterApproximation K)
    (ε : ℝ) (hε : 0 < ε) :
    K ⊆ (chooseSmoothJordanOuter houter ε hε).carrier :=
  (Classical.choose_spec (houter ε hε)).1
theorem closure_chooseSmoothJordanOuter_subset_thickening
    {K : Set ℂ} (houter : HasSmoothJordanOuterApproximation K)
    (ε : ℝ) (hε : 0 < ε) :
    closure (chooseSmoothJordanOuter houter ε hε).carrier ⊆
      Metric.thickening ε K :=
  (Classical.choose_spec (houter ε hε)).2
abbrev ContainingSmoothJordanDomain (K : Set ℂ) :=
  { Omega : SmoothJordanDomain // K ⊆ Omega.carrier }
noncomputable def smoothJordanNestingRadius
    {K : Set ℂ} (hK : IsCompact K)
    (Omega : ContainingSmoothJordanDomain K) : ℝ :=
  Classical.choose
    (hK.exists_cthickening_subset_open
      Omega.val.isOpen_carrier Omega.property)
theorem smoothJordanNestingRadius_pos
    {K : Set ℂ} (hK : IsCompact K)
    (Omega : ContainingSmoothJordanDomain K) :
    0 < smoothJordanNestingRadius hK Omega :=
  (Classical.choose_spec
    (hK.exists_cthickening_subset_open
      Omega.val.isOpen_carrier Omega.property)).1
theorem cthickening_smoothJordanNestingRadius_subset
    {K : Set ℂ} (hK : IsCompact K)
    (Omega : ContainingSmoothJordanDomain K) :
    Metric.cthickening (smoothJordanNestingRadius hK Omega) K ⊆
      Omega.val.carrier :=
  (Classical.choose_spec
    (hK.exists_cthickening_subset_open
      Omega.val.isOpen_carrier Omega.property)).2
theorem smoothApproxRadius_pos_outer (n : ℕ) :
    0 < smoothApproxRadius n := by
  unfold smoothApproxRadius
  positivity
noncomputable def smoothJordanOuterStepRadius
    {K : Set ℂ} (hK : IsCompact K) (n : ℕ)
    (Omega : ContainingSmoothJordanDomain K) : ℝ :=
  min (smoothJordanNestingRadius hK Omega) (smoothApproxRadius (n + 1))
theorem smoothJordanOuterStepRadius_pos
    {K : Set ℂ} (hK : IsCompact K) (n : ℕ)
    (Omega : ContainingSmoothJordanDomain K) :
    0 < smoothJordanOuterStepRadius hK n Omega := by
  exact lt_min (smoothJordanNestingRadius_pos hK Omega)
    (smoothApproxRadius_pos_outer (n + 1))
theorem smoothJordanOuterStepRadius_le_nesting
    {K : Set ℂ} (hK : IsCompact K) (n : ℕ)
    (Omega : ContainingSmoothJordanDomain K) :
    smoothJordanOuterStepRadius hK n Omega ≤
      smoothJordanNestingRadius hK Omega :=
  min_le_left _ _
theorem smoothJordanOuterStepRadius_le_schedule
    {K : Set ℂ} (hK : IsCompact K) (n : ℕ)
    (Omega : ContainingSmoothJordanDomain K) :
    smoothJordanOuterStepRadius hK n Omega ≤
      smoothApproxRadius (n + 1) :=
  min_le_right _ _
noncomputable def nextSmoothJordanOuter
    {K : Set ℂ} (hK : IsCompact K)
    (houter : HasSmoothJordanOuterApproximation K) (n : ℕ)
    (Omega : ContainingSmoothJordanDomain K) :
    ContainingSmoothJordanDomain K :=
  ⟨chooseSmoothJordanOuter houter
      (smoothJordanOuterStepRadius hK n Omega)
      (smoothJordanOuterStepRadius_pos hK n Omega),
    target_subset_chooseSmoothJordanOuter houter
      (smoothJordanOuterStepRadius hK n Omega)
      (smoothJordanOuterStepRadius_pos hK n Omega)⟩
theorem closure_nextSmoothJordanOuter_subset_carrier
    {K : Set ℂ} (hK : IsCompact K)
    (houter : HasSmoothJordanOuterApproximation K) (n : ℕ)
    (Omega : ContainingSmoothJordanDomain K) :
    closure (nextSmoothJordanOuter hK houter n Omega).val.carrier ⊆
      Omega.val.carrier := by
  apply (closure_chooseSmoothJordanOuter_subset_thickening houter
    (smoothJordanOuterStepRadius hK n Omega)
    (smoothJordanOuterStepRadius_pos hK n Omega)).trans
  apply (Metric.thickening_subset_cthickening_of_le
    (smoothJordanOuterStepRadius_le_nesting hK n Omega) K).trans
  exact cthickening_smoothJordanNestingRadius_subset hK Omega
theorem closure_nextSmoothJordanOuter_subset_schedule
    {K : Set ℂ} (hK : IsCompact K)
    (houter : HasSmoothJordanOuterApproximation K) (n : ℕ)
    (Omega : ContainingSmoothJordanDomain K) :
    closure (nextSmoothJordanOuter hK houter n Omega).val.carrier ⊆
      convexThickeningApprox K (n + 1) := by
  apply (closure_chooseSmoothJordanOuter_subset_thickening houter
    (smoothJordanOuterStepRadius hK n Omega)
    (smoothJordanOuterStepRadius_pos hK n Omega)).trans
  unfold convexThickeningApprox
  exact Metric.thickening_mono
    (smoothJordanOuterStepRadius_le_schedule hK n Omega) K
noncomputable def firstSmoothJordanOuter
    {K : Set ℂ} (houter : HasSmoothJordanOuterApproximation K) :
    ContainingSmoothJordanDomain K :=
  ⟨chooseSmoothJordanOuter houter (smoothApproxRadius 0)
      (smoothApproxRadius_pos_outer 0),
    target_subset_chooseSmoothJordanOuter houter (smoothApproxRadius 0)
      (smoothApproxRadius_pos_outer 0)⟩
theorem closure_firstSmoothJordanOuter_subset_schedule
    {K : Set ℂ} (houter : HasSmoothJordanOuterApproximation K) :
    closure (firstSmoothJordanOuter houter).val.carrier ⊆
      convexThickeningApprox K 0 := by
  exact closure_chooseSmoothJordanOuter_subset_thickening houter
    (smoothApproxRadius 0) (smoothApproxRadius_pos_outer 0)
noncomputable def nestedSmoothJordanOuterStage
    {K : Set ℂ} (hK : IsCompact K)
    (houter : HasSmoothJordanOuterApproximation K) :
    ℕ → ContainingSmoothJordanDomain K :=
  fun n => Nat.rec (firstSmoothJordanOuter houter)
    (fun n Omega => nextSmoothJordanOuter hK houter n Omega) n
theorem closure_nestedSmoothJordanOuterStage_succ_subset
    {K : Set ℂ} (hK : IsCompact K)
    (houter : HasSmoothJordanOuterApproximation K) (n : ℕ) :
    closure (nestedSmoothJordanOuterStage hK houter (n + 1)).val.carrier ⊆
      (nestedSmoothJordanOuterStage hK houter n).val.carrier := by
  exact closure_nextSmoothJordanOuter_subset_carrier hK houter n
    (nestedSmoothJordanOuterStage hK houter n)
theorem closure_nestedSmoothJordanOuterStage_subset_schedule
    {K : Set ℂ} (hK : IsCompact K)
    (houter : HasSmoothJordanOuterApproximation K) (n : ℕ) :
    closure (nestedSmoothJordanOuterStage hK houter n).val.carrier ⊆
      convexThickeningApprox K n := by
  cases n with
  | zero => exact closure_firstSmoothJordanOuter_subset_schedule houter
  | succ n =>
      exact closure_nextSmoothJordanOuter_subset_schedule hK houter n
        (nestedSmoothJordanOuterStage hK houter n)
noncomputable def StrictNestedSmoothJordanExhaustion.ofOuterApproximation
    (K : Set ℂ) (hK : IsCompact K) (hconvex : Convex ℝ K)
    (houter : HasSmoothJordanOuterApproximation K) :
    StrictNestedSmoothJordanExhaustion K where
  domain n := (nestedSmoothJordanOuterStage hK houter n).val
  target_subset n := (nestedSmoothJordanOuterStage hK houter n).property
  isCompact_closure n := by
    apply (hK.cthickening (r := smoothApproxRadius n)).of_isClosed_subset
      isClosed_closure
    exact (closure_nestedSmoothJordanOuterStage_subset_schedule
      hK houter n).trans
        (Metric.thickening_subset_cthickening (smoothApproxRadius n) K)
  closure_succ_subset n :=
    closure_nestedSmoothJordanOuterStage_succ_subset hK houter n
  iInter_closure := by
    apply Set.Subset.antisymm
    · intro z hz
      have hthick : z ∈ ⋂ n, convexThickeningApprox K n := by
        rw [Set.mem_iInter]
        intro n
        exact closure_nestedSmoothJordanOuterStage_subset_schedule
          hK houter n (Set.mem_iInter.mp hz n)
      rw [(convexThickeningApprox_spec K hK hconvex).2] at hthick
      exact hthick
    · intro z hz
      rw [Set.mem_iInter]
      intro n
      exact subset_closure
        ((nestedSmoothJordanOuterStage hK houter n).property hz)
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


