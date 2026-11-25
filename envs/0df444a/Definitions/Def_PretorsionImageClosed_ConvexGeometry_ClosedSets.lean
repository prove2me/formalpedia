-- Prove2me | Definitions.Def_PretorsionImageClosed_ConvexGeometry_ClosedSets
-- name    : PretorsionImageClosed_ConvexGeometry_ClosedSets
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T05:46:30.724927+00:00
-- url     : https://prove2.me/theorems/a3573cb5-c8ad-4a9f-9dc3-885ffd7430ee
-- title:
--   Closed Sets
-- statement:
--   Definitions and structural lemmas for Closed Sets, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/ConvexGeometry/ClosedSets.lean

module
public import Mathlib.Order.Grade
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Finite
public import Theorems.Thm_PretorsionImageClosed_SetClosure_exists_closed_sdiff_singleton_between

set_option autoImplicit true
@[expose] public section
@[expose] public section
open Set
namespace PretorsionImageClosed.SetClosure
variable {E : Type*}
noncomputable instance instCompleteLatticeCloseds (c : SetClosure E) :
    CompleteLattice c.Closeds :=
  c.gi.liftCompleteLattice
variable {c : SetClosure E}
def pointClosure (c : SetClosure E) (x : E) : c.Closeds :=
  c.toCloseds ({x} : Set E)
theorem covBy_eq_insert [Finite E]
    (hae : c.IsAntiExchange) {C D : c.Closeds} (hCD : C ⋖ D) :
    ∃ x : E, x ∉ (C : Set E) ∧ (D : Set E) = insert x (C : Set E) := by
  have hlt := hCD.lt
  change (C : Set E) ⊂ (D : Set E) at hlt
  obtain ⟨x, hxDC, hdel, hCdel⟩ :=
    exists_closed_sdiff_singleton_between hae C.2 D.2 hlt
  let D' : c.Closeds := ⟨(D : Set E) \ {x}, hdel⟩
  have hCD' : C ≤ D' := hCdel
  have hD'D : D' ≤ D := sdiff_subset
  have hD'ne : D' ≠ D := by
    intro heq
    have hxD' : x ∈ (D' : Set E) := by
      rw [heq]
      exact hxDC.1
    exact hxD'.2 rfl
  have hD'eq : D' = C :=
    (hCD.eq_or_eq hCD' hD'D).resolve_right hD'ne
  have hdiff : (D : Set E) \ {x} = (C : Set E) :=
    congrArg Subtype.val hD'eq
  refine ⟨x, hxDC.2, ?_⟩
  calc
    (D : Set E) = insert x ((D : Set E) \ {x}) :=
      (insert_sdiff_self_of_mem hxDC.1).symm
    _ = insert x (C : Set E) := congrArg (insert x) hdiff
theorem ncard_add_one_eq_of_covBy [Finite E]
    (hae : c.IsAntiExchange) {C D : c.Closeds} (hCD : C ⋖ D) :
    (C : Set E).ncard + 1 = (D : Set E).ncard := by
  obtain ⟨x, hxC, hD⟩ := covBy_eq_insert hae hCD
  rw [hD]
  exact (ncard_insert_of_notMem hxC).symm
@[reducible] noncomputable def gradeOrder [Finite E]
    (hae : c.IsAntiExchange) : GradeOrder ℕ c.Closeds where
  grade C := (C : Set E).ncard
  grade_strictMono := by
    intro C D hCD
    exact Set.ncard_strictMono hCD
  covBy_grade := by
    intro C D hCD
    rw [Nat.covBy_iff_add_one_eq]
    exact ncard_add_one_eq_of_covBy hae hCD
end PretorsionImageClosed.SetClosure


