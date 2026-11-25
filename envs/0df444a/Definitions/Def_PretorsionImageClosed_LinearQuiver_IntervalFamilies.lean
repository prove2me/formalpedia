-- Prove2me | Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
-- name    : PretorsionImageClosed_LinearQuiver_IntervalFamilies
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T04:00:42.121864+00:00
-- url     : https://prove2.me/theorems/d18e6009-9ee3-40d0-8c85-46666da600c8
-- title:
--   Interval Families
-- statement:
--   Definitions and structural lemmas for Interval Families, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalFamilies.lean

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Counting
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_intersectionClosed_of_isImageClosed
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_isImageClosed_of_intersectionClosed
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_ofIntervals_prop_interval
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_ext
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsQuotientClosed_isImageClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsSubobjectClosed_isImageClosed

set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits Statement Polynomial Finset
namespace LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
@[ext]
structure IntervalFamily (n : ℕ) where
  /-- The set of pairs `(a, d)`. -/
  D : Finset (Fin n × Fin n)
  le_of_mem : ∀ p ∈ D, p.1 ≤ p.2
def IntervalFamily.IsClosed (D : IntervalFamily n) : Prop :=
  ∀ a b c d : Fin n, (a, b) ∈ D.D → (c, d) ∈ D.D → max a c ≤ min b d → (max a c, min b d) ∈ D.D
def ClosedFamily (n : ℕ) : Type := {D : IntervalFamily n // D.IsClosed}
open Classical in
/-- The interval family `𝕀(Z)` of a subcategory. -/
def familyOf (Z : Subcategory (Statement.LinRep k n)) : IntervalFamily n where
  D := univ.filter (fun p : Fin n × Fin n => p.1 ≤ p.2 ∧ Z.prop (interval k p.1 p.2))
  le_of_mem p hp := (Finset.mem_filter.1 hp).2.1
theorem mem_familyOf {Z : Subcategory (Statement.LinRep k n)} {p : Fin n × Fin n} :
    p ∈ (familyOf Z).D ↔ p.1 ≤ p.2 ∧ Z.prop (interval k p.1 p.2) := by
  simp [familyOf]
def IntervalFamily.subcategory (D : IntervalFamily n) : Subcategory (Statement.LinRep k n) :=
  ofIntervals (fun a d => (a, d) ∈ D.D)
theorem IntervalFamily.prop_interval_iff (D : IntervalFamily n) {a d : Fin n} (had : a ≤ d) :
    (D.subcategory (k := k)).prop (interval k a d) ↔ (a, d) ∈ D.D :=
  ofIntervals_prop_interval _ had
theorem familyOf_isClosed {Z : Subcategory (Statement.LinRep k n)} (hZ : Z.IsImageClosed) :
    (familyOf (k := k) Z).IsClosed := by
  intro a b c d hab hcd hmin
  rw [mem_familyOf] at hab hcd ⊢
  exact ⟨hmin, intersectionClosed_of_isImageClosed Z hZ a b c d hab.1 hcd.1 hab.2 hcd.2 hmin⟩
theorem IntervalFamily.IsClosed.isImageClosed {D : IntervalFamily n} (hD : D.IsClosed) :
    (D.subcategory (k := k)).IsImageClosed := by
  apply isImageClosed_of_intersectionClosed
  intro a b c d hab hcd ha hc hmin
  rw [D.prop_interval_iff hab] at ha
  rw [D.prop_interval_iff hcd] at hc
  rw [D.prop_interval_iff hmin]
  exact hD a b c d ha hc hmin
theorem familyOf_subcategory (D : IntervalFamily n) : familyOf (D.subcategory (k := k)) = D := by
  ext p
  rw [mem_familyOf]
  constructor
  · rintro ⟨h1, h2⟩
    exact (D.prop_interval_iff h1).1 h2
  · intro h
    exact ⟨D.le_of_mem p h, (D.prop_interval_iff (D.le_of_mem p h)).2 h⟩
theorem subcategory_familyOf (Z : Subcategory (Statement.LinRep k n)) :
    (familyOf Z).subcategory = Z := by
  apply subcategory_ext_intervals
  intro a d had
  rw [IntervalFamily.prop_interval_iff _ had, mem_familyOf]
  exact ⟨fun h => h.2, fun h => ⟨had, h⟩⟩
def imageClosedEquiv : ImageClosedSubcategory k n ≃ ClosedFamily n where
  toFun Z := ⟨familyOf Z.1, familyOf_isClosed Z.2⟩
  invFun D := ⟨D.1.subcategory, D.2.isImageClosed⟩
  left_inv Z := Subtype.ext (subcategory_familyOf Z.1)
  right_inv D := Subtype.ext (familyOf_subcategory D.1)
def IntervalFamily.lastCount (D : IntervalFamily n) : ℕ :=
  (D.D.filter (fun p => p.2.val + 1 = n)).card
def fWeight (D : ClosedFamily n) : Rq[X] := X ^ D.1.lastCount * C (q ^ D.1.D.card)
instance : Finite (IntervalFamily n) :=
  Finite.of_injective IntervalFamily.D (fun _ _ h => IntervalFamily.ext h)
instance : Finite (ClosedFamily n) := Subtype.finite
instance : Fintype (ClosedFamily n) := Fintype.ofFinite _
instance : Finite (ImageClosedSubcategory k n) := Finite.of_equiv _ (imageClosedEquiv (k := k) (n := n)).symm
instance : Fintype (ImageClosedSubcategory k n) := Fintype.ofFinite _
end LinearQuiver
end PretorsionImageClosed


