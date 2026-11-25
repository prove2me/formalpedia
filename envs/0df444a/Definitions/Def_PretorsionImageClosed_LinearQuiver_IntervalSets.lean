-- Prove2me | Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalSets
-- name    : PretorsionImageClosed_LinearQuiver_IntervalSets
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T03:13:54.488834+00:00
-- url     : https://prove2.me/theorems/b5756890-cc9b-43f1-bbf8-49bb75bce03e
-- title:
--   Interval Sets
-- statement:
--   Definitions and structural lemmas for Interval Sets, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalSets.lean

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Data.Fintype.Powerset
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_end_eq
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_id
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_hom_ext_coord
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_intervalSum
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_not_isZero_interval
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_ext

set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits Statement
namespace LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
theorem coord_add {c d a b : Fin n} (η θ : interval k c d ⟶ interval k a b) (i : Fin n) :
    coord (η + θ) i = coord η i + coord θ i := by
  unfold coord
  rw [NatTrans.app_add]
  rfl
theorem retract_or_retract_of_retract_biprod {a d : Fin n} (had : a ≤ d) {X Y : Statement.LinRep k n}
    (h : Retract (interval k a d) (X ⊞ Y)) :
    Nonempty (Retract (interval k a d) X) ∨ Nonempty (Retract (interval k a d) Y) := by
  -- the two components of the identity of `M_{a,d}`
  have hsum : (h.i ≫ biprod.fst) ≫ (biprod.inl ≫ h.r) + (h.i ≫ biprod.snd) ≫ (biprod.inr ≫ h.r) =
      𝟙 (interval k a d) := by
    have := congrArg (fun φ => h.i ≫ φ ≫ h.r) (biprod.total (X := X) (Y := Y))
    simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, Category.id_comp,
      h.retract] at this
    simpa only [Category.assoc] using this
  have hc := congrArg (fun φ => coord φ a) hsum
  simp only [coord_add, coord_id] at hc
  rw [if_pos ⟨le_rfl, had⟩] at hc
  -- one of the two scalars is nonzero
  rcases eq_or_ne (coord ((h.i ≫ biprod.fst) ≫ (biprod.inl ≫ h.r)) a) 0 with h0 | h0
  · right
    have hne : coord ((h.i ≫ biprod.snd) ≫ (biprod.inr ≫ h.r)) a ≠ 0 := by
      rw [h0, zero_add] at hc
      rw [hc]
      exact one_ne_zero
    refine ⟨⟨h.i ≫ biprod.snd, (biprod.inr ≫ h.r) ≫
      scalarHom a d (coord ((h.i ≫ biprod.snd) ≫ (biprod.inr ≫ h.r)) a)⁻¹, ?_⟩⟩
    rw [← Category.assoc, ← scalarHom_one a d, ← mul_inv_cancel₀ hne, ← scalarHom_comp_scalarHom]
    congr 1
    apply hom_ext_coord
    intro i
    rw [coord_scalarHom, coord_end_eq had _ i]
  · left
    refine ⟨⟨h.i ≫ biprod.fst, (biprod.inl ≫ h.r) ≫
      scalarHom a d (coord ((h.i ≫ biprod.fst) ≫ (biprod.inl ≫ h.r)) a)⁻¹, ?_⟩⟩
    rw [← Category.assoc, ← scalarHom_one a d, ← mul_inv_cancel₀ h0, ← scalarHom_comp_scalarHom]
    congr 1
    apply hom_ext_coord
    intro i
    rw [coord_scalarHom, coord_end_eq had _ i]
def ofIntervals (S : Fin n → Fin n → Prop) : Subcategory (Statement.LinRep k n) where
  prop X := ∀ a d : Fin n, a ≤ d → Retract (interval k a d) X → S a d
  prop_of_retract {X Y} h hY a d had h' := hY a d had (h'.trans h)
  prop_biprod {X Y} hX hY a d had h' := by
    rcases retract_or_retract_of_retract_biprod had h' with hX' | hY'
    · exact hX a d had hX'.some
    · exact hY a d had hY'.some
  prop_of_isZero {X} hX a d had h' := by
    exfalso
    apply not_isZero_interval (k := k) had
    rw [IsZero.iff_id_eq_zero, ← h'.retract, hX.eq_zero_of_tgt h'.i, zero_comp]
theorem prop_of_forall_retract (C : Subcategory (Statement.LinRep k n))
    (X : Statement.LinRep k n)
    (hX : ∀ a d : Fin n, a ≤ d → Retract (interval k a d) X → C.prop (interval k a d)) :
    C.prop X := by
  induction intervalSum X with
  | zero hz => exact C.prop_of_isZero hz
  | @step X X' a d had h' e ih =>
    apply C.prop_of_iso e.symm
    apply C.prop_biprod
    · exact hX a d had ((Retract.ofIso (Iso.refl _)).trans
        ((⟨biprod.inl, biprod.fst, biprod.inl_fst⟩ : Retract (interval k a d) (interval k a d ⊞ X')).trans
          (Retract.ofIso e.symm)))
    · apply ih
      intro a' d' had' h''
      exact hX a' d' had' (h''.trans
        ((⟨biprod.inr, biprod.snd, biprod.inr_snd⟩ : Retract X' (interval k a d ⊞ X')).trans
          (Retract.ofIso e.symm)))
theorem subcategory_eq_ofIntervals (C : Subcategory (Statement.LinRep k n)) :
    C = ofIntervals (fun a d => C.prop (interval k a d)) := by
  apply Subcategory.ext
  funext X
  apply propext
  constructor
  · intro hX a d _ h
    exact C.prop_of_retract h hX
  · intro hX
    exact prop_of_forall_retract C X hX
theorem subcategory_ext_intervals {C D : Subcategory (Statement.LinRep k n)}
    (h : ∀ a d : Fin n, a ≤ d → (C.prop (interval k a d) ↔ D.prop (interval k a d))) : C = D := by
  rw [subcategory_eq_ofIntervals C, subcategory_eq_ofIntervals D]
  apply Subcategory.ext
  funext X
  apply propext
  constructor
  · intro hX a d had hr
    exact (h a d had).1 (hX a d had hr)
  · intro hX a d had hr
    exact (h a d had).2 (hX a d had hr)
def intervalSet (C : Subcategory (Statement.LinRep k n)) : Set (Fin n × Fin n) :=
  {p | p.1 ≤ p.2 ∧ C.prop (interval k p.1 p.2)}
theorem intervalSet_injective :
    Function.Injective (intervalSet : Subcategory (Statement.LinRep k n) → Set (Fin n × Fin n)) := by
  intro C D h
  apply subcategory_ext_intervals
  intro a d had
  have := congrArg (fun S : Set (Fin n × Fin n) => (a, d) ∈ S) h
  simp only [intervalSet, Set.mem_setOf_eq, eq_iff_iff] at this
  exact ⟨fun hC => (this.1 ⟨had, hC⟩).2, fun hD => (this.2 ⟨had, hD⟩).2⟩
instance : Finite (Subcategory (Statement.LinRep k n)) :=
  Finite.of_injective _ intervalSet_injective
end LinearQuiver
end PretorsionImageClosed


