-- Prove2me | Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
-- name    : PretorsionImageClosed_Pretorsion_Lattice
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T06:32:45.75956+00:00
-- url     : https://prove2.me/theorems/52f8a756-bcc9-5b63-85c2-a1010e7f6ab1
-- title:
--   Lattice
-- statement:
--   Definitions and structural lemmas for Lattice, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Pretorsion/Lattice.lean

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Duality
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isQuotientClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_ext
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsImageClosed_iInf
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_isQuotientClosed_bot
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_isSubobjectClosed_bot
public import Theorems.Thm_PretorsionImageClosed_Statement_isPretorsionTheory_iInf
public import Theorems.Thm_PretorsionImageClosed_Statement_isPretorsionTheory_iInf_left
public import Theorems.Thm_PretorsionImageClosed_Statement_isPretorsionTheory_top_left
public import Theorems.Thm_PretorsionImageClosed_Statement_isPretorsionTheory_top_right

set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C]
instance : PartialOrder (PretorsionTheory C) where
  le := PretorsionTheory.LE
  le_refl _ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ h h' := ⟨h.1.trans h'.1, h'.2.trans h.2⟩
  le_antisymm _ _ h h' := PretorsionTheory.ext (Subcategory.ext (le_antisymm h.1 h'.1))
    (Subcategory.ext (le_antisymm h'.2 h.2))
variable [HasLength C]
namespace PretorsionTheory
def meetT (S : Set (PretorsionTheory C)) : Subcategory C := Subcategory.iInf (fun P : S => P.1.T)
def MeetPartners (S : Set (PretorsionTheory C)) : Type _ :=
  {F : Subcategory C // IsPretorsionTheory (meetT S).prop F.prop ∧ ∀ P ∈ S, P.F ≤ F}
def meet (S : Set (PretorsionTheory C)) : PretorsionTheory C :=
  ⟨meetT S, Subcategory.iInf (fun F : MeetPartners S => F.1),
    isPretorsionTheory_iInf (IsQuotientClosed.iInf fun P : S => P.1.isPretorsionTheory.isQuotientClosed)
      (fun F => F.2.1)⟩
theorem isGLB_meet (S : Set (PretorsionTheory C)) : IsGLB S (meet S) := by
  refine ⟨fun P hP => ⟨fun X hX => (iInf_prop_iff _ X).1 hX ⟨P, hP⟩, fun X hX => ?_⟩,
    fun Q hQ => ⟨fun X hX => ?_, fun X hX => ?_⟩⟩
  · rw [show (meet S).F = Subcategory.iInf (fun F : MeetPartners S => F.1) from rfl, iInf_prop_iff]
    exact fun F => F.2.2 P hP X hX
  · show (meetT S).prop X
    rw [meetT, iInf_prop_iff]
    exact fun P => (hQ P.2).1 X hX
  · have hQF : IsPretorsionTheory (meetT S).prop Q.F.prop :=
      isPretorsionTheory_iInf_left (T := fun P : S => P.1.T) (F := fun P : S => P.1.F)
        (fun P => P.1.isPretorsionTheory) Q.isPretorsionTheory (fun P => (hQ P.2).1)
        (fun P => (hQ P.2).2)
    exact (iInf_prop_iff _ X).1 hX ⟨Q.F, hQF, fun P hP => (hQ hP).2⟩
instance : InfSet (PretorsionTheory C) := ⟨meet⟩
instance : _root_.CompleteLattice (PretorsionTheory C) := completeLatticeOfInf _ isGLB_meet
def join (S : Set (PretorsionTheory C)) : PretorsionTheory C := (meet (PretorsionTheory.op '' S)).unop
def botPT : PretorsionTheory C := ⟨⊥, ⊤, isPretorsionTheory_top_right isQuotientClosed_bot⟩
def topPT : PretorsionTheory C := ⟨⊤, ⊥, isPretorsionTheory_top_left isSubobjectClosed_bot⟩
end PretorsionTheory
end PretorsionImageClosed.Statement


