-- Prove2me | Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma_Lib
-- name    : ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma_Lib
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:37:30.522806+00:00
-- url     : https://prove2.me/theorems/b0ed7e2f-1c03-4ad1-aec0-6677e769e1e1
-- title:
--   Comma categories with morphism properties: lifts, opposite duality of over and under categories, and iterated slices
-- statement:
--   This file continues the published file of the same module. For a morphism property $P$ on a category $T$ and a multiplicative morphism property $Q$, $P.\mathrm{Over}\,Q\,X$ denotes the category of arrows $Y \to X$ in $P$ with morphisms over $X$ whose underlying morphism is in $Q$; dually for $P.\mathrm{Under}\,Q\,X$. The file provides:
--
--   1. **Lifts.** A functor $F : \mathcal C \to T/X$ whose objects have structure maps in $P$ and whose morphisms have underlying maps in $Q$ lifts to a functor $\mathcal C \to P.\mathrm{Over}\,Q\,X$; likewise for under categories.
--   2. **Opposite duality.** An equivalence
--   $$P.\mathrm{Under}\,Q\,X \;\simeq\; \big(P^{\mathrm{op}}.\mathrm{Over}\,Q^{\mathrm{op}}\,X^{\mathrm{op}}\big)^{\mathrm{op}}.$$
--   3. **Trivial properties.** If $P$, $Q$ and $W$ are all the total property $\top$, the comma category with properties is equivalent to the ordinary comma category $(L \downarrow R)$.
--   4. **Iterated slices.** If $P$ is stable under composition and $A = (A \to X) \in P.\mathrm{Over}\,\top\,X$, then the category of objects over $A$ (in the slice $P.\mathrm{Over}\,\top\,X$) whose underlying morphism is in $P$ is equivalent to $P.\mathrm{Over}\,\top\,A$.
--
--   These equivalences are used to pass between rings and affine schemes and to identify slices of the étale and pro-étale sites.
--
--   **Formalization Note** Main declarations: `CategoryTheory.MorphismProperty.Over.lift`, `MorphismProperty.Under.lift`, `MorphismProperty.Under.equivOpOverOp`, `MorphismProperty.Comma.equivOfEqTop` (the equalities $P = \top$ etc. are default arguments closed by `rfl`), `MorphismProperty.Over.iteratedSliceEquiv`. In item 4 the property on the iterated slice is the inverse image of $P$ under the forgetful functor $P.\mathrm{Over}\,\top\,X \to T$.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/MorphismProperty/Comma.lean (declarations needed by the transplanted proofs, unused ones removed). Continues the published definition file Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma of the same module.

import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty_Lib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
namespace CategoryTheory
namespace MorphismProperty

variable {T : Type*} [Category T] {P Q : MorphismProperty T} (X : T) [Q.IsMultiplicative]

variable {C D : Type*} [Category C] [Category D]
variable (P : MorphismProperty D) (Q : MorphismProperty C) [Q.IsMultiplicative] (F : C ⥤ D) (X : D)

section Opposite

variable {A B T : Type*} [Category A] [Category B] [Category T]
  (L : A ⥤ T) (R : B ⥤ T)
  (P : MorphismProperty T) (Q : MorphismProperty A) (W : MorphismProperty B)
  [Q.IsMultiplicative]
  [W.IsMultiplicative]


section

variable {P}
variable {Q : MorphismProperty T} [Q.IsMultiplicative]
variable {C : Type*} [Category C]

def Over.lift {X : T} (F : C ⥤ Over X) (obj : ∀ Y, P (F.obj Y).hom)
    (map : ∀ {Y Z : C} (f : Y ⟶ Z), Q (F.map f).left) : C ⥤ P.Over Q X where
  obj Y := ⟨F.obj Y, obj Y⟩
  map f := ⟨F.map f, map f, trivial⟩

def Under.lift {X : T} (F : C ⥤ Under X) (obj : ∀ Y, P (F.obj Y).hom)
    (map : ∀ {Y Z : C} (f : Y ⟶ Z), Q (F.map f).right) : C ⥤ P.Under Q X where
  obj Y := ⟨F.obj Y, obj Y⟩
  map f := ⟨F.map f, trivial, map f⟩

end


@[simps! functor_obj_unop_left functor_map_unop_left inverse_obj_right inverse_map_right]
def Under.equivOpOverOp (Q : MorphismProperty T) [Q.IsMultiplicative] (X : T) :
    P.Under Q X ≌ (P.op.Over Q.op (Opposite.op X))ᵒᵖ where
  functor := .rightOp <| Over.lift
    (.leftOp <| Under.forget _ _ _ ⋙ (CategoryTheory.Over.opEquivOpUnder X).inverse.rightOp)
    (fun Y ↦ Y.unop.prop) (fun f ↦ f.unop.prop_hom_right)
  inverse := Under.lift
    (.leftOp <| Over.forget _ _ _ ⋙ (CategoryTheory.Over.opEquivOpUnder X).functor)
    (fun Y ↦ Y.unop.prop) (fun f ↦ f.unop.prop_hom_left)
  unitIso := NatIso.ofComponents fun _ ↦ Iso.refl _
  counitIso := NatIso.ofComponents fun _ ↦ Iso.refl _

end Opposite


@[simps]
def Comma.equivOfEqTop {A B T : Type*} [Category* A]
    [Category* B] [Category* T] (L : A ⥤ T) (R : B ⥤ T)
    {P : MorphismProperty T} {Q : MorphismProperty A} {W : MorphismProperty B}
    [Q.IsMultiplicative] [W.IsMultiplicative]
    (hP : P = ⊤ := by rfl) (hQ : Q = ⊤ := by rfl) (hW : W = ⊤ := by rfl) :
    P.Comma L R Q W ≌ Comma L R where
  functor := MorphismProperty.Comma.forget _ _ _ _ _
  inverse := MorphismProperty.Comma.lift (𝟭 _) (by simp [hP]) (by simp [hQ]) (by simp [hW])
  unitIso := Iso.refl _
  counitIso := Iso.refl _

@[simps]
def Over.iteratedSliceEquiv {C : Type*} [Category* C]
    {P : MorphismProperty C} [P.IsStableUnderComposition] {X : C} (A : P.Over ⊤ X) :
    MorphismProperty.Over
      (P.inverseImage <| MorphismProperty.Over.forget _ _ _ ⋙ CategoryTheory.Over.forget _) ⊤ A ≌
      P.Over ⊤ A.left where
  functor.obj U := .mk _ U.hom.left U.prop
  functor.map {U V} f :=
    MorphismProperty.Over.homMk f.left.left (by dsimp; rw [← Over.w f]; rfl) trivial
  inverse.obj U := .mk _
    (MorphismProperty.Over.homMk (A := .mk _ (U.hom ≫ A.hom)
      (P.comp_mem _ _ U.prop A.prop)) U.hom (by simp) trivial) (by simp [U.prop])
  inverse.map f :=
    MorphismProperty.Over.homMk (MorphismProperty.Over.homMk f.left (by simp) trivial)
      (by ext; simp) trivial
  -- We don't use `cat_disch` to improve performance.
  unitIso := NatIso.ofComponents (fun U ↦ Over.isoMk (Over.isoMk (Iso.refl _)) (by ext; simp))
    (by intros; ext; simp)
  counitIso := NatIso.ofComponents (fun U ↦ Over.isoMk (Iso.refl _))
    (by intros; ext; simp)
  functor_unitIso_comp U := by ext; simp

end MorphismProperty
end CategoryTheory


