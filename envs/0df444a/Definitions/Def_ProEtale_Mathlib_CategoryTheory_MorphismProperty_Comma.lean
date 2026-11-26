-- Prove2me | Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma
-- name    : ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T11:12:11.585671+00:00
-- url     : https://prove2.me/theorems/3a85feb5-27d8-4d16-af59-dd89b672512e
-- title:
--   Functors between comma categories defined by morphism properties
-- statement:
--   The functors `MorphismProperty.Comma.preLeft` and `MorphismProperty.CostructuredArrow.pre` induced on comma categories with prescribed morphism properties by precomposition on the left.
-- source:
--   Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/MorphismProperty/Comma.lean (declarations kept unchanged, unused ones removed).

import Mathlib
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
namespace CategoryTheory.MorphismProperty

variable {T : Type*} [Category T] {P Q : MorphismProperty T} (X : T) [Q.IsMultiplicative]

variable {C D : Type*} [Category C] [Category D]
variable (P : MorphismProperty D) (Q : MorphismProperty C) [Q.IsMultiplicative] (F : C ⥤ D) (X : D)


@[simps]
def Comma.preLeft {A : Type*} [Category* A] {B : Type*}
    [Category* B] {T : Type*} [Category* T] {C : Type*} [Category* C] (F : C ⥤ A) (L : A ⥤ T)
    (R : B ⥤ T) {P P' : MorphismProperty T} {Q : MorphismProperty C} [Q.IsMultiplicative]
    {Q' : MorphismProperty A} [Q'.IsMultiplicative] (W : MorphismProperty B) [W.IsMultiplicative]
    (h : P ⊓ .ofObjectProperty (F ⋙ L).essImage ⊤ ≤ P') (h' : Q ≤ Q'.inverseImage F) :
    P.Comma (F ⋙ L) R Q W ⥤ P'.Comma L R Q' W where
  obj X :=
    { left := F.obj X.left
      right := X.right
      hom := X.hom
      prop := h _ ⟨X.prop, by
        simp only [ofObjectProperty_top_right_iff]; apply Functor.obj_mem_essImage⟩ }
  map f :=
    { left := F.map f.left
      right := f.right
      w := by simpa using f.w
      prop_hom_left := h' _ f.prop_hom_left
      prop_hom_right := f.prop_hom_right }

@[simps!]
def CostructuredArrow.pre
    {C D E : Type*} [Category* C] [Category* D] [Category* E] (F : C ⥤ D) (G : D ⥤ E)
    (X : E)
    {P P' : MorphismProperty E}
    (h : P ⊓ .ofObjectProperty (F ⋙ G).essImage ⊤ ≤ P')
    {Q : MorphismProperty C} [Q.IsMultiplicative]
    {Q' : MorphismProperty D} [Q'.IsMultiplicative]
    (h' : Q ≤ Q'.inverseImage F) :
    P.CostructuredArrow Q (F ⋙ G) X ⥤ P'.CostructuredArrow Q' G X :=
  MorphismProperty.Comma.preLeft _ _ _ _ h h'


end CategoryTheory.MorphismProperty


