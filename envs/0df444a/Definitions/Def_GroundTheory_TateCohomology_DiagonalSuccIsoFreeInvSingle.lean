-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_DiagonalSuccIsoFreeInvSingle
-- name    : GroundTheory_TateCohomology_DiagonalSuccIsoFreeInvSingle
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:50:52.857072+00:00
-- url     : https://prove2.me/theorems/a15d87db-2f06-449b-a8a5-7ca309229af3
-- title:
--   Diagonal Succ Iso Free Inv Single
-- statement:
--   Definitions and structural lemmas for Diagonal Succ Iso Free Inv Single, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/DiagonalSuccIsoFreeInvSingle.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.GroupCoh
open CategoryTheory Limits groupCohomology Rep
universe v w u
section HomComplex
variable {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
noncomputable def linearYonedaObjMap {X Y : ChainComplex C ℕ} (f : X ⟶ Y) (B : C) :
    Y.linearYonedaObj R B ⟶ X.linearYonedaObj R B :=
  (HomologicalComplex.unopFunctor (ModuleCat R) (ComplexShape.down ℕ)).map
    ((((linearYoneda R C).obj B).rightOp.mapHomologicalComplex _).map f).op
lemma linearYonedaObjMap_comp {X Y Z : ChainComplex C ℕ} (f : X ⟶ Y) (g : Y ⟶ Z) (B : C) :
    linearYonedaObjMap (R := R) (f ≫ g) B = linearYonedaObjMap g B ≫ linearYonedaObjMap f B := by
  ext n x
  change (f ≫ g).f n ≫ x = f.f n ≫ g.f n ≫ x
  rw [HomologicalComplex.comp_f]
  exact Category.assoc _ _ _
lemma linearYonedaObjMap_id (X : ChainComplex C ℕ) (B : C) :
    linearYonedaObjMap (R := R) (𝟙 X) B = 𝟙 _ := by
  ext n x
  change (𝟙 X : X ⟶ X).f n ≫ x = x
  rw [HomologicalComplex.id_f]
  exact Category.id_comp _
noncomputable def linearYonedaObjHomotopy {X Y : ChainComplex C ℕ} {f g : X ⟶ Y}
    (h : Homotopy f g) (B : C) :
    Homotopy (linearYonedaObjMap (R := R) f B) (linearYonedaObjMap g B) :=
  ((((linearYoneda R C).obj B).rightOp).mapHomotopy h).unop
noncomputable def linearYonedaObjHomotopyEquiv {X Y : ChainComplex C ℕ} (e : HomotopyEquiv X Y)
    (B : C) : HomotopyEquiv (Y.linearYonedaObj R B) (X.linearYonedaObj R B) where
  hom := linearYonedaObjMap e.hom B
  inv := linearYonedaObjMap e.inv B
  homotopyHomInvId := (Homotopy.ofEq (linearYonedaObjMap_comp _ _ _).symm).trans
    ((linearYonedaObjHomotopy e.homotopyInvHomId B).trans
      (Homotopy.ofEq (linearYonedaObjMap_id _ _)))
  homotopyInvHomId := (Homotopy.ofEq (linearYonedaObjMap_comp _ _ _).symm).trans
    ((linearYonedaObjHomotopy e.homotopyHomInvId B).trans
      (Homotopy.ofEq (linearYonedaObjMap_id _ _)))
end HomComplex
section Bar
variable {k G : Type u} [CommRing k] [Group G]
end Bar
section Norm
variable {k H : Type u} [CommRing k] [Group H] [Fintype H]
end Norm
end GroundTheory.GroupCoh


