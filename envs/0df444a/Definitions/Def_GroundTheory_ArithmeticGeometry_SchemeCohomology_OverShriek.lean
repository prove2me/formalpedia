-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_OverShriek
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_OverShriek
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:30.730362+00:00
-- url     : https://prove2.me/theorems/71fda703-56b5-4c3c-a321-d8aac08d3056
-- title:
--   Over Shriek
-- statement:
--   Definitions and structural lemmas for Over Shriek, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/OverShriek.lean

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
namespace GroundTheory.Arith.SchemeCoh
open CategoryTheory Limits Opposite DirectSum
universe v u
attribute [local instance] Classical.decEq
variable {C : Type u} [Category.{v} C] {U : C}
section Presheaf
variable (P : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{v})
abbrev shriekSummand (X : C) (s : X ⟶ U) : Type v := P.obj (op (Over.mk s))
noncomputable def shriekMap {X Y : C} (g : Y ⟶ X) :
    (⨁ s : X ⟶ U, shriekSummand P X s) →+ ⨁ t : Y ⟶ U, shriekSummand P Y t :=
  DirectSum.toAddMonoid fun s =>
    (DirectSum.of (shriekSummand P Y) (g ≫ s)).comp
      (P.map (Over.homMk g rfl : Over.mk (g ≫ s) ⟶ Over.mk s).op).hom
lemma shriekMap_of {X Y : C} (g : Y ⟶ X) (s : X ⟶ U) (x : shriekSummand P X s) :
    shriekMap P g (DirectSum.of _ s x) =
      DirectSum.of (shriekSummand P Y) (g ≫ s)
        (P.map (Over.homMk g rfl : Over.mk (g ≫ s) ⟶ Over.mk s).op x) :=
  DirectSum.toAddMonoid_of _ _ _
lemma shriek_of_eq_of {Y : C} {V : Over U} {t t' : Y ⟶ U} (h : t = t') (a : Over.mk t ⟶ V)
    (a' : Over.mk t' ⟶ V) (ha : a.left = a'.left) (x : P.obj (op V)) :
    DirectSum.of (shriekSummand P Y) t (P.map a.op x) =
      DirectSum.of (shriekSummand P Y) t' (P.map a'.op x) := by
  subst h
  rw [Over.OverMorphism.ext ha]
@[simps]
noncomputable def shriekPresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj X := AddCommGrpCat.of (⨁ s : X.unop ⟶ U, shriekSummand P X.unop s)
  map g := AddCommGrpCat.ofHom (shriekMap P g.unop)
  map_id X := by
    apply AddCommGrpCat.hom_ext
    apply DirectSum.addHom_ext
    intro s x
    simp only [AddCommGrpCat.hom_ofHom, unop_id, AddCommGrpCat.hom_id, AddMonoidHom.id_apply]
    rw [shriekMap_of]
    rw [shriek_of_eq_of P (Category.id_comp s) _ (𝟙 _) (by simp)]
    simp
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    apply DirectSum.addHom_ext
    intro s x
    simp only [AddCommGrpCat.hom_ofHom, unop_comp, AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp,
      Function.comp_apply]
    rw [shriekMap_of, shriekMap_of, shriekMap_of, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← op_comp]
    exact shriek_of_eq_of P (by simp) _ _ (by simp) x
variable {P} in

@[simps]
noncomputable def shriekPresheafMap {Q : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{v}} (φ : P ⟶ Q) :
    shriekPresheaf P ⟶ shriekPresheaf Q where
  app X := AddCommGrpCat.ofHom (DirectSum.toAddMonoid fun s =>
    (DirectSum.of (shriekSummand Q X.unop) s).comp (φ.app (op (Over.mk s))).hom)
  naturality X Y g := by
    apply AddCommGrpCat.hom_ext
    apply DirectSum.addHom_ext
    intro s x
    change (DirectSum.toAddMonoid fun s => (DirectSum.of (shriekSummand Q Y.unop) s).comp
        (φ.app (op (Over.mk s))).hom) (shriekMap P g.unop (DirectSum.of _ s x)) =
      shriekMap Q g.unop ((DirectSum.toAddMonoid fun s => (DirectSum.of (shriekSummand Q X.unop) s).comp
        (φ.app (op (Over.mk s))).hom) (DirectSum.of _ s x))
    rw [shriekMap_of, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of,
      AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, shriekMap_of]
    congr 1
    exact NatTrans.naturality_apply φ _ x
lemma shriekPresheafMap_app_of {P Q : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{v}} (φ : P ⟶ Q) (X : Cᵒᵖ)
    (s : X.unop ⟶ U) (x : shriekSummand P X.unop s) :
    (shriekPresheafMap φ).app X (DirectSum.of (shriekSummand P X.unop) s x) =
      DirectSum.of (shriekSummand Q X.unop) s (φ.app (op (Over.mk s)) x) :=
  DirectSum.toAddMonoid_of
    (fun t => (DirectSum.of (shriekSummand Q X.unop) t).comp (φ.app (op (Over.mk t))).hom) s x
end Presheaf
variable (U) in

@[simps]
noncomputable def shriekFunctor : ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{v}) where
  obj P := shriekPresheaf P
  map φ := shriekPresheafMap φ
  map_id P := by
    ext X : 2
    apply AddCommGrpCat.hom_ext
    apply DirectSum.addHom_ext
    intro s x
    change DirectSum.toAddMonoid _ (DirectSum.of _ s x) = DirectSum.of _ s x
    rw [DirectSum.toAddMonoid_of]
    rfl
  map_comp {P₁ P₂ P₃} φ ψ := by
    ext X : 2
    apply AddCommGrpCat.hom_ext
    apply DirectSum.addHom_ext
    intro s x
    change (DirectSum.toAddMonoid fun s => (DirectSum.of (shriekSummand P₃ X.unop) s).comp
        ((ψ.app (op (Over.mk s))).hom.comp (φ.app (op (Over.mk s))).hom))
          (DirectSum.of (shriekSummand P₁ X.unop) s x) =
      (DirectSum.toAddMonoid fun s => (DirectSum.of (shriekSummand P₃ X.unop) s).comp
        (ψ.app (op (Over.mk s))).hom) ((DirectSum.toAddMonoid fun s =>
          (DirectSum.of (shriekSummand P₂ X.unop) s).comp (φ.app (op (Over.mk s))).hom)
            (DirectSum.of (shriekSummand P₁ X.unop) s x))
    simp only [DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply]
section Adjunction
variable {P : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{v}} {Q : Cᵒᵖ ⥤ AddCommGrpCat.{v}}
@[simps]
noncomputable def shriekHomToRestrict (α : shriekPresheaf P ⟶ Q) :
    P ⟶ (Over.forget U).op ⋙ Q where
  app V := AddCommGrpCat.ofHom ((α.app (op V.unop.left)).hom.comp
    (DirectSum.of (shriekSummand P V.unop.left) V.unop.hom))
  naturality V W f := by
    ext x
    change (α.app (op W.unop.left)) (DirectSum.of (shriekSummand P W.unop.left) W.unop.hom
        (P.map f x)) =
      Q.map f.unop.left.op ((α.app (op V.unop.left)) (DirectSum.of (shriekSummand P V.unop.left)
        V.unop.hom x))
    refine (congrArg (α.app (op W.unop.left)) ?_).trans
      (NatTrans.naturality_apply α f.unop.left.op _)
    exact (shriek_of_eq_of P (Over.w f.unop).symm f.unop _ rfl x).trans
      (shriekMap_of P f.unop.left V.unop.hom x).symm
noncomputable abbrev shriekHomOfRestrictApp (β : P ⟶ (Over.forget U).op ⋙ Q) (X : Cᵒᵖ) :
    (⨁ s : X.unop ⟶ U, shriekSummand P X.unop s) →+ Q.obj X :=
  DirectSum.toAddMonoid fun s => (β.app (op (Over.mk s))).hom
lemma shriekHomOfRestrictApp_of (β : P ⟶ (Over.forget U).op ⋙ Q) (X : Cᵒᵖ) (s : X.unop ⟶ U)
    (x : shriekSummand P X.unop s) :
    shriekHomOfRestrictApp β X (DirectSum.of (shriekSummand P X.unop) s x) =
      β.app (op (Over.mk s)) x :=
  DirectSum.toAddMonoid_of _ _ _
@[simps]
noncomputable def shriekHomOfRestrict (β : P ⟶ (Over.forget U).op ⋙ Q) :
    shriekPresheaf P ⟶ Q where
  app X := AddCommGrpCat.ofHom (shriekHomOfRestrictApp β X)
  naturality X Y g := by
    apply AddCommGrpCat.hom_ext
    apply DirectSum.addHom_ext
    intro s x
    refine (congrArg ((shriekHomOfRestrictApp β Y)) (shriekMap_of P g.unop s x)).trans ?_
    refine (shriekHomOfRestrictApp_of β Y _ _).trans ?_
    refine Eq.trans ?_ (congrArg (Q.map g) (shriekHomOfRestrictApp_of β X s x).symm)
    exact NatTrans.naturality_apply β _ x
variable (U) in

noncomputable def shriekAdjunction :
    shriekFunctor U ⊣ (Functor.whiskeringLeft _ _ AddCommGrpCat.{v}).obj (Over.forget U).op :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P Q =>
        { toFun := shriekHomToRestrict
          invFun := shriekHomOfRestrict
          left_inv := fun α => by
            ext X : 2
            apply AddCommGrpCat.hom_ext
            apply DirectSum.addHom_ext
            intro s x
            exact (shriekHomOfRestrictApp_of (shriekHomToRestrict α) X s x).trans rfl
          right_inv := fun β => by
            ext V x
            exact shriekHomOfRestrictApp_of β (op V.unop.left) V.unop.hom x }
      homEquiv_naturality_left_symm := fun {P P' Q} f g => by
        ext X : 2
        apply AddCommGrpCat.hom_ext
        apply DirectSum.addHom_ext
        intro s x
        refine (shriekHomOfRestrictApp_of (f ≫ g) X s x).trans ?_
        refine Eq.trans ?_ (congrArg (shriekHomOfRestrictApp g X)
          (shriekPresheafMap_app_of f X s x).symm)
        exact (shriekHomOfRestrictApp_of g X s _).symm
      homEquiv_naturality_right := fun {P Q Q'} f g => rfl }
end Adjunction
instance : (shriekFunctor U).PreservesMonomorphisms where
  preserves {P Q} φ _ := by
    have hφ : ∀ V, Function.Injective (φ.app V) := fun V =>
      (AddCommGrpCat.mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app φ).1 inferInstance V)
    rw [NatTrans.mono_iff_mono_app]
    intro X
    rw [AddCommGrpCat.mono_iff_injective]
    have key : (DirectSum.toAddMonoid fun s => (DirectSum.of (shriekSummand Q X.unop) s).comp
        (φ.app (op (Over.mk s))).hom) =
        DFinsupp.mapRange.addMonoidHom (fun s => (φ.app (op (Over.mk s))).hom) := by
      apply DirectSum.addHom_ext
      intro s x
      rw [DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply, DFinsupp.mapRange.addMonoidHom_apply]
      exact (DFinsupp.mapRange_single (f := fun s => ⇑(φ.app (op (Over.mk s))).hom)
        (hf := fun s => map_zero _)).symm
    change Function.Injective (DirectSum.toAddMonoid fun s =>
      (DirectSum.of (shriekSummand Q X.unop) s).comp (φ.app (op (Over.mk s))).hom)
    rw [key]
    intro a b hab
    exact (DFinsupp.mapRange_injective _ (fun s => map_zero _)).2 (fun s => hφ _) hab
section Sheaf
variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]
noncomputable def sheafShriek (U : C) : Sheaf (J.over U) AddCommGrpCat.{v} ⥤ Sheaf J AddCommGrpCat.{v} :=
  sheafToPresheaf _ _ ⋙ shriekFunctor U ⋙ presheafToSheaf J _
noncomputable def sheafShriekAdjunction (U : C) :
    sheafShriek J U ⊣ J.overPullback AddCommGrpCat.{v} U :=
  ((shriekAdjunction U).comp (sheafificationAdjunction J AddCommGrpCat.{v})).restrictFullyFaithful
    (iC := sheafToPresheaf (J.over U) AddCommGrpCat.{v}) (iD := 𝟭 _)
    (fullyFaithfulSheafToPresheaf _ _) (Functor.FullyFaithful.id _)
    (Functor.rightUnitor _).symm
    (Functor.leftUnitor _ ≪≫ ((Over.forget U).sheafPushforwardContinuousCompSheafToPresheafIso
      AddCommGrpCat.{v} (J.over U) J).symm)
instance (U : C) : (sheafShriek J U).PreservesMonomorphisms := by
  unfold sheafShriek
  infer_instance
instance (U : C) : (J.overPullback AddCommGrpCat.{v} U).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (sheafShriekAdjunction J U)
end Sheaf
end GroundTheory.Arith.SchemeCoh


