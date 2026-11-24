-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_SheafH
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_SheafH
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:28.760417+00:00
-- url     : https://prove2.me/theorems/8c1a5db9-cc6d-4cba-8777-11f4bc1df55c
-- title:
--   Sheaf H
-- statement:
--   Definitions and structural lemmas for Sheaf H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/SheafH.lean

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
open CategoryTheory Limits Opposite Abelian
universe w' v u
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
section ExtIso
variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasExt.{w'} 𝒜]
noncomputable def extAddEquivOfIsoLeft {X X' : 𝒜} (e : X ≅ X') (Y : 𝒜) (n : ℕ) :
    Ext X Y n ≃+ Ext X' Y n where
  toFun x := (Ext.mk₀ e.inv).comp x (zero_add n)
  invFun x := (Ext.mk₀ e.hom).comp x (zero_add n)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp [Ext.comp_add]
end ExtIso
section Terminal
noncomputable def freeYonedaTerminalIso {T : C} (hT : IsTerminal T) :
    yoneda.obj T ⋙ AddCommGrpCat.free.{v} ≅
      (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  NatIso.ofComponents (fun X =>
    letI : Unique (X.unop ⟶ T) := ⟨⟨hT.from _⟩, fun _ => hT.hom_ext _ _⟩
    ((FreeAbelianGroup.uniqueEquiv (X.unop ⟶ T)).trans AddEquiv.ulift.symm).toAddCommGrpIso)
    (fun {X Y} f => by
      ext x
      change ULift.up (FreeAbelianGroup.lift (fun _ => (1 : ℤ))
          (FreeAbelianGroup.map (fun g => f.unop ≫ g) x)) =
        ULift.up (FreeAbelianGroup.lift (fun _ => (1 : ℤ)) x)
      congr 1
      induction x using FreeAbelianGroup.induction_on with
      | zero => simp
      | of a => simp
      | neg a h => simp only [map_neg, h]
      | add a b ha hb => simp only [map_add, ha, hb])
variable [HasSheafify J AddCommGrpCat.{v}]
noncomputable def freeSheafTerminalIso {T : C} (hT : IsTerminal T) :
    (presheafToSheaf J AddCommGrpCat.{v}).obj (yoneda.obj T ⋙ AddCommGrpCat.free) ≅
      (constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  (presheafToSheaf J AddCommGrpCat.{v}).mapIso (freeYonedaTerminalIso hT)
variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
noncomputable def cohomologyPresheafTerminalAddEquiv (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ)
    {T : C} (hT : IsTerminal T) :
    (F.cohomologyPresheaf n).obj (op T) ≃+ Sheaf.H F n :=
  extAddEquivOfIsoLeft (freeSheafTerminalIso (J := J) hT) F n
end Terminal
section Zero
noncomputable def freeYonedaHomAddEquiv (U : C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    (yoneda.obj U ⋙ AddCommGrpCat.free.{v} ⟶ P) ≃+ P.obj (op U) where
  toEquiv := ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj U) P).trans yonedaEquiv
  map_add' _ _ := rfl
variable [HasSheafify J AddCommGrpCat.{v}]
noncomputable abbrev freeSheaf (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]
    (U : C) : Sheaf J AddCommGrpCat.{v} :=
  (presheafToSheaf J AddCommGrpCat.{v}).obj (yoneda.obj U ⋙ AddCommGrpCat.free)
noncomputable abbrev freeSheafMap (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]
    {U V : C} (f : U ⟶ V) : freeSheaf J U ⟶ freeSheaf J V :=
  (presheafToSheaf J AddCommGrpCat.{v}).map
    (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free)
noncomputable def freeSheafHomAddEquiv (U : C) (F : Sheaf J AddCommGrpCat.{v}) :
    (freeSheaf J U ⟶ F) ≃+ F.obj.obj (op U) :=
  ((sheafificationAdjunction J AddCommGrpCat.{v}).homAddEquiv _ F).trans
    (freeYonedaHomAddEquiv U F.obj)
variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
noncomputable def H'.equiv₀ (F : Sheaf J AddCommGrpCat.{v}) (U : C) :
    F.H' 0 U ≃+ F.obj.obj (op U) :=
  (Ext.addEquiv₀ (X := freeSheaf J U) (Y := F)).trans (freeSheafHomAddEquiv U F)
end Zero
section Injective
variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
lemma H.eq_zero_of_injective (F : Sheaf J AddCommGrpCat.{v}) [Injective F] {n : ℕ}
    (x : Sheaf.H F (n + 1)) : x = 0 :=
  Ext.eq_zero_of_injective x
instance H'.subsingleton_of_injective (F : Sheaf J AddCommGrpCat.{v}) [Injective F] (n : ℕ)
    (U : C) : Subsingleton (F.H' (n + 1) U) :=
  subsingleton_of_forall_eq 0 fun x =>
    Ext.eq_zero_of_injective (show Ext (freeSheaf J U) F (n + 1) from x)
end Injective
section LongExact
variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)
noncomputable def H.δ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) : Sheaf.H S.X₃ n₀ →+ Sheaf.H S.X₁ n₁ :=
  hS.extClass.postcomp _ h
noncomputable def H.sequence (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat.{w'} 5 :=
  ComposableArrows.mk₅ ((Sheaf.functorH J n₀).map S.f) ((Sheaf.functorH J n₀).map S.g)
    (AddCommGrpCat.ofHom (H.δ hS n₀ n₁ h)) ((Sheaf.functorH J n₁).map S.f)
    ((Sheaf.functorH J n₁).map S.g)
noncomputable def H'.δ (U : C) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) : S.X₃.H' n₀ U ⟶ S.X₁.H' n₁ U :=
  AddCommGrpCat.ofHom (hS.extClass.postcomp (freeSheaf J U) h)
noncomputable def H'.sequence (U : C) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat.{w'} 5 :=
  ComposableArrows.mk₅ (((Sheaf.cohomologyPresheafFunctor J n₀).map S.f).app (op U))
    (((Sheaf.cohomologyPresheafFunctor J n₀).map S.g).app (op U)) (H'.δ hS U n₀ n₁ h)
    (((Sheaf.cohomologyPresheafFunctor J n₁).map S.f).app (op U))
    (((Sheaf.cohomologyPresheafFunctor J n₁).map S.g).app (op U))
end LongExact
end GroundTheory.Arith.SchemeCoh


