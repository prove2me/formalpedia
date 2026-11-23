-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:52.914328+00:00
-- url     : https://prove2.me/theorems/4bde6dfa-e136-4483-b853-6c272726a434
-- title:
--   Cohomology Presheaf Functor Map App Apply
-- statement:
--   Definitions and structural lemmas for Cohomology Presheaf Functor Map App Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w v u
namespace GlobalTheory
namespace Flasque
section Site
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]
noncomputable abbrev freeSheaf (U : C) : Sheaf J AddCommGrpCat.{v} :=
  (presheafToSheaf J _).obj (yoneda.obj U ⋙ AddCommGrpCat.free)
noncomputable abbrev freeSheafMap {V U : C} (i : V ⟶ U) : freeSheaf J V ⟶ freeSheaf J U :=
  (presheafToSheaf J _).map (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free)
instance mono_freeSheafMap {V U : C} (i : V ⟶ U) [Mono i] : Mono (freeSheafMap J i) := by
  infer_instance
noncomputable def freeSheafGen (U : C) : (freeSheaf J U).obj.obj (op U) :=
  (toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)).app (op U) (FreeAbelianGroup.of (𝟙 U))
variable {J}
noncomputable def freeSheafHomEquiv (U : C) (F : Sheaf J AddCommGrpCat.{v}) :
    (freeSheaf J U ⟶ F) ≃+ F.obj.obj (op U) where
  toEquiv := ((sheafificationAdjunction J _).homEquiv _ _).trans
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _).trans yonedaEquiv)
  map_add' f g := by
    rfl
lemma freeSheafHomEquiv_comp {U : C} {F G : Sheaf J AddCommGrpCat.{v}} (f : freeSheaf J U ⟶ F)
    (g : F ⟶ G) :
    freeSheafHomEquiv U G (f ≫ g) = g.hom.app (op U) (freeSheafHomEquiv U F f) := rfl
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
noncomputable def sectionsEquiv (F : Sheaf J AddCommGrpCat.{v}) (U : C) :
    F.H' 0 U ≃+ F.obj.obj (op U) :=
  (Ext.addEquiv₀ (X := freeSheaf J U) (Y := F)).trans (freeSheafHomEquiv U F)
lemma sectionsEquiv_mk₀ {F : Sheaf J AddCommGrpCat.{v}} {U : C} (f : freeSheaf J U ⟶ F) :
    sectionsEquiv F U (Ext.mk₀ f) = freeSheafHomEquiv U F f :=
  congrArg (freeSheafHomEquiv U F) (Ext.addEquiv₀.apply_symm_apply f)
lemma sectionsEquiv_map {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (U : C) (x : F.H' 0 U) :
    sectionsEquiv G U (((Sheaf.cohomologyPresheafFunctor J 0).map f).app (op U) x) =
      f.hom.app (op U) (sectionsEquiv F U x) := by
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective (freeSheaf J U) F).2 x
  refine (congrArg (sectionsEquiv G U) (Ext.mk₀_comp_mk₀ g f)).trans ?_
  rw [sectionsEquiv_mk₀, sectionsEquiv_mk₀, freeSheafHomEquiv_comp]
section Shift
variable {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)
noncomputable def connecting (n : ℕ) (U : C) : S.X₃.H' n U →+ S.X₁.H' (n + 1) U :=
  hS.extClass.postcomp (freeSheaf J U) rfl
lemma exact_map_connecting (n : ℕ) (U : C) :
    Function.Exact (((Sheaf.cohomologyPresheafFunctor J n).map S.g).app (op U))
      (connecting hS n U) :=
  (ShortComplex.ab_exact_iff_function_exact _).1
    (Ext.covariant_sequence_exact₃' (freeSheaf J U) hS n (n + 1) rfl)
lemma exact_connecting_map (n : ℕ) (U : C) :
    Function.Exact (connecting hS n U)
      (((Sheaf.cohomologyPresheafFunctor J (n + 1)).map S.f).app (op U)) :=
  (ShortComplex.ab_exact_iff_function_exact _).1
    (Ext.covariant_sequence_exact₁' (freeSheaf J U) hS n (n + 1) rfl)
lemma connecting_injective (n : ℕ) (U : C) (h : Subsingleton (S.X₂.H' n U)) :
    Function.Injective (connecting hS n U) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (exact_map_connecting hS n U x).1 hx
  rw [Subsingleton.elim y 0, map_zero]
lemma connecting_surjective (n : ℕ) (U : C) (h : Subsingleton (S.X₂.H' (n + 1) U)) :
    Function.Surjective (connecting hS n U) := fun x ↦
  (exact_connecting_map hS n U x).1 (Subsingleton.elim (h := h) _ _)
noncomputable def shiftEquiv (n : ℕ) (U : C) (h : Subsingleton (S.X₂.H' n U))
    (h' : Subsingleton (S.X₂.H' (n + 1) U)) : S.X₃.H' n U ≃+ S.X₁.H' (n + 1) U :=
  AddEquiv.ofBijective (connecting hS n U)
    ⟨connecting_injective hS n U h, connecting_surjective hS n U h'⟩
@[simp]
lemma shiftEquiv_apply (n : ℕ) (U : C) (h : Subsingleton (S.X₂.H' n U))
    (h' : Subsingleton (S.X₂.H' (n + 1) U)) (x : S.X₃.H' n U) :
    shiftEquiv hS n U h h' x = connecting hS n U x := rfl
noncomputable def connecting₀ (U : C) : S.X₃.obj.obj (op U) →+ S.X₁.H' 1 U :=
  (connecting hS 0 U).comp (sectionsEquiv S.X₃ U).symm.toAddMonoidHom
lemma connecting₀_apply (U : C) (s : S.X₃.obj.obj (op U)) :
    connecting₀ hS U s = connecting hS 0 U ((sectionsEquiv S.X₃ U).symm s) := rfl
lemma exact_app_connecting₀ (U : C) :
    Function.Exact (S.g.hom.app (op U)) (connecting₀ hS U) := by
  intro s
  obtain ⟨x, rfl⟩ := (sectionsEquiv S.X₃ U).surjective s
  rw [connecting₀_apply, AddEquiv.symm_apply_apply, exact_map_connecting hS 0 U x]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨sectionsEquiv S.X₂ U y, (sectionsEquiv_map S.g U y).symm⟩
  · rintro ⟨t, ht⟩
    obtain ⟨y, rfl⟩ := (sectionsEquiv S.X₂ U).surjective t
    exact ⟨y, (sectionsEquiv S.X₃ U).injective ((sectionsEquiv_map S.g U y).trans ht)⟩
lemma connecting₀_surjective (U : C) (h : Subsingleton (S.X₂.H' 1 U)) :
    Function.Surjective (connecting₀ hS U) :=
  (connecting_surjective hS 0 U h).comp (sectionsEquiv S.X₃ U).symm.surjective
lemma ker_connecting₀ (U : C) : (connecting₀ hS U).ker = (S.g.hom.app (op U)).hom.range :=
  AddSubgroup.ext fun s ↦ exact_app_connecting₀ hS U s
noncomputable def cokerEquiv (U : C) (h : Subsingleton (S.X₂.H' 1 U)) :
    (S.X₃.obj.obj (op U) ⧸ (S.g.hom.app (op U)).hom.range) ≃+ S.X₁.H' 1 U :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_connecting₀ hS U).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (connecting₀_surjective hS U h))
@[simp]
lemma cokerEquiv_mk (U : C) (h : Subsingleton (S.X₂.H' 1 U)) (s : S.X₃.obj.obj (op U)) :
    cokerEquiv hS U h (QuotientAddGroup.mk s) = connecting₀ hS U s := rfl
end Shift
end Site
section Injective
variable {A : Type u} [Category.{v} A] [Abelian A]
noncomputable abbrev injectiveShortComplex [EnoughInjectives A] (F : A) : ShortComplex A :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
end Injective
section Space
variable {X : TopCat.{u}}
open CategoryTheory Abelian Opposite Limits TopologicalSpace in
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] in
variable {J} in
lemma freeSheafHomEquiv_eq_yonedaEquiv (U : C) (F : Sheaf J AddCommGrpCat.{v})
    (h : _root_.GlobalTheory.Flasque.freeSheaf J U ⟶ F) :
    _root_.GlobalTheory.Flasque.freeSheafHomEquiv U F h = yonedaEquiv
      (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _)
        ((sheafificationAdjunction J _).homEquiv _ _ h)) := rfl
open CategoryTheory Abelian Opposite Limits TopologicalSpace in
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] in
variable {J} in
lemma freeSheafHomEquiv_freeSheafMap_comp' {V U : C} (i : V ⟶ U) (F : Sheaf J AddCommGrpCat.{v})
    (h : _root_.GlobalTheory.Flasque.freeSheaf J U ⟶ F) :
    _root_.GlobalTheory.Flasque.freeSheafHomEquiv V F (_root_.GlobalTheory.Flasque.freeSheafMap J i ≫ h) =
      F.obj.map i.op (_root_.GlobalTheory.Flasque.freeSheafHomEquiv U F h) := by
  rw [freeSheafHomEquiv_eq_yonedaEquiv, freeSheafHomEquiv_eq_yonedaEquiv,
    Adjunction.homEquiv_naturality_left]
  erw [Adjunction.homEquiv_naturality_left]
  rw [← yonedaEquiv_naturality]
  rfl
open CategoryTheory Abelian Opposite Limits TopologicalSpace in
variable {X : TopCat.{u}} in

theorem _root_.GlobalTheory.Flasque.isFlasque_of_injective (I : TopCat.Sheaf AddCommGrpCat.{u} X) [hI : Injective I] :
    I.IsFlasque := by
  let I' : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} := I
  haveI : Injective I' := hI
  refine ⟨fun {U V} i => ?_⟩
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  let g : _root_.GlobalTheory.Flasque.freeSheaf _ (unop V) ⟶ I' :=
    (_root_.GlobalTheory.Flasque.freeSheafHomEquiv (unop V) I').symm s
  let h : _root_.GlobalTheory.Flasque.freeSheaf _ (unop U) ⟶ I' :=
    Injective.factorThru g (_root_.GlobalTheory.Flasque.freeSheafMap _ i.unop)
  refine ⟨_root_.GlobalTheory.Flasque.freeSheafHomEquiv (unop U) I' h, ?_⟩
  have key := freeSheafHomEquiv_freeSheafMap_comp' i.unop I' h
  rw [Injective.comp_factorThru] at key
  simpa [g] using key.symm
instance isFlasque_injectiveShortComplex_X₂ (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (injectiveShortComplex F).X₂.IsFlasque :=
  isFlasque_of_injective _
variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
end Space
end Flasque
end GlobalTheory


