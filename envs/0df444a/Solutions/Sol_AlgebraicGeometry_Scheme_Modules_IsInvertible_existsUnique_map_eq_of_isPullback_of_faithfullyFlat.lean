-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.existsUnique_map_eq_of_isPullback_of_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/5b79b798-66da-5147-a586-8ce133eae897

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_map_eq_of_isPullback_of_faithfullyFlat

set_option autoImplicit false

universe u v v' u' w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace BenchQD3

section abstract

p2m_open "CategoryTheory.Pseudofunctor CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat"

variable {C : Type w} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {S X P : C} (p : X ⟶ S) (q₁ q₂ : P ⟶ X) (hP : IsPullback q₁ q₂ p p)

@[reassoc]
theorem catIso_hom_inv_app {A B : Cat.{v', u'}} {G H : A ⟶ B} (e : G ≅ H) (Z : A) :
    e.hom.toNatTrans.app Z ≫ e.inv.toNatTrans.app Z = 𝟙 _ := by
  rw [← Cat.Hom₂.comp_app, e.hom_inv_id]; rfl

theorem catIso_hom_inv_app_left {A B : Cat.{v', u'}} {G H : A ⟶ B} (e : G ≅ H) (Z : A) {W W' : B}
    (f : G.toFunctor.obj Z ⟶ W) (g : W ⟶ W') :
    e.hom.toNatTrans.app Z ≫ (e.inv.toNatTrans.app Z ≫ f) ≫ g = f ≫ g := by
  rw [← Category.assoc, ← Category.assoc, catIso_hom_inv_app, Category.id_comp]

theorem catIso_hom_inv_app_right {A B : Cat.{v', u'}} {G H : A ⟶ B} (e : G ≅ H) (Z : A) {W : B}
    (f : W ⟶ G.toFunctor.obj Z) :
    (f ≫ e.hom.toNatTrans.app Z) ≫ e.inv.toNatTrans.app Z = f := by
  rw [Category.assoc, catIso_hom_inv_app, Category.comp_id]

@[reassoc]
theorem catIso_inv_hom_app {A B : Cat.{v', u'}} {G H : A ⟶ B} (e : G ≅ H) (Z : A) :
    e.inv.toNatTrans.app Z ≫ e.hom.toNatTrans.app Z = 𝟙 _ := by
  rw [← Cat.Hom₂.comp_app, e.inv_hom_id]; rfl

set_option backward.defeqAttrib.useBackward true in
theorem comm_of_kernelPair {L M : F.obj (.mk (Opposite.op S))}
    (α : (F.map p.op.toLoc).toFunctor.obj L ⟶ (F.map p.op.toLoc).toFunctor.obj M)
    (H0 : (F.map q₁.op.toLoc).toFunctor.map α ≫
        (DescentData.ofObj (F := F) (f := fun _ : Unit => p) M).hom (q₂ ≫ p) (i₁ := ()) (i₂ := ()) q₁ q₂ hP.w rfl =
      (DescentData.ofObj (F := F) (f := fun _ : Unit => p) L).hom (q₂ ≫ p) (i₁ := ()) (i₂ := ()) q₁ q₂ hP.w rfl ≫
        (F.map q₂.op.toLoc).toFunctor.map α)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : Unit⦄ (f₁ f₂ : Y ⟶ X) (hf₁ : f₁ ≫ p = q) (hf₂ : f₂ ≫ p = q) :
    (F.map f₁.op.toLoc).toFunctor.map ((fun _ : Unit => α) i₁) ≫
        ((F.toDescentData (fun _ : Unit => p)).obj M).hom q (i₁ := i₁) (i₂ := i₂) f₁ f₂ hf₁ hf₂ =
      ((F.toDescentData (fun _ : Unit => p)).obj L).hom q (i₁ := i₁) (i₂ := i₂) f₁ f₂ hf₁ hf₂ ≫
        (F.map f₂.op.toLoc).toFunctor.map ((fun _ : Unit => α) i₂) := by
  obtain ⟨⟩ := i₁; obtain ⟨⟩ := i₂
  dsimp only [Pseudofunctor.toDescentData_obj]
  let l : Y ⟶ P := hP.lift f₁ f₂ (hf₁.trans hf₂.symm)
  have hl₁ : l ≫ q₁ = f₁ := hP.lift_fst _ _ _
  have hl₂ : l ≫ q₂ = f₂ := hP.lift_snd _ _ _
  have hq : l ≫ (q₂ ≫ p) = q := by rw [← Category.assoc, hl₂, hf₂]

  have E : ∀ (N : F.obj (.mk (Opposite.op S))),
      (DescentData.ofObj (F := F) (f := fun _ : Unit => p) N).hom q (i₁ := ()) (i₂ := ()) f₁ f₂ hf₁ hf₂ =
        (F.mapComp' q₁.op.toLoc l.op.toLoc f₁.op.toLoc (by rw [← hl₁]; rfl)).hom.toNatTrans.app _ ≫
          (F.map l.op.toLoc).toFunctor.map
            ((DescentData.ofObj (F := F) (f := fun _ : Unit => p) N).hom (q₂ ≫ p) (i₁ := ()) (i₂ := ()) q₁ q₂ hP.w rfl) ≫
          (F.mapComp' q₂.op.toLoc l.op.toLoc f₂.op.toLoc (by rw [← hl₂]; rfl)).inv.toNatTrans.app _ := by
    intro N
    rw [map_eq_pullHom _ l f₁ f₂ hl₁ hl₂,
      (DescentData.ofObj (F := F) (f := fun _ : Unit => p) N).pullHom_hom l (q₂ ≫ p) q hq q₁ q₂ hP.w rfl f₁ f₂ hl₁ hl₂]
    erw [catIso_hom_inv_app_left, catIso_hom_inv_app_right]
  erw [E M, E L]
  simp only [DescentData.ofObj_obj, Category.assoc]
  rw [← Category.assoc, F.mapComp'_hom_naturality q₁.op.toLoc l.op.toLoc f₁.op.toLoc _ α]

  refine (Category.assoc _ _ _).trans ?_
  refine congrArg (CategoryStruct.comp
    ((F.mapComp' q₁.op.toLoc l.op.toLoc f₁.op.toLoc (by rw [← hl₁]; rfl)).hom.toNatTrans.app
      ((F.map p.op.toLoc).toFunctor.obj L))) ?_
  have h1 : (F.map l.op.toLoc).toFunctor.map ((F.map q₁.op.toLoc).toFunctor.map α) ≫
      (F.map l.op.toLoc).toFunctor.map
        ((DescentData.ofObj (F := F) (f := fun _ : Unit => p) M).hom (q₂ ≫ p) (i₁ := ()) (i₂ := ()) q₁ q₂ hP.w rfl) =
      (F.map l.op.toLoc).toFunctor.map
        ((DescentData.ofObj (F := F) (f := fun _ : Unit => p) L).hom (q₂ ≫ p) (i₁ := ()) (i₂ := ()) q₁ q₂ hP.w rfl) ≫
      (F.map l.op.toLoc).toFunctor.map ((F.map q₂.op.toLoc).toFunctor.map α) := by
    rw [← Functor.map_comp, H0]
    exact Functor.map_comp _ _ _
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) h1).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg _ (F.mapComp'_inv_naturality q₂.op.toLoc l.op.toLoc f₂.op.toLoc _ α)

end abstract

section scheme

noncomputable abbrev FF := (Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁

theorem cat_eqToHom_app {A B : Cat.{u, u + 1}} {G H : A ⟶ B} (h : G = H) (Z : A) :
    (eqToHom h).toNatTrans.app Z = eqToHom (by rw [h]) := by
  subst h; rfl

theorem eqToHom_sandwich {D : Type (u + 1)} [Category.{u} D] {a b c d e : D} (A : a ⟶ b) (h₁ : b = c) (h₂ : c = d)
    (B : d ⟶ e) : (A ≫ eqToHom h₁) ≫ eqToHom h₂ ≫ B = A ≫ eqToHom (h₁.trans h₂) ≫ B := by
  simp

theorem ofObj_hom_eq {T T' Y : Scheme.{u}} (p : T' ⟶ T) (X : T.Modules)
    (q : Y ⟶ T) (f₁ f₂ : Y ⟶ T') (hf₁ : f₁ ≫ p = q) (hf₂ : f₂ ≫ p = q) :
    (Pseudofunctor.DescentData.ofObj (F := FF) (f := fun _ : Unit => p) X).hom q (i₁ := ()) (i₂ := ()) f₁ f₂ hf₁ hf₂ =
      (Scheme.Modules.pullbackComp f₁ p).hom.app X ≫ (Scheme.Modules.pullbackCongr (hf₁.trans hf₂.symm)).hom.app X ≫
        (Scheme.Modules.pullbackComp f₂ p).inv.app X := by
  subst hf₂
  dsimp only [Pseudofunctor.DescentData.ofObj, Pseudofunctor.mapComp']
  simp only [Iso.trans_hom, Iso.trans_inv, PrelaxFunctor.map₂Iso_hom, PrelaxFunctor.map₂Iso_inv,
    eqToIso.hom, eqToIso.inv, PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.comp_app]
  rw [cat_eqToHom_app, cat_eqToHom_app]
  have e1 : (FF.mapComp p.op.toLoc f₁.op.toLoc).inv.toNatTrans.app X = (Scheme.Modules.pullbackComp f₁ p).hom.app X := rfl
  have e2 : (FF.mapComp p.op.toLoc f₂.op.toLoc).hom.toNatTrans.app X = (Scheme.Modules.pullbackComp f₂ p).inv.app X := rfl
  rw [e1, e2]
  simp only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app]
  exact eqToHom_sandwich _ _ _ _

theorem flat_specMap {S S' : Type u} [CommRing S] [CommRing S'] [Algebra S S'] [Module.Flat S S'] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap S S'))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  show (algebraMap S S').Flat
  have h : (algebraMap S S').toAlgebra = ‹Algebra S S'› := Algebra.algebra_ext _ _ fun _ => rfl
  unfold RingHom.Flat
  rw [h]; infer_instance

theorem FF_map_map {T T' : Scheme.{u}} (p : T' ⟶ T) {L M : T.Modules} (β : L ⟶ M) :
    (FF.map p.op.toLoc).toFunctor.map β = (Scheme.Modules.pullback p).map β := rfl

theorem toDescentData_map_hom_eq {T T' : Scheme.{u}} (p : T' ⟶ T) {L M : T.Modules} (β : L ⟶ M) :
    ((FF.toDescentData (fun _ : Unit => p)).map β).hom () = (Scheme.Modules.pullback p).map β := rfl

theorem H0_of_hα {T T' T'' : Scheme.{u}} (p : T' ⟶ T) (q₁ q₂ : T'' ⟶ T') (hq : q₁ ≫ p = q₂ ≫ p)
    (L M : T.Modules) (α : (Scheme.Modules.pullback p).obj L ⟶ (Scheme.Modules.pullback p).obj M)
    (hα : (Scheme.Modules.pullback q₁).map α ≫ ((Scheme.Modules.pullbackComp q₁ p).app M).hom ≫
        ((Scheme.Modules.pullbackCongr hq).app M).hom ≫ ((Scheme.Modules.pullbackComp q₂ p).app M).inv =
      ((Scheme.Modules.pullbackComp q₁ p).app L).hom ≫ ((Scheme.Modules.pullbackCongr hq).app L).hom ≫
        ((Scheme.Modules.pullbackComp q₂ p).app L).inv ≫ (Scheme.Modules.pullback q₂).map α) :
    (FF.map q₁.op.toLoc).toFunctor.map α ≫
      (Pseudofunctor.DescentData.ofObj (F := FF) (f := fun _ : Unit => p) M).hom (q₂ ≫ p) (i₁ := ()) (i₂ := ()) q₁ q₂ hq rfl =
      (Pseudofunctor.DescentData.ofObj (F := FF) (f := fun _ : Unit => p) L).hom (q₂ ≫ p) (i₁ := ()) (i₂ := ()) q₁ q₂ hq rfl ≫
        (FF.map q₂.op.toLoc).toFunctor.map α := by
  rw [ofObj_hom_eq, ofObj_hom_eq]
  have h := hα
  simp only [Iso.app_hom, Iso.app_inv] at h
  exact h

theorem descend_hom {T T' T'' : Scheme.{u}} (p : T' ⟶ T) [IsAffineHom p] [Flat p] [Surjective p]
    (q₁ q₂ : T'' ⟶ T') (hPB : IsPullback q₁ q₂ p p)
    (L M : T.Modules) (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (α : (Scheme.Modules.pullback p).obj L ⟶ (Scheme.Modules.pullback p).obj M)
    (H0 : (FF.map q₁.op.toLoc).toFunctor.map α ≫
      (Pseudofunctor.DescentData.ofObj (F := FF) (f := fun _ : Unit => p) M).hom (q₂ ≫ p) (i₁ := ()) (i₂ := ()) q₁ q₂ hPB.w rfl =
      (Pseudofunctor.DescentData.ofObj (F := FF) (f := fun _ : Unit => p) L).hom (q₂ ≫ p) (i₁ := ()) (i₂ := ()) q₁ q₂ hPB.w rfl ≫
        (FF.map q₂.op.toLoc).toFunctor.map α) :
    ∃! β : L ⟶ M, (Scheme.Modules.pullback p).map β = α := by
  let Φ : (FF.toDescentData (fun _ : Unit => p)).obj L ⟶ (FF.toDescentData (fun _ : Unit => p)).obj M :=
    { hom := fun _ => α
      comm := comm_of_kernelPair FF p q₁ q₂ hPB α H0 }
  have bij := AlgebraicGeometry.Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
    p L M hL hM
  obtain ⟨β, hβ⟩ := bij.2 Φ
  have hΦ : Pseudofunctor.DescentData.Hom.hom Φ () = α := rfl
  refine ⟨β, ?_, fun β' hβ' => bij.1 ?_⟩
  · show (Scheme.Modules.pullback p).map β = α
    rw [← toDescentData_map_hom_eq, hβ, hΦ]
  · show (FF.toDescentData fun _ : Unit => p).map β' = (FF.toDescentData fun _ : Unit => p).map β
    rw [hβ]
    ext i
    obtain ⟨⟩ := i
    rw [toDescentData_map_hom_eq, hΦ]
    exact hβ'

theorem main
    {S S' : Type u} [CommRing S] [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {T T' T'' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S'))
    (p : T' ⟶ T) (hp : IsPullback p t' t (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (t'' : T'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (q₁ q₂ : T'' ⟶ T')
    (hq₁ : IsPullback q₁ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S'))))
    (hq₂ : IsPullback q₂ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (hq : q₁ ≫ p = q₂ ≫ p)
    (L M : T.Modules) (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (α : (Scheme.Modules.pullback p).obj L ⟶ (Scheme.Modules.pullback p).obj M)
    (hα : (Scheme.Modules.pullback q₁).map α ≫ ((Scheme.Modules.pullbackComp q₁ p).app M).hom ≫
        ((Scheme.Modules.pullbackCongr hq).app M).hom ≫ ((Scheme.Modules.pullbackComp q₂ p).app M).inv =
      ((Scheme.Modules.pullbackComp q₁ p).app L).hom ≫ ((Scheme.Modules.pullbackCongr hq).app L).hom ≫
        ((Scheme.Modules.pullbackComp q₂ p).app L).inv ≫ (Scheme.Modules.pullback q₂).map α) :
    ∃! β : L ⟶ M, (Scheme.Modules.pullback p).map β = α := by
  let ι := Spec.map (CommRingCat.ofHom (algebraMap S S'))
  let ιL := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S'))
  let ιR := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)
  haveI : Flat ι := flat_specMap
  haveI : Surjective ι := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩
  haveI : IsAffineHom ι := inferInstance
  haveI : Flat p := MorphismProperty.of_isPullback hp.flip inferInstance
  haveI : Surjective p := MorphismProperty.of_isPullback hp.flip inferInstance
  haveI : IsAffineHom p := MorphismProperty.of_isPullback hp.flip inferInstance
  have hSpec : IsPullback ιL ιR ι ι :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct S S' S')
  have hbig : IsPullback (t'' ≫ ιR) q₁ ι (t' ≫ ι) := hq₁.flip.paste_horiz hSpec.flip
  have hbig' : IsPullback (q₂ ≫ t') q₁ ι (p ≫ t) := by rw [hq₂.w, hp.w]; exact hbig
  have hPB : IsPullback q₁ q₂ p p := (IsPullback.of_right hbig' hq.symm hp.flip).flip
  exact descend_hom p q₁ q₂ hPB L M hL hM α (H0_of_hα p q₁ q₂ hq L M α hα)

end scheme

end BenchQD3

theorem solution
    {S S' : Type u} [CommRing S] [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {T T' T'' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S'))
    (p : T' ⟶ T) (hp : IsPullback p t' t (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (t'' : T'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (q₁ q₂ : T'' ⟶ T')
    (hq₁ : IsPullback q₁ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S'))))
    (hq₂ : IsPullback q₂ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (hq : q₁ ≫ p = q₂ ≫ p)
    (L M : T.Modules) (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (α : (Scheme.Modules.pullback p).obj L ⟶ (Scheme.Modules.pullback p).obj M)
    (hα : (Scheme.Modules.pullback q₁).map α ≫ ((Scheme.Modules.pullbackComp q₁ p).app M).hom ≫
        ((Scheme.Modules.pullbackCongr hq).app M).hom ≫ ((Scheme.Modules.pullbackComp q₂ p).app M).inv =
      ((Scheme.Modules.pullbackComp q₁ p).app L).hom ≫ ((Scheme.Modules.pullbackCongr hq).app L).hom ≫
        ((Scheme.Modules.pullbackComp q₂ p).app L).inv ≫ (Scheme.Modules.pullback q₂).map α) :
    ∃! β : L ⟶ M, (Scheme.Modules.pullback p).map β = α :=
  BenchQD3.main t t' p hp t'' q₁ q₂ hq₁ hq₂ hq L M hL hM α hα

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_map_eq_of_isPullback_of_faithfullyFlat
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_map_eq_of_isPullback_of_faithfullyFlat (solution)
