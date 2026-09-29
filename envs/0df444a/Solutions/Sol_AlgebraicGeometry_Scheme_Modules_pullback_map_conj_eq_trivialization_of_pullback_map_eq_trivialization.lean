-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.pullback_map_conj_eq_trivialization_of_pullback_map_eq_trivialization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/8023bab0-b069-5b5b-a6aa-15734d4aff47

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_pullback_map_conj_eq_trivialization_of_pullback_map_eq_trivialization

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace BenchR_RR

lemma homEquiv_conjugateEquiv {C D : Type*} [Category C] [Category D] {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁) {c : C} {d : D} (h : L₁.obj c ⟶ d) :
    adj₂.homEquiv c d (α.app c ≫ h) = adj₁.homEquiv c d h ≫ (conjugateEquiv adj₁ adj₂ α).app d := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp]
  have e1 := unit_conjugateEquiv adj₁ adj₂ α c
  have e2 := (conjugateEquiv adj₁ adj₂ α).naturality h
  calc adj₂.unit.app c ≫ R₂.map (α.app c) ≫ R₂.map h
      = (adj₂.unit.app c ≫ R₂.map (α.app c)) ≫ R₂.map h := (Category.assoc _ _ _).symm
    _ = (adj₁.unit.app c ≫ (conjugateEquiv adj₁ adj₂ α).app (L₁.obj c)) ≫ R₂.map h := by rw [e1]
    _ = adj₁.unit.app c ≫ ((conjugateEquiv adj₁ adj₂ α).app (L₁.obj c) ≫ R₂.map h) := Category.assoc _ _ _
    _ = adj₁.unit.app c ≫ (R₁.map h ≫ (conjugateEquiv adj₁ adj₂ α).app d) := by erw [e2]
    _ = (adj₁.unit.app c ≫ R₁.map h) ≫ (conjugateEquiv adj₁ adj₂ α).app d := (Category.assoc _ _ _).symm

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

lemma pullbackComp_inv_app_pullbackUnitIso :
    (Scheme.Modules.pullbackComp f g).inv.app _ ≫
      (Scheme.Modules.pullback f).map (Scheme.Modules.pullbackUnitIso g).hom ≫ (Scheme.Modules.pullbackUnitIso f).hom =
      (Scheme.Modules.pullbackUnitIso (f ≫ g)).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  rw [homEquiv_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)) (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv]
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_homEquiv]
  dsimp only
  first
    | simp only [Equiv.trans_apply]
    | change ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
          ((Scheme.Modules.pullback f).map (Scheme.Modules.pullbackUnitIso g).hom ≫
            (Scheme.Modules.pullbackUnitIso f).hom))) ≫ _ = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]

  erw [SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit,
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit,
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardComp_hom_app_app, CategoryTheory.comp_apply, Category.comp_id]
  first
    | rfl
    | (change f.app _ (g.app _ x) = (f ≫ g).app _ x; rw [Scheme.comp_app]; rfl)
    | done

section coh

p2m_open "AlgebraicGeometry.Scheme.Modules"

variable {T' T A' : Scheme.{u}}

lemma pullbackCongr_hom_app_eq {q q' : T ⟶ A'} (H : q = q') (N : A'.Modules) :
    (pullbackCongr H).hom.app N = eqToHom (by rw [H]) := by
  subst H; simp [pullbackCongr]

lemma pullbackCongr_inv_app_eq {q q' : T ⟶ A'} (H : q = q') (N : A'.Modules) :
    (pullbackCongr H).inv.app N = eqToHom (by rw [H]) := by
  subst H; simp [pullbackCongr]

lemma assoc_app {W : Scheme.{u}} (f : T' ⟶ T) (g : T ⟶ W) (h : W ⟶ A') (N : A'.Modules) :
    (Scheme.Modules.pullback f).map ((pullbackComp g h).inv.app N) ≫
      (pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj N) ≫ (pullbackComp (f ≫ g) h).hom.app N =
    (pullbackComp f (g ≫ h)).hom.app N ≫ eqToHom (by rw [Category.assoc]) := by
  have := NatTrans.congr_app (pseudofunctor_associativity f g h) N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Category.id_comp, eqToHom_app] at this
  exact (Iso.inv_comp_eq ((pullbackComp f (g ≫ h)).app N)).1 this

end coh

section coh2

p2m_open "AlgebraicGeometry.Scheme.Modules"

variable {T' T A' : Scheme.{u}}

lemma pullbackCongr_refl {q : T ⟶ A'} : pullbackCongr (rfl : q = q) = Iso.refl _ := rfl

lemma congr_comp {W : Scheme.{u}} {q q' : T ⟶ W} (H : q = q') (ι : W ⟶ A') (N : A'.Modules) :
    (pullbackCongr H).hom.app ((Scheme.Modules.pullback ι).obj N) =
      (pullbackComp q ι).hom.app N ≫ eqToHom (by rw [H]) ≫ (pullbackComp q' ι).inv.app N := by
  subst H
  simp only [pullbackCongr, eqToIso_refl, eqToHom_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  exact ((pullbackComp q ι).hom_inv_id_app N).symm

lemma map_congr (lam : T' ⟶ T) {q q' : T ⟶ A'} (H : q = q') (N : A'.Modules) :
    (Scheme.Modules.pullback lam).map ((pullbackCongr H).hom.app N) =
      (pullbackComp lam q).hom.app N ≫ eqToHom (by rw [H]) ≫ (pullbackComp lam q').inv.app N := by
  subst H
  simp only [pullbackCongr, eqToIso_refl, eqToHom_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    CategoryTheory.Functor.map_id]
  first
    | exact ((pullbackComp lam q).hom_inv_id_app N).symm
    | (erw [CategoryTheory.Functor.map_id]; exact ((pullbackComp lam q).hom_inv_id_app N).symm)

lemma assoc_app' {W : Scheme.{u}} (f : T' ⟶ T) (g : T ⟶ W) (h : W ⟶ A') (N : A'.Modules) :
    (pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj N) ≫
      (Scheme.Modules.pullback f).map ((pullbackComp g h).hom.app N) =
    (pullbackComp (f ≫ g) h).hom.app N ≫ eqToHom (by rw [Category.assoc]) ≫ (pullbackComp f (g ≫ h)).inv.app N := by
  have h1 := assoc_app f g h N

  let α : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj N)) ≅
      (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback (g ≫ h)).obj N) :=
    (Scheme.Modules.pullback f).mapIso ((pullbackComp g h).app N)
  let β : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj N)) ≅
      (Scheme.Modules.pullback (f ≫ g)).obj ((Scheme.Modules.pullback h).obj N) :=
    (pullbackComp f g).app ((Scheme.Modules.pullback h).obj N)
  let γ : (Scheme.Modules.pullback (f ≫ g)).obj ((Scheme.Modules.pullback h).obj N) ≅
      (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj N := (pullbackComp (f ≫ g) h).app N
  let δ : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback (g ≫ h)).obj N) ≅
      (Scheme.Modules.pullback (f ≫ g ≫ h)).obj N := (pullbackComp f (g ≫ h)).app N
  let η : (Scheme.Modules.pullback (f ≫ g ≫ h)).obj N ≅ (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj N :=
    eqToIso (by rw [Category.assoc])
  have h2 : α.symm ≪≫ β ≪≫ γ = δ ≪≫ η := Iso.ext h1
  have h3 : β.symm ≪≫ α = γ ≪≫ η.symm ≪≫ δ.symm := by
    have h2' : β ≪≫ γ = α ≪≫ δ ≪≫ η := by
      rw [← h2]; simp
    calc β.symm ≪≫ α = β.symm ≪≫ α ≪≫ (δ ≪≫ η) ≪≫ (δ ≪≫ η).symm := by simp
      _ = β.symm ≪≫ (α ≪≫ δ ≪≫ η) ≪≫ (η.symm ≪≫ δ.symm) := by simp
      _ = β.symm ≪≫ (β ≪≫ γ) ≪≫ (η.symm ≪≫ δ.symm) := by rw [h2']
      _ = γ ≪≫ η.symm ≪≫ δ.symm := by simp
  have h4 := congrArg Iso.hom h3
  simpa [α, β, γ, δ, η, eqToIso] using h4

end coh2

section coh3

p2m_open "AlgebraicGeometry.Scheme.Modules"

variable {T' T A' : Scheme.{u}}

lemma assoc_app'' {W : Scheme.{u}} (f : T' ⟶ T) (g : T ⟶ W) (h : W ⟶ A') (N : A'.Modules) :
    (Scheme.Modules.pullback f).map ((pullbackComp g h).inv.app N) =
      (pullbackComp f (g ≫ h)).hom.app N ≫ eqToHom (by rw [Category.assoc]) ≫ (pullbackComp (f ≫ g) h).inv.app N ≫
        (pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj N) := by
  have h1 := assoc_app f g h N
  let α : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj N)) ≅
      (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback (g ≫ h)).obj N) :=
    (Scheme.Modules.pullback f).mapIso ((pullbackComp g h).app N)
  let β : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj N)) ≅
      (Scheme.Modules.pullback (f ≫ g)).obj ((Scheme.Modules.pullback h).obj N) :=
    (pullbackComp f g).app ((Scheme.Modules.pullback h).obj N)
  let γ : (Scheme.Modules.pullback (f ≫ g)).obj ((Scheme.Modules.pullback h).obj N) ≅
      (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj N := (pullbackComp (f ≫ g) h).app N
  let δ : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback (g ≫ h)).obj N) ≅
      (Scheme.Modules.pullback (f ≫ g ≫ h)).obj N := (pullbackComp f (g ≫ h)).app N
  let η : (Scheme.Modules.pullback (f ≫ g ≫ h)).obj N ≅ (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj N :=
    eqToIso (by rw [Category.assoc])
  have h2 : α.symm ≪≫ β ≪≫ γ = δ ≪≫ η := Iso.ext h1
  have h3 : α.symm = δ ≪≫ η ≪≫ γ.symm ≪≫ β.symm := by
    calc α.symm = (α.symm ≪≫ β ≪≫ γ) ≪≫ (γ.symm ≪≫ β.symm) := by simp
      _ = (δ ≪≫ η) ≪≫ (γ.symm ≪≫ β.symm) := by rw [h2]
      _ = δ ≪≫ η ≪≫ γ.symm ≪≫ β.symm := by simp
  have h4 := congrArg Iso.hom h3
  simpa [α, β, γ, δ, η, eqToIso] using h4

end coh3

section rules

p2m_open "AlgebraicGeometry.Scheme.Modules"

variable {T' T A' : Scheme.{u}}

lemma mapIso_pullbackComp_app {W : Scheme.{u}} (f : T' ⟶ T) (g : T ⟶ W) (h : W ⟶ A') (N : A'.Modules) :
    (Scheme.Modules.pullback f).mapIso (X := (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj N))
      (Y := (Scheme.Modules.pullback (g ≫ h)).obj N) ((pullbackComp g h).app N) =
      (pullbackComp f g).app ((Scheme.Modules.pullback h).obj N) ≪≫ (pullbackComp (f ≫ g) h).app N ≪≫
        eqToIso (by rw [Category.assoc]) ≪≫ ((pullbackComp f (g ≫ h)).app N).symm := by
  have h1 := assoc_app f g h N
  let α : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj N)) ≅
      (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback (g ≫ h)).obj N) :=
    (Scheme.Modules.pullback f).mapIso ((pullbackComp g h).app N)
  let β : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj N)) ≅
      (Scheme.Modules.pullback (f ≫ g)).obj ((Scheme.Modules.pullback h).obj N) :=
    (pullbackComp f g).app ((Scheme.Modules.pullback h).obj N)
  let γ : (Scheme.Modules.pullback (f ≫ g)).obj ((Scheme.Modules.pullback h).obj N) ≅
      (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj N := (pullbackComp (f ≫ g) h).app N
  let δ : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback (g ≫ h)).obj N) ≅
      (Scheme.Modules.pullback (f ≫ g ≫ h)).obj N := (pullbackComp f (g ≫ h)).app N
  let η : (Scheme.Modules.pullback (f ≫ g ≫ h)).obj N ≅ (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj N :=
    eqToIso (by rw [Category.assoc])
  have h2 : α.symm ≪≫ β ≪≫ γ = δ ≪≫ η := Iso.ext h1
  have h3 : α = β ≪≫ γ ≪≫ η.symm ≪≫ δ.symm := by
    calc α = α ≪≫ (δ ≪≫ η) ≪≫ (η.symm ≪≫ δ.symm) := by simp
      _ = α ≪≫ (α.symm ≪≫ β ≪≫ γ) ≪≫ (η.symm ≪≫ δ.symm) := by rw [h2]
      _ = β ≪≫ γ ≪≫ η.symm ≪≫ δ.symm := by simp
  have h5 : η.symm = eqToIso (by rw [Category.assoc]) := rfl
  rw [h5] at h3
  exact h3

lemma congr_app_comp {W : Scheme.{u}} {q q' : T ⟶ W} (H : q = q') (ι : W ⟶ A') (N : A'.Modules) :
    (pullbackCongr H).app ((Scheme.Modules.pullback ι).obj N) =
      (pullbackComp q ι).app N ≪≫ eqToIso (by rw [H]) ≪≫ ((pullbackComp q' ι).app N).symm := by
  subst H
  ext : 1
  simp only [pullbackCongr, eqToIso_refl, Iso.trans_hom, Iso.app_hom, Iso.refl_hom, NatTrans.id_app,
    Iso.symm_hom, Iso.app_inv, Category.id_comp]
  exact ((pullbackComp q ι).hom_inv_id_app N).symm

lemma mapIso_congr_app (lam : T' ⟶ T) {q q' : T ⟶ A'} (H : q = q') (N : A'.Modules) :
    (Scheme.Modules.pullback lam).mapIso ((pullbackCongr H).app N) =
      (pullbackComp lam q).app N ≪≫ eqToIso (by rw [H]) ≪≫ ((pullbackComp lam q').app N).symm := by
  subst H
  ext : 1
  simp only [pullbackCongr, eqToIso_refl, Iso.trans_hom, Iso.app_hom, Iso.refl_hom, NatTrans.id_app,
    Iso.symm_hom, Iso.app_inv, Category.id_comp, Functor.mapIso_hom]
  first
    | exact ((pullbackComp lam q).hom_inv_id_app N).symm
    | (erw [CategoryTheory.Functor.map_id]; exact ((pullbackComp lam q).hom_inv_id_app N).symm)

lemma congr_app_eqToIso {q q' : T ⟶ A'} (H : q = q') (N : A'.Modules) :
    (pullbackCongr H).app N = eqToIso (by rw [H]) := by
  subst H; ext : 1; simp [pullbackCongr]

lemma mapIso_mapIso (lam : T' ⟶ T) (p : T ⟶ A') {N N' : A'.Modules} (τ : N ≅ N') :
    (Scheme.Modules.pullback lam).mapIso ((Scheme.Modules.pullback p).mapIso τ) =
      (pullbackComp lam p).app N ≪≫ (Scheme.Modules.pullback (lam ≫ p)).mapIso τ ≪≫ ((pullbackComp lam p).app N').symm := by
  ext : 1
  have := (pullbackComp lam p).hom.naturality τ.hom
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom]
  rw [← Category.assoc, ← this]
  simp only [Functor.comp_map, Category.assoc]
  first
    | (rw [Iso.hom_inv_id_app, Category.comp_id])
    | (erw [Iso.hom_inv_id_app]; erw [Category.comp_id])

lemma mapIso_pullbackUnitIso (f : T' ⟶ T) (g : T ⟶ A') :
    (Scheme.Modules.pullback f).mapIso (pullbackUnitIso g) =
      (pullbackComp f g).app _ ≪≫ pullbackUnitIso (f ≫ g) ≪≫ (pullbackUnitIso f).symm := by
  have h1 := pullbackComp_inv_app_pullbackUnitIso f g
  let α : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj (SheafOfModules.unit A'.ringCatSheaf)) ≅
      (Scheme.Modules.pullback f).obj (SheafOfModules.unit T.ringCatSheaf) :=
    (Scheme.Modules.pullback f).mapIso (pullbackUnitIso g)
  let β : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj (SheafOfModules.unit A'.ringCatSheaf)) ≅
      (Scheme.Modules.pullback (f ≫ g)).obj (SheafOfModules.unit A'.ringCatSheaf) := (pullbackComp f g).app _
  let γ : (Scheme.Modules.pullback (f ≫ g)).obj (SheafOfModules.unit A'.ringCatSheaf) ≅
      SheafOfModules.unit T'.ringCatSheaf := pullbackUnitIso (f ≫ g)
  let δ : (Scheme.Modules.pullback f).obj (SheafOfModules.unit T.ringCatSheaf) ≅ SheafOfModules.unit T'.ringCatSheaf :=
    pullbackUnitIso f
  have h2 : β.symm ≪≫ α ≪≫ δ = γ := Iso.ext h1
  have h3 : α = β ≪≫ γ ≪≫ δ.symm := by
    calc α = β ≪≫ (β.symm ≪≫ α ≪≫ δ) ≪≫ δ.symm := by simp
      _ = β ≪≫ γ ≪≫ δ.symm := by rw [h2]
  exact h3

end rules

section core

p2m_open "AlgebraicGeometry.Scheme.Modules"

variable {B A Y Y₂ T T₂ : Scheme.{u}} (e : B ⟶ A) (ι : Y ⟶ A)
  (ε : T ⟶ Y) (p : T ⟶ B) (hp : ε ≫ ι = p ≫ e)
  (ε₂ : T₂ ⟶ Y₂) (j : Y₂ ⟶ Y) (lam : T₂ ⟶ T) (hlam : ε₂ ≫ j = lam ≫ ε)
  (hp₂ : ε₂ ≫ j ≫ ι = (lam ≫ p) ≫ e)

noncomputable abbrev triv {T Y : Scheme.{u}} (ε : T ⟶ Y) (ι : Y ⟶ A) (p : T ⟶ B) (hp : ε ≫ ι = p ≫ e)
    (N : A.Modules) (t : (Scheme.Modules.pullback e).obj N ≅ SheafOfModules.unit B.ringCatSheaf) :
    (Scheme.Modules.pullback ε).obj ((Scheme.Modules.pullback ι).obj N) ≅
      SheafOfModules.unit T.ringCatSheaf :=
  (pullbackComp ε ι).app N ≪≫ (pullbackCongr hp).app N ≪≫ ((pullbackComp p e).app N).symm ≪≫
    (Scheme.Modules.pullback p).mapIso t ≪≫ pullbackUnitIso p

include hlam in
lemma core (N : A.Modules) (t : (Scheme.Modules.pullback e).obj N ≅ SheafOfModules.unit B.ringCatSheaf) :
    ((Scheme.Modules.pullback ε₂).mapIso ((pullbackComp j ι).app N)).symm ≪≫
      ((pullbackComp ε₂ j).app ((Scheme.Modules.pullback ι).obj N) ≪≫
        (pullbackCongr hlam).app ((Scheme.Modules.pullback ι).obj N) ≪≫
        ((pullbackComp lam ε).app ((Scheme.Modules.pullback ι).obj N)).symm) ≪≫
      (Scheme.Modules.pullback lam).mapIso (triv e ε ι p hp N t) ≪≫ pullbackUnitIso lam =
    triv e ε₂ (j ≫ ι) (lam ≫ p) hp₂ N t := by
  simp only [Functor.comp_obj, triv, Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_symm, Iso.symm_symm_eq,
    Iso.trans_assoc,
    mapIso_pullbackComp_app, congr_app_comp hlam, mapIso_congr_app lam hp, congr_app_eqToIso hp₂,
    mapIso_mapIso, mapIso_pullbackUnitIso, Iso.symm_self_id, Iso.self_symm_id, Iso.symm_self_id_assoc,
    Iso.self_symm_id_assoc, Iso.refl_trans, Iso.trans_refl]
  ext : 1
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv, eqToHom_trans, eqToHom_trans_assoc,
    Category.assoc]

end core

section more_rules

p2m_open "AlgebraicGeometry.Scheme.Modules"

variable {T A' : Scheme.{u}}

lemma mapIso_congr_nat {q q' : T ⟶ A'} (H : q = q') {N N' : A'.Modules} (ψ : N ≅ N') :
    (Scheme.Modules.pullback q).mapIso ψ =
      (pullbackCongr H).app N ≪≫ (Scheme.Modules.pullback q').mapIso ψ ≪≫ ((pullbackCongr H).app N').symm := by
  subst H
  ext : 1
  simp [pullbackCongr]

lemma congr_app_refl {q : T ⟶ A'} (N : A'.Modules) :
    (pullbackCongr (rfl : q = q)).app N = Iso.refl _ := by
  ext : 1
  simp [pullbackCongr]

end more_rules

end BenchR_RR

open BenchR_RR _root_.AlgebraicGeometry.Scheme.Modules in
theorem solution
    {B A Y Y₂ T T₂ : Scheme.{u}} (e : B ⟶ A) (ι : Y ⟶ A) (ι₂ : Y₂ ⟶ A)
    (ε : T ⟶ Y) (p : T ⟶ B) (hp : ε ≫ ι = p ≫ e)
    (ε₂ : T₂ ⟶ Y₂) (p₂ : T₂ ⟶ B) (hp₂ : ε₂ ≫ ι₂ = p₂ ≫ e)
    (j : Y₂ ⟶ Y) (hj : j ≫ ι = ι₂) (lam : T₂ ⟶ T) (hlam : ε₂ ≫ j = lam ≫ ε) (hlamp : lam ≫ p = p₂)
    (L M : A.Modules)
    (hLe : (Scheme.Modules.pullback e).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (hMe : (Scheme.Modules.pullback e).obj M ≅ SheafOfModules.unit B.ringCatSheaf)
    (φ : (Scheme.Modules.pullback ι).obj L ≅ (Scheme.Modules.pullback ι).obj M)
    (hφ : (Scheme.Modules.pullback ε).map φ.hom =
        ((Scheme.Modules.pullbackComp ε ι).app L ≪≫ (Scheme.Modules.pullbackCongr hp).app L ≪≫
            ((Scheme.Modules.pullbackComp p e).app L).symm ≪≫ (Scheme.Modules.pullback p).mapIso hLe ≪≫
            Scheme.Modules.pullbackUnitIso p).hom ≫
        ((Scheme.Modules.pullbackComp ε ι).app M ≪≫ (Scheme.Modules.pullbackCongr hp).app M ≪≫
            ((Scheme.Modules.pullbackComp p e).app M).symm ≪≫ (Scheme.Modules.pullback p).mapIso hMe ≪≫
            Scheme.Modules.pullbackUnitIso p).inv) :
    (Scheme.Modules.pullback ε₂).map
        (((Scheme.Modules.pullbackComp j ι).app L ≪≫ (Scheme.Modules.pullbackCongr hj).app L).symm ≪≫
          (Scheme.Modules.pullback j).mapIso φ ≪≫
          ((Scheme.Modules.pullbackComp j ι).app M ≪≫ (Scheme.Modules.pullbackCongr hj).app M)).hom =
      ((Scheme.Modules.pullbackComp ε₂ ι₂).app L ≪≫ (Scheme.Modules.pullbackCongr hp₂).app L ≪≫
          ((Scheme.Modules.pullbackComp p₂ e).app L).symm ≪≫ (Scheme.Modules.pullback p₂).mapIso hLe ≪≫
          Scheme.Modules.pullbackUnitIso p₂).hom ≫
      ((Scheme.Modules.pullbackComp ε₂ ι₂).app M ≪≫ (Scheme.Modules.pullbackCongr hp₂).app M ≪≫
          ((Scheme.Modules.pullbackComp p₂ e).app M).symm ≪≫ (Scheme.Modules.pullback p₂).mapIso hMe ≪≫
          Scheme.Modules.pullbackUnitIso p₂).inv := by
  subst hj
  subst hlamp
  have hφiso : (Scheme.Modules.pullback ε).mapIso φ = triv e ε ι p hp L hLe ≪≫ (triv e ε ι p hp M hMe).symm :=
    Iso.ext hφ
  have hnat := mapIso_mapIso lam ε φ
  rw [hφiso, Functor.mapIso_trans, Functor.mapIso_symm] at hnat

  have hφ2 : (Scheme.Modules.pullback (lam ≫ ε)).mapIso φ =
      ((pullbackComp lam ε).app ((Scheme.Modules.pullback ι).obj L)).symm ≪≫
        ((Scheme.Modules.pullback lam).mapIso (triv e ε ι p hp L hLe) ≪≫
          ((Scheme.Modules.pullback lam).mapIso (triv e ε ι p hp M hMe)).symm) ≪≫
        (pullbackComp lam ε).app ((Scheme.Modules.pullback ι).obj M) := by
    calc (Scheme.Modules.pullback (lam ≫ ε)).mapIso φ
        = ((pullbackComp lam ε).app ((Scheme.Modules.pullback ι).obj L)).symm ≪≫
            ((pullbackComp lam ε).app ((Scheme.Modules.pullback ι).obj L) ≪≫
              (Scheme.Modules.pullback (lam ≫ ε)).mapIso φ ≪≫
              ((pullbackComp lam ε).app ((Scheme.Modules.pullback ι).obj M)).symm) ≪≫
            (pullbackComp lam ε).app ((Scheme.Modules.pullback ι).obj M) := by simp
      _ = ((pullbackComp lam ε).app ((Scheme.Modules.pullback ι).obj L)).symm ≪≫
            ((Scheme.Modules.pullback lam).mapIso (triv e ε ι p hp L hLe) ≪≫
              ((Scheme.Modules.pullback lam).mapIso (triv e ε ι p hp M hMe)).symm) ≪≫
            (pullbackComp lam ε).app ((Scheme.Modules.pullback ι).obj M) := by rw [← hnat]
  have key : (Scheme.Modules.pullback ε₂).mapIso
        (((Scheme.Modules.pullbackComp j ι).app L ≪≫ (Scheme.Modules.pullbackCongr rfl).app L).symm ≪≫
          (Scheme.Modules.pullback j).mapIso φ ≪≫
          ((Scheme.Modules.pullbackComp j ι).app M ≪≫ (Scheme.Modules.pullbackCongr rfl).app M)) =
      triv e ε₂ (j ≫ ι) (lam ≫ p) hp₂ L hLe ≪≫ (triv e ε₂ (j ≫ ι) (lam ≫ p) hp₂ M hMe).symm := by
    rw [← core e ι ε p hp ε₂ j lam hlam hp₂ L hLe, ← core e ι ε p hp ε₂ j lam hlam hp₂ M hMe]
    simp only [congr_app_refl, Iso.trans_refl, Iso.refl_trans, Functor.comp_obj, Functor.mapIso_trans,
      Functor.mapIso_symm, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, mapIso_mapIso,
      mapIso_congr_nat hlam, hφ2, Iso.symm_self_id, Iso.self_symm_id, Iso.symm_self_id_assoc, Iso.self_symm_id_assoc]
  exact congrArg Iso.hom key

end S_AlgebraicGeometry_Scheme_Modules_pullback_map_conj_eq_trivialization_of_pullback_map_eq_trivialization
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_pullback_map_conj_eq_trivialization_of_pullback_map_eq_trivialization (solution)
