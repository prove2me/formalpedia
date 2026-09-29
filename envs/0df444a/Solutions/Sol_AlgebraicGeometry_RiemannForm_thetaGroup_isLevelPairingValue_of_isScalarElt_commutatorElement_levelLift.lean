-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.thetaGroup.isLevelPairingValue_of_isScalarElt_commutatorElement_levelLift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/c7dacd41-33da-534e-abdf-d787ec9c3404

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_AlgebraicGeometry_ThetaGroup
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_RiemannForm_schemeNsmul_mul_and_translation_comp_schemeNsmul
import Theorems.Thm_AlgebraicGeometry_RiemannForm_isConstScalar_pullback_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_isLevelPairingValue_of_isScalarElt_commutatorElement_levelLift

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm

open scoped commutatorElement

namespace ThetaE165

universe u
set_option backward.isDefEq.respectTransparency false

p2m_open "CategoryTheory.Pseudofunctor.CoGrothendieck"

section coh
variable {X Y Z T' : Scheme.{u}}

theorem assoc_app (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T') (M : T'.Modules)
    (p : (Scheme.Modules.pullback (f ≫ g ≫ h)).obj M = (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj M) :
    (Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M) ≫
        (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
          (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M = eqToHom p := by
  have := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity f g h) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, eqToHom_app] at this
  exact this

@[reassoc]
theorem assoc_app₄ (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T') (M : T'.Modules)
    (p : (Scheme.Modules.pullback (f ≫ g ≫ h)).obj M = (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj M) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M) ≫
        (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) =
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M ≫ eqToHom p ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).inv.app M := by
  rw [← assoc_app f g h M p]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app, Iso.inv_hom_id_app_assoc,
    Functor.comp_obj, Category.comp_id]

@[reassoc]
theorem assoc_app₃ (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T') (M : T'.Modules)
    (q : (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj M = (Scheme.Modules.pullback (f ≫ g ≫ h)).obj M) :
    (Scheme.Modules.pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj M) ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) =
      (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M ≫ eqToHom q ≫
        (Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M := by
  have h4 := assoc_app₄ f g h M q.symm
  have hiso : ((Scheme.Modules.pullback f).mapIso ((Scheme.Modules.pullbackComp g h).app M)).symm ≪≫
      (Scheme.Modules.pullbackComp f g).app ((Scheme.Modules.pullback h).obj M) =
      (Scheme.Modules.pullbackComp f (g ≫ h)).app M ≪≫ eqToIso q.symm ≪≫
        ((Scheme.Modules.pullbackComp (f ≫ g) h).app M).symm := by
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, eqToIso.hom]
    exact h4
  have := congrArg Iso.inv hiso
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, eqToIso.inv,
    Category.assoc] at this
  exact this

theorem assoc_app₂ (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T') (M : T'.Modules)
    (q : (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj M = (Scheme.Modules.pullback (f ≫ g ≫ h)).obj M) :
    (Scheme.Modules.pullbackComp (f ≫ g) h).inv.app M ≫
        (Scheme.Modules.pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj M) =
      eqToHom q ≫ (Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M) := by
  have e := assoc_app f g h M q.symm
  have : eqToHom q ≫ (Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M) =
      eqToHom q ≫ ((Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M) ≫
        (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
          (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M) ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).inv.app M ≫
        (Scheme.Modules.pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj M) := by
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]
  rw [this, e, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

variable {X Y Z : Scheme.{u}}

@[reassoc]
theorem congr_left_inv {a b : X ⟶ Y} (hab : a = b) (g : Y ⟶ Z) (M : Z.Modules)
    (pa : (Scheme.Modules.pullback (a ≫ g)).obj M = (Scheme.Modules.pullback (b ≫ g)).obj M)
    (pb : (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback g).obj M) =
      (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback g).obj M)) :
    (Scheme.Modules.pullbackComp a g).inv.app M ≫ eqToHom pb =
      eqToHom pa ≫ (Scheme.Modules.pullbackComp b g).inv.app M := by
  subst hab; simp

@[reassoc]
theorem congr_left_inv_hom {a b : X ⟶ Y} (hab : a = b) (g : Y ⟶ Z) (M : Z.Modules)
    (pb : (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback g).obj M) =
      (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback g).obj M))
    (pa : (Scheme.Modules.pullback (a ≫ g)).obj M = (Scheme.Modules.pullback (b ≫ g)).obj M) :
    (Scheme.Modules.pullbackComp a g).inv.app M ≫ eqToHom pb ≫ (Scheme.Modules.pullbackComp b g).hom.app M =
      eqToHom pa := by
  subst hab; simp

@[reassoc]
theorem congr_right_hom_inv (a : X ⟶ Y) {g g' : Y ⟶ Z} (hg : g = g') (M : Z.Modules)
    (p1 : (Scheme.Modules.pullback (a ≫ g)).obj M = (Scheme.Modules.pullback (a ≫ g')).obj M)
    (p2 : (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback g).obj M) =
      (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback g').obj M)) :
    (Scheme.Modules.pullbackComp a g).hom.app M ≫ eqToHom p1 ≫ (Scheme.Modules.pullbackComp a g').inv.app M =
      eqToHom p2 := by
  subst hg; simp

@[reassoc]
theorem congr_right_inv (a : X ⟶ Y) {g g' : Y ⟶ Z} (hg : g = g') (M : Z.Modules)
    (p2 : (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback g).obj M) =
      (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback g').obj M))
    (p1 : (Scheme.Modules.pullback (a ≫ g)).obj M = (Scheme.Modules.pullback (a ≫ g')).obj M) :
    (Scheme.Modules.pullbackComp a g).inv.app M ≫ eqToHom p2 =
      eqToHom p1 ≫ (Scheme.Modules.pullbackComp a g').inv.app M := by
  subst hg; simp

@[reassoc]
theorem congr_right_hom (a : X ⟶ Y) {g g' : Y ⟶ Z} (hg : g = g') (M : Z.Modules)
    (p2 : (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback g).obj M) =
      (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback g').obj M))
    (p1 : (Scheme.Modules.pullback (a ≫ g)).obj M = (Scheme.Modules.pullback (a ≫ g')).obj M) :
    eqToHom p2 ≫ (Scheme.Modules.pullbackComp a g').hom.app M =
      (Scheme.Modules.pullbackComp a g).hom.app M ≫ eqToHom p1 := by
  subst hg; simp

theorem unit_app (W : X ⟶ Y) (M : Y.Modules)
    (p : (Scheme.Modules.pullback W).obj M = (Scheme.Modules.pullback (W ≫ 𝟙 Y)).obj M) :
    (Scheme.Modules.pullback W).map ((Scheme.Modules.pullbackId Y).inv.app M) ≫
      (Scheme.Modules.pullbackComp W (𝟙 Y)).hom.app M = eqToHom p := by
  have := NatTrans.congr_app (Scheme.Modules.pseudofunctor_left_unitality W) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Category.comp_id,
    eqToHom_app] at this

  have this' : eqToHom p.symm = (Scheme.Modules.pullbackComp W (𝟙 Y)).inv.app M ≫
      (Scheme.Modules.pullback W).map ((Scheme.Modules.pullbackId Y).hom.app M) ≫ 𝟙 _ := this.symm
  suffices h : ((Scheme.Modules.pullback W).map ((Scheme.Modules.pullbackId Y).inv.app M) ≫
      (Scheme.Modules.pullbackComp W (𝟙 Y)).hom.app M) ≫ eqToHom p.symm = 𝟙 _ by
    have := (comp_eqToHom_iff _ _ _).1 h
    simpa using this
  rw [this']
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

end coh

end ThetaE165

namespace ThetaE165
set_option backward.isDefEq.respectTransparency false
p2m_open "CategoryTheory.Pseudofunctor.CoGrothendieck"

section fiber
variable {A : Scheme.{0}}

theorem fib_mapComp_inv_app (a b : A ⟶ A) (X : A.Modules) :
    (Scheme.Modules.fibration.mapComp a.op.toLoc b.op.toLoc).inv.toNatTrans.app X =
      (Scheme.Modules.pullbackComp b a).hom.app X := by
  simp [Scheme.Modules.fibration]
  erw [Category.id_comp]
  rfl

theorem fib_mapComp_hom_app (a b : A ⟶ A) (X : A.Modules) :
    (Scheme.Modules.fibration.mapComp a.op.toLoc b.op.toLoc).hom.toNatTrans.app X =
      (Scheme.Modules.pullbackComp b a).inv.app X := by
  simp [Scheme.Modules.fibration]
  erw [Category.comp_id]
  rfl

theorem fib_mapId_inv_app (X : A.Modules) :
    (Scheme.Modules.fibration.mapId ⟨Opposite.op A⟩).inv.toNatTrans.app X = (Scheme.Modules.pullbackId A).inv.app X := by
  simp [Scheme.Modules.fibration]

theorem fib_mapId_hom_app (X : A.Modules) :
    (Scheme.Modules.fibration.mapId ⟨Opposite.op A⟩).hom.toNatTrans.app X = (Scheme.Modules.pullbackId A).hom.app X := by
  simp [Scheme.Modules.fibration]
  erw [Category.comp_id]

variable {M : A.Modules}

theorem isIso_fiber (g : Aut (modulePair (A := A) M)) : IsIso g.hom.fiber := by
  have h1 := Hom.congr g.hom_inv_id
  have h2 := Hom.congr g.inv_hom_id
  have hb : g.hom.base ≫ g.inv.base = 𝟙 A := by
    rw [← categoryStruct_comp_base, g.hom_inv_id]; rfl
  have hb2 : g.inv.base ≫ g.hom.base = 𝟙 A := by
    rw [← categoryStruct_comp_base, g.inv_hom_id]; rfl
  simp only [categoryStruct_comp_fiber, categoryStruct_id_fiber, categoryStruct_comp_base,
    Scheme.Modules.fibration_map_toFunctor, fib_mapComp_inv_app, fib_mapId_inv_app] at h1 h2
  have q1 : (Scheme.Modules.pullback (g.hom.base ≫ g.inv.base)).obj M = (Scheme.Modules.pullback (𝟙 A)).obj M := by
    rw [hb]
  have q2 : (Scheme.Modules.pullback (g.inv.base ≫ g.hom.base)).obj M = (Scheme.Modules.pullback (𝟙 A)).obj M := by
    rw [hb2]

  have hsm : IsSplitMono g.hom.fiber := IsSplitMono.mk'
    ⟨(Scheme.Modules.pullback g.hom.base).map g.inv.fiber ≫
      (Scheme.Modules.pullbackComp g.hom.base g.inv.base).hom.app M ≫ eqToHom q1 ≫ (Scheme.Modules.pullbackId A).hom.app M, by
    rw [reassoc_of% h1]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Iso.inv_hom_id_app]
    rfl⟩

  haveI : IsSplitMono ((Scheme.Modules.pullback g.inv.base).map g.hom.fiber) := inferInstance
  have hψφ : g.inv.fiber ≫ (Scheme.Modules.pullback g.inv.base).map g.hom.fiber =
      ((Scheme.Modules.pullbackId A).inv.app M ≫ eqToHom q2.symm) ≫
        (Scheme.Modules.pullbackComp g.inv.base g.hom.base).inv.app M := by
    have h2' : g.inv.fiber ≫ (Scheme.Modules.pullback g.inv.base).map g.hom.fiber ≫
        (Scheme.Modules.pullbackComp g.inv.base g.hom.base).hom.app M =
        (Scheme.Modules.pullbackId A).inv.app M ≫ eqToHom q2.symm := h2
    rw [← h2']
    simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]
    erw [Category.comp_id]
  haveI : IsSplitEpi ((Scheme.Modules.pullback g.inv.base).map g.hom.fiber) := IsSplitEpi.mk'
    ⟨(Scheme.Modules.pullbackComp g.inv.base g.hom.base).hom.app M ≫ eqToHom q2 ≫
      (Scheme.Modules.pullbackId A).hom.app M ≫ g.inv.fiber, by
      simp only [Category.assoc]
      rw [hψφ]
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        Iso.hom_inv_id_app]
      rfl⟩
  haveI : IsIso ((Scheme.Modules.pullback g.inv.base).map g.hom.fiber) := isIso_of_mono_of_isSplitEpi _

  let θ : Scheme.Modules.pullback g.inv.base ⋙ Scheme.Modules.pullback g.hom.base ≅ 𝟭 _ :=
    Scheme.Modules.pullbackComp g.hom.base g.inv.base ≪≫ Scheme.Modules.pullbackCongr hb ≪≫ Scheme.Modules.pullbackId A
  have hnat := θ.hom.naturality g.hom.fiber
  simp only [Functor.comp_map, Functor.id_map] at hnat
  have hφ' : g.hom.fiber = θ.inv.app M ≫
      (Scheme.Modules.pullback g.hom.base).map ((Scheme.Modules.pullback g.inv.base).map g.hom.fiber) ≫ θ.hom.app _ := by
    rw [hnat, Iso.inv_hom_id_app_assoc]
  rw [hφ']
  infer_instance

noncomputable def fiberIso (g : Aut (modulePair (A := A) M)) :
    M ≅ (Scheme.Modules.pullback g.hom.base).obj M :=
  haveI := isIso_fiber g
  asIso g.hom.fiber

@[scoped simp] theorem fiberIso_hom (g : Aut (modulePair (A := A) M)) : (fiberIso g).hom = g.hom.fiber := rfl

theorem commutatorElement_hom {C : Type*} [Category C] {X : C} (x g : Aut X) :
    (⁅x, g⁆ : Aut X).hom = g.inv ≫ x.inv ≫ g.hom ≫ x.hom := by
  simp only [commutatorElement_def]
  rfl

theorem comp_commutator_hom {C : Type*} [Category C] {X : C} (x g : Aut X) :
    (x.hom ≫ g.hom) ≫ (⁅x, g⁆ : Aut X).hom = g.hom ≫ x.hom := by
  rw [commutatorElement_hom]; simp

end fiber
end ThetaE165
p2m_reactivate "P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_isLevelPairingValue_of_isScalarElt_commutatorElement_levelLift.ThetaE165"

namespace ThetaE165
set_option backward.isDefEq.respectTransparency false
p2m_open "CategoryTheory.Pseudofunctor.CoGrothendieck"

section coh2
variable {A : Scheme.{0}}

theorem unitB (W B : A ⟶ A) (hB : B = 𝟙 A) (M : A.Modules)
    (p : (Scheme.Modules.pullback W).obj M = (Scheme.Modules.pullback (W ≫ B)).obj M) :
    (Scheme.Modules.pullback W).map ((Scheme.Modules.pullbackId A).inv.app M) ≫
      (Scheme.Modules.pullback W).map ((Scheme.Modules.pullbackCongr hB).inv.app M) ≫
      (Scheme.Modules.pullbackComp W B).hom.app M = eqToHom p := by
  subst hB
  simp only [Scheme.Modules.pullbackCongr, eqToIso.inv, eqToHom_app, eqToHom_refl, eqToIso_refl, Iso.refl_inv,
    NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  exact unit_app W M p

noncomputable def canIso (S N Ty : A ⟶ A) (hS : S ≫ N = N ≫ Ty) (𝓛 : A.Modules) :
    (Scheme.Modules.pullback S).obj ((Scheme.Modules.pullback N).obj 𝓛) ≅
      (Scheme.Modules.pullback N).obj ((Scheme.Modules.pullback Ty).obj 𝓛) :=
  (Scheme.Modules.pullbackComp S N).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr hS).app 𝓛 ≪≫
    ((Scheme.Modules.pullbackComp N Ty).app 𝓛).symm

end coh2
p2m_reactivate "P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_isLevelPairingValue_of_isScalarElt_commutatorElement_levelLift.ThetaE165"
end ThetaE165
p2m_reactivate "P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_isLevelPairingValue_of_isScalarElt_commutatorElement_levelLift.ThetaE165"

namespace ThetaE169K
set_option backward.isDefEq.respectTransparency false
open ThetaE165
variable {A : Scheme.{0}}

theorem canL (T S N Ty : A ⟶ A) (hx : T ≫ N = N) (hS : S ≫ N = N ≫ Ty) (𝓛 : A.Modules)
    (P : (Scheme.Modules.pullback (S ≫ N)).obj 𝓛 = (Scheme.Modules.pullback (T ≫ S ≫ N)).obj 𝓛) :
    (canIso S N Ty hS 𝓛).hom ≫ (transportIso hx ((Scheme.Modules.pullback Ty).obj 𝓛)).inv ≫
      (Scheme.Modules.pullback T).map (canIso S N Ty hS 𝓛).inv =
    (Scheme.Modules.pullbackComp S N).hom.app 𝓛 ≫ eqToHom P ≫
      (Scheme.Modules.pullbackComp T (S ≫ N)).inv.app 𝓛 ≫
        (Scheme.Modules.pullback T).map ((Scheme.Modules.pullbackComp S N).inv.app 𝓛) := by
  simp only [canIso, transportIso, Scheme.Modules.pullbackCongr, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, Iso.app_hom, Iso.app_inv, eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_map,
    Functor.map_comp, Category.assoc]
  rw [assoc_app₃_assoc T N Ty 𝓛 (by simp only [Category.assoc])]
  rw [congr_left_inv_hom_assoc hx.symm Ty 𝓛 _ (by rw [hx])]
  rw [congr_right_inv_assoc T hS.symm 𝓛 _ (by rw [hS])]
  simp only [eqToHom_trans_assoc, Category.assoc]

theorem canR (T S N : A ⟶ A) (hx : T ≫ N = N) (hTS : T ≫ S = S ≫ T) (𝓛 : A.Modules)
    (P : (Scheme.Modules.pullback (S ≫ N)).obj 𝓛 = (Scheme.Modules.pullback (T ≫ S ≫ N)).obj 𝓛) :
    (Scheme.Modules.pullback S).map (transportIso hx 𝓛).inv ≫
      (Scheme.Modules.pullbackComp S T).hom.app ((Scheme.Modules.pullback N).obj 𝓛) ≫
      (Scheme.Modules.pullbackCongr hTS).inv.app ((Scheme.Modules.pullback N).obj 𝓛) ≫
      (Scheme.Modules.pullbackComp T S).inv.app ((Scheme.Modules.pullback N).obj 𝓛) =
    (Scheme.Modules.pullbackComp S N).hom.app 𝓛 ≫ eqToHom P ≫
      (Scheme.Modules.pullbackComp T (S ≫ N)).inv.app 𝓛 ≫
        (Scheme.Modules.pullback T).map ((Scheme.Modules.pullbackComp S N).inv.app 𝓛) := by
  simp only [transportIso, Scheme.Modules.pullbackCongr, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, Iso.app_hom, Iso.app_inv, eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_map,
    Functor.map_comp, Category.assoc]
  rw [assoc_app₄_assoc S T N 𝓛 (by simp only [Category.assoc])]
  rw [congr_right_hom_assoc S hx.symm 𝓛 _ (by rw [hx])]
  rw [congr_left_inv_assoc hTS.symm N 𝓛 (by rw [hTS])]
  rw [assoc_app₂ T S N 𝓛 (by simp only [Category.assoc])]
  simp only [eqToHom_trans_assoc, Category.assoc]

@[reassoc]
theorem can_coh' (T S N Ty : A ⟶ A) (hx : T ≫ N = N) (hS : S ≫ N = N ≫ Ty) (hTS : T ≫ S = S ≫ T)
    (𝓛 : A.Modules) :
    (canIso S N Ty hS 𝓛).hom ≫ (transportIso hx ((Scheme.Modules.pullback Ty).obj 𝓛)).inv ≫
      (Scheme.Modules.pullback T).map (canIso S N Ty hS 𝓛).inv =
    (Scheme.Modules.pullback S).map (transportIso hx 𝓛).inv ≫
      (Scheme.Modules.pullbackComp S T).hom.app ((Scheme.Modules.pullback N).obj 𝓛) ≫
      (Scheme.Modules.pullbackCongr hTS).inv.app ((Scheme.Modules.pullback N).obj 𝓛) ≫
      (Scheme.Modules.pullbackComp T S).inv.app ((Scheme.Modules.pullback N).obj 𝓛) := by
  have P : (Scheme.Modules.pullback (S ≫ N)).obj 𝓛 = (Scheme.Modules.pullback (T ≫ S ≫ N)).obj 𝓛 := by
    rw [← Category.assoc, hTS, Category.assoc, hx]
  rw [canL T S N Ty hx hS 𝓛 P, canR T S N hx hTS 𝓛 P]

theorem sigma_eq' (T S N Ty : A ⟶ A) (hx : T ≫ N = N) (hS : S ≫ N = N ≫ Ty) (hTS : T ≫ S = S ≫ T)
    (𝓛 : A.Modules)
    (φ : (Scheme.Modules.pullback N).obj 𝓛 ≅ (Scheme.Modules.pullback S).obj ((Scheme.Modules.pullback N).obj 𝓛)) :
    ((φ ≪≫ canIso S N Ty hS 𝓛).symm.symm ≪≫ (transportIso hx ((Scheme.Modules.pullback Ty).obj 𝓛)).symm ≪≫
        (Scheme.Modules.pullback T).mapIso (φ ≪≫ canIso S N Ty hS 𝓛).symm ≪≫ transportIso hx 𝓛).hom =
      (φ.hom ≫ (Scheme.Modules.pullback S).map (transportIso hx 𝓛).inv ≫
          (Scheme.Modules.pullbackComp S T).hom.app ((Scheme.Modules.pullback N).obj 𝓛)) ≫
        (Scheme.Modules.pullbackCongr hTS).inv.app ((Scheme.Modules.pullback N).obj 𝓛) ≫
        ((transportIso hx 𝓛).symm ≪≫ (Scheme.Modules.pullback T).mapIso φ ≪≫
          (Scheme.Modules.pullbackComp T S).app ((Scheme.Modules.pullback N).obj 𝓛)).inv := by
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Iso.symm_symm_eq, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.app_inv, Functor.map_comp, Category.assoc]
  rw [can_coh'_assoc T S N Ty hx hS hTS 𝓛]

end ThetaE169K
p2m_reactivate "P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_isLevelPairingValue_of_isScalarElt_commutatorElement_levelLift.ThetaE165"

namespace ThetaE169C
set_option backward.isDefEq.respectTransparency false
p2m_open "CategoryTheory.Pseudofunctor.CoGrothendieck P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_isLevelPairingValue_of_isScalarElt_commutatorElement_levelLift.ThetaE165"
variable {A : Scheme.{0}}

theorem coreKey (M : A.Modules) (x g : Aut (modulePair (A := A) M))
    (hB : (⁅x, g⁆ : Aut _).hom.base = 𝟙 A)
    (q1 : (Scheme.Modules.pullback (x.hom.base ≫ g.hom.base)).obj M =
      (Scheme.Modules.pullback ((x.hom.base ≫ g.hom.base) ≫ (⁅x, g⁆ : Aut _).hom.base)).obj M)
    (q2 : (Scheme.Modules.pullback (g.hom.base ≫ x.hom.base)).obj M =
      (Scheme.Modules.pullback ((x.hom.base ≫ g.hom.base) ≫ (⁅x, g⁆ : Aut _).hom.base)).obj M) :
    (x.hom.fiber ≫ (Scheme.Modules.pullback x.hom.base).map g.hom.fiber ≫
        (Scheme.Modules.pullbackComp x.hom.base g.hom.base).hom.app M) ≫
          (Scheme.Modules.pullback (x.hom.base ≫ g.hom.base)).map (thetaGroup.unitReading M hB) ≫ eqToHom q1 =
      (g.hom.fiber ≫ (Scheme.Modules.pullback g.hom.base).map x.hom.fiber ≫
        (Scheme.Modules.pullbackComp g.hom.base x.hom.base).hom.app M) ≫ eqToHom q2 := by
  have key := Hom.congr (comp_commutator_hom x g)
  simp only [categoryStruct_comp_fiber, categoryStruct_comp_base, Scheme.Modules.fibration_map_toFunctor,
    fib_mapComp_inv_app, Category.assoc] at key
  have hζf : (⁅x, g⁆ : Aut _).hom.fiber =
      thetaGroup.unitReading M hB ≫ (Scheme.Modules.pullbackId A).inv.app _ ≫ (Scheme.Modules.pullbackCongr hB).inv.app _ := by
    simp only [thetaGroup.unitReading, Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  rw [hζf] at key
  simp only [Functor.map_comp, Category.assoc] at key
  rw [unitB _ _ hB _ (by rw [hB, Category.comp_id])] at key
  simp only [Category.assoc]
  exact key

theorem core (M : A.Modules) (x g : Aut (modulePair (A := A) M))
    (hB : (⁅x, g⁆ : Aut _).hom.base = 𝟙 A)
    (hTS : x.hom.base ≫ g.hom.base = g.hom.base ≫ x.hom.base)
    (e0 : (Scheme.Modules.pullback (g.hom.base ≫ x.hom.base)).obj M =
      (Scheme.Modules.pullback (x.hom.base ≫ g.hom.base)).obj M) :
    (Scheme.Modules.pullback (x.hom.base ≫ g.hom.base)).map (thetaGroup.unitReading M hB) =
      (fiberIso x ≪≫ (Scheme.Modules.pullback x.hom.base).mapIso (fiberIso g) ≪≫
          (Scheme.Modules.pullbackComp x.hom.base g.hom.base).app M).inv ≫
        (g.hom.fiber ≫ (Scheme.Modules.pullback g.hom.base).map x.hom.fiber ≫
          (Scheme.Modules.pullbackComp g.hom.base x.hom.base).hom.app M) ≫
        eqToHom e0 := by
  have q1 : (Scheme.Modules.pullback (x.hom.base ≫ g.hom.base)).obj M =
      (Scheme.Modules.pullback ((x.hom.base ≫ g.hom.base) ≫ (⁅x, g⁆ : Aut _).hom.base)).obj M := by
    rw [hB, Category.comp_id]
  have q2 : (Scheme.Modules.pullback (g.hom.base ≫ x.hom.base)).obj M =
      (Scheme.Modules.pullback ((x.hom.base ≫ g.hom.base) ≫ (⁅x, g⁆ : Aut _).hom.base)).obj M := by
    rw [hB, Category.comp_id, ← hTS]
  have key2 : (fiberIso x ≪≫ (Scheme.Modules.pullback x.hom.base).mapIso (fiberIso g) ≪≫
        (Scheme.Modules.pullbackComp x.hom.base g.hom.base).app M).hom ≫
      (Scheme.Modules.pullback (x.hom.base ≫ g.hom.base)).map (thetaGroup.unitReading M hB) ≫ eqToHom q1 =
      (g.hom.fiber ≫ (Scheme.Modules.pullback g.hom.base).map x.hom.fiber ≫
          (Scheme.Modules.pullbackComp g.hom.base x.hom.base).hom.app M) ≫ eqToHom q2 := by
    rw [Iso.trans_hom, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, fiberIso_hom, fiberIso_hom]
    exact coreKey M x g hB q1 q2
  rw [← Iso.eq_inv_comp] at key2
  rw [comp_eqToHom_iff] at key2
  rw [key2]
  simp only [Category.assoc, eqToHom_trans]

end ThetaE169C
p2m_reactivate "P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_isLevelPairingValue_of_isScalarElt_commutatorElement_levelLift.ThetaE165"

namespace ThetaX
set_option backward.isDefEq.respectTransparency false
p2m_open "CategoryTheory.Pseudofunctor.CoGrothendieck P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_isLevelPairingValue_of_isScalarElt_commutatorElement_levelLift.ThetaE165"

theorem conj_cancel {C : Type*} [Category C] {M N P : C} (e : M ≅ N) (X : M ⟶ P) (q : P ⟶ N) :
    e.hom ≫ (e.inv ≫ X ≫ q) = (X ≫ q ≫ e.inv) ≫ e.hom := by
  simp

section generic
variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))

theorem isConstScalar_conj {M N : A.Modules} (e : M ≅ N) {σ : N ⟶ N} {c : k}
    (hσ : IsConstScalar f σ c) : IsConstScalar f (e.hom ≫ σ ≫ e.inv) c := by
  intro U s
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app]
  change e.inv.app U (σ.app U (e.hom.app U s)) = _
  rw [hσ U, Scheme.Modules.Hom.app_smul]
  change _ • (e.hom.app U ≫ e.inv.app U) s = _
  rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]
  rfl

theorem isConstScalar_conj' {M N : A.Modules} (e : M ≅ N) {σ : M ⟶ M} {c : k}
    (hσ : IsConstScalar f σ c) : IsConstScalar f (e.inv ≫ σ ≫ e.hom) c :=
  isConstScalar_conj f e.symm hσ

theorem isConstScalar_of_pullback_map (W W' : A ⟶ A) (hW' : W' ≫ f = f) (h : W' ≫ W = 𝟙 A)
    {M : A.Modules} {r : M ⟶ M} {c : k} (hr : IsConstScalar f ((Scheme.Modules.pullback W).map r) c) :
    IsConstScalar f r c := by
  let θ : Scheme.Modules.pullback W ⋙ Scheme.Modules.pullback W' ≅ 𝟭 _ :=
    Scheme.Modules.pullbackComp W' W ≪≫ Scheme.Modules.pullbackCongr h ≪≫ Scheme.Modules.pullbackId A
  have hnat := θ.hom.naturality r
  simp only [Functor.comp_map, Functor.id_map] at hnat
  have hr' : r = (θ.app M).inv ≫ (Scheme.Modules.pullback W').map ((Scheme.Modules.pullback W).map r) ≫ (θ.app M).hom := by
    rw [Iso.app_inv, Iso.app_hom, hnat, Iso.inv_hom_id_app_assoc]
  rw [hr']
  exact isConstScalar_conj' f (θ.app M)
    (AlgebraicGeometry.RiemannForm.isConstScalar_pullback_map k f W' hW' hr)

theorem isConstScalar_of_conj {M N : A.Modules} (e : M ≅ N) {σ : M ⟶ M} {τ : N ⟶ N} {c : k}
    (hσ : IsConstScalar f σ c) (h : e.hom ≫ τ = σ ≫ e.hom) : IsConstScalar f τ c := by
  have hτ : τ = e.inv ≫ σ ≫ e.hom := by
    rw [Iso.eq_inv_comp]
    exact h
  rw [hτ]
  exact isConstScalar_conj' f e hσ

variable (L : RelativeGroupLaw k f) (hc : L.IsCommutative)

theorem pullbackCongr_inv_app_eq {X Y : Scheme.{0}} {a b : X ⟶ Y} (h : a = b) (M : Y.Modules)
    (p : (Scheme.Modules.pullback b).obj M = (Scheme.Modules.pullback a).obj M) :
    (Scheme.Modules.pullbackCongr h).inv.app M = eqToHom p := by
  subst h
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_inv, NatTrans.id_app, eqToHom_refl]

theorem dir1x (𝓛 : A.Modules) (n : ℕ)
    (x g : thetaGroup f L hc ((Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛)) (P : L.AlgPoints hc k)
    (hXT : x.1.1.hom.base = translation f L (RelativeGroupLaw.AlgPoints.toPoint P))
    (hxN : x.1.1.hom.base ≫ L.schemeNsmul n = L.schemeNsmul n)
    (hxfib : x.1.1.hom.fiber = (transportIso hxN 𝓛).inv) (c : k)
    (hsc : thetaGroup.IsScalarElt f L hc _ ⁅x, g⁆ c) :
    ∃ β : (Scheme.Modules.pullback (L.schemeNsmul n)).obj ((Scheme.Modules.pullback (translation f L
        (RelativeGroupLaw.AlgPoints.toPoint (n • Multiplicative.toAdd (thetaGroup.pt f L hc _ g))))).obj 𝓛) ≅
        (Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛,
      IsConstScalar f (β.symm ≪≫ (transportIso hxN ((Scheme.Modules.pullback (translation f L
        (RelativeGroupLaw.AlgPoints.toPoint (n • Multiplicative.toAdd (thetaGroup.pt f L hc _ g))))).obj 𝓛)).symm ≪≫
        (Scheme.Modules.pullback x.1.1.hom.base).mapIso β ≪≫ transportIso hxN 𝓛).hom c := by
  obtain ⟨hζ1, hr⟩ := hsc
  have hB : (⁅x.1.1, g.1.1⁆ : Aut _).hom.base = 𝟙 A := thetaGroup.base_eq_id_of_pt_eq_one f L hc _ _ hζ1
  have hr' : IsConstScalar f (thetaGroup.unitReading ((Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛) hB) c := hr
  have hSz : g.1.1.hom.base = translation f L (RelativeGroupLaw.AlgPoints.toPoint
      (Multiplicative.toAdd (thetaGroup.pt f L hc _ g))) := thetaGroup.base_eq f L hc _ g
  have hS : g.1.1.hom.base ≫ L.schemeNsmul n =
      L.schemeNsmul n ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint
        (n • Multiplicative.toAdd (thetaGroup.pt f L hc _ g))) := by
    rw [hSz]
    exact (AlgebraicGeometry.RiemannForm.schemeNsmul_mul_and_translation_comp_schemeNsmul k f L hc 1 n _).2
  have hTS : x.1.1.hom.base ≫ g.1.1.hom.base = g.1.1.hom.base ≫ x.1.1.hom.base := by
    rw [hSz, hXT, ← translation_toPoint_add, ← translation_toPoint_add, add_comm]
  have hW : (x.1.1.hom.base ≫ g.1.1.hom.base) ≫ f = f := by
    rw [Category.assoc, hSz, translation_over, hXT, translation_over]
  have e0 : (Scheme.Modules.pullback (g.1.1.hom.base ≫ x.1.1.hom.base)).obj
        ((Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛) =
      (Scheme.Modules.pullback (x.1.1.hom.base ≫ g.1.1.hom.base)).obj
        ((Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛) := by rw [hTS]
  have hcore := ThetaE169C.core _ x.1.1 g.1.1 hB hTS e0
  have hxF : fiberIso x.1.1 = (transportIso hxN 𝓛).symm := Iso.ext (by rw [fiberIso_hom, hxfib, Iso.symm_hom])
  rw [hxF, hxfib] at hcore
  refine ⟨(fiberIso g.1.1 ≪≫ canIso g.1.1.hom.base (L.schemeNsmul n) _ hS 𝓛).symm, ?_⟩
  rw [ThetaE169K.sigma_eq' _ _ _ _ hxN hS hTS 𝓛 (fiberIso g.1.1)]
  have hε : (Scheme.Modules.pullbackCongr hTS).inv.app ((Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛) =
      eqToHom e0 :=
    pullbackCongr_inv_app_eq hTS _ e0
  rw [hε, fiberIso_hom, ← Category.assoc]
  rw [← Iso.hom_inv_id_assoc ((transportIso hxN 𝓛).symm ≪≫
      (Scheme.Modules.pullback x.1.1.hom.base).mapIso (fiberIso g.1.1) ≪≫
        (Scheme.Modules.pullbackComp x.1.1.hom.base g.1.1.hom.base).app _)
      ((g.1.1.hom.fiber ≫ (Scheme.Modules.pullback g.1.1.hom.base).map (transportIso hxN 𝓛).inv ≫
          (Scheme.Modules.pullbackComp g.1.1.hom.base x.1.1.hom.base).hom.app _) ≫
        eqToHom e0)]
  rw [← hcore, Category.assoc]
  exact isConstScalar_conj f _
    (AlgebraicGeometry.RiemannForm.isConstScalar_pullback_map k f _ hW hr')

theorem dir2x (𝓛 : A.Modules) (n : ℕ)
    (x g : thetaGroup f L hc ((Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛)) (P : L.AlgPoints hc k)
    (hXT : x.1.1.hom.base = translation f L (RelativeGroupLaw.AlgPoints.toPoint P))
    (hxN : x.1.1.hom.base ≫ L.schemeNsmul n = L.schemeNsmul n)
    (hxfib : x.1.1.hom.fiber = (transportIso hxN 𝓛).inv) (c : k) (Q₁ : L.AlgPoints hc k)
    (hg : thetaGroup.pt f L hc _ g = Multiplicative.ofAdd Q₁)
    (hS : g.1.1.hom.base ≫ L.schemeNsmul n =
      L.schemeNsmul n ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint (n • Q₁)))
    (β : (Scheme.Modules.pullback (L.schemeNsmul n)).obj
        ((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint (n • Q₁)))).obj 𝓛) ≅
      (Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛)
    (hfib : g.1.1.hom.fiber = β.inv ≫ (canIso g.1.1.hom.base (L.schemeNsmul n)
      (translation f L (RelativeGroupLaw.AlgPoints.toPoint (n • Q₁))) hS 𝓛).inv)
    (hσ : IsConstScalar f
      (β.symm ≪≫ (transportIso hxN ((Scheme.Modules.pullback
          (translation f L (RelativeGroupLaw.AlgPoints.toPoint (n • Q₁)))).obj 𝓛)).symm ≪≫
        (Scheme.Modules.pullback x.1.1.hom.base).mapIso β ≪≫ transportIso hxN 𝓛).hom c) :
    thetaGroup.IsScalarElt f L hc _ ⁅x, g⁆ c := by
  have hζ1 : thetaGroup.pt f L hc _ ⁅x, g⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
  refine ⟨hζ1, ?_⟩
  have hB : (⁅x.1.1, g.1.1⁆ : Aut _).hom.base = 𝟙 A := thetaGroup.base_eq_id_of_pt_eq_one f L hc _ _ hζ1
  change IsConstScalar f (thetaGroup.unitReading ((Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛) hB) c
  have hSz : g.1.1.hom.base = translation f L (RelativeGroupLaw.AlgPoints.toPoint Q₁) := by
    rw [thetaGroup.base_eq f L hc _ g, ← thetaGroup.pt_apply, hg, toAdd_ofAdd]
  have hTS : x.1.1.hom.base ≫ g.1.1.hom.base = g.1.1.hom.base ≫ x.1.1.hom.base := by
    rw [hSz, hXT, ← translation_toPoint_add, ← translation_toPoint_add, add_comm]
  have hW' : translation f L (RelativeGroupLaw.AlgPoints.toPoint (-(P + Q₁))) ≫ f = f := translation_over f L _
  have hWW' : translation f L (RelativeGroupLaw.AlgPoints.toPoint (-(P + Q₁))) ≫
      (x.1.1.hom.base ≫ g.1.1.hom.base) = 𝟙 A := by
    rw [hSz, hXT, ← translation_toPoint_add, ← translation_toPoint_add, neg_add_cancel, translation_toPoint_zero]
  have e0 : (Scheme.Modules.pullback (g.1.1.hom.base ≫ x.1.1.hom.base)).obj
        ((Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛) =
      (Scheme.Modules.pullback (x.1.1.hom.base ≫ g.1.1.hom.base)).obj
        ((Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛) := by rw [hTS]
  have hcore := ThetaE169C.core _ x.1.1 g.1.1 hB hTS e0
  have hxF : fiberIso x.1.1 = (transportIso hxN 𝓛).symm := Iso.ext (by rw [fiberIso_hom, hxfib, Iso.symm_hom])
  rw [hxF, hxfib] at hcore
  have hφ : fiberIso g.1.1 = (canIso g.1.1.hom.base (L.schemeNsmul n)
      (translation f L (RelativeGroupLaw.AlgPoints.toPoint (n • Q₁))) hS 𝓛 ≪≫ β).symm :=
    Iso.ext (by rw [fiberIso_hom, hfib, Iso.symm_hom, Iso.trans_inv])
  rw [hφ, hfib] at hcore
  have hs := ThetaE169K.sigma_eq' x.1.1.hom.base g.1.1.hom.base (L.schemeNsmul n)
    (translation f L (RelativeGroupLaw.AlgPoints.toPoint (n • Q₁))) hxN hS hTS 𝓛
    (canIso g.1.1.hom.base (L.schemeNsmul n) (translation f L (RelativeGroupLaw.AlgPoints.toPoint (n • Q₁))) hS 𝓛
      ≪≫ β).symm
  have hβ : ((canIso g.1.1.hom.base (L.schemeNsmul n) (translation f L (RelativeGroupLaw.AlgPoints.toPoint (n • Q₁)))
      hS 𝓛 ≪≫ β).symm ≪≫ canIso g.1.1.hom.base (L.schemeNsmul n)
        (translation f L (RelativeGroupLaw.AlgPoints.toPoint (n • Q₁))) hS 𝓛).symm = β := by
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Iso.inv_hom_id_assoc]
  rw [hβ] at hs
  have hσ' := hσ
  rw [hs] at hσ'
  have hε : (Scheme.Modules.pullbackCongr hTS).inv.app ((Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛) =
      eqToHom e0 :=
    pullbackCongr_inv_app_eq hTS _ e0
  rw [hε] at hσ'
  apply isConstScalar_of_pullback_map f (x.1.1.hom.base ≫ g.1.1.hom.base)
    (translation f L (RelativeGroupLaw.AlgPoints.toPoint (-(P + Q₁)))) hW' hWW'
  rw [hcore]
  exact isConstScalar_of_conj f _ hσ' (conj_cancel _ _ _)

theorem dir1 (𝓛 : A.Modules) (n : ℕ) (P : L.AlgPoints hc k)
    (hx : translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ L.schemeNsmul n = L.schemeNsmul n) (c : k)
    (g : thetaGroup f L hc ((Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛))
    (hsc : thetaGroup.IsScalarElt f L hc _ ⁅levelLift f L hc 𝓛 n P hx, g⁆ c) :
    IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint P)
      (RelativeGroupLaw.AlgPoints.toPoint (n • Multiplicative.toAdd (thetaGroup.pt f L hc _ g))) c := by
  obtain ⟨β, hβ⟩ := dir1x f L hc 𝓛 n (levelLift f L hc 𝓛 n P hx) g P rfl hx rfl c hsc
  exact ⟨hx, β, hβ⟩

theorem dir2 (𝓛 : A.Modules) (n : ℕ) (P : L.AlgPoints hc k)
    (hx : translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ L.schemeNsmul n = L.schemeNsmul n) (c : k)
    (Q₁ : L.AlgPoints hc k)
    (hv : IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint P)
      (RelativeGroupLaw.AlgPoints.toPoint (n • Q₁)) c) :
    ∃ g : thetaGroup f L hc ((Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛),
      thetaGroup.pt f L hc _ g = Multiplicative.ofAdd Q₁ ∧
        thetaGroup.IsScalarElt f L hc _ ⁅levelLift f L hc 𝓛 n P hx, g⁆ c := by
  obtain ⟨hx₂, β, hσ⟩ := hv
  have hS : translation f L (RelativeGroupLaw.AlgPoints.toPoint Q₁) ≫ L.schemeNsmul n =
      L.schemeNsmul n ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint (n • Q₁)) :=
    (AlgebraicGeometry.RiemannForm.schemeNsmul_mul_and_translation_comp_schemeNsmul k f L hc 1 n Q₁).2
  refine ⟨thetaGroup.liftOfIso f L hc _ Q₁ (canIso (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q₁))
    (L.schemeNsmul n) (translation f L (RelativeGroupLaw.AlgPoints.toPoint (n • Q₁))) hS 𝓛 ≪≫ β), rfl, ?_⟩
  exact dir2x f L hc 𝓛 n (levelLift f L hc 𝓛 n P hx) _ P rfl hx rfl c Q₁ rfl hS β rfl hσ

end generic
p2m_reactivate "P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_isLevelPairingValue_of_isScalarElt_commutatorElement_levelLift.ThetaE165"
end ThetaX
p2m_reactivate "P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_isLevelPairingValue_of_isScalarElt_commutatorElement_levelLift.ThetaE165"

theorem solution
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (𝓛 : A.Modules) (n : ℕ) (P : L.AlgPoints hc k)
    (hx : translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ L.schemeNsmul n = L.schemeNsmul n) (c : k) :
    (∀ g : thetaGroup f L hc ((Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛),
      thetaGroup.IsScalarElt f L hc _ ⁅levelLift f L hc 𝓛 n P hx, g⁆ c →
        IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint P)
          (RelativeGroupLaw.AlgPoints.toPoint (n • Multiplicative.toAdd (thetaGroup.pt f L hc _ g))) c) ∧
    (∀ Q₁ : L.AlgPoints hc k,
      IsLevelPairingValue f L 𝓛 n (RelativeGroupLaw.AlgPoints.toPoint P) (RelativeGroupLaw.AlgPoints.toPoint (n • Q₁)) c →
        ∃ g : thetaGroup f L hc ((Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛),
          thetaGroup.pt f L hc _ g = Multiplicative.ofAdd Q₁ ∧
            thetaGroup.IsScalarElt f L hc _ ⁅levelLift f L hc 𝓛 n P hx, g⁆ c) :=
  ⟨fun g h => ThetaX.dir1 f L hc 𝓛 n P hx c g h, fun Q₁ h => ThetaX.dir2 f L hc 𝓛 n P hx c Q₁ h⟩

end S_AlgebraicGeometry_RiemannForm_thetaGroup_isLevelPairingValue_of_isScalarElt_commutatorElement_levelLift
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_isLevelPairingValue_of_isScalarElt_commutatorElement_levelLift (solution)
