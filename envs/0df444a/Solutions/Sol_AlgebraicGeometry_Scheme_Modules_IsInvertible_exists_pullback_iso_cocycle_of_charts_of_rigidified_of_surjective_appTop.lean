-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_pullback_iso_cocycle_of_charts_of_rigidified_of_surjective_appTop
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/5a158350-fb8b-54e2-8383-b8186913c70a

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_overlaps_toSpecAway_section_of_charts_of_isPullback_of_surjective_appTop
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_pullback_mapIso_eq_of_locally_of_rigidified
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_trans_eq_of_pullback_mapIso_eq_of_surjective_appTop
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_forall_pullback_cocycle_of_cocycle_pullback_snd_fst
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullback_mapIso_pullback_mapIso_eq_of_pullback_mapIso_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_pullback_iso_cocycle_of_charts_of_rigidified_of_surjective_appTop
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_pullback_iso_cocycle_of_charts_of_rigidified_of_surjective_appTop.AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open scoped TensorProduct

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective Scheme.Modules.pushforward Scheme.Modules.pushforwardComp Scheme.Modules.pullback Scheme.Hom Spec Spec.map Scheme Scheme.Modules.pseudofunctor_associativity IsOpenImmersion Scheme.Modules.pullbackCongr Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules Scheme.Hom.comp_preimage Scheme.Modules.conjugateEquiv_pullbackComp_inv Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.exists_overlaps_toSpecAway_section_of_charts_of_isPullback_of_surjective_appTop Scheme.Modules.IsInvertible.exists_iso_pullback_mapIso_eq_of_locally_of_rigidified Scheme.Modules.IsInvertible.trans_eq_of_pullback_mapIso_eq_of_surjective_appTop Scheme.Modules.forall_pullback_cocycle_of_cocycle_pullback_snd_fst Scheme.Modules.pullback_mapIso_pullback_mapIso_eq_of_pullback_mapIso_eq"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Modules.pushforward Modules.pushforwardComp Modules.pullback Hom Modules.pseudofunctor_associativity Modules.pullbackCongr Modules.pullbackPushforwardAdjunction Modules Opens Hom.comp_preimage Modules.conjugateEquiv_pullbackComp_inv Modules.pullbackComp Modules.IsInvertible Modules.pullbackUnitIso exists_overlaps_toSpecAway_section_of_charts_of_isPullback_of_surjective_appTop Modules.IsInvertible.exists_iso_pullback_mapIso_eq_of_locally_of_rigidified Modules.IsInvertible.trans_eq_of_pullback_mapIso_eq_of_surjective_appTop Modules.forall_pullback_cocycle_of_cocycle_pullback_snd_fst Modules.pullback_mapIso_pullback_mapIso_eq_of_pullback_mapIso_eq"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pushforward pushforwardComp pullback Hom pseudofunctor_associativity pullbackCongr pullbackPushforwardAdjunction conjugateEquiv_pullbackComp_inv pullbackComp IsInvertible pullbackUnitIso IsInvertible.exists_iso_pullback_mapIso_eq_of_locally_of_rigidified IsInvertible.trans_eq_of_pullback_mapIso_eq_of_surjective_appTop forall_pullback_cocycle_of_cocycle_pullback_snd_fst pullback_mapIso_pullback_mapIso_eq_of_pullback_mapIso_eq"
namespace RTKit
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

theorem pc_assoc_hom {W X Y Z : Scheme.{u}} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (N : Z.Modules) :
    (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b c).inv.app N) ≫
      (Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback c).obj N) ≫
        (Scheme.Modules.pullbackComp (a ≫ b) c).hom.app N =
    (Scheme.Modules.pullbackComp a (b ≫ c)).hom.app N ≫
      (Scheme.Modules.pullbackCongr (Category.assoc a b c).symm).hom.app N := by
  have h := congrArg (fun t => t.app N) (Scheme.Modules.pseudofunctor_associativity a b c)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    eqToHom_app] at h
  have h2 : (Scheme.Modules.pullbackCongr (Category.assoc a b c).symm).hom.app N =
      eqToHom (by rw [Category.assoc]) := by
    simp only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app]
  rw [h2, ← h, Iso.hom_inv_id_app_assoc]
  congr 1

theorem pc_assoc_hom' {W X Y Z : Scheme.{u}} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (N : Z.Modules) :
    (Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback c).obj N) ≫
        (Scheme.Modules.pullbackComp (a ≫ b) c).hom.app N =
    (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b c).hom.app N) ≫
      (Scheme.Modules.pullbackComp a (b ≫ c)).hom.app N ≫
      (Scheme.Modules.pullbackCongr (Category.assoc a b c).symm).hom.app N := by
  have h := pc_assoc_hom a b c N
  calc (Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback c).obj N) ≫
          (Scheme.Modules.pullbackComp (a ≫ b) c).hom.app N
      = (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b c).hom.app N) ≫
          ((Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b c).inv.app N) ≫
            (Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback c).obj N) ≫
              (Scheme.Modules.pullbackComp (a ≫ b) c).hom.app N) := by
        rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
        try rfl
    _ = _ := by
        rw [h]
        try rfl

theorem cg_hom_app_self {X Y : Scheme.{u}} {a : X ⟶ Y} (h : a = a) (N : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app N = 𝟙 _ := by
  simp [Scheme.Modules.pullbackCongr]

theorem cg_trans {X Y : Scheme.{u}} {a b c : X ⟶ Y} (h : a = b) (h' : b = c) (N : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app N ≫ (Scheme.Modules.pullbackCongr h').hom.app N =
      (Scheme.Modules.pullbackCongr (h.trans h')).hom.app N := by
  subst h' h; simp [Scheme.Modules.pullbackCongr]

theorem cg_inv {X Y : Scheme.{u}} {a b : X ⟶ Y} (h : a = b) (N : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).inv.app N = (Scheme.Modules.pullbackCongr h.symm).hom.app N := by
  subst h; simp [Scheme.Modules.pullbackCongr]

theorem map_cg_pc {W X Y : Scheme.{u}} (a : W ⟶ X) {b b' : X ⟶ Y} (h : b = b') (N : Y.Modules) :
    (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackCongr h).hom.app N) ≫
        (Scheme.Modules.pullbackComp a b').hom.app N =
    (Scheme.Modules.pullbackComp a b).hom.app N ≫
      (Scheme.Modules.pullbackCongr (show a ≫ b = a ≫ b' by rw [h])).hom.app N := by
  subst h; simp [Scheme.Modules.pullbackCongr]

theorem cg_pc {W X Y : Scheme.{u}} {a a' : W ⟶ X} (h : a = a') (b : X ⟶ Y) (N : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app ((Scheme.Modules.pullback b).obj N) ≫
        (Scheme.Modules.pullbackComp a' b).hom.app N =
    (Scheme.Modules.pullbackComp a b).hom.app N ≫
      (Scheme.Modules.pullbackCongr (show a ≫ b = a' ≫ b by rw [h])).hom.app N := by
  subst h; simp [Scheme.Modules.pullbackCongr]

theorem cg_unitIso {X Y : Scheme.{u}} {a a' : X ⟶ Y} (h : a = a') :
    (Scheme.Modules.pullbackCongr h).hom.app _ ≫ (Scheme.Modules.pullbackUnitIso a').hom =
      (Scheme.Modules.pullbackUnitIso a).hom := by
  subst h; simp [Scheme.Modules.pullbackCongr]

theorem pc_assoc_hom'' {W X Y Z : Scheme.{u}} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (N : Z.Modules) :
    (Scheme.Modules.pullbackComp a b).inv.app ((Scheme.Modules.pullback c).obj N) ≫
      (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b c).hom.app N) ≫
        (Scheme.Modules.pullbackComp a (b ≫ c)).hom.app N =
    (Scheme.Modules.pullbackComp (a ≫ b) c).hom.app N ≫
      (Scheme.Modules.pullbackCongr (Category.assoc a b c)).hom.app N := by
  rw [← cancel_epi ((Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback c).obj N)),
    Iso.hom_inv_id_app_assoc]
  have t := pc_assoc_hom' a b c N
  try dsimp only [Functor.comp_obj] at t
  try dsimp only [Functor.comp_obj]
  rw [reassoc_of% t, cg_trans, cg_hom_app_self, Category.comp_id]

theorem pullbackUnitIso_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.pullbackComp f g).inv.app (SheafOfModules.unit Z.ringCatSheaf) ≫
      (Scheme.Modules.pullback f).map (Scheme.Modules.pullbackUnitIso g).hom ≫
        (Scheme.Modules.pullbackUnitIso f).hom =
    (Scheme.Modules.pullbackUnitIso (f ≫ g)).hom := by
  let κ : ∀ {A B : Scheme.{u}} (h : A ⟶ B),
      (Scheme.Modules.pullback h).obj (SheafOfModules.unit B.ringCatSheaf) ⟶ SheafOfModules.unit A.ringCatSheaf :=
    fun h => SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom
  let η : ∀ {A B : Scheme.{u}} (h : A ⟶ B),
      SheafOfModules.unit B.ringCatSheaf ⟶ (Scheme.Modules.pushforward h).obj (SheafOfModules.unit A.ringCatSheaf) :=
    fun h => SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom
  have hu : ∀ {A B : Scheme.{u}} (h : A ⟶ B), (Scheme.Modules.pullbackUnitIso h).hom = κ h := fun h => rfl
  rw [hu, hu, hu]
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  have key : ∀ (c : Z.Modules) (b : X.Modules)
      (h : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj c) ⟶ b),
      (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _
          ((Scheme.Modules.pullbackComp f g).inv.app c ≫ h) =
        ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
            (Scheme.Modules.pullbackPushforwardAdjunction f)).homEquiv _ _ h ≫
          (Scheme.Modules.pushforwardComp f g).hom.app b := by
    intro c b h
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp]
    have u := unit_conjugateEquiv
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp (Scheme.Modules.pullbackPushforwardAdjunction f))
      (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)) (Scheme.Modules.pullbackComp f g).inv c
    rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at u
    calc (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app c ≫
            (Scheme.Modules.pushforward (f ≫ g)).map ((Scheme.Modules.pullbackComp f g).inv.app c) ≫
              (Scheme.Modules.pushforward (f ≫ g)).map h
        = (((Scheme.Modules.pullbackPushforwardAdjunction g).comp
              (Scheme.Modules.pullbackPushforwardAdjunction f)).unit.app c ≫
            (Scheme.Modules.pushforwardComp f g).hom.app ((Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f).obj c)) ≫
              (Scheme.Modules.pushforward (f ≫ g)).map h := by simp only [u, Category.assoc]
      _ = _ := by
        rw [Category.assoc]
        congr 1
  rw [key]
  have hcomp : ∀ (c : Z.Modules) (b : X.Modules)
      (h : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj c) ⟶ b),
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
          (Scheme.Modules.pullbackPushforwardAdjunction f)).homEquiv _ _ h =
        (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
          ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ h) := by
    intro c b h; rw [Adjunction.comp_homEquiv]; rfl
  rw [hcomp]
  have e1 : ∀ {A B : Scheme.{u}} (h : A ⟶ B),
      (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _ (κ h) = η h := by
    intro A B h; simp only [κ, η]
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit h.toRingCatSheafHom
  refine Eq.trans ?_ (e1 (f ≫ g)).symm
  have H : (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        ((Scheme.Modules.pullback f).map (κ g) ≫ κ f)) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app _ = η (f ≫ g) := by
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right, e1, e1]
    simp only [η]
    ext U x
    rfl
  exact H

noncomputable def rigAlong {X B Z : Scheme.{u}} (N : X.Modules) (ε : B ⟶ X)
    (ρ : (Scheme.Modules.pullback ε).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (z : Z ⟶ X) (w : Z ⟶ B) (h : z = w ≫ ε) :
    (Scheme.Modules.pullback z).obj N ≅ SheafOfModules.unit Z.ringCatSheaf :=
  (Scheme.Modules.pullbackCongr h).app N ≪≫ ((Scheme.Modules.pullbackComp w ε).app N).symm ≪≫
    (Scheme.Modules.pullback w).mapIso ρ ≪≫ Scheme.Modules.pullbackUnitIso w

theorem rigAlong_hom {X B Z : Scheme.{u}} (N : X.Modules) (ε : B ⟶ X)
    (ρ : (Scheme.Modules.pullback ε).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (z : Z ⟶ X) (w : Z ⟶ B) (h : z = w ≫ ε) :
    (rigAlong N ε ρ z w h).hom = (Scheme.Modules.pullbackCongr h).hom.app N ≫
      (Scheme.Modules.pullbackComp w ε).inv.app N ≫ (Scheme.Modules.pullback w).map ρ.hom ≫
        (Scheme.Modules.pullbackUnitIso w).hom := by
  simp [rigAlong]

theorem rigAlong_congr {X B Z : Scheme.{u}} (N : X.Modules) (ε : B ⟶ X)
    (ρ : (Scheme.Modules.pullback ε).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    {z z' : Z ⟶ X} (hz : z = z') {w w' : Z ⟶ B} (hw : w = w') (h : z = w ≫ ε) (h' : z' = w' ≫ ε) :
    rigAlong N ε ρ z w h = (Scheme.Modules.pullbackCongr hz).app N ≪≫ rigAlong N ε ρ z' w' h' := by
  subst hz hw
  ext
  simp [Scheme.Modules.pullbackCongr]

theorem transport_rigAlong {X B E P C : Scheme.{u}} (N : X.Modules) (ε : B ⟶ X)
    (ρ : (Scheme.Modules.pullback ε).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (q : P ⟶ X) (eP : C ⟶ P) (v : C ⟶ B) (hv : eP ≫ q = v ≫ ε)
    (m : E ⟶ P) (u : E ⟶ C) (hm : m = u ≫ eP) :
    (Scheme.Modules.pullbackCongr hm).app ((Scheme.Modules.pullback q).obj N) ≪≫
      ((Scheme.Modules.pullbackComp u eP).app ((Scheme.Modules.pullback q).obj N)).symm ≪≫
      (Scheme.Modules.pullback u).mapIso
        ((Scheme.Modules.pullbackComp eP q).app N ≪≫ rigAlong N ε ρ (eP ≫ q) v hv) ≪≫
      Scheme.Modules.pullbackUnitIso u =
    (Scheme.Modules.pullbackComp m q).app N ≪≫
      rigAlong N ε ρ (m ≫ q) (u ≫ v) (by rw [hm, Category.assoc, hv, Category.assoc]) := by
  subst hm
  refine Iso.ext ?_
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, rigAlong_hom,
    Functor.map_comp, Category.assoc, cg_hom_app_self, Category.id_comp, Functor.comp_obj]
  try dsimp only [Functor.comp_obj]
  have s1 : (Scheme.Modules.pullback u).map (Scheme.Modules.pullbackUnitIso v).hom ≫
      (Scheme.Modules.pullbackUnitIso u).hom =
      (Scheme.Modules.pullbackComp u v).hom.app _ ≫ (Scheme.Modules.pullbackUnitIso (u ≫ v)).hom := by
    rw [← pullbackUnitIso_comp u v, Iso.hom_inv_id_app_assoc]
    try rfl
  try dsimp only [Functor.comp_obj] at s1
  rw [s1]
  have s2 : (Scheme.Modules.pullback u).map ((Scheme.Modules.pullback v).map ρ.hom) ≫
      (Scheme.Modules.pullbackComp u v).hom.app (SheafOfModules.unit B.ringCatSheaf) =
      (Scheme.Modules.pullbackComp u v).hom.app ((Scheme.Modules.pullback ε).obj N) ≫
        (Scheme.Modules.pullback (u ≫ v)).map ρ.hom :=
    (Scheme.Modules.pullbackComp u v).hom.naturality ρ.hom
  try dsimp only [Functor.comp_obj] at s2
  rw [reassoc_of% s2]
  have s3a := pc_assoc_hom u v ε N
  have s3 := (Iso.eq_comp_inv ((Scheme.Modules.pullbackComp (u ≫ v) ε).app N)).mpr
    ((Category.assoc _ _ _).trans s3a)
  simp only [Iso.app_inv, Category.assoc] at s3
  try dsimp only [Functor.comp_obj] at s3
  rw [reassoc_of% s3]
  have s4 := map_cg_pc u hv N
  try dsimp only [Functor.comp_obj] at s4
  rw [reassoc_of% s4]
  have s5 := pc_assoc_hom'' u eP q N
  try dsimp only [Functor.comp_obj] at s5
  rw [reassoc_of% s5]
  rw [reassoc_of% (cg_trans _ _ N)]
  rw [reassoc_of% (cg_trans _ _ N)]

theorem nf_coherence {X B E T P P' : Scheme.{u}} (N : X.Modules) (ε : B ⟶ X)
    (ρ : (Scheme.Modules.pullback ε).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (eT : E ⟶ T) (p : T ⟶ P) (q : P ⟶ X) (p' : T ⟶ P') (q' : P' ⟶ X) (hpq : p ≫ q = p' ≫ q')
    (w w' : E ⟶ B) (hw : w = w') (h : (eT ≫ p) ≫ q = w ≫ ε) (h' : (eT ≫ p') ≫ q' = w' ≫ ε) :
    (Scheme.Modules.pullbackComp eT p).app ((Scheme.Modules.pullback q).obj N) ≪≫
      (Scheme.Modules.pullbackComp (eT ≫ p) q).app N ≪≫ rigAlong N ε ρ ((eT ≫ p) ≫ q) w h =
    (Scheme.Modules.pullback eT).mapIso
        ((Scheme.Modules.pullbackComp p q).app N ≪≫ (Scheme.Modules.pullbackCongr hpq).app N ≪≫
          ((Scheme.Modules.pullbackComp p' q').app N).symm) ≪≫
      (Scheme.Modules.pullbackComp eT p').app ((Scheme.Modules.pullback q').obj N) ≪≫
      (Scheme.Modules.pullbackComp (eT ≫ p') q').app N ≪≫ rigAlong N ε ρ ((eT ≫ p') ≫ q') w' h' := by
  subst hw
  refine Iso.ext ?_
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, rigAlong_hom,
    Functor.map_comp, Category.assoc, Functor.comp_obj]
  try dsimp only [Functor.comp_obj]
  have t1 := pc_assoc_hom' eT p q N
  have t2 := pc_assoc_hom' eT p' q' N
  try dsimp only [Functor.comp_obj] at t1 t2
  rw [reassoc_of% t1, reassoc_of% t2]
  have s6 : (Scheme.Modules.pullback eT).map ((Scheme.Modules.pullbackComp p' q').inv.app N) ≫
      (Scheme.Modules.pullback eT).map ((Scheme.Modules.pullbackComp p' q').hom.app N) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  try dsimp only [Functor.comp_obj] at s6
  rw [reassoc_of% s6]
  have s7 := map_cg_pc eT hpq N
  try dsimp only [Functor.comp_obj] at s7
  rw [reassoc_of% s7]
  rw [reassoc_of% (cg_trans _ _ N)]
  rw [reassoc_of% (cg_trans _ _ N)]
  rw [reassoc_of% (cg_trans _ _ N)]

end AlgebraicGeometry.Scheme.Modules.RTKit

namespace RTAsm
open AlgebraicGeometry.Scheme.Modules.RTKit

noncomputable def NF {X B E T P : Scheme.{u}} (eT : E ⟶ T) (p : T ⟶ P) (q : P ⟶ X) (N : X.Modules) (ε : B ⟶ X)
    (ρ : (Scheme.Modules.pullback ε).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (w : E ⟶ B) (h : (eT ≫ p) ≫ q = w ≫ ε) :
    (Scheme.Modules.pullback eT).obj ((Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback q).obj N)) ≅
      SheafOfModules.unit E.ringCatSheaf :=
  (Scheme.Modules.pullbackComp eT p).app ((Scheme.Modules.pullback q).obj N) ≪≫
    (Scheme.Modules.pullbackComp (eT ≫ p) q).app N ≪≫ rigAlong N ε ρ ((eT ≫ p) ≫ q) w h

theorem mapIso_mapIso_eq_NF {X₁ X₂ B₁ B₂ E T P C : Scheme.{u}}
    (eT : E ⟶ T) (p : T ⟶ P) (eP : C ⟶ P) (u : E ⟶ C) (hsq : eT ≫ p = u ≫ eP)
    (q₁ : P ⟶ X₁) (q₂ : P ⟶ X₂) (N₁ : X₁.Modules) (N₂ : X₂.Modules)
    (ε₁ : B₁ ⟶ X₁) (ε₂ : B₂ ⟶ X₂)
    (ρ₁ : (Scheme.Modules.pullback ε₁).obj N₁ ≅ SheafOfModules.unit B₁.ringCatSheaf)
    (ρ₂ : (Scheme.Modules.pullback ε₂).obj N₂ ≅ SheafOfModules.unit B₂.ringCatSheaf)
    (v₁ : C ⟶ B₁) (v₂ : C ⟶ B₂) (hv₁ : eP ≫ q₁ = v₁ ≫ ε₁) (hv₂ : eP ≫ q₂ = v₂ ≫ ε₂)
    (φ : (Scheme.Modules.pullback q₁).obj N₁ ≅ (Scheme.Modules.pullback q₂).obj N₂)
    (hφ : (Scheme.Modules.pullback eP).mapIso φ =
      ((Scheme.Modules.pullbackComp eP q₁).app N₁ ≪≫ rigAlong N₁ ε₁ ρ₁ (eP ≫ q₁) v₁ hv₁) ≪≫
        ((Scheme.Modules.pullbackComp eP q₂).app N₂ ≪≫ rigAlong N₂ ε₂ ρ₂ (eP ≫ q₂) v₂ hv₂).symm) :
    (Scheme.Modules.pullback eT).mapIso ((Scheme.Modules.pullback p).mapIso φ) =
      NF eT p q₁ N₁ ε₁ ρ₁ (u ≫ v₁) (by rw [hsq, Category.assoc, hv₁, Category.assoc]) ≪≫
        (NF eT p q₂ N₂ ε₂ ρ₂ (u ≫ v₂) (by rw [hsq, Category.assoc, hv₂, Category.assoc])).symm := by
  refine (AlgebraicGeometry.Scheme.Modules.pullback_mapIso_pullback_mapIso_eq_of_pullback_mapIso_eq p eP eT u hsq _ _ _ _ φ hφ).trans ?_
  have t₁ := transport_rigAlong N₁ ε₁ ρ₁ q₁ eP v₁ hv₁ (eT ≫ p) u hsq
  have t₂ := transport_rigAlong N₂ ε₂ ρ₂ q₂ eP v₂ hv₂ (eT ≫ p) u hsq
  have e₁ := congrArg (fun z => (Scheme.Modules.pullbackComp eT p).app ((Scheme.Modules.pullback q₁).obj N₁) ≪≫ z) t₁
  have e₂ := congrArg (fun z => (Scheme.Modules.pullbackComp eT p).app ((Scheme.Modules.pullback q₂).obj N₂) ≪≫ z) t₂
  exact congrArg₂ (fun a b => a ≪≫ Iso.symm b) e₁ e₂

end RTAsm

theorem solution
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of S))
    {A' : Fin k → Scheme.{u}} (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (B i))) (ι : ∀ i, A' i ⟶ Y)
    [∀ i, IsOpenImmersion (ι i)]
    (hsq : ∀ i, CategoryTheory.IsPullback (ι i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))))
    (hsurj : ∀ y : ↥Y, ∃ (i : Fin k) (x : ↥(A' i)), (ι i).base x = y)
    (hΓ : ∀ i, Function.Surjective ((f' i).appTop).hom ∧
      ∀ r : B i, Function.Surjective
        ((pullback.snd (f' i) (Spec.map (CommRingCat.ofHom (algebraMap (B i) (Localization.Away r))))).appTop).hom)
    (e : ∀ i, Spec (CommRingCat.of (B i)) ⟶ A' i) (he : ∀ i, e i ≫ f' i = 𝟙 _)
    (heagree : ∀ (i j : Fin k) (C : Type u) [CommRing C] [Algebra S C] [IsLocalization.Away (r i * r j) C]
        (ρ₁ : B i →ₐ[S] C) (ρ₂ : B j →ₐ[S] C),
        Spec.map (CommRingCat.ofHom ρ₁.toRingHom) ≫ e i ≫ ι i = Spec.map (CommRingCat.ofHom ρ₂.toRingHom) ≫ e j ≫ ι j)
    (M : ∀ i, (A' i).Modules) (hM : ∀ i, Scheme.Modules.IsInvertible (M i))
    (hrig : ∀ i, Nonempty ((Scheme.Modules.pullback (e i)).obj (M i) ≅ SheafOfModules.unit (Spec (CommRingCat.of (B i))).ringCatSheaf))
    (hloc : ∀ (i j : Fin k) (q : ↥(Limits.pullback (ι i) (ι j))), ∃ U : (Spec (CommRingCat.of S)).Opens,
        (pullback.fst (ι i) (ι j) ≫ ι i ≫ f).base q ∈ U ∧
        Nonempty
          ((Scheme.Modules.pullback ((pullback.fst (ι i) (ι j) ≫ ι i ≫ f) ⁻¹ᵁ U).ι).obj
              ((Scheme.Modules.pullback (pullback.fst (ι i) (ι j))).obj (M i)) ≅
            (Scheme.Modules.pullback ((pullback.fst (ι i) (ι j) ≫ ι i ≫ f) ⁻¹ᵁ U).ι).obj
              ((Scheme.Modules.pullback (pullback.snd (ι i) (ι j))).obj (M j)))) :
    ∃ φ : ∀ i j : Fin k,
        (Scheme.Modules.pullback (Limits.pullback.fst (ι i) (ι j))).obj (M i) ≅
          (Scheme.Modules.pullback (Limits.pullback.snd (ι i) (ι j))).obj (M j),
      ∀ (i j l : Fin k) (T : Scheme.{u})
      (π₁₂ : T ⟶ Limits.pullback (ι i) (ι j)) (π₂₃ : T ⟶ Limits.pullback (ι j) (ι l)) (π₁₃ : T ⟶ Limits.pullback (ι i) (ι l))
      (h₂ : π₁₂ ≫ Limits.pullback.snd (ι i) (ι j) = π₂₃ ≫ Limits.pullback.fst (ι j) (ι l))
      (h₁ : π₁₃ ≫ Limits.pullback.fst (ι i) (ι l) = π₁₂ ≫ Limits.pullback.fst (ι i) (ι j))
      (h₃ : π₁₃ ≫ Limits.pullback.snd (ι i) (ι l) = π₂₃ ≫ Limits.pullback.snd (ι j) (ι l)),

      ((Scheme.Modules.pullbackComp π₁₂ (Limits.pullback.fst (ι i) (ι j))).app (M i)).symm ≪≫
          (Scheme.Modules.pullback π₁₂).mapIso (φ i j) ≪≫
          (Scheme.Modules.pullbackComp π₁₂ (Limits.pullback.snd (ι i) (ι j))).app (M j) ≪≫
          (Scheme.Modules.pullbackCongr h₂).app (M j) ≪≫
          ((Scheme.Modules.pullbackComp π₂₃ (Limits.pullback.fst (ι j) (ι l))).app (M j)).symm ≪≫
          (Scheme.Modules.pullback π₂₃).mapIso (φ j l) ≪≫
          (Scheme.Modules.pullbackComp π₂₃ (Limits.pullback.snd (ι j) (ι l))).app (M l) ≪≫
          (Scheme.Modules.pullbackCongr h₃.symm).app (M l)
        = (Scheme.Modules.pullbackCongr h₁.symm).app (M i) ≪≫
          ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.fst (ι i) (ι l))).app (M i)).symm ≪≫
          (Scheme.Modules.pullback π₁₃).mapIso (φ i l) ≪≫
          (Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.snd (ι i) (ι l))).app (M l) := by
  classical

  obtain ⟨ρ₁, ρ₂, fP, eP, hsec, hoverS, hfst, hsnd, hΓ₀, hΓA, htrip⟩ :=
    AlgebraicGeometry.Scheme.exists_overlaps_toSpecAway_section_of_charts_of_isPullback_of_surjective_appTop
      r B f f' ι hsq hΓ e he heagree

  let ρL : ∀ i j : Fin k, (Scheme.Modules.pullback (eP i j)).obj
      ((Scheme.Modules.pullback (Limits.pullback.fst (ι i) (ι j))).obj (M i)) ≅
        SheafOfModules.unit (Spec (CommRingCat.of (Localization.Away (r i * r j)))).ringCatSheaf :=
    fun i j => (Scheme.Modules.pullbackComp (eP i j) (Limits.pullback.fst (ι i) (ι j))).app (M i) ≪≫
      AlgebraicGeometry.Scheme.Modules.RTKit.rigAlong (M i) (e i) (Classical.choice (hrig i))
        (eP i j ≫ Limits.pullback.fst (ι i) (ι j)) (Spec.map (CommRingCat.ofHom (ρ₁ i j).toRingHom)) (hfst i j)
  let ρM : ∀ i j : Fin k, (Scheme.Modules.pullback (eP i j)).obj
      ((Scheme.Modules.pullback (Limits.pullback.snd (ι i) (ι j))).obj (M j)) ≅
        SheafOfModules.unit (Spec (CommRingCat.of (Localization.Away (r i * r j)))).ringCatSheaf :=
    fun i j => (Scheme.Modules.pullbackComp (eP i j) (Limits.pullback.snd (ι i) (ι j))).app (M j) ≪≫
      AlgebraicGeometry.Scheme.Modules.RTKit.rigAlong (M j) (e j) (Classical.choice (hrig j))
        (eP i j ≫ Limits.pullback.snd (ι i) (ι j)) (Spec.map (CommRingCat.ofHom (ρ₂ i j).toRingHom)) (hsnd i j)

  have hlocP : ∀ (i j : Fin k) (s : ↥(Spec (CommRingCat.of (Localization.Away (r i * r j))))),
      ∃ U : (Spec (CommRingCat.of (Localization.Away (r i * r j)))).Opens, s ∈ U ∧
        Nonempty ((Scheme.Modules.pullback ((fP i j) ⁻¹ᵁ U).ι).obj
            ((Scheme.Modules.pullback (Limits.pullback.fst (ι i) (ι j))).obj (M i)) ≅
          (Scheme.Modules.pullback ((fP i j) ⁻¹ᵁ U).ι).obj
            ((Scheme.Modules.pullback (Limits.pullback.snd (ι i) (ι j))).obj (M j))) := by
    intro i j s
    obtain ⟨U, hqU, hne⟩ := hloc i j ((eP i j).base s)
    refine ⟨Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i * r j)))) ⁻¹ᵁ U, ?_, ?_⟩
    · change (eP i j ≫ Limits.pullback.fst (ι i) (ι j) ≫ ι i ≫ f).base s ∈ U at hqU
      rwa [← hoverS i j, reassoc_of% (hsec i j)] at hqU
    · have hV : (fP i j) ⁻¹ᵁ (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i * r j)))) ⁻¹ᵁ U) =
          (Limits.pullback.fst (ι i) (ι j) ≫ ι i ≫ f) ⁻¹ᵁ U := by
        rw [← Scheme.Hom.comp_preimage, hoverS]
      rw [hV]
      exact hne

  have hR1 := fun i j : Fin k =>
    AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_iso_pullback_mapIso_eq_of_locally_of_rigidified
      (fP i j) (eP i j) (hsec i j) (hΓ₀ i j) (hΓA i j)
      ((Scheme.Modules.pullback (Limits.pullback.fst (ι i) (ι j))).obj (M i))
      ((Scheme.Modules.pullback (Limits.pullback.snd (ι i) (ι j))).obj (M j))
      ((hM i).pullback _) ((hM j).pullback _) (ρL i j) (ρM i j) (hlocP i j)
  choose φ hφ using hR1
  refine ⟨φ, ?_⟩

  have h0 : ∀ (i j l : Fin k) (π₁₃ : Limits.pullback (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l)) ⟶ Limits.pullback (ι i) (ι l))
      (h₁ : π₁₃ ≫ Limits.pullback.fst (ι i) (ι l) = (Limits.pullback.fst (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l))) ≫ Limits.pullback.fst (ι i) (ι j))
      (h₃ : π₁₃ ≫ Limits.pullback.snd (ι i) (ι l) = (Limits.pullback.snd (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l))) ≫ Limits.pullback.snd (ι j) (ι l)),

      ((Scheme.Modules.pullbackComp (Limits.pullback.fst (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l))) (Limits.pullback.fst (ι i) (ι j))).app (M i)).symm ≪≫
          (Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l)))).mapIso (φ i j) ≪≫
          (Scheme.Modules.pullbackComp (Limits.pullback.fst (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l))) (Limits.pullback.snd (ι i) (ι j))).app (M j) ≪≫
          (Scheme.Modules.pullbackCongr (Limits.pullback.condition)).app (M j) ≪≫
          ((Scheme.Modules.pullbackComp (Limits.pullback.snd (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l))) (Limits.pullback.fst (ι j) (ι l))).app (M j)).symm ≪≫
          (Scheme.Modules.pullback (Limits.pullback.snd (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l)))).mapIso (φ j l) ≪≫
          (Scheme.Modules.pullbackComp (Limits.pullback.snd (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l))) (Limits.pullback.snd (ι j) (ι l))).app (M l) ≪≫
          (Scheme.Modules.pullbackCongr h₃.symm).app (M l)
        = (Scheme.Modules.pullbackCongr h₁.symm).app (M i) ≪≫
          ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.fst (ι i) (ι l))).app (M i)).symm ≪≫
          (Scheme.Modules.pullback π₁₃).mapIso (φ i l) ≪≫
          (Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.snd (ι i) (ι l))).app (M l) := by
    intro i j l π₁₃ h₁ h₃
    obtain ⟨fT, eT, σ₁₂, σ₂₃, σ₁₃, hTsec, hTΓ, hT12, hT23, hT13⟩ := htrip i j l π₁₃ h₁ h₃

    set p1 := Limits.pullback.fst (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l)) with hp1
    set p2 := Limits.pullback.snd (Limits.pullback.snd (ι i) (ι j)) (Limits.pullback.fst (ι j) (ι l)) with hp2
    set u₁₂ := Spec.map (CommRingCat.ofHom σ₁₂.toRingHom) with hu₁₂
    set u₂₃ := Spec.map (CommRingCat.ofHom σ₂₃.toRingHom) with hu₂₃
    set u₁₃ := Spec.map (CommRingCat.ofHom σ₁₃.toRingHom) with hu₁₃
    let ρi := Classical.choice (hrig i)
    let ρj := Classical.choice (hrig j)
    let ρl := Classical.choice (hrig l)

    have hw : ∀ (m : Fin k) {D D' : Type u} [CommRing D] [CommRing D'] [Algebra S D] [Algebra S D']
        (a : B m →ₐ[S] D) (a' : B m →ₐ[S] D')
        (b : D →ₐ[S] Localization.Away (r i * r j * r l)) (b' : D' →ₐ[S] Localization.Away (r i * r j * r l)),
        Spec.map (CommRingCat.ofHom b.toRingHom) ≫ Spec.map (CommRingCat.ofHom a.toRingHom) =
          Spec.map (CommRingCat.ofHom b'.toRingHom) ≫ Spec.map (CommRingCat.ofHom a'.toRingHom) := by
      intro m D D' _ _ _ _ a a' b b'
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact congrArg AlgHom.toRingHom
        ((IsLocalization.algHom_subsingleton (Submonoid.powers (r m))).elim (b.comp a) (b'.comp a'))

    have h12 := RTAsm.mapIso_mapIso_eq_NF eT p1 (eP i j) u₁₂ hT12
      (Limits.pullback.fst (ι i) (ι j)) (Limits.pullback.snd (ι i) (ι j)) (M i) (M j) (e i) (e j) ρi ρj
      (Spec.map (CommRingCat.ofHom (ρ₁ i j).toRingHom)) (Spec.map (CommRingCat.ofHom (ρ₂ i j).toRingHom))
      (hfst i j) (hsnd i j) (φ i j) (hφ i j)
    have h23raw := RTAsm.mapIso_mapIso_eq_NF eT p2 (eP j l) u₂₃ hT23
      (Limits.pullback.fst (ι j) (ι l)) (Limits.pullback.snd (ι j) (ι l)) (M j) (M l) (e j) (e l) ρj ρl
      (Spec.map (CommRingCat.ofHom (ρ₁ j l).toRingHom)) (Spec.map (CommRingCat.ofHom (ρ₂ j l).toRingHom))
      (hfst j l) (hsnd j l) (φ j l) (hφ j l)
    have h13raw := RTAsm.mapIso_mapIso_eq_NF eT π₁₃ (eP i l) u₁₃ hT13
      (Limits.pullback.fst (ι i) (ι l)) (Limits.pullback.snd (ι i) (ι l)) (M i) (M l) (e i) (e l) ρi ρl
      (Spec.map (CommRingCat.ofHom (ρ₁ i l).toRingHom)) (Spec.map (CommRingCat.ofHom (ρ₂ i l).toRingHom))
      (hfst i l) (hsnd i l) (φ i l) (hφ i l)

    have P₁ : (eT ≫ p1) ≫ (Limits.pullback.fst (ι i) (ι j)) = (u₁₂ ≫ Spec.map (CommRingCat.ofHom (ρ₁ i j).toRingHom)) ≫ e i := by rw [hT12, Category.assoc, hfst, Category.assoc]
    have P₁' : (eT ≫ π₁₃) ≫ (Limits.pullback.fst (ι i) (ι l)) = (u₁₃ ≫ Spec.map (CommRingCat.ofHom (ρ₁ i l).toRingHom)) ≫ e i := by rw [hT13, Category.assoc, hfst, Category.assoc]
    have P₂ : (eT ≫ p1) ≫ (Limits.pullback.snd (ι i) (ι j)) = (u₁₂ ≫ Spec.map (CommRingCat.ofHom (ρ₂ i j).toRingHom)) ≫ e j := by rw [hT12, Category.assoc, hsnd, Category.assoc]
    have P₂' : (eT ≫ p2) ≫ (Limits.pullback.fst (ι j) (ι l)) = (u₂₃ ≫ Spec.map (CommRingCat.ofHom (ρ₁ j l).toRingHom)) ≫ e j := by rw [hT23, Category.assoc, hfst, Category.assoc]
    have P₃ : (eT ≫ p2) ≫ (Limits.pullback.snd (ι j) (ι l)) = (u₂₃ ≫ Spec.map (CommRingCat.ofHom (ρ₂ j l).toRingHom)) ≫ e l := by rw [hT23, Category.assoc, hsnd, Category.assoc]
    have P₃' : (eT ≫ π₁₃) ≫ (Limits.pullback.snd (ι i) (ι l)) = (u₁₃ ≫ Spec.map (CommRingCat.ofHom (ρ₂ i l).toRingHom)) ≫ e l := by rw [hT13, Category.assoc, hsnd, Category.assoc]

    have c_i : RTAsm.NF eT p1 (Limits.pullback.fst (ι i) (ι j)) (M i) (e i) ρi (u₁₂ ≫ Spec.map (CommRingCat.ofHom (ρ₁ i j).toRingHom)) P₁ =
        (Scheme.Modules.pullback eT).mapIso ((Scheme.Modules.pullbackComp p1 (Limits.pullback.fst (ι i) (ι j))).app (M i) ≪≫ (Scheme.Modules.pullbackCongr h₁.symm).app (M i) ≪≫ ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.fst (ι i) (ι l))).app (M i)).symm) ≪≫ RTAsm.NF eT π₁₃ (Limits.pullback.fst (ι i) (ι l)) (M i) (e i) ρi (u₁₃ ≫ Spec.map (CommRingCat.ofHom (ρ₁ i l).toRingHom)) P₁' :=
      AlgebraicGeometry.Scheme.Modules.RTKit.nf_coherence (M i) (e i) ρi eT p1 (Limits.pullback.fst (ι i) (ι j)) π₁₃ (Limits.pullback.fst (ι i) (ι l)) h₁.symm _ _
        (hw i (ρ₁ i j) (ρ₁ i l) σ₁₂ σ₁₃) P₁ P₁'
    have c_j : RTAsm.NF eT p1 (Limits.pullback.snd (ι i) (ι j)) (M j) (e j) ρj (u₁₂ ≫ Spec.map (CommRingCat.ofHom (ρ₂ i j).toRingHom)) P₂ =
        (Scheme.Modules.pullback eT).mapIso ((Scheme.Modules.pullbackComp p1 (Limits.pullback.snd (ι i) (ι j))).app (M j) ≪≫ (Scheme.Modules.pullbackCongr (Limits.pullback.condition)).app (M j) ≪≫ ((Scheme.Modules.pullbackComp p2 (Limits.pullback.fst (ι j) (ι l))).app (M j)).symm) ≪≫ RTAsm.NF eT p2 (Limits.pullback.fst (ι j) (ι l)) (M j) (e j) ρj (u₂₃ ≫ Spec.map (CommRingCat.ofHom (ρ₁ j l).toRingHom)) P₂' :=
      AlgebraicGeometry.Scheme.Modules.RTKit.nf_coherence (M j) (e j) ρj eT p1 (Limits.pullback.snd (ι i) (ι j)) p2 (Limits.pullback.fst (ι j) (ι l)) Limits.pullback.condition _ _
        (hw j (ρ₂ i j) (ρ₁ j l) σ₁₂ σ₂₃) P₂ P₂'
    have c_l : RTAsm.NF eT p2 (Limits.pullback.snd (ι j) (ι l)) (M l) (e l) ρl (u₂₃ ≫ Spec.map (CommRingCat.ofHom (ρ₂ j l).toRingHom)) P₃ =
        (Scheme.Modules.pullback eT).mapIso ((Scheme.Modules.pullbackComp p2 (Limits.pullback.snd (ι j) (ι l))).app (M l) ≪≫ (Scheme.Modules.pullbackCongr h₃.symm).app (M l) ≪≫ ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.snd (ι i) (ι l))).app (M l)).symm) ≪≫ RTAsm.NF eT π₁₃ (Limits.pullback.snd (ι i) (ι l)) (M l) (e l) ρl (u₁₃ ≫ Spec.map (CommRingCat.ofHom (ρ₂ i l).toRingHom)) P₃' :=
      AlgebraicGeometry.Scheme.Modules.RTKit.nf_coherence (M l) (e l) ρl eT p2 (Limits.pullback.snd (ι j) (ι l)) π₁₃ (Limits.pullback.snd (ι i) (ι l)) h₃.symm _ _
        (hw l (ρ₂ j l) (ρ₂ i l) σ₂₃ σ₁₃) P₃ P₃'

    have h12' : (Scheme.Modules.pullback eT).mapIso ((Scheme.Modules.pullback p1).mapIso (φ i j)) = RTAsm.NF eT p1 (Limits.pullback.fst (ι i) (ι j)) (M i) (e i) ρi (u₁₂ ≫ Spec.map (CommRingCat.ofHom (ρ₁ i j).toRingHom)) P₁ ≪≫ (RTAsm.NF eT p1 (Limits.pullback.snd (ι i) (ι j)) (M j) (e j) ρj (u₁₂ ≫ Spec.map (CommRingCat.ofHom (ρ₂ i j).toRingHom)) P₂).symm := h12
    have h23c : (Scheme.Modules.pullback eT).mapIso (((Scheme.Modules.pullbackComp p1 (Limits.pullback.snd (ι i) (ι j))).app (M j) ≪≫ (Scheme.Modules.pullbackCongr (Limits.pullback.condition)).app (M j) ≪≫ ((Scheme.Modules.pullbackComp p2 (Limits.pullback.fst (ι j) (ι l))).app (M j)).symm) ≪≫ ((Scheme.Modules.pullback p2).mapIso (φ j l)) ≪≫ ((Scheme.Modules.pullbackComp p2 (Limits.pullback.snd (ι j) (ι l))).app (M l) ≪≫ (Scheme.Modules.pullbackCongr h₃.symm).app (M l) ≪≫ ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.snd (ι i) (ι l))).app (M l)).symm)) = ((Scheme.Modules.pullback eT).mapIso ((Scheme.Modules.pullbackComp p1 (Limits.pullback.snd (ι i) (ι j))).app (M j) ≪≫ (Scheme.Modules.pullbackCongr (Limits.pullback.condition)).app (M j) ≪≫ ((Scheme.Modules.pullbackComp p2 (Limits.pullback.fst (ι j) (ι l))).app (M j)).symm) ≪≫ RTAsm.NF eT p2 (Limits.pullback.fst (ι j) (ι l)) (M j) (e j) ρj (u₂₃ ≫ Spec.map (CommRingCat.ofHom (ρ₁ j l).toRingHom)) P₂') ≪≫ (RTAsm.NF eT π₁₃ (Limits.pullback.snd (ι i) (ι l)) (M l) (e l) ρl (u₁₃ ≫ Spec.map (CommRingCat.ofHom (ρ₂ i l).toRingHom)) P₃').symm :=
      calc (Scheme.Modules.pullback eT).mapIso (((Scheme.Modules.pullbackComp p1 (Limits.pullback.snd (ι i) (ι j))).app (M j) ≪≫ (Scheme.Modules.pullbackCongr (Limits.pullback.condition)).app (M j) ≪≫ ((Scheme.Modules.pullbackComp p2 (Limits.pullback.fst (ι j) (ι l))).app (M j)).symm) ≪≫ ((Scheme.Modules.pullback p2).mapIso (φ j l)) ≪≫ ((Scheme.Modules.pullbackComp p2 (Limits.pullback.snd (ι j) (ι l))).app (M l) ≪≫ (Scheme.Modules.pullbackCongr h₃.symm).app (M l) ≪≫ ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.snd (ι i) (ι l))).app (M l)).symm))
          = (Scheme.Modules.pullback eT).mapIso ((Scheme.Modules.pullbackComp p1 (Limits.pullback.snd (ι i) (ι j))).app (M j) ≪≫ (Scheme.Modules.pullbackCongr (Limits.pullback.condition)).app (M j) ≪≫ ((Scheme.Modules.pullbackComp p2 (Limits.pullback.fst (ι j) (ι l))).app (M j)).symm) ≪≫ ((Scheme.Modules.pullback eT).mapIso ((Scheme.Modules.pullback p2).mapIso (φ j l)) ≪≫ (Scheme.Modules.pullback eT).mapIso ((Scheme.Modules.pullbackComp p2 (Limits.pullback.snd (ι j) (ι l))).app (M l) ≪≫ (Scheme.Modules.pullbackCongr h₃.symm).app (M l) ≪≫ ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.snd (ι i) (ι l))).app (M l)).symm)) :=
            ((Scheme.Modules.pullback eT).mapIso_trans _ _).trans (congrArg (fun z => (Scheme.Modules.pullback eT).mapIso ((Scheme.Modules.pullbackComp p1 (Limits.pullback.snd (ι i) (ι j))).app (M j) ≪≫ (Scheme.Modules.pullbackCongr (Limits.pullback.condition)).app (M j) ≪≫ ((Scheme.Modules.pullbackComp p2 (Limits.pullback.fst (ι j) (ι l))).app (M j)).symm) ≪≫ z) ((Scheme.Modules.pullback eT).mapIso_trans _ _))
        _ = (Scheme.Modules.pullback eT).mapIso ((Scheme.Modules.pullbackComp p1 (Limits.pullback.snd (ι i) (ι j))).app (M j) ≪≫ (Scheme.Modules.pullbackCongr (Limits.pullback.condition)).app (M j) ≪≫ ((Scheme.Modules.pullbackComp p2 (Limits.pullback.fst (ι j) (ι l))).app (M j)).symm) ≪≫ ((RTAsm.NF eT p2 (Limits.pullback.fst (ι j) (ι l)) (M j) (e j) ρj (u₂₃ ≫ Spec.map (CommRingCat.ofHom (ρ₁ j l).toRingHom)) P₂' ≪≫ (RTAsm.NF eT p2 (Limits.pullback.snd (ι j) (ι l)) (M l) (e l) ρl (u₂₃ ≫ Spec.map (CommRingCat.ofHom (ρ₂ j l).toRingHom)) P₃).symm) ≪≫ (Scheme.Modules.pullback eT).mapIso ((Scheme.Modules.pullbackComp p2 (Limits.pullback.snd (ι j) (ι l))).app (M l) ≪≫ (Scheme.Modules.pullbackCongr h₃.symm).app (M l) ≪≫ ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.snd (ι i) (ι l))).app (M l)).symm)) :=
            congrArg (fun z => (Scheme.Modules.pullback eT).mapIso ((Scheme.Modules.pullbackComp p1 (Limits.pullback.snd (ι i) (ι j))).app (M j) ≪≫ (Scheme.Modules.pullbackCongr (Limits.pullback.condition)).app (M j) ≪≫ ((Scheme.Modules.pullbackComp p2 (Limits.pullback.fst (ι j) (ι l))).app (M j)).symm) ≪≫ (z ≪≫ (Scheme.Modules.pullback eT).mapIso ((Scheme.Modules.pullbackComp p2 (Limits.pullback.snd (ι j) (ι l))).app (M l) ≪≫ (Scheme.Modules.pullbackCongr h₃.symm).app (M l) ≪≫ ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.snd (ι i) (ι l))).app (M l)).symm))) h23raw
        _ = (Scheme.Modules.pullback eT).mapIso ((Scheme.Modules.pullbackComp p1 (Limits.pullback.snd (ι i) (ι j))).app (M j) ≪≫ (Scheme.Modules.pullbackCongr (Limits.pullback.condition)).app (M j) ≪≫ ((Scheme.Modules.pullbackComp p2 (Limits.pullback.fst (ι j) (ι l))).app (M j)).symm) ≪≫ ((RTAsm.NF eT p2 (Limits.pullback.fst (ι j) (ι l)) (M j) (e j) ρj (u₂₃ ≫ Spec.map (CommRingCat.ofHom (ρ₁ j l).toRingHom)) P₂' ≪≫ ((Scheme.Modules.pullback eT).mapIso ((Scheme.Modules.pullbackComp p2 (Limits.pullback.snd (ι j) (ι l))).app (M l) ≪≫ (Scheme.Modules.pullbackCongr h₃.symm).app (M l) ≪≫ ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.snd (ι i) (ι l))).app (M l)).symm) ≪≫ RTAsm.NF eT π₁₃ (Limits.pullback.snd (ι i) (ι l)) (M l) (e l) ρl (u₁₃ ≫ Spec.map (CommRingCat.ofHom (ρ₂ i l).toRingHom)) P₃').symm) ≪≫ (Scheme.Modules.pullback eT).mapIso ((Scheme.Modules.pullbackComp p2 (Limits.pullback.snd (ι j) (ι l))).app (M l) ≪≫ (Scheme.Modules.pullbackCongr h₃.symm).app (M l) ≪≫ ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.snd (ι i) (ι l))).app (M l)).symm)) :=
            congrArg (fun z => (Scheme.Modules.pullback eT).mapIso ((Scheme.Modules.pullbackComp p1 (Limits.pullback.snd (ι i) (ι j))).app (M j) ≪≫ (Scheme.Modules.pullbackCongr (Limits.pullback.condition)).app (M j) ≪≫ ((Scheme.Modules.pullbackComp p2 (Limits.pullback.fst (ι j) (ι l))).app (M j)).symm) ≪≫ ((RTAsm.NF eT p2 (Limits.pullback.fst (ι j) (ι l)) (M j) (e j) ρj (u₂₃ ≫ Spec.map (CommRingCat.ofHom (ρ₁ j l).toRingHom)) P₂' ≪≫ Iso.symm z) ≪≫ (Scheme.Modules.pullback eT).mapIso ((Scheme.Modules.pullbackComp p2 (Limits.pullback.snd (ι j) (ι l))).app (M l) ≪≫ (Scheme.Modules.pullbackCongr h₃.symm).app (M l) ≪≫ ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.snd (ι i) (ι l))).app (M l)).symm))) c_l
        _ = ((Scheme.Modules.pullback eT).mapIso ((Scheme.Modules.pullbackComp p1 (Limits.pullback.snd (ι i) (ι j))).app (M j) ≪≫ (Scheme.Modules.pullbackCongr (Limits.pullback.condition)).app (M j) ≪≫ ((Scheme.Modules.pullbackComp p2 (Limits.pullback.fst (ι j) (ι l))).app (M j)).symm) ≪≫ RTAsm.NF eT p2 (Limits.pullback.fst (ι j) (ι l)) (M j) (e j) ρj (u₂₃ ≫ Spec.map (CommRingCat.ofHom (ρ₁ j l).toRingHom)) P₂') ≪≫ (RTAsm.NF eT π₁₃ (Limits.pullback.snd (ι i) (ι l)) (M l) (e l) ρl (u₁₃ ≫ Spec.map (CommRingCat.ofHom (ρ₂ i l).toRingHom)) P₃').symm := by
            simp only [Iso.trans_symm, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
            try (dsimp only [Functor.comp_obj]); try rfl
    have h23 : (Scheme.Modules.pullback eT).mapIso (((Scheme.Modules.pullbackComp p1 (Limits.pullback.snd (ι i) (ι j))).app (M j) ≪≫ (Scheme.Modules.pullbackCongr (Limits.pullback.condition)).app (M j) ≪≫ ((Scheme.Modules.pullbackComp p2 (Limits.pullback.fst (ι j) (ι l))).app (M j)).symm) ≪≫ ((Scheme.Modules.pullback p2).mapIso (φ j l)) ≪≫ ((Scheme.Modules.pullbackComp p2 (Limits.pullback.snd (ι j) (ι l))).app (M l) ≪≫ (Scheme.Modules.pullbackCongr h₃.symm).app (M l) ≪≫ ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.snd (ι i) (ι l))).app (M l)).symm)) = RTAsm.NF eT p1 (Limits.pullback.snd (ι i) (ι j)) (M j) (e j) ρj (u₁₂ ≫ Spec.map (CommRingCat.ofHom (ρ₂ i j).toRingHom)) P₂ ≪≫ (RTAsm.NF eT π₁₃ (Limits.pullback.snd (ι i) (ι l)) (M l) (e l) ρl (u₁₃ ≫ Spec.map (CommRingCat.ofHom (ρ₂ i l).toRingHom)) P₃').symm :=
      h23c.trans (congrArg (fun z => z ≪≫ (RTAsm.NF eT π₁₃ (Limits.pullback.snd (ι i) (ι l)) (M l) (e l) ρl (u₁₃ ≫ Spec.map (CommRingCat.ofHom (ρ₂ i l).toRingHom)) P₃').symm) c_j.symm)
    have h13 : (Scheme.Modules.pullback eT).mapIso (((Scheme.Modules.pullbackComp p1 (Limits.pullback.fst (ι i) (ι j))).app (M i) ≪≫ (Scheme.Modules.pullbackCongr h₁.symm).app (M i) ≪≫ ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.fst (ι i) (ι l))).app (M i)).symm) ≪≫ ((Scheme.Modules.pullback π₁₃).mapIso (φ i l))) = RTAsm.NF eT p1 (Limits.pullback.fst (ι i) (ι j)) (M i) (e i) ρi (u₁₂ ≫ Spec.map (CommRingCat.ofHom (ρ₁ i j).toRingHom)) P₁ ≪≫ (RTAsm.NF eT π₁₃ (Limits.pullback.snd (ι i) (ι l)) (M l) (e l) ρl (u₁₃ ≫ Spec.map (CommRingCat.ofHom (ρ₂ i l).toRingHom)) P₃').symm :=
      calc (Scheme.Modules.pullback eT).mapIso (((Scheme.Modules.pullbackComp p1 (Limits.pullback.fst (ι i) (ι j))).app (M i) ≪≫ (Scheme.Modules.pullbackCongr h₁.symm).app (M i) ≪≫ ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.fst (ι i) (ι l))).app (M i)).symm) ≪≫ ((Scheme.Modules.pullback π₁₃).mapIso (φ i l)))
          = (Scheme.Modules.pullback eT).mapIso ((Scheme.Modules.pullbackComp p1 (Limits.pullback.fst (ι i) (ι j))).app (M i) ≪≫ (Scheme.Modules.pullbackCongr h₁.symm).app (M i) ≪≫ ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.fst (ι i) (ι l))).app (M i)).symm) ≪≫ (Scheme.Modules.pullback eT).mapIso ((Scheme.Modules.pullback π₁₃).mapIso (φ i l)) := (Scheme.Modules.pullback eT).mapIso_trans _ _
        _ = (Scheme.Modules.pullback eT).mapIso ((Scheme.Modules.pullbackComp p1 (Limits.pullback.fst (ι i) (ι j))).app (M i) ≪≫ (Scheme.Modules.pullbackCongr h₁.symm).app (M i) ≪≫ ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.fst (ι i) (ι l))).app (M i)).symm) ≪≫ (RTAsm.NF eT π₁₃ (Limits.pullback.fst (ι i) (ι l)) (M i) (e i) ρi (u₁₃ ≫ Spec.map (CommRingCat.ofHom (ρ₁ i l).toRingHom)) P₁' ≪≫ (RTAsm.NF eT π₁₃ (Limits.pullback.snd (ι i) (ι l)) (M l) (e l) ρl (u₁₃ ≫ Spec.map (CommRingCat.ofHom (ρ₂ i l).toRingHom)) P₃').symm) := congrArg (fun z => (Scheme.Modules.pullback eT).mapIso ((Scheme.Modules.pullbackComp p1 (Limits.pullback.fst (ι i) (ι j))).app (M i) ≪≫ (Scheme.Modules.pullbackCongr h₁.symm).app (M i) ≪≫ ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.fst (ι i) (ι l))).app (M i)).symm) ≪≫ z) h13raw
        _ = ((Scheme.Modules.pullback eT).mapIso ((Scheme.Modules.pullbackComp p1 (Limits.pullback.fst (ι i) (ι j))).app (M i) ≪≫ (Scheme.Modules.pullbackCongr h₁.symm).app (M i) ≪≫ ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.fst (ι i) (ι l))).app (M i)).symm) ≪≫ RTAsm.NF eT π₁₃ (Limits.pullback.fst (ι i) (ι l)) (M i) (e i) ρi (u₁₃ ≫ Spec.map (CommRingCat.ofHom (ρ₁ i l).toRingHom)) P₁') ≪≫ (RTAsm.NF eT π₁₃ (Limits.pullback.snd (ι i) (ι l)) (M l) (e l) ρl (u₁₃ ≫ Spec.map (CommRingCat.ofHom (ρ₂ i l).toRingHom)) P₃').symm := (Iso.trans_assoc _ _ _).symm
        _ = RTAsm.NF eT p1 (Limits.pullback.fst (ι i) (ι j)) (M i) (e i) ρi (u₁₂ ≫ Spec.map (CommRingCat.ofHom (ρ₁ i j).toRingHom)) P₁ ≪≫ (RTAsm.NF eT π₁₃ (Limits.pullback.snd (ι i) (ι l)) (M l) (e l) ρl (u₁₃ ≫ Spec.map (CommRingCat.ofHom (ρ₂ i l).toRingHom)) P₃').symm := congrArg (fun z => z ≪≫ (RTAsm.NF eT π₁₃ (Limits.pullback.snd (ι i) (ι l)) (M l) (e l) ρl (u₁₃ ≫ Spec.map (CommRingCat.ofHom (ρ₂ i l).toRingHom)) P₃').symm) c_i.symm

    have hR2 : ((Scheme.Modules.pullback p1).mapIso (φ i j)) ≪≫ (((Scheme.Modules.pullbackComp p1 (Limits.pullback.snd (ι i) (ι j))).app (M j) ≪≫ (Scheme.Modules.pullbackCongr (Limits.pullback.condition)).app (M j) ≪≫ ((Scheme.Modules.pullbackComp p2 (Limits.pullback.fst (ι j) (ι l))).app (M j)).symm) ≪≫ ((Scheme.Modules.pullback p2).mapIso (φ j l)) ≪≫ ((Scheme.Modules.pullbackComp p2 (Limits.pullback.snd (ι j) (ι l))).app (M l) ≪≫ (Scheme.Modules.pullbackCongr h₃.symm).app (M l) ≪≫ ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.snd (ι i) (ι l))).app (M l)).symm)) = (((Scheme.Modules.pullbackComp p1 (Limits.pullback.fst (ι i) (ι j))).app (M i) ≪≫ (Scheme.Modules.pullbackCongr h₁.symm).app (M i) ≪≫ ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.fst (ι i) (ι l))).app (M i)).symm) ≪≫ ((Scheme.Modules.pullback π₁₃).mapIso (φ i l))) :=
      AlgebraicGeometry.Scheme.Modules.IsInvertible.trans_eq_of_pullback_mapIso_eq_of_surjective_appTop fT eT hTsec hTΓ
        ((Scheme.Modules.pullback p1).obj ((Scheme.Modules.pullback (Limits.pullback.fst (ι i) (ι j))).obj (M i)))
        ((Scheme.Modules.pullback p1).obj ((Scheme.Modules.pullback (Limits.pullback.snd (ι i) (ι j))).obj (M j)))
        ((Scheme.Modules.pullback π₁₃).obj ((Scheme.Modules.pullback (Limits.pullback.snd (ι i) (ι l))).obj (M l)))
        (((hM i).pullback _).pullback _)
        (RTAsm.NF eT p1 (Limits.pullback.fst (ι i) (ι j)) (M i) (e i) ρi (u₁₂ ≫ Spec.map (CommRingCat.ofHom (ρ₁ i j).toRingHom)) P₁) (RTAsm.NF eT p1 (Limits.pullback.snd (ι i) (ι j)) (M j) (e j) ρj (u₁₂ ≫ Spec.map (CommRingCat.ofHom (ρ₂ i j).toRingHom)) P₂) (RTAsm.NF eT π₁₃ (Limits.pullback.snd (ι i) (ι l)) (M l) (e l) ρl (u₁₃ ≫ Spec.map (CommRingCat.ofHom (ρ₂ i l).toRingHom)) P₃')
        ((Scheme.Modules.pullback p1).mapIso (φ i j)) (((Scheme.Modules.pullbackComp p1 (Limits.pullback.snd (ι i) (ι j))).app (M j) ≪≫ (Scheme.Modules.pullbackCongr (Limits.pullback.condition)).app (M j) ≪≫ ((Scheme.Modules.pullbackComp p2 (Limits.pullback.fst (ι j) (ι l))).app (M j)).symm) ≪≫ ((Scheme.Modules.pullback p2).mapIso (φ j l)) ≪≫ ((Scheme.Modules.pullbackComp p2 (Limits.pullback.snd (ι j) (ι l))).app (M l) ≪≫ (Scheme.Modules.pullbackCongr h₃.symm).app (M l) ≪≫ ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.snd (ι i) (ι l))).app (M l)).symm)) (((Scheme.Modules.pullbackComp p1 (Limits.pullback.fst (ι i) (ι j))).app (M i) ≪≫ (Scheme.Modules.pullbackCongr h₁.symm).app (M i) ≪≫ ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.fst (ι i) (ι l))).app (M i)).symm) ≪≫ ((Scheme.Modules.pullback π₁₃).mapIso (φ i l))) h12' h23 h13
    have hfin := congrArg (fun Φ => ((Scheme.Modules.pullbackComp p1 (Limits.pullback.fst (ι i) (ι j))).app (M i)).symm ≪≫ Φ ≪≫ (Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.snd (ι i) (ι l))).app (M l)) hR2
    dsimp only [Functor.comp_obj] at hfin ⊢
    simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id, Iso.trans_refl] at hfin
    exact hfin

  have key := AlgebraicGeometry.Scheme.Modules.forall_pullback_cocycle_of_cocycle_pullback_snd_fst
    (I := ULift.{u, 0} (Fin k)) (X := fun i => A' i.down) (fun i => ι i.down) (fun i => M i.down)
    (fun i j => φ i.down j.down) (fun i j l π₁₃ h₁ h₃ => h0 i.down j.down l.down π₁₃ h₁ h₃)
  intro i j l T π₁₂ π₂₃ π₁₃ h₂ h₁ h₃
  exact key ⟨i⟩ ⟨j⟩ ⟨l⟩ T π₁₂ π₂₃ π₁₃ h₂ h₁ h₃

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_pullback_iso_cocycle_of_charts_of_rigidified_of_surjective_appTop
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_pullback_iso_cocycle_of_charts_of_rigidified_of_surjective_appTop (solution)
