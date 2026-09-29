-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_abelJacobi_of_representsRelSubPic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/b8e0c0ff-a28f-5603-aef0-c9363d69e3a6

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_twistModule_and_nonempty_pullback_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_of_iso_pointSubBasepoint
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_abelJacobi_of_representsRelSubPic

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_abelJacobi_of_representsRelSubPic.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_abelJacobi_of_representsRelSubPic.AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral Spec Scheme IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.dual Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule RelEffCartierDiv mapOnProdOver RelEffCartierDiv.I graphOver graphOver_fst graphOver_snd RelEffCartierDiv.ofPoint Scheme.IdealSheafData.IsInvertible RelEffCartierDiv.isInvertible_I RelEffCartierDiv.isInvertible_twistModule_and_nonempty_pullback_iso Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field RelEffCartierDiv.pullbackAlong_ofPoint Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection RigidifiedLineBundle RepresentsRelSubPic fibreAt IsAlgEquivZero algEquivZeroCut sectionIdeal Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso pointSubBasepointModule IsAlgEquivZero.of_iso_pointSubBasepoint"
namespace AbelJacobiGlue
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

theorem ofPoint_congr_point {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] {T : Scheme.{u}}
    {g : T ⟶ S} {a b : T ⟶ 𝒞} (h : a = b) (ha : a ≫ f = g) (hb : b ≫ f = g) :
    RelEffCartierDiv.ofPoint f a ha = RelEffCartierDiv.ofPoint f b hb := by
  subst h; rfl

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem nonempty_pullback_baseChangeSnd_ajFamilyOver_iso
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t c) :
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd c x)).obj
        ((RelEffCartierDiv.ofPoint c (𝟙 C) (Category.id_comp c)).lineBundle ⊗
          (RelEffCartierDiv.ofPoint c (c ≫ ε.1)
            ((Category.assoc _ _ _).trans ((congrArg (c ≫ ·) ε.2).trans (Category.comp_id c)))).idealModule) ≅
      (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
          ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule) := by

  have hbm : baseChangeSnd c x = mapOnProdOver c x.1 x.2 := by
    apply pullback.hom_ext <;>
      simp only [baseChangeSnd, mapOnProdOver, pullback.map, pullback.lift_fst, pullback.lift_snd,
        Category.comp_id]
  have hε : (c ≫ ε.1) ≫ c = c := by rw [Category.assoc, ε.2, Category.comp_id]
  have htε : (t ≫ ε.1) ≫ c = t := by rw [Category.assoc, ε.2, Category.comp_id]

  have h₁ : (RelEffCartierDiv.ofPoint c (𝟙 C) (Category.id_comp c)).pullbackAlong x.1 x.2 =
      RelEffCartierDiv.ofPoint c x.1 x.2 :=
    (RelEffCartierDiv.pullbackAlong_ofPoint c (𝟙 C) (Category.id_comp c) x.1 x.2).trans
      (ofPoint_congr_point c (Category.comp_id x.1) _ _)
  have h₂ : (RelEffCartierDiv.ofPoint c (c ≫ ε.1) hε).pullbackAlong x.1 x.2 =
      RelEffCartierDiv.ofPoint c (t ≫ ε.1) htε :=
    (RelEffCartierDiv.pullbackAlong_ofPoint c (c ≫ ε.1) hε x.1 x.2).trans
      (ofPoint_congr_point c (by rw [← Category.assoc, x.2]) _ _)

  have hI₁ : (RelEffCartierDiv.ofPoint c (𝟙 C) (Category.id_comp c)).I.IsInvertible :=
    RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint c (𝟙 C) (Category.id_comp c))
  have hI₁' : ((RelEffCartierDiv.ofPoint c (𝟙 C) (Category.id_comp c)).I.comap
      (mapOnProdOver c x.1 x.2)).IsInvertible :=
    RelEffCartierDiv.isInvertible_I
      ((RelEffCartierDiv.ofPoint c (𝟙 C) (Category.id_comp c)).pullbackAlong x.1 x.2)
  have hI₂ : (RelEffCartierDiv.ofPoint c (c ≫ ε.1) hε).I.IsInvertible :=
    RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint c (c ≫ ε.1) hε)
  have hI₂' : ((RelEffCartierDiv.ofPoint c (c ≫ ε.1) hε).I.comap (mapOnProdOver c x.1 x.2)).IsInvertible :=
    RelEffCartierDiv.isInvertible_I ((RelEffCartierDiv.ofPoint c (c ≫ ε.1) hε).pullbackAlong x.1 x.2)

  have hK₁ : (RelEffCartierDiv.ofPoint c (𝟙 C) (Category.id_comp c)).I.comap (mapOnProdOver c x.1 x.2) =
      (RelEffCartierDiv.ofPoint c x.1 x.2).I :=
    congrArg RelEffCartierDiv.I h₁
  have hK₂ : (RelEffCartierDiv.ofPoint c (c ≫ ε.1) hε).I.comap (mapOnProdOver c x.1 x.2) =
      (RelEffCartierDiv.ofPoint c (t ≫ ε.1) htε).I :=
    congrArg RelEffCartierDiv.I h₂

  have e₁ : (Scheme.Modules.pullback (mapOnProdOver c x.1 x.2)).obj
      (RelEffCartierDiv.ofPoint c (𝟙 C) (Category.id_comp c)).I.invModule ≅
        (RelEffCartierDiv.ofPoint c x.1 x.2).I.invModule :=
    (Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso
        (mapOnProdOver c x.1 x.2) hI₁ hI₁').some ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.invModule hK₁)

  have e₂ : (Scheme.Modules.pullback (mapOnProdOver c x.1 x.2)).obj
      (RelEffCartierDiv.ofPoint c (c ≫ ε.1) hε).I.module ≅
        (RelEffCartierDiv.ofPoint c (t ≫ ε.1) htε).I.module :=
    @asIso _ _ _ _
        ((RelEffCartierDiv.ofPoint c (c ≫ ε.1) hε).I.pullbackModuleComparison (mapOnProdOver c x.1 x.2))
        (Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison
          (mapOnProdOver c x.1 x.2) hI₂ hI₂') ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.module hK₂)

  exact ⟨(Scheme.Modules.pullbackCongr hbm).app _ ≪≫
    Scheme.Modules.pullbackTensorObjIso (mapOnProdOver c x.1 x.2) _ _ ≪≫ tensorIso e₁ e₂⟩

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem baseChangeSnd_snd {R : Type u} [CommRing R] {C T T' : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} (s : SchemeHomOver t' t) :
    baseChangeSnd c s ≫ pullback.snd c t = pullback.snd c t' ≫ s.1 := by
  unfold baseChangeSnd
  exact pullback.lift_snd _ _ _

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem rigSection_snd {R : Type u} [CommRing R] {C T : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (t : T ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    rigSection c t ε ≫ pullback.snd c t = 𝟙 T := by
  unfold rigSection
  exact pullback.lift_snd _ _ _

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

def pullbackBaseChangeSndPullbackSndIso {R : Type u} [CommRing R] {C T T' : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} (s : SchemeHomOver t' t) (F : T.Modules) :
    (Scheme.Modules.pullback (baseChangeSnd c s)).obj ((Scheme.Modules.pullback (pullback.snd c t)).obj F) ≅
      (Scheme.Modules.pullback (pullback.snd c t')).obj ((Scheme.Modules.pullback s.1).obj F) :=
  (Scheme.Modules.pullbackComp _ _).app F ≪≫ (Scheme.Modules.pullbackCongr (baseChangeSnd_snd c s)).app F ≪≫
    ((Scheme.Modules.pullbackComp _ _).app F).symm

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

def pullbackRigSectionPullbackSndIso {R : Type u} [CommRing R] {C T : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (t : T ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (F : T.Modules) :
    (Scheme.Modules.pullback (rigSection c t ε)).obj ((Scheme.Modules.pullback (pullback.snd c t)).obj F) ≅ F :=
  (Scheme.Modules.pullbackComp _ _).app F ≪≫ (Scheme.Modules.pullbackCongr (rigSection_snd c t ε)).app F ≪≫
    (Scheme.Modules.pullbackId T).app F

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem nonempty_pullback_fst_pointBundle_iso_pointSubBasepointModule
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ C) :
    Nonempty ((Scheme.Modules.pullback (pullback.fst (pullback.snd c (s ≫ c)) (𝟙 (Spec (CommRingCat.of k))))).obj
        ((RelEffCartierDiv.ofPoint c s rfl).lineBundle ⊗
          (RelEffCartierDiv.ofPoint c ((s ≫ c) ≫ ε.1)
            ((Category.assoc _ _ _).trans ((congrArg ((s ≫ c) ≫ ·) ε.2).trans (Category.comp_id _)))).idealModule) ≅
      pointSubBasepointModule (a := pullback.snd c (s ≫ c))
        ⟨graphOver c s rfl, graphOver_snd c s rfl⟩
        ⟨rigSection c (s ≫ c) ε, rigSection_snd c (s ≫ c) ε⟩) := by

  have hε : ((s ≫ c) ≫ ε.1) ≫ c = s ≫ c := by rw [Category.assoc, ε.2, Category.comp_id]
  have hrig : rigSection c (s ≫ c) ε = graphOver c ((s ≫ c) ≫ ε.1) hε := by
    apply pullback.hom_ext <;>
      simp only [rigSection, graphOver, pullback.lift_fst, pullback.lift_snd]

  have hpP : graphOver (pullback.snd c (s ≫ c)) (graphOver c s rfl) (graphOver_snd c s rfl) ≫
      pullback.fst (pullback.snd c (s ≫ c)) (𝟙 (Spec (CommRingCat.of k))) = graphOver c s rfl :=
    graphOver_fst _ _ _
  have hpE : graphOver (pullback.snd c (s ≫ c)) (rigSection c (s ≫ c) ε) (rigSection_snd c (s ≫ c) ε) ≫
      pullback.fst (pullback.snd c (s ≫ c)) (𝟙 (Spec (CommRingCat.of k))) =
        graphOver c ((s ≫ c) ≫ ε.1) hε :=
    (graphOver_fst _ _ _).trans hrig

  haveI : SmoothOfRelativeDimension 1 (pullback.snd c (s ≫ c)) :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange 1
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) c (s ≫ c) inferInstance

  have hI₁ : (graphOver c s rfl).ker.IsInvertible :=
    RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint c s rfl)
  have hI₁' : (graphOver (pullback.snd c (s ≫ c)) (graphOver c s rfl) (graphOver_snd c s rfl)).ker.IsInvertible :=
    RelEffCartierDiv.isInvertible_I
      (RelEffCartierDiv.ofPoint (pullback.snd c (s ≫ c)) (graphOver c s rfl) (graphOver_snd c s rfl))
  have hI₂ : (graphOver c ((s ≫ c) ≫ ε.1) hε).ker.IsInvertible :=
    RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint c ((s ≫ c) ≫ ε.1) hε)
  have hI₂' : (graphOver (pullback.snd c (s ≫ c)) (rigSection c (s ≫ c) ε)
      (rigSection_snd c (s ≫ c) ε)).ker.IsInvertible :=
    RelEffCartierDiv.isInvertible_I
      (RelEffCartierDiv.ofPoint (pullback.snd c (s ≫ c)) (rigSection c (s ≫ c) ε) (rigSection_snd c (s ≫ c) ε))

  obtain ⟨eP⟩ := (Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso
    (pullback.fst (pullback.snd c (s ≫ c)) (𝟙 (Spec (CommRingCat.of k))))
    (graphOver c s rfl)
    (graphOver (pullback.snd c (s ≫ c)) (graphOver c s rfl) (graphOver_snd c s rfl)) hpP hI₁ hI₁' 1).1
  obtain ⟨eE⟩ := (Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso
    (pullback.fst (pullback.snd c (s ≫ c)) (𝟙 (Spec (CommRingCat.of k))))
    (graphOver c ((s ≫ c) ≫ ε.1) hε)
    (graphOver (pullback.snd c (s ≫ c)) (rigSection c (s ≫ c) ε) (rigSection_snd c (s ≫ c) ε))
    hpE hI₂ hI₂' 1).2

  have eP' : (Scheme.Modules.pullback (pullback.fst (pullback.snd c (s ≫ c)) (𝟙 (Spec (CommRingCat.of k))))).obj
      (graphOver c s rfl).ker.invModule ≅
        (graphOver (pullback.snd c (s ≫ c)) (graphOver c s rfl) (graphOver_snd c s rfl)).ker.invModule :=
    (Scheme.Modules.pullback _).mapIso
        (eqToIso (congrArg Scheme.IdealSheafData.invModule (pow_one _).symm)) ≪≫ eP ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.invModule (pow_one _))
  have eE' : (Scheme.Modules.pullback (pullback.fst (pullback.snd c (s ≫ c)) (𝟙 (Spec (CommRingCat.of k))))).obj
      (graphOver c ((s ≫ c) ≫ ε.1) hε).ker.module ≅
        (graphOver (pullback.snd c (s ≫ c)) (rigSection c (s ≫ c) ε) (rigSection_snd c (s ≫ c) ε)).ker.module :=
    (Scheme.Modules.pullback _).mapIso
        (eqToIso (congrArg Scheme.IdealSheafData.module (pow_one _).symm)) ≪≫ eE ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.module (pow_one _))

  exact ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ tensorIso eP' eE'⟩

end AlgebraicGeometry.RelPicard.AbelJacobiGlue

open AlgebraicGeometry.RelPicard.AbelJacobiGlue in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) :
    ∃ aj : SchemeHomOver c D.toBase,
      ε.1 ≫ aj.1 = D.zeroSection ∧
      ∀ (K : Type u) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t c),
        Nonempty ((h.poincare.pullbackAlong
            ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule) := by
  haveI : IsSeparated c := inferInstance
  have hcε : (c ≫ ε.1) ≫ c = c := (Category.assoc _ _ _).trans ((congrArg (c ≫ ·) ε.2).trans (Category.comp_id c))

  let Δ : RelEffCartierDiv c 1 c := RelEffCartierDiv.ofPoint c (𝟙 C) (Category.id_comp c)
  obtain ⟨hNinv, ⟨rigN⟩⟩ := RelEffCartierDiv.isInvertible_twistModule_and_nonempty_pullback_iso c ε Δ
  let N : RigidifiedLineBundle c ε c := ⟨Δ.twistModule c ε, hNinv, ⟨rigN⟩⟩

  let L₁ : (pullback c c).Modules := Δ.lineBundle ⊗ ((sectionIdeal c ε c) ^ 1).module
  have hL₁ : Scheme.Modules.IsInvertible L₁ :=
    (RelEffCartierDiv.isInvertible_I Δ).isInvertible_invModule.tensor
      ((RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint c (c ≫ ε.1) hcε)).pow 1).isInvertible_module
  let Ed : C.Modules := Scheme.Modules.dual ((Scheme.Modules.pullback (rigSection c c ε)).obj L₁)
  have hEd : Scheme.Modules.IsInvertible Ed := (hL₁.pullback _).dual.1
  have hNL : N.L = L₁ ⊗ (Scheme.Modules.pullback (pullback.snd c c)).obj Ed := rfl

  have iL₁ : L₁ ≅ Δ.lineBundle ⊗ (RelEffCartierDiv.ofPoint c (c ≫ ε.1) hcε).idealModule :=
    Iso.refl _ ⊗ᵢ eqToIso (congrArg Scheme.IdealSheafData.module (pow_one _))

  have hNx : ∀ {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t' c),
      Nonempty ((N.pullbackAlong x).L ≅
        (Scheme.Modules.pullback (baseChangeSnd c x)).obj L₁ ⊗
          (Scheme.Modules.pullback (pullback.snd c t')).obj ((Scheme.Modules.pullback x.1).obj Ed)) := fun t' x =>
    ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (Iso.refl _ ⊗ᵢ pullbackBaseChangeSndPullbackSndIso c x Ed)⟩

  have hcut : (algEquivZeroCut c ε).P c N := by
    intro k _ _ s

    let κ := pullbackLeftPullbackSndIso c c s
    let xs : SchemeHomOver (s ≫ c) c := ⟨s, rfl⟩
    have hκ : κ.hom ≫ baseChangeSnd c xs = pullback.fst (pullback.snd c c) s := by
      apply pullback.hom_ext
      · unfold baseChangeSnd
        rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullbackLeftPullbackSndIso_hom_fst, Category.comp_id]
      · rw [Category.assoc, baseChangeSnd_snd, ← Category.assoc, pullbackLeftPullbackSndIso_hom_snd, pullback.condition]
    have hκsnd : κ.hom ≫ pullback.snd c (s ≫ c) = fibreAt c c s := pullbackLeftPullbackSndIso_hom_snd _ _ _
    have iFib : (Scheme.Modules.pullback (pullback.fst (pullback.snd c c) s)).obj N.L ≅
        (Scheme.Modules.pullback κ.hom).obj ((N.pullbackAlong xs).L) :=
      (Scheme.Modules.pullbackCongr hκ.symm).app _ ≪≫ ((Scheme.Modules.pullbackComp κ.hom (baseChangeSnd c xs)).app N.L).symm

    obtain ⟨i2⟩ := hNx (s ≫ c) xs
    obtain ⟨i3⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k
      ((Scheme.Modules.pullback xs.1).obj Ed) (hEd.pullback _)
    obtain ⟨i4⟩ := nonempty_pullback_baseChangeSnd_ajFamilyOver_iso R c ε (s ≫ c) xs
    have iPt := i2 ≪≫
      (((Scheme.Modules.pullback (baseChangeSnd c xs)).mapIso iL₁ ≪≫ i4) ⊗ᵢ
        ((Scheme.Modules.pullback (pullback.snd c (s ≫ c))).mapIso i3 ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _)) ≪≫
      ρ_ _

    obtain ⟨i6⟩ := nonempty_pullback_fst_pointBundle_iso_pointSubBasepointModule R c ε k s
    have hM := IsAlgEquivZero.of_iso_pointSubBasepoint (a := pullback.snd c (s ≫ c))
      ⟨graphOver c s rfl, graphOver_snd c s rfl⟩ ⟨rigSection c (s ≫ c) ε, rigSection_snd c (s ≫ c) ε⟩ i6
    exact (hM.pullback κ.hom hκsnd).of_iso ((Scheme.Modules.pullback κ.hom).mapIso iPt.symm ≪≫ iFib.symm)
  let aj : SchemeHomOver c D.toBase := h.classify c N hcut
  obtain ⟨iaj⟩ := h.classify_spec c N hcut

  have hcomp : ∀ {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t' c),
      Nonempty ((h.poincare.pullbackAlong
          ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (N.pullbackAlong x).L) := fun t' x =>
    ⟨(h.poincare.pullbackAlongPullbackAlongIso' aj x).symm ≪≫ (Scheme.Modules.pullback (baseChangeSnd c x)).mapIso iaj⟩
  refine ⟨aj, ?_, ?_⟩
  ·
    have hz : (⟨ε.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (ε.1 ≫ ·) aj.2).trans ε.2)⟩ :
        SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) D.toBase) = ⟨D.zeroSection, D.zeroSection_toBase⟩ := by
      apply h.ext_of_iso (𝟙 _)
      obtain ⟨i1⟩ := hcomp (𝟙 _) ε
      obtain ⟨i2⟩ := hNx (𝟙 _) ε
      obtain ⟨i4⟩ := nonempty_pullback_baseChangeSnd_ajFamilyOver_iso R c ε (𝟙 _) ε
      have hpt : RelEffCartierDiv.ofPoint c (𝟙 (Spec (CommRingCat.of R)) ≫ ε.1)
          ((Category.assoc _ _ _).trans ((congrArg (𝟙 (Spec (CommRingCat.of R)) ≫ ·) ε.2).trans (Category.comp_id _))) =
            RelEffCartierDiv.ofPoint c ε.1 ε.2 := by
        congr 1
      obtain ⟨i5⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso
        (RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint c ε.1 ε.2))
      have i15 : (Scheme.Modules.pullback (baseChangeSnd c ε)).obj L₁ ≅ 𝟙_ _ :=
        (Scheme.Modules.pullback _).mapIso iL₁ ≪≫ i4 ≪≫
          (Iso.refl _ ⊗ᵢ eqToIso (congrArg (fun D' : RelEffCartierDiv c 1 (𝟙 _) => D'.idealModule) hpt)) ≪≫ i5
      let F : (Spec (CommRingCat.of R)).Modules := (Scheme.Modules.pullback ε.1).obj Ed
      have iQ : (N.pullbackAlong ε).L ≅ (Scheme.Modules.pullback (pullback.snd c (𝟙 _))).obj F :=
        i2 ≪≫ (i15 ⊗ᵢ Iso.refl _) ≪≫ λ_ _
      obtain ⟨r⟩ := (N.pullbackAlong ε).rigidified
      have iF : F ≅ 𝟙_ _ :=
        (pullbackRigSectionPullbackSndIso c (𝟙 _) ε F).symm ≪≫
          (Scheme.Modules.pullback (rigSection c (𝟙 _) ε)).mapIso iQ.symm ≪≫ r
      exact ⟨i1 ≪≫ iQ ≪≫ (Scheme.Modules.pullback _).mapIso iF ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _ ≪≫
        h.zero.some.symm⟩
    exact congrArg Subtype.val hz
  · intro K _ t x
    obtain ⟨i1⟩ := hcomp t x
    obtain ⟨i2⟩ := hNx t x
    obtain ⟨i3⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field K
      ((Scheme.Modules.pullback x.1).obj Ed) (hEd.pullback _)
    obtain ⟨i4⟩ := nonempty_pullback_baseChangeSnd_ajFamilyOver_iso R c ε t x
    exact ⟨i1 ≪≫ i2 ≪≫
      (((Scheme.Modules.pullback (baseChangeSnd c x)).mapIso iL₁ ≪≫ i4) ⊗ᵢ
        ((Scheme.Modules.pullback (pullback.snd c t)).mapIso i3 ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _)) ≪≫
      ρ_ _⟩

end
end S_AlgebraicGeometry_RelPicard_exists_abelJacobi_of_representsRelSubPic
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_abelJacobi_of_representsRelSubPic (solution)
