-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_iso_rigidify_normModule_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/53dfb2fb-3612-5c22-bc20-e0c51bf53321

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_ModularCurve_HeckeProj
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_RigKerDualNumber
import Definitions.Def_AlgebraicGeometry_RelPicardStageHom
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import Definitions.Def_AlgebraicGeometry_TwoChartCechSerrePairingInt
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_CechH1PushPull

import Definitions.Def_AlgebraicGeometry_RigKerDualNumberBaseTransport
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_normModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_pullbackMap_of_comp_eq
import Theorems.Thm_CategoryTheory_IsPullback_fst_pullbackMap_of_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_iso_rigidify_normModule_baseChange
p2m_attr_erase "simp" "PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicCurve AlgebraicGeometry.Scheme.TwoAffineOpenCover"

namespace T2Sol

section MonoBase

variable (R : Type u) [CommRing R] (K : Type u) [CommRing K] [Algebra R K] [Mono (specMap R K)]
  {Y T : Scheme.{u}} (y : Y ⟶ Spec (.of K)) (t : T ⟶ Spec (.of K))

theorem isPullback_of_mono :
    IsPullback (pullback.fst y t) (pullback.snd y t) (y ≫ specMap R K) (t ≫ specMap R K) :=
  IsPullback.of_isLimit' ⟨by rw [← Category.assoc, pullback.condition, Category.assoc]⟩
    (PullbackCone.isLimitOfCompMono y t (specMap R K) _ (pullback.isLimit y t))

noncomputable def eY : Limits.pullback y t ≅ Limits.pullback (y ≫ specMap R K) (t ≫ specMap R K) :=
  (isPullback_of_mono R K y t).isoPullback

theorem eY_hom_fst :
    (eY R K y t).hom ≫ pullback.fst (y ≫ specMap R K) (t ≫ specMap R K) = pullback.fst y t :=
  (isPullback_of_mono R K y t).isoPullback_hom_fst

theorem eY_hom_snd :
    (eY R K y t).hom ≫ pullback.snd (y ≫ specMap R K) (t ≫ specMap R K) = pullback.snd y t :=
  (isPullback_of_mono R K y t).isoPullback_hom_snd

end MonoBase

section Squares

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (K : Type u) [CommRing K] [Algebra R K]
  [Mono (specMap R K)] {Y T : Scheme.{u}} (y : Y ⟶ Spec (.of K)) (t : T ⟶ Spec (.of K))
  (π : Y ⟶ C) (Hπ : π ≫ c = y ≫ specMap R K) (Hπ₁ : pullback.lift π y Hπ ≫ SmoothProperCurve.baseChange R c K = y)

theorem eY_curveChange :
    (eY R K y t).hom ≫ curveChange (c' := y ≫ specMap R K) π Hπ (t ≫ specMap R K) =
      curveChange (c' := y) (pullback.lift π y Hπ) Hπ₁ t ≫ (BaseChange.κ c K t).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, BaseChange.κ_hom_fst]
    simp only [curveChange, pullback.lift_fst, pullback.lift_fst_assoc]
    rw [← Category.assoc, eY_hom_fst, Category.assoc, pullback.lift_fst]
  · rw [Category.assoc, Category.assoc, BaseChange.κ_hom_snd]
    simp only [curveChange, pullback.lift_snd, Category.comp_id]
    rw [eY_hom_snd]

theorem eY_inv_curveChange :
    (eY R K y t).inv ≫ curveChange (c' := y) (pullback.lift π y Hπ) Hπ₁ t =
      curveChange (c' := y ≫ specMap R K) π Hπ (t ≫ specMap R K) ≫ (BaseChange.κ c K t).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, eY_curveChange, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem isPullback_curveChange :
    IsPullback (eY R K y t).inv (curveChange (c' := y ≫ specMap R K) π Hπ (t ≫ specMap R K))
      (curveChange (c' := y) (pullback.lift π y Hπ) Hπ₁ t) (BaseChange.κ c K t).inv :=
  IsPullback.of_horiz_isIso ⟨eY_inv_curveChange c K y t π Hπ Hπ₁⟩

omit [Mono (specMap R K)] in

theorem isPullback_fst_curveChange :
    IsPullback (pullback.fst y t) (curveChange (c' := y) (pullback.lift π y Hπ) Hπ₁ t) (pullback.lift π y Hπ)
      (pullback.fst (SmoothProperCurve.baseChange R c K) t) :=
  CategoryTheory.IsPullback.fst_pullbackMap_of_comp_eq _ _ _ _ Hπ₁

omit [Mono (specMap R K)] in
theorem finrank_curveChange [Flat (pullback.lift π y Hπ)] [IsFinite (pullback.lift π y Hπ)] (z) :
    (curveChange (c' := y) (pullback.lift π y Hπ) Hπ₁ t).finrank z =
      (pullback.lift π y Hπ).finrank (pullback.fst (SmoothProperCurve.baseChange R c K) t z) :=
  Scheme.Hom.finrank_pullbackMap_of_comp_eq _ _ _ _ Hπ₁ z

end Squares

section Rigidify

variable {T P P' : Scheme.{u}} (σ : T ⟶ P) (q : P ⟶ T) (σ' : T ⟶ P') (q' : P' ⟶ T) (e : P' ⟶ P)
  (hσ : σ' ≫ e = σ) (hq : e ≫ q = q')

noncomputable def pullbackRigidifyIso (L : P.Modules) :
    (Scheme.Modules.pullback e).obj (Scheme.Modules.rigidify σ q L) ≅
      Scheme.Modules.rigidify σ' q' ((Scheme.Modules.pullback e).obj L) :=
  Scheme.Modules.pullbackTensorObjIso e L _ ≪≫
    (Iso.refl _ ⊗ᵢ
      (((Scheme.Modules.pullbackComp e q).app _) ≪≫ (Scheme.Modules.pullbackCongr hq).app _ ≪≫
        (Scheme.Modules.pullback q').mapIso
          (Scheme.Modules.dualMapIso
            (((Scheme.Modules.pullbackCongr hσ.symm).app L) ≪≫ ((Scheme.Modules.pullbackComp σ' e).app L).symm))))

end Rigidify

section Classify

open AlgebraicGeometry.RelPicard.BaseTransport

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
  (K : Type u) [CommRing K] [Algebra R K]
  (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
  (h' : RepresentsRelSubPic (SmoothProperCurve.baseChange R c K) (SmoothProperCurve.sectionBaseChange K ε)
    (algEquivZeroCut (SmoothProperCurve.baseChange R c K) (SmoothProperCurve.sectionBaseChange K ε)) (D.baseChange K))
  (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε K
    (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R K), pullback.condition⟩)).L))
  {T : Scheme.{u}} (t : T ⟶ Spec (.of K))

noncomputable def fstPoint (b : SchemeHomOver t (D.baseChange K).toBase) : SchemeHomOver (t ≫ specMap R K) D.toBase :=
  postComp ⟨pullback.fst D.toBase (specMap R K), pullback.condition⟩ (BaseChange.overR K b)

theorem fstPoint_coe (b : SchemeHomOver t (D.baseChange K).toBase) :
    (fstPoint c K D t b).1 = b.1 ≫ pullback.fst D.toBase (specMap R K) := rfl

noncomputable def poincareFstIso (b : SchemeHomOver t (D.baseChange K).toBase) :
    (h.poincare.pullbackAlong (fstPoint c K D t b)).L ≅ (BaseChange.toR c ε K (h'.poincare.pullbackAlong b)).L :=
  (RigidifiedLineBundle.pullbackAlong_pullbackAlong_iso h.poincare _ _).symm ≪≫
    (BaseChange.toR_ofR_iso c ε K _).symm ≪≫
    BaseChange.toR_mapIso c ε K
      ((BaseChange.ofR_pullbackAlong_iso c ε K b _).symm ≪≫
        (RigidifiedLineBundle.pullbackAlong_mapIso b hP.some).symm)

theorem toR_mem (M : RigidifiedLineBundle (SmoothProperCurve.baseChange R c K) (SmoothProperCurve.sectionBaseChange K ε) t)
    (hM : (algEquivZeroCut (SmoothProperCurve.baseChange R c K) (SmoothProperCurve.sectionBaseChange K ε)).P t M) :
    (algEquivZeroCut c ε).P (t ≫ specMap R K) (BaseChange.toR c ε K M) := by
  have : (BaseChange.restrict c ε K (algEquivZeroCut c ε)).P t M := by
    rw [BaseChange.restrict_algEquivZeroCut]; exact hM
  exact (BaseChange.restrict_P c ε K _ t M).1 this

include hP in

theorem fstPoint_classify
    (M : RigidifiedLineBundle (SmoothProperCurve.baseChange R c K) (SmoothProperCurve.sectionBaseChange K ε) t)
    (hM : (algEquivZeroCut (SmoothProperCurve.baseChange R c K) (SmoothProperCurve.sectionBaseChange K ε)).P t M) :
    fstPoint c K D t (h'.classify t M hM) = h.classify (t ≫ specMap R K) (BaseChange.toR c ε K M) (toR_mem c ε K t M hM) :=
  h.classify_unique _ _ _ _
    ⟨poincareFstIso c ε K D h h' hP t _ ≪≫ BaseChange.toR_mapIso c ε K (h'.classify_spec t M hM).some⟩

end Classify

end T2Sol

open T2Sol AlgebraicGeometry.RelPicard.BaseTransport in
theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
    (K : Type u) [CommRing K] [Algebra R K] [Mono (specMap R K)]
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic (SmoothProperCurve.baseChange R c K) (SmoothProperCurve.sectionBaseChange K ε)
      (algEquivZeroCut (SmoothProperCurve.baseChange R c K) (SmoothProperCurve.sectionBaseChange K ε)) (D.baseChange K))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε K
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R K), pullback.condition⟩)).L))
    {Y : Scheme.{u}} (y : Y ⟶ Spec (.of K))
    (πα πβ : Y ⟶ C) (Hα : πα ≫ c = y ≫ specMap R K) (Hβ : πβ ≫ c = y ≫ specMap R K)
    [IsFinite (pullback.lift πα y Hα : Y ⟶ Limits.pullback c (specMap R K))]
    [Flat (pullback.lift πα y Hα : Y ⟶ Limits.pullback c (specMap R K))]
    [LocallyOfFinitePresentation (pullback.lift πα y Hα : Y ⟶ Limits.pullback c (specMap R K))]
    (d : ℕ) (hd : ∀ z, (pullback.lift πα y Hα : Y ⟶ Limits.pullback c (specMap R K)).finrank z = d)
    (φ₁ : SchemeHomOver D.toBase D.toBase)
    (hmoduli :
      ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (.of K))
          (M : RigidifiedLineBundle c ε (t' ≫ specMap R K))
          (hM : (algEquivZeroCut c ε).P (t' ≫ specMap R K) M),
        Nonempty ((h.poincare.pullbackAlong
            (NeronModelInfra.schemeHomOverComp (h.classify (t' ≫ specMap R K) M hM) φ₁)).L ≅
          Scheme.Modules.rigidify (rigSection c (t' ≫ specMap R K) ε) (pullback.snd c (t' ≫ specMap R K))
            (Scheme.Modules.normModule (curveChange (c' := y ≫ specMap R K) πα Hα (t' ≫ specMap R K)) d
              ((Scheme.Modules.pullback (curveChange (c' := y ≫ specMap R K) πβ Hβ (t' ≫ specMap R K))).obj M.L))))
    (φ₁K : SchemeHomOver (D.baseChange K).toBase (D.baseChange K).toBase)
    (hφ₁K : φ₁K.1 ≫ pullback.fst D.toBase (specMap R K) = pullback.fst D.toBase (specMap R K) ≫ φ₁.1)
    (Hα₁ : pullback.lift πα y Hα ≫ SmoothProperCurve.baseChange R c K = y)
    (Hβ₁ : pullback.lift πβ y Hβ ≫ SmoothProperCurve.baseChange R c K = y)
    (T : Scheme.{u}) (t : T ⟶ Spec (.of K))
    (M : RigidifiedLineBundle (SmoothProperCurve.baseChange R c K) (SmoothProperCurve.sectionBaseChange K ε) t)
    (hM : (algEquivZeroCut (SmoothProperCurve.baseChange R c K) (SmoothProperCurve.sectionBaseChange K ε)).P t M) :
    Nonempty ((h'.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp (h'.classify t M hM) φ₁K)).L ≅
      Scheme.Modules.rigidify
        (rigSection (SmoothProperCurve.baseChange R c K) t (SmoothProperCurve.sectionBaseChange K ε))
        (pullback.snd (SmoothProperCurve.baseChange R c K) t)
        (Scheme.Modules.normModule (curveChange (c' := y) (pullback.lift πα y Hα) Hα₁ t) d
          ((Scheme.Modules.pullback (curveChange (c' := y) (pullback.lift πβ y Hβ) Hβ₁ t)).obj M.L))) := by
  classical

  have hM₀ := toR_mem c ε K t M hM
  let b := h'.classify t M hM
  let a := h.classify (t ≫ specMap R K) (BaseChange.toR c ε K M) hM₀
  have hab : fstPoint c K D t b = a := fstPoint_classify c ε K D h h' hP t M hM

  have hcoe : (fstPoint c K D t (NeronModelInfra.schemeHomOverComp b φ₁K)).1 =
      (NeronModelInfra.schemeHomOverComp a φ₁).1 := by
    rw [fstPoint_coe, NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe, Category.assoc,
      hφ₁K, ← Category.assoc, ← fstPoint_coe, hab]
  let e1 : (h'.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b φ₁K)).L ≅
      (BaseChange.ofR c ε K (h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a φ₁))).L :=
    RigidifiedLineBundle.pullbackAlong_mapIso _ hP.some ≪≫
      BaseChange.ofR_pullbackAlong_iso c ε K _ _ ≪≫
      BaseChange.ofR_mapIso c ε K
        (RigidifiedLineBundle.pullbackAlong_pullbackAlong_iso h.poincare _ _ ≪≫
          RigidifiedLineBundle.pullbackAlong_congr_hom h.poincare _ _ hcoe)

  let e2 := (Scheme.Modules.pullback (BaseChange.κ c K t).hom).mapIso (hmoduli T t (BaseChange.toR c ε K M) hM₀).some

  let e3 := pullbackRigidifyIso (rigSection c (t ≫ specMap R K) ε) (pullback.snd c (t ≫ specMap R K))
    (rigSection (SmoothProperCurve.baseChange R c K) t (SmoothProperCurve.sectionBaseChange K ε))
    (pullback.snd (SmoothProperCurve.baseChange R c K) t) (BaseChange.κ c K t).hom
    (BaseChange.rigSection_κ_hom c ε K t) (BaseChange.κ_hom_snd c K t)
    (Scheme.Modules.normModule (curveChange (c' := y ≫ specMap R K) πα Hα (t ≫ specMap R K)) d
      ((Scheme.Modules.pullback (curveChange (c' := y ≫ specMap R K) πβ Hβ (t ≫ specMap R K))).obj
        (BaseChange.toR c ε K M).L))

  haveI : IsFinite (curveChange (c' := y) (pullback.lift πα y Hα) Hα₁ t) :=
    MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_fst_curveChange c K y t πα Hα Hα₁) inferInstance
  haveI : Flat (curveChange (c' := y) (pullback.lift πα y Hα) Hα₁ t) :=
    MorphismProperty.of_isPullback (P := @Flat) (isPullback_fst_curveChange c K y t πα Hα Hα₁) inferInstance
  haveI : LocallyOfFinitePresentation (curveChange (c' := y) (pullback.lift πα y Hα) Hα₁ t) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
      (isPullback_fst_curveChange c K y t πα Hα Hα₁) inferInstance
  have hrk : ∀ z, (curveChange (c' := y) (pullback.lift πα y Hα) Hα₁ t).finrank z = d := fun z => by
    rw [finrank_curveChange c K y t πα Hα Hα₁, hd]
  let L := (Scheme.Modules.pullback (curveChange (c' := y) (pullback.lift πβ y Hβ) Hβ₁ t)).obj M.L
  have hL : Scheme.Modules.IsInvertible L := M.isInvertible.pullback _
  obtain ⟨e4⟩ := Scheme.Modules.nonempty_pullback_normModule_iso
    (curveChange (c' := y) (pullback.lift πα y Hα) Hα₁ t) d hrk (BaseChange.κ c K t).inv
    (curveChange (c' := y ≫ specMap R K) πα Hα (t ≫ specMap R K)) (eY R K y t).inv
    (isPullback_curveChange c K y t πα Hα Hα₁) hL

  let e5 : (Scheme.Modules.pullback (eY R K y t).inv).obj L ≅
      (Scheme.Modules.pullback (curveChange (c' := y ≫ specMap R K) πβ Hβ (t ≫ specMap R K))).obj
        (BaseChange.toR c ε K M).L :=
    (Scheme.Modules.pullbackComp (eY R K y t).inv _).app M.L ≪≫
      (Scheme.Modules.pullbackCongr (eY_inv_curveChange c K y t πβ Hβ Hβ₁)).app M.L ≪≫
      ((Scheme.Modules.pullbackComp _ (BaseChange.κ c K t).inv).app M.L).symm

  let e6 : (Scheme.Modules.pullback (BaseChange.κ c K t).hom).obj
      (Scheme.Modules.normModule (curveChange (c' := y ≫ specMap R K) πα Hα (t ≫ specMap R K)) d
        ((Scheme.Modules.pullback (curveChange (c' := y ≫ specMap R K) πβ Hβ (t ≫ specMap R K))).obj
          (BaseChange.toR c ε K M).L)) ≅
      Scheme.Modules.normModule (curveChange (c' := y) (pullback.lift πα y Hα) Hα₁ t) d L :=
    (Scheme.Modules.pullback (BaseChange.κ c K t).hom).mapIso
        ((Scheme.Modules.normModuleMapIso _ d e5).symm ≪≫ e4.symm) ≪≫
      (Scheme.Modules.pullbackComp (BaseChange.κ c K t).hom (BaseChange.κ c K t).inv).app _ ≪≫
      (Scheme.Modules.pullbackCongr (BaseChange.κ c K t).hom_inv_id).app _ ≪≫
      (Scheme.Modules.pullbackId _).app _
  exact ⟨e1 ≪≫ e2 ≪≫ e3 ≪≫ Scheme.Modules.rigidifyMapIso _ _ e6⟩

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_iso_rigidify_normModule_baseChange
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_iso_rigidify_normModule_baseChange (solution)
