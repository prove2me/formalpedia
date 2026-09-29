-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.IsDeformationClassMap.exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/dd944cfc-88bd-54ff-be4a-6e137ed2d22a

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
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_baseChange
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_isDeformationClassMap
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_field
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsDeformationClassMap_apply_baseTransport_eq_H1baseChangeMap
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_iso_rigidify_normModule_baseChange
import Theorems.Thm_AlgebraicCurve_cechH1ToH1_corrH1_of_pullback_specMap_self
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_mono
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.preimage_U0 AlgebraicGeometry.Scheme.TwoAffineOpenCover.preimage_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.ofPreimage_hom PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicCurve AlgebraicGeometry.Scheme.TwoAffineOpenCover"

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
    (K : Type u) [Field K] [Algebra R K]

    [Mono (specMap R K)]
    [IsIntegral (Limits.pullback c (specMap R K))]
    [IsSeparated (pullback.snd c (specMap R K))]
    [SmoothOfRelativeDimension 1 (pullback.snd c (specMap R K))]

    (hC : ∀ Z : Set ↥(Limits.pullback c (specMap R K)), IsClosed Z → Z ≠ Set.univ → Z.Finite)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)

    {Y : Scheme.{u}} (y : Y ⟶ Spec (.of K)) [IsIntegral Y] [IsProper y] [SmoothOfRelativeDimension 1 y]
    (πα πβ : Y ⟶ C) (Hα : πα ≫ c = y ≫ specMap R K) (Hβ : πβ ≫ c = y ≫ specMap R K)
    [IsFinite (pullback.lift πα y Hα : Y ⟶ Limits.pullback c (specMap R K))]
    [Flat (pullback.lift πα y Hα : Y ⟶ Limits.pullback c (specMap R K))]
    [LocallyOfFinitePresentation (pullback.lift πα y Hα : Y ⟶ Limits.pullback c (specMap R K))]
    [IsAffineHom (pullback.lift πβ y Hβ : Y ⟶ Limits.pullback c (specMap R K))]
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

    (𝒲 : C.TwoAffineOpenCover)
    {δ : RigKerDualNumber c ε K → H1StructureSheaf c K 𝒲} (hδ : IsDeformationClassMap c ε K 𝒲 δ)
    (x xr : {x : SchemeHomOver (specMap R (DualNumber K)) D.toBase //
        dualNumberReduction R K ≫ x.1 =
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one (specMap R K)).1})
    (hxr : xr.1.1 = x.1.1 ≫ φ₁.1)
    (s : ((𝒲.pullback c K).cover (pullback.snd c (specMap R K))).A01)
    (hs : δ (h.kerPointsToRigKer K x) = Submodule.Quotient.mk s) :
    letI X' := Limits.pullback c (specMap R K)
    letI c' : X' ⟶ Spec (.of K) := pullback.snd c (specMap R K)
    letI := (AlgebraicCurve.baseToFunctionField c').toAlgebra
    letI := (AlgebraicCurve.baseToFunctionField y).toAlgebra
    letI W := 𝒲.pullback c K
    ∀ [Nonempty (W.U0 ⊓ W.U1 : X'.Opens)]

      (φα φβ : X'.functionField →ₐ[K] Y.functionField)
      (hφπα : Y.fromSpecStalk (genericPoint Y) ≫ pullback.lift πα y Hα =
        Spec.map (CommRingCat.ofHom φα.toRingHom) ≫ X'.fromSpecStalk (genericPoint X'))
      (hφπβ : Y.fromSpecStalk (genericPoint Y) ≫ pullback.lift πβ y Hβ =
        Spec.map (CommRingCat.ofHom φβ.toRingHom) ≫ X'.fromSpecStalk (genericPoint X'))
      (hφα : φα.toRingHom.IsIntegral) (hφβ : φβ.toRingHom.IsIntegral) (htrα : TraceIntegralAlong φα hφα)
      (hW : AlgebraicCurve.placesOf c' W.U0 ∪ AlgebraicCurve.placesOf c' W.U1 = Set.univ)
      (hsr : (X'.germToFunctionField (W.U0 ⊓ W.U1)).hom s ∈
        AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c' W.U0 ∩ AlgebraicCurve.placesOf c' W.U1)
          (0 : AlgebraicCurve.Divisor K X'.functionField)),
      ∃ (sr : ((𝒲.pullback c K).cover (pullback.snd c (specMap R K))).A01)
        (hsrr : (X'.germToFunctionField (W.U0 ⊓ W.U1)).hom sr ∈
          AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c' W.U0 ∩ AlgebraicCurve.placesOf c' W.U1)
            (0 : AlgebraicCurve.Divisor K X'.functionField))
        (x' : AlgebraicCurve.cechH1 ((AlgebraicCurve.Place.restrictAlong φα hφα) ⁻¹' AlgebraicCurve.placesOf c' W.U0)
          ((AlgebraicCurve.Place.restrictAlong φα hφα) ⁻¹' AlgebraicCurve.placesOf c' W.U1)
          (0 : AlgebraicCurve.Divisor K Y.functionField)),
        δ (h.kerPointsToRigKer K xr) = Submodule.Quotient.mk sr ∧
        AlgebraicCurve.cechH1ToH1 (AlgebraicCurve.preimage_restrictAlong_union_eq_univ φα hφα hW) 0 x' =
          AlgebraicCurve.cechH1ToH1 (AlgebraicCurve.preimage_restrictAlong_union_eq_univ φβ hφβ hW) 0
            (AlgebraicCurve.cechH1.pullbackAlong φβ hφβ _ _
              (Submodule.Quotient.mk ⟨(X'.germToFunctionField (W.U0 ⊓ W.U1)).hom s, hsr⟩)) ∧
        AlgebraicCurve.cechH1ToH1 hW 0
            (Submodule.Quotient.mk ⟨(X'.germToFunctionField (W.U0 ⊓ W.U1)).hom sr, hsrr⟩) =
          AlgebraicCurve.cechH1ToH1 hW 0 (AlgebraicCurve.cechH1.traceAlong φα hφα htrα _ _ x') := by
  intro instNE φα φβ hφπα hφπβ hφα hφβ htrα hW hsr

  obtain ⟨h', hP⟩ := AlgebraicGeometry.RelPicard.exists_representsRelSubPic_baseChange R c ε D h K

  obtain ⟨x₁, hx₁, -⟩ :=
    AlgebraicGeometry.RelPicard.RigKerDualNumber.existsUnique_kerPoint_baseChange_comp_fst_eq c ε D h K h' hP K x
  obtain ⟨xr₁, hxr₁, -⟩ :=
    AlgebraicGeometry.RelPicard.RigKerDualNumber.existsUnique_kerPoint_baseChange_comp_fst_eq c ε D h K h' hP K xr
  let φ₁K : SchemeHomOver (D.baseChange K).toBase (D.baseChange K).toBase :=
    ⟨pullback.lift (pullback.fst D.toBase (specMap R K) ≫ φ₁.1) (pullback.snd D.toBase (specMap R K))
        (by rw [Category.assoc, φ₁.2]; exact pullback.condition),
      pullback.lift_snd _ _ _⟩
  have hφ₁K : φ₁K.1 ≫ pullback.fst D.toBase (specMap R K) = pullback.fst D.toBase (specMap R K) ≫ φ₁.1 :=
    pullback.lift_fst _ _ _
  have hxr₁' : xr₁.1.1 = x₁.1.1 ≫ φ₁K.1 := by
    apply pullback.hom_ext
    · rw [hxr₁, Category.assoc, hφ₁K, ← Category.assoc, hx₁, hxr]
    · rw [Category.assoc]
      exact xr₁.1.2.trans (x₁.1.2.symm.trans (by rw [φ₁K.2]))

  have Hα₁ : pullback.lift πα y Hα ≫ SmoothProperCurve.baseChange R c K = y := pullback.lift_snd _ _ _
  have Hβ₁ : pullback.lift πβ y Hβ ≫ SmoothProperCurve.baseChange R c K = y := pullback.lift_snd _ _ _
  have hmoduli₁ := fun (T : Scheme.{u}) (t : T ⟶ Spec (.of K)) M hM =>
    AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_iso_rigidify_normModule_baseChange c ε K D h h' hP y πα πβ Hα Hβ d hd φ₁ hmoduli φ₁K hφ₁K Hα₁ Hβ₁ T t M hM

  obtain ⟨δ₁, hδ₁⟩ := AlgebraicGeometry.RelPicard.exists_isDeformationClassMap
    (SmoothProperCurve.baseChange R c K) (SmoothProperCurve.sectionBaseChange K ε) K (𝒲.pullback c K)
  have hT1 := fun m => AlgebraicGeometry.RelPicard.IsDeformationClassMap.apply_baseTransport_eq_H1baseChangeMap c ε K 𝒲 hδ hδ₁ m
  have hbx : RigKerDualNumber.baseTransport K c ε K (h.kerPointsToRigKer K x) = h'.kerPointsToRigKer K x₁ :=
    AlgebraicGeometry.RelPicard.RigKerDualNumber.kerPointsToRigKer_baseTransport c ε D h K h' hP K x x₁ hx₁
  have hbxr : RigKerDualNumber.baseTransport K c ε K (h.kerPointsToRigKer K xr) = h'.kerPointsToRigKer K xr₁ :=
    AlgebraicGeometry.RelPicard.RigKerDualNumber.kerPointsToRigKer_baseTransport c ε D h K h' hP K xr xr₁ hxr₁
  have hs₁ : δ₁ (h'.kerPointsToRigKer K x₁) =
      Submodule.Quotient.mk ((HomOver.baseChange (𝒲.pullback c K) (pullback.snd c (specMap R K)) K).map01 s) := by
    rw [← hbx, hT1, hs]; rfl

  have hKK : specMap K K = 𝟙 _ := by
    change Spec.map (CommRingCat.ofHom (RingHom.id K)) = _
    rw [CommRingCat.ofHom_id]; exact Spec.map_id _
  haveI : IsIso (specMap K K) := by rw [hKK]; infer_instance
  haveI : IsIntegral (Limits.pullback (pullback.snd c (specMap R K)) (specMap K K)) :=
    IsIntegral.of_isIso (inv (pullback.fst (pullback.snd c (specMap R K)) (specMap K K)))

  refine AlgebraicCurve.cechH1ToH1_corrH1_of_pullback_specMap_self K (pullback.snd c (specMap R K)) (𝒲.pullback c K) y
    (pullback.lift πα y Hα) (pullback.lift πβ y Hβ) (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _)
    (pullback.lift (pullback.lift πα y Hα) y (by rw [pullback.lift_snd, hKK, Category.comp_id]))
    (pullback.lift (pullback.lift πβ y Hβ) y (by rw [pullback.lift_snd, hKK, Category.comp_id]))
    (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _)
    s (δ (h.kerPointsToRigKer K xr)) ?_ φα φβ hφπα hφπβ hφα hφβ htrα hW hsr
  intro instNE₁ ψα ψβ hψπα hψπβ hψα hψβ htrψα hW₁ hs₁m
  obtain ⟨sr₁, hsrr₁, x₁', h1, h2, h3⟩ :=
    AlgebraicGeometry.RelPicard.IsDeformationClassMap.exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_field
      K (pullback.snd c (specMap R K)) (SmoothProperCurve.sectionBaseChange K ε) hC (D.baseChange K) h' y
      (pullback.lift πα y Hα) (pullback.lift πβ y Hβ) Hα₁ Hβ₁ d hd
      (pullback.lift (pullback.lift πα y Hα) y (by rw [pullback.lift_snd, hKK, Category.comp_id]))
      (pullback.lift (pullback.lift πβ y Hβ) y (by rw [pullback.lift_snd, hKK, Category.comp_id]))
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      φ₁K hmoduli₁ (𝒲.pullback c K) hδ₁ x₁ xr₁ hxr₁' _ hs₁ ψα ψβ hψπα hψπβ hψα hψβ htrψα hW₁ hs₁m
  refine ⟨sr₁, hsrr₁, x₁', ?_, h2, h3⟩
  rw [← h1, ← hbxr, hT1]

#print axioms solution

end S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_mono
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_mono (solution)
