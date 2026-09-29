-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.IsDeformationClassMap.exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/ee4f207b-1dc1-5da5-a1fc-67b143a08224

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
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverPreimage
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigKerDualNumber_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_HomOver_exists_isFrameOn_pullback_of_map_eq_smul
import Theorems.Thm_AlgebraicGeometry_RelPicard_map01_oneAddEpsMul
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_pullbackMap_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_forall_basis_pushforward_dualNumberThickening_of_forall_basis
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_rigidify_iso_of_nonempty_pullback_iso_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import Theorems.Thm_AlgebraicGeometry_RelPicard_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_dualNumber_of_reduction
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_isDeformationClassMap
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsDeformationClassMap_cechH1ToH1_germ_eq_of_two_covers
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_crossSections_of_isFrameOn_of_map_eq_oneAddEpsMul_smul
import Theorems.Thm_AlgebraicCurve_germToFunctionField_inf_mem_lSpaceOn_inter_placesOf
import Theorems.Thm_AlgebraicCurve_germToFunctionField_mem_lSpaceOn_placesOf
import Theorems.Thm_AlgebraicCurve_germToFunctionField_app_eq_of_fromSpecStalk_comp_eq
import Theorems.Thm_AlgebraicGeometry_germToFunctionField_trace_eq_traceFunAlong_germToFunctionField
import Theorems.Thm_AlgebraicCurve_placesOf_preimage_eq_preimage_restrictAlong_placesOf
import Theorems.Thm_AlgebraicCurve_cechH1ToH1_mk_eq_cechH1ToH1_mk_of_crossSections
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_field
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicCurve AlgebraicGeometry.Scheme.TwoAffineOpenCover"

namespace NormDefTriv

variable {κ : Type u} [Field κ] {C C' : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of κ)) (c' : C' ⟶ Spec (CommRingCat.of κ)) (f : C' ⟶ C) (hf : f ≫ c = c')

scoped instance isIso_specMap_self : IsIso (specMap κ κ) := by
  rw [show specMap κ κ = 𝟙 _ by
    simp only [Scheme.TwoAffineOpenCover.specMap, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]]
  infer_instance

scoped instance isIso_fst_specMap_self : IsIso (pullback.fst c (specMap κ κ)) :=
  (IsPullback.of_hasPullback c (specMap κ κ)).isIso_fst_of_isIso

theorem isIntegral_pullback_specMap_self [IsIntegral C] : IsIntegral (pullback c (specMap κ κ)) :=
  IsIntegral.of_isIso (inv (pullback.fst c (specMap κ κ)))

example [LocallyOfFiniteType c] : LocallyOfFiniteType (pullback.snd c (specMap κ κ)) := inferInstance

theorem curveHyp_pullback_specMap_self (hC : ∀ Z : Set C, IsClosed Z → Z ≠ Set.univ → Z.Finite) :
    ∀ Z : Set ↥(pullback c (specMap κ κ)), IsClosed Z → Z ≠ Set.univ → Z.Finite := by
  intro Z hZ hZne
  let φ := Scheme.homeoOfIso (asIso (pullback.fst c (specMap κ κ)))
  have himg : (φ '' Z).Finite := by
    refine hC _ (φ.isClosedMap _ hZ) ?_
    intro h
    apply hZne
    rw [← Set.image_univ_of_surjective φ.surjective] at h
    exact φ.injective.image_injective h
  exact himg.of_finite_image φ.injective.injOn

variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ))

theorem isPullback_curveChange :
    IsPullback (curveChange f hf t) (pullback.fst c' t) (pullback.fst c t) f := by
  refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback c t).flip
  · rw [curveChange_snd]
    subst hf
    exact (IsPullback.of_hasPullback (f ≫ c) t).flip
  · simp only [curveChange, pullback.lift_fst]

scoped instance isFinite_curveChange [IsFinite f] : IsFinite (curveChange f hf t) :=
  MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_curveChange c c' f hf t).flip ‹_›
scoped instance flat_curveChange [Flat f] : Flat (curveChange f hf t) :=
  MorphismProperty.of_isPullback (P := @Flat) (isPullback_curveChange c c' f hf t).flip ‹_›
scoped instance locallyOfFinitePresentation_curveChange [LocallyOfFinitePresentation f] :
    LocallyOfFinitePresentation (curveChange f hf t) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) (isPullback_curveChange c c' f hf t).flip ‹_›
scoped instance isAffineHom_curveChange [IsAffineHom f] : IsAffineHom (curveChange f hf t) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_curveChange c c' f hf t).flip ‹_›

theorem finrank_curveChange [IsFinite f] [Flat f] {p : ℕ} (hrk : ∀ y, f.finrank y = p) (y) :
    (curveChange f hf t).finrank y = p := by
  have h := AlgebraicGeometry.Scheme.Hom.finrank_pullbackMap_of_comp_eq c c' t f hf y
  simp only [curveChange]
  exact h.trans (hrk _)

theorem hinj_curveChange_specMap_self
    (hinj : ∀ x₁ x₂ : C', IsClosed ({x₁} : Set C') → IsClosed ({x₂} : Set C') → f.base x₁ = f.base x₂ → x₁ = x₂)
    (x₁ x₂ : ↥(pullback c' (specMap κ κ))) (h₁ : IsClosed ({x₁} : Set _)) (h₂ : IsClosed ({x₂} : Set _))
    (h : (curveChange f hf (specMap κ κ)).base x₁ = (curveChange f hf (specMap κ κ)).base x₂) : x₁ = x₂ := by
  let φ' := Scheme.homeoOfIso (asIso (pullback.fst c' (specMap κ κ)))
  have hcomm : ∀ x, f.base ((pullback.fst c' (specMap κ κ)).base x) =
      (pullback.fst c (specMap κ κ)).base ((curveChange f hf (specMap κ κ)).base x) := fun x => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
    congr 2
    simp only [curveChange, pullback.lift_fst]
  apply φ'.injective
  refine hinj _ _ ?_ ?_ ?_
  · simpa only [Set.image_singleton] using φ'.isClosedMap _ h₁
  · simpa only [Set.image_singleton] using φ'.isClosedMap _ h₂
  · change f.base ((pullback.fst c' (specMap κ κ)).base x₁) = f.base ((pullback.fst c' (specMap κ κ)).base x₂)
    rw [hcomm, hcomm, h]

theorem basisOn_congr {X : Scheme.{u}} (M : X.Modules) {p : ℕ} {U U' : X.Opens} (h : U' = U)
    (H : ∃ e : Fin p → Γ(M, U), ∀ (W : X.Opens) (hW : W ≤ U),
      ∃ b : Module.Basis (Fin p) Γ(X, W) Γ(M, W), ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i)) :
    ∃ e : Fin p → Γ(M, U'), ∀ (W : X.Opens) (hW : W ≤ U'),
      ∃ b : Module.Basis (Fin p) Γ(X, W) Γ(M, W), ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i) := by
  subst h; exact H

theorem exists_twoAffineOpenCover_forall_basis [IsIntegral C]
    (hC : ∀ Z : Set C, IsClosed Z → Z ≠ Set.univ → Z.Finite) (𝒱 : C.TwoAffineOpenCover)
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] {p : ℕ} (hrk : ∀ y, f.finrank y = p) :
    ∃ 𝒱' : C.TwoAffineOpenCover,
      (∃ e : Fin p → Γ((Scheme.Modules.pushforward (curveChange f hf (specMap κ κ))).obj (𝟙_ _), (𝒱'.pullback c κ).U0),
        ∀ (W : (pullback c (specMap κ κ)).Opens) (hW : W ≤ (𝒱'.pullback c κ).U0),
          ∃ b : Module.Basis (Fin p) Γ(pullback c (specMap κ κ), W)
              Γ((Scheme.Modules.pushforward (curveChange f hf (specMap κ κ))).obj (𝟙_ _), W),
            ∀ i, b i = ((Scheme.Modules.pushforward (curveChange f hf (specMap κ κ))).obj (𝟙_ _)).presheaf.map
              (homOfLE hW).op (e i)) ∧
      (∃ e : Fin p → Γ((Scheme.Modules.pushforward (curveChange f hf (specMap κ κ))).obj (𝟙_ _), (𝒱'.pullback c κ).U1),
        ∀ (W : (pullback c (specMap κ κ)).Opens) (hW : W ≤ (𝒱'.pullback c κ).U1),
          ∃ b : Module.Basis (Fin p) Γ(pullback c (specMap κ κ), W)
              Γ((Scheme.Modules.pushforward (curveChange f hf (specMap κ κ))).obj (𝟙_ _), W),
            ∀ i, b i = ((Scheme.Modules.pushforward (curveChange f hf (specMap κ κ))).obj (𝟙_ _)).presheaf.map
              (homOfLE hW).op (e i)) := by
  classical

  haveI : IsIntegral (pullback c (specMap κ κ)) := isIntegral_pullback_specMap_self c
  have hX := curveHyp_pullback_specMap_self c hC
  have hd : ∀ x, (curveChange f hf (specMap κ κ)).finrank x = p := finrank_curveChange c c' f hf _ hrk
  let φh := Scheme.homeoOfIso (asIso (pullback.fst c (specMap κ κ)))

  obtain ⟨𝒱n, hn0, hn1⟩ : ∃ 𝒱n : C.TwoAffineOpenCover, (𝒱n.U0 : Set C).Nonempty ∧ (𝒱n.U1 : Set C).Nonempty := by
    by_cases h0 : (𝒱.U0 : Set C).Nonempty <;> by_cases h1 : (𝒱.U1 : Set C).Nonempty
    · exact ⟨𝒱, h0, h1⟩
    · have hU1 : 𝒱.U1 = ⊥ :=
        TopologicalSpace.Opens.ext (by rw [TopologicalSpace.Opens.coe_bot]; exact Set.not_nonempty_iff_eq_empty.mp h1)
      have hU0 : 𝒱.U0 = ⊤ := by simpa [hU1] using 𝒱.sup_eq_top
      refine ⟨⟨𝒱.U0, 𝒱.U0, 𝒱.isAffineOpen_U0, 𝒱.isAffineOpen_U0, by rw [hU0, sup_idem], by
        rw [inf_idem]; exact 𝒱.isAffineOpen_U0⟩, h0, h0⟩
    · have hU0 : 𝒱.U0 = ⊥ :=
        TopologicalSpace.Opens.ext (by rw [TopologicalSpace.Opens.coe_bot]; exact Set.not_nonempty_iff_eq_empty.mp h0)
      have hU1 : 𝒱.U1 = ⊤ := by simpa [hU0] using 𝒱.sup_eq_top
      refine ⟨⟨𝒱.U1, 𝒱.U1, 𝒱.isAffineOpen_U1, 𝒱.isAffineOpen_U1, by rw [hU1, sup_idem], by
        rw [inf_idem]; exact 𝒱.isAffineOpen_U1⟩, h1, h1⟩
    · exfalso
      have hU0 : 𝒱.U0 = ⊥ :=
        TopologicalSpace.Opens.ext (by rw [TopologicalSpace.Opens.coe_bot]; exact Set.not_nonempty_iff_eq_empty.mp h0)
      have hU1 : 𝒱.U1 = ⊥ :=
        TopologicalSpace.Opens.ext (by rw [TopologicalSpace.Opens.coe_bot]; exact Set.not_nonempty_iff_eq_empty.mp h1)
      have htop : (⊤ : C.Opens) = ⊥ := by rw [← 𝒱.sup_eq_top, hU0, hU1, sup_idem]
      have hne : ((⊤ : C.Opens) : Set C).Nonempty := by
        rw [TopologicalSpace.Opens.coe_top]; exact Set.univ_nonempty
      rw [htop, TopologicalSpace.Opens.coe_bot] at hne
      exact Set.not_nonempty_empty hne

  have h₀ : ((𝒱n.pullback c κ).U0 : Set ↥(pullback c (specMap κ κ))).Nonempty := hn0.preimage φh.surjective
  have h₁ : ((𝒱n.pullback c κ).U1 : Set ↥(pullback c (specMap κ κ))).Nonempty := hn1.preimage φh.surjective
  obtain ⟨-, -, 𝒱'', -, -, hb0, hb1⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_basicOpen_refinement_basis_pushforward
      (curveChange f hf (specMap κ κ)) p hd hX (𝒱n.pullback c κ) h₀ h₁

  let ψ := inv (pullback.fst c (specMap κ κ))
  let 𝒱' : C.TwoAffineOpenCover :=
    { U0 := ψ ⁻¹ᵁ 𝒱''.U0
      U1 := ψ ⁻¹ᵁ 𝒱''.U1
      isAffineOpen_U0 := 𝒱''.isAffineOpen_U0.preimage ψ
      isAffineOpen_U1 := 𝒱''.isAffineOpen_U1.preimage ψ
      sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒱''.sup_eq_top]; rfl
      isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒱''.isAffineOpen_inf.preimage ψ }
  have hU0 : (𝒱'.pullback c κ).U0 = 𝒱''.U0 := by
    show (pullback.fst c (specMap κ κ) ≫ ψ) ⁻¹ᵁ 𝒱''.U0 = 𝒱''.U0
    rw [IsIso.hom_inv_id]; rfl
  have hU1 : (𝒱'.pullback c κ).U1 = 𝒱''.U1 := by
    show (pullback.fst c (specMap κ κ) ≫ ψ) ⁻¹ᵁ 𝒱''.U1 = 𝒱''.U1
    rw [IsIso.hom_inv_id]; rfl
  exact ⟨𝒱', basisOn_congr _ hU0 hb0, basisOn_congr _ hU1 hb1⟩

section U3
variable {κ : Type u} [Field κ] {C C' : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of κ)) (c' : C' ⟶ Spec (CommRingCat.of κ)) (f : C' ⟶ C) (hf : f ≫ c = c')

theorem curveChange_fst {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) :
    curveChange f hf t ≫ pullback.fst c t = pullback.fst c' t ≫ f := by
  simp only [curveChange, pullback.lift_fst]

def preimageCover [IsAffineHom f] (𝒱 : C.TwoAffineOpenCover) : C'.TwoAffineOpenCover where
  U0 := f ⁻¹ᵁ 𝒱.U0
  U1 := f ⁻¹ᵁ 𝒱.U1
  isAffineOpen_U0 := 𝒱.isAffineOpen_U0.preimage f
  isAffineOpen_U1 := 𝒱.isAffineOpen_U1.preimage f
  sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒱.sup_eq_top]; rfl
  isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒱.isAffineOpen_inf.preimage f

variable (A : Type u) [CommRing A] [Algebra κ A]

theorem preimageCover_pullback_U0 [IsAffineHom f] (𝒱 : C.TwoAffineOpenCover) :
    ((preimageCover f 𝒱).pullback c' A).U0 = curveChange f hf (specMap κ A) ⁻¹ᵁ (𝒱.pullback c A).U0 := by
  simp only [pullback_U0, preimageCover, ← Scheme.Hom.comp_preimage, curveChange_fst]

theorem preimageCover_pullback_U1 [IsAffineHom f] (𝒱 : C.TwoAffineOpenCover) :
    ((preimageCover f 𝒱).pullback c' A).U1 = curveChange f hf (specMap κ A) ⁻¹ᵁ (𝒱.pullback c A).U1 := by
  simp only [pullback_U1, preimageCover, ← Scheme.Hom.comp_preimage, curveChange_fst]

noncomputable def homOver [IsAffineHom f] (𝒱 : C.TwoAffineOpenCover) :
    HomOver (RingHom.id A) (𝒱.pullback c A) (pullback.snd c (specMap κ A))
      ((preimageCover f 𝒱).pullback c' A) (pullback.snd c' (specMap κ A)) where
  hom := curveChange f hf (specMap κ A)
  comm := by
    rw [curveChange_snd]
    change _ = _ ≫ Spec.map (𝟙 _)
    rw [Spec.map_id, Category.comp_id]
  U0_le := (preimageCover_pullback_U0 c c' f hf A 𝒱).le
  U1_le := (preimageCover_pullback_U1 c c' f hf A 𝒱).le

@[scoped simp] theorem homOver_hom [IsAffineHom f] (𝒱 : C.TwoAffineOpenCover) :
    (homOver c c' f hf A 𝒱).hom = curveChange f hf (specMap κ A) := rfl

theorem isPullback_thickening [IsAffineHom f] (𝒱 : C.TwoAffineOpenCover) :
    IsPullback (homOver c c' f hf (DualNumber A) 𝒱).hom (dualNumberThickening A (preimageCover f 𝒱) c').hom
      (dualNumberThickening A 𝒱 c).hom (homOver c c' f hf A 𝒱).hom := by

  have outer := isPullback_curveChange c c' f hf (specMap κ (DualNumber A))
  have bot := isPullback_curveChange c c' f hf (specMap κ A)
  refine IsPullback.of_bot ?_ ?_ bot
  ·
    have h1 : (dualNumberThickening A (preimageCover f 𝒱) c').hom ≫ pullback.fst c' (specMap κ A) =
        pullback.fst c' (specMap κ (DualNumber A)) := by
      dsimp only [dualNumberThickening, HomOver.stage]
      exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    have h2 : (dualNumberThickening A 𝒱 c).hom ≫ pullback.fst c (specMap κ A) =
        pullback.fst c (specMap κ (DualNumber A)) := by
      dsimp only [dualNumberThickening, HomOver.stage]
      exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    rw [h1, h2]
    exact outer
  ·
    dsimp only [dualNumberThickening, HomOver.stage, homOver]
    exact curveChange_baseChangeSnd f hf _

theorem free_finite_trace_of_basis {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (hV : V = g ⁻¹ᵁ U)
    {d : ℕ} (b : Module.Basis (Fin d) Γ(Y, U) Γ((Scheme.Modules.pushforward g).obj (𝟙_ X.Modules), U))
    (htz : letI := (g.app U).hom.toAlgebra
      ∀ [Module.Free Γ(Y, U) Γ(X, g ⁻¹ᵁ U)] [Module.Finite Γ(Y, U) Γ(X, g ⁻¹ᵁ U)],
        Algebra.trace Γ(Y, U) Γ(X, g ⁻¹ᵁ U) = 0) :
    letI := (g.appLE U V hV.le).hom.toAlgebra
    ∃ (_ : Module.Free Γ(Y, U) Γ(X, V)) (_ : Module.Finite Γ(Y, U) Γ(X, V)), Algebra.trace Γ(Y, U) Γ(X, V) = 0 := by
  generalize hφ : g.appLE U V hV.le = φ
  subst hV
  obtain rfl : φ = g.app U := by rw [← hφ]; exact (Scheme.Hom.app_eq_appLE g).symm
  letI : Algebra Γ(Y, U) Γ(X, g ⁻¹ᵁ U) := (g.app U).hom.toAlgebra
  haveI hF : Module.Free Γ(Y, U) Γ(X, g ⁻¹ᵁ U) := Module.Free.of_basis b
  haveI hFin : Module.Finite Γ(Y, U) Γ(X, g ⁻¹ᵁ U) := Module.Finite.of_basis b
  exact ⟨hF, hFin, htz⟩

end U3
end NormDefTriv
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_field.NormDefTriv"

open NormDefTriv

namespace CorrH1Aux
open Opposite
variable {X : Scheme.{u}} {N N' : X.Modules}

theorem app_map (φ : N ⟶ N') {U W : X.Opens} (i : W ⟶ U) (s : Γ(N, U)) :
    N'.presheaf.map i.op (φ.app U s) = φ.app W (N.presheaf.map i.op s) := by
  have := (φ.mapPresheaf).naturality i.op
  exact (congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(N, U) → Γ(N', W))) this) s).symm

theorem map_eq_smul_of_hom (φ : N ⟶ N') {U0 U1 : X.Opens} (e₀ : Γ(N, U0)) (e₁ : Γ(N, U1)) (τ : Γ(X, U0 ⊓ U1))
    (h : N.presheaf.map (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op e₁ =
      τ • N.presheaf.map (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op e₀) :
    N'.presheaf.map (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op (φ.app U1 e₁) =
      τ • N'.presheaf.map (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op (φ.app U0 e₀) := by
  rw [app_map, app_map, h, Scheme.Modules.Hom.app_smul]

theorem exists_twoAffineOpenCover_forall_basis_nonempty
    {κ : Type u} [Field κ] {C C' : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of κ)) (c' : C' ⟶ Spec (CommRingCat.of κ)) (f : C' ⟶ C) (hf : f ≫ c = c')
    [IsIntegral C] (hC : ∀ Z : Set C, IsClosed Z → Z ≠ Set.univ → Z.Finite) (𝒱 : C.TwoAffineOpenCover)
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] {p : ℕ} (hrk : ∀ y, f.finrank y = p) :
    ∃ 𝒱' : C.TwoAffineOpenCover,
      ((𝒱'.pullback c κ).U0 : Set ↥(Limits.pullback c (specMap κ κ))).Nonempty ∧
      ((𝒱'.pullback c κ).U1 : Set ↥(Limits.pullback c (specMap κ κ))).Nonempty ∧
      (∃ e : Fin p → Γ((Scheme.Modules.pushforward (curveChange f hf (specMap κ κ))).obj (𝟙_ _), (𝒱'.pullback c κ).U0),
        ∀ (W : (Limits.pullback c (specMap κ κ)).Opens) (hW : W ≤ (𝒱'.pullback c κ).U0),
          ∃ b : Module.Basis (Fin p) Γ(Limits.pullback c (specMap κ κ), W)
              Γ((Scheme.Modules.pushforward (curveChange f hf (specMap κ κ))).obj (𝟙_ _), W),
            ∀ i, b i = ((Scheme.Modules.pushforward (curveChange f hf (specMap κ κ))).obj (𝟙_ _)).presheaf.map
              (homOfLE hW).op (e i)) ∧
      (∃ e : Fin p → Γ((Scheme.Modules.pushforward (curveChange f hf (specMap κ κ))).obj (𝟙_ _), (𝒱'.pullback c κ).U1),
        ∀ (W : (Limits.pullback c (specMap κ κ)).Opens) (hW : W ≤ (𝒱'.pullback c κ).U1),
          ∃ b : Module.Basis (Fin p) Γ(Limits.pullback c (specMap κ κ), W)
              Γ((Scheme.Modules.pushforward (curveChange f hf (specMap κ κ))).obj (𝟙_ _), W),
            ∀ i, b i = ((Scheme.Modules.pushforward (curveChange f hf (specMap κ κ))).obj (𝟙_ _)).presheaf.map
              (homOfLE hW).op (e i)) := by
  obtain ⟨𝒱'', hb0, hb1⟩ := NormDefTriv.exists_twoAffineOpenCover_forall_basis c c' f hf hC 𝒱 hrk
  haveI : IsIntegral (Limits.pullback c (specMap κ κ)) := NormDefTriv.isIntegral_pullback_specMap_self c

  have htop : ∀ U : C.Opens, (pullback.fst c (specMap κ κ)) ⁻¹ᵁ U = ⊤ → U = ⊤ := by
    intro U hU
    apply top_le_iff.mp
    intro x _
    obtain ⟨y, rfl⟩ := (Scheme.homeoOfIso (asIso (pullback.fst c (specMap κ κ)))).surjective x
    have : y ∈ ((pullback.fst c (specMap κ κ)) ⁻¹ᵁ U) := by rw [hU]; trivial
    exact this

  have hsup := (𝒱''.pullback c κ).sup_eq_top
  by_cases h0 : ((𝒱''.pullback c κ).U0 : Set ↥(Limits.pullback c (specMap κ κ))).Nonempty
  · by_cases h1 : ((𝒱''.pullback c κ).U1 : Set ↥(Limits.pullback c (specMap κ κ))).Nonempty
    · exact ⟨𝒱'', h0, h1, hb0, hb1⟩
    · have hU1 : (𝒱''.pullback c κ).U1 = ⊥ :=
        TopologicalSpace.Opens.ext (by rw [TopologicalSpace.Opens.coe_bot]; exact Set.not_nonempty_iff_eq_empty.mp h1)
      have hU0 : 𝒱''.U0 = ⊤ := htop _ (by rw [← hsup, hU1, sup_bot_eq]; rfl)
      refine ⟨{ U0 := 𝒱''.U0, U1 := 𝒱''.U0, isAffineOpen_U0 := 𝒱''.isAffineOpen_U0, isAffineOpen_U1 := 𝒱''.isAffineOpen_U0,
                sup_eq_top := by rw [sup_idem, hU0], isAffineOpen_inf := by rw [inf_idem]; exact 𝒱''.isAffineOpen_U0 },
              h0, h0, hb0, hb0⟩
  · have hU0 : (𝒱''.pullback c κ).U0 = ⊥ :=
      TopologicalSpace.Opens.ext (by rw [TopologicalSpace.Opens.coe_bot]; exact Set.not_nonempty_iff_eq_empty.mp h0)
    have hU1 : 𝒱''.U1 = ⊤ := htop _ (by rw [← hsup, hU0, bot_sup_eq]; rfl)
    have h1 : ((𝒱''.pullback c κ).U1 : Set ↥(Limits.pullback c (specMap κ κ))).Nonempty := by
      have : (𝒱''.pullback c κ).U1 = ⊤ := by
        change (pullback.fst c (specMap κ κ)) ⁻¹ᵁ 𝒱''.U1 = ⊤; rw [hU1]; rfl
      rw [this, TopologicalSpace.Opens.coe_top]; exact Set.univ_nonempty
    refine ⟨{ U0 := 𝒱''.U1, U1 := 𝒱''.U1, isAffineOpen_U0 := 𝒱''.isAffineOpen_U1, isAffineOpen_U1 := 𝒱''.isAffineOpen_U1,
              sup_eq_top := by rw [sup_idem, hU1], isAffineOpen_inf := by rw [inf_idem]; exact 𝒱''.isAffineOpen_U1 },
            h1, h1, hb1, hb1⟩

end CorrH1Aux
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_field.NormDefTriv"

namespace Step7a

open Opposite

theorem upstairs_package
    (K : Type u) [Field K] {C : Scheme.{u}} {Y : Scheme.{u}} (y : Y ⟶ Spec (.of K))
    (πα πβ : Y ⟶ C) [IsAffineHom πα] [IsAffineHom πβ] [IsSeparated (pullback.snd y (specMap K K))]
    (𝒲 𝒲' : C.TwoAffineOpenCover)
    (L : (Limits.pullback y (specMap K (DualNumber K))).Modules) (hLinv : Scheme.Modules.IsInvertible L)
    (hL0 : Nonempty ((Scheme.Modules.pullback (RelPicard.baseChangeSnd y (dualNumberReductionOver K K))).obj L ≅
      SheafOfModules.unit.{u} (Limits.pullback y (specMap K K)).ringCatSheaf))

    (tβ : (((NormDefTriv.preimageCover πβ 𝒲).pullback y K).cover (pullback.snd y (specMap K K))).A01)
    (b₀ : Γ(L, ((NormDefTriv.preimageCover πβ 𝒲).pullback y (DualNumber K)).U0))
    (b₁ : Γ(L, ((NormDefTriv.preimageCover πβ 𝒲).pullback y (DualNumber K)).U1))
    (hb₀ : Scheme.Modules.IsFrameOn b₀ ((NormDefTriv.preimageCover πβ 𝒲).pullback y (DualNumber K)).U0)
    (hb₁ : Scheme.Modules.IsFrameOn b₁ ((NormDefTriv.preimageCover πβ 𝒲).pullback y (DualNumber K)).U1)
    (hbt : L.presheaf.map (homOfLE inf_le_right).op b₁ =
      (show Γ(Limits.pullback y (specMap K (DualNumber K)),
          ((NormDefTriv.preimageCover πβ 𝒲).pullback y (DualNumber K)).U0 ⊓
            ((NormDefTriv.preimageCover πβ 𝒲).pullback y (DualNumber K)).U1)
        from oneAddEpsMul K (NormDefTriv.preimageCover πβ 𝒲) y tβ) •
        L.presheaf.map (homOfLE inf_le_left).op b₀)

    (g : (((NormDefTriv.preimageCover πα 𝒲').pullback y K).cover (pullback.snd y (specMap K K))).A01)
    (s₀ : Γ(L, ((NormDefTriv.preimageCover πα 𝒲').pullback y (DualNumber K)).U0))
    (s₁ : Γ(L, ((NormDefTriv.preimageCover πα 𝒲').pullback y (DualNumber K)).U1))
    (hs₀ : Scheme.Modules.IsFrameOn s₀ ((NormDefTriv.preimageCover πα 𝒲').pullback y (DualNumber K)).U0)
    (hs₁ : Scheme.Modules.IsFrameOn s₁ ((NormDefTriv.preimageCover πα 𝒲').pullback y (DualNumber K)).U1)
    (hsg : L.presheaf.map (homOfLE inf_le_right).op s₁ =
      (show Γ(Limits.pullback y (specMap K (DualNumber K)),
          ((NormDefTriv.preimageCover πα 𝒲').pullback y (DualNumber K)).U0 ⊓
            ((NormDefTriv.preimageCover πα 𝒲').pullback y (DualNumber K)).U1)
        from oneAddEpsMul K (NormDefTriv.preimageCover πα 𝒲') y g) •
        L.presheaf.map (homOfLE inf_le_left).op s₀) :
    letI Y₁ := Limits.pullback y (specMap K K)
    letI Wα := (NormDefTriv.preimageCover πα 𝒲).pullback y K
    letI Wβ := (NormDefTriv.preimageCover πβ 𝒲).pullback y K
    letI Wα' := (NormDefTriv.preimageCover πα 𝒲').pullback y K
    ∃ (g'' : (Wα.cover (pullback.snd y (specMap K K))).A01),

      (∃ (e₀ : Γ(L, ((NormDefTriv.preimageCover πα 𝒲).pullback y (DualNumber K)).U0))
          (e₁ : Γ(L, ((NormDefTriv.preimageCover πα 𝒲).pullback y (DualNumber K)).U1)),
        Scheme.Modules.IsFrameOn e₀ ((NormDefTriv.preimageCover πα 𝒲).pullback y (DualNumber K)).U0 ∧
        Scheme.Modules.IsFrameOn e₁ ((NormDefTriv.preimageCover πα 𝒲).pullback y (DualNumber K)).U1 ∧
        L.presheaf.map (homOfLE inf_le_right).op e₁ =
          (show Γ(Limits.pullback y (specMap K (DualNumber K)),
              ((NormDefTriv.preimageCover πα 𝒲).pullback y (DualNumber K)).U0 ⊓
                ((NormDefTriv.preimageCover πα 𝒲).pullback y (DualNumber K)).U1)
            from oneAddEpsMul K (NormDefTriv.preimageCover πα 𝒲) y g'') •
            L.presheaf.map (homOfLE inf_le_left).op e₀) ∧

      (∃ (k00 : Γ(Limits.pullback y (specMap K K), Wα.U0 ⊓ Wβ.U0)) (k01 : Γ(Limits.pullback y (specMap K K), Wα.U0 ⊓ Wβ.U1))
          (k10 : Γ(Limits.pullback y (specMap K K), Wα.U1 ⊓ Wβ.U0)) (k11 : Γ(Limits.pullback y (specMap K K), Wα.U1 ⊓ Wβ.U1)),
        (Y₁.presheaf.map (homOfLE (inf_le_inf_right Wβ.U0 inf_le_left : (Wα.U0 ⊓ Wα.U1) ⊓ Wβ.U0 ≤ Wα.U0 ⊓ Wβ.U0)).op).hom k00
          = (Y₁.presheaf.map (homOfLE (inf_le_inf_right Wβ.U0 inf_le_right : (Wα.U0 ⊓ Wα.U1) ⊓ Wβ.U0 ≤ Wα.U1 ⊓ Wβ.U0)).op).hom k10
            + (Y₁.presheaf.map (homOfLE (inf_le_left : (Wα.U0 ⊓ Wα.U1) ⊓ Wβ.U0 ≤ Wα.U0 ⊓ Wα.U1)).op).hom g'' ∧
        (Y₁.presheaf.map (homOfLE (inf_le_inf_right Wβ.U1 inf_le_left : (Wα.U0 ⊓ Wα.U1) ⊓ Wβ.U1 ≤ Wα.U0 ⊓ Wβ.U1)).op).hom k01
          = (Y₁.presheaf.map (homOfLE (inf_le_inf_right Wβ.U1 inf_le_right : (Wα.U0 ⊓ Wα.U1) ⊓ Wβ.U1 ≤ Wα.U1 ⊓ Wβ.U1)).op).hom k11
            + (Y₁.presheaf.map (homOfLE (inf_le_left : (Wα.U0 ⊓ Wα.U1) ⊓ Wβ.U1 ≤ Wα.U0 ⊓ Wα.U1)).op).hom g'' ∧
        (Y₁.presheaf.map (homOfLE (inf_le_inf_left Wα.U0 inf_le_right : Wα.U0 ⊓ (Wβ.U0 ⊓ Wβ.U1) ≤ Wα.U0 ⊓ Wβ.U1)).op).hom k01
          = (Y₁.presheaf.map (homOfLE (inf_le_inf_left Wα.U0 inf_le_left : Wα.U0 ⊓ (Wβ.U0 ⊓ Wβ.U1) ≤ Wα.U0 ⊓ Wβ.U0)).op).hom k00
            + (Y₁.presheaf.map (homOfLE (inf_le_right : Wα.U0 ⊓ (Wβ.U0 ⊓ Wβ.U1) ≤ Wβ.U0 ⊓ Wβ.U1)).op).hom tβ ∧
        (Y₁.presheaf.map (homOfLE (inf_le_inf_left Wα.U1 inf_le_right : Wα.U1 ⊓ (Wβ.U0 ⊓ Wβ.U1) ≤ Wα.U1 ⊓ Wβ.U1)).op).hom k11
          = (Y₁.presheaf.map (homOfLE (inf_le_inf_left Wα.U1 inf_le_left : Wα.U1 ⊓ (Wβ.U0 ⊓ Wβ.U1) ≤ Wα.U1 ⊓ Wβ.U0)).op).hom k10
            + (Y₁.presheaf.map (homOfLE (inf_le_right : Wα.U1 ⊓ (Wβ.U0 ⊓ Wβ.U1) ≤ Wβ.U0 ⊓ Wβ.U1)).op).hom tβ) ∧

      (∃ (h00 : Γ(Limits.pullback y (specMap K K), Wα.U0 ⊓ Wα'.U0)) (h01 : Γ(Limits.pullback y (specMap K K), Wα.U0 ⊓ Wα'.U1))
          (h10 : Γ(Limits.pullback y (specMap K K), Wα.U1 ⊓ Wα'.U0)) (h11 : Γ(Limits.pullback y (specMap K K), Wα.U1 ⊓ Wα'.U1)),
        (Y₁.presheaf.map (homOfLE (inf_le_inf_right Wα'.U0 inf_le_left : (Wα.U0 ⊓ Wα.U1) ⊓ Wα'.U0 ≤ Wα.U0 ⊓ Wα'.U0)).op).hom h00
          = (Y₁.presheaf.map (homOfLE (inf_le_inf_right Wα'.U0 inf_le_right : (Wα.U0 ⊓ Wα.U1) ⊓ Wα'.U0 ≤ Wα.U1 ⊓ Wα'.U0)).op).hom h10
            + (Y₁.presheaf.map (homOfLE (inf_le_left : (Wα.U0 ⊓ Wα.U1) ⊓ Wα'.U0 ≤ Wα.U0 ⊓ Wα.U1)).op).hom g'' ∧
        (Y₁.presheaf.map (homOfLE (inf_le_inf_right Wα'.U1 inf_le_left : (Wα.U0 ⊓ Wα.U1) ⊓ Wα'.U1 ≤ Wα.U0 ⊓ Wα'.U1)).op).hom h01
          = (Y₁.presheaf.map (homOfLE (inf_le_inf_right Wα'.U1 inf_le_right : (Wα.U0 ⊓ Wα.U1) ⊓ Wα'.U1 ≤ Wα.U1 ⊓ Wα'.U1)).op).hom h11
            + (Y₁.presheaf.map (homOfLE (inf_le_left : (Wα.U0 ⊓ Wα.U1) ⊓ Wα'.U1 ≤ Wα.U0 ⊓ Wα.U1)).op).hom g'' ∧
        (Y₁.presheaf.map (homOfLE (inf_le_inf_left Wα.U0 inf_le_right : Wα.U0 ⊓ (Wα'.U0 ⊓ Wα'.U1) ≤ Wα.U0 ⊓ Wα'.U1)).op).hom h01
          = (Y₁.presheaf.map (homOfLE (inf_le_inf_left Wα.U0 inf_le_left : Wα.U0 ⊓ (Wα'.U0 ⊓ Wα'.U1) ≤ Wα.U0 ⊓ Wα'.U0)).op).hom h00
            + (Y₁.presheaf.map (homOfLE (inf_le_right : Wα.U0 ⊓ (Wα'.U0 ⊓ Wα'.U1) ≤ Wα'.U0 ⊓ Wα'.U1)).op).hom g ∧
        (Y₁.presheaf.map (homOfLE (inf_le_inf_left Wα.U1 inf_le_right : Wα.U1 ⊓ (Wα'.U0 ⊓ Wα'.U1) ≤ Wα.U1 ⊓ Wα'.U1)).op).hom h11
          = (Y₁.presheaf.map (homOfLE (inf_le_inf_left Wα.U1 inf_le_left : Wα.U1 ⊓ (Wα'.U0 ⊓ Wα'.U1) ≤ Wα.U1 ⊓ Wα'.U0)).op).hom h10
            + (Y₁.presheaf.map (homOfLE (inf_le_right : Wα.U1 ⊓ (Wα'.U0 ⊓ Wα'.U1) ≤ Wα'.U0 ⊓ Wα'.U1)).op).hom g) := by

  obtain ⟨e₀, e₁, g'', he₀, he₁, heg⟩ :=
    AlgebraicGeometry.RelPicard.exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit
      y K (NormDefTriv.preimageCover πα 𝒲) L hLinv hL0
  refine ⟨g'', ⟨e₀, e₁, he₀, he₁, heg⟩, ?_, ?_⟩
  · obtain ⟨k00, k01, k10, k11, r1, r2, r3, r4⟩ :=
      AlgebraicGeometry.RelPicard.exists_crossSections_of_isFrameOn_of_map_eq_oneAddEpsMul_smul y K
        (NormDefTriv.preimageCover πα 𝒲) (NormDefTriv.preimageCover πβ 𝒲) L e₀ e₁ g'' he₀ he₁ heg b₀ b₁ tβ hb₀ hb₁ hbt
    exact ⟨k00, k01, k10, k11, r1, r2, r3, r4⟩
  · obtain ⟨h00, h01, h10, h11, r1, r2, r3, r4⟩ :=
      AlgebraicGeometry.RelPicard.exists_crossSections_of_isFrameOn_of_map_eq_oneAddEpsMul_smul y K
        (NormDefTriv.preimageCover πα 𝒲) (NormDefTriv.preimageCover πα 𝒲') L e₀ e₁ g'' he₀ he₁ heg s₀ s₁ g hs₀ hs₁ hsg
    exact ⟨h00, h01, h10, h11, r1, r2, r3, r4⟩

end Step7a
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_field.NormDefTriv"

namespace CorrH1Kit

open Opposite TopologicalSpace

section Down
variable {Y Y₁ : Scheme.{u}} (f : Y₁ ⟶ Y) [IsIso f]

noncomputable def down (V : Y.Opens) : Γ(Y₁, f ⁻¹ᵁ V) →+* Γ(Y, V) := (inv (f.app V)).hom

theorem down_app (V : Y.Opens) (a : Γ(Y, V)) : down f V (f.app V a) = a := by
  change (f.app V ≫ inv (f.app V)).hom a = a
  rw [IsIso.hom_inv_id]; rfl

theorem app_down (V : Y.Opens) (z : Γ(Y₁, f ⁻¹ᵁ V)) : f.app V (down f V z) = z := by
  change (inv (f.app V) ≫ f.app V).hom z = z
  rw [IsIso.inv_hom_id]; rfl

theorem map_down {V V' : Y.Opens} (i : V' ≤ V) (z : Γ(Y₁, f ⁻¹ᵁ V)) :
    Y.presheaf.map (homOfLE i).op (down f V z) =
      down f V' (Y₁.presheaf.map (homOfLE (f.preimage_mono i)).op z) := by
  have hnat := f.naturality (homOfLE i).op
  have key : f.app V' (Y.presheaf.map (homOfLE i).op (down f V z)) =
      Y₁.presheaf.map (homOfLE (f.preimage_mono i)).op z := by
    change (Y.presheaf.map (homOfLE i).op ≫ f.app V') (down f V z) = _
    rw [hnat]
    change Y₁.presheaf.map _ (f.app V (down f V z)) = _
    rw [app_down]
    rfl
  rw [← key, down_app]

end Down
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_field.NormDefTriv"

section Germ
variable {Y Y₁ : Scheme.{u}} (f : Y₁ ⟶ Y) [IsIso f] [IsIntegral Y]

noncomputable def Gm (V : Y.Opens) [Nonempty V] {V₁ : Y₁.Opens} (h : f ⁻¹ᵁ V ≤ V₁) (z : Γ(Y₁, V₁)) :
    Y.functionField :=
  (Y.germToFunctionField V).hom (down f V (Y₁.presheaf.map (homOfLE h).op z))

theorem Gm_add (V : Y.Opens) [Nonempty V] {V₁ : Y₁.Opens} (h : f ⁻¹ᵁ V ≤ V₁) (z z' : Γ(Y₁, V₁)) :
    Gm f V h (z + z') = Gm f V h z + Gm f V h z' := by
  simp only [Gm, map_add]

theorem Gm_sub (V : Y.Opens) [Nonempty V] {V₁ : Y₁.Opens} (h : f ⁻¹ᵁ V ≤ V₁) (z z' : Γ(Y₁, V₁)) :
    Gm f V h (z - z') = Gm f V h z - Gm f V h z' := by
  simp only [Gm, map_sub]

theorem Gm_neg (V : Y.Opens) [Nonempty V] {V₁ : Y₁.Opens} (h : f ⁻¹ᵁ V ≤ V₁) (z : Γ(Y₁, V₁)) :
    Gm f V h (-z) = -Gm f V h z := by
  simp only [Gm, map_neg]

theorem Gm_res {V V' : Y.Opens} [Nonempty V] [Nonempty V'] (i : V' ≤ V) {V₁ V₁' : Y₁.Opens}
    (h : f ⁻¹ᵁ V ≤ V₁) (h' : f ⁻¹ᵁ V' ≤ V₁') (e : V₁' ≤ V₁) (z : Γ(Y₁, V₁)) :
    Gm f V h z = Gm f V' h' (Y₁.presheaf.map (homOfLE e).op z) := by
  unfold Gm
  have hg : (Y.germToFunctionField V).hom (down f V (Y₁.presheaf.map (homOfLE h).op z)) =
      (Y.germToFunctionField V').hom
        (Y.presheaf.map (homOfLE i).op (down f V (Y₁.presheaf.map (homOfLE h).op z))) := by
    change _ = (Y.presheaf.map (homOfLE i).op ≫ Y.germToFunctionField V') _
    rw [Scheme.germToFunctionField, Scheme.germToFunctionField, TopCat.Presheaf.germ_res]
  rw [hg, map_down]
  congr 2
  change (Y₁.presheaf.map (homOfLE h).op ≫ Y₁.presheaf.map _) z = (Y₁.presheaf.map (homOfLE e).op ≫ Y₁.presheaf.map _) z
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

theorem Gm_res' {V V' : Y.Opens} [Nonempty V] [Nonempty V'] (i : V' ≤ V) {V₁ : Y₁.Opens}
    (h : f ⁻¹ᵁ V ≤ V₁) (h' : f ⁻¹ᵁ V' ≤ V₁) (z : Γ(Y₁, V₁)) :
    Gm f V h z = Gm f V' h' z := by
  rw [Gm_res f i h h' le_rfl z]
  congr 1
  have hid : (homOfLE (le_refl V₁)).op = 𝟙 (op V₁) := rfl
  change (Y₁.presheaf.map (homOfLE (le_refl V₁)).op) z = z
  rw [hid, Y₁.presheaf.map_id]; rfl

theorem Gm_appLE {X : Scheme.{u}} (π₁ : Y ⟶ X) (g : Y₁ ⟶ X) (hg : g = f ≫ π₁) (U : X.Opens)
    [Nonempty (π₁ ⁻¹ᵁ U : Y.Opens)] (V₁ : Y₁.Opens) (hle : V₁ ≤ g ⁻¹ᵁ U) (h : f ⁻¹ᵁ (π₁ ⁻¹ᵁ U) ≤ V₁)
    (a : Γ(X, U)) :
    Gm f (π₁ ⁻¹ᵁ U) h (g.appLE U V₁ hle a) = (Y.germToFunctionField (π₁ ⁻¹ᵁ U)).hom (π₁.app U a) := by
  subst hg
  unfold Gm
  congr 1
  have h1 : Y₁.presheaf.map (homOfLE h).op ((f ≫ π₁).appLE U V₁ hle a) = (f ≫ π₁).app U a := by
    change ((f ≫ π₁).appLE U V₁ hle ≫ Y₁.presheaf.map (homOfLE h).op) a = _
    rw [Scheme.Hom.appLE_map, Scheme.Hom.app_eq_appLE]
    rfl
  rw [h1, Scheme.Hom.comp_app]
  exact down_app f _ _

theorem Gm_mem {K : Type u} [Field K] (cY : Y ⟶ Spec (.of K)) [IsSeparated cY] [SmoothOfRelativeDimension 1 cY]
    (U U' : Y.Opens) [Nonempty (U ⊓ U' : Y.Opens)] {V₁ : Y₁.Opens} (h : f ⁻¹ᵁ (U ⊓ U') ≤ V₁) (z : Γ(Y₁, V₁)) :
    letI := (baseToFunctionField cY).toAlgebra
    Gm f (U ⊓ U') h z ∈ lSpaceOn (placesOf cY U ∩ placesOf cY U') (0 : Divisor K Y.functionField) :=
  AlgebraicCurve.germToFunctionField_inf_mem_lSpaceOn_inter_placesOf cY U U' _

end Germ
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_field.NormDefTriv"

theorem nonempty_preimage_of_fromSpecStalk_comp_eq {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
    (φ : X.functionField →+* Y.functionField)
    (hφπ : Y.fromSpecStalk (genericPoint Y) ≫ π = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (genericPoint X))
    (U : X.Opens) [hU : Nonempty (U : X.Opens)] : Nonempty (π ⁻¹ᵁ U : Y.Opens) := by
  have hgen : π (genericPoint Y) = genericPoint X := by
    have h1 := congrArg (fun q => q (IsLocalRing.closedPoint (Y.presheaf.stalk (genericPoint Y)))) hφπ
    simp only [Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint] at h1
    rw [h1]
    have h2 : (Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint (Y.presheaf.stalk (genericPoint Y))) =
        IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X)) := Subsingleton.elim _ _
    rw [h2, Scheme.fromSpecStalk_closedPoint]
  obtain ⟨⟨x, hx⟩⟩ := hU
  have hmem : genericPoint X ∈ (U : Set X) :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, Set.mem_univ _, hx⟩
  exact ⟨⟨genericPoint Y, show π (genericPoint Y) ∈ (U : Set X) by rw [hgen]; exact hmem⟩⟩

section Relations
variable {Y Y₁ : Scheme.{u}} (f : Y₁ ⟶ Y) [IsIso f] [IsIntegral Y]

omit [IsIso f] [IsIntegral Y] in

theorem preimage_preimage_eq {X : Scheme.{u}} (π₁ : Y ⟶ X) (G : Y₁ ⟶ X) (hfac : f ≫ π₁ = G) (U : X.Opens) :
    f ⁻¹ᵁ (π₁ ⁻¹ᵁ U) = G ⁻¹ᵁ U := by
  subst hfac; rfl

theorem Gm_rel_right (A B C : Y₁.Opens) (RA RB RC : Y.Opens)
    (hRA : f ⁻¹ᵁ RA = A) (hRB : f ⁻¹ᵁ RB = B) (hRC : f ⁻¹ᵁ RC = C)
    [Nonempty (RA ⊓ RC : Y.Opens)] [Nonempty (RB ⊓ RC : Y.Opens)] [Nonempty (RA ⊓ RB : Y.Opens)]
    [Nonempty ((RA ⊓ RB) ⊓ RC : Y.Opens)]
    (zA : Γ(Y₁, A ⊓ C)) (zB : Γ(Y₁, B ⊓ C)) (t : Γ(Y₁, A ⊓ B))
    (hrel : (Y₁.presheaf.map (homOfLE (inf_le_inf_right C inf_le_left : (A ⊓ B) ⊓ C ≤ A ⊓ C)).op).hom zA
      = (Y₁.presheaf.map (homOfLE (inf_le_inf_right C inf_le_right : (A ⊓ B) ⊓ C ≤ B ⊓ C)).op).hom zB
        + (Y₁.presheaf.map (homOfLE (inf_le_left : (A ⊓ B) ⊓ C ≤ A ⊓ B)).op).hom t) :
    Gm f (RA ⊓ RC) (show f ⁻¹ᵁ (RA ⊓ RC) ≤ A ⊓ C by rw [Scheme.Hom.preimage_inf, hRA, hRC]) zA =
      Gm f (RB ⊓ RC) (show f ⁻¹ᵁ (RB ⊓ RC) ≤ B ⊓ C by rw [Scheme.Hom.preimage_inf, hRB, hRC]) zB +
        Gm f (RA ⊓ RB) (show f ⁻¹ᵁ (RA ⊓ RB) ≤ A ⊓ B by rw [Scheme.Hom.preimage_inf, hRA, hRB]) t := by
  have hA : f ⁻¹ᵁ (RA ⊓ RC) ≤ A ⊓ C := by rw [Scheme.Hom.preimage_inf, hRA, hRC]
  have hB : f ⁻¹ᵁ (RB ⊓ RC) ≤ B ⊓ C := by rw [Scheme.Hom.preimage_inf, hRB, hRC]
  have hT : f ⁻¹ᵁ (RA ⊓ RB) ≤ A ⊓ B := by rw [Scheme.Hom.preimage_inf, hRA, hRB]
  have h3 : f ⁻¹ᵁ ((RA ⊓ RB) ⊓ RC) ≤ (A ⊓ B) ⊓ C := by
    rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf, hRA, hRB, hRC]
  rw [Gm_res f (inf_le_inf_right RC inf_le_left : (RA ⊓ RB) ⊓ RC ≤ RA ⊓ RC) hA h3
        (inf_le_inf_right C inf_le_left : (A ⊓ B) ⊓ C ≤ A ⊓ C) zA,
      Gm_res f (inf_le_inf_right RC inf_le_right : (RA ⊓ RB) ⊓ RC ≤ RB ⊓ RC) hB h3
        (inf_le_inf_right C inf_le_right : (A ⊓ B) ⊓ C ≤ B ⊓ C) zB,
      Gm_res f (inf_le_left : (RA ⊓ RB) ⊓ RC ≤ RA ⊓ RB) hT h3
        (inf_le_left : (A ⊓ B) ⊓ C ≤ A ⊓ B) t, ← Gm_add]
  exact congrArg (Gm f ((RA ⊓ RB) ⊓ RC) h3) hrel

theorem Gm_rel_left (A B C : Y₁.Opens) (RA RB RC : Y.Opens)
    (hRA : f ⁻¹ᵁ RA = A) (hRB : f ⁻¹ᵁ RB = B) (hRC : f ⁻¹ᵁ RC = C)
    [Nonempty (RA ⊓ RC : Y.Opens)] [Nonempty (RA ⊓ RB : Y.Opens)] [Nonempty (RB ⊓ RC : Y.Opens)]
    [Nonempty (RA ⊓ (RB ⊓ RC) : Y.Opens)]
    (z₁ : Γ(Y₁, A ⊓ C)) (z₀ : Γ(Y₁, A ⊓ B)) (t' : Γ(Y₁, B ⊓ C))
    (hrel : (Y₁.presheaf.map (homOfLE (inf_le_inf_left A inf_le_right : A ⊓ (B ⊓ C) ≤ A ⊓ C)).op).hom z₁
      = (Y₁.presheaf.map (homOfLE (inf_le_inf_left A inf_le_left : A ⊓ (B ⊓ C) ≤ A ⊓ B)).op).hom z₀
        + (Y₁.presheaf.map (homOfLE (inf_le_right : A ⊓ (B ⊓ C) ≤ B ⊓ C)).op).hom t') :
    Gm f (RA ⊓ RC) (show f ⁻¹ᵁ (RA ⊓ RC) ≤ A ⊓ C by rw [Scheme.Hom.preimage_inf, hRA, hRC]) z₁ =
      Gm f (RA ⊓ RB) (show f ⁻¹ᵁ (RA ⊓ RB) ≤ A ⊓ B by rw [Scheme.Hom.preimage_inf, hRA, hRB]) z₀ +
        Gm f (RB ⊓ RC) (show f ⁻¹ᵁ (RB ⊓ RC) ≤ B ⊓ C by rw [Scheme.Hom.preimage_inf, hRB, hRC]) t' := by
  have h₁ : f ⁻¹ᵁ (RA ⊓ RC) ≤ A ⊓ C := by rw [Scheme.Hom.preimage_inf, hRA, hRC]
  have h₀ : f ⁻¹ᵁ (RA ⊓ RB) ≤ A ⊓ B := by rw [Scheme.Hom.preimage_inf, hRA, hRB]
  have hT : f ⁻¹ᵁ (RB ⊓ RC) ≤ B ⊓ C := by rw [Scheme.Hom.preimage_inf, hRB, hRC]
  have h3 : f ⁻¹ᵁ (RA ⊓ (RB ⊓ RC)) ≤ A ⊓ (B ⊓ C) := by
    rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf, hRA, hRB, hRC]
  rw [Gm_res f (inf_le_inf_left RA inf_le_right : RA ⊓ (RB ⊓ RC) ≤ RA ⊓ RC) h₁ h3
        (inf_le_inf_left A inf_le_right : A ⊓ (B ⊓ C) ≤ A ⊓ C) z₁,
      Gm_res f (inf_le_inf_left RA inf_le_left : RA ⊓ (RB ⊓ RC) ≤ RA ⊓ RB) h₀ h3
        (inf_le_inf_left A inf_le_left : A ⊓ (B ⊓ C) ≤ A ⊓ B) z₀,
      Gm_res f (inf_le_right : RA ⊓ (RB ⊓ RC) ≤ RB ⊓ RC) hT h3
        (inf_le_right : A ⊓ (B ⊓ C) ≤ B ⊓ C) t', ← Gm_add]
  exact congrArg (Gm f (RA ⊓ (RB ⊓ RC)) h3) hrel

end Relations
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_field.NormDefTriv"

theorem nonempty_inf {Y : Scheme.{u}} [IrreducibleSpace Y] (U V : Y.Opens) [hU : Nonempty (U : Y.Opens)]
    [hV : Nonempty (V : Y.Opens)] : Nonempty (U ⊓ V : Y.Opens) := by
  obtain ⟨⟨u, hu⟩⟩ := hU
  obtain ⟨⟨v, hv⟩⟩ := hV
  obtain ⟨z, hz⟩ := nonempty_preirreducible_inter U.isOpen V.isOpen ⟨u, hu⟩ ⟨v, hv⟩
  exact ⟨⟨z, hz⟩⟩

theorem germ_map {X : Scheme.{u}} [IsIntegral X] {U V : X.Opens} [Nonempty (U : X.Opens)] [Nonempty (V : X.Opens)]
    (i : U ≤ V) (s : Γ(X, V)) :
    (X.germToFunctionField U).hom ((X.presheaf.map (homOfLE i).op).hom s) = (X.germToFunctionField V).hom s := by
  change (X.presheaf.map (homOfLE i).op ≫ X.germToFunctionField U) s = _
  rw [Scheme.germToFunctionField, Scheme.germToFunctionField, TopCat.Presheaf.germ_res]

theorem germ_trace_eq_traceFunAlong_Gm
    {K : Type u} [Field K] {X Y Y₁ : Scheme.{u}} (cX : X ⟶ Spec (.of K)) (cY : Y ⟶ Spec (.of K))
    [IsIntegral X] [IsIntegral Y] (f : Y₁ ⟶ Y) [IsIso f]
    (π₁ : Y ⟶ X) [IsAffineHom π₁] (hπ : π₁ ≫ cX = cY) (g : Y₁ ⟶ X) (hg : g = f ≫ π₁)
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty (U : X.Opens)] [Nonempty (π₁ ⁻¹ᵁ U : Y.Opens)]
    (V₁ : Y₁.Opens) (hV₁ : V₁ = g ⁻¹ᵁ U) (hle : f ⁻¹ᵁ (π₁ ⁻¹ᵁ U) ≤ V₁) :
    letI := (baseToFunctionField cX).toAlgebra
    letI := (baseToFunctionField cY).toAlgebra
    letI : Algebra Γ(X, U) Γ(Y₁, V₁) := (g.appLE U V₁ hV₁.le).hom.toAlgebra
    ∀ [Module.Free Γ(X, U) Γ(Y₁, V₁)] [Module.Finite Γ(X, U) Γ(Y₁, V₁)]
      (φ : X.functionField →ₐ[K] Y.functionField)
      (hφπ : Y.fromSpecStalk (genericPoint Y) ≫ π₁ =
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ X.fromSpecStalk (genericPoint X))
      (z : Γ(Y₁, V₁)),
      (X.germToFunctionField U).hom (Algebra.trace Γ(X, U) Γ(Y₁, V₁) z) =
        AlgebraicCurve.traceFunAlong φ (Gm f (π₁ ⁻¹ᵁ U) hle z) := by
  intro _ _ φ hφπ z
  subst hg
  subst hV₁
  letI algB₁ : Algebra Γ(X, U) Γ(Y₁, (f ≫ π₁) ⁻¹ᵁ U) :=
    ((f ≫ π₁).appLE U ((f ≫ π₁) ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  letI algB : Algebra Γ(X, U) Γ(Y, π₁ ⁻¹ᵁ U) := (π₁.app U).hom.toAlgebra

  let eR : Γ(Y₁, (f ≫ π₁) ⁻¹ᵁ U) ≃+* Γ(Y, π₁ ⁻¹ᵁ U) := (asIso (f.app (π₁ ⁻¹ᵁ U))).commRingCatIsoToRingEquiv.symm
  have heR : ∀ w, eR w = down f (π₁ ⁻¹ᵁ U) w := fun w => rfl
  let e : Γ(Y₁, (f ≫ π₁) ⁻¹ᵁ U) ≃ₐ[Γ(X, U)] Γ(Y, π₁ ⁻¹ᵁ U) :=
    { eR with
      commutes' := fun a => by
        change eR (((f ≫ π₁).appLE U ((f ≫ π₁) ⁻¹ᵁ U) le_rfl).hom a) = (π₁.app U).hom a
        rw [heR, ← Scheme.Hom.app_eq_appLE, Scheme.Hom.comp_app]
        exact down_app f _ _ }
  have he : ∀ w, e w = down f (π₁ ⁻¹ᵁ U) w := fun w => rfl
  haveI : Module.Free Γ(X, U) Γ(Y, π₁ ⁻¹ᵁ U) := Module.Free.of_equiv e.toLinearEquiv
  haveI : Module.Finite Γ(X, U) Γ(Y, π₁ ⁻¹ᵁ U) := Module.Finite.equiv e.toLinearEquiv
  rw [← Algebra.trace_eq_of_algEquiv e z,
    AlgebraicGeometry.germToFunctionField_trace_eq_traceFunAlong_germToFunctionField cX cY π₁ hπ U hU φ hφπ (e z), he]

  unfold Gm
  congr 2
  show down f (π₁ ⁻¹ᵁ U) z = down f (π₁ ⁻¹ᵁ U) ((Y₁.presheaf.map (𝟙 (op ((f ≫ π₁) ⁻¹ᵁ U)))).hom z)
  rw [CategoryTheory.Functor.map_id]
  rfl

end CorrH1Kit
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_field.NormDefTriv"

set_option maxHeartbeats 6400000 in

theorem solution
    (K : Type u) [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) (ε : SchemeHomOver (𝟙 (Spec (.of K))) c)
    [IsIntegral (Limits.pullback c (specMap K K))]
    [IsSeparated (pullback.snd c (specMap K K))]
    [SmoothOfRelativeDimension 1 (pullback.snd c (specMap K K))]

    (hC : ∀ Z : Set C, IsClosed Z → Z ≠ Set.univ → Z.Finite)
    (D : RelativePic0Designation K c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)

    {Y : Scheme.{u}} (y : Y ⟶ Spec (.of K)) [IsIntegral Y] [IsProper y] [SmoothOfRelativeDimension 1 y]
    (πα πβ : Y ⟶ C) (Hα : πα ≫ c = y) (Hβ : πβ ≫ c = y)
    [IsFinite πα] [Flat πα] [LocallyOfFinitePresentation πα] [IsAffineHom πβ]
    (d : ℕ) (hd : ∀ z, πα.finrank z = d)
    (πα₁ πβ₁ : Y ⟶ Limits.pullback c (specMap K K))
    (hα₁ : πα₁ ≫ pullback.fst c (specMap K K) = πα) (hα₁' : πα₁ ≫ pullback.snd c (specMap K K) = y)
    (hβ₁ : πβ₁ ≫ pullback.fst c (specMap K K) = πβ) (hβ₁' : πβ₁ ≫ pullback.snd c (specMap K K) = y)

    (φ₁ : SchemeHomOver D.toBase D.toBase)
    (hmoduli :
      ∀ (T : Scheme.{u}) (t : T ⟶ Spec (.of K))
          (M : RigidifiedLineBundle c ε t) (hM : (algEquivZeroCut c ε).P t M),
        Nonempty ((h.poincare.pullbackAlong
            (NeronModelInfra.schemeHomOverComp (h.classify t M hM) φ₁)).L ≅
          Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
            (Scheme.Modules.normModule (curveChange (c' := y) πα Hα t) d
              ((Scheme.Modules.pullback (curveChange (c' := y) πβ Hβ t)).obj M.L))))

    (𝒲 : C.TwoAffineOpenCover)
    {δ : RigKerDualNumber c ε K → H1StructureSheaf c K 𝒲} (hδ : IsDeformationClassMap c ε K 𝒲 δ)
    (x xr : {x : SchemeHomOver (specMap K (DualNumber K)) D.toBase //
        dualNumberReduction K K ≫ x.1 =
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one (specMap K K)).1})
    (hxr : xr.1.1 = x.1.1 ≫ φ₁.1)
    (s : ((𝒲.pullback c K).cover (pullback.snd c (specMap K K))).A01)
    (hs : δ (h.kerPointsToRigKer K x) = Submodule.Quotient.mk s) :
    letI X' := Limits.pullback c (specMap K K)
    letI c' : X' ⟶ Spec (.of K) := pullback.snd c (specMap K K)
    letI := (AlgebraicCurve.baseToFunctionField c').toAlgebra
    letI := (AlgebraicCurve.baseToFunctionField y).toAlgebra
    letI W := 𝒲.pullback c K
    ∀ [Nonempty (W.U0 ⊓ W.U1 : X'.Opens)]

      (φα φβ : X'.functionField →ₐ[K] Y.functionField)
      (hφπα : Y.fromSpecStalk (genericPoint Y) ≫ πα₁ =
        Spec.map (CommRingCat.ofHom φα.toRingHom) ≫ X'.fromSpecStalk (genericPoint X'))
      (hφπβ : Y.fromSpecStalk (genericPoint Y) ≫ πβ₁ =
        Spec.map (CommRingCat.ofHom φβ.toRingHom) ≫ X'.fromSpecStalk (genericPoint X'))
      (hφα : φα.toRingHom.IsIntegral) (hφβ : φβ.toRingHom.IsIntegral) (htrα : TraceIntegralAlong φα hφα)
      (hW : AlgebraicCurve.placesOf c' W.U0 ∪ AlgebraicCurve.placesOf c' W.U1 = Set.univ)
      (hsr : (X'.germToFunctionField (W.U0 ⊓ W.U1)).hom s ∈
        AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c' W.U0 ∩ AlgebraicCurve.placesOf c' W.U1)
          (0 : AlgebraicCurve.Divisor K X'.functionField)),
      ∃ (sr : ((𝒲.pullback c K).cover (pullback.snd c (specMap K K))).A01)
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
  intro _ φα φβ hφπα hφπβ hφα hφβ htrα hW hsr

  obtain ⟨M, hM⟩ := Quotient.exists_rep (h.kerPointsToRigKer K x)
  obtain ⟨e₀, e₁, f, he₀, he₁, hef⟩ :=
    AlgebraicGeometry.RelPicard.RigKerDualNumber.exists_isFrameOn_and_map_eq_oneAddEpsMul_smul c ε K 𝒲 M
  have hδx : δ (h.kerPointsToRigKer K x) = Submodule.Quotient.mk f := by
    rw [← hM]; exact hδ M e₀ e₁ f he₀ he₁ hef
  have hfs : (Submodule.Quotient.mk f : H1StructureSheaf c K 𝒲) = Submodule.Quotient.mk s := hδx.symm.trans hs

  have hMx : Nonempty (M.1.L ≅ (h.poincare.pullbackAlong x.1).L) := by
    have hM' := hM
    unfold RepresentsRelSubPic.kerPointsToRigKer at hM'
    exact Quotient.exact hM'
  let M₀ : RigidifiedLineBundle c ε (specMap K (DualNumber K)) := M.1
  have hM₀ : (algEquivZeroCut c ε).P _ M₀ :=
    (algEquivZeroCut c ε).congr _ _ _ ⟨hMx.some.symm⟩ ((algEquivZeroCut c ε).pullback_mem _ _ x.1 _ h.poincare_mem)
  have hx₀ : x.1 = h.classify _ M₀ hM₀ := h.classify_unique _ M₀ hM₀ x.1 ⟨hMx.some.symm⟩
  obtain ⟨ιr⟩ := hmoduli (Spec (.of (DualNumber K))) (specMap K (DualNumber K)) M₀ hM₀
  rw [← hx₀] at ιr
  have hxr₁ : NeronModelInfra.schemeHomOverComp x.1 φ₁ = xr.1 := by
    apply Subtype.ext
    change x.1.1 ≫ φ₁.1 = xr.1.1
    exact hxr.symm
  rw [hxr₁] at ιr

  obtain ⟨Mr, hMr⟩ := Quotient.exists_rep (h.kerPointsToRigKer K xr)
  have hMr' : Nonempty (Mr.1.L ≅ (h.poincare.pullbackAlong xr.1).L) := by
    unfold RepresentsRelSubPic.kerPointsToRigKer at hMr
    exact Quotient.exact hMr

  let fβ := NormDefTriv.homOver c y πβ Hβ K 𝒲
  let fβε := NormDefTriv.homOver c y πβ Hβ (DualNumber K) 𝒲
  have hcommβ : fβε.hom ≫ (dualNumberThickening K 𝒲 c).hom =
      (dualNumberThickening K (NormDefTriv.preimageCover πβ 𝒲) y).hom ≫ fβ.hom :=
    (NormDefTriv.isPullback_thickening c y πβ Hβ K 𝒲).w
  obtain ⟨b₀, b₁, hb₀, hb₁, hbf⟩ :=
    HomOver.exists_isFrameOn_pullback_of_map_eq_smul fβε M₀.L e₀ e₁ he₀ he₁ (oneAddEpsMul K 𝒲 c f) hef
  have htransβ : fβε.map01 (oneAddEpsMul K 𝒲 c f) =
      oneAddEpsMul K (NormDefTriv.preimageCover πβ 𝒲) y (fβ.map01 f) :=
    AlgebraicGeometry.RelPicard.map01_oneAddEpsMul fβ fβε hcommβ f
  rw [htransβ] at hbf
  have hcurveβ : fβε.hom = curveChange (c' := y) πβ Hβ (specMap K (DualNumber K)) := rfl

  haveI : IsIntegral C := IsIntegral.of_isIso (pullback.fst c (specMap K K))
  obtain ⟨𝒲', hne0, hne1, hbas0, hbas1⟩ := CorrH1Aux.exists_twoAffineOpenCover_forall_basis_nonempty c y πα Hα hC 𝒲 hd
  obtain ⟨eα₀, heα₀⟩ := hbas0
  obtain ⟨eα₁, heα₁⟩ := hbas1

  let L : (Limits.pullback y (specMap K (DualNumber K))).Modules :=
    (Scheme.Modules.pullback (curveChange (c' := y) πβ Hβ (specMap K (DualNumber K)))).obj M₀.L
  have hLinv : Scheme.Modules.IsInvertible L := M₀.isInvertible.pullback _
  have hcommred : RelPicard.baseChangeSnd y (dualNumberReductionOver K K) ≫
      curveChange (c' := y) πβ Hβ (specMap K (DualNumber K)) =
        curveChange (c' := y) πβ Hβ (specMap K K) ≫ RelPicard.baseChangeSnd c (dualNumberReductionOver K K) :=
    (curveChange_baseChangeSnd πβ Hβ (dualNumberReductionOver K K)).symm
  have hL0 : Nonempty ((Scheme.Modules.pullback (RelPicard.baseChangeSnd y (dualNumberReductionOver K K))).obj L ≅
      SheafOfModules.unit.{u} (Limits.pullback y (specMap K K)).ringCatSheaf) :=
    ⟨(Scheme.Modules.pullbackComp (RelPicard.baseChangeSnd y (dualNumberReductionOver K K))
        (curveChange (c' := y) πβ Hβ (specMap K (DualNumber K)))).app M₀.L ≪≫
      (Scheme.Modules.pullbackCongr hcommred).app M₀.L ≪≫
      ((Scheme.Modules.pullbackComp (curveChange (c' := y) πβ Hβ (specMap K K))
        (RelPicard.baseChangeSnd c (dualNumberReductionOver K K))).app M₀.L).symm ≪≫
      (Scheme.Modules.pullback (curveChange (c' := y) πβ Hβ (specMap K K))).mapIso M.2.some ≪≫
      Scheme.Modules.pullbackUnitIso _⟩

  let 𝒲α' := NormDefTriv.preimageCover πα 𝒲'
  obtain ⟨s₀, s₁, g, hs₀, hs₁, hsg⟩ :=
    AlgebraicGeometry.RelPicard.exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit
      y K 𝒲α' L hLinv hL0

  let fα := NormDefTriv.homOver c y πα Hα K 𝒲'
  let fαε := NormDefTriv.homOver c y πα Hα (DualNumber K) 𝒲'
  have hsq := NormDefTriv.isPullback_thickening c y πα Hα K 𝒲'
  haveI : IsAffineHom fα.hom := by rw [NormDefTriv.homOver_hom]; infer_instance
  haveI : IsFinite fαε.hom := by rw [NormDefTriv.homOver_hom]; infer_instance
  haveI : Flat fαε.hom := by rw [NormDefTriv.homOver_hom]; infer_instance
  haveI : LocallyOfFinitePresentation fαε.hom := by rw [NormDefTriv.homOver_hom]; infer_instance
  have hdε : ∀ z, fαε.hom.finrank z = d := fun z => NormDefTriv.finrank_curveChange c y πα Hα _ hd z
  have hW0 := NormDefTriv.preimageCover_pullback_U0 c y πα Hα K 𝒲'
  have hW1 := NormDefTriv.preimageCover_pullback_U1 c y πα Hα K 𝒲'
  have hW0ε := NormDefTriv.preimageCover_pullback_U0 c y πα Hα (DualNumber K) 𝒲'
  have hW1ε := NormDefTriv.preimageCover_pullback_U1 c y πα Hα (DualNumber K) 𝒲'
  obtain ⟨eε₀, heε₀⟩ :=
    AlgebraicGeometry.RelPicard.exists_forall_basis_pushforward_dualNumberThickening_of_forall_basis c y K 𝒲' 𝒲α' fα fαε
      hsq d (𝒲'.pullback c K).U0 ((𝒲'.pullback c (DualNumber K)).U0)
      (baseChangeSnd_preimage_U0 𝒲' c (RelPicard.LFP.stageHom K (IsScalarTower.toAlgHom K K (DualNumber K)))).symm eα₀ heα₀
  obtain ⟨eε₁, heε₁⟩ :=
    AlgebraicGeometry.RelPicard.exists_forall_basis_pushforward_dualNumberThickening_of_forall_basis c y K 𝒲' 𝒲α' fα fαε
      hsq d (𝒲'.pullback c K).U1 ((𝒲'.pullback c (DualNumber K)).U1)
      (baseChangeSnd_preimage_U1 𝒲' c (RelPicard.LFP.stageHom K (IsScalarTower.toAlgHom K K (DualNumber K)))).symm eα₁ heα₁

  have hV : (𝒲α'.pullback y K).U0 ⊓ (𝒲α'.pullback y K).U1 =
      fα.hom ⁻¹ᵁ ((𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1) := by
    rw [Scheme.Hom.preimage_inf, hW0, hW1]; rfl
  obtain ⟨bas, -⟩ := heα₀ ((𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1) inf_le_left
  letI instA01 : Algebra ((𝒲'.pullback c K).cover (pullback.snd c (specMap K K))).A01
      ((𝒲α'.pullback y K).cover (pullback.snd y (specMap K K))).A01 :=
    (fα.hom.appLE ((𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1) ((𝒲α'.pullback y K).U0 ⊓ (𝒲α'.pullback y K).U1)
      fα.inf_le).hom.toAlgebra
  letI instΓ : Algebra Γ(Limits.pullback c (specMap K K), (𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1)
      Γ(Limits.pullback y (specMap K K), (𝒲α'.pullback y K).U0 ⊓ (𝒲α'.pullback y K).U1) :=
    (fα.hom.appLE ((𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1) ((𝒲α'.pullback y K).U0 ⊓ (𝒲α'.pullback y K).U1)
      hV.le).hom.toAlgebra
  have hfreefin : ∃ (_ : Module.Free ((𝒲'.pullback c K).cover (pullback.snd c (specMap K K))).A01
        ((𝒲α'.pullback y K).cover (pullback.snd y (specMap K K))).A01)
      (_ : Module.Finite ((𝒲'.pullback c K).cover (pullback.snd c (specMap K K))).A01
        ((𝒲α'.pullback y K).cover (pullback.snd y (specMap K K))).A01), True := by

    have aux : ∀ (V : (Limits.pullback y (specMap K K)).Opens)
        (hV' : V = fα.hom ⁻¹ᵁ ((𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1)),
        letI := (fα.hom.appLE ((𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1) V hV'.le).hom.toAlgebra
        ∃ (_ : Module.Free Γ(Limits.pullback c (specMap K K), (𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1)
              Γ(Limits.pullback y (specMap K K), V))
          (_ : Module.Finite Γ(Limits.pullback c (specMap K K), (𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1)
              Γ(Limits.pullback y (specMap K K), V)), True := by
      intro V hV'
      generalize hφ : fα.hom.appLE ((𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1) V hV'.le = φ
      subst hV'
      obtain rfl : φ = fα.hom.app _ := by rw [← hφ]; exact (Scheme.Hom.app_eq_appLE fα.hom).symm
      letI : Algebra Γ(Limits.pullback c (specMap K K), (𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1)
          Γ(Limits.pullback y (specMap K K), fα.hom ⁻¹ᵁ ((𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1)) :=
        (fα.hom.app _).hom.toAlgebra
      exact ⟨Module.Free.of_basis bas, Module.Finite.of_basis bas, trivial⟩
    exact aux _ hV
  obtain ⟨hfree, hfin, -⟩ := hfreefin
  haveI := hfree
  haveI := hfin
  have key := AlgebraicGeometry.RelPicard.exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul c y K 𝒲' 𝒲α'
    fα fαε hsq hW0 hW1 hW0ε hW1ε d hdε eε₀ heε₀ eε₁ heε₁ L s₀ s₁ hs₀ hs₁ g hsg
  obtain ⟨Ω₀, Ω₁, hΩ₀, hΩ₁, hΩ⟩ := key

  let Nm := Scheme.Modules.normModule fαε.hom d L
  have hNm_inv : Scheme.Modules.IsInvertible Nm := by
    refine ⟨fun z => ?_⟩
    have hz : z ∈ ((𝒲'.pullback c (DualNumber K)).U0 ⊔ (𝒲'.pullback c (DualNumber K)).U1 : (Limits.pullback c _).Opens) := by
      rw [(𝒲'.pullback c (DualNumber K)).sup_eq_top]; trivial
    rcases hz with hz | hz
    · exact ⟨_, hz, AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_pullback_iso_unit hΩ₀ _ le_rfl le_rfl⟩
    · exact ⟨_, hz, AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_pullback_iso_unit hΩ₁ _ le_rfl le_rfl⟩
  let σ := rigSection c (specMap K (DualNumber K)) ε
  have hσNm : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback σ).obj Nm) := hNm_inv.pullback σ
  have hσNm0 : Nonempty ((Scheme.Modules.pullback σ).obj Nm ≅ SheafOfModules.unit.{u} (Spec (.of (DualNumber K))).ringCatSheaf) := by
    refine AlgebraicGeometry.RelPicard.Scheme.Modules.IsInvertible.nonempty_iso_unit_of_dualNumber_of_reduction K _ hσNm ?_
    exact AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field K _ (hσNm.pullback _)
  obtain ⟨ιrig⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_rigidify_iso_of_nonempty_pullback_iso_unit σ
    (pullback.snd c (specMap K (DualNumber K))) Nm hσNm0
  obtain ⟨ιfin⟩ : Nonempty (Mr.1.L ≅ Nm) := ⟨hMr'.some ≪≫ ιr ≪≫ ιrig⟩

  let Ωr₀ := ιfin.symm.hom.app _ Ω₀
  let Ωr₁ := ιfin.symm.hom.app _ Ω₁
  have hΩr₀ := hΩ₀.map_iso ιfin.symm
  have hΩr₁ := hΩ₁.map_iso ιfin.symm
  let U0ε := (𝒲'.pullback c (DualNumber K)).U0
  let U1ε := (𝒲'.pullback c (DualNumber K)).U1
  have hle0 : U0ε ⊓ U1ε ≤ U0ε := inf_le_left
  have hle1 : U0ε ⊓ U1ε ≤ U1ε := inf_le_right
  have hΩr := CorrH1Aux.map_eq_smul_of_hom ιfin.symm.hom Ω₀ Ω₁ _ hΩ

  obtain ⟨δ', hδ'⟩ := AlgebraicGeometry.RelPicard.exists_isDeformationClassMap c ε K 𝒲'
  have hδ'xr := hδ' Mr Ωr₀ Ωr₁ _ hΩr₀ hΩr₁ hΩr
  rw [hMr] at hδ'xr

  obtain ⟨sr, hsr0⟩ := Submodule.Quotient.mk_surjective _ (δ (h.kerPointsToRigKer K xr))
  haveI : Nonempty ((𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1 : (Limits.pullback c (specMap K K)).Opens) := by
    obtain ⟨z, hz⟩ := nonempty_preirreducible_inter (𝒲'.pullback c K).U0.isOpen (𝒲'.pullback c K).U1.isOpen hne0 hne1
    exact ⟨⟨z, hz⟩⟩
  have hW' : AlgebraicCurve.placesOf (pullback.snd c (specMap K K)) (𝒲'.pullback c K).U0 ∪
      AlgebraicCurve.placesOf (pullback.snd c (specMap K K)) (𝒲'.pullback c K).U1 = Set.univ := by
    rw [← AlgebraicCurve.placesOf_sup, (𝒲'.pullback c K).sup_eq_top, ← (𝒲.pullback c K).sup_eq_top,
      AlgebraicCurve.placesOf_sup]
    exact hW
  have hind := AlgebraicGeometry.RelPicard.IsDeformationClassMap.cechH1ToH1_germ_eq_of_two_covers c ε K 𝒲 𝒲' hδ hδ'
    (h.kerPointsToRigKer K xr) sr _ hsr0.symm hδ'xr hW hW'

  haveI : IsSeparated (pullback.snd y (specMap K K)) := inferInstance
  obtain ⟨g'', ⟨eb₀, eb₁, heb₀, heb₁, hebg⟩, ⟨k00, k01, k10, k11, hk1, hk2, hk3, hk4⟩, ⟨h00, h01, h10, h11, hh1, hh2, hh3, hh4⟩⟩ :=
    Step7a.upstairs_package K y πα πβ 𝒲 𝒲' L hLinv hL0 (fβ.map01 f) b₀ b₁ hb₀ hb₁ hbf g s₀ s₁ hs₀ hs₁ hsg

  letI := (AlgebraicCurve.baseToFunctionField (pullback.snd c (specMap K K))).toAlgebra
  letI := (AlgebraicCurve.baseToFunctionField y).toAlgebra
  have hKK : specMap K K = 𝟙 (Spec (.of K)) := by
    simp only [Scheme.TwoAffineOpenCover.specMap, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hfacα : pullback.fst y (specMap K K) ≫ πα₁ = curveChange (c' := y) πα Hα (specMap K K) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hα₁, NormDefTriv.curveChange_fst]
    · rw [Category.assoc, hα₁', curveChange_snd, pullback.condition, hKK, Category.comp_id]
  have hfacβ : pullback.fst y (specMap K K) ≫ πβ₁ = curveChange (c' := y) πβ Hβ (specMap K K) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hβ₁, NormDefTriv.curveChange_fst]
    · rw [Category.assoc, hβ₁', curveChange_snd, pullback.condition, hKK, Category.comp_id]
  haveI : IsSeparated (pullback.fst c (specMap K K)) := MorphismProperty.pullback_fst _ _ inferInstance
  haveI : IsAffineHom πα₁ := MorphismProperty.of_postcomp (W := @IsAffineHom) (W' := @IsSeparated)
    πα₁ (pullback.fst c (specMap K K)) inferInstance (by rw [hα₁]; infer_instance)
  haveI : UniversallyClosed πα₁ := MorphismProperty.of_postcomp (W := @UniversallyClosed) (W' := @IsSeparated)
    πα₁ (pullback.snd c (specMap K K)) inferInstance (by rw [hα₁']; infer_instance)
  haveI : UniversallyClosed πβ₁ := MorphismProperty.of_postcomp (W := @UniversallyClosed) (W' := @IsSeparated)
    πβ₁ (pullback.snd c (specMap K K)) inferInstance (by rw [hβ₁']; infer_instance)
  have hPα : ∀ U : (Limits.pullback c (specMap K K)).Opens, AlgebraicCurve.placesOf y (πα₁ ⁻¹ᵁ U) =
      (AlgebraicCurve.Place.restrictAlong φα hφα) ⁻¹' AlgebraicCurve.placesOf (pullback.snd c (specMap K K)) U := fun U =>
    AlgebraicCurve.placesOf_preimage_eq_preimage_restrictAlong_placesOf (pullback.snd c (specMap K K)) y πα₁ φα hφα hφπα U
  have hPβ : ∀ U : (Limits.pullback c (specMap K K)).Opens, AlgebraicCurve.placesOf y (πβ₁ ⁻¹ᵁ U) =
      (AlgebraicCurve.Place.restrictAlong φβ hφβ) ⁻¹' AlgebraicCurve.placesOf (pullback.snd c (specMap K K)) U := fun U =>
    AlgebraicCurve.placesOf_preimage_eq_preimage_restrictAlong_placesOf (pullback.snd c (specMap K K)) y πβ₁ φβ hφβ hφπβ U
  have hRα0 : pullback.fst y (specMap K K) ⁻¹ᵁ (πα₁ ⁻¹ᵁ (𝒲.pullback c K).U0) = ((NormDefTriv.preimageCover πα 𝒲).pullback y K).U0 := by
    rw [CorrH1Kit.preimage_preimage_eq _ πα₁ _ hfacα]; exact (NormDefTriv.preimageCover_pullback_U0 c y πα Hα K 𝒲).symm
  have hRα1 : pullback.fst y (specMap K K) ⁻¹ᵁ (πα₁ ⁻¹ᵁ (𝒲.pullback c K).U1) = ((NormDefTriv.preimageCover πα 𝒲).pullback y K).U1 := by
    rw [CorrH1Kit.preimage_preimage_eq _ πα₁ _ hfacα]; exact (NormDefTriv.preimageCover_pullback_U1 c y πα Hα K 𝒲).symm
  have hRα'0 : pullback.fst y (specMap K K) ⁻¹ᵁ (πα₁ ⁻¹ᵁ (𝒲'.pullback c K).U0) = ((NormDefTriv.preimageCover πα 𝒲').pullback y K).U0 := by
    rw [CorrH1Kit.preimage_preimage_eq _ πα₁ _ hfacα]; exact (NormDefTriv.preimageCover_pullback_U0 c y πα Hα K 𝒲').symm
  have hRα'1 : pullback.fst y (specMap K K) ⁻¹ᵁ (πα₁ ⁻¹ᵁ (𝒲'.pullback c K).U1) = ((NormDefTriv.preimageCover πα 𝒲').pullback y K).U1 := by
    rw [CorrH1Kit.preimage_preimage_eq _ πα₁ _ hfacα]; exact (NormDefTriv.preimageCover_pullback_U1 c y πα Hα K 𝒲').symm
  have hRβ0 : pullback.fst y (specMap K K) ⁻¹ᵁ (πβ₁ ⁻¹ᵁ (𝒲.pullback c K).U0) = ((NormDefTriv.preimageCover πβ 𝒲).pullback y K).U0 := by
    rw [CorrH1Kit.preimage_preimage_eq _ πβ₁ _ hfacβ]; exact (NormDefTriv.preimageCover_pullback_U0 c y πβ Hβ K 𝒲).symm
  have hRβ1 : pullback.fst y (specMap K K) ⁻¹ᵁ (πβ₁ ⁻¹ᵁ (𝒲.pullback c K).U1) = ((NormDefTriv.preimageCover πβ 𝒲).pullback y K).U1 := by
    rw [CorrH1Kit.preimage_preimage_eq _ πβ₁ _ hfacβ]; exact (NormDefTriv.preimageCover_pullback_U1 c y πβ Hβ K 𝒲).symm

  have nW01 : Nonempty ((𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1 : (Limits.pullback c (specMap K K)).Opens) := inferInstance
  obtain ⟨⟨zW, hzW⟩⟩ := nW01
  haveI : Nonempty ((𝒲.pullback c K).U0 : (Limits.pullback c (specMap K K)).Opens) := ⟨⟨zW, hzW.1⟩⟩
  haveI : Nonempty ((𝒲.pullback c K).U1 : (Limits.pullback c (specMap K K)).Opens) := ⟨⟨zW, hzW.2⟩⟩
  haveI : Nonempty ((𝒲'.pullback c K).U0 : (Limits.pullback c (specMap K K)).Opens) := by obtain ⟨z, hz⟩ := hne0; exact ⟨⟨z, hz⟩⟩
  haveI : Nonempty ((𝒲'.pullback c K).U1 : (Limits.pullback c (specMap K K)).Opens) := by obtain ⟨z, hz⟩ := hne1; exact ⟨⟨z, hz⟩⟩
  haveI nYα : ∀ (U : (Limits.pullback c (specMap K K)).Opens) [Nonempty (U : (Limits.pullback c (specMap K K)).Opens)], Nonempty (πα₁ ⁻¹ᵁ U : Y.Opens) :=
    fun U _ => CorrH1Kit.nonempty_preimage_of_fromSpecStalk_comp_eq πα₁ φα.toRingHom hφπα U
  haveI nYβ : ∀ (U : (Limits.pullback c (specMap K K)).Opens) [Nonempty (U : (Limits.pullback c (specMap K K)).Opens)], Nonempty (πβ₁ ⁻¹ᵁ U : Y.Opens) :=
    fun U _ => CorrH1Kit.nonempty_preimage_of_fromSpecStalk_comp_eq πβ₁ φβ.toRingHom hφπβ U
  haveI nYinf : ∀ (U U' : Y.Opens) [Nonempty (U : Y.Opens)] [Nonempty (U' : Y.Opens)], Nonempty (U ⊓ U' : Y.Opens) :=
    fun U U' _ _ => CorrH1Kit.nonempty_inf U U'
  haveI nXinf : ∀ (U U' : (Limits.pullback c (specMap K K)).Opens) [Nonempty (U : (Limits.pullback c (specMap K K)).Opens)] [Nonempty (U' : (Limits.pullback c (specMap K K)).Opens)],
      Nonempty (U ⊓ U' : (Limits.pullback c (specMap K K)).Opens) :=
    fun U U' _ _ => CorrH1Kit.nonempty_inf U U'

  have hI : ∀ {A B : (Limits.pullback y (specMap K K)).Opens} {RA RB : Y.Opens}, pullback.fst y (specMap K K) ⁻¹ᵁ RA = A → pullback.fst y (specMap K K) ⁻¹ᵁ RB = B →
      pullback.fst y (specMap K K) ⁻¹ᵁ (RA ⊓ RB) ≤ A ⊓ B := by
    intro A B RA RB hA hB; rw [Scheme.Hom.preimage_inf, hA, hB]
  let G'' : Y.functionField := CorrH1Kit.Gm (pullback.fst y (specMap K K)) (πα₁ ⁻¹ᵁ (𝒲.pullback c K).U0 ⊓ πα₁ ⁻¹ᵁ (𝒲.pullback c K).U1) (hI hRα0 hRα1) g''
  let Gg : Y.functionField := CorrH1Kit.Gm (pullback.fst y (specMap K K)) (πα₁ ⁻¹ᵁ (𝒲'.pullback c K).U0 ⊓ πα₁ ⁻¹ᵁ (𝒲'.pullback c K).U1) (hI hRα'0 hRα'1) g
  let Gt : Y.functionField := CorrH1Kit.Gm (pullback.fst y (specMap K K)) (πβ₁ ⁻¹ᵁ (𝒲.pullback c K).U0 ⊓ πβ₁ ⁻¹ᵁ (𝒲.pullback c K).U1) (hI hRβ0 hRβ1) (fβ.map01 f)
  let H00 : Y.functionField := CorrH1Kit.Gm (pullback.fst y (specMap K K)) (πα₁ ⁻¹ᵁ (𝒲.pullback c K).U0 ⊓ πα₁ ⁻¹ᵁ (𝒲'.pullback c K).U0) (hI hRα0 hRα'0) h00
  let H01 : Y.functionField := CorrH1Kit.Gm (pullback.fst y (specMap K K)) (πα₁ ⁻¹ᵁ (𝒲.pullback c K).U0 ⊓ πα₁ ⁻¹ᵁ (𝒲'.pullback c K).U1) (hI hRα0 hRα'1) h01
  let H10 : Y.functionField := CorrH1Kit.Gm (pullback.fst y (specMap K K)) (πα₁ ⁻¹ᵁ (𝒲.pullback c K).U1 ⊓ πα₁ ⁻¹ᵁ (𝒲'.pullback c K).U0) (hI hRα1 hRα'0) h10
  let H11 : Y.functionField := CorrH1Kit.Gm (pullback.fst y (specMap K K)) (πα₁ ⁻¹ᵁ (𝒲.pullback c K).U1 ⊓ πα₁ ⁻¹ᵁ (𝒲'.pullback c K).U1) (hI hRα1 hRα'1) h11
  let K00 : Y.functionField := CorrH1Kit.Gm (pullback.fst y (specMap K K)) (πα₁ ⁻¹ᵁ (𝒲.pullback c K).U0 ⊓ πβ₁ ⁻¹ᵁ (𝒲.pullback c K).U0) (hI hRα0 hRβ0) k00
  let K01 : Y.functionField := CorrH1Kit.Gm (pullback.fst y (specMap K K)) (πα₁ ⁻¹ᵁ (𝒲.pullback c K).U0 ⊓ πβ₁ ⁻¹ᵁ (𝒲.pullback c K).U1) (hI hRα0 hRβ1) k01
  let K10 : Y.functionField := CorrH1Kit.Gm (pullback.fst y (specMap K K)) (πα₁ ⁻¹ᵁ (𝒲.pullback c K).U1 ⊓ πβ₁ ⁻¹ᵁ (𝒲.pullback c K).U0) (hI hRα1 hRβ0) k10
  let K11 : Y.functionField := CorrH1Kit.Gm (pullback.fst y (specMap K K)) (πα₁ ⁻¹ᵁ (𝒲.pullback c K).U1 ⊓ πβ₁ ⁻¹ᵁ (𝒲.pullback c K).U1) (hI hRα1 hRβ1) k11

  have rH1 : H00 = H10 + G'' :=
    CorrH1Kit.Gm_rel_right (pullback.fst y (specMap K K)) (((NormDefTriv.preimageCover πα 𝒲).pullback y K).U0) (((NormDefTriv.preimageCover πα 𝒲).pullback y K).U1) (((NormDefTriv.preimageCover πα 𝒲').pullback y K).U0) (πα₁ ⁻¹ᵁ (𝒲.pullback c K).U0) (πα₁ ⁻¹ᵁ (𝒲.pullback c K).U1) (πα₁ ⁻¹ᵁ (𝒲'.pullback c K).U0)
      hRα0 hRα1 hRα'0 h00 h10 g'' hh1
  have rH2 : H01 = H11 + G'' :=
    CorrH1Kit.Gm_rel_right (pullback.fst y (specMap K K)) (((NormDefTriv.preimageCover πα 𝒲).pullback y K).U0) (((NormDefTriv.preimageCover πα 𝒲).pullback y K).U1) (((NormDefTriv.preimageCover πα 𝒲').pullback y K).U1) (πα₁ ⁻¹ᵁ (𝒲.pullback c K).U0) (πα₁ ⁻¹ᵁ (𝒲.pullback c K).U1) (πα₁ ⁻¹ᵁ (𝒲'.pullback c K).U1)
      hRα0 hRα1 hRα'1 h01 h11 g'' hh2
  have rH3 : H01 = H00 + Gg :=
    CorrH1Kit.Gm_rel_left (pullback.fst y (specMap K K)) (((NormDefTriv.preimageCover πα 𝒲).pullback y K).U0) (((NormDefTriv.preimageCover πα 𝒲').pullback y K).U0) (((NormDefTriv.preimageCover πα 𝒲').pullback y K).U1) (πα₁ ⁻¹ᵁ (𝒲.pullback c K).U0) (πα₁ ⁻¹ᵁ (𝒲'.pullback c K).U0) (πα₁ ⁻¹ᵁ (𝒲'.pullback c K).U1)
      hRα0 hRα'0 hRα'1 h01 h00 g hh3
  have rK1 : K00 = K10 + G'' :=
    CorrH1Kit.Gm_rel_right (pullback.fst y (specMap K K)) (((NormDefTriv.preimageCover πα 𝒲).pullback y K).U0) (((NormDefTriv.preimageCover πα 𝒲).pullback y K).U1) (((NormDefTriv.preimageCover πβ 𝒲).pullback y K).U0) (πα₁ ⁻¹ᵁ (𝒲.pullback c K).U0) (πα₁ ⁻¹ᵁ (𝒲.pullback c K).U1) (πβ₁ ⁻¹ᵁ (𝒲.pullback c K).U0)
      hRα0 hRα1 hRβ0 k00 k10 g'' hk1
  have rK2 : K01 = K11 + G'' :=
    CorrH1Kit.Gm_rel_right (pullback.fst y (specMap K K)) (((NormDefTriv.preimageCover πα 𝒲).pullback y K).U0) (((NormDefTriv.preimageCover πα 𝒲).pullback y K).U1) (((NormDefTriv.preimageCover πβ 𝒲).pullback y K).U1) (πα₁ ⁻¹ᵁ (𝒲.pullback c K).U0) (πα₁ ⁻¹ᵁ (𝒲.pullback c K).U1) (πβ₁ ⁻¹ᵁ (𝒲.pullback c K).U1)
      hRα0 hRα1 hRβ1 k01 k11 g'' hk2
  have rK3 : K01 = K00 + Gt :=
    CorrH1Kit.Gm_rel_left (pullback.fst y (specMap K K)) (((NormDefTriv.preimageCover πα 𝒲).pullback y K).U0) (((NormDefTriv.preimageCover πβ 𝒲).pullback y K).U0) (((NormDefTriv.preimageCover πβ 𝒲).pullback y K).U1) (πα₁ ⁻¹ᵁ (𝒲.pullback c K).U0) (πβ₁ ⁻¹ᵁ (𝒲.pullback c K).U0) (πβ₁ ⁻¹ᵁ (𝒲.pullback c K).U1)
      hRα0 hRβ0 hRβ1 k01 k00 (fβ.map01 f) hk3

  have mG'' : G'' ∈ AlgebraicCurve.lSpaceOn
      ((AlgebraicCurve.Place.restrictAlong φα hφα) ⁻¹' AlgebraicCurve.placesOf (pullback.snd c (specMap K K)) (𝒲.pullback c K).U0 ∩
        (AlgebraicCurve.Place.restrictAlong φα hφα) ⁻¹' AlgebraicCurve.placesOf (pullback.snd c (specMap K K)) (𝒲.pullback c K).U1)
      (0 : AlgebraicCurve.Divisor K Y.functionField) := by
    rw [← hPα, ← hPα]; exact CorrH1Kit.Gm_mem (pullback.fst y (specMap K K)) y _ _ _ g''
  have mH : ∀ (i j : (Limits.pullback c (specMap K K)).Opens) [Nonempty (πα₁ ⁻¹ᵁ i ⊓ πα₁ ⁻¹ᵁ j : Y.Opens)] {V₁ : (Limits.pullback y (specMap K K)).Opens}
      (hV₁ : pullback.fst y (specMap K K) ⁻¹ᵁ (πα₁ ⁻¹ᵁ i ⊓ πα₁ ⁻¹ᵁ j) ≤ V₁) (z : Γ(Limits.pullback y (specMap K K), V₁)),
      AlgebraicCurve.traceFunAlong φα (CorrH1Kit.Gm (pullback.fst y (specMap K K)) (πα₁ ⁻¹ᵁ i ⊓ πα₁ ⁻¹ᵁ j) hV₁ z) ∈
        AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf (pullback.snd c (specMap K K)) i ∩ AlgebraicCurve.placesOf (pullback.snd c (specMap K K)) j)
          (0 : AlgebraicCurve.Divisor K (Limits.pullback c (specMap K K)).functionField) := by
    intro i j _ V₁ hV₁ z
    refine AlgebraicCurve.traceFunAlong_mem_lSpaceOn htrα ?_
    rw [Set.preimage_inter, ← hPα, ← hPα]
    exact CorrH1Kit.Gm_mem (pullback.fst y (specMap K K)) y _ _ _ z
  have mK : ∀ (i j : (Limits.pullback c (specMap K K)).Opens) [Nonempty (πα₁ ⁻¹ᵁ i ⊓ πβ₁ ⁻¹ᵁ j : Y.Opens)] {V₁ : (Limits.pullback y (specMap K K)).Opens}
      (hV₁ : pullback.fst y (specMap K K) ⁻¹ᵁ (πα₁ ⁻¹ᵁ i ⊓ πβ₁ ⁻¹ᵁ j) ≤ V₁) (z : Γ(Limits.pullback y (specMap K K), V₁)),
      CorrH1Kit.Gm (pullback.fst y (specMap K K)) (πα₁ ⁻¹ᵁ i ⊓ πβ₁ ⁻¹ᵁ j) hV₁ z ∈
        AlgebraicCurve.lSpaceOn ((AlgebraicCurve.Place.restrictAlong φα hφα) ⁻¹' AlgebraicCurve.placesOf (pullback.snd c (specMap K K)) i ∩
          (AlgebraicCurve.Place.restrictAlong φβ hφβ) ⁻¹' AlgebraicCurve.placesOf (pullback.snd c (specMap K K)) j)
          (0 : AlgebraicCurve.Divisor K Y.functionField) := by
    intro i j _ V₁ hV₁ z
    rw [← hPα, ← hPβ]
    exact CorrH1Kit.Gm_mem (pullback.fst y (specMap K K)) y _ _ _ z

  have hGt : Gt = φβ (((Limits.pullback c (specMap K K)).germToFunctionField ((𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1)).hom f) := by
    have h1 : Gt = CorrH1Kit.Gm (pullback.fst y (specMap K K)) (πβ₁ ⁻¹ᵁ ((𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1))
        (by rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf, hRβ0, hRβ1]) (fβ.map01 f) :=
      CorrH1Kit.Gm_res' (pullback.fst y (specMap K K)) (by rw [Scheme.Hom.preimage_inf]) _ _ _
    rw [h1, HomOver.map01_apply,
      CorrH1Kit.Gm_appLE (pullback.fst y (specMap K K)) πβ₁ fβ.hom hfacβ.symm ((𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1) _ fβ.inf_le _ f]
    exact AlgebraicCurve.germToFunctionField_app_eq_of_fromSpecStalk_comp_eq πβ₁ φβ.toRingHom hφπβ _ f

  obtain ⟨⟨u₀, u₁⟩, hu⟩ := LinearMap.mem_range.mp ((Submodule.Quotient.eq _).mp hfs)
  have hu' : ((Limits.pullback c (specMap K K)).presheaf.map (homOfLE (inf_le_right : (𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1 ≤ (𝒲.pullback c K).U1)).op).hom u₁ -
      ((Limits.pullback c (specMap K K)).presheaf.map (homOfLE (inf_le_left : (𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1 ≤ (𝒲.pullback c K).U0)).op).hom u₀ = f - s := by
    have := hu
    rw [TwoChartCech.Sections.cechDiff_apply, TwoChartCech.Cover.lineBundle_r1_apply,
      TwoChartCech.Cover.lineBundle_r0_apply, Units.val_one, one_mul] at this
    exact this
  have hgfs : φβ (((Limits.pullback c (specMap K K)).germToFunctionField ((𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1)).hom f) =
      φβ (((Limits.pullback c (specMap K K)).germToFunctionField ((𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1)).hom s) +
        φβ (((Limits.pullback c (specMap K K)).germToFunctionField (𝒲.pullback c K).U1).hom u₁) - φβ (((Limits.pullback c (specMap K K)).germToFunctionField (𝒲.pullback c K).U0).hom u₀) := by
    have hf' : (show Γ(Limits.pullback c (specMap K K), (𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1) from f) = (show Γ(Limits.pullback c (specMap K K), (𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1) from s) + (((Limits.pullback c (specMap K K)).presheaf.map (homOfLE (inf_le_right : (𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1 ≤ (𝒲.pullback c K).U1)).op).hom u₁ -
        ((Limits.pullback c (specMap K K)).presheaf.map (homOfLE (inf_le_left : (𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1 ≤ (𝒲.pullback c K).U0)).op).hom u₀) := by
      rw [hu']; abel
    rw [← CorrH1Kit.germ_map (inf_le_right : (𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1 ≤ (𝒲.pullback c K).U1) u₁,
      ← CorrH1Kit.germ_map (inf_le_left : (𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1 ≤ (𝒲.pullback c K).U0) u₀, hf']
    simp only [map_add, map_sub]
    abel

  have mu : ∀ (i j : (Limits.pullback c (specMap K K)).Opens) [Nonempty (j : (Limits.pullback c (specMap K K)).Opens)] (u : Γ(Limits.pullback c (specMap K K), j)),
      φβ (((Limits.pullback c (specMap K K)).germToFunctionField j).hom u) ∈
        AlgebraicCurve.lSpaceOn ((AlgebraicCurve.Place.restrictAlong φα hφα) ⁻¹' AlgebraicCurve.placesOf (pullback.snd c (specMap K K)) i ∩
          (AlgebraicCurve.Place.restrictAlong φβ hφβ) ⁻¹' AlgebraicCurve.placesOf (pullback.snd c (specMap K K)) j)
          (0 : AlgebraicCurve.Divisor K Y.functionField) := fun i j _ u =>
    AlgebraicCurve.lSpaceOn_anti Set.inter_subset_right _
      (AlgebraicCurve.map_mem_lSpaceOn_preimage φβ hφβ (AlgebraicCurve.germToFunctionField_mem_lSpaceOn_placesOf (pullback.snd c (specMap K K)) j u))
  have clause2 := AlgebraicCurve.cechH1ToH1_mk_eq_cechH1ToH1_mk_of_crossSections
    (AlgebraicCurve.preimage_restrictAlong_union_eq_univ φα hφα hW) (AlgebraicCurve.preimage_restrictAlong_union_eq_univ φβ hφβ hW)
    ⟨G'', mG''⟩
    (AlgebraicCurve.lSpaceOnZero.pullbackAlong φβ hφβ _ _ ⟨((Limits.pullback c (specMap K K)).germToFunctionField ((𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1)).hom s, hsr⟩)
    (K00 - φβ (((Limits.pullback c (specMap K K)).germToFunctionField (𝒲.pullback c K).U0).hom u₀)) (K01 - φβ (((Limits.pullback c (specMap K K)).germToFunctionField (𝒲.pullback c K).U1).hom u₁))
    (K10 - φβ (((Limits.pullback c (specMap K K)).germToFunctionField (𝒲.pullback c K).U0).hom u₀)) (K11 - φβ (((Limits.pullback c (specMap K K)).germToFunctionField (𝒲.pullback c K).U1).hom u₁))
    (sub_mem (mK _ _ _ k00) (mu _ _ u₀)) (sub_mem (mK _ _ _ k01) (mu _ _ u₁))
    (sub_mem (mK _ _ _ k10) (mu _ _ u₀)) (sub_mem (mK _ _ _ k11) (mu _ _ u₁))
    (by rw [rK1]; change _ = _ + G''; abel) (by rw [rK2]; change _ = _ + G''; abel)
    (by
      rw [rK3, hGt, hgfs, AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply]
      abel)

  haveI hfreeΓ : Module.Free Γ(Limits.pullback c (specMap K K), (𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1) Γ(Limits.pullback y (specMap K K), (𝒲α'.pullback y K).U0 ⊓ (𝒲α'.pullback y K).U1) := hfree
  haveI hfinΓ : Module.Finite Γ(Limits.pullback c (specMap K K), (𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1) Γ(Limits.pullback y (specMap K K), (𝒲α'.pullback y K).U0 ⊓ (𝒲α'.pullback y K).U1) := hfin
  haveI : Nonempty (πα₁ ⁻¹ᵁ ((𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1) : Y.Opens) :=
    CorrH1Kit.nonempty_preimage_of_fromSpecStalk_comp_eq πα₁ φα.toRingHom hφπα _
  have hTr : ((Limits.pullback c (specMap K K)).germToFunctionField ((𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1)).hom
      (Algebra.trace ((𝒲'.pullback c K).cover (pullback.snd c (specMap K K))).A01 ((𝒲α'.pullback y K).cover (pullback.snd y (specMap K K))).A01 g) =
      AlgebraicCurve.traceFunAlong φα Gg := by
    have h1 : Gg = CorrH1Kit.Gm (pullback.fst y (specMap K K)) (πα₁ ⁻¹ᵁ ((𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1))
        (by rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf, hRα'0, hRα'1]) g :=
      CorrH1Kit.Gm_res' (pullback.fst y (specMap K K)) (by rw [Scheme.Hom.preimage_inf]) _ _ _
    rw [h1]
    exact CorrH1Kit.germ_trace_eq_traceFunAlong_Gm (pullback.snd c (specMap K K)) y (pullback.fst y (specMap K K)) πα₁ hα₁' fα.hom hfacα.symm
      ((𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1) (𝒲'.pullback c K).isAffineOpen_inf _ hV _ φα hφπα g
  have hsr'g : ((Limits.pullback c (specMap K K)).germToFunctionField ((𝒲'.pullback c K).U0 ⊓ (𝒲'.pullback c K).U1)).hom
      (Algebra.trace ((𝒲'.pullback c K).cover (pullback.snd c (specMap K K))).A01 ((𝒲α'.pullback y K).cover (pullback.snd y (specMap K K))).A01 g) ∈
      AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf (pullback.snd c (specMap K K)) (𝒲'.pullback c K).U0 ∩ AlgebraicCurve.placesOf (pullback.snd c (specMap K K)) (𝒲'.pullback c K).U1)
        (0 : AlgebraicCurve.Divisor K (Limits.pullback c (specMap K K)).functionField) :=
    AlgebraicCurve.germToFunctionField_inf_mem_lSpaceOn_inter_placesOf (pullback.snd c (specMap K K)) _ _ _
  have hsrr : ((Limits.pullback c (specMap K K)).germToFunctionField ((𝒲.pullback c K).U0 ⊓ (𝒲.pullback c K).U1)).hom sr ∈
      AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf (pullback.snd c (specMap K K)) (𝒲.pullback c K).U0 ∩ AlgebraicCurve.placesOf (pullback.snd c (specMap K K)) (𝒲.pullback c K).U1)
        (0 : AlgebraicCurve.Divisor K (Limits.pullback c (specMap K K)).functionField) :=
    AlgebraicCurve.germToFunctionField_inf_mem_lSpaceOn_inter_placesOf (pullback.snd c (specMap K K)) _ _ _
  have clause3 := AlgebraicCurve.cechH1ToH1_mk_eq_cechH1ToH1_mk_of_crossSections hW hW'
    (AlgebraicCurve.lSpaceOnZero.traceAlong φα hφα htrα _ _ ⟨G'', mG''⟩)
    ⟨_, hsr'g⟩
    (AlgebraicCurve.traceFunAlong φα H00) (AlgebraicCurve.traceFunAlong φα H01)
    (AlgebraicCurve.traceFunAlong φα H10) (AlgebraicCurve.traceFunAlong φα H11)
    (mH _ _ _ h00) (mH _ _ _ h01) (mH _ _ _ h10) (mH _ _ _ h11)
    (by rw [rH1, map_add]; rfl) (by rw [rH2, map_add]; rfl) (by rw [rH3, map_add, ← hTr])

  refine ⟨sr, hsrr, Submodule.Quotient.mk ⟨G'', mG''⟩, hsr0.symm, ?_, ?_⟩
  · rw [AlgebraicCurve.cechH1.pullbackAlong_mk]; exact clause2
  · rw [AlgebraicCurve.cechH1.traceAlong_mk, hind hsrr hsr'g]; exact clause3.symm

end S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_field
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_field (solution)
