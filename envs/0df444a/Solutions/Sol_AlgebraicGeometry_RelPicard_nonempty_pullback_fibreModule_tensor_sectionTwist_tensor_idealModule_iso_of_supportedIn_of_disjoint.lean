-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.nonempty_pullback_fibreModule_tensor_sectionTwist_tensor_idealModule_iso_of_supportedIn_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/d7f901dc-d0b2-587b-90f4-fd3023b2e979

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isFrameOn_app_of_disjoint_support_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_iso_tensorUnit_of_map_eq_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection
import Theorems.Thm_AlgebraicGeometry_RelPicard_isInvertible_sectionIdeal_of_range_subset
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_ev_app_tensorUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_nonempty_pullback_fibreModule_tensor_sectionTwist_tensor_idealModule_iso_of_supportedIn_of_disjoint
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve NeronModelInfra"

namespace Book1

p2m_open "AlgebraicGeometry.Scheme.Modules"

theorem nonempty_pullback_iso_unit_of_forall_notMem {X Y : Scheme.{u}} (φ : Y ⟶ X)
    {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M)
    (hφ : ∀ y : Y, φ.base y ∉ ((Scheme.Modules.zeroSchemeIdeal s).support : Set X)) :
    Nonempty ((Scheme.Modules.pullback φ).obj M ≅ 𝟙_ Y.Modules) := by

  let V : X.Opens := (Scheme.Modules.zeroSchemeIdeal s).support.compl
  have hdisj : Disjoint (V : Set X) (Scheme.Modules.zeroSchemeIdeal s).support :=
    Set.disjoint_left.mpr fun x hx hx' => hx hx'
  have hfr := hM.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal s V hdisj

  have hfr' := hfr.pullbackLocalSection φ
  have hV : φ ⁻¹ᵁ V = ⊤ := by
    ext y
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, TopologicalSpace.Opens.coe_top,
      Set.mem_univ, iff_true]
    exact hφ y
  rw [hV] at hfr'

  set σ := Scheme.Modules.pullbackLocalSection φ (s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) with hσ
  refine Scheme.Modules.IsFrameOn.nonempty_iso_tensorUnit_of_map_eq_mul (U := ⊤) (V := ⊤)
    (by simp) hfr' hfr' 1 (by rw [one_smul]) 1 1 isUnit_one isUnit_one (by rw [one_mul])

end Book1

open Book1 in
theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]

    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hεU : Set.range ε.1 ⊆ (U : Set C))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {r e : ℕ} (D : RelEffCartierDiv c e t) (hDU : D.SupportedIn U)
    {k : Type u} [Field k] (pt : Spec (CommRingCat.of k) ⟶ T)
    {Y : Scheme.{u}} (i₂ : Y ⟶ pullback (pullback.snd c t) pt)

    (hD : ∀ y : Y, (pullback.fst (pullback.snd c t) pt).base (i₂.base y) ∉ D.I.support)
    (hε : ∀ y : Y, (pullback.fst (pullback.snd c t) pt).base (i₂.base y) ∉ Set.range (rigSection c t ε).base)
    (LL : (pullback c t).Modules) (hLL : Scheme.Modules.IsInvertible LL)
    (hLL₂ : Nonempty ((Scheme.Modules.pullback i₂).obj (fibreModule c t pt LL) ≅
      (Scheme.Modules.pullback i₂).obj (SheafOfModules.unit (pullback (pullback.snd c t) pt).ringCatSheaf))) :
    Nonempty ((Scheme.Modules.pullback i₂).obj (fibreModule c t pt (LL ⊗ (sectionTwist c ε t r ⊗ D.idealModule))) ≅
      (Scheme.Modules.pullback i₂).obj (SheafOfModules.unit (pullback (pullback.snd c t) pt).ringCatSheaf))  := by

  let pr := pullback.fst (pullback.snd c t) pt
  let φ : Y ⟶ pullback c t := i₂ ≫ pr
  have hφb : ∀ y : Y, φ.base y = pr.base (i₂.base y) := fun y => rfl
  let J := sectionIdeal c ε t
  have hJ : J = sectionIdeal c ε t := rfl

  have hJinv : J.IsInvertible := isInvertible_sectionIdeal_of_range_subset c ε U hεU t
  have hJr : (J ^ r).IsInvertible := hJinv.pow r
  have hI : D.I.IsInvertible := D.isInvertible_I_of_supportedIn U hDU

  have hεclosed : IsClosedImmersion (rigSection c t ε) := by
    have h1 : rigSection c t ε ≫ pullback.snd c t = 𝟙 T := pullback.lift_snd _ _ _
    haveI : IsClosedImmersion (rigSection c t ε ≫ pullback.snd c t) := by rw [h1]; infer_instance
    exact IsClosedImmersion.of_comp (rigSection c t ε) (pullback.snd c t)
  have hsuppJ : (J.support : Set ↥(pullback c t)) = Set.range (rigSection c t ε).base := by
    show ((rigSection c t ε).ker.support : Set ↥(pullback c t)) = _
    rw [Scheme.Hom.support_ker, (hεclosed.base_closed.isClosedMap.isClosed_range).closure_eq]
  have hsuppJr : ((J ^ r).support : Set ↥(pullback c t)) ⊆ Set.range (rigSection c t ε).base := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      rw [pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top]
      intro x hx
      exact absurd hx (by simp)
    · rw [Scheme.IdealSheafData.support_pow _ _ hr.ne', hsuppJ]
  obtain ⟨eS⟩ : Nonempty ((Scheme.Modules.pullback φ).obj (sectionTwist c ε t r) ≅ 𝟙_ Y.Modules) := by
    have hz := Scheme.IdealSheafData.IsInvertible.zeroSchemeIdeal_invModuleSection hJr
    refine nonempty_pullback_iso_unit_of_forall_notMem φ hJr.isInvertible_invModule (J ^ r).invModuleSection ?_
    intro y hy
    have hy' : φ.base y ∈ ((J ^ r).support : Set ↥(pullback c t)) := by
      have hs : ((Scheme.Modules.zeroSchemeIdeal (J ^ r).invModuleSection).support : Set ↥(pullback c t))
          = (J ^ r).support := by rw [hz]
      rw [← hs]; exact hy
    exact hε y (hφb y ▸ hsuppJr hy')

  obtain ⟨eD'⟩ : Nonempty ((Scheme.Modules.pullback φ).obj D.I.invModule ≅ 𝟙_ Y.Modules) := by
    have hz := Scheme.IdealSheafData.IsInvertible.zeroSchemeIdeal_invModuleSection hI
    refine nonempty_pullback_iso_unit_of_forall_notMem φ hI.isInvertible_invModule D.I.invModuleSection ?_
    intro y hy
    have hy' : φ.base y ∈ (D.I.support : Set ↥(pullback c t)) := by
      have hs : ((Scheme.Modules.zeroSchemeIdeal D.I.invModuleSection).support : Set ↥(pullback c t))
          = D.I.support := by rw [hz]
      rw [← hs]; exact hy
    exact hD y (hφb y ▸ hy')
  have hN : Scheme.Modules.IsInvertible D.idealModule := hI.isInvertible_module

  have eEv : D.idealModule ⊗ D.I.invModule ≅ 𝟙_ (pullback c t).Modules :=
    @asIso _ _ _ _ ((ihom.ev D.idealModule).app (𝟙_ (pullback c t).Modules)) hN.isIso_ev_app_tensorUnit
  have eN : (Scheme.Modules.pullback φ).obj D.idealModule ≅ 𝟙_ Y.Modules :=
    (ρ_ _).symm ≪≫ (whiskerLeftIso _ eD'.symm) ≪≫ (Scheme.Modules.pullbackTensorObjIso φ _ _).symm ≪≫
      (Scheme.Modules.pullback φ).mapIso eEv ≪≫ Scheme.Modules.pullbackTensorUnitObjIso φ

  obtain ⟨eL2⟩ := hLL₂
  have eL : (Scheme.Modules.pullback φ).obj LL ≅ 𝟙_ Y.Modules :=
    ((Scheme.Modules.pullbackComp i₂ pr).app LL).symm ≪≫ eL2 ≪≫ Scheme.Modules.pullbackTensorUnitObjIso i₂

  have eF : (Scheme.Modules.pullback φ).obj (LL ⊗ (sectionTwist c ε t r ⊗ D.idealModule)) ≅ 𝟙_ Y.Modules :=
    Scheme.Modules.pullbackTensorObjIso φ _ _ ≪≫ (eL ⊗ᵢ (Scheme.Modules.pullbackTensorObjIso φ _ _ ≪≫ (eS ⊗ᵢ eN) ≪≫ λ_ _)) ≪≫ λ_ _
  exact ⟨(Scheme.Modules.pullbackComp i₂ pr).app _ ≪≫ eF ≪≫ (Scheme.Modules.pullbackTensorUnitObjIso i₂).symm⟩

end S_AlgebraicGeometry_RelPicard_nonempty_pullback_fibreModule_tensor_sectionTwist_tensor_idealModule_iso_of_supportedIn_of_disjoint
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_nonempty_pullback_fibreModule_tensor_sectionTwist_tensor_idealModule_iso_of_supportedIn_of_disjoint (solution)
