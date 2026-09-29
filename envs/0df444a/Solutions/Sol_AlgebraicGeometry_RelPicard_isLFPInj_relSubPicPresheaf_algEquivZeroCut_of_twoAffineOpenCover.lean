-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.isLFPInj_relSubPicPresheaf_algEquivZeroCut_of_twoAffineOpenCover
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/45a8c570-fa94-59a5-99a8-58a9a6fc207c

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_AffineLimit
import Theorems.Thm_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relSubPicPresheaf_algEquivZeroCut_of_twoAffineOpenCover
p2m_attr_erase "instance" "AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "simp" "AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relSubPicPresheaf_algEquivZeroCut_of_twoAffineOpenCover.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relSubPicPresheaf_algEquivZeroCut_of_twoAffineOpenCover.AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.AffineLimit"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec Scheme Flat geometrically AffineLimit.specOverOfSubalgebra AffineLimit.IsLFPInj" namespace RelPicard p2m_export "AlgebraicGeometry.RelPicard" "relPicardPresheaf SubPicCondition algEquivZeroCut relSubPicPresheaf relSubPicPresheaf_map_coe isLFPInj_relPicardPresheaf" end AlgebraicGeometry.RelPicard
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.RelPicard" in

theorem AlgebraicGeometry.RelPicard.isLFPInj_relSubPicPresheaf_of_relPicardPresheaf'
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (P : SubPicCondition c ε)
    (h : AffineLimit.IsLFPInj (relPicardPresheaf c ε)) :
    AffineLimit.IsLFPInj (relSubPicPresheaf c ε P) := by
  intro A _ _ A₀ hA₀ x₀ x₀' hx
  have hx' : (relPicardPresheaf c ε).map (AffineLimit.specOverOfSubalgebra R A₀).op x₀.1 =
      (relPicardPresheaf c ε).map (AffineLimit.specOverOfSubalgebra R A₀).op x₀'.1 := by
    have := congrArg Subtype.val hx
    simp only [relSubPicPresheaf_map_coe] at this
    exact this
  obtain ⟨A₁, hA₁, hle, h1⟩ := h A A₀ hA₀ x₀.1 x₀'.1 hx'
  refine ⟨A₁, hA₁, hle, Subtype.ext ?_⟩
  simp only [relSubPicPresheaf_map_coe] at h1
  exact h1

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (𝒱 : C.TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    IsLFPInj (relSubPicPresheaf c ε (algEquivZeroCut c ε)) := by
  exact isLFPInj_relSubPicPresheaf_of_relPicardPresheaf' c ε _ (isLFPInj_relPicardPresheaf R 𝒱 c ε)

end S_AlgebraicGeometry_RelPicard_isLFPInj_relSubPicPresheaf_algEquivZeroCut_of_twoAffineOpenCover
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relSubPicPresheaf_algEquivZeroCut_of_twoAffineOpenCover (solution)
