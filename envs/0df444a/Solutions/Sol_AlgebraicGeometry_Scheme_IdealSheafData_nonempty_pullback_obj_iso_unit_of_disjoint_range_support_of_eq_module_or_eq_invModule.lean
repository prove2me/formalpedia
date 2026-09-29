-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.nonempty_pullback_obj_iso_unit_of_disjoint_range_support_of_eq_module_or_eq_invModule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/bde96a7b-841e-5062-91c9-bbc1253b4f7d

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_eq_top_and_nonempty_module_iso_and_nonempty_invModule_iso_of_disjoint_range_support
import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_nonempty_pullback_obj_iso_unit_of_disjoint_range_support_of_eq_module_or_eq_invModule
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

universe u

theorem solution
    {X Y : Scheme.{u}} (I : Y.IdealSheafData) (hI : I.IsInvertible) (f : X ⟶ Y)
    (h : Disjoint (Set.range f.base) (I.support : Set ↥Y)) (B : Y.Modules) (hB : B = I.module ∨ B = I.invModule) :
    Nonempty ((Scheme.Modules.pullback f).obj B ≅ 𝟙_ X.Modules) := by
  obtain ⟨htop, ⟨em⟩, ⟨ei⟩⟩ :=
    AlgebraicGeometry.Scheme.IdealSheafData.comap_eq_top_and_nonempty_module_iso_and_nonempty_invModule_iso_of_disjoint_range_support I f h
  have hI' : (I.comap f).IsInvertible := by rw [htop]; exact Scheme.IdealSheafData.isInvertible_top
  rcases hB with rfl | rfl
  · haveI := AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison f hI hI'
    exact ⟨asIso (I.pullbackModuleComparison f) ≪≫ em⟩
  · obtain ⟨e⟩ := AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso f hI hI'
    exact ⟨e ≪≫ ei⟩

end S_AlgebraicGeometry_Scheme_IdealSheafData_nonempty_pullback_obj_iso_unit_of_disjoint_range_support_of_eq_module_or_eq_invModule
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_nonempty_pullback_obj_iso_unit_of_disjoint_range_support_of_eq_module_or_eq_invModule (solution)
