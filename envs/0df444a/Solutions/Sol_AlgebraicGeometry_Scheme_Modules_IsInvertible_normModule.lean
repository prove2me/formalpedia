-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.normModule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/c8da72a1-f7ba-502f-b411-b4bb3e5e89a2

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_det_of_isLocallyFreeOfRank
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_normModule
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

theorem solution {X Y : Scheme.{u}} (π : X ⟶ Y)
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π] (d : ℕ) (hd : ∀ y : Y, π.finrank y = d)
    {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Scheme.Modules.IsInvertible (Scheme.Modules.normModule π d L) := by

  have hU : Scheme.Modules.IsInvertible (𝟙_ X.Modules) :=
    Scheme.Modules.isInvertible_unit X
  have h1 : Scheme.Modules.IsLocallyFreeOfRank d ((Scheme.Modules.pushforward π).obj L) :=
    Scheme.Modules.isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver π d hd L
      (fun y => hL.exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite π y)
  have h2 : Scheme.Modules.IsLocallyFreeOfRank d ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)) :=
    Scheme.Modules.isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver π d hd _
      (fun y => hU.exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite π y)

  exact (Scheme.Modules.isInvertible_det_of_isLocallyFreeOfRank h1).tensor
    (Scheme.Modules.isInvertible_det_of_isLocallyFreeOfRank h2).dual.1

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_normModule
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_normModule (solution)
