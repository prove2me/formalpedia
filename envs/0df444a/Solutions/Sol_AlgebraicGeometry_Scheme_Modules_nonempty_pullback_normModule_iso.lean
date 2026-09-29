-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.nonempty_pullback_normModule_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/b57b83bc-1696-5c6b-ba94-cf0a6462e11b

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_SheafOfModules_Monoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_det_iso_det_pullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_isAffineHom
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_det_of_isLocallyFreeOfRank
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_normModule_iso
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_normModule_iso.AlgebraicGeometry CategoryTheory.MonoidalCategory"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.Modules.pushforward Scheme.Modules.pullback IsFinite Scheme Flat Scheme.Modules LocallyOfFinitePresentation IsAffineHom Scheme.Modules.normModule Scheme.Modules.dualCongr Scheme.Modules.exteriorPower Scheme.Modules.IsLocallyFreeOfRank Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit Scheme.Modules.baseChangeHom Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.Modules.nonempty_pullback_det_iso_det_pullback Scheme.Modules.IsInvertible.pullback_dual Scheme.Modules.isIso_baseChangeHom_of_isAffineHom Scheme.Modules.isInvertible_det_of_isLocallyFreeOfRank Scheme.Modules.isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver Scheme.Modules.IsInvertible.exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Modules.pushforward Modules.pullback Modules Modules.normModule Modules.dualCongr Modules.exteriorPower Modules.IsLocallyFreeOfRank Modules.IsInvertible Modules.isInvertible_unit Modules.baseChangeHom Modules.pullbackTensorObjIso Modules.pullbackTensorUnitObjIso Modules.nonempty_pullback_det_iso_det_pullback Modules.IsInvertible.pullback_dual Modules.isIso_baseChangeHom_of_isAffineHom Modules.isInvertible_det_of_isLocallyFreeOfRank Modules.isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver Modules.IsInvertible.exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "pushforward pullback normModule dualCongr exteriorPower det dual IsLocallyFreeOfRank IsInvertible isInvertible_unit baseChangeHom pullbackTensorObjIso pullbackTensorUnitObjIso nonempty_pullback_det_iso_det_pullback IsInvertible.pullback_dual isIso_baseChangeHom_of_isAffineHom isInvertible_det_of_isLocallyFreeOfRank isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver IsInvertible.exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite" end AlgebraicGeometry.Scheme.Modules
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules" in

theorem AlgebraicGeometry.Scheme.Modules.nonempty_pullback_normModule_iso_of_isAffineHom
    {X T X' T' : Scheme.{u}} {π : X ⟶ T} {ψ : T' ⟶ T} {π' : X' ⟶ T'} {g' : X' ⟶ X}
    (hcart : IsPullback g' π' π ψ) [IsAffineHom π] (d : ℕ) {L : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    (hE : Scheme.Modules.IsLocallyFreeOfRank d ((Scheme.Modules.pushforward π).obj L))
    (h𝒪 : Scheme.Modules.IsLocallyFreeOfRank d ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules))) :
    Nonempty ((Scheme.Modules.pullback ψ).obj (Scheme.Modules.normModule π d L) ≅
      Scheme.Modules.normModule π' d ((Scheme.Modules.pullback g').obj L)) := by

  haveI := Scheme.Modules.isIso_baseChangeHom_of_isAffineHom hcart L hL.exists_trivialization
  haveI := Scheme.Modules.isIso_baseChangeHom_of_isAffineHom hcart (𝟙_ X.Modules)
    (Scheme.Modules.isInvertible_unit X).exists_trivialization
  let bcL : (Scheme.Modules.pullback ψ).obj ((Scheme.Modules.pushforward π).obj L) ≅
      (Scheme.Modules.pushforward π').obj ((Scheme.Modules.pullback g').obj L) :=
    asIso (Scheme.Modules.baseChangeHom hcart.w L)
  let bc𝒪 : (Scheme.Modules.pullback ψ).obj ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)) ≅
      (Scheme.Modules.pushforward π').obj (𝟙_ X'.Modules) :=
    asIso (Scheme.Modules.baseChangeHom hcart.w (𝟙_ X.Modules)) ≪≫
      (Scheme.Modules.pushforward π').mapIso (Scheme.Modules.pullbackTensorUnitObjIso g')

  obtain ⟨eDetL⟩ := Scheme.Modules.nonempty_pullback_det_iso_det_pullback ψ d hE
  obtain ⟨eDet𝒪⟩ := Scheme.Modules.nonempty_pullback_det_iso_det_pullback ψ d h𝒪

  obtain ⟨eDual⟩ := Scheme.Modules.IsInvertible.pullback_dual ψ
    (Scheme.Modules.isInvertible_det_of_isLocallyFreeOfRank h𝒪)

  refine ⟨Scheme.Modules.pullbackTensorObjIso ψ _ _ ≪≫ (?_ ⊗ᵢ ?_)⟩
  · exact eDetL ≪≫ (Scheme.Modules.exteriorPower T' d).mapIso bcL
  · exact eDual ≪≫ Scheme.Modules.dualCongr (eDet𝒪 ≪≫ (Scheme.Modules.exteriorPower T' d).mapIso bc𝒪)

theorem solution
    {X Y X' Y' : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ y : Y, π.finrank y = d)
    (g : Y' ⟶ Y) (π' : X' ⟶ Y') (g' : X' ⟶ X) (sq : IsPullback g' π' π g)
    {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty ((Scheme.Modules.pullback g).obj (Scheme.Modules.normModule π d L) ≅
      Scheme.Modules.normModule π' d ((Scheme.Modules.pullback g').obj L)) :=
  Scheme.Modules.nonempty_pullback_normModule_iso_of_isAffineHom sq d hL
    (Scheme.Modules.isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver π d hd L
      (fun t => Scheme.Modules.IsInvertible.exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite π hL t))
    (Scheme.Modules.isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver π d hd (𝟙_ X.Modules)
      (fun t => Scheme.Modules.IsInvertible.exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite π
        (Scheme.Modules.isInvertible_unit X) t))

end S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_normModule_iso
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_normModule_iso (solution)
