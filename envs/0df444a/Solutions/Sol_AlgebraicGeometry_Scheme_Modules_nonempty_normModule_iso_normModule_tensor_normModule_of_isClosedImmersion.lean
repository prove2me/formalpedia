-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.nonempty_normModule_iso_normModule_tensor_normModule_of_isClosedImmersion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1d3ac73a-bbff-5ad3-891b-2b0fe5c3894c

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_isFrameOn_of_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_normModule_frameKit_of_isClosedImmersion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_iso_normModule_tensor_normModule_of_isClosedImmersion
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal"
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal'"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite"

theorem solution
    {X Z Z₀ Z₁ : Scheme.{u}} [IsIntegral X] (π : Z ⟶ X) (ι₀ : Z₀ ⟶ Z) (ι₁ : Z₁ ⟶ Z)
    [IsClosedImmersion ι₀] [IsClosedImmersion ι₁]
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    [IsFinite (ι₀ ≫ π)] [Flat (ι₀ ≫ π)] [LocallyOfFinitePresentation (ι₀ ≫ π)]
    [IsFinite (ι₁ ≫ π)] [Flat (ι₁ ≫ π)] [LocallyOfFinitePresentation (ι₁ ≫ π)]
    (d d₀ d₁ : ℕ) (hd : ∀ x : X, π.finrank x = d) (hd₀ : ∀ x : X, (ι₀ ≫ π).finrank x = d₀)
    (hd₁ : ∀ x : X, (ι₁ ≫ π).finrank x = d₁) (hsum : d = d₀ + d₁)
    (hcov : ∀ (U : Z.Opens) (s : Γ(Z, U)), (ι₀.app U).hom s = 0 → (ι₁.app U).hom s = 0 → s = 0)
    {L : Z.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (Scheme.Modules.normModule π d L ≅
      Scheme.Modules.normModule (ι₀ ≫ π) d₀ ((Scheme.Modules.pullback ι₀).obj L) ⊗
        Scheme.Modules.normModule (ι₁ ≫ π) d₁ ((Scheme.Modules.pullback ι₁).obj L)) := by
  obtain ⟨S, hframe, hcov', hres, hunit⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_normModule_frameKit_of_isClosedImmersion π ι₀ ι₁ d d₀ d₁ hd hd₀ hd₁ hsum hcov hL
  obtain ⟨e, -⟩ := AlgebraicGeometry.Scheme.Modules.exists_iso_app_eq_of_isFrameOn_of_eq_smul S hframe hcov' hres hunit
  exact ⟨e⟩

end S_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_iso_normModule_tensor_normModule_of_isClosedImmersion
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_iso_normModule_tensor_normModule_of_isClosedImmersion (solution)
