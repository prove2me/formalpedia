-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.isInvertible_thetaBundle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/fa99e472-e334-537a-9b4e-8d47091ce585

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Theorems.Thm_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_of_forall_fibre
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_det_of_isLocallyFreeOfRank
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isInvertible_thetaBundle
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicGeometry.SmoothProperCurve"

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} [LocallyOfFiniteType t]
    (M : RigidifiedLineBundle c ε t) (r n : ℕ)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t r))).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t r))).H0 = n) :
    Scheme.Modules.IsInvertible (thetaBundle c ε t M r n) := by

  have hsec : rigSection c t ε ≫ pullback.snd c t = 𝟙 T := pullback.lift_snd _ _ _
  haveI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) c t inferInstance

  have hI : (sectionIdeal c ε t).IsInvertible :=
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (rigSection c t ε) hsec
  have hpow : ∀ k : ℕ, ((sectionIdeal c ε t) ^ k).IsInvertible := fun k => by
    induction k with
    | zero => rw [pow_zero, Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_top
    | succ k ih => rw [pow_succ]; exact ih.mul hI

  have hN : Scheme.Modules.IsInvertible (sectionTwist c ε t r) := (hpow r).isInvertible_invModule
  have hF : Scheme.Modules.IsInvertible (M.L ⊗ sectionTwist c ε t r) := M.isInvertible.tensor hN

  have hE : Scheme.Modules.IsLocallyFreeOfRank n (picardBundle c ε t M (sectionTwist c ε t r)) :=
    AlgebraicGeometry.RelPicard.isLocallyFreeOfRank_pushforward_of_forall_fibre R c ε h𝔉 t
      (M.L ⊗ sectionTwist c ε t r) hF n hfib

  exact (AlgebraicGeometry.Scheme.Modules.isInvertible_det_of_isLocallyFreeOfRank hE).dual.1

end S_AlgebraicGeometry_RelPicard_isInvertible_thetaBundle
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_isInvertible_thetaBundle (solution)
