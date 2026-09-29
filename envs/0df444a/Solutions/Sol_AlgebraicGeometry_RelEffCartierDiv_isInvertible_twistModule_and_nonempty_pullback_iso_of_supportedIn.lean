-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.isInvertible_twistModule_and_nonempty_pullback_iso_of_supportedIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/e02f81c7-9f52-5906-8408-ab39dca9d0b0

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_rigidify
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_RelPicard_isInvertible_sectionIdeal_of_range_subset
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isInvertible_twistModule_and_nonempty_pullback_iso_of_supportedIn
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst"

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra"

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (hεU : Set.range ε.1 ⊆ (U : Set C))
    {r : ℕ} {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (D : RelEffCartierDiv c r t) (hD : D.SupportedIn U) :
    Scheme.Modules.IsInvertible (D.twistModule c ε) ∧
      Nonempty ((Scheme.Modules.pullback (RelPicard.rigSection c t ε)).obj (D.twistModule c ε) ≅
        𝟙_ T.Modules) := by
  have hσq : RelPicard.rigSection c t ε ≫ pullback.snd c t = 𝟙 T := by
    simp only [RelPicard.rigSection, pullback.lift_snd]
  have hJ : (RelPicard.sectionIdeal c ε t).IsInvertible :=
    RelPicard.isInvertible_sectionIdeal_of_range_subset c ε U hεU t
  have h₁ : Scheme.Modules.IsInvertible D.lineBundle :=
    (RelEffCartierDiv.isInvertible_I_of_supportedIn U D hD).isInvertible_invModule
  have h₂ : Scheme.Modules.IsInvertible (((RelPicard.sectionIdeal c ε t) ^ r).module) :=
    (hJ.pow r).isInvertible_module
  rw [RelEffCartierDiv.twistModule_def]
  exact Scheme.Modules.IsInvertible.rigidify hσq (h₁.tensor h₂)

end S_AlgebraicGeometry_RelEffCartierDiv_isInvertible_twistModule_and_nonempty_pullback_iso_of_supportedIn
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isInvertible_twistModule_and_nonempty_pullback_iso_of_supportedIn (solution)
