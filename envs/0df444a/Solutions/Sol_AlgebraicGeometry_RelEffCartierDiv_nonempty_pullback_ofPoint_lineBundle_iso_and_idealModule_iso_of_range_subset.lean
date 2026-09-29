-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/5e082373-a219-53a4-97f2-7994b84fcf87

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_supportedIn_ofPoint
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard"

theorem OfPointBC.main
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (u : SchemeHomOver t c) (hu : Set.range u.1.base ⊆ (U : Set C)) (ψ : SchemeHomOver t' t)
    (hψu : (ψ.1 ≫ u.1) ≫ c = t') :
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (RelEffCartierDiv.ofPoint c u.1 u.2).lineBundle ≅
        (RelEffCartierDiv.ofPoint c (ψ.1 ≫ u.1) hψu).lineBundle) ∧
      Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (RelEffCartierDiv.ofPoint c u.1 u.2).idealModule ≅
        (RelEffCartierDiv.ofPoint c (ψ.1 ≫ u.1) hψu).idealModule) := by
  let Ψ := baseChangeSnd c ψ
  let D := RelEffCartierDiv.ofPoint c u.1 u.2
  have hDU : D.SupportedIn U := RelEffCartierDiv.supportedIn_ofPoint u.1 u.2 U (fun x => hu ⟨x, rfl⟩)
  have hD : D.I.IsInvertible := RelEffCartierDiv.isInvertible_I_of_supportedIn U D hDU
  have hD' : (D.pullbackAlong ψ.1 ψ.2).I.IsInvertible :=
    RelEffCartierDiv.isInvertible_I_of_supportedIn U (D.pullbackAlong ψ.1 ψ.2) (hDU.pullbackAlong ψ.1 ψ.2)

  have key : D.pullbackAlong ψ.1 ψ.2 = RelEffCartierDiv.ofPoint c (ψ.1 ≫ u.1) hψu :=
    RelEffCartierDiv.pullbackAlong_ofPoint c u.1 u.2 ψ.1 ψ.2
  have hcomap : D.I.comap Ψ = (D.pullbackAlong ψ.1 ψ.2).I := rfl
  have hIc : (D.I.comap Ψ).IsInvertible := hcomap ▸ hD'
  have hI' : D.I.comap Ψ = (RelEffCartierDiv.ofPoint c (ψ.1 ≫ u.1) hψu).I := by rw [hcomap, key]
  refine ⟨?_, ?_⟩
  · obtain ⟨e⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso Ψ hD hIc
    exact ⟨e ≪≫ eqToIso (by rw [hI'])⟩
  · haveI := Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Ψ hD hIc
    exact ⟨asIso (D.I.pullbackModuleComparison Ψ) ≪≫ eqToIso (by rw [hI'])⟩

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (u : SchemeHomOver t c) (hu : Set.range u.1.base ⊆ (U : Set C)) (ψ : SchemeHomOver t' t)
    (hψu : (ψ.1 ≫ u.1) ≫ c = t') :
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (RelEffCartierDiv.ofPoint c u.1 u.2).lineBundle ≅
        (RelEffCartierDiv.ofPoint c (ψ.1 ≫ u.1) hψu).lineBundle) ∧
      Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (RelEffCartierDiv.ofPoint c u.1 u.2).idealModule ≅
        (RelEffCartierDiv.ofPoint c (ψ.1 ≫ u.1) hψu).idealModule) :=
  OfPointBC.main R c U u hu ψ hψu

#print axioms solution

end S_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset (solution)
