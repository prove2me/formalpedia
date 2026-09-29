-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.nonempty_pullback_lineBundle_pullbackAlong_iso_of_supportedIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/1149d922-262c-5ce8-b6f9-8501864d47ce

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivRestrict
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_lineBundle_pullbackAlong_iso_of_supportedIn
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory"
set_option maxHeartbeats 800000

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {ρ : ℕ} (E : RelEffCartierDiv c ρ (𝟙 (Spec (CommRingCat.of R)))) (hEU : E.SupportedIn U)
    ⦃T T' : Scheme.{u}⦄ {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (E.pullbackAlong t (Category.comp_id t)).lineBundle ≅
      (E.pullbackAlong t' (Category.comp_id t')).lineBundle) := by
  obtain ⟨ψ1, hψ⟩ := ψ
  subst hψ

  have hT : (E.pullbackAlong t (Category.comp_id t)).I.IsInvertible :=
    RelEffCartierDiv.isInvertible_I_of_supportedIn U _ (hEU.pullbackAlong t (Category.comp_id t))
  have hT' : ((E.pullbackAlong t (Category.comp_id t)).pullbackAlong ψ1 rfl).I.IsInvertible :=
    RelEffCartierDiv.isInvertible_I_of_supportedIn U _ ((hEU.pullbackAlong t (Category.comp_id t)).pullbackAlong ψ1 rfl)

  have hcomp : (E.pullbackAlong t (Category.comp_id t)).pullbackAlong ψ1 rfl =
      E.pullbackAlong (ψ1 ≫ t) (Category.comp_id _) :=
    RelEffCartierDiv.pullbackAlong_comp E t (Category.comp_id t) ψ1 rfl

  have hI : ((E.pullbackAlong t (Category.comp_id t)).pullbackAlong ψ1 rfl).I =
      (E.pullbackAlong t (Category.comp_id t)).I.comap (baseChangeSnd c ⟨ψ1, rfl⟩) := rfl
  obtain ⟨e⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso (baseChangeSnd c ⟨ψ1, rfl⟩) hT
    (hI ▸ hT')
  refine ⟨e ≪≫ eqToIso ?_⟩
  change ((E.pullbackAlong t (Category.comp_id t)).I.comap (baseChangeSnd c ⟨ψ1, rfl⟩)).invModule =
    (E.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).lineBundle
  rw [← hI, hcomp]

end S_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_lineBundle_pullbackAlong_iso_of_supportedIn
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_lineBundle_pullbackAlong_iso_of_supportedIn (solution)
