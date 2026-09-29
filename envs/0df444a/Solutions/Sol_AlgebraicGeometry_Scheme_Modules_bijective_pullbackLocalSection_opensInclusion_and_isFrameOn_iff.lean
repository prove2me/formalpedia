-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.bijective_pullbackLocalSection_opensInclusion_and_isFrameOn_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a499d433-b2e6-5d1f-a72b-2425292c79e1

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_pullbackLocalSection_opensInclusion_and_isFrameOn_iff
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

p2m_open "CategoryTheory Opposite AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_pullbackLocalSection_opensInclusion_and_isFrameOn_iff.AlgebraicGeometry"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom Scheme Scheme.Hom.isIso_app Scheme.Modules Scheme.Opens Scheme.Opens.opensRange_ι Scheme.Modules.IsFrameOn Scheme.Modules.IsFrameOn.of_inf Scheme.Modules.pullbackLocalSection Scheme.Modules.pullbackLocalSection_smul Scheme.Modules.map_homOfLE_pullbackLocalSection"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom Γ Hom.isIso_app Modules Opens Opens.opensRange_ι Modules.IsFrameOn Modules.IsFrameOn.of_inf Modules.pullbackLocalSection Modules.pullbackLocalSection_smul Modules.map_homOfLE_pullbackLocalSection"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "presheaf Hom IsFrameOn IsFrameOn.of_inf pullbackLocalSection pullbackLocalSection_smul map_homOfLE_pullbackLocalSection bijective_unit_app_of_le_opensRange"
namespace G2
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)

lemma bij (W : X.Opens) (hW : W ≤ U) :
    Function.Bijective (fun s : Γ(M, W) => pullbackLocalSection U.ι s) :=
  bijective_unit_app_of_le_opensRange U.ι M W (hW.trans (Scheme.Opens.opensRange_ι U).ge)

lemma app_bij (W : X.Opens) (hW : W ≤ U) : Function.Bijective (fun g : Γ(X, W) => U.ι.app W g) := by
  haveI := Scheme.Hom.isIso_app U.ι W (hW.trans (Scheme.Opens.opensRange_ι U).ge)
  exact ConcreteCategory.bijective_of_isIso (U.ι.app W)

end AlgebraicGeometry.Scheme.Modules.G2

theorem solution {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Function.Bijective (fun s : Γ(M, U) => Scheme.Modules.pullbackLocalSection U.ι s) ∧
      ∀ s : Γ(M, U), Scheme.Modules.IsFrameOn (Scheme.Modules.pullbackLocalSection U.ι s) ⊤ ↔
        Scheme.Modules.IsFrameOn s U := by
  refine ⟨Scheme.Modules.G2.bij M U U le_rfl, fun s => ⟨fun h => ?_, fun h => ?_⟩⟩
  ·
    intro W hWU _
    have hle : U.ι ⁻¹ᵁ W ≤ U.ι ⁻¹ᵁ U := fun _ hx => hWU hx
    have h1 : Function.Bijective fun g' : Γ(↑U, U.ι ⁻¹ᵁ W) =>
        g' • Scheme.Modules.pullbackLocalSection U.ι (M.presheaf.map (homOfLE hWU).op s) := by
      have h0 := h hle le_top
      rw [Scheme.Modules.map_homOfLE_pullbackLocalSection U.ι hWU s] at h0
      exact h0
    have h2 : (fun g : Γ(X, W) => Scheme.Modules.pullbackLocalSection U.ι (g • M.presheaf.map (homOfLE hWU).op s)) =
        (fun g' : Γ(↑U, U.ι ⁻¹ᵁ W) => g' • Scheme.Modules.pullbackLocalSection U.ι (M.presheaf.map (homOfLE hWU).op s)) ∘
          (fun g : Γ(X, W) => U.ι.app W g) := by
      funext g
      simp only [Function.comp_apply, Scheme.Modules.pullbackLocalSection_smul]
    have h3 : Function.Bijective
        (fun g : Γ(X, W) => Scheme.Modules.pullbackLocalSection U.ι (g • M.presheaf.map (homOfLE hWU).op s)) := by
      rw [h2]; exact h1.comp (Scheme.Modules.G2.app_bij U W hWU)
    exact (Function.Bijective.of_comp_iff' (Scheme.Modules.G2.bij M U W hWU)
      (fun g : Γ(X, W) => g • M.presheaf.map (homOfLE hWU).op s)).1 h3
  ·
    exact Scheme.Modules.IsFrameOn.of_inf ((h.pullbackLocalSection U.ι).mono inf_le_right)

end S_AlgebraicGeometry_Scheme_Modules_bijective_pullbackLocalSection_opensInclusion_and_isFrameOn_iff
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_pullbackLocalSection_opensInclusion_and_isFrameOn_iff (solution)
