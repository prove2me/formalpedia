-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.bijective_smul_topFormMap_of_isFrameOn_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/2c2784f8-1dd2-5532-9ed0-bb4636baeef9

import Mathlib
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_NeronModelInfra_TopFormOrder
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isIso_of_map_pullbackLocalSection_topToSections_eq_of_isPullback_of_smoothOfRelativeDimension
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_topToSections_bijective_of_isAffineOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_bijective_smul_topFormMap_of_isFrameOn_of_isPullback
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

theorem solution
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B))
    (φ : X ⟶ Y) (hφ : IsPullback φ gX gY (Spec.map (CommRingCat.ofHom (algebraMap A B)))) (d : ℕ)
    [SmoothOfRelativeDimension d gY]
    (U : Y.Opens) (hU : IsAffineOpen U) (s : Γ(gY.topDifferentials d, U)) (hs : Scheme.Modules.IsFrameOn s U)
    (η : ⋀[Γ(Y, U)]^d (gY.kaehlerPresheaf.obj (op U)))
    (hη : gY.topToSections d U η = s)
    (W : X.Opens) (hW : IsAffineOpen W) (hWU : W ≤ φ ⁻¹ᵁ U) :
    letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra W
    letI : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
    ∀ [Algebra A Γ(X, W)] [IsScalarTower A B Γ(X, W)] [IsScalarTower A Γ(Y, U) Γ(X, W)],
      Function.Bijective fun c : Γ(X, W) =>
        c • NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, W) d η := by
  intro iA iT₁ iT₂
  letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra W
  letI : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
  subst hη
  obtain ⟨θ, hθ⟩ :=
    Scheme.Hom.exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq gY gX φ hφ.w d
  haveI : IsIso θ :=
    Scheme.Hom.isIso_of_map_pullbackLocalSection_topToSections_eq_of_isPullback_of_smoothOfRelativeDimension
      gY gX φ hφ d θ hθ

  have hfr : Scheme.Modules.IsFrameOn
      ((asIso θ).hom.app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ (gY.topToSections d U η))) (φ ⁻¹ᵁ U) :=
    (Scheme.Modules.IsFrameOn.pullbackLocalSection φ hs).map_iso (asIso θ)
  have hb := hfr.bijective hWU hWU

  have hchart := hθ U hU W hW hWU η
  rw [asIso_hom, hchart] at hb

  have hT := Scheme.Hom.topToSections_bijective_of_isAffineOpen gX d hW
  have hlin : ∀ (c : Γ(X, W)) (x : ⋀[Γ(X, W)]^d (Ω[Γ(X, W)⁄B])),
      gX.topToSections d W (c • x) = c • gX.topToSections d W x := by
    intro c x
    show (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((Scheme.Modules.presheafExteriorPower X d).obj gX.kaehler.val)).app (op W)).hom
        (exteriorPower.map d (gX.kaehlerToSectionsₗ W) (c • x)) = c • _
    erw [LinearMap.map_smul (exteriorPower.map d (gX.kaehlerToSectionsₗ W))]
    exact (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      ((Scheme.Modules.presheafExteriorPower X d).obj gX.kaehler.val)).app (op W)).hom.map_smul c _
  refine ⟨fun c₁ c₂ h => hb.1 ?_, fun x => ?_⟩
  ·
    dsimp only at h ⊢
    rw [← hlin, ← hlin, h]
  ·
    obtain ⟨c, hc⟩ := hb.2 (gX.topToSections d W x)
    refine ⟨c, hT.1 ?_⟩
    dsimp only at hc ⊢
    rw [hlin]
    exact hc

end S_AlgebraicGeometry_Scheme_Hom_bijective_smul_topFormMap_of_isFrameOn_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_bijective_smul_topFormMap_of_isFrameOn_of_isPullback (solution)
