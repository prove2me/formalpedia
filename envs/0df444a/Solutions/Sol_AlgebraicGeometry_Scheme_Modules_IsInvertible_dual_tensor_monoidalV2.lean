-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.dual_tensor_monoidalV2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/3e2be821-f658-5aea-82f9-29b4d8fddf8a

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_PresheafOfModules_InternalHom
import Definitions.Def_SheafOfModules_MonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor_monoidalV2
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme Scheme.Modules Scheme.Modules.IsInvertible Scheme.Modules.dual Scheme.Modules.IsInvertible.dual_monoidalV2 Scheme.Modules.IsInvertible.tensor_monoidalV2"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules Modules.IsInvertible Modules.dual Modules.IsInvertible.dual_monoidalV2 Modules.IsInvertible.tensor_monoidalV2"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "IsInvertible tensor dual IsInvertible.dual_monoidalV2 IsInvertible.tensor_monoidalV2"
namespace InverseUnique
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory"

noncomputable def inverseUnique {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    {L M M' : C} (e : L ⊗ M ≅ 𝟙_ C) (e' : L ⊗ M' ≅ 𝟙_ C) : M ≅ M' :=
  (λ_ M).symm ≪≫ (e'.symm ⊗ᵢ Iso.refl M) ≪≫ (β_ L M' ⊗ᵢ Iso.refl M) ≪≫ α_ M' L M ≪≫
    (Iso.refl M' ⊗ᵢ e) ≪≫ ρ_ M'

end AlgebraicGeometry.Scheme.Modules.InverseUnique

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor_monoidalV2.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor_monoidalV2.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.InverseUnique in
theorem solution
    {X : AlgebraicGeometry.Scheme.{u}} {L M : X.Modules}
    (hL : AlgebraicGeometry.Scheme.Modules.IsInvertible L)
    (hM : AlgebraicGeometry.Scheme.Modules.IsInvertible M) :
    Nonempty (AlgebraicGeometry.Scheme.Modules.dual (L ⊗ M) ≅
      AlgebraicGeometry.Scheme.Modules.dual L ⊗ AlgebraicGeometry.Scheme.Modules.dual M) := by
  obtain ⟨eL⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2 hL).2
  obtain ⟨eM⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2 hM).2
  obtain ⟨eLM⟩ := (Scheme.Modules.IsInvertible.dual_monoidalV2
    (Scheme.Modules.IsInvertible.tensor_monoidalV2 hL hM)).2

  let e' : (L ⊗ M) ⊗ (Scheme.Modules.dual L ⊗ Scheme.Modules.dual M) ≅ 𝟙_ X.Modules :=
    α_ L M _ ≪≫ (Iso.refl L ⊗ᵢ ((α_ M _ _).symm ≪≫ (β_ M (Scheme.Modules.dual L) ⊗ᵢ Iso.refl _) ≪≫
      α_ _ M _ ≪≫ (Iso.refl _ ⊗ᵢ eM) ≪≫ ρ_ _)) ≪≫ eL
  exact ⟨inverseUnique eLM e'⟩

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor_monoidalV2
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor_monoidalV2 (solution)
