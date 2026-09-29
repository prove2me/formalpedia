-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.pullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/1bce6718-68c1-5c0f-b5e6-1a247ff075ba

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "morphismRestrict_ι Scheme.Modules.pullback Scheme Scheme.Modules Scheme.Modules.IsLocallyFreeOfRank"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.pullback Modules.pullbackCongr Modules Opens Modules.pullbackComp Modules.IsLocallyFreeOfRank"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback pullbackCongr pullbackComp IsLocallyFreeOfRank"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

scoped instance opensMap_final_of_hom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (TopologicalSpace.Opens.map f.base).Final :=
  CategoryTheory.final_of_representablyFlat _

noncomputable def pullbackFreeIso {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Type u) :
    (Modules.pullback f).obj (SheafOfModules.free.{u} I) ≅ SheafOfModules.free.{u} I :=
  SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I

namespace IsLocallyFreeOfRank p2m_export "AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank" "exists_trivialization" end IsLocallyFreeOfRank
p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank" in
theorem IsLocallyFreeOfRank.pullback' {X Y : Scheme.{u}} (ψ : X ⟶ Y) {n : ℕ} {E : Y.Modules}
    (hE : IsLocallyFreeOfRank n E) :
    IsLocallyFreeOfRank n ((Modules.pullback ψ).obj E) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hU, ⟨eU⟩⟩ := hE.exists_trivialization (ψ.base x)
  refine ⟨ψ ⁻¹ᵁ U, hU, ⟨?_⟩⟩
  have hfact : (ψ ⁻¹ᵁ U).ι ≫ ψ = (ψ ∣_ U) ≫ U.ι := (morphismRestrict_ι ψ U).symm
  exact (Modules.pullbackComp _ _).app E ≪≫ (Modules.pullbackCongr hfact).app E ≪≫
    ((Modules.pullbackComp _ _).app E).symm ≪≫ (Modules.pullback (ψ ∣_ U)).mapIso eU ≪≫
    pullbackFreeIso (ψ ∣_ U) (ULift.{u} (Fin n))

end AlgebraicGeometry.Scheme.Modules
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry.Scheme.Modules"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry"

theorem solution
    {X Y : Scheme.{u}} (ψ : X ⟶ Y) {n : ℕ} {E : Y.Modules}
    (hE : Scheme.Modules.IsLocallyFreeOfRank n E) :
    Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pullback ψ).obj E) :=
  AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.pullback' ψ hE

end S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback (solution)
