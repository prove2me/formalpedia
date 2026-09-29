-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.of_forall_exists_opens
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/0915999f-5a80-5c6c-b7ba-6b52dfbc0e88

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_forall_exists_opens

universe u
p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_forall_exists_opens.AlgebraicGeometry Opposite AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_forall_exists_opens.AlgebraicGeometry.Scheme.Modules"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme Scheme.Modules Scheme.Modules.IsLocallyFreeOfRank"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.pullback Modules Opens Modules.IsLocallyFreeOfRank"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback pullbackCongr pullbackComp IsLocallyFreeOfRank"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

theorem opensMap_final' {X Y : Scheme.{u}} (f : X ⟶ Y) : (TopologicalSpace.Opens.map f.base).Final :=
  CategoryTheory.final_of_representablyFlat _

noncomputable def pullbackFreeIso' {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Type u) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.free.{u} I) ≅ SheafOfModules.free.{u} I :=
  haveI := opensMap_final' f
  SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I
end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_forall_exists_opens.AlgebraicGeometry in
theorem solution {X : Scheme.{u}} {n : ℕ} {M : X.Modules}
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pullback U.ι).obj M)) :
    Scheme.Modules.IsLocallyFreeOfRank n M := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hxU, hU⟩ := h x
  obtain ⟨V, hxV, ⟨e⟩⟩ := hU.exists_trivialization ⟨x, hxU⟩
  refine ⟨U.ι ''ᵁ V, ⟨⟨x, hxU⟩, hxV, rfl⟩, ⟨?_⟩⟩
  let i := U.ι.isoImage V
  have hi : i.inv ≫ V.ι ≫ U.ι = (U.ι ''ᵁ V).ι := U.ι.isoImage_inv_ι V
  exact (pullbackCongr hi.symm).app M ≪≫
    ((pullbackComp i.inv (V.ι ≫ U.ι)).symm.app M) ≪≫
    (Scheme.Modules.pullback i.inv).mapIso
      (((pullbackComp V.ι U.ι).symm.app M) ≪≫ (Scheme.Modules.pullback V.ι).mapIso (Iso.refl _) ≪≫ e) ≪≫
    pullbackFreeIso' i.inv _

end S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_forall_exists_opens
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_forall_exists_opens (solution)
