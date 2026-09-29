-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/76d40451-f24e-55bd-9d90-d189c132e96c

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_iso

universe u
open CategoryTheory AlgebraicGeometry

theorem solution {X : Scheme.{u}} {n : ℕ} {M N : X.Modules} (e : M ≅ N) (h : Scheme.Modules.IsLocallyFreeOfRank n M) :
    Scheme.Modules.IsLocallyFreeOfRank n N := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hx, ⟨i⟩⟩ := h.exists_trivialization x
  exact ⟨U, hx, ⟨((Scheme.Modules.pullback U.ι).mapIso e).symm ≪≫ i⟩⟩

end S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_iso
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_iso (solution)
