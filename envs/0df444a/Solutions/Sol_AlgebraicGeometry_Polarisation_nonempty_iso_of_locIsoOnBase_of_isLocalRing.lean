-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.nonempty_iso_of_locIsoOnBase_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/39fdd632-2142-5ea9-899d-eafff0bdd30c

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_nonempty_iso_of_locIsoOnBase_of_isLocalRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Polarisation

universe u

theorem solution
    {S : Type u} [CommRing S] [IsLocalRing S] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of S))
    (M M' : X.Modules) (h : LocIsoOnBase g M M') :
    Nonempty (M ≅ M') := by
  obtain ⟨U, hsU, ⟨φ⟩⟩ := h (IsLocalRing.closedPoint S)
  have hU : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hsU
  subst hU

  let ψ : ∀ N : X.Modules,
      N ≅ (Scheme.Modules.pullback X.topIso.inv).obj ((Scheme.Modules.pullback (⊤ : X.Opens).ι).obj N) := fun N =>
    ((Scheme.Modules.pullbackId X).app N).symm ≪≫
      (Scheme.Modules.pullbackCongr (Scheme.toIso_inv_ι X).symm).app N ≪≫
      ((Scheme.Modules.pullbackComp X.topIso.inv (⊤ : X.Opens).ι).symm).app N
  exact ⟨ψ M ≪≫ (Scheme.Modules.pullback X.topIso.inv).mapIso φ ≪≫ (ψ M').symm⟩

end S_AlgebraicGeometry_Polarisation_nonempty_iso_of_locIsoOnBase_of_isLocalRing
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_nonempty_iso_of_locIsoOnBase_of_isLocalRing (solution)
