-- Prove2me | solution 1 for AlgebraicGeometry.surjective_specMap_of_surjective_of_ker_le_nilradical
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6a9fe7e9-42a2-50bf-9a86-439e8475375c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_surjective_specMap_of_surjective_of_ker_le_nilradical

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
    (hker : RingHom.ker f ≤ nilradical R) :
    Surjective (Spec.map (CommRingCat.ofHom f)) := by
  have h := PrimeSpectrum.isHomeomorph_comap f (fun x => ⟨1, one_pos, by simpa using hf x⟩) hker
  exact ⟨fun x => by
    obtain ⟨y, hy⟩ := h.surjective x
    exact ⟨y, hy⟩⟩

end S_AlgebraicGeometry_surjective_specMap_of_surjective_of_ker_le_nilradical
end P2MW
export P2MW.S_AlgebraicGeometry_surjective_specMap_of_surjective_of_ker_le_nilradical (solution)
