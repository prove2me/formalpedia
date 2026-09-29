-- Prove2me | solution 1 for AdicCompletion.eq_maximalIdeal_of_comap_algebraMap_eq_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/dc3fb1e0-c061-53b3-ae6d-def39df35014

import Mathlib
import Definitions.Def_AdicCompletionLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AdicCompletion_eq_maximalIdeal_of_comap_algebraMap_eq_maximalIdeal

set_option autoImplicit false

open IsLocalRing

theorem solution
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (P : Ideal (AdicCompletion (maximalIdeal R) R)) [P.IsPrime]
    (hP : Ideal.comap (algebraMap R (AdicCompletion (maximalIdeal R) R)) P = maximalIdeal R) :
    P = maximalIdeal (AdicCompletion (maximalIdeal R) R) := by
  have hle : maximalIdeal (AdicCompletion (maximalIdeal R) R) ≤ P := by
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_le_iff_le_comap, hP]
  exact ((IsLocalRing.maximalIdeal.isMaximal _).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm

end S_AdicCompletion_eq_maximalIdeal_of_comap_algebraMap_eq_maximalIdeal
end P2MW
export P2MW.S_AdicCompletion_eq_maximalIdeal_of_comap_algebraMap_eq_maximalIdeal (solution)
