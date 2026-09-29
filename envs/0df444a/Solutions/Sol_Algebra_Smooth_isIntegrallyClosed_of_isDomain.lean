-- Prove2me | solution 1 for Algebra.Smooth.isIntegrallyClosed_of_isDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/7d849952-2770-5d38-a42a-4f9e7a5362a4

import Mathlib
import Theorems.Thm_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_Smooth_isIntegrallyClosed_of_isDomain

universe u

theorem solution (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (S : Type u) [CommRing S] [IsDomain S] [Algebra R S] [Algebra.Smooth R S] : IsIntegrallyClosed S := by

  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ hp
  haveI := hp.isPrime
  exact (Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime R S p (Localization.AtPrime p)).2

end S_Algebra_Smooth_isIntegrallyClosed_of_isDomain
end P2MW
export P2MW.S_Algebra_Smooth_isIntegrallyClosed_of_isDomain (solution)
