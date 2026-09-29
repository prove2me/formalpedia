-- Prove2me | solution 1 for Algebra.norm_of_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/207dad7c-023f-5234-bb73-1f08066aa3db

import Mathlib.RingTheory.Norm.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_norm_of_subsingleton

theorem solution {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [Subsingleton A] (a : A) : Algebra.norm R a = 1 :=
  LinearMap.det_eq_one_of_subsingleton _

end S_Algebra_norm_of_subsingleton
end P2MW
export P2MW.S_Algebra_norm_of_subsingleton (solution)
