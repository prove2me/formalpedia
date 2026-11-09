-- Prove2me | Definitions.Def_ManipPotential_cycR
-- name    : ManipPotential_cycR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:45:57.87313+00:00
-- url     : https://prove2.me/theorems/8c9fddd9-6920-423f-8f30-e88baa3cab4c
-- title:
--   R-profile $xR = \sum_j x_j r_j$
-- statement:
--   For a coefficient vector $x = (x_1, \dots, x_m)$, the R-profile is
--   $$
--   xR = \sum_{j=1}^m x_j\, r_j ,
--   $$
--   the profile giving weight $x_j$ to the cyclic ranking $r_j$ and weight $0$ to every other ranking.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, "Cyclic profiles", p.27

import Mathlib
import Definitions.Def_ManipPotential_rr
import Definitions.Def_ManipPotential_unitVec

namespace ManipPotential

/-- The R-profile `xR = ∑_j x_j r_j` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, p.27). -/
def cycR {m : ℕ} [NeZero m] {R : Type*} [Semiring R] (x : Fin m → R) : Ranking m → R :=
  ∑ j, x j • unitVec (rr j)

end ManipPotential


