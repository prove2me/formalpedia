-- Prove2me | Definitions.Def_ManipPotential_cycL
-- name    : ManipPotential_cycL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:44:57.701416+00:00
-- url     : https://prove2.me/theorems/2f0eee18-7e77-4a61-b285-84a5437d5e45
-- title:
--   L-profile $xL = \sum_j x_j \ell_j$
-- statement:
--   For a coefficient vector $x = (x_1, \dots, x_m)$, the L-profile is
--   $$
--   xL = \sum_{j=1}^m x_j\, \ell_j ,
--   $$
--   the profile giving weight $x_j$ to the cyclic ranking $\ell_j$ and weight $0$ to every other ranking.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, "Cyclic profiles", p.27

import Mathlib
import Definitions.Def_ManipPotential_ell
import Definitions.Def_ManipPotential_unitVec

namespace ManipPotential

/-- The L-profile `xL = ∑_j x_j ℓ_j` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, p.27). -/
def cycL {m : ℕ} [NeZero m] {R : Type*} [Semiring R] (x : Fin m → R) : Ranking m → R :=
  ∑ j, x j • unitVec (ell j)

end ManipPotential


