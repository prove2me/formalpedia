-- Prove2me | Definitions.Def_ManipPotential_extNorm
-- name    : ManipPotential_extNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:45:48.532272+00:00
-- url     : https://prove2.me/theorems/d2ee2296-f59b-47f8-9510-cdd3ffa7dab0
-- title:
--   External $\ell^1$ norm $\|y\|_1$
-- statement:
--   For a profile $P = (x, y)$, the $\ell^1$ norm of its external coordinates is
--   $$
--   \|y\|_1 = \sum_{s \in \mathcal L(C) \setminus L} |P_s| .
--   $$
--   For nonnegative profiles this is the total weight on external rankings.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, p.30, Corollary 6.7

import Mathlib
import Definitions.Def_ManipPotential_ExtRanking

namespace ManipPotential

/-- The ℓ¹ norm `‖y‖₁ = ∑_{s ∈ L(C) \ L} |y_s|` of the external coordinates of a profile
`P = (x, y)` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, p.30, Corollary 6.7). -/
def extNorm {m : ℕ} [NeZero m] {R : Type*} [Lattice R] [AddCommGroup R] (P : Ranking m → R) : R :=
  ∑ s : ExtRanking m, |P s.1|

end ManipPotential


