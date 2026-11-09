-- Prove2me | Definitions.Def_ManipPotential_cycTotal
-- name    : ManipPotential_cycTotal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:44:56.098115+00:00
-- url     : https://prove2.me/theorems/ad7efb6c-18cb-405c-9c73-e3b972404d5a
-- title:
--   Total cyclic weight $X = \sum_j x_j$
-- statement:
--   Write a profile as $P = (x, y)$, where $x_j = P_{\ell_j}$ are its **cyclic coordinates** and $y$ its external coordinates. The total cyclic weight of $P$ is
--   $$
--   X = \sum_{j=1}^m x_j = \sum_{j=1}^m P_{\ell_j}.
--   $$
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, p.30

import Mathlib
import Definitions.Def_ManipPotential_ell

namespace ManipPotential

/-- The total cyclic weight `X = ∑_j x_j` of a profile `P = (x, y)`, where `x_j = P_{ℓ_j}` are its
cyclic coordinates (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, p.30). -/
def cycTotal {m : ℕ} [NeZero m] {R : Type*} [AddCommMonoid R] (P : Ranking m → R) : R :=
  ∑ j, P (ell j)

end ManipPotential


