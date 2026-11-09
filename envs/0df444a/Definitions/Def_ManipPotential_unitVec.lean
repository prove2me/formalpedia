-- Prove2me | Definitions.Def_ManipPotential_unitVec
-- name    : ManipPotential_unitVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:43:29.66683+00:00
-- url     : https://prove2.me/theorems/7620c816-9bed-4014-b427-bb23786ac04c
-- title:
--   Unit vector $e_r$ of a ranking
-- statement:
--   A rational (or real) profile is a vector $P = (P_r)_{r \in \mathcal L(C)}$ of nonnegative multiplicities. For a ranking $r$, $e_r$ is the corresponding unit vector: $1$ in coordinate $r$, $0$ elsewhere. Following the paper, $P + a r$ denotes $P + a\,e_r$.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, "From integer to rational profiles", p.26

import Mathlib
import Definitions.Def_ManipPotential_Ranking

namespace ManipPotential

/-- The unit vector `e_r` of a ranking `r` in `R^{L(C)}` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, p.26: "we also use
each ranking `r` to denote its corresponding unit vector `e_r`"). -/
def unitVec {m : ℕ} {R : Type*} [Zero R] [One R] (r : Ranking m) : Ranking m → R :=
  Pi.single r 1

end ManipPotential


