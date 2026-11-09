-- Prove2me | Definitions.Def_ManipPotential_Ranking_Prefers
-- name    : ManipPotential_Ranking_Prefers
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:43:30.908902+00:00
-- url     : https://prove2.me/theorems/d8692638-3006-4e07-9cd3-2f3882a63786
-- title:
--   Strict preference $c \succ_r c'$
-- statement:
--   For a ranking $r \in \mathcal L(C)$ and candidates $c, c'$, write $c \succ_r c'$ if $r$ ranks $c$ strictly above $c'$, that is, the position of $c$ in $r$ is smaller than the position of $c'$.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 2, p.8

import Mathlib
import Definitions.Def_ManipPotential_Ranking

namespace ManipPotential

/-- `c ≻_r c'`: ranking `r` places candidate `c` strictly above `c'` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 2, p.8):
`r c < r c'` (smaller position = higher). -/
def Ranking.Prefers {m : ℕ} (r : Ranking m) (c c' : Fin m) : Prop := r c < r c'

instance {m : ℕ} (r : Ranking m) (c c' : Fin m) : Decidable (Ranking.Prefers r c c') :=
  inferInstanceAs (Decidable (r c < r c'))

end ManipPotential


