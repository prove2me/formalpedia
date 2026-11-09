-- Prove2me | Definitions.Def_ManipPotential_Ranking_WeaklyPrefers
-- name    : ManipPotential_Ranking_WeaklyPrefers
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:43:22.058278+00:00
-- url     : https://prove2.me/theorems/e6f5d2f1-48c8-46f6-886d-18d93f329790
-- title:
--   Weak preference $c \succeq_r c'$
-- statement:
--   For a ranking $r \in \mathcal L(C)$ and candidates $c, c'$, write $c \succeq_r c'$ if either $c \succ_r c'$ or $c = c'$; equivalently, the position of $c$ in $r$ is at most the position of $c'$.
--
--   This is the comparison used in the definition of $k$-augmentation strategyproofness and in all axioms for rules on rational profiles.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 2, p.8

import Mathlib
import Definitions.Def_ManipPotential_Ranking

namespace ManipPotential

/-- `c ⪰_r c'`: either `c ≻_r c'` or `c = c'` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 2, p.8): `r c ≤ r c'`. -/
def Ranking.WeaklyPrefers {m : ℕ} (r : Ranking m) (c c' : Fin m) : Prop := r c ≤ r c'

instance {m : ℕ} (r : Ranking m) (c c' : Fin m) : Decidable (Ranking.WeaklyPrefers r c c') :=
  inferInstanceAs (Decidable (r c ≤ r c'))

end ManipPotential


