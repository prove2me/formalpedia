-- Prove2me | Definitions.Def_ManipPotential_Ranking_top
-- name    : ManipPotential_Ranking_top
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:45:00.249211+00:00
-- url     : https://prove2.me/theorems/5f262f7d-5a64-430d-a978-4ad9f0829125
-- title:
--   Top candidate $\mathrm{top}_r C$
-- statement:
--   For a ranking $r \in \mathcal L(C)$ (with $m \ge 1$ candidates), $\mathrm{top}_r C$ is the candidate that $r$ ranks first, i.e. the candidate at position $0$.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 2, p.8

import Mathlib
import Definitions.Def_ManipPotential_Ranking

namespace ManipPotential

/-- `top_r C`, the candidate ranked first by `r` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 2, p.8): the candidate at
position `0`. Requires at least one candidate (`[NeZero m]`). -/
def Ranking.top {m : ℕ} [NeZero m] (r : Ranking m) : Fin m := r.symm 0

end ManipPotential


