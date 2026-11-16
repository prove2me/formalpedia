-- Prove2me | Definitions.Def_ManipPotential_Supplement_pairCount
-- name    : ManipPotential_Supplement_pairCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:01:46.757031+00:00
-- url     : https://prove2.me/theorems/34c12c2a-2cb6-41c5-9bc6-45792e7cecbb
-- title:
--   Pairwise counts $|\{i : c \succ_i d\}|$
-- statement:
--   For a profile $\succ_N$ and candidates $c, d$, the **pairwise count** $n_{c \succ d} = |\{ i \in N : c \succ_i d \}|$ is the number of voters ranking $c$ strictly above $d$.
--
--   It decides the runoff round of plurality with runoff and defines the margin matrix.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.1.2, p.12; Section 4.3, p.19

import Mathlib
import Definitions.Def_ManipPotential_Ranking_Prefers

namespace ManipPotential.Supplement

/-- `|{i : c ≻_i d}|`, the number of ballots of the profile ranking `c` strictly above `d`
(Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.1.2, p.12 (runoff round) and Section 4.3, p.19 (margin matrix)). -/
def pairCount {m : ℕ} (P : List (Ranking m)) (c d : Fin m) : ℕ :=
  P.countP (fun r => decide (Ranking.Prefers r c d))

end ManipPotential.Supplement


