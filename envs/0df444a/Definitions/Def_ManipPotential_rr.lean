-- Prove2me | Definitions.Def_ManipPotential_rr
-- name    : ManipPotential_rr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:44:10.134999+00:00
-- url     : https://prove2.me/theorems/2d996c51-c6fe-406b-aab8-5f427e1a7e90
-- title:
--   Cyclic ranking $r_j : c_j \succ c_{j+1} \succ \cdots \succ c_{j-1}$
-- statement:
--   For an index $j$ (taken modulo $m$), $r_j$ is the ranking
--   $$
--   r_j :\ c_j \succ c_{j+1} \succ c_{j+2} \succ \cdots \succ c_{j-1},
--   $$
--   which starts at $c_j$ and lists the candidates in increasing index order, cyclically. The family is $R = \{r_j\}_j$.
--
--   **Formalization Note** Candidate $c$ sits at position $c - j$ of $r_j$ (arithmetic in `Fin m`), so position $t$ holds $c_{j+t}$.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, "Cyclic profiles", p.27

import Mathlib
import Definitions.Def_ManipPotential_Ranking

namespace ManipPotential

/-- The cyclic ranking `r_j : c_j ≻ c_{j+1} ≻ ⋯ ≻ c_{j−1}` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, "Cyclic profiles",
p.27), indices mod `m`.

**Formalization Note** Candidate `c` sits at position `c − j` in `Fin m`, so position `t` holds
`c_{j+t}`. -/
def rr {m : ℕ} [NeZero m] (j : Fin m) : Ranking m := Equiv.subRight j

end ManipPotential


