-- Prove2me | Definitions.Def_ManipPotential_ell
-- name    : ManipPotential_ell
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:43:35.235204+00:00
-- url     : https://prove2.me/theorems/ca4dd412-2e88-4cdd-bc3e-13a41daf8408
-- title:
--   Cyclic ranking $\ell_j : c_j \succ c_{j-1} \succ \cdots \succ c_{j+1}$
-- statement:
--   For an index $j$ (taken modulo $m$), $\ell_j$ is the ranking
--   $$
--   \ell_j :\ c_j \succ c_{j-1} \succ c_{j-2} \succ \cdots \succ c_{j+1},
--   $$
--   which starts at $c_j$ and lists the candidates in decreasing index order, cyclically. The family $L = \{\ell_j\}_{j}$ carries the cyclic coordinates of a profile.
--
--   **Formalization Note** Indices are elements of `Fin m` with arithmetic mod $m$; candidate $c$ sits at position $j - c$ of $\ell_j$, so position $t$ holds $c_{j-t}$.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, "Cyclic profiles", p.27

import Mathlib
import Definitions.Def_ManipPotential_Ranking

namespace ManipPotential

/-- The cyclic ranking `ℓ_j : c_j ≻ c_{j−1} ≻ ⋯ ≻ c_{j+1}` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, "Cyclic profiles",
p.27), indices mod `m`.

**Formalization Note** Candidate `c` sits at position `j − c` in `Fin m`, so position `t` holds
`c_{j−t}`. -/
def ell {m : ℕ} [NeZero m] (j : Fin m) : Ranking m := Equiv.subLeft j

end ManipPotential


