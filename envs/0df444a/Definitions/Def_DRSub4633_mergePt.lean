-- Prove2me | Definitions.Def_DRSub4633_mergePt
-- name    : DRSub4633_mergePt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:59:06.861644+00:00
-- url     : https://prove2.me/theorems/a269ed63-f94e-4fc9-90c2-eb75fb4be4c7
-- title:
--   The merged point $(r,l)$ of a small and a large block
-- statement:
--   For the state $x$, with blocks $S=\{j:x_j\le s\}$ and $L$ its complement, a small vector $r$ and a large vector $l$ are merged in the original coordinate order into the point $(r,l)\in\mathbb R^n$ whose $j$-th coordinate is $r_j$ for $j\in S$ and $l_j$ for $j\in L$.
--
--   **Formalization Note** Both blocks are functions on all coordinates; only the relevant block is read at each coordinate.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, p.10

import Mathlib
import Definitions.Def_DRSub4633_sPar

namespace DRSub4633

/-- **The merged point `(r, l)`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, p.10: "A pair of block vectors is
merged in the original coordinate order when used as a function argument", with the blocks
`S = {j : x_j ≤ s}` and `L = [n] ∖ S`.

`mergePt x r l` has coordinate `r_j` for `j ∈ S` and `l_j` for `j ∈ L`.

**Formalization Note.** Both blocks are given as functions on all of `Fin n`; `mergePt` reads `r` on
the small coordinates and `l` on the large ones. The dummy large coordinate is not a coordinate of
`ℝⁿ` (p.10: "all oracle queries omit the dummy coordinate"). -/
noncomputable def mergePt {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (r l : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => if x j ≤ sPar then r j else l j)

end DRSub4633


