-- Prove2me | Definitions.Def_SparseDisc_restrictTo
-- name    : SparseDisc_restrictTo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:52:25.811653+00:00
-- url     : https://prove2.me/theorems/0ae309f0-85c8-4051-8ded-9cb3795f8c1c
-- title:
--   Restriction $x|_s$ of a sign vector
-- statement:
--   The **restriction** of $x \in \{\pm1\}^{\iota}$ to a set of items $s \subseteq \iota$ is $x|_s \in \{\pm1\}^s$, $(x|_s)_j = x_j$.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Definition 8.4, p.30

import Mathlib
import Definitions.Def_SparseDisc_Cube

namespace SparseDisc

/-- The restriction `x|_s ∈ {±1}^s` of `x ∈ {±1}^ι` to a set of items `s` (Zeng–Cao–Dai–Wang–Liao,
*Sparse Discrepancy Beyond Additive Functions*, STOC 2027 submission manuscript (sha256
0f09ec60…25b81), Definition 8.4, p.30: "x|Uv"). -/
def restrictTo {ι : Type} (s : Finset ι) (x : Cube ι) : Cube s := fun j => x j

end SparseDisc


