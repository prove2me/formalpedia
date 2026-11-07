-- Prove2me | Definitions.Def_SparseDisc_Cube
-- name    : SparseDisc_Cube
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:38.655871+00:00
-- url     : https://prove2.me/theorems/5c6c228f-5e2f-44a3-a880-157d90598b7b
-- title:
--   Hamming cube $\{\pm1\}^U$
-- statement:
--   For a finite set $U$, $\{\pm1\}^U$ is the set of sign vectors indexed by $U$, with pointwise negation $z \mapsto -z$ and the Hamming distance $\operatorname{dist}$.
--
--   **Formalization Note** Signs are the units of $\mathbb Z$ and the distance is Mathlib's `hammingDist`. For $U = \emptyset$ the cube has a single point, which is its own antipode, as in Section 8.1.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Section 2 (Notation), p.11; Section 8.1, p.29

import Mathlib

namespace SparseDisc

/-- The **Hamming cube** `{±1}^U` of sign vectors indexed by `U` (Zeng–Cao–Dai–Wang–Liao, *Sparse
Discrepancy Beyond Additive Functions*, STOC 2027 submission manuscript (sha256 0f09ec60…25b81),
Section 2, p.11).

**Formalization Note** `U` is a type (finite in every use) and signs are the units `±1` of `ℤ`;
negation is pointwise and the distance is Mathlib's `hammingDist`. For empty `U` the cube has one
point, which is its own antipode, as on p.29. -/
abbrev Cube (U : Type) : Type := U → ℤˣ

end SparseDisc


