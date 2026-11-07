-- Prove2me | Definitions.Def_SparseDisc_IsLip
-- name    : SparseDisc_IsLip
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:52:28.600183+00:00
-- url     : https://prove2.me/theorems/5d6b634d-a76d-4293-934a-5205ee19b98b
-- title:
--   $L$-Lipschitz function on the cube
-- statement:
--   A function $g : \{\pm1\}^U \to \mathbb R$ is **$L$-Lipschitz** if
--   $$
--   |g(z) - g(z')| \le L \operatorname{dist}(z, z') \qquad \text{for all } z, z' ,
--   $$
--   for the Hamming distance.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Section 2 (Notation), p.11

import Mathlib
import Definitions.Def_SparseDisc_Cube

namespace SparseDisc

/-- A function `g : {±1}^U → ℝ` is **`L`-Lipschitz** for the Hamming distance:
`|g(z) − g(z')| ≤ L · dist(z, z')` (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive
Functions*, STOC 2027 submission manuscript (sha256 0f09ec60…25b81), Section 2, p.11). -/
def IsLip {U : Type} [Fintype U] (L : ℝ) (g : Cube U → ℝ) : Prop :=
  ∀ z z' : Cube U, |g z - g z'| ≤ L * hammingDist z z'

end SparseDisc


