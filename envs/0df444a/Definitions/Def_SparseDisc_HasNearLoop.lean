-- Prove2me | Definitions.Def_SparseDisc_HasNearLoop
-- name    : SparseDisc_HasNearLoop
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:53:19.050052+00:00
-- url     : https://prove2.me/theorems/a5ecf406-4c20-4216-8c41-673fd4d36b4b
-- title:
--   Set containing a near-loop
-- statement:
--   A **near-loop** in $A \subseteq \{\pm1\}^S$ is a 2-path $z_0, \dots, z_k$ in $A$ with $\operatorname{dist}(z_k, -z_0) \le 1$. Every 1-loop and every 2-loop is a near-loop.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Section 8.7, p.39

import Mathlib
import Definitions.Def_SparseDisc_IsSPath

namespace SparseDisc

/-- `HasNearLoop A`: the set `A` **contains a near-loop**, a 2-path `z₀, …, z_k` in `A` with
`dist(z_k, −z₀) ≤ 1` (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC
2027 submission manuscript (sha256 0f09ec60…25b81), Section 8.7, p.39). -/
def HasNearLoop {U : Type} [Fintype U] (A : Set (Cube U)) : Prop :=
  ∃ (z : ℕ → Cube U) (L : ℕ), IsSPath 2 A z L ∧ hammingDist (z L) (-(z 0)) ≤ 1

end SparseDisc


