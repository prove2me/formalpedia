-- Prove2me | Definitions.Def_SparseDisc_IsOrientation
-- name    : SparseDisc_IsOrientation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:36.888339+00:00
-- url     : https://prove2.me/theorems/279b49b9-8f09-4268-8363-e041bac7e5d0
-- title:
--   Orientation of a graph
-- statement:
--   An **orientation** of a graph $H$ assigns to every edge $uv$ exactly one of the two directions $u \to v$, $v \to u$, and directs nothing else. The in-degree of $v$ is the number of edges directed towards $v$.
--
--   **Formalization Note** The orientation is a relation $D$ with $D(u, v)$ meaning $u \to v$.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Theorem 8.32, p.43

import Mathlib

namespace SparseDisc

/-- `IsOrientation H D`: the relation `D` (`D u v` meaning the edge `uv` is directed from `u` to
`v`) is an **orientation** of `H`: it only directs edges of `H`, and every edge receives exactly
one direction (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027
submission manuscript (sha256 0f09ec60…25b81), Theorem 8.32, p.43). The in-degree of `v` is the
number of `u` with `D u v`. -/
def IsOrientation {V : Type} (H : SimpleGraph V) (D : V → V → Prop) : Prop :=
  (∀ u v, D u v → H.Adj u v) ∧ ∀ u v, H.Adj u v → (D u v ∨ D v u) ∧ ¬ (D u v ∧ D v u)

end SparseDisc


