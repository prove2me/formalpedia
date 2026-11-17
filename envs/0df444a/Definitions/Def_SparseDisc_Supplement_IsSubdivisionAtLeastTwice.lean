-- Prove2me | Definitions.Def_SparseDisc_Supplement_IsSubdivisionAtLeastTwice
-- name    : SparseDisc_Supplement_IsSubdivisionAtLeastTwice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:04:58.731215+00:00
-- url     : https://prove2.me/theorems/a56d0b1d-9718-4717-9556-4b472ae42f0b
-- title:
--   Every edge subdivided at least twice
-- statement:
--   A graph is an **at-least-twice subdivision** if it is isomorphic to a simple graph in which every original edge is replaced by a path containing at least two new vertices.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Theorem 8.22(b), p.38

import Mathlib
import Definitions.Def_SparseDisc_subdivide

namespace SparseDisc.Supplement

/-- A graph obtained from a simple graph by subdividing every edge at least twice, the example in
Theorem 8.22(b) (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027
submission manuscript (sha256 0f09ec60…25b81), p.38).

**Formalization Note** `SparseDisc.subdivide G₀ k` inserts `k e + 1` vertices on edge `e`, so
`1 ≤ k e` is exactly at least two inserted vertices. -/
def IsSubdivisionAtLeastTwice {V : Type} (H : SimpleGraph V) : Prop :=
  ∃ (W : Type) (G₀ : SimpleGraph W) (k : G₀.edgeSet → ℕ),
    (∀ e, 1 ≤ k e) ∧ Nonempty (H ≃g SparseDisc.subdivide G₀ k)

end SparseDisc.Supplement


