-- Prove2me | Definitions.Def_SparseDisc_laterNeighbours
-- name    : SparseDisc_laterNeighbours
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:49:47.416046+00:00
-- url     : https://prove2.me/theorems/f2dddca0-4ce4-4361-b570-573f6c77e037
-- title:
--   Later neighbours in a vertex ordering
-- statement:
--   Let $H$ be a graph on a finite vertex set $V$ and order $V$ by injective ranks $r : V \to \mathbb N$. The **later neighbours** of $v$ are the neighbours $w$ of $v$ with $r(v) < r(w)$.
--
--   **Formalization Note** An ordering $v_1, \dots, v_n$ is encoded by the ranks $r(v_j) = j$; only the relative order matters.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Section 8, p.29

import Mathlib

namespace SparseDisc

open Classical in
/-- The **later neighbours** of `v` in the ordering of `V` given by the ranks `r : V → ℕ`: the
neighbours `w` of `v` in `H` with `r v < r w` (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond
Additive Functions*, STOC 2027 submission manuscript (sha256 0f09ec60…25b81), Section 8, p.29:
"every vj has at most d neighbours vk with k > j (its later neighbours)").

**Formalization Note** An ordering `v₁, …, v_n` is encoded by injective ranks `r` (`v_j` has rank
`j`); only the relative order of the ranks matters. -/
noncomputable def laterNeighbours {V : Type} [Fintype V] (H : SimpleGraph V) (r : V → ℕ) (v : V) :
    Finset V :=
  Finset.univ.filter (fun w => H.Adj v w ∧ r v < r w)

end SparseDisc


