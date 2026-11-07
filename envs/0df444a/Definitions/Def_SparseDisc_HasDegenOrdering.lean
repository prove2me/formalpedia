-- Prove2me | Definitions.Def_SparseDisc_HasDegenOrdering
-- name    : SparseDisc_HasDegenOrdering
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:05.783207+00:00
-- url     : https://prove2.me/theorems/d3c88859-a29d-48c8-a345-c2755b2e265d
-- title:
--   $d$-degenerate graph
-- statement:
--   A graph $H$ on a finite vertex set is **$d$-degenerate** if its vertices can be ordered $v_1, \dots, v_n$ so that every $v_j$ has at most $d$ neighbours $v_k$ with $k > j$ (its later neighbours).
--
--   Degeneracy is the sparsity measure of the main theorem: planar graphs are 5-degenerate, graphs of treewidth $k$ are $k$-degenerate, and graphs of maximum degree $\Delta$ are $\Delta$-degenerate.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Section 8, p.29; also p.4

import Mathlib
import Definitions.Def_SparseDisc_laterNeighbours

namespace SparseDisc

/-- `HasDegenOrdering H d`: the graph `H` is **`d`-degenerate**, i.e. its vertices can be ordered so
that every vertex has at most `d` later neighbours (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy
Beyond Additive Functions*, STOC 2027 submission manuscript (sha256 0f09ec60…25b81), Section 8,
p.29; also p.4).

**Formalization Note** The ordering is given by injective ranks `r : V → ℕ`. -/
def HasDegenOrdering {V : Type} [Fintype V] (H : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ r : V → ℕ, Function.Injective r ∧ ∀ v, (laterNeighbours H r v).card ≤ d

end SparseDisc


