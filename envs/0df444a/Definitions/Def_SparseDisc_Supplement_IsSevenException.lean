-- Prove2me | Definitions.Def_SparseDisc_Supplement_IsSevenException
-- name    : SparseDisc_Supplement_IsSevenException
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:06:29.279489+00:00
-- url     : https://prove2.me/theorems/0c4c3efd-6e9c-42b0-aede-3865c11f389f
-- title:
--   Seven-vertex exception family from Theorem 8.35
-- statement:
--   A graph is a **seven-vertex exception** when it is $K_7-E(F)$ and the edge-bearing part of $F$ is isomorphic to a subgraph of $C_4$, $3K_2$, or $K_3$. This is exactly the exception family in Theorem 8.35.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Theorem 8.35, p.45

import Mathlib
import Definitions.Def_SparseDisc_Supplement_EdgeEmbedsInto

namespace SparseDisc.Supplement

/-- The seven-vertex exceptions of Theorem 8.35: `K₇ - E(F)` where the edge-bearing part of `F`
is isomorphic to a subgraph of `C₄`, `3K₂`, or `K₃` (Zeng–Cao–Dai–Wang–Liao, *Sparse
Discrepancy Beyond Additive Functions*, STOC 2027 submission manuscript (sha256
0f09ec60…25b81), p.45).

**Formalization Note** `3K₂` has vertex type `Fin 3 × Bool`, with the two vertices sharing their
first coordinate adjacent. Isolated vertices of the omitted-edge graph are suppressed by
`EdgeEmbedsInto`, matching the paper's graph-isomorphism convention. -/
def IsSevenException {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  Fintype.card V = 7 ∧ ∃ F : SimpleGraph V, G = (⊤ \ F) ∧
    (EdgeEmbedsInto F (SimpleGraph.cycleGraph 4) ∨
     EdgeEmbedsInto F (SimpleGraph.fromRel (fun a b : Fin 3 × Bool => a.1 = b.1 ∧ a.2 ≠ b.2)) ∨
     EdgeEmbedsInto F (⊤ : SimpleGraph (Fin 3)))

end SparseDisc.Supplement


