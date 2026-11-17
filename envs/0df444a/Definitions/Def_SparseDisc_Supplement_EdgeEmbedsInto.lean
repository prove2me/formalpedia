-- Prove2me | Definitions.Def_SparseDisc_Supplement_EdgeEmbedsInto
-- name    : SparseDisc_Supplement_EdgeEmbedsInto
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:06:04.168514+00:00
-- url     : https://prove2.me/theorems/1ff376c9-0313-4fea-878c-7ef81c162e37
-- title:
--   Edge-bearing part embeds as a subgraph
-- statement:
--   The edge-bearing part of a graph $F$ **embeds into** a graph $T$ if its non-isolated vertices inject into $T$ and every edge maps to an edge. Isolated vertices of $F$ are suppressed.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Theorem 8.35, p.45

import Mathlib

namespace SparseDisc.Supplement

/-- The edge-bearing part of `F` is isomorphic to a subgraph of `T`; isolated vertices of `F` are
ignored. This is the convention used for the omitted-edge graphs in Theorem 8.35
(Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027 submission
manuscript (sha256 0f09ec60…25b81), p.45). -/
def EdgeEmbedsInto {V W : Type} (F : SimpleGraph V) (T : SimpleGraph W) : Prop :=
  ∃ φ : V → W, Set.InjOn φ {v | (F.neighborSet v).Nonempty} ∧
    ∀ u v, F.Adj u v → T.Adj (φ u) (φ v)

end SparseDisc.Supplement


