-- Prove2me | Definitions.Def_SparseDisc_Supplement_PeelsToAtMost
-- name    : SparseDisc_Supplement_PeelsToAtMost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:05:47.354207+00:00
-- url     : https://prove2.me/theorems/a6b7aaaf-40f7-421b-bffc-57673b790085
-- title:
--   Peeling by vertices of current degree at most $2$
-- statement:
--   A graph **peels to at most $k$ vertices** when repeated deletion of a vertex having at most two neighbours in the current graph leaves a residual graph with at most $k$ vertices. An injective rank records the deletion order.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Theorem 8.35, p.45

import Mathlib

namespace SparseDisc.Supplement

open Classical in
/-- `PeelsToAtMost G k`: repeated deletion of a current vertex having at most two current
neighbours leaves at most `k` vertices (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive
Functions*, STOC 2027 submission manuscript (sha256 0f09ec60…25b81), Theorem 8.35, p.45).

**Formalization Note** `W` is the final residual graph. Injective ranks order deleted vertices;
when `v` is deleted, its current neighbours are the later-ranked deleted vertices together with
the vertices of `W`. -/
noncomputable def PeelsToAtMost {V : Type} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ W : Finset V, W.card ≤ k ∧ ∃ r : V → ℕ, Function.Injective r ∧
    ∀ v, v ∉ W →
      (Finset.univ.filter (fun w => G.Adj v w ∧ (w ∈ W ∨ r v < r w))).card ≤ 2

end SparseDisc.Supplement


