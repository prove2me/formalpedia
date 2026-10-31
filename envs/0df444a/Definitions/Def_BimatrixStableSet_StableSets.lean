-- Prove2me | Definitions.Def_BimatrixStableSet_StableSets
-- name    : BimatrixStableSet_StableSets
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:18:26.30198+00:00
-- url     : https://prove2.me/theorems/9f345f10-90bc-4f69-bfe4-cfdbeda56848
-- title:
--   Disjoint stable pairs and the stable-set bound $b(G)$
-- statement:
--   Let $G$ be a graph. A **stable set** is a set of vertices no two of which are adjacent. A **stable pair** is a pair $S_1,S_2$ of disjoint stable sets with $|S_1|=|S_2|$. The **stable-set bound** of $G$ is
--
--   $$
--   b(G)=2\max\{\,|S_1| : (S_1,S_2)\ \text{a stable pair of } G\,\}.
--   $$
--
--   This is the number $b$ in Theorem 3 and in the tables (8) and (9) of the paper. It bounds the number of equilibria, because the equilibrium vertices of the two index classes form such a pair.
--
--   **Formalization Note** Stable sets are Mathlib's `SimpleGraph.IsIndepSet`. The maximum is a `sSup` in $\mathbb N$. Its set contains $0$ and, for a finite graph, is bounded, and polytope graphs are finite.
-- source:
--   Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3, Theorem 3, p.12; Lemma 6, p.15; display (8), p.16

import Mathlib

namespace BimatrixStableSet

/-- A pair of disjoint stable sets of equal size, as in Theorem 3, p.12 (Ickstadt, Theobald, von
Stengel, arXiv:2411.12385v3). A stable set is "a set of vertices no two of which are adjacent",
which is Mathlib's `SimpleGraph.IsIndepSet`. -/
def IsStablePair {V : Type} (G : SimpleGraph V) (S₁ S₂ : Finset V) : Prop :=
  Disjoint S₁ S₂ ∧ G.IsIndepSet (S₁ : Set V) ∧ G.IsIndepSet (S₂ : Set V) ∧ S₁.card = S₂.card

/-- The stable-set bound `b(G)`: twice the largest size `s` such that `G` has two disjoint stable
sets of size `s` (Theorem 3, p.12; Lemma 6, p.15; the numbers `b` of display (8), p.16).

**Formalization Note.** The set of sizes contains `0` (take `S₁ = S₂ = ∅`) and is bounded by the
number of vertices of a finite graph, so the `sSup` in `ℕ` is a true maximum. The graphs of polytopes
have finitely many vertices, which is proved in the verification file. -/
noncomputable def stableSetBound {V : Type} (G : SimpleGraph V) : ℕ :=
  2 * sSup {s : ℕ | ∃ S₁ S₂ : Finset V, IsStablePair G S₁ S₂ ∧ S₁.card = s}

end BimatrixStableSet


