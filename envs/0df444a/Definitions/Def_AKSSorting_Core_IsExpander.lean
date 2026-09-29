-- Prove2me | Definitions.Def_AKSSorting_Core_IsExpander
-- name    : AKSSorting_Core_IsExpander
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T09:42:47.535616+00:00
-- url     : https://prove2.me/theorems/6b16078e-343f-4862-b6f7-6758dd52f33a
-- title:
--   ⟨k, ε⟩ bipartite expanders on ⟨A, B⟩ (Definition 2.2, nonempty-set reading)
-- statement:
--   Let $A$ and $B$ be disjoint finite sets of vertices, $k\in\mathbb N$ and $\varepsilon>0$. For a set of vertices $X$ let $\Gamma_X$ be the set of vertices adjacent to some vertex of $X$. A graph $G$ is a **$\langle k,\varepsilon\rangle$ expander on $\langle A,B\rangle$** if
--
--   1. every edge of $G$ joins a vertex of $A$ to a vertex of $B$ (so $A\cup B$ carries all edges and no edge lies inside $A$ or inside $B$);
--   2. every vertex has at most $k$ neighbours;
--   3. for every nonempty $X\subseteq A$ and every nonempty $Y\subseteq B$,
--   $$
--   |\Gamma_X| > (1-\varepsilon)\,\frac1\varepsilon\,\min\{|X|,\ \varepsilon|B|\},
--   \qquad
--   |\Gamma_Y| > (1-\varepsilon)\,\frac1\varepsilon\,\min\{|Y|,\ \varepsilon|A|\}.
--   $$
--
--   Small sets expand by a factor $(1-\varepsilon)/\varepsilon$, and every set whose size exceeds an $\varepsilon$-fraction of the opposite side has more than a $(1-\varepsilon)$-fraction of that side as neighbours. In the sorting network these graphs supply the comparators of the $\varepsilon$-halving steps.
--
--   **Formalization Note** Definition 2.2 of the paper imposes the inequalities for *all* $X\subseteq A$ and $Y\subseteq B$. For $X=\emptyset$ both sides are $0$ and the strict inequality $0>0$ fails, so as printed no graph is an expander and Lemma 3 would be false. The conditions are imposed on nonempty sets only; the strict inequality is kept, since the proof of Lemma 4 needs it and applies it only to nonempty sets. The graph lives on an ambient vertex type; condition 1 makes $\Gamma_X$ and every neighbourhood finite, so `Set.ncard` gives the true cardinality. The degree bound uses `Set.encard`. Disjointness of $A$ and $B$ is part of the definition.
-- source:
--   Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983), p. 6, Definition 2.2

import Mathlib

namespace AKSSorting.Core

/-- `Γ_X`: the set of vertices adjacent to some vertex of `X`. -/
def neighbours {V : Type} (G : SimpleGraph V) (X : Finset V) : Set V :=
  {v | ∃ x ∈ X, G.Adj x v}

/-- `G` is a `⟨k, ε⟩` expander on `⟨A, B⟩` (Ajtai–Komlós–Szemerédi 1983, Definition 2.2, p. 6):
`A` and `B` are disjoint, every edge of `G` joins a vertex of `A` to a vertex of `B` (so no edge
lies inside `A` or inside `B` and no vertex outside `A ∪ B` has an edge), every vertex has at most
`k` neighbours, and for every **nonempty** `X ⊆ A` and every **nonempty** `Y ⊆ B`
`|Γ_X| > (1-ε)(1/ε) min{|X|, ε|B|}` and `|Γ_Y| > (1-ε)(1/ε) min{|Y|, ε|A|}`.

Correction to the page: the paper requires the inequalities for all `X ⊆ A`, including `X = ∅`,
where both sides are `0` and the strict inequality fails; as printed no graph would be an
expander. The conditions are therefore imposed on nonempty sets only. -/
def IsExpander {V : Type} (G : SimpleGraph V) (A B : Finset V) (k : ℕ) (ε : ℝ) : Prop :=
  Disjoint A B ∧
  (∀ u v, G.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)) ∧
  (∀ v, (G.neighborSet v).encard ≤ (k : ℕ∞)) ∧
  (∀ X ⊆ A, X.Nonempty →
    (1 - ε) * (1 / ε) * min (X.card : ℝ) (ε * B.card) < ((neighbours G X).ncard : ℝ)) ∧
  (∀ Y ⊆ B, Y.Nonempty →
    (1 - ε) * (1 / ε) * min (Y.card : ℝ) (ε * A.card) < ((neighbours G Y).ncard : ℝ))

end AKSSorting.Core


