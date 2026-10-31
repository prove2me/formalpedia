-- Prove2me | Definitions.Def_CombOpt_MatroidIntersection_contractIndep
-- name    : CombOpt_MatroidIntersection_contractIndep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:49.960993+00:00
-- url     : https://prove2.me/theorems/cbcea109-ce4d-4854-ad17-57be701e218f
-- title:
--   Independent sets of the contraction $M/B$
-- statement:
--   Let $M=(S,\mathcal I)$ be a matroid, $B\subseteq S$, and $J$ a basis of $B$. The **contraction** $M'=M/B$ has ground set $S'=S\setminus B$ and independent sets
--   $$\mathcal I'=\{J'\subseteq S' : J'\cup J\in\mathcal I\}.$$
--
--   For the forest matroid of a graph, contracting an edge $e$ gives the forest matroid of the graph with $e$ contracted. Theorem 8.11 shows that $M'$ is a matroid that does not depend on the choice of $J$.
--
--   **Formalization Note** $S'$ is the subtype `{x : S // x ∉ B}`; a subset $J'$ of $S'$ is mapped into $S$ before the union with $J$. The definition takes $J$ as a parameter; the theorems assume it is a basis of $B$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.2, p. 285 (PDF p. 292)

import Mathlib

namespace CombOpt.MatroidIntersection

/-- **The independent sets of the contraction `M / B`, built from a basis `J` of `B`.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.2,
p. 285 (PDF p. 292): "Let M = (S, I) be a matroid and B ⊆ S. Choose a basis J of B and define
M′ = (S′, I′) by S′ = S\B and I′ = {J′ ⊆ S′ : J′ ∪ J ∈ I}."

For a family `Indep` of subsets of `S`, a set `B` and a set `J` (in the book a basis of `B`),
`contractIndep Indep B J` is the family of subsets `J′` of the new ground set
`S′ = S \ B` (the subtype `{x : S // x ∉ B}`) such that `J′ ∪ J` is independent.

**Formalization Note.** A subset of `S′` is a `Finset {x : S // x ∉ B}`; it is mapped back into
`S` by the subtype embedding before taking the union with `J`. The definition does not itself
require `J` to be a basis of `B`; Theorem 8.11 assumes it. -/
def contractIndep {S : Type*} [DecidableEq S] (Indep : Finset S → Prop) (B J : Finset S) :
    Finset {x : S // x ∉ B} → Prop :=
  fun J' => Indep (J'.map (Function.Embedding.subtype _) ∪ J)

end CombOpt.MatroidIntersection


