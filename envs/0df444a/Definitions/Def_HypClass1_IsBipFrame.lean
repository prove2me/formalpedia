-- Prove2me | Definitions.Def_HypClass1_IsBipFrame
-- name    : HypClass1_IsBipFrame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:19:47.095538+00:00
-- url     : https://prove2.me/theorems/e35bbf3b-35dc-4e79-9e8d-b52c88ac8f70
-- title:
--   Bipartite structure $\Xi = (X,Y,Z,M,E)$: the frame $(X,Y,Z,M)$
-- statement:
--   Let $n \in 3\mathbb Z$. A **bipartite structure** $\Xi = (X, Y, Z, M, E)$ on $[n]$ is an ordered quintuple where $[n] = X \cup Y \cup Z$ is an equipartition with $|X| = |Y| = |Z| = n/3$, $M$ is a perfect matching from $X$ to $Y$, and
--   $$
--   E \subseteq M \times Z := \{\{x, y, z\} : \{x, y\} \in M,\ z \in Z\}
--   $$
--   is a 3-graph. This item defines the frame $(X, Y, Z, M)$ (the predicate that it is an equipartition with a perfect matching) and the triple set $M \times Z$; the 3-graph $E$ is the random part of Definition 5.1.
--
--   **Formalization Note** $X, Y, Z$ are labelled; $M$ is a set of pairs $\{x, y\}$, $x \in X$, $y \in Y$, covering each vertex of $X \cup Y$ exactly once.
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §5 p.11

import Mathlib

namespace HypClass1

/-- The data `(X, Y, Z, M)` of a bipartite structure, written as a tuple
`(X, Y, Z, M) : Finset V × Finset V × Finset V × Finset (Finset V)`. -/
abbrev BipFrame (V : Type*) := Finset V × Finset V × Finset V × Finset (Finset V)

/-- `M × Z := {{x, y, z} : {x, y} ∈ M, z ∈ Z}`, the triples compatible with a matching `M` and a set `Z`.
Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §5 p.11. -/
def structTriples {V : Type*} [DecidableEq V] (M : Finset (Finset V)) (Z : Finset V) :
    Finset (Finset V) :=
  (M ×ˢ Z).image (fun mz => insert mz.2 mz.1)

/-- **Frame of a bipartite structure** on the vertex set `V`. Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §5 p.11: "Given any integer
n ∈ 3Z, we define a bipartite structure Ξ = (X, Y, Z, M, E) as an ordered quintuplet where
[n] = X ∪ Y ∪ Z is an equipartition of the vertex set [n] with |X| = |Y| = |Z| = n/3, M ⊆ X × Y is a
perfect matching from X to Y and E ⊆ M × Z := {{x, y, z} : {x, y} ∈ M, z ∈ Z} is a 3-graph."

`IsBipFrame (X, Y, Z, M)` says that `X, Y, Z` are pairwise disjoint with union `V`, each of size
`|V|/3`, and that `M` is a perfect matching from `X` to `Y`: every member of `M` is a pair `{x, y}` with
`x ∈ X`, `y ∈ Y`, and every vertex of `X` and of `Y` lies in exactly one member of `M`. The third
part of the paper's quintuplet, `E ⊆ M × Z`, is carried separately (`bipStructProb`).

**Formalization Note.** `X, Y, Z` are labelled (an ordered quintuplet). -/
def IsBipFrame {V : Type*} [Fintype V] [DecidableEq V] (s : BipFrame V) : Prop :=
  s.1 ∪ s.2.1 ∪ s.2.2.1 = Finset.univ ∧
  Disjoint s.1 s.2.1 ∧ Disjoint s.1 s.2.2.1 ∧ Disjoint s.2.1 s.2.2.1 ∧
  3 * s.1.card = Fintype.card V ∧ 3 * s.2.1.card = Fintype.card V ∧
  3 * s.2.2.1.card = Fintype.card V ∧
  (∀ m ∈ s.2.2.2, ∃ x ∈ s.1, ∃ y ∈ s.2.1, m = {x, y}) ∧
  (∀ x ∈ s.1, ∃! m, m ∈ s.2.2.2 ∧ x ∈ m) ∧
  (∀ y ∈ s.2.1, ∃! m, m ∈ s.2.2.2 ∧ y ∈ m)

end HypClass1


