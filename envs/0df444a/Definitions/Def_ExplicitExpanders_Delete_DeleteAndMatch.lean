-- Prove2me | Definitions.Def_ExplicitExpanders_Delete_DeleteAndMatch
-- name    : ExplicitExpanders_Delete_DeleteAndMatch
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T06:56:05.132249+00:00
-- url     : https://prove2.me/theorems/1b13939c-8c70-4629-bb84-82aac6175b3d
-- title:
--   Omitting a vertex set $U$ and adding a matching on $N(U)$ (proof of Theorem 1.3)
-- statement:
--   Let $H$ be a finite simple graph on $V$ and $U \subseteq V$.
--
--   1. $N(U) = \{x \in V : x \text{ is adjacent in } H \text{ to some } z \in U\}$ is the set of neighbours of $U$.
--   2. A map $m : V \to V$ is a **perfect matching on a set $S$** if for every $x \in S$: $m(x)\in S$, $m(m(x)) = x$ and $m(x) \ne x$. The matching edges are the pairs $\{x, m(x)\}$, $x\in S$.
--   3. $H' = H - U$ is the subgraph of $H$ induced on $V\setminus U$.
--   4. $M$ is the graph on $V\setminus U$ whose edges are the pairs $\{x, m(x)\}$ with $x \in N(U)$ (and both endpoints outside $U$).
--   5. The **resulting graph** is $G = H' \cup M$ on the vertex set $V\setminus U$: two vertices of $V \setminus U$ are adjacent in $G$ if they are adjacent in $H$, or if one is $m$ of the other and lies in $N(U)$.
--
--   This is the construction in the proof of Theorem 1.3 (pp. 12–13): "Omit these vertices from the graph to get a graph $H'$ and add a matching $M$ between their neighbors retaining the degree of regularity $d$. Let $G$ denote the resulting graph." When $N(U)$ is disjoint from $U$, $M$ is a perfect matching on $N(U)$, and when moreover no matching pair is an edge of $H$, $A_G = A_{H'} + A_M$. Under the conclusions of Lemma 3.1 both facts hold; they are stated as theorems, not built into the definition.
--
--   **Formalization Note** The vertex type of $H'$, $M$ and $G$ is the subtype `Kept U = {v // v ∉ U}`. $H'$ is `H.comap Subtype.val` (the induced subgraph), $M$ is `SimpleGraph.fromRel` of the relation "$x\in N(U)$ and $y = m(x)$", which symmetrises it and removes loops, and $G = H' \sqcup M$. The matching is a fixed-point-free involution of $N(U)$; its values outside $N(U)$ play no role.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, pp. 12–13, proof of Theorem 1.3 (the graphs H′, M and G)

import Mathlib

namespace ExplicitExpanders.Delete

/-- `N(U)`: the vertices adjacent (in `H`) to some vertex of `U`. -/
def nbrSet {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (U : Finset V) :
    Finset V :=
  Finset.univ.filter fun x => ∃ z ∈ U, H.Adj z x

/-- `m` is a perfect matching on the set `S`, given as a fixed-point-free involution of `S`:
it maps `S` to `S`, `m (m x) = x` and `m x ≠ x` for every `x ∈ S`; the matching edges are the
pairs `{x, m x}`. -/
def IsMatchingOn {V : Type*} (S : Finset V) (m : V → V) : Prop :=
  ∀ x ∈ S, m x ∈ S ∧ m (m x) = x ∧ m x ≠ x

/-- The vertex set `V ∖ U` of the graph obtained by omitting `U`. -/
abbrev Kept {V : Type*} (U : Finset V) : Type _ := {v : V // v ∉ U}

/-- `H'`: the subgraph of `H` induced on `V ∖ U` (omit the vertices of `U`). -/
def deleted {V : Type*} (H : SimpleGraph V) (U : Finset V) : SimpleGraph (Kept U) :=
  H.comap Subtype.val

/-- `M`: the graph on `V ∖ U` whose edges are the pairs `{x, m x}` with `x ∈ N(U)`. -/
def matchGraph {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (U : Finset V)
    (m : V → V) : SimpleGraph (Kept U) :=
  SimpleGraph.fromRel fun x y => x.1 ∈ nbrSet H U ∧ y.1 = m x.1

/-- `G = H' + M` (Alon, arXiv:2003.11673v1, proof of Theorem 1.3, pp. 12–13): omit the vertices of
`U` from `H` and add the matching `m` between their neighbours. -/
def deleteAndMatch {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (m : V → V) : SimpleGraph (Kept U) :=
  deleted H U ⊔ matchGraph H U m

end ExplicitExpanders.Delete


