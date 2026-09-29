-- Prove2me | Definitions.Def_BertsekasSPGraph
-- name    : BertsekasSPGraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-06T05:05:02.863713+00:00
-- url     : https://prove2.me/theorems/6e147034-8614-42e3-8af7-58e566a93ee3
-- title:
--   Shortest path graphs, walks, and distances
-- statement:
--   This module fixes the shortest path setting of Bertsekas, Vol. I, §2.3, and the notions of walk, walk length and distance built on it.
--
--   **The graph.** A finite directed graph is given by a set of arcs $\mathcal{A}$ of ordered node pairs, a length $a_{ij} \in \mathbb{R}$ attached to each pair, an origin $s$ and a destination $t$ with $s \ne t$.
--
--   **Walks.** A list of nodes $(v_0, v_1, \dots, v_r)$ is a walk from $a$ to $b$ when it is nonempty, $v_0 = a$, $v_r = b$, and every consecutive pair is an arc, $(v_{m}, v_{m+1}) \in \mathcal{A}$. Nodes may repeat, so walks include cyclic traversals; the one-element list $(a)$ is a walk from $a$ to itself.
--
--   **Length and distance.** The length of a walk is the sum of the lengths of its arcs,
--
--   $$\ell(v_0, \dots, v_r) \;=\; \sum_{m=0}^{r-1} a_{v_m v_{m+1}},$$
--
--   so a one-element walk has length $0$. The distance from $a$ to $b$ is the infimum of the lengths of all walks from $a$ to $b$, taken in the extended reals:
--
--   $$\operatorname{dist}(a,b) \;=\; \inf\bigl\{\, \ell(l) \;:\; l \text{ a walk from } a \text{ to } b \,\bigr\} \;\in\; \overline{\mathbb{R}}.$$
--
--   These are the objects against which any shortest path algorithm must be judged; the label correcting method of §2.3.1 is proved correct by comparing its output with $\operatorname{dist}(s,t)$.
--
--   **Formalization Note** The node type is finite with decidable equality. Lengths are total on all node pairs, but only the values at arcs ever enter a walk length. Distance is an `EReal`: when no walk from $a$ to $b$ exists the infimum is over an empty family and equals $+\infty$, which is the honest reading of "unreachable" rather than a sentinel value; if walk lengths are unbounded below (possible only with a negative cycle) it is $-\infty$.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Section 2.3

import Mathlib

/-- The shortest path setting of Bertsekas, "Dynamic Programming and Optimal
Control", Vol. I, 3rd ed., Section 2.3: a finite directed graph with arc set
`arcs`, arc lengths `length`, an origin node `s` and a destination node `t`. -/
structure BertsekasSPGraph (V : Type) [Fintype V] [DecidableEq V] where
  arcs : Finset (V × V)
  length : V → V → ℝ
  s : V
  t : V
  hst : s ≠ t

/-- `BertsekasIsWalkFrom G a b l` says the list of nodes `l` is a path
(a forward walk) in the graph `G` from node `a` to node `b`: it is nonempty,
consecutive nodes are joined by arcs of `G`, it starts at `a` and ends at `b`. -/
def BertsekasIsWalkFrom {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasSPGraph V) (a b : V) (l : List V) : Prop :=
  l ≠ [] ∧ List.IsChain (fun x y => (x, y) ∈ G.arcs) l ∧
    l.head? = some a ∧ l.getLast? = some b

/-- The length of a walk, i.e. the sum of the lengths of its consecutive arcs. -/
def BertsekasWalkLength {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasSPGraph V) (l : List V) : ℝ :=
  ((l.zip l.tail).map fun p => G.length p.1 p.2).sum

/-- The shortest distance from `a` to `b` in `G`, as an extended real number:
the infimum of the lengths of all walks from `a` to `b` (`⊤` if none exists). -/
noncomputable def BertsekasShortestDistance {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasSPGraph V) (a b : V) : EReal :=
  ⨅ l : {l : List V // BertsekasIsWalkFrom G a b l}, (BertsekasWalkLength G l.1 : EReal)


