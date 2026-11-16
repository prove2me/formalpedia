-- Prove2me | Definitions.Def_SpreadMatchCircuit_Matching_Supplement_Cliques
-- name    : SpreadMatchCircuit_Matching_Supplement_Cliques
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:32:01.822714+00:00
-- url     : https://prove2.me/theorems/4bdbbb1c-9a73-4c19-8f56-5be40c6f6c2e
-- title:
--   Cliques $C_S$, clique containment, and the clique promise problem
-- statement:
--   Graphs are finite sets of edges on the vertex set $[n]$, as in the mission's graph vocabulary: an edge is an unordered pair of distinct vertices.
--
--   1. For a set of vertices $S\subseteq[n]$, the **clique** $C_S$ is the graph consisting of all edges both of whose endpoints lie in $S$:
--   $$C_S=\{\{u,v\} : u,v\in S,\ u\neq v\}.$$
--   When $|S|\le 1$, $C_S$ is the empty graph.
--   2. A graph $x$ **contains a clique of size $j$** if there is a set $S$ of exactly $j$ vertices with $C_S\subseteq x$. Its negation says that the clique number of $x$ is less than $j$.
--   3. A monotone circuit $C$ on the edge variables **distinguishes** graphs that contain a clique of size $k$ from graphs that have no clique of size $q$ if $C$ outputs $1$ on every graph that contains a clique of size $k$ and $0$ on every graph that contains no clique of size $q$. Its output on all remaining graphs is unconstrained.
--
--   These notions state the clique lower bound (Theorem 8) and the Spread Clique Lemma (Lemma 4).
--
--   **Formalization Note** A circuit reads the graph $x$ through its edge-indicator assignment, the published `graphInput`. No bipartiteness is imposed. The promise quantifies over all graphs on $[n]$.
-- source:
--   Anup Rao, STOC 2027 submission #299 (October 2026), p. 4 (§1.1: "For a set S, let C_S denote the clique on the vertices of S"), p. 5 (Theorem 8: distinguishing graphs that contain a clique of size k from graphs that have no clique of size q)

import Mathlib
import Definitions.Def_SpreadMatchCircuit_Matching_Graphs
import Definitions.Def_SpreadMatchCircuit_Matching_MonotoneCircuit
import Definitions.Def_SpreadMatchCircuit_Matching_Promise

namespace SpreadMatchCircuit.Matching.Supplement

open Finset

variable {n : ℕ}

/-- `C_S`: the clique on the vertex set `S`, i.e. every edge both of whose endpoints lie in `S`.
For `|S| ≤ 1` it is the empty graph. -/
def cliqueEdges (S : Finset (Fin n)) : Finset (Edge n) :=
  univ.filter fun e => endpoints e ⊆ S

/-- The graph `x` contains a clique of size `j`: some set `S` of exactly `j` vertices has
`C_S ⊆ x`. Its negation says that the clique number of `x` is less than `j`. -/
def HasCliqueOfSize (x : Finset (Edge n)) (j : ℕ) : Prop :=
  ∃ S : Finset (Fin n), S.card = j ∧ cliqueEdges S ⊆ x

/-- `C` distinguishes `n`-vertex graphs containing a clique of size `k` from graphs with no clique
of size `q`: it outputs `1` on every graph of the former kind and `0` on every graph of the latter
kind. Its behaviour on all other graphs is unconstrained. -/
def DistinguishesCliques (C : MonotoneCircuit (Edge n)) (k q : ℕ) : Prop :=
  ∀ x : Finset (Edge n),
    (HasCliqueOfSize x k → C.eval (graphInput x) = true) ∧
    (¬ HasCliqueOfSize x q → C.eval (graphInput x) = false)

end SpreadMatchCircuit.Matching.Supplement


