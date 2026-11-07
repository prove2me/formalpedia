-- Prove2me | Definitions.Def_ForestBackdoorFPT_RawGraph
-- name    : ForestBackdoorFPT_RawGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:29:35.457309+00:00
-- url     : https://prove2.me/theorems/cb9bc12b-d078-49cc-bca3-57d1747e61f6
-- title:
--   Edge-list encodings of graphs
-- statement:
--   A graph on the vertex set $\{0,\dots,n-1\}$ is given to a program as the words $n,m,u_1,v_1,\dots,u_m,v_m$, its edge list. The encoding is **valid** if no edge is a loop and no edge is listed twice (in either orientation); the graph is then the simple graph with exactly the listed edges.
--
--   This is the input of the graph algorithms used by the paper: the degeneracy ordering of Matula and Beck and the $K_{2,2}$ search of Lemma 4.9.
-- source:
--   Bilyk–Munduzbaev–Sharma–Siam, Strong Backdoor to Forests is FPT: Tight Linear-Time FPT for Essentially General SAT, STOC 2027 submission (manuscript sha256 7fd1a7a8…), §2, p.6 (PDF p.7); Lemma 4.9, p.20 (PDF p.21)

import Mathlib

set_option autoImplicit false

namespace ForestBackdoorFPT

/-- A **list encoding of a graph** on the vertex set `Fin n` (Bilyk–Munduzbaev–Sharma–Siam, *Strong
Backdoor to Forests is FPT*, STOC 2027 submission (manuscript sha256 7fd1a7a8…), §2, p.6 (PDF p.7):
"graph vertices are represented by integer indices. Graphs … are stored using adjacency … lists"):
an edge list. Used for the graph algorithms of [MB83] and Lemma 4.9 (p.20). -/
structure RawGraph where
  /-- the number of vertices -/
  n : ℕ
  /-- the edges, each listed once in one orientation -/
  edges : List (Fin n × Fin n)

namespace RawGraph

/-- Validity: no loops and no edge listed twice (in either orientation). -/
def Valid (R : RawGraph) : Prop :=
  (∀ e ∈ R.edges, e.1 ≠ e.2) ∧ (R.edges.map (fun e => Sym2.mk e)).Nodup

/-- The word encoding `n, m, u₁, v₁, …, u_m, v_m`. -/
def encode (R : RawGraph) : List ℕ :=
  [R.n, R.edges.length] ++ R.edges.flatMap (fun e => [e.1.val, e.2.val])

/-- The simple graph on `Fin n` with the listed edges. -/
def toGraph (R : RawGraph) : SimpleGraph (Fin R.n) :=
  SimpleGraph.fromRel (fun u v => (u, v) ∈ R.edges)

end RawGraph

end ForestBackdoorFPT


