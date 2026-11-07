-- Prove2me | Definitions.Def_ForestBackdoorFPT_IsDegenerate
-- name    : ForestBackdoorFPT_IsDegenerate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:29:32.126192+00:00
-- url     : https://prove2.me/theorems/cb62d8c2-9f00-485d-bdef-51285f33f5ff
-- title:
--   $d$-degenerate graphs and the degeneracy
-- statement:
--   For an integer $d\ge0$, a graph $G$ is **$d$-degenerate** if every nonempty subgraph of $G$ contains a vertex of degree at most $d$. The **degeneracy** of $G$ is the smallest such $d$.
--
--   Lemma 4.2 shows that yes-instances have incidence graphs of degeneracy at most $3^k+k$, and the algorithm of Theorem 4.1 is parameterized by the degeneracy.
--
--   **Formalization Note** The condition is stated for vertex sets: every nonempty set $S$ of vertices contains a vertex with at most $d$ neighbours in $S$. This is equivalent, since a subgraph on $S$ has degrees at most those in the induced subgraph $G[S]$, which is itself a subgraph. The degeneracy is the infimum of a set of natural numbers that is nonempty for every finite graph ($G$ is $|V(G)|$-degenerate).
-- source:
--   Bilyk–Munduzbaev–Sharma–Siam, Strong Backdoor to Forests is FPT: Tight Linear-Time FPT for Essentially General SAT, STOC 2027 submission (manuscript sha256 7fd1a7a8…), §2, p.5 (PDF p.6)

import Mathlib

set_option autoImplicit false

namespace ForestBackdoorFPT

open Classical in
/-- **d-degenerate graph** (Bilyk–Munduzbaev–Sharma–Siam, *Strong Backdoor to Forests is FPT*,
STOC 2027 submission (manuscript sha256 7fd1a7a8…), §2, p.5 (PDF p.6)): "For an integer d ≥ 0, a
graph G is d-degenerate if every nonempty subgraph of G contains a vertex of degree at most d."

**Formalization Note** Stated for induced subgraphs: every nonempty vertex set `S` contains a
vertex with at most `d` neighbours inside `S`. This is equivalent to the paper's wording, since a
subgraph on `S` has degrees at most those of the induced subgraph `G[S]`, and `G[S]` is itself a
subgraph. -/
def IsDegenerate {W : Type*} (G : SimpleGraph W) (d : ℕ) : Prop :=
  ∀ S : Finset W, S.Nonempty → ∃ v ∈ S, (S.filter (G.Adj v)).card ≤ d

/-- The **degeneracy** of `G` (p.5): "the smallest such integer d".

**Formalization Note** `sInf` on `ℕ`. For a finite vertex type the set is nonempty (`G` is
`|V(G)|`-degenerate), so `sInf` is its least element; the junk value `0` of `sInf ∅` never occurs
for the finite graphs this mission uses. -/
noncomputable def degeneracy {W : Type*} (G : SimpleGraph W) : ℕ :=
  sInf {d : ℕ | IsDegenerate G d}

end ForestBackdoorFPT


