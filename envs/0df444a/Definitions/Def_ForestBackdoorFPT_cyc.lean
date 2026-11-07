-- Prove2me | Definitions.Def_ForestBackdoorFPT_cyc
-- name    : ForestBackdoorFPT_cyc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:29:33.696085+00:00
-- url     : https://prove2.me/theorems/b4aeccf3-ac74-4e07-83da-6df91ccc62b6
-- title:
--   Cyclomatic number $\mathrm{cyc}(G)$
-- statement:
--   For a graph $G$ with connected components $\mathrm{cc}(G)$, the **cyclomatic number** is
--
--   $$
--   \mathrm{cyc}(G) \;=\; |E(G)| - |V(G)| + |\mathrm{cc}(G)|.
--   $$
--
--   It is the minimum number of edges whose deletion makes $G$ a forest; in particular $\mathrm{cyc}(G)=0$ if and only if $G$ is a forest. Lemmas 4.7 and 4.8 split the $K_{2,2}$-free case according to its size.
--
--   **Formalization Note** Computed as an integer, so there is no truncated subtraction. The vertex count and the component count are over the whole vertex type, isolated vertices included; an isolated vertex contributes $-1+1=0$.
-- source:
--   Bilyk–Munduzbaev–Sharma–Siam, Strong Backdoor to Forests is FPT: Tight Linear-Time FPT for Essentially General SAT, STOC 2027 submission (manuscript sha256 7fd1a7a8…), Definition 2.1, p.5 (PDF p.6)

import Mathlib

set_option autoImplicit false

namespace ForestBackdoorFPT

/-- The **cyclomatic number** (Bilyk–Munduzbaev–Sharma–Siam, *Strong Backdoor to Forests is FPT*,
STOC 2027 submission (manuscript sha256 7fd1a7a8…), Definition 2.1, p.5 (PDF p.6)):
`cyc(G) := |E(G)| − |V(G)| + |cc(G)|`, where `cc(G)` is the set of connected components.

**Formalization Note** Computed in `ℤ`, so there is no truncated subtraction. `|V(G)|` is the
cardinality of the whole vertex type and `cc(G)` counts the connected components of the whole type
(isolated vertices included), so an isolated vertex contributes `−1 + 1 = 0`. Cardinalities are
`Nat.card`/`Set.ncard`; every statement using `cyc` has a finite vertex type, where these are the
ordinary cardinalities. -/
noncomputable def cyc {W : Type*} (G : SimpleGraph W) : ℤ :=
  (G.edgeSet.ncard : ℤ) - (Nat.card W : ℤ) + (Nat.card G.ConnectedComponent : ℤ)

end ForestBackdoorFPT


