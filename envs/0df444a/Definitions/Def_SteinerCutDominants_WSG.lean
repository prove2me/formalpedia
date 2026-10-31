-- Prove2me | Definitions.Def_SteinerCutDominants_WSG
-- name    : SteinerCutDominants_WSG
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:14:20.611603+00:00
-- url     : https://prove2.me/theorems/a98fdcbf-4a4e-48ed-b93f-177800968c27
-- title:
--   Weighted Steiner graph
-- statement:
--   A **Steiner graph** $(G,T)$ is a connected graph $G$ with a subset $T\subseteq V(G)$ of $|T|\ge 2$ terminals. Graphs are finite and have no loops or multiple edges. A **weighted** Steiner graph carries in addition a vector $c$ of nonnegative integer edge weights.
--
--   **Formalization Note** The structure bundles a finite vertex type, a `SimpleGraph`, connectivity, $2\le|T|$, and $c:E(G)\to\mathbb N$. Positivity and minimum integer form of $c$ are not bundled; they are clauses of `IsFacetInducing`.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §1, p.1; §6, p.10

import Mathlib

namespace SteinerCutDominants

/-- A weighted Steiner graph `((G, T), c)` (Conforti, Kaibel, *Steiner Cut Dominants*,
arXiv:2209.14802v2, §1, p.1, and the "(weighted)" of §6, p.10): `G` is a connected finite simple
graph, `T ⊆ V(G)` has at least two terminals, and `c` is a vector of nonnegative integer edge
weights.

**Formalization Note** Connectivity and `2 ≤ |T|` are bundled, being part of the page's notion of a
Steiner graph. Graphs are simple ("we only consider graphs without loops or multiple edges", p.12).
Positivity of `c` and minimum integer form are not bundled: they belong to `IsFacetInducing`. -/
structure WSG where
  /-- The node set. -/
  V : Type
  [fintypeV : Fintype V]
  [decEqV : DecidableEq V]
  /-- The graph. -/
  G : SimpleGraph V
  [decAdj : DecidableRel G.Adj]
  /-- The terminals. -/
  T : Finset V
  /-- `G` is connected. -/
  conn : G.Connected
  /-- At least two terminals. -/
  two : 2 ≤ T.card
  /-- The edge weights. -/
  c : G.edgeSet → ℕ

attribute [instance] WSG.fintypeV WSG.decEqV WSG.decAdj

end SteinerCutDominants


