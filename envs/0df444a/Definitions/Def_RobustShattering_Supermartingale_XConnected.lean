-- Prove2me | Definitions.Def_RobustShattering_Supermartingale_XConnected
-- name    : RobustShattering_Supermartingale_XConnected
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:42:45.359444+00:00
-- url     : https://prove2.me/theorems/f0774a7d-4415-451d-94c6-23d067f5fcdd
-- title:
--   Definition 4.1 — x-connected vertex sets (connected in the power graph $G^x$)
-- statement:
--   Let $G=(V,E)$ be a simple graph and $x\ge 0$ an integer. The **power graph** $G^x$ has vertex set $V$ and an edge between distinct vertices $u,v$ exactly when $\mathrm{dist}_G(u,v)\le x$, where $\mathrm{dist}_G$ is the graph distance in $G$ (equal to $+\infty$ between different connected components). A set $S\subseteq V$ is **$x$-connected** if the subgraph $G^x[S]$ of $G^x$ induced on $S$ is connected. Distances are always measured in $G$, not in $G[S]$.
--
--   The companion notion of Definition 4.1, **$a$-independence** (the vertices of $S$ are pairwise at distance greater than $a$ in $G$, i.e. $S$ is independent in $G^a$), is the published predicate `LocalLLL.Main.separated G a S`, and $G^x$ is the published `LocalLLL.Main.graphPower G x`; both are reused unchanged.
--
--   **Formalization Note.** `XConnected G x S` is `((graphPower G x).induce S).Connected`. Mathlib's `Connected` includes nonemptiness, so the empty set is not $x$-connected; every statement of this mission only concerns $x$-connected sets of size at least $1$, where this changes nothing. For $x=0$ the graph $G^0$ has no edges, so the $0$-connected sets are exactly the singletons.
-- source:
--   Davies-Peck, Ghaffari, Halldórsson, Maus, Nolin, Robust Shattering Arguments, arXiv:2606.27847 (held manuscript, sha256 21726e7f…8128), p. 9, §2.7; p. 12, Definition 4.1

import Mathlib
import Definitions.Def_LocalLLL_Main_GraphModel

namespace RobustShattering.Supermartingale

/-!
# x-connected sets (Definition 4.1, §2.7)

Davies-Peck, Ghaffari, Halldórsson, Maus, Nolin, *Robust Shattering Arguments*,
arXiv:2606.27847 (held manuscript, sha256 21726e7f…8128), p. 9 (§2.7) and p. 12, Definition 4.1.

For an integer `x ≥ 0`, the power graph `G^x` is `LocalLLL.Main.graphPower G x` (distinct
vertices at graph distance at most `x` in `G`). A set `S` of vertices is `x`-connected when the
subgraph of `G^x` induced on `S` is connected. Mathlib's `SimpleGraph.Connected` requires a
nonempty vertex type, so the empty set is not `x`-connected. The companion notion
"`a`-independent" is `LocalLLL.Main.separated G a S`, reused unchanged.
-/

/-- `S` is `x`-connected in `G`: the subgraph of the power graph `G^x` induced on `S` is
connected (Definition 4.1; distances are measured in `G`). -/
def XConnected {V : Type} (G : SimpleGraph V) (x : ℕ) (S : Set V) : Prop :=
  ((LocalLLL.Main.graphPower G x).induce S).Connected

end RobustShattering.Supermartingale


