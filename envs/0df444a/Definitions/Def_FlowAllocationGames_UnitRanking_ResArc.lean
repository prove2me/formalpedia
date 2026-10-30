-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_ResArc
-- name    : FlowAllocationGames_UnitRanking_ResArc
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:25:51.006361+00:00
-- url     : https://prove2.me/theorems/6184ad14-d053-44a2-8ef9-a8b840333a1d
-- title:
--   Arc of a residual network
-- statement:
--   An arc of a residual network: a start node, an end node, a cost per unit of flow, the index of the underlying edge of $G'$, and whether it is the forward arc (more flow on the edge) or the backward arc (less flow on the edge).
--
--   This is part of the witness algorithm of the mission: the paper computes the optimal circulation $f^*$ by citing Tardos [45] and fixes no algorithm.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, proof of Theorem 9, p. 23

import Mathlib

namespace FlowAllocationGames.UnitRanking

/-- **Arc of a residual network.**
Witness algorithm of the mission for "f∗ can be computed in strongly polynomial time [45]" in
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, proof of Theorem 9,
p. 23.

A residual arc goes from `src` to `dst`, has cost `cost`, and belongs to edge `edge` of the
network: it is the forward arc of that edge (`fwd = true`, more flow on the edge) or its backward
arc (`fwd = false`, less flow on the edge). -/
structure ResArc where
  /-- Start node. -/
  src : ℕ
  /-- End node. -/
  dst : ℕ
  /-- Cost per unit of flow. -/
  cost : ℤ
  /-- Index of the underlying edge. -/
  edge : ℕ
  /-- Forward (`true`) or backward (`false`) arc. -/
  fwd : Bool
deriving Inhabited

end FlowAllocationGames.UnitRanking


