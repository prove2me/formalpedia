-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_Net
-- name    : FlowAllocationGames_UnitRanking_Net
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:24:38.806415+00:00
-- url     : https://prove2.me/theorems/33989f0e-640a-4962-b592-387780f6fbcc
-- title:
--   The circulation network in array form
-- statement:
--   A network with nodes $0, \dots, N-1$ whose edges are listed by their tails, heads and integer capacities. It is the data structure on which the witness algorithm computes an optimal circulation of $G'$.
--
--   This is part of the witness algorithm of the mission: the paper computes the optimal circulation $f^*$ by citing Tardos [45] and fixes no algorithm.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, §3.1, p. 17; proof of Theorem 9, p. 23

import Mathlib

namespace FlowAllocationGames.UnitRanking

/-- **The circulation network `G′` in array form.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, §3.1, p. 17
(the circulation network `G′`). Data structure of the witness algorithm of the mission (the paper
cites [45] for the computation of `f∗`, p. 23).

A network with nodes `0, …, N - 1` and edges `j` listed by their tails `tl[j]`, heads `hd[j]` and
integer capacities `cap[j]`. -/
structure Net where
  /-- Number of nodes. -/
  N : ℕ
  /-- Tail of each edge. -/
  tl : Array ℕ
  /-- Head of each edge. -/
  hd : Array ℕ
  /-- Capacity of each edge. -/
  cap : Array ℤ

end FlowAllocationGames.UnitRanking


