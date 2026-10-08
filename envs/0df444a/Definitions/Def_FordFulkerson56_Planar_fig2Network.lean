-- Prove2me | Definitions.Def_FordFulkerson56_Planar_fig2Network
-- name    : FordFulkerson56_Planar_fig2Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:26:00.633523+00:00
-- url     : https://prove2.me/theorems/5a5593de-acdb-4648-bb99-0b220e136f36
-- title:
--   The network of Fig. 2: the "gas, water, electricity" graph K₃,₃ with arc ab removed
-- statement:
--   The network of Fig. 2 of Ford and Fulkerson is the "gas, water, electricity" graph $K_{3,3}$ with the arc $ab$ removed. It has six vertices: the source $a$, the sink $b$, and four further vertices, labelled here by their position in the figure: $p$ (top left), $q$ (top right), $r$ (bottom left) and $s$ (middle right). Its eight arcs are
--   $$ar,\ as,\ pr,\ ps,\ pb,\ qb,\ qr,\ qs,$$
--   i.e. every arc between $\{a,p,q\}$ and $\{b,r,s\}$ except $ab$. Every capacity is $1$.
--
--   The paper uses this network to show that Theorem 2 fails without ab-planarity.
--
--   **Formalization Note** Vertices are `Fin 6` with $a=0$, $b=1$, $p=2$, $q=3$, $r=4$, $s=5$; arcs $0,\dots,7$ are listed in the order above. The figure shows no capacities; the paper's claim about this network concerns chains and cuts only and does not depend on them.
-- source:
--   Ford & Fulkerson, Maximal Flow Through a Network, Canad. J. Math. 8 (1956), p. 403, Fig. 2

import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network

namespace FordFulkerson56.Planar

/-- The network of Fig. 2 (Ford–Fulkerson, p. 403): the "gas, water, electricity" graph `K₃,₃` with
the arc `ab` removed. Vertices: `0 = a` (source), `1 = b` (sink), `2` top-left, `3` top-right,
`4` bottom-left, `5` middle-right. Arcs `0 … 7` join `0–4, 0–5, 2–4, 2–5, 2–1, 3–1, 3–4, 3–5`.
Every capacity is `1` (the figure shows none; the paper's claim about it involves no capacities). -/
def fig2Network : FordFulkerson56.MinCut.Network (Fin 6) (Fin 8) where
  tail := ![0, 0, 2, 2, 2, 3, 3, 3]
  head := ![4, 5, 4, 5, 1, 1, 4, 5]
  tail_ne_head := by decide
  source := 0
  sink := 1
  source_ne_sink := by decide
  cap := fun _ => 1
  cap_pos := fun _ => one_pos

end FordFulkerson56.Planar


