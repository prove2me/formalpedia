-- Prove2me | Definitions.Def_FordFulkerson58_ArcChain_fig1Network
-- name    : FordFulkerson58_ArcChain_fig1Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:15:34.803332+00:00
-- url     : https://prove2.me/theorems/12272561-a393-4ef6-a210-b07c2531f740
-- title:
--   Figure 1, p. 1779 — the four-node network with sources P₁, P₂, sink P₃ (commodity 1) and source P₄, sink P₁ (commodity 2)
-- statement:
--   The network of Figure 1 has four nodes $P_1, P_2, P_3, P_4$ and six undirected arcs
--   $$A_1 = P_1P_2,\ A_2 = P_2P_3,\ A_3 = P_1P_3,\ A_4 = P_1P_4,\ A_5 = P_2P_4,\ A_6 = P_3P_4.$$
--   Commodity 1 has sources $P_1, P_2$ and sink $P_3$; commodity 2 has source $P_4$ and sink $P_1$ (§2, p. 1778). Every capacity is set to $1$.
--
--   It is the example whose incidence matrix the paper displays in Figure 2.
--
--   **Formalization Note** Indices are 0-based: $P_i \mapsto i-1$, $A_r \mapsto r-1$, commodity $1 \mapsto 0$, $2 \mapsto 1$. The figure gives no capacities, and the claim about it does not involve them.
-- source:
--   Ford and Fulkerson, A suggested computation for maximal multi-commodity network flows, Management Sci. 50(12S) (2004), p. 1779, Figure 1, with the commodities of §2, p. 1778

import Mathlib
import Definitions.Def_FordFulkerson58_ArcChain_Network

namespace FordFulkerson58.ArcChain

/-- The network of Figure 1 (p. 1779) with the two commodities of §2 (p. 1778), indices 0-based
(`P_i ↦ i − 1`, `A_r ↦ r − 1`, commodity `1 ↦ 0`, `2 ↦ 1`). Arcs, all undirected:
`A₁ = P₁P₂`, `A₂ = P₂P₃`, `A₃ = P₁P₃`, `A₄ = P₁P₄`, `A₅ = P₂P₄`, `A₆ = P₃P₄`. Commodity 1 has
sources `P₁, P₂` and sink `P₃`; commodity 2 has source `P₄` and sink `P₁`. Every capacity is `1`
(the figure gives none; the claim about it does not involve capacities). -/
def fig1Network : Network (Fin 4) (Fin 6) (Fin 2) where
  tail := ![0, 1, 0, 0, 1, 2]
  head := ![1, 2, 2, 3, 3, 3]
  directed := fun _ => false
  b := fun _ => 1
  src := ![{0, 1}, {3}]
  snk := ![{2}, {0}]

end FordFulkerson58.ArcChain


