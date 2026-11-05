-- Prove2me | Definitions.Def_OmniThreshold_fulfillmentNetwork
-- name    : OmniThreshold_fulfillmentNetwork
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:34:39.507988+00:00
-- url     : https://prove2.me/theorems/dcfcbc0f-2552-4145-99f5-b4f0884bb01c
-- title:
--   The bipartite fulfillment network of LP (2)
-- statement:
--   Fix $n$ locations, cancellation costs $c_i$, unit shipping costs $s_{ji}$ from location $j$ to location $i$, unsold inventories $u_j\in\mathbb N$, and an integer $K$. The **fulfillment network** has
--
--   1. an order node $o_i$ for every location $i$ (the sources),
--   2. a store node $r_j$ for every location $j$,
--   3. one cancellation node $\kappa$, and
--   4. one sink $t$,
--
--   and the arcs
--
--   1. $o_i\to r_j$ with cost $s_{ji}$ and capacity $K$ (an order at $i$ filled from the inventory at $j$),
--   2. $o_i\to\kappa$ with cost $c_i$ and capacity $K$ (an order at $i$ cancelled),
--   3. $r_j\to t$ with cost $0$ and capacity $u_j$ (the unsold inventory at $j$),
--   4. $\kappa\to t$ with cost $0$ and capacity $K$.
--
--   This is the bipartite network in which the paper views LP (2) as a minimum-cost single-commodity flow problem, with supplies equal to the accepted orders at the order nodes.
--
--   **Formalization Note** The paper gives the cancellation arc "an unlimited capacity" and states no capacity on the arcs out of the order nodes. Since capacities are integers, these arcs carry the parameter $K$; any $K\ge\sum_i A_i^O$ never binds. Nodes are `Fin n ⊕ Fin n ⊕ Bool` (cancellation node `false`, sink `true`).
-- source:
--   Jia, Karp, Ravi & Tayur, Effective Online Order Acceptance Policies for Omni-Channel Fulfillment, SSRN 3932692, proof of Theorem 2, p.10

import Mathlib
import Definitions.Def_OmniThreshold_FlowNetwork

namespace OmniThreshold

/-- The **bipartite fulfillment network of LP (2)** (Jia, Karp, Ravi & Tayur, *Effective Online
Order Acceptance Policies for Omni-Channel Fulfillment*, SSRN 3932692, proof of Theorem 2, p.10:
"LP (2) may be viewed as a minimum cost, single-commodity flow problem in a bipartite network where
nodes corresponding to each location are on one side of the bipartition and have supplies equal to
the number of accepted orders at that location. Nodes corresponding to each location and a node
corresponding to cancellations are on the other side. In this second set, all nodes have arcs
directed to a sink node, and these arcs have capacities equal to the number of unsold units of
inventory at the corresponding location and an unlimited capacity on the arc between the
cancellation node and the sink.").

Nodes (`Fin n ⊕ Fin n ⊕ Bool`):
1. `Sum.inl i` — the order node of location `i` (a source);
2. `Sum.inr (Sum.inl j)` — the store node of location `j`;
3. `Sum.inr (Sum.inr false)` — the cancellation node;
4. `Sum.inr (Sum.inr true)` — the sink.

Arcs (`(Fin n × Fin n) ⊕ Fin n ⊕ Fin n ⊕ Unit`):
1. `Sum.inl (i, j)` — order node `i` → store node `j`, cost `s j i` (shipping from `j` to the
   customer at `i`), capacity `K`;
2. `Sum.inr (Sum.inl i)` — order node `i` → cancellation node, cost `c i`, capacity `K`;
3. `Sum.inr (Sum.inr (Sum.inl j))` — store node `j` → sink, cost `0`, capacity `u j` (the unsold
   inventory at `j`);
4. `Sum.inr (Sum.inr (Sum.inr ()))` — cancellation node → sink, cost `0`, capacity `K`.

**Formalization Note** Capacities are natural numbers (the integer capacities of Lemma 1). The
paper's "unlimited" capacity, on the cancellation arc and implicitly on the order-to-store and
order-to-cancellation arcs (the paper states no capacity there), is the parameter `K`; any
`K ≥ ∑_i A_i^O` never binds. -/
def fulfillmentNetwork {n : ℕ} (c : Fin n → ℝ) (s : Fin n → Fin n → ℝ) (u : Fin n → ℕ) (K : ℕ) :
    FlowNetwork (Fin n ⊕ Fin n ⊕ Bool) ((Fin n × Fin n) ⊕ Fin n ⊕ Fin n ⊕ Unit) where
  tail
    | Sum.inl (i, _) => Sum.inl i
    | Sum.inr (Sum.inl i) => Sum.inl i
    | Sum.inr (Sum.inr (Sum.inl j)) => Sum.inr (Sum.inl j)
    | Sum.inr (Sum.inr (Sum.inr _)) => Sum.inr (Sum.inr false)
  head
    | Sum.inl (_, j) => Sum.inr (Sum.inl j)
    | Sum.inr (Sum.inl _) => Sum.inr (Sum.inr false)
    | Sum.inr (Sum.inr (Sum.inl _)) => Sum.inr (Sum.inr true)
    | Sum.inr (Sum.inr (Sum.inr _)) => Sum.inr (Sum.inr true)
  cost
    | Sum.inl (i, j) => s j i
    | Sum.inr (Sum.inl i) => c i
    | Sum.inr (Sum.inr _) => 0
  cap
    | Sum.inl _ => K
    | Sum.inr (Sum.inl _) => K
    | Sum.inr (Sum.inr (Sum.inl j)) => u j
    | Sum.inr (Sum.inr (Sum.inr _)) => K

end OmniThreshold


