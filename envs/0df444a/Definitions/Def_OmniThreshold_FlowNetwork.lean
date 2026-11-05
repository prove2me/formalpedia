-- Prove2me | Definitions.Def_OmniThreshold_FlowNetwork
-- name    : OmniThreshold_FlowNetwork
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:33:56.880091+00:00
-- url     : https://prove2.me/theorems/dde235a2-4d28-4108-908a-517643473ad1
-- title:
--   A capacitated network with arc costs
-- statement:
--   A **flow network** consists of a node set $V$, an arc set $E$, and for every arc $e\in E$ a tail $\mathrm{tail}(e)\in V$, a head $\mathrm{head}(e)\in V$, a unit cost $w_e\in\mathbb R$ (of any sign) and an integer capacity $u_e\in\mathbb N$.
--
--   This is the network of Lemma 1, a minimum-cost single-commodity flow problem with integer capacities; the mission uses it both for the general Lemma 1 and for the bipartite fulfillment network of LP (2).
--
--   **Formalization Note** A paper arc with "unlimited" capacity is represented by an integer capacity at least the total supply, which no feasible flow can exceed.
-- source:
--   Jia, Karp, Ravi & Tayur, Effective Online Order Acceptance Policies for Omni-Channel Fulfillment, SSRN 3932692, Lemma 1, p.9

import Mathlib

namespace OmniThreshold

/-- A **capacitated network with arc costs** (Jia, Karp, Ravi & Tayur, *Effective Online Order
Acceptance Policies for Omni-Channel Fulfillment*, SSRN 3932692, Lemma 1, p.9: "a minimum-cost,
single-commodity flow problem with multiple sources, one sink, and integer supplies, demands, and
capacities").

The node set is `V` and the arc set `E`; the arc `e` runs from `tail e` to `head e`, carries the
unit cost `cost e` (any real sign) and the integer capacity `cap e`.

**Formalization Note** Capacities are natural numbers, the integer capacities of Lemma 1; an arc
with "unlimited" capacity in the paper is modelled by a capacity at least the total supply. -/
structure FlowNetwork (V E : Type*) where
  /-- The tail of an arc. -/
  tail : E → V
  /-- The head of an arc. -/
  head : E → V
  /-- The unit cost of an arc. -/
  cost : E → ℝ
  /-- The integer capacity of an arc. -/
  cap : E → ℕ

end OmniThreshold


