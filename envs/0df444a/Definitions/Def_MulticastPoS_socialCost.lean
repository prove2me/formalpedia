-- Prove2me | Definitions.Def_MulticastPoS_socialCost
-- name    : MulticastPoS_socialCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:38:48.265657+00:00
-- url     : https://prove2.me/theorems/01b0b014-f715-4a46-80ae-81b49edcffa4
-- title:
--   Social cost $SC(P)$
-- statement:
--   The **social cost** of a path profile $P=(P_1,\dots,P_n)$ is the total cost of the edges used by at least one player, each edge counted once:
--
--   $$
--   SC(P)=c(\operatorname{supp}(P))=\sum_{e\,:\,x_e(P)\ge 1} c_e .
--   $$
--
--   The price of stability compares the least $SC$ of a Nash equilibrium with the least $SC$ of any profile.
--
--   **Formalization Note** This is the published `designCost` with constant edge costs.
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), Section 1, p.1; Eq. (2), p.4

import Mathlib
import Definitions.Def_PriceOfStability_Harmonic_Model

open CongestionPoA.AsymSum PriceOfStability.Harmonic

namespace MulticastPoS

/-- The social cost `SC(P)` (Huang–Yuan, *An O(log log n) Upper Bound on the Price of Stability
for Undirected Multicast Shapley Games*, STOC 2027 submission manuscript (sha256 dd0e08d0…f6d4),
Section 1, p.1; Eq. (2), p.4): the total cost of the edges used by the profile `P`, counting each
edge once, `SC(P) = c(supp(P)) = Σ_{e : x_e(P) ≥ 1} c_e`.

**Formalization Note** This is the published `PriceOfStability.Harmonic.designCost` with constant
edge costs `fun e _ => c e`, i.e. the sum of `c e` over the edges `e` with positive load. -/
noncomputable def socialCost {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    [DecidableEq ι] (c : Sym2 V → ℝ) (P : ι → Finset (Sym2 V)) : ℝ :=
  designCost (fun e _ => c e) P

end MulticastPoS


