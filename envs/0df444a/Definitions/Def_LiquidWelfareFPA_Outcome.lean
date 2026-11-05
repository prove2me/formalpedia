-- Prove2me | Definitions.Def_LiquidWelfareFPA_Outcome
-- name    : LiquidWelfareFPA_Outcome
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:30:53.947988+00:00
-- url     : https://prove2.me/theorems/db878c49-5450-4ea0-9bdc-e149f9d88060
-- title:
--   Run of $T$ sequential first-price auctions among $n$ players
-- statement:
--   There are $n$ players and $T$ rounds, and one item is sold in every round. An **outcome** of the sequential first-price auction records
--
--   1. the value $v_{it}\in[0,1]$ of player $i$ for the item of round $t$;
--   2. the bid $b_{it}\ge 0$ of player $i$ in round $t$;
--   3. the winner $w_t$ of round $t$, which is any player with the highest bid: $b_{jt}\le b_{w_t t}$ for every $j$ (ties are broken arbitrarily).
--
--   The winner pays her bid, so the **price** of round $t$ is the highest bid $p_t=b_{w_t t}=\max_j b_{jt}$. Player $i$'s total **payment** and total allocated **value** are
--
--   $$P_i=\sum_{t:\,w_t=i}p_t,\qquad V_i=\sum_{t:\,w_t=i}v_{it}.$$
--
--   This is the model of the paper's Section 3, on which liquid welfare, the shading benchmark and the competitive-ratio assumption are built.
--
--   **Formalization Note** Players are `Fin n`, rounds `Fin T`. Budgets are not part of an outcome; they are a separate fixed vector $B$.
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, §3, pp.5–6

import Mathlib

namespace LiquidWelfareFPA

/-- **One run of `T` sequential first-price auctions among `n` players.**
Fikioris & Tardos, *Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted
Auctions*, arXiv:2210.07502v4, §3, pp.5–6: "We assume there are n players, T rounds, and one item
per round", "v_it ∈ [0, 1]", "in every round t, each player i submits a bid b_it and the player
with the highest bid wins the item and pays her bid (ties are broken arbitrarily). We denote with
p_t the price of the item, i.e., the highest bid", "P_i = ∑_{t∈𝒯} p_t".

An outcome records, for every player `i : Fin n` and round `t : Fin T`, the value `v i t ∈ [0,1]`
and the bid `bid i t ≥ 0`, and for every round the winner `w t`, which is any player whose bid is
highest (`bid j t ≤ bid (w t) t` for every `j`).

**Formalization Note** Bids are nonnegative. The winner is any highest bidder: the paper breaks
ties arbitrarily. The budgets are not part of an outcome; they are a separate fixed argument
`B : Fin n → ℝ` of the definitions that use them. -/
structure Outcome (n T : ℕ) where
  /-- `v i t`: player `i`'s value for the item of round `t`. -/
  v : Fin n → Fin T → ℝ
  /-- `bid i t`: player `i`'s bid in round `t`. -/
  bid : Fin n → Fin T → ℝ
  /-- `w t`: the winner of round `t`. -/
  w : Fin T → Fin n
  v_nonneg : ∀ i t, 0 ≤ v i t
  v_le_one : ∀ i t, v i t ≤ 1
  bid_nonneg : ∀ i t, 0 ≤ bid i t
  w_highest : ∀ t j, bid j t ≤ bid (w t) t

variable {n T : ℕ}

/-- The price `p_t` of round `t`: the winner's bid, which is the highest bid (p.6). -/
def Outcome.price (o : Outcome n T) (t : Fin T) : ℝ := o.bid (o.w t) t

/-- Player `i`'s total payment `P_i = ∑_{t : w_t = i} p_t` (p.6). -/
def Outcome.pay (o : Outcome n T) (i : Fin n) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t => o.w t = i), o.price t

/-- Player `i`'s total allocated value `V_i = ∑_{t : w_t = i} v_it` (p.5). -/
def Outcome.val (o : Outcome n T) (i : Fin n) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t => o.w t = i), o.v i t

end LiquidWelfareFPA


