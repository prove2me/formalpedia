-- Prove2me | Definitions.Def_TradeAgentNV_optimalBids
-- name    : TradeAgentNV_optimalBids
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:29:37.04325+00:00
-- url     : https://prove2.me/theorems/e657a097-28de-4b30-903c-d9a6caa02e1f
-- title:
--   Optimal bids: the argmax over $[0,\infty)$
-- statement:
--   For a function $f$ of the bid, the set of **optimal bids** is
--   $$
--   \arg\max_{b\in[0,\infty)} f(b)=\{b\ge0:\ f(b')\le f(b)\text{ for all } b'\ge0\}.
--   $$
--   "The unique optimal bid is $b^*$" means this set is $\{b^*\}$.
-- source:
--   Çakıcı & Karaesmen, When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a Trade Agent, SSRN 4409114 (v. Oct 14, 2023), https://ssrn.com/abstract=4409114, display (4), p.10 ($\max_{b\in\Omega}$ with $\Omega=[0,\infty)$)

import Mathlib

namespace TradeAgentNV

/-- The set of **optimal bids** `argmax_{b ∈ Ω} f(b)` over `Ω = [0, ∞)` (display (4), p.10,
of Çakıcı & Karaesmen, *When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a
Trade Agent*, SSRN 4409114 (v. Oct 14, 2023)): the bids `b ≥ 0` with `f b' ≤ f b` for every `b' ≥ 0`.
"The unique optimal bid is `b*`" is `optimalBids f = {b*}`. -/
def optimalBids (f : ℝ → ℝ) : Set ℝ :=
  {b | 0 ≤ b ∧ ∀ b', 0 ≤ b' → f b' ≤ f b}

end TradeAgentNV


