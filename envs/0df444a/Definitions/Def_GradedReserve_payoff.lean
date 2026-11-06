-- Prove2me | Definitions.Def_GradedReserve_payoff
-- name    : GradedReserve_payoff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:32:40.96054+00:00
-- url     : https://prove2.me/theorems/8884a71c-8ac7-4859-806a-0171e1b39471
-- title:
--   Interim payoff of an action
-- statement:
--   A risk-neutral bidder of value $v$ who bids $a\in[0,1]$ against the symmetric strategy $\sigma$ in $G_\pi$ earns
--   $$u(v,a)=(v-a)\,W(a)$$
--   in expectation, since the winner pays its bid. Exit (any action outside $[0,1]$) earns $0$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section 2 and Definition 2.3, p.4 (PDF 5)

import Mathlib
import Definitions.Def_GradedReserve_winProb
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The interim payoff of a risk-neutral bidder of value `v` taking action `a` in `G_π` against the
symmetric strategy `σ` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section 2 and Definition 2.3, p.4, PDF 5): `(v − a) W(a)` for a bid
`a ∈ [0, 1]` (the winner pays its bid), and `0` for exit (any action outside `[0, 1]`). -/
noncomputable def payoff (f : ℝ → ℝ) (n : ℕ) (π : ℝ → ℝ) (σ : Kernel ℝ ℝ) (v a : ℝ) : ℝ :=
  if a ∈ Icc (0:ℝ) 1 then (v - a) * winProb f n π σ a else 0

end GradedReserve


