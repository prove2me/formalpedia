-- Prove2me | Definitions.Def_SeasonalPricing_MyopicDet_pointMassTail
-- name    : SeasonalPricing_MyopicDet_pointMassTail
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:58:09.344988+00:00
-- url     : https://prove2.me/theorems/1761bceb-261e-4846-ad07-24b148b138b2
-- title:
--   Tail of the base valuation when every customer values the product at $\mu = 1$ ($c = 0$)
-- statement:
--   In the numerical study of Aviv and Pazgal the base valuation $V$ has mean $\mu = 1$ and coefficient of variation $c$. Proposition 4 treats the case $c = 0$: there is no heterogeneity, and every customer has base valuation $V = 1$. Its tail is
--
--   $$
--   \bar F(x) = \Pr\{V \ge x\} = \begin{cases} 1, & x \le 1,\\ 0, & x > 1. \end{cases}
--   $$
--
--   With valuation $e^{-\alpha t}$ at time $t$, a customer arriving at time $t$ is willing to pay a price $p$ iff $\bar F(p e^{\alpha t}) = 1$.
--
--   **Formalization Note** The case $c = 0$ is the degenerate end of the Gamma family of p. 349 and lies outside §3's "continuous distribution"; the paper uses it in Propositions 4–6. The choice $\Pr\{V \ge x\}$ rather than $\Pr\{V > x\}$ changes $\bar F$ only at $x = 1$, which affects no integral over time in this mission.
-- source:
--   Aviv and Pazgal, Optimal Pricing of Seasonal Products in the Presence of Forward-Looking Consumers, Manufacturing & Service Operations Management 10(3), 2008, p. 349, §7 (μ, c); p. 350, §7 (μ = 1); p. 351, Proposition 4 (c = 0)

import Mathlib

namespace SeasonalPricing.MyopicDet

/-- The tail `F̄(x) = Pr{V ≥ x}` of the base valuation in the case `c = 0`, `μ = 1` of
Aviv–Pazgal 2008 (§7, pp. 349–351): with coefficient of variation `c = 0` every customer has the
same base valuation `V = μ = 1`, so `F̄(x) = 1` for `x ≤ 1` and `F̄(x) = 0` for `x > 1`. -/
noncomputable def pointMassTail (x : ℝ) : ℝ :=
  if x ≤ 1 then 1 else 0

end SeasonalPricing.MyopicDet


