-- Prove2me | Definitions.Def_SeasonalPricing_MyopicDet_reducedObjective
-- name    : SeasonalPricing_MyopicDet_reducedObjective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:59:10.612774+00:00
-- url     : https://prove2.me/theorems/e2171146-40cf-4b16-a4cf-3be4931c5c3e
-- title:
--   The reduced objective of Proposition 4 and the times $\tau = \ln(p)/\ln(\rho)$
-- statement:
--   Fix $0 < \rho < 1$. For a price $p \in [\rho, 1]$ let
--
--   $$
--   \tau(p) = \frac{\ln p}{\ln \rho} \in [0, 1],
--   $$
--
--   the time at which a customer whose valuation at time $t$ is $\rho^t$ values the product exactly at $p$; the proof of Proposition 4 writes $\tau_1 = \tau(p_1)$ and $\tau_2 = \tau(p_2)$. The objective inside the maximum of Proposition 4 is
--
--   $$
--   G(p_1, p_2) = (p_1 - p_2)\cdot\frac{\ln p_1}{\ln \rho} + p_2 \cdot \frac{\ln p_2}{\ln \rho}, \qquad \rho \le p_2 \le p_1 \le 1 .
--   $$
--
--   Multiplied by the arrival rate $\lambda$ it is the revenue collected at price $p_1$ from customers arriving during $[0, \tau_1]$ plus the revenue collected at price $p_2$ from customers arriving during $[\tau_1, \tau_2]$.
--
--   **Formalization Note** Both functions are defined for all real arguments, with Lean's conventions $\ln x = \ln|x|$, $\ln 0 = 0$ and division by $0$ giving $0$; every statement of the mission uses them only on $\rho \le p_2 \le p_1 \le 1$ with $0 < \rho < 1$, where $\ln \rho < 0$ and every logarithm is of a positive number.
-- source:
--   Aviv and Pazgal, Optimal Pricing of Seasonal Products in the Presence of Forward-Looking Consumers, Manufacturing & Service Operations Management 10(3), 2008, p. 351, Proposition 4 (maximum operand); p. 359, Proof of Proposition 4 (τ₁ ≐ ln(p₁)/ln(ρ), τ₂ ≐ ln(p₂)/ln(ρ))

import Mathlib

namespace SeasonalPricing.MyopicDet

/-- The time `τ ≐ ln(p)/ln(ρ)` at which a customer with base valuation `1` and valuation `ρ^t`
at time `t` values the product exactly at the price `p` (Aviv–Pazgal 2008, Proof of
Proposition 4, p. 359: `τ₁ = ln(p₁)/ln(ρ)`, `τ₂ = ln(p₂)/ln(ρ)`). -/
noncomputable def tau (ρ p : ℝ) : ℝ :=
  Real.log p / Real.log ρ

/-- The objective inside the maximum of Proposition 4 (Aviv–Pazgal 2008, p. 351):
`(p₁ − p₂) · ln(p₁)/ln(ρ) + p₂ · ln(p₂)/ln(ρ)`. It is used on `ρ ≤ p₂ ≤ p₁ ≤ 1`. -/
noncomputable def reducedObjective (ρ p1 p2 : ℝ) : ℝ :=
  (p1 - p2) * (Real.log p1 / Real.log ρ) + p2 * (Real.log p2 / Real.log ρ)

end SeasonalPricing.MyopicDet


