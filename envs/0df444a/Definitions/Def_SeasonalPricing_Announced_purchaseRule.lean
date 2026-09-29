-- Prove2me | Definitions.Def_SeasonalPricing_Announced_purchaseRule
-- name    : SeasonalPricing_Announced_purchaseRule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:11:27.871248+00:00
-- url     : https://prove2.me/theorems/28fbfcf1-4d25-4e85-b8b2-b74d91c92298
-- title:
--   Valuations, the immediate-purchase rule, and the threshold ψ_A of Eq. (7) under an announced price path
-- statement:
--   A seller sells a seasonal product over a season $[0, H]$ split at a fixed time $T$: the premium price $p_1$ applies on $[0, T)$ and the discount price $p_2 \le p_1$ from $T$ on. Under an **announced** price path the seller commits to the pair $(p_1, p_2)$ upfront. A customer with **base valuation** $V$ values the product at time $t$ at
--
--   $$
--   V(t) = V e^{-\alpha t},
--   $$
--
--   where $\alpha \ge 0$ is the common decline factor.
--
--   A customer arriving at a time $t < T$ who believes that a unit will still be available to him at time $T$ with probability $\omega$ **buys immediately** if and only if both
--
--   1. the current surplus is nonnegative, $V(t) - p_1 \ge 0$, and
--   2. the current surplus is at least the expected surplus of waiting for the discount,
--   $$
--   V(t) - p_1 \ge \omega \cdot \max\{V(T) - p_2,\ 0\}.
--   $$
--
--   The file also defines, for a number $w$, the function of Eq. (7) on $0 \le t < T$,
--
--   $$
--   \psi_A(t) = \max\left\{p_1,\ \frac{p_1 - w p_2}{1 - w e^{-\alpha(T-t)}}\right\}.
--   $$
--
--   These are the objects of Theorem 2 of Aviv and Pazgal: the purchase rule is the customer's decision problem on $[0, T)$, and $\psi_A$ is the claimed equilibrium threshold.
--
--   **Formalization Note** The expected surplus of waiting is $\omega\max\{V(T)-p_2,0\}$: under an announced path the discount price is known, so the only uncertainty is whether a unit is allocated, with probability $\omega$. The definition of $\psi_A$ is a plain real expression; Lean's convention $x/0 = 0$ would apply if $w e^{-\alpha(T-t)} = 1$, and every theorem using $\psi_A$ excludes that case by hypothesis.
-- source:
--   Aviv and Pazgal, Optimal Pricing of Seasonal Products in the Presence of Forward-Looking Consumers, Manufacturing & Service Operations Management 10(3), 2008, p. 343 (valuation V_j(t) = V_j e^{−αt}), p. 344 (the two conditions for an immediate purchase), p. 348, Theorem 2, Eq. (7)

import Mathlib

namespace SeasonalPricing.Announced

/-- The valuation at time `t` of a customer with base valuation `V`: `V(t) = V e^{-α t}` (p. 343). -/
noncomputable def valuation (α V t : ℝ) : ℝ := V * Real.exp (-(α * t))

/-- The purchase rule of p. 344 under an announced price path `(p1, p2)`: a customer with base
valuation `V`, arriving at time `t < T`, who expects a unit to be available at time `T` with
probability `ω`, buys immediately iff (i) the current surplus `V(t) - p1` is nonnegative and
(ii) it is at least the expected surplus of waiting, `ω · max{V(T) - p2, 0}`. -/
def buysNow (α T p1 p2 ω t V : ℝ) : Prop :=
  0 ≤ valuation α V t - p1 ∧ ω * max (valuation α V T - p2) 0 ≤ valuation α V t - p1

/-- The threshold `ψ_A(t) = max{p1, (p1 - w p2)/(1 - w e^{-α(T-t)})}` of Eq. (7), p. 348,
on `0 ≤ t < T`. -/
noncomputable def psiA (α T p1 p2 w : ℝ) (t : ℝ) : ℝ :=
  max p1 ((p1 - w * p2) / (1 - w * Real.exp (-(α * (T - t)))))

end SeasonalPricing.Announced


