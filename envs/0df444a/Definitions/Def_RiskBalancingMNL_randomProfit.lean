-- Prove2me | Definitions.Def_RiskBalancingMNL_randomProfit
-- name    : RiskBalancingMNL_randomProfit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:30.367814+00:00
-- url     : https://prove2.me/theorems/6c1dc0ee-91ab-4d16-ab99-21738161e98e
-- title:
--   Multinomial demand of $N$ customers and the random profit $\hat\pi=\sum_i m_iX_i$
-- statement:
--   Each of $N$ customers chooses independently one of $n$ products or nothing, with the same law $\nu$; write $q_i=\nu(\{i\})$ for the probability of choosing product $i$. The joint law of the $N$ choices is the product measure $\nu^{\otimes N}$. The demand $X_i$ for product $i$ is the number of customers who choose it, so $X=(X_1,\dots,X_n)$ is multinomial, and for a markup vector $m$ the firm's profit is
--   $$
--   \hat\pi=\sum_{i=1}^n m_iX_i .
--   $$
--   These objects connect the deterministic objective $L$ to the mean and variance of profit (equations (2)–(3)).
--
--   **Formalization Note** A customer's choice lives in $\{0,\dots,n-1\}\sqcup\{\ast\}$, with $\ast$ the no-purchase option.
-- source:
--   Li & Webster, Optimizing Risk-balancing Return under Discrete Choice Models, SSRN 3959428 (PDF of 2021-11-14), §3, pp.7–8 (demand vector multinomial, $\hat\pi=\sum_im_iX_i$)

import Mathlib

namespace RiskBalancingMNL

open MeasureTheory

/-- The probability `qᵢ` that one customer chooses product `i`, when a customer's choice has law
`ν` on `Fin n ⊕ Unit` (`Sum.inl i` = product `i`, `Sum.inr ()` = no purchase). Li & Webster,
*Optimizing Risk-balancing Return under Discrete Choice Models*, SSRN 3959428 (PDF of
2021-11-14), §3, p.7. -/
noncomputable def choiceProb {n : ℕ} (ν : Measure (Fin n ⊕ Unit)) (i : Fin n) : ℝ :=
  ν.real {Sum.inl i}

/-- The joint law of the choices of `N` customers who choose independently with the same law
`ν` (SSRN 3959428, §3, pp.7–8: the demand vector is multinomial). -/
noncomputable def customerLaw {n : ℕ} (N : ℕ) (ν : Measure (Fin n ⊕ Unit)) :
    Measure (Fin N → Fin n ⊕ Unit) :=
  Measure.pi fun _ => ν

/-- The demand `Xᵢ` for product `i`: the number of the `N` customers who choose it (SSRN 3959428,
§3, p.7). -/
noncomputable def demand {n N : ℕ} (i : Fin n) (ω : Fin N → Fin n ⊕ Unit) : ℝ :=
  ((Finset.univ.filter fun k => ω k = Sum.inl i).card : ℝ)

/-- The firm's random profit `π̂ = Σᵢ mᵢ Xᵢ` (SSRN 3959428, p.8). -/
noncomputable def randomProfit {n N : ℕ} (m : Fin n → ℝ) (ω : Fin N → Fin n ⊕ Unit) : ℝ :=
  ∑ i, m i * demand i ω

end RiskBalancingMNL


