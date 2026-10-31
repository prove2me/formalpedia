-- Prove2me | Definitions.Def_DynTradeFinance_ValueOfDTF
-- name    : DynTradeFinance_ValueOfDTF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:20:31.492644+00:00
-- url     : https://prove2.me/theorems/9475490f-7066-4ad1-b82b-3b9e9a9c0136
-- title:
--   The closed form (10) of the value of DTF and the marginal benefit $-\partial V/\partial\bar d$ of reducing the information delay
-- statement:
--   For real numbers $p_1,l_1,l_2,\mu,\lambda,\delta$ the **closed form (10)** is
--   $$F(p_1,l_1,l_2,\mu,\lambda,\delta)=p_1(l_2-l_1)\,\frac{\delta}{(1-\delta)(\mu-\delta)}\cdot\frac{\lambda}{\lambda+\mu-\delta}.$$
--   Writing the expected information delay as $\bar d=1/\lambda$, the **marginal benefit of reducing the delay** is
--   $$\mathrm{MB}(p_1,l_1,l_2,\mu,\delta,\bar d)=-\frac{d}{d\bar d}\,F\big(p_1,l_1,l_2,\mu,1/\bar d,\delta\big).$$
--
--   Proposition 3 shows that $F$ is the value of DTF, $V=\Pi_D-\Pi_U$, and describes how $F$ and $\mathrm{MB}$ depend on the parameters.
--
--   **Formalization Note** $F$ is only the formula; its identification with $\Pi_D-\Pi_U$ is a clause of the goal theorem. $\mathrm{MB}$ uses Lean's `deriv` of an explicit real function, which is differentiable at every $\bar d>0$ when $\mu>\delta$, so it is the genuine derivative there.
-- source:
--   Lee, Tang, Yang, Zhang, Dynamic trade finance in the presence of information frictions and FinTech, SSRN 3632563 (Feb. 2022 revision), Proposition 3, Eq. (10), p. 14; proof of Proposition 3, Eqs. (68)–(69), pp. 40–41

import Mathlib

namespace DynTradeFinance

/-- **The closed form (10) of the value of DTF**, Proposition 3, Lee, Tang, Yang, Zhang,
SSRN 3632563, p. 14:
`F(p₁, l₁, l₂, μ, λ, δ) = p₁(l₂ − l₁)·δ/((1 − δ)(μ − δ))·λ/(λ + μ − δ)`.

This is only the formula; Proposition 3 (`proposition_3`) proves that it equals `Π_D − Π_U` for
competitive UF and DTF rates. -/
noncomputable def valueFormula (p₁ l₁ l₂ μ lam δ : ℝ) : ℝ :=
  p₁ * (l₂ - l₁) * (δ / ((1 - δ) * (μ - δ))) * (lam / (lam + μ - δ))

/-- **The marginal benefit of reducing the information delay**, Proposition 3, item 2,
SSRN 3632563, p. 14, and its proof, Eqs. (68)–(69), pp. 40–41: with the expected delay
`d̄ = 1/λ`, `MB(d̄) := −∂V/∂d̄`, the negative derivative in `d̄` of the closed form (10) evaluated
at `λ = 1/d̄`.

**Formalization Note.** Lean's `deriv` of an explicit real function; at every `d̄ > 0` with
`μ > δ` the function is differentiable, so this is the genuine derivative there. -/
noncomputable def marginalBenefit (p₁ l₁ l₂ μ δ dbar : ℝ) : ℝ :=
  -deriv (fun x : ℝ => valueFormula p₁ l₁ l₂ μ (1 / x) δ) dbar

end DynTradeFinance


