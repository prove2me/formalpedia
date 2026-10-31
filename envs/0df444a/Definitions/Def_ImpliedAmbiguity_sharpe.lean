-- Prove2me | Definitions.Def_ImpliedAmbiguity_sharpe
-- name    : ImpliedAmbiguity_sharpe
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:05:08.842715+00:00
-- url     : https://prove2.me/theorems/6bff1032-ef0e-42e6-a29d-c3b095db51e1
-- title:
--   Sharpe ratio $\mathrm{Sr}(x) = (\mu-R_f\mathbf 1)^\top x / (x^\top\Sigma_R x)^{1/2}$
-- statement:
--   For a nonzero portfolio $x\in\mathbb R^N\setminus\{0\}$, covariance matrix $\Sigma_R$ and expected excess return vector $c = \mu - R_f\mathbf 1$, the **Sharpe ratio** of $x$ is
--
--   $$
--   \mathrm{Sr}(x) = \frac{c^\top x}{(x^\top\Sigma_R x)^{1/2}},
--   $$
--
--   the expected excess return per unit of standard deviation of the portfolio's return.
--
--   **Formalization Note** The square root is `Real.sqrt`. The function is total on $\mathbb R^N$ (its value at $x=0$ is $0/0 = 0$); every statement of the mission applies it to nonzero portfolios with $\Sigma_R$ positive definite.
-- source:
--   Hara & Honda, Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors, working paper (October 9, 2018; published version doi:10.1287/mnsc.2021.4097), §4.3, p.21 (definition of Sr)

import Mathlib

open Matrix

namespace ImpliedAmbiguity

/-- Hara & Honda, *Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors*, working
paper (October 9, 2018; published version Management Science 2022, doi:10.1287/mnsc.2021.4097),
§4.3, p.21: "deﬁne Sr : R^N∖{0} → R by Sr(x) = (µ − R_f1)ᵀx / (xᵀΣ_R x)^{1/2}", the Sharpe ratio
of the portfolio `x`.

**Formalization Note.** The excess return vector is passed as `c`; `(xᵀΣ_R x)^{1/2}` is
`Real.sqrt (x ⬝ᵥ (SigmaR *ᵥ x))`. The function is total on `Fin N → ℝ` (at `x = 0` it is `0/0 = 0`);
every statement of the mission applies it to nonzero portfolios and positive definite `Σ_R`. -/
noncomputable def sharpe {N : ℕ} (SigmaR : Matrix (Fin N) (Fin N) ℝ) (c x : Fin N → ℝ) : ℝ :=
  (c ⬝ᵥ x) / Real.sqrt (x ⬝ᵥ (SigmaR *ᵥ x))

end ImpliedAmbiguity


