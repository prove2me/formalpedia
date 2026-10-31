-- Prove2me | Definitions.Def_ImpliedAmbiguity_excessReturn
-- name    : ImpliedAmbiguity_excessReturn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:05:04.790163+00:00
-- url     : https://prove2.me/theorems/175cb925-6306-44e5-8ae3-729977df6b6b
-- title:
--   Expected excess return vector $\mu - R_f\mathbf 1$
-- statement:
--   Consider $N$ risky assets with expected return vector $\mu \in \mathbb R^N$ and a risk-free asset with return $R_f \in \mathbb R$. Write $\mathbf 1$ for the vector of $\mathbb R^N$ all of whose coordinates equal one. The **expected excess return vector** is
--
--   $$
--   \mu - R_f\mathbf 1 \in \mathbb R^N .
--   $$
--
--   Every formula of the mission (the bound $\bar\theta$, the vector $v^\theta$, the Sharpe ratio, the tangency portfolio) is expressed through this vector.
--
--   **Formalization Note** Assets are indexed by `Fin N`, and $\mathbf 1$ is the constant function `fun _ => 1`.
-- source:
--   Hara & Honda, Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors, working paper (October 9, 2018; published version doi:10.1287/mnsc.2021.4097), §2.2, p.11 (definition of 1 and µ − R_f1)

import Mathlib

namespace ImpliedAmbiguity

/-- Hara & Honda, *Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors*, working
paper (October 9, 2018; published version Management Science 2022, doi:10.1287/mnsc.2021.4097),
§2.2, p.11: the expected excess return vector `µ − R_f 1` of the N risky assets, where `µ` is
the vector of expected returns, `R_f` the risk-free return and `1` "the vector in R^N of which
the N coordinates are all equal to one" (p.11).

**Formalization Note.** Assets are indexed by `Fin N`; `1` is the constant function `fun _ => 1`,
so `µ − R_f 1` is `μ - fun _ => Rf`. -/
def excessReturn {N : ℕ} (μ : Fin N → ℝ) (Rf : ℝ) : Fin N → ℝ :=
  μ - fun _ => Rf

end ImpliedAmbiguity


