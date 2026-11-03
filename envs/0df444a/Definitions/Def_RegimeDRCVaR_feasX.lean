-- Prove2me | Definitions.Def_RegimeDRCVaR_feasX
-- name    : RegimeDRCVaR_feasX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:22:37.463686+00:00
-- url     : https://prove2.me/theorems/76e27ddc-d352-4dfb-bb0a-ce9e14643fba
-- title:
--   Feasible portfolios $\mathcal X=\{x\mid Ax=b,\ Cx\ge d\}$
-- statement:
--   Let $A\in\mathbb R^{p\times I}$, $b\in\mathbb R^p$, $C\in\mathbb R^{q\times I}$ and $d\in\mathbb R^q$. The set of **feasible portfolios** is the polyhedron
--   $$
--   \mathcal X=\{x\in\mathbb R^I \mid Ax=b,\ Cx\ge d\},
--   $$
--   with $Cx\ge d$ componentwise. The budget constraint $\mathbf 1'x=1$ is one of the rows of $Ax=b$; leverage or no-shorting constraints are further rows.
--
--   **Formalization Note** The paper calls the number of rows of $A$ "$m$", which clashes with the norm index $m$; here the row counts are $p$ and $q$. No row is imposed: $\mathcal X$ is any polyhedron, possibly empty.
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, §3.1.2, p.9 (x ∈ 𝒳 := {x | Ax = b, Cx ≥ d})

import Mathlib

open Matrix

namespace RegimeDRCVaR

/-- **The feasible portfolio set** `𝒳 := {x | Ax = b, Cx ≥ d}`
(Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930, §3.1.2, p.9), with `A ∈ ℝ^{p×I}`, `b ∈ ℝ^p`, `C ∈ ℝ^{q×I}`, `d ∈ ℝ^q`.

**Formalization Note** The paper calls the row count of `A` "m", which clashes with the norm
index; it is `p` here and the row count of `C` is `q`. The budget constraint `1′x = 1` is
"embedded into 𝒳" by the paper, i.e. it is one of the rows of `A`; it is not a separate
condition. `Cx ≥ d` is componentwise. -/
def feasX {I p q : ℕ} (A : Matrix (Fin p) (Fin I) ℝ) (b : Fin p → ℝ)
    (C : Matrix (Fin q) (Fin I) ℝ) (d : Fin q → ℝ) : Set (Fin I → ℝ) :=
  {x | A *ᵥ x = b ∧ ∀ j, d j ≤ (C *ᵥ x) j}

end RegimeDRCVaR


