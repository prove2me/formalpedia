-- Prove2me | Definitions.Def_RegimeDRCVaR_val11
-- name    : RegimeDRCVaR_val11
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:15.792043+00:00
-- url     : https://prove2.me/theorems/35676bee-933f-45fb-9bcd-447220814ebc
-- title:
--   Optimal value of problem (11)
-- statement:
--   The optimal value of the distributionally robust CVaR portfolio problem (11) is
--   $$
--   \min_{x\in\mathcal X,\ v\in\mathbb R}\Big\{v+\frac{1}{1-\eta}\sup_{\mathbb P\in\mathcal U_{rs}(\boldsymbol\theta)}\mathbb E^{\mathbb P}[G(x,\tilde r)]\Big\}.
--   $$
--
--   **Formalization Note** The minimum is an infimum in the extended reals over $x\in\mathcal X$ and $v\in\mathbb R$; it is $+\infty$ when $\mathcal X$ is empty. Attainment is not built in.
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, display (11), p.13

import Mathlib
import Definitions.Def_RegimeDRCVaR_obj11
import Definitions.Def_RegimeDRCVaR_feasX

open scoped ENNReal

namespace RegimeDRCVaR

/-- **The optimal value of problem (11)**
`min_{x ∈ 𝒳, v ∈ ℝ} {v + (1 − η)⁻¹ sup_{P ∈ U_rs(θ)} 𝔼^P[G(x, r̃)]}`
(Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930, display (11), p.13).

**Formalization Note** The "min" is an infimum in `EReal` over `x ∈ 𝒳` and `v ∈ ℝ`; it is `+∞`
when `𝒳` is empty. Attainment is not built in. -/
noncomputable def val11 {I K p q : ℕ} {N : Fin K → ℕ} (m : ℝ≥0∞)
    (r : (k : Fin K) → Fin (N k) → Fin I → ℝ) (w θ : Fin K → ℝ) (η : ℝ)
    (A : Matrix (Fin p) (Fin I) ℝ) (b : Fin p → ℝ) (C : Matrix (Fin q) (Fin I) ℝ)
    (d : Fin q → ℝ) : EReal :=
  ⨅ x ∈ feasX A b C d, ⨅ v : ℝ, obj11 m r w θ η x v

end RegimeDRCVaR


