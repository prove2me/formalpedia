-- Prove2me | Definitions.Def_RegimeDRCVaR_obj11
-- name    : RegimeDRCVaR_obj11
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:25:23.632671+00:00
-- url     : https://prove2.me/theorems/a0f5501a-9d2d-4e8b-9e29-9fc2797d56de
-- title:
--   Objective of problem (11)
-- statement:
--   For a confidence level $\eta$, a portfolio $x$ and $v\in\mathbb R$, the objective of problem (11) is
--   $$
--   J_{11}(x,v)=v+\frac{1}{1-\eta}\sup_{\mathbb P\in\mathcal U_{rs}(\boldsymbol\theta)}\mathbb E^{\mathbb P}\big[G(x,\tilde r)\big],
--   $$
--   the Rockafellar–Uryasev function of the worst-case distribution: minimized over $v$ it gives the worst-case CVaR of the loss $-x'\tilde r$.
--
--   **Formalization Note** The value is an extended real (`EReal`), so an infinite worst case gives $+\infty$.
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, display (11), p.13

import Mathlib
import Definitions.Def_RegimeDRCVaR_worstCase

open scoped ENNReal

namespace RegimeDRCVaR

/-- **The objective of problem (11)**
`J₁₁(x, v) = v + (1 − η)⁻¹ · sup_{P ∈ U_rs(θ)} 𝔼^P[G(x, r̃)]`
(Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930, display (11), p.13), for a confidence level `η`.

**Formalization Note** The value is in `EReal`: the worst-case expectation (an `ℝ≥0∞`) is coerced
to `EReal`, so an infinite worst case gives `J₁₁ = +∞` rather than a junk real. -/
noncomputable def obj11 {I K : ℕ} {N : Fin K → ℕ} (m : ℝ≥0∞)
    (r : (k : Fin K) → Fin (N k) → Fin I → ℝ) (w θ : Fin K → ℝ) (η : ℝ)
    (x : Fin I → ℝ) (v : ℝ) : EReal :=
  (v : EReal) + (((1 - η)⁻¹ : ℝ) : EReal) * ((worstCase m r w θ x v : ℝ≥0∞) : EReal)

end RegimeDRCVaR


