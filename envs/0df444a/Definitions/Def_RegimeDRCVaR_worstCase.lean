-- Prove2me | Definitions.Def_RegimeDRCVaR_worstCase
-- name    : RegimeDRCVaR_worstCase
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:20.415813+00:00
-- url     : https://prove2.me/theorems/ddce10b7-5201-40c2-9345-0885aa0c7977
-- title:
--   Worst-case expected loss $\sup_{\mathbb P\in\mathcal U_{rs}(\boldsymbol\theta)}\mathbb E^{\mathbb P}[G(x,\tilde r)]$
-- statement:
--   For a portfolio $x$ and level $v$, the **worst-case expected loss** over the regime-switching ambiguity set is
--   $$
--   \sup_{\mathbb P\in\mathcal U_{rs}(\boldsymbol\theta)}\mathbb E^{\mathbb P}\big[G(x,\tilde r)\big],\qquad G(x,r)=(-x'r-v)^+ .
--   $$
--   It is the inner problem of (11).
--
--   **Formalization Note** The loss is nonnegative, so the expectation is a lower Lebesgue integral and the supremum is taken in $[0,+\infty]$; an unbounded supremum is $+\infty$.
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, display (11), p.13

import Mathlib
import Definitions.Def_RegimeDRCVaR_Urs
import Definitions.Def_RegimeDRCVaR_lossG

open MeasureTheory
open scoped ENNReal

namespace RegimeDRCVaR

/-- **The worst-case expected loss** `sup_{P ∈ U_rs(θ)} 𝔼^P[G(x, r̃)]`
(Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930, problem (11), p.13), where
`G(x, r) = (−x′r − v)⁺` is the loss (6) at the same `v` as the outer objective.

**Formalization Note** The loss is nonnegative, so the expectation is the lower Lebesgue integral
of `ofReal (G(x, r̃))` and the supremum is taken in `ℝ≥0∞` (an unbounded supremum is `∞`, not a
junk value; the supremum over an empty set would be `0`, but `U_rs(θ)` is nonempty for
`θ ≥ 0`, `w` in the simplex and `N_k ≥ 1`). -/
noncomputable def worstCase {I K : ℕ} {N : Fin K → ℕ} (m : ℝ≥0∞)
    (r : (k : Fin K) → Fin (N k) → Fin I → ℝ) (w θ : Fin K → ℝ) (x : Fin I → ℝ) (v : ℝ) : ℝ≥0∞ :=
  ⨆ P ∈ Urs m r w θ, ∫⁻ ω, ENNReal.ofReal (lossG x v ω.1) ∂P

end RegimeDRCVaR


