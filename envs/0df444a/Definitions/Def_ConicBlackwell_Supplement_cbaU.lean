-- Prove2me | Definitions.Def_ConicBlackwell_Supplement_cbaU
-- name    : ConicBlackwell_Supplement_cbaU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:45:53.742812+00:00
-- url     : https://prove2.me/theorems/0d0b4491-31d1-5adc-b280-0eeed60b5949
-- title:
--   Aggregate payoff $u_t$ of a CBA run
-- statement:
--   The aggregate payoff vector $u_t\in\mathbb R^{n+1}$ of the CBA run after round $t$: $u_0=0$ and $u_{t+1}=u_t+\omega_{t+1}v_{t+1}$, so that $u_t=\sum_{\tau=1}^t\omega_\tau v_\tau$; see the definition of the run's state.
--
--   **Formalization Note** The second component of `cbaState`.
-- source:
--   Grand-Clément & Kroer, Solving Optimization Problems with Blackwell Approachability, arXiv:2202.12277v1 (https://arxiv.org/abs/2202.12277v1), §3.1, p.6; p.7

import Mathlib
import Definitions.Def_ConicBlackwell_Supplement_cbaState
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

namespace ConicBlackwell.Supplement

/-- **The aggregate payoff `u_t` of a CBA run** (§3.1, p.6), with `u₀ = 0` and
`u_{t+1} = u_t + ω_{t+1} v_{t+1}`, so `u_t = Σ_{τ=1}^t ω_τ v_τ` (p.7).
Grand-Clément & Kroer, *Solving Optimization Problems with Blackwell Approachability*,
arXiv:2202.12277v1, §3.1, p.6.

Formalization Note: `u t` is the second component of `cbaState X x₀ x₁ ω f t`. -/
noncomputable def cbaU {n : ℕ} (X : Set (E n)) (x₀ x₁ : E n) (ω : ℕ → ℝ)
    (f : ℕ → E n) (t : ℕ) : E (n + 1) :=
  (cbaState X x₀ x₁ ω f t).2

end ConicBlackwell.Supplement


