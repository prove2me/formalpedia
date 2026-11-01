-- Prove2me | Definitions.Def_ConicBlackwell_cbaPlusU
-- name    : ConicBlackwell_cbaPlusU
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:44:55.096368+00:00
-- url     : https://prove2.me/theorems/fbfa9f08-cf52-4639-a61d-326abc28995a
-- title:
--   Aggregate payoff $u_t$ of a CBA$^+$ run
-- statement:
--   The aggregate payoff vector $u_t\in\mathbb R^{n+1}$ of the CBA$^+$ run (Algorithm 1) after round $t$, with $u_0=0$ and $u_{t+1}=\pi_{\mathcal C}(u_t+\omega_{t+1}v_{t+1})$; see the definition of the run's state.
--
--   **Formalization Note** The second component of `cbaPlusState`; $u_1=\pi_{\mathcal C}(\omega_1v_1)$ (corrected start, see `cbaPlusState`).
-- source:
--   Grand-Clément & Kroer, Solving Optimization Problems with Blackwell Approachability, arXiv:2202.12277v1 (https://arxiv.org/abs/2202.12277v1), Algorithm 1, p.6

import Mathlib
import Definitions.Def_ConicBlackwell_cbaPlusState
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

namespace ConicBlackwell

/-- **The aggregate payoff `u_t` of a CBA+ run** (Algorithm 1, p.6), with `u₀ = 0`.
Grand-Clément & Kroer, *Solving Optimization Problems with Blackwell Approachability*, arXiv:2202.12277v1, Algorithm 1, p.6.

Formalization Note: `u t` is the second component of `cbaPlusState X x₀ x₁ ω f t`; `u 0 = 0`
is the corrected start (see `cbaPlusState`). -/
noncomputable def cbaPlusU {n : ℕ} (X : Set (E n)) (x₀ x₁ : E n) (ω : ℕ → ℝ)
    (f : ℕ → E n) (t : ℕ) : E (n + 1) :=
  (cbaPlusState X x₀ x₁ ω f t).2

end ConicBlackwell


