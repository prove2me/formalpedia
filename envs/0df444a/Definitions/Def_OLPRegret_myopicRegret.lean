-- Prove2me | Definitions.Def_OLPRegret_myopicRegret
-- name    : OLPRegret_myopicRegret
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:04:23.327286+00:00
-- url     : https://prove2.me/theorems/edb1ff5f-a9b1-4298-8715-0a47dae8bd9f
-- title:
--   The upper and lower myopic regrets
-- statement:
--   For $\delta>0$ and a choice of shadow prices, the **upper myopic regret** is
--   $$
--   r_t=\mathbb 1\{b_t\notin B_{\delta/2}(\beta)\}\sum_{s=1}^tu_s+\mathbb 1\{b_t\in B_{\delta/2}(\beta)\}\Big(x_t\Delta_t\big(y_{t-1}^{\psi_t^{b_t}(a_t)}\big)^-+(1-x_t)\Delta_t\big(y_{t-1}^{\psi_t^{b_t}(0)}\big)^+\Big),
--   $$
--   and the **lower myopic regret** is
--   $$
--   r_t=\mathbb 1\{b_t\in B_{\delta/2}(\beta)\}\Big(x_t\Delta_t\big(y_{t-1}^{\psi_t^{b_t}(0)}\big)^-+(1-x_t)\Delta_t\big(y_{t-1}^{\psi_t^{b_t}(a_t)}\big)^+\Big),
--   $$
--   where $x_t$ is the realized decision. They price each decision at an empirical shadow price computed from the periods still to come; summing them bounds the regret against the linear program from above and below.
--
--   **Formalization Note** The printed upper $r_t$ in (35) selects its terms by the sign of $\Delta_t(y_\infty^{b_t})$. This agrees with $x_t$ unless $\Delta_t(y_\infty^{b_t})>0$ and $a_t\not\le tb_t$, where the printed form is false; see `OLPRegret.eq_35`.
-- source:
--   Bray, arXiv:1912.08917v6, (35), p.27; (39), p.32

import Mathlib
import Definitions.Def_OLPRegret_dualMin

set_option autoImplicit false

open MeasureTheory

namespace OLPRegret

open scoped Classical in
/-- The upper myopic regret `rₜ` of (35) (Bray, arXiv:1912.08917v6, p.27), corrected:
with `xₜ` the realized decision,
`rₜ = 𝟙{bₜ ∉ B_{δ/2}(β)} Σ_{s≤t} uₛ
  + 𝟙{bₜ ∈ B_{δ/2}(β)} (xₜ Δₜ(y_{t−1}^{ψ(aₜ)})⁻ + (1 − xₜ) Δₜ(y_{t−1}^{ψ(0)})⁺)`.

**Formalization Note** The printed `rₜ` selects its term by `Δₜ(y∞^{bₜ}) > 0` or `≤ 0`. That agrees
with `xₜ = 1` or `0` except when `Δₜ(y∞^{bₜ}) > 0` and `aₜ ≰ tbₜ`, where (33) is false as printed and
Algorithm 2 rejects; see the difference list of `OLPRegret.eq_35`. `Y (t−1)` reads the customers of
periods `t − 1, …, 1` only. -/
noncomputable def rUpper {m n : ℕ} (δ : ℝ) (D : Scheme m n) (β : E m) (Y : ℕ → E m → E m)
    (ω : Sample m n) (t : Fin n) : ℝ :=
  if inventory D β ω (period t) ∈ Metric.ball β (δ / 2) then
    decision D β ω t *
        max (-surplus (ω t) (Y t.val (psi (period t) (inventory D β ω (period t)) (ω t).2))) 0 +
      (1 - decision D β ω t) *
        max (surplus (ω t) (Y t.val (psi (period t) (inventory D β ω (period t)) 0))) 0
  else ∑ s : Fin n with s ≤ t, (ω s).1

open scoped Classical in
/-- The lower myopic regret `rₜ` of (39) (Bray, arXiv:1912.08917v6, p.32):
`rₜ = 𝟙{bₜ ∈ B_{δ/2}(β)} (πₜ Δₜ(y_{t−1}^{ψ(0)})⁻ + (1 − πₜ) Δₜ(y_{t−1}^{ψ(aₜ)})⁺)`, with `πₜ` the
realized decision `xₜ`. -/
noncomputable def rLower {m n : ℕ} (δ : ℝ) (D : Scheme m n) (β : E m) (Y : ℕ → E m → E m)
    (ω : Sample m n) (t : Fin n) : ℝ :=
  if inventory D β ω (period t) ∈ Metric.ball β (δ / 2) then
    decision D β ω t *
        max (-surplus (ω t) (Y t.val (psi (period t) (inventory D β ω (period t)) 0))) 0 +
      (1 - decision D β ω t) *
        max (surplus (ω t) (Y t.val (psi (period t) (inventory D β ω (period t)) (ω t).2))) 0
  else 0

end OLPRegret


