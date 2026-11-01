-- Prove2me | Definitions.Def_SimpleMenus_homogenizedValue
-- name    : SimpleMenus_homogenizedValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:58.255402+00:00
-- url     : https://prove2.me/theorems/74fbc427-d058-4fd4-8855-f40bf28aa5ba
-- title:
--   Homogenized nature problem at price $p$
-- statement:
--   For a mechanism $\pi$ and a price $p$, the homogenized problem in the proof of Proposition 1 is the linear program over measures
--
--   $$\inf_{dH_p\ge0}\int_0^{\bar v} t(w)\,dH_p(w)\quad\text{s.t.}\quad\int_{[p,\bar v]}dH_p=1,\qquad\int_{[0,\bar v]}\phi_k\,dH_p\ge0,\ k=1,\dots,K,$$
--
--   where $H_p$ ranges over finite measures on $[0,\bar v]$ and $t$ is the expected payment.
--
--   **Formalization Note** $H_p$ is a finite, not a probability, measure on $\mathbb R$ carried by $[0,\bar v]$; each constraint requires integrability. The value lies in the extended reals and is $+\infty$ if the feasible set is empty.
-- source:
--   Wang, The Power of Simple Menus in Robust Selling Mechanisms, arXiv:2310.17392v3, proof of Proposition 1, p.ec6 (PDF p.40)

import Mathlib
import Definitions.Def_SimpleMenus_pay

open MeasureTheory Set

namespace SimpleMenus

/-- The feasible set of the homogenized nature problem at the price `p`: the finite measures
`H_p` carried by `[0, v̄]` with `∫_{[p, v̄]} dH_p = 1` and `∫_{[0, v̄]} ϕ_k dH_p ≥ 0` for every `k`
(Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, proof of Proposition 1, p.ec6 = PDF p.40).

Formalization Note: `H_p` is a finite measure, not a probability measure; its total mass
`1 / (1 − F(p−))` is unbounded. Each constraint carries integrability. -/
def Hset (vbar : ℝ) {K : ℕ} (phi : Fin K → ℝ → ℝ) (p : ℝ) : Set (Measure ℝ) :=
  {H | IsFiniteMeasure H ∧ H (Icc 0 vbar)ᶜ = 0 ∧ H (Icc p vbar) = 1 ∧
      ∀ k, Integrable (phi k) H ∧ 0 ≤ ∫ w, phi k w ∂H}

/-- The value of the homogenized linear program `inf_{dH_p ≥ 0} ∫_0^v̄ t(w) dH_p(w)` over `Hset`
(Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, proof of Proposition 1, p.ec6 = PDF p.40).

Formalization Note: the value is in `EReal`; it is `⊤` when `Hset` is empty. -/
noncomputable def homogenizedValue (vbar : ℝ) {K n : ℕ} (phi : Fin K → ℝ → ℝ)
    (v x : Fin n → ℝ) (p : ℝ) : EReal :=
  ⨅ H ∈ Hset vbar phi p, ((∫ w, pay v x w ∂H : ℝ) : EReal)

end SimpleMenus


