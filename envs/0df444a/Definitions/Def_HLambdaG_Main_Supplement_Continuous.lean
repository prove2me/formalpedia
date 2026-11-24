-- Prove2me | Definitions.Def_HLambdaG_Main_Supplement_Continuous
-- name    : HLambdaG_Main_Supplement_Continuous
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:59:11.190164+00:00
-- url     : https://prove2.me/theorems/c289e3be-0ba5-43c6-9f8c-a81e78eeec58
-- title:
--   §1.6, §4.4, pp. 637–638, 642 — continuous L = λW: F_u(t) of (13) with (25), averages G(s), H(t) of (12)
-- statement:
--   **The continuous $L=\lambda W$ setting (§1.6 with (13) and (25)).** Customers are indexed by a continuous variable $u\ge0$. Customer $u$ arrives at time $T_1(u)$, where $T_1$ is a nonnegative, nondecreasing, right-continuous, finite function with $T_1(s)\to\infty$. It stays for the waiting time $w(u)\ge0$. Its input is
--   $$
--   F_u(t)=\int_0^t f(u,v)\,dv,\qquad f(u,v)=1_{[T_1(u),\,T_1(u)+w(u)]}(v),
--   $$
--   so that $F_u(t)=\min\{w(u),\,(t-T_1(u))^+\}$ and $F_u(\infty)=w(u)$. The averages (12) are
--   $$
--   G(s)=s^{-1}\int_0^s F_u(\infty)\,du=s^{-1}\int_0^s w(u)\,du,\qquad
--   H(t)=t^{-1}\int_0^\infty F_u(t)\,du .
--   $$
--
--   These are the averages of Theorem 6, the continuous analogue of $L=\lambda W$.
--
--   **Formalization Note** $F_u(t)$ is defined by the closed form $\min\{w(u),\max\{0,t-T_1(u)\}\}$. It equals the integral of (13) with (25) whenever $w(u)\ge0$, which Theorem 6 assumes. $w$ is a function on $\mathbb R_{\ge0}$. The integrals are Lebesgue integrals over $[0,s]$ and $[0,\infty)$ in $\mathbb R$, evaluated at `u.toNNReal`, which is $u$ itself on these sets. $T_1$ is the published `HLambdaG.Main.TimeChange`. Integrability is not part of the definition. Theorem 6 assumes $w$ integrable on every $[0,s]$. The integrand of $H(t)$ is then integrable, because it lies between $0$ and $w(u)$ and vanishes when $T_1(u)\ge t$, a condition that holds for all large $u$.
-- source:
--   Glynn and Whitt, Extensions of the queueing relations L = λW and H = λG, Oper. Res. 37 (1989), p. 637, §1.6 display (12); p. 638, display (13); p. 642, §4.4 display (25); https://doi.org/10.1287/opre.37.4.634

import Mathlib
import Definitions.Def_HLambdaG_Main_TimeChange

open scoped NNReal

namespace HLambdaG.Main.Supplement

open MeasureTheory

/-- (13) with (25): the input of the customer arriving at "index" `u ≥ 0`,
`F_u(t) = ∫₀ᵗ 1_{[T₁(u), T₁(u) + w(u)]}(v) dv = min(w(u), (t − T₁(u))⁺)` for `w(u) ≥ 0`. -/
noncomputable def contF (τ₁ : TimeChange) (w : ℝ≥0 → ℝ) (u t : ℝ≥0) : ℝ :=
  min (w u) (max 0 ((t : ℝ) - τ₁.T u))

/-- The customer average (12) in the continuous `L = λW` setting:
`G(s) = s⁻¹ ∫₀ˢ F_u(∞) du = s⁻¹ ∫₀ˢ w(u) du`. -/
noncomputable def contG (w : ℝ≥0 → ℝ) (s : ℝ≥0) : ℝ :=
  ((s : ℝ))⁻¹ * ∫ u in Set.Icc (0 : ℝ) s, w u.toNNReal

/-- The time average (12) in the continuous `L = λW` setting:
`H(t) = t⁻¹ ∫₀^∞ F_u(t) du`. -/
noncomputable def contH (τ₁ : TimeChange) (w : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  ((t : ℝ))⁻¹ * ∫ u in Set.Ici (0 : ℝ), contF τ₁ w u.toNNReal t

end HLambdaG.Main.Supplement


