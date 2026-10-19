-- Prove2me | Definitions.Def_DriftVarCtrl_FixedLB_TwoInterval
-- name    : DriftVarCtrl_FixedLB_TwoInterval
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:18.579148+00:00
-- url     : https://prove2.me/theorems/2c6f3325-36e4-43a8-beb0-ef2ca9915fd1
-- title:
--   Proof of Theorem 2 (c), pp. EC-5–EC-11 — the two-interval value V₁₂(x; S) via (74), (75), (87), and F₁, F₂, f₁, f₂ (70)–(71)
-- statement:
--   This file defines the explicit value of the two-interval policy "control 1 on $[0,S)$, control 2 on $[S,U)$" and the functions whose signs decide whether that policy is optimal. Throughout, $h_1$ is the model's control-1 cost and $h_2$ is a free argument (Lemmas 4–10 vary it).
--
--   **Coefficients ((87), p. EC-11, and (75), p. EC-8).**
--   $$A_3(S,h_2) = \frac{\Big[\frac{1}{v_1}(e^{v_1S} - 1) - S\Big]\Big(\frac{h_1}{\mu_1} - \frac{h_2}{\mu_2}\Big) - \frac{M\mu_2 + h_2U}{\mu_2}}{\frac{v_2}{v_1}e^{-(v_2 - v_1)S} - \frac{v_2}{v_1}e^{-v_2S} + e^{-v_2S} - e^{-v_2U}},$$
--   $$A_1(S,h_2) = \Big(\frac{h_2}{\mu_2} - \frac{h_1}{\mu_1} + A_3(S,h_2)\,v_2e^{-v_2S}\Big)\frac{e^{v_1S}}{v_1},$$
--   the latter being the second (smooth-pasting) equation of (75) solved for $A_1$.
--
--   **The two branches ((74), p. EC-8) and the value ((60)).**
--   $$V_{0S}(x) = -\frac{h_1}{\mu_1}x + A_1(e^{-v_1x} - 1),\qquad V_{SU}(x) = -\frac{h_2}{\mu_2}x + \frac{M\mu_2 + h_2U}{\mu_2} + A_3(e^{-v_2x} - e^{-v_2U}),$$
--   and $V_{12}(x;S) = V_{0S}(x)$ for $x \le S$, $V_{12}(x;S) = V_{SU}(x)$ for $x > S$.
--
--   **Test functions ((70)–(71), p. EC-6).**
--   $$F_1(S,x,h_2) = h_1 + \mu_1V_{SU}'(x) + \frac{\sigma_1^2}{2}V_{SU}''(x),\qquad F_2(S,x,h_2) = h_2 + \mu_2V_{0S}'(x) + \frac{\sigma_2^2}{2}V_{0S}''(x),$$
--   and $f_1(S,h_2) = F_1(S,S,h_2)$, $f_2(S,h_2) = F_2(S,S,h_2)$. $F_1 \ge 0$ on $[S,U]$ says that switching to control 1 there does not help, $F_2 \ge 0$ on $[0,S]$ says the same for control 2; these are the inequalities (68)–(69) of the proof of Theorem 2 (c).
--
--   **Formalization Note.** $F_1, F_2$ are defined through derivatives of $V_{SU}, V_{0S}$, exactly as in (70), not through the simplified forms (78), (80); identities between them are theorems. The closed form (61)–(66) of the paper is not used; (74) with (87) and $A_1$ from (75) is equivalent and was checked numerically. The denominator of $A_3$ is positive for $S \in [0,U]$; outside it may vanish, where Lean's convention $x/0 = 0$ gives a junk value no statement of the mission uses.
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), pp. EC-5–EC-11, proof of Theorem 2 (c): (60), (70)–(71), (74)–(75), (87)

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model

namespace DriftVarCtrl.FixedLB

/-- The coefficient `A₃(S, h₂)` of the two-interval value ((87), proof of Lemma 6, Wang, Zenios,
SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-11), with the control-2 cost `h₂'` as an
argument (Lemmas 4–10 vary it) and `h₁ = p.h₁`:
`A₃ = ([ (e^{v₁S} − 1)/v₁ − S ](h₁/μ₁ − h₂/μ₂) − (Mμ₂ + h₂U)/μ₂) /
       ((v₂/v₁)e^{−(v₂−v₁)S} − (v₂/v₁)e^{−v₂S} + e^{−v₂S} − e^{−v₂U})`.

Formalization Note: the denominator is positive for `S ∈ [0, U]`; outside it may vanish and
Lean's `x / 0 = 0` gives a junk value that no statement of the mission uses. -/
noncomputable def A3 (p : Params) (S h₂' : ℝ) : ℝ :=
  (((Real.exp (v p .one * S) - 1) / v p .one - S) * (p.h₁ / p.μ₁ - h₂' / p.μ₂)
      - (p.M * p.μ₂ + h₂' * p.U) / p.μ₂) /
    ((v p .two / v p .one) * Real.exp (-(v p .two - v p .one) * S)
      - (v p .two / v p .one) * Real.exp (-v p .two * S)
      + Real.exp (-v p .two * S) - Real.exp (-v p .two * p.U))

/-- The coefficient `A₁(S, h₂)`, solved from the second (smooth-pasting) equation of (75)
(SSRN 3667132 p. EC-8): `A₁ = (h₂/μ₂ − h₁/μ₁ + A₃ v₂ e^{−v₂S}) e^{v₁S} / v₁`. -/
noncomputable def A1 (p : Params) (S h₂' : ℝ) : ℝ :=
  (h₂' / p.μ₂ - p.h₁ / p.μ₁ + A3 p S h₂' * v p .two * Real.exp (-v p .two * S))
    * Real.exp (v p .one * S) / v p .one

/-- The control-1 branch of the two-interval value ((74), SSRN 3667132 p. EC-8):
`V_{0S}(x) = −(h₁/μ₁)x + A₁(e^{−v₁x} − 1)`. -/
noncomputable def V0S (p : Params) (S h₂' : ℝ) (x : ℝ) : ℝ :=
  -(p.h₁ / p.μ₁) * x + A1 p S h₂' * (Real.exp (-v p .one * x) - 1)

/-- The control-2 branch of the two-interval value ((74), SSRN 3667132 p. EC-8):
`V_{SU}(x) = −(h₂/μ₂)x + (Mμ₂ + h₂U)/μ₂ + A₃(e^{−v₂x} − e^{−v₂U})`. -/
noncomputable def VSU (p : Params) (S h₂' : ℝ) (x : ℝ) : ℝ :=
  -(h₂' / p.μ₂) * x + (p.M * p.μ₂ + h₂' * p.U) / p.μ₂
    + A3 p S h₂' * (Real.exp (-v p .two * x) - Real.exp (-v p .two * p.U))

/-- The value `V₁₂(x; S)` of the policy "control 1 on `[0, S)`, control 2 on `[S, U)`"
((60), SSRN 3667132 p. EC-5, in the closed form (74)). -/
noncomputable def V12 (p : Params) (S h₂' : ℝ) (x : ℝ) : ℝ :=
  if x ≤ S then V0S p S h₂' x else VSU p S h₂' x

/-- `F₁(S, x, h₂) = h₁ + μ₁ V_{SU}′(x) + σ₁²/2 · V_{SU}″(x)` ((70), SSRN 3667132 p. EC-6),
defined through `deriv` of `V_{SU}` as in (70). -/
noncomputable def F1 (p : Params) (S x h₂' : ℝ) : ℝ :=
  p.h₁ + p.μ₁ * deriv (VSU p S h₂') x + p.σ₁ ^ 2 / 2 * deriv (deriv (VSU p S h₂')) x

/-- `F₂(S, x, h₂) = h₂ + μ₂ V_{0S}′(x) + σ₂²/2 · V_{0S}″(x)` ((70), SSRN 3667132 p. EC-6),
defined through `deriv` of `V_{0S}` as in (70). -/
noncomputable def F2 (p : Params) (S x h₂' : ℝ) : ℝ :=
  h₂' + p.μ₂ * deriv (V0S p S h₂') x + p.σ₂ ^ 2 / 2 * deriv (deriv (V0S p S h₂')) x

/-- `f₁(S, h₂) = F₁(S, S, h₂)` ((71), SSRN 3667132 p. EC-6). -/
noncomputable def f1 (p : Params) (S h₂' : ℝ) : ℝ := F1 p S S h₂'

/-- `f₂(S, h₂) = F₂(S, S, h₂)` ((71), SSRN 3667132 p. EC-6). -/
noncomputable def f2 (p : Params) (S h₂' : ℝ) : ℝ := F2 p S S h₂'

end DriftVarCtrl.FixedLB


