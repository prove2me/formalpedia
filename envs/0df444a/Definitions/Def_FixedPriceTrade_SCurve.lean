-- Prove2me | Definitions.Def_FixedPriceTrade_SCurve
-- name    : FixedPriceTrade_SCurve
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:40:45.330199+00:00
-- url     : https://prove2.me/theorems/9f66be92-6794-493c-a8ab-2ec708e85dd2
-- title:
--   The scalar curve $D_C$, $y_e$, $\mathcal I_C$, $\mathcal I$, $\tau$, $S$ and the closed form (5)
-- statement:
--   For $1/4<C<1/2$ define
--   $$
--   D_C(y)=1-y+Cy^2,\qquad y_e(C)=\frac{1-2C}{C(1-C)},\qquad \mathcal I_C(y)=\int_0^y\frac{dr}{D_C(r)},\qquad \mathcal I(C)=\mathcal I_C(y_e(C)),
--   $$
--   and the **scalar curve**
--   $$
--   \tau(C)=\frac{C^2}{1-2C}\,e^{-\mathcal I(C)/2},\qquad S(C)=C\,(2+\mathcal I(C)).
--   $$
--   With $\omega=\sqrt{C-1/4}$ and principal arctangents, the closed form printed in (5) and (47) is
--   $$
--   \frac1\omega\Big(\arctan\frac{1-3C}{2(1-C)\omega}+\arctan\frac1{2\omega}\Big).
--   $$
--   $\tau(C)$ is the initial state at which the arc with curvature parameter $C$ is optimal, and $S(C)$ is the optimal value of the control functional there; the welfare constant is $1/S(C_*)$ at the root of $S=1+\tau$.
--
--   **Formalization Note** All functions are total on $\mathbb R$. $D_C$ and $\mathcal I_C$ are also used in §6 for other $C$, only where $D_C>0$ on $[0,y]$. The closed form is a separate definition; that it equals $\mathcal I(C)$ is milestone (5).
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 26832346…), §3, (3)–(5), p.10

import Mathlib

set_option autoImplicit false

namespace FixedPriceTrade

open Real

/-- The reciprocal quadratic `D_C(y) = 1 − y + C y²` ((3), p.10). -/
def Dq (C y : ℝ) : ℝ := 1 - y + C * y ^ 2

/-- `y_e(C) = (1 − 2C)/(C(1 − C))` ((3), p.10). -/
noncomputable def yE (C : ℝ) : ℝ := (1 - 2 * C) / (C * (1 - C))

/-- The running integral `I_C(y) = ∫_0^y dr / D_C(r)` ((3), p.10).

**Formalization Note.** Used only where `D_C > 0` on `[0, y]`: on all of `ℝ` for
`1/4 < C < 1/2`, and under the side conditions of (19) in §6. -/
noncomputable def ICrun (C y : ℝ) : ℝ := ∫ r in (0 : ℝ)..y, 1 / Dq C r

/-- `I(C) = I_C(y_e(C))` ((3), p.10). -/
noncomputable def Ical (C : ℝ) : ℝ := ICrun C (yE C)

/-- `τ(C) = C²/(1 − 2C) · e^{−I(C)/2}` ((4), p.10). Used for `1/4 < C < 1/2`. -/
noncomputable def tauCurve (C : ℝ) : ℝ := C ^ 2 / (1 - 2 * C) * exp (-(Ical C) / 2)

/-- The arctangent closed form of `I(C)` printed in (5), p.10 and (47), p.22: with
`ω = √(C − 1/4)` and principal arctangents,
`(1/ω)(arctan((1 − 3C)/(2(1 − C)ω)) + arctan(1/(2ω)))`. Used for `1/4 < C < 1/2`. -/
noncomputable def IArctan (C : ℝ) : ℝ :=
  1 / sqrt (C - 1 / 4) *
    (arctan ((1 - 3 * C) / (2 * (1 - C) * sqrt (C - 1 / 4))) +
      arctan (1 / (2 * sqrt (C - 1 / 4))))

/-- **The scalar curve** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact Welfare Guarantee of
Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…), §3, (3)–(4), p.10:
for `1/4 < C < 1/2`, `S(C) = C(2 + I(C))`, together with `D_C`, `y_e`, `I_C`, `I`, `τ` above
and the closed form (5).

**Formalization Note.** All functions are total on `ℝ`; the paper uses them for
`1/4 < C < 1/2` (and `D_C`, `I_C` on the larger range of §6 where `D_C > 0`), and every statement
of the mission evaluates them only there. `I_C` is a Lebesgue interval integral. -/
noncomputable def SCurve (C : ℝ) : ℝ := C * (2 + Ical C)

end FixedPriceTrade


