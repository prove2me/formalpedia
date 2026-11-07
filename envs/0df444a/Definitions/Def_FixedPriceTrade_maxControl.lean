-- Prove2me | Definitions.Def_FixedPriceTrade_maxControl
-- name    : FixedPriceTrade_maxControl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:41:32.863197+00:00
-- url     : https://prove2.me/theorems/c0d5b055-e494-4093-bd15-032546e06f10
-- title:
--   The maximizing control $h_C$ of (34) and the survival functions $H_C$, $H_{\eta,C}$ of (46)
-- statement:
--   For $1/4<C<1/2$ and $d=\tau(C)$, the **maximizing control** $h_C$ is $0$ on $[0,C)$; on the middle arc $t=C(1+y)$, $0\le y\le y_e(C)$,
--   $$
--   h_C(t)=\frac{y\,g(t)}{D_C(y)},\qquad g(t)=\tau(C)\sqrt{D_C(y)}\,e^{\mathcal I_C(y)/2};
--   $$
--   and $1$ on the rest of $[0,1]$, an arc of length $C^2/(1-C)$. From it,
--   $$
--   H_C(s)=h_C(1-s),\qquad H_{\eta,C}(s)=\eta+(1-\eta)H_C(s)\qquad(0\le s\le1).
--   $$
--   $H_{\eta,C}$ is the buyer survival function of the hard family; at $C=C_*$ and $\eta\downarrow0$ it approaches the welfare constant.
--
--   **Formalization Note** The formula uses the running integral $\mathcal I_C(y)$, not $\mathcal I(C)$. Functions on $\mathbb R$; only their values on $[0,1]$ are used.
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 26832346…), Theorem C, (34), p.19; §9, (46), p.22

import Mathlib
import Definitions.Def_FixedPriceTrade_SCurve

set_option autoImplicit false

namespace FixedPriceTrade

open Real

/-- **The maximizing control** `h_C` — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact Welfare Guarantee
of Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…), Theorem C, (34),
p.19, at `d = τ(C)` (§9, (46), p.22): a zero arc on `[0, C)`; on the middle arc
`t = C(1 + y)`, `0 ≤ y ≤ y_e(C)`, the value `h(t) = y g(t)/D_C(y)` with
`g(t) = τ(C) √D_C(y) e^{I_C(y)/2}`; and the value `1` on the rest of `[0, 1]`.

**Formalization Note.** A function on `ℝ`, used for `1/4 < C < 1/2`. The middle arc ends at
`t = C(1 + y_e(C)) = 1 − C²/(1 − C)`, so the last arc has length `C²/(1 − C)`. The formula uses the
running integral `I_C(y)`, not `I(C)`. -/
noncomputable def maxControl (C t : ℝ) : ℝ :=
  if t < C then 0
  else if t ≤ C * (1 + yE C) then
    (t / C - 1) * (tauCurve C * sqrt (Dq C (t / C - 1)) * exp (ICrun C (t / C - 1) / 2)) /
      Dq C (t / C - 1)
  else 1

/-- `H_C(s) = h_C(1 − s)` ((46), p.22). -/
noncomputable def HC (C s : ℝ) : ℝ := maxControl C (1 - s)

/-- `H_{η,C}(s) = η + (1 − η) H_C(s)` for `0 ≤ s ≤ 1` ((46), p.22). -/
noncomputable def Heta (η C s : ℝ) : ℝ := η + (1 - η) * HC C s

end FixedPriceTrade


