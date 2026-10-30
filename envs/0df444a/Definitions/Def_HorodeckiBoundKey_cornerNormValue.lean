-- Prove2me | Definitions.Def_HorodeckiBoundKey_cornerNormValue
-- name    : HorodeckiBoundKey_cornerNormValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:41.456129+00:00
-- url     : https://prove2.me/theorems/77902003-a905-40f5-828b-60ff48a0ef02
-- title:
--   The value $f(p,l,n)$ of (13)
-- statement:
--   For real $p$ and $l, n\in\mathbb N$, let
--   $$
--   f(p,l,n) = \frac12\Big(1-\frac1{2^l}\Big)^n\,\frac{1}{1+\big(\frac{1-2p}{2p}\big)^n},
--   $$
--   the right-hand side of (13): the trace norm of the off-diagonal block of the state $\rho'$ of (12). For $1/4 < p\le 1/2$ the ratio $\frac{1-2p}{2p}$ lies in $[0,1)$, which is why the value can approach $1/2$.
--
--   **Formalization Note** Real-valued, with Lean's total division; it is used only for $p>0$.
-- source:
--   Horodecki, Horodecki, Horodecki, Oppenheim, Secure key from bound entanglement, arXiv:quant-ph/0309110v2, eq. (13), p.3

import Mathlib

namespace HorodeckiBoundKey

/-- Horodecki, Horodecki, Horodecki, Oppenheim, arXiv:quant-ph/0309110v2, eq. (13), p.3: the
right-hand side
`f(p, l, n) = ½ (1 − 1/2^l)ⁿ · 1 / (1 + ((1 − 2p)/(2p))ⁿ)`
of (13), the trace norm of the off-diagonal block of the state `ρ′` of (12).

**Formalization Note.** Real-valued. The division by `2p` is Lean's total division; it is used
only for `0 < p`, where it is the page's value. -/
noncomputable def cornerNormValue (p : ℝ) (l n : ℕ) : ℝ :=
  1 / 2 * (1 - 1 / 2 ^ l) ^ n * (1 / (1 + ((1 - 2 * p) / (2 * p)) ^ n))

end HorodeckiBoundKey


