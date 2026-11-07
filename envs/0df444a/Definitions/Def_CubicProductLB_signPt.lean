-- Prove2me | Definitions.Def_CubicProductLB_signPt
-- name    : CubicProductLB_signPt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:12:52.972421+00:00
-- url     : https://prove2.me/theorems/a835db24-a0b2-4159-8366-9d4a7278cdf1
-- title:
--   The sign point $x(z)$ of a Boolean vector
-- statement:
--   For $z \in \{0,1\}^n$, the **sign point** $x(z) \in X_n$ has $x_i = -1$ exactly when $z_i = 1$, and $x_i = 1$ otherwise. In $\mathbb F_3$ this is $x_i = 1 + z_i$. The map translates between the sign cube and Boolean negative-sign coordinates.
--
--   **Formalization Note** Bits are Booleans, with `true` for the bit $1$.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Eqs. (251)–(252), p.30

import Mathlib

namespace CubicProductLB

/-- The sign point of a Boolean vector: `x_i = -1` exactly when `z_i = 1`
(Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Eq. (251), p.30).

**Formalization Note** Bits are `Bool`, with `true` for the bit `1`. -/
def signPt {n : ℕ} (z : Fin n → Bool) : Fin n → ZMod 3 :=
  fun i => if z i then -1 else 1

end CubicProductLB


