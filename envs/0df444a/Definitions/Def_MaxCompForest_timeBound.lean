-- Prove2me | Definitions.Def_MaxCompForest_timeBound
-- name    : MaxCompForest_timeBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:13.835675+00:00
-- url     : https://prove2.me/theorems/f824a3eb-5fe7-46e5-aec4-94c3c53547a4
-- title:
--   The running-time bound of Theorem 3.1
-- statement:
--   The bit-time bound of the forest algorithm for constants $C,a,b$:
--   $$
--   \Big\lceil\Big(\frac{Ckq}{\gamma\varepsilon}\Big)^{ak}(L+2)^{b}\Big\rceil .
--   $$
--   It has the shape $(Ckq/(\gamma\varepsilon))^{O(k)}\mathrm{poly}(L)$ of (3.4), with $a$ the hidden exponent and $b$ the degree of the polynomial in the input length.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), (3.4), p.15

import Mathlib

namespace MaxCompForest

/-- **The time bound** `⌈(C k q / (γ ε))^(a k) · (L + 2)^b⌉`, the shape of (3.4).
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), (3.4), p.15.

**Formalization Note.** `q` and `k` are cast to `ℚ` before the division. The `+ 2` makes the base of the
polynomial factor at least `2`. At `k = 0` the exponent is `0` and the bound is `(L + 2)^b`. -/
def timeBound (C a b k q : ℕ) (γ ε : ℚ) (L : ℕ) : ℕ :=
  ⌈(((C : ℚ) * k * q) / (γ * ε)) ^ (a * k) * ((L : ℚ) + 2) ^ b⌉₊

end MaxCompForest


