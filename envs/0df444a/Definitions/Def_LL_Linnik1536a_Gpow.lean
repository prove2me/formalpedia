-- Prove2me | Definitions.Def_LL_Linnik1536a_Gpow
-- name    : LL_Linnik1536a_Gpow
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-10-27T21:42:13.378409+00:00
-- url     : https://prove2.me/theorems/7c6fdb09-f650-4dba-bb0d-f7d4245407b2
-- title:
--   The power-of-two exponential sum $G_L(x)$
-- statement:
--   For $L\in\mathbb N$ and real $x$, $G_L(x)=\sum_{j=0}^{L-1} e(2^j x)$ with $e(t)=e^{2\pi i t}$, the exponential sum over powers of two in Pintz and Ruzsa, Acta Arith. 109 (2003), Section 4.

import Mathlib

namespace LL_Linnik1536a
open Real MeasureTheory Finset

noncomputable def Gpow (L : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ range L, Complex.exp (2 * π * Complex.I * ((2 : ℂ) ^ j * x))

end LL_Linnik1536a


