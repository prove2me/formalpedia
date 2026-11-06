-- Prove2me | Definitions.Def_SilverRateLB_pSil
-- name    : SilverRateLB_pSil
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:20:10.128941+00:00
-- url     : https://prove2.me/theorems/af4ccc1c-c536-4849-9ed4-c9e41c47ee66
-- title:
--   The silver exponent $p_{\mathrm{sil}}=\log_2(1+\sqrt2)$
-- statement:
--   The **silver exponent** is
--   $$p_{\mathrm{sil}} := \log_2\bigl(1+\sqrt2\bigr)\approx 1.2716,$$
--   the base-2 logarithm of the silver ratio $1+\sqrt2$. It is the convergence exponent of the silver stepsize schedule of Altschuler and Parrilo, $f(x_n)-f_\star=O(n^{-p_{\mathrm{sil}}})$, and the exponent of the lower bound of Theorem 1.1.
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), §1, p. 3

import Mathlib

namespace SilverRateLB

/-- **The silver exponent** `p_sil := log₂(1 + √2) ≈ 1.2716`, the base-2 logarithm of the
silver ratio `1 + √2`.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, §1, p. 3:
"psil := log2(1 + √2) ≈ 1.2716".

**Formalization Note** `log₂` is `Real.logb 2`. -/
noncomputable def pSil : ℝ := Real.logb 2 (1 + Real.sqrt 2)

end SilverRateLB


