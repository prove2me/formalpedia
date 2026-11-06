-- Prove2me | Definitions.Def_DRSub4633_sPar
-- name    : DRSub4633_sPar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:15.040532+00:00
-- url     : https://prove2.me/theorems/4af93470-f88f-48c0-b715-d8e2c9d9e7fc
-- title:
--   The threshold $s=1-b$
-- statement:
--   The number
--   $$s=1-b=\frac{32237}{250000}.$$
--   It is both the threshold separating small coordinates ($x_j\le s$) from large ones and the rate in the exponential factors $e^{\pm st}$ of the averaging weights.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4, Eq. (8), p.9

import Mathlib
import Definitions.Def_DRSub4633_bPar

namespace DRSub4633

/-- **The threshold and rate `s = 1 − b`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4, Eq. (8), p.9:
"`s = 1 − b = 32237/250000`". It is both the small/large coordinate threshold and the rate in the
factors `e^(±st)`. -/
noncomputable def sPar : ℝ := 1 - bPar

end DRSub4633


