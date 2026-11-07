-- Prove2me | Definitions.Def_Max3CutHard_betaT
-- name    : Max3CutHard_betaT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:46.691179+00:00
-- url     : https://prove2.me/theorems/fa398a02-6dcb-4b0d-9dd3-0ac3c4df8bda
-- title:
--   The constants $\beta_t$ of (3)
-- statement:
--   The constants
--
--   $$\beta_0=32,\qquad\beta_1=\beta_2=9$$
--
--   of equation (3).
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Proof of Theorem 1.1, Eq. (3), p.6

import Mathlib

namespace Max3CutHard

/-- **The constants `β_t` of (3).** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Proof of Theorem 1.1, Eq. (3), p.6: "`β0 = 32`,
`β1 = β2 = 9`". -/
noncomputable def betaT (t : ZMod 3) : ℝ := if t = 0 then 32 else 9

end Max3CutHard


