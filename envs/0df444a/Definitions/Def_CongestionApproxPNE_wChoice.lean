-- Prove2me | Definitions.Def_CongestionApproxPNE_wChoice
-- name    : CongestionApproxPNE_wChoice
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:16:10.163996+00:00
-- url     : https://prove2.me/theorems/bfaa074e-db2d-4e3e-bfb6-6a1797d5a119
-- title:
--   The light weight of the parameter choice, $w=\ln d/(2d)$
-- statement:
--   For an integer $d$, the light-player weight used in the asymptotic part of the proof of Theorem 1 is
--
--   $$
--   w=\frac{\ln d}{2d}.
--   $$
-- source:
--   Christodoulou et al., Existence and Complexity of Approximate Equilibria in Weighted Congestion Games, arXiv:2002.07466v3, proof of Theorem 1, p.6 (PDF p.7), choice of w

import Mathlib

set_option autoImplicit false

namespace CongestionApproxPNE

/-- **The light weight of the parameter choice, `w = ln d / (2d)`.**
Christodoulou, Gairing, Giannakopoulos, Poças, Waldmann, arXiv:2002.07466v3, proof of Theorem 1,
p.6.

**Formalization Note** `Real.log` is `ln`. -/
noncomputable def wChoice (d : ℕ) : ℝ :=
  Real.log d / (2 * d)

end CongestionApproxPNE


