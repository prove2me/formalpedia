-- Prove2me | Definitions.Def_TwoWayCVQKD_thetaCoef
-- name    : TwoWayCVQKD_thetaCoef
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:01.008133+00:00
-- url     : https://prove2.me/theorems/72bb1f3b-9f69-4eb7-920d-cfcc9e3c167c
-- title:
--   The coefficient $\theta$
-- statement:
--   The correlation coefficient between the modes $E''$ and $B$, $\theta:=[(1-T)(W^2-1)]^{1/2}$.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eq. (20), p.7

import Mathlib

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eq. (20), p.7:
`θ := [(1 - T)(W² - 1)]^{1/2}`. -/
noncomputable def thetaCoef (T W : ℝ) : ℝ :=
  Real.sqrt ((1 - T) * (W ^ 2 - 1))

end TwoWayCVQKD


