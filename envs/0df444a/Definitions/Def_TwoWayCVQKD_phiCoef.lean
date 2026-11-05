-- Prove2me | Definitions.Def_TwoWayCVQKD_phiCoef
-- name    : TwoWayCVQKD_phiCoef
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:58.037441+00:00
-- url     : https://prove2.me/theorems/b175f115-b4ed-44df-a053-10103b44074b
-- title:
--   The coefficient $\varphi$
-- statement:
--   The correlation coefficient between Eve's modes $E'$ and $E''$, $\varphi:=[T(W^2-1)]^{1/2}$.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eq. (19), p.7

import Mathlib

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eq. (19), p.7:
`φ := [T(W² - 1)]^{1/2}`. -/
noncomputable def phiCoef (T W : ℝ) : ℝ :=
  Real.sqrt (T * (W ^ 2 - 1))

end TwoWayCVQKD


