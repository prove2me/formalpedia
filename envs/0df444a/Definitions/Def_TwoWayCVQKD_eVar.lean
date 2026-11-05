-- Prove2me | Definitions.Def_TwoWayCVQKD_eVar
-- name    : TwoWayCVQKD_eVar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:00.708839+00:00
-- url     : https://prove2.me/theorems/52d2a824-2ff2-48e6-b79d-453cc9ae7c38
-- title:
--   Eve's output variance $e_V$
-- statement:
--   The variance of the quadratures of Eve's output mode $E'$ in the one-way model, $e_V:=(1-T)V+TW$. Its value at $V=1$ is the conditional variance $e_1=(1-T)+TW$ of Eq. (15).
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eqs. (13), (15), p.7

import Mathlib

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eqs. (13), (15), p.7:
`e_V := (1 - T)V + TW`, with `e₁ = (1 - T) + TW` the case `V = 1`. -/
def eVar (T W V : ℝ) : ℝ :=
  (1 - T) * V + T * W

end TwoWayCVQKD


