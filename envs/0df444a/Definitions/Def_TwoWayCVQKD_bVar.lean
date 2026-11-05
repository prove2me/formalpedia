-- Prove2me | Definitions.Def_TwoWayCVQKD_bVar
-- name    : TwoWayCVQKD_bVar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:57.536553+00:00
-- url     : https://prove2.me/theorems/fdaa6a1a-5f77-4ad4-a405-b0a4ec4dabc5
-- title:
--   Bob's output variance $b_V$
-- statement:
--   The variance of Bob's output quadratures in the one-way model, $b_V:=(1-T)W+TV$. Its value at $V=1$ is the conditional variance $b_1=(1-T)W+T$ of Eq. (14).
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eqs. (12), (14), p.7

import Mathlib

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eqs. (12), (14), p.7:
`b_V := (1 - T)W + TV`, with `b₁ = (1 - T)W + T` the case `V = 1`. -/
def bVar (T W V : ℝ) : ℝ :=
  (1 - T) * W + T * V

end TwoWayCVQKD


