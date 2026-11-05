-- Prove2me | Definitions.Def_TwoWayCVQKD_muCoef
-- name    : TwoWayCVQKD_muCoef
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:58.429894+00:00
-- url     : https://prove2.me/theorems/6eaef294-5403-4fec-b670-c4691fcad1fe
-- title:
--   The coefficient $\mu$
-- statement:
--   The correlation coefficient between the modes $E'$ and $B$, $\mu:=(W-V)[(1-T)T]^{1/2}$.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eq. (19), p.7

import Mathlib

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eq. (19), p.7:
`μ := (W - V)[(1 - T)T]^{1/2}`. -/
noncomputable def muCoef (T W V : ℝ) : ℝ :=
  (W - V) * Real.sqrt ((1 - T) * T)

end TwoWayCVQKD


