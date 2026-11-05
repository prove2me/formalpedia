-- Prove2me | Definitions.Def_TwoWayCVQKD_zMat
-- name    : TwoWayCVQKD_zMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:45.672844+00:00
-- url     : https://prove2.me/theorems/5d49f733-d28a-41fd-b86b-5e97e5dd4373
-- title:
--   The matrix $\mathbf Z=\mathbf\Delta(1,-1)$
-- statement:
--   The $2\times 2$ diagonal matrix $\mathbf Z:=\mathbf\Delta(1,-1)$. It carries the opposite signs of the $\hat Q$ and $\hat P$ correlations of an EPR pair.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, below Eq. (4), p.6

import Mathlib

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, below Eq. (4), p.6:
`Z := Δ(1, -1)`. -/
def zMat : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![1, -1]

end TwoWayCVQKD


