-- Prove2me | Definitions.Def_TwoWayCVQKD_twoWayHomBob
-- name    : TwoWayCVQKD_twoWayHomBob
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:47:42.112249+00:00
-- url     : https://prove2.me/theorems/b4c2424e-2974-4289-8f50-91024e8faec5
-- title:
--   Bob's variable $Q_B:=Q_{B_2}-TQ_{B_1}$ in $Hom^2$
-- statement:
--   In the protocol $Hom^2$ Bob measures $\hat Q_{B_1}$ and $\hat Q_{B_2}$ and decodes $Q_A$ through the output variable
--   $$
--   Q_B:=Q_{B_2}-T\,Q_{B_1}.
--   $$
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, p.9, above Eq. (63)

import Mathlib
import Definitions.Def_TwoWayCVQKD_twoWayBob

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, p.9: in `Hom²`, Bob decodes
`Q_A` by constructing the output variable `Q_B := Q_B₂ - T Q_B₁` from his measurements of `Q̂_B₁`
and `Q̂_B₂`. -/
noncomputable def twoWayHomBob (T : ℝ) : Fin 1 → TwoWaySrc → ℝ :=
  fun _ => twoWayBob T (1, 0) - T • twoWayBob T (0, 0)

end TwoWayCVQKD


