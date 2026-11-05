-- Prove2me | Definitions.Def_TwoWayCVQKD_twoWayBob
-- name    : TwoWayCVQKD_twoWayBob
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:46:38.973854+00:00
-- url     : https://prove2.me/theorems/0a48cce1-418f-4dfa-9b38-4fb96291b1aa
-- title:
--   Bob's modes $B_1,B_2$ in the two-way model
-- statement:
--   Bob ends with two modes: $B_1$, the arm of his EPR pair that he kept, and $B_2$, the output of the second cloner. This definition lists their quadratures as linear combinations of the two-way sources, in the order $B_1,B_2$.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, p.8 and Fig. 5 (p.4)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08
import Definitions.Def_TwoWayCVQKD_twoWayBackward
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, p.8: Bob's two modes: `B₁`,
which he keeps from his EPR pair (mode index `0`), and the output `B₂` of the channel (mode
index `1`). -/
noncomputable def twoWayBob (T : ℝ) : QuadratureIndex 2 → TwoWaySrc → ℝ :=
  fun i => ![Pi.single (Sum.inr (Sum.inl (0, i.2))) 1, (twoWayBackward T i.2).1] i.1

end TwoWayCVQKD


