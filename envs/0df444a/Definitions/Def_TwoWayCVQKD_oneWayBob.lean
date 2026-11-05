-- Prove2me | Definitions.Def_TwoWayCVQKD_oneWayBob
-- name    : TwoWayCVQKD_oneWayBob
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:45:55.978349+00:00
-- url     : https://prove2.me/theorems/68eba9a1-73e6-4cb0-929b-5f36036d38b8
-- title:
--   Bob's output mode $B$ in the one-way model
-- statement:
--   The two quadratures $\hat Q_B,\hat P_B$ of the output mode $B$ of the attacked channel, as linear combinations of the one-way sources. In the protocol $Hom$ Bob's variable is $Q_B=\hat Q_B$.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, p.7 and Fig. 1 (p.2)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08
import Definitions.Def_TwoWayCVQKD_oneWayCloner
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, p.7: the quadratures of the
output mode `B` of the channel. -/
noncomputable def oneWayBob (T : ℝ) : QuadratureIndex 1 → OneWaySrc → ℝ :=
  fun i => (oneWayCloner T i.2).1

end TwoWayCVQKD


