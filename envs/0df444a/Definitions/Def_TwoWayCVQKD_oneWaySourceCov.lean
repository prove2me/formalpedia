-- Prove2me | Definitions.Def_TwoWayCVQKD_oneWaySourceCov
-- name    : TwoWayCVQKD_oneWaySourceCov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:45:37.903239+00:00
-- url     : https://prove2.me/theorems/073bb216-a221-475e-be41-35d88234ee2f
-- title:
--   Source covariance matrix of the one-way model
-- statement:
--   The sources of the one-way model are independent, so their covariance matrix is block diagonal, with blocks
--   $$
--   (V-1)\mathbf I,\quad \mathbf I,\quad \mathbf V_{EPR}(W),\quad \mathbf I,
--   $$
--   namely Alice's classical modulation $V(Q_A)=V(P_A)=V-1$, the shot noise $V(\hat Q_A|Q_A)=V(\hat P_A|P_A)=1$ of her signal mode, Eve's EPR source, and Bob's heterodyne vacuum.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, p.7, first paragraph of 'Secret-key rates of the one-way protocols'

import Mathlib
import Definitions.Def_TwoWayCVQKD_eprCov
import Definitions.Def_TwoWayCVQKD_OneWaySrc

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, p.7: the block-diagonal
covariance matrix of the one-way sources: `V(Q_A) = V(P_A) = V - 1`, unit shot noise of the signal
mode, Eve's `V_EPR(W)`, and the vacuum mode `0`. -/
noncomputable def oneWaySourceCov (V W : ℝ) : Matrix OneWaySrc OneWaySrc ℝ :=
  Matrix.fromBlocks ((V - 1) • 1) 0 0 (Matrix.fromBlocks 1 0 0 (Matrix.fromBlocks (eprCov W) 0 0 1))

end TwoWayCVQKD


