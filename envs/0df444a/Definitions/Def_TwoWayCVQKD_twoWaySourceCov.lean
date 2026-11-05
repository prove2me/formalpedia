-- Prove2me | Definitions.Def_TwoWayCVQKD_twoWaySourceCov
-- name    : TwoWayCVQKD_twoWaySourceCov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:45:51.52153+00:00
-- url     : https://prove2.me/theorems/81e84138-3b28-465f-ad6a-25a13b1094d4
-- title:
--   Source covariance matrix of the two-way model
-- statement:
--   The sources of the two-way model are independent, so their covariance matrix is block diagonal, with blocks
--   $$
--   \bar V\mathbf I,\quad \mathbf V_{EPR}(V),\quad \mathbf V_{EPR}(W),\quad \mathbf V_{EPR}(W),\quad \mathbf I,\quad \mathbf I,
--   $$
--   namely Alice's modulation $V(Q_A)=V(P_A)=\bar V$ with $\langle Q_AP_A\rangle=0$, Bob's EPR source, the EPR sources of Eve's two cloners, and the two heterodyne vacua. The two cloners are independent because the attack is a one-mode attack.
--
--   **Formalization Note** The asymptotic rates use $\bar V=V-1$, the identical resources of p.9.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, p.8, first paragraph of 'Secret-key rates of the two-way protocols'

import Mathlib
import Definitions.Def_TwoWayCVQKD_eprCov
import Definitions.Def_TwoWayCVQKD_TwoWaySrc

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, p.8: the block-diagonal
covariance matrix of the two-way sources for a triple `Vbar, V, W`: `V(Q_A) = V(P_A) = Vbar`,
Bob's `V_EPR(V)`, two independent `V_EPR(W)` (one-mode attack, the two paths are attacked
incoherently), and the two vacuum modes.

**Formalization Note** The rates use `Vbar = V - 1`, the "identical resources" of p.9. -/
noncomputable def twoWaySourceCov (Vbar V W : ℝ) : Matrix TwoWaySrc TwoWaySrc ℝ :=
  Matrix.fromBlocks (Vbar • 1) 0 0 (Matrix.fromBlocks (eprCov V) 0 0
    (Matrix.fromBlocks (eprCov W) 0 0 (Matrix.fromBlocks (eprCov W) 0 0 (Matrix.fromBlocks 1 0 0 1))))

end TwoWayCVQKD


