-- Prove2me | Definitions.Def_TwoWayCVQKD_oneWayBobCM
-- name    : TwoWayCVQKD_oneWayBobCM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:56.86696+00:00
-- url     : https://prove2.me/theorems/d8da37e2-a977-4a9c-a85d-3737e776c362
-- title:
--   The matrix $\mathbf V_B(V_Q,V_P)$ of Eq. (16)
-- statement:
--   The paper writes Bob's one-way covariance matrix as a function of the variances of the two quadratures of the signal,
--   $$
--   \mathbf V_B(V_Q,V_P)=\mathbf\Delta(b_{V_Q},b_{V_P}),
--   $$
--   so that Eq. (16) is $\mathbf V_B(V,V)$ and the conditional matrices of Eq. (21) are $\mathbf V_B(1,V)$ and $\mathbf V_B(1,1)$.
--
--   **Formalization Note** This is the displayed form only. It is the right-hand side of a milestone and is not used by the rates.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eqs. (16), (21), p.7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P19
import Definitions.Def_TwoWayCVQKD_modeBlocks
import Definitions.Def_TwoWayCVQKD_bVar
open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eqs. (16), (21), p.7: Bob's
covariance matrix `V_B(Vq, Vp) = Δ(b_Vq, b_Vp)`, a function of the variances of the two
quadratures of Alice's signal.

**Formalization Note** This is a display of the paper, used only as the right-hand side of the
milestone `oneWay_output_cms`. The rates do not use it. -/
def oneWayBobCM (T W Vq Vp : ℝ) : Cov 1 :=
  modeBlocks ![![Matrix.diagonal ![bVar T W Vq, bVar T W Vp]]]

end TwoWayCVQKD


