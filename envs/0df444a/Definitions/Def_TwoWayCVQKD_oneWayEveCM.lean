-- Prove2me | Definitions.Def_TwoWayCVQKD_oneWayEveCM
-- name    : TwoWayCVQKD_oneWayEveCM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:55.926647+00:00
-- url     : https://prove2.me/theorems/c6190c69-daa7-455f-bbfa-909d2104a06f
-- title:
--   The matrix $\mathbf V_E(V_Q,V_P)$ of Eq. (17)
-- statement:
--   The paper writes Eve's one-way covariance matrix as a function of the variances of the two quadratures of the signal,
--   $$
--   \mathbf V_E(V_Q,V_P)=\begin{pmatrix}\mathbf\Delta[e_{V_Q},e_{V_P}] & \varphi\mathbf Z\\ \varphi\mathbf Z & W\mathbf I\end{pmatrix},
--   $$
--   so that Eq. (17) is $\mathbf V_E(V,V)$ and the conditional matrices of Eq. (21) are $\mathbf V_E(1,V)$ and $\mathbf V_E(1,1)$.
--
--   **Formalization Note** This is the displayed form only. It is the right-hand side of a milestone and is not used by the rates.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eqs. (17), (21), p.7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P19
import Definitions.Def_TwoWayCVQKD_modeBlocks
import Definitions.Def_TwoWayCVQKD_zMat
import Definitions.Def_TwoWayCVQKD_eVar
import Definitions.Def_TwoWayCVQKD_phiCoef
open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eqs. (17), (21), p.7: Eve's
covariance matrix `V_E(Vq, Vp) = [[Δ[e_Vq, e_Vp], φZ], [φZ, W I]]`.

**Formalization Note** This is a display of the paper, used only as the right-hand side of the
milestone `oneWay_output_cms`. The rates do not use it. -/
noncomputable def oneWayEveCM (T W Vq Vp : ℝ) : Cov 2 :=
  modeBlocks ![![Matrix.diagonal ![eVar T W Vq, eVar T W Vp], phiCoef T W • zMat],
    ![phiCoef T W • zMat, W • (1 : Matrix (Fin 2) (Fin 2) ℝ)]]

end TwoWayCVQKD


