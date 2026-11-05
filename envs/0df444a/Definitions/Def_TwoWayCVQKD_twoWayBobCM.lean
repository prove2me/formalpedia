-- Prove2me | Definitions.Def_TwoWayCVQKD_twoWayBobCM
-- name    : TwoWayCVQKD_twoWayBobCM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:45.844255+00:00
-- url     : https://prove2.me/theorems/aae8eaf7-cf3d-4f7e-bb1c-2696c1468cb2
-- title:
--   The matrix $\mathbf V_B(\bar V_Q,\bar V_P)$ of Eq. (47)
-- statement:
--   The paper writes Bob's two-way covariance matrix as a function of the variances $\bar V_Q,\bar V_P$ of Alice's classical variables,
--   $$
--   \mathbf V_B(\bar V_Q,\bar V_P)=\begin{pmatrix}V\mathbf I & T\sqrt{V^2-1}\,\mathbf Z\\ T\sqrt{V^2-1}\,\mathbf Z & \mathbf\Lambda_B(\bar V_Q,\bar V_P)\end{pmatrix},\qquad \mathbf\Lambda_B(\bar V_Q,\bar V_P):=[T^2V+(1-T^2)W]\mathbf I+T\mathbf\Delta(\bar V_Q,\bar V_P).
--   $$
--   Eq. (47) is $\mathbf V_B(\bar V,\bar V)$, and the conditional matrices of Eq. (53) are $\mathbf V_B(0,\bar V)$ and $\mathbf V_B(0,0)$.
--
--   **Formalization Note** This is the displayed form only. It is the right-hand side of a milestone and is not used by the rates.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eqs. (47), (49), (53), pp.8–9

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P19
import Definitions.Def_TwoWayCVQKD_modeBlocks
import Definitions.Def_TwoWayCVQKD_zMat
open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eqs. (47), (49), (53), pp.8–9:
Bob's covariance matrix `V_B(Vq, Vp) = [[V I, T√(V² - 1) Z], [T√(V² - 1) Z, Λ_B(Vq, Vp)]]`, with
`Λ_B(Vq, Vp) := [T²V + (1 - T²)W] I + T Δ(Vq, Vp)`, where `Vq`, `Vp` are the variances of Alice's
two classical variables.

**Formalization Note** This is a display of the paper, used only as the right-hand side of the
milestone `twoWay_output_cms`. The rates do not use it. -/
noncomputable def twoWayBobCM (T W V Vq Vp : ℝ) : Cov 2 :=
  modeBlocks ![![V • (1 : Matrix (Fin 2) (Fin 2) ℝ), (T * Real.sqrt (V ^ 2 - 1)) • zMat],
    ![(T * Real.sqrt (V ^ 2 - 1)) • zMat,
      (T ^ 2 * V + (1 - T ^ 2) * W) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        T • Matrix.diagonal ![Vq, Vp]]]

end TwoWayCVQKD


