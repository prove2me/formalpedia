-- Prove2me | Definitions.Def_TwoWayCVQKD_twoWayEveCM
-- name    : TwoWayCVQKD_twoWayEveCM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:45:03.515645+00:00
-- url     : https://prove2.me/theorems/f7e2f4b3-cac6-4c09-8313-a37a5929ea15
-- title:
--   The matrix $\mathbf V_E(\bar V_Q,\bar V_P)$ of Eq. (48)
-- statement:
--   The paper writes Eve's two-way covariance matrix as a function of the variances $\bar V_Q,\bar V_P$ of Alice's classical variables,
--   $$
--   \mathbf V_E(\bar V_Q,\bar V_P)=\begin{pmatrix} e_V\mathbf I & \varphi\mathbf Z & \mu'\mathbf I & \mathbf 0\\ \varphi\mathbf Z & W\mathbf I & \theta'\mathbf Z & \mathbf 0\\ \mu'\mathbf I & \theta'\mathbf Z & \mathbf\Lambda_E(\bar V_Q,\bar V_P) & \varphi\mathbf Z\\ \mathbf 0 & \mathbf 0 & \varphi\mathbf Z & W\mathbf I\end{pmatrix},
--   $$
--   with $\mathbf\Lambda_E(\bar V_Q,\bar V_P):=\gamma\mathbf I+(1-T)\mathbf\Delta(\bar V_Q,\bar V_P)$, $\mu':=-\sqrt{1-T}\,\mu$, $\theta':=-\sqrt{1-T}\,\theta$ and $\gamma:=T(1-T)V+(1-T)^2W+TW$. Eq. (48) is $\mathbf V_E(\bar V,\bar V)$, and the conditional matrices of Eq. (53) are $\mathbf V_E(0,\bar V)$ and $\mathbf V_E(0,0)$.
--
--   **Formalization Note** This is the displayed form only. It is the right-hand side of a milestone and is not used by the rates.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eqs. (48), (50)–(53), pp.8–9

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P19
import Definitions.Def_TwoWayCVQKD_modeBlocks
import Definitions.Def_TwoWayCVQKD_zMat
import Definitions.Def_TwoWayCVQKD_eVar
import Definitions.Def_TwoWayCVQKD_phiCoef
import Definitions.Def_TwoWayCVQKD_muCoef
import Definitions.Def_TwoWayCVQKD_thetaCoef
open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eqs. (48), (50)–(53), pp.8–9:
Eve's covariance matrix, the `4 × 4` block matrix with rows `[e_V I, φZ, μ'I, 0]`,
`[φZ, W I, θ'Z, 0]`, `[μ'I, θ'Z, Λ_E(Vq, Vp), φZ]`, `[0, 0, φZ, W I]`, where
`Λ_E(Vq, Vp) := γ I + (1 - T) Δ(Vq, Vp)`, `μ' := -√(1 - T) μ`, `θ' := -√(1 - T) θ` and
`γ := T(1 - T)V + (1 - T)²W + TW`.

**Formalization Note** This is a display of the paper, used only as the right-hand side of the
milestone `twoWay_output_cms`. The rates do not use it. -/
noncomputable def twoWayEveCM (T W V Vq Vp : ℝ) : Cov 4 :=
  modeBlocks
    ![![eVar T W V • (1 : Matrix (Fin 2) (Fin 2) ℝ), phiCoef T W • zMat,
        (-Real.sqrt (1 - T) * muCoef T W V) • (1 : Matrix (Fin 2) (Fin 2) ℝ), 0],
      ![phiCoef T W • zMat, W • (1 : Matrix (Fin 2) (Fin 2) ℝ),
        (-Real.sqrt (1 - T) * thetaCoef T W) • zMat, 0],
      ![(-Real.sqrt (1 - T) * muCoef T W V) • (1 : Matrix (Fin 2) (Fin 2) ℝ),
        (-Real.sqrt (1 - T) * thetaCoef T W) • zMat,
        (T * (1 - T) * V + (1 - T) ^ 2 * W + T * W) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          (1 - T) • Matrix.diagonal ![Vq, Vp],
        phiCoef T W • zMat],
      ![0, 0, phiCoef T W • zMat, W • (1 : Matrix (Fin 2) (Fin 2) ℝ)]]

end TwoWayCVQKD


