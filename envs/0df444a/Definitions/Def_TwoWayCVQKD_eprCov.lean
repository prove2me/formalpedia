-- Prove2me | Definitions.Def_TwoWayCVQKD_eprCov
-- name    : TwoWayCVQKD_eprCov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:42.18072+00:00
-- url     : https://prove2.me/theorems/3794cc8a-b5cb-4c26-817f-f0d07268ce5d
-- title:
--   The EPR covariance matrix $\mathbf V_{EPR}(V)$
-- statement:
--   The two-mode squeezed vacuum state (EPR source) of variance $V\ge 1$ has the covariance matrix
--   $$
--   \mathbf V_{EPR}(V)=\begin{pmatrix} V\mathbf I & \sqrt{V^2-1}\,\mathbf Z\\ \sqrt{V^2-1}\,\mathbf Z & V\mathbf I\end{pmatrix},\qquad \mathbf Z=\mathbf\Delta(1,-1).
--   $$
--   Bob's EPR source in the two-way protocols has variance $V$, and each of Eve's entangling cloners uses an EPR source of variance $W$.
--
--   **Formalization Note** The vacuum covariance matrix is the identity, as in the commutation relation $[\hat Y_l,\hat Y_m]=2i\Omega_{lm}$ of Eq. (1).
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eq. (4), p.6

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P19
import Definitions.Def_TwoWayCVQKD_modeBlocks
import Definitions.Def_TwoWayCVQKD_zMat
open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eq. (4), p.6: the covariance
matrix of the two-mode squeezed vacuum state (EPR source) of variance `V`,
`V_EPR(V) = [[V I, √(V² - 1) Z], [√(V² - 1) Z, V I]]`.

**Formalization Note** The vacuum covariance matrix is the identity (Eq. (1), `[Ŷ_l, Ŷ_m] = 2iΩ_lm`).
The formula is meant for `V ≥ 1`; every use in this mission has `1 ≤ V` or `V → ∞`. -/
noncomputable def eprCov (V : ℝ) : Cov 2 :=
  modeBlocks ![![V • (1 : Matrix (Fin 2) (Fin 2) ℝ), Real.sqrt (V ^ 2 - 1) • zMat],
    ![Real.sqrt (V ^ 2 - 1) • zMat, V • (1 : Matrix (Fin 2) (Fin 2) ℝ)]]

end TwoWayCVQKD


