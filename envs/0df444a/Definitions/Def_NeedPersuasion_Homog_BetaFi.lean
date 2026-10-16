-- Prove2me | Definitions.Def_NeedPersuasion_Homog_BetaFi
-- name    : NeedPersuasion_Homog_BetaFi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T01:04:57.123111+00:00
-- url     : https://prove2.me/theorems/16975868-4c35-4101-bbdc-82789964bea1
-- title:
--   Proposition 1, p. 16 — the constant β_fi
-- statement:
--   For the model of the congested service with low-need arrival rate $\lambda_L$ and full-information threshold $m_{fi}$, the constant of Proposition 1 is the ratio of two finite geometric sums,
--   $$\beta_{fi} = \frac{\sum_{n=0}^{m_{fi}-1} \lambda_L^n}{\sum_{n=0}^{m_{fi}} \lambda_L^n}.$$
--   It is the factor by which, in the homogeneous setting, the welfare of full information is guaranteed to approach the welfare of the optimal signaling mechanism.
--
--   **Formalization Note** The sums are `Finset.range (mfi M)` (indices $0,\dots,m_{fi}-1$) and `Finset.range (mfi M + 1)` (indices $0,\dots,m_{fi}$).
-- source:
--   arXiv:2005.07253v3, Proposition 1, p. 16

import Mathlib
import Definitions.Def_NeedPersuasion_Homog_Model

namespace NeedPersuasion.Homog

/-- `β_fi = (∑_{n=0}^{m_fi - 1} λ_L^n) / (∑_{n=0}^{m_fi} λ_L^n)` (Proposition 1, p. 16). -/
noncomputable def betaFi (M : Model) : ℝ :=
  (∑ n ∈ Finset.range (mfi M), M.lamL ^ n) / (∑ n ∈ Finset.range (mfi M + 1), M.lamL ^ n)

end NeedPersuasion.Homog


