-- Prove2me | Definitions.Def_RobustSurvey_Affine_AARC
-- name    : RobustSurvey_Affine_AARC
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:02:05.680945+00:00
-- url     : https://prove2.me/theorems/2c36c01e-4680-4013-9849-b4487017a0ce
-- title:
--   Original affinely adjustable robust feasible set
-- statement:
--   For two-stage data $D$, centered ellipsoidal uncertainty $U_\rho$, and a full decision tuple $\chi=(x_1,q,Q)$, define
--   $$X_\rho=\{\chi:\ A_1(u)x_1+A_2(u)(Qu+q)\le b\text{ for every }u\in U_\rho\}.$$
--   The associated objective is $c^Tx_1$. This is the original affinely adjustable robust counterpart (AARC). Its feasibility is evaluated from the raw matrix data, independently of the printed quadratic coefficients and independently of the semidefinite certificate. The set retains $x_1,q,Q$ together; it is not projected onto the first-stage coordinates. Uncertainty ranges over the entire real set, with no sampling or discretization.
-- source:
--   Bertsimas, Brown and Caramanis, Theory and Applications of Robust Optimization, held PDF marked arXiv:1010.5445v1 (2010), https://arxiv.org/abs/1010.5445v1; SHA-256 25714e004b9b868fcb48997d3364800e379cd1be5f8b027ca6f50ee08f25ae50; anomalous revised-version date November 26, 2024; (4.10) and §4.3.1, printed pp. 22–25 / PDF pp. 23–26; X notation in Theorem 7, printed p. 26 / PDF p. 27.

import Definitions.Def_RobustSurvey_Affine_Data
import Definitions.Def_RobustSurvey_Affine_Ellipsoids
import Definitions.Def_RobustSurvey_Affine_Decision

namespace RobustSurvey.Affine

/-- Feasible full coefficient tuples for the original AARC, directly from (4.10). -/
def aarcFeasible {m n₁ n₂ L K : ℕ} (D : Data m n₁ n₂ L)
    (E : Ellipsoids L K) (ρ : ℝ) : Set (Decision n₁ n₂ L) :=
  {χ | D.RobustFeasible (E.uncertainty ρ) χ.x χ.policy}

/-- Both programs minimize this same first-stage cost. -/
noncomputable def aarcObjective {m n₁ n₂ L : ℕ} (D : Data m n₁ n₂ L)
    (χ : Decision n₁ n₂ L) : ℝ := D.objective χ.x

end RobustSurvey.Affine


