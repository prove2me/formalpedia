-- Prove2me | Definitions.Def_RobustSurvey_Affine_PrintedCoefficients
-- name    : RobustSurvey_Affine_PrintedCoefficients
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:02:04.97263+00:00
-- url     : https://prove2.me/theorems/9884711a-b29d-41ec-84a5-eb5a4da804d9
-- title:
--   Literal printed coefficients for the semidefinite approximation
-- statement:
--   Given two-stage data and $\chi=(x_1,q^{(0)},q^{(1)},\ldots,q^{(L)})$, define for each row $i$
--   $$\alpha_i=-[A_1^{(0)}x_1+A_2^{(0)}q^{(0)}-b]_i,$$
--   $$\beta_i^{(l)}=-\frac{[A_1^{(l)}x_1+A_2^{(0)}q^{(l)}-b]_i}{2},$$
--   $$\Gamma_i^{(l,k)}=-\frac{[A_2^{(k)}q^{(l)}+A_2^{(l)}q^{(k)}]_i}{2}.$$
--   These are exactly the displayed coefficients, including the $-b$ term inside the bracket in $\beta$. In particular, the missing $A_2^{(l)}q^{(0)}$ term is not silently supplied. The resulting $\Gamma_i$ is symmetric. No identity between this quadratic expression and the original robust residual is asserted or assumed. The discrepancy is recorded as counterexample I1 in the mission's insight record.
-- source:
--   Bertsimas, Brown and Caramanis, Theory and Applications of Robust Optimization, held PDF marked arXiv:1010.5445v1 (2010), https://arxiv.org/abs/1010.5445v1; SHA-256 25714e004b9b868fcb48997d3364800e379cd1be5f8b027ca6f50ee08f25ae50; anomalous revised-version date November 26, 2024; coefficient display immediately before (4.13), printed p. 25 / PDF p. 26.

import Definitions.Def_RobustSurvey_Affine_Data
import Definitions.Def_RobustSurvey_Affine_Decision

open Matrix

namespace RobustSurvey.Affine

noncomputable def alpha {m n₁ n₂ L : ℕ} (D : Data m n₁ n₂ L)
    (χ : Decision n₁ n₂ L) (i : Fin m) : ℝ :=
  -((D.A₁₀ *ᵥ χ.x) i + (D.A₂₀ *ᵥ χ.q) i - D.b i)

/-- Literal printed beta on p. 25, including its b term. -/
noncomputable def beta {m n₁ n₂ L : ℕ} (D : Data m n₁ n₂ L)
    (χ : Decision n₁ n₂ L) (i : Fin m) (l : Fin L) : ℝ :=
  -(((D.A₁ l) *ᵥ χ.x) i + (D.A₂₀ *ᵥ (fun j => χ.Q j l)) i - D.b i) / 2

noncomputable def Gamma {m n₁ n₂ L : ℕ} (D : Data m n₁ n₂ L)
    (χ : Decision n₁ n₂ L) (i : Fin m) : Matrix (Fin L) (Fin L) ℝ :=
  fun l k => -(((D.A₂ k) *ᵥ (fun j => χ.Q j l)) i +
    ((D.A₂ l) *ᵥ (fun j => χ.Q j k)) i) / 2

end RobustSurvey.Affine


