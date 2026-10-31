-- Prove2me | Definitions.Def_RobustSurvey_Affine_SDP
-- name    : RobustSurvey_Affine_SDP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:02:55.872904+00:00
-- url     : https://prove2.me/theorems/c542fa76-d307-4f07-9633-0f59a1602c36
-- title:
--   Explicit SDP certificate and its projected feasible set
-- statement:
--   For two-stage data, ellipsoid matrices, radius $\rho>0$, a decision $\chi$, and one multiplier vector $\lambda^{(i)}\in\mathbb R^K$ for each row, define
--   $$M_i(\chi,\lambda,\rho)=\begin{bmatrix}
--   \Gamma_i(\chi)+\rho^{-2}\sum_k\lambda_k^{(i)}S_k&\beta_i(\chi)\\
--   \beta_i(\chi)^T&\alpha_i(\chi)-\sum_k\lambda_k^{(i)}
--   \end{bmatrix}.$$
--   The finite SDP (4.14) minimizes $c^Tx_1$ over $(\chi,\lambda)$ subject to $\lambda_k^{(i)}\ge0$ for every $i,k$ and $M_i\succeq0$ for every $i$. Its objective is the original AARC objective and does not depend on $\lambda$. Define
--   $$X_\rho^{\mathrm{approx}}=\{\chi:\ \exists\lambda,\ \lambda\ge0\text{ and }M_i\succeq0\text{ for every }i\}.$$
--   Only multipliers are eliminated. The matrix is explicitly assembled with coordinate type $\mathrm{Fin}\,L\oplus\mathrm{Unit}$, putting the scalar coordinate last. Positive semidefiniteness includes real symmetry. The upper-left block's printed $\lambda_k$ is read as the same row's $\lambda_k^{(i)}$ used in the lower-right block and nonnegativity condition. There are $m$ blocks of order $L+1$ and $n_1+(L+1)n_2+mK$ real variables. No optimum, certificate existence, or correspondence with original feasibility is assumed.
-- source:
--   Bertsimas, Brown and Caramanis, Theory and Applications of Robust Optimization, held PDF marked arXiv:1010.5445v1 (2010), https://arxiv.org/abs/1010.5445v1; SHA-256 25714e004b9b868fcb48997d3364800e379cd1be5f8b027ca6f50ee08f25ae50; anomalous revised-version date November 26, 2024; Theorem 6, (4.14), printed pp. 25–26 / PDF pp. 26–27.

import Definitions.Def_RobustSurvey_Affine_AARC
import Definitions.Def_RobustSurvey_Affine_PrintedCoefficients

open scoped BigOperators
open Matrix

namespace RobustSurvey.Affine

/-- The precise block matrix (4.14), with the scalar coordinate last. -/
noncomputable def certificateMatrix {m n₁ n₂ L K : ℕ} (D : Data m n₁ n₂ L)
    (E : Ellipsoids L K) (ρ : ℝ) (χ : Decision n₁ n₂ L)
    (lam : Fin m → Fin K → ℝ) (i : Fin m) :
    Matrix (Fin L ⊕ Unit) (Fin L ⊕ Unit) ℝ :=
  Matrix.fromBlocks
    (Gamma D χ i + (ρ ^ 2)⁻¹ • ∑ k, lam i k • E.S k)
    (fun l _ => beta D χ i l)
    (fun _ l => beta D χ i l)
    (fun _ _ => alpha D χ i - ∑ k, lam i k)

/-- Explicit finite SDP: nonnegative multipliers and one PSD block per constraint. -/
def sdpFeasible {m n₁ n₂ L K : ℕ} (D : Data m n₁ n₂ L)
    (E : Ellipsoids L K) (ρ : ℝ) (χ : Decision n₁ n₂ L)
    (lam : Fin m → Fin K → ℝ) : Prop :=
  (∀ i k, 0 ≤ lam i k) ∧ ∀ i, (certificateMatrix D E ρ χ lam i).PosSemidef

noncomputable def sdpObjective {m n₁ n₂ L K : ℕ} (D : Data m n₁ n₂ L)
    (χ : Decision n₁ n₂ L) (_lam : Fin m → Fin K → ℝ) : ℝ :=
  D.objective χ.x

/-- Eliminate only the SDP multipliers, retaining the entire policy coefficient tuple. -/
def approxFeasible {m n₁ n₂ L K : ℕ} (D : Data m n₁ n₂ L)
    (E : Ellipsoids L K) (ρ : ℝ) : Set (Decision n₁ n₂ L) :=
  {χ | ∃ lam : Fin m → Fin K → ℝ, sdpFeasible D E ρ χ lam}

end RobustSurvey.Affine


