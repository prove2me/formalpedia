-- Prove2me | Definitions.Def_DRJointCC_Individual_Supplement_ZICC
-- name    : DRJointCC_Individual_Supplement_ZICC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:23:32.915579+00:00
-- url     : https://prove2.me/theorems/9464fbd2-6f4e-4889-ac99-8aa01a2bcd6d
-- title:
--   (8), p. 6 — the worst-case CVaR feasible set $\mathcal Z^{\mathrm{ICC}}$ of an individual chance constraint
-- statement:
--   Throughout, $\mathcal P$ is the set of all probability distributions on $\mathbb R^k$ with mean $\mu$ and covariance matrix $\Sigma\succ0$, $\Omega=\begin{bmatrix}\Sigma+\mu\mu^\top&\mu\\\mu^\top&1\end{bmatrix}$ is the second-order moment matrix, $\langle X,Y\rangle=\mathrm{Tr}(XY)$, and $\epsilon\in(0,1)$.
--
--   Let $y^0:\mathbb R^n\to\mathbb R$ and $\boldsymbol y:\mathbb R^n\to\mathbb R^k$ describe an uncertain affine constraint $y^0(x)+y(x)^\top\tilde\xi\le0$ in the decision $x\in\mathbb R^n$. The **worst-case CVaR feasible set** of this individual chance constraint is
--
--   $$
--   \mathcal Z^{\mathrm{ICC}}=\Big\{x\in\mathbb R^n:\ \sup_{\mathbb P\in\mathcal P}\mathbb P\text{-}\mathrm{CVaR}_\epsilon\big(y^0(x)+y(x)^\top\tilde\xi\big)\le0\Big\},
--   $$
--
--   where $\mathbb P\text{-}\mathrm{CVaR}_\epsilon(L)=\inf_{\beta\in\mathbb R}\{\beta+\frac1\epsilon\mathbb E_{\mathbb P}[(L-\beta)^+]\}$.
--
--   By (7) this set is a conservative approximation of the distributionally robust individual chance constraint; Theorem 2.1 represents it by linear matrix inequalities.
--
--   **Formalization Note** The worst-case CVaR is the published extended-real `DRJointCC.Individual.wcCVaR`. In the paper $y^0$ and $y$ are affine in $x$ (p. 2); here they are arbitrary maps, which contains the affine case.
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 6, (8); p. 2 (y^0, y)

import Mathlib
import Definitions.Def_DRJointCC_Individual_Moments

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Individual.Supplement

/-- The worst-case CVaR feasible set of the individual chance constraint, (8), p. 6:
`𝒵^ICC = { x ∈ ℝ^n : sup_{ℙ ∈ 𝒫} ℙ-CVaR_ε(y⁰(x) + y(x)ᵀξ̃) ≤ 0 }`.
The maps `y⁰ : ℝ^n → ℝ` and `y : ℝ^n → ℝ^k` are arguments (affine in the paper, p. 2). -/
def ZICC {n k : ℕ} (ε : ℝ) (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ)
    (y0 : (Fin n → ℝ) → ℝ) (y : (Fin n → ℝ) → Fin k → ℝ) : Set (Fin n → ℝ) :=
  {x | DRJointCC.Individual.wcCVaR ε μ Sig (fun ξ => y0 x + y x ⬝ᵥ ξ) ≤ 0}

end DRJointCC.Individual.Supplement


