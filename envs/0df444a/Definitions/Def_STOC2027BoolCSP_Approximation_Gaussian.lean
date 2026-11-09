-- Prove2me | Definitions.Def_STOC2027BoolCSP_Approximation_Gaussian
-- name    : STOC2027BoolCSP_Approximation_Gaussian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:23.792258+00:00
-- url     : https://prove2.me/theorems/aa36ca9f-80e4-4075-99d6-b7652d7c96a0
-- title:
--   Correlation matrices, Gaussian orthant probability, the centered tilt $a(b)$, $F(b)$ and the potential of (9)
-- statement:
--   A **correlation matrix** is a real positive semidefinite $m\times m$ matrix with unit diagonal; $J$ is the all-ones matrix. For a positive semidefinite $R$, $N(0,R)$ is the centered Gaussian law on $\mathbb R^m$ with covariance $R$, and the **orthant probability** is $\Pr(X\ge0)$ for $X\sim N(0,R)$, the inequality being coordinatewise.
--
--   Let $\phi$ be the standard normal density. For $b>0$ the **centered tilt** $a(b)>0$ is the positive solution of
--   $$\int_{-\infty}^{b} x\,e^{a(b)x}\phi(x)\,dx=0,\qquad\text{and}\qquad F(b)=\log\int_{-\infty}^{b}e^{a(b)x}\phi(x)\,dx,$$
--   equation (8). The paper shows that this solution exists and is unique. For $b\in(0,\infty)^m$ and invertible $R$ the **variational potential** is
--   $$\Psi_R(b)=\sum_{i=1}^m F(b_i)-\tfrac12\,b^{\mathsf T}R^{-1}b,$$
--   the bracket on the right of equation (9).
--
--   These objects carry Theorem 4.1, Proposition 4.2 and Lemma 5.1.
--
--   **Formalization Note** $N(0,R)$ is Mathlib's `multivariateGaussian 0 R`. It is the Gaussian law only for positive semidefinite $R$ (otherwise Mathlib returns a Dirac mass), so every statement that uses it assumes positive semidefiniteness. The tilt is chosen by Hilbert's $\varepsilon$ among positive roots of the centering integral; since that root is unique, this picks the paper's $a(b)$. Existence and uniqueness are not assumed anywhere.
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 5, 7 (PDF 8, 10), Section 1.5 notation; Section 4, equation (8) and equation (9)

import Mathlib

namespace STOC2027BoolCSP.Approximation

open MeasureTheory ProbabilityTheory Matrix

/-- A correlation matrix: real positive semidefinite (in particular symmetric) with unit diagonal
(Section 1.5, printed p. 5). -/
def IsCorrelation {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  R.PosSemidef ∧ ∀ i, R i i = 1

/-- The all-ones matrix `J`. -/
def onesMat (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun _ _ => 1

/-- The orthant probability `Pr(X ≥ 0)` for `X ∼ N(0, R)` (coordinatewise inequality), with
`N(0, R)` Mathlib's centered multivariate Gaussian on `ℝ^m`. -/
noncomputable def orthantProb {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  (multivariateGaussian 0 R).real {x | ∀ i, 0 ≤ x i}

/-- The standard normal density `ϕ`. -/
noncomputable def phi (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

/-- The centering integral `∫_{-∞}^b x e^{a x} ϕ(x) dx` of equation (8). -/
noncomputable def centering (a b : ℝ) : ℝ :=
  ∫ x in Set.Iic b, x * Real.exp (a * x) * phi x

/-- The centered tilt `a(b)` of equation (8): the positive `a` with vanishing centering integral
(it exists and is unique for every `b > 0`; this definition picks it). -/
noncomputable def tilt (b : ℝ) : ℝ :=
  Classical.epsilon (fun a : ℝ => 0 < a ∧ centering a b = 0)

/-- `F(b) = log ∫_{-∞}^b e^{a(b) x} ϕ(x) dx` of equation (8). -/
noncomputable def Fpot (b : ℝ) : ℝ :=
  Real.log (∫ x in Set.Iic b, Real.exp (tilt b * x) * phi x)

/-- The variational potential `Σ_i F(b_i) − ½ bᵀ R⁻¹ b` on the right of equation (9). -/
noncomputable def potential {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (b : Fin m → ℝ) : ℝ :=
  ∑ i, Fpot (b i) - (1 / 2) * (b ⬝ᵥ (R⁻¹ *ᵥ b))

end STOC2027BoolCSP.Approximation


