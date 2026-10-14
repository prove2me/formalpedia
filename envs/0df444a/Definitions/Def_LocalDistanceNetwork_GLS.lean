-- Prove2me | Definitions.Def_LocalDistanceNetwork_GLS
-- name    : LocalDistanceNetwork_GLS
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T20:23:00.842723+00:00
-- url     : https://prove2.me/theorems/5a4a4caa-e4b5-4d51-805f-ab967a2e4891
-- title:
--   Generalized least squares: quadratic form $Q$, GLS estimator, estimator covariance, Moore–Penrose inverse (Eqs. (B.1)–(B.2))
-- statement:
--   Basic objects of the generalized least-squares (GLS) problem of Appendix B.2. Throughout, $Y\in\mathbb R^{m}$ is the data vector (one entry per equation of the Distance Network), $X\in\mathbb R^{n}$ is the vector of optimization parameters, and $A\in\mathbb R^{m\times n}$ is the coefficient matrix, so that the theory prediction of the data is $AX$.
--
--   1. **Weighted quadratic form** (Eq. (B.2)). For a weight matrix $W\in\mathbb R^{m\times m}$,
--   $$
--   Q_{A,W,Y}(X)=(Y-AX)^{\mathsf T}\,W\,(Y-AX).
--   $$
--   With $W=C^{-1}$, where $C$ is the covariance matrix of the data, this is the $\chi^2$ of Eq. (B.1).
--
--   2. **GLS estimator matrix and estimate.**
--   $$
--   L_W=(A^{\mathsf T}WA)^{-1}A^{\mathsf T}W\in\mathbb R^{n\times m},\qquad \hat X_W(Y)=L_W\,Y .
--   $$
--
--   3. **Covariance of a linear estimator.** For $L\in\mathbb R^{n\times m}$ and a data covariance matrix $C$, the matrix $L\,C\,L^{\mathsf T}$, which is the covariance matrix of $LY$ when $Y$ has covariance $C$.
--
--   4. **Moore–Penrose inverse** (Penrose 1956). A matrix $P\in\mathbb R^{k\times m}$ is a Moore–Penrose inverse of $M\in\mathbb R^{m\times k}$ when the four Penrose equations hold:
--   $$
--   MPM=M,\qquad PMP=P,\qquad (MP)^{\mathsf T}=MP,\qquad (PM)^{\mathsf T}=PM .
--   $$
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** Index sets are arbitrary finite types. The inverse $(A^{\mathsf T}WA)^{-1}$ is Mathlib's matrix inverse, which returns $0$ for a singular matrix; every theorem that uses $L_W$ carries hypotheses (positive-definite $W$, injective $A$) under which $A^{\mathsf T}WA$ is invertible. The Moore–Penrose inverse is introduced as a predicate (the four Penrose equations) rather than as a function; its existence and uniqueness is a separate milestone.
-- source:
--   H0DN Collaboration (S. Casertano et al.), The Local Distance Network: A community consensus report on the measurement of the Hubble constant at ~1% precision, A&A 708, A166 (2026), https://doi.org/10.1051/0004-6361/202557993, Appendix B (p. 34) and Appendix B.2 (pp. 34-35), Eqs. (B.1)-(B.2)

import Mathlib

open Matrix

namespace LocalDistanceNetwork

/-- The generalized least-squares quadratic form of Eq. (B.2),
`Q(X) = (Y - A X)ᵀ W (Y - A X)`, for a coefficient matrix `A`, weight matrix `W`,
data vector `Y` and parameter vector `X`. With `W = C⁻¹` this is the `χ²` of Eq. (B.1). -/
def glsObjective {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (W : Matrix m m ℝ) (Y : m → ℝ) (X : n → ℝ) : ℝ :=
  (Y - A *ᵥ X) ⬝ᵥ (W *ᵥ (Y - A *ᵥ X))

/-- The generalized least-squares estimator matrix `(Aᵀ W A)⁻¹ Aᵀ W`. -/
noncomputable def glsEstimatorMatrix {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (W : Matrix m m ℝ) : Matrix n m ℝ :=
  (Aᵀ * W * A)⁻¹ * Aᵀ * W

/-- The generalized least-squares estimate `X̂ = (Aᵀ W A)⁻¹ Aᵀ W Y`. -/
noncomputable def glsEstimate {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (W : Matrix m m ℝ) (Y : m → ℝ) : n → ℝ :=
  glsEstimatorMatrix A W *ᵥ Y

/-- The covariance matrix `L C Lᵀ` of the linear estimator `L Y` when the data `Y`
have covariance matrix `C`. -/
def linearEstimatorCov {m n : Type*} [Fintype m]
    (L : Matrix n m ℝ) (C : Matrix m m ℝ) : Matrix n n ℝ :=
  L * C * Lᵀ

/-- `P` is a Moore–Penrose (pseudo)inverse of `M` (Penrose 1956): the four Penrose equations
`M P M = M`, `P M P = P`, `(M P)ᵀ = M P`, `(P M)ᵀ = P M` hold. -/
def IsMoorePenroseInverse {m k : Type*} [Fintype m] [Fintype k]
    (M : Matrix m k ℝ) (P : Matrix k m ℝ) : Prop :=
  M * P * M = M ∧ P * M * P = P ∧ (M * P)ᵀ = M * P ∧ (P * M)ᵀ = P * M

end LocalDistanceNetwork


