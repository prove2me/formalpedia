-- Prove2me | Definitions.Def_BoydADMM_ModelFit_Basic
-- name    : BoydADMM_ModelFit_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:17:58.109272+00:00
-- url     : https://prove2.me/theorems/e6ffdc5e-6793-48f1-ab1a-1463159a696d
-- title:
--   Chapter 8 objects: shifted soft thresholding, ‖·‖₁, the group-lasso block objective and the ridge point
-- statement:
--   This file fixes the objects of Chapter 8 ("Distributed Model Fitting") of Boyd, Parikh, Chu, Peleato and Eckstein that the closed-form ADMM updates of the chapter are written with. Vectors live in $\mathbb R^n$ with the Euclidean norm $\|\cdot\|_2$; a matrix $A\in\mathbb R^{m\times n}$ acts on $\mathbb R^n$ in the usual way.
--
--   **Soft thresholding** $S_\kappa$ (§4.4.3, p. 32) comes from the shared item `BoydADMM.Prox.Basic`. This file adds:
--
--   1. **Shifted soft thresholding** (§8.3.4, p. 71): for a number of blocks $N\ge 1$, a penalty parameter $\rho>0$ and $a\in\mathbb R$,
--   $$T_{N,\rho}(a)=\begin{cases}a-N/\rho & a>-1/N+N/\rho\\ -1/N & a\in[-1/N,\,-1/N+N/\rho]\\ a & a<-1/N.\end{cases}$$
--   2. **The $\ell_1$ norm** $\|x\|_1=\sum_j|x_j|$.
--   3. **The group-lasso block objective** (§8.3.2, p. 69): for $\rho,\lambda\in\mathbb R$, $A\in\mathbb R^{m\times n}$ and $v\in\mathbb R^m$,
--   $$h(x)=\frac{\rho}{2}\|Ax-v\|_2^2+\lambda\|x\|_2,\qquad x\in\mathbb R^n.$$
--   4. **The ridge point** (§8.3.2, p. 69): for $\nu\in\mathbb R$,
--   $$x(\nu)=(A^TA+\nu I)^{-1}A^Tv.$$
--
--   These are the objects in which the $x_i$- and $\bar z$-updates of distributed lasso, group lasso and support vector machine fitting are expressed in closed form.
--
--   **Formalization Note** Vectors are `EuclideanSpace ℝ (Fin n)`, so `‖·‖` is the $\ell_2$ norm; matrices act through `Matrix.toEuclideanLin`. The book's regularization weight $\lambda$ is named `lam`, since `λ` is a Lean keyword. The ridge point uses Mathlib's matrix inverse `⁻¹`, which returns $0$ for a singular matrix; every theorem uses it only for $\nu>0$, where $A^TA+\nu I$ is positive definite and the inverse is the true one. The middle case of $T_{N,\rho}$ is the `else` branch, so the three cases are exactly those printed.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), pp. 69–71 (§8.3.2, §8.3.4) (DOI 10.1561/2200000016)

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

namespace BoydADMM.ModelFit

open Matrix

/-! Objects of Chapter 8 (distributed model fitting) of Boyd–Parikh–Chu–Peleato–Eckstein (2011),
pp. 61–72. Vectors live in `EuclideanSpace ℝ (Fin n)`, so `‖·‖` is the Euclidean norm `‖·‖₂`; a
matrix `A ∈ ℝ^{m×n}` acts by `Matrix.toEuclideanLin A`, and `Aᵀ` by `Matrix.toEuclideanLin Aᵀ`.
The regularization weight `λ` of the book is called `lam` (`λ` is a Lean keyword). -/

/-- The shifted soft thresholding operation of §8.3.4 (p. 71), for `N` blocks and penalty `ρ`:
`a − N/ρ` if `a > −1/N + N/ρ`, `−1/N` if `a ∈ [−1/N, −1/N + N/ρ]`, `a` if `a < −1/N`. -/
noncomputable def shiftedSoftThreshold (N : ℕ) (ρ a : ℝ) : ℝ :=
  if -1 / (N : ℝ) + N / ρ < a then a - N / ρ
  else if a < -1 / (N : ℝ) then a else -1 / (N : ℝ)

/-- The ℓ1 norm `‖x‖₁ = ∑ⱼ |xⱼ|` of a vector. -/
noncomputable def l1norm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ j, |x j|

/-- The group-lasso block objective of §8.3.2 (p. 69):
`h(x) = (ρ/2)‖A x − v‖₂² + λ‖x‖₂` for `x ∈ ℝⁿ`, with `A ∈ ℝ^{m×n}` and `v ∈ ℝᵐ`. -/
noncomputable def groupLassoObj {m n : ℕ} (ρ lam : ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ρ / 2 * ‖Matrix.toEuclideanLin A x - v‖ ^ 2 + lam * ‖x‖

/-- The ridge point `(AᵀA + νI)⁻¹ Aᵀ v` of §8.3.2 (p. 69). For `ν > 0` the matrix `AᵀA + νI` is
positive definite, so `⁻¹` is the true inverse. -/
noncomputable def ridgeSol {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (ν : ℝ)
    (v : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanLin ((Aᵀ * A + ν • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ * Aᵀ) v

end BoydADMM.ModelFit


