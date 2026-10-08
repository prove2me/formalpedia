-- Prove2me | Definitions.Def_ManPG_Conv_Basic
-- name    : ManPG_Conv_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T19:02:09.789974+00:00
-- url     : https://prove2.me/theorems/681da8a8-44ee-45d9-a34e-1ed59977124e
-- title:
--   Frobenius inner product and norm, convex subgradients, and the tangent space of St(n, r) with its projection
-- statement:
--   The basic objects of matrix optimization over the Stiefel manifold
--   $\mathrm{St}(n,r)=\{X\in\mathbb R^{n\times r}: X^\top X=I_r\}$.
--
--   1. The ambient space is $\mathbb R^{n\times r}$, the real $n\times r$ matrices, with the Euclidean (Frobenius) inner product and norm
--   $$\langle A,B\rangle=\operatorname{Tr}(A^\top B),\qquad \|A\|_F=\sqrt{\langle A,A\rangle}.$$
--   2. For a function $h:\mathbb R^{n\times r}\to\mathbb R$, a matrix $G$ is a (Euclidean) subgradient of $h$ at $X$, written $G\in\partial h(X)$, if
--   $$h(X)+\langle G,Y-X\rangle\le h(Y)\qquad\text{for all }Y\in\mathbb R^{n\times r}.$$
--   3. The tangent space of $\mathcal M=\mathrm{St}(n,r)$ at $X$ is
--   $$T_X\mathcal M=\{V\in\mathbb R^{n\times r}: V^\top X+X^\top V=0\}.$$
--   4. The projection onto the tangent space is
--   $$\operatorname{Proj}_{T_X\mathcal M}(Y)=(I_n-XX^\top)Y+\tfrac12 X\,(X^\top Y-Y^\top X).$$
--   For $X\in\mathrm{St}(n,r)$ it is the orthogonal projection (with respect to $\langle\cdot,\cdot\rangle$) of $Y$ onto $T_X\mathcal M$.
--
--   These are the objects in which problem (1.1), its first-order stationarity condition and the ManPG subproblem are written.
--
--   **Formalization Note** Matrices are `Matrix (Fin n) (Fin r) ℝ` (abbreviated `Mat n r`). The inner product is written as a trace and the norm as its square root, so no `Matrix` norm instance is used: Mathlib's default would be the sup norm. The tangent space and the projection are given by the formulas above for every matrix $X$. They have their geometric meaning only for $X\in\mathrm{St}(n,r)$, and every statement that uses them assumes that.
-- source:
--   Chen, Ma, So, Zhang, Proximal gradient method for nonsmooth optimization over the Stiefel manifold, SIAM J. Optim. (2020), p. 3 (Notation: ⟨A, B⟩ = Tr(AᵀB), ‖·‖_F, Proj_{T_X St(n,r)}, ∂h) and p. 10 (T_X M = {V | VᵀX + XᵀV = 0})

import Mathlib
import Definitions.Def_ProjLikeRetr_Stiefel_stiefel

open scoped Matrix

namespace ManPG.Conv

/-- The ambient Euclidean space `ℝ^{n×r}` of problem (1.1): real `n × r` matrices. -/
abbrev Mat (n r : ℕ) : Type := Matrix (Fin n) (Fin r) ℝ

/-- Notation, p. 3: the Euclidean (Frobenius) inner product `⟨A, B⟩ = Tr(AᵀB)` of two matrices. -/
def frobInner {n r : ℕ} (A B : Mat n r) : ℝ :=
  Matrix.trace (Aᵀ * B)

/-- Notation, p. 3: the Frobenius norm `‖A‖_F = √⟨A, A⟩ = √Tr(AᵀA)`. -/
noncomputable def frobNorm {n r : ℕ} (A : Mat n r) : ℝ :=
  Real.sqrt (frobInner A A)

/-- Notation, p. 3: `G` is a (Euclidean, convex-analysis) subgradient of `h` at `X`, i.e.
`G ∈ ∂h(X)`: `h(X) + ⟨G, Y − X⟩ ≤ h(Y)` for every `Y ∈ ℝ^{n×r}`. -/
def IsSubgrad {n r : ℕ} (h : Mat n r → ℝ) (X G : Mat n r) : Prop :=
  ∀ Y : Mat n r, h X + frobInner G (Y - X) ≤ h Y

/-- p. 10: the tangent space `T_X M = {V | VᵀX + XᵀV = 0}` of `M = St(n, r)` at `X`
(meaningful for `X ∈ St(n, r)`). -/
def tangent {n r : ℕ} (X : Mat n r) : Set (Mat n r) :=
  {V | Vᵀ * X + Xᵀ * V = 0}

/-- Notation, p. 3: `Proj_{T_X St(n,r)}(Y) = (I_n − XXᵀ)Y + ½ X(XᵀY − YᵀX)`, the orthogonal
projection of `Y` onto the tangent space `T_X M` when `X ∈ St(n, r)`. -/
noncomputable def projT {n r : ℕ} (X Y : Mat n r) : Mat n r :=
  (1 - X * Xᵀ) * Y + (1 / 2 : ℝ) • (X * (Xᵀ * Y - Yᵀ * X))

end ManPG.Conv


