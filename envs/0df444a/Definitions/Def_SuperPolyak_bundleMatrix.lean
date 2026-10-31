-- Prove2me | Definitions.Def_SuperPolyak_bundleMatrix
-- name    : SuperPolyak_bundleMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:11:59.141008+00:00
-- url     : https://prove2.me/theorems/1f9c29c1-bf82-4144-86cc-222c828874c3
-- title:
--   The bundle matrices $A_i=[v_0^\top;\dots;v_{i-1}^\top]$ and the stacked matrix $[A;v^\top]$
-- statement:
--   Given vectors $v_0,v_1,\dots\in\mathbb R^d$, the **bundle matrix** $A_i\in\mathbb R^{i\times d}$ has rows $v_0^\top,\dots,v_{i-1}^\top$, so $A_1=v_0^\top$ and $A_{i+1}=\begin{bmatrix}A_i\\ v_i^\top\end{bmatrix}$. It acts as the linear map $z\mapsto(\langle v_j,z\rangle)_{j<i}$ from $\mathbb R^d$ to $\mathbb R^i$; $\ker(A_i)=\{v_0,\dots,v_{i-1}\}^\perp$, $\|A_i\|_2$ is its operator norm and $\sigma_k(A_i)$ its $k$-th largest singular value.
--
--   For $A\in\mathbb R^{m\times d}$ and $v\in\mathbb R^d$, the **stacked matrix** $\begin{bmatrix}A\\ v^\top\end{bmatrix}\in\mathbb R^{(m+1)\times d}$ appends the row $v^\top$.
--
--   **Formalization Note** The index convention is Algorithm 2's throughout: $A_0$ is the empty $0\times d$ matrix with $\ker(A_0)=\mathbb R^d$. Matrices act through `Matrix.toEuclideanLin`; Mathlib's `LinearMap.singularValues` is 0-indexed, so $\sigma_k$ is `singularValues (k-1)`.
-- source:
--   Charisopoulos & Davis, arXiv:2201.04611v1, Algorithm 2, p.11 (A_1 := v_0ᵀ, A_{i+1} := [A_i; v_iᵀ]) and Lemma A.2, display (35), p.47–48 ([A; vᵀ])

import Mathlib

namespace SuperPolyak

/-- **The bundle matrix** `A_i = [v₀ᵀ; …; v_{i−1}ᵀ] ∈ ℝ^{i×d}` (Charisopoulos & Davis,
arXiv:2201.04611v1, Algorithm 2, p.11: `A₁ := v₀ᵀ`, `A_{i+1} := [A_i; v_iᵀ]`): row `j` is `v_j`.

**Formalization Note** This is Algorithm 2's index convention, used everywhere in the mission:
`A_i` has the `i` rows `v₀, …, v_{i−1}`, and `A₀` is the empty `0 × d` matrix, whose kernel is all
of `ℝᵈ`. Only `v₀, …, v_{i−1}` enter. -/
def bundleMatrix {d : ℕ} (v : ℕ → EuclideanSpace ℝ (Fin d)) (i : ℕ) : Matrix (Fin i) (Fin d) ℝ :=
  Matrix.of fun j k => v j k

/-- The bundle matrix `A_i` as a linear map `ℝᵈ → ℝⁱ`, `z ↦ (⟨v_j, z⟩)_{j<i}`, between Euclidean
spaces (arXiv:2201.04611v1, Algorithm 2, p.11). Its kernel is `ker(A_i)`, its singular values are
`σ_k(A_i) = singularValues (k − 1)` (Mathlib's singular values are 0-indexed). -/
noncomputable def bundleLin {d : ℕ} (v : ℕ → EuclideanSpace ℝ (Fin d)) (i : ℕ) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin i) :=
  Matrix.toEuclideanLin (bundleMatrix v i)

/-- The bundle matrix `A_i` as a continuous linear map `ℝᵈ → ℝⁱ` (arXiv:2201.04611v1,
Algorithm 2, p.11); its operator norm is the spectral norm `‖A_i‖₂` and its pseudoinverse is
`A_i†`. -/
noncomputable def bundleOp {d : ℕ} (v : ℕ → EuclideanSpace ℝ (Fin d)) (i : ℕ) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin i) :=
  LinearMap.toContinuousLinearMap (bundleLin v i)

/-- **The stacked matrix** `[A; vᵀ] ∈ ℝ^{(m+1)×d}` (arXiv:2201.04611v1, Lemma A.2, display (35),
p.47): the matrix `A ∈ ℝ^{m×d}` with the row `vᵀ` appended at the bottom. -/
def stackRow {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin (m + 1)) (Fin d) ℝ :=
  Matrix.of (Fin.snoc (α := fun _ => Fin d → ℝ) (fun j => A j) (fun k => v k))

end SuperPolyak


