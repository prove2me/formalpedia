-- Prove2me | Definitions.Def_TensorNP_SymEigen_Defs
-- name    : TensorNP_SymEigen_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:07:09.391981+00:00
-- url     : https://prove2.me/theorems/ee93c5d7-92ea-4896-900a-fee2583e377d
-- title:
--   (2), (13), (14), (19), Def. 5.1 — symmetric real 3-tensors, cubic and trilinear forms, unit ℓ²-eigenvalues, and λ_l
-- statement:
--   Let $\iota$ be a finite index set of size $n$ (for instance $\{1,\dots,n\}$). A **real 3-tensor** is an array $\mathcal A = [\![a_{ijk}]\!] \in \mathbb R^{n\times n\times n}$ with entries indexed by $i,j,k\in\iota$.
--
--   1. $\mathcal A$ is **symmetric** (display (2)) if for all $i,j,k$
--   $$a_{ijk}=a_{ikj}=a_{jik}=a_{jki}=a_{kij}=a_{kji}.$$
--   2. The **trilinear form** (19) and the **cubic form** (14) of $\mathcal A$ are
--   $$\mathcal A(\mathbf x,\mathbf y,\mathbf z)=\sum_{i,j,k}a_{ijk}x_iy_jz_k,\qquad \mathcal A(\mathbf x,\mathbf x,\mathbf x)=\sum_{i,j,k}a_{ijk}x_ix_jx_k .$$
--   3. $\|\mathbf x\|_2=(\sum_i x_i^2)^{1/2}$ is the Euclidean norm.
--   4. A real number $\lambda$ is a **unit $\ell^2$-eigenvalue** of $\mathcal A$ if there is $\mathbf x\in\mathbb R^n$ with $\|\mathbf x\|_2=1$ and
--   $$\sum_{i,j}a_{ijk}x_ix_j=\lambda x_k\qquad\text{for every }k .$$
--   5. For a positive integer $l$, $\lambda_l = 2\sqrt{\tfrac23\left(1-\tfrac1l\right)}$.
--
--   These are the objects of Hillar and Lim's §5 and §9: eigenvalues of a 3-tensor are the stationary values of its cubic form on the unit sphere (13), and the numbers $\lambda_l$ are the values queried in the proof of Theorem 9.3.
--
--   **Formalization Note** Definition 5.1 asks only for $\mathbf x\neq\mathbf 0$. Since $(\lambda,\mathbf x)\mapsto(t\lambda,t\mathbf x)$ preserves the eigen-equation (3), that reading makes every nonzero real an eigenvalue as soon as one nonzero eigenvalue exists; the unit normalization (13), from which the paper derives the notion, is used instead. With index set $\{0,\dots,n-1\}$ the paper's $a_{ijk}$ is the Lean entry at $(i-1,j-1,k-1)$. In Lean $1/0=0$, so $\lambda_0$ would equal $2\sqrt{2/3}$; $\lambda_l$ is only ever used for $l\ge1$.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:4, (2), (3); p. 0:19, (13), (14); p. 0:20, Definition 5.1; p. 0:21, (19); p. 0:28, proof of Theorem 9.3

import Mathlib

namespace TensorNP.SymEigen

/-- A real 3-tensor `A ∈ ℝ^{n×n×n}` whose three indices range over a finite type `ι`
(Hillar–Lim §1.1, p. 0:3–0:4). With `ι = Fin n` the paper's entry `a_{ijk}` is
`A (i-1) (j-1) (k-1)` (0-based indices); any other finite index type is a relabelling of the
coordinates of `ℝ^n` with `n = Fintype.card ι`. -/
abbrev Tensor3 (ι : Type*) : Type _ := ι → ι → ι → ℝ

/-- A 3-tensor is symmetric, display (2) of Hillar–Lim (p. 0:4):
`a_{ijk} = a_{ikj} = a_{jik} = a_{jki} = a_{kij} = a_{kji}` for all `i, j, k`. All six
equalities are written out. -/
def IsSymmetric {ι : Type*} (A : Tensor3 ι) : Prop :=
  ∀ i j k, A i j k = A i k j ∧ A i j k = A j i k ∧ A i j k = A j k i ∧
    A i j k = A k i j ∧ A i j k = A k j i

/-- The trilinear form (19) of Hillar–Lim (p. 0:21):
`A(x, y, z) = ∑_{i,j,k} a_{ijk} x_i y_j z_k`. -/
def trilinearForm {ι : Type*} [Fintype ι] (A : Tensor3 ι) (x y z : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, A i j k * x i * y j * z k

/-- The cubic form (14) of Hillar–Lim (p. 0:19): `A(x, x, x) = ∑_{i,j,k} a_{ijk} x_i x_j x_k`. -/
def cubicForm {ι : Type*} [Fintype ι] (A : Tensor3 ι) (x : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, A i j k * x i * x j * x k

/-- The Euclidean norm `‖x‖₂ = (∑_i x_i²)^{1/2}` of a real vector (constraint (13), p. 0:19). -/
noncomputable def l2norm {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, x i ^ 2)

/-- `λ` is a **unit ℓ²-eigenvalue** of the real 3-tensor `A` (Definition 5.1 with (3), p. 0:20
and p. 0:4, normalized by (13)): there is `x ∈ ℝ^n` with `‖x‖₂ = 1` and
`∑_{i,j} a_{ijk} x_i x_j = λ x_k` for every `k`. The unit normalization replaces the paper's
`x ≠ 0`; it is needed because `(λ, x) ↦ (tλ, tx)` preserves (3), so without it every nonzero real
number would be an eigenvalue as soon as one nonzero eigenvalue exists. -/
def IsUnitL2Eigenvalue {ι : Type*} [Fintype ι] (A : Tensor3 ι) (lam : ℝ) : Prop :=
  ∃ x : ι → ℝ, l2norm x = 1 ∧ ∀ k, ∑ i, ∑ j, A i j k * x i * x j = lam * x k

/-- The query values of the proof of Theorem 9.3 (p. 0:28):
`λ_l = 2 √((2/3)(1 − 1/l))`, used for `l = 1, …, v`. -/
noncomputable def lambdaL (l : ℕ) : ℝ :=
  2 * Real.sqrt (2 / 3 * (1 - 1 / (l : ℝ)))

end TensorNP.SymEigen


