-- Prove2me | Definitions.Def_TensorNP_SpectralNorm_Tensor
-- name    : TensorNP_SpectralNorm_Tensor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:06:14.752301+00:00
-- url     : https://prove2.me/theorems/63a24aab-86a4-42b6-b9fd-899dec6f2ffa
-- title:
--   Definitions 6.1 and 6.6 — trilinear form, spectral norm and unit ℓ²-singular values of a real 3-tensor
-- statement:
--   Let $l, m, n \in \mathbb N$. A real **3-tensor** is an array $\mathcal A = [\![a_{ijk}]\!] \in \mathbb R^{l\times m\times n}$, and $\|\mathbf x\|_2 = (\sum_i x_i^2)^{1/2}$ is the Euclidean norm.
--
--   1. The **trilinear form** (19) of $\mathcal A$ is
--   $$
--   \mathcal A(\mathbf x,\mathbf y,\mathbf z) = \sum_{i,j,k} a_{ijk}\, x_i y_j z_k, \qquad \mathbf x\in\mathbb R^l,\ \mathbf y\in\mathbb R^m,\ \mathbf z\in\mathbb R^n .
--   $$
--   2. The **spectral norm** (Definition 6.6) is
--   $$
--   \|\mathcal A\|_{2,2,2} = \sup_{\mathbf x,\mathbf y,\mathbf z\neq \mathbf 0} \frac{|\mathcal A(\mathbf x,\mathbf y,\mathbf z)|}{\|\mathbf x\|_2\|\mathbf y\|_2\|\mathbf z\|_2}.
--   $$
--   3. A real number $\sigma$ is a **unit $\ell^2$-singular value** of $\mathcal A$ (Definition 6.1, equations (20), with unit singular vectors) if there are $\mathbf u\in\mathbb R^l$, $\mathbf v\in\mathbb R^m$, $\mathbf w\in\mathbb R^n$ with $\|\mathbf u\|_2=\|\mathbf v\|_2=\|\mathbf w\|_2=1$ and
--   $$
--   \sum_{j,k} a_{ijk} v_j w_k = \sigma u_i,\qquad \sum_{i,k} a_{ijk} u_i w_k = \sigma v_j,\qquad \sum_{i,j} a_{ijk} u_i v_j = \sigma w_k
--   $$
--   for all $i, j, k$.
--   4. For a 4-tensor $\mathcal S\in\mathbb R^{n\times n\times n\times n}$: the 4-linear form $\mathcal S(\mathbf w,\mathbf x,\mathbf y,\mathbf z)=\sum s_{ijkp}w_ix_jy_kz_p$, the spectral norm $\|\mathcal S\|_{2,2,2,2}=\sup_{\mathbf w,\mathbf x,\mathbf y,\mathbf z\ne\mathbf 0}|\mathcal S(\mathbf w,\mathbf x,\mathbf y,\mathbf z)|/(\|\mathbf w\|_2\|\mathbf x\|_2\|\mathbf y\|_2\|\mathbf z\|_2)$ (left side of (24)), and symmetry: $s_{ijkp}$ is invariant under every permutation of its four indices.
--   5. The outer product $(\mathbf x\otimes\mathbf y\otimes\mathbf z)_{ijk}=x_iy_jz_k$ and the squared Frobenius norm $\|\mathcal A\|_F^2=\sum_{i,j,k}a_{ijk}^2$ (§7).
--
--   These are the general tensor notions on which the clique-number construction of §6 is built.
--
--   **Formalization Note** Tensors are functions `Fin l → Fin m → Fin n → ℝ`, so indices are 0-based: the paper's $a_{ijk}$ is `A (i-1) (j-1) (k-1)`. The Euclidean norm is `Real.sqrt (∑ i, x i ^ 2)`. The spectral norm is `sSup` of the set of quotients over nonzero vectors; this set is bounded, and for a format with a zero dimension it is empty and the value is $0$. Definition 6.1 as printed only asks the singular vectors to be nonzero; since $(\sigma,\mathbf u,\mathbf v,\mathbf w)\mapsto(t\sigma,t\mathbf u,t\mathbf v,t\mathbf w)$ preserves (20), without a normalization every nonzero $\sigma$ would be a singular value of any tensor having a nonzero one. The paper obtains singular values as stationary values on the product of unit spheres (p. 0:21), so unit vectors are required here. Symmetry of a 4-tensor is stated as invariance under the three adjacent transpositions of indices, which generate all permutations.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:21, (19), Definition 6.1, (20); p. 0:22, Definition 6.6; p. 0:23, (24); p. 0:24, §7 (Frobenius norm)

import Mathlib

namespace TensorNP.SpectralNorm

/-! # Tensors, their spectral norm and unit ℓ²-singular values
(Hillar–Lim, Definitions 6.1 and 6.6, pp. 0:21–0:22; (19), p. 0:21; (24), p. 0:23; §7, p. 0:24)

A real 3-tensor of format `l × m × n` is an array `A : Fin l → Fin m → Fin n → ℝ`; the paper's
entry `a_{ijk}` (indices from 1) is `A (i-1) (j-1) (k-1)`. Vectors are functions `Fin n → ℝ`. -/

/-- The Euclidean norm `‖x‖₂ = (Σ_i x_i²)^{1/2}` of a real vector. -/
noncomputable def l2norm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, x i ^ 2)

/-- The trilinear form (19): `A(x, y, z) = Σ_{i,j,k} a_{ijk} x_i y_j z_k`. -/
def trilinear {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℝ)
    (x : Fin l → ℝ) (y : Fin m → ℝ) (z : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, A i j k * x i * y j * z k

/-- Definition 6.6, the **spectral norm** `‖A‖_{2,2,2} = sup_{x,y,z ≠ 0} |A(x,y,z)| /
(‖x‖₂ ‖y‖₂ ‖z‖₂)`, as the supremum of the set of these quotients over nonzero vectors. -/
noncomputable def specNorm {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℝ) : ℝ :=
  sSup {t : ℝ | ∃ (x : Fin l → ℝ) (y : Fin m → ℝ) (z : Fin n → ℝ),
    x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ t = |trilinear A x y z| / (l2norm x * l2norm y * l2norm z)}

/-- Definition 6.1 (equations (20)) with unit singular vectors: `σ` is a **unit ℓ²-singular
value** of `A` if there are `u, v, w` with `‖u‖₂ = ‖v‖₂ = ‖w‖₂ = 1` and
`Σ_{j,k} a_{ijk} v_j w_k = σ u_i`, `Σ_{i,k} a_{ijk} u_i w_k = σ v_j`,
`Σ_{i,j} a_{ijk} u_i v_j = σ w_k` for all `i, j, k`. -/
def IsUnitSingularValue {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℝ) (σ : ℝ) : Prop :=
  ∃ (u : Fin l → ℝ) (v : Fin m → ℝ) (w : Fin n → ℝ),
    l2norm u = 1 ∧ l2norm v = 1 ∧ l2norm w = 1 ∧
    (∀ i, ∑ j, ∑ k, A i j k * v j * w k = σ * u i) ∧
    (∀ j, ∑ i, ∑ k, A i j k * u i * w k = σ * v j) ∧
    (∀ k, ∑ i, ∑ j, A i j k * u i * v j = σ * w k)

/-- The 4-linear form `S(w, x, y, z) = Σ_{i,j,k,p} s_{ijkp} w_i x_j y_k z_p` of a real
`n × n × n × n` tensor. -/
def quadrilinear {n : ℕ} (S : Fin n → Fin n → Fin n → Fin n → ℝ)
    (w x y z : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ p, S i j k p * w i * x j * y k * z p

/-- A 4-tensor is **symmetric** if its entries are invariant under every permutation of the four
indices; it suffices to ask invariance under the three adjacent transpositions, which generate
the symmetric group on four letters. -/
def IsSymmetric4 {n : ℕ} (S : Fin n → Fin n → Fin n → Fin n → ℝ) : Prop :=
  (∀ i j k p, S i j k p = S j i k p) ∧
  (∀ i j k p, S i j k p = S i k j p) ∧
  (∀ i j k p, S i j k p = S i j p k)

/-- The spectral norm of a 4-tensor, `‖S‖_{2,2,2,2} = sup_{w,x,y,z ≠ 0} |S(w,x,y,z)| /
(‖w‖₂ ‖x‖₂ ‖y‖₂ ‖z‖₂)` (left-hand side of (24)). -/
noncomputable def specNorm4 {n : ℕ} (S : Fin n → Fin n → Fin n → Fin n → ℝ) : ℝ :=
  sSup {t : ℝ | ∃ (w x y z : Fin n → ℝ), w ≠ 0 ∧ x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧
    t = |quadrilinear S w x y z| / (l2norm w * l2norm x * l2norm y * l2norm z)}

/-- The outer product `(x ⊗ y ⊗ z)_{ijk} = x_i y_j z_k`. -/
def outer3 {l m n : ℕ} (x : Fin l → ℝ) (y : Fin m → ℝ) (z : Fin n → ℝ) :
    Fin l → Fin m → Fin n → ℝ :=
  fun i j k => x i * y j * z k

/-- The squared Frobenius norm `‖A‖_F² = Σ_{i,j,k} a_{ijk}²` (§7, p. 0:24). -/
def frobSq {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, A i j k ^ 2

end TensorNP.SpectralNorm


