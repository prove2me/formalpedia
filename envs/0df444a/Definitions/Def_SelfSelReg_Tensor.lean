-- Prove2me | Definitions.Def_SelfSelReg_Tensor
-- name    : SelfSelReg_Tensor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:46:28.61364+00:00
-- url     : https://prove2.me/theorems/d893d1aa-8818-46d4-910b-75b42c647e35
-- title:
--   Tensors on $\mathbb R^n$: tensor powers, Frobenius inner product, flattening, contraction
-- statement:
--   An order-$d$ tensor on $\mathbb R^n$ is an array $A=(A_{j_1\dots j_d})$ indexed by $(j_1,\dots,j_d)\in[n]^d$. This file fixes the notation of §4.2:
--
--   1. the tensor power $v^{\otimes d}$, with entries $v_{j_1}\cdots v_{j_d}$;
--   2. the Frobenius inner product $\langle A,B\rangle=\sum_J A_JB_J$, and the Frobenius norm of a matrix $\|M\|_F=(\sum_{a,c}M_{ac}^2)^{1/2}$;
--   3. symmetric tensors: entries unchanged under every permutation of the indices;
--   4. the flattening $\mathrm{Mat}_r(A)$ of an order-$2r$ tensor into an $n^r\times n^r$ matrix, rows indexed by the first $r$ indices and columns by the last $r$;
--   5. the contraction $A\lrcorner b$ of an order-$(d+1)$ tensor against $b\in\mathbb R^n$ in the last factor, $(A\lrcorner b)_{j_1\dots j_d}=\sum_\ell A_{j_1\dots j_d\ell}\,b_\ell$.
--
--   These are the objects in which the restricted Hermite moments and their rank-one decompositions are stated.
--
--   **Formalization Note** Index tuples are functions $\mathrm{Fin}\,d\to\mathrm{Fin}\,n$. The Frobenius norm of a tensor is the published `GaussPart.frobeniusNorm`.
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), §4.2, p.15 (PDF p.18); §4.4, p.17 (PDF p.20)

import Mathlib

namespace SelfSelReg

/-- **Tensors on `ℝⁿ` and the notation of §4.2**.

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), §4.2, p.15 (PDF p.18): "We use ⟨·,·⟩ for … the Frobenius inner product
on real matrices and tensors … v^{⊗d} for the d-fold tensor product of v. … A ⌟ b denotes contraction
against b in the last tensor factor. For an order-2r tensor on ℝⁿ, Mat_r(·) flattens its argument
into an n^r × n^r matrix using the first r multi-indices as the row index and the last r as the column
index."

An order-`d` tensor on `ℝⁿ` is a function of index tuples `Fin d → Fin n`.

**Formalization Note.** The Frobenius norm of a tensor is the published
`GaussPart.frobeniusNorm` (module `Definitions.Def_GaussPart_hermiteTensor`), not restated here. -/
abbrev Tensor (n d : ℕ) := (Fin d → Fin n) → ℝ

/-- `v^{⊗d}`: the entry at `(j₁, …, j_d)` is `v_{j₁} ⋯ v_{j_d}`. -/
noncomputable def tensorPow {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) (d : ℕ) : Tensor n d :=
  fun J => ∏ m, v (J m)

/-- The Frobenius inner product `⟨A, B⟩ = Σ_J A_J B_J`. -/
noncomputable def frobInner {n d : ℕ} (A B : Tensor n d) : ℝ := ∑ J, A J * B J

/-- The Frobenius norm of a real matrix, `‖M‖_F = (Σ_{a,c} M_{ac}²)^{1/2}`. -/
noncomputable def matFrobNorm {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℝ) : ℝ :=
  Real.sqrt (∑ a, ∑ c, M a c ^ 2)

/-- A symmetric tensor (an element of `Sym^d(ℝⁿ)`): its entries are unchanged when the indices are
permuted (§4.4, p.17). -/
def IsSymmetricTensor {n d : ℕ} (A : Tensor n d) : Prop :=
  ∀ σ : Equiv.Perm (Fin d), ∀ J, A (J ∘ σ) = A J

/-- `Mat_r(A)` for an order-`2r` tensor: the `n^r × n^r` matrix with rows indexed by the first `r`
indices and columns by the last `r`. -/
noncomputable def matFlat {n : ℕ} (r : ℕ) (A : Tensor n (2 * r)) : Matrix (Fin r → Fin n) (Fin r → Fin n) ℝ :=
  fun I J => A (Fin.append I J ∘ Fin.cast (two_mul r))

/-- `A ⌟ b`: contraction against `b` in the last tensor factor,
`(A ⌟ b)_{j₁…j_d} = Σ_ℓ A_{j₁…j_d ℓ} b_ℓ`. -/
noncomputable def contractLast {n d : ℕ} (A : Tensor n (d + 1)) (b : EuclideanSpace ℝ (Fin n)) : Tensor n d :=
  fun J => ∑ ℓ, A (Fin.snoc J ℓ) * b ℓ

end SelfSelReg


