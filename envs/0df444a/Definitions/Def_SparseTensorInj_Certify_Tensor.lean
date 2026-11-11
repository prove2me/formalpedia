-- Prove2me | Definitions.Def_SparseTensorInj_Certify_Tensor
-- name    : SparseTensorInj_Certify_Tensor
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:36:38.184298+00:00
-- url     : https://prove2.me/theorems/601a50d9-055d-4b77-8fc2-4036fb5f3149
-- title:
--   Order-$k$ tensors, symmetry, the injective norm, the $\ell_2$ operator norm and trace moments (Definitions 1, 2, 53, 54)
-- statement:
--   An **order-$k$ tensor** over $\mathbb R^n$ is a real array $T=(T_{i_1,\dots,i_k})$ indexed by $k$-tuples of indices in $[n]$; in Lean the index set $[n]$ is `Fin n` and a tensor is a function `(Fin k → Fin n) → ℝ`. It is **symmetric** if $T_{i_{\pi(1)},\dots,i_{\pi(k)}}=T_{i_1,\dots,i_k}$ for every permutation $\pi$ of the $k$ positions.
--
--   For $x\in\mathbb R^n$ the multilinear form is
--   $$\langle T,x^{\otimes k}\rangle=\sum_{i_1,\dots,i_k\in[n]}T_{i_1,\dots,i_k}\,x_{i_1}\cdots x_{i_k},$$
--   and the **injective norm** (Definition 2) is
--   $$\|T\|_{\mathrm{inj}}=\max_{x\in\mathbb R^n,\ \|x\|_2=1}\big|\langle T,x^{\otimes k}\rangle\big|.$$
--   The **Frobenius norm** is $\|T\|_F=(\sum_{i\in[n]^k}T_i^2)^{1/2}$, and $[n]_k$ denotes the family of $k$-element subsets of $[n]$.
--
--   For a real matrix $A$, $\|A\|_{\mathrm{op}}$ is the $\ell_2\to\ell_2$ operator norm (largest singular value). For an integer $t\ge1$ the **trace moment** (Definition 54) is $\Phi_t(Q)=\mathrm{Tr}\big((QQ^\top)^t\big)=\|Q\|_{S_{2t}}^{2t}$, the $2t$-th power of the Schatten $2t$-norm (Definition 53).
--
--   These are the basic objects of Theorem 5 and of every milestone.
--
--   **Formalization Note.** `injNorm T = ⨆ x : unitSphere n, |multilinearForm T x|` with `unitSphere n = {x | Σ x_i² = 1}`: the values are bounded and the supremum is attained for $n\ge1$ (compact sphere, continuous form), so it is the paper's maximum; for $n=0$ the sphere is empty and the value is $0$. `opNorm A = ‖toContinuousLinearMap (toEuclideanLin A)‖`, which is Mathlib's $\ell_2$ operator norm (`Matrix.l2_opNorm_def`), not the Frobenius norm. `traceMoment t Q = trace ((Q * Qᵀ)^t)`.
-- source:
--   Kothari, Louis, Paul, Raghavendra, Improved Bounds for Certifying Injective Norm of Sparse Random Tensors, STOC 2027 submission (manuscript of November 3, 2026, sha256 e46cf53d…), pp. 3–4, Definitions 1 and 2; p. 31, Definitions 53 and 54

import Mathlib

namespace SparseTensorInj.Certify

/-- An order-`k` tensor over `ℝ^n` (Definition 2, p. 4): a real array `T_{i_1, …, i_k}` indexed
by `k`-tuples of indices in `[n]`. Indices are 0-based: `[n]` is `Fin n`. -/
abbrev Tensor (k n : ℕ) : Type := (Fin k → Fin n) → ℝ

/-- A tensor is symmetric (Definition 2) when every permutation of its `k` indices leaves the
entry unchanged: `T_{i_{π(1)}, …, i_{π(k)}} = T_{i_1, …, i_k}`. -/
def IsSymmetric {k n : ℕ} (T : Tensor k n) : Prop :=
  ∀ (π : Equiv.Perm (Fin k)) (i : Fin k → Fin n), T (i ∘ π) = T i

/-- The multilinear form `⟨T, x^{⊗k}⟩ = Σ_{i_1, …, i_k ∈ [n]} T_{i_1, …, i_k} x_{i_1} ⋯ x_{i_k}`
(Definitions 1 and 2, pp. 3–4). -/
def multilinearForm {k n : ℕ} (T : Tensor k n) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin k → Fin n, T i * ∏ j : Fin k, x (i j)

/-- The Euclidean unit sphere of `ℝ^n`, in coordinates: `‖x‖_2 = 1`, i.e. `Σ_i x_i^2 = 1`. -/
def unitSphere (n : ℕ) : Set (Fin n → ℝ) := {x | ∑ i, x i ^ 2 = 1}

/-- The injective norm (Definition 2, p. 4): `‖T‖_inj = max_{‖x‖_2 = 1} |⟨T, x^{⊗k}⟩|`.
For `n ≥ 1` the sphere is nonempty and compact and the form is continuous, so the real
supremum below is attained and equals the paper's maximum. (For `n = 0` the sphere is empty
and the value is `0`.) -/
noncomputable def injNorm {k n : ℕ} (T : Tensor k n) : ℝ :=
  ⨆ x : unitSphere n, |multilinearForm T x.1|

/-- The Frobenius norm of a tensor, `‖T‖_F = (Σ_{i ∈ [n]^k} T_i^2)^{1/2}`. -/
noncomputable def frobNorm {k n : ℕ} (T : Tensor k n) : ℝ :=
  Real.sqrt (∑ i : Fin k → Fin n, T i ^ 2)

/-- The family `[n]_k` of `k`-element subsets of `[n]` (Notation, p. 3). -/
abbrev KSubset (n k : ℕ) : Type := {e : Finset (Fin n) // e.card = k}

/-- The operator norm `‖A‖_op` of a real matrix: the norm of `x ↦ A x` as a linear map between
Euclidean spaces (`ℓ2 → ℓ2`), i.e. the largest singular value. This is Mathlib's `ℓ2` operator
norm on matrices (`Matrix.l2_opNorm_def`), not the Frobenius norm. -/
noncomputable def opNorm {m p : Type*} [Fintype m] [Fintype p] [DecidableEq m] [DecidableEq p]
    (A : Matrix m p ℝ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖

/-- The `2t`-th trace moment (Definition 54, p. 31): `Φ_t(Q) = Tr((Q Q^⊤)^t)`, which equals
`‖Q‖_{S_{2t}}^{2t}`, the `2t`-th power of the Schatten `2t`-norm of `Q` (Definition 53). -/
noncomputable def traceMoment {m p : Type*} [Fintype m] [DecidableEq m] [Fintype p]
    (t : ℕ) (Q : Matrix m p ℝ) : ℝ :=
  Matrix.trace ((Q * Q.transpose) ^ t)

end SparseTensorInj.Certify


