-- Prove2me | Definitions.Def_SparseApprox_Greedy_Basic
-- name    : SparseApprox_Greedy_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:19:30.851872+00:00
-- url     : https://prove2.me/theorems/4c93463f-6329-41e3-a62b-e390ddfd7e9d
-- title:
--   Sparse approximation: column normalization, number of nonzeros, Opt(δ), Moore–Penrose inverse, spectral norm
-- statement:
--   This file fixes the basic objects of Natarajan's analysis of sparse approximate solutions of $Ax\approx b$.
--
--   1. **Columns.** For $A\in\mathbb R^{m\times n}$ and $j\in\{1,\dots,n\}$, $a_j\in\mathbb R^m$ is the $j$-th column of $A$, viewed in Euclidean space, so that $\|\cdot\|_2$ is the Euclidean norm and $u^Tv$ the dot product. For a family of vectors $(c_i)_{i\in I}$, $[c_i]_{i\in I}$ is the $m\times|I|$ matrix with these columns.
--   2. **Normalization.** $\operatorname{normalize}(v)=v/\|v\|_2$, with the convention $\operatorname{normalize}(0)=0$.
--   3. **Sparsity.** For $x\in\mathbb R^n$, $\sigma(x)=\{i : x_i\neq 0\}$ and $\|x\|_0=|\sigma(x)|$ is the number of nonzero entries.
--   4. **Optimum.** For $\delta\in\mathbb R$,
--   $$\operatorname{Opt}(\delta)=\min\{\|x\|_0 : x\in\mathbb R^n,\ \|Ax-b\|_2\le\delta\},$$
--   the fewest number of nonzero entries over all solutions within error $\delta$.
--   5. **Normalized matrix.** $\mathbf A$ is the matrix obtained by normalizing each column of $A$ with respect to the $L_2$ norm.
--   6. **Pseudo-inverse.** $P\in\mathbb R^{n\times m}$ is the (Moore–Penrose) pseudo-inverse of $M\in\mathbb R^{m\times n}$ when the four Penrose equations hold:
--   $$MPM=M,\quad PMP=P,\quad (MP)^T=MP,\quad (PM)^T=PM.$$
--   Such a $P$ exists and is unique; it is written $M^+$.
--   7. **Spectral norm.** $\|P\|_2=\sup_{\|y\|_2\le 1}\|Py\|_2$, the operator norm from $\ell_2$ to $\ell_2$.
--   8. **Minimum-support solutions.** Given vectors $c_1,\dots,c_n$, a target $c$ and a tolerance $\delta$, a vector $u$ is a minimum-support solution if $\|\sum_i u_ic_i-c\|_2\le\delta$ and every $v$ with $\|\sum_iv_ic_i-c\|_2\le\delta$ has $\|v\|_0\ge\|u\|_0$. The paper's $u^{(r)}$ is such a vector for $c_i=a^{(r)}_i$, $c=b^{(r)}$, $\delta=\varepsilon/2$.
--
--   These objects appear in the statement of Theorem 2 and throughout its proof.
--
--   **Formalization Note** Vectors live in `EuclideanSpace ℝ (Fin m)`. $\operatorname{Opt}(\delta)$ is an `sInf` over ℕ and equals $0$ when no $x$ satisfies the constraint; every theorem that uses it assumes such an $x$ exists. The pseudo-inverse is a predicate (the Penrose equations), not a formula such as $(M^TM)^{-1}M^T$, so it makes sense for every matrix.
-- source:
--   Natarajan, Sparse Approximate Solutions to Linear Systems, SIAM J. Comput. 24 (1995), p. 227 (Abstract: bold A and A⁺), p. 228 (§2, Problem), p. 229 (Theorem 2: Opt(ε/2)), p. 230 (u⁽ʳ⁾, N⁽ʳ⁾)

import Mathlib

open scoped InnerProductSpace

namespace SparseApprox.Greedy

/-- Column `j` of a real `m × n` matrix, as a vector of Euclidean space `ℝ^m` (so that `‖·‖` is
the ℓ2 norm and `⟪·,·⟫_ℝ` the dot product). -/
def colE {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i => A i j)

/-- The matrix whose `j`-th column is the vector `cols j`. -/
def colsMatrix {m : ℕ} {ι : Type*} (cols : ι → EuclideanSpace ℝ (Fin m)) : Matrix (Fin m) ι ℝ :=
  Matrix.of fun i j => cols j i

/-- Normalization of a vector with respect to the ℓ2 norm, `v / ‖v‖₂`.
Lean's convention `0⁻¹ = 0` sends the zero vector to itself. -/
noncomputable def normalizeVec {m : ℕ} (v : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) :=
  ‖v‖⁻¹ • v

/-- The set of indices of the nonzero entries of `x`. -/
noncomputable def nzSet {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ≠ 0)

/-- The number of nonzero entries of `x`. -/
noncomputable def nnz {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℕ :=
  (nzSet x).card

/-- `Opt(δ)`: the fewest number of nonzero entries over all `x` with `‖Ax − b‖₂ ≤ δ`.
(Lean's `sInf ∅ = 0`: the value is meaningful only when such an `x` exists.) -/
noncomputable def optSparsity {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (δ : ℝ) : ℕ :=
  sInf {N : ℕ | ∃ x : EuclideanSpace ℝ (Fin n),
    nnz x = N ∧ ‖Matrix.toEuclideanLin A x - b‖ ≤ δ}

/-- The bold `A` of the paper: `A` with each column normalized with respect to the ℓ2 norm
(a zero column stays zero). -/
noncomputable def Abar {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  colsMatrix (fun j => normalizeVec (colE A j))

/-- `P` is the Moore–Penrose pseudo-inverse of `M`: the four Penrose equations. -/
def IsMoorePenrose {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) (P : Matrix κ ι ℝ) : Prop :=
  M * P * M = M ∧ P * M * P = P ∧ (M * P).transpose = M * P ∧ (P * M).transpose = P * M

/-- The spectral norm `‖P‖₂`: the operator norm of `P` from `ℓ2` to `ℓ2`. -/
noncomputable def opNorm2 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (P : Matrix ι κ ℝ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin P)‖

/-- `u` is a vector with the minimum number of nonzero entries among all `v` with
`‖∑ᵢ vᵢ cᵢ − c‖₂ ≤ δ`, where `cᵢ = cols i` (the paper's `u⁽ʳ⁾` for `cols = A⁽ʳ⁾`,
`c = b⁽ʳ⁾`, `δ = ε/2`). -/
def IsMinSparseSol {m n : ℕ} (cols : Fin n → EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin m)) (δ : ℝ) (u : EuclideanSpace ℝ (Fin n)) : Prop :=
  ‖(∑ i, u i • cols i) - c‖ ≤ δ ∧
    ∀ v : EuclideanSpace ℝ (Fin n), ‖(∑ i, v i • cols i) - c‖ ≤ δ → nnz u ≤ nnz v

end SparseApprox.Greedy


