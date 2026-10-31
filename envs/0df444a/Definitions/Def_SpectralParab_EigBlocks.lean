-- Prove2me | Definitions.Def_SpectralParab_EigBlocks
-- name    : SpectralParab_EigBlocks
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:45:16.613985+00:00
-- url     : https://prove2.me/theorems/894d4522-865d-4c38-aea4-55c5e26f42be
-- title:
--   Eigenvalue blocks $\alpha_m$, the index maps $\ell_i$, $\ell'_i$, $U_{\alpha_m}$, $\mu_mI-X$, the curvature sum of (5.1) and $\mathbf P^n_{X,H}$
-- statement:
--   Let $X\in\mathbf S^n$ have distinct eigenvalues $\mu_1>\dots>\mu_r$.
--
--   1. (2.4) $\alpha_m=\{i\mid\lambda_i(X)=\mu_m\}$; (2.5) $\ell_i(X)$ is the position of $i$ inside its block $\alpha_m$. For an index set $I$, $U_I$ is the submatrix of the columns of $U$ in $I$, and $Z_{IJ}$ the submatrix with rows $I$ and columns $J$.
--   2. (2.11) For $B=U_{\alpha_m}^\top HU_{\alpha_m}$, the blocks $\beta^m_j$ are the level sets of $\lambda(B)$, and $\ell'_i(X,H)$ is the position of $\ell_i(X)$ inside its block $\beta^m_j$.
--   3. The **curvature sum** of (5.1) and Theorem 5.8 is
--   $$\sum_{m=1}^r\big\langle\Lambda(Y)_{\alpha_m\alpha_m},\,U_{\alpha_m}^\top H(\mu_mI-X)^\dagger HU_{\alpha_m}\big\rangle,\qquad\Lambda(Y)=\operatorname{Diag}(\lambda(Y)),$$
--   where $Z^\dagger$ is the Moore–Penrose inverse.
--   4. $\mathbf P^n_{X,H}$ (p.21) is the set of block-diagonal permutation matrices $\operatorname{Diag}(B^1_1,\dots,B^r_{\rho_r})$ that permute indices only inside each $\beta^m_j$.
--
--   **Formalization Note** 0-based indices. A block is named by any of its members $i$; its elements are enumerated increasingly, and $\ell_i$ is the position in that enumeration. The curvature sum is written per index, $\sum_i\lambda_i(Y)\,(U^\top H(\lambda_i(X)I-X)^\dagger HU)_{ii}$, which regroups the block sum because $\Lambda(Y)_{\alpha_m\alpha_m}$ is diagonal and $\mu_m=\lambda_i(X)$ on $\alpha_m$. $^\dagger$ is the published `SunNLSDP.Equiv.pinv` (functional calculus $\mu\mapsto\mu^{-1}$, $0\mapsto0$), the Moore–Penrose inverse of a symmetric matrix. $\mathbf P^n_{X,H}$ is encoded as the permutations $\sigma$ with $\lambda(X)\circ\sigma=\lambda(X)$ and $\lambda'(X;H)\circ\sigma=\lambda'(X;H)$; by (2.9) these are exactly the block permutations of item 4.
-- source:
--   A. Mohammadi, E. Sarabi, Parabolic Regularity of Spectral Functions, arXiv:2301.04240v3 (preprint basis), https://arxiv.org/abs/2301.04240v3, (2.4)–(2.5) p.3, (2.10)–(2.12) pp.4–5, P^n_{X,H} p.21, (5.1) p.23

import Mathlib
import Definitions.Def_SpectralParab_SymMatSpace

open Matrix
open SunNLSDP.Equiv

namespace SpectralParab

/-! # Eigenvalue blocks, the index maps `ℓᵢ`, `ℓ'ᵢ`, and the curvature sum

Mohammadi–Sarabi, arXiv:2301.04240v3, (2.4)–(2.5) p.3, (2.10)–(2.12) pp.4–5, p.21, (5.1) p.23.

**Formalization Note.** Indices are 0-based. A block `α_m` (or `β^m_j`) is the set of indices
carrying one value of a nonincreasing vector, so it is a run of consecutive indices; its elements
are enumerated increasingly by `Finset.orderEmbOfFin`, and `ℓᵢ` (the paper's 1-based position of
`i` in its block) is the 0-based position of `i` in that enumeration. A block `α_m` is named by
any of its members `i` (`m` is the block with `i ∈ α_m`). -/

/-- The index set `{j | v_j = v_i}` of the entries of `v` equal to `v_i`; for `v = λ(X)` it is the
`α_m ∋ i` of (2.4), for `v = λ(U_{α_m}ᵀ H U_{α_m})` it is the `β^m_j` of (2.11). -/
noncomputable def eqBlock {m : ℕ} (v : Fin m → ℝ) (i : Fin m) : Finset (Fin m) :=
  Finset.univ.filter (fun j => v j = v i)

theorem mem_eqBlock_self {m : ℕ} (v : Fin m → ℝ) (i : Fin m) : i ∈ eqBlock v i := by
  simp [eqBlock]

/-- The 0-based position of `i ∈ s` in the increasing enumeration of `s`. -/
def posIn {m : ℕ} (s : Finset (Fin m)) (i : Fin m) (hi : i ∈ s) : Fin s.card :=
  (s.orderIsoOfFin rfl).symm ⟨i, hi⟩

/-- `U_s` (p.3): the submatrix of `U` formed by the columns indexed by `s`, in increasing order. -/
def colsOf {p m : ℕ} (U : Matrix (Fin p) (Fin m) ℝ) (s : Finset (Fin m)) :
    Matrix (Fin p) (Fin s.card) ℝ :=
  fun a b => U a (s.orderEmbOfFin rfl b)

/-- `α_m ∋ i`, (2.4) p.3: `{j | λⱼ(X) = λᵢ(X)}`. -/
noncomputable def alpha {n : ℕ} (X : SymMat (Fin n)) (i : Fin n) : Finset (Fin n) :=
  eqBlock (ModernConvex.Spectral.eigVec X.toMat) i

/-- `ℓᵢ(X)`, (2.5) p.3, 0-based: the position of `i` inside its block `α_m`. -/
noncomputable def ell {n : ℕ} (X : SymMat (Fin n)) (i : Fin n) : Fin (alpha X i).card :=
  posIn (alpha X i) i (mem_eqBlock_self _ i)

/-- `U_{α_m}ᵀ M U_{α_m}` for the block `α_m ∋ i` (p.4). -/
noncomputable def blockMat {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (X : SymMat (Fin n)) (i : Fin n)
    (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin (alpha X i).card) (Fin (alpha X i).card) ℝ :=
  (colsOf U (alpha X i))ᵀ * M * colsOf U (alpha X i)

/-- `Λ(Y)_{α_m α_m}` for the block `α_m ∋ i` of `X` (p.3 notation `Z_{IJ}`, Λ(Y) = Diag(λ(Y))). -/
noncomputable def diagBlock {n : ℕ} (X Y : SymMat (Fin n)) (i : Fin n) :
    Matrix (Fin (alpha X i).card) (Fin (alpha X i).card) ℝ :=
  (Matrix.diagonal (ModernConvex.Spectral.eigVec Y.toMat)).submatrix
    ((alpha X i).orderEmbOfFin rfl) ((alpha X i).orderEmbOfFin rfl)

/-- `μ_m I − X ∈ Sⁿ` for the block `α_m ∋ i`, where `μ_m = λᵢ(X)`. -/
noncomputable def shiftMat {n : ℕ} (X : SymMat (Fin n)) (i : Fin n) : SymMat (Fin n) :=
  SymMat.ofMat ((ModernConvex.Spectral.eigVec X.toMat i) • (1 : Matrix (Fin n) (Fin n) ℝ) - X.toMat)

/-- The curvature sum of Proposition 5.3 and Theorem 5.8 (p.23, p.30):
`∑_{m=1}^r ⟨Λ(Y)_{α_mα_m}, U_{α_m}ᵀ H (μ_m I − X)† H U_{α_m}⟩`, the inner product being the trace
inner product on `S^{|α_m|}`.
**Formalization Note.** Written per index:
`∑_{i=1}^n λᵢ(Y) · (Uᵀ H (λᵢ(X) I − X)† H U)_{ii}`. Since `Λ(Y)_{α_mα_m}` is diagonal with entries
`λᵢ(Y)`, `i ∈ α_m`, and `μ_m = λᵢ(X)` for `i ∈ α_m`, this is a regrouping of the same finite sum.
`†` is the published `SunNLSDP.Equiv.pinv` (the Moore–Penrose inverse of a symmetric matrix by
functional calculus: eigenvalue `μ ≠ 0 ↦ μ⁻¹`, `0 ↦ 0`). -/
noncomputable def curvSum {n : ℕ} (X Y H : SymMat (Fin n)) (U : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i : Fin n, ModernConvex.Spectral.eigVec Y.toMat i *
    (Uᵀ * H.toMat * pinv (shiftMat X i) * H.toMat * U) i i

/-- `Pⁿ_{X,H}` (p.21), as permutations: the block-diagonal permutations `Diag(B^1_1, …, B^r_{ρ_r})`
that permute indices only inside each block `β^m_j`.
**Formalization Note.** Encoded as the permutations `σ` with `λ(X) ∘ σ = λ(X)` and
`λ'(X; H) ∘ σ = λ'(X; H)`: fixing `λ(X)` keeps each `α_m`, and inside `α_m` the vector `λ'(X;H)`
is `λ(U_{α_m}ᵀ H U_{α_m})` by (2.9), whose level sets are the `β^m_j`. -/
noncomputable def PnXH {n : ℕ} (X H : SymMat (Fin n)) : Set (Equiv.Perm (Fin n)) :=
  {σ | (∀ i, lam X (σ i) = lam X i) ∧ ∀ i, lamDir X H (σ i) = lamDir X H i}

end SpectralParab


