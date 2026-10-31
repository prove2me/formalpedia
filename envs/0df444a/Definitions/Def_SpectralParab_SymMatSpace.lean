-- Prove2me | Definitions.Def_SpectralParab_SymMatSpace
-- name    : SpectralParab_SymMatSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:44:25.246184+00:00
-- url     : https://prove2.me/theorems/b9a312a1-ecbc-4325-86bd-897c171db734
-- title:
--   The space $\mathbf S^n$, the eigenvalue map $\lambda$, symmetric and spectral functions and sets, $O^n(X)$, and $\lambda'$, $\lambda''$
-- statement:
--   $\mathbf S^n$ is the space of real symmetric $n\times n$ matrices with $\langle X,Y\rangle=\operatorname{tr}(XY)$, and $\lambda(X)=(\lambda_1(X),\dots,\lambda_n(X))$ lists the eigenvalues of $X$ in nonincreasing order.
--
--   1. $\theta:\mathbb R^n\to\overline{\mathbb R}$ is **symmetric** if $\theta(Qx)=\theta(x)$ for every $x$ and every permutation matrix $Q$; $\Theta\subset\mathbb R^n$ is a **symmetric set** if its indicator is symmetric. The **spectral function** of $\theta$ is $g=\theta\circ\lambda$ (1.1), and the **spectral set** of $\Theta$ is $C=\{X\in\mathbf S^n\mid\lambda(X)\in\Theta\}$ (3.2).
--   2. $\operatorname{Diag}(x)$ is the diagonal matrix with diagonal $x$.
--   3. $O^n(X)$ is the set of orthogonal $U$ with $X=U\operatorname{Diag}(\lambda(X))U^\top$ (2.1). Two symmetric matrices $A,B$ have a **simultaneous ordered spectral decomposition** if one orthogonal $U$ gives $U^\top AU=\operatorname{Diag}(\lambda(A))$ and $U^\top BU=\operatorname{Diag}(\lambda(B))$.
--   4. The directional derivative and the parabolic second-order directional derivative of $\lambda$ are
--   $$\lambda'(X;H)=\lim_{t\downarrow0}\frac{\lambda(X+tH)-\lambda(X)}t,\qquad \lambda''(X;H,W)=\lim_{t\downarrow0}\frac{\lambda(X+tH+\tfrac12t^2W)-\lambda(X)-t\lambda'(X;H)}{\tfrac12t^2}.$$
--
--   **Formalization Note** $\mathbf S^n$ is the published `SunNLSDP.Equiv.SymMat (Fin n)`, the entrywise-symmetric vectors of `EuclideanSpace ℝ (Fin n × Fin n)`, whose inner product $\sum_{ij}X_{ij}Y_{ij}$ equals $\operatorname{tr}(XY)$ on symmetric matrices, so all limits stay in $\mathbf S^n$. $\lambda$ is the published `ModernConvex.Spectral.eigVec` (Mathlib's sorted eigenvalues). Indices are 0-based. A permutation matrix acts as $x\mapsto x\circ\sigma$. $\lambda'$ and $\lambda''$ are the one-sided limits (`limUnder`); their existence is Corollary 2.3, a milestone.
-- source:
--   A. Mohammadi, E. Sarabi, Parabolic Regularity of Spectral Functions, arXiv:2301.04240v3 (preprint basis), https://arxiv.org/abs/2301.04240v3, (1.1) p.1, (2.1) and simultaneous ordered spectral decomposition p.3, (2.9) p.4, λ″ p.5, symmetric function/set and (3.2) p.7

import Mathlib
import Definitions.Def_SunNLSDP_Equiv_Setting
import Definitions.Def_ModernConvex_Spectral_SDR

open Filter Topology Matrix
open SunNLSDP.Equiv

namespace SpectralParab

/-! # `ℝⁿ`, `Sⁿ`, the eigenvalue map and spectral functions

Mohammadi–Sarabi, arXiv:2301.04240v3, (1.1) p.1, §2 pp.3–5, §3 p.7.

**Formalization Note.**
* `Sⁿ` is the published `SunNLSDP.Equiv.SymMat (Fin n)`: the entrywise-symmetric vectors of
  `EuclideanSpace ℝ (Fin n × Fin n)`, whose inner product `∑_{ij} X_ij Y_ij` equals the paper's
  `⟨X, Y⟩ = tr(XY)` on symmetric matrices; its norm is the Frobenius norm `√tr(X²)`. Every limit
  and `liminf` over directions therefore stays inside `Sⁿ`.
* `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`. Indices are 0-based: `i : Fin n` is the paper's `i + 1`.
* `λ(X)` is the published `ModernConvex.Spectral.eigVec` (Mathlib's antitone `eigenvalues₀`): the
  eigenvalues with multiplicity in nonincreasing order. -/

/-- `ℝⁿ` with the Euclidean inner product. -/
abbrev Rn (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- `Qx` for the permutation matrix `Q` of `σ`: the vector `i ↦ x_{σ i}`. Every `n × n` permutation
matrix acts this way for some `σ`, and conversely. -/
def permute {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Rn n) : Rn n :=
  WithLp.toLp 2 (fun i => x (σ i))

/-- A symmetric function `θ : ℝⁿ → R̄` (arXiv:2301.04240v3, p.7): `θ(Qx) = θ(x)` for every `x` and
every permutation matrix `Q`. -/
def IsSymmetricFn {n : ℕ} (θ : Rn n → EReal) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (x : Rn n), θ (permute σ x) = θ x

/-- A symmetric set `Θ ⊂ ℝⁿ` (p.7): its indicator is a symmetric function, i.e. `Qx ∈ Θ ↔ x ∈ Θ`. -/
def IsSymmetricSet {n : ℕ} (Θ : Set (Rn n)) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (x : Rn n), permute σ x ∈ Θ ↔ x ∈ Θ

/-- `λ(X) = (λ₁(X), …, λₙ(X))`, the eigenvalues of `X ∈ Sⁿ` in nonincreasing order (p.3). -/
noncomputable def lam {n : ℕ} (X : SymMat (Fin n)) : Rn n :=
  WithLp.toLp 2 (ModernConvex.Spectral.eigVec X.toMat)

/-- `Diag(x) ∈ Sⁿ`, the diagonal matrix with diagonal `x` (p.3). -/
noncomputable def Diag {n : ℕ} (x : Rn n) : SymMat (Fin n) :=
  SymMat.ofMat (Matrix.diagonal (fun i => x i))

/-- The spectral function `g = θ ∘ λ : Sⁿ → R̄` of (1.1) (p.1). -/
noncomputable def specFn {n : ℕ} (θ : Rn n → EReal) : SymMat (Fin n) → EReal :=
  fun X => θ (lam X)

/-- The spectral set `C = {X ∈ Sⁿ | λ(X) ∈ Θ}` of (3.2) (p.7). -/
def specSet {n : ℕ} (Θ : Set (Rn n)) : Set (SymMat (Fin n)) :=
  {X | lam X ∈ Θ}

/-- `Oᵏ(A)` (p.3): the orthogonal `k × k` matrices `U` with `A = U Diag(λ(A)) Uᵀ`, for a symmetric
`k × k` matrix `A`. -/
def OrthDiag {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) : Set (Matrix (Fin k) (Fin k) ℝ) :=
  {U | U ∈ Matrix.orthogonalGroup (Fin k) ℝ ∧
    A = U * Matrix.diagonal (ModernConvex.Spectral.eigVec A) * Uᵀ}

/-- `Oⁿ(X)` (p.3, (2.1)): the orthogonal `U` with `X = U Diag(λ(X)) Uᵀ`. -/
def On {n : ℕ} (X : SymMat (Fin n)) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  OrthDiag X.toMat

/-- Two symmetric `k × k` matrices have a simultaneous ordered spectral decomposition (p.3): there
is an orthogonal `U` with `Uᵀ A U = Diag(λ(A))` and `Uᵀ B U = Diag(λ(B))`. -/
def SimOrdSpecDecomp {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  ∃ U ∈ Matrix.orthogonalGroup (Fin k) ℝ,
    Uᵀ * A * U = Matrix.diagonal (ModernConvex.Spectral.eigVec A) ∧
    Uᵀ * B * U = Matrix.diagonal (ModernConvex.Spectral.eigVec B)

/-- The directional derivative of the eigenvalue map, (2.9) (p.4):
`λ'(X; H) = lim_{t↓0} (λ(X + tH) − λ(X)) / t`.
**Formalization Note.** Defined as the one-sided limit (`limUnder`); its existence is part of
Corollary 2.3 (`SpectralParab.corollary_2_3`). The block formula of (2.9) is a theorem
(`SpectralParab.proposition_2_1`), not the definition. -/
noncomputable def lamDir {n : ℕ} (X H : SymMat (Fin n)) : Rn n :=
  limUnder (𝓝[>] (0 : ℝ)) (fun t : ℝ => t⁻¹ • (lam (X + t • H) - lam X))

/-- The parabolic second-order directional derivative of the eigenvalue map (p.5):
`λ''(X; H, W) = lim_{t↓0} (λ(X + tH + ½t²W) − λ(X) − t λ'(X; H)) / (½ t²)`.
**Formalization Note.** A one-sided limit (`limUnder`); its existence is part of Corollary 2.3. -/
noncomputable def lamDir2 {n : ℕ} (X H W : SymMat (Fin n)) : Rn n :=
  limUnder (𝓝[>] (0 : ℝ))
    (fun t : ℝ => (2 / t ^ 2) • (lam (X + t • H + (t ^ 2 / 2) • W) - lam X - t • lamDir X H))

end SpectralParab


