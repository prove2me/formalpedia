-- Prove2me | Definitions.Def_ModernConvex_Spectral_SDR
-- name    : ModernConvex_Spectral_SDR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:53.483093+00:00
-- url     : https://prove2.me/theorems/7d5b09c7-b4a2-4500-af3d-5f83e324841c
-- title:
--   Eigenvalue and singular value vectors, Ky Fan sums, symmetric and convex functions, double-stochastic matrices, permutation hulls, SDRs of epigraphs
-- statement:
--   The objects of §4.2 and Exercises 4.14–4.16 of the book, for real vectors $x \in \mathbb R^m$ and real matrices.
--
--   1. **Eigenvalue vector** (p. 147). For a symmetric $m\times m$ matrix $X$, $\lambda(X) = (\lambda_1(X),\dots,\lambda_m(X))^T$ lists the eigenvalues of $X$ counted with multiplicity and arranged in nonascending order, $\lambda_1(X) \ge \lambda_2(X) \ge \cdots \ge \lambda_m(X)$.
--   2. **Partial sums** $x_1 + \cdots + x_j$ of the first $j$ coordinates of a vector $x$.
--   3. **Sum of the $k$ largest eigenvalues** (p. 147): $S_k(X) = \sum_{i=1}^k \lambda_i(X)$.
--   4. **Sum of the $j$ largest entries** of a vector $y \in \mathbb R^m$ (p. 285): $S_j(y) = \max\{\sum_{i\in s} y_i : s \subseteq \{1,\dots,m\},\ |s| = j\}$.
--   5. **Symmetric function** (p. 281): $f(x_{\sigma(1)},\dots,x_{\sigma(m)}) = f(x)$ for every permutation $\sigma$ and every $x$.
--   6. **Convex function with values in $\mathbb R \cup \{+\infty\}$**: a function that never takes the value $-\infty$ and whose epigraph $\{(x,t) \in \mathbb R^m\times\mathbb R : f(x) \le t\}$ is convex.
--   7. **Double-stochastic matrices** $\mathcal S_m$ (p. 281): $p_{ij} \ge 0$, $\sum_{i} p_{ij} = 1$ for every $j$, $\sum_j p_{ij} = 1$ for every $i$.
--   8. **Permutation hull** $X[x]$ (p. 285): the set of all convex combinations of the $m!$ vectors obtained from $x$ by permuting its coordinates.
--   9. **Affine matrix maps** $\mathcal S(x,t,u) = S_0 + \sum_{i=1}^m x_i S^x_i + t\,S^t + \sum_{l=1}^k u_l S^u_l$ from $\mathbb R^m\times\mathbb R\times\mathbb R^k$ into the symmetric $N\times N$ matrices, with symmetric coefficient matrices ("$\mathcal S$ affinely depending on $x, t, u$", pp. 151, 154).
--   10. **Semidefinite representation of an epigraph** (p. 144): $\mathcal S$ represents $g : \mathbb R^m \to \mathbb R\cup\{+\infty\}$ if for all $x \in \mathbb R^m$, $t \in \mathbb R$:
--   $$t \ge g(x) \iff \exists u \in \mathbb R^k : \mathcal S(x,t,u) \succeq 0.$$
--   11. **Singular values** (pp. 151–152) of a $k\times l$ matrix $X$: $\sigma_i(X) = \lambda_i\big((XX^T)^{1/2}\big)$, $i = 1,\dots,k$, in nonascending order, and $\Sigma_p(X) = \sum_{i=1}^p \sigma_i(X)$.
--
--   These are the objects in which the book states the semidefinite representability of symmetric functions of eigenvalues (Proposition 4.2.1) and of singular values (Proposition 4.2.2), and the majorization principle used to prove them.
--
--   **Formalization Note** Vectors are `Fin m → ℝ`, so the book's index $i$ is `i : Fin m` with value $i-1$. $\lambda(X)$ is built from Mathlib's sorted eigenvalues `IsHermitian.eigenvalues₀`; on a non-symmetric matrix it returns the junk value $0$, but every statement applies it to symmetric matrices only. $S_j(y)$ is a real supremum over the $j$-element index sets; it is used only for $j \le m$, where it is an attained maximum. Functions with values in $\mathbb R\cup\{+\infty\}$ are `EReal`-valued, and every statement assumes they never equal $-\infty$. The singular values are written as $\sigma_i(X) = \sqrt{\lambda_i(XX^T)}$. This is the same number: $XX^T$ is positive semidefinite and its square root has eigenvalues $\sqrt{\lambda_i(XX^T)}$ in the same order. Symmetric matrices are `Matrix.IsHermitian` over $\mathbb R$, and $A \succeq 0$ is `Matrix.PosSemidef`.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 144 (SDr sets and functions), p. 147 (λ(X), S_k(X)), pp. 151–152 (singular values, Σ_p), p. 154 (Proposition 4.2.2's 𝒮), p. 281 (double-stochastic matrices, symmetric functions), p. 285 (X[x], S_j(y))

import Mathlib

open Matrix

namespace ModernConvex.Spectral

/-- The vector of eigenvalues `λ(X) = (λ₁(X), …, λ_m(X))ᵀ` of a symmetric `m × m` real matrix
(Ben-Tal–Nemirovski, p. 147): the eigenvalues counted with their multiplicities and arranged in
nonascending order, `λ₁(X) ≥ λ₂(X) ≥ ⋯ ≥ λ_m(X)`; index `i : Fin m` is the book's `λ_{i+1}`.
Built from Mathlib's sorted eigenvalues `IsHermitian.eigenvalues₀` (antitone). A non-symmetric
input gets the junk value `0`; every statement of the mission applies `eigVec` to symmetric
matrices only. -/
noncomputable def eigVec {m : ℕ} (X : Matrix (Fin m) (Fin m) ℝ) : Fin m → ℝ :=
  if h : X.IsHermitian then fun i => h.eigenvalues₀ (Fin.cast (Fintype.card_fin m).symm i)
  else 0

/-- The partial sum `x₁ + ⋯ + x_j` of the first `j` coordinates of `x ∈ ℝᵐ` (all of them when
`j ≥ m`). -/
def partialSum {m : ℕ} (j : ℕ) (x : Fin m → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < j), x i

/-- The sum of the `k` largest eigenvalues of a symmetric `m × m` matrix (p. 147):
`S_k(X) = ∑_{i=1}^k λᵢ(X)`. -/
noncomputable def sumLargestEig {m : ℕ} (k : ℕ) (X : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  partialSum k (eigVec X)

/-- The sum of the `j` largest entries of a vector `y ∈ ℝᵐ` (p. 285, "Sⱼ(y) is the sum of the
largest j entries of a vector y"): the maximum of `∑_{i ∈ s} yᵢ` over the `j`-element index
sets `s`. Used only for `j ≤ m`, where the index type is nonempty and finite, so the real
supremum is an attained maximum (for `j > m` it would be the junk value `0`). -/
noncomputable def sumLargest {m : ℕ} (j : ℕ) (y : Fin m → ℝ) : ℝ :=
  ⨆ s : {s : Finset (Fin m) // s.card = j}, ∑ i ∈ s.1, y i

/-- Symmetry of a function of `x ∈ ℝᵐ` (p. 281): its value is unchanged when the coordinates
of the argument are permuted, `f(x ∘ σ) = f(x)` for every permutation `σ`. -/
def IsSymmetricFn {m : ℕ} {β : Type*} (f : (Fin m → ℝ) → β) : Prop :=
  ∀ (σ : Equiv.Perm (Fin m)) (x : Fin m → ℝ), f (x ∘ σ) = f x

/-- Convexity of a function `f : ℝᵐ → ℝ ∪ {+∞}`, modelled as an `EReal`-valued function that
never takes the value `−∞`, whose epigraph `{(x, t) ∈ ℝᵐ × ℝ | f(x) ≤ t}` is convex. -/
def IsConvexExt {m : ℕ} (f : (Fin m → ℝ) → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ Convex ℝ {p : (Fin m → ℝ) × ℝ | f p.1 ≤ (p.2 : EReal)}

/-- The set `𝒮_m` of double-stochastic `m × m` matrices (p. 281): `pᵢⱼ ≥ 0`,
`∑ᵢ pᵢⱼ = 1` for every column `j`, `∑ⱼ pᵢⱼ = 1` for every row `i`. -/
def IsDoublyStochastic {m : ℕ} (P : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ (∀ j, ∑ i, P i j = 1) ∧ (∀ i, ∑ j, P i j = 1)

/-- `X[x]` (p. 285): the set of all convex combinations of the `m!` vectors obtained from
`x ∈ ℝᵐ` by all permutations of the coordinates. -/
def permHull {m : ℕ} (x : Fin m → ℝ) : Set (Fin m → ℝ) :=
  convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin m) => x ∘ σ)

/-- An affine map `(x, t, u) ↦ 𝒮(x, t, u)` from `ℝᵐ × ℝ × ℝᵏ` into the space `S^N` of symmetric
`N × N` matrices (pp. 151, 154: "with 𝒮 affinely depending on x, t, u"):
`𝒮(x, t, u) = S₀ + ∑ᵢ xᵢ Sxᵢ + t St + ∑ₗ uₗ Suₗ` with symmetric coefficient matrices. -/
structure EpiLMI (m k N : ℕ) where
  /-- the constant term -/
  S₀ : Matrix (Fin N) (Fin N) ℝ
  /-- the coefficient of `xᵢ` -/
  Sx : Fin m → Matrix (Fin N) (Fin N) ℝ
  /-- the coefficient of `t` -/
  St : Matrix (Fin N) (Fin N) ℝ
  /-- the coefficient of `uₗ` -/
  Su : Fin k → Matrix (Fin N) (Fin N) ℝ
  S₀_symm : S₀.IsHermitian
  Sx_symm : ∀ i, (Sx i).IsHermitian
  St_symm : St.IsHermitian
  Su_symm : ∀ l, (Su l).IsHermitian

/-- The value `𝒮(x, t, u)` of the affine map. -/
def EpiLMI.eval {m k N : ℕ} (S : EpiLMI m k N) (x : Fin m → ℝ) (t : ℝ) (u : Fin k → ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  S.S₀ + ∑ i, x i • S.Sx i + t • S.St + ∑ l, u l • S.Su l

/-- `𝒮` is a semidefinite representation (SDR) of the epigraph of `g : ℝᵐ → ℝ ∪ {+∞}`
(p. 144, pp. 151, 154): for every `x ∈ ℝᵐ` and `t ∈ ℝ`, `t ≥ g(x) ⇔ ∃ u : 𝒮(x, t, u) ⪰ 0`. -/
def EpiLMI.Represents {m k N : ℕ} (S : EpiLMI m k N) (g : (Fin m → ℝ) → EReal) : Prop :=
  ∀ (x : Fin m → ℝ) (t : ℝ), g x ≤ (t : EReal) ↔ ∃ u : Fin k → ℝ, (S.eval x t u).PosSemidef

/-- The vector of singular values `σ(X) = (σ₁(X), …, σ_k(X))` of a `k × l` real matrix
(pp. 151–152): `σᵢ(X) = λᵢ((XXᵀ)^{1/2})`, in nonascending order. Written as
`σᵢ(X) = √(λᵢ(XXᵀ))`, which is the same number: `XXᵀ` is symmetric positive semidefinite and its
square root has the eigenvalues `√(λᵢ(XXᵀ))`, in the same order. -/
noncomputable def singVec {k l : ℕ} (X : Matrix (Fin k) (Fin l) ℝ) : Fin k → ℝ :=
  fun i => Real.sqrt (eigVec (X * Xᵀ) i)

/-- The sum of the `p` largest singular values (p. 152): `Σ_p(X) = ∑_{i=1}^p σᵢ(X)`. -/
noncomputable def sumLargestSing {k l : ℕ} (p : ℕ) (X : Matrix (Fin k) (Fin l) ℝ) : ℝ :=
  partialSum p (singVec X)

end ModernConvex.Spectral


