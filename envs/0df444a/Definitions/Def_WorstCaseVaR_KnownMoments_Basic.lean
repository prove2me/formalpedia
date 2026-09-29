-- Prove2me | Definitions.Def_WorstCaseVaR_KnownMoments_Basic
-- name    : WorstCaseVaR_KnownMoments_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:12:42.386348+00:00
-- url     : https://prove2.me/theorems/8a3bf9f2-31bb-494f-8f66-13934ac95670
-- title:
--   Known-moment model of worst-case VaR: loss set, the class $\mathcal P$ of distributions with mean $\hat x$ and covariance $\Gamma$, $\kappa(\varepsilon)$, and $\Sigma$
-- statement:
--   This file fixes the objects of §2.1 of El Ghaoui, Oks and Oustry (2003) on which every statement of the mission rests.
--
--   The returns of $n$ assets over one period form a random vector $x \in \mathbb R^n$, and a portfolio $w \in \mathbb R^n$ earns the return $r(w,x) = w^\top x$.
--
--   1. **Loss set** (Eq. (13)). For a loss level $\gamma \in \mathbb R$,
--   $$\mathcal S = \{x \in \mathbb R^n \mid \gamma \le -x^\top w\},$$
--   the returns for which the portfolio loses at least $\gamma$.
--   2. **The class $\mathcal P$** (Theorem 1). A Borel probability measure $P$ on $\mathbb R^n$ belongs to the class with mean $\hat x$ and covariance $\Gamma$ when every coordinate $x_i$ is square-integrable under $P$ and
--   $$\mathbb E_P[x_i] = \hat x_i, \qquad \mathbb E_P[(x_i - \hat x_i)(x_j - \hat x_j)] = \Gamma_{ij} \quad (1 \le i,j \le n).$$
--   Arbitrary probability measures are allowed, including discrete ones; no density is assumed.
--   3. **The constant** (Eq. (8)) $\kappa(\varepsilon) = \sqrt{(1-\varepsilon)/\varepsilon}$.
--   4. **Bordered matrices.** For an $n\times n$ matrix $A$, a vector $v\in\mathbb R^n$ and a scalar $c$, $\begin{bmatrix} A & v \\ v^\top & c\end{bmatrix}$ denotes the $(n+1)\times(n+1)$ block matrix; all the matrix conditions (6), (9), (10), (11), (18) of the paper are of this shape.
--   5. **Second-moment matrix** (Eq. (6)). With $S = \Gamma + \hat x \hat x^\top$,
--   $$\Sigma = \begin{bmatrix} S & \hat x \\ \hat x^\top & 1\end{bmatrix},$$
--   which is $\mathbb E\,[x;1][x;1]^\top$ for every $P$ in the class; here it is defined directly from $\hat x$ and $\Gamma$.
--   6. **The quadratic function** (Eq. (15)) of a symmetric $(n+1)\times(n+1)$ matrix $M$: $l(x) = [x^\top\ 1]\, M\, [x^\top\ 1]^\top$.
--
--   These are the data of the worst-case Value-at-Risk problem with known first and second moments.
--
--   **Formalization Note.** Vectors live in `EuclideanSpace ℝ (Fin n)`, with $x^\top w$ the inner product and coordinates read through the coercion to `Fin n → ℝ`. Matrices of size $n+1$ are indexed by `Fin n ⊕ Fin 1` (`Matrix.fromBlocks`). The square-integrability clause (`MemLp … 2`) is part of the class so that the mean and covariance are genuine moments: without it a Bochner integral of a non-integrable function is $0$. The class is nonempty for $\Gamma \succ 0$: the Gaussian $\mathcal N(\hat x, \Gamma)$ belongs to it.
-- source:
--   El Ghaoui, Oks and Oustry, Worst-Case Value-at-Risk and Robust Portfolio Optimization: A Conic Programming Approach, Oper. Res. 51 (2003), p. 543 (model r(w,x) = w^T x), p. 545, §2.1, Eq. (6), Theorem 1 (class 𝒫), Eq. (8); p. 546, Eqs. (13), (15). DOI 10.1287/opre.51.4.543.16101

import Mathlib

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace WorstCaseVaR.KnownMoments

/-- The loss set `𝒮 = {x | γ ≤ -xᵀw}` of El Ghaoui–Oks–Oustry (2003), Eq. (13), p. 546:
the returns `x ∈ ℝⁿ` for which the portfolio `w` loses at least `γ`, i.e. `γ ≤ -r(w, x)` with
`r(w, x) = wᵀx`. -/
def lossSet {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (γ : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | γ ≤ -⟪w, x⟫_ℝ}

/-- `P` is a probability distribution on `ℝⁿ` (a Borel probability measure, not necessarily with a
density) with mean vector `xhat` and covariance matrix `Γ` (Theorem 1, p. 545: the class `𝒫`).
Square-integrability of every coordinate is part of the predicate, so that the mean and the
covariance are genuine (finite) moments. -/
structure HasMeanCov {n : ℕ} (P : Measure (EuclideanSpace ℝ (Fin n)))
    (xhat : EuclideanSpace ℝ (Fin n)) (Γ : Matrix (Fin n) (Fin n) ℝ) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure P
  memLp_two : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 P
  mean_eq : ∀ i : Fin n, ∫ x, x i ∂P = xhat i
  cov_eq : ∀ i j : Fin n, ∫ x, (x i - xhat i) * (x j - xhat j) ∂P = Γ i j

/-- `κ(ε) = √((1 - ε)/ε)`, Eq. (8), p. 545. -/
noncomputable def kappa (ε : ℝ) : ℝ :=
  Real.sqrt ((1 - ε) / ε)

/-- The bordered symmetric block matrix `[[A, v], [vᵀ, c]]` of size `(n+1) × (n+1)`, indexed by
`Fin n ⊕ Fin 1`: upper-left block `A`, column `v`, row `vᵀ`, scalar corner `c`. -/
def bordered {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (c : ℝ) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks A (Matrix.of fun i _ => v i) (Matrix.of fun _ j => v j) (Matrix.of fun _ _ => c)

/-- `S = Γ + x̂x̂ᵀ`, Eq. (6), p. 545. -/
def momentS {n : ℕ} (xhat : EuclideanSpace ℝ (Fin n)) (Γ : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Γ + Matrix.vecMulVec ⇑xhat ⇑xhat

/-- The second-moment matrix `Σ = [[S, x̂], [x̂ᵀ, 1]]`, `S = Γ + x̂x̂ᵀ`, Eq. (6), p. 545,
defined directly from the mean `x̂` and the covariance `Γ`. -/
def secondMomentMatrix {n : ℕ} (xhat : EuclideanSpace ℝ (Fin n)) (Γ : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  bordered (momentS xhat Γ) ⇑xhat 1

/-- The lifted vector `[x; 1] ∈ ℝ^{n+1}`. -/
def liftVec {n : ℕ} (x : Fin n → ℝ) : Fin n ⊕ Fin 1 → ℝ :=
  Sum.elim x (fun _ => 1)

/-- The quadratic function `l(x) = [xᵀ 1] M [xᵀ 1]ᵀ`, Eq. (15), p. 546. -/
def quadFn {n : ℕ} (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) (x : Fin n → ℝ) : ℝ :=
  liftVec x ⬝ᵥ (M *ᵥ liftVec x)

end WorstCaseVaR.KnownMoments


