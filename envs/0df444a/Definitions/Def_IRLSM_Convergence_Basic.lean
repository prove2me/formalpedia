-- Prove2me | Definitions.Def_IRLSM_Convergence_Basic
-- name    : IRLSM_Convergence_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:51:12.336303+00:00
-- url     : https://prove2.me/theorems/74041164-b216-4690-bfb9-c17a4dcc97cb
-- title:
--   Singular values $\sigma_i$, $\|\mathcal S(X)\|^2$, $\rho_k(X)_*$, the rank-RIP constant $\delta_k$, and the (strong) rank null space property (Definitions 1.1, 6.2, 6.4)
-- statement:
--   Let $X$ be a real $n\times p$ matrix with singular values $\sigma_1(X)\ge\sigma_2(X)\ge\cdots\ge0$ (the square roots of the eigenvalues of $X^{\mathsf T}X$, in decreasing order; $\sigma_i(X)=0$ for $i>p$). Let $\|X\|_*=\sum_i\sigma_i(X)$ be the nuclear norm and $\|X\|_F$ the Frobenius norm. A linear measurement map $\mathcal S:\mathbb R^{n\times p}\to\mathbb R^m$ is given by matrices $A_1,\dots,A_m$ via $\mathcal S(X)_l=\langle A_l,X\rangle=\sum_{i,j}(A_l)_{ij}X_{ij}$.
--
--   This module defines:
--
--   1. the singular values $\sigma_{i+1}(X)$, indexed from $0$;
--   2. $\|\mathcal S(X)\|_{\ell_2^m}^2=\sum_l\mathcal S(X)_l^2$;
--   3. the **best $k$-rank approximation error** in the nuclear norm,
--   $$\rho_k(X)_*=\inf_{\operatorname{rank}Z\le k}\|X-Z\|_*;$$
--   4. the **restricted isometry constant** $\delta_k$ of $\mathcal S$, the smallest $\delta\ge0$ with $(1-\delta)\|X\|_F^2\le\|\mathcal S(X)\|_{\ell_2^m}^2\le(1+\delta)\|X\|_F^2$ for all $X$ of rank at most $k$;
--   5. the **rank null space property (RNSP)** of order $k$: for every $H\in\ker\mathcal S\setminus\{0\}$ and every decomposition $H=H_1+H_2$ with $\operatorname{rank}H_1\le k$, $\|H_1\|_*<\|H_2\|_*$;
--   6. the **strong rank null space property (SRNSP)** of order $k$ with constant $\eta\in(0,1)$: for every $X\in\ker\mathcal S\setminus\{0\}$ and every decomposition $X=X_1+X_2$ with $\operatorname{rank}X_1\le k$ there is a decomposition $X=H_1+H_2$ with $\operatorname{rank}H_1\le 2k$, $\langle H_1,H_2\rangle=0$, $X_1H_2^{\mathsf T}=0$, $X_1^{\mathsf T}H_2=0$ and
--   $$\|H_1\|_*\le\eta\|H_2\|_*.$$
--
--   These are the objects of the null space analysis of the IRLS-M algorithm; every statement of the mission is phrased with them.
--
--   **Formalization Note** `sv X i` is $\sigma_{i+1}(X)$ (0-based). $\rho_k$ and $\delta_k$ are real infima over nonempty sets bounded below by $0$, so they are never junk values; $\delta_k$ is defined for every $k\in\mathbb N$ in the squared form of the page. Real matrices; $\eta\in(0,1)$ is part of the SRNSP, as on the page. The Euclidean norm of $\mathcal S(X)$ is written as a sum of squares (Mathlib's norm on $\mathbb R^m$ is the sup norm).
-- source:
--   Fornasier, Rauhut, Ward, Low-rank matrix recovery via iteratively reweighted least squares minimization, arXiv:1010.2471v4 (2011), Definition 1.1, p. 2; §2.1, pp. 3–4; Definition 6.2, p. 16; Definition 6.4 and the definition of ρ_k, p. 17

import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core

open HighDimStat.MatrixRank Matrix

namespace IRLSM.Convergence

/-- The singular values of a real `n × p` matrix, **0-based**: `sv X i` is the page's
`σ_{i+1}(X)`, the `(i+1)`-st largest singular value. Thus `σ_{K+1}(X)` is `sv X K` and `σ_J(X)` is
`sv X (J - 1)`. Indices `i ≥ p` give `0`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, §2.1, pp. 3–4 (`σ(X) = (σ_1, …, σ_n)`, decreasing).

Formalization Note: built on `singularValues` of `HighDimStat_MatrixRank_Core` (square roots of the
eigenvalues of `XᵀX` in decreasing order, indexed by `Fin p`). Under the page's standing assumption
`n ≤ p`, the entries `0, …, n - 1` are `σ_1, …, σ_n` and the remaining ones are `0`. -/
noncomputable def sv {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (i : ℕ) : ℝ :=
  if h : i < p then singularValues X ⟨i, h⟩ else 0

/-- `‖S(X)‖²_{ℓ_2^m}`, the squared Euclidean norm of the measurement vector `S(X)`, where
`S(X)_l = ⟨A_l, X⟩` (`observationOp`).

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, Definition 1.1, p. 2.

Formalization Note: the Euclidean norm is written out as a sum of squares; the norm of
`Fin m → ℝ` in Mathlib is the sup norm and is not used. -/
noncomputable def measSq {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ)
    (X : Matrix (Fin n) (Fin p) ℝ) : ℝ :=
  ∑ l, (observationOp A X l) ^ 2

/-- The best `k`-rank approximation error in the nuclear norm,
`ρ_k(X)_* := min_{rank Z ≤ k} ‖X − Z‖_*`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, §6.2, p. 17.

Formalization Note: written as a real `sInf`; the set is nonempty (`Z = 0`) and bounded below by
`0`, so the infimum is never a junk value. That it is attained (at the `k`-spectral truncation) is
a separate statement of the mission. -/
noncomputable def rho {n p : ℕ} (k : ℕ) (X : Matrix (Fin n) (Fin p) ℝ) : ℝ :=
  sInf ((fun Z : Matrix (Fin n) (Fin p) ℝ => nuclearNorm (X - Z)) ''
    {Z : Matrix (Fin n) (Fin p) ℝ | Z.rank ≤ k})

/-- The `k`-restricted isometry constant `δ_k(S)`: the smallest `δ ≥ 0` such that
`(1 − δ)‖X‖²_F ≤ ‖S(X)‖²_{ℓ_2^m} ≤ (1 + δ)‖X‖²_F` for every matrix `X` of rank at most `k`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, Definition 1.1, p. 2 ("k-rank" = rank ≤ k, p. 4).

Formalization Notes: real matrices; `S` is given by measurement matrices `A l`
(`S(X)_l = ⟨A_l, X⟩`); the **squared** form of the page is used. The constant is defined for
every `k : ℕ`. The set is nonempty and bounded below by `0`, so the real `sInf` is its minimum,
never a junk value. -/
noncomputable def ripConst {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (k : ℕ) : ℝ :=
  sInf {δ : ℝ | 0 ≤ δ ∧ ∀ X : Matrix (Fin n) (Fin p) ℝ, X.rank ≤ k →
    (1 - δ) * frobeniusNorm X ^ 2 ≤ measSq A X ∧ measSq A X ≤ (1 + δ) * frobeniusNorm X ^ 2}

/-- The rank null space property (RNSP) of order `k`: for all `H ∈ ker S \ {0}` and all
decompositions `H = H₁ + H₂` with `rank H₁ ≤ k`, `‖H₁‖_* < ‖H₂‖_*`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, Definition 6.2, p. 16.

Formalization Note: real matrices; `S` is given by measurement matrices (`observationOp`). -/
def RNSP {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (k : ℕ) : Prop :=
  ∀ H : Matrix (Fin n) (Fin p) ℝ, observationOp A H = 0 → H ≠ 0 →
    ∀ H₁ H₂ : Matrix (Fin n) (Fin p) ℝ, H = H₁ + H₂ → H₁.rank ≤ k →
      nuclearNorm H₁ < nuclearNorm H₂

/-- The strong rank null space property (SRNSP) of order `k` with constant `η ∈ (0, 1)`: for
every `X ∈ ker S \ {0}` and every decomposition `X = X₁ + X₂` with `rank X₁ ≤ k` there is a
decomposition `X = H₁ + H₂` with `rank H₁ ≤ 2k`, `⟨H₁, H₂⟩ = 0`, `X₁ H₂ᵀ = 0`, `X₁ᵀ H₂ = 0` and
`‖H₁‖_* ≤ η ‖H₂‖_*`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, Definition 6.4, p. 17.

Formalization Notes: real matrices, so `X*` is `Xᵀ` and `⟨·,·⟩` is `traceInner`; `S` is given
by measurement matrices; `η ∈ (0, 1)` is part of the property, as on the page. -/
def SRNSP {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (k : ℕ) (η : ℝ) : Prop :=
  0 < η ∧ η < 1 ∧
    ∀ X : Matrix (Fin n) (Fin p) ℝ, observationOp A X = 0 → X ≠ 0 →
      ∀ X₁ X₂ : Matrix (Fin n) (Fin p) ℝ, X = X₁ + X₂ → X₁.rank ≤ k →
        ∃ H₁ H₂ : Matrix (Fin n) (Fin p) ℝ, X = H₁ + H₂ ∧ H₁.rank ≤ 2 * k ∧
          traceInner H₁ H₂ = 0 ∧ X₁ * H₂ᵀ = 0 ∧ X₁ᵀ * H₂ = 0 ∧
          nuclearNorm H₁ ≤ η * nuclearNorm H₂

end IRLSM.Convergence


