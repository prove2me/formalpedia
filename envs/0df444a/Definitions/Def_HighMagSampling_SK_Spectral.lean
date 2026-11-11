-- Prove2me | Definitions.Def_HighMagSampling_SK_Spectral
-- name    : HighMagSampling_SK_Spectral
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:27:38.146209+00:00
-- url     : https://prove2.me/theorems/edaf06b2-04e9-4b02-ac82-76f9a09a8138
-- title:
--   Second eigenvalue $\lambda_2(P)$ of a random walk, link graphs $P_R$, $m(K)$, $\rho(K)$, $\|\cdot\|_{\mathrm{op}}$, $\Delta$ and $\bar\beta$
-- statement:
--   **Eigenvalues.** For a real symmetric $n\times n$ matrix $M$, $\lambda_1(M)\ge\lambda_2(M)\ge\dots\ge\lambda_n(M)$ are its eigenvalues counted with multiplicity; $\lambda_2(M)$ is the second largest.
--
--   **Random walks.** For an edge weight matrix $W\in\mathbb R^{n\times n}_{\ge0}$ the random walk matrix is
--   $$P=D^{-1}W,\qquad D=\mathrm{diag}(W\mathbf 1_n).$$
--   For symmetric $W$ with positive degrees $D_{ii}$, $P$ is similar to the symmetric matrix $N=D^{-1/2}WD^{-1/2}$, and $\lambda_2(P):=\lambda_2(N)$.
--
--   **Link graphs.** For a probability measure $\pi$ on $\mathcal X^d_k$ and $R\subseteq[d]$ with $|R|=k-2$, the link graph of $R$ has vertex set $[d]\setminus R$ and weights $W_{ij}=\pi(R\cup\{i,j\})$ for $i\ne j$ ($W_{ii}=0$); $P_R$ is its random walk matrix.
--
--   **Perturbation parameters.** For $K\in\mathbb R^{d\times d}$, let $m(K)=\max_{i,j}|K_{ij}|$, let $X$ have entries $X_{ij}=\exp(K_{ij})-1$, let $\mathrm{nnz}(u)$ count the nonzero entries of $u$, and
--   $$\rho(K)=\max\Big(0,\ \sup_{u\in\mathbb R^d:\ \mathrm{nnz}(u)>1}\frac{u^\top(X-I_d)u}{\|u\|_1^2-\|u\|_2^2}\Big).$$
--
--   **Norms and scales.** $\|M\|_{\mathrm{op}}$ is the $(2\to2)$ operator norm. For $d\ge1$ and $\delta>0$, $\Delta=\sqrt{\log(d/\delta)/d}+\log(d/\delta)/d$ (Eq. (31)), and $\bar\beta=\max(1,\beta)$. Logarithms are natural.
--
--   These are the quantities in the trickle-down criterion (Lemma 6), the rank-one perturbation bound (Lemma 7) and the temperature and sparsity conditions of Theorem 4.
--
--   **Formalization Note.** `lambdaTwo M` is Mathlib's sorted `eigenvalues₀` at index `1` when $M$ is symmetric of size at least $2$, and $0$ otherwise; the statements only evaluate it on symmetric matrices of size at least $2$. `lambdaTwoRW W` is `lambdaTwo` of $N=(W_{ij}/(\sqrt{D_{ii}}\sqrt{D_{jj}}))_{ij}$, the matrix the paper uses in the proof of Lemma 7 ("$\lambda_2(P)=\lambda_2(N)$"), which is the second eigenvalue of $P$ with multiplicity whenever all degrees are positive. The link-graph weight is read off $\pi$ at the slice element whose underlying set is $R\cup\{i,j\}$. $m(K)$ is an iterated supremum over the finite index set, i.e. the maximum when $d\ge1$. The supremum in $\rho(K)$ is the real `sSup` of the set of ratios: that set is bounded above by $\max_{i\ne j}|X_{ij}|$ (the denominator equals $\sum_{i\ne j}|u_i||u_j|$), so `sSup` is the true supremum, and for $d\le1$ the set is empty and $\rho(K)=\max(0,0)=0$. `opNorm M` is the norm of $M$ as a continuous linear map on Euclidean space.
-- source:
--   Kumar, Sarkar, Tian, Zhu, High-Magnetization Sampling at Low Temperatures, arXiv:2609.08873v1, p. 9, §2.1 (eigenvalues, nnz, operator norm); p. 19, Eq. (18) and link graph; p. 20, Lemma 7, Eq. (21); p. 26, Eq. (31); p. 27, Theorem 4 (β̄)

import Mathlib
import Definitions.Def_HighMagSampling_SK_DownUp

open MeasureTheory Matrix
open scoped ENNReal

namespace HighMagSampling.SK

/-!
# Second eigenvalues of random walks, link graphs, `m(K)`, `ρ(K)`, operator norm, `Δ`, `β̄`

Kumar, Sarkar, Tian, Zhu, *High-Magnetization Sampling at Low Temperatures*, arXiv:2609.08873v1,
§2.1, p. 9 (PDF p. 11); §4.1, Eq. (18), p. 19 (PDF p. 21); Lemma 7, Eq. (21), p. 20 (PDF p. 22);
Theorem 4 and Eq. (31), pp. 26–27 (PDF pp. 28–29).

**Formalization Note.**
* `lambdaTwo M` is `λ₂(M)`, the second largest eigenvalue counted with multiplicity of a real
  symmetric matrix (`λ₁ ≥ λ₂ ≥ … ≥ λ_n`, p. 9): Mathlib's `eigenvalues₀` are sorted
  nonincreasingly, so `λ₂` is the entry at index `1`. It is used only for symmetric matrices of
  size at least `2`; elsewhere it is `0` (a junk value never reached by the statements).
* For an edge weight matrix `W ≥ 0`, the random walk matrix is `P = D⁻¹W`, `D = diag(W 1)` (18).
  `lambdaTwoRW W` is `λ₂(P)`, computed as `λ₂` of the similar symmetric matrix
  `N = D^{-1/2} W D^{-1/2}`, as in the proof of Lemma 7 ("`λ₂(P) = λ₂(N)`"). When every degree
  `D_ii` is positive, `P` and `N` have the same eigenvalues with multiplicity.
* `linkWeight π R` is the link graph of `R` (p. 19): vertices `[d] \ R`, weights
  `W_ij = π(R ∪ {i, j})` for `i ≠ j`, `W_ii = 0`.
* `maxAbs K = max_{i,j} |K_ij|` (written as an iterated `⨆` over the finite index, a maximum for
  `d ≥ 1`), `expMinusOne K = (exp(K_ij) − 1)_{ij}` is the matrix `X` of (21), `nnz u` the number of
  nonzero entries.
* `rho K = max(0, sup_{u : nnz(u) > 1} uᵀ(X − I)u / (‖u‖₁² − ‖u‖₂²))` (21). The ratio is bounded
  above by `max_{i≠j} |X_ij|` (the denominator is `Σ_{i≠j} |u_i||u_j|`), so the real `sSup` is the
  supremum; for `d ≤ 1` the set is empty and `rho K = max(0, 0) = 0`, the page's convention.
* `opNorm M` is the `(2 → 2)` operator norm `‖M‖_op` (p. 9), the norm of `M` acting on Euclidean
  space.
* `Delta d δ = √(log(d/δ)/d) + log(d/δ)/d` (31) and `betaBar β = max(1, β)` (Theorem 4); natural log.
-/

/-- `λ₂(M)`: the second largest eigenvalue, with multiplicity, of a real symmetric matrix (p. 9). -/
noncomputable def lambdaTwo {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) : ℝ :=
  open Classical in
  if h : M.IsHermitian ∧ 2 ≤ Fintype.card n then h.1.eigenvalues₀ ⟨1, h.2⟩ else 0

/-- The degree `D_ii = (W 1)_i` (Eq. (18)). -/
noncomputable def degree {n : Type*} [Fintype n] (W : Matrix n n ℝ) (i : n) : ℝ :=
  ∑ j, W i j

/-- `N = D^{-1/2} W D^{-1/2}`, the symmetric matrix similar to `P = D⁻¹W` (proof of Lemma 7). -/
noncomputable def normalizedWeight {n : Type*} [Fintype n] (W : Matrix n n ℝ) : Matrix n n ℝ :=
  fun i j => W i j / (Real.sqrt (degree W i) * Real.sqrt (degree W j))

/-- `λ₂(P)` for the random walk matrix `P = D⁻¹W` of a symmetric weight matrix `W` (Eq. (18)). -/
noncomputable def lambdaTwoRW {n : Type*} [Fintype n] [DecidableEq n] (W : Matrix n n ℝ) : ℝ :=
  lambdaTwo (normalizedWeight W)

/-- The link graph of `R` (p. 19): on `[d] \ R`, `W_ij = π(R ∪ {i, j})` for `i ≠ j`, `W_ii = 0`. -/
noncomputable def linkWeight {d k : ℕ} (π : Measure (Slice d k)) (R : Finset (Fin d)) :
    Matrix {i : Fin d // i ∉ R} {i : Fin d // i ∉ R} ℝ :=
  fun i j => if i = j then 0 else (π {S | S.1 = insert i.1 (insert j.1 R)}).toReal

/-- `m(K) = max_{(i,j)} |K_ij|` (Eq. (21)). -/
noncomputable def maxAbs {d : ℕ} (K : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ⨆ i, ⨆ j, |K i j|

/-- The matrix `X` with `X_ij = exp(K_ij) − 1` entrywise (Eq. (21)). -/
noncomputable def expMinusOne {d : ℕ} (K : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => Real.exp (K i j) - 1

/-- `nnz(u)`, the number of nonzero entries of `u` (p. 9). -/
noncomputable def nnz {d : ℕ} (u : Fin d → ℝ) : ℕ :=
  open Classical in (Finset.univ.filter (fun i => u i ≠ 0)).card

/-- `ρ(K) = max(0, sup_{nnz(u) > 1} uᵀ(X − I_d)u / (‖u‖₁² − ‖u‖₂²))` (Eq. (21)). -/
noncomputable def rho {d : ℕ} (K : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  max 0 (sSup {r : ℝ | ∃ u : Fin d → ℝ, 1 < nnz u ∧
    r = (u ⬝ᵥ ((expMinusOne K - 1) *ᵥ u)) / ((∑ i, |u i|) ^ 2 - ∑ i, u i ^ 2)})

/-- The `(2 → 2)` operator norm `‖M‖_op` (p. 9). -/
noncomputable def opNorm {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖

/-- `Δ = √(log(d/δ)/d) + log(d/δ)/d` (Eq. (31)). -/
noncomputable def Delta (d : ℕ) (δ : ℝ) : ℝ :=
  Real.sqrt (Real.log (d / δ) / d) + Real.log (d / δ) / d

/-- `β̄ = max(1, β)` (Theorem 4; Lemma 13). -/
noncomputable def betaBar (β : ℝ) : ℝ := max 1 β

end HighMagSampling.SK


