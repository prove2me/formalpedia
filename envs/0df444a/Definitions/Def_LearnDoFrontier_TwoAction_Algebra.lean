-- Prove2me | Definitions.Def_LearnDoFrontier_TwoAction_Algebra
-- name    : LearnDoFrontier_TwoAction_Algebra
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:59.033992+00:00
-- url     : https://prove2.me/theorems/ef01acae-d30f-4ad0-93ef-a1bf42825632
-- title:
--   §4.3, Eqs. (16)–(20), Theorem 3, Theorem 6 (Complete) — linear recurrences, root expansions, the generalized Vandermonde matrix, the matrices Y and det Y formula
-- statement:
--   This file fixes the model-free linear algebra of the paper.
--
--   1. **Linear recurrence (16) and characteristic polynomial (17).** For $n \in \mathbb N$ and coefficients $q_1, \dots, q_n \in \mathbb C$, a sequence $x : \mathbb N \to \mathbb C$ solves (16) when
--   $$x(k+n) + q_1 x(k+n-1) + \cdots + q_n x(k) = 0 \qquad \text{for all } k \ge 0,$$
--   and its characteristic polynomial is $z^n + q_1 z^{n-1} + \cdots + q_n$.
--
--   2. **Root expansions.** For points $z_1, \dots, z_r \in \mathbb C$ with multiplicities $m_1, \dots, m_r$ and coefficients $a_{i,\tau}$ ($0 \le \tau < m_i$), the expansion of Eq. (18) is $\sum_i \sum_{\tau < m_i} a_{i,\tau} \binom{k}{\tau} z_i^{k-\tau}$ (with $\binom{k}{\tau} = 0$ for $k < \tau$), and that of Eq. (20) is $\sum_i \sum_{\tau < m_i} b_{i,\tau} k^\tau z_i^k$.
--
--   3. **Generalized Vandermonde matrix $W$ of (19).** The $n \times n$ matrix, $n = \sum_i m_i$, with rows $k = 0, \dots, n-1$ and columns ordered by the point $i$ first and $\tau = 0, \dots, m_i - 1$ second, whose $(k, (i,\tau))$ entry is $\binom{k}{\tau} z_i^{k-\tau}$.
--
--   4. **The matrix of Theorem 3.** Given a labelling $j \mapsto (z(j), \tau(j))$ of $N$ pairs, the $N \times N$ matrix $y_{kj} = k^{\tau(j)} z(j)^k$, $k, j = 0, \dots, N-1$ (with $0^0 = 1$).
--
--   5. **The matrix $Y = (Y^A, Y^B)$ of Theorem 6 (Complete).** For points $z^A_1, \dots, z^A_{d^A}$ with multiplicities $m^A_i$ and $z^B_1, \dots, z^B_{d^B}$ with multiplicities $m^B_j$, put $N = \sum_i m^A_i + \sum_j m^B_j$. $Y$ is $N \times N$ with rows $k = 0, \dots, N-1$. Its first columns are those of $Y^A$, indexed by $(i, \tau)$ with $i$ first and $\tau = 0, \dots, m^A_i - 1$ second, with entries $\binom{k}{\tau}(z^A_i)^{k-\tau}$. The remaining columns are those of $Y^B$, indexed by $(j, \tau)$ with $j$ first and $\tau = m^B_j - 1, \dots, 0$ second (descending), with entries $\binom{N-1-k}{\tau}(z^B_j)^{N-1-k-\tau}$. The matrix $\hat Y(t)$ is $Y$ with the first column of the block of $z^B_j$ (the column $\tau = m^B_j - 1$) replaced by $(t^{N-1-k})_k$.
--
--   6. **The determinant formula of Theorem 6 (Complete):**
--   $$\prod_{1\le i<l\le d^A}(z^A_l - z^A_i)^{m^A_i m^A_l}\cdot\prod_{i=1}^{d^A}\prod_{l=1}^{d^B}(1 - z^A_i z^B_l)^{m^A_i m^B_l}\cdot\prod_{1\le i<l\le d^B}(z^B_i - z^B_l)^{m^B_i m^B_l}.$$
--
--   These objects carry the statements about the boundary-value problems of the paper: the general solution of (16), the determinant of $W$, and the determinant of $Y$, for arbitrary points rather than roots, as the paper's induction uses them.
--
--   **Formalization Note** Points are enumerated by `Fin d`, coefficient pairs $(i,\tau)$ by the dependent pair type `Σ i, Fin (m i)`, and columns are relabelled into `Fin N` lexicographically (`finSigmaFinEquiv`, `finSumFinEquiv`), A-columns before B-columns, which is the paper's column order. A B-column $(j, t)$ with $t = 0, 1, \dots$ stands for $\tau = m^B_j - 1 - t$ (`Fin.rev`). Exponents use natural-number subtraction; whenever $k < \tau$ the binomial factor is $0$, so the truncated exponent never matters, matching the paper's convention $\binom{k}{\tau} = 0$ for $k < \tau$. The coefficient $q_{j+1}$ of (16) is `q j` for `j : Fin n`.
-- source:
--   Zhang, SSRN 3847049 (accepted version with E-Companion), pp. 20–22, §4.3, Eqs. (16)–(20), Theorem 3; EC pp. 11, 13, Theorem 6 (Complete) and its proof

import Mathlib

open Polynomial

namespace LearnDoFrontier.TwoAction

/-- Eq. (16), p. 20: `x` solves `x(k+n) + q₁ x(k+n-1) + ⋯ + qₙ x(k) = 0` for every `k ≥ 0`.
The coefficient `q j` (with `j : Fin n`) is the paper's `q_{j+1}`. -/
def recSol (n : ℕ) (q : Fin n → ℂ) (x : ℕ → ℂ) : Prop :=
  ∀ k : ℕ, x (k + n) + ∑ j : Fin n, q j * x (k + n - ((j : ℕ) + 1)) = 0

/-- Eq. (17), p. 20: the characteristic polynomial `zⁿ + q₁ zⁿ⁻¹ + ⋯ + qₙ` of (16). -/
noncomputable def charPoly (n : ℕ) (q : Fin n → ℂ) : ℂ[X] :=
  X ^ n + ∑ j : Fin n, C (q j) * X ^ (n - ((j : ℕ) + 1))

/-- The root expansion of Eq. (18), p. 21: `∑ᵢ ∑_{τ < mᵢ} a_{i,τ} (k choose τ) zᵢ^{k-τ}`.
For `k < τ` the binomial coefficient is `0`, which is the paper's convention; the truncated
exponent `k - τ` is then irrelevant. -/
noncomputable def rootExp {r : ℕ} (z : Fin r → ℂ) (m : Fin r → ℕ)
    (a : (Σ i : Fin r, Fin (m i)) → ℂ) (k : ℕ) : ℂ :=
  ∑ p : (Σ i : Fin r, Fin (m i)), a p * (k.choose (p.2 : ℕ) : ℂ) * z p.1 ^ (k - (p.2 : ℕ))

/-- The alternative root expansion of Eq. (20), p. 21: `∑ᵢ (∑_{τ < mᵢ} b_{i,τ} k^τ) zᵢ^k`. -/
noncomputable def exp3 {r : ℕ} (z : Fin r → ℂ) (m : Fin r → ℕ)
    (b : (Σ i : Fin r, Fin (m i)) → ℂ) (k : ℕ) : ℂ :=
  ∑ p : (Σ i : Fin r, Fin (m i)), b p * (k : ℂ) ^ (p.2 : ℕ) * z p.1 ^ k

/-- The generalized Vandermonde matrix `W` of Eq. (19), p. 21: rows `k = 0, …, n-1` with
`n = ∑ᵢ mᵢ`; columns ordered by the root `i` first and `τ = 0, …, mᵢ - 1` second
(lexicographically); entry `(k choose τ) zᵢ^{k-τ}`. -/
noncomputable def GVM {r : ℕ} (z : Fin r → ℂ) (m : Fin r → ℕ) :
    Matrix (Fin (∑ i, m i)) (Fin (∑ i, m i)) ℂ :=
  Matrix.of fun k c =>
    let p := (finSigmaFinEquiv (n := m)).symm c
    ((k : ℕ).choose (p.2 : ℕ) : ℂ) * z p.1 ^ ((k : ℕ) - (p.2 : ℕ))

/-- The matrix `Y` of Theorem 3, p. 22: given the labelling `j ↦ (z(j), τ(j))` of the
coefficient pairs, `y_{kj} = k^{τ(j)} z(j)^k` for `k, j = 0, …, N-1` (with `0⁰ = 1`). -/
noncomputable def Y3mat {N : ℕ} (zτ : Fin N → ℂ × ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun k j => ((k : ℕ) : ℂ) ^ (zτ j).2 * (zτ j).1 ^ (k : ℕ)

/-- The column order of the matrix `Y` of Theorem 6 (Complete), EC p. 11: the A-columns
`(i, τ)` (root `i` first, then `τ`), then the B-columns `(j, t)`, lexicographically. -/
def colEquiv {dA dB : ℕ} (mA : Fin dA → ℕ) (mB : Fin dB → ℕ) :
    ((Σ i : Fin dA, Fin (mA i)) ⊕ (Σ j : Fin dB, Fin (mB j))) ≃ Fin (∑ i, mA i + ∑ j, mB j) :=
  ((finSigmaFinEquiv (n := mA)).sumCongr (finSigmaFinEquiv (n := mB))).trans finSumFinEquiv

/-- The two blocks of the matrix `Y = (Y^A, Y^B)` of Theorem 6 (Complete), (1)–(3), EC p. 11,
before the columns are relabelled by `colEquiv`. Rows `k = 0, …, N-1` with
`N = ∑ m^A_i + ∑ m^B_j`.
* A-column `(i, τ)`: `(k choose τ) (z^A_i)^{k-τ}`.
* B-column `(j, t)`, standing for `τ = m^B_j - 1 - t` (so `τ` runs `m^B_j - 1, …, 0` as `t`
  increases): `(N-1-k choose τ) (z^B_j)^{N-1-k-τ}`. -/
noncomputable def YBlocks {dA dB : ℕ} (zA : Fin dA → ℂ) (mA : Fin dA → ℕ)
    (zB : Fin dB → ℂ) (mB : Fin dB → ℕ) :
    Matrix (Fin (∑ i, mA i + ∑ j, mB j)) ((Σ i : Fin dA, Fin (mA i)) ⊕ (Σ j : Fin dB, Fin (mB j))) ℂ :=
  Matrix.of fun k c =>
    match c with
    | Sum.inl p => ((k : ℕ).choose (p.2 : ℕ) : ℂ) * zA p.1 ^ ((k : ℕ) - (p.2 : ℕ))
    | Sum.inr p =>
        let N := ∑ i, mA i + ∑ j, mB j
        let τ : ℕ := (Fin.rev p.2 : ℕ)
        ((N - 1 - (k : ℕ)).choose τ : ℂ) * zB p.1 ^ (N - 1 - (k : ℕ) - τ)

/-- The square matrix `Y = (Y^A, Y^B)` of Theorem 6 (Complete), EC p. 11, with its columns in
the paper's order (`colEquiv`). It is defined for arbitrary points and multiplicities, because
the proof (EC p. 13) applies it to a "nominal root" that is not a root. -/
noncomputable def Ymat {dA dB : ℕ} (zA : Fin dA → ℂ) (mA : Fin dA → ℕ)
    (zB : Fin dB → ℂ) (mB : Fin dB → ℕ) :
    Matrix (Fin (∑ i, mA i + ∑ j, mB j)) (Fin (∑ i, mA i + ∑ j, mB j)) ℂ :=
  Matrix.of fun k c => YBlocks zA mA zB mB k ((colEquiv mA mB).symm c)

/-- The determinant formula of Theorem 6 (Complete), EC p. 11:
`∏_{i<l} (z^A_l - z^A_i)^{m^A_i m^A_l} · ∏_{i,l} (1 - z^A_i z^B_l)^{m^A_i m^B_l} ·
∏_{i<l} (z^B_i - z^B_l)^{m^B_i m^B_l}`. -/
noncomputable def detFormula {dA dB : ℕ} (zA : Fin dA → ℂ) (mA : Fin dA → ℕ)
    (zB : Fin dB → ℂ) (mB : Fin dB → ℕ) : ℂ :=
  (∏ i : Fin dA, ∏ l ∈ Finset.Ioi i, (zA l - zA i) ^ (mA i * mA l)) *
  (∏ i : Fin dA, ∏ l : Fin dB, (1 - zA i * zB l) ^ (mA i * mB l)) *
  (∏ i : Fin dB, ∏ l ∈ Finset.Ioi i, (zB i - zB l) ^ (mB i * mB l))

/-- The column of `Y` that the inductive step of the proof of Theorem 6 (Complete), EC p. 13,
replaces: the first column of the B-block of root `j`, i.e. `τ = m^B_j - 1`. -/
def firstBCol {dA dB : ℕ} (mA : Fin dA → ℕ) (mB : Fin dB → ℕ) (j : Fin dB) (h : 0 < mB j) :
    Fin (∑ i, mA i + ∑ j, mB j) :=
  colEquiv mA mB (Sum.inr ⟨j, ⟨0, h⟩⟩)

/-- The matrix `Ŷ(t)` of the inductive step, EC p. 13: `Y` with the first column of the
B-block of root `j` replaced by `(t^{N-1-k})_k`. -/
noncomputable def Yhat {dA dB : ℕ} (zA : Fin dA → ℂ) (mA : Fin dA → ℕ)
    (zB : Fin dB → ℂ) (mB : Fin dB → ℕ) (j : Fin dB) (h : 0 < mB j) (t : ℂ) :
    Matrix (Fin (∑ i, mA i + ∑ j, mB j)) (Fin (∑ i, mA i + ∑ j, mB j)) ℂ :=
  (Ymat zA mA zB mB).updateCol (firstBCol mA mB j h)
    (fun k => t ^ (∑ i, mA i + ∑ j, mB j - 1 - (k : ℕ)))

end LearnDoFrontier.TwoAction


