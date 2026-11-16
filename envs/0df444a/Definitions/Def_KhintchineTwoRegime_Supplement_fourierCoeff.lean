-- Prove2me | Definitions.Def_KhintchineTwoRegime_Supplement_fourierCoeff
-- name    : KhintchineTwoRegime_Supplement_fourierCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:24:16.397469+00:00
-- url     : https://prove2.me/theorems/c8506045-761e-47c0-a97a-1c50ffe2e2ca
-- title:
--   Fourier coefficient $\hat h(S)=\langle h,x_S\rangle$ on the Hamming cube
-- statement:
--   Equip the Hamming cube $\{-1,1\}^n$ with the uniform probability measure $\mu_n(x)=2^{-n}$. For $h:\{-1,1\}^n\to\mathbb R$ and $S\subseteq[n]$, write $x_S=\prod_{i\in S}x_i$. The **Fourier coefficient** of $h$ at $S$ is
--   $$
--   \hat h(S)=\langle h,x_S\rangle=2^{-n}\sum_{x\in\{-1,1\}^n}h(x)\prod_{i\in S}x_i .
--   $$
--   The characters $\{x_S\}_{S\subseteq[n]}$ form an orthonormal basis, so $h=\sum_S\hat h(S)x_S$. In particular $\hat h(\emptyset)$ is the mean of $h$.
--
--   **Formalization Note** A point $x\in\{-1,1\}^n$ is encoded as `x : Fin n → Bool` with true read as $+1$ and false as $-1$, the encoding of the published $K_n$ (`KhintchineTwoRegime.K`); subsets of $[n]$ are `Finset (Fin n)` (0-based).
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §4, p.10

import Mathlib

namespace KhintchineTwoRegime.Supplement

/-- The Fourier coefficient `ĥ(S) = ⟨h, x_S⟩ = 2⁻ⁿ ∑_{x ∈ {−1,1}ⁿ} h(x) ∏_{i ∈ S} xᵢ` of a
function `h : {−1,1}ⁿ → ℝ` on the Hamming cube with the uniform probability measure
`µₙ(x) = 2⁻ⁿ` (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §4, p.10).

**Formalization Note** A point `x ∈ {−1,1}ⁿ` is encoded as `x : Fin n → Bool` with
`true ↦ +1`, `false ↦ −1`, the encoding of `KhintchineTwoRegime.K`; `S` is a subset of the
0-based index set `Fin n` (the paper's `[n]`). The expectation is the `2⁻ⁿ`-weighted finite
sum. `ĥ(∅)` is the mean of `h`. -/
noncomputable def fourierCoeff {n : ℕ} (h : (Fin n → Bool) → ℝ) (S : Finset (Fin n)) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ x : Fin n → Bool, h x * ∏ i ∈ S, (if x i then (1 : ℝ) else -1)

end KhintchineTwoRegime.Supplement


