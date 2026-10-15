-- Prove2me | Definitions.Def_SwitchbackExp_CLT_Setting
-- name    : SwitchbackExp_CLT_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:20.740546+00:00
-- url     : https://prove2.me/theorems/56d3518d-6d38-4051-90a5-3ec6df8a0c1f
-- title:
--   §4.2, p. 16; EC.3.1; EC.4.1 — the optimal design 𝕋*, block sums Ȳ_k, error terms 𝟙_t and 𝟙̄_k, Var(τ̂_m), Assumption 4, (10), Var^{U2} and σ̂²_U
-- statement:
--   This file sets up the $n$-replica experiment of §4.2: $T=nm$ periods and the optimal design of Theorem 2.
--
--   **The optimal design.** Its randomization points are
--   $$\mathbb T^*=\{1,\;2m+1,\;3m+1,\;\dots,\;(n-2)m+1\},$$
--   each with a fair coin, $q_k=\tfrac12$. The probability space of the experiment is the uniform distribution on the $2^{|\mathbb T^*|}$ coin vectors; its image under the path map is the design's law $\eta_{\mathbb T^*,1/2}$.
--
--   **Variance.** $\mathrm{Var}(\hat\tau_m)=\mathbb E[(\hat\tau_m-\mathbb E\hat\tau_m)^2]$ under a design $(\mathbb T,\mathbb Q)$.
--
--   **Block sums.** For $k\in\{0,1,\dots,n-2\}$,
--   $$\bar Y_k(\mathbf 1_{m+1})=\sum_{t=(k+1)m+1}^{(k+2)m}Y_t(\mathbf 1_{m+1}),\qquad \bar Y_k(\mathbf 0_{m+1})=\sum_{t=(k+1)m+1}^{(k+2)m}Y_t(\mathbf 0_{m+1}),\qquad \bar Y_k^{\mathrm{obs}}=\sum_{t=(k+1)m+1}^{(k+2)m}Y_t^{\mathrm{obs}}.$$
--
--   **Error terms.** With $f^m_{\mathbb T}(t)=\{f_{\mathbb T}(i):t-m\le i\le t\}=\{u_1,\dots,u_J\}$ the determining randomization points of the periods $t-m,\dots,t$ and $\bar q=1-q$, the error term (EC.2) for $t\in\{m+1,\dots,T\}$ is
--   $$\mathbb 1_t=Y_t(\mathbf 1_{m+1})\Big[\mathbb 1\{W_{t-m:t}=\mathbf 1_{m+1}\}\prod_{j=1}^{J}\frac1{q_{u_j}}-1\Big]-Y_t(\mathbf 0_{m+1})\Big[\mathbb 1\{W_{t-m:t}=\mathbf 0_{m+1}\}\prod_{j=1}^{J}\frac1{\bar q_{u_j}}-1\Big],$$
--   and the block error of EC.4.1 is $\bar{\mathbb 1}_k=\sum_{t=(k+1)m+1}^{(k+2)m}\mathbb 1_t$.
--
--   **Assumption 4** (Non-negligible variance, (11)). For a sequence of $n$-replica experiments with potential outcomes $Y^{(n)}$: $\mathrm{Var}(\hat\tau_m)\ge\Omega(n^{-1})$, that is, there is $c>0$ such that $\mathrm{Var}(\hat\tau_m)\ge c/n$ for all sufficiently large $n$.
--
--   **The variance formula (10), the bound $\mathrm{Var}^{U2}$ and the estimator $\hat\sigma^2_U$.** With $\bar Y_k(1)=\bar Y_k(\mathbf 1_{m+1})$ and $\bar Y_k(0)=\bar Y_k(\mathbf 0_{m+1})$,
--   $$\begin{aligned}V_{(10)}=\frac1{(T-m)^2}\Big\{&\bar Y_0(1)^2+\bar Y_0(0)^2+2\bar Y_0(1)\bar Y_0(0)+\sum_{k=1}^{n-3}\big[3\bar Y_k(1)^2+3\bar Y_k(0)^2+2\bar Y_k(1)\bar Y_k(0)\big]\\&+\bar Y_{n-2}(1)^2+\bar Y_{n-2}(0)^2+2\bar Y_{n-2}(1)\bar Y_{n-2}(0)+\sum_{k=0}^{n-3}2\big[\bar Y_k(1)+\bar Y_k(0)\big]\big[\bar Y_{k+1}(1)+\bar Y_{k+1}(0)\big]\Big\},\end{aligned}$$
--   $$\mathrm{Var}^{U2}=\frac1{(T-m)^2}\Big\{4\big[\bar Y_0(1)^2+\bar Y_0(0)^2\big]+\sum_{k=1}^{n-3}8\big[\bar Y_k(1)^2+\bar Y_k(0)^2\big]+4\big[\bar Y_{n-2}(1)^2+\bar Y_{n-2}(0)^2\big]\Big\},$$
--   $$\hat\sigma^2_U=\frac1{(T-m)^2}\Big\{8(\bar Y_0^{\mathrm{obs}})^2+\sum_{k=1}^{n-3}32(\bar Y_k^{\mathrm{obs}})^2\,\mathbb 1\{W_{km+1}=W_{(k+1)m+1}\}+8(\bar Y_{n-2}^{\mathrm{obs}})^2\Big\}.$$
--
--   These are the objects of Lemma 2, Corollary 1 and Theorem 3.
--
--   **Formalization Note** `optPoints m n` is $\{1\}\cup\{km+1:2\le k\le n-2\}$; it is the paper's $\mathbb T^*$ for $m\ge1$, $n\ge4$, and a degenerate set otherwise (only rows $n\ge4$ matter). The coin space `Coins m n` is the set of functions from $\mathbb T^*$ to `Bool` with the uniform probability measure. Assumption 4 is stated for a sequence `Y : ℕ → Outcomes` with row $n$ having $T=nm$ and potential outcomes `Y n`; $\Omega(n^{-1})$ is "eventually at least a positive constant times $1/n$". In (10), $\mathrm{Var}^{U2}$ and $\hat\sigma^2_U$, $T=nm$; the sums $\sum_{k=1}^{n-3}$ are over `Finset.Icc 1 (n - 3)` and $\sum_{k=0}^{n-3}$ over `Finset.range (n - 2)`.
-- source:
--   arXiv:2009.00148v4, §4.2, p. 16 (Ȳ_k, Ȳ_k^obs, (10), σ̂²_U), Assumption 4 (11), p. 17, Theorem 2 (𝕋*), p. 13; EC.3.1, (EC.2), p. ec3; EC.4.1, p. ec24; Var^{U2}, EC.4.3, p. ec26

import Mathlib
import Definitions.Def_SwitchbackExp_Design_Model

open SwitchbackExp.Design

namespace SwitchbackExp.CLT

open Finset MeasureTheory ProbabilityTheory

/-- The fair-coin probabilities `q₀ = q₁ = ⋯ = 1/2` of the optimal design (Theorem 2, p. 13). -/
noncomputable def half : ℕ → ℝ := fun _ => 1 / 2

/-- The randomization points `𝕋* = {1, 2m+1, 3m+1, …, (n−2)m+1}` of the optimal design (Theorem 2, p. 13). -/
def optPoints (m n : ℕ) : Finset ℕ := insert 1 ((Finset.Icc 2 (n - 2)).image (fun k => k * m + 1))

/-- `Var(τ̂_m)` under the design `(𝕋, ℚ)`: the variance of the Horvitz–Thompson estimator (4) under the
law (3). -/
noncomputable def htVar (m T : ℕ) (P : Finset ℕ) (q : ℕ → ℝ) (Y : Outcomes) : ℝ :=
  expect P q (fun w => (htEstimator m T P q Y w - expect P q (htEstimator m T P q Y)) ^ 2)

/-- `Ȳ_k(1_{m+1}) = ∑_{t=(k+1)m+1}^{(k+2)m} Y_t(1_{m+1})` (§4.2, p. 16). -/
def blockSum1 (m : ℕ) (Y : Outcomes) (k : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc ((k + 1) * m + 1) ((k + 2) * m), Y1 Y t

/-- `Ȳ_k(0_{m+1}) = ∑_{t=(k+1)m+1}^{(k+2)m} Y_t(0_{m+1})` (§4.2, p. 16). -/
def blockSum0 (m : ℕ) (Y : Outcomes) (k : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc ((k + 1) * m + 1) ((k + 2) * m), Y0 Y t

/-- `Ȳ_k^obs = ∑_{t=(k+1)m+1}^{(k+2)m} Y_t^obs`, the sum of the observed outcomes of block `k` on the
path `w` (§4.2, p. 16). -/
def blockObs (m : ℕ) (Y : Outcomes) (w : Path) (k : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc ((k + 1) * m + 1) ((k + 2) * m), Y t w

/-- `f^m_𝕋(t) = {f_𝕋(i) : i ∈ {t − m, …, t}}` (EC.3.1, p. ec3), the determining randomization points of
the periods `t − m, …, t`. -/
def detPoints (P : Finset ℕ) (m t : ℕ) : Finset ℕ := (Finset.Icc (t - m) t).image (detPoint P)

/-- The error term `𝟙_t(𝕋, ℚ, 𝕐)` of (EC.2), p. ec3, for `t ∈ {m+1 : T}`:
`Y_t(1_{m+1})[𝟙{w_{t−m:t} = 1_{m+1}} ∏_j 1/q_{u_j} − 1] − Y_t(0_{m+1})[𝟙{w_{t−m:t} = 0_{m+1}} ∏_j 1/q̄_{u_j} − 1]`,
the products over `u_j ∈ f^m_𝕋(t)`. -/
noncomputable def errTerm (m : ℕ) (P : Finset ℕ) (q : ℕ → ℝ) (Y : Outcomes) (t : ℕ) (w : Path) : ℝ :=
  Y1 Y t * (onesInd m w t * ∏ u ∈ detPoints P m t, 1 / q u - 1) - Y0 Y t * (zerosInd m w t * ∏ u ∈ detPoints P m t, 1 / (1 - q u) - 1)

/-- `𝟙̄_k = ∑_{t=(k+1)m+1}^{(k+2)m} 𝟙_t` (EC.4.1, p. ec24), the error of block `k`, `k = 0, …, n − 2`. -/
noncomputable def blockErr (m : ℕ) (P : Finset ℕ) (q : ℕ → ℝ) (Y : Outcomes) (k : ℕ) (w : Path) : ℝ :=
  ∑ t ∈ Finset.Icc ((k + 1) * m + 1) ((k + 2) * m), errTerm m P q Y t w

/-- The coin flips of the `n`-replica experiment under the optimal design: one fair coin at each point of
`𝕋* = optPoints m n`. -/
abbrev Coins (m n : ℕ) := ↥(optPoints m n) → Bool

/-- The uniform probability measure on the coin flips; its image under `pathOf (optPoints m n)` is the
law `η_{𝕋*, ½}` of (3). -/
noncomputable def coinMeasure (m n : ℕ) : Measure (Coins m n) :=
  (PMF.uniformOfFintype (Coins m n)).toMeasure

instance (m n : ℕ) : IsProbabilityMeasure (coinMeasure m n) := by
  unfold coinMeasure; infer_instance

/-- Assumption 4 (Non-negligible Variance, (11), p. 17) for the sequence of `n`-replica experiments
(`T = n m`, potential outcomes `Y n`, optimal design): `Var(τ̂_m) ≥ Ω(n⁻¹)`, i.e. there is a constant
`c > 0` with `Var(τ̂_m) ≥ c / n` for all sufficiently large `n`. -/
def NonNegligibleVariance (m : ℕ) (Y : ℕ → Outcomes) : Prop :=
  ∃ c > 0, ∀ᶠ n : ℕ in Filter.atTop, c / (n : ℝ) ≤ htVar m (n * m) (optPoints m n) half (Y n)

/-- The right-hand side of (10) (Lemma 2, p. 16), for `T = n m`. -/
noncomputable def lemma2Var (m n : ℕ) (Y : Outcomes) : ℝ :=
  1 / (((n * m : ℕ) : ℝ) - m) ^ 2 *
    (blockSum1 m Y 0 ^ 2 + blockSum0 m Y 0 ^ 2 + 2 * blockSum1 m Y 0 * blockSum0 m Y 0
      + ∑ k ∈ Finset.Icc 1 (n - 3),
          (3 * blockSum1 m Y k ^ 2 + 3 * blockSum0 m Y k ^ 2 + 2 * blockSum1 m Y k * blockSum0 m Y k)
      + blockSum1 m Y (n - 2) ^ 2 + blockSum0 m Y (n - 2) ^ 2
      + 2 * blockSum1 m Y (n - 2) * blockSum0 m Y (n - 2)
      + ∑ k ∈ Finset.range (n - 2),
          2 * (blockSum1 m Y k + blockSum0 m Y k) * (blockSum1 m Y (k + 1) + blockSum0 m Y (k + 1)))

/-- The variance upper bound `Var^{U2}(τ̂_m)` (EC.4.3, p. ec26), for `T = n m`; Corollary 1's `Var^U`. -/
noncomputable def varU (m n : ℕ) (Y : Outcomes) : ℝ :=
  1 / (((n * m : ℕ) : ℝ) - m) ^ 2 *
    (4 * (blockSum1 m Y 0 ^ 2 + blockSum0 m Y 0 ^ 2)
      + ∑ k ∈ Finset.Icc 1 (n - 3), 8 * (blockSum1 m Y k ^ 2 + blockSum0 m Y k ^ 2)
      + 4 * (blockSum1 m Y (n - 2) ^ 2 + blockSum0 m Y (n - 2) ^ 2))

/-- The variance estimator `σ̂²_U` of Corollary 1 (p. 16), for `T = n m`, on the observed path `w`. -/
noncomputable def sigmaU2 (m n : ℕ) (Y : Outcomes) (w : Path) : ℝ :=
  1 / (((n * m : ℕ) : ℝ) - m) ^ 2 *
    (8 * blockObs m Y w 0 ^ 2
      + ∑ k ∈ Finset.Icc 1 (n - 3),
          32 * blockObs m Y w k ^ 2 * (if w (k * m + 1) = w ((k + 1) * m + 1) then 1 else 0)
      + 8 * blockObs m Y w (n - 2) ^ 2)

end SwitchbackExp.CLT


