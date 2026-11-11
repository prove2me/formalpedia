-- Prove2me | Definitions.Def_LargeSupplyFPA_Asymptotic_Thresholds
-- name    : LargeSupplyFPA_Asymptotic_Thresholds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:02:41.602203+00:00
-- url     : https://prove2.me/theorems/0842a41c-d0e2-4f50-a0a8-8403dd287b4d
-- title:
--   High and low threshold bids ψ̄_*^(k), ψ̲_*^(k) ((14)–(15), p. 15)
-- statement:
--   Fix $\delta\in(0,0.5)$. In the $k$-th auction let $\mathbb E[T^{(k)}(b)]$ be the expected number of bids strictly above $b$. The **high threshold bid** and the **low threshold bid** are
--   $$\overline\psi_*^{(k)}=\min\{b\ge 0:\mathbb E[T^{(k)}(b)]\le k-k^{0.5+\delta}-1\},\qquad \underline\psi_*^{(k)}=\min\{b\ge0:\mathbb E[T^{(k)}(b)]\le k+k^{0.5+\delta}-1\}.$$
--   Since $\mathbb E[T^{(k)}(b)]$ is non-increasing and right-continuous in $b$ and tends to $0$, each set is a closed half-line once its right-hand side is positive, and $\underline\psi_*^{(k)}\le\overline\psi_*^{(k)}$ for all large $k$.
--
--   **Formalization Note** Each threshold is the `sInf` of its set. This is the minimum whenever the set is nonempty (for every large $k$) and $0$ for the finitely many $k$ where it is empty; the paper says both thresholds "exist for $k$ large enough". Powers are real powers `Real.rpow`.
-- source:
--   Hartline, Shah, vonAllmen, Robust Analysis of First-Price Auctions with Large Supply, STOC 2027 submission (manuscript of November 3, 2026, sha256 2ad8363b…), p. 15, Definition (14)–(15)

import Mathlib
import Definitions.Def_LargeSupplyFPA_Asymptotic_Model

open MeasureTheory ProbabilityTheory

namespace LargeSupplyFPA.Asymptotic

/-- The high threshold bid (14): `ψ̄_*^(k) = min {b ≥ 0 : E[T^(k)(b)] ≤ k - k^(0.5+δ) - 1}`.
The set is closed and bounded below, so this is its minimum whenever it is nonempty (for all
large `k`); for the finitely many `k` where it is empty the value is `0`. -/
noncomputable def highThreshold (δ : ℝ) {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ)
    (E : Fin n → Kernel ℝ ℝ) : ℝ :=
  sInf {b : ℝ | 0 ≤ b ∧ expNumAbove V E b ≤ (k : ℝ) - (k : ℝ) ^ ((0.5 : ℝ) + δ) - 1}

/-- The low threshold bid (15): `ψ̲_*^(k) = min {b ≥ 0 : E[T^(k)(b)] ≤ k + k^(0.5+δ) - 1}`
(value `0` when the set is empty, which happens only at `k = 0`). -/
noncomputable def lowThreshold (δ : ℝ) {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ)
    (E : Fin n → Kernel ℝ ℝ) : ℝ :=
  sInf {b : ℝ | 0 ≤ b ∧ expNumAbove V E b ≤ (k : ℝ) + (k : ℝ) ^ ((0.5 : ℝ) + δ) - 1}

end LargeSupplyFPA.Asymptotic


