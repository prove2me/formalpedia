-- Prove2me | Definitions.Def_L22EigEst_bernW
-- name    : L22EigEst_bernW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:12:13.070279+00:00
-- url     : https://prove2.me/theorems/50cab1c5-b0e5-4d51-a53e-8f846e6ee252
-- title:
--   Independent Bernoulli coordinates — product weights, probabilities, expectations
-- statement:
--   Let $\iota$ be a finite index set and $p=(p_i)_{i\in\iota}$. For an outcome $\delta\in\{0,1\}^\iota$ of independent coordinates $\delta_i\sim\mathrm{Ber}(p_i)$, the **product weight** is
--
--   $$w_p(\delta)=\prod_{i\in\iota}\begin{cases}p_i&\delta_i=1\\1-p_i&\delta_i=0.\end{cases}$$
--
--   The probability of an event $E$ is $\Pr_p[E]=\sum_{\delta\in E}w_p(\delta)$ and the expectation of $f$ is $\mathbb E_p[f]=\sum_{\delta}w_p(\delta)f(\delta)$.
--
--   These finite sums are the laws of the row-sampling pattern $\delta_i\sim\mathrm{Ber}(p_i)$ of $S$ and of the coins $\xi_{ij}\sim\mathrm{Ber}(q)$, $i<j$, of Algorithm 1. An independent copy $S'$ is a second pattern $\delta'$ with the same weights.
--
--   **Formalization Note** The weights sum to $1$ whenever every $p_i\in[0,1]$; the statements using them assume or imply this.
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), §2, p.9 (δ_i ∼ Ber(p_i)); Algorithm 1 (Figure 1), p.11 (ξ_ij ∼ Ber(q))

import Mathlib

namespace L22EigEst

/-- **Product Bernoulli weight** of an outcome `δ : ι → Bool` when the coordinates are independent
with `δ_i ∼ Ber(p_i)`: `∏_i (p_i if δ_i else 1 − p_i)`.
Menand, Waingarten, STOC 2027 submission (manuscript sha256 b1f6adce…), §2, p.9 ("For each i ∈ [n]
sample δ_i ∼ Ber(p_i)") and Algorithm 1 (Figure 1), p.11 ("sampling ξ_ij ∼ Ber(q) for each i < j").

**Formalization Note.** The weights sum to `1` over all outcomes whenever every `p_i ∈ [0, 1]`;
the statements that use them assume this or imply it. -/
noncomputable def bernW {ι : Type*} [Fintype ι] (p : ι → ℝ) (δ : ι → Bool) : ℝ :=
  ∏ i, if δ i then p i else 1 - p i

/-- **Probability of an event** under independent Bernoulli coordinates: the sum of the product
weights `bernW p δ` over the outcomes `δ` in the event. -/
noncomputable def bernProb {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ)
    (E : (ι → Bool) → Prop) : ℝ := by
  classical
  exact ∑ δ ∈ Finset.univ.filter E, bernW p δ

/-- **Expectation** of `f` under independent Bernoulli coordinates: `∑_δ bernW p δ · f δ`. -/
noncomputable def bernExp {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ)
    (f : (ι → Bool) → ℝ) : ℝ :=
  ∑ δ, bernW p δ * f δ

end L22EigEst


