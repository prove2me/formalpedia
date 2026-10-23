-- Prove2me | Definitions.Def_HubSpokePricing_Lagrangian_Prob
-- name    : HubSpokePricing_Lagrangian_Prob
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:30:44.829676+00:00
-- url     : https://prove2.me/theorems/89961abc-b258-41dd-9eae-39a75d6ca9a4
-- title:
--   Definition B.1, p. 66 — discrete log-concave distributions on ℕ, means, and laws of sums of independent variables
-- statement:
--   A **probability mass function** on $\mathbb N=\{0,1,2,\dots\}$ is a sequence $p=(p_k)_{k\ge0}$ with $p_k\ge 0$ and $\sum_k p_k=1$.
--
--   **Discrete log-concavity** (Definition B.1, after Keilson and Gerber 1971, Keilson 1972). The mass function $p$ is *discrete log-concave* if
--
--   1. its support $I_p=\{k\ge 0: p_k>0\}$ is a set of consecutive integers: whenever $a\le k\le b$ and $a,b\in I_p$, also $k\in I_p$; and
--   2. $$p_k^2\;\ge\; p_{k-1}\,p_{k+1}\qquad\text{for all }k\ge 1.$$
--
--   **Mean.** The mean of $p$ is $\mu(p)=\sum_{k\ge0} k\,p_k$.
--
--   **Sums of independent variables.** The convolution of two mass functions is $(p*q)_k=\sum_{j=0}^{k}p_j\,q_{k-j}$, the law of $X+Y$ for independent $X\sim p$, $Y\sim q$. For mass functions $p^{(1)},\dots,p^{(n)}$, the law of $X_1+\dots+X_n$ with independent $X_i\sim p^{(i)}$ is the iterated convolution $p^{(1)}*\cdots*p^{(n)}$ (the point mass at $0$ when $n=0$).
--
--   These objects are used in Proposition B.9 and Lemmas A.12–A.14 of the paper, which bound the probability that the hub of the relaxed system is depleted.
--
--   **Formalization Note** A mass function is a function `ℕ → ℝ`; `IsLogConcave p` bundles nonnegativity, `HasSum p 1` and conditions 1–2. The mean `pmfMean` is a `tsum`; for a log-concave mass function the series converges (its tail is geometric), so the `tsum` is the true mean. Independence is encoded by the product form of the joint law, i.e. by the convolution `sumLaw`, so no measure theory is needed.
-- source:
--   Balseiro, Brown & Chen, Dynamic Pricing of Relocating Resources in Large Networks, SSRN 3313737 (version of May 23, 2020), https://ssrn.com/abstract=3313737, p. 66, Definition B.1; pp. 52–54, Lemmas A.12, A.14

import Mathlib

namespace HubSpokePricing.Lagrangian

open Finset

/-! # Discrete log-concave distributions and sums of independent ℕ-valued variables
(Balseiro, Brown & Chen, SSRN 3313737, May 23, 2020: Definition B.1, p. 66; Lemmas A.12–A.14,
pp. 52–54). A distribution on ℕ is a probability mass function `p : ℕ → ℝ`. -/

/-- Definition B.1: `p` is a probability mass function on ℕ that is discrete log-concave:
(i) its support is a set of consecutive integers, and (ii) `p_k² ≥ p_{k−1} p_{k+1}` for `k ≥ 1`. -/
def IsLogConcave (p : ℕ → ℝ) : Prop :=
  (∀ k, 0 ≤ p k) ∧ HasSum p 1 ∧
  (∀ a b k, a ≤ k → k ≤ b → 0 < p a → 0 < p b → 0 < p k) ∧
  ∀ k, 1 ≤ k → p (k - 1) * p (k + 1) ≤ p k ^ 2

/-- The mean `∑ₖ k p_k` of a probability mass function on ℕ. -/
noncomputable def pmfMean (p : ℕ → ℝ) : ℝ := ∑' k : ℕ, (k : ℝ) * p k

/-- Convolution of two mass functions on ℕ: the law of `X + Y` for independent `X ~ p`, `Y ~ q`. -/
def conv (p q : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ range (k + 1), p j * q (k - j)

/-- The law of `X₁ + ⋯ + Xₙ` for independent `Xᵢ ~ ps i`: the iterated convolution. -/
def sumLaw : (n : ℕ) → (Fin n → ℕ → ℝ) → ℕ → ℝ
  | 0, _ => fun k => if k = 0 then 1 else 0
  | n + 1, ps => conv (sumLaw n (fun i => ps i.castSucc)) (ps (Fin.last n))

end HubSpokePricing.Lagrangian


