-- Prove2me | Definitions.Def_BewleyGE_Economy
-- name    : BewleyGE_Economy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:27:31.666586+00:00
-- url     : https://prove2.me/theorems/354dadac-522b-448e-95a3-6dca0720e3b1
-- title:
--   The exchange economy with random endowments, discounting and a savings cap
-- statement:
--   An **economy** with $n\ge 2$ goods consists of:
--
--   1. a finite nonempty set $\mathcal Y\subset\mathbb R^n$ of endowment vectors, each strictly positive ($y\gg 0$, i.e. $y_i>0$ for every $i$);
--   2. probabilities $e(y)>0$ for $y\in\mathcal Y$ with $\sum_{y\in\mathcal Y}e(y)=1$: in every period each agent independently receives the endowment vector $y$ with probability $e(y)$;
--   3. a discount factor $\beta$ with $\tfrac12<\beta<1$;
--   4. a constant $\bar b>0$, which scales the upper bound $\sum_i p_i\bar b/(1-r)^2$ on savings;
--   5. a utility function $U:\mathbb R^n_+\to\mathbb R$ over consumption bundles.
--
--   These are the primitives of the incomplete-market economy: a continuum of ex-ante identical agents trades the $n$ goods at prices $p$ and saves or borrows in a risk-free bond at interest rate $r$.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ` and $U$ is a total function whose values off $\mathbb R^n_+$ are never used. The page's product form $\mathcal Y=\mathcal Y_1\times\cdots\times\mathcal Y_n$ is not imposed: together with the page's strict top element it would force $\mathcal Y$ to be a single point when $n\ge2$. The endowment hypotheses used by the results are the separate predicates *Spread* and "$\mathcal Y$ is a singleton".
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, §2, pp.5–6

import Mathlib

namespace BewleyGE

/-- **The economy** of Light, *General equilibrium in a heterogeneous-agent incomplete-market
economy*, arXiv:1906.06810v2, §2, pp.5–6.

There are `n ≥ 2` goods. In each period every agent receives an endowment vector `y` from the
finite support `𝒴 ⊂ ℝⁿ` with probability `e y > 0`; every endowment vector is strictly positive
(`y ≫ 0`). Agents discount with `1/2 < β < 1`, the savings cap constant is `b̄ > 0`, and
preferences over bundles are a utility `U : ℝⁿ₊ → ℝ`.

**Formalization Note.** `ℝⁿ` is `Fin n → ℝ`. The support `𝒴` is a finite set of vectors; the
page's product form `𝒴 = 𝒴₁ × ⋯ × 𝒴ₙ` is not imposed (reading R1: with the page's strict top
element it would force `𝒴` to be a singleton when `n ≥ 2`); the endowment hypotheses used by the
results are the separate predicates `Spread` and `𝒴.card = 1`. `U` is a total function on `ℝⁿ`;
only its values on the orthant `ℝⁿ₊` are ever used. The probabilities `e y` are positive on `𝒴`
and sum to one; values of `e` off `𝒴` are irrelevant. -/
structure Economy (n : ℕ) where
  /-- The finite support `𝒴` of the endowment vector. -/
  Y : Finset (Fin n → ℝ)
  /-- The probability mass function `e` of the endowment vector. -/
  e : (Fin n → ℝ) → ℝ
  /-- The discount factor `β`. -/
  β : ℝ
  /-- The constant `b̄` of the savings cap `∑ pᵢ b̄ / (1 − r)²`. -/
  bbar : ℝ
  /-- The utility function `U` over bundles. -/
  U : (Fin n → ℝ) → ℝ
  /-- There are at least two goods. -/
  two_le_n : 2 ≤ n
  /-- `𝒴` is nonempty. -/
  Y_nonempty : Y.Nonempty
  /-- Every endowment vector is strictly positive, `y ≫ 0`. -/
  Y_pos : ∀ y ∈ Y, ∀ i, 0 < y i
  /-- Every endowment vector of `𝒴` has positive probability. -/
  e_pos : ∀ y ∈ Y, 0 < e y
  /-- `e` is a probability mass function on `𝒴`. -/
  e_sum : ∑ y ∈ Y, e y = 1
  /-- `1/2 < β`. -/
  β_gt : 1 / 2 < β
  /-- `β < 1`. -/
  β_lt : β < 1
  /-- `b̄ > 0`. -/
  bbar_pos : 0 < bbar

end BewleyGE


