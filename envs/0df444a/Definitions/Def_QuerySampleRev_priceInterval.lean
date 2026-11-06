-- Prove2me | Definitions.Def_QuerySampleRev_priceInterval
-- name    : QuerySampleRev_priceInterval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:34:54.565789+00:00
-- url     : https://prove2.me/theorems/d133c3e5-a647-40b4-b537-995478bf18ee
-- title:
--   Parameters $K$, $w$, $\rho$, $a_i$, $m_i$, $b_i$ and price intervals $P^{(i)}$ of the hard instances
-- statement:
--   For an accuracy $\varepsilon>0$ and an exponent $c\in[0,1]$, the lower-bound construction of §5.5 uses
--   $$
--   K=\max\{2,\lfloor\varepsilon^{-c}/64\rfloor\},\qquad w=\frac1{8K},\qquad \rho=16K\varepsilon ,
--   $$
--   the number of hard distributions, the half-width of their price intervals, and the relative density change. For $i\in[K]=\{1,\dots,K\}$,
--   $$
--   a_i=\tfrac32-2iw,\qquad m_i=a_i+w,\qquad b_i=a_i+2w,\qquad P^{(i)}=(a_i,b_i] .
--   $$
--
--   **Formalization Note** All quantities are functions of $(\varepsilon,c)$ and of a natural index $i$; the theorems use them for $i\in\{1,\dots,K\}$.
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), §5.5, proof of Theorem 21, p.36 (PDF p.38)

import Mathlib

namespace QuerySampleRev

/-- **Number of hard distributions `K`.** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue
Maximization* (manuscript, sha256 c31ea3d3…), §5.5, proof of Theorem 21, p.36 (PDF 38):
"Set `K ≜ max{2, ⌊ε^{−c}/64⌋}`". Here `ε^{−c}` is the real power. -/
noncomputable def numHard (ε c : ℝ) : ℕ := max 2 ⌊ε ^ (-c) / 64⌋₊

/-- **Half-width `w ≜ 1/(8K)`** (same source, p.36). -/
noncomputable def halfWidth (ε c : ℝ) : ℝ := 1 / (8 * (numHard ε c : ℝ))

/-- **Relative density change `ρ ≜ 16Kε`** (same source, p.36). -/
noncomputable def rho (ε c : ℝ) : ℝ := 16 * (numHard ε c : ℝ) * ε

/-- **Left endpoint `a_i ≜ 3/2 − 2iw`** (same source, p.36), for the paper's index `i ∈ [K] = {1, …, K}`. -/
noncomputable def aPt (ε c : ℝ) (i : ℕ) : ℝ := 3 / 2 - 2 * (i : ℝ) * halfWidth ε c

/-- **Midpoint `m_i ≜ a_i + w`** (same source, p.36). -/
noncomputable def mPt (ε c : ℝ) (i : ℕ) : ℝ := aPt ε c i + halfWidth ε c

/-- **Right endpoint `b_i ≜ a_i + 2w`** (same source, p.36). -/
noncomputable def bPt (ε c : ℝ) (i : ℕ) : ℝ := aPt ε c i + 2 * halfWidth ε c

/-- **Price interval `P⁽ⁱ⁾ ≜ (a_i, b_i]`.** Same source, §5.5, p.36 (PDF 38): "For `i ∈ [K]`, denote by
`a_i ≜ 3/2 − 2iw`, `m_i ≜ a_i + w`, and `b_i ≜ a_i + 2w` the endpoints and the midpoint of the interval
`P⁽ⁱ⁾ ≜ (a_i, b_i]` on which the `i`-th hard distribution `F⁽ⁱ⁾` differs from `F⁽⁰⁾`."

**Formalization Note.** All parameters are functions of `(ε, c)`; indices are natural numbers and the
statements use them for `i ∈ Finset.Icc 1 K`, the paper's `[K]`. -/
noncomputable def priceInterval (ε c : ℝ) (i : ℕ) : Set ℝ := Set.Ioc (aPt ε c i) (bPt ε c i)

end QuerySampleRev


