-- Prove2me | Definitions.Def_CongestionTaxes_gRatio
-- name    : CongestionTaxes_gRatio
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:31:49.384321+00:00
-- url     : https://prove2.me/theorems/abbcfb44-6abc-4de9-8aaf-8278daf0cda8
-- title:
--   The ratio $g(x,v)$ of Lemma 5
-- statement:
--   For $c:\mathbb N_0\to\mathbb R$, $x\in\mathbb N$ and $v>0$, let
--
--   $$
--   g(x,v)=\frac{\sum_{i=1}^{x}\frac{x\,c(i)-i\,c(i-1)}{i!}v^i}{\sum_{i=0}^{x}\frac{x-i}{i!}v^i}.
--   $$
--
--   With $c(x)=x\ell(x)$ it is the right-hand side of (16), the bound that $p(v)$ must dominate for the modified costs of Definition 4 to be non-decreasing.
--
--   **Formalization Note** The denominator is positive for $x\ge1$, $v>0$; no statement uses other arguments.
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, Lemma 5, p.30; display (16), p.29

import Mathlib

namespace CongestionTaxes

/-- The ratio `g(x, v)` of Lemma 5 and display (16) (Paccagnan, Gairing, arXiv:2105.07480v2,
Lemma 5, p.30, and (16), p.29): for `c : ℕ₀ → ℝ`,
`g(x, v) = (∑_{i=1}^x ((x c(i) − i c(i−1)) / i!) vⁱ) / (∑_{i=0}^x ((x − i) / i!) vⁱ)`.

**Formalization Note** The denominator is positive for `x ≥ 1`, `v > 0` (its `i = 0` term is `x`),
the only arguments any statement uses. `c (i - 1)` is evaluated for `i ≥ 1` only; `x − i` is real
subtraction. -/
noncomputable def gRatio (c : ℕ → ℝ) (x : ℕ) (v : ℝ) : ℝ :=
  (∑ i ∈ Finset.Icc 1 x, ((x : ℝ) * c i - (i : ℝ) * c (i - 1)) / (i.factorial : ℝ) * v ^ i) /
    (∑ i ∈ Finset.range (x + 1), ((x : ℝ) - (i : ℝ)) / (i.factorial : ℝ) * v ^ i)

end CongestionTaxes


