-- Prove2me | Definitions.Def_NumStochOpt_LogConcave_polyDistF
-- name    : NumStochOpt_LogConcave_polyDistF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T19:41:01.681681+00:00
-- url     : https://prove2.me/theorems/782b342b-0b5e-49e4-812d-a07b2810ea29
-- title:
--   Prékopa's polynomial distribution function (5.19): $F(z) = 1/\sum_i c_i z_1^{\alpha_{i1}}\cdots z_n^{\alpha_{in}}$
-- statement:
--   This file fixes the formula of the **polynomial distribution** introduced by Prékopa to approximate the distribution of a random vector with values in the unit cube.
--
--   Let $N, n \ge 1$, let $c_1, \dots, c_N$ be real constants and let $\alpha_{ij}$ ($i = 1, \dots, N$, $j = 1, \dots, n$) be real exponents. For $z = (z_1, \dots, z_n)$ with $0 < z_j \le 1$,
--
--   $$
--   F(z_1, \dots, z_n) = \frac{1}{\sum_{i=1}^{N} c_i\, z_1^{\alpha_{i1}} \cdots z_n^{\alpha_{in}}} .
--   $$
--
--   In the book the constants satisfy $c_i > 0$, $\alpha_{ij} \le 0$ and $\alpha_{i1} + \dots + \alpha_{in} < 0$ for every $i$; these conditions are stated as hypotheses of the theorems about $F$, not built into the formula. Probabilistic constraints $F(z) \ge p$ with such an $F$ keep a geometric programme a geometric programme.
--
--   **Formalization Note** Points are `Fin n → ℝ` and the powers are real powers (`Real.rpow`). The book defines $F$ only on the cube $0 < z_j \le 1$ and leaves it "suitably defined otherwise"; the Lean formula is evaluated everywhere, but every theorem about it restricts to the cube (or its interior), so values outside are never used. The book prints the $i$-th term as $c_i z_i^{\alpha_{i1}} \cdots z_n^{\alpha_{in}}$; the first factor is $z_1^{\alpha_{i1}}$ (as in the proof of Theorem 5.7.1, p. 134), and that is the reading used. The book's domain condition reads "$0 < z_i \le 1$, $i = 1, \dots, N$"; the index there should run over the $n$ coordinates, and that is the reading used.
-- source:
--   A. Prékopa, "Numerical Solution of Probabilistic Constrained Programming Problems", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 5, §5.7, p. 133, Eq. (5.19)

import Mathlib

namespace NumStochOpt.LogConcave

/-- The formula (5.19) of the "polynomial distribution" (Prékopa, Ch. 5 of Ermoliev & Wets
(1988), p. 133):
`F(z₁, …, zₙ) = 1 / ∑_{i=1}^N cᵢ z₁^{α_{i1}} ⋯ zₙ^{α_{in}}`, with real exponents (`Real.rpow`).
The book uses the formula only on the cube `0 < zⱼ ≤ 1` and leaves `F` "suitably defined
otherwise"; every theorem about `polyDistF` restricts to that cube (or to its interior), so
the values the formula takes elsewhere are never used. The standing conditions of (5.19)
(`cᵢ > 0`, `α_{ij} ≤ 0`, `∑ⱼ α_{ij} < 0`) are hypotheses of those theorems. -/
noncomputable def polyDistF {N n : ℕ} (c : Fin N → ℝ) (α : Fin N → Fin n → ℝ)
    (z : Fin n → ℝ) : ℝ :=
  1 / ∑ i, c i * ∏ j, z j ^ α i j

end NumStochOpt.LogConcave


