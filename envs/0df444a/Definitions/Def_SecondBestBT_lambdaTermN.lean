-- Prove2me | Definitions.Def_SecondBestBT_lambdaTermN
-- name    : SecondBestBT_lambdaTermN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:06.972347+00:00
-- url     : https://prove2.me/theorems/01fbaec5-3262-4ee5-93b4-72e6edc599a8
-- title:
--   Summand of $\Lambda_D(x)$ on $\mathbb Z_{\ge0}^2$
-- statement:
--   For priors $f_S,f_B$ on $\mathbb Z_{\ge0}$ and an allocation $x$, the summand of the budget-balance discriminant at $(s,b)$ is
--   $$
--   x(s,b)\Big[f_S(s)f_B(b)(b-s)-f_S(s)\big(1-F_B(b)\big)-f_B(b)F_S(s-1)\Big],
--   $$
--   with $F_B(b)=\sum_{k\le b}f_B(k)$ and $F_S(s-1)=\sum_{k<s}f_S(k)$; $\Lambda_D(x)$ is the sum of these terms over $(s,b)\in\mathbb Z_{\ge0}^2$.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 4.1, p.8; display on p.13

import Mathlib

namespace SecondBestBT

/-- The summand of the budget-balance discriminant `Λ_D(x)` on `Z²_{≥0}` in its expanded,
denominator-free form (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256 17184930…,
Section 4.1, p.8, and the display on p.13):
`x(s, b) [f_S(s) f_B(b)(b − s) − f_S(s)(1 − F_B(b)) − f_B(b) F_S(s − 1)]` at `p = (s, b)`.

**Formalization Note** `1 − F_B(b) = 1 − ∑_{k ≤ b} f_B(k)` (the paper's `∑_{b'>b} f_B(b')` for a
probability vector) and `F_S(s − 1) = ∑_{k < s} f_S(k)`. `Λ_D(x)` is the series
`∑' p, lambdaTermN f_S f_B x p`; theorems state its summability. -/
def lambdaTermN (fS fB : ℕ → ℝ) (x : ℕ → ℕ → ℝ) (p : ℕ × ℕ) : ℝ :=
  x p.1 p.2 * (fS p.1 * fB p.2 * ((p.2 : ℝ) - p.1) -
    fS p.1 * (1 - ∑ k ∈ Finset.range (p.2 + 1), fB k) - fB p.2 * ∑ k ∈ Finset.range p.1, fS k)

end SecondBestBT


