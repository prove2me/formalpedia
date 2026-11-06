-- Prove2me | Definitions.Def_GradedReserve_winProb
-- name    : GradedReserve_winProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:31:16.655087+00:00
-- url     : https://prove2.me/theorems/f1b6077b-69c9-4c28-9bbf-39b11a5cfa05
-- title:
--   Winning probability $W(b)$ in $G_\pi$ with uniform ties
-- statement:
--   Against $n-1$ independent opponents who play the symmetric strategy $\sigma$, a bid $b\in[0,1]$ wins the item in $G_\pi$ with probability
--   $$W(b)=\pi(b)\sum_{j=0}^{n-1}\binom{n-1}{j}\frac{a^j\,c^{\,n-1-j}}{j+1},$$
--   where $a=\mu_\sigma(\{b\})$ is the probability that an opponent bids exactly $b$ and $c=\mu_\sigma((-\infty,b))$ the probability that an opponent's action is below $b$ (exit included). The term $j$ is the event that exactly $j$ opponents tie at $b$ and all others are below; the uniform tie-break then gives the bid probability $1/(j+1)$, and the item is sold with probability $\pi(b)$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Definition 2.3, p.4 (PDF 5)

import Mathlib
import Definitions.Def_GradedReserve_bidLaw
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The probability `W(b)` that a bid `b ∈ [0, 1]` wins in `G_π` against `n − 1` independent opponents
who play the symmetric strategy `σ` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Definition 2.3, p.4, PDF 5): the item is sold with
probability `π(b)` when `b` is the highest bid, and ties are broken uniformly at random. With
`a = P(opponent bids b)` and `c = P(opponent's action < b)` (exits included),
`W(b) = π(b) Σ_{j=0}^{n−1} C(n−1, j) a^j c^{n−1−j} / (j + 1)`. -/
noncomputable def winProb (f : ℝ → ℝ) (n : ℕ) (π : ℝ → ℝ) (σ : Kernel ℝ ℝ) (b : ℝ) : ℝ :=
  π b * ∑ j ∈ Finset.range n, ((n - 1).choose j : ℝ) * (bidLaw f σ {b}).toReal ^ j *
    (bidLaw f σ (Iio b)).toReal ^ (n - 1 - j) / ((j : ℝ) + 1)

end GradedReserve


