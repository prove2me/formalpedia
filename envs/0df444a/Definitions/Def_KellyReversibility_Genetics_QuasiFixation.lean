-- Prove2me | Definitions.Def_KellyReversibility_Genetics_QuasiFixation
-- name    : KellyReversibility_Genetics_QuasiFixation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:50:29.139987+00:00
-- url     : https://prove2.me/theorems/f4dfbd31-85e7-4c70-9a96-05bde86744b2
-- title:
--   Eq. (7.8) — the allele-frequency random walk and its probability of quasi-fixation
-- statement:
--   In the infinite alleles model with population size $M\ge 2$, death rate $\mu$ and mutation probability $u$, the number $j\in\{0,1,\dots,M\}$ of individuals representing a given allele follows a random walk with transition intensities
--
--   $$q(j,j-1)=\mu\,\frac{j}{M}\Big(\frac{M-j}{M-1}+\frac{j-1}{M-1}\,u\Big),\qquad q(j,j+1)=\mu\,\frac{M-j}{M}\,\frac{j}{M-1}\,(1-u). \qquad (7.8)$$
--
--   An allele is **quasi-fixed** when it is the only allele present, i.e. when $j=M$. Let $h_n(j)$ be the probability that the walk started at $j$, stopped at $0$ and at $M$, reaches $M$ within its first $n$ jumps: $h_0(j)=1$ if $j=M$ and $0$ otherwise, and for $n\ge 0$
--   $$h_{n+1}(0)=0,\quad h_{n+1}(M)=1,\quad h_{n+1}(j)=\frac{q(j,j+1)}{q(j,j+1)+q(j,j-1)}h_n(j+1)+\frac{q(j,j-1)}{q(j,j+1)+q(j,j-1)}h_n(j-1)\ \ (0<j<M).$$
--   The probability that a new allele (represented by one individual) becomes quasi-fixed is
--   $$Q=\lim_{n\to\infty}h_n(1)=\sup_n h_n(1),$$
--   the probability that the walk started at $1$ reaches $M$ before $0$.
--
--   This is the quantity computed in Theorem 7.9.
--
--   **Formalization Note** The intensities are computed in $\mathbb R$ (no natural-number subtraction). The hitting probability is defined through the jump chain of the walk, which has the same absorption probabilities as the continuous-time walk; $h_n(j)$ is nondecreasing in $n$ and lies in $[0,1]$, so the real supremum `⨆ n, hitWithin μ u M n 1` is its limit. No positivity is built into the definitions; the theorem assumes $\mu>0$, $0<u<1$, $M\ge2$, under which both intensities are positive for $0<j<M$.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 153, Eq. (7.8); p. 156–157, §7.3 (quasi-fixation) and proof of Theorem 7.9

import Mathlib

namespace KellyReversibility.Genetics

/-- Kelly (1979), §7.2, p. 153, Eq. (7.8): the intensity `q(j, j − 1)` of the random walk
followed by the number `j` of representatives of an allele in a population of size `M`
(death rate `μ`, mutation probability `u`):
`q(j, j−1) = μ (j/M) ((M − j)/(M − 1) + ((j − 1)/(M − 1)) u)`.
All arithmetic is in `ℝ`. -/
noncomputable def downRate (μ u : ℝ) (M j : ℕ) : ℝ :=
  μ * ((j : ℝ) / M) * (((M : ℝ) - j) / ((M : ℝ) - 1) + (((j : ℝ) - 1) / ((M : ℝ) - 1)) * u)

/-- Kelly (1979), §7.2, p. 153, Eq. (7.8): the intensity
`q(j, j+1) = μ ((M − j)/M) (j/(M − 1)) (1 − u)`. All arithmetic is in `ℝ`. -/
noncomputable def upRate (μ u : ℝ) (M j : ℕ) : ℝ :=
  μ * (((M : ℝ) - j) / M) * ((j : ℝ) / ((M : ℝ) - 1)) * (1 - u)

/-- The probability that the random walk (7.8), started at `j` and absorbed at `0` and `M`,
reaches `M` within its first `n` jumps without having reached `0`. From a state `0 < j < M`
the walk jumps to `j + 1` with probability `q(j,j+1)/(q(j,j+1)+q(j,j−1))` and to `j − 1`
otherwise (its jump chain). -/
noncomputable def hitWithin (μ u : ℝ) (M : ℕ) : ℕ → ℕ → ℝ
  | 0, j => if j = M then 1 else 0
  | n + 1, j =>
    if j = 0 then 0
    else if j = M then 1
    else (upRate μ u M j / (upRate μ u M j + downRate μ u M j)) * hitWithin μ u M n (j + 1)
      + (downRate μ u M j / (upRate μ u M j + downRate μ u M j)) * hitWithin μ u M n (j - 1)

/-- Kelly (1979), §7.3, p. 157: the probability that a new allele (represented by one
individual) becomes *quasi-fixed*, i.e. that the walk (7.8) started at `1` reaches `M` before
it reaches `0`. It is the limit (= supremum, the sequence is nondecreasing and bounded by `1`)
of the probabilities `hitWithin μ u M n 1` of doing so within `n` jumps. -/
noncomputable def quasiFixProb (μ u : ℝ) (M : ℕ) : ℝ :=
  ⨆ n : ℕ, hitWithin μ u M n 1

end KellyReversibility.Genetics


