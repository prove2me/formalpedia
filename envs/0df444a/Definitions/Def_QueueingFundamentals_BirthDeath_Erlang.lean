-- Prove2me | Definitions.Def_QueueingFundamentals_BirthDeath_Erlang
-- name    : QueueingFundamentals_BirthDeath_Erlang
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T07:01:37.36732+00:00
-- url     : https://prove2.me/theorems/9e0719b4-9729-43cc-b349-3021ea6ff03f
-- title:
--   The Erlang-B formula B(c, r), the Erlang-C formula C(c, r), and the Halfin–Whitt function α(β)
-- statement:
--   Three explicit functions of Chapter 2.
--
--   1. The **Erlang-B** (Erlang loss) formula (2.53): for $c \in \{0,1,2,\dots\}$ servers and offered load $r$,
--   $$B(c, r) = \frac{r^c/c!}{\sum_{i=0}^{c} r^i/i!}.$$
--   2. The **Erlang-C** formula (2.38): with $\rho = r/c$,
--   $$C(c, r) = \frac{\dfrac{r^c}{c!(1-\rho)}}{\dfrac{r^c}{c!(1-\rho)} + \displaystyle\sum_{n=0}^{c-1} \frac{r^n}{n!}}.$$
--   The book defines $C(c, r)$ only for $\rho = r/c < 1$; it is the steady-state probability that an arriving customer of the $M/M/c$ queue has to wait.
--   3. The right-hand side of (2.44),
--   $$\alpha(\beta) = \frac{\phi(\beta)}{\phi(\beta) + \beta\,\Phi(\beta)},$$
--   where $\phi$ and $\Phi$ are the density and the distribution function of a standard normal random variable.
--
--   **Formalization Note** $C(c, r)$ is written as a total function of $c$ and $r$; its value for $r \ge c$ carries no meaning, and every theorem that uses it assumes $0 < r < c$. $\phi$ is Mathlib's `gaussianPDFReal 0 1` and $\Phi$ is the CDF of Mathlib's `gaussianReal 0 1`.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.69, Eq. (2.38); p.75, Eq. (2.44); p.82, Eq. (2.53)

import Mathlib

namespace QueueingFundamentals.BirthDeath

/-- The Erlang-B (Erlang loss) formula (2.53), p.82:
`B(c, r) = (r^c / c!) / ∑_{i=0}^{c} r^i / i!`. -/
noncomputable def erlangB (c : ℕ) (r : ℝ) : ℝ :=
  (r ^ c / (c.factorial : ℝ)) / ∑ i ∈ Finset.range (c + 1), r ^ i / (i.factorial : ℝ)

/-- The Erlang-C formula (2.38), p.69, with `ρ = r / c`:
`C(c, r) = (r^c / (c!(1 − ρ))) / (r^c / (c!(1 − ρ)) + ∑_{n=0}^{c-1} r^n / n!)`.
The book defines it for `r < c` (`ρ < 1`); outside that range the expression has no meaning,
and every statement using it assumes `0 < r < c`. -/
noncomputable def erlangC (c : ℕ) (r : ℝ) : ℝ :=
  (r ^ c / ((c.factorial : ℝ) * (1 - r / c))) /
    (r ^ c / ((c.factorial : ℝ) * (1 - r / c)) +
      ∑ n ∈ Finset.range c, r ^ n / (n.factorial : ℝ))

/-- The right-hand side of (2.44), p.75: `α(β) = φ(β) / (φ(β) + β Φ(β))`, where `φ` and `Φ` are
the PDF and the CDF of a standard normal random variable. -/
noncomputable def halfinWhittAlpha (β : ℝ) : ℝ :=
  ProbabilityTheory.gaussianPDFReal 0 1 β /
    (ProbabilityTheory.gaussianPDFReal 0 1 β +
      β * ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) β)

end QueueingFundamentals.BirthDeath


