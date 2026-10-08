-- Prove2me | Definitions.Def_PowerTwoChoices_Asymptotics_ExpectedTime
-- name    : PowerTwoChoices_Asymptotics_ExpectedTime
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:04:19.483361+00:00
-- url     : https://prove2.me/theorems/642a114f-dcc8-490b-8738-4a15fd16def4
-- title:
--   The expected times $T_d(\lambda)$ and $T_1(\lambda)=1/(1-\lambda)$, and the ratio $F_d(\lambda)$ of Lemma 3
-- statement:
--   Fix an integer $d\ge 2$ (the number of queues each arriving customer samples in the supermarket model) and an arrival rate $\lambda$ with $0\le\lambda<1$. This file defines three explicit real functions of $\lambda$.
--
--   1. The equilibrium expected time a customer spends in the limiting supermarket system with $d$ choices (Corollary 2):
--   $$T_d(\lambda)=\sum_{i=1}^{\infty}\lambda^{\frac{d^i-d}{d-1}} .$$
--   The exponent $\frac{d^i-d}{d-1}=d+d^2+\dots+d^{i-1}$ is a natural number; the $i=1$ term is $\lambda^0=1$.
--   2. The expected time in an M/M/1 queue with arrival rate $\lambda$ and service rate $1$, i.e. the case of one choice:
--   $$T_1(\lambda)=\frac{1}{1-\lambda}.$$
--   3. The ratio of Lemma 3, whose numerator is the whole series:
--   $$F_d(\lambda)=\frac{\sum_{i=0}^{\infty}\lambda^{d^i}}{\log\frac{1}{1-\lambda}} .$$
--
--   Logarithms are natural. These functions are the objects of the heavy-traffic comparison between $d\ge2$ choices and one choice: every statement of the mission is about their behaviour as $\lambda\to1^-$.
--
--   **Formalization Note.** $\lambda$ is written `lam`. $T_d$ is a real series over $i\in\mathbb N$ whose $i=0$ term is $0$ and whose $i$-th term for $i\ge1$ is $\lambda^{\sum_{1\le k<i}d^k}$ (a natural-number power), so it is exactly $\sum_{i\ge1}\lambda^{(d^i-d)/(d-1)}$. $T_1$ is defined directly by $1/(1-\lambda)$, since the formula for $T_d$ has $d-1$ in a denominator. Both series converge for $0\le\lambda<1$; outside that range Lean returns junk values (a divergent series sums to $0$, $x/0=0$, $\log x=0$ for $x\le0$), but every statement of the mission only looks at $\lambda<1$ close to $1$. The same $T_d$ appears (computed in $[0,\infty]$) in the companion mission on the limiting system.
-- source:
--   Mitzenmacher, The Power of Two Choices in Randomized Load Balancing, IEEE Trans. Parallel Distrib. Syst. 12(10), 2001, p. 1099, Corollary 2 (T_d), §2.4 (T_1(λ) = 1/(1 − λ)), Lemma 3 (F_d); p. 1100, footnote 2 (natural logarithms)

import Mathlib

namespace PowerTwoChoices.Asymptotics

/-- `T_d(λ) = ∑_{i ≥ 1} λ^{(d^i - d)/(d - 1)}` (Mitzenmacher 2001, Corollary 2, p. 1099): the
equilibrium expected time a customer spends in the limiting supermarket system with `d ≥ 2`
choices. The exponent is written as the natural number
`(d^i - d)/(d - 1) = d + d² + ⋯ + d^{i-1} = ∑_{1 ≤ k < i} d^k`, so the `i = 1` term is `λ⁰ = 1`;
the `i = 0` index contributes `0`, so the sum starts at `i = 1` as printed.
The series is a real `tsum`; it converges for `0 ≤ λ < 1` (the only range used here), and Lean
returns `0` for a divergent series (e.g. at `λ = 1`). -/
noncomputable def Td (d : ℕ) (lam : ℝ) : ℝ :=
  ∑' i : ℕ, if 1 ≤ i then lam ^ (∑ k ∈ Finset.Ico 1 i, d ^ k) else 0

/-- `T_1(λ) = 1/(1 - λ)` (p. 1099, "from standard queueing theory"): the expected time in an
M/M/1 queue with arrival rate `λ < 1` and service rate `1`, i.e. the one-choice case. Defined
directly by the formula (the formula for `T_d` is meaningless at `d = 1`). Lean's `1/0 = 0`
makes `T1 1 = 0`; only `λ < 1` is used. -/
noncomputable def T1 (lam : ℝ) : ℝ :=
  1 / (1 - lam)

/-- `F_d(λ) = (∑_{i ≥ 0} λ^{d^i}) / log(1/(1 - λ))` (Lemma 3, p. 1099): the whole series is the
numerator. Natural logarithm (footnote 2, p. 1100). For `0 ≤ λ < 1` the series converges and
`log(1/(1-λ)) > 0` when `λ > 0`; Lean's junk values (`tsum` of a divergent series `= 0`,
`x / 0 = 0`, `Real.log` of a nonpositive number `= 0`) occur only outside this range. -/
noncomputable def Fd (d : ℕ) (lam : ℝ) : ℝ :=
  (∑' i : ℕ, lam ^ (d ^ i)) / Real.log (1 / (1 - lam))

end PowerTwoChoices.Asymptotics


