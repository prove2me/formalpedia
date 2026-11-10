-- Prove2me | Definitions.Def_RadioInitBits_exactLoadProb
-- name    : RadioInitBits_exactLoadProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:10:09.258962+00:00
-- url     : https://prove2.me/theorems/53bd09af-8b18-4158-902b-7a7ada0e1f67
-- title:
--   Load vectors of balls in bins, exact and Poisson probabilities
-- statement:
--   Throw $m$ balls independently and uniformly at random into $N$ bins. The **load vector** $(L_1,\dots,L_N)$ records the number of balls in each bin. For a set $A\subseteq\mathbb N^N$ of load vectors:
--
--   1. the **exact probability** of $A$ is
--   $$\Pr_{\text{exact}}[L\in A]=\frac{\#\{x\in[N]^m : \mathrm{load}(x)\in A\}}{N^m},$$
--   where $x_b$ is the bin of ball $b$;
--   2. the **Poisson probability** of $A$ treats the loads as independent Poisson random variables with mean $\lambda=m/N$:
--   $$\Pr_{\text{Poisson}}[A]=\sum_{a\in A}\ \prod_{j=1}^{N}\frac{e^{-\lambda}\lambda^{a_j}}{a_j!}.$$
--
--   These are the two sides of the Poisson approximation (Theorem 11). The paper uses it to analyse how many bins of a phase are occupied by exactly one node.
--
--   **Formalization Note** Both probabilities take values in $[0,\infty]$ (`ℝ≥0∞`). The exact side is a ratio of counts, and the Poisson side is a sum of nonnegative terms over a countable set, so no measurability question arises. When $N=0$, $\lambda$ is $0$.
-- source:
--   Banasik, Dani, Hayes, Initialization with Exponentially Fewer Bits, STOC 2027 submission (manuscript, sha256 859ca50d…), full version Theorem 11, p.6 (PDF p.27)

import Mathlib

set_option autoImplicit false

namespace RadioInitBits

open scoped ENNReal

/-- The **load vector** of a throw of `m` balls into `N` bins: `x b` is the bin of ball `b`, and
`load x j` is the number of balls in bin `j`. -/
def load {m N : ℕ} (x : Fin m → Fin N) (j : Fin N) : ℕ :=
  (Finset.univ.filter fun b => x b = j).card

/-- The **exact** probability that the load vector lies in `A` when `m` balls are thrown
independently and uniformly at random into `N` bins: the number of throws `x : Fin m → Fin N`
with `load x ∈ A`, divided by the number `N ^ m` of all throws.
D. Banasik, V. Dani, T. P. Hayes, *Initialization with Exponentially Fewer Bits*, STOC 2027
submission (held version, sha256 859ca50d…), full version Theorem 11, p.6 (PDF p.27) ("the true
probability").

**Formalization Note** Independent uniform throws make every `x : Fin m → Fin N` equally likely,
so the probability is a ratio of counts (in `ℝ≥0∞`; no measurability question arises). -/
noncomputable def exactLoadProb (m N : ℕ) (A : Set (Fin N → ℕ)) : ℝ≥0∞ := by
  classical
  exact ((Finset.univ.filter fun x : Fin m → Fin N => load x ∈ A).card : ℝ≥0∞) /
    (N : ℝ≥0∞) ^ m

/-- The probability of `A` under the **Poisson approximation** of the load vector of `m` balls in
`N` bins: the loads of the `N` bins are independent Poisson random variables with mean `m / N`,
so the probability is `∑_{a ∈ A} ∏_j e^{−m/N} (m/N)^{a_j} / a_j!`.
Banasik, Dani, Hayes, full version Theorem 11, p.6 (PDF p.27): "the joint distribution of the
number of balls in all the bins is approximated by assuming the load at each bin is an
independent Poisson random variable with mean m/n".

**Formalization Note** The Poisson probabilities are written out, with `λ = m / N` (a real
number; `λ = 0` when `N = 0`, a case with no bins). The sum over the countable set `A ⊆ ℕ^N` is
an `ℝ≥0∞`-valued `tsum` of nonnegative terms. -/
noncomputable def poissonLoadProb (m N : ℕ) (A : Set (Fin N → ℕ)) : ℝ≥0∞ :=
  ∑' a : Fin N → ℕ,
    A.indicator (fun a => ∏ j, ENNReal.ofReal
      (Real.exp (-((m : ℝ) / N)) * ((m : ℝ) / N) ^ (a j) / ((a j).factorial : ℝ))) a

end RadioInitBits


