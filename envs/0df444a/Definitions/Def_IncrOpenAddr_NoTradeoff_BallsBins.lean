-- Prove2me | Definitions.Def_IncrOpenAddr_NoTradeoff_BallsBins
-- name    : IncrOpenAddr_NoTradeoff_BallsBins
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:34:42.739824+00:00
-- url     : https://prove2.me/theorems/cd10a3b5-3062-4189-a375-e2ef73972e3c
-- title:
--   Balls thrown independently into bins, each by its own distribution: outcomes, probabilities, expectations, bin loads
-- statement:
--   A fixed number $N$ of balls is thrown into a finite set $\beta$ of bins. Ball $b$ lands in bin $x$ with probability $p_b(x)$ and in no bin with probability $p_b(\varnothing)$ (`IsBallLaw`: each $p_b$ is a probability distribution on $\beta\cup\{\varnothing\}$). The balls are independent: an outcome $\omega$ (where each ball landed) has probability $\prod_b p_b(\omega_b)$. For an event $E$ and a real random variable $F$,
--   $$\mathbb P(E)=\sum_{\omega\in E}\prod_b p_b(\omega_b),\qquad \mathbb E[F]=\sum_\omega\Big(\prod_b p_b(\omega_b)\Big)F(\omega),$$
--   and the **load** of bin $x$ is the number of balls that landed in $x$.
--
--   **Formalization Note.** Outcomes are `Fin N → Option β`; all sums are finite.
-- source:
--   Farach-Colton, Krapivin, Kuszmaul, Incremental Open Addressing Has No Time-Space Tradeoff, arXiv:2611.04186 (manuscript sha256 9486c2b8…), p. 11 (PDF 12), Lemma 2.5

import Mathlib

set_option autoImplicit false

/-!
# Balls thrown independently into bins

Farach-Colton, Krapivin, Kuszmaul, arXiv:2611.04186 (manuscript sha256 9486c2b8…), Lemma 2.5
(p. 11, PDF 12): "Throw a fixed number of balls into bins independently, each ball according to
its own distribution (a ball may land in no bin)."

`N` balls, a finite set `β` of bins; ball `b` lands in bin `o = some x` or in no bin
(`o = none`) with probability `p b o`.  An outcome is `ω : Fin N → Option β`, of probability
`∏_b p b (ω b)`.  Probabilities and expectations are finite sums over outcomes.
-/

namespace IncrOpenAddr.NoTradeoff

open scoped BigOperators

variable {β : Type} [Fintype β] [DecidableEq β] {N : ℕ}

/-- `p` gives every ball a probability distribution on `Option β`. -/
def IsBallLaw (p : Fin N → Option β → ℝ) : Prop :=
  ∀ b, (∀ o, 0 ≤ p b o) ∧ ∑ o, p b o = 1

/-- The probability of an outcome: the balls are independent. -/
def ballWeight (p : Fin N → Option β → ℝ) (ω : Fin N → Option β) : ℝ := ∏ b, p b (ω b)

/-- The probability of an event. -/
noncomputable def ballProb (p : Fin N → Option β → ℝ) (E : (Fin N → Option β) → Prop) : ℝ := by
  classical
  exact ∑ ω, if E ω then ballWeight p ω else 0

/-- The expectation of a real random variable. -/
def ballExp (p : Fin N → Option β → ℝ) (F : (Fin N → Option β) → ℝ) : ℝ :=
  ∑ ω, ballWeight p ω * F ω

/-- The load of each bin: the number of balls in it. -/
def binLoads (ω : Fin N → Option β) : β → ℕ :=
  fun x => (Finset.univ.filter fun b => ω b = some x).card

end IncrOpenAddr.NoTradeoff


