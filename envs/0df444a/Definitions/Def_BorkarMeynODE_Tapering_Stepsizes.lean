-- Prove2me | Definitions.Def_BorkarMeynODE_Tapering_Stepsizes
-- name    : BorkarMeynODE_Tapering_Stepsizes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:38:10.757131+00:00
-- url     : https://prove2.me/theorems/3c8d03ea-85ed-4844-aa33-840edc7c6826
-- title:
--   Step-size conditions (TS) tapering and (BS) bounded
-- statement:
--   Let $\{a(n)\}_{n\ge0}$ be a deterministic sequence of real step sizes.
--
--   1. **(TS) tapering step sizes:** $0<a(n)\le 1$ for all $n\ge0$, and
--   $$
--   \sum_n a(n) = \infty, \qquad \sum_n a(n)^2 < \infty .
--   $$
--   2. **(BS) bounded step sizes:** there are constants $1>\bar\alpha>\underline\alpha>0$ with $\underline\alpha\le a(n)\le\bar\alpha$ for all $n\ge0$.
--
--   Theorem 2.1 of the paper treats the two regimes separately: under (TS) the iterates are almost surely bounded, under (BS) their second moments are eventually bounded. Some lemmas of Section 4.1 hold under either condition.
--
--   **Formalization Note** For a sequence of positive terms, "not summable" is exactly $\sum_n a(n)=\infty$, and that is how the divergence is written. In (BS) both constants are existentially quantified.
-- source:
--   Borkar and Meyn, The O.D.E. Method for Convergence of Stochastic Approximation and Reinforcement Learning, SIAM J. Control Optim. 38(2) (2000), p. 449, conditions (TS) and (BS)

import Mathlib

namespace BorkarMeynODE.Tapering

/-- Tapering step sizes (TS), p. 449: `0 < a(n) ≤ 1` for all `n`, `∑ a(n) = ∞` and
`∑ a(n)² < ∞`. For a sequence of positive terms, `¬ Summable a` is exactly `∑ a(n) = ∞`. -/
def TaperingStepsize (a : ℕ → ℝ) : Prop :=
  (∀ n, 0 < a n ∧ a n ≤ 1) ∧ ¬ Summable a ∧ Summable (fun n => a n ^ 2)

/-- Bounded step sizes (BS), p. 449: for some constants `1 > ᾱ > α̲ > 0`,
`α̲ ≤ a(n) ≤ ᾱ` for all `n`. -/
def BoundedStepsize (a : ℕ → ℝ) : Prop :=
  ∃ αlo αhi : ℝ, 0 < αlo ∧ αlo < αhi ∧ αhi < 1 ∧ ∀ n, αlo ≤ a n ∧ a n ≤ αhi

end BorkarMeynODE.Tapering


