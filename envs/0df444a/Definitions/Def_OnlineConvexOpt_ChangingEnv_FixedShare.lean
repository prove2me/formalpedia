-- Prove2me | Definitions.Def_OnlineConvexOpt_ChangingEnv_FixedShare
-- name    : OnlineConvexOpt_ChangingEnv_FixedShare
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T17:31:23.268846+00:00
-- url     : https://prove2.me/theorems/0c63b23d-fe14-4699-bb1b-69cf868b9a1e
-- title:
--   Fixed Share algorithm run (Algorithm 30)
-- statement:
--   `IsFixedShareRun f α δ xi p phat x` formalizes the Fixed Share algorithm (Algorithm 30,
--   p. 174) over `N` experts with parameter `δ`, on `α`-exp-concave losses `f`, where `xi t i`
--   is expert `i`'s round-`t` suggested decision (external data): uniform initial weights
--   (`p 0 i = 1/N`); the play $x_t = \sum_i p^i_t x^i_t$; the exponential-weights update
--   `phat`; and the fixed-share mixing step $p^i_{t+1} = (1-\delta)\hat p^i_{t+1} + \delta/N$.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 174, Algorithm 30 (PDF p. 196)

import Mathlib

namespace OnlineConvexOpt.ChangingEnv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `IsFixedShareRun f α δ xi p phat x` formalizes the Fixed Share algorithm (Algorithm 30,
Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3, p. 174, PDF
p. 196) run over `N` experts (`N` the `Fintype.card` of the index type of `xi`) with parameter
`δ`, on `α`-exp-concave losses `f`, where `xi t i` is the round-`t` decision suggested by
expert `i` (external data, not defined by the algorithm): the initial weights are uniform
(`p 0 i = 1/N`, line 2, `p^1_i = 1/N`); the play is the weighted mixture `x t = ∑ p^i_t x^i_t`
(line 3); `phat (t+1)` is the exponential-weights update (line 5); and `p (t+1)` is the
fixed-share mixing step (line 6, `p^i_{t+1} = (1-δ)p̂^i_{t+1} + δ/N`). Indexed from round `0`
(the book's round `1`, shifted down by one, matching this chunk's other definitions). -/
def IsFixedShareRun {N : ℕ} (f : ℕ → E → ℝ) (α δ : ℝ)
    (xi : ℕ → Fin N → E) (p phat : ℕ → Fin N → ℝ) (x : ℕ → E) : Prop :=
  (∀ i : Fin N, p 0 i = 1 / (N : ℝ)) ∧
  (∀ t : ℕ, x t = ∑ i : Fin N, p t i • xi t i) ∧
  (∀ t : ℕ, ∀ i : Fin N,
    phat (t + 1) i =
      p t i * Real.exp (-α * f t (xi t i)) /
        ∑ j : Fin N, p t j * Real.exp (-α * f t (xi t j))) ∧
  (∀ t : ℕ, ∀ i : Fin N, p (t + 1) i = (1 - δ) * phat (t + 1) i + δ / N)

end OnlineConvexOpt.ChangingEnv


