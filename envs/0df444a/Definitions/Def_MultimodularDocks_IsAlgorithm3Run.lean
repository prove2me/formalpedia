-- Prove2me | Definitions.Def_MultimodularDocks_IsAlgorithm3Run
-- name    : MultimodularDocks_IsAlgorithm3Run
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:21.188428+00:00
-- url     : https://prove2.me/theorems/c2f2be62-fff3-4975-9b0a-2f377a742adb
-- title:
--   A run of Algorithm 3 (discrete gradient descent)
-- statement:
--   Algorithm 3 starts from the current allocation $(\bar{\vec d},\bar{\vec b})$, places the bikes optimally with Algorithm 1 to obtain $(\vec d^0,\vec b^0)$, and then applies gradient-descent steps (Algorithm 2), $(\vec d^r,\vec b^r)$ being the step from $(\vec d^{r-1},\vec b^{r-1})$; it returns as soon as a step does not move, and otherwise after $z$ iterations.
--
--   A **run** from $a_0$ is a sequence $x_0,x_1,x_2,\dots$ in which $x_0$ is the output of a complete run of Algorithm 1 from $a_0$ and $x_{r+1}$ is a gradient-descent step from $x_r$ for every $r$.
--
--   **Formalization Note** The run is the infinite sequence; once a step stays put the sequence is constant, so the output of Algorithm 3 with budget $z$ is $x_z$, and one run serves every budget.
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, Algorithm 3, p.36

import Mathlib
import Definitions.Def_MultimodularDocks_IsBikeGreedyRun
import Definitions.Def_MultimodularDocks_IsGDStep

namespace MultimodularDocks

/-- **A run of Algorithm 3** (Gradient-descent algorithm, Freund, Henderson, Shmoys,
arXiv:1611.09304v5, Algorithm 3, p.36) from the current allocation `a₀`: `x 0` is the output of
Algorithm 1 applied to `a₀` (line 1), and `x (r + 1)` is the output of Algorithm 2 applied to
`x r` for every `r` (line 3).

**Formalization Note** The page stops at the first `r` with `x r = x (r − 1)` (line 4) or after
`z` iterations; here the run is the whole sequence, which is constant once it stops (the second
branch of `IsGDStep`), and the output for budget `z` is `x z`. One run serves every `z`. -/
def IsAlgorithm3Run {S : Type*} [Fintype S] [DecidableEq S] (I : Instance S) (a₀ : Alloc S)
    (x : ℕ → Alloc S) : Prop :=
  IsBikeGreedyRun I a₀ (x 0) ∧ ∀ r : ℕ, IsGDStep I (x r) (x (r + 1))

end MultimodularDocks


