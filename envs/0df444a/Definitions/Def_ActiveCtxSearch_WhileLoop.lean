-- Prove2me | Definitions.Def_ActiveCtxSearch_WhileLoop
-- name    : ActiveCtxSearch_WhileLoop
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:39:17.540653+00:00
-- url     : https://prove2.me/theorems/e72fe390-7a77-4288-8777-a8528be6b894
-- title:
--   Semantics of a `while` loop
-- statement:
--   For a condition on states and a partial step (a step may fail), the loop **while** cond **do** body started at a state $s$ applies the step as long as the condition holds. Its result is the first state at which the condition fails, or **no result** when the loop runs forever or a step fails.
--
--   This is the semantics of every `while` loop in Algorithms 2 and 3, so "the algorithm halts" means that each of its loops reaches a state where its condition fails.
--
--   **Formalization Note** The result is the iterate at the least number of passes after which the condition fails; it is `none` if no such number exists.
-- source:
--   Chen, Liu & Wang, Active Learning for Contextual Search with Binary Feedback, arXiv:2110.01072v2, Algorithm 2, p.11, lines 3, 5; Algorithm 3, p.13, line 7

import Mathlib

namespace ActiveCtxSearch

/-- `k` iterations of a partial step function `f` from the state `s` (`none` as soon as a step
fails). -/
def iterOpt {S : Type*} (f : S → Option S) : ℕ → S → Option S
  | 0, s => some s
  | k + 1, s => (iterOpt f k s).bind f

open Classical in
/-- The pseudocode loop `while cond do body`, started from the state `s`, used for the `while` loops
of Algorithms 2 and 3 of Chen, Liu & Wang, arXiv:2110.01072v2, pp.11 and 13.

The result is `some t` where `t` is the first state with `¬ cond t` reached by applying `body` while
`cond` holds, and `none` ("does not halt") if the loop runs forever or a `body` step fails.

**Formalization Note** The step function applies `body` only while `cond` holds, so the least
iteration count `k` at which the iterate exists and violates `cond` is the number of loop passes;
the loop returns the state at that `k`. -/
noncomputable def whileRun {S : Type*} (cond : S → Prop) (body : S → Option S) (s : S) :
    Option S :=
  let step : S → Option S := fun t => if cond t then body t else some t
  if h : ∃ k, ∃ t, iterOpt step k s = some t ∧ ¬ cond t then iterOpt step (Nat.find h) s else none

end ActiveCtxSearch


