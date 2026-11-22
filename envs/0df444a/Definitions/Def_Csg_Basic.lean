-- Prove2me | Definitions.Def_Csg_Basic
-- name    : Csg_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:40:13.882654+00:00
-- url     : https://prove2.me/theorems/94ebf2fa-cbe2-41c7-8dd5-e98ed0514783
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Basic.lean

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Definitions.Def_Csg_MatrixGame
set_option autoImplicit true
namespace Csg
structure CSG (S A1 A2 : Type*) [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
    [DecidableEq A1] [DecidableEq A2] where
  /-- Transition kernel: `K s a1 a2` is the distribution over next states after the row player
      plays `a1` and the column player plays `a2` simultaneously in state `s`. -/
  K : S → A1 → A2 → PMF S
  /-- Reward for the joint action `(a1, a2)` in state `s`, paid by the row player to the column
      player -- matching `MatrixGame`'s own row-minimizes/column-maximizes convention. -/
  r : S → A1 → A2 → ℝ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
namespace CSG
variable (C : CSG S A1 A2)
noncomputable def expect (s : S) (a1 : A1) (a2 : A2) (v : S → ℝ) : ℝ :=
  ∑ s', (C.K s a1 a2 s').toReal * v s'
noncomputable def stageGame (s : S) (v : S → ℝ) : MatrixGame A1 A2 where
  A a1 a2 := C.r s a1 a2 + C.expect s a1 a2 v
noncomputable def stageValue (s : S) (v : S → ℝ) : ℝ := (C.stageGame s v).value
end CSG
end Csg


