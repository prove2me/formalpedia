-- Prove2me | Definitions.Def_Mdp_Basic
-- name    : Mdp_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:37:04.070807+00:00
-- url     : https://prove2.me/theorems/045d78ca-ba9e-4c60-9998-f55b6a94e03e
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/Basic.lean

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic
set_option autoImplicit true
namespace Mdp
structure DiscountedMDP (S A : Type*) [Fintype S] [Fintype A] [Nonempty A] where
  /-- Transition kernel: `K s a` is the distribution over next states after taking action `a`
      in state `s`. Corresponds to `K :: 's × 'a ⇒ 's pmf`, curried here. -/
  K : S → A → PMF S
  /-- Reward for taking action `a` in state `s`. Corresponds to `r :: 's × 'a ⇒ real`; no
      explicit boundedness hypothesis needed here since `S × A` is finite. -/
  r : S → A → ℝ
  /-- Discount factor. Corresponds to `l :: real`. -/
  l : ℝ
  l_nonneg : 0 ≤ l
  l_lt_one : l < 1
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
namespace DiscountedMDP
variable (M : DiscountedMDP S A)
noncomputable def expect (s : S) (a : A) (v : S → ℝ) : ℝ :=
  ∑ s', (M.K s a s').toReal * v s'
noncomputable def bellman (v : S → ℝ) (s : S) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a => M.r s a + M.l * M.expect s a v)
noncomputable def lNN (M : DiscountedMDP S A) : NNReal := ⟨M.l, M.l_nonneg⟩
end DiscountedMDP
end Mdp


