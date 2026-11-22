-- Prove2me | Definitions.Def_Csg_Discounted
-- name    : Csg_Discounted
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:42:26.490935+00:00
-- url     : https://prove2.me/theorems/1a023bea-f138-4433-a128-133b471e5d5e
-- title:
--   Discounted
-- statement:
--   Definitions and structural lemmas for Discounted, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Discounted.lean

import Definitions.Def_Csg_CsgMonotone
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic
set_option autoImplicit true
namespace Csg
structure DiscountedCSG (S A1 A2 : Type*) [Fintype S] [Fintype A1] [Fintype A2]
    [Nonempty A1] [Nonempty A2] [DecidableEq A1] [DecidableEq A2] extends CSG S A1 A2 where
  /-- Discount factor. Corresponds to `l` in `DiscountedMDP` (`Mdp/Basic.lean`). -/
  l : ℝ
  l_nonneg : 0 ≤ l
  l_lt_one : l < 1
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
namespace DiscountedCSG
variable (D : DiscountedCSG S A1 A2)
noncomputable def shapleyGame (s : S) (v : S → ℝ) : MatrixGame A1 A2 where
  A a1 a2 := D.toCSG.r s a1 a2 + D.l * D.toCSG.expect s a1 a2 v
noncomputable def shapley (v : S → ℝ) (s : S) : ℝ := (D.shapleyGame s v).value
noncomputable def lNN (D : DiscountedCSG S A1 A2) : NNReal := ⟨D.l, D.l_nonneg⟩
end DiscountedCSG
end Csg


