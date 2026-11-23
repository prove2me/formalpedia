-- Prove2me | Definitions.Def_Mdp_RecyclingRobot
-- name    : Mdp_RecyclingRobot
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T01:40:08.162027+00:00
-- url     : https://prove2.me/theorems/833d0017-15fe-40a7-8a8c-7e3fc2751fd9
-- title:
--   Recycling Robot
-- statement:
--   Definitions and structural lemmas for Recycling Robot, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/RecyclingRobot.lean

import Definitions.Def_Mdp_PolicyIteration
set_option autoImplicit true
open Mdp Mdp.DiscountedMDP
inductive RobotState
  | high
  | low
  deriving DecidableEq, Inhabited
instance : Fintype RobotState where
  elems := {RobotState.high, RobotState.low}
  complete := by intro x; cases x <;> decide
inductive RobotAction
  | search
  | wait
  | recharge
  deriving DecidableEq, Inhabited
instance : Fintype RobotAction where
  elems := {RobotAction.search, RobotAction.wait, RobotAction.recharge}
  complete := by intro x; cases x <;> decide
theorem robotState_sum {β : Type*} [AddCommMonoid β] (f : RobotState → β) :
    ∑ s : RobotState, f s = f RobotState.high + f RobotState.low := by
  have huniv : (Finset.univ : Finset RobotState) = {RobotState.high, RobotState.low} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]
noncomputable def searchPMF : PMF RobotState :=
  PMF.ofFintype (fun _ => ENNReal.ofReal (1 / 2)) (by
    rw [robotState_sum, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num [ENNReal.ofReal_one])
noncomputable def robotK : RobotState → RobotAction → PMF RobotState
  | .high, .search => searchPMF
  | .high, .wait => PMF.pure .high
  | .high, .recharge => PMF.pure .high
  | .low, .search => searchPMF
  | .low, .wait => PMF.pure .low
  | .low, .recharge => PMF.pure .high
noncomputable def robotR : RobotState → RobotAction → ℝ
  | .high, .search => 2
  | .high, .wait => 1
  | .high, .recharge => 1
  | .low, .search => -(1 / 2)
  | .low, .wait => 1
  | .low, .recharge => 0
noncomputable def robotMDP : DiscountedMDP RobotState RobotAction where
  K := robotK
  r := robotR
  l := 1 / 2
  l_nonneg := by norm_num
  l_lt_one := by norm_num
noncomputable def robotV0 : RobotState → ℝ
  | .high => 10 / 3
  | .low => 2


