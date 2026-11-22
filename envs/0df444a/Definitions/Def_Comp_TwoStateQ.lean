-- Prove2me | Definitions.Def_Comp_TwoStateQ
-- name    : Comp_TwoStateQ
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T23:34:05.796344+00:00
-- url     : https://prove2.me/theorems/0a2d94c6-1411-4d4d-bbf0-cf3f12ab6842
-- title:
--   Two State Q
-- statement:
--   Definitions and structural lemmas for Two State Q, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/TwoStateQ.lean

import Definitions.Def_Comp_Iterate
import Theorems.Thm_Comp_MatrixGameQ_toMatrixGame_A
attribute [local simp] Comp.MatrixGameQ.toMatrixGame_A


set_option autoImplicit true
set_option linter.hashCommand false
namespace Comp
open Csg
def twoR : Bool → Bool → Bool → ℚ
  | true, _, _ => 0
  | false, _, _ => 1
def twoK : Bool → Bool → Bool → Bool → ℚ
  | true, a1, a2, s' => if s' = (a1 == a2) then 1 else 0
  | false, _, _, s' => if s' = false then 1 else 0
def twoGame : DiscountedCsgQ Bool Bool Bool where
  K := twoK
  r := twoR
  l := 1 / 2
def bothBools : List Bool := [true, false]
theorem twoGame_wf : twoGame.WellFormed := by
  refine ⟨⟨fun s a1 a2 s' => ?_, fun s a1 a2 => ?_⟩, ?_, ?_⟩
  · cases s <;> cases a1 <;> cases a2 <;> cases s' <;> simp [twoGame, twoK]
  · cases s <;> cases a1 <;> cases a2 <;>
      rw [Fintype.sum_bool] <;> simp [twoGame, twoK]
  · norm_num [twoGame]
  · norm_num [twoGame]
def v1 : Bool → ℚ
  | true => 0
  | false => 1
def v2 : Bool → ℚ
  | true => 1 / 4
  | false => 3 / 2
def vStar : Bool → ℚ
  | true => 2 / 3
  | false => 2
def unif2 : Bool → ℚ := fun _ => 1 / 2
def pure2 : Bool → ℚ
  | true => 1
  | false => 0
end Comp


