-- Prove2me | Definitions.Def_B1s_resolvent_scale_9_11
-- name    : B1s_resolvent_scale_9_11
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:37:18.641323+00:00
-- url     : https://prove2.me/theorems/ea6f4963-472d-56c2-90ee-e7a37f33913f
-- title:
--   resolvent scale 9 11
-- statement:
--   Definitions and structural lemmas for resolvent scale 9 11, from Ben Lawton (blawton/fried-conj-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Resonance-cluster conditional reduction for a proposed counterexample to Fried's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean

import Definitions.Def_B1s_fried_statement_defs_9_14
set_option autoImplicit true
set_option linter.style.header false
namespace FriedCrossing
open Filter Topology ContinuousLinearMap Asymptotics
namespace Scale
universe u
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {S : BanachScale.{u}} (F : ResolventFamily S X)
noncomputable def derivLoss (a b : ℕ) (hab : b + 2 ≤ a) (x : X) :
    X →L[ℝ] (S.H a →L[ℝ] S.H b) :=
  -(((compL ℝ (S.H a) (S.H (b + 1)) (S.H b))
      ((S.incl (b + 1) b (Nat.le_succ b)).comp (F.R (b + 1) x))).comp
    (((compL ℝ (S.H a) (S.H (b + 2)) (S.H (b + 1))).flip
      ((S.incl a (b + 2) hab).comp (F.R a x))).comp (fderiv ℝ (F.B (b + 1)) x)))
def lossBudget : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 * lossBudget k + 1
noncomputable def derivSplit (a b j : ℕ) (hj : b + j + 1 ≤ a) (x : X) :
    X →L[ℝ] (S.H a →L[ℝ] S.H b) :=
  -(((compL ℝ (S.H a) (S.H (b + j)) (S.H b))
      ((S.incl (b + j) b (Nat.le_add_right b j)).comp (F.R (b + j) x))).comp
    (((compL ℝ (S.H a) (S.H (b + j + 1)) (S.H (b + j))).flip
      ((S.incl a (b + j + 1) hj).comp (F.R a x))).comp (fderiv ℝ (F.B (b + j)) x)))
end Scale
end FriedCrossing


