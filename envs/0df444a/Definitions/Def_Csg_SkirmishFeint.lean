-- Prove2me | Definitions.Def_Csg_SkirmishFeint
-- name    : Csg_SkirmishFeint
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:41:56.015558+00:00
-- url     : https://prove2.me/theorems/ab36c589-02c2-4334-8e10-214b32177c60
-- title:
--   Skirmish Feint
-- statement:
--   Definitions and structural lemmas for Skirmish Feint, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
set_option autoImplicit true
namespace Csg
inductive HiderAction
  | hide
  | run
  deriving DecidableEq, Inhabited
instance : Fintype HiderAction where
  elems := {HiderAction.hide, .run}
  complete := by intro a; cases a <;> decide
inductive ThrowerAction
  | wait
  | throw
  | feint
  deriving DecidableEq, Inhabited
instance : Fintype ThrowerAction where
  elems := {ThrowerAction.wait, .throw, .feint}
  complete := by intro a; cases a <;> decide
inductive SkirmishState
  | hide
  | home
  | wet
  deriving DecidableEq, Inhabited
instance : Fintype SkirmishState where
  elems := {SkirmishState.hide, .home, .wet}
  complete := by intro s; cases s <;> decide
noncomputable def homeWetSplit (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : PMF SkirmishState :=
  PMF.ofFinset
    (fun s => match s with
      | .home => ENNReal.ofReal p
      | .wet => ENNReal.ofReal (1 - p)
      | .hide => 0)
    {SkirmishState.home, .wet}
    (by
      have hne : (SkirmishState.home : SkirmishState) ≠ .wet := by decide
      rw [Finset.sum_insert (by simp), Finset.sum_singleton]
      change ENNReal.ofReal p + ENNReal.ofReal (1 - p) = 1
      rw [← ENNReal.ofReal_add hp0 (by linarith), show p + (1 - p) = 1 by ring, ENNReal.ofReal_one])
    (by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      push Not at hs
      rcases s with _ | _ | _
      · rfl
      · exact absurd rfl hs.1
      · exact absurd rfl hs.2)
noncomputable def jointK : SkirmishState → HiderAction → ThrowerAction → PMF SkirmishState
  | .home, _, _ => PMF.pure .home
  | .wet, _, _ => PMF.pure .wet
  | .hide, .hide, .wait => PMF.pure .hide
  | .hide, .hide, .throw => homeWetSplit (4 / 5) (by norm_num) (by norm_num)
  | .hide, .hide, .feint => homeWetSplit (1 / 2) (by norm_num) (by norm_num)
  | .hide, .run, .wait => PMF.pure .home
  | .hide, .run, .throw => PMF.pure .wet
  | .hide, .run, .feint => homeWetSplit (3 / 10) (by norm_num) (by norm_num)
noncomputable def jointR : SkirmishState → HiderAction → ThrowerAction → ℝ := fun _ _ _ => 0
noncomputable def skirmishMinCSG : CSG SkirmishState HiderAction ThrowerAction where
  K s a1 a2 := jointK s a1 a2
  r s a1 a2 := jointR s a1 a2
noncomputable def skirmishMaxCSG : CSG SkirmishState ThrowerAction HiderAction where
  K s a2 a1 := jointK s a1 a2
  r s a2 a1 := jointR s a1 a2
def hiderPureHide : HiderAction → ℝ
  | .hide => 1
  | .run => 0
noncomputable def throwerMinMix : ThrowerAction → ℝ
  | .wait => 4 / 5
  | .throw => 1 / 5
  | .feint => 0
noncomputable def throwerMaxMix : ThrowerAction → ℝ
  | .wait => 2 / 7
  | .throw => 0
  | .feint => 5 / 7
def hiderPureHideCol : HiderAction → ℝ
  | .hide => 1
  | .run => 0
end Csg


