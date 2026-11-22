-- Prove2me | Definitions.Def_Csg_SkirmishFeintCoalition
-- name    : Csg_SkirmishFeintCoalition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:42:30.515296+00:00
-- url     : https://prove2.me/theorems/d2778b7f-0035-4c81-a022-946078bec16b
-- title:
--   Skirmish Feint Coalition
-- statement:
--   Definitions and structural lemmas for Skirmish Feint Coalition, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeintCoalition.lean

import Definitions.Def_Csg_SkirmishFeint
import Definitions.Def_Csg_Coalition
set_option autoImplicit true
namespace Csg
inductive SkirmishPlayer
  | hider
  | thrower
  deriving DecidableEq, Inhabited
instance : Fintype SkirmishPlayer where
  elems := {SkirmishPlayer.hider, .thrower}
  complete := by intro p; cases p <;> decide
theorem skirmishPlayer_ne_hider_iff (p : SkirmishPlayer) :
    p ≠ SkirmishPlayer.hider ↔ p = SkirmishPlayer.thrower := by
  cases p <;> simp
def SkirmishAction : SkirmishPlayer → Type
  | .hider => HiderAction
  | .thrower => ThrowerAction
instance : ∀ p, Fintype (SkirmishAction p)
  | .hider => inferInstanceAs (Fintype HiderAction)
  | .thrower => inferInstanceAs (Fintype ThrowerAction)
instance : ∀ p, Nonempty (SkirmishAction p)
  | .hider => inferInstanceAs (Nonempty HiderAction)
  | .thrower => inferInstanceAs (Nonempty ThrowerAction)
instance : ∀ p, DecidableEq (SkirmishAction p)
  | .hider => inferInstanceAs (DecidableEq HiderAction)
  | .thrower => inferInstanceAs (DecidableEq ThrowerAction)
noncomputable def skirmishNCSG : NCSG SkirmishState SkirmishPlayer SkirmishAction where
  K s a := jointK s (a .hider) (a .thrower)
  r s a := jointR s (a .hider) (a .thrower)
def hiderC : Finset SkirmishPlayer := {SkirmishPlayer.hider}
def hiderSingletonEquiv : NCSG.CoalitionAction SkirmishAction hiderC ≃ HiderAction where
  toFun x := x ⟨SkirmishPlayer.hider, Finset.mem_singleton_self _⟩
  invFun h := fun i => by
    obtain ⟨val, prop⟩ := i
    have hval : val = SkirmishPlayer.hider := Finset.mem_singleton.mp prop
    subst hval
    exact h
  left_inv x := by
    funext i
    obtain ⟨val, prop⟩ := i
    have hval : val = SkirmishPlayer.hider := Finset.mem_singleton.mp prop
    subst hval
    rfl
  right_inv _ := rfl
def throwerComplementEquiv : NCSG.ComplementAction SkirmishAction hiderC ≃ ThrowerAction where
  toFun x := x ⟨SkirmishPlayer.thrower, by simp [hiderC, Finset.mem_compl]⟩
  invFun h := fun i => by
    obtain ⟨val, prop⟩ := i
    have hne : val ≠ SkirmishPlayer.hider := by simpa [hiderC, Finset.mem_compl] using prop
    have hval : val = SkirmishPlayer.thrower := (skirmishPlayer_ne_hider_iff val).mp hne
    subst hval
    exact h
  left_inv x := by
    funext i
    obtain ⟨val, prop⟩ := i
    have hne : val ≠ SkirmishPlayer.hider := by simpa [hiderC, Finset.mem_compl] using prop
    have hval : val = SkirmishPlayer.thrower := (skirmishPlayer_ne_hider_iff val).mp hne
    subst hval
    rfl
  right_inv _ := rfl
end Csg


