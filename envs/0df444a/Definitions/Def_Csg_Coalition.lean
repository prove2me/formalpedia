-- Prove2me | Definitions.Def_Csg_Coalition
-- name    : Csg_Coalition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:41:51.996633+00:00
-- url     : https://prove2.me/theorems/8e6fb691-408c-4537-98e3-9b27c3de485f
-- title:
--   Coalition
-- statement:
--   Definitions and structural lemmas for Coalition, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Coalition.lean

import Definitions.Def_Csg_Basic
set_option autoImplicit true
namespace Csg
structure NCSG (S Players : Type*) (A : Players → Type*)
    [Fintype S] [Fintype Players] [DecidableEq Players]
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)] where
  /-- Transition kernel: `K s a` is the distribution over next states after every player
      simultaneously plays their component of the joint action `a`. -/
  K : S → (∀ i, A i) → PMF S
  /-- Reward for the joint action `a` in state `s`. Which side this favours, once a coalition is
      plugged into the maximising slot by `reduceMax`, is the "least certain part" flagged in the
      module docstring above -- not validated yet. -/
  r : S → (∀ i, A i) → ℝ
variable {S Players : Type*} {A : Players → Type*}
  [Fintype S] [Fintype Players] [DecidableEq Players]
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
namespace NCSG
variable (C : Finset Players)
abbrev CoalitionAction (A : Players → Type*) (C : Finset Players) : Type _ := ∀ i : C, A i
abbrev ComplementAction (A : Players → Type*) (C : Finset Players) : Type _ :=
  ∀ i : (Cᶜ : Finset Players), A i
def combine (aC : CoalitionAction A C) (aC' : ComplementAction A C) : ∀ i, A i :=
  fun i => if h : i ∈ C then aC ⟨i, h⟩ else aC' ⟨i, Finset.mem_compl.mpr h⟩
variable (G : NCSG S Players A)
noncomputable def reduceMin : CSG S (CoalitionAction A C) (ComplementAction A C) where
  K s aC aC' := G.K s (combine C aC aC')
  r s aC aC' := G.r s (combine C aC aC')
noncomputable def reduceMax : CSG S (ComplementAction A C) (CoalitionAction A C) where
  K s aC' aC := G.K s (combine C aC aC')
  r s aC' aC := G.r s (combine C aC aC')
end NCSG
end Csg


