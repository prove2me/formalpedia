-- Prove2me | Definitions.Def_Comp_Qualitative
-- name    : Comp_Qualitative
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T22:51:38.351496+00:00
-- url     : https://prove2.me/theorems/c462190e-a07f-460e-b003-73b36b2c5958
-- title:
--   Qualitative
-- statement:
--   Definitions and structural lemmas for Qualitative, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Qualitative.lean

import Definitions.Def_Comp_Basic
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Comp_Lattice
set_option autoImplicit true
namespace Comp
open Csg
namespace CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
def supportQ (G : CsgQ S A1 A2) (s : S) (a1 : A1) (a2 : A2) : Set S :=
  {s' | G.K s a1 a2 s' ≠ 0}
instance (G : CsgQ S A1 A2) (s : S) (a1 : A1) (a2 : A2) :
    DecidablePred (· ∈ G.supportQ s a1 a2) := fun _ => by
  unfold supportQ
  infer_instance
def Pre1Q (G : CsgQ S A1 A2) (x : Set S) : Set S :=
  {s | ∃ a1, ∀ a2, G.supportQ s a1 a2 ⊆ x}
theorem mem_Pre1Q_iff (G : CsgQ S A1 A2) (x : Set S) (s : S) :
    s ∈ G.Pre1Q x ↔ ∃ a1, ∀ a2, ∀ s', G.K s a1 a2 s' ≠ 0 → s' ∈ x := Iff.rfl
instance (G : CsgQ S A1 A2) (x : Set S) [DecidablePred (· ∈ x)] :
    DecidablePred (· ∈ G.Pre1Q x) := fun s =>
  decidable_of_iff (∃ a1, ∀ a2, ∀ s', G.K s a1 a2 s' ≠ 0 → s' ∈ x)
    (mem_Pre1Q_iff G x s).symm
def GStepQ (G : CsgQ S A1 A2) (safe : Set S) (x : Set S) : Set S := G.Pre1Q x ∩ safe
instance (G : CsgQ S A1 A2) (safe x : Set S) [DecidablePred (· ∈ safe)]
    [DecidablePred (· ∈ x)] : DecidablePred (· ∈ G.GStepQ safe x) := fun _ => by
  unfold GStepQ
  infer_instance
end CsgQ
end Comp


