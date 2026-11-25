-- Prove2me | Definitions.Def_NashWilliamsLib_Basic
-- name    : NashWilliamsLib_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T17:44:54.164819+00:00
-- url     : https://prove2.me/theorems/99d1541b-4c70-4c57-83f6-258931e1bdbb
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Juan Pablo Traverso Gianini (jtraverso/nash-williams-orientation; see pinned Apache-2.0 LICENSE and source headers)'s pinned Nash-Williams' weak orientation theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/nash-williams-orientation/blob/3412d885cf3ba6680770cb8014df96af8fa3d042/NashWilliamsLib/Basic.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace NashWilliams
variable {V ι : Type*} [DecidableEq V]
def cutF (ends : ι → V × V) (F : Finset ι) (S : Finset V) : ℕ :=
  (F.filter fun i => ((ends i).1 ∈ S) ≠ ((ends i).2 ∈ S)).card
def Leaves (p : V × V) (b : Bool) (S : Finset V) : Prop :=
  if b then p.1 ∈ S ∧ p.2 ∉ S else p.2 ∈ S ∧ p.1 ∉ S
instance (p : V × V) (b : Bool) (S : Finset V) : Decidable (Leaves p b S) := by
  unfold Leaves; split <;> infer_instance
def outCutF (ends : ι → V × V) (o : ι → Bool) (F : Finset ι) (S : Finset V) : ℕ :=
  (F.filter fun i => Leaves (ends i) (o i) S).card
def Req (K : ℕ) (T : Finset V) (ends : ι → V × V) (F : Finset ι) : Prop :=
  ∀ S ⊆ T, S.Nonempty → S ≠ T → K ≤ cutF ends F S
def Inside (T : Finset V) (ends : ι → V × V) (F : Finset ι) : Prop :=
  ∀ i ∈ F, (ends i).1 ∈ T ∧ (ends i).2 ∈ T
def cr (p : V × V) (S : Finset V) : ℕ := if (p.1 ∈ S) ≠ (p.2 ∈ S) then 1 else 0
end NashWilliams


