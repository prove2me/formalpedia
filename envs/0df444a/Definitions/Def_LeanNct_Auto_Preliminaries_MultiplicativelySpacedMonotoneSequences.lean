-- Prove2me | Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences
-- name    : LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:37:53.666109+00:00
-- url     : https://prove2.me/theorems/86004c20-27cc-454f-9ca2-6847965ceebd
-- title:
--   Multiplicatively Spaced Monotone Sequences
-- statement:
--   Definitions and structural lemmas for Multiplicatively Spaced Monotone Sequences, from Floris van Doorn, Polona Durcik, Joris Roos, Lenka Slavíková, Christoph Thiele (roos-j/lean-nct; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Norm-variation of multiple ergodic averages for commuting transformations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Auto
open Set
def SpacedSequence (a : ℤ → ℝ) : Prop :=
  ∀ j : ℤ, 0 < a j ∧ 2 * a j ≤ a (j + 1)
def A : Set (ℤ → ℝ) := {a | SpacedSequence a}
noncomputable def aux_extensionOfSequence (J : ℕ) (a : ℤ → ℝ) : ℤ → ℝ := fun j =>
  if j < 0 then (2 : ℝ) ^ j * a 0
  else if j < (J : ℤ) then a j
  else (2 : ℝ) ^ (j - J + 1) * a (J - 1)
def WithinSequenceDistance (a b : ℤ → ℝ) (k : ℕ) : Prop :=
  ∀ j : ℤ, a (j - k) ≤ b j ∧ b j ≤ a (j + k)
noncomputable def SequenceDistance (a b : ℤ → ℝ) : WithTop ℕ :=
  by
    classical
    exact if h : ∃ k : ℕ, WithinSequenceDistance a b k then (Nat.find h : WithTop ℕ) else ⊤
def sequenceDistanceBall (a : ℤ → ℝ) (r : WithTop ℕ) : Set (ℤ → ℝ) :=
  {b | SpacedSequence b ∧ SequenceDistance a b ≤ r}
end Auto


