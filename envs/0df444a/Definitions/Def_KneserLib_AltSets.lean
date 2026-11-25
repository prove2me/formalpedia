-- Prove2me | Definitions.Def_KneserLib_AltSets
-- name    : KneserLib_AltSets
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:42:26.696369+00:00
-- url     : https://prove2.me/theorems/f2a5f5ee-2d38-5cc9-8caf-e652edfc1e2e
-- title:
--   Alt Sets
-- statement:
--   Definitions and structural lemmas for Alt Sets, from Juan Pablo Traverso Gianini (jtraverso/kneser-lovasz; see pinned Apache-2.0 LICENSE and source headers)'s pinned Kneser's conjecture and the octahedral Tucker lemma development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/AltSets.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace KneserColouring
open Finset
def IsAlt (s : ℕ) (S : Finset ℤ) : Prop :=
  ∀ a ∈ S, (0 < a ↔ Even ((S.filter (fun b => |b| < |a|)).card + s))
instance (s : ℕ) (S : Finset ℤ) : Decidable (IsAlt s S) := by
  unfold IsAlt; infer_instance
def NoComp (S : Finset ℤ) : Prop := ∀ a ∈ S, ∀ b ∈ S, a ≠ -b
end KneserColouring


