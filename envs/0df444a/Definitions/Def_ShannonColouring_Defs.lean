-- Prove2me | Definitions.Def_ShannonColouring_Defs
-- name    : ShannonColouring_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T14:32:49.773841+00:00
-- url     : https://prove2.me/theorems/53bba087-2bed-5545-9eb4-672c8c4e8b21
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Juan Pablo Traverso Gianini (jtraverso/shannon-edge-colouring; see pinned Apache-2.0 LICENSE and source headers)'s pinned Shannon's theorem on edge colourings of multigraphs and its sharpness development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Defs.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace ShannonColouring
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
def Incident (ends : ι → V × V) (i : ι) (v : V) : Prop := (ends i).1 = v ∨ (ends i).2 = v
def degree (ends : ι → V × V) (v : V) : ℕ :=
  (Finset.univ.filter fun i => (ends i).1 = v ∨ (ends i).2 = v).card
def IsProperEdgeColouring (ends : ι → V × V) {k : ℕ} (c : ι → Fin k) : Prop :=
  ∀ i j, i ≠ j → (∃ v, Incident ends i v ∧ Incident ends j v) → c i ≠ c j
end ShannonColouring


