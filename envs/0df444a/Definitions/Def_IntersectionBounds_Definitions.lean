-- Prove2me | Definitions.Def_IntersectionBounds_Definitions
-- name    : IntersectionBounds_Definitions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T12:37:02.97351+00:00
-- url     : https://prove2.me/theorems/371ada21-54c7-46b2-9a6a-63bf6de2ed8a
-- title:
--   Definitions
-- statement:
--   Definitions and structural lemmas for Definitions, from Juan Pablo Traverso Gianini (jtraverso/restricted-intersections; see pinned Apache-2.0 LICENSE and source headers)'s pinned Ray-Chaudhuri-Wilson theorem for uniform families with restricted intersections development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/Definitions.lean

module
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace IntersectionBounds
universe u
variable {V : Type u}
def Uniform (F : Finset (Finset V)) (k : ℕ) : Prop := ∀ A ∈ F, A.card = k
open Classical in
/-- Distinct members have intersection cardinality in L. -/
def IntersectionsIn (F : Finset (Finset V)) (L : Finset ℕ) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).card ∈ L
open Classical in
/-- The actual intersection cardinalities of distinct members. -/
noncomputable def intersectionSpectrum (F : Finset (Finset V)) : Finset ℕ :=
  F.offDiag.image (fun p => (p.1 ∩ p.2).card)
end IntersectionBounds


