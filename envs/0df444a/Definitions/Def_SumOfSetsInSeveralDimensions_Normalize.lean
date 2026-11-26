-- Prove2me | Definitions.Def_SumOfSetsInSeveralDimensions_Normalize
-- name    : SumOfSetsInSeveralDimensions_Normalize
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:05:30.221132+00:00
-- url     : https://prove2.me/theorems/4c9ccbe4-17fd-411e-a50e-1538d0b39a3c
-- title:
--   Normalize
-- statement:
--   Definitions and structural lemmas for Normalize, from Gabriel Dahia (gdahia/SumOfSetsInSeveralDimensions; see pinned Apache-2.0 LICENSE and source headers)'s pinned Ruzsa's lower bound for sumsets in several dimensions and asymmetric Freiman lemma development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/Normalize.lean

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Order.Group.PiLex
public import Mathlib.Tactic.Abel
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {D : ℕ}
noncomputable def lexMin (S : Finset (Fin D → ℝ)) (hS : S.Nonempty) : Fin D → ℝ :=
  ofLex ((S.image toLex).min' (hS.image toLex))
noncomputable def normalize (S : Finset (Fin D → ℝ)) (hS : S.Nonempty) : Finset (Fin D → ℝ) :=
  S.image fun x ↦ x - lexMin S hS
end SumOfSetsInSeveralDimensions


