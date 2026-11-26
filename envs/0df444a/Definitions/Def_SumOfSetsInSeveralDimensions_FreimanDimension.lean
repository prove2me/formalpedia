-- Prove2me | Definitions.Def_SumOfSetsInSeveralDimensions_FreimanDimension
-- name    : SumOfSetsInSeveralDimensions_FreimanDimension
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:05:23.554459+00:00
-- url     : https://prove2.me/theorems/05241288-5c3d-41f1-bb34-fa3aa16fe46f
-- title:
--   Freiman Dimension
-- statement:
--   Definitions and structural lemmas for Freiman Dimension, from Gabriel Dahia (gdahia/SumOfSetsInSeveralDimensions; see pinned Apache-2.0 LICENSE and source headers)'s pinned Ruzsa's lower bound for sumsets in several dimensions and asymmetric Freiman lemma development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gdahia/SumOfSetsInSeveralDimensions/blob/1f8da867debcce675e07cac515ea9598c1245a92/SumOfSetsInSeveralDimensions/FreimanDimension.lean

module
public import Mathlib.Combinatorics.Additive.FreimanHom
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace SumOfSetsInSeveralDimensions
open Finset
def rationalVectorToReal {d : ℕ} (v : Fin d → ℚ) : Fin d → ℝ := fun i ↦ (v i : ℝ)
def freimanModelDim {G : Type*} [DecidableEq G] [AddCommMonoid G] (X : Finset G) (d : ℕ) : Prop :=
  ∃ f : G → (Fin d → ℚ), IsAddFreimanIso 2 (X : Set G) (X.image f : Set (Fin d → ℚ)) f ∧
    ((X.image f).image rationalVectorToReal).affineDim = d
noncomputable def freimanDim {G : Type*} [DecidableEq G] [AddCommMonoid G] (X : Finset G) : ℕ := by
  classical
  exact Nat.findGreatest (freimanModelDim X) #X
end SumOfSetsInSeveralDimensions


