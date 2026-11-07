-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
-- name    : QEC_Coding_ExpanderCodes_LocallyMinimalDistance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:09:26.411948+00:00
-- url     : https://prove2.me/theorems/1a08ca82-b01a-456e-9ab8-62d963e7512c
-- title:
--   Locally Minimal Distance
-- statement:
--   Definitions and structural lemmas for Locally Minimal Distance, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocallyMinimalDistance.lean

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.Order.Lattice.Nat
set_option autoImplicit false
namespace QEC.Coding.LocallyMinimalDistance
universe u v
variable {C : Type*} [AddCommGroup C]
def IsLocallyMinimal (weight : C → Nat) (moves : Finset C) (c : C) : Prop :=
  ∀ m ∈ moves, weight c ≤ weight (c + m)
noncomputable def cosetWeight (weight : C → Nat) (B : AddSubgroup C) (c : C) : Nat :=
  sInf {n : Nat | ∃ b ∈ B, weight (c + b) = n}
noncomputable def elementaryBoundaryMoves
    {F : Type u} {ι κ₀ κ₂ : Type v} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂)) :
    Finset (Word F ι) := by
  classical
  exact Finset.univ.image
    (fun p : κ₂ × F => K.boundary2 (p.2 • canonicalBasisWord p.1))
noncomputable def elementaryCoboundaryMoves
    {F : Type u} {ι κ₀ κ₂ : Type v} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂)) :
    Finset (Word F ι) := by
  classical
  exact Finset.univ.image
    (fun p : κ₀ × F =>
      wordLinearMapTranspose K.boundary1 (p.2 • canonicalBasisWord p.1))
end QEC.Coding.LocallyMinimalDistance


