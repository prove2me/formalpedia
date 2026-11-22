-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
-- name    : LeanPool_LowWeightPauliDynamics_Pauli_DiscardWitness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:35:49.648718+00:00
-- url     : https://prove2.me/theorems/030312bd-0e75-4d7c-b149-b9cbef741598
-- title:
--   Discard Witness
-- statement:
--   Definitions and structural lemmas for Discard Witness, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/DiscardWitness.lean

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD.DiscardWitness
open Finset PauliString
def G : PauliString 2 := ⟨![1, 1], ![0, 0], 0⟩
def P : PauliString 2 := ⟨![0, 0], ![1, 0], 0⟩
def Q : PauliString 2 := ⟨![1, 1], ![1, 0], 1⟩
def Gs (g : ℕ) : PauliString 2 := if g % 2 = 0 then G else Q
noncomputable def angles (_ : ℕ) : ℝ := Real.pi / 2
end Lean4LPD.DiscardWitness


