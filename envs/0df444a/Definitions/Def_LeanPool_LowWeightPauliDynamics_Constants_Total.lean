-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
-- name    : LeanPool_LowWeightPauliDynamics_Constants_Total
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T06:58:30.444857+00:00
-- url     : https://prove2.me/theorems/151e9904-d8dd-4b6b-8d15-57a4f207299d
-- title:
--   Total
-- statement:
--   Definitions and structural lemmas for Total, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Total.lean

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD
open Finset
noncomputable def tZeroModel (G kh a : ℝ) : ℝ := 1 / (2 * G * (kh - 1) * a)
noncomputable def decayBase (G kh a t : ℝ) : ℝ := t / tZeroModel G kh a
end Lean4LPD


