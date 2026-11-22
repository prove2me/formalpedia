-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
-- name    : LeanPool_LowWeightPauliDynamics_Constants_PartFactor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T06:57:45.195821+00:00
-- url     : https://prove2.me/theorems/7cfe6287-b1dd-4619-92e9-a85b5db57f80
-- title:
--   Part Factor
-- statement:
--   Definitions and structural lemmas for Part Factor, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/PartFactor.lean

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD
open Finset
noncomputable def partFactor (j : ℕ) (s : ℝ) : ℝ :=
  (s + j - 1) ^ j / ((Nat.factorial j : ℝ) * ∏ i ∈ range j, (s - j + 1 + i))
noncomputable def diagFactor (j : ℕ) : ℝ :=
  (2 * (j : ℝ) - 1) ^ j / ((Nat.factorial j : ℝ) * (Nat.factorial j : ℝ))
end Lean4LPD


