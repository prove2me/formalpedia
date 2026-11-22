-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Recursion
-- name    : LeanPool_LowWeightPauliDynamics_Ladder_Recursion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T06:58:45.220307+00:00
-- url     : https://prove2.me/theorems/617a8a7a-be7a-416f-aee6-6e3892b875f3
-- title:
--   Recursion
-- statement:
--   Definitions and structural lemmas for Recursion, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/Recursion.lean

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Defs
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_HockeyStick
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD.Ladder
open Finset
variable {a M : ℝ} (L : Ladder a M)
end Lean4LPD.Ladder


