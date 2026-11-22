-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
-- name    : LeanPool_LowWeightPauliDynamics_Constants_C0
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T06:57:47.699694+00:00
-- url     : https://prove2.me/theorems/c9b3e240-19db-43f6-bb5a-de834cc08dcb
-- title:
--   C0
-- statement:
--   Definitions and structural lemmas for C0, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD
open Real
noncomputable def cZero (r m G B : ℝ) : ℝ :=
  (r + 1) / r * exp (9 / 4 * (m + 1) / (r * G)) * (1 + B) ^ ((1 : ℝ) / (m + 1))
noncomputable def tZero (c G kh a : ℝ) : ℝ := 1 / (c * G * (kh - 1) * a)
def Admissible (r m G : ℝ) : Prop :=
  1 ≤ r ∧ 0 ≤ m ∧ 0 < G ∧ m ≤ r ∧ 8 * (m + 1) ^ 2 ≤ r * G
end Lean4LPD


