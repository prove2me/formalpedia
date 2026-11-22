-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
-- name    : LeanPool_LowWeightPauliDynamics_Constants_Entry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T06:57:48.501803+00:00
-- url     : https://prove2.me/theorems/68aeaa37-be81-413d-8315-f2cf76a04b93
-- title:
--   Entry
-- statement:
--   Definitions and structural lemmas for Entry, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Entry.lean

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD
open Finset
def rungW (kh1 c : ℝ) (m : ℕ) : ℝ := kh1 * ((m : ℝ) - 1 + c)
noncomputable def epsJump (kh1 c a : ℝ) (j nu : ℕ) : ℝ :=
  (rungW kh1 c (nu + j) * a) ^ j / (Nat.factorial j : ℝ)
noncomputable def betaOf (kh1 c a : ℝ) : ℝ := 2 * Real.exp 1 * rungW kh1 c 2 * a
noncomputable def entryFactor (kh1 c a : ℝ) (nu : ℕ) : ℝ :=
  ∑' i : ℕ, epsJump kh1 c a (nu + i) nu
end Lean4LPD


