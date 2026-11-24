-- Prove2me | Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
-- name    : LeanPool_BlockSpectralSensitivity_Numerics_Binomial
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T00:44:04.430081+00:00
-- url     : https://prove2.me/theorems/e050a8c3-f6f5-42af-a20a-a22dad619dfb
-- title:
--   Binomial
-- statement:
--   Definitions and structural lemmas for Binomial, from Alex Meiburg (Timeroot/BS_Lam) and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Block sensitivity vs squared spectral sensitivity separation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Numerics/Binomial.lean

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.NormNum.Pow
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BSLambda.Numerics
attribute [local simp] Nat.choose_eq_descFactorial_div_factorial Nat.descFactorial Nat.factorial
end BSLambda.Numerics


