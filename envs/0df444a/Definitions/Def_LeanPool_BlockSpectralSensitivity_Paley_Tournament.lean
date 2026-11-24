-- Prove2me | Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
-- name    : LeanPool_BlockSpectralSensitivity_Paley_Tournament
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T00:46:55.115409+00:00
-- url     : https://prove2.me/theorems/76936fa5-792e-4f97-9372-d646e8c52078
-- title:
--   Tournament
-- statement:
--   Definitions and structural lemmas for Tournament, from Alex Meiburg (Timeroot/BS_Lam) and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Block sensitivity vs squared spectral sensitivity separation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Paley/Tournament.lean

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Tactic.NormNum.Prime
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
section QuadraticCharSums
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end QuadraticCharSums
namespace BSLambda
section Paley
def paleyArc (k : ℕ) [Fact (Nat.Prime k)] (i j : ZMod k) : Bool :=
  decide (quadraticChar (ZMod k) (j - i) = 1)
theorem prime_14011 : Nat.Prime 14011 := by norm_num
instance factPrime14011 : Fact (Nat.Prime 14011) := ⟨prime_14011⟩
end Paley
end BSLambda


