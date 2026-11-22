-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
-- name    : LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:32:49.09173+00:00
-- url     : https://prove2.me/theorems/1a047fd7-dd4f-45b6-a437-2e17e4c66325
-- title:
--   Elementary Bounds
-- statement:
--   Definitions and structural lemmas for Elementary Bounds, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/ElementaryBounds.lean

module
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Iterate
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Order.Monotone.Defs
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Arithmetic
def exp2 (x : ℕ) : ℕ := 2 ^ x
end DeciSigma1.Arithmetic


