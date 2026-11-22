-- Prove2me | Definitions.Def_SumProduct_EulerBound
-- name    : SumProduct_EulerBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T23:45:04.826126+00:00
-- url     : https://prove2.me/theorems/a52e03f2-a3eb-401e-a908-d2f4cf6d42ba
-- title:
--   Euler Bound
-- statement:
--   Definitions and structural lemmas for Euler Bound, from Mathlib Initiative and contributors's pinned A real sum-product counterexample conditional on Martinet’s tower theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/EulerBound.lean

import Mathlib
set_option autoImplicit true
open scoped NumberField
open NumberField UniqueFactorizationMonoid
namespace SumProduct
variable {K : Type*} [Field K] [NumberField K]
noncomputable def idealCount (K : Type*) [Field K] [NumberField K] (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
noncomputable def idealCountArith (K : Type*) [Field K] [NumberField K] : ArithmeticFunction ℕ where
  toFun n := if n = 0 then 0 else idealCount K n
  map_zero' := if_pos rfl
end SumProduct


