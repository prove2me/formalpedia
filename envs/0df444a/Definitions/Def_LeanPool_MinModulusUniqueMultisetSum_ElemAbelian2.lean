-- Prove2me | Definitions.Def_LeanPool_MinModulusUniqueMultisetSum_ElemAbelian2
-- name    : LeanPool_MinModulusUniqueMultisetSum_ElemAbelian2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T22:39:37.364831+00:00
-- url     : https://prove2.me/theorems/e5e47cd0-b568-4a5d-a207-8b32d307f6ab
-- title:
--   Elem Abelian2
-- statement:
--   Definitions and structural lemmas for Elem Abelian2, from José A. R. Fonollosa; maintained by LeanPool contributors's pinned Minimum modulus for the unique multiset-sum problem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MinModulusUniqueMultisetSum/ElemAbelian2.lean

module
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.GroupTheory.GroupAction.Ring
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MinModulus
open scoped BigOperators
open Module
def UniqueMultisetSums {n k : ℕ} (g : Fin n → (Fin k → ZMod 2)) : Prop :=
  ∀ m : Fin n → ℕ,
    (∑ i, m i = n) →
    (∑ i, ((m i : ℕ) : ZMod 2) • g i = ∑ i, g i) →
    ∀ i, m i = 1
end MinModulus


