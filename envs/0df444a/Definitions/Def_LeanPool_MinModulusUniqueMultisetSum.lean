-- Prove2me | Definitions.Def_LeanPool_MinModulusUniqueMultisetSum
-- name    : LeanPool_MinModulusUniqueMultisetSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T22:40:28.311282+00:00
-- url     : https://prove2.me/theorems/7908acbd-a893-44cd-8d86-c8a4753c1cfe
-- title:
--   Min Modulus Unique Multiset Sum
-- statement:
--   Definitions and structural lemmas for Min Modulus Unique Multiset Sum, from José A. R. Fonollosa; maintained by LeanPool contributors's pinned Minimum modulus for the unique multiset-sum problem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MinModulusUniqueMultisetSum.lean

module
public import Definitions.Def_LeanPool_MinModulusUniqueMultisetSum_UniqueSums
public import Definitions.Def_LeanPool_MinModulusUniqueMultisetSum_ElemAbelian2
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Continuity.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset
set_option autoImplicit true
@[expose] public section
@[expose] public section


