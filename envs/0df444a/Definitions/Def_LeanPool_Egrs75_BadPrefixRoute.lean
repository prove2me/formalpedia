-- Prove2me | Definitions.Def_LeanPool_Egrs75_BadPrefixRoute
-- name    : LeanPool_Egrs75_BadPrefixRoute
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:27:55.039623+00:00
-- url     : https://prove2.me/theorems/c7bf1383-5e6e-409a-90e3-6e2cee7ef6dd
-- title:
--   Bad Prefix Route
-- statement:
--   Definitions and structural lemmas for Bad Prefix Route, from Egor Lyfar; LeanPool contributors's pinned The EGRS two-prime theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/BadPrefixRoute.lean

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Definitions.Def_LeanPool_Egrs75_ClearingHigh
public import Definitions.Def_LeanPool_Egrs75_MuFinish
public import Definitions.Def_LeanPool_Egrs75_Reduction
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Totient
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Egrs75.Finish
open Nat
open Finset
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
open Egrs75.Probe
noncomputable def badPrefix (q n : ℕ) : ℕ := ∑ i ∈ badIndexSet q n, 2 ^ i
end Egrs75.Finish


