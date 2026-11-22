-- Prove2me | Definitions.Def_LeanPool_Egrs75_SubtractBranch
-- name    : LeanPool_Egrs75_SubtractBranch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:26:58.548179+00:00
-- url     : https://prove2.me/theorems/9e8ec304-4832-4c2a-b093-9f40726029aa
-- title:
--   Subtract Branch
-- statement:
--   Definitions and structural lemmas for Subtract Branch, from Egor Lyfar; LeanPool contributors's pinned The EGRS two-prime theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SubtractBranch.lean

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.Nat.Factorization.Defs
public import Definitions.Def_LeanPool_Egrs75_RoundUp
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Egrs75.ClearingP3
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
noncomputable def lowPDigitIndex (p n : ℕ) : ℕ := (n.factorization p)
end Egrs75.ClearingP3


