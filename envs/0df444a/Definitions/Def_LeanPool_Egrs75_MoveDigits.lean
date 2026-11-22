-- Prove2me | Definitions.Def_LeanPool_Egrs75_MoveDigits
-- name    : LeanPool_Egrs75_MoveDigits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:27:01.950591+00:00
-- url     : https://prove2.me/theorems/4ed00788-7069-4172-9e52-b25f56a9cac3
-- title:
--   Move Digits
-- statement:
--   Definitions and structural lemmas for Move Digits, from Egor Lyfar; LeanPool contributors's pinned The EGRS two-prime theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MoveDigits.lean

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Egrs75.MoveDigits
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
end Egrs75.MoveDigits


