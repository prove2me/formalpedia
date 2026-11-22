-- Prove2me | Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
-- name    : LeanPool_Egrs75_DigitAtToolkit
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:26:40.803703+00:00
-- url     : https://prove2.me/theorems/0a765baf-7fa6-486d-a0f0-72997dffd2aa
-- title:
--   Digit At Toolkit
-- statement:
--   Definitions and structural lemmas for Digit At Toolkit, from Egor Lyfar; LeanPool contributors's pinned The EGRS two-prime theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitAtToolkit.lean

module
public import Definitions.Def_LeanPool_Egrs75_LeafInduction
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Egrs75.RepairPaperfaithful
open Nat
open Egrs75
open Egrs75.LeafInduction
def digitAt (p i n : ℕ) : ℕ := n / p ^ i % p
def BadAt (q i n : ℕ) : Prop := (q - 1) / 2 < digitAt q i n
end Egrs75.RepairPaperfaithful


