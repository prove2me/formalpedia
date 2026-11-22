-- Prove2me | Definitions.Def_LeanPool_Egrs75_DigitVector
-- name    : LeanPool_Egrs75_DigitVector
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:26:38.80584+00:00
-- url     : https://prove2.me/theorems/7d907d25-e875-42b7-925c-222d10b2154d
-- title:
--   Digit Vector
-- statement:
--   Definitions and structural lemmas for Digit Vector, from Egor Lyfar; LeanPool contributors's pinned The EGRS two-prime theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/DigitVector.lean

module
public import Definitions.Def_LeanPool_Egrs75_LeafInduction
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Egrs75.RepairDV
open Nat
open Egrs75
open Egrs75.LeafInduction
@[reducible] def bigQ (q d : ℕ) : Bool := decide ((q - 1) / 2 < d)
def badIndexSet (q n : ℕ) : Finset ℕ :=
  (Finset.range (Nat.digits q n).length).filter (fun i => bigQ q ((Nat.digits q n).getD i 0))
noncomputable def topBadIndex (q n : ℕ) : ℕ :=
  if h : (badIndexSet q n).Nonempty then (badIndexSet q n).max' h else 0
end Egrs75.RepairDV


