-- Prove2me | Definitions.Def_LeanPool_Egrs75_MuFinish
-- name    : LeanPool_Egrs75_MuFinish
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:27:31.529976+00:00
-- url     : https://prove2.me/theorems/2dd9099b-5342-424f-80b6-4667d3036c0c
-- title:
--   Mu Finish
-- statement:
--   Definitions and structural lemmas for Mu Finish, from Egor Lyfar; LeanPool contributors's pinned The EGRS two-prime theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MuFinish.lean

module
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Definitions.Def_LeanPool_Egrs75_ConditionThreeWindow
public import Definitions.Def_LeanPool_Egrs75_AddBranch
public import Definitions.Def_LeanPool_Egrs75_MoveDigits
public import Definitions.Def_LeanPool_Egrs75_Reduction
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_SeedWindow
public import Definitions.Def_LeanPool_Egrs75_SubtractBranch
public import Mathlib.Data.Nat.Totient
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Egrs75.MuFinish
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
open Egrs75.P4
noncomputable def muVal (q : ℕ) (hq3 : 3 ≤ q) (n : ℕ) : ℕ :=
  if hbad : 0 < badCountQ q n then
    leastGoodAbove hq3 hbad * q + ((q - 1) / 2 - n / q ^ (leastGoodAbove hq3 hbad) % q)
  else 0
end Egrs75.MuFinish


