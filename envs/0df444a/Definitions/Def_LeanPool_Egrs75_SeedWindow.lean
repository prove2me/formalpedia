-- Prove2me | Definitions.Def_LeanPool_Egrs75_SeedWindow
-- name    : LeanPool_Egrs75_SeedWindow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:24:31.266226+00:00
-- url     : https://prove2.me/theorems/ca31bc77-1e32-4f57-869c-2b37ecfbcf7d
-- title:
--   Seed Window
-- statement:
--   Definitions and structural lemmas for Seed Window, from Egor Lyfar; LeanPool contributors's pinned The EGRS two-prime theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/SeedWindow.lean

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_Egrs75_LogIrrationality
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Egrs75.SeedWindow
open Nat
open Egrs75
end Egrs75.SeedWindow


