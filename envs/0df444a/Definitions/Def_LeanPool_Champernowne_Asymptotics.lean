-- Prove2me | Definitions.Def_LeanPool_Champernowne_Asymptotics
-- name    : LeanPool_Champernowne_Asymptotics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:35:34.76694+00:00
-- url     : https://prove2.me/theorems/e045f75a-285f-4513-b253-9aabba901867
-- title:
--   Asymptotics
-- statement:
--   Definitions and structural lemmas for Asymptotics, from Arthur Champernowne and LeanPool contributors's pinned Champernowne normality in every base development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Asymptotics.lean

module
public import Definitions.Def_LeanPool_Champernowne_Positions
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Champernowne
open Filter Asymptotics Topology
def champM (b n : ℕ) : ℕ := Nat.log b (champIndex b n + 1) + 1
end Champernowne


