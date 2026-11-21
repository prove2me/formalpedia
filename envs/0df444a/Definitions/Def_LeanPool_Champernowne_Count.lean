-- Prove2me | Definitions.Def_LeanPool_Champernowne_Count
-- name    : LeanPool_Champernowne_Count
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:34:29.734291+00:00
-- url     : https://prove2.me/theorems/88d698cc-b4d8-4aaa-bf18-d45ef425d1da
-- title:
--   Count
-- statement:
--   Definitions and structural lemmas for Count, from Arthur Champernowne and LeanPool contributors's pinned Champernowne normality in every base development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Count.lean

module
public import Definitions.Def_LeanPool_Champernowne_Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Finset.Powerset
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Champernowne
def allWords (b : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | k + 1 => (Finset.range b).biUnion fun d => (allWords b k).image (d :: ·)
end Champernowne


