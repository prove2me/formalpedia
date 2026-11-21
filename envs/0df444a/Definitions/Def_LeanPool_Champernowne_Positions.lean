-- Prove2me | Definitions.Def_LeanPool_Champernowne_Positions
-- name    : LeanPool_Champernowne_Positions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:35:11.460606+00:00
-- url     : https://prove2.me/theorems/db2846b3-e008-4378-bcc8-283ee5fcf687
-- title:
--   Positions
-- statement:
--   Definitions and structural lemmas for Positions, from Arthur Champernowne and LeanPool contributors's pinned Champernowne normality in every base development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Positions.lean

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Definitions.Def_LeanPool_Champernowne_Prefix
public import Mathlib.Algebra.BigOperators.Ring.Finset
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Champernowne
def champIndex (b n : ℕ) : ℕ :=
  Nat.findGreatest (fun N => (champBlocks b N).length ≤ n) n
end Champernowne


