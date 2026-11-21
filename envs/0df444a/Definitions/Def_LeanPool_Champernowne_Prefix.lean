-- Prove2me | Definitions.Def_LeanPool_Champernowne_Prefix
-- name    : LeanPool_Champernowne_Prefix
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:34:32.408549+00:00
-- url     : https://prove2.me/theorems/a1d4646d-d74b-4014-ba97-93ebb94fb586
-- title:
--   Prefix
-- statement:
--   Definitions and structural lemmas for Prefix, from Arthur Champernowne and LeanPool contributors's pinned Champernowne normality in every base development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Prefix.lean

module
public import Definitions.Def_LeanPool_Champernowne_Defs
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Champernowne
def champPrefix (b n : ℕ) : List ℕ := (champBlocks b n).take n
end Champernowne


