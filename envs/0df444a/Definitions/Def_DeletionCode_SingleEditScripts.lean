-- Prove2me | Definitions.Def_DeletionCode_SingleEditScripts
-- name    : DeletionCode_SingleEditScripts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:19:12.851203+00:00
-- url     : https://prove2.me/theorems/a0b6847c-1aeb-420f-98ff-d52d9fb9f412
-- title:
--   Single Edit Scripts
-- statement:
--   Definitions and structural lemmas for Single Edit Scripts, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditScripts.lean

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_SingleEditOrigins
import Definitions.Def_DeletionCode_CatalogueWords
set_option autoImplicit true
namespace DeletionCode.EditAlignment
end DeletionCode.EditAlignment
namespace DeletionCode.SingleEditScripts
open Windows CatalogueWords EditAlignment SingleEditOrigins
end DeletionCode.SingleEditScripts


