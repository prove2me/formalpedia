-- Prove2me | Definitions.Def_DeletionCode_MaximalRuns
-- name    : DeletionCode_MaximalRuns
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:21:20.725566+00:00
-- url     : https://prove2.me/theorems/8086606e-6e1f-47eb-ac0e-d3b3ef59aaf5
-- title:
--   Maximal Runs
-- statement:
--   Definitions and structural lemmas for Maximal Runs, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/MaximalRuns.lean

import Definitions.Def_DeletionCode_UniqueRuns
import Definitions.Def_DeletionCode_SingleEditScripts
set_option autoImplicit true
namespace DeletionCode.MaximalRuns
open Windows CatalogueWords UniqueRuns
end DeletionCode.MaximalRuns


