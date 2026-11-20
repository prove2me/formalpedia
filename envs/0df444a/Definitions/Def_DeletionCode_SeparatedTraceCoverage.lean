-- Prove2me | Definitions.Def_DeletionCode_SeparatedTraceCoverage
-- name    : DeletionCode_SeparatedTraceCoverage
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:57:21.805342+00:00
-- url     : https://prove2.me/theorems/6d567bd2-a40b-4ee9-930c-0ddf81c038f4
-- title:
--   Separated Trace Coverage
-- statement:
--   Definitions and structural lemmas for Separated Trace Coverage, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SeparatedTraceCoverage.lean

import Definitions.Def_DeletionCode_TraceBubbleFamily
import Definitions.Def_DeletionCode_BubbleCatalogue
import Definitions.Def_DeletionCode_LocalBubbleDisjoint
import Definitions.Def_DeletionCode_TraceSpectrumAssembly
set_option autoImplicit true
namespace DeletionCode.SeparatedTraceCoverage
open Windows HeaderRecovery CatalogueWords AlignmentTrace FiniteConflictGraph
open SignedSupport RunBubbleConstruction TraceEditData TraceBubbleFamily
open scoped BigOperators
end DeletionCode.SeparatedTraceCoverage


