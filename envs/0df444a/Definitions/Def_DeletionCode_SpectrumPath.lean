-- Prove2me | Definitions.Def_DeletionCode_SpectrumPath
-- name    : DeletionCode_SpectrumPath
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:10:51.48806+00:00
-- url     : https://prove2.me/theorems/7e52a2f7-69d4-4356-b3d0-988cbac85d1e
-- title:
--   Spectrum Path
-- statement:
--   Definitions and structural lemmas for Spectrum Path, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPath.lean

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_WordPaths
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset
set_option autoImplicit true
namespace DeletionCode.SpectrumPath
open Windows SignedSupport
open scoped BigOperators
def vertexAt (word : Letters) (L offset : ℕ) : SupportComponents.Vertex L :=
  fun i => word (offset + i.val)
end DeletionCode.SpectrumPath


