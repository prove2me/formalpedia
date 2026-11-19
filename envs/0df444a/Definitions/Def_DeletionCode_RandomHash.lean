-- Prove2me | Definitions.Def_DeletionCode_RandomHash
-- name    : DeletionCode_RandomHash
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:35:59.161246+00:00
-- url     : https://prove2.me/theorems/c2d22217-3d8a-4a30-9994-9c272c66d8f5
-- title:
--   Random Hash
-- statement:
--   Definitions and structural lemmas for Random Hash, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
set_option autoImplicit true
namespace DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]
end DeletionCode.RandomHash


