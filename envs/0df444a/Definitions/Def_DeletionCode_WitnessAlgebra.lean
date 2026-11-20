-- Prove2me | Definitions.Def_DeletionCode_WitnessAlgebra
-- name    : DeletionCode_WitnessAlgebra
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:08:01.734932+00:00
-- url     : https://prove2.me/theorems/1b008061-0bdc-42c3-b702-651068205070
-- title:
--   Witness Algebra
-- statement:
--   Definitions and structural lemmas for Witness Algebra, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessAlgebra.lean

import Definitions.Def_DeletionCode_GeneratingBlocks
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Basic
set_option autoImplicit true
namespace DeletionCode.WitnessAlgebra
open scoped BigOperators
def BooleanVector {H : Type*} (v : H → ℚ) : Prop := ∀ h, v h = 0 ∨ v h = 1
def SignedUnitVector {H : Type*} (v : H → ℚ) : Prop :=
  ∀ h, v h = -1 ∨ v h = 0 ∨ v h = 1
end DeletionCode.WitnessAlgebra


