-- Prove2me | Definitions.Def_DeletionCode_ExceptionalPartnerCount
-- name    : DeletionCode_ExceptionalPartnerCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:54:46.247225+00:00
-- url     : https://prove2.me/theorems/58bb5954-0f92-4ecf-9523-31f14f6521e9
-- title:
--   Exceptional Partner Count
-- statement:
--   Definitions and structural lemmas for Exceptional Partner Count, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalPartnerCount.lean

import Definitions.Def_DeletionCode_AnchorRecords
import Definitions.Def_DeletionCode_TaggedAnchorCount
import Definitions.Def_DeletionCode_ExceptionalProbability
import Definitions.Def_DeletionCode_ExceptionalCountArithmetic
set_option autoImplicit true
namespace DeletionCode.ExceptionalPartnerCount
open HeaderRecovery TaggedAnchorCount AlignmentTrace FiniteConflictGraph TraceEditData
open ExceptionalProbability ExceptionalCountArithmetic
open scoped BigOperators
def decodeWord {n r : ℕ} (x : Bits n) (record : Record n r) : Bits n :=
  fun i => (AnchorRecords.decode (List.ofFn x) (packets record)).getD i.val false
noncomputable def shortPartners {n : ℕ} (t : ℕ) (x : Bits n) : Finset (Bits n) := by
  classical
  exact (Finset.range t).biUnion fun d =>
    (Finset.univ : Finset (Record n (2 * d))).image (decodeWord x)
noncomputable def fullPartners {n : ℕ} (t k : ℕ) (x : Bits n) : Finset (Bits n) := by
  classical
  exact ((Finset.univ : Finset (Record n (2 * t))).filter
    (Bad (n - t) (4 * windowLength k))).image (decodeWord x)
end DeletionCode.ExceptionalPartnerCount


