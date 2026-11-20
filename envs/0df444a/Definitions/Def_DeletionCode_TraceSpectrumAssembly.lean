-- Prove2me | Definitions.Def_DeletionCode_TraceSpectrumAssembly
-- name    : DeletionCode_TraceSpectrumAssembly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:46:30.76615+00:00
-- url     : https://prove2.me/theorems/db84daf9-0f87-4a6f-9b26-d01bb1ef3889
-- title:
--   Trace Spectrum Assembly
-- statement:
--   Definitions and structural lemmas for Trace Spectrum Assembly, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSpectrumAssembly.lean

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceMatchedSuffix
import Definitions.Def_DeletionCode_SpectrumPrefixChange
set_option autoImplicit true
namespace DeletionCode.TraceSpectrumAssembly
open AlignmentTrace FiniteConflictGraph TraceEditData SignedSupport
open SpectrumPrefixChange TraceMatchedSuffix
open scoped BigOperators
def hybrid (trace : Trace) (j : ℕ) : List Bool :=
  Trace.target (trace.take j) ++ Trace.source (trace.drop j)
end DeletionCode.TraceSpectrumAssembly


