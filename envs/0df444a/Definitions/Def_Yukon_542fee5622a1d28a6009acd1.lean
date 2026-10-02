-- Prove2me | Definitions.Def_Yukon_542fee5622a1d28a6009acd1
-- name    : Yukon_542fee5622a1d28a6009acd1
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T05:09:03.083188+00:00
-- url     : https://prove2.me/theorems/08bda5ba-790d-468a-a018-a7f180f30377
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberDataTypes6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberDataTypes6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberDataTypes6814.lean
--
--   yukon-proof-operation:foundation-direct-5e3ece50f39622132b3ad60c885d8d003dc26525a5918117506a0cf0a6df9076
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNzU5NTU0M2I0OTI3ZDcyZDAxYmUxMjg4MGJkYjhmMzAwMzA3NjRjNzRmMGU2ODZjYzQ0ZTVjMGU5MmNkZGY2NSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTVlM2VjZTUwZjM5NjIyMTMyYjNhZDYwYzg4NWQ4ZDAwM2RjMjY1MjVhNTkxODExNzUwNmEwY2YwYTZkZjkwNzYiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl81NDJmZWU1NjIyYTFkMjhhNjAwOWFjZDEiLCJ2IjoyfQ]

import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561







































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! The row data types of the moving-fiber receipts.

They live apart from the checkers so that the generated row tables
(`MovingFiberContextData6814R*`) import `LowerGeometry` only and elaborate while the checker
modules build, instead of after them. Names and namespaces are those of the modules that
use them. -/

namespace ProximityPrize.SubmissionLower.MovingFiberSingleCore6814
set_option autoImplicit false

structure Carrier where
  c0 : ℕ
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  c4 : ℕ
  deriving DecidableEq, Repr

structure Run where
  stop : ℕ
  who : ℕ
  deriving DecidableEq, Repr

end ProximityPrize.SubmissionLower.MovingFiberSingleCore6814

namespace ProximityPrize.SubmissionLower.Lower80889.PhaseRows
set_option autoImplicit false

structure PhaseRun where
  stop : ℕ
  witness : ℕ
  deriving DecidableEq, Repr

end ProximityPrize.SubmissionLower.Lower80889.PhaseRows

namespace ProximityPrize.SubmissionLower.Lower80889.LedgerAudit
set_option autoImplicit false

structure LedgerRun where
  stop : ℕ
  witness : ℕ
  mode : ℕ
  deriving DecidableEq, Repr

end ProximityPrize.SubmissionLower.Lower80889.LedgerAudit

namespace ProximityPrize.SubmissionLower.Lower80889.CompressedBand
set_option autoImplicit false

structure Run where
  stop : ℕ
  code : ℕ
  deriving DecidableEq, Repr

end ProximityPrize.SubmissionLower.Lower80889.CompressedBand

namespace ProximityPrize.SubmissionLower.MovingFiberReceiptTypes6814
open LocatorPhase6800Oracle Lower80889.PhaseRows
set_option autoImplicit false

structure BaseRun where
  stop : Nat
  sheet : Nat
  deriving DecidableEq, Repr

structure Numbers where
  carrier : MovingFiberSingleCore6814.Carrier
  base : BaseRow
  threshold : Array Nat
  prefixValues : Array Nat
  singletons : List MovingFiberSingleCore6814.Run
  baseChoices : List BaseRun
  phaseRuns : Array (List PhaseRun)
  ledgerRuns : List Lower80889.LedgerAudit.LedgerRun
  thresholdRuns : Array (List Lower80889.CompressedBand.Run)

def defaults : Numbers := ⟨⟨0,0,0,0,0⟩,⟨0,0,0,0,0,[]⟩,#[],#[],[],[],#[],[],#[]⟩

end ProximityPrize.SubmissionLower.MovingFiberReceiptTypes6814


