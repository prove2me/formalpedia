-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryCountFrontend
-- name    : Submission_ThreeSum_LightTernaryCountFrontend
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:04:54.281685+00:00
-- url     : https://prove2.me/theorems/44b5d7d8-2c14-469a-9bff-d6bb5e61b143
-- title:
--   Light Ternary Count Frontend
-- statement:
--   Definitions and structural lemmas for Light Ternary Count Frontend, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCountFrontend.lean

import Definitions.Def_Submission_ThreeSum_LightTernaryGroupBankResources
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedRows
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightTernaryCountFrontend
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryBankStageModel
open ThreeSum.LightTernaryNearPair ThreeSum.LightTernaryWantedRowDispatch ThreeSum.LightTernaryPreparedState
set_option maxHeartbeats 8000000
set_option maxRecDepth 18000
def nearEntries : LightTernaryNearPair.Entries :=
  ⟨20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37⟩
def wantedEntries : LightTernaryWantedQuery.Entries :=⟨nearEntries,38,39,40⟩
def preparedEntries : LightTernaryPreparedWanted.Entries :=⟨wantedEntries,41,42,43,44,45,46⟩
def body : Stmt :=
  .call 51 [v 3,k 2 *' v 0 +' k 1,k 2] 60 ;;
  .call 19 [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11] 60 ;;
  .call 49 [v 12,v 13,v 14,v 15,v 16,v 17,v 18,v 19,v 20,v 21,v 22,v 23,v 24,v 25,v 26,v 27,v 28,
    v 29,v 30,v 31,v 32,v 33,v 34,v 35,v 36,v 37,v 38,v 39,v 40,v 41,v 42,v 43,v 44,v 45,v 46,v 47,v 48,v 49,v 50,v 51,v 52,v 53,v 54,v 55,v 56,v 57,v 58,v 59] 0
def tail : Program :=[
  LightTernaryNearSource.body 21 22 23,LightTernaryRankTable.body 29,
  LightTernaryEulerMetadata.body 24,LightTernaryEulerMemo.body 31,
  LightTernaryPredecessorTable.body 25 26,LightTernaryPredecessor.body 26 27 28 29 30,
  LightTernaryCodes.digitBody 28,LightTernaryCodes.zeroBody 28,LightMaskErase.body 28,
  LightTernaryRank.body 26,LightBandLookup.searchBody 30,LightTernaryEulerScan.body 32,
  LightTernaryEulerRow.fillBody 33,LightTernaryEulerRow.body 34 35,LightTernaryWeightedSum.body,
  LightTernaryDivide.body 36,LightOutputDecodeDivide.body,LightTernaryProduct.body,
  LightTernaryNearPair.body 20 37,
  LightTernaryFrozenQuery.body 39 40 26 27 28,LightTernaryQueryLookup.body 30,
  LightTernaryWantedQuery.body wantedEntries,
  LightTernaryNearSetup.body 43 44 45,powTableBody,LightTernaryNearDigits.body 26,
  LightTernaryNearEnumeration.body 46,LightTernaryNearEnumeration.branchBody 45,
  LightTernaryPreparedWanted.body preparedEntries,
  LightTernaryWantedRowDispatch.body 47,LightTernaryWantedRows.body 48,body,powTableBody]
def program : Program :=LightTernaryGroupedBanks.program++tail
def args {N : ℕ} (f g : Config) (Qstar : TritWord N)
    (bankPowers keyBase groups fsource gsource fbase gbase hbase out caps records count dst : ℕ) : List ℤ :=
  [(N : ℤ),f.bank,f.nb,bankPowers,f.L,keyBase,groups,fsource,gsource,fbase,gbase,hbase]++
    LightTernaryWantedRows.args f g Qstar out hbase caps records count dst fbase gbase hbase
      ((N+1)*f.nb) (N*f.nb)
def time (groups N L n count t : ℕ) : ℕ :=
  powTableTime (2*N+1)+LightTernaryGroupedBanks.time groups N L n+LightTernaryWantedRows.time count t+700
end ThreeSum.LightTernaryCountFrontend


