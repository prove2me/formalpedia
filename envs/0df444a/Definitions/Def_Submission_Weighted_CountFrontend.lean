-- Prove2me | Definitions.Def_Submission_Weighted_CountFrontend
-- name    : Submission_Weighted_CountFrontend
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:06:41.817443+00:00
-- url     : https://prove2.me/theorems/f62abdf1-a85d-4cd8-a4c6-15a8df3a4e25
-- title:
--   Count Frontend
-- statement:
--   Definitions and structural lemmas for Count Frontend, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/CountFrontend.lean

import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_Weighted_GroupBankResources
import Definitions.Def_Submission_Weighted_WantedRows
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightWeightedCountFrontend
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.WeightedBankStageModel
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedWantedRowDispatch ThreeSum.LightWeightedPreparedState
set_option maxHeartbeats 8000000
set_option maxRecDepth 18000
def nearEntries : LightWeightedNearPair.Entries :=
  ⟨20,21,22,23,25,28,27,31,30,24,33,26,29,34,35,36,37,55,32⟩
def wantedEntries : LightWeightedWantedQuery.Entries :=⟨nearEntries,58,53,54⟩
def preparedEntries : LightWeightedPreparedWanted.Entries :=⟨wantedEntries,59,57,50,56,51,52⟩
def body : Stmt :=
  .call 50 [v 3,k 2 *' v 0 +' k 1,k 2] 60 ;;
  .call 19 [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11] 60 ;;
  .call 62 [v 12,v 13,v 14,v 15,v 16,v 17,v 18,v 19,v 20,v 21,v 22,v 23,v 24,v 25,v 26,v 27,v 28,
    v 29,v 30,v 31,v 32,v 33,v 34,v 35,v 36,v 37,v 38,v 39,v 40,v 41,v 42,v 43,v 44,v 45,v 46,v 47,v 48,v 49,v 50,v 51,v 52,v 53,v 54,v 55,v 56,v 57,v 58,v 59] 0
def tail : Program :=
  LightWeightedPreparedWanted.program.map (ReportingHostRelocation.relocate 20)++
    [LightWeightedWantedRowDispatch.body 60,LightWeightedWantedRows.body 61,body]
def program : Program :=LightWeightedGroupedBanks.program++tail
def args {N : ℕ} (f g : Config) (Qstar : TritWord N)
    (bankPowers keyBase groups fsource gsource fbase gbase hbase out caps records count dst : ℕ) : List ℤ :=
  [(N : ℤ),f.bank,f.nb,bankPowers,f.L,keyBase,groups,fsource,gsource,fbase,gbase,hbase]++
    LightWeightedWantedRows.args f g Qstar out hbase caps records count dst fbase gbase hbase
      ((N+1)*f.nb) (N*f.nb)
def time (groups N L n count t : ℕ) : ℕ :=
  powTableTime (2*N+1)+LightWeightedGroupedBanks.time groups N L n+LightWeightedWantedRows.time count t+700
end ThreeSum.LightWeightedCountFrontend


