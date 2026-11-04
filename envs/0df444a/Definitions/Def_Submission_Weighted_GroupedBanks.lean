-- Prove2me | Definitions.Def_Submission_Weighted_GroupedBanks
-- name    : Submission_Weighted_GroupedBanks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:00:05.665788+00:00
-- url     : https://prove2.me/theorems/cf148cbc-91d3-414d-9bbb-de200639820c
-- title:
--   Grouped Banks
-- statement:
--   Definitions and structural lemmas for Grouped Banks, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GroupedBanks.lean

import Definitions.Def_Submission_Weighted_GroupBankStep
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightWeightedGroupedBanks
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.LightWeightedBankSweep
set_option maxHeartbeats 6000000
variable {lim : Limits}
def roundBody (pStep : ℕ) : Stmt :=
  .call pStep [v 0,v 1,v 2,v 3,v 4,v 5,
    v 7 +' v 12 *' v 2,v 8 +' v 12 *' v 2,
    v 9 +' v 12 *' ((v 0 +' k 1) *' v 2),
    v 10 +' v 12 *' ((v 0 +' k 1) *' v 2),
    v 11 +' v 12 *' ((v 0 +' k 1) *' v 2)] 13
def body (pStep : ℕ) : Stmt := .for 12 (v 6) (roundBody pStep)
def program : Program :=LightWeightedBankAssembly.program++
  [LightWeightedGroupBankStep.body 18,copyBody,body 17]
def time (groups N L n : ℕ) : ℕ :=groups*(LightWeightedGroupBankStep.time N L n+200)+100
def GroupStages {N T n : ℕ} (E : Enumeration N T n) (φ : ℕ→ℕ→TritWord N→ℤ)
    (base groups : ℕ) (μ : ℕ→ℤ) : Prop :=
  ∀ g<groups, Stages E (φ g) (base+g*((N+1)*n)) N μ
def Preserved (μ μ' : ℕ→ℤ) (keyBase n fbase gbase hbase N groups : ℕ) : Prop :=
  ∀ x, (x<keyBase ∨ keyBase+4*n≤x) →
    (x<fbase ∨ fbase+groups*((N+1)*n)≤x) →
    (x<gbase ∨ gbase+groups*((N+1)*n)≤x) →
    (x<hbase ∨ hbase+groups*((N+1)*n)≤x) → μ' x=μ x
def Inv {N T n : ℕ} (E : Enumeration N T n) (F G : ℕ→TritWord N→ℤ)
    (μ : ℕ→ℤ) (a powers L keyBase groups fsource gsource fbase gbase hbase : ℕ)
    (k : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ→ℤ),
    σ=⟨frame [N,a,n,powers,L,keyBase,groups,fsource,gsource,fbase,gbase,hbase,k,r],μ'⟩ ∧
    GroupStages E (fun g s => forwardStage s (F g)) fbase k μ' ∧
    GroupStages E (fun g s => forwardStage s (G g)) gbase k μ' ∧
    GroupStages E (fun g s => stageValue s (LightWeightedBankAssembly.product (F g) (G g))) hbase k μ' ∧
    Preserved μ μ' keyBase n fbase gbase hbase N groups ∧ Powers μ' powers (2*N)
end ThreeSum.LightWeightedGroupedBanks


