-- Prove2me | Definitions.Def_Submission_ThreeSum_LightExtensionBackend
-- name    : Submission_ThreeSum_LightExtensionBackend
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:49:47.491629+00:00
-- url     : https://prove2.me/theorems/24049b13-6946-4613-b76f-b54deaf9bcda
-- title:
--   Light Extension Backend
-- statement:
--   Definitions and structural lemmas for Light Extension Backend, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionBackend.lean

import Definitions.Def_Submission_ThreeSum_LightIrreducibleFinder
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuMatrix
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuSemantics
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_monicCandidate_monic

set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightExtensionBackend
open Light TernaryExtensionEncoding
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
noncomputable local instance _p2m_local_instance_a49b488cb7_11 (Q : Prop) : Decidable Q := Classical.propDecidable Q
def quotientLayout (F : LightExtensionFactorPredicate.Layout) (a b h r prod sum : ℕ) :
    LightExtensionQuotientPredicate.Layout where
  p := F.p
  dim := F.dim
  powers := F.powers
  a := a
  b := b
  modulus := F.target
  h := h
  remainder := r
  productWork := prod
  sumWork := sum
def body : Stmt :=
  .call 35 [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7] 19 ;;
  .call 36 [v 8,v 0,v 1,v 3,v 12,v 13,v 4,v 14,v 15,v 16,v 17] 20 ;;
  .call 19 [v 2,v 8,v 0,v 1,v 3,v 12,v 13,v 9,v 10,v 11,v 18] 20 ;;
  .set 0 (v 19)
def prefixProgram : Program := ReportingHostRelocation.program LightExtensionMenuMatrix.program LightIrreducibleFinder.program
def program : Program := prefixProgram++[LightArgumentTable.stores 0 10,body]
structure Budget (lim : Limits) (F : LightExtensionFactorPredicate.Layout)
    (q fctx ctx table logical physical J a b h r prod sum T : ℕ) : Prop where
  finder : LightIrreducibleFinder.Budget lim F q fctx T
  targetCtx : F.target+2*F.dim ≤ ctx
  ctxTable : ctx+10 ≤ table
  tableLogical : table+q*q ≤ logical
  logicalPhysical : logical+q*q*(J+2) ≤ physical
  physicalA : physical+q*q*(J+2) ≤ a
  aB : a+F.dim ≤ b
  bH : b+F.dim ≤ h
  hR : h+F.dim ≤ r
  rProduct : r+2*F.dim ≤ prod
  productSum : prod+2*F.dim ≤ sum
  space : sum+2*F.dim ≤ lim.space
  tableWord : (LightExtensionMultiplyTable.word q ctx F.p F.dim F.powers a b : ℤ) ≤ lim.word
  cellWord : (LightExtensionMultiplyCell.word (quotientLayout F a b h r prod sum) q ctx : ℤ) ≤ lim.word
  seedWord : (LightExtensionSeedMatrix.word (J+2) q F.p : ℤ) ≤ lim.word
def time (F : LightExtensionFactorPredicate.Layout) (q J a b h r prod sum T : ℕ) : ℕ :=
  LightIrreducibleFinder.setupTime F q T+
  LightExtensionMenuMatrix.time (quotientLayout F a b h r prod sum) q J+1000
def modulusMonic (F : LightExtensionFactorPredicate.Layout) [Fact F.p.Prime] (c : ℕ) :
    (monicOfCode (p := F.p) F.dim c).Monic := monicCandidate_monic _
variable {lim : Limits}
end ThreeSum.LightExtensionBackend


