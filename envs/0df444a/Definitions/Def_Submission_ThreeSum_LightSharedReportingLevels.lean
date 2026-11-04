-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSharedReportingLevels
-- name    : Submission_ThreeSum_LightSharedReportingLevels
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:20:09.990012+00:00
-- url     : https://prove2.me/theorems/5ac3a859-686b-40ee-9a2c-a907f67b7dbf
-- title:
--   Light Shared Reporting Levels
-- statement:
--   Definitions and structural lemmas for Light Shared Reporting Levels, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSharedReportingLevels.lean

import Definitions.Def_Submission_ThreeSum_LightSharedReportingCell
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
import Definitions.Def_Submission_ThreeSum_LightSharedReportingLoop
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightSharedReportingLevels
open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData SharedReportingBankLevels
set_option maxHeartbeats 3000000
set_option maxRecDepth 14000
def body (pSwitch pCell : ℕ) : Stmt :=
  .set 9 (k 1) ;;
  .set 10 (k 2) ;;
  .set 11 (v 8) ;;
  .for 12 (v 2) (
    .set 13 (k 2 *' v 0 *' (v 1 -' v 12)) ;;
    .call pSwitch [v 1,v 12,v 13] 14 ;;
    .set 15 (v 13 -' v 14) ;;
    .call pCell [v 0,v 1,v 12,v 3,v 4,v 14,v 15,v 5,v 6,v 9,v 10,
      v 7 +' k 5 *' v 12,v 11] 11 ;;
    .set 9 (v 9 *' v 6) ;;
    .set 10 (v 10 +' k 1 +' v 9)) ;;
  .set 0 (v 11)
def roundTime (h J i : ℕ) : ℕ :=
  LightSwitch.time (residual h J i)+LightSharedReportingCell.time h J i (boxCut h J i)+800
def time (h J K : ℕ) : ℕ := (∑ i ∈ Finset.range K, (roundTime h J i+8))+100
def program : Program :=
  ReportingHostRelocation.program LightSharedReportingCell.program LightSwitch.program ++ [body 63 62]
structure Resources (lim : Limits) (base h J K B D d : ℕ) : Prop where
  state : ((J+K+512+prefixSpan h K+count h K : ℕ) : ℤ) ≤ lim.word
  space : baseAt base h J K ≤ lim.space
  powers : ((2^(512*h+1) : ℕ) : ℤ) ≤ lim.word
  keys : ∀ i < K, (LightRadixKeys.word (2^(512*h)) (2^(512*h)) i : ℤ) ≤ lim.word
  width : (((J*(512*h)+1)*2^(J*(512*h)+1) : ℕ) : ℤ) ≤ lim.word
  index : ∀ i < K, (LightReportingSortedCatalog.word (J*(512*h)) (count h i) : ℤ) ≤ lim.word
  values : ∀ i < K, (((2^((J-i)*(512*h))*
    ((2^((J-i)*(512*h))*B)*(2^((J-i)*(512*h))*D))) : ℕ) : ℤ) ≤ lim.word
  switch : ∀ i < K, (LightSwitch.word J (residual h J i) : ℤ) ≤ lim.word
  pairDepth : d+512*h+K+8 ≤ lim.depth
  widthDepth : d+J*(512*h)+18 ≤ lim.depth
  sortDepth : ∀ i < K, d+Nat.clog 2 (count h i)+6 ≤ lim.depth
def Inv (μ : ℕ → ℤ) (record base h J K cellL cellR i : ℕ)
    (f g : Finset (Fin (J*(512*h))) → ℤ) (σ : State) : Prop :=
  ∃ (r t cut : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [h,J,K,cellL,cellR,localChoose h,localPairs h,record,base,
      count h i,prefixSpan h i,baseAt base h J i,i,r,t,cut],ν⟩ ∧
    Built ν record base h J i f g ∧ Kept μ ν record ∧ KeptBut μ ν base record (5*K)
end ThreeSum.LightSharedReportingLevels


