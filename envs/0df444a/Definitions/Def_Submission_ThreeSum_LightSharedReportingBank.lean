-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSharedReportingBank
-- name    : Submission_ThreeSum_LightSharedReportingBank
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:38:06.679236+00:00
-- url     : https://prove2.me/theorems/c669ca3e-0e9a-49fa-ab37-87681ee5b905
-- title:
--   Light Shared Reporting Bank
-- statement:
--   Definitions and structural lemmas for Light Shared Reporting Bank, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSharedReportingBank.lean

import Definitions.Def_Submission_ThreeSum_LightSharedReportingPair
import Definitions.Def_Submission_ThreeSum_SharedReportingBankRows
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightSharedReportingBank
open Light GlobalEncoding SharedReportingBankLayout SharedReportingBankLevels
open SharedReportingBankRows
set_option maxHeartbeats 3800000
set_option maxRecDepth 16000
def body (pPair : ℕ) : Stmt :=
  .set 17 (v 5 *' v 6 *' v 7) ;;
  .set 12 (k 0) ;;
  .set 13 (k 0) ;;
  .set 14 (k 0) ;;
  .set 15 (v 10) ;;
  .set 16 (v 11) ;;
  .for 18 (v 17) (
    .call pPair [v 0,v 1,v 2,v 3,v 4,v 12,v 13,v 14,v 8,v 9,v 15,v 16] 16 ;;
    .set 16 (v 16) ;;
    .set 15 (v 15 +' k 5 *' v 2) ;;
    .ite (v 14 +' k 1 <' v 7)
      (.set 14 (v 14 +' k 1))
      (.set 14 (k 0) ;;
        .ite (v 13 +' k 1 <' v 6)
          (.set 13 (v 13 +' k 1))
          (.set 13 (k 0) ;; .set 12 (v 12 +' k 1)))) ;;
  .set 0 (v 16)
def time (h J K NB NC g : ℕ) : ℕ :=
  total h J NB NC g*(LightSharedReportingPair.time h J K+1000)+300
def controlWord (h J K NB NC g : ℕ) : ℕ :=
  LightBlockSourceCatalog.count h J*BandPartition.size NB g+
  LightBlockSourceCatalog.count h J+BandPartition.size NB g+BandPartition.size NC g+J+K+512
def program : Program := LightSharedReportingPair.program ++ [body 65]
def Inv (μ : ℕ → ℤ) (fB fC : ℕ → ℤ) (p shift : ℤ)
    (header record base h J K NB NC g q : ℕ) (σ : State) : Prop :=
  ∃ (s i j : ℕ) (ν : ℕ → ℤ),
    σ=⟨frame [h,J,K,SourceBandBankData.first header,SourceBandBankLayout.span h J (2*h*J),
      LightBlockSourceCatalog.count h J,BandPartition.size NB g,BandPartition.size NC g,
      localChoose h,localPairs h,record,base,s,i,j,rowRecord record K q,rowBase base h J K q,
      total h J NB NC g,q],ν⟩ ∧
    q=rank (BandPartition.size NB g) (BandPartition.size NC g) s i j ∧
    s ≤ LightBlockSourceCatalog.count h J ∧ i ≤ BandPartition.size NB g ∧ j ≤ BandPartition.size NC g ∧
    (0 < total h J NB NC g → i < BandPartition.size NB g ∧ j < BandPartition.size NC g) ∧
    Done ν record base h J K NB NC g q fB fC p shift ∧ Kept μ ν record ∧
    KeptBut μ ν base record (5*K*total h J NB NC g)
end ThreeSum.LightSharedReportingBank


