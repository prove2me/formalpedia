-- Prove2me | Definitions.Def_Submission_ThreeSum_SharedReportingBankRows
-- name    : Submission_ThreeSum_SharedReportingBankRows
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:18:53.464224+00:00
-- url     : https://prove2.me/theorems/1ccf3ad0-0a36-413d-81de-7fa4c52a4577
-- title:
--   Shared Reporting Bank Rows
-- statement:
--   Definitions and structural lemmas for Shared Reporting Bank Rows, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankRows.lean

import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSourceBounds
set_option autoImplicit false
namespace ThreeSum.SharedReportingBankRows
open Light GlobalEncoding BlockIndexedQuery BlockSourceOccurrenceOrder
open SharedReportingBankData SharedReportingBankLayout SharedReportingBankLevels
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData
set_option maxHeartbeats 1800000
def pairs (S nb nc : ℕ) : ℕ := S*nb*nc
def rank (nb nc s i j : ℕ) : ℕ := (s*nb+i)*nc+j
def total (h J NB NC g : ℕ) : ℕ :=
  pairs (LightBlockSourceCatalog.count h J) (BandPartition.size NB g) (BandPartition.size NC g)
def rowRecord (record K q : ℕ) : ℕ := record+5*K*q
def rowBase (base h J K q : ℕ) : ℕ := base+q*offset h J K
def Done (μ : ℕ → ℤ) (record base h J K NB NC g processed : ℕ)
    (fB fC : ℕ → ℤ) (p shift : ℤ) : Prop :=
  ∀ s < LightBlockSourceCatalog.count h J, ∀ i < BandPartition.size NB g,
    ∀ j < BandPartition.size NC g,
    rank (BandPartition.size NB g) (BandPartition.size NC g) s i j < processed →
    Built μ (rowRecord record K (rank (BandPartition.size NB g) (BandPartition.size NC g) s i j))
      (rowBase base h J K (rank (BandPartition.size NB g) (BandPartition.size NC g) s i j)) h J K
      (leftSource p (SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val) (representative h J s))
      (rightSource p shift (SourceBandPartition.source NC g j) (fun t : Fin NC => fC t.val) (representative h J s))
end ThreeSum.SharedReportingBankRows


