-- Prove2me | Definitions.Def_Submission_ThreeSum_SharedReportingBankSources
-- name    : Submission_ThreeSum_SharedReportingBankSources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:03:42.980689+00:00
-- url     : https://prove2.me/theorems/d03b775b-91c7-4f97-a9d3-95aa218fee4a
-- title:
--   Shared Reporting Bank Sources
-- statement:
--   Definitions and structural lemmas for Shared Reporting Bank Sources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankSources.lean

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_SourceBandBankData
set_option autoImplicit false
namespace ThreeSum.SharedReportingBankSources
open Light GlobalEncoding BlockEncoding BlockIndexedQuery SharedReportingBankData
open BlockSourceOccurrenceOrder BlockSourceSharing OutputDecodeRecords
def bankBase (base h J cut band : ℕ) : ℕ :=
  SourceBandBankLayout.baseAt (SourceBandBankData.first base) h J cut band
def leftCell (base h J cut band occurrence : ℕ) : ℕ := bankBase base h J cut band+2*occurrence
def rightCell (base h J cut band occurrence : ℕ) : ℕ := bankBase base h J cut band+2*occurrence+1
def leftBase (base h J cut band occurrence : ℕ) : ℕ :=
  LightBlockSourceBatchLayout.leftBase (bankBase base h J cut band)
    (LightBlockSourceCatalog.count h J) (J*(512*h)) cut occurrence
def rightBase (base h J cut band occurrence : ℕ) : ℕ :=
  LightBlockSourceBatchLayout.rightBase (bankBase base h J cut band)
    (LightBlockSourceCatalog.count h J) (J*(512*h)) cut occurrence
end ThreeSum.SharedReportingBankSources


