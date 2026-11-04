-- Prove2me | Definitions.Def_Submission_ThreeSum_SourceBandBankLayout
-- name    : Submission_ThreeSum_SourceBandBankLayout
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:56:17.366321+00:00
-- url     : https://prove2.me/theorems/0531aeab-10c0-47ed-96f7-37137ac81ed6
-- title:
--   Source Band Bank Layout
-- statement:
--   Definitions and structural lemmas for Source Band Bank Layout, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBankLayout.lean

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalog
import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
set_option autoImplicit false
namespace ThreeSum.SourceBandBankLayout
open Light LightBlockSourceBatchLayout GlobalEncoding BlockSourceOccurrenceOrder
def span (h J cut : ℕ) : ℕ :=
  LightBlockSourceRetainedHost.space
    (work 0 (LightBlockSourceCatalog.count h J) (J*(512*h)) cut) h J
def baseAt (base h J cut i : ℕ) : ℕ := base+i*span h J cut
def At (μ : ℕ → ℤ) (fL fR : ℕ → ℤ) (base NL NR g h J cut : ℕ) (p shift : ℤ) (i : ℕ) : Prop :=
  LightBlockSourceCatalog.Stored μ h J (baseAt base h J cut i) cut p shift
    (SourceBandPartition.source NL g i) (fun t : Fin NL => fL t.val)
    (SourceBandPartition.source NR g i) (fun t : Fin NR => fR t.val)
end ThreeSum.SourceBandBankLayout


