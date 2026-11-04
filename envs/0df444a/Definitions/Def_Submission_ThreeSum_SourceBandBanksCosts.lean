-- Prove2me | Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
-- name    : Submission_ThreeSum_SourceBandBanksCosts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:18:50.297879+00:00
-- url     : https://prove2.me/theorems/ff6c78f3-229f-4440-bbbe-4dcd135e4003
-- title:
--   Source Band Banks Costs
-- statement:
--   Definitions and structural lemmas for Source Band Banks Costs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBanksCosts.lean

import Definitions.Def_Submission_ThreeSum_LightSourceBandBanksProgram
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
set_option autoImplicit false
namespace ThreeSum.SourceBandBanksCosts
open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress
def familyCount (NL NR g h J : ℕ) : ℕ :=
  2*SourceBandPairSlices.count NL NR g*LightBlockSourceCatalog.count h J
def stageCells (NL NR g h J cut : ℕ) : ℕ :=
  familyCount NL NR g h J*LightBlockSourceBatchLayout.family (J*(512*h)) cut
def storageFactor (n : ℕ) : ℕ :=
  (blockCount (inputBits n)+2*(256*mu n)+7)*(256*mu n+2)+mu n+256*mu n+3+
    LightBlockSourceRetainedHost.space 0 (microHalf (inputBits n)) (blockCount (inputBits n))
end ThreeSum.SourceBandBanksCosts


