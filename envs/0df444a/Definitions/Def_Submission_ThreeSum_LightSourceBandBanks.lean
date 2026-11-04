-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSourceBandBanks
-- name    : Submission_ThreeSum_LightSourceBandBanks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:08:50.75237+00:00
-- url     : https://prove2.me/theorems/9b2403cb-f2b3-4275-bb50-0acd752c145b
-- title:
--   Light Source Band Banks
-- statement:
--   Definitions and structural lemmas for Light Source Band Banks, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandBanks.lean

import Definitions.Def_Submission_ThreeSum_LightSourceBandBankBatch
import Definitions.Def_Submission_ThreeSum_SourceBandBankData
import Definitions.Def_Submission_ThreeSum_LightSourceOccurrenceArray
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightSourceBandBanks
open Light GlobalEncoding BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds SubsetAddress BlockSourceOccurrenceOrder SourceBandBankLayout SourceBandBankData
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
def afterCountBody (pRows pBanks : ℕ) : Stmt :=
  .set 19 (v 13 +' k 5) ;;
  .set 20 (v 19 +' v 18 *' v 17) ;;
  .call pRows [v 15,v 0,v 16,v 7,v 20] 21 ;;
  .store (v 13) (v 19) ;;
  .store (v 13 +' k 1) (v 18) ;;
  .store (v 13 +' k 2) (v 17) ;;
  .store (v 13 +' k 3) (v 20) ;;
  .store (v 13 +' k 4) (v 7) ;;
  .call pBanks [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,
    v 19,v 14,v 15,v 18,v 17] 21 ;;
  .set 0 (v 20)
def body (pRows pBanks : ℕ) : Stmt :=
  .set 18 (M (v 12 +' k 1)) ;;
  .ite (v 18 <' M (v 12 +' k 3)) (.set 18 (M (v 12 +' k 3))) .skip ;;
  afterCountBody pRows pBanks
def afterTime (NL NR g h J cut : ℕ) : ℕ :=
  LightSourceOccurrenceArray.time (LightBlockSourceCatalog.count h J) J+
    LightSourceBandBankBatch.time NL NR g h J cut+1000
def time (NL NR g h J cut : ℕ) : ℕ :=
  LightSourceOccurrenceArray.time (LightBlockSourceCatalog.count h J) J+
    LightSourceBandBankBatch.time NL NR g h J cut+1200
def space (base NL NR g h J cut : ℕ) : ℕ :=
  max (LightOutputDecodeDigits.space (finish base NL NR g h J cut) (LightBlockSourceCatalog.count h J))
    (span h J cut)
def word (NL NR h J : ℕ) : ℕ :=
  max (LightSourceBandBankStep.word NL NR h J)
    (LightOutputDecodeDigits.word (LightBlockSourceCatalog.count h J) (scheduleSize h) J)
structure Procs (P : Program) (pMain : ℕ) where
  pRows : ℕ
  pDigits : ℕ
  pDivide : ℕ
  pBanks : ℕ
  rows : P[pRows]?=some (LightSourceOccurrenceArray.body pDigits)
  digits : P[pDigits]?=some (LightOutputDecodeDigits.body pDivide)
  divide : P[pDivide]?=some LightOutputDecodeDivide.body
  banks : LightSourceBandBankBatch.Procs P pBanks
  main : P[pMain]?=some (body pRows pBanks)
variable {lim : Limits} {P : Program} {d : ℕ}
end ThreeSum.LightSourceBandBanks


