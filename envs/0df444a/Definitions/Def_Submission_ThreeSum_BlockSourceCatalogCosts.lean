-- Prove2me | Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
-- name    : Submission_ThreeSum_BlockSourceCatalogCosts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:52:43.81902+00:00
-- url     : https://prove2.me/theorems/def406ce-2150-481f-868f-4c30150a107a
-- title:
--   Block Source Catalog Costs
-- statement:
--   Definitions and structural lemmas for Block Source Catalog Costs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceCatalogCosts.lean

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalogProgram
import Definitions.Def_Submission_ThreeSum_BlockSourceStageCosts
set_option autoImplicit false
namespace ThreeSum.BlockSourceCatalogCosts
open Scales TrimScales StageBounds CostLedger BlockSourceSharing SubsetAddress
open LightBlockSourceBatchLayout
def stageFamilyCount (n : ℕ) : ℕ :=
  2*bandCount n*LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n))
def stageCellCount (n : ℕ) : ℕ :=
  stageFamilyCount n*family (256*mu n) (mu n)
def work (n : ℕ) : ℕ := bandCount n*LightBlockSourceCatalog.time
  (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n)
def catalogCells (n : ℕ) : ℕ :=
  bandCount n*scheduleCount n*(blockCount (inputBits n)+stride (256*mu n) (mu n)+2)
end ThreeSum.BlockSourceCatalogCosts


