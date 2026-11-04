-- Prove2me | Definitions.Def_Submission_ThreeSum_SourceBandData
-- name    : Submission_ThreeSum_SourceBandData
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:53:13.030219+00:00
-- url     : https://prove2.me/theorems/867f7dae-3f34-4c41-a38d-adc21d6aef47
-- title:
--   Source Band Data
-- statement:
--   Definitions and structural lemmas for Source Band Data, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandData.lean

import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedStages
set_option autoImplicit false
namespace ThreeSum.SourceBandData
open Light BandPartition SourceBandLayout
structure At (μ : ℕ → ℤ) (f : ℕ → ℤ) (base n g p m : ℕ) (shift : ℤ) (i : ℕ) : Prop where
  headStart : μ (base+6*i) = (start g i : ℤ)
  headLength : μ (base+6*i+1) = (len n g i : ℤ)
  headCodes : μ (base+6*i+2) = (codes base n g m i : ℤ)
  headHist : μ (base+6*i+3) = (hist base n g m i : ℤ)
  headOffsets : μ (base+6*i+4) = (offsets base n g m i : ℤ)
  headFlat : μ (base+6*i+5) = (flat base n g m i : ℤ)
  codesRead : ∀ j < len n g i, μ (codes base n g m i+j) = (key f g p m shift i j : ℤ)
  histRead : ∀ r < m, μ (hist base n g m i+r) = (LightHistogram.count (key f g p m shift i) r (len n g i) : ℤ)
  buckets : SourceBuckets.Stored μ (key f g p m shift i) (len n g i) m
    (offsets base n g m i) (flat base n g m i)
def positions (μ : ℕ → ℤ) (base n g m i r : ℕ) : List ℕ :=
  (SourceBucketView.indices μ (offsets base n g m i) (flat base n g m i) r).map (fun j => start g i+j)
end ThreeSum.SourceBandData


