-- Prove2me | Definitions.Def_Submission_ThreeSum_LightLocalCoverTables
-- name    : Submission_ThreeSum_LightLocalCoverTables
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:56:25.01511+00:00
-- url     : https://prove2.me/theorems/89ac2bca-4d8c-436b-b39d-c0e4edb8222a
-- title:
--   Light Local Cover Tables
-- statement:
--   Definitions and structural lemmas for Light Local Cover Tables, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverTables.lean

import Definitions.Def_Submission_ThreeSum_LightLocalCoverMatrix
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
set_option autoImplicit false
namespace ThreeSum.LightLocalCoverTables
open Light LocalHashMoments LocalCoverBounds GlobalEncoding LightLocalCoverSchedule
def Data (μ : ℕ → ℤ) (h maps hist0 hist1 matrixPtr : ℕ) : Prop :=
  LightLocalCoverMatrix.Tables μ (512*h) (LocalMaskGraph.vertexCount (512*h) h)
    (localPrime h) (localBucketCap h) maps hist0 hist1 matrixPtr
    (LocalMaskGraph.maskAt (512*h) h) (LocalCoverMatrix.bits (512*h) h)
    (fun j => LocalMaskHashes.coeff false (candidate h j))
    (fun j => LocalMaskHashes.coeff true (candidate h j)) (rows h)
def ScheduleRows (μ : ℕ → ℤ) (h dst : ℕ) : Prop :=
  ∀ s < scheduleSize h, ∀ i < 512*h,
    μ (dst+s*(2*(512*h))+i) = (BlockCoefficientRows.mapRow h false s i : ℤ) ∧
    μ (dst+s*(2*(512*h))+512*h+i) = (BlockCoefficientRows.mapRow h true s i : ℤ)
end ThreeSum.LightLocalCoverTables


