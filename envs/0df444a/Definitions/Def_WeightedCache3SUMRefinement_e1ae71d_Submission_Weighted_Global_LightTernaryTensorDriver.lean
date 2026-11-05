-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorDriver
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorDriver
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:40:14.42742+00:00
-- url     : https://prove2.me/theorems/b455f2be-c935-4d1d-92f6-5726c935ae76
-- title:
--   LightTernaryTensorDriver
-- statement:
--   Definitions and structural lemmas for LightTernaryTensorDriver, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryTensorDriver.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryQuarticStep
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.LightWeightedGlobalTensorDriver
open Light
def channelLibraries (xl yl zl xr yr zr : List ℤ) : Program :=
  ReportingHostRelocation.program (LightWeightedSourceCountHost.program xl yl zl xr yr zr)
    LightTernaryTaggedChannel.program
def quadLibraries (xl yl zl xr yr zr : List ℤ) : Program :=
  ReportingHostRelocation.program (channelLibraries xl yl zl xr yr zr) LightWeightRow.program
def potentialLibraries (xl yl zl xr yr zr : List ℤ) (K : ℕ) : Program :=
  ReportingHostRelocation.program (quadLibraries xl yl zl xr yr zr)
    (LightTernaryPairedPotential.program K)
def program (xl yl zl xr yr zr : List ℤ) (K : ℕ) : Program :=
  potentialLibraries xl yl zl xr yr zr K++
    [LightTernaryPairedPotentialBatch.body 141,LightTernaryTensorScatter.body,
      LightWeightedGlobalQuarticStep.body 135 134 148,body 142 138 149 147]
def entry : ℕ := 150
end ThreeSum.LightWeightedGlobalTensorDriver
end
end WeightedCache3SUMRefinement_e1ae71d


