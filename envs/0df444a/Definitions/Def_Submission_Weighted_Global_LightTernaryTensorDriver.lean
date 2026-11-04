-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightTernaryTensorDriver
-- name    : Submission_Weighted_Global_LightTernaryTensorDriver
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:07:55.443074+00:00
-- url     : https://prove2.me/theorems/12087331-1194-43dd-8ecc-2835099bda44
-- title:
--   Light Ternary Tensor Driver
-- statement:
--   Definitions and structural lemmas for Light Ternary Tensor Driver, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryTensorDriver.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryQuarticStep
set_option autoImplicit false
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


