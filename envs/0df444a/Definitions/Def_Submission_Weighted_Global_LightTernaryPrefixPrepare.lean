-- Prove2me | Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixPrepare
-- name    : Submission_Weighted_Global_LightTernaryPrefixPrepare
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:49:51.966197+00:00
-- url     : https://prove2.me/theorems/20f1a9e4-6893-4401-a979-49a2f3e26777
-- title:
--   Light Ternary Prefix Prepare
-- statement:
--   Definitions and structural lemmas for Light Ternary Prefix Prepare, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixPrepare.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixHeaderSegment
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixSetupResources
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_Reads_update

set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightWeightedGlobalPrefixPrepare
open Light LightWeightedGlobalPrefixLoop
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
def seedChanged (μ : ℕ→ℤ) (seed power header s : ℕ) : ℕ→ℤ :=
  Function.update (Function.update (Function.update (Function.update μ (seed+4) power)
    (seed+6) power) (seed+24) header) (seed+39) s
def time (m j alpha2 : ℕ) : ℕ :=
  LightWeightedGlobalPrefixSetup.allocateTime m (j+1)+LightWeightedGlobalPrefixHeader.time (j+1) alpha2+1250
def headerLoc (m F p template liveHeader prefixFree alpha2 alphaRank localQ radix J j power Fbase Gbase : ℕ)
    (ret : ℤ) : ℕ→ℤ :=
  frame (LightWeightedGlobalPrefixHeader.args template liveHeader
    (LightWeightedGlobalPrefixSetup.headerAt prefixFree m (j+1)) (j+1) m p power alpha2 alphaRank localQ radix J++
    LightWeightedGlobalPrefixHeader.locals (LightWeightedGlobalPrefixSetup.N m (j+1))
      (LightWeightedGlobalPrefixSetup.T m (j+1)) (2*LightWeightedGlobalPrefixSetup.N m (j+1))
      (F^(j+1)) (LightWeightedGlobalPrefixSetup.nb m (j+1)) prefixFree
      (LightWeightedGlobalPrefixSetup.workAt prefixFree m (j+1)) (j+1) p power alpha2 alphaRank localQ radix Fbase Gbase++[ret])
def HeaderReceipt (μ ν : ℕ→ℤ)
    (m F p template liveHeader prefixFree alpha2 alphaRank localQ radix J j power Fbase Gbase : ℕ) : Prop :=
  ∃ μcopy ret, (∀i<106, μcopy (liveHeader+i)=μ (template+i)) ∧ SameOutside μ μcopy liveHeader 106 ∧
    ν=Function.update (LightWeightedGlobalPrefixHeader.patch liveHeader
      (headerLoc m F p template liveHeader prefixFree alpha2 alphaRank localQ radix J j power Fbase Gbase ret)
      μcopy headerWrites) (liveHeader+104) 0
end ThreeSum.LightWeightedGlobalPrefixPrepare


