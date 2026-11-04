-- Prove2me | Definitions.Def_Submission_ThreeSum_LightThreeSumColorDriver
-- name    : Submission_ThreeSum_LightThreeSumColorDriver
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:34:04.936259+00:00
-- url     : https://prove2.me/theorems/df360e6a-cee0-40e9-8b8e-ddd5b6ac07e1
-- title:
--   Light Three Sum Color Driver
-- statement:
--   Definitions and structural lemmas for Light Three Sum Color Driver, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightThreeSumColorDriver.lean

import Definitions.Def_Submission_ThreeSum_LightColorScanHost
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Theorems.Thm_P2M_Light_getElem__append_length_add_3291fe153891
import Theorems.Thm_ThreeSum_LightReportingSortedCatalog_procs

set_option autoImplicit false
namespace ThreeSum.LightThreeSumColorDriver
open Light ColorParameters LightColorParametersCosts
set_option maxHeartbeats 2000000
set_option maxRecDepth 14000
def extra (colorProgram : Program) (pColor : ℕ) : Program :=
  [LightColorParameters.body (colorProgram.length+1),LightSmallDivide.body,
    LightColorScan.body (colorProgram.length+2) colorProgram.length pColor,
    LightColorScanHost.body (colorProgram.length+2)]
def program (colorProgram : Program) (pColor : ℕ) : Program := colorProgram++extra colorProgram pColor
def procs (colorProgram : Program) (pColor : ℕ) :
    LightColorScanHost.Procs (program colorProgram pColor) (colorProgram.length+3) where
  pScan := colorProgram.length+2
  scan := {
    pParameters := colorProgram.length
    pDivide := colorProgram.length+1
    pColor := pColor
    main := by apply getElem?_append_length_add; rfl
    parameters := by
      change (colorProgram++extra colorProgram pColor)[colorProgram.length+0]?=_
      apply getElem?_append_length_add
      rfl
    divide := by apply getElem?_append_length_add; rfl }
  main := by apply getElem?_append_length_add; rfl
end ThreeSum.LightThreeSumColorDriver


