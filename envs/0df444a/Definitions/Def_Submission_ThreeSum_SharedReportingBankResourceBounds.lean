-- Prove2me | Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBounds
-- name    : Submission_ThreeSum_SharedReportingBankResourceBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:10:19.337707+00:00
-- url     : https://prove2.me/theorems/e3f313d7-85e7-4f27-b3d9-b2f4b5634539
-- title:
--   Shared Reporting Bank Resource Bounds
-- statement:
--   Definitions and structural lemmas for Shared Reporting Bank Resource Bounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankResourceBounds.lean

import Definitions.Def_Submission_ThreeSum_SharedReportingBankCosts
import Definitions.Def_Submission_ThreeSum_PolynomialResources
set_option autoImplicit false
namespace ThreeSum.SharedReportingBankResourceBounds
open Light SubsetAddress SharedReportingBankLayout SharedReportingBankLevels
open SharedReportingBankHeader SharedReportingBankRows
set_option maxHeartbeats 2800000
set_option maxRecDepth 14000
def prefixCount (h J : ℕ) : ℕ := 2^(2*((J+1)*(512*h)))
def prefixStorage (h J : ℕ) : ℕ := (levels J+1)*(prefixCount h J+1)
def cellBound (h J : ℕ) : ℕ :=
  2^(512*h)+2*2^(2*(512*h))+2*prefixStorage h J+3*prefixCount h J+
    prefixCount h J*(width h J+1)*2^(width h J)+2^(width h J)+2*(512*h)+3+
    (width h J+1)^2+(width h J+1)
def extent (h J n : ℕ) : ℕ :=
  9+(512*h+1)^2+LightBlockSourceCatalog.count h J*n*n*
    (5*levels J+levels J*cellBound h J)
def depth (h J : ℕ) : ℕ := 512*h+levels J+2*width h J+30
def control (h J n : ℕ) : ℕ :=
  LightBlockSourceCatalog.count h J*n+LightBlockSourceCatalog.count h J+n+n+J+levels J+512
def stateWord (h J : ℕ) : ℕ := J+levels J+512+prefixStorage h J+prefixCount h J
def word (h J n g : ℕ) : ℕ :=
  control h J n+SourceBandBankLayout.span h J (2*h*J)+2^(512*h+1)+2^(2*(512*h))+
    LightSwitchDepth.word J+stateWord h J+LightRadixKeys.word (2^(512*h)) (2^(512*h)) J+
    (width h J+1)*2^(width h J+1)+
    LightReportingSortedCatalog.word (width h J) (2^(2*width h J))+
    2^(width h J)*((2^(width h J)*g)*(2^(width h J)*g))+
    (J+2*h*J+1001)^64
end ThreeSum.SharedReportingBankResourceBounds


