-- Prove2me | Definitions.Def_Submission_ThreeSum_SourceControlLayout
-- name    : Submission_ThreeSum_SourceControlLayout
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:23:46.816547+00:00
-- url     : https://prove2.me/theorems/e5d879c2-fcdc-4152-a038-5bf4c50bd5b9
-- title:
--   Source Control Layout
-- statement:
--   Definitions and structural lemmas for Source Control Layout, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceControlLayout.lean

import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
set_option autoImplicit false
namespace ThreeSum.SourceControlLayout
open GlobalEncoding LocalCoverBounds BlockSourceEncoding SubsetAddress
def scratch (J W logP logE : ℕ) : ℕ :=
  max (max (max ((W+1)^2+(W+1)) (logE+2)) (logP+5)) (J+1)
def stride (W K : ℕ) : ℕ := 5*K+2*W+4+2*(W+1)*K
def span (J W K S logP logE : ℕ) : ℕ :=
  S*stride W K+K+W+2+scratch J W logP logE
def word (J W K S logP logE : ℕ) : ℕ :=
  span J W K S logP logE+stride W K+J+W+K+S+logP+logE+(W+1)^2+30
def values (h J cut : ℕ) : List ℤ :=
  [downsetCap (J*(512*h)) cut,LightBlockSourceCatalog.count h J,SourceBandBankLayout.span h J cut]
end ThreeSum.SourceControlLayout


