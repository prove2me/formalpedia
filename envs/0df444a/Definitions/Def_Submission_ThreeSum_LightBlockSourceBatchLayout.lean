-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchLayout
-- name    : Submission_ThreeSum_LightBlockSourceBatchLayout
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:40:58.85587+00:00
-- url     : https://prove2.me/theorems/ffdd98a1-7034-4f18-be87-20bcbb0cd3d1
-- title:
--   Light Block Source Batch Layout
-- statement:
--   Definitions and structural lemmas for Light Block Source Batch Layout, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceBatchLayout.lean

import Definitions.Def_Submission_ThreeSum_LightZetaStages
set_option autoImplicit false
namespace ThreeSum.LightBlockSourceBatchLayout
open SubsetAddress LightZetaStages
def family (W cut : ℕ) : ℕ := (W+1)*downsetCap W cut
def stride (W cut : ℕ) : ℕ := 5*downsetCap W cut+2*W+2+2*family W cut
def banks (base count : ℕ) : ℕ := base+2*count
def slot (base count W cut i : ℕ) : ℕ := banks base count+i*stride W cut
def coeff0 (base count W cut i : ℕ) : ℕ := slot base count W cut i+downsetCap W cut
def coeff1 (base count W cut i : ℕ) : ℕ := coeff0 base count W cut i+W
def rawLeft (base count W cut i : ℕ) : ℕ := coeff1 base count W cut i+W
def rawRight (base count W cut i : ℕ) : ℕ := rawLeft base count W cut i+downsetCap W cut
def flags (base count W cut i : ℕ) : ℕ := rawRight base count W cut i+downsetCap W cut
def leftBase (base count W cut i : ℕ) : ℕ := flags base count W cut i+2*downsetCap W cut+2
def rightBase (base count W cut i : ℕ) : ℕ := leftBase base count W cut i+family W cut
def maskBase (base count W cut : ℕ) : ℕ := slot base count W cut count
def bitBase (base count W cut : ℕ) : ℕ := maskBase base count W cut+downsetCap W cut
def rowOut (base count W cut : ℕ) : ℕ := bitBase base count W cut+W
def work (base count W cut : ℕ) : ℕ := rowOut base count W cut+2
end ThreeSum.LightBlockSourceBatchLayout


