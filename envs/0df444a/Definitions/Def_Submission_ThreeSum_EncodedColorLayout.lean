-- Prove2me | Definitions.Def_Submission_ThreeSum_EncodedColorLayout
-- name    : Submission_ThreeSum_EncodedColorLayout
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:49:49.145809+00:00
-- url     : https://prove2.me/theorems/79b69fd8-1ccc-4a86-908d-7a94b9a6b8db
-- title:
--   Encoded Color Layout
-- statement:
--   Definitions and structural lemmas for Encoded Color Layout, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorLayout.lean

import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeData
import Definitions.Def_Submission_ThreeSum_LightBandRawAColor
set_option autoImplicit false
namespace ThreeSum.EncodedColorLayout
def colors (free : ℕ) : ℕ := free+8
def class0 (free n : ℕ) : ℕ := colors free+n
def class1 (free n : ℕ) : ℕ := class0 free n+n+1
def class2 (free n : ℕ) : ℕ := class1 free n+n+1
def av (free n : ℕ) : ℕ := class2 free n+n+1
def ae (free n : ℕ) : ℕ := av free n+n
def bv (free n : ℕ) : ℕ := ae free n+2+2*n
def be (free n : ℕ) : ℕ := bv free n+n
def cv (free n : ℕ) : ℕ := be free n+2+2*n
def ce (free n : ℕ) : ℕ := cv free n+n
def tables (free n : ℕ) : ℕ := ce free n+2+2*n
def rec (free n g : ℕ) : ℕ := tables free n+ColorBandBounds.count n g
def vals (free n g : ℕ) : ℕ := rec free n g+4*ColorBandBounds.count n g
def normalizedEnd (free n g : ℕ) : ℕ := LightBandRawA.space (vals free n g) (ColorBandBounds.count n g) g
def prime (free n g : ℕ) : ℕ := normalizedEnd free n g+1
def cover (free n g M y : ℕ) : ℕ := EncodedColorPrimeData.nextFree (prime free n g) M y
def normalizedHeads (free n g : ℕ) : List ℤ :=
  [av free n,ae free n,bv free n,be free n,cv free n,ce free n,rec free n g,vals free n g]
end ThreeSum.EncodedColorLayout


