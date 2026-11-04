-- Prove2me | Definitions.Def_Submission_ThreeSum_LightHistogram
-- name    : Submission_ThreeSum_LightHistogram
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:20:04.410224+00:00
-- url     : https://prove2.me/theorems/13ddf6bf-4c95-44d6-8c19-6bfd24c7941a
-- title:
--   Light Histogram
-- statement:
--   Definitions and structural lemmas for Light Histogram, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightHistogram.lean

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
namespace ThreeSum.LightHistogram
open Light Finset
variable {lim : Limits} {P : Program} {d : ℕ}
def count (key : ℕ → ℕ) (r i : ℕ) : ℕ :=
  ((Finset.range i).filter fun j => key j = r).card
def countBody : Stmt :=
  .for 4 (v 2) (.store (v 1 +' M (v 0 +' v 4))
    (M (v 1 +' M (v 0 +' v 4)) +' k 1))
def countTime (n : ℕ) : ℕ := 24 * n + 6
def histogramBody (pFill : ℕ) : Stmt :=
  .call pFill [v 1, v 3, k 0] 5 ;; countBody
def histogramTime (n p : ℕ) : ℕ := fillTime p + countTime n + 5
end ThreeSum.LightHistogram


