-- Prove2me | Definitions.Def_Submission_ThreeSum_OneHotMask
-- name    : Submission_ThreeSum_OneHotMask
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:12:18.897444+00:00
-- url     : https://prove2.me/theorems/817d5fdc-cc01-41d0-a162-9d2d84bddd4d
-- title:
--   One Hot Mask
-- statement:
--   Definitions and structural lemmas for One Hot Mask, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OneHotMask.lean

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_MaskErase
set_option autoImplicit false
namespace ThreeSum.OneHotMask
open Finset SubsetAddress LocalHashMoments
open scoped BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
def eval (w0 w1 : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | L+1, m =>
    if m < 2^L then eval w0 w1 L m + w0 L
    else eval w0 w1 L (m-2^L) + w1 L
def extend {L : ℕ} (f : Fin L → ℕ) (i : ℕ) : ℕ :=
  if hi : i < L then f ⟨i,hi⟩ else 0
end ThreeSum.OneHotMask


