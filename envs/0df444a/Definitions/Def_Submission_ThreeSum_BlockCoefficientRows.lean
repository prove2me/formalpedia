-- Prove2me | Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
-- name    : Submission_ThreeSum_BlockCoefficientRows
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:32:35.188252+00:00
-- url     : https://prove2.me/theorems/050950f2-cb5b-43ee-97b5-36a2fb029838
-- title:
--   Block Coefficient Rows
-- statement:
--   Definitions and structural lemmas for Block Coefficient Rows, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockCoefficientRows.lean

import Definitions.Def_Submission_ThreeSum_LightBlockCoefficients
set_option autoImplicit false
namespace ThreeSum.BlockCoefficientRows
open BlockRows BlockIndex BlockEncoding GlobalEncoding LocalCoverBounds
def flat (J L p : ℕ) (sel : ℕ → ℕ) (w : ℕ → ℕ → ℕ) : ℕ → ℕ :=
  OneHotMask.extend fun i : Fin (J*L) =>
    let c := (coordEquiv J L).symm i
    p^c.1.val * w (sel c.1.val) c.2.val
def occurrenceIndices {h J : ℕ} (o : Occurrences h J) : ℕ → ℕ :=
  OneHotMask.extend fun i => (o i).val
def mapRow (h : ℕ) (b : Bool) (s : ℕ) : ℕ → ℕ :=
  if hs : s < scheduleSize h then
    OneHotMask.extend fun i : Fin (512*h) => (mapAt h ⟨s,hs⟩ (i,b)).val
  else fun _ => 0
end ThreeSum.BlockCoefficientRows


