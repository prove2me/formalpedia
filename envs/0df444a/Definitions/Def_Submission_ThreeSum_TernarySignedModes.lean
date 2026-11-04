-- Prove2me | Definitions.Def_Submission_ThreeSum_TernarySignedModes
-- name    : Submission_ThreeSum_TernarySignedModes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:41:10.939914+00:00
-- url     : https://prove2.me/theorems/942760fc-b961-404f-a183-f8cbbcc4419e
-- title:
--   Ternary Signed Modes
-- statement:
--   Definitions and structural lemmas for Ternary Signed Modes, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedModes.lean

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Mathlib.Data.Int.Lemmas
set_option autoImplicit false
namespace ThreeSum.TernarySignedModes
open TernarySignedDigits TernarySignedReduction Finset
def rawMode (U radix J : ℕ) (b c : ℤ) (k : Coordinate J) : ℤ :=
  leftRaw U radix J b k+rightRaw U radix J c k
def fieldLeft (p U radix J : ℕ) (b : ℤ) (k : Coordinate J) : ZMod p := leftRaw U radix J b k
def fieldRight (p U radix J : ℕ) (c : ℤ) (k : Coordinate J) : ZMod p := rightRaw U radix J c k
def fieldRequester (p U radix J : ℕ) (a : ℤ) (carry : CarryWord J)
    (k : Coordinate J) : ZMod p := requesterRaw U radix J a carry k
def fieldMode (p U radix J : ℕ) (b c : ℤ) (k : Coordinate J) : ZMod p := rawMode U radix J b c k
end ThreeSum.TernarySignedModes


