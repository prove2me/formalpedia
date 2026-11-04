-- Prove2me | Definitions.Def_Submission_ThreeSum_TernarySignedReduction
-- name    : Submission_ThreeSum_TernarySignedReduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:24:31.670589+00:00
-- url     : https://prove2.me/theorems/aeec5735-21b2-49fd-a879-402ca14173f2
-- title:
--   Ternary Signed Reduction
-- statement:
--   Definitions and structural lemmas for Ternary Signed Reduction, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedReduction.lean

import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Mathlib.Data.ZMod.Basic
set_option autoImplicit false
namespace ThreeSum.TernarySignedReduction
open TernarySignedDigits Finset
def shiftOne (U : ℕ) (x : ℤ) : ℕ := (x+U).toNat
def shiftTwo (U : ℕ) (x : ℤ) : ℕ := (x+2*U).toNat
def carryCatalog (J : ℕ) : Finset (CarryWord J) := univ.filter ValidCarry
abbrev Coordinate (J : ℕ) := Sum (Fin J) Bool
def leftRaw (U radix J : ℕ) (b : ℤ) : Coordinate J → ℤ
  | .inl j => -(digit radix (shiftOne U b) j : ℤ)
  | .inr false => 1
  | .inr true => 0
def rightRaw (U radix J : ℕ) (c : ℤ) : Coordinate J → ℤ
  | .inl j => (digit radix (shiftTwo U c) j : ℤ)
  | .inr false => 0
  | .inr true => 1
def requesterRaw (U radix J : ℕ) (a : ℤ) (carry : CarryWord J) : Coordinate J → ℤ
  | .inl j => (digit radix (shiftOne U a) j : ℤ)-
      ((radix : ℤ)*carryAt carry (j+1)-carryAt carry j)
  | .inr _ => 1
end ThreeSum.TernarySignedReduction


