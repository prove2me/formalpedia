-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
-- name    : Submission_ThreeSum_TernaryWantedRadix
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:15:47.663004+00:00
-- url     : https://prove2.me/theorems/3778e0f8-26b1-489e-b20f-88e9f6548ee8
-- title:
--   Ternary Wanted Radix
-- statement:
--   Definitions and structural lemmas for Ternary Wanted Radix, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedRadix.lean

import Definitions.Def_Submission_ThreeSum_Radix
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
set_option autoImplicit false
namespace ThreeSum.TernaryWantedRadix
open Finset
def localBucket (p : ℤ) (raws : List ℤ) (x : ℤ) : List ℕ :=
  (List.range raws.length).filter fun i => p ∣ x-raws.getD i 0
def wantedOutputs (p : ℤ) (raws : List ℤ) : ℕ → ℤ → List (List ℕ)
  | 0, _ => [[]]
  | j+1, x => (localBucket p raws x).flatMap fun i =>
      (wantedOutputs p raws j ((x-raws.getD i 0)/p)).map (List.cons i)
def encode (N code scale : ℕ) : List ℕ → ℕ
  | [] => code
  | i::is => encode N (code+scale*i) (scale*N) is
def wantedCodes (p : ℤ) (raws : List ℤ) (j : ℕ) (x : ℤ) (code scale : ℕ) : List ℕ :=
  (wantedOutputs p raws j x).map (encode raws.length code scale)
def visits (p : ℤ) (raws : List ℤ) : ℕ → ℤ → ℕ
  | 0, _ => 1
  | j+1, x => 1+((localBucket p raws x).map fun i => visits p raws j ((x-raws.getD i 0)/p)).sum
def codeLimit (N code scale j : ℕ) : ℕ := (code+scale)*(2*N)^j
end ThreeSum.TernaryWantedRadix


