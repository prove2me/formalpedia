-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryEnumeration
-- name    : Submission_ThreeSum_TernaryEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:23:50.283358+00:00
-- url     : https://prove2.me/theorems/7ad13b21-07e0-4bbb-ad06-627433a862c2
-- title:
--   Ternary Enumeration
-- statement:
--   Definitions and structural lemmas for Ternary Enumeration, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEnumeration.lean

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
set_option autoImplicit false
namespace ThreeSum.TernaryEnumeration
def digits (t : ℕ) : List ℕ := (List.range 3).filter (fun d => d ≤ t)
def words : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | n + 1, t => (digits t).flatMap fun d => (words n (t - d)).map (List.cons d)
def visits : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, t => 1 + ((digits t).map fun d => visits n (t - d)).sum
end ThreeSum.TernaryEnumeration


