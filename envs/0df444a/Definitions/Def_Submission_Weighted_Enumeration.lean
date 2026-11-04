-- Prove2me | Definitions.Def_Submission_Weighted_Enumeration
-- name    : Submission_Weighted_Enumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:23:50.629745+00:00
-- url     : https://prove2.me/theorems/22140a4c-a83f-44fb-8f42-2a49705b2421
-- title:
--   Enumeration
-- statement:
--   Definitions and structural lemmas for Enumeration, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Enumeration.lean

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
set_option autoImplicit false
namespace ThreeSum.WeightedEnumeration
def digitCost (d : ℕ) : ℕ := if d = 2 then 1025 else 512*d
def digits (t : ℕ) : List ℕ := (List.range 3).filter (fun d => digitCost d ≤ t)
def words : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | n + 1, t => (digits t).flatMap fun d => (words n (t - digitCost d)).map (List.cons d)
def visits : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, t => 1 + ((digits t).map fun d => visits n (t - digitCost d)).sum
end ThreeSum.WeightedEnumeration


