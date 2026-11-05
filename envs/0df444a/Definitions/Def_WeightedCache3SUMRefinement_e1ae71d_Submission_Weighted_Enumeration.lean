-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Enumeration
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Enumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:05:06.078799+00:00
-- url     : https://prove2.me/theorems/19bf1162-cda1-4645-8589-d1e1f47fdabe
-- title:
--   Enumeration
-- statement:
--   Definitions and structural lemmas for Enumeration, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Enumeration.lean

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
namespace ThreeSum.WeightedEnumeration
def digitCost (d : ℕ) : ℕ := if d = 2 then 2740 else 1369*d
def digits (t : ℕ) : List ℕ := (List.range 3).filter (fun d => digitCost d ≤ t)
def words : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | n + 1, t => (digits t).flatMap fun d => (words n (t - digitCost d)).map (List.cons d)
def visits : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, t => 1 + ((digits t).map fun d => visits n (t - digitCost d)).sum
end ThreeSum.WeightedEnumeration
end WeightedCache3SUMRefinement_e1ae71d


