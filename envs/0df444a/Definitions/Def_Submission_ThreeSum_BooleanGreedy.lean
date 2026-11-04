-- Prove2me | Definitions.Def_Submission_ThreeSum_BooleanGreedy
-- name    : Submission_ThreeSum_BooleanGreedy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:27:51.228242+00:00
-- url     : https://prove2.me/theorems/51606278-f8d3-4b8f-bf51-2ef5965c6d55
-- title:
--   Boolean Greedy
-- statement:
--   Definitions and structural lemmas for Boolean Greedy, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BooleanGreedy.lean

import Definitions.Def_Submission_ThreeSum_IndexedGreedy
import Definitions.Def_Submission_ThreeSum_LightCoverScores
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
set_option autoImplicit false
namespace ThreeSum.BooleanGreedy
open Finset
open scoped BigOperators
def covers (matrix : ℕ → ℕ → ℕ) (row col : ℕ) : Prop := matrix row col = 1
instance (matrix : ℕ → ℕ → ℕ) : DecidableRel (covers matrix) :=
  fun _ _ => inferInstanceAs (Decidable (_ = _))
def state (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) : Finset ℕ :=
  Cover.greedyState (List.range rows) (covers matrix) (range cols) t
def active (matrix : ℕ → ℕ → ℕ) (rows cols t j : ℕ) : ℕ :=
  if j ∈ state matrix rows cols t then 1 else 0
def choice (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) : ℕ :=
  Cover.selectMap (List.range rows) (covers matrix) (state matrix rows cols t)
def choices (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) : List ℕ :=
  Cover.greedyChoices (List.range rows) (covers matrix) (range cols) t
end ThreeSum.BooleanGreedy


