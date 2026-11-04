-- Prove2me | Definitions.Def_Submission_ThreeSum_Greedy
-- name    : Submission_ThreeSum_Greedy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:04:55.115908+00:00
-- url     : https://prove2.me/theorems/eb658e91-8f07-4c80-8d97-78cf39f4fbd4
-- title:
--   Greedy
-- statement:
--   Definitions and structural lemmas for Greedy, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Greedy.lean

import Definitions.Def_Submission_ThreeSum_Cover
import Mathlib.Data.List.MinMax
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Ring
import Aesop
set_option autoImplicit false
namespace ThreeSum.Cover
open Finset
open scoped BigOperators
variable {Ω U : Type*} [Inhabited Ω] [DecidableEq U]
def selectMap (maps : List Ω) (covers : Ω → U → Prop) [DecidableRel covers]
    (targets : Finset U) : Ω :=
  (maps.argmax fun ω => (targets.filter (covers ω)).card).getD default
def greedyState (maps : List Ω) (covers : Ω → U → Prop) [DecidableRel covers]
    (targets : Finset U) : ℕ → Finset U
  | 0 => targets
  | t + 1 =>
    let old := greedyState maps covers targets t
    old.filter fun u => ¬ covers (selectMap maps covers old) u
def greedyChoices (maps : List Ω) (covers : Ω → U → Prop) [DecidableRel covers]
    (targets : Finset U) : ℕ → List Ω
  | 0 => []
  | t + 1 => greedyChoices maps covers targets t ++
      [selectMap maps covers (greedyState maps covers targets t)]
end ThreeSum.Cover


