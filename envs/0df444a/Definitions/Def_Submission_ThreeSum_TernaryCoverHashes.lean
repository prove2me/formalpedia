-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
-- name    : Submission_ThreeSum_TernaryCoverHashes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:41:08.356824+00:00
-- url     : https://prove2.me/theorems/1c1a3b37-be0b-4ecf-b305-8c581f7b5ed6
-- title:
--   Ternary Cover Hashes
-- statement:
--   Definitions and structural lemmas for Ternary Cover Hashes, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverHashes.lean

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Tactic.LinearCombination
set_option autoImplicit false
namespace ThreeSum.TernaryCoverHashes
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [Field K]
abbrev Coordinate (ι : Type*) := Sum ι Bool
def leftVector (x : ι → K) : Coordinate ι → K :=
  Sum.elim x (fun b => if b then 0 else 1)
def rightVector (x : ι → K) : Coordinate ι → K :=
  Sum.elim x (fun b => if b then 1 else 0)
def outputVector (x : ι → K) : Coordinate ι → K :=
  Sum.elim x (fun _ => 1)
section Finite
variable [Fintype K] [DecidableEq K] [DecidableEq ι]
def linearHash (v : Coordinate ι → K) (w : Coordinate ι → K) : K :=
  ∑ i, v i * w i
def pairEvent (x y : ι → K) (a b : K) : Finset (Coordinate ι → K) :=
  Finset.univ.filter fun w => linearHash (leftVector x) w = a ∧
    linearHash (rightVector y) w = b
end Finite
end ThreeSum.TernaryCoverHashes


