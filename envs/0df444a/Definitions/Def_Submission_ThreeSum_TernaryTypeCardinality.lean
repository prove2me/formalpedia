-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
-- name    : Submission_ThreeSum_TernaryTypeCardinality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:51:06.616401+00:00
-- url     : https://prove2.me/theorems/ed3d3b54-b39d-4194-92ed-230f5d5bc549
-- title:
--   Ternary Type Cardinality
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryTypeCardinality
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryCoverLocal
set_option maxHeartbeats 2000000
def positions {L : ℕ} (w : TritWord L) (d : Fin 3) : Finset (Fin L) :=
  univ.filter (fun i => w i=d)
abbrev Pair (L : ℕ) := Σ _t : Finset (Fin L), Finset (Fin L)
def digitPairs (L a b : ℕ) : Finset (Pair L) :=
  (univ.powersetCard b).sigma (fun t => (univ\t).powersetCard a)
def encode {L : ℕ} (w : TritWord L) : Pair L :=
  ⟨positions w 2,positions w 1⟩
def decode {L : ℕ} (p : Pair L) : TritWord L := fun i =>
  if i∈p.1 then 2 else if i∈p.2 then 1 else 0
end ThreeSum.TernaryTypeCardinality


