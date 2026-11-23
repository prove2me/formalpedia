-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_cqReplayRows
-- name    : GrothendieckLB_Supplement_cqReplayRows
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T19:43:42.829408+00:00
-- url     : https://prove2.me/theorems/367bdd28-45fc-40e9-8d7a-8c8376fc8789
-- title:
--   Checkpoint witnesses for the cubic Hermite recurrence
-- statement:
--   A checkpoint stores two consecutive rows of the cubic Hermite recurrence. The strip predicate checks all intervening shifts, outward quotients and Gaussian weights and matches the next checkpoint.
-- source:
--   Independent integer replay of the cubic–quintic Hermite coefficient calculation in Saha et al., arXiv:2608.11158v2, (13) and Appendix C.1.

import Definitions.Def_GrothendieckLB_Supplement_cqReplayWeights
import Definitions.Def_GrothendieckLB_Supplement_cqReplayCheckpoint0
import Definitions.Def_GrothendieckLB_Supplement_cqReplayCheckpoint1
import Definitions.Def_GrothendieckLB_Supplement_cqReplayCheckpoint2
import Definitions.Def_GrothendieckLB_Supplement_cqReplayCheckpoint3

set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

open GrothendieckLB.Supplement.CQHeadArithmetic
namespace GrothendieckLB.Supplement.CQHeadCertificate

def checkpoints : Array (Packed × Packed) := #[stage0, stage1, stage2, stage3, stage4, stage5, stage6, stage7, stage8, stage9, stage10, stage11, stage12, stage13, stage14, stage15, stage16]

def cpRow (p : ℕ) := (entry default checkpoints (p/16)).2

def cpPrev (p : ℕ) := (entry default checkpoints (p/16)).1

def makeStrip (start count : ℕ) : Array Packed := Id.run do
  let mut l := rowAt (start-1) (cpPrev start)
  let mut r := rowAt start (cpRow start)
  let mut out := #[]
  for k in [:count] do
    out := out.push (packA ((start+k)%2) r)
    let s := nextRow (start+k) l r
    l := r
    r := s
  return out

def checkpoint (c : ℕ) := entry default checkpoints c

def inStrip (c : ℕ) (xs : Array Packed) (k : ℕ) : Packed :=
  if k=0 then (checkpoint c).2 else if k=stripLen c then (checkpoint (c+1)).2 else entry default xs k

def beforeStrip (c : ℕ) (xs : Array Packed) (k : ℕ) : Packed :=
  if k=0 then (checkpoint c).1 else inStrip c xs (k-1)

def stripChecks (c : ℕ) (xs : Array Packed) : Bool :=
  decide (inStrip c xs (stripLen c-1) = (checkpoint (c+1)).1) &&
  (List.range (stripLen c)).all fun k =>
    let p := 16*c+k
    let cur := inStrip c xs k
    ((List.range (rowLength (p+1))).all
      (rowTest p (beforeStrip c xs k) cur (inStrip c xs (k+1)))) &&
    (List.range (251-p)).all fun b => decide (weight (p+1) b=weightAt p b (getA cur (p%2) b))

end GrothendieckLB.Supplement.CQHeadCertificate


