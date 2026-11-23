-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_cqReplayRowRecurrence
-- name    : GrothendieckLB_Supplement_cqReplayRowRecurrence
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T19:38:01.087916+00:00
-- url     : https://prove2.me/theorems/9f598c92-f6e0-45ae-8978-c9b9427b12c8
-- title:
--   Pointwise cubic Hermite recurrence and checkpoint generator
-- statement:
--   Three elementary Hermite shifts and the parity-dependent outward quotient specify each new row. Two consecutive such rows determine all subsequent rows.
-- source:
--   Independent integer replay of the cubic–quintic Hermite coefficient calculation in Saha et al., arXiv:2608.11158v2, (13) and Appendix C.1.

import Definitions.Def_GrothendieckLB_Supplement_cqReplayMoments

set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

open GrothendieckLB.Supplement.CQHeadArithmetic
namespace GrothendieckLB.Supplement.CQHeadCertificate

def roll (start count : ℕ) (prev cur : Array MomentCombination)
    (keep : ℕ → Bool) : Array (Packed × Packed) := Id.run do
  let mut left := prev
  let mut right := cur
  let mut out := #[]
  for k in [:count] do
    let p := start+k
    if keep p then
      out := out.push (packA ((p-1)%2) left, packA (p%2) right)
    let r := nextRow p left right
    left := right
    right := r
  return out

def makeCheckpoint (p : ℕ) : Packed × Packed :=
  let x := rowAt 0 startData
  entry default (roll 0 (p+1) x x (fun i => i=p)) 0

def nextAt (p : ℕ) (l r : ℕ → MomentCombination) (b : ℕ) :=
  subCombination (multiplyByParityFactor p (subCombination (scaleCombination 3 (shiftAt r b))
    (shiftAt (shiftAt (shiftAt r)) b))) (scaleCombination p (l b))

def rowTest (p : ℕ) (prev cur next : Packed) (b : ℕ) : Bool :=
  decide (getA next ((p+1)%2) b = nextAt p (getA prev ((p-1)%2)) (getA cur (p%2)) b)

def stripLen (c : ℕ) : ℕ := min 16 (251-16*c)

end GrothendieckLB.Supplement.CQHeadCertificate


