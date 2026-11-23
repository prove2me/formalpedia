-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_cqReplaySums
-- name    : GrothendieckLB_Supplement_cqReplaySums
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T19:40:42.870814+00:00
-- url     : https://prove2.me/theorems/fd627df3-fd7a-4a7a-8693-bafd4fb5814e
-- title:
--   Signed convolution witnesses in the cubic–quintic head
-- statement:
--   For each odd scalar degree up to 251, the table stores the signed contribution at each primary degree. The checks compare individual terms, partial sums and the final integer enclosure.
-- source:
--   Independent integer replay of the cubic–quintic Hermite coefficient calculation in Saha et al., arXiv:2608.11158v2, (13) and Appendix C.1.

import Definitions.Def_GrothendieckLB_Supplement_cqReplayWeights
import Definitions.Def_GrothendieckLB_Supplement_cqReplayPowers

set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

open GrothendieckLB.Supplement.CQHeadArithmetic
namespace GrothendieckLB.Supplement.CQHeadCertificate

def term (m a b : ℕ) : Interval :=
  scaleInterval ((-1:ℤ)^b) (mulInterval coefficientScale (weight a b) (power a (m-b)))

def part (m a : ℕ) : Interval := sumIntervals (term m a) (m+1-a)

def partialData : Array Packed := eval%
  let ws := (grid 251 (rowAt 0 startData) 251).weights
  let rs := rhoPowers 251 251
  tab 125 fun j =>
    let m := 2*j+3
    let res := tab (m+1) fun a =>
      let w := entry #[] ws a
      let r := entry #[] rs a
      sumIntervals (fun b => scaleInterval ((-1:ℤ)^b) (mulInterval coefficientScale
        (entry zeroInterval w b) (entry zeroInterval r (m-b)))) (m+1-a)
    packed (m+1) 2 16 fun a k => if k=0 then (entry zeroInterval res a).lo else (entry zeroInterval res a).hi

def savedPart (j a : ℕ) : Interval :=
  let p := entry default partialData j
  ⟨getN p 2 16 a 0, getN p 2 16 a 1⟩

def partialChecks (j : ℕ) : Bool :=
  (List.range (2*j+4)).all fun a => decide (savedPart j a=part (2*j+3) a)

def totalChecks : Bool := (List.range 125).all fun j =>
  let v := sumIntervals (savedPart j) (2*j+4)
  max (-v.lo) v.hi * 10^40 ≤ coefficientScale*2*314159265358979323846*(cqHeadUnits[j]?.getD 0)

end GrothendieckLB.Supplement.CQHeadCertificate


