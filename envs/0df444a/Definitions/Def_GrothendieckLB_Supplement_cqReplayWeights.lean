-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_cqReplayWeights
-- name    : GrothendieckLB_Supplement_cqReplayWeights
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T19:38:00.757219+00:00
-- url     : https://prove2.me/theorems/36713b3e-3fc8-45a8-a622-f059d3fa4aa1
-- title:
--   Paged squared weights for the cubic Hermite threshold
-- statement:
--   The squared Gaussian weights are stored with denominator $2^{144}$. The defining predicates compute each candidate weight from the appropriate Hermite row, including the exceptional zeroth row.
-- source:
--   Independent integer replay of the cubic–quintic Hermite coefficient calculation in Saha et al., arXiv:2608.11158v2, (13) and Appendix C.1.

import Definitions.Def_GrothendieckLB_Supplement_cqReplayMoments

set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

open GrothendieckLB.Supplement.CQHeadArithmetic
namespace GrothendieckLB.Supplement.CQHeadCertificate

def weightsData : Array Packed := eval%
  let ws := (grid 251 (rowAt 0 startData) 251).weights
  tab 252 fun a => packB ((a+1)%2) (entry #[] ws a)

def weight (a b : ℕ) : Interval := getB (entry default weightsData a) ((a+1)%2) b

def weightAt (p b : ℕ) (x : MomentCombination) : Interval :=
  let base : ℤ := (fac (p+1):ℤ)*(fac b:ℤ)
  if p%2=0 then scaledSq 1 base x else scaledSq slopeNumerator (slopeDenominator*base) x

def zeroWeightAt (b : ℕ) : Interval := if b=0 then zeroInterval else
  scaledSq (9*slopeNumerator) (slopeDenominator*fac b)
    (subCombination (shiftAt (shiftAt first) (b-1)) (first (b-1)))

end GrothendieckLB.Supplement.CQHeadCertificate


