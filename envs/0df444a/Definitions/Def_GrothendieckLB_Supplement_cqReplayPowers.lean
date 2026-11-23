-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_cqReplayPowers
-- name    : GrothendieckLB_Supplement_cqReplayPowers
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T19:36:29.247385+00:00
-- url     : https://prove2.me/theorems/dc3da3dd-d6c9-4c79-b32b-8b0fa584b2cb
-- title:
--   Paged coefficient intervals of the primary correlation powers
-- statement:
--   For the exact cubic–quintic primary correlation, each packed row stores outward integer endpoints for its polynomial powers. The row predicate compares these endpoints with one multiplication by the primary correlation.
-- source:
--   Independent integer replay of the cubic–quintic Hermite coefficient calculation in Saha et al., arXiv:2608.11158v2, (13) and Appendix C.1.

import Definitions.Def_GrothendieckLB_Supplement_cqReplayPacking

set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

open GrothendieckLB.Supplement.CQHeadArithmetic
namespace GrothendieckLB.Supplement.CQHeadCertificate

def powersData : Array Packed := eval%
  let rs := rhoPowers 251 251
  tab 252 fun a => packB (a%2) (entry #[] rs a)

def power (a j : ℕ) : Interval := getB (entry default powersData a) (a%2) j

def powerAt (a j : ℕ) : Interval :=
  let s (k : ℕ) := if k≤j then power a (j-k) else zeroInterval
  divideOut rhoDen (addInterval (subInterval (scaleInterval rho1 (s 1)) (scaleInterval rho3 (s 3)))
    (scaleInterval rho5 (s 5)))

def powerChecks (c : ℕ) : Bool := (List.range (min 16 (251-16*c))).all fun k =>
  (List.range 252).all fun j => decide (power (16*c+k+1) j=powerAt (16*c+k) j)

end GrothendieckLB.Supplement.CQHeadCertificate


