-- Prove2me | Definitions.Def_Submission_ThreeSum_LightSignedRowHash
-- name    : Submission_ThreeSum_LightSignedRowHash
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:25:57.032399+00:00
-- url     : https://prove2.me/theorems/a6602316-3c3a-4767-9d11-aed2930cf267
-- title:
--   Light Signed Row Hash
-- statement:
--   Definitions and structural lemmas for Light Signed Row Hash, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedRowHash.lean

import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_LightNaturalDot
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightSignedRowHash
open Light
set_option maxHeartbeats 2000000
def lifted (p : ℕ) (z : ℤ) : ℕ := ((p : ℤ)+z).toNat
def body (pLift pDot : ℕ) : Stmt :=
  .call pLift [v 0,v 2,v 3,v 4,k 1] 5 ;;
  .call pDot [v 1,v 2,v 3,v 4] 0
def time (n p b : ℕ) : ℕ := LightReportingAffine.time n+LightNaturalDot.reducedTime n p (p+b)+100
def word (n p b : ℕ) : ℕ := 20*((n+1)*(p+1)*(p+b+1)+p+10)+100
structure Procs (P : Program) (main : ℕ) where
  lift : ℕ
  dot : ℕ
  rawDot : ℕ
  digit : ℕ
  divide : ℕ
  mainBody : P[main]?=some (body lift dot)
  liftBody : P[lift]?=some LightReportingAffine.body
  dotBody : P[dot]?=some (LightNaturalDot.reducedBody rawDot digit)
  rawBody : P[rawDot]?=some LightNaturalDot.body
  digitBody : P[digit]?=some (LightRadixDigit.body divide)
  divideBody : P[divide]?=some LightSmallDivide.body
variable {lim : Limits} {P : Program} {depth : ℕ}
def program : Program := [body 1 2,LightReportingAffine.body,LightNaturalDot.reducedBody 3 4,
  LightNaturalDot.body,LightRadixDigit.body 5,LightSmallDivide.body]
def procs : Procs program 0 where
  lift := 1
  dot := 2
  rawDot := 3
  digit := 4
  divide := 5
  mainBody := rfl
  liftBody := rfl
  dotBody := rfl
  rawBody := rfl
  digitBody := rfl
  divideBody := rfl
end ThreeSum.LightSignedRowHash


