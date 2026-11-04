-- Prove2me | Definitions.Def_Submission_ThreeSum_LightExtensionFactorCheck
-- name    : Submission_ThreeSum_LightExtensionFactorCheck
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:59:41.585107+00:00
-- url     : https://prove2.me/theorems/cf536eb6-265d-49ea-af3c-60af5ffca91c
-- title:
--   Light Extension Factor Check
-- statement:
--   Definitions and structural lemmas for Light Extension Factor Check, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionFactorCheck.lean

import Definitions.Def_Submission_ThreeSum_LightPolynomialProductCheck
import Definitions.Def_Submission_ThreeSum_LightCoefficientDecode
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightExtensionFactorCheck
open Light
set_option maxHeartbeats 2000000
def body (pDecode pCheck : ℕ) : Stmt :=
  .set 9 (k 2 *' v 3) ;;
  .call pDecode [v 9,v 2,v 0,v 5,k 0,k 1,v 7,v 9] 10 ;;
  .call pDecode [v 9,v 2,v 1,v 5,k 0,k 1,v 8,v 9] 10 ;;
  .call pCheck [v 7,v 8,v 6,v 4 +' k 1,v 3 -' v 4 +' k 1,v 9,v 2] 0
def digits (p code : ℕ) (i : ℕ) : ℕ := LightCoefficientDecode.digit p code i
def time (d e p u v : ℕ) : ℕ := LightCoefficientDecode.time (2*d) u+
  LightCoefficientDecode.time (2*d) v+LightPolynomialProductCheck.time (e+1) p (2*d)+300
def word (d e p u v : ℕ) : ℕ := LightCoefficientDecode.word (2*d) p u 0 1+
  LightCoefficientDecode.word (2*d) p v 0 1+
  20*((e+2)*(p+1)^2+2*d+(d-e+1)+10)+100
structure Procs (P : Program) (main : ℕ) where
  decode : ℕ
  check : ℕ
  digit : ℕ
  divide : ℕ
  coefficient : ℕ
  raw : ℕ
  mainBody : P[main]?=some (body decode check)
  decodeBody : P[decode]?=some (LightCoefficientDecode.body digit)
  checkBody : P[check]?=some (LightPolynomialProductCheck.body coefficient)
  coefficientBody : P[coefficient]?=some (LightPolynomialCoefficient.reducedBody raw digit)
  rawBody : P[raw]?=some LightPolynomialCoefficient.body
  digitBody : P[digit]?=some (LightRadixDigit.body divide)
  divideBody : P[divide]?=some LightSmallDivide.body
variable {lim : Limits} {P : Program} {depth : ℕ}
end ThreeSum.LightExtensionFactorCheck


