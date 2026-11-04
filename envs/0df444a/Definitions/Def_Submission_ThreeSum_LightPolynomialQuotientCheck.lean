-- Prove2me | Definitions.Def_Submission_ThreeSum_LightPolynomialQuotientCheck
-- name    : Submission_ThreeSum_LightPolynomialQuotientCheck
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:09:22.28023+00:00
-- url     : https://prove2.me/theorems/ef771690-8c50-46a1-8f3e-65c17cf34deb
-- title:
--   Light Polynomial Quotient Check
-- statement:
--   Definitions and structural lemmas for Light Polynomial Quotient Check, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPolynomialQuotientCheck.lean

import Definitions.Def_Submission_ThreeSum_LightPolynomialProductArray
import Definitions.Def_Submission_ThreeSum_LightPolynomialProductCheck
import Definitions.Def_Submission_ThreeSum_LightPrimeAddArray
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightPolynomialQuotientCheck
open Light
set_option maxHeartbeats 3000000
def body (pProduct pAdd pCheck : ℕ) : Stmt :=
  .set 9 (k 2 *' v 5) ;;
  .call pProduct [v 2,v 3,v 5,v 5 +' k 1,v 9,v 6,v 7] 10 ;;
  .call pAdd [v 7,v 4,v 8,v 9,v 6] 10 ;;
  .call pCheck [v 0,v 1,v 8,v 5,v 5,v 9,v 6] 0
def expected (p d : ℕ) (h f r : ℕ → ℕ) (i : ℕ) : ℕ :=
  (LightPolynomialCoefficient.coefficient p h f d (d+1) i+r i)%p
def time (d p : ℕ) : ℕ := LightPolynomialProductArray.time d p (2*d)+
  LightPrimeAddArray.time (2*d) p+LightPolynomialProductCheck.time d p (2*d)+100
def word (d p : ℕ) : ℕ := 100*((d+2)*(p+1)^2+4*d+p+20)
structure Procs (P : Program) (main : ℕ) where
  product : ℕ
  add : ℕ
  check : ℕ
  coefficient : ℕ
  raw : ℕ
  digit : ℕ
  divide : ℕ
  mulAdd : ℕ
  mainBody : P[main]?=some (body product add check)
  productBody : P[product]?=some (LightPolynomialProductArray.body coefficient)
  addBody : P[add]?=some (LightPrimeAddArray.body mulAdd)
  checkBody : P[check]?=some (LightPolynomialProductCheck.body coefficient)
  coefficientBody : P[coefficient]?=some (LightPolynomialCoefficient.reducedBody raw digit)
  rawBody : P[raw]?=some LightPolynomialCoefficient.body
  digitBody : P[digit]?=some (LightRadixDigit.body divide)
  divideBody : P[divide]?=some LightSmallDivide.body
  mulAddBody : P[mulAdd]?=some (LightPrimeCoefficient.mulAddBody divide)
variable {lim : Limits} {P : Program} {depth : ℕ}
end ThreeSum.LightPolynomialQuotientCheck


