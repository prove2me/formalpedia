-- Prove2me | Definitions.Def_Submission_ThreeSum_LightExtensionQuotientPredicate
-- name    : Submission_ThreeSum_LightExtensionQuotientPredicate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:12:52.727387+00:00
-- url     : https://prove2.me/theorems/ce23d578-c1c9-44a9-a228-dad9b3520c38
-- title:
--   Light Extension Quotient Predicate
-- statement:
--   Definitions and structural lemmas for Light Extension Quotient Predicate, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionQuotientPredicate.lean

import Definitions.Def_Submission_ThreeSum_LightPolynomialQuotientCheck
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Seg_get

set_option autoImplicit false
namespace ThreeSum.LightExtensionQuotientPredicate
open Light
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000
structure Layout where
  p : ℕ
  dim : ℕ
  powers : ℕ
  a : ℕ
  b : ℕ
  modulus : ℕ
  h : ℕ
  remainder : ℕ
  productWork : ℕ
  sumWork : ℕ
def header (C : Layout) : List ℤ :=
  [C.p,C.dim,C.powers,C.a,C.b,C.modulus,C.h,C.remainder,C.productWork,C.sumWork]
def get (offset : ℕ) : Expr := M (v 2 +' k offset)
def body (pDecode pCore : ℕ) : Stmt :=
  .call pDecode [get 1,get 0,v 0,get 2,k 0,k 1,get 6,get 1] 3 ;;
  .call pDecode [k 2 *' get 1,get 0,v 1,get 2,k 0,k 1,get 7,k 2 *' get 1] 3 ;;
  .call pCore [get 3,get 4,get 6,get 5,get 7,get 1,get 0,get 8,get 9] 0
def time (d p u v : ℕ) : ℕ := LightCoefficientDecode.time d u+
  LightCoefficientDecode.time (2*d) v+LightPolynomialQuotientCheck.time d p+500
def word (d p u v : ℕ) : ℕ := LightCoefficientDecode.word d p u 0 1+
  LightCoefficientDecode.word (2*d) p v 0 1+LightPolynomialQuotientCheck.word d p+100
def digits (p code : ℕ) (i : ℕ) : ℕ := LightCoefficientDecode.digit p code i
noncomputable def result (C : Layout) (x y f : ℕ → ℕ) (u v : ℕ) : ℤ :=
  LightPolynomialProductCheck.flag C.p x y
    (LightPolynomialQuotientCheck.expected C.p C.dim (digits C.p u) f (digits C.p v))
    C.dim C.dim (2*C.dim)
structure Procs (P : Program) (main : ℕ) where
  decode : ℕ
  digit : ℕ
  divide : ℕ
  core : ℕ
  mainBody : P[main]?=some (body decode core)
  decodeBody : P[decode]?=some (LightCoefficientDecode.body digit)
  digitBody : P[digit]?=some (LightRadixDigit.body divide)
  divideBody : P[divide]?=some LightSmallDivide.body
  coreProcs : LightPolynomialQuotientCheck.Procs P core
variable {lim : Limits} {P : Program} {depth : ℕ}
def program : Program :=
  [body 1 4, LightCoefficientDecode.body 2,LightRadixDigit.body 3,LightSmallDivide.body,
    LightPolynomialQuotientCheck.body 5 6 7,LightPolynomialProductArray.body 8,
    LightPrimeAddArray.body 10,LightPolynomialProductCheck.body 8,
    LightPolynomialCoefficient.reducedBody 9 2,LightPolynomialCoefficient.body,
    LightPrimeCoefficient.mulAddBody 3]
def procs : Procs program 0 where
  decode := 1
  digit := 2
  divide := 3
  core := 4
  mainBody := rfl
  decodeBody := rfl
  digitBody := rfl
  divideBody := rfl
  coreProcs := {
    product := 5, add := 6, check := 7, coefficient := 8, raw := 9,
    digit := 2, divide := 3, mulAdd := 10,
    mainBody := rfl,productBody := rfl,addBody := rfl,checkBody := rfl,
    coefficientBody := rfl,rawBody := rfl,digitBody := rfl,divideBody := rfl,mulAddBody := rfl }
end ThreeSum.LightExtensionQuotientPredicate


