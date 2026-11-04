-- Prove2me | Definitions.Def_Submission_ThreeSum_LightExtensionFactorPredicate
-- name    : Submission_ThreeSum_LightExtensionFactorPredicate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:03:35.770605+00:00
-- url     : https://prove2.me/theorems/481d1891-3a27-4aac-9603-fd8b8d619ced
-- title:
--   Light Extension Factor Predicate
-- statement:
--   Definitions and structural lemmas for Light Extension Factor Predicate, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionFactorPredicate.lean

import Definitions.Def_Submission_ThreeSum_LightExtensionFactorCheck
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Seg_get

set_option autoImplicit false
namespace ThreeSum.LightExtensionFactorPredicate
open Light
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000
noncomputable local instance _p2m_local_instance_595e8f8b6a_7 (Q : Prop) : Decidable Q := Classical.propDecidable Q
structure Layout where
  p : ℕ
  dim : ℕ
  degree : ℕ
  powers : ℕ
  target : ℕ
  left : ℕ
  right : ℕ
def header (C : Layout) : List ℤ := [C.p,C.dim,C.degree,C.powers,C.target,C.left,C.right]
def get (i : ℕ) : Expr := M (v 2 +' k i)
def body (pCore : ℕ) : Stmt :=
  .set 3 (M (get 3 +' get 2)) ;;
  .set 4 (M (get 3 +' get 1 -' get 2)) ;;
  .ite (v 0 <' v 3)
    (.ite (v 1 <' v 4)
      (.call pCore [v 0 +' v 3,v 1 +' v 4,get 0,get 1,get 2,get 3,get 4,get 5,get 6] 0)
      (.set 0 (k 0)))
    (.set 0 (k 0))
noncomputable def result (C : Layout) (f : ℕ → ℕ) (u v : ℕ) : ℤ :=
  if u<C.p^C.degree ∧ v<C.p^(C.dim-C.degree) then
    LightPolynomialProductCheck.flag C.p
      (LightExtensionFactorCheck.digits C.p (u+C.p^C.degree))
      (LightExtensionFactorCheck.digits C.p (v+C.p^(C.dim-C.degree))) f
      (C.degree+1) (C.dim-C.degree+1) (2*C.dim)
  else 0
def time (C : Layout) (u v : ℕ) : ℕ :=
  LightExtensionFactorCheck.time C.dim C.degree C.p (u+C.p^C.degree) (v+C.p^(C.dim-C.degree))+200
def word (C : Layout) (u v : ℕ) : ℕ :=
  LightExtensionFactorCheck.word C.dim C.degree C.p (u+C.p^C.degree) (v+C.p^(C.dim-C.degree))+100
structure Procs (P : Program) (main : ℕ) where
  core : ℕ
  mainBody : P[main]?=some (body core)
  coreProcs : LightExtensionFactorCheck.Procs P core
variable {lim : Limits} {P : Program} {depth : ℕ}
def program : Program :=
  [body 1,LightExtensionFactorCheck.body 2 5,LightCoefficientDecode.body 3,
    LightRadixDigit.body 4,LightSmallDivide.body,LightPolynomialProductCheck.body 6,
    LightPolynomialCoefficient.reducedBody 7 3,LightPolynomialCoefficient.body]
def procs : Procs program 0 where
  core := 1
  mainBody := rfl
  coreProcs := {
    decode := 2, check := 5, digit := 3, divide := 4, coefficient := 6, raw := 7,
    mainBody := rfl,decodeBody := rfl,checkBody := rfl,coefficientBody := rfl,
    rawBody := rfl,digitBody := rfl,divideBody := rfl }
end ThreeSum.LightExtensionFactorPredicate


