-- Prove2me | Definitions.Def_Submission_ThreeSum_LightIrreducibleFinder
-- name    : Submission_ThreeSum_LightIrreducibleFinder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:41:36.935232+00:00
-- url     : https://prove2.me/theorems/a419fcf7-6380-408e-8bde-2774bbfe3d37
-- title:
--   Light Irreducible Finder
-- statement:
--   Definitions and structural lemmas for Light Irreducible Finder, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightIrreducibleFinder.lean

import Definitions.Def_Submission_ThreeSum_LightExtensionFactorSearch
import Definitions.Def_Submission_ThreeSum_LightArgumentTable
import Definitions.Def_Submission_ThreeSum_TernaryExtensionSearchCorrect
import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryRowSelector
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip

set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightIrreducibleFinder
open Light ThreeSum.LightExtensionFactorPredicate
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
def atDegree (C : Layout) (e : ℕ) : Layout := {C with degree := e}
def factorFirst (C : Layout) (q : ℕ) (f : ℕ → ℕ) (e : ℕ) : ℕ :=
  LightPairSearch.first (LightPairSearch.goodCode q (LightExtensionFactorSearch.good (atDegree C e) f)) (q*q)
def factorTime (C : Layout) (q e : ℕ) : ℕ := q*q*(LightExtensionFactorPredicate.time (atDegree C e) q q+200)+100
def degreeFlag (C : Layout) (q : ℕ) (f : ℕ → ℕ) (j : ℕ) : ℕ :=
  if ∀ t<j, factorFirst C q f (t+1)=0 then 1 else 0
def degreeRound : Stmt :=
  .call 11 [v 3,v 0,v 1,v 9 +' k 1,v 4,v 5,v 6,v 7] 10 ;;
  .call 9 [v 2,v 3] 11 ;;
  .ite (k 0 <' v 11) (.set 8 (k 0)) .skip
def degreeBody : Stmt := .set 8 (k 1) ;; .for 9 (v 1 -' k 1) degreeRound ;; .set 0 (v 8)
def degreeTime (dim T : ℕ) : ℕ := (dim-1)*(T+200)+100
def candidateBody : Stmt :=
  .call 2 [k 2 *' v 2,v 1,v 0 +' v 3,v 4,k 0,k 1,v 5,k 2 *' v 2] 9 ;;
  .call 10 [v 1,v 2,v 3,v 6,v 4,v 5,v 7,v 8] 0
def searchRound : Stmt :=
  .call 12 [v 10,v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7] 11 ;;
  .ite (v 11 =' k 1) (.set 9 (v 10 +' k 1)) .skip
def searchBody : Stmt := .set 9 (k 0) ;; .for 10 (v 2) searchRound ;; .set 0 (v 9)
def setupBody : Stmt :=
  .call 14 [v 3,k 2 *' v 1 +' k 1,v 0] 8 ;;
  .call 13 [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7] 9 ;;
  .call 2 [k 2 *' v 1,v 0,v 9 -' k 1 +' v 2,v 3,k 0,k 1,v 4,k 2 *' v 1] 10 ;;
  .set 0 (v 9)
def tail : Program := [degreeBody,LightArgumentTable.stores 0 7,candidateBody,searchBody,powTableBody,setupBody]
def program : Program := LightExtensionFactorSearch.program++tail
def DegreeInv (μ : ℕ → ℤ) (C : Layout) (q ctx : ℕ) (f : ℕ → ℕ) (j : ℕ) (σ : State) : Prop :=
  ∃ headerResult result : ℤ, ∃ ν : ℕ → ℤ,
    σ=⟨frame [C.p,C.dim,q,ctx,C.powers,C.target,C.left,C.right,degreeFlag C q f j,j,headerResult,result],ν⟩ ∧
      Kept μ ν ctx
variable {lim : Limits}
open TernaryExtensionEncoding
structure Budget (lim : Limits) (C : Layout) (q ctx T : ℕ) : Prop where
  qpos : 0<q
  primeBase : 1<C.p
  dimpos : 0<C.dim
  ctxLeft : ctx+7≤C.left
  powersTarget : C.powers+(2*C.dim+1)≤C.target
  targetCtx : C.target+2*C.dim≤ctx
  leftRight : C.left+2*C.dim≤C.right
  space : C.right+2*C.dim≤lim.space
  factorWord : ∀ e, 0<e → e<C.dim → (LightExtensionFactorPredicate.word (atDegree C e) q q : ℤ)≤lim.word
  searchWord : ((q*q+q+ctx+20 : ℕ) : ℤ)≤lim.word
  controls : ((C.p+C.dim+q+ctx+32 : ℕ) : ℤ)≤lim.word
  decodeWord : (LightCoefficientDecode.word (2*C.dim) C.p (2*q) 0 1 : ℤ)≤lim.word
  factorTime : ∀ e, 0<e → e<C.dim → LightIrreducibleFinder.factorTime C q e≤T
def candidateTime (C : Layout) (q T : ℕ) : ℕ :=
  LightCoefficientDecode.time (2*C.dim) (2*q)+degreeTime C.dim T+200
def accepted (C : Layout) (q c : ℕ) : Prop :=
  degreeFlag C q (LightCoefficientDecode.digit C.p (c+q)) (C.dim-1)=1
def chosen (C : Layout) (q n : ℕ) : ℕ := LightTernaryRowSelector.pick (accepted C q) n
def searchTime (C : Layout) (q T : ℕ) : ℕ := q*(candidateTime C q T+200)+100
def SearchInv (μ : ℕ → ℤ) (C : Layout) (q ctx : ℕ) (j : ℕ) (σ : State) : Prop :=
  ∃ result : ℤ, ∃ ν : ℕ → ℤ,
    σ=⟨frame [C.p,C.dim,q,C.powers,C.target,ctx,C.left,C.right,0,chosen C q j,j,result],ν⟩ ∧
      Kept μ ν C.target
def setupTime (C : Layout) (q T : ℕ) : ℕ :=
  powTableTime (2*C.dim+1)+searchTime C q T+LightCoefficientDecode.time (2*C.dim) (2*q)+300
end ThreeSum.LightIrreducibleFinder


