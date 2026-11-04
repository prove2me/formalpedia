-- Prove2me | Definitions.Def_Submission_ThreeSum_LightBandRawA
-- name    : Submission_ThreeSum_LightBandRawA
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:28:56.522199+00:00
-- url     : https://prove2.me/theorems/7607d122-f450-4302-b1a0-af4245f5844e
-- title:
--   Light Band Raw A
-- statement:
--   Definitions and structural lemmas for Light Band Raw A, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawA.lean

import Definitions.Def_Submission_ThreeSum_LightBandRawAStep
import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set

set_option autoImplicit false
namespace ThreeSum.LightBandRawA
open Light BandCandidateRows BandRawA
set_option maxHeartbeats 2200000
set_option maxRecDepth 8000
def capacity (N g : ℕ) : ℕ := g*N
def ownerBase (vals N g : ℕ) : ℕ := vals+capacity N g
def positionBase (vals N g : ℕ) : ℕ := ownerBase vals N g+capacity N g
def space (vals N g : ℕ) : ℕ := positionBase vals N g+capacity N g
def word (n g N : ℕ) : ℕ := n+g+N+20
def time (N g : ℕ) : ℕ := N*(LightBandRawAStep.time g+200)+100
def body (pStep : ℕ) : Stmt :=
  .set 6 (v 4 *' v 1) ;;
  .set 7 (v 5 +' v 6) ;;
  .set 8 (v 7 +' v 6) ;;
  .set 9 (k 0) ;;
  .for 10 (v 1) (
    .set 11 (M (v 0 +' k 4 *' v 10)) ;;
    .set 12 (M (v 0 +' k 4 *' v 10 +' k 1)) ;;
    .call pStep [v 2,v 3,v 4,v 11,v 12,v 10,v 5,v 7,v 8,v 9] 9) ;;
  .set 0 (v 9)
def Inv (μ : ℕ → ℤ) (rs : List Record) (f : ℕ → ℤ)
    (records src n g vals i : ℕ) (σ : State) : Prop :=
  ∃ (flag a : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [records,rs.length,src,n,g,vals,capacity rs.length g,
      ownerBase vals rs.length g,positionBase vals rs.length g,count n g rs i,i,flag,a],ν⟩ ∧
    Stored ν vals (ownerBase vals rs.length g) (positionBase vals rs.length g)
      f (firstRows n g rs i) ∧ Kept μ ν vals
structure Procs (P : Program) (pMain : ℕ) where
  pStep : ℕ
  pRow : ℕ
  pCopy : ℕ
  pFill : ℕ
  step : P[pStep]?=some (LightBandRawAStep.body pRow)
  row : P[pRow]?=some (LightBandRawARow.body pCopy pFill)
  copy : P[pCopy]?=some copyBody
  fill : P[pFill]?=some fillBody
  main : P[pMain]?=some (body pStep)
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {records src n g vals : ℕ} {rs : List Record} {f : ℕ → ℤ}
def program : Program :=
  [body 1,LightBandRawAStep.body 2,LightBandRawARow.body 3 4,copyBody,fillBody]
def programProcs : Procs program 0 := ⟨1,2,3,4,rfl,rfl,rfl,rfl,rfl⟩
end ThreeSum.LightBandRawA


