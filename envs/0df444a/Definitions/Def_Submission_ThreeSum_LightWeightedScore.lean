-- Prove2me | Definitions.Def_Submission_ThreeSum_LightWeightedScore
-- name    : Submission_ThreeSum_LightWeightedScore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:44:42.278517+00:00
-- url     : https://prove2.me/theorems/747d077a-c512-43d1-9433-8beab4ead6fa
-- title:
--   Light Weighted Score
-- statement:
--   Definitions and structural lemmas for Light Weighted Score, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightedScore.lean

import Definitions.Def_Submission_ThreeSum_WeightedScore
import Definitions.Def_Submission_ThreeSum_ModuloRuntime
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_ThreeSum_LightCyclic_program_procs
import Theorems.Thm_ThreeSum_LightKaratsuba_program_procs

set_option autoImplicit false
namespace ThreeSum.LightWeightedScore
open Light WeightedModuli WeightedScore LightResidues
variable {lim : Limits} {P : Program} {d : ℕ}
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
def jointBody (pEmod : ℕ) : Stmt :=
  .call pEmod [v 0, v 1, v 2] 3 ;;
  .ite (v 3 =' k 0) .skip (.set 0 (v 0 *' v 1))
def jointTime (maxMod : ℕ) : ℕ := residueBudget maxMod + 40
def body (pCount pJoint : ℕ) : Stmt :=
  .call pCount [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 10] 11 ;;
  .set 12 (v 9 *' v 11) ;;
  .for 13 (v 9) (
    .call pJoint [v 6,M (v 8 +' v 13),v 10] 14 ;;
    .call pCount [v 0,v 1,v 2,v 3,v 4,v 5,v 14,v 7,v 10] 15 ;;
    .set 12 (v 12 -' v 15)) ;;
  .set 0 (v 12)
def time (countTime s maxMod : ℕ) : ℕ :=
  countTime + s*(countTime+jointTime maxMod+100)+100
def Inv (μ : ℕ → ℤ) (primes : ℕ → ℕ)
    (a b c nA nB nC q N aux s free : ℕ) (i : ℕ) (σ : State) : Prop :=
  ∃ (jval cval : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [(a : ℤ),b,c,nA,nB,nC,q,N,aux,s,free,
      ModuloCounts.count q nA nB nC (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)),
      remaining primes s q nA nB nC (fun j => μ (a+j)) (fun j => μ (b+j))
        (fun j => μ (c+j)) i,i,jval,cval],ν⟩ ∧ Kept μ ν free
def runtimeTime (maxMod nA nB nC s U : ℕ) : ℕ :=
  time (LightModuloCounts.time maxMod nA nB nC U) s maxMod
def space (free maxMod N U : ℕ) : ℕ :=
  max (LightModuloCounts.space free maxMod N U)
    (free + (Nat.log 2 (maxMod+1)+2))
def word (maxMod N s U : ℕ) : ℕ :=
  LightModuloCounts.word maxMod N U + (s+1)*N^3 + 8*maxMod + 16
structure Procs (P : Program) (pMain : ℕ) where
  pCount : ℕ
  pJoint : ℕ
  count : LightModuloCounts.Procs P pCount
  main : P[pMain]? = some (body pCount pJoint)
  joint : P[pJoint]? = some (jointBody count.pEmod)
def program : Program :=
  [body 2 1, jointBody 6, LightModuloCounts.body 3 4 8 5 13,
    LightCapacity.body, LightResidueHistogram.body 5 7, residuesBody 6,
    emodBody, LightHistogram.histogramBody 12, LightCyclic.body 9 11,
    LightKaratsuba.body 9 10 11 12, halfBody, LightArray.linearBody, fillBody,
    LightLookupSum.body]
def program_count_procs : LightModuloCounts.Procs program 2 where
  pCapacity := 3
  pHist := 4
  pCyclic := 8
  pResidues := 5
  pEmod := 6
  pHistogram := 7
  pMultiply := 9
  pHalf := 10
  pLinear := 11
  pFill := 12
  pLookup := 13
  main := rfl
  capacity := rfl
  hist := rfl
  residues := rfl
  emod := rfl
  histogram := rfl
  cyclic := rfl
  multiply := ⟨rfl,rfl,rfl,rfl⟩
  lookup := rfl
def program_procs : Procs program 0 where
  pCount := 2
  pJoint := 1
  count := program_count_procs
  main := rfl
  joint := rfl
end ThreeSum.LightWeightedScore


