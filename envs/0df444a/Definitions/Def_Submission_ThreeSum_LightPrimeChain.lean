-- Prove2me | Definitions.Def_Submission_ThreeSum_LightPrimeChain
-- name    : Submission_ThreeSum_LightPrimeChain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:51:11.364869+00:00
-- url     : https://prove2.me/theorems/eb13959a-c6bb-47d8-a841-4693d9c68b0d
-- title:
--   Light Prime Chain
-- statement:
--   Definitions and structural lemmas for Light Prime Chain, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimeChain.lean

import Definitions.Def_Submission_ThreeSum_LightPrimeMinimum
import Definitions.Def_Submission_ThreeSum_PrimeChain
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_store
import Theorems.Thm_ThreeSum_LightCyclic_program_procs
import Theorems.Thm_ThreeSum_LightKaratsuba_program_procs

set_option autoImplicit false
namespace ThreeSum.LightPrimeChain
open Light WeightedScore LightPrimeMinimum Finset
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
def modulus (primes : ℕ → ℕ) (s nA nB nC : ℕ) (A B C : ℕ → ℤ) : ℕ → ℕ
  | 0 => 1
  | r+1 =>
    let q := modulus primes s nA nB nC A B C r
    q * chosenPrime primes s q nA nB nC A B C
def body (pMinimum : ℕ) : Stmt :=
  .set 11 (k 1) ;;
  .set 14 (v 10 +' v 9 +' k 1) ;;
  .store (v 10) (v 11) ;;
  .for 12 (v 9) (
    .call pMinimum [v 0,v 1,v 2,v 3,v 4,v 5,v 11,v 6,v 7,v 8,v 14] 13 ;;
    .set 11 (v 11 *' v 13) ;;
    .store (v 10 +' v 12 +' k 1) (v 11)) ;;
  .set 0 (v 11)
def time (maxMod nA nB nC s U levels : ℕ) : ℕ :=
  levels*(LightPrimeMinimum.time maxMod nA nB nC s U+100)+100
def space (free maxMod N U levels : ℕ) : ℕ :=
  LightWeightedScore.space (free+levels+1) maxMod N U
def Inv (μ : ℕ → ℤ) (qs : ℕ → ℕ)
    (a b c nA nB nC N aux s levels free : ℕ) (i : ℕ) (σ : State) : Prop :=
  ∃ (pval : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [(a : ℤ),b,c,nA,nB,nC,N,aux,s,levels,free,
      qs i,i,pval,free+levels+1],ν⟩ ∧
      (∀ j ≤ i, ν (free+j) = (qs j : ℤ)) ∧ Kept μ ν free
structure Procs (P : Program) (pMain : ℕ) where
  pMinimum : ℕ
  minimum : LightPrimeMinimum.Procs P pMinimum
  main : P[pMain]? = some (body pMinimum)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1, LightPrimeMinimum.body 2, LightWeightedScore.body 4 3,
    LightWeightedScore.jointBody 8, LightModuloCounts.body 5 6 10 7 15,
    LightCapacity.body, LightResidueHistogram.body 7 9, LightResidues.residuesBody 8,
    emodBody, LightHistogram.histogramBody 14, LightCyclic.body 11 13,
    LightKaratsuba.body 11 12 13 14, halfBody, LightArray.linearBody, fillBody,
    LightLookupSum.body]
def program_count_procs : LightModuloCounts.Procs program 4 where
  pCapacity := 5
  pHist := 6
  pCyclic := 10
  pResidues := 7
  pEmod := 8
  pHistogram := 9
  pMultiply := 11
  pHalf := 12
  pLinear := 13
  pFill := 14
  pLookup := 15
  main := rfl
  capacity := rfl
  hist := rfl
  residues := rfl
  emod := rfl
  histogram := rfl
  cyclic := rfl
  multiply := ⟨rfl,rfl,rfl,rfl⟩
  lookup := rfl
def program_score_procs : LightWeightedScore.Procs program 2 where
  pCount := 4
  pJoint := 3
  count := program_count_procs
  main := rfl
  joint := rfl
def program_minimum_procs : LightPrimeMinimum.Procs program 1 where
  pScore := 2
  score := program_score_procs
  main := rfl
def program_procs : Procs program 0 where
  pMinimum := 1
  minimum := program_minimum_procs
  main := rfl
end ThreeSum.LightPrimeChain


