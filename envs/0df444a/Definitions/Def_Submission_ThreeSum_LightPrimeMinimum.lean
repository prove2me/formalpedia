-- Prove2me | Definitions.Def_Submission_ThreeSum_LightPrimeMinimum
-- name    : Submission_ThreeSum_LightPrimeMinimum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:47:56.063413+00:00
-- url     : https://prove2.me/theorems/51a872a6-dc28-479e-bd1f-fca46371cfe6
-- title:
--   Light Prime Minimum
-- statement:
--   Definitions and structural lemmas for Light Prime Minimum, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimeMinimum.lean

import Definitions.Def_Submission_ThreeSum_LightWeightedScore
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_ThreeSum_LightCyclic_program_procs
import Theorems.Thm_ThreeSum_LightKaratsuba_program_procs

set_option autoImplicit false
namespace ThreeSum.LightPrimeMinimum
open Light WeightedScore
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
def candidateScore (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (A B C : ℕ → ℤ) (i : ℕ) : ℤ :=
  (score primes s (q*primes i) nA nB nC A B C : ℤ)
def chosenIndex (primes : ℕ → ℕ) (s q nA nB nC : ℕ) (A B C : ℕ → ℤ) : ℕ :=
  LightMinimum.least (candidateScore primes s q nA nB nC A B C) s
def chosenPrime (primes : ℕ → ℕ) (s q nA nB nC : ℕ) (A B C : ℕ → ℤ) : ℕ :=
  primes (chosenIndex primes s q nA nB nC A B C)
def body (pScore : ℕ) : Stmt :=
  .call pScore [v 0,v 1,v 2,v 3,v 4,v 5,v 6 *' M (v 8),v 7,v 8,v 9,v 10] 11 ;;
  .set 12 (k 0) ;;
  .for 13 (v 9) (
    .call pScore [v 0,v 1,v 2,v 3,v 4,v 5,v 6 *' M (v 8 +' v 13),v 7,v 8,v 9,v 10] 14 ;;
    .ite (v 14 <' v 11) (.set 11 (v 14) ;; .set 12 (v 13)) .skip) ;;
  .set 0 (M (v 8 +' v 12))
def time (maxMod nA nB nC s U : ℕ) : ℕ :=
  LightWeightedScore.runtimeTime maxMod nA nB nC s U +
    s*(LightWeightedScore.runtimeTime maxMod nA nB nC s U+100)+100
def Inv (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (a b c nA nB nC q N aux s free : ℕ) (i : ℕ) (σ : State) : Prop :=
  ∃ (rval : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [(a : ℤ),b,c,nA,nB,nC,q,N,aux,s,free,
      f (LightMinimum.least f i), LightMinimum.least f i,i,rval],ν⟩ ∧ Kept μ ν free
structure Procs (P : Program) (pMain : ℕ) where
  pScore : ℕ
  score : LightWeightedScore.Procs P pScore
  main : P[pMain]? = some (body pScore)
variable {lim : Limits} {P : Program} {d : ℕ}
def program : Program :=
  [body 1, LightWeightedScore.body 3 2, LightWeightedScore.jointBody 7,
    LightModuloCounts.body 4 5 9 6 14, LightCapacity.body,
    LightResidueHistogram.body 6 8, LightResidues.residuesBody 7, emodBody,
    LightHistogram.histogramBody 13, LightCyclic.body 10 12,
    LightKaratsuba.body 10 11 12 13, halfBody, LightArray.linearBody, fillBody,
    LightLookupSum.body]
def program_count_procs : LightModuloCounts.Procs program 3 where
  pCapacity := 4
  pHist := 5
  pCyclic := 9
  pResidues := 6
  pEmod := 7
  pHistogram := 8
  pMultiply := 10
  pHalf := 11
  pLinear := 12
  pFill := 13
  pLookup := 14
  main := rfl
  capacity := rfl
  hist := rfl
  residues := rfl
  emod := rfl
  histogram := rfl
  cyclic := rfl
  multiply := ⟨rfl,rfl,rfl,rfl⟩
  lookup := rfl
def program_score_procs : LightWeightedScore.Procs program 1 where
  pCount := 3
  pJoint := 2
  count := program_count_procs
  main := rfl
  joint := rfl
def program_procs : Procs program 0 where
  pScore := 1
  score := program_score_procs
  main := rfl
end ThreeSum.LightPrimeMinimum


