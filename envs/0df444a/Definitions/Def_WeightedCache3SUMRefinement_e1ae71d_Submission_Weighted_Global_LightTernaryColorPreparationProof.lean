-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColorPreparationProof
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColorPreparationProof
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T11:48:55.567037+00:00
-- url     : https://prove2.me/theorems/d93efeb1-834f-408c-ab3c-ebdfc266e0d9
-- title:
--   LightTernaryColorPreparationProof
-- statement:
--   Definitions and structural lemmas for LightTernaryColorPreparationProof, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryColorPreparationProof.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColorPreparationLayout
import Theorems.Thm_Light_LocalsBut_update

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.LightWeightedGlobalColorPreparationProof
open Light LightWeightedGlobalColorPreparation
open LightColorParametersCosts
set_option maxHeartbeats 12000000
set_option maxRecDepth 24000
def colorLibrary (radix : ℕ) : LightColorBands.Procs (program radix) 20 where
  pClasses:=21
  pBands:=0
  classes:=⟨22,23,24,25,26,rfl,rfl,rfl,rfl,rfl,rfl⟩
  bands:={
    pPrepare:=1
    pEnumerate:=12
    prepare:=⟨2,8,9,10,11,⟨3,4,5,6,7,⟨rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl⟩
    enumerate:=⟨13,⟨14,15,16,17,18,19,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩
    main:=rfl }
  main:=rfl
def leftProcs (radix : ℕ) :
    LightTernarySignedMatrix.Procs (program radix) 28 false :=
  ⟨29,⟨30,31,rfl,rfl,rfl⟩,rfl⟩
def rightProcs (radix : ℕ) :
    LightTernarySignedMatrix.Procs (program radix) 32 true :=
  ⟨33,⟨34,35,rfl,rfl,rfl⟩,rfl⟩
def requesterProcs (radix : ℕ) :
    LightTernaryRequesterMatrix.Procs (program radix) 49 where
  inner:=48
  requester:=42
  mainBody:=rfl
  innerBody:=rfl
  requesterProcs:={
    pRow:=43,pApply:=46,pLinear:=47,
    row:=⟨44,45,rfl,rfl,rfl⟩,
    correction:=rfl,linear:=rfl,main:=rfl }
noncomputable def patch (base : ℕ) (loc : ℕ→ℤ) : (ℕ→ℤ)→ℕ→List ℕ→(ℕ→ℤ)
  | μ,_,[]=>μ
  | μ,offset,r::rs=>patch base loc (Function.update μ (base+offset) (loc r)) (offset+1) rs
structure Bounds (lim : Limits) (radix n U J depth : ℕ) : Prop where
  hw : (lim.space:ℤ)≤lim.word
  colorWord : (LightTernaryColorPrelude.word n U:ℤ)≤lim.word
  matrixWord : (LightTernarySignedMatrix.word U radix J:ℤ)≤lim.word
  carryWord : (LightTernaryCarryCodes.word J (2^J):ℤ)≤lim.word
  colorDepth : depth+1+LightTernaryColorPrelude.depth n≤lim.depth
  kernelDepth : depth+7<lim.depth
def header (free n U R J q menu : ℕ) (A B C : List ℤ) : List ℤ :=
  let W:=width n
  [LightTernaryColorPrelude.av free n,A.length,
    LightTernaryColorPrelude.bv free n,B.length,
    LightTernaryColorPrelude.cv free n,C.length,
    bMatrix free n W,cMatrix free n W B.length J,
    oMatrix free n W A.length B.length C.length J,A.length*2^J,
    positions free n W A.length B.length C.length J,
    carry free n W A.length B.length C.length J,
    work free n W A.length B.length C.length J,
    arenaFree free n W A.length B.length C.length J U,U,R,J,q,menu]
structure Matrices (ν : ℕ→ℤ) (free n U J radix : ℕ) (A B C : List ℤ) : Prop where
  left : LightTernarySignedMatrix.Rows ν (bMatrix free n (width n)) B.length J
    (fun i=>TernarySignedReduction.leftRaw U radix J (B.getD i 0))
  right : LightTernarySignedMatrix.Rows ν (cMatrix free n (width n) B.length J) C.length J
    (fun i=>TernarySignedReduction.rightRaw U radix J (C.getD i 0))
  carries : LightTernaryCarryCodes.Table ν
    (carry free n (width n) A.length B.length C.length J) J (2^J)
  requesters : LightTernaryRequesterMatrix.Entries ν
    (positions free n (width n) A.length B.length C.length J)
    (oMatrix free n (width n) A.length B.length C.length J)
    J (2^J) (A.length*2^J) U radix (fun i=>A.getD i 0)
def buildTime (a b c J U : ℕ) :=
  LightNatPower.time J+LightTernarySignedMatrix.time b J U+
    LightTernarySignedMatrix.time c J U+LightTernaryCarryCodes.time J+
    LightTernaryRequesterMatrix.time a (2^J) J U+5000
def time (n J U : ℕ) :=LightTernaryColorPrelude.time n+buildTime n n n J U+5000
structure Built (μ ν : ℕ→ℤ) (free n U R J q menu radix : ℕ) (A B C : List ℤ) : Prop where
  kept : Kept μ ν (headerAt free n (width n))
  header : Seg ν (headerAt free n (width n)) (header free n U R J q menu A B C)
  matrices : Matrices ν free n U J radix A B C
def space (free n J U : ℕ) :=arenaFree free n (width n) n n n J U
def Output {n : ℕ} (μ ν : ℕ→ℤ) (free U R J q menu radix : ℕ)
    (p : Coloring.Parameter (width n)) (x : Fin n→ℤ) (ret : ℤ) : Prop :=
  Kept μ ν free ∧ ∃A B C : List ℤ,
    LightTernaryColorPrelude.Normalized ν (LightTernaryColorPrelude.av free n) n
      (ColorClassLists.classList p x 0 1) A ∧
    LightTernaryColorPrelude.Normalized ν (LightTernaryColorPrelude.bv free n) n
      (ColorClassLists.classList p x 1 1) B ∧
    LightTernaryColorPrelude.Normalized ν (LightTernaryColorPrelude.cv free n) n
      (ColorClassLists.classList p x 2 (-1)) C ∧
    ((ret=0 ∧ (A=[] ∨ B=[] ∨ C=[])) ∨
      (ret=(headerAt free n (width n):ℤ) ∧ A≠[] ∧ B≠[] ∧ C≠[] ∧
        Seg ν (headerAt free n (width n)) (header free n U R J q menu A B C) ∧
        Matrices ν free n U J radix A B C))
end ThreeSum.LightWeightedGlobalColorPreparationProof
end WeightedCache3SUMRefinement_e1ae71d


