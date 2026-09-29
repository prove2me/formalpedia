-- Prove2me | Definitions.Def_Freiman_lowerInitialEntry
-- name    : Freiman_lowerInitialEntry
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T11:52:25.147804+00:00
-- url     : https://prove2.me/theorems/72336a49-7edd-469b-bd2a-887444438b66
-- title:
--   Freiman H entry: exact finite parameter and endpoint cases
-- statement:
--   Seven actual matrix parameter cases, three terminal parity classes, all84 fork comparisons,69 core comparisons (including28 exact equality rows),15 adjacent contacts, six explicit contained cores and the single virtual NN exception.
-- source:
--   Freiman report, prop:lc-H-entry; certificates/initial_covers/h_parameter_box.json, h_core.json, h_children_goodness.json. Exact source binding in ENTRY_DATA_BINDING.json.

import Definitions.Def_Freiman_lowerInitialSeamData

namespace Freiman
inductive LowerEntryClass where
  | threeEven | threeOdd | twoOdd
  deriving DecidableEq
noncomputable def lowerEntryDomain (p : LowerPair) : Prop :=
  (729/1024:ℝ) < lowerScale p ∧ lowerScale p < (225/289:ℝ) ∧
  (1/4:ℝ) < lowerRatio p.1 ∧ lowerRatio p.1 < (9/25:ℝ) ∧
  (1/4:ℝ) < lowerRatio p.2 ∧ lowerRatio p.2 < (4/13:ℝ)
noncomputable def lowerEntryContext (c : LowerEntryClass) (p : LowerPair) : Prop :=
  lowerNormalize p = p ∧ p.1.length % 2 = p.2.length % 2 ∧
  lowerEnds p.2 [3] ∧
  (match c with
   | .threeEven => lowerEnds p.1 [3] ∧ p.1.length % 2 = 0
   | .threeOdd => lowerEnds p.1 [3] ∧ p.1.length % 2 = 1
   | .twoOdd => lowerEnds p.1 [2] ∧ p.1.length % 2 = 1)
noncomputable def lowerEntryH (c : LowerEntryClass) (p : LowerPair) : Set ℝ :=
  let a := 4+prefixEval (p.1++[3,1,2,1,3]) lowerTau+prefixEval (p.2++[2,1,3]) lowerTau
  let b := 4+prefixEval (p.1++(if c=.twoOdd then [1,3] else [1,2,1,3])) lowerTau+
    prefixEval (p.2++[1,2,1,3]) lowerTau
  Set.Icc (min a b) (max a b)
noncomputable def lowerEntryMatrixBounds (m : LowerInitialMatrix × LowerInitialMatrix) : Prop :=
  0 < 32*m.1.d-27*m.2.d ∧ 0 < 15*m.2.d-17*m.1.d ∧
  0 < 4*m.1.c-m.1.d ∧ 0 < 9*m.1.d-25*m.1.c ∧
  0 < 4*m.2.c-m.2.d ∧ 0 < 4*m.2.d-13*m.2.c
noncomputable def lowerEntryAuxMatrices (x : ℝ) : LowerInitialMatrix × LowerInitialMatrix :=
  (lowerInitialMatMul (lowerInitialMatMul (lowerInitialWordMatrix [3,2,1,1]) (lowerInitialP false x))
    (lowerInitialWordMatrix [3,1,2]),
   lowerInitialMatMul (lowerInitialMatMul (lowerInitialWordMatrix [4,3,2,2]) (lowerInitialP false x))
    (lowerInitialWordMatrix [3]))
structure LowerEntryRow where
  upperWords : LowerPair
  lowerWords : LowerPair
  parity : ℕ
  strict : Bool
noncomputable def lowerEntryMargin (e : LowerEntryRow) (r s q : ℝ) : ℝ :=
  let a := prefixEval e.upperWords.1 lowerTau
  let b := prefixEval e.lowerWords.1 lowerTau
  let c := prefixEval e.upperWords.2 lowerTau
  let d := prefixEval e.lowerWords.2 lowerTau
  (-1:ℝ)^e.parity*(a-b)*(1+s*c)*(1+s*d)+
    q*((-1:ℝ)^e.parity*(c-d))*(1+r*a)*(1+r*b)
noncomputable def lowerEntryRowValid (e : LowerEntryRow) : Prop :=
  ∀ r ∈ Set.Icc (1/4:ℝ) (9/25), ∀ s ∈ Set.Icc (1/4:ℝ) (4/13),
    ∀ q ∈ Set.Icc (729/1024:ℝ) (225/289),
      if e.strict then 0 < lowerEntryMargin e r s q else lowerEntryMargin e r s q = 0

def lowerEntryGoodRows : LowerEntryClass → List LowerEntryRow
  | .threeEven => [
    ⟨([1,2,1,3],[1,2,1,3]),([1,1,3],[2,1,3]),0,true⟩,
    ⟨([1,2,1,3],[1,2,1,3]),([1,1,3],[2,1,2,1,3]),0,true⟩,
    ⟨([1,2,1,3],[1,2,1,3]),([1,1,2,1,3],[2,1,3]),0,true⟩,
    ⟨([1,2,1,3],[2,3]),([1,1,3],[1,1,3]),0,true⟩,
    ⟨([1,2,1,3],[2,3]),([1,1,3],[1,1,2,1,3]),0,true⟩,
    ⟨([1,2,1,3],[2,3]),([1,1,2,1,3],[1,1,3]),0,true⟩,
    ⟨([2,3],[1,1,1,3]),([2,1,3],[1,2,3]),0,true⟩,
    ⟨([2,3],[1,1,1,3]),([2,1,3],[1,2,2,1,3]),0,true⟩,
    ⟨([2,3],[1,1,1,3]),([2,1,2,1,3],[1,2,3]),0,true⟩,
    ⟨([2,3],[1,2,1,3]),([2,1,3],[1,1,3]),0,true⟩,
    ⟨([2,3],[1,2,1,3]),([2,1,3],[1,1,2,1,3]),0,true⟩,
    ⟨([2,3],[1,2,1,3]),([2,1,2,1,3],[1,1,3]),0,true⟩,
    ⟨([3,3],[1,1,1,3]),([3,1,2,1,3],[1,2,3]),0,true⟩,
    ⟨([3,3],[1,2,1,3]),([3,1,2,1,3],[1,1,3]),0,true⟩,
    ⟨([2,1,1,3],[2,3]),([2,2,3],[2,1,3]),0,true⟩,
    ⟨([2,1,1,3],[2,3]),([2,2,3],[2,1,2,1,3]),0,true⟩,
    ⟨([2,1,1,3],[2,3]),([2,2,2,1,3],[2,1,3]),0,true⟩,
    ⟨([2,2,1,3],[2,3]),([2,1,3],[2,1,3]),0,true⟩,
    ⟨([2,2,1,3],[2,3]),([2,1,3],[2,1,2,1,3]),0,true⟩,
    ⟨([2,2,1,3],[2,3]),([2,1,2,1,3],[2,1,3]),0,true⟩,
    ⟨([2,1,1,3],[3,3]),([2,2,3],[3,1,2,1,3]),0,true⟩,
    ⟨([2,1,1,3],[3,2,1,3]),([2,2,3],[3,1,2,1,3]),0,true⟩,
    ⟨([2,1,1,2,1,3],[3,3]),([2,2,3],[3,1,2,1,3]),0,true⟩,
    ⟨([2,2,1,3],[3,3]),([2,1,3],[3,1,2,1,3]),0,true⟩,
    ⟨([3,3],[2,1,1,3]),([3,1,2,1,3],[2,2,3]),0,true⟩,
    ⟨([3,3],[2,2,1,3]),([3,1,2,1,3],[2,1,3]),0,true⟩]
  | .threeOdd => [
    ⟨([1,1,3],[1,1,3]),([1,2,1,3],[2,3]),1,true⟩,
    ⟨([1,1,3],[1,1,2,1,3]),([1,2,1,3],[2,3]),1,true⟩,
    ⟨([1,1,2,1,3],[1,1,3]),([1,2,1,3],[2,3]),1,true⟩,
    ⟨([1,1,3],[2,1,3]),([1,2,1,3],[1,2,1,3]),1,true⟩,
    ⟨([1,1,3],[2,1,2,1,3]),([1,2,1,3],[1,2,1,3]),1,true⟩,
    ⟨([1,1,2,1,3],[2,1,3]),([1,2,1,3],[1,2,1,3]),1,true⟩,
    ⟨([2,1,3],[1,1,3]),([2,3],[1,2,1,3]),1,true⟩,
    ⟨([2,1,3],[1,1,2,1,3]),([2,3],[1,2,1,3]),1,true⟩,
    ⟨([2,1,2,1,3],[1,1,3]),([2,3],[1,2,1,3]),1,true⟩,
    ⟨([2,1,3],[1,2,3]),([2,3],[1,1,1,3]),1,true⟩,
    ⟨([2,1,3],[1,2,2,1,3]),([2,3],[1,1,1,3]),1,true⟩,
    ⟨([2,1,2,1,3],[1,2,3]),([2,3],[1,1,1,3]),1,true⟩,
    ⟨([3,1,2,1,3],[1,1,3]),([3,3],[1,2,1,3]),1,true⟩,
    ⟨([3,1,2,1,3],[1,2,3]),([3,3],[1,1,1,3]),1,true⟩,
    ⟨([2,1,3],[2,1,3]),([2,2,1,3],[2,3]),1,true⟩,
    ⟨([2,1,3],[2,1,2,1,3]),([2,2,1,3],[2,3]),1,true⟩,
    ⟨([2,1,2,1,3],[2,1,3]),([2,2,1,3],[2,3]),1,true⟩,
    ⟨([2,2,3],[2,1,3]),([2,1,1,3],[2,3]),1,true⟩,
    ⟨([2,2,3],[2,1,2,1,3]),([2,1,1,3],[2,3]),1,true⟩,
    ⟨([2,2,2,1,3],[2,1,3]),([2,1,1,3],[2,3]),1,true⟩,
    ⟨([2,1,3],[3,1,2,1,3]),([2,2,1,3],[3,3]),1,true⟩,
    ⟨([2,2,3],[3,1,2,1,3]),([2,1,1,3],[3,3]),1,true⟩,
    ⟨([2,2,3],[3,1,2,1,3]),([2,1,1,3],[3,2,1,3]),1,true⟩,
    ⟨([2,2,3],[3,1,2,1,3]),([2,1,1,2,1,3],[3,3]),1,true⟩,
    ⟨([3,1,2,1,3],[2,1,3]),([3,3],[2,2,1,3]),1,true⟩,
    ⟨([3,1,2,1,3],[2,2,3]),([3,3],[2,1,1,3]),1,true⟩]
  | .twoOdd => [
    ⟨([1,1,3],[1,1,3]),([1,3],[2,3]),1,true⟩,
    ⟨([1,1,3],[1,1,3]),([1,3],[2,2,1,3]),1,true⟩,
    ⟨([1,1,3],[1,1,3]),([1,2,1,3],[2,3]),1,true⟩,
    ⟨([1,1,3],[1,1,2,1,3]),([1,3],[2,3]),1,true⟩,
    ⟨([1,1,3],[1,1,2,1,3]),([1,3],[2,2,1,3]),1,true⟩,
    ⟨([1,1,3],[1,1,2,1,3]),([1,2,1,3],[2,3]),1,true⟩,
    ⟨([1,1,2,1,3],[1,1,3]),([1,3],[2,3]),1,true⟩,
    ⟨([1,1,2,1,3],[1,1,3]),([1,3],[2,2,1,3]),1,true⟩,
    ⟨([1,1,2,1,3],[1,1,3]),([1,2,1,3],[2,3]),1,true⟩,
    ⟨([1,1,3],[2,1,3]),([1,3],[1,2,1,3]),1,true⟩,
    ⟨([1,1,3],[2,1,2,1,3]),([1,3],[1,2,1,3]),1,true⟩,
    ⟨([1,1,2,1,3],[2,1,3]),([1,3],[1,2,1,3]),1,true⟩,
    ⟨([2,1,3],[1,1,3]),([2,3],[1,2,1,3]),1,true⟩,
    ⟨([2,1,3],[1,1,2,1,3]),([2,3],[1,2,1,3]),1,true⟩,
    ⟨([2,1,2,1,3],[1,1,3]),([2,3],[1,2,1,3]),1,true⟩,
    ⟨([2,1,3],[1,2,3]),([2,3],[1,1,1,3]),1,true⟩,
    ⟨([2,1,3],[1,2,2,1,3]),([2,3],[1,1,1,3]),1,true⟩,
    ⟨([2,1,2,1,3],[1,2,3]),([2,3],[1,1,1,3]),1,true⟩,
    ⟨([3,1,2,1,3],[1,1,3]),([3,3],[1,2,1,3]),1,true⟩,
    ⟨([3,1,2,1,3],[1,2,3]),([3,3],[1,1,1,3]),1,true⟩,
    ⟨([2,1,3],[2,1,3]),([2,2,1,3],[2,3]),1,true⟩,
    ⟨([2,1,3],[2,1,2,1,3]),([2,2,1,3],[2,3]),1,true⟩,
    ⟨([2,1,2,1,3],[2,1,3]),([2,2,1,3],[2,3]),1,true⟩,
    ⟨([2,2,3],[2,1,3]),([2,1,1,3],[2,3]),1,true⟩,
    ⟨([2,2,3],[2,1,2,1,3]),([2,1,1,3],[2,3]),1,true⟩,
    ⟨([2,2,2,1,3],[2,1,3]),([2,1,1,3],[2,3]),1,true⟩,
    ⟨([2,1,3],[3,1,2,1,3]),([2,2,1,3],[3,3]),1,true⟩,
    ⟨([2,2,3],[3,1,2,1,3]),([2,1,1,3],[3,3]),1,true⟩,
    ⟨([2,2,3],[3,1,2,1,3]),([2,1,1,3],[3,2,1,3]),1,true⟩,
    ⟨([2,2,3],[3,1,2,1,3]),([2,1,1,2,1,3],[3,3]),1,true⟩,
    ⟨([3,1,2,1,3],[2,1,3]),([3,3],[2,2,1,3]),1,true⟩,
    ⟨([3,1,2,1,3],[2,2,3]),([3,3],[2,1,1,3]),1,true⟩]

def lowerEntryCoreRows : LowerEntryClass → List LowerEntryRow
  | .threeEven => [
    ⟨([3,1,2,1,3],[2,1,3]),([3,1,2,1,3],[2,1,3]),0,false⟩,
    ⟨([3,3],[2,3]),([3,2,1,3],[2,3]),0,true⟩,
    ⟨([3,2,1,3],[2,3]),([3,2,1,3],[2,3]),0,false⟩,
    ⟨([3,2,1,3],[2,3]),([3,1,2,1,3],[2,1,3]),0,true⟩,
    ⟨([2,1,3],[3]),([2,1,3],[3,1,2,1,3]),0,true⟩,
    ⟨([2,3],[3,3]),([2,3],[3,2,1,3]),0,true⟩,
    ⟨([2,3],[3,2,1,3]),([2,3],[3,2,1,3]),0,false⟩,
    ⟨([2,3],[3,2,1,3]),([2,1,3],[3]),0,true⟩,
    ⟨([2,1,3],[2,1,2,1,3]),([2,1,3],[2,1,3]),0,true⟩,
    ⟨([2,1,3],[2,1,2,1,3]),([2,1,3],[2,1,2,1,3]),0,false⟩,
    ⟨([2,3],[2,3]),([2,3],[2,2,1,3]),0,true⟩,
    ⟨([2,3],[2,2,1,3]),([2,3],[2,2,1,3]),0,false⟩,
    ⟨([2,3],[2,2,1,3]),([2,1,3],[2,1,2,1,3]),0,true⟩,
    ⟨([3],[1,1,3]),([3,1,2,1,3],[1,1,3]),0,true⟩,
    ⟨([3,3],[1,2,1,3]),([3,3],[1,2,1,3]),0,false⟩,
    ⟨([3,3],[1,2,1,3]),([3],[1,1,3]),0,true⟩,
    ⟨([2,1,2,1,3],[1,1,3]),([2,1,3],[1,1,3]),0,true⟩,
    ⟨([2,1,2,1,3],[1,1,3]),([2,1,2,1,3],[1,1,3]),0,false⟩,
    ⟨([2,3],[1,2,1,3]),([2,3],[1,2,1,3]),0,false⟩,
    ⟨([2,3],[1,2,1,3]),([2,1,2,1,3],[1,1,3]),0,true⟩,
    ⟨([1,1,3],[3]),([1,1,3],[3]),0,false⟩,
    ⟨([1,2,1,3],[1,2,1,3]),([1,2,1,3],[1,2,1,3]),0,false⟩,
    ⟨([1,2,1,3],[1,2,1,3]),([1,1,3],[3]),0,true⟩]
  | .threeOdd => [
    ⟨([1,2,1,3],[1,2,1,3]),([1,2,1,3],[1,2,1,3]),1,false⟩,
    ⟨([1,1,3],[3]),([1,1,2,1,3],[3]),1,true⟩,
    ⟨([1,1,2,1,3],[3]),([1,2,1,3],[1,2,1,3]),1,true⟩,
    ⟨([2,3],[1,2,1,3]),([2,3],[1,2,1,3]),1,false⟩,
    ⟨([2,1,3],[1,1,3]),([2,1,2,1,3],[1,1,3]),1,true⟩,
    ⟨([2,1,2,1,3],[1,1,3]),([2,1,2,1,3],[1,1,3]),1,false⟩,
    ⟨([2,1,2,1,3],[1,1,3]),([2,3],[1,2,1,3]),1,true⟩,
    ⟨([3,3],[1,2,1,3]),([3,3],[1,2,1,3]),1,false⟩,
    ⟨([3,1,2,1,3],[1,1,3]),([3],[1,1,3]),1,true⟩,
    ⟨([3],[1,1,3]),([3,3],[1,2,1,3]),1,true⟩,
    ⟨([2,3],[2,2,1,3]),([2,3],[2,3]),1,true⟩,
    ⟨([2,3],[2,2,1,3]),([2,3],[2,2,1,3]),1,false⟩,
    ⟨([2,1,3],[2,1,3]),([2,1,3],[2,1,2,1,3]),1,true⟩,
    ⟨([2,1,3],[2,1,2,1,3]),([2,1,3],[2,1,2,1,3]),1,false⟩,
    ⟨([2,1,3],[2,1,2,1,3]),([2,3],[2,2,1,3]),1,true⟩,
    ⟨([2,3],[3,2,1,3]),([2,3],[3,3]),1,true⟩,
    ⟨([2,3],[3,2,1,3]),([2,3],[3,2,1,3]),1,false⟩,
    ⟨([2,1,3],[3,1,2,1,3]),([2,1,3],[3]),1,true⟩,
    ⟨([2,1,3],[3]),([2,3],[3,2,1,3]),1,true⟩,
    ⟨([3,2,1,3],[2,3]),([3,3],[2,3]),1,true⟩,
    ⟨([3,2,1,3],[2,3]),([3,2,1,3],[2,3]),1,false⟩,
    ⟨([3,1,2,1,3],[2,1,3]),([3,1,2,1,3],[2,1,3]),1,false⟩,
    ⟨([3,1,2,1,3],[2,1,3]),([3,2,1,3],[2,3]),1,true⟩]
  | .twoOdd => [
    ⟨([1,3],[1,2,1,3]),([1,3],[1,2,1,3]),1,false⟩,
    ⟨([1,1,3],[3]),([1,1,2,1,3],[3]),1,true⟩,
    ⟨([1,1,2,1,3],[3]),([1,3],[1,2,1,3]),1,true⟩,
    ⟨([2,3],[1,2,1,3]),([2,3],[1,2,1,3]),1,false⟩,
    ⟨([2,1,3],[1,1,3]),([2,1,2,1,3],[1,1,3]),1,true⟩,
    ⟨([2,1,2,1,3],[1,1,3]),([2,1,2,1,3],[1,1,3]),1,false⟩,
    ⟨([2,1,2,1,3],[1,1,3]),([2,3],[1,2,1,3]),1,true⟩,
    ⟨([3,3],[1,2,1,3]),([3,3],[1,2,1,3]),1,false⟩,
    ⟨([3,1,2,1,3],[1,1,3]),([3],[1,1,3]),1,true⟩,
    ⟨([3],[1,1,3]),([3,3],[1,2,1,3]),1,true⟩,
    ⟨([2,3],[2,2,1,3]),([2,3],[2,3]),1,true⟩,
    ⟨([2,3],[2,2,1,3]),([2,3],[2,2,1,3]),1,false⟩,
    ⟨([2,1,3],[2,1,3]),([2,1,3],[2,1,2,1,3]),1,true⟩,
    ⟨([2,1,3],[2,1,2,1,3]),([2,1,3],[2,1,2,1,3]),1,false⟩,
    ⟨([2,1,3],[2,1,2,1,3]),([2,3],[2,2,1,3]),1,true⟩,
    ⟨([2,3],[3,2,1,3]),([2,3],[3,3]),1,true⟩,
    ⟨([2,3],[3,2,1,3]),([2,3],[3,2,1,3]),1,false⟩,
    ⟨([2,1,3],[3,1,2,1,3]),([2,1,3],[3]),1,true⟩,
    ⟨([2,1,3],[3]),([2,3],[3,2,1,3]),1,true⟩,
    ⟨([3,2,1,3],[2,3]),([3,3],[2,3]),1,true⟩,
    ⟨([3,2,1,3],[2,3]),([3,2,1,3],[2,3]),1,false⟩,
    ⟨([3,1,2,1,3],[2,1,3]),([3,1,2,1,3],[2,1,3]),1,false⟩,
    ⟨([3,1,2,1,3],[2,1,3]),([3,2,1,3],[2,3]),1,true⟩]

def lowerEntryContactRows : LowerEntryClass → List LowerEntryRow
  | .threeEven => [
    ⟨([3,2,1,3],[2,3]),([2,1,3],[3]),0,true⟩,
    ⟨([2,3],[3,2,1,3]),([2,1,3],[2,1,2,1,3]),0,true⟩,
    ⟨([2,3],[2,2,1,3]),([3],[1,1,3]),0,true⟩,
    ⟨([3,3],[1,2,1,3]),([2,1,2,1,3],[1,1,3]),0,true⟩,
    ⟨([2,3],[1,2,1,3]),([1,1,3],[3]),0,true⟩]
  | .threeOdd => [
    ⟨([1,1,2,1,3],[3]),([2,3],[1,2,1,3]),1,true⟩,
    ⟨([2,1,2,1,3],[1,1,3]),([3,3],[1,2,1,3]),1,true⟩,
    ⟨([3],[1,1,3]),([2,3],[2,2,1,3]),1,true⟩,
    ⟨([2,1,3],[2,1,2,1,3]),([2,3],[3,2,1,3]),1,true⟩,
    ⟨([2,1,3],[3]),([3,2,1,3],[2,3]),1,true⟩]
  | .twoOdd => [
    ⟨([1,1,2,1,3],[3]),([2,3],[1,2,1,3]),1,true⟩,
    ⟨([2,1,2,1,3],[1,1,3]),([3,3],[1,2,1,3]),1,true⟩,
    ⟨([3],[1,1,3]),([2,3],[2,2,1,3]),1,true⟩,
    ⟨([2,1,3],[2,1,2,1,3]),([2,3],[3,2,1,3]),1,true⟩,
    ⟨([2,1,3],[3]),([3,2,1,3],[2,3]),1,true⟩]

def lowerEntryCoreWords (c : LowerEntryClass) (l : LowerLabel) : LowerPair × LowerPair :=
  let e : LowerPair × LowerPair :=
    if l = ([3],[2]) then (([3,1,2,1,3],[2,1,3]),([3,2,1,3],[2,3]))
    else if l = ([2],[3]) then (([2,1,3],[3]),([2,3],[3,2,1,3]))
    else if l = ([2],[2]) then (([2,1,3],[2,1,2,1,3]),([2,3],[2,2,1,3]))
    else if l = ([3],[1]) then (([3],[1,1,3]),([3,3],[1,2,1,3]))
    else if l = ([2],[1]) then (([2,1,2,1,3],[1,1,3]),([2,3],[1,2,1,3]))
    else if l = ([1],[]) then (([1,1,3],[3]),([1,2,1,3],[1,2,1,3]))
    else (([],[]),([],[]))
  if c=.threeEven then e else
    if l=([1],[]) then
      (if c=.twoOdd then (([1,3],[1,2,1,3]),([1,1,2,1,3],[3]))
       else (([1,2,1,3],[1,2,1,3]),([1,1,2,1,3],[3])))
    else (e.2,e.1)
noncomputable def lowerEntryCore (c : LowerEntryClass) (p : LowerPair) (l : LowerLabel) : Set ℝ :=
  let e := lowerEntryCoreWords c l
  let a := 4+prefixEval (p.1++e.1.1) lowerTau+prefixEval (p.2++e.1.2) lowerTau
  let b := 4+prefixEval (p.1++e.2.1) lowerTau+prefixEval (p.2++e.2.2) lowerTau
  Set.Icc (min a b) (max a b)
noncomputable def lowerEntryActualDifference (p : LowerPair) (e : LowerEntryRow) : ℝ :=
  prefixEval (p.1++e.upperWords.1) lowerTau + prefixEval (p.2++e.upperWords.2) lowerTau -
  prefixEval (p.1++e.lowerWords.1) lowerTau - prefixEval (p.2++e.lowerWords.2) lowerTau
noncomputable def lowerEntryRowsHold (p : LowerPair) (es : List LowerEntryRow) : Prop :=
  ∀ e ∈ es, if e.strict then 0 < lowerEntryActualDifference p e else lowerEntryActualDifference p e = 0
noncomputable def lowerEntryChildOrientation (p : LowerPair) : Prop :=
  ∀ l ∈ lowerEntryLabels,
    if l=([2],[2]) ∨ l=([2],[3]) then
      lowerWidth (lowerChild p l).2 < lowerWidth (lowerChild p l).1
    else lowerWidth (lowerChild p l).1 < lowerWidth (lowerChild p l).2
noncomputable def lowerEntryVirtualNN (p : LowerPair) : Prop :=
  (2998375/1672704:ℝ)*lowerWidth (p.2++[1,1,1]) < lowerWidth (p.1++[3]) ∧
  (4036065625/2475596544:ℝ)*lowerWidth (p.2++[1,1,1,3]) < lowerWidth (p.1++[3,3])
end Freiman


