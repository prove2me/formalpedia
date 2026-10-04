-- Prove2me | Definitions.Def_Yukon_f3d7314030f7069e4d8b829c
-- name    : Yukon_f3d7314030f7069e4d8b829c
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T19:38:58.683379+00:00
-- url     : https://prove2.me/theorems/efa77cfe-1df0-438e-973e-d360cb1f3ca0
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberProfile6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberProfile6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberProfile6814.lean
--
--   yukon-proof-operation:certificate-split-793cc935ebef314f1e01079f5aee5c3238245bde6ca19de66e56f73a0fc464e1
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNGRkY2M0M2UxOTM0MzU0MDg1NzcyZmQ4Yjk5Y2M2ZDE2MmM2MmI1YzA1NGMyZjBhMzRjMWMyNWJjZjA5ZDkzMyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LTc5M2NjOTM1ZWJlZjMxNGYxZTAxMDc5ZjVhZWU1YzMyMzgyNDViZGU2Y2ExOWRlNjZlNTZmNzNhMGZjNDY0ZTEiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9mM2Q3MzE0MDMwZjcwNjllNGQ4YjgyOWMiLCJ2IjoyfQ]

import Definitions.Def_Yukon_e1a1d0c7582a0e3bb14b33e7

import Definitions.Def_Yukon_0c908ad128e35e387549499c

import Definitions.Def_Yukon_eed5b48fe35aa7de80eb9c3e

















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.MovingFiberProfile6814
open scoped Classical BigOperators
open MvPolynomial RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN174 RCN222 RCN234 RCN238 RCN243 RCN260 RCN319 RCN327
open LocatorHybridCells LocatorHybridCellsC1 BoundaryTailProvider
open MovingFiberRegularData6814 MovingFiberThreeSources6811 MovingFiberInterpolation6814 MovingFiberTotalAvoidance6814
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

structure Params where
  m : ℕ
  B : ℕ
  s : ℕ
  U : ℕ
  L : ℕ
  k : ℕ
  n0 : ℕ
  deriving DecidableEq, Repr

def Params.d (P : Params) : ℕ := P.k+1
def Params.flag (P : Params) : FlagDegree := SecondJetRelaxedFlag.budgetFlag P.B P.U P.L P.d P.n0
def Params.WellFormed (P : Params) : Prop :=
  2*P.s ≤ P.B ∧ P.B ≤ P.U ∧ P.U ≤ P.L ∧ P.k ≤ P.s ∧ P.s < P.m ∧
    P.k+1 ≤ P.n0 ∧ 2*(P.n0-(P.k+1)) ≤ P.B ∧ P.s < 2130706433
def number (cfg : Fin 3 → Params) (scale t y r : ℕ) (f : FlagDegree) : ℕ :=
  scale/3*flagMixed f (MovingFiberRetainedStage6811.hfreeFirst t y r) (cellNormal t y r) +
    ∑ j : Fin 3, (4*(w+1)*weight (cellNormal t y r) j*(scale/(3*(cfg j).d))+
      65539*weight (MovingFiberRetainedStage6811.rawFirstFlag t y r) j*(scale/(cfg j).d))*
      flagMixed f (MovingFiberThreeSources6811.direction j) (cfg j).flag

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance  _root_.ProximityPrize.SubmissionLower.MovingFiberProfile6814.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.MovingFiberProfile6814.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I
local instance  _root_.ProximityPrize.SubmissionLower.MovingFiberProfile6814.instCharPGenericFieldOfNatNat : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
variable {nodes : I ↪ K} {u0 u1 : I → K}

def helperCap (S : Data nodes u0 u1) (P : Params) : ℕ :=
  AsymmetricHelper.leftRegularCountCap (S.pair (P.B+P.s*(S.r-1)) (P.U+P.s*(S.y-1)) (P.L+P.s*(S.t-1)))
def coefficientCap (S : Data nodes u0 u1) (P : Params) : ℕ :=
  AsymmetricHelper.leftRegularCountCap (S.pair P.B P.U P.L)
def bound (S : Data nodes u0 u1) (cfg : Fin 3 → Params) (scale : ℕ) : ℕ :=
  max (Finset.univ.sup (fun j : Fin 3 => helperCap S (cfg j)))
    (number cfg scale S.t S.y S.r (originalCumulativeFlag S.F)/scale +
      ∑ j : Fin 3, coefficientCap S (cfg j))






end
end ProximityPrize.SubmissionLower.MovingFiberProfile6814


