-- Prove2me | Definitions.Def_Yukon_fdec088c29e5451064f27f59
-- name    : Yukon_fdec088c29e5451064f27f59
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T17:18:54.975104+00:00
-- url     : https://prove2.me/theorems/a7212248-a06f-4e81-ab3d-c70c801f43f1
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberProfile6811.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberProfile6811.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberProfile6811.lean
--
--   yukon-proof-operation:certificate-split-3761f9cb2e0244d7010acea57489a9275c46105c9e27440f7b36a36ce9d0e5a9
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZGE3YTc2N2QyNjJhM2U3NWIxMWM2NGI1NmUzZmQ5ZWJmN2E3ZGRkZGZiMWNiNTVkMGE2YTg0Nzc4YjY5NThlOSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LTM3NjFmOWNiMmUwMjQ0ZDcwMTBhY2VhNTc0ODlhOTI3NWM0NjEwNWM5ZTI3NDQwZjdiMzZhMzZjZTlkMGU1YTkiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9mZGVjMDg4YzI5ZTU0NTEwNjRmMjdmNTkiLCJ2IjoyfQ]

import Definitions.Def_Yukon_563b4d7a022320de51406d74

import Definitions.Def_Yukon_b18ab9084e250f4b6a2f2e45

import Definitions.Def_Yukon_c15a74a0e1b49af1a1be45f3

















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.MovingFiberProfile6811
open scoped Classical BigOperators
open MvPolynomial RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN174 RCN222 RCN234 RCN238 RCN243 RCN260 RCN319 RCN327
open LocatorHybridCells LocatorHybridCellsC1 BoundaryTailProvider
open MovingFiberRegularData6811 MovingFiberThreeSources6811 MovingFiberInterpolation6811 MovingFiberTotalAvoidance6811
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
local instance  _root_.ProximityPrize.SubmissionLower.MovingFiberProfile6811.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.MovingFiberProfile6811.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I
local instance  _root_.ProximityPrize.SubmissionLower.MovingFiberProfile6811.instCharPGenericFieldOfNatNat : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
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
end ProximityPrize.SubmissionLower.MovingFiberProfile6811


