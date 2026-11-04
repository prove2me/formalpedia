-- Prove2me | Definitions.Def_Submission_Weighted_FrontendResources
-- name    : Submission_Weighted_FrontendResources
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:13:34.411206+00:00
-- url     : https://prove2.me/theorems/af3371d9-06c0-4e6e-929a-4129b31c5879
-- title:
--   Frontend Resources
-- statement:
--   Definitions and structural lemmas for Frontend Resources, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrontendResources.lean

import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_TernaryRadixOverhead
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedFrontendResources
open Light ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedPreparedWanted
open Filter StageBounds ThreeSum.TernaryCodeSemantics
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
def sourceZeta (N A : ℕ) : ℕ := 4^N*A
def eulerBound (N A : ℕ) : ℕ := 2*(N+1)*sourceZeta N A
def caps (a R : ℕ) : ℕ := a+R
def active (a N R : ℕ) : ℕ := caps a R+N
def powers (a N R : ℕ) : ℕ := active a N R+N
def fws (a N R : ℕ) : ℕ := powers a N R+(2*N+1)
def ranks (ws N R : ℕ) : ℕ := ws+2*N*R+N
def vals (ws N R : ℕ) : ℕ := ranks ws N R+R
def division (ws N R : ℕ) : ℕ := vals ws N R+R
def gws (a N R A : ℕ) : ℕ := division (fws a N R) N R+eulerBound N A+3
def out (a N R A : ℕ) : ℕ := division (gws a N R A) N R+eulerBound N A+3
def heapEnd (a N R A : ℕ) : ℕ := out a N R A+R
def config (a N R A bank nb bv T h ws : ℕ) : Config where
  a:= a; powers:= powers a N R; bank:= bank; nb:= nb; bv:= bv; L:= 2*N; T:= T
  activeBase:= active a N R; ws:= ws; rankBase:= ranks ws N R; vals:= vals ws N R
  h:= h; pcount:= division ws N R; fr:= division ws N R
  U:= sourceZeta N A; V:= eulerBound N A
def word (N nb groups count R A : ℕ) : ℕ :=
  10000*(N+nb+groups+count+R+(N+1)*nb+2^(2*N+1)+4^(N+1)+sourceZeta N A+
    eulerBound N A+(sourceZeta N A)^2+4^N*(sourceZeta N A)^2+100)
def need (N nb groups count R A priorCells hostWord : ℕ) : Light.Need :=
  ⟨hostWord+word N nb groups count R A, heapEnd priorCells N R A,5*N+16⟩
def envelope (B : ℕ) : ℕ := 2000000*(B+1)^6
open ThreeSum.TernaryCoverScale ThreeSum.TernaryPrincipalDimensions
end ThreeSum.WeightedFrontendResources


