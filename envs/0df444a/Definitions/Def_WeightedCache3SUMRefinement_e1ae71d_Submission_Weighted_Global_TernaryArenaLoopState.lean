-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLoopState
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLoopState
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T20:37:39.624779+00:00
-- url     : https://prove2.me/theorems/4fc589f3-5c57-4476-95b3-a3b37f11e6fe
-- title:
--   TernaryArenaLoopState
-- statement:
--   Definitions and structural lemmas for TernaryArenaLoopState, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaLoopState.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPhaseBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPhaseFrames
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixInit
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_prepared
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedCountFrontend_prepared
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalControllerFactory_Candidate_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalControllerFactory_SpanGuard_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalControllerFactory_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixPhases_LoopPlan_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixPhases_Phase_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixStep_PrepareReady_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalSeedScoreFactory_Ready_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalTensorFactory_Ready_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedCountExecutionFactory_Ready_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaFrontBounds_capacity
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaLayout_before
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPrefixState_prepared
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPreparedMemory_prepared
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_initial
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run
attribute [local simp] ThreeSum.LightTernaryCountFrontend.prepared
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCountFrontend.prepared


set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalArenaLoop
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaLayout
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaSeedData
open WeightedGlobalArenaSelectedBudgets WeightedGlobalArenaAllocation WeightedGlobalArenaPrefixInputs
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
structure Setup (p m F K N : ℕ) [Fact p.Prime]
    (E : Type*) [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E] where
  maps : Fin F→Weight m p
  threshold : ℕ
  cap : ℕ
  Q : WeightedGlobalGoodOutputCatalog.Output m
  M : ℕ
  radix : ℕ
  H : ℕ
  drift : ℕ
  scale : ℕ
  allocation : Allocation maps threshold cap M radix K H drift scale
  input : Input
  arrays : Inputs
  n : ℕ
  U : ℕ
  rounds : ℕ
  U0 : ℕ
  featureBound : ℕ
  tagBound : ℕ
  positionCap : ℕ
  valueTag : ℕ
  V : ℕ
  scoreBound : ℕ
  enumeration : (E×E)≃Fin N
  ell : E→ₗ[ZMod p] ZMod p
  L : ℕ→ℕ→ℤ
  R : ℕ→ℕ→ℤ
  O : ℕ→ℕ→ℤ
  catalogs : ℕ→ℕ→ℕ→ℕ
  initial : ℕ→ℤ
variable {p m F K N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
abbrev Setup.alpha (_S : Setup p m F K N E) : ℕ :=p^(2*K)
abbrev Setup.beta (_S : Setup p m F K N E) : ℕ :=9*WeightedGlobalArenaBudgetExistence.pairFactor m F K
abbrev Setup.budgetScale (_S : Setup p m F K N E) : ℕ :=2^(fixedPi m 2*K)
abbrev Setup.wordRadix (_S : Setup p m F K N E) : ℕ :=4^fixedLength m
abbrev Setup.raws (S : Setup p m F K N E) :=WeightedGlobalGoodOutputCatalog.raws S.maps S.threshold
abbrev Setup.words (S : Setup p m F K N E) :=WeightedGlobalGoodOutputCatalog.wordCodes S.maps S.threshold
abbrev Setup.mapCodes (S : Setup p m F K N E) :=WeightedGlobalGoodOutputCatalog.mapCodes S.maps S.threshold
abbrev Setup.newSpan (S : Setup p m F K N E) :=addr S.input.free S.input.capacity 8
def Setup.state (S : Setup p m F K N E) (j : ℕ) : State (p:=p) S.arrays :=
  run S.maps S.threshold S.cap S.valueTag S.V S.scoreBound S.Q S.input S.arrays S.featureBound K S.n S.U0
    S.enumeration S.ell S.L S.R S.O S.catalogs j
def Setup.family (S : Setup p m F K N E) (j : ℕ) (catalog : ℕ→ℕ→ℕ) :=
  WeightedGlobalArenaPhase.family S.maps S.threshold S.cap S.tagBound S.Q S.input S.arrays j S.featureBound
    S.ell (WeightedGlobalArenaFamilyBudget.seedAt S.enumeration) S.L S.R S.O (S.state j) catalog
def Setup.prefixInput (S : Setup p m F K N E) (j : ℕ) :=
  WeightedGlobalArenaPrefixPrepare.inputs p m F j S.arrays.J S.n S.U0 S.alpha S.beta S.budgetScale S.input S.Q
def Setup.seedHeader (S : Setup p m F K N E) (j : ℕ) :=
  LightWeightedGlobalPrefixFinish.header (config p j S.input S.arrays 0) N (p^j) (p^j) (S.alpha^j)
    (9^j*S.n^2) (9^j*S.n^2) (S.U0*(S.beta*S.budgetScale)^j) S.newSpan
def Setup.chosen (S : Setup p m F K N E) (j : ℕ) (catalog : ℕ→ℕ→ℕ) :=
  (S.family j catalog).pick K N (p^(j+1)) (p^(j+1)) (S.alpha^(j+1))
    (9^(j+1)*S.n^2) (9^(j+1)*S.n^2) (S.U0*(S.beta*S.budgetScale)^(j+1))-1
structure LastRecord (S : Setup p m F K N E) (j : ℕ) (ω : ℕ→ℤ) where
  before : ℕ→ℤ
  catalog : ℕ→ℕ→ℕ
  oldMemory : WeightedGlobalArenaPrefixState.Memory S.input S.arrays (fun i t=>S.L i t.val)
    (fun i t=>S.R i t.val) (fun i t=>S.O i t.val) j (S.state j) catalog S.initial before
  oldTemplate : Seg before (addr S.input.free S.input.capacity 0)
    (WeightedGlobalArenaHeaderAgreement.templateValues S.input p m F)
  preparedMemory : ℕ→ℤ
  prepared : LightWeightedGlobalPrefixStep.Prepared (S.prefixInput j) before preparedMemory
  finalMemory : ℕ→ℤ
  final : WeightedGlobalArenaControllerPlan.Final S.input (S.family j catalog) K S.wordRadix F
    (S.chosen j catalog) S.newSpan S.raws S.words S.mapCodes preparedMemory finalMemory
  committed : LightWeightedGlobalPrefixFinish.Committed (config p (j+1) S.input S.arrays 0)
    (p^(j+1)) S.newSpan finalMemory ω
def Invariant (S : Setup p m F K N E) (j : ℕ) (μ : ℕ→ℤ) : Prop :=
  ∃catalog,
    WeightedGlobalArenaPrefixState.Memory S.input S.arrays (fun i t=>S.L i t.val)
      (fun i t=>S.R i t.val) (fun i t=>S.O i t.val) j (S.state j) catalog S.initial μ ∧
    Seg μ (addr S.input.free S.input.capacity 3) (S.seedHeader j) ∧
    Seg μ (addr S.input.free S.input.capacity 0) (WeightedGlobalArenaHeaderAgreement.templateValues S.input p m F) ∧
    match j with
    | 0=>True
    | j+1=>Nonempty (LastRecord S j μ)
def Setup.timeAt (S : Setup p m F K N E) (j : ℕ) : ℕ :=
  LightWeightedGlobalPrefixStep.time (S.prefixInput j) (config p (j+1) S.input S.arrays 0) N
    (WeightedGlobalArenaControllerCore.seedTime (S.family j (fun _ _=>0)) K S.wordRadix F N S.raws S.words S.mapCodes)
def Setup.stepTime (S : Setup p m F K N E) : ℕ :=(Finset.range S.rounds).sup S.timeAt
def Setup.time (S : Setup p m F K N E) : ℕ :=LightWeightedGlobalPrefixLoop.time S.rounds S.stepTime
def Setup.program (S : Setup p m F K N E) : Program :=
  LightWeightedGlobalPrefixLoop.program p S.wordRadix F K S.raws S.words S.mapCodes
    ((WeightedGlobalNativeCompleteFrontend.localRecords S.maps S.cap false).map (TernaryCanonicalDictionaries.native false S.maps))
    ((WeightedGlobalNativeCompleteFrontend.localRecords S.maps S.cap false).map TernaryCanonicalDictionaries.wordCode)
    ((WeightedGlobalNativeCompleteFrontend.localRecords S.maps S.cap false).map TernaryCanonicalDictionaries.mapCode)
    ((WeightedGlobalNativeCompleteFrontend.localRecords S.maps S.cap true).map (TernaryCanonicalDictionaries.native true S.maps))
    ((WeightedGlobalNativeCompleteFrontend.localRecords S.maps S.cap true).map TernaryCanonicalDictionaries.wordCode)
    ((WeightedGlobalNativeCompleteFrontend.localRecords S.maps S.cap true).map TernaryCanonicalDictionaries.mapCode)
def Setup.argv (S : Setup p m F K N E) : List ℤ :=
  LightWeightedGlobalPrefixLoop.args S.rounds m F p (addr S.input.free S.input.capacity 3)
    (addr S.input.free S.input.capacity 0) (addr S.input.free S.input.capacity 1)
    (addr S.input.free S.input.capacity 13) (fixedAlpha m 2) (alphaRank m)
    (TernaryCodeSemantics.address S.Q.val) S.wordRadix S.arrays.J S.alpha S.beta S.budgetScale
def Setup.initArgs (S : Setup p m F K N E) : List ℤ:=S.argv++[(addr S.input.free S.input.capacity 2:ℤ)]
def Setup.initTime (S : Setup p m F K N E) : ℕ:=
  LightWeightedGlobalPrefixInit.time (config p 0 S.input S.arrays 0) S.rounds S.stepTime
end ThreeSum.WeightedGlobalArenaLoop
end
end WeightedCache3SUMRefinement_e1ae71d


