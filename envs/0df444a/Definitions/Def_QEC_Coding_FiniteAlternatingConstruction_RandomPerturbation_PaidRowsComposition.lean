-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T03:18:28.080477+00:00
-- url     : https://prove2.me/theorems/37eb2815-c7ff-47d8-a64f-a9350f1f842d
-- title:
--   Paid Rows Composition
-- statement:
--   Definitions and structural lemmas for Paid Rows Composition, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26PaidRowsComposition
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26ReplacementMaterialization BDL26IncomingRowsExecution
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
def stampRowsQuery {A : Type*} (R : List (A × Space)) : List (A × ℕ × Space) × ℕ :=
  mapQuery (fun row => ((row.1,0,row.2),2)) R
def composedStageQuery {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (I : StateRows (StagePresentation p n)) (T : StageTables p n) :
    StateRows (StagePresentation p (n+1)) × ℝ≥0∞ :=
  let perturbation := rowExecutionQuery (StagePresentation p n) I
    (by positivity : (0 : ℝ) ≤ anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda) T
  let replacement := materializeRows p n perturbation.1
  let wrapped := stampRowsQuery replacement.1
  (wrapped.1,perturbation.2+((replacement.2+wrapped.2 : ℕ) : ℝ≥0∞))
def run {L : ℝ} (p : GeometricParameters L) :
    (N : ℕ) → Experiment p N → StateRows (StagePresentation p N) × ℝ≥0∞
  | 0, _ => (incomingRows _ (BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p)),0)
  | N+1, z => let prior := run p N z.1
              let next := composedStageQuery p N prior.1 z.2
              (next.1,prior.2+next.2)
def transferTotal {L : ℝ} (p : GeometricParameters L) (N : ℕ) : ℕ :=
  ∑ i : Fin N, 3*Fintype.card (Vertex (StagePresentation p (i.val+1)))
def totalCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) : ℝ≥0∞ :=
  (run p N z).2
def inputRows {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N) (z : Experiment p N) :
    StateRows (StagePresentation p i.val) :=
  (run p i.val (experimentPrefix p i.val N (by omega) z)).1
def stageCost {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N) (z : Experiment p N) : ℝ≥0∞ :=
  (composedStageQuery p i.val (inputRows p N i z) (tableAt p N i z)).2
def stagePrefixRows {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (time : ℕ) (z : Experiment p N) : StateRows (StagePresentation p i.val) :=
  (rowPrefixQuery (StagePresentation p i.val) (inputRows p N i z) (anchorRadius p.m)
    p.lambda ((6*p.m+2)*p.lambda)
    (rowUniverseQuery (StagePresentation p i.val) (inputRows p N i z) (by positivity)).1
    (tableAt p N i z) time).1
def actualStageCounters {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (time : ℕ) (z : Experiment p N) : Counters (Vertex (StagePresentation p i.val)) :=
  fun v => (stateRowQuery v (stagePrefixRows p N i time z)).1.1
def actualStageSamples {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (time : ℕ) (z : Experiment p N) : StageMaps p i.val :=
  statePoints (stagePrefixRows p N i time z)
def actualStageSelected {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (time : ℕ) (z : Experiment p N) : Option (MasterEvent (StagePresentation p i.val)) :=
  ((rowScanQuery (StagePresentation p i.val) (inputRows p N i z) (anchorRadius p.m)
    p.lambda ((6*p.m+2)*p.lambda)
    (rowUniverseQuery (StagePresentation p i.val) (inputRows p N i z) (by positivity)).1
    (stagePrefixRows p N i time z)).1).map
      (eventToMaster (StagePresentation p i.val) (statePoints (inputRows p N i z)) (anchorRadius p.m))
def actualStageHalts {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : Prop :=
  Halts (eventSupport (StagePresentation p i.val) (statePoints (inputRows p N i z)) (anchorRadius p.m))
    (eventBad (StagePresentation p i.val) (statePoints (inputRows p N i z))
      (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) (tableAt p N i z)
def actualStageHaltTime {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : ℕ :=
  haltTime (eventSupport (StagePresentation p i.val) (statePoints (inputRows p N i z)) (anchorRadius p.m))
    (eventBad (StagePresentation p i.val) (statePoints (inputRows p N i z))
      (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) (tableAt p N i z)
def actualStageGeometric {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : StageMaps p i.val :=
  statePoints (stagePrefixRows p N i (actualStageHaltTime p N i z) z)
def actualStagePerturbed {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : StageMaps p i.val :=
  statePoints (stampRowsQuery
    (rowExecutionQuery (StagePresentation p i.val) (inputRows p N i z)
      (by positivity : (0 : ℝ) ≤ anchorRadius p.m)
      p.lambda ((6*p.m+2)*p.lambda) (tableAt p N i z)).1).1
def actualStagePhysical {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : StageMaps p (i.val+1) :=
  statePoints (composedStageQuery p i.val (inputRows p N i z) (tableAt p N i z)).1
abbrev StageTrace {L : ℝ} (p : GeometricParameters L) (n : ℕ) :=
  (ℕ → Counters (Vertex (StagePresentation p n))) ×
  (ℕ → Option (MasterEvent (StagePresentation p n))) ×
  (ℕ → StageMaps p n) × Bool × ℕ × StageMaps p n × StageMaps p n × StageMaps p (n+1)
def stageTrace {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : StageTrace p i.val :=
  (fun time => actualStageCounters p N i time z,
   fun time => actualStageSelected p N i time z,
   fun time => actualStageSamples p N i time z,
   if actualStageHalts p N i z then true else false,
   actualStageHaltTime p N i z,actualStageGeometric p N i z,
   actualStagePerturbed p N i z,actualStagePhysical p N i z)
def originalStageTrace {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) : StageTrace p i.val :=
  (fun time => stageCounters p N i time z,
   fun time => stageSelected p N i time z,
   fun time v => (tableAt p N i z) (v,stageCounters p N i time z v),
   if stageHalts p N i z then true else false,
   stageHaltTime p N i z,stageGeometricOutput p N i z,
   stagePerturbedOutput p N i z,stagePhysicalOutput p N i z)
abbrev Observation {L : ℝ} (p : GeometricParameters L) (N : ℕ) :=
  ((i : Fin (N+1)) → StageMaps p i.val) ×
  ((i : Fin N) → StageTrace p i.val) × (Fin N → ℝ≥0∞) × ℝ≥0∞
def paidHistory {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N)
    (i : Fin (N+1)) : StageMaps p i.val :=
  statePoints (run p i.val (experimentPrefix p i.val N (by omega) z)).1
def finiteObservation {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) : Observation p N :=
  (paidHistory p N z,fun i => stageTrace p N i z,fun i => stageCost p N i z,totalCost p N z)
def originalObservation {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) : Observation p N :=
  (history p N z,fun i => originalStageTrace p N i z,fun i => stageCost p N i z,totalCost p N z)
def streamRun {L : ℝ} (p : GeometricParameters L) (omega : BDL26CountableEmbeddingExperiment.Omega p) :
    (N : ℕ) → StateRows (StagePresentation p N) × ℝ≥0∞
  | 0 => (incomingRows _ (BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p)),0)
  | N+1 => let prior := streamRun p omega N
           let next := composedStageQuery p N prior.1 (omega N)
           (next.1,prior.2+next.2)
def streamStageCost {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) : ℝ≥0∞ :=
  (composedStageQuery p n (streamRun p omega n).1 (omega n)).2
def streamTotalCost {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) : ℝ≥0∞ := (streamRun p omega N).2
def streamStageTrace {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) : StageTrace p n :=
  let I := (streamRun p omega n).1
  let T := omega n
  let events := (rowUniverseQuery (StagePresentation p n) I (by positivity : (0 : ℝ) ≤ anchorRadius p.m)).1
  let rows := fun time => (rowPrefixQuery (StagePresentation p n) I (anchorRadius p.m)
    p.lambda ((6*p.m+2)*p.lambda) events T time).1
  let halt := haltTime (eventSupport (StagePresentation p n) (statePoints I) (anchorRadius p.m))
    (eventBad (StagePresentation p n) (statePoints I) (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T
  (fun time v => (stateRowQuery v (rows time)).1.1,
   fun time => ((rowScanQuery (StagePresentation p n) I (anchorRadius p.m) p.lambda
      ((6*p.m+2)*p.lambda) events (rows time)).1).map
        (eventToMaster (StagePresentation p n) (statePoints I) (anchorRadius p.m)),
   fun time => statePoints (rows time),
   if Halts (eventSupport (StagePresentation p n) (statePoints I) (anchorRadius p.m))
       (eventBad (StagePresentation p n) (statePoints I) (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T
     then true else false,
   halt,statePoints (rows halt),
   statePoints (stampRowsQuery (rowExecutionQuery (StagePresentation p n) I
      (by positivity : (0 : ℝ) ≤ anchorRadius p.m)
      p.lambda ((6*p.m+2)*p.lambda) T).1).1,
   statePoints (composedStageQuery p n I T).1)
def streamObservation {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) : Observation p N :=
  (fun i => statePoints (streamRun p omega i.val).1,
   fun i => streamStageTrace p i.val omega,fun i => streamStageCost p i.val omega,streamTotalCost p N omega)
end QEC.Coding.BDL26PaidRowsComposition


