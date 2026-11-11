-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T03:02:41.030772+00:00
-- url     : https://prove2.me/theorems/785fe657-620e-4e19-8d2a-3061e94823c8
-- title:
--   Countable Experiment Cost
-- statement:
--   Definitions and structural lemmas for Countable Experiment Cost, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory
open BDL26FiniteEmbeddingExperiment BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation BDL26ReplacementEmbedding
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
def streamStageCost {L : ℝ} (p : GeometricParameters L) (i : ℕ)
    (omega : Omega p) : ℝ≥0∞ := jointStageCost p i (levelMap p omega i, omega i)
def prefixStageCost {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (omega : Omega p) : ℝ≥0∞ := ∑ i : Fin N, streamStageCost p i.val omega
abbrev PaidObservation {L : ℝ} (p : GeometricParameters L) (N : ℕ) :=
  ((i : Fin (N+1)) → StageMaps p i.val) × (Fin N → ℝ≥0∞) × ℝ≥0∞
def finitePaidObservation {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) : PaidObservation p N :=
  (history p N z, (fun i => stageCost p N i z), totalStageCost p N z)
def streamPaidObservation {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (omega : Omega p) : PaidObservation p N :=
  ((fun i => levelMap p omega i.val), (fun i => streamStageCost p i.val omega),
    prefixStageCost p N omega)
end QEC.Coding.BDL26CountableEmbeddingExperiment


