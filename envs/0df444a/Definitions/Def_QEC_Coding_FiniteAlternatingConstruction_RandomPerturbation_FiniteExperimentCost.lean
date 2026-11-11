-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T02:18:57.875592+00:00
-- url     : https://prove2.me/theorems/1aa3566a-12ee-40cb-b6fc-016b86b1c2c7
-- title:
--   Finite Experiment Cost
-- statement:
--   Definitions and structural lemmas for Finite Experiment Cost, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26QuantitativeBounds
open BDL26RandomPerturbation BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
def jointStageCost {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (w : StageMaps p n × StageTables p n) : ℝ≥0∞ :=
  actualExecutionCost (StagePresentation p n) w.1
    (by positivity : (0 : ℝ) ≤ anchorRadius p.m)
    p.lambda ((6*p.m+2)*p.lambda) w.2
def stageCost {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (z : Experiment p n) : ℝ≥0∞ :=
  jointStageCost p i.val (stagePair p n i z)
def totalStageCost {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (z : Experiment p n) : ℝ≥0∞ := ∑ i : Fin n, stageCost p n i z
def stageQubits {L : ℝ} (p : GeometricParameters L) (n : ℕ) : ℕ :=
  Fintype.card (StagePresentation p n).Q
end QEC.Coding.BDL26FiniteEmbeddingExperiment


