-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T02:09:00.664175+00:00
-- url     : https://prove2.me/theorems/0e89a46b-10c6-4d8a-a32a-42ae0dab7a52
-- title:
--   Laws
-- statement:
--   Definitions and structural lemmas for Laws, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Laws.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Core
import Mathlib.Probability.Independence.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_evaluate

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped ENNReal ProbabilityTheory
def experimentLaw {L : ℝ} (p : GeometricParameters L) :
    (n : ℕ) → Measure (Experiment p n)
  | 0 => Measure.dirac ()
  | n+1 => (experimentLaw p n).prod (physicalTableLaw p n)
instance experimentLaw_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    IsProbabilityMeasure (experimentLaw p n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | succ n ih =>
      letI := ih
      change IsProbabilityMeasure ((experimentLaw p n).prod (physicalTableLaw p n))
      infer_instance
def outputLaw {L : ℝ} (p : GeometricParameters L) (n : ℕ) : Measure (StageMaps p n) :=
  (experimentLaw p n).map (evaluate p n)
instance outputLaw_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    IsProbabilityMeasure (outputLaw p n) :=
  Measure.isProbabilityMeasure_map (measurable_evaluate p n).aemeasurable
def freshPair {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Experiment p (n+1) → StageMaps p n × StageTables p n :=
  fun z => (evaluate p n z.1, z.2)
end QEC.Coding.BDL26FiniteEmbeddingExperiment


