-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T02:53:28.244547+00:00
-- url     : https://prove2.me/theorems/77ace088-c4de-48b3-ae54-7755a80abcc6
-- title:
--   Countable Experiment
-- statement:
--   Definitions and structural lemmas for Countable Experiment, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperiment.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
import Mathlib.Probability.Independence.InfinitePi
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal ProbabilityTheory BigOperators
def streamLaw {L : ℝ} (p : GeometricParameters L) : Measure (Omega p) :=
  Measure.infinitePi (fun n => physicalTableLaw p n)
instance streamLaw_probability {L : ℝ} (p : GeometricParameters L) :
    IsProbabilityMeasure (streamLaw p) := by
  unfold streamLaw
  infer_instance
def levelMap {L : ℝ} (p : GeometricParameters L) (omega : Omega p) (n : ℕ) :
    StageMaps p n := evaluate p n (truncate p n omega)
def process {L : ℝ} (p : GeometricParameters L) :
    Omega p → (n : ℕ) → StageMaps p n := fun omega n => levelMap p omega n
def streamCounters {L : ℝ} (p : GeometricParameters L) (n time : ℕ) (omega : Omega p) :=
  stageCounters p (n+1) (Fin.last n) time (truncate p (n+1) omega)
def streamSelected {L : ℝ} (p : GeometricParameters L) (n time : ℕ) (omega : Omega p) :=
  stageSelected p (n+1) (Fin.last n) time (truncate p (n+1) omega)
def streamHalts {L : ℝ} (p : GeometricParameters L) (n : ℕ) (omega : Omega p) : Prop :=
  stageHalts p (n+1) (Fin.last n) (truncate p (n+1) omega)
def streamHaltTime {L : ℝ} (p : GeometricParameters L) (n : ℕ) (omega : Omega p) : ℕ :=
  stageHaltTime p (n+1) (Fin.last n) (truncate p (n+1) omega)
def streamGeometricOutput {L : ℝ} (p : GeometricParameters L) (n : ℕ) (omega : Omega p) :=
  stageGeometricOutput p (n+1) (Fin.last n) (truncate p (n+1) omega)
def streamPerturbedOutput {L : ℝ} (p : GeometricParameters L) (n : ℕ) (omega : Omega p) :=
  stagePerturbedOutput p (n+1) (Fin.last n) (truncate p (n+1) omega)
def streamPhysicalOutput {L : ℝ} (p : GeometricParameters L) (n : ℕ) (omega : Omega p) :=
  stagePhysicalOutput p (n+1) (Fin.last n) (truncate p (n+1) omega)
end QEC.Coding.BDL26CountableEmbeddingExperiment


