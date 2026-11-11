-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T02:13:12.118415+00:00
-- url     : https://prove2.me/theorems/3b2afa34-3e85-4dfc-88e3-9fbb67307719
-- title:
--   Finite Experiment
-- statement:
--   Definitions and structural lemmas for Finite Experiment, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
abbrev StagePresentation {L : ℝ} (p : GeometricParameters L) (n : ℕ) :=
  (state (perturbationOddScale p) n).presentation
def stageCounters {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (time : ℕ) (z : Experiment p n) :=
  counters (eventSupport (StagePresentation p i.val) (stageInput p n i z) (anchorRadius p.m))
    (eventBad (StagePresentation p i.val) (stageInput p n i z)
      (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) (tableAt p n i z) time
def stageSelected {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (time : ℕ) (z : Experiment p n) : Option (MasterEvent (StagePresentation p i.val)) :=
  (selected (eventSupport (StagePresentation p i.val) (stageInput p n i z) (anchorRadius p.m))
    (eventBad (StagePresentation p i.val) (stageInput p n i z)
      (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) (tableAt p n i z) time).map
        (eventToMaster (StagePresentation p i.val) (stageInput p n i z) (anchorRadius p.m))
def stageHalts {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (z : Experiment p n) : Prop :=
  Halts (eventSupport (StagePresentation p i.val) (stageInput p n i z) (anchorRadius p.m))
    (eventBad (StagePresentation p i.val) (stageInput p n i z)
      (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) (tableAt p n i z)
def stageHaltTime {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (z : Experiment p n) : ℕ :=
  haltTime (eventSupport (StagePresentation p i.val) (stageInput p n i z) (anchorRadius p.m))
    (eventBad (StagePresentation p i.val) (stageInput p n i z)
      (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) (tableAt p n i z)
def stageGeometricOutput {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (z : Experiment p n) : StageMaps p i.val :=
  geometricOutput (StagePresentation p i.val) (stageInput p n i z) p (tableAt p n i z)
def stagePerturbedOutput {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (z : Experiment p n) : StageMaps p i.val :=
  perturbationEmbeddingOutput (StagePresentation p i.val) (stageInput p n i z) p (tableAt p n i z)
def stagePhysicalOutput {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (z : Experiment p n) : StageMaps p (i.val+1) :=
  physicalSuccessorOutput p i.val (stageInput p n i z) (tableAt p n i z)
end QEC.Coding.BDL26FiniteEmbeddingExperiment


