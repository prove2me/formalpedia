-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T02:16:15.101207+00:00
-- url     : https://prove2.me/theorems/99be23f5-95c3-4e4c-81fd-c8323a6492c8
-- title:
--   Finite Experiment Geometry
-- statement:
--   Definitions and structural lemmas for Finite Experiment Geometry, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentGeometry.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
def finiteSuccess {L : ℝ} (p : GeometricParameters L) (n : ℕ) : Set (Experiment p n) :=
  {z | IsBoundedDensityLocalMap (StagePresentation p 0)
      (BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p)) p.t ∧
    (∀ i : Fin n, stageHalts p n i z) ∧
    ∀ i : Fin (n+1), IsBoundedDensityLocalMap (StagePresentation p i.val) (history p n z i) p.t}
end QEC.Coding.BDL26FiniteEmbeddingExperiment


