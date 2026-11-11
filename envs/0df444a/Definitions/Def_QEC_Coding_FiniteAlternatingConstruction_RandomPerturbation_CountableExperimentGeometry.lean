-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T02:56:20.460738+00:00
-- url     : https://prove2.me/theorems/519c4727-85b7-4f0e-86e9-af78dd9b3787
-- title:
--   Countable Experiment Geometry
-- statement:
--   Definitions and structural lemmas for Countable Experiment Geometry, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentGeometry.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26ReplacementEmbedding BDL26RandomPerturbation BDL26RandomPhysicalLocality
open BDL26CSSHamiltonian Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
def allFiniteSuccess {L : ℝ} (p : GeometricParameters L) : Set (Omega p) :=
  {omega | ∀ n, truncate p n omega ∈ finiteSuccess p n}
end QEC.Coding.BDL26CountableEmbeddingExperiment


