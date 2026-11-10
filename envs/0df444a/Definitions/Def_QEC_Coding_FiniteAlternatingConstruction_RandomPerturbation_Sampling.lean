-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Sampling
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Sampling
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T02:51:41.544138+00:00
-- url     : https://prove2.me/theorems/f22c6f19-de34-454f-88c7-963a100f5b7a
-- title:
--   Sampling
-- statement:
--   Definitions and structural lemmas for Sampling, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Sampling.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Coloring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_TriangleHit
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_capDisplacementLaw_isProbabilityMeasure

set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
noncomputable def vertexAxis (P : TannerSquarePresentation) (v : Vertex P) : Sphere :=
  coordinateAxis (vertexColor P v)
noncomputable def vertexLaw (P : TannerSquarePresentation) (R c : ℝ) (v : Vertex P) :
    Measure Space := capDisplacementLaw R (vertexAxis P v) c
theorem vertexLaw_probability (P : TannerSquarePresentation) (R : ℝ) {c : ℝ} (hc : c < 1)
    (v : Vertex P) : IsProbabilityMeasure (vertexLaw P R c v) :=
  capDisplacementLaw_isProbabilityMeasure R (vertexAxis P v) hc
end QEC.Coding.BDL26RandomPerturbation


