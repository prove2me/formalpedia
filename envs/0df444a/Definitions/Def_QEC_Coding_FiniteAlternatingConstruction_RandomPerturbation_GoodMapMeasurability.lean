-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodMapMeasurability
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodMapMeasurability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T02:34:14.520457+00:00
-- url     : https://prove2.me/theorems/0d8371f1-79de-4921-bbad-c3dac8f01cbe
-- title:
--   Good Map Measurability
-- statement:
--   Definitions and structural lemmas for Good Map Measurability, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GoodMapMeasurability.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Incidence
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_JointTriangleHit
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
def faceBallHit (P : TannerSquarePresentation) (J : Vertex P → Space)
    (f : P.Face) (c : Space) : Prop :=
  ∃ y ∈ tannerFaceImage P J f, dist y c ≤ 1
def boundedLabelHit (P : TannerSquarePresentation) (s : Finset P.Face) (N : ℕ) :
    Set (Vertex P → Space) :=
  {J | ∃ c : Metric.closedBall (0 : Space) (N : ℝ), ∀ f ∈ s, faceBallHit P J f c}
end QEC.Coding.BDL26RandomPerturbation


