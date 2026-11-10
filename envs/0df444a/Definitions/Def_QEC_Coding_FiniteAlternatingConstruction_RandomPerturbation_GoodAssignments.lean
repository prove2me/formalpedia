-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodAssignments
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodAssignments
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T03:15:56.988021+00:00
-- url     : https://prove2.me/theorems/9391458f-1738-463d-ab66-7ad41b88caeb
-- title:
--   Good Assignments
-- statement:
--   Definitions and structural lemmas for Good Assignments, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GoodAssignments.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_AvoidanceDensity
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
noncomputable def geometricLaw (P : TannerSquarePresentation) {L : ℝ}
    (p : GeometricParameters L) :=
  Measure.pi (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))
def geometricSupport (P : TannerSquarePresentation) {L : ℝ}
    (p : GeometricParameters L) : Set (Vertex P → Space) :=
  {w | ∀ v, w v ∈ displacementCap ((6*p.m : ℕ)*(p.lambda : ℝ))
    (vertexAxis P v) (capCutoff p.m)}
noncomputable def geometricAvoidance (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) : Set (Vertex P → Space) :=
  avoid (localEvent (eventSupport P J (anchorRadius p.m))
    (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda))) Finset.univ
end QEC.Coding.BDL26RandomPerturbation


