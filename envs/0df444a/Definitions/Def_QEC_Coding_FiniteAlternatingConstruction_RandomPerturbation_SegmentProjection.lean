-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SegmentProjection
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SegmentProjection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:08:32.702196+00:00
-- url     : https://prove2.me/theorems/3c55a4d8-8c81-4764-81b2-08ed3bb0f601
-- title:
--   Segment Projection
-- statement:
--   Definitions and structural lemmas for Segment Projection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/SegmentProjection.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace
noncomputable def clampUnit (x : ℝ) : ℝ := max 0 (min 1 x)
noncomputable def segmentParameter (a b z : Space) : ℝ :=
  clampUnit (inner ℝ (z-a) (b-a)/‖b-a‖^2)
noncomputable def segmentPoint (a b z : Space) : Space :=
  a+segmentParameter a b z • (b-a)
end QEC.Coding.BDL26RandomPerturbation


