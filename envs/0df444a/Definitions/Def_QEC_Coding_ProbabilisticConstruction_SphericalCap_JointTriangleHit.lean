-- Prove2me | Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_JointTriangleHit
-- name    : QEC_Coding_ProbabilisticConstruction_SphericalCap_JointTriangleHit
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:08:35.684086+00:00
-- url     : https://prove2.me/theorems/cdff71a7-b4cd-4d87-b57e-198f1965299b
-- title:
--   Joint Triangle Hit
-- statement:
--   Definitions and structural lemmas for Joint Triangle Hit, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/JointTriangleHit.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
set_option autoImplicit false
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped BigOperators
abbrev TriangleHitData := (Fin 3 → Space) × Space × ℝ × (Fin 3 → Space)
end QEC.Coding.ProbabilisticConstruction.SphericalCap


