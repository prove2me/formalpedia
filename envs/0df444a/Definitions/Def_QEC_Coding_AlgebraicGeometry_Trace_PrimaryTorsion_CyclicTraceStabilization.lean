-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicTraceStabilization
-- name    : QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CyclicTraceStabilization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:21:15.6757+00:00
-- url     : https://prove2.me/theorems/fdca9f26-6cad-449e-ab57-f3bf78818740
-- title:
--   Cyclic Trace Stabilization
-- statement:
--   Definitions and structural lemmas for Cyclic Trace Stabilization, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/CyclicTraceStabilization.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_PolynomialQuotientTrace
set_option autoImplicit false
open scoped Polynomial
namespace QEC.Coding.AlgebraicGeometry
variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {k : Type*} [Field k] [Finite k]
end QEC.Coding.AlgebraicGeometry


