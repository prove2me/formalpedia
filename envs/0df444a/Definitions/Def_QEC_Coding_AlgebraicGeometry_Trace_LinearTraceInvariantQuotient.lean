-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_LinearTraceInvariantQuotient
-- name    : QEC_Coding_AlgebraicGeometry_Trace_LinearTraceInvariantQuotient
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:00:47.655762+00:00
-- url     : https://prove2.me/theorems/27fe78b8-b3fb-4007-a636-7ecd8406c94a
-- title:
--   Linear Trace Invariant Quotient
-- statement:
--   Definitions and structural lemmas for Linear Trace Invariant Quotient, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/LinearTraceInvariantQuotient.lean

import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Trace
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
namespace LinearMap
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]
end LinearMap
end QEC.Coding.AlgebraicGeometry


