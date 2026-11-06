-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_ProdTrace
-- name    : QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_ProdTrace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:42:29.081647+00:00
-- url     : https://prove2.me/theorems/595cc234-2ec8-4a4c-81db-0ca21b3c22a9
-- title:
--   Prod Trace
-- statement:
--   Definitions and structural lemmas for Prod Trace, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/ProdTrace.lean

import Mathlib.LinearAlgebra.Prod
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceFunctorial
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
end QEC.Coding.AlgebraicGeometry


