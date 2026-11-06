-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialTrace
-- name    : QEC_Coding_AlgebraicGeometry_Differentials_DifferentialTrace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:23:53.599336+00:00
-- url     : https://prove2.me/theorems/64555677-8ed2-409f-a561-919b7b4bb314
-- title:
--   Differential Trace
-- statement:
--   Definitions and structural lemmas for Differential Trace, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialTrace.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DerivationTrace
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
namespace FunctionFieldDifferential
open scoped RatFunc
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]
noncomputable def functionFieldDifferentialTrace :
    Differential k F →ₗ[RatFunc k] Differential k (RatFunc k) :=
  (functionFieldDifferentialGeneratorMap (k := k) (F := RatFunc k)).comp
    ((Algebra.trace (RatFunc k) F).comp
      ((functionFieldDifferentialCoordinate (k := k) (F := F)).restrictScalars
        (RatFunc k)))
end FunctionFieldDifferential
end QEC.Coding.AlgebraicGeometry


