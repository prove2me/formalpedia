-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferentialDivisor
-- name    : QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferentialDivisor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:23:27.026584+00:00
-- url     : https://prove2.me/theorems/8668571e-7df1-4f08-99b5-e5f99c4f1654
-- title:
--   Closure Differential Divisor
-- statement:
--   Definitions and structural lemmas for Closure Differential Divisor, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureDifferentialDivisor.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureFibreDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureRegularDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential
set_option autoImplicit false
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


