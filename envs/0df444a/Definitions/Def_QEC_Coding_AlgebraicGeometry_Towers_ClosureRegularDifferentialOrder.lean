-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureRegularDifferentialOrder
-- name    : QEC_Coding_AlgebraicGeometry_Towers_ClosureRegularDifferentialOrder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:18:26.470895+00:00
-- url     : https://prove2.me/theorems/2102ee78-f753-4c98-911a-a20569491fe4
-- title:
--   Closure Regular Differential Order
-- statement:
--   Definitions and structural lemmas for Closure Regular Differential Order, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureRegularDifferentialOrder.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureUnramified
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_WBaseDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialPlaceTransport
set_option autoImplicit false
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] closureDifferent_modelDedekind closureDifferent_modelFinite
  closureDifferent_modelFraction closureDifferent_modelTorsionFree
variable (m : ℕ) (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A (sourceClosureWBase m)] [IsFractionRing A (sourceClosureWBase m)]
    [Algebra A (SourceGaloisClosureField m)]
    [IsScalarTower A (sourceClosureWBase m) (SourceGaloisClosureField m)]
    [Module.IsTorsionFree A (SourceGaloisClosureField m)]
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


