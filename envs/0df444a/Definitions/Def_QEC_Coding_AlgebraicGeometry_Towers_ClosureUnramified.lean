-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureUnramified
-- name    : QEC_Coding_AlgebraicGeometry_Towers_ClosureUnramified
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:14:59.33448+00:00
-- url     : https://prove2.me/theorems/a18861b6-edcc-475f-bf10-b62fa22d383d
-- title:
--   Closure Unramified
-- statement:
--   Definitions and structural lemmas for Closure Unramified, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureUnramified.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureRegularRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularRefinementRamification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPrincipalDivisor
set_option autoImplicit false
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


