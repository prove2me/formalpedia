-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferent
-- name    : QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:45:34.605373+00:00
-- url     : https://prove2.me/theorems/639d56ec-75a2-4592-b5da-50e0de2ef301
-- title:
--   Closure Different
-- statement:
--   Definitions and structural lemmas for Closure Different, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureDifferent.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RefinementEndpoints
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable (m : ℕ) (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A (sourceClosureWBase m)] [IsFractionRing A (sourceClosureWBase m)]
    [Algebra A (SourceGaloisClosureField m)]
    [IsScalarTower A (sourceClosureWBase m) (SourceGaloisClosureField m)]
    [Module.IsTorsionFree A (SourceGaloisClosureField m)]
local instance closureDifferent_modelDedekind :
    IsDedekindDomain (integralClosure A (SourceGaloisClosureField m)) :=
  integralClosure.isDedekindDomain A (sourceClosureWBase m) (SourceGaloisClosureField m)
local instance closureDifferent_modelFinite :
    Module.Finite A (integralClosure A (SourceGaloisClosureField m)) :=
  IsIntegralClosure.finite A (sourceClosureWBase m) (SourceGaloisClosureField m)
    (integralClosure A (SourceGaloisClosureField m))
local instance closureDifferent_modelFraction :
    IsFractionRing (integralClosure A (SourceGaloisClosureField m)) (SourceGaloisClosureField m) :=
  integralClosure.isFractionRing_of_finite_extension (sourceClosureWBase m) (SourceGaloisClosureField m)
local instance closureDifferent_modelTorsionFree :
    Module.IsTorsionFree A (integralClosure A (SourceGaloisClosureField m)) :=
  IsIntegralClosure.isTorsionFree A (SourceGaloisClosureField m)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


