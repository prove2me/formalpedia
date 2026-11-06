-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionRefinement
-- name    : QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionRefinement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:13:57.306557+00:00
-- url     : https://prove2.me/theorems/1acd564b-c2de-46a8-83c8-0116033a842b
-- title:
--   Basic Projection Refinement
-- statement:
--   Definitions and structural lemmas for Basic Projection Refinement, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BasicProjectionRefinement.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_TraceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionFields
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable (A F E : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [_root_.Field F] [_root_.Field E] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [Algebra F256 F] [Algebra F256 E] [IsScalarTower F256 F E]
    [Module.Finite A (integralClosure A E)]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))
end
section Rational
variable {E : Type*} [_root_.Field E] [Algebra F256 E]
    (x : E) (hx : Transcendental F256 x) (y : E)
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A F256⟮x⟯] [IsFractionRing A F256⟮x⟯]
    [Algebra A E] [IsScalarTower A F256⟮x⟯ E]
    [FiniteDimensional F256⟮x⟯ E] [Algebra.IsSeparable F256⟮x⟯ E]
    [Module.Finite A (integralClosure A E)]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))
end Rational
noncomputable section
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


