-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RefinementEndpoints
-- name    : QEC_Coding_AlgebraicGeometry_Towers_RefinementEndpoints
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:09:58.83659+00:00
-- url     : https://prove2.me/theorems/b17d57b0-edb1-48bc-b21f-2c705b219d20
-- title:
--   Refinement Endpoints
-- statement:
--   Definitions and structural lemmas for Refinement Endpoints, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RefinementEndpoints.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable (A F E : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [_root_.Field F] [_root_.Field E] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [Module.IsTorsionFree A E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [Algebra F256 F] [Algebra F256 E] [IsScalarTower F256 F E]
    [IsDedekindDomain (integralClosure A E)] [Module.Finite A (integralClosure A E)]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))
local instance endpointAmbientModelTorsionFree : Module.IsTorsionFree A (integralClosure A E) :=
  IsIntegralClosure.isTorsionFree A E
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


