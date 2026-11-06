-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RefinementBaseTransport
-- name    : QEC_Coding_AlgebraicGeometry_Towers_RefinementBaseTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:10:10.356054+00:00
-- url     : https://prove2.me/theorems/7ae4a175-c5ea-48ac-bd34-a90815882687
-- title:
--   Refinement Base Transport
-- statement:
--   Definitions and structural lemmas for Refinement Base Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RefinementBaseTransport.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrderTransport
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable (A B F K E : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [_root_.Field F] [_root_.Field K] [_root_.Field E]
    [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E]
    [Algebra A F] [IsFractionRing A F] [Algebra A E] [IsScalarTower A F E]
    [Algebra B K] [IsFractionRing B K] [Algebra B E] [IsScalarTower B K E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    [Algebra F256 F] [Algebra F256 K] [Algebra F256 E]
    [IsScalarTower F256 F E] [IsScalarTower F256 K E]
    [Module.Finite A (integralClosure A E)] [Module.Finite B (integralClosure B E)]
    [IsDedekindDomain (integralClosure A E)] [IsDedekindDomain (integralClosure B E)]
    [IsFractionRing (integralClosure A E) E] [IsFractionRing (integralClosure B E) E]
    (QA : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))
    (QB : IsDedekindDomain.HeightOneSpectrum (integralClosure B E))
local notation "CA" => IntermediateIntegralModels.Model A F E
local notation "CB" => IntermediateIntegralModels.Model B K E
local notation "PA" => IntermediateIntegralModels.prime A F E QA
local notation "PB" => IntermediateIntegralModels.prime B K E QB
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


