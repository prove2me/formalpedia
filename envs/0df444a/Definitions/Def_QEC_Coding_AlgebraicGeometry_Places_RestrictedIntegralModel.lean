-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RestrictedIntegralModel
-- name    : QEC_Coding_AlgebraicGeometry_Places_RestrictedIntegralModel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:18:19.932293+00:00
-- url     : https://prove2.me/theorems/4737f472-b8f9-47cc-af94-d3fce6fbb2bc
-- title:
--   Restricted Integral Model
-- statement:
--   Definitions and structural lemmas for Restricted Integral Model, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RestrictedIntegralModel.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_NormalizedRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralModelCentre
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
noncomputable section
variable {k F E : Type*} [Field k] [Finite k] [Field F] [Field E]
    [Algebra k F] [Algebra k E] [Algebra F E] [Algebra.IsAlgebraic F E]
    (Q : GlobalPlace k E)
local notation "P" => Q.restrict (F := F)
local notation "A" => GlobalPlace.valuationRing (GlobalPlace.restrict (F := F) Q)
local notation "C" => integralClosure A E
variable [Algebra (Q.restrict (F := F)).valuationRing E]
    [IsScalarTower (Q.restrict (F := F)).valuationRing F E]
end
end QEC.Coding.AlgebraicGeometry.GlobalPlace


