-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalTraceSeed
-- name    : QEC_Coding_AlgebraicGeometry_Towers_RationalTraceSeed
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:29:02.599653+00:00
-- url     : https://prove2.me/theorems/a5fad057-6b52-43bd-8259-aa029b47b23e
-- title:
--   Rational Trace Seed
-- statement:
--   Definitions and structural lemmas for Rational Trace Seed, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalTraceSeed.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPlaces
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
instance sourceGaloisWField_seedScalarTower :
    IsScalarTower F256 SourceGaloisWField (RatFunc F256) :=
  IsScalarTower.of_algebraMap_eq' rfl
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


