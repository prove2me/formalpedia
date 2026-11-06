-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RatFuncRationalInfinityDegreeTransport
-- name    : QEC_Coding_AlgebraicGeometry_Places_RatFuncRationalInfinityDegreeTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:19:18.130595+00:00
-- url     : https://prove2.me/theorems/86f2c40f-7a5f-4cbb-95c9-d0f393e4bd97
-- title:
--   Rat Func Rational Infinity Degree Transport
-- statement:
--   Definitions and structural lemmas for Rat Func Rational Infinity Degree Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RatFuncRationalInfinityDegreeTransport.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RatFuncInverseInfinityValuation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces
open scoped Polynomial RatFunc WithZero
open RatFuncInverseInfinityValuation
local instance _p2m_local_instance_137389a7d4_9 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
noncomputable local instance fixtureOldRationalAlgebra : Algebra K⟮X⟯ F :=
  RatFuncFixturePlaces.oldRationalAlgebra
noncomputable local instance fixtureOldPolynomialAlgebra : Algebra K[X] F :=
  RatFuncFixturePlaces.oldPolynomialAlgebra
noncomputable local instance fixtureOldScalarTower : IsScalarTower K[X] K⟮X⟯ F :=
  RatFuncFixturePlaces.oldScalarTower
noncomputable local instance fixtureOldFunctionField : _root_.FunctionField K F :=
  RatFuncFixturePlaces.oldFunctionField
noncomputable local instance fixtureOldSeparable : Algebra.IsSeparable K⟮X⟯ F :=
  RatFuncFixturePlaces.oldSeparable
abbrev ratFuncRationalInfinityDegreeTransport_inverseScalarTowerType : Prop :=
  @IsScalarTower K[X] K⟮X⟯ F RatFunc.instSMulOfFractionRingPolynomial
    (InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := fixtureOldRationalAlgebra) K F).toSMul
    (InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := fixtureOldRationalAlgebra) K F).toSMul
end QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces


