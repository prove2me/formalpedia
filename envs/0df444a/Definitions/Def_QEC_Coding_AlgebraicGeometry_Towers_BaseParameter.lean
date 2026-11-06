-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BaseParameter
-- name    : QEC_Coding_AlgebraicGeometry_Towers_BaseParameter
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:16:48.564747+00:00
-- url     : https://prove2.me/theorems/6790241f-3351-4b6a-9b04-6296d7fa68bf
-- title:
--   Base Parameter
-- statement:
--   Definitions and structural lemmas for Base Parameter, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BaseParameter.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Divisors
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarDegree
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [-instance]
  selectedFieldField
  selectedFieldConstantAlgebra
  selectedFieldRatFuncAlgebra
  selectedFieldConstantTower
  selectedFieldFunctionField
  selectedFieldRatFuncSeparable
@[reducible] noncomputable local instance (priority := 2000)
    basePowerParameterConstantAlgebra (m : ℕ) : Algebra F256 (Field m) :=
  @AffinePlace.constantAlgebra F256 (Field m) _ _ (fieldPolynomialAlgebra m)
@[reducible] noncomputable local instance (priority := 2000)
    basePowerParameterRatFuncAlgebra (m : ℕ) :
    Algebra (RatFunc F256) (Field m) :=
  fieldRatFuncAlgebra m
noncomputable local instance (priority := 2000)
    basePowerParameterFunctionField (m : ℕ) :
    _root_.FunctionField F256 (Field m) :=
  fieldFunctionField m
noncomputable local instance (priority := 2000)
    basePowerParameterSeparable (m : ℕ) :
    Algebra.IsSeparable (RatFunc F256) (Field m) :=
  fieldRatFuncSeparable m
abbrev BasePowerParameterPlace (m : ℕ) : Type :=
  @GlobalPlace F256 (Field m) _ _ _
    (riemannRochPolarFamilyAlgebra
      (π := fieldPolynomialAlgebra m) F256 (Field m))
noncomputable def basePowerParameterResidueDegree (m : ℕ) :
    BasePowerParameterPlace m → ℕ :=
  fun P => GlobalPlace.residueDegree
    (π := fieldPolynomialAlgebra m)
    (ρ := basePowerParameterRatFuncAlgebra m)
    (τ := fieldPolynomialRatFuncTower m)
    (φ := basePowerParameterFunctionField m)
    (σ := basePowerParameterSeparable m)
    (κ := riemannRochPolarFamilyAlgebra
      (π := fieldPolynomialAlgebra m) F256 (Field m)) P
noncomputable def basePowerParameter (m : ℕ) : Field m :=
  GlobalPlace.chartVariable (k := F256) (F := Field m) ^ 17
noncomputable def chartVariablePoleDivisor (m : ℕ) :
    Divisor (BasePowerParameterPlace m) :=
  GlobalPlace.polarDivisor
    (π := fieldPolynomialAlgebra m)
    (ρ := basePowerParameterRatFuncAlgebra m)
    (τ := fieldPolynomialRatFuncTower m)
    (φ := basePowerParameterFunctionField m)
    (s := basePowerParameterSeparable m)
    (k := F256) (F := Field m)
    (GlobalPlace.chartVariable (k := F256) (F := Field m))
noncomputable def basePowerParameterPoleDivisor (m : ℕ) :
    Divisor (BasePowerParameterPlace m) :=
  GlobalPlace.polarDivisor
    (π := fieldPolynomialAlgebra m)
    (ρ := basePowerParameterRatFuncAlgebra m)
    (τ := fieldPolynomialRatFuncTower m)
    (φ := basePowerParameterFunctionField m)
    (s := basePowerParameterSeparable m)
    (k := F256) (F := Field m) (basePowerParameter m)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


