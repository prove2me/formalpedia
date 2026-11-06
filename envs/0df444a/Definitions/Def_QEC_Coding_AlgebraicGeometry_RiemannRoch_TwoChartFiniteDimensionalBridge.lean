-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_TwoChartFiniteDimensionalBridge
-- name    : QEC_Coding_AlgebraicGeometry_RiemannRoch_TwoChartFiniteDimensionalBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:04:51.546088+00:00
-- url     : https://prove2.me/theorems/e8ca97b5-c25a-43e9-83b6-d4f99a08d7a0
-- title:
--   Two Chart Finite Dimensional Bridge
-- statement:
--   Definitions and structural lemmas for Two Chart Finite Dimensional Bridge, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/TwoChartFiniteDimensionalBridge.lean

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_DirectChartCommonDenominator
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_InverseChartDenominatorTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge
open scoped LaurentPolynomial Polynomial RatFunc
variable {k F ι : Type*}
noncomputable def directLaurentLinear (k : Type*) [Field k] :
    LaurentPolynomial k →ₗ[k] RatFunc k where
  toFun := InverseChartDenominatorTransport.directLaurentToRatFunc k
  map_add' := map_add _
  map_smul' := by
    intro c z
    rw [LaurentPolynomial.smul_eq_C_mul]
    rw [map_mul]
    simp [InverseChartDenominatorTransport.directLaurentToRatFunc,
      InverseChartDenominatorTransport.ratFuncXUnit, Algebra.smul_def]
noncomputable def directLaurentWindow (k : Type*) [Field k]
    (lower upper : ℤ) : Submodule k (RatFunc k) :=
  LinearMap.range <|
    (directLaurentLinear k).comp
      (LaurentFiniteWindow.laurentWindow k lower upper).subtype
noncomputable def directLaurentWindowCoordinates (k : Type*) [Field k]
    (ι : Type*) (lower upper : ℤ) : Submodule k (ι →₀ RatFunc k) :=
  LinearMap.range <|
    Finsupp.mapRange.linearMap
      (directLaurentWindow k lower upper).subtype
noncomputable def twoChartScaledCoordinateMap
    [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F]
    (b : Module.Basis ι (RatFunc k) F) (a d : Polynomial k) :
    F →ₗ[k] (ι →₀ RatFunc k) where
  toFun := fun x =>
    (algebraMap (Polynomial k) (RatFunc k) a *
      InverseAffinePlace.rationalInvolution k
        (algebraMap (Polynomial k) (RatFunc k) d)) • b.repr x
  map_add' := by
    intro x y
    simp
  map_smul' := by
    intro c x
    ext j
    have hj := congrArg (fun q : ι →₀ RatFunc k => q j)
      ((b.repr.restrictScalars k).map_smul c x)
    simp only [LinearEquiv.restrictScalars_apply, Finsupp.smul_apply,
      Algebra.smul_def] at hj ⊢
    rw [hj]
    ac_rfl
end QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge


