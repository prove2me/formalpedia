-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureFullConstants
-- name    : QEC_Coding_AlgebraicGeometry_Towers_ClosureFullConstants
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T21:42:14.277331+00:00
-- url     : https://prove2.me/theorems/5c7d30cb-8d5c-496e-acc6-f0dd08f91690
-- title:
--   Closure Full Constants
-- statement:
--   Definitions and structural lemmas for Closure Full Constants, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureFullConstants.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlaceFullConstants
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedPlaces
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosureSelectedLength_lower_bound
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_isFullConstantField_of_rationalPlace

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
scoped instance sourceClosureFullConstants (m : ℕ) :
    IsFullConstantField F256 (SourceGaloisClosureField m) :=
  isFullConstantField_of_rationalPlace
    (sourceGaloisClosureSelectedRationalPlace m
      ⟨0, lt_of_lt_of_le (by positivity) (sourceGaloisClosureSelectedLength_lower_bound m)⟩)
scoped instance sourceClosurePolynomialAlgebra (m : ℕ) :
    Algebra (Polynomial F256) (SourceGaloisClosureField m) :=
  ((algebraMap (RatFunc F256) (SourceGaloisClosureField m)).comp
    (algebraMap (Polynomial F256) (RatFunc F256))).toAlgebra
scoped instance sourceClosurePolynomialTower (m : ℕ) :
    IsScalarTower (Polynomial F256) (RatFunc F256) (SourceGaloisClosureField m) :=
  IsScalarTower.of_algebraMap_eq' rfl
theorem sourceClosureDirectConstant_eq (m : ℕ) :
    @AffinePlace.constantAlgebra F256 (SourceGaloisClosureField m) _ _
      (sourceClosurePolynomialAlgebra m) = sourceGaloisClosureConstantAlgebra m := by
  apply Algebra.algebra_ext
  intro c
  change algebraMap (RatFunc F256) (SourceGaloisClosureField m)
    (algebraMap (Polynomial F256) (RatFunc F256) (Polynomial.C c)) =
      algebraMap F256 (SourceGaloisClosureField m) c
  rw [RatFunc.algebraMap_C]
  exact (IsScalarTower.algebraMap_apply F256 (RatFunc F256) (SourceGaloisClosureField m) c).symm
scoped instance sourceClosureDirectFullConstants (m : ℕ) :
    @IsFullConstantField F256 (SourceGaloisClosureField m) _ _
      (@AffinePlace.constantAlgebra F256 (SourceGaloisClosureField m) _ _
        (sourceClosurePolynomialAlgebra m)) := by
  rw [sourceClosureDirectConstant_eq]
  exact sourceClosureFullConstants m
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


