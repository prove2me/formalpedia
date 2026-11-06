-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
-- name    : QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:10:35.974262+00:00
-- url     : https://prove2.me/theorems/45e8c230-4f89-491d-ae1f-37764c76ab0d
-- title:
--   Affine Principal Divisor
-- statement:
--   Definitions and structural lemmas for Affine Principal Divisor, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/AffinePrincipalDivisor.lean

import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.DedekindDomain.Factorization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero nonZeroDivisors
namespace AffinePlace
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
noncomputable local instance _p2m_local_instance_63657f3d4b_35 : Algebra k F := constantAlgebra k F
noncomputable def affinePrincipalCoefficient (P : carrier k F) (f : Fˣ) : ℤ :=
  -(P.valuationOfNeZero f).toAdd
theorem affinePrincipalCoefficient_eventually_zero (f : Fˣ) :
    ∀ᶠ P : carrier k F in Filter.cofinite,
      affinePrincipalCoefficient k F P f = 0 := by
  classical
  let B := _root_.FunctionField.ringOfIntegers k F
  let fraction := IsLocalization.sec B⁰ (f : F)
  have hnum : Ideal.span {fraction.1} ≠ (0 : Ideal B) := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact IsLocalization.sec_fst_ne_zero f.ne_zero
  have hden : Ideal.span {(fraction.2 : B)} ≠ (0 : Ideal B) := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact nonZeroDivisors.coe_ne_zero fraction.2
  filter_upwards [Associates.finite_factors hnum, Associates.finite_factors hden] with P hnumP hdenP
  unfold affinePrincipalCoefficient
  unfold IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero
  unfold IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroToFun
  change -((Multiplicative.ofAdd
    ((Associates.mk P.asIdeal).count (Associates.mk (Ideal.span {fraction.1})).factors : ℤ))⁻¹ /
    (Multiplicative.ofAdd
      ((Associates.mk P.asIdeal).count (Associates.mk (Ideal.span {(fraction.2 : B)})).factors : ℤ))⁻¹).toAdd = 0
  rw [hnumP, hdenP]
  norm_num
theorem affinePrincipalCoefficient_finiteSupport (f : Fˣ) :
    (Function.support (fun P : carrier k F => affinePrincipalCoefficient k F P f)).Finite := by
  change {P : carrier k F | ¬affinePrincipalCoefficient k F P f = 0}.Finite
  exact Filter.eventually_cofinite.mp (affinePrincipalCoefficient_eventually_zero k F f)
noncomputable def affinePrincipalDivisor (f : Fˣ) : Divisor (carrier k F) :=
  Finsupp.ofSupportFinite
    (fun P => affinePrincipalCoefficient k F P f)
    (affinePrincipalCoefficient_finiteSupport k F f)
end AffinePlace
end QEC.Coding.AlgebraicGeometry


