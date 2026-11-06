-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
-- name    : QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:13:21.835204+00:00
-- url     : https://prove2.me/theorems/6e2f72d0-dcb4-450d-8a25-05f2a7778ec6
-- title:
--   Affine Place Degree
-- statement:
--   Definitions and structural lemmas for Affine Place Degree, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffinePlaceDegree.lean

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
namespace AffinePlace
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
noncomputable abbrev basePrime (P : carrier k F) : Ideal k[X] :=
  P.asIdeal.under k[X]
theorem finite_ringOfIntegers :
    Module.Finite k[X] (_root_.FunctionField.ringOfIntegers k F) :=
  IsIntegralClosure.finite k[X] k⟮X⟯ F (_root_.FunctionField.ringOfIntegers k F)
theorem basePrime_ne_bot (P : carrier k F) : basePrime k F P ≠ ⊥ :=
  Ideal.under_ne_bot k[X] P.ne_bot
theorem finite_basePrime_quotient (P : carrier k F) :
    Module.Finite k (k[X] ⧸ basePrime k F P) := by
  classical
  rw [← Ideal.span_singleton_generator (basePrime k F P)]
  change Module.Finite k (AdjoinRoot (Submodule.IsPrincipal.generator (basePrime k F P)))
  exact
    (AdjoinRoot.powerBasis (by
      rw [Ne, ← Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero]
      exact basePrime_ne_bot k F P)).finite
theorem finite_residueField (P : carrier k F) : Finite (residueField k F P) := by
  let B : Type _ := _root_.FunctionField.ringOfIntegers k F
  let p : Ideal k[X] := basePrime k F P
  letI : Module.Finite k[X] B := finite_ringOfIntegers k F
  letI : Module.Finite k (k[X] ⧸ p) := finite_basePrime_quotient k F P
  letI : Finite (k[X] ⧸ p) := Module.finite_of_finite k
  letI : Module.Finite (k[X] ⧸ p) (B ⧸ P.asIdeal) := by
    change Module.Finite (k[X] ⧸ P.asIdeal.under k[X])
      (_root_.FunctionField.ringOfIntegers k F ⧸ P.asIdeal)
    infer_instance
  letI : Module.Finite (B ⧸ P.asIdeal) (residueField k F P) :=
    Module.Finite.of_surjective (Algebra.linearMap _ _)
      P.asIdeal.bijective_algebraMap_quotient_residueField.surjective
  letI : Algebra (k[X] ⧸ p) (residueField k F P) :=
    ((algebraMap (B ⧸ P.asIdeal) (residueField k F P)).comp
      (algebraMap (k[X] ⧸ p) (B ⧸ P.asIdeal))).toAlgebra
  letI : IsScalarTower (k[X] ⧸ p) (B ⧸ P.asIdeal) (residueField k F P) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Module.Finite (k[X] ⧸ p) (residueField k F P) :=
    Module.Finite.trans (B ⧸ P.asIdeal) (residueField k F P)
  exact Module.finite_of_finite (k[X] ⧸ p)
theorem residueField_finiteDimensional (P : carrier k F) :
    letI : Algebra k (residueField k F P) := residueAlgebra k F P
    FiniteDimensional k (residueField k F P) := by
  letI : Algebra k (residueField k F P) := residueAlgebra k F P
  letI : Finite (residueField k F P) := finite_residueField k F P
  exact (Module.finite_iff_finite).mpr inferInstance
noncomputable def residueDegree (P : carrier k F) : ℕ := by
  letI : Algebra k (residueField k F P) := residueAlgebra k F P
  letI : FiniteDimensional k (residueField k F P) :=
    residueField_finiteDimensional k F P
  exact Module.finrank k (residueField k F P)
noncomputable def divisorDegree (D : Divisor (carrier k F)) : ℤ :=
  Divisor.degree (residueDegree k F) D
structure Rational (P : carrier k F) where
  constantsEquiv : k ≃+* residueField k F P
  constantsEquiv_apply (a : k) :
    constantsEquiv a = constantsToResidue k F P a
namespace Rational
end Rational
end AffinePlace
end QEC.Coding.AlgebraicGeometry


