-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectPrincipalDegree
-- name    : QEC_Coding_AlgebraicGeometry_Divisors_DirectPrincipalDegree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:11:08.76833+00:00
-- url     : https://prove2.me/theorems/7f08196b-ef05-4581-adf5-1eedc2e073c5
-- title:
--   Direct Principal Degree
-- statement:
--   Definitions and structural lemmas for Direct Principal Degree, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/DirectPrincipalDegree.lean

import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_AffineCountBridge
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectNormCount
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectRelNormCoefficient
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.DirectPrincipalDegree
open scoped BigOperators Polynomial RatFunc WithZero nonZeroDivisors
open UniqueFactorizationMonoid
open Submodule.IsPrincipal
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
noncomputable local instance directPrincipalDegree_constantAlgebra : Algebra k F := AffinePlace.constantAlgebra k F
attribute [local instance] directPrincipalDegree_constantAlgebra
abbrev B : Type _ := _root_.FunctionField.ringOfIntegers k F
abbrev R : Type _ := k[X]
local instance directPrincipalDegree_isTorsionFree : Module.IsTorsionFree (R k) (B k F) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)
attribute [local instance] directPrincipalDegree_isTorsionFree
noncomputable def factorPlaceOfPrime (P : Ideal (B k F)) (hP : Prime P) :
    AffinePlace.carrier k F :=
  { asIdeal := P
    isPrime := Ideal.isPrime_of_prime hP
    ne_bot := by
      simpa only [Ideal.zero_eq_bot] using hP.ne_zero }
noncomputable def factorPlace (I : Ideal (B k F))
    (P : {P : Ideal (B k F) // P ∈ normalizedFactors I}) : AffinePlace.carrier k F :=
  factorPlaceOfPrime k F P.1 (prime_of_normalized_factor P.1 P.2)
noncomputable def factorDivisorOfPrimes (s : Multiset (Ideal (B k F)))
    (hprime : ∀ P ∈ s, Prime P) : Divisor (AffinePlace.carrier k F) :=
  (s.attach.map fun P =>
    Finsupp.single (factorPlaceOfPrime k F P.1 (hprime P.1 P.2)) (1 : Int)).sum
noncomputable def factorDivisor (I : Ideal (B k F)) :
    Divisor (AffinePlace.carrier k F) :=
  factorDivisorOfPrimes k F (normalizedFactors I)
    (fun P hP => prime_of_normalized_factor P hP)
end QEC.Coding.AlgebraicGeometry.DirectPrincipalDegree


