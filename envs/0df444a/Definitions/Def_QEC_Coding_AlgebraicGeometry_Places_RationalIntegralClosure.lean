-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalIntegralClosure
-- name    : QEC_Coding_AlgebraicGeometry_Places_RationalIntegralClosure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:42:59.448988+00:00
-- url     : https://prove2.me/theorems/4f087948-7a16-4d72-977b-5d0bd9481fb5
-- title:
--   Rational Integral Closure
-- statement:
--   Definitions and structural lemmas for Rational Integral Closure, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalIntegralClosure.lean

import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.IsIntegral
set_option autoImplicit false
open scoped Polynomial RatFunc
namespace QEC.Coding.AlgebraicGeometry.RatFuncFixtureDirectIntegralClosure
abbrev K : Type := ZMod 2
local instance _p2m_local_instance_c6523eaeb4_13 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
abbrev F : Type := RatFunc K
abbrev B : Type := FunctionField.ringOfIntegers K F
local instance _p2m_local_instance_c6523eaeb4_18 : IsIntegralClosure K[X] K[X] F :=
  IsIntegralClosure.of_isIntegrallyClosed K[X] K[X] F
noncomputable def ringOfIntegersToPolynomial : B ≃ₐ[K[X]] K[X] :=
  IsIntegralClosure.equiv K[X] B F K[X]
noncomputable def directIntegralClosureEquiv : K[X] ≃ₐ[K[X]] B :=
  ringOfIntegersToPolynomial.symm
end QEC.Coding.AlgebraicGeometry.RatFuncFixtureDirectIntegralClosure


