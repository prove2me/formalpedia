-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrincipalCokernelTrace
-- name    : QEC_Coding_AlgebraicGeometry_Trace_PrincipalCokernelTrace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:26:00.040837+00:00
-- url     : https://prove2.me/theorems/3deb2ed7-0b7a-46ed-ac19-213696bfb3fa
-- title:
--   Principal Cokernel Trace
-- statement:
--   Definitions and structural lemmas for Principal Cokernel Trace, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrincipalCokernelTrace.lean

import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Operations
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_SmithTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
universe u v
variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
noncomputable local instance principalCokernelModuleFinite
    [Module.Finite R S] (t : S) :
    Module.Finite R (S ⧸ LinearMap.range (Algebra.lmul R S t)) :=
  Module.Finite.quotient R (LinearMap.range (Algebra.lmul R S t))
noncomputable local instance idealQuotientModuleFinite
    [Module.Finite R S] (I : Ideal S) : Module.Finite R (S ⧸ I) :=
  Module.Finite.quotient R I
theorem range_lmul_eq_restrictScalars_span_singleton (t : S) :
    LinearMap.range (Algebra.lmul R S t) =
      (Ideal.span ({t} : Set S)).restrictScalars R := by
  change LinearMap.range (LinearMap.mul R S t) =
    (Ideal.span ({t} : Set S)).restrictScalars R
  exact Ideal.range_mul S t
noncomputable def principalCokernelEquivOfEq (t : S) (I : Ideal S)
    (hspan : Ideal.span ({t} : Set S) = I) :
    (S ⧸ LinearMap.range (Algebra.lmul R S t)) ≃ₗ[R]
      S ⧸ I :=
  (Submodule.quotEquivOfEq
      (LinearMap.range (Algebra.lmul R S t))
      (I.restrictScalars R)
      (by rw [range_lmul_eq_restrictScalars_span_singleton t, hspan])).trans
    (Submodule.Quotient.restrictScalarsEquiv R I)
@[simp]
theorem principalCokernelEquivOfEq_mk (t x : S) (I : Ideal S)
    (hspan : Ideal.span ({t} : Set S) = I) :
    principalCokernelEquivOfEq (R := R) t I hspan
        (Submodule.Quotient.mk x) =
      Ideal.Quotient.mk I x :=
  rfl
noncomputable def principalCokernelEquiv (t : S) :
    (S ⧸ LinearMap.range (Algebra.lmul R S t)) ≃ₗ[R]
      S ⧸ Ideal.span ({t} : Set S) :=
  principalCokernelEquivOfEq (R := R) t (Ideal.span ({t} : Set S)) rfl
@[simp]
theorem principalCokernelEquiv_mk (t x : S) :
    principalCokernelEquiv (R := R) t (Submodule.Quotient.mk x) =
      Ideal.Quotient.mk (Ideal.span ({t} : Set S)) x :=
  rfl
theorem lmul_comp_comm (t b : S) :
    (Algebra.lmul R S t).comp (Algebra.lmul R S b) =
      (Algebra.lmul R S b).comp (Algebra.lmul R S t) := by
  apply LinearMap.ext
  intro x
  change t * (b * x) = b * (t * x)
  ring
def principalCokernelMul (t b : S) :
    (S ⧸ LinearMap.range (Algebra.lmul R S t)) →ₗ[R]
      S ⧸ LinearMap.range (Algebra.lmul R S t) :=
  cokernelEndomorphism (Algebra.lmul R S t) (Algebra.lmul R S b)
    (lmul_comp_comm t b)
end QEC.Coding.AlgebraicGeometry


