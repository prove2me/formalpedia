-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_StepTransport
-- name    : QEC_Coding_AlgebraicGeometry_Towers_StepTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:45:08.339368+00:00
-- url     : https://prove2.me/theorems/d39a710b-a175-426b-9947-4a043771d79d
-- title:
--   Step Transport
-- statement:
--   Definitions and structural lemmas for Step Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/StepTransport.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
theorem stepPolynomial_eq_explicit_transport
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    stepPolynomial P x hx =
      X ^ 16 + C (x⁻¹ ^ 16) * X ^ 15 + C x⁻¹ := by
  simp [stepPolynomial, reciprocalPolynomial, coe_reciprocalUniformizer]
  rw [← map_pow, inv_pow]
theorem stepPolynomial_eq_of_place
    (P Q : GlobalPlace F256 K) (x : K)
    (hP : P.order x = -1) (hQ : Q.order x = -1) :
    stepPolynomial P x hP = stepPolynomial Q x hQ := by
  rw [stepPolynomial_eq_explicit_transport,
    stepPolynomial_eq_explicit_transport]
noncomputable def stepFieldEquiv
    (P Q : GlobalPlace F256 K) (x : K)
    (hP : P.order x = -1) (hQ : Q.order x = -1) :
    StepField P x hP ≃ₐ[K] StepField Q x hQ :=
  AdjoinRoot.algEquivOfEq K
    (stepPolynomial P x hP) (stepPolynomial Q x hQ)
    (stepPolynomial_eq_of_place P Q x hP hQ)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


