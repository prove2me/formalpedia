-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_RationalInfinityTransport
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Inverse_RationalInfinityTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:43:27.553414+00:00
-- url     : https://prove2.me/theorems/05273409-0995-4c6e-bdaa-9f91bf88c66d
-- title:
--   Rational Infinity Transport
-- statement:
--   Definitions and structural lemmas for Rational Infinity Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Inverse/RationalInfinityTransport.lean

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Norm.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport
open scoped LaurentPolynomial Polynomial RatFunc WithZero
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]
noncomputable def xAdicPlace (k : Type*) [Field k] [Finite k] :
    GlobalPlace k (RatFunc k) where
  valuation := (Polynomial.idealX k).valuation (RatFunc k)
  normalized := (Polynomial.idealX k).valuation_surjective (RatFunc k)
noncomputable def directLaurentToRatFunc (k : Type*) [Field k] :
    LaurentPolynomial k →+* RatFunc k :=
  LaurentPolynomial.eval₂ (algebraMap k (RatFunc k))
    (Units.mk0 RatFunc.X RatFunc.X_ne_zero)
noncomputable def inverseLaurentCoordinate (k : Type*) [Field k] :
    k[X] →ₐ[k] LaurentPolynomial k :=
  (LaurentPolynomial.invert (R := k)).toAlgHom.comp Polynomial.toLaurentAlg
noncomputable def rationalInvolutionOnPolynomial (k : Type*) [Field k] [Finite k] :
    k[X] →+* RatFunc k :=
  (InverseAffinePlace.rationalInvolution k).toRingHom.comp
    (algebraMap k[X] (RatFunc k))
end QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport


