-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualOrdinaryPolynomialTranscendence
-- name    : MazurTransfer_Order13ActualOrdinaryPolynomialTranscendence
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T09:56:22.121429+00:00
-- url     : https://prove2.me/theorems/a9978368-7e85-460c-a26a-952bb1cc47f7
-- title:
--   Transcendence and integral ordinary-coordinate structure for the actual rational curve
-- statement:
--   For the literal order-thirteen curve over $\mathbb Q$, the ordinary-coordinate embedding defines the specified polynomial algebra homomorphism into its actual function field. It agrees with evaluation at the original coordinate $x$, and $$x\text{ is transcendental over }\mathbb Q,\qquad x+1\ne0.$$ The ordinary coordinate algebra is integral over $\mathbb Q[X]$. These facts give the injectivity and denominator conditions required to extend the diamond coordinate substitution to the actual function field.
-- source:
--   Original complete Order13ActualOrdinaryPolynomialTranscendence.lean from MazurTheorem, Apache-2.0, Vas and contributors. All six original declarations and bodies are unchanged; the import becomes the public original ordinary-coordinate interface. Six original closed types and two data values (the polynomial embedding and polynomial algebra homomorphism) are kernel-compared. Native, strict and complete frontend checks pass with standard axioms only. Named downstream consumer: the actual rational diamond coordinate injection and function-field automorphism.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the ordinary abscissa in the actual rational scheme
function field is transcendental, and its coordinate algebra is integral
over Q[X]. Named downstream consumer: the diamond coordinate map's
injectivity and its extension to a genuine function-field automorphism.
-/
import Definitions.Def_MazurTransfer_Order13ActualOrdinaryFunctionFieldCoordinates

noncomputable section
namespace MazurTransfer.Order13ActualOrdinaryPolynomialTranscendence
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart Order13ChartOverlapFunctionField
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

def polynomialEmbedding : Polynomial ℚ →+* actualCurveFunctionField ℚ :=
  (algebraMap (CoordinateRing ℚ) (actualCurveFunctionField ℚ)).comp (AdjoinRoot.of (affineEquation ℚ))

def polynomialAlgHom : Polynomial ℚ →ₐ[ℚ] actualCurveFunctionField ℚ where
  __ := polynomialEmbedding
  commutes' r := RingHom.congr_fun (Subsingleton.elim
    (polynomialEmbedding.comp (algebraMap ℚ (Polynomial ℚ)))
    (algebraMap ℚ (actualCurveFunctionField ℚ))) r

theorem polynomialAlgHom_eq_aeval : polynomialAlgHom = aeval (xImage ℚ) := by
  apply Polynomial.algHom_ext
  rw [Polynomial.aeval_X]
  rfl

theorem xImage_transcendental : Transcendental ℚ (xImage ℚ) := by
  apply transcendental_iff_injective.mpr
  rw [← polynomialAlgHom_eq_aeval]
  exact (IsFractionRing.injective (CoordinateRing ℚ) (actualCurveFunctionField ℚ)).comp
    (Order13SingleSectionFiniteAlgebra.ordinary_polynomial_inclusion_injective ℚ)

theorem xImage_add_one_ne_zero : xImage ℚ + 1 ≠ 0 := by
  intro H
  have Hx : xImage ℚ = -1 := by linear_combination H
  apply xImage_transcendental
  rw [Hx]
  exact isIntegral_one.neg.isAlgebraic

theorem ordinary_isIntegral : Algebra.IsIntegral (Polynomial ℚ) (CoordinateRing ℚ) := by
  have H : (affineEquation ℚ).Monic := by
    exact Polynomial.monic_X_pow_sub_C _ (by decide : 2 ≠ 0)
  let : Module.Finite (Polynomial ℚ) (CoordinateRing ℚ) := H.finite_adjoinRoot
  exact Algebra.IsIntegral.of_finite _ _

end MazurTransfer.Order13ActualOrdinaryPolynomialTranscendence
#print axioms MazurTransfer.Order13ActualOrdinaryPolynomialTranscendence.xImage_transcendental
#print axioms MazurTransfer.Order13ActualOrdinaryPolynomialTranscendence.ordinary_isIntegral


