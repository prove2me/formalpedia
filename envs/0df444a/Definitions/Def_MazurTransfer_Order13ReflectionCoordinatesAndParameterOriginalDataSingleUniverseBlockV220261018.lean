-- Prove2me | Definitions.Def_MazurTransfer_Order13ReflectionCoordinatesAndParameterOriginalDataSingleUniverseBlockV220261018
-- name    : MazurTransfer_Order13ReflectionCoordinatesAndParameterOriginalDataSingleUniverseBlockV220261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T21:04:34.784326+00:00
-- url     : https://prove2.me/theorems/1739f70e-9e85-4f2f-b2bb-b154de5adf1f
-- title:
--   Original order-thirteen reflection coordinates and parameter record
-- statement:
--   The five literal reflection coordinate functions and the original reflection parameter record retain their exact cubic and square equations. Eleven complete original declaration types include the record type, constructor and all four field projections. Seven complete nonproof values include all five functions and both data projections. The original record constructor shape is checked explicitly. Named downstream consumer: MazurTransfer.Order13ActualReflectionFunctionField.reflectionAlgEquiv. Polynomial certificates, parameter existence and automorphism proofs are separate.
-- source:
--   MazurTheorem Order13ReflectionSexticSymmetry reflection coordinate declarations and Order13ReflectionParameter.ReflectionParameter with its complete constructor and field telescope; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13DiamondSexticCoordinateTransform
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Original MazurTheorem reflection-coordinate and parameter declarations.
Design boundary: the literal five reflection coordinate functions and the original parameter record with its exact cubic and square equations. Named downstream consumer: MazurTransfer.Order13ActualReflectionFunctionField.reflectionAlgEquiv. Polynomial identities, parameter existence and automorphism proofs remain separate.
-/
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: explicit reflection identities for the literal order-13
sextic, with every coefficient parameter and denominator hypothesis stated.
Named downstream consumer: the actual curve function-field reflection and
its arithmetic intertwiner for the cyclotomic quotient kernel.
-/
noncomputable section
universe u v
namespace MazurTransfer.Order13ReflectionSexticSymmetry
open Order13PellChartCertificate
variable {F : Type u} [Field F]

def reflectionCubic (t : F) : F := t ^ 3 + 4 * t ^ 2 + t - 1
def reflectionScalar (t : F) : F := t ^ 2 + t + 1
def reflectionDenominator (t x : F) : F := (t + 1) * x + 1
def reflectionX (t x : F) : F := (t - x) / reflectionDenominator t x
def reflectionY (t s x y : F) : F := s ^ 3 * y / reflectionDenominator t x ^ 3

end MazurTransfer.Order13ReflectionSexticSymmetry

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: literal coefficients for an order-13 reflection, together
with transcendence of its fractional-linear coordinate. Named downstream
consumer: the actual scheme function-field reflection automorphism.
-/
noncomputable section
namespace MazurTransfer.Order13ReflectionParameter
open Order13ReflectionSexticSymmetry Polynomial

structure ReflectionParameter (K : Type u) [Field K] where
  t : K
  s : K
  cubic_eq_zero : reflectionCubic t = 0
  square_eq_scalar : s ^ 2 = reflectionScalar t

end MazurTransfer.Order13ReflectionParameter

#print axioms MazurTransfer.Order13ReflectionSexticSymmetry.reflectionCubic
#print axioms MazurTransfer.Order13ReflectionParameter.ReflectionParameter.mk


