-- Prove2me | Definitions.Def_MazurTransfer_MixedQuadraticOriginalCoordinateEquationAndJacobianData20261019
-- name    : MazurTransfer_MixedQuadraticOriginalCoordinateEquationAndJacobianData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T02:17:23.138911+00:00
-- url     : https://prove2.me/theorems/28e9641d-5fff-4bc6-9f30-817dd669278b
-- title:
--   Original mixed quadratic coordinate algebra and Jacobian elements
-- statement:
--   The original equation y squared plus h times y minus f, its AdjoinRoot coordinate algebra and its two actual Jacobian elements. All four original complete types and whole values are compared with the source. Named downstream consumer: actual ordinary and reciprocal dyadic affine chart smoothness.
-- source:
--   MazurTheorem original mixed quadratic coordinate and integral Jacobian constructions; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the coordinate algebra y^2+h(x)y=f(x), its actual
Jacobian elements and first-order error across square-zero corrections.
Named downstream consumer: the mixed quadratic integral model at two.
-/
import Mathlib

noncomputable section
namespace MazurTransfer.MixedQuadraticCoordinateJacobian
open Polynomial
universe u v
variable (R : Type u) [CommRing R]

def equation (h f : Polynomial R) : Polynomial (Polynomial R) := X ^ 2 + C h * X - C f
abbrev CoordinateRing (h f : Polynomial R) := AdjoinRoot (equation R h f)

def partialX (h f : Polynomial R) : CoordinateRing R h f :=
  AdjoinRoot.of (equation R h f) h.derivative * AdjoinRoot.root (equation R h f) -
    AdjoinRoot.of (equation R h f) f.derivative

def partialY (h f : Polynomial R) : CoordinateRing R h f :=
  2 * AdjoinRoot.root (equation R h f) + AdjoinRoot.of (equation R h f) h

end MazurTransfer.MixedQuadraticCoordinateJacobian
#print axioms MazurTransfer.MixedQuadraticCoordinateJacobian.equation
#print axioms MazurTransfer.MixedQuadraticCoordinateJacobian.CoordinateRing
#print axioms MazurTransfer.MixedQuadraticCoordinateJacobian.partialX
#print axioms MazurTransfer.MixedQuadraticCoordinateJacobian.partialY


