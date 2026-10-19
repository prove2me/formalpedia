-- Prove2me | Definitions.Def_MazurTransfer_Order13DiamondSexticCoordinateTransform
-- name    : MazurTransfer_Order13DiamondSexticCoordinateTransform
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T10:07:42.851959+00:00
-- url     : https://prove2.me/theorems/0d18b09c-79f2-41ec-8aa7-3cd2e6b1c4f3
-- title:
--   The original diamond coordinate substitution and sextic covariance
-- statement:
--   For a field $F$, set $$d_X(x)=-\frac1{x+1},\qquad d_Y(x,y)=\frac{y}{(x+1)^3}.$$ Whenever $x+1\ne0$, the literal sextic satisfies $(x+1)^6s(d_X(x))=s(x)$, so the substitution preserves $y^2=s(x)$. Its inverse coordinate expression is $x=-d_X(x)^{-1}-1$. These original formulas supply the rational function-field diamond map.
-- source:
--   Original complete diamondX, diamondY, covariance, preserves_curve and inverse_expression declarations and bodies from MazurTheorem Order13DiamondSexticSymmetry.lean, Apache-2.0, Vas and contributors. Coefficients and formulas adapt MazurTheorem XOneThirteenDescent.lean at exact source pin 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. The transcendence argument is a separate theorem node. Five full original closed types and two data values are kernel-compared; native, strict and complete frontend checks pass with standard axioms only. Named downstream consumer: the actual rational diamond coordinate-ring injection and function-field automorphism.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
The explicit substitution and identities adapt MazurTheorem's
XOneThirteenDescent.lean, at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c.
Design boundary: sextic covariance and the inverse fractional-linear
substitution over a field. Named downstream consumer: the actual order-13
function-field diamond automorphism for the nineteen-isogeny descent.
-/
import Definitions.Def_MazurTransfer_Order13LiteralSextic

noncomputable section
universe u v
namespace MazurTransfer.Order13DiamondSexticSymmetry
open Order13PellChartCertificate
variable {F : Type u} [Field F]

def diamondX (x : F) : F := -1 / (x + 1)
def diamondY (x y : F) : F := y / (x + 1) ^ 3

theorem covariance (x : F) (hx : x + 1 ≠ 0) :
    (x + 1) ^ 6 * sextic (diamondX x) = sextic x := by
  dsimp [diamondX, sextic]
  field_simp [hx] <;> ring

theorem preserves_curve (x y : F) (hx : x + 1 ≠ 0) (hy : y ^ 2 = sextic x) :
    diamondY x y ^ 2 = sextic (diamondX x) := by
  have H := covariance x hx
  dsimp [diamondY]
  field_simp [hx]
  rw [hy]
  exact H.symm

theorem inverse_expression (x : F) (hx : x + 1 ≠ 0) :
    x = -(diamondX x)⁻¹ - 1 := by
  dsimp [diamondX]
  field_simp [hx] <;> ring



end MazurTransfer.Order13DiamondSexticSymmetry
#print axioms MazurTransfer.Order13DiamondSexticSymmetry.covariance
#print axioms MazurTransfer.Order13DiamondSexticSymmetry.preserves_curve


