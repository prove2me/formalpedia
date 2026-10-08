-- Prove2me | Definitions.Def_MazurTransfer_Order49DoublingCoordinateFormulas
-- name    : MazurTransfer_Order49DoublingCoordinateFormulas
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T03:40:49.16435+00:00
-- url     : https://prove2.me/theorems/2cbb3b17-5393-404e-88d5-e294ae5fe955
-- title:
--   Exact algebraic doubling coordinate and derivative formulas
-- statement:
--   For the rational order-seven family $E_d$ and its prescribed quotient $E_d^\prime$, this package records the original homogeneous coordinate numerators for doubling, the polynomial compositions used to differentiate the explicit coordinate map, its seven specialized coefficient functions, and the predicate expressing compatibility of the affine doubling coordinates. These exact formulas support the proof that the explicit point map respects doubling at points of order $49$. The package contains formulas and predicates; the required polynomial identities and point-map assertions are proved separately.
--
--   Formalization Note: all thirty-one exported values were compared with their exact original kernel constants by kernel-checked reflexivity. Eight originally private formulas are exposed at their original user names by changing declaration visibility only.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; Apache-2.0 headers and attribution retained. Thirty-one exact pure definitions selected by original kernel type dependencies and complete original Lean AST source ranges. Every exported value is compared against the original using standard axioms. Existing exact published selection and cofactor data are reused. Named downstream consumers: original coordinate doubling and derivative certificates, and the full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas


/- Source module: MazurTorsion.EllipticCurve.DoublingCoordinates. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



section
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Doubling



/-- The numerator of the affine doubling abscissa over
`completedCubic`. -/
def xNumerator (W : WeierstrassCurve ℚ) (x : ℚ) : ℚ :=
  x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈

/-- The numerator of the completed ordinate of the affine double over
the cube of the source completed ordinate. -/
def completedYNumerator (W : WeierstrassCurve ℚ) (x : ℚ) : ℚ :=
  2 * x ^ 6 + W.b₂ * x ^ 5 + 5 * W.b₄ * x ^ 4 +
    10 * W.b₆ * x ^ 3 + 10 * W.b₈ * x ^ 2 +
    (W.b₂ * W.b₈ - W.b₄ * W.b₆) * x +
    (W.b₄ * W.b₈ - W.b₆ ^ 2)

/-- Homogenization of `xNumerator` to degree four. -/
def xNumeratorHomogeneous
    {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (u v : R) : R :=
  u ^ 4 - W.b₄ * u ^ 2 * v ^ 2 - 2 * W.b₆ * u * v ^ 3 -
    W.b₈ * v ^ 4

/-- Homogenization of `completedYNumerator` to degree six. -/
def completedYNumeratorHomogeneous
    {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (u v : R) : R :=
  2 * u ^ 6 + W.b₂ * u ^ 5 * v + 5 * W.b₄ * u ^ 4 * v ^ 2 +
    10 * W.b₆ * u ^ 3 * v ^ 3 + 10 * W.b₈ * u ^ 2 * v ^ 4 +
    (W.b₂ * W.b₈ - W.b₄ * W.b₆) * u * v ^ 5 +
    (W.b₄ * W.b₈ - W.b₆ ^ 2) * v ^ 6





















end MazurTorsion.Doubling

end
end


/- Source module: MazurTorsion.Kubert.OrderSevenIsogenyDoublingDerivative. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenDoublingDerivative















noncomputable def completedCubicPolynomial
    (W : WeierstrassCurve ℚ) (u v : ℚ[X]) : ℚ[X] :=
  C 4 * u ^ 3 + C W.b₂ * u ^ 2 * v + C (2 * W.b₄) * u * v ^ 2 +
    C W.b₆ * v ^ 3

noncomputable def doubleXPolynomial
    (W : WeierstrassCurve ℚ) (u v : ℚ[X]) : ℚ[X] :=
  u ^ 4 - C W.b₄ * u ^ 2 * v ^ 2 - C (2 * W.b₆) * u * v ^ 3 -
    C W.b₈ * v ^ 4



noncomputable def veluXPolynomial
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ : ℚ) (u v : ℚ[X]) : ℚ[X] :=
  u ^ 7 + C a₆ * u ^ 6 * v + C a₅ * u ^ 5 * v ^ 2 +
    C a₄ * u ^ 4 * v ^ 3 + C a₃ * u ^ 3 * v ^ 4 +
    C a₂ * u ^ 2 * v ^ 5 + C a₁ * u * v ^ 6 + C a₀ * v ^ 7

noncomputable def kernelPolynomial
    (b c : ℚ) (u v : ℚ[X]) : ℚ[X] :=
  u * (u - C b * v) * (u - C c * v)































noncomputable def sourceCompletedCubic
    (W : WeierstrassCurve ℚ) : ℚ[X] :=
  completedCubicPolynomial W X 1

noncomputable def sourceDoubleX
    (W : WeierstrassCurve ℚ) : ℚ[X] :=
  doubleXPolynomial W X 1



noncomputable def baseVeluX
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ : ℚ) : ℚ[X] :=
  veluXPolynomial a₆ a₅ a₄ a₃ a₂ a₁ a₀ X 1

noncomputable def baseKernel (b c : ℚ) : ℚ[X] :=
  kernelPolynomial b c X 1



noncomputable def composedVeluX
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ : ℚ)
    (W : WeierstrassCurve ℚ) : ℚ[X] :=
  veluXPolynomial a₆ a₅ a₄ a₃ a₂ a₁ a₀
    (sourceDoubleX W) (sourceCompletedCubic W)





noncomputable def targetDoubleX
    (W' : WeierstrassCurve ℚ)
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c : ℚ) : ℚ[X] :=
  doubleXPolynomial W'
    (baseVeluX a₆ a₅ a₄ a₃ a₂ a₁ a₀) (baseKernel b c ^ 2)







end MazurTorsion.Kubert.OrderSevenDoublingDerivative

end


/- Source module: MazurTorsion.Kubert.OrderSevenIsogenyDoublingSpecialization. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenDoublingSpecialization

open OrderSevenDoublingDerivative

def a₆ (d : ℚ) : ℚ := -2 * d * (d - 1) * (d + 1)

def a₅ (d : ℚ) : ℚ :=
  d * (d - 1) *
    (d ^ 5 + 2 * d ^ 4 - 3 * d ^ 3 + 5 * d ^ 2 - 7 * d + 1)

def a₄ (d : ℚ) : ℚ :=
  -d ^ 3 * (d - 1) ^ 2 *
    (6 * d ^ 4 - 9 * d ^ 3 + 12 * d ^ 2 - 13 * d - 1)

def a₃ (d : ℚ) : ℚ :=
  d ^ 4 * (d - 1) ^ 3 *
    (d ^ 5 + d ^ 4 + 4 * d ^ 3 - 8 * d ^ 2 - 7 * d - 1)

def a₂ (d : ℚ) : ℚ :=
  -d ^ 6 * (d - 1) ^ 4 * (d + 1) * (3 * d ^ 2 - 5 * d - 3)

def a₁ (d : ℚ) : ℚ :=
  d ^ 8 * (d - 1) ^ 5 * (d ^ 2 - 3 * d - 3)

def a₀ (d : ℚ) : ℚ := d ^ 10 * (d - 1) ^ 6











end MazurTorsion.Kubert.OrderSevenDoublingSpecialization

end


/- Source module: MazurTorsion.Kubert.OrderSevenIsogenyDoubling. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

 abbrev orderSevenVeluA6 := OrderSevenDoublingSpecialization.a₆
 abbrev orderSevenVeluA5 := OrderSevenDoublingSpecialization.a₅
 abbrev orderSevenVeluA4 := OrderSevenDoublingSpecialization.a₄
 abbrev orderSevenVeluA3 := OrderSevenDoublingSpecialization.a₃
 abbrev orderSevenVeluA2 := OrderSevenDoublingSpecialization.a₂
 abbrev orderSevenVeluA1 := OrderSevenDoublingSpecialization.a₁
 abbrev orderSevenVeluA0 := OrderSevenDoublingSpecialization.a₀

/-- Homogenization of the cleared order-seven Vélu abscissa numerator. -/
def orderSevenVeluXNumeratorHomogeneous
    {R : Type*} [CommRing R] (d u v : R) : R :=
  u ^ 7 - 2 * d * (d - 1) * (d + 1) * u ^ 6 * v +
    d * (d - 1) *
      (d ^ 5 + 2 * d ^ 4 - 3 * d ^ 3 + 5 * d ^ 2 - 7 * d + 1) *
        u ^ 5 * v ^ 2 -
    d ^ 3 * (d - 1) ^ 2 *
      (6 * d ^ 4 - 9 * d ^ 3 + 12 * d ^ 2 - 13 * d - 1) *
        u ^ 4 * v ^ 3 +
    d ^ 4 * (d - 1) ^ 3 *
      (d ^ 5 + d ^ 4 + 4 * d ^ 3 - 8 * d ^ 2 - 7 * d - 1) *
        u ^ 3 * v ^ 4 -
    d ^ 6 * (d - 1) ^ 4 * (d + 1) *
      (3 * d ^ 2 - 5 * d - 3) * u ^ 2 * v ^ 5 +
    d ^ 8 * (d - 1) ^ 5 * (d ^ 2 - 3 * d - 3) * u * v ^ 6 +
    d ^ 10 * (d - 1) ^ 6 * v ^ 7

/-- Homogenization of the cleared order-seven Vélu differential numerator. -/
def orderSevenVeluDifferentialNumeratorHomogeneous
    {R : Type*} [CommRing R] (d u v : R) : R :=
  u ^ 9 - 3 * d * (d - 1) * (d + 1) * u ^ 8 * v -
    d * (d - 1) *
      (d ^ 5 - 2 * d ^ 4 - 12 * d ^ 3 + 14 * d ^ 2 - 3 * d + 1) *
        u ^ 7 * v ^ 2 -
    d ^ 2 * (d - 1) ^ 2 *
      (d ^ 6 - 9 * d ^ 5 + 25 * d ^ 4 - 22 * d ^ 3 +
        16 * d ^ 2 - 4 * d + 1) * u ^ 6 * v ^ 3 +
    3 * d ^ 4 * (d - 1) ^ 3 *
      (d ^ 4 - 7 * d ^ 3 + 13 * d ^ 2 + 2) * u ^ 5 * v ^ 4 +
    d ^ 5 * (d - 1) ^ 4 *
      (d ^ 6 - 10 * d ^ 5 + 35 * d ^ 4 - 36 * d ^ 3 -
        21 * d ^ 2 - 18 * d - 1) * u ^ 4 * v ^ 5 +
    d ^ 7 * (d - 1) ^ 5 *
      (d ^ 5 - 5 * d ^ 4 - 3 * d ^ 3 + 27 * d ^ 2 +
        30 * d + 5) * u ^ 3 * v ^ 6 +
    3 * d ^ 9 * (d - 1) ^ 6 *
      (d ^ 3 - 2 * d ^ 2 - 8 * d - 3) * u ^ 2 * v ^ 7 -
    d ^ 11 * (d - 1) ^ 7 * (d ^ 2 - 7 * d - 7) * u * v ^ 8 -
    2 * d ^ 13 * (d - 1) ^ 8 * v ^ 9

































 def OrderSevenDoublingCoordinates (d x y : ℚ) : Prop :=
  let W := (MazurTorsion.Kubert.orderSevenFamily d).toAffine
  let Wq := (MazurTorsion.Kubert.orderSevenQuotient d).toAffine
  let m := W.slope x x y y
  let x₂ := W.addX x x m
  let y₂ := W.addY x x y m
  let X := MazurTorsion.Kubert.orderSevenVeluX d x
  let Y := MazurTorsion.Kubert.orderSevenVeluY d x y
  let M := Wq.slope X X Y Y
  let X₂ := Wq.addX X X M
  let Y₂ := Wq.addY X X Y M
  MazurTorsion.Kubert.orderSevenVeluX d x₂ = X₂ ∧
    2 * MazurTorsion.Kubert.orderSevenVeluY d x₂ y₂ +
        Wq.a₁ * MazurTorsion.Kubert.orderSevenVeluX d x₂ + Wq.a₃ =
      2 * Y₂ + Wq.a₁ * X₂ + Wq.a₃





















end MazurTorsion.Kubert

end

#print axioms MazurTorsion.Doubling.completedYNumerator
#print axioms MazurTorsion.Doubling.completedYNumeratorHomogeneous
#print axioms MazurTorsion.Doubling.xNumerator
#print axioms MazurTorsion.Doubling.xNumeratorHomogeneous
#print axioms MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseKernel
#print axioms MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluX
#print axioms MazurTorsion.Kubert.OrderSevenDoublingDerivative.completedCubicPolynomial
#print axioms MazurTorsion.Kubert.OrderSevenDoublingDerivative.composedVeluX
#print axioms MazurTorsion.Kubert.OrderSevenDoublingDerivative.doubleXPolynomial
#print axioms MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelPolynomial
#print axioms MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceCompletedCubic
#print axioms MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceDoubleX
#print axioms MazurTorsion.Kubert.OrderSevenDoublingDerivative.targetDoubleX
#print axioms MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXPolynomial
#print axioms MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₀
#print axioms MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₁
#print axioms MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₂
#print axioms MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₃
#print axioms MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₄
#print axioms MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₅
#print axioms MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₆
#print axioms MazurTorsion.Kubert.orderSevenVeluDifferentialNumeratorHomogeneous
#print axioms MazurTorsion.Kubert.orderSevenVeluXNumeratorHomogeneous
#print axioms MazurTorsion.Kubert.OrderSevenDoublingCoordinates
#print axioms MazurTorsion.Kubert.orderSevenVeluA0
#print axioms MazurTorsion.Kubert.orderSevenVeluA1
#print axioms MazurTorsion.Kubert.orderSevenVeluA2
#print axioms MazurTorsion.Kubert.orderSevenVeluA3
#print axioms MazurTorsion.Kubert.orderSevenVeluA4
#print axioms MazurTorsion.Kubert.orderSevenVeluA5
#print axioms MazurTorsion.Kubert.orderSevenVeluA6


