-- Prove2me | Definitions.Def_MazurTransfer_Order49DifferentialCertificateFormulas
-- name    : MazurTransfer_Order49DifferentialCertificateFormulas
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T04:19:07.9213+00:00
-- url     : https://prove2.me/theorems/70f7fd50-ae52-4e4b-bf09-36f13ef2b076
-- title:
--   Exact original homogeneous directional derivative and vertical polynomial formulas
-- statement:
--   Exact original homogeneous directional derivatives and vertical polynomial formulas, with every exported value independently compared by kernel-checked reflexivity; no mathematical theorem is bundled as a definition
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; Apache-2.0 headers and attribution retained. 17 exact pure definitions selected by original kernel type dependencies and complete original Lean AST source ranges. Every exported value is compared against the original using standard axioms. Existing exact published selection and cofactor data are reused. Named downstream consumers: original coordinate doubling and derivative certificates, and the full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DoublingCoordinateFormulas


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











/-- Homogenization of `completedCubic` to degree three. -/
def completedCubicHomogeneous
    {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (u v : R) : R :=
  4 * u ^ 3 + W.b₂ * u ^ 2 * v + 2 * W.b₄ * u * v ^ 2 +
    W.b₆ * v ^ 3

/-- Directional derivative of `completedCubicHomogeneous` at `(u, v)`
in the direction `(du, dv)`. -/
def completedCubicHomogeneousDirectional
    (W : WeierstrassCurve ℚ) (u v du dv : ℚ) : ℚ :=
  (12 * u ^ 2 + 2 * W.b₂ * u * v + 2 * W.b₄ * v ^ 2) * du +
    (W.b₂ * u ^ 2 + 4 * W.b₄ * u * v + 3 * W.b₆ * v ^ 2) * dv

/-- Directional derivative of `xNumeratorHomogeneous` at `(u, v)`
in the direction `(du, dv)`. -/
def xNumeratorHomogeneousDirectional
    (W : WeierstrassCurve ℚ) (u v du dv : ℚ) : ℚ :=
  (4 * u ^ 3 - 2 * W.b₄ * u * v ^ 2 - 2 * W.b₆ * v ^ 3) * du +
    (-2 * W.b₄ * u ^ 2 * v - 6 * W.b₆ * u * v ^ 2 -
      4 * W.b₈ * v ^ 3) * dv















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

/-- A monic degree-seven binary form, written with its seven lower
coefficients. -/
def veluXHomogeneous
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ u v : ℚ) : ℚ :=
  u ^ 7 + a₆ * u ^ 6 * v + a₅ * u ^ 5 * v ^ 2 +
    a₄ * u ^ 4 * v ^ 3 + a₃ * u ^ 3 * v ^ 4 +
    a₂ * u ^ 2 * v ^ 5 + a₁ * u * v ^ 6 + a₀ * v ^ 7

/-- Directional derivative of `veluXHomogeneous`. -/
def veluXHomogeneousDirectional
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ u v du dv : ℚ) : ℚ :=
  (7 * u ^ 6 + 6 * a₆ * u ^ 5 * v + 5 * a₅ * u ^ 4 * v ^ 2 +
      4 * a₄ * u ^ 3 * v ^ 3 + 3 * a₃ * u ^ 2 * v ^ 4 +
      2 * a₂ * u * v ^ 5 + a₁ * v ^ 6) * du +
    (a₆ * u ^ 6 + 2 * a₅ * u ^ 5 * v + 3 * a₄ * u ^ 4 * v ^ 2 +
      4 * a₃ * u ^ 3 * v ^ 3 + 5 * a₂ * u ^ 2 * v ^ 4 +
      6 * a₁ * u * v ^ 5 + 7 * a₀ * v ^ 6) * dv

/-- Homogenization of the cubic denominator `X (X - b) (X - c)`. -/
def kernelHomogeneous (b c u v : ℚ) : ℚ :=
  u * (u - b * v) * (u - c * v)

/-- Directional derivative of `kernelHomogeneous`. -/
def kernelHomogeneousDirectional (b c u v du dv : ℚ) : ℚ :=
  ((u - b * v) * (u - c * v) + u * (u - c * v) +
      u * (u - b * v)) * du +
    (-b * u * (u - c * v) - c * u * (u - b * v)) * dv

/-- Homogenization to degree nine of `F'K - 2FK'`, for the degree-seven
form `F` and cubic kernel `K`. -/
def veluDifferentialHomogeneous
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c u v : ℚ) : ℚ :=
  (7 * u ^ 6 + 6 * a₆ * u ^ 5 * v + 5 * a₅ * u ^ 4 * v ^ 2 +
      4 * a₄ * u ^ 3 * v ^ 3 + 3 * a₃ * u ^ 2 * v ^ 4 +
      2 * a₂ * u * v ^ 5 + a₁ * v ^ 6) *
      kernelHomogeneous b c u v -
    2 * veluXHomogeneous a₆ a₅ a₄ a₃ a₂ a₁ a₀ u v *
      ((u - b * v) * (u - c * v) + u * (u - c * v) +
        u * (u - b * v))









noncomputable def doubleCompletedYPolynomial
    (W : WeierstrassCurve ℚ) (u v : ℚ[X]) : ℚ[X] :=
  C 2 * u ^ 6 + C W.b₂ * u ^ 5 * v + C (5 * W.b₄) * u ^ 4 * v ^ 2 +
    C (10 * W.b₆) * u ^ 3 * v ^ 3 + C (10 * W.b₈) * u ^ 2 * v ^ 4 +
    C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * u * v ^ 5 +
    C (W.b₄ * W.b₈ - W.b₆ ^ 2) * v ^ 6





noncomputable def veluDifferentialPolynomial
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c : ℚ)
    (u v : ℚ[X]) : ℚ[X] :=
  (C 7 * u ^ 6 + C (6 * a₆) * u ^ 5 * v + C (5 * a₅) * u ^ 4 * v ^ 2 +
      C (4 * a₄) * u ^ 3 * v ^ 3 + C (3 * a₃) * u ^ 2 * v ^ 4 +
      C (2 * a₂) * u * v ^ 5 + C a₁ * v ^ 6) *
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelPolynomial b c u v -
    C 2 * MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXPolynomial a₆ a₅ a₄ a₃ a₂ a₁ a₀ u v *
      ((u - C b * v) * (u - C c * v) +
        u * (u - C c * v) + u * (u - C b * v))

































noncomputable def sourceDoubleCompletedY
    (W : WeierstrassCurve ℚ) : ℚ[X] :=
  doubleCompletedYPolynomial W X 1





noncomputable def baseVeluDifferential
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c : ℚ) : ℚ[X] :=
  veluDifferentialPolynomial a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c X 1



noncomputable def composedKernel
    (b c : ℚ) (W : WeierstrassCurve ℚ) : ℚ[X] :=
  MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelPolynomial b c (MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceDoubleX W) (MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceCompletedCubic W)

noncomputable def composedVeluDifferential
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c : ℚ)
    (W : WeierstrassCurve ℚ) : ℚ[X] :=
  veluDifferentialPolynomial a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c
    (MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceDoubleX W) (MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceCompletedCubic W)



noncomputable def targetCompletedCubic
    (W' : WeierstrassCurve ℚ)
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c : ℚ) : ℚ[X] :=
  MazurTorsion.Kubert.OrderSevenDoublingDerivative.completedCubicPolynomial W'
    (MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluX a₆ a₅ a₄ a₃ a₂ a₁ a₀) (MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseKernel b c ^ 2)

noncomputable def targetDoubleCompletedY
    (W' : WeierstrassCurve ℚ)
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c : ℚ) : ℚ[X] :=
  doubleCompletedYPolynomial W'
    (MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluX a₆ a₅ a₄ a₃ a₂ a₁ a₀) (MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseKernel b c ^ 2)



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















/-- The polynomial whose evaluation is the cleared Vélu differential
numerator. -/
noncomputable def differentialPolynomial (d : ℚ) : ℚ[X] :=
  X ^ 9 - C (3 * d * (d - 1) * (d + 1)) * X ^ 8 -
    C (d * (d - 1) *
      (d ^ 5 - 2 * d ^ 4 - 12 * d ^ 3 + 14 * d ^ 2 - 3 * d + 1)) * X ^ 7 -
    C (d ^ 2 * (d - 1) ^ 2 *
      (d ^ 6 - 9 * d ^ 5 + 25 * d ^ 4 - 22 * d ^ 3 +
        16 * d ^ 2 - 4 * d + 1)) * X ^ 6 +
    C (3 * d ^ 4 * (d - 1) ^ 3 *
      (d ^ 4 - 7 * d ^ 3 + 13 * d ^ 2 + 2)) * X ^ 5 +
    C (d ^ 5 * (d - 1) ^ 4 *
      (d ^ 6 - 10 * d ^ 5 + 35 * d ^ 4 - 36 * d ^ 3 -
        21 * d ^ 2 - 18 * d - 1)) * X ^ 4 +
    C (d ^ 7 * (d - 1) ^ 5 *
      (d ^ 5 - 5 * d ^ 4 - 3 * d ^ 3 + 27 * d ^ 2 + 30 * d + 5)) * X ^ 3 +
    C (3 * d ^ 9 * (d - 1) ^ 6 *
      (d ^ 3 - 2 * d ^ 2 - 8 * d - 3)) * X ^ 2 -
    C (d ^ 11 * (d - 1) ^ 7 * (d ^ 2 - 7 * d - 7)) * X -
    C (2 * d ^ 13 * (d - 1) ^ 8)









end MazurTorsion.Kubert.OrderSevenDoublingSpecialization

end

#print axioms MazurTorsion.Doubling.completedCubicHomogeneous
#print axioms MazurTorsion.Doubling.completedCubicHomogeneousDirectional
#print axioms MazurTorsion.Doubling.xNumeratorHomogeneousDirectional
#print axioms MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluDifferential
#print axioms MazurTorsion.Kubert.OrderSevenDoublingDerivative.composedKernel
#print axioms MazurTorsion.Kubert.OrderSevenDoublingDerivative.composedVeluDifferential
#print axioms MazurTorsion.Kubert.OrderSevenDoublingDerivative.doubleCompletedYPolynomial
#print axioms MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneous
#print axioms MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneousDirectional
#print axioms MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceDoubleCompletedY
#print axioms MazurTorsion.Kubert.OrderSevenDoublingDerivative.targetCompletedCubic
#print axioms MazurTorsion.Kubert.OrderSevenDoublingDerivative.targetDoubleCompletedY
#print axioms MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluDifferentialHomogeneous
#print axioms MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluDifferentialPolynomial
#print axioms MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneous
#print axioms MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneousDirectional
#print axioms MazurTorsion.Kubert.OrderSevenDoublingSpecialization.differentialPolynomial


