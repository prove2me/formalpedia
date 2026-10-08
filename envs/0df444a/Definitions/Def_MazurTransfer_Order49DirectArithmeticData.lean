-- Prove2me | Definitions.Def_MazurTransfer_Order49DirectArithmeticData
-- name    : MazurTransfer_Order49DirectArithmeticData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T02:03:15.462165+00:00
-- url     : https://prove2.me/theorems/a0f375bf-7fb5-4f30-ae05-23267b6c38f3
-- title:
--   Exact seven-isogeny arithmetic formulas
-- statement:
--   Exact original polynomial formulas for the seven-isogeny doubling identity and quotient division-polynomial factorization. This data package asserts neither identity and changes no coefficient or final every-curve statement.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; Apache-2.0 headers and attribution retained. Eleven exact pure definitions selected by original kernel type dependencies and complete original Lean AST source ranges. Every exported value is compared against the original using standard axioms. Existing exact published selection and cofactor data are reused. Named downstream consumers: original homogeneous doubling identity, original quotient-prePsi-seven factorization, and the full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingCertificateData. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

noncomputable section

namespace Internal

-- In the coefficient declarations below, `X : ℚ[X]` is the parameter `D`.




























































































































































































































































































































































































































































































































































































































end Internal

















namespace Internal

/-- Internal datum. -/ noncomputable def dualKernelPolynomial (d : ℚ) : ℚ[X] :=
  C 7 * X ^ 3 +
    C (14 * d ^ 4 - 35 * d ^ 3 + 42 * d ^ 2 - 21 * d + 14) * X ^ 2 +
    C (7 * d ^ 8 - 7 * d ^ 7 - 98 * d ^ 6 + 224 * d ^ 5 - 203 * d ^ 4 +
      49 * d ^ 3 + 77 * d ^ 2 - 49 * d + 7) * X +
    C (d ^ 12 + 3 * d ^ 11 - 51 * d ^ 10 + 185 * d ^ 9 - 767 * d ^ 8 +
      2097 * d ^ 7 - 2835 * d ^ 6 + 1738 * d ^ 5 - 295 * d ^ 4 -
      116 * d ^ 3 + 55 * d ^ 2 - 15 * d + 1)



end Internal

























































namespace Internal






















































end Internal

end

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end
end


/- Source module: MazurTorsion.Kubert.OrderSevenIsogenyPolynomialData. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenIsogenyPolynomialData

/-- The polynomial form of the three source kernel abscissae. -/
noncomputable def kernelPolynomial (d : ℚ) : ℚ[X] :=
  X * (X - C (MazurTorsion.Kubert.orderSevenB d)) * (X - C (MazurTorsion.Kubert.orderSevenC d))

/-- The polynomial form of the cleared explicit Vélu abscissa numerator. -/
noncomputable def veluXPolynomial (d : ℚ) : ℚ[X] :=
  X ^ 7 - C (2 * d * (d - 1) * (d + 1)) * X ^ 6 +
    C (d * (d - 1) *
      (d ^ 5 + 2 * d ^ 4 - 3 * d ^ 3 + 5 * d ^ 2 - 7 * d + 1)) *
        X ^ 5 -
    C (d ^ 3 * (d - 1) ^ 2 *
      (6 * d ^ 4 - 9 * d ^ 3 + 12 * d ^ 2 - 13 * d - 1)) * X ^ 4 +
    C (d ^ 4 * (d - 1) ^ 3 *
      (d ^ 5 + d ^ 4 + 4 * d ^ 3 - 8 * d ^ 2 - 7 * d - 1)) * X ^ 3 -
    C (d ^ 6 * (d - 1) ^ 4 * (d + 1) *
      (3 * d ^ 2 - 5 * d - 3)) * X ^ 2 +
    C (d ^ 8 * (d - 1) ^ 5 * (d ^ 2 - 3 * d - 3)) * X +
    C (d ^ 10 * (d - 1) ^ 6)





end MazurTorsion.Kubert.OrderSevenIsogenyPolynomialData

end


/- Source module: MazurTorsion.Kubert.TateNormalForm. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



section
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- Tate normal form
`y² + (1-c)xy - by = x³ - bx²`, with marked point `(0,0)`. -/
def tateNormalCurve (b c : ℚ) : WeierstrassCurve ℚ :=
  ⟨1 - c, -b, -b, 0, 0⟩




































end MazurTorsion.Kubert

namespace MazurTorsion.ExceptionalTwoTen



end MazurTorsion.ExceptionalTwoTen

end
end


/- Source module: MazurTorsion.Kubert.OrderSevenIsogeny. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/




open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert





/-- The order-seven Tate family, with marked point `(0,0)`. -/
@[expose] def orderSevenFamily (d : ℚ) : WeierstrassCurve ℚ :=
  tateNormalCurve (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d)






























































































































end MazurTorsion.Kubert

end


/- Source module: MazurTorsion.Kubert.OrderSevenIsogenyDoublingCertificateData. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenDoublingCertificate

noncomputable def sourceCompletedCubicPolynomial (d : ℚ) : ℚ[X] :=
  C 4 * X ^ 3 + C (orderSevenFamily d).b₂ * X ^ 2 +
    C (2 * (orderSevenFamily d).b₄) * X + C (orderSevenFamily d).b₆

noncomputable def sourceDoubleXPolynomial (d : ℚ) : ℚ[X] :=
  X ^ 4 - C (orderSevenFamily d).b₄ * X ^ 2 -
    C (2 * (orderSevenFamily d).b₆) * X - C (orderSevenFamily d).b₈

/-- Compatibility alias for the shared source kernel polynomial. -/
noncomputable abbrev kernelPolynomial :=
  OrderSevenIsogenyPolynomialData.kernelPolynomial

/-- Compatibility alias for the shared cleared Vélu abscissa polynomial. -/
noncomputable abbrev veluXPolynomial :=
  OrderSevenIsogenyPolynomialData.veluXPolynomial

noncomputable def veluXHomogeneousPolynomial
    (d : ℚ) (u v : ℚ[X]) : ℚ[X] :=
  u ^ 7 - C (2 * d * (d - 1) * (d + 1)) * u ^ 6 * v +
    C (d * (d - 1) *
      (d ^ 5 + 2 * d ^ 4 - 3 * d ^ 3 + 5 * d ^ 2 - 7 * d + 1)) *
        u ^ 5 * v ^ 2 -
    C (d ^ 3 * (d - 1) ^ 2 *
      (6 * d ^ 4 - 9 * d ^ 3 + 12 * d ^ 2 - 13 * d - 1)) *
        u ^ 4 * v ^ 3 +
    C (d ^ 4 * (d - 1) ^ 3 *
      (d ^ 5 + d ^ 4 + 4 * d ^ 3 - 8 * d ^ 2 - 7 * d - 1)) *
        u ^ 3 * v ^ 4 -
    C (d ^ 6 * (d - 1) ^ 4 * (d + 1) *
      (3 * d ^ 2 - 5 * d - 3)) * u ^ 2 * v ^ 5 +
    C (d ^ 8 * (d - 1) ^ 5 * (d ^ 2 - 3 * d - 3)) * u * v ^ 6 +
    C (d ^ 10 * (d - 1) ^ 6) * v ^ 7

noncomputable def doubleXHomogeneousPolynomial
    (W : WeierstrassCurve ℚ) (u v : ℚ[X]) : ℚ[X] :=
  u ^ 4 - C W.b₄ * u ^ 2 * v ^ 2 - C (2 * W.b₆) * u * v ^ 3 -
    C W.b₈ * v ^ 4

namespace Internal







end Internal

end MazurTorsion.Kubert.OrderSevenDoublingCertificate

end

#print axioms MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.dualKernelPolynomial
#print axioms MazurTorsion.Kubert.OrderSevenDoublingCertificate.doubleXHomogeneousPolynomial
#print axioms MazurTorsion.Kubert.OrderSevenDoublingCertificate.kernelPolynomial
#print axioms MazurTorsion.Kubert.OrderSevenDoublingCertificate.sourceCompletedCubicPolynomial
#print axioms MazurTorsion.Kubert.OrderSevenDoublingCertificate.sourceDoubleXPolynomial
#print axioms MazurTorsion.Kubert.OrderSevenDoublingCertificate.veluXHomogeneousPolynomial
#print axioms MazurTorsion.Kubert.OrderSevenDoublingCertificate.veluXPolynomial
#print axioms MazurTorsion.Kubert.OrderSevenIsogenyPolynomialData.kernelPolynomial
#print axioms MazurTorsion.Kubert.OrderSevenIsogenyPolynomialData.veluXPolynomial
#print axioms MazurTorsion.Kubert.orderSevenFamily
#print axioms MazurTorsion.Kubert.tateNormalCurve


