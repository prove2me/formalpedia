-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelB
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:39.087592+00:00
-- url     : https://prove2.me/theorems/6f607fc2-ee83-45d9-aebc-da93d41a47cb
-- title:
--   Col Abel B
-- statement:
--   Definitions and structural lemmas for Col Abel B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
section
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
def cabPoly (η : EuclideanSpace ℂ ι) (c : ℕ) : MvPolynomial ι ℂ :=
  (∑ i, MvPolynomial.C ((starRingEnd ℂ) (η i)) * MvPolynomial.X i) ^ c
end
end
section
open MeasureTheory
noncomputable section
variable {ι : Type} [Fintype ι]
end
end
section
noncomputable section
end
end
section
noncomputable section
end
end
end ReciprocityTheory.ChartRestriction.G.I2


