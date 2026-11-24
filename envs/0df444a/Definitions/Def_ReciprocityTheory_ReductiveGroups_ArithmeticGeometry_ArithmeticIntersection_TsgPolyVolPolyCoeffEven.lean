-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_TsgPolyVolPolyCoeffEven
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_TsgPolyVolPolyCoeffEven
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:01.021996+00:00
-- url     : https://prove2.me/theorems/3565f358-b72f-4175-8891-3819d72e7920
-- title:
--   Tsg Poly Vol Poly Coeff Even
-- statement:
--   Definitions and structural lemmas for Tsg Poly Vol Poly Coeff Even, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/TsgPolyVolPolyCoeffEven.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_APrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AI
open Polynomial
noncomputable def FibreSquare.evenPoly {D : ℕ} (S : FibreSquare D) : ℝ[X] :=
  ∑ j ∈ Finset.range (D + 1 + 1),
    C (((D + 1).choose j : ℝ) * ((-1) ^ j + 1) * S.I (mix j S.ξ S.A)) * X ^ j
end ReciprocityTheory.ChartRestriction.G.AI


