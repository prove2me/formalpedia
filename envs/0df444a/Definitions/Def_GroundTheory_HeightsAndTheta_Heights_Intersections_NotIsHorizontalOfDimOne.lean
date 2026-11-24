-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:05.477119+00:00
-- url     : https://prove2.me/theorems/bb3fd109-7000-4746-a7a7-9ecdc40b8de3
-- title:
--   Not Is Horizontal Of Dim One
-- statement:
--   Definitions and structural lemmas for Not Is Horizontal Of Dim One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsHorizontalOfDimOne.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogTwoXc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_MultAtHorizontalEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
section Cycles
open Classical in

def cycWeight (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) {n : ℕ}
    (L : Fin n → HermLine ι) (W : Ideal (MRing ι)) : ℝ :=
  if IsHorizontal W then I W n L else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W)
end Cycles
section NoHorizontal
end NoHorizontal
section Integral
end Integral
end
end GroundTheory.Heights₂.Heights.Inter


