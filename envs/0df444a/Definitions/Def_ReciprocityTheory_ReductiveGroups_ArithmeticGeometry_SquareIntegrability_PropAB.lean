-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:27:41.930083+00:00
-- url     : https://prove2.me/theorems/8f2a1f2c-1d56-43d9-8fd6-c2410f691aae
-- title:
--   Prop AB
-- statement:
--   Definitions and structural lemmas for Prop AB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropABSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaThContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_ExpNEllMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
def paT : EuclideanSpace ℂ (Fin (Fintype.card ι)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fintype.equivFin ι).symm
def paTR : EuclideanSpace ℂ (Fin (Fintype.card ι)) ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι :=
  { toLinearEquiv := (paT (ι := ι)).toLinearEquiv.restrictScalars ℝ
    norm_map' := (paT (ι := ι)).norm_map }
end
end ReciprocityTheory.ChartRestriction.G.I2


