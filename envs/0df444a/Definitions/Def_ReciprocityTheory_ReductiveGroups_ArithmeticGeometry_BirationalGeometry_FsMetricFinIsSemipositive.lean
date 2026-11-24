-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_FsMetricFinIsSemipositive
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_FsMetricFinIsSemipositive
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:10.742799+00:00
-- url     : https://prove2.me/theorems/498002e6-7486-4621-b29a-b39c449ba371
-- title:
--   Fs Metric Fin Is Semipositive
-- statement:
--   Definitions and structural lemmas for Fs Metric Fin Is Semipositive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/FsMetricFinIsSemipositive.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo
variable {ι : Type*} [Fintype ι]
def fsLp (ι : Type*) [Fintype ι] : (ι → ℂ) →L[ℝ] EuclideanSpace ℂ ι :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => ℂ)).symm :
    (ι → ℂ) →L[ℂ] EuclideanSpace ℂ ι).restrictScalars ℝ
def fsGrad (y : ι → ℂ) : (ι → ℂ) →L[ℝ] ℝ :=
  (‖fsLp ι y‖ ^ 2)⁻¹ • (innerSL ℝ (fsLp ι y)).comp (fsLp ι)
end ReciprocityTheory.ChartRestriction.G.Geo


