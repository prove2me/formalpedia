-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:05.67583+00:00
-- url     : https://prove2.me/theorems/6557272f-dc77-4622-8829-8d81828b639d
-- title:
--   Chart Mass Affine
-- statement:
--   Definitions and structural lemmas for Chart Mass Affine, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
noncomputable section
namespace ChartMongeAmpereAffineInvariance
variable {D : ℕ}
def sesq (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (u v : Fin D → ℂ) : ℂ :=
  ((H u v + H (Complex.I • u) (Complex.I • v) : ℝ) +
    Complex.I * ((H u (Complex.I • v) - H (Complex.I • u) v : ℝ))) / 4
section Sesq
variable (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)
end Sesq
def realCLE (P : Matrix (Fin D) (Fin D) ℂ) (hP : P.det ≠ 0) : (Fin D → ℂ) ≃L[ℝ] (Fin D → ℂ) :=
  letI := P.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hP)
  ((P.toLinearEquiv' this).restrictScalars ℝ).toContinuousLinearEquiv
end ChartMongeAmpereAffineInvariance
end
end GroundTheory.Heights₂.Heights


