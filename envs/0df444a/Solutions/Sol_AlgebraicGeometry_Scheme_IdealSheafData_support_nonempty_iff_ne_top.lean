-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.support_nonempty_iff_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:56.855104+00:00
-- url     : https://prove2.me/submissions/269859dd-3874-4dab-85ee-11be1452faa0

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_eq_top_iff_support_eq_empty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}}
namespace AlgebraicGeometry.Scheme.IdealSheafData
theorem _root_.solution {X : Scheme.{u}} (I : X.IdealSheafData) :
    (I.support : Set X).Nonempty ↔ I ≠ ⊤ := by
  rw [ne_eq, eq_top_iff_support_eq_empty, Set.nonempty_iff_ne_empty, ne_eq]
end AlgebraicGeometry.Scheme.IdealSheafData
