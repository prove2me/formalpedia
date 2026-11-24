-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.ne_top_of_mem_support
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:29.567083+00:00
-- url     : https://prove2.me/submissions/926c7751-4a02-45b9-baf9-d662470b8849

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData

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
theorem _root_.solution (J : Y.IdealSheafData) (x : ↥Y) (hx : x ∈ J.support) : J ≠ ⊤ := by
  intro hc
  have hb : J.support = ⊥ :=
    (AlgebraicGeometry.Scheme.IdealSheafData.support_eq_bot_iff J).mpr hc
  have hx2 : x ∈ (J.support : Set ↥Y) := hx
  rw [hb] at hx2
  simp at hx2
end AlgebraicGeometry.Scheme.IdealSheafData
