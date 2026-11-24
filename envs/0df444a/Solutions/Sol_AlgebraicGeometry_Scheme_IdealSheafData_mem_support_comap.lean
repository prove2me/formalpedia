-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:01.949573+00:00
-- url     : https://prove2.me/submissions/834a0033-f8fc-45f2-8e7e-4faa5d7d3459

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
theorem _root_.solution {f : X ⟶ Y} {I : Y.IdealSheafData} {x : X} :
    x ∈ (I.comap f).support ↔ f.base x ∈ I.support := by
  constructor
  · intro hx
    rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap] at hx
    exact hx
  · intro hx
    rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap]
    exact hx
end AlgebraicGeometry.Scheme.IdealSheafData
