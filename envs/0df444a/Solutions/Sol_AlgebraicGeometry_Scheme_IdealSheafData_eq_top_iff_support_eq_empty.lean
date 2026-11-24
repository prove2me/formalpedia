-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.eq_top_iff_support_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:00.422408+00:00
-- url     : https://prove2.me/submissions/30ad36f6-10e0-48c1-8d27-2f502ae86ff0

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
theorem _root_.solution {X : Scheme.{u}} (I : X.IdealSheafData) :
    I = ⊤ ↔ (I.support : Set X) = ∅ := by
  rw [← support_eq_bot_iff, SetLike.ext'_iff]
  simp
end AlgebraicGeometry.Scheme.IdealSheafData
