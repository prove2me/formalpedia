-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.comap_iSup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:35.635231+00:00
-- url     : https://prove2.me/submissions/c32beeba-8871-45db-ae54-948bf6be3fad

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
theorem _root_.solution {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Sort*} (I : ι → Y.IdealSheafData) :
    (⨆ i, I i).comap f = ⨆ i, (I i).comap f :=
  (map_gc f).l_iSup
end AlgebraicGeometry.Scheme.IdealSheafData
