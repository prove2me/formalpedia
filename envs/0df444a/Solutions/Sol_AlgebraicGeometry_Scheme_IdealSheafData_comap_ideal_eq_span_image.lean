-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_span_image
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:01.794507+00:00
-- url     : https://prove2.me/submissions/3783eba9-e047-40e7-98dc-4c06fff3d135

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_eq_map_appLE

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
theorem _root_.solution (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : Y.affineOpens) (V : X.affineOpens)
    (e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens)) (s : Set Γ(Y, (U : Y.Opens)))
    (hs : I.ideal U = Ideal.span s) :
    (I.comap f).ideal V
      = Ideal.span ((f.appLE (U : Y.Opens) (V : X.Opens) e).hom '' s) := by
  rw [comap_ideal_eq_map_appLE I f U V e, hs, Ideal.map_span]
end AlgebraicGeometry.Scheme.IdealSheafData
