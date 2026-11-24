-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.appLE_mem_comap_ideal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:51.995499+00:00
-- url     : https://prove2.me/submissions/6174b345-5c30-4a73-8012-19cbb16f993d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_map_appLE_le_comap_ideal

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
    (e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens)) {x : Γ(Y, (U : Y.Opens))}
    (hx : x ∈ I.ideal U) :
    (f.appLE (U : Y.Opens) (V : X.Opens) e).hom x ∈ (I.comap f).ideal V :=
  map_appLE_le_comap_ideal I f U V e (Ideal.mem_map_of_mem _ hx)
end AlgebraicGeometry.Scheme.IdealSheafData
