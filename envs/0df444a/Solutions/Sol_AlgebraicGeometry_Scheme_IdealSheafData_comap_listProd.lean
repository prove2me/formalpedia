-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.comap_listProd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:01.915817+00:00
-- url     : https://prove2.me/submissions/751e85b6-793c-410a-ba81-cebcda1153d9

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Theorems.Thm_P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul_ffd4b47c5064b9ee

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
theorem _root_.solution {X Y : Scheme.{u}} (f : X ⟶ Y) (L : List Y.IdealSheafData) :
    L.prod.comap f = (L.map (·.comap f)).prod := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    exact comap_top f
  | cons D E ih => simp only [List.map_cons, List.prod_cons, comap_mul, ih]
end AlgebraicGeometry.Scheme.IdealSheafData
