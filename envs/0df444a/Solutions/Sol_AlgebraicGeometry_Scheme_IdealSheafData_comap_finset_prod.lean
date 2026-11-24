-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.comap_finset_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:06.173675+00:00
-- url     : https://prove2.me/submissions/e0b84f20-28cf-40b9-af67-a86ad36d0174

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
theorem _root_.solution {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*} (s : Finset ι)
    (F : ι → Y.IdealSheafData) :
    (∏ i ∈ s, F i).comap f = ∏ i ∈ s, (F i).comap f := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty]
    exact comap_top f
  · intro a t ha ih
    simp only [Finset.prod_insert ha, comap_mul, ih]
end AlgebraicGeometry.Scheme.IdealSheafData
