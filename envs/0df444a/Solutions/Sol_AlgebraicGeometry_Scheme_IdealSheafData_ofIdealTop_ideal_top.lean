-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop_ideal_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:37.29259+00:00
-- url     : https://prove2.me/submissions/b3b2d475-21d2-4271-b260-59a675bb0728

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
theorem _root_.solution {Z : Scheme.{u}} [IsAffine Z] (J : Ideal Γ(Z, ⊤)) :
    (ofIdealTop J).ideal ⟨⊤, isAffineOpen_top Z⟩ = J := by
  have h := (equivOfIsAffine (X := Z)).apply_symm_apply J
  rw [equivOfIsAffine_symm_apply, equivOfIsAffine_apply] at h
  exact h
end AlgebraicGeometry.Scheme.IdealSheafData
