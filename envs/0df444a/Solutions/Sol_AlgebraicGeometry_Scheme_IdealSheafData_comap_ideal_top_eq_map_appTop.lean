-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_top_eq_map_appTop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:56.207096+00:00
-- url     : https://prove2.me/submissions/8dcccd93-1c8a-4a8c-a0f3-709f9cbdcd9e

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
section
universe u
open CategoryTheory AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}}
private theorem appLE_top_eq_appTop (f : X ⟶ Y) (e0 : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens)) :
    f.appLE (⊤ : Y.Opens) (⊤ : X.Opens) e0 = f.appTop := by
  have h1 : X.presheaf.map (homOfLE e0).op = 𝟙 Γ(X, ⊤) := X.presheaf.map_id (op (⊤ : X.Opens))
  calc f.appLE (⊤ : Y.Opens) (⊤ : X.Opens) e0
      = f.app (⊤ : Y.Opens) ≫ X.presheaf.map (homOfLE e0).op := rfl
    _ = f.app (⊤ : Y.Opens) ≫ 𝟙 Γ(X, ⊤) := by rw [h1]
    _ = f.appTop := Category.comp_id _
end AlgebraicGeometry.Scheme.IdealSheafData
namespace FunctorialResolution.Blowup
end FunctorialResolution.Blowup
namespace AlgebraicGeometry.Scheme.IdealSheafData
end AlgebraicGeometry.Scheme.IdealSheafData
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}}
namespace AlgebraicGeometry.Scheme.IdealSheafData
theorem _root_.solution [IsAffine X] [IsAffine Y]
    (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom := by
  have e0 : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens) := by simp
  rw [comap_ideal_eq_map_appLE I f ⟨⊤, isAffineOpen_top Y⟩ ⟨⊤, isAffineOpen_top X⟩ e0]
  exact congrArg
    (fun φ => Ideal.map (CommRingCat.Hom.hom φ) (I.ideal ⟨⊤, isAffineOpen_top Y⟩))
    (appLE_top_eq_appTop f e0)
end AlgebraicGeometry.Scheme.IdealSheafData
