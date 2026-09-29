-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsFrameOn.isUnit_of_isFrameOn_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/7aaba7c9-3798-5bc1-b7d2-e942ec6b6ef6

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_isUnit_of_isFrameOn_smul

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization"

theorem solution
    {X : Scheme.{u}} {M : X.Modules} {U V W : X.Opens} (s : Γ(M, U))
    (hs : AlgebraicGeometry.Scheme.Modules.IsFrameOn s V) (hWU : W ≤ U) (hWV : W ≤ V) (g : Γ(X, W))
    (hg : AlgebraicGeometry.Scheme.Modules.IsFrameOn (g • M.presheaf.map (homOfLE hWU).op s) W) :
    IsUnit g := by
  have hb := hg (le_refl W) (le_refl W)
  have hid : ∀ t : Γ(M, W), M.presheaf.map (homOfLE (le_refl W)).op t = t := fun t => by
    rw [show (homOfLE (le_refl W)).op = 𝟙 (Opposite.op W) from rfl, CategoryTheory.Functor.map_id]
    rfl
  obtain ⟨g', hg'⟩ := hb.2 (M.presheaf.map (homOfLE hWU).op s)
  dsimp only at hg'
  rw [hid, smul_smul] at hg'
  have h1 : (g' * g) • M.presheaf.map (homOfLE hWU).op s =
      (1 : Γ(X, W)) • M.presheaf.map (homOfLE hWU).op s := by
    rw [hg', one_smul]
  have h2 : g' * g = 1 := (hs hWU hWV).1 h1
  exact isUnit_iff_exists_inv'.2 ⟨g', h2⟩

end S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_isUnit_of_isFrameOn_smul
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_isUnit_of_isFrameOn_smul (solution)
