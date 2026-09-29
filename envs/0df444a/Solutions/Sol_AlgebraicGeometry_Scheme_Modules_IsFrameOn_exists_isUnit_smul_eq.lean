-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsFrameOn.exists_isUnit_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/4d4100b2-2301-59ae-badb-ac75b8ff1a08

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isUnit_smul_eq

set_option autoImplicit false

universe u v

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

theorem solution
    {X : Scheme.{u}} {M : X.Modules} {U : X.Opens} {s s' : Γ(M, U)} {V : X.Opens}
    (hs : Scheme.Modules.IsFrameOn s V) (hs' : Scheme.Modules.IsFrameOn s' V)
    {W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V) :
    ∃ u : Γ(X, W), IsUnit u ∧
      u • M.presheaf.map (homOfLE hWU).op s = M.presheaf.map (homOfLE hWU).op s' := by
  obtain ⟨u, hu⟩ := (hs hWU hWV).2 (M.presheaf.map (homOfLE hWU).op s')
  obtain ⟨w, hw⟩ := (hs' hWU hWV).2 (M.presheaf.map (homOfLE hWU).op s)
  refine ⟨u, ?_, hu⟩
  have h1 : (w * u) • M.presheaf.map (homOfLE hWU).op s =
      (1 : Γ(X, W)) • M.presheaf.map (homOfLE hWU).op s := by
    rw [mul_smul, one_smul]
    simp only at hu hw
    rw [hu, hw]
  have hwu : w * u = 1 := (hs hWU hWV).1 h1
  exact ⟨⟨u, w, (mul_comm u w).trans hwu, hwu⟩, rfl⟩

end S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isUnit_smul_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isUnit_smul_eq (solution)
