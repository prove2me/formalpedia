-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsFrameOn.dual_eq_of_ihomEval_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/800c3fe3-9204-5dfe-82ff-ec9dd98f3546

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_dual_eq_of_ihomEval_eq

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite"

lemma presheaf_map_map_aux {X : Scheme.{u}} (M : X.Modules) {A B C : X.Opens} (f : B ⟶ A) (g : C ⟶ B) (k : C ⟶ A)
    (x : Γ(M, A)) : M.presheaf.map g.op (M.presheaf.map f.op x) = M.presheaf.map k.op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Subsingleton.elim (g ≫ f) k]

theorem solution
    {X : Scheme.{u}} {P : X.Modules} {U V : X.Opens} {p : Γ(P, U)}
    (hp : Scheme.Modules.IsFrameOn p V) (hVU : V ≤ U) {q q' : Γ(Scheme.Modules.dual P, V)}
    (h : Scheme.Modules.ihomEval P (𝟙_ X.Modules) V (P.presheaf.map (homOfLE hVU).op p) q =
      Scheme.Modules.ihomEval P (𝟙_ X.Modules) V (P.presheaf.map (homOfLE hVU).op p) q') :
    q = q' := by
  apply Scheme.Modules.ihom_sections_ext
  intro W i m

  obtain ⟨c, hc⟩ := (hp (i.le.trans hVU) i.le).2 m
  change c • P.presheaf.map (homOfLE (i.le.trans hVU)).op p = m at hc
  have hres : P.presheaf.map (homOfLE (i.le.trans hVU)).op p = P.presheaf.map i.op (P.presheaf.map (homOfLE hVU).op p) :=
    (presheaf_map_map_aux P _ _ _ p).symm
  rw [← hc, hres, Scheme.Modules.ihomEval_smul_left, Scheme.Modules.ihomEval_smul_left,
    ← Scheme.Modules.map_ihomEval, ← Scheme.Modules.map_ihomEval, h]

end S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_dual_eq_of_ihomEval_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_dual_eq_of_ihomEval_eq (solution)
