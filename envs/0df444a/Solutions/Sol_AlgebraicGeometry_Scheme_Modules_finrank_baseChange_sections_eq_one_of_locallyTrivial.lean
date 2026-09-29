-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.finrank_baseChange_sections_eq_one_of_locallyTrivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/38994906-76cd-5d0b-a376-e6c21c74e235

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_finite_sections_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_rankAtStalk_sections_eq_one_of_locallyTrivial
import Theorems.Thm_Module_finrank_baseChange_eq_one_of_rankAtStalk_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_finrank_baseChange_sections_eq_one_of_locallyTrivial

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 16000000

noncomputable section

theorem solution
    {X : Scheme.{u}} (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : X.affineOpens) (K : Type u) [Field K] [Algebra Γ(X, U.1) K] :
    Module.finrank K (K ⊗[Γ(X, U.1)] Γ(M, U.1)) = 1 := by
  haveI := Scheme.Modules.projective_sections_of_locallyTrivial M htriv U
  haveI := Scheme.Modules.finite_sections_of_locallyTrivial M htriv U
  haveI : Module.Flat ↑Γ(X, U.1) ↑Γ(M, U.1) := inferInstance
  exact Module.finrank_baseChange_eq_one_of_rankAtStalk_eq_one
    (R := ↑Γ(X, U.1)) ↑Γ(M, U.1)
    (fun 𝔭 => Scheme.Modules.rankAtStalk_sections_eq_one_of_locallyTrivial M htriv U 𝔭) K

end

end S_AlgebraicGeometry_Scheme_Modules_finrank_baseChange_sections_eq_one_of_locallyTrivial
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_finrank_baseChange_sections_eq_one_of_locallyTrivial (solution)
