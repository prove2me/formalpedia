-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.isInvertible_glueOfCocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/591f28ed-0b96-5689-936b-ddf277d225fe

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_of_forall_exists_isFrameOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isInvertible_glueOfCocycle

set_option autoImplicit false

p2m_open "CategoryTheory Opposite TopologicalSpace CategoryTheory.MonoidalCategory AlgebraicGeometry"

universe u

theorem solution
    {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (hU : ⨆ i, U i = ⊤) (c : Scheme.Modules.UnitCocycle U) :
    Scheme.Modules.IsInvertible (Scheme.Modules.glueOfCocycle c) := by
  apply AlgebraicGeometry.Scheme.Modules.isInvertible_of_forall_exists_isFrameOn
  intro x
  have hx : x ∈ (⨆ i, U i) := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact ⟨U i, Scheme.Modules.glueFrame c i, hi, Scheme.Modules.isFrameOn_glueFrame c i⟩

end S_AlgebraicGeometry_Scheme_Modules_isInvertible_glueOfCocycle
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_isInvertible_glueOfCocycle (solution)
