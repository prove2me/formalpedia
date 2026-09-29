-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections.pullback_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/407d3b72-8ea3-590d-976a-55905211fb41

import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {R R' : Type u} [CommRing R] [CommRing R'] (φ : R →+* R')
    {X X' : Scheme.{u}} {f : X ⟶ Spec (.of R)} {f' : X' ⟶ Spec (.of R')} (g : X' ⟶ X)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    {M : X.Modules} (hM : Scheme.Modules.ClosedImmersionBySections M f) :
    Scheme.Modules.ClosedImmersionBySections ((Scheme.Modules.pullback g).obj M) f' := by
  letI : Algebra R R' := φ.toAlgebra
  obtain ⟨N, 𝔓, h𝔓⟩ := hM
  have sq : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := hg
  obtain ⟨𝔓', -, -, hsq⟩ :=
    AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback sq 𝔓
  exact ⟨N, 𝔓', MorphismProperty.of_isPullback hsq h𝔓⟩

end S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_of_isPullback (solution)
