-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.nonempty_pullback_iso_of_bijective_app_of_le_opensRange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1c486e34-4ac5-5915-9720-02ee6cb7fb30

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_of_bijective_app_of_le_opensRange

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace AlgebraicGeometry.Scheme.Modules

theorem solution
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (M : Y.Modules) (L : X.Modules)
    (π : L ⟶ (Scheme.Modules.pushforward f).obj M)
    (hπ : ∀ U : X.Opens, U ≤ f.opensRange → Function.Bijective (π.app U)) :
    Nonempty ((Scheme.Modules.pullback f).obj L ≅ M) := by
  have happ : ∀ U : Y.Opens, ((restrictFunctor f).map π).app U = π.app (f ''ᵁ U) := fun U => rfl
  haveI : IsIso ((restrictFunctor f).map π) := by
    rw [Hom.isIso_iff_isIso_app]
    intro U
    rw [happ, ConcreteCategory.isIso_iff_bijective]
    exact hπ _ (f.image_le_opensRange U)
  exact ⟨((restrictFunctorIsoPullback f).app L).symm ≪≫ asIso ((restrictFunctor f).map π) ≪≫
    (restrictFunctorAdjCounitIso f).app M⟩

end S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_of_bijective_app_of_le_opensRange
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_of_bijective_app_of_le_opensRange (solution)
