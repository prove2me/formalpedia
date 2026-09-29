-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor_pullback_dual_pullback_and_nonempty_pullback_iso_unit_monoidalV2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/b6f3db36-b521-553b-a365-b7a393ca17e3

import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_pullback_dual_pullback_and_nonempty_pullback_iso_unit_monoidalV2

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry"

theorem solution
    {T P : Scheme.{u}} {σ : T ⟶ P} {q : P ⟶ T} (hσq : σ ≫ q = 𝟙 T) {L : P.Modules}
    (hL : Scheme.Modules.IsInvertible L) :
    Scheme.Modules.IsInvertible
        (L ⊗ (Scheme.Modules.pullback q).obj (Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L))) ∧
      Nonempty ((Scheme.Modules.pullback σ).obj
          (L ⊗ (Scheme.Modules.pullback q).obj (Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L))) ≅
        𝟙_ T.Modules) := by

  have hσL : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback σ).obj L) :=
    Scheme.Modules.IsInvertible.pullback σ hL
  obtain ⟨hM, ⟨pairing⟩⟩ := Scheme.Modules.IsInvertible.dual_monoidalV2 hσL
  refine ⟨hL.tensor_monoidalV2 (Scheme.Modules.IsInvertible.pullback q hM), ⟨?_⟩⟩
  let M := Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L)

  let e : (Scheme.Modules.pullback σ).obj ((Scheme.Modules.pullback q).obj M) ≅ M :=
    (Scheme.Modules.pullbackComp σ q).app M ≪≫
      (Scheme.Modules.pullbackCongr hσq).app M ≪≫ (Scheme.Modules.pullbackId (X := T)).app M
  exact Scheme.Modules.pullbackTensorObjIso σ L _ ≪≫ (Iso.refl _ ⊗ᵢ e) ≪≫ pairing

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_pullback_dual_pullback_and_nonempty_pullback_iso_unit_monoidalV2
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_pullback_dual_pullback_and_nonempty_pullback_iso_unit_monoidalV2 (solution)
