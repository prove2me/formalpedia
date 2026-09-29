-- Prove2me | solution 1 for AlgebraicGeometry.IsClosedImmersion.app_injective_and_exists_of_app_pullback_eq_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/f12645be-814a-5d2b-9c28-dc11f49b23f0

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_app_injective_and_exists_of_forall_isAffineOpen
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_app_injective_and_exists_of_app_pullback_eq_of_isAffineOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IsClosedImmersion_app_injective_and_exists_of_app_pullback_eq_of_isReduced

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {X Y₁ Y₂ : Scheme.{u}} [IsReduced X] (i₁ : Y₁ ⟶ X) (i₂ : Y₂ ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (U : X.Opens) :
    Function.Injective (fun f : Γ(X, U) => ((i₁.app U) f, (i₂.app U) f)) ∧
      ∀ (g₁ : Γ(Y₁, i₁ ⁻¹ᵁ U)) (g₂ : Γ(Y₂, i₂ ⁻¹ᵁ U)),
        (pullback i₁ i₂).presheaf.map
            (eqToHom (show (pullback.snd i₁ i₂) ⁻¹ᵁ (i₂ ⁻¹ᵁ U) = (pullback.fst i₁ i₂) ⁻¹ᵁ (i₁ ⁻¹ᵁ U) by
              rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition])).op
          ((pullback.fst i₁ i₂).app (i₁ ⁻¹ᵁ U) g₁) =
          (pullback.snd i₁ i₂).app (i₂ ⁻¹ᵁ U) g₂ →
        ∃ f : Γ(X, U), (i₁.app U) f = g₁ ∧ (i₂.app U) f = g₂ := by
  exact AlgebraicGeometry.Scheme.Hom.app_injective_and_exists_of_forall_isAffineOpen i₁ i₂ U
    (fun V hV _ => AlgebraicGeometry.IsClosedImmersion.app_injective_and_exists_of_app_pullback_eq_of_isAffineOpen
      i₁ i₂ hcover V hV)

end S_AlgebraicGeometry_IsClosedImmersion_app_injective_and_exists_of_app_pullback_eq_of_isReduced
end P2MW
export P2MW.S_AlgebraicGeometry_IsClosedImmersion_app_injective_and_exists_of_app_pullback_eq_of_isReduced (solution)
