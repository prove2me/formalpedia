-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_pullback_iso_of_forall_maximal_isIrreducible_image_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/51a1877c-9c04-5b24-b43f-4a92cd1dc6d6

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_zeroSchemeIdeal_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal_eq_of_forall_maximal_isIrreducible_image_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_pullback_iso_of_forall_maximal_isIrreducible_image_eq
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

theorem solution
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M) (hs : s ≠ 0)
    (σ : X ≅ X)
    (hσ : ∀ C : Set X,
      Maximal (fun C' : Set X => IsIrreducible C' ∧ C' ⊆ (Scheme.Modules.zeroSchemeIdeal s).support) C →
        σ.hom.base '' C = C) :
    Nonempty ((Scheme.Modules.pullback σ.hom).obj M ≅ M) := by
  have hM' : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback σ.hom).obj M) := hM.pullback σ.hom
  have hZ : Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection σ.hom s) = Scheme.Modules.zeroSchemeIdeal s := by
    rw [← hM.comap_zeroSchemeIdeal_monoidalV2 σ.hom s]
    exact AlgebraicGeometry.Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal_eq_of_forall_maximal_isIrreducible_image_eq hX hM s hs σ hσ
  obtain ⟨e⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_zeroSchemeIdeal_eq hM hM' s
    (Scheme.Modules.pullbackSection σ.hom s) hs hZ.symm
  exact ⟨e.symm⟩

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_pullback_iso_of_forall_maximal_isIrreducible_image_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_pullback_iso_of_forall_maximal_isIrreducible_image_eq (solution)
