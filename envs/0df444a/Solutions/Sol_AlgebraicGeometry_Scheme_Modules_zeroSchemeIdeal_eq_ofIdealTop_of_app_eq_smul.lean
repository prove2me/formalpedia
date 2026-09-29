-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.zeroSchemeIdeal_eq_ofIdealTop_of_app_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/2d4ea592-7f26-5ee1-9af6-a5dd8948952f

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_eq_ofIdealTop_of_app_eq_smul
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite"

theorem solution
    {X : Scheme.{u}} (t : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) (r : Γ(X, ⊤))
    (ht : t.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = r • Scheme.Modules.toUnitSection ⊤ 1) :
    Scheme.Modules.zeroSchemeIdeal t = Scheme.IdealSheafData.ofIdealTop (Ideal.span {r}) := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span, Set.image_singleton]
  have hΩ : Scheme.Modules.IsFrameOn (Scheme.Modules.toUnitSection (⊤ : X.Opens) (1 : Γ(X, ⊤))) ⊤ :=
    Scheme.Modules.isFrameOn_unitSection (U := ⊤) ⊤
  exact AlgebraicGeometry.Scheme.Modules.IsInvertible.ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul (Scheme.Modules.isInvertible_unit X) _ hΩ t r ht U le_top

end S_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_eq_ofIdealTop_of_app_eq_smul
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_eq_ofIdealTop_of_app_eq_smul (solution)
