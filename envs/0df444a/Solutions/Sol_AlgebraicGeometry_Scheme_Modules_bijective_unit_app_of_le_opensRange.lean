-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.bijective_unit_app_of_le_opensRange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/b5bfa23a-3ee6-50a0-803c-5bd46af34b5e

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange

universe u

open CategoryTheory AlgebraicGeometry Opposite AlgebraicGeometry.Scheme.Modules

theorem solution
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] (N : X.Modules)
    (V : X.Opens) (hV : V ≤ j.opensRange) :
    Function.Bijective (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N).app V) := by
  have hfac := Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction j) (pullbackPushforwardAdjunction j) N
  have hfac' := congrArg (fun t => Hom.app t V) hfac.symm

  have heq : j ''ᵁ j ⁻¹ᵁ V = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hV]
  have h2 : (homOfLE (j.image_preimage_le V)).op = eqToHom (congrArg op heq.symm) := Subsingleton.elim _ _
  have hiso1 : IsIso (N.presheaf.map (homOfLE (j.image_preimage_le V)).op) := by
    rw [h2]
    exact ⟨N.presheaf.map (eqToHom (congrArg op heq)), by simp [eqToHom_map], by simp [eqToHom_map]⟩
  have hiso2 : IsIso ((((restrictAdjunction j).leftAdjointUniq (pullbackPushforwardAdjunction j)).hom.app N).app
      (j ⁻¹ᵁ V)) := inferInstance
  have hiso := @IsIso.comp_isIso _ _ _ _ _ _ _ hiso1 hiso2
  rw [← ConcreteCategory.isIso_iff_bijective]

  revert hiso
  refine fun hiso => ?_
  rw [hfac']
  exact hiso

end S_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange (solution)
