-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.nonempty_pullback_fst_rigidify_iso_of_isInvertible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/6aec3fde-7319-52cb-8777-016dbbd94179

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_isLocalRing
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_fst_rigidify_iso_of_isInvertible
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

theorem solution
    {T P : Scheme.{u}} (σ : T ⟶ P) (q : P ⟶ T) (L : P.Modules) (hL : Scheme.Modules.IsInvertible L)
    (k : Type u) [Field k] (x : Spec (CommRingCat.of k) ⟶ T) :
    Nonempty ((Scheme.Modules.pullback (pullback.fst q x)).obj (Scheme.Modules.rigidify σ q L) ≅
      (Scheme.Modules.pullback (pullback.fst q x)).obj L) := by

  obtain ⟨e1⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_isLocalRing
    (((hL.pullback σ).dual.1).pullback x)
  rw [Scheme.Modules.rigidify_def]
  refine ⟨Scheme.Modules.pullbackTensorObjIso (pullback.fst q x) L _ ≪≫ whiskerLeftIso _ ?_ ≪≫ ρ_ _⟩

  exact (Scheme.Modules.pullbackComp (pullback.fst q x) q).app _ ≪≫
    (Scheme.Modules.pullbackCongr (pullback.condition (f := q) (g := x))).app _ ≪≫
    ((Scheme.Modules.pullbackComp (pullback.snd q x) x).app _).symm ≪≫
    (Scheme.Modules.pullback (pullback.snd q x)).mapIso e1 ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso (pullback.snd q x)

end S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_fst_rigidify_iso_of_isInvertible
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_fst_rigidify_iso_of_isInvertible (solution)
