-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isInvertible_rigidified_locIsoOnBase_of_section
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/16990b14-a838-5bdc-beef-431417ce9f77

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_pullback_dual_pullback_and_nonempty_pullback_iso_unit_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isInvertible_rigidified_locIsoOnBase_of_section

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Polarisation"

universe u

theorem solution
    {T : Type u} [CommRing T] {B : Scheme.{u}} (h : B ⟶ Spec (CommRingCat.of T))
    (e : Spec (CommRingCat.of T) ⟶ B) (he : e ≫ h = 𝟙 _)
    (M : B.Modules) (hM : Scheme.Modules.IsInvertible M) :
    ∃ M₁ : B.Modules, Scheme.Modules.IsInvertible M₁ ∧
      Nonempty ((Scheme.Modules.pullback e).obj M₁ ≅ SheafOfModules.unit (Spec (CommRingCat.of T)).ringCatSheaf) ∧
      LocIsoOnBase h M M₁ := by
  classical
  obtain ⟨hinv, ⟨erig⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor_pullback_dual_pullback_and_nonempty_pullback_iso_unit_monoidalV2 he hM
  refine ⟨M ⊗ (Scheme.Modules.pullback h).obj (Scheme.Modules.dual ((Scheme.Modules.pullback e).obj M)), hinv, ⟨erig⟩, ?_⟩
  intro s
  have hNd : Scheme.Modules.IsInvertible (Scheme.Modules.dual ((Scheme.Modules.pullback e).obj M)) :=
    (Scheme.Modules.IsInvertible.dual_monoidalV2 (hM.pullback e)).1
  obtain ⟨U, hsU, ⟨eU⟩⟩ := hNd.exists_trivialization s
  refine ⟨U, hsU, ⟨?_⟩⟩
  have hfact : (h ⁻¹ᵁ U).ι ≫ h = (h ∣_ U) ≫ U.ι := (morphismRestrict_ι h U).symm

  have eN : (Scheme.Modules.pullback (h ⁻¹ᵁ U).ι).obj
      ((Scheme.Modules.pullback h).obj (Scheme.Modules.dual ((Scheme.Modules.pullback e).obj M))) ≅ 𝟙_ _ :=
    (Scheme.Modules.pullbackComp (h ⁻¹ᵁ U).ι h).app _ ≪≫ (Scheme.Modules.pullbackCongr hfact).app _ ≪≫
      ((Scheme.Modules.pullbackComp (h ∣_ U) U.ι).app _).symm ≪≫
      (Scheme.Modules.pullback (h ∣_ U)).mapIso eU ≪≫ Scheme.Modules.pullbackTensorUnitObjIso (h ∣_ U)
  exact (Scheme.Modules.pullbackTensorObjIso (h ⁻¹ᵁ U).ι M _ ≪≫ whiskerLeftIso _ eN ≪≫ ρ_ _).symm

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isInvertible_rigidified_locIsoOnBase_of_section
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isInvertible_rigidified_locIsoOnBase_of_section (solution)
