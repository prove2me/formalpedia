-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.nonempty_pullback_one_pol_iso_unit_of_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/3ef46a78-8ffc-5541-930b-8e25600b7330

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_one_comp_eq_specMap_comp_one_of_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_nonempty_pullback_one_pol_iso_unit_of_pullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem solution
    {g d n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : PolarisedAbelianScheme g d n S) (v : PolarisedAbelianScheme g d n S')
    (h : PolarisedAbelianScheme.IsPullback φ u v)

    (hu : Nonempty ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).obj
      ((Scheme.Modules.pullback (u.L.one (𝟙 _)).1).obj u.pol) ≅ SheafOfModules.unit (Spec (CommRingCat.of S')).ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback (v.L.one (𝟙 _)).1).obj v.pol ≅ SheafOfModules.unit (Spec (CommRingCat.of S')).ringCatSheaf) := by
  obtain ⟨gA, hg, hmul, -, ⟨epol⟩⟩ := h
  obtain ⟨eu⟩ := hu
  have hone : (v.L.one (𝟙 _)).1 ≫ gA = Spec.map (CommRingCat.ofHom φ) ≫ (u.L.one (𝟙 _)).1 :=
    AlgebraicGeometry.PolarisedAbelianScheme.one_comp_eq_specMap_comp_one_of_mul φ u v gA hg hmul
  exact ⟨(Scheme.Modules.pullback (v.L.one (𝟙 _)).1).mapIso epol.symm ≪≫
    (Scheme.Modules.pullbackComp (v.L.one (𝟙 _)).1 gA).app u.pol ≪≫
    (Scheme.Modules.pullbackCongr hone).app u.pol ≪≫
    ((Scheme.Modules.pullbackComp (Spec.map (CommRingCat.ofHom φ)) (u.L.one (𝟙 _)).1).app u.pol).symm ≪≫ eu⟩

end S_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_nonempty_pullback_one_pol_iso_unit_of_pullback
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_nonempty_pullback_one_pol_iso_unit_of_pullback (solution)
