-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/ecaf0072-b74a-5935-8d99-a4fd56ed2063

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Hom_isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map.AlgebraicGeometry TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "map_injective_of_isIntegral Scheme.Hom morphismRestrict_app Scheme.Hom.image_preimage_eq_opensRange_inf IsIntegral Scheme image_morphismRestrict_preimage Scheme.Opens Scheme.Opens.opensRange_ι"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom Γ Hom.image_preimage_eq_opensRange_inf Opens Opens.opensRange_ι"
namespace Hom
p2m_export "AlgebraicGeometry.Scheme.Hom" "app image_preimage_eq_opensRange_inf naturality comp_apply"
namespace OConnected
p2m_open "AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)]

theorem isIso_app_of_le (V : X.Opens) (hV : V ≤ U) : IsIso (f.app V) := by
  obtain ⟨V₁, rfl⟩ : ∃ V₁ : U.toScheme.Opens, U.ι ''ᵁ V₁ = V :=
    ⟨U.ι ⁻¹ᵁ V, by rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hV]⟩
  have h := morphismRestrict_app f U V₁
  have i1 : IsIso ((f ∣_ U).app V₁) := inferInstance
  have i2 : IsIso (Y.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V₁)).op) := by
    rw [eqToHom_op]; infer_instance
  exact @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _ i2 i1 h.symm

end AlgebraicGeometry.Scheme.Hom.OConnected

theorem solution
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIntegral Y] (U : X.Opens) (hU : IsIso (f ∣_ U))
    (V : X.Opens) (hV : Function.Bijective (X.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op)) :
    IsIso (f.app V) := by
  haveI := hU
  let i : V ⊓ U ⟶ V := homOfLE inf_le_left
  let rX : Γ(X, V) ⟶ Γ(X, V ⊓ U) := X.presheaf.map i.op
  let rY : Γ(Y, f ⁻¹ᵁ V) ⟶ Γ(Y, f ⁻¹ᵁ (V ⊓ U)) := Y.presheaf.map ((Opens.map f.base).map i).op
  have hnat : rX ≫ f.app (V ⊓ U) = f.app V ≫ rY := f.naturality i.op
  haveI hiso : IsIso (f.app (V ⊓ U)) := Scheme.Hom.OConnected.isIso_app_of_le f U (V ⊓ U) inf_le_right
  have hbU : Function.Bijective (f.app (V ⊓ U)).hom := ConcreteCategory.bijective_of_isIso (f.app (V ⊓ U))
  have hc : Function.Bijective ((f.app (V ⊓ U)).hom ∘ rX.hom) := hbU.comp hV
  have hpt : ∀ s, (f.app (V ⊓ U)).hom (rX.hom s) = rY.hom ((f.app V).hom s) := fun s => by
    have := congrArg (fun φ => φ.hom s) hnat
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using this
  have hc' : Function.Bijective (rY.hom ∘ (f.app V).hom) := by
    have heq : (f.app (V ⊓ U)).hom ∘ rX.hom = rY.hom ∘ (f.app V).hom := funext hpt
    rw [← heq]; exact hc
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (f.app V).hom
  refine ⟨hc'.1.of_comp, fun t => ?_⟩
  by_cases hne : Nonempty ↥(f ⁻¹ᵁ (V ⊓ U))
  · have hinj : Function.Injective rY.hom :=
      map_injective_of_isIntegral Y ((Opens.map f.base).map i) (H := hne)
    obtain ⟨s, hs⟩ := hc'.2 (rY.hom t)
    exact ⟨s, hinj hs⟩
  · have hempty : ((f ⁻¹ᵁ (V ⊓ U) : Y.Opens) : Set Y) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp (fun h => hne h.to_subtype)
    have hbot : f ⁻¹ᵁ (V ⊓ U) = ⊥ := Opens.ext (hempty.trans Opens.coe_bot.symm)
    haveI hsub : Subsingleton Γ(Y, f ⁻¹ᵁ (V ⊓ U)) :=
      CommRingCat.subsingleton_of_isTerminal (Y.sheaf.isTerminalOfEqEmpty hbot)
    haveI hsubX : Subsingleton Γ(X, V) := hc.1.subsingleton
    have h1 : (1 : Γ(Y, f ⁻¹ᵁ V)) = 0 := by
      rw [← map_one (f.app V).hom, Subsingleton.elim (1 : Γ(X, V)) 0, map_zero]
    refine ⟨0, ?_⟩
    rw [map_zero, ← mul_one t, h1, mul_zero]

end S_AlgebraicGeometry_Scheme_Hom_isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map (solution)
