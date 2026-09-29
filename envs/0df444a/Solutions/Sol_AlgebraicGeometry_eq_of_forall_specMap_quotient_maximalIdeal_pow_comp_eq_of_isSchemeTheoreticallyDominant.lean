-- Prove2me | solution 1 for AlgebraicGeometry.eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq_of_isSchemeTheoreticallyDominant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/e239d3dc-2c87-516f-b827-0b457508f165

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_mem_and_iota_comp_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq_of_isSchemeTheoreticallyDominant

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq_of_isSchemeTheoreticallyDominant.AlgebraicGeometry TopologicalSpace Opposite"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsLocallyNoetherian IsClosedImmersion.isIso_iff_ker_eq_bot Scheme.Hom.le_ker_comp Scheme.Hom Opens.isDominant_ι isClosedImmersion_equalizer_ι_left Spec IsIntegral Spec.map Scheme IsSchemeTheoreticallyDominant IsClosedImmersion IsSeparated IsDominant IsSchemeTheoreticallyDominant.of_isDominant exists_mem_and_iota_comp_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq"
namespace InfinitesimalRigidityGlobal
p2m_open "AlgebraicGeometry"

theorem eq_of_isSchemeTheoreticallyDominant_comp_eq {W X Y Z : Scheme.{u}} (ι : W ⟶ X)
    [IsSchemeTheoreticallyDominant ι] (f g : X ⟶ Y) (s : Y ⟶ Z) [IsSeparated s]
    (hs : f ≫ s = g ≫ s) (hU : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g hs.symm
  let ι' : U' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := ‹_›
  have hlift : (equalizer.lift ι' (by ext1; exact hU)).left ≫ (equalizer.ι f' g').left = ι := by
    rw [← Over.comp_left, equalizer.lift_ι]
    rfl
  have hker : (equalizer.ι f' g').left.ker = ⊥ := by
    have := Scheme.Hom.le_ker_comp (equalizer.lift ι' (by ext1; exact hU)).left
      (equalizer.ι f' g').left
    rw [hlift] at this
    exact le_bot_iff.mp (this.trans (le_of_eq ι.ker_eq_bot))
  have : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  have key : (equalizer.ι f' g').left ≫ f = (equalizer.ι f' g').left ≫ g :=
    congr($(equalizer.condition f' g').left)
  simpa using congrArg (fun φ => inv ((equalizer.ι f' g').left) ≫ φ) key

theorem eq_of_forall_jets_eq {X Y Z : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : ∀ U : X.Opens, (U : Set X).Nonempty → IsSchemeTheoreticallyDominant U.ι)
    (f g : X ⟶ Y) (s : Y ⟶ Z) [IsSeparated s] (hs : f ≫ s = g ≫ s) (x : X)
    (h : ∀ n : ℕ,
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n))) ≫ X.fromSpecStalk x ≫ f =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n))) ≫ X.fromSpecStalk x ≫ g) :
    f = g := by
  obtain ⟨U, hxU, hU⟩ :=
    AlgebraicGeometry.exists_mem_and_iota_comp_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq
      f g x h
  haveI : IsSchemeTheoreticallyDominant U.ι := hX U ⟨x, hxU⟩
  exact eq_of_isSchemeTheoreticallyDominant_comp_eq U.ι f g s hs hU

theorem eq_of_forall_jets_eq_of_isIntegral {X Y Z : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X]
    (f g : X ⟶ Y) (s : Y ⟶ Z) [IsSeparated s] (hs : f ≫ s = g ≫ s) (x : X)
    (h : ∀ n : ℕ,
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n))) ≫ X.fromSpecStalk x ≫ f =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n))) ≫ X.fromSpecStalk x ≫ g) :
    f = g := by
  refine eq_of_forall_jets_eq (fun U hU => ?_) f g s hs x h
  haveI : IsDominant U.ι := AlgebraicGeometry.Opens.isDominant_ι (U.2.dense hU)
  exact IsSchemeTheoreticallyDominant.of_isDominant _

end AlgebraicGeometry.InfinitesimalRigidityGlobal

theorem solution
    {X Y Z : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : ∀ U : X.Opens, (U : Set X).Nonempty → IsSchemeTheoreticallyDominant U.ι)
    (f g : X ⟶ Y) (s : Y ⟶ Z) [IsSeparated s] (hs : f ≫ s = g ≫ s) (x : X)
    (h : ∀ n : ℕ,
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n))) ≫ X.fromSpecStalk x ≫ f =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n))) ≫ X.fromSpecStalk x ≫ g) :
    f = g :=
  AlgebraicGeometry.InfinitesimalRigidityGlobal.eq_of_forall_jets_eq hX f g s hs x h

end S_AlgebraicGeometry_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq_of_isSchemeTheoreticallyDominant
end P2MW
export P2MW.S_AlgebraicGeometry_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq_of_isSchemeTheoreticallyDominant (solution)
