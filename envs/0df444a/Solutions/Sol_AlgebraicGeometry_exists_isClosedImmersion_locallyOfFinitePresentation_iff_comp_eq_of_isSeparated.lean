-- Prove2me | solution 1 for AlgebraicGeometry.exists_isClosedImmersion_locallyOfFinitePresentation_iff_comp_eq_of_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/fecd6c42-9d00-54e7-87e8-ddfbc5efa575

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_locallyOfFinitePresentation_iff_comp_eq_of_isSeparated

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace EqLocus2

theorem locallyOfFinitePresentation_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hg : LocallyOfFiniteType g] [hfg : LocallyOfFinitePresentation (f ≫ g)] : LocallyOfFinitePresentation f := by
  have hQ : RingHom.StableUnderCompositionWithLocalizationAwaySource @RingHom.FinitePresentation :=
    (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finitePresentation_holdsForLocalizationAway).left
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation) hQ]
  intro x

  obtain ⟨W, hW, hxW, -⟩ := (Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens Z))
    (show g.base (f.base x) ∈ (⊤ : Z.Opens) from trivial)

  obtain ⟨U, hU, hxU, hUW⟩ := (Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens Y))
    (show f.base x ∈ g ⁻¹ᵁ W from hxW)

  obtain ⟨V, hV, hxV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X))
    (show x ∈ f ⁻¹ᵁ U from hxU)
  refine ⟨⟨U, hU⟩, ⟨V, hV⟩, hxV, hVU, ?_⟩
  have h1 : (g.appLE W U hUW).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType g hg ⟨W, hW⟩ ⟨U, hU⟩ hUW
  have hVW : V ≤ (f ≫ g) ⁻¹ᵁ W := by
    rw [Scheme.Hom.comp_preimage]; exact hVU.trans fun y hy => hUW hy
  have h2 : ((f ≫ g).appLE W V hVW).hom.FinitePresentation :=
    HasRingHomProperty.appLE @LocallyOfFinitePresentation (f ≫ g) hfg ⟨W, hW⟩ ⟨V, hV⟩ hVW
  rw [← Scheme.Hom.appLE_comp_appLE f g W U V hUW hVU, CommRingCat.hom_comp] at h2
  exact RingHom.FinitePresentation.of_comp_finiteType _ h2 h1

theorem locallyOfFinitePresentation_diagonal {H S : Scheme.{u}} (q : H ⟶ S) [LocallyOfFiniteType q] :
    LocallyOfFinitePresentation (pullback.diagonal q) := by
  haveI : LocallyOfFinitePresentation (pullback.diagonal q ≫ pullback.fst q q) := by
    rw [pullback.diagonal_fst]; infer_instance
  exact locallyOfFinitePresentation_of_comp _ (pullback.fst q q)

end EqLocus2

theorem solution
    {H S T : Scheme.{u}} (q : H ⟶ S) [IsSeparated q] (t : T ⟶ S) (u v : T ⟶ H) (hu : u ≫ q = t) (hv : v ≫ q = t) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ T), IsClosedImmersion j ∧ (LocallyOfFiniteType q → LocallyOfFinitePresentation j) ∧
      ∀ {T' : Scheme.{u}} (ψ : T' ⟶ T), ψ ≫ u = ψ ≫ v ↔ ∃ ψ' : T' ⟶ Z, ψ' ≫ j = ψ := by
  refine ⟨pullback (pullback.lift u v (hu.trans hv.symm)) (pullback.diagonal q),
    pullback.fst (pullback.lift u v (hu.trans hv.symm)) (pullback.diagonal q), inferInstance, ?_,
    fun ψ => ⟨fun h => ?_, fun ⟨ψ', hψ'⟩ => ?_⟩⟩
  · intro hq
    haveI := EqLocus2.locallyOfFinitePresentation_diagonal q
    infer_instance
  · refine ⟨pullback.lift ψ (ψ ≫ u) ?_, pullback.lift_fst _ _ _⟩
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd, Category.comp_id, h]
  · have hc := pullback.condition (f := pullback.lift u v (hu.trans hv.symm)) (g := pullback.diagonal q)
    have h1 := congrArg (fun φ => φ ≫ pullback.fst q q) hc
    have h2 := congrArg (fun φ => φ ≫ pullback.snd q q) hc
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst, pullback.diagonal_snd,
      Category.comp_id] at h1 h2
    rw [← hψ', Category.assoc, Category.assoc, h1, h2]

end S_AlgebraicGeometry_exists_isClosedImmersion_locallyOfFinitePresentation_iff_comp_eq_of_isSeparated
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_locallyOfFinitePresentation_iff_comp_eq_of_isSeparated (solution)
