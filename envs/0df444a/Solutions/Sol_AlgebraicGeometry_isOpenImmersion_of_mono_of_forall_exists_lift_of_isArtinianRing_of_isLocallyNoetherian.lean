-- Prove2me | solution 1 for AlgebraicGeometry.isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocallyNoetherian
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/2b798025-6622-5133-ac0e-c85a1a1a964f

import Mathlib
import Theorems.Thm_AlgebraicGeometry_isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocallyNoetherian

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

theorem solution
    {X M : Scheme.{u}} [IsLocallyNoetherian X] (ϖ : M ⟶ X) [LocallyOfFinitePresentation ϖ] [Mono ϖ]
    (h : ∀ (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
      [CommRing T] [Nontrivial T] (p : T' →+* T), Function.Surjective p → RingHom.ker p * maximalIdeal T' = ⊥ →
      ∀ (s : Spec (CommRingCat.of T') ⟶ X) (m : Spec (CommRingCat.of T) ⟶ M),
        m ≫ ϖ = Spec.map (CommRingCat.ofHom p) ≫ s →
        ∃ m' : Spec (CommRingCat.of T') ⟶ M, m' ≫ ϖ = s ∧ Spec.map (CommRingCat.ofHom p) ≫ m' = m) :
    IsOpenImmersion ϖ := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsOpenImmersion) (fun U : X.affineOpens => (U : X.Opens))
    (iSup_affineOpens_eq_top X)
  intro U
  haveI : IsNoetherianRing Γ(X, (U : X.Opens)) := IsLocallyNoetherian.component_noetherian U
  let e : (↑(U : X.Opens) : Scheme.{u}) ≅ Spec Γ(X, (U : X.Opens)) := U.2.isoSpec
  haveI : Mono (ϖ ∣_ (U : X.Opens)) :=
    mono_of_mono_fac (morphismRestrict_ι ϖ (U : X.Opens))
  haveI : Mono (ϖ ∣_ (U : X.Opens) ≫ e.hom) := mono_comp _ _
  haveI : LocallyOfFinitePresentation (ϖ ∣_ (U : X.Opens) ≫ e.hom) := inferInstance
  have key : IsOpenImmersion (ϖ ∣_ (U : X.Opens) ≫ e.hom) := by
    refine AlgebraicGeometry.isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocalRing
      (ϖ ∣_ (U : X.Opens) ≫ e.hom) ?_
    intro T' T _ _ _ _ _ p hp hsmall s m hm
    obtain ⟨m₁, hm₁, hm₂⟩ := h T' T p hp hsmall (s ≫ e.inv ≫ (U : X.Opens).ι) (m ≫ (ϖ ⁻¹ᵁ (U : X.Opens)).ι) (by
      rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, ← Category.assoc]
      have : m ≫ ϖ ∣_ (U : X.Opens) = (Spec.map (CommRingCat.ofHom p) ≫ s) ≫ e.inv := by
        rw [← hm, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [this, Category.assoc, Category.assoc])
    have hrange : Set.range m₁.base ⊆ Set.range (ϖ ⁻¹ᵁ (U : X.Opens)).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      show ϖ.base (m₁.base t) ∈ (U : X.Opens)
      have ht : ϖ.base (m₁.base t) = (U : X.Opens).ι.base (e.inv.base (s.base t)) := by
        have := congrArg (fun φ => φ.base t) hm₁
        simpa using this
      rw [ht]
      exact (e.inv.base (s.base t)).2
    refine ⟨IsOpenImmersion.lift (ϖ ⁻¹ᵁ (U : X.Opens)).ι m₁ hrange, ?_, ?_⟩
    · haveI : Mono (e.inv ≫ (U : X.Opens).ι) := mono_comp _ _
      apply (cancel_mono (e.inv ≫ (U : X.Opens).ι)).1
      rw [Category.assoc, Category.assoc, e.hom_inv_id_assoc, morphismRestrict_ι, ← Category.assoc,
        IsOpenImmersion.lift_fac, hm₁]
    · apply (cancel_mono (ϖ ⁻¹ᵁ (U : X.Opens)).ι).1
      rw [Category.assoc, IsOpenImmersion.lift_fac, hm₂]
  exact IsOpenImmersion.of_comp (ϖ ∣_ (U : X.Opens)) e.hom

end S_AlgebraicGeometry_isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocallyNoetherian
end P2MW
export P2MW.S_AlgebraicGeometry_isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocallyNoetherian (solution)
