-- Prove2me | solution 1 for AlgebraicGeometry.exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_of_fg_idealCut
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/2a3034cf-b4dc-5e58-a930-a73c80d5cdb3

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_forall_factors_iff_of_idealCut
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_of_fg_idealCut

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry

namespace P2mWs11CS1p

theorem finitePresentation_app_of_fg_cut {C H : Scheme.{u}} (ι : C ⟶ H) [IsClosedImmersion ι]
    (U : H.Opens) (hU : IsAffineOpen U) (J : Ideal Γ(H, U)) (hJ : J.FG)
    (hcut : ∀ (A : Type u) [CommRing A] (φ : Γ(H, U) →+* A),
      (∃ v : Spec (CommRingCat.of A) ⟶ C, v ≫ ι = Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec) ↔
        Ideal.map φ J = ⊥) :
    (ι.app U).hom.FinitePresentation := by
  have hV : IsAffineOpen (ι ⁻¹ᵁ U) := hU.preimage ι
  refine RingHom.FinitePresentation.of_surjective _ (ι.app_surjective U hU) ?_
  suffices hker : RingHom.ker (ι.app U).hom = J by rw [hker]; exact hJ
  apply le_antisymm
  ·
    intro k hk
    have hQ : Ideal.map (Ideal.Quotient.mk J) J = ⊥ := by
      rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    obtain ⟨v, hv⟩ := (hcut _ (Ideal.Quotient.mk J)).mpr hQ
    have hrange : Set.range v ⊆ Set.range (ι ⁻¹ᵁ U).ι := by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      show ι (v x) ∈ U
      rw [← Scheme.Hom.comp_apply, hv, Scheme.Hom.comp_apply, ← SetLike.mem_coe, ← hU.range_fromSpec]
      exact ⟨_, rfl⟩
    let w : Spec (CommRingCat.of (Γ(H, U) ⧸ J)) ⟶ ↑(ι ⁻¹ᵁ U) := IsOpenImmersion.lift (ι ⁻¹ᵁ U).ι v hrange
    have hw : w ≫ (ι ⁻¹ᵁ U).ι = v := IsOpenImmersion.lift_fac _ _ _
    let ψ : Γ(C, ι ⁻¹ᵁ U) ⟶ CommRingCat.of (Γ(H, U) ⧸ J) := Spec.preimage (w ≫ hV.isoSpec.hom)
    have hψ : Spec.map ψ = w ≫ hV.isoSpec.hom := Spec.map_preimage _
    have key : ι.app U ≫ ψ = CommRingCat.ofHom (Ideal.Quotient.mk J) := by
      apply Spec.map_injective
      rw [← cancel_mono hU.fromSpec, Spec.map_comp, Category.assoc, Scheme.Hom.app_eq_appLE,
        IsAffineOpen.SpecMap_appLE_fromSpec ι hU hV le_rfl, hψ, Category.assoc,
        ← IsAffineOpen.isoSpec_inv_ι, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, hw, hv]
    have : (Ideal.Quotient.mk J) k = 0 := by
      have := congrArg (fun f : Γ(H, U) ⟶ CommRingCat.of (Γ(H, U) ⧸ J) => f.hom k) key
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
      rw [← this, RingHom.mem_ker.mp hk, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  ·
    rw [← Ideal.map_eq_bot_iff_le_ker]
    refine (hcut _ (ι.app U).hom).mp ⟨hV.fromSpec, ?_⟩
    rw [CommRingCat.ofHom_hom, Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec ι hU hV le_rfl]

theorem finitePresentation_map_of_isAffineOpen {C : Scheme.{u}} (V W : C.Opens)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (e : V ≤ W) :
    (C.presheaf.map (homOfLE e).op).hom.FinitePresentation := by
  have := HasRingHomProperty.appLE @LocallyOfFinitePresentation (𝟙 C) inferInstance ⟨W, hW⟩ ⟨V, hV⟩ e
  simp [Scheme.Hom.appLE] at this
  exact this

end P2mWs11CS1p

open P2mWs11CS1p in

theorem solution
    (H : Scheme.{u})
    (Q : ∀ (A : Type u) [CommRing A], (Spec (CommRingCat.of A) ⟶ H) → Prop)

    (hQmap : ∀ (A A' : Type u) [CommRing A] [CommRing A'] (φ : A →+* A') (u : Spec (CommRingCat.of A) ⟶ H),
      Q A u → Q A' (Spec.map (CommRingCat.ofHom φ) ≫ u))

    (hQloc : ∀ (A : Type u) [CommRing A] (u : Spec (CommRingCat.of A) ⟶ H) (ι : Type u) (r : ι → A),
      Ideal.span (Set.range r) = ⊤ →
      (∀ i, Q (Localization.Away (r i))
        (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (r i)))) ≫ u)) → Q A u)

    (hQcut : ∀ (U : H.Opens) (hU : IsAffineOpen U) (B : Type u) [CommRing B]
      (e : Spec (CommRingCat.of B) ≅ (U : Scheme.{u})),
      ∃ J : Ideal B, J.FG ∧ ∀ (A : Type u) [CommRing A] (φ : B →+* A),
        Q A (Spec.map (CommRingCat.ofHom φ) ≫ e.hom ≫ U.ι) ↔ Ideal.map φ J = ⊥) :
    ∃ (C : Scheme.{u}) (ι : C ⟶ H), IsClosedImmersion ι ∧ LocallyOfFinitePresentation ι ∧
      ∀ (A : Type u) [CommRing A] (u : Spec (CommRingCat.of A) ⟶ H),
        (∃ v : Spec (CommRingCat.of A) ⟶ C, v ≫ ι = u) ↔ Q A u := by
  obtain ⟨C, ι, hι, hC⟩ :=
    AlgebraicGeometry.exists_isClosedImmersion_forall_factors_iff_of_idealCut H Q hQmap hQloc
      (fun U hU B _ e => (hQcut U hU B e).imp fun J hJ => hJ.2)
  refine ⟨C, ι, hι, ?_, hC⟩
  rw [HasRingHomProperty.iff_appLE (P := @LocallyOfFinitePresentation)]
  intro U V e
  obtain ⟨J, hJfg, hJ⟩ := hQcut U.1 U.2 Γ(H, U.1) U.2.isoSpec.symm
  have happ : (ι.app U.1).hom.FinitePresentation := by
    refine finitePresentation_app_of_fg_cut ι U.1 U.2 J hJfg fun A _ φ => ?_
    rw [hC A, ← hJ A φ, Iso.symm_hom, IsAffineOpen.isoSpec_inv_ι]
  have hres : (C.presheaf.map (homOfLE e).op).hom.FinitePresentation :=
    finitePresentation_map_of_isAffineOpen V.1 (ι ⁻¹ᵁ U.1) V.2 (U.2.preimage ι) e
  show (ι.app U.1 ≫ C.presheaf.map (homOfLE e).op).hom.FinitePresentation
  rw [CommRingCat.hom_comp]
  exact hres.comp happ

end S_AlgebraicGeometry_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_of_fg_idealCut
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_locallyOfFinitePresentation_forall_factors_iff_of_fg_idealCut (solution)
