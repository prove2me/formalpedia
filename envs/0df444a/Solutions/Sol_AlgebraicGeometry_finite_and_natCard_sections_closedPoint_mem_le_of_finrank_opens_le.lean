-- Prove2me | solution 1 for AlgebraicGeometry.finite_and_natCard_sections_closedPoint_mem_le_of_finrank_opens_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/7c2fce25-2cc8-5f23-b1ba-02f1c6161daa

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_finite_and_natCard_sections_le_of_finrank_specialFibre_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_finite_and_natCard_sections_closedPoint_mem_le_of_finrank_opens_le

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace LocalCount

theorem quasiCompact_ι {X : Scheme.{u}} [QuasiSeparatedSpace X] (U : X.Opens) (hU : IsCompact (U : Set X)) :
    QuasiCompact U.ι := by
  refine ⟨fun W hWo hWc => ?_⟩
  rw [U.ι.isOpenEmbedding.isEmbedding.isCompact_iff, Set.image_preimage_eq_inter_range]
  have hr : Set.range U.ι.base = (U : Set X) := U.range_ι
  rw [hr]
  exact QuasiSeparatedSpace.inter_isCompact W U hWo hWc U.isOpen hU

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R] [HenselianLocalRing R]

theorem core {X Y : Scheme.{u}} (g : X ⟶ Spec (.of R))
    [LocallyOfFiniteType g] [LocallyQuasiFinite g] [IsSeparated g] [QuasiCompact g]
    (q : Y ⟶ Spec (.of (IsLocalRing.ResidueField R))) (π : Y ⟶ X)
    (hY : IsPullback π q g (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    (U : X.Opens) [QuasiCompact U.ι] (V : Y.Opens) (hUV : π ⁻¹ᵁ U = V) (B : ℕ)
    (hB : letI := Scheme.TwoAffineOpenCover.algebraOfHom q V
      Module.Finite (IsLocalRing.ResidueField R) Γ(Y, V) ∧
        Module.finrank (IsLocalRing.ResidueField R) Γ(Y, V) ≤ B) :
    Finite {s : Spec (.of R) ⟶ (U : Scheme.{u}) // s ≫ (U.ι ≫ g) = 𝟙 _} ∧
      Nat.card {s : Spec (.of R) ⟶ (U : Scheme.{u}) // s ≫ (U.ι ≫ g) = 𝟙 _} ≤ B := by
  subst hUV
  have hY' : IsPullback (π ∣_ U) ((π ⁻¹ᵁ U).ι ≫ q) (U.ι ≫ g)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :=
    (isPullback_morphismRestrict π U).paste_vert hY
  refine finite_and_natCard_sections_le_of_finrank_specialFibre_le (FractionRing R) (U.ι ≫ g)
    ((π ⁻¹ᵁ U).ι ≫ q) (π ∣_ U) hY' B ?_
  letI iV := Scheme.TwoAffineOpenCover.algebraOfHom q (π ⁻¹ᵁ U)
  letI iT := Scheme.TwoAffineOpenCover.algebraOfHom ((π ⁻¹ᵁ U).ι ≫ q) ⊤

  have key : q.appLE ⊤ (π ⁻¹ᵁ U) le_top ≫ (π ⁻¹ᵁ U).topIso.inv = ((π ⁻¹ᵁ U).ι ≫ q).appLE ⊤ ⊤ le_top := by
    rw [← Scheme.Hom.appLE_comp_appLE (π ⁻¹ᵁ U).ι q ⊤ (π ⁻¹ᵁ U) ⊤ le_top
      (by rw [Scheme.Opens.ι_preimage_self])]
    congr 1
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    rfl
  let e : Γ(Y, π ⁻¹ᵁ U) ≃ₐ[IsLocalRing.ResidueField R] Γ(↑(π ⁻¹ᵁ U), ⊤) :=
    AlgEquiv.ofRingEquiv (f := (π ⁻¹ᵁ U).topIso.symm.commRingCatIsoToRingEquiv) (fun x => by
      change ((q.appLE ⊤ (π ⁻¹ᵁ U) le_top) ≫ (π ⁻¹ᵁ U).topIso.inv).hom
          ((Scheme.ΓSpecIso (.of (IsLocalRing.ResidueField R))).inv.hom x) =
        (((π ⁻¹ᵁ U).ι ≫ q).appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (.of (IsLocalRing.ResidueField R))).inv.hom x)
      rw [key])
  haveI : Module.Finite (IsLocalRing.ResidueField R) Γ(Y, π ⁻¹ᵁ U) := hB.1
  exact ⟨Module.Finite.equiv e.toLinearEquiv, e.toLinearEquiv.finrank_eq ▸ hB.2⟩

end LocalCount

open LocalCount in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R] [HenselianLocalRing R]
    {X Y : Scheme.{u}} (g : X ⟶ Spec (.of R))
    [LocallyOfFiniteType g] [LocallyQuasiFinite g] [IsSeparated g] [QuasiCompact g]
    (q : Y ⟶ Spec (.of (IsLocalRing.ResidueField R))) (π : Y ⟶ X)
    (hY : IsPullback π q g (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    (V : Y.Opens) (B : ℕ)
    (hB : letI := Scheme.TwoAffineOpenCover.algebraOfHom q V
      Module.Finite (IsLocalRing.ResidueField R) Γ(Y, V) ∧
        Module.finrank (IsLocalRing.ResidueField R) Γ(Y, V) ≤ B) :
    Finite {s : Spec (.of R) ⟶ X // s ≫ g = 𝟙 _ ∧ s.base (IsLocalRing.closedPoint R) ∈ π.base '' (V : Set Y)} ∧
      Nat.card {s : Spec (.of R) ⟶ X // s ≫ g = 𝟙 _ ∧
        s.base (IsLocalRing.closedPoint R) ∈ π.base '' (V : Set Y)} ≤ B := by
  classical

  haveI : LocallyQuasiFinite q := MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) hY inferInstance
  haveI : QuasiCompact q := MorphismProperty.of_isPullback (P := @QuasiCompact) hY inferInstance
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  haveI : IsClosedImmersion π := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hY.flip inferInstance
  have hYuniv : (q.base ⁻¹' {default} : Set Y) = Set.univ :=
    Set.eq_univ_of_forall fun y => Subsingleton.elim _ _
  haveI : DiscreteTopology Y := isDiscrete_univ_iff.mp (hYuniv ▸ q.isDiscrete_preimage_singleton default)
  haveI : Finite Y := Set.finite_univ_iff.mp (hYuniv ▸ q.finite_preimage_singleton default)

  have hW : ∀ y : Y, ∃ W : X.Opens, IsAffineOpen W ∧ π.base ⁻¹' (W : Set X) = {y} := by
    intro y
    obtain ⟨t, ht, hty⟩ := π.isClosedEmbedding.isInducing.isOpen_iff.mp (isOpen_discrete {y})
    have hyt : π.base y ∈ t := by rw [← Set.mem_preimage, hty]; exact Set.mem_singleton y
    obtain ⟨_, ⟨W, hWa, rfl⟩, hyW, hWt⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hyt ht
    refine ⟨W, hWa, subset_antisymm (fun z hz => ?_) ?_⟩
    · rw [← hty]; exact hWt hz
    · rintro z rfl; exact hyW
  choose W hWa hWy using hW
  let U : X.Opens := ⨆ v : V, W v.1
  have hUV : π ⁻¹ᵁ U = V := by
    ext y
    change y ∈ π.base ⁻¹' (U : Set X) ↔ y ∈ (V : Set Y)
    simp only [U, TopologicalSpace.Opens.coe_iSup, Set.preimage_iUnion, Set.mem_iUnion, hWy,
      Set.mem_singleton_iff]
    exact ⟨fun ⟨v, hv⟩ => hv ▸ v.2, fun hy => ⟨⟨y, hy⟩, rfl⟩⟩
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated g
  haveI : QuasiCompact U.ι := quasiCompact_ι U (by
    change IsCompact ((⨆ v : V, W v.1 : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_iSup]
    exact isCompact_iUnion fun v => (hWa v.1).isCompact)
  obtain ⟨hfin, hcard⟩ := core g q π hY U V hUV B hB

  have hcl : ∀ s : {s : Spec (.of R) ⟶ X // s ≫ g = 𝟙 _ ∧
      s.base (IsLocalRing.closedPoint R) ∈ π.base '' (V : Set Y)}, Set.range s.1.base ⊆ Set.range U.ι.base := by
    rintro ⟨s, -, v, hv, hsv⟩
    rw [Scheme.Opens.range_ι]
    have hmem : s.base (IsLocalRing.closedPoint R) ∈ U := by
      rw [← hsv]
      change v ∈ π ⁻¹ᵁ U
      rw [hUV]
      exact hv
    have htop : s ⁻¹ᵁ U = ⊤ := IsLocalRing.closed_point_mem_iff.mp hmem
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ s ⁻¹ᵁ U := by rw [htop]; trivial
    exact hx
  let Φ : {s : Spec (.of R) ⟶ X // s ≫ g = 𝟙 _ ∧ s.base (IsLocalRing.closedPoint R) ∈ π.base '' (V : Set Y)} →
      {s : Spec (.of R) ⟶ (U : Scheme.{u}) // s ≫ (U.ι ≫ g) = 𝟙 _} := fun s =>
    ⟨IsOpenImmersion.lift U.ι s.1 (hcl s), by rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact s.2.1⟩
  have hΦ : Function.Injective Φ := by
    intro s t h
    apply Subtype.ext
    have h' := congrArg (fun s' => s'.1 ≫ U.ι) h
    simpa only [Φ, IsOpenImmersion.lift_fac] using h'
  haveI := hfin
  exact ⟨Finite.of_injective Φ hΦ, (Nat.card_le_card_of_injective Φ hΦ).trans hcard⟩

end S_AlgebraicGeometry_finite_and_natCard_sections_closedPoint_mem_le_of_finrank_opens_le
end P2MW
export P2MW.S_AlgebraicGeometry_finite_and_natCard_sections_closedPoint_mem_le_of_finrank_opens_le (solution)
