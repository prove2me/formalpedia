-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.card_le_of_subset_support
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/7c25bf91-95f6-5d4e-8756-14dbca9f8abf

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_card_le_of_subset_support

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FltWs21
namespace B1

theorem card_le_finrank_of_primes {k A : Type u} [Field k] [CommRing A] [Algebra k A] [Module.Finite k A]
    (F : Finset (PrimeSpectrum A)) : F.card ≤ Module.finrank k A := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  have hmax : ∀ p : ↥F, (p : PrimeSpectrum A).asIdeal.IsMaximal := fun p =>
    (IsArtinianRing.isPrime_iff_isMaximal _).mp p.1.isPrime
  have hcop : Pairwise (Function.onFun IsCoprime fun p : ↥F => (p : PrimeSpectrum A).asIdeal) := by
    intro p q hpq
    rw [Function.onFun, Ideal.isCoprime_iff_codisjoint, codisjoint_iff]
    exact (hmax p).coprime_of_ne (hmax q) (fun h => hpq (Subtype.ext (PrimeSpectrum.ext h)))

  let L : A →ₗ[k] ((p : ↥F) → A ⧸ (p : PrimeSpectrum A).asIdeal) :=
    LinearMap.pi fun p => (Ideal.Quotient.mkₐ k (p : PrimeSpectrum A).asIdeal).toLinearMap
  have hLsurj : Function.Surjective L := by
    intro y
    obtain ⟨x, hx⟩ := Ideal.quotientInfToPiQuotient_surj hcop y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨a, ?_⟩
    rw [← hx]
    funext p
    rfl
  have h1 : Module.finrank k ((p : ↥F) → A ⧸ (p : PrimeSpectrum A).asIdeal) ≤ Module.finrank k A := by
    rw [← LinearMap.range_eq_top] at hLsurj
    rw [← finrank_top k ((p : ↥F) → A ⧸ (p : PrimeSpectrum A).asIdeal), ← hLsurj]
    exact LinearMap.finrank_range_le L
  have h2 : F.card ≤ Module.finrank k ((p : ↥F) → A ⧸ (p : PrimeSpectrum A).asIdeal) := by
    rw [Module.finrank_pi_fintype]
    calc F.card = ∑ _p : ↥F, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun p _ => ?_
    haveI : Nontrivial (A ⧸ (p : PrimeSpectrum A).asIdeal) :=
      Ideal.Quotient.nontrivial_iff.mpr (hmax p).ne_top
    exact Module.finrank_pos
  exact h2.trans h1

theorem card_le_finrank_of_isFinite {k : Type u} [Field k] {Z : Scheme.{u}} (q : Z ⟶ Spec (CommRingCat.of k))
    [IsFinite q] [Flat q] (F : Finset Z) : F.card ≤ q.finrank (IsLocalRing.closedPoint k) := by
  classical
  haveI : IsAffine Z := isAffine_of_isAffineHom q

  let φ : k →+* Γ(Z, ⊤) := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  letI : Algebra k Γ(Z, ⊤) := φ.toAlgebra
  haveI : Module.Finite k Γ(Z, ⊤) := by
    have h1 : q.appTop.hom.Finite := IsFinite.finite_app q ⊤ (isAffineOpen_top _)
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.Finite :=
      RingHom.Finite.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective
    have h3 : φ.Finite := RingHom.Finite.comp h1 h2
    exact h3

  have hq : q = Z.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(Z, ⊤))) := by
    have := Scheme.isoSpec_hom_naturality q
    rw [Scheme.isoSpec_Spec_hom] at this

    have e : CommRingCat.ofHom (algebraMap k Γ(Z, ⊤)) = (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ q.appTop := rfl
    rw [e, Spec.map_comp, ← Category.assoc, this, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.comp_id]
  haveI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k Γ(Z, ⊤)))) := by
    rw [show Spec.map (CommRingCat.ofHom (algebraMap k Γ(Z, ⊤))) = Z.isoSpec.inv ≫ q from by
      rw [hq, Iso.inv_hom_id_assoc]]
    infer_instance
  haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap k Γ(Z, ⊤)))) := by
    rw [show Spec.map (CommRingCat.ofHom (algebraMap k Γ(Z, ⊤))) = Z.isoSpec.inv ≫ q from by
      rw [hq, Iso.inv_hom_id_assoc]]
    infer_instance

  have hdeg : q.finrank (IsLocalRing.closedPoint k) = Module.finrank k Γ(Z, ⊤) := by
    rw [hq, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_algebraMap,
      Module.rankAtStalk_eq_finrank_of_free]
    rfl

  rw [hdeg]
  have hinj : Function.Injective (Z.isoSpec.hom.base : Z → PrimeSpectrum Γ(Z, ⊤)) :=
    Z.isoSpec.hom.homeomorph.injective
  calc F.card = (F.image Z.isoSpec.hom.base).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ Module.finrank k Γ(Z, ⊤) := card_le_finrank_of_primes _

end FltWs21.B1

open FltWs21.B1 in

theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ} {k : Type u} [Field k] {x : Spec (CommRingCat.of k) ⟶ S}
    (D : RelEffCartierDiv f r x) (F : Finset ↥(pullback f x)) (hF : ∀ z ∈ F, z ∈ D.I.support) :
    F.card ≤ r := by
  classical
  haveI := D.isFinite
  haveI := D.flat
  let ζ := D.I.subschemeι

  have hmem : ∀ z ∈ F, z ∈ Set.range ζ.base := by
    intro z hz; rw [Scheme.IdealSheafData.range_subschemeι]; exact hF z hz
  by_cases hF0 : F = ∅
  · simp [hF0]
  obtain ⟨z0, hz0⟩ := Finset.nonempty_iff_ne_empty.mpr hF0
  haveI : Nonempty D.I.subscheme := ⟨(hmem z0 hz0).choose⟩
  choose! lift hlift using hmem
  have hinj : Set.InjOn lift F := by
    intro z hz z' hz' h
    rw [← hlift z hz, ← hlift z' hz', h]
  have := card_le_finrank_of_isFinite (ζ ≫ pullback.snd f x) (F.image lift)
  rw [Finset.card_image_of_injOn hinj, D.finrank_eq] at this
  exact this

end S_AlgebraicGeometry_RelEffCartierDiv_card_le_of_subset_support
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_card_le_of_subset_support (solution)
