-- Prove2me | solution 1 for AlgebraicGeometry.exists_isAffineOpen_isPullback_restrict_of_isPullback_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/4afd7676-3308-545e-9c01-597f3257d12a

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Theorems.Thm_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isAffineOpen_isPullback_restrict_of_isPullback_of_isNilpotent

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem P3cAux.surjective_specMap {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (hnil : ∀ x ∈ RingHom.ker f, IsNilpotent x) :
    Surjective (Spec.map (CommRingCat.ofHom f)) := by
  refine ⟨fun x => ?_⟩
  have hx : x ∈ Set.range (PrimeSpectrum.comap f) := by
    rw [range_comap_of_surjective _ f hf]
    refine (PrimeSpectrum.mem_zeroLocus x _).mpr ?_
    intro t ht
    obtain ⟨n, hn⟩ := hnil t ht
    exact x.2.mem_of_pow_mem n (by rw [hn]; exact x.asIdeal.zero_mem)
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, hy⟩

theorem solution
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {W Q : Scheme.{u}} (q : Q ⟶ Spec (CommRingCat.of T')) (w : W ⟶ Spec (CommRingCat.of T)) (G : W ⟶ Q)
    (hG : IsPullback G w q (Spec.map (CommRingCat.ofHom π)))
    (V : W.Opens) (hV : IsAffineOpen V) :
    ∃ (Z : Q.Opens) (_ : IsAffineOpen Z) (γ : (↑V : Scheme.{u}) ⟶ ↑Z),
      γ ≫ Z.ι = V.ι ≫ G ∧ IsPullback γ (V.ι ≫ w) (Z.ι ≫ q) (Spec.map (CommRingCat.ofHom π)) := by
  classical

  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom π)) := IsClosedImmersion.spec_of_surjective _ hπ
  haveI : Surjective (Spec.map (CommRingCat.ofHom π)) := by
    refine P3cAux.surjective_specMap π hπ (fun x hx => ?_)
    obtain ⟨n, hn⟩ := hker
    refine ⟨n, ?_⟩
    have hx' : x ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at hx'
    exact (Submodule.mem_bot _).mp hx'
  haveI hGc : IsClosedImmersion G := MorphismProperty.of_isPullback hG.flip inferInstance
  haveI hGs : Surjective G := MorphismProperty.of_isPullback hG.flip inferInstance
  have hce : Topology.IsClosedEmbedding G.base := G.isClosedEmbedding
  have hinj : Function.Injective G.base := hce.injective
  have hbij : Function.Bijective G.base := ⟨hinj, G.surjective⟩
  have hopen : ∀ O : Set W, IsOpen O → IsOpen (G.base '' O) := by
    intro O hO
    have h1 : G.base '' O = (G.base '' Oᶜ)ᶜ := by rw [Set.image_compl_eq hbij, compl_compl]
    rw [h1, isOpen_compl_iff]
    exact hce.isClosedMap _ hO.isClosed_compl
  let Z : Q.Opens := ⟨G.base '' (V : Set W), hopen _ V.isOpen⟩
  have hpre : G ⁻¹ᵁ Z = V := by
    ext x
    change G.base x ∈ G.base '' (V : Set W) ↔ x ∈ (V : Set W)
    exact hinj.mem_set_image

  let ε : (↑V : Scheme.{u}) ≅ ↑(G ⁻¹ᵁ Z) := W.isoOfEq hpre.symm
  have hε : ε.hom ≫ (G ⁻¹ᵁ Z).ι = V.ι := Scheme.isoOfEq_hom_ι _ _
  let γ : (↑V : Scheme.{u}) ⟶ ↑Z := ε.hom ≫ (G ∣_ Z)
  have hγ : γ ≫ Z.ι = V.ι ≫ G := by
    simp only [γ, Category.assoc, morphismRestrict_ι]
    rw [← Category.assoc, hε]
  have sq1 : IsPullback γ V.ι Z.ι G := by
    have s : IsPullback ε.hom V.ι (G ⁻¹ᵁ Z).ι (𝟙 W) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, hε]⟩
    have := s.paste_horiz (isPullback_morphismRestrict G Z)
    rwa [Category.id_comp] at this
  haveI : IsAffine (↑V : Scheme.{u}) := hV
  haveI : IsClosedImmersion (G ∣_ Z) := IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) hGc Z
  haveI : Surjective (G ∣_ Z) := IsZariskiLocalAtTarget.restrict (P := @Surjective) hGs Z
  haveI : IsClosedImmersion γ := inferInstance
  haveI : Surjective γ := inferInstance
  have hZaff : IsAffineOpen Z := AlgebraicGeometry.isAffine_of_isClosedImmersion_of_surjective γ
  exact ⟨Z, hZaff, γ, hγ, sq1.paste_vert hG⟩

end S_AlgebraicGeometry_exists_isAffineOpen_isPullback_restrict_of_isPullback_of_isNilpotent
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isAffineOpen_isPullback_restrict_of_isPullback_of_isNilpotent (solution)
