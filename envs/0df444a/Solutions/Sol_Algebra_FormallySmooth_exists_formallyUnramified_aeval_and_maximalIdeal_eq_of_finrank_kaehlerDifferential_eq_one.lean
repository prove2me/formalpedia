-- Prove2me | solution 1 for Algebra.FormallySmooth.exists_formallyUnramified_aeval_and_maximalIdeal_eq_of_finrank_kaehlerDifferential_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/e15d1f26-5ca8-5965-a2f1-bb5c84c4d69b

import Mathlib
import Theorems.Thm_Algebra_FormallySmooth_formallySmooth_and_formallyUnramified_aeval_of_existsUnique_smul_D_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_FormallySmooth_exists_formallyUnramified_aeval_and_maximalIdeal_eq_of_finrank_kaehlerDifferential_eq_one

set_option autoImplicit false

open IsLocalRing Polynomial TensorProduct

universe u v

theorem solution
    {A : Type u} {S : Type v} [CommRing A] [IsLocalRing A] [CommRing S] [IsLocalRing S]
    [Algebra A S] [IsLocalHom (algebraMap A S)] [Algebra.FormallySmooth A S] [Algebra.EssFiniteType A S]
    (hres : Function.Surjective (algebraMap A (ResidueField S)))
    (h1 : Module.finrank S Ω[S⁄A] = 1) :
    ∃ t : S, t ∈ maximalIdeal S ∧
      (Polynomial.aeval t : A[X] →ₐ[A] S).toRingHom.FormallySmooth ∧
      (Polynomial.aeval t : A[X] →ₐ[A] S).toRingHom.FormallyUnramified ∧
      maximalIdeal S = Ideal.span {t} ⊔ (maximalIdeal A).map (algebraMap A S) := by
  classical
  set κ := ResidueField S with hκ

  haveI : Module.Finite S Ω[S⁄A] := inferInstance
  haveI : Module.Free S Ω[S⁄A] := Module.free_of_flat_of_isLocalRing
  let b : Module.Basis (Fin 1) S Ω[S⁄A] := Module.finBasisOfFinrankEq S Ω[S⁄A] h1
  set ω₀ : Ω[S⁄A] := b 0 with hω₀
  have hrepr : ∀ ω : Ω[S⁄A], ω = b.repr ω 0 • ω₀ := by
    intro ω
    conv_lhs => rw [← b.sum_repr ω]
    rw [Fin.sum_univ_one]
  have hcoord : ∀ s : S, b.repr (s • ω₀) 0 = s := by
    intro s
    rw [map_smul, hω₀, b.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_eq_same]

  have hne : (1 : κ) ⊗ₜ[S] ω₀ ≠ (0 : κ ⊗[S] Ω[S⁄A]) := by
    intro h0
    let φ : κ ⊗[S] Ω[S⁄A] →ₗ[S] κ ⊗[S] S := LinearMap.lTensor κ (b.coord 0)
    have h1' : φ ((1 : κ) ⊗ₜ[S] ω₀) = (1 : κ) ⊗ₜ[S] (1 : S) := by
      simp only [φ, LinearMap.lTensor_tmul, Module.Basis.coord_apply, hω₀, b.repr_self,
        Finsupp.single_eq_same]
    have h2 : (TensorProduct.rid S κ) ((1 : κ) ⊗ₜ[S] (1 : S)) = 1 := by
      rw [TensorProduct.rid_tmul, one_smul]
    have h3 : (TensorProduct.rid S κ) (φ ((1 : κ) ⊗ₜ[S] ω₀)) = 0 := by rw [h0, map_zero, map_zero]
    rw [h1', h2] at h3
    exact one_ne_zero h3

  have hsurjκ : Function.Surjective (algebraMap S κ) := IsLocalRing.residue_surjective
  have hsurjAκ : Function.Surjective (algebraMap A κ) := hres
  haveI : Subsingleton (Ω[κ⁄A]) := KaehlerDifferential.subsingleton_of_surjective A κ hsurjAκ
  have hexact := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange A S κ hsurjκ
  obtain ⟨x, hx⟩ := (hexact ((1 : κ) ⊗ₜ[S] ω₀)).mp (Subsingleton.elim _ _)
  obtain ⟨⟨t, htker⟩, rfl⟩ := Ideal.toCotangent_surjective _ x
  rw [KaehlerDifferential.kerCotangentToTensor_toCotangent] at hx

  have htmax : t ∈ maximalIdeal S := by
    have h2 : algebraMap S κ t = 0 := htker
    have h3 : IsLocalRing.residue S t = 0 := h2
    exact (IsLocalRing.residue_eq_zero_iff t).mp h3

  set c : S := b.repr (KaehlerDifferential.D A S t) 0 with hc
  have hDt : KaehlerDifferential.D A S t = c • ω₀ := hrepr _
  have hmm : ∀ a : A, algebraMap A S a ∈ maximalIdeal S ↔ a ∈ maximalIdeal A := by
    intro a
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
      isUnit_map_iff]
  have hcunit : IsUnit c := by
    by_contra hcu
    have hcm : c ∈ maximalIdeal S := (IsLocalRing.mem_maximalIdeal _).mpr hcu
    have hres0 : IsLocalRing.residue S c = 0 := (IsLocalRing.residue_eq_zero_iff c).mpr hcm
    apply hne
    rw [← hx, hDt, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    change (IsLocalRing.residue S c) ⊗ₜ[S] ω₀ = 0
    rw [hres0, TensorProduct.zero_tmul]
  obtain ⟨cu, hcu⟩ := hcunit
  have hbasis : ∀ ω : Ω[S⁄A], ∃! s : S, ω = s • KaehlerDifferential.D A S t := by
    intro ω
    refine ⟨b.repr ω 0 * ↑cu⁻¹, ?_, ?_⟩
    · change ω = (b.repr ω 0 * ↑cu⁻¹) • KaehlerDifferential.D A S t
      rw [hDt, ← hcu, smul_smul, mul_assoc, Units.inv_mul, mul_one]
      exact hrepr ω
    · intro s hs
      have h2 : b.repr ω 0 = s * c := by
        rw [hs, hDt, smul_smul, hcoord]
      rw [h2, ← hcu, mul_assoc, Units.mul_inv, mul_one]

  obtain ⟨hφs, hφu⟩ :=
    Algebra.FormallySmooth.formallySmooth_and_formallyUnramified_aeval_of_existsUnique_smul_D_eq t hbasis
  refine ⟨t, htmax, hφs, hφu, ?_⟩

  letI algX : Algebra A[X] S := (Polynomial.aeval t : A[X] →ₐ[A] S).toRingHom.toAlgebra
  have halgX : ∀ p : A[X], algebraMap A[X] S p = aeval t p := fun _ => rfl
  haveI : IsScalarTower A A[X] S := IsScalarTower.of_algebraMap_eq fun a => by
    rw [halgX, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, aeval_C]
  haveI : Algebra.FormallyUnramified A[X] S := hφu
  set 𝔭 : Ideal A[X] := (maximalIdeal S).comap (algebraMap A[X] S) with h𝔭
  haveI h𝔭p : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  set R' := Localization.AtPrime 𝔭 with hR'
  have hunits : ∀ y : 𝔭.primeCompl, IsUnit (algebraMap A[X] S y) := by
    intro y
    have hy : (y : A[X]) ∉ (maximalIdeal S).comap (algebraMap A[X] S) := y.2
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hy
    exact hy
  let f' : R' →+* S := IsLocalization.lift (M := 𝔭.primeCompl) hunits
  have hf' : ∀ p : A[X], f' (algebraMap A[X] R' p) = algebraMap A[X] S p :=
    fun p => IsLocalization.lift_eq hunits p
  letI algR' : Algebra R' S := f'.toAlgebra
  haveI : IsScalarTower A[X] R' S := IsScalarTower.of_algebraMap_eq fun p => (hf' p).symm
  have h𝔭le : 𝔭.map (algebraMap A[X] S) ≤ maximalIdeal S := by rw [h𝔭]; exact Ideal.map_comap_le
  haveI : IsLocalHom (algebraMap R' S) := ⟨fun z hz => by
    by_contra hzu
    have hzm : z ∈ maximalIdeal R' := (IsLocalRing.mem_maximalIdeal _).mpr hzu
    rw [← Localization.AtPrime.map_eq_maximalIdeal] at hzm
    have h2 : algebraMap R' S z ∈ (𝔭.map (algebraMap A[X] R')).map (algebraMap R' S) :=
      Ideal.mem_map_of_mem _ hzm
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq] at h2
    exact (IsLocalRing.mem_maximalIdeal _).mp (h𝔭le h2) hz⟩
  haveI : Algebra.EssFiniteType A[X] S := Algebra.EssFiniteType.of_comp A A[X] S
  haveI : Algebra.EssFiniteType R' S := Algebra.EssFiniteType.of_comp A[X] R' S
  haveI : Algebra.FormallyUnramified R' S := Algebra.FormallyUnramified.of_restrictScalars A[X] R' S
  have hmapmax : (maximalIdeal R').map (algebraMap R' S) = maximalIdeal S :=
    Algebra.FormallyUnramified.map_maximalIdeal
  have h𝔭map : 𝔭.map (algebraMap A[X] S) = maximalIdeal S := by
    rw [← hmapmax, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
  have hdec : ∀ p : A[X], algebraMap A[X] S p = t * aeval t p.divX + algebraMap A S (p.coeff 0) := by
    intro p
    rw [halgX]
    conv_lhs => rw [← Polynomial.X_mul_divX_add p]
    rw [map_add, map_mul, aeval_X, aeval_C]
  apply le_antisymm
  · rw [← h𝔭map, Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap]
    have hpt : algebraMap A[X] S p ∈ maximalIdeal S := by
      have := hp; rwa [h𝔭, Ideal.mem_comap] at this
    have hp0 : p.coeff 0 ∈ maximalIdeal A := by
      rw [← hmm]
      have h3 : algebraMap A S (p.coeff 0) = algebraMap A[X] S p - t * aeval t p.divX := by
        rw [hdec]; ring
      rw [h3]
      exact Ideal.sub_mem _ hpt (Ideal.mul_mem_right _ _ htmax)
    rw [hdec]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton'.mpr ⟨aeval t p.divX, by ring⟩))
      (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hp0))
  · apply sup_le
    · rw [Ideal.span_singleton_le_iff_mem]; exact htmax
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, hmm]
      exact ha

end S_Algebra_FormallySmooth_exists_formallyUnramified_aeval_and_maximalIdeal_eq_of_finrank_kaehlerDifferential_eq_one
end P2MW
export P2MW.S_Algebra_FormallySmooth_exists_formallyUnramified_aeval_and_maximalIdeal_eq_of_finrank_kaehlerDifferential_eq_one (solution)
