-- Prove2me | solution 1 for Algebra.exists_cyclotomic_galois_cover_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/6bb7938c-6792-5ea4-8f3c-784dc41028d3

import Mathlib
import Theorems.Thm_AdjoinRoot_isUnit_one_sub_root_pow_of_isUnit_of_not_dvd
import Theorems.Thm_AdjoinRoot_finite_free_faithfullyFlat_etale_cyclotomic_of_isUnit
import Theorems.Thm_AdjoinRoot_exists_monoidHom_algEquiv_bijective_tensorProduct_cyclotomic_of_isUnit
import Theorems.Thm_Algebra_exists_span_eq_top_forall_exists_algebraMap_comp_eq_comp_of_bijective_tensorProduct
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_cyclotomic_galois_cover_of_isUnit

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

theorem solution
    (𝒪 : Type) [CommRing 𝒪] (m : ℕ) (hm : 0 < m) (hmu : IsUnit ((m : ℕ) : 𝒪)) :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : Algebra 𝒪 𝒪'),
      Module.Finite 𝒪 𝒪' ∧ Module.Free 𝒪 𝒪' ∧ Module.FaithfullyFlat 𝒪 𝒪' ∧
      (∃ ζ : 𝒪', ζ ^ m = 1 ∧ ∀ j : ℕ, 0 < j → j < m → IsUnit (1 - ζ ^ j)) ∧
      (∀ (S : Type) [CommRing S] [Algebra 𝒪 S], Module.FaithfullyFlat S (S ⊗[𝒪] 𝒪') ∧ Algebra.Etale S (S ⊗[𝒪] 𝒪')) ∧
      ∃ (G : Type) (_ : Group G) (_ : Finite G) (τ : G →* (𝒪' ≃ₐ[𝒪] 𝒪')),
        (Function.Bijective fun x : 𝒪' ⊗[𝒪] 𝒪' => fun σ : G =>
          Algebra.TensorProduct.lmul' (S := 𝒪') 𝒪
            (Algebra.TensorProduct.map (AlgHom.id 𝒪 𝒪') ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →ₐ[𝒪] 𝒪') x)) ∧
        (∀ (S : Type) [CommRing S] (s₁ s₂ : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪')),
          s₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 𝒪')) = s₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 𝒪')) →
          ∃ (k : ℕ) (r : Fin k → S), Ideal.span (Set.range r) = ⊤ ∧ ∀ i : Fin k, ∃ σ : G,
            Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) ≫ s₂ =
              Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) ≫ s₁ ≫
                Spec.map (CommRingCat.ofHom ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪'))) := by
  classical
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨hfin, hfree, hff, het, -⟩ := AdjoinRoot.finite_free_faithfullyFlat_etale_cyclotomic_of_isUnit 𝒪 m hmu
  obtain ⟨τ, hτ, hbij⟩ := AdjoinRoot.exists_monoidHom_algEquiv_bijective_tensorProduct_cyclotomic_of_isUnit 𝒪 m hmu
  haveI := hff
  haveI := het
  haveI := hfree
  have hroot : AdjoinRoot.root (cyclotomic m 𝒪) ^ m = 1 := by
    have h : AdjoinRoot.mk (cyclotomic m 𝒪) (X ^ m - 1) = 0 :=
      AdjoinRoot.mk_eq_zero.mpr (cyclotomic.dvd_X_pow_sub_one m 𝒪)
    rwa [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h
  refine ⟨AdjoinRoot (cyclotomic m 𝒪), inferInstance, inferInstance, hfin, hfree, hff,
    ⟨AdjoinRoot.root (cyclotomic m 𝒪), hroot, fun j hj0 hjm =>
      AdjoinRoot.isUnit_one_sub_root_pow_of_isUnit_of_not_dvd 𝒪 m hmu j
        (fun h => absurd (Nat.le_of_dvd hj0 h) (not_le.mpr hjm))⟩,
    fun S _ _ => ⟨inferInstance, inferInstance⟩,
    (ZMod m)ˣ, inferInstance, inferInstance, τ, hbij, ?_⟩
  intro S _ s₁ s₂ hs

  set p₁ := Spec.preimage s₁ with hp₁
  set p₂ := Spec.preimage s₂ with hp₂
  have hs₁ : Spec.map p₁ = s₁ := Spec.map_preimage s₁
  have hs₂ : Spec.map p₂ = s₂ := Spec.map_preimage s₂
  have hagree : p₁.hom.comp (algebraMap 𝒪 (AdjoinRoot (cyclotomic m 𝒪))) =
      p₂.hom.comp (algebraMap 𝒪 (AdjoinRoot (cyclotomic m 𝒪))) := by
    rw [← hs₁, ← hs₂, ← Spec.map_comp, ← Spec.map_comp] at hs
    have := Spec.map_injective hs
    have := congrArg CommRingCat.Hom.hom this
    simpa [CommRingCat.hom_comp, CommRingCat.hom_ofHom] using this
  obtain ⟨k, r, hr, hloc⟩ :=
    Algebra.exists_span_eq_top_forall_exists_algebraMap_comp_eq_comp_of_bijective_tensorProduct
      𝒪 (AdjoinRoot (cyclotomic m 𝒪)) (ZMod m)ˣ τ hbij S p₁.hom p₂.hom hagree
  refine ⟨k, r, hr, fun i => ?_⟩
  obtain ⟨σ, hσ⟩ := hloc i
  refine ⟨σ, ?_⟩
  rw [← hs₁, ← hs₂, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_assoc]
  exact hσ

end S_Algebra_exists_cyclotomic_galois_cover_of_isUnit
end P2MW
export P2MW.S_Algebra_exists_cyclotomic_galois_cover_of_isUnit (solution)
