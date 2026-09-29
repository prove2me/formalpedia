-- Prove2me | solution 1 for ArtinL.Abelian.exists_inertia_pow_eq_map_conj_ramificationGroup_of_under_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/c0db8794-78c2-5cd8-9c6b-ebe47cef77d7

import Mathlib
import Definitions.Def_ArtinL_Abelian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_Abelian_exists_inertia_pow_eq_map_conj_ramificationGroup_of_under_eq

set_option autoImplicit false

open NumberField IsDedekindDomain

universe u v

open scoped Pointwise

theorem solution
    (K : Type u) (M : Type v) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (v : HeightOneSpectrum (𝓞 K))
    (Q : Ideal (𝓞 M)) [Q.IsMaximal] (hQ : Q.under (𝓞 K) = v.asIdeal) :
    ∃ τ : M ≃ₐ[K] M,
      (∀ x : 𝓞 M, x ∈ LanglandsTunnell.P2.Artin.primeAbove K M v ↔ τ • x ∈ Q) ∧
      ∀ i : ℕ,
        (Q ^ (i + 1)).inertia (M ≃ₐ[K] M) = (ArtinL.Abelian.ramificationGroup K M v i).map (MulAut.conj τ).toMonoidHom ∧
        Nat.card ((Q ^ (i + 1)).inertia (M ≃ₐ[K] M)) = Nat.card (ArtinL.Abelian.ramificationGroup K M v i) ∧
        ∀ {A : Type*} [CommGroup A] (ψ : (M ≃ₐ[K] M) →* A),
          (∀ σ ∈ (Q ^ (i + 1)).inertia (M ≃ₐ[K] M), ψ σ = 1) ↔
            ∀ σ ∈ ArtinL.Abelian.ramificationGroup K M v i, ψ σ = 1 := by
  classical
  haveI : (LanglandsTunnell.P2.Artin.primeAbove K M v).IsMaximal := LanglandsTunnell.P2.Artin.primeAbove_isMaximal K M v
  obtain ⟨τ, hτ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 M) (M ≃ₐ[K] M)
    (LanglandsTunnell.P2.Artin.primeAbove K M v) Q (by rw [LanglandsTunnell.P2.Artin.under_primeAbove, hQ])

  have mem_inertia : ∀ (J : Ideal (𝓞 M)) (σ : M ≃ₐ[K] M), σ ∈ J.inertia (M ≃ₐ[K] M) ↔ ∀ x : 𝓞 M, σ • x - x ∈ J :=
    fun J σ => Iff.rfl

  have hconj : ∀ J : Ideal (𝓞 M), (τ • J).inertia (M ≃ₐ[K] M) = (J.inertia (M ≃ₐ[K] M)).map (MulAut.conj τ).toMonoidHom := by
    intro J
    ext σ
    rw [mem_inertia, Subgroup.mem_map]
    constructor
    · intro h
      refine ⟨τ⁻¹ * σ * τ, (mem_inertia J _).2 fun y => ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      have hy := h (τ • y)
      rw [← Ideal.smul_mem_pointwise_smul_iff (a := τ), smul_sub, ← mul_smul]
      have e : τ * (τ⁻¹ * σ * τ) = σ * τ := by group
      rwa [e, mul_smul]
    · rintro ⟨ρ, hρ, rfl⟩ x
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hx := (mem_inertia J ρ).1 hρ (τ⁻¹ • x)
      rw [← Ideal.smul_mem_pointwise_smul_iff (a := τ), smul_sub, ← mul_smul, ← mul_smul, smul_inv_smul] at hx
      exact hx
  refine ⟨τ, fun x => ?_, fun i => ?_⟩
  · rw [hτ]
    exact Ideal.smul_mem_pointwise_smul_iff.symm
  · have hmap : (Q ^ (i + 1)).inertia (M ≃ₐ[K] M) =
        (ArtinL.Abelian.ramificationGroup K M v i).map (MulAut.conj τ).toMonoidHom := by
      rw [hτ, ← smul_pow', ArtinL.Abelian.ramificationGroup]
      exact hconj _
    refine ⟨hmap, ?_, ?_⟩
    · rw [hmap]
      exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj τ).injective).toEquiv).symm
    · intro A _ ψ
      rw [hmap]
      constructor
      · intro h σ hσ
        have := h (τ * σ * τ⁻¹) ⟨σ, hσ, rfl⟩
        rwa [map_mul, map_mul, map_inv, mul_comm (ψ τ), mul_assoc, mul_inv_cancel, mul_one] at this
      · rintro h _ ⟨σ, hσ, rfl⟩
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv, h σ hσ, mul_one, mul_inv_cancel]

end S_ArtinL_Abelian_exists_inertia_pow_eq_map_conj_ramificationGroup_of_under_eq
end P2MW
export P2MW.S_ArtinL_Abelian_exists_inertia_pow_eq_map_conj_ramificationGroup_of_under_eq (solution)
