-- Prove2me | solution 1 for ArtinL.eulerFactorAt_eq_eulerFactor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ecc423be-ca9d-52db-b154-70285bd2cd31

import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import Theorems.Thm_ValuationSubring_exists_algEquiv_smul_eq_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_eulerFactorAt_eq_eulerFactor

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups Pointwise
open Polynomial

namespace ArtinLEFwd

section Places

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem mem_decompositionSubgroup_iff (A : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    σ ∈ A.decompositionSubgroup K ↔ σ • A = A := MulAction.mem_stabilizer_iff

@[scoped simp] theorem coe_decomp_smul (A : ValuationSubring L) (d : A.decompositionSubgroup K) (a : A) :
    ((d • a : A) : L) = (d : L ≃ₐ[K] L) a := rfl

theorem residue_eq_iff (A : ValuationSubring L) (a b : A) :
    IsLocalRing.residue A a = IsLocalRing.residue A b ↔ ((a : L) - b) ∈ A.nonunits := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

theorem isFrobeniusAt_iff (A : ValuationSubring L) (σ : L ≃ₐ[K] L) (q : ℕ) :
    A.IsFrobeniusAt σ q ↔ σ • A = A ∧ ∀ a ∈ A, σ a - a ^ q ∈ A.nonunits := by
  constructor
  · rintro ⟨hσ, h⟩
    refine ⟨(mem_decompositionSubgroup_iff A σ).1 hσ, fun a ha => ?_⟩
    have h1 := h (IsLocalRing.residue A ⟨a, ha⟩)
    rw [← IsLocalRing.ResidueField.residue_smul, ← map_pow, residue_eq_iff] at h1
    simpa using h1
  · rintro ⟨hσ, h⟩
    refine ⟨(mem_decompositionSubgroup_iff A σ).2 hσ, fun x => ?_⟩
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    rw [← IsLocalRing.ResidueField.residue_smul, ← map_pow, residue_eq_iff]
    simpa using h a a.2

theorem mem_inertiaSubgroupIn_iff (A : ValuationSubring L) (τ : L ≃ₐ[K] L) :
    τ ∈ A.inertiaSubgroupIn K ↔ τ • A = A ∧ ∀ a ∈ A, τ a - a ∈ A.nonunits := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨(mem_decompositionSubgroup_iff A _).1 d.2, fun a ha => ?_⟩
    have hker : ∀ x : IsLocalRing.ResidueField A, d • x = x := fun x => by
      have := RingEquiv.congr_fun (MonoidHom.mem_ker.1 hd) x
      simpa using this
    have h1 := hker (IsLocalRing.residue A ⟨a, ha⟩)
    rw [← IsLocalRing.ResidueField.residue_smul, residue_eq_iff] at h1
    simpa using h1
  · rintro ⟨hτ, h⟩
    have hτ' : τ ∈ A.decompositionSubgroup K := (mem_decompositionSubgroup_iff A τ).2 hτ
    refine ⟨⟨τ, hτ'⟩, ?_, rfl⟩
    simp only [ValuationSubring.inertiaSubgroup, SetLike.mem_coe, MonoidHom.mem_ker]
    ext x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    change (⟨τ, hτ'⟩ : A.decompositionSubgroup K) • IsLocalRing.residue A a = IsLocalRing.residue A a
    rw [← IsLocalRing.ResidueField.residue_smul, residue_eq_iff]
    simpa using h a a.2

theorem mem_smul_iff (g : L ≃ₐ[K] L) (A : ValuationSubring L) (x : L) :
    x ∈ g • A ↔ g⁻¹ x ∈ A :=
  ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem

theorem mem_nonunits_smul_iff (g : L ≃ₐ[K] L) (A : ValuationSubring L) (x : L) :
    x ∈ (g • A).nonunits ↔ g⁻¹ x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    mem_smul_iff, map_inv₀, EmbeddingLike.map_eq_zero_iff]

theorem apply_mem_nonunits (A : ValuationSubring L) {σ : L ≃ₐ[K] L} (hσ : σ • A = A) {x : L}
    (hx : x ∈ A.nonunits) : σ x ∈ A.nonunits := by
  have : σ x ∈ (σ • A).nonunits := by
    rw [mem_nonunits_smul_iff]
    simpa [AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply] using hx
  rwa [hσ] at this

theorem sub_mem_nonunits (A : ValuationSubring L) {x y : L} (hx : x ∈ A.nonunits)
    (hy : y ∈ A.nonunits) : x - y ∈ A.nonunits := by
  have hx' := ValuationSubring.nonunits_subset hx
  have hy' := ValuationSubring.nonunits_subset hy
  have h1 : (⟨x, hx'⟩ : A) ∈ IsLocalRing.maximalIdeal A :=
    ValuationSubring.coe_mem_nonunits_iff.1 hx
  have h2 : (⟨y, hy'⟩ : A) ∈ IsLocalRing.maximalIdeal A :=
    ValuationSubring.coe_mem_nonunits_iff.1 hy
  have := Ideal.sub_mem _ h1 h2
  rw [← ValuationSubring.coe_mem_nonunits_iff] at this
  simpa using this

theorem isFrobeniusAt_conj {A : ValuationSubring L} {σ : L ≃ₐ[K] L} {q : ℕ}
    (h : A.IsFrobeniusAt σ q) (g : L ≃ₐ[K] L) :
    (g • A).IsFrobeniusAt (g * σ * g⁻¹) q := by
  rw [isFrobeniusAt_iff] at h ⊢
  obtain ⟨hσ, h⟩ := h
  refine ⟨by rw [mul_smul, mul_smul, inv_smul_smul, hσ], fun x hx => ?_⟩
  rw [mem_nonunits_smul_iff, map_sub, map_pow]
  have hx' : g⁻¹ x ∈ A := (mem_smul_iff g A x).1 hx
  have := h _ hx'
  simpa [AlgEquiv.aut_mul, AlgEquiv.aut_inv, AlgEquiv.mul_apply] using this

theorem conj_mem_inertiaSubgroupIn {A : ValuationSubring L} {τ : L ≃ₐ[K] L}
    (h : τ ∈ A.inertiaSubgroupIn K) (g : L ≃ₐ[K] L) :
    g * τ * g⁻¹ ∈ (g • A).inertiaSubgroupIn K := by
  rw [mem_inertiaSubgroupIn_iff] at h ⊢
  obtain ⟨hτ, h⟩ := h
  refine ⟨by rw [mul_smul, mul_smul, inv_smul_smul, hτ], fun x hx => ?_⟩
  rw [mem_nonunits_smul_iff, map_sub]
  have hx' : g⁻¹ x ∈ A := (mem_smul_iff g A x).1 hx
  have := h _ hx'
  simpa [AlgEquiv.aut_mul, AlgEquiv.aut_inv, AlgEquiv.mul_apply] using this

theorem inv_conj_mem_inertiaSubgroupIn {A : ValuationSubring L} {τ : L ≃ₐ[K] L} (g : L ≃ₐ[K] L)
    (h : τ ∈ (g • A).inertiaSubgroupIn K) : g⁻¹ * τ * g ∈ A.inertiaSubgroupIn K := by
  have := conj_mem_inertiaSubgroupIn h g⁻¹
  rwa [inv_smul_smul, inv_inv] at this

theorem inv_mul_mem_inertiaSubgroupIn {A : ValuationSubring L} {σ₀ σ₁ : L ≃ₐ[K] L} {q : ℕ}
    (h₀ : A.IsFrobeniusAt σ₀ q) (h₁ : A.IsFrobeniusAt σ₁ q) :
    σ₀⁻¹ * σ₁ ∈ A.inertiaSubgroupIn K := by
  rw [isFrobeniusAt_iff] at h₀ h₁
  rw [mem_inertiaSubgroupIn_iff]
  have hσ₀' : σ₀⁻¹ • A = A := by
    conv_lhs => rw [← h₀.1]
    rw [inv_smul_smul]
  refine ⟨by rw [mul_smul, h₁.1, hσ₀'], fun a ha => ?_⟩
  have hdiff : σ₁ a - σ₀ a ∈ A.nonunits := by
    have := sub_mem_nonunits A (h₁.2 a ha) (h₀.2 a ha)
    simpa using this
  have := apply_mem_nonunits A hσ₀' hdiff
  simpa [map_sub, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply] using this

end Places

section Rep

variable {n : ℕ}

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
local notation "ℚbar" => AlgebraicClosure ℚ

variable (ρ : Γℚ →* GL (Fin n) ℂ)

abbrev π : Representation ℂ Γℚ (Fin n → ℂ) := Deformation.matrixRepresentation ρ

theorem mem_invariantsUnder_iff (H : Subgroup Γℚ) (v : Fin n → ℂ) :
    v ∈ ArtinL.invariantsUnder ρ H ↔ ∀ τ ∈ H, π ρ τ v = v := by
  rw [ArtinL.invariantsUnder, Representation.mem_invariants]
  exact ⟨fun h τ hτ => h ⟨τ, hτ⟩, fun h τ => h τ τ.2⟩

theorem π_mul_apply (σ τ : Γℚ) (v : Fin n → ℂ) : π ρ (σ * τ) v = π ρ σ (π ρ τ v) := by
  rw [map_mul]; rfl

theorem apply_mem_inertiaInvariants_smul (A : ValuationSubring ℚbar) (g : Γℚ) {v : Fin n → ℂ}
    (hv : v ∈ ArtinL.inertiaInvariants ρ A) : π ρ g v ∈ ArtinL.inertiaInvariants ρ (g • A) := by
  rw [ArtinL.inertiaInvariants, mem_invariantsUnder_iff] at hv ⊢
  intro τ hτ
  have hτ' := inv_conj_mem_inertiaSubgroupIn g hτ
  have := hv _ hτ'
  calc π ρ τ (π ρ g v) = π ρ (g * (g⁻¹ * τ * g)) v := by
          rw [← π_mul_apply]; congr 1; group
    _ = π ρ g v := by rw [π_mul_apply, this]

theorem stable_of_smul_eq (A : ValuationSubring ℚbar) {σ : Γℚ} (hσ : σ • A = A) :
    ∀ v ∈ ArtinL.inertiaInvariants ρ A, π ρ σ v ∈ ArtinL.inertiaInvariants ρ A := by
  intro v hv
  have := apply_mem_inertiaInvariants_smul ρ A σ hv
  rwa [hσ] at this

theorem restrict_mul_of_mem_inertia (A : ValuationSubring ℚbar) {σ τ : Γℚ}
    (hτ : τ ∈ A.inertiaSubgroupIn ℚ)
    (h₁ : ∀ v ∈ ArtinL.inertiaInvariants ρ A, π ρ (σ * τ) v ∈ ArtinL.inertiaInvariants ρ A)
    (h₂ : ∀ v ∈ ArtinL.inertiaInvariants ρ A, π ρ σ v ∈ ArtinL.inertiaInvariants ρ A) :
    (π ρ (σ * τ)).restrict h₁ = (π ρ σ).restrict h₂ := by
  ext ⟨v, hv⟩
  have hfix : π ρ τ v = v := by
    rw [ArtinL.inertiaInvariants, mem_invariantsUnder_iff] at hv
    exact hv τ hτ
  simp only [LinearMap.coe_restrict_apply]
  rw [π_mul_apply, hfix]

theorem restrict_congr (A : ValuationSubring ℚbar) {σ σ' : Γℚ} (e : σ = σ')
    (h : ∀ v ∈ ArtinL.inertiaInvariants ρ A, π ρ σ v ∈ ArtinL.inertiaInvariants ρ A)
    (h' : ∀ v ∈ ArtinL.inertiaInvariants ρ A, π ρ σ' v ∈ ArtinL.inertiaInvariants ρ A) :
    (π ρ σ).restrict h = (π ρ σ').restrict h' := by
  subst e; rfl

def πEquiv (g : Γℚ) : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
  LinearEquiv.ofLinear (π ρ g) (π ρ g⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)

@[scoped simp] theorem πEquiv_apply (g : Γℚ) (v : Fin n → ℂ) : πEquiv ρ g v = π ρ g v := rfl

theorem map_inertiaInvariants (A : ValuationSubring ℚbar) (g : Γℚ) :
    (ArtinL.inertiaInvariants ρ A).map (πEquiv ρ g : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) =
      ArtinL.inertiaInvariants ρ (g • A) := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact apply_mem_inertiaInvariants_smul ρ A g hv
  · intro w hw
    refine ⟨π ρ g⁻¹ w, ?_, ?_⟩
    · have := apply_mem_inertiaInvariants_smul ρ (g • A) g⁻¹ hw
      rwa [inv_smul_smul] at this
    · change π ρ g (π ρ g⁻¹ w) = w
      rw [← π_mul_apply, mul_inv_cancel, map_one]; rfl

def invEquiv (A : ValuationSubring ℚbar) (g : Γℚ) :
    ArtinL.inertiaInvariants ρ A ≃ₗ[ℂ] ArtinL.inertiaInvariants ρ (g • A) :=
  LinearEquiv.ofSubmodules (πEquiv ρ g) _ _ (map_inertiaInvariants ρ A g)

@[scoped simp] theorem coe_invEquiv_apply (A : ValuationSubring ℚbar) (g : Γℚ)
    (v : ArtinL.inertiaInvariants ρ A) : ((invEquiv ρ A g v : ArtinL.inertiaInvariants ρ (g • A)) :
      Fin n → ℂ) = π ρ g v := rfl

theorem coe_invEquiv_symm_apply (A : ValuationSubring ℚbar) (g : Γℚ)
    (w : ArtinL.inertiaInvariants ρ (g • A)) :
    (((invEquiv ρ A g).symm w : ArtinL.inertiaInvariants ρ A) : Fin n → ℂ) = π ρ g⁻¹ w := rfl

theorem restrict_conj (A : ValuationSubring ℚbar) (g σ : Γℚ)
    (h : ∀ v ∈ ArtinL.inertiaInvariants ρ A, π ρ σ v ∈ ArtinL.inertiaInvariants ρ A)
    (h' : ∀ v ∈ ArtinL.inertiaInvariants ρ (g • A),
      π ρ (g * σ * g⁻¹) v ∈ ArtinL.inertiaInvariants ρ (g • A)) :
    (π ρ (g * σ * g⁻¹)).restrict h' = (invEquiv ρ A g).conj ((π ρ σ).restrict h) := by
  ext ⟨w, hw⟩
  rw [LinearEquiv.conj_apply]
  simp only [LinearMap.coe_restrict_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, coe_invEquiv_apply, coe_invEquiv_symm_apply]
  rw [π_mul_apply, π_mul_apply]

theorem eulerFactorAt_eq_of_stable (A : ValuationSubring ℚbar) (σ : Γℚ)
    (h : ∀ v ∈ ArtinL.inertiaInvariants ρ A, π ρ σ v ∈ ArtinL.inertiaInvariants ρ A) :
    ArtinL.eulerFactorAt ρ A σ = ArtinL.charpolyRev ((π ρ σ).restrict h) := by
  rw [ArtinL.eulerFactorAt, dif_pos h]

theorem eulerFactorAt_conj (A : ValuationSubring ℚbar) {σ : Γℚ} (hσ : σ • A = A) (g : Γℚ) :
    ArtinL.eulerFactorAt ρ (g • A) (g * σ * g⁻¹) = ArtinL.eulerFactorAt ρ A σ := by
  have h := stable_of_smul_eq ρ A hσ
  have hσ' : (g * σ * g⁻¹) • (g • A) = g • A := by
    rw [mul_smul, mul_smul, inv_smul_smul, hσ]
  have h' := stable_of_smul_eq ρ (g • A) hσ'
  rw [eulerFactorAt_eq_of_stable ρ A σ h, eulerFactorAt_eq_of_stable ρ (g • A) _ h',
    restrict_conj ρ A g σ h h', ArtinL.charpolyRev_conj]

theorem eulerFactorAt_eq_of_isFrobeniusAt (A : ValuationSubring ℚbar) {σ₀ σ₁ : Γℚ} {q : ℕ}
    (h₀ : A.IsFrobeniusAt σ₀ q) (h₁ : A.IsFrobeniusAt σ₁ q) :
    ArtinL.eulerFactorAt ρ A σ₁ = ArtinL.eulerFactorAt ρ A σ₀ := by
  have hτ := inv_mul_mem_inertiaSubgroupIn h₀ h₁
  have hσ₀ : σ₀ • A = A := ((isFrobeniusAt_iff A σ₀ q).1 h₀).1
  have hσ₁ : σ₁ • A = A := ((isFrobeniusAt_iff A σ₁ q).1 h₁).1
  have hs₀ := stable_of_smul_eq ρ A hσ₀
  have hs₁ := stable_of_smul_eq ρ A hσ₁
  have heq : σ₁ = σ₀ * (σ₀⁻¹ * σ₁) := by group
  have hs₁' : ∀ v ∈ ArtinL.inertiaInvariants ρ A,
      π ρ (σ₀ * (σ₀⁻¹ * σ₁)) v ∈ ArtinL.inertiaInvariants ρ A := by
    rw [← heq]; exact hs₁
  rw [eulerFactorAt_eq_of_stable ρ A σ₁ hs₁, eulerFactorAt_eq_of_stable ρ A σ₀ hs₀]
  rw [restrict_congr ρ A heq hs₁ hs₁', restrict_mul_of_mem_inertia ρ A hτ hs₁' hs₀]

end Rep

end ArtinLEFwd
p2m_reactivate "P2MW.S_ArtinL_eulerFactorAt_eq_eulerFactor.ArtinLEFwd"

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

open ArtinLEFwd in
theorem solution {n : ℕ} (ρ : Γℚ →* GL (Fin n) ℂ)
    {p : ℕ} (hp : p.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (σ : Γℚ) (hσ : A.IsFrobeniusAt σ p) :
    (∀ v ∈ ArtinL.inertiaInvariants ρ A,
        Deformation.matrixRepresentation ρ σ v ∈ ArtinL.inertiaInvariants ρ A) ∧
      ArtinL.eulerFactorAt ρ A σ = ArtinL.eulerFactor ρ p := by
  have hσA : σ • A = A := ((isFrobeniusAt_iff A σ p).1 hσ).1
  refine ⟨stable_of_smul_eq ρ A hσA, ?_⟩
  have hex : ∃ A' : ValuationSubring (AlgebraicClosure ℚ), ∃ σ' : Γℚ,
        A'.LiesOverPrime p ∧ A'.IsFrobeniusAt σ' p := ⟨A, σ, hA, hσ⟩
  rw [ArtinL.eulerFactor, dif_pos hex]
  have hA₀ : hex.choose.LiesOverPrime p := hex.choose_spec.choose_spec.1
  have hσ₀ : hex.choose.IsFrobeniusAt hex.choose_spec.choose p := hex.choose_spec.choose_spec.2
  obtain ⟨g, hg⟩ :=
    ValuationSubring.exists_algEquiv_smul_eq_of_liesOverPrime hp A hex.choose hA hA₀
  have hσ₁ : hex.choose.IsFrobeniusAt (g * σ * g⁻¹) p := by
    rw [← hg]; exact isFrobeniusAt_conj hσ g
  rw [← eulerFactorAt_eq_of_isFrobeniusAt ρ hex.choose hσ₀ hσ₁, ← hg,
    eulerFactorAt_conj ρ A hσA g]

end
p2m_reactivate "P2MW.S_ArtinL_eulerFactorAt_eq_eulerFactor.ArtinLEFwd"

end S_ArtinL_eulerFactorAt_eq_eulerFactor
end P2MW
export P2MW.S_ArtinL_eulerFactorAt_eq_eulerFactor (solution)
