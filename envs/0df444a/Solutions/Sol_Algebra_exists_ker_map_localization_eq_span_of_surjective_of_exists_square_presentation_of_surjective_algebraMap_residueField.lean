-- Prove2me | solution 1 for Algebra.exists_ker_map_localization_eq_span_of_surjective_of_exists_square_presentation_of_surjective_algebraMap_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/0851dc03-10ab-5782-ac37-bffe3f4c7336

import Mathlib
import Theorems.Thm_Algebra_exists_ker_eq_span_of_surjective_truncated_of_ker_eq_span
import Theorems.Thm_Ideal_map_algebraMap_localizationAtPrime_eq_span_of_le_span_sup_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_ker_map_localization_eq_span_of_surjective_of_exists_square_presentation_of_surjective_algebraMap_residueField

set_option autoImplicit false

universe u

namespace PresIndep

open MvPolynomial

variable (k : Type u) [Field k]

section Translate
variable (n : ℕ) (a : Fin n → k)

noncomputable def transl : MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin n) k :=
  AlgEquiv.ofAlgHom (aeval fun j => X j + C (a j)) (aeval fun j => X j - C (a j))
    (by ext j; simp) (by ext j; simp)

@[scoped simp] theorem transl_X (j : Fin n) : transl k n a (X j) = X j + C (a j) := by
  simp [transl]

end Translate

theorem ker_constantCoeff_eq_span (n : ℕ) :
    RingHom.ker (constantCoeff : MvPolynomial (Fin n) k →+* k) = Ideal.span (Set.range (X : Fin n → _)) := by
  ext f
  rw [RingHom.mem_ker, ← Set.image_univ, mem_ideal_span_X_image, constantCoeff_eq, ← notMem_support_iff]
  constructor
  · intro h m hm
    by_contra hne
    push Not at hne
    have : m = 0 := Finsupp.ext fun i => by simpa using hne i (Set.mem_univ i)
    exact h (this ▸ hm)
  · intro h h0
    obtain ⟨i, -, hi⟩ := h 0 h0
    exact hi rfl

theorem eq_comap_maximalIdeal {A C : Type*} [CommRing A] [CommRing C] [IsLocalRing C]
    (ψ : A →+* C) (hψ : Function.Surjective ψ) (𝔫 : Ideal A) [h𝔫 : 𝔫.IsMaximal] (hker : RingHom.ker ψ ≤ 𝔫) :
    𝔫 = (IsLocalRing.maximalIdeal C).comap ψ := by
  refine (h𝔫.eq_of_le (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal C).ne_top) ?_)
  intro x hx
  rw [Ideal.mem_comap]
  by_contra hunit
  have hu : IsUnit (ψ x) := by
    simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hunit
  obtain ⟨y, hy⟩ := hψ (hu.unit⁻¹ : Cˣ)
  have h1 : 1 - y * x ∈ RingHom.ker ψ := by
    rw [RingHom.mem_ker, map_sub, map_one, map_mul, hy, IsUnit.val_inv_mul, sub_self]
  have : (1 : A) ∈ 𝔫 := by
    have h2 := 𝔫.add_mem (hker h1) (𝔫.mul_mem_left y hx)
    rwa [sub_add_cancel] at h2
  exact h𝔫.ne_top ((Ideal.eq_top_iff_one _).mpr this)

section Trunc

variable {C : Type u} [CommRing C] [Algebra k C] [IsLocalRing C]

theorem exists_add_algebraMap_mem (hres : Function.Surjective (algebraMap k (IsLocalRing.ResidueField C))) (c : C) : ∃ a : k, c + algebraMap k C a ∈ IsLocalRing.maximalIdeal C := by
  obtain ⟨b, hb⟩ := hres (IsLocalRing.residue C c)
  refine ⟨-b, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff]
  simp only [map_add, map_neg]
  have : IsLocalRing.residue C (algebraMap k C b) = algebraMap k (IsLocalRing.ResidueField C) b :=
    (IsScalarTower.algebraMap_apply k C (IsLocalRing.ResidueField C) b).symm
  rw [this, hb, add_neg_cancel]

variable {n : ℕ} (φ : MvPolynomial (Fin n) k →ₐ[k] C)

theorem exists_transl_X_mem (hres : Function.Surjective (algebraMap k (IsLocalRing.ResidueField C))) :
    ∃ a : Fin n → k, ∀ j, (φ.comp (transl k n a).toAlgHom) (X j) ∈ IsLocalRing.maximalIdeal C := by
  choose a ha using fun j => exists_add_algebraMap_mem k hres (φ (X j))
  exact ⟨a, fun j => by simpa [AlgHom.commutes] using ha j⟩

theorem pow_ker_constantCoeff_le_ker (M : ℕ) (hM : IsLocalRing.maximalIdeal C ^ M = ⊥)
    (hX : ∀ j, φ (X j) ∈ IsLocalRing.maximalIdeal C) :
    RingHom.ker (constantCoeff : MvPolynomial (Fin n) k →+* k) ^ M ≤ RingHom.ker φ := by
  have h1 : (RingHom.ker (constantCoeff : MvPolynomial (Fin n) k →+* k)).map φ ≤ IsLocalRing.maximalIdeal C := by
    rw [ker_constantCoeff_eq_span, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact hX j
  intro x hx
  rw [RingHom.mem_ker, ← Ideal.mem_bot, ← hM]
  have : φ x ∈ ((RingHom.ker (constantCoeff : MvPolynomial (Fin n) k →+* k)) ^ M).map φ := Ideal.mem_map_of_mem _ hx
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono h1 M this

end Trunc

end PresIndep
p2m_reactivate "P2MW.S_Algebra_exists_ker_map_localization_eq_span_of_surjective_of_exists_square_presentation_of_surjective_algebraMap_residueField.PresIndep"

open PresIndep MvPolynomial in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (k : Type u) [Field k] (C : Type u) [CommRing C] [Algebra k C] [IsLocalRing C]
    (hres : Function.Surjective (algebraMap k (IsLocalRing.ResidueField C)))
    [Module.Finite k C]
    (hsq : ∃ (r : ℕ) (g : Fin r → MvPolynomial (Fin r) k),
      Nonempty (C ≃ₐ[k] (MvPolynomial (Fin r) k ⧸ Ideal.span (Set.range g))))
    (N : ℕ) (ψ : MvPolynomial (Fin N) k →ₐ[k] C) (hψ : Function.Surjective ψ)
    (𝔫 : Ideal (MvPolynomial (Fin N) k)) [𝔫.IsMaximal] (h𝔫 : RingHom.ker ψ ≤ 𝔫) :
    ∃ g : Fin N → Localization.AtPrime 𝔫, Ideal.map (algebraMap (MvPolynomial (Fin N) k) (Localization.AtPrime 𝔫)) (RingHom.ker ψ) = Ideal.span (Set.range g) := by
  classical

  haveI : IsArtinianRing C := IsArtinianRing.of_finite k C
  obtain ⟨M, hM⟩ : ∃ M : ℕ, IsLocalRing.maximalIdeal C ^ M = ⊥ := by
    obtain ⟨M, hM⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := C)
    exact ⟨M, by rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hM⟩

  let 𝔫₀ : ∀ n : ℕ, Ideal (MvPolynomial (Fin n) k) := fun n => RingHom.ker (constantCoeff : MvPolynomial (Fin n) k →+* k)
  have h01 : ∀ n : ℕ, 𝔫₀ n ^ (M + 1) ≤ 𝔫₀ n ^ M := fun n => Ideal.pow_le_pow_right (Nat.le_succ M)

  obtain ⟨r, gsq, ⟨esq⟩⟩ := hsq
  let β₀ : MvPolynomial (Fin r) k →ₐ[k] C := esq.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k (Ideal.span (Set.range gsq)))
  have hβ₀s : Function.Surjective β₀ := esq.symm.surjective.comp (Ideal.Quotient.mkₐ_surjective k _)
  have hkerβ₀ : RingHom.ker β₀ = Ideal.span (Set.range gsq) := by
    ext x
    rw [RingHom.mem_ker, show β₀ x = esq.symm (Ideal.Quotient.mk _ x) from rfl, map_eq_zero_iff _ esq.symm.injective,
      Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨b, hb⟩ := exists_transl_X_mem k β₀ hres
  let β₁ : MvPolynomial (Fin r) k →ₐ[k] C := β₀.comp (transl k r b).toAlgHom
  have hβ₁s : Function.Surjective β₁ := hβ₀s.comp (transl k r b).surjective
  have hkerβ₁ : RingHom.ker β₁ = Ideal.span (Set.range fun i => (transl k r b).symm (gsq i)) := by
    have h1 : RingHom.ker β₁ = (RingHom.ker β₀).comap (transl k r b).toRingEquiv := by
      ext x; simp [β₁, RingHom.mem_ker, Ideal.mem_comap]
    rw [h1, hkerβ₀, ← Ideal.map_symm, Ideal.map_span, ← Set.range_comp]
    rfl
  have hβ₁pow : 𝔫₀ r ^ (M + 1) ≤ RingHom.ker β₁ :=
    (h01 r).trans (pow_ker_constantCoeff_le_ker k β₁ M hM hb)
  let β : (MvPolynomial (Fin r) k ⧸ 𝔫₀ r ^ (M + 1)) →ₐ[k] C :=
    Ideal.Quotient.liftₐ (𝔫₀ r ^ (M + 1)) β₁ (fun x hx => hβ₁pow hx)
  have hβs : Function.Surjective β := by
    intro c; obtain ⟨x, rfl⟩ := hβ₁s c; exact ⟨Ideal.Quotient.mk _ x, rfl⟩
  have hkerβ : RingHom.ker β = Ideal.span (Set.range fun i => Ideal.Quotient.mk (𝔫₀ r ^ (M + 1)) ((transl k r b).symm (gsq i))) := by
    rw [show RingHom.ker β = (RingHom.ker β₁).map (Ideal.Quotient.mk (𝔫₀ r ^ (M + 1))) from
      Ideal.ker_quotient_lift _ _, hkerβ₁, Ideal.map_span, ← Set.range_comp]
    rfl

  obtain ⟨a, ha⟩ := exists_transl_X_mem k ψ hres
  let ψ₁ : MvPolynomial (Fin N) k →ₐ[k] C := ψ.comp (transl k N a).toAlgHom
  have hψ₁s : Function.Surjective ψ₁ := hψ.comp (transl k N a).surjective
  have hψ₁M : 𝔫₀ N ^ M ≤ RingHom.ker ψ₁ := pow_ker_constantCoeff_le_ker k ψ₁ M hM ha
  have hψ₁pow : 𝔫₀ N ^ (M + 1) ≤ RingHom.ker ψ₁ := (h01 N).trans hψ₁M
  let α : (MvPolynomial (Fin N) k ⧸ 𝔫₀ N ^ (M + 1)) →ₐ[k] C :=
    Ideal.Quotient.liftₐ (𝔫₀ N ^ (M + 1)) ψ₁ (fun x hx => hψ₁pow hx)
  have hαs : Function.Surjective α := by
    intro c; obtain ⟨x, rfl⟩ := hψ₁s c; exact ⟨Ideal.Quotient.mk _ x, rfl⟩

  obtain ⟨hbar, hker_α⟩ := Algebra.exists_ker_eq_span_of_surjective_truncated_of_ker_eq_span k C M r β hβs _ hkerβ N α hαs

  have hkerα : RingHom.ker α = (RingHom.ker ψ₁).map (Ideal.Quotient.mk (𝔫₀ N ^ (M + 1))) :=
    Ideal.ker_quotient_lift _ _
  have hlift : ∀ i, ∃ y ∈ RingHom.ker ψ₁, Ideal.Quotient.mk (𝔫₀ N ^ (M + 1)) y = hbar i := fun i => by
    have : hbar i ∈ RingHom.ker α := hker_α ▸ Ideal.subset_span (Set.mem_range_self i)
    rw [hkerα] at this
    exact (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp this
  choose h₁ hh₁ hh₁' using hlift
  have hle₁ : RingHom.ker ψ₁ ≤ Ideal.span (Set.range h₁) ⊔ 𝔫₀ N * RingHom.ker ψ₁ := by
    intro x hx
    have hx' : Ideal.Quotient.mk (𝔫₀ N ^ (M + 1)) x ∈ (Ideal.span (Set.range h₁)).map (Ideal.Quotient.mk (𝔫₀ N ^ (M + 1))) := by
      rw [Ideal.map_span, ← Set.range_comp, show (⇑(Ideal.Quotient.mk (𝔫₀ N ^ (M + 1))) ∘ h₁) = hbar from funext hh₁',
        ← hker_α, RingHom.mem_ker]
      exact hx
    obtain ⟨y, hy, hyx⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hx'
    have hxy : x - y ∈ 𝔫₀ N ^ (M + 1) := by
      rw [← Ideal.Quotient.eq, hyx]
    have : x = y + (x - y) := by ring
    rw [this]
    refine Ideal.add_mem _ (Ideal.mem_sup_left hy) (Ideal.mem_sup_right ?_)
    rw [pow_succ'] at hxy
    exact Ideal.mul_mono_right hψ₁M hxy

  have hkerψ : RingHom.ker ψ = (RingHom.ker ψ₁).map (transl k N a).toAlgHom := by
    have h1 : RingHom.ker ψ₁ = (RingHom.ker ψ).comap (transl k N a).toAlgHom := by
      ext x; simp [ψ₁, RingHom.mem_ker, Ideal.mem_comap]
    rw [h1]
    exact (Ideal.map_comap_of_surjective (transl k N a).toAlgHom (transl k N a).surjective _).symm
  let h : Fin N → MvPolynomial (Fin N) k := fun i => transl k N a (h₁ i)
  have hh : ∀ i, h i ∈ RingHom.ker ψ := fun i => by
    rw [hkerψ]; exact Ideal.mem_map_of_mem _ (hh₁ i)
  have h𝔫eq : 𝔫 = (IsLocalRing.maximalIdeal C).comap ψ := eq_comap_maximalIdeal (ψ : _ →+* C) hψ 𝔫 h𝔫
  have h𝔫₀le : (𝔫₀ N).map (transl k N a).toAlgHom ≤ 𝔫 := by
    change (RingHom.ker (constantCoeff : MvPolynomial (Fin N) k →+* k)).map _ ≤ _
    rw [h𝔫eq, ker_constantCoeff_eq_span, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap]
    exact ha j
  have hle : RingHom.ker ψ ≤ Ideal.span (Set.range h) ⊔ 𝔫 * RingHom.ker ψ := by
    rw [hkerψ]
    refine (Ideal.map_mono hle₁).trans ?_
    rw [Ideal.map_sup, Ideal.map_mul, Ideal.map_span, ← Set.range_comp]
    exact sup_le_sup_left (Ideal.mul_mono_left h𝔫₀le) _

  exact ⟨fun i => algebraMap _ _ (h i),
    Ideal.map_algebraMap_localizationAtPrime_eq_span_of_le_span_sup_mul (RingHom.ker ψ) 𝔫 h hh hle⟩

end S_Algebra_exists_ker_map_localization_eq_span_of_surjective_of_exists_square_presentation_of_surjective_algebraMap_residueField
end P2MW
export P2MW.S_Algebra_exists_ker_map_localization_eq_span_of_surjective_of_exists_square_presentation_of_surjective_algebraMap_residueField (solution)
