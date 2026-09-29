-- Prove2me | solution 1 for ArtinL.Abelian.inv_card_inertia_mul_sum_induced_frob_pow_mul_eq_finsum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/f55d7952-0d8c-5000-8428-716517d0200d

import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import Definitions.Def_ArtinL_Abelian
import Theorems.Thm_ArtinL_Abelian_galois_primesOver_dictionary
import Theorems.Thm_ArtinL_Abelian_isUnramifiedAt_ofSubgroup_iff_and_localValue_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_Abelian_inv_card_inertia_mul_sum_induced_frob_pow_mul_eq_finsum

set_option autoImplicit false

open scoped MatrixGroups
open NumberField

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

open scoped Pointwise Classical
open IsDedekindDomain

namespace ArtinL
p2m_export "ArtinL" "Abelian.IsUnramifiedAt Abelian.localValue Abelian.ofSubgroup Abelian.galois_primesOver_dictionary Abelian.isUnramifiedAt_ofSubgroup_iff_and_localValue_eq"
namespace Abelian
p2m_export "ArtinL.Abelian" "IsUnramifiedAt localValue ofSubgroup galois_primesOver_dictionary isUnramifiedAt_ofSubgroup_iff_and_localValue_eq"
namespace C3
p2m_open "ArtinL.Abelian ArtinL"

open MulAction

section group
variable {G : Type*} [Group G] {R : Type*} [CommRing R] [MulSemiringAction G R]

theorem mem_inertia_smul_iff (g σ : G) (Q : Ideal R) : σ ∈ (g • Q).inertia G ↔ g⁻¹ * σ * g ∈ Q.inertia G := by
  constructor
  · intro h x
    have := h (g • x)
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub, inv_smul_smul, ← mul_smul,
      ← mul_smul] at this
    rw [Submodule.mem_toAddSubgroup]
    simpa [mul_assoc] using this
  · intro h x
    have := h (g⁻¹ • x)
    rw [Submodule.mem_toAddSubgroup] at this
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub, ← mul_smul]
    simpa [mul_smul, mul_assoc] using this

theorem mem_stabilizer_smul_iff (g σ : G) (Q : Ideal R) : σ ∈ stabilizer G (g • Q) ↔ g⁻¹ * σ * g ∈ stabilizer G Q := by
  rw [mem_stabilizer_iff, mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_eq_iff, smul_smul]

theorem conj_mem_inertia {Q : Ideal R} {d i : G} (hd : d ∈ stabilizer G Q) (hi : i ∈ Q.inertia G) :
    d * i * d⁻¹ ∈ Q.inertia G := by
  have h : d * i * d⁻¹ ∈ (d • Q).inertia G := by
    rw [mem_inertia_smul_iff, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc, inv_mul_cancel, mul_one]
    exact hi
  rwa [mem_stabilizer_iff.1 hd] at h

theorem inv_conj_mem_inertia {Q : Ideal R} {d i : G} (hd : d ∈ stabilizer G Q) (hi : i ∈ Q.inertia G) :
    d⁻¹ * i * d ∈ Q.inertia G := by
  have := conj_mem_inertia (Q := Q) ((stabilizer G Q).inv_mem hd) hi
  rwa [inv_inv] at this

theorem pow_inv_mul_pow_mem_inertia {Q : Ideal R} {a b : G} (hb : b ∈ stabilizer G Q) (h : a⁻¹ * b ∈ Q.inertia G) (k : ℕ) :
    (a ^ k)⁻¹ * b ^ k ∈ Q.inertia G := by
  have ha : a ∈ stabilizer G Q := by
    have : b * (a⁻¹ * b)⁻¹ ∈ stabilizer G Q := (stabilizer G Q).mul_mem hb ((stabilizer G Q).inv_mem (Ideal.inertia_le_stabilizer Q h))
    rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at this
  induction k with
  | zero => rw [pow_zero, pow_zero, inv_one, one_mul]; exact (Q.inertia G).one_mem
  | succ k ih =>

    have e : (a ^ (k + 1))⁻¹ * b ^ (k + 1) = (a⁻¹ * ((a ^ k)⁻¹ * b ^ k) * a) * (a⁻¹ * b) := by group
    rw [e]
    exact (Q.inertia G).mul_mem (inv_conj_mem_inertia ha ih) h

end group

section sums
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

theorem sum_smul_eq_card_stabilizer_smul_sum_image {X : Type*} [MulAction G X] [DecidableEq X] {M : Type*} [AddCommMonoid M]
    (a : X) (f : X → M) :
    ∑ x : G, f (x • a) = Fintype.card (stabilizer G a) • ∑ b ∈ Finset.univ.image (fun x : G => x • a), f b := by
  rw [Finset.smul_sum, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (g := fun x : G => x • a)
    (t := Finset.univ.image (fun x : G => x • a)) (fun x _ => Finset.mem_image_of_mem _ (Finset.mem_univ x))]
  refine Finset.sum_congr rfl fun b hb => ?_
  obtain ⟨x₀, -, rfl⟩ := Finset.mem_image.1 hb
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2]), Finset.sum_const]
  congr 1
  rw [← Fintype.card_coe]
  refine Fintype.card_congr (Equiv.ofBijective (fun x : {x // x ∈ Finset.univ.filter fun x : G => x • a = x₀ • a} =>
    (⟨x₀⁻¹ * (x : G), mem_stabilizer_iff.2 (by rw [mul_smul, (Finset.mem_filter.1 x.2).2, inv_smul_smul])⟩ : stabilizer G a)) ⟨?_, ?_⟩)
  · intro x y h
    have := congrArg (fun s : stabilizer G a => (s : G)) h
    exact Subtype.ext (mul_left_cancel this)
  · intro s
    refine ⟨⟨x₀ * (s : G), Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [mul_smul, mem_stabilizer_iff.1 s.2]⟩⟩, ?_⟩
    exact Subtype.ext (by simp)

theorem sum_dite_mem (I H : Subgroup G) (χ : H →* ℂˣ) :
    (∑ s : I, if hs : (s : G) ∈ H then ((χ ⟨s, hs⟩ : ℂˣ) : ℂ) else 0) =
      if ∀ (σ : G) (hσ : σ ∈ H), σ ∈ I → χ ⟨σ, hσ⟩ = 1 then (Fintype.card ↥(I ⊓ H) : ℂ) else 0 := by

  let ι : ↥(I ⊓ H) → I := fun u => ⟨u, u.2.1⟩
  have hι : Function.Injective ι := fun u u' h => Subtype.ext (congrArg (fun s : I => (s : G)) h)
  have e : (∑ s : I, if hs : (s : G) ∈ H then ((χ ⟨s, hs⟩ : ℂˣ) : ℂ) else 0) =
      ∑ u : ↥(I ⊓ H), ((χ ⟨u, u.2.2⟩ : ℂˣ) : ℂ) := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image ι)), Finset.sum_image (fun u _ u' _ h => hι h)]
    · exact Finset.sum_congr rfl fun u _ => dif_pos u.2.2
    · intro s _ hs
      rw [dif_neg]
      intro hsH
      exact hs (Finset.mem_image.2 ⟨⟨s, s.2, hsH⟩, Finset.mem_univ _, Subtype.ext rfl⟩)
  rw [e]
  let χ' : ↥(I ⊓ H) →* ℂˣ := χ.comp (Subgroup.inclusion inf_le_right)
  have hχ' : ∀ u : ↥(I ⊓ H), χ' u = χ ⟨u, u.2.2⟩ := fun u => rfl
  simp_rw [← hχ']
  split_ifs with htriv
  · rw [Finset.sum_congr rfl (fun u _ => by rw [hχ', htriv u u.2.2 u.2.1, Units.val_one]), Finset.sum_const, nsmul_eq_mul, mul_one]
    rfl
  · have h0 := sum_hom_units_eq_zero ((Units.coeHom ℂ).comp χ') (by
      intro h1
      apply htriv
      intro σ hσ hI
      have := congrArg (fun f : ↥(I ⊓ H) →* ℂ => f ⟨σ, hI, hσ⟩) h1
      simp only [MonoidHom.comp_apply, Units.coeHom_apply, MonoidHom.one_apply, hχ'] at this
      exact Units.val_eq_one.1 this)
    simpa using h0

theorem sum_coset_eq (I H : Subgroup G) (χ : H →* ℂˣ) (g τ₀ : G) (hτ₀ : τ₀ ∈ I) (h₀ : g * τ₀ ∈ H) :
    (∑ τ : I, if hx : g * (τ : G) ∈ H then ((χ ⟨g * τ, hx⟩ : ℂˣ) : ℂ) else 0) =
      (if ∀ (σ : G) (hσ : σ ∈ H), σ ∈ I → χ ⟨σ, hσ⟩ = 1 then (Fintype.card ↥(I ⊓ H) : ℂ) else 0) * ((χ ⟨g * τ₀, h₀⟩ : ℂˣ) : ℂ) := by

  rw [← sum_dite_mem I H χ, Finset.sum_mul]
  symm
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨τ₀, hτ₀⟩ : I)) _ _ fun s => ?_
  change (if hs : (s : G) ∈ H then ((χ ⟨s, hs⟩ : ℂˣ) : ℂ) else 0) * _ =
    if hx : g * (τ₀ * (s : G)) ∈ H then ((χ ⟨g * (τ₀ * s), hx⟩ : ℂˣ) : ℂ) else 0
  have key : (s : G) ∈ H ↔ g * (τ₀ * (s : G)) ∈ H := by
    rw [← mul_assoc]
    exact ⟨fun h => H.mul_mem h₀ h, fun h => by simpa [mul_assoc] using H.mul_mem (H.inv_mem h₀) h⟩
  by_cases hs : (s : G) ∈ H
  · rw [dif_pos hs, dif_pos (key.1 hs), mul_comm, ← Units.val_mul, ← map_mul]
    congr 2
    apply Subtype.ext
    change g * τ₀ * (s : G) = g * (τ₀ * s)
    rw [mul_assoc]
  · rw [dif_neg hs, dif_neg (fun h => hs (key.2 h)), zero_mul]

omit [DecidableEq G] in
theorem sum_coset_eq_zero (I H : Subgroup G) (χ : H →* ℂˣ) (g : G) (hne : ¬ ∃ τ : G, τ ∈ I ∧ g * τ ∈ H) :
    (∑ τ : I, if hx : g * (τ : G) ∈ H then ((χ ⟨g * τ, hx⟩ : ℂˣ) : ℂ) else 0) = 0 :=
  Finset.sum_eq_zero fun τ _ => dif_neg fun h => hne ⟨τ, τ.2, h⟩

end sums

end ArtinL.Abelian.C3

namespace ArtinL
p2m_export "ArtinL" "Abelian.IsUnramifiedAt Abelian.localValue Abelian.ofSubgroup Abelian.galois_primesOver_dictionary Abelian.isUnramifiedAt_ofSubgroup_iff_and_localValue_eq"
namespace Abelian
p2m_export "ArtinL.Abelian" "IsUnramifiedAt localValue ofSubgroup galois_primesOver_dictionary isUnramifiedAt_ofSubgroup_iff_and_localValue_eq"
namespace C3
p2m_open "ArtinL.Abelian ArtinL"

open MulAction

section frame
variable {G : Type*} [Group G] (H : Subgroup G) (χ : H →* ℂˣ)

noncomputable def chiZ (σ : G) : ℂ := if hσ : σ ∈ H then ((χ ⟨σ, hσ⟩ : ℂˣ) : ℂ) else 0

theorem chiZ_def (σ : G) : chiZ H χ σ = if hσ : σ ∈ H then ((χ ⟨σ, hσ⟩ : ℂˣ) : ℂ) else 0 := rfl

theorem chiZ_conj (h : G) (hh : h ∈ H) (σ : G) : chiZ H χ (h⁻¹ * σ * h) = chiZ H χ σ := by
  unfold chiZ
  have key : h⁻¹ * σ * h ∈ H ↔ σ ∈ H :=
    ⟨fun hx => by simpa [mul_assoc] using H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh),
     fun hx => H.mul_mem (H.mul_mem (H.inv_mem hh) hx) hh⟩
  by_cases hσ : σ ∈ H
  · rw [dif_pos hσ, dif_pos (key.2 hσ)]
    congr 1
    have : (⟨h⁻¹ * σ * h, key.2 hσ⟩ : H) = ⟨h, hh⟩⁻¹ * ⟨σ, hσ⟩ * ⟨h, hh⟩ := rfl
    rw [this, map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  · rw [dif_neg hσ, dif_neg (fun hx => hσ (key.1 hx))]

variable {R : Type*} [CommRing R] [MulSemiringAction G R]

theorem sum_inertia_mul_eq {M : Type*} [AddCommMonoid M] [Fintype G] (Q : Ideal R) (f : G → M) {g g' : G} (h : g⁻¹ * g' ∈ Q.inertia G) :
    (∑ τ : ↥(Q.inertia G), f (g * τ)) = ∑ τ : ↥(Q.inertia G), f (g' * τ) := by
  classical
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨g⁻¹ * g', h⟩ : ↥(Q.inertia G))).symm _ _ fun τ => ?_
  change f (g * τ) = f (g' * (((⟨g⁻¹ * g', h⟩ : ↥(Q.inertia G))⁻¹ * τ : ↥(Q.inertia G)) : G))
  congr 1
  change g * (τ : G) = g' * ((g⁻¹ * g')⁻¹ * τ)
  group

theorem sum_inertia_conj_eq {M : Type*} [AddCommMonoid M] [Fintype G] (Q : Ideal R) (f : G → M) {c : G} (hc : c ∈ stabilizer G Q) :
    (∑ τ : ↥(Q.inertia G), f (c⁻¹ * τ * c)) = ∑ τ : ↥(Q.inertia G), f τ := by
  classical
  exact Fintype.sum_equiv (Equiv.ofBijective (fun τ : ↥(Q.inertia G) => (⟨c⁻¹ * τ * c, inv_conj_mem_inertia hc τ.2⟩ : ↥(Q.inertia G)))
    ⟨fun a b hab => Subtype.ext (by simpa [mul_assoc] using congrArg (fun s : ↥(Q.inertia G) => c * (s : G) * c⁻¹) hab),
     fun s => ⟨⟨c * s * c⁻¹, conj_mem_inertia hc s.2⟩, Subtype.ext (by simp [mul_assoc])⟩⟩) _ _ fun τ => rfl

theorem sum_inertia_smul_eq {M : Type*} [AddCommMonoid M] [Fintype G] (Q : Ideal R) (f : G → M) (g : G) :
    (∑ τ : ↥(Q.inertia G), f (g⁻¹ * τ * g)) = ∑ τ : ↥((g⁻¹ • Q).inertia G), f τ := by
  classical
  refine Fintype.sum_equiv (Equiv.ofBijective (fun τ : ↥(Q.inertia G) => (⟨g⁻¹ * τ * g, (mem_inertia_smul_iff g⁻¹ _ Q).2 (by
      rw [inv_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_assoc, mul_inv_cancel, mul_one]; exact τ.2)⟩ : ↥((g⁻¹ • Q).inertia G)))
    ⟨fun a b hab => Subtype.ext (by simpa [mul_assoc] using congrArg (fun s : ↥((g⁻¹ • Q).inertia G) => g * (s : G) * g⁻¹) hab),
     fun s => ⟨⟨g * s * g⁻¹, by simpa [mul_assoc] using (mem_inertia_smul_iff g⁻¹ (s : G) Q).1 s.2⟩, Subtype.ext (by simp [mul_assoc])⟩⟩) _ _ fun τ => rfl

end frame

end ArtinL.Abelian.C3

namespace ArtinL
p2m_export "ArtinL" "Abelian.IsUnramifiedAt Abelian.localValue Abelian.ofSubgroup Abelian.galois_primesOver_dictionary Abelian.isUnramifiedAt_ofSubgroup_iff_and_localValue_eq"
namespace Abelian
p2m_export "ArtinL.Abelian" "IsUnramifiedAt localValue ofSubgroup galois_primesOver_dictionary isUnramifiedAt_ofSubgroup_iff_and_localValue_eq"
namespace C3
p2m_open "ArtinL.Abelian ArtinL"

open MulAction

theorem isMaximal_smul {R : Type*} [CommRing R] {G : Type*} [Group G] [MulSemiringAction G R] (g : G) (P : Ideal R)
    [hP : P.IsMaximal] : (g • P).IsMaximal := by
  rw [Ideal.pointwise_smul_eq_comap]
  exact Ideal.comap_isMaximal_of_surjective _ (RingEquiv.surjective _)

theorem card_inertia_smul {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G] [DecidableEq G] [MulSemiringAction G R]
    (g : G) (P : Ideal R) : Fintype.card ↥((g • P).inertia G) = Fintype.card ↥(P.inertia G) :=
  Fintype.card_congr (Equiv.ofBijective (fun τ : ↥((g • P).inertia G) => (⟨g⁻¹ * τ * g, (mem_inertia_smul_iff g τ P).1 τ.2⟩ : ↥(P.inertia G)))
    ⟨fun a b hab => Subtype.ext (by simpa [mul_assoc] using congrArg (fun s : ↥(P.inertia G) => g * (s : G) * g⁻¹) hab),
     fun s => ⟨⟨g * s * g⁻¹, (mem_inertia_smul_iff g _ P).2 (by simpa [mul_assoc] using s.2)⟩, Subtype.ext (by simp [mul_assoc])⟩⟩)

theorem card_stabilizer_smul {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G] [DecidableEq G] [MulSemiringAction G R]
    (g : G) (P : Ideal R) : Fintype.card ↥(stabilizer G (g • P)) = Fintype.card ↥(stabilizer G P) :=
  Fintype.card_congr (Equiv.ofBijective (fun τ : ↥(stabilizer G (g • P)) => (⟨g⁻¹ * τ * g, (mem_stabilizer_smul_iff g τ P).1 τ.2⟩ : ↥(stabilizer G P)))
    ⟨fun a b hab => Subtype.ext (by simpa [mul_assoc] using congrArg (fun s : ↥(stabilizer G P) => g * (s : G) * g⁻¹) hab),
     fun s => ⟨⟨g * s * g⁻¹, (mem_stabilizer_smul_iff g _ P).2 (by simpa [mul_assoc] using s.2)⟩, Subtype.ext (by simp [mul_assoc])⟩⟩)

theorem card_inf_stabilizer_smul {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G] [DecidableEq G] [MulSemiringAction G R]
    (H : Subgroup G) (h : G) (hh : h ∈ H) (P : Ideal R) :
    Fintype.card ↥(H ⊓ stabilizer G (h • P)) = Fintype.card ↥(H ⊓ stabilizer G P) :=
  Fintype.card_congr (Equiv.ofBijective
    (fun τ : ↥(H ⊓ stabilizer G (h • P)) => (⟨h⁻¹ * τ * h, H.mul_mem (H.mul_mem (H.inv_mem hh) τ.2.1) hh, (mem_stabilizer_smul_iff h τ P).1 τ.2.2⟩ : ↥(H ⊓ stabilizer G P)))
    ⟨fun a b hab => Subtype.ext (by simpa [mul_assoc] using congrArg (fun s : ↥(H ⊓ stabilizer G P) => h * (s : G) * h⁻¹) hab),
     fun s => ⟨⟨h * s * h⁻¹, H.mul_mem (H.mul_mem hh s.2.1) (H.inv_mem hh), (mem_stabilizer_smul_iff h _ P).2 (by simpa [mul_assoc] using s.2.2)⟩,
       Subtype.ext (by simp [mul_assoc])⟩⟩)

section main
variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F] (H : Subgroup (F ≃ₐ[ℚ] F)) (χ : H →* ℂˣ)
  {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 F)) [hPmax : P.IsMaximal] [hPover : P.LiesOver (Ideal.span {(p : ℤ)})] (j : ℕ)

noncomputable def inner (x : F ≃ₐ[ℚ] F) : ℂ :=
  ∑ τ : ↥(P.inertia (F ≃ₐ[ℚ] F)), chiZ H χ (x⁻¹ * (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P ^ j * τ) * x)

theorem conj_frob_pow_inv_mul_mem (d : F ≃ₐ[ℚ] F) (hd : d ∈ stabilizer (F ≃ₐ[ℚ] F) P) :
    ((d * arithFrobAt ℤ (F ≃ₐ[ℚ] F) P * d⁻¹) ^ j)⁻¹ * arithFrobAt ℤ (F ≃ₐ[ℚ] F) P ^ j ∈ P.inertia (F ≃ₐ[ℚ] F) := by
  have hφ : IsArithFrobAt ℤ (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P) P := IsArithFrobAt.arithFrobAt _ _ _
  have hψ : IsArithFrobAt ℤ (d * arithFrobAt ℤ (F ≃ₐ[ℚ] F) P * d⁻¹) P := by
    have := hφ.conj d
    rwa [mem_stabilizer_iff.1 hd] at this
  apply pow_inv_mul_pow_mem_inertia hφ.mem_stabilizer

  have h1 := IsArithFrobAt.mul_inv_mem_inertia hφ hψ
  have h2 := inv_conj_mem_inertia hψ.mem_stabilizer h1
  simpa [mul_assoc] using h2

theorem inner_mul_eq (x d h : F ≃ₐ[ℚ] F) (hd : d ∈ stabilizer (F ≃ₐ[ℚ] F) P) (hh : h ∈ H) :
    inner F H χ P j (d * x * h) = inner F H χ P j x := by
  unfold inner

  have e1 : ∀ τ : ↥(P.inertia (F ≃ₐ[ℚ] F)), chiZ H χ ((d * x * h)⁻¹ * (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P ^ j * τ) * (d * x * h)) =
      chiZ H χ (x⁻¹ * (d⁻¹ * (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P ^ j * τ) * d) * x) := by
    intro τ
    have e : (d * x * h)⁻¹ * (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P ^ j * τ) * (d * x * h) =
        h⁻¹ * (x⁻¹ * (d⁻¹ * (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P ^ j * τ) * d) * x) * h := by
      simp only [mul_inv_rev, mul_assoc]
    rw [e, chiZ_conj H χ h hh]
  simp_rw [e1]

  have e2 : ∀ τ : ↥(P.inertia (F ≃ₐ[ℚ] F)), x⁻¹ * (d⁻¹ * (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P ^ j * τ) * d) * x =
      x⁻¹ * ((d⁻¹ * arithFrobAt ℤ (F ≃ₐ[ℚ] F) P * d⁻¹⁻¹) ^ j * (d⁻¹ * τ * d)) * x := by
    intro τ; rw [conj_pow]; group
  simp_rw [e2]
  rw [sum_inertia_conj_eq P (fun σ => chiZ H χ (x⁻¹ * ((d⁻¹ * arithFrobAt ℤ (F ≃ₐ[ℚ] F) P * d⁻¹⁻¹) ^ j * σ) * x)) hd]

  exact sum_inertia_mul_eq P (fun σ => chiZ H χ (x⁻¹ * σ * x))
    (conj_frob_pow_inv_mul_mem F P j d⁻¹ ((stabilizer (F ≃ₐ[ℚ] F) P).inv_mem hd))

end main

end ArtinL.Abelian.C3

namespace ArtinL
p2m_export "ArtinL" "Abelian.IsUnramifiedAt Abelian.localValue Abelian.ofSubgroup Abelian.galois_primesOver_dictionary Abelian.isUnramifiedAt_ofSubgroup_iff_and_localValue_eq"
namespace Abelian
p2m_export "ArtinL.Abelian" "IsUnramifiedAt localValue ofSubgroup galois_primesOver_dictionary isUnramifiedAt_ofSubgroup_iff_and_localValue_eq"
namespace C3
p2m_open "ArtinL.Abelian ArtinL"

open MulAction

section main2
variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F] (H : Subgroup (F ≃ₐ[ℚ] F)) (χ : H →* ℂˣ)
  {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 F)) [hPmax : P.IsMaximal] [hPover : P.LiesOver (Ideal.span {(p : ℤ)})] (j : ℕ)

include hp in

theorem natCast_mem_under_smul (x : F ≃ₐ[ℚ] F) :
    ((p : ℕ) : 𝓞 ↥(IntermediateField.fixedField H)) ∈ (x • P).under (𝓞 ↥(IntermediateField.fixedField H)) := by
  rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
  have h1 : ((p : ℤ) : 𝓞 F) ∈ x • P := by
    have : (p : ℤ) ∈ (x • P).under ℤ := by
      rw [Ideal.under_smul, ← Ideal.over_def P (Ideal.span {(p : ℤ)})]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.under_def, Ideal.mem_comap] at this
    simpa using this
  simpa using h1

include hp in

noncomputable def plV (x : F ≃ₐ[ℚ] F) : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) where
  asIdeal := (x⁻¹ • P).under (𝓞 ↥(IntermediateField.fixedField H))
  isPrime := by
    haveI := isMaximal_smul x⁻¹ P
    exact Ideal.IsPrime.under _ _
  ne_bot := by
    intro h
    have := natCast_mem_under_smul F H hp P x⁻¹
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at this
    exact hp.ne_zero this

theorem plV_asIdeal (x : F ≃ₐ[ℚ] F) : (plV F H hp P x).asIdeal = (x⁻¹ • P).under (𝓞 ↥(IntermediateField.fixedField H)) := rfl

include hp in

theorem under_smul_of_mem (h : F ≃ₐ[ℚ] F) (hh : h ∈ H) (x : F ≃ₐ[ℚ] F) :
    ((h * x) • P).under (𝓞 ↥(IntermediateField.fixedField H)) = (x • P).under (𝓞 ↥(IntermediateField.fixedField H)) :=
  ((ArtinL.Abelian.galois_primesOver_dictionary F H hp P).2.1 x (h * x)).2 ⟨h, hh, 1, (stabilizer _ P).one_mem, by rw [mul_one]⟩ |>.symm

theorem inner_eq_of_plV_eq {x y : F ≃ₐ[ℚ] F} (hxy : plV F H hp P x = plV F H hp P y) :
    inner F H χ P j x = inner F H χ P j y := by
  have h := congrArg HeightOneSpectrum.asIdeal hxy
  rw [plV_asIdeal, plV_asIdeal] at h
  obtain ⟨h', hh', d, hd, e⟩ := ((ArtinL.Abelian.galois_primesOver_dictionary F H hp P).2.1 x⁻¹ y⁻¹).1 h

  have hy : y = d⁻¹ * x * h'⁻¹ := by
    have := congrArg (·⁻¹) e; simp only [inv_inv, mul_inv_rev] at this; rw [this, mul_assoc]
  rw [hy, inner_mul_eq F H χ P j x d⁻¹ h'⁻¹ ((stabilizer _ P).inv_mem hd) (H.inv_mem hh')]

theorem card_fiber_mul (x₀ : F ≃ₐ[ℚ] F) :
    (Finset.univ.filter fun x : F ≃ₐ[ℚ] F => plV F H hp P x = plV F H hp P x₀).card *
        Fintype.card ↥(H ⊓ stabilizer (F ≃ₐ[ℚ] F) (x₀⁻¹ • P)) =
      Fintype.card ↥(stabilizer (F ≃ₐ[ℚ] F) P) * Fintype.card H := by
  classical

  let A : Ideal (𝓞 F) → ℕ := fun Q => if Q.under (𝓞 ↥(IntermediateField.fixedField H)) = (x₀⁻¹ • P).under (𝓞 ↥(IntermediateField.fixedField H)) then 1 else 0

  have h1 : (Finset.univ.filter fun x : F ≃ₐ[ℚ] F => plV F H hp P x = plV F H hp P x₀).card = ∑ x : F ≃ₐ[ℚ] F, A (x • P) := by
    rw [Finset.card_filter]
    refine (Fintype.sum_equiv (Equiv.inv (F ≃ₐ[ℚ] F)) _ _ fun x => ?_).symm
    change A (x • P) = if plV F H hp P x⁻¹ = plV F H hp P x₀ then 1 else 0
    simp only [A, HeightOneSpectrum.ext_iff, plV_asIdeal, inv_inv]
  have h2 := sum_smul_eq_card_stabilizer_smul_sum_image (G := F ≃ₐ[ℚ] F) P A

  have h3 := sum_smul_eq_card_stabilizer_smul_sum_image (G := H) (x₀⁻¹ • P) A
  have hA1 : ∀ h : H, A (h • (x₀⁻¹ • P)) = 1 := by
    intro h
    have e : h • (x₀⁻¹ • P) = ((h : F ≃ₐ[ℚ] F) * x₀⁻¹) • P := by
      rw [mul_smul]; rfl
    rw [e]
    simp only [A, under_smul_of_mem F H hp P h h.2, if_true]

  have h4 : ∑ b ∈ Finset.univ.image (fun x : F ≃ₐ[ℚ] F => x • P), A b =
      ∑ b ∈ Finset.univ.image (fun h : H => h • (x₀⁻¹ • P)), A b := by
    rw [← Finset.sum_filter_ne_zero (Finset.univ.image (fun x : F ≃ₐ[ℚ] F => x • P)),
      ← Finset.sum_filter_ne_zero (Finset.univ.image (fun h : H => h • (x₀⁻¹ • P)))]
    congr 1
    ext Q
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨x, rfl⟩, hA⟩
      have hx : (x • P).under (𝓞 ↥(IntermediateField.fixedField H)) = (x₀⁻¹ • P).under (𝓞 ↥(IntermediateField.fixedField H)) := by
        by_contra hne; exact hA (if_neg hne)
      obtain ⟨h', hh', d, hd, e⟩ := ((ArtinL.Abelian.galois_primesOver_dictionary F H hp P).2.1 x₀⁻¹ x).1 hx.symm
      refine ⟨⟨⟨h', hh'⟩, ?_⟩, hA⟩
      change h' • (x₀⁻¹ • P) = x • P
      rw [← mul_smul, e, mul_smul (h' * x₀⁻¹) d P, mem_stabilizer_iff.1 hd]
    · rintro ⟨⟨h, rfl⟩, hA⟩
      exact ⟨⟨(h : F ≃ₐ[ℚ] F) * x₀⁻¹, by rw [mul_smul]; rfl⟩, hA⟩

  have h5 : Fintype.card ↥(stabilizer H (x₀⁻¹ • P)) = Fintype.card ↥(H ⊓ stabilizer (F ≃ₐ[ℚ] F) (x₀⁻¹ • P)) :=
    Fintype.card_congr (Equiv.ofBijective (fun s : ↥(stabilizer H (x₀⁻¹ • P)) =>
        (⟨((s : H) : F ≃ₐ[ℚ] F), (s : H).2, s.2⟩ : ↥(H ⊓ stabilizer (F ≃ₐ[ℚ] F) (x₀⁻¹ • P))))
      ⟨fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun u : ↥(H ⊓ stabilizer (F ≃ₐ[ℚ] F) (x₀⁻¹ • P)) => (u : F ≃ₐ[ℚ] F)) hab)),
       fun u => ⟨⟨⟨u, u.2.1⟩, u.2.2⟩, rfl⟩⟩)

  have hH : Fintype.card H = Fintype.card ↥(stabilizer H (x₀⁻¹ • P)) * ∑ b ∈ Finset.univ.image (fun h : H => h • (x₀⁻¹ • P)), A b := by
    rw [← smul_eq_mul, ← h3, Finset.sum_congr rfl (fun h _ => hA1 h), Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  rw [h1, h2, h4, smul_eq_mul, hH, h5]
  ring

end main2

end ArtinL.Abelian.C3

namespace ArtinL
p2m_export "ArtinL" "Abelian.IsUnramifiedAt Abelian.localValue Abelian.ofSubgroup Abelian.galois_primesOver_dictionary Abelian.isUnramifiedAt_ofSubgroup_iff_and_localValue_eq"
namespace Abelian
p2m_export "ArtinL.Abelian" "IsUnramifiedAt localValue ofSubgroup galois_primesOver_dictionary isUnramifiedAt_ofSubgroup_iff_and_localValue_eq"
namespace C3
p2m_open "ArtinL.Abelian ArtinL"

open MulAction

section main3
variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F] (H : Subgroup (F ≃ₐ[ℚ] F)) (χ : H →* ℂˣ)
  {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 F)) [hPmax : P.IsMaximal] [hPover : P.LiesOver (Ideal.span {(p : ℤ)})] {j : ℕ} (hj : 0 < j)

theorem inner_eq_sum_smul (x₀ : F ≃ₐ[ℚ] F) :
    haveI := isMaximal_smul x₀⁻¹ P
    inner F H χ P j x₀ = ∑ τ : ↥((x₀⁻¹ • P).inertia (F ≃ₐ[ℚ] F)),
      chiZ H χ (arithFrobAt ℤ (F ≃ₐ[ℚ] F) (x₀⁻¹ • P) ^ j * τ) := by
  haveI := isMaximal_smul x₀⁻¹ P
  have hφ : IsArithFrobAt ℤ (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P) P := IsArithFrobAt.arithFrobAt _ _ _
  have hψ : IsArithFrobAt ℤ (x₀⁻¹ * arithFrobAt ℤ (F ≃ₐ[ℚ] F) P * x₀⁻¹⁻¹) (x₀⁻¹ • P) := hφ.conj x₀⁻¹
  have hφQ : IsArithFrobAt ℤ (arithFrobAt ℤ (F ≃ₐ[ℚ] F) (x₀⁻¹ • P)) (x₀⁻¹ • P) := IsArithFrobAt.arithFrobAt _ _ _
  unfold inner
  have e1 : ∀ τ : ↥(P.inertia (F ≃ₐ[ℚ] F)), x₀⁻¹ * (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P ^ j * τ) * x₀ =
      (x₀⁻¹ * arithFrobAt ℤ (F ≃ₐ[ℚ] F) P * x₀⁻¹⁻¹) ^ j * (x₀⁻¹ * τ * x₀) := by
    intro τ; rw [conj_pow]; group
  simp_rw [e1]
  rw [sum_inertia_smul_eq P (fun σ => chiZ H χ ((x₀⁻¹ * arithFrobAt ℤ (F ≃ₐ[ℚ] F) P * x₀⁻¹⁻¹) ^ j * σ)) x₀]
  apply sum_inertia_mul_eq (x₀⁻¹ • P) (chiZ H χ)
  apply pow_inv_mul_pow_mem_inertia hφQ.mem_stabilizer
  have h1 := IsArithFrobAt.mul_inv_mem_inertia hφQ hψ
  simpa [mul_assoc] using inv_conj_mem_inertia hψ.mem_stabilizer h1

set_option maxHeartbeats 6400000 in
include hj in

theorem weighted_inner_eq (x₀ : F ≃ₐ[ℚ] F) :
    (Fintype.card ↥(P.inertia (F ≃ₐ[ℚ] F)) : ℂ)⁻¹ * (Nat.card ↥H : ℂ)⁻¹ *
        ((Finset.univ.filter fun x : F ≃ₐ[ℚ] F => plV F H hp P x = plV F H hp P x₀).card : ℂ) * inner F H χ P j x₀ =
      if (Ideal.span {(p : ℤ)}).inertiaDeg' (plV F H hp P x₀).asIdeal ∣ j then
        ((Ideal.span {(p : ℤ)}).inertiaDeg' (plV F H hp P x₀).asIdeal : ℂ) *
          ArtinL.Abelian.localValue (ArtinL.Abelian.ofSubgroup H χ) (plV F H hp P x₀) ^
            (j / (Ideal.span {(p : ℤ)}).inertiaDeg' (plV F H hp P x₀).asIdeal)
      else 0 := by
  classical
  haveI hQmax := isMaximal_smul x₀⁻¹ P
  haveI hQover : (x₀⁻¹ • P).LiesOver (Ideal.span {(p : ℤ)}) := ⟨by rw [Ideal.under_smul]; exact Ideal.over_def P _⟩
  have hv : (x₀⁻¹ • P).under (𝓞 ↥(IntermediateField.fixedField H)) = (plV F H hp P x₀).asIdeal := rfl
  obtain ⟨-, -, hQ, -⟩ := ArtinL.Abelian.galois_primesOver_dictionary F H hp P
  obtain ⟨hiii, hiv⟩ := hQ (x₀⁻¹ • P) (plV F H hp P x₀) hv
  obtain ⟨hbi, hbii⟩ := ArtinL.Abelian.isUnramifiedAt_ofSubgroup_iff_and_localValue_eq F H χ hp (x₀⁻¹ • P) (plV F H hp P x₀) hv

  have hI : Fintype.card ↥((x₀⁻¹ • P).inertia (F ≃ₐ[ℚ] F)) = Fintype.card ↥(P.inertia (F ≃ₐ[ℚ] F)) := card_inertia_smul x₀⁻¹ P
  have hD : Fintype.card ↥(stabilizer (F ≃ₐ[ℚ] F) (x₀⁻¹ • P)) = Fintype.card ↥(stabilizer (F ≃ₐ[ℚ] F) P) := card_stabilizer_smul x₀⁻¹ P

  have hfib := card_fiber_mul F H hp P x₀

  have cI0 : (Fintype.card ↥(P.inertia (F ≃ₐ[ℚ] F)) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have cH0 : (Nat.card ↥H : ℂ) ≠ 0 := by rw [Nat.card_eq_fintype_card]; exact Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have cHD0 : (Fintype.card ↥(H ⊓ stabilizer (F ≃ₐ[ℚ] F) (x₀⁻¹ • P)) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero

  have hcoef : (Fintype.card ↥(P.inertia (F ≃ₐ[ℚ] F)) : ℂ)⁻¹ * (Nat.card ↥H : ℂ)⁻¹ *
      ((Finset.univ.filter fun x : F ≃ₐ[ℚ] F => plV F H hp P x = plV F H hp P x₀).card : ℂ) *
        (Fintype.card ↥((x₀⁻¹ • P).inertia (F ≃ₐ[ℚ] F) ⊓ H) : ℂ) =
      ((Ideal.span {(p : ℤ)}).inertiaDeg' (plV F H hp P x₀).asIdeal : ℂ) := by
    have h1 : (((Finset.univ.filter fun x : F ≃ₐ[ℚ] F => plV F H hp P x = plV F H hp P x₀).card : ℕ) : ℂ) *
        (Fintype.card ↥(H ⊓ stabilizer (F ≃ₐ[ℚ] F) (x₀⁻¹ • P)) : ℂ) =
        (Fintype.card ↥(stabilizer (F ≃ₐ[ℚ] F) P) : ℂ) * (Nat.card ↥H : ℂ) := by
      rw [Nat.card_eq_fintype_card]; exact_mod_cast hfib
    have h2 : ((Ideal.span {(p : ℤ)}).inertiaDeg' (plV F H hp P x₀).asIdeal : ℂ) *
        (Fintype.card ↥(H ⊓ stabilizer (F ≃ₐ[ℚ] F) (x₀⁻¹ • P)) : ℂ) * (Fintype.card ↥(P.inertia (F ≃ₐ[ℚ] F)) : ℂ) =
        (Fintype.card ↥(stabilizer (F ≃ₐ[ℚ] F) P) : ℂ) * (Fintype.card ↥((x₀⁻¹ • P).inertia (F ≃ₐ[ℚ] F) ⊓ H) : ℂ) := by
      have := hiii
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hI, hD,
        inf_comm H ((x₀⁻¹ • P).inertia (F ≃ₐ[ℚ] F))] at this
      exact_mod_cast this
    have cD_eq : (Fintype.card ↥(stabilizer (F ≃ₐ[ℚ] F) P) : ℂ) * (Nat.card ↥H : ℂ) *
        (Fintype.card ↥((x₀⁻¹ • P).inertia (F ≃ₐ[ℚ] F) ⊓ H) : ℂ) =
        (Nat.card ↥H : ℂ) * (((Ideal.span {(p : ℤ)}).inertiaDeg' (plV F H hp P x₀).asIdeal : ℂ) *
          (Fintype.card ↥(H ⊓ stabilizer (F ≃ₐ[ℚ] F) (x₀⁻¹ • P)) : ℂ) * (Fintype.card ↥(P.inertia (F ≃ₐ[ℚ] F)) : ℂ)) := by
      rw [h2]; ring
    rw [← h1] at cD_eq

    have key : ((Finset.univ.filter fun x : F ≃ₐ[ℚ] F => plV F H hp P x = plV F H hp P x₀).card : ℂ) *
        (Fintype.card ↥((x₀⁻¹ • P).inertia (F ≃ₐ[ℚ] F) ⊓ H) : ℂ) =
        (Nat.card ↥H : ℂ) * ((Ideal.span {(p : ℤ)}).inertiaDeg' (plV F H hp P x₀).asIdeal : ℂ) *
          (Fintype.card ↥(P.inertia (F ≃ₐ[ℚ] F)) : ℂ) := by
      apply mul_left_cancel₀ cHD0
      linear_combination cD_eq
    field_simp
    linear_combination key
  rw [inner_eq_sum_smul F H χ P x₀]

  by_cases hex : ∃ τ : F ≃ₐ[ℚ] F, τ ∈ (x₀⁻¹ • P).inertia (F ≃ₐ[ℚ] F) ∧ arithFrobAt ℤ (F ≃ₐ[ℚ] F) (x₀⁻¹ • P) ^ j * τ ∈ H
  · obtain ⟨τ₀, hτ₀, h₀⟩ := hex

    have hdvd : (Ideal.span {(p : ℤ)}).inertiaDeg' (plV F H hp P x₀).asIdeal ∣ j :=
      (hiv j).1 ⟨_, h₀, by simpa [mul_assoc] using ((x₀⁻¹ • P).inertia (F ≃ₐ[ℚ] F)).inv_mem hτ₀⟩
    rw [if_pos hdvd]
    have hsum : (∑ τ : ↥((x₀⁻¹ • P).inertia (F ≃ₐ[ℚ] F)), chiZ H χ (arithFrobAt ℤ (F ≃ₐ[ℚ] F) (x₀⁻¹ • P) ^ j * τ)) =
        (if ∀ (σ : F ≃ₐ[ℚ] F) (hσ : σ ∈ H), σ ∈ (x₀⁻¹ • P).inertia (F ≃ₐ[ℚ] F) → χ ⟨σ, hσ⟩ = 1 then
          (Fintype.card ↥((x₀⁻¹ • P).inertia (F ≃ₐ[ℚ] F) ⊓ H) : ℂ) else 0) *
          ((χ ⟨arithFrobAt ℤ (F ≃ₐ[ℚ] F) (x₀⁻¹ • P) ^ j * τ₀, h₀⟩ : ℂˣ) : ℂ) :=
      sum_coset_eq ((x₀⁻¹ • P).inertia (F ≃ₐ[ℚ] F)) H χ _ τ₀ hτ₀ h₀
    rw [hsum]
    by_cases htriv : ∀ (σ : F ≃ₐ[ℚ] F) (hσ : σ ∈ H), σ ∈ (x₀⁻¹ • P).inertia (F ≃ₐ[ℚ] F) → χ ⟨σ, hσ⟩ = 1
    ·
      rw [if_pos htriv, ← mul_assoc, hcoef]
      congr 1
      have hunr : ArtinL.Abelian.IsUnramifiedAt (ArtinL.Abelian.ofSubgroup H χ) (plV F H hp P x₀) := hbi.2 htriv
      obtain ⟨σ₁, hσ₁, hσ₁'⟩ := (hiv _).2 (dvd_refl _)
      rw [hbii hunr σ₁ hσ₁ hσ₁', ← Units.val_pow_eq_pow_val, ← map_pow]

      set k := j / (Ideal.span {(p : ℤ)}).inertiaDeg' (plV F H hp P x₀).asIdeal with hk
      have hjk : arithFrobAt ℤ (F ≃ₐ[ℚ] F) (x₀⁻¹ • P) ^ j =
          (arithFrobAt ℤ (F ≃ₐ[ℚ] F) (x₀⁻¹ • P) ^ (Ideal.span {(p : ℤ)}).inertiaDeg' (plV F H hp P x₀).asIdeal) ^ k := by
        rw [← pow_mul, Nat.mul_div_cancel' hdvd]
      have hu : (σ₁ ^ k)⁻¹ * (arithFrobAt ℤ (F ≃ₐ[ℚ] F) (x₀⁻¹ • P) ^ j * τ₀) ∈ (x₀⁻¹ • P).inertia (F ≃ₐ[ℚ] F) := by
        rw [hjk, ← mul_assoc]
        exact ((x₀⁻¹ • P).inertia (F ≃ₐ[ℚ] F)).mul_mem
          (pow_inv_mul_pow_mem_inertia ((stabilizer _ _).pow_mem (IsArithFrobAt.arithFrobAt ℤ (F ≃ₐ[ℚ] F) (x₀⁻¹ • P)).mem_stabilizer _) hσ₁' k) hτ₀
      have huH : (σ₁ ^ k)⁻¹ * (arithFrobAt ℤ (F ≃ₐ[ℚ] F) (x₀⁻¹ • P) ^ j * τ₀) ∈ H := H.mul_mem (H.inv_mem (H.pow_mem hσ₁ k)) h₀
      have e : (⟨arithFrobAt ℤ (F ≃ₐ[ℚ] F) (x₀⁻¹ • P) ^ j * τ₀, h₀⟩ : H) =
          ⟨σ₁, hσ₁⟩ ^ k * ⟨_, huH⟩ := Subtype.ext (by simp [mul_assoc])
      rw [e, map_mul, htriv _ huH hu, mul_one]
    ·
      rw [if_neg htriv, zero_mul, mul_zero]
      have hunr : ¬ ArtinL.Abelian.IsUnramifiedAt (ArtinL.Abelian.ofSubgroup H χ) (plV F H hp P x₀) := fun h => htriv (hbi.1 h)
      have hk : 0 < j / (Ideal.span {(p : ℤ)}).inertiaDeg' (plV F H hp P x₀).asIdeal :=
        Nat.div_pos (Nat.le_of_dvd hj hdvd) (Nat.pos_of_ne_zero fun h0 => by rw [h0, zero_dvd_iff] at hdvd; omega)
      rw [ArtinL.Abelian.localValue, if_neg hunr, zero_pow hk.ne', mul_zero]
  ·
    have hsum0 : (∑ τ : ↥((x₀⁻¹ • P).inertia (F ≃ₐ[ℚ] F)), chiZ H χ (arithFrobAt ℤ (F ≃ₐ[ℚ] F) (x₀⁻¹ • P) ^ j * τ)) = 0 :=
      sum_coset_eq_zero ((x₀⁻¹ • P).inertia (F ≃ₐ[ℚ] F)) H χ _ hex
    rw [hsum0, mul_zero, if_neg]
    intro hdvd
    obtain ⟨σ, hσ, hσ'⟩ := (hiv j).2 hdvd
    refine hex ⟨(σ⁻¹ * arithFrobAt ℤ (F ≃ₐ[ℚ] F) (x₀⁻¹ • P) ^ j)⁻¹, ((x₀⁻¹ • P).inertia (F ≃ₐ[ℚ] F)).inv_mem hσ', ?_⟩
    simpa [mul_assoc] using hσ

end main3

end ArtinL.Abelian.C3

theorem solution
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (H : Subgroup (F ≃ₐ[ℚ] F)) (χ : H →* ℂˣ) {p : ℕ} (hp : p.Prime)
    (P : Ideal (𝓞 F)) [P.IsMaximal] [P.LiesOver (Ideal.span {(p : ℤ)})] {j : ℕ} (hj : 0 < j) :
    (Fintype.card ↥(P.inertia (F ≃ₐ[ℚ] F)) : ℂ)⁻¹ *
        ∑ τ : ↥(P.inertia (F ≃ₐ[ℚ] F)), ((Nat.card ↥H : ℂ)⁻¹ *
          ∑ x : F ≃ₐ[ℚ] F,
            if hx : x⁻¹ * (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P ^ j * (τ : F ≃ₐ[ℚ] F)) * x ∈ H then
              ((χ ⟨x⁻¹ * (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P ^ j * (τ : F ≃ₐ[ℚ] F)) * x, hx⟩ : ℂˣ) : ℂ)
            else 0) =
      ∑ᶠ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)),
        if ((p : ℕ) : 𝓞 ↥(IntermediateField.fixedField H)) ∈ v.asIdeal ∧
            (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal ∣ j then
          ((Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal : ℂ) *
            ArtinL.Abelian.localValue (ArtinL.Abelian.ofSubgroup H χ) v ^
              (j / (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal)
        else 0 := by
  classical

  have hA : (Fintype.card ↥(P.inertia (F ≃ₐ[ℚ] F)) : ℂ)⁻¹ *
        ∑ τ : ↥(P.inertia (F ≃ₐ[ℚ] F)), ((Nat.card ↥H : ℂ)⁻¹ *
          ∑ x : (F ≃ₐ[ℚ] F),
            if hx : x⁻¹ * (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P ^ j * (τ : (F ≃ₐ[ℚ] F))) * x ∈ H then
              ((χ ⟨x⁻¹ * (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P ^ j * (τ : (F ≃ₐ[ℚ] F))) * x, hx⟩ : ℂˣ) : ℂ)
            else 0) =
      ∑ x : (F ≃ₐ[ℚ] F), (Fintype.card ↥(P.inertia (F ≃ₐ[ℚ] F)) : ℂ)⁻¹ * (Nat.card ↥H : ℂ)⁻¹ * ArtinL.Abelian.C3.inner F H χ P j x := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [ArtinL.Abelian.C3.inner, ArtinL.Abelian.C3.chiZ, Finset.mul_sum, mul_assoc]
  rw [hA]

  set T := Finset.univ.image (ArtinL.Abelian.C3.plV F H hp P) with hT
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := T) (g := ArtinL.Abelian.C3.plV F H hp P)
    (fun x _ => Finset.mem_image_of_mem _ (Finset.mem_univ x))]

  have hsupp : Function.support (fun v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) =>
      if ((p : ℕ) : 𝓞 ↥(IntermediateField.fixedField H)) ∈ v.asIdeal ∧ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal ∣ j then
        ((Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal : ℂ) *
          ArtinL.Abelian.localValue (ArtinL.Abelian.ofSubgroup H χ) v ^ (j / (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal)
      else 0) ⊆ ↑T := by
    intro v hv
    rw [Function.mem_support] at hv
    have hpv : ((p : ℕ) : 𝓞 ↥(IntermediateField.fixedField H)) ∈ v.asIdeal := by
      by_contra h; exact hv (if_neg fun h' => h h'.1)
    obtain ⟨x, hx⟩ := (ArtinL.Abelian.galois_primesOver_dictionary F H hp P).1 v hpv
    rw [hT, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact ⟨x⁻¹, HeightOneSpectrum.ext (by rw [ArtinL.Abelian.C3.plV_asIdeal, inv_inv, hx])⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  refine Finset.sum_congr rfl fun v hv => ?_
  obtain ⟨x₀, -, rfl⟩ := Finset.mem_image.1 hv

  rw [Finset.sum_congr rfl (fun x hx => by rw [ArtinL.Abelian.C3.inner_eq_of_plV_eq F H χ hp P j (Finset.mem_filter.1 hx).2]),
    Finset.sum_const, nsmul_eq_mul]
  have hpv : ((p : ℕ) : 𝓞 ↥(IntermediateField.fixedField H)) ∈ (ArtinL.Abelian.C3.plV F H hp P x₀).asIdeal :=
    ArtinL.Abelian.C3.natCast_mem_under_smul F H hp P x₀⁻¹
  simp only [hpv, true_and]
  rw [← ArtinL.Abelian.C3.weighted_inner_eq F H χ hp P hj x₀]
  ring

end S_ArtinL_Abelian_inv_card_inertia_mul_sum_induced_frob_pow_mul_eq_finsum
end P2MW
export P2MW.S_ArtinL_Abelian_inv_card_inertia_mul_sum_induced_frob_pow_mul_eq_finsum (solution)
