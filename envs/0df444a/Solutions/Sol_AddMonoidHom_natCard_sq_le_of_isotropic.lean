-- Prove2me | solution 1 for AddMonoidHom.natCard_sq_le_of_isotropic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/84e96f96-18fe-50ad-ab8c-be0c6759487f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddMonoidHom_natCard_sq_le_of_isotropic

set_option autoImplicit false

namespace IsotropicCard

universe u v w

section Hom

variable {Q : Type v} [AddCommGroup Q]

theorem nsmul_natCard_eq_zero {A : Type u} [AddCommGroup A] [Finite A] (a : A) : Nat.card A • a = 0 :=
  addOrderOf_dvd_iff_nsmul_eq_zero.1 (addOrderOf_dvd_natCard a)

theorem finite_torsion_of_encard_le {n : ℕ} (h : ({x : Q | n • x = 0} : Set Q).encard ≤ n) :
    Finite {x : Q // n • x = 0} := by
  rw [Set.encard_le_coe_iff_finite_ncard_le] at h
  rw [← Set.coe_setOf]
  exact h.1.to_subtype

theorem natCard_torsion_le_of_encard_le {n : ℕ} (h : ({x : Q | n • x = 0} : Set Q).encard ≤ n) :
    Nat.card {x : Q // n • x = 0} ≤ n := by
  rw [Set.encard_le_coe_iff_finite_ncard_le] at h
  rw [← Set.coe_setOf, Nat.card_coe_set_eq]
  exact h.2

variable (hQ : ∀ n : ℕ, n ≠ 0 → ({x : Q | n • x = 0} : Set Q).encard ≤ n)
include hQ

theorem finite_addMonoidHom (A : Type u) [AddCommGroup A] [Finite A] : Finite (A →+ Q) := by
  haveI := finite_torsion_of_encard_le (hQ (Nat.card A) Nat.card_pos.ne')
  let f : (A →+ Q) → (A → {x : Q // Nat.card A • x = 0}) :=
    fun φ a => ⟨φ a, by rw [← map_nsmul, nsmul_natCard_eq_zero, map_zero]⟩
  refine Finite.of_injective f fun φ ψ h => ?_
  ext a
  exact congrArg Subtype.val (congrFun h a)

theorem natCard_addMonoidHom_zmultiples_le {A : Type u} [AddCommGroup A] [Finite A] (a : A) :
    Nat.card (AddSubgroup.zmultiples a →+ Q) ≤ Nat.card (AddSubgroup.zmultiples a) := by
  have hn : addOrderOf a ≠ 0 := (addOrderOf_pos a).ne'
  haveI := finite_torsion_of_encard_le (hQ _ hn)
  rw [Nat.card_zmultiples]
  refine le_trans ?_ (natCard_torsion_le_of_encard_le (hQ _ hn))
  let f : (AddSubgroup.zmultiples a →+ Q) → {x : Q // addOrderOf a • x = 0} :=
    fun φ => ⟨φ ⟨a, AddSubgroup.mem_zmultiples a⟩, by
      rw [← map_nsmul]
      convert map_zero φ
      exact Subtype.ext (addOrderOf_nsmul_eq_zero a)⟩
  refine Nat.card_le_card_of_injective f fun φ ψ h => ?_
  have h1 : φ ⟨a, AddSubgroup.mem_zmultiples a⟩ = ψ ⟨a, AddSubgroup.mem_zmultiples a⟩ :=
    congrArg Subtype.val h
  ext ⟨b, hb⟩
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hb
  have : (⟨k • a, hb⟩ : AddSubgroup.zmultiples a) = k • ⟨a, AddSubgroup.mem_zmultiples a⟩ := rfl
  rw [this, map_zsmul, map_zsmul, h1]

theorem natCard_addMonoidHom_le (A : Type u) [AddCommGroup A] [Finite A] :
    Nat.card (A →+ Q) ≤ Nat.card A := by
  suffices H : ∀ (n : ℕ) (A : Type u) [AddCommGroup A] [Finite A], Nat.card A = n →
      Nat.card (A →+ Q) ≤ Nat.card A from H _ A rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A _ _ hA
    by_cases hs : Subsingleton A
    · haveI : Subsingleton (A →+ Q) :=
        ⟨fun φ ψ => by ext x; rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
      rw [Nat.card_of_subsingleton (0 : A →+ Q), Nat.card_of_subsingleton (0 : A)]
    · obtain ⟨a, ha⟩ : ∃ a : A, a ≠ 0 := by
        by_contra! h; exact hs ⟨fun x y => by rw [h x, h y]⟩
      let B := AddSubgroup.zmultiples a
      haveI : Finite (A →+ Q) := finite_addMonoidHom hQ A
      haveI : Finite (B →+ Q) := finite_addMonoidHom hQ B
      haveI : Finite (A ⧸ B →+ Q) := finite_addMonoidHom hQ (A ⧸ B)

      let res : (A →+ Q) →+ (B →+ Q) :=
        AddMonoidHom.mk' (fun φ => φ.comp B.subtype) (fun φ ψ => AddMonoidHom.add_comp φ ψ _)

      have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup res.ker
      have h1 : Nat.card ((A →+ Q) ⧸ res.ker) ≤ Nat.card (B →+ Q) := by
        rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange res).toEquiv]
        exact Nat.card_le_card_of_injective _ Subtype.val_injective
      have h2 : Nat.card res.ker ≤ Nat.card (A ⧸ B →+ Q) := by
        let g : res.ker → (A ⧸ B →+ Q) := fun φ =>
          QuotientAddGroup.lift B φ.1 (fun b hb => by
            have := φ.2
            rw [AddMonoidHom.mem_ker] at this
            exact DFunLike.congr_fun this ⟨b, hb⟩)
        refine Nat.card_le_card_of_injective g fun φ ψ h => ?_
        apply Subtype.ext
        ext x
        have := DFunLike.congr_fun h (QuotientAddGroup.mk x)
        simpa [g] using this
      have hB : Nat.card (B →+ Q) ≤ Nat.card B := natCard_addMonoidHom_zmultiples_le hQ a
      have hAB : Nat.card (A ⧸ B →+ Q) ≤ Nat.card (A ⧸ B) := by
        refine ih (Nat.card (A ⧸ B)) ?_ (A ⧸ B) rfl
        rw [← hA, AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup B]
        have hB2 : 1 < Nat.card B := by
          rw [Nat.card_zmultiples]
          have h1 := addOrderOf_pos a
          have h2 : addOrderOf a ≠ 1 := fun h => ha (AddMonoid.addOrderOf_eq_one_iff.1 h)
          omega
        have hQpos : 0 < Nat.card (A ⧸ B) := Nat.card_pos
        nlinarith
      calc Nat.card (A →+ Q) = Nat.card ((A →+ Q) ⧸ res.ker) * Nat.card res.ker := hcard
        _ ≤ Nat.card (B →+ Q) * Nat.card (A ⧸ B →+ Q) := Nat.mul_le_mul h1 h2
        _ ≤ Nat.card B * Nat.card (A ⧸ B) := Nat.mul_le_mul hB hAB
        _ = Nat.card A := by
          rw [mul_comm, ← AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup B]

end Hom

section TorsionBounds

variable {Q : Type v} [AddCommGroup Q]

theorem encard_torsion_le_of_injective {Q' : Type w} [AddCommGroup Q'] (ι : Q →+ Q')
    (hι : Function.Injective ι)
    (hQ' : ∀ n : ℕ, n ≠ 0 → ({x : Q' | n • x = 0} : Set Q').encard ≤ n) (n : ℕ) (hn : n ≠ 0) :
    ({x : Q | n • x = 0} : Set Q).encard ≤ n := by
  refine le_trans ?_ (hQ' n hn)
  rw [← hι.encard_image]
  refine Set.encard_le_encard ?_
  rintro _ ⟨x, hx, rfl⟩
  simp only [Set.mem_setOf_eq] at hx ⊢
  rw [← map_nsmul, hx, map_zero]

theorem encard_torsion_addCircle_le {𝕜 : Type w} [AddCommGroup 𝕜] [IsAddTorsionFree 𝕜] (p : 𝕜)
    (n : ℕ) (hn : n ≠ 0) :
    ({x : AddCircle p | n • x = 0} : Set (AddCircle p)).encard ≤ n :=
  AddCircle.card_torsion_le_of_isSMulRegular p n hn (nsmul_right_injective hn)

theorem encard_torsion_zmod_le (m : ℕ) [NeZero m] (n : ℕ) (hn : n ≠ 0) :
    ({x : ZMod m | n • x = 0} : Set (ZMod m)).encard ≤ n :=
  encard_torsion_le_of_injective ZMod.toAddCircle (ZMod.toAddCircle_injective m)
    (encard_torsion_addCircle_le (1 : ℝ)) n hn

theorem encard_torsion_additive_units_le (L : Type w) [CommRing L] [IsDomain L] (n : ℕ) (hn : n ≠ 0) :
    ({x : Additive Lˣ | n • x = 0} : Set (Additive Lˣ)).encard ≤ n := by
  haveI : NeZero n := ⟨hn⟩
  let e : ({x : Additive Lˣ | n • x = 0} : Set (Additive Lˣ)) ≃ rootsOfUnity n L :=
    { toFun := fun x => ⟨Additive.toMul x.1, x.2⟩
      invFun := fun u => ⟨Additive.ofMul u.1, u.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hfin : Finite ({x : Additive Lˣ | n • x = 0} : Set (Additive Lˣ)) := Finite.of_equiv _ e.symm
  rw [Set.encard_le_coe_iff_finite_ncard_le, ← Nat.card_coe_set_eq, Nat.card_congr e]
  exact ⟨Set.finite_coe_iff.mp hfin, card_rootsOfUnity (R := L) (k := n)⟩

theorem encard_torsion_additive_subgroup_units_le (L : Type w) [CommRing L] [IsDomain L]
    (S : Subgroup Lˣ) (n : ℕ) (hn : n ≠ 0) :
    ({x : Additive S | n • x = 0} : Set (Additive S)).encard ≤ n :=
  encard_torsion_le_of_injective (MonoidHom.toAdditive S.subtype)
    (fun _ _ h => Subtype.val_injective h) (encard_torsion_additive_units_le L) n hn

end TorsionBounds

section Pairing

variable {V : Type u} {Q : Type v} [AddCommGroup V] [AddCommGroup Q]

def orthogonal (β : V →+ V →+ Q) (K : AddSubgroup V) : AddSubgroup V where
  carrier := {v | ∀ k ∈ K, β k v = 0}
  zero_mem' := fun k _ => map_zero (β k)
  add_mem' := fun {a b} ha hb k hk => by rw [map_add, ha k hk, hb k hk, add_zero]
  neg_mem' := fun {a} ha k hk => by rw [map_neg, ha k hk, neg_zero]

theorem mem_orthogonal {β : V →+ V →+ Q} {K : AddSubgroup V} {v : V} :
    v ∈ orthogonal β K ↔ ∀ k ∈ K, β k v = 0 := Iff.rfl

theorem le_orthogonal_of_isotropic (β : V →+ V →+ Q) (K : AddSubgroup V)
    (hK : ∀ k ∈ K, ∀ k' ∈ K, β k k' = 0) : K ≤ orthogonal β K :=
  fun v hv k hk => hK k hk v hv

theorem natCard_le_natCard_addMonoidHom_quotient_orthogonal (β : V →+ V →+ Q)
    (hβ : ∀ v, β v = 0 → v = 0) (K : AddSubgroup V) [Finite (V ⧸ orthogonal β K →+ Q)] :
    Nat.card K ≤ Nat.card (V ⧸ orthogonal β K →+ Q) := by
  let f : K → (V ⧸ orthogonal β K →+ Q) := fun k =>
    QuotientAddGroup.lift (orthogonal β K) (β k) (fun v hv => AddMonoidHom.mem_ker.mpr (hv k k.2))
  refine Nat.card_le_card_of_injective f fun k₁ k₂ h => ?_
  apply Subtype.ext
  rw [← sub_eq_zero]
  refine hβ _ ?_
  ext v
  have := DFunLike.congr_fun h (QuotientAddGroup.mk v)
  simp only [f, QuotientAddGroup.lift_mk] at this
  rw [map_sub, AddMonoidHom.sub_apply, this, sub_self, AddMonoidHom.zero_apply]

variable [Finite V]

theorem natCard_sq_le_of_isotropic
    (hQ : ∀ n : ℕ, n ≠ 0 → ({x : Q | n • x = 0} : Set Q).encard ≤ n)
    (β : V →+ V →+ Q) (hβ : ∀ v, β v = 0 → v = 0)
    (K : AddSubgroup V) (hK : ∀ k ∈ K, ∀ k' ∈ K, β k k' = 0) :
    Nat.card K ^ 2 ≤ Nat.card V := by
  haveI : Finite (V ⧸ orthogonal β K →+ Q) := finite_addMonoidHom hQ _
  have h1 := natCard_le_natCard_addMonoidHom_quotient_orthogonal β hβ K
  have h2 : Nat.card (V ⧸ orthogonal β K →+ Q) ≤ Nat.card (V ⧸ orthogonal β K) :=
    natCard_addMonoidHom_le hQ _
  have h3 : Nat.card K ≤ Nat.card (orthogonal β K) :=
    Nat.card_le_card_of_injective _
      (AddSubgroup.inclusion_injective (le_orthogonal_of_isotropic β K hK))
  calc Nat.card K ^ 2 = Nat.card K * Nat.card K := sq _
    _ ≤ Nat.card (V ⧸ orthogonal β K) * Nat.card (orthogonal β K) := Nat.mul_le_mul (h1.trans h2) h3
    _ = Nat.card V := (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _).symm

theorem natCard_mul_natCard_le_of_isotropic
    (hQ : ∀ n : ℕ, n ≠ 0 → ({x : Q | n • x = 0} : Set Q).encard ≤ n)
    (β : V →+ V →+ Q) (hβ : ∀ v, β v = 0 → v = 0)
    (K : AddSubgroup V) (hK : ∀ k ∈ K, ∀ k' ∈ K, β k k' = 0) :
    Nat.card K * Nat.card K ≤ Nat.card V := by
  rw [← sq]; exact natCard_sq_le_of_isotropic hQ β hβ K hK

theorem natCard_sq_le_of_isotropic_addCircle {𝕜 : Type w} [AddCommGroup 𝕜] [IsAddTorsionFree 𝕜]
    (p : 𝕜) (β : V →+ V →+ AddCircle p) (hβ : ∀ v, β v = 0 → v = 0)
    (K : AddSubgroup V) (hK : ∀ k ∈ K, ∀ k' ∈ K, β k k' = 0) :
    Nat.card K ^ 2 ≤ Nat.card V :=
  natCard_sq_le_of_isotropic (encard_torsion_addCircle_le p) β hβ K hK

theorem natCard_sq_le_of_isotropic_zmod (m : ℕ) [NeZero m]
    (β : V →+ V →+ ZMod m) (hβ : ∀ v, β v = 0 → v = 0)
    (K : AddSubgroup V) (hK : ∀ k ∈ K, ∀ k' ∈ K, β k k' = 0) :
    Nat.card K ^ 2 ≤ Nat.card V :=
  natCard_sq_le_of_isotropic (encard_torsion_zmod_le m) β hβ K hK

theorem natCard_sq_le_of_isotropic_of_injective {Q' : Type w} [AddCommGroup Q'] (ι : Q →+ Q')
    (hι : Function.Injective ι)
    (hQ' : ∀ n : ℕ, n ≠ 0 → ({x : Q' | n • x = 0} : Set Q').encard ≤ n)
    (β : V →+ V →+ Q) (hβ : ∀ v, β v = 0 → v = 0)
    (K : AddSubgroup V) (hK : ∀ k ∈ K, ∀ k' ∈ K, β k k' = 0) :
    Nat.card K ^ 2 ≤ Nat.card V :=
  natCard_sq_le_of_isotropic (encard_torsion_le_of_injective ι hι hQ') β hβ K hK

theorem natCard_sq_le_of_isotropic_units (L : Type w) [CommRing L] [IsDomain L]
    (β : V →+ V →+ Additive Lˣ) (hβ : ∀ v, β v = 0 → v = 0)
    (K : AddSubgroup V) (hK : ∀ k ∈ K, ∀ k' ∈ K, β k k' = 0) :
    Nat.card K ^ 2 ≤ Nat.card V :=
  natCard_sq_le_of_isotropic (encard_torsion_additive_units_le L) β hβ K hK

theorem natCard_sq_le_of_isotropic_subgroup_units (L : Type w) [CommRing L] [IsDomain L]
    (S : Subgroup Lˣ) (β : V →+ V →+ Additive S) (hβ : ∀ v, β v = 0 → v = 0)
    (K : AddSubgroup V) (hK : ∀ k ∈ K, ∀ k' ∈ K, β k k' = 0) :
    Nat.card K ^ 2 ≤ Nat.card V :=
  natCard_sq_le_of_isotropic (encard_torsion_additive_subgroup_units_le L S) β hβ K hK

end Pairing

end IsotropicCard

theorem solution
    {V Q : Type*} [AddCommGroup V] [Finite V] [AddCommGroup Q]
    (β : V →+ V →+ Q) (hβ : ∀ v, β v = 0 → v = 0)
    (hQ : ∀ n : ℕ, n ≠ 0 → {x : Q | n • x = 0}.encard ≤ n)
    (K : AddSubgroup V) (hK : ∀ k ∈ K, ∀ k' ∈ K, β k k' = 0) :
    Nat.card K ^ 2 ≤ Nat.card V := by
  exact IsotropicCard.natCard_sq_le_of_isotropic hQ β hβ K hK

end S_AddMonoidHom_natCard_sq_le_of_isotropic
end P2MW
export P2MW.S_AddMonoidHom_natCard_sq_le_of_isotropic (solution)
