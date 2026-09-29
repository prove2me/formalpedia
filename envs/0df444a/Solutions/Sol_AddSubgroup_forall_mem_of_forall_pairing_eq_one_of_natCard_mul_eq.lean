-- Prove2me | solution 1 for AddSubgroup.forall_mem_of_forall_pairing_eq_one_of_natCard_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/38f63cab-f1a6-52c8-a1f7-caf0ff9ef5e3

import Mathlib
import Theorems.Thm_Set_ncard_pairing_annihilator_mul_ncard_eq_ncard_mul_ncard_radical
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddSubgroup_forall_mem_of_forall_pairing_eq_one_of_natCard_mul_eq

set_option autoImplicit false

theorem solution
    {G : Type} [AddCommGroup G] [Finite G] {L : Type} [Field L] [CharZero L] (n : ℕ) (hn : n ≠ 0)
    (B : G → G → L)
    (hval : ∀ x y : G, B x y ^ n = 1)
    (hadd₁ : ∀ x x' y : G, B (x + x') y = B x y * B x' y)
    (hadd₂ : ∀ x y y' : G, B x (y + y') = B x y * B x y')
    (hleft : ∀ x : G, (∀ y : G, B x y = 1) → x = 0)
    (hright : ∀ y : G, (∀ x : G, B x y = 1) → y = 0)
    (T F : AddSubgroup G) (hiso : ∀ t ∈ T, ∀ f ∈ F, B t f = 1)
    (hcard : Nat.card T * Nat.card F = Nat.card G) :
    (∀ x : G, (∀ f ∈ F, B x f = 1) → x ∈ T) ∧ (∀ y : G, (∀ t ∈ T, B t y = 1) → y ∈ F) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G

  let annL : AddSubgroup G :=
    { carrier := {x | ∀ f ∈ F, B x f = 1}
      zero_mem' := by
        intro f hf
        have h := hadd₁ 0 0 f
        rw [add_zero] at h

        have hne : B 0 f ≠ 0 := fun h0 => by
          have := hval 0 f; rw [h0, zero_pow hn] at this; exact zero_ne_one this
        exact (mul_right_eq_self₀.mp h.symm).resolve_right hne
      add_mem' := by
        intro a b ha hb f hf
        rw [hadd₁, ha f hf, hb f hf, one_mul]
      neg_mem' := by
        intro a ha f hf
        have h := hadd₁ a (-a) f
        rw [add_neg_cancel, ha f hf, one_mul] at h

        have h0 : B 0 f = 1 := by
          have h2 := hadd₁ 0 0 f
          rw [add_zero] at h2
          have hne : B 0 f ≠ 0 := fun h0 => by
            have := hval 0 f; rw [h0, zero_pow hn] at this; exact zero_ne_one this
          exact (mul_right_eq_self₀.mp h2.symm).resolve_right hne
        rw [h0] at h
        exact h.symm }
  let annR : AddSubgroup G :=
    { carrier := {y | ∀ t ∈ T, B t y = 1}
      zero_mem' := by
        intro t ht
        have h := hadd₂ t 0 0
        rw [add_zero] at h
        have hne : B t 0 ≠ 0 := fun h0 => by
          have := hval t 0; rw [h0, zero_pow hn] at this; exact zero_ne_one this
        exact (mul_right_eq_self₀.mp h.symm).resolve_right hne
      add_mem' := by
        intro a b ha hb t ht
        rw [hadd₂, ha t ht, hb t ht, one_mul]
      neg_mem' := by
        intro a ha t ht
        have h := hadd₂ t a (-a)
        rw [add_neg_cancel, ha t ht, one_mul] at h
        have h0 : B t 0 = 1 := by
          have h2 := hadd₂ t 0 0
          rw [add_zero] at h2
          have hne : B t 0 ≠ 0 := fun h0 => by
            have := hval t 0; rw [h0, zero_pow hn] at this; exact zero_ne_one this
          exact (mul_right_eq_self₀.mp h2.symm).resolve_right hne
        rw [h0] at h
        exact h.symm }
  have hT_le : T ≤ annL := fun t ht f hf => hiso t ht f hf
  have hF_le : F ≤ annR := fun f hf t ht => hiso t ht f hf

  have hsub : ∀ (S : AddSubgroup G), (S : Set G).Finite := fun S => Set.toFinite _

  have hA := Set.ncard_pairing_annihilator_mul_ncard_eq_ncard_mul_ncard_radical (T : Set G) (Set.univ : Set G)
    (hsub T) Set.finite_univ T.zero_mem (fun x hx y hy => T.add_mem hx hy) (fun x hx => T.neg_mem hx)
    (Set.mem_univ _) (fun _ _ _ _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _) B
    (fun a _ a' _ y _ => hadd₁ a a' y) (fun a _ y _ y' _ => hadd₂ a y y')
  have hradT : {a : G | a ∈ (T : Set G) ∧ ∀ y ∈ (Set.univ : Set G), B a y = 1} = {0} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_univ, forall_const, Set.mem_singleton_iff, SetLike.mem_coe]
    constructor
    · rintro ⟨-, h⟩; exact hleft a h
    · rintro rfl
      refine ⟨T.zero_mem, fun y => ?_⟩
      have h := hadd₁ 0 0 y
      rw [add_zero] at h
      have hne : B 0 y ≠ 0 := fun h0 => by
        have := hval 0 y; rw [h0, zero_pow hn] at this; exact zero_ne_one this
      exact (mul_right_eq_self₀.mp h.symm).resolve_right hne
  have hannR_set : {y : G | y ∈ (Set.univ : Set G) ∧ ∀ a ∈ (T : Set G), B a y = 1} = (annR : Set G) := by
    ext y; simp only [Set.mem_setOf_eq, Set.mem_univ, true_and, SetLike.mem_coe]; rfl
  rw [hradT, hannR_set, Set.ncard_singleton, mul_one, Set.ncard_univ] at hA

  have hB := Set.ncard_pairing_annihilator_mul_ncard_eq_ncard_mul_ncard_radical (F : Set G) (Set.univ : Set G)
    (hsub F) Set.finite_univ F.zero_mem (fun x hx y hy => F.add_mem hx hy) (fun x hx => F.neg_mem hx)
    (Set.mem_univ _) (fun _ _ _ _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _) (fun a y => B y a)
    (fun a _ a' _ y _ => hadd₂ y a a') (fun a _ y _ y' _ => hadd₁ y y' a)
  have hradF : {a : G | a ∈ (F : Set G) ∧ ∀ y ∈ (Set.univ : Set G), B y a = 1} = {0} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_univ, forall_const, Set.mem_singleton_iff, SetLike.mem_coe]
    constructor
    · rintro ⟨-, h⟩; exact hright a h
    · rintro rfl
      refine ⟨F.zero_mem, fun y => ?_⟩
      have h := hadd₂ y 0 0
      rw [add_zero] at h
      have hne : B y 0 ≠ 0 := fun h0 => by
        have := hval y 0; rw [h0, zero_pow hn] at this; exact zero_ne_one this
      exact (mul_right_eq_self₀.mp h.symm).resolve_right hne
  have hannL_set : {y : G | y ∈ (Set.univ : Set G) ∧ ∀ a ∈ (F : Set G), B y a = 1} = (annL : Set G) := by
    ext y; simp only [Set.mem_setOf_eq, Set.mem_univ, true_and, SetLike.mem_coe]; rfl
  rw [hradF, hannL_set, Set.ncard_singleton, mul_one, Set.ncard_univ] at hB

  have cT : Set.ncard (T : Set G) = Nat.card T := (Nat.card_coe_set_eq (T : Set G)).symm
  have cF : Set.ncard (F : Set G) = Nat.card F := (Nat.card_coe_set_eq (F : Set G)).symm
  have cR : Set.ncard (annR : Set G) = Nat.card annR := (Nat.card_coe_set_eq (annR : Set G)).symm
  have cL : Set.ncard (annL : Set G) = Nat.card annL := (Nat.card_coe_set_eq (annL : Set G)).symm
  rw [cT, cR] at hA
  rw [cF, cL] at hB
  have hGpos : 0 < Nat.card G := Nat.card_pos
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hFpos : 0 < Nat.card F := Nat.card_pos

  have hL : Nat.card annL = Nat.card T := by
    have h1 : Nat.card annL * Nat.card F = Nat.card T * Nat.card F := by rw [hB, hcard]
    exact Nat.eq_of_mul_eq_mul_right hFpos h1
  have hR : Nat.card annR = Nat.card F := by
    have h1 : Nat.card annR * Nat.card T = Nat.card F * Nat.card T := by rw [hA, mul_comm, hcard]
    exact Nat.eq_of_mul_eq_mul_right hTpos h1
  have eT : T = annL := AddSubgroup.eq_of_le_of_card_ge hT_le hL.le
  have eF : F = annR := AddSubgroup.eq_of_le_of_card_ge hF_le hR.le
  constructor
  · intro x hx
    rw [eT]; exact hx
  · intro y hy
    rw [eF]; exact hy

end S_AddSubgroup_forall_mem_of_forall_pairing_eq_one_of_natCard_mul_eq
end P2MW
export P2MW.S_AddSubgroup_forall_mem_of_forall_pairing_eq_one_of_natCard_mul_eq (solution)
