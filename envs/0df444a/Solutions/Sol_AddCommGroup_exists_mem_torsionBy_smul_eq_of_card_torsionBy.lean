-- Prove2me | solution 1 for AddCommGroup.exists_mem_torsionBy_smul_eq_of_card_torsionBy
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/6671c23f-d01a-5326-b28e-8b45b81ea4a4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddCommGroup_exists_mem_torsionBy_smul_eq_of_card_torsionBy

set_option autoImplicit false

namespace P2mLwS

open Module Submodule Function

structure Pres (M : Type*) [AddCommGroup M] (n : ℕ) (V : Type*) [AddCommGroup V] where
  ι : V →+ M
  hι : Injective ι
  hιr : ∀ x : M, x ∈ ι.range ↔ ((n : ℕ) : ℤ) • x = 0

namespace Pres

variable {M : Type*} [AddCommGroup M] {n : ℕ} {V : Type*} [AddCommGroup V]

theorem nsmul_ι (P : Pres M n V) (v : V) : n • P.ι v = 0 := by
  have := (P.hιr (P.ι v)).1 ⟨v, rfl⟩
  rwa [natCast_zsmul] at this

theorem nsmul_self (P : Pres M n V) (v : V) : n • v = 0 :=
  P.hι (by rw [map_nsmul, P.nsmul_ι, map_zero])

theorem exists_eq (P : Pres M n V) {x : M} (hx : n • x = 0) : ∃ v, P.ι v = x := by
  obtain ⟨v, hv⟩ := (P.hιr x).2 (by rwa [natCast_zsmul])
  exact ⟨v, hv⟩

theorem mem_torsionBy (P : Pres M n V) (v : V) : P.ι v ∈ torsionBy ℤ M ((n : ℕ) : ℤ) :=
  (mem_torsionBy_iff _ _).2 ((P.hιr _).1 ⟨v, rfl⟩)

noncomputable def equiv (P : Pres M n V) : V ≃ torsionBy ℤ M ((n : ℕ) : ℤ) :=
  Equiv.ofBijective (fun v => ⟨P.ι v, P.mem_torsionBy v⟩)
    ⟨fun v w h => P.hι (Subtype.ext_iff.1 h), fun x => by
      obtain ⟨v, hv⟩ := (P.hιr x.1).2 ((mem_torsionBy_iff _ _).1 x.2)
      exact ⟨v, Subtype.ext hv⟩⟩

theorem natCard_eq (P : Pres M n V) : Nat.card V = Nat.card (torsionBy ℤ M ((n : ℕ) : ℤ)) :=
  Nat.card_congr P.equiv

variable (M) in

def self (n : ℕ) : Pres M n (torsionBy ℤ M ((n : ℕ) : ℤ)) where
  ι := (torsionBy ℤ M ((n : ℕ) : ℤ)).subtype.toAddMonoidHom
  hι := Subtype.val_injective
  hιr x := by
    constructor
    · rintro ⟨v, rfl⟩
      exact (mem_torsionBy_iff _ _).1 v.2
    · intro hx
      exact ⟨⟨x, (mem_torsionBy_iff _ _).2 hx⟩, rfl⟩

end Pres

section S

variable {M : Type*} [AddCommGroup M] (ℓ m : ℕ)

theorem nsmul_mem_torsionBy_pow {x : M} (hx : x ∈ torsionBy ℤ M ((ℓ ^ (m + 1) : ℕ) : ℤ)) :
    ℓ • x ∈ torsionBy ℤ M ((ℓ ^ m : ℕ) : ℤ) := by
  rw [mem_torsionBy_iff, natCast_zsmul] at hx ⊢
  rwa [← mul_smul, ← pow_succ]

def mulL : torsionBy ℤ M ((ℓ ^ (m + 1) : ℕ) : ℤ) →ₗ[ℤ] torsionBy ℤ M ((ℓ ^ m : ℕ) : ℤ) where
  toFun x := ⟨ℓ • (x : M), nsmul_mem_torsionBy_pow ℓ m x.2⟩
  map_add' x y := by
    apply Subtype.ext
    change ℓ • ((x : M) + y) = ℓ • (x : M) + ℓ • (y : M)
    exact smul_add ℓ (x : M) y
  map_smul' c x := by
    apply Subtype.ext
    change ℓ • (c • (x : M)) = c • (ℓ • (x : M))
    exact smul_comm ℓ c (x : M)

@[scoped simp] theorem coe_mulL (x : torsionBy ℤ M ((ℓ ^ (m + 1) : ℕ) : ℤ)) :
    ((mulL ℓ m x : torsionBy ℤ M ((ℓ ^ m : ℕ) : ℤ)) : M) = ℓ • (x : M) := rfl

theorem natCard_ker_mulL :
    Nat.card (LinearMap.ker (mulL (M := M) ℓ m)) =
      Nat.card (torsionBy ℤ M ((ℓ ^ 1 : ℕ) : ℤ)) := by
  refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨x.1.1, ?_⟩) ⟨?_, ?_⟩)
  · have hx := x.2
    rw [LinearMap.mem_ker, Subtype.ext_iff, coe_mulL] at hx
    rw [mem_torsionBy_iff, natCast_zsmul, pow_one]
    exact hx
  · intro x y h
    exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))
  · rintro ⟨y, hy⟩
    rw [mem_torsionBy_iff, natCast_zsmul, pow_one] at hy
    have hy' : y ∈ torsionBy ℤ M ((ℓ ^ (m + 1) : ℕ) : ℤ) := by
      rw [mem_torsionBy_iff, natCast_zsmul, pow_succ, mul_smul, hy, smul_zero]
    refine ⟨⟨⟨y, hy'⟩, ?_⟩, rfl⟩
    rw [LinearMap.mem_ker, Subtype.ext_iff, coe_mulL]
    exact hy

variable (r : ℕ)

theorem mulL_surjective (hℓ : 0 < ℓ)
    (h1 : Nat.card (torsionBy ℤ M ((ℓ ^ 1 : ℕ) : ℤ)) = (ℓ ^ 1) ^ r)
    (hm : Nat.card (torsionBy ℤ M ((ℓ ^ m : ℕ) : ℤ)) = (ℓ ^ m) ^ r)
    (hm1 : Nat.card (torsionBy ℤ M ((ℓ ^ (m + 1) : ℕ) : ℤ)) = (ℓ ^ (m + 1)) ^ r) :
    Surjective (mulL (M := M) ℓ m) := by
  set f := mulL (M := M) ℓ m with hf
  have hℓ0 : ℓ ≠ 0 := hℓ.ne'
  haveI hfin1 : Finite (torsionBy ℤ M ((ℓ ^ (m + 1) : ℕ) : ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [hm1]; positivity)
  haveI hfin0 : Finite (torsionBy ℤ M ((ℓ ^ m : ℕ) : ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [hm]; positivity)

  have hmul := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  rw [Nat.card_congr f.quotKerEquivRange.toEquiv, hm1, natCard_ker_mulL, h1] at hmul

  have hrange : Nat.card (LinearMap.range f) = (ℓ ^ m) ^ r := by
    have h : (ℓ ^ 1) ^ r * Nat.card (LinearMap.range f) = (ℓ ^ 1) ^ r * (ℓ ^ m) ^ r := by
      rw [← hmul, ← mul_pow, pow_one, ← pow_succ']
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h

  have hbij : Bijective (LinearMap.range f).subtype :=
    (LinearMap.range f).injective_subtype.bijective_of_nat_card_le (by rw [hrange, hm])
  intro y
  obtain ⟨⟨z, x, rfl⟩, hz⟩ := hbij.2 y
  exact ⟨x, hz⟩

end S

end P2mLwS
p2m_reactivate "P2MW.S_AddCommGroup_exists_mem_torsionBy_smul_eq_of_card_torsionBy.P2mLwS"

theorem solution (ℓ : ℕ) [Fact ℓ.Prime] {M : Type*} [AddCommGroup M] (r m : ℕ)
    (hcard : ∀ j ≤ m + 1, Nat.card (Submodule.torsionBy ℤ M ((ℓ ^ j : ℕ) : ℤ)) = (ℓ ^ j) ^ r)
    (x : M) (hx : x ∈ Submodule.torsionBy ℤ M ((ℓ ^ m : ℕ) : ℤ)) :
    ∃ y ∈ Submodule.torsionBy ℤ M ((ℓ ^ (m + 1) : ℕ) : ℤ), ℓ • y = x := by
  have hm : m ≤ m + 1 := Nat.le_succ m
  have h1 : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
  obtain ⟨⟨y, hy⟩, hyx⟩ := P2mLwS.mulL_surjective ℓ m r (Fact.out : ℓ.Prime).pos (hcard 1 h1)
    (hcard m hm) (hcard (m + 1) le_rfl) ⟨x, hx⟩
  exact ⟨y, hy, Subtype.ext_iff.1 hyx⟩

end S_AddCommGroup_exists_mem_torsionBy_smul_eq_of_card_torsionBy
end P2MW
export P2MW.S_AddCommGroup_exists_mem_torsionBy_smul_eq_of_card_torsionBy (solution)
