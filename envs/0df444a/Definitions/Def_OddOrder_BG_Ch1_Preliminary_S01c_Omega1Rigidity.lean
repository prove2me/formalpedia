-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S01c_Omega1Rigidity
-- name    : OddOrder_BG_Ch1_Preliminary_S01c_Omega1Rigidity
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:44:11.574029+00:00
-- url     : https://prove2.me/theorems/aac23043-40f1-4e91-9b1a-4c8d68712ff9
-- title:
--   BG §1: coprime $\Omega_1$-rigidity (Theorem 1.11, Corollary 1.12)
-- statement:
--   Formalizes Theorem 1.11 and Corollary 1.12 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §1. Theorem 1.11 (Gorenstein 5.3.10): a $p'$-group of operators on an odd $p$-group that acts trivially on $\Omega_1$ acts trivially everywhere. Corollary 1.12 concerns an elementary abelian subgroup $E$ and a $p'$-group of operators ($p$ odd) fixing every order-$p$ element.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S01c_Omega1Rigidity.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S01c_Omega1Rigidity.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S01_Solvable
import Definitions.Def_OddOrder_GroupTheory_CriticalSubgroup

namespace OddOrder.BG.Ch1.S01

open OddOrder.GroupTheory

open OddOrder.Isaacs.Ch03 (IsAInvariant)

variable {A G : Type*} [Group A] [Group G]

/-- **BG Theorem 1.11** (mmd L453, Gorenstein 5.3.10): let `p` be an odd prime, `P` a finite
`p`-group, and `A` a finite `p′`-group of operators on `P` (`φ : A →* MulAut P`, `p ∤ |A|`)
that fixes every element of order dividing `p` (i.e. acts trivially on `Ω₁(P)`). Then `A` acts
trivially on `P`.

Each `φ a` lies in `autFixerOfOrderP P p`, a `p`-group (`isPGroup_autFixerOfOrderP`), so
`orderOf (φ a)` is a power of `p`; but it also divides `|A|`, which is prime to `p`. Hence
`orderOf (φ a) = 1`, i.e. `φ a = 1`. -/
theorem actsTrivially_of_fixes_omega1 {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (hp_odd : p ≠ 2) (hP : IsPGroup p P) [Finite A] (hA_p' : ¬ p ∣ Nat.card A)
    (φ : A →* MulAut P) (htriv : ∀ a : A, ∀ g : P, g ^ p = 1 → φ a g = g) :
    ∀ a : A, ∀ g : P, φ a g = g := by
  have key : ∀ a : A, φ a = 1 := by
    intro a
    have hmem : φ a ∈ autFixerOfOrderP P p := fun g hg => htriv a g hg
    -- `φ a` has `p`-power order (element of the `p`-group `autFixerOfOrderP P p`).
    obtain ⟨k, hk⟩ := (isPGroup_autFixerOfOrderP hp_odd hP) ⟨φ a, hmem⟩
    have hpow : (φ a) ^ (p ^ k) = 1 := by
      have h := hk
      rwa [← OneMemClass.coe_eq_one, Subgroup.coe_pow] at h
    have hord_dvd_pk : orderOf (φ a) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hpow
    -- `orderOf (φ a)` also divides `|A|`, which is prime to `p`.
    have hord_dvd_A : orderOf (φ a) ∣ Nat.card A :=
      dvd_trans (orderOf_map_dvd φ a) (orderOf_dvd_natCard a)
    have hord1 : orderOf (φ a) = 1 := by
      by_contra h1
      obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd h1
      have hqp : q = p :=
        (Nat.prime_dvd_prime_iff_eq hq_prime Fact.out).mp
          (hq_prime.dvd_of_dvd_pow (dvd_trans hq_dvd hord_dvd_pk))
      exact hA_p' (hqp ▸ dvd_trans hq_dvd hord_dvd_A)
    exact orderOf_eq_one_iff.mp hord1
  intro a g
  rw [key a, MulAut.one_apply]

/-- **BG Theorem 1.11, subgroup form**: the same statement restricted to an `A`-invariant
`p`-subgroup `H ≤ G` (`G` itself need not be a `p`-group, only `H`). If `A` (a `p′`-group of
operators, `p` odd) fixes every order-`p` element of `H`, then `A` fixes `H` pointwise. -/
theorem actsTrivially_on_of_fixes_omega1 {p : ℕ} [Fact p.Prime] [Finite G]
    (hp_odd : p ≠ 2) (hG : IsPGroup p G) [Finite A] (hA_p' : ¬ p ∣ Nat.card A)
    (φ : A →* MulAut G) {H : Subgroup G} (hH_inv : IsAInvariant φ H)
    (hfix : ∀ a : A, ∀ g ∈ H, g ^ p = 1 → φ a g = g) :
    ∀ a : A, ∀ g ∈ H, φ a g = g := by
  have hHp : IsPGroup p ↥H := hG.to_subgroup H
  have habs : ∀ a : A, ∀ x : ↥H, (hH_inv.restrict a) x = x := by
    refine actsTrivially_of_fixes_omega1 hp_odd hHp hA_p' hH_inv.restrict ?_
    intro a x hxp
    apply Subtype.ext
    rw [hH_inv.restrict_apply_val a x]
    exact hfix a (x : G) x.2 (by simpa using Subtype.ext_iff.mp hxp)
  intro a g hg
  have h2 := congrArg Subtype.val (habs a ⟨g, hg⟩)
  rwa [hH_inv.restrict_apply_val a ⟨g, hg⟩] at h2

/-- **BG Corollary 1.12** (mmd L457): `p` odd, `G` a finite `p`-group, `E ≤ G` elementary
abelian, and `A` a finite `p′`-group of operators on `G` that fixes every element of order
dividing `p` in `C_G(E)`. Then `A` acts trivially on `G`.

Proof (mmd L459): with `C = C_G(A) = fixedPointsOfMulAut φ`, the elementary abelian `E` lies
in `C` (its elements have order `∣ p` and centralize `E`, so the hypothesis fixes them); hence
`C_G(C) ⊆ C_G(E)`, so `A` fixes every order-`p` element of `C_G(C)`, whence `A` fixes `C_G(C)`
pointwise by Theorem 1.11, i.e. `C_G(C) ⊆ C`. Proposition 1.10 then gives the conclusion. -/
theorem actsTrivially_of_fixes_omega1_centralizer {p : ℕ} [Fact p.Prime] [Finite G]
    (hp_odd : p ≠ 2) (hG : IsPGroup p G) [Finite A] (hA_p' : ¬ p ∣ Nat.card A)
    (φ : A →* MulAut G) {E : Subgroup G} (hE : E.IsElementaryAbelian p)
    (hfix : ∀ a : A, ∀ g ∈ Subgroup.centralizer (E : Set G), g ^ p = 1 → φ a g = g) :
    ∀ a : A, ∀ g : G, φ a g = g := by
  have : Group.IsNilpotent G := hG.isNilpotent
  set C := Subgroup.fixedPointsOfMulAut φ with hC
  have hC_inv : IsAInvariant φ C := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a g hg
    rw [hC, Subgroup.mem_fixedPointsOfMulAut] at hg ⊢
    intro a'
    rw [hg a, hg a']
  -- `E ≤ C`: each `e ∈ E` has order `∣ p`, centralizes `E`, hence is fixed by `A`.
  have hE_le_C : E ≤ C := by
    intro e he
    rw [hC, Subgroup.mem_fixedPointsOfMulAut]
    intro a
    refine hfix a e ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subtype.ext_iff.mp (hE.1 ⟨x, hx⟩ ⟨e, he⟩)
    · exact Subtype.ext_iff.mp (hE.2 ⟨e, he⟩)
  -- `C_G(C) ≤ C_G(E)` (antitone in the subset `E ⊆ C`).
  have hCC_le_CE : Subgroup.centralizer (C : Set G) ≤ Subgroup.centralizer (E : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    intro e he
    exact hg e (hE_le_C he)
  -- `C_G(C) ≤ C` via Theorem 1.11 applied to the `A`-invariant `p`-subgroup `C_G(C)`.
  have hCC_le_C : Subgroup.centralizer (C : Set G) ≤ C := by
    intro g hg
    rw [hC, Subgroup.mem_fixedPointsOfMulAut]
    intro a
    exact actsTrivially_on_of_fixes_omega1 hp_odd hG hA_p' φ hC_inv.centralizer
      (fun a' g' hg' hg'p => hfix a' g' (hCC_le_CE hg') hg'p) a g hg
  -- Proposition 1.10 closes the argument (`G` nilpotent, coprime action, `C` self-centralizing).
  obtain ⟨k, hk⟩ := hG.exists_card_eq
  have hCop : Nat.Coprime (Nat.card A) (Nat.card G) := by
    rw [hk]
    exact (Nat.coprime_comm.mp ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hA_p')).pow_right k
  exact coprime_nilpotent_acts_trivially_of_centralizer_self hCop hCC_le_C

end OddOrder.BG.Ch1.S01


