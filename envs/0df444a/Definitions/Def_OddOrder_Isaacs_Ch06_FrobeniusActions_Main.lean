-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_Main
-- name    : OddOrder_Isaacs_Ch06_FrobeniusActions_Main
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:43:30.141698+00:00
-- url     : https://prove2.me/theorems/3ed51b29-31a6-4e1f-ad32-339ce552cab2
-- title:
--   Isaacs Ch. 6: Frobenius actions (main file)
-- statement:
--   The main file of the Chapter 6 (Frobenius Actions) formalization of Isaacs, *Finite Group Theory* (pp. 177–200). The chapter splits into 6A (definition and equivalences, 6.1–6.7), 6B (Sylow structure of Frobenius complements, 6.8–6.21) and 6C (Frobenius kernel nilpotent and Thompson, 6.22–6.24). Mathlib lacks Frobenius groups and actions, so they are defined here, with an action-based core (`IsFrobeniusAction`) and the subgroup-pair version derived via conjugation.
--
--   This file holds the Lemma 6.15 dispatch, the Thm 6.12 congruence and the Thm 6.11 route, and consists of lemmas only, such as existence of characteristic elementary abelian subgroups of order $p^2$ under various hypotheses.
--
--   The bundle also proves 28 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch06_FrobeniusActions/Main.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch06_FrobeniusActions/Main.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_Lemma615

namespace OddOrder.Isaacs.Ch06

open OddOrder.GroupTheory

/-- **Isaacs Lemma 6.15**.

Let `T` be a finite `p`-group with order different from `8`, and suppose
`|T : Z(T)| = p²`. If `C` is cyclic and `Z(T) < C < T`, then `T` contains a
characteristic elementary abelian subgroup of order `p²`.

The proof dispatches to the already-formalized odd-prime branch and the separate `p = 2`
center-index-four branch. -/
theorem exists_characteristic_isElementaryAbelian_of_center_index_prime_sq
    {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]
    (hT : IsPGroup p T) (hT_card_ne : Nat.card T ≠ 8)
    (h_idx : (Subgroup.center T).index = p ^ 2)
    {C : Subgroup T} (hC_cyclic : IsCyclic C)
    (hZ_lt_C : Subgroup.center T < C) (hC_lt_T : C < ⊤) :
    ∃ K : Subgroup T, K.Characteristic ∧
      IsElementaryAbelian p K ∧ Nat.card K = p ^ 2 := by
  rcases (Fact.out : p.Prime).eq_two_or_odd' with hp_two | hp_odd
  · subst p
    simpa using
      exists_characteristic_isElementaryAbelian_four_of_center_index_four
        hT hT_card_ne h_idx hC_cyclic hC_lt_T hZ_lt_C
  · exact exists_characteristic_isElementaryAbelian_of_center_index_prime_sq_odd
      hp_odd h_idx hC_cyclic hZ_lt_C hC_lt_T

/-- **Isaacs Thm 6.12 setup**: Lemma 6.15 applied to an ambient self-centralizing
subgroup `C ≤ T ≤ P`.

In the proof of Thm 6.12, after choosing `T/C` of order `p`, this packages the
translation from the ambient cyclic self-centralizing subgroup `C : Subgroup P` to the
subgroup `C.subgroupOf T` required by Lemma 6.15. -/
theorem exists_characteristic_isElementaryAbelian_of_self_centralizing_relIndex_prime
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    {C T : Subgroup P} [C.Normal]
    (hT : IsPGroup p T) (hT_card_ne : Nat.card T ≠ 8)
    (h_idx : (Subgroup.center T).index = p ^ 2)
    (hC_le_T : C ≤ T) (hCent : Subgroup.centralizer (C : Set P) = C)
    (hC_rel : C.relIndex T = p) (hC_cyclic : IsCyclic C)
    (hT_not_comm : ¬ IsMulCommutative T) :
    ∃ K : Subgroup T, K.Characteristic ∧
      IsElementaryAbelian p K ∧ Nat.card K = p ^ 2 := by
  have hZ_lt_C : Subgroup.center T < C.subgroupOf T :=
    center_lt_subgroupOf_of_self_centralizing_of_relIndex_prime_of_not_isMulCommutative
      hC_le_T hCent hC_rel hT_not_comm
  have hCsub_index : (C.subgroupOf T).index = p := by
    simpa [Subgroup.relIndex] using hC_rel
  have hCsub_lt_top : C.subgroupOf T < ⊤ := by
    refine lt_of_le_of_ne le_top ?_
    intro htop
    have hidx_one : (C.subgroupOf T).index = 1 := by
      rw [htop, Subgroup.index_top]
    exact (Fact.out : p.Prime).ne_one (hCsub_index.symm.trans hidx_one)
  have hCsub_cyclic : IsCyclic (C.subgroupOf T) :=
    subgroupOf_isCyclic_of_isCyclic hC_cyclic
  exact exists_characteristic_isElementaryAbelian_of_center_index_prime_sq
    hT hT_card_ne h_idx hCsub_cyclic hZ_lt_C hCsub_lt_top

/-- **Isaacs Thm 6.12 setup**: Lemma 6.15 applied after the `c^p ∈ Z(T)` index
calculation.

This packages the proof step where `C = ⟨c⟩`, `|T : C| = p`, and `c^p ∈ Z(T)` give
`|T : Z(T)| = p²`, so the characteristic elementary abelian subgroup supplied by
Lemma 6.15 can be invoked. -/
theorem exists_characteristic_isElementaryAbelian_of_zpowers_relIndex_pow_mem_center
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    {C T : Subgroup P} [C.Normal] {c : P}
    (hT : IsPGroup p T) (hT_card_ne : Nat.card T ≠ 8)
    (hC_eq : C = Subgroup.zpowers c) (hcT : c ∈ T)
    (hC_le_T : C ≤ T) (hCent : Subgroup.centralizer (C : Set P) = C)
    (hC_rel : C.relIndex T = p) (hT_not_comm : ¬ IsMulCommutative T)
    (hcp : (⟨c, hcT⟩ : T) ^ p ∈ Subgroup.center T) :
    ∃ K : Subgroup T, K.Characteristic ∧
      IsElementaryAbelian p K ∧ Nat.card K = p ^ 2 := by
  let cT : T := ⟨c, hcT⟩
  have hCsub_eq : C.subgroupOf T = Subgroup.zpowers cT := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [hC_eq] at hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨k, ?_⟩
      apply Subtype.ext
      simpa [cT] using hk
    · intro hx
      rw [Subgroup.mem_subgroupOf, hC_eq]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have hk_val := congrArg Subtype.val hk
      simpa [cT] using hk_val
  have hZ_lt_C : Subgroup.center T < C.subgroupOf T :=
    center_lt_subgroupOf_of_self_centralizing_of_relIndex_prime_of_not_isMulCommutative
      hC_le_T hCent hC_rel hT_not_comm
  have hZ_lt_zpowers : Subgroup.center T < Subgroup.zpowers cT := by
    simpa [hCsub_eq] using hZ_lt_C
  have hZ_rel_zpowers : (Subgroup.center T).relIndex (Subgroup.zpowers cT) = p :=
    center_relIndex_zpowers_eq_prime_of_pow_mem_center hT hZ_lt_zpowers hcp
  have hZ_rel_C : (Subgroup.center T).relIndex (C.subgroupOf T) = p := by
    simpa [hCsub_eq] using hZ_rel_zpowers
  have h_idx : (Subgroup.center T).index = p ^ 2 :=
    center_index_eq_prime_sq_of_subgroupOf_relIndex_prime hC_rel hZ_lt_C.le hZ_rel_C
  have hC_cyclic : IsCyclic C := by
    rw [hC_eq]
    exact Subgroup.isCyclic_zpowers c
  exact exists_characteristic_isElementaryAbelian_of_self_centralizing_relIndex_prime
    hT hT_card_ne h_idx hC_le_T hCent hC_rel hC_cyclic hT_not_comm

/-- **Isaacs Thm 6.12 setup**: if every normal abelian subgroup of `P` is cyclic, then a
normal subgroup `T` has no characteristic elementary abelian subgroup of order `p²`.

Indeed, such a subgroup is normal in `P` because it is characteristic in `T` and `T ⊴ P`;
as an elementary abelian group of order `p²`, it is not cyclic. -/
theorem not_exists_characteristic_isElementaryAbelian_card_prime_sq_of_normal_abelian_cyclic
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime] {T : Subgroup P}
    (hT_normal : T.Normal)
    (hcyc : ∀ B : Subgroup P, B.Normal → IsMulCommutative B → IsCyclic B) :
    ¬ ∃ K : Subgroup T, K.Characteristic ∧
      IsElementaryAbelian p K ∧ Nat.card K = p ^ 2 := by
  rintro ⟨K, hK_char, hK_elem, hK_card⟩
  let B : Subgroup P := K.map T.subtype
  have : T.Normal := hT_normal
  have : K.Characteristic := hK_char
  have hB_normal : B.Normal := by
    dsimp [B]
    infer_instance
  have hB_elem : IsElementaryAbelian p B := by
    dsimp [B]
    exact isElementaryAbelian_of_mulEquiv
      (Subgroup.equivMapOfInjective K T.subtype T.subtype_injective) hK_elem
  have hB_comm : IsMulCommutative B := ⟨⟨fun x y => hB_elem.comm x y⟩⟩
  have hB_card : Nat.card B = p ^ 2 := by
    dsimp [B]
    rw [Subgroup.card_subtype, hK_card]
  exact (hB_elem.not_isCyclic_of_card_prime_sq (Fact.out : p.Prime) hB_card)
    (hcyc B hB_normal hB_comm)

/-- **Isaacs Thm 6.12 setup**: under the normal-abelian-cyclic hypothesis, the element
`c^p` is not central in `T` in the main 6.12 configuration.

This is the sentence in the proof of Theorem 6.12 where Lemma 6.15 is applied by
contradiction: if `c^p ∈ Z(T)`, the preceding bridge produces a characteristic elementary
abelian subgroup of `T` of order `p²`, contradicting the ambient hypothesis. -/
theorem pow_not_mem_center_of_zpowers_relIndex_of_normal_abelian_cyclic
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    {C T : Subgroup P} [C.Normal] {c : P}
    (hT : IsPGroup p T) (hT_card_ne : Nat.card T ≠ 8)
    (hT_normal : T.Normal)
    (hcyc : ∀ B : Subgroup P, B.Normal → IsMulCommutative B → IsCyclic B)
    (hC_eq : C = Subgroup.zpowers c) (hcT : c ∈ T)
    (hC_le_T : C ≤ T) (hCent : Subgroup.centralizer (C : Set P) = C)
    (hC_rel : C.relIndex T = p) (hT_not_comm : ¬ IsMulCommutative T) :
    (⟨c, hcT⟩ : T) ^ p ∉ Subgroup.center T := by
  intro hcp
  have h_exists :
      ∃ K : Subgroup T, K.Characteristic ∧
        IsElementaryAbelian p K ∧ Nat.card K = p ^ 2 :=
    exists_characteristic_isElementaryAbelian_of_zpowers_relIndex_pow_mem_center
      hT hT_card_ne hC_eq hcT hC_le_T hCent hC_rel hT_not_comm hcp
  exact
    (not_exists_characteristic_isElementaryAbelian_card_prime_sq_of_normal_abelian_cyclic
      hT_normal hcyc) h_exists

/-- **Isaacs Thm 6.12 setup**: if conjugation by `a` sends `c` to `c^i`, then it sends
`c^k` to `c^(i*k)`. -/
private lemma conj_zpow_eq_zpow_mul_of_conj_eq_zpow
    {G : Type*} [Group G] {a c : G} {i k : ℤ}
    (h_conj : a * c * a⁻¹ = c ^ i) :
    a * c ^ k * a⁻¹ = c ^ (i * k) := by
  have hmap : a * c ^ k * a⁻¹ = (a * c * a⁻¹) ^ k := by
    simp
  rw [hmap, h_conj, zpow_mul]

/-- **Isaacs Thm 6.12 setup**: iterating the conjugation exponent. -/
private lemma conj_pow_eq_zpow_pow_of_conj_eq_zpow
    {G : Type*} [Group G] {a c : G} {i : ℤ}
    (h_conj : a * c * a⁻¹ = c ^ i) (n : ℕ) :
    a ^ n * c * (a ^ n)⁻¹ = c ^ (i ^ n : ℤ) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        a ^ (n + 1) * c * (a ^ (n + 1))⁻¹ =
            a * (a ^ n * c * (a ^ n)⁻¹) * a⁻¹ := by
          rw [pow_succ']
          group
        _ = a * c ^ (i ^ n : ℤ) * a⁻¹ := by rw [ih]
        _ = c ^ (i * (i ^ n : ℤ)) :=
          conj_zpow_eq_zpow_mul_of_conj_eq_zpow h_conj
        _ = c ^ (i ^ (n + 1) : ℤ) := by
          congr 1
          rw [pow_succ']

/-- **Isaacs Thm 6.12 setup**: if `aC = (bC)^2` in `P/C`, and conjugation by
`a` and `b` sends `c` to `c^i` and `c^j`, respectively, then `i ≡ j² (mod |c|)`.

This is the square-root bridge used after the cyclic quotient step: an element of `C = ⟨c⟩`
commutes with every power of `c`, so replacing `a` by a representative `c^m * b²` makes
conjugation by `a` agree with conjugation by `b²` on `c`. -/
theorem conj_exponent_modEq_sq_of_quotient_sq_eq
    {P : Type*} [Group P] {C : Subgroup P} [C.Normal] {a b c : P} {i j : ℤ}
    (hC_eq : C = Subgroup.zpowers c)
    (hquot : QuotientGroup.mk' C a = (QuotientGroup.mk' C b) ^ 2)
    (h_conj_a : a * c * a⁻¹ = c ^ i)
    (h_conj_b : b * c * b⁻¹ = c ^ j) :
    i ≡ j ^ 2 [ZMOD orderOf c] := by
  classical
  have hquot' : QuotientGroup.mk' C a = QuotientGroup.mk' C (b ^ 2) := by
    simpa [QuotientGroup.mk_pow] using hquot
  have hdiv : a / b ^ 2 ∈ C :=
    (QuotientGroup.eq_iff_div_mem (N := C)).mp hquot'
  have hz_mem : a / b ^ 2 ∈ Subgroup.zpowers c := by
    simpa [hC_eq] using hdiv
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hz_mem
  have ha_eq : a = c ^ m * b ^ 2 := by
    calc
      a = (a / b ^ 2) * b ^ 2 := by
        rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel, mul_one]
      _ = c ^ m * b ^ 2 := by rw [← hm]
  have hb2_conj : b ^ 2 * c * (b ^ 2)⁻¹ = c ^ (j ^ 2 : ℤ) :=
    conj_pow_eq_zpow_pow_of_conj_eq_zpow h_conj_b 2
  have hsame : a * c * a⁻¹ = b ^ 2 * c * (b ^ 2)⁻¹ := by
    rw [ha_eq]
    calc
      (c ^ m * b ^ 2) * c * (c ^ m * b ^ 2)⁻¹ =
          c ^ m * (b ^ 2 * c * (b ^ 2)⁻¹) * (c ^ m)⁻¹ := by
        group
      _ = c ^ m * c ^ (j ^ 2 : ℤ) * (c ^ m)⁻¹ := by rw [hb2_conj]
      _ = c ^ (j ^ 2 : ℤ) := by
        have hcomm : Commute (c ^ m) (c ^ (j ^ 2 : ℤ)) :=
          (Commute.zpow_self c m).zpow_right (j ^ 2 : ℤ)
        rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
      _ = b ^ 2 * c * (b ^ 2)⁻¹ := hb2_conj.symm
  have hpow_eq : c ^ i = c ^ (j ^ 2 : ℤ) := by
    rw [← h_conj_a, hsame, hb2_conj]
  rw [← zpow_eq_zpow_iff_modEq]
  exact hpow_eq

/-- **Isaacs Thm 6.12 setup**: if `a^p ∈ ⟨c⟩` and conjugation by `a` sends `c` to
`c^i`, then `i^p ≡ 1 (mod |c|)`.

In the proof of Theorem 6.12 this is the line `c = c^{a^p} = c^{i^p}`. -/
theorem conj_exponent_pow_modEq_one_of_pow_mem_zpowers
    {G : Type*} [Group G] {p e : ℕ} {a c : G} {i : ℤ}
    (h_order : orderOf c = p ^ e)
    (h_conj : a * c * a⁻¹ = c ^ i)
    (ha_pow : a ^ p ∈ Subgroup.zpowers c) :
    i ^ p ≡ 1 [ZMOD ((p : ℤ) ^ e)] := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp ha_pow
  have hcomm : a ^ p * c * (a ^ p)⁻¹ = c := by
    rw [← hm]
    have hzc : c ^ m * c = c * c ^ m := (Commute.zpow_self c m).eq
    calc
      c ^ m * c * (c ^ m)⁻¹ = c * c ^ m * (c ^ m)⁻¹ := by rw [hzc]
      _ = c := by simp [mul_assoc]
  have hiter : a ^ p * c * (a ^ p)⁻¹ = c ^ (i ^ p : ℤ) :=
    conj_pow_eq_zpow_pow_of_conj_eq_zpow h_conj p
  have hpow_eq : c ^ (i ^ p : ℤ) = c := hiter.symm.trans hcomm
  have hmod : i ^ p ≡ (1 : ℤ) [ZMOD orderOf c] := by
    rw [← zpow_eq_zpow_iff_modEq]
    simpa using hpow_eq
  simpa [h_order] using hmod

/-- **Isaacs Thm 6.12 setup**: if conjugation by `a` does not fix `c^p`, the exponent `i`
cannot be `1` modulo `p^(e-1)`. -/
theorem conj_exponent_not_modEq_one_of_pow_conj_ne
    {G : Type*} [Group G] {p e : ℕ} (he : 0 < e)
    {a c : G} {i : ℤ}
    (h_order : orderOf c = p ^ e)
    (h_conj : a * c * a⁻¹ = c ^ i)
    (hpow_ne : a * c ^ p * a⁻¹ ≠ c ^ p) :
    ¬ i ≡ 1 [ZMOD ((p : ℤ) ^ (e - 1))] := by
  intro hmod
  have hmod_mul : i * (p : ℤ) ≡ (p : ℤ) [ZMOD ((p : ℤ) ^ e)] := by
    obtain ⟨m, hm⟩ := hmod.symm.dvd
    refine Int.modEq_iff_dvd.mpr ?_
    refine ⟨-m, ?_⟩
    have hpow : (p : ℤ) ^ e = (p : ℤ) ^ (e - 1) * (p : ℤ) := by
      rw [← pow_succ, Nat.sub_add_cancel he]
    calc
      (p : ℤ) - i * (p : ℤ)
          = -((i - 1) * (p : ℤ)) := by ring
      _ = -(((p : ℤ) ^ (e - 1) * m) * (p : ℤ)) := by rw [hm]
      _ = ((p : ℤ) ^ e) * -m := by
        rw [hpow]
        ring
  have hmod_order : i * (p : ℤ) ≡ (p : ℤ) [ZMOD orderOf c] := by
    simpa [h_order] using hmod_mul
  have hfix : a * c ^ p * a⁻¹ = c ^ p := by
    calc
      a * c ^ p * a⁻¹ = a * c ^ (p : ℤ) * a⁻¹ := by rw [zpow_natCast]
      _ = c ^ (i * (p : ℤ)) :=
        conj_zpow_eq_zpow_mul_of_conj_eq_zpow h_conj
      _ = c ^ (p : ℤ) := by
        rw [zpow_eq_zpow_iff_modEq]
        exact hmod_order
      _ = c ^ p := by rw [zpow_natCast]
  exact hpow_ne hfix

/-- **Isaacs Thm 6.12 setup**: the Lemma 6.16 dispatch for the conjugation exponent.

From `a^p ∈ ⟨c⟩`, conjugation by `a` as `c ↦ c^i`, and non-fixity of `c^p`, Lemma 6.16
forces `p = 2` and leaves only the two `2`-adic alternatives for `i`. -/
theorem conj_exponent_two_cases_of_pow_mem_zpowers_of_pow_conj_ne
    {G : Type*} [Group G] {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    {a c : G} {i : ℤ}
    (h_order : orderOf c = p ^ e)
    (h_conj : a * c * a⁻¹ = c ^ i)
    (ha_pow : a ^ p ∈ Subgroup.zpowers c)
    (hpow_ne : a * c ^ p * a⁻¹ ≠ c ^ p) :
    p = 2 ∧
      (i ≡ -1 [ZMOD ((2 : ℤ) ^ e)] ∨
        i ≡ ((2 : ℤ) ^ (e - 1) - 1) [ZMOD ((2 : ℤ) ^ e)]) := by
  have hpow_mod : i ^ p ≡ 1 [ZMOD ((p : ℤ) ^ e)] :=
    conj_exponent_pow_modEq_one_of_pow_mem_zpowers h_order h_conj ha_pow
  have hnot_mod :
      ¬ i ≡ 1 [ZMOD ((p : ℤ) ^ (e - 1))] :=
    conj_exponent_not_modEq_one_of_pow_conj_ne he h_order h_conj hpow_ne
  rcases pow_prime_modEq_one_cases hp he hpow_mod with hmod_one | htwo | htwo
  · exact (hnot_mod hmod_one).elim
  · exact ⟨htwo.1, Or.inl htwo.2⟩
  · exact ⟨htwo.1, Or.inr htwo.2⟩

/-- **Isaacs Thm 6.12 setup**: extracting the element `a` and conjugation exponent `i`
from the noncentrality of `c^p`.

Under the normal-abelian-cyclic hypothesis, the preceding Lemma 6.15 bridge shows that
`c^p` is not central in `T`. This theorem chooses an element `a ∈ T` witnessing that
noncentrality, proves `a ∉ C`, uses `|T : C| = p` to get `a^p ∈ C = ⟨c⟩`, writes
`a c a⁻¹ = c^i`, and dispatches Lemma 6.16 to obtain `p = 2` and the two 2-adic
alternatives for `i`. -/
theorem exists_conj_exponent_two_adic_cases_of_zpowers_relIndex_of_normal_abelian_cyclic
    {P : Type*} [Group P] [Finite P] {p e : ℕ} [hp : Fact p.Prime]
    {C T : Subgroup P} [C.Normal] {c : P}
    (hT : IsPGroup p T) (hT_card_ne : Nat.card T ≠ 8)
    (hT_normal : T.Normal)
    (hcyc : ∀ B : Subgroup P, B.Normal → IsMulCommutative B → IsCyclic B)
    (hC_eq : C = Subgroup.zpowers c) (hcT : c ∈ T)
    (hC_le_T : C ≤ T) (hCent : Subgroup.centralizer (C : Set P) = C)
    (hC_rel : C.relIndex T = p) (hT_not_comm : ¬ IsMulCommutative T)
    (h_order : orderOf c = p ^ e) (he : 0 < e) :
    ∃ a : P, ∃ i : ℤ, a ∈ T ∧ a ∉ C ∧ a ^ p ∈ C ∧
      a * c * a⁻¹ = c ^ i ∧ p = 2 ∧
        (i ≡ -1 [ZMOD ((2 : ℤ) ^ e)] ∨
          i ≡ ((2 : ℤ) ^ (e - 1) - 1) [ZMOD ((2 : ℤ) ^ e)]) := by
  classical
  let cT : T := ⟨c, hcT⟩
  have hc_pow_not_center : cT ^ p ∉ Subgroup.center T :=
    pow_not_mem_center_of_zpowers_relIndex_of_normal_abelian_cyclic
      hT hT_card_ne hT_normal hcyc hC_eq hcT hC_le_T hCent hC_rel hT_not_comm
  obtain ⟨aT, haT_noncomm⟩ : ∃ aT : T, aT * cT ^ p ≠ cT ^ p * aT := by
    by_contra hno
    push Not at hno
    apply hc_pow_not_center
    rw [Subgroup.mem_center_iff]
    intro x
    exact hno x
  let a : P := aT
  have haT : a ∈ T := aT.2
  have hpow_ne : a * c ^ p * a⁻¹ ≠ c ^ p := by
    intro hfix
    apply haT_noncomm
    apply Subtype.ext
    have hcommP : a * c ^ p = c ^ p * a := by
      calc
        a * c ^ p = (a * c ^ p * a⁻¹) * a := by group
        _ = c ^ p * a := by rw [hfix]
    simpa [a, cT] using hcommP
  have ha_notmem : a ∉ C := by
    intro haC
    apply hpow_ne
    have ha_z : a ∈ Subgroup.zpowers c := by
      simpa [hC_eq] using haC
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp ha_z
    rw [← hm]
    have hcomm : Commute (c ^ m) (c ^ p) :=
      (Commute.zpow_self c m).pow_right p
    rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  have ha_pow_C : a ^ p ∈ C := by
    have hpow := C.pow_relIndex_mem (K := T) haT
    simpa [hC_rel] using hpow
  have ha_pow_z : a ^ p ∈ Subgroup.zpowers c := by
    simpa [hC_eq] using ha_pow_C
  have hcC : c ∈ C := by
    rw [hC_eq]
    exact Subgroup.mem_zpowers c
  have h_conj_mem_C : a * c * a⁻¹ ∈ C := by
    exact (inferInstance : C.Normal).conj_mem c hcC a
  have h_conj_mem_z : a * c * a⁻¹ ∈ Subgroup.zpowers c := by
    simpa [hC_eq] using h_conj_mem_C
  obtain ⟨i, h_conj_symm⟩ := Subgroup.mem_zpowers_iff.mp h_conj_mem_z
  have h_conj : a * c * a⁻¹ = c ^ i := h_conj_symm.symm
  obtain ⟨hp_eq_two, hcases⟩ :=
    conj_exponent_two_cases_of_pow_mem_zpowers_of_pow_conj_ne
      (Fact.out : p.Prime) he h_order h_conj ha_pow_z hpow_ne
  exact ⟨a, i, haT, ha_notmem, ha_pow_C, h_conj, hp_eq_two, hcases⟩

/-- **Isaacs Thm 6.12 setup**: after excluding `|C| = 4`, the cyclic subgroup
`C = ⟨c⟩` has exponent at least `p³` in the main nonabelian branch.

The proof uses the Lemma 6.15 bridge `c^p ∉ Z(T)` to exclude `e = 0, 1`, while the
Lemma 6.16 exponent dispatch gives `p = 2`; then `e = 2` is exactly the excluded
`|C| = 4` case. -/
theorem three_le_exponent_of_zpowers_relIndex_of_normal_abelian_cyclic
    {P : Type*} [Group P] [Finite P] {p e : ℕ} [hp : Fact p.Prime]
    {C T : Subgroup P} [C.Normal] {c : P}
    (hT : IsPGroup p T) (hT_card_ne : Nat.card T ≠ 8)
    (hT_normal : T.Normal)
    (hcyc : ∀ B : Subgroup P, B.Normal → IsMulCommutative B → IsCyclic B)
    (hC_eq : C = Subgroup.zpowers c) (hcT : c ∈ T)
    (hC_le_T : C ≤ T) (hCent : Subgroup.centralizer (C : Set P) = C)
    (hC_rel : C.relIndex T = p) (hT_not_comm : ¬ IsMulCommutative T)
    (hC_card_ne : Nat.card C ≠ 4)
    (h_order : orderOf c = p ^ e) :
    3 ≤ e := by
  classical
  let cT : T := ⟨c, hcT⟩
  have hc_pow_not_center : cT ^ p ∉ Subgroup.center T :=
    pow_not_mem_center_of_zpowers_relIndex_of_normal_abelian_cyclic
      hT hT_card_ne hT_normal hcyc hC_eq hcT hC_le_T hCent hC_rel hT_not_comm
  have he_pos : 0 < e := by
    by_contra he_not
    have he0 : e = 0 := Nat.eq_zero_of_not_pos he_not
    have hc_one : c = 1 := by
      apply orderOf_eq_one_iff.mp
      rw [h_order, he0, pow_zero]
    have hcp_one : cT ^ p = 1 := by
      apply Subtype.ext
      simp [cT, hc_one]
    exact hc_pow_not_center (by rw [hcp_one]; exact Subgroup.one_mem _)
  obtain ⟨_a, _i, _haT, _ha_notmem, _ha_pow_C, _h_conj, hp_eq_two, _hcases⟩ :=
    exists_conj_exponent_two_adic_cases_of_zpowers_relIndex_of_normal_abelian_cyclic
      hT hT_card_ne hT_normal hcyc hC_eq hcT hC_le_T hCent hC_rel hT_not_comm
      h_order he_pos
  by_contra he_not
  have he_cases : e = 0 ∨ e = 1 ∨ e = 2 := by omega
  rcases he_cases with he0 | he1 | he2
  · omega
  · have hc_pow_one : c ^ p = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, h_order, he1, pow_one]
    have hcp_one : cT ^ p = 1 := by
      apply Subtype.ext
      simpa [cT] using hc_pow_one
    exact hc_pow_not_center (by rw [hcp_one]; exact Subgroup.one_mem _)
  · have hC_card : Nat.card C = 4 := by
      rw [hC_eq, Nat.card_zpowers, h_order, hp_eq_two, he2]
      norm_num
    exact hC_card_ne hC_card

/-- **Isaacs Thm 6.12 setup**: both `2`-adic alternatives from Lemma 6.16 make
`i * 2 ≡ -2 (mod 2^e)`. -/
private lemma mul_two_modEq_neg_two_of_two_adic_conj_cases
    {e : ℕ} (he : 0 < e) {i : ℤ}
    (hcases :
      i ≡ -1 [ZMOD ((2 : ℤ) ^ e)] ∨
        i ≡ ((2 : ℤ) ^ (e - 1) - 1) [ZMOD ((2 : ℤ) ^ e)]) :
    i * (2 : ℤ) ≡ (-2 : ℤ) [ZMOD ((2 : ℤ) ^ e)] := by
  rcases hcases with hi | hi
  · simpa using hi.mul_right (2 : ℤ)
  · have hrhs :
        ((2 : ℤ) ^ (e - 1) - 1) * (2 : ℤ) ≡
          (-2 : ℤ) [ZMOD ((2 : ℤ) ^ e)] := by
      refine Int.modEq_iff_dvd.mpr ?_
      refine ⟨-1, ?_⟩
      have hpow : (2 : ℤ) ^ e = (2 : ℤ) ^ (e - 1) * (2 : ℤ) := by
        rw [← pow_succ, Nat.sub_add_cancel he]
      rw [hpow]
      ring
    exact (hi.mul_right (2 : ℤ)).trans hrhs

/-- **Isaacs Thm 6.12 setup**: after the Lemma 6.16 dispatch, conjugation by `a`
inverts `c^2`.

This formalizes the sentence following the congruence computation in the proof of Theorem 6.12:
`i ≡ -1 (mod 2^(e-1))`, hence `(c^2)^a = (c^2)⁻¹`. -/
theorem conj_square_eq_inv_of_pow_mem_zpowers_of_pow_conj_ne
    {G : Type*} [Group G] {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    {a c : G} {i : ℤ}
    (h_order : orderOf c = p ^ e)
    (h_conj : a * c * a⁻¹ = c ^ i)
    (ha_pow : a ^ p ∈ Subgroup.zpowers c)
    (hpow_ne : a * c ^ p * a⁻¹ ≠ c ^ p) :
    p = 2 ∧ a * c ^ 2 * a⁻¹ = (c ^ 2)⁻¹ := by
  obtain ⟨hp_eq_two, hcases⟩ :=
    conj_exponent_two_cases_of_pow_mem_zpowers_of_pow_conj_ne
      hp he h_order h_conj ha_pow hpow_ne
  refine ⟨hp_eq_two, ?_⟩
  have hmod_two :
      i * (2 : ℤ) ≡ (-2 : ℤ) [ZMOD ((2 : ℤ) ^ e)] :=
    mul_two_modEq_neg_two_of_two_adic_conj_cases he hcases
  have hmod_order : i * (2 : ℤ) ≡ (-2 : ℤ) [ZMOD orderOf c] := by
    simpa [h_order, hp_eq_two] using hmod_two
  have hzpow : a * c ^ (2 : ℤ) * a⁻¹ = (c ^ (2 : ℤ))⁻¹ := by
    calc
      a * c ^ (2 : ℤ) * a⁻¹ = c ^ (i * (2 : ℤ)) :=
        conj_zpow_eq_zpow_mul_of_conj_eq_zpow h_conj
      _ = c ^ (-2 : ℤ) := by
        rw [zpow_eq_zpow_iff_modEq]
        exact hmod_order
      _ = (c ^ (2 : ℤ))⁻¹ := by rw [zpow_neg]
  simpa [zpow_ofNat] using hzpow

/-- **Isaacs Thm 6.12 setup**: normality of `C = ⟨c⟩` supplies the missing conjugation
exponent for the square-inversion step.

This is the quotient-involution bridge used later in Thm 6.12: once a representative `a`
has `a^p ∈ C` and does not fix `c^p`, normality of `C` writes `a c a⁻¹ = c^i`, so the
Lemma 6.16 dispatch inverts `c²`. -/
theorem conj_square_eq_inv_of_normal_zpowers_of_pow_mem_of_pow_conj_ne
    {G : Type*} [Group G] {p e : ℕ} (hp : p.Prime)
    {C : Subgroup G} [C.Normal] {a c : G}
    (hC_eq : C = Subgroup.zpowers c)
    (h_order : orderOf c = p ^ e) (he : 0 < e)
    (ha_pow : a ^ p ∈ C)
    (hpow_ne : a * c ^ p * a⁻¹ ≠ c ^ p) :
    p = 2 ∧ a * c ^ 2 * a⁻¹ = (c ^ 2)⁻¹ := by
  have hcC : c ∈ C := by
    rw [hC_eq]
    exact Subgroup.mem_zpowers c
  have h_conj_mem_C : a * c * a⁻¹ ∈ C :=
    (inferInstance : C.Normal).conj_mem c hcC a
  have h_conj_mem_z : a * c * a⁻¹ ∈ Subgroup.zpowers c := by
    simpa [hC_eq] using h_conj_mem_C
  obtain ⟨i, h_conj_symm⟩ := Subgroup.mem_zpowers_iff.mp h_conj_mem_z
  have h_conj : a * c * a⁻¹ = c ^ i := h_conj_symm.symm
  have ha_pow_z : a ^ p ∈ Subgroup.zpowers c := by
    simpa [hC_eq] using ha_pow
  exact conj_square_eq_inv_of_pow_mem_zpowers_of_pow_conj_ne
    hp he h_order h_conj ha_pow_z hpow_ne

/-- **Isaacs Thm 6.12 setup**: the pullback of a quotient involution does not have
order `8` once the `|C| = 4` case has been excluded. -/
theorem quotient_involution_comap_card_ne_eight_of_card_ne_four
    {P : Type*} [Group P] {C : Subgroup P} [C.Normal]
    (hC_card_ne : Nat.card C ≠ 4) :
    ∀ q : P ⧸ C, q ≠ 1 → q ^ 2 = 1 →
      Nat.card ((Subgroup.zpowers q).comap (QuotientGroup.mk' C)) ≠ 8 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro q hq_ne hq_sq
  let Q : Subgroup (P ⧸ C) := Subgroup.zpowers q
  let T : Subgroup P := Q.comap (QuotientGroup.mk' C)
  have hC_le_T : C ≤ T := QuotientGroup.le_comap_mk' C Q
  have hT_map : T.map (QuotientGroup.mk' C) = Q :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective C) Q
  have hq_order : orderOf q = 2 := orderOf_eq_prime (p := 2) hq_sq hq_ne
  have hC_rel : C.relIndex T = 2 := by
    have hrel : C.relIndex T = Nat.card Q := by
      have hrel_ker :
          (QuotientGroup.mk' C).ker.relIndex T = Nat.card Q := by
        rw [Subgroup.relIndex_ker, hT_map]
      simpa [QuotientGroup.ker_mk'] using hrel_ker
    rw [hrel]
    change Nat.card (Subgroup.zpowers q) = 2
    rw [Nat.card_zpowers, hq_order]
  exact card_ne_eight_of_relIndex_prime_of_card_ne_four hC_le_T hC_rel hC_card_ne

/-- **Isaacs Thm 6.12 setup**: a quotient involution inverts `c²`.

For a nontrivial involution `q ∈ P/C`, pull back `⟨q⟩` to a subgroup `T`. Then
`|T : C| = 2`.  Lemma 6.15 gives `c² ∉ Z(T)`, and since `T = C ⊔ ⟨a⟩` for any
representative `a` of `q`, the representative cannot centralize `c²`.  The preceding
exponent-free bridge then gives `(c²)^a = (c²)⁻¹`. -/
theorem quotient_involution_conj_square_eq_inv_of_zpowers
    {P : Type*} [Group P] [Finite P]
    {C : Subgroup P} [C.Normal] {c : P} {e : ℕ}
    (hP : IsPGroup 2 P)
    (hC_eq : C = Subgroup.zpowers c)
    (hCent : Subgroup.centralizer (C : Set P) = C)
    (hC_max : ∀ B : Subgroup P, B.Normal → IsMulCommutative B → C < B → False)
    (hcyc : ∀ B : Subgroup P, B.Normal → IsMulCommutative B → IsCyclic B)
    (h_order : orderOf c = 2 ^ e) (he : 0 < e)
    (hT_card_ne :
      ∀ q : P ⧸ C, q ≠ 1 → q ^ 2 = 1 →
        Nat.card ((Subgroup.zpowers q).comap (QuotientGroup.mk' C)) ≠ 8)
    {q : P ⧸ C} (hq_ne : q ≠ 1) (hq_sq : q ^ 2 = 1)
    {a : P} (haq : QuotientGroup.mk' C a = q) :
    a * c ^ 2 * a⁻¹ = (c ^ 2)⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Subgroup (P ⧸ C) := Subgroup.zpowers q
  let T : Subgroup P := Q.comap (QuotientGroup.mk' C)
  have hC_le_T : C ≤ T := QuotientGroup.le_comap_mk' C Q
  have hT_map : T.map (QuotientGroup.mk' C) = Q :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective C) Q
  have hq_order : orderOf q = 2 := orderOf_eq_prime (p := 2) hq_sq hq_ne
  have hC_rel : C.relIndex T = 2 := by
    have hrel : C.relIndex T = Nat.card Q := by
      have hrel_ker :
          (QuotientGroup.mk' C).ker.relIndex T = Nat.card Q := by
        rw [Subgroup.relIndex_ker, hT_map]
      simpa [QuotientGroup.ker_mk'] using hrel_ker
    rw [hrel]
    change Nat.card (Subgroup.zpowers q) = 2
    rw [Nat.card_zpowers, hq_order]
  have haT : a ∈ T := by
    change QuotientGroup.mk' C a ∈ Q
    rw [haq]
    exact Subgroup.mem_zpowers q
  have ha_notmem_C : a ∉ C := by
    intro haC
    apply hq_ne
    rw [← haq]
    exact (QuotientGroup.eq_one_iff a).mpr haC
  have hC_lt_T : C < T := by
    refine lt_of_le_of_ne hC_le_T ?_
    intro h_eq
    exact ha_notmem_C (by simpa [h_eq] using haT)
  have hC_cyclic : IsCyclic C := by
    rw [hC_eq]
    exact Subgroup.isCyclic_zpowers c
  have hquot_comm : ∀ x y : P ⧸ C, x * y = y * x :=
    quotient_commutative_of_isCyclic_of_self_centralizing hC_cyclic hCent
  have hT_normal : T.Normal :=
    normal_of_le_of_quotient_commutative hC_le_T hquot_comm
  have hT_not_comm : ¬ IsMulCommutative T := by
    intro hT_comm
    exact hC_max T hT_normal hT_comm hC_lt_T
  have hcC : c ∈ C := by
    rw [hC_eq]
    exact Subgroup.mem_zpowers c
  have hcT : c ∈ T := hC_le_T hcC
  have hQ_eq : Q = (Subgroup.zpowers a).map (QuotientGroup.mk' C) := by
    rw [MonoidHom.map_zpowers, haq]
  have hT_eq : T = C ⊔ Subgroup.zpowers a := by
    dsimp [T]
    rw [hQ_eq, QuotientGroup.comap_map_mk']
  have hc_pow_not_center : (⟨c, hcT⟩ : T) ^ 2 ∉ Subgroup.center T :=
    pow_not_mem_center_of_zpowers_relIndex_of_normal_abelian_cyclic
      (hP.to_subgroup T) (hT_card_ne q hq_ne hq_sq) hT_normal hcyc hC_eq hcT
      hC_le_T hCent hC_rel hT_not_comm
  have hpow_ne : a * c ^ 2 * a⁻¹ ≠ c ^ 2 := by
    intro hfix
    apply hc_pow_not_center
    rw [Subgroup.mem_center_iff]
    intro t
    apply Subtype.ext
    have ht_sup : (t : P) ∈ C ⊔ Subgroup.zpowers a := by
      rw [← hT_eq]
      exact t.2
    obtain ⟨y, hyC, z, hzA, hyz⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := C) (t := Subgroup.zpowers a)).mp ht_sup
    have hy_zpowers : y ∈ Subgroup.zpowers c := by
      simpa [hC_eq] using hyC
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hy_zpowers
    have hcomm_y : Commute y (c ^ 2) := by
      rw [← hm]
      exact (Commute.zpow_self c m).pow_right 2
    have hcomm_a : Commute a (c ^ 2) := by
      calc
        a * c ^ 2 = (a * c ^ 2 * a⁻¹) * a := by group
        _ = c ^ 2 * a := by rw [hfix]
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hzA
    have hcomm_z : Commute z (c ^ 2) := by
      rw [← hn]
      exact hcomm_a.zpow_left n
    have ht_comm : (t : P) * c ^ 2 = c ^ 2 * (t : P) := by
      calc
        (t : P) * c ^ 2 = (y * z) * c ^ 2 := by rw [hyz]
        _ = y * (z * c ^ 2) := by group
        _ = y * (c ^ 2 * z) := by rw [hcomm_z.eq]
        _ = (y * c ^ 2) * z := by group
        _ = (c ^ 2 * y) * z := by rw [hcomm_y.eq]
        _ = c ^ 2 * (y * z) := by group
        _ = c ^ 2 * (t : P) := by rw [hyz]
    simpa using ht_comm
  have ha_pow : a ^ 2 ∈ C := by
    have h := C.pow_relIndex_mem (K := T) haT
    simpa [hC_rel] using h
  exact (conj_square_eq_inv_of_normal_zpowers_of_pow_mem_of_pow_conj_ne
    (p := 2) (e := e) Nat.prime_two hC_eq h_order he ha_pow hpow_ne).2

/-- **Isaacs Thm 6.12 setup**: the quotient `P/C` is cyclic once all quotient
involutions are handled.

The action is the conjugation action of `P/C` on `C`.  The preceding theorem proves every
nontrivial involution in `P/C` inverts `c²`; since `e ≥ 3`, the element `c² ∈ C` has square
not equal to `1`.  Thus `P/C` has a unique involution, and the commutative finite `2`-group
cyclicity criterion applies. -/
theorem quotient_isCyclic_of_involutions_invert_zpowers_square
    {P : Type*} [Group P] [Finite P]
    {C : Subgroup P} [C.Normal] {c : P} {e : ℕ}
    (hP : IsPGroup 2 P)
    (hC_eq : C = Subgroup.zpowers c)
    (hCent : Subgroup.centralizer (C : Set P) = C)
    (hC_max : ∀ B : Subgroup P, B.Normal → IsMulCommutative B → C < B → False)
    (hcyc : ∀ B : Subgroup P, B.Normal → IsMulCommutative B → IsCyclic B)
    (h_order : orderOf c = 2 ^ e) (he : 3 ≤ e)
    (hT_card_ne :
      ∀ q : P ⧸ C, q ≠ 1 → q ^ 2 = 1 →
        Nat.card ((Subgroup.zpowers q).comap (QuotientGroup.mk' C)) ≠ 8) :
    IsCyclic (P ⧸ C) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC_cyclic : IsCyclic C := by
    rw [hC_eq]
    exact Subgroup.isCyclic_zpowers c
  have hquot_comm : ∀ x y : P ⧸ C, x * y = y * x :=
    quotient_commutative_of_isCyclic_of_self_centralizing hC_cyclic hCent
  have hcC : c ∈ C := by
    rw [hC_eq]
    exact Subgroup.mem_zpowers c
  have hc2C : c ^ 2 ∈ C := C.pow_mem hcC 2
  let n : C := ⟨c ^ 2, hc2C⟩
  have hn_sq_ne : n ^ 2 ≠ 1 := by
    intro hn
    have hc4 : c ^ 4 = 1 := by
      have hval := congrArg Subtype.val hn
      calc
        c ^ 4 = (c ^ 2) ^ 2 := by group
        _ = 1 := by simpa [n] using hval
    have hdvd : orderOf c ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr hc4
    rw [h_order] at hdvd
    have hlt : 4 < 2 ^ e := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ < 2 ^ e := Nat.pow_lt_pow_right (by norm_num) (by omega)
    exact (not_le_of_gt hlt) (Nat.le_of_dvd (by norm_num) hdvd)
  let φ : P →* MulAut C := MulAut.conjNormal (H := C)
  have hC_le_ker : C ≤ φ.ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    ext x
    have hcomm : g * (x : P) = (x : P) * g := by
      have : IsCyclic C := hC_cyclic
      have hmul : (⟨g, hg⟩ : C) * x = x * ⟨g, hg⟩ :=
        (inferInstance : IsMulCommutative C).is_comm.comm _ _
      exact congrArg Subtype.val hmul
    calc
      ((φ g x : C) : P) = g * (x : P) * g⁻¹ := by rfl
      _ = ((x : P) * g) * g⁻¹ := by rw [hcomm]
      _ = (x : P) := by simp [mul_assoc]
      _ = (((1 : MulAut C) x : C) : P) := by rfl
  let ψ : P ⧸ C →* MulAut C := QuotientGroup.lift C φ hC_le_ker
  let : MulDistribMulAction (P ⧸ C) C := MulDistribMulAction.compHom C ψ
  have hinv : ∀ q : P ⧸ C, q ≠ 1 → q ^ 2 = 1 → q • n = n⁻¹ := by
    intro q hq_ne hq_sq
    obtain ⟨a, haq⟩ := QuotientGroup.mk'_surjective C q
    have hconj :
        a * c ^ 2 * a⁻¹ = (c ^ 2)⁻¹ :=
      quotient_involution_conj_square_eq_inv_of_zpowers
        hP hC_eq hCent hC_max hcyc h_order (by omega) hT_card_ne hq_ne hq_sq haq
    apply Subtype.ext
    calc
      ((q • n : C) : P) = a * c ^ 2 * a⁻¹ := by
        rw [← haq]
        rfl
      _ = (c ^ 2)⁻¹ := hconj
      _ = ((n⁻¹ : C) : P) := by rfl
  exact isCyclic_of_comm_two_group_involutions_invert_element
    (hP.to_quotient C) hquot_comm hn_sq_ne hinv

/-- **Isaacs Thm 6.12 setup**: the two `2`-adic alternatives from Lemma 6.16 are
exactly the inversion and semidihedral-twist conjugation alternatives used by Lemma 6.13. -/
theorem conj_eq_inv_or_twist_of_two_adic_cases
    {G : Type*} [Group G] {c a : G} {e : ℕ} {i : ℤ}
    (h_order : orderOf c = 2 ^ e)
    (h_conj : a * c * a⁻¹ = c ^ i)
    (hcases :
      i ≡ -1 [ZMOD ((2 : ℤ) ^ e)] ∨
        i ≡ ((2 : ℤ) ^ (e - 1) - 1) [ZMOD ((2 : ℤ) ^ e)]) :
    a * c * a⁻¹ = c⁻¹ ∨
      a * c * a⁻¹ = c ^ (2 ^ (e - 1)) * c⁻¹ := by
  rcases hcases with hi | hi
  · left
    have hpow : c ^ i = c ^ (-1 : ℤ) := by
      rw [zpow_eq_zpow_iff_modEq]
      simpa [h_order] using hi
    calc
      a * c * a⁻¹ = c ^ i := h_conj
      _ = c ^ (-1 : ℤ) := hpow
      _ = c⁻¹ := by rw [zpow_neg_one]
  · right
    have hpow : c ^ i = c ^ ((2 : ℤ) ^ (e - 1) - 1) := by
      rw [zpow_eq_zpow_iff_modEq]
      simpa [h_order] using hi
    have hpow_cast : ((2 : ℤ) ^ (e - 1)) = ((2 ^ (e - 1) : ℕ) : ℤ) := by
      norm_num
    calc
      a * c * a⁻¹ = c ^ i := h_conj
      _ = c ^ ((2 : ℤ) ^ (e - 1) - 1) := hpow
      _ = c ^ ((2 : ℤ) ^ (e - 1)) * c⁻¹ := by
        rw [zpow_sub, zpow_one]
      _ = c ^ (2 ^ (e - 1)) * c⁻¹ := by
        rw [hpow_cast, zpow_natCast]

/-- The two 2-adic alternatives in Isaacs Lemma 6.16 cannot be a square modulo `2^e`
when `e ≥ 3`.

The proof reduces modulo `4`: both alternatives are `-1 mod 4`, but no square in
`ZMod 4` is `-1`. -/
private lemma square_root_two_adic_cases_false
    {e : ℕ} (he : 3 ≤ e) {i j : ℤ}
    (hij : i ≡ j ^ 2 [ZMOD ((2 : ℤ) ^ e)])
    (hcases :
      i ≡ -1 [ZMOD ((2 : ℤ) ^ e)] ∨
        i ≡ ((2 : ℤ) ^ (e - 1) - 1) [ZMOD ((2 : ℤ) ^ e)]) :
    False := by
  have h4_dvd : (4 : ℤ) ∣ (2 : ℤ) ^ e := by
    have hle : 2 ≤ e := le_trans (by norm_num) he
    simpa [show (4 : ℤ) = (2 : ℤ) ^ 2 by norm_num] using
      pow_dvd_pow (2 : ℤ) hle
  have hij4 : i ≡ j ^ 2 [ZMOD (4 : ℤ)] := hij.of_dvd h4_dvd
  have hi4 : i ≡ -1 [ZMOD (4 : ℤ)] := by
    rcases hcases with hi | hi
    · exact hi.of_dvd h4_dvd
    · have hsemi :
          ((2 : ℤ) ^ (e - 1) - 1) ≡ (-1 : ℤ) [ZMOD (4 : ℤ)] := by
        refine Int.modEq_iff_dvd.mpr ?_
        have hle : 2 ≤ e - 1 := Nat.le_sub_of_add_le he
        have h4 : (4 : ℤ) ∣ (2 : ℤ) ^ (e - 1) := by
          simpa [show (4 : ℤ) = (2 : ℤ) ^ 2 by norm_num] using
            pow_dvd_pow (2 : ℤ) hle
        have hrw : (-1 : ℤ) - ((2 : ℤ) ^ (e - 1) - 1) = -((2 : ℤ) ^ (e - 1)) := by
          ring
        rw [hrw]
        exact dvd_neg.mpr h4
      exact (hi.of_dvd h4_dvd).trans hsemi
  have hsq : (j ^ 2 : ℤ) ≡ (-1 : ℤ) [ZMOD (4 : ℤ)] :=
    hij4.symm.trans hi4
  have hZcast : ((j ^ 2 : ℤ) : ZMod 4) = (-1 : ZMod 4) :=
    (ZMod.intCast_eq_intCast_iff (j ^ 2) (-1) 4).mpr hsq
  have hZ : ((j : ZMod 4) ^ 2) = (-1 : ZMod 4) := by
    simpa using hZcast
  have hbad : ∀ x : ZMod 4, x ^ 2 ≠ (-1 : ZMod 4) := by
    decide
  exact hbad (j : ZMod 4) hZ

/-- **Isaacs Thm 6.12 setup**: in the cyclic quotient branch, the 2-adic conjugation
alternatives force `|P/C| = 2`.

If `P/C` had order larger than `2`, the nontrivial involution `aC` would be a square
`(bC)^2`. Conjugation by `b` on `C = ⟨c⟩` has some exponent `j`, so
`conj_exponent_modEq_sq_of_quotient_sq_eq` gives `i ≡ j² (mod |c|)`. Since the two
2-adic alternatives both reduce to `-1 mod 4`, this is impossible. -/
theorem index_eq_two_of_cyclic_quotient_of_two_adic_conj_cases
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    {C : Subgroup P} [C.Normal] {c a : P} {e : ℕ} {i : ℤ}
    (hC_eq : C = Subgroup.zpowers c)
    (hquot_cyclic : IsCyclic (P ⧸ C))
    (h_order : orderOf c = 2 ^ e) (he : 3 ≤ e)
    (ha_notmem : a ∉ C) (ha_sq_mem : a ^ 2 ∈ C)
    (h_conj : a * c * a⁻¹ = c ^ i)
    (hcases :
      i ≡ -1 [ZMOD ((2 : ℤ) ^ e)] ∨
        i ≡ ((2 : ℤ) ^ (e - 1) - 1) [ZMOD ((2 : ℤ) ^ e)]) :
    C.index = 2 := by
  classical
  rw [Subgroup.index_eq_card]
  by_contra hcard_ne_two
  let q : P ⧸ C := QuotientGroup.mk' C a
  have hq_ne : q ≠ 1 := by
    intro hq_one
    exact ha_notmem ((QuotientGroup.eq_one_iff a).mp hq_one)
  have hq_sq : q ^ 2 = 1 := by
    change ((a : P ⧸ C) ^ 2 = 1)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ha_sq_mem
  have hQ : IsPGroup 2 (P ⧸ C) := hP.to_quotient C
  have : IsCyclic (P ⧸ C) := hquot_cyclic
  obtain ⟨r, hr_sq⟩ :=
    exists_sq_eq_of_isCyclic_two_group_involution_of_card_ne_two
      (Q := P ⧸ C) hQ hq_ne hq_sq hcard_ne_two
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective C r
  have hquot : QuotientGroup.mk' C a = (QuotientGroup.mk' C b) ^ 2 := by
    rw [hb]
    exact hr_sq.symm
  have hcC : c ∈ C := by
    rw [hC_eq]
    exact Subgroup.mem_zpowers c
  have hb_conj_mem_C : b * c * b⁻¹ ∈ C := by
    exact (inferInstance : C.Normal).conj_mem c hcC b
  have hb_conj_mem_z : b * c * b⁻¹ ∈ Subgroup.zpowers c := by
    simpa [hC_eq] using hb_conj_mem_C
  obtain ⟨j, h_conj_b_symm⟩ := Subgroup.mem_zpowers_iff.mp hb_conj_mem_z
  have h_conj_b : b * c * b⁻¹ = c ^ j := h_conj_b_symm.symm
  have hij_order : i ≡ j ^ 2 [ZMOD orderOf c] :=
    conj_exponent_modEq_sq_of_quotient_sq_eq hC_eq hquot h_conj h_conj_b
  have hij : i ≡ j ^ 2 [ZMOD ((2 : ℤ) ^ e)] := by
    simpa [h_order] using hij_order
  exact square_root_two_adic_cases_false he hij hcases

/-- **Isaacs Thm 6.12 setup**: the cyclic-quotient 2-adic branch feeds into the
Lemma 6.13 recognizers.

The previous theorem gives `C.index = 2`; the two 2-adic alternatives then become either
inversion, handled by `dihedralOrQuaternion_of_invertingConjugation`, or the semidihedral
twist, handled by `semiDihedral_of_twistConjugation` using the unique involution
`c^(2^(e-1))` in `⟨c⟩`. -/
theorem dihedralOrQuaternionOrSemiDihedral_of_cyclic_quotient_two_adic_conj_cases
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (h_nonab : ∃ x y : P, x * y ≠ y * x)
    {C : Subgroup P} [C.Normal] {c a : P} {e : ℕ} {i : ℤ}
    (hC_eq : C = Subgroup.zpowers c)
    (hquot_cyclic : IsCyclic (P ⧸ C))
    (h_order : orderOf c = 2 ^ e) (he : 3 ≤ e)
    (ha_notmem : a ∉ C) (ha_sq_mem : a ^ 2 ∈ C)
    (h_conj : a * c * a⁻¹ = c ^ i)
    (hcases :
      i ≡ -1 [ZMOD ((2 : ℤ) ^ e)] ∨
        i ≡ ((2 : ℤ) ^ (e - 1) - 1) [ZMOD ((2 : ℤ) ^ e)]) :
    Nonempty (P ≃* DihedralGroup (orderOf c)) ∨
      Nonempty (P ≃* QuaternionGroup (orderOf c / 2)) ∨
        ∃ k : ℕ, 2 ^ k = orderOf c ∧ Nonempty (P ≃* SemiDihedralGroup k) := by
  classical
  have h_idx_C : C.index = 2 :=
    index_eq_two_of_cyclic_quotient_of_two_adic_conj_cases hP hC_eq hquot_cyclic
      h_order he ha_notmem ha_sq_mem h_conj hcases
  have h_idx : (Subgroup.zpowers c).index = 2 := by
    simpa [hC_eq] using h_idx_C
  have h_a_notmem_z : a ∉ Subgroup.zpowers c := by
    intro ha
    exact ha_notmem (by simpa [hC_eq] using ha)
  rcases conj_eq_inv_or_twist_of_two_adic_cases h_order h_conj hcases with h_inv | h_twist
  · rcases dihedralOrQuaternion_of_invertingConjugation hP c a h_idx h_a_notmem_z h_inv
      with hD | hQ
    · exact Or.inl hD
    · exact Or.inr (Or.inl hQ)
  · right
    right
    let z : P := c ^ (2 ^ (e - 1))
    have h_z_mem : z ∈ Subgroup.zpowers c := by
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _
    have h_z_sq : z ^ 2 = 1 := by
      dsimp [z]
      rw [← pow_mul]
      have hmul : 2 ^ (e - 1) * 2 = 2 ^ e := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hmul, ← h_order, pow_orderOf_eq_one]
    have h_z_ne : z ≠ 1 := by
      dsimp [z]
      intro hz_one
      have hdvd : orderOf c ∣ 2 ^ (e - 1) :=
        orderOf_dvd_iff_pow_eq_one.mpr hz_one
      rw [h_order] at hdvd
      have hlt : 2 ^ (e - 1) < 2 ^ e :=
        Nat.pow_lt_pow_right (by norm_num) (by omega)
      have hpos : 0 < 2 ^ (e - 1) := Nat.two_pow_pos _
      exact (not_le_of_gt hlt) (Nat.le_of_dvd hpos hdvd)
    have h_z_unique :
        ∀ y ∈ Subgroup.zpowers c, y ^ 2 = 1 → y ≠ 1 → y = z := by
      intro y hy_mem hy_sq hy_ne
      dsimp [z]
      exact zpowers_involution_eq_pow_pred_of_order_two_pow c y (by omega)
        h_order hy_mem hy_sq hy_ne
    exact semiDihedral_of_twistConjugation hP h_nonab c a z h_idx h_a_notmem_z
      h_z_mem h_z_sq h_z_ne h_z_unique (by simpa [z] using h_twist)

/-- **Isaacs Thm 6.12 setup**: the quotient-involution computation supplies the
cyclic-quotient input for the Lemma 6.13 classification branch.

This is the assembly point after proving that every nontrivial involution in `P/C` inverts
`c²`: it removes the theorem-stage assumption `P/C` cyclic from
`dihedralOrQuaternionOrSemiDihedral_of_zpowers_relIndex_cyclic_quotient`. -/
theorem dihedralOrQuaternionOrSemiDihedral_of_zpowers_relIndex_of_quotient_involutions
    {P : Type*} [Group P] [Finite P] {p e : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p P) (h_nonab : ∃ x y : P, x * y ≠ y * x)
    {C T : Subgroup P} [C.Normal] {c : P}
    (hT_card_ne : Nat.card T ≠ 8) (hT_normal : T.Normal)
    (hcyc : ∀ B : Subgroup P, B.Normal → IsMulCommutative B → IsCyclic B)
    (hC_eq : C = Subgroup.zpowers c) (hcT : c ∈ T)
    (hC_le_T : C ≤ T) (hCent : Subgroup.centralizer (C : Set P) = C)
    (hC_max : ∀ B : Subgroup P, B.Normal → IsMulCommutative B → C < B → False)
    (hC_rel : C.relIndex T = p) (hT_not_comm : ¬ IsMulCommutative T)
    (hT_card_ne_quot :
      ∀ q : P ⧸ C, q ≠ 1 → q ^ 2 = 1 →
        Nat.card ((Subgroup.zpowers q).comap (QuotientGroup.mk' C)) ≠ 8)
    (h_order : orderOf c = p ^ e) (he : 3 ≤ e) :
    p = 2 ∧
      (Nonempty (P ≃* DihedralGroup (orderOf c)) ∨
        Nonempty (P ≃* QuaternionGroup (orderOf c / 2)) ∨
          ∃ k : ℕ, 2 ^ k = orderOf c ∧ Nonempty (P ≃* SemiDihedralGroup k)) := by
  classical
  obtain ⟨a, i, _haT, ha_notmem, ha_pow_C, h_conj, hp_eq_two, hcases⟩ :=
    exists_conj_exponent_two_adic_cases_of_zpowers_relIndex_of_normal_abelian_cyclic
      (hP.to_subgroup T) hT_card_ne hT_normal hcyc hC_eq hcT hC_le_T hCent
      hC_rel hT_not_comm h_order (by omega)
  cases hp_eq_two
  have hquot_cyclic : IsCyclic (P ⧸ C) :=
    quotient_isCyclic_of_involutions_invert_zpowers_square
      hP hC_eq hCent hC_max hcyc h_order he hT_card_ne_quot
  refine ⟨rfl, ?_⟩
  have ha_sq_mem : a ^ 2 ∈ C := by
    simpa using ha_pow_C
  exact dihedralOrQuaternionOrSemiDihedral_of_cyclic_quotient_two_adic_conj_cases
    hP h_nonab hC_eq hquot_cyclic h_order he ha_notmem ha_sq_mem h_conj hcases

/-- **Isaacs Thm 6.12 setup**: the maximal normal cyclic branch reaches the
dihedral/quaternion/semidihedral classification surface after excluding `|C| = 4`.

This is the same branch as
`dihedralOrQuaternionOrSemiDihedral_of_maximal_normal_zpowers_lt_top`, but it derives the
needed exponent bound `3 ≤ e` from the normal-abelian-cyclic hypothesis instead of taking it
as an external assumption. -/
theorem dihedralOrQuaternionOrSemiDihedral_of_maximal_normal_zpowers_lt_top_card_ne_four
    {P : Type*} [Group P] [Finite P] {p e : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p P) (h_nonab : ∃ x y : P, x * y ≠ y * x)
    {C : Subgroup P} [C.Normal] {c : P}
    (hcyc : ∀ B : Subgroup P, B.Normal → IsMulCommutative B → IsCyclic B)
    (hC_eq : C = Subgroup.zpowers c)
    (hC_max : ∀ B : Subgroup P, B.Normal → IsMulCommutative B → C < B → False)
    (hC_lt_top : C < ⊤) (hC_card_ne : Nat.card C ≠ 4)
    (h_order : orderOf c = p ^ e) :
    p = 2 ∧
      (Nonempty (P ≃* DihedralGroup (orderOf c)) ∨
        Nonempty (P ≃* QuaternionGroup (orderOf c / 2)) ∨
          ∃ k : ℕ, 2 ^ k = orderOf c ∧ Nonempty (P ≃* SemiDihedralGroup k)) := by
  classical
  have hC_cyclic : IsCyclic C := by
    rw [hC_eq]
    exact Subgroup.isCyclic_zpowers c
  have hC_comm : IsMulCommutative C := by
    have : IsCyclic C := hC_cyclic
    infer_instance
  have hCent : Subgroup.centralizer (C : Set P) = C :=
    centralizer_eq_of_maximal_normal_isMulCommutative hP hC_comm hC_max
  obtain ⟨T, hT_normal, hcT, hC_le_T, hC_rel, hT_not_comm⟩ :=
    exists_normal_noncomm_relIndex_prime_of_maximal_normal_zpowers_lt_top
      hP hC_eq hC_max hC_lt_top
  have hT_card_ne : Nat.card T ≠ 8 :=
    card_ne_eight_of_relIndex_prime_of_card_ne_four hC_le_T hC_rel hC_card_ne
  have hT_card_ne_quot :
      ∀ q : P ⧸ C, q ≠ 1 → q ^ 2 = 1 →
        Nat.card ((Subgroup.zpowers q).comap (QuotientGroup.mk' C)) ≠ 8 :=
    quotient_involution_comap_card_ne_eight_of_card_ne_four hC_card_ne
  have he : 3 ≤ e :=
    three_le_exponent_of_zpowers_relIndex_of_normal_abelian_cyclic
      (hP.to_subgroup T) hT_card_ne hT_normal hcyc hC_eq hcT hC_le_T hCent
      hC_rel hT_not_comm hC_card_ne h_order
  exact dihedralOrQuaternionOrSemiDihedral_of_zpowers_relIndex_of_quotient_involutions
    hP h_nonab hT_card_ne hT_normal hcyc hC_eq hcT hC_le_T hCent hC_max
    hC_rel hT_not_comm hT_card_ne_quot h_order he

/-- **Isaacs Thm 6.12**: if every normal abelian subgroup of a finite `p`-group is cyclic,
then the group is cyclic, or `p = 2` and the group is dihedral, generalized quaternion, or
semidihedral.

This theorem assembles the already-formalized proof branches: choose a maximal normal abelian
subgroup `C`; if `C = P`, the group is cyclic; if `|C| = 4`, Corollary 6.14 applies; otherwise
the maximal-normal-cyclic branch reaches the dihedral/quaternion/semidihedral classification. -/
theorem isCyclic_or_two_dihedralOrQuaternionOrSemiDihedral_of_normal_abelian_cyclic
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p P)
    (hcyc : ∀ B : Subgroup P, B.Normal → IsMulCommutative B → IsCyclic B) :
    IsCyclic P ∨
      p = 2 ∧
        ((∃ n : ℕ, Nonempty (P ≃* DihedralGroup n)) ∨
          (∃ n : ℕ, Nonempty (P ≃* QuaternionGroup n)) ∨
            ∃ k : ℕ, Nonempty (P ≃* SemiDihedralGroup k)) := by
  classical
  by_cases hP_cyclic : IsCyclic P
  · exact Or.inl hP_cyclic
  right
  have hP_not_comm : ¬ IsMulCommutative P := by
    intro hP_comm
    apply hP_cyclic
    have htop_cyclic : IsCyclic (⊤ : Subgroup P) := by
      apply hcyc
      · infer_instance
      · -- rc2: no auto `IsMulCommutative P → IsMulCommutative ↥⊤`; build it directly.
        exact ⟨⟨fun a b => Subtype.ext (hP_comm.is_comm.comm a b)⟩⟩
    rw [← Subgroup.topEquiv.isCyclic]
    exact htop_cyclic
  have h_nonab : ∃ x y : P, x * y ≠ y * x := by
    by_contra hnone
    exact hP_not_comm ⟨⟨fun x y => by
      by_contra hxy
      exact hnone ⟨x, y, hxy⟩⟩⟩
  obtain ⟨C, hC_normal, hC_comm, hC_max⟩ :=
    exists_maximal_normal_isMulCommutative (P := P)
  have hC_normal_inst : C.Normal := hC_normal
  have hC_cyclic : IsCyclic C := hcyc C hC_normal hC_comm
  have hC_ne_top : C ≠ ⊤ := by
    intro hC_top
    apply hP_cyclic
    rw [← Subgroup.topEquiv.isCyclic]
    rwa [← hC_top]
  have hC_lt_top : C < ⊤ := lt_top_iff_ne_top.mpr hC_ne_top
  have hCent : Subgroup.centralizer (C : Set P) = C :=
    centralizer_eq_of_maximal_normal_isMulCommutative hP hC_comm hC_max
  by_cases hC_card : Nat.card C = 4
  · have hp_eq_two : p = 2 := by
      have hC_pgroup : IsPGroup p C := hP.to_subgroup C
      have hp_dvd : p ∣ Nat.card C := by
        rcases hC_pgroup.card_eq_or_dvd with hC_card_one | hdiv
        · rw [hC_card] at hC_card_one
          omega
        · exact hdiv
      exact Nat.prime_eq_prime_of_dvd_pow (m := 2) (p := p) (q := 2)
        (Fact.out : p.Prime) Nat.prime_two (by simpa [hC_card] using hp_dvd)
    obtain hD | hQ :=
      dihedralOrQuaternion_of_self_centralizing_cyclic_card_four
        hC_cyclic hCent hC_card h_nonab
    · exact ⟨hp_eq_two, Or.inl ⟨4, hD⟩⟩
    · exact ⟨hp_eq_two, Or.inr (Or.inl ⟨2, hQ⟩)⟩
  · obtain ⟨c, hC_eq⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top C).mp hC_cyclic
    obtain ⟨e, h_order⟩ := (IsPGroup.iff_orderOf.mp hP) c
    obtain ⟨hp_eq_two, hclass⟩ :=
      dihedralOrQuaternionOrSemiDihedral_of_maximal_normal_zpowers_lt_top_card_ne_four
        hP h_nonab hcyc hC_eq.symm hC_max hC_lt_top hC_card h_order
    refine ⟨hp_eq_two, ?_⟩
    rcases hclass with hD | hQ | hSD
    · exact Or.inl ⟨orderOf c, hD⟩
    · exact Or.inr (Or.inl ⟨orderOf c / 2, hQ⟩)
    · obtain ⟨k, _hk_order, hSD⟩ := hSD
      exact Or.inr (Or.inr ⟨k, hSD⟩)

/-- **Isaacs Thm 6.11, odd-prime corollary**: if `p ≠ 2`, a finite `p`-group with
at most one subgroup of order `p` is cyclic.

The order-`p` subgroup uniqueness hypothesis makes every abelian subgroup cyclic, so
Theorem 6.12 applies.  Its noncyclic alternatives force `p = 2`, which is excluded here. -/
theorem isCyclic_of_subgroups_card_prime_unique_of_prime_ne_two
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p P) (hp_ne_two : p ≠ 2)
    (hUnique : ∀ K L : Subgroup P, Nat.card K = p → Nat.card L = p → K = L) :
    IsCyclic P := by
  have hcyc : ∀ B : Subgroup P, B.Normal → IsMulCommutative B → IsCyclic B := by
    intro B _hB_normal hB_comm
    have : IsMulCommutative B := hB_comm
    exact hP.isCyclic_subgroup_of_subgroups_card_prime_unique hUnique B
  rcases isCyclic_or_two_dihedralOrQuaternionOrSemiDihedral_of_normal_abelian_cyclic
      hP hcyc with hP_cyclic | htwo
  · exact hP_cyclic
  · exact False.elim (hp_ne_two htwo.1)

/-- **Isaacs Thm 6.11, odd-prime corollary** in the form used by odd-order applications. -/
theorem isCyclic_of_subgroups_card_prime_unique_of_odd
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p P) (hp_odd : Odd p)
    (hUnique : ∀ K L : Subgroup P, Nat.card K = p → Nat.card L = p → K = L) :
    IsCyclic P :=
  isCyclic_of_subgroups_card_prime_unique_of_prime_ne_two hP
    (fun hp_eq_two => by
      rw [hp_eq_two] at hp_odd
      rcases hp_odd with ⟨k, hk⟩
      omega) hUnique

end OddOrder.Isaacs.Ch06


