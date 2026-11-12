-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04_SmallRankBasic
-- name    : OddOrder_BG_Ch1_Preliminary_S04_SmallRankBasic
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:47:04.033854+00:00
-- url     : https://prove2.me/theorems/e140c5d3-ee03-47a7-a6f2-5cd950392462
-- title:
--   BG §4: small-rank $p$-groups, basic lemmas
-- statement:
--   Part of Bender–Glauberman §4 on $p$-groups of small rank, containing the basic lemmas.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 14 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S04_SmallRankBasic.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S04_SmallRankBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S01_Solvable
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04_CommutatorCollection
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S02_Representations
import Definitions.Def_OddOrder_GroupTheory_CriticalSubgroup
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Definitions.Def_OddOrder_GroupTheory_FrattiniPGroup
import Definitions.Def_OddOrder_GroupTheory_IsExtraspecial
import Definitions.Def_OddOrder_GroupTheory_IsMetacyclic
import Definitions.Def_OddOrder_GroupTheory_PRank
import Definitions.Def_OddOrder_GroupTheory_SCN
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_Main
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

namespace OddOrder.BG.Ch1.S04

open OddOrder.BG.Ch1.S02

section ElementaryAbelianExistence

open OddOrder.GroupTheory

variable {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]

/-- A noncyclic finite `p`-group (`p` odd) has two distinct subgroups of order `p`.

This is the contrapositive of Isaacs Thm 6.11
(`OddOrder.Isaacs.Ch06.isCyclic_of_subgroups_card_prime_unique_of_odd`): a finite
odd `p`-group with a *unique* subgroup of order `p` is cyclic. -/
theorem exists_distinct_subgroups_card_prime_of_not_isCyclic (hR : IsPGroup p R)
    (hp_odd : Odd p) (hnc : ¬ IsCyclic R) :
    ∃ K L : Subgroup R, Nat.card K = p ∧ Nat.card L = p ∧ K ≠ L := by
  -- If no two order-`p` subgroups were distinct, `R` would be cyclic (Thm 6.11).
  have huniq : (∀ K L : Subgroup R, Nat.card K = p → Nat.card L = p → K = L) →
      IsCyclic R :=
    fun h => OddOrder.Isaacs.Ch06.isCyclic_of_subgroups_card_prime_unique_of_odd hR hp_odd h
  by_contra h
  -- `push Not` is deprecated in this toolchain; unfold the negated existential by hand.
  simp only [not_exists, not_and, ne_eq, not_not] at h
  exact hnc (huniq fun K L hK hL => h K L hK hL)

/-- **BG Lemma 4.5(a)**, existence half only (no normality). An odd noncyclic
`p`-group `R` contains an elementary abelian subgroup of order `p²`.

Proof: by `exists_distinct_subgroups_card_prime_of_not_isCyclic` there are two
distinct order-`p` subgroups; `ElementaryAbelian.lean`'s
`exists_isElementaryAbelian_card_prime_sq_of_subgroups_card_prime_ne` builds an
`E_{p²}` from them.

⚠ This is *not* the frontier: the **full** Lemma 4.5(a) — with the book's `normal`
conclusion and no side hypothesis — is
`exists_normal_isElementaryAbelian_card_prime_sq_of_not_isCyclic` **later in this file**.
This weaker form is kept because several callers only need a (non-normal) `E_{p²}`. -/
theorem exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic (hR : IsPGroup p R)
    (hp_odd : Odd p) (hnc : ¬ IsCyclic R) :
    ∃ E : Subgroup R, E.IsElementaryAbelian p ∧ Nat.card E = p ^ 2 := by
  obtain ⟨K, L, hK, hL, hKL⟩ :=
    exists_distinct_subgroups_card_prime_of_not_isCyclic hR hp_odd hnc
  obtain ⟨E, hE_elem, hE_card⟩ :=
    hR.exists_isElementaryAbelian_card_prime_sq_of_subgroups_card_prime_ne hK hL hKL
  exact ⟨E, hE_elem, hE_card⟩

end ElementaryAbelianExistence

section SCN3Empty

open OddOrder.GroupTheory

variable {R : Type*} [Group R] [Finite R] {p : ℕ}

/-- **BG Lemma 4.7**, the easy (`⇐`) direction — *"Obviously, `SCN₃(R)` is empty if
`r(R) ≤ 2`"* (mmd L1502).

If the `p`-rank of `R` is at most `2` then `R` has no `SCN₃` subgroup: any subgroup `A`
with `3 ≤ pRank A p` (in particular any `IsSCN₃ p A`) would violate monotonicity of the
`p`-rank, since `pRank A p ≤ pRank R p ≤ 2` for `A ≤ R` (`pRank_mono_of_le`).

This is the half of BG's iff that §5 / §7 (Thompson transitivity) / §10 use to *detect*
`SCN₃`. The hard converse `SCN₃(R) = ∅ ⇒ pRank R p ≤ 2` is **G** Theorem 5.4.15(i)
(Gorenstein), deferred (see the section docstring); note it needs neither the SCN nor the
self-centralizing structure of `A` — only `3 ≤ pRank A p` and `A ≤ R` — so we state the
hypothesis-minimal form. -/
theorem not_le_pRank_of_pRank_le_two (hr : pRank R p ≤ 2) (A : Subgroup R) :
    ¬ 3 ≤ pRank A p := by
  intro hA
  -- `3 ≤ pRank A p ≤ pRank R p ≤ 2`, contradiction.
  have : (3 : ℕ) ≤ 2 := hA.trans ((pRank_mono_of_le A).trans hr)
  omega

/-- **BG Lemma 4.7**, the easy (`⇐`) direction, SCN form: if `r(R) ≤ 2` (i.e.
`pRank R p ≤ 2`) then `SCN₃(R)` is empty, `∀ A, ¬ IsSCN₃ p A`.

Immediate from `not_le_pRank_of_pRank_le_two` applied to the rank component of `IsSCN₃`.
This is the v1 goal opening the §4 dependency of §5 / §7 (Thompson transitivity) / §10. -/
theorem scn3_empty_of_pRank_le_two (hr : pRank R p ≤ 2) (A : Subgroup R) :
    ¬ IsSCN₃ p A := fun h => not_le_pRank_of_pRank_le_two hr A h.le_pRank

/-- **`SCN₃(R) = ∅ ⇒ d_n(R) ≤ 2`** — the *translation* half of the hard direction of BG
Lemma 4.7 (= **G** Theorem 5.4.15(i)). In a finite `p`-group with no `SCN₃` subgroup, every
**normal abelian** subgroup has `p`-rank `≤ 2`.

Each abelian normal `B` lies in a maximal abelian normal `A`
(`exists_maximalAbelianNormal_ge`), which is `SCN` in a `p`-group
(`IsMaximalAbelianNormal.isSCN`); since `A` is `SCN` but not `SCN₃`, we get `pRank A p ≤ 2`,
and `pRank B p ≤ pRank A p` by monotonicity (`pRank_le_of_injective` on the inclusion
`B ↪ A`). This `d_n(R) ≤ 2` statement is the genuine hypothesis fed to `G` Theorem 4.15(i)
(`pRank ≤ 2` for the *whole* group); it is **not** itself a rank bound on `R` (it constrains
only normal abelian subgroups), so it does not pre-suppose the conclusion. -/
theorem normalAbelian_pRank_le_two_of_scn3_empty [Fact p.Prime] (hR : IsPGroup p R)
    (hSCN : ∀ A : Subgroup R, ¬ IsSCN₃ p A)
    {B : Subgroup R} (hBnorm : B.Normal) (hBcomm : IsMulCommutative B) :
    pRank B p ≤ 2 := by
  obtain ⟨A, hBA, hAmax⟩ := exists_maximalAbelianNormal_ge hBnorm hBcomm
  have hAscn : IsSCN A := hAmax.isSCN hR
  have hApr : pRank A p ≤ 2 := by
    by_contra h
    exact hSCN A ⟨hAscn, by omega⟩
  have hmono : pRank B p ≤ pRank A p :=
    pRank_le_of_injective (Subgroup.inclusion_injective hBA)
  omega

end SCN3Empty

section CyclicIndexP

open OddOrder.GroupTheory

variable {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]

/-- ⚠ GENUINE SUB-LEMMA (the heart of 4.5(b)): for `p` odd and `H = ⟨x⟩ ⊴ R` cyclic of
index `p` in a `p`-group `R`, the `p`-th power `x^p` is central.

This is the Gorenstein 5.4.4 Frattini step, and where odd `p` is essential. For any
`a ∈ R`, conjugation acts on the normal cyclic `H = ⟨x⟩` as `a x a⁻¹ = x^i`; since
`a^p ∈ H` (as `|R:H| = p`), Isaacs Lemma 6.5-style bookkeeping gives `i^p ≡ 1 [ZMOD p^e]`
(`orderOf x = p^e`), and Isaacs Lemma 6.16 (`pow_prime_modEq_one_cases`) — whose `p = 2`
alternatives are excluded by `p` odd — forces `i ≡ 1 [ZMOD p^(e-1)]`, which is exactly
`a x^p a⁻¹ = x^p` (`conj_exponent_not_modEq_one_of_pow_conj_ne`, contrapositive). -/
theorem pow_mem_center_of_cyclic_index_prime
    (hR : IsPGroup p R) (hp_odd : Odd p) {x : R} (hHidx : (Subgroup.zpowers x).index = p) :
    x ^ p ∈ Subgroup.center R := by
  set H : Subgroup R := Subgroup.zpowers x with hH_def
  -- `H ⊴ R` (index `p` = `minFac` in a `p`-group).
  have hH_normal : H.Normal := by
    have hp_prime : p.Prime := Fact.out
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hR
    have hm_ne : m ≠ 0 := by
      rintro rfl
      have : Nat.card R = 1 := by simpa using hm
      have hdvd : p ∣ 1 := this ▸ hHidx ▸ H.index_dvd_card
      exact hp_prime.not_dvd_one hdvd
    have hmin : (Nat.card R).minFac = p := by rw [hm, hp_prime.pow_minFac hm_ne]
    exact Subgroup.normal_of_index_eq_minFac_card (by rw [hHidx, hmin])
  -- `orderOf x = p^e`.
  obtain ⟨e, he_order⟩ := (IsPGroup.iff_orderOf.mp hR) x
  rw [Subgroup.mem_center_iff]
  intro a
  -- It suffices to show `a * x^p * a⁻¹ = x^p` (i.e. `a` and `x^p` commute).
  suffices hfix : a * x ^ p * a⁻¹ = x ^ p by
    calc a * x ^ p = (a * x ^ p * a⁻¹) * a := by group
      _ = x ^ p * a := by rw [hfix]
  -- Degenerate case `e = 0` (`x = 1`): the goal is about `x^p = 1`, trivially fixed.
  rcases Nat.eq_zero_or_pos e with he0 | he_pos
  · have hx1 : x = 1 := orderOf_eq_one_iff.mp (by rw [he_order, he0, pow_zero])
    rw [hx1]; group
  -- Main case `e ≥ 1`. Conjugation by `a` sends `x` into `H = ⟨x⟩`: `a x a⁻¹ = x^i`.
  have hconj_mem : a * x * a⁻¹ ∈ Subgroup.zpowers x :=
    hH_normal.conj_mem x (Subgroup.mem_zpowers x) a
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hconj_mem
  have h_conj : a * x * a⁻¹ = x ^ i := hi.symm
  -- `a^p ∈ H = ⟨x⟩` (since `|R : H| = p`).
  have ha_pow_mem : a ^ p ∈ Subgroup.zpowers x := by
    have := H.pow_index_mem a
    rwa [hHidx] at this
  -- `i^p ≡ 1 [ZMOD p^e]`.
  have hpow_mod : i ^ p ≡ 1 [ZMOD ((p : ℤ) ^ e)] :=
    OddOrder.Isaacs.Ch06.conj_exponent_pow_modEq_one_of_pow_mem_zpowers
      he_order h_conj ha_pow_mem
  -- For `p` odd, Lemma 6.16 leaves only `i ≡ 1 [ZMOD p^(e-1)]`.
  have hp_ne_two : p ≠ 2 := by
    rintro rfl; exact (Nat.not_odd_iff_even.mpr (by norm_num)) hp_odd
  have hmod_one : i ≡ 1 [ZMOD ((p : ℤ) ^ (e - 1))] := by
    rcases OddOrder.Isaacs.Ch06.pow_prime_modEq_one_cases (Fact.out : p.Prime) he_pos hpow_mod
      with h | h2 | h2
    · exact h
    · exact absurd h2.1 hp_ne_two
    · exact absurd h2.1 hp_ne_two
  -- `i ≡ 1 [ZMOD p^(e-1)]` ⇒ `a x^p a⁻¹ = x^p` (contrapositive of the noncentrality lemma).
  by_contra hne
  exact OddOrder.Isaacs.Ch06.conj_exponent_not_modEq_one_of_pow_conj_ne
    he_pos he_order h_conj hne hmod_one

/-- ⚠ GENUINE SUB-LEMMA (the heart of 4.5(b)): for `p` odd and `R` a `p`-group with a
cyclic subgroup `H = ⟨x⟩` of index `p`, the nilpotence class is `≤ 2`,
`commutator R ≤ Z(R)`.

`H ⊴ R` and `x^p ∈ Z(R)` (`pow_mem_center_of_cyclic_index_prime`). Then `⟨x^p⟩ ⊴ R` is
central, and `R⧸⟨x^p⟩` has order `p²` (`= |R:H|·|H:⟨x^p⟩| = p·p`), hence is abelian, so
`commutator R ≤ ⟨x^p⟩ ≤ Z(R)`. The order computation uses `|H| = orderOf x = p^e`
(`e ≥ 1`) and `|⟨x^p⟩| = orderOf (x^p) = p^(e-1)`. -/
theorem commutator_le_center_of_cyclic_index_prime
    (hR : IsPGroup p R) (hp_odd : Odd p) {x : R} (hHidx : (Subgroup.zpowers x).index = p) :
    _root_.commutator R ≤ Subgroup.center R := by
  have hp_prime : p.Prime := Fact.out
  set H : Subgroup R := Subgroup.zpowers x with hH_def
  -- `x^p` is central.
  have hxp_center : x ^ p ∈ Subgroup.center R :=
    pow_mem_center_of_cyclic_index_prime hR hp_odd hHidx
  -- `N := ⟨x^p⟩` is central, hence normal.
  set N : Subgroup R := Subgroup.zpowers (x ^ p) with hN_def
  have hN_le_center : N ≤ Subgroup.center R := by
    rw [hN_def, Subgroup.zpowers_le]; exact hxp_center
  have hN_normal : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hgn : g * n = n * g := Subgroup.mem_center_iff.mp (hN_le_center hn) g
    simpa [mul_assoc, hgn] using hn
  -- `orderOf x = p^e`.
  obtain ⟨e, he_order⟩ := (IsPGroup.iff_orderOf.mp hR) x
  -- Degenerate case `e = 0` (`x = 1`): `H = ⊥`, `|R| = p`, so `R` is cyclic (hence
  -- commutative) and `commutator R = ⊥ ≤ Z(R)`.
  rcases Nat.eq_zero_or_pos e with he0 | he_pos
  · have hx1 : x = 1 := orderOf_eq_one_iff.mp (by rw [he_order, he0, pow_zero])
    have hHbot : H = ⊥ := by rw [hH_def, hx1, Subgroup.zpowers_one_eq_bot]
    have hcardR : Nat.card R = p := by
      have hidx : (⊥ : Subgroup R).index = Nat.card R := Subgroup.index_bot
      rw [← hHbot, hHidx] at hidx; exact hidx.symm
    have : IsCyclic R := isCyclic_of_prime_card hcardR
    exact (commutator_eq_bot R).le.trans bot_le
  -- Main case `e ≥ 1`. `|R| = p · orderOf x = p^(e+1)`.
  have hcardR : Nat.card R = p ^ (e + 1) := by
    have h1 : Nat.card H * H.index = Nat.card R := Subgroup.card_mul_index H
    have hcardH : Nat.card H = p ^ e := by rw [hH_def, Nat.card_zpowers, he_order]
    rw [hcardH, hHidx, ← pow_succ] at h1
    exact h1.symm
  -- `|N| = orderOf (x^p) = p^(e-1)`.
  have hcardN : Nat.card N = p ^ (e - 1) := by
    rw [hN_def, Nat.card_zpowers, orderOf_pow x, he_order]
    -- `gcd (p^e) p = p`, so `p^e / p = p^(e-1)`.
    have hgcd : Nat.gcd (p ^ e) p = p := by
      have hdvd : p ∣ p ^ e := dvd_pow_self p he_pos.ne'
      exact Nat.gcd_eq_right hdvd
    rw [hgcd]
    -- `p^e / p = p^e / p^1 = p^(e-1)`.
    have : p ^ e / p = p ^ e / p ^ 1 := by rw [pow_one]
    rw [this, Nat.pow_div he_pos hp_prime.pos]
  -- `R ⧸ N` has order `p²`, hence abelian.
  have hcard_quot : Nat.card (R ⧸ N) = p ^ 2 := by
    have hmul : Nat.card N * N.index = Nat.card R := Subgroup.card_mul_index N
    rw [hcardN, hcardR] at hmul
    have hNidx : N.index = p ^ 2 := by
      have he1 : (e - 1) + 2 = e + 1 := by omega
      have : p ^ (e - 1) * N.index = p ^ (e - 1) * p ^ 2 := by
        rw [hmul, ← pow_add, he1]
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp_prime.pos _) this
    rw [← Subgroup.index_eq_card]; exact hNidx
  have hquot_comm : ∀ a b : R ⧸ N, a * b = b * a :=
    isMulCommutative_iff.mp
      (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hcard_quot)
  -- `commutator R ≤ N ≤ Z(R)`.
  have hcomm_le_N : _root_.commutator R ≤ N :=
    hN_normal.quotient_commutative_iff_commutator_le.mp ⟨⟨hquot_comm⟩⟩
  exact hcomm_le_N.trans hN_le_center

/-- ⚠ GENUINE SUB-LEMMA (the rank bound of 4.5(b)): for `p` odd and `R` a `p`-group with a
cyclic subgroup `H = ⟨x⟩` of index `p`, `|Ω₁(R)| ≤ p²`.

Set `Ω := Ω₁(R)` and `K := Ω ⊓ H`. By `commutator_le_center_of_cyclic_index_prime`,
`cl(R) ≤ 2`, so every element of `Ω` has `p`-th power `1` (`Omega.pow_eq_one_of_class_le_two`).
Hence `K ≤ H` is a finite subgroup of the cyclic `H` with exponent dividing `p`, so
`|K| ∣ p`. The second isomorphism `Ω⧸K ↪ R⧸H` (order `p`) gives
`(Ω⊓H).relIndex Ω ∣ H.index = p`. Then
`|Ω| = |K| · (Ω⊓H).relIndex Ω ≤ p · p`. -/
theorem card_omega1_le_prime_sq_of_cyclic_index_prime
    (hR : IsPGroup p R) (hp_odd : Odd p) {x : R} (hHidx : (Subgroup.zpowers x).index = p) :
    Nat.card (Omega R p 1) ≤ p ^ 2 := by
  set H : Subgroup R := Subgroup.zpowers x with hH_def
  set Ω : Subgroup R := Omega R p 1 with hΩ_def
  have hp_prime : p.Prime := Fact.out
  -- `H ⊴ R`.
  have hH_normal : H.Normal := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hR
    have hm_ne : m ≠ 0 := by
      rintro rfl
      have : Nat.card R = 1 := by simpa using hm
      have hdvd : p ∣ 1 := this ▸ hHidx ▸ H.index_dvd_card
      exact hp_prime.not_dvd_one hdvd
    have hmin : (Nat.card R).minFac = p := by rw [hm, hp_prime.pow_minFac hm_ne]
    exact Subgroup.normal_of_index_eq_minFac_card (by rw [hHidx, hmin])
  -- `cl(R) ≤ 2`.
  have hcl : _root_.commutator R ≤ Subgroup.center R :=
    commutator_le_center_of_cyclic_index_prime hR hp_odd hHidx
  -- Every element of `Ω` has `p`-th power `1`.
  have hΩ_exp : ∀ g ∈ Ω, g ^ p = 1 := fun g hg =>
    Omega.pow_eq_one_of_class_le_two hp_odd hcl hg
  -- (1) `|K| ∣ p` where `K := Ω ⊓ H`.
  set K : Subgroup R := Ω ⊓ H with hK_def
  have hK_card_dvd : Nat.card K ∣ p := by
    -- `K` is a subgroup of cyclic `H`, hence cyclic; its exponent divides `p`.
    have hHcyc : IsCyclic H := by rw [hH_def]; exact Subgroup.isCyclic_zpowers x
    have hK_cyc : IsCyclic K := by
      -- `K.subgroupOf H` is a subgroup of the cyclic `H`, hence cyclic; transport to `K`.
      have hKH : K ≤ H := inf_le_right
      have : IsCyclic (K.subgroupOf H) := Subgroup.isCyclic _
      exact isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe hKH).surjective
    -- exponent of `K` divides `p`.
    have hexp_dvd : Monoid.exponent K ∣ p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro g
      apply Subtype.ext
      have hgΩ : (g : R) ∈ Ω := (inf_le_left : K ≤ Ω) g.2
      rw [SubmonoidClass.coe_pow]; simpa using hΩ_exp (g : R) hgΩ
    -- cyclic ⇒ `card = exponent`.
    have : Nat.card K = Monoid.exponent K := IsCyclic.exponent_eq_card.symm
    rw [this]; exact hexp_dvd
  have hK_le : Nat.card K ≤ p := Nat.le_of_dvd hp_prime.pos hK_card_dvd
  -- (2) `(Ω ⊓ H).relIndex Ω ∣ p`.
  have hrel_dvd : (Ω ⊓ H).relIndex Ω ∣ p := by
    have h1 : (Ω ⊓ H).relIndex Ω = H.relIndex Ω := by
      rw [inf_comm]; exact Subgroup.inf_relIndex_right H Ω
    rw [h1]
    have h2 : H.relIndex Ω ∣ H.index := Subgroup.relIndex_dvd_index_of_normal H Ω
    rw [hHidx] at h2; exact h2
  have hrel_le : (Ω ⊓ H).relIndex Ω ≤ p := Nat.le_of_dvd hp_prime.pos hrel_dvd
  -- `|Ω| = |K| · (Ω ⊓ H).relIndex Ω`.
  have hΩ_factor : Nat.card K * (Ω ⊓ H).relIndex Ω = Nat.card Ω := by
    have hbot1 : (⊥ : Subgroup R).relIndex K = Nat.card K := Subgroup.relIndex_bot_left K
    have hbot2 : (⊥ : Subgroup R).relIndex Ω = Nat.card Ω := Subgroup.relIndex_bot_left Ω
    have hmrr := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup R) K Ω
      (bot_le) (inf_le_left)
    rw [hbot1, hbot2] at hmrr
    -- `(⊥).relIndex K = Nat.card K` and `K.relIndex Ω = (Ω⊓H).relIndex Ω`.
    simpa [hK_def] using hmrr
  -- Combine: `|Ω| ≤ p · p = p²`.
  rw [← hΩ_factor]
  calc Nat.card K * (Ω ⊓ H).relIndex Ω ≤ p * p := Nat.mul_le_mul hK_le hrel_le
    _ = p ^ 2 := by rw [sq]

/-- **BG Lemma 4.5(b)**, generator form (**G** Thms 5.4.3/5.4.4). For `p` odd, a noncyclic
`p`-group `R` such that `⟨x⟩ = Subgroup.zpowers x` has index `p` has `Ω₁(R)` elementary
abelian of order `p²`.

The hard content `|Ω₁(R)| ≤ p²` is `card_omega1_le_prime_sq_of_cyclic_index_prime`
(proven from the cyclic-index-`p` hypothesis via `cl(R) ≤ 2`, NOT hoisted). The finisher
is the prime-square classification. `Ω₁(R)` is noncyclic because the two distinct order-`p`
subgroups of `R` (Isaacs Thm 6.11) both lie in `Ω₁(R)`. The BG-facing statement
(`isElementaryAbelian_omega1_of_isCyclic_index_prime`) takes an abstract cyclic subgroup
`H` of index `p` and is reduced to this by extracting a generator. -/
theorem isElementaryAbelian_omega1_of_cyclic_index_prime
    (hR : IsPGroup p R) (hp_odd : Odd p) (hnc : ¬ IsCyclic R)
    {x : R} (hHidx : (Subgroup.zpowers x).index = p) :
    (Omega R p 1).IsElementaryAbelian p ∧ Nat.card (Omega R p 1) = p ^ 2 := by
  have hp_prime : p.Prime := Fact.out
  set Ω : Subgroup R := Omega R p 1 with hΩ_def
  -- `Ω` is a `p`-group.
  have hΩ_pgroup : IsPGroup p Ω := hR.to_subgroup _
  -- `|Ω| ≤ p²` (the genuine crux).
  have hle : Nat.card Ω ≤ p ^ 2 :=
    card_omega1_le_prime_sq_of_cyclic_index_prime hR hp_odd hHidx
  -- `Ω` is noncyclic: pull `R`'s two distinct order-`p` subgroups into `Ω`.
  have hΩ_nc : ¬ IsCyclic Ω := by
    obtain ⟨Ksub, Lsub, hK, hL, hKL⟩ :=
      exists_distinct_subgroups_card_prime_of_not_isCyclic hR hp_odd hnc
    -- order-`p` subgroups consist of `p`-torsion, hence sit inside `Ω`.
    have mem_omega_of_card_p : ∀ (M : Subgroup R), Nat.card M = p → M ≤ Ω := by
      intro M hM g hg
      have hgp : g ^ p = 1 := by
        have hM1 : (⟨g, hg⟩ : M) ^ Nat.card M = 1 := pow_card_eq_one'
        have hcoe : g ^ Nat.card M = 1 := by
          have := congrArg (Subtype.val) hM1
          rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
        rwa [hM] at hcoe
      exact Omega.mem_of_pow_eq_one (by rw [pow_one]; exact hgp)
    have hKΩ : Ksub ≤ Ω := mem_omega_of_card_p Ksub hK
    have hLΩ : Lsub ≤ Ω := mem_omega_of_card_p Lsub hL
    intro hcyc
    have : IsCyclic Ω := hcyc
    -- `Ω` has exponent dividing `p` (class ≤ 2 + odd), and cyclic ⇒ `|Ω| = exponent ∣ p`.
    have hcl : _root_.commutator R ≤ Subgroup.center R :=
      commutator_le_center_of_cyclic_index_prime hR hp_odd hHidx
    have hexp_dvd : Monoid.exponent Ω ∣ p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro g; apply Subtype.ext
      rw [SubmonoidClass.coe_pow]
      simpa using Omega.pow_eq_one_of_class_le_two hp_odd hcl g.2
    have hΩcard_dvd : Nat.card Ω ∣ p := by
      rw [IsCyclic.exponent_eq_card (α := Ω)] at hexp_dvd; exact hexp_dvd
    -- `|Ksub| = p ≤ |Ω| ∣ p` ⇒ `|Ω| = p`, then `Ksub = Ω` and `Lsub = Ω` by card.
    have hp_le_Ω : p ≤ Nat.card Ω := hK ▸ Subgroup.card_le_of_le hKΩ
    have hΩ_le_p : Nat.card Ω ≤ p := Nat.le_of_dvd hp_prime.pos hΩcard_dvd
    have hΩcard : Nat.card Ω = p := le_antisymm hΩ_le_p hp_le_Ω
    have hKeq : Ksub = Ω := Subgroup.eq_of_le_of_card_ge hKΩ (by rw [hΩcard, hK])
    have hLeq : Lsub = Ω := Subgroup.eq_of_le_of_card_ge hLΩ (by rw [hΩcard, hL])
    exact hKL (hKeq.trans hLeq.symm)
  -- Finisher: noncyclic + `≤ p²` ⇒ `E_{p²}`.
  obtain ⟨hElem, hCard⟩ :=
    hΩ_pgroup.isElementaryAbelian_card_prime_sq_of_card_le_prime_sq_of_not_isCyclic hle hΩ_nc
  exact ⟨hElem, hCard⟩

/-- **BG Lemma 4.5(b)** (**G** Thms 5.4.3/5.4.4). For `p` odd, a noncyclic `p`-group `R`
possessing a cyclic subgroup `H` of index `p` has `Ω₁(R)` elementary abelian of order `p²`.

This is the faithful BG statement: `H` is an abstract cyclic subgroup of index `p`. The
proof extracts a generator (`H = Subgroup.zpowers x`) and applies the generator-form
`isElementaryAbelian_omega1_of_cyclic_index_prime`. Callers (BG Prop 4.11 / Thm 4.12)
instantiate `R` at a noncyclic subgroup `S₁` having a cyclic subgroup `S` of relative
index `p`. -/
theorem isElementaryAbelian_omega1_of_isCyclic_index_prime
    (hR : IsPGroup p R) (hp_odd : Odd p) (hnc : ¬ IsCyclic R)
    {H : Subgroup R} (hHcyc : IsCyclic H) (hidx : H.index = p) :
    (Omega R p 1).IsElementaryAbelian p ∧ Nat.card (Omega R p 1) = p ^ 2 := by
  -- Extract an ambient generator `x` with `H = ⟨x⟩`.
  obtain ⟨x, hx⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top H).mp hHcyc
  have hHidx : (Subgroup.zpowers x).index = p := by rw [hx]; exact hidx
  exact isElementaryAbelian_omega1_of_cyclic_index_prime hR hp_odd hnc hHidx

end CyclicIndexP

section MetacyclicOmega

open OddOrder.GroupTheory

variable {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]

/-- A nontrivial finite cyclic `p`-group `Q` has `|Ω₁(Q)| = p`.

`Q` cyclic ⇒ commutative, so the generating set `{g | g^p = 1}` of `Ω₁(Q) = Omega Q p 1`
is already the kernel of the `p`-th power map (`powMonoidHom p`), hence
`Ω₁(Q) = (powMonoidHom p).ker`. Its cardinality is `(|Q|).gcd p`
(`IsCyclic.card_powMonoidHom_ker`); for a nontrivial `p`-group `|Q| = p^k` with `k ≥ 1`, so
`gcd(p^k, p) = p`. -/
theorem card_omega1_eq_prime_of_isCyclic
    {Q : Type*} [Group Q] [Finite Q] [IsCyclic Q] [Nontrivial Q] (hQ : IsPGroup p Q) :
    Nat.card (Omega Q p 1) = p := by
  have hp_prime : p.Prime := Fact.out
  -- `Q` is commutative; use it for the `powMonoidHom` kernel cardinality lemma.
  let : CommGroup Q := IsCyclic.commGroup
  -- `Ω₁(Q) = (powMonoidHom p).ker`: the generating set `{g | g^(p^1)=1}` *is* the kernel.
  have hset : {g : Q | g ^ (p ^ 1) = 1} = ((powMonoidHom p : Q →* Q).ker : Set Q) := by
    ext g
    simp only [Set.mem_ofPred_eq, pow_one, SetLike.mem_coe, MonoidHom.mem_ker, powMonoidHom_apply]
  have hΩ_ker : Omega Q p 1 = (powMonoidHom p : Q →* Q).ker := by
    rw [Omega, hset, Subgroup.closure_eq]
  -- `|Q| = p^k` with `k ≥ 1` (nontrivial `p`-group).
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  have hk_pos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · exact absurd (by rw [hk, hk0, pow_zero] : Nat.card Q = 1)
        (by simpa using (Finite.one_lt_card (α := Q)).ne')
    · exact hk0
  -- `gcd(p^k, p) = p`.
  have hgcd : (Nat.card Q).gcd p = p := by
    rw [hk]; exact Nat.gcd_eq_right (dvd_pow_self p hk_pos.ne')
  rw [hΩ_ker, IsCyclic.card_powMonoidHom_ker (G := Q) p, hgcd]

/-- In a finite cyclic group `C`, two subgroups of order `p` (`p` prime) are equal.

This is the uniqueness half behind "noncyclic ⇒ two distinct order-`p` subgroups". Proof: any
order-`p` subgroup `K` has every element `p`-torsion (Lagrange), so `K ≤ (powMonoidHom p).ker`;
and `|ker| = gcd(|C|, p) = p` since `p = |K|` divides `|C|`. Equal cardinalities force
`K = ker`, so both `K` and `L` equal that unique kernel. -/
private theorem subgroup_card_prime_unique_of_isCyclic
    {C : Type*} [Group C] [Finite C] [IsCyclic C] {K L : Subgroup C}
    (hK : Nat.card K = p) (hL : Nat.card L = p) : K = L := by
  have hp_prime : p.Prime := Fact.out
  let : CommGroup C := IsCyclic.commGroup
  -- Each order-`p` subgroup equals the unique order-`p` kernel `(powMonoidHom p).ker`.
  have key : ∀ {M : Subgroup C}, Nat.card M = p → M = (powMonoidHom p : C →* C).ker := by
    intro M hM
    -- `M ≤ ker`: every element of `M` is `p`-torsion (Lagrange in `M`).
    have hM_le : M ≤ (powMonoidHom p : C →* C).ker := by
      intro g hg
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      have hg1 : (⟨g, hg⟩ : M) ^ Nat.card M = 1 := pow_card_eq_one'
      have := congrArg (Subtype.val) hg1
      rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one, hM] at this
    -- `|ker| = gcd(|C|, p) = p` (as `p = |M| ∣ |C|`).
    have hp_dvd : p ∣ Nat.card C := hM ▸ M.card_subgroup_dvd_card
    have hker_card : Nat.card (powMonoidHom p : C →* C).ker = p := by
      rw [IsCyclic.card_powMonoidHom_ker (G := C) p, Nat.gcd_eq_right hp_dvd]
    exact Subgroup.eq_of_le_of_card_ge hM_le (by rw [hker_card, hM])
  exact (key hK).trans (key hL).symm

/-- **BG Lemma 4.10** (mmd L1546-1552). For `p` odd, a noncyclic metacyclic `p`-group `R`
has `Ω₁(R)` elementary abelian of order `p²`.

Reduction to BG Lemma 4.5(b) (`isElementaryAbelian_omega1_of_isCyclic_index_prime`): with
`S ⊴ R` cyclic and `R/S` cyclic, the subgroup `T = comap (mk' S) (Ω₁(R/S))` satisfies
`Ω₁(R) = (Ω₁ ↥T).map T.subtype` and contains `S` with `S.relIndex T = p`; apply 4.5(b) to the
noncyclic `↥T` (cyclic subgroup `S.subgroupOf T` of index `p`) and transfer. -/
theorem isElementaryAbelian_omega1_of_isMetacyclic
    (hR : IsPGroup p R) (hp_odd : Odd p) (hmeta : IsMetacyclic R) (hnc : ¬ IsCyclic R) :
    (Omega R p 1).IsElementaryAbelian p ∧ Nat.card (Omega R p 1) = p ^ 2 := by
  classical
  -- Unpack the metacyclic structure.
  obtain ⟨S, hS_norm, hS_cyc, hQ_cyc⟩ := hmeta
  have := hS_norm
  have : IsCyclic (R ⧸ S) := hQ_cyc
  -- `R/S` is nontrivial: else `S = ⊤` and `R ≅ ↥S` is cyclic, contradicting `hnc`.
  have hQ_nontriv : Nontrivial (R ⧸ S) := by
    rcases subsingleton_or_nontrivial (R ⧸ S) with hsub | hnt
    · exfalso
      -- `R⧸S` subsingleton ⇒ `S.index = 1` ⇒ `S = ⊤`; then `↥(⊤) ≅ R` is cyclic.
      have hidx1 : S.index = 1 := by
        rw [Subgroup.index, Nat.card_eq_one_iff_unique]
        exact ⟨hsub, ⟨1⟩⟩
      have hStop : S = ⊤ := Subgroup.index_eq_one.mp hidx1
      have : IsCyclic ↥(⊤ : Subgroup R) := hStop ▸ hS_cyc
      exact hnc (isCyclic_of_surjective (Subgroup.topEquiv (G := R)).toMonoidHom
        (Subgroup.topEquiv (G := R)).surjective)
    · exact hnt
  have hQ_pgroup : IsPGroup p (R ⧸ S) := hR.to_quotient S
  -- `T := comap (mk' S) (Ω₁(R/S))`; `S ≤ T`.
  set T : Subgroup R := Subgroup.comap (QuotientGroup.mk' S) (Omega (R ⧸ S) p 1) with hT_def
  have hS_le_T : S ≤ T := by
    rw [hT_def]; exact QuotientGroup.le_comap_mk' S _
  have hT_pgroup : IsPGroup p T := hR.to_subgroup T
  -- (a) `Ω₁(R) = (Ω₁ ↥T).map T.subtype`.
  have hΩ_eq : Omega R p 1 = (Omega (↥T) p 1).map T.subtype := by
    apply le_antisymm
    · -- ⊆ : push each generator `g` (with `g^p = 1`) of `Ω₁(R)` into `T`, then into `Ω₁ ↥T`.
      rw [Omega, Subgroup.closure_le]
      intro g (hg : g ^ (p ^ 1) = 1)
      rw [pow_one] at hg
      have hgT : g ∈ T := by
        rw [hT_def, Subgroup.mem_comap]
        refine Omega.mem_of_pow_eq_one ?_
        rw [pow_one, ← map_pow, hg, map_one]
      change g ∈ Subgroup.map T.subtype (Omega (↥T) p 1)
      rw [Subgroup.mem_map]
      refine ⟨⟨g, hgT⟩, ?_, rfl⟩
      refine Omega.mem_of_pow_eq_one ?_
      rw [pow_one]
      ext
      rw [SubmonoidClass.coe_pow, Subgroup.coe_mk, OneMemClass.coe_one, hg]
    · -- ⊇ : the image of an `Ω₁ ↥T` generator lies in `Ω₁(R)`.
      rw [Subgroup.map_le_iff_le_comap, Omega, Subgroup.closure_le]
      rintro ⟨g, hgT⟩ (hg : (⟨g, hgT⟩ : ↥T) ^ (p ^ 1) = 1)
      change (⟨g, hgT⟩ : ↥T) ∈ Subgroup.comap T.subtype (Omega R p 1)
      rw [Subgroup.mem_comap]
      refine Omega.mem_of_pow_eq_one ?_
      rw [pow_one]
      have hval := congrArg (Subgroup.subtype T) hg
      rw [map_pow, pow_one, map_one] at hval
      simpa using hval
  -- `Ω₁(R) ≤ T` (image under `T.subtype` lands in `T`).
  have hΩ_le_T : Omega R p 1 ≤ T := by
    rw [hΩ_eq]; exact Subgroup.map_subtype_le _
  -- (b) `S.relIndex T = p`.
  have hSrel : S.relIndex T = p := by
    have hker : S = (QuotientGroup.mk' S).ker := (QuotientGroup.ker_mk' S).symm
    rw [hker, Subgroup.relIndex_ker, hT_def,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective S)]
    exact card_omega1_eq_prime_of_isCyclic hQ_pgroup
  -- `↥T` noncyclic: pull `R`'s two distinct order-`p` subgroups into `↥T`.
  have hT_nc : ¬ IsCyclic ↥T := by
    intro hTcyc
    obtain ⟨Ksub, Lsub, hK, hL, hKL⟩ :=
      exists_distinct_subgroups_card_prime_of_not_isCyclic hR hp_odd hnc
    -- order-`p` subgroups of `R` sit inside `Ω₁(R) ≤ T`.
    have mem_omega_of_card_p : ∀ (M : Subgroup R), Nat.card M = p → M ≤ T := by
      intro M hM g hg
      have hgp : g ^ p = 1 := by
        have hM1 : (⟨g, hg⟩ : M) ^ Nat.card M = 1 := pow_card_eq_one'
        have hcoe : g ^ Nat.card M = 1 := by
          have := congrArg (Subtype.val) hM1
          rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
        rwa [hM] at hcoe
      exact hΩ_le_T (Omega.mem_of_pow_eq_one (by rw [pow_one]; exact hgp))
    have hKT : Ksub ≤ T := mem_omega_of_card_p Ksub hK
    have hLT : Lsub ≤ T := mem_omega_of_card_p Lsub hL
    -- their `subgroupOf T` versions have order `p`; uniqueness in cyclic `↥T` forces equality.
    have hcardK : Nat.card (Ksub.subgroupOf T) = p := by
      rw [← Subgroup.card_map_of_injective (K := Ksub.subgroupOf T) (f := T.subtype)
            T.subtype_injective,
        Subgroup.subgroupOf_map_subtype, inf_of_le_left hKT, hK]
    have hcardL : Nat.card (Lsub.subgroupOf T) = p := by
      rw [← Subgroup.card_map_of_injective (K := Lsub.subgroupOf T) (f := T.subtype)
            T.subtype_injective,
        Subgroup.subgroupOf_map_subtype, inf_of_le_left hLT, hL]
    have hsub_eq : Ksub.subgroupOf T = Lsub.subgroupOf T :=
      subgroup_card_prime_unique_of_isCyclic hcardK hcardL
    -- map back along `T.subtype` to recover `Ksub = Lsub`, contradiction.
    apply hKL
    have := congrArg (Subgroup.map T.subtype) hsub_eq
    rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hKT, inf_of_le_left hLT] at this
  -- `S.subgroupOf T` is cyclic (`≅ ↥S`) of index `p`.
  have hSsub_cyc : IsCyclic ↥(S.subgroupOf T) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hS_le_T).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hS_le_T).symm.surjective
  have hSsub_idx : (S.subgroupOf T).index = p := hSrel
  -- Apply Lemma 4.5(b) to `↥T`.
  obtain ⟨hΩT_elem, hΩT_card⟩ :=
    isElementaryAbelian_omega1_of_isCyclic_index_prime hT_pgroup hp_odd hT_nc
      hSsub_cyc hSsub_idx
  -- Transfer `E_{p²}` across `T.subtype`.
  refine ⟨?_, ?_⟩
  · rw [hΩ_eq]; exact hΩT_elem.map T.subtype_injective
  · rw [hΩ_eq, Subgroup.card_map_of_injective T.subtype_injective]; exact hΩT_card

end MetacyclicOmega

section ConverseLemma45

open OddOrder.GroupTheory

variable {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]

/-- **Converse of BG Lemma 4.5**: a finite `p`-group (`p` odd) with `|Ω₁(R)| ≤ p` is cyclic.

Every order-`p` subgroup lies in `Ω₁(R)`; if `|Ω₁(R)| ≤ p` it is the unique such subgroup,
so `R` is cyclic by Isaacs Thm 6.11
(`OddOrder.Isaacs.Ch06.isCyclic_of_subgroups_card_prime_unique_of_odd`).

Used in BG Thm 4.12(a) (mmd L1608, L1612) — the `|Ω₁(X)| ≤ p ⇒ X` cyclic and
`|Ω₁(R/S)| ≤ p ⇒ R/S` cyclic steps — and reusable for Prop 4.11. -/
theorem isCyclic_of_card_omega1_le_prime (hR : IsPGroup p R) (hp_odd : Odd p)
    (hΩ : Nat.card (Omega R p 1) ≤ p) : IsCyclic R := by
  apply OddOrder.Isaacs.Ch06.isCyclic_of_subgroups_card_prime_unique_of_odd hR hp_odd
  intro K L hK hL
  -- Every order-`p` subgroup consists of `p`-torsion, hence lies in `Ω₁(R)`.
  have memle : ∀ M : Subgroup R, Nat.card M = p → M ≤ Omega R p 1 := by
    intro M hM g hg
    have hgp : g ^ p = 1 := by
      have h1 : (⟨g, hg⟩ : M) ^ Nat.card M = 1 := pow_card_eq_one'
      have := congrArg Subtype.val h1
      rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one, hM] at this
    exact Omega.mem_of_pow_eq_one (by rw [pow_one]; exact hgp)
  -- `|M| = p ≥ |Ω₁|` forces `M = Ω₁(R)`, so the order-`p` subgroup is unique.
  rw [Subgroup.eq_of_le_of_card_ge (memle K hK) (by rw [hK]; exact hΩ),
      Subgroup.eq_of_le_of_card_ge (memle L hL) (by rw [hL]; exact hΩ)]

end ConverseLemma45

end OddOrder.BG.Ch1.S04


