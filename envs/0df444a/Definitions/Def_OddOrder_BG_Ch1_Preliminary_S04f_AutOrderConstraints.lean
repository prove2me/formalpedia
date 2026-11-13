-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04f_AutOrderConstraints
-- name    : OddOrder_BG_Ch1_Preliminary_S04f_AutOrderConstraints
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:00:49.347268+00:00
-- url     : https://prove2.me/theorems/d913750b-8245-499d-b66b-692cfa630a5a
-- title:
--   BG §4E: automorphism-order constraints (Lemmas 4.13 and 4.14)
-- statement:
--   Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §4E: constraints on the order of automorphisms (Lemmas 4.13 and 4.14).
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 14 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S04f_AutOrderConstraints.lean

/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S04f_AutOrderConstraints.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04b_Thm412
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04c_Prop411
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04d_GorThm415
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04e_GorThm37
import Definitions.Def_OddOrder_GroupTheory_CentralProduct
import Mathlib.GroupTheory.Perm.Cycle.Type

open scoped Pointwise commutatorElement

namespace OddOrder.BG.Ch1.S04

open OddOrder.GroupTheory

open OddOrder.Isaacs.Ch03 (IsAInvariant)

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply)

open OddOrder.BG.Ch1_Preliminary (isAInvariant_map_subtype_of_restrict
  isAInvariant_subgroupOf_restrict)

section AutOrderConstraints

/-- Arithmetic half of BG Lemma 4.14.  For odd `p`, every prime divisor `q` of
`p^2 - 1` divides one of the half-factors `(p + 1) / 2` or `(p - 1) / 2`.

The only small wrinkle is `q = 2`: since `p` is odd, exactly one of
`(p - 1) / 2`, `(p + 1) / 2` is even.  For odd `q`, remove the factor `4` from
`p^2 - 1 = 4 * ((p - 1) / 2) * ((p + 1) / 2)`. -/
private theorem prime_dvd_half_factor_of_odd_dvd_sq_sub_one {p q : ℕ}
    (hp_odd : Odd p) (hq : q.Prime) (hq_dvd : q ∣ p ^ 2 - 1) :
    q ∣ (p + 1) / 2 ∨ q ∣ (p - 1) / 2 := by
  classical
  by_cases hq2 : q = 2
  · subst q
    have hp_repr : 2 * (p / 2) + 1 = p := Nat.two_mul_div_two_add_one_of_odd hp_odd
    have hsub : (p - 1) / 2 = p / 2 := by omega
    have hadd : (p + 1) / 2 = p / 2 + 1 := by omega
    rcases Nat.even_or_odd (p / 2) with h_even | h_odd
    · right
      rw [hsub]
      exact Even.two_dvd h_even
    · left
      rw [hadd]
      exact Even.two_dvd h_odd.add_one
  · set a := (p - 1) / 2 with ha
    set b := (p + 1) / 2 with hb
    have hsub_even : Even (p - 1) := by
      rcases hp_odd with ⟨k, rfl⟩
      rw [Nat.add_sub_cancel]
      exact even_two_mul k
    have hadd_even : Even (p + 1) := hp_odd.add_one
    have hsub : p - 1 = 2 * a := by
      rw [ha]
      exact (Nat.two_mul_div_two_of_even hsub_even).symm
    have hadd : p + 1 = 2 * b := by
      rw [hb]
      exact (Nat.two_mul_div_two_of_even hadd_even).symm
    have hsq : p ^ 2 - 1 = (p - 1) * (p + 1) := by
      rcases p with _ | n
      · simp
      · rw [Nat.succ_sub_one,
          show (n + 1) ^ 2 = n * (n + 2) + 1 from by ring, Nat.add_sub_cancel]
    have hfac : p ^ 2 - 1 = 4 * (a * b) := by
      calc
        p ^ 2 - 1 = (p - 1) * (p + 1) := hsq
        _ = (2 * a) * (2 * b) := by rw [hsub, hadd]
        _ = 4 * (a * b) := by ring
    have hq_dvd_four_mul : q ∣ 4 * (a * b) := by rwa [hfac] at hq_dvd
    have hq_not_dvd_four : ¬ q ∣ 4 := by
      intro hq4
      have hq_le4 : q ≤ 4 := Nat.le_of_dvd (by norm_num) hq4
      have hq_ge2 : 2 ≤ q := hq.two_le
      interval_cases q
      · exact hq2 rfl
      · exact (by decide : ¬ 3 ∣ 4) hq4
      · exact (by decide : ¬ Nat.Prime 4) hq
    have hq_coprime_four : Nat.Coprime q 4 :=
      hq.coprime_iff_not_dvd.mpr hq_not_dvd_four
    have hq_dvd_ab : q ∣ a * b :=
      (Nat.Coprime.dvd_mul_left hq_coprime_four).mp hq_dvd_four_mul
    rcases hq.dvd_mul.mp hq_dvd_ab with hqa | hqb
    · right
      rwa [ha]
    · left
      rwa [hb]

/-- Cauchy extraction for BG Lemma 4.13: a prime divisor of `|Aut R|` is realized
by an automorphism of order exactly that prime. -/
private theorem exists_mulAut_orderOf_eq_prime_of_prime_dvd_card
    {R : Type*} [Group R] [Finite R] {q : ℕ}
    (hq : q.Prime) (hq_dvd : q ∣ Nat.card (MulAut R)) :
    ∃ ψ : MulAut R, orderOf ψ = q := by
  let : Fact q.Prime := ⟨hq⟩
  exact exists_prime_orderOf_dvd_card' q hq_dvd

/-- The cyclic automorphism group generated by a `q`-element acts with order
coprime to a finite `p`-group when `q ≠ p`. -/
private theorem coprime_card_zpowers_mulAut_of_prime_order_ne
    {R : Type*} [Group R] [Finite R] {p q : ℕ} [Fact p.Prime]
    (hR : IsPGroup p R) (hq : q.Prime) (hqp : q ≠ p)
    {ψ : MulAut R} (hψ_order : orderOf ψ = q) :
    Nat.Coprime (Nat.card (Subgroup.zpowers ψ)) (Nat.card R) := by
  obtain ⟨n, hn⟩ := hR.exists_card_eq
  rw [Nat.card_zpowers, hψ_order, hn]
  exact ((Nat.coprime_primes hq Fact.out).mpr hqp).pow_right n

/-- Subgroups inherit the BG Lemma 4.7 rank bound from the ambient `SCN₃`-empty
`p`-group. -/
private theorem pRank_subgroup_le_two_of_scn3_empty
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hp_odd : Odd p) (hR : IsPGroup p R)
    (hSCN : ∀ A : Subgroup R, ¬ IsSCN₃ p A) (Q : Subgroup R) :
    pRank Q p ≤ 2 :=
  (pRank_mono_of_le Q).trans (pRank_le_two_of_scn3_empty hp_odd hR hSCN)

/-- Abelian branch support for BG Lemma 4.13: an elementary abelian subgroup of an
`SCN₃`-empty finite `p`-group has order at most `p²`. -/
private theorem card_le_prime_sq_of_scn3_empty_elementaryAbelian_subgroup
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hp_odd : Odd p) (hR : IsPGroup p R)
    (hSCN : ∀ A : Subgroup R, ¬ IsSCN₃ p A) {Q : Subgroup R}
    (hQ : IsElementaryAbelian p Q) :
    Nat.card Q ≤ p ^ 2 := by
  have hQ_rank : pRank Q p ≤ 2 :=
    pRank_subgroup_le_two_of_scn3_empty hp_odd hR hSCN Q
  have hlog_le : Nat.log p (Nat.card Q) ≤ 2 := hQ.log_card_le_pRank.trans hQ_rank
  have hcard : Nat.card Q = p ^ Nat.log p (Nat.card Q) := by
    let : IsMulCommutative Q := IsMulCommutative.of_comm hQ.comm
    let := hQ.zmodModule
    rw [hQ.log_card_eq_finrank]
    exact hQ.card_eq_pow_finrank
  rw [hcard]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hlog_le

/-- Exponent-`p` support for BG Lemma 4.13: a subgroup of an `SCN₃`-empty finite
`p`-group with exponent `p` has order at most `p³`. -/
private theorem card_le_prime_cube_of_scn3_empty_exp_prime_subgroup
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hp_odd : Odd p) (hR : IsPGroup p R)
    (hSCN : ∀ A : Subgroup R, ¬ IsSCN₃ p A) {Q : Subgroup R}
    (hQ_exp : Monoid.exponent Q = p) :
    Nat.card Q ≤ p ^ 3 := by
  have hQ_rank : pRank Q p ≤ 2 :=
    pRank_subgroup_le_two_of_scn3_empty hp_odd hR hSCN Q
  have hQ_pow : ∀ x : Q, x ^ p = 1 := by
    intro x
    simpa [hQ_exp] using (Monoid.pow_exponent_eq_one x)
  exact card_le_prime_cube_of_pRank_le_two_of_exponent_prime
    (hR.to_subgroup Q) hQ_rank hQ_pow

/-- Frattini-quotient support for the non-elementary branch of BG Lemma 4.13.
If a finite `p`-group has order at most `p³` but is not elementary abelian, then
its Frattini quotient has order at most `p²`. -/
private theorem card_quotient_frattini_le_prime_sq_of_not_elementary
    {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hQ : IsPGroup p Q) (hQ_card : Nat.card Q ≤ p ^ 3)
    (hQ_not_elem : ¬ IsElementaryAbelian p Q) :
    Nat.card (Q ⧸ frattini Q) ≤ p ^ 2 := by
  have hp : p.Prime := Fact.out
  have hfr_ne_bot : frattini Q ≠ ⊥ := by
    intro hfr
    exact hQ_not_elem (hQ.isElementaryAbelian_of_frattini_eq_bot hfr)
  have hfr_pgroup : IsPGroup p (frattini Q) := hQ.to_subgroup (frattini Q)
  have hp_dvd_fr : p ∣ Nat.card (frattini Q) := by
    rcases hfr_pgroup.card_eq_or_dvd with hfr_card | hp_dvd
    · exact False.elim (hfr_ne_bot (Subgroup.eq_bot_of_card_eq _ hfr_card))
    · exact hp_dvd
  have hp_le_fr : p ≤ Nat.card (frattini Q) := Nat.le_of_dvd Nat.card_pos hp_dvd_fr
  have hlag : Nat.card Q = Nat.card (Q ⧸ frattini Q) * Nat.card (frattini Q) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini Q)
  have hmul_le : Nat.card (Q ⧸ frattini Q) * p ≤ p ^ 3 := by
    calc
      Nat.card (Q ⧸ frattini Q) * p
          ≤ Nat.card (Q ⧸ frattini Q) * Nat.card (frattini Q) :=
            Nat.mul_le_mul_left _ hp_le_fr
      _ = Nat.card Q := hlag.symm
      _ ≤ p ^ 3 := hQ_card
  have hmul_le_sq : Nat.card (Q ⧸ frattini Q) * p ≤ p ^ 2 * p := by
    calc
      Nat.card (Q ⧸ frattini Q) * p ≤ p ^ 3 := hmul_le
      _ = p ^ 2 * p := by ring
  exact Nat.le_of_mul_le_mul_right hmul_le_sq hp.pos

/-- In a nontrivial finite group, the Frattini subgroup is proper. -/
private theorem frattini_ne_top_of_nontrivial
    {Q : Type*} [Group Q] [Finite Q] [Nontrivial Q] :
    frattini Q ≠ ⊤ := by
  obtain ⟨M, hM, _⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup Q)).resolve_left bot_lt_top.ne
  exact fun htop => hM.1 (le_antisymm le_top (htop ▸ frattini_le_coatom hM))

/-- Quotient-action support for BG Lemma 4.13: if `ψ` fixes a normal invariant
subgroup but acts nontrivially on the whole group, then it acts nontrivially on
the quotient. -/
private theorem quotient_action_nontrivial_of_fixed_normal_and_nontrivial
    {A Q : Type*} [Group A] [Finite A] [Group Q] [Finite Q]
    {p : ℕ} [Fact p.Prime] {φ : A →* MulAut Q}
    (hQ : IsPGroup p Q) (hCop : Nat.Coprime (Nat.card A) (Nat.card Q))
    {ψ : A} {N : Subgroup Q} [N.Normal] (hN_inv : IsAInvariant φ N)
    (hfix : ∀ n ∈ N, (φ ψ) n = n)
    (hψ_nt : ¬ ∀ g : Q, (φ ψ) g = g) :
    ¬ ∀ x : Q ⧸ N, (quotientMulAutHom hN_inv ψ) x = x := by
  intro hquot
  apply hψ_nt
  exact acts_trivially_of_trivial_on_normal_quotient φ hQ hCop hN_inv hfix (by
    intro g
    have hg := hquot (g : Q ⧸ N)
    rw [quotientMulAutHom_apply, QuotientGroup.eq_iff_div_mem, div_eq_mul_inv] at hg
    exact hg)

/-- If an operator has prime-power-one relation and acts nontrivially on an
invariant subgroup, then its restricted automorphism has that prime order. -/
private theorem orderOf_restrict_eq_prime_of_pow_eq_one_and_nontrivial
    {A R : Type*} [Group A] [Group R] {φ : A →* MulAut R}
    {Q : Subgroup R} (hQ_inv : IsAInvariant φ Q) {ψ : A} {q : ℕ}
    (hq : q.Prime) (hψ_pow : ψ ^ q = 1)
    (hψ_nt : ∃ g ∈ Q, (φ ψ) g ≠ g) :
    orderOf (hQ_inv.restrict ψ) = q := by
  have hres_ne_one : hQ_inv.restrict ψ ≠ 1 := by
    intro hres
    obtain ⟨g, hgQ, hg⟩ := hψ_nt
    apply hg
    have hfix : (hQ_inv.restrict ψ) ⟨g, hgQ⟩ = ⟨g, hgQ⟩ := by
      rw [hres]
      rfl
    exact congrArg Subtype.val hfix
  have hres_pow : (hQ_inv.restrict ψ) ^ q = 1 := by
    rw [← map_pow, hψ_pow, map_one]
  have hdvd : orderOf (hQ_inv.restrict ψ) ∣ q := orderOf_dvd_of_pow_eq_one hres_pow
  rcases hq.eq_one_or_self_of_dvd _ hdvd with h1 | hqeq
  · exact (hres_ne_one (orderOf_eq_one_iff.mp h1)).elim
  · exact hqeq

/-- Minimality support for BG Lemma 4.13: if `Q` is minimal among `φ`-invariant
subgroups on which `ψ` acts nontrivially, then `ψ` fixes every proper
`φ`-invariant subgroup of `Q` pointwise. -/
private theorem acts_trivially_on_proper_of_minimal_nontrivial
    {A R : Type*} [Group A] [Group R] {φ : A →* MulAut R}
    {Q : Subgroup R} {ψ : A}
    (hmin : ∀ N : Subgroup R, IsAInvariant φ N → N ≤ Q →
      (∃ g ∈ N, (φ ψ) g ≠ g) → N = Q)
    {N : Subgroup R} (hN_inv : IsAInvariant φ N) (hN_le : N ≤ Q)
    (hN_ne : N ≠ Q) :
    ∀ n ∈ N, (φ ψ) n = n := by
  intro n hn
  by_contra hn_ne
  exact hN_ne (hmin N hN_inv hN_le ⟨n, hn, hn_ne⟩)

/-- Restricted form of `acts_trivially_on_proper_of_minimal_nontrivial`, for
proper invariant subgroups of the selected subgroup `Q`. -/
private theorem restrict_acts_trivially_on_proper_of_minimal_nontrivial
    {A R : Type*} [Group A] [Group R] {φ : A →* MulAut R}
    {Q : Subgroup R} (hQ_inv : IsAInvariant φ Q) {ψ : A}
    (hmin : ∀ N : Subgroup R, IsAInvariant φ N → N ≤ Q →
      (∃ g ∈ N, (φ ψ) g ≠ g) → N = Q)
    {K : Subgroup Q} (hK_inv : IsAInvariant hQ_inv.restrict K)
    (hK_ne : K ≠ ⊤) :
    ∀ z ∈ K, (hQ_inv.restrict ψ) z = z := by
  intro z hz
  let N : Subgroup R := K.map Q.subtype
  have hN_inv : IsAInvariant φ N := isAInvariant_map_subtype_of_restrict hQ_inv hK_inv
  have hN_le : N ≤ Q := Subgroup.map_subtype_le K
  have hN_ne : N ≠ Q := by
    intro hNQ
    apply hK_ne
    have hQtop : Q = (⊤ : Subgroup Q).map Q.subtype := by
      rw [← MonoidHom.range_eq_map, Q.range_subtype]
    exact Subgroup.map_injective Q.subtype_injective (hNQ.trans hQtop)
  apply Subtype.ext
  rw [IsAInvariant.restrict_apply_val]
  exact acts_trivially_on_proper_of_minimal_nontrivial hmin hN_inv hN_le hN_ne
    (z : R) (Subgroup.mem_map_of_mem _ hz)

/-- **BG Lemma 4.13** (via Gorenstein Theorem 4.15(ii)). Suppose `p` is an odd
prime, `R` is a finite `p`-group, and `q` is a prime divisor of `|Aut R|`. If
`SCN₃(R)` is empty and `q ≠ p`, then `q ∣ p^2 - 1` and `q < p`.

The proof is the remaining assembly of `pRank_le_two_of_scn3_empty`,
`exists_minimal_aInvariant_isExpPSpecial_of_pprimeAction`, and the existing
rank-`≤ 2` linear automorphism bounds in `PRank.lean`. -/
theorem dvd_prime_sq_sub_one_and_lt_of_prime_dvd_aut_of_scn3_empty
    {R : Type*} [Group R] [Finite R] {p q : ℕ} [Fact p.Prime]
    (hp_odd : Odd p) (hR : IsPGroup p R)
    (hSCN : ∀ A : Subgroup R, ¬ IsSCN₃ p A)
    (hq : q.Prime) (hqp : q ≠ p) (hq_dvd : q ∣ Nat.card (MulAut R)) :
    q ∣ p ^ 2 - 1 ∧ q < p := by
  obtain ⟨ψ, hψ_order⟩ := exists_mulAut_orderOf_eq_prime_of_prime_dvd_card hq hq_dvd
  have hψ_ne_one : ψ ≠ 1 := by
    intro hψ
    have hq_one : q = 1 := by rw [← hψ_order, hψ, orderOf_one]
    exact hq.ne_one hq_one
  let A : Subgroup (MulAut R) := Subgroup.zpowers ψ
  let φ : A →* MulAut R := A.subtype
  let ψA : A := ⟨ψ, Subgroup.mem_zpowers ψ⟩
  have hA_cop : Nat.Coprime (Nat.card A) (Nat.card R) := by
    dsimp [A]
    exact coprime_card_zpowers_mulAut_of_prime_order_ne hR hq hqp hψ_order
  have hψA_ntriv : ¬ ∀ g : R, (φ ψA) g = g := by
    intro hfix
    apply hψ_ne_one
    ext g
    exact hfix g
  obtain ⟨Q, hQ_inv, hψ_nt_Q, hQ_special, hQ_exp, hQ_min⟩ :=
    exists_minimal_aInvariant_isExpPSpecial_of_pprimeAction_with_minimality
      hp_odd φ hR hA_cop hψA_ntriv
  have hQ_rank : pRank Q p ≤ 2 :=
    pRank_subgroup_le_two_of_scn3_empty hp_odd hR hSCN Q
  have hQ_card_cube : Nat.card Q ≤ p ^ 3 :=
    card_le_prime_cube_of_scn3_empty_exp_prime_subgroup hp_odd hR hSCN hQ_exp
  have hQ_elem_card_le : IsElementaryAbelian p Q → Nat.card Q ≤ p ^ 2 :=
    card_le_prime_sq_of_scn3_empty_elementaryAbelian_subgroup hp_odd hR hSCN
  have hQ_quot_frattini_elem : IsElementaryAbelian p (Q ⧸ frattini Q) :=
    IsPGroup.quotient_frattini_isElementaryAbelian hQ_special.1
  have hQ_quot_frattini_card_le :
      ¬ IsElementaryAbelian p Q → Nat.card (Q ⧸ frattini Q) ≤ p ^ 2 :=
    card_quotient_frattini_le_prime_sq_of_not_elementary hQ_special.1 hQ_card_cube
  have hQ_nontrivial : Nontrivial Q := by
    obtain ⟨g, hgQ, hg⟩ := hψ_nt_Q
    have hg1 : g ≠ 1 := fun h => hg (by rw [h, map_one])
    exact ⟨⟨g, hgQ⟩, 1, fun h => hg1 (congrArg Subtype.val h)⟩
  have hQ_cop : Nat.Coprime (Nat.card A) (Nat.card Q) :=
    hA_cop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card Q)
  have hψA_pow : ψA ^ q = 1 := by
    apply Subtype.ext
    change ψ ^ q = 1
    rw [← hψ_order]
    exact pow_orderOf_eq_one ψ
  have hψQ_order : orderOf (hQ_inv.restrict ψA) = q :=
    orderOf_restrict_eq_prime_of_pow_eq_one_and_nontrivial hQ_inv hq hψA_pow hψ_nt_Q
  have hQ_min_fix : ∀ K : Subgroup Q, IsAInvariant hQ_inv.restrict K → K ≠ ⊤ →
      ∀ z ∈ K, (hQ_inv.restrict ψA) z = z :=
    fun K hK_inv hK_ne =>
      restrict_acts_trivially_on_proper_of_minimal_nontrivial hQ_inv hQ_min hK_inv hK_ne
  have hψ_nt_Q_restrict : ¬ ∀ x : Q, (hQ_inv.restrict ψA) x = x := by
    intro hfix
    obtain ⟨g, hgQ, hg⟩ := hψ_nt_Q
    apply hg
    have hgg := hfix ⟨g, hgQ⟩
    rwa [Subtype.ext_iff, IsAInvariant.restrict_apply_val] at hgg
  have hfr_inv : IsAInvariant hQ_inv.restrict (frattini Q) :=
    IsAInvariant.frattini hQ_inv.restrict
  have hfr_ne_top : frattini Q ≠ ⊤ := frattini_ne_top_of_nontrivial
  have hfr_fix : ∀ z ∈ frattini Q, (hQ_inv.restrict ψA) z = z :=
    hQ_min_fix (frattini Q) hfr_inv hfr_ne_top
  have hψ_fr_quot_nt :
      ¬ ∀ x : Q ⧸ frattini Q, (quotientMulAutHom hfr_inv ψA) x = x :=
    quotient_action_nontrivial_of_fixed_normal_and_nontrivial hQ_special.1 hQ_cop
      hfr_inv hfr_fix hψ_nt_Q_restrict
  have hψ_fr_quot_order : orderOf (quotientMulAutHom hfr_inv ψA) = q := by
    have hbar_ne_one : quotientMulAutHom hfr_inv ψA ≠ 1 := by
      intro hbar
      apply hψ_fr_quot_nt
      intro x
      rw [hbar]
      rfl
    have hbar_pow : (quotientMulAutHom hfr_inv ψA) ^ q = 1 := by
      rw [← map_pow, hψA_pow, map_one]
    have hdvd : orderOf (quotientMulAutHom hfr_inv ψA) ∣ q :=
      orderOf_dvd_of_pow_eq_one hbar_pow
    rcases hq.eq_one_or_self_of_dvd _ hdvd with h1 | hqeq
    · exact (hbar_ne_one (orderOf_eq_one_iff.mp h1)).elim
    · exact hqeq
  have hQ_elem_dvd : IsElementaryAbelian p Q → q ∣ p ^ 2 - 1 := by
    intro hQ_elem
    exact prime_dvd_prime_sq_sub_one_of_orderOf_mulAut hq hqp hQ_elem
      (hQ_elem_card_le hQ_elem) hψQ_order
  have hQ_elem_lt : IsElementaryAbelian p Q → q < p := by
    intro hQ_elem
    exact lt_of_prime_dvd_prime_sq_sub_one Fact.out hp_odd hq hqp (hQ_elem_dvd hQ_elem)
  have hQ_non_elem_dvd : ¬ IsElementaryAbelian p Q → q ∣ p ^ 2 - 1 := by
    intro hQ_not_elem
    exact prime_dvd_prime_sq_sub_one_of_orderOf_mulAut hq hqp hQ_quot_frattini_elem
      (hQ_quot_frattini_card_le hQ_not_elem) hψ_fr_quot_order
  have hQ_non_elem_lt : ¬ IsElementaryAbelian p Q → q < p := by
    intro hQ_not_elem
    exact lt_of_prime_dvd_prime_sq_sub_one Fact.out hp_odd hq hqp
      (hQ_non_elem_dvd hQ_not_elem)
  by_cases hQ_elem : IsElementaryAbelian p Q
  · exact ⟨hQ_elem_dvd hQ_elem, hQ_elem_lt hQ_elem⟩
  · exact ⟨hQ_non_elem_dvd hQ_elem, hQ_non_elem_lt hQ_elem⟩

/-- **BG Lemma 4.14.** Under the hypotheses of Lemma 4.13, `q` divides one of the
half-factors `(p + 1) / 2` or `(p - 1) / 2`.

BG derives this from Lemma 4.13 and the factorization
`p^2 - 1 = 4 * ((p - 1) / 2) * ((p + 1) / 2)` for odd `p`; the `q = 2` case is
absorbed by the same parity split. -/
theorem dvd_half_prime_add_or_sub_of_prime_dvd_aut_of_scn3_empty
    {R : Type*} [Group R] [Finite R] {p q : ℕ} [Fact p.Prime]
    (hp_odd : Odd p) (hR : IsPGroup p R)
    (hSCN : ∀ A : Subgroup R, ¬ IsSCN₃ p A)
    (hq : q.Prime) (hqp : q ≠ p) (hq_dvd : q ∣ Nat.card (MulAut R)) :
    q ∣ (p + 1) / 2 ∨ q ∣ (p - 1) / 2 := by
  exact prime_dvd_half_factor_of_odd_dvd_sq_sub_one hp_odd hq
    (dvd_prime_sq_sub_one_and_lt_of_prime_dvd_aut_of_scn3_empty hp_odd hR hSCN hq hqp
      hq_dvd).1

end AutOrderConstraints

end OddOrder.BG.Ch1.S04


