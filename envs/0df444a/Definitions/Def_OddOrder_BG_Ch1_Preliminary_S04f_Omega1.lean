-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04f_Omega1
-- name    : OddOrder_BG_Ch1_Preliminary_S04f_Omega1
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:04:31.408691+00:00
-- url     : https://prove2.me/theorems/c6e3e8c5-3fcf-4ff2-b24d-b9281bcdd1d7
-- title:
--   BG §4F: Blackburn's theorem, $\Omega_1$ part (Theorem 4.16)
-- statement:
--   Part of the Bender–Glauberman §4F development on Blackburn's classification (Theorem 4.16), concerning $\Omega_1$.
--
--   The main definition is `BlackburnCentralProductCase`, BG Theorem 4.16 case (2) (Blackburn): $R$ is the central product $R_1\circ R_2$.
--
--   The bundle also proves 33 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S04f_Omega1.lean

/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S04f_Omega1.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04b_Thm412
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04c_Prop411
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04d_GorThm415
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04e_GorThm37
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04f_AutOrderConstraints
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

section BlackburnClassification

/-- **BG Theorem 4.16, case (2)** (Blackburn): `R` is the central product
`R₁ ∘ R₂`, where `R₁` is nonabelian of order `p^3` and exponent `p`, `R₂` is
cyclic, and `Ω₁(R₂) = R₁'`.

The equality `Ω₁(R₂) = R₁'` is stated after mapping both subgroups into the
ambient group `R`: `Ω₁(R₂)` is `(Omega R₂ p 1).map R₂.subtype`, and `R₁'` is
`(commutator R₁).map R₁.subtype`. -/
def BlackburnCentralProductCase (p : ℕ) (R : Type*) [Group R] : Prop :=
  ∃ R₁ R₂ : Subgroup R,
    IsCentralProduct (⊤ : Subgroup R) R₁ R₂ ∧
      ¬ IsMulCommutative ↥R₁ ∧
      Nat.card ↥R₁ = p ^ 3 ∧
      Monoid.exponent ↥R₁ = p ∧
      IsCyclic ↥R₂ ∧
      (Omega ↥R₂ p 1).map R₂.subtype =
        (_root_.commutator ↥R₁).map R₁.subtype

/-- Nontriviality bridge for Blackburn 4.16: if `[R,A]=R` and `R ≠ 1`, then the image
of the operator group supplies a prime divisor common to `|A|` and `|Aut R|`. -/
private theorem exists_prime_dvd_actor_and_aut_of_actionCommutator_eq_top
    {R : Type*} [Group R] [Finite R] [Nontrivial R]
    {A : Type*} [Group A] [Finite A] {φ : A →* MulAut R}
    (hRA : OddOrder.Isaacs.Ch04.actionCommutator φ = ⊤) :
    ∃ q : ℕ, q.Prime ∧ q ∣ Nat.card A ∧ q ∣ Nat.card (MulAut R) := by
  have hφ_range_ne_bot : φ.range ≠ (⊥ : Subgroup (MulAut R)) := by
    intro hφ_range_bot
    have htriv : ∀ a : A, ∀ g : R, (φ a) g = g := by
      intro a g
      have ha : φ a ∈ φ.range := ⟨a, rfl⟩
      rw [hφ_range_bot] at ha
      have hφa : φ a = 1 := Subgroup.mem_bot.mp ha
      rw [hφa]
      rfl
    have hcomm_bot : OddOrder.Isaacs.Ch04.actionCommutator φ = ⊥ :=
      (OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_iff_acts_trivially φ).mpr htriv
    have htop_bot : (⊤ : Subgroup R) = ⊥ := by rw [← hRA, hcomm_bot]
    exact (top_ne_bot : (⊤ : Subgroup R) ≠ ⊥) htop_bot
  have hcard_ne_one : Nat.card φ.range ≠ 1 := fun hcard =>
    hφ_range_ne_bot (Subgroup.card_eq_one.mp hcard)
  obtain ⟨q, hq, hq_dvd_range⟩ := Nat.exists_prime_and_dvd hcard_ne_one
  exact ⟨q, hq, hq_dvd_range.trans (Subgroup.card_range_dvd φ),
    hq_dvd_range.trans (Subgroup.card_subgroup_dvd_card φ.range)⟩

/-- The first conclusion of Blackburn 4.16. BG derives `p > 3` immediately from
Lemma 4.13/4.14: a nontrivial odd `p'` operator image provides an odd prime
`q ≠ p` dividing `|Aut R|`; when `p = 3`, Lemma 4.14 forces `q ∣ 2` or `q ∣ 1`. -/
theorem three_lt_of_odd_coprime_actionCommutator_top_rank_le_two
    {R : Type*} [Group R] [Finite R] [Nontrivial R]
    {p : ℕ} [Fact p.Prime] (hp_odd : Odd p) (hR : IsPGroup p R)
    {A : Type*} [Group A] [Finite A] {φ : A →* MulAut R}
    (hcop : Nat.Coprime (Nat.card A) (Nat.card R))
    (hrank : pRank R p ≤ 2)
    (hRA : OddOrder.Isaacs.Ch04.actionCommutator φ = ⊤)
    (hAodd : Odd (Nat.card A)) :
    3 < p := by
  have hp : p.Prime := Fact.out
  obtain ⟨q, hq, hq_dvd_A, hq_dvd_aut⟩ :=
    exists_prime_dvd_actor_and_aut_of_actionCommutator_eq_top (φ := φ) hRA
  have hp_dvd_R : p ∣ Nat.card R := by
    rcases hR.card_eq_or_dvd with hcard | hdvd
    · have hR_card_gt_one : 1 < Nat.card R :=
        Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      omega
    · exact hdvd
  have hq_ne_p : q ≠ p := by
    intro hqp
    have hp_dvd_A : p ∣ Nat.card A := by simpa [hqp] using hq_dvd_A
    exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hp_dvd_A hp_dvd_R) hcop
  have hq_ne_two : q ≠ 2 := by
    intro hq2
    have h2_dvd_A : 2 ∣ Nat.card A := by simpa [hq2] using hq_dvd_A
    exact (Nat.not_even_iff_odd.mpr hAodd) (even_iff_two_dvd.mpr h2_dvd_A)
  by_contra hp_not_three_lt
  have hp_ne_two : p ≠ 2 := by
    intro hp2
    rw [hp2] at hp_odd
    rcases hp_odd with ⟨k, hk⟩
    omega
  have hp_eq_three : p = 3 := by
    have hp_ge_two : 2 ≤ p := hp.two_le
    omega
  have hSCN : ∀ B : Subgroup R, ¬ IsSCN₃ p B :=
    scn3_empty_of_pRank_le_two hrank
  have hhalf :=
    dvd_half_prime_add_or_sub_of_prime_dvd_aut_of_scn3_empty
      (R := R) (p := p) (q := q) hp_odd hR hSCN hq hq_ne_p hq_dvd_aut
  rw [hp_eq_three] at hhalf
  norm_num at hhalf
  rcases hhalf with hq_dvd_two | hq_dvd_one
  · have hq_eq_two : q = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hq_dvd_two with hq_one | hq_two
      · exact absurd hq_one hq.one_lt.ne'
      · exact hq_two
    exact hq_ne_two hq_eq_two
  · exact hq.ne_one hq_dvd_one

/-- Blackburn 4.16, Case A. If `|Ω₁(R)| ≤ p²`, Proposition 4.11 makes `R`
metacyclic, and Huppert's operator theorem 4.12(a) then makes `R` abelian from
`[R,A]=R`. -/
theorem isMulCommutative_of_omega1_card_le_prime_sq_blackburn
    {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime] (hp_odd : Odd p) (hR : IsPGroup p R) (hp3 : 3 < p)
    {A : Type*} [Group A] [Finite A] {φ : A →* MulAut R}
    (hcop : Nat.Coprime (Nat.card A) (Nat.card R))
    (hΩ : Nat.card (Omega R p 1) ≤ p ^ 2)
    (hRA : OddOrder.Isaacs.Ch04.actionCommutator φ = ⊤) :
    IsMulCommutative R := by
  have hmeta : OddOrder.GroupTheory.IsMetacyclic R :=
    isMetacyclic_of_omega1_card_le_prime_sq hR hp3 hΩ
  exact OddOrder.BG.Ch1.S04b.isMulCommutative_of_metacyclic_actionCommutator_eq_top
    hp_odd hR hmeta hcop hRA

/-- Blackburn 4.16, start of Case B. If `p > 3`, `pRank R p ≤ 2`, and
`|Ω₁(R)| > p²`, then `Ω₁(R)` has exponent dividing `p` and exact order `p³`.
This is the Prop. 4.8 input used before setting `S = Ω₁(R)` in the printed proof. -/
theorem omega1_large_card_eq_prime_cube_and_pow_eq_one
    {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime] (hR : IsPGroup p R) (hp3 : 3 < p)
    (hrank : pRank R p ≤ 2)
    (hΩ_large : ¬ Nat.card (Omega R p 1) ≤ p ^ 2) :
    Nat.card (Omega R p 1) = p ^ 3 ∧ ∀ x : Omega R p 1, x ^ p = 1 := by
  have hp : p.Prime := Fact.out
  have hΩ_pow : ∀ x : Omega R p 1, x ^ p = 1 := by
    intro x
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact omega1_pow_eq_one_of_pRank_le_two_of_three_lt hR hp3 hrank x.2
  have hΩ_pg : IsPGroup p (Omega R p 1) := hR.to_subgroup _
  have hΩ_rank : pRank (Omega R p 1) p ≤ 2 :=
    (pRank_mono_of_le (Omega R p 1)).trans hrank
  have hΩ_le_cube : Nat.card (Omega R p 1) ≤ p ^ 3 :=
    card_le_prime_cube_of_pRank_le_two_of_exponent_prime hΩ_pg hΩ_rank hΩ_pow
  have hΩ_gt_sq : p ^ 2 < Nat.card (Omega R p 1) := lt_of_not_ge hΩ_large
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hΩ_pg
  have hcard : Nat.card (Omega R p 1) = p ^ 3 := by
    rw [hn] at hΩ_le_cube hΩ_gt_sq ⊢
    have h2 : 2 < n := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hΩ_gt_sq
    have h3 : n ≤ 3 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hΩ_le_cube
    have hn3 : n = 3 := by omega
    rw [hn3]
  exact ⟨hcard, hΩ_pow⟩

/-- If a finite group has order `p³` and all elements have `p`-th power one, its
exponent is exactly `p`. -/
theorem exponent_eq_prime_of_card_prime_cube_and_pow_eq_one
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hcard : Nat.card G = p ^ 3) (hpow : ∀ x : G, x ^ p = 1) :
    Monoid.exponent G = p := by
  have hp : p.Prime := Fact.out
  have hcard_gt_one : 1 < Nat.card G := by
    rw [hcard]
    exact one_lt_pow₀ hp.one_lt (by norm_num : 3 ≠ 0)
  have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp hcard_gt_one
  rw [Monoid.exponent_eq_prime_iff hp]
  intro g hg
  exact orderOf_eq_prime (hpow g) hg

/-- In Blackburn 4.16 Case B, `S = Ω₁(R)` cannot be abelian: otherwise it would
be elementary abelian of order `p³`, contradicting `pRank R p ≤ 2`. -/
theorem omega1_large_not_isMulCommutative
    {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime]
    (hrank : pRank R p ≤ 2)
    (hΩ_card : Nat.card (Omega R p 1) = p ^ 3)
    (hΩ_pow : ∀ x : Omega R p 1, x ^ p = 1) :
    ¬ IsMulCommutative (Omega R p 1) := by
  intro hcomm
  have hp : p.Prime := Fact.out
  have hΩ_ea : IsElementaryAbelian p (Omega R p 1) :=
    ⟨isMulCommutative_iff.mp hcomm, hΩ_pow⟩
  have hΩ_rank : pRank (Omega R p 1) p ≤ 2 :=
    (pRank_mono_of_le (Omega R p 1)).trans hrank
  have hlog_le : Nat.log p (Nat.card (Omega R p 1)) ≤ 2 :=
    hΩ_ea.log_card_le_pRank.trans hΩ_rank
  have hlog_eq : Nat.log p (Nat.card (Omega R p 1)) = 3 := by
    rw [hΩ_card, Nat.log_pow hp.one_lt]
  omega

/-- The image of `Ω₁(H)` in an ambient group lies in `Ω₁(R)`. -/
private theorem omega1_subgroup_map_le_omega1
    {R : Type*} [Group R] {p : ℕ} (H : Subgroup R) :
    (Omega H p 1).map H.subtype ≤ Omega R p 1 := by
  rw [Subgroup.map_le_iff_le_comap, Omega, Subgroup.closure_le]
  intro g hg
  change (g : R) ∈ Omega R p 1
  refine Omega.mem_of_pow_eq_one ?_
  rw [pow_one]
  have hgp : (g : H) ^ p = 1 := by simpa [pow_one] using hg
  exact congrArg Subtype.val hgp

/-- For `S = Ω₁(R)` and `C = C_R(S)`, the image of `Ω₁(C)` lies in the ambient
image of `Z(S)`. This is the formal `Ω₁(C) ≤ S ∩ C ≤ Z(S)` step in BG 4.16. -/
private theorem omega1_centralizer_omega1_map_le_center_map
    {R : Type*} [Group R] {p : ℕ} :
    let S : Subgroup R := Omega R p 1
    let C : Subgroup R := Subgroup.centralizer (S : Set R)
    (Omega C p 1).map C.subtype ≤ (Subgroup.center S).map S.subtype := by
  dsimp
  intro x hx
  have hxS : x ∈ Omega R p 1 :=
    omega1_subgroup_map_le_omega1
      (Subgroup.centralizer ((Omega R p 1 : Subgroup R) : Set R)) hx
  have hxC : x ∈ Subgroup.centralizer ((Omega R p 1 : Subgroup R) : Set R) := by
    rcases hx with ⟨c, _hc, rfl⟩
    exact c.2
  refine ⟨⟨x, hxS⟩, ?_, rfl⟩
  change ⟨x, hxS⟩ ∈ Subgroup.center (Omega R p 1)
  rw [Subgroup.mem_center_iff]
  intro y
  apply (Omega R p 1).subtype_injective
  simpa using hxC (y : R) y.2

/-- The ambient image of `Z(Ω₁(R))` lies in the image of `Ω₁(C_R(Ω₁(R)))` when
`Ω₁(R)` has exponent `p`. -/
private theorem center_map_le_omega1_centralizer_omega1_map
    {R : Type*} [Group R] {p : ℕ}
    (hΩ_pow : ∀ x : Omega R p 1, x ^ p = 1) :
    let S : Subgroup R := Omega R p 1
    let C : Subgroup R := Subgroup.centralizer (S : Set R)
    (Subgroup.center S).map S.subtype ≤ (Omega C p 1).map C.subtype := by
  dsimp
  rintro x ⟨z, hz, rfl⟩
  have hzC : (z : R) ∈ Subgroup.centralizer ((Omega R p 1 : Subgroup R) : Set R) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hz_center : z ∈ Subgroup.center (Omega R p 1) := hz
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz_center) ⟨y, hy⟩)
  have hz_pow : (⟨(z : R), hzC⟩ :
      Subgroup.centralizer ((Omega R p 1 : Subgroup R) : Set R)) ^ p = 1 := by
    apply Subtype.ext
    change ((z : R) ^ p) = 1
    exact congrArg Subtype.val (hΩ_pow z)
  have hz_omega : (⟨(z : R), hzC⟩ :
      Subgroup.centralizer ((Omega R p 1 : Subgroup R) : Set R)) ∈
      Omega (Subgroup.centralizer ((Omega R p 1 : Subgroup R) : Set R)) p 1 := by
    refine Omega.mem_of_pow_eq_one ?_
    rw [pow_one]
    exact hz_pow
  exact ⟨⟨(z : R), hzC⟩, hz_omega, rfl⟩

/-- Blackburn 4.16 centralizer core: for `S = Ω₁(R)` and `C = C_R(S)`,
`Ω₁(C)` is the ambient copy of `Z(S)`; in the extraspecial case this is `S'`,
and `C` is cyclic. -/
theorem blackburn_omega1_centralizer_eq_center_cyclic_and_commutator
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hp_odd : Odd p) (hR : IsPGroup p R)
    (hΩ_pow : ∀ x : Omega R p 1, x ^ p = 1)
    (hΩ_extraspecial : IsExtraspecial p (Omega R p 1)) :
    let S : Subgroup R := Omega R p 1
    let C : Subgroup R := Subgroup.centralizer (S : Set R)
    (Omega C p 1).map C.subtype = (Subgroup.center S).map S.subtype ∧
      IsCyclic C ∧
      (Omega C p 1).map C.subtype = (_root_.commutator S).map S.subtype := by
  dsimp
  let S : Subgroup R := Omega R p 1
  let C : Subgroup R := Subgroup.centralizer (S : Set R)
  have hΩC_eq_center :
      (Omega C p 1).map C.subtype = (Subgroup.center S).map S.subtype := by
    change (Omega (Subgroup.centralizer ((Omega R p 1 : Subgroup R) : Set R)) p 1).map
        (Subgroup.centralizer ((Omega R p 1 : Subgroup R) : Set R)).subtype =
      (Subgroup.center (Omega R p 1)).map (Omega R p 1).subtype
    exact le_antisymm
      (omega1_centralizer_omega1_map_le_center_map (R := R) (p := p))
      (center_map_le_omega1_centralizer_omega1_map (R := R) (p := p) hΩ_pow)
  have hΩC_card_le_p : Nat.card (Omega C p 1) ≤ p := by
    have hmap_card : Nat.card ((Omega C p 1).map C.subtype) = Nat.card (Omega C p 1) := by
      rw [Subgroup.card_map_of_injective C.subtype_injective]
    rw [← hmap_card, hΩC_eq_center,
      Subgroup.card_map_of_injective S.subtype_injective, hΩ_extraspecial.center_card]
  have hC_pg : IsPGroup p C := hR.to_subgroup C
  have hC_cyclic : IsCyclic C :=
    isCyclic_of_card_omega1_le_prime hC_pg hp_odd hΩC_card_le_p
  have hΩC_eq_comm :
      (Omega C p 1).map C.subtype = (_root_.commutator S).map S.subtype := by
    rw [hΩC_eq_center, hΩ_extraspecial.commutator_eq_center]
  exact ⟨hΩC_eq_center, hC_cyclic, hΩC_eq_comm⟩

/-- A nonabelian finite group of order `p³` has center of order `p`. -/
theorem center_card_eq_prime_of_noncomm_card_prime_cube
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hcard : Nat.card G = p ^ 3) (hnoncomm : ¬ IsMulCommutative G) :
    Nat.card (Subgroup.center G) = p := by
  have hp : p.Prime := Fact.out
  obtain ⟨k, hk_pos, hk⟩ :=
    IsPGroup.card_center_eq_prime_pow (G := G) (p := p) (n := 3) hcard (by norm_num)
  have hk_le_three : k ≤ 3 := by
    have hle : p ^ k ≤ p ^ 3 := by
      rw [← hk, ← hcard]
      simpa [Subgroup.card_top] using
        (Subgroup.card_le_of_le (le_top : Subgroup.center G ≤ (⊤ : Subgroup G)))
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
  have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk_cases with hk1 | hk2 | hk3
  · simpa [hk1] using hk
  · exfalso
    have hlag : Nat.card G =
        Nat.card (G ⧸ Subgroup.center G) * Nat.card (Subgroup.center G) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)
    have hquot_card : Nat.card (G ⧸ Subgroup.center G) = p := by
      have hmul : Nat.card (G ⧸ Subgroup.center G) * (p ^ 2) = p * (p ^ 2) := by
        calc
          Nat.card (G ⧸ Subgroup.center G) * (p ^ 2)
              = Nat.card (G ⧸ Subgroup.center G) * Nat.card (Subgroup.center G) := by
                rw [hk, hk2]
          _ = Nat.card G := hlag.symm
          _ = p ^ 3 := hcard
          _ = p * (p ^ 2) := by ring
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 2) hmul
    have hcyc : IsCyclic (G ⧸ Subgroup.center G) := isCyclic_of_prime_card hquot_card
    have := hcyc
    have hcomm : ∀ x y : G, x * y = y * x :=
      (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
        (QuotientGroup.mk' (Subgroup.center G))
        (le_of_eq (QuotientGroup.ker_mk' (Subgroup.center G)))).is_comm.comm
    exact hnoncomm (IsMulCommutative.of_comm hcomm)
  · exfalso
    have hcenter_card_top : Nat.card (Subgroup.center G) = Nat.card G := by
      rw [hk, hk3, hcard]
    have hcenter_top : Subgroup.center G = ⊤ :=
      Subgroup.eq_top_of_card_eq (H := Subgroup.center G) hcenter_card_top
    have hcomm : ∀ x y : G, x * y = y * x := by
      intro x y
      have hx : x ∈ Subgroup.center G := by rw [hcenter_top]; exact Subgroup.mem_top x
      exact (Subgroup.mem_center_iff.mp hx y).symm
    exact hnoncomm (IsMulCommutative.of_comm hcomm)

/-- A nonabelian group of order `p³` and exponent `p` is extraspecial.

This packages the standard rank-two Blackburn Case B structure: the quotient by the
center has order `p²`, hence is abelian, so the commutator subgroup is nontrivial and
lies in the center of order `p`; exponent `p` then collapses the p-power part in
BG Lemma 1.7(d), giving `Φ(G)=G'=Z(G)`. -/
theorem isExtraspecial_of_noncomm_card_prime_cube_exp_prime
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hcard : Nat.card G = p ^ 3)
    (hnoncomm : ¬ IsMulCommutative G)
    (hexp : Monoid.exponent G = p) :
    IsExtraspecial p G := by
  have hp : p.Prime := Fact.out
  have hG : IsPGroup p G := IsPGroup.of_card (n := 3) hcard
  have hcenter_card : Nat.card (Subgroup.center G) = p :=
    center_card_eq_prime_of_noncomm_card_prime_cube hcard hnoncomm
  have hlag : Nat.card G =
      Nat.card (G ⧸ Subgroup.center G) * Nat.card (Subgroup.center G) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)
  have hquot_center_card : Nat.card (G ⧸ Subgroup.center G) = p ^ 2 := by
    have hmul : Nat.card (G ⧸ Subgroup.center G) * p = (p ^ 2) * p := by
      calc
        Nat.card (G ⧸ Subgroup.center G) * p
            = Nat.card (G ⧸ Subgroup.center G) * Nat.card (Subgroup.center G) := by
              rw [hcenter_card]
        _ = Nat.card G := hlag.symm
        _ = p ^ 3 := hcard
        _ = (p ^ 2) * p := by ring
    exact Nat.eq_of_mul_eq_mul_right hp.pos hmul
  have hquot_comm : ∀ x y : G ⧸ Subgroup.center G, x * y = y * x :=
    isMulCommutative_iff.mp
      (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hquot_center_card)
  have hcomm_le_center : _root_.commutator G ≤ Subgroup.center G :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le
      (N := Subgroup.center G)).mp ⟨⟨hquot_comm⟩⟩
  have hcomm_ne_bot : _root_.commutator G ≠ (⊥ : Subgroup G) := by
    intro hbot
    exact hnoncomm ((commutator_eq_bot_iff G).mp hbot)
  have hcomm_pg : IsPGroup p (_root_.commutator G) := hG.to_subgroup _
  have hcomm_card_ne_one : Nat.card (_root_.commutator G) ≠ 1 := by
    intro hcard_one
    exact hcomm_ne_bot (Subgroup.card_eq_one.mp hcard_one)
  have hcomm_card_le_p : Nat.card (_root_.commutator G) ≤ p := by
    rw [← hcenter_card]
    exact Subgroup.card_le_of_le hcomm_le_center
  have hp_dvd_comm : p ∣ Nat.card (_root_.commutator G) := by
    rcases hcomm_pg.card_eq_or_dvd with h1 | hdvd
    · exact False.elim (hcomm_card_ne_one h1)
    · exact hdvd
  have hp_le_comm : p ≤ Nat.card (_root_.commutator G) :=
    Nat.le_of_dvd Nat.card_pos hp_dvd_comm
  have hcomm_card : Nat.card (_root_.commutator G) = p :=
    le_antisymm hcomm_card_le_p hp_le_comm
  have hcomm_eq_center : _root_.commutator G = Subgroup.center G :=
    Subgroup.eq_of_le_of_card_ge hcomm_le_center (by rw [hcomm_card, hcenter_card])
  have hpow_closure_bot :
      Subgroup.closure (Set.range (fun x : G => x ^ p)) = (⊥ : Subgroup G) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro y ⟨x, rfl⟩
      change x ^ p = 1
      simpa [hexp] using (Monoid.pow_exponent_eq_one x)
    · exact bot_le
  have hcomm_eq_frattini :
      _root_.commutator G = frattini G := by
    simpa [hpow_closure_bot] using
      (OddOrder.BG.Ch1.S01.commutator_sup_pow_closure_eq_frattini hG)
  have hfrat_eq_center : frattini G = Subgroup.center G := by
    rw [← hcomm_eq_center]
    exact hcomm_eq_frattini.symm
  exact ⟨hG, hcomm_eq_center, hfrat_eq_center, hcenter_card⟩

/-- Blackburn 4.16 Case B-1: if `R` centralizes `S/S'` for `S = Ω₁(R)`, then
`R = S ∘ C_R(S)` gives the central-product conclusion. -/
theorem blackburnCentralProductCase_of_omega1_commutator_le_center
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hp_odd : Odd p) (hR : IsPGroup p R)
    (hΩ_card : Nat.card (Omega R p 1) = p ^ 3)
    (hΩ_pow : ∀ x : Omega R p 1, x ^ p = 1)
    (hΩ_noncomm : ¬ IsMulCommutative (Omega R p 1))
    (hΩ_exp : Monoid.exponent (Omega R p 1) = p)
    (hΩ_extraspecial : IsExtraspecial p (Omega R p 1))
    (hSR : ⁅(Omega R p 1 : Subgroup R), (⊤ : Subgroup R)⁆ ≤
      (Subgroup.center (Omega R p 1)).map (Omega R p 1).subtype) :
    BlackburnCentralProductCase p R := by
  let S : Subgroup R := Omega R p 1
  let C : Subgroup R := Subgroup.centralizer (S : Set R)
  obtain ⟨_hΩC_eq_center, hC_cyclic, hΩC_eq_comm⟩ :=
    blackburn_omega1_centralizer_eq_center_cyclic_and_commutator
      hp_odd hR hΩ_pow hΩ_extraspecial
  have hsup : S ⊔ C = ⊤ := by
    change (Omega R p 1 : Subgroup R) ⊔
        Subgroup.centralizer (((Omega R p 1 : Subgroup R)) : Set R) = ⊤
    exact mul_centralizer_eq_top_of_isExtraspecial (S := (Omega R p 1 : Subgroup R))
      hΩ_extraspecial hSR
  have hS_le_centC : S ≤ Subgroup.centralizer (C : Set R) :=
    Subgroup.le_centralizer_iff.mp
      (le_rfl : C ≤ Subgroup.centralizer (S : Set R))
  have hcentral : IsCentralProduct (⊤ : Subgroup R) S C :=
    IsCentralProduct.of_le_centralizer hsup.symm hS_le_centC
  exact ⟨S, C, hcentral, hΩ_noncomm, hΩ_card, hΩ_exp, hC_cyclic, hΩC_eq_comm⟩

/-- A strict subgroup inclusion in a finite ambient group gives a strict cardinality
inequality. -/
private theorem subgroup_card_lt_of_lt
    {G : Type*} [Group G] [Finite G] {H K : Subgroup G} (h : H < K) :
    Nat.card H < Nat.card K := by
  have hle : Nat.card H ≤ Nat.card K := Subgroup.card_le_of_le h.le
  exact lt_of_le_of_ne hle (by
    intro hcard
    have heq : H = K := Subgroup.eq_of_le_of_card_ge h.le (by rw [hcard])
    exact h.ne heq)

/-- A finite `p`-group whose order is strictly between `p` and `p³` has order `p²`. -/
private theorem card_eq_prime_sq_of_pgroup_card_gt_prime_lt_cube
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) (hp_lt : p < Nat.card G) (hlt_cube : Nat.card G < p ^ 3) :
    Nat.card G = p ^ 2 := by
  have hp : p.Prime := Fact.out
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hG
  have h1n : 1 < n := by
    have hpow : p ^ 1 < p ^ n := by simpa [hn] using hp_lt
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp hpow
  have hn3 : n < 3 := by
    rw [hn] at hlt_cube
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt_cube
  have hn2 : n = 2 := by omega
  rw [hn, hn2]

/-- Blackburn 4.16 Case B-2 setup: if `R` does not centralize `S/S'` for
`S = Ω₁(R)`, then `T = [S,R]` satisfies `Z(S) < T < S` and `|T| = p²`. -/
theorem blackburn_noncentral_commutator_facts
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hR : IsPGroup p R)
    (hΩ_card : Nat.card (Omega R p 1) = p ^ 3)
    (hΩ_extraspecial : IsExtraspecial p (Omega R p 1))
    (hnot : ¬ ⁅(Omega R p 1 : Subgroup R), (⊤ : Subgroup R)⁆ ≤
      (Subgroup.center (Omega R p 1)).map (Omega R p 1).subtype) :
    let S : Subgroup R := Omega R p 1
    let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
    (Subgroup.center S).map S.subtype < T ∧ T < S ∧ Nat.card T = p ^ 2 := by
  dsimp
  let S : Subgroup R := Omega R p 1
  let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
  have : Group.IsNilpotent R := hR.isNilpotent
  have : S.Normal := by dsimp [S]; infer_instance
  have hS_card_gt_one : 1 < Nat.card S := by
    dsimp [S]
    rw [hΩ_card]
    exact one_lt_pow₀ (Fact.out (p := p.Prime)).one_lt (by norm_num : 3 ≠ 0)
  have hS_ne_bot : S ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot S).mp hS_card_gt_one
  have hT_lt_S : T < S := by
    dsimp [T]
    exact OddOrder.Isaacs.Ch04.commutator_lt_self_of_isNilpotent_ambient
      (E := S) (F := (⊤ : Subgroup R)) hS_ne_bot
  have hcenter_eq_comm_map :
      (Subgroup.center S).map S.subtype = ⁅S, S⁆ := by
    dsimp [S]
    rw [← hΩ_extraspecial.commutator_eq_center, Subgroup.map_subtype_commutator]
  have hcenter_le_T : (Subgroup.center S).map S.subtype ≤ T := by
    dsimp [T]
    rw [hcenter_eq_comm_map]
    exact Subgroup.commutator_mono le_rfl le_top
  have hcenter_lt_T : (Subgroup.center S).map S.subtype < T := by
    refine lt_of_le_of_ne hcenter_le_T ?_
    intro heq
    apply hnot
    dsimp [S, T] at heq ⊢
    exact le_of_eq heq.symm
  have hcenter_map_card : Nat.card ((Subgroup.center S).map S.subtype) = p := by
    rw [Subgroup.card_map_of_injective S.subtype_injective, hΩ_extraspecial.center_card]
  have hp_lt_T : p < Nat.card T := by
    have hlt : Nat.card ((Subgroup.center S).map S.subtype) < Nat.card T :=
      subgroup_card_lt_of_lt hcenter_lt_T
    rw [hcenter_map_card] at hlt
    exact hlt
  have hT_card_lt_cube : Nat.card T < p ^ 3 := by
    have hlt := subgroup_card_lt_of_lt hT_lt_S
    dsimp [S] at hlt
    simpa [hΩ_card] using hlt
  have hT_pg : IsPGroup p T := hR.to_subgroup T
  exact ⟨hcenter_lt_T, hT_lt_S,
    card_eq_prime_sq_of_pgroup_card_gt_prime_lt_cube hT_pg hp_lt_T hT_card_lt_cube⟩

/-- In Blackburn 4.16 Case B-2, `T = [S,R]` is elementary abelian once
`Z(S) < T < S = Ω₁(R)` and `|T| = p²` are known. -/
theorem blackburn_noncentral_commutator_isElementaryAbelian
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hΩ_pow : ∀ x : Omega R p 1, x ^ p = 1)
    (hT_facts :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      (Subgroup.center S).map S.subtype < T ∧ T < S ∧ Nat.card T = p ^ 2) :
    let S : Subgroup R := Omega R p 1
    let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
    T.IsElementaryAbelian p := by
  dsimp at hT_facts ⊢
  let S : Subgroup R := Omega R p 1
  let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
  have hT_le_S : T ≤ S := hT_facts.2.1.le
  have hT_comm : ∀ x y : T, x * y = y * x :=
    isMulCommutative_iff.mp
      (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hT_facts.2.2)
  refine ⟨hT_comm, ?_⟩
  intro x
  have hxpow : (⟨(x : R), hT_le_S x.2⟩ : S) ^ p = 1 :=
    hΩ_pow ⟨(x : R), hT_le_S x.2⟩
  ext
  change (x : R) ^ p = 1
  exact congrArg Subtype.val hxpow

/-- The kernel of conjugation on a normal subgroup is its ambient centralizer. -/
private theorem conjNormal_ker_eq_centralizer_for_subgroup
    {G : Type*} [Group G] {V : Subgroup G} [V.Normal] :
    (MulAut.conjNormal (H := V)).ker = Subgroup.centralizer (V : Set G) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro hg v hv
    have hfix : (MulAut.conjNormal g (⟨v, hv⟩ : V) : G) = ((⟨v, hv⟩ : V) : G) := by
      rw [hg]
      rfl
    rw [MulAut.conjNormal_apply] at hfix
    have hcomm : g * v = v * g := by
      have : g * v * g⁻¹ * g = v * g := by rw [hfix]
      simpa [mul_assoc] using this
    exact hcomm.symm
  · intro hg
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    simp only [MulAut.one_apply]
    rw [MulAut.conjNormal_apply]
    have hcomm : (v : G) * g = g * (v : G) := hg (v : G) v.property
    rw [← hcomm]
    group

/-- Blackburn 4.16 Case B-2: `C = C_R(S)` and `D = C_R(T)` are normal,
and so `C.subgroupOf D` is normal inside `D`. -/
theorem blackburn_noncentral_centralizer_normalities
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime] :
    let S : Subgroup R := Omega R p 1
    let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
    let C : Subgroup R := Subgroup.centralizer (S : Set R)
    let D : Subgroup R := Subgroup.centralizer (T : Set R)
    C.Normal ∧ D.Normal ∧ (C.subgroupOf D).Normal := by
  dsimp
  let S : Subgroup R := Omega R p 1
  let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
  let C : Subgroup R := Subgroup.centralizer (S : Set R)
  let D : Subgroup R := Subgroup.centralizer (T : Set R)
  have hS_normal : S.Normal := by dsimp [S]; infer_instance
  have hT_normal : T.Normal := by
    dsimp [T]
    exact Subgroup.commutator_normal S (⊤ : Subgroup R)
  have hC_normal : C.Normal := by
    dsimp [C]
    infer_instance
  have hD_normal : D.Normal := by
    dsimp [D]
    infer_instance
  exact ⟨hC_normal, hD_normal, hC_normal.subgroupOf D⟩

/-- Blackburn 4.16 Case B-2: the subgroups `S = Omega R p 1`, `T = [S,R]`,
`C = C_R(S)`, and `D = C_R(T)` are invariant under every operator action on `R`. -/
theorem blackburn_noncentral_operator_invariances
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    {A : Type*} [Group A] {φ : A →* MulAut R} :
    let S : Subgroup R := Omega R p 1
    let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
    let C : Subgroup R := Subgroup.centralizer (S : Set R)
    let D : Subgroup R := Subgroup.centralizer (T : Set R)
    IsAInvariant φ S ∧ IsAInvariant φ T ∧ IsAInvariant φ C ∧ IsAInvariant φ D := by
  dsimp
  let S : Subgroup R := Omega R p 1
  let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
  let C : Subgroup R := Subgroup.centralizer (S : Set R)
  let D : Subgroup R := Subgroup.centralizer (T : Set R)
  have hS_inv : IsAInvariant φ S := IsAInvariant.of_characteristic φ
  have hT_inv : IsAInvariant φ T := hS_inv.commutator (IsAInvariant.top φ)
  have hC_inv : IsAInvariant φ C := hS_inv.centralizer
  have hD_inv : IsAInvariant φ D := hT_inv.centralizer
  exact ⟨hS_inv, hT_inv, hC_inv, hD_inv⟩

/-- Blackburn 4.16 Case B-2: the conjugation quotient on
`T = [Ω₁(R),R]` has order at most `p`.  The image is a `p`-subgroup of
`Aut(T)`, and `T` is elementary abelian of order `p²`, so the GL squeeze applies. -/
private theorem blackburn_noncentral_centralizer_quotient_card_le_prime
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hR : IsPGroup p R)
    (hT_facts :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      (Subgroup.center S).map S.subtype < T ∧ T < S ∧ Nat.card T = p ^ 2)
    (hT_elem :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      T.IsElementaryAbelian p) :
    let S : Subgroup R := Omega R p 1
    let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
    Nat.card (R ⧸ Subgroup.centralizer (T : Set R)) ≤ p := by
  dsimp at hT_facts hT_elem ⊢
  let S : Subgroup R := Omega R p 1
  let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
  have hT_card_le : Nat.card T ≤ p ^ 2 := le_of_eq hT_facts.2.2
  have hS_normal : S.Normal := by dsimp [S]; infer_instance
  have hT_normal : T.Normal := by
    dsimp [T]
    exact Subgroup.commutator_normal S (⊤ : Subgroup R)
  let φ : R →* MulAut T := MulAut.conjNormal (H := T)
  have hker : φ.ker = Subgroup.centralizer (T : Set R) := by
    simpa [φ] using conjNormal_ker_eq_centralizer_for_subgroup (G := R) (V := T)
  have hquot_range : Nat.card (R ⧸ Subgroup.centralizer (T : Set R)) = Nat.card φ.range := by
    rw [← hker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hrange_pg : IsPGroup p φ.range :=
    hR.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hrange_le : Nat.card φ.range ≤ p :=
    card_pSubgroup_mulAut_le_prime_of_card_le_prime_sq hT_elem hT_card_le hrange_pg
  change Nat.card (R ⧸ Subgroup.centralizer (T : Set R)) ≤ p
  rw [hquot_range]
  exact hrange_le

/-- Blackburn 4.16 Case B-2: `C_R(T)` is proper when
`Z(S) < T = [Ω₁(R),R]`.  If every element of `S` centralized `T`, then each
`z ∈ T` would be central in `S`, contradicting `Z(S) < T`. -/
private theorem blackburn_noncentral_centralizer_ne_top
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hT_facts :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      (Subgroup.center S).map S.subtype < T ∧ T < S ∧ Nat.card T = p ^ 2) :
    let S : Subgroup R := Omega R p 1
    let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
    Subgroup.centralizer (T : Set R) ≠ ⊤ := by
  dsimp at hT_facts ⊢
  let S : Subgroup R := Omega R p 1
  let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
  let Z : Subgroup R := (Subgroup.center S).map S.subtype
  obtain ⟨z, hzT, hzZ⟩ := SetLike.exists_of_lt hT_facts.1
  have hzS : z ∈ S := hT_facts.2.1.le hzT
  intro hC_top
  have hz_center : (⟨z, hzS⟩ : S) ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply S.subtype_injective
    have hsC : (s : R) ∈ Subgroup.centralizer (T : Set R) := by
      rw [hC_top]
      exact Subgroup.mem_top (s : R)
    exact (hsC z hzT).symm
  exact hzZ ⟨⟨z, hzS⟩, hz_center, rfl⟩

/-- Blackburn 4.16 Case B-2, equation (4.12), cardinal part:
`|R/C_R(T)| = p` for `T = [Ω₁(R),R]` in the noncentral commutator branch. -/
theorem blackburn_noncentral_centralizer_quotient_card_eq_prime
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hR : IsPGroup p R)
    (hT_facts :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      (Subgroup.center S).map S.subtype < T ∧ T < S ∧ Nat.card T = p ^ 2)
    (hT_elem :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      T.IsElementaryAbelian p) :
    let S : Subgroup R := Omega R p 1
    let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
    Nat.card (R ⧸ Subgroup.centralizer (T : Set R)) = p := by
  dsimp at hT_facts hT_elem ⊢
  let S : Subgroup R := Omega R p 1
  let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
  let C : Subgroup R := Subgroup.centralizer (T : Set R)
  have hS_normal : S.Normal := by dsimp [S]; infer_instance
  have hT_normal : T.Normal := by
    dsimp [T]
    exact Subgroup.commutator_normal S (⊤ : Subgroup R)
  have hC_ne_top : C ≠ ⊤ := by
    dsimp [C]
    exact blackburn_noncentral_centralizer_ne_top (R := R) (p := p) hT_facts
  have hquot_nontrivial : Nontrivial (R ⧸ C) :=
    Subgroup.nontrivial_quotient_of_ne_top hC_ne_top
  have hquot_gt_one : 1 < Nat.card (R ⧸ C) :=
    Finite.one_lt_card_iff_nontrivial.mpr hquot_nontrivial
  have hquot_pg : IsPGroup p (R ⧸ C) := hR.to_quotient C
  have hquot_le : Nat.card (R ⧸ C) ≤ p := by
    dsimp [C]
    exact blackburn_noncentral_centralizer_quotient_card_le_prime hR hT_facts hT_elem
  rcases hquot_pg.card_eq_or_dvd with hquot_one | hp_dvd
  · exact False.elim ((ne_of_gt hquot_gt_one) hquot_one)
  · exact le_antisymm hquot_le
      (Nat.le_of_dvd (Nat.lt_trans Nat.zero_lt_one hquot_gt_one) hp_dvd)

/-- Blackburn 4.16 Case B-2: `S = Ω₁(R)` is not contained in `C_R(T)` when
`Z(S) < T = [S,R]`. -/
theorem blackburn_noncentral_omega1_not_le_centralizer
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hT_facts :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      (Subgroup.center S).map S.subtype < T ∧ T < S ∧ Nat.card T = p ^ 2) :
    let S : Subgroup R := Omega R p 1
    let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
    ¬ S ≤ Subgroup.centralizer (T : Set R) := by
  dsimp at hT_facts ⊢
  let S : Subgroup R := Omega R p 1
  let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
  let Z : Subgroup R := (Subgroup.center S).map S.subtype
  obtain ⟨z, hzT, hzZ⟩ := SetLike.exists_of_lt hT_facts.1
  have hzS : z ∈ S := hT_facts.2.1.le hzT
  intro hS_le_C
  have hz_center : (⟨z, hzS⟩ : S) ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply S.subtype_injective
    exact ((hS_le_C s.2) z hzT).symm
  exact hzZ ⟨⟨z, hzS⟩, hz_center, rfl⟩

/-- Blackburn 4.16 Case B-2, equation (4.12), product part:
`R = Ω₁(R) C_R(T)` for `T = [Ω₁(R),R]` in the noncentral commutator branch. -/
theorem blackburn_noncentral_omega1_sup_centralizer_eq_top
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hR : IsPGroup p R)
    (hT_facts :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      (Subgroup.center S).map S.subtype < T ∧ T < S ∧ Nat.card T = p ^ 2)
    (hT_elem :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      T.IsElementaryAbelian p) :
    let S : Subgroup R := Omega R p 1
    let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
    S ⊔ Subgroup.centralizer (T : Set R) = ⊤ := by
  dsimp at hT_facts hT_elem ⊢
  let S : Subgroup R := Omega R p 1
  let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
  let C : Subgroup R := Subgroup.centralizer (T : Set R)
  have hS_normal : S.Normal := by dsimp [S]; infer_instance
  have hT_normal : T.Normal := by
    dsimp [T]
    exact Subgroup.commutator_normal S (⊤ : Subgroup R)
  have hquot_card : Nat.card (R ⧸ C) = p := by
    dsimp [C]
    exact blackburn_noncentral_centralizer_quotient_card_eq_prime hR hT_facts hT_elem
  have hS_not_le_C : ¬ S ≤ C := by
    dsimp [C]
    exact blackburn_noncentral_omega1_not_le_centralizer (R := R) (p := p) hT_facts
  have hSmap_ne_bot : S.map (QuotientGroup.mk' C) ≠ ⊥ := by
    intro hbot
    apply hS_not_le_C
    intro s hsS
    have hsmap : (QuotientGroup.mk' C) s ∈ S.map (QuotientGroup.mk' C) :=
      Subgroup.mem_map.mpr ⟨s, hsS, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hsmap
    exact (QuotientGroup.eq_one_iff s).mp hsmap
  have hSmap_card_ne_one : Nat.card (S.map (QuotientGroup.mk' C)) ≠ 1 := by
    intro hcard
    exact hSmap_ne_bot (Subgroup.eq_bot_of_card_eq _ hcard)
  have hSmap_card_dvd : Nat.card (S.map (QuotientGroup.mk' C)) ∣ p := by
    rw [← hquot_card]
    exact Subgroup.card_subgroup_dvd_card (S.map (QuotientGroup.mk' C))
  have hSmap_card : Nat.card (S.map (QuotientGroup.mk' C)) = p := by
    rcases (Nat.dvd_prime (Fact.out : Nat.Prime p)).mp hSmap_card_dvd with hcard_one | hcard_p
    · exact False.elim (hSmap_card_ne_one hcard_one)
    · exact hcard_p
  have hSmap_top : S.map (QuotientGroup.mk' C) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq (H := S.map (QuotientGroup.mk' C))
    rw [hSmap_card, hquot_card]
  have hcomap : (S.map (QuotientGroup.mk' C)).comap (QuotientGroup.mk' C) = C ⊔ S :=
    QuotientGroup.comap_map_mk' C S
  have hCS_top : C ⊔ S = ⊤ := by
    rw [hSmap_top, Subgroup.comap_top] at hcomap
    exact hcomap.symm
  rw [sup_comm]
  exact hCS_top

/-- Blackburn 4.16 Case B-2 centralizer relations.  With
`S = Ω₁(R)`, `T = [S,R]`, `C = C_R(S)`, and `D = C_R(T)`, we have
`C ≤ D`, `T ≤ D`, and `T ∩ C = Z(S)` (embedded in `R`). -/
theorem blackburn_noncentral_centralizer_relations
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hT_facts :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      (Subgroup.center S).map S.subtype < T ∧ T < S ∧ Nat.card T = p ^ 2)
    (hT_elem :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      T.IsElementaryAbelian p) :
    let S : Subgroup R := Omega R p 1
    let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
    let C : Subgroup R := Subgroup.centralizer (S : Set R)
    let D : Subgroup R := Subgroup.centralizer (T : Set R)
    let Z : Subgroup R := (Subgroup.center S).map S.subtype
    C ≤ D ∧ T ≤ D ∧ T ⊓ C = Z := by
  dsimp at hT_facts hT_elem ⊢
  let S : Subgroup R := Omega R p 1
  let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
  let C : Subgroup R := Subgroup.centralizer (S : Set R)
  let D : Subgroup R := Subgroup.centralizer (T : Set R)
  let Z : Subgroup R := (Subgroup.center S).map S.subtype
  have hT_le_S : T ≤ S := hT_facts.2.1.le
  refine ⟨?_, ?_, ?_⟩
  · intro c hcC
    rw [Subgroup.mem_centralizer_iff] at hcC ⊢
    intro t htT
    exact hcC t (hT_le_S htT)
  · intro t htT
    rw [Subgroup.mem_centralizer_iff]
    intro u huT
    exact congrArg Subtype.val (hT_elem.1 ⟨u, huT⟩ ⟨t, htT⟩)
  · apply le_antisymm
    · intro x hx
      have hxS : x ∈ S := hT_le_S hx.1
      refine ⟨⟨x, hxS⟩, ?_, rfl⟩
      change ⟨x, hxS⟩ ∈ Subgroup.center S
      rw [Subgroup.mem_center_iff]
      intro s
      apply S.subtype_injective
      exact hx.2 (s : R) s.2
    · rintro x ⟨z, hz_center, rfl⟩
      constructor
      · exact hT_facts.1.le ⟨z, hz_center, rfl⟩
      · change (z : R) ∈ C
        rw [Subgroup.mem_centralizer_iff]
        intro s hsS
        exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz_center) ⟨s, hsS⟩)

/-- Blackburn 4.16 Case B-2: `D = C_R(T)` has order divisible by `p`, because
`T ≤ D` and `|T| = p²`. -/
theorem blackburn_noncentral_prime_dvd_centralizer_card
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hT_facts :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      (Subgroup.center S).map S.subtype < T ∧ T < S ∧ Nat.card T = p ^ 2)
    (hT_elem :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      T.IsElementaryAbelian p) :
    let S : Subgroup R := Omega R p 1
    let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
    let D : Subgroup R := Subgroup.centralizer (T : Set R)
    p ∣ Nat.card D := by
  dsimp at hT_facts hT_elem ⊢
  let S : Subgroup R := Omega R p 1
  let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
  let D : Subgroup R := Subgroup.centralizer (T : Set R)
  have hrelations := blackburn_noncentral_centralizer_relations hT_facts hT_elem
  have hT_dvd_D : Nat.card T ∣ Nat.card D := Subgroup.card_dvd_of_le hrelations.2.1
  have hp_dvd_T : p ∣ Nat.card T := by
    rw [hT_facts.2.2, pow_two]
    exact dvd_mul_right p p
  exact hp_dvd_T.trans hT_dvd_D

/-- Blackburn 4.16 Case B-2 support: if `T` is elementary abelian of exponent `p`,
then the image of `T.subgroupOf D` in any quotient `D/(C.subgroupOf D)` lies in `Ω₁`. -/
theorem subgroupOf_image_le_omega_quotient_of_isElementaryAbelian
    {R : Type*} [Group R] {p : ℕ} {C D T : Subgroup R}
    [(C.subgroupOf D).Normal] (hT_elem : T.IsElementaryAbelian p) :
    (T.subgroupOf D).map (QuotientGroup.mk' (C.subgroupOf D)) ≤
      Omega (D ⧸ C.subgroupOf D) p 1 := by
  rintro q ⟨d, hdT, rfl⟩
  refine Omega.mem_of_pow_eq_one ?_
  rw [pow_one, ← map_pow]
  have hd_pow_D : d ^ p = 1 := by
    apply Subtype.ext
    change (d : R) ^ p = 1
    exact congrArg Subtype.val
      (hT_elem.pow_eq_one ⟨(d : R), Subgroup.mem_subgroupOf.mp hdT⟩)
  rw [hd_pow_D, map_one]

/-- Blackburn 4.16 Case B-2: `D/C` is abelian for `D = C_R(T)` and
`C = C_R(S)`.  This is the subgroup form of BG's assertion that `C_R(T)/C`
embeds in the elementary abelian stabilizer group of the series `S ⊵ T ⊵ 1`:
commutators of elements centralizing `T` centralize all of `S`. -/
theorem blackburn_noncentral_centralizer_quotient_commutative
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hT_facts :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      (Subgroup.center S).map S.subtype < T ∧ T < S ∧ Nat.card T = p ^ 2)
    (hT_elem :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      T.IsElementaryAbelian p) :
    let S : Subgroup R := Omega R p 1
    let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
    let C : Subgroup R := Subgroup.centralizer (S : Set R)
    let D : Subgroup R := Subgroup.centralizer (T : Set R)
    let hCD_normal : (C.subgroupOf D).Normal :=
      (blackburn_noncentral_centralizer_normalities (R := R) (p := p)).2.2
    letI : (C.subgroupOf D).Normal := hCD_normal
    ∀ x y : D ⧸ C.subgroupOf D, x * y = y * x := by
  dsimp at hT_facts hT_elem ⊢
  let S : Subgroup R := Omega R p 1
  let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
  let C : Subgroup R := Subgroup.centralizer (S : Set R)
  let D : Subgroup R := Subgroup.centralizer (T : Set R)
  have hCD_norms := blackburn_noncentral_centralizer_normalities (R := R) (p := p)
  have hCD_normal : (C.subgroupOf D).Normal := hCD_norms.2.2
  have hT_le_S : T ≤ S := hT_facts.2.1.le
  have hS_normal : S.Normal := by dsimp [S]; infer_instance
  have hT_comm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s := by
    intro s hs t ht
    exact congrArg Subtype.val (hT_elem.1 ⟨s, hs⟩ ⟨t, ht⟩)
  have hdisp : ∀ d : D, ∀ s ∈ S, (d : R)⁻¹ * s * (d : R) * s⁻¹ ∈ T := by
    intro d s hs
    have hmem : ⁅(d : R)⁻¹, s⁆ ∈ (⁅(⊤ : Subgroup R), S⁆ : Subgroup R) :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) hs
    have hexpr : (d : R)⁻¹ * s * (d : R) * s⁻¹ = ⁅(d : R)⁻¹, s⁆ := by
      rw [commutatorElement_def]
      group
    rw [hexpr]
    rwa [Subgroup.commutator_comm] at hmem
  have hfix : ∀ d : D, ∀ w ∈ T, (d : R) * w = w * (d : R) := by
    intro d w hw
    exact (Subgroup.mem_centralizer_iff.mp d.property w hw).symm
  have hcomm_le : _root_.commutator D ≤ C.subgroupOf D := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro d₁ _ d₂ _
    rw [Subgroup.mem_subgroupOf]
    change ⁅(d₁ : R), (d₂ : R)⁆ ∈ C
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (commutator_centralizes_of_stabilize hT_le_S hT_comm
      (hdisp d₂) (hdisp d₁) (hfix d₂) (hfix d₁) s hs).symm
  exact isMulCommutative_iff.mp
    ((Subgroup.Normal.quotient_commutative_iff_commutator_le
      (N := C.subgroupOf D)).mpr hcomm_le)

/-- If conjugation by `d` moves `s` by an element `u` centralized by `d` and
`u ^ p = 1`, then `d ^ p` centralizes `s`.  This is the elementary collection
calculation used in Blackburn 4.16 to show `C_R(T)/C_R(S)` has exponent `p`. -/
private theorem pow_centralizes_of_displacement_order_p
    {G : Type*} [Group G] {d s u : G} {p : ℕ}
    (hconj : d⁻¹ * s * d = u * s)
    (hdu : d * u = u * d)
    (hup : u ^ p = 1) :
    s * d ^ p = d ^ p * s := by
  have hdu_pow : ∀ n : ℕ, d⁻¹ * u ^ n * d = u ^ n := by
    intro n
    have hcomm_du : Commute d u := hdu
    have hcomm_pow : d * u ^ n = u ^ n * d := hcomm_du.pow_right n |>.eq
    calc
      d⁻¹ * u ^ n * d = d⁻¹ * (u ^ n * d) := by group
      _ = d⁻¹ * (d * u ^ n) := by rw [← hcomm_pow]
      _ = u ^ n := by group
  have hiter : ∀ n : ℕ, (d⁻¹) ^ n * s * d ^ n = u ^ n * s := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          (d⁻¹) ^ (n + 1) * s * d ^ (n + 1)
              = d⁻¹ * ((d⁻¹) ^ n * s * d ^ n) * d := by group
          _ = d⁻¹ * (u ^ n * s) * d := by rw [ih]
          _ = (d⁻¹ * u ^ n * d) * (d⁻¹ * s * d) := by group
          _ = u ^ n * (u * s) := by rw [hdu_pow n, hconj]
          _ = u ^ (n + 1) * s := by rw [pow_succ]; group
  have hfixed : (d ^ p)⁻¹ * s * d ^ p = s := by
    have hpiter := hiter p
    simpa [← inv_pow, hup] using hpiter
  calc
    s * d ^ p = d ^ p * ((d ^ p)⁻¹ * s * d ^ p) := by group
    _ = d ^ p * s := by rw [hfixed]

/-- Blackburn 4.16 Case B-2: `D/C` has exponent `p`, stated as
`Ω₁(D/C) = ⊤`.  For `d ∈ D = C_R(T)` and `s ∈ S = Ω₁(R)`, the displacement
`d⁻¹ s d s⁻¹` lies in `T`; since `d` centralizes `T` and `T` has exponent `p`,
the collection lemma gives that `d ^ p` centralizes every element of `S`. -/
private theorem blackburn_noncentral_centralizer_quotient_omega_eq_top
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hT_facts :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      (Subgroup.center S).map S.subtype < T ∧ T < S ∧ Nat.card T = p ^ 2)
    (hT_elem :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      T.IsElementaryAbelian p) :
    let S : Subgroup R := Omega R p 1
    let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
    let C : Subgroup R := Subgroup.centralizer (S : Set R)
    let D : Subgroup R := Subgroup.centralizer (T : Set R)
    let hCD_normal : (C.subgroupOf D).Normal :=
      (blackburn_noncentral_centralizer_normalities (R := R) (p := p)).2.2
    letI : (C.subgroupOf D).Normal := hCD_normal
    Omega (D ⧸ C.subgroupOf D) p 1 = ⊤ := by
  dsimp at hT_facts hT_elem ⊢
  let S : Subgroup R := Omega R p 1
  let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
  let C : Subgroup R := Subgroup.centralizer (S : Set R)
  let D : Subgroup R := Subgroup.centralizer (T : Set R)
  have hCD_norms := blackburn_noncentral_centralizer_normalities (R := R) (p := p)
  have hCD_normal : (C.subgroupOf D).Normal := hCD_norms.2.2
  have hT_le_S : T ≤ S := hT_facts.2.1.le
  have hS_normal : S.Normal := by dsimp [S]; infer_instance
  apply eq_top_iff.mpr
  intro q _
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf D) q
  refine Omega.mem_of_pow_eq_one ?_
  rw [pow_one, ← map_pow]
  change QuotientGroup.mk' (C.subgroupOf D) (d ^ p) = 1
  have hd_pow_C : d ^ p ∈ C.subgroupOf D := by
    rw [Subgroup.mem_subgroupOf]
    change ((d : R) ^ p) ∈ C
    rw [Subgroup.mem_centralizer_iff]
    intro s hsS
    let u : R := (d : R)⁻¹ * s * (d : R) * s⁻¹
    have huT : u ∈ T := by
      have hmem : ⁅(d : R)⁻¹, s⁆ ∈ (⁅(⊤ : Subgroup R), S⁆ : Subgroup R) :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) hsS
      have hexpr : (d : R)⁻¹ * s * (d : R) * s⁻¹ = ⁅(d : R)⁻¹, s⁆ := by
        rw [commutatorElement_def]
        group
      dsimp [u]
      rw [hexpr]
      rwa [Subgroup.commutator_comm] at hmem
    have hconj : (d : R)⁻¹ * s * (d : R) = u * s := by
      dsimp [u]
      group
    have hdu : (d : R) * u = u * (d : R) :=
      (Subgroup.mem_centralizer_iff.mp d.property u huT).symm
    have hup : u ^ p = 1 :=
      congrArg Subtype.val (hT_elem.pow_eq_one ⟨u, huT⟩)
    exact pow_centralizes_of_displacement_order_p hconj hdu hup
  exact (QuotientGroup.eq_one_iff (d ^ p)).mpr hd_pow_C

/-- Lift a quotient-level product decomposition through `G/N`, when the kernel
`N` is already contained in the first factor. -/
private theorem sup_eq_top_of_quotient_sup_eq_top
    {G : Type*} [Group G] {N X Y : Subgroup G} [N.Normal]
    (hN_le_X : N ≤ X)
    (hquot : X.map (QuotientGroup.mk' N) ⊔ Y.map (QuotientGroup.mk' N) = ⊤) :
    X ⊔ Y = ⊤ := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hmap : (X ⊔ Y).map q = ⊤ := by
    rw [Subgroup.map_sup, hquot]
  have hcomap : ((X ⊔ Y).map q).comap q = N ⊔ (X ⊔ Y) :=
    QuotientGroup.comap_map_mk' N (X ⊔ Y)
  have hN_sup_top : N ⊔ (X ⊔ Y) = ⊤ := by
    rw [hmap, Subgroup.comap_top] at hcomap
    exact hcomap.symm
  have hN_le_sup : N ≤ X ⊔ Y := hN_le_X.trans le_sup_left
  have hcollapse : N ⊔ (X ⊔ Y) = X ⊔ Y := sup_eq_right.mpr hN_le_sup
  rwa [hcollapse] at hN_sup_top

/-- Blackburn 4.16 Case B-2: the Maschke complement `X/C` lifts to
`D = X T`, where `D = C_R(T)`, `C = C_R(S)`, and `T = [S,R]`. -/
theorem blackburn_noncentral_centralizer_complement_sup_commutator_eq_top
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hT_facts :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      (Subgroup.center S).map S.subtype < T ∧ T < S ∧ Nat.card T = p ^ 2)
    (hT_elem :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      T.IsElementaryAbelian p)
    {X : Subgroup (Subgroup.centralizer ((⁅Omega R p 1, (⊤ : Subgroup R)⁆ : Subgroup R) : Set R))}
    (hC_le_X :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      let C : Subgroup R := Subgroup.centralizer (S : Set R)
      let D : Subgroup R := Subgroup.centralizer (T : Set R)
      C.subgroupOf D ≤ X)
    (hX_sup_T :
      let S : Subgroup R := Omega R p 1
      let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
      let C : Subgroup R := Subgroup.centralizer (S : Set R)
      let D : Subgroup R := Subgroup.centralizer (T : Set R)
      let hCD_normal : (C.subgroupOf D).Normal :=
        (blackburn_noncentral_centralizer_normalities (R := R) (p := p)).2.2
      letI : (C.subgroupOf D).Normal := hCD_normal
      X.map (QuotientGroup.mk' (C.subgroupOf D)) ⊔
          (T.subgroupOf D).map (QuotientGroup.mk' (C.subgroupOf D)) =
        Omega (D ⧸ C.subgroupOf D) p 1) :
    let S : Subgroup R := Omega R p 1
    let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
    let D : Subgroup R := Subgroup.centralizer (T : Set R)
    X ⊔ T.subgroupOf D = ⊤ := by
  dsimp at hT_facts hT_elem hC_le_X hX_sup_T ⊢
  let S : Subgroup R := Omega R p 1
  let T : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
  let C : Subgroup R := Subgroup.centralizer (S : Set R)
  let D : Subgroup R := Subgroup.centralizer (T : Set R)
  have hCD_norms := blackburn_noncentral_centralizer_normalities (R := R) (p := p)
  have hCD_normal : (C.subgroupOf D).Normal := hCD_norms.2.2
  have hD_quot_omega_top :=
    blackburn_noncentral_centralizer_quotient_omega_eq_top hT_facts hT_elem
  have hquot_top : X.map (QuotientGroup.mk' (C.subgroupOf D)) ⊔
      (T.subgroupOf D).map (QuotientGroup.mk' (C.subgroupOf D)) = ⊤ := by
    simpa [hD_quot_omega_top] using hX_sup_T
  exact sup_eq_top_of_quotient_sup_eq_top hC_le_X hquot_top

end BlackburnClassification

end OddOrder.BG.Ch1.S04


