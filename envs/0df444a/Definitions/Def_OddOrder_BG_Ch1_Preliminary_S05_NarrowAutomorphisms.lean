-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S05_NarrowAutomorphisms
-- name    : OddOrder_BG_Ch1_Preliminary_S05_NarrowAutomorphisms
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:26:17.241389+00:00
-- url     : https://prove2.me/theorems/9d45b65c-c344-4bf4-8d68-faaed39b03f1
-- title:
--   BG §5: narrow $p$-groups, Theorem 5.5
-- statement:
--   Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, Chapter I §5, Theorem 5.5: the structure of solvable odd automorphism groups of narrow $p$-groups.
--
--   Results: `isPGroup_commutator_and_orderOf_dvd_of_narrow_witness` (the $r(R)\ge3$ chain machinery) and `thm55c_of_pRank_le_two` (BG Theorem 5.5(c), the $r(R)\le2$ assembly).
--
--   The bundle also proves 7 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S05_NarrowAutomorphisms.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S05_NarrowAutomorphisms.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S05_NarrowCharacterization

namespace OddOrder.BG.Ch1.S05

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped IsMulCommutative commutatorElement

variable {R : Type*} [Group R]

/-- **BG Theorem 5.5(a) core (generic)**: if `A'` is a `p`-group then `A/O_p(A)` is an
abelian `p'`-group. Abelian: `A' ⊴ A` is a normal `p`-subgroup, so `A' ≤ O_p(A)`.
`p'`: an order-`p` element of the abelian quotient (Cauchy) would generate a normal
`p`-subgroup whose pullback is a normal `p`-subgroup of `A` not inside `O_p(A)`'s kernel.

Both branches of Thm 5.5 (`r(R) ≤ 2` via Lemma 4.17, `r(R) ≥ 3` via the `H_i` chain)
land here once `A'` is known to be a `p`-group. -/
private theorem quotient_opCore_comm_and_not_dvd_of_isPGroup_commutator
    {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    (hA' : IsPGroup p (_root_.commutator A)) :
    (∀ x y : A ⧸ Ch01.opCore p A, x * y = y * x) ∧
      ¬ p ∣ Nat.card (A ⧸ Ch01.opCore p A) := by
  classical
  have hA'_le : _root_.commutator A ≤ Ch01.opCore p A :=
    Ch01.normal_pgroup_le_opCore hA'
  have hcomm : ∀ x y : A ⧸ Ch01.opCore p A, x * y = y * x := by
    intro x y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hrw : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [hrw]
    exact hA'_le (Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
      (Subgroup.mem_top _))
  refine ⟨hcomm, ?_⟩
  intro hp_dvd
  obtain ⟨x, hx_ord⟩ := exists_prime_orderOf_dvd_card' p hp_dvd
  have hx_ne : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx_ord
    exact (Fact.out : p.Prime).one_lt.ne' hx_ord.symm
  -- `⟨x⟩` is a normal `p`-subgroup of the abelian quotient.
  have hS_pg : IsPGroup p (Subgroup.zpowers x) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hx_ord, pow_one]
  have hS_norm : (Subgroup.zpowers x).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hgn : g * n * g⁻¹ = n := by
      rw [hcomm g n]
      group
    rwa [hgn]
  -- Pull back along `mk'`: a normal `p`-subgroup of `A`, hence `≤ O_p(A)`.
  have hP_pg : IsPGroup p
      ((Subgroup.zpowers x).comap (QuotientGroup.mk' (Ch01.opCore p A))) := by
    refine hS_pg.comap_of_ker_isPGroup _ ?_
    rw [QuotientGroup.ker_mk']
    exact Ch01.opCore_isPGroup p A
  have hP_norm :
      ((Subgroup.zpowers x).comap (QuotientGroup.mk' (Ch01.opCore p A))).Normal :=
    Subgroup.Normal.comap hS_norm _
  have hP_le := Ch01.normal_pgroup_le_opCore hP_pg
  -- `x` lifts into `O_p(A)`, so it dies in the quotient: contradiction with `orderOf x = p`.
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (Ch01.opCore p A) x
  have ha_mem : a ∈ (Subgroup.zpowers x).comap (QuotientGroup.mk' (Ch01.opCore p A)) := by
    rw [Subgroup.mem_comap, ha]
    exact Subgroup.mem_zpowers x
  have hx_one : x = 1 := by
    rw [← ha]
    exact (QuotientGroup.eq_one_iff a).mpr (hP_le ha_mem)
  exact hx_ne hx_one

/-- A characteristic subgroup of exponent `p` is nontrivial as a subgroup
(`exponent ⊥ = 1 ≠ p`). Shared input for the `H ∩ Z(R) ≠ 1` steps of Thm 5.5. -/
private theorem ne_bot_of_exponent_eq_prime
    {p : ℕ} [Fact p.Prime] {H : Subgroup R} (hHexp : Monoid.exponent ↥H = p) :
    H ≠ ⊥ := by
  intro hbot
  have h1 : Monoid.exponent ↥H = 1 := by
    have : Subsingleton ↥H := by rw [hbot]; infer_instance
    exact Monoid.exp_eq_one_of_subsingleton
  rw [hHexp] at h1
  exact (Fact.out : p.Prime).one_lt.ne' h1

/-- **BG Theorem 5.5 support (Brick A)**: under `r(R) ≥ 3`, a narrow witness `S = R₀`
(order `p`, `C_R(S) = S ⊔ K` with `K` cyclic) cannot lie inside the Thompson critical
subgroup `H` (characteristic, `⁅H,⊤⁆ ≤ Z(H)`, exponent `p`).

Otherwise `U = S ⊔ Z(H)` is a normal (via `⁅H,⊤⁆ ≤ Z(H) ≤ U`) elementary abelian
subgroup of `C_R(S)` of order `p` — forcing `S = U ⊇ H ∩ Z(R) ≠ 1`, so `S ≤ Z(R)` and
`C_R(S) = R` has rank `≥ 3` — or of order `p²` — feeding Lemma 5.1(b) and producing an
`SCN₃` element inside `C_R(S)`. Both contradict `r(C_R(S)) ≤ 2`. mmd L1893-1900. -/
private theorem not_narrow_witness_le_critical
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p)
    {S K H : Subgroup R} (hScard : Nat.card S = p) (hKcyc : IsCyclic K)
    (hSKinf : S ⊓ K = ⊥) (hCeq : Subgroup.centralizer (S : Set R) = S ⊔ K)
    (hHchar : H.Characteristic)
    (hHcomm : ⁅H, (⊤ : Subgroup R)⁆ ≤ (Subgroup.center ↥H).map H.subtype)
    (hHexp : Monoid.exponent ↥H = p) :
    ¬ S ≤ H := by
  classical
  have : H.Characteristic := hHchar
  intro hSH
  have hSrank : pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2 :=
    pRank_centralizer_le_two_of_narrow_witness hp hpg hScard hKcyc hSKinf hCeq
  have hS_elem : S.IsElementaryAbelian p := isElementaryAbelian_of_card_prime hScard
  -- `Z(H)` mapped into `R`, and `U = S ⊔ Z(H)`.
  set ZH : Subgroup R := (Subgroup.center ↥H).map H.subtype with hZH_def
  have hZH_le_H : ZH ≤ H := Subgroup.map_subtype_le _
  have hZH_elem : ZH.IsElementaryAbelian p := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩
      obtain ⟨x', hx'_center, rfl⟩ := hx
      obtain ⟨y', hy'_center, rfl⟩ := hy
      apply Subtype.ext
      change (x' : R) * (y' : R) = (y' : R) * (x' : R)
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy'_center x')
    · rintro ⟨x, hx⟩
      apply Subtype.ext
      obtain ⟨x', _, rfl⟩ := hx
      have : x' ^ p = 1 := by
        rw [← hHexp]
        exact Monoid.pow_exponent_eq_one x'
      calc ((⟨(x' : R), _⟩ : ↥ZH) ^ p : ↥ZH).val = (x' : R) ^ p := rfl
        _ = ((x' ^ p : ↥H) : R) := rfl
        _ = 1 := by rw [this]; rfl
  have hS_le_cent_ZH : S ≤ Subgroup.centralizer (ZH : Set R) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    rintro z hz
    obtain ⟨z', hz'_center, rfl⟩ := hz
    exact (congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hz'_center ⟨s, hSH hs⟩)).symm
  set U : Subgroup R := S ⊔ ZH with hU_def
  have hU_elem : U.IsElementaryAbelian p :=
    Subgroup.IsElementaryAbelian.sup_of_le_centralizer hS_elem hZH_elem hS_le_cent_ZH
  have hS_le_C : S ≤ Subgroup.centralizer (S : Set R) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (hS_elem.comm ⟨t, ht⟩ ⟨s, hs⟩)
  have hZH_le_C : ZH ≤ Subgroup.centralizer (S : Set R) := by
    rintro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨z', hz'_center, rfl⟩ := hz
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hz'_center ⟨s, hSH hs⟩)
  have hU_le_C : U ≤ Subgroup.centralizer (S : Set R) := sup_le hS_le_C hZH_le_C
  -- `U ⊴ R` via `⁅U,⊤⁆ ≤ ⁅H,⊤⁆ ≤ Z(H) ≤ U`.
  have hU_le_H : U ≤ H := sup_le hSH hZH_le_H
  have hU_normal : U.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    rw [eq_top_iff]
    apply OddOrder.Isaacs.Ch04.le_normalizer_of_commutator_le
    calc ⁅U, (⊤ : Subgroup R)⁆ ≤ ⁅H, (⊤ : Subgroup R)⁆ :=
          Subgroup.commutator_mono hU_le_H le_rfl
      _ ≤ ZH := hHcomm
      _ ≤ U := le_sup_right
  -- `|U| = p ^ d` with `1 ≤ d ≤ 2`.
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp (hpg.to_subgroup U)
  have hd_ge : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h
    · exfalso
      rw [h0, pow_zero] at hd
      have hcard_le : Nat.card S ≤ 1 := by
        rw [← hd]
        exact Subgroup.card_le_of_le le_sup_left
      rw [hScard] at hcard_le
      have := (Fact.out : p.Prime).one_lt
      omega
    · exact h
  have hd_le : d ≤ 2 := by
    let Usub : Subgroup ↥(Subgroup.centralizer (S : Set R)) :=
      U.subgroupOf (Subgroup.centralizer (S : Set R))
    have hUsub_elem : Usub.IsElementaryAbelian p :=
      IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hU_le_C).symm hU_elem
    have hUsub_card : Nat.card Usub = Nat.card U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU_le_C).toEquiv
    have hlog := (pRank_le_iff.mp hSrank) Usub hUsub_elem
    rw [hUsub_card, hd, Nat.log_pow (Fact.out : p.Prime).one_lt] at hlog
    exact hlog
  -- `H ∩ Z(R) ≠ 1` supplies a nontrivial central element of `H`.
  obtain ⟨z, hzH, hzZR, hz_ne⟩ :=
    OddOrder.GroupTheory.exists_mem_center_of_normal_ne_bot hpg (K := H)
      (ne_bot_of_exponent_eq_prime hHexp)
  have hz_ZH : z ∈ ZH := by
    have hz_center : (⟨z, hzH⟩ : ↥H) ∈ Subgroup.center ↥H := by
      rw [Subgroup.mem_center_iff]
      intro h
      exact Subtype.ext (Subgroup.mem_center_iff.mp hzZR (h : R))
    exact ⟨⟨z, hzH⟩, hz_center, rfl⟩
  interval_cases d
  -- `d = 1`: `U = S`, so `S` contains `z`, is central, and `C_R(S) = ⊤` has rank ≥ 3.
  · have hUS : S = U := by
      refine Subgroup.eq_of_le_of_card_ge le_sup_left (le_of_eq ?_)
      rw [hd, pow_one, hScard]
    have hzU : z ∈ U := Subgroup.mem_sup_right hz_ZH
    have hzS : z ∈ S := by rw [hUS]; exact hzU
    have hzpow_eq : Subgroup.zpowers z = S := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzS) ?_
      have hdvd : Nat.card (Subgroup.zpowers z) ∣ Nat.card S :=
        Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hzS)
      have hne1 : Nat.card (Subgroup.zpowers z) ≠ 1 := by
        rw [Nat.card_zpowers]
        intro h1
        exact hz_ne (orderOf_eq_one_iff.mp h1)
      rw [hScard] at hdvd ⊢
      rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h | h
      · exact absurd h hne1
      · omega
    have hS_le_center : S ≤ Subgroup.center R := by
      rw [← hzpow_eq]
      exact Subgroup.zpowers_le.mpr hzZR
    have hCtop : Subgroup.centralizer (S : Set R) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact (Subgroup.mem_center_iff.mp (hS_le_center hs) x).symm
    let toC : R →* ↥(Subgroup.centralizer (S : Set R)) :=
      { toFun := fun r => ⟨r, by rw [hCtop]; exact trivial⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have htoC_inj : Function.Injective toC := fun x y hxy => congrArg Subtype.val hxy
    have hRrank_le : pRank R p ≤ pRank ↥(Subgroup.centralizer (S : Set R)) p :=
      pRank_le_of_injective (f := toC) htoC_inj
    omega
  -- `d = 2`: `U` is a normal `E_{p²}`, so Lemma 5.1(b) puts an `SCN₃` element in `C_R(S)`.
  · obtain ⟨A, hA_scn3, hUA⟩ :=
      mem_scn3_of_normal_isElementaryAbelian_card_prime_sq hp hpg h3 U hU_elem hd
    have hA_le_CS : A ≤ Subgroup.centralizer (S : Set R) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hsA : s ∈ A := hUA (Subgroup.mem_sup_left hs)
      have := hA_scn3.isSCN.isMulCommutative
      exact congrArg Subtype.val (mul_comm (⟨s, hsA⟩ : ↥A) ⟨a, ha⟩)
    have hArank_le : pRank ↥A p ≤ pRank ↥(Subgroup.centralizer (S : Set R)) p :=
      pRank_le_of_injective (f := Subgroup.inclusion hA_le_CS)
        (Subgroup.inclusion_injective hA_le_CS)
    have h3A : 3 ≤ pRank ↥A p := hA_scn3.le_pRank
    omega

/-- **BG (5.5) `|C_H(S)| = p`** (Brick B): for a narrow witness `S` not inside the
Thompson critical `H` (exponent `p`), the centralizer `C_H(S) = H ⊓ C_R(S)` has order
exactly `p`: it is cyclic of exponent `p` (rank-2 squeeze), and contains the
nontrivial `H ∩ Z(R)`. mmd L1901-1904, (5.5). -/
private theorem card_inf_critical_centralizer_eq_prime
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    {S K H : Subgroup R} (hScard : Nat.card S = p) (hKcyc : IsCyclic K)
    (hSKinf : S ⊓ K = ⊥) (hCeq : Subgroup.centralizer (S : Set R) = S ⊔ K)
    (hHchar : H.Characteristic) (hHexp : Monoid.exponent ↥H = p)
    (hSH : ¬ S ≤ H) :
    Nat.card ↥(H ⊓ Subgroup.centralizer (S : Set R)) = p := by
  classical
  have : H.Characteristic := hHchar
  have hSrank : pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2 :=
    pRank_centralizer_le_two_of_narrow_witness hp hpg hScard hKcyc hSKinf hCeq
  have hSH_bot : S ⊓ H = ⊥ := by
    by_contra hne
    exact hSH (le_of_inf_ne_bot_of_card_prime hScard hne)
  have hScap : S ⊓ (H ⊓ Subgroup.centralizer (S : Set R)) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    have : x ∈ S ⊓ H := ⟨hx.1, hx.2.1⟩
    rwa [hSH_bot] at this
  have hcyc : IsCyclic ↥(H ⊓ Subgroup.centralizer (S : Set R)) :=
    isCyclic_of_le_centralizer_of_inf_eq_bot_of_pRank_le_two hp hpg hScard hSrank
      inf_le_right hScap
  -- cyclic of exponent dividing `p` ⇒ order divides `p`
  have hexp_dvd : Monoid.exponent ↥(H ⊓ Subgroup.centralizer (S : Set R)) ∣ p := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro x
    apply Subtype.ext
    have hxH : (x : R) ∈ H := x.2.1
    have : ((⟨(x : R), hxH⟩ : ↥H) ^ p : ↥H) = 1 := by
      rw [← hHexp]
      exact Monoid.pow_exponent_eq_one _
    calc ((x ^ p : ↥(H ⊓ Subgroup.centralizer (S : Set R))) : R)
        = (x : R) ^ p := rfl
      _ = ((⟨(x : R), hxH⟩ : ↥H) ^ p : ↥H) := rfl
      _ = 1 := by rw [this]; rfl
  have hcard_dvd : Nat.card ↥(H ⊓ Subgroup.centralizer (S : Set R)) ∣ p := by
    have := hcyc
    calc Nat.card ↥(H ⊓ Subgroup.centralizer (S : Set R))
        = Monoid.exponent ↥(H ⊓ Subgroup.centralizer (S : Set R)) :=
          IsCyclic.exponent_eq_card.symm
      _ ∣ p := hexp_dvd
  -- the nontrivial `H ∩ Z(R)` lands in `C_H(S)`
  obtain ⟨z, hzH, hzZR, hz_ne⟩ :=
    OddOrder.GroupTheory.exists_mem_center_of_normal_ne_bot hpg (K := H)
      (ne_bot_of_exponent_eq_prime hHexp)
  have hz_mem : z ∈ H ⊓ Subgroup.centralizer (S : Set R) := by
    refine ⟨hzH, ?_⟩
    change z ∈ Subgroup.centralizer (S : Set R)
    rw [Subgroup.mem_centralizer_iff]
    intro s _
    exact Subgroup.mem_center_iff.mp hzZR s
  have hcard_ne1 : Nat.card ↥(H ⊓ Subgroup.centralizer (S : Set R)) ≠ 1 := by
    intro h1
    have hbot : H ⊓ Subgroup.centralizer (S : Set R) = ⊥ :=
      Subgroup.eq_bot_of_card_eq _ h1
    rw [hbot, Subgroup.mem_bot] at hz_mem
    exact hz_ne hz_mem
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hcard_dvd with h | h
  · exact absurd h hcard_ne1
  · exact h

/-- **Chain factor counting, injection form (BG (5.6) step)**: if every `⁅v,·⁆`-commutator
of `M` lands in `N`, then `|M : C_M(v)| ≤ |N|`.

The map `x ↦ ⁅v, x⁆` is constant exactly on left cosets of `C_M(v)`, hence induces an
**injection** `M ⧸ C_M(v) ↪ N`. mmd L1907-1913.

Pure counting: no `p`-group, oddness or narrowness hypothesis, and no bound on the
centralizer.  This is the sharp form; `card_le_card_mul_of_commutator_mem_of_card_centralizer_le`
is the immediate corollary once `|C_M(v)|` is bounded.

⚠ The index bound is what App.E's (E.12) needs: there the counting is *tight*, so the
injection is a bijection, and that is what forces `⁅v, x⁆ ∈ H_{i+1} ↔ x ∈ H_i` — a step BG
asserts without proof when it writes "`⟨w̄ᵢ⟩ = H̄ᵢ`". -/
theorem index_centralizer_le_card_of_commutator_mem
    [Finite R] {M N : Subgroup R} {v : R}
    (hcomm : ∀ x ∈ M, ⁅v, x⁆ ∈ N) :
    ((Subgroup.centralizer ({v} : Set R) ⊓ M).subgroupOf M).index ≤ Nat.card ↥N := by
  classical
  set C' : Subgroup ↥M :=
    (Subgroup.centralizer ({v} : Set R) ⊓ M).subgroupOf M with hC'_def
  -- the commutator map is constant exactly on left cosets of `C'`
  have key : ∀ x y : ↥M, ⁅v, (x : R)⁆ = ⁅v, (y : R)⁆ ↔ x⁻¹ * y ∈ C' := by
    intro x y
    have hmem_iff : x⁻¹ * y ∈ C' ↔
        v * ((x : R)⁻¹ * (y : R)) = ((x : R)⁻¹ * (y : R)) * v := by
      rw [hC'_def, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        have h1 : ((x⁻¹ * y : ↥M) : R) ∈ Subgroup.centralizer ({v} : Set R) := h.1
        rw [Subgroup.mem_centralizer_iff] at h1
        exact h1 v (Set.mem_singleton v)
      · intro h
        refine ⟨?_, (x⁻¹ * y).2⟩
        change ((x⁻¹ * y : ↥M) : R) ∈ Subgroup.centralizer ({v} : Set R)
        rw [Subgroup.mem_centralizer_iff]
        intro h' hh'
        rw [Set.mem_singleton_iff] at hh'
        subst hh'
        exact h
    rw [hmem_iff]
    constructor
    · intro h
      rw [commutatorElement_def, commutatorElement_def] at h
      have h2 : (x : R) * v⁻¹ * (x : R)⁻¹ = (y : R) * v⁻¹ * (y : R)⁻¹ := by
        refine mul_left_cancel (a := v) ?_
        calc v * ((x : R) * v⁻¹ * (x : R)⁻¹)
            = v * (x : R) * v⁻¹ * ((x : R))⁻¹ := by group
          _ = v * (y : R) * v⁻¹ * ((y : R))⁻¹ := h
          _ = v * ((y : R) * v⁻¹ * (y : R)⁻¹) := by group
      have h3 : v⁻¹ * ((x : R)⁻¹ * (y : R)) = ((x : R)⁻¹ * (y : R)) * v⁻¹ := by
        calc v⁻¹ * ((x : R)⁻¹ * (y : R))
            = (x : R)⁻¹ * ((x : R) * v⁻¹ * (x : R)⁻¹) * (y : R) := by group
          _ = (x : R)⁻¹ * ((y : R) * v⁻¹ * (y : R)⁻¹) * (y : R) := by rw [h2]
          _ = ((x : R)⁻¹ * (y : R)) * v⁻¹ := by group
      have h4 : Commute v⁻¹ ((x : R)⁻¹ * (y : R)) := h3
      exact (Commute.inv_left_iff.mp h4).eq
    · intro h
      have hgv : ((x : R)⁻¹ * (y : R)) * v⁻¹ = v⁻¹ * ((x : R)⁻¹ * (y : R)) := by
        calc ((x : R)⁻¹ * (y : R)) * v⁻¹
            = v⁻¹ * (v * ((x : R)⁻¹ * (y : R))) * v⁻¹ := by group
          _ = v⁻¹ * (((x : R)⁻¹ * (y : R)) * v) * v⁻¹ := by rw [h]
          _ = v⁻¹ * ((x : R)⁻¹ * (y : R)) := by group
      rw [commutatorElement_def, commutatorElement_def]
      calc v * (x : R) * v⁻¹ * ((x : R))⁻¹
          = v * (x : R) * (v⁻¹ * ((x : R)⁻¹ * (y : R)))
              * (((x : R)⁻¹ * (y : R)))⁻¹ * ((x : R))⁻¹ := by group
        _ = v * (x : R) * (((x : R)⁻¹ * (y : R)) * v⁻¹)
              * (((x : R)⁻¹ * (y : R)))⁻¹ * ((x : R))⁻¹ := by rw [hgv]
        _ = v * (y : R) * v⁻¹ * ((y : R))⁻¹ := by group
  -- the induced injection `↥M ⧸ C' ↪ ↥N`
  let F : (↥M ⧸ C') → ↥N := Quotient.lift
    (fun x : ↥M => (⟨⁅v, (x : R)⁆, hcomm _ x.2⟩ : ↥N))
    (by
      intro x y hxy
      have hmem : x⁻¹ * y ∈ C' := (QuotientGroup.leftRel_apply).mp hxy
      exact Subtype.ext ((key x y).mpr hmem))
  have hF_inj : Function.Injective F := by
    intro q₁ q₂
    refine Quotient.inductionOn₂ q₁ q₂ ?_
    intro x y h
    have hxy : ⁅v, (x : R)⁆ = ⁅v, (y : R)⁆ := congrArg Subtype.val h
    exact Quotient.sound ((QuotientGroup.leftRel_apply).mpr ((key x y).mp hxy))
  have : Nat.card (↥M ⧸ C') ≤ Nat.card ↥N := Nat.card_le_card_of_injective F hF_inj
  simpa [hC'_def, Subgroup.index] using this

/-- **Chain factor counting (BG (5.6) step)**: if every `⁅v,·⁆`-commutator of `M` lands
in `N` and the `v`-centralizer inside `M` has order at most `m`, then `|M| ≤ |N| · m`.

Immediate from the sharp `index_centralizer_le_card_of_commutator_mem` together with the
bound on `|C_M(v)|`. -/
theorem card_le_card_mul_of_commutator_mem_of_card_centralizer_le
    [Finite R] {M N : Subgroup R} {v : R} {m : ℕ}
    (hcomm : ∀ x ∈ M, ⁅v, x⁆ ∈ N)
    (hcent : Nat.card ↥(Subgroup.centralizer ({v} : Set R) ⊓ M) ≤ m) :
    Nat.card ↥M ≤ Nat.card ↥N * m := by
  set C' : Subgroup ↥M :=
    (Subgroup.centralizer ({v} : Set R) ⊓ M).subgroupOf M with hC'_def
  have hC'_card : Nat.card C' ≤ m := by
    rw [hC'_def]
    calc Nat.card ↥((Subgroup.centralizer ({v} : Set R) ⊓ M).subgroupOf M)
        = Nat.card ↥(Subgroup.centralizer ({v} : Set R) ⊓ M) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
      _ ≤ m := hcent
  calc Nat.card ↥M = C'.index * Nat.card C' := (C'.index_mul_card).symm
    _ ≤ Nat.card ↥N * m :=
        Nat.mul_le_mul (index_centralizer_le_card_of_commutator_mem hcomm) hC'_card

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **BG Theorem 5.5, `r(R) ≥ 3` chain machinery** (mmd L1905-1917): for a narrow
witness `S` and any faithful action `φ : A →* MulAut R`, the descending chain
`H_0 = H` (Thompson critical), `H_{i+1} = ⁅H_i, R⁆` is characteristic with factors of
order dividing `p` (counting against `|C_H(S)| = p`) and reaches `⊥` (nilpotency).
Each factor has automorphism group of order dividing `p - 1`, so `A'` and every
`α^(p-1)` stabilize the chain; a `p'`-order stabilizing element acts trivially on `H`
(BG Lem 1.9, `coprime_stabilizes_chain_trivial`), lands in the `p`-group `C_A(H)`
(Thm 1.13), and is trivial. Hence `A'` is a `p`-group and every `p'`-element of `A`
has order dividing `p - 1` (= Thm 5.5(a)(b) inputs for `r(R) ≥ 3`). -/
private theorem isPGroup_commutator_and_orderOf_dvd_of_narrow_witness
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p)
    {S K : Subgroup R} (hScard : Nat.card S = p) (hKcyc : IsCyclic K)
    (hSKinf : S ⊓ K = ⊥) (hCeq : Subgroup.centralizer (S : Set R) = S ⊔ K)
    {A : Type*} [Group A] [Finite A] {φ : A →* MulAut R}
    (hφ : Function.Injective φ) :
    IsPGroup p (_root_.commutator A) ∧
      ∀ a : A, Nat.Coprime (orderOf a) p → orderOf a ∣ (p - 1) := by
  classical
  have hprime : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [Nat.odd_iff] at hp
    norm_num at hp
  -- `R` is nontrivial since `pRank R ≥ 3`.
  have hRnt : Nontrivial R := by
    rcases subsingleton_or_nontrivial R with hsub | hnt
    · exfalso
      have h0 : pRank R p ≤ 0 := by
        rw [pRank_le_iff]
        intro B hB
        have hcard1 : Nat.card ↥B = 1 := by
          have h1 : Nat.card R = 1 := by
            have : Unique R := ⟨⟨1⟩, fun a => Subsingleton.elim a 1⟩
            exact Nat.card_unique
          have h2 := Subgroup.card_subgroup_dvd_card B
          rw [h1] at h2
          exact Nat.dvd_one.mp h2
        rw [hcard1, Nat.log_one_right]
      omega
    · exact hnt
  -- Thompson critical subgroup.
  obtain ⟨H, hHchar, hHcommtop, hHcommcenter, hHexp, hHaut⟩ :=
    OddOrder.BG.Ch1.S01.thompson_critical_omega (p := p) hp2 hpg
  have : H.Characteristic := hHchar
  have hH_pg : IsPGroup p ↥H := hpg.to_subgroup H
  have hSH : ¬ S ≤ H :=
    not_narrow_witness_le_critical hp hpg h3 hScard hKcyc hSKinf hCeq hHchar
      hHcommtop hHexp
  have hCH_card : Nat.card ↥(H ⊓ Subgroup.centralizer (S : Set R)) = p :=
    card_inf_critical_centralizer_eq_prime hp hpg hScard hKcyc hSKinf hCeq hHchar
      hHexp hSH
  -- generator of `S`.
  have hS_nt : Nontrivial ↥S := by
    rw [← Finite.one_lt_card_iff_nontrivial, hScard]
    exact hprime.one_lt
  obtain ⟨⟨v, hvS⟩, hv_ne⟩ := exists_ne (1 : ↥S)
  have hv_ne1 : v ≠ 1 := fun h => hv_ne (Subtype.ext h)
  have hzpow_v : Subgroup.zpowers v = S := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hvS) ?_
    have hdvd : Nat.card (Subgroup.zpowers v) ∣ Nat.card S :=
      Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hvS)
    have hne1 : Nat.card (Subgroup.zpowers v) ≠ 1 := by
      rw [Nat.card_zpowers]
      intro h1
      exact hv_ne1 (orderOf_eq_one_iff.mp h1)
    rw [hScard] at hdvd ⊢
    rcases (Nat.dvd_prime hprime).mp hdvd with h | h
    · exact absurd h hne1
    · omega
  -- the `v`-centralizer inside `H` sits in `C_H(S)`.
  have hCv_le : ∀ {M : Subgroup R}, M ≤ H →
      Subgroup.centralizer ({v} : Set R) ⊓ M ≤
        H ⊓ Subgroup.centralizer (S : Set R) := by
    intro M hMH x hx
    refine ⟨hMH hx.2, ?_⟩
    change x ∈ Subgroup.centralizer (S : Set R)
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [← hzpow_v] at hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    have hxv : Commute v x := by
      have h1 : x ∈ Subgroup.centralizer ({v} : Set R) := hx.1
      rw [Subgroup.mem_centralizer_iff] at h1
      exact h1 v (Set.mem_singleton v)
    exact (hxv.zpow_left k).eq
  -- the descending characteristic chain `s 0 = H`, `s (i+1) = ⁅s i, R⁆`.
  set s : ℕ → Subgroup R := fun i => (fun B => ⁅B, (⊤ : Subgroup R)⁆)^[i] H with hs_def
  have hs0 : s 0 = H := rfl
  have hs_succ : ∀ i, s (i + 1) = ⁅s i, (⊤ : Subgroup R)⁆ := by
    intro i
    rw [hs_def]
    exact Function.iterate_succ_apply' _ i H
  have hchar : ∀ i, (s i).Characteristic := by
    intro i
    induction i with
    | zero => exact hHchar
    | succ i ih =>
      rw [hs_succ]
      have := ih
      infer_instance
  have hnormal : ∀ i, (s i).Normal := fun i => by have := hchar i; infer_instance
  have hs_step : ∀ i, s (i + 1) ≤ s i := by
    intro i
    rw [hs_succ, Subgroup.commutator_comm]
    have := hnormal i
    exact Subgroup.commutator_le_right ⊤ (s i)
  have hs_le_H : ∀ i, s i ≤ H := by
    intro i
    induction i with
    | zero => exact le_of_eq hs0
    | succ i ih => exact (hs_step i).trans ih
  have hanti : Antitone s := antitone_nat_of_succ_le hs_step
  obtain ⟨n, hn⟩ : ∃ n, (⊤ : Subgroup R).lowerCentralSeries n = ⊥ := by
    have := hpg.isNilpotent
    exact Subgroup.nilpotent_iff_lowerCentralSeries.mp inferInstance
  have hsn : s n = ⊥ := by
    have hLCS : ∀ i, s i ≤ (⊤ : Subgroup R).lowerCentralSeries i := by
      intro i
      induction i with
      | zero =>
        rw [Subgroup.lowerCentralSeries_zero]
        exact le_top
      | succ i ih =>
        rw [hs_succ, Subgroup.lowerCentralSeries_succ]
        exact Subgroup.commutator_mono ih le_rfl
    exact le_bot_iff.mp (hn ▸ hLCS n)
  -- factor bound `|s i| ≤ |s (i+1)| · p`.
  have hfactor : ∀ i, Nat.card ↥(s i) ≤ Nat.card ↥(s (i + 1)) * p := by
    intro i
    refine card_le_card_mul_of_commutator_mem_of_card_centralizer_le (v := v) ?_ ?_
    · intro x hx
      rw [hs_succ, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top v) hx
    · calc Nat.card ↥(Subgroup.centralizer ({v} : Set R) ⊓ s i)
          ≤ Nat.card ↥(H ⊓ Subgroup.centralizer (S : Set R)) :=
            Subgroup.card_le_of_le (hCv_le (hs_le_H i))
        _ = p := hCH_card
  -- factor cards divide `p`.
  have hQcard : ∀ i, Nat.card (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i)) ∣ p := by
    intro i
    have : ((s (i + 1)).subgroupOf (s i)).Normal :=
      (hnormal (i + 1)).subgroupOf (s i)
    have hmul : Nat.card (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i)) *
        Nat.card ((s (i + 1)).subgroupOf (s i)) = Nat.card ↥(s i) := by
      have := ((s (i + 1)).subgroupOf (s i)).index_mul_card
      simpa [Subgroup.index] using this
    have hN'card : Nat.card ((s (i + 1)).subgroupOf (s i)) = Nat.card ↥(s (i + 1)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hs_step i)).toEquiv
    have hQ_le : Nat.card (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i)) ≤ p := by
      have h1 : Nat.card (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i)) *
          Nat.card ((s (i + 1)).subgroupOf (s i)) ≤
          p * Nat.card ((s (i + 1)).subgroupOf (s i)) := by
        calc Nat.card (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i)) *
            Nat.card ((s (i + 1)).subgroupOf (s i)) = Nat.card ↥(s i) := hmul
          _ ≤ Nat.card ↥(s (i + 1)) * p := hfactor i
          _ = p * Nat.card ((s (i + 1)).subgroupOf (s i)) := by
              rw [hN'card]; ring
      exact Nat.le_of_mul_le_mul_right h1 Nat.card_pos
    obtain ⟨e, he⟩ :=
      IsPGroup.iff_card.mp
        ((hpg.to_subgroup (s i)).to_quotient ((s (i + 1)).subgroupOf (s i)))
    rw [he] at hQ_le ⊢
    have he_le : e ≤ 1 := by
      have h2 : p ^ e ≤ p ^ 1 := by
        rw [pow_one]
        exact hQ_le
      exact (Nat.pow_le_pow_iff_right hprime.one_lt).mp h2
    calc p ^ e ∣ p ^ 1 := pow_dvd_pow p he_le
      _ = p := pow_one p
  -- `A` acts on each `s i` and on each factor.
  have hsi_inv : ∀ i, OddOrder.Isaacs.Ch03.IsAInvariant φ (s i) := fun i => by
    have := hchar i
    exact OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic φ
  set ψs : (i : ℕ) → A →* MulAut ↥(s i) := fun i =>
    OddOrder.BG.Ch1.S01.restrictAction (hsi_inv i) with hψs_def
  have hNi_inv : ∀ i, OddOrder.Isaacs.Ch03.IsAInvariant (ψs i)
      ((s (i + 1)).subgroupOf (s i)) := by
    intro i
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a g hg
    rw [Subgroup.mem_subgroupOf] at hg ⊢
    have hval : (((ψs i) a g : ↥(s i)) : R) = φ a (g : R) := by
      rw [hψs_def]
      rfl
    rw [hval]
    exact (hsi_inv (i + 1)).smul_mem a hg
  set ψQ : (i : ℕ) → A →* MulAut (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i)) := fun i =>
    letI := (hnormal (i + 1)).subgroupOf (s i)
    quotientMulAutHom (hNi_inv i) with hψQ_def
  -- the chain stabilizer.
  set Stab : Subgroup A := ⨅ i, (ψQ i).ker with hStab_def
  have hStab_mem : ∀ a : A, a ∈ Stab ↔ ∀ i, (ψQ i) a = 1 := by
    intro a
    rw [hStab_def]
    simp [Subgroup.mem_iInf, MonoidHom.mem_ker]
  -- each factor automorphism group has order dividing `p - 1`.
  have hMulAutQ : ∀ i,
      Nat.card (MulAut (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i))) ∣ (p - 1) := by
    intro i
    have : ((s (i + 1)).subgroupOf (s i)).Normal :=
      (hnormal (i + 1)).subgroupOf (s i)
    rcases (Nat.dvd_prime hprime).mp (hQcard i) with h1 | hp'
    · have : Subsingleton (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i)) :=
        ((Nat.card_eq_one_iff_unique).mp h1).1
      have : Subsingleton (MulAut (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i))) :=
        ⟨fun f g => by ext x; exact Subsingleton.elim _ _⟩
      have hone : Nat.card (MulAut (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i))) = 1 := by
        have : Unique (MulAut (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i))) :=
          ⟨⟨1⟩, fun a => Subsingleton.elim a 1⟩
        exact Nat.card_unique
      rw [hone]
      exact one_dvd _
    · have : IsCyclic (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i)) :=
        isCyclic_of_prime_card hp'
      rw [IsCyclic.card_mulAut, hp', Nat.totient_prime hprime]
  -- `A'` and all `α^(p-1)` stabilize the chain.
  have hcomm_mem_Stab : _root_.commutator A ≤ Stab := by
    rw [_root_.commutator, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [hStab_mem]
    intro i
    have : ((s (i + 1)).subgroupOf (s i)).Normal :=
      (hnormal (i + 1)).subgroupOf (s i)
    rcases (Nat.dvd_prime hprime).mp (hQcard i) with h1 | hp'
    · have : Subsingleton (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i)) :=
        ((Nat.card_eq_one_iff_unique).mp h1).1
      have : Subsingleton (MulAut (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i))) :=
        ⟨fun f g => by ext x; exact Subsingleton.elim _ _⟩
      exact Subsingleton.elim _ _
    · have : IsCyclic (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i)) :=
        isCyclic_of_prime_card hp'
      let e := IsCyclic.mulAutMulEquiv (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i))
      let : CommGroup (MulAut (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i))) :=
        e.toMonoidHom.commGroupOfInjective e.injective
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr (mul_comm _ _)
  have hpow_mem_Stab : ∀ α : A, α ^ (p - 1) ∈ Stab := by
    intro α
    rw [hStab_mem]
    intro i
    have : ((s (i + 1)).subgroupOf (s i)).Normal :=
      (hnormal (i + 1)).subgroupOf (s i)
    rw [map_pow]
    have hdvd : orderOf ((ψQ i) α) ∣ p - 1 :=
      dvd_trans (orderOf_dvd_natCard _) (hMulAutQ i)
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  -- a `p'`-order chain stabilizer is trivial.
  have hStab_p' : ∀ b ∈ Stab, Nat.Coprime (orderOf b) p → b = 1 := by
    intro b hb hbcop
    set ψB : ↥(Subgroup.zpowers b) →* MulAut ↥H :=
      (ψs 0).comp (Subgroup.zpowers b).subtype with hψB_def
    have htriv_chain : ∀ a' : ↥(Subgroup.zpowers b), ψB a' = 1 := by
      refine OddOrder.BG.Ch1.S01.coprime_stabilizes_chain_trivial ψB ?_ (Or.inr ?_)
        (fun i => (s i).subgroupOf H) ?_ ?_ (n := n) ?_ ?_ ?_ ?_
      · rw [Nat.card_zpowers]
        obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hH_pg
        rw [hj]
        exact Nat.Coprime.pow_right j hbcop
      · have := hH_pg.isNilpotent
        infer_instance
      · intro i j hij
        exact Subgroup.comap_mono (hanti hij)
      · exact Subgroup.subgroupOf_self H
      · show (s n).subgroupOf H = ⊥
        rw [hsn]
        exact Subgroup.bot_subgroupOf H
      · intro i
        exact (hnormal i).subgroupOf H
      · intro i
        rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
        intro a' g hg
        rw [Subgroup.mem_subgroupOf] at hg ⊢
        have hval : (((ψB a') g : ↥H) : R) = φ (a' : A) (g : R) := by
          rw [hψB_def, hψs_def]
          rfl
        rw [hval]
        exact (hsi_inv i).smul_mem _ hg
      · intro i a' x hx
        have : ((s (i + 1)).subgroupOf (s i)).Normal :=
      (hnormal (i + 1)).subgroupOf (s i)
        rw [Subgroup.mem_subgroupOf] at hx
        obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp a'.2
        have hker : (ψQ i) (a' : A) = 1 := by
          rw [← hz, map_zpow]
          have h1 : (ψQ i) b = 1 := (hStab_mem b).mp hb i
          rw [h1, one_zpow]
        rw [hψQ_def] at hker
        have hker_app := congrArg
          (fun e : MulAut (↥(s i) ⧸ (s (i + 1)).subgroupOf (s i)) =>
            e ((⟨(x : R), hx⟩ : ↥(s i)) : ↥(s i) ⧸ (s (i + 1)).subgroupOf (s i))) hker
        simp only [MulAut.one_apply] at hker_app
        have hmem : (⟨(x : R), hx⟩ : ↥(s i))⁻¹ *
            (ψs i (a' : A)) ⟨(x : R), hx⟩ ∈ (s (i + 1)).subgroupOf (s i) := by
          rw [← QuotientGroup.eq]
          exact hker_app.symm
        rw [Subgroup.mem_subgroupOf] at hmem
        refine ⟨x⁻¹ * (ψB a') x, ?_, by group⟩
        rw [Subgroup.mem_subgroupOf]
        have hval : ((x⁻¹ * (ψB a') x : ↥H) : R) =
            (((⟨(x : R), hx⟩ : ↥(s i))⁻¹ *
              (ψs i (a' : A)) ⟨(x : R), hx⟩ : ↥(s i)) : R) := by
          rw [hψB_def, hψs_def]
          rfl
        change ((x⁻¹ * (ψB a') x : ↥H) : R) ∈ s (i + 1)
        rw [hval]
        exact hmem
    have hbH : (ψs 0) b = 1 := by
      have h := htriv_chain ⟨b, Subgroup.mem_zpowers b⟩
      rw [hψB_def] at h
      exact h
    have hker_le : (ψs 0).ker ≤ (autCentralizer H).comap φ := by
      intro a ha
      rw [Subgroup.mem_comap, mem_autCentralizer]
      intro h hh
      have happ := congrArg (fun e : MulAut ↥H => ((e ⟨h, hh⟩ : ↥H) : R)) ha
      calc φ a h = (((ψs 0) a ⟨h, hh⟩ : ↥H) : R) := rfl
        _ = (((1 : MulAut ↥H) ⟨h, hh⟩ : ↥H) : R) := happ
        _ = h := rfl
    have hker_pg : IsPGroup p (ψs 0).ker :=
      (hHaut.comap_of_injective φ hφ).to_le hker_le
    obtain ⟨j, hj⟩ := hker_pg ⟨b, hbH⟩
    have hj' : b ^ p ^ j = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right j hbcop) dvd_rfl
      (orderOf_dvd_of_pow_eq_one hj')
  -- conclusions.
  constructor
  · intro g
    have hn_pos : 0 < orderOf (g : A) := orderOf_pos _
    obtain ⟨k, m, hpm, hmn⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd hn_pos.ne' p hprime.ne_one
    have hm_cop : Nat.Coprime p m := hprime.coprime_iff_not_dvd.mpr hpm
    have ha'_pow_m : ((g : A) ^ p ^ k) ^ m = 1 := by
      rw [← pow_mul, ← hmn, pow_orderOf_eq_one]
    have ha'_mem : (g : A) ^ p ^ k ∈ Stab :=
      hcomm_mem_Stab ((_root_.commutator A).pow_mem g.2 _)
    have ha'_cop : Nat.Coprime (orderOf ((g : A) ^ p ^ k)) p :=
      Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one ha'_pow_m) hm_cop.symm
    have ha'_one : (g : A) ^ p ^ k = 1 := hStab_p' _ ha'_mem ha'_cop
    exact ⟨k, Subtype.ext (by simpa using ha'_one)⟩
  · intro α hα_cop
    have hα_mem : α ^ (p - 1) ∈ Stab := hpow_mem_Stab α
    have hα_pow_dvd : orderOf (α ^ (p - 1)) ∣ orderOf α := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    have hα_pow_cop : Nat.Coprime (orderOf (α ^ (p - 1))) p :=
      Nat.Coprime.coprime_dvd_left hα_pow_dvd hα_cop
    exact orderOf_dvd_of_pow_eq_one (hStab_p' _ hα_mem hα_pow_cop)

open scoped Pointwise in
open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **BG Theorem 5.5(c)** (`r(R) ≤ 2` assembly, mmd L1919-1941): if `|A| = q` is a
prime not dividing `p(p-1)`, then `q ∣ (p+1)/2` (Lemma 4.14 under `SCN₃(R) = ∅`);
if moreover `R = [R,A]` and `R` is nonabelian, then `|R| = p³`: Thm 4.16 (Blackburn)
gives the central product `R = R₁ ∘ R₂` with `Ω₁(R) = R₁` of order `p³` and `R/Ω₁(R)`
cyclic; `A` centralizes `R/Ω₁(R)` since `|Aut(C_{p^t})| = p^{t-1}(p-1)` is prime to
`q` (the **G** Thm 5.4.1 step via `Nat.totient_prime_pow`), so
`R = [R,A] ≤ Ω₁(R) = R₁`. -/
private theorem thm55c_of_pRank_le_two
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (hrank : pRank R p ≤ 2)
    {A : Type*} [Group A] [Finite A] (φ : A →* MulAut R)
    (hφ : Function.Injective φ) (hAodd : Odd (Nat.card A))
    (hq_prime : (Nat.card A).Prime) (hq_ndvd : ¬ Nat.card A ∣ p * (p - 1)) :
    Nat.card A ∣ (p + 1) / 2 ∧
      (OddOrder.Isaacs.Ch04.actionCommutator φ = ⊤ →
        (¬ ∀ x y : R, x * y = y * x) → Nat.card R = p ^ 3) := by
  classical
  have hprime : p.Prime := Fact.out
  have hq_ne_p : Nat.card A ≠ p := by
    intro h
    exact hq_ndvd (h ▸ dvd_mul_right p (p - 1))
  have hSCN : ∀ B : Subgroup R, ¬ OddOrder.GroupTheory.IsSCN₃ p B := by
    intro B hB
    have h3 : 3 ≤ pRank ↥B p := hB.le_pRank
    have hle : pRank ↥B p ≤ pRank R p :=
      pRank_le_of_injective (f := B.subtype) B.subtype_injective
    omega
  have hq_dvd_aut : Nat.card A ∣ Nat.card (MulAut R) := by
    have h1 : Nat.card A = Nat.card φ.range :=
      Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv
    rw [h1]
    exact Subgroup.card_subgroup_dvd_card φ.range
  have h2dvd : (2 : ℕ) ∣ p - 1 := by
    obtain ⟨t, ht⟩ := hp
    exact ⟨t, by omega⟩
  constructor
  · rcases OddOrder.BG.Ch1.S04.dvd_half_prime_add_or_sub_of_prime_dvd_aut_of_scn3_empty
      hp hpg hSCN hq_prime hq_ne_p hq_dvd_aut with h | h
    · exact h
    · exfalso
      have hq_dvd_pm1 : Nat.card A ∣ p - 1 :=
        dvd_trans h ⟨2, (Nat.div_mul_cancel h2dvd).symm⟩
      exact hq_ndvd (Dvd.dvd.mul_left hq_dvd_pm1 p)
  · intro hRA hnab
    have : Nontrivial R := by
      rcases subsingleton_or_nontrivial R with hs | hn
      · exact absurd (fun x y => Subsingleton.elim _ _) hnab
      · exact hn
    have hcop : Nat.Coprime (Nat.card A) (Nat.card R) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
      rw [hn]
      exact Nat.Coprime.pow_right n
        ((Nat.coprime_primes hq_prime hprime).mpr hq_ne_p)
    obtain ⟨hp3, hcase⟩ :=
      OddOrder.BG.Ch1.S04.blackburnRankTwoClassification hp hpg hcop hrank hRA hAodd
    rcases hcase with hcomm | hcp
    · exfalso
      have := hcomm
      exact hnab fun x y => mul_comm x y
    · obtain ⟨R₁, R₂, hcp', hR₁nab, hR₁card, hR₁exp, hR₂cyc, hΩeq⟩ := hcp
      -- `R₁ ⊴ R` (it is centralized by `R₂` and normalized by itself).
      have hR₁_normal : R₁.Normal := by
        rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
        rw [hcp'.sup_eq]
        refine sup_le Subgroup.le_normalizer ?_
        intro g hg
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · intro hx
          have hc : Commute x g := hcp'.commute_of_mem hx hg
          have hfix : g * x * g⁻¹ = x := by
            calc g * x * g⁻¹ = (x * g) * g⁻¹ := by rw [← hc.eq]
              _ = x := by group
          rw [hfix]
          exact hx
        · intro hx
          have hc : Commute (g * x * g⁻¹) g := hcp'.commute_of_mem hx hg
          have hfix : x = g * x * g⁻¹ := by
            calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
              _ = g⁻¹ * ((g * x * g⁻¹) * g) := by group
              _ = g⁻¹ * (g * (g * x * g⁻¹)) := by rw [hc.eq]
              _ = g * x * g⁻¹ := by group
          rw [hfix]
          exact hx
      -- element decomposition along the central product.
      have hdecomp : ∀ x : R, ∃ u ∈ R₁, ∃ v ∈ R₂, x = u * v := by
        intro x
        have hx : x ∈ R₁ ⊔ R₂ := by
          rw [← hcp'.sup_eq]
          exact Subgroup.mem_top x
        have hx' : x ∈ (R₁ : Set R) * (R₂ : Set R) := by
          rw [← Subgroup.normal_mul]
          exact hx
        obtain ⟨u, hu, v, hv, huv⟩ := hx'
        exact ⟨u, hu, v, hv, huv.symm⟩
      -- `Ω₁(R) = R₁`.
      have hΩR : Omega R p 1 = R₁ := by
        apply le_antisymm
        · rw [Omega]
          refine (Subgroup.closure_le _).mpr ?_
          rintro x hx
          rw [Set.mem_ofPred_eq, pow_one] at hx
          obtain ⟨u, hu, v, hv, huv⟩ := hdecomp x
          subst huv
          have hcomm_uv : Commute u v := hcp'.commute_of_mem hu hv
          have hup : u ^ p = 1 := by
            have h1 := Monoid.pow_exponent_eq_one (⟨u, hu⟩ : ↥R₁)
            rw [hR₁exp] at h1
            exact congrArg Subtype.val h1
          have hvp : v ^ p = 1 := by
            have hxp : (u * v) ^ p = u ^ p * v ^ p := hcomm_uv.mul_pow p
            have h1 : u ^ p * v ^ p = 1 := by
              rw [← hxp]
              exact hx
            rw [hup, one_mul] at h1
            exact h1
          have hv_mem : v ∈ (Omega ↥R₂ p 1).map R₂.subtype := by
            refine ⟨⟨v, hv⟩, ?_, rfl⟩
            apply Omega.mem_of_pow_eq_one
            apply Subtype.ext
            change v ^ p ^ 1 = 1
            rw [pow_one]
            exact hvp
          rw [hΩeq] at hv_mem
          exact R₁.mul_mem hu (Subgroup.map_subtype_le _ hv_mem)
        · intro x hx
          apply Omega.mem_of_pow_eq_one
          rw [pow_one]
          have h1 := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : ↥R₁)
          rw [hR₁exp] at h1
          exact congrArg Subtype.val h1
      -- the quotient `R ⧸ Ω₁(R)` is cyclic (image of `R₂`).
      have : (Omega R p 1).Normal := inferInstance
      have hΩ_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ (Omega R p 1) :=
        OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic φ
      have hQcyc : IsCyclic (R ⧸ Omega R p 1) := by
        apply isCyclic_of_surjective
          ((QuotientGroup.mk' (Omega R p 1)).comp R₂.subtype)
        intro q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
        obtain ⟨u, hu, v, hv, huv⟩ := hdecomp x
        refine ⟨⟨v, hv⟩, ?_⟩
        change ((v : R) : R ⧸ Omega R p 1) = ((x : R) : R ⧸ Omega R p 1)
        rw [QuotientGroup.eq, hΩR]
        have hcomm_uv : Commute u v := hcp'.commute_of_mem hu hv
        have hval : v⁻¹ * x = u := by
          rw [huv, hcomm_uv.eq]
          group
        rw [hval]
        exact hu
      -- `A` centralizes the cyclic `p`-group `R ⧸ Ω₁(R)`.
      have hψQ_triv : ∀ a : A, quotientMulAutHom hΩ_inv a = 1 := by
        intro a
        rcases eq_or_ne (quotientMulAutHom hΩ_inv a) 1 with h | hne
        · exact h
        · exfalso
          have ho_dvd_q : orderOf (quotientMulAutHom hΩ_inv a) ∣ Nat.card A :=
            dvd_trans (orderOf_map_dvd _ a) (orderOf_dvd_natCard a)
          have ho_dvd_aut : orderOf (quotientMulAutHom hΩ_inv a) ∣
              Nat.card (MulAut (R ⧸ Omega R p 1)) := orderOf_dvd_natCard _
          rcases (Nat.dvd_prime hq_prime).mp ho_dvd_q with h1 | hq
          · exact hne (orderOf_eq_one_iff.mp h1)
          · rw [hq] at ho_dvd_aut
            obtain ⟨t, ht⟩ := IsPGroup.iff_card.mp (hpg.to_quotient (Omega R p 1))
            rw [IsCyclic.card_mulAut, ht] at ho_dvd_aut
            rcases Nat.eq_zero_or_pos t with ht0 | htpos
            · rw [ht0, pow_zero, Nat.totient_one] at ho_dvd_aut
              exact hq_prime.one_lt.ne' (Nat.dvd_one.mp ho_dvd_aut)
            · rw [Nat.totient_prime_pow hprime htpos] at ho_dvd_aut
              rcases (Nat.Prime.dvd_mul hq_prime).mp ho_dvd_aut with h | h
              · have hqp : Nat.card A ∣ p := hq_prime.dvd_of_dvd_pow h
                rcases (Nat.dvd_prime hprime).mp hqp with h1 | h1
                · exact hq_prime.one_lt.ne' h1
                · exact hq_ne_p h1
              · exact hq_ndvd (Dvd.dvd.mul_left h p)
      -- `[R,A] ≤ Ω₁(R)`, but `[R,A] = R`.
      have hAC_le : OddOrder.Isaacs.Ch04.actionCommutator φ ≤ Omega R p 1 := by
        have hψ_one : quotientMulAutHom hΩ_inv = 1 :=
          MonoidHom.ext fun a => hψQ_triv a
        have hmap : (OddOrder.Isaacs.Ch04.actionCommutator φ).map
            (QuotientGroup.mk' (Omega R p 1)) = ⊥ := by
          rw [← OddOrder.Isaacs.Ch04.actionCommutator_quotient_eq_map hΩ_inv, hψ_one]
          exact OddOrder.Isaacs.Ch04.actionCommutator_one_eq_bot
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap
        exact hmap
      rw [hRA] at hAC_le
      have hΩtop : R₁ = ⊤ := by
        rw [← hΩR]
        exact le_antisymm le_top hAC_le
      calc Nat.card R = Nat.card ↥(⊤ : Subgroup R) := Subgroup.card_top.symm
        _ = Nat.card ↥R₁ := by rw [hΩtop]
        _ = p ^ 3 := hR₁card

/-- **BG Theorem 5.5**: 奇素数 `p`, narrow な有限 `p`-群 `R`, `A` を `R` の自己同型群の solvable
odd 位数部分群 (`φ : A →* MulAut R` faithful, `[Group.IsSolvable A]`, `Odd |A|`) とする。すると:

* (a) `A/O_p(A)` は abelian な `p'`-群,
* (b) `r(R) ≥ 3` なら `A` の各 `p'`-元の位数は `p-1` を割る,
* (c) `|A|` が `p(p-1)` を割らない素数なら `|A| ∣ (p+1)/2`; さらに `R=[R,A]` かつ `R` 非可換なら
  `|R| = p³`。

mmd L1887-1941。Thm 1.13 (critical Ω) + Lem 1.9 (stability) + (rank≤2 で) Lem 4.17/4.14/Thm 4.16
+ **G** Thm 5.4.1。§5 で最も重い結果。 -/
theorem solvableAut_of_narrow [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (hnarrow : IsNarrow p R) {A : Type*} [Group A] [Finite A] (φ : A →* MulAut R)
    (hφ : Function.Injective φ) [Group.IsSolvable A] (hAodd : Odd (Nat.card A)) :
    (∀ x y : A ⧸ Ch01.opCore p A, x * y = y * x) ∧
      ¬ p ∣ Nat.card (A ⧸ Ch01.opCore p A) ∧
    (3 ≤ pRank R p → ∀ a : A, Nat.Coprime (orderOf a) p → orderOf a ∣ (p - 1)) ∧
    ((Nat.card A).Prime → ¬ Nat.card A ∣ p * (p - 1) →
      Nat.card A ∣ (p + 1) / 2 ∧
        (Ch04.actionCommutator φ = ⊤ → (¬ ∀ x y : R, x * y = y * x) → Nat.card R = p ^ 3)) := by
  classical
  by_cases hrank : pRank R p ≤ 2
  · -- `r(R) ≤ 2`: `A'` is a `p`-group by Lemma 4.17; (b) is vacuous; (c) by assembly.
    have hA' : IsPGroup p (_root_.commutator A) :=
      OddOrder.BG.Ch1.S04.isPGroup_commutator_of_mulAut_odd_of_pRank_le_two hp hpg
        hrank hφ hAodd
    obtain ⟨hcomm, hndvd⟩ := quotient_opCore_comm_and_not_dvd_of_isPGroup_commutator hA'
    refine ⟨hcomm, hndvd, ?_, ?_⟩
    · intro h3
      exfalso
      omega
    · intro hq hndvd'
      exact thm55c_of_pRank_le_two hp hpg hrank φ hφ hAodd hq hndvd'
  · -- `r(R) ≥ 3`: chain machinery; the hypotheses of (c) cannot occur.
    have h3 : 3 ≤ pRank R p := by omega
    obtain ⟨S, K, hScard, hKcyc, hSKinf, hCeq⟩ :=
      exists_narrow_witness_of_three_le_pRank h3 hnarrow
    obtain ⟨hA', hb⟩ := isPGroup_commutator_and_orderOf_dvd_of_narrow_witness hp hpg h3
      hScard hKcyc hSKinf hCeq hφ
    obtain ⟨hcomm, hndvd⟩ := quotient_opCore_comm_and_not_dvd_of_isPGroup_commutator hA'
    refine ⟨hcomm, hndvd, fun _ => hb, ?_⟩
    intro hq hndvd'
    exfalso
    have hq_ne_p : Nat.card A ≠ p := by
      intro h
      exact hndvd' (h ▸ dvd_mul_right p (p - 1))
    have : Fact (Nat.card A).Prime := ⟨hq⟩
    obtain ⟨α, hα⟩ := exists_prime_orderOf_dvd_card' (Nat.card A) dvd_rfl
    have hα_cop : Nat.Coprime (orderOf α) p := by
      rw [hα]
      exact (Nat.coprime_primes hq (Fact.out : p.Prime)).mpr hq_ne_p
    have hα_dvd := hb α hα_cop
    rw [hα] at hα_dvd
    exact hndvd' (Dvd.dvd.mul_left hα_dvd p)

end OddOrder.BG.Ch1.S05


