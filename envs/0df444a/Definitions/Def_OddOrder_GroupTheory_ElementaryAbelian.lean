-- Prove2me | Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
-- name    : OddOrder_GroupTheory_ElementaryAbelian
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:44:08.47309+00:00
-- url     : https://prove2.me/theorems/c3d46159-9171-471c-b037-d49b7b504d83
-- title:
--   Elementary abelian groups
-- statement:
--   Introduces the notion of an elementary abelian $p$-group (abelian with $x^p=1$ for all $x$), absent from Mathlib, as a shared concept used by Isaacs Ch. 3 (Thm 3.11), Ch. 6 (6.9/6.15), Ch. 7 (definition of $J(P)$) and, in the future, Bender–Glauberman Appendices A and B (Puig's $L(S)$).
--
--   Main definitions: `IsElementaryAbelian p G` (type-level predicate for a group $G$) and `Subgroup.IsElementaryAbelian` (the same for a subgroup $H\le G$). The prime hypothesis on $p$ is not built into the definition.
--
--   The bundle also proves 23 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/ElementaryAbelian.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/ElementaryAbelian.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Mathlib_Subgroup
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Sylow

open scoped IsMulCommutative

namespace OddOrder.GroupTheory

/-- **Elementary Abelian p-Group** (type-level): `G` is `p`-elementary abelian iff
`G` is abelian and `∀ x : G, x ^ p = 1`. -/
def IsElementaryAbelian (p : ℕ) (G : Type*) [Group G] : Prop :=
  (∀ x y : G, x * y = y * x) ∧ (∀ x : G, x ^ p = 1)

namespace IsElementaryAbelian

variable {p : ℕ} {G : Type*} [Group G]

/-- Commutativity projection. -/
theorem comm (h : IsElementaryAbelian p G) (x y : G) : x * y = y * x := h.1 x y

/-- `p`-th power projection. -/
theorem pow_eq_one (h : IsElementaryAbelian p G) (x : G) : x ^ p = 1 := h.2 x

/-- An elementary abelian `p`-group is a `p`-group. -/
theorem isPGroup (h : IsElementaryAbelian p G) : IsPGroup p G := fun x =>
  ⟨1, by simpa using h.pow_eq_one x⟩

/-- Subgroups of elementary abelian groups are elementary abelian. -/
theorem to_subgroup (h : IsElementaryAbelian p G) (H : Subgroup G) :
    IsElementaryAbelian p H := by
  refine ⟨?_, ?_⟩
  · intro x y
    ext
    exact h.comm (x : G) (y : G)
  · intro x
    ext
    exact h.pow_eq_one (x : G)

/-- **Transport across a group isomorphism**: if `A ≃* B` and `A` is
`p`-elementary abelian, then so is `B`. -/
theorem of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : IsElementaryAbelian p A) : IsElementaryAbelian p B := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · -- commutativity transfers via `e⁻¹`.
    have := h.comm (e.symm x) (e.symm y)
    have h2 := congrArg e this
    simpa using h2
  · -- `x ^ p = 1` transfers via `e⁻¹`.
    have := h.pow_eq_one (e.symm x)
    have h2 := congrArg e this
    simpa using h2

/-- A noncyclic finite group of order `p^2` is elementary abelian. -/
theorem of_card_prime_sq_of_not_isCyclic
    [Finite G] (hp : p.Prime) (hCard : Nat.card G = p ^ 2)
    (hNotCyclic : ¬ IsCyclic G) :
    IsElementaryAbelian p G := by
  let : Fact p.Prime := ⟨hp⟩
  have hExp : Monoid.exponent G = p :=
    (not_isCyclic_iff_exponent_eq_prime hp hCard).mp hNotCyclic
  refine ⟨isMulCommutative_iff.mp
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hCard), ?_⟩
  intro x
  simpa [hExp] using (Monoid.pow_exponent_eq_one x)

/-- A finite elementary abelian group of order `p^2` is not cyclic. -/
theorem not_isCyclic_of_card_prime_sq
    [Finite G] (hp : p.Prime) (h : IsElementaryAbelian p G)
    (hCard : Nat.card G = p ^ 2) :
    ¬ IsCyclic G := by
  intro hcyc
  have : IsCyclic G := hcyc
  have hExp_eq : Monoid.exponent G = Nat.card G := IsCyclic.exponent_eq_card
  have hExp_dvd_p : Monoid.exponent G ∣ p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    exact h.pow_eq_one
  rw [hCard] at hExp_eq
  rw [hExp_eq] at hExp_dvd_p
  have hp_lt_sq : p < p ^ 2 := by
    have hp_pow : p ^ 1 < p ^ 2 :=
      pow_lt_pow_right₀ hp.one_lt (by norm_num : (1 : ℕ) < 2)
    simpa using hp_pow
  exact (Nat.not_dvd_of_pos_of_lt hp.pos hp_lt_sq) hExp_dvd_p

/-- An elementary abelian group of order `p^2` has at least two distinct subgroups of order `p`.
-/
theorem exists_distinct_subgroups_card_prime_of_card_prime_sq
    [Finite G] (hp : p.Prime) (h : IsElementaryAbelian p G)
    (hCard : Nat.card G = p ^ 2) :
    ∃ H K : Subgroup G, Nat.card H = p ∧ Nat.card K = p ∧ H ≠ K := by
  have : Fact p.Prime := ⟨hp⟩
  have hNotCyclic : ¬ IsCyclic G := h.not_isCyclic_of_card_prime_sq hp hCard
  have hCard_gt_one : 1 < Nat.card G := by
    rw [hCard]
    exact one_lt_pow₀ hp.one_lt two_ne_zero
  have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp hCard_gt_one
  obtain ⟨x, hx_ne⟩ := exists_ne (1 : G)
  let H : Subgroup G := Subgroup.zpowers x
  have hx_order : orderOf x = p := orderOf_eq_prime (h.pow_eq_one x) hx_ne
  have hH_card : Nat.card H = p := by
    rw [show H = Subgroup.zpowers x from rfl, Nat.card_zpowers, hx_order]
  have hH_ne_top : H ≠ ⊤ := by
    intro hH_top
    exact hNotCyclic ((isCyclic_iff_exists_zpowers_eq_top (α := G)).mpr ⟨x, hH_top⟩)
  have h_exists_not_mem : ∃ y : G, y ∉ H := by
    by_contra hAll
    apply hH_ne_top
    ext y
    constructor
    · intro hy
      exact Subgroup.mem_top y
    · intro _hy
      by_contra hyH
      exact hAll ⟨y, hyH⟩
  obtain ⟨y, hy_not_mem⟩ := h_exists_not_mem
  let K : Subgroup G := Subgroup.zpowers y
  have hy_ne : y ≠ 1 := by
    intro hy
    exact hy_not_mem (hy ▸ H.one_mem)
  have hy_order : orderOf y = p := orderOf_eq_prime (h.pow_eq_one y) hy_ne
  have hK_card : Nat.card K = p := by
    rw [show K = Subgroup.zpowers y from rfl, Nat.card_zpowers, hy_order]
  refine ⟨H, K, hH_card, hK_card, ?_⟩
  intro hHK
  exact hy_not_mem (hHK ▸ Subgroup.mem_zpowers y)

/-- A finite elementary abelian group of cardinality at least `p^2` contains an elementary
abelian subgroup of order `p^2`. -/
theorem exists_subgroup_card_prime_sq
    [Finite G] (hp : p.Prime) (h : IsElementaryAbelian p G)
    (hCard : p ^ 2 ≤ Nat.card G) :
    ∃ H : Subgroup G, IsElementaryAbelian p H ∧ Nat.card H = p ^ 2 := by
  obtain ⟨H, hH_card⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card (n := 2) hp h.isPGroup hCard
  exact ⟨H, h.to_subgroup H, hH_card⟩

end IsElementaryAbelian

end OddOrder.GroupTheory

namespace IsPGroup

variable {p : ℕ} {G : Type*} [Group G]

open scoped Pointwise

private theorem zmod_prime_power_top_order_prime {p k : ℕ} [Fact p.Prime] (hk : 0 < k) :
    orderOf (Multiplicative.ofAdd ((p ^ (k - 1) : ℕ) : ZMod (p ^ k))) = p := by
  rw [orderOf_ofAdd_eq_addOrderOf]
  rw [ZMod.addOrderOf_coe (p ^ (k - 1)) (pow_ne_zero k (Fact.out : p.Prime).ne_zero)]
  rw [Nat.gcd_eq_right (pow_dvd_pow p (Nat.sub_le k 1))]
  have hpow : p ^ k = p ^ (k - 1) * p := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  rw [hpow]
  exact Nat.mul_div_right _ (pow_pos (Fact.out : p.Prime).pos _)

private theorem zmod_eq_prime_power_top_order_prime {p n k : ℕ} [Fact p.Prime]
    (hn : n = p ^ k) (hk : 0 < k) :
    orderOf (Multiplicative.ofAdd ((p ^ (k - 1) : ℕ) : ZMod n)) = p := by
  subst n
  exact zmod_prime_power_top_order_prime (p := p) (k := k) hk

private theorem isCyclic_pi_of_subsingleton
    {ι : Type*} [Subsingleton ι]
    {M : ι → Type*} [∀ i, Group (M i)] [∀ i, IsCyclic (M i)] :
    IsCyclic (∀ i, M i) := by
  by_cases hι : Nonempty ι
  · classical
    rcases hι with ⟨i⟩
    have : Unique ι := uniqueOfSubsingleton i
    let e : (∀ i, M i) ≃* M default :=
      { toEquiv := Equiv.piUnique M
        map_mul' := fun _ _ => rfl }
    exact e.isCyclic.mpr inferInstance
  · have : IsEmpty ι := ⟨fun i => hι ⟨i⟩⟩
    exact isCyclic_of_subsingleton

/-- A finite commutative `p`-group with at most one subgroup of order `p` is cyclic.

This is the abelian branch used in Isaacs Thm 6.11: in the finite abelian decomposition, two
nontrivial cyclic factors would give two distinct order-`p` subgroups, one in each factor. -/
theorem isCyclic_of_subgroups_card_prime_unique
    [Finite G] [IsMulCommutative G] [Fact p.Prime] (hG : IsPGroup p G)
    (hUnique : ∀ K L : Subgroup G, Nat.card K = p → Nat.card L = p → K = L) :
    IsCyclic G := by
  classical
  obtain ⟨ι, _, n, hn_gt, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  let T := (i : ι) → Multiplicative (ZMod (n i))
  have hn_pow : ∀ i : ι, ∃ k, n i = p ^ k := by
    intro i
    let gen : T := Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod (n i)))
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hG) (e.symm gen)
    refine ⟨k, ?_⟩
    have horder : orderOf (e.symm gen) = n i := by
      rw [← e.orderOf_eq (e.symm gen)]
      simp [gen, orderOf_piMulSingle, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
    exact horder.symm.trans hk
  have hι_sub : Subsingleton ι := by
    by_contra hnot
    have : Nontrivial ι := not_subsingleton_iff_nontrivial.mp hnot
    obtain ⟨i, j, hij⟩ := exists_pair_ne ι
    obtain ⟨ki, hki⟩ := hn_pow i
    obtain ⟨kj, hkj⟩ := hn_pow j
    have hki_pos : 0 < ki := by
      cases ki with
      | zero =>
          have : 1 < (1 : ℕ) := by simpa [hki] using hn_gt i
          omega
      | succ ki => exact Nat.succ_pos _
    have hkj_pos : 0 < kj := by
      cases kj with
      | zero =>
          have : 1 < (1 : ℕ) := by simpa [hkj] using hn_gt j
          omega
      | succ kj => exact Nat.succ_pos _
    let ai : Multiplicative (ZMod (n i)) :=
      Multiplicative.ofAdd ((p ^ (ki - 1) : ℕ) : ZMod (n i))
    let aj : Multiplicative (ZMod (n j)) :=
      Multiplicative.ofAdd ((p ^ (kj - 1) : ℕ) : ZMod (n j))
    have hai_order : orderOf ai = p := by
      simpa [ai] using
        zmod_eq_prime_power_top_order_prime (p := p) (n := n i) (k := ki) hki hki_pos
    have haj_order : orderOf aj = p := by
      simpa [aj] using
        zmod_eq_prime_power_top_order_prime (p := p) (n := n j) (k := kj) hkj hkj_pos
    let xi : T := Pi.mulSingle i ai
    let xj : T := Pi.mulSingle j aj
    have hxi_order : orderOf xi = p := by
      simpa [xi, hai_order] using
        (orderOf_piMulSingle
          (M := fun t : ι => Multiplicative (ZMod (n t))) (i := i) (g := ai))
    have hxj_order : orderOf xj = p := by
      simpa [xj, haj_order] using
        (orderOf_piMulSingle
          (M := fun t : ι => Multiplicative (ZMod (n t))) (i := j) (g := aj))
    let Xi : Subgroup G := Subgroup.zpowers (e.symm xi)
    let Xj : Subgroup G := Subgroup.zpowers (e.symm xj)
    have hXi_card : Nat.card Xi = p := by
      rw [show Xi = Subgroup.zpowers (e.symm xi) from rfl, Nat.card_zpowers]
      rw [← e.orderOf_eq (e.symm xi)]
      simpa using hxi_order
    have hXj_card : Nat.card Xj = p := by
      rw [show Xj = Subgroup.zpowers (e.symm xj) from rfl, Nat.card_zpowers]
      rw [← e.orderOf_eq (e.symm xj)]
      simpa using hxj_order
    have hXiXj : Xi = Xj := hUnique Xi Xj hXi_card hXj_card
    have hmem : e.symm xi ∈ Subgroup.zpowers (e.symm xj) := by
      have hmemXj : e.symm xi ∈ Xj := by
        rw [← hXiXj]
        exact Subgroup.mem_zpowers _
      simpa [Xj] using hmemXj
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hxi_eq : xi = xj ^ m := by
      have := congrArg e hm
      simpa using this.symm
    have hai_ne_one : ai ≠ 1 := by
      intro hai
      have hai_order_one : orderOf ai = 1 := by simp [hai]
      exact (Fact.out : p.Prime).ne_one (hai_order.symm.trans hai_order_one)
    apply hai_ne_one
    have hcoord := congrFun hxi_eq i
    have hxj_i : xj i = 1 := by
      simp [xj, hij]
    have hpow_i : (xj ^ m) i = 1 := by
      rw [Pi.pow_apply, hxj_i]
      simp
    calc
      ai = xi i := by simp [xi]
      _ = (xj ^ m) i := hcoord
      _ = 1 := hpow_i
  have htarget : IsCyclic T := by
    have : Subsingleton ι := hι_sub
    exact isCyclic_pi_of_subsingleton
  exact e.isCyclic.mpr htarget

/-- If a finite `p`-group has at most one subgroup of order `p`, then every commutative
subgroup is cyclic.

This is the bridge used before Isaacs Thm 6.12: the ambient uniqueness hypothesis descends to
each abelian subgroup by mapping its order-`p` subgroups back into the ambient group. -/
theorem isCyclic_subgroup_of_subgroups_card_prime_unique
    [Finite G] [Fact p.Prime] (hG : IsPGroup p G)
    (hUnique : ∀ K L : Subgroup G, Nat.card K = p → Nat.card L = p → K = L)
    (H : Subgroup G) [IsMulCommutative H] :
    IsCyclic H := by
  apply (hG.to_subgroup H).isCyclic_of_subgroups_card_prime_unique
  intro K L hK_card hL_card
  have hK_map_card : Nat.card (K.map H.subtype) = p := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hK_card]
  have hL_map_card : Nat.card (L.map H.subtype) = p := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hL_card]
  exact Subgroup.map_injective H.subtype_injective
    (hUnique (K.map H.subtype) (L.map H.subtype) hK_map_card hL_map_card)

/-- A noncyclic finite `p`-group of order at most `p²` is elementary abelian of order `p²`.

This is the small-order reduction used in Isaacs Thm 7.5 after quotienting to
`|V : U| ≤ p²`: the cyclic cases have order `1` or `p`, so a noncyclic `p`-group must have
exactly order `p²`, where the prime-square classification makes it elementary abelian. -/
theorem isElementaryAbelian_card_prime_sq_of_card_le_prime_sq_of_not_isCyclic
    [Finite G] [Fact p.Prime] (hG : IsPGroup p G)
    (hCard_le : Nat.card G ≤ p ^ 2) (hNotCyclic : ¬ IsCyclic G) :
    OddOrder.GroupTheory.IsElementaryAbelian p G ∧ Nat.card G = p ^ 2 := by
  obtain ⟨n, hcard⟩ := IsPGroup.iff_card.mp hG
  have hp : p.Prime := Fact.out
  have hn_ge_two : 2 ≤ n := by
    by_contra hnot
    have hn_lt_two : n < 2 := Nat.lt_of_not_ge hnot
    have hcyc : IsCyclic G := by
      interval_cases n
      · have hcard_one : Nat.card G = 1 := by
          simpa using hcard
        exact @isCyclic_of_subsingleton G _ (Nat.card_eq_one_iff_unique.mp hcard_one).1
      · have hcard_p : Nat.card G = p := by
          simpa using hcard
        exact isCyclic_of_prime_card hcard_p
    exact hNotCyclic hcyc
  have hn_le_two : n ≤ 2 := by
    by_contra hnot
    have hthree_le : 3 ≤ n := by omega
    have hpow_le : p ^ 3 ≤ p ^ n :=
      pow_le_pow_right₀ hp.one_lt.le hthree_le
    have hp_sq_lt_cube : p ^ 2 < p ^ 3 :=
      pow_lt_pow_right₀ hp.one_lt (by norm_num : (2 : ℕ) < 3)
    have hcube_le_sq : p ^ 3 ≤ p ^ 2 := by
      calc
        p ^ 3 ≤ p ^ n := hpow_le
        _ = Nat.card G := hcard.symm
        _ ≤ p ^ 2 := hCard_le
    exact (not_lt_of_ge hcube_le_sq) hp_sq_lt_cube
  have hn_eq_two : n = 2 := le_antisymm hn_le_two hn_ge_two
  have hCard : Nat.card G = p ^ 2 := by
    simpa [hn_eq_two] using hcard
  exact ⟨OddOrder.GroupTheory.IsElementaryAbelian.of_card_prime_sq_of_not_isCyclic
    hp hCard hNotCyclic, hCard⟩

private theorem subgroup_normal_of_le_center {H : Subgroup G} (hH : H ≤ Subgroup.center G) :
    H.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn_center : n ∈ Subgroup.center G := hH hn
  have hgn : g * n = n * g := Subgroup.mem_center_iff.mp hn_center g
  have hconj : g * n * g⁻¹ = n := by
    calc
      g * n * g⁻¹ = n * g * g⁻¹ := by rw [hgn]
      _ = n := by simp
  rwa [hconj]

/-- A nontrivial finite `p`-group contains a central subgroup of order `p`. -/
theorem exists_subgroup_le_center_card_prime
    [Finite G] [Fact p.Prime] (hG : IsPGroup p G) [Nontrivial G] :
    ∃ Z : Subgroup G, Z ≤ Subgroup.center G ∧ Nat.card Z = p := by
  have hCenter_nontrivial : Nontrivial (Subgroup.center G) := hG.center_nontrivial
  have hCenter_card_gt : 1 < Nat.card (Subgroup.center G) :=
    Finite.one_lt_card_iff_nontrivial.mpr hCenter_nontrivial
  have hCenter_pgroup : IsPGroup p (Subgroup.center G) := hG.to_subgroup _
  have hp_dvd_center : p ∣ Nat.card (Subgroup.center G) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hCenter_pgroup
    rw [hn] at hCenter_card_gt ⊢
    have hn_pos : 0 < n := by
      cases n with
      | zero =>
          simp at hCenter_card_gt
      | succ n =>
          exact Nat.succ_pos n
    exact dvd_pow_self p hn_pos.ne'
  obtain ⟨z, hz_order⟩ :=
    exists_prime_orderOf_dvd_card' (G := Subgroup.center G) p hp_dvd_center
  let Z : Subgroup G := Subgroup.zpowers (z : G)
  have hZ_le_center : Z ≤ Subgroup.center G := Subgroup.zpowers_le.mpr z.2
  have hZ_card : Nat.card Z = p := by
    rw [show Z = Subgroup.zpowers (z : G) from rfl, Nat.card_zpowers]
    exact (Subgroup.orderOf_coe z).trans hz_order
  exact ⟨Z, hZ_le_center, hZ_card⟩

/-- If a finite `p`-group has two distinct subgroups of order `p`, then it contains an
elementary abelian subgroup of order `p^2`. -/
theorem exists_isElementaryAbelian_card_prime_sq_of_subgroups_card_prime_ne
    [Finite G] [Fact p.Prime] (hG : IsPGroup p G)
    {K L : Subgroup G} (hK_card : Nat.card K = p) (hL_card : Nat.card L = p)
    (hKL_ne : K ≠ L) :
    ∃ E : Subgroup G, OddOrder.GroupTheory.IsElementaryAbelian p E ∧ Nat.card E = p ^ 2 := by
  classical
  have : Nontrivial K := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [hK_card]
    exact (Fact.out : p.Prime).one_lt
  obtain ⟨k, hk_ne⟩ := exists_ne (1 : K)
  have : Nontrivial G := ⟨⟨(k : G), 1, fun hk => hk_ne (Subtype.ext hk)⟩⟩
  obtain ⟨Z, hZ_le_center, hZ_card⟩ := hG.exists_subgroup_le_center_card_prime
  let U : Subgroup G := if Z = K then L else K
  have hU_card : Nat.card U = p := by
    by_cases hZK : Z = K
    · simp [U, hZK, hL_card]
    · simp [U, hZK, hK_card]
  have hZU_ne : Z ≠ U := by
    by_cases hZK : Z = K
    · simp [U, hZK, hKL_ne]
    · simp [U, hZK]
  have hInf_bot : Z ⊓ U = ⊥ := by
    have hInf_dvd : Nat.card (Z ⊓ U : Subgroup G) ∣ p := by
      rw [← hU_card]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Fact.out).mp hInf_dvd with hInf_card | hInf_card
    · exact Subgroup.eq_bot_of_card_eq _ hInf_card
    · exfalso
      have hInf_eq_Z : Z ⊓ U = Z :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hInf_card, hZ_card])
      have hInf_eq_U : Z ⊓ U = U :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hInf_card, hU_card])
      exact hZU_ne (hInf_eq_Z.symm.trans hInf_eq_U)
  have hZ_normal : Z.Normal := subgroup_normal_of_le_center hZ_le_center
  let E : Subgroup G := Z ⊔ U
  have hE_card : Nat.card E = p ^ 2 := by
    have hcard := Subgroup.card_HK_mul_card_inf_eq_card_mul_card Z U
    rw [← Subgroup.normal_mul Z U, hInf_bot, Subgroup.card_bot, hZ_card, hU_card, mul_one] at hcard
    simpa [E, pow_two] using hcard
  have hE_set : (E : Set G) = (Z : Set G) * (U : Set G) := by
    simpa [E] using (Subgroup.normal_mul Z U)
  have hZ_pow : ∀ z ∈ Z, z ^ p = 1 := by
    intro z hz
    have hz_pow := pow_card_eq_one' (G := Z) (x := (⟨z, hz⟩ : Z))
    have hz_pow_coe := congrArg Subtype.val hz_pow
    simpa [hZ_card] using hz_pow_coe
  have hU_pow : ∀ u ∈ U, u ^ p = 1 := by
    intro u hu
    have hu_pow := pow_card_eq_one' (G := U) (x := (⟨u, hu⟩ : U))
    have hu_pow_coe := congrArg Subtype.val hu_pow
    simpa [hU_card] using hu_pow_coe
  have hZ_comm : ∀ z ∈ Z, ∀ g : G, z * g = g * z := by
    intro z hz g
    exact (Subgroup.mem_center_iff.mp (hZ_le_center hz) g).symm
  have hU_comm : ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ * u₂ = u₂ * u₁ := by
    have : IsCyclic U := isCyclic_of_prime_card hU_card
    let : CommGroup U := IsCyclic.commGroup
    intro u₁ hu₁ u₂ hu₂
    have hcomm : (⟨u₁, hu₁⟩ : U) * ⟨u₂, hu₂⟩ = ⟨u₂, hu₂⟩ * ⟨u₁, hu₁⟩ :=
      mul_comm _ _
    exact congrArg Subtype.val hcomm
  refine ⟨E, ?_, hE_card⟩
  constructor
  · intro x y
    obtain ⟨zx, hzx, ux, hux, hx_prod⟩ : ∃ zx ∈ Z, ∃ ux ∈ U, zx * ux = (x : G) := by
      have hx_mem : (x : G) ∈ (Z : Set G) * (U : Set G) := by
        rw [← hE_set]
        exact x.2
      simpa only [Set.mem_mul, SetLike.mem_coe] using hx_mem
    obtain ⟨zy, hzy, uy, huy, hy_prod⟩ : ∃ zy ∈ Z, ∃ uy ∈ U, zy * uy = (y : G) := by
      have hy_mem : (y : G) ∈ (Z : Set G) * (U : Set G) := by
        rw [← hE_set]
        exact y.2
      simpa only [Set.mem_mul, SetLike.mem_coe] using hy_mem
    apply Subtype.ext
    change (x : G) * (y : G) = (y : G) * (x : G)
    rw [← hx_prod, ← hy_prod]
    have hux_zy : Commute ux zy := (hZ_comm zy hzy ux).symm
    have hzx_zy : Commute zx zy := hZ_comm zx hzx zy
    have hux_uy : Commute ux uy := hU_comm ux hux uy huy
    have hzx_uy : Commute zx uy := hZ_comm zx hzx uy
    calc
      (zx * ux) * (zy * uy) = zx * ux * (zy * uy) := by rw [mul_assoc]
      _ = zx * zy * (ux * uy) := hux_zy.mul_mul_mul_comm zx uy
      _ = zy * zx * (uy * ux) := by rw [hzx_zy.eq, hux_uy.eq]
      _ = zy * uy * (zx * ux) := hzx_uy.mul_mul_mul_comm zy ux
      _ = (zy * uy) * (zx * ux) := by rw [mul_assoc]
  · intro x
    obtain ⟨z, hz, u, hu, hx_prod⟩ : ∃ z ∈ Z, ∃ u ∈ U, z * u = (x : G) := by
      have hx_mem : (x : G) ∈ (Z : Set G) * (U : Set G) := by
        rw [← hE_set]
        exact x.2
      simpa only [Set.mem_mul, SetLike.mem_coe] using hx_mem
    apply Subtype.ext
    change ((x : G) ^ p) = 1
    rw [← hx_prod]
    have hzu : Commute z u := hZ_comm z hz u
    rw [hzu.mul_pow, hZ_pow z hz, hU_pow u hu, one_mul]

end IsPGroup

namespace Subgroup

variable {G : Type*} [Group G]

/-- **Subgroup is Elementary Abelian**: subgroup `H ≤ G` is `p`-elementary abelian iff
the subtype `↥H` is `p`-elementary abelian as a group. -/
def IsElementaryAbelian (H : Subgroup G) (p : ℕ) : Prop :=
  OddOrder.GroupTheory.IsElementaryAbelian p ↥H

/-- The image `H.map f` of an elementary abelian subgroup under an *injective*
homomorphism is elementary abelian (via `↥H ≃* ↥(H.map f)`). -/
theorem IsElementaryAbelian.map {p : ℕ} {N : Type*} [Group N] {H : Subgroup G}
    {f : G →* N} (hf : Function.Injective f) (hH : H.IsElementaryAbelian p) :
    (H.map f).IsElementaryAbelian p :=
  OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
    (Subgroup.equivMapOfInjective H f hf) hH

/-- Pulling back along an injective hom: if `H.map f` is elementary abelian, so
is `H` (via the same iso `↥H ≃* ↥(H.map f)`). -/
theorem IsElementaryAbelian.of_map {p : ℕ} {N : Type*} [Group N] {H : Subgroup G}
    {f : G →* N} (hf : Function.Injective f) (hH : (H.map f).IsElementaryAbelian p) :
    H.IsElementaryAbelian p :=
  OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
    (Subgroup.equivMapOfInjective H f hf).symm hH

/-- A finite subgroup of prime order is elementary abelian. -/
theorem IsElementaryAbelian.of_card_prime {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    [Finite H] (hH : Nat.card H = p) :
    H.IsElementaryAbelian p := by
  have hHcyc : IsCyclic H := isCyclic_of_prime_card hH
  constructor
  · have : IsCyclic H := hHcyc
    let : CommGroup H := IsCyclic.commGroup
    intro x y
    exact mul_comm x y
  · intro x
    have hx := pow_card_eq_one' (G := H) (x := x)
    simpa [hH] using hx

/-- The join of two elementary abelian subgroups is elementary abelian when the two
subgroups centralize each other. -/
theorem IsElementaryAbelian.sup_of_le_centralizer {p : ℕ} {H K : Subgroup G}
    (hH : H.IsElementaryAbelian p) (hK : K.IsElementaryAbelian p)
    (hHK : H ≤ Subgroup.centralizer (K : Set G)) :
    (H ⊔ K).IsElementaryAbelian p := by
  let S : Set G := (H : Set G) ∪ (K : Set G)
  have hsup_closure : H ⊔ K = Subgroup.closure S := by
    dsimp [S]
    rw [Subgroup.closure_union, H.closure_eq, K.closure_eq]
  have hgen_comm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    rcases hx with hxH | hxK
    · rcases hy with hyH | hyK
      · exact congrArg Subtype.val (hH.comm ⟨x, hxH⟩ ⟨y, hyH⟩)
      · exact (hHK hxH y hyK).symm
    · rcases hy with hyH | hyK
      · exact hHK hyH x hxK
      · exact congrArg Subtype.val (hK.comm ⟨x, hxK⟩ ⟨y, hyK⟩)
  have hclosure_comm : IsMulCommutative (Subgroup.closure S) :=
    Subgroup.isMulCommutative_closure hgen_comm
  refine ⟨?_, ?_⟩
  · intro x y
    have hx : (x : G) ∈ Subgroup.closure S := by
      rw [← hsup_closure]
      exact x.2
    have hy : (y : G) ∈ Subgroup.closure S := by
      rw [← hsup_closure]
      exact y.2
    let : IsMulCommutative (Subgroup.closure S) := hclosure_comm
    apply Subtype.ext
    change (x : G) * (y : G) = (y : G) * (x : G)
    simpa using congrArg (fun z : Subgroup.closure S => (z : G))
      (mul_comm (⟨(x : G), hx⟩ : Subgroup.closure S) ⟨(y : G), hy⟩)
  · intro x
    have hx : (x : G) ∈ Subgroup.closure S := by
      rw [← hsup_closure]
      exact x.2
    apply Subtype.ext
    change ((x : G) ^ p = 1)
    refine Subgroup.closure_induction (p := fun g _ => g ^ p = 1) ?_ ?_ ?_ ?_ hx
    · intro g hg
      rcases hg with hgH | hgK
      · exact congrArg Subtype.val (hH.pow_eq_one ⟨g, hgH⟩)
      · exact congrArg Subtype.val (hK.pow_eq_one ⟨g, hgK⟩)
    · simp
    · intro a b ha hb hap hbp
      let : IsMulCommutative (Subgroup.closure S) := hclosure_comm
      have hab_eq : a * b = b * a := by
        exact congrArg Subtype.val
          (mul_comm (⟨a, ha⟩ : Subgroup.closure S) ⟨b, hb⟩)
      have hab : Commute a b := hab_eq
      rw [hab.mul_pow p, hap, hbp, one_mul]
    · intro a ha hap
      simpa [inv_pow] using congrArg Inv.inv hap

/-- An elementary abelian subgroup of order `p^2` contains two distinct ambient subgroups of
order `p`. -/
theorem exists_distinct_subgroups_card_prime_of_isElementaryAbelian_card_prime_sq
    {H : Subgroup G} [Finite H] {p : ℕ} (hp : p.Prime)
    (hH : H.IsElementaryAbelian p) (hCard : Nat.card H = p ^ 2) :
    ∃ K L : Subgroup G, K ≤ H ∧ L ≤ H ∧
      Nat.card K = p ∧ Nat.card L = p ∧ K ≠ L := by
  obtain ⟨K₀, L₀, hK₀_card, hL₀_card, hK₀L₀_ne⟩ :=
    hH.exists_distinct_subgroups_card_prime_of_card_prime_sq hp hCard
  let K : Subgroup G := K₀.map H.subtype
  let L : Subgroup G := L₀.map H.subtype
  have hK_card : Nat.card K = p := by
    rw [show K = K₀.map H.subtype from rfl,
      Subgroup.card_map_of_injective H.subtype_injective, hK₀_card]
  have hL_card : Nat.card L = p := by
    rw [show L = L₀.map H.subtype from rfl,
      Subgroup.card_map_of_injective H.subtype_injective, hL₀_card]
  have hKL_ne : K ≠ L := by
    intro hKL
    exact hK₀L₀_ne (Subgroup.map_injective H.subtype_injective hKL)
  exact ⟨K, L, Subgroup.map_subtype_le K₀, Subgroup.map_subtype_le L₀,
    hK_card, hL_card, hKL_ne⟩

end Subgroup


