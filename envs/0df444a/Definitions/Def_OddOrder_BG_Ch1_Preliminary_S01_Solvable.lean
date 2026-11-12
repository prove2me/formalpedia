-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S01_Solvable
-- name    : OddOrder_BG_Ch1_Preliminary_S01_Solvable
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:41:38.659195+00:00
-- url     : https://prove2.me/theorems/9ec4a3d4-a97d-412a-80d0-73be6a75f2db
-- title:
--   Bender–Glauberman §1D–§1G: Thompson's critical subgroup theorem and tail of §1
-- statement:
--   The tail of Bender–Glauberman §1 (Thm 1.11–1.13, Lem 1.14–1.16, Thm 1.17–1.20, Lem 1.21–1.22), including Thompson's Theorem 1.13 and Corollary 1.12 on elementary abelian subgroups of $p$-groups for odd $p$.
--
--   Main definitions: `thompson_critical_omega` (BG Theorem 1.13, J. G. Thompson), `corollary_1_12` (BG Corollary 1.12), and `oPiPrimePiPiPrimeCore` (the BG subgroup $O_{\pi',\pi,\pi'}(G)$, shown normal).
--
--   The bundle also proves 14 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S01_BurnsideOperator

namespace OddOrder.BG.Ch1.S01

open OddOrder.Isaacs.Ch01

open Pointwise

open OddOrder.GroupTheory in
/-- **BG Theorem 1.13** (J. G. Thompson) — `references/bg/local-analysis.mmd:461`.
**Gorenstein "Finite Groups" Theorem 5.3.13** (p. 186) の Lean 化.

`p` が奇素数で `G` が非自明な `p`-群ならば, `G` は次の四性質を持つ characteristic
subgroup `H` (= ある critical subgroup `C` の `Ω₁(C)`) を含む:

* (a) `[H, G] ⊆ Z(H)`;
* (b) `H` の nilpotence class は `≤ 2` (`commutator ↥H ≤ Z(↥H)`);
* (c) `H` の exponent は `p`;
* (d) `C_{Aut G}(H)` (= `H` を pointwise に固定する `Aut G` の部分群) は `p`-群.

証明: `isCritical_exists` で critical subgroup `C` を取り `H = Ω₁(C)`
(`omega1Map C p`) とする. (a)=`commutator_top_le_center_omega1Map` (BG L468 の
三段包含), (b)=`omega1Map_class_le_two` (`H ≤ C` から継承), (c)=`exponent_omega1Map`
(Gorenstein 5.3.9(i)), (d)=`isPGroup_autCentralizer_omega1Map` (Gorenstein 5.3.10
で `Ω₁(C)` 固定 ⇒ `C` 上自明, 5.3.11(iv) で `G` 上自明). characteristic は
`omega1Map_characteristic` (char-in-char). -/
theorem thompson_critical_omega {G : Type*} [Group G] [Finite G] [Nontrivial G]
    {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2) (hG : IsPGroup p G) :
    ∃ H : Subgroup G,
      H.Characteristic
      ∧ ⁅H, (⊤ : Subgroup G)⁆ ≤ (Subgroup.center ↥H).map H.subtype
      ∧ _root_.commutator ↥H ≤ Subgroup.center ↥H
      ∧ Monoid.exponent ↥H = p
      ∧ IsPGroup p (autCentralizer H) := by
  obtain ⟨C, hC⟩ := isCritical_exists hG
  refine ⟨omega1Map C p, hC.omega1Map_characteristic, ?_,
    hC.omega1Map_class_le_two, hC.exponent_omega1Map hp_odd hG,
    hC.isPGroup_autCentralizer_omega1Map hp_odd hG⟩
  -- (a) `[H, G] ⊆ Z(H)` from the symmetric `[G, H]` via `commutator_comm`.
  rw [Subgroup.commutator_comm]
  exact hC.commutator_top_le_center_omega1Map

open OddOrder.Isaacs.Ch03 (IsAInvariant) in
/-- **BG Corollary 1.12** (mmd L457): `p` odd, `G` a `p`-group, `E` an elementary abelian
subgroup, `A` a `p'`-group of operators on `G` (via `φ : A →* MulAut G`). If `A` fixes every
order-`p` element of `C_G(E)`, then `A` acts trivially on `G`.

**証明** (BG): `C := C_G(A)` (`fixedPointsOfMulAut φ`) とおく.
- `E ⊆ C`: `E` の各元 `e` は `E` を中心化し (`E` abelian) かつ `eᵖ = 1` (`E` elementary
  abelian) なので, `e ∈ C_G(E)` の order-`p` 元として仮定 `h_fix` で `A` に固定される,
  すなわち `e ∈ C`.
- `D := C_G(C)` は `A`-不変 (`IsAInvariant.centralizer`) で, `E ⊆ C` より `D ⊆ C_G(E)`
  (centralizer の反単調性). `D` は `G` の部分群として `p`-群 (`hG.to_subgroup`).
- `D` の order-`p` 元 `ḡ` は `(ḡ : G) ∈ D ⊆ C_G(E)` で `(ḡ)ᵖ = 1` ゆえ `h_fix` で `A` に固定;
  ゆえに `restrictAction` 経由の `↥D` 上作用は全 order-`p` 元を固定. BG Thm 1.11 = Isaacs
  Thm 4.36 (`isaacs_thm_4_36`) を `↥D` 上の制限作用に適用すると `A` は `↥D` 上自明に作用し,
  これは `D ⊆ C`, すなわち `C_G(C) ⊆ C` を与える.
- 最後に `G` は冪零 (`hG.isNilpotent`), `(|A|, |G|) = 1`, `C_G(C) ⊆ C` の三条件で BG
  Prop 1.10 (`coprime_nilpotent_acts_trivially_of_centralizer_self`) を適用し結論. -/
theorem corollary_1_12 {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2) (hG : IsPGroup p G) (hA_p' : ¬ p ∣ Nat.card A)
    (φ : A →* MulAut G) {E : Subgroup G} (hE : E.IsElementaryAbelian p)
    (h_fix : ∀ g : G, g ∈ Subgroup.centralizer (E : Set G) → g ^ p = 1 → ∀ a : A, (φ a) g = g) :
    ∀ a : A, ∀ g : G, (φ a) g = g := by
  set C := Subgroup.fixedPointsOfMulAut φ with hC
  -- `C` is `A`-invariant (fixed pointwise), as in Prop 1.10.
  have hC_inv : IsAInvariant φ C := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a g hg
    rw [hC, Subgroup.mem_fixedPointsOfMulAut] at hg ⊢
    intro a'
    rw [hg a, hg a']
  -- Step 1: `E ≤ C`.
  have hE_le_C : E ≤ C := by
    intro e he
    rw [hC, Subgroup.mem_fixedPointsOfMulAut]
    -- `e ∈ C_G(E)`: `e` commutes with every element of `E` (`E` abelian).
    have he_cent : e ∈ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [SetLike.mem_coe] at hy
      have := hE.comm ⟨e, he⟩ ⟨y, hy⟩
      exact congrArg Subtype.val this.symm
    -- `e ^ p = 1` (`E` elementary abelian).
    have he_pow : e ^ p = 1 := by
      have h := congrArg (fun x : ↥E => (x : G)) (hE.pow_eq_one ⟨e, he⟩)
      simpa using h
    exact h_fix e he_cent he_pow
  -- Step 2/3: `D := C_G(C)` is `A`-invariant and `D ≤ C_G(E)`.
  set D := Subgroup.centralizer (C : Set G) with hD
  have hD_inv : IsAInvariant φ D := hC_inv.centralizer
  have hD_le_cE : D ≤ Subgroup.centralizer (E : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hE_le_C)
  -- `D` is a `p`-group (subgroup of the `p`-group `G`).
  have hD_pgroup : IsPGroup p ↥D := hG.to_subgroup D
  -- Step 4: every order-`p` element of `↥D` is fixed by the restricted action.
  have h_fixD : ∀ x : ↥D, x ^ p = 1 → ∀ a : A, (restrictAction hD_inv a) x = x := by
    intro x hpow a
    have hgD : (x : G) ∈ D := x.2
    have hg_cent : (x : G) ∈ Subgroup.centralizer (E : Set G) := hD_le_cE hgD
    have hg_pow : (x : G) ^ p = 1 := by
      have h := congrArg (fun y : ↥D => (y : G)) hpow
      simpa using h
    apply Subtype.ext
    rw [restrictAction_apply]
    exact h_fix (x : G) hg_cent hg_pow a
  -- Apply BG Thm 1.11 = Isaacs Thm 4.36 to the restricted action on `↥D`.
  have hAC : OddOrder.Isaacs.Ch04.actionCommutator (restrictAction hD_inv) = ⊥ :=
    OddOrder.Isaacs.Ch04.isaacs_thm_4_36 hp_odd (restrictAction hD_inv) hD_pgroup hA_p' h_fixD
  have hTrivD : ∀ a : A, ∀ x : ↥D, (restrictAction hD_inv a) x = x :=
    (OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_iff_acts_trivially (restrictAction hD_inv)).mp hAC
  -- `D ≤ C`, i.e. `C_G(C) ⊆ C`.
  have hCC : Subgroup.centralizer (C : Set G) ≤ C := by
    intro g hg
    rw [hC, Subgroup.mem_fixedPointsOfMulAut]
    intro a
    have := hTrivD a ⟨g, hg⟩
    have h2 := congrArg Subtype.val this
    rwa [restrictAction_apply] at h2
  -- Step 5: conclude via BG Prop 1.10.
  have : Group.IsNilpotent G := hG.isNilpotent
  have hCop : Nat.Coprime (Nat.card A) (Nat.card G) := by
    obtain ⟨n, hn⟩ := hG.exists_card_eq
    rw [hn]
    exact (((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hA_p').symm).pow_right n
  exact coprime_nilpotent_acts_trivially_of_centralizer_self hCop hCC

/-- **Helper for Lem 1.14**: T p-group + M p'-group ⇒ `T ⊓ M = ⊥`.

`T ⊓ M` は T の subgroup として p-group (`hT.of_injective Subgroup.inclusion`) かつ
|T ⊓ M| ∣ |M|. |M| が p と coprime ⇒ p^k ∣ |M| ⇒ k = 0 ⇒ |T ⊓ M| = 1 ⇒ T ⊓ M = ⊥. -/
theorem inf_eq_bot_of_pGroup_coprime
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T : Subgroup G} (hT : IsPGroup p T)
    {M : Subgroup G} (hM_p' : (Nat.card M).Coprime p) :
    T ⊓ M = ⊥ := by
  have hTM_le_T : T ⊓ M ≤ T := inf_le_left
  have hTM_le_M : T ⊓ M ≤ M := inf_le_right
  have hTM_pgroup : IsPGroup p (T ⊓ M : Subgroup G) :=
    hT.of_injective (Subgroup.inclusion hTM_le_T) (Subgroup.inclusion_injective hTM_le_T)
  have hcard_dvd : Nat.card (T ⊓ M : Subgroup G) ∣ Nat.card M :=
    Subgroup.card_dvd_of_le hTM_le_M
  obtain ⟨k, hk⟩ := hTM_pgroup.exists_card_eq
  rw [hk] at hcard_dvd
  -- p^k ∣ |M| and (|M|, p) = 1 ⇒ p^k = 1
  have hcop_pow : ((p ^ k).Coprime (Nat.card M)) := (hM_p'.symm).pow_left k
  have hpow_eq_one : p ^ k = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop_pow dvd_rfl hcard_dvd
  rw [hpow_eq_one] at hk
  exact Subgroup.eq_bot_of_card_eq _ hk

/-- **Helper for Lem 1.14** (Step 2, cardinality): `T ⊓ M = ⊥` + `M ⊴ G` ⇒
`|T ⊔ M| = |T| · |M|`. mathlib 第二同型 `quotientInfEquivProdNormalQuotient` +
`subgroupOfEquivOfLe` + `card_eq_card_quotient_mul_card_subgroup`. -/
theorem card_sup_eq_card_mul_card_of_disjoint_normal
    {G : Type*} [Group G] [Finite G]
    {T M : Subgroup G} [M.Normal] (h_disj : T ⊓ M = ⊥) :
    Nat.card (T ⊔ M : Subgroup G) = Nat.card T * Nat.card M := by
  -- Step A: M.subgroupOf T = ⊥ (from T ⊓ M = ⊥)
  have hMT_bot : M.subgroupOf T = ⊥ := by
    rw [Subgroup.subgroupOf_eq_bot, Subgroup.disjoint_def]
    intro x hxM hxT
    have hx_inf : x ∈ T ⊓ M := Subgroup.mem_inf.mpr ⟨hxT, hxM⟩
    rwa [h_disj, Subgroup.mem_bot] at hx_inf
  -- |M.subgroupOf T| = 1
  have hMT_card_one : Nat.card (M.subgroupOf T) = 1 := by
    rw [hMT_bot]; exact Subgroup.card_bot
  -- |T| = |T ⧸ M.subgroupOf T| * |M.subgroupOf T| = |T ⧸ M.subgroupOf T|
  have hT_quot_card : Nat.card T = Nat.card (T ⧸ M.subgroupOf T) := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (M.subgroupOf T)
    rw [hMT_card_one, mul_one] at this
    exact this
  -- Second iso theorem: T ⧸ M.subgroupOf T ≃* (T ⊔ M) ⧸ M.subgroupOf (T ⊔ M)
  have h_iso := QuotientGroup.quotientInfEquivProdNormalQuotient T M
  have h_eq_TM : Nat.card ((T ⊔ M : Subgroup G) ⧸ (M.subgroupOf (T ⊔ M))) = Nat.card T := by
    rw [hT_quot_card]
    exact (Nat.card_congr h_iso.toEquiv).symm
  -- |M.subgroupOf (T ⊔ M)| = |M|
  have hM_sub_TM_card : Nat.card (M.subgroupOf (T ⊔ M : Subgroup G)) = Nat.card M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : M ≤ T ⊔ M)).toEquiv
  -- |T ⊔ M| = |quotient| · |M.subgroupOf (T ⊔ M)| = |T| · |M|
  have h_card : Nat.card ↥(T ⊔ M : Subgroup G) =
      Nat.card ((T ⊔ M : Subgroup G) ⧸ (M.subgroupOf (T ⊔ M))) *
      Nat.card (M.subgroupOf (T ⊔ M : Subgroup G)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [h_card, h_eq_TM, hM_sub_TM_card]

/-- **Helper for Lem 1.14** (Step 3 part 1): `T.subgroupOf (T ⊔ M)` is a p-group with
cardinality `|T|`. uses `Subgroup.subgroupOfEquivOfLe` (T ≤ T ⊔ M ⇒ T.subgroupOf (T⊔M) ≃* T). -/
theorem subgroupOf_sup_card_eq_and_pGroup
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T : Subgroup G} (hT : IsPGroup p T) (M : Subgroup G) :
    Nat.card (T.subgroupOf (T ⊔ M)) = Nat.card T ∧
      IsPGroup p (T.subgroupOf (T ⊔ M : Subgroup G)) := by
  refine ⟨?_, ?_⟩
  · exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : T ≤ T ⊔ M)).toEquiv
  · exact hT.of_injective (Subgroup.subgroupOfEquivOfLe (le_sup_left : T ≤ T ⊔ M)).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : T ≤ T ⊔ M)).injective

/-- **Helper for Lem 1.14** (Step 3 part 2 一般版, Sylow 性): 任意の `S ≤ T ⊔ M` で
`|S| = |T|` ⇒ `S.subgroupOf (T ⊔ M)` は ↥(T ⊔ M) の Sylow p (Q ≥ S.subgroupOf + Q p-group
⇒ Q = S.subgroupOf).

`S = T` の場合 `subgroupOf_sup_eq_of_pGroup_le_of_coprime` (corollary 下記),
`S = xTx⁻¹` (T_x) の場合 Lem 1.14 main proof 内の T_xSyl 構築で使用.

証明: |Q| = p^j ∣ |T ⊔ M| = |T| · |M| with (|M|, p) = 1 ⇒ p^j ∣ p^k = |T|.
`S.subgroupOf ≤ Q` + `|S.subgroupOf| = |S| = |T| = p^k` ⇒ k ≤ j. 両方合わせて j = k,
|Q| = |S.subgroupOf|. `Subgroup.eq_of_le_of_card_ge` で等号. -/
theorem subgroupOf_sup_eq_of_pGroup_le_of_card_eq
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T : Subgroup G} (hT : IsPGroup p T)
    {M : Subgroup G} [_hM_norm : M.Normal] (hM_p' : (Nat.card M).Coprime p)
    {S : Subgroup G} (hS_le : S ≤ T ⊔ M) (hS_card : Nat.card S = Nat.card T)
    {Q : Subgroup ↥(T ⊔ M : Subgroup G)} (hQ_pgroup : IsPGroup p Q)
    (hS_sub_Q : S.subgroupOf (T ⊔ M) ≤ Q) :
    Q = S.subgroupOf (T ⊔ M) := by
  have hS_sub_card : Nat.card (S.subgroupOf (T ⊔ M : Subgroup G)) = Nat.card T := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS_le).toEquiv, hS_card]
  have h_disj : T ⊓ M = ⊥ := inf_eq_bot_of_pGroup_coprime hT hM_p'
  have h_card_sup : Nat.card (T ⊔ M : Subgroup G) = Nat.card T * Nat.card M :=
    card_sup_eq_card_mul_card_of_disjoint_normal h_disj
  obtain ⟨k, hk⟩ := hT.exists_card_eq
  obtain ⟨j, hj⟩ := hQ_pgroup.exists_card_eq
  have hQ_dvd : Nat.card Q ∣ Nat.card ↥(T ⊔ M : Subgroup G) :=
    Subgroup.card_subgroup_dvd_card Q
  rw [h_card_sup, hk, hj] at hQ_dvd
  have hp_cop : (p ^ j).Coprime (Nat.card M) := (hM_p'.symm).pow_left j
  have hpj_dvd_pk : p ^ j ∣ p ^ k := Nat.Coprime.dvd_of_dvd_mul_right hp_cop hQ_dvd
  have hcard_le : Nat.card (S.subgroupOf (T ⊔ M : Subgroup G)) ≤ Nat.card Q :=
    Subgroup.card_le_of_le hS_sub_Q
  rw [hS_sub_card, hk, hj] at hcard_le
  have hk_le_j : k ≤ j := (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hcard_le
  have hj_le_k : j ≤ k :=
    (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp hpj_dvd_pk
  have hjk : j = k := le_antisymm hj_le_k hk_le_j
  symm
  apply Subgroup.eq_of_le_of_card_ge hS_sub_Q
  rw [hS_sub_card, hk, hj, hjk]

/-- **Helper for Lem 1.14** (Step 3 part 2, Sylow 性, S = T 特殊化):
T p-group + M ⊴ G p'-subgroup ⇒ `T.subgroupOf (T ⊔ M)` は ↥(T ⊔ M) の Sylow p.
一般版 `subgroupOf_sup_eq_of_pGroup_le_of_card_eq` (S = T の場合) の corollary. -/
theorem subgroupOf_sup_eq_of_pGroup_le_of_coprime
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T : Subgroup G} (hT : IsPGroup p T)
    {M : Subgroup G} [_hM_norm : M.Normal] (hM_p' : (Nat.card M).Coprime p)
    {Q : Subgroup ↥(T ⊔ M : Subgroup G)} (hQ_pgroup : IsPGroup p Q)
    (hT_sub_Q : T.subgroupOf (T ⊔ M) ≤ Q) :
    Q = T.subgroupOf (T ⊔ M) :=
  subgroupOf_sup_eq_of_pGroup_le_of_card_eq hT hM_p' le_sup_left rfl hQ_pgroup hT_sub_Q

/-- **BG Lemma 1.14 (易 direction, sorry-free)**: `N_G(T)·M ≤ N_G(T·M)`.

- `T.normalizer ≤ (T ⊔ M).normalizer`: x normalizes T ⇒ x normalizes M (M ⊴ G) ⇒ x
  normalizes T ⊔ M.
- `M ≤ (T ⊔ M).normalizer`: M ≤ T ⊔ M and subgroup self-normalizes via inner conjugation. -/
theorem le_normalizer_sup_of_normal
    {G : Type*} [Group G] (T : Subgroup G) (M : Subgroup G) [M.Normal] :
    Subgroup.normalizer T ⊔ M ≤ Subgroup.normalizer (T ⊔ M : Subgroup G) :=
  sup_le Subgroup.normalizer_le_normalizer_sup_normal
    (le_sup_right.trans Subgroup.le_normalizer)

/-- **BG Lemma 1.14 (heart, normalizer-in-G form)**: `T` p-subgroup of `G`, `M ⊴ G` p'-subgroup
(`gcd(|M|, p) = 1` を採用) ⇒ `N_G(T·M) = N_G(T)·M`.

In quotient form: with `f = QuotientGroup.mk' M`,
- `(N_{G/M}(T·M/M)).comap f = N_G(T·M)` (mathlib `comap_normalizer_eq_of_surjective`)
- `N_G(T·M) = N_G(T)·M` (this lemma)

**Proof** (BG p.5, 主要部 = hard direction):
- 易: `M ≤ T·M ≤ N_G(T·M)` (subgroup self-normalization) + `N_G(T) ≤ N_G(T·M)` (M normal
  ⇒ conjugation fixes M, T conjugation fixes T, so T·M fixed).
- 難: `x ∈ N_G(T·M)` ⇒ `xTx⁻¹ ⊆ T·M`. `T ∩ M = ⊥` (coprime orders) ⇒ `|T·M| = |T|·|M|`,
  `|T|` は `|T·M|` の p-part ⇒ `T` Sylow `p` of `T·M`. 同様に `xTx⁻¹` Sylow `p` of `T·M`.
  Sylow II in T·M: `∃ y ∈ T·M, xTx⁻¹ = yTy⁻¹`. `y = m·t` (`m ∈ M`, `t ∈ T`, possible
  since `M·T = T·M` for M normal) ⇒ `xTx⁻¹ = m·T·m⁻¹` ⇒ `m⁻¹x ∈ N_G(T)` ⇒
  `x ∈ M·N_G(T) = N_G(T)·M`.

**実装状態**: ⭐ **sorry-free 完成** (2026-05-24). TSyl + T_xSyl 構築 + Sylow II
(`MulAction.exists_smul_eq`) + `Subgroup.conj_smul_subgroupOf` + `subgroupOf_inj` で
`MulAut.conj y.val • T = T_x` を G で取得. `mem_sup_of_normal_left` で `y.val = m·t'`
分解 + `t' ∈ T ⇒ t'·T·t'⁻¹ = T` + `m⁻¹·x ∈ N_G(T)` で集約. ~115 LOC inline. -/
theorem normalizer_sup_eq_normalizer_sup_of_pGroup_coprime
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T : Subgroup G} (hT : IsPGroup p T)
    {M : Subgroup G} [hM_norm : M.Normal] (hM_p' : (Nat.card M).Coprime p) :
    Subgroup.normalizer (T ⊔ M : Subgroup G) = Subgroup.normalizer T ⊔ M := by
  apply le_antisymm _ (le_normalizer_sup_of_normal T M)
  intro x hx
  -- === Step 0: setup ===
  have h_disj : T ⊓ M = ⊥ := inf_eq_bot_of_pGroup_coprime hT hM_p'
  have h_card_sup : Nat.card (T ⊔ M : Subgroup G) = Nat.card T * Nat.card M :=
    card_sup_eq_card_mul_card_of_disjoint_normal h_disj
  have hT_le_TM : T ≤ (T ⊔ M : Subgroup G) := le_sup_left
  have hM_le_TM : M ≤ (T ⊔ M : Subgroup G) := le_sup_right
  have hx_norm : ∀ s, s ∈ (T ⊔ M : Subgroup G) ↔ x * s * x⁻¹ ∈ T ⊔ M :=
    Subgroup.mem_normalizer_iff.mp hx
  -- === Step 1: TSyl construction ===
  let TSyl : Sylow p ↥(T ⊔ M : Subgroup G) :=
    ⟨T.subgroupOf (T ⊔ M),
     (subgroupOf_sup_card_eq_and_pGroup hT M).2,
     fun {Q} hQ hle => subgroupOf_sup_eq_of_pGroup_le_of_coprime hT hM_p' hQ hle⟩
  -- === Step 2: T_x = x · T · x⁻¹ properties ===
  let T_x : Subgroup G := T.map (MulAut.conj x).toMonoidHom
  have hT_x_pg : IsPGroup p T_x :=
    hT.of_equiv (Subgroup.equivMapOfInjective T _ (MulAut.conj x).injective)
  have hT_x_card : Nat.card T_x = Nat.card T :=
    (Nat.card_congr (Subgroup.equivMapOfInjective T _ (MulAut.conj x).injective).toEquiv).symm
  have hT_x_le : T_x ≤ (T ⊔ M : Subgroup G) := by
    rintro a ⟨t, ht, hta⟩
    rw [← hta]
    change x * t * x⁻¹ ∈ T ⊔ M
    exact (hx_norm t).mp (hT_le_TM ht)
  have hT_x_sub_pg : IsPGroup p (T_x.subgroupOf (T ⊔ M : Subgroup G)) :=
    hT_x_pg.of_injective (Subgroup.subgroupOfEquivOfLe hT_x_le).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hT_x_le).injective
  have hT_x_sub_card : Nat.card (T_x.subgroupOf (T ⊔ M : Subgroup G)) = Nat.card T := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT_x_le).toEquiv, hT_x_card]
  -- === Step 3: T_xSyl construction (一般 helper 使用) ===
  let T_xSyl : Sylow p ↥(T ⊔ M : Subgroup G) :=
    ⟨T_x.subgroupOf (T ⊔ M),
     hT_x_sub_pg,
     fun {Q} hQ_pg hT_x_sub_Q =>
       subgroupOf_sup_eq_of_pGroup_le_of_card_eq hT hM_p' hT_x_le hT_x_card hQ_pg hT_x_sub_Q⟩
  -- === Step 4: Sylow II — ∃ y : ↥(T ⊔ M), y • TSyl = T_xSyl ===
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (↥(T ⊔ M : Subgroup G)) TSyl T_xSyl
  -- === Step 5: extract y.val · T · y.val⁻¹ = T_x as subgroups of G ===
  have hy_carrier : (y • TSyl).toSubgroup = T_xSyl.toSubgroup := congrArg Sylow.toSubgroup hy
  have h_conj_T_eq_Tx : MulAut.conj (y : G) • T = T_x := by
    have h1 : (y • TSyl).toSubgroup = MulAut.conj y • T.subgroupOf (T ⊔ M) := rfl
    have h2 : T_xSyl.toSubgroup = T_x.subgroupOf (T ⊔ M : Subgroup G) := rfl
    have h3 : MulAut.conj y • T.subgroupOf (T ⊔ M : Subgroup G) =
        (MulAut.conj (y : G) • T).subgroupOf (T ⊔ M : Subgroup G) :=
      Subgroup.conj_smul_subgroupOf hT_le_TM y
    rw [h1, h2, h3] at hy_carrier
    -- hy_carrier : (MulAut.conj y.val • T).subgroupOf (T ⊔ M) = T_x.subgroupOf (T ⊔ M)
    have h_smul_T_le : MulAut.conj (y : G) • T ≤ (T ⊔ M : Subgroup G) := by
      rintro - ⟨t, ht, rfl⟩
      change (y : G) * t * (y : G)⁻¹ ∈ T ⊔ M
      exact (T ⊔ M).mul_mem ((T ⊔ M).mul_mem y.2 (hT_le_TM ht)) ((T ⊔ M).inv_mem y.2)
    rw [Subgroup.subgroupOf_inj] at hy_carrier
    rwa [inf_of_le_left h_smul_T_le, inf_of_le_left hT_x_le] at hy_carrier
  -- === Step 6: decompose y.val = m · t' (m ∈ M, t' ∈ T) ===
  have hy_in_MT : (y : G) ∈ (M ⊔ T : Subgroup G) := by
    rw [sup_comm]; exact y.2
  obtain ⟨m, hm_M, t', ht'_T, hmt⟩ := Subgroup.mem_sup_of_normal_left.mp hy_in_MT
  -- hmt : m * t' = y.val
  -- === Step 7: m · T · m⁻¹ = T_x (since t' normalizes T) ===
  have h_t'_norm_T : MulAut.conj t' • T = T := by
    ext s
    refine ⟨?_, ?_⟩
    · rintro ⟨u, hu, rfl⟩
      change t' * u * t'⁻¹ ∈ T
      exact T.mul_mem (T.mul_mem ht'_T hu) (T.inv_mem ht'_T)
    · intro hs
      refine ⟨t'⁻¹ * s * t', T.mul_mem (T.mul_mem (T.inv_mem ht'_T) hs) ht'_T, ?_⟩
      change t' * (t'⁻¹ * s * t') * t'⁻¹ = s
      group
  have h_conj_y_eq_conj_m : MulAut.conj (y : G) • T = MulAut.conj m • T := by
    rw [← hmt, map_mul, mul_smul, h_t'_norm_T]
  have h_mT_eq_Tx : MulAut.conj m • T = T_x := h_conj_y_eq_conj_m.symm.trans h_conj_T_eq_Tx
  -- === Step 8: m⁻¹ * x ∈ N_G(T) ===
  have h_mx_in_NT : m⁻¹ * x ∈ Subgroup.normalizer T := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨?_, ?_⟩
    · -- Forward: t ∈ T ⇒ (m⁻¹x)t(m⁻¹x)⁻¹ ∈ T
      intro ht
      -- x·t·x⁻¹ ∈ T_x (definition unfolding)
      have hxtx_in_Tx : x * t * x⁻¹ ∈ T_x := ⟨t, ht, by simp [MulAut.conj_apply]⟩
      rw [← h_mT_eq_Tx] at hxtx_in_Tx
      -- Get s ∈ T with m * s * m⁻¹ = x * t * x⁻¹
      obtain ⟨s, hs, hms⟩ := hxtx_in_Tx
      have hms_eq : m * s * m⁻¹ = x * t * x⁻¹ := by
        rw [← MulAut.conj_apply m s]; exact hms
      -- (m⁻¹x) · t · (m⁻¹x)⁻¹ = m⁻¹ · (x*t*x⁻¹) · m = m⁻¹ · (m*s*m⁻¹) · m = s
      have h_eq : m⁻¹ * x * t * (m⁻¹ * x)⁻¹ = s := by
        have step : m⁻¹ * (x * t * x⁻¹) * m = s := by rw [← hms_eq]; group
        calc m⁻¹ * x * t * (m⁻¹ * x)⁻¹
            = m⁻¹ * (x * t * x⁻¹) * m := by group
          _ = s := step
      rw [h_eq]; exact hs
    · -- Reverse: (m⁻¹x)t(m⁻¹x)⁻¹ ∈ T ⇒ t ∈ T
      intro hut
      set u := m⁻¹ * x * t * (m⁻¹ * x)⁻¹ with hu_def
      -- u ∈ T, and m·u·m⁻¹ = x·t·x⁻¹
      have hmum_eq_xtx : m * u * m⁻¹ = x * t * x⁻¹ := by rw [hu_def]; group
      -- m·u·m⁻¹ ∈ MulAut.conj m • T = T_x
      have hmum_in_mT : m * u * m⁻¹ ∈ MulAut.conj m • T :=
        ⟨u, hut, by simp [MulAut.conj_apply]⟩
      rw [h_mT_eq_Tx, hmum_eq_xtx] at hmum_in_mT
      -- hmum_in_mT : x * t * x⁻¹ ∈ T_x
      obtain ⟨s, hs, hxs⟩ := hmum_in_mT
      have hxs_eq : x * s * x⁻¹ = x * t * x⁻¹ := by
        rw [← MulAut.conj_apply x s]; exact hxs
      have h_st : s = t := mul_left_cancel (mul_right_cancel hxs_eq)
      rw [← h_st]; exact hs
  -- === Step 9: x = m · (m⁻¹ * x) ∈ M · N_G(T) ⊆ N_G(T) ⊔ M ===
  have h_x_eq : x = m * (m⁻¹ * x) := by group
  rw [h_x_eq]
  have h_in_M_NT : m * (m⁻¹ * x) ∈ (M : Subgroup G) ⊔ Subgroup.normalizer T :=
    Subgroup.mul_mem_sup hm_M h_mx_in_NT
  rwa [sup_comm] at h_in_M_NT

/-- **BG Lemma 1.14 (centralizer-in-G form)**: `T` p-subgroup of `G`, `M ⊴ G` p'-subgroup.
Writing `f = QuotientGroup.mk' M`, the preimage of `C_{G/M}(TM/M)` equals `C_G(T)·M`:
`(C_{G/M}(T.map f)).comap f = C_G(T) ⊔ M`. Equivalently `C_G(T)` surjects onto `C_{G/M}(TM/M)`.

This is the centralizer half of BG Lemma 1.14, derived from the normalizer half
(`normalizer_sup_eq_normalizer_sup_of_pGroup_coprime`) plus `T ⊓ M = ⊥`
(BG p.5: `CM ⊆ C* ⊆ N* = NM`, `C* ⊓ N = C`, so `C* = (C* ⊓ N)·M = CM`). Used for the
`O_{p'}(G) = 1` reduction in Proposition 1.15(b). -/
theorem centralizer_comap_mk'_eq_centralizer_sup_of_pGroup_coprime
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {T : Subgroup G} (hT : IsPGroup p T)
    {M : Subgroup G} [M.Normal] (hM_p' : (Nat.card M).Coprime p) :
    (Subgroup.centralizer
        ((T.map (QuotientGroup.mk' M) : Subgroup (G ⧸ M)) : Set (G ⧸ M))).comap
        (QuotientGroup.mk' M)
      = Subgroup.centralizer (T : Set G) ⊔ M := by
  set f := QuotientGroup.mk' M with hf
  have hsurj : Function.Surjective f := QuotientGroup.mk'_surjective M
  have hker : f.ker = M := QuotientGroup.ker_mk' M
  have hdisj : T ⊓ M = ⊥ := inf_eq_bot_of_pGroup_coprime hT hM_p'
  apply le_antisymm
  · -- hard direction: `C* ⊆ C_G(T) ⊔ M`.
    intro x hx
    rw [Subgroup.mem_comap] at hx
    -- `x ∈ N_G(T ⊔ M)` via the normalizer-of-quotient identity.
    have hxN : x ∈ Subgroup.normalizer (T ⊔ M : Subgroup G) := by
      have hxn : f x ∈ Subgroup.normalizer (T.map f : Subgroup (G ⧸ M)) :=
        Subgroup.centralizer_le_normalizer _ hx
      have e1 : (T.map f).comap f = (T ⊔ M : Subgroup G) := by
        rw [Subgroup.comap_map_eq, hker]
      have e2 := Subgroup.comap_normalizer_eq_of_surjective (T.map f) hsurj
      have hmem : x ∈ (Subgroup.normalizer (T.map f : Subgroup (G ⧸ M))).comap f := by
        rw [Subgroup.mem_comap]; exact hxn
      rw [e2, e1] at hmem
      exact hmem
    rw [normalizer_sup_eq_normalizer_sup_of_pGroup_coprime hT hM_p', sup_comm] at hxN
    obtain ⟨m, hm, n, hn, hmn⟩ := Subgroup.mem_sup_of_normal_left.mp hxN
    -- `f m = 1`, hence `f n = f x`.
    have hfm : f m = 1 := MonoidHom.mem_ker.mp (by rw [hker]; exact hm)
    have hfn : f n = f x := by rw [← hmn, map_mul, hfm, one_mul]
    -- `n` centralizes `T`.
    have hn_cent : n ∈ Subgroup.centralizer (T : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have htT : t ∈ T := SetLike.mem_coe.mp ht
      -- `f n` commutes with `f t` (image of `T`).
      have hcomm : f n * f t = f t * f n := by
        have hft : (f t) ∈ (↑(T.map f) : Set (G ⧸ M)) :=
          SetLike.mem_coe.mpr (Subgroup.mem_map_of_mem f htT)
        rw [hfn]
        exact (Subgroup.mem_centralizer_iff.mp hx (f t) hft).symm
      -- `c := n*t*n⁻¹*t⁻¹ ∈ M` (vanishes mod `M`).
      have hcM : n * t * n⁻¹ * t⁻¹ ∈ M := by
        rw [← hker]
        refine MonoidHom.mem_ker.mpr ?_
        have : f n * f t * (f n)⁻¹ * (f t)⁻¹ = 1 := by rw [hcomm]; group
        simpa [map_mul, map_inv] using this
      -- `c ∈ T` since `n` normalizes `T`.
      have hcT : n * t * n⁻¹ * t⁻¹ ∈ T := by
        have hntn : n * t * n⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hn t).mp htT
        exact T.mul_mem hntn (T.inv_mem htT)
      have hc1 : n * t * n⁻¹ * t⁻¹ = 1 :=
        Subgroup.mem_bot.mp (hdisj ▸ Subgroup.mem_inf.mpr ⟨hcT, hcM⟩)
      have h1 : n * t * n⁻¹ = t := mul_inv_eq_one.mp hc1
      calc t * n = (n * t * n⁻¹) * n := by rw [h1]
        _ = n * t := by group
    rw [sup_comm]
    exact Subgroup.mem_sup_of_normal_left.mpr ⟨m, hm, n, hn_cent, hmn⟩
  · -- easy direction: `C_G(T) ⊔ M ⊆ C*`.
    rw [sup_le_iff]
    refine ⟨?_, ?_⟩
    · intro c hc
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      rintro h ⟨t, ht, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg f (Subgroup.mem_centralizer_iff.mp hc t ht)
    · intro μ hμ
      rw [Subgroup.mem_comap]
      have hμ1 : f μ = 1 := MonoidHom.mem_ker.mp (by rw [hker]; exact hμ)
      rw [hμ1]
      exact Subgroup.one_mem _

/-- **BG Proposition 1.15(a) (P. Hall & G. Higman "Lemma 1.2.3", thin wrap)**: `G` 有限可解 +
`O_{p'}(G) = ⊥` ⇒ `C_G(O_p(G)) ⊆ O_p(G)`.

**形式化**: Phase 1 `OddOrder.Isaacs.Ch03.hall_higman_1_2_3` の π = {p} 特殊化.
Ch.3 §3D の Hall-Higman は `[IsPiSeparable π G]` 版で, ここでは `[Group.IsSolvable G]`
から `isPiSeparable_of_isSolvable` instance を使って適用する.

**BG 原 statement (`T` Sylow p of `O_{p',p}(G)` ⇒ `C_G(T) ⊆ O_{p',p}(G)`) との関係**:
G を G/O_{p'}(G) に置き換えると `T` は `O_p(G/O_{p'}(G))` に一致 (Sylow p of p-group は
全体). この特殊形が下の statement.

CLAUDE.md no-wrapper policy 例外 (仮定特殊化: `Group.IsSolvable G` instance + π = {p}
specialization). -/
theorem hall_higman_solvable_specialization
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    (hp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G = ⊥) :
    Subgroup.centralizer (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G : Set G) ≤
      OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
  OddOrder.Isaacs.Ch03.hall_higman_1_2_3 ({p} : Set ℕ) hp'

/-- **Prop 1.15(b) core** (`O_{p'}(G) = ⊥` case, per element): every `u ∈ M := O_{p'}(C_G(R))`
centralizes `T := O_p(G)`. Proof mirrors `BG.AppA.thmA5_part2`: `⟨u⟩` acts by conjugation on the
`p`-group `RT := R ⊔ T`, and `C_{RT}(C_{RT}(u)) ⊆ C_{RT}(R) ⊆ C_{RT}(u)` — the second inclusion
because `C_{RT}(R) ⊆ C_G(R)` centralizes `u` (`[c,u] ∈ RT ⊓ M = ⊥`, since `M ⊴ C_G(R)` and `u`
normalizes `RT`). Proposition 1.10 then makes `⟨u⟩` act trivially on `RT ⊇ T`. -/
private theorem mem_centralizer_opCore_of_mem_oPiPrimeCore_centralizer
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    {R : Subgroup G} (hR : IsPGroup p R)
    {u : G} (huM : u ∈ OddOrder.GroupTheory.opiCoreInG ({p} : Set ℕ)ᶜ
      (Subgroup.centralizer (R : Set G))) :
    u ∈ Subgroup.centralizer ((OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) : Set G) := by
  classical
  set M : Subgroup G := OddOrder.GroupTheory.opiCoreInG ({p} : Set ℕ)ᶜ
    (Subgroup.centralizer (R : Set G)) with hM
  set T : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hT
  set RT : Subgroup G := R ⊔ T with hRT
  -- `u ∈ C_G(R)` and `u` is a `p'`-element.
  have huC : u ∈ Subgroup.centralizer (R : Set G) :=
    OddOrder.GroupTheory.opiCoreInG_le _ _ huM
  have hMp' : Nat.Coprime (Nat.card ↥M) p := by
    refine OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl (π := ({p} : Set ℕ)ᶜ)
      Nat.card_pos.ne' (Fact.out : p.Prime).pos.ne' ?_ ?_
    · intro q hq
      rw [hM, OddOrder.GroupTheory.card_opiCoreInG] at hq
      exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (({p} : Set ℕ)ᶜ) q hq
    · intro q hq
      rw [Nat.Prime.primeFactors (Fact.out : p.Prime), Finset.mem_singleton] at hq
      simp [hq]
  have hu_cop : (orderOf u).Coprime p := by
    have hdvd : orderOf u ∣ Nat.card ↥M := by
      have h : orderOf (⟨u, huM⟩ : ↥M) ∣ Nat.card ↥M := orderOf_dvd_natCard _
      rwa [Subgroup.orderOf_mk] at h
    exact Nat.Coprime.coprime_dvd_left hdvd hMp'
  -- `T` normal, `RT` a `p`-group; `RT ⊓ M = ⊥`.
  have hTnorm : T.Normal := by rw [hT]; exact OddOrder.Isaacs.Ch01.opCore.normal p G
  have hRT_pg : IsPGroup p ↥RT :=
    hR.to_sup_of_normal_right (OddOrder.Isaacs.Ch01.opCore_isPGroup p G)
  have hRTM_disj : RT ⊓ M = ⊥ := inf_eq_bot_of_pGroup_coprime hRT_pg hMp'
  -- `u` normalizes `RT` (centralizes `R`, normalizes `T ⊴ G`).
  have hu_norm_RT : u ∈ Subgroup.normalizer RT := by
    have huNR : u ∈ Subgroup.normalizer (R : Set G) :=
      Subgroup.centralizer_le_normalizer (R : Set G) huC
    rw [hRT]
    exact le_normalizer_sup_of_normal R T (Subgroup.mem_sup_left huNR)
  have hzu_le : Subgroup.zpowers u ≤ Subgroup.normalizer RT :=
    Subgroup.zpowers_le.mpr hu_norm_RT
  -- conjugation action of `⟨u⟩` on `RT`.
  set φ : ↥(Subgroup.zpowers u) →* MulAut ↥RT :=
    RT.normalizerMonoidHom.comp (Subgroup.inclusion hzu_le) with hφ
  have hφcoe : ∀ (a : ↥(Subgroup.zpowers u)) (g : ↥RT),
      ((φ a) g : G) = (a : G) * (g : G) * (a : G)⁻¹ := by
    intro a g; rw [hφ]; rfl
  -- (i) `R.subgroupOf RT ≤ fixedPoints` (`R ⊆ C_{RT}(u)`).
  have hR_le_fix : R.subgroupOf RT ≤ Subgroup.fixedPointsOfMulAut φ := by
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg
    rw [Subgroup.mem_fixedPointsOfMulAut]
    intro a
    refine Subtype.ext ?_
    rw [hφcoe]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    have hgu : Commute (g : G) u := Subgroup.mem_centralizer_iff.mp huC (g : G) hg
    have hcomm : Commute (a : G) (g : G) := by rw [← hk]; exact (hgu.symm).zpow_left k
    rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  -- (ii) `C_{RT}(R) ≤ fixedPoints` (`C_{RT}(R)` centralizes `u`, via `[c,u] ∈ RT ⊓ M = ⊥`).
  have hCRTR_le_fix : Subgroup.centralizer ((R.subgroupOf RT : Subgroup ↥RT) : Set ↥RT)
      ≤ Subgroup.fixedPointsOfMulAut φ := by
    intro c hc
    rw [Subgroup.mem_fixedPointsOfMulAut]
    intro a
    refine Subtype.ext ?_
    rw [hφcoe]
    -- `c` centralizes `R`, so `c ∈ C_G(R)`.
    have hc_cent_R : (c : G) ∈ Subgroup.centralizer (R : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have hr' : (⟨r, Subgroup.mem_sup_left hr⟩ : ↥RT) ∈ (R.subgroupOf RT : Subgroup ↥RT) := by
        rw [Subgroup.mem_subgroupOf]; exact hr
      have hcr := Subgroup.mem_centralizer_iff.mp hc ⟨r, Subgroup.mem_sup_left hr⟩ hr'
      exact congrArg Subtype.val hcr
    -- `[c,u] ∈ M` (since `M ⊴ C_G(R)`).
    have hcomm_M : (c : G) * u * (c : G)⁻¹ * u⁻¹ ∈ M := by
      have hcu : (c : G) * u * (c : G)⁻¹ ∈ M :=
        ((Subgroup.mem_normalizer_iff.mp
          (OddOrder.GroupTheory.le_normalizer_opiCoreInG _ _ hc_cent_R)) u).mp huM
      exact M.mul_mem hcu (M.inv_mem huM)
    -- `[c,u] ∈ RT` (`c ∈ RT`, `u` normalizes `RT`).
    have hcomm_RT : (c : G) * u * (c : G)⁻¹ * u⁻¹ ∈ RT := by
      have hucu : u * (c : G)⁻¹ * u⁻¹ ∈ RT :=
        ((Subgroup.mem_normalizer_iff.mp hu_norm_RT) (c : G)⁻¹).mp (RT.inv_mem c.2)
      have hrw : (c : G) * u * (c : G)⁻¹ * u⁻¹ = (c : G) * (u * (c : G)⁻¹ * u⁻¹) := by group
      rw [hrw]; exact RT.mul_mem c.2 hucu
    -- so `[c,u] = 1`, i.e. `u` and `c` commute.
    have hcomm1 : (c : G) * u * (c : G)⁻¹ * u⁻¹ = 1 :=
      Subgroup.mem_bot.mp (hRTM_disj ▸ Subgroup.mem_inf.mpr ⟨hcomm_RT, hcomm_M⟩)
    have hcu_eq : u * (c : G) = (c : G) * u := by
      have h1 : (c : G) * u * (c : G)⁻¹ = u := mul_inv_eq_one.mp hcomm1
      calc u * (c : G) = ((c : G) * u * (c : G)⁻¹) * (c : G) := by rw [h1]
        _ = (c : G) * u := by group
    have hcu : Commute u (c : G) := hcu_eq
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    have hac : Commute (a : G) (c : G) := by rw [← hk]; exact hcu.zpow_left k
    rw [hac.eq, mul_assoc, mul_inv_cancel, mul_one]
  -- `C_{RT}(C_{RT}(u)) ⊆ C_{RT}(u)` for Prop 1.10.
  have hCC : Subgroup.centralizer (Subgroup.fixedPointsOfMulAut φ : Set ↥RT)
      ≤ Subgroup.fixedPointsOfMulAut φ :=
    calc Subgroup.centralizer (Subgroup.fixedPointsOfMulAut φ : Set ↥RT)
        ≤ Subgroup.centralizer ((R.subgroupOf RT : Subgroup ↥RT) : Set ↥RT) :=
          Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hR_le_fix)
      _ ≤ Subgroup.fixedPointsOfMulAut φ := hCRTR_le_fix
  have : Group.IsNilpotent ↥RT := hRT_pg.isNilpotent
  have hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers u)) (Nat.card ↥RT) := by
    obtain ⟨n, hn⟩ := hRT_pg.exists_card_eq
    rw [Nat.card_zpowers, hn]
    exact hu_cop.pow_right n
  have htrivφ := coprime_nilpotent_acts_trivially_of_centralizer_self
    (A := ↥(Subgroup.zpowers u)) (G := ↥RT) (φ := φ) hcop hCC
  -- `u` centralizes `T ≤ RT`.
  rw [Subgroup.mem_centralizer_iff]
  intro x hxT
  have hxRT : x ∈ RT := Subgroup.mem_sup_right hxT
  have h := htrivφ ⟨u, Subgroup.mem_zpowers u⟩ ⟨x, hxRT⟩
  have hco := congrArg Subtype.val h
  rw [hφcoe] at hco
  have hco' : u * x * u⁻¹ = x := hco
  have hux : u * x = x * u := by
    have hcg := congrArg (· * u) hco'; simpa [mul_assoc] using hcg
  exact hux.symm

/-- **BG Proposition 1.15(b), `O_{p'}(G) = ⊥` case** (D. Goldschmidt): if `G` is solvable with
trivial `p'`-core and `R` is a `p`-subgroup, then `O_{p'}(C_G(R)) = ⊥`. From the unconditional
`O_{p'}(C_G(R)) ⊆ C_G(O_p(G))` (`mem_centralizer_opCore_of_mem_oPiPrimeCore_centralizer`) and
`C_G(O_p(G)) ⊆ O_p(G)` (Prop 1.15(a)): `O_{p'}(C_G(R))` is both a `p`-subgroup (`≤ O_p(G)`) and a
`p'`-group, hence `⊥`. The general form (below) reduces to this case modulo `O_{p'}(G)`. -/
theorem oPiPrimeCore_centralizer_eq_bot_of_oPiPrimeCore_eq_bot
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    {R : Subgroup G} (hR : IsPGroup p R)
    (hbot : OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ)ᶜ G = ⊥) :
    OddOrder.GroupTheory.opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer (R : Set G)) = ⊥ := by
  set M : Subgroup G := OddOrder.GroupTheory.opiCoreInG ({p} : Set ℕ)ᶜ
    (Subgroup.centralizer (R : Set G)) with hM
  set T : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hT
  -- `M ≤ C_G(T) ≤ T`.
  have hM_le_T : M ≤ T := by
    have hM_le_CT : M ≤ Subgroup.centralizer (T : Set G) := fun u hu =>
      mem_centralizer_opCore_of_mem_oPiPrimeCore_centralizer hR (hM ▸ hu)
    have hset : {q | q ∉ ({p} : Set ℕ)} = ({p} : Set ℕ)ᶜ := by ext q; simp
    have hHH := hall_higman_solvable_specialization (p := p) (G := G) (by rw [hset]; exact hbot)
    rw [OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore, ← hT] at hHH
    exact hM_le_CT.trans hHH
  -- `card M` is coprime to `p` (`M` is a `p'`-group).
  have hMp' : Nat.Coprime (Nat.card ↥M) p := by
    refine OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl (π := ({p} : Set ℕ)ᶜ)
      Nat.card_pos.ne' (Fact.out : p.Prime).pos.ne' ?_ ?_
    · intro q hq
      rw [hM, OddOrder.GroupTheory.card_opiCoreInG] at hq
      exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (({p} : Set ℕ)ᶜ) q hq
    · intro q hq
      rw [Nat.Prime.primeFactors (Fact.out : p.Prime), Finset.mem_singleton] at hq
      simp [hq]
  -- `card M ∣ card T = p^n` and coprime to `p` ⟹ `card M = 1` ⟹ `M = ⊥`.
  obtain ⟨n, hn⟩ := (OddOrder.Isaacs.Ch01.opCore_isPGroup p G).exists_card_eq
  have hdvd : Nat.card ↥M ∣ Nat.card ↥T := Subgroup.card_dvd_of_le hM_le_T
  rw [hT, hn] at hdvd
  have hcard1 : Nat.card ↥M = 1 := by
    have hg := Nat.gcd_eq_left hdvd
    rw [← hg]; exact hMp'.pow_right n
  exact (Subgroup.card_eq_one).mp hcard1

/-- **BG Proposition 1.15(b) (D. Goldschmidt)**, general form: if `G` is a finite solvable group
and `R` is a `p`-subgroup, then `O_{p'}(C_G(R)) ≤ O_{p'}(G)`.

This reduces the general statement to the `O_{p'}(G) = ⊥` case
(`oPiPrimeCore_centralizer_eq_bot_of_oPiPrimeCore_eq_bot`) modulo `M₀ := O_{p'}(G)`. Writing
`f = mk' M₀`, `Ḡ = G/M₀`, `R̄ = R.map f`, Lemma 1.14 (`centralizer_comap_mk'_…`) gives
`C_Ḡ(R̄) = C_G(R)·M₀/M₀ = (C_G(R)).map f`. Setting `K := M.map f` for `M := O_{p'}(C_G(R))`:
`K` lies in `C̄ := C_Ḡ(R̄)`, is normalized by `C̄` (since `M ⊴ C_G(R)`), and is a `p'`-group, so
`K.subgroupOf C̄ ≤ O_{p'}(↥C̄)`, i.e. `K ≤ O_{p'}(C_Ḡ(R̄))`. The special case at `Ḡ` (where
`O_{p'}(Ḡ) = ⊥` by `oPiCore_quotient_self_eq_bot`) forces `K = ⊥`, hence `M ≤ ker f = M₀`. -/
theorem oPiPrimeCore_centralizer_le_oPiPrimeCore
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    {R : Subgroup G} (hR : IsPGroup p R) :
    OddOrder.GroupTheory.opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer (R : Set G)) ≤
      OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ)ᶜ G := by
  set M : Subgroup G := OddOrder.GroupTheory.opiCoreInG ({p} : Set ℕ)ᶜ
    (Subgroup.centralizer (R : Set G)) with hMdef
  set M₀ : Subgroup G := OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ)ᶜ G with hM₀def
  -- goal is now `M ≤ M₀`.
  have hM₀norm : M₀.Normal := by rw [hM₀def]; infer_instance
  set f : G →* G ⧸ M₀ := QuotientGroup.mk' M₀ with hfdef
  have hsurj : Function.Surjective f := QuotientGroup.mk'_surjective M₀
  have hker : f.ker = M₀ := QuotientGroup.ker_mk' M₀
  -- `M₀ = O_{p'}(G)` is a `p'`-group, so its order is coprime to `p`.
  have hM₀p' : Nat.Coprime (Nat.card ↥M₀) p := by
    refine OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := ({p} : Set ℕ)ᶜ) Nat.card_pos.ne' (Fact.out : p.Prime).pos.ne' ?_ ?_
    · intro q hq
      rw [hM₀def] at hq
      exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (({p} : Set ℕ)ᶜ) q hq
    · intro q hq
      rw [Nat.Prime.primeFactors (Fact.out : p.Prime), Finset.mem_singleton] at hq
      simp [hq]
  have hM₀map : M₀.map f = ⊥ := by rw [Subgroup.map_eq_bot_iff]; exact hker.ge
  -- `Cbar = C_Ḡ(R̄)`, the centralizer of the image of `R`.
  set Cbar : Subgroup (G ⧸ M₀) := Subgroup.centralizer ((R.map f) : Set (G ⧸ M₀)) with hCbardef
  -- brick 1 (Lemma 1.14): the preimage of `Cbar` is `C_G(R) ⊔ M₀`.
  have hbrick1 : Cbar.comap f = Subgroup.centralizer (R : Set G) ⊔ M₀ :=
    centralizer_comap_mk'_eq_centralizer_sup_of_pGroup_coprime hR hM₀p'
  -- hence `Cbar = (C_G(R)).map f` (apply `map f`, `M₀.map f = ⊥`).
  have hCbareq : Cbar = (Subgroup.centralizer (R : Set G)).map f := by
    have h := congrArg (Subgroup.map f) hbrick1
    rwa [Subgroup.map_comap_eq_self_of_surjective hsurj, Subgroup.map_sup, hM₀map,
      sup_bot_eq] at h
  set K : Subgroup (G ⧸ M₀) := M.map f with hKdef
  -- (A) `K ≤ Cbar`.
  have hM_le_C : M ≤ Subgroup.centralizer (R : Set G) :=
    OddOrder.GroupTheory.opiCoreInG_le _ _
  have hKC : K ≤ Cbar := by rw [hKdef, hCbareq]; exact Subgroup.map_mono hM_le_C
  -- (B) `Cbar` stabilizes `K` by conjugation (`M ⊴ C_G(R)`).
  have hK_conj_stable : ∀ g ∈ Cbar, ∀ x ∈ K, g * x * g⁻¹ ∈ K := by
    intro g hg x hx
    rw [hCbareq] at hg
    obtain ⟨y, hy, rfl⟩ := hg
    rw [hKdef] at hx ⊢
    obtain ⟨m, hm, rfl⟩ := hx
    have hconj : y * m * y⁻¹ ∈ M :=
      (Subgroup.mem_normalizer_iff.mp
        (OddOrder.GroupTheory.le_normalizer_opiCoreInG ({p} : Set ℕ)ᶜ
          (Subgroup.centralizer (R : Set G)) hy) m).mp hm
    have heq : f y * f m * (f y)⁻¹ = f (y * m * y⁻¹) := by rw [map_mul, map_mul, map_inv]
    rw [heq]
    exact Subgroup.mem_map_of_mem f hconj
  -- (C) `K.subgroupOf Cbar` is normal in `↥Cbar`.
  have hK_norm : (K.subgroupOf Cbar).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hK_conj_stable (g : G ⧸ M₀) g.2 (n : G ⧸ M₀) hn
  -- (D) `K` is a `p'`-group, so `K.subgroupOf Cbar ≤ O_{p'}(↥Cbar)`.
  have hM_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ)ᶜ M := by
    intro q hq
    rw [hMdef, OddOrder.GroupTheory.card_opiCoreInG] at hq
    exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (({p} : Set ℕ)ᶜ) q hq
  have hK_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ)ᶜ K := by
    intro q hq
    have hdvd : Nat.card ↥K ∣ Nat.card ↥M := by rw [hKdef]; exact Subgroup.card_map_dvd _ _
    exact hM_pi q (Nat.primeFactors_mono hdvd Nat.card_pos.ne' hq)
  have hK_le_oPiCore : K.subgroupOf Cbar ≤ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ)ᶜ ↥Cbar :=
    (OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.subgroupOf hKC hK_pi).le_oPiCore
  -- (E) `K ≤ O_{p'}(Cbar)` realized in `Ḡ`.
  have hK_le : K ≤ OddOrder.GroupTheory.opiCoreInG ({p} : Set ℕ)ᶜ Cbar := by
    intro x hx
    have hxCbar : x ∈ Cbar := hKC hx
    have hmem : (⟨x, hxCbar⟩ : ↥Cbar) ∈ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ)ᶜ ↥Cbar :=
      hK_le_oPiCore (by rw [Subgroup.mem_subgroupOf]; exact hx)
    change x ∈ (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ)ᶜ ↥Cbar).map Cbar.subtype
    exact Subgroup.mem_map.mpr ⟨⟨x, hxCbar⟩, hmem, rfl⟩
  -- (F) special case at `Ḡ`: `O_{p'}(Cbar) = ⊥` (because `O_{p'}(Ḡ) = ⊥`).
  have hbarbot : OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ)ᶜ (G ⧸ M₀) = ⊥ :=
    OddOrder.Isaacs.Ch03.oPiCore_quotient_self_eq_bot ({p} : Set ℕ)ᶜ
  have hCbarbot : OddOrder.GroupTheory.opiCoreInG ({p} : Set ℕ)ᶜ Cbar = ⊥ :=
    oPiPrimeCore_centralizer_eq_bot_of_oPiPrimeCore_eq_bot (hR.map f) hbarbot
  -- conclude `K = ⊥`, hence `M ≤ ker f = M₀`.
  have hKbot : K = ⊥ := le_bot_iff.mp (hK_le.trans hCbarbot.le)
  have hMmap : M.map f = ⊥ := by rw [← hKdef]; exact hKbot
  rw [Subgroup.map_eq_bot_iff, hker] at hMmap
  exact hMmap

/-- The BG subgroup `O_{π',π,π'}(G)`.

It is defined as the preimage of `O_{π'}` in `G / O_{π',π}(G)`, where
`O_{π',π}` is the Phase 1 subgroup `OddOrder.Isaacs.Ch03.oPiPrimePiCore`. -/
noncomputable def oPiPrimePiPiPrimeCore (π : Set ℕ) (G : Type*) [Group G] :
    Subgroup G :=
  Subgroup.comap
    (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiPrimePiCore π G))
    (OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ π}
      (G ⧸ OddOrder.Isaacs.Ch03.oPiPrimePiCore π G))

instance oPiPrimePiPiPrimeCore.normal (π : Set ℕ) (G : Type*) [Group G] :
    (oPiPrimePiPiPrimeCore π G).Normal := by
  rw [oPiPrimePiPiPrimeCore]
  infer_instance

variable {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G] [Finite G]

/-- Helper: for a surjective group hom `f : G →* H`, the cardinality of the preimage of a
subgroup `K ≤ H` equals `|K| * |ker f|`. Used in Lem 1.22 induction step. -/
lemma card_comap_eq_card_mul_card_ker
    {G' H : Type*} [Group G'] [Group H] [Finite G'] [Finite H]
    (f : G' →* H) (hf : Function.Surjective f) (K : Subgroup H) :
    Nat.card (K.comap f) = Nat.card K * Nat.card f.ker := by
  have h1 : (K.comap f).index = K.index := K.index_comap_of_surjective hf
  have h2 : (K.comap f).index * Nat.card (K.comap f) = Nat.card G' :=
    (K.comap f).index_mul_card
  have h3 : K.index * Nat.card K = Nat.card H := K.index_mul_card
  have h4 : Nat.card G' = Nat.card H * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker]
    exact congrArg (· * _)
      (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv)
  have hidx_ne : K.index ≠ 0 := by
    rw [Subgroup.index_eq_card]; exact Nat.card_pos.ne'
  have hstep : K.index * Nat.card (K.comap f) = K.index * (Nat.card K * Nat.card f.ker) := by
    calc K.index * Nat.card (K.comap f)
        = (K.comap f).index * Nat.card (K.comap f) := by rw [h1]
      _ = Nat.card G' := h2
      _ = Nat.card H * Nat.card f.ker := h4
      _ = (K.index * Nat.card K) * Nat.card f.ker := by rw [h3]
      _ = K.index * (Nat.card K * Nat.card f.ker) := mul_assoc _ _ _
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hidx_ne) hstep

/-- **BG Lemma 1.22**: in a finite `p`-group `G`, every normal subgroup `N` contains, for each
`r` with `p^r ∣ |N|`, a normal subgroup of `G` of order `p^r`.

**Proof** (BG p.8): induction on `r`.
- Base `r = 0`: `L = ⊥`.
- Step `r → r+1`: by IH get `L₀ ⊴ G`, `L₀ ≤ N`, `|L₀| = p^r`. Work in quotient
  `G ⧸ L₀` (which is `p`-group by `IsPGroup.to_quotient`). The image `N' = N.map (mk' L₀)`
  is normal, nontrivial since `p ∣ |N'| = |N|/p^r` (by `card_comap_eq_card_mul_card_ker`).
  By Phase 1 `IsPGroup.normal_inf_center_nontrivial`, `N' ⊓ Z(G ⧸ L₀)` is nontrivial. By
  Cauchy, take `x ∈ N' ⊓ Z(G ⧸ L₀)` of order `p`. Then `⟨x⟩` is central (hence normal in
  `G ⧸ L₀`). The preimage `L = ⟨x⟩.comap (mk' L₀)` satisfies `L ⊴ G`, `L ≤ N` (since
  `(N.map f).comap f = N ⊔ ker f = N`), `|L| = p · p^r = p^(r+1)` (helper).

proof 実装は次 commit (技術的詳細: `orderOf_subtype_coe`, `Subgroup.zpowers` 中央化, など
mathlib API の精査要). -/
theorem normal_subgroup_card_pow_le_of_pGroup
    (hG : IsPGroup p G) {N : Subgroup G} [hN : N.Normal] {r : ℕ}
    (hr_dvd : p ^ r ∣ Nat.card N) :
    ∃ L : Subgroup G, L.Normal ∧ L ≤ N ∧ Nat.card L = p ^ r := by
  classical
  induction r with
  | zero =>
    exact ⟨⊥, Subgroup.normal_bot, bot_le, by rw [Subgroup.card_bot, pow_zero]⟩
  | succ r ih =>
    obtain ⟨L₀, hL₀_norm, hL₀_le_N, hL₀_card⟩ :=
      ih (dvd_trans (pow_dvd_pow p (Nat.le_succ _)) hr_dvd)
    have : L₀.Normal := hL₀_norm
    let f : G →* G ⧸ L₀ := QuotientGroup.mk' L₀
    have hf_surj : Function.Surjective f := QuotientGroup.mk'_surjective _
    have hf_ker : f.ker = L₀ := QuotientGroup.ker_mk' L₀
    let N' : Subgroup (G ⧸ L₀) := N.map f
    have hN'_normal : N'.Normal := hN.map f hf_surj
    have hG'_pgroup : IsPGroup p (G ⧸ L₀) := hG.to_quotient L₀
    have hN'_comap : (N.map f).comap f = N := by
      rw [Subgroup.comap_map_eq, hf_ker, sup_eq_left]; exact hL₀_le_N
    have hN_card_eq : Nat.card N = Nat.card N' * Nat.card L₀ := by
      have h := card_comap_eq_card_mul_card_ker f hf_surj N'
      rwa [hN'_comap, hf_ker] at h
    have hpr_pos : 0 < p ^ r := Nat.pos_of_ne_zero (pow_ne_zero _ hp.out.ne_zero)
    have hp_dvd_N' : p ∣ Nat.card N' := by
      have h1 : p ^ (r + 1) ∣ Nat.card N' * p ^ r := by
        rw [← hL₀_card, ← hN_card_eq]; exact hr_dvd
      have h2 : p * p ^ r ∣ Nat.card N' * p ^ r := by
        rw [show p * p ^ r = p ^ (r + 1) by ring]; exact h1
      exact Nat.dvd_of_mul_dvd_mul_right hpr_pos h2
    have hN'_card_gt : 1 < Nat.card N' :=
      lt_of_lt_of_le hp.out.one_lt (Nat.le_of_dvd Nat.card_pos hp_dvd_N')
    have hN'_nontrivial : Nontrivial N' :=
      Finite.one_lt_card_iff_nontrivial.mp hN'_card_gt
    have hinter_nontrivial :
        Nontrivial ((N' ⊓ Subgroup.center (G ⧸ L₀) : Subgroup (G ⧸ L₀))) :=
      OddOrder.Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial hG'_pgroup hN'_nontrivial
    have hinter_card_gt : 1 < Nat.card ((N' ⊓ Subgroup.center (G ⧸ L₀) : Subgroup (G ⧸ L₀))) :=
      Finite.one_lt_card_iff_nontrivial.mpr hinter_nontrivial
    have hinter_pgroup : IsPGroup p ((N' ⊓ Subgroup.center (G ⧸ L₀) : Subgroup (G ⧸ L₀))) :=
      hG'_pgroup.to_subgroup _
    have hp_dvd_inter : p ∣ Nat.card ((N' ⊓ Subgroup.center (G ⧸ L₀) : Subgroup (G ⧸ L₀))) := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hinter_pgroup
      rw [hn] at hinter_card_gt ⊢
      have : 0 < n := by
        rcases n with _ | n
        · simp at hinter_card_gt
        · exact Nat.succ_pos _
      exact dvd_pow_self p this.ne'
    have : Fintype ((N' ⊓ Subgroup.center (G ⧸ L₀) : Subgroup (G ⧸ L₀))) := Fintype.ofFinite _
    have hp_dvd_fintype :
        p ∣ Fintype.card ((N' ⊓ Subgroup.center (G ⧸ L₀) : Subgroup (G ⧸ L₀))) := by
      rwa [← Nat.card_eq_fintype_card]
    obtain ⟨⟨xc, hxc_mem⟩, hxc_order⟩ := exists_prime_orderOf_dvd_card p hp_dvd_fintype
    set x : G ⧸ L₀ := xc with hx_def
    have hx_in_N' : x ∈ N' := (Subgroup.mem_inf.mp hxc_mem).1
    have hx_in_center : x ∈ Subgroup.center (G ⧸ L₀) := (Subgroup.mem_inf.mp hxc_mem).2
    set K : Subgroup (G ⧸ L₀) := Subgroup.zpowers x with hK_def
    have hK_le_N' : K ≤ N' := Subgroup.zpowers_le.mpr hx_in_N'
    have hx_orderOf : orderOf x = p := by
      change orderOf xc = p
      exact (Subgroup.orderOf_coe ⟨xc, hxc_mem⟩).trans hxc_order
    have hK_card : Nat.card K = p := by
      rw [Nat.card_zpowers, hx_orderOf]
    have hx_comm : ∀ g, g * x = x * g := Subgroup.mem_center_iff.mp hx_in_center
    have hK_normal : K.Normal := by
      refine ⟨fun a ha g => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hgx : Commute g x := hx_comm g
      have hgxk : Commute g (x ^ k) := hgx.zpow_right k
      rw [show g * x ^ k * g⁻¹ = x ^ k from by rw [hgxk.eq, mul_inv_cancel_right]]
      exact zpow_mem (Subgroup.mem_zpowers x) k
    refine ⟨K.comap f, hK_normal.comap f, ?_, ?_⟩
    · intro g hg
      have hg_N' : f g ∈ N' := hK_le_N' hg
      have : g ∈ (N.map f).comap f := hg_N'
      rwa [hN'_comap] at this
    · have h := card_comap_eq_card_mul_card_ker f hf_surj K
      rw [hf_ker, hL₀_card, hK_card] at h
      rw [h, pow_succ, mul_comm]

end OddOrder.BG.Ch1.S01


