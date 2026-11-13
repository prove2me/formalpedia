-- Prove2me | Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74
-- name    : OddOrder_BG_Ch2_Uniqueness_S07_Theorem74
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:03:03.671416+00:00
-- url     : https://prove2.me/theorems/3fcb352f-5484-4bb6-9946-bec064a2bdfa
-- title:
--   BG §7: Theorem 7.4 and Hypothesis 7.1
-- statement:
--   Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §7: Hypothesis 7.1 on a subgroup $A$ and the setup for Theorem 7.4, from the transitivity development.
--
--   Main definitions: `primesOf` ($\pi(A)$, the set of prime divisors of $|A|$), `kSubgroup` ($K=O_{\pi'}(C_G(A))$), `ConjTransitiveOn` ($K$ acts transitively by conjugation on a set of subgroups), `scn3Global` ($\mathrm{SCN}_3(p)$ globally), `Hypothesis71` (BG Hypothesis 7.1) and `conjAction` (the conjugation action of $A$ on $G$).
--
--   The bundle also proves 24 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch2_Uniqueness/S07_Theorem74.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch2_Uniqueness/S07_Theorem74.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_Setup
import Definitions.Def_OddOrder_BG_AppA_PStability
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_PLength
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S01_Solvable
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S01b_Prop116
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04_PGroupsSmallRank
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S06_Additional
import Definitions.Def_OddOrder_GroupTheory_MaximalSubgroup
import Definitions.Def_OddOrder_GroupTheory_AInvariantPiSubgroups
import Definitions.Def_OddOrder_GroupTheory_SCN
import Definitions.Def_OddOrder_GroupTheory_PRank
import Definitions.Def_OddOrder_GroupTheory_SubgroupInAmbient
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Main
import Mathlib.GroupTheory.IsSubnormal
import Mathlib.Algebra.Group.Subgroup.Pointwise

namespace OddOrder.BG.Ch2.S07

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.Isaacs.Ch06 (actionFixedBy mem_actionFixedBy nontrivialActionFixedByClosure
  nontrivialActionFixedByClosure_le_iff)

open scoped Pointwise

variable {G : Type*} [Group G]

/-- `π(A)`: `|A|` の素因子集合。 -/
def primesOf (A : Subgroup G) : Set ℕ := {q | q ∈ (Nat.card ↥A).primeFactors}

/-- `K = O_{π'}(C_G(A))` (Hypothesis 7.1 の `K`)。`opiCoreInG` と `derivedInG` の canonical は
`OddOrder.GroupTheory.SubgroupInAmbient` に移動 (issue 0052; `open OddOrder.GroupTheory` で参照)。 -/
def kSubgroup (A : Subgroup G) : Subgroup G :=
  opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (A : Set G))

/-- `K` が部分群の集合 `S` 上 conjugation で **推移的に作用**する: 任意の `Q₁,Q₂ ∈ S` に対し
ある `k ∈ K` で `Q₁^k = Q₂` (`MulAut.conj k • Q₁ = Q₂`)。 -/
def ConjTransitiveOn (K : Subgroup G) (S : Set (Subgroup G)) : Prop :=
  ∀ Q₁ ∈ S, ∀ Q₂ ∈ S, ∃ k ∈ K, MulAut.conj k • Q₁ = Q₂

/-- If a trivial subgroup acts transitively on `ℋ_H*(A;π)`, that set has at most one
member. -/
theorem hInvariantStar_eq_of_conjTransitiveOn_bot
    {K H A : Subgroup G} {π : Set ℕ} (hKbot : K = ⊥)
    (htrans : ConjTransitiveOn K (hInvariantStar H A π))
    {Q₁ Q₂ : Subgroup G} (hQ₁ : Q₁ ∈ hInvariantStar H A π)
    (hQ₂ : Q₂ ∈ hInvariantStar H A π) :
    Q₁ = Q₂ := by
  obtain ⟨k, hkK, hkQ⟩ := htrans Q₁ hQ₁ Q₂ hQ₂
  have hk_one : k = 1 := by
    rw [hKbot, Subgroup.mem_bot] at hkK
    exact hkK
  rw [hk_one, map_one, one_smul] at hkQ
  exact hkQ

/-- **`SCN₃(p)` global** (BG §7 L2137): あるシロー `p`-部分群 `P` で `A ∈ SCN₃(P)`
(↥P 内で `IsSCN₃`) となる `A ≤ G`。 -/
def scn3Global (p : ℕ) (G : Type*) [Group G] : Set (Subgroup G) :=
  {A | ∃ P : Sylow p G, A ≤ (P : Subgroup G) ∧ IsSCN₃ p (A.subgroupOf (P : Subgroup G))}

@[simp]
theorem mem_scn3Global {p : ℕ} {A : Subgroup G} :
    A ∈ scn3Global p G ↔
      ∃ P : Sylow p G, A ≤ (P : Subgroup G) ∧ IsSCN₃ p (A.subgroupOf (P : Subgroup G)) :=
  Iff.rfl

/-- Unpack global `SCN₃(p)` membership into the Sylow subgroup that witnesses it. -/
theorem exists_sylow_of_mem_scn3Global {p : ℕ} {A : Subgroup G}
    (hA : A ∈ scn3Global p G) :
    ∃ P : Sylow p G, A ≤ (P : Subgroup G) ∧ IsSCN₃ p (A.subgroupOf (P : Subgroup G)) :=
  hA

/-- **BG Hypothesis 7.1** (mmd L2141): `A` についての固定設定。`π = π(A)`,
`K = O_{π'}(C_G(A))` (`kSubgroup A`) を伴い:

1. `A` は `G` の非自明な真部分群、
2. `A` を含む任意の真部分群 `X` について `⟨ℋ_X(A;π')⟩ = O_{π'}(X)`
   (`sSup (hInvariant X A π') = opiCoreInG π' X`)。 -/
structure Hypothesis71 (A : Subgroup G) : Prop where
  /-- `A ≠ 1`. -/
  ne_bot : A ≠ ⊥
  /-- `A` は `G` の真部分群。 -/
  proper : A < ⊤
  /-- (2): `A ⊆ X < G` なら `⟨ℋ_X(A;π')⟩ = O_{π'}(X)`。 -/
  generated_eq : ∀ X : Subgroup G, A ≤ X → X < ⊤ →
    sSup (hInvariant X A (primesOf A)ᶜ) = opiCoreInG (primesOf A)ᶜ X

/-- The conjugation action of a subgroup `A` on the ambient group `G`. -/
def conjAction (A : Subgroup G) : ↥A →* MulAut G :=
  MulAut.conj.comp A.subtype

/-- `Q` is invariant under the conjugation action of `A` iff `A` normalizes `Q`. -/
theorem isAInvariant_conjAction_iff {A Q : Subgroup G} :
    Ch03.IsAInvariant (conjAction A) Q ↔ A ≤ Subgroup.normalizer Q := by
  constructor
  · intro h a ha
    exact mem_normalizer_of_conj_smul_eq_self (h ⟨a, ha⟩)
  · intro h a
    exact conj_smul_eq_self_of_mem_normalizer (h a.2)

/-- `K = O_{π'}(C_G(A)) ≤ C_G(A)`. -/
theorem kSubgroup_le_centralizer (A : Subgroup G) :
    kSubgroup A ≤ Subgroup.centralizer (A : Set G) :=
  opiCoreInG_le _ _

/-- `K` is a `π'`-subgroup of `G`. -/
theorem isPiSubgroup_kSubgroup [Finite G] (A : Subgroup G) :
    Subgroup.IsPiSubgroup (primesOf A)ᶜ (kSubgroup A) :=
  isPiSubgroup_opiCoreInG _ _

/-- If the centralizer C_G(A) is a pi(A)-subgroup, then K = O_{pi(A)-prime}(C_G(A))
is trivial. This is the group-theoretic bridge used in BG (8.3) -> (8.6). -/
theorem kSubgroup_eq_bot_of_centralizer_isPiSubgroup [Finite G] {A : Subgroup G}
    (hCpi : Subgroup.IsPiSubgroup (primesOf A) (Subgroup.centralizer (A : Set G))) :
    kSubgroup A = ⊥ :=
  opiCoreInG_compl_eq_bot_of_isPiSubgroup hCpi

set_option backward.isDefEq.respectTransparency false in
/-- **BG §7 の Note** (Hypothesis 7.1 直後, mmd L2145): Hypothesis 7.1 のもとで、
`C_G(A)` の任意の `π'`-元は `K = O_{π'}(C_G(A))` に入る。

証明: `X := A ⊔ C_G(A) ≤ N_G(A)` は真部分群 (`G` simple, `A` 非自明真部分群)。
`⟨c⟩ ∈ ℋ_X(A;π')` なので Hypothesis 7.1(2) から `c ∈ O_{π'}(X)`;
`O_{π'}(X) ⊓ C_G(A)` は `C_G(A)` の正規 `π'`-部分群なので `K` に入る。 -/
theorem mem_kSubgroup_of_piPrime_mem_centralizer [Finite G] (hG : IsMinimalSimpleOdd G)
    {A : Subgroup G} (hA : Hypothesis71 A) {c : G}
    (hc : c ∈ Subgroup.centralizer (A : Set G))
    (hc_pi' : Subgroup.IsPiSubgroup (primesOf A)ᶜ (Subgroup.zpowers c)) :
    c ∈ kSubgroup A := by
  classical
  set π' : Set ℕ := (primesOf A)ᶜ
  set C : Subgroup G := Subgroup.centralizer (A : Set G) with hC_def
  set X : Subgroup G := A ⊔ C with hX_def
  have hAX : A ≤ X := le_sup_left
  have hCX : C ≤ X := le_sup_right
  -- `X` is proper: it normalizes `A`, and `N_G(A) < ⊤` by simplicity
  have hX_proper : X < ⊤ := by
    have hX_le : X ≤ Subgroup.normalizer A := by
      refine sup_le Subgroup.le_normalizer ?_
      intro x hx
      apply mem_normalizer_of_conj_smul_eq_self
      ext y
      rw [Subgroup.pointwise_smul_def, Subgroup.mem_map]
      constructor
      · rintro ⟨z, hz, rfl⟩
        change x * z * x⁻¹ ∈ A
        have hxz : x * z * x⁻¹ = z := by
          rw [← Subgroup.mem_centralizer_iff.mp hx z hz, mul_inv_cancel_right]
        rw [hxz]
        exact hz
      · intro hy
        refine ⟨y, hy, ?_⟩
        change x * y * x⁻¹ = y
        rw [← Subgroup.mem_centralizer_iff.mp hx y hy, mul_inv_cancel_right]
    rw [lt_top_iff_ne_top]
    intro hX_top
    have hnorm_top : Subgroup.normalizer (A : Set G) = ⊤ := by
      apply le_antisymm le_top
      rw [← hX_top]
      exact hX_le
    have hA_normal : A.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm_top
    rcases hG.simple.eq_bot_or_eq_top_of_normal A hA_normal with h | h
    · exact hA.ne_bot h
    · exact hA.proper.ne h
  -- Hypothesis 7.1(2) puts `c` into `O_{π'}(X)`
  have hzc_mem : Subgroup.zpowers c ∈ hInvariant X A π' := by
    refine ⟨Subgroup.zpowers_le.mpr (hCX hc), ?_, hc_pi'⟩
    intro a ha
    apply mem_normalizer_of_conj_smul_eq_self
    have hac : a * c * a⁻¹ = c := by
      rw [Subgroup.mem_centralizer_iff.mp hc a ha, mul_inv_cancel_right]
    ext y
    rw [Subgroup.pointwise_smul_def, Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
      change c ^ n = MulAut.conj a (c ^ n)
      rw [map_zpow]
      simp only [MulAut.conj_apply]
      rw [hac]
    · intro hy
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
      refine ⟨c ^ n, Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩, ?_⟩
      change MulAut.conj a (c ^ n) = y
      rw [map_zpow]
      simp only [MulAut.conj_apply]
      rw [hac, hn]
  have hc_O : c ∈ opiCoreInG π' X := by
    rw [← hA.generated_eq X hAX hX_proper]
    exact le_sSup hzc_mem (Subgroup.mem_zpowers c)
  -- `O_{π'}(X) ⊓ C` is a normal `π'`-subgroup of `C`, hence lies in `K`
  set W : Subgroup G := opiCoreInG π' X ⊓ C with hW_def
  have hW_le_C : W ≤ C := inf_le_right
  have hW_pi' : Subgroup.IsPiSubgroup π' W := by
    intro r hr
    refine isPiSubgroup_opiCoreInG π' X r ?_
    exact Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hr).1,
      dvd_trans (Nat.mem_primeFactors.mp hr).2.1
        (Subgroup.card_dvd_of_le inf_le_left), Nat.card_pos.ne'⟩
  have hWC_normal : (W.subgroupOf C).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgO : (g : G) ∈ Subgroup.normalizer (opiCoreInG π' X) :=
      le_normalizer_opiCoreInG π' X (hCX g.2)
    constructor
    · exact (Subgroup.mem_normalizer_iff.mp hgO _).mp hn.1
    · exact C.mul_mem (C.mul_mem g.2 hn.2) (C.inv_mem g.2)
  have hW_le_K : W ≤ kSubgroup A :=
    le_opiCoreInG_of_normal_of_isPiSubgroup hW_le_C hWC_normal hW_pi'
  exact hW_le_K ⟨hc_O, hc⟩

/-- `MulAut.conj` 作用は `map` で書ける (S01/S11 の private 版の局所コピー)。 -/
theorem mulAut_smul_eq_map (φ : MulAut G) (H : Subgroup G) :
    φ • H = H.map (φ : G →* G) := by
  rw [Subgroup.pointwise_smul_def]; rfl

/-- A-不変 `U` 上の制限作用に対し, A-不変な `H` の `subgroupOf U` も不変 (S01 private の局所複製)。 -/
theorem isAInvariant_subgroupOf_restrict {A : Type*} [Group A]
    {φ : A →* MulAut G} {U H : Subgroup G} (hU : Ch03.IsAInvariant φ U)
    (hH : Ch03.IsAInvariant φ H) :
    Ch03.IsAInvariant hU.restrict (H.subgroupOf U) := by
  rw [Ch03.isAInvariant_iff_smul_mem]
  intro a h hh
  rw [Subgroup.mem_subgroupOf] at hh ⊢
  rw [Ch03.IsAInvariant.restrict_apply_val]
  exact hH.smul_mem a hh

/-- 不変 `U` の不変部分群を `U.subtype` で `G` に戻すと不変 (S01 private の局所複製)。 -/
theorem isAInvariant_map_subtype_of_restrict {A : Type*} [Group A]
    {φ : A →* MulAut G} {U : Subgroup G} (hU : Ch03.IsAInvariant φ U)
    {L : Subgroup ↥U} (hL : Ch03.IsAInvariant hU.restrict L) :
    Ch03.IsAInvariant φ (L.map U.subtype) := by
  rw [Ch03.isAInvariant_iff_smul_mem]
  intro a x hx
  rw [Subgroup.mem_map] at hx ⊢
  obtain ⟨l, hl, rfl⟩ := hx
  exact ⟨(hU.restrict a) l, hL.smul_mem a hl, Ch03.IsAInvariant.restrict_apply_val hU a l⟩

/-- **q-群内 normalizer 増大** (Lem 7.1 Case B 用, `lt_normalizer_inf_sylow_of_lt` の一般化):
有限 `q`-群 `P` の真部分群 `Q < P` は `N_G(Q) ⊓ P` の真部分群。 -/
theorem lt_normalizer_inf_of_pgroup_lt [Finite G] {q : ℕ} [Fact q.Prime]
    {P Q : Subgroup G} (hP : IsPGroup q ↥P) (hQP : Q < P) :
    Q < P ⊓ Subgroup.normalizer Q := by
  classical
  have : Group.IsNilpotent ↥P := hP.isNilpotent
  have hNC : NormalizerCondition ↥P := Group.normalizerCondition_of_isNilpotent (G := ↥P)
  have hQ_le : Q ≤ P := le_of_lt hQP
  have hsub_lt_top : Q.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact (ne_of_lt hQP) (le_antisymm hQ_le htop)
  have hlt := hNC (Q.subgroupOf P) hsub_lt_top
  obtain ⟨t, ht_norm, ht_not⟩ := SetLike.exists_of_lt hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hQ_le, Subgroup.mem_subgroupOf] at ht_norm
  rw [Subgroup.mem_subgroupOf] at ht_not
  refine lt_of_le_of_ne (le_inf hQ_le Subgroup.le_normalizer) ?_
  intro heq
  apply ht_not
  have hmem : (t : G) ∈ P ⊓ Subgroup.normalizer Q := ⟨t.2, ht_norm⟩
  rw [← heq] at hmem
  exact hmem

/-- `ℋ_G*(A;q)` の元は `G` の真部分群 (`G` は `q`-群でない: さもなくば可解)。 -/
theorem lt_top_of_mem_hInvariantStar [Finite G] (hG : IsMinimalSimpleOdd G)
    {A : Subgroup G} {q : ℕ} [Fact q.Prime] {Q : Subgroup G}
    (hQ : Q ∈ hInvariantStar ⊤ A {q}) : Q < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro hQtop
  have hpi : Subgroup.IsPiSubgroup {q} (⊤ : Subgroup G) :=
    hQtop ▸ hInvariantStar_isPiSubgroup hQ
  have hpg : IsPGroup q ↥(⊤ : Subgroup G) :=
    OddOrder.Isaacs.Ch04.isPGroup_of_isPiGroup_singleton hpi
  have : Group.IsNilpotent ↥(⊤ : Subgroup G) := hpg.isNilpotent
  exact hG.notSolvable
    (Group.isSolvable_of_surjective (MonoidHom.range_eq_top.mp (Subgroup.range_subtype ⊤)))

/-- **Lemma 7.1 の共通構成** (mmd L2151-2158): Hypothesis 7.1 のもと、真部分群 `H ⊇ A` で
`H ⊓ Q₁ ≠ 1 ≠ H ⊓ Q₂` のとき、`H ⊓ Qᵢ` を `O_{π'}(H)` の `A`-不変 Sylow `q`-部分群 `Rᵢ` に
含め (Prop 1.5(b))、`R₁^h = R₂` (`h ∈ C_G(A) ∩ O_{π'}(H) ⊆ K`, Prop 1.5(c)) とし、`R₂ ⊆ Q₃`
となる `Q₃ ∈ ℋ_G*(A;q)` を取る。すると (7.1) と `|Q₁^h ∩ H| = |Q₁ ∩ H|` が成り立つ。 -/
theorem commonConstruction [Finite G] (hG : IsMinimalSimpleOdd G)
    {A : Subgroup G} (hA : Hypothesis71 A) {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    {Q₁ Q₂ : Subgroup G} (hQ₁ : Q₁ ∈ hInvariantStar ⊤ A {q})
    (hQ₂ : Q₂ ∈ hInvariantStar ⊤ A {q})
    {H : Subgroup G} (hHproper : H < ⊤) (hAH : A ≤ H) :
    ∃ h ∈ kSubgroup A, ∃ Q₃ ∈ hInvariantStar ⊤ A {q},
      MulAut.conj h • Q₁ ∈ hInvariantStar ⊤ A {q} ∧
      (MulAut.conj h • Q₁) ⊓ H ≤ Q₃ ∧
      Q₂ ⊓ H ≤ Q₃ ∧
      Nat.card ↥((MulAut.conj h • Q₁) ⊓ H) = Nat.card ↥(Q₁ ⊓ H) := by
  classical
  set N : Subgroup G := opiCoreInG (primesOf A)ᶜ H with hN_def
  have hN_le_H : N ≤ H := opiCoreInG_le _ _
  have hN_lt : N < ⊤ := lt_of_le_of_lt hN_le_H hHproper
  have hN_solv : Group.IsSolvable ↥N := hG.isSolvable_of_lt_top N hN_lt
  have hN_inv : Ch03.IsAInvariant (conjAction A) N := by
    rw [isAInvariant_conjAction_iff]
    exact le_trans hAH (le_normalizer_opiCoreInG (primesOf A)ᶜ H)
  have hCop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥N) := by
    refine OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := primesOf A) Nat.card_pos.ne' Nat.card_pos.ne' (fun p hp => hp) (fun p hp => ?_)
    exact isPiSubgroup_opiCoreInG (primesOf A)ᶜ H p hp
  -- `hle_N`: `H ⊓ Q ≤ O_{π'}(H)` for each `Q ∈ ℋ_G*(A;q)` (via Hypothesis 7.1(2)).
  have hle_N : ∀ Q : Subgroup G, Q ∈ hInvariantStar ⊤ A {q} → H ⊓ Q ≤ N := by
    intro Q hQ
    have hpi_HQ : Subgroup.IsPiSubgroup ((primesOf A)ᶜ) (H ⊓ Q) := by
      refine Subgroup.IsPiSubgroup.mono (Set.singleton_subset_iff.mpr hq) ?_
      intro p hp
      exact (hInvariantStar_isPiSubgroup hQ) p (Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primeFactors.mp hp).1, dvd_trans (Nat.mem_primeFactors.mp hp).2.1
          (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩)
    have hnorm_HQ : A ≤ Subgroup.normalizer (H ⊓ Q) := by
      intro a ha
      apply mem_normalizer_of_conj_smul_eq_self (Q := H ⊓ Q)
      rw [Subgroup.smul_inf, conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer (hAH ha)),
          conj_smul_eq_self_of_mem_normalizer (hInvariantStar_le_normalizer hQ ha)]
    have hmem : H ⊓ Q ∈ hInvariant H A ((primesOf A)ᶜ) := ⟨inf_le_left, hnorm_HQ, hpi_HQ⟩
    have h1 := le_sSup hmem
    rwa [hA.generated_eq H hAH hHproper] at h1
  -- `getR`: each `H ⊓ Q` sits in an `A`-invariant Hall `q`-subgroup of `↥N` (Prop 1.5(b)).
  have getR : ∀ Q : Subgroup G, Q ∈ hInvariantStar ⊤ A {q} →
      ∃ R : Subgroup ↥N, Ch03.IsHallSubgroup {q} R ∧ Ch03.IsAInvariant hN_inv.restrict R ∧
        (H ⊓ Q).subgroupOf N ≤ R := by
    intro Q hQ
    have hle := hle_N Q hQ
    have hpi_HQ : Subgroup.IsPiSubgroup {q} (H ⊓ Q) := by
      intro p hp
      exact (hInvariantStar_isPiSubgroup hQ) p (Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primeFactors.mp hp).1, dvd_trans (Nat.mem_primeFactors.mp hp).2.1
          (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩)
    have hpi_sub : Ch03.Subgroup.IsPiGroup {q} ((H ⊓ Q).subgroupOf N) := by
      intro p hp
      apply hpi_HQ p
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hp
    have hinv_HQ : Ch03.IsAInvariant (conjAction A) (H ⊓ Q) := by
      rw [isAInvariant_conjAction_iff]
      intro a ha
      apply mem_normalizer_of_conj_smul_eq_self (Q := H ⊓ Q)
      rw [Subgroup.smul_inf, conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer (hAH ha)),
          conj_smul_eq_self_of_mem_normalizer (hInvariantStar_le_normalizer hQ ha)]
    have hinv_sub : Ch03.IsAInvariant hN_inv.restrict ((H ⊓ Q).subgroupOf N) :=
      isAInvariant_subgroupOf_restrict hN_inv hinv_HQ
    exact OddOrder.BG.Ch1.S01.aInvariant_piSubgroup_le_aInvariant_hall
      (G := ↥N) (A := ↥A) (φ := hN_inv.restrict) hCop hpi_sub hinv_sub
  obtain ⟨R₁', hR₁'_hall, hR₁'_inv, hR₁'_ge⟩ := getR Q₁ hQ₁
  obtain ⟨R₂', hR₂'_hall, hR₂'_inv, hR₂'_ge⟩ := getR Q₂ hQ₂
  -- Prop 1.5(c): `R₁ ↦ R₂` by some `c` fixed by `A`, inside `↥N`.
  obtain ⟨c, hc_fix, hc_conj⟩ := OddOrder.BG.Ch1.S01.aInvariant_hall_conj
    (G := ↥N) (A := ↥A) (φ := hN_inv.restrict) hCop hR₁'_hall hR₂'_hall hR₁'_inv hR₂'_inv
  have hc_mem_H : (c : G) ∈ H := hN_le_H c.2
  have hc_norm_H : (c : G) ∈ Subgroup.normalizer H := Subgroup.le_normalizer hc_mem_H
  -- `(c : G) ∈ C_G(A)` (fixed by `A`).
  have hc_centralizer : (c : G) ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hval := congrArg Subtype.val (hc_fix ⟨a, ha⟩)
    rw [Ch03.IsAInvariant.restrict_apply_val] at hval
    simp only [conjAction, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conj_apply] at hval
    exact mul_inv_eq_iff_eq_mul.mp hval
  -- `(c : G) ∈ K` (it is a `π'`-element of `C_G(A)`).
  have hzc_le_N : Subgroup.zpowers (c : G) ≤ N := Subgroup.zpowers_le.mpr c.2
  have hc_pi' : Subgroup.IsPiSubgroup ((primesOf A)ᶜ) (Subgroup.zpowers (c : G)) := by
    intro p hp
    exact isPiSubgroup_opiCoreInG (primesOf A)ᶜ H p (Nat.mem_primeFactors.mpr
      ⟨(Nat.mem_primeFactors.mp hp).1, dvd_trans (Nat.mem_primeFactors.mp hp).2.1
        (Subgroup.card_dvd_of_le hzc_le_N), Nat.card_pos.ne'⟩)
  have hc_K : (c : G) ∈ kSubgroup A :=
    mem_kSubgroup_of_piPrime_mem_centralizer hG hA hc_centralizer hc_pi'
  -- `R₂ := R₂'.map N.subtype` and its `ℋ_G*`-extension `Q₃`.
  set R₂ : Subgroup G := R₂'.map N.subtype with hR₂_def
  have hR₂_pi : Subgroup.IsPiSubgroup {q} R₂ := by
    intro p hp
    rw [hR₂_def] at hp
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective R₂' N.subtype
      N.subtype_injective).toEquiv] at hp
    exact hR₂'_hall.1 p hp
  have hR₂_norm : A ≤ Subgroup.normalizer R₂ := by
    rw [hR₂_def]
    exact isAInvariant_conjAction_iff.mp (isAInvariant_map_subtype_of_restrict hN_inv hR₂'_inv)
  obtain ⟨Q₃, hQ₃_star, hR₂_le_Q₃⟩ :=
    exists_le_hInvariantStar (H := ⊤) (A := A) (π := {q}) ⟨le_top, hR₂_norm, hR₂_pi⟩
  -- containments of `H ⊓ Qᵢ` in `Rᵢ`.
  have hHQ₁_le_R₁ : H ⊓ Q₁ ≤ R₁'.map N.subtype := by
    have h1 : ((H ⊓ Q₁).subgroupOf N).map N.subtype ≤ R₁'.map N.subtype :=
      Subgroup.map_mono hR₁'_ge
    rwa [Subgroup.map_subgroupOf_eq_of_le (hle_N Q₁ hQ₁)] at h1
  have hHQ₂_le_R₂ : H ⊓ Q₂ ≤ R₂ := by
    have h1 : ((H ⊓ Q₂).subgroupOf N).map N.subtype ≤ R₂'.map N.subtype :=
      Subgroup.map_mono hR₂'_ge
    rw [Subgroup.map_subgroupOf_eq_of_le (hle_N Q₂ hQ₂)] at h1
    rw [hR₂_def]; exact h1
  -- the conjugation/inf identity `(c • Q₁) ⊓ H = c • (Q₁ ⊓ H)`.
  have heq : (MulAut.conj (c : G) • Q₁) ⊓ H = MulAut.conj (c : G) • (Q₁ ⊓ H) := by
    rw [Subgroup.smul_inf, conj_smul_eq_self_of_mem_normalizer hc_norm_H]
  -- `R₂`-transport `(c • R₁) = R₂`.
  have htransport : MulAut.conj (c : G) • (R₁'.map N.subtype) = R₂ := by
    rw [hR₂_def, ← hc_conj, mulAut_smul_eq_map, mulAut_smul_eq_map, Subgroup.map_map,
        Subgroup.map_map]
    congr 1
  -- assemble.
  refine ⟨(c : G), hc_K, Q₃, hQ₃_star,
    conj_smul_mem_hInvariantStar_top hQ₁ hc_centralizer, ?_, ?_, ?_⟩
  · -- `(c • Q₁) ⊓ H ≤ Q₃`
    rw [heq]
    calc MulAut.conj (c : G) • (Q₁ ⊓ H)
        = MulAut.conj (c : G) • (H ⊓ Q₁) := by rw [inf_comm]
      _ ≤ MulAut.conj (c : G) • (R₁'.map N.subtype) := by
          rw [Subgroup.pointwise_smul_le_pointwise_smul_iff]; exact hHQ₁_le_R₁
      _ = R₂ := htransport
      _ ≤ Q₃ := hR₂_le_Q₃
  · -- `Q₂ ⊓ H ≤ Q₃`
    rw [inf_comm]; exact le_trans hHQ₂_le_R₂ hR₂_le_Q₃
  · -- card equality
    rw [heq]
    exact (Nat.card_congr (Subgroup.equivSMul (MulAut.conj (c : G)) (Q₁ ⊓ H)).toEquiv).symm

/-- **BG Lemma 7.1** (Inductive Lemma, mmd L2147): Hypothesis 7.1 のもと、`q ∈ π'`,
`Q₁, Q₂ ∈ ℋ_G*(A;q)`、`A ⊆ H < G` で `H ∩ Q₁ ≠ 1`, `H ∩ Q₂ ≠ 1` となる真部分群 `H` が
あれば、`Q₂ = Q₁^k` (`k ∈ K`)。`|G|_q / |Q₁∩Q₂|` の帰納が核。 -/
theorem inductiveLemma [Finite G] (hG : IsMinimalSimpleOdd G)
    {A : Subgroup G} (hA : Hypothesis71 A) {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    {Q₁ Q₂ : Subgroup G} (hQ₁ : Q₁ ∈ hInvariantStar ⊤ A {q})
    (hQ₂ : Q₂ ∈ hInvariantStar ⊤ A {q})
    (H : Subgroup G) (hHproper : H < ⊤) (hAH : A ≤ H)
    (hHQ₁ : H ⊓ Q₁ ≠ ⊥) (hHQ₂ : H ⊓ Q₂ ≠ ⊥) :
    ∃ k ∈ kSubgroup A, MulAut.conj k • Q₁ = Q₂ := by
  classical
  -- 強帰納法 on `|G| - |Q₁ ∩ Q₂|` (BG の `|G|_q/|Q₁∩Q₂|` と同値な減少測度)。
  suffices key : ∀ n : ℕ, ∀ Q₁ Q₂ : Subgroup G, Q₁ ∈ hInvariantStar ⊤ A {q} →
      Q₂ ∈ hInvariantStar ⊤ A {q} → Nat.card G - Nat.card ↥(Q₁ ⊓ Q₂) = n →
      ∀ H : Subgroup G, H < ⊤ → A ≤ H → H ⊓ Q₁ ≠ ⊥ → H ⊓ Q₂ ≠ ⊥ →
      ∃ k ∈ kSubgroup A, MulAut.conj k • Q₁ = Q₂ by
    exact key _ Q₁ Q₂ hQ₁ hQ₂ rfl H hHproper hAH hHQ₁ hHQ₂
  -- 汎用 card ヘルパー。
  have card_mono : ∀ {S T : Subgroup G}, S ≤ T → Nat.card ↥S ≤ Nat.card ↥T :=
    fun h => Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le h)
  have card_lt : ∀ {S T : Subgroup G}, S < T → Nat.card ↥S < Nat.card ↥T := by
    intro S T hST
    have h2 := Set.ncard_lt_ncard (SetLike.coe_ssubset_coe.mpr hST) (Set.toFinite _)
    rwa [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at h2
  have card_inf_le : ∀ S T : Subgroup G, Nat.card ↥(S ⊓ T) ≤ Nat.card G :=
    fun S T => Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card _)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q₁ Q₂ hQ₁ hQ₂ hmeasure H hHproper hAH hHQ₁ hHQ₂
    -- IH ラッパー: 交わりが増大 (= 測度減少) すれば再帰できる。
    have applyIH : ∀ Q₁' Q₂' : Subgroup G, Q₁' ∈ hInvariantStar ⊤ A {q} →
        Q₂' ∈ hInvariantStar ⊤ A {q} →
        Nat.card ↥(Q₁ ⊓ Q₂) < Nat.card ↥(Q₁' ⊓ Q₂') →
        ∀ H' : Subgroup G, H' < ⊤ → A ≤ H' → H' ⊓ Q₁' ≠ ⊥ → H' ⊓ Q₂' ≠ ⊥ →
        ∃ k ∈ kSubgroup A, MulAut.conj k • Q₁' = Q₂' := by
      intro Q₁' Q₂' hQ₁' hQ₂' hgt H' hH'p hAH' hne1 hne2
      have hlt : Nat.card G - Nat.card ↥(Q₁' ⊓ Q₂') < n := by
        have hle := card_inf_le Q₁' Q₂'; omega
      exact ih _ hlt Q₁' Q₂' hQ₁' hQ₂' rfl H' hH'p hAH' hne1 hne2
    -- 共通構成 (witness = 与えられた `H`)。
    obtain ⟨h, hh_K, Q₃, hQ₃, hconjQ₁, hstep1, hstep2, hcard⟩ :=
      commonConstruction hG hA hq hQ₁ hQ₂ hHproper hAH
    -- `(h • Q₁) ⊓ H` の非自明性。
    have hne_conj : (MulAut.conj h • Q₁) ⊓ H ≠ ⊥ := by
      intro hbot
      have h1 : Q₁ ⊓ H = ⊥ := by
        apply Subgroup.card_eq_one.mp
        rw [← hcard, hbot]; exact Subgroup.card_eq_one.mpr rfl
      exact hHQ₁ (by rw [inf_comm]; exact h1)
    by_cases hQinf : Q₁ ⊓ Q₂ = ⊥
    · -- Case A: `Q₁ ⊓ Q₂ = 1`. 共通構成を H で 1 回、合成 `k = g·f·h`。
      have hbig1 : (MulAut.conj h • Q₁) ⊓ Q₃ ≠ ⊥ := by
        intro hb
        have hle : (MulAut.conj h • Q₁) ⊓ H ≤ (MulAut.conj h • Q₁) ⊓ Q₃ :=
          le_inf inf_le_left hstep1
        rw [hb, le_bot_iff] at hle; exact hne_conj hle
      have hHQ₃ : H ⊓ Q₃ ≠ ⊥ := by
        intro hb
        apply hHQ₂
        have h2 : Q₂ ⊓ H ≤ H ⊓ Q₃ := le_inf inf_le_right hstep2
        rw [hb, le_bot_iff] at h2; rw [inf_comm]; exact h2
      have hbig2 : Q₂ ⊓ Q₃ ≠ ⊥ := by
        intro hb
        apply hHQ₂
        have h2 : Q₂ ⊓ H ≤ Q₂ ⊓ Q₃ := le_inf inf_le_left hstep2
        rw [hb, le_bot_iff] at h2; rw [inf_comm]; exact h2
      have hmes1 : Nat.card ↥(Q₁ ⊓ Q₂) < Nat.card ↥((MulAut.conj h • Q₁) ⊓ Q₃) := by
        rw [hQinf, Subgroup.card_eq_one.mpr rfl]
        exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hbig1
      have hmes2 : Nat.card ↥(Q₁ ⊓ Q₂) < Nat.card ↥(Q₃ ⊓ Q₂) := by
        rw [hQinf, Subgroup.card_eq_one.mpr rfl]
        refine (Subgroup.one_lt_card_iff_ne_bot _).mpr ?_
        rw [inf_comm]; exact hbig2
      obtain ⟨f, hf_K, hf_eq⟩ := applyIH (MulAut.conj h • Q₁) Q₃ hconjQ₁ hQ₃ hmes1
        H hHproper hAH (by rw [inf_comm]; exact hne_conj) hHQ₃
      obtain ⟨g, hg_K, hg_eq⟩ := applyIH Q₃ Q₂ hQ₃ hQ₂ hmes2 H hHproper hAH hHQ₃ hHQ₂
      refine ⟨g * f * h, (kSubgroup A).mul_mem ((kSubgroup A).mul_mem hg_K hf_K) hh_K, ?_⟩
      calc MulAut.conj (g * f * h) • Q₁
          = MulAut.conj g • (MulAut.conj f • (MulAut.conj h • Q₁)) := by
            rw [map_mul, map_mul, mul_smul, mul_smul]
        _ = MulAut.conj g • Q₃ := by rw [hf_eq]
        _ = Q₂ := hg_eq
    · -- Case B: `Q₁ ⊓ Q₂ ≠ 1`. `H' = N_G(Q)` で共通構成し、normalizer 増大で結論。
      have hQ₁_lt : Q₁ < ⊤ := lt_top_of_mem_hInvariantStar hG hQ₁
      have hQ_proper : Q₁ ⊓ Q₂ < ⊤ := lt_of_le_of_lt inf_le_left hQ₁_lt
      have hA_normQ : A ≤ Subgroup.normalizer ((Q₁ ⊓ Q₂ : Subgroup G) : Set G) := by
        intro a ha
        apply mem_normalizer_of_conj_smul_eq_self (Q := Q₁ ⊓ Q₂)
        rw [Subgroup.smul_inf,
            conj_smul_eq_self_of_mem_normalizer (hInvariantStar_le_normalizer hQ₁ ha),
            conj_smul_eq_self_of_mem_normalizer (hInvariantStar_le_normalizer hQ₂ ha)]
      have hNQ_lt : Subgroup.normalizer ((Q₁ ⊓ Q₂ : Subgroup G) : Set G) < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro htop
        have hnorm : (Q₁ ⊓ Q₂).Normal := Subgroup.normalizer_eq_top_iff.mp htop
        rcases hG.simple.eq_bot_or_eq_top_of_normal (Q₁ ⊓ Q₂) hnorm with hh | hh
        · exact hQinf hh
        · exact (ne_of_lt hQ_proper) hh
      obtain ⟨h, hh_K, Q₃, hQ₃, hconjQ₁, hstep1, hstep2, hcard⟩ :=
        commonConstruction hG hA hq hQ₁ hQ₂ hNQ_lt hA_normQ
      set NQ : Subgroup G := Subgroup.normalizer ((Q₁ ⊓ Q₂ : Subgroup G) : Set G) with hNQ_def
      have hQ_le_NQ : Q₁ ⊓ Q₂ ≤ NQ := Subgroup.le_normalizer
      have hQ_le_M₁ : Q₁ ⊓ Q₂ ≤ Q₁ ⊓ NQ := le_inf inf_le_left hQ_le_NQ
      have hQ_le_M₂ : Q₁ ⊓ Q₂ ≤ Q₂ ⊓ NQ := le_inf inf_le_right hQ_le_NQ
      have hcard1 : Nat.card ↥(Q₁ ⊓ NQ) ≤ Nat.card ↥((MulAut.conj h • Q₁) ⊓ Q₃) := by
        rw [← hcard]; exact card_mono (le_inf inf_le_left hstep1)
      have hcard2 : Nat.card ↥(Q₂ ⊓ NQ) ≤ Nat.card ↥(Q₂ ⊓ Q₃) :=
        card_mono (le_inf inf_le_left hstep2)
      have hPQ₁ : IsPGroup q ↥Q₁ :=
        OddOrder.Isaacs.Ch04.isPGroup_of_isPiGroup_singleton (hInvariantStar_isPiSubgroup hQ₁)
      have hPQ₂ : IsPGroup q ↥Q₂ :=
        OddOrder.Isaacs.Ch04.isPGroup_of_isPiGroup_singleton (hInvariantStar_isPiSubgroup hQ₂)
      by_cases hb1 : Nat.card ↥(Q₁ ⊓ Q₂) < Nat.card ↥((MulAut.conj h • Q₁) ⊓ Q₃) ∧
          Nat.card ↥(Q₁ ⊓ Q₂) < Nat.card ↥(Q₂ ⊓ Q₃)
      · -- B1: 両交わりが増大 → Case A と同じ合成 (witness = N_G(Q))。
        obtain ⟨hb1a, hb1b⟩ := hb1
        have hM₁_ne : Q₁ ⊓ NQ ≠ ⊥ := fun hb => hQinf (le_bot_iff.mp (hb ▸ hQ_le_M₁))
        have hM₂_ne : Q₂ ⊓ NQ ≠ ⊥ := fun hb => hQinf (le_bot_iff.mp (hb ▸ hQ_le_M₂))
        have hne_conjNQ : NQ ⊓ (MulAut.conj h • Q₁) ≠ ⊥ := by
          rw [inf_comm]
          intro hb
          apply hM₁_ne
          apply Subgroup.card_eq_one.mp
          rw [← hcard, hb]; exact Subgroup.card_eq_one.mpr rfl
        have hNQ_Q₃ : NQ ⊓ Q₃ ≠ ⊥ := by
          intro hb
          apply hM₂_ne
          have h2 : Q₂ ⊓ NQ ≤ NQ ⊓ Q₃ := le_inf inf_le_right hstep2
          rw [hb, le_bot_iff] at h2; exact h2
        have hNQ_Q₂ : NQ ⊓ Q₂ ≠ ⊥ := fun hb => hM₂_ne (by rw [inf_comm]; exact hb)
        obtain ⟨f, hf_K, hf_eq⟩ := applyIH (MulAut.conj h • Q₁) Q₃ hconjQ₁ hQ₃ hb1a
          NQ hNQ_lt hA_normQ hne_conjNQ hNQ_Q₃
        obtain ⟨g, hg_K, hg_eq⟩ := applyIH Q₃ Q₂ hQ₃ hQ₂
          (by rw [inf_comm Q₃ Q₂]; exact hb1b) NQ hNQ_lt hA_normQ hNQ_Q₃ hNQ_Q₂
        refine ⟨g * f * h, (kSubgroup A).mul_mem ((kSubgroup A).mul_mem hg_K hf_K) hh_K, ?_⟩
        calc MulAut.conj (g * f * h) • Q₁
            = MulAut.conj g • (MulAut.conj f • (MulAut.conj h • Q₁)) := by
              rw [map_mul, map_mul, mul_smul, mul_smul]
          _ = MulAut.conj g • Q₃ := by rw [hf_eq]
          _ = Q₂ := hg_eq
      · -- B2: 片方の交わりが増大しない → normalizer 増大より `Q = Qᵢ`、ゆえ `Q₁ = Q₂` (k = 1)。
        rw [not_and_or, not_lt, not_lt] at hb1
        have hle12 : Q₁ ≤ Q₂ ∨ Q₂ ≤ Q₁ := by
          rcases hb1 with hb | hb
          · left
            rw [← inf_eq_left]
            by_contra hne
            have hlt : Q₁ ⊓ Q₂ < Q₁ := lt_of_le_of_ne inf_le_left hne
            have hlt2 : Q₁ ⊓ Q₂ < Q₁ ⊓ NQ := lt_normalizer_inf_of_pgroup_lt hPQ₁ hlt
            have hgt := card_lt hlt2
            have hle' : Nat.card ↥(Q₁ ⊓ NQ) ≤ Nat.card ↥(Q₁ ⊓ Q₂) := le_trans hcard1 hb
            omega
          · right
            rw [← inf_eq_right]
            by_contra hne
            have hlt : Q₁ ⊓ Q₂ < Q₂ := lt_of_le_of_ne inf_le_right hne
            have hlt2 : Q₁ ⊓ Q₂ < Q₂ ⊓ NQ := lt_normalizer_inf_of_pgroup_lt hPQ₂ hlt
            have hgt := card_lt hlt2
            have hle' : Nat.card ↥(Q₂ ⊓ NQ) ≤ Nat.card ↥(Q₁ ⊓ Q₂) := le_trans hcard2 hb
            omega
        have hQ₁Q₂ : Q₁ = Q₂ := by
          rcases hle12 with hle | hle
          · exact (hInvariantStar_eq_of_le hQ₁ (hInvariantStar_mem_hInvariant hQ₂) hle).symm
          · exact hInvariantStar_eq_of_le hQ₂ (hInvariantStar_mem_hInvariant hQ₁) hle
        exact ⟨1, one_mem _, by rw [hQ₁Q₂, map_one, one_smul]⟩

/-- `actionFixedBy` of the conjugation action of `B` on `Q` (= `C_Q(x) = Q ⊓ C_G(x)` in
`subgroupOf` form). -/
theorem actionFixedBy_conjAction_restrict {B Q : Subgroup G}
    (hQ_inv : Ch03.IsAInvariant (conjAction B) Q) (x : ↥B) :
    actionFixedBy hQ_inv.restrict x
      = (Q ⊓ Subgroup.centralizer ({(x : G)} : Set G)).subgroupOf Q := by
  ext g
  rw [mem_actionFixedBy, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h
    refine ⟨g.2, Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)⟩
    rw [Set.mem_singleton_iff] at hy; subst hy
    have hval : ((hQ_inv.restrict x) g : G) = (g : G) := congrArg Subtype.val h
    rw [Ch03.IsAInvariant.restrict_apply_val] at hval
    simp only [conjAction, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conj_apply] at hval
    exact mul_inv_eq_iff_eq_mul.mp hval
  · rintro ⟨-, hgC⟩
    apply Subtype.ext
    rw [Ch03.IsAInvariant.restrict_apply_val]
    simp only [conjAction, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conj_apply]
    rw [Subgroup.mem_centralizer_iff.mp hgC (x : G) (Set.mem_singleton _)]; group

/-- **BG Prop 1.16(1), conjugation form**: a noncyclic abelian subgroup `B ≤ G` normalizing a
coprime subgroup `Q ≠ 1` has a nonidentity element `x` with `Q ⊓ C_G(x) ≠ 1`. (If every
`C_Q(x)` were trivial the centralizers would generate only `1`, contradicting Isaacs 6.21.) -/
theorem exists_mem_inf_centralizer_ne_bot_of_not_isCyclic [Finite G]
    {B Q : Subgroup G} [IsMulCommutative ↥B] (hBQ : B ≤ Subgroup.normalizer Q)
    (hB_nc : ¬ IsCyclic ↥B) (hCop : Nat.Coprime (Nat.card ↥B) (Nat.card ↥Q)) (hQ : Q ≠ ⊥) :
    ∃ x ∈ B, x ≠ (1 : G) ∧ Q ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
  classical
  have hQ_inv : Ch03.IsAInvariant (conjAction B) Q := isAInvariant_conjAction_iff.mpr hBQ
  have htop := OddOrder.BG.Ch1.S01.nontrivialActionFixedByClosure_eq_top_of_not_isCyclic'
    hQ_inv.restrict hCop hB_nc
  by_contra hcon
  have hle : nontrivialActionFixedByClosure hQ_inv.restrict ≤ ⊥ := by
    rw [nontrivialActionFixedByClosure_le_iff]
    intro x hx_ne
    rw [actionFixedBy_conjAction_restrict]
    have hxbot : Q ⊓ Subgroup.centralizer ({(x : G)} : Set G) = ⊥ := by
      by_contra hne
      exact hcon ⟨(x : G), x.2, fun h => hx_ne (Subtype.ext (by rw [h]; rfl)), hne⟩
    rw [hxbot, Subgroup.bot_subgroupOf]
  rw [htop, top_le_iff] at hle
  have : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ
  exact bot_ne_top hle

/-- **BG Prop 1.16(2), conjugation form**: a noncyclic abelian `B ≤ G` normalizing a coprime
`Q ≠ 1` has a subgroup `Y ≤ B` with `B/Y` cyclic (`Y ⊔ ⟨b⟩ = B`) and `Q ⊓ C_G(Y) ≠ 1`. -/
theorem exists_cocyclic_inf_centralizer_ne_bot_of_not_isCyclic [Finite G]
    {B Q : Subgroup G} [IsMulCommutative ↥B] (hBQ : B ≤ Subgroup.normalizer Q)
    (hB_nc : ¬ IsCyclic ↥B) (hCop : Nat.Coprime (Nat.card ↥B) (Nat.card ↥Q)) (hQ : Q ≠ ⊥) :
    ∃ Y : Subgroup G, Y ≤ B ∧ (∃ b ∈ B, Y ⊔ Subgroup.zpowers b = B) ∧
      Q ⊓ Subgroup.centralizer (Y : Set G) ≠ ⊥ := by
  classical
  have hQ_inv : Ch03.IsAInvariant (conjAction B) Q := isAInvariant_conjAction_iff.mpr hBQ
  have htop := OddOrder.BG.Ch1.S01.cocyclicFixedByClosure_eq_top_of_not_isCyclic
    hQ_inv.restrict hCop hB_nc
  by_contra hcon
  push Not at hcon
  have hle : OddOrder.BG.Ch1.S01.cocyclicFixedByClosure hQ_inv.restrict ≤ ⊥ := by
    rw [OddOrder.BG.Ch1.S01.cocyclicFixedByClosure, Subgroup.closure_le]
    rintro g ⟨Yb, ⟨b, hb⟩, hYfix⟩
    set Y : Subgroup G := Yb.map B.subtype with hYdef
    have hYcocyc : ∃ b' ∈ B, Y ⊔ Subgroup.zpowers b' = B := by
      refine ⟨(b : G), b.2, ?_⟩
      have hzp : Subgroup.zpowers (b : G) = (Subgroup.zpowers b).map B.subtype :=
        (MonoidHom.map_zpowers B.subtype b).symm
      rw [hYdef, hzp, ← Subgroup.map_sup, hb, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hmemG : (g : G) ∈ Q ⊓ Subgroup.centralizer (Y : Set G) := by
      refine ⟨g.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro y hy
      rw [hYdef, Subgroup.coe_map, Set.mem_image] at hy
      obtain ⟨yb, hyb, rfl⟩ := hy
      have hval : ((hQ_inv.restrict yb) g : G) = (g : G) := congrArg Subtype.val (hYfix yb hyb)
      rw [Ch03.IsAInvariant.restrict_apply_val] at hval
      simp only [conjAction, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conj_apply] at hval
      exact mul_inv_eq_iff_eq_mul.mp hval
    rw [hcon Y (Subgroup.map_subtype_le _) hYcocyc] at hmemG
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hmemG))
  rw [htop, top_le_iff] at hle
  have : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ
  exact bot_ne_top hle

/-- `n ≤ rank G` で `n > 0` なら、ある素数 `p` で `n ≤ pRank G p` (`rank_le_iff` の逆向き)。 -/
private theorem exists_le_pRank_of_le_rank {H : Type*} [Group H] [Finite H] {n : ℕ}
    (hn : 0 < n) (h : n ≤ rank H) : ∃ p : ℕ, n ≤ pRank H p := by
  by_contra hcon
  push Not at hcon
  have : rank H ≤ n - 1 := by
    rw [rank_le_iff]; intro p; have := hcon p; omega
  omega

/-- **`m(Z(A)) ≥ n` (n ≥ 2) から `Z(A)` 内の noncyclic elementary abelian 部分群を抽出**:
ある `p ≥ 2` と `B ≤ A`, `B ≤ C_G(A)` (= `B ≤ Z(A)`) で `B` は elementary abelian `p`, noncyclic,
`n ≤ log_p |B|`。Thm 7.2/7.3 の `B ∈ ℰ_p^n(Z(A))` 部分。`B ≤ A` から coprimality (`q ∈ π'` で
`q ∤ |B|`) が従うので `p` の素数性は不要。 -/
private theorem exists_elementaryAbelian_le_center_of_le_rank [Finite G]
    {A : Subgroup G} {n : ℕ} (hn2 : 2 ≤ n) (hm : n ≤ rank ↥(Subgroup.center ↥A)) :
    ∃ (p : ℕ) (B : Subgroup G), B.IsElementaryAbelian p ∧ ¬ IsCyclic ↥B ∧
      n ≤ Nat.log p (Nat.card ↥B) ∧ B ≤ A ∧ B ≤ Subgroup.centralizer (A : Set G) := by
  classical
  set ZA : Subgroup G := (Subgroup.center ↥A).map A.subtype with hZA
  have hrankZA : n ≤ rank ↥ZA :=
    le_trans hm (rank_le_of_injective
      (f := (Subgroup.equivMapOfInjective (Subgroup.center ↥A) A.subtype
        A.subtype_injective).toMonoidHom)
      (Subgroup.equivMapOfInjective (Subgroup.center ↥A) A.subtype A.subtype_injective).injective)
  obtain ⟨p, hp_rank⟩ := exists_le_pRank_of_le_rank (by omega) hrankZA
  obtain ⟨B₀, hB₀_ea, hB₀_log⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank (by omega : 0 < n) hp_rank
  have hp2 : 2 ≤ p := by
    rcases Nat.lt_or_ge p 2 with hlt | hge
    · exfalso
      have h0 : pRank ↥ZA p ≤ 0 := by
        rw [pRank_le_iff]; intro A' _; rw [Nat.log_of_left_le_one (by omega)]
      omega
    · exact hge
  set B : Subgroup G := B₀.map ZA.subtype with hB
  have hB_ea : B.IsElementaryAbelian p := Subgroup.IsElementaryAbelian.map ZA.subtype_injective
      hB₀_ea
  have hlogB : n ≤ Nat.log p (Nat.card ↥B) := by
    rw [hB, Subgroup.card_map_of_injective ZA.subtype_injective]; exact hB₀_log
  refine ⟨p, B, hB_ea, ?_, hlogB, le_trans (Subgroup.map_subtype_le _) (Subgroup.map_subtype_le _),
    ?_⟩
  · -- ¬ IsCyclic: exponent ∣ p but |B| ≥ p² > p.
    intro hcyc
    have hexp : Monoid.exponent ↥B = Nat.card ↥B := hcyc.exponent_eq_card
    have hdvd : Monoid.exponent ↥B ∣ p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]; exact hB_ea.pow_eq_one
    rw [hexp] at hdvd
    have hcard_le : Nat.card ↥B ≤ p := Nat.le_of_dvd (by omega) hdvd
    have hp_sq : p ^ 2 ≤ Nat.card ↥B :=
      (Nat.le_log_iff_pow_le (by omega) Nat.card_pos.ne').mp (le_trans hn2 hlogB)
    rw [pow_two] at hp_sq; nlinarith
  · refine le_trans (Subgroup.map_subtype_le _) ?_
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨a, ha⟩)

/-- A cocyclic subgroup `Y` (`Y ⊔ ⟨b⟩ = B`) of an elementary abelian `p`-group `B` of rank
`≥ 3` is noncyclic: `|B| ≤ |Y|·|⟨b⟩| ≤ |Y|·p`, so `|Y| ≥ p²`. -/
private theorem not_isCyclic_of_cocyclic [Finite G] {p : ℕ} (hp2 : 2 ≤ p) {B Y : Subgroup G}
    (hB_ea : B.IsElementaryAbelian p) (hlog : 3 ≤ Nat.log p (Nat.card ↥B))
    (hYB : Y ≤ B) {b : G} (hb : b ∈ B) (hsup : Y ⊔ Subgroup.zpowers b = B) :
    ¬ IsCyclic ↥Y := by
  classical
  have : IsMulCommutative ↥B := IsMulCommutative.of_comm hB_ea.1
  set Y' : Subgroup ↥B := Y.subgroupOf B with hY'
  set K : Subgroup ↥B := (Subgroup.zpowers b).subgroupOf B with hK
  have : Y'.Normal := Subgroup.normal_of_isMulCommutative _
  have hzple : Subgroup.zpowers b ≤ B := Subgroup.zpowers_le.mpr hb
  have hsup' : Y' ⊔ K = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_sup, hY', hK, Subgroup.map_subgroupOf_eq_of_le hYB,
      Subgroup.map_subgroupOf_eq_of_le hzple, hsup, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype]
  have hKle : Nat.card ↥K ≤ p := by
    rw [hK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzple).toEquiv, Nat.card_zpowers]
    refine Nat.le_of_dvd (by omega : 0 < p) (orderOf_dvd_of_pow_eq_one ?_)
    have hbp := congrArg Subtype.val (hB_ea.2 (⟨b, hb⟩ : ↥B)); simpa using hbp
  have hKmap : K.map (QuotientGroup.mk' Y') = ⊤ := by
    have h1 : (Y' ⊔ K).map (QuotientGroup.mk' Y') = ⊤ := by
      rw [hsup', Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Y')]
    rwa [Subgroup.map_sup,
      (Subgroup.map_eq_bot_iff Y').mpr (le_of_eq (QuotientGroup.ker_mk' Y').symm),
      bot_sup_eq] at h1
  have hquot_le : Nat.card (↥B ⧸ Y') ≤ Nat.card ↥K :=
    Nat.card_le_card_of_surjective ((QuotientGroup.mk' Y').comp K.subtype) (by
      intro x
      obtain ⟨k, hk, hkx⟩ := hKmap ▸ Subgroup.mem_top x
      exact ⟨⟨k, hk⟩, hkx⟩)
  have hcardB : Nat.card ↥B ≤ Nat.card ↥K * Nat.card ↥Y := by
    have hY'card : Nat.card ↥Y' = Nat.card ↥Y :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYB).toEquiv
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Y', hY'card]
    exact Nat.mul_le_mul_right _ hquot_le
  intro hcyc
  -- `Y` is elementary abelian and cyclic, so `|Y| ≤ p`.
  have hY_ea : Y.IsElementaryAbelian p := by
    refine ⟨fun x y => Subtype.ext ?_, fun x => Subtype.ext ?_⟩
    · change (x : G) * (y : G) = (y : G) * (x : G)
      exact congrArg (Subtype.val : ↥B → G) (hB_ea.1 ⟨(x : G), hYB x.2⟩ ⟨(y : G), hYB y.2⟩)
    · change (x : G) ^ p = 1
      exact congrArg (Subtype.val : ↥B → G) (hB_ea.2 (⟨(x : G), hYB x.2⟩ : ↥B))
  have hYle : Nat.card ↥Y ≤ p := by
    have hdvd : Monoid.exponent ↥Y ∣ p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]; exact hY_ea.2
    rw [← hcyc.exponent_eq_card]; exact Nat.le_of_dvd (by omega : 0 < p) hdvd
  have hp3 : p ^ 3 ≤ Nat.card ↥B :=
    (Nat.le_log_iff_pow_le (by omega : 1 < p) Nat.card_pos.ne').mp hlog
  have h1 : Nat.card ↥B ≤ p ^ 2 := by
    rw [pow_two]; exact le_trans hcardB (Nat.mul_le_mul hKle hYle)
  have h2 : p ^ 2 < p ^ 3 :=
    Nat.pow_lt_pow_right (by omega : 1 < p) (by norm_num)
  omega

/-- `C_G(x) < ⊤` for `x ≠ 1` in a minimal simple group (`Z(G) = 1`). -/
theorem centralizer_singleton_lt_top [Finite G] (hG : IsMinimalSimpleOdd G) {x : G}
    (hx : x ≠ (1 : G)) : Subgroup.centralizer ({x} : Set G) < ⊤ := by
  have hZbot : Subgroup.center G = ⊥ := by
    rcases hG.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with h | h
    · exact h
    · exact absurd (Group.isSolvable_of_comm fun a b =>
        (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm) hG.notSolvable
  rw [lt_top_iff_ne_top]
  intro htop
  refine hx (Subgroup.mem_bot.mp (hZbot ▸ ?_))
  rw [Subgroup.mem_center_iff]
  intro g
  exact (Subgroup.mem_centralizer_iff.mp (htop ▸ Subgroup.mem_top g) x (Set.mem_singleton x)).symm

/-- **BG Theorem 7.2** (mmd L2177): Hypothesis 7.1, `q ∈ π'`, `m(Z(A)) ≥ 3` ⇒ `K` は
`ℋ_G*(A;q)` 上推移的。Prop 1.16(2) で `B ∈ ℰ_p³(Z(A))` から cocyclic `Y` (noncyclic) を取り、
`C_{Q₁}(Y) ⊆ C_G(z)` (z∈Y) で Lem 7.1 を適用。 -/
theorem transitive_of_three_le_rank_center [Finite G] (hG : IsMinimalSimpleOdd G)
    {A : Subgroup G} (hA : Hypothesis71 A) {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    (hm : 3 ≤ rank ↥(Subgroup.center ↥A)) :
    ConjTransitiveOn (kSubgroup A) (hInvariantStar ⊤ A {q}) := by
  classical
  have hCop : ∀ {S Q : Subgroup G}, S ≤ A → Q ∈ hInvariantStar ⊤ A {q} →
      Nat.Coprime (Nat.card ↥S) (Nat.card ↥Q) := by
    intro S Q hSA hQ
    refine OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := primesOf A) Nat.card_pos.ne' Nat.card_pos.ne' (fun r hr => ?_) (fun r hr => ?_)
    · exact Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hr).1,
        dvd_trans (Nat.mem_primeFactors.mp hr).2.1 (Subgroup.card_dvd_of_le hSA), Nat.card_pos.ne'⟩
    · rw [Set.mem_singleton_iff.mp (hInvariantStar_isPiSubgroup hQ r hr)]; exact hq
  have hA_Cz : ∀ z : G, z ∈ Subgroup.centralizer (A : Set G) →
      A ≤ Subgroup.centralizer ({z} : Set G) := by
    intro z hz a ha
    rw [Subgroup.mem_centralizer_iff]
    rintro y hy; rw [Set.mem_singleton_iff] at hy; subst hy
    exact (Subgroup.mem_centralizer_iff.mp hz a ha).symm
  obtain ⟨p, B, hB_ea, hB_nc, hB_log, hBA, hB_cent⟩ :=
    exists_elementaryAbelian_le_center_of_le_rank (n := 3) (by norm_num) hm
  have hp2 : 2 ≤ p := by
    by_contra h; push Not at h
    rw [Nat.log_of_left_le_one (by omega)] at hB_log; omega
  intro Q₁ hQ₁ Q₂ hQ₂
  by_cases hQ₁bot : Q₁ = ⊥
  · refine ⟨1, one_mem _, ?_⟩
    rw [map_one, one_smul]
    exact (hQ₁.2 Q₂ (hInvariantStar_mem_hInvariant hQ₂) (by rw [hQ₁bot]; exact bot_le)).symm
  · have hQ₂bot : Q₂ ≠ ⊥ := fun h =>
      hQ₁bot ((hQ₂.2 Q₁ (hInvariantStar_mem_hInvariant hQ₁) (by rw [h]; exact bot_le)).trans h)
    have : IsMulCommutative ↥B := IsMulCommutative.of_comm hB_ea.1
    obtain ⟨Y, hYB, ⟨b, hbB, hsup⟩, hYQ₁⟩ :=
      exists_cocyclic_inf_centralizer_ne_bot_of_not_isCyclic
        (le_trans hBA (hInvariantStar_le_normalizer hQ₁)) hB_nc (hCop hBA hQ₁) hQ₁bot
    have hY_nc : ¬ IsCyclic ↥Y := not_isCyclic_of_cocyclic hp2 hB_ea hB_log hYB hbB hsup
    have : IsMulCommutative ↥Y :=
      IsMulCommutative.of_comm fun x y => Subtype.ext (by
        change (x : G) * (y : G) = (y : G) * (x : G)
        exact congrArg (Subtype.val : ↥B → G) (hB_ea.1 ⟨(x : G), hYB x.2⟩ ⟨(y : G), hYB y.2⟩))
    have hYA : Y ≤ A := le_trans hYB hBA
    obtain ⟨z, hzY, hz_ne, hzQ₂⟩ :=
      exists_mem_inf_centralizer_ne_bot_of_not_isCyclic
        (le_trans hYA (hInvariantStar_le_normalizer hQ₂)) hY_nc (hCop hYA hQ₂) hQ₂bot
    have hHQ₁ : Subgroup.centralizer ({z} : Set G) ⊓ Q₁ ≠ ⊥ := by
      rw [inf_comm]
      refine fun h => hYQ₁ (le_bot_iff.mp ?_)
      rw [← h]
      exact le_inf inf_le_left (le_trans inf_le_right
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzY)))
    obtain ⟨k, hk_K, hk_eq⟩ := inductiveLemma hG hA hq hQ₁ hQ₂
      (Subgroup.centralizer ({z} : Set G)) (centralizer_singleton_lt_top hG hz_ne)
      (hA_Cz z (le_trans hYB hB_cent hzY)) hHQ₁ (by rw [inf_comm]; exact hzQ₂)
    exact ⟨k, hk_K, hk_eq⟩

/-- If `K = O_{π'}(C_G(A))` is trivial, Theorem 7.2 makes `ℋ_G*(A;q)`
a singleton. This is the reusable form of the first conclusion in BG (8.6). -/
theorem hInvariantStar_eq_of_three_le_rank_center_of_kSubgroup_eq_bot [Finite G]
    (hG : IsMinimalSimpleOdd G) {A : Subgroup G} (hA : Hypothesis71 A)
    {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    (hm : 3 ≤ rank ↥(Subgroup.center ↥A)) (hKbot : kSubgroup A = ⊥)
    {Q₁ Q₂ : Subgroup G} (hQ₁ : Q₁ ∈ hInvariantStar ⊤ A {q})
    (hQ₂ : Q₂ ∈ hInvariantStar ⊤ A {q}) :
    Q₁ = Q₂ :=
  hInvariantStar_eq_of_conjTransitiveOn_bot hKbot
    (transitive_of_three_le_rank_center hG hA hq hm) hQ₁ hQ₂

/-- If C_G(A) is a pi(A)-subgroup, Theorem 7.2 makes H_G*(A;q) a singleton.
This packages the kSubgroup-triviality bridge needed in BG (8.6). -/
theorem hInvariantStar_eq_of_three_le_rank_center_of_centralizer_isPiSubgroup [Finite G]
    (hG : IsMinimalSimpleOdd G) {A : Subgroup G} (hA : Hypothesis71 A)
    {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    (hm : 3 ≤ rank ↥(Subgroup.center ↥A))
    (hCpi : Subgroup.IsPiSubgroup (primesOf A) (Subgroup.centralizer (A : Set G)))
    {Q₁ Q₂ : Subgroup G} (hQ₁ : Q₁ ∈ hInvariantStar ⊤ A {q})
    (hQ₂ : Q₂ ∈ hInvariantStar ⊤ A {q}) :
    Q₁ = Q₂ :=
  hInvariantStar_eq_of_three_le_rank_center_of_kSubgroup_eq_bot hG hA hq hm
    (kSubgroup_eq_bot_of_centralizer_isPiSubgroup hCpi) hQ₁ hQ₂

set_option backward.isDefEq.respectTransparency false in
/-- **BG Theorem 7.3** (mmd L2187): Hypothesis 7.1, `q ∈ π'`, `m(Z(A)) ≥ 2` かつ
`q ∈ π(C_G(A))` ⇒ `K` は `ℋ_G*(A;q)` 上推移的。`R ⊇ Sylow_q(C_G(A))` 経由で Lem 7.1 を連鎖。 -/
theorem transitive_of_two_le_rank_center_of_dvd [Finite G] (hG : IsMinimalSimpleOdd G)
    {A : Subgroup G} (hA : Hypothesis71 A) {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    (hm : 2 ≤ rank ↥(Subgroup.center ↥A))
    (hqc : q ∈ (Nat.card ↥(Subgroup.centralizer (A : Set G))).primeFactors) :
    ConjTransitiveOn (kSubgroup A) (hInvariantStar ⊤ A {q}) := by
  classical
  -- `Z(G) = 1` (nonabelian simple), so `C_G(x) < ⊤` for `x ≠ 1`.
  have hZbot : Subgroup.center G = ⊥ := by
    rcases hG.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with h | h
    · exact h
    · exact absurd (Group.isSolvable_of_comm fun a b =>
        (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm) hG.notSolvable
  have hCGx_proper : ∀ x : G, x ≠ 1 → Subgroup.centralizer ({x} : Set G) < ⊤ := by
    intro x hx
    rw [lt_top_iff_ne_top]
    intro htop
    refine hx (Subgroup.mem_bot.mp (hZbot ▸ ?_))
    rw [Subgroup.mem_center_iff]
    intro g
    exact (Subgroup.mem_centralizer_iff.mp (htop ▸ Subgroup.mem_top g) x (Set.mem_singleton x)).symm
  -- `B ≤ Z(A)` noncyclic elementary abelian.
  obtain ⟨p, B, hB_ea, hB_nc, _hB_log, hBA, hB_cent⟩ :=
    exists_elementaryAbelian_le_center_of_le_rank (n := 2) le_rfl hm
  have : IsMulCommutative ↥B := IsMulCommutative.of_comm hB_ea.1
  -- coprimality `(|B|, |Q|) = 1` for any `Q ∈ ℋ_G*(A;q)`.
  have hCop_BQ : ∀ Q : Subgroup G, Q ∈ hInvariantStar ⊤ A {q} →
      Nat.Coprime (Nat.card ↥B) (Nat.card ↥Q) := by
    intro Q hQ
    refine OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := primesOf A) Nat.card_pos.ne' Nat.card_pos.ne' (fun r hr => ?_) (fun r hr => ?_)
    · exact Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hr).1,
        dvd_trans (Nat.mem_primeFactors.mp hr).2.1 (Subgroup.card_dvd_of_le hBA), Nat.card_pos.ne'⟩
    · rw [Set.mem_singleton_iff.mp (hInvariantStar_isPiSubgroup hQ r hr)]; exact hq
  -- `B` normalizes every `Q ∈ ℋ_G*(A;q)` (via `B ≤ A`).
  have hBnorm : ∀ Q : Subgroup G, Q ∈ hInvariantStar ⊤ A {q} → B ≤ Subgroup.normalizer Q :=
    fun Q hQ => le_trans hBA (hInvariantStar_le_normalizer hQ)
  -- Cauchy: a nonidentity `A`-invariant `q`-subgroup `cc ≤ C_G(A)`.
  obtain ⟨c, hc_ord⟩ :=
    exists_prime_orderOf_dvd_card' q (G := ↥(Subgroup.centralizer (A : Set G)))
      (Nat.mem_primeFactors.mp hqc).2.1
  set cc : Subgroup G := Subgroup.zpowers (c : G) with hcc
  have hc_mem : (c : G) ∈ Subgroup.centralizer (A : Set G) := c.2
  have hcc_le_cent : cc ≤ Subgroup.centralizer (A : Set G) := Subgroup.zpowers_le.mpr hc_mem
  have hcc_card : Nat.card ↥cc = q := by
    rw [hcc, Nat.card_zpowers]
    exact (orderOf_injective (Subgroup.centralizer (A : Set G)).subtype
      (Subgroup.subtype_injective _) c).trans hc_ord
  have hcc_ne : cc ≠ ⊥ := by
    intro h; rw [h, Subgroup.card_bot] at hcc_card
    exact (Nat.Prime.one_lt (Fact.out : q.Prime)).ne hcc_card
  have hcc_mem : cc ∈ hInvariant ⊤ A {q} := by
    refine ⟨le_top, ?_, ?_⟩
    · intro a ha
      apply mem_normalizer_of_conj_smul_eq_self
      have hac : a * (c : G) * a⁻¹ = (c : G) := by
        rw [Subgroup.mem_centralizer_iff.mp hc_mem a ha, mul_inv_cancel_right]
      ext y
      rw [Subgroup.pointwise_smul_def, Subgroup.mem_map]
      constructor
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
        change (c : G) ^ n = MulAut.conj a ((c : G) ^ n)
        rw [map_zpow]; simp only [MulAut.conj_apply]; rw [hac]
      · intro hy
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact ⟨(c : G) ^ n, Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩, by
          change MulAut.conj a ((c : G) ^ n) = y
          rw [map_zpow]; simp only [MulAut.conj_apply]; rw [hac, hn]⟩
    · intro r hr
      rw [hcc_card] at hr
      rw [Set.mem_singleton_iff,
        ← Finset.mem_singleton, ← Nat.Prime.primeFactors (Fact.out : q.Prime)]
      exact hr
  -- every `Q ∈ ℋ_G*(A;q)` is nontrivial.
  have hQne : ∀ Q : Subgroup G, Q ∈ hInvariantStar ⊤ A {q} → Q ≠ ⊥ := by
    intro Q hQ hQbot
    have heq : cc = Q := hQ.2 cc hcc_mem (by rw [hQbot]; exact bot_le)
    rw [hQbot] at heq; exact hcc_ne heq
  -- `A ≤ C_G(x)` and `C_R(x) ≠ 1` for `x ∈ B`.
  have hA_CGx : ∀ x ∈ B, A ≤ Subgroup.centralizer ({x} : Set G) := by
    intro x hx a ha
    rw [Subgroup.mem_centralizer_iff]
    rintro y hy; rw [Set.mem_singleton_iff] at hy; subst hy
    exact (Subgroup.mem_centralizer_iff.mp (hB_cent hx) a ha).symm
  -- main transitivity.
  intro Q₁ hQ₁ Q₂ hQ₂
  obtain ⟨R, hR_mem, hcc_le_R⟩ := exists_le_hInvariantStar hcc_mem
  have hCRx : ∀ x ∈ B, R ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
    intro x hx h
    refine hcc_ne (le_bot_iff.mp ?_)
    rw [← h]
    exact le_inf hcc_le_R
      (le_trans hcc_le_cent (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (hBA hx))))
  obtain ⟨x, hxB, hx_ne, hQ₁x⟩ :=
    exists_mem_inf_centralizer_ne_bot_of_not_isCyclic (hBnorm Q₁ hQ₁) hB_nc (hCop_BQ Q₁ hQ₁)
      (hQne Q₁ hQ₁)
  obtain ⟨f, hf_K, hf_eq⟩ := inductiveLemma hG hA hq hQ₁ hR_mem
    (Subgroup.centralizer ({x} : Set G)) (hCGx_proper x hx_ne) (hA_CGx x hxB)
    (by rw [inf_comm]; exact hQ₁x) (by rw [inf_comm]; exact hCRx x hxB)
  obtain ⟨x', hx'B, hx'_ne, hQ₂x'⟩ :=
    exists_mem_inf_centralizer_ne_bot_of_not_isCyclic (hBnorm Q₂ hQ₂) hB_nc (hCop_BQ Q₂ hQ₂)
      (hQne Q₂ hQ₂)
  obtain ⟨g, hg_K, hg_eq⟩ := inductiveLemma hG hA hq hR_mem hQ₂
    (Subgroup.centralizer ({x'} : Set G)) (hCGx_proper x' hx'_ne) (hA_CGx x' hx'B)
    (by rw [inf_comm]; exact hCRx x' hx'B) (by rw [inf_comm]; exact hQ₂x')
  exact ⟨g * f, (kSubgroup A).mul_mem hg_K hf_K, by rw [map_mul, mul_smul, hf_eq]; exact hg_eq⟩

end OddOrder.BG.Ch2.S07


