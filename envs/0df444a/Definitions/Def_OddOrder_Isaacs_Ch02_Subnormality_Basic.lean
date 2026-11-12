-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch02_Subnormality_Basic
-- name    : OddOrder_Isaacs_Ch02_Subnormality_Basic
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:49:48.662362+00:00
-- url     : https://prove2.me/theorems/b304e4a8-8925-4c96-98f4-22ff5f9ac2cf
-- title:
--   Isaacs Ch. 2: minimal normal subgroups, socle, and Wielandt's zipper lemma
-- statement:
--   The basic part of the Chapter 2 (Subnormality) formalization of Isaacs, *Finite Group Theory*. It defines minimal normal subgroups and the socle, and proves Wielandt's Zipper Lemma (Isaacs Thm 2.9).
--
--   Main definitions: `IsMinimalNormal` (a nontrivial normal subgroup of $G$ properly containing no nontrivial $G$-normal subgroup), `socle` (the join of all minimal normal subgroups, shown normal and characteristic), and `zipper_lemma`.
--
--   The bundle also proves 11 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch02_Subnormality/Basic.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch02_Subnormality/Basic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch01_Sylow_Main
import Mathlib.GroupTheory.IsSubnormal

open OddOrder.Isaacs.Ch01

namespace OddOrder.Isaacs.Ch02

section

variable {G : Type*} [Group G]

/-- **Minimal normal subgroup**: `M` が `G` の非自明正規部分群で、`M` に真に含まれる
`G`-正規部分群は `⊥` のみ。

mathlib 未収載 (`IsAtom` は subgroup lattice 全体に対するもので normal lattice
には対応しない). Isaacs Thm 2.6, 2.18 (Zenkov) で必須。 -/
def IsMinimalNormal (M : Subgroup G) : Prop :=
  M.Normal ∧ M ≠ ⊥ ∧ ∀ N : Subgroup G, N.Normal → N ≤ M → N = ⊥ ∨ N = M

/-- **Isaacs Lemma 2.1, hard direction** (nilpotent ⇒ every subgroup subnormal).

`H.index` についての強induction。`H = ⊤` ならば trivially top。さもなくば
NormalizerCondition (Thm 1.26) で `H < N_G(H)`，`N_G(H).index < H.index` なので
帰納仮定 → `N_G(H).IsSubnormal` → `IsSubnormal.step` で `H.IsSubnormal`。

`H` のなかで `H ⊴ N_G(H)` は `Subgroup.normal_subgroupOf_iff_le_normalizer le_normalizer`
で，K = N_G(H) のときは `K = normalizer K` ではないが `H ≤ normalizer H` から
`(H.subgroupOf normalizer H).Normal` が出る。 -/
theorem isSubnormal_of_isNilpotent_finite [Finite G] [Group.IsNilpotent G]
    (H : Subgroup G) : H.IsSubnormal := by
  classical
  -- Strong induction on H.index.
  induction hN : H.index using Nat.strong_induction_on generalizing H with
  | _ n ih =>
    by_cases hHt : H = ⊤
    · rw [hHt]; exact Subgroup.IsSubnormal.top
    · -- H < ⊤ via hHt; NormalizerCondition gives H < N_G(H).
      have hNC : NormalizerCondition G :=
        ((Group.isNilpotent_of_finite_tfae (G := G)).out 0 1).mp ‹_›
      have hHlt : H < ⊤ := lt_top_iff_ne_top.mpr hHt
      have hH_lt_N : H < Subgroup.normalizer (H : Set G) := hNC H hHlt
      -- (normalizer H).index < H.index
      have hidx : (Subgroup.normalizer (H : Set G)).index < n := by
        rw [← hN]
        exact Subgroup.index_strictAnti hH_lt_N
      -- Apply induction hypothesis to normalizer H.
      have hSubnN : (Subgroup.normalizer (H : Set G)).IsSubnormal :=
        ih _ hidx _ rfl
      -- H ⊴ normalizer H, i.e., (H.subgroupOf normalizer H).Normal.
      have hNorm : (H.subgroupOf (Subgroup.normalizer (H : Set G))).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer
          (Subgroup.le_normalizer)).mpr le_rfl
      exact Subgroup.IsSubnormal.step _ _ Subgroup.le_normalizer hSubnN hNorm

/-- **Isaacs Lemma 2.7**: `M, N ◁ G` で `M ∩ N = 1` ならば `M` の元と `N` の元は可換.

mathlib `Subgroup.commute_of_normal_of_disjoint` の **適応版** —
`Normal` を instance, `M N` を implicit に取り直す (Isaacs 流の呼び出し記法).
Thm 2.6 等で複数回使用予定. (CLAUDE.md mathlib ラッパー方針の例外規定に該当.) -/
theorem commute_of_disjoint_normal {M N : Subgroup G} [hM : M.Normal] [hN : N.Normal]
    (hDis : Disjoint M N) {m n : G} (hm : m ∈ M) (hn : n ∈ N) : Commute m n :=
  Subgroup.commute_of_normal_of_disjoint M N hM hN hDis m n hm hn

variable (G) in
/-- **Socle**: `G` の全ての minimal normal subgroup の sup.

`Soc(G)` (Isaacs では §4Aで導入, p.92). Thm 2.6 で `M ≤ Soc(N)` の経路を作るのに使う.
mathlib 未収載. -/
def socle : Subgroup G :=
  ⨆ M : {M : Subgroup G // IsMinimalNormal M}, (M : Subgroup G)

/-- minimal normal subgroup は socle に含まれる. (`le_iSup` 適応; 章内で 2 回以上使う.) -/
theorem isMinimalNormal_le_socle {M : Subgroup G} (hM : IsMinimalNormal M) :
    M ≤ socle G :=
  le_iSup (fun M : {M : Subgroup G // IsMinimalNormal M} => (M : Subgroup G)) ⟨M, hM⟩

/-- `Soc(G)` は `G` の正規部分群. 各 minimal normal の正規性を `iSup_induction` で
全体に持ち上げる. テンプレートは [`Ch01_Sylow/Main.lean` `fitting.normal`](Ch01_Sylow/Main.lean#L834). -/
instance socle.normal : (socle G).Normal := by
  refine ⟨fun n hn g => ?_⟩
  refine Subgroup.iSup_induction _ (C := fun x => g * x * g⁻¹ ∈ socle G) hn
    ?mem ?one ?mul
  case mem =>
    rintro ⟨M, hM⟩ x hx
    exact isMinimalNormal_le_socle hM (hM.1.conj_mem x hx g)
  case one => simp
  case mul =>
    intro x y hx hy
    have heq : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [heq]
    exact (socle G).mul_mem hx hy

/-- minimal normal subgroup は MulEquiv `ϕ : G ≃* G` による像も minimal normal. -/
theorem IsMinimalNormal.map_equiv {M : Subgroup G} (hM : IsMinimalNormal M) (ϕ : G ≃* G) :
    IsMinimalNormal (M.map ϕ.toMonoidHom) := by
  refine ⟨hM.1.map ϕ.toMonoidHom ϕ.surjective, ?_, ?_⟩
  · -- `M.map ϕ ≠ ⊥` since `ϕ` injective ⇒ image of a nontrivial subgroup is nontrivial.
    intro heq
    apply hM.2.1
    rw [eq_bot_iff]
    intro m hm
    have hmem : ϕ m ∈ M.map ϕ.toMonoidHom := ⟨m, hm, rfl⟩
    rw [heq, Subgroup.mem_bot] at hmem
    have h1 : m = 1 := ϕ.injective (by rw [hmem]; exact (ϕ.map_one).symm)
    rw [h1]; exact Subgroup.one_mem _
  · -- minimality: any `N ≤ M.map ϕ` normal in `G` must be `⊥` or `M.map ϕ`.
    intro N hN hNle
    -- Move along ϕ.symm.
    have hN' : (N.map ϕ.symm.toMonoidHom).Normal := hN.map ϕ.symm.toMonoidHom ϕ.symm.surjective
    have hle : N.map ϕ.symm.toMonoidHom ≤ M := by
      rintro _ ⟨y, hyN, rfl⟩
      rcases hNle hyN with ⟨z, hzM, hzeq⟩
      have h1 : ϕ.symm.toMonoidHom y = z := by
        change ϕ.symm y = z
        rw [← hzeq]; exact ϕ.symm_apply_apply z
      rw [h1]; exact hzM
    -- Transport back: N = (N.map ϕ.symm).map ϕ via map_map and ϕ.symm.trans ϕ = id.
    have hback : (N.map ϕ.symm.toMonoidHom).map ϕ.toMonoidHom = N := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id N
      ext x; simp
    rcases hM.2.2 _ hN' hle with hbot | htop
    · left
      rw [← hback, hbot, Subgroup.map_bot]
    · right
      rw [← hback, htop]

/-- `Soc(G)` は `G` の特性部分群. 任意の `ϕ : G ≃* G` について `(Soc G).map ϕ ≤ Soc G`
を `characteristic_iff_map_le` で示す. -/
instance socle.characteristic : (socle G).Characteristic := by
  refine (Subgroup.characteristic_iff_map_le).mpr ?_
  intro ϕ
  change (⨆ M : {M : Subgroup G // IsMinimalNormal M}, (M : Subgroup G)).map
      ϕ.toMonoidHom ≤ socle G
  rw [Subgroup.map_iSup]
  refine iSup_le ?_
  rintro ⟨M, hM⟩
  exact isMinimalNormal_le_socle (hM.map_equiv ϕ)

/-- 有限群の任意の非自明な正規部分群は minimal normal subgroup を含む.
`Nat.card N` の強induction. テンプレートは `isSubnormal_of_isNilpotent_finite`. -/
theorem exists_isMinimalNormal_le_of_normal [Finite G] (N : Subgroup G) [N.Normal]
    (hN : N ≠ ⊥) : ∃ M : Subgroup G, IsMinimalNormal M ∧ M ≤ N := by
  classical
  -- We need to carry `N.Normal` through the induction; promote it to an explicit hyp.
  suffices h : ∀ (k : ℕ) (N : Subgroup G), N.Normal → Nat.card N ≤ k → N ≠ ⊥ →
      ∃ M : Subgroup G, IsMinimalNormal M ∧ M ≤ N by
    exact h (Nat.card N) N ‹N.Normal› le_rfl hN
  intro k
  induction k with
  | zero =>
    intro N _ hcard _
    -- Nat.card N = 0 contradiction with Nat.card_pos
    exact absurd (Nat.le_zero.mp hcard) Nat.card_pos.ne'
  | succ k ih =>
    intro N hNn hcard hNne
    by_cases hmin : ∀ K : Subgroup G, K.Normal → K ≤ N → K = ⊥ ∨ K = N
    · exact ⟨N, ⟨hNn, hNne, hmin⟩, le_rfl⟩
    · push Not at hmin
      obtain ⟨K, hKnorm, hKleN, hKne_bot, hKne_N⟩ := hmin
      have hKlt : K < N := lt_of_le_of_ne hKleN hKne_N
      have hsub : (K : Set G) ⊂ (N : Set G) := SetLike.coe_ssubset_coe.mpr hKlt
      obtain ⟨x, hxN, hxK⟩ := Set.exists_of_ssubset hsub
      have hcard_K : Nat.card K < Nat.card N := by
        have hequiv : K ≃ {n : N // (n : G) ∈ K} :=
          { toFun := fun ⟨g, hg⟩ => ⟨⟨g, hKleN hg⟩, hg⟩
            invFun := fun ⟨⟨g, _⟩, hg⟩ => ⟨g, hg⟩
            left_inv := fun ⟨_, _⟩ => rfl
            right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
        rw [Nat.card_congr hequiv]
        exact Finite.card_subtype_lt (p := fun n : N => (n : G) ∈ K)
          (x := ⟨x, hxN⟩) hxK
      have hcard_K_le : Nat.card K ≤ k := by omega
      obtain ⟨M, hMmin, hMleK⟩ := ih K hKnorm hcard_K_le hKne_bot
      exact ⟨M, hMmin, hMleK.trans hKleN⟩

/-- Thm 2.2 逆方向の strong induction を `|G| ≤ n` で外側に出した補助補題.
`G` を generalize するため `∀ n, ∀ G, ...` の形を取る (Ch.2 内の
`isMinimalNormal_le_normalizer_aux` と同じパターン). -/
private theorem le_fitting_aux :
    ∀ n, ∀ (G : Type*) [Group G] [Finite G],
      Nat.card G ≤ n → ∀ {H : Subgroup G},
      Group.IsNilpotent H → H.IsSubnormal → H ≤ fitting G := by
  intro n
  induction n with
  | zero =>
    intro G _ _ hG _ _ _
    exact absurd (Nat.le_zero.mp hG) Nat.card_pos.ne'
  | succ n ih =>
    intro G _ _ _ H hNilp hSn
    by_cases hHtop : H = ⊤
    · -- H = ⊤: `G` 冪零 ⇒ `(⊤ : Subgroup G) ≤ fitting G`
      subst hHtop
      have := hNilp
      exact nilpotent_normal_le_fitting
    · -- H < ⊤: penultimate term `K` を取って IH を `K` に適用
      obtain ⟨K, hKnorm, hHK, hKlt⟩ := hSn.exists_normal_and_le_and_lt_top_of_ne hHtop
      have _ := hKnorm
      -- `Nat.card K < Nat.card G ≤ succ n`, so `Nat.card K ≤ n`.
      have hKcard_le : Nat.card K ≤ n := by
        have hKle : Nat.card K ≤ Nat.card G := K.card_le_card_group
        have hKne_top : K ≠ ⊤ := hKlt.ne
        have hKne : Nat.card K ≠ Nat.card G := fun heq =>
          hKne_top (Subgroup.eq_top_of_card_eq K heq)
        omega
      -- IH の入力: subnormality と nilpotency を `H.subgroupOf K` (K の部分群) に転送.
      have hH_sn_in_K : (H.subgroupOf K).IsSubnormal := hSn.subgroupOf
      have hH_nilp_in_K : Group.IsNilpotent (H.subgroupOf K) :=
        Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHK).symm
      have hH_le_fitK : H.subgroupOf K ≤ fitting K :=
        ih K hKcard_le hH_nilp_in_K hH_sn_in_K
      -- `H = (H.subgroupOf K).map K.subtype ≤ (fitting K).map K.subtype`.
      have hHeq : (H.subgroupOf K).map K.subtype = H :=
        Subgroup.map_subgroupOf_eq_of_le hHK
      have hpush : H ≤ (fitting K).map K.subtype := by
        rw [← hHeq]; exact Subgroup.map_mono hH_le_fitK
      -- `(fitting K).map K.subtype` は normal (characteristic in K + K ⊴ G) かつ nilpotent.
      have : ((fitting K).map K.subtype).Normal := inferInstance
      have : Group.IsNilpotent ((fitting K).map K.subtype) :=
        Group.nilpotent_of_mulEquiv ((fitting K).equivMapOfInjective K.subtype K.subtype_injective)
      exact hpush.trans nilpotent_normal_le_fitting

/-- **Isaacs Thm 2.2**: 有限群 `G` の部分群 `H` について,
`H ≤ F(G) ↔ H が冪零かつ G で部分正規`.

形式化メモ:
- 順方向: `H ≤ F(G)`, `F(G)` 冪零 (Ch.1 `fitting.isNilpotent`) ⇒ `H` も冪零
  (`Subgroup.subgroupOfEquivOfLe` 経由).  `F(G) ⊴ G` で `F(G).IsSubnormal`,
  Lemma 2.1 (`isSubnormal_of_isNilpotent_finite`) で `H.subgroupOf (F(G))` も subnormal,
  `IsSubnormal.trans` で `H.IsSubnormal`.
- 逆方向: `|G|`-induction (`le_fitting_aux`).  `H = ⊤` なら `G` 冪零 ⇒
  `nilpotent_normal_le_fitting`.  `H < ⊤` なら `K ⊴ G, H ≤ K, K < ⊤` を取り
  (`exists_normal_and_le_and_lt_top_of_ne`), IH を `K` に適用して
  `H.subgroupOf K ≤ fitting K`.  `fitting K` は `K` で特性的 (Ch.1
  `fitting.characteristic`) + `K ⊴ G` ⇒ `(fitting K).map K.subtype ⊴ G`, 冪零でもあるので
  `nilpotent_normal_le_fitting` で `fitting G` 配下. -/
theorem le_fitting_iff_isNilpotent_and_isSubnormal [Finite G] (H : Subgroup G) :
    H ≤ fitting G ↔ Group.IsNilpotent H ∧ H.IsSubnormal := by
  refine ⟨fun hH => ⟨?_, ?_⟩,
    fun ⟨hNilp, hSn⟩ => le_fitting_aux (Nat.card G) G le_rfl hNilp hSn⟩
  · -- H ≤ F(G) ⇒ H 冪零 (`H.subgroupOf F(G) ≃* H`, F(G) 冪零, subgroup 継承)
    exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hH)
  · -- H ≤ F(G) ⇒ H subnormal (F(G) subnormal in G + H.subgroupOf F(G) subnormal in F(G))
    have hFsn : (fitting G).IsSubnormal := Subgroup.Normal.isSubnormal inferInstance
    have hHsn_in_F : (H.subgroupOf (fitting G)).IsSubnormal :=
      isSubnormal_of_isNilpotent_finite _
    exact Subgroup.IsSubnormal.trans hH hHsn_in_F hFsn

/-- 補助補題 (Thm 2.6 の strong induction の generalized core).

`n : ℕ` についての induction で, 任意の有限群 `G` (with `|G| ≤ n`) に対し,
任意の subnormal `S` と minimal normal `M` で `M ≤ N_G(S)` を示す. -/
private theorem isMinimalNormal_le_normalizer_aux :
    ∀ n, ∀ (G : Type*) [Group G] [Finite G],
      Nat.card G ≤ n → ∀ {S M : Subgroup G}, S.IsSubnormal → IsMinimalNormal M →
      M ≤ Subgroup.normalizer (S : Set G) := by
  intro n
  induction n with
  | zero =>
    intro G _ _ hG _ _ _ _
    -- Nat.card G = 0 contradicts the fact that G has the identity.
    exact absurd (Nat.le_zero.mp hG) Nat.card_pos.ne'
  | succ n ih =>
    intro G _ _ hG S M hS hM
    classical
    have _ : M.Normal := hM.1
    by_cases hStop : S = ⊤
    · -- normalizer of ⊤ is ⊤ (since ⊤ is normal).
      subst hStop
      rw [Subgroup.normalizer_eq_top (⊤ : Subgroup G)]
      exact le_top
    · obtain ⟨N, hNnorm, hSleN, hNlt⟩ := hS.exists_normal_and_le_and_lt_top_of_ne hStop
      have _ := hNnorm
      by_cases hMN : M ⊓ N = ⊥
      · -- Case 1: M ⊓ N = ⊥. M and N commute; S ≤ N ⇒ M centralizes S.
        intro m hm
        rw [Subgroup.mem_normalizer_iff]
        intro s
        constructor
        · intro hsS
          have hsN : s ∈ N := hSleN hsS
          have hcomm : Commute m s := commute_of_disjoint_normal
            (M := M) (N := N) (disjoint_iff.mpr hMN) hm hsN
          have hmsm : m * s * m⁻¹ = s := by
            rw [Commute.eq hcomm, mul_inv_cancel_right]
          rw [hmsm]; exact hsS
        · intro hmsm
          have hsN : m * s * m⁻¹ ∈ N := hSleN hmsm
          have hm_inv : m⁻¹ ∈ M := M.inv_mem hm
          have hcomm : Commute m⁻¹ (m * s * m⁻¹) := commute_of_disjoint_normal
            (M := M) (N := N) (disjoint_iff.mpr hMN) hm_inv hsN
          have hseq : s = m⁻¹ * (m * s * m⁻¹) * m := by group
          rw [hseq, Commute.eq hcomm, mul_assoc, inv_mul_cancel, mul_one]
          exact hmsm
      · -- Case 2: M ⊓ N ≠ ⊥. By minimality of M, M ⊓ N = M, i.e., M ≤ N.
        have hMN_le_M : M ⊓ N ≤ M := inf_le_left
        have hMN_norm : (M ⊓ N).Normal := Subgroup.normal_inf_normal M N
        have hMN_eq_M : M ⊓ N = M := by
          rcases hM.2.2 (M ⊓ N) hMN_norm hMN_le_M with h | h
          · exact absurd h hMN
          · exact h
        have hMleN : M ≤ N := by
          have h : M ≤ M ⊓ N := le_of_eq hMN_eq_M.symm
          exact (le_inf_iff.mp h).2
        -- |N| < |G| ≤ n+1 so |N| ≤ n.
        have hN_ne_top : N ≠ ⊤ := hNlt.ne
        obtain ⟨g, hg⟩ : ∃ g : G, g ∉ N := by
          by_contra h
          push Not at h
          exact hN_ne_top (eq_top_iff.mpr fun x _ => h x)
        have hN_card_lt : Nat.card N < Nat.card G :=
          Finite.card_subtype_lt (p := fun x : G => x ∈ N) (x := g) hg
        have hN_card_le_n : Nat.card N ≤ n := by omega
        have hNne_bot : N ≠ ⊥ := by
          intro h
          apply hM.2.1
          rw [eq_bot_iff]; rw [h] at hMleN; exact hMleN
        have hNNontriv : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNne_bot
        -- IH on ↥N.
        have hSsubN_sn : (S.subgroupOf N).IsSubnormal := hS.subgroupOf
        have hIH : ∀ K : Subgroup N, IsMinimalNormal K →
            K ≤ Subgroup.normalizer (S.subgroupOf N : Set N) := by
          intro K hK
          exact ih N hN_card_le_n hSsubN_sn hK
        have hSoc_le_norm_inner : socle N ≤ Subgroup.normalizer (S.subgroupOf N : Set N) := by
          refine iSup_le ?_
          rintro ⟨K, hK⟩
          exact hIH K hK
        -- Lift: (socle N).map N.subtype ≤ normalizer S in G.
        have hSoc_lift_le_norm :
            (socle N).map N.subtype ≤ Subgroup.normalizer (S : Set G) := by
          rintro _ ⟨⟨g', hg'N⟩, hg'soc, rfl⟩
          change (g' : G) ∈ Subgroup.normalizer (S : Set G)
          have hg'norm : (⟨g', hg'N⟩ : N) ∈
              Subgroup.normalizer (S.subgroupOf N : Set N) := hSoc_le_norm_inner hg'soc
          rw [Subgroup.mem_normalizer_iff] at hg'norm ⊢
          intro s
          by_cases hsN : s ∈ N
          · -- s ∈ N: lift to N, apply hg'norm.
            have hpair := hg'norm ⟨s, hsN⟩
            constructor
            · intro hsS
              have h1 : (⟨s, hsN⟩ : N) ∈ S.subgroupOf N := by
                rwa [Subgroup.mem_subgroupOf]
              have h2 := hpair.mp h1
              rw [Subgroup.mem_subgroupOf] at h2
              -- h2 : ((⟨g', _⟩ * ⟨s, _⟩ * ⟨g', _⟩⁻¹ : N) : G) ∈ S
              -- coerce: (⟨a, _⟩ * ⟨b, _⟩ : N : G) = a * b in G.
              simpa using h2
            · intro hgsg
              have hgsg_N : g' * s * g'⁻¹ ∈ N := hNnorm.conj_mem s hsN g'
              have h1 : (⟨g' * s * g'⁻¹, hgsg_N⟩ : N) ∈ S.subgroupOf N := by
                rwa [Subgroup.mem_subgroupOf]
              -- Identify ⟨g' * s * g'⁻¹, _⟩ with ⟨g', _⟩ * ⟨s, _⟩ * ⟨g', _⟩⁻¹ as N-element.
              have hcong : (⟨g' * s * g'⁻¹, hgsg_N⟩ : N) =
                  ⟨g', hg'N⟩ * ⟨s, hsN⟩ * ⟨g', hg'N⟩⁻¹ := by
                apply Subtype.ext
                change g' * s * g'⁻¹ = (↑(⟨g', hg'N⟩ * ⟨s, hsN⟩ * ⟨g', hg'N⟩⁻¹ : N) : G)
                push_cast
                rfl
              rw [hcong] at h1
              have h2 := hpair.mpr h1
              rwa [Subgroup.mem_subgroupOf] at h2
          · -- s ∉ N: both sides false.
            have hgsg_notN : g' * s * g'⁻¹ ∉ N := by
              intro h
              apply hsN
              have hseq : s = g'⁻¹ * (g' * s * g'⁻¹) * g' := by group
              rw [hseq]
              have h' : g'⁻¹ * (g' * s * g'⁻¹) * (g'⁻¹)⁻¹ ∈ N :=
                hNnorm.conj_mem _ h g'⁻¹
              rwa [inv_inv] at h'
            constructor
            · intro hsS; exact absurd (hSleN hsS) hsN
            · intro hgsg; exact absurd (hSleN hgsg) hgsg_notN
        -- M.subgroupOf N is normal in N (since M is normal in G and M ≤ N).
        have hMsubN_norm : (M.subgroupOf N).Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hMleN).mpr
            Subgroup.le_normalizer_of_normal
        -- M.subgroupOf N ≠ ⊥ (since M ≠ ⊥ and M ≤ N).
        have hMsubN_ne_bot : M.subgroupOf N ≠ ⊥ := by
          intro heq
          apply hM.2.1
          have hM_eq : M = (M.subgroupOf N).map N.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hMleN).symm
          rw [hM_eq, heq, Subgroup.map_bot]
        -- Pick a minimal-normal-in-N subgroup K ≤ M.subgroupOf N.
        obtain ⟨K, hKmin, hKle⟩ :=
          exists_isMinimalNormal_le_of_normal (G := N) (M.subgroupOf N) hMsubN_ne_bot
        have hK_le_socN : K ≤ socle N := isMinimalNormal_le_socle hKmin
        -- K.map N.subtype ≤ M ∩ (socle N).map N.subtype, and ≠ ⊥.
        have hKmap_le_M : K.map N.subtype ≤ M := by
          rintro _ ⟨k, hk, rfl⟩
          have := hKle hk
          rwa [Subgroup.mem_subgroupOf] at this
        have hKmap_le_socMap : K.map N.subtype ≤ (socle N).map N.subtype :=
          Subgroup.map_mono hK_le_socN
        have hKmap_ne_bot : K.map N.subtype ≠ ⊥ := by
          intro heq
          apply hKmin.2.1
          rw [eq_bot_iff]
          intro k hk
          have hmem : (k : G) ∈ K.map N.subtype := ⟨k, hk, rfl⟩
          rw [heq, Subgroup.mem_bot] at hmem
          have : k = 1 := Subtype.ext hmem
          rw [this]; exact Subgroup.one_mem _
        -- M ⊓ ((socle N).map N.subtype) is G-normal, ≤ M, ≠ ⊥.
        have hSocLift_normal : ((socle N).map N.subtype).Normal := inferInstance
        have hM_inf_norm : (M ⊓ (socle N).map N.subtype).Normal :=
          Subgroup.normal_inf_normal _ _
        have hM_inf_ne_bot : M ⊓ (socle N).map N.subtype ≠ ⊥ := by
          intro heq
          apply hKmap_ne_bot
          rw [eq_bot_iff]
          exact (le_inf hKmap_le_M hKmap_le_socMap).trans heq.le
        have hM_inf_eq_M : M ⊓ (socle N).map N.subtype = M := by
          rcases hM.2.2 _ hM_inf_norm inf_le_left with h | h
          · exact absurd h hM_inf_ne_bot
          · exact h
        have hM_le_SocLift : M ≤ (socle N).map N.subtype := by
          intro m hm
          have hmem : m ∈ M ⊓ (socle N).map N.subtype := by rw [hM_inf_eq_M]; exact hm
          exact hmem.2
        exact hM_le_SocLift.trans hSoc_lift_le_norm

/-- **Isaacs Thm 2.6** (minimal normal が subnormal を正規化).

Subnormal `S ⊴⊴ G` と minimal normal `M` について `M ≤ N_G(S)`.

Isaacs p.46 の証明: `|G|`-induction.
* `S = ⊤` なら `N_G(⊤) = ⊤` で trivial.
* `S ≠ ⊤` なら proper G-正規 `N` で `S ≤ N` を取る.
  - **Case 1** `M ⊓ N = ⊥`: `commute_of_disjoint_normal` で `M` と `N` の元は可換,
    特に `S ≤ N` の元とも可換 ⇒ `M ≤ centralizer S ≤ normalizer S`.
  - **Case 2** `M ⊓ N ≠ ⊥`: minimality で `M ≤ N`. IH を ambient group `↥N` に適用し,
    `socle ↥N` の各 minimal normal が `S.subgroupOf N` を正規化 ⇒ `S` を正規化.
    Characteristic 経由で `(socle ↥N).map N.subtype` は `G` 正規, `M ≤ ↥N` と合わせ
    minimality 適用. -/
theorem isMinimalNormal_le_normalizer_of_isSubnormal [Finite G]
    {S M : Subgroup G} (hS : S.IsSubnormal) (hM : IsMinimalNormal M) :
    M ≤ Subgroup.normalizer (S : Set G) :=
  isMinimalNormal_le_normalizer_aux (Nat.card G) G le_rfl hS hM

/-- 補助補題 (Thm 2.5 の strong induction の generalized core).

任意の有限群 `G` (with `Nat.card G ≤ n`) について, subnormal `S, T : Subgroup G`
の sup `S ⊔ T` も subnormal. -/
private theorem isSubnormal_sup_aux :
    ∀ n, ∀ (G : Type*) [Group G] [Finite G],
      Nat.card G ≤ n → ∀ {S T : Subgroup G}, S.IsSubnormal → T.IsSubnormal →
      (S ⊔ T).IsSubnormal := by
  intro n
  induction n with
  | zero =>
    intro G _ _ hG _ _ _ _
    exact absurd (Nat.le_zero.mp hG) Nat.card_pos.ne'
  | succ n ih =>
    intro G _ _ hG S T hS hT
    classical
    by_cases hGnontriv : Nontrivial G
    case neg =>
      -- Subsingleton G ⇒ every subgroup = ⊤ ⇒ IsSubnormal.top.
      rw [not_nontrivial_iff_subsingleton] at hGnontriv
      have := hGnontriv
      have hST_top : (S ⊔ T : Subgroup G) = ⊤ := by
        refine eq_top_iff.mpr (fun x _ => ?_)
        rw [show x = 1 from Subsingleton.elim x 1]
        exact (S ⊔ T).one_mem
      rw [hST_top]
      exact Subgroup.IsSubnormal.top
    case pos =>
      have := hGnontriv
      -- Pick minimal normal M ≤ ⊤.
      have htop_ne_bot : (⊤ : Subgroup G) ≠ ⊥ := by
        intro h
        obtain ⟨x, y, hxy⟩ := hGnontriv
        apply hxy
        have hxbot : x ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_top x
        have hybot : y ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_top y
        rw [Subgroup.mem_bot] at hxbot hybot
        rw [hxbot, hybot]
      obtain ⟨M, hM, _⟩ :=
        exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) htop_ne_bot
      have hMnorm : M.Normal := hM.1
      -- Quotient map f : G →* G ⧸ M.
      let f : G →* G ⧸ M := QuotientGroup.mk' M
      have hSbar : (S.map f).IsSubnormal := hS.map (QuotientGroup.mk'_surjective M)
      have hTbar : (T.map f).IsSubnormal := hT.map (QuotientGroup.mk'_surjective M)
      -- Card bound: |G/M| < |G| ≤ n+1, so |G/M| ≤ n.
      have h1lt_M : 1 < Nat.card M := by
        have h_ne_one : Nat.card M ≠ 1 := by
          intro h1
          apply hM.2.1
          have hSub : Subsingleton M := Nat.card_eq_one_iff_unique.mp h1 |>.1
          refine eq_bot_iff.mpr (fun x hx => ?_)
          rw [Subgroup.mem_bot]
          exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : M) 1)
        have h_pos : 0 < Nat.card M := Nat.card_pos
        omega
      have hquot_lt : Nat.card (G ⧸ M) < Nat.card G := by
        have heq : M.index * Nat.card M = Nat.card G := M.index_mul_card
        have hM_pos : 0 < Nat.card M := Nat.card_pos
        have hidx_eq : M.index = Nat.card G / Nat.card M := by
          rw [← heq, Nat.mul_div_cancel _ hM_pos]
        change M.index < Nat.card G
        rw [hidx_eq]
        exact Nat.div_lt_self Nat.card_pos h1lt_M
      have hquot_le : Nat.card (G ⧸ M) ≤ n := by omega
      -- IH on G ⧸ M.
      have hIH : (S.map f ⊔ T.map f).IsSubnormal :=
        ih (G ⧸ M) hquot_le hSbar hTbar
      rw [← Subgroup.map_sup] at hIH
      -- Comap back to G: comap f (map f (S ⊔ T)) = (S ⊔ T) ⊔ ker f = (S ⊔ T) ⊔ M.
      have hcomap_subn : (((S ⊔ T).map f).comap f).IsSubnormal := hIH.comap f
      have hcomap_eq : ((S ⊔ T).map f).comap f = (S ⊔ T) ⊔ M := by
        rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      rw [hcomap_eq] at hcomap_subn
      -- Thm 2.6: M ≤ N(S) ⊓ N(T) ≤ N(S ⊔ T).
      have hMS : M ≤ Subgroup.normalizer (S : Set G) :=
        isMinimalNormal_le_normalizer_of_isSubnormal hS hM
      have hMT : M ≤ Subgroup.normalizer (T : Set G) :=
        isMinimalNormal_le_normalizer_of_isSubnormal hT hM
      have hMnormST : M ≤ Subgroup.normalizer ((S ⊔ T : Subgroup G) : Set G) :=
        (le_inf hMS hMT).trans (Subgroup.normalizer_inf_normalizer_le_normalizer_sup S T)
      -- S ⊔ T ⊴ (S ⊔ T) ⊔ M. Both summands ⊆ N(S ⊔ T).
      have hSupSup_le_norm :
          (S ⊔ T) ⊔ M ≤ Subgroup.normalizer ((S ⊔ T : Subgroup G) : Set G) :=
        sup_le Subgroup.le_normalizer hMnormST
      have hSupNormal : ((S ⊔ T).subgroupOf ((S ⊔ T) ⊔ M)).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hSupSup_le_norm
      exact Subgroup.IsSubnormal.step _ _ le_sup_left hcomap_subn hSupNormal

/-- **Isaacs Thm 2.5 Wielandt 結合定理**: 部分正規部分群の sup は部分正規.

有限群 `G` の subnormal `S, T : Subgroup G` について `S ⊔ T` も subnormal.

Isaacs p.46 の証明: `|G|`-induction. minimal normal `M` を取って `G ⧸ M` に IH を
適用 ⇒ `(S ⊔ T) ⊔ M ⊴⊴ G`. Thm 2.6 で `M ≤ N(S ⊔ T)` ⇒ `S ⊔ T ⊴ (S ⊔ T) ⊔ M`.
合わせて `S ⊔ T ⊴⊴ G`. -/
theorem isSubnormal_sup_of_isSubnormal [Finite G] {S T : Subgroup G}
    (hS : S.IsSubnormal) (hT : T.IsSubnormal) : (S ⊔ T).IsSubnormal :=
  isSubnormal_sup_aux (Nat.card G) G le_rfl hS hT

open scoped Pointwise in
/-- **Isaacs Thm 2.9 Wielandt's Zipper Lemma**. 有限群 `G` の部分群 `S` で,
`S` を真に含む任意の真部分群 `H` について `S ⊴⊴ H` であり, かつ `S` 自身は
`G` で部分正規でないとする. このとき `S` を含む `G` の極大部分群は一意.

Isaacs p.49 の証明: `|G:S|` (= `S.index`) についての強induction.
* `S.index = 1` ⇒ `S = ⊤` ⇒ `S ⊴⊴ G` (`IsSubnormal.top`) で仮定矛盾, vacuous.
* induction step: `S` が `G` で正規でない (else `S ⊴⊴ G`, 矛盾) ので
  `N_G(S) < ⊤`, 極大 `M ≥ N_G(S)` を取る. 任意の極大 `K ≥ S` で `K = M` を示す:
  - **Case A** `S ⊴ K`: `K ≤ N_G(S) ≤ M`, `K` 極大 で `K = M`.
  - **Case B** `S ⊴⊴ K` だが `S ⋬ K`: K の subnormal chain で「`S` が正規でなくなる」
    最初の `f i` を Nat.find で取り, x ∈ f i \ N_K(S) を選ぶ. `T := S ⊔ S^x` は
    `T > S`, `T ≤ N_G(S) ≤ M`, `T ≤ K` で, T が IH の hypotheses を満たす
    (Thm 2.5 を使う). IH で T を含む極大は一意 ⇒ M = K. -/
theorem zipper_lemma [Finite G] {S : Subgroup G}
    (hS_proper : ∀ H : Subgroup G, S ≤ H → H ≠ ⊤ → (S.subgroupOf H).IsSubnormal)
    (hS_not_sn : ¬ S.IsSubnormal) :
    ∃ M : Subgroup G, IsCoatom M ∧ S ≤ M ∧
      ∀ K : Subgroup G, IsCoatom K → S ≤ K → K = M := by
  classical
  -- Strong induction on S.index.
  induction hIdx : S.index using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    -- Rule out S.index = 1 first. In finite group, S.index ≥ 1.
    have hS_idx_pos : 0 < S.index :=
      Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    rcases Nat.lt_or_ge 1 n with hgt | hle
    swap
    · -- n ≤ 1: since S.index = n > 0, we have n = 1.
      have hn_eq : n = 1 := by
        have hn_pos : 0 < n := hIdx ▸ hS_idx_pos
        omega
      -- S.index = 1 ⇒ S = ⊤ ⇒ S subnormal, contradiction.
      have hS_top : S = ⊤ := Subgroup.index_eq_one.mp (hIdx.trans hn_eq)
      exact absurd (hS_top ▸ Subgroup.IsSubnormal.top) hS_not_sn
    · -- n > 1: induction step.
      -- Step 1: S not normal in G.
      have hS_not_normal : ¬ S.Normal := fun hN => hS_not_sn hN.isSubnormal
      -- N_G(S) < ⊤.
      have hN_lt_top : Subgroup.normalizer (S : Set G) < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro hN_top
        exact hS_not_normal (Subgroup.normalizer_eq_top_iff.mp hN_top)
      -- Step 2: pick maximal M ≥ N_G(S). Note S ≤ N_G(S).
      obtain ⟨M, hM_coatom, hN_le_M⟩ :=
        (eq_top_or_exists_le_coatom (Subgroup.normalizer (S : Set G))).resolve_left hN_lt_top.ne
      have hS_le_NS : S ≤ Subgroup.normalizer (S : Set G) := Subgroup.le_normalizer
      have hS_le_M : S ≤ M := hS_le_NS.trans hN_le_M
      refine ⟨M, hM_coatom, hS_le_M, ?_⟩
      intro K hK_coatom hS_le_K
      -- K is a maximal subgroup containing S; show K = M.
      have hK_ne_top : K ≠ ⊤ := hK_coatom.1
      -- H1 ⇒ S.subgroupOf K is subnormal.
      have hSsubK_sn : (S.subgroupOf K).IsSubnormal := hS_proper K hS_le_K hK_ne_top
      -- Case split: is S normal in K?
      by_cases hSK_normal : (S.subgroupOf K).Normal
      · -- Case A: S ⊴ K. Then K ≤ N_G(S) ≤ M, K coatom ⇒ K = M.
        have hK_le_NS : K ≤ Subgroup.normalizer (S : Set G) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hS_le_K).mp hSK_normal
        have hK_le_M : K ≤ M := hK_le_NS.trans hN_le_M
        -- K coatom and K ≤ M ≠ ⊤ (M coatom).
        rcases hK_coatom.le_iff.mp hK_le_M with hM_top | hM_eq
        · exact absurd hM_top hM_coatom.1
        · exact hM_eq.symm
      · -- Case B: S subnormal in K but not normal in K. Extract chain.
        obtain ⟨nChain, f, hf_mono, hf_step, hf0, hfN⟩ :=
          hSsubK_sn.exists_chain
        -- f : ℕ → Subgroup ↥K with f 0 = S.subgroupOf K, f nChain = ⊤, chain property.
        -- Find smallest i with S.subgroupOf K NOT normal in f i.
        -- (S.subgroupOf K).subgroupOf (f i) Normal ⇔ f i ≤ normalizer (S.subgroupOf K).
        have hPred_exists : ∃ i, ¬ (((S.subgroupOf K).subgroupOf (f i)).Normal) := by
          refine ⟨nChain, ?_⟩
          intro hN
          apply hSK_normal
          -- hN : (S.subgroupOf K).subgroupOf (f nChain) Normal.
          -- f nChain = ⊤_K, so subgroupOf ⊤_K = identification, giving normality in K.
          rw [hfN] at hN
          -- (S.subgroupOf K).subgroupOf ⊤ Normal ⇒ ⊤ ≤ normalizer (S.subgroupOf K)
          have h1 : (⊤ : Subgroup K) ≤
              Subgroup.normalizer ((S.subgroupOf K) : Set K) :=
            (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp hN
          rw [top_le_iff, Subgroup.normalizer_eq_top_iff] at h1
          exact h1
        -- Smallest such i.
        let m := Nat.find hPred_exists
        have hm_spec : ¬ (((S.subgroupOf K).subgroupOf (f m)).Normal) := Nat.find_spec hPred_exists
        have hm_min : ∀ k < m, ((S.subgroupOf K).subgroupOf (f k)).Normal := by
          intro k hk
          by_contra h
          exact absurd (Nat.find_min hPred_exists hk) (not_not.mpr h)
        -- f 0 = S.subgroupOf K, normal in itself, so m ≥ 1.
        have hm_pos : 0 < m := by
          by_contra h
          push Not at h
          interval_cases m
          apply hm_spec
          rw [hf0]
          -- (S.subgroupOf K).subgroupOf (S.subgroupOf K) = ⊤, hence normal.
          rw [show (S.subgroupOf K).subgroupOf (S.subgroupOf K) = ⊤ from
            Subgroup.subgroupOf_self _]
          exact Subgroup.normal_top
        -- f (m-1) ≤ normalizer (S.subgroupOf K). f m has element not normalizing S.subgroupOf K.
        have hfm1_norm : ((S.subgroupOf K).subgroupOf (f (m - 1))).Normal :=
          hm_min (m - 1) (Nat.sub_lt hm_pos Nat.zero_lt_one)
        -- f (m-1) ≤ N_K(S.subgroupOf K).
        -- Need S.subgroupOf K ≤ f (m-1) first.
        have hS_le_fm1 : S.subgroupOf K ≤ f (m - 1) := by
          rw [← hf0]; exact hf_mono (Nat.zero_le _)
        have hfm1_le_norm : f (m - 1) ≤
            Subgroup.normalizer ((S.subgroupOf K) : Set K) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hS_le_fm1).mp hfm1_norm
        -- f (m-1) ≤ f m: take an element of f m not in N_K(S.subgroupOf K).
        have hS_le_fm : S.subgroupOf K ≤ f m := by
          rw [← hf0]; exact hf_mono (Nat.zero_le _)
        have hfm_not_le_norm : ¬ (f m ≤
            Subgroup.normalizer ((S.subgroupOf K) : Set K)) := by
          intro h
          exact hm_spec ((Subgroup.normal_subgroupOf_iff_le_normalizer hS_le_fm).mpr h)
        -- Get x in f m not in N_K(S.subgroupOf K).
        obtain ⟨x, hx_in_fm, hx_not_norm⟩ : ∃ x : K, x ∈ f m ∧
            x ∉ Subgroup.normalizer ((S.subgroupOf K) : Set K) := by
          by_contra h
          push Not at h
          apply hfm_not_le_norm
          intro y hy
          exact h y hy
        -- f (m-1) ⊴ f m by chain property; so x normalizes f (m-1) in f m, i.e.,
        -- (MulAut.conj (x : K)⁻¹) • (f (m-1)) ≤ f (m-1) as subgroups of f m... wait, simpler:
        -- (f (m-1)).subgroupOf (f m) is Normal, so x in f m normalizes (f (m-1)).subgroupOf (f m).
        -- Translate to: x · f (m-1) · x⁻¹ ≤ f (m-1) as subgroup of K (since f (m-1) ≤ f m).
        have hfm1_le_fm : f (m - 1) ≤ f m := by
          have : m - 1 ≤ m := Nat.sub_le _ _
          exact hf_mono this
        -- Use chain property at index m - 1: ((f (m-1)).subgroupOf (f m)).Normal
        have hfm1_norm_in_fm : ((f (m - 1)).subgroupOf (f m)).Normal := by
          have hstep := hf_step (m - 1)
          rwa [Nat.sub_add_cancel hm_pos] at hstep
        have hfm_le_normfm1 : f m ≤ Subgroup.normalizer ((f (m - 1)) : Set K) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hfm1_le_fm).mp hfm1_norm_in_fm
        -- Now translate to G-level. x : K, x.val : G is in K.
        -- We want to construct S^x.
        set xG : G := (x : G)
        have hxG_in_K : xG ∈ K := x.2
        -- Key: x normalizes f (m-1) in K. In particular,
        -- (MulAut.conj x.val⁻¹) • S ≤ image of f (m-1) in G ≤ N_G(S).
        -- Image of f (m-1) in G:
        let J : Subgroup G := (f (m - 1)).map K.subtype
        -- S ≤ J (since S.subgroupOf K ≤ f (m-1), and (S.subgroupOf K).map K.subtype = S).
        have hS_le_J : S ≤ J := by
          rw [show S = (S.subgroupOf K).map K.subtype from
            (Subgroup.map_subgroupOf_eq_of_le hS_le_K).symm]
          exact Subgroup.map_mono hS_le_fm1
        -- J ≤ K.
        have hJ_le_K : J ≤ K := by
          rintro _ ⟨⟨y, hyK⟩, _, rfl⟩
          exact hyK
        -- J ≤ N_G(S) (since (f (m-1)).subgroupOf K ≤ N_K(S.subgroupOf K) lifted to G).
        have hJ_le_NS : J ≤ Subgroup.normalizer (S : Set G) := by
          intro y hy
          rcases hy with ⟨⟨y', hy'K⟩, hy'_in, rfl⟩
          -- y'_in : ⟨y', hy'K⟩ ∈ f (m-1), so it's in N_K(S.subgroupOf K).
          have hy'_norm : (⟨y', hy'K⟩ : K) ∈
              Subgroup.normalizer ((S.subgroupOf K) : Set K) := hfm1_le_norm hy'_in
          rw [Subgroup.mem_normalizer_iff] at hy'_norm ⊢
          intro s
          by_cases hsK : s ∈ K
          · -- s ∈ K: lift to K, apply hy'_norm.
            have h := hy'_norm ⟨s, hsK⟩
            constructor
            · intro hsS
              have h1 : (⟨s, hsK⟩ : K) ∈ S.subgroupOf K := by
                rwa [Subgroup.mem_subgroupOf]
              have h2 := h.mp h1
              rw [Subgroup.mem_subgroupOf] at h2
              -- Coerce computation. y' * s * y'⁻¹ as K-element coerces correctly.
              exact h2
            · intro hys
              have hys_in_K : y' * s * y'⁻¹ ∈ K :=
                K.mul_mem (K.mul_mem hy'K hsK) (K.inv_mem hy'K)
              have h1 : (⟨y' * s * y'⁻¹, hys_in_K⟩ : K) ∈ S.subgroupOf K := by
                rwa [Subgroup.mem_subgroupOf]
              have hcong : (⟨y' * s * y'⁻¹, hys_in_K⟩ : K) =
                  ⟨y', hy'K⟩ * ⟨s, hsK⟩ * ⟨y', hy'K⟩⁻¹ := by
                apply Subtype.ext
                change y' * s * y'⁻¹ =
                  ((⟨y', hy'K⟩ * ⟨s, hsK⟩ * ⟨y', hy'K⟩⁻¹ : K) : G)
                push_cast
                rfl
              rw [hcong] at h1
              have h2 := h.mpr h1
              rwa [Subgroup.mem_subgroupOf] at h2
          · -- s ∉ K: both sides false (since S ≤ K).
            have hys_notK : y' * s * y'⁻¹ ∉ K := by
              intro h
              apply hsK
              have hseq : s = y'⁻¹ * (y' * s * y'⁻¹) * y' := by group
              rw [hseq]
              exact K.mul_mem (K.mul_mem (K.inv_mem hy'K) h) hy'K
            constructor
            · intro hsS; exact absurd (hS_le_K hsS) hsK
            · intro hys; exact absurd (hS_le_K hys) hys_notK
        -- Now construct T = S ⊔ MulAut.conj xG⁻¹ • S.
        set Sx : Subgroup G := (MulAut.conj xG⁻¹ : MulAut G) • S with hSx_def
        set T : Subgroup G := S ⊔ Sx with hT_def
        -- Sx ≤ J ≤ N_G(S): show Sx ≤ J.
        -- xG normalizes J: J = (f(m-1)).map K.subtype. We need
        -- MulAut.conj xG⁻¹ • J ≤ J (since x in K normalizes f(m-1) in K).
        have hJ_normalizes_xG : (MulAut.conj xG : MulAut G) • J ≤ J := by
          rintro - ⟨z, hzJ, rfl⟩
          rcases hzJ with ⟨⟨z', hz'K⟩, hz'_in_fm1, rfl⟩
          have hx_norm_fm1 : x ∈ Subgroup.normalizer ((f (m - 1)) : Set K) :=
            hfm_le_normfm1 hx_in_fm
          have h_conj : x * ⟨z', hz'K⟩ * x⁻¹ ∈ f (m - 1) :=
            ((Subgroup.mem_normalizer_iff.mp hx_norm_fm1) ⟨z', hz'K⟩).mp hz'_in_fm1
          refine ⟨x * ⟨z', hz'K⟩ * x⁻¹, h_conj, ?_⟩
          change ((x * ⟨z', hz'K⟩ * x⁻¹ : K) : G) = MulAut.conj xG z'
          push_cast
          simp [xG]
        -- Also need MulAut.conj xG⁻¹ • J ≤ J (same argument with x⁻¹).
        have hx_inv_in_fm : x⁻¹ ∈ f m := (f m).inv_mem hx_in_fm
        have hJ_normalizes_xG_inv : (MulAut.conj xG⁻¹ : MulAut G) • J ≤ J := by
          rintro - ⟨z, hzJ, rfl⟩
          rcases hzJ with ⟨⟨z', hz'K⟩, hz'_in_fm1, rfl⟩
          have hxinv_norm_fm1 : x⁻¹ ∈ Subgroup.normalizer ((f (m - 1)) : Set K) :=
            hfm_le_normfm1 hx_inv_in_fm
          have h_conj : x⁻¹ * ⟨z', hz'K⟩ * x⁻¹⁻¹ ∈ f (m - 1) :=
            ((Subgroup.mem_normalizer_iff.mp hxinv_norm_fm1) ⟨z', hz'K⟩).mp hz'_in_fm1
          refine ⟨x⁻¹ * ⟨z', hz'K⟩ * x⁻¹⁻¹, h_conj, ?_⟩
          change ((x⁻¹ * ⟨z', hz'K⟩ * x⁻¹⁻¹ : K) : G) = MulAut.conj xG⁻¹ z'
          push_cast
          simp [xG]
        have hSx_le_J : Sx ≤ J := by
          rw [hSx_def]
          calc (MulAut.conj xG⁻¹ : MulAut G) • S
              ≤ (MulAut.conj xG⁻¹ : MulAut G) • J :=
                Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hS_le_J
            _ ≤ J := hJ_normalizes_xG_inv
        have hSx_le_NS : Sx ≤ Subgroup.normalizer (S : Set G) := hSx_le_J.trans hJ_le_NS
        have hSx_le_K : Sx ≤ K := hSx_le_J.trans hJ_le_K
        have hT_le_NS : T ≤ Subgroup.normalizer (S : Set G) :=
          sup_le hS_le_NS hSx_le_NS
        have hT_le_K : T ≤ K := sup_le hS_le_K hSx_le_K
        have hT_le_M : T ≤ M := hT_le_NS.trans hN_le_M
        -- T > S strictly: Sx ⊈ S since xG ∉ N_G(S).
        -- Strategy: if Sx ≤ S, then |Sx| = |S| and Sx = S in finite ⇒ xG⁻¹ ∈ N_G(S) ⇒ xG ∈ N_G(S).
        -- This translates to x ∈ N_K(S.subgroupOf K), contradicting hx_not_norm.
        have hSx_card : Nat.card Sx = Nat.card S :=
          Nat.card_congr (Subgroup.equivSMul (MulAut.conj xG⁻¹) S).toEquiv.symm
        have hSx_not_le_S : ¬ (Sx ≤ S) := by
          intro h
          -- Cardinality forces Sx = S.
          have hSx_eq : Sx = S := Subgroup.eq_of_le_of_card_ge h hSx_card.ge
          -- From Sx = S, we extract xG⁻¹ ∈ N_G(S).
          have hxG_norm_S : xG ∈ Subgroup.normalizer (S : Set G) := by
            -- Sx = S ⇒ xG⁻¹ ∈ N_G(S), hence xG ∈ N_G(S).
            rw [Subgroup.mem_normalizer_iff]
            intro u
            constructor
            · -- u ∈ S → xG * u * xG⁻¹ ∈ S.
              -- xG * u * xG⁻¹ = MulAut.conj xG u; via hSx_eq, MulAut.conj xG • S = S.
              intro huS
              have hsmul_eq : (MulAut.conj xG : MulAut G) • S = S := by
                have h1 : (MulAut.conj xG⁻¹ : MulAut G) • S = S := hSx_eq
                have h2 : (MulAut.conj xG : MulAut G)⁻¹ • S = S := by
                  rw [← map_inv MulAut.conj]; exact h1
                calc (MulAut.conj xG : MulAut G) • S
                    = (MulAut.conj xG : MulAut G) •
                      ((MulAut.conj xG : MulAut G)⁻¹ • S) := by rw [h2]
                  _ = S := by rw [smul_inv_smul]
              have hu_smul : MulAut.conj xG u ∈ (MulAut.conj xG : MulAut G) • S := ⟨u, huS, rfl⟩
              rw [hsmul_eq] at hu_smul
              change xG * u * xG⁻¹ ∈ S
              exact hu_smul
            · intro hxu
              -- have: xG * u * xG⁻¹ ∈ S. Want u ∈ S.
              -- xG * u * xG⁻¹ ∈ S ⇒ MulAut.conj xG u ∈ S.
              -- Apply (MulAut.conj xG⁻¹ • -) and use hSx_eq.
              have h_smul_eq : (MulAut.conj xG⁻¹ : MulAut G) • S = S := hSx_eq
              have : MulAut.conj xG⁻¹ (xG * u * xG⁻¹) ∈ (MulAut.conj xG⁻¹ : MulAut G) • S :=
                ⟨xG * u * xG⁻¹, hxu, rfl⟩
              rw [h_smul_eq] at this
              -- MulAut.conj xG⁻¹ (xG * u * xG⁻¹) = xG⁻¹ * (xG * u * xG⁻¹) * xG = u.
              have hsimp : MulAut.conj xG⁻¹ (xG * u * xG⁻¹) = u := by
                change xG⁻¹ * (xG * u * xG⁻¹) * (xG⁻¹)⁻¹ = u
                group
              rwa [hsimp] at this
          -- Translate to x ∈ N_K(S.subgroupOf K), contradicting hx_not_norm.
          apply hx_not_norm
          rw [Subgroup.mem_normalizer_iff]
          intro a
          have hmem : ∀ b : K, b ∈ S.subgroupOf K ↔ (b : G) ∈ S := fun b => Subgroup.mem_subgroupOf
          rw [hmem a]
          have hcoe : (((x : K) * a * (x : K)⁻¹ : K) : G) = xG * (a : G) * xG⁻¹ := by
            push_cast; rfl
          rw [hmem _, hcoe]
          rw [Subgroup.mem_normalizer_iff] at hxG_norm_S
          exact hxG_norm_S a
        -- T > S strictly: Sx ≤ T, Sx ⊈ S.
        have hS_le_T : S ≤ T := le_sup_left
        have hS_lt_T : S < T := by
          refine lt_of_le_of_ne hS_le_T ?_
          intro hST
          apply hSx_not_le_S
          -- hST : S = T = S ⊔ Sx, so Sx ≤ S ⊔ Sx = S.
          have : Sx ≤ T := le_sup_right
          rw [← hST] at this
          exact this
        -- T.index < S.index.
        have : S.FiniteIndex := ⟨by rw [hIdx]; omega⟩
        have hT_idx_lt : T.index < S.index := Subgroup.index_strictAnti hS_lt_T
        -- ¬ T.IsSubnormal:
        -- T ≤ N_G(S) means S.subgroupOf T Normal. If T.IsSubnormal, then S.IsSubnormal via trans.
        have hT_not_sn : ¬ T.IsSubnormal := by
          intro hT_sn
          apply hS_not_sn
          have hS_norm_T : (S.subgroupOf T).Normal :=
            (Subgroup.normal_subgroupOf_iff_le_normalizer hS_le_T).mpr hT_le_NS
          exact Subgroup.IsSubnormal.trans hS_le_T hS_norm_T.isSubnormal hT_sn
        -- T satisfies hS_proper:
        have hT_proper : ∀ H : Subgroup G, T ≤ H → H ≠ ⊤ → (T.subgroupOf H).IsSubnormal := by
          intro H hTH hH_ne
          -- S ≤ T ≤ H, Sx ≤ T ≤ H.
          have hS_le_H : S ≤ H := hS_le_T.trans hTH
          have hSx_le_H : Sx ≤ H := le_sup_right.trans hTH
          -- (S.subgroupOf H).IsSubnormal by H1.
          have h1 : (S.subgroupOf H).IsSubnormal := hS_proper H hS_le_H hH_ne
          -- (Sx.subgroupOf H).IsSubnormal: apply H1 to MulAut.conj xG⁻¹ • H ≠ ⊤ (containing S).
          have hH_conj_ne_top : (MulAut.conj xG : MulAut G) • H ≠ ⊤ := by
            intro h
            apply hH_ne
            -- (MulAut.conj xG) is a MulAut, so it's a bijection. smul preserves ⊤ iff arg = ⊤.
            have h1 : (MulAut.conj xG : MulAut G) • H = (MulAut.conj xG : MulAut G) • ⊤ := by
              rw [h]
              ext y
              simp
            -- pointwise_smul cancels (it's a MulAut, hence bijection).
            have h2 : H ≤ ⊤ := le_top
            have h3 : ⊤ ≤ H :=
              Subgroup.pointwise_smul_le_pointwise_smul_iff.mp h1.ge
            exact le_antisymm h2 h3
          have hS_le_HConj : S ≤ (MulAut.conj xG : MulAut G) • H := by
            -- S = conj xG • Sx and Sx ≤ H, so S ≤ conj xG • H.
            have hSx_eq : (MulAut.conj xG : MulAut G) • Sx = S := by
              rw [hSx_def, ← smul_assoc]
              change (MulAut.conj xG * MulAut.conj xG⁻¹ : MulAut G) • S = S
              rw [← map_mul, mul_inv_cancel, map_one]
              exact one_smul _ _
            rw [← hSx_eq]
            exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hSx_le_H
          have h_sub_subn : (S.subgroupOf ((MulAut.conj xG : MulAut G) • H)).IsSubnormal :=
            hS_proper _ hS_le_HConj hH_conj_ne_top
          -- Transport via iso H ≃* conj xG • H. Under h ↦ xG h xG⁻¹,
          -- Sx.subgroupOf H corresponds to S.subgroupOf (conj xG • H).
          let φ : H →* ((MulAut.conj xG : MulAut G) • H : Subgroup G) :=
            (Subgroup.equivSMul (MulAut.conj xG) H).toMonoidHom
          have hφ_surj : Function.Surjective φ :=
            (Subgroup.equivSMul (MulAut.conj xG) H).surjective
          -- (S.subgroupOf (conj xG • H)).comap φ = Sx.subgroupOf H.
          have hcomap_eq : (S.subgroupOf ((MulAut.conj xG : MulAut G) • H)).comap φ =
              Sx.subgroupOf H := by
            ext ⟨h, hhH⟩
            constructor
            · intro hh
              -- hh : φ ⟨h, hhH⟩ ∈ S.subgroupOf (conj xG • H), i.e., (φ ⟨h, hhH⟩ : G) ∈ S.
              -- φ ⟨h, hhH⟩ has coercion to G = xG * h * xG⁻¹.
              rw [Subgroup.mem_subgroupOf]
              -- Goal: h ∈ Sx = conj xG⁻¹ • S = {xG⁻¹ * s * xG : s ∈ S}.
              -- From xG * h * xG⁻¹ ∈ S, h = xG⁻¹ * (xG * h * xG⁻¹) * xG ∈ Sx.
              rw [Subgroup.mem_comap] at hh
              rw [Subgroup.mem_subgroupOf] at hh
              -- hh : (φ ⟨h, hhH⟩ : G) ∈ S.
              -- φ ⟨h, hhH⟩ = ⟨xG * h * xG⁻¹, _⟩, so (φ ⟨h, hhH⟩ : G) = xG * h * xG⁻¹.
              refine ⟨xG * h * xG⁻¹, hh, ?_⟩
              change xG⁻¹ * (xG * h * xG⁻¹) * (xG⁻¹)⁻¹ = h
              group
            · intro hh
              rw [Subgroup.mem_comap]
              rw [Subgroup.mem_subgroupOf] at hh
              rw [Subgroup.mem_subgroupOf]
              -- hh : h ∈ Sx = conj xG⁻¹ • S. Get s ∈ S with h = xG⁻¹ * s * xG.
              rcases hh with ⟨s, hsS, hhs⟩
              -- φ ⟨h, hhH⟩ as G-element: xG * h * xG⁻¹.
              have hφ_coe : (((φ ⟨h, hhH⟩) :
                  ((MulAut.conj xG : MulAut G) • H : Subgroup G)) : G) = xG * h * xG⁻¹ := rfl
              -- Convert hhs : MulAut.conj xG⁻¹ s = h to xG * h * xG⁻¹ = s.
              have hsh : xG * h * xG⁻¹ = s := by
                -- hhs has form (MulDistribMulAction action).
                -- We unfold: pointwise smul of an element via MulAut is conj.
                -- The membership in MulAut.conj xG⁻¹ • S says ∃ s ∈ S, conj xG⁻¹ s = h.
                -- I.e., xG⁻¹ * s * xG = h.
                have hh_eq : xG⁻¹ * s * xG = h := by
                  have hh_eq' : (MulAut.conj xG⁻¹ : MulAut G) s = h := hhs
                  have h2 : (MulAut.conj xG⁻¹ : MulAut G) s = xG⁻¹ * s * xG := by
                    change xG⁻¹ * s * (xG⁻¹)⁻¹ = xG⁻¹ * s * xG
                    rw [inv_inv]
                  rw [← h2]; exact hh_eq'
                -- s = xG * h * xG⁻¹.
                have : s = xG * h * xG⁻¹ := by rw [← hh_eq]; group
                exact this.symm
              rw [hφ_coe, hsh]; exact hsS
          have h2 : (Sx.subgroupOf H).IsSubnormal := hcomap_eq ▸ h_sub_subn.comap φ
          -- (S.subgroupOf H).IsSubnormal and (Sx.subgroupOf H).IsSubnormal; their sup is subnormal.
          have hsup : ((S.subgroupOf H) ⊔ (Sx.subgroupOf H)).IsSubnormal :=
            isSubnormal_sup_of_isSubnormal h1 h2
          -- (S.subgroupOf H) ⊔ (Sx.subgroupOf H) = (S ⊔ Sx).subgroupOf H = T.subgroupOf H.
          rw [show (S.subgroupOf H) ⊔ (Sx.subgroupOf H) = T.subgroupOf H from
            (Subgroup.subgroupOf_sup hS_le_H hSx_le_H).symm] at hsup
          exact hsup
        -- Apply IH to T.
        obtain ⟨M', hM'_coatom, _, hM'_uniq⟩ :=
          ih T.index (hIdx ▸ hT_idx_lt) hT_proper hT_not_sn rfl
        -- Both M and K are maximal subgroups containing T (M via hT_le_M, K via hT_le_K).
        -- By uniqueness: M = M' and K = M'. So K = M.
        have hM_eq_M' : M = M' := hM'_uniq M hM_coatom hT_le_M
        have hK_eq_M' : K = M' := hM'_uniq K hK_coatom hT_le_K
        rw [hM_eq_M', hK_eq_M']

end

end OddOrder.Isaacs.Ch02


