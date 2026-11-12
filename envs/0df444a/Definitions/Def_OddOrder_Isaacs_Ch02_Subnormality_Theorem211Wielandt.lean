-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch02_Subnormality_Theorem211Wielandt
-- name    : OddOrder_Isaacs_Ch02_Subnormality_Theorem211Wielandt
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:52:08.07571+00:00
-- url     : https://prove2.me/theorems/6845fdc8-ccbc-4692-9ab6-c1aa8f13d2d0
-- title:
--   Isaacs Thm 2.11–2.12: Wielandt, Baer and Baer–Suzuki
-- statement:
--   A file of the Chapter 2 (Subnormality) formalization of Isaacs, *Finite Group Theory*, centred on Baer's theorem (Thm 2.12): for a subgroup $H$ of a finite group $G$, $H\le F(G)$ if and only if $\langle H,H^x\rangle$ is nilpotent for all $x\in G$. It also contains the Baer–Suzuki theorem in its single-element $p$-core form.
--
--   Declarations: the forward direction `baer_sup_conj_isNilpotent_of_le_fitting`, the generalized induction core `le_fitting_of_baer_aux`, the converse `le_fitting_of_baer_sup_conj_isNilpotent`, the iff form `le_fitting_iff_baer_sup_conj_isNilpotent`, and `baerSuzuki_pCore`.
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch02_Subnormality/Theorem211Wielandt.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch02_Subnormality/Theorem211Wielandt.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch02_Subnormality_Basic

open OddOrder.Isaacs.Ch01

namespace OddOrder.Isaacs.Ch02

section

variable {G : Type*} [Group G]

open scoped Pointwise in
/-- **Isaacs Thm 2.12 (Baer)** — 順方向: `H ≤ F(G)` ⇒ ∀x, `⟨H, H^x⟩` 冪零.

`H, H^x ⊆ F(G)` (F(G) ⊴ G で `H^x ⊆ F(G)`), `⟨H, H^x⟩ = H ⊔ H^x ≤ F(G)`,
F(G) 冪零, subgroup of nilpotent も冪零. -/
theorem baer_sup_conj_isNilpotent_of_le_fitting [Finite G] {H : Subgroup G}
    (hH : H ≤ fitting G) (x : G) :
    Group.IsNilpotent ↥(H ⊔ ((MulAut.conj x) • H : Subgroup G)) := by
  -- MulAut.conj x • F(G) = F(G) (F(G) ⊴ G).
  have hFnormal : (MulAut.conj x : MulAut G) • (fitting G : Subgroup G) = fitting G :=
    Subgroup.Normal.conj_smul_eq_self (h := fitting.normal G) x (fitting G)
  -- H^x ≤ F(G).
  have hHx_le : ((MulAut.conj x) • H : Subgroup G) ≤ fitting G := by
    rw [← hFnormal]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hH
  -- H ⊔ H^x ≤ F(G).
  have hSup_le : (H ⊔ ((MulAut.conj x) • H : Subgroup G)) ≤ fitting G := sup_le hH hHx_le
  -- Subgroup of nilpotent F(G) is nilpotent.
  exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSup_le)

open scoped Pointwise in
/-- **Isaacs Thm 2.12 (Baer)** 逆方向の `|G|`-induction の generalized core.

任意の有限群 `G` (with `Nat.card G ≤ n`) について,
`∀x ∈ G, ⟨H, H^x⟩ 冪零` ならば `H ≤ F(G)`.

Isaacs p.55 の証明戦略:
1. `x = 1` 適用で `H` 自身が冪零.
2. Thm 2.2 で `H ≤ F(G) ⟺ H 冪零 ∧ H 部分正規`. 部分正規性のみ示せばよい.
3. 部分正規性を背理法 + `|G|`-induction.  IH が真部分群 `K ⊇ H` で `H` の部分正規性を
   与える (Zipper Lemma の hypothesis を充足).
4. Zipper Lemma で `H` を含む極大 `M` 一意.
5. 各 `x` で `⟨H, H^x⟩` 冪零 ≠ ⊤ (= ⊤ なら `G` 冪零 ⇒ 矛盾) ⇒ `⟨H, H^x⟩ ⊆ M`.
6. 正規閉包 `H^G ⊆ M < ⊤`. IH で `H ⊴⊴ H^G ⊴ G`, 矛盾. -/
private theorem le_fitting_of_baer_aux :
    ∀ n, ∀ (G : Type*) [Group G] [Finite G],
      Nat.card G ≤ n → ∀ {H : Subgroup G},
      (∀ x : G, Group.IsNilpotent ↥(H ⊔ ((MulAut.conj x) • H : Subgroup G))) →
      H ≤ fitting G := by
  intro n
  induction n with
  | zero =>
    intro G _ _ hG _ _
    exact absurd (Nat.le_zero.mp hG) Nat.card_pos.ne'
  | succ n ih =>
    intro G _ _ _ H hN
    -- Step 0: H は冪零 (x = 1 で hN 適用).
    have hH_nilp : Group.IsNilpotent ↥H := by
      have h1 := hN 1
      rw [map_one, one_smul, sup_idem] at h1
      exact h1
    -- Step 1: H が部分正規であれば Thm 2.2 で結論.
    suffices hSn : H.IsSubnormal from
      (le_fitting_iff_isNilpotent_and_isSubnormal H).mpr ⟨hH_nilp, hSn⟩
    -- Step 2: H 部分正規でないと仮定 ⇒ 矛盾.
    by_contra hSnneg
    -- IH: 真部分群 K ⊇ H で H.subgroupOf K は部分正規.
    have hIH : ∀ K : Subgroup G, H ≤ K → K ≠ ⊤ →
        (H.subgroupOf K).IsSubnormal := by
      intro K hHK hKne
      have hK_card : Nat.card K ≤ n := by
        have hKle : Nat.card K ≤ Nat.card G := K.card_le_card_group
        have hKne_card : Nat.card K ≠ Nat.card G := fun heq =>
          hKne (Subgroup.eq_top_of_card_eq K heq)
        omega
      have hIH_K : (H.subgroupOf K) ≤ fitting K := by
        apply ih K hK_card
        intro y
        -- Permutability transfer G → ↥K via Subgroup.conj_smul_subgroupOf.
        rw [Subgroup.conj_smul_subgroupOf hHK]
        have hHy_le_K : ((MulAut.conj (y : G)) • H : Subgroup G) ≤ K :=
          Subgroup.conj_smul_le_of_le hHK y
        rw [← Subgroup.subgroupOf_sup hHK hHy_le_K]
        have : Group.IsNilpotent
            ↥(H ⊔ ((MulAut.conj (y : G)) • H) : Subgroup G) := hN (y : G)
        have hsup_le_K : (H ⊔ ((MulAut.conj (y : G)) • H) : Subgroup G) ≤ K :=
          sup_le hHK hHy_le_K
        exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hsup_le_K).symm
      exact ((le_fitting_iff_isNilpotent_and_isSubnormal _).mp hIH_K).2
    -- Zipper Lemma で `H` を含む極大部分群 `M` の一意性.
    obtain ⟨M, hMcoatom, _, hMuniq⟩ := zipper_lemma hIH hSnneg
    -- 各 x : G で `MulAut.conj x • H ≤ M`.
    have hHx_le_M : ∀ x : G, ((MulAut.conj x) • H : Subgroup G) ≤ M := by
      intro x
      have hNx := hN x
      -- ⟨H, H^x⟩ ≠ ⊤ (else G 冪零 ⇒ H 部分正規, 矛盾).
      have hsup_ne_top : (H ⊔ ((MulAut.conj x) • H : Subgroup G)) ≠ ⊤ := by
        intro h_top
        apply hSnneg
        rw [h_top] at hNx
        have := hNx
        have hG_nilp : Group.IsNilpotent G :=
          Group.nilpotent_of_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
        exact isSubnormal_of_isNilpotent_finite H
      -- ⟨H, H^x⟩ ≤ M (M は H を含む唯一の極大).
      obtain ⟨K, hKcoatom, hKle⟩ :=
        (eq_top_or_exists_le_coatom (H ⊔ ((MulAut.conj x) • H : Subgroup G) :
          Subgroup G)).resolve_left hsup_ne_top
      have hHK : H ≤ K := le_sup_left.trans hKle
      have hKM : K = M := hMuniq K hKcoatom hHK
      exact (le_sup_right.trans hKle).trans hKM.le
    -- 正規閉包 `H^G ≤ M`.
    have hNH_le_M : Subgroup.normalClosure (H : Set G) ≤ M := by
      rw [Subgroup.normalClosure, Subgroup.closure_le]
      intro y hy
      rcases Group.mem_conjugatesOfSet_iff.mp hy with ⟨a, haH, hConj⟩
      rcases hConj with ⟨c, hc⟩
      apply hHx_le_M (c : G)
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def]
      change ((c : G)⁻¹) * y * ((c : G)⁻¹)⁻¹ ∈ H
      rw [inv_inv]
      have hc_eq : (c : G) * a = y * (c : G) := hc
      have ha_eq : ((c : G)⁻¹) * y * ((c : G)) = a := by
        rw [mul_assoc, ← hc_eq]
        group
      rw [ha_eq]
      exact haH
    -- 正規閉包 < ⊤ (since ≤ M coatom).
    have hNH_lt : Subgroup.normalClosure (H : Set G) ≠ ⊤ := fun hNHtop =>
      hMcoatom.1 (le_top.antisymm (hNHtop.symm.le.trans hNH_le_M))
    -- IH を `normalClosure H` に適用.
    have hHle_NH : H ≤ Subgroup.normalClosure (H : Set G) :=
      Subgroup.le_normalClosure
    have hH_sn_in_NH : (H.subgroupOf (Subgroup.normalClosure (H : Set G))).IsSubnormal :=
      hIH _ hHle_NH hNH_lt
    have hNH_sn : (Subgroup.normalClosure (H : Set G)).IsSubnormal :=
      Subgroup.Normal.isSubnormal inferInstance
    exact hSnneg (Subgroup.IsSubnormal.trans hHle_NH hH_sn_in_NH hNH_sn)

open scoped Pointwise in
/-- **Isaacs Thm 2.12 (Baer)** 逆方向: `∀ x ∈ G, ⟨H, H^x⟩` 冪零 ⇒ `H ≤ F(G)`.

Isaacs p.55 の証明: Wielandt's Zipper Lemma (Thm 2.9) + Thm 2.2 経由の `|G|`-induction.
詳細は補助 [`le_fitting_of_baer_aux`](#le_fitting_of_baer_aux) の docstring 参照. -/
theorem le_fitting_of_baer_sup_conj_isNilpotent [Finite G] {H : Subgroup G}
    (hN : ∀ x : G, Group.IsNilpotent ↥(H ⊔ ((MulAut.conj x) • H : Subgroup G))) :
    H ≤ fitting G :=
  le_fitting_of_baer_aux (Nat.card G) G le_rfl hN

open scoped Pointwise in
/-- **Isaacs Thm 2.12 (Baer)** 完全形 (iff): 有限群 `G` の部分群 `H` について,
`H ≤ F(G) ↔ ∀ x ∈ G, ⟨H, H^x⟩ 冪零`.

順方向 (`baer_sup_conj_isNilpotent_of_le_fitting`) は F(G) ⊴ G の単なる帰結.
逆方向 (`le_fitting_of_baer_sup_conj_isNilpotent`) は Zipper Lemma 経由の核心. -/
theorem le_fitting_iff_baer_sup_conj_isNilpotent [Finite G] (H : Subgroup G) :
    H ≤ fitting G ↔
      ∀ x : G, Group.IsNilpotent ↥(H ⊔ ((MulAut.conj x) • H : Subgroup G)) :=
  ⟨fun hH => baer_sup_conj_isNilpotent_of_le_fitting hH,
   le_fitting_of_baer_sup_conj_isNilpotent⟩

/-- `H ≤ F(G)` で `H` が `p`-subgroup なら `H ≤ O_p(G)`.

証明: `F(G)` は冪零 ⇒ 各素数 `p` について Sylow `p` が一意 (`Sylow.normal_of_isNilpotent`
+ `Sylow.characteristic_of_normal`). `H` をその unique Sylow に含め, characteristic
in normal で `G` の正規 `p`-部分群 ⇒ `normal_pgroup_le_opCore` で `O_p(G)` 配下.

Matsuyama (Thm 2.13) と Baer-Suzuki p-core 単一元版 (`baerSuzuki_pCore`, lean-eval
problem) の両方で `F(G) → O_p(G)` 橋渡しに使う. -/
theorem mem_opCore_of_le_fitting_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime]
    {H : Subgroup G} (hH_pgroup : IsPGroup p H) (hH_fit : H ≤ fitting G) :
    H ≤ opCore p G := by
  -- Lift H to a subgroup of fitting G.
  set Hin : Subgroup (fitting G) := H.subgroupOf (fitting G) with hHin_def
  have hHin_pgroup : IsPGroup p Hin :=
    hH_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hH_fit).symm
  -- Sylow p of fitting G containing Hin.
  obtain ⟨Q, hHin_le_Q⟩ := hHin_pgroup.exists_le_sylow
  have hQ_normal : (Q : Subgroup (fitting G)).Normal := Sylow.normal_of_isNilpotent _
  have hQ_char : (Q : Subgroup (fitting G)).Characteristic :=
    Sylow.characteristic_of_normal _ hQ_normal
  have : ((Q : Subgroup (fitting G)).map (fitting G).subtype).Normal := inferInstance
  have hpgroupG : IsPGroup p ((Q : Subgroup (fitting G)).map (fitting G).subtype) :=
    Q.2.map (fitting G).subtype
  have hQ_le_op : (Q : Subgroup (fitting G)).map (fitting G).subtype ≤ opCore p G :=
    normal_pgroup_le_opCore hpgroupG
  intro x hx
  have hx_fit : x ∈ fitting G := hH_fit hx
  have hx_Hin : (⟨x, hx_fit⟩ : fitting G) ∈ Hin := by
    rw [hHin_def, Subgroup.mem_subgroupOf]
    exact hx
  have hx_Q : (⟨x, hx_fit⟩ : fitting G) ∈ (Q : Subgroup (fitting G)) :=
    hHin_le_Q hx_Hin
  exact hQ_le_op ⟨⟨x, hx_fit⟩, hx_Q, rfl⟩

open scoped Pointwise in
/-- **Baer-Suzuki Theorem (single-element p-core form)**: 有限群 `G` の元 `x`,
素数 `p` について,
`x ∈ O_p(G) ↔ ∀ g : G, ⟨x, g·x·g⁻¹⟩` is a `p`-group.

これは Isaacs Thm 2.12 (Baer, `H ≤ F(G) ↔ ∀ x ∈ G, ⟨H, H^x⟩` 冪零) の
`H := ⟨x⟩` への特殊化と, `p`-元 ∈ `F(G)` ⇒ `p`-元 ∈ `O_p(G)`
([`mem_opCore_of_le_fitting_of_isPGroup`](#mem_opCore_of_le_fitting_of_isPGroup))
の合成で得られる.

- 順方向 (`⇒`): `O_p(G) ⊴ G` で共役不変 ⇒ `closure {x, gxg⁻¹} ≤ O_p(G)`,
  `O_p(G)` は `p`-群 ⇒ 部分群も `p`-群.
- 逆方向 (`⇐`): `g = 1` で `⟨x⟩` が `p`-群; 各 `g` で `⟨x⟩ ⊔ ⟨x⟩^g
  = ⟨x, gxg⁻¹⟩` が `p`-群 ⇒ 冪零. Baer 2.12 で `⟨x⟩ ≤ F(G)`, 橋渡し
  で `⟨x⟩ ≤ O_p(G)`.

lean-eval problem suite signature:
<https://lean-lang.org/eval/problems/baer_suzuki/>
(eval 側の `LeanEval.GroupTheory.Defs.pCore` は本 repo の
[`OddOrder.Isaacs.Ch01.opCore`](Ch01_Sylow/Main.lean#L533) と同じく最大正規 `p`-部分群).

古典 Baer-Suzuki theorem は通常 subset 版 (`X ⊆ O_p(G) ↔ ∀ a b ∈ X,
⟨a, b⟩` p-群) で語られるが, 本定理はその単一元への特殊化. -/
theorem baerSuzuki_pCore [Finite G] {p : ℕ} [Fact p.Prime] (x : G) :
    x ∈ opCore p G ↔
      ∀ g : G, IsPGroup p ↥(Subgroup.closure ({x, g * x * g⁻¹} : Set G)) := by
  refine ⟨?_, ?_⟩
  · -- (⇒) x ∈ O_p(G) ⇒ closure {x, gxg⁻¹} ≤ O_p(G), 部分群は p-群.
    intro hx g
    have hOp_pgroup : IsPGroup p ↥(opCore p G) := opCore_isPGroup p G
    have hgx : g * x * g⁻¹ ∈ opCore p G :=
      (opCore.normal p G).conj_mem x hx g
    have hclos_le : Subgroup.closure ({x, g * x * g⁻¹} : Set G) ≤ opCore p G := by
      rw [Subgroup.closure_le]
      intro y hy
      rcases hy with rfl | hy
      · exact hx
      · rw [Set.mem_singleton_iff] at hy
        exact hy ▸ hgx
    exact hOp_pgroup.of_injective (Subgroup.inclusion hclos_le)
      (Subgroup.inclusion_injective hclos_le)
  · -- (⇐) ∀ g, closure {x, gxg⁻¹} p-群 ⇒ Isaacs 2.12 iff で ⟨x⟩ ≤ F(G), 橋渡しで x ∈ O_p(G).
    intro hPg
    -- ⟨x⟩ は p-群 (g = 1 で closure {x, x} = ⟨x⟩).
    have hx_pgroup : IsPGroup p ↥(Subgroup.zpowers x) := by
      have h1 := hPg 1
      have h_set : ({x, 1 * x * 1⁻¹} : Set G) = {x} := by simp
      rw [h_set, ← Subgroup.zpowers_eq_closure] at h1
      exact h1
    -- ⟨x⟩ ⊔ (MulAut.conj g) • ⟨x⟩ = closure {x, gxg⁻¹}.
    have hsup_eq : ∀ g : G,
        (Subgroup.zpowers x ⊔ ((MulAut.conj g) • Subgroup.zpowers x : Subgroup G))
          = Subgroup.closure ({x, g * x * g⁻¹} : Set G) := by
      intro g
      -- まず (MulAut.conj g) • ⟨x⟩ = ⟨gxg⁻¹⟩.
      have h_conj : (MulAut.conj g : MulAut G) • Subgroup.zpowers x
          = Subgroup.zpowers (g * x * g⁻¹) := by
        rw [Subgroup.zpowers_eq_closure x,
            Subgroup.zpowers_eq_closure (g * x * g⁻¹),
            Subgroup.smul_closure]
        congr 1
        ext y
        simp [MulAut.smul_def, MulAut.conj_apply]
      -- closure {x} ⊔ closure {gxg⁻¹} = closure ({x} ∪ {gxg⁻¹}) = closure {x, gxg⁻¹}.
      rw [h_conj, Subgroup.zpowers_eq_closure x,
          Subgroup.zpowers_eq_closure (g * x * g⁻¹),
          ← Subgroup.closure_union]
      congr 1
    -- Baer 仮定: ∀ g, ⟨x⟩ ⊔ ⟨x⟩^g 冪零.
    have hbaer : ∀ g : G,
        Group.IsNilpotent ↥(Subgroup.zpowers x ⊔
          ((MulAut.conj g) • Subgroup.zpowers x : Subgroup G)) := by
      intro g
      rw [hsup_eq g]
      exact (hPg g).isNilpotent
    -- Isaacs 2.12 iff ⇒ ⟨x⟩ ≤ F(G).
    have hxle_fit : Subgroup.zpowers x ≤ fitting G :=
      (le_fitting_iff_baer_sup_conj_isNilpotent _).mpr hbaer
    -- 橋渡し: ⟨x⟩ p-群 + ⟨x⟩ ≤ F(G) ⇒ ⟨x⟩ ≤ O_p(G).
    exact mem_opCore_of_le_fitting_of_isPGroup hx_pgroup hxle_fit
      (Subgroup.mem_zpowers x)

end

end OddOrder.Isaacs.Ch02


