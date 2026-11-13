-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03f_R0Action
-- name    : OddOrder_BG_Ch1_Preliminary_S03f_R0Action
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:07:21.658487+00:00
-- url     : https://prove2.me/theorems/6c7fb497-293a-41ab-8232-ab7f2d49804e
-- title:
--   BG §3: Theorem 3.6, Phase C, the action of $R_0$ ((3.17)–(3.21))
-- statement:
--   Phase C of the minimal-counterexample proof of Theorem 3.6 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §3, as a standalone lemma using only the phase A/B facts. It covers (3.17) $[K,R_0]\ne 1$, the ambient structure $S_1:=K_G R_0$, (3.18) $C_{S_1}(V_G)=1$ and (3.19) $|C_{V_G}(R_0)|=p$, through (3.21).
--
--   The main declaration: `r0_action_facts`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S03f_R0Action.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S03f_R0Action.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S01b_Prop116
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03_FrobeniusActions
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03f_OrbitParity
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03f_Prelim
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03d_Thm34
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03e_Thm35
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_PLengthTransfer
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_OperatorQuotientAction
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_OperatorMaschke
import Definitions.Def_OddOrder_GroupTheory_ZGroup

namespace OddOrder.BG.Ch1.S03f

open scoped commutatorElement Pointwise IsMulCommutative

open OddOrder.GroupTheory OddOrder.Isaacs.Ch04 OddOrder.BG.Ch1.OperatorQuotientAction

set_option maxHeartbeats 2400000 in
-- the `IsMulCommutative` scoped instances (priority 50) cycle with `CommMagma.to_isCommutative`;
-- failing class searches must exhaust that branch (cf. `S03f_Thm36`)
set_option synthInstance.maxHeartbeats 400000 in
/-- **BG Theorem 3.6, Phase C** ((3.17)–(3.21), mmd L1010-L1090): the action of `R₀`.
IH-free segment of the minimal-counterexample proof.  From the phase A/B structure
(`V = F(H)` elementary abelian and self-centralizing, `K` the `R`-invariant complement of
`V` in the preimage of `F(H/V)`, `P` an invariant Sylow `p`-subgroup of `N_H(K)`) it
produces, at the ambient (`G`) level: `[K,R₀] ≠ 1` ((3.17)), `C_{S₁}(V_G) = ⊥` ((3.18)),
`V_G ⊴ G` elementary abelian with `|C_{V_G}(R₀)| = p` ((3.19)), and `⁅P_G, R₀⁆ = P_G`
((3.21)), plus the bookkeeping facts `¬ r ∣ |K|`, `V ≠ ⊥`, `p ≠ r`. -/
theorem r0_action_facts
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] (hodd : Odd (Nat.card G))
    {p r a : ℕ} (hp : p.Prime) (hr_prime : r.Prime)
    {H R R₀ : Subgroup G} [H.Normal]
    (hcompl : Subgroup.IsComplement' H R)
    (hHall : Nat.Coprime (Nat.card ↥H) (Nat.card ↥R))
    (hR₀R : R₀ ≤ R)
    (hr_card : Nat.card ↥R₀ = r)
    (hZ : OddOrder.GroupTheory.IsZGroup ↥(H ⊓ Subgroup.centralizer (R₀ : Set G)))
    (hcounter : ¬ hasPLengthOne p ↥(⁅H, R⁆ : Subgroup G))
    (h36 : (⁅H, R⁆ : Subgroup G) = H)
    {V K N P : Subgroup ↥H}
    (hVdef : V = OddOrder.Isaacs.Ch01.fitting ↥H)
    [hVnorm : V.Normal] [hVchar : V.Characteristic]
    (hVelem : IsElementaryAbelian p ↥V)
    (hCHV : Subgroup.centralizer ((V : Subgroup ↥H) : Set ↥H) = V)
    (hVa : Nat.card ↥V = p ^ a)
    (hp_ndvd : ¬ p ∣ Nat.card ↥(OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V)))
    (hfalse_of_pndvd : ¬ p ∣ Nat.card (↥H ⧸ V) → False)
    (hKmap : K.map (QuotientGroup.mk' V) = OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V))
    (hKp_ndvd : ¬ p ∣ Nat.card ↥K)
    (hVK_inf : V ⊓ K = ⊥)
    (hK_inv : OddOrder.Isaacs.Ch03.IsAInvariant
      ((MulAut.conjNormal (G := G) (H := H)).comp R.subtype) K)
    (hV_inv : OddOrder.Isaacs.Ch03.IsAInvariant
      ((MulAut.conjNormal (G := G) (H := H)).comp R.subtype) V)
    (hP_inv : OddOrder.Isaacs.Ch03.IsAInvariant
      ((MulAut.conjNormal (G := G) (H := H)).comp R.subtype) P)
    (hK_le_N : K ≤ N) (hP_le_N : P ≤ N)
    (hVN_inf : V ⊓ N = ⊥)
    (hKN_fit : K.subgroupOf N = OddOrder.Isaacs.Ch01.fitting ↥N)
    (hPp : IsPGroup p ↥P) :
    ¬ ((K.map H.subtype : Subgroup G) ≤ Subgroup.centralizer (R₀ : Set G)) ∧
    ¬ r ∣ Nat.card ↥K ∧
    (V.map H.subtype : Subgroup G).Normal ∧
    ((K.map H.subtype : Subgroup G) ⊔ R₀)
      ⊓ Subgroup.centralizer ((V.map H.subtype : Subgroup G) : Set G) = ⊥ ∧
    V ≠ ⊥ ∧ p ≠ r ∧
    IsElementaryAbelian p ↥(V.map H.subtype : Subgroup G) ∧
    Nat.card ↥((V.map H.subtype : Subgroup G) ⊓ Subgroup.centralizer (R₀ : Set G)) = p ∧
    (⁅(P.map H.subtype : Subgroup G), R₀⁆ : Subgroup G) = P.map H.subtype := by
    have : Fact p.Prime := ⟨hp⟩
    set φ : ↥R →* MulAut ↥H := (MulAut.conjNormal (G := G) (H := H)).comp R.subtype with hφ
    have h317 : ¬ ((K.map H.subtype : Subgroup G) ≤ Subgroup.centralizer (R₀ : Set G)) := by
      intro hKcent
      -- `K` is a nilpotent `Z`-group, hence cyclic.
      have hKG_Z : _root_.IsZGroup ↥(K.map H.subtype) := by
        have hle : K.map H.subtype ≤ H ⊓ Subgroup.centralizer (R₀ : Set G) :=
          le_inf (Subgroup.map_subtype_le K) hKcent
        have := isZGroup_iff_mathlib.mp hZ
        exact IsZGroup.of_injective (Subgroup.inclusion_injective hle)
      have hK_nilp : Group.IsNilpotent ↥(K.map H.subtype) := by
        have e1 := Subgroup.equivMapOfInjective K H.subtype H.subtype_injective
        have e2 := Subgroup.subgroupOfEquivOfLe hK_le_N
        have : Group.IsNilpotent ↥(K.subgroupOf N) := by
          rw [hKN_fit]
          infer_instance
        refine Group.nilpotent_of_surjective (e1.toMonoidHom.comp e2.toMonoidHom) ?_
        rw [MonoidHom.coe_comp]
        exact e1.surjective.comp e2.surjective
      have hKG_cyc : IsCyclic ↥(K.map H.subtype) := inferInstance
      have hK_cyc : IsCyclic ↥K := by
        have e1 := Subgroup.equivMapOfInjective K H.subtype H.subtype_injective
        exact isCyclic_of_surjective e1.symm e1.symm.surjective
      -- hence `F(H/V) ≅ K` is cyclic (`mk' V` is injective on `K` since `V ⊓ K = ⊥`).
      have hFQ_cyc : IsCyclic ↥(OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V)) := by
        have hinj : Function.Injective ((QuotientGroup.mk' V).comp K.subtype) := by
          rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
          intro x hx
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
            QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
          have hxm : (x : ↥H) ∈ V ⊓ K := ⟨hx, x.2⟩
          rw [hVK_inf, Subgroup.mem_bot] at hxm
          rw [Subgroup.mem_bot]
          exact Subtype.ext hxm
        have hrange : ((QuotientGroup.mk' V).comp K.subtype).range
            = K.map (QuotientGroup.mk' V) := by
          rw [MonoidHom.range_comp, K.range_subtype]
        have e3 : ↥K ≃* ↥(OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V)) :=
          (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (hrange.trans hKmap))
        exact isCyclic_of_surjective e3 e3.surjective
      -- the induced `R`-action on `Q = ↥H ⧸ V` has full action commutator ((3.6)).
      set φQ : ↥R →* MulAut (↥H ⧸ V) :=
        OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hV_inv with hφQ
      have hACH : OddOrder.Isaacs.Ch04.actionCommutator φ = ⊤ := by
        have hb := actionCommutator_conjNormal_map_subtype_eq H R
        rw [h36] at hb
        rw [eq_top_iff]
        intro x _
        have hx : (x : G) ∈ (OddOrder.Isaacs.Ch04.actionCommutator φ).map H.subtype := by
          rw [hb]
          exact x.2
        obtain ⟨y, hy, hyx⟩ := hx
        rwa [show y = x from Subtype.ext hyx] at hy
      have hACQ : OddOrder.Isaacs.Ch04.actionCommutator φQ = ⊤ := by
        have hmap_le : (OddOrder.Isaacs.Ch04.actionCommutator φ).map (QuotientGroup.mk' V)
            ≤ OddOrder.Isaacs.Ch04.actionCommutator φQ := by
          rw [Subgroup.map_le_iff_le_comap, OddOrder.Isaacs.Ch04.actionCommutator,
            Subgroup.closure_le]
          rintro _ ⟨g, r, rfl⟩
          rw [SetLike.mem_coe, Subgroup.mem_comap]
          have hgen : (QuotientGroup.mk' V) (g * (φ r) g⁻¹)
              = (QuotientGroup.mk' V g) * (φQ r) ((QuotientGroup.mk' V g)⁻¹) := by
            rw [map_mul, hφQ, ← map_inv,
              OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk']
          rw [hgen]
          exact Subgroup.subset_closure ⟨_, _, rfl⟩
        rw [eq_top_iff]
        calc (⊤ : Subgroup (↥H ⧸ V))
            = (⊤ : Subgroup ↥H).map (QuotientGroup.mk' V) :=
              (Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective V)).symm
          _ = (OddOrder.Isaacs.Ch04.actionCommutator φ).map (QuotientGroup.mk' V) := by
              rw [hACH]
          _ ≤ OddOrder.Isaacs.Ch04.actionCommutator φQ := hmap_le
      -- cyclic + normal + invariant: the action commutator centralizes `F(Q)`; with (3.6) and
      -- Prop 1.3, `F(Q) = ⊤`, so `p ∤ |Q|` (`F(Q)` is a `p'`-group) — contradiction.
      have hFQ_inv : OddOrder.Isaacs.Ch03.IsAInvariant φQ
          (OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V)) :=
        OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic φQ
      have hAC_le := actionCommutator_le_centralizer_of_isCyclic_isAInvariant
        (OddOrder.Isaacs.Ch01.fitting.normal (↥H ⧸ V)) hFQ_inv
      rw [hACQ, top_le_iff] at hAC_le
      have hFQ_top : OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V) = ⊤ := by
        rw [eq_top_iff, ← hAC_le]
        exact OddOrder.GroupTheory.centralizer_fitting_le_fitting
      apply hfalse_of_pndvd
      intro hdvd
      apply hp_ndvd
      have hcardtop : Nat.card ↥(⊤ : Subgroup (↥H ⧸ V)) = Nat.card (↥H ⧸ V) :=
        Nat.card_congr Subgroup.topEquiv.toEquiv
      rw [hFQ_top, hcardtop]
      exact hdvd
    -- **(3.18)** `C_{KR₀}(V) = ⊥` (at the `G` level).  The `K`-part dies by (3.10)+(3.14)
    -- (`C_K(V) ≤ K ⊓ C_H(V) = K ⊓ V = ⊥`); so `C := C_{KR₀}(V)` is a normal subgroup of `KR₀`
    -- meeting `K` trivially, hence of order dividing `r = |R₀|`.  If `C ≠ ⊥` then `|C| = r`;
    -- a second order-`r` subgroup (`R₀` itself) distinct from the normal `C` would force
    -- `r² ∣ |KR₀| = |K|·r`, impossible; so `C = R₀ ⊴ KR₀`, making `⁅K,R₀⁆ ≤ K ⊓ R₀ = ⊥`,
    -- contradicting (3.17).
    set KG : Subgroup G := K.map H.subtype with hKG
    set VG : Subgroup G := V.map H.subtype with hVG
    set KG : Subgroup G := K.map H.subtype with hKG
    set S₁ : Subgroup G := KG ⊔ R₀ with hS₁
    have hKG_le_S₁ : KG ≤ S₁ := le_sup_left
    have hR₀_le_S₁ : R₀ ≤ S₁ := le_sup_right
    have hKG_le_H : KG ≤ H := Subgroup.map_subtype_le K
    -- `S₁ ≤ N_G(KG)` (`K` is `R`-invariant), so `KG.subgroupOf S₁` is normal.
    have hS₁norm : S₁ ≤ Subgroup.normalizer (KG : Set G) := by
      refine sup_le Subgroup.le_normalizer ?_
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨k, hk, rfl⟩
        refine ⟨φ ⟨g, hR₀R hg⟩ k, hK_inv.smul_mem _ hk, ?_⟩
        simp only [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply]
      · rintro hgx
        obtain ⟨k, hk, hkeq⟩ := hgx
        refine ⟨(φ ⟨g, hR₀R hg⟩)⁻¹ k, hK_inv.inv_smul_mem _ hk, ?_⟩
        have hv2 : ((φ ⟨g, hR₀R hg⟩ ((φ ⟨g, hR₀R hg⟩)⁻¹ k) : ↥H) : G)
            = g * (((φ ⟨g, hR₀R hg⟩)⁻¹ k : ↥H) : G) * g⁻¹ := by
          simp only [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply]
        rw [MulAut.apply_inv_self] at hv2
        have h3 := hv2.symm.trans hkeq
        exact mul_left_cancel (mul_right_cancel h3)
    have hKG'norm : ((KG.subgroupOf S₁) : Subgroup ↥S₁).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hS₁norm
    -- complement `KG' ⋊ R₀'` inside `S₁`, and the resulting cardinalities.
    have hdisjKR : Disjoint KG R₀ :=
      (hcompl.disjoint.mono hKG_le_H hR₀R)
    have hcompl₁ : Subgroup.IsComplement' (KG.subgroupOf S₁) (R₀.subgroupOf S₁) := by
      refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
      · refine disjoint_iff.mpr (eq_bot_iff.mpr fun x hx => ?_)
        rw [Subgroup.mem_inf] at hx
        simp only [Subgroup.mem_subgroupOf] at hx
        have hmem : (x : G) ∈ KG ⊓ R₀ := ⟨hx.1, hx.2⟩
        rw [hdisjKR.eq_bot, Subgroup.mem_bot] at hmem
        rw [Subgroup.mem_bot]
        exact Subtype.ext (by simpa using hmem)
      · have hsup : ((KG.subgroupOf S₁) : Subgroup ↥S₁) ⊔ (R₀.subgroupOf S₁) = ⊤ := by
          rw [← Subgroup.subgroupOf_sup hKG_le_S₁ hR₀_le_S₁, Subgroup.subgroupOf_self]
        have hmul := Subgroup.normal_mul ((KG.subgroupOf S₁) : Subgroup ↥S₁) (R₀.subgroupOf S₁)
        rw [hsup, Subgroup.coe_top] at hmul
        exact hmul.symm
    have hR₀'card : Nat.card ↥(R₀.subgroupOf S₁) = r :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀_le_S₁).toEquiv).trans hr_card
    have hKG'card : Nat.card ↥(KG.subgroupOf S₁) = Nat.card ↥K :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKG_le_S₁).toEquiv).trans
        (Subgroup.card_map_of_injective H.subtype_injective)
    have hr_ndvd_K : ¬ r ∣ Nat.card ↥K := by
      intro hdvd
      have h1 : r ∣ Nat.card ↥H :=
        hdvd.trans (Subgroup.card_subgroup_dvd_card K)
      have h2 : r ∣ Nat.card ↥R := hr_card ▸ Subgroup.card_dvd_of_le hR₀R
      have := Nat.Coprime.eq_one_of_dvd (hHall.coprime_dvd_left h1) h2
      exact hr_prime.one_lt.ne' this
    have hVGnorm : VG.Normal := by
      constructor
      intro n hn gg
      obtain ⟨v, hv, rfl⟩ := hn
      have hvH : gg * (v : G) * gg⁻¹ ∈ H := (inferInstance : H.Normal).conj_mem _ v.2 gg
      have hfix : V.map (MulAut.conjNormal gg).toMonoidHom = V :=
        Subgroup.characteristic_iff_map_eq.mp hVchar (MulAut.conjNormal gg)
      have hmem : MulAut.conjNormal gg v ∈ V := by
        rw [← hfix]
        exact Subgroup.mem_map_of_mem _ hv
      exact ⟨MulAut.conjNormal gg v, hmem, by
        rw [Subgroup.coe_subtype, MulAut.conjNormal_apply]⟩
    have h318 : S₁ ⊓ Subgroup.centralizer (VG : Set G) = ⊥ := by
      -- main step: the centralizer part `C` is `⊥`.
      rw [eq_bot_iff]
      intro g hg
      obtain ⟨hgS₁, hgc⟩ := Subgroup.mem_inf.mp hg
      set C : Subgroup G := S₁ ⊓ Subgroup.centralizer (VG : Set G) with hC
      by_contra hgne
      rw [Subgroup.mem_bot] at hgne
      -- `C ⊓ KG = ⊥` ((3.10) + (3.14): a `K`-element centralizing `V` lies in `V ⊓ K = ⊥`).
      have hCK : C ⊓ KG = ⊥ := by
        rw [eq_bot_iff]
        rintro x ⟨⟨_, hxc⟩, hxK⟩
        obtain ⟨k, hk, rfl⟩ := hxK
        have hkcent : k ∈ Subgroup.centralizer ((V : Subgroup ↥H) : Set ↥H) := by
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          apply Subtype.ext
          rw [Subgroup.coe_mul, Subgroup.coe_mul]
          exact Subgroup.mem_centralizer_iff.mp hxc (w : G) ⟨w, hw, rfl⟩
        rw [hCHV] at hkcent
        have hkb : k ∈ V ⊓ K := ⟨hkcent, hk⟩
        rw [hVK_inf, Subgroup.mem_bot] at hkb
        rw [Subgroup.mem_bot, hkb]
        simp
      -- `C.subgroupOf S₁` is normal (`C_G(V_G) ⊴ G` since `V_G ⊴ G`).
      have hC'norm : ((C.subgroupOf S₁) : Subgroup ↥S₁).Normal := by
        constructor
        intro c hc s
        rw [Subgroup.mem_subgroupOf] at hc ⊢
        obtain ⟨hcS₁, hcc⟩ := Subgroup.mem_inf.mp hc
        refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ s.2 hcS₁)
          (Subgroup.inv_mem _ s.2), ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hy' : (s : G)⁻¹ * y * (s : G) ∈ VG := by
          have := hVGnorm.conj_mem y hy (s : G)⁻¹
          simpa using this
        have hcy := Subgroup.mem_centralizer_iff.mp hcc _ hy'
        calc y * ((s : G) * (c : G) * (s : G)⁻¹)
            = (s : G) * (((s : G)⁻¹ * y * (s : G)) * (c : G)) * (s : G)⁻¹ := by group
          _ = (s : G) * ((c : G) * ((s : G)⁻¹ * y * (s : G))) * (s : G)⁻¹ := by rw [hcy]
          _ = ((s : G) * (c : G) * (s : G)⁻¹) * y := by group
      -- `|C'| ∣ r`: `C'` embeds into `S₁/KG'`, which has order `r`.
      have hquot_card : Nat.card (↥S₁ ⧸ ((KG.subgroupOf S₁) : Subgroup ↥S₁)) = r := by
        have h1 : Nat.card ↥S₁ = Nat.card (↥S₁ ⧸ ((KG.subgroupOf S₁) : Subgroup ↥S₁))
            * Nat.card ↥(KG.subgroupOf S₁) :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup _
        have h2 : Nat.card ↥(KG.subgroupOf S₁) * Nat.card ↥(R₀.subgroupOf S₁)
            = Nat.card ↥S₁ := hcompl₁.card_mul_card
        rw [← h2, mul_comm (Nat.card ↥(KG.subgroupOf S₁))] at h1
        have h3 := Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(KG.subgroupOf S₁))) h1
        rw [← h3]
        exact hR₀'card
      have hCcard_dvd : Nat.card ↥(C.subgroupOf S₁) ∣ r := by
        rw [← hquot_card]
        refine Subgroup.card_dvd_of_injective
          ((QuotientGroup.mk' ((KG.subgroupOf S₁) : Subgroup ↥S₁)).comp
            (C.subgroupOf S₁).subtype) ?_
        rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
        intro x hx
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
          QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
        have hxC : ((x : ↥S₁) : G) ∈ C := Subgroup.mem_subgroupOf.mp x.2
        have hxb : ((x : ↥S₁) : G) ∈ C ⊓ KG := ⟨hxC, hx⟩
        rw [hCK, Subgroup.mem_bot] at hxb
        rw [Subgroup.mem_bot]
        exact Subtype.ext (Subtype.ext hxb)
      rcases (Nat.dvd_prime hr_prime).mp hCcard_dvd with h1card | hCr
      · -- `|C'| = 1` ⟹ `C = ⊥` ⟹ `g = 1`, contradiction with `hgne`.
        have hC'bot : (C.subgroupOf S₁ : Subgroup ↥S₁) = ⊥ :=
          Subgroup.eq_bot_of_card_eq _ h1card
        have hgC' : (⟨g, hgS₁⟩ : ↥S₁) ∈ C.subgroupOf S₁ :=
          Subgroup.mem_subgroupOf.mpr ⟨hgS₁, hgc⟩
        rw [hC'bot, Subgroup.mem_bot] at hgC'
        exact hgne (by simpa using congrArg Subtype.val hgC')
      · -- `|C'| = r`: then `C' = R₀'` (else `r² ∣ |S₁| = |K|·r`), so `R₀'` is normal in `S₁`,
        -- `⁅KG',R₀'⁆ ≤ KG' ⊓ R₀' = ⊥`, and `K` centralizes `R₀` — contradicting (3.17).
        exfalso
        have hCR₀ : (C.subgroupOf S₁ : Subgroup ↥S₁) = R₀.subgroupOf S₁ := by
          by_contra hne
          have hinf_bot : (C.subgroupOf S₁ : Subgroup ↥S₁) ⊓ (R₀.subgroupOf S₁) = ⊥ := by
            by_contra hinfne
            have hle1 : Nat.card ↥((C.subgroupOf S₁ : Subgroup ↥S₁) ⊓ (R₀.subgroupOf S₁)) ∣ r := by
              rw [← hCr]
              exact Subgroup.card_dvd_of_le inf_le_left
            rcases (Nat.dvd_prime hr_prime).mp hle1 with hi1 | hir
            · exact hinfne (Subgroup.eq_bot_of_card_eq _ hi1)
            · have he1 : (C.subgroupOf S₁ : Subgroup ↥S₁) ⊓ (R₀.subgroupOf S₁)
                  = C.subgroupOf S₁ :=
                Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (hCr.trans hir.symm))
              have he2 : (C.subgroupOf S₁ : Subgroup ↥S₁) ⊓ (R₀.subgroupOf S₁)
                  = R₀.subgroupOf S₁ :=
                Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq (hR₀'card.trans hir.symm))
              exact hne (he1.symm.trans he2)
          -- the image of `R₀'` in `S₁/C'` is injective, so `r ∣ |S₁/C'|` and `r² ∣ |S₁|`.
          have hrdvd_quot : r ∣ Nat.card (↥S₁ ⧸ (C.subgroupOf S₁ : Subgroup ↥S₁)) := by
            have hinj : Function.Injective
                ((QuotientGroup.mk' (C.subgroupOf S₁ : Subgroup ↥S₁)).comp
                  (R₀.subgroupOf S₁).subtype) := by
              rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
              intro x hx
              rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
                QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
              have hxm : (x : ↥S₁) ∈ (C.subgroupOf S₁ : Subgroup ↥S₁) ⊓ (R₀.subgroupOf S₁) :=
                ⟨hx, x.2⟩
              rw [hinf_bot, Subgroup.mem_bot] at hxm
              rw [Subgroup.mem_bot]
              exact Subtype.ext hxm
            rw [← hR₀'card]
            exact Subgroup.card_dvd_of_injective _ hinj
          have hr2 : r * r ∣ Nat.card ↥S₁ := by
            rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
              (C.subgroupOf S₁ : Subgroup ↥S₁)]
            exact mul_dvd_mul hrdvd_quot (dvd_of_eq hCr.symm)
          have hS₁card : Nat.card ↥S₁ = Nat.card ↥K * r := by
            rw [← hcompl₁.card_mul_card, hKG'card, hR₀'card]
          rw [hS₁card] at hr2
          exact hr_ndvd_K ((Nat.mul_dvd_mul_iff_right hr_prime.pos).mp hr2)
        have hR₀'norm : ((R₀.subgroupOf S₁) : Subgroup ↥S₁).Normal := hCR₀ ▸ hC'norm
        have hcomm_bot :
            (⁅(KG.subgroupOf S₁ : Subgroup ↥S₁), R₀.subgroupOf S₁⁆ : Subgroup ↥S₁) = ⊥ := by
          rw [eq_bot_iff, ← hcompl₁.disjoint.eq_bot]
          exact le_inf (Subgroup.commutator_le_left _ _) (Subgroup.commutator_le_right _ _)
        apply h317
        intro x hxK
        rw [Subgroup.mem_centralizer_iff]
        intro y hyR₀
        have hx' : (⟨x, hKG_le_S₁ hxK⟩ : ↥S₁) ∈ KG.subgroupOf S₁ :=
          Subgroup.mem_subgroupOf.mpr hxK
        have hy' : (⟨y, hR₀_le_S₁ hyR₀⟩ : ↥S₁) ∈ R₀.subgroupOf S₁ :=
          Subgroup.mem_subgroupOf.mpr hyR₀
        have hcomm1 : ⁅(⟨x, hKG_le_S₁ hxK⟩ : ↥S₁), (⟨y, hR₀_le_S₁ hyR₀⟩ : ↥S₁)⁆ = 1 := by
          have hm := Subgroup.commutator_mem_commutator hx' hy'
          rwa [hcomm_bot, Subgroup.mem_bot] at hm
        have hc2 := commutatorElement_eq_one_iff_commute.mp hcomm1
        have hval := congrArg Subtype.val hc2.eq
        simp only [Subgroup.coe_mul] at hval
        exact hval.symm
    -- **(3.19)** `|C_{V_G}(R₀)| = p`.  First `H ≠ ⊥` (else `⁅H,R⁆ = ⊥` has `p`-length one), so
    -- `V = F(H) ≠ ⊥`, `p ∣ |V|`, `p ≠ r`, and `p ∤ |S₁|`.
    have hH_ne_bot : H ≠ ⊥ := by
      intro hHbot
      apply hcounter
      rw [hasPLengthOne]
      intro hdvd
      have h1 : Nat.card (↥(⁅H, R⁆ : Subgroup G) ⧸
          OddOrder.Isaacs.Ch03.oPiPrimePiCore ({p} : Set ℕ) ↥(⁅H, R⁆ : Subgroup G)) ∣
          Nat.card ↥(⁅H, R⁆ : Subgroup G) :=
        ⟨_, Subgroup.card_eq_card_quotient_mul_card_subgroup _⟩
      have h2 : Nat.card ↥(⁅H, R⁆ : Subgroup G) = 1 := by
        rw [h36, hHbot, Subgroup.card_bot]
      rw [h2, Nat.dvd_one] at h1
      rw [h1, Nat.dvd_one] at hdvd
      exact hp.ne_one hdvd
    have hV_ne_bot : V ≠ ⊥ := by
      have : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hH_ne_bot
      exact hVdef ▸ OddOrder.Isaacs.Ch01.fitting_ne_bot_of_isSolvable_nontrivial ↥H
    have ha0 : a ≠ 0 := by
      intro h0
      exact hV_ne_bot (Subgroup.eq_bot_of_card_eq _ (by rw [hVa, h0, pow_zero]))
    have hpr : p ≠ r := by
      intro hpr_eq
      have h1 : p ∣ Nat.card ↥H :=
        (show p ∣ Nat.card ↥V by rw [hVa]; exact dvd_pow_self p ha0).trans
          (Subgroup.card_subgroup_dvd_card V)
      have h2 : p ∣ Nat.card ↥R := by
        rw [hpr_eq, ← hr_card]
        exact Subgroup.card_dvd_of_le hR₀R
      exact hp.ne_one (Nat.Coprime.eq_one_of_dvd (hHall.coprime_dvd_left h1) h2)
    have hS₁card : Nat.card ↥S₁ = Nat.card ↥K * r := by
      rw [← hcompl₁.card_mul_card, hKG'card, hR₀'card]
    have hp_ndvd_S₁ : ¬ p ∣ Nat.card ↥S₁ := by
      rw [hS₁card]
      intro hdvd
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
      · exact hKp_ndvd h
      · exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr_prime).mp h)
    -- `V_G` is elementary abelian (transport along `↥V ≃* ↥V_G`).
    have hVGelem : OddOrder.GroupTheory.IsElementaryAbelian p ↥VG := by
      have e := Subgroup.equivMapOfInjective V H.subtype H.subtype_injective
      refine ⟨fun x y => ?_, fun x => ?_⟩
      · have h1 := congrArg e (hVelem.1 (e.symm x) (e.symm y))
        rwa [map_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply] at h1
      · have h1 := congrArg e (hVelem.2 (e.symm x))
        rwa [map_pow, map_one, e.apply_symm_apply] at h1
    -- Part 1: `C_{V_G}(R₀) ≠ ⊥`.  Otherwise Theorem 3.4, applied to the conjugation
    -- representation of `S₁ = K_G·R₀` on the `𝔽_p`-vector space `V_G`, makes `⁅R₀,K_G⁆` act
    -- trivially on `V_G`; by (3.18) it is then trivial, contradicting (3.17).
    have h319a : VG ⊓ Subgroup.centralizer (R₀ : Set G) ≠ ⊥ := by
      intro hCVbot
      have hVGcomm : IsMulCommutative ↥VG := ⟨⟨fun a b => hVGelem.1 a b⟩⟩
      have hpsmul : ∀ x : Additive ↥VG, (p : ℕ) • x = 0 := by
        intro x
        apply Additive.toMul.injective
        rw [toMul_nsmul, toMul_zero]
        exact hVGelem.2 x.toMul
      have hVGmod : Module (ZMod p) (Additive ↥VG) := AddCommGroup.zmodModule hpsmul
      have : Module.Finite (ZMod p) (Additive ↥VG) := Module.Finite.of_finite
      set ρ : Representation (ZMod p) ↥S₁ (Additive ↥VG) :=
        (OddOrder.BG.Ch1_Preliminary.mulAutToEnd ↥VG p).comp
          ((MulAut.conjNormal (G := G) (H := VG)).comp S₁.subtype) with hρdef
      have hρ_apply : ∀ (g : ↥S₁) (x : Additive ↥VG),
          ρ g x = Additive.ofMul (MulAut.conjNormal (H := VG) (g : G) (Additive.toMul x)) := by
        intro g x
        rfl
      have hodd_S₁ : Odd (Nat.card ↥S₁) := by
        obtain ⟨m, hm⟩ := Subgroup.card_subgroup_dvd_card S₁
        rw [hm, Nat.odd_mul] at hodd
        exact hodd.1
      have hchar : (Nat.card ↥S₁ : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact hp_ndvd_S₁
      have hHall34 : Nat.Coprime (Nat.card ↥(KG.subgroupOf S₁))
          (Nat.card ↥(R₀.subgroupOf S₁)) := by
        rw [hKG'card, hR₀'card]
        exact (hr_prime.coprime_iff_not_dvd.mpr hr_ndvd_K).symm
      have hCV : ∀ v : Additive ↥VG,
          (∀ rr : ↥(R₀.subgroupOf S₁), ρ ((rr : ↥S₁)) v = v) → v = 0 := by
        intro v hv
        have hmem : ((Additive.toMul v : ↥VG) : G)
            ∈ VG ⊓ Subgroup.centralizer (R₀ : Set G) := by
          refine Subgroup.mem_inf.mpr
            ⟨(Additive.toMul v).2, Subgroup.mem_centralizer_iff.mpr fun gr hgr => ?_⟩
          have h1 := hv ⟨⟨gr, hR₀_le_S₁ hgr⟩, Subgroup.mem_subgroupOf.mpr hgr⟩
          rw [hρ_apply] at h1
          have h2 := congrArg Additive.toMul h1
          rw [toMul_ofMul] at h2
          have h3 := congrArg Subtype.val h2
          rw [MulAut.conjNormal_apply] at h3
          exact mul_inv_eq_iff_eq_mul.mp h3
        rw [hCVbot, Subgroup.mem_bot] at hmem
        have hw : (Additive.toMul v : ↥VG) = 1 := Subtype.ext hmem
        rw [← ofMul_toMul v, hw, ofMul_one]
      have hthm34 := S03d.thm34 ρ (KG.subgroupOf S₁) (R₀.subgroupOf S₁)
        hcompl₁ hHall34 ⟨r, hr_prime, hR₀'card⟩ hodd_S₁ hchar hCV
      -- every element of `⁅R₀, K_G⁆` therefore centralizes `V_G`, hence dies by (3.18).
      have hcomm_bot : (⁅R₀, KG⁆ : Subgroup G) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hsub : (⁅R₀, KG⁆ : Subgroup G) ≤ S₁ := by
          rw [Subgroup.commutator_le]
          intro g₁ hg₁ g₂ hg₂
          have h1 : g₁ ∈ S₁ := hR₀_le_S₁ hg₁
          have h2 : g₂ ∈ S₁ := hKG_le_S₁ hg₂
          rw [commutatorElement_def]
          exact S₁.mul_mem (S₁.mul_mem (S₁.mul_mem h1 h2) (S₁.inv_mem h1)) (S₁.inv_mem h2)
        have hxS₁ : x ∈ S₁ := hsub hx
        have hmapeq : (⁅(R₀.subgroupOf S₁ : Subgroup ↥S₁), KG.subgroupOf S₁⁆
            : Subgroup ↥S₁).map S₁.subtype = ⁅R₀, KG⁆ := by
          rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
            Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hR₀_le_S₁,
            inf_eq_left.mpr hKG_le_S₁]
        have hx' : (⟨x, hxS₁⟩ : ↥S₁)
            ∈ (⁅(R₀.subgroupOf S₁ : Subgroup ↥S₁), KG.subgroupOf S₁⁆ : Subgroup ↥S₁) := by
          have hmem : x ∈ (⁅(R₀.subgroupOf S₁ : Subgroup ↥S₁), KG.subgroupOf S₁⁆
              : Subgroup ↥S₁).map S₁.subtype := hmapeq.symm ▸ hx
          obtain ⟨z, hz, hzx⟩ := hmem
          rwa [show z = ⟨x, hxS₁⟩ from Subtype.ext hzx] at hz
        have hρ1 : ρ ⟨x, hxS₁⟩ = 1 := hthm34 _ hx'
        have hxc : x ∈ Subgroup.centralizer (VG : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have hx1 := DFunLike.congr_fun hρ1 (Additive.ofMul (⟨y, hy⟩ : ↥VG))
          rw [hρ_apply, Module.End.one_apply] at hx1
          have hcoe := congrArg Subtype.val (Additive.ofMul.injective hx1)
          rw [MulAut.conjNormal_apply] at hcoe
          exact (mul_inv_eq_iff_eq_mul.mp hcoe).symm
        have hfin : x ∈ S₁ ⊓ Subgroup.centralizer (VG : Set G) := ⟨hxS₁, hxc⟩
        rwa [h318] at hfin
      apply h317
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hcomm_bot
    -- Part 2: `C_{V_G}(R₀)` is a nontrivial subgroup of exponent `p` inside the `Z`-group
    -- `H ⊓ C_G(R₀)`, hence has order exactly `p`.
    have hA_exp : ∀ x ∈ VG ⊓ Subgroup.centralizer (R₀ : Set G), x ^ p = (1 : G) := by
      intro x hx
      obtain ⟨hxV, _⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨w, hw, rfl⟩ := hxV
      have h1 : w ^ p = (1 : ↥H) := by
        have h2 := congrArg Subtype.val (hVelem.2 ⟨w, hw⟩)
        rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
      have h4 := congrArg Subtype.val h1
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h4
    have h319 : Nat.card ↥(VG ⊓ Subgroup.centralizer (R₀ : Set G)) = p :=
      card_eq_prime_of_le_isZGroup hZ
        (inf_le_inf_right _ (Subgroup.map_subtype_le V)) hp hA_exp h319a
    -- **(3.20)** `C_{P_G}(R₀) = ⊥`.  Otherwise pick `y` of order `p` in `P_G ⊓ C_G(R₀)`
    -- (Cauchy); `y` normalizes `A := C_{V_G}(R₀)` (it centralizes `R₀` and `V_G ⊴ G`), so
    -- `T := A·⟨y⟩` is a `p`-subgroup of the `Z`-group `H ⊓ C_G(R₀)`, hence cyclic; a cyclic
    -- group has at most `p` solutions of `t^p = 1`, so `y ∈ A ≤ V_G`; but `P_G ⊓ V_G = ⊥`.
    have hPV_inf : (P.map H.subtype : Subgroup G) ⊓ VG = ⊥ := by
      have h1 : P ⊓ V = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have h2 : x ∈ V ⊓ N := ⟨hx.2, hP_le_N hx.1⟩
        rwa [hVN_inf] at h2
      rw [← Subgroup.map_inf _ _ H.subtype H.subtype_injective, h1, Subgroup.map_bot]
    have h320 : (P.map H.subtype : Subgroup G) ⊓ Subgroup.centralizer (R₀ : Set G) = ⊥ := by
      by_contra hne
      -- a `p`-element `y` of order `p` in `W := P_G ⊓ C_G(R₀)` (Cauchy).
      set W : Subgroup G := (P.map H.subtype) ⊓ Subgroup.centralizer (R₀ : Set G) with hW
      have hWp : IsPGroup p ↥W :=
        (hPp.map H.subtype).to_le inf_le_left
      have hpdvdW : p ∣ Nat.card ↥W := by
        obtain ⟨m, hm⟩ := hWp.exists_card_eq
        rw [hm]
        refine dvd_pow_self p ?_
        intro h0
        exact hne (Subgroup.eq_bot_of_card_eq _ (by rw [hm, h0, pow_zero]))
      obtain ⟨y, hy_ord⟩ := exists_prime_orderOf_dvd_card' p hpdvdW
      have hy_ordG : orderOf ((y : G)) = p := by
        rw [← hy_ord]
        exact orderOf_injective W.subtype W.subtype_injective y
      have hyP : (y : G) ∈ P.map H.subtype := y.2.1
      have hyC : (y : G) ∈ Subgroup.centralizer (R₀ : Set G) := y.2.2
      -- conjugation by anything centralizing `R₀` preserves `C_G(R₀)`.
      have hCnorm : ∀ z ∈ Subgroup.centralizer (R₀ : Set G),
          ∀ c ∈ Subgroup.centralizer (R₀ : Set G),
          z * c * z⁻¹ ∈ Subgroup.centralizer (R₀ : Set G) := by
        intro z hz c hc
        rw [Subgroup.mem_centralizer_iff] at hz hc ⊢
        intro g hg
        have h1 := hz g hg
        have h2 := hc g hg
        have h3 : g * z⁻¹ = z⁻¹ * g := (Commute.inv_right (h1 : Commute g z) : Commute g z⁻¹)
        calc g * (z * c * z⁻¹)
            = (g * z) * c * z⁻¹ := by group
          _ = (z * g) * c * z⁻¹ := by rw [h1]
          _ = z * (g * c) * z⁻¹ := by group
          _ = z * (c * g) * z⁻¹ := by rw [h2]
          _ = z * c * (g * z⁻¹) := by group
          _ = z * c * (z⁻¹ * g) := by rw [h3]
          _ = (z * c * z⁻¹) * g := by group
      -- `↑y` normalizes `A := C_{V_G}(R₀)`.
      obtain ⟨A, hA⟩ : ∃ A : Subgroup G, A = VG ⊓ Subgroup.centralizer (R₀ : Set G) := ⟨_, rfl⟩
      have hy_normA : (y : G) ∈ Subgroup.normalizer (A : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        rw [hA]
        constructor
        · intro hx1
          obtain ⟨hxV, hxc⟩ := Subgroup.mem_inf.mp hx1
          exact Subgroup.mem_inf.mpr ⟨hVGnorm.conj_mem x hxV (y : G), hCnorm _ hyC x hxc⟩
        · intro hx1
          obtain ⟨hxV, hxc⟩ := Subgroup.mem_inf.mp hx1
          have h1 : (y : G)⁻¹ * ((y : G) * x * (y : G)⁻¹) * ((y : G)⁻¹)⁻¹ = x := by group
          refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
          · have h2 := hVGnorm.conj_mem _ hxV (y : G)⁻¹
            rwa [h1] at h2
          · have h2 := hCnorm _ (Subgroup.inv_mem _ hyC) _ hxc
            rwa [h1] at h2
      -- `T := A ⊔ ⟨y⟩` is a `p`-group inside the `Z`-group `H ⊓ C_G(R₀)`, hence cyclic.
      set Y : Subgroup G := Subgroup.zpowers (y : G) with hY
      set T : Subgroup G := A ⊔ Y with hT
      have hAT : A ≤ T := le_sup_left
      have hYT : Y ≤ T := le_sup_right
      have hyT : (y : G) ∈ T := hYT (Subgroup.mem_zpowers _)
      have hT_norm : T ≤ Subgroup.normalizer (A : Set G) :=
        sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hy_normA)
      have hA''norm : ((A.subgroupOf T) : Subgroup ↥T).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer hT_norm
      have hA''card : Nat.card ↥(A.subgroupOf T) = p :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAT).toEquiv).trans (by rw [hA]; exact h319)
      -- the product decomposition `T = A·Y` and the quotient `T/A` generated by `mk y`.
      have hTset : (T : Set G) = (A : Set G) * (Y : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left A Y
          (Subgroup.zpowers_le.mpr hy_normA)
      have hquot_gen : ∀ q : (↥T ⧸ (A.subgroupOf T : Subgroup ↥T)),
          q ∈ Subgroup.zpowers ((QuotientGroup.mk' (A.subgroupOf T)) ⟨(y : G), hyT⟩) := by
        intro q
        obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective _ q
        have htm : (t : G) ∈ (A : Set G) * (Y : Set G) := by
          rw [← hTset]
          exact t.2
        obtain ⟨av, hav, yv, hyv, heq⟩ := htm
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyv
        have ht_eq : t = (⟨av, hAT hav⟩ : ↥T) * (⟨(y : G), hyT⟩ : ↥T) ^ k := by
          apply Subtype.ext
          rw [Subgroup.coe_mul, Subgroup.coe_zpow]
          rw [← heq, hk]
        rw [ht_eq, map_mul, map_zpow]
        have hav1 : (QuotientGroup.mk' (A.subgroupOf T : Subgroup ↥T)) ⟨av, hAT hav⟩ = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact Subgroup.mem_subgroupOf.mpr hav
        rw [hav1, one_mul]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
      have hquot_card : Nat.card (↥T ⧸ (A.subgroupOf T : Subgroup ↥T)) ∣ p := by
        have htop : Subgroup.zpowers ((QuotientGroup.mk' (A.subgroupOf T : Subgroup ↥T))
            ⟨(y : G), hyT⟩) = ⊤ := by
          rw [eq_top_iff]
          exact fun q _ => hquot_gen q
        have h1 : Nat.card (↥T ⧸ (A.subgroupOf T : Subgroup ↥T))
            = orderOf ((QuotientGroup.mk' (A.subgroupOf T : Subgroup ↥T)) ⟨(y : G), hyT⟩) := by
          rw [← Nat.card_zpowers, htop]
          exact Nat.card_congr Subgroup.topEquiv.symm.toEquiv
        rw [h1, ← hy_ordG]
        have h2 : orderOf (⟨(y : G), hyT⟩ : ↥T) = orderOf (y : G) :=
          (orderOf_injective T.subtype T.subtype_injective ⟨(y : G), hyT⟩).symm
        rw [← h2]
        exact orderOf_map_dvd _ _
      have hTp : IsPGroup p ↥T := by
        have h1 : Nat.card ↥T ∣ p * p := by
          rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
            (A.subgroupOf T : Subgroup ↥T), hA''card]
          exact mul_dvd_mul hquot_card dvd_rfl
        have h1' : Nat.card ↥T ∣ p ^ 2 := by rwa [← pow_two] at h1
        rcases (Nat.dvd_prime_pow hp).mp h1' with ⟨k, _, hcard⟩
        exact IsPGroup.of_card hcard
      have hT_le_Z : T ≤ H ⊓ Subgroup.centralizer (R₀ : Set G) := by
        refine sup_le ?_ ?_
        · rw [hA]
          exact le_inf (inf_le_left.trans (Subgroup.map_subtype_le V)) inf_le_right
        rw [Subgroup.zpowers_le]
        exact ⟨Subgroup.map_subtype_le P hyP, hyC⟩
      -- `T` is cyclic (`p`-subgroup of a `Z`-group).
      have hTZ : _root_.IsZGroup ↥T := by
        have := isZGroup_iff_mathlib.mp hZ
        exact IsZGroup.of_injective (Subgroup.inclusion_injective hT_le_Z)
      have hTcyc : IsCyclic ↥T := by
        have h1 : IsPGroup p ↥(⊤ : Subgroup ↥T) :=
          hTp.of_injective (⊤ : Subgroup ↥T).subtype (⊤ : Subgroup ↥T).subtype_injective
        have := IsPGroup.isCyclic_of_isZGroup h1
        exact isCyclic_of_surjective _ (Subgroup.topEquiv (G := ↥T)).surjective
      -- the `p`-torsion of the cyclic `T` has at most `p` elements, and `A` already fills it;
      -- so `y ∈ A ≤ V_G`, contradicting `P_G ⊓ V_G = ⊥`.
      classical
      have := Fintype.ofFinite ↥T
      have hle : (Finset.univ.filter (fun a : ↥T => a ^ p = 1)).card ≤ p := by
        convert IsCyclic.card_pow_eq_one_le (α := ↥T) (n := p) hp.pos using 2
      have hsubset : Set.toFinset ((A.subgroupOf T : Subgroup ↥T) : Set ↥T)
          ⊆ Finset.univ.filter (fun a : ↥T => a ^ p = 1) := by
        intro t ht
        rw [Set.mem_toFinset] at ht
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hA_exp _ (hA ▸ Subgroup.mem_subgroupOf.mp ht)
      have hcard_eq : (Set.toFinset ((A.subgroupOf T : Subgroup ↥T) : Set ↥T)).card = p := by
        rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
        exact hA''card
      have hy_filter : (⟨(y : G), hyT⟩ : ↥T)
          ∈ Finset.univ.filter (fun a : ↥T => a ^ p = 1) := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one, ← hy_ordG]
        exact pow_orderOf_eq_one _
      have hyA : (y : G) ∈ A := by
        by_contra hnot
        have hnotfin : (⟨(y : G), hyT⟩ : ↥T)
            ∉ Set.toFinset ((A.subgroupOf T : Subgroup ↥T) : Set ↥T) := by
          rw [Set.mem_toFinset]
          intro hmem
          exact hnot (Subgroup.mem_subgroupOf.mp hmem)
        have hsub2 : insert (⟨(y : G), hyT⟩ : ↥T)
            (Set.toFinset ((A.subgroupOf T : Subgroup ↥T) : Set ↥T))
            ⊆ Finset.univ.filter (fun a : ↥T => a ^ p = 1) :=
          Finset.insert_subset hy_filter hsubset
        have hcard2 := Finset.card_le_card hsub2
        rw [Finset.card_insert_of_notMem hnotfin, hcard_eq] at hcard2
        omega
      have hybot : (y : G) ∈ (P.map H.subtype : Subgroup G) ⊓ VG := ⟨hyP, (hA ▸ hyA).1⟩
      rw [hPV_inf, Subgroup.mem_bot] at hybot
      rw [hybot, orderOf_one] at hy_ordG
      exact hp.one_lt.ne hy_ordG
    -- **(3.21)** `P = ⁅P, R₀⁆` (action-commutator form): the `R₀`-action on `P` has trivial
    -- fixed points by (3.20), so Prop 1.6(a) makes its action commutator all of `P`.
    have hP₀_inv : OddOrder.Isaacs.Ch03.IsAInvariant
        (φ.comp (Subgroup.inclusion hR₀R)) P :=
      fun a => hP_inv (Subgroup.inclusion hR₀R a)
    have h321 : OddOrder.Isaacs.Ch04.actionCommutator hP₀_inv.restrict = ⊤ := by
      have hCopP : Nat.Coprime (Nat.card ↥R₀) (Nat.card ↥P) :=
        (hHall.symm.coprime_dvd_left (Subgroup.card_dvd_of_le hR₀R)).coprime_dvd_right
          (Subgroup.card_subgroup_dvd_card P)
      have hsup := OddOrder.Isaacs.Ch04.fixedPoints_sup_actionCommutator_eq_top
        (φ := hP₀_inv.restrict) hCopP (Or.inr inferInstance)
      have hfix_bot : Subgroup.fixedPointsOfMulAut hP₀_inv.restrict = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rw [Subgroup.mem_fixedPointsOfMulAut] at hx
        have hmem : ((x : ↥H) : G) ∈ (P.map H.subtype : Subgroup G)
            ⊓ Subgroup.centralizer (R₀ : Set G) := by
          refine ⟨⟨(x : ↥H), x.2, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
          have h1 := hx ⟨g, hg⟩
          have h2 := congrArg Subtype.val h1
          rw [OddOrder.Isaacs.Ch03.IsAInvariant.restrict_apply_val] at h2
          have h3 := congrArg Subtype.val h2
          simp only [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype,
            MulAut.conjNormal_apply, Subgroup.coe_inclusion] at h3
          exact mul_inv_eq_iff_eq_mul.mp h3
        rw [h320, Subgroup.mem_bot] at hmem
        rw [Subgroup.mem_bot]
        exact Subtype.ext (Subtype.ext (by simpa using hmem))
      rw [hfix_bot, bot_sup_eq] at hsup
      exact hsup
    -- `G`-level form of (3.21): `⁅P_G, R₀⁆ = P_G` (push the action commutator through the two
    -- subtype levels `↥P → ↥H → G`).  Used at (3.22) (`P = [P,R₀] ≤ [VXP,R₀]`).
    have h321G : (⁅(P.map H.subtype : Subgroup G), R₀⁆ : Subgroup G) = P.map H.subtype := by
      apply le_antisymm
      · rw [Subgroup.commutator_le]
        intro g₁ hg₁ g₂ hg₂
        obtain ⟨ph, hph, rfl⟩ := hg₁
        have h2 : g₂ * (ph : G)⁻¹ * g₂⁻¹ ∈ (P.map H.subtype : Subgroup G) := by
          refine ⟨_, hP_inv.smul_mem ⟨g₂, hR₀R hg₂⟩ (P.inv_mem hph), ?_⟩
          simp only [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply,
            Subgroup.coe_inv]
        have heq : ⁅(ph : G), g₂⁆ = (ph : G) * (g₂ * (ph : G)⁻¹ * g₂⁻¹) := by
          rw [commutatorElement_def]
          group
        change ⁅(ph : G), g₂⁆ ∈ (P.map H.subtype : Subgroup G)
        rw [heq]
        exact Subgroup.mul_mem _ ⟨ph, hph, rfl⟩ h2
      · rintro _ ⟨pp, hpp, rfl⟩
        have hmem : (⟨pp, hpp⟩ : ↥P) ∈ OddOrder.Isaacs.Ch04.actionCommutator hP₀_inv.restrict := by
          rw [h321]
          trivial
        have key : ∀ x ∈ OddOrder.Isaacs.Ch04.actionCommutator hP₀_inv.restrict,
            ((x : ↥H) : G) ∈ (⁅(P.map H.subtype : Subgroup G), R₀⁆ : Subgroup G) := by
          intro x hx
          rw [OddOrder.Isaacs.Ch04.actionCommutator] at hx
          induction hx using Subgroup.closure_induction with
          | mem y hy =>
            obtain ⟨g, a, rfl⟩ := hy
            have h1 := congrArg Subtype.val
              (OddOrder.Isaacs.Ch03.IsAInvariant.restrict_apply_val hP₀_inv a g⁻¹)
            simp only [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype,
              MulAut.conjNormal_apply, Subgroup.coe_inclusion] at h1
            have hval : (((g * (hP₀_inv.restrict a) g⁻¹ : ↥P) : ↥H) : G)
                = ⁅((g : ↥H) : G), (a : G)⁆ := by
              rw [Subgroup.coe_mul, Subgroup.coe_mul, h1, commutatorElement_def]
              simp only [Subgroup.coe_inv]
              group
            rw [hval]
            exact Subgroup.commutator_mem_commutator ⟨(g : ↥H), g.2, rfl⟩ a.2
          | one => simp
          | mul y z hy hz ihy ihz =>
            rw [Subgroup.coe_mul, Subgroup.coe_mul]
            exact Subgroup.mul_mem _ ihy ihz
          | inv y hy ihy =>
            rw [Subgroup.coe_inv, Subgroup.coe_inv]
            exact Subgroup.inv_mem _ ihy
        exact key _ hmem
    exact ⟨h317, hr_ndvd_K, hVGnorm, h318, hV_ne_bot, hpr, hVGelem, h319, h321G⟩

end OddOrder.BG.Ch1.S03f


