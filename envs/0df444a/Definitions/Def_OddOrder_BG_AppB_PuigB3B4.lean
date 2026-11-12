-- Prove2me | Definitions.Def_OddOrder_BG_AppB_PuigB3B4
-- name    : OddOrder_BG_AppB_PuigB3B4
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:48:36.860192+00:00
-- url     : https://prove2.me/theorems/ec5801c0-9a1e-4d15-8df0-01116c068af5
-- title:
--   Bender–Glauberman Appendix B: Lemma B.3 and Theorem B.4 (Puig)
-- statement:
--   Formalizes Lemma B.3 (the Sylow/$p$-core tower for the $L$-operator) and Theorem B.4(b) (Puig: if $O_{p'}(G)=1$ then $Z(L(S))\trianglelefteq G$) of Bender–Glauberman, Appendix B (pp. 142–144). This is the self-contained substitute for BG Thm 6.2 (Glauberman's $Z(J)$-theorem). Part B.4(a) is treated elsewhere since it needs covariance under isomorphisms of different groups.
--
--   Main definitions: `zCenterLOdd` ($Z(L(H))$ realized as a subgroup of $G$) and `normalInf_isSylow` (for $Q\in\mathrm{Syl}_p(G)$ and $N\trianglelefteq G$, $Q\sqcap N$ is Sylow in $N$).
--
--   The bundle also proves 13 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppB_PuigB3B4.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppB_PuigB3B4.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppB_Puig
import Definitions.Def_OddOrder_BG_AppA_PStability
import Mathlib.GroupTheory.GroupAction.ConjAct

namespace OddOrder.BG.AppB

open OddOrder.Isaacs.Ch01 OddOrder.Isaacs.Ch03 OddOrder.BG.AppA

variable {G : Type*} [Group G]

/-- **BG Lemma B.3 帰納核** (mmd L4650-4668): `∀ n`,
`L_{2n}(S) ⊆ L_{2n}(T) ⊆ L_{2n+1}(T) ⊆ L_{2n+1}(S)` (`T = O_p(G)`).
偶段は Thm A.5(2) (`P = L_{2n+1}(T)`, `X = L_{2n+2}(S)`) で `L_{2n+2}(S) ⊆ T` を得て従う. -/
private theorem b3_interleave [Finite G] {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hsolv : Group.IsSolvable G) (hodd : Odd (Nat.card G))
    (hOp' : oPiCore {q | q ≠ p} G = ⊥) (S : Sylow p G) :
    ∀ n, lNIn (S : Subgroup G) (2 * n) ≤ lNIn (opCore p G) (2 * n) ∧
      lNIn (opCore p G) (2 * n) ≤ lNIn (opCore p G) (2 * n + 1) ∧
      lNIn (opCore p G) (2 * n + 1) ≤ lNIn (S : Subgroup G) (2 * n + 1) := by
  have hT_le_S : opCore p G ≤ (S : Subgroup G) := opCore_le S
  have hT_pg : IsPGroup p ↥(opCore p G) := opCore_isPGroup p G
  intro n
  induction n with
  | zero =>
      have h1 : lNIn (S : Subgroup G) (2 * 0) = ⊥ := lNIn_zero _
      have h2 : lNIn (opCore p G) (2 * 0) = ⊥ := lNIn_zero _
      have h3 : lNIn (opCore p G) (2 * 0 + 1) = opCore p G := lNIn_one _
      have h4 : lNIn (S : Subgroup G) (2 * 0 + 1) = (S : Subgroup G) := lNIn_one _
      rw [h1, h2, h3, h4]
      exact ⟨le_refl _, bot_le, hT_le_S⟩
  | succ n ih =>
      obtain ⟨_, _, hTS⟩ := ih
      -- Step 1 (A.5): L_{2n+2}(S) ⊆ T
      have hP_char : (lNIn (opCore p G) (2 * n + 1)).Characteristic :=
        lNIn_characteristic_of_characteristic (opCore.characteristic p G) (2 * n + 1)
      have hP_normal : (lNIn (opCore p G) (2 * n + 1)).Normal := inferInstance
      have hP_pg : IsPGroup p ↥(lNIn (opCore p G) (2 * n + 1)) := hT_pg.to_le (lNIn_le_self _ _)
      have hX : lNIn (S : Subgroup G) (2 * n + 2) ≤ ⨆ A ∈ {A : Subgroup G | IsMulCommutative ↥A ∧
          IsPGroup p ↥A ∧ lNIn (opCore p G) (2 * n + 1) ≤ Subgroup.normalizer (A : Set G)}, A := by
        rw [show lNIn (S : Subgroup G) (2 * n + 2)
            = lRelIn (S : Subgroup G) (lNIn (S : Subgroup G) (2 * n + 1)) from lNIn_succ _ _]
        exact lRelIn_le_iSup_pgroup_normalized S.isPGroup' hTS
      have hST2 : lNIn (S : Subgroup G) (2 * n + 2) ≤ opCore p G :=
        thmA5_part2 hp_odd hsolv hodd hP_pg hX hOp' (centralizer_lNIn_inf_le hT_pg (by omega))
      -- (a) L_{2n+2}(S) ⊆ L_{2n+2}(T)
      have e1 : lNIn (S : Subgroup G) (2 * n + 2)
          = lRelIn (S : Subgroup G) (lNIn (S : Subgroup G) (2 * n + 1)) := lNIn_succ _ _
      have e2 : lNIn (opCore p G) (2 * n + 2)
          = lRelIn (opCore p G) (lNIn (opCore p G) (2 * n + 1)) := lNIn_succ _ _
      have ha : lNIn (S : Subgroup G) (2 * n + 2) ≤ lNIn (opCore p G) (2 * n + 2) := by
        rw [e1, e2]; exact lRelIn_le_lRelIn hTS hST2
      -- (b) L_{2n+2}(T) ⊆ L_{2n+3}(T)
      have hb : lNIn (opCore p G) (2 * n + 2) ≤ lNIn (opCore p G) (2 * n + 3) := by
        have h := lNIn_even_le_odd (opCore p G) (n + 1) (n + 1)
        rwa [show 2 * (n + 1) = 2 * n + 2 from by ring] at h
      -- (c) L_{2n+3}(T) ⊆ L_{2n+3}(S)
      have hc : lNIn (opCore p G) (2 * n + 3) ≤ lNIn (S : Subgroup G) (2 * n + 3) := by
        rw [show lNIn (opCore p G) (2 * n + 3)
              = lRelIn (opCore p G) (lNIn (opCore p G) (2 * n + 2)) from lNIn_succ _ _,
          show lNIn (S : Subgroup G) (2 * n + 3)
              = lRelIn (S : Subgroup G) (lNIn (S : Subgroup G) (2 * n + 2)) from lNIn_succ _ _]
        exact (lRelIn_anti_right ha).trans (lRelIn_mono_left hT_le_S _)
      refine ⟨?_, ?_, ?_⟩
      · rw [show 2 * (n + 1) = 2 * n + 2 from by ring]; exact ha
      · rw [show 2 * (n + 1) = 2 * n + 2 from by ring]; exact hb
      · rw [show 2 * (n + 1) + 1 = 2 * n + 3 from by ring]; exact hc

/-- **BG Lemma B.3** (mmd L4646): `p` odd, `G` solvable of odd order, `O_{p'}(G)=1`,
`S ∈ Syl_p(G)`, `T = O_p(G)` ⇒ `L_*(S) ⊆ L_*(T) ⊆ L(T) ⊆ L(S)`. -/
theorem b3_chain [Finite G] {p : ℕ} [Fact p.Prime] (hp_odd : p ≠ 2)
    (hsolv : Group.IsSolvable G) (hodd : Odd (Nat.card G))
    (hOp' : oPiCore {q | q ≠ p} G = ⊥) (S : Sylow p G) :
    lStarIn (S : Subgroup G) ≤ lStarIn (opCore p G) ∧
      lStarIn (opCore p G) ≤ lOddIn (opCore p G) ∧
      lOddIn (opCore p G) ≤ lOddIn (S : Subgroup G) := by
  obtain ⟨k1, hk1⟩ := exists_lStarIn_eq (S : Subgroup G)
  obtain ⟨k2, hk2⟩ := exists_lStarIn_eq (opCore p G)
  obtain ⟨k3, hk3⟩ := exists_lOddIn_eq (opCore p G)
  obtain ⟨k4, hk4⟩ := exists_lOddIn_eq (S : Subgroup G)
  set K := max (max k1 k2) (max k3 k4) with hK
  obtain ⟨hSS, _, hTS⟩ := b3_interleave hp_odd hsolv hodd hOp' S K
  refine ⟨?_, lStarIn_le_lOddIn (opCore p G), ?_⟩
  · rw [hk1 K (le_trans (le_max_left _ _) (le_max_left _ _)),
      hk2 K (le_trans (le_max_right _ _) (le_max_left _ _))]
    exact hSS
  · rw [hk3 K (le_trans (le_max_left _ _) (le_max_right _ _)),
      hk4 K (le_trans (le_max_right _ _) (le_max_right _ _))]
    exact hTS

/-- `Z(L(H))` を `G` の部分群として実現: `L(H)` の中心を subtype で `G` に落とす. -/
def zCenterLOdd (H : Subgroup G) : Subgroup G :=
  (Subgroup.center (lOddIn H : Subgroup G)).map (lOddIn H).subtype

/-- `Z(L(H)) ⊆ L(H)`. -/
theorem zCenterLOdd_le_lOddIn (H : Subgroup G) : zCenterLOdd H ≤ (lOddIn H : Subgroup G) :=
  Subgroup.map_subtype_le _

/-- **keystone bridge**: `Z(L(H)) = C_G(L(H)) ⊓ L(H)` (中心を `G`-中心化群の交わりで表す). -/
theorem zCenterLOdd_eq_centralizer_inf (H : Subgroup G) :
    zCenterLOdd H = Subgroup.centralizer (lOddIn H : Set G) ⊓ (lOddIn H : Subgroup G) := by
  refine le_antisymm (le_inf ?_ (zCenterLOdd_le_lOddIn H)) ?_
  · rintro g hg
    obtain ⟨z, hz_center, rfl⟩ := Subgroup.mem_map.mp hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hw := Subgroup.mem_center_iff.mp hz_center ⟨h, hh⟩
    have hco := congrArg (Subtype.val) hw
    push_cast at hco
    exact hco
  · intro g hg
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hg
    obtain ⟨hg_cent, hg_mem⟩ := hg
    refine ⟨⟨g, hg_mem⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    push_cast
    exact hg_cent (w : G) w.2

/-- `Z(L(H))` は可換 (中心ゆえ): `Z(L(H)) = C_G(L(H)) ⊓ L(H)` の任意 2 元は互いに中心化する. -/
theorem zCenterLOdd_isMulCommutative (H : Subgroup G) :
    IsMulCommutative ↥(zCenterLOdd H) := by
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have hle : zCenterLOdd H ≤ Subgroup.centralizer (lOddIn H : Set G) := by
    rw [zCenterLOdd_eq_centralizer_inf]; exact inf_le_left
  have ha_cent : (a : G) ∈ Subgroup.centralizer (lOddIn H : Set G) := hle a.2
  have hb_mem : (b : G) ∈ (lOddIn H : Subgroup G) := zCenterLOdd_le_lOddIn H b.2
  rw [Subgroup.mem_centralizer_iff] at ha_cent
  exact (ha_cent (b : G) hb_mem).symm

/-- **BG Theorem B.4(b) Step 2** (mmd L4707-4719): `Z(L(S)) ⊆ Z(L(T))` (`T = O_p(G)`).
`Z(L(S))` は `S` 内で `L(S) ⊇ L_*(S)` を中心化 ⇒ 相対 B.1(f) で `L_*(S)` に入り,
B.3 で `L_*(S) ⊆ L_*(T) ⊆ L(T)`; かつ `L(T) ⊆ L(S)` ゆえ `L(T)` も中心化. -/
theorem zCenterLOdd_sylow_le_zCenterLOdd_opCore [Finite G] {p : ℕ} [Fact p.Prime]
    (hp_odd : p ≠ 2) (hsolv : Group.IsSolvable G) (hodd : Odd (Nat.card G))
    (hOp' : oPiCore {q | q ≠ p} G = ⊥) (S : Sylow p G) :
    zCenterLOdd (S : Subgroup G) ≤ zCenterLOdd (opCore p G) := by
  obtain ⟨hSS, hST, hTS⟩ := b3_chain hp_odd hsolv hodd hOp' S
  have hZ_cent_LS : zCenterLOdd (S : Subgroup G)
      ≤ Subgroup.centralizer (lOddIn (S : Subgroup G) : Set G) := by
    rw [zCenterLOdd_eq_centralizer_inf]; exact inf_le_left
  have hZ_le_S : zCenterLOdd (S : Subgroup G) ≤ (S : Subgroup G) :=
    (zCenterLOdd_le_lOddIn (S : Subgroup G)).trans (lOddIn_le_self (S : Subgroup G))
  have hZ_cent_LstarS : zCenterLOdd (S : Subgroup G)
      ≤ Subgroup.centralizer (lStarIn (S : Subgroup G) : Set G) :=
    hZ_cent_LS.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (lStarIn_le_lOddIn _)))
  have hZ_le_LstarS : zCenterLOdd (S : Subgroup G) ≤ lStarIn (S : Subgroup G) :=
    (le_inf hZ_cent_LstarS hZ_le_S).trans (centralizer_lStarIn_inf_le S.isPGroup')
  have hZ_le_LT : zCenterLOdd (S : Subgroup G) ≤ lOddIn (opCore p G) :=
    (hZ_le_LstarS.trans hSS).trans hST
  have hZ_cent_LT : zCenterLOdd (S : Subgroup G)
      ≤ Subgroup.centralizer (lOddIn (opCore p G) : Set G) :=
    hZ_cent_LS.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hTS))
  rw [zCenterLOdd_eq_centralizer_inf (opCore p G)]
  exact le_inf hZ_cent_LT hZ_le_LT

/-- `L(H)` は `H` を固定する `G`-自己同型 `φ` で不変 (`lNIn_map_equiv` を `⨅` に分配). -/
theorem lOddIn_map_equiv (φ : G ≃* G) {H : Subgroup G} (hH : H.map φ.toMonoidHom = H) :
    (lOddIn H).map φ.toMonoidHom = lOddIn H := by
  change (⨅ n, lNIn H (2 * n + 1)).map φ.toMonoidHom = ⨅ n, lNIn H (2 * n + 1)
  rw [Subgroup.map_iInf φ.toMonoidHom φ.injective]
  exact iInf_congr fun n => lNIn_map_equiv φ hH (2 * n + 1)

/-- `K.map (conj g) = K ↔ g ∈ N_G(K)` (共役写像が `K` を固定 ⇔ `g` が `K` を正規化). -/
theorem map_conj_eq_iff_mem_normalizer {K : Subgroup G} {g : G} :
    K.map (MulAut.conj g).toMonoidHom = K ↔ g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  constructor
  · intro hmap h
    constructor
    · intro hh
      have hm : (MulAut.conj g).toMonoidHom h ∈ K.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hh
      rw [hmap] at hm
      simpa [MulAut.conj_apply] using hm
    · intro hh
      have hm : g * h * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom := by rw [hmap]; exact hh
      obtain ⟨y, hy, hxy⟩ := hm
      have hyh : y = h := mul_left_cancel (mul_right_cancel hxy)
      rwa [← hyh]
  · intro hnorm
    ext x
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hnorm y).mp hy
    · intro hx
      have he : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      refine ⟨g⁻¹ * x * g, ?_, he⟩
      rw [← SetLike.mem_coe, hnorm (g⁻¹ * x * g), he]
      exact hx

/-- **`L`-operator の normalizer 同変性**: `N_G(H) ≤ N_G(L(H))` (任意の `H`).
`g ∈ N_G(H)` ⇒ 共役 `conj g` が `H` を固定 ⇒ `L(H)` も固定 ⇒ `g ∈ N_G(L(H))`.
これが B.4(b) Step3 の `N_G(C∩S) ≤ N_G(L(C∩S))` を subgroupOf transport 無しで与える. -/
theorem normalizer_le_normalizer_lOddIn (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (lOddIn H : Set G) := by
  intro g hg
  exact map_conj_eq_iff_mem_normalizer.mp
    (lOddIn_map_equiv (MulAut.conj g) (map_conj_eq_iff_mem_normalizer.mpr hg))

/-- `K` の characteristic 部分群 `W` の `G`-像 `W.map K.subtype` は `N_G(K)` で正規化される.
(`OddOrder.Isaacs.Ch07` S7D1 の同名定理の port; Ch07 は AppB の import 閉包外ゆえ規約上 new generic
helper として複製する.) -/
theorem normalizer_le_normalizer_map_of_characteristic
    {H : Type*} [Group H] {K : Subgroup H} {W : Subgroup ↥K} [W.Characteristic] :
    Subgroup.normalizer (K : Set H) ≤ Subgroup.normalizer ((W.map K.subtype) : Set H) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  set cg : ↥K ≃* ↥K := K.normalizerMonoidHom (⟨g, hg⟩ : ↥(Subgroup.normalizer K)) with hcg_def
  have hWfix : W.map (cg : ↥K →* ↥K) = W :=
    (Subgroup.characteristic_iff_map_eq.mp ‹W.Characteristic›) cg
  have hcg_apply : ∀ w : ↥K, ((cg w : ↥K) : H) = g * (w : H) * g⁻¹ := fun w => rfl
  have hcg_symm_apply : ∀ w : ↥K, ((cg.symm w : ↥K) : H) = g⁻¹ * (w : H) * g := by
    intro w
    have h := hcg_apply (cg.symm w)
    rw [cg.apply_symm_apply] at h
    rw [h]; group
  intro y
  simp only [Subgroup.mem_map, Subgroup.coe_subtype]
  constructor
  · rintro ⟨w, hwW, rfl⟩
    refine ⟨cg w, ?_, ?_⟩
    · rw [← hWfix]; exact ⟨w, hwW, rfl⟩
    · rw [hcg_apply]
  · rintro ⟨w, hwW, hyeq⟩
    refine ⟨cg.symm w, ?_, ?_⟩
    · rw [← hWfix] at hwW
      obtain ⟨w', hw'W, hw'eq⟩ := hwW
      have : cg.symm w = w' := by rw [← hw'eq]; exact cg.symm_apply_apply w'
      rw [this]; exact hw'W
    · rw [hcg_symm_apply, hyeq]; group

/-- **第2同型の指数版** (積公式): `N ⊴ G` で `[N : Q⊓N] = [Q⊔N : Q]`.
`Sylow ∩ normal` が `normal` 内で Sylow であることの index 義務に使う. -/
private theorem relIndex_inf_eq_relIndex_sup [Finite G] {Q N : Subgroup G} [N.Normal] :
    (Q ⊓ N).relIndex N = Q.relIndex (Q ⊔ N) := by
  have hpos : 0 < N.relIndex Q :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := N.subgroupOf Q))
  apply Nat.eq_of_mul_eq_mul_right hpos
  have e1 : (Q ⊓ N).relIndex N * N.relIndex (Q ⊔ N) = (Q ⊓ N).relIndex (Q ⊔ N) :=
    Subgroup.relIndex_mul_relIndex (Q ⊓ N) N (Q ⊔ N) inf_le_right le_sup_right
  have e2 : (Q ⊓ N).relIndex Q * Q.relIndex (Q ⊔ N) = (Q ⊓ N).relIndex (Q ⊔ N) :=
    Subgroup.relIndex_mul_relIndex (Q ⊓ N) Q (Q ⊔ N) inf_le_left le_sup_left
  rw [Subgroup.relIndex_sup_right] at e1
  rw [Subgroup.inf_relIndex_left] at e2
  rw [e1, ← e2]; ring

/-- `Q ∈ Syl_p(G)`, `N ⊴ G` ⇒ `Q ⊓ N` は `N` の Sylow `p`-部分群 (`(↑Q ⊓ N).subgroupOf N` で実現).
Step4 の Frattini argument 用. 先例 `Isaacs/Ch07/S7B2:955`. -/
noncomputable def normalInf_isSylow {p : ℕ} [Fact p.Prime] [Finite G]
    {N : Subgroup G} [N.Normal] (Q : Sylow p G) : Sylow p ↥N :=
  (show IsPGroup p (((Q : Subgroup G) ⊓ N).subgroupOf N) from Q.2.to_inf_left.comap_subtype).toSylow
    (by
      change ¬ p ∣ ((Q : Subgroup G) ⊓ N).relIndex N
      rw [relIndex_inf_eq_relIndex_sup]
      exact fun h => Q.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le le_sup_left)))

/-- `normalInf_isSylow Q` の台部分群は `(↑Q ⊓ N).subgroupOf N`. -/
theorem normalInf_isSylow_coe {p : ℕ} [Fact p.Prime] [Finite G]
    {N : Subgroup G} [N.Normal] (Q : Sylow p G) :
    ((normalInf_isSylow (N := N) Q : Sylow p ↥N) : Subgroup ↥N)
      = ((Q : Subgroup G) ⊓ N).subgroupOf N :=
  rfl

/-- **BG Theorem B.4(b)** (mmd L4689-4762, Puig 1976): `p` odd, `G` solvable of odd order,
`O_{p'}(G) = 1`, `S ∈ Syl_p(G)` ⇒ `Z(L(S)) ⊴ G`.

これは **BG Thm 6.2 (Glauberman `Z(J)`) の自己完結代替** (BG L4691). Isaacs FGT が `Z(J)`
定理を省くため, no-Gorenstein 方針下では Thm 6.2 一般形への唯一の自己完結ルート.

証明 (mmd 4-Step): `T = O_p(G)`, `Y = Z(L(T))`.
* **Step 2** = `zCenterLOdd_sylow_le_zCenterLOdd_opCore`: `Z(L(S)) ⊆ Y`.
* **Step 3** (inline): `C` を `C/C_G(Y) = O_p(G/C_G(Y))` で取ると, `Y ⊆ L_*(S)` (B.1(e)),
  `L(S) → L` (A.5) で `L(S) ⊆ C`, よって `L(C∩S) = L(S)` (相対 B.2), 共役同変で
  `N_G(C∩S) ⊆ N_G(L(S))`.
* **Step 4** (inline): Frattini (`C∩S ∈ Syl_p(C)`) + 吸収 `C = C_G(Y)(C∩S)` で
  `C_G(Y) ⊔ N_G(C∩S) = ⊤`.
* **FINAL**: `⊤ = C_G(Y) ⊔ N_G(C∩S) ≤ N_G(Z(L(S)))` (左枝 `Z ⊆ Y`, 右枝 Step3 + center 同変). -/
theorem zCenter_lOdd_normal_of_oPiCore_eq_bot [Finite G] {p : ℕ} [Fact p.Prime]
    (hp_odd : p ≠ 2) (hsolv : Group.IsSolvable G) (hodd : Odd (Nat.card G))
    (hOp' : oPiCore {q | q ≠ p} G = ⊥) (S : Sylow p G) :
    (zCenterLOdd (S : Subgroup G)).Normal := by
  -- Step 2: Z(L(S)) ⊆ Y = Z(L(T))
  have hZ_le_Y : zCenterLOdd (S : Subgroup G) ≤ zCenterLOdd (opCore p G) :=
    zCenterLOdd_sylow_le_zCenterLOdd_opCore hp_odd hsolv hodd hOp' S
  -- Y = Z(L(T)) は characteristic-of-characteristic ルートで正規
  have hLT_char : (lOddIn (opCore p G)).Characteristic :=
    lOddIn_characteristic_of_characteristic (opCore.characteristic p G)
  have hLT_normal : (lOddIn (opCore p G)).Normal := inferInstance
  have hY_normal : (zCenterLOdd (opCore p G)).Normal := by
    unfold zCenterLOdd; infer_instance
  set Y := zCenterLOdd (opCore p G) with hY_def
  -- C₀ = C_G(Y) は正規 (`centralizer` 頭で保持, set しない — A.5 出力の quotient instance 用)
  have hC₀_normal : (Subgroup.centralizer (Y : Set G)).Normal := inferInstance
  have hC_normal :
      ((opCore p (G ⧸ Subgroup.centralizer (Y : Set G))).comap
        (QuotientGroup.mk' (Subgroup.centralizer (Y : Set G)))).Normal := inferInstance
  set C := (opCore p (G ⧸ Subgroup.centralizer (Y : Set G))).comap
    (QuotientGroup.mk' (Subgroup.centralizer (Y : Set G))) with hC_def
  set CapS := C ⊓ (S : Subgroup G) with hCapS_def
  -- === Step 3 の素材 ===
  have hY_le_T : Y ≤ opCore p G :=
    (zCenterLOdd_le_lOddIn (opCore p G)).trans (lOddIn_le_self (opCore p G))
  have hY_le_S : Y ≤ (S : Subgroup G) := hY_le_T.trans (opCore_le S)
  have hY_pg : IsPGroup p ↥Y := (opCore_isPGroup p G).to_le hY_le_T
  have hY_comm : IsMulCommutative ↥Y := zCenterLOdd_isMulCommutative (opCore p G)
  -- Y ⊆ L_*(S): Y abelian, Y ⊴ S ⟹ B.1(e)
  have hS_norm_Y : (S : Subgroup G) ≤ Subgroup.normalizer (Y : Set G) :=
    le_top.trans_eq (Subgroup.normalizer_eq_top_iff.mpr hY_normal).symm
  have hY_le_LstarS : Y ≤ lStarIn (S : Subgroup G) := by
    obtain ⟨k, hk⟩ := exists_lStarIn_eq (S : Subgroup G)
    have hpos : 0 < 2 * max k 1 := by have := le_max_right k 1; omega
    rw [hk (max k 1) (le_max_left _ _)]
    exact abelian_le_lNIn hY_comm hY_le_S hS_norm_Y hpos
  -- hX: L(S) ≤ ⨆ (Y-正規化 abelian p-群)
  have hX : lOddIn (S : Subgroup G) ≤ ⨆ A ∈ {A : Subgroup G | IsMulCommutative ↥A ∧
      IsPGroup p ↥A ∧ Y ≤ Subgroup.normalizer (A : Set G)}, A := by
    rw [← lRelIn_lStarIn (S : Subgroup G)]
    exact lRelIn_le_iSup_pgroup_normalized S.isPGroup' hY_le_LstarS
  -- A.5(1): L(S)·C₀/C₀ ⊆ O_p(G/C₀) = C/C₀, ゆえ L(S) ⊆ C
  have hmap := thmA5_part1 hp_odd hsolv hodd (P := Y) hY_pg hX
  have hL_le_C : lOddIn (S : Subgroup G) ≤ C := Subgroup.map_le_iff_le_comap.mp hmap
  -- 相対 B.2: L(C∩S) = L(S)
  have hLeq : lOddIn CapS = lOddIn (S : Subgroup G) :=
    lOddIn_eq_of_lOddIn_le_relative (H := CapS) (H₀ := (S : Subgroup G))
      (by rw [hCapS_def]; exact inf_le_right)
      (by rw [hCapS_def]; exact le_inf hL_le_C (lOddIn_le_self _))
  -- Step 3 結論: N_G(C∩S) ⊆ N_G(L(S))
  have hN : Subgroup.normalizer (CapS : Set G)
      ≤ Subgroup.normalizer (lOddIn (S : Subgroup G) : Set G) := by
    have h := normalizer_le_normalizer_lOddIn CapS
    rwa [hLeq] at h
  -- === Step 4: Frattini + 吸収 ⟹ C₀ ⊔ N_G(C∩S) = ⊤ ===
  have : Finite (Sylow p ↥C) := inferInstance
  have hQcs_map : ((normalInf_isSylow (N := C) S : Sylow p ↥C) : Subgroup ↥C).map C.subtype
      = CapS := by
    rw [normalInf_isSylow_coe, Subgroup.subgroupOf_map_subtype, hCapS_def, inf_assoc, inf_idem,
      inf_comm]
  have hFr : Subgroup.normalizer (CapS : Set G) ⊔ C = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top (normalInf_isSylow (N := C) S)
    rwa [hQcs_map] at h
  -- 吸収: C ⊆ C₀(C∩S)
  have hC_absorb : C ≤ Subgroup.centralizer (Y : Set G) ⊔ CapS := by
    intro c hc
    rw [hC_def, Subgroup.mem_comap] at hc
    have hle : opCore p (G ⧸ Subgroup.centralizer (Y : Set G))
        ≤ (S : Subgroup G).map (QuotientGroup.mk' (Subgroup.centralizer (Y : Set G))) := by
      have h := opCore_le (S.mapSurjective (QuotientGroup.mk'_surjective
        (Subgroup.centralizer (Y : Set G))))
      rwa [Sylow.coe_mapSurjective] at h
    obtain ⟨s, hsS, hs_eq⟩ := Subgroup.mem_map.mp (hle hc)
    have hsC : s ∈ C := by rw [hC_def, Subgroup.mem_comap, hs_eq]; exact hc
    have hcs : c * s⁻¹ ∈ Subgroup.centralizer (Y : Set G) := by
      have hker : (QuotientGroup.mk' (Subgroup.centralizer (Y : Set G))) (c * s⁻¹) = 1 := by
        rw [map_mul, map_inv, hs_eq, mul_inv_cancel]
      rwa [← QuotientGroup.ker_mk' (Subgroup.centralizer (Y : Set G)), MonoidHom.mem_ker]
    have hsCapS : s ∈ CapS := by rw [hCapS_def, Subgroup.mem_inf]; exact ⟨hsC, hsS⟩
    have hceq : c = (c * s⁻¹) * s := by group
    rw [hceq]; exact Subgroup.mul_mem_sup hcs hsCapS
  have hCabs : C ≤ Subgroup.centralizer (Y : Set G) ⊔ Subgroup.normalizer (CapS : Set G) :=
    hC_absorb.trans (sup_le_sup_left Subgroup.le_normalizer _)
  have hTop : Subgroup.centralizer (Y : Set G) ⊔ Subgroup.normalizer (CapS : Set G) = ⊤ := by
    rw [eq_top_iff, ← hFr]; exact sup_le le_sup_right hCabs
  -- === FINAL: ⊤ = C₀ ⊔ N_G(C∩S) ≤ N_G(Z) ⟹ Z ⊴ G ===
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hTop]
  refine sup_le ?_ ?_
  · -- 左枝: C_G(Y) ≤ C_G(Z) ≤ N_G(Z)  (Z ⊆ Y)
    exact (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZ_le_Y)).trans
      (Subgroup.centralizer_le_normalizer _)
  · -- 右枝: N_G(C∩S) ⊆ N_G(L(S)) ⊆ N_G(Z)
    exact hN.trans (normalizer_le_normalizer_map_of_characteristic
      (K := lOddIn (S : Subgroup G)) (W := Subgroup.center _))

end OddOrder.BG.AppB


