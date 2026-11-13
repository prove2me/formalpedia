-- Prove2me | Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S08_SCN3Map
-- name    : OddOrder_BG_Ch2_Uniqueness_S08_SCN3Map
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:24:34.807952+00:00
-- url     : https://prove2.me/theorems/a7c8a8e2-1911-4b95-97db-592947bae80f
-- title:
--   BG §8: $\mathrm{SCN}_3$ and the Fitting subgroup of a maximal subgroup (`scn3_map` layer)
-- statement:
--   The `scn3_map` comparison lemmas of Bender–Glauberman §8: $A\in\mathrm{SCN}_3(P)$ mapped into $G$ against $F(M)$, Sylow normalizer transport, and the $O_{\pi'}(C(A))$-vanishing facts, for the case where $F(M)$ is a $p$-group.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 11 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch2_Uniqueness/S08_SCN3Map.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch2_Uniqueness/S08_SCN3Map.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S08_SCNFitting

namespace OddOrder.BG.Ch2.S08

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- BG 8.1(b), fourth p-group bridge: Theorem 6.1 puts every `SCN₃(P)` subgroup in
`O_{p',p}(M)`, hence in `F(M)` when `F(M)` is a `p`-group. -/
theorem scn3_map_le_fittingInG_of_fittingInG_isPGroup [Finite G]
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) :
    A.map M.subtype ≤ fittingInG M := by
  have hp_dvd_G : p ∣ Nat.card G :=
    (Nat.mem_primeFactors.mp hp).2.1.trans (Subgroup.card_subgroup_dvd_card (fittingInG M))
  have hp_odd_prop : Odd p := hG.odd.of_dvd_nat hp_dvd_G
  have hp_odd : p ≠ 2 := by
    rintro rfl
    rw [Nat.odd_iff] at hp_odd_prop
    omega
  have hsolvM : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hoddM : Odd (Nat.card ↥M) :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hAcomm : IsMulCommutative A :=
    IsMulCommutative.of_setLike_mul_comm fun a ha b hb =>
      congrArg Subtype.val (isMulCommutative_iff_of_setLike.mp hA.1.isMulCommutative
        (⟨a, hAP ha⟩ : ↥(P : Subgroup ↥M)) (Subgroup.mem_subgroupOf.mpr ha)
        ⟨b, hAP hb⟩ (Subgroup.mem_subgroupOf.mpr hb))
  have hA_norm : (P : Subgroup ↥M) ≤ Subgroup.normalizer (A : Set ↥M) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAP).mp hA.1.isNormal
  have hA_le_OPP : A ≤ Ch03.oPiPrimePiCore ({p} : Set ℕ) ↥M :=
    OddOrder.BG.AppA.thmA4b hp_odd hsolvM hoddM P hAP hA_norm
  exact (Subgroup.map_mono hA_le_OPP).trans
    (oPiPrimePiCore_singleton_map_le_fittingInG_of_fittingInG_isPGroup (M := M) hp hFp)

/-- If a nontrivial subgroup `K ≤ S.map subtype` has normalizer exactly controlled by a
maximal subgroup `M`, then the image of the Sylow subgroup `S` of `M` is a full Sylow
subgroup of the ambient minimal simple group. -/
theorem sylow_map_mem_range_of_normalizer_le_normalizer [Finite G]
    (hG : IsMinimalSimpleOdd G) {M K : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} [Fact p.Prime] (S : Sylow p ↥M)
    (hK_ne_bot : K ≠ ⊥) (hK_le_SH : K ≤ (S : Subgroup ↥M).map M.subtype)
    (hM_norm_K : M ≤ Subgroup.normalizer (K : Set G))
    (hN_SH_le_NK : Subgroup.normalizer (((S : Subgroup ↥M).map M.subtype : Subgroup G) : Set G) ≤
      Subgroup.normalizer (K : Set G)) :
    ∃ Q : Sylow p G, (Q : Subgroup G) = (S : Subgroup ↥M).map M.subtype := by
  classical
  have : IsSimpleGroup G := hG.simple
  set SH : Subgroup G := (S : Subgroup ↥M).map M.subtype with hSH_def
  have hSH_p : IsPGroup p SH := S.isPGroup'.map M.subtype
  obtain ⟨PH, hSH_le_PH⟩ := IsPGroup.exists_le_sylow hSH_p
  have hK_le_M : K ≤ M := by
    exact hK_le_SH.trans (hSH_def ▸ Subgroup.map_subtype_le _)
  have hNK_eq_M : Subgroup.normalizer K = M :=
    OddOrder.Isaacs.Ch07.maximal_eq_normalizer_of_M_normalizes
      (mem_maximalSubgroups.mp hM) hK_ne_bot hK_le_M hM_norm_K
  have hPH_subOf_p : IsPGroup p ((PH : Subgroup G).subgroupOf M) :=
    PH.isPGroup'.comap_subtype
  have hS_le_PH_subOf : (S : Subgroup ↥M) ≤ (PH : Subgroup G).subgroupOf M := by
    intro s hs
    have : M.subtype s ∈ SH := ⟨s, hs, rfl⟩
    exact hSH_le_PH this
  have hS_eq : (PH : Subgroup G).subgroupOf M = (S : Subgroup ↥M) :=
    S.is_maximal' hPH_subOf_p hS_le_PH_subOf
  suffices hSH_eq : SH = (PH : Subgroup G) by
    exact ⟨PH, hSH_eq.symm.trans hSH_def⟩
  refine le_antisymm hSH_le_PH ?_
  by_contra hPH_not_le
  have hSH_lt_PH : SH < (PH : Subgroup G) := lt_of_le_of_ne hSH_le_PH (by
    intro h
    exact hPH_not_le (le_of_eq h.symm))
  have : Group.IsNilpotent ↥(PH : Subgroup G) := PH.isPGroup'.isNilpotent
  have hNC : NormalizerCondition ↥(PH : Subgroup G) :=
    Group.normalizerCondition_of_isNilpotent (G := ↥(PH : Subgroup G))
  have hSH_subOf_lt_top : SH.subgroupOf (PH : Subgroup G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hPH_not_le htop
  have hlt := hNC (SH.subgroupOf (PH : Subgroup G)) hSH_subOf_lt_top
  obtain ⟨t, ht_norm, ht_not⟩ := SetLike.exists_of_lt hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hSH_le_PH, Subgroup.mem_subgroupOf] at ht_norm
  rw [Subgroup.mem_subgroupOf] at ht_not
  set tG : G := (t : G) with htG_def
  have htG_norm_K : tG ∈ Subgroup.normalizer (K : Set G) := hN_SH_le_NK ht_norm
  have htG_in_M : tG ∈ M := hNK_eq_M ▸ htG_norm_K
  have htG_in_PH : tG ∈ (PH : Subgroup G) := t.2
  have htM_in_S : (⟨tG, htG_in_M⟩ : ↥M) ∈ (S : Subgroup ↥M) := by
    rw [← hS_eq, Subgroup.mem_subgroupOf]
    exact htG_in_PH
  have htG_in_SH : tG ∈ SH := ⟨⟨tG, htG_in_M⟩, htM_in_S, rfl⟩
  exact ht_not htG_in_SH

/-- If `F(M)` is a `p`-group, it lies in every Sylow `p`-subgroup of `M`, viewed in
`G`. -/
theorem fittingInG_le_sylow_map_of_isPGroup [Finite G]
    {p : ℕ} [Fact p.Prime] {M : Subgroup G} (P : Sylow p ↥M)
    (hFp : IsPGroup p ↥(fittingInG M)) :
    fittingInG M ≤ (P : Subgroup ↥M).map M.subtype := by
  rw [fittingInG_eq_opiCoreInG_singleton_of_isPGroup (M := M) hFp, opiCoreInG]
  rw [OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := ↥M) p]
  exact Subgroup.map_mono (OddOrder.Isaacs.Ch01.opCore_le P)

/-- A subgroup of the image of a Sylow subgroup that centralizes the image of an
`SCN₃(P)` subgroup already lies in that image. -/
theorem le_scn3_map_of_le_sylow_map_of_le_centralizer_map
    {M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (P : Sylow p ↥M) {A : Subgroup ↥M} {B : Subgroup G}
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M)))
    (hB_le_P : B ≤ (P : Subgroup ↥M).map M.subtype)
    (hB_le_cent : B ≤ Subgroup.centralizer (A.map M.subtype : Set G)) :
    B ≤ A.map M.subtype := by
  intro b hb
  obtain ⟨y, hyP, hy_eq⟩ := Subgroup.mem_map.mp (hB_le_P hb)
  have hy_cent : (⟨y, hyP⟩ : ↥(P : Subgroup ↥M)) ∈
      Subgroup.centralizer ((A.subgroupOf (P : Subgroup ↥M)) : Set ↥(P : Subgroup ↥M)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzA : ((z : ↥(P : Subgroup ↥M)) : ↥M) ∈ A :=
      Subgroup.mem_subgroupOf.mp hz
    have hz_map : M.subtype ((z : ↥(P : Subgroup ↥M)) : ↥M) ∈ A.map M.subtype :=
      Subgroup.mem_map.mpr ⟨((z : ↥(P : Subgroup ↥M)) : ↥M), hzA, rfl⟩
    have hb_cent : b ∈ Subgroup.centralizer (A.map M.subtype : Set G) := hB_le_cent hb
    have hcommG :=
      Subgroup.mem_centralizer_iff.mp hb_cent
        (M.subtype ((z : ↥(P : Subgroup ↥M)) : ↥M)) hz_map
    have hcommM : ((z : ↥(P : Subgroup ↥M)) : ↥M) * y =
        y * ((z : ↥(P : Subgroup ↥M)) : ↥M) := by
      apply M.subtype_injective
      simpa [map_mul, hy_eq] using hcommG
    exact Subtype.ext hcommM
  have hyA_sub : (⟨y, hyP⟩ : ↥(P : Subgroup ↥M)) ∈
      A.subgroupOf (P : Subgroup ↥M) :=
    hA.1.centralizer_le hy_cent
  have hyA : y ∈ A := Subgroup.mem_subgroupOf.mp hyA_sub
  exact Subgroup.mem_map.mpr ⟨y, hyA, hy_eq⟩

/-- BG (8.10), first p-group form: when `F(M)` is a `p`-group, the nontrivial
`p`-core of `Z(F(M))` is absorbed by every local `SCN₃(P)` subgroup. -/
theorem centerFittingOpCoreInG_le_scn3_map_of_fittingInG_isPGroup [Finite G]
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) :
    centerFittingOpCoreInG p M ≤ A.map M.subtype := by
  apply le_scn3_map_of_le_sylow_map_of_le_centralizer_map P hA
  · exact ((centerFittingOpCoreInG_le_centerFittingInG p M).trans
        (centerFittingInG_le_fittingInG M)).trans
      (fittingInG_le_sylow_map_of_isPGroup P hFp)
  · intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hAF : A.map M.subtype ≤ fittingInG M :=
      scn3_map_le_fittingInG_of_fittingInG_isPGroup hG hM hp P hFp hAP hA
    have haF : a ∈ fittingInG M := hAF ha
    have hzZ : z ∈ centerFittingInG M :=
      centerFittingOpCoreInG_le_centerFittingInG p M hz
    exact (Subgroup.mem_centralizer_iff.mp
      (fittingInG_le_centralizer_centerFittingInG M haF) z hzZ).symm

/-- BG (8.10), centralizer form: when `F(M)` is a `p`-group, the ambient centralizer
of every local `SCN₃(P)` image is contained in `M`. -/
theorem centralizer_scn3_map_le_maximal_of_fittingInG_isPGroup [Finite G]
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) :
    Subgroup.centralizer (A.map M.subtype : Set G) ≤ M :=
  centralizer_le_maximal_of_centerFittingOpCoreInG_le hG hM
    (centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_fittingInG hp)
    (centerFittingOpCoreInG_le_scn3_map_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA)

/-- Inside `F(M)`, the centralizer of a local `SCN₃(P)` image is contained in that
image when `F(M)` is a `p`-group. -/
theorem centralizer_scn3_map_inf_fittingInG_le_scn3_map_of_fittingInG_isPGroup
    [Finite G] {M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) :
    Subgroup.centralizer (A.map M.subtype : Set G) ⊓ fittingInG M ≤ A.map M.subtype := by
  apply le_scn3_map_of_le_sylow_map_of_le_centralizer_map P hA
  · exact inf_le_right.trans (fittingInG_le_sylow_map_of_isPGroup P hFp)
  · exact inf_le_left

/-- If `x` centralizes the image of a local `SCN₃(P)` subgroup, that image lies in
`C_{F(M)}(<x>)`. -/
theorem scn3_map_le_centralizer_zpowers_inf_fittingInG_of_mem_centralizer
    {M : Subgroup G} {A : Subgroup ↥M} {x : G}
    (hAF : A.map M.subtype ≤ fittingInG M)
    (hxC : x ∈ Subgroup.centralizer (A.map M.subtype : Set G)) :
    A.map M.subtype ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M := by
  intro a haA
  refine ⟨?_, hAF haA⟩
  change a ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hcomm_eq : (a : G) * x = x * (a : G) :=
    Subgroup.mem_centralizer_iff.mp hxC (a : G) haA
  have hcomm : Commute (a : G) x := hcomm_eq
  exact (hcomm.symm.zpow_left n).eq

/-- BG (8.11), Prop 1.10 input for the p-group case: an element of `C_G(A)` satisfies
the self-centralizer condition on `C_{F(M)}(<x>)`. -/
theorem centralizer_zpowers_inf_fittingInG_self_of_mem_centralizer_scn3_map
    [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M)))
    {x : G} (hxC : x ∈ Subgroup.centralizer (A.map M.subtype : Set G)) :
    Subgroup.centralizer
        ((Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M) : Set ↥(fittingInG M))
      ≤ (Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M) := by
  let Amap : Subgroup G := A.map M.subtype
  let C : Subgroup G := Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M
  have hAF : Amap ≤ fittingInG M := by
    dsimp [Amap]
    exact scn3_map_le_fittingInG_of_fittingInG_isPGroup hG hM hp P hFp hAP hA
  have hCFA : Subgroup.centralizer (Amap : Set G) ⊓ fittingInG M ≤ Amap := by
    dsimp [Amap]
    exact centralizer_scn3_map_inf_fittingInG_le_scn3_map_of_fittingInG_isPGroup
      P hFp hA
  have hA_le_C : Amap ≤ C := by
    dsimp [Amap, C]
    exact scn3_map_le_centralizer_zpowers_inf_fittingInG_of_mem_centralizer hAF hxC
  intro y hy
  rw [Subgroup.mem_subgroupOf]
  have hyA : (y : G) ∈ Amap := by
    apply hCFA
    rw [Subgroup.mem_inf]
    refine ⟨?_, y.2⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    let aF : ↥(fittingInG M) := ⟨a, hAF ha⟩
    have haC : aF ∈ C.subgroupOf (fittingInG M) := by
      rw [Subgroup.mem_subgroupOf]
      exact hA_le_C ha
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hy aF haC)
  exact hA_le_C hyA

/-- BG (8.11), containment form: `O_{p'}(C_G(A))` lies in `F(M)` in the p-group
case. -/
theorem opiCoreInG_singleton_compl_centralizer_scn3_map_le_fittingInG_of_fittingInG_isPGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) :
    opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer (A.map M.subtype : Set G)) ≤
      fittingInG M := by
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  let C : Subgroup G := Subgroup.centralizer (A.map M.subtype : Set G)
  let K : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ C
  change K ≤ fittingInG M
  intro x hxK
  have hxC : x ∈ C := by
    dsimp [K] at hxK
    exact opiCoreInG_le ({p} : Set ℕ)ᶜ C hxK
  have hxM : x ∈ M :=
    centralizer_scn3_map_le_maximal_of_fittingInG_isPGroup hG hM hp P hFp hAP hA hxC
  have hxpi_singleton : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ (Subgroup.zpowers x) := by
    intro r hr
    have hz_le_K : Subgroup.zpowers x ≤ K := Subgroup.zpowers_le.mpr hxK
    have hrK : r ∈ (Nat.card ↥K).primeFactors :=
      Nat.primeFactors_mono (Subgroup.card_dvd_of_le hz_le_K) Nat.card_pos.ne' hr
    exact isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ C r hrK
  have hxpi : Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf (fittingInG M))ᶜ
      (Subgroup.zpowers x) := by
    have hπ : OddOrder.BG.Ch2.S07.primesOf (fittingInG M) = ({p} : Set ℕ) :=
      primesOf_fittingInG_eq_singleton_of_isPGroup hp hFp
    simpa [hπ] using hxpi_singleton
  exact mem_fittingInG_of_centralizer_self_zpowers hxM
    (coprime_card_zpowers_fittingInG_of_isPiSubgroup_primesOf_compl hxpi)
    (centralizer_zpowers_inf_fittingInG_self_of_mem_centralizer_scn3_map
      hG hM hp P hFp hAP hA hxC)

/-- BG (8.11): if `F(M)` is a `p`-group, then
`O_{p'}(C_G(A)) = 1` for every local `SCN₃(P)` image `A`. -/
theorem opiCoreInG_singleton_compl_centralizer_scn3_map_eq_bot_of_fittingInG_isPGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) :
    opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer (A.map M.subtype : Set G)) = ⊥ := by
  exact eq_bot_of_le_of_isPiSubgroup_of_isPiSubgroup_compl
    (opiCoreInG_singleton_compl_centralizer_scn3_map_le_fittingInG_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA)
    (isPiSubgroup_singleton_of_isPGroup hFp)
    (isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ
      (Subgroup.centralizer (A.map M.subtype : Set G)))

end OddOrder.BG.Ch2.S08


