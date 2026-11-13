-- Prove2me | Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S08_FittingOfMaximal
-- name    : OddOrder_BG_Ch2_Uniqueness_S08_FittingOfMaximal
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:27:32.528995+00:00
-- url     : https://prove2.me/theorems/ca5726c8-9af7-4425-a6c6-6104d6afc047
-- title:
--   BG §8: the Fitting subgroup of a maximal subgroup (tail, (8.13) counterexample measure)
-- statement:
--   The final part of the Bender–Glauberman §8 development on the Fitting subgroup of a maximal subgroup.
--
--   The main definition is `sylowInfCard`, the BG (8.13) counterexample measure: the order of a Sylow $p$-subgroup of $K\cap M$.
--
--   The bundle also proves 40 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch2_Uniqueness/S08_FittingOfMaximal.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch2_Uniqueness/S08_FittingOfMaximal.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S08_SCN3Map

namespace OddOrder.BG.Ch2.S08

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- In a nontrivial finite `p`-group, `Z(L(G))` is nontrivial. -/
theorem zCenterLOdd_top_ne_bot_of_isPGroup
    {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime] [Nontrivial X]
    (hX : IsPGroup p X) :
    OddOrder.BG.AppB.zCenterLOdd (⊤ : Subgroup X) ≠ ⊥ := by
  have hL_ne : OddOrder.BG.AppB.lOddIn (⊤ : Subgroup X) ≠ ⊥ :=
    OddOrder.BG.AppB.lOddIn_ne_bot hX
  have hL_pg : IsPGroup p (OddOrder.BG.AppB.lOddIn (⊤ : Subgroup X)) :=
    hX.to_subgroup _
  have hL_nontriv : Nontrivial ↥(OddOrder.BG.AppB.lOddIn (⊤ : Subgroup X)) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hL_ne
  have hcenter_ne :
      Subgroup.center (OddOrder.BG.AppB.lOddIn (⊤ : Subgroup X) : Subgroup X) ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot _).mp hL_pg.center_nontrivial
  intro hZ
  rw [OddOrder.BG.AppB.zCenterLOdd] at hZ
  exact hcenter_ne ((Subgroup.map_eq_bot_iff_of_injective
    (Subgroup.center (OddOrder.BG.AppB.lOddIn (⊤ : Subgroup X) : Subgroup X))
    (OddOrder.BG.AppB.lOddIn (⊤ : Subgroup X)).subtype_injective).mp hZ)

/-- If `H` is a nontrivial finite `p`-subgroup, then `Z(L(H))`, realized in the ambient
group, is nontrivial. -/
theorem zCenterLOdd_ne_bot_of_isPGroup [Finite G]
    {p : ℕ} [Fact p.Prime] {H : Subgroup G} (hHp : IsPGroup p H) (hH_ne : H ≠ ⊥) :
    OddOrder.BG.AppB.zCenterLOdd H ≠ ⊥ := by
  have hH_nontriv : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hH_ne
  have htop_ne : OddOrder.BG.AppB.zCenterLOdd (⊤ : Subgroup ↥H) ≠ ⊥ :=
    zCenterLOdd_top_ne_bot_of_isPGroup (X := ↥H) hHp
  have hinj : Function.Injective (H.subtype.comp (⊤ : Subgroup ↥H).subtype) := by
    intro x y hxy
    exact Subtype.ext (H.subtype_injective hxy)
  have hmap := OddOrder.BG.AppB.map_zCenterLOdd_of_injOn
    (G := ↥H) (G' := G) H.subtype (H := (⊤ : Subgroup ↥H)) hinj
  have htop_map : ((⊤ : Subgroup ↥H).map H.subtype) = H := by
    rw [← MonoidHom.range_eq_map, H.range_subtype]
  rw [htop_map] at hmap
  intro hbot
  have hmap_bot : (OddOrder.BG.AppB.zCenterLOdd (⊤ : Subgroup ↥H)).map H.subtype = ⊥ := by
    rw [hmap, hbot]
  exact htop_ne ((Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp hmap_bot)

/-- The normalizer of `H` normalizes the characteristic subgroup `Z(L(H))`. -/
theorem normalizer_le_normalizer_zCenterLOdd (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (OddOrder.BG.AppB.zCenterLOdd H : Set G) := by
  intro g hg
  have hHmap : H.map (MulAut.conj g).toMonoidHom = H :=
    OddOrder.BG.AppB.map_conj_eq_iff_mem_normalizer.mpr hg
  have hinj : Function.Injective ((MulAut.conj g).toMonoidHom.comp H.subtype) :=
    (MulAut.conj g).injective.comp H.subtype_injective
  have hmap : (OddOrder.BG.AppB.zCenterLOdd H).map (MulAut.conj g).toMonoidHom =
      OddOrder.BG.AppB.zCenterLOdd (H.map (MulAut.conj g).toMonoidHom) :=
    OddOrder.BG.AppB.map_zCenterLOdd_of_injOn
      (G := G) (G' := G) (MulAut.conj g).toMonoidHom (H := H) hinj
  have hZmap : (OddOrder.BG.AppB.zCenterLOdd H).map (MulAut.conj g).toMonoidHom =
      OddOrder.BG.AppB.zCenterLOdd H := by
    calc
      (OddOrder.BG.AppB.zCenterLOdd H).map (MulAut.conj g).toMonoidHom
          = OddOrder.BG.AppB.zCenterLOdd (H.map (MulAut.conj g).toMonoidHom) := hmap
      _ = OddOrder.BG.AppB.zCenterLOdd H := by rw [hHmap]
  exact OddOrder.BG.AppB.map_conj_eq_iff_mem_normalizer.mp hZmap

/-- The ambient image of `Z(L(K))` is normalized by the normalizer of the ambient image
of `K`. -/
theorem normalizer_map_le_normalizer_zCenterLOdd_map {H : Subgroup G} (K : Subgroup ↥H) :
    Subgroup.normalizer ((K.map H.subtype) : Set G) ≤
      Subgroup.normalizer (((OddOrder.BG.AppB.zCenterLOdd K).map H.subtype) : Set G) := by
  have hinj : Function.Injective (H.subtype.comp K.subtype) := by
    intro x y hxy
    exact K.subtype_injective (H.subtype_injective hxy)
  have hZmap :
      (OddOrder.BG.AppB.zCenterLOdd K).map H.subtype =
        OddOrder.BG.AppB.zCenterLOdd (K.map H.subtype) :=
    OddOrder.BG.AppB.map_zCenterLOdd_of_injOn
      (G := ↥H) (G' := G) H.subtype (H := K) hinj
  simpa [hZmap] using normalizer_le_normalizer_zCenterLOdd (K.map H.subtype)

/-- The ambient image of `Z(L(K))` lies in the ambient image of `K`. -/
theorem zCenterLOdd_map_le_map {H : Subgroup G} (K : Subgroup ↥H) :
    (OddOrder.BG.AppB.zCenterLOdd K).map H.subtype ≤ K.map H.subtype :=
  Subgroup.map_mono ((OddOrder.BG.AppB.zCenterLOdd_le_lOddIn K).trans
    (OddOrder.BG.AppB.lOddIn_le_self K))

/-- The ambient image of `Z(L(K))` depends only on the ambient image of `K`. -/
theorem zCenterLOdd_map_eq_of_map_eq {H₁ H₂ : Subgroup G}
    {K₁ : Subgroup ↥H₁} {K₂ : Subgroup ↥H₂}
    (hK : K₁.map H₁.subtype = K₂.map H₂.subtype) :
    (OddOrder.BG.AppB.zCenterLOdd K₁).map H₁.subtype =
      (OddOrder.BG.AppB.zCenterLOdd K₂).map H₂.subtype := by
  have hinj₁ : Function.Injective (H₁.subtype.comp K₁.subtype) := by
    intro x y hxy
    exact K₁.subtype_injective (H₁.subtype_injective hxy)
  have hinj₂ : Function.Injective (H₂.subtype.comp K₂.subtype) := by
    intro x y hxy
    exact K₂.subtype_injective (H₂.subtype_injective hxy)
  have hZ₁ :
      (OddOrder.BG.AppB.zCenterLOdd K₁).map H₁.subtype =
        OddOrder.BG.AppB.zCenterLOdd (K₁.map H₁.subtype) :=
    OddOrder.BG.AppB.map_zCenterLOdd_of_injOn
      (G := ↥H₁) (G' := G) H₁.subtype (H := K₁) hinj₁
  have hZ₂ :
      (OddOrder.BG.AppB.zCenterLOdd K₂).map H₂.subtype =
        OddOrder.BG.AppB.zCenterLOdd (K₂.map H₂.subtype) :=
    OddOrder.BG.AppB.map_zCenterLOdd_of_injOn
      (G := ↥H₂) (G' := G) H₂.subtype (H := K₂) hinj₂
  rw [hZ₁, hZ₂, hK]

/-- BG 8.1(b), fifth p-group bridge: Theorem 6.2 applied to `M` gives enough
normalizer control on `Z(L(P))` to make the image of `P` a Sylow `p`-subgroup of `G`. -/
theorem sylow_map_mem_range_of_fittingInG_isPGroup [Finite G]
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M)) :
    ∃ Q : Sylow p G, (Q : Subgroup G) = (P : Subgroup ↥M).map M.subtype := by
  classical
  set SH : Subgroup G := (P : Subgroup ↥M).map M.subtype with hSH_def
  set K : Subgroup G := OddOrder.BG.AppB.zCenterLOdd SH with hK_def
  have hF_ne_bot : fittingInG M ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card ↥(fittingInG M) = 1 := Subgroup.card_eq_one.mpr hbot
    rw [hcard, Nat.primeFactors_one] at hp
    exact Finset.notMem_empty p hp
  have hF_le_SH : fittingInG M ≤ SH := by
    rw [hSH_def]
    exact fittingInG_le_sylow_map_of_isPGroup P hFp
  have hSH_ne_bot : SH ≠ ⊥ := by
    intro hbot
    exact hF_ne_bot (le_bot_iff.mp (hF_le_SH.trans (le_of_eq hbot)))
  have hSH_p : IsPGroup p SH := by
    rw [hSH_def]
    exact P.isPGroup'.map M.subtype
  have hK_ne_bot : K ≠ ⊥ := by
    rw [hK_def]
    exact zCenterLOdd_ne_bot_of_isPGroup hSH_p hSH_ne_bot
  have hK_le_SH : K ≤ SH := by
    rw [hK_def]
    exact (OddOrder.BG.AppB.zCenterLOdd_le_lOddIn SH).trans
      (OddOrder.BG.AppB.lOddIn_le_self SH)
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
  have hmap_bot : (Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥M).map M.subtype = ⊥ := by
    simpa [opiCoreInG] using
      (opiCoreInG_singleton_compl_eq_bot_of_fittingInG_isPGroup (M := M) hp hFp)
  have hcore_bot_compl : Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥M = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective
      (Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥M) M.subtype_injective).mp hmap_bot
  -- `{q | q ≠ p}` is definitionally `({p} : Set ℕ)ᶜ`.
  have hcore_bot : Ch03.oPiCore {q | q ≠ p} ↥M = ⊥ := hcore_bot_compl
  have hZ_norm_M : (OddOrder.BG.AppB.zCenterLOdd (P : Subgroup ↥M)).Normal := by
    have h := OddOrder.BG.AppB.zCenter_lOdd_sup_oPiCore_normal hp_odd hsolvM hoddM P
    rwa [hcore_bot, sup_bot_eq] at h
  have hinjP : Function.Injective (M.subtype.comp (P : Subgroup ↥M).subtype) := by
    intro x y hxy
    exact Subtype.ext (M.subtype_injective hxy)
  have hZmap : (OddOrder.BG.AppB.zCenterLOdd (P : Subgroup ↥M)).map M.subtype = K := by
    have h := OddOrder.BG.AppB.map_zCenterLOdd_of_injOn
      (G := ↥M) (G' := G) M.subtype (H := (P : Subgroup ↥M)) hinjP
    rw [← hSH_def] at h
    simpa [hK_def] using h
  have hM_norm_K : M ≤ Subgroup.normalizer (K : Set G) := by
    have h1 : (Subgroup.normalizer (OddOrder.BG.AppB.zCenterLOdd (P : Subgroup ↥M) : Set ↥M)).map
        M.subtype ≤ Subgroup.normalizer (((OddOrder.BG.AppB.zCenterLOdd (P : Subgroup ↥M)).map
          M.subtype) : Set G) :=
      Subgroup.le_normalizer_map M.subtype
    rw [Subgroup.normalizer_eq_top_iff.mpr hZ_norm_M] at h1
    have htop_map : (⊤ : Subgroup ↥M).map M.subtype = M := by
      rw [← MonoidHom.range_eq_map, M.range_subtype]
    rw [htop_map, hZmap] at h1
    exact h1
  have hN_SH_le_NK : Subgroup.normalizer (SH : Set G) ≤ Subgroup.normalizer (K : Set G) := by
    rw [hK_def]
    exact normalizer_le_normalizer_zCenterLOdd SH
  exact sylow_map_mem_range_of_normalizer_le_normalizer hG hM P hK_ne_bot hK_le_SH
    hM_norm_K (by simpa [hSH_def] using hN_SH_le_NK)

/-- BG 8.1(b), SCN3 bridge: if the image of a Sylow subgroup of `M` is the Sylow
`Q` of `G`, then the image of every local `SCN₃(P)` subgroup is a global
`SCN₃(p)` subgroup in the sense of §7. -/
theorem scn3_map_mem_scn3Global_of_sylow_map [Finite G]
    {M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (P : Sylow p ↥M) {Q : Sylow p G}
    (hQ : (Q : Subgroup G) = (P : Subgroup ↥M).map M.subtype)
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) :
    A.map M.subtype ∈ OddOrder.BG.Ch2.S07.scn3Global p G := by
  classical
  let Pm : Subgroup ↥M := (P : Subgroup ↥M)
  let SH : Subgroup G := Pm.map M.subtype
  have hQSH : (Q : Subgroup G) = SH := by
    simpa [SH, Pm] using hQ
  let e0 : ↥Pm ≃* ↥SH :=
    Subgroup.equivMapOfInjective Pm M.subtype M.subtype_injective
  let eQ : ↥SH ≃* ↥(Q : Subgroup G) := (MulEquiv.subgroupCongr hQSH).symm
  let e : ↥Pm ≃* ↥(Q : Subgroup G) := e0.trans eQ
  have hAQ : A.map M.subtype ≤ (Q : Subgroup G) := by
    rw [hQ]
    exact Subgroup.map_mono hAP
  have htarget :
      (A.subgroupOf Pm).map e.toMonoidHom =
        (A.map M.subtype).subgroupOf (Q : Subgroup G) := by
    apply (Subgroup.map_subtype_inj (H := (Q : Subgroup G))).mp
    rw [Subgroup.map_subgroupOf_eq_of_le hAQ]
    rw [Subgroup.map_map]
    have hcomp : (Q : Subgroup G).subtype.comp e.toMonoidHom = M.subtype.comp Pm.subtype := by
      ext x
      simp [e, e0, eQ, SH, Pm]
    rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hAP]
  exact ⟨Q, hAQ, by
    rw [← htarget]
    exact hA.map_equiv e⟩

/-- BG (8.12), uniqueness part: for `q ≠ p`, `H_G^*(A;q)` has at most one member
for every local `SCN₃(P)` image `A` in the p-group case. -/
theorem hInvariantStar_scn3_map_eq_of_fittingInG_isPGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) (hq : q ≠ p)
    {Q₁ Q₂ : Subgroup G}
    (hQ₁ : Q₁ ∈ hInvariantStar ⊤ (A.map M.subtype) {q})
    (hQ₂ : Q₂ ∈ hInvariantStar ⊤ (A.map M.subtype) {q}) :
    Q₁ = Q₂ := by
  have hp_dvd_G : p ∣ Nat.card G :=
    (Nat.mem_primeFactors.mp hp).2.1.trans (Subgroup.card_subgroup_dvd_card (fittingInG M))
  obtain ⟨Q, hQ⟩ := sylow_map_mem_range_of_fittingInG_isPGroup hG hM hp P hFp
  have hAglobal : A.map M.subtype ∈ OddOrder.BG.Ch2.S07.scn3Global p G :=
    scn3_map_mem_scn3Global_of_sylow_map P hQ hAP hA
  have hKbot :
      opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer (A.map M.subtype : Set G)) = ⊥ :=
    opiCoreInG_singleton_compl_centralizer_scn3_map_eq_bot_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA
  exact OddOrder.BG.Ch2.S07.hInvariantStar_eq_of_conjTransitiveOn_bot hKbot
    (OddOrder.BG.Ch2.S07.thompsonTransitivity hG hp_dvd_G hAglobal hq) hQ₁ hQ₂

/-- A local `SCN₃(P)` subgroup is normalized by the image of `P` in the ambient group. -/
theorem sylow_map_le_normalizer_scn3_map
    {M : Subgroup G} {p : ℕ} [Fact p.Prime] (P : Sylow p ↥M)
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) :
    (P : Subgroup ↥M).map M.subtype ≤
      Subgroup.normalizer (A.map M.subtype : Set G) := by
  have hA_norm : (P : Subgroup ↥M) ≤ Subgroup.normalizer (A : Set ↥M) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAP).mp hA.1.isNormal
  exact (Subgroup.map_mono hA_norm).trans (Subgroup.le_normalizer_map M.subtype)

/-- BG (8.12): in the p-group case, `F(M)` normalizes every local `SCN₃(P)` image. -/
theorem fittingInG_le_normalizer_scn3_map_of_fittingInG_isPGroup
    [Finite G] {M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) :
    fittingInG M ≤ Subgroup.normalizer (A.map M.subtype : Set G) :=
  (fittingInG_le_sylow_map_of_isPGroup P hFp).trans
    (sylow_map_le_normalizer_scn3_map P hAP hA)

/-- BG (8.12): the uniqueness of `H_G^*(A;q)` makes `N_G(A)` normalize its member. -/
theorem normalizer_scn3_map_le_normalizer_hInvariantStar_of_fittingInG_isPGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) (hq : q ≠ p)
    {Q : Subgroup G} (hQ : Q ∈ hInvariantStar ⊤ (A.map M.subtype) {q}) :
    Subgroup.normalizer (A.map M.subtype : Set G) ≤ Subgroup.normalizer (Q : Set G) := by
  intro x hxA
  have hxA_eq : MulAut.conj x • (A.map M.subtype) = A.map M.subtype :=
    conj_smul_eq_self_of_mem_normalizer hxA
  have hQconj : MulAut.conj x • Q ∈ hInvariantStar ⊤ (A.map M.subtype) {q} :=
    conj_smul_mem_hInvariantStar_top_of_normalizer hQ hxA_eq
  have hconj_eq : MulAut.conj x • Q = Q :=
    hInvariantStar_scn3_map_eq_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA hq hQconj hQ
  exact mem_normalizer_of_conj_smul_eq_self hconj_eq

/-- BG (8.12): the unique member of `H_G^*(A;q)` is also maximal for `F(M)` invariance. -/
theorem hInvariantStar_scn3_map_mem_hInvariantStar_fittingInG_of_fittingInG_isPGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) (hq : q ≠ p)
    {Q : Subgroup G} (hQ : Q ∈ hInvariantStar ⊤ (A.map M.subtype) {q}) :
    Q ∈ hInvariantStar ⊤ (fittingInG M) {q} := by
  have hF_norm_A : fittingInG M ≤ Subgroup.normalizer (A.map M.subtype : Set G) :=
    fittingInG_le_normalizer_scn3_map_of_fittingInG_isPGroup P hFp hAP hA
  have hF_norm_Q : fittingInG M ≤ Subgroup.normalizer (Q : Set G) :=
    hF_norm_A.trans
      (normalizer_scn3_map_le_normalizer_hInvariantStar_of_fittingInG_isPGroup
        hG hM hp P hFp hAP hA hq hQ)
  refine ⟨⟨le_top, hF_norm_Q, hInvariantStar_isPiSubgroup hQ⟩, ?_⟩
  intro R hR hQR
  have hA_le_F : A.map M.subtype ≤ fittingInG M :=
    scn3_map_le_fittingInG_of_fittingInG_isPGroup hG hM hp P hFp hAP hA
  have hR_A : R ∈ hInvariant ⊤ (A.map M.subtype) {q} := by
    rw [mem_hInvariant] at hR ⊢
    exact ⟨le_top, hA_le_F.trans hR.2.1, hR.2.2⟩
  exact hQ.2 R hR_A hQR

/-- BG (8.12): `H_G^*(F(M);q)` has the same unique member as `H_G^*(A;q)`. -/
theorem hInvariantStar_fittingInG_eq_of_scn3_map_of_fittingInG_isPGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) (hq : q ≠ p)
    {Q R : Subgroup G} (hQ : Q ∈ hInvariantStar ⊤ (A.map M.subtype) {q})
    (hR : R ∈ hInvariantStar ⊤ (fittingInG M) {q}) :
    R = Q := by
  have hA_le_F : A.map M.subtype ≤ fittingInG M :=
    scn3_map_le_fittingInG_of_fittingInG_isPGroup hG hM hp P hFp hAP hA
  have hR_A : R ∈ hInvariant ⊤ (A.map M.subtype) {q} := by
    rw [mem_hInvariant]
    exact ⟨le_top, hA_le_F.trans (hInvariantStar_le_normalizer hR),
      hInvariantStar_isPiSubgroup hR⟩
  obtain ⟨S, hSstar, hRS⟩ := exists_le_hInvariantStar hR_A
  have hS_eq_Q : S = Q :=
    hInvariantStar_scn3_map_eq_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA hq hSstar hQ
  have hRQ : R ≤ Q := by
    rw [← hS_eq_Q]
    exact hRS
  have hQF : Q ∈ hInvariantStar ⊤ (fittingInG M) {q} :=
    hInvariantStar_scn3_map_mem_hInvariantStar_fittingInG_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA hq hQ
  exact (hInvariantStar_eq_of_le hR (hInvariantStar_mem_hInvariant hQF) hRQ).symm

/-- BG (8.12): `M` normalizes the unique member of `H_G^*(A;q)`. -/
theorem maximal_le_normalizer_hInvariantStar_scn3_map_of_fittingInG_isPGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) (hq : q ≠ p)
    {Q : Subgroup G} (hQ : Q ∈ hInvariantStar ⊤ (A.map M.subtype) {q}) :
    M ≤ Subgroup.normalizer (Q : Set G) := by
  have hQF : Q ∈ hInvariantStar ⊤ (fittingInG M) {q} :=
    hInvariantStar_scn3_map_mem_hInvariantStar_fittingInG_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA hq hQ
  intro x hxM
  have hxF : x ∈ Subgroup.normalizer (fittingInG M : Set G) :=
    mem_normalizer_fittingInG_of_mem hxM
  have hxF_eq : MulAut.conj x • (fittingInG M) = fittingInG M :=
    conj_smul_eq_self_of_mem_normalizer hxF
  have hQconjF : MulAut.conj x • Q ∈ hInvariantStar ⊤ (fittingInG M) {q} :=
    conj_smul_mem_hInvariantStar_top_of_normalizer hQF hxF_eq
  have hconj_eq : MulAut.conj x • Q = Q :=
    hInvariantStar_fittingInG_eq_of_scn3_map_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA hq hQ hQconjF
  exact mem_normalizer_of_conj_smul_eq_self hconj_eq

/-- BG (8.12): for `q ≠ p`, every member of `H_G^*(A;q)` is trivial in the p-group case. -/
theorem hInvariantStar_scn3_map_eq_bot_of_fittingInG_isPGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) (hq : q ≠ p)
    {Q : Subgroup G} (hQ : Q ∈ hInvariantStar ⊤ (A.map M.subtype) {q}) :
    Q = ⊥ := by
  by_cases hQbot : Q = ⊥
  · exact hQbot
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    maximal_le_normalizer_hInvariantStar_scn3_map_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA hq hQ
  have hQM : Q ≤ M :=
    le_maximal_of_le_normalizer_of_ne_bot_isPiSubgroup_singleton hG hM hMQ hQbot
      (hInvariantStar_isPiSubgroup hQ)
  have hQnorm : (Q.subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hMQ
  have hQleF : Q ≤ fittingInG M :=
    le_fittingInG_of_normal_isPiSubgroup_singleton hQM hQnorm
      (hInvariantStar_isPiSubgroup hQ)
  have hFpi : Subgroup.IsPiSubgroup ({p} : Set ℕ) (fittingInG M) :=
    isPiSubgroup_singleton_of_isPGroup hFp
  have hQpi_compl : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ Q := by
    intro r hr
    have hrq : r = q := Set.mem_singleton_iff.mp ((hInvariantStar_isPiSubgroup hQ) r hr)
    rw [hrq]
    simpa [Set.mem_singleton_iff] using hq
  exact eq_bot_of_le_of_isPiSubgroup_of_isPiSubgroup_compl hQleF hFpi hQpi_compl

/-- BG (8.12), non-star form: for `q ≠ p`, every `A`-invariant q-subgroup is trivial. -/
theorem hInvariant_scn3_map_eq_bot_of_fittingInG_isPGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) (hq : q ≠ p)
    {Q : Subgroup G} (hQ : Q ∈ hInvariant ⊤ (A.map M.subtype) {q}) :
    Q = ⊥ := by
  obtain ⟨R, hRstar, hQR⟩ := exists_le_hInvariantStar hQ
  have hRbot : R = ⊥ :=
    hInvariantStar_scn3_map_eq_bot_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA hq hRstar
  exact le_bot_iff.mp (by simpa [hRbot] using hQR)

/-- BG (8.12), `p'` form: every `A`-invariant `p'`-subgroup is trivial in the
p-group case. -/
theorem hInvariant_scn3_map_singleton_compl_eq_bot_of_fittingInG_isPGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M)))
    {Y : Subgroup G} (hY : Y ∈ hInvariant ⊤ (A.map M.subtype) ({p} : Set ℕ)ᶜ) :
    Y = ⊥ := by
  by_contra hYne
  have hp_dvd_G : p ∣ Nat.card G :=
    (Nat.mem_primeFactors.mp hp).2.1.trans (Subgroup.card_subgroup_dvd_card (fittingInG M))
  have hYpi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ Y := hInvariant_isPiSubgroup hY
  have hYlt : Y < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hYtop
    have hpY : p ∈ (Nat.card ↥Y).primeFactors := by
      rw [hYtop, Subgroup.card_top]
      exact Nat.mem_primeFactors.mpr ⟨Fact.out, hp_dvd_G, Nat.card_pos.ne'⟩
    have hp_not : p ∈ ({p} : Set ℕ)ᶜ := hYpi p hpY
    exact hp_not (by simp)
  have hYsolv : Group.IsSolvable ↥Y := hG.isSolvable_of_lt_top Y hYlt
  have hY_nontriv : Nontrivial ↥Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hYne
  have hFY_ne : fittingInG Y ≠ ⊥ := by
    have hF_ne : Ch01.fitting ↥Y ≠ ⊥ := Ch01.fitting_ne_bot_of_isSolvable_nontrivial ↥Y
    intro hbot
    rw [fittingInG] at hbot
    exact hF_ne ((Subgroup.map_eq_bot_iff_of_injective (Ch01.fitting ↥Y)
      Y.subtype_injective).mp hbot)
  have hFY_card_ne_one : Nat.card ↥(fittingInG Y) ≠ 1 := by
    intro hcard
    exact hFY_ne (Subgroup.card_eq_one.mp hcard)
  obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hFY_card_ne_one
  have hqFact : Fact q.Prime := ⟨hq_prime⟩
  have hqF : q ∈ (Nat.card ↥(fittingInG Y)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd, Nat.card_pos.ne'⟩
  have hqY : q ∈ (Nat.card ↥Y).primeFactors :=
    Nat.primeFactors_mono (Subgroup.card_dvd_of_le (fittingInG_le Y)) Nat.card_pos.ne' hqF
  have hq_compl : q ∈ ({p} : Set ℕ)ᶜ := hYpi q hqY
  have hq_ne_p : q ≠ p := by
    simpa [Set.mem_singleton_iff] using hq_compl
  let Oq : Subgroup G := opiCoreInG ({q} : Set ℕ) Y
  have hOq_ne : Oq ≠ ⊥ := by
    dsimp [Oq]
    exact opiCoreInG_singleton_ne_bot_of_mem_primeFactors_fittingInG (H := Y) hqF
  have hOq_mem : Oq ∈ hInvariant ⊤ (A.map M.subtype) {q} := by
    rw [mem_hInvariant]
    refine ⟨le_top, ?_, ?_⟩
    · dsimp [Oq]
      exact le_normalizer_opiCoreInG_of_le_normalizer ({q} : Set ℕ)
        (hInvariant_le_normalizer hY)
    · dsimp [Oq]
      exact isPiSubgroup_opiCoreInG ({q} : Set ℕ) Y
  have hOq_bot : Oq = ⊥ :=
    hInvariant_scn3_map_eq_bot_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA hq_ne_p hOq_mem
  exact hOq_ne hOq_bot

/-- BG (8.13), first p-group input: any subgroup containing the local `SCN₃(P)` image
has trivial `p'`-core. -/
theorem opiCoreInG_singleton_compl_eq_bot_of_scn3_map_le_of_fittingInG_isPGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {M H : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M))
    {A : Subgroup ↥M} (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M)))
    (hAH : A.map M.subtype ≤ H) :
    opiCoreInG ({p} : Set ℕ)ᶜ H = ⊥ := by
  have hY : opiCoreInG ({p} : Set ℕ)ᶜ H ∈
      hInvariant ⊤ (A.map M.subtype) ({p} : Set ℕ)ᶜ := by
    rw [mem_hInvariant]
    refine ⟨le_top, ?_, ?_⟩
    · exact hAH.trans (le_normalizer_opiCoreInG ({p} : Set ℕ)ᶜ H)
    · exact isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ H
  exact hInvariant_scn3_map_singleton_compl_eq_bot_of_fittingInG_isPGroup
    hG hM hp P hFp hAP hA hY

/-- BG (8.13), second p-group input: if the `p'`-core of `H` is trivial, then
Theorem 6.2 makes `Z(L(R))` normal in `H` for every Sylow `p`-subgroup `R` of `H`. -/
theorem zCenterLOdd_sylow_map_subgroupOf_normal_of_opiCoreInG_singleton_compl_eq_bot
    [Finite G] (hG : IsMinimalSimpleOdd G) {H : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hp_dvd_G : p ∣ Nat.card G) (R : Sylow p ↥H) (hH_solvable : Group.IsSolvable ↥H)
    (hOpBot : opiCoreInG ({p} : Set ℕ)ᶜ H = ⊥) :
    (((OddOrder.BG.AppB.zCenterLOdd (R : Subgroup ↥H)).map H.subtype).subgroupOf H).Normal := by
  have hp_odd_prop : Odd p := hG.odd.of_dvd_nat hp_dvd_G
  have hp_odd : p ≠ 2 := by
    rintro rfl
    rw [Nat.odd_iff] at hp_odd_prop
    omega
  have hoddH : Odd (Nat.card ↥H) :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card H)
  have hmap_bot : (Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥H).map H.subtype = ⊥ := by
    simpa [opiCoreInG] using hOpBot
  have hcore_bot_compl : Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥H = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective
      (Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥H) H.subtype_injective).mp hmap_bot
  -- `{q | q ≠ p}` is definitionally `({p} : Set ℕ)ᶜ`.
  have hcore_bot : Ch03.oPiCore {q | q ≠ p} ↥H = ⊥ := hcore_bot_compl
  have hZ_norm_H : (OddOrder.BG.AppB.zCenterLOdd (R : Subgroup ↥H)).Normal := by
    have h := OddOrder.BG.AppB.zCenter_lOdd_sup_oPiCore_normal hp_odd hH_solvable hoddH R
    rwa [hcore_bot, sup_bot_eq] at h
  have hH_norm_Z : H ≤ Subgroup.normalizer
      (((OddOrder.BG.AppB.zCenterLOdd (R : Subgroup ↥H)).map H.subtype) : Set G) := by
    have h1 : (Subgroup.normalizer (OddOrder.BG.AppB.zCenterLOdd (R : Subgroup ↥H) : Set ↥H)).map
        H.subtype ≤ Subgroup.normalizer
          (((OddOrder.BG.AppB.zCenterLOdd (R : Subgroup ↥H)).map H.subtype) : Set G) :=
      Subgroup.le_normalizer_map H.subtype
    rw [Subgroup.normalizer_eq_top_iff.mpr hZ_norm_H] at h1
    have htop_map : (⊤ : Subgroup ↥H).map H.subtype = H := by
      rw [← MonoidHom.range_eq_map, H.range_subtype]
    simpa [htop_map] using h1
  exact Subgroup.normal_subgroupOf_of_le_normalizer hH_norm_Z

/-- BG (8.13), Sylow setup: if the local `SCN₃(P)` subgroup image lies in `H`,
then it lies in a Sylow `p`-subgroup of the intersection `H ⊓ M`. -/
theorem exists_sylow_inf_containing_scn3_map_of_le
    {M H : Subgroup G} {p : ℕ} [Fact p.Prime]
    (P : Sylow p ↥M) {A : Subgroup ↥M}
    (hAP : A ≤ (P : Subgroup ↥M)) (hAH : A.map M.subtype ≤ H) :
    ∃ R : Sylow p ↥(H ⊓ M),
      (A.map M.subtype).subgroupOf (H ⊓ M) ≤ (R : Subgroup ↥(H ⊓ M)) := by
  have hA_le_inf : A.map M.subtype ≤ H ⊓ M :=
    le_inf hAH (Subgroup.map_subtype_le A)
  have hAsub_p : IsPGroup p (A.subgroupOf (P : Subgroup ↥M)) :=
    P.isPGroup'.to_subgroup _
  have hA_p : IsPGroup p A :=
    hAsub_p.of_equiv (Subgroup.subgroupOfEquivOfLe hAP)
  have hAmap_p : IsPGroup p (A.map M.subtype) :=
    hA_p.map M.subtype
  have hAinf_p : IsPGroup p ((A.map M.subtype).subgroupOf (H ⊓ M)) :=
    hAmap_p.of_equiv (Subgroup.subgroupOfEquivOfLe hA_le_inf).symm
  exact hAinf_p.exists_le_sylow

/-- A `SCN₃` subgroup is nontrivial. -/
theorem isSCN3_ne_bot [Finite G] {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : IsSCN₃ p A) :
    A ≠ ⊥ := by
  intro hbot
  have hprank_le : pRank A p ≤ 0 := by
    rw [pRank_le_iff]
    intro B hB
    have : Subsingleton A := by
      rw [hbot]
      infer_instance
    have hBcard : Nat.card B = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    rw [hBcard, Nat.log_one_right]
  have h3 : 3 ≤ pRank A p := hA.le_pRank
  omega

/-- A local `SCN₃(P)` subgroup has nontrivial image in the ambient group. -/
theorem scn3_map_ne_bot_of_le_sylow [Finite G]
    {M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (P : Sylow p ↥M) {A : Subgroup ↥M}
    (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M))) :
    A.map M.subtype ≠ ⊥ := by
  have hAsub_ne : A.subgroupOf (P : Subgroup ↥M) ≠ ⊥ :=
    isSCN3_ne_bot (G := ↥(P : Subgroup ↥M)) hA
  intro hAmap_bot
  have hA_bot : A = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective A M.subtype_injective).mp hAmap_bot
  have hAsub_bot : A.subgroupOf (P : Subgroup ↥M) = ⊥ := by
    have hmap_bot : (A.subgroupOf (P : Subgroup ↥M)).map
        (P : Subgroup ↥M).subtype = ⊥ := by
      rw [Subgroup.map_subgroupOf_eq_of_le hAP, hA_bot]
    exact (Subgroup.map_eq_bot_iff_of_injective _ (P : Subgroup ↥M).subtype_injective).mp
      hmap_bot
  exact hAsub_ne hAsub_bot

/-- BG (8.13), nontriviality setup: the Sylow subgroup of `H ⊓ M` containing the local
`SCN₃(P)` image is nontrivial. -/
theorem sylow_inf_ne_bot_of_scn3_map_le [Finite G]
    {M H : Subgroup G} {p : ℕ} [Fact p.Prime]
    (P : Sylow p ↥M) {A : Subgroup ↥M}
    (hAP : A ≤ (P : Subgroup ↥M))
    (hA : IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M)))
    (hAH : A.map M.subtype ≤ H) {R : Sylow p ↥(H ⊓ M)}
    (hA_R : (A.map M.subtype).subgroupOf (H ⊓ M) ≤
      (R : Subgroup ↥(H ⊓ M))) :
    (R : Subgroup ↥(H ⊓ M)) ≠ ⊥ := by
  have hAmap_ne : A.map M.subtype ≠ ⊥ :=
    scn3_map_ne_bot_of_le_sylow P hAP hA
  have hA_le_inf : A.map M.subtype ≤ H ⊓ M :=
    le_inf hAH (Subgroup.map_subtype_le A)
  have hAinf_ne : (A.map M.subtype).subgroupOf (H ⊓ M) ≠ ⊥ := by
    intro hAinf_bot
    apply hAmap_ne
    have hmap_bot : ((A.map M.subtype).subgroupOf (H ⊓ M)).map
        (H ⊓ M).subtype = ⊥ := by
      rw [hAinf_bot, Subgroup.map_bot]
    rwa [Subgroup.map_subgroupOf_eq_of_le hA_le_inf] at hmap_bot
  intro hR_bot
  exact hAinf_ne (le_bot_iff.mp (hA_R.trans (le_of_eq hR_bot)))

/-- A `p`-subgroup `K` of `H` is realized as a Sylow `p`-subgroup of `H` once its
index in `H` is prime to `p`. -/
theorem exists_sylow_subgroupOf_map_eq_of_not_dvd_index [Finite G]
    {p : ℕ} [Fact p.Prime] {H K : Subgroup G}
    (hKp : IsPGroup p K) (hKH : K ≤ H) (hidx : ¬ p ∣ (K.subgroupOf H).index) :
    ∃ R : Sylow p ↥H, (R : Subgroup ↥H).map H.subtype = K := by
  have hidx' : ¬ p ∣ (K.comap H.subtype).index := by
    rwa [Subgroup.comap_subtype]
  let R : Sylow p ↥H := (hKp.comap_subtype (K := H)).toSylow hidx'
  refine ⟨R, ?_⟩
  change ((hKp.comap_subtype (K := H)).toSylow hidx' : Subgroup ↥H).map H.subtype = K
  rw [(hKp.comap_subtype (K := H)).toSylow_coe hidx', Subgroup.comap_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKH]

/-- A `p`-subgroup `K ≤ H` has `p`-prime index in `H` if every `p`-subgroup of
`H` containing `K` has cardinal at most `K`. -/
theorem not_dvd_subgroupOf_index_of_forall_card_le [Finite G]
    {p : ℕ} [Fact p.Prime] {H K : Subgroup G}
    (hKp : IsPGroup p K) (hKH : K ≤ H)
    (hmax : ∀ L : Subgroup G, IsPGroup p L → K ≤ L → L ≤ H →
      Nat.card ↥L ≤ Nat.card ↥K) :
    ¬ p ∣ (K.subgroupOf H).index := by
  intro hidx
  have hKsub_p : IsPGroup p (K.subgroupOf H) :=
    hKp.of_equiv (Subgroup.subgroupOfEquivOfLe hKH).symm
  obtain ⟨S, hKS⟩ := hKsub_p.exists_le_sylow
  have hS_ne : (S : Subgroup ↥H) ≠ K.subgroupOf H := by
    intro hS
    have hnot : ¬ p ∣ (K.subgroupOf H).index := by
      simpa [hS] using S.not_dvd_index
    exact hnot hidx
  have hKsub_lt_S : K.subgroupOf H < (S : Subgroup ↥H) :=
    lt_of_le_of_ne hKS (fun h => hS_ne h.symm)
  have hcard_lt : Nat.card ↥(K.subgroupOf H) < Nat.card ↥(S : Subgroup ↥H) := by
    have hss : (K.subgroupOf H : Set ↥H) ⊂ ((S : Subgroup ↥H) : Set ↥H) :=
      SetLike.coe_ssubset_coe.mpr hKsub_lt_S
    exact Set.Finite.card_lt_card (Set.toFinite ((S : Subgroup ↥H) : Set ↥H)) hss
  have hK_le_Smap : K ≤ (S : Subgroup ↥H).map H.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hKH]
    exact Subgroup.map_mono hKS
  have hSmap_p : IsPGroup p ((S : Subgroup ↥H).map H.subtype) :=
    S.isPGroup'.map H.subtype
  have hSmap_le_H : (S : Subgroup ↥H).map H.subtype ≤ H :=
    Subgroup.map_subtype_le _
  have hSmap_card_le_K :
      Nat.card ↥((S : Subgroup ↥H).map H.subtype) ≤ Nat.card ↥K :=
    hmax _ hSmap_p hK_le_Smap hSmap_le_H
  have hSmap_card :
      Nat.card ↥((S : Subgroup ↥H).map H.subtype) = Nat.card ↥(S : Subgroup ↥H) :=
    Subgroup.card_map_of_injective H.subtype_injective
  have hKsub_card : Nat.card ↥(K.subgroupOf H) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
  have hS_card_le_Ksub : Nat.card ↥(S : Subgroup ↥H) ≤ Nat.card ↥(K.subgroupOf H) := by
    rw [← hSmap_card, hKsub_card]
    exact hSmap_card_le_K
  exact (not_lt_of_ge hS_card_le_Ksub) hcard_lt

/-- A subgroup properly contained in a finite `p`-group is properly contained in its
normalizer inside that `p`-group. -/
theorem lt_inf_normalizer_of_isPGroup_lt [Finite G]
    {p : ℕ} [Fact p.Prime] {K L : Subgroup G}
    (hL : IsPGroup p L) (hKL : K < L) :
    K < L ⊓ Subgroup.normalizer (K : Set G) := by
  have : Group.IsNilpotent ↥L := hL.isNilpotent
  have hNC : NormalizerCondition ↥L := Group.normalizerCondition_of_isNilpotent (G := ↥L)
  have hK_le : K ≤ L := le_of_lt hKL
  have hsub_lt_top : K.subgroupOf L < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact (ne_of_lt hKL) (le_antisymm hK_le htop)
  have hlt := hNC (K.subgroupOf L) hsub_lt_top
  obtain ⟨t, ht_norm, ht_not⟩ := SetLike.exists_of_lt hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hK_le, Subgroup.mem_subgroupOf] at ht_norm
  rw [Subgroup.mem_subgroupOf] at ht_not
  refine lt_of_le_of_ne (le_inf hK_le Subgroup.le_normalizer) ?_
  intro heq
  apply ht_not
  have hmem : (t : G) ∈ L ⊓ Subgroup.normalizer (K : Set G) := ⟨t.2, ht_norm⟩
  rw [← heq] at hmem
  exact hmem

/-- The ambient image of a Sylow subgroup of `H ⊓ M` dominates every ambient
`p`-subgroup lying in `H ⊓ M` and containing that image. -/
theorem card_le_sylow_inf_map_of_le [Finite G]
    {M H : Subgroup G} {p : ℕ} [Fact p.Prime]
    (R : Sylow p ↥(H ⊓ M)) {L : Subgroup G}
    (hLp : IsPGroup p L)
    (hRL : (R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype ≤ L)
    (hLH : L ≤ H) (hLM : L ≤ M) :
    Nat.card ↥L ≤ Nat.card ↥((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) := by
  have hL_inf : L ≤ H ⊓ M := le_inf hLH hLM
  have hLsub_p : IsPGroup p (L.subgroupOf (H ⊓ M)) :=
    hLp.of_equiv (Subgroup.subgroupOfEquivOfLe hL_inf).symm
  have hR_le_Lsub : (R : Subgroup ↥(H ⊓ M)) ≤ L.subgroupOf (H ⊓ M) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hRL ⟨x, hx, rfl⟩
  have hLsub_eq_R : L.subgroupOf (H ⊓ M) = (R : Subgroup ↥(H ⊓ M)) :=
    R.is_maximal' hLsub_p hR_le_Lsub
  have hLsub_card : Nat.card ↥(L.subgroupOf (H ⊓ M)) = Nat.card ↥L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL_inf).toEquiv
  have hRmap_card :
      Nat.card ↥((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) =
        Nat.card ↥(R : Subgroup ↥(H ⊓ M)) :=
    Subgroup.card_map_of_injective (H ⊓ M).subtype_injective
  rw [← hLsub_card, hLsub_eq_R, hRmap_card]

/-- If the ambient normalizer of the Sylow image in `H ⊓ M` lies in `M`, then that
image is card-maximal among `p`-subgroups of `H` containing it. -/
theorem forall_card_le_of_normalizer_sylow_inf_map_le [Finite G]
    {M H : Subgroup G} {p : ℕ} [Fact p.Prime]
    (R : Sylow p ↥(H ⊓ M))
    (hN_le_M : Subgroup.normalizer
      (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) ≤ M) :
    ∀ L : Subgroup G, IsPGroup p L →
      (R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype ≤ L → L ≤ H →
      Nat.card ↥L ≤ Nat.card ↥((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) := by
  intro L hLp hRL hLH
  by_cases hL_le_R : L ≤ (R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype
  · exact Subgroup.card_le_of_le hL_le_R
  · have hR_lt_L :
        (R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype < L :=
      lt_of_le_of_ne hRL (fun hEq => hL_le_R (le_of_eq hEq.symm))
    have hR_lt_LN := lt_inf_normalizer_of_isPGroup_lt hLp hR_lt_L
    have hLN_p : IsPGroup p
        (L ⊓ Subgroup.normalizer
          (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) : Subgroup G) :=
      hLp.to_inf_left
    have hLN_le_H : L ⊓ Subgroup.normalizer
        (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) ≤ H :=
      inf_le_left.trans hLH
    have hLN_le_M : L ⊓ Subgroup.normalizer
        (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) ≤ M :=
      inf_le_right.trans hN_le_M
    have hLN_card_le_R :=
      card_le_sylow_inf_map_of_le R hLN_p hR_lt_LN.le hLN_le_H hLN_le_M
    have hcard_lt :
        Nat.card ↥((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) <
          Nat.card ↥(L ⊓ Subgroup.normalizer
            (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) : Subgroup G) := by
      have hss :
          (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype : Subgroup G) : Set G) ⊂
            ((L ⊓ Subgroup.normalizer
              (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) : Subgroup G) : Set G) :=
        SetLike.coe_ssubset_coe.mpr hR_lt_LN
      exact Set.Finite.card_lt_card (Set.toFinite
        ((L ⊓ Subgroup.normalizer
          (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) : Subgroup G) : Set G)) hss
    exact False.elim ((not_lt_of_ge hLN_card_le_R) hcard_lt)

/-- If `Z(L(K))`, realized in the ambient group, is nontrivial and normal in a maximal
subgroup `H`, then its ambient normalizer is exactly `H`. -/
theorem normalizer_zCenterLOdd_map_eq_of_normal_of_ne_bot [Finite G]
    (hG : IsMinimalSimpleOdd G) {H : Subgroup G} (hH : H ∈ maximalSubgroups G)
    {K : Subgroup ↥H}
    (hZnorm : (((OddOrder.BG.AppB.zCenterLOdd K).map H.subtype).subgroupOf H).Normal)
    (hZne : (OddOrder.BG.AppB.zCenterLOdd K).map H.subtype ≠ ⊥) :
    Subgroup.normalizer (((OddOrder.BG.AppB.zCenterLOdd K).map H.subtype) : Set G) = H :=
  normalizer_eq_of_normal_of_mem_maximal hG hH hZnorm hZne (Subgroup.map_subtype_le _)

/-- The BG (8.13) counterexample measure: the order of a Sylow `p`-subgroup of
`K ⊓ M`, i.e. the `p`-part of `|K ∩ M|` in the finite setting. -/
noncomputable def sylowInfCard (p : ℕ) [Fact p.Prime] (K M : Subgroup G) : ℕ :=
  Nat.card ↥((default : Sylow p ↥(K ⊓ M)) : Subgroup ↥(K ⊓ M))

/-- `sylowInfCard` is independent of the chosen Sylow subgroup. -/
theorem sylowInfCard_eq_card [Finite G]
    (p : ℕ) [Fact p.Prime] (K M : Subgroup G) (R : Sylow p ↥(K ⊓ M)) :
    sylowInfCard p K M = Nat.card ↥(R : Subgroup ↥(K ⊓ M)) := by
  unfold sylowInfCard
  rw [Sylow.card_eq_multiplicity (default : Sylow p ↥(K ⊓ M)),
    Sylow.card_eq_multiplicity R]

/-- Any ambient `p`-subgroup contained in `L ⊓ M` is bounded by `sylowInfCard p L M`. -/
theorem card_le_sylowInfCard_of_isPGroup_le [Finite G]
    {p : ℕ} [Fact p.Prime] {L M K : Subgroup G}
    (hKp : IsPGroup p K) (hKL : K ≤ L) (hKM : K ≤ M) :
    Nat.card ↥K ≤ sylowInfCard p L M := by
  have hK_inf : K ≤ L ⊓ M := le_inf hKL hKM
  have hKsub_p : IsPGroup p (K.subgroupOf (L ⊓ M)) :=
    hKp.of_equiv (Subgroup.subgroupOfEquivOfLe hK_inf).symm
  obtain ⟨S, hKS⟩ := hKsub_p.exists_le_sylow
  have hKsub_card : Nat.card ↥(K.subgroupOf (L ⊓ M)) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK_inf).toEquiv
  calc
    Nat.card ↥K = Nat.card ↥(K.subgroupOf (L ⊓ M)) := hKsub_card.symm
    _ ≤ Nat.card ↥(S : Subgroup ↥(L ⊓ M)) := Subgroup.card_le_of_le hKS
    _ = sylowInfCard p L M := (sylowInfCard_eq_card p L M S).symm

/-- If the normalizer of `K` lies in `L` and the `p`-part of `L ⊓ M` is no larger
than `K`, then `K` is card-maximal among `p`-subgroups of `M` containing it. -/
theorem forall_card_le_of_normalizer_le_and_sylowInfCard_le [Finite G]
    {p : ℕ} [Fact p.Prime] {L M K : Subgroup G}
    (hN_le_L : Subgroup.normalizer (K : Set G) ≤ L)
    (hbound : sylowInfCard p L M ≤ Nat.card ↥K) :
    ∀ T : Subgroup G, IsPGroup p T → K ≤ T → T ≤ M → Nat.card ↥T ≤ Nat.card ↥K := by
  intro T hTp hKT hTM
  by_cases hT_le_K : T ≤ K
  · exact Subgroup.card_le_of_le hT_le_K
  · have hK_lt_T : K < T :=
      lt_of_le_of_ne hKT (fun hEq => hT_le_K (le_of_eq hEq.symm))
    have hK_lt_TN := lt_inf_normalizer_of_isPGroup_lt hTp hK_lt_T
    have hTN_p : IsPGroup p (T ⊓ Subgroup.normalizer (K : Set G) : Subgroup G) :=
      hTp.to_inf_left
    have hTN_le_L : T ⊓ Subgroup.normalizer (K : Set G) ≤ L :=
      inf_le_right.trans hN_le_L
    have hTN_le_M : T ⊓ Subgroup.normalizer (K : Set G) ≤ M :=
      inf_le_left.trans hTM
    have hTN_card_le_K :
        Nat.card ↥(T ⊓ Subgroup.normalizer (K : Set G) : Subgroup G) ≤ Nat.card ↥K :=
      (card_le_sylowInfCard_of_isPGroup_le hTN_p hTN_le_L hTN_le_M).trans hbound
    have hcard_lt :
        Nat.card ↥K < Nat.card ↥(T ⊓ Subgroup.normalizer (K : Set G) : Subgroup G) := by
      have hss : (K : Set G) ⊂ ((T ⊓ Subgroup.normalizer (K : Set G) : Subgroup G) : Set G) :=
        SetLike.coe_ssubset_coe.mpr hK_lt_TN
      exact Set.Finite.card_lt_card (Set.toFinite
        ((T ⊓ Subgroup.normalizer (K : Set G) : Subgroup G) : Set G)) hss
    exact False.elim ((not_lt_of_ge hTN_card_le_K) hcard_lt)

/-- If the normalizer of `K` lies in `L` and `sylowInfCard p L M` is bounded by `K`,
then `K`, viewed inside `M`, is a Sylow `p`-subgroup. -/
theorem exists_sylow_map_eq_of_normalizer_le_and_sylowInfCard_le [Finite G]
    {p : ℕ} [Fact p.Prime] {L M K : Subgroup G}
    (hKp : IsPGroup p K) (hKM : K ≤ M)
    (hN_le_L : Subgroup.normalizer (K : Set G) ≤ L)
    (hbound : sylowInfCard p L M ≤ Nat.card ↥K) :
    ∃ R : Sylow p ↥M, (R : Subgroup ↥M).map M.subtype = K :=
  exists_sylow_subgroupOf_map_eq_of_not_dvd_index hKp hKM
    (not_dvd_subgroupOf_index_of_forall_card_le hKp hKM
      (forall_card_le_of_normalizer_le_and_sylowInfCard_le hN_le_L hbound))

/-- If an ambient subgroup has the same cardinal as a Sylow subgroup, every ambient
`p`-subgroup has cardinal at most that subgroup. -/
theorem card_le_of_isPGroup_of_card_eq_sylow [Finite G]
    {p : ℕ} [Fact p.Prime] {K L : Subgroup G} (Q : Sylow p G)
    (hKcard : Nat.card ↥K = Nat.card ↥(Q : Subgroup G))
    (hLp : IsPGroup p L) :
    Nat.card ↥L ≤ Nat.card ↥K := by
  obtain ⟨S, hLS⟩ := hLp.exists_le_sylow
  calc
    Nat.card ↥L ≤ Nat.card ↥(S : Subgroup G) := Subgroup.card_le_of_le hLS
    _ = Nat.card ↥(Q : Subgroup G) := by
      rw [Sylow.card_eq_multiplicity S, Sylow.card_eq_multiplicity Q]
    _ = Nat.card ↥K := hKcard.symm

/-- If the normalizer of the Sylow image in `H ⊓ M` lies in `H`, then that image is
card-maximal among `p`-subgroups of `M` containing it. -/
theorem forall_card_le_of_normalizer_sylow_inf_map_le_left [Finite G]
    {M H : Subgroup G} {p : ℕ} [Fact p.Prime]
    (R : Sylow p ↥(H ⊓ M))
    (hN_le_H : Subgroup.normalizer
      (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) ≤ H) :
    ∀ L : Subgroup G, IsPGroup p L →
      (R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype ≤ L → L ≤ M →
      Nat.card ↥L ≤ Nat.card ↥((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) := by
  intro L hLp hRL hLM
  by_cases hL_le_R : L ≤ (R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype
  · exact Subgroup.card_le_of_le hL_le_R
  · have hR_lt_L :
        (R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype < L :=
      lt_of_le_of_ne hRL (fun hEq => hL_le_R (le_of_eq hEq.symm))
    have hR_lt_LN := lt_inf_normalizer_of_isPGroup_lt hLp hR_lt_L
    have hLN_p : IsPGroup p
        (L ⊓ Subgroup.normalizer
          (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) : Subgroup G) :=
      hLp.to_inf_left
    have hLN_le_H : L ⊓ Subgroup.normalizer
        (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) ≤ H :=
      inf_le_right.trans hN_le_H
    have hLN_le_M : L ⊓ Subgroup.normalizer
        (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) ≤ M :=
      inf_le_left.trans hLM
    have hLN_card_le_R :=
      card_le_sylow_inf_map_of_le R hLN_p hR_lt_LN.le hLN_le_H hLN_le_M
    have hcard_lt :
        Nat.card ↥((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) <
          Nat.card ↥(L ⊓ Subgroup.normalizer
            (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) : Subgroup G) := by
      have hss :
          (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype : Subgroup G) : Set G) ⊂
            ((L ⊓ Subgroup.normalizer
              (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) : Subgroup G) : Set G) :=
        SetLike.coe_ssubset_coe.mpr hR_lt_LN
      exact Set.Finite.card_lt_card (Set.toFinite
        ((L ⊓ Subgroup.normalizer
          (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) : Subgroup G) : Set G)) hss
    exact False.elim ((not_lt_of_ge hLN_card_le_R) hcard_lt)

/-- If the local `A` lies in the chosen Sylow subgroup of `H ⊓ M`, then its ambient image
lies in the ambient image of that Sylow subgroup. -/
theorem scn3_map_le_sylow_inf_map_of_le
    {M H : Subgroup G} {p : ℕ} [Fact p.Prime] {A : Subgroup ↥M}
    (hAH : A.map M.subtype ≤ H) {R : Sylow p ↥(H ⊓ M)}
    (hA_R : (A.map M.subtype).subgroupOf (H ⊓ M) ≤
      (R : Subgroup ↥(H ⊓ M))) :
    A.map M.subtype ≤ (R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype := by
  intro x hx
  have hx_inf : x ∈ H ⊓ M := ⟨hAH hx, Subgroup.map_subtype_le A hx⟩
  let xinf : ↥(H ⊓ M) := ⟨x, hx_inf⟩
  have hx_sub : xinf ∈ (A.map M.subtype).subgroupOf (H ⊓ M) := by
    rw [Subgroup.mem_subgroupOf]
    exact hx
  exact ⟨xinf, hA_R hx_sub, rfl⟩

/-- If the local `A` lies in the chosen Sylow subgroup of `H ⊓ M`, then its ambient image
normalizes the ambient image of that Sylow subgroup. -/
theorem scn3_map_le_normalizer_sylow_inf_map_of_le
    {M H : Subgroup G} {p : ℕ} [Fact p.Prime] {A : Subgroup ↥M}
    (hAH : A.map M.subtype ≤ H) {R : Sylow p ↥(H ⊓ M)}
    (hA_R : (A.map M.subtype).subgroupOf (H ⊓ M) ≤
      (R : Subgroup ↥(H ⊓ M))) :
    A.map M.subtype ≤
      Subgroup.normalizer (((R : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) :=
  (scn3_map_le_sylow_inf_map_of_le hAH hA_R).trans Subgroup.le_normalizer

/-- In a minimal simple group, the normalizer of a nontrivial subgroup lying in a maximal
subgroup is contained in some maximal subgroup. -/
theorem exists_maximalSubgroup_containing_normalizer_of_ne_bot_le_maximal [Finite G]
    (hG : IsMinimalSimpleOdd G) {M K : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKne : K ≠ ⊥) (hKM : K ≤ M) :
    ∃ L : Subgroup G, L ∈ maximalSubgroups G ∧ Subgroup.normalizer (K : Set G) ≤ L := by
  have : IsSimpleGroup G := hG.simple
  have hMco : IsCoatom M := mem_maximalSubgroups.mp hM
  have hN_ne_top : Subgroup.normalizer (K : Set G) ≠ ⊤ := by
    intro hN_top
    have hK_normal : K.Normal := Subgroup.normalizer_eq_top_iff.mp hN_top
    rcases hK_normal.eq_bot_or_eq_top with hK_bot | hK_top
    · exact hKne hK_bot
    · have htop_le_M : ⊤ ≤ M := by
        rw [← hK_top]
        exact hKM
      exact hMco.lt_top.ne (eq_top_iff.mpr htop_le_M)
  obtain ⟨L, hLco, hN_le_L⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer (K : Set G))).resolve_left hN_ne_top
  exact ⟨L, hLco, hN_le_L⟩

/-- **BG Theorem 8.1(b)** (mmd L2319-2322): 同じ仮定で `F(M)` が `p`-群なら、`M` の Sylow
`p`-部分群 `P` は `G` の Sylow `p`-部分群であり、`SCN₃(P)` の各元は `F(M)` に含まれ `𝒰` に属す。

`SCN₃(P)` 非空は §5 Lem 5.1 (Remark, mmd L2324) で保証されるが、この定理型では
非空性を仮定にせず、BG 本文どおり `SCN₃(P)` の任意の元に対する結論として保持する。 -/
theorem sylow_isSylow_and_scn3_isUniquelyMaximal_of_pGroup [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    {A₀ : Subgroup G} (_hA₀ : isMaxElemAbelianIn p A₀ (fittingInG M))
    (_hm : 3 ≤ rank ↥A₀)
    (P : Sylow p ↥M) (hFp : IsPGroup p ↥(fittingInG M)) :
    (∃ Q : Sylow p G, (Q : Subgroup G) = (P : Subgroup ↥M).map M.subtype) ∧
    (∀ A : Subgroup ↥M, A ≤ (P : Subgroup ↥M) → IsSCN₃ p (A.subgroupOf (P : Subgroup ↥M)) →
      A.map M.subtype ≤ fittingInG M ∧ IsUniquelyMaximal (A.map M.subtype)) := by
  obtain ⟨Q, hQ⟩ := sylow_map_mem_range_of_fittingInG_isPGroup hG hM hp P hFp
  refine ⟨⟨Q, hQ⟩, ?_⟩
  intro A hAP hA
  have hAglobal : A.map M.subtype ∈ OddOrder.BG.Ch2.S07.scn3Global p G :=
    scn3_map_mem_scn3Global_of_sylow_map P hQ hAP hA
  have hCentM : Subgroup.centralizer (A.map M.subtype : Set G) ≤ M :=
    centralizer_scn3_map_le_maximal_of_fittingInG_isPGroup hG hM hp P hFp hAP hA
  have hOpCentBot :
      opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer (A.map M.subtype : Set G)) = ⊥ :=
    opiCoreInG_singleton_compl_centralizer_scn3_map_eq_bot_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA
  have hHqBot : ∀ {q : ℕ} [Fact q.Prime], q ≠ p →
      ∀ {Y : Subgroup G}, Y ∈ hInvariant ⊤ (A.map M.subtype) {q} → Y = ⊥ := by
    intro q _ hq Y hY
    exact hInvariant_scn3_map_eq_bot_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA hq hY
  have hHpPrimeBot : ∀ {Y : Subgroup G},
      Y ∈ hInvariant ⊤ (A.map M.subtype) ({p} : Set ℕ)ᶜ → Y = ⊥ := by
    intro Y hY
    exact hInvariant_scn3_map_singleton_compl_eq_bot_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA hY
  have hAF : A.map M.subtype ≤ fittingInG M :=
    scn3_map_le_fittingInG_of_fittingInG_isPGroup hG hM hp P hFp hAP hA
  refine ⟨hAF, ?_⟩
  have hA_le_M : A.map M.subtype ≤ M := hAF.trans (fittingInG_le M)
  have hA_proper : A.map M.subtype < ⊤ :=
    lt_of_le_of_lt hA_le_M (mem_maximalSubgroups.mp hM).lt_top
  by_contra hnotU
  obtain ⟨H, hH, hAH, hH_ne_M, hHmax⟩ :=
    exists_maximal_counterexample_image_of_not_isUniquelyMaximal
      (H := A.map M.subtype) (M := M)
      (w := fun K : Subgroup G => sylowInfCard p K M)
      hA_proper hM hA_le_M hnotU
  have hHco : IsCoatom H := mem_maximalSubgroups.mp hH
  have hH_solvable : Group.IsSolvable ↥H := hG.isSolvable_of_lt_top H hHco.lt_top
  have hOpComplHBot : opiCoreInG ({p} : Set ℕ)ᶜ H = ⊥ :=
    opiCoreInG_singleton_compl_eq_bot_of_scn3_map_le_of_fittingInG_isPGroup
      hG hM hp P hFp hAP hA hAH
  have hp_dvd_G : p ∣ Nat.card G :=
    (Nat.mem_primeFactors.mp hp).2.1.trans (Subgroup.card_subgroup_dvd_card (fittingInG M))
  have hZNormH : ∀ R : Sylow p ↥H,
      (((OddOrder.BG.AppB.zCenterLOdd (R : Subgroup ↥H)).map H.subtype).subgroupOf H).Normal := by
    intro R
    exact zCenterLOdd_sylow_map_subgroupOf_normal_of_opiCoreInG_singleton_compl_eq_bot
      hG hp_dvd_G R hH_solvable hOpComplHBot
  obtain ⟨Rinf, hA_Rinf⟩ := exists_sylow_inf_containing_scn3_map_of_le P hAP hAH
  have hRinf_ne_bot : (Rinf : Subgroup ↥(H ⊓ M)) ≠ ⊥ :=
    sylow_inf_ne_bot_of_scn3_map_le P hAP hA hAH hA_Rinf
  have hZ_Rinf_ne_bot :
      ((OddOrder.BG.AppB.zCenterLOdd (Rinf : Subgroup ↥(H ⊓ M))).map
        (H ⊓ M).subtype) ≠ ⊥ := by
    have hZ_ne : OddOrder.BG.AppB.zCenterLOdd (Rinf : Subgroup ↥(H ⊓ M)) ≠ ⊥ :=
      zCenterLOdd_ne_bot_of_isPGroup Rinf.isPGroup' hRinf_ne_bot
    intro hZ_map_bot
    exact hZ_ne ((Subgroup.map_eq_bot_iff_of_injective _
      (H ⊓ M).subtype_injective).mp hZ_map_bot)
  have hZ_Rinf_le_Rinf_amb :
      ((OddOrder.BG.AppB.zCenterLOdd (Rinf : Subgroup ↥(H ⊓ M))).map
        (H ⊓ M).subtype) ≤
          (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype :=
    zCenterLOdd_map_le_map (H := H ⊓ M) (Rinf : Subgroup ↥(H ⊓ M))
  have hSylowInfCard_H :
      sylowInfCard p H M = Nat.card ↥(Rinf : Subgroup ↥(H ⊓ M)) :=
    sylowInfCard_eq_card p H M Rinf
  have hHmax_Rinf : ∀ L : Subgroup G, L ∈ maximalSubgroups G →
      A.map M.subtype ≤ L → L ≠ M →
      sylowInfCard p L M ≤ Nat.card ↥(Rinf : Subgroup ↥(H ⊓ M)) := by
    intro L hL hAL hLM
    calc
      sylowInfCard p L M ≤ sylowInfCard p H M := hHmax L hL hAL hLM
      _ = Nat.card ↥(Rinf : Subgroup ↥(H ⊓ M)) := hSylowInfCard_H
  have hA_le_Rinf_amb :
      A.map M.subtype ≤ (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype :=
    scn3_map_le_sylow_inf_map_of_le hAH hA_Rinf
  have hA_le_NRinf : A.map M.subtype ≤
      Subgroup.normalizer (((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) :=
    scn3_map_le_normalizer_sylow_inf_map_of_le hAH hA_Rinf
  have hNRinf_le_NZ_Rinf :
      Subgroup.normalizer
          (((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) ≤
        Subgroup.normalizer
          (((OddOrder.BG.AppB.zCenterLOdd (Rinf : Subgroup ↥(H ⊓ M))).map
            (H ⊓ M).subtype) : Set G) :=
    normalizer_map_le_normalizer_zCenterLOdd_map
      (H := H ⊓ M) (Rinf : Subgroup ↥(H ⊓ M))
  have hA_le_NZ_Rinf : A.map M.subtype ≤
      Subgroup.normalizer
        (((OddOrder.BG.AppB.zCenterLOdd (Rinf : Subgroup ↥(H ⊓ M))).map
          (H ⊓ M).subtype) : Set G) :=
    hA_le_NRinf.trans hNRinf_le_NZ_Rinf
  have hRinf_amb_ne_bot :
      (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype ≠ ⊥ := by
    intro hR_map_bot
    exact hRinf_ne_bot
      ((Subgroup.map_eq_bot_iff_of_injective _
        (H ⊓ M).subtype_injective).mp hR_map_bot)
  have hRinf_amb_le_M :
      (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype ≤ M := by
    intro x hx
    rcases hx with ⟨xinf, -, rfl⟩
    exact xinf.2.2
  have hRinf_amb_le_H :
      (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype ≤ H := by
    intro x hx
    rcases hx with ⟨xinf, -, rfl⟩
    exact xinf.2.1
  have hRinf_amb_p :
      IsPGroup p ((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) :=
    Rinf.isPGroup'.map (H ⊓ M).subtype
  have hRinfH_of_not_dvd :
      (¬ p ∣ (((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype).subgroupOf H).index) →
        ∃ RinfH : Sylow p ↥H,
          (RinfH : Subgroup ↥H).map H.subtype =
            (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype := by
    intro hidx
    exact exists_sylow_subgroupOf_map_eq_of_not_dvd_index
      hRinf_amb_p hRinf_amb_le_H hidx
  have hRinfH_of_forall_card_le :
      (∀ L : Subgroup G, IsPGroup p L →
          (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype ≤ L → L ≤ H →
          Nat.card ↥L ≤ Nat.card ↥((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype)) →
        ∃ RinfH : Sylow p ↥H,
          (RinfH : Subgroup ↥H).map H.subtype =
            (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype := by
    intro hmax
    exact hRinfH_of_not_dvd
      (not_dvd_subgroupOf_index_of_forall_card_le
        hRinf_amb_p hRinf_amb_le_H hmax)
  have hRinfH_of_normalizer_le_M :
      Subgroup.normalizer
          (((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) ≤ M →
        ∃ RinfH : Sylow p ↥H,
          (RinfH : Subgroup ↥H).map H.subtype =
            (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype := by
    intro hN_le_M
    exact hRinfH_of_forall_card_le
      (forall_card_le_of_normalizer_sylow_inf_map_le Rinf hN_le_M)
  obtain ⟨LRinf, hLRinf, hNRinf_le_LRinf⟩ :=
    exists_maximalSubgroup_containing_normalizer_of_ne_bot_le_maximal
      hG hM hRinf_amb_ne_bot hRinf_amb_le_M
  have hA_le_LRinf : A.map M.subtype ≤ LRinf :=
    hA_le_NRinf.trans hNRinf_le_LRinf
  have hLRinf_bound : LRinf ≠ M →
      sylowInfCard p LRinf M ≤ Nat.card ↥(Rinf : Subgroup ↥(H ⊓ M)) := by
    intro hLRinf_ne_M
    exact hHmax_Rinf LRinf hLRinf hA_le_LRinf hLRinf_ne_M
  have hNRinf_le_M_or_bound :
      Subgroup.normalizer
          (((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) ≤ M ∨
        sylowInfCard p LRinf M ≤ Nat.card ↥(Rinf : Subgroup ↥(H ⊓ M)) := by
    by_cases hLRinf_eq_M : LRinf = M
    · left
      simpa [hLRinf_eq_M] using hNRinf_le_LRinf
    · right
      exact hLRinf_bound hLRinf_eq_M
  have hRinfH_or_bound :
      (∃ RinfH : Sylow p ↥H,
          (RinfH : Subgroup ↥H).map H.subtype =
            (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) ∨
        sylowInfCard p LRinf M ≤ Nat.card ↥(Rinf : Subgroup ↥(H ⊓ M)) := by
    rcases hNRinf_le_M_or_bound with hN_le_M | hbound
    · left
      exact hRinfH_of_normalizer_le_M hN_le_M
    · right
      exact hbound
  have hRinfH_of_bound :
      sylowInfCard p LRinf M ≤ Nat.card ↥(Rinf : Subgroup ↥(H ⊓ M)) →
        ∃ RinfH : Sylow p ↥H,
          (RinfH : Subgroup ↥H).map H.subtype =
            (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype := by
    intro hbound
    have hRinf_amb_card :
        Nat.card ↥((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) =
          Nat.card ↥(Rinf : Subgroup ↥(H ⊓ M)) :=
      Subgroup.card_map_of_injective (H ⊓ M).subtype_injective
    have hbound_amb :
        sylowInfCard p LRinf M ≤
          Nat.card ↥((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) := by
      calc
        sylowInfCard p LRinf M ≤ Nat.card ↥(Rinf : Subgroup ↥(H ⊓ M)) := hbound
        _ = Nat.card ↥((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) :=
          hRinf_amb_card.symm
    obtain ⟨RM, hRM_map⟩ :=
      exists_sylow_map_eq_of_normalizer_le_and_sylowInfCard_le
        hRinf_amb_p hRinf_amb_le_M hNRinf_le_LRinf hbound_amb
    have hRinf_card_Q :
        Nat.card ↥((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) =
          Nat.card ↥(Q : Subgroup G) := by
      calc
        Nat.card ↥((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype)
            = Nat.card ↥(RM : Subgroup ↥M) := by
              rw [← hRM_map, Subgroup.card_map_of_injective M.subtype_injective]
        _ = Nat.card ↥(P : Subgroup ↥M) := by
              rw [Sylow.card_eq_multiplicity RM, Sylow.card_eq_multiplicity P]
        _ = Nat.card ↥((P : Subgroup ↥M).map M.subtype) := by
              rw [Subgroup.card_map_of_injective M.subtype_injective]
        _ = Nat.card ↥(Q : Subgroup G) := by rw [hQ]
    exact hRinfH_of_forall_card_le fun L hLp _hRL _hLH =>
      card_le_of_isPGroup_of_card_eq_sylow Q hRinf_card_Q hLp
  have hRinfH_exists :
      ∃ RinfH : Sylow p ↥H,
        (RinfH : Subgroup ↥H).map H.subtype =
          (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype := by
    rcases hRinfH_or_bound with hRinfH | hbound
    · exact hRinfH
    · exact hRinfH_of_bound hbound
  obtain ⟨RinfH, hRinfH_map⟩ := hRinfH_exists
  have hZ_RinfH_eq_Rinf :
      (OddOrder.BG.AppB.zCenterLOdd (RinfH : Subgroup ↥H)).map H.subtype =
        (OddOrder.BG.AppB.zCenterLOdd (Rinf : Subgroup ↥(H ⊓ M))).map (H ⊓ M).subtype :=
    zCenterLOdd_map_eq_of_map_eq hRinfH_map
  have hZ_RinfH_ne_bot :
      (OddOrder.BG.AppB.zCenterLOdd (RinfH : Subgroup ↥H)).map H.subtype ≠ ⊥ := by
    intro hZ_map_bot
    exact hZ_Rinf_ne_bot (by rw [← hZ_RinfH_eq_Rinf, hZ_map_bot])
  have hNZ_Rinf_eq_H : Subgroup.normalizer
      (((OddOrder.BG.AppB.zCenterLOdd (Rinf : Subgroup ↥(H ⊓ M))).map
        (H ⊓ M).subtype) : Set G) = H := by
    have hNZ_RinfH_eq_H : Subgroup.normalizer
        (((OddOrder.BG.AppB.zCenterLOdd (RinfH : Subgroup ↥H)).map H.subtype) : Set G) = H :=
      normalizer_zCenterLOdd_map_eq_of_normal_of_ne_bot
        hG hH (hZNormH RinfH) hZ_RinfH_ne_bot
    simpa [hZ_RinfH_eq_Rinf] using hNZ_RinfH_eq_H
  have hNRinf_le_H :
      Subgroup.normalizer
          (((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) ≤ H :=
    hNRinf_le_NZ_Rinf.trans (le_of_eq hNZ_Rinf_eq_H)
  obtain ⟨RM, hRM_map⟩ :=
    exists_sylow_subgroupOf_map_eq_of_not_dvd_index hRinf_amb_p hRinf_amb_le_M
      (not_dvd_subgroupOf_index_of_forall_card_le hRinf_amb_p hRinf_amb_le_M
        (forall_card_le_of_normalizer_sylow_inf_map_le_left Rinf hNRinf_le_H))
  have hM_solvable : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hOpComplMBot : opiCoreInG ({p} : Set ℕ)ᶜ M = ⊥ :=
    opiCoreInG_singleton_compl_eq_bot_of_fittingInG_isPGroup (M := M) hp hFp
  have hZNormM :
      (((OddOrder.BG.AppB.zCenterLOdd (RM : Subgroup ↥M)).map M.subtype).subgroupOf M).Normal :=
    zCenterLOdd_sylow_map_subgroupOf_normal_of_opiCoreInG_singleton_compl_eq_bot
      hG hp_dvd_G RM hM_solvable hOpComplMBot
  have hZ_RM_eq_Rinf :
      (OddOrder.BG.AppB.zCenterLOdd (RM : Subgroup ↥M)).map M.subtype =
        (OddOrder.BG.AppB.zCenterLOdd (Rinf : Subgroup ↥(H ⊓ M))).map (H ⊓ M).subtype :=
    zCenterLOdd_map_eq_of_map_eq hRM_map
  have hZ_RM_ne_bot :
      (OddOrder.BG.AppB.zCenterLOdd (RM : Subgroup ↥M)).map M.subtype ≠ ⊥ := by
    intro hZ_map_bot
    exact hZ_Rinf_ne_bot (by rw [← hZ_RM_eq_Rinf, hZ_map_bot])
  have hNZ_Rinf_eq_M : Subgroup.normalizer
      (((OddOrder.BG.AppB.zCenterLOdd (Rinf : Subgroup ↥(H ⊓ M))).map
        (H ⊓ M).subtype) : Set G) = M := by
    have hNZ_RM_eq_M : Subgroup.normalizer
        (((OddOrder.BG.AppB.zCenterLOdd (RM : Subgroup ↥M)).map M.subtype) : Set G) = M :=
      normalizer_zCenterLOdd_map_eq_of_normal_of_ne_bot hG hM hZNormM hZ_RM_ne_bot
    simpa [hZ_RM_eq_Rinf] using hNZ_RM_eq_M
  exact hH_ne_M (hNZ_Rinf_eq_H.symm.trans hNZ_Rinf_eq_M)

end OddOrder.BG.Ch2.S08


