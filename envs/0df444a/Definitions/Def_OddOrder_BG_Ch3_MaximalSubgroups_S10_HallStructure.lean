-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S10_HallStructure
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S10_HallStructure
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:46:02.63518+00:00
-- url     : https://prove2.me/theorems/fb5d0d6b-0e6f-4218-8dda-8a5855df2756
-- title:
--   BG §10: Theorem 10.2, second half (Hall identification of $M_\sigma$ and $M_\alpha$, $M_\sigma\ne 1$)
-- statement:
--   Continues the formalization of Theorem 10.2 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §10: absorption of $\alpha$-Sylow subgroups, the rank bound for $M/M_\alpha$, the identification of $M_\sigma$ and $M_\alpha$ as Hall subgroups, and the proof that $M_\sigma\ne 1$. It builds on the Core file with the definition layer, Theorem 10.1 and the first half of Theorem 10.2.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 41 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S10_HallStructure.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S10_HallStructure.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S10_HallStructureCore
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Theorem315
import Mathlib.GroupTheory.Nilpotent

namespace OddOrder.BG.Ch3.S10

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BG Theorem 10.6 support, α-Sylow absorption**:
if `M_α` is an `α(M)`-Hall subgroup, then every Sylow `p`-subgroup of `M` with
`p ∈ α(M)` lies in `M_α` when mapped back to `G`. -/
theorem sylow_le_Malpha_of_mem_alpha_of_isHall [Finite G] {M : Subgroup G}
    (hHallα : Ch03.IsHallSubgroup (alpha M) (Malpha M)) {p : ℕ} [Fact p.Prime]
    (hpα : p ∈ alpha M) (P : Sylow p ↥M) :
    ((P : Subgroup ↥M).map M.subtype : Subgroup G) ≤ Malpha M := by
  let Pbar : Subgroup G := (P : Subgroup ↥M).map M.subtype
  have hPbarM : Pbar ≤ M := Subgroup.map_subtype_le _
  have hPbar_pg : IsPGroup p ↥Pbar :=
    P.2.of_equiv (Subgroup.equivMapOfInjective _ _ M.subtype_injective)
  have hPbarα : Ch03.Subgroup.IsPiGroup (alpha M) Pbar := by
    intro r hr
    obtain ⟨n, hn⟩ := hPbar_pg.exists_card_eq
    rw [hn, Nat.mem_primeFactors] at hr
    have hrp : r = p :=
      (Nat.prime_dvd_prime_iff_eq hr.1 Fact.out).mp (hr.1.dvd_of_dvd_pow hr.2.1)
    exact hrp ▸ hpα
  exact alpha_subgroup_le_Malpha_of_isHall hHallα hPbarM hPbarα

/-- **BG Theorem 10.2(d), Fitting rank part** (mmd L2733-2738):
`F(M/M_α)` has rank at most two. For primes in `α(M)` this follows from
`F(M/M_α)` being an `α(M)'`-group; for primes outside `α(M)`, the `α(M)`-core
kernel is a `p'`-group, so quotienting by it does not increase `p`-rank. -/
theorem rank_fitting_quotient_Malpha_le_two [Finite G] (M : Subgroup G) :
    rank ↥(Ch01.fitting (↥M ⧸ (Malpha M).subgroupOf M)) ≤ 2 := by
  let Q : Type _ := ↥M ⧸ (Malpha M).subgroupOf M
  change rank ↥(Ch01.fitting Q) ≤ 2
  rw [rank_le_iff]
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  by_cases hpα : p ∈ alpha M
  · by_contra hpRank
    have h3 : 3 ≤ pRank ↥(Ch01.fitting Q) p := by omega
    have hpos : 0 < pRank ↥(Ch01.fitting Q) p := by omega
    have hpF : p ∈ (Nat.card ↥(Ch01.fitting Q)).primeFactors :=
      OddOrder.BG.Ch2.S09.mem_primeFactors_card_of_pos_pRank
        (H := ↥(Ch01.fitting Q)) (p := p) hpos
    exact fitting_quotient_Malpha_isPiGroup_alphaCompl M p hpF hpα
  · have hN_p' : ¬ p ∣ Nat.card ↥((Malpha M).subgroupOf M) := by
      intro hdiv
      have hpNsub : p ∈ (Nat.card ↥((Malpha M).subgroupOf M)).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdiv, Nat.card_pos.ne'⟩
      have hpN : p ∈ (Nat.card ↥(Malpha M)).primeFactors := by
        rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Malpha_le M)).toEquiv]
        exact hpNsub
      exact hpα (Malpha_isPiGroup M p hpN)
    have hM_rank : pRank ↥M p ≤ 2 := by
      by_contra hpMRank
      have h3 : 3 ≤ pRank ↥M p := by omega
      have hposM : 0 < pRank ↥M p := by omega
      have hpM : p ∈ (Nat.card ↥M).primeFactors :=
        OddOrder.BG.Ch2.S09.mem_primeFactors_card_of_pos_pRank (H := ↥M) (p := p) hposM
      have hpα' : p ∈ alpha M := by
        rw [mem_alpha_iff]
        exact ⟨hpM, h3⟩
      exact hpα hpα'
    have hFQ_pRank : pRank ↥(Ch01.fitting Q) p ≤ pRank Q p :=
      pRank_le_of_injective
        (f := (Ch01.fitting Q).subtype) (Ch01.fitting Q).subtype_injective
    exact hFQ_pRank.trans
      ((Ch1.S04.pRank_quotient_le_of_coprime
        (G := ↥M) (N := (Malpha M).subgroupOf M) hN_p').trans hM_rank)

/-- **BG Theorem 10.2(d), nilpotence entry point** (mmd L2733-2738): the
derived subgroup of `M/M_α` lies in the Fitting subgroup of `M/M_α`. -/
theorem derived_quotient_Malpha_le_fitting [Finite G]
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    commutator (↥M ⧸ (Malpha M).subgroupOf M) ≤
      Ch01.fitting (↥M ⧸ (Malpha M).subgroupOf M) := by
  let Q : Type _ := ↥M ⧸ (Malpha M).subgroupOf M
  change commutator Q ≤ Ch01.fitting Q
  have hFQrank : rank ↥(Ch01.fitting Q) ≤ 2 :=
    rank_fitting_quotient_Malpha_le_two M
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have : Group.IsSolvable Q := inferInstance
  have hoddM : Odd (Nat.card ↥M) := by
    rcases Nat.even_or_odd (Nat.card ↥M) with he | ho
    · exfalso
      have h2 : (2 : ℕ) ∣ Nat.card G := he.two_dvd.trans (Subgroup.card_subgroup_dvd_card M)
      have := hG.odd
      rw [Nat.odd_iff] at this
      omega
    · exact ho
  have hQ_dvd_M : Nat.card Q ∣ Nat.card ↥M := by
    change ((Malpha M).subgroupOf M).index ∣ Nat.card ↥M
    exact Subgroup.index_dvd_card ((Malpha M).subgroupOf M)
  have hoddQ : Odd (Nat.card Q) := by
    rcases Nat.even_or_odd (Nat.card Q) with he | ho
    · exfalso
      have h2 : (2 : ℕ) ∣ Nat.card ↥M := he.two_dvd.trans hQ_dvd_M
      rw [Nat.odd_iff] at hoddM
      omega
    · exact ho
  rcases subsingleton_or_nontrivial Q with hsub | hnontriv
  · intro x _hx
    have hx1 : x = 1 := hsub.elim x 1
    rw [hx1]
    exact (Ch01.fitting Q).one_mem
  · have : Nontrivial Q := hnontriv
    exact OddOrder.BG.Ch1.S05.derived_le_fitting_of_rank_fitting_le_two hoddQ hFQrank

/-- **BG Theorem 10.2(d), `M_σ/M_α` Fitting containment** (mmd L2733-2738):
the image of `M_σ` in `M/M_α` lies in the Fitting subgroup of the quotient. This
combines Step 2 (`M_σ ≤ M'`) with the quotient derived-subgroup containment above. -/
theorem Msigma_quotient_Malpha_le_fitting [Finite G]
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    ((Msigma M).subgroupOf M).map (QuotientGroup.mk' ((Malpha M).subgroupOf M)) ≤
      Ch01.fitting (↥M ⧸ (Malpha M).subgroupOf M) := by
  let N : Subgroup ↥M := (Malpha M).subgroupOf M
  have hMsigma_der : (Msigma M).subgroupOf M ≤ commutator ↥M := by
    intro x hx
    have hxσ : (x : G) ∈ Msigma M := Subgroup.mem_subgroupOf.mp hx
    have hxD : (x : G) ∈ derivedInG M := Msigma_le_derived hG hM hxσ
    rw [derivedInG] at hxD
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxD
    have hxy : y = x := M.subtype_injective hyx
    rwa [← hxy]
  calc
    ((Msigma M).subgroupOf M).map (QuotientGroup.mk' N) ≤
        (commutator ↥M).map (QuotientGroup.mk' N) := Subgroup.map_mono hMsigma_der
    _ = commutator (↥M ⧸ N) := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N),
        _root_.commutator_def]
    _ ≤ Ch01.fitting (↥M ⧸ N) :=
      derived_quotient_Malpha_le_fitting hG hM

/-- **BG Theorem 10.2(d), Hall-`σ` quotient Fitting containment**:
any Hall `σ(M)`-subgroup of `M` has image in `F(M/M_α)`. This is the
Hall-subgroup version of `Msigma_quotient_Malpha_le_fitting`, using the focal
subgroup step `hallSigmaSubgroup_le_derived`. -/
theorem hallSigmaSubgroup_quotient_Malpha_le_fitting [Finite G]
    (hG : IsMinimalSimpleOdd G) {M S : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hSM : S ≤ M)
    (hHallσ : Ch03.IsHallSubgroup (sigma M) (S.subgroupOf M)) :
    (S.subgroupOf M).map (QuotientGroup.mk' ((Malpha M).subgroupOf M)) ≤
      Ch01.fitting (↥M ⧸ (Malpha M).subgroupOf M) := by
  let N : Subgroup ↥M := (Malpha M).subgroupOf M
  have hS_der : S.subgroupOf M ≤ commutator ↥M := by
    intro x hx
    have hxS : (x : G) ∈ S := Subgroup.mem_subgroupOf.mp hx
    have hxD : (x : G) ∈ derivedInG M :=
      hallSigmaSubgroup_le_derived hG hM hSM hHallσ hxS
    rw [derivedInG] at hxD
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxD
    have hxy : y = x := M.subtype_injective hyx
    rwa [← hxy]
  calc
    (S.subgroupOf M).map (QuotientGroup.mk' N) ≤
        (commutator ↥M).map (QuotientGroup.mk' N) := Subgroup.map_mono hS_der
    _ = commutator (↥M ⧸ N) := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N),
        _root_.commutator_def]
    _ ≤ Ch01.fitting (↥M ⧸ N) :=
      derived_quotient_Malpha_le_fitting hG hM

/-- **BG Theorem 10.2(d), Hall-`σ` quotient is an `α(M)'`-group**:
the image of any Hall `σ(M)`-subgroup of `M` lies in `F(M/M_α)`, and that
Fitting subgroup is an `α(M)'`-group. -/
theorem hallSigmaSubgroup_quotient_Malpha_isPiGroup_alphaCompl [Finite G]
    (hG : IsMinimalSimpleOdd G) {M S : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hSM : S ≤ M)
    (hHallσ : Ch03.IsHallSubgroup (sigma M) (S.subgroupOf M)) :
    Ch03.Subgroup.IsPiGroup (alpha M)ᶜ
      ((S.subgroupOf M).map (QuotientGroup.mk' ((Malpha M).subgroupOf M))) :=
  Ch03.Subgroup.IsPiGroup.le
    (hallSigmaSubgroup_quotient_Malpha_le_fitting hG hM hSM hHallσ)
    (fitting_quotient_Malpha_isPiGroup_alphaCompl M)

/-- **BG Theorem 10.2(b), Hall-`σ` quotient**:
the image of a Hall `σ(M)`-subgroup of `M` in `M/M_α` is again Hall
`σ(M)`. -/
theorem hallSigmaSubgroup_quotient_Malpha_isHall [Finite G] {M S : Subgroup G}
    (hHallσ : Ch03.IsHallSubgroup (sigma M) (S.subgroupOf M)) :
    Ch03.IsHallSubgroup (sigma M)
      ((S.subgroupOf M).map (QuotientGroup.mk' ((Malpha M).subgroupOf M))) :=
  Ch03.IsHallSubgroup.map_quotient (N := (Malpha M).subgroupOf M) hHallσ

/-- **BG Theorem 10.2(b), Hall-`σ` inside the quotient Fitting subgroup**:
if `S` is a Hall `σ(M)`-subgroup of `M`, then its image is not only contained
in `F(M/M_α)`, but remains Hall `σ(M)` after viewing it as a subgroup of that
Fitting subgroup. This packages the quotient Hall step with the BG
`M'/M_α ≤ F(M/M_α)` argument. -/
theorem hallSigmaSubgroup_quotient_Malpha_isHall_in_fitting [Finite G]
    (hG : IsMinimalSimpleOdd G) {M S : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hSM : S ≤ M)
    (hHallσ : Ch03.IsHallSubgroup (sigma M) (S.subgroupOf M)) :
    Ch03.IsHallSubgroup (sigma M)
      (((S.subgroupOf M).map (QuotientGroup.mk' ((Malpha M).subgroupOf M))).subgroupOf
        (Ch01.fitting (↥M ⧸ (Malpha M).subgroupOf M))) := by
  let N : Subgroup ↥M := (Malpha M).subgroupOf M
  let Q : Type _ := ↥M ⧸ N
  let q : ↥M →* Q := QuotientGroup.mk' N
  let Hbar : Subgroup Q := (S.subgroupOf M).map q
  let F : Subgroup Q := Ch01.fitting Q
  have hHbarF : Hbar ≤ F := by
    exact hallSigmaSubgroup_quotient_Malpha_le_fitting hG hM hSM hHallσ
  have hHbarHall : Ch03.IsHallSubgroup (sigma M) Hbar := by
    exact hallSigmaSubgroup_quotient_Malpha_isHall hHallσ
  refine ⟨?_, ?_⟩
  · intro p hp
    have hpHbar : p ∈ (Nat.card ↥Hbar).primeFactors := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHbarF).toEquiv] at hp
    exact hHbarHall.1 p hpHbar
  · intro p hpidx hpσ
    have hidx : (Hbar.subgroupOf F).index ∣ Hbar.index := by
      have htower : (Hbar.subgroupOf F).index * F.index = Hbar.index :=
        Subgroup.relIndex_mul_index hHbarF
      exact ⟨F.index, htower.symm⟩
    exact hHbarHall.2 p
      (Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primeFactors.mp hpidx).1,
          dvd_trans (Nat.mem_primeFactors.mp hpidx).2.1 hidx,
          Subgroup.index_ne_zero_of_finite⟩) hpσ

/-- **Nilpotent `π`/`π'` core decomposition**:
in a finite nilpotent group, `O_π(K)` together with `O_{π'}(K)` generates all
of `K`. This is the arbitrary-`π` version of the singleton decomposition used
in BG Lemma 9.5. -/
theorem top_le_oPiCore_sup_compl_of_isNilpotent
    {K : Type*} [Group K] [Finite K] [Group.IsNilpotent K] (π : Set ℕ) :
    (⊤ : Subgroup K) ≤ Ch03.oPiCore π K ⊔ Ch03.oPiCore {p | p ∉ π} K := by
  classical
  have hfit : Ch01.fitting K = ⊤ := by
    refine top_le_iff.mp ?_
    have : Group.IsNilpotent ↥(⊤ : Subgroup K) := Group.isNilpotent_top.mpr inferInstance
    exact Ch01.nilpotent_normal_le_fitting
  rw [← hfit, Ch01.fitting_eq_iSup_primeFactors]
  refine iSup_le fun q => ?_
  obtain ⟨qval, hq_mem⟩ := q
  have : Fact qval.Prime := ⟨(Nat.mem_primeFactors.mp hq_mem).1⟩
  rw [show Ch01.opCore qval K = Ch03.oPiCore ({qval} : Set ℕ) K from
    (OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := K) qval).symm]
  by_cases hqπ : qval ∈ π
  · exact le_sup_of_le_left
      (Ch03.oPiCore_mono (Set.singleton_subset_iff.mpr hqπ) K)
  · exact le_sup_of_le_right
      (Ch03.oPiCore_mono (Set.singleton_subset_iff.mpr hqπ) K)

/-- **Nilpotent Hall core**:
in a finite nilpotent group, `O_π(K)` is a `π`-Hall subgroup. -/
theorem oPiCore_isHall_of_isNilpotent
    {K : Type*} [Group K] [Finite K] [Group.IsNilpotent K] (π : Set ℕ) :
    Ch03.IsHallSubgroup π (Ch03.oPiCore π K) := by
  let Oπ : Subgroup K := Ch03.oPiCore π K
  let Oπc : Subgroup K := Ch03.oPiCore {p | p ∉ π} K
  refine ⟨Ch03.oPiCore.isPiGroup π, ?_⟩
  intro p hpidx hpπ
  have hsup : Oπ ⊔ Oπc = ⊤ := by
    exact top_le_iff.mp (top_le_oPiCore_sup_compl_of_isNilpotent (K := K) π)
  have hdisj : Oπ ⊓ Oπc = ⊥ := by
    exact Ch03.oPiCore.coprime_inf π
  have hcard_sup : Nat.card ↥(Oπ ⊔ Oπc : Subgroup K) =
      Nat.card ↥Oπ * Nat.card ↥Oπc :=
    OddOrder.BG.Ch1.S01.card_sup_eq_card_mul_card_of_disjoint_normal
      (T := Oπ) (M := Oπc) hdisj
  have hcardK : Nat.card K = Nat.card ↥(Oπ ⊔ Oπc : Subgroup K) := by
    rw [hsup, Subgroup.card_top]
  have hidx_eq : Oπ.index = Nat.card ↥Oπc := by
    have hmul : Nat.card ↥Oπ * Oπ.index = Nat.card ↥Oπ * Nat.card ↥Oπc := by
      calc
        Nat.card ↥Oπ * Oπ.index = Nat.card K := Subgroup.card_mul_index Oπ
        _ = Nat.card ↥(Oπ ⊔ Oπc : Subgroup K) := hcardK
        _ = Nat.card ↥Oπ * Nat.card ↥Oπc := hcard_sup
    exact Nat.mul_left_cancel Nat.card_pos hmul
  have hpOπc : p ∈ (Nat.card ↥Oπc).primeFactors := by
    rwa [hidx_eq] at hpidx
  exact (Ch03.oPiCore.isPiGroup {q | q ∉ π} p hpOπc) hpπ

/-- **BG Theorem 10.2(b), Hall-`σ` quotient as the Fitting `σ`-core**:
inside the nilpotent group `F(M/M_α)`, the image of any Hall `σ(M)`-subgroup
is exactly `O_{σ(M)}(F(M/M_α))`. -/
theorem hallSigmaSubgroup_quotient_Malpha_eq_oPiCore_in_fitting [Finite G]
    (hG : IsMinimalSimpleOdd G) {M S : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hSM : S ≤ M)
    (hHallσ : Ch03.IsHallSubgroup (sigma M) (S.subgroupOf M)) :
    let N : Subgroup ↥M := (Malpha M).subgroupOf M
    let q : ↥M →* ↥M ⧸ N := QuotientGroup.mk' N
    let Hbar : Subgroup (↥M ⧸ N) := (S.subgroupOf M).map q
    let F : Subgroup (↥M ⧸ N) := Ch01.fitting (↥M ⧸ N)
    Hbar.subgroupOf F = Ch03.oPiCore (sigma M) ↥F := by
  let N : Subgroup ↥M := (Malpha M).subgroupOf M
  let q : ↥M →* ↥M ⧸ N := QuotientGroup.mk' N
  let Hbar : Subgroup (↥M ⧸ N) := (S.subgroupOf M).map q
  let F : Subgroup (↥M ⧸ N) := Ch01.fitting (↥M ⧸ N)
  have hHallF : Ch03.IsHallSubgroup (sigma M) (Hbar.subgroupOf F) :=
    hallSigmaSubgroup_quotient_Malpha_isHall_in_fitting hG hM hSM hHallσ
  have hCoreHall : Ch03.IsHallSubgroup (sigma M) (Ch03.oPiCore (sigma M) ↥F) :=
    oPiCore_isHall_of_isNilpotent (K := ↥F) (sigma M)
  have hCore_le_H : Ch03.oPiCore (sigma M) ↥F ≤ Hbar.subgroupOf F :=
    Ch03.Subgroup.IsPiGroup.normal_le_hall (Ch03.oPiCore.isPiGroup (sigma M)) hHallF
  have hH_le_Core : Hbar.subgroupOf F ≤ Ch03.oPiCore (sigma M) ↥F :=
    isPiGroup_le_of_normal_isHallSubgroup hCoreHall hHallF.1
  exact le_antisymm hH_le_Core hCore_le_H

/-- **BG Theorem 10.2(b), Hall-`σ` quotient lies in the quotient `σ`-core**:
the image of any Hall `σ(M)`-subgroup of `M` in `M/M_α` is contained in
`O_{σ(M)}(M/M_α)`. The key point is that the image is the `σ`-core of the
nilpotent Fitting subgroup, and that core is characteristic in the normal
Fitting subgroup. -/
theorem hallSigmaSubgroup_quotient_Malpha_le_oPiCore_quotient [Finite G]
    (hG : IsMinimalSimpleOdd G) {M S : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hSM : S ≤ M)
    (hHallσ : Ch03.IsHallSubgroup (sigma M) (S.subgroupOf M)) :
    (S.subgroupOf M).map (QuotientGroup.mk' ((Malpha M).subgroupOf M)) ≤
      Ch03.oPiCore (sigma M) (↥M ⧸ (Malpha M).subgroupOf M) := by
  let N : Subgroup ↥M := (Malpha M).subgroupOf M
  let Q : Type _ := ↥M ⧸ N
  let q : ↥M →* Q := QuotientGroup.mk' N
  let Hbar : Subgroup Q := (S.subgroupOf M).map q
  let F : Subgroup Q := Ch01.fitting Q
  have hHbarF : Hbar ≤ F := by
    exact hallSigmaSubgroup_quotient_Malpha_le_fitting hG hM hSM hHallσ
  have hEq : Hbar.subgroupOf F = Ch03.oPiCore (sigma M) ↥F := by
    simpa [N, Q, q, Hbar, F] using
      hallSigmaSubgroup_quotient_Malpha_eq_oPiCore_in_fitting hG hM hSM hHallσ
  have hCoreMap_le : (Ch03.oPiCore (sigma M) ↥F).map F.subtype ≤
      Ch03.oPiCore (sigma M) Q := by
    have hCoreMapPi : Ch03.Subgroup.IsPiGroup (sigma M)
        ((Ch03.oPiCore (sigma M) ↥F).map F.subtype) := by
      intro p hp
      exact (Ch03.oPiCore.isPiGroup (sigma M)) p
        (Nat.primeFactors_mono
          (Subgroup.card_map_dvd (Ch03.oPiCore (sigma M) ↥F) F.subtype)
          Nat.card_pos.ne' hp)
    exact Ch03.Subgroup.IsPiGroup.le_oPiCore hCoreMapPi
  intro x hx
  have hxF : x ∈ F := hHbarF hx
  have hxSub : (⟨x, hxF⟩ : ↥F) ∈ Hbar.subgroupOf F :=
    Subgroup.mem_subgroupOf.mpr hx
  have hxCoreF : (⟨x, hxF⟩ : ↥F) ∈ Ch03.oPiCore (sigma M) ↥F := by
    rwa [hEq] at hxSub
  have hxMap : x ∈ (Ch03.oPiCore (sigma M) ↥F).map F.subtype := by
    exact ⟨⟨x, hxF⟩, hxCoreF, rfl⟩
  exact hCoreMap_le hxMap

/-- **Quotient `π`-core preimage**:
if `N ≤ O_π(K)`, then the preimage of `O_π(K/N)` is still contained in
`O_π(K)`. The proof is the standard extension argument: the preimage has
π-group quotient over `N`, and `N` itself is a π-group. -/
theorem oPiCore_quotient_comap_le_oPiCore_of_le
    {K : Type*} [Group K] [Finite K] {π : Set ℕ} {N : Subgroup K} [N.Normal]
    (hNle : N ≤ Ch03.oPiCore π K) :
    (Ch03.oPiCore π (K ⧸ N)).comap (QuotientGroup.mk' N) ≤ Ch03.oPiCore π K := by
  let q : K →* K ⧸ N := QuotientGroup.mk' N
  let Kbar : Subgroup (K ⧸ N) := Ch03.oPiCore π (K ⧸ N)
  let L : Subgroup K := Kbar.comap q
  have hN_le_L : N ≤ L := by
    intro x hx
    change q x ∈ Kbar
    rw [show q x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact Kbar.one_mem
  have hL_map : L.map q = Kbar := by
    dsimp [L, q, Kbar]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) Kbar
  have hLmap_pi : Ch03.Subgroup.IsPiGroup π (L.map q) := by
    rw [hL_map]
    exact Ch03.oPiCore.isPiGroup π
  have hN_pi : Ch03.Subgroup.IsPiGroup π N :=
    Ch03.Subgroup.IsPiGroup.le hNle (Ch03.oPiCore.isPiGroup π)
  have hNsub_pi : Ch03.Subgroup.IsPiGroup π (N.subgroupOf L) :=
    Ch03.Subgroup.IsPiGroup.subgroupOf hN_le_L hN_pi
  have hLquot_pi : ∀ p ∈ (Nat.card (↥L ⧸ N.subgroupOf L)).primeFactors, p ∈ π :=
    Ch03.Subgroup.IsPiGroup.primeFactors_quotient_subgroupOf hLmap_pi
  have hL_pi : Ch03.Subgroup.IsPiGroup π L :=
    Ch03.IsPiGroup.of_normal_quotient (N.subgroupOf L) hNsub_pi hLquot_pi
  exact hL_pi.le_oPiCore

/-- **BG Theorem 10.2(b), Hall-`σ` subgroup absorbed by `M_σ`, internal form**:
any Hall `σ(M)`-subgroup of `M`, viewed internally in `M`, lies in the local
`σ`-core `M_σ`. -/
theorem hallSigmaSubgroup_subgroupOf_le_Msigma_subgroupOf [Finite G]
    (hG : IsMinimalSimpleOdd G) {M S : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hSM : S ≤ M)
    (hHallσ : Ch03.IsHallSubgroup (sigma M) (S.subgroupOf M)) :
    S.subgroupOf M ≤ (Msigma M).subgroupOf M := by
  let N : Subgroup ↥M := (Malpha M).subgroupOf M
  let q : ↥M →* ↥M ⧸ N := QuotientGroup.mk' N
  have hSbar : (S.subgroupOf M).map q ≤ Ch03.oPiCore (sigma M) (↥M ⧸ N) := by
    exact hallSigmaSubgroup_quotient_Malpha_le_oPiCore_quotient hG hM hSM hHallσ
  have hNle : N ≤ Ch03.oPiCore (sigma M) ↥M := by
    rw [← Msigma_subgroupOf M]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      (Malpha_le_Msigma hG hM (Subgroup.mem_subgroupOf.mp hx))
  have hpre : (Ch03.oPiCore (sigma M) (↥M ⧸ N)).comap q ≤
      Ch03.oPiCore (sigma M) ↥M :=
    oPiCore_quotient_comap_le_oPiCore_of_le (π := sigma M) (N := N) hNle
  intro x hx
  rw [Msigma_subgroupOf M]
  apply hpre
  change q x ∈ Ch03.oPiCore (sigma M) (↥M ⧸ N)
  exact hSbar ⟨x, hx, rfl⟩

/-- **BG Theorem 10.2(b), Hall-`σ` subgroup absorbed by `M_σ`, ambient form**:
any Hall `σ(M)`-subgroup of `M`, viewed as a subgroup of `G`, lies in `M_σ`. -/
theorem hallSigmaSubgroup_le_Msigma [Finite G]
    (hG : IsMinimalSimpleOdd G) {M S : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hSM : S ≤ M)
    (hHallσ : Ch03.IsHallSubgroup (sigma M) (S.subgroupOf M)) :
    S ≤ Msigma M := by
  have hsub : S.subgroupOf M ≤ (Msigma M).subgroupOf M :=
    hallSigmaSubgroup_subgroupOf_le_Msigma_subgroupOf hG hM hSM hHallσ
  intro x hx
  have hxM : x ∈ M := hSM hx
  have hxSub : (⟨x, hxM⟩ : ↥M) ∈ S.subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr hx
  exact Subgroup.mem_subgroupOf.mp (hsub hxSub)

/-- **BG Theorem 10.2(b), `M_σ` lies in every Hall-`σ` subgroup, internal form**:
the normal local `σ(M)`-core is contained in any Hall `σ(M)`-subgroup of `M`. -/
theorem Msigma_subgroupOf_le_hallSigmaSubgroup [Finite G] {M S : Subgroup G}
    (hHallσ : Ch03.IsHallSubgroup (sigma M) (S.subgroupOf M)) :
    (Msigma M).subgroupOf M ≤ S.subgroupOf M := by
  have : ((Msigma M).subgroupOf M).Normal := by
    rw [Msigma_subgroupOf]
    infer_instance
  have hMsigmaσ : Ch03.Subgroup.IsPiGroup (sigma M) ((Msigma M).subgroupOf M) := by
    rw [Msigma_subgroupOf]
    exact Ch03.oPiCore.isPiGroup (sigma M)
  exact Ch03.Subgroup.IsPiGroup.normal_le_hall hMsigmaσ hHallσ

/-- **BG Theorem 10.2(b), `M_σ` lies in every Hall-`σ` subgroup, ambient form**. -/
theorem Msigma_le_hallSigmaSubgroup [Finite G] {M S : Subgroup G}
    (hHallσ : Ch03.IsHallSubgroup (sigma M) (S.subgroupOf M)) :
    Msigma M ≤ S := by
  have hsub : (Msigma M).subgroupOf M ≤ S.subgroupOf M :=
    Msigma_subgroupOf_le_hallSigmaSubgroup hHallσ
  intro x hx
  have hxM : x ∈ M := Msigma_le M hx
  have hxSub : (⟨x, hxM⟩ : ↥M) ∈ (Msigma M).subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr hx
  exact Subgroup.mem_subgroupOf.mp (hsub hxSub)

/-- **BG Theorem 10.2(b), Hall-`σ` subgroup identification**:
any Hall `σ(M)`-subgroup of `M`, viewed in `G`, is exactly `M_σ`. -/
theorem hallSigmaSubgroup_eq_Msigma [Finite G]
    (hG : IsMinimalSimpleOdd G) {M S : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hSM : S ≤ M)
    (hHallσ : Ch03.IsHallSubgroup (sigma M) (S.subgroupOf M)) :
    S = Msigma M :=
  le_antisymm (hallSigmaSubgroup_le_Msigma hG hM hSM hHallσ)
    (Msigma_le_hallSigmaSubgroup hHallσ)

/-- **BG Theorem 10.2(b), local Hall property of `M_σ`**:
inside `M`, the local `σ`-core `M_σ` is a Hall `σ(M)`-subgroup. -/
theorem Msigma_subgroupOf_isHall [Finite G]
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    Ch03.IsHallSubgroup (sigma M) ((Msigma M).subgroupOf M) := by
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  obtain ⟨H, hH⟩ := Ch03.hall_E_exists (G := ↥M) (sigma M)
  set S : Subgroup G := H.map M.subtype with hSdef
  have hSM : S ≤ M := by
    rw [hSdef]
    exact Subgroup.map_subtype_le H
  have hS_sub : S.subgroupOf M = H := by
    rw [hSdef, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  have hHallS : Ch03.IsHallSubgroup (sigma M) (S.subgroupOf M) := by
    rwa [hS_sub]
  have hEq : S = Msigma M := hallSigmaSubgroup_eq_Msigma hG hM hSM hHallS
  rwa [← hEq]

/-- **BG Theorem 10.2(b), ambient Hall property of `M_σ`**:
`M_σ` is a Hall `σ(M)`-subgroup of `G`. The internal Hall property supplies the
`M`-index part, and `σ(M)` itself rules out primes in `[G:M]`. -/
theorem Msigma_isHall [Finite G]
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    Ch03.IsHallSubgroup (sigma M) (Msigma M) := by
  refine ⟨Msigma_isPiGroup M, ?_⟩
  intro p hpidx hpσ
  have hp_prime : p.Prime := (Nat.mem_primeFactors.mp hpidx).1
  have : Fact p.Prime := ⟨hp_prime⟩
  have hrel : ((Msigma M).subgroupOf M).index * M.index = (Msigma M).index :=
    Subgroup.relIndex_mul_index (Msigma_le M)
  have hp_dvd_prod : p ∣ ((Msigma M).subgroupOf M).index * M.index := by
    rw [hrel]
    exact (Nat.mem_primeFactors.mp hpidx).2.1
  rcases hp_prime.dvd_mul.mp hp_dvd_prod with hp_internal | hp_M
  · have hHallLocal : Ch03.IsHallSubgroup (sigma M) ((Msigma M).subgroupOf M) :=
      Msigma_subgroupOf_isHall hG hM
    exact hHallLocal.2 p
      (Nat.mem_primeFactors.mpr
        ⟨hp_prime, hp_internal, Subgroup.index_ne_zero_of_finite⟩) hpσ
  · exact not_dvd_index_of_mem_sigma hpσ hp_M

/-- **BG Theorem 10.2(d), Hall-`σ` kills `α` in the quotient**:
if an `α(M)`-subgroup of `M` lies in a Hall `σ(M)`-subgroup, then its image in
`M/M_α` is simultaneously an `α(M)`-group and an `α(M)'`-group, hence trivial.
Equivalently the subgroup already lies in `M_α`. -/
theorem alphaSubgroup_le_Malpha_of_le_hallSigmaSubgroup [Finite G]
    (hG : IsMinimalSimpleOdd G) {M S A : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hSM : S ≤ M)
    (hHallσ : Ch03.IsHallSubgroup (sigma M) (S.subgroupOf M))
    (hAS : A ≤ S) (hAα : Ch03.Subgroup.IsPiGroup (alpha M) A) :
    A ≤ Malpha M := by
  let N : Subgroup ↥M := (Malpha M).subgroupOf M
  let q : ↥M →* ↥M ⧸ N := QuotientGroup.mk' N
  have hAM : A ≤ M := hAS.trans hSM
  have hAS_sub : A.subgroupOf M ≤ S.subgroupOf M := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hAS (Subgroup.mem_subgroupOf.mp hx))
  have hAbar_le_Sbar :
      (A.subgroupOf M).map q ≤ (S.subgroupOf M).map q :=
    Subgroup.map_mono hAS_sub
  have hSbarαc : Ch03.Subgroup.IsPiGroup (alpha M)ᶜ ((S.subgroupOf M).map q) :=
    hallSigmaSubgroup_quotient_Malpha_isPiGroup_alphaCompl hG hM hSM hHallσ
  have hAbarαc : Ch03.Subgroup.IsPiGroup (alpha M)ᶜ ((A.subgroupOf M).map q) :=
    Ch03.Subgroup.IsPiGroup.le hAbar_le_Sbar hSbarαc
  have hAbarα : Ch03.Subgroup.IsPiGroup (alpha M) ((A.subgroupOf M).map q) := by
    intro r hr
    have hrAsub : r ∈ (Nat.card ↥(A.subgroupOf M)).primeFactors :=
      Nat.primeFactors_mono (Subgroup.card_map_dvd (A.subgroupOf M) q)
        Nat.card_pos.ne' hr
    have hrA : r ∈ (Nat.card ↥A).primeFactors := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv] at hrAsub
    exact hAα r hrA
  have hAbar_bot : (A.subgroupOf M).map q = ⊥ := by
    apply Subgroup.card_eq_one.mp
    have hEmpty : (Nat.card ↥((A.subgroupOf M).map q)).primeFactors = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      have hr_not_alpha : r ∉ alpha M := by
        simpa using hAbarαc r hr
      exact hr_not_alpha (hAbarα r hr)
    rcases Nat.primeFactors_eq_empty.mp hEmpty with hzero | hone
    · exact False.elim (Nat.card_pos.ne' hzero)
    · exact hone
  have hA_le_N : A.subgroupOf M ≤ N := by
    have hleKer : A.subgroupOf M ≤ q.ker :=
      (Subgroup.map_eq_bot_iff (A.subgroupOf M)).mp hAbar_bot
    simpa [q, QuotientGroup.ker_mk'] using hleKer
  intro x hx
  have hxM : x ∈ M := hAM hx
  have hxAsub : (⟨x, hxM⟩ : ↥M) ∈ A.subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr hx
  exact Subgroup.mem_subgroupOf.mp (hA_le_N hxAsub)

/-- **BG Theorem 10.2(d), Hall-`σ` contains `α`-subgroups**:
every `α(M)`-subgroup of `M` is contained in a Hall `σ(M)`-subgroup of `M`.
This is Hall-D (BG Prop. 1.5(b)) with the trivial operator group, plus
`α(M) ⊆ σ(M)`. -/
theorem exists_hallSigmaSubgroup_containing_alphaSubgroup [Finite G]
    (hG : IsMinimalSimpleOdd G) {M A : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hAM : A ≤ M) (hAα : Ch03.Subgroup.IsPiGroup (alpha M) A) :
    ∃ S : Subgroup G,
      S ≤ M ∧ Ch03.IsHallSubgroup (sigma M) (S.subgroupOf M) ∧ A ≤ S := by
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  let φ : Unit →* MulAut ↥M := 1
  have hA_sub_σ : Ch03.Subgroup.IsPiGroup (sigma M) (A.subgroupOf M) := by
    intro p hp
    have hpA : p ∈ (Nat.card ↥A).primeFactors := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv] at hp
    exact alpha_subset_sigma hG hM (hAα p hpA)
  have hA_sub_inv : Ch03.IsAInvariant φ (A.subgroupOf M) := by
    rw [Ch03.isAInvariant_iff_smul_mem]
    intro _ x hx
    simpa [φ] using hx
  have hCop : Nat.Coprime (Nat.card Unit) (Nat.card ↥M) := by
    simp
  obtain ⟨H, hH_hall, _hH_inv, hA_le_H⟩ :=
    OddOrder.BG.Ch1.S01.aInvariant_piSubgroup_le_aInvariant_hall
      (G := ↥M) (A := Unit) (φ := φ) hCop hA_sub_σ hA_sub_inv
  let S : Subgroup G := H.map M.subtype
  have hSM : S ≤ M := by
    exact Subgroup.map_subtype_le H
  refine ⟨S, hSM, ?_, ?_⟩
  · have hS_sub : S.subgroupOf M = H := by
      rw [show S = H.map M.subtype from rfl, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    rwa [hS_sub]
  · intro x hx
    have hxM : x ∈ M := hAM hx
    have hxA_sub : (⟨x, hxM⟩ : ↥M) ∈ A.subgroupOf M :=
      Subgroup.mem_subgroupOf.mpr hx
    rw [show S = H.map M.subtype from rfl, Subgroup.mem_map]
    exact ⟨⟨x, hxM⟩, hA_le_H hxA_sub, rfl⟩

/-- **BG Theorem 10.2(a), Hall-`α` subgroup collapses to `M_α`**:
an `α(M)`-Hall subgroup of `M`, viewed in `G`, is contained in `M_α`.
Choose a Hall `σ(M)`-subgroup containing it and apply the quotient
`α/α'`-triviality step above. -/
theorem hallAlphaSubgroup_le_Malpha [Finite G]
    (hG : IsMinimalSimpleOdd G) {M A : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hAM : A ≤ M)
    (hHallα : Ch03.IsHallSubgroup (alpha M) (A.subgroupOf M)) :
    A ≤ Malpha M := by
  have hAα : Ch03.Subgroup.IsPiGroup (alpha M) A := by
    intro p hp
    have hpSub : p ∈ (Nat.card ↥(A.subgroupOf M)).primeFactors := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv]
    exact hHallα.1 p hpSub
  obtain ⟨S, hSM, hHallσ, hAS⟩ :=
    exists_hallSigmaSubgroup_containing_alphaSubgroup hG hM hAM hAα
  exact alphaSubgroup_le_Malpha_of_le_hallSigmaSubgroup hG hM hSM hHallσ hAS hAα

/-- **BG Theorem 10.2(a)**: `M_α` is an `α(M)`-Hall subgroup of `G`.
Hall-E gives a local Hall `α(M)`-subgroup `A` of `M`; the previous theorem puts
`A ≤ M_α`, and the index of `M_α` then divides the index of the `G`-Hall subgroup `A`. -/
theorem Malpha_isHall [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    Ch03.IsHallSubgroup (alpha M) (Malpha M) := by
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  obtain ⟨H, hH⟩ := Ch03.hall_E_exists (G := ↥M) (alpha M)
  set A : Subgroup G := H.map M.subtype with hAdef
  have hAM : A ≤ M := by
    rw [hAdef]
    exact Subgroup.map_subtype_le H
  have hA_sub : A.subgroupOf M = H := by
    rw [hAdef, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  have hHallA_sub : Ch03.IsHallSubgroup (alpha M) (A.subgroupOf M) := by
    rwa [hA_sub]
  have hHallA_G : Ch03.IsHallSubgroup (alpha M) A :=
    hallAlphaSubgroup_isHallInG hG hM hAM hHallA_sub
  have hA_le_Mα : A ≤ Malpha M :=
    hallAlphaSubgroup_le_Malpha hG hM hAM hHallA_sub
  refine ⟨Malpha_isPiGroup M, ?_⟩
  intro p hpidx hpα
  apply hHallA_G.2 p ?_ hpα
  exact Nat.primeFactors_mono (Subgroup.index_dvd_of_le hA_le_Mα)
    Subgroup.index_ne_zero_of_finite hpidx

/-- Singleton cores for primes in `σ(M)` lie in `M_σ`. This is the local bridge used in
the hard `M_α = 1` branch of BG Theorem 10.2(e): once the low-rank argument produces a
nontrivial `O_q(M)` with `q ∈ σ(M)`, this inclusion turns it into `M_σ ≠ 1`. -/
theorem opiCoreInG_singleton_le_Msigma_of_mem_sigma {M : Subgroup G} {q : ℕ}
    (hq : q ∈ sigma M) :
    opiCoreInG ({q} : Set ℕ) M ≤ Msigma M := by
  rw [Msigma, opiCoreInG, opiCoreInG]
  exact Subgroup.map_mono (Ch03.oPiCore_mono (by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    rwa [hr]) ↥M)

/-- If a singleton core `O_q(M)` is nontrivial for some `q ∈ σ(M)`, then `M_σ` is
nontrivial. This isolates the final algebraic step needed after the low-rank/Thm 4.20
argument in the hard branch of BG Theorem 10.2(e). -/
theorem Msigma_ne_bot_of_opiCoreInG_singleton_ne_bot_of_mem_sigma {M : Subgroup G} {q : ℕ}
    (hq : q ∈ sigma M) (hOq : opiCoreInG ({q} : Set ℕ) M ≠ ⊥) :
    Msigma M ≠ ⊥ := by
  intro hσ
  exact hOq (le_bot_iff.mp (by
    simpa [hσ] using opiCoreInG_singleton_le_Msigma_of_mem_sigma (M := M) hq))

/-- If a Sylow `q`-subgroup of `M` maps onto the singleton core `O_q(M)` and the
ambient normalizer of that core lies in `M`, then `q ∈ σ(M)`. This packages the exact
output expected from the low-rank/Thm 4.20 branch of BG Theorem 10.2(e). -/
theorem mem_sigma_of_sylowMap_eq_opiCoreInG_singleton {M : Subgroup G} {q : ℕ}
    (hqM : q ∈ (Nat.card ↥M).primeFactors) (P : Sylow q ↥M)
    (hP : (P : Subgroup ↥M).map M.subtype = opiCoreInG ({q} : Set ℕ) M)
    (hN : Subgroup.normalizer (opiCoreInG ({q} : Set ℕ) M : Set G) ≤ M) :
    q ∈ sigma M := by
  rw [mem_sigma_iff]
  refine ⟨hqM, P, ?_⟩
  simpa [hP] using hN

/-- A singleton core that is the ambient image of a Sylow subgroup for a prime divisor of
`|M|` is nontrivial. -/
theorem opiCoreInG_singleton_ne_bot_of_sylowMap_eq [Finite G] {M : Subgroup G} {q : ℕ}
    (hqM : q ∈ (Nat.card ↥M).primeFactors) (P : Sylow q ↥M)
    (hP : (P : Subgroup ↥M).map M.subtype = opiCoreInG ({q} : Set ℕ) M) :
    opiCoreInG ({q} : Set ℕ) M ≠ ⊥ := by
  have : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hqM⟩
  have hP_ne : (P : Subgroup ↥M) ≠ ⊥ :=
    OddOrder.Isaacs.Ch07.Sylow.ne_bot_of_dvd_card (Nat.dvd_of_mem_primeFactors hqM) P
  intro hOq
  have hPmap_bot : (P : Subgroup ↥M).map M.subtype = ⊥ := by
    rw [hP, hOq]
  exact hP_ne ((Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp hPmap_bot)

/-- Hard-branch support for BG Theorem 10.2(e): once the low-rank argument shows that
`O_q(M)` is the image of a Sylow `q`-subgroup of `M` and has normalizer inside `M`, the
nontriviality of `M_σ` follows. -/
theorem Msigma_ne_bot_of_sylowMap_eq_opiCoreInG_singleton [Finite G] {M : Subgroup G} {q : ℕ}
    (hqM : q ∈ (Nat.card ↥M).primeFactors) (P : Sylow q ↥M)
    (hP : (P : Subgroup ↥M).map M.subtype = opiCoreInG ({q} : Set ℕ) M)
    (hN : Subgroup.normalizer (opiCoreInG ({q} : Set ℕ) M : Set G) ≤ M) :
    Msigma M ≠ ⊥ := by
  have hqσ : q ∈ sigma M :=
    mem_sigma_of_sylowMap_eq_opiCoreInG_singleton hqM P hP hN
  have hOq : opiCoreInG ({q} : Set ℕ) M ≠ ⊥ :=
    opiCoreInG_singleton_ne_bot_of_sylowMap_eq hqM P hP
  exact Msigma_ne_bot_of_opiCoreInG_singleton_ne_bot_of_mem_sigma hqσ hOq

/-- Convert the local `O_q(M)` notation from §4/Thm 4.20 into the ambient `O_q(M)`
notation used in §10. -/
theorem sylowMap_eq_opiCoreInG_singleton_of_eq_opCore [Finite G] {M : Subgroup G} {q : ℕ}
    [Fact q.Prime] (P : Sylow q ↥M)
    (hP : (P : Subgroup ↥M) = Ch01.opCore q ↥M) :
    (P : Subgroup ↥M).map M.subtype = opiCoreInG ({q} : Set ℕ) M := by
  rw [hP, opiCoreInG, OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := ↥M) q]

/-- A normal local Sylow subgroup is the local core, hence maps to the ambient singleton
core. -/
theorem sylowMap_eq_opiCoreInG_singleton_of_normal [Finite G] {M : Subgroup G} {q : ℕ}
    [Fact q.Prime] (P : Sylow q ↥M) (hP : (P : Subgroup ↥M).Normal) :
    (P : Subgroup ↥M).map M.subtype = opiCoreInG ({q} : Set ℕ) M :=
  sylowMap_eq_opiCoreInG_singleton_of_eq_opCore P (Ch01.Sylow.eq_opCore_of_normal P hP)

/-- Hard-branch support for BG Theorem 10.2(e) in the natural Thm 4.20(c) form: a
normal Sylow `q`-subgroup of `M` supplies `M_σ ≠ 1`. -/
theorem Msigma_ne_bot_of_normal_local_sylow [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {q : ℕ} [Fact q.Prime]
    (P : Sylow q ↥M) (hP : (P : Subgroup ↥M).Normal)
    (hqM : q ∈ (Nat.card ↥M).primeFactors) :
    Msigma M ≠ ⊥ := by
  have hPcore : (P : Subgroup ↥M).map M.subtype = opiCoreInG ({q} : Set ℕ) M :=
    sylowMap_eq_opiCoreInG_singleton_of_normal P hP
  have hOq : opiCoreInG ({q} : Set ℕ) M ≠ ⊥ :=
    opiCoreInG_singleton_ne_bot_of_sylowMap_eq hqM P hPcore
  have hN : Subgroup.normalizer (opiCoreInG ({q} : Set ℕ) M : Set G) ≤ M :=
    OddOrder.BG.Ch2.S09.normalizer_opiCoreInG_singleton_le_maximal_of_ne_bot hG hM hOq
  exact Msigma_ne_bot_of_sylowMap_eq_opiCoreInG_singleton hqM P hPcore hN

/-- A BG Theorem 4.20(c) characteristic Sylow-series package for `M` supplies the hard
branch nontriviality `M_σ ≠ 1`. -/
theorem Msigma_ne_bot_of_characteristicSylowSeriesPackage [Finite G]
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (pkg : OddOrder.BG.Ch1.S04.CharacteristicSylowSeriesPackage ↥M) :
    Msigma M ≠ ⊥ := by
  obtain ⟨i, _hi, hqM, P, hP⟩ :=
    OddOrder.BG.Ch1.S04.CharacteristicSylowSeriesPackage.exists_terminal_normal_sylow pkg
  have : Fact (pkg.series.step i).q.Prime := (pkg.series.step i).q_prime
  exact Msigma_ne_bot_of_normal_local_sylow hG hM P hP hqM

/-- Rank-`≤ 2` Fitting input for the hard branch of BG Theorem 10.2(e): applying BG
Theorem 4.20(c) inside the maximal subgroup `M` gives a characteristic Sylow series, hence
`M_σ ≠ 1`. -/
theorem Msigma_ne_bot_of_rank_fittingInG_le_two [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) [Nontrivial ↥M]
    (hrank : rank ↥(Ch2.S08.fittingInG M) ≤ 2) :
    Msigma M ≠ ⊥ := by
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hodd : Odd (Nat.card ↥M) := by
    rcases Nat.even_or_odd (Nat.card ↥M) with he | ho
    · exfalso
      have h2 : (2 : ℕ) ∣ Nat.card G := he.two_dvd.trans (Subgroup.card_subgroup_dvd_card M)
      have := hG.odd
      rw [Nat.odd_iff] at this
      omega
    · exact ho
  have hrankF : rank ↥(Ch01.fitting ↥M) ≤ 2 := by
    refine le_trans (OddOrder.GroupTheory.rank_le_of_injective
      (f := (Subgroup.equivMapOfInjective (Ch01.fitting ↥M) M.subtype
        M.subtype_injective).toMonoidHom) ?_) hrank
    exact (Subgroup.equivMapOfInjective (Ch01.fitting ↥M) M.subtype
      M.subtype_injective).injective
  obtain ⟨pkg⟩ :=
    OddOrder.BG.Ch1.S05.exists_characteristicSylowSeriesPackage_of_rank_fitting_le_two
      hodd hrankF
  exact Msigma_ne_bot_of_characteristicSylowSeriesPackage hG hM pkg

/-- The Fitting subgroup of `M`, viewed inside `G`, has rank no larger than `M`. -/
theorem rank_fittingInG_le_rank [Finite G] (M : Subgroup G) :
    rank ↥(Ch2.S08.fittingInG M) ≤ rank ↥M :=
  OddOrder.GroupTheory.rank_le_of_injective
    (f := Subgroup.inclusion (Ch2.S08.fittingInG_le M))
    (Subgroup.inclusion_injective (Ch2.S08.fittingInG_le M))

/-- Low-rank maximal-subgroup input for the hard branch of BG Theorem 10.2(e). -/
theorem Msigma_ne_bot_of_rank_le_two [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hrank : rank ↥M ≤ 2) :
    Msigma M ≠ ⊥ := by
  have : Nontrivial ↥M :=
    (Subgroup.nontrivial_iff_ne_bot M).mpr (hG.ne_bot_of_mem_maximalSubgroups hM)
  exact Msigma_ne_bot_of_rank_fittingInG_le_two hG hM
    ((rank_fittingInG_le_rank M).trans hrank)

/-- If `M_α` is an `α(M)`-Hall subgroup and is trivial, then no prime has
`p`-rank at least three in `M`; hence `rank M ≤ 2`. -/
theorem rank_le_two_of_Malpha_eq_bot_of_isHall [Finite G] {M : Subgroup G}
    (hHallα : Ch03.IsHallSubgroup (alpha M) (Malpha M)) (hαbot : Malpha M = ⊥) :
    rank ↥M ≤ 2 := by
  rw [rank_le_iff]
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  by_contra hpRank
  have h3 : 3 ≤ pRank ↥M p := by omega
  have hpos : 0 < pRank ↥M p := by omega
  have hpM : p ∈ (Nat.card ↥M).primeFactors :=
    OddOrder.BG.Ch2.S09.mem_primeFactors_card_of_pos_pRank (H := ↥M) (p := p) hpos
  have hpG : p ∈ (Nat.card G).primeFactors :=
    Nat.primeFactors_mono (Subgroup.card_subgroup_dvd_card M) Nat.card_pos.ne' hpM
  have hHallBot : Ch03.IsHallSubgroup (alpha M) (⊥ : Subgroup G) := by
    simpa [hαbot] using hHallα
  have hnotα : ∀ q ∈ (Nat.card G).primeFactors, q ∉ alpha M :=
    (Ch03.IsHallSubgroup.bot_iff (G := G) (alpha M)).mp hHallBot
  have hpα : p ∈ alpha M := by
    rw [mem_alpha_iff]
    exact ⟨hpM, h3⟩
  exact hnotα p hpG hpα

/-- Hard branch of BG Theorem 10.2(e), conditional on the Hall `M_α` conjunct. -/
theorem Msigma_ne_bot_of_Malpha_eq_bot_of_isHall [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hHallα : Ch03.IsHallSubgroup (alpha M) (Malpha M)) (hαbot : Malpha M = ⊥) :
    Msigma M ≠ ⊥ :=
  Msigma_ne_bot_of_rank_le_two hG hM
    (rank_le_two_of_Malpha_eq_bot_of_isHall hHallα hαbot)

/-- **BG Theorem 10.2(e), easy branch**: if `M_α` is nontrivial, then `M_σ` is
nontrivial because `M_α ≤ M_σ`. The remaining branch of (e) is the hard
`M_α = 1` case using the low-rank/Thm 4.20 argument. -/
theorem Msigma_ne_bot_of_Malpha_ne_bot [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hα : Malpha M ≠ ⊥) :
    Msigma M ≠ ⊥ := by
  intro hσ
  exact hα (le_bot_iff.mp (by
    simpa [hσ] using Malpha_le_Msigma hG hM))

/-- **BG Theorem 10.2(e)**: `M_σ` is nontrivial. If `M_α` is nontrivial, this is
immediate from `M_α ≤ M_σ`; if `M_α = 1`, the Hall-`α` theorem above unlocks the
low-rank/Thm 4.20 hard branch. -/
theorem Msigma_ne_bot [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    Msigma M ≠ ⊥ := by
  by_cases hα : Malpha M = ⊥
  · exact Msigma_ne_bot_of_Malpha_eq_bot_of_isHall hG hM (Malpha_isHall hG hM) hα
  · exact Msigma_ne_bot_of_Malpha_ne_bot hG hM hα

/-- **BG Theorem 10.2 の (a)(b)(c)(e)** (mmd L2713): `M ∈ ℳ` のとき `M_σ`, `M_α` は Hall 部分群で、
`M_α ⊆ M_σ ⊆ M'`、`M_σ ≠ 1`。

⚠ 原典の **(d)** (`r(M/M_α) ≤ 2` と `M'/M_α` nilpotent) は**この束にだけ入っていない**。
(d) 自体は形式化済で、`rank_quotient_Malpha_le_two_of_isHall` と
`derived_quotient_Malpha_le_fitting` (+ `rank_fitting_quotient_Malpha_le_two`) が与える。
書籍の 5 条項すべてを 1 statement にした形は `bgThm102` (本ファイル末尾)。
(以前ここには「quotient 型の `Normal` instance 整備後に追加予定」と書かれていたが stale
だった — issue 0177 §10 監査, 2026-08-08。) -/
theorem isHall_Msigma_Malpha [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    Ch03.IsHallSubgroup (sigma M) (Msigma M) ∧
    Ch03.IsHallSubgroup (alpha M) (Malpha M) ∧
    Malpha M ≤ Msigma M ∧ Msigma M ≤ derivedInG M ∧
    Msigma M ≠ ⊥ := by
  exact ⟨Msigma_isHall hG hM, Malpha_isHall hG hM, Malpha_le_Msigma hG hM,
    Msigma_le_derived hG hM, Msigma_ne_bot hG hM⟩

end OddOrder.BG.Ch3.S10


