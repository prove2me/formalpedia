-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TheoremIIPackaging
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TheoremIIPackaging
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T10:59:54.973844+00:00
-- url     : https://prove2.me/theorems/32b9cf55-d4f8-4ebd-abe6-13d10120383b
-- title:
--   Bender–Glauberman Theorem II: the system of supporting subgroups for $A(M)$
-- statement:
--   Formalizes Theorem II (Tii) of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, Chapter IV §16, and the remark after it, concerning the system of supporting subgroups for $A(M)$ for a maximal subgroup $M$. The bundle consists of lemmas only.
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/TheoremIIPackaging.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/TheoremIIPackaging.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TheoremsAE
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TypeBridges
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TaxonomyOutput
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_Lemma1413

namespace OddOrder.BG.Ch4.S16

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch4.S14

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **`𝒞_G(K₀#)`-points are nonidentity `κ`-elements** (issue 9076 piece 4c; moved here from
`Peterfalvi.S10_TypePSupportA0` — the statement and proof are entirely BG §14/§16): every
`G`-conjugate of a nontrivial element of the `κ(M)`-Hall `K₀` is a nonidentity `κ(M)`-element.
A `k ∈ K₀#` has `orderOf k ∣ |K₀|`, a `κ`-number (`hK`), so `k` is a `κ`-element; conjugation
preserves this (`isPiElement_conj`) and non-triviality.  This is the exclusion input for both `A(S)`
(`κ′`-elements) and `V^S` (`σ`-prime carriers) against `A0Set M K₀ = hatMsigma M ∖ 𝒞_G(K₀#)`. -/
theorem kappaHall_conjClassSet_isPiElement [Finite G] {M K₀ : Subgroup G} (hKM : K₀ ≤ M)
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M) (K₀.subgroupOf M))
    {w : G} (hw : w ∈ conjClassSet (OddOrder.GroupTheory.sharpSubgroup K₀)) :
    IsPiElement (OddOrder.BG.Ch4.S14.kappa M) w ∧ w ≠ 1 := by
  obtain ⟨k, hk, g, hgw⟩ := hw
  rw [OddOrder.GroupTheory.sharpSubgroup, Set.mem_sdiff, SetLike.mem_coe,
    Set.mem_singleton_iff] at hk
  obtain ⟨hkK, hk1⟩ := hk
  subst hgw
  have hkord : orderOf k ∣ Nat.card ↥K₀ := by
    have horx : orderOf k = orderOf (⟨k, hkK⟩ : ↥K₀) :=
      orderOf_injective K₀.subtype K₀.subtype_injective ⟨k, hkK⟩
    rw [horx]; exact orderOf_dvd_natCard _
  have hkκ : IsPiElement (OddOrder.BG.Ch4.S14.kappa M) k := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ orderOf k := Nat.dvd_of_mem_primeFactors hp
    have hcardeq : Nat.card ↥(K₀.subgroupOf M) = Nat.card ↥K₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
    refine hK.1 p ?_
    rw [hcardeq]
    exact Nat.mem_primeFactors.mpr ⟨hpp, hpdvd.trans hkord, Nat.card_pos.ne'⟩
  refine ⟨OddOrder.BG.Ch4.S14.isPiElement_conj g hkκ, fun hcontra => hk1 ?_⟩
  have hkk : k = g⁻¹ * (g * k * g⁻¹) * g := by group
  rw [hkk, hcontra]; group

/-- **`ASet M U₀ ⊆ A0Set M K₀`** (issue 9076 piece 4c; moved here from
`Peterfalvi.S10_TypePSupportA0` — the statement and proof are entirely BG §14/§16): the BG
Theorem-E `A(M)`-set embeds into the `A_0(M)`-set.  Both are `⊆ hatMsigma M`; and an
`ASet`-point `x ∈ U₀ ⊔ M_σ` is a `κ′`-element
(`mem_U_sup_Msigma_iff_isPiElement_kappa_compl`), while a `𝒞_G(K₀#)`-point is a nonidentity
`κ`-element (`kappaHall_conjClassSet_isPiElement`) — no element is both, so `x ∉ 𝒞_G(K₀#)`. -/
theorem aSet_subset_A0Set [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K₀ U₀ : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKM : K₀ ≤ M) (hUM : U₀ ≤ M)
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M) (K₀.subgroupOf M))
    (hU : OddOrder.Isaacs.Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U₀.subgroupOf M)) :
    OddOrder.BG.Ch4.S16.ASet M U₀ ⊆ OddOrder.BG.Ch4.S16.A0Set M K₀ := by
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hnorm : ((U₀ ⊔ OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hUM hMσM)).mpr
      (OddOrder.BG.Ch4.S16.theoremA_ungated_conjuncts hG hM hKM hUM hK rfl hU).2.2.1
  intro x hx
  simp only [OddOrder.BG.Ch4.S16.ASet, Set.mem_inter_iff, SetLike.mem_coe] at hx
  obtain ⟨hxhat, hxsup⟩ := hx
  simp only [OddOrder.BG.Ch4.S16.A0Set, Set.mem_sdiff]
  refine ⟨hxhat, fun hxconj => ?_⟩
  obtain ⟨hxκ, hx1⟩ := kappaHall_conjClassSet_isPiElement hKM hK hxconj
  have hxκ' : IsPiElement (OddOrder.BG.Ch4.S14.kappa M)ᶜ x :=
    (OddOrder.BG.Ch4.S14.mem_U_sup_Msigma_iff_isPiElement_kappa_compl hG hM hUM hU hnorm
      hxhat.1).mp hxsup
  have hne1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hpp, hpdvd⟩ := (orderOf x).exists_prime_and_dvd hne1
  have hpf : p ∈ (orderOf x).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpp, hpdvd, (orderOf_pos x).ne'⟩
  exact (hxκ' p hpf) (hxκ p hpf)

end OddOrder.BG.Ch4.S16


