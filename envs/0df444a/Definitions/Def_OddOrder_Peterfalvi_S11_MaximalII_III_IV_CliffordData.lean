-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CliffordData
-- name    : OddOrder_Peterfalvi_S11_MaximalII_III_IV_CliffordData
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T11:38:01.484736+00:00
-- url     : https://prove2.me/theorems/e4d5d3d7-761a-4ce1-9c16-b695f4f941ca
-- title:
--   Peterfalvi §9/§11: Clifford data, chief-factor quotients and Singer adapters (continuation)
-- statement:
--   A continuation file in the formalization of Peterfalvi's analysis of the Clifford cases for maximal subgroups of types II, III and IV. It collects chief-factor quotient hypotheses and subgroup-to-module transport results for the elementary abelian chief factor.
--
--   Main declarations: `chiefFactorQuotientHypothesisGen` (Generic chief-factor quotient `Hypothesis`); `elabRepresentation_isIrreducible` (The descended representation `elabRepresentation p φ` on `Additive K` is irreducible exactly…); `elabRepresentation_isSimpleModule_and_faithful` (Thin subgroup→module Singer adapter); `exists_units_monoidHom_of_isIrreducibleCharacter_of_isMulCommutative` (An irreducible character of a finite abelian group is a linear character).
--
--   The bundle also proves 27 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_MaximalII_III_IV/CliffordData.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_MaximalII_III_IV/CliffordData.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_ChiefFactorCore

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

variable {M : Subgroup G}

/-- The chief factor `H̄ = H/H₀ ≅ ↥H ⧸ N` has order `p^q`: `|H| = p^q·|H₀|` (`quotient_order`) and
`|H₀| = |N|` (`H₀ = N.map H.subtype`), so `[H : N] = p^q`. -/
theorem chiefFactor_quotient_card [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    (chief : ChiefFactorData data) :
    Nat.card (↥data.H ⧸ chief.N) = chief.p ^ data.q := by
  have := chief.N_normal
  have hH0card : Nat.card ↥chief.H0 = Nat.card ↥chief.N := by
    rw [chief.H0_eq]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective chief.N data.H.subtype
      data.H.subtype_injective).toEquiv).symm
  have key : chief.N.index * Nat.card ↥chief.N = chief.p ^ data.q * Nat.card ↥chief.N := by
    rw [Subgroup.index_mul_card, chief.quotient_order, hH0card]
  rw [(Subgroup.index_eq_card chief.N).symm]
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos key

/-- **`|C_{H̄}(W₁)| = p`** (Peterfalvi (9.6)).  The `W₁`-fixed points of the chief factor
`H̄ = ↥H ⧸ N` have order exactly `p`: this is the second clause of
`coprimeFrobeniusChiefFactor_card` (Wielandt's fixed-point formula), with all of its hypotheses
read off `chief`.

Both `chiefFactor_W2_not_le_H0` (which needs `C_{H̄}(W₁) ≠ ⊥`) and Peterfalvi (9.7.b) (which
needs a base point `s ∈ W̄₂^#`) consume this. -/
theorem chiefFactor_card_fixedByE [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    Nat.card ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1
      chief.N_aInvariant).fixedByE = chief.p := by
  have := chief.N_normal
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  have hHbar : Nat.card (↥data.H ⧸ chief.N) ≠ 1 := by
    rw [chiefFactor_quotient_card chief]
    exact (Nat.one_lt_pow (Nat.card_pos (α := ↥data.W1)).ne' chief.p_prime.one_lt).ne'
  have hUnorm : ((typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant).U).Normal :=
    (typeP_uW1_frobenius data.typeP hU).isNormal
  have hEcyc := typeP_quotient_fixedByE_cyclic data.typeP hU chief.N_aInvariant
  exact (coprimeFrobeniusChiefFactor_card
    (typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant) hUnorm chief.p_prime
    chief.quotient_elementaryAbelian chief.quotient_chiefFactor chief.U_noncentral_on_quotient
    hEcyc hHbar).2

/-- **Peterfalvi (8.4.d) `W2_nontrivial` input: `W₂ ⊄ H₀`.**  The `W₁`-fixed points of the chief
factor `H̄ = ↥H ⧸ N` have order `p ≠ 1` (`coprimeFrobeniusChiefFactor_card`, Wielandt), and they are
the image of `C_H(W₁) = W₂` (`map_fixedSubgroup_eq_fixedSubgroup_quotient`).  So `C_H(W₁) ⊄ N`, i.e.
some element of `W₂` lies outside `H₀ = N.map H.subtype`; hence `W₂ ⊄ H₀`, equivalently the
certain-type `W̄₂ = W₂ H₀ / H₀` of `S06.Hypothesis (M/H₀)` is nontrivial. -/
theorem chiefFactor_W2_not_le_H0 [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    ¬ data.W2 ≤ chief.H0 := by
  change ¬ data.typeP.W2 ≤ chief.H0
  have := chief.N_normal
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  have hfixne : (typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant).fixedByE ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥(typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant).fixedByE =
        1 :=
      by rw [h]; simp
    exact chief.p_prime.ne_one ((chiefFactor_card_fixedByE chief).symm.trans h1)
  have hcopHW1 : Nat.Coprime
      (Nat.card ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1))) (Nat.card ↥data.H) :=
    (typeP_coprime_H_uW1 data.typeP hU).symm.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _)
  have : Group.IsSolvable ↥data.H := (typeP_coprimeAction data.typeP hU).H_solvable
  have hmap : (fixedSubgroup (typeP_conjAction data.typeP)
      (data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1))).map (QuotientGroup.mk' chief.N)
      = (typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant).fixedByE :=
    map_fixedSubgroup_eq_fixedSubgroup_quotient chief.N_aInvariant hcopHW1 (Or.inr inferInstance)
  have hCHW1 : (fixedSubgroup (typeP_conjAction data.typeP)
        (data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1))).map data.typeP.H.subtype
      = data.typeP.W2 := by
    rw [typeP_fixedSubgroup_map data.typeP le_sup_right, typeP_H_inf_centralizer_W1]
  have hCfixN : ¬ (fixedSubgroup (typeP_conjAction data.typeP)
      (data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1))) ≤ chief.N := by
    intro hle
    apply hfixne
    rw [← hmap, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hle
  obtain ⟨c, hcCfix, hcN⟩ := SetLike.not_le_iff_exists.mp hCfixN
  intro hW2H0
  have hcG_W2 : (data.typeP.H.subtype c) ∈ data.typeP.W2 := by
    rw [← hCHW1]; exact Subgroup.mem_map_of_mem _ hcCfix
  have hcG_H0 : (data.typeP.H.subtype c) ∈ chief.H0 := hW2H0 hcG_W2
  rw [chief.H0_eq, Subgroup.mem_map] at hcG_H0
  obtain ⟨n, hn, hnc⟩ := hcG_H0
  exact hcN (data.typeP.H.subtype_injective hnc ▸ hn)

/-- **`W₁ ⊓ H₀C = ⊥` inside `↥M`** (the `N' = H₀C` non-degeneracy input for
`chiefFactorQuotientHypothesisGen`): `H₀C ≤ M'` (`chiefFactor_H0supC_le_derived`) and `W₁` is a
complement to `M'` (`M_complement`), so `W₁ ⊓ H₀C ≤ W₁ ⊓ M' = ⊥`. -/
theorem chiefFactor_W1_inf_H0supC_subgroupOf_eq_bot [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    (data.W1.subgroupOf M) ⊓ ((chief.H0 ⊔ cSub data chief).subgroupOf M) = ⊥ := by
  have hH0CM' : ((chief.H0 ⊔ cSub data chief).subgroupOf M) ≤ (derivedInG M).subgroupOf M :=
    Subgroup.comap_mono (chiefFactor_H0supC_le_derived chief)
  rw [eq_bot_iff]
  exact le_trans (inf_le_inf_left _ hH0CM')
    (disjoint_iff.mp data.typeP.M_complement.disjoint.symm).le

/-- **`W₂ ⊄ H₀C` inside `↥M`** (the `N' = H₀C` `W2_nontrivial` input): if `W₂ ≤ H₀C` then, as
`W₂ ≤ H`, `W₂ ≤ H₀C ⊓ H = H₀` (`chiefFactor_H0supC_inf_H_eq_H0`), contradicting
`chiefFactor_W2_not_le_H0`. -/
theorem chiefFactor_W2_not_le_H0supC [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    ¬ data.W2.subgroupOf M ≤ (chief.H0 ⊔ cSub data chief).subgroupOf M := by
  intro hle
  have hW2leM : data.W2 ≤ M := (data.typeP.W2_le.trans inf_le_left).trans (H_le_M data)
  have hW2H0C : data.W2 ≤ chief.H0 ⊔ cSub data chief := by
    intro y hy
    have hyM : (⟨y, hW2leM hy⟩ : ↥M) ∈ data.W2.subgroupOf M := Subgroup.mem_subgroupOf.mpr hy
    exact Subgroup.mem_subgroupOf.mp (hle hyM)
  refine chiefFactor_W2_not_le_H0 chief ?_
  have hW2H : data.W2 ≤ data.H := data.typeP.W2_le.trans inf_le_left
  have hkey : data.W2 ≤ (chief.H0 ⊔ cSub data chief) ⊓ data.H := le_inf hW2H0C hW2H
  rwa [chiefFactor_H0supC_inf_H_eq_H0 chief] at hkey

/-- **Peterfalvi (9.9.b), `|W̄₂| = p`**: the image `W̄₂ = (W₂.subgroupOf M).map(mk' H₀')` of the
cyclic factor `W₂` in the chief-factor quotient `↥M ⧸ H₀` has order `p` — the quotient chief-factor
centralizer order `|C_{H̄}(W₁)| = p` (`coprimeFrobeniusChiefFactor_card`), *not* `|W₂|` (which can
exceed `p` in type II).

The bridge is a card identity avoiding the explicit cross-quotient iso: both `W̄₂` and the quotient
`fixedByE = F.map(mk' N)` (`F = C_H(W₁)` the `W₁`-fixed points in `↥H`) are quotients
`|F|/|F ⊓ kernel|`.  Via the injective `H.subtype` (`F ↦ W₂`, `N ↦ H₀`), the kernels match
(`|F ⊓ N| = |W₂ ⊓ H₀| = |J₁|`), and `|F| = |W₂|`, so `|W̄₂| = |F|/|F⊓N| = |fixedByE| = p`.  This
gives the `p-1` reducible count once `card_reducible_Hnontrivial_induce_eq_W2_sub_one` is
instantiated on `chiefFactorQuotientHypothesis` (issue 1012, B3). -/
theorem chiefFactor_card_W2bar [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    [(chief.H0.subgroupOf M).Normal] :
    Nat.card ↥((data.W2.subgroupOf M).map (QuotientGroup.mk' (chief.H0.subgroupOf M)))
      = chief.p := by
  have := chief.N_normal
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  -- The quotient chief-factor action and `|fixedByE| = p`.
  have hHbar : Nat.card (↥data.typeP.H ⧸ chief.N) ≠ 1 := by
    rw [chiefFactor_quotient_card chief]
    exact (Nat.one_lt_pow (Nat.card_pos (α := ↥data.typeP.W1)).ne' chief.p_prime.one_lt).ne'
  have hUnorm : ((typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant).U).Normal :=
    (typeP_uW1_frobenius data.typeP hU).isNormal
  have hEcyc := typeP_quotient_fixedByE_cyclic data.typeP hU chief.N_aInvariant
  have hcard := coprimeFrobeniusChiefFactor_card
    (typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant) hUnorm chief.p_prime
    chief.quotient_elementaryAbelian chief.quotient_chiefFactor chief.U_noncentral_on_quotient
    hEcyc hHbar
  have hcopHW1 : Nat.Coprime
      (Nat.card ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1))) (Nat.card
          ↥data.typeP.H) :=
    (typeP_coprime_H_uW1 data.typeP hU).symm.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _)
  have : Group.IsSolvable ↥data.typeP.H := (typeP_coprimeAction data.typeP hU).H_solvable
  -- `F = C_H(W₁)`, with `F.map(mk' N) = fixedByE` and `F.map H.subtype = W₂`.
  set F := fixedSubgroup (typeP_conjAction data.typeP)
    (data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) with hF
  have hmap : F.map (QuotientGroup.mk' chief.N)
      = (typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant).fixedByE :=
    map_fixedSubgroup_eq_fixedSubgroup_quotient chief.N_aInvariant hcopHW1 (Or.inr inferInstance)
  have hCHW1 : F.map data.typeP.H.subtype = data.typeP.W2 := by
    rw [hF, typeP_fixedSubgroup_map data.typeP le_sup_right, typeP_H_inf_centralizer_W1]
  -- `W₂ ≤ M` (via `W₂ ≤ H ≤ M' ≤ M`).
  have hW2M : data.typeP.W2 ≤ M := ((data.typeP.W2_le.trans inf_le_left).trans
    data.typeP.H_le).trans (Subgroup.map_subtype_le _)
  -- `|A.subgroupOf B| = |A ⊓ B|` (image under the injective `B.subtype`).
  have hcardSubOf : ∀ {K : Type u_1} [inst : Group K] (A B : Subgroup K),
      Nat.card ↥(A.subgroupOf B) = Nat.card ↥(A ⊓ B) := by
    intro K _ A B
    rw [← Subgroup.subgroupOf_map_subtype A B]
    exact Nat.card_congr (Subgroup.equivMapOfInjective (A.subgroupOf B) B.subtype
      (Subgroup.subtype_injective B)).toEquiv
  -- `|F| = |W₂|` (`H.subtype` injective) and `|fixedByE| = p`.
  have hcardF_W2 : Nat.card ↥F = Nat.card ↥data.typeP.W2 := by
    rw [← hCHW1]
    exact Nat.card_congr (Subgroup.equivMapOfInjective F data.typeP.H.subtype
      data.typeP.H.subtype_injective).toEquiv
  have hfixp : Nat.card ↥(typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant).fixedByE
      = chief.p := hcard.2
  -- `|F| = |fixedByE| · |N ⊓ F|` (first iso for `mk' N` restricted to `F`).
  have hFsplit : Nat.card ↥F
      = Nat.card ↥(typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant).fixedByE
        * Nat.card ↥(chief.N.subgroupOf F) := by
    rw [← hmap, ← Subgroup.nat_card_quotient_subgroupOf_eq_card_map]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  -- `|W₂.subgroupOf M| = |W̄₂| · |J₁|` (first iso for `mk' H₀'` restricted to `W₂.subgroupOf M`).
  set J₁ := (chief.H0.subgroupOf M).subgroupOf (data.typeP.W2.subgroupOf M) with hJ₁
  have hW2split : Nat.card ↥(data.typeP.W2.subgroupOf M)
      = Nat.card ↥((data.typeP.W2.subgroupOf M).map (QuotientGroup.mk' (chief.H0.subgroupOf M)))
        * Nat.card ↥J₁ := by
    rw [← Subgroup.nat_card_quotient_subgroupOf_eq_card_map]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hcardW2M : Nat.card ↥(data.typeP.W2.subgroupOf M) = Nat.card ↥data.typeP.W2 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2M).toEquiv
  -- The two kernels have equal order: `|J₁| = |N ⊓ F| = |W₂ ⊓ H₀|`.
  have hker : Nat.card ↥J₁ = Nat.card ↥(chief.N.subgroupOf F) := by
    -- `|J₁| = |(H₀.subgroupOf M) ⊓ (W₂.subgroupOf M)| = |(H₀ ⊓ W₂).subgroupOf M| = |H₀ ⊓ W₂|`.
    have hinf : (chief.H0.subgroupOf M) ⊓ (data.typeP.W2.subgroupOf M)
        = (chief.H0 ⊓ data.typeP.W2).subgroupOf M :=
      (Subgroup.comap_inf chief.H0 data.typeP.W2 M.subtype).symm
    have h1 : Nat.card ↥J₁ = Nat.card ↥(chief.H0 ⊓ data.typeP.W2 : Subgroup G) := by
      rw [hJ₁, hcardSubOf, hinf, hcardSubOf, inf_of_le_left (inf_le_right.trans hW2M)]
    -- `|N.subgroupOf F| = |N ⊓ F| = |(N ⊓ F).map H.subtype| = |H₀ ⊓ W₂|`.
    have h2 : Nat.card ↥(chief.N.subgroupOf F)
        = Nat.card ↥(chief.H0 ⊓ data.typeP.W2 : Subgroup G) := by
      rw [hcardSubOf]
      have hmapinf : (chief.N ⊓ F).map data.typeP.H.subtype
          = (chief.H0 ⊓ data.typeP.W2 : Subgroup G) := by
        rw [Subgroup.map_inf_eq chief.N F data.typeP.H.subtype data.typeP.H.subtype_injective,
          hCHW1, ← chief.H0_eq]
      rw [← hmapinf]
      exact Nat.card_congr (Subgroup.equivMapOfInjective _ data.typeP.H.subtype
        data.typeP.H.subtype_injective).toEquiv
    rw [h1, h2]
  -- Combine: `|W̄₂| · |J₁| = |W₂| = |F| = |fixedByE| · |J₁|`, cancel.
  have hposJ : 0 < Nat.card ↥J₁ := Nat.card_pos
  have hchain : Nat.card ↥((data.typeP.W2.subgroupOf M).map
        (QuotientGroup.mk' (chief.H0.subgroupOf M))) * Nat.card ↥J₁
      = chief.p * Nat.card ↥J₁ := by
    rw [← hW2split, hcardW2M, ← hcardF_W2, hFsplit, hfixp, hker]
  change Nat.card ↥((data.typeP.W2.subgroupOf M).map (QuotientGroup.mk' (chief.H0.subgroupOf M)))
    = chief.p
  exact Nat.eq_of_mul_eq_mul_right hposJ hchain

/-- **Image order under `mk'` depends only on `S ∩ N`** (general): for normal `N₁, N₂` with
`S ⊓ N₁ = S ⊓ N₂`, the images `S/(S∩Nᵢ)` have equal order, since `|S.map(mk' N)| · |S ⊓ N| = |S|`
(first isomorphism `nat_card_quotient_subgroupOf_eq_card_map`). -/
theorem nat_card_map_mk'_eq_of_inf_eq {Γ : Type*} [Group Γ] [Finite Γ]
    (S N₁ N₂ : Subgroup Γ) [N₁.Normal] [N₂.Normal] (h : S ⊓ N₁ = S ⊓ N₂) :
    Nat.card ↥(S.map (QuotientGroup.mk' N₁)) = Nat.card ↥(S.map (QuotientGroup.mk' N₂)) := by
  have hsplit : ∀ (N : Subgroup Γ) [N.Normal],
      Nat.card ↥(S.map (QuotientGroup.mk' N)) * Nat.card ↥(S ⊓ N) = Nat.card ↥S := by
    intro N _
    have hc : Nat.card ↥(N.subgroupOf S) = Nat.card ↥(S ⊓ N) := by
      rw [inf_comm, ← Subgroup.subgroupOf_map_subtype N S]
      exact Nat.card_congr (Subgroup.equivMapOfInjective (N.subgroupOf S) S.subtype
        (Subgroup.subtype_injective S)).toEquiv
    rw [← hc, ← Subgroup.nat_card_quotient_subgroupOf_eq_card_map]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf S)).symm
  have h1 := hsplit N₁
  rw [h] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans (hsplit N₂).symm)

/-- **`|W̄₂'| = p` for the `M/H₀C` quotient** (issue 1012, step A): the chief-factor image `W̄₂'` in
`↥M ⧸ H₀C` keeps order `p`.  Reduces to the `H₀` case (`chiefFactor_card_W2bar`): the kernels
coincide, `W₂ ⊓ H₀C = W₂ ⊓ H₀` (as `W₂ ≤ H` and `(H₀C) ⊓ H = H₀` by
`chiefFactor_H0supC_inf_H_eq_H0`), so by `nat_card_map_mk'_eq_of_inf_eq` the images have equal
order. -/
theorem chiefFactor_card_W2bar_H0supC [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    [(chief.H0.subgroupOf M).Normal] [((chief.H0 ⊔ cSub data chief).subgroupOf M).Normal] :
    Nat.card ↥((data.W2.subgroupOf M).map
        (QuotientGroup.mk' ((chief.H0 ⊔ cSub data chief).subgroupOf M))) = chief.p := by
  have hW2H : data.W2 ≤ data.H := data.typeP.W2_le.trans inf_le_left
  have hG_eq : data.W2 ⊓ (chief.H0 ⊔ cSub data chief) = data.W2 ⊓ chief.H0 := by
    apply le_antisymm
    · refine le_inf inf_le_left ?_
      calc data.W2 ⊓ (chief.H0 ⊔ cSub data chief)
          ≤ data.H ⊓ (chief.H0 ⊔ cSub data chief) := inf_le_inf_right _ hW2H
        _ = (chief.H0 ⊔ cSub data chief) ⊓ data.H := inf_comm _ _
        _ = chief.H0 := chiefFactor_H0supC_inf_H_eq_H0 chief
    · exact inf_le_inf_left _ le_sup_left
  have hinf : (data.W2.subgroupOf M) ⊓ ((chief.H0 ⊔ cSub data chief).subgroupOf M)
      = (data.W2.subgroupOf M) ⊓ (chief.H0.subgroupOf M) := by
    simp only [Subgroup.subgroupOf, ← Subgroup.comap_inf, hG_eq]
  rw [nat_card_map_mk'_eq_of_inf_eq (data.W2.subgroupOf M)
    ((chief.H0 ⊔ cSub data chief).subgroupOf M) (chief.H0.subgroupOf M) hinf]
  exact chiefFactor_card_W2bar chief

/-- **`𝒮 = sSet` is finite** (issue 1017, the `hSfin` input of the caseB (5.7) coherence engine and
the (9.11) non-Galois maximal-subfamily refutation): the family injects into
`IrreducibleCharacter ↥(huSub data)` (a `Finite` type) via the induction map, so it is a subset of a
finite range.

Stated over Hypothesis (9.2) alone, so it belongs in §9; it previously sat in
`S15_SAndT_Setup/HypothesisBasics` (namespace `S15`), which put a §9 fact downstream of its own
users (issue 1045). -/
theorem sSet_finite {M : Subgroup G} [Finite G] (data : TypesIIIIIIVSetup M) :
    (sSet data).Finite := by
  apply Set.Finite.subset (Set.finite_range
    (fun χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(huSub data) =>
      induceHU data (χ : ClassFunction ↥(huSub data) ℂ)))
  rintro φ ⟨χ, -, rfl⟩
  exact ⟨χ, rfl⟩

/-- **`𝒮(Y) = sOf data Y` is finite** — the `hSfin` input of the (9.11) maximal-subfamily
refutation, at §9 level.

`𝒮(Y) ⊆ 𝒮` (`sOf_subset_sSet`) and `𝒮` is finite.  The §11 packaging derives the same fact by
routing through the §10 kernel-filtered family (`S08.inducedKernelFamily_finite` composed with
`sOf_subset_SOf`), which needs a `S13.Hypothesis`; nothing about the statement does.  Issue 1045. -/
theorem sOf_finite {M : Subgroup G} [Finite G] (data : TypesIIIIIIVSetup M) (Y : Subgroup G) :
    (sOf data Y).Finite :=
  (sSet_finite data).subset (sOf_subset_sSet data Y)

/-- **Induction-inflation commute, term level** (general): for `f : Γ →* Q` with `ker f ≤ H`, the
induced-character term of the inflated `compHom (f.subgroupMap H) χ̄` at `(x, g)` equals the
induced-character term of `χ̄` on `H.map f` at `(f x, f g)`.  The conjugate `x⁻¹gx ∈ H` iff
`f(x⁻¹gx) = (fx)⁻¹(fg)(fx) ∈ H.map f` (`comap_map_eq_self`, `ker f ≤ H`), and the values agree
(`χ̄⟨f(x⁻¹gx)⟩`).  Term level of the (8.4.d) induction-inflation commute (issue 1012, B2). -/
theorem induceTerm_compHom_subgroupMap {Γ Q : Type*} [Group Γ] [Group Q]
    (f : Γ →* Q) {H : Subgroup Γ} (hker : f.ker ≤ H)
    (χbar : ClassFunction ↥(H.map f) ℂ) (x g : Γ) :
    ClassFunction.induceTerm H (ClassFunction.compHom (f.subgroupMap H) χbar) x g
      = ClassFunction.induceTerm (H.map f) χbar (f x) (f g) := by
  have hmem : (f x)⁻¹ * (f g) * (f x) ∈ H.map f ↔ x⁻¹ * g * x ∈ H := by
    rw [← map_inv, ← map_mul, ← map_mul, ← Subgroup.mem_comap, Subgroup.comap_map_eq_self hker]
  by_cases hx : x⁻¹ * g * x ∈ H
  · rw [ClassFunction.induceTerm_of_mem _ hx, ClassFunction.induceTerm_of_mem _ (hmem.mpr hx),
      ClassFunction.compHom_apply]
    have heq : (f.subgroupMap H) ⟨x⁻¹ * g * x, hx⟩
        = (⟨(f x)⁻¹ * (f g) * (f x), hmem.mpr hx⟩ : ↥(H.map f)) := by
      apply Subtype.ext
      change f (x⁻¹ * g * x) = (f x)⁻¹ * (f g) * (f x)
      rw [map_mul, map_mul, map_inv]
    rw [heq]
  · rw [ClassFunction.induceTerm_of_not_mem _ hx,
      ClassFunction.induceTerm_of_not_mem _ (fun h => hx (hmem.mp h))]

/-- **The fiber of `mk' N` over `q` is equinumerous to `N`** (`x ↦ x₀⁻¹ x` for a representative
`x₀`).  Used for the `|N|`-fold fiberwise sum in the (8.4.d) induction-inflation commute. -/
theorem card_fiber_mk'_eq {Γ : Type*} [Group Γ] {N : Subgroup Γ} [N.Normal] (q : Γ ⧸ N) :
    Nat.card {x : Γ // QuotientGroup.mk' N x = q} = Nat.card ↥N := by
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk'_surjective N q
  refine Nat.card_congr ⟨fun p => ⟨x₀⁻¹ * (p : Γ), QuotientGroup.eq.mp p.2.symm⟩,
    fun n => ⟨x₀ * (n : Γ), ?_⟩, ?_, ?_⟩
  · refine QuotientGroup.eq.mpr ?_
    have he : (x₀ * (n : Γ))⁻¹ * x₀ = ((n : Γ))⁻¹ := by group
    rw [he]; exact inv_mem n.2
  · intro p; ext; change x₀ * (x₀⁻¹ * (p : Γ)) = (p : Γ); group
  · intro n; ext; change x₀⁻¹ * (x₀ * (n : Γ)) = (n : Γ); group

/-- **`|N|`-fold fiberwise sum over a quotient** (general): `∑_{x:Γ} g(x N) = |N| • ∑_{q:Γ/N} g q`.
Each fiber of `mk' N` has `|N|` elements (`card_fiber_mk'_eq`), and the summand is constant on
fibers.  This is step 2 of the (8.4.d) induction-inflation commute (issue 1012, B2). -/
theorem sum_comp_mk'_eq {Γ : Type*} [Group Γ] [Fintype Γ] (N : Subgroup Γ) [N.Normal]
    [DecidablePred (· ∈ N)] {M : Type*} [AddCommMonoid M] (g : Γ ⧸ N → M) :
    (∑ x : Γ, g (QuotientGroup.mk' N x)) = Nat.card ↥N • ∑ q : Γ ⧸ N, g q := by
  classical
  rw [Finset.smul_sum,
    ← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset (Γ ⧸ N)))
      (fun (x : Γ) (_ : x ∈ Finset.univ) => Finset.mem_univ (QuotientGroup.mk' N x))]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Finset.sum_congr rfl (g := fun _ => g q)
      (fun x hx => by rw [(Finset.mem_filter.mp hx).2]), Finset.sum_const]
  congr 1
  rw [← card_fiber_mk'_eq q, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **`|H| = |N| · |H/N|`** (`N ◁ Γ`, `N ≤ H`): the image `H.map (mk' N)` of `H` in `Γ/N` has order
`|H|/|N|`, since the restriction `mk' N |_H : ↥H → ↥(H.map (mk' N))` has kernel `N` and is onto
(Noether's first isomorphism, `quotientKerEquivRange`).  The `|H|⁻¹·|N| = |H/N|⁻¹` normalization
(step 3) of the (8.4.d) induction-inflation commute (issue 1012, B2). -/
theorem card_eq_card_subgroup_mul_card_map_mk' {Γ : Type*} [Group Γ] [Finite Γ]
    {N H : Subgroup Γ} [N.Normal] (hNH : N ≤ H) :
    Nat.card ↥H = Nat.card ↥N * Nat.card ↥(H.map (QuotientGroup.mk' N)) := by
  have : Fintype Γ := Fintype.ofFinite Γ
  set φ := (QuotientGroup.mk' N).comp H.subtype with hφ
  have hrange : φ.range = H.map (QuotientGroup.mk' N) := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : φ.ker = N.subgroupOf H := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff (h : Γ)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrange, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv, mul_comm]

/-- **Induction-inflation commute** (B2 crux, for `f = mk' N`): for `N ◁ Γ`, `N ≤ H`, the induced
character of the inflated `compHom ((mk' N).subgroupMap H) χ̄` on `Γ` equals the inflation
`compHom (mk' N)` of the induced character of `χ̄` on the image `H.map (mk' N) ⊆ Γ/N`.

Term-by-term equality (`induceTerm_compHom_subgroupMap`), the `|N|`-fold fiberwise sum
(`sum_comp_mk'_eq`), and the `|H| = |N|·|H/N|` normalization
(`card_eq_card_subgroup_mul_card_map_mk'`) combine to cancel the `|N|` factor.  This is the
character-level engine of Peterfalvi's (8.4.d) identification of `𝒮(H₀)` with the `M/H₀`-induction
family (issue 1012, B2). -/
theorem induce_compHom_subgroupMap_mk' {Γ : Type*} [Group Γ] [Fintype Γ] (N : Subgroup Γ) [N.Normal]
    [DecidablePred (· ∈ N)] {H : Subgroup Γ} (hNH : N ≤ H)
    [Invertible (Nat.card ↥H : ℂ)] [Invertible (Nat.card ↥(H.map (QuotientGroup.mk' N)) : ℂ)]
    (χbar : ClassFunction ↥(H.map (QuotientGroup.mk' N)) ℂ) :
    ClassFunction.induce H (ClassFunction.compHom ((QuotientGroup.mk' N).subgroupMap H) χbar)
      = ClassFunction.compHom (QuotientGroup.mk' N)
          (ClassFunction.induce (H.map (QuotientGroup.mk' N)) χbar) := by
  have hker : (QuotientGroup.mk' N).ker ≤ H := by rw [QuotientGroup.ker_mk']; exact hNH
  have : Invertible (Nat.card ↥N : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hnorm : (Nat.card ↥H : ℂ)
      = (Nat.card ↥N : ℂ) * (Nat.card ↥(H.map (QuotientGroup.mk' N)) : ℂ) := by
    rw [← Nat.cast_mul, card_eq_card_subgroup_mul_card_map_mk' hNH]
  have hkey : ⅟(Nat.card ↥H : ℂ) * (Nat.card ↥N : ℂ)
      = ⅟(Nat.card ↥(H.map (QuotientGroup.mk' N)) : ℂ) := by
    rw [invOf_eq_inv, invOf_eq_inv, hnorm, mul_inv, mul_comm ((Nat.card ↥N : ℂ)⁻¹), mul_assoc,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), mul_one]
  apply ClassFunction.ext
  intro g
  rw [ClassFunction.compHom_apply, ClassFunction.induce_apply, ClassFunction.induce_apply,
    Finset.sum_congr rfl (fun x _ =>
      induceTerm_compHom_subgroupMap (QuotientGroup.mk' N) hker χbar x g),
    sum_comp_mk'_eq N (fun x' => ClassFunction.induceTerm (H.map (QuotientGroup.mk' N)) χbar x'
      (QuotientGroup.mk' N g)), nsmul_eq_mul, ← mul_assoc, hkey]

open OddOrder.Peterfalvi.S06 in
/-- **Generic chief-factor quotient `Hypothesis`** over a normal `N' ◁ ↥M` with `N' ≤ M'` and the
non-degeneracy `W₁ ⊓ N' = ⊥`, `W₂ ⊄ N'`: the certain-type structural hypothesis
`S06.Hypothesis (↥M ⧸ N')` with `K̄ = M'/N'`, `W̄₁ = W₁ N'/N'`, `W̄₂ = W₂ N'/N'`.  Both the chief
factor kernel `N' = H₀` and the join `N' = H₀ ⊔ C` instantiate this (Coq `PFsection9` `nb_redM`),
the unifying conditions being exactly `N' ◁ M`, `N' ≤ HU`, and (through the non-degeneracy)
`N' ∩ H = H₀`.  `isComplement` from `IsComplement'.map_mk'`, `centralizer_W2` from
`centralizer_W2bar_quotient`, `W2_nontrivial` from `W₂ ⊄ N'` directly. -/
noncomputable def chiefFactorQuotientHypothesisGen [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (_chief : ChiefFactorData data)
    (N' : Subgroup ↥M) [N'.Normal]
    (hN'le : N' ≤ (derivedInG M).subgroupOf M)
    (hW1inf : data.W1.subgroupOf M ⊓ N' = ⊥)
    (hW2notle : ¬ data.W2.subgroupOf M ≤ N')
    (hodd : Odd (Nat.card G))
    (hHall : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1)) :
    Hypothesis (↥M ⧸ N') := by
  haveI := data.typeP.W1_cyclic
  haveI := data.typeP.W2_cyclic
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hW2leM' : data.W2 ≤ derivedInG M :=
    data.typeP.W2_le.trans (le_trans inf_le_right (Subgroup.map_subtype_le _))
  have hW2leM : data.W2 ≤ M := hW2leM'.trans hM'le
  have hKnorm : ((derivedInG M).subgroupOf M).Normal := by
    rw [show (derivedInG M).subgroupOf M = commutator ↥M by
      rw [derivedInG, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective]]
    infer_instance
  have hcardK : Nat.card ↥((derivedInG M).subgroupOf M) = Nat.card ↥(derivedInG M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv
  have hcardW1 : Nat.card ↥(data.W1.subgroupOf M) = Nat.card ↥data.W1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.typeP.W1_le).toEquiv
  have hcopW1 : Nat.Coprime (Nat.card ↥data.W1) (Nat.card ↥N') :=
    hHall.symm.coprime_dvd_right (hcardK ▸ Subgroup.card_dvd_of_le hN'le)
  refine
    { K := ((derivedInG M).subgroupOf M).map (QuotientGroup.mk' N')
      W1 := (data.W1.subgroupOf M).map (QuotientGroup.mk' N')
      W2 := (data.W2.subgroupOf M).map (QuotientGroup.mk' N')
      K_normal := hKnorm.map _ (QuotientGroup.mk'_surjective _)
      isComplement := by
        have hcop : Nat.Coprime (Nat.card ↥((derivedInG M).subgroupOf M))
            (Nat.card ↥(data.W1.subgroupOf M)) := by rw [hcardK, hcardW1]; exact hHall
        exact data.typeP.M_complement.map_mk' hcop N'
      W1_nontrivial := ?_
      W1_cyclic := ?_
      card_coprime :=
        (hHall.coprime_dvd_left (hcardK ▸ Subgroup.card_map_dvd _ _)).coprime_dvd_right
          (hcardW1 ▸ Subgroup.card_map_dvd _ _)
      W2_nontrivial := ?_
      W2_cyclic := ?_
      W2_le_K := Subgroup.map_mono (Subgroup.comap_mono hW2leM')
      centralizer_W2 := fun x hx hx1 => centralizer_W2bar_quotient N' hN'le hcopW1 x hx hx1
      W_odd := ?_ }
  · rw [ne_eq, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    intro hle
    have hbot : data.W1.subgroupOf M = ⊥ :=
      le_bot_iff.mp (le_trans (le_inf le_rfl hle) hW1inf.le)
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    exact data.typeP.W1_nontrivial (disjoint_self.mp (hbot.mono_right data.typeP.W1_le))
  · have : IsCyclic ↥(data.W1.subgroupOf M) :=
      isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe data.typeP.W1_le).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe data.typeP.W1_le).injective
    rw [show (data.W1.subgroupOf M).map (QuotientGroup.mk' N')
        = ((QuotientGroup.mk' N').comp (data.W1.subgroupOf M).subtype).range by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]]
    exact isCyclic_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  · rw [ne_eq, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hW2notle
  · have : IsCyclic ↥data.W2 := data.typeP.W2_cyclic
    have : IsCyclic ↥(data.W2.subgroupOf M) :=
      isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hW2leM).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hW2leM).injective
    rw [show (data.W2.subgroupOf M).map (QuotientGroup.mk' N')
        = ((QuotientGroup.mk' N').comp (data.W2.subgroupOf M).subtype).range by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]]
    exact isCyclic_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  · have hdvd : Nat.card ↥(((data.W1.subgroupOf M).map (QuotientGroup.mk' N'))
        ⊔ ((data.W2.subgroupOf M).map (QuotientGroup.mk' N')))
        ∣ Nat.card G :=
      dvd_trans (Subgroup.card_subgroup_dvd_card _)
        (dvd_trans (Subgroup.index_dvd_card _) (Subgroup.card_subgroup_dvd_card M))
    rcases Nat.even_or_odd (Nat.card ↥(((data.W1.subgroupOf M).map (QuotientGroup.mk' N'))
        ⊔ ((data.W2.subgroupOf M).map (QuotientGroup.mk' N')))) with he | ho
    · have h2G : 2 ∣ Nat.card G := dvd_trans he.two_dvd hdvd
      rw [Nat.odd_iff] at hodd
      omega
    · exact ho

/-- The `K` of the generic `chiefFactorQuotientHypothesisGen` is the `mk' N'`-image of the §9
induction carrier `HU = huSub` (`huSub_eq_derivedInG_subgroupOf`); same bridge as the `H₀` case,
generic in `N'`. -/
theorem chiefFactorQuotientHypothesisGen_K_eq [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (N' : Subgroup ↥M) [N'.Normal]
    (hN'le : N' ≤ (derivedInG M).subgroupOf M)
    (hW1inf : data.W1.subgroupOf M ⊓ N' = ⊥)
    (hW2notle : ¬ data.W2.subgroupOf M ≤ N')
    (hodd : Odd (Nat.card G))
    (hHall : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1)) :
    (chiefFactorQuotientHypothesisGen chief N' hN'le hW1inf hW2notle hodd hHall).K
      = (huSub data).map (QuotientGroup.mk' N') := by
  change ((derivedInG M).subgroupOf M).map (QuotientGroup.mk' N')
      = (huSub data).map (QuotientGroup.mk' N')
  rw [huSub_eq_derivedInG_subgroupOf]

/-- **(9.7) span step** (general form): in an irreducible `A`-action on a group `H` (every
`A`-invariant subgroup is `⊥` or `⊤`), any nonzero subgroup `S₀` generates `H` under its
`A`-orbit — `⨆_{a} φ(a) • S₀ = ⊤`.  The orbit join is `A`-invariant (reindex `a ↦ h·a`) and
contains `S₀ ≠ ⊥`, hence is `⊤`.  Applied to the `U W₁`-irreducible chief factor `H̄` with `S₀` a
minimal `U`-invariant piece, this shows `H̄` is spanned by the `W₁`-conjugates of `S₀` — the entry
point to the Clifford decomposition. -/
theorem iSup_smul_eq_top_of_irreducible {A H : Type*} [Group A] [Group H] {φ : A →* MulAut H}
    (hirr : ∀ J : Subgroup H, IsAInvariant φ J → J = ⊥ ∨ J = ⊤)
    {S₀ : Subgroup H} (hS₀ : S₀ ≠ ⊥) :
    ⨆ (a : A), φ a • S₀ = ⊤ := by
  set T := ⨆ (a : A), φ a • S₀ with hT
  -- `T` is `φ`-invariant: `φ h • T = ⨆ a, φ (h·a) • S₀ = T` by reindexing `a ↦ h·a`.
  have hTinv : IsAInvariant φ T := by
    intro h
    have h1 : φ h • T = ⨆ (a : A), φ (h * a) • S₀ := by
      rw [hT, pointwise_mulAut_smul_eq_map, Subgroup.map_iSup]
      exact iSup_congr fun a => by
        rw [← pointwise_mulAut_smul_eq_map, smul_smul, ← map_mul]
    rw [h1]
    exact le_antisymm (iSup_le fun a => le_iSup_of_le (h * a) le_rfl)
      (iSup_le fun a => le_iSup_of_le (h⁻¹ * a)
        (le_of_eq (by rw [← mul_assoc, mul_inv_cancel, one_mul])))
  -- `T ≠ ⊥` (contains the `a = 1` term `S₀`), so irreducibility forces `T = ⊤`.
  have hTne : T ≠ ⊥ := by
    intro hbot
    refine hS₀ (le_bot_iff.mp (hbot ▸ ?_))
    have := le_iSup (fun a : A => φ a • S₀) 1
    rwa [map_one, one_smul] at this
  exact (hirr T hTinv).resolve_left hTne

/-- **(9.7) order step** (general form): a finite group `K` whose elements pairwise commute (e.g. an
elementary abelian `p`-group) that is the join `⨆ i, S i` of a family of `φ`-invariant subgroups,
each either trivial or `φ`-irreducible of a common order `n`, has order a power of `n`.

Extract a maximal `SupIndep` subfamily of the nonzero pieces.  By irreducibility it still spans `K`:
any piece meets the partial join in a `φ`-invariant subgroup `≤` the piece, hence `⊥` or the whole
piece — and `⊥` would let us enlarge the subfamily, contradicting maximality.  An independent
commuting spanning family realises `K` as the internal direct product `∏ ↥(S i)` (via
`Subgroup.noncommPiCoprod`, injective from independence and surjective from spanning), so
`|K| = ∏ |S i| = ∏ n = n ^ k`.

Applied to the chief factor `H̄` under the restricted `U`-action, with the pieces the `U W₁`-orbit
of
a minimal `U`-invariant `S₀` (each `U`-irreducible of order `|S₀| = p^d`), this gives
`|H̄| = (p^d)^k`,
i.e. `q = d·k` — the divisibility `d ∣ q` underlying the Clifford dichotomy (`q` prime ⟹
`d ∈ {1, q}`). -/
theorem exists_supIndep_aInvariant_family_of_iSup {K : Type*} [Group K] [Finite K]
    {A : Type*} [Group A] {φ : A →* MulAut K} {ι : Type*} [Finite ι]
    {S : ι → Subgroup K} {n : ℕ}
    (hcomm : ∀ x y : K, Commute x y)
    (hspan : ⨆ i, S i = ⊤)
    (hinv : ∀ i, IsAInvariant φ (S i))
    (hirr : ∀ i, ∀ J : Subgroup K, IsAInvariant φ J → J ≤ S i → J = ⊥ ∨ J = S i)
    (hcard : ∀ i, S i ≠ ⊥ → Nat.card ↥(S i) = n) :
    ∃ t : Finset ι, t.SupIndep S ∧ (∀ i ∈ t, S i ≠ ⊥) ∧ (⨆ i ∈ t, S i = ⊤) ∧
      Nat.card K = n ^ t.card := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  -- `K` is abelian, so its subgroup lattice is modular (used to enlarge `SupIndep` families).
  let : CommGroup K := { (inferInstance : Group K) with mul_comm := fun a b => (hcomm a b).eq }
  -- Candidate finsets: `SupIndep` subfamilies of nonzero pieces.
  set cands : Finset (Finset ι) :=
    Finset.univ.filter (fun t => t.SupIndep S ∧ ∀ i ∈ t, S i ≠ ⊥) with hcands
  have hmem_cands : ∀ {t : Finset ι}, t ∈ cands ↔ t.SupIndep S ∧ ∀ i ∈ t, S i ≠ ⊥ := by
    intro t; rw [hcands, Finset.mem_filter]; exact and_iff_right (Finset.mem_univ _)
  have hempty : (∅ : Finset ι) ∈ cands :=
    hmem_cands.mpr ⟨Finset.supIndep_empty S, by simp⟩
  -- Choose a candidate of maximal cardinality.
  obtain ⟨t, ht_mem, ht_max⟩ := cands.exists_max_image Finset.card ⟨∅, hempty⟩
  obtain ⟨ht_si, ht_ne⟩ := hmem_cands.mp ht_mem
  -- The maximal subfamily already spans `K`.
  have hspan_t : ⨆ i ∈ t, S i = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hspan]
    refine iSup_le fun j => ?_
    by_cases hj0 : S j = ⊥
    · rw [hj0]; exact bot_le
    · have hBinv : IsAInvariant φ (⨆ i ∈ t, S i) :=
        IsAInvariant.iSup fun i => IsAInvariant.iSup fun _ => hinv i
      rcases hirr j (S j ⊓ ⨆ i ∈ t, S i) (IsAInvariant.inf (hinv j) hBinv) inf_le_left with
        hbot | heq
      · -- `S j ⊓ B = ⊥`: enlarging `t` by `j` stays a candidate, contradicting maximality.
        exfalso
        have hjt : j ∉ t := fun hj => hj0 (by
          have hle : S j ≤ ⨆ i ∈ t, S i :=
            le_iSup_of_le j (le_iSup_of_le hj le_rfl)
          rwa [inf_eq_left.mpr hle] at hbot)
        have hdisj : Disjoint (S j) (t.sup S) := by
          rw [Finset.sup_eq_iSup]; exact disjoint_iff.mpr hbot
        have hins_ne : ∀ i ∈ insert j t, S i ≠ ⊥ := by
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact hj0
          · exact ht_ne i hi
        have hins_mem : insert j t ∈ cands := hmem_cands.mpr ⟨ht_si.insert hdisj, hins_ne⟩
        have hle_card := ht_max (insert j t) hins_mem
        rw [Finset.card_insert_of_notMem hjt] at hle_card
        omega
      · exact inf_eq_left.mp heq
  -- The independent, commuting, spanning subfamily makes `K` the internal direct product `∏ S i`.
  have hcomm_pair : Pairwise fun i j : (t : Finset ι) =>
      ∀ x y : K, x ∈ S ↑i → y ∈ S ↑j → Commute x y :=
    fun _ _ _ x y _ _ => hcomm x y
  have hrange : (Subgroup.noncommPiCoprod hcomm_pair).range = ⊤ := by
    rw [Subgroup.noncommPiCoprod_range, iSup_subtype]; exact hspan_t
  have hbij : Function.Bijective (Subgroup.noncommPiCoprod hcomm_pair) :=
    ⟨Subgroup.injective_noncommPiCoprod_of_iSupIndep ht_si.independent,
      MonoidHom.range_eq_top.mp hrange⟩
  refine ⟨t, ht_si, ht_ne, hspan_t, ?_⟩
  have hfac : ∀ i : (t : Finset ι), Nat.card ↥(S ↑i) = n := fun i => hcard ↑i (ht_ne ↑i i.2)
  calc Nat.card K = Nat.card (∀ i : (t : Finset ι), ↥(S ↑i)) :=
        (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
    _ = ∏ i : (t : Finset ι), Nat.card ↥(S ↑i) := Nat.card_pi
    _ = ∏ _i : (t : Finset ι), n := Finset.prod_congr rfl (fun i _ => hfac i)
    _ = n ^ t.card := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]

/-- **(9.7) order step** (cardinality corollary): a finite group `K` whose elements pairwise
commute,
the join `⨆ i, S i` of `φ`-invariant subgroups each trivial or `φ`-irreducible of common order `n`,
has order a power of `n`.  Forgets the `SupIndep` partition of
`exists_supIndep_aInvariant_family_of_iSup`. -/
theorem card_eq_pow_of_iSup_aInvariant_irreducible {K : Type*} [Group K] [Finite K]
    {A : Type*} [Group A] {φ : A →* MulAut K} {ι : Type*} [Finite ι]
    {S : ι → Subgroup K} {n : ℕ}
    (hcomm : ∀ x y : K, Commute x y)
    (hspan : ⨆ i, S i = ⊤)
    (hinv : ∀ i, IsAInvariant φ (S i))
    (hirr : ∀ i, ∀ J : Subgroup K, IsAInvariant φ J → J ≤ S i → J = ⊥ ∨ J = S i)
    (hcard : ∀ i, S i ≠ ⊥ → Nat.card ↥(S i) = n) :
    ∃ k, Nat.card K = n ^ k :=
  let ⟨t, _, _, _, h⟩ := exists_supIndep_aInvariant_family_of_iSup hcomm hspan hinv hirr hcard
  ⟨t.card, h⟩

/-- **Clifford orbit, invariance.** If `U ◁ A` acts on `K` through `φ` and `S₀` is `U`-invariant
(invariant under `φ` restricted to `U`), then every `A`-translate `φ a • S₀` is again `U`-invariant:
for `u ∈ U`, `φ u • (φ a • S₀) = φ (u·a) • S₀ = φ a • (φ (a⁻¹·u·a) • S₀) = φ a • S₀` since
`a⁻¹·u·a ∈ U`. -/
theorem isAInvariant_comp_subtype_pointwise_smul {A K : Type*} [Group A] [Group K]
    {φ : A →* MulAut K} {U : Subgroup A} (hU : U.Normal)
    {S₀ : Subgroup K} (hS₀ : IsAInvariant (φ.comp U.subtype) S₀) (a : A) :
    IsAInvariant (φ.comp U.subtype) (φ a • S₀) := by
  intro u
  change φ ↑u • (φ a • S₀) = φ a • S₀
  have hmem : a⁻¹ * (↑u : A) * a ∈ U := by
    have h := hU.conj_mem (↑u) u.2 a⁻¹; rwa [inv_inv] at h
  rw [smul_smul, ← map_mul,
    show (↑u : A) * a = a * (a⁻¹ * ↑u * a) by group, map_mul, ← smul_smul]
  congr 1
  exact hS₀ ⟨a⁻¹ * ↑u * a, hmem⟩

/-- **Clifford orbit, irreducibility.** `A`-translates of a `U`-irreducible (minimal nonzero
`U`-invariant) subgroup `S₀` are again `U`-irreducible: a `U`-invariant `J ≤ φ a • S₀` pulls back to
`φ a⁻¹ • J ≤ S₀`, which is `⊥` or `S₀`, so `J = φ a • (φ a⁻¹ • J)` is `⊥` or `φ a • S₀`. -/
theorem forall_aInvariant_le_pointwise_smul {A K : Type*} [Group A] [Group K]
    {φ : A →* MulAut K} {U : Subgroup A} (hU : U.Normal) {S₀ : Subgroup K}
    (hirr₀ : ∀ J : Subgroup K, IsAInvariant (φ.comp U.subtype) J → J ≤ S₀ → J = ⊥ ∨ J = S₀)
    (a : A) (J : Subgroup K) (hJinv : IsAInvariant (φ.comp U.subtype) J) (hJle : J ≤ φ a • S₀) :
    J = ⊥ ∨ J = φ a • S₀ := by
  have hback : φ a • (φ a⁻¹ • J) = J := by
    rw [smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  have hJ'inv : IsAInvariant (φ.comp U.subtype) (φ a⁻¹ • J) :=
    isAInvariant_comp_subtype_pointwise_smul hU hJinv a⁻¹
  have hJ'le : φ a⁻¹ • J ≤ S₀ := by
    have h := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := φ a⁻¹)).mpr hJle
    rwa [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h
  rcases hirr₀ (φ a⁻¹ • J) hJ'inv hJ'le with h | h
  · exact Or.inl (by rw [← hback, h, Subgroup.smul_bot])
  · exact Or.inr (by rw [← hback, h])

/-- **Clifford orbit, order.** Translation by an automorphism preserves order: `|φ a • S| = |S|`. -/
theorem card_pointwise_smul {A K : Type*} [Group A] [Group K] [Finite K]
    (φ : A →* MulAut K) (a : A) (S : Subgroup K) :
    Nat.card ↥(φ a • S) = Nat.card ↥S :=
  (Nat.card_congr (Subgroup.equivMapOfInjective S (φ a).toMonoidHom (φ a).injective).toEquiv).symm

/-- **`U W`-orbit collapses to the `W`-orbit** for a `U`-invariant `S₀` (`U ◁ A`).  Since each
`W`-conjugate `φ w • S₀` is again `U`-invariant (`isAInvariant_comp_subtype_pointwise_smul`), a
`U W`-element `a = u·w` gives `φ a • S₀ = φ u • (φ w • S₀) = φ w • S₀`.  Hence the spanning
`U W`-orbit of `S₀` already equals its `W`-orbit — the elementary span step of the `(9.7)`
decomposition `H̄ = ⊕_{w∈W1} S₀^w`. -/
theorem iSup_phi_smul_eq_iSup_W_of_normal {A K : Type*} [Group A] [Group K]
    {φ : A →* MulAut K} {U W : Subgroup A} (hU : U.Normal) {S₀ : Subgroup K}
    (hS₀ : IsAInvariant (φ.comp U.subtype) S₀) :
    ⨆ a : ↥(U ⊔ W), φ ↑a • S₀ = ⨆ w : ↥W, φ ↑w • S₀ := by
  have := hU
  apply le_antisymm
  · rw [iSup_le_iff]
    rintro ⟨a, ha⟩
    have ha' : a ∈ (↑U * ↑W : Set A) := by rw [← Subgroup.normal_mul]; exact ha
    obtain ⟨u, hu, w, hw, huw⟩ := Set.mem_mul.mp ha'
    change φ a • S₀ ≤ ⨆ w' : ↥W, φ ↑w' • S₀
    rw [← huw, map_mul, mul_smul]
    have key : φ u • (φ w • S₀) = φ w • S₀ :=
      isAInvariant_comp_subtype_pointwise_smul hU hS₀ w ⟨u, hu⟩
    rw [key]
    exact le_iSup (fun w' : ↥W => φ ↑w' • S₀) ⟨w, hw⟩
  · rw [iSup_le_iff]
    rintro ⟨w, hw⟩
    exact le_iSup (fun a : ↥(U ⊔ W) => φ ↑a • S₀) ⟨w, Subgroup.mem_sup_right hw⟩

open OddOrder.RepresentationTheory in
/-- The descended representation `elabRepresentation p φ` on `Additive K` is irreducible exactly
when
the `φ`-action is irreducible at the subgroup level (`K` nontrivial; every `φ`-invariant subgroup of
`K` is `⊥` or `⊤`).  `ZMod p`-submodules of `Additive K` are the subgroups of `K`
(`AddSubgroup.toZModSubmodule`/`toSubgroup'`) and the action correspondence is
`elabRepresentation_apply`.  Stated as `IsSimpleOrder (Subrepresentation …)` (= `IsIrreducible`,
definitionally) to avoid pulling in the `Field (ZMod p)` instance and its `ZMod`-semiring
diamond. -/
theorem elabRepresentation_isIrreducible {A K : Type*} [Group A] [CommGroup K] {p : ℕ}
    [Module (ZMod p) (Additive K)] {φ : A →* MulAut K} (hnt : Nontrivial K)
    (hirr : ∀ J : Subgroup K, IsAInvariant φ J → J = ⊥ ∨ J = ⊤) :
    IsSimpleOrder (Subrepresentation (elabRepresentation p φ)) := by
  classical
  set Φ : Submodule (ZMod p) (Additive K) ≃o Subgroup K :=
    (AddSubgroup.toZModSubmodule p).symm.trans AddSubgroup.toSubgroup' with hΦ
  have hmem : ∀ (W : Submodule (ZMod p) (Additive K)) (x : K),
      x ∈ Φ W ↔ Additive.ofMul x ∈ W := fun W x => by
    simp only [hΦ, OrderIso.trans_apply, AddSubgroup.mem_toSubgroup',
      AddSubgroup.toZModSubmodule_symm, Submodule.mem_toAddSubgroup]
  have hbot_ne_top : (⊥ : Subrepresentation (elabRepresentation p φ)) ≠ ⊤ := by
    have : Nontrivial (Additive K) := hnt
    exact fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  have : Nontrivial (Subrepresentation (elabRepresentation p φ)) := ⟨⊥, ⊤, hbot_ne_top⟩
  refine IsSimpleOrder.of_forall_eq_top fun S hSne => ?_
  have hJinv : IsAInvariant φ (Φ S.toSubmodule) := by
    rw [isAInvariant_iff_smul_mem]
    intro a x hx
    rw [hmem] at hx ⊢
    exact S.apply_mem_toSubmodule a hx
  rcases hirr _ hJinv with hJbot | hJtop
  · refine absurd (Subrepresentation.toSubmodule_injective (show S.toSubmodule = ⊥ from ?_)) hSne
    rw [← Φ.symm_apply_apply S.toSubmodule, hJbot]; exact Φ.symm.map_bot
  · refine Subrepresentation.toSubmodule_injective (show S.toSubmodule = ⊤ from ?_)
    rw [← Φ.symm_apply_apply S.toSubmodule, hJtop]; exact Φ.symm.map_top

set_option backward.isDefEq.respectTransparency false in
open OddOrder.RepresentationTheory Representation in
/-- **Thin subgroup→module Singer adapter** (issue 9000 dedup): a `φ`-irreducible, faithful
action of `A` on the elementary abelian `p`-group `K` makes `(elabRepresentation p φ).asModule`
a *simple* `𝔽ₚ[A]`-module with the faithfulness transported to `𝔽ₚ[A]`-module terms.  This is
the single subgroup→module conversion through which the §9 case-(b) results cite the canonical
module-level Singer lemmas of the shared σ-theory leaves (`SingerField` / `SingerLineBound`);
the former subgroup-level Singer wrappers are retired (hub ruling, issue 9000). -/
theorem elabRepresentation_isSimpleModule_and_faithful
    {A K : Type*} [Group A] [CommGroup K] [Finite K] {p : ℕ}
    [Module (ZMod p) (Additive K)] {φ : A →* MulAut K}
    (hnt : Nontrivial K)
    (hirr : ∀ J : Subgroup K, IsAInvariant φ J → J = ⊥ ∨ J = ⊤)
    (hfaith : ∀ a : A, (∀ x : K, φ a x = x) → a = 1) :
    IsSimpleModule (MonoidAlgebra (ZMod p) A) (elabRepresentation p φ).asModule ∧
      ∀ a : A, (∀ y : (elabRepresentation p φ).asModule,
        MonoidAlgebra.of (ZMod p) A a • y = y) → a = 1 := by
  have hirrep : IsSimpleOrder (Subrepresentation (elabRepresentation p φ)) :=
    elabRepresentation_isIrreducible hnt hirr
  refine ⟨?_, ?_⟩
  · rw [isSimpleModule_iff]
    exact (OrderIso.isSimpleOrder_iff
      Subrepresentation.subrepresentationSubmoduleOrderIso).mp hirrep
  -- Faithfulness in `𝔽ₚ[A]`-module terms: `of a • y = y` for all `y` ⟹ `φ a x = x` for all `x`.
  · intro a ha
    refine hfaith a fun x => ?_
    have key : (elabRepresentation p φ).asModuleEquiv
        (MonoidAlgebra.of (ZMod p) A a •
          (elabRepresentation p φ).asModuleEquiv.symm (Additive.ofMul x)) = Additive.ofMul x := by
      rw [ha]; exact (elabRepresentation p φ).asModuleEquiv.apply_symm_apply _
    rw [asModuleEquiv_map_smul, asAlgebraHom_of,
      (elabRepresentation p φ).asModuleEquiv.apply_symm_apply, elabRepresentation_apply] at key
    exact Additive.ofMul.injective key

/-- **Fixed-point-freeness of an irreducible action with commuting image.**  If a group `A` acts on
a group `K` via `φ : A →* MulAut K` whose image is commutative (`hcomm : Commute (φ a) (φ b)`) and
irreducible (the only `A`-invariant subgroups are `⊥`/`⊤`, `hirr`), then every `a` with nontrivial
action `φ a ≠ 1` acts **fixed-point-freely**: `φ a x = x → x = 1`.

The fixed-point subgroup `Fix(φ a) = {y | φ a y = y}` is `A`-invariant — for `y` fixed by `φ a` and
any `b`, `φ a (φ b y) = φ b (φ a y) = φ b y` since `φ a`, `φ b` commute (`hcomm`) — so by
irreducibility it is `⊥` or `⊤`, and `⊤` would make `φ a = 1`.  This is the structural core of the
Frobenius action `H̄ ⋊ Ū` of Peterfalvi (9.7)(b)/(9.9): no Singer field model is needed, only the
irreducibility already supplied by Clifford case (b) and the commuting image (`U/C_U(H̄)` abelian).
The hypothesis is on the *image* (`Commute (φ a) (φ b)`), not on `A`, so it applies to the
`U`-action even though `U` itself is non-abelian. -/
theorem fixedPointFree_of_aInvariant_irreducible_comm
    {A K : Type*} [Group A] [Group K] {φ : A →* MulAut K}
    (hcomm : ∀ a b : A, Commute (φ a) (φ b))
    (hirr : ∀ J : Subgroup K, IsAInvariant φ J → J = ⊥ ∨ J = ⊤)
    (a : A) (ha : φ a ≠ 1) (x : K) (hx : φ a x = x) : x = 1 := by
  -- The fixed-point subgroup of `φ a`.
  let F : Subgroup K :=
    { carrier := {y | φ a y = y}
      one_mem' := map_one (φ a)
      mul_mem' := fun {y z} hy hz => by
        change φ a (y * z) = y * z
        rw [map_mul, show φ a y = y from hy, show φ a z = z from hz]
      inv_mem' := fun {y} hy => by
        change φ a y⁻¹ = y⁻¹
        rw [map_inv, show φ a y = y from hy] }
  have hxF : x ∈ F := hx
  -- `Fix(φ a)` is `A`-invariant: `φ a` commutes with every `φ b` (image of `φ` abelian).
  have hAinv : IsAInvariant φ F := isAInvariant_iff_smul_mem.mpr fun b y hy => by
    change φ a (φ b y) = φ b y
    have he : (φ a * φ b) y = (φ b * φ a) y := by rw [(hcomm a b).eq]
    rw [MulAut.mul_apply, MulAut.mul_apply, show φ a y = y from hy] at he
    exact he
  rcases hirr F hAinv with hbot | htop
  · -- `Fix(φ a) = ⊥`: the fixed point `x` is trivial.
    rw [hbot] at hxF; exact Subgroup.mem_bot.mp hxF
  · -- `Fix(φ a) = ⊤`: `φ a` is the identity, contradicting `φ a ≠ 1`.
    exact absurd (MulEquiv.ext fun y => by
      have hy : y ∈ F := htop ▸ Subgroup.mem_top y
      rw [MulAut.one_apply]; exact hy) ha

/-- **A fixed-point-free automorphism leaves no nontrivial character invariant** (abelian case).
If `α` is a fixed-point-free automorphism of a finite abelian group `K`, then any homomorphism
`θ : K →* M'` to a commutative group that is `α`-invariant (`θ (α x) = θ x` for all `x`) is trivial.

The displacement `x ↦ x / α x` is surjective (`MonoidHom.FixedPointFree.commutatorMap_surjective`),
and `θ (x / α x) = θ x / θ (α x) = 1` by invariance, so `θ` vanishes on all of `K`.  This is the
**character-side fixed-point-freeness** of the Frobenius action `H̄ ⋊ Ū` — for a nontrivial linear
character `θ ∈ Irr(H̄)` and `g ∉ C = C_U(H̄)` (so `φ_U(g)` is FPF by
`chiefFactor_caseB_action_fpf`),
`θ` is *not* `φ_U(g)`-invariant, giving the inertia `I_U(θ) = C` underlying Peterfalvi (9.9). -/
theorem eq_one_of_invariant_of_fixedPointFree {K M' : Type*} [Group K] [Finite K] [CommGroup M']
    {α : MulAut K} (hα : MonoidHom.FixedPointFree α) {θ : K →* M'}
    (hinv : ∀ x : K, θ (α x) = θ x) : θ = 1 := by
  ext y
  obtain ⟨x, hx⟩ := hα.commutatorMap_surjective y
  rw [MonoidHom.commutatorMap_apply] at hx
  rw [MonoidHom.one_apply, ← hx, map_div, hinv, div_self']

open OddOrder.RepresentationTheory Representation in
/-- **An irreducible character of a finite abelian group is a linear character.**  For a finite
commutative group `Γ`, any irreducible character `φ` (`IsIrreducibleCharacter`) arises from a
homomorphism `θ : Γ →* ℂˣ` with `(θ g : ℂ) = φ g`.

Irreducible representations of a commutative group are `1`-dimensional
(`finrank_eq_one_of_isMulCommutative`), so each `ρ g` acts as a nonzero scalar `θ g` (extracted by
`exists_smul_eq_of_finrank_eq_one`), and the character `φ g = trace(ρ g) = θ g`.  This abelian
`Irr ↔ Hom(·, ℂˣ)` bridge lets `eq_one_of_invariant_of_fixedPointFree` apply to genuine irreducible
characters of the abelian chief factor `H̄`, giving the inertia `I_U(θ) = C` of Peterfalvi (9.9)
without realizing `H̄` as a subgroup. -/
theorem exists_units_monoidHom_of_isIrreducibleCharacter_of_isMulCommutative
    {Γ : Type*} [Group Γ] [Finite Γ] [IsMulCommutative Γ]
    {φ : ClassFunction Γ ℂ} (hφ : IsIrreducibleCharacter φ) :
    ∃ θ : Γ →* ℂˣ, ∀ g, (θ g : ℂ) = φ g := by
  obtain ⟨V, _, _, _, ρ, hρ, hχ⟩ := hφ
  have : ρ.IsIrreducible := hρ
  have hfin : Module.finrank ℂ V = 1 :=
    Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative ρ
  have : FiniteDimensional ℂ V := .of_finrank_eq_succ hfin
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hfin
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  -- `span {x} = ⊤` (1-dimensional), so a linear map is determined by its value on `x`.
  have hspan : Submodule.span ℂ ({x} : Set V) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hfin]; exact finrank_span_singleton hx
  -- The scalar `c g` with `ρ g x = c g • x`.
  choose c hc using fun g => exists_smul_eq_of_finrank_eq_one hfin hx ((ρ g) x)
  -- `ρ g = c g • id` (agree on the spanning vector `x`).
  have hρeq : ∀ g, (ρ g : V →ₗ[ℂ] V) = c g • LinearMap.id := fun g => by
    refine LinearMap.ext_on hspan fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy; subst hy
    simpa [LinearMap.smul_apply] using (hc g).symm
  -- `c` is multiplicative and unital, and never zero (`ρ g` is invertible).
  have hc1 : c 1 = 1 := by
    have h := hc 1
    rw [map_one, Module.End.one_apply] at h
    have h2 : c 1 • x = (1 : ℂ) • x := by rw [one_smul]; exact h
    exact smul_left_injective ℂ hx h2
  have hcmul : ∀ g h, c (g * h) = c g * c h := fun g h => by
    have e1 : (ρ (g * h)) x = (c g * c h) • x := by
      rw [map_mul]
      change (ρ g) ((ρ h) x) = (c g * c h) • x
      rw [← hc h, map_smul, ← hc g, smul_smul, mul_comm]
    have key : c (g * h) • x = (c g * c h) • x := by rw [hc (g * h)]; exact e1
    exact smul_left_injective ℂ hx key
  have hcne : ∀ g, c g ≠ 0 := fun g hc0 => by
    have hρ0 : (ρ g : V →ₗ[ℂ] V) = 0 := by rw [hρeq g, hc0, zero_smul]
    have h1 : (ρ (g⁻¹) * ρ g : V →ₗ[ℂ] V) = ρ 1 := by rw [← map_mul, inv_mul_cancel]
    rw [hρ0, mul_zero, map_one] at h1
    exact zero_ne_one h1
  -- `φ g = trace(ρ g) = c g · finrank = c g`.
  have hφc : ∀ g, φ g = c g := fun g => by
    have hco : φ g = LinearMap.trace ℂ V (ρ g) := congrFun hχ g
    rw [hco, hρeq g, map_smul, LinearMap.trace_id, hfin]
    simp
  exact ⟨{ toFun := fun g => Units.mk0 (c g) (hcne g)
           map_one' := Units.ext (by simpa using hc1)
           map_mul' := fun g h => Units.ext (by simpa using hcmul g h) },
        fun g => by simpa using (hφc g).symm⟩

set_option backward.isDefEq.respectTransparency false in
open OddOrder.RepresentationTheory Representation in
/-- **Subgroup→module transport of a fixed-point-free `MulAut`** (issue 9000 dedup companion of
`elabRepresentation_isSimpleModule_and_faithful`): a `σ : MulAut K` carries to an additive
automorphism `τ` of `(elabRepresentation p φ).asModule` with the commuting-with-`φ` condition
transported to `𝔽ₚ[A]`-module terms — the `(σ, hfpf)` input shape of the canonical module-level
`coprime_card_sub_one_of_faithful_irreducible_comm_fpf` (shared `SingerField` leaf). -/
theorem exists_addEquiv_asModule_fpf
    {A K : Type*} [Group A] [CommGroup K] [Finite K] {p : ℕ}
    [Module (ZMod p) (Additive K)] {φ : A →* MulAut K}
    (σ : MulAut K)
    (hfpf : ∀ a : A, (∀ x : K, σ (φ a x) = φ a (σ x)) → a = 1) :
    ∃ τ : (elabRepresentation p φ).asModule ≃+ (elabRepresentation p φ).asModule,
      ∀ a : A, (∀ y : (elabRepresentation p φ).asModule,
        τ (MonoidAlgebra.of (ZMod p) A a • y)
          = MonoidAlgebra.of (ZMod p) A a • τ y) → a = 1 := by
  -- The `MulAut K`-action `σ`, carried to an additive automorphism of `asModule = Additive K`.
  let τ : (elabRepresentation p φ).asModule ≃+ (elabRepresentation p φ).asModule :=
    { toFun := fun z => Additive.ofMul (σ (Additive.toMul z))
      invFun := fun z => Additive.ofMul (σ.symm (Additive.toMul z))
      left_inv := fun z => by simp
      right_inv := fun z => by simp
      map_add' := fun z w => by
        change Additive.ofMul (σ (Additive.toMul (z + w)))
          = Additive.ofMul (σ (Additive.toMul z)) + Additive.ofMul (σ (Additive.toMul w))
        rw [show Additive.toMul (z + w) = Additive.toMul z * Additive.toMul w from rfl, map_mul]
        rfl }
  refine ⟨τ, ?_⟩
  -- The action `of a • z` is `ρ a z` (the descended representation).
  have hact : ∀ (a : A) (z : (elabRepresentation p φ).asModule),
      MonoidAlgebra.of (ZMod p) A a • z = (elabRepresentation p φ) a z := by
    intro a z
    have h2 := asModuleEquiv_map_smul (ρ := elabRepresentation p φ)
      (MonoidAlgebra.of (ZMod p) A a) z
    rw [asAlgebraHom_of] at h2
    -- `asModuleEquiv` is `LinearEquiv.refl`, so both sides are definitionally unchanged.
    exact h2
  -- Fixed-point-freeness in `𝔽ₚ[A]`-module terms.
  intro a ha
  apply hfpf a
  intro x
  have h := ha (Additive.ofMul x)
  rw [hact, hact, elabRepresentation_apply] at h
  have hτ : ∀ w : K, τ (Additive.ofMul w) = Additive.ofMul (σ w) := fun w => rfl
  rw [hτ, hτ, elabRepresentation_apply] at h
  exact Additive.ofMul.injective h

set_option backward.isDefEq.respectTransparency false in
open OddOrder.RepresentationTheory Representation in
/-- **Thin subgroup-level entry to the canonical Singer cyclicity+divisibility** (issue 9000
dedup): the subgroup→module conversion `elabRepresentation_isSimpleModule_and_faithful` followed
by the single cite of the shared `SingerField` lemma
`isCyclic_and_card_dvd_of_faithful_irreducible_comm`.  No Singer content lives here — the
`asModule` types must be elaborated under the `[Module (ZMod p) (Additive K)]` binder, which is
why the two steps are packaged once instead of being inlined at every §9 use site. -/
theorem singerAdapter_isCyclic_card_dvd
    {A K : Type*} [Group A] [Finite A] [CommGroup K] [Finite K] {p : ℕ}
    [Module (ZMod p) (Additive K)] {φ : A →* MulAut K}
    (hcomm : ∀ a b : A, a * b = b * a) (hnt : Nontrivial K)
    (hirr : ∀ J : Subgroup K, IsAInvariant φ J → J = ⊥ ∨ J = ⊤)
    (hfaith : ∀ a : A, (∀ x : K, φ a x = x) → a = 1) :
    IsCyclic A ∧ Nat.card A ∣ Nat.card K - 1 := by
  obtain ⟨hsimp, hfaith'⟩ :=
    elabRepresentation_isSimpleModule_and_faithful (p := p) hnt hirr hfaith
  have := hsimp
  have : Finite (elabRepresentation p φ).asModule := ‹Finite K›
  obtain ⟨hcyc, hdvd⟩ := isCyclic_and_card_dvd_of_faithful_irreducible_comm
    (E := A) (M := (elabRepresentation p φ).asModule) (p := p) hcomm hfaith'
  exact ⟨hcyc, by
    rwa [show Nat.card (elabRepresentation p φ).asModule = Nat.card K from rfl] at hdvd⟩

set_option backward.isDefEq.respectTransparency false in
open OddOrder.RepresentationTheory Representation in
/-- **Thin subgroup-level entry to the canonical Singer FPF-coprimality** (issue 9000 dedup):
the subgroup→module conversions (`elabRepresentation_isSimpleModule_and_faithful` +
`exists_addEquiv_asModule_fpf`) followed by the single cite of the shared `SingerField` lemma
`coprime_card_sub_one_of_faithful_irreducible_comm_fpf`.  As with
`singerAdapter_isCyclic_card_dvd`, no Singer content lives here. -/
theorem singerAdapter_coprime_fpf
    {A K : Type*} [Group A] [Finite A] [CommGroup K] [Finite K] {p : ℕ} [Fact p.Prime]
    [Module (ZMod p) (Additive K)] {φ : A →* MulAut K}
    (hcomm : ∀ a b : A, a * b = b * a) (hnt : Nontrivial K)
    (hirr : ∀ J : Subgroup K, IsAInvariant φ J → J = ⊥ ∨ J = ⊤)
    (hfaith : ∀ a : A, (∀ x : K, φ a x = x) → a = 1)
    (σ : MulAut K)
    (hfpf : ∀ a : A, (∀ x : K, σ (φ a x) = φ a (σ x)) → a = 1) :
    Nat.Coprime (Nat.card A) (p - 1) := by
  obtain ⟨hsimp, hfaith'⟩ :=
    elabRepresentation_isSimpleModule_and_faithful (p := p) hnt hirr hfaith
  have := hsimp
  have : Finite (elabRepresentation p φ).asModule := ‹Finite K›
  obtain ⟨τ, hτfpf⟩ := exists_addEquiv_asModule_fpf (p := p) (φ := φ) σ hfpf
  exact coprime_card_sub_one_of_faithful_irreducible_comm_fpf
    (E := A) (M := (elabRepresentation p φ).asModule) hcomm hfaith' τ hτfpf

/-- **(9.7) case (a) bound.**  A group `A` acting on a group `K` of prime order `p` has its
action-image `φ.range` of order dividing `p - 1`: `K` is cyclic, so `MulAut K ≅ (ZMod p)ˣ` has order
`p - 1` (`IsCyclic.card_mulAut`), and `φ.range ≤ MulAut K`.  This is the `a ∣ p - 1` bound of
Peterfalvi (9.7) case (a) for `a = |A : C_A(K)| = |φ.range|` (the `U`-action on an order-`p`
Clifford
factor `H₁` embeds `U/C_U(H₁)` into the cyclic `Aut(H₁)`). -/
theorem card_range_dvd_card_sub_one_of_prime_card {A K : Type*} [Group A] [Group K] [Finite K]
    (φ : A →* MulAut K) (hp : (Nat.card K).Prime) :
    Nat.card ↥φ.range ∣ Nat.card K - 1 := by
  have : Fact (Nat.card K).Prime := ⟨hp⟩
  have : IsCyclic K := isCyclic_of_prime_card rfl
  calc Nat.card ↥φ.range ∣ Nat.card (MulAut K) := Subgroup.card_subgroup_dvd_card _
    _ = Nat.totient (Nat.card K) := IsCyclic.card_mulAut K
    _ = Nat.card K - 1 := Nat.totient_prime hp

/-- **(9.7) case (a) bound for a Clifford factor.**  The image of the restricted `A`-action on a
`φ`-invariant subgroup `S` of prime order has order dividing `|S| - 1`. -/
theorem aInvariantRestrictAut_range_card_dvd {K A : Type*} [Group K] [Group A] [Finite K]
    {φ : A →* MulAut K} {S : Subgroup K} (hS : IsAInvariant φ S) (hp : (Nat.card ↥S).Prime) :
    Nat.card ↥(aInvariantRestrictAut hS).range ∣ Nat.card ↥S - 1 :=
  card_range_dvd_card_sub_one_of_prime_card (aInvariantRestrictAut hS) hp

end OddOrder.Peterfalvi.S11


