-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_PairIntersection
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S16_PairIntersection
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T09:50:21.813336+00:00
-- url     : https://prove2.me/theorems/900a7e4c-d87f-45c4-b101-681e6025049a
-- title:
--   BG §16: the type-$\mathcal{P}$ dual pair intersection $S\cap T=W$
-- statement:
--   Formalizes a clause of Theorem I (clause (2)) / Theorem C(6) of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §16: for a type-$\mathcal{P}$ maximal subgroup $M$ with Hall $\kappa(M)$-factor $K$ and its unique nonconjugate partner $M^*$, the intersection of the corresponding subgroups $S\cap T$ equals $W$.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 4 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S16_PairIntersection.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S16_PairIntersection.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_Basics
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_LocalStructure
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_SigmaLengthOne
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_TypePDuality
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_GlobalCounting

namespace OddOrder.BG.Ch4.S16

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch4.S14

open scoped Pointwise

variable {G : Type*} [Group G]

/-- If `B` normalizes `N` and `A ≤ N`, `B ≤ P ≤ N_G(N)`, then `⁅A, B⁆ ≤ N`.
A normal subgroup `N` of `P` absorbs commutators `⁅A, B⁆` with `A ≤ N`, `B ≤ P`. -/
private theorem commutator_le_of_le_normalizer {N P A B : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (N : Set G)) (hA : A ≤ N) (hB : B ≤ P) :
    ⁅A, B⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hbN : b ∈ Subgroup.normalizer (N : Set G) := hPN (hB hb)
  have hconj : b * a⁻¹ * b⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp hbN a⁻¹).mp (N.inv_mem (hA ha))
  have key : a * (b * a⁻¹ * b⁻¹) ∈ N := N.mul_mem (hA ha) hconj
  rwa [commutatorElement_def, show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]

/-- **BG Theorem 14.7(4) / Theorem C(6) / Theorem I(2)** (mmd L3967, L4382, L4531):
the type-`P` dual pair intersects in the cyclic group `Z = K ⊔ K*`,

    `M ⊓ M* = K ⊔ K*`.

`M` is a type-`P` maximal subgroup with Hall `κ(M)`-factor `K` and canonical
`K* = M_σ ⊓ C_G(K)`; `M*` is the partner exposed by `typeP_duality`'s `∃!`
conclusion (`M*` maximal type-`P`, nonconjugate to `M`, with `K* ≤ M*`, `K*` a
Hall `κ(M*)`-factor, and `K = M*_σ ⊓ C_G(K*)`).  The forward inclusion is
immediate; the reverse inclusion is the genuine §16 structural content. -/
theorem typeP_pair_inf_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstar : Mstar ∈ maximalSubgroups G) (hPstar : S14.IsTypeP Mstar)
    (hnc : ¬ IsConjugateSubgroup M Mstar)
    (hKstarMstar : Kstar ≤ Mstar)
    (hKstar_hall : Ch03.IsHallSubgroup (kappa Mstar) (Kstar.subgroupOf Mstar))
    (hZcyc : IsCyclic ↥(K ⊔ Kstar))
    (hK_eq : K = OddOrder.BG.Ch3.S10.Msigma Mstar ⊓ Subgroup.centralizer (Kstar : Set G)) :
    M ⊓ Mstar = K ⊔ Kstar := by
  classical
  -- Basic containments.
  have hKstarMsig : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M := by rw [hKstar]; exact inf_le_left
  have hKstarM : Kstar ≤ M := hKstarMsig.trans (OddOrder.BG.Ch3.S10.Msigma_le M)
  have hKMstarσ : K ≤ OddOrder.BG.Ch3.S10.Msigma Mstar := by rw [hK_eq]; exact inf_le_left
  have hKMstar : K ≤ Mstar := hKMstarσ.trans (OddOrder.BG.Ch3.S10.Msigma_le Mstar)
  -- Forward inclusion `Z ≤ M ⊓ M*`.
  have hfwd : K ⊔ Kstar ≤ M ⊓ Mstar :=
    le_inf (sup_le hKM hKstarM) (sup_le hKMstar hKstarMstar)
  -- σ(M) and σ(M*) are disjoint (Theorem 13.9), so `M_σ ⊓ M*_σ = ⊥`.
  have hσdisj : Disjoint (OddOrder.BG.Ch3.S10.sigma M) (OddOrder.BG.Ch3.S10.sigma Mstar) :=
    OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hM hMstar hnc
  have hMsigInf : OddOrder.BG.Ch3.S10.Msigma M ⊓ OddOrder.BG.Ch3.S10.Msigma Mstar = ⊥ := by
    apply Disjoint.eq_bot
    apply Subgroup.disjoint_of_coprime_natCard
    rw [← Nat.disjoint_primeFactors Nat.card_pos.ne' Nat.card_pos.ne']
    refine Finset.disjoint_left.mpr (fun q hqM hqMstar => ?_)
    exact Set.disjoint_left.mp hσdisj
      (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q hqM)
      (OddOrder.BG.Ch3.S10.Msigma_isPiGroup Mstar q hqMstar)
  -- Normalizer facts for the σ-cores.
  have hMnorm : M ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) := by
    rw [OddOrder.BG.Ch3.S10.Msigma]; exact le_normalizer_opiCoreInG _ _
  have hMstarnorm : Mstar ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma Mstar : Set G) := by
    rw [OddOrder.BG.Ch3.S10.Msigma]; exact le_normalizer_opiCoreInG _ _
  -- **Step 1**: `M_σ ⊓ M* = K*`.  The σ(M)-subgroup `W := M_σ ⊓ M*` centralizes `K`
  -- (`⁅W, K⁆ ≤ M_σ ⊓ M*_σ = ⊥`), so `W ≤ M_σ ⊓ C_G(K) = K*`.
  have hstep1 : OddOrder.BG.Ch3.S10.Msigma M ⊓ Mstar = Kstar := by
    refine le_antisymm ?_ (le_inf hKstarMsig hKstarMstar)
    -- `⁅W, K⁆ = ⊥`.
    have hcomm1 : ⁅OddOrder.BG.Ch3.S10.Msigma M ⊓ Mstar, K⁆ ≤ OddOrder.BG.Ch3.S10.Msigma M :=
      commutator_le_of_le_normalizer hMnorm inf_le_left hKM
    have hcomm2 : ⁅OddOrder.BG.Ch3.S10.Msigma M ⊓ Mstar, K⁆ ≤ OddOrder.BG.Ch3.S10.Msigma Mstar := by
      rw [Subgroup.commutator_comm]
      exact commutator_le_of_le_normalizer hMstarnorm hKMstarσ inf_le_right
    have hcommbot : ⁅OddOrder.BG.Ch3.S10.Msigma M ⊓ Mstar, K⁆ = ⊥ :=
      le_bot_iff.mp (hMsigInf ▸ le_inf hcomm1 hcomm2)
    have hWcentK : OddOrder.BG.Ch3.S10.Msigma M ⊓ Mstar ≤ Subgroup.centralizer (K : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommbot
    rw [hKstar]
    exact le_inf inf_le_left hWcentK
  -- **Step 2**: `M ⊓ M* ≤ Z`.  `K* = M_σ ⊓ M*` is normalized by `M ⊓ M*`, so `M ⊓ M*`
  -- normalizes the characteristic line `X* ≤ K*`; Proposition 14.2(b1) for `M*` then gives
  -- `M ⊓ M* ≤ N_G(X*) ⊓ M* = K* ⊔ K = Z`.
  -- `K* ≠ ⊥`.
  obtain ⟨hself1, _, _, hself4⟩ := typeP_self_member hG hM hP hKM hK hKstar hU
  have hKstar_ne : Kstar ≠ ⊥ := fun h => hself4 (hself1.trans h)
  -- `K*` is cyclic (a subgroup of the cyclic `Z`).
  have : IsCyclic ↥(K ⊔ Kstar) := hZcyc
  have hKstarcyc : IsCyclic ↥Kstar :=
    (Subgroup.subgroupOfEquivOfLe (le_sup_right : Kstar ≤ K ⊔ Kstar)).isCyclic.mp inferInstance
  -- A prime `p ∣ |K*|` and an order-`p` line `X* ≤ K*`.
  have hcard_ne_one : Nat.card ↥Kstar ≠ 1 := fun h => hKstar_ne (Subgroup.card_eq_one.mp h)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard_ne_one
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ : ∃ g : ↥Kstar, orderOf g = p := exists_prime_orderOf_dvd_card' p hpdvd
  set X : Subgroup G := Subgroup.zpowers ((g : ↥Kstar) : G) with hXdef
  have hgord : orderOf ((g : ↥Kstar) : G) = p :=
    (orderOf_injective Kstar.subtype Kstar.subtype_injective g).trans hg
  have hXcard : Nat.card ↥X = p := by rw [hXdef, Nat.card_zpowers]; exact hgord
  have hXE1 : X ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXKstar : X ≤ Kstar := Subgroup.zpowers_le.mpr g.2
  -- `M ⊓ M*` normalizes `K*` (from Step 1).
  have hnormKstar : (M ⊓ Mstar : Subgroup G) ≤ Subgroup.normalizer (Kstar : Set G) := by
    intro x hx
    refine mem_normalizer_of_conj_smul_eq_self ?_
    have hxM := (Subgroup.mem_inf.mp hx).1
    have hxMstar := (Subgroup.mem_inf.mp hx).2
    have h1 : MulAut.conj x • OddOrder.BG.Ch3.S10.Msigma M = OddOrder.BG.Ch3.S10.Msigma M :=
      conj_smul_eq_self_of_mem_normalizer (hMnorm hxM)
    have h2 : MulAut.conj x • Mstar = Mstar :=
      conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hxMstar)
    rw [← hstep1, Subgroup.smul_inf, h1, h2]
  -- `M ⊓ M*` normalizes the characteristic line `X*` (unique order-`p` subgroup of cyclic `K*`).
  have hnormX : (M ⊓ Mstar : Subgroup G) ≤ Subgroup.normalizer (X : Set G) := by
    intro x hx
    refine mem_normalizer_of_conj_smul_eq_self ?_
    have hxKstar : MulAut.conj x • Kstar = Kstar :=
      conj_smul_eq_self_of_mem_normalizer (hnormKstar hx)
    refine OddOrder.BG.Ch3.S13.eq_of_card_eq_prime_of_le_isCyclic hKstarcyc hp ?_ hXKstar ?_ hXcard
    · calc MulAut.conj x • X ≤ MulAut.conj x • Kstar :=
            Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hXKstar
        _ = Kstar := hxKstar
    · exact (OddOrder.BG.Ch3.S12.conj_smul_mem_elemAbelianOfRank x hXE1).2.trans (pow_one p)
  -- Proposition 14.2(b1) for the partner: `N_G(X*) ⊓ M* = K* ⊔ K = Z`.
  have hb1 := typeP_normalizer_inf_eq hG hMstar hPstar hKstarMstar hKstar_hall hp hXE1 hXKstar
  rw [← hK_eq] at hb1
  refine le_antisymm ?_ hfwd
  calc (M ⊓ Mstar : Subgroup G) ≤ Subgroup.normalizer (X : Set G) ⊓ Mstar :=
        le_inf hnormX inf_le_right
    _ = Kstar ⊔ K := hb1
    _ = K ⊔ Kstar := sup_comm Kstar K

/-- **BG Theorem 14.7(8) / Theorem C, order form**: a Hall `κ(M)`-subgroup `K` of a type-`P`
maximal subgroup has order `|M : M'|`, since it complements the derived subgroup `M' = [M,M]`
in `M` (`typeP_derivedInG_isComplement_kappaHall`, BG part (h)).

Companion of `OddOrder.GroupTheory.TypePData.card_W1_eq_derived_index` (`|W₁| = |M:M'|`): both `K`
and the type-data factor `W₁` complement `M'`, so they share this order, `|K| = |W₁|`.  This is the
bridge from the BG §14 κ-Hall presentation to the Peterfalvi (8.8.b1) `M = M' ⋊ W₁` presentation —
in particular it transports BG Theorem C(10)'s "`|K|` prime" (type II–IV) to the `(card W₁).Prime`
field carried by `TypePNontrivialCore`, the key step toward discharging the
`section16TypePStructure` producer's prime-order fields. -/
theorem card_kappaHall_eq_derived_index [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M)) [IsCyclic ↥K] :
    Nat.card ↥K = ((derivedInG M).subgroupOf M).index := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv,
    ← (typeP_derivedInG_isComplement_kappaHall hG hM hP hKM hK).symm.index_eq_card]

/-- **BG Theorem 14.7(4)(5), the `W`-side structure of the type-`P` dual pair** (mmd L3967):
the full cyclic-product structure of `S ∩ T = W = W₁ × W₂`, bundling the intersection identity
(`typeP_pair_inf_eq`), the cyclicity of `S ∩ T` (BG 14.7(4)), and that `K, K*` form a *direct*
product inside it (`K ⊓ K* = 1`, `K`/`K*` commute — BG 14.7's `Z = K × K*`).

These are exactly the `Section16TypePStructure` fields `W_eq_inter`/`W_cyclic`/`W1_inf_W2_eq_bot`/
`W1_commutes_W2` for the κ-Hall presentation `W₁ = K`, `W₂ = K*`.  They are sourced from the
canonical `typeP_duality` witnesses, which an *enriched* `Section16MaximalPair` must carry for the
producer to discharge the pairing (the intrinsic `Section16MaximalPair` axioms fix the partner only
up to conjugacy, so `S ∩ T` need not be this cyclic product without the enrichment). -/
theorem typeP_pair_W_structure [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstar : Mstar ∈ maximalSubgroups G) (hPstar : S14.IsTypeP Mstar)
    (hnc : ¬ IsConjugateSubgroup M Mstar)
    (hKstarMstar : Kstar ≤ Mstar)
    (hKstar_hall : Ch03.IsHallSubgroup (kappa Mstar) (Kstar.subgroupOf Mstar))
    (hZcyc : IsCyclic ↥(K ⊔ Kstar))
    (hK_eq : K = OddOrder.BG.Ch3.S10.Msigma Mstar ⊓ Subgroup.centralizer (Kstar : Set G)) :
    M ⊓ Mstar = K ⊔ Kstar ∧ IsCyclic ↥(M ⊓ Mstar) ∧ K ⊓ Kstar = ⊥ ∧
      (∀ x ∈ K, ∀ y ∈ Kstar, Commute x y) := by
  have heq : M ⊓ Mstar = K ⊔ Kstar :=
    typeP_pair_inf_eq hG hM hP hKM hK hKstar hU hMstar hPstar hnc hKstarMstar hKstar_hall hZcyc
        hK_eq
  refine ⟨heq, heq ▸ hZcyc, kappaHall_inf_Kstar_eq_bot hKM hK hKstar, fun x hx y hy => ?_⟩
  let : CommGroup ↥(K ⊔ Kstar) := IsCyclic.commGroup
  exact congrArg Subtype.val
    (mul_comm (⟨x, Subgroup.mem_sup_left hx⟩ : ↥(K ⊔ Kstar)) ⟨y, Subgroup.mem_sup_right hy⟩)

end OddOrder.BG.Ch4.S16


