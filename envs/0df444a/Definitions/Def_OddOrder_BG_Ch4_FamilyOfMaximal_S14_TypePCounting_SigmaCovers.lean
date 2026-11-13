-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_SigmaCovers
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_SigmaCovers
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T09:19:48.826094+00:00
-- url     : https://prove2.me/theorems/7e0dad81-4dff-45d0-8568-16d132bc6eeb
-- title:
--   BG §14: type-$\mathcal{P}$ counting, $\sigma$-covers and the family $\mathcal{Z}$ (14.7)
-- statement:
--   A part of the §14 type-$\mathcal{P}$ counting development of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, split from the type-$\mathcal{P}$ duality file, around Theorem 14.7: the internal direct product $Z=K\times K^*$, the predicate and finset for members of the type-$\mathcal{P}$ family, and lemmas that the family covers, e.g. `typeP_family_sigma_covers` and that its members are TI.
--
--   Main declarations: `kappaHall_prod_Kstar_mulEquiv`; `IsZFamilyMember`; `ZFamilyFinset`.
--
--   The bundle also proves 41 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/SigmaCovers.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/SigmaCovers.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_SigmaLengthOne

namespace OddOrder.BG.Ch4.S14

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch3.S13

open scoped Pointwise

variable {G : Type*} [Group G]

/-- A Hall `κ(M)`-subgroup `K` is a `σ(M)'`-subgroup (since `κ(M) ⊆ σ(M)'`).  Extracted from
the `hK_pi` step internal to `typeP_structure` for reuse in the `Z`-structure lemmas. -/
theorem kappaHall_isPiSubgroup_sigmaCompl {M K : Subgroup G} (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M)) :
    Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma M)ᶜ) K := by
  intro p hp
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hp
  exact kappa_subset_sigmaCompl (hK.1 p hp)

/-- `K* = C_{M_σ}(K)` is a `σ(M)`-subgroup (it lies in `M_σ`, a `σ(M)`-group). -/
theorem Kstar_isPiSubgroup_sigma [Finite G] {M K Kstar : Subgroup G}
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma M) Kstar := by
  intro p hp
  have hle : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M := hKstar ▸ inf_le_left
  obtain ⟨hpp, hpdvd, _⟩ := Nat.mem_primeFactors.mp hp
  refine OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p (Nat.mem_primeFactors.mpr
    ⟨hpp, hpdvd.trans (Subgroup.card_dvd_of_le hle), Nat.card_pos.ne'⟩)

/-- **BG 14.7, `|K|`, `|K*|` coprime** (mmd L4027): `K` is a `σ(M)'`-group, `K* ≤ M_σ` a
`σ(M)`-group, so no prime divides both. -/
theorem coprime_card_kappaHall_Kstar [Finite G] {M K Kstar : Subgroup G} (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    Nat.Coprime (Nat.card ↥K) (Nat.card ↥Kstar) := by
  apply Nat.coprime_of_dvd
  intro p hp hpK hpKstar
  have hpσc : p ∉ OddOrder.BG.Ch3.S10.sigma M :=
    kappaHall_isPiSubgroup_sigmaCompl hKM hK p
      (Nat.mem_primeFactors.mpr ⟨hp, hpK, Nat.card_pos.ne'⟩)
  exact hpσc (Kstar_isPiSubgroup_sigma hKstar p
    (Nat.mem_primeFactors.mpr ⟨hp, hpKstar, Nat.card_pos.ne'⟩))

/-- **BG 14.7, `|K| > 1`**: the κ-Hall factor of a type-`P` maximal subgroup is nontrivial.  Some
prime `p ∈ κ(M)` divides `|K|`: `p` divides `|M|` (it is the order of an elementary abelian
`p`-subgroup of `M`, by the definition of `κ`), and is coprime to the Hall index `[M : K]`, so it
divides the Hall order `|K|`. -/
theorem card_kappaHall_ne_one [Finite G] {M K : Subgroup G} (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M)) :
    Nat.card ↥K ≠ 1 := by
  obtain ⟨p, hpκ⟩ := hP
  have hpprime : p.Prime := hpκ.1
  obtain ⟨P, hPelem, hPM, -⟩ := hpκ.2.2
  have hpcardP : Nat.card ↥P = p := by obtain ⟨_, hc⟩ := hPelem; rwa [pow_one] at hc
  have hpM : p ∣ Nat.card ↥M := hpcardP ▸ Subgroup.card_dvd_of_le hPM
  have hpK : p ∣ Nat.card ↥K := by
    have hlag : Nat.card ↥K * (K.subgroupOf M).index = Nat.card ↥M := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
      exact Subgroup.card_mul_index (K.subgroupOf M)
    have hpidx : ¬ p ∣ (K.subgroupOf M).index := fun hd =>
      hK.2 p (Nat.mem_primeFactors.mpr ⟨hpprime, hd, Subgroup.index_ne_zero_of_finite⟩) hpκ
    exact (hpprime.dvd_mul.mp (hlag.symm ▸ hpM)).resolve_right hpidx
  exact fun h => hpprime.ne_one (Nat.dvd_one.mp (h ▸ hpK))

/-- **BG 14.7, `K ⊓ K* = 1`**: the coprime factors meet trivially. -/
theorem kappaHall_inf_Kstar_eq_bot [Finite G] {M K Kstar : Subgroup G} (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    K ⊓ Kstar = ⊥ :=
  (Subgroup.disjoint_of_coprime_natCard (coprime_card_kappaHall_Kstar hKM hK hKstar)).eq_bot

/-- **BG 14.7, `K*` centralizes `K`**: every element of `K` commutes with every element of
`K* = C_{M_σ}(K)` (which lies in `C_G(K)`). -/
theorem commute_kappaHall_Kstar {M K Kstar : Subgroup G}
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    ∀ (a : ↥K) (b : ↥Kstar), Commute (K.subtype a) (Kstar.subtype b) := by
  intro a b
  have hb : (b : G) ∈ Subgroup.centralizer (K : Set G) := by
    have hbmem : (b : G) ∈
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) := by
      rw [← hKstar]; exact b.2
    exact (Subgroup.mem_inf.mp hbmem).2
  exact Subgroup.mem_centralizer_iff.mp hb (a : G) a.2

/-- **BG 14.7, `Z = K × K*` internal direct product iso** `↥K × ↥K* ≃* ↥(K ⊔ K*)`,
`(a, b) ↦ a·b` (well-defined since `K`, `K*` commute, injective since `K ⊓ K* = 1`). -/
noncomputable def kappaHall_prod_Kstar_mulEquiv [Finite G] {M K Kstar : Subgroup G} (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    (↥K × ↥Kstar) ≃* ↥(K ⊔ Kstar) := by
  have hcomm := commute_kappaHall_Kstar hKstar
  have hinj : Function.Injective (MonoidHom.noncommCoprod K.subtype Kstar.subtype hcomm) :=
    (MonoidHom.noncommCoprod_injective _ _ hcomm).mpr
      ⟨K.subtype_injective, Kstar.subtype_injective, by
        rw [K.range_subtype, Kstar.range_subtype]
        exact disjoint_iff.mpr (kappaHall_inf_Kstar_eq_bot hKM hK hKstar)⟩
  have hrange : (MonoidHom.noncommCoprod K.subtype Kstar.subtype hcomm).range = K ⊔ Kstar := by
    rw [MonoidHom.noncommCoprod_range, K.range_subtype, Kstar.range_subtype]
  exact (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)

/-- **BG 14.7, `|Z| = |K|·|K*|`** (mmd L4029, `z = k k*`): the internal direct product order. -/
theorem card_kappaHall_sup_Kstar [Finite G] {M K Kstar : Subgroup G} (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    Nat.card ↥(K ⊔ Kstar) = Nat.card ↥K * Nat.card ↥Kstar := by
  rw [← Nat.card_congr (kappaHall_prod_Kstar_mulEquiv hKM hK hKstar).toEquiv, Nat.card_prod]

/-- **BG 14.7(d), `Z = K ⊔ K*` cyclic** (mmd L4041): once both factors are cyclic (forced by the
counting collapse `n = 1`, where `r(K) = r(K*) = 1`), the coprime commuting product is cyclic. -/
theorem isCyclic_kappaHall_sup_Kstar_of_cyclic [Finite G] {M K Kstar : Subgroup G} (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    [IsCyclic ↥K] [IsCyclic ↥Kstar] :
    IsCyclic ↥(K ⊔ Kstar) := by
  have hprodcyc : IsCyclic (↥K × ↥Kstar) :=
    Group.isCyclic_prod_iff.mpr
      ⟨inferInstance, inferInstance, coprime_card_kappaHall_Kstar hKM hK hKstar⟩
  exact (kappaHall_prod_Kstar_mulEquiv hKM hK hKstar).isCyclic.mp hprodcyc

/-- **BG 14.7(h), coprimality is free given the complement**: if `M' = [M,M]` complements the
Hall `κ(M)`-subgroup `K` in `M`, then `|M'|` and `|K|` are coprime — `|M'| = [M : K]` (from the
complement) and a Hall subgroup has order coprime to its index.  This reduces Theorem 14.7(h) to its
substantive obligation `IsComplement' M' K` (mmd L4061, which consumes "`K` cyclic" from the
counting collapse); the second conjunct then follows with no further input. -/
theorem coprime_card_derived_kappaHall_of_isComplement' [Finite G] {M K : Subgroup G}
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hc : Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M)) :
    Nat.Coprime (Nat.card ↥((derivedInG M).subgroupOf M)) (Nat.card ↥(K.subgroupOf M)) := by
  have hcop := hK.coprime_index
  rw [hc.index_eq_card] at hcop
  exact hcop.symm

/-- **BG Theorem 14.7, partner existence** (§16-independent core, mmd L3975-3991): for a type-`P`
maximal `M` with Hall `κ(M)`-subgroup `K`, `Kstar = C_{M_σ}(K)`, and a line `X ∈ ℰ_p¹(K)`, every
`M* ∈ 𝓜(N_G(X))` (which exists, `N_G(X)` being proper) is type-`P`, nonconjugate to `M`, contains
`K ⊔ Kstar` with `X ≤ M*_σ`, and `π(Kstar) ⊆ κ(M*)`.  This is the nonconjugate partner `M*` of
Theorem 14.7 with its basic neighbour data; cyclicity of `Z`, the TI property, type-`P₂`, and the
§16-gated covering/uniqueness are layered on top.  Built from `typeP_neighbor_embed` +
`typeP_neighbor_kappa` (the §16-independent pre-position, steps 1a/1b). -/
theorem exists_typeP_partner [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXK : X ≤ K) :
    ∃ Mstar : Subgroup G,
      Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) ∧
      ¬ IsConjugateSubgroup M Mstar ∧ K ⊔ Kstar ≤ Mstar ∧
      X ≤ OddOrder.BG.Ch3.S10.Msigma Mstar ∧
      (∀ q ∈ (Nat.card ↥Kstar).primeFactors, q ∈ kappa Mstar) ∧ IsTypeP Mstar := by
  classical
  have hKstarne : Kstar ≠ ⊥ := (typeP_structure hG hM hP hKM hK hKstar hU).2.1
  -- `C_{M_σ}(X) ⊇ C_{M_σ}(K) = Kstar ≠ 1`.
  have hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ := by
    intro hbot
    refine hKstarne (le_bot_iff.mp ?_)
    rw [hKstar]
    calc OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
        ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) :=
          inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXK))
      _ = ⊥ := hbot
  have hXne : X ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hX
  obtain ⟨Mstar, hMstarmax, hMstarge⟩ :=
    OddOrder.BG.Ch2.S08.exists_maximalSubgroup_containing_normalizer_of_ne_bot_le_maximal
      hG hM hXne (hXK.trans hKM)
  have hMstarmem : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hMstarmax, hMstarge⟩
  obtain ⟨hnc, hZle, hXMsσ⟩ :=
    typeP_neighbor_embed hG hM hP hKM hK hKstar hU hX hXK hCX hMstarmem
  have hκ := typeP_neighbor_kappa hG hM hP hKM hK hKstar hU hX hXK hCX hMstarmem
  have : Nontrivial ↥Kstar := (Subgroup.nontrivial_iff_ne_bot _).mpr hKstarne
  obtain ⟨q, hq⟩ : (Nat.card ↥Kstar).primeFactors.Nonempty :=
    Nat.nonempty_primeFactors.mpr Finite.one_lt_card
  exact ⟨Mstar, hMstarmem, hnc, hZle, hXMsσ, hκ, ⟨q, hκ q hq⟩⟩

/-- **σ-part lands in the σ-factor of an internal direct product**: in `Ki ⊔ Kistar`, where `Kistar`
centralizes `Ki`, `Kistar ≤ M_σ`, and `Ki ⊓ M_σ = ⊥` (e.g. `Ki` is a `σ(Mi)'`-group), any subgroup
`X ≤ Ki ⊔ Kistar` contained in `M_σ` lies in `Kistar`.  Writing `x = a·b` (`a ∈ Ki`, `b ∈ Kistar`),
the `σ'`-part `a = x·b⁻¹ ∈ M_σ ⊓ Ki = ⊥`, so `x = b ∈ Kistar`.  This is the `σ`-projection used by
the swap argument (BG mmd L3999, "it follows that `X_i ⊆ K_i*`") and the `Z`-decomposition. -/
theorem le_centralizerFactor_of_le_sup_of_le_Msigma [Finite G] {Mi Ki Kistar X : Subgroup G}
    (hKistarC : Kistar ≤ Subgroup.centralizer (Ki : Set G))
    (hKistarMσ : Kistar ≤ OddOrder.BG.Ch3.S10.Msigma Mi)
    (hKiMσ : Ki ⊓ OddOrder.BG.Ch3.S10.Msigma Mi = ⊥)
    (hXsup : X ≤ Ki ⊔ Kistar) (hXMσ : X ≤ OddOrder.BG.Ch3.S10.Msigma Mi) :
    X ≤ Kistar := by
  classical
  -- `Ki` is normal in `Ki ⊔ Kistar` (`Kistar` centralizes it), so elements decompose as `a · b`.
  have hKnorm : Ki ⊔ Kistar ≤ Subgroup.normalizer (Ki : Set G) :=
    sup_le Subgroup.le_normalizer (hKistarC.trans (Subgroup.centralizer_le_normalizer _))
  have : ((Ki).subgroupOf (Ki ⊔ Kistar)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hKnorm
  have hsuptop : (Ki.subgroupOf (Ki ⊔ Kistar)) ⊔ (Kistar.subgroupOf (Ki ⊔ Kistar)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  intro x hx
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp
    (hsuptop ▸ Subgroup.mem_top (⟨x, hXsup hx⟩ : ↥(Ki ⊔ Kistar)))
  have haKi : (a : G) ∈ Ki := Subgroup.mem_subgroupOf.mp ha
  have hbKistar : (b : G) ∈ Kistar := Subgroup.mem_subgroupOf.mp hb
  have hab' : (a : G) * (b : G) = x := by have := congrArg Subtype.val hab; simpa using this
  have haMσ : (a : G) ∈ OddOrder.BG.Ch3.S10.Msigma Mi := by
    have heq : (a : G) = x * (b : G)⁻¹ := by rw [← hab']; group
    rw [heq]
    exact (OddOrder.BG.Ch3.S10.Msigma Mi).mul_mem (hXMσ hx)
      ((OddOrder.BG.Ch3.S10.Msigma Mi).inv_mem (hKistarMσ hbKistar))
  have ha1 : (a : G) = 1 := Subgroup.mem_bot.mp (hKiMσ ▸ Subgroup.mem_inf.mpr ⟨haKi, haMσ⟩)
  rw [← hab', ha1, one_mul]; exact hbKistar

/-- **BG 14.7, neighbour normalizer identity** (Proposition 14.2(b1) packaged for a neighbour,
mmd L3997): for a type-`P` maximal `Mi`, a Hall `κ(Mi)`-subgroup `Ki ≤ Mi`, and a rank-one
`X ≤ Ki`, `N_G(X) ⊓ Mi = Ki ⊔ C_{Mi_σ}(Ki)`.  The Hall `(κ(Mi) ∪ σ(Mi))'`-subgroup that
Proposition 14.2 needs is produced internally via `hall_E_exists` (in the solvable group `↥Mi`),
so the swap argument supplies only `Ki` and `X`.  Applied twice — to `Ki` and to a Hall
`κ(Mi)`-subgroup `Ki' ⊇ K*` — it yields `Ki ⊔ Ki* = N_G(X) ⊓ Mi = Ki' ⊔ Ki'*`, the choice
independence at the heart of the swap. -/
theorem typeP_normalizer_inf_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {Mi Ki : Subgroup G} (hMi : Mi ∈ maximalSubgroups G) (hPi : IsTypeP Mi)
    (hKiMi : Ki ≤ Mi) (hKi : Ch03.IsHallSubgroup (kappa Mi) (Ki.subgroupOf Mi))
    {p : ℕ} (hp : p.Prime) {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXKi : X ≤ Ki) :
    Subgroup.normalizer (X : Set G) ⊓ Mi =
      Ki ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) := by
  classical
  have : Group.IsSolvable ↥Mi := hG.isSolvable_of_mem_maximalSubgroups hMi
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥Mi)
    ((kappa Mi ∪ OddOrder.BG.Ch3.S10.sigma Mi)ᶜ)
  have hUeq : (U'.map Mi.subtype).subgroupOf Mi = U' :=
    Subgroup.comap_map_eq_self_of_injective Mi.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((kappa Mi ∪ OddOrder.BG.Ch3.S10.sigma Mi)ᶜ)
      ((U'.map Mi.subtype).subgroupOf Mi) := by rw [hUeq]; exact hU'
  obtain ⟨_, _, hb1, _, _, _⟩ := typeP_structure hG hMi hPi hKiMi hKi rfl hU
  exact hb1 p hp X hX hXKi

/-- **BG 14.7, `M ⊇ N_G(X)` from a unique centralizer-maximal** (mmd L3992, "Moreover, `M ⊇
N_G(X)`"): if `M` is the *unique* maximal subgroup containing `C_G(X)` (i.e.
`ℳ(C_G(X)) = {M}`, the conclusion of Proposition 14.2(c)), then `N_G(X) ≤ M`.

For `g ∈ N_G(X)`, conjugation by `g` fixes `C_G(X)` (`g` normalizes `X`), so `Mᵍ` is again a
maximal subgroup containing `C_G(X)`; by uniqueness `Mᵍ = M`, hence `g ∈ N_G(M) = M`
(`M` self-normalizing as a maximal subgroup).  A general fact, independent of §13. -/
theorem normalizer_le_of_maximalSubgroupsContaining_centralizer [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M X : Subgroup G}
    (hsing : maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M}) :
    Subgroup.normalizer (X : Set G) ≤ M := by
  classical
  have hMmem : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) := by
    rw [hsing]; rfl
  rw [mem_maximalSubgroupsContaining] at hMmem
  obtain ⟨hMcoat, hCXM⟩ := hMmem
  intro g hg
  -- `g` normalizes `X`, hence normalizes `C_G(X)`: `Mᵍ ⊇ C_G(X)ᵍ = C_G(X)`.
  have hgcent : MulAut.conj g • Subgroup.centralizer (X : Set G)
      = Subgroup.centralizer (X : Set G) := by
    have h1 : MulAut.conj g • Subgroup.centralizer (X : Set G)
        = Subgroup.centralizer ((MulAut.conj g • X : Subgroup G) : Set G) :=
      Subgroup.map_centralizer_eq_of_bijective (X : Set G) (MulAut.conj g).toMonoidHom
        (MulAut.conj g).bijective
    rwa [OddOrder.GroupTheory.conj_smul_eq_self_of_mem_normalizer hg] at h1
  -- `Mᵍ` is a maximal subgroup containing `C_G(X)`, so by uniqueness `Mᵍ = M`.
  have hgM_mem : (MulAut.conj g • M) ∈
      maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) := by
    rw [mem_maximalSubgroupsContaining]
    refine ⟨OddOrder.BG.Ch3.S12.isCoatom_conj_smul hMcoat, ?_⟩
    rw [← hgcent]
    exact (Subgroup.pointwise_smul_le_pointwise_smul_iff).mpr hCXM
  rw [hsing, Set.mem_singleton_iff] at hgM_mem
  -- `Mᵍ = M` gives `g ∈ N_G(M) = M`.
  have hgNM : g ∈ Subgroup.normalizer (M : Set G) :=
    OddOrder.GroupTheory.mem_normalizer_of_conj_smul_eq_self hgM_mem
  rwa [normalizer_eq_self_of_mem_maximalSubgroups hG (mem_maximalSubgroups.mpr hMcoat)] at hgNM

/-- **BG 14.7, swap argument — direction `⊆`** (mmd L3999): with `M` type-`P`, `K* = C_{M_σ}(K)`,
and a neighbour `Mi` containing `Z = K ⊔ K*` with `π(K*) ⊆ κ(Mi)`, for any line `X* ≤ K*` and any
Hall `κ(Mi)`-subgroup `Ki ∋ X*` (with `Ki* = C_{Mi_σ}(Ki)`),
`K ⊔ K* ≤ Ki ⊔ Ki*`.

`K`-part: `K` centralizes `K* ⊇ X*`, so `K ≤ N_G(X*)`, and `K ≤ Mi`; thus `K ≤ N_G(X*) ⊓ Mi =
Ki ⊔ Ki*` (Proposition 14.2(b1) for `Mi`).  `K*`-part (the "swap"): `K*` is a `κ(Mi)`-subgroup, so
it lies in *some* Hall `κ(Mi)`-subgroup `Ki' ⊇ K*`, and `N_G(X*) ⊓ Mi = Ki' ⊔ Ki'*` is the *same*
group as `Ki ⊔ Ki*` (it depends only on `X*`, not on the chosen Hall subgroup), so
`K* ≤ Ki' ≤ Ki ⊔ Ki*`. -/
theorem typeP_swap_Z_le [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar Mi Ki : Subgroup G}
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hMi : Mi ∈ maximalSubgroups G) (hPi : IsTypeP Mi) (hZMi : K ⊔ Kstar ≤ Mi)
    (hKstarκ : ∀ q ∈ (Nat.card ↥Kstar).primeFactors, q ∈ kappa Mi)
    {p : ℕ} (hp : p.Prime) {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXKstar : X ≤ Kstar)
    (hKiMi : Ki ≤ Mi) (hKi : Ch03.IsHallSubgroup (kappa Mi) (Ki.subgroupOf Mi)) (hXKi : X ≤ Ki) :
    K ⊔ Kstar ≤ Ki ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) := by
  classical
  set Kistar := OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G) with hKistar
  -- `N_G(X) ⊓ Mi = Ki ⊔ Ki*` (Proposition 14.2(b1) for `Mi`, the reference choice of Hall
  -- subgroup).
  have hNeq : Subgroup.normalizer (X : Set G) ⊓ Mi = Ki ⊔ Kistar :=
    typeP_normalizer_inf_eq hG hMi hPi hKiMi hKi hp hX hXKi
  -- `K` centralizes `K*` (since `K* ≤ C_G(K)`), hence `K ≤ C_G(X) ≤ N_G(X)`.
  have hKCKstar : K ≤ Subgroup.centralizer (Kstar : Set G) := by
    have hKstarCK : Kstar ≤ Subgroup.centralizer (K : Set G) := hKstar ▸ inf_le_right
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (Subgroup.mem_centralizer_iff.mp (hKstarCK hs) k hk).symm
  have hKNX : K ≤ Subgroup.normalizer (X : Set G) :=
    (hKCKstar.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXKstar))).trans
      (Subgroup.centralizer_le_normalizer _)
  -- `K ≤ N_G(X) ⊓ Mi = Ki ⊔ Ki*`.
  have hKle : K ≤ Ki ⊔ Kistar := by
    rw [← hNeq]; exact le_inf hKNX (le_sup_left.trans hZMi)
  -- `K* ≤ Ki ⊔ Ki*` via the swap: pick a Hall `κ(Mi)`-subgroup `Ki' ⊇ K*`.
  have hKstarle : Kstar ≤ Ki ⊔ Kistar := by
    have hKstarMi : Kstar ≤ Mi := le_sup_right.trans hZMi
    obtain ⟨Ki', hKi'Mi, hKi', hKstarKi'⟩ :=
      exists_isHallSubgroup_kappa_ge hG hMi hKstarMi hKstarκ
    have hNeq' : Subgroup.normalizer (X : Set G) ⊓ Mi =
        Ki' ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki' : Set G)) :=
      typeP_normalizer_inf_eq hG hMi hPi hKi'Mi hKi' hp hX (hXKstar.trans hKstarKi')
    calc Kstar ≤ Ki' := hKstarKi'
      _ ≤ Ki' ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki' : Set G)) := le_sup_left
      _ = Subgroup.normalizer (X : Set G) ⊓ Mi := hNeq'.symm
      _ = Ki ⊔ Kistar := hNeq
  exact sup_le hKle hKstarle

/-- **BG 14.7, swap argument — the `Z`-coincidence** (mmd L3999-4001): the neighbour `Mi`'s own
direct-product decomposition coincides with `Z`, i.e. `Z = K ⊔ K* = Ki ⊔ Ki*`.

`M`/`K`/`K*` are the type-`P` data, `Mi` a nonconjugate type-`P` neighbour (e.g. the partner
`exists_typeP_partner` from a line `Xi ∈ ℰ¹(K)`) containing `Z` with `π(K*) ⊆ κ(Mi)`,
`Xi ⊆ Mi_σ`; `X* ∈ ℰ¹(K*)` is a line lying in a Hall `κ(Mi)`-subgroup `Ki`, with
`Ki* = C_{Mi_σ}(Ki)`.  Direction `⊆` is `typeP_swap_Z_le`.  Direction `⊇` re-runs the swap with
the roles of `(M, K, X*)` and `(Mi, Ki, Xi)` exchanged, using:
* `M ⊇ N_G(X*)` (`normalizer_le_of_maximalSubgroupsContaining_centralizer` applied to Prop 14.2(c)'s
  `ℳ(C_G(X*)) = {M}`), which gives `Ki ⊔ Ki* = N_G(X*) ⊓ Mi ≤ M`;
* `π(Ki*) ⊆ κ(M)` (`typeP_neighbor_kappa` for `Mi`, since `M` is the partner of `Mi` via `X*`);
* `Xi ⊆ Ki*` (`le_centralizerFactor_of_le_sup_of_le_Msigma`: `Xi`, a `σ(Mi)`-group inside
  `Ki × Ki*`, lands in the `σ`-factor `Ki*`). -/
theorem typeP_swap_Z_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mi Ki : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMimax : Mi ∈ maximalSubgroups G) (hPi : IsTypeP Mi) (hZMi : K ⊔ Kstar ≤ Mi)
    (hKstarκ : ∀ q ∈ (Nat.card ↥Kstar).primeFactors, q ∈ kappa Mi)
    {pstar : ℕ} (hpstar : pstar.Prime) {Xstar : Subgroup G}
    (hXstar : Xstar ∈ elemAbelianOfRank G pstar 1) (hXstarKstar : Xstar ≤ Kstar)
    (hXstarKi : Xstar ≤ Ki)
    {pi : ℕ} (hpi : pi.Prime) {Xi : Subgroup G}
    (hXi : Xi ∈ elemAbelianOfRank G pi 1) (hXiK : Xi ≤ K)
    (hXiMiσ : Xi ≤ OddOrder.BG.Ch3.S10.Msigma Mi)
    (hKiMi : Ki ≤ Mi) (hKi : Ch03.IsHallSubgroup (kappa Mi) (Ki.subgroupOf Mi)) :
    K ⊔ Kstar = Ki ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) := by
  classical
  have : Fact pstar.Prime := ⟨hpstar⟩
  -- Direction `⊆` (the original swap).
  have hle1 : K ⊔ Kstar ≤
      Ki ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) :=
    typeP_swap_Z_le hG hKstar hMimax hPi hZMi hKstarκ hpstar hXstar hXstarKstar hKiMi hKi hXstarKi
  -- `ℳ(C_G(X*)) = {M}` (Prop 14.2(c)) and hence `N_G(X*) ≤ M`.
  obtain ⟨_, _, _, _, _, hc, _⟩ := typeP_structure hG hM hP hKM hK hKstar hU
  have hNXstarM : Subgroup.normalizer (Xstar : Set G) ≤ M :=
    normalizer_le_of_maximalSubgroupsContaining_centralizer hG
      (hc pstar hpstar Xstar hXstar hXstarKstar)
  -- `N_G(X*) ⊓ Mi = Ki ⊔ Ki*` (Prop 14.2(b1) for `Mi`).
  have hZiMi : Subgroup.normalizer (Xstar : Set G) ⊓ Mi =
      Ki ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) :=
    typeP_normalizer_inf_eq hG hMimax hPi hKiMi hKi hpstar hXstar hXstarKi
  -- (A) `Ki ⊔ Ki* ≤ M`.
  have hA : Ki ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) ≤ M := by
    rw [← hZiMi]; exact inf_le_left.trans hNXstarM
  -- A Hall `(κ(Mi) ∪ σ(Mi))'`-subgroup of `Mi` (for Proposition 14.2 applied to `Mi`).
  have : Group.IsSolvable ↥Mi := hG.isSolvable_of_mem_maximalSubgroups hMimax
  obtain ⟨Ui', hUi'⟩ := Ch03.hall_E_exists (G := ↥Mi)
    ((kappa Mi ∪ OddOrder.BG.Ch3.S10.sigma Mi)ᶜ)
  have hUieq : (Ui'.map Mi.subtype).subgroupOf Mi = Ui' :=
    Subgroup.comap_map_eq_self_of_injective Mi.subtype_injective Ui'
  have hUi : Ch03.IsHallSubgroup ((kappa Mi ∪ OddOrder.BG.Ch3.S10.sigma Mi)ᶜ)
      ((Ui'.map Mi.subtype).subgroupOf Mi) := by rw [hUieq]; exact hUi'
  -- (B) `π(Ki*) ⊆ κ(M)`: `M` is the partner of `Mi` via `X*` (`ℳ(N_G(X*)) = {M}`).
  have hKistarne : OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G) ≠ ⊥ :=
    (typeP_structure hG hMimax hPi hKiMi hKi rfl hUi).2.1
  have hCXstarMi : OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Xstar : Set G) ≠ ⊥ :=
    fun hbot => hKistarne (le_bot_iff.mp (hbot ▸ inf_le_inf_left _
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXstarKi))))
  have hM_in_NXstar : M ∈ maximalSubgroupsContaining (Subgroup.normalizer (Xstar : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hM, hNXstarM⟩
  have hB : ∀ q ∈ (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma Mi ⊓
      Subgroup.centralizer (Ki : Set G))).primeFactors, q ∈ kappa M :=
    typeP_neighbor_kappa hG hMimax hPi hKiMi hKi rfl hUi hXstar hXstarKi hCXstarMi hM_in_NXstar
  -- (C) `Xi ≤ Ki*` (`σ`-part extraction).
  have hXiCXstar : Xi ≤ Subgroup.centralizer (Xstar : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyCK : y ∈ Subgroup.centralizer (K : Set G) :=
      (Subgroup.mem_inf.mp (hKstar ▸ hXstarKstar hy)).2
    exact (Subgroup.mem_centralizer_iff.mp hyCK a (hXiK ha)).symm
  have hXisup : Xi ≤ Ki ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) := by
    rw [← hZiMi]
    exact le_inf (hXiCXstar.trans (Subgroup.centralizer_le_normalizer _))
      (hXiMiσ.trans (OddOrder.BG.Ch3.S10.Msigma_le Mi))
  have hKiMσbot : Ki ⊓ OddOrder.BG.Ch3.S10.Msigma Mi = ⊥ := by
    apply Disjoint.eq_bot
    refine Subgroup.disjoint_of_coprime_natCard (coprime_of_forall_prime_not_dvd ?_)
    intro r hr hrKi hrMσ
    exact (kappaHall_isPiSubgroup_sigmaCompl hKiMi hKi r
        (Nat.mem_primeFactors.mpr ⟨hr, hrKi, Nat.card_pos.ne'⟩))
      (OddOrder.BG.Ch3.S10.Msigma_isPiGroup Mi r
        (Nat.mem_primeFactors.mpr ⟨hr, hrMσ, Nat.card_pos.ne'⟩))
  have hC : Xi ≤ OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G) :=
    le_centralizerFactor_of_le_sup_of_le_Msigma inf_le_right inf_le_left hKiMσbot hXisup hXiMiσ
  -- Direction `⊇` (the swap with `(M, K, X*) ↔ (Mi, Ki, Xi)` exchanged).
  have hle2 : Ki ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) ≤
      K ⊔ Kstar := by
    have h := typeP_swap_Z_le hG (rfl :
      OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G) =
        OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G))
      hM hP hA hB hpi hXi hC hKM hK hXiK
    rwa [← hKstar] at h
  exact le_antisymm hle1 hle2

/-- **BG 14.7, Proposition 14.2(c) packaged** (the unique-centralizer clause): for a type-`P`
maximal `M` with Hall `κ(M)`-subgroup `K`, every line `Y ∈ ℰ¹(K*)` (`K* = C_{M_σ}(K)`) satisfies
`ℳ(C_G(Y)) = {M}`.  The Hall `(κ∪σ)'`-subgroup is produced internally, so callers supply only
`Y ≤ M_σ ⊓ C_G(K)`.  Used to show the `K_i*` are pairwise disjoint. -/
theorem typeP_centralizer_singleton [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    {p : ℕ} (hp : p.Prime) {Y : Subgroup G} (hY : Y ∈ elemAbelianOfRank G p 1)
    (hYK : Y ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    maximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) = {M} := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
    ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  have hUeq : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUeq]; exact hU'
  obtain ⟨_, _, _, _, _, hc, _⟩ := typeP_structure hG hM hP hKM hK rfl hU
  exact hc p hp Y hY hYK

/-- **BG 14.7, distinct neighbours have disjoint `K*`** (mmd L4005, "By Proposition 14.2(c)
applied to each `Mi`, `Ki* ∩ Kj* = 1` for `i ≠ j`"): if `Mi ≠ Mj` are type-`P` maximal
subgroups with Hall `κ`-subgroups `Ki`, `Kj`, then `C_{Mi_σ}(Ki) ⊓ C_{Mj_σ}(Kj) = ⊥`.

A common nonidentity element gives, by Cauchy, a line `Y ∈ ℰ¹(Ki* ⊓ Kj*)`; Proposition 14.2(c)
then forces `{Mi} = ℳ(C_G(Y)) = {Mj}`, i.e. `Mi = Mj`. -/
theorem typeP_neighbor_Kstar_inf_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {Mi Mj Ki Kj : Subgroup G}
    (hMi : Mi ∈ maximalSubgroups G) (hPi : IsTypeP Mi) (hKiMi : Ki ≤ Mi)
    (hKi : Ch03.IsHallSubgroup (kappa Mi) (Ki.subgroupOf Mi))
    (hMj : Mj ∈ maximalSubgroups G) (hPj : IsTypeP Mj) (hKjMj : Kj ≤ Mj)
    (hKj : Ch03.IsHallSubgroup (kappa Mj) (Kj.subgroupOf Mj))
    (hne : Mi ≠ Mj) :
    (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) ⊓
      (OddOrder.BG.Ch3.S10.Msigma Mj ⊓ Subgroup.centralizer (Kj : Set G)) = ⊥ := by
  classical
  by_contra hbot
  set H := (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) ⊓
    (OddOrder.BG.Ch3.S10.Msigma Mj ⊓ Subgroup.centralizer (Kj : Set G)) with hHdef
  -- Cauchy: a prime-order element `z ∈ H`, generating a line `Y ∈ ℰ¹(H)`.
  have : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hbot
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card (α := ↥H)).ne'
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  have hzH : (z : G) ∈ H := z.2
  have hzord : orderOf (z : G) = p := (orderOf_injective H.subtype H.subtype_injective z).trans hz
  have hYcard : Nat.card ↥(Subgroup.zpowers (z : G)) = p := by rw [Nat.card_zpowers, hzord]
  have hY : Subgroup.zpowers (z : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hYcard, by rw [hYcard, pow_one]⟩
  have hYH : Subgroup.zpowers (z : G) ≤ H := Subgroup.zpowers_le.mpr hzH
  -- `ℳ(C_G(Y)) = {Mi} = {Mj}`, so `Mi = Mj`, contradiction.
  have hi : maximalSubgroupsContaining (Subgroup.centralizer ((Subgroup.zpowers (z : G)) : Set G))
      = {Mi} := typeP_centralizer_singleton hG hMi hPi hKiMi hKi hp hY (hYH.trans inf_le_left)
  have hj : maximalSubgroupsContaining (Subgroup.centralizer ((Subgroup.zpowers (z : G)) : Set G))
      = {Mj} := typeP_centralizer_singleton hG hMj hPj hKjMj hKj hp hY (hYH.trans inf_le_right)
  exact hne (Set.singleton_eq_singleton_iff.mp (hi.symm.trans hj))

/-- **Inclusion–exclusion for subgroups meeting only at the identity** (BG 14.7 density backbone,
mmd L4031): for a nonempty finite family `{Sᵢ}_{i ∈ s}` of subgroups of `G` with `Sᵢ ⊓ Sⱼ = ⊥`
(`i ≠ j`), `|⋃ᵢ Sᵢ| + |s| = (∑ᵢ |Sᵢ|) + 1`.  Each `Sᵢ` contributes `|Sᵢ| − 1` non-identity
elements, all pairwise disjoint, plus the single shared identity.  In Theorem 14.7 (with `n + 1`
subgroups `Kᵢ*`) this gives `|T| = |Z| + n − ∑ kᵢ*` for `T = Z − ⋃ Kᵢ*`. -/
theorem ncard_biUnion_subgroup_add_card [Finite G] {ι : Type*}
    {s : Finset ι} (hs : s.Nonempty) (S : ι → Subgroup G)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → S i ⊓ S j = ⊥) :
    (⋃ i ∈ s, (S i : Set G)).ncard + s.card = (∑ i ∈ s, Nat.card ↥(S i)) + 1 := by
  classical
  have hcard_eq : ∀ i, (S i : Set G).ncard = Nat.card ↥(S i) := fun i =>
    (Nat.card_coe_set_eq (S i : Set G)).symm
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left, Finset.card_singleton,
      Finset.sum_singleton, hcard_eq]
  | cons a t ha htne ih =>
    have hpair_t : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → S i ⊓ S j = ⊥ := fun i hi j hj hij =>
      hpair i (Finset.mem_cons.mpr (Or.inr hi)) j (Finset.mem_cons.mpr (Or.inr hj)) hij
    have ih' := ih hpair_t
    -- `⋃_{cons a t} = S a ∪ ⋃_t`.
    have hunion : (⋃ i ∈ (Finset.cons a t ha), (S i : Set G))
        = (S a : Set G) ∪ ⋃ i ∈ t, (S i : Set G) := by
      ext x
      simp only [Set.mem_iUnion, Finset.mem_cons, Set.mem_union, exists_prop]
      constructor
      · rintro ⟨i, rfl | hi, hxi⟩
        · exact Or.inl hxi
        · exact Or.inr ⟨i, hi, hxi⟩
      · rintro (hxa | ⟨i, hi, hxi⟩)
        · exact ⟨a, Or.inl rfl, hxa⟩
        · exact ⟨i, Or.inr hi, hxi⟩
    -- `S a ∩ ⋃_t = {1}` (pairwise meet at the identity, `t` nonempty).
    have hinter : (S a : Set G) ∩ (⋃ i ∈ t, (S i : Set G)) = {1} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
      constructor
      · rintro ⟨hxa, i, hi, hxi⟩
        have hmem : x ∈ S a ⊓ S i := Subgroup.mem_inf.mpr ⟨hxa, hxi⟩
        rwa [hpair a (Finset.mem_cons_self a t) i (Finset.mem_cons.mpr (Or.inr hi))
          (fun h => ha (h ▸ hi)), Subgroup.mem_bot] at hmem
      · rintro rfl
        obtain ⟨i, hi⟩ := htne
        exact ⟨(S a).one_mem, i, hi, (S i).one_mem⟩
    have hunion_card : ((S a : Set G) ∪ ⋃ i ∈ t, (S i : Set G)).ncard + 1 =
        Nat.card ↥(S a) + (⋃ i ∈ t, (S i : Set G)).ncard := by
      have hfin1 : (S a : Set G).Finite := Set.Finite.subset Set.finite_univ (Set.subset_univ _)
      have hfin2 : (⋃ i ∈ t, (S i : Set G)).Finite :=
        Set.Finite.subset Set.finite_univ (Set.subset_univ _)
      have h := Set.ncard_union_add_ncard_inter (S a : Set G) (⋃ i ∈ t, (S i : Set G)) hfin1 hfin2
      rw [hinter, Set.ncard_singleton, hcard_eq a] at h
      exact h
    rw [hunion, Finset.card_cons, Finset.sum_cons]
    omega

/-- **BG 14.7, the `T = Z − ⋃ Kᵢ*` density count** (mmd L4031): for a nonempty finite family
`{Sᵢ}_{i ∈ s}` of subgroups of `Z` pairwise meeting at `⊥`,
`|Z − ⋃ Sᵢ| + (∑ |Sᵢ|) + 1 = |Z| + |s|`, i.e. `|T| = |Z| + (|s| − 1) − ∑ |Sᵢ|`.
With `s.card = n + 1` this is BG's `|T| = z + n − ∑ kᵢ*`.  Combines the inclusion–exclusion
count with the complement `|Z − ⋃| + |⋃| = |Z|`. -/
theorem ncard_sdiff_biUnion_subgroup [Finite G] {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (S : ι → Subgroup G) {Z : Subgroup G} (hSZ : ∀ i ∈ s, S i ≤ Z)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → S i ⊓ S j = ⊥) :
    ((Z : Set G) \ ⋃ i ∈ s, (S i : Set G)).ncard + (∑ i ∈ s, Nat.card ↥(S i)) + 1
      = Nat.card ↥Z + s.card := by
  classical
  have hsub : (⋃ i ∈ s, (S i : Set G)) ⊆ (Z : Set G) :=
    Set.iUnion₂_subset (fun i hi => SetLike.coe_subset_coe.mpr (hSZ i hi))
  have hIE := ncard_biUnion_subgroup_add_card hs S hpair
  have hdiff := Set.ncard_sdiff_add_ncard_of_subset hsub
  have hZcard : Nat.card ↥Z = (Z : Set G).ncard := Nat.card_coe_set_eq (Z : Set G)
  omega

/-- **BG 14.7, the canonical form of `Kᵢ*`** (mmd L4009): once the swap gives `Z = Kₙ ⊔ Kₙ*`
(`Kₙ* = C_{Nσ}(Kₙ)`), the factor `Kₙ*` is exactly `Z ⊓ Nσ` — the `σ(N)`-part of `Z`.  This
removes the dependence of `Kₙ*` on the chosen Hall `κ(N)`-subgroup `Kₙ`: it is the canonical
`Z ⊓ M_σ(N)`, so the family `{Kᵢ*}` can be defined choice-free as `N ↦ Z ⊓ Nσ`.

`⊆`: `Kₙ* ≤ Z` (a factor) and `Kₙ* ≤ Nσ`.  `⊇`: `Z ⊓ Nσ = (Kₙ ⊔ Kₙ*) ⊓ Nσ` is a `σ(N)`-group
inside the product `Kₙ × Kₙ*`, so the `σ`-projection lands it in `Kₙ*`. -/
theorem typeP_neighbor_Kstar_eq_Z_inf_Msigma [Finite G]
    {N K Kstar KN : Subgroup G} (hKNN : KN ≤ N)
    (hKN : Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N))
    (hZeq : K ⊔ Kstar = KN ⊔ (OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G))) :
    OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)
      = (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N := by
  classical
  refine le_antisymm (le_inf (hZeq ▸ le_sup_right) inf_le_left) ?_
  rw [hZeq]
  have hKNMσbot : KN ⊓ OddOrder.BG.Ch3.S10.Msigma N = ⊥ := by
    apply Disjoint.eq_bot
    refine Subgroup.disjoint_of_coprime_natCard (coprime_of_forall_prime_not_dvd ?_)
    intro r hr hrKN hrMσ
    exact (kappaHall_isPiSubgroup_sigmaCompl hKNN hKN r
        (Nat.mem_primeFactors.mpr ⟨hr, hrKN, Nat.card_pos.ne'⟩))
      (OddOrder.BG.Ch3.S10.Msigma_isPiGroup N r
        (Nat.mem_primeFactors.mpr ⟨hr, hrMσ, Nat.card_pos.ne'⟩))
  exact le_centralizerFactor_of_le_sup_of_le_Msigma inf_le_right inf_le_left hKNMσbot
    inf_le_left inf_le_right

/-- **BG 14.7, per-neighbour swap package** (mmd L3997-4009): for a type-`P` maximal `M` with Hall
data `K`, `K*`, a line `X ∈ ℰ_p¹(K)` (`C_{M_σ}(X) ≠ 1`) and a maximal `N ⊇ N_G(X)`, there is a
Hall `κ(N)`-subgroup `K_N` of `N` realising the swap: `Z = K ⊔ K* = K_N ⊔ K_N*` with the canonical
factor `K_N* = Z ⊓ M_σ(N)`.  This is the per-neighbour foundation that the `M_i` family iterates
over: assembles `typeP_neighbor_embed`/`typeP_neighbor_kappa` (neighbour data), a chosen line
`X* ∈ ℰ¹(K*)` with a Hall `κ(N)`-subgroup `K_N ∋ X*`, `typeP_swap_Z_eq` (the swap) and
`typeP_neighbor_Kstar_eq_Z_inf_Msigma` (the canonical form). -/
theorem exists_neighbor_kappaHall_swap [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXK : X ≤ K)
    (hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥)
    {N : Subgroup G} (hN : N ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))) :
    ∃ KN : Subgroup G, KN ≤ N ∧ Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N) ∧
      K ⊔ Kstar = KN ⊔ (OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)) ∧
      OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)
        = (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N := by
  classical
  obtain ⟨hnc, hZN, hXNσ⟩ := typeP_neighbor_embed hG hM hP hKM hK hKstar hU hX hXK hCX hN
  have hκ := typeP_neighbor_kappa hG hM hP hKM hK hKstar hU hX hXK hCX hN
  have hNmax : N ∈ maximalSubgroups G :=
    mem_maximalSubgroups.mpr (mem_maximalSubgroupsContaining.mp hN).1
  have hKstarne : Kstar ≠ ⊥ := (typeP_structure hG hM hP hKM hK hKstar hU).2.1
  have : Nontrivial ↥Kstar := (Subgroup.nontrivial_iff_ne_bot _).mpr hKstarne
  obtain ⟨q, hq⟩ : (Nat.card ↥Kstar).primeFactors.Nonempty :=
    Nat.nonempty_primeFactors.mpr Finite.one_lt_card
  have hqκN : q ∈ kappa N := hκ q hq
  have : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hq⟩
  -- A line `X* ∈ ℰ¹(K*)` of prime order `q`, inside a Hall `κ(N)`-subgroup `K_N`.
  obtain ⟨x', hx'⟩ := exists_prime_orderOf_dvd_card' q (Nat.dvd_of_mem_primeFactors hq)
  have hx'ord : orderOf (x' : G) = q :=
    (orderOf_injective Kstar.subtype Kstar.subtype_injective x').trans hx'
  have hXstarcard : Nat.card ↥(Subgroup.zpowers (x' : G)) = q := by rw [Nat.card_zpowers, hx'ord]
  have hXstarElem : Subgroup.zpowers (x' : G) ∈ elemAbelianOfRank G q 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXstarcard, by rw [hXstarcard, pow_one]⟩
  have hXstarKstar : Subgroup.zpowers (x' : G) ≤ Kstar := Subgroup.zpowers_le.mpr x'.2
  have hXstarκN : ∀ r ∈ (Nat.card ↥(Subgroup.zpowers (x' : G))).primeFactors, r ∈ kappa N := by
    intro r hr
    rw [hXstarcard, (Nat.prime_of_mem_primeFactors hq).primeFactors, Finset.mem_singleton] at hr
    exact hr ▸ hqκN
  obtain ⟨KN, hKNN, hKN, hXstarKN⟩ :=
    exists_isHallSubgroup_kappa_ge hG hNmax (hXstarKstar.trans (le_sup_right.trans hZN)) hXstarκN
  have hswap : K ⊔ Kstar =
      KN ⊔ (OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)) :=
    typeP_swap_Z_eq hG hM hP hKM hK hKstar hU hNmax ⟨q, hqκN⟩ hZN hκ
      (Nat.prime_of_mem_primeFactors hq) hXstarElem hXstarKstar hXstarKN
      Fact.out hX hXK hXNσ hKNN hKN
  exact ⟨KN, hKNN, hKN, hswap, typeP_neighbor_Kstar_eq_Z_inf_Msigma hKNN hKN hswap⟩

/-- **BG 14.7, coverage of `κ(M)`-primes** (mmd L4007): every prime `p ∣ |K|` lies in `σ(N)` for
some nonconjugate type-`P` neighbour `N` containing `Z`.  A line `X ∈ ℰ_p¹(K)` (Cauchy in `K`) has
a partner `N ∈ 𝓜(N_G(X))` (`exists_typeP_partner`) with `X ⊆ M_σ(N)`, so `p ∈ σ(N)`.  Together with
`M` itself (covering `σ(M) ⊇ π(K*)`), this gives the coverage `⋃ σ(Mᵢ) ⊇ π(Z)` that forces
`⨆ Kᵢ* = Z`. -/
theorem exists_typeP_neighbor_mem_sigma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card ↥K) :
    ∃ N : Subgroup G, N ∈ maximalSubgroups G ∧ IsTypeP N ∧ ¬ IsConjugateSubgroup M N ∧
      p ∈ OddOrder.BG.Ch3.S10.sigma N ∧ K ⊔ Kstar ≤ N := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hxord : orderOf (x : G) = p := (orderOf_injective K.subtype K.subtype_injective x).trans hx
  have hXcard : Nat.card ↥(Subgroup.zpowers (x : G)) = p := by rw [Nat.card_zpowers, hxord]
  have hXelem : Subgroup.zpowers (x : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXK : Subgroup.zpowers (x : G) ≤ K := Subgroup.zpowers_le.mpr x.2
  obtain ⟨N, hNmem, hnc, hZN, hXNσ, _, hPN⟩ :=
    exists_typeP_partner hG hM hP hKM hK hKstar hU hXelem hXK
  have hNmax : N ∈ maximalSubgroups G :=
    mem_maximalSubgroups.mpr (mem_maximalSubgroupsContaining.mp hNmem).1
  -- `p ∈ σ(N)` since `X ⊆ M_σ(N)` and `p ∣ |X|`.
  have hpσN : p ∈ OddOrder.BG.Ch3.S10.sigma N :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup N p (Nat.mem_primeFactors.mpr
      ⟨hp, (by rw [hXcard] : p ∣ Nat.card ↥(Subgroup.zpowers (x : G))).trans
        (Subgroup.card_dvd_of_le hXNσ), Nat.card_pos.ne'⟩)
  exact ⟨N, hNmax, hPN, hnc, hpσN, hZN⟩

/-- **Both factors of an internal direct product are normal**: in `A ⊔ B` with `B ≤ C_G(A)`
(so `A`, `B` commute), `A ⊔ B ≤ N_G(A) ⊓ N_G(B)`.  In Theorem 14.7, applied to the swap
`Z = K_N ⊔ K_N*` (`K_N* ≤ C(K_N)`), it makes both `K_N` and `K_N* = Z ⊓ M_σ(N)` normal in `Z` —
the input to pairwise commutativity of the `Kᵢ*` (for `z = ∏ kᵢ*`), to pairwise nonconjugacy of
the `Mᵢ`, and to the `n = 1` collapse (`Kᵢ ◁ Z` is the unique `σ(Mᵢ)'`-Hall). -/
theorem sup_le_normalizer_inf_of_commute {A B : Subgroup G}
    (h : B ≤ Subgroup.centralizer (A : Set G)) :
    A ⊔ B ≤ Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (B : Set G) := by
  have hAB : A ≤ Subgroup.centralizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.mem_centralizer_iff.mp (h hb) a ha).symm
  exact le_inf
    (sup_le Subgroup.le_normalizer (h.trans (Subgroup.centralizer_le_normalizer _)))
    (sup_le (hAB.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer)

/-- **Internal direct product of two commuting subgroups**: if `H`, `K` commute elementwise and
`H ⊓ K = ⊥`, then `|H ⊔ K| = |H|·|K|`.  (The `noncommCoprod` map `↥H × ↥K → ↥(H ⊔ K)` is an
isomorphism.)  Used by the family argument for `|Kᵢ* ⊔ Kⱼ*| = kᵢ*·kⱼ*` (pairwise nonconjugacy) and
in the `n = 1` collapse. -/
theorem card_sup_of_commute_of_disjoint [Finite G] {H K : Subgroup G}
    (hcomm : ∀ x ∈ H, ∀ y ∈ K, Commute x y) (hdisj : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card ↥H * Nat.card ↥K := by
  classical
  have hc : ∀ (a : ↥H) (b : ↥K), Commute (H.subtype a) (K.subtype b) :=
    fun a b => hcomm (a : G) a.2 (b : G) b.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod H.subtype K.subtype hc) :=
    (MonoidHom.noncommCoprod_injective _ _ hc).mpr
      ⟨H.subtype_injective, K.subtype_injective, by
        rw [H.range_subtype, K.range_subtype]; exact disjoint_iff.mpr hdisj⟩
  have hrange : (MonoidHom.noncommCoprod H.subtype K.subtype hc).range = H ⊔ K := by
    rw [MonoidHom.noncommCoprod_range, H.range_subtype, K.range_subtype]
  rw [← Nat.card_congr
      ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).toEquiv, Nat.card_prod]

/-- **Subgroups normal in a common overgroup, meeting trivially, commute**: if `A, B ≤ Z` with
`Z ≤ N_G(A)`, `Z ≤ N_G(B)` (so `A, B ◁ Z`) and `A ⊓ B = ⊥`, then every element of `A` commutes with
every element of `B`.  (The commutator `[x,y]` lies in `A ⊓ B = ⊥`.)  Used for `|Kᵢ* ⊔ Kⱼ*| =
kᵢ*·kⱼ*` once the `Kᵢ*` are known normal in `Z`. -/
theorem commute_of_le_normalizer_of_disjoint {Z A B : Subgroup G}
    (hAZ : A ≤ Z) (hBZ : B ≤ Z) (hAnorm : Z ≤ Subgroup.normalizer (A : Set G))
    (hBnorm : Z ≤ Subgroup.normalizer (B : Set G)) (hdisj : A ⊓ B = ⊥) :
    ∀ x ∈ A, ∀ y ∈ B, Commute x y := by
  have hAn : (A.subgroupOf Z).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAnorm
  have hBn : (B.subgroupOf Z).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hBnorm
  have hdisjZ : Disjoint (A.subgroupOf Z) (B.subgroupOf Z) := by
    rw [Subgroup.disjoint_def]
    intro g hgA hgB
    have : (g : G) ∈ A ⊓ B :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hgA, Subgroup.mem_subgroupOf.mp hgB⟩
    rw [hdisj, Subgroup.mem_bot] at this
    exact OneMemClass.coe_eq_one.mp this
  intro x hx y hy
  have h := Subgroup.commute_of_normal_of_disjoint (A.subgroupOf Z) (B.subgroupOf Z) hAn hBn hdisjZ
    ⟨x, hAZ hx⟩ ⟨y, hBZ hy⟩ (Subgroup.mem_subgroupOf.mpr hx) (Subgroup.mem_subgroupOf.mpr hy)
  exact h.map Z.subtype

/-- **BG 14.7, pairwise nonconjugacy of the family** (mmd L4015, "the `Mᵢ` are pairwise not
conjugate"): if `M₁`, `M₂` are maximal subgroups whose swap factors `Zₖ = M_σ(Mₖ) ⊓ C(Kₖ)` (the
`σ(Mₖ)`-Halls of `Z = K ⊔ K*`, `Kₖ` Hall `κ(Mₖ)`) meet trivially and `Z₂ ≠ ⊥`, then `M₁`, `M₂` are
nonconjugate.

Were they conjugate, `σ(M₁) = σ(M₂) =: τ`, so `Z₁`, `Z₂` are both `τ`-Halls of `Z`, normal
(direct factors) and disjoint.  Then `|Z₁ ⊔ Z₂| = z₁ z₂ ∣ z = k₁ z₁`, giving `z₂ ∣ k₁`; but `z₂` is
a `τ`-number and `k₁` a `τ'`-number, so `z₂ = 1`, contradicting `Z₂ ≠ ⊥`.  Feeds Lemma 14.5(b)
(pairwise disjointness of the `𝒞_G(M̃ᵢ)`). -/
theorem typeP_family_nonconjugate [Finite G]
    {K Kstar M₁ M₂ K₁ K₂ : Subgroup G}
    (hK₁M₁ : K₁ ≤ M₁) (hK₁ : Ch03.IsHallSubgroup (kappa M₁) (K₁.subgroupOf M₁))
    (hsw₁ : K ⊔ Kstar = K₁ ⊔ (OddOrder.BG.Ch3.S10.Msigma M₁ ⊓ Subgroup.centralizer (K₁ : Set G)))
    (hsw₂ : K ⊔ Kstar = K₂ ⊔ (OddOrder.BG.Ch3.S10.Msigma M₂ ⊓ Subgroup.centralizer (K₂ : Set G)))
    (hne₂ : OddOrder.BG.Ch3.S10.Msigma M₂ ⊓ Subgroup.centralizer (K₂ : Set G) ≠ ⊥)
    (hdisj : (OddOrder.BG.Ch3.S10.Msigma M₁ ⊓ Subgroup.centralizer (K₁ : Set G)) ⊓
      (OddOrder.BG.Ch3.S10.Msigma M₂ ⊓ Subgroup.centralizer (K₂ : Set G)) = ⊥) :
    ¬ IsConjugateSubgroup M₁ M₂ := by
  classical
  set Z₁ := OddOrder.BG.Ch3.S10.Msigma M₁ ⊓ Subgroup.centralizer (K₁ : Set G) with hZ₁def
  set Z₂ := OddOrder.BG.Ch3.S10.Msigma M₂ ⊓ Subgroup.centralizer (K₂ : Set G) with hZ₂def
  rintro ⟨g, hg⟩
  have hσ : OddOrder.BG.Ch3.S10.sigma M₂ = OddOrder.BG.Ch3.S10.sigma M₁ := by
    rw [← hg]; exact sigma_conj_smul_eq g M₁
  have hZ₁CK₁ : Z₁ ≤ Subgroup.centralizer (K₁ : Set G) := by rw [hZ₁def]; exact inf_le_right
  have hZ₁Mσ : Z₁ ≤ OddOrder.BG.Ch3.S10.Msigma M₁ := by rw [hZ₁def]; exact inf_le_left
  have hZ₂CK₂ : Z₂ ≤ Subgroup.centralizer (K₂ : Set G) := by rw [hZ₂def]; exact inf_le_right
  have hZ₂Mσ : Z₂ ≤ OddOrder.BG.Ch3.S10.Msigma M₂ := by rw [hZ₂def]; exact inf_le_left
  have hcommK₁Z₁ : ∀ x ∈ K₁, ∀ y ∈ Z₁, Commute x y := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (hZ₁CK₁ hy) x hx
  have hdisjK₁Z₁ : K₁ ⊓ Z₁ = ⊥ := by
    apply Disjoint.eq_bot
    refine Subgroup.disjoint_of_coprime_natCard (coprime_of_forall_prime_not_dvd ?_)
    intro r hr hrK₁ hrZ₁
    exact kappaHall_isPiSubgroup_sigmaCompl hK₁M₁ hK₁ r
        (Nat.mem_primeFactors.mpr ⟨hr, hrK₁, Nat.card_pos.ne'⟩)
      (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M₁ r (Nat.mem_primeFactors.mpr
        ⟨hr, hrZ₁.trans (Subgroup.card_dvd_of_le hZ₁Mσ), Nat.card_pos.ne'⟩))
  have hzcard : Nat.card ↥(K ⊔ Kstar) = Nat.card ↥K₁ * Nat.card ↥Z₁ := by
    rw [hsw₁]; exact card_sup_of_commute_of_disjoint hcommK₁Z₁ hdisjK₁Z₁
  have hZ₁Z : Z₁ ≤ K ⊔ Kstar := by rw [hsw₁]; exact le_sup_right
  have hZ₂Z : Z₂ ≤ K ⊔ Kstar := by rw [hsw₂]; exact le_sup_right
  have hZ₁norm : K ⊔ Kstar ≤ Subgroup.normalizer (Z₁ : Set G) := by
    rw [hsw₁]; exact (sup_le_normalizer_inf_of_commute hZ₁CK₁).trans inf_le_right
  have hZ₂norm : K ⊔ Kstar ≤ Subgroup.normalizer (Z₂ : Set G) := by
    rw [hsw₂]; exact (sup_le_normalizer_inf_of_commute hZ₂CK₂).trans inf_le_right
  have hz12 : Nat.card ↥(Z₁ ⊔ Z₂) = Nat.card ↥Z₁ * Nat.card ↥Z₂ :=
    card_sup_of_commute_of_disjoint
      (commute_of_le_normalizer_of_disjoint hZ₁Z hZ₂Z hZ₁norm hZ₂norm hdisj) hdisj
  have hdvd : Nat.card ↥(Z₁ ⊔ Z₂) ∣ Nat.card ↥(K ⊔ Kstar) :=
    Subgroup.card_dvd_of_le (sup_le hZ₁Z hZ₂Z)
  rw [hz12, hzcard] at hdvd
  have hZ₂dvdK₁ : Nat.card ↥Z₂ ∣ Nat.card ↥K₁ := by
    rw [mul_comm (Nat.card ↥K₁)] at hdvd
    exact (Nat.mul_dvd_mul_iff_left Nat.card_pos).mp hdvd
  have hcop : Nat.Coprime (Nat.card ↥Z₂) (Nat.card ↥K₁) :=
    coprime_of_forall_prime_not_dvd (fun r hr hrZ₂ hrK₁ =>
      kappaHall_isPiSubgroup_sigmaCompl hK₁M₁ hK₁ r
        (Nat.mem_primeFactors.mpr ⟨hr, hrK₁, Nat.card_pos.ne'⟩)
        (hσ ▸ OddOrder.BG.Ch3.S10.Msigma_isPiGroup M₂ r (Nat.mem_primeFactors.mpr
          ⟨hr, hrZ₂.trans (Subgroup.card_dvd_of_le hZ₂Mσ), Nat.card_pos.ne'⟩)))
  have hZ₂one : Nat.card ↥Z₂ = 1 := (Nat.gcd_eq_left hZ₂dvdK₁).symm.trans hcop
  exact hne₂ (Subgroup.card_eq_one.mp hZ₂one)

/-- **BG 14.7, per-neighbour swap package with normality** (mmd L3997-4015): the per-neighbour
swap `exists_neighbor_kappaHall_swap`, restated with the canonical factor `K_N* = Z ⊓ M_σ(N)`
folded into the swap and augmented with `K_N* ◁ Z` (`Z ≤ N_G(K_N*)`).  This is the exact per-member
data the `M_i` family consumes: the swap `Z = K_N ⊔ K_N*`, the canonical `K_N*`, and its normality
in `Z` (for pairwise commutativity, the `|T|` count, and the `n = 1` collapse). -/
theorem exists_neighbor_kappaHall_swap_normal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXK : X ≤ K)
    (hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥)
    {N : Subgroup G} (hN : N ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))) :
    ∃ KN : Subgroup G, KN ≤ N ∧ Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N) ∧
      K ⊔ Kstar = KN ⊔ ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) ∧
      K ⊔ Kstar ≤ Subgroup.normalizer
        (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) := by
  obtain ⟨KN, hKNN, hKN, hswap, hcanon⟩ :=
    exists_neighbor_kappaHall_swap hG hM hP hKM hK hKstar hU hX hXK hCX hN
  refine ⟨KN, hKNN, hKN, hswap.trans (by rw [hcanon]), ?_⟩
  rw [← hcanon, hswap]
  exact (sup_le_normalizer_inf_of_commute inf_le_right).trans inf_le_right

/-- **BG 14.7, full per-neighbour data** (mmd L3997-4015): the complete per-member package the
`M_i` family consumes — for a line `X ∈ ℰ_p¹(K)` and a maximal `N ⊇ N_G(X)`, a Hall `κ(N)`-subgroup
`K_N` with the swap `Z = K_N ⊔ K_N*` (canonical `K_N* = Z ⊓ M_σ(N)`), `K_N* ◁ Z`, `N` type-`P`, and
`K_N* ≠ ⊥` (since `X ≤ K_N*`, as `X ≤ K ≤ Z` and `X ⊆ M_σ(N)`).  Builds on
`exists_neighbor_kappaHall_swap_normal` + `typeP_neighbor_embed`/`typeP_neighbor_kappa`. -/
theorem exists_neighbor_full [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXK : X ≤ K)
    (hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥)
    {N : Subgroup G} (hN : N ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))) :
    ∃ KN : Subgroup G, KN ≤ N ∧ Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N) ∧
      K ⊔ Kstar = KN ⊔ ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) ∧
      K ⊔ Kstar ≤ Subgroup.normalizer
        (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) ∧
      IsTypeP N ∧ (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N ≠ ⊥ := by
  obtain ⟨KN, hKNN, hKN, hswap, hnorm⟩ :=
    exists_neighbor_kappaHall_swap_normal hG hM hP hKM hK hKstar hU hX hXK hCX hN
  obtain ⟨_, _, hXNσ⟩ := typeP_neighbor_embed hG hM hP hKM hK hKstar hU hX hXK hCX hN
  have hκ := typeP_neighbor_kappa hG hM hP hKM hK hKstar hU hX hXK hCX hN
  have hKstarne : Kstar ≠ ⊥ := (typeP_structure hG hM hP hKM hK hKstar hU).2.1
  have : Nontrivial ↥Kstar := (Subgroup.nontrivial_iff_ne_bot _).mpr hKstarne
  obtain ⟨q, hq⟩ : (Nat.card ↥Kstar).primeFactors.Nonempty :=
    Nat.nonempty_primeFactors.mpr Finite.one_lt_card
  have hPN : IsTypeP N := ⟨q, hκ q hq⟩
  have hXKstar : X ≤ (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N :=
    le_inf (hXK.trans le_sup_left) hXNσ
  have hKstarNne : (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N ≠ ⊥ := fun hbot =>
    ne_bot_of_mem_elemAbelianOfRank_one hX (le_bot_iff.mp (hbot ▸ hXKstar))
  exact ⟨KN, hKNN, hKN, hswap, hnorm, hPN, hKstarNne⟩

/-- **BG 14.7, two family members are nonconjugate** (mmd L4015): given two type-`P` maximals
`N₁ ≠ N₂` with Hall `κ`-subgroups and the swaps `Z = Kₖ ⊔ (M_σ(Nₖ) ⊓ C(Kₖ))` (`Z₂* ≠ ⊥`), the
members are nonconjugate.  Combines Proposition 14.2(c) (`typeP_neighbor_Kstar_inf_eq_bot`: the swap
factors meet trivially since the members are distinct) with `typeP_family_nonconjugate`.  This is
the per-pair input to the family's pairwise nonconjugacy (and thence Lemma 14.5(b)). -/
theorem neighbor_pair_nonconjugate [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {K Kstar N₁ N₂ K₁ K₂ : Subgroup G}
    (hN₁ : N₁ ∈ maximalSubgroups G) (hP₁ : IsTypeP N₁) (hK₁N₁ : K₁ ≤ N₁)
    (hK₁ : Ch03.IsHallSubgroup (kappa N₁) (K₁.subgroupOf N₁))
    (hN₂ : N₂ ∈ maximalSubgroups G) (hP₂ : IsTypeP N₂) (hK₂N₂ : K₂ ≤ N₂)
    (hK₂ : Ch03.IsHallSubgroup (kappa N₂) (K₂.subgroupOf N₂))
    (hsw₁ : K ⊔ Kstar = K₁ ⊔ (OddOrder.BG.Ch3.S10.Msigma N₁ ⊓ Subgroup.centralizer (K₁ : Set G)))
    (hsw₂ : K ⊔ Kstar = K₂ ⊔ (OddOrder.BG.Ch3.S10.Msigma N₂ ⊓ Subgroup.centralizer (K₂ : Set G)))
    (hne₂ : OddOrder.BG.Ch3.S10.Msigma N₂ ⊓ Subgroup.centralizer (K₂ : Set G) ≠ ⊥)
    (hne : N₁ ≠ N₂) :
    ¬ IsConjugateSubgroup N₁ N₂ :=
  typeP_family_nonconjugate hK₁N₁ hK₁ hsw₁ hsw₂ hne₂
    (typeP_neighbor_Kstar_inf_eq_bot hG hN₁ hP₁ hK₁N₁ hK₁ hN₂ hP₂ hK₂N₂ hK₂ hne)

/-- **BG 14.7, the base member `M` (`i = 0`)** (mmd L4003, "let `M₀ = M`"): `M`'s own data in the
same canonical shape the family uses.  `K_M* = Z ⊓ M_σ(M)` equals `K* = Kstar`, the swap
`Z = K ⊔ K_M*` is trivial, `K_M* ◁ Z`, and `K_M* ≠ ⊥` (since `Kstar ≠ ⊥`).  Aligns `M` with the
neighbours (`exists_neighbor_full`) so the family `{M} ∪ {neighbours}` has uniform per-member
data. -/
theorem typeP_self_member [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma M = Kstar ∧
    K ⊔ Kstar = K ⊔ ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma M) ∧
    K ⊔ Kstar ≤ Subgroup.normalizer
      (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) ∧
    (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma M ≠ ⊥ := by
  have hcanon : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
      = (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma M :=
    typeP_neighbor_Kstar_eq_Z_inf_Msigma hKM hK (by rw [hKstar])
  have hKstarEq : (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma M = Kstar := hcanon.symm.trans
      hKstar.symm
  refine ⟨hKstarEq, by rw [hKstarEq], ?_, ?_⟩
  · rw [hKstarEq, hKstar]
    exact (sup_le_normalizer_inf_of_commute inf_le_right).trans inf_le_right
  · rw [hKstarEq]; exact (typeP_structure hG hM hP hKM hK hKstar hU).2.1

/-- **A subgroup of order coprime to a normal subgroup's index lies inside it** (BG 14.7 `n = 1`
collapse, mmd L4043): if `N ◁ G` and `|H|` is coprime to `[G : N]`, then `H ≤ N`.  (The image of
`H` in `G/N` has order dividing both `|H|` and `[G : N]`, hence `1`, so `H ≤ ker = N`.)  In the
collapse, applied with `N = Kᵢ` (the normal `σ(Mᵢ)'`-Hall of `Z`, `[Z : Kᵢ] = kᵢ*` a `σ(Mᵢ)`-number)
and `H = Kⱼ*` (a `σ(Mᵢ)'`-group), it gives `Kⱼ* ≤ Kᵢ`; with `|Kᵢ|` prime this forces `Kⱼ* = Kᵢ`. -/
theorem le_of_coprime_index {N H : Subgroup G} [N.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) N.index) : H ≤ N := by
  have hd1 : Nat.card ↥(H.map (QuotientGroup.mk' N)) ∣ Nat.card ↥H :=
    Subgroup.card_map_dvd H (QuotientGroup.mk' N)
  have hd2 : Nat.card ↥(H.map (QuotientGroup.mk' N)) ∣ N.index :=
    Subgroup.card_subgroup_dvd_card _
  have hcard1 : Nat.card ↥(H.map (QuotientGroup.mk' N)) = 1 :=
    Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hd1 hd2)
  have hbot : H.map (QuotientGroup.mk' N) = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard1
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot

/-- **BG 14.7, unified per-neighbour data** (mmd L3997-4015): the single per-member source for the
family, exposing the **raw** swap factor `K_N* = M_σ(N) ⊓ C(K_N)` (for pairwise nonconjugacy and the
`z = k_N·k_N*` card) together with the **canonical identity** `K_N* = Z ⊓ M_σ(N)` (for the family's
`Kᵢ*`), plus `N` type-`P` and `K_N* ≠ ⊥`.  Resolves the raw/canonical form tension at the source. -/
theorem exists_neighbor_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXK : X ≤ K)
    (hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥)
    {N : Subgroup G} (hN : N ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))) :
    ∃ KN : Subgroup G, KN ≤ N ∧ Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N) ∧
      K ⊔ Kstar = KN ⊔ (OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)) ∧
      OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)
        = (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N ∧
      IsTypeP N ∧
      OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G) ≠ ⊥ := by
  obtain ⟨KN, hKNN, hKN, hswap, hcanon⟩ :=
    exists_neighbor_kappaHall_swap hG hM hP hKM hK hKstar hU hX hXK hCX hN
  obtain ⟨_, _, hXNσ⟩ := typeP_neighbor_embed hG hM hP hKM hK hKstar hU hX hXK hCX hN
  have hκ := typeP_neighbor_kappa hG hM hP hKM hK hKstar hU hX hXK hCX hN
  have hKstarne : Kstar ≠ ⊥ := (typeP_structure hG hM hP hKM hK hKstar hU).2.1
  have : Nontrivial ↥Kstar := (Subgroup.nontrivial_iff_ne_bot _).mpr hKstarne
  obtain ⟨q, hq⟩ : (Nat.card ↥Kstar).primeFactors.Nonempty :=
    Nat.nonempty_primeFactors.mpr Finite.one_lt_card
  have hXcanon : X ≤ (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N :=
    le_inf (hXK.trans le_sup_left) hXNσ
  exact ⟨KN, hKNN, hKN, hswap, hcanon, ⟨q, hκ q hq⟩, fun hbot =>
    ne_bot_of_mem_elemAbelianOfRank_one hX (le_bot_iff.mp (hbot ▸ hcanon.symm ▸ hXcanon))⟩

/-- **BG 14.7, the family member predicate** (mmd L4003): `N` is a member of the type-`P` family
attached to `Z` — either `N = M`, or `N` is a maximal subgroup over `N_G(X)` for a line
`X ∈ ℰ_p¹(K)`. -/
def IsZFamilyMember (M K N : Subgroup G) : Prop :=
  N = M ∨ ∃ (p : ℕ) (X : Subgroup G), p.Prime ∧ X ∈ elemAbelianOfRank G p 1 ∧ X ≤ K ∧
    N ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))

/-- **BG 14.7, uniform per-member data for the family** (mmd L4003-4015): every member `N` of the
type-`P` family is a type-`P` maximal subgroup containing `Z = K ⊔ K*`, with a Hall `κ(N)`-subgroup
`K_N` realising the swap `Z = K_N ⊔ K_N*` (raw `K_N* = M_σ(N) ⊓ C(K_N)`, canonical
`K_N* = Z ⊓ M_σ(N)`, `K_N* ≠ ⊥`).  Case-split on `N = M` (`typeP_self_member`) vs a neighbour
(`exists_neighbor_data`); this is the data the family `Finset` carries. -/
theorem typeP_family_member_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N : Subgroup G} (hN : IsZFamilyMember M K N) :
    N ∈ maximalSubgroups G ∧ IsTypeP N ∧ K ⊔ Kstar ≤ N ∧
    ∃ KN : Subgroup G, KN ≤ N ∧ Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N) ∧
      K ⊔ Kstar = KN ⊔ (OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)) ∧
      OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)
        = (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N ∧
      OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G) ≠ ⊥ := by
  rcases hN with hNM | ⟨p, X, hp, hX, hXK, hN⟩
  · -- `N = M`: base member.
    rw [hNM]
    obtain ⟨hKstarEq, _, _, _⟩ := typeP_self_member hG hM hP hKM hK hKstar hU
    refine ⟨hM, hP, sup_le hKM (hKstar ▸ inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le M)),
      K, hKM, hK, by rw [hKstar], (hKstarEq.trans hKstar).symm,
      hKstar ▸ (typeP_structure hG hM hP hKM hK hKstar hU).2.1⟩
  · -- neighbour from a line `X`.
    have : Fact p.Prime := ⟨hp⟩
    have hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ := by
      intro hbot
      refine (typeP_structure hG hM hP hKM hK hKstar hU).2.1 (le_bot_iff.mp ?_)
      rw [hKstar]
      calc OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
          ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) :=
            inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXK))
        _ = ⊥ := hbot
    obtain ⟨KN, hKNN, hKN, hswap, hcanon, hPN, hne⟩ :=
      exists_neighbor_data hG hM hP hKM hK hKstar hU hX hXK hCX hN
    refine ⟨mem_maximalSubgroups.mpr (mem_maximalSubgroupsContaining.mp hN).1, hPN,
      hswap ▸ sup_le hKNN (inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le N)),
      KN, hKNN, hKN, hswap, hcanon, hne⟩

/-- **BG 14.7, the family is pairwise nonconjugate** (mmd L4015): any two distinct members of the
type-`P` family are nonconjugate.  Extracts each member's swap data
(`typeP_family_member_data`) and applies `neighbor_pair_nonconjugate`.  Feeds Lemma 14.5(b)
(pairwise disjointness of the `𝒞_G(M̃ᵢ)`). -/
theorem typeP_family_pairwise_nonconjugate [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N₁ N₂ : Subgroup G} (hN₁ : IsZFamilyMember M K N₁) (hN₂ : IsZFamilyMember M K N₂)
    (hne : N₁ ≠ N₂) :
    ¬ IsConjugateSubgroup N₁ N₂ := by
  obtain ⟨hN₁max, hP₁, _, K₁, hK₁N₁, hK₁, hsw₁, _, _⟩ :=
    typeP_family_member_data hG hM hP hKM hK hKstar hU hN₁
  obtain ⟨hN₂max, hP₂, _, K₂, hK₂N₂, hK₂, hsw₂, _, hne₂⟩ :=
    typeP_family_member_data hG hM hP hKM hK hKstar hU hN₂
  exact neighbor_pair_nonconjugate hG hN₁max hP₁ hK₁N₁ hK₁ hN₂max hP₂ hK₂N₂ hK₂ hsw₁ hsw₂ hne₂ hne

/-- **BG 14.7, the family `Kᵢ*` are pairwise disjoint** (mmd L4005): for distinct members
`N₁ ≠ N₂`, the canonical factors `Kᵢ* = Z ⊓ M_σ(Nᵢ)` meet trivially.  Distinct members are
nonconjugate (`typeP_family_pairwise_nonconjugate`), so `σ(N₁)`, `σ(N₂)` are disjoint
(Theorem 13.9), hence `M_σ(N₁) ⊓ M_σ(N₂) = ⊥` (coprime `σ`-groups), and a fortiori the `Kᵢ*` meet
trivially.  This is the pairwise-`⊥` input to the inclusion–exclusion `|T|` count. -/
theorem typeP_family_Kstar_disjoint [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N₁ N₂ : Subgroup G} (hN₁ : IsZFamilyMember M K N₁) (hN₂ : IsZFamilyMember M K N₂)
    (hne : N₁ ≠ N₂) :
    ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N₁) ⊓
      ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N₂) = ⊥ := by
  obtain ⟨hN₁max, _, _, _⟩ := typeP_family_member_data hG hM hP hKM hK hKstar hU hN₁
  obtain ⟨hN₂max, _, _, _⟩ := typeP_family_member_data hG hM hP hKM hK hKstar hU hN₂
  have hnc := typeP_family_pairwise_nonconjugate hG hM hP hKM hK hKstar hU hN₁ hN₂ hne
  have hσdisj := OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hN₁max hN₂max hnc
  have hMσdisj : OddOrder.BG.Ch3.S10.Msigma N₁ ⊓ OddOrder.BG.Ch3.S10.Msigma N₂ = ⊥ := by
    apply Disjoint.eq_bot
    refine Subgroup.disjoint_of_coprime_natCard (coprime_of_forall_prime_not_dvd ?_)
    intro r hr hr₁ hr₂
    exact Set.disjoint_left.mp hσdisj
      (OddOrder.BG.Ch3.S10.Msigma_isPiGroup N₁ r
        (Nat.mem_primeFactors.mpr ⟨hr, hr₁, Nat.card_pos.ne'⟩))
      (OddOrder.BG.Ch3.S10.Msigma_isPiGroup N₂ r
        (Nat.mem_primeFactors.mpr ⟨hr, hr₂, Nat.card_pos.ne'⟩))
  exact le_bot_iff.mp (le_trans (inf_le_inf inf_le_right inf_le_right) (le_of_eq hMσdisj))

/-- **BG 14.7, the type-`P` family as a `Finset`** (mmd L4003): `{N | IsZFamilyMember M K N}`
collected as a `Finset` (finite since `Subgroup G` is finite). -/
noncomputable def ZFamilyFinset [Finite G] (M K : Subgroup G) : Finset (Subgroup G) :=
  (Set.toFinite {N | IsZFamilyMember M K N}).toFinset

theorem mem_ZFamilyFinset [Finite G] {M K N : Subgroup G} :
    N ∈ ZFamilyFinset M K ↔ IsZFamilyMember M K N :=
  Set.Finite.mem_toFinset _

theorem ZFamilyFinset_nonempty [Finite G] {M K : Subgroup G} : (ZFamilyFinset M K).Nonempty :=
  ⟨M, mem_ZFamilyFinset.mpr (Or.inl rfl)⟩

/-- **BG 14.7, the `|T|` count for the family** (mmd L4031): with `T = Z − ⋃_{N} (Z ⊓ M_σ(N))`
over the family `ZFamilyFinset`, `|T| + ∑ |Kᵢ*| + 1 = |Z| + |family|` — i.e. `|T| = z + n − ∑ kᵢ*`
(`|family| = n + 1`).  Direct instance of inclusion–exclusion
(`ncard_sdiff_biUnion_subgroup`) with the pairwise disjointness `typeP_family_Kstar_disjoint`. -/
theorem typeP_family_T_count [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    (((K ⊔ Kstar : Subgroup G) : Set G) \
        ⋃ N ∈ ZFamilyFinset M K,
          (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G)).ncard
      + (∑ N ∈ ZFamilyFinset M K, Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N)) + 1
      = Nat.card ↥(K ⊔ Kstar) + (ZFamilyFinset M K).card := by
  refine ncard_sdiff_biUnion_subgroup (s := ZFamilyFinset M K) (Z := K ⊔ Kstar)
    (S := fun N => (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N)
    ZFamilyFinset_nonempty (fun _ _ => inf_le_left) ?_
  intro N₁ hN₁ N₂ hN₂ hne
  exact typeP_family_Kstar_disjoint hG hM hP hKM hK hKstar hU
    (mem_ZFamilyFinset.mp hN₁) (mem_ZFamilyFinset.mp hN₂) hne

/-- **BG 14.7, each family factor `Kᵢ* ◁ Z`** (mmd L3995 "`N_{M_i}(X*) = K_i × K_i*`"): every member
`N` of the type-`P` family has its canonical factor `Z ⊓ M_σ(N)` normalised by all of `Z = K ⊔ K*`.
For `N = M` this is `typeP_self_member`; for a neighbour it is the normality clause of
`exists_neighbor_full`.  Feeds the `Z`-stability of `T` (`hstab` for the TI count). -/
theorem typeP_family_member_normal [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N : Subgroup G} (hN : IsZFamilyMember M K N) :
    K ⊔ Kstar ≤ Subgroup.normalizer
      (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) := by
  rcases hN with hNM | ⟨p, X, hp, hX, hXK, hN⟩
  · rw [hNM]; exact (typeP_self_member hG hM hP hKM hK hKstar hU).2.2.1
  · have : Fact p.Prime := ⟨hp⟩
    have hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ := by
      intro hbot
      refine (typeP_structure hG hM hP hKM hK hKstar hU).2.1 (le_bot_iff.mp ?_)
      rw [hKstar]
      calc OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
          ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) :=
            inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXK))
        _ = ⊥ := hbot
    obtain ⟨_, _, _, _, hnorm, _, _⟩ :=
      exists_neighbor_full hG hM hP hKM hK hKstar hU hX hXK hCX hN
    exact hnorm

/-- **BG 14.7, `Z` normalises `T`** (mmd L4029, "`N_G(T) = Z`" half — the easy `Z ≤ N_G(T)` part):
conjugation by any `l ∈ Z = K ⊔ K*` fixes the set `T = Z − ⋃_{N} (Z ⊓ M_σ(N))`, because `l`
normalises `Z` (self-normalisation) and each canonical factor `Z ⊓ M_σ(N)`
(`typeP_family_member_normal`).  This is the `hstab` hypothesis of
`ncard_conjClassSet_of_isTISubset` once `T` is shown to be a TI-subset. -/
theorem typeP_family_Z_normalizes_T [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    ∀ l ∈ K ⊔ Kstar, MulAut.conj l •
        (((K ⊔ Kstar : Subgroup G) : Set G) \
          ⋃ N ∈ ZFamilyFinset M K,
            (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G))
      = ((K ⊔ Kstar : Subgroup G) : Set G) \
          ⋃ N ∈ ZFamilyFinset M K,
            (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) := by
  intro l hl
  rw [Set.smul_set_sdiff, Set.smul_set_iUnion₂]
  congr 1
  · rw [← Subgroup.coe_pointwise_smul,
      conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hl)]
  · refine Set.iUnion₂_congr (fun N hN => ?_)
    rw [← Subgroup.coe_pointwise_smul,
      conj_smul_eq_self_of_mem_normalizer
        (typeP_family_member_normal hG hM hP hKM hK hKstar hU (mem_ZFamilyFinset.mp hN) hl)]

/-- **BG Proposition 14.2(d), second assertion** (mmd L3827): for a type-`P` maximal `M` with Hall
`κ(M)`-subgroup `K` and `K* = C_{M_σ}(K)`, every `g ∈ M − (K ⊔ K*)` satisfies `K ∩ K^g = 1`.

BG: "the second assertion follows easily from (b1) since `K` is a Z-group."  Lean proof: a
nontrivial element of `K ∩ K^g` gives a rank-one `X = ⟨x⟩ ≤ K` of prime order `p` and its conjugate
`Y = ⟨g⁻¹ x g⟩ ≤ K`.  By Proposition 14.2(b1) (`typeP_structure`), `N_G(X) ⊓ M = N_G(Y) ⊓ M = Z`, so
`K` normalises both.  Since `g ∈ M` but `g ∉ Z`, `g ∉ N_G(X)`, hence `MulAut.conj g⁻¹ • X ≠ X`,
i.e. `X ≠ Y`.  Two distinct normal rank-one subgroups of `K` generate an elementary abelian `p²`
inside `M`, forcing `pRank_M(p) ≥ 2` — contradicting `pRank_M(p) = 1` (`p ∈ π(K) ⊆ κ(M) ⊆ τ₁ ∪ τ₃`).
This is the `(d)`-clause the TI-argument of Theorem 14.7 invokes (`g ∈ K_i × K_i*`). -/
theorem typeP_kappaHall_inf_conj_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {g : G} (hgM : g ∈ M) (hgZ : g ∉ K ⊔ Kstar) :
    K ⊓ (MulAut.conj g • K) = ⊥ := by
  classical
  by_contra hne
  -- A prime `p ∣ |K ∩ K^g|` and an order-`p` element `x ∈ K ∩ K^g`.
  have hcard_ne : Nat.card ↥(K ⊓ (MulAut.conj g • K)) ≠ 1 :=
    fun h => hne (Subgroup.eq_bot_of_card_eq _ h)
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hcard_ne
  have : Fact p.Prime := ⟨hp_prime⟩
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' p hp_dvd
  have hxmem : (x : G) ∈ K ⊓ (MulAut.conj g • K) := x.2
  have hxK : (x : G) ∈ K := (Subgroup.mem_inf.mp hxmem).1
  have hxKg : (x : G) ∈ MulAut.conj g • K := (Subgroup.mem_inf.mp hxmem).2
  have hxord' : orderOf (x : G) = p :=
    (orderOf_injective (K ⊓ (MulAut.conj g • K)).subtype
      (K ⊓ (MulAut.conj g • K)).subtype_injective x).trans hxord
  have hxne1 : (x : G) ≠ 1 := fun h => hp_prime.ne_one (by rw [← hxord', h, orderOf_one])
  -- `X = ⟨x⟩ ≤ K`, rank-one.
  set X := Subgroup.zpowers (x : G) with hXdef
  have hXcard : Nat.card ↥X = p := by rw [hXdef, Nat.card_zpowers, hxord']
  have hXea : X ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXleK : X ≤ K := Subgroup.zpowers_le.mpr hxK
  -- `Y = ⟨g⁻¹ x g⟩ ≤ K`, rank-one (`g⁻¹ x g ∈ K` since `x ∈ K^g`).
  have hgxgK : g⁻¹ * (x : G) * g ∈ K := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxKg
    simpa [MulAut.smul_def] using hxKg
  set y₀ := g⁻¹ * (x : G) * g with hy₀def
  have hy₀conj : y₀ = (MulAut.conj g⁻¹).toMonoidHom (x : G) := by
    rw [hy₀def, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
  have hy₀ord : orderOf y₀ = p := by
    rw [hy₀conj, orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective]
    exact hxord'
  set Y := Subgroup.zpowers y₀ with hYdef
  have hYcard : Nat.card ↥Y = p := by rw [hYdef, Nat.card_zpowers, hy₀ord]
  have hYea : Y ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hYcard, by rw [hYcard, pow_one]⟩
  have hYleK : Y ≤ K := Subgroup.zpowers_le.mpr hgxgK
  -- (b1): `N_G(X) ⊓ M = N_G(Y) ⊓ M = Z`, so `K` normalises both.
  have hb1 := (typeP_structure hG hM hP hKM hK hKstar hU).2.2.1
  have hNX : Subgroup.normalizer (X : Set G) ⊓ M = K ⊔ Kstar := hb1 p hp_prime X hXea hXleK
  have hNY : Subgroup.normalizer (Y : Set G) ⊓ M = K ⊔ Kstar := hb1 p hp_prime Y hYea hYleK
  have hKNX : K ≤ Subgroup.normalizer (X : Set G) :=
    le_trans (le_trans le_sup_left hNX.ge) inf_le_left
  have hKNY : K ≤ Subgroup.normalizer (Y : Set G) :=
    le_trans (le_trans le_sup_left hNY.ge) inf_le_left
  -- `X ≠ Y`: else `MulAut.conj g⁻¹ • X = Y = X`, so `g ∈ N_G(X) ⊓ M = Z`, against `g ∉ Z`.
  have hXneY : X ≠ Y := by
    intro hXeqY
    have hsmulXY : MulAut.conj g⁻¹ • X = Y := by
      rw [hXdef, hYdef, hy₀conj,
        show MulAut.conj g⁻¹ • Subgroup.zpowers (x : G)
          = (Subgroup.zpowers (x : G)).map (MulAut.conj g⁻¹).toMonoidHom from rfl,
        MonoidHom.map_zpowers]
    have hginvNX : g⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
      mem_normalizer_of_conj_smul_eq_self (hsmulXY.trans hXeqY.symm)
    have hgNX : g ∈ Subgroup.normalizer (X : Set G) := by
      simpa using (Subgroup.normalizer (X : Set G)).inv_mem hginvNX
    exact hgZ (hNX ▸ Subgroup.mem_inf.mpr ⟨hgNX, hgM⟩)
  -- `X ⊓ Y = ⊥` (distinct rank-one subgroups of prime order `p`).
  have hXYbot : X ⊓ Y = ⊥ := by
    by_contra hb
    have hdvd : Nat.card ↥(X ⊓ Y) ∣ p := hXcard ▸ Subgroup.card_dvd_of_le inf_le_left
    have hne1 : Nat.card ↥(X ⊓ Y) ≠ 1 := fun h => hb (Subgroup.eq_bot_of_card_eq _ h)
    have hpeq : Nat.card ↥(X ⊓ Y) = p := ((Nat.dvd_prime hp_prime).mp hdvd).resolve_left hne1
    have hXY_eq_X : X ⊓ Y = X :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (hXcard.le.trans hpeq.ge)
    exact hXneY (Subgroup.eq_of_le_of_card_ge (hXY_eq_X ▸ inf_le_right)
      (hYcard.le.trans hXcard.ge))
  -- `X`, `Y` commute (both normal in `K`, trivial meet), so `X ⊔ Y` is elementary abelian `p²`.
  have hcomm : ∀ a ∈ X, ∀ b ∈ Y, Commute a b :=
    commute_of_le_normalizer_of_disjoint hXleK hYleK hKNX hKNY hXYbot
  have hXcentY : X ≤ Subgroup.centralizer (Y : Set G) := fun a ha =>
    (Subgroup.mem_centralizer_iff).mpr fun b hb => (hcomm a ha b hb).symm
  have hsupea : (X ⊔ Y).IsElementaryAbelian p :=
    Subgroup.IsElementaryAbelian.sup_of_le_centralizer hXea.1 hYea.1 hXcentY
  have hsupcard : Nat.card ↥(X ⊔ Y) = p ^ 2 := by
    rw [card_sup_of_commute_of_disjoint hcomm hXYbot, hXcard, hYcard]; ring
  -- `X ⊔ Y ≤ M`, witnessing `pRank_M(p) ≥ 2`.
  have hsupM : X ⊔ Y ≤ M := sup_le (hXleK.trans hKM) (hYleK.trans hKM)
  have hsubea : ((X ⊔ Y).subgroupOf M).IsElementaryAbelian p :=
    IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hsupM).symm hsupea
  have hsubcard : Nat.card ↥((X ⊔ Y).subgroupOf M) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsupM).toEquiv, hsupcard]
  have hle := le_pRank ((X ⊔ Y).subgroupOf M) hsubea
  rw [hsubcard, Nat.log_pow hp_prime.one_lt] at hle
  -- but `pRank_M(p) = 1` since `p ∈ π(K) ⊆ κ(M) ⊆ τ₁ ∪ τ₃`.
  have hp_kappa : p ∈ kappa M := by
    apply hK.1 p
    rw [Nat.mem_primeFactors]
    refine ⟨hp_prime, ?_, Nat.card_pos.ne'⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
    exact hp_dvd.trans (Subgroup.card_dvd_of_le inf_le_left)
  have hpRank1 : pRank ↥M p = 1 := by
    rcases kappa_subset_tau1_union_tau3 hp_kappa with h | h
    · exact tau1_pRank_eq_one h
    · exact tau3_pRank_eq_one h
  omega

end OddOrder.BG.Ch4.S14


