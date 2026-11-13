-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_LocalStructure
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_LocalStructure
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T09:12:58.729341+00:00
-- url     : https://prove2.me/theorems/4e94cb45-183f-49ff-ba2f-a287172440ed
-- title:
--   BG §14: type-$\mathcal{P}$ counting, local structure (continuation)
-- statement:
--   A continuation of the local-structure part of the §14 type-$\mathcal{P}$ counting development of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*. Lemmas include embeddings of elementary abelian subgroups into the neighbor's $M_\sigma$, existence of Hall subgroups containing $\kappa$-parts, and existence of a type-$\mathcal{P}$ $E$-setup with a $\kappa$-Hall subgroup.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 15 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/LocalStructure.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/LocalStructure.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_ElemAbelianNeighbor

namespace OddOrder.BG.Ch4.S14

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch3.S13

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BG Proposition 14.2(b2)** (mmd L3829): for a type-`P` `M`, a Hall `κ(M)`-subgroup `K`, and
`X ∈ ℰ_p¹(K)` with `C_{M_σ}(X) ≠ 1`, every `M* ∈ ℳ(N_G(X))` satisfies `X ⊆ M*_σ`.

This is the clause of Prop 14.2(b) that `typeP_structure` omits — it carries only (b1)
(`N_M(X) = K × K*`).  The hypothesis `C_{M_σ}(X) ≠ 1` is automatic for `X ∈ ℰ¹(K)` (then
`C_{M_σ}(X) ⊇ C_{M_σ}(K) = K* ≠ 1`), so callers supply it from `typeP_structure`'s `K* ≠ 1`.
Theorem 14.7's neighbour analysis (`Z = K×K* ⊆ M_i`, `X_i ⊆ M_{iσ}`) needs this clause.

Proof (BG): `p ∈ κ(M) ⊆ τ₁(M) ∪ τ₃(M)`; Lemma 13.13 (`mem_sigma_of_tau1_tau3_centralize`) gives
`p ∈ σ(M*)`; since `X ≤ N_G(X) ≤ M*` is a `σ(M*)`-subgroup, `X ⊆ M*_σ`. -/
theorem typeP_elemAbelian_le_neighbor_Msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXK : X ≤ K)
    (hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥)
    {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))) :
    X ≤ OddOrder.BG.Ch3.S10.Msigma Mstar := by
  classical
  -- `p ∈ κ(M) ⊆ τ₁(M) ∪ τ₃(M)`.
  have hpdvd : p ∣ Nat.card ↥X := by
    rw [(mem_elemAbelianOfRank.mp hX).2]; exact dvd_pow_self p one_ne_zero
  have hpcardK : p ∈ (Nat.card ↥K).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Fact.out, hpdvd.trans (Subgroup.card_dvd_of_le hXK), Nat.card_pos.ne'⟩
  have hpκ : p ∈ kappa M := hK.1 p (by
    rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hpcardK)
  have hpτ13 : p ∈ tau1 M ∪ tau3 M := kappa_subset_tau1_union_tau3 hpκ
  -- `K` is a `σ(M)'`-subgroup; get an `E`-setup with `K ≤ E`, so `X ≤ E`.
  have hK_pi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma M)ᶜ) K := fun q hq =>
    kappa_subset_sigmaCompl (hK.1 q (by
      rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hq))
  obtain ⟨E, E₁, E₂, E₃, hsetup, hKE, _⟩ :=
    OddOrder.BG.Ch3.S12.exists_subgroupESetup_with_le hG hM hKM hK_pi
  -- Lemma 13.13: `p ∈ σ(M*)`.
  have hpσMstar : p ∈ OddOrder.BG.Ch3.S10.sigma Mstar :=
    OddOrder.BG.Ch3.S13.mem_sigma_of_tau1_tau3_centralize hG hsetup hpτ13 hX (hXK.trans hKE)
      hCX hMstar
  -- `X ≤ M*` is a `σ(M*)`-subgroup, hence `X ≤ M*_σ`.
  have hMstarMax : Mstar ∈ maximalSubgroups G :=
    mem_maximalSubgroups.mpr (mem_maximalSubgroupsContaining.mp hMstar).1
  have hXMstar : X ≤ Mstar :=
    Subgroup.le_normalizer.trans (mem_maximalSubgroupsContaining.mp hMstar).2
  refine OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
    (OddOrder.BG.Ch3.S10.Msigma_isHall hG hMstarMax) hXMstar (fun q hq => ?_)
  rw [(mem_elemAbelianOfRank.mp hX).2, pow_one, Nat.Prime.primeFactors (Fact.out : p.Prime),
    Finset.mem_singleton] at hq
  rwa [hq]

/-- **Theorem 14.7 neighbour-embedding** (BG L3977-3982), step 1 of the §16-independent
pre-position: for a type-`P` `M` with Hall `κ(M)`-subgroup `K`, `K* = C_{M_σ}(K)`, and
`X ∈ ℰ_p¹(K)` with `C_{M_σ}(X) ≠ 1`, every neighbour `M_i ∈ ℳ(N_G(X))` is **not conjugate to `M`**,
contains `Z = K ⊔ K*`, and has `X ⊆ M_{iσ}`.

Uses Prop 14.2(b1) [`N_M(X) = K×K*`, so `K ⊔ K* = N_G(X) ⊓ M ≤ N_G(X) ≤ M_i`], Prop 14.2(b2)
[`X ⊆ M_{iσ}`], and `σ`-conjugation-invariance: `p ∈ π(X) ⊆ κ(M) ⊆ σ(M)'`, but `X ⊆ M_{iσ}` gives
`p ∈ σ(M_i)`, so `M_i = M^g` would force `p ∈ σ(M^g) = σ(M)`, a contradiction. -/
theorem typeP_neighbor_embed [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXK : X ≤ K)
    (hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥)
    {Mi : Subgroup G} (hMi : Mi ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))) :
    ¬ IsConjugateSubgroup M Mi ∧ K ⊔ Kstar ≤ Mi ∧ X ≤ OddOrder.BG.Ch3.S10.Msigma Mi := by
  classical
  -- `p ∈ κ(M)`.
  have hpdvd : p ∣ Nat.card ↥X := by
    rw [(mem_elemAbelianOfRank.mp hX).2]; exact dvd_pow_self p one_ne_zero
  have hpcardK : p ∈ (Nat.card ↥K).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Fact.out, hpdvd.trans (Subgroup.card_dvd_of_le hXK), Nat.card_pos.ne'⟩
  have hpκ : p ∈ kappa M := hK.1 p (by
    rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hpcardK)
  -- `X ⊆ M_{iσ}` (Prop 14.2(b2)).
  have hXMiσ : X ≤ OddOrder.BG.Ch3.S10.Msigma Mi :=
    typeP_elemAbelian_le_neighbor_Msigma hG hM hKM hK hX hXK hCX hMi
  -- `K ⊔ K* ≤ M_i` (Prop 14.2(b1): `N_G(X) ⊓ M = K ⊔ K*`, and `N_G(X) ≤ M_i`).
  obtain ⟨_, _, hb1, _, _, _⟩ := typeP_structure hG hM hP hKM hK hKstar hU
  have hZMi : K ⊔ Kstar ≤ Mi := by
    rw [← hb1 p Fact.out X hX hXK]
    exact le_trans inf_le_left (mem_maximalSubgroupsContaining.mp hMi).2
  refine ⟨?_, hZMi, hXMiσ⟩
  -- `M_i` not conjugate to `M`: else `σ(M_i) = σ(M)`, but `p ∈ σ(M_i) ∩ κ(M) ⊆ σ(M) ∩ σ(M)'`.
  rintro ⟨g, hg⟩
  have hpσMi : p ∈ OddOrder.BG.Ch3.S10.sigma Mi :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup Mi p (Nat.mem_primeFactors.mpr
      ⟨Fact.out, hpdvd.trans (Subgroup.card_dvd_of_le hXMiσ), Nat.card_pos.ne'⟩)
  rw [← hg] at hpσMi
  have hpσM : p ∈ OddOrder.BG.Ch3.S10.sigma M := by
    have h2 := OddOrder.BG.Ch3.S10.sigma_conj g⁻¹ hpσMi
    rwa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h2
  exact kappa_subset_sigmaCompl hpκ hpσM

/-- **A `κ(M)`-subgroup of `M` lies in some Hall `κ(M)`-subgroup of `M`** (Hall D / Wielandt,
`Ch03.hall_D`, applied inside the solvable group `↥M`).  Used by Corollary 14.3 branch 1 to put
the `κ`-witness `X₀ ≤ ⟨x'⟩` into a Hall `κ`-subgroup `K`, so that Proposition 14.2(b1)/(c) apply. -/
theorem exists_isHallSubgroup_kappa_ge [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {X : Subgroup G} (hXM : X ≤ M)
    (hXκ : ∀ q ∈ (Nat.card ↥X).primeFactors, q ∈ kappa M) :
    ∃ K : Subgroup G, K ≤ M ∧ Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M) ∧ X ≤ K := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hXsub : ∀ q ∈ (Nat.card ↥(X.subgroupOf M)).primeFactors, q ∈ kappa M := by
    intro q hq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv] at hq
    exact hXκ q hq
  obtain ⟨K', hK'hall, hK'ge⟩ := Ch03.hall_D (G := ↥M) hXsub
  have hKeq : (K'.map M.subtype).subgroupOf M = K' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
  refine ⟨K'.map M.subtype, Subgroup.map_subtype_le K', ?_, ?_⟩
  · rw [hKeq]; exact hK'hall
  · exact le_of_eq_of_le (Subgroup.map_subgroupOf_eq_of_le hXM).symm (Subgroup.map_mono hK'ge)

/-- **`C_M(M_σ)` is a `κ(M)'`-group** (BG Corollary 15.3 step, mmd L4209 "By Proposition
14.2(b1) and (e), `C_M(H)` is a `κ(M)'`-group", for `H = M_σ`).  No prime of `κ(M)` divides
`|C_M(M_σ)|`.

Proof.  If some `p ∈ κ(M)` divided `|C_M(M_σ)|`, take `x ∈ C_M(M_σ)` of order `p`; then
`X₀ = ⟨x⟩` is a `κ`-subgroup, so it lies in a Hall `κ(M)`-subgroup `K`.  Since `x` centralizes
`M_σ`, `M_σ ≤ C_G(X₀) ≤ N_G(X₀)`, and Proposition 14.2(b1) (`typeP_structure` conjunct 3) gives
`N_G(X₀) ⊓ M = K ⊔ K*`.  By the Dedekind identity (`K* ≤ M_σ`, `M_σ ⊓ K = ⊥`, `K ≤ N(K*)`),
`M_σ ⊓ (K ⊔ K*) = K*`, whence `M_σ = K*`, contradicting `K* ≠ M_σ` (`typeP_structure`
conjunct 7, BG Prop 14.2(e), `kstar_ne_msigma_aux`). -/
theorem centralizer_msigma_isPiSubgroup_kappa_compl [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    Subgroup.IsPiSubgroup (kappa M)ᶜ
      (Subgroup.centralizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) ⊓ M) := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  intro p hp
  rw [Set.mem_compl_iff]
  intro hpκ
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have : Fact p.Prime := ⟨hpp⟩
  have hP : IsTypeP M := ⟨p, hpκ⟩
  -- Cauchy: an order-`p` element `x` of `C = C_M(M_σ)`; `X₀ = ⟨x⟩`.
  have hpdvd : p ∣ Nat.card ↥(Subgroup.centralizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) ⊓ M) :=
    (Nat.mem_primeFactors.mp hp).2.1
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  have hX₀card : Nat.card ↥(Subgroup.zpowers (x : G)) = p := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective _ (Subgroup.centralizer _ ⊓ M).subtype_injective x).trans hxord
  have hX₀C : Subgroup.zpowers (x : G) ≤
      Subgroup.centralizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) ⊓ M :=
    Subgroup.zpowers_le.mpr x.2
  have hX₀M : Subgroup.zpowers (x : G) ≤ M := hX₀C.trans inf_le_right
  have hX₀elem : Subgroup.zpowers (x : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hX₀card, by rw [hX₀card, pow_one]⟩
  -- `X₀` is a `κ`-subgroup, so it lies in a Hall `κ(M)`-subgroup `K`.
  have hX₀κ : ∀ q ∈ (Nat.card ↥(Subgroup.zpowers (x : G))).primeFactors, q ∈ kappa M := by
    intro q hq
    rw [hX₀card, Nat.Prime.primeFactors hpp, Finset.mem_singleton] at hq
    rwa [hq]
  obtain ⟨K, hKM, hKHall, hX₀K⟩ := exists_isHallSubgroup_kappa_ge hG hM hX₀M hX₀κ
  -- A Hall `(κ ∪ σ)'`-subgroup `U` of `M`.
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M) ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  have hUof : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hUHall : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUof]; exact hU'
  -- `typeP_structure`: (b1) and (e) `K* ≠ M_σ`, with `K* = M_σ ⊓ C(K)`.
  obtain ⟨_, _, hb1, _, _, _, hKstar_ne⟩ := typeP_structure hG hM hP hKM hKHall
    (rfl : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) = _) hUHall
  set Kstar : Subgroup G :=
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) with hKstardef
  -- `M_σ ≤ N_G(X₀) ⊓ M = K ⊔ K*`  (`X₀ ≤ C(M_σ)` ⟹ `M_σ ≤ C(X₀) ≤ N_G(X₀)`).
  have hMσ_le : OddOrder.BG.Ch3.S10.Msigma M ≤ K ⊔ Kstar := by
    rw [← hb1 p hpp _ hX₀elem hX₀K]
    refine le_inf ?_ (OddOrder.BG.Ch3.S10.Msigma_le M)
    have hcent : OddOrder.BG.Ch3.S10.Msigma M ≤
        Subgroup.centralizer ((Subgroup.zpowers (x : G)) : Set G) :=
      Subgroup.le_centralizer_iff.mp (hX₀C.trans inf_le_left)
    exact hcent.trans (Subgroup.centralizer_le_normalizer _)
  -- Dedekind: `M_σ ⊓ (K ⊔ K*) = K*`.
  have hKstar_le_Mσ : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M := inf_le_left
  have hKnormKstar : K ≤ Subgroup.normalizer (Kstar : Set G) :=
    (Subgroup.le_centralizer_iff.mp (inf_le_right : Kstar ≤ Subgroup.centralizer (K : Set G))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hMσK_bot : OddOrder.BG.Ch3.S10.Msigma M ⊓ K = ⊥ := by
    apply Disjoint.eq_bot
    refine Subgroup.disjoint_of_coprime_natCard (Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := OddOrder.BG.Ch3.S10.sigma M) Nat.card_pos.ne' Nat.card_pos.ne'
      (fun r hr => OddOrder.BG.Ch3.S10.Msigma_isPiGroup M r hr) (fun r hr => ?_))
    exact kappa_subset_sigmaCompl (hKHall.1 r (by
      rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hr))
  have hdedekind : OddOrder.BG.Ch3.S10.Msigma M ⊓ (K ⊔ Kstar) = Kstar := by
    apply SetLike.coe_injective
    rw [Subgroup.coe_inf, Subgroup.coe_mul_of_left_le_normalizer_right K Kstar hKnormKstar,
      ← Subgroup.inf_mul_assoc _ _ _ hKstar_le_Mσ, hMσK_bot, Subgroup.coe_bot]
    simp
  -- `M_σ = K*` (since `M_σ ≤ K ⊔ K*`), contradicting `K* ≠ M_σ`.
  exact hKstar_ne (((inf_of_le_left hMσ_le).symm).trans hdedekind).symm

/-- **§12 `E`-setup adapted to a `κ(M)`-Hall subgroup `K`** (the preamble of BG Prop 14.2's proof,
mmd L3832-3840).  For a type-`P` `M` and a Hall `κ(M)`-subgroup `K`, there is an `E`-setup whose
`τ₁`-Hall `E₁` lies in `K ≤ E` with `E₁ ≠ 1`.  In the `κ ∩ τ₃ ≠ ∅` case `K = E ⊇ E₁`; in the
`κ ⊆ τ₁` case the setup is conjugated so its `E₁` becomes `K`.  Packages exactly the hypotheses
that `typeP_sylow_not_le_kstar` (Prop 14.2(e)) consumes. -/
theorem exists_typePESetup_kappaHall [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M)) :
    ∃ E E₁ E₂ E₃ : Subgroup G, SubgroupESetup M E E₁ E₂ E₃ ∧ E₁ ≤ K ∧ K ≤ E ∧ E₁ ≠ ⊥ := by
  classical
  have hK_pi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma M)ᶜ) K := by
    intro p hp
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hp
    exact kappa_subset_sigmaCompl (hK.1 p hp)
  obtain ⟨E, E₁, E₂, E₃, hsetup, hKE, _⟩ :=
    OddOrder.BG.Ch3.S12.exists_subgroupESetup_with_le hG hM hKM hK_pi
  by_cases hτ3 : (kappa M ∩ tau3 M).Nonempty
  · -- Case `κ ∩ τ₃ ≠ ∅`: `E = E₁ E₃` is `κ`-pure, so `K = E`; then `E₁ ≤ E = K`.
    obtain ⟨p, hpmem⟩ := hτ3
    rw [Set.mem_inter_iff] at hpmem
    obtain ⟨hpκ, hpτ3⟩ := hpmem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors ((mem_tau3_iff M p).mp hpτ3).2.1
    obtain ⟨hE3ne, hreg⟩ := E3_not_regular_of_mem_kappa_tau3 hG hsetup hp hpκ hpτ3
    obtain ⟨hE1ne, _, hEprime, _⟩ := E3_not_regular_consequences hG hsetup hE3ne hreg
    obtain ⟨x, hxE3, hxne, hxC⟩ : ∃ x ∈ E₃, x ≠ 1 ∧
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
      by_contra hcon
      push Not at hcon
      exact hreg fun y hy hy1 => hcon y hy hy1
    have hEpi : Ch03.Subgroup.IsPiGroup (kappa M) (E.subgroupOf M) := by
      intro q hq
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E_le).toEquiv] at hq
      exact mem_kappa_of_mem_primeFactors_card_E hG hsetup hEprime hxE3 hxne hxC hq
    have hEdvdK : Nat.card ↥E ∣ Nat.card ↥K := by
      have hd := hK.card_dvd_of_isPiGroup hEpi
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E_le).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hd
    have hKEeq : K = E :=
      Subgroup.eq_of_le_of_card_ge hKE (Nat.dvd_antisymm hEdvdK (Subgroup.card_dvd_of_le hKE)).le
    exact ⟨E, E₁, E₂, E₃, hsetup, hsetup.E₁_le.trans hKEeq.ge, hKEeq.le, hE1ne⟩
  · -- Case `κ ⊆ τ₁`: `K` is `M`-conjugate to `E₁`; conjugate the setup so its new `E₁ = K`.
    have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hsetup.mem_maximal
    have hκτ1 : ∀ p ∈ kappa M, p ∈ tau1 M := fun p hpκ =>
      (kappa_subset_tau1_union_tau3 hpκ).resolve_right
        (fun hpτ3 => hτ3 ⟨p, Set.mem_inter hpκ hpτ3⟩)
    obtain ⟨p₀, hp₀κ⟩ := hP
    obtain ⟨hE1ne, hE1nonreg⟩ := E1_not_regular_of_mem_kappa_tau1 hG hsetup
      (prime_of_mem_kappa hp₀κ) hp₀κ (hκτ1 p₀ hp₀κ)
    have hE1prime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) E₁ := E1_actsPrime hG hsetup hE1ne
    have hCE1 : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥ :=
      Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hE1prime (le_refl E₁) hE1nonreg
    have hE1HallκE : Ch03.IsHallSubgroup (kappa M) (E₁.subgroupOf E) :=
      ⟨fun p hp => mem_kappa_of_mem_primeFactors_card_E1 hG hsetup hE1prime hCE1
          (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E₁_le).toEquiv] at hp),
        fun p hp hpκ => hsetup.E₁_hall.2 p hp (hκτ1 p hpκ)⟩
    have hE1Hallκ : Ch03.IsHallSubgroup (kappa M) (E₁.subgroupOf M) :=
      hallPiece_isHall_in_M hG hsetup hsetup.E₁_le hE1HallκE kappa_subset_sigmaCompl
    obtain ⟨w, hwM, hw⟩ := OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf hMsolv
      (hsetup.E₁_le.trans hsetup.E_le) hKM hE1Hallκ hK
    have h' := SubgroupESetup.conj' hsetup hwM
    rw [hw] at h'
    obtain ⟨hKne, _⟩ := E1_not_regular_of_mem_kappa_tau1 hG h'
      (prime_of_mem_kappa hp₀κ) hp₀κ (hκτ1 p₀ hp₀κ)
    exact ⟨MulAut.conj w • E, K, MulAut.conj w • E₂, MulAut.conj w • E₃, h', le_refl K,
      h'.E₁_le, hKne⟩

/-- **BG Proposition 14.2(e), packaged for `typeP_structure` inputs** (mmd L3828).  The `S ⊄ K*`
clause of Prop 14.2(e) stated with the natural type-`P` hypotheses (`M` maximal type-`P`, `K` a
Hall `κ(M)`-subgroup) instead of a raw `E`-setup: it builds the setup via
`exists_typePESetup_kappaHall` and applies `typeP_sylow_not_le_kstar`. -/
theorem typeP_sylow_not_le_kstar_of_isHall [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hKstar_ne : Kstar ≠ ⊥)
    {q : ℕ} [Fact q.Prime] {S : Subgroup G} (hSne : S ≠ ⊥)
    (hSle : S ≤ OddOrder.BG.Ch3.S10.Msigma M) (hSq : IsPGroup q ↥S)
    (hSmax : ∀ T : Subgroup G, T ≤ OddOrder.BG.Ch3.S10.Msigma M → IsPGroup q ↥T → S ≤ T → S = T) :
    ¬ S ≤ Kstar := by
  obtain ⟨E, E₁, E₂, E₃, h, hE1K, hKE, hE1ne⟩ := exists_typePESetup_kappaHall hG hM hP hKM hK
  have hKne : K ≠ ⊥ := fun hKbot => hE1ne (le_bot_iff.mp (hE1K.trans hKbot.le))
  have hKpi13 : ∀ p ∈ (Nat.card ↥K).primeFactors, p ∈ tau1 M ∪ tau3 M := fun p hp =>
    kappa_subset_tau1_union_tau3 (hK.1 p (by
      rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hp))
  exact typeP_sylow_not_le_kstar hG h hE1K hKE hE1ne hKne hKpi13 hKstar hKstar_ne
    hSne hSle hSq hSmax

/-- **`C_M(H)` is a `κ(M)'`-group for every nontrivial Hall subgroup `H` of `M_σ`** (BG Corollary
15.3(a) start, mmd L4209 "By Proposition 14.2(b1) and (e), `C_M(H)` is a `κ(M)'`-group").  The
general-Hall analogue of `centralizer_msigma_isPiSubgroup_kappa_compl` (`H = M_σ`).

Proof.  If `p ∈ κ(M)` divided `|C_M(H)|`, take `x ∈ C_M(H)` of order `p`; then `X₀ = ⟨x⟩` is a
`κ`-subgroup lying in a Hall `κ(M)`-subgroup `K`.  Since `x` centralizes `H`, `H ≤ C_G(X₀) ≤
N_G(X₀)`, and Prop 14.2(b1) gives `N_G(X₀) ⊓ M = K ⊔ K*`; with `H ≤ M_σ`, the Dedekind identity
`M_σ ⊓ (K ⊔ K*) = K*` forces `H ≤ K*`.  As `H` is Hall in `M_σ`, a Sylow `q`-subgroup `S` of `M_σ`
(for `q ∈ π(H)`) lies in `H ≤ K*`, contradicting Prop 14.2(e)
(`typeP_sylow_not_le_kstar_of_isHall`, `S ⊄ K*`). -/
theorem centralizer_hall_isPiSubgroup_kappa_compl [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hHMσ : H ≤ OddOrder.BG.Ch3.S10.Msigma M)
    (hHhall : Ch03.IsHallSubgroup (piSet H) (H.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)))
    (hHne : H ≠ ⊥) :
    Subgroup.IsPiSubgroup (kappa M)ᶜ (Subgroup.centralizer (H : Set G) ⊓ M) := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  intro p hp
  rw [Set.mem_compl_iff]
  intro hpκ
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have : Fact p.Prime := ⟨hpp⟩
  have hP : IsTypeP M := ⟨p, hpκ⟩
  -- Cauchy: `x ∈ C = C_G(H) ⊓ M` of order `p`; `X₀ = ⟨x⟩`.
  have hpdvd : p ∣ Nat.card ↥(Subgroup.centralizer (H : Set G) ⊓ M) :=
    (Nat.mem_primeFactors.mp hp).2.1
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  have hX₀card : Nat.card ↥(Subgroup.zpowers (x : G)) = p := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective _ (Subgroup.centralizer _ ⊓ M).subtype_injective x).trans hxord
  have hX₀C : Subgroup.zpowers (x : G) ≤ Subgroup.centralizer (H : Set G) ⊓ M :=
    Subgroup.zpowers_le.mpr x.2
  have hX₀M : Subgroup.zpowers (x : G) ≤ M := hX₀C.trans inf_le_right
  have hX₀elem : Subgroup.zpowers (x : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hX₀card, by rw [hX₀card, pow_one]⟩
  have hX₀κ : ∀ q ∈ (Nat.card ↥(Subgroup.zpowers (x : G))).primeFactors, q ∈ kappa M := by
    intro q hq
    rw [hX₀card, Nat.Prime.primeFactors hpp, Finset.mem_singleton] at hq
    rwa [hq]
  obtain ⟨K, hKM, hKHall, hX₀K⟩ := exists_isHallSubgroup_kappa_ge hG hM hX₀M hX₀κ
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M) ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  have hUof : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hUHall : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUof]; exact hU'
  -- `typeP_structure`: `K* ≠ 1` and (b1) `N_M(X₀) = K ⊔ K*`.
  obtain ⟨_, hKstar_ne, hb1, _, _, _, _⟩ := typeP_structure hG hM hP hKM hKHall
    (rfl : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) = _) hUHall
  set Kstar : Subgroup G :=
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) with hKstardef
  -- `H ≤ C_G(X₀) ≤ N_G(X₀)` (`x` centralizes `H`), and `H ≤ M`, so `H ≤ N_M(X₀) = K ⊔ K*`.
  have hH_le_N : H ≤ Subgroup.normalizer ((Subgroup.zpowers (x : G)) : Set G) :=
    (Subgroup.le_centralizer_iff.mp (hX₀C.trans inf_le_left)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hH_le_KKstar : H ≤ K ⊔ Kstar := by
    rw [← hb1 p hpp _ hX₀elem hX₀K]
    exact le_inf hH_le_N (hHMσ.trans (OddOrder.BG.Ch3.S10.Msigma_le M))
  -- Dedekind: `M_σ ⊓ (K ⊔ K*) = K*`; with `H ≤ M_σ`, `H ≤ K*`.
  have hKstar_le_Mσ : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M := inf_le_left
  have hKnormKstar : K ≤ Subgroup.normalizer (Kstar : Set G) :=
    (Subgroup.le_centralizer_iff.mp
      (inf_le_right : Kstar ≤ Subgroup.centralizer (K : Set G))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hMσK_bot : OddOrder.BG.Ch3.S10.Msigma M ⊓ K = ⊥ := by
    apply Disjoint.eq_bot
    refine Subgroup.disjoint_of_coprime_natCard (Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := OddOrder.BG.Ch3.S10.sigma M) Nat.card_pos.ne' Nat.card_pos.ne'
      (fun r hr => OddOrder.BG.Ch3.S10.Msigma_isPiGroup M r hr) (fun r hr => ?_))
    exact kappa_subset_sigmaCompl (hKHall.1 r (by
      rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hr))
  have hdedekind : OddOrder.BG.Ch3.S10.Msigma M ⊓ (K ⊔ Kstar) = Kstar := by
    apply SetLike.coe_injective
    rw [Subgroup.coe_inf, Subgroup.coe_mul_of_left_le_normalizer_right K Kstar hKnormKstar,
      ← Subgroup.inf_mul_assoc _ _ _ hKstar_le_Mσ, hMσK_bot, Subgroup.coe_bot]
    simp
  have hH_le_Kstar : H ≤ Kstar := by
    have hHmem : H ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ (K ⊔ Kstar) := le_inf hHMσ hH_le_KKstar
    rwa [hdedekind] at hHmem
  -- A prime `q ∈ π(H)` and a Sylow `q`-subgroup `S` of `M_σ` with `S ≤ H ≤ K*`.
  obtain ⟨q, hq, hqdvd⟩ := (Nat.card ↥H).exists_prime_and_dvd
    (fun hc => hHne (Subgroup.card_eq_one.mp hc))
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨P⟩ : Nonempty (Sylow q ↥H) := Sylow.nonempty
  set S : Subgroup G := (P : Subgroup ↥H).map H.subtype with hSdef
  have hS_le_H : S ≤ H := hSdef ▸ Subgroup.map_subtype_le _
  have hS_le_Mσ : S ≤ OddOrder.BG.Ch3.S10.Msigma M := hS_le_H.trans hHMσ
  have hScardH : Nat.card ↥S = q ^ (Nat.card ↥H).factorization q := by
    rw [hSdef, Subgroup.card_map_of_injective H.subtype_injective, P.card_eq_multiplicity]
  have hSq : IsPGroup q ↥S := IsPGroup.iff_card.mpr ⟨_, hScardH⟩
  -- Hall: `q ∤ [M_σ : H]`, so `v_q(|H|) = v_q(|M_σ|)`.
  have hqpiH : q ∈ piSet H := Nat.mem_primeFactors.mpr ⟨hq, hqdvd, Nat.card_pos.ne'⟩
  have hHcard : Nat.card ↥(H.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHMσ).toEquiv
  have hq_ndvd_index : ¬ q ∣ (H.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).index := fun hdvd =>
    hHhall.index_no_pi q
      (Nat.mem_primeFactors.mpr ⟨hq, hdvd, Subgroup.index_ne_zero_of_finite⟩) hqpiH
  have hfact_eq : (Nat.card ↥H).factorization q
      = (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)).factorization q := by
    have hsplit : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)
        = Nat.card ↥H * (H.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).index := by
      rw [← hHcard]; exact (Subgroup.card_mul_index _).symm
    rw [hsplit, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hq_ndvd_index, add_zero]
  have hScard : Nat.card ↥S = q ^ (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)).factorization q := by
    rw [hScardH, hfact_eq]
  have hSmax : ∀ T : Subgroup G, T ≤ OddOrder.BG.Ch3.S10.Msigma M → IsPGroup q ↥T → S ≤ T → S = T :=
    fun T hTM hTq hST => eq_of_le_of_isPGroup_card_eq_factorization hScard hTM hTq hST
  have hSne : S ≠ ⊥ := by
    intro hSbot
    have hqdvdS : q ∣ Nat.card ↥S := by
      rw [hScardH]
      exact dvd_pow_self q (hq.factorization_pos_of_dvd Nat.card_pos.ne' hqdvd).ne'
    rw [Subgroup.card_eq_one.mpr hSbot] at hqdvdS
    exact hq.one_lt.ne' (Nat.dvd_one.mp hqdvdS)
  exact typeP_sylow_not_le_kstar_of_isHall hG hM hP hKM hKHall hKstardef hKstar_ne
    hSne hS_le_Mσ hSq hSmax (hS_le_H.trans hH_le_Kstar)

/-- **BG Corollary 14.3, branch-2 piece** (mmd L3858): if `x'` is a nonidentity `τ₂(M)`-element
of `M` with `C_{M_σ}(x') ≠ 1`, then `ℳ(C_G(x')) = {M}`.  This is Corollary 12.10(e)
(`nilpotent_sigmaComplement_abelian`, fifth conjunct) for an `E`-setup of `M`, with the prime
set `π(⟨x'⟩)` rewritten as `(orderOf x').primeFactors`. -/
theorem maximalContaining_centralizer_eq_singleton_of_tau2_element [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {x' : G} (hx'M : x' ∈ M) (hx'1 : x' ≠ 1)
    (hx'τ2 : ∀ p ∈ piSet (Subgroup.closure {x'}), p ∈ tau2 M)
    (hC : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x'} : Set G) ≠ ⊥) :
    maximalSubgroupsContaining (Subgroup.centralizer ({x'} : Set G)) = {M} := by
  classical
  obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := exists_subgroupESetup hG hM
  have hcard : Nat.card ↥(Subgroup.closure {x'}) = orderOf x' := by
    rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
  exact (nilpotent_sigmaComplement_abelian hG hsetup).2.2.2.2 x' hx'M hx'1
    (fun r hr => hx'τ2 r (by
      change r ∈ (Nat.card ↥(Subgroup.closure {x'})).primeFactors
      rw [hcard]; exact hr)) hC

/-- **BG Lemma 15.1(c)** (mmd L4170): if `U` is a `(κ(M) ∪ σ(M))'`-Hall subgroup of `M` and
`X` is a nonidentity subgroup of `U` with `C_{M_σ}(X) ≠ 1`, then `ℳ(C_G(X)) = {M}` and `X` is a
cyclic `τ₂(M)`-subgroup.

Proof (following BG L4176): since `X ≤ U`, every prime `p ∈ π(X)` lies in `(κ(M) ∪ σ(M))'`,
so `p ∉ σ(M)`, `p ∉ κ(M)`, and `p ∈ π(M)`.

*`π(X) ⊆ τ₂(M)`:* if some `p ∈ π(X)` had `p ∉ τ₂(M)`, then `r_p(M) = 1`, and a rank-one
elementary abelian `A ≤ X` (Cauchy) realizes the maximal rank, so Lemma 14.1
(`msigma_structure_of_notMem_sigma_kappa`) gives `C_{M_σ}(A) = 1`; centralizer antitonicity
(`A ≤ X`) yields `C_{M_σ}(X) ≤ C_{M_σ}(A) = 1`, contradicting `hCX`.

*`X` cyclic:* `X` is a `τ₂(M)`-subgroup of the solvable `M`, hence (Hall D) conjugate into the
abelian Hall `τ₂(M)`-subgroup `E₂` (Corollary 12.10(b)), so `X` is abelian.  Each Sylow `p` of `X`
is cyclic, for if it contained `A ∈ ℰ_p²(X)` then Theorem 12.5(d) (`Msigma_nilpotent_of_tau2`)
would give `C_{M_σ}(A) = 1` and again `C_{M_σ}(X) = 1`.  An abelian group with cyclic Sylow
subgroups is cyclic (`isCyclic_of_sylow_isCyclic`).

*`ℳ(C_G(X)) = {M}`:* with `X = ⟨x⟩` cyclic and `C_G(X) = C_G(x)`, apply Corollary 14.3 branch 2
(`maximalContaining_centralizer_eq_singleton_of_tau2_element`). -/
theorem typeP_hall_small_subgroup_cyclic_tau2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hUM : U ≤ M)
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {X : Subgroup G} (hXU : X ≤ U) (hXne : X ≠ ⊥)
    (hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥) :
    maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} ∧
      IsCyclic ↥X ∧ (↑(Nat.card ↥X).primeFactors ⊆ tau2 M) := by
  classical
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hXM : X ≤ M := hXU.trans hUM
  obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := exists_subgroupESetup hG hM
  -- Each prime of `X` lies in `(κ(M) ∪ σ(M))'`, hence `∉ σ`, `∉ κ`, and `∈ π(M)`.
  have hXprimes : ∀ p ∈ (Nat.card ↥X).primeFactors,
      p ∉ OddOrder.BG.Ch3.S10.sigma M ∧ p ∉ kappa M ∧ p ∈ piSet M := by
    intro p hp
    obtain ⟨hpp, hpdvdX, _⟩ := Nat.mem_primeFactors.mp hp
    have hpdvdU : p ∣ Nat.card ↥U := hpdvdX.trans (Subgroup.card_dvd_of_le hXU)
    have hpdvdM : p ∣ Nat.card ↥M := hpdvdX.trans (Subgroup.card_dvd_of_le hXM)
    have hpUM : p ∈ (Nat.card ↥(U.subgroupOf M)).primeFactors := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv]
      exact Nat.mem_primeFactors.mpr ⟨hpp, hpdvdU, Nat.card_pos.ne'⟩
    have hpcompl : p ∈ (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ := hU.1 p hpUM
    rw [Set.mem_compl_iff, Set.mem_union, not_or] at hpcompl
    exact ⟨hpcompl.2, hpcompl.1, Nat.mem_primeFactors.mpr ⟨hpp, hpdvdM, Nat.card_pos.ne'⟩⟩
  -- **Part A**: `π(X) ⊆ τ₂(M)`.
  have hXτ2 : ∀ p ∈ (Nat.card ↥X).primeFactors, p ∈ tau2 M := by
    intro p hp
    obtain ⟨hpσ, hpκ, hpπ⟩ := hXprimes p hp
    obtain ⟨hpp, hpdvdX, _⟩ := Nat.mem_primeFactors.mp hp
    have : Fact p.Prime := ⟨hpp⟩
    by_contra hpτ2
    -- `p ∉ τ₂(M)` with `p ∉ σ(M)` gives `r_p(M) ≠ 2`; rank bounds force `r_p(M) = 1`.
    have hr2 : pRank ↥M p ≠ 2 := fun h => hpτ2 ((mem_tau2_iff M p).mpr ⟨hpσ, h⟩)
    have hpE : p ∈ (Nat.card ↥E).primeFactors :=
      mem_primeFactors_E_of_mem_M_of_not_sigma hG hsetup hpp hpπ hpσ
    have h1r : 1 ≤ pRank ↥M p := one_le_pRank_of_mem_primeFactors hpπ
    have hub : pRank ↥M p ≤ 2 := hsetup.pRank_M_le_two hG hpE
    have hr1 : pRank ↥M p = 1 := by omega
    -- A rank-one elementary abelian subgroup `A ≤ X` of maximal rank.
    obtain ⟨a, hacard⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) p hpdvdX
    set A : Subgroup G := Subgroup.zpowers (a : G) with hAdef
    have hAX : A ≤ X := by rw [hAdef, Subgroup.zpowers_le]; exact a.2
    have haGcard : orderOf (a : G) = p :=
      (orderOf_injective X.subtype X.subtype_injective a).trans hacard
    have hAcard : Nat.card ↥A = p := by rw [hAdef, Nat.card_zpowers]; exact haGcard
    have hAelem : A.IsElementaryAbelian p := Subgroup.IsElementaryAbelian.of_card_prime hAcard
    have hA : A ∈ elemAbelianOfRank G p (pRank ↥M p) := by
      rw [hr1, mem_elemAbelianOfRank]
      exact ⟨hAelem, by rw [hAcard, pow_one]⟩
    -- Lemma 14.1: `C_{M_σ}(A) = 1`; antitonicity gives `C_{M_σ}(X) = 1`, contradiction.
    obtain ⟨_, hCA, _⟩ :=
      msigma_structure_of_notMem_sigma_kappa hG hM hpπ hpσ hpκ hA (hAX.trans hXM)
    apply hCX
    rw [eq_bot_iff, ← hCA]
    exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAX))
  -- **Part B(i)**: `X` is abelian (conjugate into the abelian Hall `τ₂`-subgroup `E₂`).
  -- `X` is a `τ₂(M)`-subgroup, so `X.subgroupOf M` is a `τ₂(M)`-π-subgroup of `↥M`.
  have hXsub : ∀ q ∈ (Nat.card ↥(X.subgroupOf M)).primeFactors, q ∈ tau2 M := by
    intro q hq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv] at hq
    exact hXτ2 q hq
  obtain ⟨H', hH'hall, hH'ge⟩ := Ch03.hall_D (G := ↥M) hXsub
  set HG : Subgroup G := H'.map M.subtype with hHGdef
  have hHG_le_M : HG ≤ M := Subgroup.map_subtype_le _
  have hHG_hall : Ch03.IsHallSubgroup (tau2 M) (HG.subgroupOf M) := by
    rw [hHGdef, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    exact hH'hall
  have hX_le_HG : X ≤ HG := by
    rw [hHGdef]
    refine le_trans ?_ (Subgroup.map_mono hH'ge)
    rw [Subgroup.map_subgroupOf_eq_of_le hXM]
  -- `E₂` is also a Hall `τ₂(M)`-subgroup of `M`.
  have hE₂_hall_M : Ch03.IsHallSubgroup (tau2 M) (E₂.subgroupOf M) :=
    hallPiece_isHall_in_M hG hsetup hsetup.E₂_le hsetup.E₂_hall (tau2_subset_sigma_compl M)
  -- Conjugate `HG` onto `E₂` (Hall C inside `↥M`).
  obtain ⟨w, _, hw⟩ :=
    OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf hMsolv hHG_le_M hsetup.E2_le_M
      hHG_hall hE₂_hall_M
  have hbE₂ : IsMulCommutative ↥E₂ := (nilpotent_sigmaComplement_abelian hG hsetup).2.1.1
  -- `conj w • X ≤ E₂`; commuting in `E₂` transports back to `X`.
  have hXwE₂ : (MulAut.conj w • X : Subgroup G) ≤ E₂ := by
    rw [← hw]
    exact Subgroup.map_mono hX_le_HG
  have hXab : IsMulCommutative ↥X := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    -- `w·a·w⁻¹` and `w·b·w⁻¹` lie in `conj w • X ≤ E₂`, hence commute.
    have haw : w * (a : G) * w⁻¹ ∈ E₂ := by
      apply hXwE₂
      have h := (Subgroup.smul_mem_pointwise_smul_iff
        (a := MulAut.conj w) (S := X) (x := (a : G))).mpr a.2
      rwa [MulAut.smul_def, MulAut.conj_apply] at h
    have hbw : w * (b : G) * w⁻¹ ∈ E₂ := by
      apply hXwE₂
      have h := (Subgroup.smul_mem_pointwise_smul_iff
        (a := MulAut.conj w) (S := X) (x := (b : G))).mpr b.2
      rwa [MulAut.smul_def, MulAut.conj_apply] at h
    have hcomm : (w * (a : G) * w⁻¹) * (w * (b : G) * w⁻¹)
        = (w * (b : G) * w⁻¹) * (w * (a : G) * w⁻¹) :=
      congrArg Subtype.val (hbE₂.is_comm.comm ⟨_, haw⟩ ⟨_, hbw⟩)
    have hcancel := congrArg (fun u => w⁻¹ * u * w) hcomm
    simpa [mul_assoc] using hcancel
  have : IsMulCommutative ↥X := hXab
  -- **Part B(ii)**: every Sylow `p` of `X` is cyclic (else `ℰ_p²(X)` ↝ `C_{M_σ}(X) = 1`).
  have hSylcyc : ∀ p : ℕ, p.Prime → ∀ P : Sylow p ↥X, IsCyclic P := by
    intro p hp P
    have : Fact p.Prime := ⟨hp⟩
    by_contra hPnc
    -- `P` is noncyclic, hence nontrivial, so `p ∣ |X|` and (oddness of `G`) `p` is odd.
    have hpcardP : p ∣ Nat.card ↥(P : Subgroup ↥X) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · refine absurd ?_ hPnc
        have : Subsingleton ↥(P : Subgroup ↥X) :=
          (Nat.card_eq_one_iff_unique.mp (by rw [hn, h0, pow_zero])).1
        exact isCyclic_of_subsingleton
      · rw [hn]; exact dvd_pow_self p hpos.ne'
    have hpcardX : p ∣ Nat.card ↥X :=
      hpcardP.trans (Subgroup.card_subgroup_dvd_card _)
    have hodd : Odd p :=
      hG.odd.of_dvd_nat (hpcardX.trans (Subgroup.card_subgroup_dvd_card X))
    -- A noncyclic odd `p`-group contains a rank-two elementary abelian subgroup (BG Lemma 4.5(a)).
    obtain ⟨B, hBelem, hBcard⟩ :=
      OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic
        P.isPGroup' hodd hPnc
    -- Map `B ≤ P ≤ ↥X` up to `G`.
    set A : Subgroup G := (B.map (P : Subgroup ↥X).subtype).map X.subtype with hAdef
    have hAelem : A.IsElementaryAbelian p := by
      rw [hAdef]
      exact (hBelem.map (Subgroup.subtype_injective _)).map X.subtype_injective
    have hAcard : Nat.card ↥A = p ^ 2 := by
      rw [hAdef, Subgroup.card_map_of_injective X.subtype_injective,
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hBcard]
    have hAX : A ≤ X := by
      rw [hAdef]
      exact le_trans (Subgroup.map_mono (Subgroup.map_subtype_le _)) (Subgroup.map_subtype_le _)
    have hA2 : A ∈ elemAbelianOfRank G p 2 := mem_elemAbelianOfRank.mpr ⟨hAelem, hAcard⟩
    -- `p ∈ τ₂(M)`, then Theorem 12.5(d): `C_{M_σ}(A) = 1`, contradicting `hCX`.
    have hpX : p ∈ (Nat.card ↥X).primeFactors := by
      refine Nat.mem_primeFactors.mpr ⟨hp, ?_, Nat.card_pos.ne'⟩
      exact (dvd_pow_self p two_ne_zero).trans (hAcard ▸ Subgroup.card_dvd_of_le hAX)
    have hpτ2 : p ∈ tau2 M := hXτ2 p hpX
    have hCA := (Msigma_nilpotent_of_tau2 hG hM hpτ2 hA2 (hAX.trans hXM)).2.2.2.1
    apply hCX
    rw [eq_bot_iff, ← hCA]
    exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAX))
  -- `X` abelian with cyclic Sylows ⟹ `X` cyclic.
  have hXcyc : IsCyclic ↥X := by
    let : IsMulCommutative ↥X := hXab
    exact OddOrder.Isaacs.Ch06.isCyclic_of_sylow_isCyclic hSylcyc
  refine ⟨?_, hXcyc, fun p hp => hXτ2 p hp⟩
  -- **Part C**: `ℳ(C_G(X)) = {M}` via the cyclic generator `x`.
  obtain ⟨x₀, hx₀gen⟩ := hXcyc.exists_generator
  set x : G := (x₀ : G) with hxdef
  have hXeq : X = Subgroup.zpowers x := by
    apply le_antisymm
    · intro y hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hx₀gen ⟨y, hy⟩)
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      rw [hxdef, ← Subgroup.coe_zpow, hk]
    · rw [Subgroup.zpowers_le, hxdef]; exact x₀.2
  have hxX : x ∈ X := hXeq ▸ Subgroup.mem_zpowers x
  have hxM : x ∈ M := hXM hxX
  -- `x ≠ 1` (else `X = ⟨1⟩ = ⊥`).
  have hx1 : x ≠ 1 := by
    intro hxe
    apply hXne
    rw [hXeq, hxe, Subgroup.zpowers_one_eq_bot]
  -- `π(⟨x⟩) ⊆ τ₂(M)`.
  have hxτ2 : ∀ p ∈ piSet (Subgroup.closure {x}), p ∈ tau2 M := by
    intro p hp
    refine hXτ2 p ?_
    have : Subgroup.closure {x} = X := by rw [← Subgroup.zpowers_eq_closure, ← hXeq]
    rwa [this] at hp
  -- `C_G(X) = C_G({x})`.
  have hCeq : Subgroup.centralizer (X : Set G) = Subgroup.centralizer ({x} : Set G) := by
    rw [hXeq, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hCne : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
    rwa [hCeq] at hCX
  rw [hCeq]
  exact maximalContaining_centralizer_eq_singleton_of_tau2_element hG hM hxM hx1 hxτ2 hCne

/-- The `σ`-set is conjugation-invariant: `σ(Mᵍ) = σ(M)` (both inclusions from `sigma_conj`;
non-primes lie in neither set). -/
theorem sigma_conj_smul_eq [Finite G] (g : G) (M : Subgroup G) :
    OddOrder.BG.Ch3.S10.sigma (MulAut.conj g • M) = OddOrder.BG.Ch3.S10.sigma M := by
  ext p
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    refine ⟨fun hmem => ?_, fun hmem => OddOrder.BG.Ch3.S10.sigma_conj g hmem⟩
    have h2 := OddOrder.BG.Ch3.S10.sigma_conj g⁻¹ hmem
    rwa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h2
  · exact ⟨fun hmem => absurd (Nat.prime_of_mem_primeFactors
        ((OddOrder.BG.Ch3.S10.mem_sigma_iff _ p).mp hmem).1) hp,
      fun hmem => absurd (Nat.prime_of_mem_primeFactors
        ((OddOrder.BG.Ch3.S10.mem_sigma_iff _ p).mp hmem).1) hp⟩

/-- `O_π` (`opiCoreInG`) commutes with conjugation (replicated from the private
`S07_Transitivity.conj_smul_opiCoreInG`). -/
private theorem conj_smul_opiCoreInG' [Finite G] (π : Set ℕ) (φ : MulAut G) (H : Subgroup G) :
    φ • opiCoreInG π H = opiCoreInG π (φ • H) := by
  have hHmap : H.map (φ : G →* G) = φ • H := (mulAut_smul_eq_map φ H).symm
  let e : ↥H ≃* ↥(φ • H) :=
    (Subgroup.equivMapOfInjective H (φ : G →* G) φ.injective).trans
      (MulEquiv.subgroupCongr hHmap)
  have hcomp : (φ • H).subtype.comp (e : ↥H →* ↥(φ • H)) = (φ : G →* G).comp H.subtype := by
    ext x; rfl
  calc φ • opiCoreInG π H
      = (opiCoreInG π H).map (φ : G →* G) := mulAut_smul_eq_map φ _
    _ = ((Ch03.oPiCore π ↥H).map H.subtype).map (φ : G →* G) := rfl
    _ = (Ch03.oPiCore π ↥H).map ((φ : G →* G).comp H.subtype) := by rw [Subgroup.map_map]
    _ = (Ch03.oPiCore π ↥H).map ((φ • H).subtype.comp (e : ↥H →* ↥(φ • H))) := by rw [hcomp]
    _ = ((Ch03.oPiCore π ↥H).map (e : ↥H →* ↥(φ • H))).map (φ • H).subtype := by
        rw [← Subgroup.map_map]
    _ = (Ch03.oPiCore π ↥(φ • H)).map (φ • H).subtype := by
        rw [Ch03.oPiCore.map_eq_of_mulEquiv]

/-- `M_σ` is conjugation-equivariant: `(Mᵍ)_σ = (M_σ)ᵍ`.  Used to move an element of `M*_σ` back to
its conjugate maximal subgroup when witnessing `ℓ_σ = 1`. -/
theorem Msigma_conj_smul [Finite G] (g : G) (M : Subgroup G) :
    OddOrder.BG.Ch3.S10.Msigma (MulAut.conj g • M)
      = MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M := by
  simp only [OddOrder.BG.Ch3.S10.Msigma]
  rw [conj_smul_opiCoreInG', sigma_conj_smul_eq]

/-- **BG Corollary 14.3** (mmd L3852): for `x ∈ M_σ^#` and a nonidentity `σ(M)'`-element `x'`
of `C_M(x)`, either (1) `π(⟨x'⟩) ⊆ κ(M)` and `C_G(x) ⊆ M`, or (2) `π(⟨x'⟩) ⊆ τ₂(M)`,
`ℓ_σ(x') = 1`, and `𝓜(C_G(x')) = {M}`.

Proof sketch (gated on §13 via Prop 14.2): a prime `p ∈ π(⟨x'⟩) ∩ τ₂(M)'` lies in
`τ₁(M) ∪ τ₃(M)`, and `C_{M_σ}(X) ⊇ ⟨x⟩ ≠ 1` for `X ∈ ℰ_p¹(⟨x'⟩)` forces `p ∈ κ(M)`; then
Lemma 14.1(b) gives `x' ∈ K`, `x ∈ C_{M_σ}(K)`, and Proposition 14.2(c) yields `C_G(x) ⊆ M`
(branch 1).  Otherwise `x'` is a `τ₂(M)`-element with `C_{M_σ}(x') ≠ 1`, so Corollary 12.10(e)
gives `𝓜(C_G(x')) = {M}` and Lemma 12.11(a) gives `ℓ_σ(x') = 1` (branch 2).

**Faithfulness (2026-06-15):** reformulated to the verbatim BG statement.  The earlier scaffold
had an `x ↔ x'` transposition (branch 1's body asserted the impossible `x' ∈ M_σ`), a missing
`x'`-centralizes-`x` hypothesis, and dropped `C_G(x) ⊆ M`, `ℓ_σ(x')`, and `𝓜(C_G(x'))`.
`ℓ_σ(x')` is carried by the `SigmaDecompositionData` `D` (`D.length x' = 1`).  Proof deferred
(gated on §13).  See `notes/bg/s14_typeP_counting.md`. -/
theorem sigma_diagnostic [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {x x' : G}
    (hx : x ∈ sigmaSharp M) (hx'M : x' ∈ M) (hx'1 : x' ≠ 1)
    (hx'cent : x' ∈ Subgroup.centralizer ({x} : Set G))
    (hx'sigma : ∀ p ∈ piSet (Subgroup.closure {x'}),
      p ∉ OddOrder.BG.Ch3.S10.sigma M) :
    ((∀ p ∈ piSet (Subgroup.closure {x'}), p ∈ kappa M) ∧
        Subgroup.centralizer ({x} : Set G) ≤ M) ∨
    ((∀ p ∈ piSet (Subgroup.closure {x'}), p ∈ tau2 M) ∧
        D.length x' = 1 ∧
        maximalSubgroupsContaining (Subgroup.centralizer ({x'} : Set G)) = {M}) := by
  classical
  -- `x ∈ M_σ`, `x ≠ 1`.
  rw [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe] at hx
  obtain ⟨hxMσ, hx1⟩ := hx
  have hclos : Subgroup.closure ({x'} : Set G) = Subgroup.zpowers x' :=
    (Subgroup.zpowers_eq_closure x').symm
  -- `x` centralizes `x'`.
  have hxCx' : x ∈ Subgroup.centralizer ({x'} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]; intro y hy; rw [Set.mem_singleton_iff.mp hy]
    exact (Subgroup.mem_centralizer_iff.mp hx'cent x (Set.mem_singleton x)).symm
  -- `C_{M_σ}(x') ≠ 1` (it contains `x ≠ 1`).
  have hCx'ne : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x'} : Set G) ≠ ⊥ :=
    fun hbot => hx1 (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_inf.mpr ⟨hxMσ, hxCx'⟩))
  by_cases hτ2 : ∀ p ∈ piSet (Subgroup.closure {x'}), p ∈ tau2 M
  · -- **Branch 2**: `x'` is a `τ₂(M)`-element.
    refine Or.inr ⟨hτ2, ?_, maximalContaining_centralizer_eq_singleton_of_tau2_element hG hM
      hx'M hx'1 hτ2 hCx'ne⟩
    -- `ℓ_σ(x') = 1`: `x'` is a `σ(M*)`-element (Lemma 12.11(a)), hence `G`-conjugate into `M*_σ`
    -- (general Corollary 12.16(a)), so `𝓜_σ(x')` is nonempty.
    refine (D.length_one_iff x').mpr ⟨hx'1, ?_⟩
    -- `π(⟨x'⟩)` is nonempty (`x' ≠ 1`); pick a prime `q₀ ∈ π(⟨x'⟩) ⊆ τ₂(M)`.
    have hclosne : Subgroup.closure ({x'} : Set G) ≠ ⊥ := fun hbot =>
      hx'1 (Subgroup.mem_bot.mp (hbot ▸ Subgroup.subset_closure (Set.mem_singleton x')))
    obtain ⟨q₀, hq₀mem⟩ : (piSet (Subgroup.closure ({x'} : Set G))).Nonempty :=
      Nat.nonempty_primeFactors.mpr (lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne')
        (Ne.symm fun h => hclosne (Subgroup.card_eq_one.mp h)))
    have hq₀prime : q₀.Prime := Nat.prime_of_mem_primeFactors hq₀mem
    have : Fact q₀.Prime := ⟨hq₀prime⟩
    have hq₀τ2 : q₀ ∈ tau2 M := hτ2 q₀ hq₀mem
    -- `E`-setup, a rank-2 `A ∈ ℰ_{q₀}²(E)` (push `ℰ_{q₀}²(M)` into `E₂`), and `M* ∈ ℳ(N_G(A))`.
    obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := exists_subgroupESetup hG hM
    obtain ⟨A₁, hA₁, hA₁M⟩ := exists_mem_elemAbelianOfRank_two_le_of_tau2 hq₀prime hq₀τ2
    obtain ⟨w, _, hwle⟩ := exists_conj_smul_le_hallPiece hG hsetup hsetup.E₂_le hsetup.E₂_hall
      (tau2_subset_sigma_compl M) hA₁M (by
        intro r hr
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₁M).toEquiv, hA₁.2,
          Nat.primeFactors_pow q₀ two_ne_zero, Nat.Prime.primeFactors hq₀prime] at hr
        rw [Finset.mem_singleton.mp hr]; exact hq₀τ2)
    have hA : MulAut.conj w • A₁ ∈ elemAbelianOfRank G q₀ 2 := conj_smul_mem_elemAbelianOfRank w hA₁
    have hAE : MulAut.conj w • A₁ ≤ E := hwle.trans hsetup.E₂_le
    have hAM : MulAut.conj w • A₁ ≤ M := hAE.trans hsetup.E_le
    have hAne : MulAut.conj w • A₁ ≠ ⊥ := by
      intro hbot
      have hc : Nat.card ↥(MulAut.conj w • A₁) = q₀ ^ 2 := hA.2
      rw [hbot, Subgroup.card_bot] at hc
      rcases Nat.pow_eq_one.mp hc.symm with h | h
      · exact hq₀prime.ne_one h
      · exact absurd h (by norm_num)
    obtain ⟨Mstar, hMstar_max, hMstar_ge⟩ :=
      OddOrder.BG.Ch2.S08.exists_maximalSubgroup_containing_normalizer_of_ne_bot_le_maximal
        hG hM hAne hAM
    have hMstarMem : Mstar ∈ maximalSubgroupsContaining
        (Subgroup.normalizer ((MulAut.conj w • A₁ : Subgroup G) : Set G)) :=
      mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hMstar_max, hMstar_ge⟩
    -- Lemma 12.11(a): every prime of `π(⟨x'⟩) ⊆ τ₂(M)` lies in `σ(M*)`.
    have hx'piMstar : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma Mstar)
        (Subgroup.closure ({x'} : Set G)) := fun p hp =>
      (tau2_prime_mem_sigma_diff_beta hG hsetup hq₀τ2 hA hAE hMstarMem
        (Nat.prime_of_mem_primeFactors hp) (hτ2 p hp)).1
    -- general Corollary 12.16(a): `⟨x'⟩` is `G`-conjugate into `M*_σ`.
    have hzplt : Subgroup.closure ({x'} : Set G) < ⊤ :=
      lt_of_le_of_lt (by rw [hclos, Subgroup.zpowers_le]; exact hx'M)
        (mem_maximalSubgroups.mp hM).lt_top
    obtain ⟨g, hg⟩ := sigma_subgroup_conj_into_Msigma_general hG hMstar_max hclosne hzplt hx'piMstar
      (fun hN hnc => sigma_disjoint_of_nonconjugate hG hMstar_max hN hnc)
    -- `M' = (M*)^{g⁻¹}` is maximal and contains `x'` in its `σ`-core.
    refine ⟨MulAut.conj g⁻¹ • Mstar,
      mem_maximalSubgroups.mpr (isCoatom_conj_smul (mem_maximalSubgroups.mp hMstar_max)), ?_⟩
    rw [Msigma_conj_smul]
    have hconj : MulAut.conj g • x' ∈ OddOrder.BG.Ch3.S10.Msigma Mstar :=
      hg (Subgroup.smul_mem_pointwise_smul x' (MulAut.conj g) (Subgroup.closure ({x'} : Set G))
        (Subgroup.subset_closure (Set.mem_singleton x')))
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa using hconj
  · -- **Branch 1**: some prime `p₀ ∈ π(⟨x'⟩)` lies in `τ₁(M) ∪ τ₃(M)`.
    left
    push Not at hτ2
    obtain ⟨p₀, hp₀mem, hp₀τ2⟩ := hτ2
    have hp₀prime : p₀.Prime := Nat.prime_of_mem_primeFactors hp₀mem
    have : Fact p₀.Prime := ⟨hp₀prime⟩
    have hp₀σ : p₀ ∉ OddOrder.BG.Ch3.S10.sigma M := hx'sigma p₀ hp₀mem
    -- `⟨x'⟩ ≤ M`, so `p₀ ∣ |M|`, and `p₀ ∤ |M_σ|`, hence `p₀ ∈ π(E)`.
    obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := exists_subgroupESetup hG hM
    have hclosM : Subgroup.closure ({x'} : Set G) ≤ M := by
      rw [hclos, Subgroup.zpowers_le]; exact hx'M
    have hp₀cardclos : p₀ ∣ Nat.card ↥(Subgroup.closure ({x'} : Set G)) :=
      (Nat.mem_primeFactors.mp hp₀mem).2.1
    have hp₀M : p₀ ∣ Nat.card ↥M := hp₀cardclos.trans (Subgroup.card_dvd_of_le hclosM)
    have hp₀nMσ : ¬ p₀ ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := fun hdvd =>
      hp₀σ (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p₀
        (Nat.mem_primeFactors.mpr ⟨hp₀prime, hdvd, Nat.card_pos.ne'⟩))
    have hp₀E : p₀ ∈ (Nat.card ↥E).primeFactors := by
      refine Nat.mem_primeFactors.mpr ⟨hp₀prime, ?_, Nat.card_pos.ne'⟩
      have hdvdME : p₀ ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) * Nat.card ↥E := by
        rw [hsetup.card_Msigma_mul_card_E]; exact hp₀M
      exact (hp₀prime.dvd_mul.mp hdvdME).resolve_left hp₀nMσ
    have hp₀τ13 : p₀ ∈ tau1 M ∪ tau3 M := by
      rcases hsetup.mem_tau_union_of_mem_primeFactors hG hp₀E with (h1 | h2) | h3
      · exact Or.inl h1
      · exact absurd h2 hp₀τ2
      · exact Or.inr h3
    -- `X₀ = ⟨w⟩` of order `p₀`, `≤ ⟨x'⟩`, with `x ∈ C_{M_σ}(X₀)`, so `p₀ ∈ κ(M)`.
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p₀
      (hclos ▸ hp₀cardclos : p₀ ∣ Nat.card ↥(Subgroup.zpowers x'))
    set X₀ : Subgroup G := Subgroup.zpowers (w : G) with hX₀def
    have hX₀le_clos : X₀ ≤ Subgroup.closure ({x'} : Set G) := by
      rw [hX₀def, hclos, Subgroup.zpowers_le]; exact w.2
    have hX₀M : X₀ ≤ M := hX₀le_clos.trans hclosM
    have hwcard : Nat.card ↥X₀ = p₀ := by
      rw [hX₀def, Nat.card_zpowers]
      exact (orderOf_injective (Subgroup.zpowers x').subtype
        (Subgroup.zpowers x').subtype_injective w).trans hw
    have hX₀elem : X₀ ∈ elemAbelianOfRank G p₀ 1 :=
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hwcard, by rw [hwcard, pow_one]⟩
    have hX₀le_zp : X₀ ≤ Subgroup.zpowers x' := by
      rw [hX₀def, Subgroup.zpowers_le]; exact w.2
    -- `x` centralizes `X₀` (it centralizes `x'`, and `X₀ ≤ ⟨x'⟩`).
    have hcomm : Commute x x' :=
      Subgroup.mem_centralizer_iff.mp hx'cent x (Set.mem_singleton x)
    have hxCw : Commute x (w : G) := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp w.2
      rw [← hn]; exact hcomm.zpow_right n
    have hxCX₀ : x ∈ Subgroup.centralizer (X₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hX₀def, SetLike.mem_coe] at hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (hxCw.zpow_right m).symm
    have hCX₀ne : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X₀ : Set G) ≠ ⊥ :=
      fun hbot => hx1 (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_inf.mpr ⟨hxMσ, hxCX₀⟩))
    have hp₀κ : p₀ ∈ kappa M := ⟨hp₀prime, hp₀τ13, X₀, hX₀elem, hX₀M, hCX₀ne⟩
    -- A Hall `κ(M)`-subgroup `K ⊇ X₀`, a Hall `(κ∪σ)'`-subgroup `U`, and `Kstar = C_{M_σ}(K)`.
    have hX₀κ : ∀ q ∈ (Nat.card ↥X₀).primeFactors, q ∈ kappa M := by
      intro q hq
      rw [hwcard, hp₀prime.primeFactors, Finset.mem_singleton] at hq
      exact hq ▸ hp₀κ
    obtain ⟨K, hKM, hK, hX₀K⟩ := exists_isHallSubgroup_kappa_ge hG hM hX₀M hX₀κ
    have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
    obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
      ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
    have hUeq : (U'.map M.subtype).subgroupOf M = U' :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
    have hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
        ((U'.map M.subtype).subgroupOf M) := by rw [hUeq]; exact hU'
    have hP : IsTypeP M := ⟨p₀, hp₀κ⟩
    obtain ⟨_, _, hb1, _, _, hc, _⟩ := typeP_structure hG hM hP hKM hK
      (rfl : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) =
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) hU
    -- `C_M(x') ⊆ N_G(X₀) ⊓ M = K ⊔ K*` (Prop 14.2(b1)).
    have hb1X₀ := hb1 p₀ hp₀prime X₀ hX₀elem hX₀K
    have hCx'_le_CX₀ : Subgroup.centralizer ({x'} : Set G) ≤ Subgroup.centralizer (X₀ : Set G) := by
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hX₀def, SetLike.mem_coe] at hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hgw : Commute g (w : G) := by
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp w.2
        rw [← hn]
        have hgx' : Commute x' g := Subgroup.mem_centralizer_iff.mp hg x' (Set.mem_singleton x')
        exact hgx'.symm.zpow_right n
      exact (hgw.zpow_right m).symm
    have hCMx'_le : Subgroup.centralizer ({x'} : Set G) ⊓ M ≤
        K ⊔ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) := by
      rw [← hb1X₀]
      exact inf_le_inf_right _ (hCx'_le_CX₀.trans (Subgroup.centralizer_le_normalizer _))
    -- `x' ∈ K` (the `σ'`-part) and `x ∈ K*` (the `σ`-part) of `K ⊔ K* = K × K*`.
    set Kst : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
      with hKstdef
    have hKstMσ : Kst ≤ OddOrder.BG.Ch3.S10.Msigma M := inf_le_left
    have hKstC : Kst ≤ Subgroup.centralizer (K : Set G) := inf_le_right
    -- `K` is normal in `K ⊔ K*` (`K*` centralizes `K`), so elements decompose as `k · s`.
    have hKnorm : K ⊔ Kst ≤ Subgroup.normalizer (K : Set G) :=
      sup_le Subgroup.le_normalizer (hKstC.trans (Subgroup.centralizer_le_normalizer _))
    have hKsNorm : ((K).subgroupOf (K ⊔ Kst)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hKnorm
    have hsuptop : (K.subgroupOf (K ⊔ Kst)) ⊔ (Kst.subgroupOf (K ⊔ Kst)) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    have hdecomp : ∀ z : G, z ∈ K ⊔ Kst → ∃ k ∈ K, ∃ s ∈ Kst, k * s = z := by
      intro z hz
      obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp
        (hsuptop ▸ Subgroup.mem_top (⟨z, hz⟩ : ↥(K ⊔ Kst)))
      exact ⟨(a : G), Subgroup.mem_subgroupOf.mp ha, (b : G), Subgroup.mem_subgroupOf.mp hb,
        by have := congrArg Subtype.val hab; simpa using this⟩
    -- `K ∩ M_σ = ⊥` (`K` is a `κ(M) ⊆ σ(M)'`-group, `M_σ` a `σ(M)`-group).
    have hKMσbot : K ⊓ OddOrder.BG.Ch3.S10.Msigma M = ⊥ := by
      apply Disjoint.eq_bot
      refine Subgroup.disjoint_of_coprime_natCard (coprime_of_forall_prime_not_dvd ?_)
      intro r hr hrK hrMσ
      have hrκ : r ∈ kappa M := hK.1 r (by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
        exact Nat.mem_primeFactors.mpr ⟨hr, hrK, Nat.card_pos.ne'⟩)
      exact kappa_subset_sigmaCompl hrκ (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M r
        (Nat.mem_primeFactors.mpr ⟨hr, hrMσ, Nat.card_pos.ne'⟩))
    have hcardclos : Nat.card ↥(Subgroup.closure ({x'} : Set G)) = orderOf x' := by
      rw [hclos, Nat.card_zpowers]
    -- `x ∈ K*`: `x = k · s` with `k ∈ K`, `s ∈ K* ≤ M_σ`; `x ∈ M_σ` forces `k ∈ K ∩ M_σ = ⊥`.
    have hxsup : x ∈ K ⊔ Kst :=
      hCMx'_le (Subgroup.mem_inf.mpr ⟨hxCx', (OddOrder.BG.Ch3.S10.Msigma_le M) hxMσ⟩)
    have hxKstar : x ∈ Kst := by
      obtain ⟨k, hkK, s, hsKst, hks⟩ := hdecomp x hxsup
      have hkMσ : k ∈ OddOrder.BG.Ch3.S10.Msigma M := by
        have : k = x * s⁻¹ := by rw [← hks]; group
        rw [this]
        exact (OddOrder.BG.Ch3.S10.Msigma M).mul_mem hxMσ
          ((OddOrder.BG.Ch3.S10.Msigma M).inv_mem (hKstMσ hsKst))
      have hk1 : k = 1 := Subgroup.mem_bot.mp (hKMσbot ▸ Subgroup.mem_inf.mpr ⟨hkK, hkMσ⟩)
      rw [← hks, hk1, one_mul]; exact hsKst
    -- `x' ∈ K`: `x' = k · s` with `s ∈ K* ≤ M_σ`; `x'` is a `σ'`-element, so `s = 1`.
    have hx'sup : x' ∈ K ⊔ Kst :=
      hCMx'_le (Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_centralizer_iff.mpr (fun y hy => by rw [Set.mem_singleton_iff.mp hy]), hx'M⟩)
    have hx'K : x' ∈ K := by
      obtain ⟨k, hkK, s, hsKst, hks⟩ := hdecomp x' hx'sup
      have hcommks : Commute k s := Subgroup.mem_centralizer_iff.mp (hKstC hsKst) k hkK
      have hsM : s ∈ OddOrder.BG.Ch3.S10.Msigma M := hKstMσ hsKst
      -- `(k·s)^N = k^N · s^N = 1` (`N = orderOf x'`), so `k^N = (s^N)⁻¹ ∈ K ∩ M_σ = ⊥`.
      have hN : k ^ orderOf x' * s ^ orderOf x' = 1 := by
        rw [← hcommks.mul_pow, hks]; exact pow_orderOf_eq_one x'
      have hkN1 : k ^ orderOf x' = 1 := by
        have hmem : k ^ orderOf x' ∈ K ⊓ OddOrder.BG.Ch3.S10.Msigma M :=
          Subgroup.mem_inf.mpr ⟨K.pow_mem hkK _, by
            rw [eq_inv_of_mul_eq_one_left hN]
            exact (OddOrder.BG.Ch3.S10.Msigma M).inv_mem
              ((OddOrder.BG.Ch3.S10.Msigma M).pow_mem hsM _)⟩
        exact Subgroup.mem_bot.mp (hKMσbot ▸ hmem)
      have hsN1 : s ^ orderOf x' = 1 := by
        have := hN; rw [hkN1, one_mul] at this; exact this
      -- `orderOf s ∣ orderOf x'` and `orderOf s ∣ |M_σ|`, which are coprime, so `s = 1`.
      have hcop : Nat.Coprime (orderOf x') (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)) :=
        coprime_of_forall_prime_not_dvd (fun r hr hrx' hrMσ => by
          exact hx'sigma r (by
            rw [piSet, Set.mem_ofPred_eq, hcardclos]
            exact Nat.mem_primeFactors.mpr ⟨hr, hrx', (orderOf_pos_iff.mpr
              (isOfFinOrder_of_finite x')).ne'⟩)
            (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M r
              (Nat.mem_primeFactors.mpr ⟨hr, hrMσ, Nat.card_pos.ne'⟩)))
      have hsord : orderOf s = 1 := by
        have hdvd1 : orderOf s ∣ orderOf x' := orderOf_dvd_of_pow_eq_one hsN1
        have hdvd2 : orderOf s ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
          have h := orderOf_dvd_natCard (⟨s, hsM⟩ : ↥(OddOrder.BG.Ch3.S10.Msigma M))
          rwa [← orderOf_injective (OddOrder.BG.Ch3.S10.Msigma M).subtype
            (OddOrder.BG.Ch3.S10.Msigma M).subtype_injective ⟨s, hsM⟩] at h
        have hg : orderOf s ∣ Nat.gcd (orderOf x')
            (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)) := Nat.dvd_gcd hdvd1 hdvd2
        rw [hcop] at hg
        exact Nat.dvd_one.mp hg
      have hs1 : s = 1 := orderOf_eq_one_iff.mp hsord
      rw [← hks, hs1, mul_one]; exact hkK
    refine ⟨?_, ?_⟩
    · -- `π(⟨x'⟩) ⊆ κ(M)`: `x' ∈ K`, `K` is a Hall `κ(M)`-subgroup.
      intro p hp
      rw [hclos] at hp
      have hpK : p ∈ (Nat.card ↥K).primeFactors := by
        refine Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, ?_, Nat.card_pos.ne'⟩
        exact ((Nat.mem_primeFactors.mp hp).2.1.trans
          (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx'K)))
      have hpKM : p ∈ (Nat.card ↥(K.subgroupOf M)).primeFactors := by
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
      exact hK.1 p hpKM
    · -- `C_G(x) ⊆ M`: a rank-one `X₁ ≤ ⟨x⟩ ≤ K*` has `ℳ(C_G(X₁)) = {M}` (Prop 14.2(c)),
      -- and `C_G(x) ⊆ C_G(X₁) ⊆ M`.
      obtain ⟨p₁, hp₁, hp₁dvd⟩ := Nat.exists_prime_and_dvd
        (show orderOf x ≠ 1 from fun h => hx1 (orderOf_eq_one_iff.mp h))
      have : Fact p₁.Prime := ⟨hp₁⟩
      obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers x)) p₁
        (by rw [Nat.card_zpowers]; exact hp₁dvd)
      have hvcard : Nat.card ↥(Subgroup.zpowers (v : G)) = p₁ := by
        rw [Nat.card_zpowers]
        exact (orderOf_injective (Subgroup.zpowers x).subtype
          (Subgroup.zpowers x).subtype_injective v).trans hv
      have hX₁elem : Subgroup.zpowers (v : G) ∈ elemAbelianOfRank G p₁ 1 :=
        ⟨Subgroup.IsElementaryAbelian.of_card_prime hvcard, by rw [hvcard, pow_one]⟩
      have hvx : (v : G) ∈ Subgroup.zpowers x := v.2
      have hX₁Kst : Subgroup.zpowers (v : G) ≤ Kst :=
        Subgroup.zpowers_le.mpr ((Subgroup.zpowers_le.mpr hxKstar) hvx)
      have h𝓜 : maximalSubgroupsContaining
          (Subgroup.centralizer (↑(Subgroup.zpowers (v : G)) : Set G)) = {M} :=
        hc p₁ hp₁ (Subgroup.zpowers (v : G)) hX₁elem hX₁Kst
      have hCX₁M : Subgroup.centralizer (↑(Subgroup.zpowers (v : G)) : Set G) ≤ M :=
        (mem_maximalSubgroupsContaining.mp (by rw [h𝓜]; exact Set.mem_singleton M)).2
      refine le_trans ?_ hCX₁M
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [SetLike.mem_coe] at hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hgx : Commute g x := (Subgroup.mem_centralizer_iff.mp hg x (Set.mem_singleton x)).symm
      have hgv : Commute g (v : G) := by
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hvx
        rw [← hn]; exact hgx.zpow_right n
      exact ((hgv.zpow_right m).symm)

/-- Centralizer of `⟨x⟩` equals centralizer of `{x}` (replicated private helper). -/
theorem centralizer_zpowers_eq_singleton' (x : G) :
    Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)
      = Subgroup.centralizer ({x} : Set G) := by
  ext c
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro hc y hy
    rw [Set.mem_singleton_iff] at hy
    exact hy ▸ hc x (Subgroup.mem_zpowers x)
  · intro hc y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((show Commute x c from hc x rfl).zpow_left k).eq

/-- **Theorem 14.7 neighbour `κ`-transfer** (BG L3983-3991), step 1b of the §16-independent
pre-position: in the situation of `typeP_neighbor_embed`, every prime `q ∈ π(K*)` lies in
`κ(M_i)`.

Proof: take `X* = ⟨x'⟩ ∈ ℰ_q¹(K*)` (Cauchy).  Since `x ∈ X ⊆ M_{iσ}^#` centralizes `x'` (both
lie in `Z = K × K*` with `[K, K*] = 1`) and `x' ∈ K*` is a `σ(M_i)'`-element (Theorem 13.9 makes
`σ(M)` disjoint from `σ(M_i)`), Corollary 14.3 (`sigma_diagnostic`) applies to `(M_i, x, x')`.
Its branch 2 would give `ℳ(C_G(x')) = {M_i}`, contradicting Prop 14.2(c)'s `ℳ(C_G(x')) = {M}`
(`M ≠ M_i`); so branch 1 holds, giving `q ∈ π(⟨x'⟩) ⊆ κ(M_i)`.  (`sigma_diagnostic`'s `ℓ_σ`
carrier `D` is supplied by a dummy `SigmaDecompositionData`; only the branch dichotomy and its
`ℳ(C_G(x'))` clause are used, not `D.length`.) -/
theorem typeP_neighbor_kappa [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXK : X ≤ K)
    (hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥)
    {Mi : Subgroup G} (hMi : Mi ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))) :
    ∀ q ∈ (Nat.card ↥Kstar).primeFactors, q ∈ kappa Mi := by
  classical
  obtain ⟨hnc, hZMi, hXMiσ⟩ := typeP_neighbor_embed hG hM hP hKM hK hKstar hU hX hXK hCX hMi
  obtain ⟨_, _, _, _, _, hc, _⟩ := typeP_structure hG hM hP hKM hK hKstar hU
  have hMiMax : Mi ∈ maximalSubgroups G :=
    mem_maximalSubgroups.mpr (mem_maximalSubgroupsContaining.mp hMi).1
  have hσdisj := OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hM hMiMax hnc
  -- A dummy `ℓ_σ` carrier for `sigma_diagnostic`.
  let D : SigmaDecompositionData G :=
    { length := fun y => if y ≠ 1 ∧ (maximalSigmaSubgroupsOfElement y).Nonempty then 1 else 0
      length_one_iff := by
        intro y; by_cases h : y ≠ 1 ∧ (maximalSigmaSubgroupsOfElement y).Nonempty <;> simp [h] }
  -- An element `x ∈ X^#` lands in `M_{iσ}^#`.
  have hXne : X ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hX
  have : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr hXne
  obtain ⟨xsub, hxsub⟩ := exists_ne (1 : ↥X)
  have hxX : (xsub : G) ∈ X := xsub.2
  have hxne : (xsub : G) ≠ 1 := fun h => hxsub (OneMemClass.coe_eq_one.mp h)
  have hxK : (xsub : G) ∈ K := hXK hxX
  have hxsharp : (xsub : G) ∈ sigmaSharp Mi := by
    rw [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe]
    exact ⟨hXMiσ hxX, hxne⟩
  intro q hq
  have : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hq⟩
  -- Cauchy: `x' ∈ K*` of order `q`.
  obtain ⟨x'sub, hx'ord⟩ := exists_prime_orderOf_dvd_card' q
    (Nat.dvd_of_mem_primeFactors hq : q ∣ Nat.card ↥Kstar)
  have hx'Kstar : (x'sub : G) ∈ Kstar := x'sub.2
  have hx'ord' : orderOf (x'sub : G) = q :=
    (orderOf_injective Kstar.subtype Kstar.subtype_injective x'sub).trans hx'ord
  have hx'ne : (x'sub : G) ≠ 1 := by
    intro h; rw [h, orderOf_one] at hx'ord'
    exact (Nat.prime_of_mem_primeFactors hq).ne_one hx'ord'.symm
  have hX'card : Nat.card ↥(Subgroup.zpowers (x'sub : G)) = q := by rw [Nat.card_zpowers, hx'ord']
  have hX'mem : Subgroup.zpowers (x'sub : G) ∈ elemAbelianOfRank G q 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hX'card, by rw [hX'card, pow_one]⟩
  have hX'Kstar : Subgroup.zpowers (x'sub : G) ≤ Kstar := Subgroup.zpowers_le.mpr hx'Kstar
  have hx'Mi : (x'sub : G) ∈ Mi := hZMi (Subgroup.mem_sup_right hx'Kstar)
  have hx'CK : (x'sub : G) ∈ Subgroup.centralizer (K : Set G) := by
    have h2 : (x'sub : G) ∈ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) := by
      rw [← hKstar]; exact hx'Kstar
    exact (Subgroup.mem_inf.mp h2).2
  have hxCx' : (x'sub : G) ∈ Subgroup.centralizer ({(xsub : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]; intro y hy; rw [Set.mem_singleton_iff.mp hy]
    exact Subgroup.mem_centralizer_iff.mp hx'CK (xsub : G) hxK
  have hqσM : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q (Nat.mem_primeFactors.mpr ⟨Fact.out,
      (Nat.dvd_of_mem_primeFactors hq).trans (Subgroup.card_dvd_of_le
        (by rw [hKstar]; exact inf_le_left : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M)),
      Nat.card_pos.ne'⟩)
  have hclos' : Subgroup.closure ({(x'sub : G)} : Set G) = Subgroup.zpowers (x'sub : G) :=
    (Subgroup.zpowers_eq_closure (x'sub : G)).symm
  have hcardclos : Nat.card ↥(Subgroup.closure ({(x'sub : G)} : Set G)) = q :=
    (congrArg (fun S : Subgroup G => Nat.card ↥S) hclos').trans hX'card
  have hx'sigma : ∀ r ∈ piSet (Subgroup.closure {(x'sub : G)}),
      r ∉ OddOrder.BG.Ch3.S10.sigma Mi := by
    intro r hr
    simp only [piSet, hcardclos, Nat.Prime.primeFactors (Nat.prime_of_mem_primeFactors hq),
      Finset.mem_singleton] at hr
    rw [hr]; exact Set.disjoint_left.mp hσdisj hqσM
  rcases sigma_diagnostic hG D hMiMax hxsharp hx'Mi hx'ne hxCx' hx'sigma with
    ⟨hπκ, _⟩ | ⟨_, _, hℳ⟩
  · refine hπκ q ?_
    simp only [piSet, hcardclos, Nat.Prime.primeFactors (Nat.prime_of_mem_primeFactors hq)]
    exact Finset.mem_singleton_self q
  · exfalso
    have hcX' := hc q (Nat.prime_of_mem_primeFactors hq) (Subgroup.zpowers (x'sub : G)) hX'mem
      hX'Kstar
    rw [centralizer_zpowers_eq_singleton'] at hcX'
    rw [hcX'] at hℳ
    exact hnc ((Set.singleton_eq_singleton_iff.mp hℳ) ▸ IsConjugateSubgroup.refl M)

end OddOrder.BG.Ch4.S14


