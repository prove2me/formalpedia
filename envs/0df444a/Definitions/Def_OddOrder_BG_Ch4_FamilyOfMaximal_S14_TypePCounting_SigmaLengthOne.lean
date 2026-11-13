-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_SigmaLengthOne
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_SigmaLengthOne
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T09:18:37.050243+00:00
-- url     : https://prove2.me/theorems/14db9aec-5c7d-4cc8-a70c-f735c36fd259
-- title:
--   BG §14: type-$\mathcal{P}$ counting, $\sigma$-length one (continuation)
-- statement:
--   A continuation of the $\sigma$-length-one part of the §14 type-$\mathcal{P}$ counting development of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*. Lemmas include self-normalizing behaviour of maximal subgroups, counting of conjugates via the index of the normalizer, $\sigma$-elements lying in $M_\sigma$, and signalizer-coset statements for $M_\sigma^\#$.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 26 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/SigmaLengthOne.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/SigmaLengthOne.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_Conjugacy145C

namespace OddOrder.BG.Ch4.S14

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch3.S13

open scoped Pointwise

variable {G : Type*} [Group G]

/-- A maximal subgroup of a minimal simple group is self-normalizing (`N_G(M) = M`).  If
`M < N_G(M)` then maximality forces `N_G(M) = ⊤`, i.e. `M ◁ G`, so by simplicity `M = ⊥` or
`M = ⊤`, both excluded (`⊥` is not maximal, `⊤` is not a coatom).  This pins the number of
conjugates of `M` to `[G : M]` (`ncard_conjugates_eq_index_of_normalizer_eq_self`). -/
theorem normalizer_eq_self_of_mem_maximalSubgroups [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    Subgroup.normalizer M = M := by
  have hcoatom : IsCoatom M := mem_maximalSubgroups.mp hM
  rcases eq_or_lt_of_le (Subgroup.le_normalizer (H := M)) with h | h
  · exact h.symm
  · exfalso
    have hnorm : M.Normal := Subgroup.normalizer_eq_top_iff.mp (hcoatom.2 _ h)
    rcases hG.simple.eq_bot_or_eq_top_of_normal M hnorm with hb | ht
    · exact hG.ne_bot_of_isCoatom hcoatom hb
    · exact hcoatom.1 ht

/-- **Orbit–stabilizer for subgroup conjugation**: when `M` is self-normalizing (`N_G(M) = M`),
the number of conjugates of `M` equals `[G : M]`.  This generalises
`ncard_conjugates_eq_index_of_TI` (which derives `N_G(M) = M` from a TI hypothesis) to any
self-normalizing `M`; the orbit map `g ↦ Mᵍ` factors through `G ⧸ M`. -/
theorem ncard_conjugates_eq_index_of_normalizer_eq_self [Finite G] {M : Subgroup G}
    (hNGM : Subgroup.normalizer M = M) :
    (Set.range (fun g : G => MulAut.conj g • M)).ncard = M.index := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set conjs : Set (Subgroup G) := Set.range (fun g : G => MulAut.conj g • M) with hconjs_def
  let f : G → conjs := fun g => ⟨MulAut.conj g • M, ⟨g, rfl⟩⟩
  have hf_lift : ∀ g₁ g₂ : G, (QuotientGroup.leftRel M) g₁ g₂ → f g₁ = f g₂ := by
    intro g₁ g₂ hrel
    rw [QuotientGroup.leftRel_apply] at hrel
    have h_in_N : g₁⁻¹ * g₂ ∈ Subgroup.normalizer M := by rw [hNGM]; exact hrel
    have h_conj : MulAut.conj (g₁⁻¹ * g₂) • M = M :=
      Subgroup.conj_smul_eq_self_of_mem (by rw [hNGM] at h_in_N; exact h_in_N)
    ext1
    simp only [f]
    have heq : MulAut.conj g₂ = MulAut.conj g₁ * MulAut.conj (g₁⁻¹ * g₂) := by
      rw [← map_mul]; congr 1; group
    calc (MulAut.conj g₁ • M : Subgroup G)
        = MulAut.conj g₁ • (MulAut.conj (g₁⁻¹ * g₂) • M) := by rw [h_conj]
      _ = (MulAut.conj g₁ * MulAut.conj (g₁⁻¹ * g₂)) • M := by rw [mul_smul]
      _ = MulAut.conj g₂ • M := by rw [← heq]
  let f' : G ⧸ M → conjs := Quotient.lift f (fun a b => hf_lift a b)
  have hf_surj : Function.Surjective f' := by
    rintro ⟨B, g, rfl⟩
    exact ⟨⟦g⟧, rfl⟩
  have hf_inj : Function.Injective f' := by
    rintro ⟨g₁⟩ ⟨g₂⟩ hfeq
    change f g₁ = f g₂ at hfeq
    have hsub : (MulAut.conj g₁ • M : Subgroup G) = MulAut.conj g₂ • M := Subtype.ext_iff.mp hfeq
    have h_step : (MulAut.conj (g₂⁻¹ * g₁) • M : Subgroup G) = M := by
      have heq : MulAut.conj (g₂⁻¹ * g₁) = MulAut.conj g₂⁻¹ * MulAut.conj g₁ := by rw [← map_mul]
      rw [heq, mul_smul, hsub, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    have h_mem : g₂⁻¹ * g₁ ∈ Subgroup.normalizer M := by
      rw [Subgroup.mem_normalizer_iff'']
      intro y
      have hmem : y ∈ MulAut.conj (g₂⁻¹ * g₁) • M ↔ y ∈ M := by rw [h_step]
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hmem
      have hcalc : (MulAut.conj (g₂⁻¹ * g₁))⁻¹ • y = (g₂⁻¹ * g₁)⁻¹ * y * (g₂⁻¹ * g₁) := by
        change (MulAut.conj (g₂⁻¹ * g₁)).symm y = _
        rw [MulAut.conj_symm_apply]
      rw [hcalc] at hmem
      exact hmem.symm
    rw [hNGM] at h_mem
    apply Quotient.sound
    change (QuotientGroup.leftRel M) g₁ g₂
    rw [QuotientGroup.leftRel_apply]
    have : (g₂⁻¹ * g₁)⁻¹ ∈ M := M.inv_mem h_mem
    simpa [mul_inv_rev] using this
  have hbij : Function.Bijective f' := ⟨hf_inj, hf_surj⟩
  have h_card_eq : Nat.card conjs = Nat.card (G ⧸ M) :=
    (Nat.card_congr (Equiv.ofBijective f' hbij)).symm
  rw [← Nat.card_coe_set_eq, h_card_eq, ← Subgroup.index]

/-- **Hall conjugacy** (Coq `Hall_subJ` for the solvable maximal `M`): in a maximal subgroup `M`,
every `π`-subgroup `X ≤ M` is conjugate by an element of `M` into any Hall `π`-subgroup `K` of `M`.
This is the general-`π` form of `exists_conj_smul_le_isHall_kappa` (which specialises `π = κ(M)`);
the proof embeds `X` in a Hall `π`-subgroup of the solvable `↥M` and conjugates the two Hall
subgroups together (`exists_conj_eq_of_isHall_subgroupOf`). -/
theorem exists_conj_smul_le_of_isHall [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {π : Set ℕ} (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup π (K.subgroupOf M))
    {X : Subgroup G} (hXM : X ≤ M)
    (hXpi : Ch03.Subgroup.IsPiGroup π (X.subgroupOf M)) :
    ∃ w ∈ M, MulAut.conj w • X ≤ K := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  obtain ⟨H, hH_hall, -, hX_le_H⟩ :=
    OddOrder.BG.Ch1.S01.aInvariant_piSubgroup_le_aInvariant_hall
      (A := Unit) (φ := (1 : Unit →* MulAut ↥M))
      (by rw [Nat.card_unique]; exact Nat.coprime_one_left _)
      hXpi (fun _ => one_smul _ _)
  set HG : Subgroup G := H.map M.subtype with hHGdef
  have hHG_le_M : HG ≤ M := Subgroup.map_subtype_le _
  have hHG_hall : Ch03.IsHallSubgroup π (HG.subgroupOf M) := by
    rwa [hHGdef, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  obtain ⟨w, hwM, hw⟩ :=
    OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf inferInstance hHG_le_M hKM
      hHG_hall hK
  have hXHG : X ≤ HG := by
    intro x hx
    rw [hHGdef]
    exact Subgroup.mem_map.mpr ⟨⟨x, hXM hx⟩, hX_le_H (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  exact ⟨w, hwM, (conj_smul_mono (MulAut.conj w) hXHG).trans hw.le⟩

/-- **Converse of `isPiElement_sigma_of_mem_Msigma`** (Coq `mem_Hall_pcore (Msigma_Hall maxM)`):
a `σ(M)`-element `x ∈ M` lies in `M_σ`.  The image of `x` in the quotient `M / M_σ` is a
`σ(M)`-element (a power of `x`), but `M_σ` is a Hall `σ(M)`-subgroup of `M` so `M / M_σ` is a
`σ(M)′`-group; hence the image is trivial and `x ∈ M_σ`. -/
theorem mem_Msigma_of_isPiElement_sigma_of_mem [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {x : G} (hxM : x ∈ M)
    (hxpi : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x) :
    x ∈ OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  set Ms : Subgroup ↥M := (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M with hMs
  have hNorm : Ms.Normal := by rw [hMs, OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
  have hHall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M) Ms :=
    OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM
  set xM : ↥M := ⟨x, hxM⟩ with hxMdef
  have hord : orderOf xM = orderOf x :=
    (orderOf_injective M.subtype M.subtype_injective xM).symm
  set q : ↥M ⧸ Ms := QuotientGroup.mk' Ms xM with hq
  have h1 : orderOf q ∣ orderOf xM := by
    rw [hq]; exact orderOf_map_dvd (QuotientGroup.mk' Ms) xM
  have hq1 : orderOf q = 1 := by
    by_contra hne
    obtain ⟨p, hpprime, hpdvd⟩ := (orderOf q).exists_prime_and_dvd hne
    have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M :=
      hxpi p (Nat.mem_primeFactors.mpr
        ⟨hpprime, (hpdvd.trans h1).trans (dvd_of_eq hord), (orderOf_pos x).ne'⟩)
    have hpidx : p ∈ Ms.index.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpprime, by
        rw [Subgroup.index_eq_card]; exact hpdvd.trans (orderOf_dvd_natCard q),
        by rw [Subgroup.index_eq_card]; exact Nat.card_pos.ne'⟩
    exact hHall.index_no_pi p hpidx hpσ
  have hqone : q = 1 := orderOf_eq_one_iff.mp hq1
  have hxMmem : xM ∈ Ms := (QuotientGroup.eq_one_iff xM).mp hqone
  exact Subgroup.mem_subgroupOf.mp hxMmem

/-- **Coq `cent1_sub_uniq_sigma_mmax`** (BGsection14:1008, a supplement to Theorem 14.4): if
`𝓜_σ(x)` is a singleton, its unique element `M` contains `C_G(x)`.  Conjugation by any
`y ∈ C_G(x)` permutes `𝓜_σ(x)` (it fixes `x`), hence fixes the unique element `M`, so
`y ∈ N_G(M) = M`.  This is the linchpin of the `|𝓜_σ(x')| > 1` step in BG Lemma 14.6. -/
theorem centralizer_le_of_maximalSigma_ncard_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {x : G} {M : Subgroup G}
    (hcard : (maximalSigmaSubgroupsOfElement x).ncard = 1)
    (hM : M ∈ maximalSigmaSubgroupsOfElement x) :
    Subgroup.centralizer ({x} : Set G) ≤ M := by
  classical
  obtain ⟨N, hsingle⟩ := Set.ncard_eq_one.mp hcard
  have hmax : M ∈ maximalSubgroups G := hM.1
  have hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M := hM.2
  intro y hy
  have hcom : x * y = y * x := (Subgroup.mem_centralizer_iff.mp hy) x (Set.mem_singleton x)
  -- `y` fixes `x` by conjugation.
  have hyx : MulAut.conj y • x = x := by
    rw [MulAut.smul_def, MulAut.conj_apply, mul_inv_eq_iff_eq_mul]; exact hcom.symm
  -- `Mʸ ∈ 𝓜_σ(x)`: it is maximal and `x = y·x·y⁻¹ ∈ Mʸ_σ`.
  have hconjMem : (MulAut.conj y • M) ∈ maximalSigmaSubgroupsOfElement x := by
    refine ⟨mem_maximalSubgroups.mpr (isCoatom_conj_smul (mem_maximalSubgroups.mp hmax)), ?_⟩
    rw [Msigma_conj_smul, ← hyx]
    exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj y) (OddOrder.BG.Ch3.S10.Msigma M) hxMσ
  -- both lie in the singleton `{N}`, so `Mʸ = M`.
  have heq : MulAut.conj y • M = M := by
    rw [hsingle, Set.mem_singleton_iff] at hconjMem hM; rw [hconjMem, ← hM]
  -- hence `y ∈ N_G(M) = M`.
  have hyN : y ∈ Subgroup.normalizer (M : Set G) :=
    OddOrder.BG.Ch1.S03f.mem_normalizer_of_map_conj_eq heq
  rwa [normalizer_eq_self_of_mem_maximalSubgroups hG hmax] at hyN

/-- **Honest content of Coq `s'g`** (the heart of BG Lemma 14.6,
`sigma_decomposition_dichotomy`): for `x ∈ M_σ^#` and a nonidentity `σ(M)′`-element `x'` of `M`
that centralizes `x`, the product `g = x · x'` falls into one of the two branches of the
σ-decomposition dichotomy:

* the **signalizer branch** — some `y` with `ℓ_σ(y) = 1` and `y⁻¹ g ∈ R(y)` (witnessed by
  `y = x'`, with `x'⁻¹ g = x ∈ R(x')`); or
* the **κ branch** — `ℓ_σ(x) = 1`, `M ∈ 𝓜_σ(x)`, `x' ∈ (C_M[x])^#`, and `x'` is a
  `κ(M)`-element.

This is the direct consumer of `sigma_diagnostic` (BG Cor 14.3 / `pi_of_cent_sigma`): the τ₂
branch lands in the signalizer disjunct (using `centralizer_le_of_maximalSigma_ncard_eq_one`
to force `|𝓜_σ(x')| > 1` and `exists_neighbor_eq_Rsub` to identify the neighbour `N` with `M`),
and the κ branch lands in the κ disjunct verbatim. -/
theorem signalizer_coset_or_kappa_of_sigmaSharp [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {x x' : G}
    (hx : x ∈ sigmaSharp M) (hx'M : x' ∈ M) (hx'1 : x' ≠ 1)
    (hx'cent : x' ∈ Subgroup.centralizer ({x} : Set G))
    (hx'sigma : ∀ p ∈ piSet (Subgroup.closure {x'}), p ∉ OddOrder.BG.Ch3.S10.sigma M) :
    (∃ y, D.length y = 1 ∧ y⁻¹ * (x * x') ∈ Rsub hG D y)
    ∨ (D.length x = 1 ∧ M ∈ maximalSigmaSubgroupsOfElement x ∧
        x' ∈ sharpSubgroup (M ⊓ Subgroup.centralizer ({x} : Set G)) ∧
        OddOrder.GroupTheory.IsPiElement (kappa M) x') := by
  classical
  rw [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe] at hx
  obtain ⟨hxMσ, hx1⟩ := hx
  -- `x` and `x'` commute.
  have hcomm : x * x' = x' * x := (Subgroup.mem_centralizer_iff.mp hx'cent) x (Set.mem_singleton x)
  rcases sigma_diagnostic hG D hM ⟨hxMσ, hx1⟩ hx'M hx'1 hx'cent hx'sigma with
    ⟨hκ, _⟩ | ⟨_, hlen', huniq⟩
  · -- **κ branch**.
    refine Or.inr ⟨?_, ⟨hM, hxMσ⟩, ?_, ?_⟩
    · exact length_one_of_isPiElement_sigma hG D hM hx1 (isPiElement_sigma_of_mem_Msigma hxMσ)
    · exact Set.mem_sdiff_singleton.mpr ⟨Subgroup.mem_inf.mpr ⟨hx'M, hx'cent⟩, hx'1⟩
    · intro p hp
      refine hκ p ?_
      change p ∈ (Nat.card ↥(Subgroup.closure ({x'} : Set G))).primeFactors
      rwa [show Nat.card ↥(Subgroup.closure ({x'} : Set G)) = orderOf x' from by
        rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]]
  · -- **signalizer branch** (τ₂ case): `y = x'`, `x'⁻¹ g = x ∈ R(x')`.
    refine Or.inl ⟨x', hlen', ?_⟩
    have hxx' : x'⁻¹ * (x * x') = x := by
      rw [hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hxx']
    -- `𝓜_σ(x')` is nonempty (from `ℓ_σ(x') = 1`).
    have hne' : (maximalSigmaSubgroupsOfElement x').Nonempty := ((D.length_one_iff x').mp hlen').2
    -- `|𝓜_σ(x')| > 1`.
    have hgt' : 1 < (maximalSigmaSubgroupsOfElement x').ncard := by
      rcases lt_or_ge 1 (maximalSigmaSubgroupsOfElement x').ncard with h | h
      · exact h
      · exfalso
        have hcard1 : (maximalSigmaSubgroupsOfElement x').ncard = 1 :=
          le_antisymm h ((Set.ncard_pos (Set.toFinite _)).mpr hne')
        obtain ⟨N₀, hN₀⟩ := hne'
        have hCx'N₀ : Subgroup.centralizer ({x'} : Set G) ≤ N₀ :=
          centralizer_le_of_maximalSigma_ncard_eq_one hG hcard1 hN₀
        have hN₀M : N₀ = M := by
          have hmem : N₀ ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x'} : Set G)) :=
            ⟨mem_maximalSubgroups.mp hN₀.1, hCx'N₀⟩
          rw [huniq, Set.mem_singleton_iff] at hmem; exact hmem
        have hx'σM : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x' :=
          isPiElement_sigma_of_mem_Msigma (hN₀M ▸ hN₀.2)
        obtain ⟨p, hp⟩ : (orderOf x').primeFactors.Nonempty :=
          Nat.nonempty_primeFactors.mpr (by
            have h1 : orderOf x' ≠ 1 := by simpa [orderOf_eq_one_iff] using hx'1
            have h0 : 0 < orderOf x' := orderOf_pos x'
            omega)
        refine hx'sigma p ?_ (hx'σM p hp)
        change p ∈ (Nat.card ↥(Subgroup.closure ({x'} : Set G))).primeFactors
        rwa [show Nat.card ↥(Subgroup.closure ({x'} : Set G)) = orderOf x' from by
          rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]]
    -- the neighbour `N = N(x')` of Theorem 14.4, with `R(x') = N_σ ∩ C_G(x')`.
    obtain ⟨N, hNmax, hCx'N, hRsub_eq, _, _⟩ := exists_neighbor_eq_Rsub hG D hlen' hgt'
    have hNM : N = M := by
      have hmem : N ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x'} : Set G)) :=
        ⟨mem_maximalSubgroups.mp hNmax, hCx'N⟩
      rw [huniq, Set.mem_singleton_iff] at hmem; exact hmem
    rw [hRsub_eq, hNM]
    refine Subgroup.mem_inf.mpr ⟨hxMσ, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz; rw [Set.mem_singleton_iff.mp hz, ← hcomm]

/-- **Coq `s'g`, the `g ∈ M` corollary** — the σ-decomposition dichotomy for an element contained
in a maximal subgroup.  If `g ∈ M` (maximal) and the `σ(M)`-part of `g` is nontrivial, then `g`
lands in the signalizer branch or the κ branch.  Combines `mem_Msigma_of_isPiElement_sigma_of_mem`
(to see the `σ(M)`-part `x ∈ M_σ^#`) with `signalizer_coset_or_kappa_of_sigmaSharp` (applied to `x`
and the `σ(M)′`-part `x' = x⁻¹g`).  This is the form consumed by the full BG Lemma 14.6 assembly. -/
theorem branchA_or_branchB_of_mem_maximal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {g : G} (hg : g ∈ M)
    (hne : sigmaPart M g ≠ 1) :
    (∃ y, D.length y = 1 ∧ y⁻¹ * g ∈ Rsub hG D y)
    ∨ (∃ y, D.length y = 1 ∧ ∃ N, N ∈ maximalSigmaSubgroupsOfElement y ∧
        y⁻¹ * g ∈ sharpSubgroup (N ⊓ Subgroup.centralizer ({y} : Set G)) ∧
        OddOrder.GroupTheory.IsPiElement (kappa N) (y⁻¹ * g)) := by
  classical
  simp only [sigmaPart] at hne
  obtain ⟨b, hbmul, hbcomm, hxπ, hbπ, hxz, hbz⟩ := piPart_spec (OddOrder.BG.Ch3.S10.sigma M) g
  set x := piPart (OddOrder.BG.Ch3.S10.sigma M) g with hxdef
  have hx1 : x ≠ 1 := hne
  have hxM : x ∈ M := Subgroup.zpowers_le.mpr hg hxz
  have hbM : b ∈ M := Subgroup.zpowers_le.mpr hg hbz
  have hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M :=
    mem_Msigma_of_isPiElement_sigma_of_mem hG hM hxM hxπ
  have hxsharp : x ∈ sigmaSharp M := by
    rw [sigmaSharp, sharpSubgroup]; exact Set.mem_sdiff_singleton.mpr ⟨hxMσ, hx1⟩
  have hxg : x⁻¹ * g = b := by rw [← hbmul, ← mul_assoc, inv_mul_cancel, one_mul]
  have hlen : D.length x = 1 := length_one_of_isPiElement_sigma hG D hM hx1 hxπ
  by_cases hb1 : b = 1
  · refine Or.inl ⟨x, hlen, ?_⟩
    rw [hxg, hb1]; exact Subgroup.one_mem _
  · have hbcent : b ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]; intro z hz
      rw [Set.mem_singleton_iff.mp hz]; exact hbcomm
    have hbσ : ∀ p ∈ piSet (Subgroup.closure {b}), p ∉ OddOrder.BG.Ch3.S10.sigma M := by
      intro p hp
      refine hbπ p ?_
      rwa [show orderOf b = Nat.card ↥(Subgroup.closure ({b} : Set G)) from by
        rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]]
    rcases signalizer_coset_or_kappa_of_sigmaSharp hG D hM hxsharp hbM hb1 hbcent hbσ with hA | hB
    · obtain ⟨y, hyl, hyr⟩ := hA
      exact Or.inl ⟨y, hyl, by rwa [hbmul] at hyr⟩
    · obtain ⟨hxl, hMmem, hbsharp, hbκ⟩ := hB
      exact Or.inr ⟨x, hxl, M, hMmem, by rw [hxg]; exact hbsharp, by rw [hxg]; exact hbκ⟩

/-- **BG Lemma 14.6** (`sigma_decomposition_dichotomy`, Coq `BGsection14`:1189): every `g ≠ 1`
satisfies (at least) one of the two branches of the σ-decomposition dichotomy: the **signalizer
branch** (`∃ y, ℓ_σ(y) = 1 ∧ y⁻¹g ∈ R(y)`) or the **κ branch** (`∃ y, ℓ_σ(y) = 1 ∧ ∃ N ∈ 𝓜_σ(y),
y⁻¹g ∈ (C_N[y])^#` with `y⁻¹g` a `κ(N)`-element).

Proof (Coq's second half): assume both branches fail.  Then `branchA_or_branchB_of_mem_maximal`
gives **`s'g`**: every `g ∈ M` (maximal) has trivial `σ(M)`-part.  Pick `x = (g)_{σ(M₀)} ≠ 1` from
the nonempty σ-decomposition; conjugate `M₀` so that `x ∈ M_σ` (preserving `σ(M) = σ(M₀)`, hence
`x = (g)_{σ(M)}`).  Then `g ∉ M` (else `s'g` kills `x`), so `|𝓜_σ(x)| > 1`
(`centralizer_le_of_maximalSigma_ncard_eq_one`).  The neighbour `N = N(x)` of Theorem 14.4 has
`C_G(x) ≤ N` and `M ∩ N` a Hall `σ(N)′`-subgroup of `N` (complement of `N_σ`); since `g` is a
`σ(N)′`-element (`s'g` for `N`), `⟨g⟩` conjugates into `M ∩ N ⊆ M`
(`exists_conj_smul_le_of_isHall`),
so `(g^w)_{σ(M)} = (x)^w = 1` by `s'g`, forcing `x = 1` — a contradiction. -/
theorem sigma_decomposition_dichotomy [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {g : G} (hg : g ≠ 1) :
    (∃ y, D.length y = 1 ∧ y⁻¹ * g ∈ Rsub hG D y)
    ∨ (∃ y, D.length y = 1 ∧ ∃ N, N ∈ maximalSigmaSubgroupsOfElement y ∧
        y⁻¹ * g ∈ sharpSubgroup (N ⊓ Subgroup.centralizer ({y} : Set G)) ∧
        OddOrder.GroupTheory.IsPiElement (kappa N) (y⁻¹ * g)) := by
  classical
  by_contra hcon
  have hnA : ¬ (∃ y, D.length y = 1 ∧ y⁻¹ * g ∈ Rsub hG D y) := fun h => hcon (Or.inl h)
  have hnB : ¬ (∃ y, D.length y = 1 ∧ ∃ N, N ∈ maximalSigmaSubgroupsOfElement y ∧
      y⁻¹ * g ∈ sharpSubgroup (N ⊓ Subgroup.centralizer ({y} : Set G)) ∧
      OddOrder.GroupTheory.IsPiElement (kappa N) (y⁻¹ * g)) := fun h => hcon (Or.inr h)
  -- **`s'g`**: `g ∈ M` (maximal) ⟹ `σ(M)`-part of `g` is trivial.
  have hsg : ∀ M, M ∈ maximalSubgroups G → g ∈ M → sigmaPart M g = 1 := by
    intro M hM hgM
    by_contra hne
    rcases branchA_or_branchB_of_mem_maximal hG D hM hgM hne with hA | hB
    · exact hnA hA
    · exact hnB hB
  -- σ-decomposition is nonempty; pick `x = (g)_{σ(M₀)} ≠ 1`.
  have hlen0 : sigmaLength g ≠ 0 := fun h => hg ((sigmaLength_eq_zero_iff hG g).mp h)
  obtain ⟨x, hxmem⟩ : (sigmaDecomposition g).Nonempty := by
    rw [sigmaLength] at hlen0; exact Set.nonempty_of_ncard_ne_zero hlen0
  rw [sigmaDecomposition, Set.mem_sdiff, Set.mem_singleton_iff] at hxmem
  obtain ⟨⟨M₀, hM₀, hxeq⟩, hx1⟩ := hxmem
  have hxπ₀ : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M₀) x :=
    hxeq ▸ isPiElement_piPart (OddOrder.BG.Ch3.S10.sigma M₀) g
  have hxz : x ∈ Subgroup.zpowers g := hxeq ▸ piPart_mem_zpowers (OddOrder.BG.Ch3.S10.sigma M₀) g
  have hxlen : D.length x = 1 := length_one_of_isPiElement_sigma hG D hM₀ hx1 hxπ₀
  -- **WLOG `x ∈ M_σ`**: conjugate `M₀` into a maximal `M` containing `x` in its `σ`-core.
  have hclosne : Subgroup.closure ({x} : Set G) ≠ ⊥ := fun h =>
    hx1 (Subgroup.mem_bot.mp (h ▸ Subgroup.subset_closure (Set.mem_singleton x)))
  have hclt : Subgroup.closure ({x} : Set G) < ⊤ := by
    refine lt_top_iff_ne_top.mpr (fun htop => hG.notSolvable
        (Group.isSolvable_of_comm fun a b => ?_))
    have hmem : ∀ y : G, y ∈ Subgroup.zpowers x := fun y => by
      rw [Subgroup.zpowers_eq_closure, htop]; exact Subgroup.mem_top y
    obtain ⟨m, rfl⟩ := hmem a; obtain ⟨n, rfl⟩ := hmem b
    rw [← zpow_add, ← zpow_add, Int.add_comm]
  have hxpisub : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma M₀)
      (Subgroup.closure ({x} : Set G)) := fun p hp =>
    hxπ₀ p (by rwa [← Subgroup.zpowers_eq_closure, Nat.card_zpowers] at hp)
  obtain ⟨c, hc⟩ := sigma_subgroup_conj_into_Msigma_general hG hM₀ hclosne hclt hxpisub
    (fun hN hnc => sigma_disjoint_of_nonconjugate hG hM₀ hN hnc)
  set M := MulAut.conj c⁻¹ • M₀ with hMdef
  have hMmax : M ∈ maximalSubgroups G :=
    mem_maximalSubgroups_of_isConjugateSubgroup hM₀ ⟨c⁻¹, rfl⟩
  have hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M := by
    rw [hMdef, Msigma_conj_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hcx : MulAut.conj c • x ∈ OddOrder.BG.Ch3.S10.Msigma M₀ :=
      hc (Subgroup.smul_mem_pointwise_smul x (MulAut.conj c) _
        (Subgroup.subset_closure (Set.mem_singleton x)))
    rwa [show (MulAut.conj c⁻¹)⁻¹ • x = MulAut.conj c • x from by rw [← map_inv, inv_inv]]
  have hσM : OddOrder.BG.Ch3.S10.sigma M = OddOrder.BG.Ch3.S10.sigma M₀ := by
    rw [hMdef, sigma_conj_smul_eq]
  have hxsig : sigmaPart M g = x := by rw [sigmaPart, hσM, ← sigmaPart, ← hxeq]
  -- `g ∉ M`, `g ∈ C_G(x)`, `M ∈ 𝓜_σ(x)`.
  have hnotMg : g ∉ M := fun hgM => hx1 (hxsig ▸ hsg M hMmax hgM)
  have hcxg : g ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]; intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    obtain ⟨k, hk⟩ := hxz; rw [← hk]; exact Commute.zpow_left (Commute.refl g) k
  have hMmemx : M ∈ maximalSigmaSubgroupsOfElement x := ⟨hMmax, hxMσ⟩
  -- `|𝓜_σ(x)| > 1` (else `C_G(x) ≤ M`, so `g ∈ M`).
  have hgt : 1 < (maximalSigmaSubgroupsOfElement x).ncard := by
    by_contra hle
    push Not at hle
    have hcard1 : (maximalSigmaSubgroupsOfElement x).ncard = 1 :=
      le_antisymm hle ((Set.ncard_pos (Set.toFinite _)).mpr ⟨M, hMmemx⟩)
    exact hnotMg ((centralizer_le_of_maximalSigma_ncard_eq_one hG hcard1 hMmemx) hcxg)
  -- Neighbour `N = N(x)`: `C_G(x) ≤ N`, and `M ∩ N` complements `N_σ` in `N`.
  obtain ⟨N, hNmax, hCxN, -, -, hcompl⟩ := exists_neighbor_eq_Rsub hG D hxlen hgt
  have hcomplM := hcompl M hMmemx
  have hgN : g ∈ N := hCxN hcxg
  have hsigNg : sigmaPart N g = 1 := hsg N hNmax hgN
  have hsN'g : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma N)ᶜ g :=
    isPiElement_compl_of_piPart_eq_one hsigNg
  -- `M ∩ N` is a Hall `σ(N)′`-subgroup of `N`.
  have hMsHall := OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hNmax
  have hMNhall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma N)ᶜ ((M ⊓ N).subgroupOf N) := by
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · rw [(hcomplM.symm.index_eq_card).symm] at hp
      exact hMsHall.index_no_pi p hp
    · rw [hcomplM.index_eq_card] at hp
      rw [Set.mem_compl_iff, not_not]
      exact hMsHall.primeFactors_card_subset p hp
  -- `⟨g⟩` is a `σ(N)′`-subgroup of `N`.
  have hgN_le : Subgroup.zpowers g ≤ N := Subgroup.zpowers_le.mpr hgN
  have hgpi : Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma N)ᶜ
      ((Subgroup.zpowers g).subgroupOf N) := by
    intro p hp
    refine hsN'g p ?_
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hgN_le).toEquiv, Nat.card_zpowers] at hp
  -- Conjugate `⟨g⟩` into `M ∩ N`, so a conjugate of `g` lies in `M`.
  obtain ⟨w, _, hwle⟩ :=
    exists_conj_smul_le_of_isHall hG hNmax (inf_le_right) hMNhall hgN_le hgpi
  have hwg : MulAut.conj w • g ∈ M := by
    have hmem : MulAut.conj w • g ∈ M ⊓ N :=
      hwle (Subgroup.smul_mem_pointwise_smul g (MulAut.conj w) _ (Subgroup.mem_zpowers g))
    exact (Subgroup.mem_inf.mp hmem).1
  -- `g ∈ Mʷ⁻¹` (a maximal conjugate of `M`); `s'g` there gives `(g)_{σ(M)} = x = 1`.
  have hM' : MulAut.conj w⁻¹ • M ∈ maximalSubgroups G :=
    mem_maximalSubgroups_of_isConjugateSubgroup hMmax ⟨w⁻¹, rfl⟩
  have hgM' : g ∈ MulAut.conj w⁻¹ • M := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      show (MulAut.conj w⁻¹)⁻¹ • g = MulAut.conj w • g from by rw [← map_inv, inv_inv]]
    exact hwg
  have hfinal : sigmaPart (MulAut.conj w⁻¹ • M) g = 1 := hsg _ hM' hgM'
  rw [sigmaPart, sigma_conj_smul_eq, ← sigmaPart, hxsig] at hfinal
  exact hx1 hfinal

/-- **BG Corollary 14.9, the type-I cover (faithful form)**: when every maximal subgroup is of
type `F` (`κ(M) = ∅`, so there is no exceptional `κ` branch), every nonidentity `g` lies in some
`𝒞_G(M̃)`.  Immediate from `sigma_decomposition_dichotomy`: the signalizer branch gives
`y` with `ℓ_σ(y) = 1` and `y⁻¹g ∈ R(y)`, so `g ∈ M̃(M)` (`mem_Mtilde_of_mem_coset`, with `M` the
maximal carrying `y ∈ M_σ^#`); the `κ` branch is impossible because a nonidentity `κ(N)`-element
would force `κ(N) ≠ ∅`, contradicting `IsTypeF N`.

**Faithfulness note:** without the all-type-`F` hypothesis the statement is *false* — `κ`-branch
elements lie in the exceptional `𝒞_G(Ẑ)` piece and in no `𝒞_G(M̃)` (the dichotomy is an XOR).  The
cover uses the canonical `genuineSigmaDecomposition`, matching `bgTheoremE_cover_data`'s `cover`. -/
theorem exists_mem_conjClassSet_Mtilde_of_ne_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hall : ∀ M ∈ maximalSubgroups G, IsTypeF M) {g : G} (hg : g ≠ 1) :
    ∃ M ∈ maximalSubgroups G,
      g ∈ conjClassSet (Mtilde hG (genuineSigmaDecomposition hG) M) := by
  set D := genuineSigmaDecomposition hG with hD
  rcases sigma_decomposition_dichotomy hG D hg with
    ⟨y, hyl, hyr⟩ | ⟨y, hyl, N, hNmem, hsharp, hκ⟩
  · -- **Signalizer branch**: `y⁻¹g ∈ R(y)` puts `g` in `M̃(M)` for the maximal `M ∋ y` in `M_σ`.
    obtain ⟨hy1, M, hMmax, hyMσ⟩ := (D.length_one_iff y).mp hyl
    exact ⟨M, hMmax, subset_conjClassSet
      (mem_Mtilde_of_mem_coset hG D (Set.mem_sdiff_singleton.mpr ⟨hyMσ, hy1⟩) hyr)⟩
  · -- **κ branch**: impossible under all-type-`F` (`κ(N) = ∅`).
    exfalso
    have hN1 : y⁻¹ * g ≠ 1 := (Set.mem_sdiff_singleton.mp hsharp).2
    obtain ⟨p, hp⟩ : (orderOf (y⁻¹ * g)).primeFactors.Nonempty :=
      Nat.nonempty_primeFactors.mpr (by
        have h1 : orderOf (y⁻¹ * g) ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
        have h0 : 0 < orderOf (y⁻¹ * g) := orderOf_pos _
        omega)
    have hpκ : p ∈ kappa N := hκ p hp
    rw [hall N hNmem.1] at hpκ
    exact (Set.mem_empty_iff_false p).mp hpκ

/-- `|L_σ^#| = |M_σ^#|` whenever `L` is a conjugate of `M`: conjugation is an order-preserving
bijection, so `|L_σ| = |M_σ|` and removing the (fixed) identity preserves the count. -/
theorem sharpSubgroup_Msigma_ncard_of_isConjugate [Finite G] {M L : Subgroup G}
    (h : IsConjugateSubgroup M L) :
    (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma L)).ncard
      = (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma M)).ncard := by
  have key : ∀ H : Subgroup G, (sharpSubgroup H).ncard = Nat.card ↥H - 1 := fun H => by
    have hc : Nat.card ↥H = (H : Set G).ncard := by
      rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
    rw [sharpSubgroup, Set.ncard_sdiff (Set.singleton_subset_iff.mpr H.one_mem),
      Set.ncard_singleton, hc]
  rw [key, key]
  congr 1
  obtain ⟨a, rfl⟩ := h
  rw [Msigma_conj_smul, OddOrder.BG.Ch3.S10.conjSmul_eq_map]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj a).injective).toEquiv).symm

/-- **All members of `𝓜_σ(x)` are conjugate** (BG Theorem 14.4 sharp transitivity): `R(x)` acts
transitively on `𝓜_σ(x)`, so any two `σ`-maximals of a `σ`-length-one element are conjugate.  In
the single-maximal case `𝓜_σ(x)` is a singleton, so the two coincide. -/
theorem isConjugateSubgroup_of_mem_maximalSigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G) {x : G}
    (hlen : D.length x = 1) {L L' : Subgroup G}
    (hL : L ∈ maximalSigmaSubgroupsOfElement x) (hL' : L' ∈ maximalSigmaSubgroupsOfElement x) :
    IsConjugateSubgroup L L' := by
  classical
  have hx : x ≠ 1 := ((D.length_one_iff x).mp hlen).1
  by_cases hgt : 1 < (maximalSigmaSubgroupsOfElement x).ncard
  · have spec := ((sigmaLength_one_centralizer_structure hG D hx hlen).2 hgt).exists.choose_spec
    obtain ⟨r, hr, -⟩ := (spec.2.2.2.2.2.2 L hL).2.2.2 L' hL'
    exact ⟨r, hr.2⟩
  · have hne : (maximalSigmaSubgroupsOfElement x).Nonempty := ((D.length_one_iff x).mp hlen).2
    have hfin : (maximalSigmaSubgroupsOfElement x).Finite := Set.toFinite _
    have h1 : (maximalSigmaSubgroupsOfElement x).ncard = 1 := by
      have hpos : 0 < (maximalSigmaSubgroupsOfElement x).ncard := by
        rw [Set.ncard_pos hfin]; exact hne
      omega
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
    rw [ha, Set.mem_singleton_iff] at hL hL'
    rw [hL, hL']

/-- **Sharp transitivity, `C_G(x)`-witness form** (BG Theorem 14.4, strengthening
`isConjugateSubgroup_of_mem_maximalSigma`): for a `σ`-length-one `x`, `R(x) = N_σ ∩ C_G(x)` acts
transitively on `𝓜_σ(x)`, so any two `σ`-maximals `L, L'` of `x` satisfy `L' = L^c` for some
`c ∈ C_G(x)` — not merely some `c ∈ G`.  This `C_G(x)`-conjugacy is the form BG Corollary 15.3(b)
consumes (after `N_G(M) = M` it forces the conjugator into `M`). -/
theorem exists_conj_centralizer_of_mem_maximalSigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G) {x : G}
    (hlen : D.length x = 1) {L L' : Subgroup G}
    (hL : L ∈ maximalSigmaSubgroupsOfElement x) (hL' : L' ∈ maximalSigmaSubgroupsOfElement x) :
    ∃ c ∈ Subgroup.centralizer ({x} : Set G), MulAut.conj c • L = L' := by
  classical
  have hx : x ≠ 1 := ((D.length_one_iff x).mp hlen).1
  by_cases hgt : 1 < (maximalSigmaSubgroupsOfElement x).ncard
  · have spec := ((sigmaLength_one_centralizer_structure hG D hx hlen).2 hgt).exists.choose_spec
    obtain ⟨r, hr, -⟩ := (spec.2.2.2.2.2.2 L hL).2.2.2 L' hL'
    exact ⟨r, (Subgroup.mem_inf.mp hr.1).2, hr.2⟩
  · have hne : (maximalSigmaSubgroupsOfElement x).Nonempty := ((D.length_one_iff x).mp hlen).2
    have h1 : (maximalSigmaSubgroupsOfElement x).ncard = 1 := by
      have hpos : 0 < (maximalSigmaSubgroupsOfElement x).ncard := by
        rw [Set.ncard_pos (Set.toFinite _)]; exact hne
      omega
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
    rw [ha, Set.mem_singleton_iff] at hL hL'
    exact ⟨1, Subgroup.one_mem _, by rw [hL, hL', map_one, one_smul]⟩

/-- **BG Corollary 15.3(b), `hconj` input** (the `§14.4` half): for a maximal `M` and
`H ≤ M_σ`, any two elements `x, y ∈ H` that are conjugate in `G` are already conjugate by an
element of `M`.  (`N_M(H)`-control is then obtained from this via the Frattini argument in the
`H ⋬ M` case.)

Proof.  If `x = 1` then `y = 1` and `m = 1` works.  Otherwise `x ∈ M_σ` has `σ`-length one, with
`M ∈ 𝓜_σ(x)` and `M^{g⁻¹} ∈ 𝓜_σ(x)` (as `x = g⁻¹yg ∈ (M_σ)^{g⁻¹}`).  Theorem 14.4's sharp
transitivity (`exists_conj_centralizer_of_mem_maximalSigma`) yields `c ∈ C_G(x)` with
`M^{cg⁻¹} = M`, so `cg⁻¹ ∈ N_G(M) = M`; then `m = (cg⁻¹)⁻¹ = gc⁻¹ ∈ M` and
`m x m⁻¹ = g(c⁻¹xc)g⁻¹ = gxg⁻¹ = y`. -/
theorem mf_hall_conj_realized_in_M [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G) {M H : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hHMσ : H ≤ OddOrder.BG.Ch3.S10.Msigma M) :
    ∀ x ∈ H, ∀ y ∈ H, ∀ g : G, y = g * x * g⁻¹ → ∃ m ∈ M, y = m * x * m⁻¹ := by
  classical
  intro x hx y hy g hyg
  by_cases hx1 : x = 1
  · exact ⟨1, M.one_mem, by rw [hyg, hx1]; group⟩
  · have hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M := hHMσ hx
    have hMmem : M ∈ maximalSigmaSubgroupsOfElement x := ⟨hM, hxMσ⟩
    have hgM_max : MulAut.conj g⁻¹ • M ∈ maximalSubgroups G :=
      mem_maximalSubgroups_of_isConjugateSubgroup hM ⟨g⁻¹, rfl⟩
    have hxgMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma (MulAut.conj g⁻¹ • M) := by
      rw [Msigma_conj_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have heq : (MulAut.conj g⁻¹)⁻¹ • x = y := by
        rw [map_inv, inv_inv, MulAut.smul_def, MulAut.conj_apply]; exact hyg.symm
      rw [heq]; exact hHMσ hy
    have hgMmem : MulAut.conj g⁻¹ • M ∈ maximalSigmaSubgroupsOfElement x := ⟨hgM_max, hxgMσ⟩
    have hlen : D.length x = 1 := (D.length_one_iff x).mpr ⟨hx1, ⟨M, hMmem⟩⟩
    obtain ⟨c, hcC, hcconj⟩ :=
      exists_conj_centralizer_of_mem_maximalSigma hG D hlen hgMmem hMmem
    have hcg : MulAut.conj (c * g⁻¹) • M = M := by rw [map_mul, mul_smul]; exact hcconj
    have hcgM : c * g⁻¹ ∈ M := by
      rw [← normalizer_eq_self_of_mem_maximalSubgroups hG hM]
      exact mem_normalizer_of_conj_smul_eq_self hcg
    have hcomm : x * c = c * x := (Subgroup.mem_centralizer_iff.mp hcC) x (Set.mem_singleton x)
    have hcx' : c⁻¹ * x * c = x := by rw [mul_assoc, hcomm, inv_mul_cancel_left]
    refine ⟨(c * g⁻¹)⁻¹, M.inv_mem hcgM, ?_⟩
    calc y = g * x * g⁻¹ := hyg
      _ = g * (c⁻¹ * x * c) * g⁻¹ := by rw [hcx']
      _ = (c * g⁻¹)⁻¹ * x * ((c * g⁻¹)⁻¹)⁻¹ := by group

/-- A conjugacy-saturation `𝒞_G(M_σ^#)` element is nonidentity (it is conjugate to some
`t ∈ M_σ^#`, and conjugation fixes the identity). -/
theorem ne_one_of_mem_sigmaConjugacySaturation {M : Subgroup G} {x : G}
    (hx : x ∈ sigmaConjugacySaturation M) : x ≠ 1 := by
  rw [sigmaConjugacySaturation, sigmaSharp, mem_conjClassSet] at hx
  obtain ⟨t, ht, g, hgt⟩ := hx
  rw [sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe] at ht
  rw [← hgt]; intro h
  have e : g * t * g⁻¹ = g * 1 * g⁻¹ := by rw [h]; group
  exact ht.2 (mul_left_cancel (mul_right_cancel e))

/-- Every `x ∈ 𝒞_G(M_σ^#)` is a `σ`-length-one element with a conjugate of `M` among its
`σ`-maximals (`x = t^a` with `t ∈ M_σ^#` puts `x ∈ (M^a)_σ`).  This routes `Rsub_ncard_eq`
(needs `ℓ_σ(x) = 1`) and the fibre identification of Lemma 14.5(c). -/
theorem length_one_of_mem_sigmaConjugacySaturation [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {x : G}
    (hx : x ∈ sigmaConjugacySaturation M) :
    D.length x = 1 ∧ ∃ a : G, MulAut.conj a • M ∈ maximalSigmaSubgroupsOfElement x := by
  classical
  rw [sigmaConjugacySaturation, sigmaSharp, mem_conjClassSet] at hx
  obtain ⟨t, ht, g, hgt⟩ := hx
  rw [sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe] at ht
  obtain ⟨htM, ht1⟩ := ht
  have hx1 : x ≠ 1 := by
    rw [← hgt]; intro h
    have e : g * t * g⁻¹ = g * 1 * g⁻¹ := by rw [h]; group
    exact ht1 (mul_left_cancel (mul_right_cancel e))
  have hmem : MulAut.conj g • M ∈ maximalSigmaSubgroupsOfElement x := by
    refine ⟨mem_maximalSubgroups_of_isConjugateSubgroup hM ⟨g, rfl⟩, ?_⟩
    rw [Msigma_conj_smul, ← hgt, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hcalc : (MulAut.conj g)⁻¹ • (g * t * g⁻¹) = t := by
      rw [← map_inv (MulAut.conj) g, MulAut.smul_def, MulAut.conj_apply, inv_inv]; group
    rw [hcalc]; exact htM
  exact ⟨(D.length_one_iff x).mpr ⟨hx1, ⟨MulAut.conj g • M, hmem⟩⟩, g, hmem⟩

/-- **Fibre over `x`** (BG 14.5(c) double count): for `x ∈ 𝒞_G(M_σ^#)`, the `σ`-maximals `𝓜_σ(x)`
are exactly the conjugates `L` of `M` with `x ∈ L_σ`.  (All of `𝓜_σ(x)` are conjugate by sharp
transitivity, and one of them is a conjugate of `M`.) -/
theorem maximalSigma_eq_conj_of_mem_saturation [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {x : G}
    (hx : x ∈ sigmaConjugacySaturation M) :
    maximalSigmaSubgroupsOfElement x
      = {L | IsConjugateSubgroup M L ∧ x ∈ OddOrder.BG.Ch3.S10.Msigma L} := by
  obtain ⟨hlen, a, hL0⟩ := length_one_of_mem_sigmaConjugacySaturation hG D hM hx
  ext L
  refine ⟨fun hL => ⟨IsConjugateSubgroup.trans ⟨a, rfl⟩
      (isConjugateSubgroup_of_mem_maximalSigma hG D hlen hL0 hL), hL.2⟩,
    fun hLc => ⟨mem_maximalSubgroups_of_isConjugateSubgroup hM hLc.1, hLc.2⟩⟩

/-- **Fibre over `L`** (BG 14.5(c) double count): for `L` conjugate to `M`, the saturated
elements lying in `L_σ` are exactly `L_σ^#`. -/
theorem saturation_inter_Msigma_eq_sharp [Finite G] {M L : Subgroup G}
    (hconj : IsConjugateSubgroup M L) :
    {x | x ∈ sigmaConjugacySaturation M ∧ x ∈ OddOrder.BG.Ch3.S10.Msigma L}
      = sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma L) := by
  ext x
  rw [sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe, Set.mem_ofPred_eq]
  refine ⟨fun hx => ⟨hx.2, ne_one_of_mem_sigmaConjugacySaturation hx.1⟩, fun hx => ⟨?_, hx.1⟩⟩
  obtain ⟨a, rfl⟩ := hconj
  rw [sigmaConjugacySaturation, sigmaSharp, mem_conjClassSet]
  rw [Msigma_conj_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
  set t := (MulAut.conj a)⁻¹ • x with htdef
  have hax : a * t * a⁻¹ = x := by
    rw [htdef, ← map_inv (MulAut.conj) a, MulAut.smul_def, MulAut.conj_apply, inv_inv]; group
  refine ⟨t, ?_, a, hax⟩
  rw [sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe]
  exact ⟨hx.1, fun ht1 => hx.2 (by rw [← hax, ht1]; group)⟩

/-- **BG Lemma 14.5(c), the double count** (mmd L3933-3940): summing `|R(x)|` over the conjugacy
saturation `𝒞_G(M_σ^#)` gives `|M_σ^#|·[G:M]`.  Counts pairs `(x, L)` with `L` a conjugate of `M`
and `x ∈ L_σ^#` two ways — by `x` (each contributes `|𝓜_σ(x)| = |R(x)|`, sharp transitivity) and
by `L` (each of the `[G:M]` conjugates contributes `|L_σ^#| = |M_σ^#|`). -/
theorem sigmaSaturation_Rsub_count [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    ∑ x ∈ (Set.toFinite (sigmaConjugacySaturation M)).toFinset, Nat.card ↥(Rsub hG D x)
      = (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma M)).ncard * M.index := by
  classical
  set Sfin := (Set.toFinite (sigmaConjugacySaturation M)).toFinset with hSf
  set Conjfin := (Set.toFinite {L : Subgroup G | IsConjugateSubgroup M L}).toFinset with hCf
  -- Step 1: rewrite each `|R(x)|` as the `x`-fibre count over conjugates of `M`.
  have step1 : ∀ x ∈ Sfin, Nat.card ↥(Rsub hG D x)
      = ∑ L ∈ Conjfin, (if x ∈ OddOrder.BG.Ch3.S10.Msigma L then 1 else 0) := by
    intro x hxfin
    have hxS : x ∈ sigmaConjugacySaturation M := by
      rw [hSf, Set.Finite.mem_toFinset] at hxfin; exact hxfin
    have hlen := (length_one_of_mem_sigmaConjugacySaturation hG D hM hxS).1
    have hcoe : (↑(Conjfin.filter (fun L => x ∈ OddOrder.BG.Ch3.S10.Msigma L)) : Set (Subgroup G))
        = maximalSigmaSubgroupsOfElement x := by
      rw [maximalSigma_eq_conj_of_mem_saturation hG D hM hxS]
      ext L
      simp only [Finset.mem_coe, Finset.mem_filter, hCf, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    rw [Rsub_ncard_eq hG D hlen, ← hcoe, Set.ncard_coe_finset, Finset.card_filter]
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  -- Step 3: each `L`-fibre is `|L_σ^#| = |M_σ^#|`, over the `[G:M]` conjugates of `M`.
  have step3 : ∀ L ∈ Conjfin,
      (∑ x ∈ Sfin, (if x ∈ OddOrder.BG.Ch3.S10.Msigma L then 1 else 0))
      = (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma M)).ncard := by
    intro L hLfin
    have hLconj : IsConjugateSubgroup M L := by
      rw [hCf, Set.Finite.mem_toFinset] at hLfin; exact hLfin
    have hcoe : (↑(Sfin.filter (fun x => x ∈ OddOrder.BG.Ch3.S10.Msigma L)) : Set G)
        = sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma L) := by
      rw [← saturation_inter_Msigma_eq_sharp hLconj]
      ext y
      simp only [Finset.mem_coe, Finset.mem_filter, hSf, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    rw [← Finset.card_filter, ← Set.ncard_coe_finset, hcoe,
      sharpSubgroup_Msigma_ncard_of_isConjugate hLconj]
  rw [Finset.sum_congr rfl step3, Finset.sum_const, smul_eq_mul]
  have hConjcard : Conjfin.card = M.index := by
    rw [hCf, ← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
    have hrange : {L : Subgroup G | IsConjugateSubgroup M L}
        = Set.range (fun g : G => MulAut.conj g • M) := rfl
    rw [hrange, ncard_conjugates_eq_index_of_normalizer_eq_self
      (normalizer_eq_self_of_mem_maximalSubgroups hG hM)]
  rw [hConjcard]
  exact Nat.mul_comm _ _

/-- The chosen neighbour `N(x)` of Theorem 14.4 (multi-maximal case), packaged with the
**singleton characterisation** `𝓜(C_G(x)) = {N(x)}` (BG mmd L3906).  The singleton clause is
Corollary 14.3's `maximalContaining_centralizer_eq_singleton_of_tau2_element` applied to the
`∃!`-spec data; it pins `N(x)` as the *unique* maximal subgroup containing `C_G(x)`, which is
exactly what makes `R(x)` conjugation-equivariant (`Rsub_conj`). -/
theorem exists_neighbor_Rsub_singleton [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {x : G} (hlen : D.length x = 1)
    (hgt : 1 < (maximalSigmaSubgroupsOfElement x).ncard) :
    ∃ N : Subgroup G, N ∈ maximalSubgroups G ∧ Subgroup.centralizer ({x} : Set G) ≤ N ∧
      Rsub hG D x = OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G) ∧
      maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {N} := by
  have hx : x ≠ 1 := ((D.length_one_iff x).mp hlen).1
  set N := ((sigmaLength_one_centralizer_structure hG D hx hlen).2 hgt).exists.choose with hNdef
  have spec := ((sigmaLength_one_centralizer_structure hG D hx hlen).2 hgt).exists.choose_spec
  have hxN : x ∈ N := spec.2.1 (Subgroup.mem_centralizer_iff.mpr
    (fun a ha => by rw [Set.mem_singleton_iff.mp ha]))
  exact ⟨N, spec.1, spec.2.1, Rsub_eq_inf hG D hx hlen hgt,
    maximalContaining_centralizer_eq_singleton_of_tau2_element hG spec.1 hxN hx
      spec.2.2.2.2.1 spec.2.2.1⟩

/-- **`𝓜_σ(x)` is conjugation-equivariant**: `𝓜_σ(gxg⁻¹) = (conj g) • 𝓜_σ(x)` (as the image
under `L ↦ Lᵍ`).  Conjugation by `g` is an order-isomorphism of subgroups carrying `M_σ` to
`(Mᵍ)_σ` (`Msigma_conj_smul`), so it bijects the `σ`-maximals of `x` with those of `gxg⁻¹`. -/
private theorem maximalSigmaSubgroupsOfElement_conj [Finite G] (g x : G) :
    maximalSigmaSubgroupsOfElement (g * x * g⁻¹)
      = (fun L : Subgroup G => MulAut.conj g • L) '' maximalSigmaSubgroupsOfElement x := by
  have key : ∀ L : Subgroup G, x ∈ OddOrder.BG.Ch3.S10.Msigma L
      ↔ g * x * g⁻¹ ∈ OddOrder.BG.Ch3.S10.Msigma (MulAut.conj g • L) := by
    intro L
    rw [Msigma_conj_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hcalc : (MulAut.conj g)⁻¹ • (g * x * g⁻¹) = x := by
      rw [← map_inv (MulAut.conj) g, MulAut.smul_def, MulAut.conj_apply, inv_inv]; group
    rw [hcalc]
  ext L
  constructor
  · rintro ⟨hLmax, hxL⟩
    have hL₀L : MulAut.conj g • (MulAut.conj g⁻¹ • L) = L := by
      rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
    exact ⟨MulAut.conj g⁻¹ • L,
      ⟨mem_maximalSubgroups_of_isConjugateSubgroup hLmax ⟨g⁻¹, rfl⟩,
        by rw [key (MulAut.conj g⁻¹ • L), hL₀L]; exact hxL⟩, hL₀L⟩
  · rintro ⟨L₀, ⟨hL₀max, hxL₀⟩, rfl⟩
    exact ⟨mem_maximalSubgroups_of_isConjugateSubgroup hL₀max ⟨g, rfl⟩, (key L₀).mp hxL₀⟩

/-- **`R(x)` is conjugation-equivariant**: `R(gxg⁻¹) = (conj g) • R(x)` (BG mmd L3908, the
identity behind the cover `𝒞_G(M̃) = ⋃ₓ x R(x)`).  The `if`-condition of `R` is conjugation
invariant (`𝓜_σ` equivariance), and in the multi-maximal case `R(x) = N_σ ∩ C_G(x)` with `N(x)`
the *unique* maximal containing `C_G(x)`; since `N(x)ᵍ` is the unique maximal containing
`C_G(gxg⁻¹)`, it equals `N(gxg⁻¹)`, and the intersection conjugates accordingly. -/
theorem Rsub_conj [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) (g x : G) :
    Rsub hG D (g * x * g⁻¹) = MulAut.conj g • Rsub hG D x := by
  classical
  have hne1 : g * x * g⁻¹ ≠ 1 ↔ x ≠ 1 := by
    rw [ne_eq, ne_eq, mul_inv_eq_one, mul_eq_left]
  have himg : maximalSigmaSubgroupsOfElement (g * x * g⁻¹)
      = (fun L : Subgroup G => MulAut.conj g • L) '' maximalSigmaSubgroupsOfElement x :=
    maximalSigmaSubgroupsOfElement_conj g x
  have hinj : Function.Injective (fun L : Subgroup G => MulAut.conj g • L) :=
    fun a b h => by simpa using congrArg (fun L => (MulAut.conj g)⁻¹ • L) h
  have hncard : (maximalSigmaSubgroupsOfElement (g * x * g⁻¹)).ncard
      = (maximalSigmaSubgroupsOfElement x).ncard := by
    rw [himg, Set.ncard_image_of_injective _ hinj]
  have hne_iff : (maximalSigmaSubgroupsOfElement (g * x * g⁻¹)).Nonempty
      ↔ (maximalSigmaSubgroupsOfElement x).Nonempty := by rw [himg, Set.image_nonempty]
  have hcond_iff : (g * x * g⁻¹ ≠ 1 ∧ D.length (g * x * g⁻¹) = 1
        ∧ 1 < (maximalSigmaSubgroupsOfElement (g * x * g⁻¹)).ncard)
      ↔ (x ≠ 1 ∧ D.length x = 1 ∧ 1 < (maximalSigmaSubgroupsOfElement x).ncard) := by
    rw [D.length_one_iff, D.length_one_iff, hne1, hne_iff, hncard]
  by_cases hcase : x ≠ 1 ∧ D.length x = 1 ∧ 1 < (maximalSigmaSubgroupsOfElement x).ncard
  · obtain ⟨hx, hlen, hgt⟩ := hcase
    obtain ⟨hxc, hlenc, hgtc⟩ := hcond_iff.mpr ⟨hx, hlen, hgt⟩
    obtain ⟨N, hNmax, hCN, hReq, _⟩ := exists_neighbor_Rsub_singleton hG D hlen hgt
    obtain ⟨N', _, _, hReq', hsing'⟩ := exists_neighbor_Rsub_singleton hG D hlenc hgtc
    have hNconj : MulAut.conj g • N = N' := by
      have hmem : MulAut.conj g • N
          ∈ maximalSubgroupsContaining (Subgroup.centralizer ({g * x * g⁻¹} : Set G)) := by
        rw [mem_maximalSubgroupsContaining]
        refine ⟨mem_maximalSubgroups.mp
          (mem_maximalSubgroups_of_isConjugateSubgroup hNmax ⟨g, rfl⟩), ?_⟩
        rw [← smul_centralizer_singleton]
        intro y hy
        rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy ⊢
        exact hCN hy
      rw [hsing', Set.mem_singleton_iff] at hmem
      exact hmem
    rw [hReq', hReq, Subgroup.smul_inf, ← Msigma_conj_smul, smul_centralizer_singleton, hNconj]
  · have h1 : Rsub hG D (g * x * g⁻¹) = ⊥ := by
      rw [Rsub, dif_neg (fun h => hcase (hcond_iff.mp h))]
    have h2 : Rsub hG D x = ⊥ := by rw [Rsub, dif_neg hcase]
    rw [h1, h2, Subgroup.smul_bot]

/-- The left coset `x R(x)` as a pointwise scalar action: `x • R = { x r | r ∈ R }`.  Bridges
the set-builder form used by `xRsub_disjoint` to the `x • (R : Set G)` form on which the
pointwise-cardinality lemmas (`Set.ncard_smul_set`) act. -/
private theorem smul_coe_eq_coset (x : G) (R : Subgroup G) :
    x • (R : Set G) = {g : G | ∃ r ∈ R, g = x * r} := by
  ext g
  rw [Set.mem_smul_set]
  simp only [SetLike.mem_coe, Set.mem_ofPred_eq, smul_eq_mul]
  constructor
  · rintro ⟨r, hr, h⟩; exact ⟨r, hr, h.symm⟩
  · rintro ⟨r, hr, h⟩; exact ⟨r, hr, h.symm⟩

/-- **The cover** (BG mmd L3933, Lemma 14.5(c) Part B): the conjugacy saturation of `M̃` is the
disjoint union of the cosets `x R(x)` over `x ∈ 𝒞_G(M_σ^#)`.  By `R`-equivariance (`Rsub_conj`),
conjugating a product `x x'` (`x ∈ M_σ^#`, `x' ∈ R(x)`) by `g` gives `(xᵍ)(x'ᵍ)` with
`x'ᵍ ∈ R(xᵍ)` and `xᵍ ∈ 𝒞_G(M_σ^#)`, and conversely. -/
theorem conjClassSet_Mtilde_eq_biUnion [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M : Subgroup G} :
    conjClassSet (Mtilde hG D M)
      = ⋃ x ∈ sigmaConjugacySaturation M, x • (Rsub hG D x : Set G) := by
  ext y
  simp only [mem_conjClassSet, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨m, hm, g, rfl⟩
    obtain ⟨x, hxsharp, x', hx'R, rfl⟩ := hm
    refine ⟨g * x * g⁻¹, ⟨x, hxsharp, g, rfl⟩, ?_⟩
    rw [Set.mem_smul_set]
    have hmem : g * x' * g⁻¹ ∈ Rsub hG D (g * x * g⁻¹) := by
      rw [Rsub_conj, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have hcalc : (MulAut.conj g)⁻¹ • (g * x' * g⁻¹) = x' := by
        rw [← map_inv (MulAut.conj) g, MulAut.smul_def, MulAut.conj_apply, inv_inv]; group
      rw [hcalc]; exact hx'R
    exact ⟨g * x' * g⁻¹, hmem, by rw [smul_eq_mul]; group⟩
  · rintro ⟨z, hz, hy⟩
    rw [Set.mem_smul_set] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    rw [sigmaConjugacySaturation, mem_conjClassSet] at hz
    obtain ⟨t, ht, a, rfl⟩ := hz
    have hr' : r ∈ Rsub hG D (a * t * a⁻¹) := hr
    rw [Rsub_conj, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hr'
    set s : G := (MulAut.conj a)⁻¹ • r with hs
    have hrs : r = a * s * a⁻¹ := by
      rw [hs, ← map_inv (MulAut.conj) a, MulAut.smul_def, MulAut.conj_apply, inv_inv]; group
    refine ⟨t * s, ⟨t, ht, s, hr', rfl⟩, a, ?_⟩
    rw [smul_eq_mul, hrs]; group

/-- **BG Lemma 14.5(c)** (mmd L3933-3940): `|𝒞_G(M̃)| = (|M_σ| − 1)·[G : M]`.  Combines Part B
(the disjoint cover `𝒞_G(M̃) = ⊔ₓ x R(x)`, giving `|𝒞_G(M̃)| = ∑ₓ |R(x)|` via 14.5(a) +
left-translation) with Part A (`sigmaSaturation_Rsub_count`: `∑ₓ |R(x)| = |M_σ^#|·[G : M]`).
This is the type-`P` counting bound that drives Theorem 14.7. -/
theorem sigmaConjugacySaturation_Mtilde_ncard [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    (conjClassSet (Mtilde hG D M)).ncard
      = (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) - 1) * M.index := by
  classical
  have hdisj : (sigmaConjugacySaturation M).PairwiseDisjoint
      (fun x => x • (Rsub hG D x : Set G)) := by
    intro x hx y hy hxy
    simp only [Function.onFun]
    rw [smul_coe_eq_coset, smul_coe_eq_coset]
    exact xRsub_disjoint hG D
      (length_one_of_mem_sigmaConjugacySaturation hG D hM hx).1
      (length_one_of_mem_sigmaConjugacySaturation hG D hM hy).1 hxy
  have key : (⋃ x ∈ sigmaConjugacySaturation M, x • (Rsub hG D x : Set G)).ncard
      = ∑ x ∈ (Set.toFinite (sigmaConjugacySaturation M)).toFinset,
          Nat.card ↥(Rsub hG D x) := by
    rw [(Set.toFinite (sigmaConjugacySaturation M)).ncard_biUnion
        (fun i _ => Set.toFinite _) hdisj, ← finsum_mem_coe_finset]
    refine finsum_mem_congr (Set.Finite.coe_toFinset _).symm (fun x _ => ?_)
    rw [Set.ncard_smul_set, ← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.refl _)
  have hsharp : (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma M)).ncard
      = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) - 1 := by
    have hc : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)
        = (OddOrder.BG.Ch3.S10.Msigma M : Set G).ncard := by
      rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
    rw [sharpSubgroup, Set.ncard_sdiff
        (Set.singleton_subset_iff.mpr (OddOrder.BG.Ch3.S10.Msigma M).one_mem),
      Set.ncard_singleton, hc]
  rw [conjClassSet_Mtilde_eq_biUnion hG D, key, sigmaSaturation_Rsub_count hG D hM, hsharp]

/-- **BG Lemma 14.6, exclusivity** (mmd L3947): the `type-2 ⟹ ¬type-1` direction that Theorem 14.7
consumes as "`T ∩ H̃` is empty".  If `g = y·y'` with `y ∈ M_σ^#` (hence `ℓ_σ(y) = 1`) and `y'` a
nonidentity `κ(M)`-element of `C_M(y)`, then `g` is **not** of the form `x·x'` with `ℓ_σ(x) = 1`
and `x' ∈ R(x)`.  Mirrors Lemma 14.5(a)'s factor matching (`isPiElement_mul_unique` + the σ-class
partition); the contradiction is `κ(M)` (`p`-rank 1) vs `τ₂(N)` (`p`-rank 2) for the factor
`x = y'`, using that `p`-rank is conjugation invariant. -/
theorem not_type1_of_type2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {g : G} {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {y y' : G} (hy : y ∈ sigmaSharp M) (hgyy' : g = y * y') (hcomm : Commute y y')
    (hy'1 : y' ≠ 1) (hy'M : y' ∈ M) (hy'C : y' ∈ Subgroup.centralizer ({y} : Set G))
    (hy'κ : ∀ p ∈ piSet (Subgroup.closure {y'}), p ∈ kappa M) :
    ¬ ∃ x x' : G, g = x * x' ∧ D.length x = 1 ∧ x' ∈ Rsub hG D x := by
  classical
  rintro ⟨x, x', hgxx', hlx, hx'R⟩
  have hx1 : x ≠ 1 := ((D.length_one_iff x).mp hlx).1
  rw [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe] at hy
  obtain ⟨hyMσ, hy1⟩ := hy
  have hgeq : x * x' = y * y' := hgxx'.symm.trans hgyy'
  have hpiSet : ∀ z : G, ∀ {q : ℕ}, q ∈ (orderOf z).primeFactors →
      q ∈ piSet (Subgroup.closure ({z} : Set G)) := fun z {q} hq => by
    rw [piSet, Set.mem_ofPred_eq, ← Subgroup.zpowers_eq_closure, Nat.card_zpowers]; exact hq
  obtain ⟨M_x, hMxmax, hxMx⟩ := ((D.length_one_iff x).mp hlx).2
  have hxPi : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M_x) x := fun p hp =>
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M_x p (Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactors hp, (Nat.dvd_of_mem_primeFactors hp).trans
        ((OddOrder.BG.Ch3.S10.Msigma M_x).orderOf_dvd_natCard hxMx), Nat.card_pos.ne'⟩)
  have hyPi : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M) y := fun p hp =>
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p (Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactors hp, (Nat.dvd_of_mem_primeFactors hp).trans
        ((OddOrder.BG.Ch3.S10.Msigma M).orderOf_dvd_natCard hyMσ), Nat.card_pos.ne'⟩)
  have hx'Pi : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M_x)ᶜ x' :=
    isPiElement_sigmaCompl_of_mem_Rsub hG D hlx ⟨hMxmax, hxMx⟩ hx'R
  have hy'Pi : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M)ᶜ y' := by
    intro p hp hpM
    rcases (hy'κ p (hpiSet y' hp)).2.1 with h1 | h3
    · exact tau1_subset_sigma_compl M h1 hpM
    · exact tau3_subset_sigma_compl M h3 hpM
  have hcx : Commute x x' :=
    Subgroup.mem_centralizer_iff.mp (Rsub_le_centralizer hG D x hx'R) x (Set.mem_singleton x)
  -- `x' ≠ 1`: else `g = x` collides with `g = y·y'`, `y' ≠ 1`.
  have hx'1 : x' ≠ 1 := by
    intro hx'0
    rw [hx'0, mul_one] at hgeq
    by_cases hσ : OddOrder.BG.Ch3.S10.sigma M_x = OddOrder.BG.Ch3.S10.sigma M
    · have hxPiM : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x := by
        rw [← hσ]; exact hxPi
      exact hy'1 (OddOrder.GroupTheory.isPiElement_mul_unique (mul_one x) (Commute.one_right x)
        hxPiM (OddOrder.GroupTheory.isPiElement_one _) hgeq.symm hcomm hyPi hy'Pi).2.symm
    · have hxPiMc : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M)ᶜ x :=
        fun p hp hpM => hσ (sigma_eq_of_mem_sigma_of_mem_sigma hG hMxmax hM (hxPi p hp) hpM)
      exact hy1 (OddOrder.GroupTheory.isPiElement_mul_unique (one_mul x) (Commute.one_left x)
        (OddOrder.GroupTheory.isPiElement_one _) hxPiMc hgeq.symm hcomm hyPi hy'Pi).1.symm
  have hgtx : 1 < (maximalSigmaSubgroupsOfElement x).ncard := by
    by_contra h
    rw [Rsub, dif_neg (fun hc => h hc.2.2), Subgroup.mem_bot] at hx'R
    exact hx'1 hx'R
  obtain ⟨N, hNmax, hCxN, hReqN, hπτ2N, _⟩ := exists_neighbor_eq_Rsub hG D hlx hgtx
  have hxN : x ∈ N := hCxN (Subgroup.mem_centralizer_iff.mpr fun z hz => by
    rw [Set.mem_singleton_iff.mp hz])
  have hRxne : OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
    rw [← hReqN]; intro hbot; exact hx'1 (Subgroup.mem_bot.mp (hbot ▸ hx'R))
  have hsingx : maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {N} :=
    maximalContaining_centralizer_eq_singleton_of_tau2_element hG hNmax hxN hx1 hπτ2N hRxne
  by_cases hσeq : OddOrder.BG.Ch3.S10.sigma M_x = OddOrder.BG.Ch3.S10.sigma M
  · -- **Equal classes**: `x = y`; then `M = N` and `x = y ∈ M_σ` is a `τ₂(M)`-element, absurd.
    have hyPiMx : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M_x) y := by
      rw [hσeq]; exact hyPi
    have hy'PiMxc : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M_x)ᶜ y' := by
      rw [hσeq]; exact hy'Pi
    have hxy : x = y :=
      (OddOrder.GroupTheory.isPiElement_mul_unique rfl hcx hxPi hx'Pi hgeq.symm hcomm
        hyPiMx hy'PiMxc).1
    -- Corollary 14.3 for `(y, y')`: branch 2 (`τ₂`) is impossible, so `C_G(y) ⊆ M`.
    have hCyM : Subgroup.centralizer ({y} : Set G) ≤ M := by
      have hyσsharp : y ∈ sigmaSharp M := by
        rw [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe]
        exact ⟨hyMσ, hy1⟩
      rcases sigma_diagnostic hG D hM hyσsharp hy'M hy'1 hy'C
        (fun p hp => hy'Pi p (by
          rw [piSet, Set.mem_ofPred_eq, ← Subgroup.zpowers_eq_closure, Nat.card_zpowers] at hp
          exact hp)) with ⟨_, hsub⟩ | ⟨hτ2, _, _⟩
      · exact hsub
      · exfalso
        obtain ⟨q, hqy⟩ : (orderOf y').primeFactors.Nonempty :=
          Nat.nonempty_primeFactors.mpr (by
            have := orderOf_pos y'
            have hne : orderOf y' ≠ 1 := fun h => hy'1 (orderOf_eq_one_iff.mp h)
            omega)
        have hqκ := hy'κ q (hpiSet y' hqy)
        have hqτ2 := hτ2 q (hpiSet y' hqy)
        rcases hqκ.2.1 with h1 | h3
        · exact absurd ((tau1_pRank_eq_one h1).symm.trans (tau2_pRank_eq_two hqτ2)) (by norm_num)
        · exact absurd ((tau3_pRank_eq_one h3).symm.trans (tau2_pRank_eq_two hqτ2)) (by norm_num)
    have hMN : M = N := by
      have hmem : M ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) :=
        mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hM, hxy ▸ hCyM⟩
      rw [hsingx, Set.mem_singleton_iff] at hmem; exact hmem
    obtain ⟨p, hpx⟩ : (orderOf x).primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by
      have := orderOf_pos x
      have hne : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
      omega)
    have hpτ2M : p ∈ tau2 M := hMN ▸ hπτ2N p (hpiSet x hpx)
    have hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M := hxy ▸ hyMσ
    have hpσM : p ∈ OddOrder.BG.Ch3.S10.sigma M :=
      OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p (Nat.mem_primeFactors.mpr
        ⟨Nat.prime_of_mem_primeFactors hpx, (Nat.dvd_of_mem_primeFactors hpx).trans
          ((OddOrder.BG.Ch3.S10.Msigma M).orderOf_dvd_natCard hxMσ), Nat.card_pos.ne'⟩)
    exact tau2_subset_sigma_compl M hpτ2M hpσM
  · -- **Disjoint classes**: factor matching gives `y = x'`, `y' = x`; then `M, N` conjugate, and
    -- `x = y'` is a `κ(M)`-element (rank 1) and a `τ₂(N)`-element (rank 2), absurd by
    -- conj-invariance.
    have hxPiMc : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M)ᶜ x :=
      fun p hp hpM => hσeq (sigma_eq_of_mem_sigma_of_mem_sigma hG hMxmax hM (hxPi p hp) hpM)
    have hx'N : x' ∈ OddOrder.BG.Ch3.S10.Msigma N := by
      rw [hReqN] at hx'R; exact (Subgroup.mem_inf.mp hx'R).1
    have hx'PiN : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma N) x' := fun q hq =>
      OddOrder.BG.Ch3.S10.Msigma_isPiGroup N q (Nat.mem_primeFactors.mpr
        ⟨Nat.prime_of_mem_primeFactors hq, (Nat.dvd_of_mem_primeFactors hq).trans
          ((OddOrder.BG.Ch3.S10.Msigma N).orderOf_dvd_natCard hx'N), Nat.card_pos.ne'⟩)
    obtain ⟨p, hpy⟩ : (orderOf y).primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by
      have := orderOf_pos y
      have hne : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
      omega)
    have hcox : Nat.Coprime (orderOf x) (orderOf x') :=
      OddOrder.GroupTheory.coprime_orderOf_of_isPiElement hxPi hx'Pi
    have hpg : (orderOf (x * x')).primeFactors =
        (orderOf x).primeFactors ∪ (orderOf x').primeFactors := by
      rw [hcx.orderOf_mul_eq_mul_orderOf_of_coprime hcox,
        Nat.primeFactors_mul (orderOf_pos x).ne' (orderOf_pos x').ne']
    have hcoy : Nat.Coprime (orderOf y) (orderOf y') :=
      OddOrder.GroupTheory.coprime_orderOf_of_isPiElement hyPi hy'Pi
    have hyg : (orderOf y).primeFactors ⊆ (orderOf (x * x')).primeFactors := by
      rw [hgeq, hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcoy,
        Nat.primeFactors_mul (orderOf_pos y).ne' (orderOf_pos y').ne']
      exact Finset.subset_union_left
    have hpmem : p ∈ (orderOf x).primeFactors ∪ (orderOf x').primeFactors := hpg ▸ hyg hpy
    have hσMN : OddOrder.BG.Ch3.S10.sigma M = OddOrder.BG.Ch3.S10.sigma N := by
      rcases Finset.mem_union.mp hpmem with hpx | hpx'
      · exact absurd (sigma_eq_of_mem_sigma_of_mem_sigma hG hMxmax hM (hxPi p hpx) (hyPi p hpy))
          hσeq
      · exact sigma_eq_of_mem_sigma_of_mem_sigma hG hM hNmax (hyPi p hpy) (hx'PiN p hpx')
    have hx'PiM : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x' := by
      rw [hσMN]; exact hx'PiN
    obtain ⟨hx'y, hxy'⟩ := OddOrder.GroupTheory.isPiElement_mul_unique (g := x * x')
      hcx.symm hcx.symm hx'PiM hxPiMc hgeq.symm hcomm hyPi hy'Pi
    -- `M, N` conjugate (`y ∈ M_σ ∩ N_σ`, `σ(M) = σ(N)`, Thm 13.9).
    have hconj : IsConjugateSubgroup M N := by
      by_contra hnc
      exact Set.disjoint_left.mp (sigma_disjoint_of_nonconjugate hG hM hNmax hnc)
        (hyPi p hpy) (hσMN ▸ hyPi p hpy)
    -- `x = y'` is a `κ(M)`-element and a `τ₂(N)`-element; `p`-rank is conjugation invariant.
    obtain ⟨p2, hp2x⟩ : (orderOf x).primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by
      have := orderOf_pos x
      have hne : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
      omega)
    have hp2κ : p2 ∈ kappa M := hy'κ p2 (hxy' ▸ hpiSet x hp2x)
    have hp2τ2 : p2 ∈ tau2 N := hπτ2N p2 (hpiSet x hp2x)
    have hrM : pRank ↥M p2 = 1 := by
      rcases hp2κ.2.1 with h1 | h3
      · exact tau1_pRank_eq_one h1
      · exact tau3_pRank_eq_one h3
    have hrN : pRank ↥N p2 = 2 := tau2_pRank_eq_two hp2τ2
    obtain ⟨c, hc⟩ := hconj
    have hmapN : M.map (MulAut.conj c).toMonoidHom = N := hc
    have heq : pRank ↥M p2 = pRank ↥N p2 :=
      pRank_eq_of_mulEquiv
        ((Subgroup.equivMapOfInjective M (MulAut.conj c).toMonoidHom
          (MulAut.conj c).injective).trans (MulEquiv.subgroupCongr hmapN))
    rw [hrM, hrN] at heq
    exact absurd heq (by norm_num)

/-- **Conjugacy-saturation count of a TI-subset** (BG §1, the input to Theorem 14.7 step 5):
for a TI-subset `A` with normalizer-bound `L` that `L` stabilizes (`A^l = A` for `l ∈ L`), the
saturation `𝒞_G(A)` is the disjoint union of the `[G:L]` conjugates `A^g` (each of cardinality
`|A|`), whence `|𝒞_G(A)| = |A|·[G:L]`.  The subset analogue of
`ncard_conjugates_eq_index_of_normalizer_eq_self`. -/
theorem ncard_conjClassSet_of_isTISubset [Finite G] {A : Set G} {L : Subgroup G}
    (hTI : OddOrder.GroupTheory.IsTISubset A L)
    (hstab : ∀ l ∈ L, MulAut.conj l • A = A) :
    (conjClassSet A).ncard = A.ncard * L.index := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hwd : ∀ g₁ g₂ : G, QuotientGroup.leftRel L g₁ g₂ →
      MulAut.conj g₁ • A = MulAut.conj g₂ • A := by
    intro g₁ g₂ hrel
    rw [QuotientGroup.leftRel_apply] at hrel
    calc MulAut.conj g₁ • A
        = MulAut.conj g₁ • (MulAut.conj (g₁⁻¹ * g₂) • A) := by rw [hstab _ hrel]
      _ = MulAut.conj g₂ • A := by rw [← mul_smul, ← map_mul, mul_inv_cancel_left]
  set B : G ⧸ L → Set G := Quotient.lift (fun g => MulAut.conj g • A) hwd with hBdef
  have hBval : ∀ g : G, B (QuotientGroup.mk g) = MulAut.conj g • A := fun g => rfl
  have hunion : conjClassSet A = ⋃ q : G ⧸ L, B q := by
    ext y
    rw [mem_conjClassSet, Set.mem_iUnion]
    constructor
    · rintro ⟨t, ht, g, rfl⟩
      refine ⟨QuotientGroup.mk g, ?_⟩
      rw [hBval, Set.mem_smul_set]
      exact ⟨t, ht, by rw [MulAut.smul_def, MulAut.conj_apply]⟩
    · rintro ⟨q, hq⟩
      obtain ⟨g, rfl⟩ := Quotient.exists_rep q
      rw [hBval, Set.mem_smul_set] at hq
      obtain ⟨a, ha, rfl⟩ := hq
      exact ⟨a, ha, g, by rw [MulAut.smul_def, MulAut.conj_apply]⟩
  have hdisj : Pairwise (Function.onFun Disjoint B) := by
    intro q q' hqq'
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    obtain ⟨g', rfl⟩ := Quotient.exists_rep q'
    simp only [Function.onFun, hBval]
    rw [Set.disjoint_left]
    rintro y hy hy'
    rw [Set.mem_smul_set] at hy hy'
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨a', ha', heq⟩ := hy'
    have he : g * a * g⁻¹ = g' * a' * g'⁻¹ := by
      rw [MulAut.smul_def, MulAut.smul_def, MulAut.conj_apply, MulAut.conj_apply] at heq
      exact heq.symm
    have hov : (g'⁻¹ * g) * a * (g'⁻¹ * g)⁻¹ ∈ A := by
      have hc : (g'⁻¹ * g) * a * (g'⁻¹ * g)⁻¹ = a' := by
        rw [show (g'⁻¹ * g) * a * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * a * g⁻¹) * g' from by group, he]; group
      rw [hc]; exact ha'
    have hmem : g'⁻¹ * g ∈ L := hTI (g'⁻¹ * g) ⟨a, ha, hov⟩
    apply hqq'
    apply Quotient.sound
    change (QuotientGroup.leftRel L) g g'
    rw [QuotientGroup.leftRel_apply]
    have h2 : g⁻¹ * g' = (g'⁻¹ * g)⁻¹ := by group
    rw [h2]; exact L.inv_mem hmem
  rw [hunion, Set.ncard_iUnion_of_finite (fun q => Set.toFinite _) hdisj]
  have hBcard : ∀ q : G ⧸ L, (B q).ncard = A.ncard := by
    intro q
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    rw [hBval]; exact Set.ncard_smul_set _ _
  rw [finsum_congr hBcard, finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, ← Nat.card_eq_fintype_card, ← Subgroup.index]
  exact mul_comm _ _

end OddOrder.BG.Ch4.S14


