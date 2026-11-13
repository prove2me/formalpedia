-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TheoremsAE
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TheoremsAE
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T10:29:27.587717+00:00
-- url     : https://prove2.me/theorems/0995aceb-430b-4f38-b7d4-cb57bb5f405d
-- title:
--   BG §16: Theorems A–E (continuation)
-- statement:
--   A continuation of the Theorems A–E development of §16 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*. It consists of lemmas only, including `theoremC_paired_structure`, `msigma_fusion_control`, matched $\kappa$-Hall pairs for type $\mathcal{P}_2$ and conjugate-of-$\widetilde Z$ statements.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 12 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/TheoremsAE.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/TheoremsAE.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_Notation
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TheoremAB

namespace OddOrder.BG.Ch4.S16

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch4.S14

open OddOrder.BG.Ch4.S15

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BG Theorem C(9), structural inclusion** (mmd L4385; schematic proof: Proposition 14.2(d) +
Theorem A(3),(5)): every element of `A_0(M) − A(M)` is `M`-conjugate to an element of
`Ẑ = Z − (K ∪ K*)`.  This is the `⊆` half of BG's identity `A_0(M) − A(M) = 𝒞_M(Ẑ)`, and together
with the TI-ness of `Ẑ` (Theorem 14.7(e), `N_G(Ẑ) = K ⊔ K* ≤ M`) it is exactly what the TI claim of
Theorem C(9) needs, via the transport lemma `IsTISubset.of_subset_conj_of_isTISubset`.

Proof: let `a ∈ A_0(M) − A(M)`, so `a ∈ M`, `M_σ ⊓ C_G(a) ≠ 1`, `a ∉ 𝒞_G(K#)`, and `a ∉ U M_σ`.
Take the `κ`/`κ'`-decomposition `a = a_κ · a_{κ'}` (`exists_isPiElement_mul`: commuting powers of
`a`, `a_κ` a `κ`-element, `a_{κ'}` a `κ'`-element).  Conjugate by some `w ∈ M` so that `a_κ ∈ K`
(`exists_conj_smul_le_isHall_kappa`, as `⟨a_κ⟩` is a `κ`-subgroup of `M`).  Then:

* `a_κ ≠ 1`: otherwise `a = a_{κ'}` is a `κ'`-element, hence lies in the normal Hall `κ'`-subgroup
  `M' = U M_σ` (Theorem C(3)), contradicting `a ∉ U M_σ`.
* `a_{κ'} ≠ 1`: otherwise `a` is `G`-conjugate to `a_κ ∈ K#`, contradicting `a ∉ 𝒞_G(K#)`.
* `a_{κ'} ∈ K*`: `a_{κ'} ∈ M' = U ⋊ M_σ` commutes with `a_κ ∈ K#`; writing `a_{κ'} = u·t`
  (`u ∈ U`, `t ∈ M_σ`), `K`-invariance of `U` (Proposition 14.2(a)) and of `M_σ` plus uniqueness of
  the `U ⋊ M_σ` factorization force `u ∈ C_U(a_κ) = 1` (Theorem A(4)) and `t ∈ C_{M_σ}(a_κ) = K*`
  (Theorem A(5)), so `a_{κ'} = t ∈ K*`.

Hence (after the conjugation) `a = a_κ · a_{κ'} ∈ K·K*` with both factors nontrivial, i.e.
`a ∈ Z − (K ∪ K*) = Ẑ`. -/
theorem a0_minus_a_subset_conj_zTilde [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M)
    (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    ∀ a ∈ A0Set M K \ ASet M U,
      ∃ m ∈ M, ∃ t ∈ S14.zTilde K Kstar, a = m * t * m⁻¹ := by
  classical
  have hsolv : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hKne : K ≠ ⊥ := fun h => card_kappaHall_ne_one hP hKM hK (by rw [h, Subgroup.card_bot])
  have hKcyc : IsCyclic ↥K := (typeP_auxiliary_structure hG hM hKM hUM hK hKstar hU).2.1
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hM'M : (U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) ≤ M := sup_le hUM hMσM
  have hKstarMσ : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M := by rw [hKstar]; exact inf_le_left
  -- `M' = U ⊔ M_σ` (Theorem C(3) / Lemma 15.1(b)).
  have hM'eq : derivedInG M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M :=
    (typeP_hall_derived_eq_and_abelian hG hM hKM hUM hKne hK hU).1
  -- **Helper A**: every `κ(M)'`-element of `M` lies in the normal Hall `κ'`-subgroup
  -- `M' = U ⊔ M_σ`.
  -- (`M'` complements the Hall `κ`-subgroup `K` in `M`, so `[M : M'] = |K|` is a `κ`-number;
  -- a `κ'`-element has image of order dividing both `[M : M']` and its own order, hence trivial.)
  have hkappaComplMem : ∀ x : G, x ∈ M → IsPiElement (S14.kappa M)ᶜ x →
      x ∈ (U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) := by
    intro x hxM hxπ'
    rw [← hM'eq]
    have hNnorm : ((derivedInG M).subgroupOf M).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (OddOrder.BG.Ch3.S10.le_normalizer_derivedInG M)
    set N := (derivedInG M).subgroupOf M with hNdef
    set x' : ↥M := ⟨x, hxM⟩ with hx'def
    -- `N.index = |K|` is a `κ`-number (`M'` complements the Hall `κ`-subgroup `K`).
    have hidxκ : ∀ p ∈ N.index.primeFactors, p ∈ S14.kappa M := by
      have hcompl := (typeP_duality hG hM hP hKM hK hKstar).1
      have hidxeq : N.index = Nat.card ↥(K.subgroupOf M) := hcompl.symm.index_eq_card
      rw [hidxeq]; exact hK.1
    -- `orderOf x'` is a `κ'`-number, hence coprime to `N.index`.
    have hordx' : orderOf x' = orderOf x :=
      (orderOf_injective M.subtype M.subtype_injective x').symm
    have hcop : Nat.Coprime (orderOf x') N.index := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
      rw [Nat.dvd_gcd_iff] at hpdvd
      have hpord : p ∈ (orderOf x).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hpp, hordx' ▸ hpdvd.1, (orderOf_pos x).ne'⟩
      exact (hxπ' p hpord)
        (hidxκ p (Nat.mem_primeFactors.mpr ⟨hpp, hpdvd.2, Subgroup.index_ne_zero_of_finite⟩))
    -- The image of `x'` in `↥M ⧸ N` has order dividing both `orderOf x'` and `N.index`, hence `1`.
    have hord1 : orderOf (QuotientGroup.mk' N x') = 1 := by
      have h1 : orderOf (QuotientGroup.mk' N x') ∣ orderOf x' :=
        orderOf_dvd_of_pow_eq_one (by rw [← map_pow, pow_orderOf_eq_one, map_one])
      have h2 : orderOf (QuotientGroup.mk' N x') ∣ N.index := orderOf_dvd_natCard _
      exact Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h1 h2)
    have hx'N : x' ∈ N := by
      have h := orderOf_eq_one_iff.mp hord1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact Subgroup.mem_subgroupOf.mp hx'N
  -- **Helper B**: `M' ⊓ (K ⊔ K*) = K*` (direct: `x = k·k* ∈ M'`, `k* ∈ K* ≤ M'`, so
  -- `k ∈ K ⊓ M' = 1`).
  have hMeetKKstar : (U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) ⊓ (K ⊔ Kstar) = Kstar := by
    refine le_antisymm ?_ (le_inf (hKstarMσ.trans le_sup_right) le_sup_right)
    -- `K` is normal in `K ⊔ K*` (`K*` centralizes it), so an element `x` of `K ⊔ K*` is `a·b`
    -- with `a ∈ K`, `b ∈ K*`.  If also `x ∈ M'`, then `a = x·b⁻¹ ∈ K ⊓ M' = ⊥`, so `x = b ∈ K*`.
    have hKstarC : Kstar ≤ Subgroup.centralizer (K : Set G) := by rw [hKstar]; exact inf_le_right
    have hKnorm : (K ⊔ Kstar : Subgroup G) ≤ Subgroup.normalizer (K : Set G) :=
      sup_le Subgroup.le_normalizer (hKstarC.trans (Subgroup.centralizer_le_normalizer _))
    have : (K.subgroupOf (K ⊔ Kstar)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hKnorm
    have hsuptop : (K.subgroupOf (K ⊔ Kstar)) ⊔ (Kstar.subgroupOf (K ⊔ Kstar)) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    have hKM'bot : K ⊓ (U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) = ⊥ := by
      have hcompl := (typeP_duality hG hM hP hKM hK hKstar).1
      have hdisj : Disjoint ((derivedInG M).subgroupOf M) (K.subgroupOf M) := hcompl.disjoint
      rw [← hM'eq, eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_inf] at hy
      have hmemMinf : (⟨y, hKM hy.1⟩ : ↥M) ∈ (K.subgroupOf M) ⊓ ((derivedInG M).subgroupOf M) :=
        Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hy.1, Subgroup.mem_subgroupOf.mpr hy.2⟩
      rw [disjoint_iff.mp hdisj.symm, Subgroup.mem_bot] at hmemMinf
      rw [Subgroup.mem_bot]; exact Subtype.ext_iff.mp hmemMinf
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxM', hxKK⟩ := hx
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp
      (hsuptop ▸ Subgroup.mem_top (⟨x, hxKK⟩ : ↥(K ⊔ Kstar)))
    have haK : (a : G) ∈ K := Subgroup.mem_subgroupOf.mp ha
    have hbKstar : (b : G) ∈ Kstar := Subgroup.mem_subgroupOf.mp hb
    have hab' : (a : G) * (b : G) = x := by have := congrArg Subtype.val hab; simpa using this
    have haM' : (a : G) ∈ (U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) := by
      have heq : (a : G) = x * (b : G)⁻¹ := by rw [← hab']; group
      rw [heq]
      exact Subgroup.mul_mem _ hxM'
        (Subgroup.inv_mem _ ((hKstarMσ.trans le_sup_right) hbKstar))
    have ha1 : (a : G) = 1 := Subgroup.mem_bot.mp (hKM'bot ▸ Subgroup.mem_inf.mpr ⟨haK, haM'⟩)
    rw [← hab', ha1, one_mul]; exact hbKstar
  -- ## Main argument.
  intro a ha
  have haM : a ∈ M := ha.1.1.1
  have hanc : a ∉ conjClassSet (sharpSubgroup K) := ha.1.2
  have haUMσ : a ∉ ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) :=
    fun hmem => ha.2 ⟨ha.1.1, hmem⟩
  -- `κ`/`κ'`-decomposition `a = a_κ · a_{κ'}`.
  obtain ⟨aκ, aκ', hmul, hcomm, hκ, hκ', hazκ, hazκ'⟩ := exists_isPiElement_mul (S14.kappa M) a
  have hzpaM : Subgroup.zpowers a ≤ M := Subgroup.zpowers_le.mpr haM
  have haκM : aκ ∈ M := hzpaM hazκ
  have haκ'M : aκ' ∈ M := hzpaM hazκ'
  -- `a_κ ≠ 1`: else `a = a_{κ'}` is a `κ'`-element, so `a ∈ M'`, contradicting `a ∉ U M_σ`.
  have haκne : aκ ≠ 1 := by
    intro h
    refine haUMσ ?_
    have : a = aκ' := by rw [← hmul, h, one_mul]
    rw [this]; exact hkappaComplMem aκ' haκ'M hκ'
  -- Conjugate `⟨a_κ⟩` into `K`.
  have hXpi : Ch03.Subgroup.IsPiGroup (S14.kappa M) ((Subgroup.zpowers aκ).subgroupOf M) := by
    intro p hp
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr haκM)).toEquiv,
      Nat.card_zpowers] at hp
    exact hκ p hp
  obtain ⟨w, hwM, hwle⟩ :=
    exists_conj_smul_le_isHall_kappa hG hM hKM hK (Subgroup.zpowers_le.mpr haκM) hXpi
  -- `b := w·a·w⁻¹ = b_κ·b_{κ'}` with `b_κ = w·a_κ·w⁻¹ ∈ K`.
  have hbκK : w * aκ * w⁻¹ ∈ K := by
    have hmem : (MulAut.conj w) • aκ ∈ MulAut.conj w • Subgroup.zpowers aκ :=
      Subgroup.smul_mem_pointwise_smul aκ (MulAut.conj w) _ (Subgroup.mem_zpowers aκ)
    have heq : (MulAut.conj w) • aκ = w * aκ * w⁻¹ := rfl
    rw [heq] at hmem; exact hwle hmem
  -- `b_κ' := w·a_{κ'}·w⁻¹ ∈ M'` (conjugate of a `κ'`-element, `M' ◁ M`, `w ∈ M`).
  have hbκ'M' : w * aκ' * w⁻¹ ∈ (U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) := by
    have hwnorm : w ∈ Subgroup.normalizer (derivedInG M) :=
      OddOrder.BG.Ch3.S10.le_normalizer_derivedInG M hwM
    have h1 : aκ' ∈ derivedInG M := by rw [hM'eq]; exact hkappaComplMem aκ' haκ'M hκ'
    have hconjM' : w * aκ' * w⁻¹ ∈ derivedInG M :=
      (Subgroup.mem_normalizer_iff.mp hwnorm aκ').mp h1
    rwa [hM'eq] at hconjM'
  -- `b_κ ≠ 1` and `b_κ' ≠ 1`.
  have hbκne : w * aκ * w⁻¹ ≠ 1 := by
    intro h
    exact haκne (by
      have := congrArg (fun y => w⁻¹ * y * w) h; simpa [mul_assoc] using this)
  have hbκ'ne : w * aκ' * w⁻¹ ≠ 1 := by
    intro h
    -- `b_κ' = 1 ⟹ a_{κ'} = 1 ⟹ a = a_κ`, and `a = w⁻¹·b_κ·w` is `G`-conjugate to `b_κ ∈ K#`.
    have haκ'1 : aκ' = 1 := by
      have h2 := congrArg (fun y => w⁻¹ * y * w) h; simpa [mul_assoc] using h2
    have haaκ : a = aκ := by rw [← hmul, haκ'1, mul_one]
    exact hanc ⟨w * aκ * w⁻¹, ⟨hbκK, hbκne⟩, w⁻¹, by rw [haaκ]; group⟩
  -- `b_κ' ∈ K*`: it lies in `M' ⊓ C_M(b_κ) = M' ⊓ (K ⊔ K*) = K*`.
  have hbκ'comm : Commute (w * aκ * w⁻¹) (w * aκ' * w⁻¹) := by
    change w * aκ * w⁻¹ * (w * aκ' * w⁻¹) = w * aκ' * w⁻¹ * (w * aκ * w⁻¹)
    calc w * aκ * w⁻¹ * (w * aκ' * w⁻¹) = w * (aκ * aκ') * w⁻¹ := by group
      _ = w * (aκ' * aκ) * w⁻¹ := by rw [hcomm.eq]
      _ = w * aκ' * w⁻¹ * (w * aκ * w⁻¹) := by group
  have hbκ'CM : w * aκ' * w⁻¹ ∈ Subgroup.centralizer ({w * aκ * w⁻¹} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg; subst hg
    exact hbκ'comm.eq
  have hbκ'Kstar : w * aκ' * w⁻¹ ∈ Kstar := by
    have hCMeq : M ⊓ Subgroup.centralizer ({w * aκ * w⁻¹} : Set G) = K ⊔ Kstar :=
      typeP_centralizer_kappaElement_eq hG hM hP hKM hK hKstar hU _ hbκK hbκne
    have hbκ'KK : w * aκ' * w⁻¹ ∈ K ⊔ Kstar := by
      rw [← hCMeq, Subgroup.mem_inf]
      exact ⟨hM'M hbκ'M', hbκ'CM⟩
    rw [← hMeetKKstar, Subgroup.mem_inf]
    exact ⟨hbκ'M', hbκ'KK⟩
  -- Assemble: `b := w·a·w⁻¹ = b_κ·b_{κ'} ∈ K·K* ⊆ K ⊔ K*`, and `b ∉ K`, `b ∉ K*`, so `b ∈ Ẑ`.
  refine ⟨w⁻¹, M.inv_mem hwM, w * a * w⁻¹, ?_, by group⟩
  have hbeq : w * a * w⁻¹ = (w * aκ * w⁻¹) * (w * aκ' * w⁻¹) := by
    rw [← hmul]; group
  refine ⟨?_, ?_⟩
  · -- `b ∈ K ⊔ K*`.
    rw [hbeq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hbκK) (Subgroup.mem_sup_right hbκ'Kstar)
  · -- `b ∉ K ∪ K*`.
    rw [Set.mem_union]
    push Not
    refine ⟨fun hbK => ?_, fun hbKstar => ?_⟩
    · -- `b ∈ K ⟹ b_κ' = b_κ⁻¹·b ∈ K ⊓ K* = 1`, contra `b_κ' ≠ 1`.
      have hbκ'K : w * aκ' * w⁻¹ ∈ K := by
        have : w * aκ' * w⁻¹ = (w * aκ * w⁻¹)⁻¹ * (w * a * w⁻¹) := by rw [hbeq]; group
        rw [this]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hbκK) hbK
      exact hbκ'ne (Subgroup.mem_bot.mp
        (kappaHall_inf_Kstar_eq_bot hKM hK hKstar ▸ Subgroup.mem_inf.mpr ⟨hbκ'K, hbκ'Kstar⟩))
    · -- `b ∈ K* ⟹ b_κ = b·b_κ'⁻¹ ∈ K ⊓ K* = 1`, contra `b_κ ≠ 1`.
      have hbκK' : w * aκ * w⁻¹ ∈ Kstar := by
        have : w * aκ * w⁻¹ = (w * a * w⁻¹) * (w * aκ' * w⁻¹)⁻¹ := by rw [hbeq]; group
        rw [this]; exact Subgroup.mul_mem _ hbKstar (Subgroup.inv_mem _ hbκ'Kstar)
      exact hbκne (Subgroup.mem_bot.mp
        (kappaHall_inf_Kstar_eq_bot hKM hK hKstar ▸ Subgroup.mem_inf.mpr ⟨hbκK, hbκK'⟩))

/-- **Matched `κ`-Hall / `(κ∪σ)'`-Hall pair for a type-`P₂` maximal subgroup**
(BG `kappa_complement`;
the Frobenius complement `E = K ⋉ U` of Proposition 14.2(a), with `U = E₂E₃` the `M_σ`-complement's
derived subgroup).  There is a `κ(M)`-Hall `K₀` and a nontrivial abelian `(κ(M)∪σ(M))'`-Hall `U₀`,
both `≤ M`, with `K₀ ≤ N_G(U₀)` — since `U₀ = E₂E₃ ◁ E` (`E23_normal`) and `K₀ = E₁ ≤ E`.

This is exactly the matched pair consumed by Corollary 14.12 (`typeP2_neighbor_is_typeF`) via its
`hKNU : K ≤ N(U)` hypothesis.  As all `(κ∪σ)'`-Hall subgroups of `M` are `M`-conjugate, the
arbitrary `U` of Theorem C is `M`-conjugate to `U₀`, which transports `N_G(U) ⊄ M` between them.

Construction: take a §12 `E`-setup (`E = E₁E₂E₃`, `E` a `σ(M)'`-complement of `M_σ`).  Type-`P₂`
excludes the degenerate cases (`κ ∩ τ₃ ≠ ∅`, or `E₂E₃ = 1`) which both make `E` a `κ`-group, hence
`κ(M) = π(M)∖σ(M)` (`kappa_eq_sigmaComplementPrimes_of_isPiGroup_card_E`), i.e. type-`P₁`.  In the
remaining case `κ ⊆ τ₁`, `E₁` is the `κ`-Hall (`mem_kappa_of_mem_primeFactors_card_E1`) and
`E₂E₃ = [E : E₁]` is the `(κ∪σ)'`-Hall (its prime divisors avoid `κ` as the index of the `κ`-Hall
`E₁`, and `σ` as `E` is a `σ'`-group). -/
theorem typeP2_matched_kappa_hall_pair_of_esetup [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M)
    (hsetup : OddOrder.BG.Ch3.S12.SubgroupESetup M E E₁ E₂ E₃) :
    E₁ ≤ M ∧ E₂ ⊔ E₃ ≤ E ∧ E₂ ⊔ E₃ ≠ ⊥ ∧
      Ch03.IsHallSubgroup (S14.kappa M) (E₁.subgroupOf M) ∧
      Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
        ((E₂ ⊔ E₃).subgroupOf M) ∧
      IsMulCommutative ↥(E₂ ⊔ E₃) ∧
      E₁ ≤ Subgroup.normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) := by
  classical
  have hP : S14.IsTypeP M := hP2.1
  -- `E` is a `σ(M)'`-group.
  have hEσ' : Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma M)ᶜ E :=
    hsetup.isPiGroup_sigma_compl hG
  -- `κ(M) ∩ τ₃(M) = ∅` (else `E` is a `κ`-group, giving type-`P₁`, contradicting `hP2`).
  have hτ3empty : ¬ (S14.kappa M ∩ tau3 M).Nonempty := by
    rintro ⟨p, hpκ, hpτ3⟩
    have hp : p.Prime := S14.prime_of_mem_kappa hpκ
    obtain ⟨hE3ne, hreg⟩ := S14.E3_not_regular_of_mem_kappa_tau3 hG hsetup hp hpκ hpτ3
    obtain ⟨_, _, hEprime, _⟩ := OddOrder.BG.Ch3.S13.E3_not_regular_consequences hG hsetup hE3ne
        hreg
    obtain ⟨x, hxE3, hxne, hxC⟩ : ∃ x ∈ E₃, x ≠ 1 ∧
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
      by_contra hcon; push Not at hcon; exact hreg fun y hy hy1 => hcon y hy hy1
    exact hP2.2 (S14.kappa_eq_sigmaComplementPrimes_of_isPiGroup_card_E hG hsetup
      (fun q hq => S14.mem_kappa_of_mem_primeFactors_card_E hG hsetup hEprime hxE3 hxne hxC hq))
  have hκτ1 : ∀ p ∈ S14.kappa M, p ∈ tau1 M := fun p hpκ =>
    (S14.kappa_subset_tau1_union_tau3 hpκ).resolve_right (fun hpτ3 => hτ3empty ⟨p, hpκ, hpτ3⟩)
  -- `E₁` acts prime/non-regularly on `M_σ`; `E₁` is the `κ`-Hall of `E`, hence of `M`.
  obtain ⟨p₀, hp₀κ⟩ := hP
  obtain ⟨hE1ne, hE1nonreg⟩ := S14.E1_not_regular_of_mem_kappa_tau1 hG hsetup
    (S14.prime_of_mem_kappa hp₀κ) hp₀κ (hκτ1 p₀ hp₀κ)
  have hE1prime := OddOrder.BG.Ch3.S13.E1_actsPrime hG hsetup hE1ne
  have hCE1 : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥ :=
    S14.Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hE1prime (le_refl E₁) hE1nonreg
  have hE1HallκE : Ch03.IsHallSubgroup (S14.kappa M) (E₁.subgroupOf E) :=
    ⟨fun p hp => S14.mem_kappa_of_mem_primeFactors_card_E1 hG hsetup hE1prime hCE1
        (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E₁_le).toEquiv] at hp),
      fun p hp hpκ => hsetup.E₁_hall.2 p hp (hκτ1 p hpκ)⟩
  have hK₀ : Ch03.IsHallSubgroup (S14.kappa M) (E₁.subgroupOf M) :=
    hallPiece_isHall_in_M hG hsetup hsetup.E₁_le hE1HallκE S14.kappa_subset_sigmaCompl
  set U₀ : Subgroup G := E₂ ⊔ E₃ with hU₀def
  have hU₀leE : U₀ ≤ E := sup_le hsetup.E₂_le hsetup.E₃_le
  -- `|E| = |E₁| · |U₀|` (the `τ₁` vs `τ₂∪τ₃` factorisation; `E₁ ⊓ U₀ = 1` by coprimality).
  have hc1E : Nat.card ↥(E₁.subgroupOf E) = Nat.card ↥E₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E₁_le).toEquiv
  have hc2E : Nat.card ↥(E₂.subgroupOf E) = Nat.card ↥E₂ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E₂_le).toEquiv
  have hc3E : Nat.card ↥(E₃.subgroupOf E) = Nat.card ↥E₃ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E₃_le).toEquiv
  have hcardE : Nat.card ↥E = Nat.card ↥E₁ * Nat.card ↥U₀ := by
    have hEsup : E = E₁ ⊔ E₂ ⊔ E₃ := (subgroupE_basic hG hsetup).2.2.2.2.1.1
    have hEnormE3 : E ≤ Subgroup.normalizer (E₃ : Set G) := (subgroupE_basic hG hsetup).2.1.2
    have hcop2 : Nat.Coprime (Nat.card ↥E₁) (Nat.card ↥E₂) := by
      by_contra hnc
      obtain ⟨s, hs, hsm, hsn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
      have := tau1_pRank_eq_one (hsetup.E₁_hall.1 s
        (hc1E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsm, Nat.card_pos.ne'⟩))
      have := tau2_pRank_eq_two (hsetup.E₂_hall.1 s
        (hc2E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsn, Nat.card_pos.ne'⟩))
      omega
    have hcop3 : Nat.Coprime (Nat.card ↥E₁) (Nat.card ↥E₃) := by
      by_contra hnc
      obtain ⟨s, hs, hsm, hsn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
      exact not_mem_tau3_of_mem_tau1
        (hsetup.E₁_hall.1 s (hc1E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsm, Nat.card_pos.ne'⟩))
        (hsetup.E₃_hall.1 s (hc3E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsn, Nat.card_pos.ne'⟩))
    have hE23disj : E₂ ⊓ E₃ = ⊥ := by
      have hd1 : Nat.card ↥(E₂ ⊓ E₃) ∣ Nat.card ↥E₂ := Subgroup.card_dvd_of_le inf_le_left
      have hd2 : Nat.card ↥(E₂ ⊓ E₃) ∣ Nat.card ↥E₃ := Subgroup.card_dvd_of_le inf_le_right
      have hcop23 : Nat.Coprime (Nat.card ↥E₂) (Nat.card ↥E₃) := by
        by_contra hnc
        obtain ⟨s, hs, hsm, hsn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
        have := tau2_pRank_eq_two (hsetup.E₂_hall.1 s
          (hc2E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsm, Nat.card_pos.ne'⟩))
        have := tau3_pRank_eq_one (hsetup.E₃_hall.1 s
          (hc3E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsn, Nat.card_pos.ne'⟩))
        omega
      exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp (hcop23 ▸ Nat.dvd_gcd hd1 hd2))
    have hcard23 : Nat.card ↥U₀ = Nat.card ↥E₂ * Nat.card ↥E₃ :=
      card_sup_eq_mul_of_le_normalizer_of_disjoint (hsetup.E₂_le.trans hEnormE3) hE23disj
    have hE1_23_disj : E₁ ⊓ U₀ = ⊥ := by
      have hd1 : Nat.card ↥(E₁ ⊓ U₀) ∣ Nat.card ↥E₁ := Subgroup.card_dvd_of_le inf_le_left
      have hd2 : Nat.card ↥(E₁ ⊓ U₀) ∣ Nat.card ↥U₀ := Subgroup.card_dvd_of_le inf_le_right
      have hcop : Nat.Coprime (Nat.card ↥E₁) (Nat.card ↥U₀) :=
        hcard23 ▸ Nat.Coprime.mul_right hcop2 hcop3
      exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hd1 hd2))
    have hE1normU0 : E₁ ≤ Subgroup.normalizer (U₀ : Set G) :=
      hsetup.E₁_le.trans (hsetup.E23_normal hG)
    have hsupEq : E₁ ⊔ U₀ = E := by rw [hU₀def, ← sup_assoc, ← hEsup]
    rw [← hsupEq, card_sup_eq_mul_of_le_normalizer_of_disjoint hE1normU0 hE1_23_disj]
  -- index facts `[E:E₁] = |U₀|`, `[E:U₀] = |E₁|`.
  have hidxE1 : (E₁.subgroupOf E).index = Nat.card ↥U₀ := by
    have hmi := Subgroup.card_mul_index (E₁.subgroupOf E)
    rw [hc1E] at hmi
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (by rw [hmi, hcardE])
  have hidxU0 : (U₀.subgroupOf E).index = Nat.card ↥E₁ := by
    have hmi := Subgroup.card_mul_index (U₀.subgroupOf E)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU₀leE).toEquiv] at hmi
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (by rw [hmi, hcardE]; ring)
  -- `U₀` is a `(κ∪σ)'`-Hall of `E`, hence of `M`.
  have hU₀HallE : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U₀.subgroupOf E) := by
    constructor
    · intro p hp
      have hpU₀ : p ∈ (Nat.card ↥U₀).primeFactors := by
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU₀leE).toEquiv] at hp
      rw [Set.mem_compl_iff, Set.mem_union, not_or]
      refine ⟨fun hpκ => hE1HallκE.2 p (by rw [hidxE1]; exact hpU₀) hpκ, ?_⟩
      exact hEσ' p (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hU₀leE) Nat.card_pos.ne' hpU₀)
    · intro p hp
      rw [hidxU0] at hp
      exact fun hc => hc (Set.mem_union_left _ (hE1HallκE.1 p (by rwa [hc1E])))
  have hU₀ : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U₀.subgroupOf M) :=
    hallPiece_isHall_in_M hG hsetup hU₀leE hU₀HallE
      (fun p hp hpσ => hp (Or.inr hpσ))
  -- `U₀ ≠ ⊥` (else `E = E₁` is a `κ`-Hall covering all `σ'`-primes, giving type-`P₁`).
  have hU₀ne : U₀ ≠ ⊥ := by
    intro hU₀bot
    refine hP2.2 (S14.kappa_eq_sigmaComplementPrimes_of_isPiGroup_card_E hG hsetup (fun q hq => ?_))
    rw [hcardE, hU₀bot, Subgroup.card_bot, mul_one] at hq
    exact hE1HallκE.1 q (by rwa [hc1E])
  -- `U₀` abelian (Lemma 15.1(b)).
  have hU₀ab : IsMulCommutative ↥U₀ :=
    (S15.typeP_hall_derived_eq_and_abelian hG hM hsetup.E1_le_M (hU₀leE.trans hsetup.E_le)
      hE1ne hK₀ hU₀).2
  have hK₀NU₀ : E₁ ≤ Subgroup.normalizer (U₀ : Set G) :=
    hsetup.E₁_le.trans (hsetup.E23_normal hG)
  exact ⟨hsetup.E1_le_M, hU₀leE, hU₀ne, hK₀, hU₀, hU₀ab, hK₀NU₀⟩

/-- **Matched `κ`-Hall / `(κ∪σ)'`-Hall pair for a type-`P₂` maximal subgroup**
(BG `kappa_complement`;
existential form).  Obtains an arbitrary `E`-setup (`exists_subgroupESetup`) and reads off the pair
via `typeP2_matched_kappa_hall_pair_of_esetup`.  Consumers needing the pair inside a *prescribed*
`σ(M)'`-complement `E` (e.g. `E = M ⊓ N` in Corollary 15.9, so a Sylow of `U₀` lands in `M`) call
the
`_of_esetup` core with their own setup. -/
theorem typeP2_exists_matched_kappa_hall_pair [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M) :
    ∃ K₀ U₀ : Subgroup G, K₀ ≤ M ∧ U₀ ≤ M ∧ U₀ ≠ ⊥ ∧
      Ch03.IsHallSubgroup (S14.kappa M) (K₀.subgroupOf M) ∧
      Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U₀.subgroupOf M) ∧
      IsMulCommutative ↥U₀ ∧
      K₀ ≤ Subgroup.normalizer (U₀ : Set G) := by
  obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := exists_subgroupESetup hG hM
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    typeP2_matched_kappa_hall_pair_of_esetup hG hM hP2 hsetup
  exact ⟨E₁, E₂ ⊔ E₃, h1, h2.trans hsetup.E_le, h3, h4, h5, h6, h7⟩

/-- **BG Theorem C** (mmd L4303): when `K ≠ 1`, `M` has a paired maximal
subgroup `Mstar`, the cyclic product `Z = K Kstar`, a TI set `Z_tilde`, and the
associated type-P duality.

**Faithfulness fixes (2026-06-21, lane F).**

* **Hypotheses `hKM : K ≤ M`, `hUM : U ≤ M`.**  In BG, `K` is the cyclic Hall
  `κ(M)`-subgroup *of* `M` and `U` the Hall `(κ(M) ∪ σ(M))'`-subgroup *of* `M`
  (`M = K U M_σ`), so `K, U ≤ M`.  The `…subgroupOf M` Hall hypotheses constrain
  only `K ⊓ M`, `U ⊓ M`, so they do **not** force `K, U ≤ M`; without them conjunct 7
  (`M' = U ⊔ M_σ`) is false for `U ⊄ M`.  The landed §14/§15 lemmas
  (`typeP_duality`, `typeP_kstar_in_mf`, `typeP_hall_derived_eq_and_abelian`) all
  take these explicitly, so they are added here and threaded through the only
  callers (`theoremII_tame_embedding{,_of_inputs}`).

* **The `∃! Mstar` clause is strengthened to the faithful `typeP_duality` predicate.**
  The previous scaffold pinned `Mstar` only by `maximal ∧ type-P ∧ ¬conj M Mstar ∧
  (type-P₂ M ∨ type-P₂ Mstar)`; since every `G`-conjugate of the partner satisfies
  that predicate (and `N_G(M*) = M* ⊊ G`), the conjunction had **no unique** witness —
  the `∃!` was false as stated.  BG Theorem C(4)-(7),(11) pins `Mstar` by the dual
  Hall datum `K* ≤ M*`, `K*` Hall-`κ(M*)`, `K = M*_σ ⊓ C_G(K*)`, which is exactly
  Theorem 14.7 (`typeP_duality`); that is the predicate used here.  The sole callers
  (`theoremII_tame_embedding_of_inputs`) project out only the TI conjunct, so the
  strengthening does not affect them.

Proof: conjuncts 1,7 from Lemma 15.1(b) (`typeP_hall_derived_eq_and_abelian`),
conjuncts 3-6,8 from Corollary 15.6 (`typeP_kstar_in_mf`), conjunct 9 from
Theorem 14.7 (`typeP_duality`).  The residual conjuncts are the genuinely deep
§14/§16 endpoints not yet available as standalone lemmas: conjunct 2 (`N_G(U) ⊄ M`,
BG Theorem C(1) / Corollary 14.12), conjunct 10 (`A_0(M) - A(M)` TI, BG Theorem A(3),(5)
/ Proposition 14.2(d)), conjunct 11 (`U ≠ 1 → |K|` prime ∧ `F(M)` TI, BG Theorem C(10)
= Proposition 14.2(g) + Theorem 15.7(a)), and conjunct 12 (`U = 1 → |K*|` prime, BG
Theorem C(8), pending the `IsTypeP1`-from-`U = ⊥` bridge). -/
theorem theoremC_paired_structure [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hKne : K ≠ ⊥) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M)) :
    IsMulCommutative ↥U ∧ ¬ Subgroup.normalizer (U : Set G) ≤ M ∧
      Kstar ≠ ⊥ ∧ IsCyclic ↥Kstar ∧ Kstar ≤ S15.MF M ∧ ¬ IsCyclic ↥(S15.MF M) ∧
      derivedInG M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M ∧
      Kstar ≤ derivedInG (derivedInG M) ∧
      (∃! Mstar : Subgroup G,
        Mstar ∈ maximalSubgroups G ∧ S14.IsTypeP Mstar ∧
          ¬ S14.IsConjugateSubgroup M Mstar ∧
          (Kstar ≤ Mstar ∧ Ch03.IsHallSubgroup (S14.kappa Mstar) (Kstar.subgroupOf Mstar) ∧
            K = OddOrder.BG.Ch3.S10.Msigma Mstar ⊓ Subgroup.centralizer (Kstar : Set G)) ∧
          IsCyclic ↥(K ⊔ Kstar) ∧ IsTISubset (S14.zTilde K Kstar) (K ⊔ Kstar) ∧
          (S14.IsTypeP2 M ∨ S14.IsTypeP2 Mstar) ∧
          (∀ H : Subgroup G, H ∈ maximalSubgroups G → S14.IsTypeP H →
            S14.IsConjugateSubgroup H M ∨ S14.IsConjugateSubgroup H Mstar)) ∧
      IsTISubset (A0Set M K \ ASet M U) M ∧
      (U ≠ ⊥ → ∃ p : ℕ, p.Prime ∧ Nat.card ↥K = p ∧ S15.FittingIsTI M) ∧
      (U = ⊥ → ∃ q : ℕ, q.Prime ∧ Nat.card ↥Kstar = q) := by
  classical
  -- `IsTypeP M` from the nonempty `κ`-Hall factor `K`.
  have hKofne : K.subgroupOf M ≠ ⊥ := by
    rw [ne_eq, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hKne (hd.eq_bot_of_le hKM)
  have hP : S14.IsTypeP M := isTypeP_of_isHall_kappa_subgroupOf_ne_bot hK hKofne
  -- Conjuncts 1, 7 (Lemma 15.1(b)): `U` abelian and `M' = U ⊔ M_σ`.
  obtain ⟨hM'eq, hUab⟩ := typeP_hall_derived_eq_and_abelian hG hM hKM hUM hKne hK hU
  -- Conjuncts 3,4,5,8,6 (Corollary 15.6): `K*` nontrivial cyclic `≤ M_F`, `K* ≤ M''`, `M_F` not
  -- cyclic.
  obtain ⟨hKsne, hKscyc, hKsMF, hKsdd, hMFnc⟩ := typeP_kstar_in_mf hG hM hP hKM hK hKstar
  -- Conjunct 9 (Theorem 14.7): the unique non-conjugate type-`P` partner `M*`.
  have hdual := (typeP_duality hG hM hP hKM hK hKstar).2.2
  refine ⟨hUab, ?_, hKsne, hKscyc, hKsMF, hMFnc, hM'eq, hKsdd, hdual, ?_, ?_, ?_⟩
  · -- Conjunct 2 (BG Theorem C(1) / Corollary 14.12): `N_G(U) ⊄ M`.
    by_cases hUbot : U = ⊥
    · -- `U = ⊥` (type-`P₁`): `N_G(⊥) = ⊤ ⊄ M` since `M` is a proper (maximal) subgroup.
      subst hUbot
      intro hle
      have htop : (⊤ : Subgroup G) ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
        intro g _
        rw [Subgroup.mem_normalizer_iff]
        intro h
        simp [Subgroup.mem_bot]
      exact (mem_maximalSubgroups.mp hM).1 (top_le_iff.mp (htop.trans hle))
    · -- `U ≠ ⊥` (type-`P₂`): `N_G(U) ⊄ M` is BG Corollary 14.12.  We produce a *matched*
      -- `κ`-Hall / `(κ∪σ)'`-Hall pair `(K₀, U₀)` (with `K₀ ≤ N_G(U₀)`, the hypothesis Corollary
      -- 14.12 consumes), apply 14.12 to get `N_G(U₀) ⊄ M`, then transport along the `M`-conjugacy
      -- `U₀ ~ U` of `(κ∪σ)'`-Hall subgroups.
      have hUne' : U.subgroupOf M ≠ ⊥ := by
        rw [ne_eq, Subgroup.subgroupOf_eq_bot]
        exact fun hd => hUbot (hd.eq_bot_of_le hUM)
      have hP2 : S14.IsTypeP2 M := isTypeP2_of_hall_subgroupOf_ne_bot hP hU hUne'
      obtain ⟨K₀, U₀, hK₀M, hU₀M, hU₀ne, hK₀, hU₀, hU₀ab, hK₀NU₀⟩ :=
        typeP2_exists_matched_kappa_hall_pair hG hM hP2
      have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
      have : Group.IsSolvable ↥U₀ :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hU₀M)
      -- a prime `r ∣ |U₀|` and a Sylow (= Hall `{r}`) subgroup `R₀ ≤ U₀`.
      have hU₀card : Nat.card ↥U₀ ≠ 1 := fun h => hU₀ne (Subgroup.card_eq_one.mp h)
      obtain ⟨r, hr⟩ : (Nat.card ↥U₀).primeFactors.Nonempty :=
        Nat.nonempty_primeFactors.mpr
          (lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne') (Ne.symm hU₀card))
      obtain ⟨R', hR'⟩ := Ch03.hall_E_exists (G := ↥U₀) ({r} : Set ℕ)
      have hR₀sub : ((R'.map U₀.subtype).subgroupOf U₀) = R' :=
        Subgroup.comap_map_eq_self_of_injective U₀.subtype_injective R'
      have hR₀ : Ch03.IsHallSubgroup ({r} : Set ℕ) ((R'.map U₀.subtype).subgroupOf U₀) := by
        rw [hR₀sub]; exact hR'
      have hU₀ab' : ∀ a ∈ U₀, ∀ b ∈ U₀, a * b = b * a := fun a ha b hb =>
        congrArg Subtype.val (isMulCommutative_iff.mp hU₀ab (⟨a, ha⟩ : ↥U₀) ⟨b, hb⟩)
      obtain ⟨H, _, _, _, _, hHNU₀⟩ :=
        S14.typeP2_neighbor_is_typeF hG hM hP2 hK₀M hU₀M hK₀ hU₀ hU₀ab' hr (Subgroup.map_subtype_le
            _)
          hR₀ hK₀NU₀
      -- Transport `N_G(U) ⊄ M` (assumed `≤`, for contradiction) to `N_G(U₀) ≤ M`.
      intro hle
      apply hHNU₀
      obtain ⟨w, hwM, hw⟩ := OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf
        inferInstance hU₀M hUM hU₀ hU
      refine le_trans inf_le_right ?_
      intro n hn
      have hn_fix : MulAut.conj n • U₀ = U₀ := conj_smul_eq_self_of_mem_normalizer hn
      have hwinv : MulAut.conj w⁻¹ • U = U₀ := by
        rw [← hw, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
      have hfix : MulAut.conj (w * n * w⁻¹) • U = U := by
        rw [map_mul, map_mul, mul_smul, mul_smul, hwinv, hn_fix, hw]
      have hwnwM : w * n * w⁻¹ ∈ M := hle (mem_normalizer_of_conj_smul_eq_self hfix)
      have hn' : n = w⁻¹ * (w * n * w⁻¹) * w := by group
      rw [hn']
      exact M.mul_mem (M.mul_mem (M.inv_mem hwM) hwnwM) hwM
  · -- Conjunct 10 (BG Theorem C(9)): `A_0(M) - A(M) = 𝒞_M(Ẑ)` is a TI-subset of `M`.  Reduce to the
    -- structural inclusion `A_0(M) - A(M) ⊆ 𝒞_M(Ẑ)` (`a0_minus_a_subset_conj_zTilde`) plus the
    -- TI-ness of `Ẑ` (`typeP_duality`; `N_G(Ẑ) = K ⊔ K* ≤ M`), via the transport lemma.
    obtain ⟨Mstar, hMstarP⟩ := hdual.exists
    have hZti : OddOrder.GroupTheory.IsTISubset (S14.zTilde K Kstar) (K ⊔ Kstar) :=
      hMstarP.2.2.2.2.2.1
    have hKstarMσ : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M := by rw [hKstar]; exact inf_le_left
    have hZM : (K ⊔ Kstar : Subgroup G) ≤ M :=
      sup_le hKM (hKstarMσ.trans (OddOrder.BG.Ch3.S10.Msigma_le M))
    exact hZti.of_subset_conj_of_isTISubset hZM
      (a0_minus_a_subset_conj_zTilde hG hM hP hKM hUM hK hKstar hU)
  · -- Conjunct 11 (BG Theorem C(10) = Prop 14.2(g) + Theorem 15.7(a)):
    -- `U ≠ ⊥ → |K|` prime ∧ `F(M)` TI.
    -- `U ≠ ⊥` makes `M` type-`P₂`; `|K| = q` prime is Prop 14.2's type-`P₂` clause.  The
    -- `FittingIsTI M` conjunct (BG Theorem C(10), via Theorem 15.7(a)) is the residual.
    intro hUne
    have hUne' : U.subgroupOf M ≠ ⊥ := by
      rw [ne_eq, Subgroup.subgroupOf_eq_bot]
      exact fun hd => hUne (hd.eq_bot_of_le hUM)
    have hP2 : S14.IsTypeP2 M := isTypeP2_of_hall_subgroupOf_ne_bot hP hU hUne'
    obtain ⟨q, hq, hKq, _⟩ := ((S14.typeP_structure hG hM hP hKM hK hKstar hU).2.2.2.2.1 hP2).2
    -- `FittingIsTI M` for type-`P₂`: BG Theorem 15.7(a) (`fittingIsTI_of_isTypeP2`).
    exact ⟨q, hq, hKq, S15.fittingIsTI_of_isTypeP2 hG hM hP2⟩
  · -- Conjunct 12 (BG Theorem C(8) = `kstar_card_prime_of_inputs`): `U = ⊥ → |K*|` prime.
    -- `U = ⊥` makes `M` type-`P₁` (`κ(M) = σ(M)'` via the trivial Hall complement), then `|K*|`
    -- prime.
    intro hUbot
    have hUbot' : U.subgroupOf M = ⊥ := by simp [hUbot]
    have hP1 : S14.IsTypeP1 M :=
      ⟨hP, kappa_eq_sigmaComplementPrimes_of_hall_subgroupOf_eq_bot hU hUbot'⟩
    exact ⟨Nat.card ↥Kstar, kstar_card_prime_of_inputs hG hM hP1 hKM hK hKstar, rfl⟩

/-- **BG Theorem D(1), `M_σ`-fusion control** (mmd L4317, the first conjunct of
`theoremD_msigma_conjugacy_and_centralizers`): two elements of `M_σ` conjugate in `G` are already
conjugate by an element of `M`.  This is the one Theorem-D conjunct that is unconditional given
Corollary 15.3: applying `mf_hall_centralizer_control` (Cor 15.3(b), sorry-free) to the trivial
Hall subgroup `H := M_σ` of `M_σ` gives `N_G(M_σ)`-fusion, and `N_G(M_σ) = M`
(`normalizer_Msigma_eq_self`) upgrades it to `M`-fusion.  Standalone and reusable; the remaining
Theorem-D conjuncts D(2) (Lemma 12.17) / D(3)(4) (the `R(x)` signalizer normal complement, deep) are
isolated in `theoremD_msigma_conjugacy_and_centralizers_of_inputs` (issue 8019). -/
theorem msigma_fusion_control [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    ∀ x ∈ OddOrder.BG.Ch3.S10.Msigma M, ∀ y ∈ OddOrder.BG.Ch3.S10.Msigma M,
      (∃ g : G, y = g * x * g⁻¹) → ∃ m ∈ M, y = m * x * m⁻¹ := by
  -- `M_σ` is (trivially) a `piSet`-Hall subgroup of itself.
  have hHall : Ch03.IsHallSubgroup (S14.piSet (OddOrder.BG.Ch3.S10.Msigma M))
      ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) := by
    rw [Subgroup.subgroupOf_self, Ch03.IsHallSubgroup.top_iff]
    exact fun p hp => hp
  intro x hx y hy hconj
  -- Corollary 15.3(b) at `H := M_σ`: `N_G(M_σ)`-fusion; then `N_G(M_σ) = M`.
  obtain ⟨n, hnN, hnconj⟩ :=
    (mf_hall_centralizer_control hG hM le_rfl hHall (OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM)).2
      x hx y hy hconj
  rw [normalizer_Msigma_eq_self hG hM] at hnN
  exact ⟨n, hnN, hnconj⟩

/-- **Dichotomy `|𝓜_σ(x)| ≤ 1 ⟹ C_G(x) ≤ M`** (the converse of
`maximalSigmaSubgroupsOfElement_eq_singleton_of_centralizer_le`, Coq Theorem 14.4's `not_sCX_M`
direction): for `x ∈ M_σ^#` with at most one `σ`-maximal, `C_G(x) ≤ M`.  If some
`c ∈ C_G(x)` escaped
`M`, then `Mᶜ` would be a second `σ`-maximal of `x` — `x ∈ Mᶜ` (as `c⁻¹xc = x ∈ M`), so `Mᶜ` is a
maximal conjugate containing `x`, hence in `𝓜_σ(x)` (`maximalConjugatesContaining_eq_maximalSigma`),
and `Mᶜ ≠ M` (else `c ∈ N_G(M) = M`) — contradicting `|𝓜_σ(x)| ≤ 1`.  Much shallower than the Coq
proof's `C(X)`-orbit count: this direction needs only `N_G(M) = M` (maximal self-normalizing,
inlined). -/
theorem centralizer_le_of_maximalSigma_le_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {x : G}
    (hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hx1 : x ≠ 1)
    (hle : (S14.maximalSigmaSubgroupsOfElement x).ncard ≤ 1) :
    Subgroup.centralizer ({x} : Set G) ≤ M := by
  have hMne : M ≠ ⊥ := fun h =>
    OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM (le_bot_iff.mp (h ▸ OddOrder.BG.Ch3.S10.Msigma_le M))
  -- `N_G(M) = M`: `M ≤ N_G(M)`, and a proper inclusion forces `M ◁ G` (maximality), excluded by
  -- simplicity (`M ≠ ⊥, ⊤`).
  have hNM : Subgroup.normalizer (M : Set G) = M := by
    refine le_antisymm ?_ Subgroup.le_normalizer
    rcases eq_or_lt_of_le (Subgroup.le_normalizer (H := M)) with heq | hlt
    · exact le_of_eq heq.symm
    · have hnorm : M.Normal :=
        Subgroup.normalizer_eq_top_iff.mp ((mem_maximalSubgroups.mp hM).2 _ hlt)
      rcases hG.simple.eq_bot_or_eq_top_of_normal _ hnorm with hbot | htop
      · exact absurd hbot hMne
      · exact absurd htop (mem_maximalSubgroups.mp hM).1
  -- `conj c • M = M → c ∈ N_G(M)`.
  have hconj_mem : ∀ c : G, MulAut.conj c • M = M → c ∈ Subgroup.normalizer (M : Set G) := by
    intro c hcfix
    rw [Subgroup.mem_normalizer_iff]
    intro n
    have key : MulAut.conj c • n ∈ MulAut.conj c • M ↔ n ∈ M :=
      Subgroup.smul_mem_pointwise_smul_iff
    rw [hcfix, show (MulAut.conj c • n) = (MulAut.conj c) n from rfl, MulAut.conj_apply] at key
    exact key.symm
  intro c hc
  by_contra hcM
  have hMmem : M ∈ S14.maximalSigmaSubgroupsOfElement x := ⟨hM, hxMσ⟩
  -- `Mᶜ ∈ 𝓜_σ(x)`: `x ∈ Mᶜ` since `c⁻¹xc = x ∈ M`.
  have hxcM : x ∈ MulAut.conj c • M := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hcalc : (MulAut.conj c)⁻¹ • x = c⁻¹ * x * c := by
      change (MulAut.conj c).symm x = _
      rw [MulAut.conj_symm_apply]
    rw [hcalc]
    have hcx : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hxconj : c⁻¹ * x * c = x := by rw [mul_assoc, ← hcx]; group
    rw [hxconj]
    exact OddOrder.BG.Ch3.S10.Msigma_le M hxMσ
  have hconjmem : MulAut.conj c • M ∈ S14.maximalSigmaSubgroupsOfElement x := by
    rw [← maximalConjugatesContaining_eq_maximalSigma hG hM hxMσ hx1]
    exact ⟨c, rfl, hxcM⟩
  -- two members of a `≤ 1`-element set coincide, so `c ∈ N_G(M) = M`.
  have heq : MulAut.conj c • M = M :=
    (Set.ncard_le_one (Set.toFinite _)).mp hle _ hconjmem _ hMmem
  exact hcM (hNM ▸ hconj_mem c heq)

/-- **BG Theorem D(3), full `hD3`** (`∀ x ∈ M_σ^#, ∃ R, RData M x R`): combine the two branches of
the `|𝓜_σ(x)|` dichotomy.  When `|𝓜_σ(x)| > 1`, `RData_of_gt_one` supplies the signalizer `R(x)`;
when `|𝓜_σ(x)| ≤ 1`, the dichotomy gives `C_G(x) ≤ M`, whereupon `R = ⊥` works: `C_M(x) = C_G(x)`
is all of `C_G(x)` (conjunct 1 trivial, conjunct 3 is `⊤ ⋊ ⊥`), `⊥ ◁ C_G(x)`, and `𝓜_σ(x) = {M}`
makes sharp transitivity vacuous. -/
theorem exists_RData_of_mem_sigmaSharp [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    ∀ x : G, x ∈ S14.sigmaSharp M → ∃ R : Subgroup G, RData M x R := by
  intro x hx
  have hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M := hx.1
  have hx1 : x ≠ 1 := hx.2
  by_cases hgt : 1 < (S14.maximalSigmaSubgroupsOfElement x).ncard
  · exact RData_of_gt_one hG hM hx hgt
  · have hCxM : Subgroup.centralizer ({x} : Set G) ≤ M :=
      centralizer_le_of_maximalSigma_le_one hG hM hxMσ hx1 (not_lt.mp hgt)
    have hMCx : M ⊓ Subgroup.centralizer ({x} : Set G) = Subgroup.centralizer ({x} : Set G) :=
      inf_eq_right.mpr hCxM
    have hc1 : Nat.Coprime
        (Nat.card ↥((M ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
          (Subgroup.centralizer ({x} : Set G))))
        ((M ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
          (Subgroup.centralizer ({x} : Set G))).index := by
      rw [hMCx, Subgroup.subgroupOf_self, Subgroup.index_top]; exact Nat.coprime_one_right _
    have hc2 : ((⊥ : Subgroup G).subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal := by
      rw [Subgroup.bot_subgroupOf]; infer_instance
    have hc3 : Subgroup.IsComplement'
        ((M ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf (Subgroup.centralizer ({x} : Set G)))
        ((⊥ : Subgroup G).subgroupOf (Subgroup.centralizer ({x} : Set G))) := by
      rw [hMCx, Subgroup.subgroupOf_self, Subgroup.bot_subgroupOf]
      exact Subgroup.isComplement'_top_bot
    have hc4 : ConjSharplyTransitiveOn (⊥ : Subgroup G) (maximalConjugatesContaining M x) := by
      have hsingle : maximalConjugatesContaining M x = {M} := by
        rw [maximalConjugatesContaining_eq_maximalSigma hG hM hxMσ hx1]
        exact maximalSigmaSubgroupsOfElement_eq_singleton_of_centralizer_le hG hM hxMσ hx1 hCxM
      rw [hsingle]
      intro A hA B hB
      rw [Set.mem_singleton_iff] at hA hB
      subst hA; subst hB
      exact ⟨1, ⟨Subgroup.mem_bot.mpr rfl, by rw [map_one, one_smul]⟩,
        fun r hr => Subgroup.mem_bot.mp hr.1⟩
    exact ⟨⊥, hc1, hc2, hc3, hc4⟩

/-- **BG Theorem E, `σ(Mᵢ)`-disjointness conjunct** (mmd L4370): distinct
representatives of the conjugacy classes of maximal subgroups have disjoint
`σ`-sets.  This is the `σ(Mᵢ)` "disjoint union" piece of Theorem E, and it is
**already unconditional**: distinct class representatives are non-conjugate (forced
by the `∃!` uniqueness in `hreps` — both `Mᵢ` and `Mⱼ` would be *the* representative
of `Mᵢ`'s class), so BG Theorem 13.9
(`OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate`, landed sorry-free) applies
directly.  `hrepsMax` records that the representatives are themselves maximal
subgroups (the hypothesis Theorem 13.9 needs); it holds for any genuine set of
conjugacy-class representatives. -/
theorem sigma_reps_pairwise_disjoint [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {reps : Set (Subgroup G)}
    (hrepsMax : ∀ Mi ∈ reps, Mi ∈ maximalSubgroups G)
    (hreps : ∀ H : Subgroup G, H ∈ maximalSubgroups G →
      ∃! Mi : Subgroup G, Mi ∈ reps ∧ S14.IsConjugateSubgroup H Mi)
    {Mi Mj : Subgroup G} (hMi : Mi ∈ reps) (hMj : Mj ∈ reps) (hne : Mi ≠ Mj) :
    OddOrder.BG.Ch3.S10.sigma Mi ∩ OddOrder.BG.Ch3.S10.sigma Mj = ∅ := by
  rw [← Set.disjoint_iff_inter_eq_empty]
  refine OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG
    (hrepsMax Mi hMi) (hrepsMax Mj hMj) ?_
  intro hconj
  obtain ⟨Z₀, _, huniq⟩ := hreps Mi (hrepsMax Mi hMi)
  exact hne ((huniq Mi ⟨hMi, S14.IsConjugateSubgroup.refl Mi⟩).trans
    (huniq Mj ⟨hMj, hconj⟩).symm)

/-- **BG Theorem E, the `π(G)` cover** (mmd L4370, clause (a1)): for a system of conjugacy-class
representatives `reps` of the maximal subgroups, a prime `p` divides `|G|` iff `p ∈ σ(Mᵢ)` for some
representative `Mᵢ`.  Forward: a prime `p ∣ |G|` is a `σ`-prime of *some* maximal subgroup `M`
(`exists_mem_sigma_of_prime_dvd_card`, BG §1 — a Sylow `p`-subgroup is non-normal, so its normalizer
lies in a maximal `M` with `p ∈ σ(M)`), and `σ` is conjugation-equivariant (`sigma_conj`), so the
representative `Mᵢ` conjugate to `M` also has `p ∈ σ(Mᵢ)`.  Reverse: `σ(Mᵢ) ⊆ π(|Mᵢ|)`
(`mem_sigma_iff`) and `|Mᵢ| ∣ |G|` (Lagrange).  Together with `sigma_reps_pairwise_disjoint`
(clause (a2)) this is the full `π(G)` partition by the `σ(Mᵢ)` — the partition core of BG Theorem E
(`theoremE_sigma_partition_and_counting`, issue 8019). -/
theorem sigma_reps_prime_cover [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {reps : Set (Subgroup G)}
    (_hrepsMax : ∀ Mi ∈ reps, Mi ∈ maximalSubgroups G)
    (hreps : ∀ H : Subgroup G, H ∈ maximalSubgroups G →
      ∃! Mi : Subgroup G, Mi ∈ reps ∧ S14.IsConjugateSubgroup H Mi)
    (p : ℕ) :
    p ∈ (Nat.card G).primeFactors ↔ ∃ Mi : Subgroup G, Mi ∈ reps ∧ p ∈ OddOrder.BG.Ch3.S10.sigma
        Mi := by
  constructor
  · -- `p ∣ |G|` ⟹ `p ∈ σ(M)` for some maximal `M` ⟹ `p ∈ σ(Mᵢ)` for its representative.
    intro hp
    have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    obtain ⟨M, hMmax, hpM⟩ :=
      S14.exists_mem_sigma_of_prime_dvd_card hG (Nat.dvd_of_mem_primeFactors hp)
    obtain ⟨Mi, ⟨hMirep, g, hg⟩, _⟩ := hreps M hMmax
    exact ⟨Mi, hMirep, hg ▸ OddOrder.BG.Ch3.S10.sigma_conj g hpM⟩
  · -- `p ∈ σ(Mᵢ) ⊆ π(|Mᵢ|)` and `|Mᵢ| ∣ |G|`.
    rintro ⟨Mi, hMirep, hpMi⟩
    have hpMiPF : p ∈ (Nat.card ↥Mi).primeFactors :=
      ((OddOrder.BG.Ch3.S10.mem_sigma_iff Mi p).mp hpMi).1
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hpMiPF,
      (Nat.dvd_of_mem_primeFactors hpMiPF).trans (Subgroup.card_subgroup_dvd_card Mi),
      (Nat.card_pos).ne'⟩

/-- **`π(M_σ) = σ(M)`** (the prime-factor content of `M_σ` being the `σ(M)`-Hall subgroup,
BG (8.11) /
`Msigma_isHall`): a prime divides `|M_σ|` iff it is a `σ`-prime of `M`.  Forward is the `π`-part of
the Hall property (`Msigma_isHall.1`); backward, a `σ`-prime `p` divides `|M|` (`mem_sigma_iff`)
hence
`|G|`, but not the `σ′`-index `[G : M_σ]` (`Msigma_isHall.2`), so by `|G| = |M_σ|·[G : M_σ]` it
divides `|M_σ|`.  Bridges the `σ`-stated partition (`sigma_reps_prime_cover`) to the
`π(mainSubgroup ·)` form of `BGTheoremECoverData` via Peterfalvi (8.10)
(`M_s = M_σ`, issue 8020). -/
theorem primeFactors_Msigma_eq_sigma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (p : ℕ) :
    p ∈ (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)).primeFactors ↔
      p ∈ OddOrder.BG.Ch3.S10.sigma M := by
  have hHall := OddOrder.BG.Ch3.S10.Msigma_isHall hG hM
  refine ⟨fun hp => hHall.1 p hp, fun hp => ?_⟩
  have hpM : p ∈ (Nat.card ↥M).primeFactors := ((OddOrder.BG.Ch3.S10.mem_sigma_iff M p).mp hp).1
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpM
  have hpG : p ∣ Nat.card G :=
    (Nat.dvd_of_mem_primeFactors hpM).trans (Subgroup.card_subgroup_dvd_card M)
  have hpnidx : ¬ p ∣ (OddOrder.BG.Ch3.S10.Msigma M).index := fun hdvd =>
    hHall.2 p (Nat.mem_primeFactors.mpr ⟨hpprime, hdvd, Subgroup.index_ne_zero_of_finite⟩) hp
  rw [← Subgroup.card_mul_index (OddOrder.BG.Ch3.S10.Msigma M)] at hpG
  exact Nat.mem_primeFactors.mpr
    ⟨hpprime, (hpprime.dvd_mul.mp hpG).resolve_right hpnidx, Nat.card_pos.ne'⟩

/-- **A system of conjugacy-class representatives of the maximal subgroups exists** (the `reps`
hypothesis of BG Theorem E, issue 8019).  Subgroup conjugacy `IsConjugateSubgroup` is an equivalence
relation (`isConjugateSubgroup_equivalence`) on the finite type of maximal subgroups; taking the
quotient and its canonical representatives `Quotient.out` yields a set `reps` of maximal subgroups
such that every maximal subgroup is conjugate to a *unique* representative.  Discharges the `hreps`
input of `sigma_reps_prime_cover` / `sigma_reps_pairwise_disjoint` (and of
`theoremE_sigma_partition_and_counting` / `bgTheoremE_cover_data`), making the `π(G)` partition
unconditional (`exists_reps_sigma_partition`). -/
theorem exists_maximal_conjugacy_reps [Finite G] :
    ∃ reps : Set (Subgroup G),
      (∀ Mi ∈ reps, Mi ∈ maximalSubgroups G) ∧
      ∀ H : Subgroup G, H ∈ maximalSubgroups G →
        ∃! Mi : Subgroup G, Mi ∈ reps ∧ S14.IsConjugateSubgroup H Mi := by
  classical
  -- Conjugacy as a setoid on the (finite) subtype of maximal subgroups.
  let S := {M : Subgroup G // M ∈ maximalSubgroups G}
  let σ : Setoid S :=
    ⟨fun a b => S14.IsConjugateSubgroup a.1 b.1,
      ⟨fun a => S14.IsConjugateSubgroup.refl a.1, fun h => S14.IsConjugateSubgroup.symm h,
        fun h₁ h₂ => S14.IsConjugateSubgroup.trans h₁ h₂⟩⟩
  -- `reps` = the canonical representatives `Quotient.out` of each conjugacy class.
  refine ⟨Set.range (fun c : Quotient σ => (c.out : Subgroup G)), ?_, ?_⟩
  · rintro Mi ⟨c, rfl⟩; exact c.out.2
  · intro H hH
    refine ⟨((Quotient.mk σ ⟨H, hH⟩).out : Subgroup G), ⟨⟨Quotient.mk σ ⟨H, hH⟩, rfl⟩, ?_⟩, ?_⟩
    · -- `H` is conjugate to its representative.
      have h : S14.IsConjugateSubgroup ((Quotient.mk σ ⟨H, hH⟩).out : Subgroup G) H :=
        Quotient.exact (Quotient.out_eq (Quotient.mk σ ⟨H, hH⟩))
      exact h.symm
    · -- Any representative conjugate to `H` is *the* representative of `H`'s class.
      rintro Mi' ⟨⟨c, rfl⟩, hconj'⟩
      have hrel : @Setoid.r S σ ⟨H, hH⟩ c.out := hconj'
      have heq : Quotient.mk σ ⟨H, hH⟩ = c := by
        rw [Quotient.sound hrel]; exact Quotient.out_eq c
      rw [heq]

/-- The `𝒞_G(M̃)` cover taken over *all* maximal subgroups equals the cover taken over a set of
conjugacy representatives `reps` (`M̃` is conjugation-equivariant, `𝒞_G` is conjugation-invariant).
The `←` direction needs `reps ⊆ maximalSubgroups`. -/
theorem mem_conjClassSet_Mtilde_maximals_iff_reps [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {reps : Set (Subgroup G)}
    (hreps_max : ∀ Mi ∈ reps, Mi ∈ maximalSubgroups G)
    (hreps : ∀ H ∈ maximalSubgroups G, ∃ Mi ∈ reps, S14.IsConjugateSubgroup H Mi) (g : G) :
    (∃ M' ∈ maximalSubgroups G,
      g ∈ conjClassSet (S14.Mtilde hG (S14.genuineSigmaDecomposition hG) M')) ↔
      (∃ Mi ∈ reps,
        g ∈ conjClassSet (S14.Mtilde hG (S14.genuineSigmaDecomposition hG) Mi)) := by
  refine ⟨fun ⟨M', hM'max, hg⟩ => ?_, fun ⟨Mi, hMirep, hg⟩ => ⟨Mi, hreps_max Mi hMirep, hg⟩⟩
  obtain ⟨Mi, hMirep, c, hc⟩ := hreps M' hM'max
  exact ⟨Mi, hMirep, by
    rw [← hc, ← S14.Mtilde_conj_smul, S14.conjClassSet_conj_smul]; exact hg⟩

end OddOrder.BG.Ch4.S16


