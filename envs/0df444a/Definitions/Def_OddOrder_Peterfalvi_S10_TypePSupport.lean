-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S10_TypePSupport
-- name    : OddOrder_Peterfalvi_S10_TypePSupport
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T11:19:40.966783+00:00
-- url     : https://prove2.me/theorems/0bcbb89a-e1d7-4897-85a5-7387d2087b68
-- title:
--   Peterfalvi (8.13) for the book-literal type-$\mathcal{P}$ support $A(M)=\bigcup_{x\in M_s^\#}C_{M'}(x)^\#$
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), §8, (8.10)/(8.13): the type-$\mathcal{P}$ counterparts of the type-I lemmas in the minimal-simple-basic file (`typeIA_subset_ASet`, `escaping_typeIA_signalizer_structure`, …), the same three (8.13) obligations for the support $A(M)=\bigcup_{x\in M_s^\#}C_{M'}(x)^\#$. It consists of lemmas only.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 7 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S10_TypePSupport.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S10_TypePSupport.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S10_MinimalSimpleBasic

namespace OddOrder.Peterfalvi.S10

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **The type-`P₂` `ASet` bridge (9008 Option A): `A(S) ⊆ ASet S U₀`** for a matched `(κ∪σ)'`-Hall
`U₀`.  Since `A(S) ⊆ M' = U₀ ⊔ M_σ` (`typeP_hall_derived_eq_and_abelian`, BG Lemma 15.1(b)) and
`A(S) ⊆ hatMsigma M` (each point centralizes a nonidentity `M_σ`-element), the definitional
`ASet M U₀ = hatMsigma M ∩ (U₀ ⊔ M_σ)` receives `A(S)`.  This is the reduction of the honest
type-`P₂` support to BG's type-agnostic Theorem-E set, feeding `theoremII_tame_embedding` and
`mem_sigmaSharp_of_mem_aSet_of_escape`. -/
theorem typePACore_subset_ASet [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K₀ U₀ : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K₀ ≤ M) (hUM : U₀ ≤ M)
    (hKne : K₀ ≠ ⊥)
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M) (K₀.subgroupOf M))
    (hU : OddOrder.Isaacs.Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U₀.subgroupOf M)) :
    typePACore M ⊆ OddOrder.BG.Ch4.S16.ASet M U₀ := by
  have hderiv : derivedInG M = U₀ ⊔ OddOrder.BG.Ch3.S10.Msigma M :=
    (OddOrder.BG.Ch4.S15.typeP_hall_derived_eq_and_abelian hG hM hKM hUM hKne hK hU).1
  intro y hy
  refine ⟨typePACore_subset_hatMsigma hy, ?_⟩
  have hyM' : y ∈ derivedInG M := hy.1
  rw [hderiv] at hyM'
  exact hyM'

/-- **(8.13.b) for the type-`P₂` support: escaping `A(S)`-points are `σ`-sharp.**  An escaping point
of `A(S)` lies in `ASet S U₀` (`typePACore_subset_ASet`), so BG Theorem-II's `D ⊆ M_σ^#`
reduction (`mem_sigmaSharp_of_mem_aSet_of_escape`, type-agnostic) puts it in `M_σ^#`. -/
theorem escaping_typePACore_mem_sigmaSharp [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K₀ U₀ : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K₀ ≤ M) (hUM : U₀ ≤ M)
    (hKne : K₀ ≠ ⊥)
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M) (K₀.subgroupOf M))
    (hU : OddOrder.Isaacs.Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U₀.subgroupOf M))
    {a : G} (ha : a ∈ OddOrder.GroupTheory.escapingCentralizerSet M (typePACore M)) :
    a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M := by
  obtain ⟨haA, haesc⟩ := ha
  exact OddOrder.BG.Ch4.S16.mem_sigmaSharp_of_mem_aSet_of_escape hG hM hKM hUM hK hU (Or.inl rfl)
    (typePACore_subset_ASet hG hM hKM hUM hKne hK hU haA) haA.2.1 haesc

/-- **(8.13.c2) coprimality for the type-`P₂` support** (the `σ`-decomposition core, `P₂` form).
For
an escaping `a ∈ M_σ^#` and any `w ∈ A(S)`, no prime `p ∈ σ(N[a])` divides `|C_S(w)|`.  Mirrors the
type-I `escaping_sigma_disjoint_centralizer`: a common prime `p ∈ σ(N[a]) ∩ π(S)` fires
`non_disjoint_signalizer_frobenius`, making `S` Frobenius with kernel `S_σ`; the `A(S)`-point `w`
centralizes a nonidentity `S_σ`-element, so Frobenius-kernel absorption
(`IsFrobeniusGroup.centralizer_kernel_le`) gives `w ∈ S_σ`, whence the `σ`-generic
`escaping_sigmaSharp_disjoint_centralizer` closes the contradiction. -/
theorem coprime_FT_signalizer_centralizerIn_typePACore [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {a : G} (haσ : a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M)
    (haesc : ¬ Subgroup.centralizer ({a} : Set G) ≤ M)
    {w : G} (hw : w ∈ typePACore M) :
    Nat.Coprime (Nat.card (OddOrder.BG.Ch4.S16.FT_signalizer a))
      (Nat.card (OddOrder.Peterfalvi.S04.centralizerIn M w)) := by
  classical
  by_contra hnc
  obtain ⟨p, hpp, hpR, hpC⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
  -- `p ∈ σ(N[a])` since `p ∣ |R(a)| ∣ |M_σ(N[a])|`.
  have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma (OddOrder.BG.Ch4.S16.FT_signalizerBase a) := by
    refine OddOrder.BG.Ch3.S10.Msigma_isPiGroup (OddOrder.BG.Ch4.S16.FT_signalizerBase a) p
      (Nat.mem_primeFactors.mpr ⟨hpp, ?_, Nat.card_pos.ne'⟩)
    refine hpR.trans (Subgroup.card_dvd_of_le ?_)
    rw [OddOrder.BG.Ch4.S16.FT_signalizer]
    exact inf_le_left
  -- escape ⟹ `1 < |𝓜_σ(a)|`.
  have ha1 : a ≠ 1 := haσ.2
  have hgt : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement a).ncard := by
    by_contra h
    exact haesc (OddOrder.BG.Ch4.S16.centralizer_le_of_maximalSigma_le_one hG hM haσ.1 ha1
      (not_lt.mp h))
  -- `p ∈ π(S)` (it divides `|C_S(w)| ∣ |S|`), so Lemma 14.13(a) fires.
  have hpS : p ∈ OddOrder.BG.Ch4.S14.piSet M := by
    refine Nat.mem_primeFactors.mpr ⟨hpp, hpC.trans ?_, Nat.card_pos.ne'⟩
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨-, -, Ufr, -, hfrobU⟩ :=
    OddOrder.BG.Ch4.S16.non_disjoint_signalizer_frobenius hG hM haσ hgt ⟨p, hpσ, hpS⟩
  -- Frobenius kernel absorption: a `w`-point centralizing a nonidentity `M_σ`-element lands in
  -- `M_σ`.
  have hker : ∀ {u v : G}, u ∈ M → v ∈ OddOrder.BG.Ch3.S10.Msigma M → v ≠ 1 →
      Commute u v → u ∈ OddOrder.BG.Ch3.S10.Msigma M := by
    intro u v huM hvMσ hv1 hcomm
    have hvM : v ∈ M := OddOrder.BG.Ch3.S10.Msigma_le M hvMσ
    have hcent := OddOrder.Isaacs.Ch06.IsFrobeniusGroup.centralizer_kernel_le hfrobU
      (⟨v, hvM⟩ : ↥M) (Subgroup.mem_subgroupOf.mpr hvMσ)
      (fun h1 => hv1 (congrArg Subtype.val h1))
    have humem : (⟨u, huM⟩ : ↥M) ∈ Subgroup.centralizer ({(⟨v, hvM⟩ : ↥M)} : Set ↥M) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hcomm.eq
    exact Subgroup.mem_subgroupOf.mp (hcent humem)
  -- `w ∈ M_σ`: `w ∈ A(S)` centralizes a nonidentity `M_σ`-element `x`.
  obtain ⟨hwM', hw1, x, hxσ, hwC⟩ := hw
  obtain ⟨hxMσ, hx1⟩ := (Set.mem_sdiff _).mp hxσ
  have hx1' : x ≠ 1 := fun he => hx1 (Set.mem_singleton_iff.mpr he)
  have hwM : w ∈ M := Subgroup.map_subtype_le _ hwM'
  have hwMσ : w ∈ OddOrder.BG.Ch3.S10.Msigma M := by
    refine hker hwM (SetLike.mem_coe.mp hxMσ) hx1' ?_
    have := Subgroup.mem_centralizer_singleton_iff.mp hwC
    exact (Commute.symm (this : Commute w x)).symm
  exact OddOrder.Peterfalvi.S10.escaping_sigmaSharp_disjoint_centralizer hG hM haσ haesc hwMσ hw1
    hpp hpσ hpC

/-- **(8.13.a) for the type-`P₂` support: `G`-conjugate `A(S)`-points are `M`-conjugate.**  BG §16
Theorem II conjunct 1 (`theoremII_tame_embedding`, first conjunct), whose `X = ASet M U₀` branch
receives `A(S)` via `typePACore_subset_ASet`.  The matched κ-Hall / `(κ∪σ)'`-Hall inputs are
`K₀`/`U₀`. -/
theorem typePACore_isConj_conj_in_M [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K₀ U₀ : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K₀ ≤ M) (hUM : U₀ ≤ M)
    (hKne : K₀ ≠ ⊥)
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M) (K₀.subgroupOf M))
    (hU : OddOrder.Isaacs.Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U₀.subgroupOf M))
    {a b : G} (ha : a ∈ typePACore M) (hb : b ∈ typePACore M) (hab : IsConj a b) :
    ∃ m : G, m ∈ M ∧ m * a * m⁻¹ = b := by
  have hII := OddOrder.BG.Ch4.S16.theoremII_tame_embedding hG hM hKM hUM hK hU
    (X := OddOrder.BG.Ch4.S16.ASet M U₀) (Or.inl rfl)
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  obtain ⟨m, hmM, hmb⟩ := hII.1 a (typePACore_subset_ASet hG hM hKM hUM hKne hK hU ha)
    b (typePACore_subset_ASet hG hM hKM hUM hKne hK hU hb) ⟨g, hg.symm⟩
  exact ⟨m, hmM, hmb.symm⟩

/-- The `κ(M)`-Hall witness on a type-`P` maximal subgroup is nontrivial (issue 2035 #82,
weakened from `IsTypeP2` for the 0116 (i) hT2-weakening): `κ(M) ≠ ∅` by type `P`, a `κ`-prime
`p` has positive `p`-rank in `M` (so `p ∣ |M|`) and avoids the index of a `κ(M)`-Hall
subgroup, so it divides `|K₀|` — impossible for `K₀ = ⊥`. -/
theorem kappaHall_ne_bot_of_isTypeP [Finite G] {M K₀ : Subgroup G}
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP M)
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M)
      (K₀.subgroupOf M)) :
    K₀ ≠ ⊥ := by
  intro hK0bot
  obtain ⟨p, hp⟩ := hTP
  -- `p ∈ κ(M) ⊆ π(M) = primeFactors |M|` (a κ-prime has `pRank_M p = 1 > 0`).
  have : Fact p.Prime := ⟨OddOrder.BG.Ch4.S14.prime_of_mem_kappa hp⟩
  have hprk : 0 < pRank ↥M p := by
    rcases OddOrder.BG.Ch4.S14.kappa_subset_tau1_union_tau3 hp with hτ1 | hτ3
    · rw [((OddOrder.BG.Ch3.S12.mem_tau1_iff M p).mp hτ1).2.2]; norm_num
    · rw [((OddOrder.BG.Ch3.S12.mem_tau3_iff M p).mp hτ3).2.2]; norm_num
  have hppi : p ∈ (Nat.card ↥M).primeFactors :=
    OddOrder.BG.Ch2.S09.mem_primeFactors_card_of_pos_pRank hprk
  obtain ⟨hpp, hpdvdM, hMne⟩ := Nat.mem_primeFactors.mp hppi
  -- `κ(M)`-Hall `K₀.subgroupOf M`: as `p ∈ κ(M)`, `p` avoids the index, so `p ∣ |K₀.subgroupOf M|`.
  have hcardMeq : Nat.card ↥(K₀.subgroupOf M) * (K₀.subgroupOf M).index = Nat.card ↥M :=
    Subgroup.card_mul_index _
  have hpKcard : p ∣ Nat.card ↥(K₀.subgroupOf M) := by
    rcases (hpp.dvd_mul.mp (hcardMeq ▸ hpdvdM)) with h | h
    · exact h
    · exact absurd hp (hK.2 p (Nat.mem_primeFactors.mpr
        ⟨hpp, h, Subgroup.index_ne_zero_of_finite⟩))
  -- but `K₀ = ⊥` makes `K₀.subgroupOf M = ⊥` of order `1`, which `p` cannot divide.
  rw [hK0bot, Subgroup.bot_subgroupOf, Subgroup.card_bot] at hpKcard
  exact hpp.one_lt.ne' (Nat.dvd_one.mp hpKcard)

/-- **Matched `κ`-Hall / `(κ∪σ)'`-Hall pair for a type-`P` maximal subgroup** (issue 2035 #82,
the 0116 Finding-2 hT2-weakening root; Coq `PFsection13` runs its §13 context at
`FTtype ∈ {2,3,4}` without assuming type II).  Type `P₂` defers to
`typeP2_exists_matched_kappa_hall_pair`; type `P₁` (`κ(M) = σ(M)'∩π(M)`, the type-III/IV case)
takes `K₀ := E` (the `σ`-complement, which is exactly a `κ`-Hall since `κ` covers the
complement primes) and `U₀ := ⊥` (vacuously `(κ∪σ)'`-Hall as `κ ∪ σ ⊇ π(M)`). -/
theorem typeP_exists_kappa_hall_pair [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hTP : OddOrder.BG.Ch4.S14.IsTypeP M) :
    ∃ K₀ U₀ : Subgroup G, K₀ ≤ M ∧ U₀ ≤ M ∧ K₀ ≠ ⊥ ∧
      OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M)
        (K₀.subgroupOf M) ∧
      OddOrder.Isaacs.Ch03.IsHallSubgroup
        ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
        (U₀.subgroupOf M) := by
  classical
  by_cases hP2 : OddOrder.BG.Ch4.S14.IsTypeP2 M
  · obtain ⟨K₀, U₀, hKM, hUM, -, hK, hU, -, -⟩ :=
      OddOrder.BG.Ch4.S16.typeP2_exists_matched_kappa_hall_pair hG hM hP2
    exact ⟨K₀, U₀, hKM, hUM, kappaHall_ne_bot_of_isTypeP hTP hK, hK, hU⟩
  · -- type `P₁`: `κ(M) = piSet(M) \ σ(M)`
    have hκeq : OddOrder.BG.Ch4.S14.kappa M
        = OddOrder.BG.Ch4.S14.sigmaComplementPrimes M := by
      by_contra hne
      exact hP2 ⟨hTP, hne⟩
    obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := OddOrder.BG.Ch3.S12.exists_subgroupESetup hG hM
    -- the product formula `|M_σ| · |E| = |M|` (`M_σ ⊴ M` normalizes, trivial intersection)
    have hnorm : E ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M) :=
      hsetup.E_le.trans (OddOrder.GroupTheory.le_normalizer_opiCoreInG _ M)
    have hdisj : Disjoint (OddOrder.BG.Ch3.S10.Msigma M) E :=
      disjoint_iff.mpr hsetup.E_compl_inf
    have hcard : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) * Nat.card ↥E = Nat.card ↥M := by
      rw [← OddOrder.BG.Ch1.S03f.card_sup_of_le_normalizer_of_disjoint hnorm hdisj,
        hsetup.E_compl_sup]
    -- `M_σ.subgroupOf M` is the `σ`-Hall; transport its card/index along the product formula
    have hMσHall := OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM
    have hMσle : OddOrder.BG.Ch3.S10.Msigma M ≤ M :=
      OddOrder.BG.Ch3.S10.Msigma_le M
    have hcardMσ : Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
        = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσle).toEquiv
    have hcardE : Nat.card ↥(E.subgroupOf M) = Nat.card ↥E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E_le).toEquiv
    have hMne : Nat.card ↥M ≠ 0 := Nat.card_pos.ne'
    -- `index (M_σ.subgroupOf M) = |E|` and `index (E.subgroupOf M) = |M_σ|`
    have hidxMσ : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index = Nat.card ↥E := by
      have h := Subgroup.card_mul_index ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
      rw [hcardMσ] at h
      have h2 : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)
          * ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index
          = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) * Nat.card ↥E := by
        rw [h, hcard]
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h2
    have hidxE : (E.subgroupOf M).index = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
      have h := Subgroup.card_mul_index (E.subgroupOf M)
      rw [hcardE] at h
      have h2 : Nat.card ↥E * (E.subgroupOf M).index
          = Nat.card ↥E * Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
        rw [h, ← hcard]; ring
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h2
    -- `E ≠ ⊥`: otherwise `π(M) ⊆ σ(M)` and `κ(M) = ∅`, contradicting type `P`
    have hEne : E ≠ ⊥ := by
      intro hEbot
      obtain ⟨p, hp⟩ := hTP
      rw [hκeq] at hp
      obtain ⟨hppi, hpσ⟩ := hp
      have hpM : p ∣ Nat.card ↥M := by
        have := hppi
        unfold OddOrder.BG.Ch4.S14.piSet at this
        exact (Nat.mem_primeFactors.mp this).2.1
      have hcard' : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) = Nat.card ↥M := by
        rw [← hcard, hEbot, Subgroup.card_bot, mul_one]
      have hpp : p.Prime := (Nat.mem_primeFactors.mp hppi).1
      have hpMσ : p ∈ (Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)).primeFactors := by
        rw [hcardMσ, hcard']
        exact Nat.mem_primeFactors.mpr ⟨hpp, hpM, hMne⟩
      exact hpσ (hMσHall.1 p hpMσ)
    refine ⟨E, ⊥, hsetup.E_le, bot_le, hEne, ?_, ?_⟩
    · -- `E` is `κ(M)`-Hall in `M` (`κ = piSet \ σ`)
      constructor
      · intro p hp
        rw [hcardE] at hp
        obtain ⟨hpp, hpE, -⟩ := Nat.mem_primeFactors.mp hp
        rw [hκeq]
        refine ⟨?_, ?_⟩
        · unfold OddOrder.BG.Ch4.S14.piSet
          have hEdvd : Nat.card ↥E ∣ Nat.card ↥M :=
            ⟨Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M), by rw [← hcard]; ring⟩
          exact Nat.mem_primeFactors.mpr ⟨hpp, hpE.trans hEdvd, hMne⟩
        · intro hpσ
          exact (hMσHall.2 p (by
            rw [hidxMσ]
            exact Nat.mem_primeFactors.mpr ⟨hpp, hpE, Nat.card_pos.ne'⟩)) hpσ
      · intro p hp
        rw [hidxE] at hp
        rw [hκeq]
        rintro ⟨-, hpσ⟩
        exact hpσ (hMσHall.1 p (by rwa [hcardMσ]))
    · -- `⊥` is `(κ∪σ)'`-Hall in `M`: `κ ∪ σ ⊇ π(M)`
      constructor
      · intro p hp
        rw [Subgroup.bot_subgroupOf, Subgroup.card_bot] at hp
        simp at hp
      · intro p hp
        rw [Subgroup.bot_subgroupOf, Subgroup.index_bot] at hp
        have hcardM : Nat.card ↥((⊤ : Subgroup ↥M)) = Nat.card ↥M := by
          simp
        simp only [Set.mem_compl_iff, not_not]
        by_cases hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M
        · exact Set.mem_union_right _ hpσ
        · refine Set.mem_union_left _ ?_
          rw [hκeq]
          refine ⟨?_, hpσ⟩
          unfold OddOrder.BG.Ch4.S14.piSet
          obtain ⟨hpp, hpM, -⟩ := Nat.mem_primeFactors.mp hp
          exact Nat.mem_primeFactors.mpr ⟨hpp, by simpa using hpM, hMne⟩

/-- **Peterfalvi (8.15) for the type-`P₂` support `A(S)`: the Dade (2.2) support hypotheses hold.**
The honest (13.2.e) foundation.  Assembles the `σ`-decomposition-generic engine
(`dadeSupportHypothesisData_of_subset_escaping_sigmaSharp`) with the type-`P₂` pins obtained from
the
matched κ-Hall / `(κ∪σ)'`-Hall pair (`typeP2_exists_matched_kappa_hall_pair`): escaping points are
`σ`-sharp (`escaping_typePACore_mem_sigmaSharp`, (8.13.b)), `G`-conjugacy is `M`-conjugacy
(`typePACore_isConj_conj_in_M`, (8.13.a)), and the coprimality
(`coprime_FT_signalizer_centralizerIn_typePACore`, (8.13.c2)), plus the set-facts (`A(S) ⊆ M`,
non-identity, nonempty, `M`-conjugation-invariant).

This is the honest type-`P₂` Dade support (issue 9008 Option A / issue 1017 update #9): its `.dade`
field is the `S04.Hypothesis G (A(S)) M` (the `τ = Ind_M^G` Dade isometry lives on `A(S)`),
replacing
the likely-unsound `sibleyTarget_H0C` route for the (13.3) `S`-instance coherence. -/
theorem dadeSupportHypothesisData_typePACore [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP M) :
    Nonempty (DadeSupportHypothesisData M (typePACore M)) := by
  classical
  obtain ⟨K₀, U₀, hKM, hUM, hKne, hK, hU⟩ :=
    typeP_exists_kappa_hall_pair hG hM hTP
  refine dadeSupportHypothesisData_of_subset_escaping_sigmaSharp hG hM
    typePACore_subset (fun x hx => hx.2.1)
    (fun a ha => escaping_typePACore_mem_sigmaSharp hG hM hKM hUM hKne hK hU ha)
    (fun a ha b hb hab => typePACore_isConj_conj_in_M hG hM hKM hUM hKne hK hU ha hb hab)
    (fun a ha b hb => coprime_FT_signalizer_centralizerIn_typePACore hG hM
      (escaping_typePACore_mem_sigmaSharp hG hM hKM hUM hKne hK hU ha) ha.2 hb)
    ?_ ?_
  · -- `A(S)` nonempty: `M_σ^# ⊆ A(S)` (a nonidentity `M_σ`-element centralizes itself).
    obtain ⟨a, ha1⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp (OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM)
    have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have haMσ : (a : G) ∈ OddOrder.BG.Ch3.S10.Msigma M := a.2
    have haM' : (a : G) ∈ derivedInG M := OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM haMσ
    refine ⟨a.1, haM', ha1', a.1, ?_, ?_⟩
    · exact (Set.mem_sdiff _).mpr ⟨SetLike.mem_coe.mpr haMσ, fun h => ha1' (Set.mem_singleton_iff.mp
        h)⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  · -- `M`-conjugation invariance.
    intro m x hm
    exact ⟨fun h => by
      have := typePACore_conj_mem (inv_mem hm) h
      rwa [show m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x from by group] at this,
      fun h => typePACore_conj_mem hm h⟩

end OddOrder.Peterfalvi.S10


