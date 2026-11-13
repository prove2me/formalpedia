-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_CentralizerSup
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_CentralizerSup
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T09:23:46.148892+00:00
-- url     : https://prove2.me/theorems/23855ac5-433a-4d4c-bbc8-1b820675291a
-- title:
--   BG §14: type-$\mathcal{P}$ counting, centralizer suprema
-- statement:
--   A part of the §14 type-$\mathcal{P}$ counting development of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, split from the type-$\mathcal{P}$ duality file. It consists of lemmas only, on the type-$\mathcal{P}$ family and $\pi$-elements and complements, e.g. `typeP_family_isPiElement_mem_Kstar` and `typeP_family_exists_sigmaPart`.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 39 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/CentralizerSup.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/CentralizerSup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_SigmaCovers

namespace OddOrder.BG.Ch4.S14

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch3.S13

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BG 14.7, the family `σ(Nᵢ)` cover `π(z)`** (mmd L4007 "each `X ∈ ℰ¹(Z)` lies in some `Kᵢ*`"):
every prime `p ∣ |Z|` lies in `σ(N)` for some family member `N`.  For `p ∣ |K*|` it is the base
member `M` (`K* ≤ M_σ`, `Kstar_isPiSubgroup_sigma`); for `p ∣ |K|` (`p ∈ κ(M)`) a line
`X ∈ ℰ_p¹(K)` has a type-`P` partner `N ∈ 𝓜(N_G(X))` — a family member — with `X ⊆ M_σ(N)`, so
`p ∈ σ(N)`.  This coverage forces `⋂ᵢ Kᵢ = 1`, i.e. the `t = yy'` characterisation of `T`. -/
theorem typeP_family_sigma_covers [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} (hp : p.Prime) (hpZ : p ∣ Nat.card ↥(K ⊔ Kstar)) :
    ∃ N : Subgroup G, IsZFamilyMember M K N ∧ p ∈ OddOrder.BG.Ch3.S10.sigma N := by
  classical
  rw [card_kappaHall_sup_Kstar hKM hK hKstar] at hpZ
  rcases hp.dvd_mul.mp hpZ with hpK | hpKstar
  · -- `p ∣ k`: a line `X ∈ ℰ_p¹(K)` and its type-`P` partner is a family member.
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpK
    have hxord : orderOf (x : G) = p :=
      (orderOf_injective K.subtype K.subtype_injective x).trans hx
    have hXcard : Nat.card ↥(Subgroup.zpowers (x : G)) = p := by rw [Nat.card_zpowers, hxord]
    have hXelem : Subgroup.zpowers (x : G) ∈ elemAbelianOfRank G p 1 :=
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
    have hXK : Subgroup.zpowers (x : G) ≤ K := Subgroup.zpowers_le.mpr x.2
    obtain ⟨N, hNmem, _, _, hXNσ, _, _⟩ :=
      exists_typeP_partner hG hM hP hKM hK hKstar hU hXelem hXK
    refine ⟨N, Or.inr ⟨p, Subgroup.zpowers (x : G), hp, hXelem, hXK, hNmem⟩, ?_⟩
    exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup N p (Nat.mem_primeFactors.mpr
      ⟨hp, (by rw [hXcard] : p ∣ Nat.card ↥(Subgroup.zpowers (x : G))).trans
        (Subgroup.card_dvd_of_le hXNσ), Nat.card_pos.ne'⟩)
  · -- `p ∣ k*`: the base member `M` itself, since `K* ≤ M_σ`.
    exact ⟨M, Or.inl rfl, Kstar_isPiSubgroup_sigma hKstar p
      (Nat.mem_primeFactors.mpr ⟨hp, hpKstar, Nat.card_pos.ne'⟩)⟩

/-- **BG 14.7, `σ(N)`-elements of `Z` lie in `Kᵢ*`** (mmd L4019, the `σ`-part lands in `Kᵢ*`): for a
family member `N`, every `σ(N)`-element `a ∈ Z` lies in `Kᵢ* = Z ⊓ M_σ(N)`.  Since `a ∈ Z ≤ N`, the
cyclic `⟨a⟩` is a `σ(N)`-subgroup of `N`, hence `⟨a⟩ ≤ M_σ(N)`
(`sigma_subgroup_le_Msigma_of_isHall`); combined with `a ∈ Z` this gives `a ∈ Z ⊓ M_σ(N)`.  This
places the `σ(N)`-part of any `t ∈ Z` into `Kᵢ*` — half of the `t = yy'` characterisation of `T`. -/
theorem typeP_family_isPiElement_mem_Kstar [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N : Subgroup G} (hN : IsZFamilyMember M K N) {a : G} (haZ : a ∈ K ⊔ Kstar)
    (hapi : IsPiElement (OddOrder.BG.Ch3.S10.sigma N) a) :
    a ∈ (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N := by
  obtain ⟨hNmax, _, hZN, _⟩ := typeP_family_member_data hG hM hP hKM hK hKstar hU hN
  refine Subgroup.mem_inf.mpr ⟨haZ, ?_⟩
  have hpi : Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma N) (Subgroup.zpowers a) := by
    intro p hp
    rw [Nat.card_zpowers] at hp
    exact hapi p hp
  exact OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
    (OddOrder.BG.Ch3.S10.Msigma_isHall hG hNmax)
    (Subgroup.zpowers_le.mpr (hZN haZ)) hpi (Subgroup.mem_zpowers a)

/-- **An internal direct factor absorbs coprime elements** (BG 14.7, the `σ(N)′`-part lands in
`K_N`): if `Z = A ⊔ B` with `B ≤ C_G(A)` (so `A`, `B` commute), `A` a `πᶜ`-group and `B` a
`π`-group, then every `πᶜ`-element of `Z` lies in `A`.  Proof: `A ◁ Z` (commuting factor) is a Hall
`πᶜ`-subgroup of `Z` (`|Z| = |A|·|B|`, index `= |B|` a `π`-number), so the `πᶜ`-group `⟨b⟩ ≤ Z` lies
in `A` (`isPiGroup_le_of_normal_isHallSubgroup` in `↥Z`).  Applied with `A = K_N` (the `σ(N)′`-Hall
of `Z`), `B = Kᵢ*`, `π = σ(N)`: the `σ(N)′`-part of any `t ∈ Z` lands in `K_N`. -/
theorem isPiElementCompl_mem_left_of_commute [Finite G] {A B Z : Subgroup G} {π : Set ℕ}
    (hswap : Z = A ⊔ B) (hcent : B ≤ Subgroup.centralizer (A : Set G))
    (hAπc : Subgroup.IsPiSubgroup πᶜ A) (hBπ : Subgroup.IsPiSubgroup π B)
    {b : G} (hbZ : b ∈ Z) (hbπc : IsPiElement πᶜ b) : b ∈ A := by
  classical
  have hAZ : A ≤ Z := by rw [hswap]; exact le_sup_left
  have hcomm : ∀ a ∈ A, ∀ c ∈ B, Commute a c := fun a ha c hc =>
    Subgroup.mem_centralizer_iff.mp (hcent hc) a ha
  have hcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥B) := by
    apply Nat.coprime_of_dvd
    intro p hp hpA hpB
    exact (hAπc p (Nat.mem_primeFactors.mpr ⟨hp, hpA, Nat.card_pos.ne'⟩))
      (hBπ p (Nat.mem_primeFactors.mpr ⟨hp, hpB, Nat.card_pos.ne'⟩))
  have hdisj : A ⊓ B = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hnorm : Z ≤ Subgroup.normalizer (A : Set G) := by
    rw [hswap]; exact (sup_le_normalizer_inf_of_commute hcent).trans inf_le_left
  have hAnZ : (A.subgroupOf Z).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAZ).mpr hnorm
  have hZcard : Nat.card ↥Z = Nat.card ↥A * Nat.card ↥B := by
    rw [hswap]; exact card_sup_of_commute_of_disjoint hcomm hdisj
  have hcardSub : Nat.card ↥(A.subgroupOf Z) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAZ).toEquiv
  have hidx : (A.subgroupOf Z).index = Nat.card ↥B := by
    have hl := Subgroup.card_mul_index (A.subgroupOf Z)
    rw [hcardSub, hZcard] at hl
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hl
  have hHall : Ch03.IsHallSubgroup πᶜ (A.subgroupOf Z) := by
    refine ⟨fun p hp => ?_, fun p hp hpc => ?_⟩
    · rw [hcardSub] at hp; exact hAπc p hp
    · exact hpc (hBπ p (by rwa [hidx] at hp))
  have hbZsub : (Subgroup.zpowers b).subgroupOf Z ≤ A.subgroupOf Z := by
    refine OddOrder.BG.Ch3.S10.isPiGroup_le_of_normal_isHallSubgroup hHall (fun p hp => ?_)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.zpowers_le.mpr hbZ)).toEquiv, Nat.card_zpowers] at hp
    exact hbπc p hp
  have hbmem : (⟨b, hbZ⟩ : ↥Z) ∈ (Subgroup.zpowers b).subgroupOf Z :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers b)
  exact Subgroup.mem_subgroupOf.mp (hbZsub hbmem)

/-- **BG 14.7, the family member's `(d)`-data bundle** (mmd L3827, both clauses of Prop 14.2(d)):
for a family member `N`, the chosen Hall `κ(N)`-subgroup `K_N` together with the swap
`Z = K_N ⊔ Kᵢ*` and both conjugacy clauses — (d)-first `Kᵢ* ⊓ Nᵍ = 1` (`g ∉ N`) and (d)-second
`K_N ⊓ K_Nᵍ = 1` (`g ∈ N`, `g ∉ Z`).  Builds `N`'s Hall `(κ∪σ)′`-subgroup once
(`hall_E_exists`, `N` solvable) and feeds it to `typeP_structure` (d-first) and
`typeP_kappaHall_inf_conj_eq_bot` (d-second).  The TI-of-`T` proof obtains this once per chosen
member and conjugates the `σ`/`σ′`-parts of `t` through the two clauses to force `g ∈ Z`. -/
theorem typeP_family_member_dData [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N : Subgroup G} (hN : IsZFamilyMember M K N) :
    ∃ KN : Subgroup G, KN ≤ N ∧ Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N) ∧
      K ⊔ Kstar = KN ⊔ ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) ∧
      ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) ≤ Subgroup.centralizer (KN : Set G) ∧
      Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma N)ᶜ KN ∧
      (∀ g : G, g ∉ N →
        ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) ⊓ (MulAut.conj g • N) = ⊥) ∧
      (∀ g : G, g ∈ N → g ∉ K ⊔ Kstar → KN ⊓ (MulAut.conj g • KN) = ⊥) := by
  classical
  obtain ⟨hNmax, hPN, _, KN, hKNN, hKN, hswap, hcanon, _⟩ :=
    typeP_family_member_data hG hM hP hKM hK hKstar hU hN
  have : Group.IsSolvable ↥N := hG.isSolvable_of_mem_maximalSubgroups hNmax
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥N)
    ((kappa N ∪ OddOrder.BG.Ch3.S10.sigma N)ᶜ)
  have hUeq : (U'.map N.subtype).subgroupOf N = U' :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective U'
  have hUN : Ch03.IsHallSubgroup ((kappa N ∪ OddOrder.BG.Ch3.S10.sigma N)ᶜ)
      ((U'.map N.subtype).subgroupOf N) := by rw [hUeq]; exact hU'
  refine ⟨KN, hKNN, hKN, hswap.trans (by rw [hcanon]), hcanon ▸ inf_le_right,
    kappaHall_isPiSubgroup_sigmaCompl hKNN hKN, ?_, ?_⟩
  · intro g hgN
    have hd := (typeP_structure hG hNmax hPN hKNN hKN rfl hUN).2.2.2.1
    rw [hcanon] at hd
    exact hd g hgN
  · intro g hgN hgZ
    exact typeP_kappaHall_inf_conj_eq_bot hG hNmax hPN hKNN hKN rfl hUN hgN (hswap ▸ hgZ)

/-- **BG 14.7, every nontrivial `t ∈ Z` has a nontrivial `σ`-part** (mmd L4015, `z = ∏ xᵢ` is the
`σ`-decomposition): for `t ∈ Z`, `t ≠ 1`, some family member `N` has `t` *not* a `σ(N)′`-element
(equivalently its `σ(N)`-part is nontrivial).  Else every prime of `ord(t)` avoids every `σ(N)`,
contradicting the coverage `⋃ σ(Nᵢ) ⊇ π(z)` (`typeP_family_sigma_covers`) since `ord(t) ∣ |Z|`.
This is the half of the `t = yy'` characterisation that finds the splitting member. -/
theorem typeP_family_exists_sigmaPart [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {t : G} (htZ : t ∈ K ⊔ Kstar) (ht1 : t ≠ 1) :
    ∃ N : Subgroup G, IsZFamilyMember M K N ∧
      ¬ IsPiElement (OddOrder.BG.Ch3.S10.sigma N)ᶜ t := by
  by_contra hcon
  push Not at hcon
  -- `ord(t) ≠ 1` has a prime factor `p`, and `p ∣ |Z|`.
  have hordne : orderOf t ≠ 1 := by rw [Ne, orderOf_eq_one_iff]; exact ht1
  obtain ⟨p, hp, hpord⟩ := Nat.exists_prime_and_dvd hordne
  have hpz : p ∣ Nat.card ↥(K ⊔ Kstar) := by
    refine hpord.trans ?_
    have := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr htZ)
    rwa [Nat.card_zpowers] at this
  obtain ⟨N, hN, hpσN⟩ := typeP_family_sigma_covers hG hM hP hKM hK hKstar hU hp hpz
  exact hcon N hN p (Nat.mem_primeFactors.mpr ⟨hp, hpord, (orderOf_pos t).ne'⟩) hpσN

/-- **BG 14.7, `T` is a TI-subset of `G` with normalizer `Z`** (mmd L4027-4029): `T = Z − ⋃ Kᵢ*`
satisfies `IsTISubset T Z`.  Given `t ∈ T` and `g` with `tᵍ ∈ T ⊆ Z`: pick a member `N` whose
`σ(N)`-part of `t` is nontrivial (`typeP_family_exists_sigmaPart`), `π`-decompose `t = y·y'`
(`exists_isPiElement_mul`, `π = σ(N)`) with `y ∈ Kᵢ*` (`…isPiElement_mem_Kstar`) and `y' ∈ K_N`
(`isPiElementCompl_mem_left_of_commute`), both nontrivial (`y` by choice of `N`, `y'` since
`t ∉ Kᵢ*`).  Conjugates `yᵍ, y'ᵍ` are powers of `tᵍ ∈ Z`, so `yᵍ ∈ Kᵢ*`, `y'ᵍ ∈ K_N`; then
`yᵍ ∈ Kᵢ* ∩ Nᵍ` forces `g ∈ N` (Prop 14.2(d)-first) and `y'ᵍ ∈ K_N ∩ K_Nᵍ` forces `g ∈ Z`
(d-second).  The structural core converting `|T|` to `|𝒞_G(T)| = |T|·[G:Z]`. -/
theorem typeP_family_T_isTI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    OddOrder.GroupTheory.IsTISubset
      (((K ⊔ Kstar : Subgroup G) : Set G) \
        ⋃ N ∈ ZFamilyFinset M K,
          (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G))
      (K ⊔ Kstar) := by
  classical
  rintro g ⟨t, ⟨htZ, htnot⟩, ⟨htgZ, -⟩⟩
  -- `t ∈ Z`, `t ∉ ⋃ Kⱼ*`, `g t g⁻¹ ∈ Z`.
  have htZ' : t ∈ K ⊔ Kstar := htZ
  have htgZ' : g * t * g⁻¹ ∈ K ⊔ Kstar := htgZ
  have ht1 : t ≠ 1 := fun h => htnot
    (Set.mem_biUnion (mem_ZFamilyFinset.mpr (Or.inl rfl)) (h ▸ one_mem _))
  -- Conjugation by `g` keeps powers of `t` inside `Z` and preserves `π`-element-ness.
  have hconjZ : ∀ a : G, a ∈ Subgroup.zpowers t → g * a * g⁻¹ ∈ K ⊔ Kstar := by
    intro a ha
    refine (Subgroup.zpowers_le.mpr htgZ') ?_
    have h1 := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom ha
    rw [MonoidHom.map_zpowers] at h1
    simpa [MulAut.conj_apply] using h1
  have hordeq : ∀ a : G, orderOf (g * a * g⁻¹) = orderOf a := fun a => by
    rw [show g * a * g⁻¹ = (MulAut.conj g).toMonoidHom a by simp [MulAut.conj_apply]]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a
  have hpiconj : ∀ {π : Set ℕ} {a : G}, IsPiElement π a → IsPiElement π (g * a * g⁻¹) :=
    fun {π a} ha p hp => ha p (by rwa [hordeq a] at hp)
  -- Pick a member `N` with nontrivial `σ(N)`-part, and `π`-decompose `t`.
  obtain ⟨N, hN, hσpart⟩ := typeP_family_exists_sigmaPart hG hM hP hKM hK hKstar hU htZ' ht1
  obtain ⟨y, y', hyy', hcomm, hyπ, hy'π, hyz, hy'z⟩ :=
    exists_isPiElement_mul (OddOrder.BG.Ch3.S10.sigma N) t
  have hyZ : y ∈ K ⊔ Kstar := (Subgroup.zpowers_le.mpr htZ') hyz
  have hy'Z : y' ∈ K ⊔ Kstar := (Subgroup.zpowers_le.mpr htZ') hy'z
  obtain ⟨KN, hKNN, _, hswap, hcent, hAπc, hdfirst, hdsecond⟩ :=
    typeP_family_member_dData hG hM hP hKM hK hKstar hU hN
  have hBπ : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma N)
      ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) := by
    intro p hp
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup N p (Nat.mem_primeFactors.mpr
      ⟨hpp, hpd.trans (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩)
  -- `y ∈ Kᵢ*`, `y' ∈ K_N`; both nontrivial.
  have hyKstar : y ∈ (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N :=
    typeP_family_isPiElement_mem_Kstar hG hM hP hKM hK hKstar hU hN hyZ hyπ
  have hy'KN : y' ∈ KN := isPiElementCompl_mem_left_of_commute hswap hcent hAπc hBπ hy'Z hy'π
  have hy1 : y ≠ 1 := by
    rintro rfl; exact hσpart (by rw [show t = y' from by rw [← hyy', one_mul]]; exact hy'π)
  have hy'1 : y' ≠ 1 := by
    rintro rfl
    exact htnot (Set.mem_biUnion (mem_ZFamilyFinset.mpr hN)
      (show t ∈ ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) from
        by rw [show t = y from by rw [← hyy', mul_one]]; exact hyKstar))
  -- `yᵍ ∈ Kᵢ*` (a `σ(N)`-element of `Z`), `yᵍ ≠ 1`; force `g ∈ N` via (d)-first.
  have hygZ : g * y * g⁻¹ ∈ K ⊔ Kstar := hconjZ y hyz
  have hygKstar : g * y * g⁻¹ ∈ (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N :=
    typeP_family_isPiElement_mem_Kstar hG hM hP hKM hK hKstar hU hN hygZ (hpiconj hyπ)
  have hyg1 : g * y * g⁻¹ ≠ 1 := fun h =>
    hy1 ((map_eq_one_iff _ (MulAut.conj g).injective).mp (by rw [MulAut.conj_apply]; exact h))
  have hgN : g ∈ N := by
    by_contra hgnot
    have hbot := hdfirst g hgnot
    have hmem : g * y * g⁻¹ ∈ ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) ⊓ (MulAut.conj g • N) :=
        by
      refine Subgroup.mem_inf.mpr ⟨hygKstar, ?_⟩
      have hyN : y ∈ N := (inf_le_right.trans (OddOrder.BG.Ch3.S10.Msigma_le N)) hyKstar
      rw [show (MulAut.conj g • N : Subgroup G) = N.map (MulAut.conj g).toMonoidHom from rfl,
        show g * y * g⁻¹ = (MulAut.conj g).toMonoidHom y from by
          rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]]
      exact Subgroup.mem_map_of_mem _ hyN
    rw [hbot] at hmem
    exact hyg1 (Subgroup.mem_bot.mp hmem)
  -- `y'ᵍ ∈ K_N ∩ K_Nᵍ`, `y'ᵍ ≠ 1`; force `g ∈ Z` via (d)-second.
  have hy'gZ : g * y' * g⁻¹ ∈ K ⊔ Kstar := hconjZ y' hy'z
  have hy'gKN : g * y' * g⁻¹ ∈ KN :=
    isPiElementCompl_mem_left_of_commute hswap hcent hAπc hBπ hy'gZ (hpiconj hy'π)
  have hy'g1 : g * y' * g⁻¹ ≠ 1 := fun h =>
    hy'1 ((map_eq_one_iff _ (MulAut.conj g).injective).mp (by rw [MulAut.conj_apply]; exact h))
  by_contra hgZ
  have hbot := hdsecond g hgN hgZ
  have hmem : g * y' * g⁻¹ ∈ KN ⊓ (MulAut.conj g • KN) := by
    refine Subgroup.mem_inf.mpr ⟨hy'gKN, ?_⟩
    rw [show (MulAut.conj g • KN : Subgroup G) = KN.map (MulAut.conj g).toMonoidHom from rfl,
      show g * y' * g⁻¹ = (MulAut.conj g).toMonoidHom y' from by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]]
    exact Subgroup.mem_map_of_mem _ hy'KN
  rw [hbot] at hmem
  exact hy'g1 (Subgroup.mem_bot.mp hmem)

/-- **BG 14.7, `|𝒞_G(T)| = |T|·[G:Z]`** (mmd L4031): the conjugacy-saturation count of the TI-set
`T = Z − ⋃ Kᵢ*`.  Direct composition of `ncard_conjClassSet_of_isTISubset` with the TI property
(`typeP_family_T_isTI`) and the `Z`-stability `hstab` (`typeP_family_Z_normalizes_T`).  With
`|T| = z + n − ∑ kᵢ*` (`typeP_family_T_count`) this is BG's `(1 + n/z − ∑ 1/kᵢ)|G|`, the left
summand of the density inequality. -/
theorem typeP_family_conjClass_T_count [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    (conjClassSet (((K ⊔ Kstar : Subgroup G) : Set G) \
        ⋃ N ∈ ZFamilyFinset M K,
          (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G))).ncard
      = (((K ⊔ Kstar : Subgroup G) : Set G) \
          ⋃ N ∈ ZFamilyFinset M K,
            (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G)).ncard
        * (K ⊔ Kstar).index :=
  ncard_conjClassSet_of_isTISubset
    (typeP_family_T_isTI hG hM hP hKM hK hKstar hU)
    (typeP_family_Z_normalizes_T hG hM hP hKM hK hKstar hU)

/-- **BG 14.7, `Z ⊊ Mᵢ` (so `|Mᵢ| ≥ 2z`)** (mmd L4033, the `|M_i| ≥ 2z` step): every family member
`N` properly contains `Z = K ⊔ K*`.  The clean argument (NOT self-centralizing — BG's "prime
manner" allows trivial action): the family has `≥ 2` members (`M` plus a neighbour, which exists
since `N_G(X) ⊄ M` for `X ∈ ℰ¹(K)`), all containing `Z`; if `Z = N` then `N ⊆ M'` for some other
member `M' ≠ N`, impossible for distinct maximal subgroups.  Hence `Z ⊊ N`, giving `|N| ≥ 2z`. -/
theorem typeP_family_Z_lt_member [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N : Subgroup G} (hN : IsZFamilyMember M K N) :
    K ⊔ Kstar < N := by
  classical
  -- Distinct maximal subgroups form an antichain.
  have hanti : ∀ {A B : Subgroup G}, A ∈ maximalSubgroups G → B ∈ maximalSubgroups G →
      A ≤ B → A = B := fun {A B} hA hB hAB => hAB.lt_or_eq.elim
    (fun hlt => absurd ((mem_maximalSubgroups.mp hA).2 _ hlt) (mem_maximalSubgroups.mp hB).1) id
  -- A prime `p ∣ |K|` (κ(M) ≠ ∅, κ-primes divide |M|, Hall index avoids κ).
  have hP2 := hP
  obtain ⟨p, hpκ⟩ := hP2
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
  -- A neighbour `N₁ ≠ M` containing `Z`.
  obtain ⟨N₁, hN₁max, -, hncM, -, hZN₁⟩ :=
    exists_typeP_neighbor_mem_sigma hG hM hP hKM hK hKstar hU hpprime hpK
  have hN₁neM : N₁ ≠ M := fun h =>
    hncM (h ▸ (⟨1, by rw [map_one, one_smul]⟩ : IsConjugateSubgroup M M))
  obtain ⟨hNmax, -, hZN, -⟩ := typeP_family_member_data hG hM hP hKM hK hKstar hU hN
  have hZM : K ⊔ Kstar ≤ M :=
    sup_le hKM (hKstar ▸ inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le M))
  refine lt_of_le_of_ne hZN (fun heq => ?_)
  by_cases hNM : N = M
  · exact hN₁neM ((hanti hNmax hN₁max (heq ▸ hZN₁)).symm.trans hNM)
  · exact hNM (hanti hNmax hM (heq ▸ hZM))

/-- **BG 14.7, `|Mᵢ| ≥ 2z`** (mmd L4033): the cardinality form of `Z ⊊ Mᵢ`, the lower bound the
density inequality needs (`|𝒞_G(M̃ᵢ)| ≥ (1/kᵢ − 1/2z)|G|`).  From `Z < N` (proper),
`[N : Z] ≥ 2`. -/
theorem typeP_family_two_mul_card_le [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N : Subgroup G} (hN : IsZFamilyMember M K N) :
    2 * Nat.card ↥(K ⊔ Kstar) ≤ Nat.card ↥N := by
  classical
  have hlt := typeP_family_Z_lt_member hG hM hP hKM hK hKstar hU hN
  have hle : K ⊔ Kstar ≤ N := hlt.le
  have hlag : Nat.card ↥(K ⊔ Kstar) * ((K ⊔ Kstar).subgroupOf N).index = Nat.card ↥N := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact Subgroup.card_mul_index ((K ⊔ Kstar).subgroupOf N)
  have hne1 : ((K ⊔ Kstar).subgroupOf N).index ≠ 1 := fun h =>
    hlt.ne (le_antisymm hle (Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp h)))
  have hidx2 : 2 ≤ ((K ⊔ Kstar).subgroupOf N).index :=
    (Nat.two_le_iff _).mpr ⟨Subgroup.index_ne_zero_of_finite, hne1⟩
  calc 2 * Nat.card ↥(K ⊔ Kstar)
      ≤ ((K ⊔ Kstar).subgroupOf N).index * Nat.card ↥(K ⊔ Kstar) :=
        Nat.mul_le_mul_right _ hidx2
    _ = Nat.card ↥(K ⊔ Kstar) * ((K ⊔ Kstar).subgroupOf N).index := Nat.mul_comm _ _
    _ = Nat.card ↥N := hlag

/-- **`σ`-sharp set is conjugation-equivariant**: `conj g • (M_σ^#) = (M^g)_σ^#`.  From
`Msigma_conj_smul` (`M_σ` equivariant) and `conj g` fixing `1`. -/
theorem sigmaSharp_conj_smul [Finite G] (g : G) (M : Subgroup G) :
    MulAut.conj g • sigmaSharp M = sigmaSharp (MulAut.conj g • M) := by
  rw [sigmaSharp, sigmaSharp, sharpSubgroup, sharpSubgroup, Set.smul_set_sdiff,
    ← Subgroup.coe_pointwise_smul, ← Msigma_conj_smul]
  congr 1
  simp [Set.smul_set_singleton]

/-- **`M̃` is conjugation-equivariant** (mmd L3908): `conj g • M̃(M) = M̃(Mᵍ)`.  Each product
`x·x'` (`x ∈ M_σ^#`, `x' ∈ R(x)`) conjugates to `(xᵍ)(x'ᵍ)` with `xᵍ ∈ (Mᵍ)_σ^#`
(`sigmaSharp_conj_smul`) and `x'ᵍ ∈ R(xᵍ)` (`Rsub_conj`).  This is what turns the set-level
disjointness 14.5(b) into disjointness of the conjugacy saturations `𝒞_G(M̃ᵢ)`. -/
theorem Mtilde_conj_smul [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) (g : G) (M : Subgroup G) :
    MulAut.conj g • Mtilde hG D M = Mtilde hG D (MulAut.conj g • M) := by
  have hle : ∀ (h : G) (N : Subgroup G),
      MulAut.conj h • Mtilde hG D N ⊆ Mtilde hG D (MulAut.conj h • N) := by
    rintro h N y ⟨z, ⟨x, hx, x', hx', rfl⟩, rfl⟩
    refine ⟨MulAut.conj h • x, ?_, MulAut.conj h • x', ?_, ?_⟩
    · rw [← sigmaSharp_conj_smul]; exact Set.smul_mem_smul_set hx
    · rw [show MulAut.conj h • x = h * x * h⁻¹ from by rw [MulAut.smul_def, MulAut.conj_apply],
        Rsub_conj]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hx'
    · exact smul_mul' _ _ _
  refine Set.Subset.antisymm (hle g M) (fun y hy => ?_)
  have h2 := hle g⁻¹ (MulAut.conj g • M)
  rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h2
  have hmem : MulAut.conj g⁻¹ • y ∈ Mtilde hG D M := h2 (Set.smul_mem_smul_set hy)
  rw [show y = MulAut.conj g • (MulAut.conj g⁻¹ • y) by
    rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]]
  exact Set.smul_mem_smul_set hmem

/-- **BG 14.7, the `𝒞_G(M̃ᵢ)` are pairwise disjoint** (mmd L4035): for nonconjugate maximal
`M₁`, `M₂`, the conjugacy saturations `𝒞_G(M̃₁)`, `𝒞_G(M̃₂)` are disjoint.  A common element `z`
is `g₁t₁g₁⁻¹ = g₂t₂g₂⁻¹` with `tᵢ ∈ M̃(Mᵢ)`, so `z ∈ M̃(M₁ᵍ¹) ∩ M̃(M₂ᵍ²)` (`Mtilde_conj_smul`);
`M₁ᵍ¹`, `M₂ᵍ²` are nonconjugate (else `M₁ ~ M₂`), so 14.5(b) (`Mtilde_disjoint`) gives a
contradiction.  Pairwise disjointness of the density-inequality summands. -/
theorem conjClassSet_Mtilde_disjoint [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M₁ M₂ : Subgroup G} (hM₁ : M₁ ∈ maximalSubgroups G)
    (hM₂ : M₂ ∈ maximalSubgroups G) (hnc : ¬ IsConjugateSubgroup M₁ M₂) :
    Disjoint (conjClassSet (Mtilde hG D M₁)) (conjClassSet (Mtilde hG D M₂)) := by
  rw [Set.disjoint_left]
  rintro z ⟨t₁, ht₁, g₁, rfl⟩ ⟨t₂, ht₂, g₂, hz₂⟩
  have hz1 : g₁ * t₁ * g₁⁻¹ ∈ Mtilde hG D (MulAut.conj g₁ • M₁) := by
    rw [show g₁ * t₁ * g₁⁻¹ = MulAut.conj g₁ • t₁ from by rw [MulAut.smul_def, MulAut.conj_apply],
      ← Mtilde_conj_smul]
    exact Set.smul_mem_smul_set ht₁
  have hz2 : g₁ * t₁ * g₁⁻¹ ∈ Mtilde hG D (MulAut.conj g₂ • M₂) := by
    rw [← hz₂, show g₂ * t₂ * g₂⁻¹ = MulAut.conj g₂ • t₂ from by
      rw [MulAut.smul_def, MulAut.conj_apply], ← Mtilde_conj_smul]
    exact Set.smul_mem_smul_set ht₂
  have hc1 : IsConjugateSubgroup M₁ (MulAut.conj g₁ • M₁) := ⟨g₁, rfl⟩
  have hc2 : IsConjugateSubgroup M₂ (MulAut.conj g₂ • M₂) := ⟨g₂, rfl⟩
  have hncc : ¬ IsConjugateSubgroup (MulAut.conj g₁ • M₁) (MulAut.conj g₂ • M₂) := fun h =>
    hnc ((hc1.trans h).trans hc2.symm)
  exact Set.disjoint_left.mp (Mtilde_disjoint hG D
    (mem_maximalSubgroups_of_isConjugateSubgroup hM₁ ⟨g₁, rfl⟩)
    (mem_maximalSubgroups_of_isConjugateSubgroup hM₂ ⟨g₂, rfl⟩) hncc) hz1 hz2

/-- **`M̃`-membership is the `not_type1_of_type2` "type-2 form"**: `g ∈ M̃(M)` (for maximal `M`)
gives `g = x·x'` with `ℓ_σ(x) = 1` and `x' ∈ R(x)`.  The `ℓ_σ(x) = 1` is from `length_one_iff`
(`x ∈ M_σ^#`, so `M ∈ 𝓜_σ(x)`).  Feeds the `𝒞_G(T) ⊥ 𝒞_G(M̃ᵢ)` disjointness via Lemma 14.6. -/
theorem mem_Mtilde_imp_form [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {g : G}
    (hg : g ∈ Mtilde hG D M) :
    ∃ x x' : G, g = x * x' ∧ D.length x = 1 ∧ x' ∈ Rsub hG D x := by
  obtain ⟨x, hx, x', hx', rfl⟩ := hg
  rw [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe] at hx
  exact ⟨x, x', rfl, (D.length_one_iff x).mpr ⟨hx.2, ⟨M, hM, hx.1⟩⟩, hx'⟩

/-- **BG 14.7, elements of `T` have the `not_type1_of_type2` "type-1 form"** (mmd L4021): for
`t ∈ T = Z − ⋃ Kᵢ*`, there is a family member `N` and `t = y·y'` with `y ∈ M_σ(N)^#`, `y'` a
nonidentity `κ(N)`-element of `N` centralising `y`.  Extracted exactly as in the TI-of-`T` proof:
the splitting member `N` (`typeP_family_exists_sigmaPart`), `π`-decompose `t = y·y'`
(`exists_isPiElement_mul`), `y ∈ Kᵢ* ≤ M_σ(N)` (`…isPiElement_mem_Kstar`) and `y' ∈ K_N` (a Hall
`κ(N)`-subgroup, `isPiElementCompl_mem_left_of_commute`), both nontrivial.  Feeds Lemma 14.6
(`not_type1_of_type2`) for the `𝒞_G(T) ⊥ 𝒞_G(M̃ᵢ)` disjointness. -/
theorem typeP_family_T_form [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {t : G} (htT : t ∈ ((K ⊔ Kstar : Subgroup G) : Set G) \
        ⋃ N ∈ ZFamilyFinset M K,
          (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G)) :
    ∃ N : Subgroup G, N ∈ maximalSubgroups G ∧ ∃ y y' : G, t = y * y' ∧ Commute y y' ∧
      y ∈ sigmaSharp N ∧ y' ≠ 1 ∧ y' ∈ N ∧ y' ∈ Subgroup.centralizer ({y} : Set G) ∧
      ∀ p ∈ piSet (Subgroup.closure ({y'} : Set G)), p ∈ kappa N := by
  classical
  obtain ⟨htZ, htnot⟩ := htT
  have ht1 : t ≠ 1 := fun h => htnot
    (Set.mem_biUnion (mem_ZFamilyFinset.mpr (Or.inl rfl)) (h ▸ one_mem _))
  obtain ⟨N, hN, hσpart⟩ := typeP_family_exists_sigmaPart hG hM hP hKM hK hKstar hU htZ ht1
  obtain ⟨y, y', hyy', hcomm, hyπ, hy'π, hyz, hy'z⟩ :=
    exists_isPiElement_mul (OddOrder.BG.Ch3.S10.sigma N) t
  have hyZ : y ∈ K ⊔ Kstar := (Subgroup.zpowers_le.mpr htZ) hyz
  have hy'Z : y' ∈ K ⊔ Kstar := (Subgroup.zpowers_le.mpr htZ) hy'z
  obtain ⟨KN, hKNN, hKN, hswap, hcent, hAπc, -, -⟩ :=
    typeP_family_member_dData hG hM hP hKM hK hKstar hU hN
  have hBπ : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma N)
      ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) := by
    intro p hp
    obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
    exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup N p (Nat.mem_primeFactors.mpr
      ⟨hpp, hpd.trans (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩)
  have hyKstar : y ∈ (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N :=
    typeP_family_isPiElement_mem_Kstar hG hM hP hKM hK hKstar hU hN hyZ hyπ
  have hy'KN : y' ∈ KN := isPiElementCompl_mem_left_of_commute hswap hcent hAπc hBπ hy'Z hy'π
  have hy1 : y ≠ 1 := fun h =>
    hσpart (by rw [show t = y' from by rw [← hyy', h, one_mul]]; exact hy'π)
  have hy'1 : y' ≠ 1 := fun h => htnot (Set.mem_biUnion (mem_ZFamilyFinset.mpr hN)
    (show t ∈ ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) from by
      rw [show t = y from by rw [← hyy', h, mul_one]]; exact hyKstar))
  obtain ⟨hNmax, -, -, -⟩ := typeP_family_member_data hG hM hP hKM hK hKstar hU hN
  refine ⟨N, hNmax, y, y', hyy'.symm, hcomm, ?_, hy'1, hKNN hy'KN, ?_, ?_⟩
  · rw [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe]
    exact ⟨(inf_le_right :
      (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N ≤ _) hyKstar, hy1⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro w hw; rw [Set.mem_singleton_iff] at hw; subst hw; exact hcomm
  · intro p hp
    simp only [piSet, Set.mem_ofPred_eq] at hp
    obtain ⟨hpp, hpdc, -⟩ := Nat.mem_primeFactors.mp hp
    have hpKN : p ∣ Nat.card ↥KN := hpdc.trans (Subgroup.card_dvd_of_le
      (by rw [← Subgroup.zpowers_eq_closure]; exact Subgroup.zpowers_le.mpr hy'KN))
    apply hKN.1 p
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKNN).toEquiv]
    exact Nat.mem_primeFactors.mpr ⟨hpp, hpKN, Nat.card_pos.ne'⟩

/-- **BG 14.7, `𝒞_G(T)` is disjoint from each `𝒞_G(M̃ᵢ)`** (mmd L4025): the TI-set's conjugacy
saturation meets no `𝒞_G(M̃ᵢ)`.  A common `z = g₁tg₁⁻¹ = g₂sg₂⁻¹` (`t ∈ T`, `s ∈ M̃ᵢ`) makes
`t = (g₁⁻¹g₂)·s·(g₁⁻¹g₂)⁻¹` a conjugate of `s ∈ M̃ᵢ`, so `t ∈ M̃(Mᵢ^{g₁⁻¹g₂})` (`Mtilde_conj_smul`)
has the type-2 form (`mem_Mtilde_imp_form`); but `t ∈ T` has the type-1 form
(`typeP_family_T_form`), contradicting Lemma 14.6 (`not_type1_of_type2`).  The last disjointness
needed for the density inequality. -/
theorem conjClassSet_T_Mtilde_disjoint [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {Mi : Subgroup G} (hMi : Mi ∈ maximalSubgroups G) :
    Disjoint (conjClassSet (((K ⊔ Kstar : Subgroup G) : Set G) \
        ⋃ N ∈ ZFamilyFinset M K,
          (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G)))
      (conjClassSet (Mtilde hG D Mi)) := by
  rw [Set.disjoint_left]
  rintro z ⟨t, htT, g₁, rfl⟩ ⟨s, hsM, g₂, hz₂⟩
  obtain ⟨N, hNmax, y, y', hgyy', hcomm, hy, hy'1, hy'N, hy'C, hy'κ⟩ :=
    typeP_family_T_form hG hM hP hKM hK hKstar hU htT
  have heq : t = MulAut.conj (g₁⁻¹ * g₂) • s := by
    rw [MulAut.smul_def, MulAut.conj_apply,
      show (g₁⁻¹ * g₂) * s * (g₁⁻¹ * g₂)⁻¹ = g₁⁻¹ * (g₂ * s * g₂⁻¹) * g₁ from by group, hz₂]
    group
  have htM : t ∈ Mtilde hG D (MulAut.conj (g₁⁻¹ * g₂) • Mi) := by
    rw [← Mtilde_conj_smul, heq]; exact Set.smul_mem_smul_set hsM
  obtain ⟨x, x'', htxx, hlenx, hx''R⟩ := mem_Mtilde_imp_form hG D
    (mem_maximalSubgroups_of_isConjugateSubgroup hMi ⟨g₁⁻¹ * g₂, rfl⟩) htM
  exact not_type1_of_type2 hG D hNmax hy hgyy' hcomm hy'1 hy'N hy'C hy'κ ⟨x, x'', htxx, hlenx,
      hx''R⟩

/-- **BG 14.7, type-`P₁` Hall complement card** (mmd L4039, "`Kᵢ` complements `M_{iσ}` in `M_i`"):
for a type-`P₁` maximal subgroup `N` with a Hall `κ(N)`-subgroup `K_N ≤ N`, the order factors as
`|N| = |N_σ|·|K_N|`.  For type `P₁`, `κ(N) = π(N) − σ(N)`, so `K_N` is a Hall `σ(N)′`-subgroup
complementing the normal Hall `σ(N)`-subgroup `N_σ` (`Msigma_isHall`).  The proof is the σ-part
uniqueness: with `m = |N_σ|`, `j = [N : N_σ]`, `a = |K_N|`, `j' = [N : K_N]`, one has
`m·j = |N| = a·j'` with `m`, `j'` being `σ`-numbers and `a`, `j` being `σ′`-numbers, so `a = j`.
This is the `[N : N_σ] = kᵢ` identity the density inequality of Theorem 14.7(e) uses to rewrite
`(|N_σ| − 1)·[G : N]` as `(1/kᵢ − 1/|N|)·|G|`. -/
theorem typeP1_card_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {N KN : Subgroup G} (hNmax : N ∈ maximalSubgroups G) (hP1 : IsTypeP1 N)
    (hKN : KN ≤ N) (hKN_hall : Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N)) :
    Nat.card ↥N = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N) * Nat.card ↥KN := by
  classical
  have hMσle : OddOrder.BG.Ch3.S10.Msigma N ≤ N := OddOrder.BG.Ch3.S10.Msigma_le N
  have hMσHall := OddOrder.BG.Ch3.S10.Msigma_isHall hG hNmax
  -- card transfers between `subgroupOf N` and the ambient subgroup
  have hcardNσ : Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N)
      = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσle).toEquiv
  have hcardKN : Nat.card ↥(KN.subgroupOf N) = Nat.card ↥KN :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN).toEquiv
  -- Lagrange inside `↥N`
  have hlagNσ : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N)
      * ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N).index = Nat.card ↥N := by
    rw [← hcardNσ]; exact Subgroup.card_mul_index _
  have hlagKN : Nat.card ↥KN * (KN.subgroupOf N).index = Nat.card ↥N := by
    rw [← hcardKN]; exact Subgroup.card_mul_index _
  set m := Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N) with hm
  set j := ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N).index with hjdef
  set a := Nat.card ↥KN with ha
  set j' := (KN.subgroupOf N).index with hj'def
  -- `m`'s primes lie in `σ(N)` (`N_σ` is a Hall `σ`-subgroup)
  have hm_sigma : ∀ p, p ∈ m.primeFactors → p ∈ OddOrder.BG.Ch3.S10.sigma N := hMσHall.1
  -- `a`'s primes avoid `σ(N)` (`κ(N) ⊆ σ(N)′`)
  have ha_sigma : ∀ p, p ∈ a.primeFactors → p ∉ OddOrder.BG.Ch3.S10.sigma N := fun p hp =>
    kappa_subset_sigmaCompl (hKN_hall.1 p (by rw [hcardKN]; exact hp))
  -- `j`'s primes avoid `σ(N)` (`j ∣ (N_σ).index`, a Hall index)
  have hj_div : j ∣ (OddOrder.BG.Ch3.S10.Msigma N).index :=
    Subgroup.relIndex_dvd_index_of_le hMσle
  have hj_sigma : ∀ p, p ∈ j.primeFactors → p ∉ OddOrder.BG.Ch3.S10.sigma N := fun p hp =>
    hMσHall.2 p (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hp).1,
      (Nat.dvd_of_mem_primeFactors hp).trans hj_div, Subgroup.index_ne_zero_of_finite⟩)
  -- `j'`'s primes lie in `σ(N)` (type `P₁`: `κ(N) = π(N) − σ(N)`)
  have hj'_dvd_N : j' ∣ Nat.card ↥N := Subgroup.index_dvd_card _
  have hj'_sigma : ∀ p, p ∈ j'.primeFactors → p ∈ OddOrder.BG.Ch3.S10.sigma N := by
    intro p hp
    have hpprime := (Nat.mem_primeFactors.mp hp).1
    have hp_dvd_N : p ∣ Nat.card ↥N := (Nat.dvd_of_mem_primeFactors hp).trans hj'_dvd_N
    have hp_notκ : p ∉ kappa N := hKN_hall.2 p hp
    rw [hP1.2] at hp_notκ
    by_contra hpσ
    exact hp_notκ ⟨Nat.mem_primeFactors.mpr ⟨hpprime, hp_dvd_N, Nat.card_pos.ne'⟩, hpσ⟩
  -- coprimalities and the `a = j` matching
  have hcop_am : Nat.Coprime a m := Nat.coprime_of_dvd fun p hp hpa hpm =>
    ha_sigma p (Nat.mem_primeFactors.mpr ⟨hp, hpa, Nat.card_pos.ne'⟩)
      (hm_sigma p (Nat.mem_primeFactors.mpr ⟨hp, hpm, Nat.card_pos.ne'⟩))
  have hcop_jj' : Nat.Coprime j j' := Nat.coprime_of_dvd fun p hp hpj hpj' =>
    hj_sigma p (Nat.mem_primeFactors.mpr ⟨hp, hpj, Subgroup.index_ne_zero_of_finite⟩)
      (hj'_sigma p (Nat.mem_primeFactors.mpr ⟨hp, hpj', Subgroup.index_ne_zero_of_finite⟩))
  have ha_dvd_j : a ∣ j := hcop_am.dvd_of_dvd_mul_left (by rw [hlagNσ]; exact ⟨j', hlagKN.symm⟩)
  have hj_dvd_a : j ∣ a := hcop_jj'.dvd_of_dvd_mul_right (by rw [hlagKN]; exact ⟨m, by
    rw [← hlagNσ]; ring⟩)
  have hja : j = a := Nat.dvd_antisymm hj_dvd_a ha_dvd_j
  rw [← hlagNσ, hja]

/-- **BG 14.7, `1 ∉ M̃`** (mmd L3920): the identity is never a "twisted" product `x·x'`
(`x ∈ M_σ^#`, `x' ∈ R(x)`).  If `x·x' = 1` then `x' = x⁻¹`, which has the same order as the
`σ(N)`-element `x`, so `x'` is a `σ(N)`-element; but `x' ∈ R(x)` is a `σ(N)′`-element
(`isPiElement_sigmaCompl_of_mem_Rsub`), and a nonidentity element cannot be both.  Hence each
`𝒞_G(M̃)` avoids `1` and lies in `G^#`, which the density inequality of Theorem 14.7(e) needs. -/
theorem one_not_mem_Mtilde [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {N : Subgroup G} (hN : N ∈ maximalSubgroups G) :
    (1 : G) ∉ Mtilde hG D N := by
  rintro ⟨x, hxsharp, x', hx'R, hxx'⟩
  rw [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe] at hxsharp
  obtain ⟨hxN, hx1⟩ := hxsharp
  have hx'eq : x' = x⁻¹ := (mul_eq_one_iff_inv_eq.mp hxx'.symm).symm
  have hlen : D.length x = 1 := (D.length_one_iff x).mpr ⟨hx1, ⟨N, hN, hxN⟩⟩
  have hπ : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma N)ᶜ x' :=
    isPiElement_sigmaCompl_of_mem_Rsub hG D hlen ⟨hN, hxN⟩ hx'R
  have hx'1 : x' ≠ 1 := by rw [hx'eq]; exact inv_ne_one.mpr hx1
  have hord : orderOf x' ≠ 1 := fun h => hx'1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hord
  have hordeq : orderOf x' = orderOf x := by rw [hx'eq, orderOf_inv]
  refine hπ p (Nat.mem_primeFactors.mpr ⟨hp, hpdvd, (orderOf_pos x').ne'⟩)
    (OddOrder.BG.Ch3.S10.Msigma_isPiGroup N p (Nat.mem_primeFactors.mpr ⟨hp,
      (hordeq ▸ hpdvd).trans ((OddOrder.BG.Ch3.S10.Msigma N).orderOf_dvd_natCard hxN),
      Nat.card_pos.ne'⟩))

/-- **BG Corollary 14.9, the `G#` cover under all-type-`F`** (the covering equality of the
`(8.8.a)` type-I case): when every maximal subgroup is of type `F`, the nonidentity elements of
`G` are exactly the union of the faithful covers `𝒞_G(M̃)` over the maximal subgroups.  The `⊆`
direction is `exists_mem_conjClassSet_Mtilde_of_ne_one` (the discharged form of BG Lemma 14.6),
and `⊇` is `one_not_mem_Mtilde` (`1 ∉ M̃`, so `1 ∉ 𝒞_G(M̃)`).  This is the `cover_nonidentity`
field of `BGTheoremETypeICovering`, modulo replacing the union over all maximals by the union over
conjugacy representatives (`conjClassSet (Mtilde …)` depends only on the conjugacy class via
`Mtilde_conj_smul`). -/
theorem sharpSubgroup_top_eq_iUnion_conjClassSet_Mtilde_of_typeF [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hall : ∀ M ∈ maximalSubgroups G, IsTypeF M) :
    sharpSubgroup (⊤ : Subgroup G)
      = ⋃ M ∈ maximalSubgroups G,
          conjClassSet (Mtilde hG (genuineSigmaDecomposition hG) M) := by
  set D := genuineSigmaDecomposition hG with hD
  ext g
  simp only [sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe,
    Subgroup.mem_top, true_and, Set.mem_iUnion₂]
  constructor
  · intro hg1
    obtain ⟨M, hM, hgM⟩ := exists_mem_conjClassSet_Mtilde_of_ne_one hG hall hg1
    exact ⟨M, hM, hgM⟩
  · rintro ⟨M, hM, t, ht, c, hc⟩ rfl
    exact one_not_mem_Mtilde hG D hM ((mul_eq_left.mp (mul_inv_eq_one.mp hc)) ▸ ht)

/-- **BG 14.7, the per-member `σ`-Hall identity** (mmd L4039): for a type-`P₁` member `N` of the
type-`P` family, `|N_σ|·[G : N] = [G : Z]·kᵢ*` where `kᵢ* = |Z ⊓ N_σ|` is the canonical family
factor.  This is the cancellation crux of the density inequality: it turns each
`|𝒞_G(M̃ᵢ)| = (|N_σ| − 1)·[G : N]` summand into `[G : Z]·kᵢ* − [G : N]`, so the `[G : Z]·kᵢ*`
parts cancel against the `𝒞_G(T)` count.  Proof: multiply by `kᵢ = |K_N|` and use
`|N| = |N_σ|·kᵢ` (type `P₁`, `typeP1_card_eq`), `z = kᵢ·kᵢ*` (the swap,
`card_kappaHall_sup_Kstar`), and Lagrange `|N|·[G:N] = |G| = z·[G:Z]`. -/
theorem typeP1_member_Msigma_index_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N : Subgroup G} (hN : IsZFamilyMember M K N) (hP1 : IsTypeP1 N) :
    Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N) * N.index
      = (K ⊔ Kstar).index * Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) := by
  classical
  obtain ⟨hNmax, hPN, hZN, KN, hKNN, hKN_hall, hswap, hcanon, hne⟩ :=
    typeP_family_member_data hG hM hP hKM hK hKstar hU hN
  have hz : Nat.card ↥(K ⊔ Kstar)
      = Nat.card ↥KN * Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) := by
    have h1 := card_kappaHall_sup_Kstar (M := N) (K := KN)
      (Kstar := OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G))
      hKNN hKN_hall rfl
    rw [← hswap, hcanon] at h1
    exact h1
  have hN_card : Nat.card ↥N
      = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N) * Nat.card ↥KN :=
    typeP1_card_eq hG hNmax hP1 hKNN hKN_hall
  have hlagN : Nat.card ↥N * N.index = Nat.card G := Subgroup.card_mul_index N
  have hlagZ : Nat.card ↥(K ⊔ Kstar) * (K ⊔ Kstar).index = Nat.card G :=
    Subgroup.card_mul_index _
  refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥KN)) ?_
  calc Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N) * N.index * Nat.card ↥KN
      = (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N) * Nat.card ↥KN) * N.index := by ring
    _ = Nat.card ↥N * N.index := by rw [← hN_card]
    _ = Nat.card G := hlagN
    _ = Nat.card ↥(K ⊔ Kstar) * (K ⊔ Kstar).index := hlagZ.symm
    _ = (Nat.card ↥KN * Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N))
          * (K ⊔ Kstar).index := by rw [hz]
    _ = (K ⊔ Kstar).index * Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N)
          * Nat.card ↥KN := by ring

/-- **BG 14.7, the per-member index bound** (mmd L4033): each family member `N` has
`2·[G : N] ≤ [G : Z]`, the upper bound on `[G : N]` the density inequality needs (from
`|N| ≥ 2z`, `typeP_family_two_mul_card_le`).  Cancelling `z` from `2z·[G:N] ≤ |N|·[G:N] =
|G| = z·[G:Z]`. -/
theorem typeP_member_two_mul_index_le [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N : Subgroup G} (hN : IsZFamilyMember M K N) :
    2 * N.index ≤ (K ⊔ Kstar).index := by
  have h2z : 2 * Nat.card ↥(K ⊔ Kstar) ≤ Nat.card ↥N :=
    typeP_family_two_mul_card_le hG hM hP hKM hK hKstar hU hN
  have hlagN : Nat.card ↥N * N.index = Nat.card G := Subgroup.card_mul_index N
  have hlagZ : Nat.card ↥(K ⊔ Kstar) * (K ⊔ Kstar).index = Nat.card G :=
    Subgroup.card_mul_index _
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.card_pos (α := ↥(K ⊔ Kstar)))
  calc Nat.card ↥(K ⊔ Kstar) * (2 * N.index)
      = (2 * Nat.card ↥(K ⊔ Kstar)) * N.index := by ring
    _ ≤ Nat.card ↥N * N.index := by gcongr
    _ = Nat.card G := hlagN
    _ = Nat.card ↥(K ⊔ Kstar) * (K ⊔ Kstar).index := hlagZ.symm

/-- **BG 14.7, the family has `≥ 2` members** (mmd L3993, "`n ≥ 1`"): the type-`P` family
`{M} ∪ {neighbours}` has at least two members — `M` itself and a neighbour `N ∈ 𝓜(N_G(X))` for a
line `X ∈ ℰ_p¹(K)` (`p ∣ |K|`), which is nonconjugate to `M` (`exists_typeP_partner`).  This is
the `n ≥ 1` the density inequality needs for `(n − 1)/2z ≥ 0`. -/
theorem ZFamilyFinset_one_lt_card [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    1 < (ZFamilyFinset M K).card := by
  classical
  have hPe := hP
  obtain ⟨p, hpκ⟩ := hPe
  have hpprime := hpκ.1
  obtain ⟨P, hPelem, hPM, -⟩ := hpκ.2.2
  have hpcardP : Nat.card ↥P = p := by obtain ⟨_, hc⟩ := hPelem; rwa [pow_one] at hc
  have hpK : p ∣ Nat.card ↥K := by
    have hlag : Nat.card ↥K * (K.subgroupOf M).index = Nat.card ↥M := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
      exact Subgroup.card_mul_index (K.subgroupOf M)
    have hpM : p ∣ Nat.card ↥M := hpcardP ▸ Subgroup.card_dvd_of_le hPM
    have hpidx : ¬ p ∣ (K.subgroupOf M).index := fun hd =>
      hK.2 p (Nat.mem_primeFactors.mpr ⟨hpprime, hd, Subgroup.index_ne_zero_of_finite⟩) hpκ
    exact (hpprime.dvd_mul.mp (hlag.symm ▸ hpM)).resolve_right hpidx
  have : Fact p.Prime := ⟨hpprime⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hxord : orderOf (x : G) = p := (orderOf_injective K.subtype K.subtype_injective x).trans hx
  have hXcard : Nat.card ↥(Subgroup.zpowers (x : G)) = p := by rw [Nat.card_zpowers, hxord]
  have hXelem : Subgroup.zpowers (x : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXK : Subgroup.zpowers (x : G) ≤ K := Subgroup.zpowers_le.mpr x.2
  obtain ⟨N, hNmem, hnc, -, -, -, -⟩ :=
    exists_typeP_partner hG hM hP hKM hK hKstar hU hXelem hXK
  have hNfam : IsZFamilyMember M K N :=
    Or.inr ⟨p, Subgroup.zpowers (x : G), hpprime, hXelem, hXK, hNmem⟩
  have hMN : M ≠ N := fun h => hnc (h ▸ IsConjugateSubgroup.refl M)
  exact Finset.one_lt_card.mpr ⟨M, mem_ZFamilyFinset.mpr (Or.inl rfl), N,
    mem_ZFamilyFinset.mpr hNfam, hMN⟩

/-- The identity is conjugacy-closed: if `1 ∉ A` then `1 ∉ 𝒞_G(A)` (a conjugate `g·t·g⁻¹ = 1`
forces `t = 1`).  Used to place each density piece `𝒞_G(T)`, `𝒞_G(M̃ᵢ)` inside `G^#`. -/
theorem one_not_mem_conjClassSet {A : Set G} (h : (1 : G) ∉ A) :
    (1 : G) ∉ conjClassSet A := by
  rintro ⟨t, ht, g, hg⟩
  rw [(MulAut.conj_apply g t).symm, ← map_one (MulAut.conj g)] at hg
  exact h ((MulAut.conj g).injective hg ▸ ht)

/-- **BG 14.7, the density pieces fit in `G^#`** (mmd L4035): the conjugacy saturations `𝒞_G(T)`
and `{𝒞_G(M̃ᵢ)}_{i}` over the type-`P` family are pairwise disjoint subsets of `G^# = G − {1}`, so
their cardinalities sum to at most `|G| − 1`.  Disjointness: `𝒞_G(T) ⊥ 𝒞_G(M̃ᵢ)`
(`conjClassSet_T_Mtilde_disjoint`, Lemma 14.6) and `𝒞_G(M̃ᵢ) ⊥ 𝒞_G(M̃ⱼ)`
(`conjClassSet_Mtilde_disjoint`, Lemma 14.5(b), via pairwise nonconjugacy of the family).
Membership in `G^#`: `1 ∉ T` (`1 ∈ Kᵢ*`) and `1 ∉ M̃ᵢ` (`one_not_mem_Mtilde`).  This is the
upper bound `∑ |𝒞_G(·)| ≤ |G^#|` of the density inequality of Theorem 14.7(e). -/
theorem density_pieces_ncard_le [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    (conjClassSet (((K ⊔ Kstar : Subgroup G) : Set G) \
        ⋃ N ∈ ZFamilyFinset M K,
          (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G))).ncard
      + (∑ N ∈ ZFamilyFinset M K, (conjClassSet (Mtilde hG D N)).ncard)
      ≤ Nat.card G - 1 := by
  classical
  set Tset := ((K ⊔ Kstar : Subgroup G) : Set G) \
      ⋃ N ∈ ZFamilyFinset M K,
        (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) with hTset
  set A := conjClassSet Tset with hA
  set U := ⋃ N ∈ (↑(ZFamilyFinset M K) : Set (Subgroup G)), conjClassSet (Mtilde hG D N) with hU'
  -- `U.ncard = ∑ |𝒞_G(M̃ᵢ)|`
  have hpair : (↑(ZFamilyFinset M K) : Set (Subgroup G)).PairwiseDisjoint
      (fun N => conjClassSet (Mtilde hG D N)) := by
    intro N₁ hN₁ N₂ hN₂ hne
    refine conjClassSet_Mtilde_disjoint hG D
      (typeP_family_member_data hG hM hP hKM hK hKstar hU (mem_ZFamilyFinset.mp hN₁)).1
      (typeP_family_member_data hG hM hP hKM hK hKstar hU (mem_ZFamilyFinset.mp hN₂)).1 ?_
    exact typeP_family_pairwise_nonconjugate hG hM hP hKM hK hKstar hU
      (mem_ZFamilyFinset.mp hN₁) (mem_ZFamilyFinset.mp hN₂) hne
  have hUcard : U.ncard = ∑ N ∈ ZFamilyFinset M K, (conjClassSet (Mtilde hG D N)).ncard := by
    rw [hU', Set.Finite.ncard_biUnion (ZFamilyFinset M K).finite_toSet
      (fun N _ => Set.toFinite _) hpair, finsum_mem_coe_finset]
  -- all pieces avoid `1`
  have h1T : (1 : G) ∉ Tset := fun h =>
    (Set.mem_sdiff _ |>.mp h).2 (Set.mem_iUnion₂.mpr ⟨M, mem_ZFamilyFinset.mpr (Or.inl rfl),
      SetLike.mem_coe.mpr (Subgroup.one_mem _)⟩)
  have h1A : (1 : G) ∉ A := one_not_mem_conjClassSet h1T
  have h1U : (1 : G) ∉ U := by
    rw [hU', Set.mem_iUnion₂]; rintro ⟨N, hN, hzN⟩
    exact one_not_mem_conjClassSet (one_not_mem_Mtilde hG D
      (typeP_family_member_data hG hM hP hKM hK hKstar hU (mem_ZFamilyFinset.mp hN)).1) hzN
  -- `A` disjoint from `U`
  have hAU : Disjoint A U := by
    rw [Set.disjoint_left]
    rintro z hzA hzU
    rw [hU', Set.mem_iUnion₂] at hzU
    obtain ⟨N, hN, hzN⟩ := hzU
    exact Set.disjoint_left.mp (conjClassSet_T_Mtilde_disjoint hG D hM hP hKM hK hKstar hU
      (typeP_family_member_data hG hM hP hKM hK hKstar hU (mem_ZFamilyFinset.mp hN)).1) hzA hzN
  -- `A ∪ U ⊆ G^#`
  have hsub : A ∪ U ⊆ {g : G | g ≠ 1} := by
    rintro z (hz | hz)
    · exact fun h => h1A (h ▸ hz)
    · exact fun h => h1U (h ▸ hz)
  have hWcard : ({g : G | g ≠ 1} : Set G).ncard = Nat.card G - 1 := by
    have hWeq : {g : G | g ≠ 1} = (Set.univ : Set G) \ {1} := by
      ext g; simp [Set.mem_sdiff]
    rw [hWeq, Set.ncard_sdiff (Set.singleton_subset_iff.mpr (Set.mem_univ 1)), Set.ncard_univ,
      Set.ncard_singleton]
  calc A.ncard + ∑ N ∈ ZFamilyFinset M K, (conjClassSet (Mtilde hG D N)).ncard
      = A.ncard + U.ncard := by rw [hUcard]
    _ = (A ∪ U).ncard := (Set.ncard_union_eq hAU).symm
    _ ≤ ({g : G | g ≠ 1} : Set G).ncard := Set.ncard_le_ncard hsub
    _ = Nat.card G - 1 := hWcard

/-- **BG Theorem 14.7, the density inequality** (mmd L4031-4045): some member of the type-`P`
family `{M} ∪ {neighbours}` has type `P₂`.  If every member were type `P₁`, the disjoint conjugacy
pieces `𝒞_G(T)` and `{𝒞_G(M̃ᵢ)}` would already cover `G^#`:
`|G^#| ≥ |𝒞_G(T)| + ∑ |𝒞_G(M̃ᵢ)| = |G| + n·[G:Z] − ∑ [G:Mᵢ] ≥ |G| + (n−1)·[G:Z]/… ≥ |G|`,
contradicting `|G^#| = |G| − 1`.  The `∑ [G:Z]·kᵢ*` parts cancel between the two counts
(`typeP1_member_Msigma_index_eq`); the bound uses `[G:Mᵢ] ≤ [G:Z]/2` (`|Mᵢ| ≥ 2z`) and `n ≥ 1`
(a neighbour exists).  Entirely a `ℕ` computation closed by `omega`. -/
theorem exists_typeP2_member [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    ∃ N ∈ ZFamilyFinset M K, IsTypeP2 N := by
  classical
  by_contra hcon
  push Not at hcon
  have hallP1 : ∀ N ∈ ZFamilyFinset M K, IsTypeP1 N := fun N hN =>
    (isTypeP_iff_isTypeP1_or_isTypeP2.mp
      (typeP_family_member_data hG hM hP hKM hK hKstar hU (mem_ZFamilyFinset.mp
          hN)).2.1).resolve_right
      (hcon N hN)
  -- lemma instances (explicit `T`), then fold `T`
  have hT_count := typeP_family_conjClass_T_count hG hM hP hKM hK hKstar hU
  have hT_card := typeP_family_T_count hG hM hP hKM hK hKstar hU
  have hbound := density_pieces_ncard_le hG D hM hP hKM hK hKstar hU
  have hcardlt := ZFamilyFinset_one_lt_card hG hM hP hKM hK hKstar hU
  set Tset := ((K ⊔ Kstar : Subgroup G) : Set G) \
      ⋃ N ∈ ZFamilyFinset M K,
        (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) with hTset
  have hzcard : Nat.card ↥(K ⊔ Kstar) * (K ⊔ Kstar).index = Nat.card G :=
    Subgroup.card_mul_index _
  -- per-member `M̃` additive identity and its sum
  have hmem_add : ∀ N ∈ ZFamilyFinset M K,
      (conjClassSet (Mtilde hG D N)).ncard + N.index
        = (K ⊔ Kstar).index * Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) := by
    intro N hN
    have hNmax := (typeP_family_member_data hG hM hP hKM hK hKstar hU
      (mem_ZFamilyFinset.mp hN)).1
    have hmem_id := typeP1_member_Msigma_index_eq hG hM hP hKM hK hKstar hU
      (mem_ZFamilyFinset.mp hN) (hallP1 N hN)
    rw [sigmaConjugacySaturation_Mtilde_ncard hG D hNmax, Nat.sub_one_mul]
    have hge : N.index ≤ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N) * N.index :=
      Nat.le_mul_of_pos_left _ Nat.card_pos
    omega
  have hMtilde_sum : (∑ N ∈ ZFamilyFinset M K, (conjClassSet (Mtilde hG D N)).ncard)
      + (∑ N ∈ ZFamilyFinset M K, N.index)
      = ∑ N ∈ ZFamilyFinset M K,
          (K ⊔ Kstar).index * Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl hmem_add
  -- `T` additive (multiply the `|T|` count by `[G:Z]`)
  have hmul : Tset.ncard * (K ⊔ Kstar).index
      + (∑ N ∈ ZFamilyFinset M K,
          Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) * (K ⊔ Kstar).index)
      + (K ⊔ Kstar).index
      = Nat.card G + (ZFamilyFinset M K).card * (K ⊔ Kstar).index := by
    have h := congrArg (· * (K ⊔ Kstar).index) hT_card
    simp only [add_mul, one_mul, Finset.sum_mul] at h
    rw [hzcard] at h
    exact h
  have hPcomm : (∑ N ∈ ZFamilyFinset M K,
        (K ⊔ Kstar).index * Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N))
      = ∑ N ∈ ZFamilyFinset M K,
        Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) * (K ⊔ Kstar).index :=
    Finset.sum_congr rfl (fun N _ => mul_comm _ _)
  -- key inequality `∑ [G:Mᵢ] ≤ (𝓕.card − 1)·[G:Z]`
  have hkey : (∑ N ∈ ZFamilyFinset M K, N.index)
      ≤ ((ZFamilyFinset M K).card - 1) * (K ⊔ Kstar).index := by
    have h2sum : 2 * (∑ N ∈ ZFamilyFinset M K, N.index)
        ≤ (ZFamilyFinset M K).card * (K ⊔ Kstar).index := by
      rw [Finset.mul_sum]
      calc (∑ N ∈ ZFamilyFinset M K, 2 * N.index)
          ≤ ∑ _N ∈ ZFamilyFinset M K, (K ⊔ Kstar).index :=
            Finset.sum_le_sum (fun N hN => typeP_member_two_mul_index_le hG hM hP hKM hK hKstar hU
              (mem_ZFamilyFinset.mp hN))
        _ = (ZFamilyFinset M K).card * (K ⊔ Kstar).index := by
            rw [Finset.sum_const, smul_eq_mul]
    have hc2 : (ZFamilyFinset M K).card ≤ 2 * ((ZFamilyFinset M K).card - 1) := by omega
    have hstep : (ZFamilyFinset M K).card * (K ⊔ Kstar).index
        ≤ 2 * (((ZFamilyFinset M K).card - 1) * (K ⊔ Kstar).index) := by
      rw [← mul_assoc]; exact mul_le_mul_left hc2 _
    omega
  -- expansion fact relating `𝓕.card·[G:Z]` and `(𝓕.card−1)·[G:Z]`
  have hexp : (ZFamilyFinset M K).card * (K ⊔ Kstar).index
      = ((ZFamilyFinset M K).card - 1) * (K ⊔ Kstar).index + (K ⊔ Kstar).index := by
    have hle : (K ⊔ Kstar).index ≤ (ZFamilyFinset M K).card * (K ⊔ Kstar).index :=
      Nat.le_mul_of_pos_left _ (by omega)
    rw [Nat.sub_one_mul]; omega
  have hgpos : 1 ≤ Nat.card G := Nat.card_pos
  omega

/-- **A `πᶜ`-subgroup of an internal direct product `Z = A × B` (`A` a `πᶜ`-group, `B` a
`π`-group) lies in the left factor `A`.**  Subgroup generalisation of
`isPiElementCompl_mem_left_of_commute`: `A.subgroupOf Z` is the normal Hall `πᶜ`-subgroup of `Z`,
so any `πᶜ`-subgroup `L ≤ Z` lies in it (`isPiGroup_le_of_normal_isHallSubgroup`).  In the `n = 1`
collapse of Theorem 14.7, `A = Kᵢ` (the Hall `κ(Mᵢ) ⊆ σ(Mᵢ)′`-subgroup), `B = Kᵢ*` (the
`σ(Mᵢ)`-part), and `L = Kⱼ*` (a `σ(Mᵢ)′`-group since `σ(Mⱼ) ∩ σ(Mᵢ) = ∅`), forcing `Kⱼ* ≤ Kᵢ`. -/
theorem isPiSubgroup_le_left_of_commute [Finite G] {A B Z L : Subgroup G} {π : Set ℕ}
    (hswap : Z = A ⊔ B) (hcent : B ≤ Subgroup.centralizer (A : Set G))
    (hAπc : Subgroup.IsPiSubgroup πᶜ A) (hBπ : Subgroup.IsPiSubgroup π B)
    (hLZ : L ≤ Z) (hLπc : Subgroup.IsPiSubgroup πᶜ L) : L ≤ A := by
  classical
  have hAZ : A ≤ Z := by rw [hswap]; exact le_sup_left
  have hcomm : ∀ a ∈ A, ∀ c ∈ B, Commute a c := fun a ha c hc =>
    Subgroup.mem_centralizer_iff.mp (hcent hc) a ha
  have hcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥B) := by
    apply Nat.coprime_of_dvd
    intro p hp hpA hpB
    exact (hAπc p (Nat.mem_primeFactors.mpr ⟨hp, hpA, Nat.card_pos.ne'⟩))
      (hBπ p (Nat.mem_primeFactors.mpr ⟨hp, hpB, Nat.card_pos.ne'⟩))
  have hdisj : A ⊓ B = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hnorm : Z ≤ Subgroup.normalizer (A : Set G) := by
    rw [hswap]; exact (sup_le_normalizer_inf_of_commute hcent).trans inf_le_left
  have hAnZ : (A.subgroupOf Z).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAZ).mpr hnorm
  have hZcard : Nat.card ↥Z = Nat.card ↥A * Nat.card ↥B := by
    rw [hswap]; exact card_sup_of_commute_of_disjoint hcomm hdisj
  have hcardSub : Nat.card ↥(A.subgroupOf Z) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAZ).toEquiv
  have hidx : (A.subgroupOf Z).index = Nat.card ↥B := by
    have hl := Subgroup.card_mul_index (A.subgroupOf Z)
    rw [hcardSub, hZcard] at hl
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hl
  have hHall : Ch03.IsHallSubgroup πᶜ (A.subgroupOf Z) := by
    refine ⟨fun p hp => ?_, fun p hp hpc => ?_⟩
    · rw [hcardSub] at hp; exact hAπc p hp
    · exact hpc (hBπ p (by rwa [hidx] at hp))
  have hLsub : L.subgroupOf Z ≤ A.subgroupOf Z := by
    refine OddOrder.BG.Ch3.S10.isPiGroup_le_of_normal_isHallSubgroup hHall (fun p hp => ?_)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLZ).toEquiv] at hp
    exact hLπc p hp
  intro x hx
  have hmem : (⟨x, hLZ hx⟩ : ↥Z) ∈ L.subgroupOf Z := Subgroup.mem_subgroupOf.mpr hx
  exact Subgroup.mem_subgroupOf.mp (hLsub hmem)

/-- **BG Theorem 14.7, the `n = 1` collapse** (mmd L4047): the type-`P` family `{M} ∪ {neighbours}`
has exactly two members.  By the density inequality some member `Mᵢ` is type `P₂`, so its Hall
`κ(Mᵢ)`-subgroup `Kᵢ` has prime order `q` (Proposition 14.2(g)).  In the swap `Z = Kᵢ × Kᵢ*`, `Kᵢ`
is the normal Hall `σ(Mᵢ)′`-subgroup; every other member `Mⱼ` has `Kⱼ* = Z ⊓ M_{jσ}` a nontrivial
`σ(Mᵢ)′`-subgroup of `Z` (`σ(Mⱼ) ∩ σ(Mᵢ) = ∅` by Theorem 13.9), hence `Kⱼ* ≤ Kᵢ`
(`isPiSubgroup_le_left_of_commute`), and `Kⱼ* = Kᵢ` since `|Kᵢ| = q` is prime.  But the `Kⱼ*` are
pairwise disjoint (`typeP_family_Kstar_disjoint`), so two distinct neighbours would give
`Kᵢ = Kⱼ* ⊓ Kₗ* = 1`, contradicting `q ≥ 2`.  Thus at most one neighbour, i.e. `|family| = 2`. -/
theorem family_card_eq_two [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    (ZFamilyFinset M K).card = 2 := by
  classical
  refine le_antisymm ?_ (ZFamilyFinset_one_lt_card hG hM hP hKM hK hKstar hU)
  obtain ⟨Mi, hMi𝓕, hMiP2⟩ := exists_typeP2_member hG D hM hP hKM hK hKstar hU
  obtain ⟨hMimax, hMiP, hZMi, KNi, hKNiMi, hKNi, hswapi, hcanoni, hnei⟩ :=
    typeP_family_member_data hG hM hP hKM hK hKstar hU (mem_ZFamilyFinset.mp hMi𝓕)
  -- `|KNi| = q` is prime (Proposition 14.2(g))
  have : Group.IsSolvable ↥Mi := hG.isSolvable_of_mem_maximalSubgroups hMimax
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥Mi)
    ((kappa Mi ∪ OddOrder.BG.Ch3.S10.sigma Mi)ᶜ)
  have hUeq : (U'.map Mi.subtype).subgroupOf Mi = U' :=
    Subgroup.comap_map_eq_self_of_injective Mi.subtype_injective U'
  have hUi : Ch03.IsHallSubgroup ((kappa Mi ∪ OddOrder.BG.Ch3.S10.sigma Mi)ᶜ)
      ((U'.map Mi.subtype).subgroupOf Mi) := by rw [hUeq]; exact hU'
  obtain ⟨q, hq, hqcard, -⟩ :=
    ((typeP_structure hG hMimax hMiP hKNiMi hKNi rfl hUi).2.2.2.2.1 hMiP2).2
  have hKNine : KNi ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hqcard; exact hq.ne_one hqcard.symm
  -- the `σ(Mᵢ)′`-Hall data of the swap `Z = KNi × Kᵢ*` for `isPiSubgroup_le_left_of_commute`
  have hswapMi : K ⊔ Kstar = KNi ⊔ ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma Mi) :=
    hswapi.trans (by rw [hcanoni])
  have hcentMi : (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma Mi
      ≤ Subgroup.centralizer (KNi : Set G) := hcanoni ▸ inf_le_right
  have hAπc : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma Mi)ᶜ KNi :=
    kappaHall_isPiSubgroup_sigmaCompl hKNiMi hKNi
  have hBπ : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma Mi)
      ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma Mi) := fun p hp =>
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup Mi p (Nat.mem_primeFactors.mpr
      ⟨(Nat.mem_primeFactors.mp hp).1,
        (Nat.dvd_of_mem_primeFactors hp).trans (Subgroup.card_dvd_of_le inf_le_right),
        Nat.card_pos.ne'⟩)
  -- every member `≠ Mᵢ` has its canonical factor equal to `KNi`
  have hKstarEq : ∀ N ∈ (ZFamilyFinset M K).erase Mi,
      (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N = KNi := by
    intro N hNe
    have hN𝓕 := Finset.mem_of_mem_erase hNe
    have hNneMi : N ≠ Mi := Finset.ne_of_mem_erase hNe
    obtain ⟨hNmax, hNP, -, KNj, -, -, -, hcanonj, hnej⟩ :=
      typeP_family_member_data hG hM hP hKM hK hKstar hU (mem_ZFamilyFinset.mp hN𝓕)
    have hnej' : (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N ≠ ⊥ := hcanonj ▸ hnej
    have hdisjσ : Disjoint (OddOrder.BG.Ch3.S10.sigma Mi) (OddOrder.BG.Ch3.S10.sigma N) :=
      sigma_disjoint_of_nonconjugate hG hMimax hNmax
        (typeP_family_pairwise_nonconjugate hG hM hP hKM hK hKstar hU
          (mem_ZFamilyFinset.mp hMi𝓕) (mem_ZFamilyFinset.mp hN𝓕) (Ne.symm hNneMi))
    have hLπc : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma Mi)ᶜ
        ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) := fun p hp => by
      have hpσN : p ∈ OddOrder.BG.Ch3.S10.sigma N :=
        OddOrder.BG.Ch3.S10.Msigma_isPiGroup N p (Nat.mem_primeFactors.mpr
          ⟨(Nat.mem_primeFactors.mp hp).1,
            (Nat.dvd_of_mem_primeFactors hp).trans (Subgroup.card_dvd_of_le inf_le_right),
            Nat.card_pos.ne'⟩)
      exact fun hpσMi => Set.disjoint_left.mp hdisjσ hpσMi hpσN
    have hle : (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N ≤ KNi :=
      isPiSubgroup_le_left_of_commute hswapMi hcentMi hAπc hBπ inf_le_left hLπc
    -- prime-order `KNi`: a nontrivial subgroup is all of it
    have hdvd : Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) ∣ q := by
      rw [← hqcard]; exact Subgroup.card_dvd_of_le hle
    have hne1 : Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) ≠ 1 :=
      fun h => hnej' (Subgroup.eq_bot_of_card_eq _ h)
    have hcardeq : Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) = Nat.card ↥KNi := by
      rw [hqcard]; exact (hq.eq_one_or_self_of_dvd _ hdvd).resolve_left hne1
    exact Subgroup.eq_of_le_of_card_ge hle hcardeq.ge
  -- at most one member is `≠ Mᵢ`
  have herase_le : ((ZFamilyFinset M K).erase Mi).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    have hdisj := typeP_family_Kstar_disjoint hG hM hP hKM hK hKstar hU
      (mem_ZFamilyFinset.mp (Finset.mem_of_mem_erase ha))
      (mem_ZFamilyFinset.mp (Finset.mem_of_mem_erase hb)) hab
    rw [hKstarEq a ha, hKstarEq b hb, inf_idem] at hdisj
    rw [hdisj, Subgroup.card_bot] at hqcard
    exact hq.ne_one hqcard.symm
  have hcard_erase := Finset.card_erase_of_mem hMi𝓕
  omega

/-- **BG Theorem 14.7, the unique partner `M*`** (mmd L4047): since the type-`P` family has exactly
two members (`family_card_eq_two`) and `M` is one of them, there is a unique other member `M*`, the
nonconjugate partner of Theorem 14.7.  It is a type-`P` maximal subgroup containing `Z = K ⊔ K*`,
nonconjugate to `M`. -/
theorem exists_partner [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    ∃ Mstar : Subgroup G, Mstar ≠ M ∧ IsZFamilyMember M K Mstar ∧
      ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar := by
  classical
  obtain ⟨a, b, hab, hfam⟩ :=
    Finset.card_eq_two.mp (family_card_eq_two hG D hM hP hKM hK hKstar hU)
  have hMfam : M ∈ ZFamilyFinset M K := mem_ZFamilyFinset.mpr (Or.inl rfl)
  rw [hfam, Finset.mem_insert, Finset.mem_singleton] at hMfam
  rcases hMfam with hMa | hMb
  · refine ⟨b, by rw [hMa]; exact Ne.symm hab,
      mem_ZFamilyFinset.mp (by rw [hfam]; simp), fun N hN => ?_⟩
    have hN' : N ∈ ({a, b} : Finset (Subgroup G)) := hfam ▸ mem_ZFamilyFinset.mpr hN
    rw [Finset.mem_insert, Finset.mem_singleton] at hN'
    exact hN'.imp (fun h => h.trans hMa.symm) id
  · refine ⟨a, by rw [hMb]; exact hab,
      mem_ZFamilyFinset.mp (by rw [hfam]; simp), fun N hN => ?_⟩
    have hN' : N ∈ ({a, b} : Finset (Subgroup G)) := hfam ▸ mem_ZFamilyFinset.mpr hN
    rw [Finset.mem_insert, Finset.mem_singleton] at hN'
    exact hN'.elim (fun h => Or.inr h) (fun h => Or.inl (h.trans hMb.symm))

/-- **BG Theorem 14.7(f), the type-`P₂` dichotomy** (mmd L4047): for the partner `M*` (so every
family member is `M` or `M*`), one of `M`, `M*` is type `P₂`.  Immediate from the density
inequality (`exists_typeP2_member`): the type-`P₂` member it produces is `M` or `M*`. -/
theorem isTypeP2_or_isTypeP2_partner [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar) :
    IsTypeP2 M ∨ IsTypeP2 Mstar := by
  obtain ⟨N, hN𝓕, hNP2⟩ := exists_typeP2_member hG D hM hP hKM hK hKstar hU
  rcases hpart N (mem_ZFamilyFinset.mp hN𝓕) with h | h
  · subst h; exact Or.inl hNP2
  · subst h; exact Or.inr hNP2

/-- **BG Theorem 14.7, `π(K) ⊆ σ(M*)`** (mmd L3987): every prime `p` dividing `|K|` lies in
`σ(M*)`, for the partner `M*`.  For a line `X ∈ ℰ_p¹(K)`, the maximal subgroup over `N_G(X)` is a
type-`P` family member nonconjugate to `M` (`exists_typeP_partner`), hence `= M*` (the only other
member), and `X ≤ M*_σ` gives `p ∈ σ(M*)`.  This is the half forcing `K ≤ M*_σ` in the partner
structure `Z ⊓ M*_σ = K`. -/
theorem kappaHall_primes_subset_sigma_partner [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U Mstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar)
    {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card ↥K) :
    p ∈ OddOrder.BG.Ch3.S10.sigma Mstar := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hxord : orderOf (x : G) = p := (orderOf_injective K.subtype K.subtype_injective x).trans hx
  have hXcard : Nat.card ↥(Subgroup.zpowers (x : G)) = p := by rw [Nat.card_zpowers, hxord]
  have hXelem : Subgroup.zpowers (x : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXK : Subgroup.zpowers (x : G) ≤ K := Subgroup.zpowers_le.mpr x.2
  obtain ⟨N, hNmem, hnc, -, hXNσ, -, -⟩ :=
    exists_typeP_partner hG hM hP hKM hK hKstar hU hXelem hXK
  have hNfam : IsZFamilyMember M K N :=
    Or.inr ⟨p, Subgroup.zpowers (x : G), hp, hXelem, hXK, hNmem⟩
  have hNM : N ≠ M :=
    fun h => hnc (h ▸ (⟨1, by rw [map_one, one_smul]⟩ : IsConjugateSubgroup M M))
  have hNMstar : N = Mstar := (hpart N hNfam).resolve_left hNM
  rw [← hNMstar]
  exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup N p (Nat.mem_primeFactors.mpr
    ⟨hp, (dvd_of_eq hXcard.symm).trans (Subgroup.card_dvd_of_le hXNσ), Nat.card_pos.ne'⟩)

/-- **BG Theorem 14.7, the partner canonical factor** (mmd L3995): `Z ⊓ M*_σ = K`.  In the swap
`Z = M*'s K* × M*'s κ-Hall`, the partner's canonical factor `Z ⊓ M*_σ` equals `K` (the original
`M`'s Hall `κ`-subgroup).  Two inclusions: `Z ⊓ M*_σ` is a `σ(M)′`-subgroup of the direct product
`Z = K × K*` (`σ(M*) ∩ σ(M) = ∅`), so it lies in the `σ(M)′`-Hall factor `K`
(`isPiSubgroup_le_left_of_commute`); conversely `K ≤ M*_σ` because every prime of `K` lies in
`σ(M*)` (`kappaHall_primes_subset_sigma_partner`).  This is the structural fact that turns the
family's `T = Z − ⋃ Kᵢ*` into `Ẑ = Z − (K ∪ K*)`. -/
theorem partner_canonical_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar) :
    (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma Mstar = K := by
  classical
  have hMstarmax : Mstar ∈ maximalSubgroups G :=
    (typeP_family_member_data hG hM hP hKM hK hKstar hU hMstarmem).1
  have hZMstar : K ⊔ Kstar ≤ Mstar :=
    (typeP_family_member_data hG hM hP hKM hK hKstar hU hMstarmem).2.2.1
  have hnc : ¬ IsConjugateSubgroup M Mstar :=
    typeP_family_pairwise_nonconjugate hG hM hP hKM hK hKstar hU (Or.inl rfl) hMstarmem
      (Ne.symm hMstarne)
  have hσdisj : Disjoint (OddOrder.BG.Ch3.S10.sigma M) (OddOrder.BG.Ch3.S10.sigma Mstar) :=
    sigma_disjoint_of_nonconjugate hG hM hMstarmax hnc
  refine le_antisymm ?_ (le_inf le_sup_left ?_)
  · -- `Z ⊓ M*_σ ≤ K`: it is a `σ(M)′`-subgroup of `Z = K × K*`
    refine isPiSubgroup_le_left_of_commute (π := OddOrder.BG.Ch3.S10.sigma M) rfl
      (hKstar ▸ inf_le_right) (kappaHall_isPiSubgroup_sigmaCompl hKM hK) (fun q hq => ?_)
      inf_le_left (fun q hq => ?_)
    · exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q (Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primeFactors.mp hq).1, (Nat.dvd_of_mem_primeFactors hq).trans
          (Subgroup.card_dvd_of_le (hKstar.le.trans inf_le_left)), Nat.card_pos.ne'⟩)
    · have hqσMstar : q ∈ OddOrder.BG.Ch3.S10.sigma Mstar :=
        OddOrder.BG.Ch3.S10.Msigma_isPiGroup Mstar q (Nat.mem_primeFactors.mpr
          ⟨(Nat.mem_primeFactors.mp hq).1, (Nat.dvd_of_mem_primeFactors hq).trans
            (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩)
      exact fun hqσM => Set.disjoint_left.mp hσdisj hqσM hqσMstar
  · -- `K ≤ M*_σ`: every prime of `K` lies in `σ(M*)`
    refine OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
      (OddOrder.BG.Ch3.S10.Msigma_isHall hG hMstarmax) (le_sup_left.trans hZMstar) (fun q hq => ?_)
    exact kappaHall_primes_subset_sigma_partner hG hM hP hKM hK hKstar hU hpart
      (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq)

/-- **BG Theorem 14.7(e), the family `Z ⊓ N_σ` collapse** (mmd L4051): for the type-`P` family
`{M, M*}` (recorded by `hpart`), the union of the canonical factors collapses to `K ∪ K*`,
`⋃_{N ∈ 𝓕} (Z ⊓ N_σ) = K ∪ K*`, since `Z ⊓ M_σ = K*` (`typeP_self_member`) and `Z ⊓ M*_σ = K`
(`partner_canonical_eq`).  Factored out of `typeP_zTilde_isTI`; reused by the `> ½|G|` density
count `typeP_zTilde_conjClass_gt_half`, where it identifies `Ẑ = Z − (K ∪ K*)` with the family
TI-set `T = Z − ⋃_{N} (Z ⊓ N_σ)`. -/
theorem family_inf_msigma_union_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar) :
    (⋃ N ∈ ZFamilyFinset M K,
        (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G))
      = ((K : Set G) ∪ (Kstar : Set G)) := by
  classical
  have hcanonM : (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma M = Kstar :=
    (typeP_self_member hG hM hP hKM hK hKstar hU).1
  have hcanonMstar : (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma Mstar = K :=
    partner_canonical_eq hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  apply Set.Subset.antisymm
  · rintro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨N, hN, hxN⟩ := hx
    rcases hpart N (mem_ZFamilyFinset.mp hN) with rfl | rfl
    · rw [hcanonM] at hxN; exact Or.inr hxN
    · rw [hcanonMstar] at hxN; exact Or.inl hxN
  · rintro x (hxK | hxKstar)
    · exact Set.mem_iUnion₂.mpr ⟨Mstar, mem_ZFamilyFinset.mpr hMstarmem,
        by rw [hcanonMstar]; exact hxK⟩
    · exact Set.mem_iUnion₂.mpr ⟨M, mem_ZFamilyFinset.mpr (Or.inl rfl),
        by rw [hcanonM]; exact hxKstar⟩

/-- **BG Theorem 14.7(e), `Ẑ` is a TI-subset** (mmd L4051): with the family `{M, M*}`, the
union `⋃_{N} (Z ⊓ N_σ)` collapses to `K ∪ K*` (`family_inf_msigma_union_eq`), so the family TI-set
`T = Z − ⋃ (Z ⊓ N_σ)` equals `Ẑ = Z − (K ∪ K*)`.  Hence `Ẑ` inherits the TI property from
`typeP_family_T_isTI`.  A conjunct of the `∃! Mstar`. -/
theorem typeP_zTilde_isTI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar) :
    OddOrder.GroupTheory.IsTISubset (zTilde K Kstar) (K ⊔ Kstar) := by
  classical
  have hunion := family_inf_msigma_union_eq hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  have hzeq : zTilde K Kstar = ((K ⊔ Kstar : Subgroup G) : Set G) \
      ⋃ N ∈ ZFamilyFinset M K,
        (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) := by
    simp only [zTilde]; rw [hunion]
  rw [hzeq]
  exact typeP_family_T_isTI hG hM hP hKM hK hKstar hU

/-- Pure `ℕ` identity for the `|Ẑ|` count: `k·l − (k + l − 1) = (k − 1)(l − 1)` for `k, l ≥ 1`. -/
theorem nat_mul_sub_kl_identity {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    k * l - (k + l - 1) = (k - 1) * (l - 1) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hk
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hl
  have h1 : (1 + a) * (1 + b) = a * b + a + b + 1 := by ring
  have h2 : (1 + a - 1) * (1 + b - 1) = a * b := by simp
  omega

/-- `1 ∉ Ẑ`: the identity lies in `K ≤ K ⊔ K*`, hence in the removed set `K ∪ K*`.  So
`sharpSubgroup Ẑ = Ẑ` and `𝒞_G(Ẑ^#) ⊆ G^#` — a prerequisite for the NonType-I `G^#` cover. -/
theorem one_not_mem_zTilde (K Kstar : Subgroup G) : (1 : G) ∉ zTilde K Kstar := by
  rw [zTilde, Set.mem_sdiff, not_and_or, not_not]
  exact Or.inr (Set.mem_union_left _ (SetLike.mem_coe.mpr K.one_mem))

/-- **`Ẑ` is symmetric in its two factors**: `zTilde K K* = zTilde K* K` (both `K ⊔ K*` and
`K ∪ K*` are symmetric).  Used for the partner side, where the swap exchanges `K ↔ K*`. -/
theorem zTilde_comm (K Kstar : Subgroup G) : zTilde K Kstar = zTilde Kstar K := by
  rw [zTilde, zTilde, sup_comm, Set.union_comm]

/-- **`Ẑ` is `G`-conjugation equivariant**: `(zTilde K K*)^g = zTilde (K^g) (K*^g)`.  Conjugation is
a set bijection commuting with `\`, `∪`, and `⊔` (`Subgroup.smul_sup`), so it distributes through
the `zTilde = (K ⊔ K*) ∖ (K ∪ K*)` definition.  Lets a `zTilde` of a conjugate type-`P` maximal be
identified (up to `conjClassSet`) with a fixed `Ẑ`. -/
theorem zTilde_conj_smul (g : G) (K Kstar : Subgroup G) :
    MulAut.conj g • zTilde K Kstar
      = zTilde (MulAut.conj g • K) (MulAut.conj g • Kstar) := by
  rw [zTilde, zTilde, Set.smul_set_sdiff, Set.smul_set_union,
    ← Subgroup.coe_pointwise_smul, ← Subgroup.coe_pointwise_smul,
    ← Subgroup.coe_pointwise_smul, Subgroup.smul_sup]

/-- **`𝒞_G` is invariant under conjugating the underlying set**: `𝒞_G(S^g) = 𝒞_G(S)` (conjugation
permutes `G`-conjugacy classes, fixing their union). -/
theorem conjClassSet_conj_smul (g : G) (S : Set G) :
    conjClassSet (MulAut.conj g • S) = conjClassSet S := by
  ext y
  simp only [OddOrder.GroupTheory.mem_conjClassSet]
  constructor
  · rintro ⟨t, ht, b, rfl⟩
    rw [Set.mem_smul_set] at ht
    obtain ⟨s, hs, hst⟩ := ht
    refine ⟨s, hs, b * g, ?_⟩
    rw [← hst, MulAut.smul_def, MulAut.conj_apply]; group
  · rintro ⟨s, hs, b, rfl⟩
    refine ⟨MulAut.conj g • s, Set.smul_mem_smul_set hs, b * g⁻¹, ?_⟩
    rw [MulAut.smul_def, MulAut.conj_apply]; group

/-- **`𝒞_G(Ẑ)` only depends on the `G`-conjugacy class of `(K, K*)`**: conjugating both factors by
`g` leaves `𝒞_G(zTilde K K*)` unchanged.  This is the fix-`W` step — a `zTilde` of a conjugate
type-`P` maximal has the same `conjClassSet` as the reference `Ẑ`. -/
theorem conjClassSet_zTilde_conj_eq (g : G) (K Kstar : Subgroup G) :
    conjClassSet (zTilde (MulAut.conj g • K) (MulAut.conj g • Kstar))
      = conjClassSet (zTilde K Kstar) := by
  rw [← zTilde_conj_smul, conjClassSet_conj_smul]

/-- **Algebraic core of the κ→Ẑ identification** (the final step of BG `mFT_partition` part 2):
a product `y · y'` of a nonidentity `K*`-element `y` and a nonidentity `K`-element `y'` lies in
`Ẑ = (K ⊔ K*) ∖ (K ∪ K*)`, provided `K ⊓ K* = ⊥`.  Membership in `K ⊔ K*` is immediate; `y·y' ∉ K`
because then `y = (y·y')·y'⁻¹ ∈ K ⊓ K* = ⊥` contradicts `y ≠ 1`, and dually `y·y' ∉ K*`.  The deep
part of κ→Ẑ (placing the σ-part `y` in `K* = C_{M_σ}(K)` via `Z = K ⊔ K*` cyclic, and the
`κ`-element `y'` in the Hall `K`) wraps this core. -/
theorem mem_zTilde_of_mul {K Kstar : Subgroup G} (htri : K ⊓ Kstar = ⊥)
    {y y' : G} (hy : y ∈ Kstar) (hy1 : y ≠ 1) (hy' : y' ∈ K) (hy'1 : y' ≠ 1) :
    y * y' ∈ zTilde K Kstar := by
  rw [zTilde, Set.mem_sdiff]
  refine ⟨(K ⊔ Kstar).mul_mem (Subgroup.mem_sup_right hy) (Subgroup.mem_sup_left hy'), ?_⟩
  rw [Set.mem_union, not_or]
  refine ⟨fun hmem => hy1 ?_, fun hmem => hy'1 ?_⟩
  · have hyK : y ∈ K := by
      have h := K.mul_mem (SetLike.mem_coe.mp hmem) (K.inv_mem hy')
      rwa [mul_assoc, mul_inv_cancel, mul_one] at h
    have h := Subgroup.mem_inf.mpr ⟨hyK, hy⟩
    rwa [htri, Subgroup.mem_bot] at h
  · have hy'Ks : y' ∈ Kstar := by
      have h := Kstar.mul_mem (Kstar.inv_mem hy) (SetLike.mem_coe.mp hmem)
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at h
    have h := Subgroup.mem_inf.mpr ⟨hy', hy'Ks⟩
    rwa [htri, Subgroup.mem_bot] at h

end OddOrder.BG.Ch4.S14


