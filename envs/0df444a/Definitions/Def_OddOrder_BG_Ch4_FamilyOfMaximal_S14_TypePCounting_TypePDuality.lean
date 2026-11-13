-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_TypePDuality
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_TypePDuality
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T09:28:25.864716+00:00
-- url     : https://prove2.me/theorems/ce92238b-7fdd-4476-b25f-984882eb2b9b
-- title:
--   BG §14: type-$\mathcal{P}$ duality (continuation)
-- statement:
--   A continuation of the type-$\mathcal{P}$ duality part of the §14 counting development of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*. It includes a reusable dummy $\sigma$-decomposition datum and the counting fact that two subsets of a finite group each covering more than half of it must intersect.
--
--   Main declarations: `dummySigmaDecomposition`; `ncard_inter_nonempty_of_two_mul_gt` (Two subsets of a finite group, each covering more than half of it, must intersect).
--
--   The bundle also proves 27 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/TypePDuality.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/TypePDuality.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_CentralizerSup

namespace OddOrder.BG.Ch4.S14

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch3.S13

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **`y ∈ C_G(K)` from `y ∈ Z = K ⊔ K*` with `Z` cyclic** (the `cKZ` step of κ→Ẑ): since the
join `K ⊔ K*` is cyclic — hence abelian — every element of it centralizes `K`.  Combined with
`y ∈ M_σ`, this places the σ-part `y` in `K* = M_σ ⊓ C_G(K)`. -/
theorem mem_centralizer_of_mem_sup_isCyclic {K Kstar : Subgroup G}
    (hcyc : IsCyclic ↥(K ⊔ Kstar)) {y : G} (hyZ : y ∈ K ⊔ Kstar) :
    y ∈ Subgroup.centralizer (K : Set G) := by
  have := hcyc
  let : CommGroup ↥(K ⊔ Kstar) := IsCyclic.commGroup
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hkZ : k ∈ K ⊔ Kstar := Subgroup.mem_sup_left (SetLike.mem_coe.mp hk)
  have hcomm : (⟨k, hkZ⟩ : ↥(K ⊔ Kstar)) * ⟨y, hyZ⟩ = ⟨y, hyZ⟩ * ⟨k, hkZ⟩ := mul_comm _ _
  have h := congrArg (Subgroup.subtype (K ⊔ Kstar)) hcomm
  simpa using h

/-- **BG Theorem 14.7, `|Ẑ| = (k − 1)(k* − 1)`** (mmd L4051): the TI-set `Ẑ = Z − (K ∪ K*)` has
`(|K| − 1)(|K*| − 1)` elements.  `|Z| = |K|·|K*|` (`card_kappaHall_sup_Kstar`), `K ∩ K* = 1`
(`kappaHall_inf_Kstar_eq_bot`) so `|K ∪ K*| = |K| + |K*| − 1`, and `|Ẑ| = |Z| − |K ∪ K*|`.
This is the cardinality the density bound `|𝒞_G(Ẑ)| = (1 − 1/k)(1 − 1/k*)|G| > ½|G|` rests on. -/
theorem zTilde_ncard_eq [Finite G] {M K Kstar : Subgroup G} (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    (zTilde K Kstar).ncard = (Nat.card ↥K - 1) * (Nat.card ↥Kstar - 1) := by
  classical
  have hsub : ((K : Set G) ∪ (Kstar : Set G)) ⊆ ((K ⊔ Kstar : Subgroup G) : Set G) :=
    Set.union_subset (SetLike.coe_subset_coe.mpr le_sup_left)
      (SetLike.coe_subset_coe.mpr le_sup_right)
  have hZc : ((K ⊔ Kstar : Subgroup G) : Set G).ncard = Nat.card ↥K * Nat.card ↥Kstar := by
    rw [← Nat.card_coe_set_eq]
    exact (Nat.card_congr (Equiv.refl _)).symm.trans (card_kappaHall_sup_Kstar hKM hK hKstar)
  have hKc : (K : Set G).ncard = Nat.card ↥K := by
    rw [← Nat.card_coe_set_eq]; exact (Nat.card_congr (Equiv.refl _)).symm
  have hKstarc : (Kstar : Set G).ncard = Nat.card ↥Kstar := by
    rw [← Nat.card_coe_set_eq]; exact (Nat.card_congr (Equiv.refl _)).symm
  have hinter : (K : Set G) ∩ (Kstar : Set G) = {1} := by
    rw [← Subgroup.coe_inf, kappaHall_inf_Kstar_eq_bot hKM hK hKstar, Subgroup.coe_bot]
  have hunion : ((K : Set G) ∪ (Kstar : Set G)).ncard = Nat.card ↥K + Nat.card ↥Kstar - 1 := by
    have h := Set.ncard_union_add_ncard_inter (K : Set G) (Kstar : Set G)
    rw [hinter, Set.ncard_singleton, hKc, hKstarc] at h
    omega
  rw [zTilde, Set.ncard_sdiff hsub, hZc, hunion]
  exact nat_mul_sub_kl_identity Nat.card_pos Nat.card_pos

/-- Pure `ℕ` arithmetic for the `8/15 > 1/2` density step: for coprime odd `k, l > 1` one has
`k·l < 2(k−1)(l−1)`.  Equivalently `(k−2)(l−2) > 2`; the only odd pair `≥ 3` failing this is
`k = l = 3`, excluded by coprimality (`gcd 3 3 = 3 ≠ 1`).  Hence one factor is `≥ 5`. -/
private theorem card_kkstar_lt {k l : ℕ} (hk : Odd k) (hl : Odd l)
    (hk1 : k ≠ 1) (hl1 : l ≠ 1) (hcop : Nat.Coprime k l) :
    k * l < 2 * ((k - 1) * (l - 1)) := by
  obtain ⟨a, rfl⟩ := hk
  obtain ⟨b, rfl⟩ := hl
  have ha : 1 ≤ a := by omega
  have hb : 1 ≤ b := by omega
  have hnotboth : ¬ (a = 1 ∧ b = 1) := by
    rintro ⟨rfl, rfl⟩; exact absurd hcop (by decide)
  have hab : 2 ≤ a ∨ 2 ≤ b := by omega
  have key : 2 * a + 2 * b + 1 < 4 * (a * b) := by
    rcases hab with ha2 | hb2
    · have h1 : 2 * b ≤ a * b := Nat.mul_le_mul ha2 (le_refl b)
      have h2 : a ≤ a * b := by simpa using Nat.mul_le_mul (le_refl a) hb
      omega
    · have h1 : 2 * a ≤ a * b := by simpa [mul_comm] using Nat.mul_le_mul (le_refl a) hb2
      have h2 : b ≤ a * b := by simpa [mul_comm] using Nat.mul_le_mul (le_refl b) ha
      omega
  have e1 : 2 * a + 1 - 1 = 2 * a := by omega
  have e2 : 2 * b + 1 - 1 = 2 * b := by omega
  rw [e1, e2]
  nlinarith [key]

/-- **BG Theorem 14.7, the density bound `|𝒞_G(Ẑ)| > ½|G|`** (mmd L3975/L4051): the conjugacy
saturation of the TI-set `Ẑ` covers more than half of `G`.  This is the counting heart of the
`∃! M*` covering — a third nonconjugate type-`P` maximal subgroup would force a *second* `> ½|G|`
saturation piece disjoint from this one, which is impossible.

Proof chain: `Ẑ` is a TI-subset of `Z = K ⊔ K*` (`typeP_zTilde_isTI`) normalised by `Z`
(`typeP_family_Z_normalizes_T`, transported along `Ẑ = T`), so `|𝒞_G(Ẑ)| = |Ẑ|·[G : Z]`; with
`|Ẑ| = (k−1)(k*−1)` (`zTilde_ncard_eq`) and `|G| = |Z|·[G : Z] = k·k*·[G : Z]`
(`card_kappaHall_sup_Kstar`), the bound reduces to the pure inequality `k·k* < 2(k−1)(k*−1)`
(`card_kkstar_lt`) for the coprime (`coprime_card_kappaHall_Kstar`) odd `k = |K|`, `k* = |K*| > 1`
(`K* ≠ 1` is `typeP_structure`'s second conjunct). -/
theorem typeP_zTilde_conjClass_gt_half [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar) :
    Nat.card G < 2 * (conjClassSet (zTilde K Kstar)).ncard := by
  classical
  -- `Ẑ = T` (the family TI-set), via the `Z ⊓ N_σ` collapse.
  have hzeq : zTilde K Kstar = ((K ⊔ Kstar : Subgroup G) : Set G) \
      ⋃ N ∈ ZFamilyFinset M K,
        (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) := by
    simp only [zTilde]
    rw [family_inf_msigma_union_eq hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart]
  -- `Z` normalises `Ẑ` (transported from the family form).
  have hstab : ∀ l ∈ K ⊔ Kstar, MulAut.conj l • (zTilde K Kstar) = zTilde K Kstar := by
    intro l hl
    rw [hzeq]; exact typeP_family_Z_normalizes_T hG hM hP hKM hK hKstar hU l hl
  -- Saturation count `|𝒞_G(Ẑ)| = |Ẑ|·[G : Z]`.
  have hcount : (conjClassSet (zTilde K Kstar)).ncard
      = (zTilde K Kstar).ncard * (K ⊔ Kstar).index :=
    ncard_conjClassSet_of_isTISubset
      (typeP_zTilde_isTI hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart) hstab
  -- `|Ẑ| = (k − 1)(k* − 1)`.
  have hZc : (zTilde K Kstar).ncard = (Nat.card ↥K - 1) * (Nat.card ↥Kstar - 1) :=
    zTilde_ncard_eq hKM hK hKstar
  -- `|G| = |Z|·[G : Z] = k·k*·[G : Z]`.
  have hG_eq : Nat.card G = Nat.card ↥K * Nat.card ↥Kstar * (K ⊔ Kstar).index := by
    rw [← card_kappaHall_sup_Kstar hKM hK hKstar]
    exact (Subgroup.card_mul_index (K ⊔ Kstar)).symm
  have hidx_pos : 0 < (K ⊔ Kstar).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  -- `k, k*` are odd (divisors of `|G|`).
  have hKodd : Odd (Nat.card ↥K) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card K)
  have hKstarodd : Odd (Nat.card ↥Kstar) :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card Kstar)
  -- `k > 1`: a prime `p ∈ κ(M)` divides `|K|` (`card_kappaHall_ne_one`).
  have hKne1 : Nat.card ↥K ≠ 1 := card_kappaHall_ne_one hP hKM hK
  -- `k* > 1`: `K* ≠ ⊥` (Proposition 14.2's second conjunct).
  have hKstarne1 : Nat.card ↥Kstar ≠ 1 :=
    fun h => (typeP_structure hG hM hP hKM hK hKstar hU).2.1 (Subgroup.eq_bot_of_card_eq _ h)
  have hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥Kstar) :=
    coprime_card_kappaHall_Kstar hKM hK hKstar
  have harith : Nat.card ↥K * Nat.card ↥Kstar
      < 2 * ((Nat.card ↥K - 1) * (Nat.card ↥Kstar - 1)) :=
    card_kkstar_lt hKodd hKstarodd hKne1 hKstarne1 hcop
  rw [hcount, hZc, hG_eq]
  calc Nat.card ↥K * Nat.card ↥Kstar * (K ⊔ Kstar).index
      < 2 * ((Nat.card ↥K - 1) * (Nat.card ↥Kstar - 1)) * (K ⊔ Kstar).index :=
        mul_lt_mul_of_pos_right harith hidx_pos
    _ = 2 * ((Nat.card ↥K - 1) * (Nat.card ↥Kstar - 1) * (K ⊔ Kstar).index) :=
        mul_assoc _ _ _

open Classical in
/-- A reusable dummy `SigmaDecompositionData`: `length x = 1` iff `x ≠ 1` and `x` has a maximal
`σ`-subgroup.  The structure axiom `length_one_iff` pins this predicate across *all* carriers, and
the family/density machinery (`family_card_eq_two`, `exists_partner`, …) consumes `D` only through
`D.length x = 1`; so this dummy suffices — no genuine `σ`-decomposition theory is needed. -/
noncomputable def dummySigmaDecomposition (G : Type*) [Group G] : SigmaDecompositionData G where
  length := fun y => if y ≠ 1 ∧ (maximalSigmaSubgroupsOfElement y).Nonempty then 1 else 0
  length_one_iff := by
    intro y
    by_cases h : y ≠ 1 ∧ (maximalSigmaSubgroupsOfElement y).Nonempty <;> simp [h]

omit [Group G] in
/-- Two subsets of a finite group, each covering more than half of it, must intersect. -/
theorem ncard_inter_nonempty_of_two_mul_gt [Finite G] {A B : Set G}
    (hA : Nat.card G < 2 * A.ncard) (hB : Nat.card G < 2 * B.ncard) :
    (A ∩ B).Nonempty := by
  classical
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have hunion := Set.ncard_union_add_ncard_inter A B
  rw [hempty, Set.ncard_empty] at hunion
  have hle : (A ∪ B).ncard ≤ Nat.card G := by
    rw [← Set.ncard_univ G]
    exact Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
  omega

/-- **BG Theorem 14.7, the density bound holds for every type-`P` maximal subgroup** (mmd L4053,
"we also have `|𝒞_G(S)| > ½|G|`"): for `H ∈ 𝓜_𝓟` there is a Hall `κ(H)`-subgroup `L` with
`L* = C_{Hσ}(L)` and `|𝒞_G(Ẑ_H)| > ½|G|`.  The same density count (`typeP_zTilde_conjClass_gt_half`)
run for `H`; the partner data for `H` is produced internally (`exists_partner`, fed the dummy
`σ`-decomposition).  Reused in the covering step of `typeP_duality`. -/
theorem exists_zTilde_conjClass_gt_half_of_isTypeP [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {H : Subgroup G}
    (hHmax : H ∈ maximalSubgroups G) (hHP : IsTypeP H) :
    ∃ L Lstar Uu : Subgroup G, L ≤ H ∧ Ch03.IsHallSubgroup (kappa H) (L.subgroupOf H) ∧
      Lstar = OddOrder.BG.Ch3.S10.Msigma H ⊓ Subgroup.centralizer (L : Set G) ∧
      Ch03.IsHallSubgroup ((kappa H ∪ OddOrder.BG.Ch3.S10.sigma H)ᶜ) (Uu.subgroupOf H) ∧
      Nat.card G < 2 * (conjClassSet (zTilde L Lstar)).ncard := by
  classical
  have : Group.IsSolvable ↥H := hG.isSolvable_of_mem_maximalSubgroups hHmax
  -- Hall `κ(H)`-subgroup `L` of `H`.
  obtain ⟨L', hL'⟩ := Ch03.hall_E_exists (G := ↥H) (kappa H)
  have hLeq : (L'.map H.subtype).subgroupOf H = L' :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective L'
  have hL : Ch03.IsHallSubgroup (kappa H) ((L'.map H.subtype).subgroupOf H) := by
    rw [hLeq]; exact hL'
  have hLH : L'.map H.subtype ≤ H := Subgroup.map_subtype_le L'
  set L := L'.map H.subtype with hLdef
  set Lstar := OddOrder.BG.Ch3.S10.Msigma H ⊓ Subgroup.centralizer (L : Set G) with hLstar
  -- Hall `(κ(H) ∪ σ(H))'`-subgroup `U` of `H`.
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥H) ((kappa H ∪ OddOrder.BG.Ch3.S10.sigma H)ᶜ)
  have hUeq : (U'.map H.subtype).subgroupOf H = U' :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((kappa H ∪ OddOrder.BG.Ch3.S10.sigma H)ᶜ)
      ((U'.map H.subtype).subgroupOf H) := by rw [hUeq]; exact hU'
  -- Partner data for `H`, then the density bound.
  obtain ⟨Hstar, hHstarne, hHstarmem, hpart⟩ :=
    exists_partner hG (dummySigmaDecomposition G) hHmax hHP hLH hL hLstar hU
  exact ⟨L, Lstar, U'.map H.subtype, hLH, hL, hLstar, hU,
    typeP_zTilde_conjClass_gt_half hG hHmax hHP hLH hL hLstar hU hHstarmem hHstarne hpart⟩

/-- Dual of `isPiElementCompl_mem_left_of_commute`: a `π`-element of `Z = A ⊔ B` (with `A` a
`πᶜ`-group, `B` a `π`-group commuting with `A`) lies in `B`.  (Swap the roles of `A`, `B` and
`π`, `πᶜ`.) -/
theorem isPiElement_mem_right_of_commute [Finite G] {A B Z : Subgroup G} {π : Set ℕ}
    (hswap : Z = A ⊔ B) (hcent : B ≤ Subgroup.centralizer (A : Set G))
    (hAπc : Subgroup.IsPiSubgroup πᶜ A) (hBπ : Subgroup.IsPiSubgroup π B)
    {b : G} (hbZ : b ∈ Z) (hbπ : IsPiElement π b) : b ∈ B := by
  have hAcent : A ≤ Subgroup.centralizer (B : Set G) := fun a ha => by
    rw [Subgroup.mem_centralizer_iff]
    exact fun c hc => (Subgroup.mem_centralizer_iff.mp (hcent hc) a ha).symm
  exact isPiElementCompl_mem_left_of_commute (A := B) (B := A) (π := πᶜ)
    (by rw [hswap, sup_comm]) hAcent (by rwa [compl_compl]) hAπc hbZ (by rwa [compl_compl])

/-- **BG Theorem 14.7 covering, the `σ`-part matching** (mmd L4053): if `t` lies in both
`Ẑ_M = (K ⊔ K*) − (K ∪ K*)` (with `K` a `σ(M)′`-group, `K*` a `σ(M)`-group commuting with `K`) and
in `L ⊔ L*` but not in `L` (with `L` a `σ(H)′`-group, `L*` a `σ(H)`-group commuting with `L`), then
`L*` meets one of `K`, `K*` nontrivially.  Proof: the `σ(H)`-part `w` of `t` is a nontrivial
element of `L*` (else `t = (σ(H)′-part) ∈ L`), and `w ∈ ⟨t⟩ ⊆ K ⊔ K*`; its `σ(M)`- and
`σ(M)′`-parts are powers of `w` (so in `L*`) lying in `K*` resp. `K`, and at least one is
nontrivial.  This realizes BG's "`T ∩ S ≠ ∅ ⟹ L* ∩ Kᵢ* ≠ 1`". -/
theorem exists_inf_ne_bot_of_mem_zTilde_inter [Finite G] {K Kstar L Lstar : Subgroup G}
    {πM πH : Set ℕ}
    (hKπ : Subgroup.IsPiSubgroup πMᶜ K) (hKstarπ : Subgroup.IsPiSubgroup πM Kstar)
    (hKcent : Kstar ≤ Subgroup.centralizer (K : Set G))
    (hLπ : Subgroup.IsPiSubgroup πHᶜ L) (hLstarπ : Subgroup.IsPiSubgroup πH Lstar)
    (hLcent : Lstar ≤ Subgroup.centralizer (L : Set G))
    {t : G} (htZ : t ∈ K ⊔ Kstar) (htnL : t ∉ L) (htZ' : t ∈ L ⊔ Lstar) :
    Lstar ⊓ K ≠ ⊥ ∨ Lstar ⊓ Kstar ≠ ⊥ := by
  classical
  -- `σ(H)`-decompose `t = w * v`; `v ∈ L`, `w ∈ L*`, and `w ≠ 1`.
  obtain ⟨w, v, hwv, -, hwπ, hvπ, hwz, hvz⟩ := exists_isPiElement_mul πH t
  have hvL : v ∈ L := isPiElementCompl_mem_left_of_commute rfl hLcent hLπ hLstarπ
    ((Subgroup.zpowers_le.mpr htZ') hvz) hvπ
  have hwLstar : w ∈ Lstar := isPiElement_mem_right_of_commute rfl hLcent hLπ hLstarπ
    ((Subgroup.zpowers_le.mpr htZ') hwz) hwπ
  have hw1 : w ≠ 1 := fun hw => htnL (by rw [show t = v by rw [← hwv, hw, one_mul]]; exact hvL)
  -- `σ(M)`-decompose `w = a * b`; `a ∈ K*`, `b ∈ K`, both powers of `w` (so in `L*`).
  have hwZ : w ∈ K ⊔ Kstar := (Subgroup.zpowers_le.mpr htZ) hwz
  obtain ⟨a, b, hab, -, haπ, hbπ, haz, hbz⟩ := exists_isPiElement_mul πM w
  have haKstar : a ∈ Kstar := isPiElement_mem_right_of_commute rfl hKcent hKπ hKstarπ
    ((Subgroup.zpowers_le.mpr hwZ) haz) haπ
  have hbK : b ∈ K := isPiElementCompl_mem_left_of_commute rfl hKcent hKπ hKstarπ
    ((Subgroup.zpowers_le.mpr hwZ) hbz) hbπ
  have haLstar : a ∈ Lstar := (Subgroup.zpowers_le.mpr hwLstar) haz
  have hbLstar : b ∈ Lstar := (Subgroup.zpowers_le.mpr hwLstar) hbz
  -- `w = a * b ≠ 1`, so one factor is nontrivial.
  have hor : a ≠ 1 ∨ b ≠ 1 := by
    by_contra h; push Not at h
    exact hw1 (by rw [← hab, h.1, h.2, mul_one])
  rcases hor with ha1 | hb1
  · exact Or.inr fun hbot => ha1 (by
      have : a ∈ Lstar ⊓ Kstar := Subgroup.mem_inf.mpr ⟨haLstar, haKstar⟩
      rwa [hbot, Subgroup.mem_bot] at this)
  · exact Or.inl fun hbot => hb1 (by
      have : b ∈ Lstar ⊓ K := Subgroup.mem_inf.mpr ⟨hbLstar, hbK⟩
      rwa [hbot, Subgroup.mem_bot] at this)

/-- **BG Proposition 14.2(f)** (mmd L3838): every `σ(M)`-subgroup `Y < ⊤` of `G` meeting `K*`
nontrivially lies in `M_σ`.  Not among `typeP_structure`'s packaged conjuncts; derived here from
Corollary 12.16 (`Y` is `G`-conjugate into `M_σ`) and Proposition 14.2(d) (the conjugator lies in
`M`, since it fixes a nontrivial element of `K*`).  A step of the partner-symmetry argument of
Theorem 14.7. -/
theorem typeP_sigma_subgroup_le_Msigma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {Y : Subgroup G} (hYlt : Y < ⊤)
    (hYpi : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma M) Y)
    (hYmeet : Y ⊓ Kstar ≠ ⊥) :
    Y ≤ OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  have hYne : Y ≠ ⊥ := fun h => hYmeet (by rw [h, bot_inf_eq])
  -- Corollary 12.16: `Y` is `G`-conjugate into `M_σ`.
  obtain ⟨g, hg⟩ := sigma_subgroup_conj_into_Msigma_general hG hM hYne hYlt hYpi
    (fun hN hnc => sigma_disjoint_of_nonconjugate hG hM hN hnc)
  -- A nontrivial common element `y ∈ Y ⊓ K*`.
  obtain ⟨ysub, hysub1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hYmeet
  have hy1 : (ysub : G) ≠ 1 := fun h => hysub1 (OneMemClass.coe_eq_one.mp h)
  have hyY : (ysub : G) ∈ Y := (Subgroup.mem_inf.mp ysub.2).1
  have hyKstar : (ysub : G) ∈ Kstar := (Subgroup.mem_inf.mp ysub.2).2
  -- `conj g • y ∈ M_σ ⊆ M`, so `y ∈ conj g⁻¹ • M`.
  have hyMconj : (ysub : G) ∈ MulAut.conj g⁻¹ • M := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      show (MulAut.conj g⁻¹)⁻¹ • (ysub : G) = MulAut.conj g • (ysub : G) by
        rw [← map_inv MulAut.conj g⁻¹, inv_inv]]
    exact OddOrder.BG.Ch3.S10.Msigma_le M
      (hg (Subgroup.smul_mem_pointwise_smul (ysub : G) (MulAut.conj g) Y hyY))
  -- Proposition 14.2(d): `K* ⊓ Mᵍ⁻¹ ≠ 1` forces `g⁻¹ ∈ M`.
  have hginvM : g⁻¹ ∈ M := by
    by_contra hg'
    exact hy1 (Subgroup.mem_bot.mp
      (((typeP_structure hG hM hP hKM hK hKstar hU).2.2.2.1 g⁻¹ hg') ▸
        Subgroup.mem_inf.mpr ⟨hyKstar, hyMconj⟩))
  have hgM : g ∈ M := inv_inv g ▸ M.inv_mem hginvM
  -- `conj g` fixes `M` and `M_σ`; descend `conj g • Y ≤ M_σ` to `Y ≤ M_σ`.
  have hconjM : MulAut.conj g • M = M :=
    conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hgM)
  have hgMsigma :
      MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M = OddOrder.BG.Ch3.S10.Msigma M := by
    rw [← Msigma_conj_smul, hconjM]
  exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mp (hgMsigma ▸ hg)

/-- **BG Theorem 14.7(2)(3), partner symmetry** (mmd L4061): the partner `M*` carries the dual
Hall structure — `K*` is a Hall `κ(M*)`-subgroup of `M*` and `K = C_{M*_σ}(K*)`.  So the roles of
`(M, K, K*)` and `(M*, K*, K)` are symmetric.

This is short here (not BG's end-of-proof `Hall σ(M)`-subgroup argument) because the family
machinery already produced `M*`'s Hall `κ(M*)`-subgroup `KN` with `Z = KN ⊔ C_{M*_σ}(KN)`
(`typeP_family_member_data`) and `Z ⊓ M*_σ = K` (`partner_canonical_eq`); two applications of
`isPiSubgroup_le_left_of_commute` (with `π = σ(M*)`: `K` is the `σ(M*)`-part of `Z`, while `KN` and
`K*` are both the `σ(M*)′`-part) give `KN = K*`. -/
theorem typeP_partner_structure [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar) :
    Mstar ∈ maximalSubgroups G ∧ IsTypeP Mstar ∧ Kstar ≤ Mstar ∧
      Ch03.IsHallSubgroup (kappa Mstar) (Kstar.subgroupOf Mstar) ∧
      K = OddOrder.BG.Ch3.S10.Msigma Mstar ⊓ Subgroup.centralizer (Kstar : Set G) := by
  classical
  obtain ⟨hMstarmax, hMstarP, hZMstar, KN, hKNMstar, hKN_hall, hsw, hcanon, -⟩ :=
    typeP_family_member_data hG hM hP hKM hK hKstar hU hMstarmem
  -- The partner's canonical factor `C_{M*_σ}(KN) = K`.
  have hcanonK : OddOrder.BG.Ch3.S10.Msigma Mstar ⊓ Subgroup.centralizer (KN : Set G) = K := by
    rw [hcanon]; exact partner_canonical_eq hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  have hnc : ¬ IsConjugateSubgroup M Mstar :=
    typeP_family_pairwise_nonconjugate hG hM hP hKM hK hKstar hU (Or.inl rfl) hMstarmem
      (Ne.symm hMstarne)
  have hσdisj : Disjoint (OddOrder.BG.Ch3.S10.sigma M) (OddOrder.BG.Ch3.S10.sigma Mstar) :=
    sigma_disjoint_of_nonconjugate hG hM hMstarmax hnc
  -- `π`-subgroup data for `π = σ(M*)`: `K` is `σ(M*)`, `K*`/`KN` are `σ(M*)′`.
  have hK_piMstar : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma Mstar) K := fun q hq =>
    kappaHall_primes_subset_sigma_partner hG hM hP hKM hK hKstar hU hpart
      (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq)
  have hKstar_piMstarc :
      Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ Kstar := fun q hq =>
    Set.disjoint_left.mp hσdisj (Kstar_isPiSubgroup_sigma hKstar q hq)
  have hKN_piMstarc :
      Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ KN := fun q hq =>
    kappa_subset_sigmaCompl (hKN_hall.1 q
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKNMstar).toEquiv]; exact hq))
  -- `K` centralizes both `K*` and `KN`.
  have hKcKstar : K ≤ Subgroup.centralizer (Kstar : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hKstar ▸ hs)).2 k hk).symm
  have hKcKN : K ≤ Subgroup.centralizer (KN : Set G) := hcanonK ▸ inf_le_right
  -- `KN = K*`: each lies in the other's `σ(M*)′`-part of `Z`.
  have hKNle : KN ≤ Kstar := isPiSubgroup_le_left_of_commute (π := OddOrder.BG.Ch3.S10.sigma Mstar)
    (by rw [sup_comm]) hKcKstar hKstar_piMstarc hK_piMstar (by rw [hsw]; exact le_sup_left)
    hKN_piMstarc
  have hKstarle : Kstar ≤ KN := isPiSubgroup_le_left_of_commute
    (π := OddOrder.BG.Ch3.S10.sigma Mstar) (hsw.trans (by rw [hcanonK])) hKcKN hKN_piMstarc
    hK_piMstar le_sup_right hKstar_piMstarc
  have hKNeq : KN = Kstar := le_antisymm hKNle hKstarle
  exact ⟨hMstarmax, hMstarP, le_sup_right.trans hZMstar, hKNeq ▸ hKN_hall,
    (hKNeq ▸ hcanonK).symm⟩

/-- **BG Theorem 14.7(1)** (mmd L3964): `ℳ(C_G(Y)) = {M*}` for every `Y ∈ ℰ¹(K)`.  This is
Proposition 14.2(c) applied to the *partner* `M*`: by the partner symmetry
(`typeP_partner_structure`) `K*` is a Hall `κ(M*)`-subgroup of `M*` and `K = C_{M*_σ}(K*)`, i.e.
`K` plays the `K*`-role for `M*`, so `14.2(c)` for `M*` yields the unique-maximal conclusion for
lines of `K`.  The `K`-side companion of Proposition 14.2(c); the covering step of Theorem 14.7
uses it to conjugate a type-`P` subgroup to `M*`. -/
theorem typeP_partner_centralizer_singleton [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar)
    {p : ℕ} [Fact p.Prime] {Y : Subgroup G} (hY : Y ∈ elemAbelianOfRank G p 1) (hYK : Y ≤ K) :
    maximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) = {Mstar} := by
  classical
  obtain ⟨hMstarmax, hMstarP, hKstarMstar, hKstar_hall, hK_eq⟩ :=
    typeP_partner_structure hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  have : Group.IsSolvable ↥Mstar := hG.isSolvable_of_mem_maximalSubgroups hMstarmax
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥Mstar)
    ((kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ)
  have hUeq : (U'.map Mstar.subtype).subgroupOf Mstar = U' :=
    Subgroup.comap_map_eq_self_of_injective Mstar.subtype_injective U'
  have hU_Mstar : Ch03.IsHallSubgroup ((kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ)
      ((U'.map Mstar.subtype).subgroupOf Mstar) := by rw [hUeq]; exact hU'
  exact (typeP_structure hG hMstarmax hMstarP hKstarMstar hKstar_hall hK_eq hU_Mstar).2.2.2.2.2.1
    p Fact.out Y hY hYK

/-- **BG Theorem 14.7(7), the covering** (mmd L4053): every type-`P` maximal subgroup `H` is
conjugate to `M` or to its partner `M*`.

Proof: both `Ẑ_M` and `Ẑ_H` have conjugacy saturation `> ½|G|`
(`typeP_zTilde_conjClass_gt_half`, `exists_zTilde_conjClass_gt_half_of_isTypeP`), so the
saturations meet (`ncard_inter_nonempty_of_two_mul_gt`); a common element gives `t ∈ Ẑ_M`,
`s ∈ Ẑ_H` with `t = c • s`.  The `σ`-part matching (`exists_inf_ne_bot_of_mem_zTilde_inter`) then
yields a nontrivial `L*ᶜ ⊓ K` or `L*ᶜ ⊓ K*` (here `L*ᶜ = c • L*`); a line `Y` in it satisfies
`ℳ(C_G(Y)) = {M}` (Proposition 14.2(c), `K*`-case) or `{M*}` (`typeP_partner_centralizer_singleton`,
`K`-case), while `c⁻¹ • Y ∈ ℰ¹(L*)` gives `ℳ(C_G(c⁻¹•Y)) = {H}` (Proposition 14.2(c) for `H`).
Transporting by `c` shows `c • H` is a maximal subgroup over `C_G(Y)`, so `c • H = M` or `M*`. -/
theorem typeP_covering [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar)
    {H : Subgroup G} (hHmax : H ∈ maximalSubgroups G) (hHP : IsTypeP H) :
    IsConjugateSubgroup H M ∨ IsConjugateSubgroup H Mstar := by
  classical
  have hMbound := typeP_zTilde_conjClass_gt_half hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  obtain ⟨L, Lstar, Uu, hLH, hL_hall, hLstar_eq, hU_H, hHbound⟩ :=
    exists_zTilde_conjClass_gt_half_of_isTypeP hG hHmax hHP
  obtain ⟨u, huM, huH⟩ := ncard_inter_nonempty_of_two_mul_gt hMbound hHbound
  obtain ⟨t, htM, a, hat⟩ := huM
  obtain ⟨s, hsH, b, hbs⟩ := huH
  simp only [zTilde, Set.mem_sdiff, Set.mem_union, SetLike.mem_coe, not_or] at htM hsH
  obtain ⟨htZ, htK, htKstar⟩ := htM
  obtain ⟨hsZ, hsL, hsLstar⟩ := hsH
  set c := a⁻¹ * b with hc_def
  -- `t = c • s`.
  have htcs : MulAut.conj c • s = t := by
    have key : b * s * b⁻¹ = a * t * a⁻¹ := hbs.trans hat.symm
    rw [MulAut.smul_def, MulAut.conj_apply, hc_def, mul_inv_rev, inv_inv]
    calc a⁻¹ * b * s * (b⁻¹ * a)
        = a⁻¹ * (b * s * b⁻¹) * a := by group
      _ = a⁻¹ * (a * t * a⁻¹) * a := by rw [key]
      _ = t := by group
  have hcancel1 : ∀ X : Subgroup G, MulAut.conj c⁻¹ • (MulAut.conj c • X) = X := fun X => by
    rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hcancel2 : ∀ X : Subgroup G, MulAut.conj c • (MulAut.conj c⁻¹ • X) = X := fun X => by
    rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  -- Matching inputs.
  have hcardL : Nat.card ↥(MulAut.conj c • L) = Nat.card ↥L :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have hcardLstar : Nat.card ↥(MulAut.conj c • Lstar) = Nat.card ↥Lstar :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have hKπ : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma M)ᶜ K :=
    kappaHall_isPiSubgroup_sigmaCompl hKM hK
  have hKstarπ : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma M) Kstar :=
    Kstar_isPiSubgroup_sigma hKstar
  have hKcent : Kstar ≤ Subgroup.centralizer (K : Set G) := hKstar ▸ inf_le_right
  have hcLπ : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma H)ᶜ (MulAut.conj c • L) := by
    intro q hq
    rw [hcardL] at hq
    exact kappa_subset_sigmaCompl
      (hL_hall.1 q (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLH).toEquiv]))
  have hcLstarπ :
      Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma H) (MulAut.conj c • Lstar) := by
    intro q hq
    rw [hcardLstar] at hq
    exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup H q (Nat.mem_primeFactors.mpr
      ⟨(Nat.mem_primeFactors.mp hq).1, (Nat.dvd_of_mem_primeFactors hq).trans
        (Subgroup.card_dvd_of_le (hLstar_eq ▸ inf_le_left)), Nat.card_pos.ne'⟩)
  have hcLcent :
      MulAut.conj c • Lstar ≤ Subgroup.centralizer ((MulAut.conj c • L : Subgroup G)) := by
    rw [← centralizer_conj_smul]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (hLstar_eq ▸ inf_le_right)
  have htnL : t ∉ MulAut.conj c • L := fun ht =>
    hsL (Subgroup.smul_mem_pointwise_smul_iff.mp (htcs.symm ▸ ht))
  have htZ' : t ∈ (MulAut.conj c • L) ⊔ (MulAut.conj c • Lstar) := by
    rw [← htcs, ← Subgroup.smul_sup]
    exact Subgroup.smul_mem_pointwise_smul s (MulAut.conj c) (L ⊔ Lstar) hsZ
  have hmatch := exists_inf_ne_bot_of_mem_zTilde_inter (πM := OddOrder.BG.Ch3.S10.sigma M)
    (πH := OddOrder.BG.Ch3.S10.sigma H) hKπ hKstarπ hKcent hcLπ hcLstarπ hcLcent htZ htnL htZ'
  -- Common tail: a line `Y ≤ c • L*` with `ℳ(C_G(Y)) = {N}` gives `H ~ N`.
  have hfinish : ∀ {N : Subgroup G} {p : ℕ}, p.Prime → ∀ {Y : Subgroup G},
      Y ∈ elemAbelianOfRank G p 1 → Y ≤ MulAut.conj c • Lstar →
      maximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) = {N} →
      IsConjugateSubgroup H N := by
    intro N p hp Y hYea hYcL hN_sing
    have hcY : MulAut.conj c⁻¹ • Y ≤ Lstar := by
      have h1 := Subgroup.pointwise_smul_le_pointwise_smul_iff
        (a := MulAut.conj c⁻¹) |>.mpr hYcL
      rwa [hcancel1 Lstar] at h1
    have hcYea : MulAut.conj c⁻¹ • Y ∈ elemAbelianOfRank G p 1 :=
      conj_smul_mem_elemAbelianOfRank c⁻¹ hYea
    have hH_sing := (typeP_structure hG hHmax hHP hLH hL_hall hLstar_eq hU_H).2.2.2.2.2.1
      p hp _ hcYea hcY
    have hCle : Subgroup.centralizer ((MulAut.conj c⁻¹ • Y : Subgroup G) : Set G) ≤ H :=
      (mem_maximalSubgroupsContaining.mp (hH_sing.symm ▸ Set.mem_singleton H)).2
    have hCYle : Subgroup.centralizer (Y : Set G) ≤ MulAut.conj c • H := by
      have h1 := Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj c) |>.mpr hCle
      rwa [centralizer_conj_smul, hcancel2 Y] at h1
    have hcHN : MulAut.conj c • H = N := by
      have hmem :
          MulAut.conj c • H ∈ maximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) :=
        mem_maximalSubgroupsContaining.mpr ⟨isCoatom_conj_smul (mem_maximalSubgroups.mp hHmax),
          hCYle⟩
      rw [hN_sing] at hmem; exact Set.eq_of_mem_singleton hmem
    exact ⟨c, hcHN⟩
  -- Extract a line `Y` from the nontrivial intersection and finish.
  rcases hmatch with hne | hne
  · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
      (fun h => hne (Subgroup.eq_bot_of_card_eq _ h))
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' p hpd
    have hyord' : orderOf (y : G) = p :=
      (orderOf_injective _ (MulAut.conj c • Lstar ⊓ K).subtype_injective y).trans hyord
    have hYcard : Nat.card ↥(Subgroup.zpowers (y : G)) = p := by rw [Nat.card_zpowers, hyord']
    have hYea : Subgroup.zpowers (y : G) ∈ elemAbelianOfRank G p 1 :=
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hYcard, by rw [hYcard, pow_one]⟩
    have hYS : Subgroup.zpowers (y : G) ≤ MulAut.conj c • Lstar ⊓ K :=
      Subgroup.zpowers_le.mpr y.2
    exact Or.inr (hfinish hp hYea (hYS.trans inf_le_left)
      (typeP_partner_centralizer_singleton hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
        hYea (hYS.trans inf_le_right)))
  · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
      (fun h => hne (Subgroup.eq_bot_of_card_eq _ h))
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' p hpd
    have hyord' : orderOf (y : G) = p :=
      (orderOf_injective _ (MulAut.conj c • Lstar ⊓ Kstar).subtype_injective y).trans hyord
    have hYcard : Nat.card ↥(Subgroup.zpowers (y : G)) = p := by rw [Nat.card_zpowers, hyord']
    have hYea : Subgroup.zpowers (y : G) ∈ elemAbelianOfRank G p 1 :=
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hYcard, by rw [hYcard, pow_one]⟩
    have hYS : Subgroup.zpowers (y : G) ≤ MulAut.conj c • Lstar ⊓ Kstar :=
      Subgroup.zpowers_le.mpr y.2
    exact Or.inl (hfinish hp hYea (hYS.trans inf_le_left)
      ((typeP_structure hG hM hP hKM hK hKstar hU).2.2.2.2.2.1 p hp _ hYea
        (hYS.trans inf_le_right)))

/-- A Hall `κ(N)`-subgroup `K'` of a maximal `N`, lying inside a nilpotent subgroup `W`, is cyclic.
Since `κ(N) ⊆ τ₁(N) ∪ τ₃(N)`, every prime `p ∣ |K'|` has `pRank N p = 1`, so `pRank K' p ≤ 1`
(`= 0` off `π(K')`); and `K' ≤ W` nilpotent makes `K'` nilpotent.  An odd nilpotent group with
`pRank ≤ 1` everywhere is cyclic (`isCyclic_of_odd_of_isNilpotent_of_forall_pRank_le_one`).  Used to
make both Hall factors of `Z` cyclic in `typeP_Z_isCyclic`. -/
theorem isCyclic_kappaHall_of_le_nilpotent [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {N K' W : Subgroup G} (hK'N : K' ≤ N)
    (hK'_hall : Ch03.IsHallSubgroup (kappa N) (K'.subgroupOf N))
    (hK'W : K' ≤ W) [Group.IsNilpotent ↥W] : IsCyclic ↥K' := by
  have : Group.IsNilpotent ↥K' :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK'W)
  have hodd : Odd (Nat.card ↥K') :=
    hG.odd.of_dvd_nat ((Subgroup.card_dvd_of_le hK'N).trans (Subgroup.card_subgroup_dvd_card N))
  refine isCyclic_of_odd_of_isNilpotent_of_forall_pRank_le_one hodd fun p hp => ?_
  have : Fact p.Prime := ⟨hp⟩
  by_cases hpK : p ∈ (Nat.card ↥K').primeFactors
  · have hpκ : p ∈ kappa N := hK'_hall.1 p (by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK'N).toEquiv])
    have hpτ : pRank ↥N p = 1 := hpκ.2.1.elim tau1_pRank_eq_one tau3_pRank_eq_one
    exact le_trans (pRank_le_of_injective (Subgroup.inclusion_injective hK'N)) (le_of_eq hpτ)
  · by_contra hcon
    exact hpK (OddOrder.BG.Ch2.S09.mem_primeFactors_card_of_pos_pRank (by omega))

/-- For a type-`P₂` maximal subgroup `M`, the `σ`-core `M_σ` is nilpotent.  Since `κ(M)` always
satisfies `κ(M) ⊆ π(M) ∖ σ(M)` and `IsTypeP2` makes this inclusion *proper*, there is a prime
`p ∈ π(M) ∖ (σ(M) ∪ κ(M))`; a maximal-rank elementary abelian `p`-subgroup `A ≤ M` then meets the
hypotheses of Lemma 14.1 (`msigma_structure_of_notMem_sigma_kappa`: `p ∈ π(M)`, `p ∉ σ(M)`,
`p ∉ κ(M)`, `A ∈ ℰ_p^{r_p(M)}`), whose third conclusion is `IsNilpotent M_σ`.  This drives the
cyclicity of `Z = K ⊔ K*` in `typeP_Z_isCyclic` (BG 14.7(d)). -/
theorem msigma_isNilpotent_of_isTypeP2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP2 : IsTypeP2 M) :
    Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
  classical
  -- `κ(M) ⊆ π(M) ∖ σ(M)`: every prime in `κ(M)` divides `|M|` (a rank-one witness `P ≤ M` has
  -- order `p`) and avoids `σ(M)` (`κ ⊆ σ′`).  `IsTypeP2` makes the inclusion proper.
  have hsub : kappa M ⊆ sigmaComplementPrimes M := by
    intro p hp
    obtain ⟨hp_prime, _, P, hPelem, hPM, _⟩ := id hp
    have hPcard : Nat.card ↥P = p := by rw [(mem_elemAbelianOfRank.mp hPelem).2, pow_one]
    refine ⟨Nat.mem_primeFactors.mpr ⟨hp_prime, ?_, Nat.card_pos.ne'⟩, kappa_subset_sigmaCompl hp⟩
    rw [← hPcard]; exact Subgroup.card_dvd_of_le hPM
  obtain ⟨p, hpπ, hpκ⟩ := Set.exists_of_ssubset (ssubset_of_subset_of_ne hsub hP2.2)
  obtain ⟨hpM, hpσ⟩ := hpπ
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpM
  have : Fact p.Prime := ⟨hp⟩
  -- A maximal-rank elementary abelian `p`-subgroup `A = B.map M.subtype ≤ M`.
  obtain ⟨B, hBea, hBlog⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank (G := ↥M) (p := p)
      (n := pRank ↥M p) (one_le_pRank_of_mem_primeFactors hpM) (le_refl _)
  obtain ⟨j, hj⟩ := hBea.isPGroup.exists_card_eq
  have hjeq : j = pRank ↥M p := by
    have hsq := le_antisymm (le_pRank B hBea) hBlog
    rwa [hj, Nat.log_pow hp.one_lt] at hsq
  have hAmem : B.map M.subtype ∈ elemAbelianOfRank G p (pRank ↥M p) := by
    refine ⟨Subgroup.IsElementaryAbelian.map M.subtype_injective hBea, ?_⟩
    rw [Subgroup.card_map_of_injective M.subtype_injective, hj, hjeq]
  exact (msigma_structure_of_notMem_sigma_kappa hG hM hpM hpσ hpκ hAmem
    (Subgroup.map_subtype_le _)).2.2

/-- **BG Theorem 14.7, cyclicity of `Z = K ⊔ K*`** (mmd L4041, conjunct (d)): for a type-`P`
maximal `M` with its nonconjugate partner `M*` (the unique other member of the `Z`-family), the
group `Z = K ⊔ K*` is cyclic.  By `isTypeP2_or_isTypeP2_partner` one of `M`, `M*` is type-`P₂`;
in either case the Hall `κ`-factor of the `P₂` member has prime order (cyclic, `typeP_structure`
clause (g)), while the other factor is a Hall `κ`-subgroup of the partner lying inside the
*nilpotent* `σ`-core of the `P₂` member (`msigma_isNilpotent_of_isTypeP2` +
`isCyclic_kappaHall_of_le_nilpotent`, whose Hall-witness `N` and nilpotent ambient `W` differ).
Two coprime cyclic factors give `Z` cyclic (`isCyclic_kappaHall_sup_Kstar_of_cyclic`). -/
theorem typeP_Z_isCyclic [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U Mstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar) :
    IsCyclic ↥(K ⊔ Kstar) := by
  classical
  -- Partner symmetry: `K*` is Hall `κ(M*)` of `M*`, and `K = C_{M*_σ}(K*)`.
  obtain ⟨hMstarmax, hMstarP, hKstarMstar, hKstar_hall, hKeq⟩ :=
    typeP_partner_structure hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  rcases isTypeP2_or_isTypeP2_partner hG D hM hP hKM hK hKstar hU hpart with hM2 | hMstar2
  · -- `M` is type-`P₂`: `|K|` prime ⟹ `K` cyclic; `K* ≤ M_σ` (nilpotent) ⟹ `K*` cyclic.
    obtain ⟨q, hq, hKq, -⟩ := ((typeP_structure hG hM hP hKM hK hKstar hU).2.2.2.2.1 hM2).2
    have : Fact q.Prime := ⟨hq⟩
    have : IsCyclic ↥K := isCyclic_of_prime_card hKq
    have : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
      msigma_isNilpotent_of_isTypeP2 hG hM hM2
    have : IsCyclic ↥Kstar :=
      isCyclic_kappaHall_of_le_nilpotent hG hKstarMstar hKstar_hall (hKstar.le.trans inf_le_left)
    exact isCyclic_kappaHall_sup_Kstar_of_cyclic hKM hK hKstar
  · -- `M*` is type-`P₂`: `|K*|` prime ⟹ `K*` cyclic; `K ≤ M*_σ` (nilpotent) ⟹ `K` cyclic.
    have : Group.IsSolvable ↥Mstar := hG.isSolvable_of_mem_maximalSubgroups hMstarmax
    obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥Mstar)
      ((kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ)
    have hUeq : (U'.map Mstar.subtype).subgroupOf Mstar = U' :=
      Subgroup.comap_map_eq_self_of_injective Mstar.subtype_injective U'
    have hUstar : Ch03.IsHallSubgroup ((kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ)
        ((U'.map Mstar.subtype).subgroupOf Mstar) := by rw [hUeq]; exact hU'
    obtain ⟨q, hq, hKstarq, -⟩ :=
      ((typeP_structure hG hMstarmax hMstarP hKstarMstar hKstar_hall hKeq hUstar).2.2.2.2.1
        hMstar2).2
    have : Fact q.Prime := ⟨hq⟩
    have : IsCyclic ↥Kstar := isCyclic_of_prime_card hKstarq
    have : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma Mstar) :=
      msigma_isNilpotent_of_isTypeP2 hG hMstarmax hMstar2
    have : IsCyclic ↥K :=
      isCyclic_kappaHall_of_le_nilpotent hG hKM hK (hKeq.le.trans inf_le_left)
    have hcyc : IsCyclic ↥(Kstar ⊔ K) :=
      isCyclic_kappaHall_sup_Kstar_of_cyclic hKstarMstar hKstar_hall hKeq
    rw [sup_comm]; exact hcyc

/-- **BG Theorem 14.7, the unique nonconjugate partner `M*`** (mmd L3962-3971, parts (1)-(7) +
appendix item (4)): for a type-`P` maximal `M`, there is a *unique* maximal subgroup `M*` that is
type-`P`, nonconjugate to `M`, has `K*` as a Hall `κ(M*)`-subgroup with `K = C_{M*_σ}(K*)`, makes
`Z = K ⊔ K*` cyclic with `Ẑ` a TI-set, has one of `M`, `M*` type-`P₂`, and covers every type-`P`
maximal up to conjugacy.

Existence is the canonical partner of `exists_partner`, its data assembled from
`typeP_partner_structure` (maximal/type-P/`K* ≤ M*`/Hall `κ(M*)`/`K = C_{M*_σ}(K*)`),
`typeP_family_pairwise_nonconjugate`, `typeP_Z_isCyclic`, `typeP_zTilde_isTI`,
`isTypeP2_or_isTypeP2_partner`, and `typeP_covering`.

**Uniqueness** turns on the partner-symmetry conjunct `K = C_{M*_σ}(K*)` (BG 14.7(3), appendix (4)):
it makes `K` the `K*`-role subgroup of any competitor `M*'`, so Proposition 14.2(c) for `M*'`
(`typeP_structure`, last conjunct) gives `ℳ(C_G(X)) = {M*'}` for a line `X ∈ ℰ¹(K)`, which also
equals `{M*}` (Theorem 14.7(1), `typeP_partner_centralizer_singleton`), forcing `M*' = M*`.

The partner-symmetry conjunct is *essential*: without it the `∃!` is false, since
`M*' := (M*)ᵈ` for `d ∈ N_{M_σ}(K*) ∖ K*` (which exists when `M_σ` is nilpotent and `K* ⊊ M_σ`,
e.g. `M` type-`P₂`) is nonconjugate to `M*`, still has `K*` Hall `κ(M*')` (as `d` normalizes `K*`),
and satisfies every other conjunct, yet `M*' ≠ M*`. -/
theorem typeP_partner_existsUnique [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    ∃! Mstar : Subgroup G,
      Mstar ∈ maximalSubgroups G ∧ IsTypeP Mstar ∧ ¬ IsConjugateSubgroup M Mstar ∧
      (Kstar ≤ Mstar ∧ Ch03.IsHallSubgroup (kappa Mstar) (Kstar.subgroupOf Mstar) ∧
        K = OddOrder.BG.Ch3.S10.Msigma Mstar ⊓ Subgroup.centralizer (Kstar : Set G)) ∧
      IsCyclic ↥(K ⊔ Kstar) ∧ IsTISubset (zTilde K Kstar) (K ⊔ Kstar) ∧
      (IsTypeP2 M ∨ IsTypeP2 Mstar) ∧
      (∀ H : Subgroup G, H ∈ maximalSubgroups G → IsTypeP H →
        IsConjugateSubgroup H M ∨ IsConjugateSubgroup H Mstar) := by
  classical
  obtain ⟨Mstar, hMstarne, hMstarmem, hpart⟩ := exists_partner hG D hM hP hKM hK hKstar hU
  obtain ⟨hMstarmax, hMstarP, hKstarMstar, hKstar_hall, hKeq⟩ :=
    typeP_partner_structure hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  -- A line `X = ⟨x⟩ ∈ ℰ¹(K)` (needed for both the existence data and the uniqueness pin).
  obtain ⟨p, hpκ⟩ := id hP
  have hp : p.Prime := prime_of_mem_kappa hpκ
  have : Fact p.Prime := ⟨hp⟩
  have hpK : p ∣ Nat.card ↥K := by
    obtain ⟨_, _, P, hPelem, hPM, _⟩ := id hpκ
    have hPcard : Nat.card ↥P = p := by rw [(mem_elemAbelianOfRank.mp hPelem).2, pow_one]
    have hpdvdM : p ∣ Nat.card ↥M := by rw [← hPcard]; exact Subgroup.card_dvd_of_le hPM
    have hsplit : p ∣ Nat.card ↥(K.subgroupOf M) * (K.subgroupOf M).index := by
      rw [Subgroup.card_mul_index]; exact hpdvdM
    have hpKsub : p ∣ Nat.card ↥(K.subgroupOf M) := by
      rcases hp.dvd_mul.mp hsplit with h | h
      · exact h
      · exact absurd hpκ (hK.2 p (Nat.mem_primeFactors.mpr
          ⟨hp, h, Subgroup.index_ne_zero_of_finite⟩))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hpKsub
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hxord : orderOf (x : G) = p := (orderOf_injective K.subtype K.subtype_injective x).trans hx
  have hXcard : Nat.card ↥(Subgroup.zpowers (x : G)) = p := by rw [Nat.card_zpowers, hxord]
  have hXelem : Subgroup.zpowers (x : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXK : Subgroup.zpowers (x : G) ≤ K := Subgroup.zpowers_le.mpr x.2
  -- `ℳ(C_G(X)) = {M*}` (Theorem 14.7(1)).
  have h0 : maximalSubgroupsContaining (Subgroup.centralizer ((Subgroup.zpowers (x : G)) : Set G))
      = {Mstar} :=
    typeP_partner_centralizer_singleton hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
      hXelem hXK
  refine ⟨Mstar, ⟨hMstarmax, hMstarP,
    typeP_family_pairwise_nonconjugate hG hM hP hKM hK hKstar hU (Or.inl rfl) hMstarmem
      (Ne.symm hMstarne),
    ⟨hKstarMstar, hKstar_hall, hKeq⟩,
    typeP_Z_isCyclic hG D hM hP hKM hK hKstar hU hMstarmem hMstarne hpart,
    typeP_zTilde_isTI hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart,
    isTypeP2_or_isTypeP2_partner hG D hM hP hKM hK hKstar hU hpart,
    fun H hHmax hHP =>
      typeP_covering hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart hHmax hHP⟩, ?_⟩
  -- Uniqueness: any competitor `M*'` satisfies `ℳ(C_G(X)) = {M*'}` via the partner symmetry.
  rintro Mstar' ⟨hMstar'max, hMstar'P, -, ⟨hKstarMstar', hKstar'_hall, hKeq'⟩, -, -, -, -⟩
  have : Group.IsSolvable ↥Mstar' := hG.isSolvable_of_mem_maximalSubgroups hMstar'max
  obtain ⟨U'', hU''⟩ := Ch03.hall_E_exists (G := ↥Mstar')
    ((kappa Mstar' ∪ OddOrder.BG.Ch3.S10.sigma Mstar')ᶜ)
  have hU''eq : (U''.map Mstar'.subtype).subgroupOf Mstar' = U'' :=
    Subgroup.comap_map_eq_self_of_injective Mstar'.subtype_injective U''
  have hUstar' : Ch03.IsHallSubgroup ((kappa Mstar' ∪ OddOrder.BG.Ch3.S10.sigma Mstar')ᶜ)
      ((U''.map Mstar'.subtype).subgroupOf Mstar') := by rw [hU''eq]; exact hU''
  have h' : maximalSubgroupsContaining (Subgroup.centralizer ((Subgroup.zpowers (x : G)) : Set G))
      = {Mstar'} :=
    (typeP_structure hG hMstar'max hMstar'P hKstarMstar' hKstar'_hall hKeq' hUstar').2.2.2.2.2.1
      p hp _ hXelem hXK
  have hmem : Mstar' ∈ maximalSubgroupsContaining
      (Subgroup.centralizer ((Subgroup.zpowers (x : G)) : Set G)) := by
    rw [h']; exact Set.mem_singleton _
  rw [h0, Set.mem_singleton_iff] at hmem
  exact hmem

/-- **Derived subgroup via a `σ`-complement** (BG 14.7(h), Proposition 14.2(a) skeleton, mmd L4061):
for any §12 `E`-setup of `M` (so `M = M_σ ⋊ E`), the derived subgroup `M' = [M,M]` equals
`M_σ ⊔ E'` where `E' = [E,E]` is the derived subgroup of the `σ(M)'`-complement.

`⊇` is `Msigma_le_derived` (`M_σ ≤ M'`) plus `commutator_mono` (`E' ≤ M'`).  For `⊆`, an element
`x ∈ M'` decomposes as `x = a·b` (`a ∈ M_σ`, `b ∈ E`) inside `↥M = M_σ ⋊ E`; then `b = a⁻¹x ∈ M'`
(both factors lie in the normal `M'`), so `b ∈ E ⊓ M' ≤ E'` by `inf_derivedInG_le_derivedInG`,
hence `x = a·b ∈ M_σ ⊔ E'`. -/
theorem derivedInG_eq_Msigma_sup_derivedInG_complement [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) :
    derivedInG M = OddOrder.BG.Ch3.S10.Msigma M ⊔ derivedInG E := by
  classical
  have hM := h.mem_maximal
  have hMσM' : OddOrder.BG.Ch3.S10.Msigma M ≤ derivedInG M :=
    OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM
  refine le_antisymm (fun x hx => ?_) (sup_le hMσM' ?_)
  · have hxM : x ∈ M := Subgroup.map_subtype_le _ hx
    have : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    have hsuptop : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M ⊔ E.subgroupOf M = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (OddOrder.BG.Ch3.S10.Msigma_le M) h.E_le,
        h.E_compl_sup, Subgroup.subgroupOf_self]
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp
      (hsuptop ▸ Subgroup.mem_top (⟨x, hxM⟩ : ↥M))
    have hs : (a : G) ∈ OddOrder.BG.Ch3.S10.Msigma M := Subgroup.mem_subgroupOf.mp ha
    have he : (b : G) ∈ E := Subgroup.mem_subgroupOf.mp hb
    have hse : (a : G) * (b : G) = x := by
      have hh := congrArg Subtype.val hab; simpa using hh
    have hbM' : (b : G) ∈ derivedInG M := by
      have hbeq : (b : G) = (a : G)⁻¹ * x := by rw [← hse]; group
      rw [hbeq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hMσM' hs)) hx
    have hbdE : (b : G) ∈ derivedInG E :=
      h.inf_derivedInG_le_derivedInG (Subgroup.mem_inf.mpr ⟨he, hbM'⟩)
    rw [← hse]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right hbdE)
  · rw [show derivedInG E = ⁅E, E⁆ from Subgroup.map_subtype_commutator E,
      show derivedInG M = ⁅M, M⁆ from Subgroup.map_subtype_commutator M]
    exact Subgroup.commutator_mono h.E_le h.E_le

/-- **part (h), degenerate case `K = E`** (BG 14.7(8), mmd L4061 with `U = 1`): if the Hall
`κ(M)`-subgroup `K` equals the whole `σ(M)'`-complement `E` (the case `κ(M) ∩ τ₃(M) ≠ ∅` of
Proposition 14.2(a), or `E₂E₃ = 1`), then `E = K` is cyclic, so `E' = 1` and `M' = M_σ`;
the `M_σ ⋊ E` structure makes `K = E` a complement of `M' = M_σ`. -/
theorem typeP_derivedInG_complement_of_eq_complement [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ K : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hKE : K = E) [IsCyclic ↥K] :
    Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M) := by
  classical
  -- `E = K` is cyclic, hence abelian, so `E' = ⁅E,E⁆ = ⊥`.
  have hEbot : derivedInG E = ⊥ := by
    rw [← hKE, show derivedInG K = ⁅K, K⁆ from Subgroup.map_subtype_commutator K]
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (fun x hx => ?_)
    let : CommGroup ↥K := IsCyclic.commGroup
    refine Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)
    exact congrArg Subtype.val (mul_comm (⟨y, hy⟩ : ↥K) (⟨x, hx⟩ : ↥K))
  -- `M' = M_σ ⊔ E' = M_σ`.
  have hM'eq : derivedInG M = OddOrder.BG.Ch3.S10.Msigma M := by
    rw [derivedInG_eq_Msigma_sup_derivedInG_complement hG h, hEbot, sup_bot_eq]
  rw [hM'eq, hKE]
  exact h.isComplement'_subgroupOf

/-- **BG Theorem 14.7(h) core, `M'` complements `K`** (mmd L4061): for a type-`P` maximal `M`
with Hall `κ(M)`-subgroup `K` *cyclic* (the counting collapse `n = 1` of Theorem 14.7 makes
`Z = K × K*` cyclic, hence `K`), the derived subgroup `M' = [M,M]` is a complement of `K` in `M`.

By Proposition 14.2(a): take a §12 `E`-setup with `K ≤ E`.  If `κ(M) ∩ τ₃(M) ≠ ∅` then `K = E`
(`typeP_derivedInG_complement_of_eq_complement`).  Otherwise `κ(M) ⊆ τ₁(M)`; conjugate so `K = E₁`,
and (when `E₂E₃ = 1`) again `K = E`, or (`E₂E₃ ≠ 1`) `E = K ⋉ U` is Frobenius with `U = E₂E₃ = E'`
(`U = [U,K]` by the coprime regular action `le_commutator_of_coprime_inf_centralizer_eq_bot`), so
`M' = M_σ ⊔ U`; coprimality (`κ` vs `σ ∪ τ₂ ∪ τ₃`) gives `M' ⊓ K = 1`, and `U ⋊ K = E`,
`M_σ ⋊ E = M` give `M' · K = M`. -/
theorem typeP_derivedInG_isComplement_kappaHall [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M)) [IsCyclic ↥K] :
    Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M) := by
  classical
  -- `K` is a `σ(M)'`-subgroup (a Hall `κ(M)`-subgroup, and `κ(M) ⊆ σ(M)'`).
  have hK_pi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma M)ᶜ) K := by
    intro p hp
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hp
    exact kappa_subset_sigmaCompl (hK.1 p hp)
  obtain ⟨E, E₁, E₂, E₃, hsetup, hKE, hE_pi⟩ :=
    OddOrder.BG.Ch3.S12.exists_subgroupESetup_with_le hG hM hKM hK_pi
  by_cases hτ3 : (kappa M ∩ tau3 M).Nonempty
  · -- Case `κ(M) ∩ τ₃(M) ≠ ∅`: `K = E`.
    obtain ⟨p, hpmem⟩ := hτ3
    rw [Set.mem_inter_iff] at hpmem
    obtain ⟨hpκ, hpτ3⟩ := hpmem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors ((mem_tau3_iff M p).mp hpτ3).2.1
    obtain ⟨hE3ne, hreg⟩ := E3_not_regular_of_mem_kappa_tau3 hG hsetup hp hpκ hpτ3
    obtain ⟨hE1ne, hEeq, hEprime, hEnorm⟩ := E3_not_regular_consequences hG hsetup hE3ne hreg
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
    exact typeP_derivedInG_complement_of_eq_complement hG hsetup hKEeq
  · -- Case `κ(M) ⊆ τ₁(M)`: conjugate the setup so its `E₁` is `K`.
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
    set Ebar := MulAut.conj w • E with hEbardef
    set Ebar₂ := MulAut.conj w • E₂ with hEbar₂def
    set Ebar₃ := MulAut.conj w • E₃ with hEbar₃def
    -- `h' : SubgroupESetup M Ebar K Ebar₂ Ebar₃`.
    by_cases hUbot : (Ebar₂ ⊔ Ebar₃ : Subgroup G) = ⊥
    · -- `Ebar = K`, so `M' = M_σ` and `K = Ebar` complements it.
      have hEbarK : K = Ebar := by
        have hsup := h'.eq_sup hG
        rw [sup_assoc, hUbot, sup_bot_eq] at hsup
        exact hsup.symm
      exact typeP_derivedInG_complement_of_eq_complement hG h' hEbarK
    · -- `E = K ⋉ U` is a Frobenius group with `U = Ebar₂ ⊔ Ebar₃ ≠ 1`, and `U = E' = [E,E]`.
      have hUleE : (Ebar₂ ⊔ Ebar₃ : Subgroup G) ≤ Ebar := sup_le h'.E₂_le h'.E₃_le
      have hKleEbar : K ≤ Ebar := h'.E₁_le
      obtain ⟨hKne, hKnonreg⟩ := E1_not_regular_of_mem_kappa_tau1 hG h'
        (prime_of_mem_kappa hp₀κ) hp₀κ (hκτ1 p₀ hp₀κ)
      have hKprime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) K := E1_actsPrime hG h' hKne
      have hKstar' : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥ :=
        Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hKprime (le_refl K) hKnonreg
      have hfrob := isFrobeniusGroup_E_of_caseTau1 hG h' hKne hKstar' hτ3 hUbot
      have hcompl_Ebar : ((Ebar₂ ⊔ Ebar₃).subgroupOf Ebar).IsComplement' (K.subgroupOf Ebar) :=
        hfrob.isComplement
      -- coprime `|K|`, `|U|` and `U ⊓ C(K) = ⊥` (regular action of `K = E₁` on `U`).
      have hcopKU : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(Ebar₂ ⊔ Ebar₃)) := by
        have hc := (hfrob.coprime_card_kernel_complement).symm
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKleEbar).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUleE).toEquiv] at hc
      have hCUK : (Ebar₂ ⊔ Ebar₃ : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
        obtain ⟨⟨g₀, hg₀K⟩, hg₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKne
        have hg₀1 : g₀ ≠ 1 := fun hc => hg₀ne (Subtype.ext hc)
        have hr := actsRegularlyOn_E23_E1_of_caseTau1 hG h' hKne hKstar' hτ3 g₀ hg₀K hg₀1
        rw [fixedByElement_def] at hr
        rw [eq_bot_iff, ← hr]
        exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hg₀K))
      -- `U = [K, U] ≤ E' = derivedInG Ebar`.
      have hKsolv : Group.IsSolvable ↥K :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
            (hKleEbar.trans h'.E_le))
      have hUleE' : (Ebar₂ ⊔ Ebar₃ : Subgroup G) ≤ derivedInG Ebar := by
        have hUcomm : (Ebar₂ ⊔ Ebar₃ : Subgroup G) ≤ ⁅K, Ebar₂ ⊔ Ebar₃⁆ :=
          OddOrder.BG.Ch2.S08.le_commutator_of_coprime_inf_centralizer_eq_bot
            (hKleEbar.trans (h'.E23_normal hG)) hcopKU hCUK
        have hcomm_le : (⁅K, Ebar₂ ⊔ Ebar₃⁆ : Subgroup G) ≤ ⁅Ebar, Ebar⁆ :=
          Subgroup.commutator_mono hKleEbar hUleE
        exact hUcomm.trans (le_of_le_of_eq hcomm_le (Subgroup.map_subtype_commutator Ebar).symm)
      -- `E' = U`: the abstract `commutator_eq_sup` for `Ebar = K ⋉ U` with `K` cyclic.
      have hcommEbar_eq : (derivedInG Ebar).subgroupOf Ebar = commutator ↥Ebar := by
        rw [derivedInG, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective Ebar.subtype_injective]
      have hdEbar : derivedInG Ebar = (Ebar₂ ⊔ Ebar₃ : Subgroup G) := by
        have hUnorm : ((Ebar₂ ⊔ Ebar₃).subgroupOf Ebar).Normal :=
          Subgroup.normal_subgroupOf_of_le_normalizer (h'.E23_normal hG)
        have hUcommE : (Ebar₂ ⊔ Ebar₃).subgroupOf Ebar ≤ commutator ↥Ebar := by
          rw [← hcommEbar_eq]; exact Subgroup.comap_mono hUleE'
        have hsupcomm := commutator_eq_sup_commutator_of_isComplement' hcompl_Ebar hUcommE
        have hKbarbot : ⁅K.subgroupOf Ebar, K.subgroupOf Ebar⁆ = ⊥ := by
          refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (fun x hx => ?_)
          let : CommGroup ↥K := IsCyclic.commGroup
          refine Subgroup.mem_centralizer_iff.mpr (fun y hy => Subtype.ext ?_)
          have hxK : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hx
          have hyK : (y : G) ∈ K := Subgroup.mem_subgroupOf.mp hy
          have hcm := congrArg Subtype.val (mul_comm (⟨(y : G), hyK⟩ : ↥K) (⟨(x : G), hxK⟩ : ↥K))
          simpa using hcm
        rw [hKbarbot, sup_bot_eq] at hsupcomm
        rw [show derivedInG Ebar = (commutator ↥Ebar).map Ebar.subtype from rfl, hsupcomm,
          Subgroup.map_subgroupOf_eq_of_le hUleE]
      -- `M' = M_σ ⊔ U`.
      have hM'eq : derivedInG M = OddOrder.BG.Ch3.S10.Msigma M ⊔ (Ebar₂ ⊔ Ebar₃) := by
        rw [derivedInG_eq_Msigma_sup_derivedInG_complement hG h', hdEbar]
      have hcommM : (derivedInG M).subgroupOf M = commutator ↥M := by
        rw [derivedInG, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
      have hdEbarM : derivedInG Ebar ≤ derivedInG M := by
        rw [show derivedInG Ebar = ⁅Ebar, Ebar⁆ from Subgroup.map_subtype_commutator Ebar,
          show derivedInG M = ⁅M, M⁆ from Subgroup.map_subtype_commutator M]
        exact Subgroup.commutator_mono h'.E_le h'.E_le
      have hUleM' : (Ebar₂ ⊔ Ebar₃ : Subgroup G) ≤ derivedInG M := hdEbar ▸ hdEbarM
      -- `M' ⊓ K = ⊥` (coprime `κ` vs `σ ∪ τ₂ ∪ τ₃`, via `M' ⊓ K ≤ E' ⊓ K = U ⊓ K`).
      have hMKbot : derivedInG M ⊓ K = ⊥ := by
        have hle1 : derivedInG M ⊓ K ≤ derivedInG Ebar :=
          (inf_le_inf_left (derivedInG M) hKleEbar).trans
            (by rw [inf_comm]; exact h'.inf_derivedInG_le_derivedInG)
        have hbot2 : (Ebar₂ ⊔ Ebar₃ : Subgroup G) ⊓ K = ⊥ := by
          rw [inf_comm]; exact (Subgroup.disjoint_of_coprime_natCard hcopKU).eq_bot
        exact le_bot_iff.mp ((le_inf (hle1.trans hdEbar.le) inf_le_right).trans hbot2.le)
      -- `M' ⊔ K = M` (`U ⊔ K = Ebar`, `M_σ ⊔ Ebar = M`).
      have hUKsup : (Ebar₂ ⊔ Ebar₃ : Subgroup G) ⊔ K = Ebar := by
        have hsup := hcompl_Ebar.sup_eq_top
        rw [← Subgroup.subgroupOf_sup hUleE hKleEbar] at hsup
        exact le_antisymm (sup_le hUleE hKleEbar) (Subgroup.subgroupOf_eq_top.mp hsup)
      have hMKsup : derivedInG M ⊔ K = M := by
        refine le_antisymm (sup_le (Subgroup.map_subtype_le _) hKM) ?_
        calc M = OddOrder.BG.Ch3.S10.Msigma M ⊔ Ebar := h'.E_compl_sup.symm
          _ ≤ derivedInG M ⊔ K := by
              refine sup_le ((OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM).trans le_sup_left) ?_
              rw [← hUKsup]
              exact sup_le (hUleM'.trans le_sup_left) le_sup_right
      -- Assemble the complement: disjoint + product covers `↥M` (`M'` normal).
      have hderM_le : derivedInG M ≤ M := Subgroup.map_subtype_le _
      rw [hcommM]
      refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
      · rw [disjoint_iff, ← hcommM,
          show (derivedInG M).subgroupOf M ⊓ K.subgroupOf M
            = (derivedInG M ⊓ K).subgroupOf M from rfl, hMKbot, Subgroup.bot_subgroupOf]
      · have hsuptop : commutator ↥M ⊔ K.subgroupOf M = ⊤ := by
          rw [← hcommM, ← Subgroup.subgroupOf_sup hderM_le hKM, hMKsup, Subgroup.subgroupOf_self]
        rw [← Subgroup.normal_mul, hsuptop, Subgroup.coe_top]

/-- **BG Theorem 14.7** (mmd L3890): type-P duality and the `Z_tilde` TI-set.

For a type-P maximal subgroup `M`, there is a unique nonconjugate type-P partner
`Mstar`.  The two Hall factors `K` and `Kstar` form a cyclic subgroup `Z`,
`Z_tilde` is a TI-set, one of the two partners is type `P2`, and every type-P
maximal subgroup is conjugate to one of the pair.

**Part (h)** (BG 14.7(8), exposed 2026-06-15 for Lane G §15 — issue 8006): `M' = [M,M]` is a
complement of `K` in `M` (`M = K M'`, `K ∩ M' = 1`), with `|M'|`, `|K|` coprime.  BG Cor 15.6
(mmd L4232) and Lemma 15.1 cite this directly; it is surfaced as the two leading conjuncts so
`§15` can apply it without re-deriving κ/τ prime-handling. -/
theorem typeP_duality [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M) ∧
    Nat.Coprime (Nat.card ↥((derivedInG M).subgroupOf M)) (Nat.card ↥(K.subgroupOf M)) ∧
    ∃! Mstar : Subgroup G,
      Mstar ∈ maximalSubgroups G ∧ IsTypeP Mstar ∧ ¬ IsConjugateSubgroup M Mstar ∧
      (Kstar ≤ Mstar ∧ Ch03.IsHallSubgroup (kappa Mstar) (Kstar.subgroupOf Mstar) ∧
        K = OddOrder.BG.Ch3.S10.Msigma Mstar ⊓ Subgroup.centralizer (Kstar : Set G)) ∧
      IsCyclic ↥(K ⊔ Kstar) ∧ IsTISubset (zTilde K Kstar) (K ⊔ Kstar) ∧
      (IsTypeP2 M ∨ IsTypeP2 Mstar) ∧
      (∀ H : Subgroup G, H ∈ maximalSubgroups G → IsTypeP H →
        IsConjugateSubgroup H M ∨ IsConjugateSubgroup H Mstar) := by
  classical
  -- A Hall `(κ(M) ∪ σ(M))'`-subgroup `U` of `M` (Hall's theorem in the solvable `M`).
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
    ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  have hUeq : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUeq]; exact hU'
  -- The counting collapse `n = 1` makes `Z = K ⊔ K*` cyclic, hence the Hall `κ`-factor `K`
  -- cyclic (subgroup of a cyclic group); this is what Proposition 14.2(a)/part (h) consumes.
  obtain ⟨Mstar, hMstarne, hMstarmem, hpart⟩ :=
    exists_partner hG (dummySigmaDecomposition G) hM hP hKM hK hKstar hU
  have hZcyc : IsCyclic ↥(K ⊔ Kstar) :=
    typeP_Z_isCyclic hG (dummySigmaDecomposition G) hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  have : IsCyclic ↥K :=
    (Subgroup.subgroupOfEquivOfLe (le_sup_left : K ≤ K ⊔ Kstar)).isCyclic.mp inferInstance
  -- Part (h): `M' = [M,M]` complements `K` in `M` (Proposition 14.2(a): `M' = U M_σ`).
  have hparth : Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M) :=
    typeP_derivedInG_isComplement_kappaHall hG hM hP hKM hK
  exact ⟨hparth, coprime_card_derived_kappaHall_of_isComplement' hK hparth,
    typeP_partner_existsUnique hG (dummySigmaDecomposition G) hM hP hKM hK hKstar hU⟩

/-- **BG `kappaJ`** (conjugation-invariance of `κ`): `κ(M^g) = κ(M)`.  Each defining condition of
`κ` is conjugation-stable: `τ₁(M) ∪ τ₃(M) = {p | p ∉ σ(M) ∧ r_p(M) = 1}` (with `σ`, `pRank`
invariant), and a rank-one witness `P ≤ M` with `M_σ ⊓ C(P) ≠ 1` transports to `P^{g⁻¹}` (via
`M_σ`, centralizer, and `ℰ_p¹` equivariance).  A prerequisite for the type-`P₁`/`P₂`
conjugation-invariance used in BG Cor 14.12 (`typeP2_neighbor_is_typeF`, `sK_FD`). -/
theorem kappa_conj_smul [Finite G] (g : G) (M : Subgroup G) :
    kappa (MulAut.conj g • M) = kappa M := by
  classical
  -- One inclusion for all `a, N` suffices; the reverse follows with `a := g⁻¹`, `N := M^g`.
  suffices h : ∀ (a : G) (N : Subgroup G), kappa (MulAut.conj a • N) ⊆ kappa N by
    refine le_antisymm (h g M) (fun p hp => ?_)
    have hMeq : MulAut.conj g⁻¹ • (MulAut.conj g • M) = M := by
      rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    exact h g⁻¹ (MulAut.conj g • M) (hMeq.symm ▸ hp)
  intro a N p hp
  obtain ⟨hpp, hτ, P, hPelem, hPN, hPC⟩ := hp
  have : Fact p.Prime := ⟨hpp⟩
  have hinv : MulAut.conj a⁻¹ • (MulAut.conj a • N) = N := by
    rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  refine ⟨hpp, ?_, MulAut.conj a⁻¹ • P, conj_smul_mem_elemAbelianOfRank a⁻¹ hPelem, ?_, ?_⟩
  · -- `p ∈ τ₁(N) ∪ τ₃(N)`: from `hτ` extract `p ∉ σ ∧ r_p = 1`, transport, rebuild.
    have hcommon : p ∉ OddOrder.BG.Ch3.S10.sigma (MulAut.conj a • N) ∧
        pRank ↥(MulAut.conj a • N) p = 1 := by
      rcases hτ with h1 | h3
      · exact ⟨((mem_tau1_iff _ _).mp h1).1, ((mem_tau1_iff _ _).mp h1).2.2⟩
      · exact ⟨((mem_tau3_iff _ _).mp h3).1, ((mem_tau3_iff _ _).mp h3).2.2⟩
    have hσN : p ∉ OddOrder.BG.Ch3.S10.sigma N := by
      have h1 := hcommon.1; rwa [sigma_conj_smul_eq] at h1
    have hpRankN : pRank ↥N p = 1 := by
      have heq : pRank ↥N p = pRank ↥(MulAut.conj a • N) p :=
        pRank_eq_of_mulEquiv
          (Subgroup.equivMapOfInjective N (MulAut.conj a).toMonoidHom (MulAut.conj a).injective)
      rw [heq]; exact hcommon.2
    by_cases hπ : p ∈ (Nat.card ↥(derivedInG N)).primeFactors
    · exact Or.inr ((mem_tau3_iff _ _).mpr ⟨hσN, hπ, hpRankN⟩)
    · exact Or.inl ((mem_tau1_iff _ _).mpr ⟨hσN, hπ, hpRankN⟩)
  · -- `P^{a⁻¹} ≤ N` (apply `conj a⁻¹` to `P ≤ M^a`).
    rw [← hinv]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hPN
  · -- `M_σ(N) ⊓ C(P^{a⁻¹}) ≠ ⊥` (apply `conj a⁻¹` to `M_σ(M^a) ⊓ C(P) ≠ ⊥`).
    have hbot : MulAut.conj a⁻¹ • (OddOrder.BG.Ch3.S10.Msigma (MulAut.conj a • N) ⊓
        Subgroup.centralizer (P : Set G)) ≠ ⊥ := by
      rw [Ne, pointwise_smul_eq_bot_iff]; exact hPC
    rwa [Subgroup.smul_inf, centralizer_pointwise_smul, ← coe_pointwise_smul,
      show MulAut.conj a⁻¹ • OddOrder.BG.Ch3.S10.Msigma (MulAut.conj a • N)
        = OddOrder.BG.Ch3.S10.Msigma N from by rw [← Msigma_conj_smul, hinv]] at hbot

/-- `π(M) ∖ σ(M)` (`sigmaComplementPrimes`) is conjugation-invariant. -/
theorem sigmaComplementPrimes_conj_smul [Finite G] (g : G) (M : Subgroup G) :
    sigmaComplementPrimes (MulAut.conj g • M) = sigmaComplementPrimes M := by
  unfold sigmaComplementPrimes piSet
  rw [card_pointwise_smul, sigma_conj_smul_eq]

/-- **Type-`P` is conjugation-invariant** (`kappa_conj_smul`). -/
theorem isTypeP_conj_smul [Finite G] (g : G) (M : Subgroup G) :
    IsTypeP (MulAut.conj g • M) ↔ IsTypeP M := by
  unfold IsTypeP; rw [kappa_conj_smul]

/-- **Type-`P₁` is conjugation-invariant**. -/
theorem isTypeP1_conj_smul [Finite G] (g : G) (M : Subgroup G) :
    IsTypeP1 (MulAut.conj g • M) ↔ IsTypeP1 M := by
  unfold IsTypeP1
  rw [kappa_conj_smul, sigmaComplementPrimes_conj_smul, isTypeP_conj_smul]

/-- **κ-Hall data transfers under conjugation of the ambient maximal**: if `conj g • N = M` and
`KN.subgroupOf N` is a Hall `κ(N)`-subgroup, then `(conj g • KN).subgroupOf M` is a Hall
`κ(M)`-subgroup.  Conjugation by `g` restricts to a `↥N ≃ ↥M` preserving both `Nat.card` and the
index, and `κ` is conjugation-invariant.  This is the fix-`W` data step: it lets a conjugate
type-`P` maximal's `Ẑ` be related to a fixed reference `Ẑ`. -/
theorem isHall_kappa_subgroupOf_conj [Finite G] (g : G) {M N KN : Subgroup G}
    (hg : MulAut.conj g • N = M) (hKNN : KN ≤ N)
    (hKN : Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N)) :
    Ch03.IsHallSubgroup (kappa M) ((MulAut.conj g • KN).subgroupOf M) := by
  have hkap : kappa M = kappa N := by rw [← hg, kappa_conj_smul]
  have hle : MulAut.conj g • KN ≤ M := by
    rw [← hg]; exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hKNN
  -- `Nat.card` is conjugation-invariant; the two `subgroupOf`s have equal card (both
  -- `= Nat.card KN`).
  have hcardKN : Nat.card ↥(MulAut.conj g • KN) = Nat.card ↥KN := by
    rw [Subgroup.pointwise_smul_def]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).toEquiv).symm
  have hcardamb : Nat.card ↥(MulAut.conj g • N) = Nat.card ↥N := by
    rw [Subgroup.pointwise_smul_def]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).toEquiv).symm
  have hcard : Nat.card ↥((MulAut.conj g • KN).subgroupOf M) = Nat.card ↥(KN.subgroupOf N) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKNN).toEquiv, hcardKN]
  -- the indices agree, via `index · card = card ambient` and the card equalities above.
  have hidx : ((MulAut.conj g • KN).subgroupOf M).index = (KN.subgroupOf N).index := by
    have hMrel := ((MulAut.conj g • KN).subgroupOf M).index_mul_card
    have hNrel := (KN.subgroupOf N).index_mul_card
    have hMN : Nat.card ↥M = Nat.card ↥N := by rw [← hg]; exact hcardamb
    rw [hcard, hMN] at hMrel
    rw [← hNrel] at hMrel
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hMrel
  unfold Ch03.IsHallSubgroup at hKN ⊢
  rw [hkap, hcard, hidx]; exact hKN

/-- **fix-`W` threading**: two conjugate type-`P` maximals `N ~ M` carry `Ẑ`'s with the same
`G`-conjugacy-class closure.  Concretely, if `N` and `M` carry Theorem 14.7 data
`(KN, KstarN)` resp. `(K, Kstar)` and `N` is `G`-conjugate to `M`, then
`𝒞_G(zTilde KN KstarN) = 𝒞_G(zTilde K Kstar)`.  The conjugator `g` (`conj g • N = M`) is corrected
by a Hall conjugacy `w ∈ M` so that `conj (w*g)` carries `N`'s data exactly onto `M`'s; the
`conjClassSet` is then conjugation-invariant via `conjClassSet_zTilde_conj_eq`. -/
theorem conjClassSet_zTilde_eq_of_isConjugate [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M N K Kstar KN KstarN : Subgroup G}
    (hMmax : M ∈ maximalSubgroups G) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (_hNmax : N ∈ maximalSubgroups G) (hKNN : KN ≤ N)
    (hKN : Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N))
    (hKstarN : KstarN = OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G))
    (hconj : IsConjugateSubgroup N M) :
    conjClassSet (zTilde KN KstarN) = conjClassSet (zTilde K Kstar) := by
  obtain ⟨g, hg⟩ := hconj
  have hle : MulAut.conj g • KN ≤ M := by
    rw [← hg]; exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hKNN
  have hHallM : Ch03.IsHallSubgroup (kappa M) ((MulAut.conj g • KN).subgroupOf M) :=
    isHall_kappa_subgroupOf_conj g hg hKNN hKN
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hMmax
  obtain ⟨w, hwM, hw⟩ :=
    OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf inferInstance hle hKM hHallM hK
  -- `conj (w*g)` carries `N`'s `κ`-Hall and ambient maximal exactly onto `M`'s.
  have hKeq : MulAut.conj (w * g) • KN = K := by rw [map_mul, mul_smul]; exact hw
  have hMN : MulAut.conj (w * g) • N = M := by
    rw [map_mul, mul_smul, hg]
    exact conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hwM)
  -- hence it carries `KstarN = N_σ ∩ C(KN)` onto `Kstar = M_σ ∩ C(K)`.
  have hKstareq : MulAut.conj (w * g) • KstarN = Kstar := by
    rw [hKstarN, Subgroup.smul_inf, centralizer_pointwise_smul, ← coe_pointwise_smul, hKeq, hKstar]
    congr 1
    rw [← Msigma_conj_smul, hMN]
  -- `conjClassSet` is conjugation-invariant on `Ẑ`.
  calc conjClassSet (zTilde KN KstarN)
      = conjClassSet (zTilde (MulAut.conj (w * g) • KN) (MulAut.conj (w * g) • KstarN)) :=
        (conjClassSet_zTilde_conj_eq (w * g) KN KstarN).symm
    _ = conjClassSet (zTilde K Kstar) := by rw [hKeq, hKstareq]

/-- **fix-`W`** (BG Cor 14.8 packaging): for a reference type-`P` maximal `M` (with Theorem 14.7
data `K, K*, U`) and *any* type-`P` maximal `N` (with data `KN, KstarN`), the `Ẑ` of `N` has the
same `G`-conjugacy-class closure as the fixed `Ẑ(M) = zTilde K K*`.  Every type-`P` `N` is
`G`-conjugate to `M` or to its partner `M*` (`typeP_covering`); the `M`-class lands on `W` by
`conjClassSet_zTilde_eq_of_isConjugate`, and the `M*`-class lands on `zTilde K* K = zTilde K K*`
(`typeP_partner_structure` supplies `M*`'s data `(K*, K)`, then `zTilde_comm`). -/
theorem conjClassSet_zTilde_eq_fixed_of_isTypeP [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U N KN KstarN : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hNmax : N ∈ maximalSubgroups G) (hNP : IsTypeP N) (hKNN : KN ≤ N)
    (hKN : Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N))
    (hKstarN : KstarN = OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)) :
    conjClassSet (zTilde KN KstarN) = conjClassSet (zTilde K Kstar) := by
  obtain ⟨Mstar, hMstarne, hMstarmem, hpart⟩ :=
    exists_partner hG (genuineSigmaDecomposition hG) hM hP hKM hK hKstar hU
  obtain ⟨hMstarmax, hMstarP, hKstarMstar, hKstar_hall, hKeq⟩ :=
    typeP_partner_structure hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  rcases typeP_covering hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart hNmax hNP with
    hNM | hNMstar
  · exact conjClassSet_zTilde_eq_of_isConjugate hG hM hKM hK hKstar hNmax hKNN hKN hKstarN hNM
  · rw [conjClassSet_zTilde_eq_of_isConjugate hG hMstarmax hKstarMstar hKstar_hall hKeq
      hNmax hKNN hKN hKstarN hNMstar, zTilde_comm]

/-- **Type-`P` data constructor**: every maximal subgroup `M` carries the Theorem 14.7 data — a
Hall `κ(M)`-subgroup `K ≤ M`, the swap `K* = M_σ ∩ C_G(K)`, and a Hall `(κ ∪ σ)ᶜ`-subgroup `U` —
obtained from Hall's theorem in the solvable `↥M`.  This is the missing constructor that lets the
family-level corollaries (14.8) feed `exists_partner` / `typeP_covering` from a bare
`M ∈ maximalTypePFamily`. -/
theorem exists_typeP_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    ∃ K Kstar U : Subgroup G, K ≤ M ∧
      Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M) ∧
      Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) ∧
      Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) := by
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  obtain ⟨HK, hHK⟩ := Ch03.hall_E_exists (G := ↥M) (kappa M)
  obtain ⟨HU, hHU⟩ :=
    Ch03.hall_E_exists (G := ↥M) ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  refine ⟨HK.map M.subtype,
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ((HK.map M.subtype : Subgroup G) : Set G),
    HU.map M.subtype, Subgroup.map_subtype_le _, ?_, rfl, ?_⟩
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    exact hHK
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    exact hHU

end OddOrder.BG.Ch4.S14


