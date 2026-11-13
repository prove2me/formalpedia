-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_GlobalCounting
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_GlobalCounting
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T09:46:38.359213+00:00
-- url     : https://prove2.me/theorems/4a39bc4d-d38b-4c60-80e0-054518035f3c
-- title:
--   BG §14: type-$\mathcal{P}$ global counting (continuation)
-- statement:
--   A continuation of the global-counting part of the §14 development of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*. It consists of lemmas only.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 9 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/GlobalCounting.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/GlobalCounting.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_KappaHallCommutator

namespace OddOrder.BG.Ch4.S14

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch3.S13

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BG `defUK`** (Coq `P2type_signalizer`, BGsection14.v L2329): for a type-`P₂` maximal
subgroup `M` with cyclic Hall `κ(M)`-subgroup `K` and abelian `(κ(M) ∪ σ(M))'`-Hall complement
`U` normalized by `K`, the commutator `⁅U, K⁆` equals `U`.

The coprime decomposition `U = (C(K) ⊓ U) ⊔ ⁅U, K⁆` (`fitting_coprime_abelian_decomp`: `U`
abelian, `K ≤ N(U)`, `gcd(|U|,|K|) = 1`) collapses because `C_U(K) = C(K) ⊓ U = ⊥`.  Indeed
Theorem A(4) (`typeP_hall_inf_centralizer_kappaElement_eq_bot`) gives `U ⊓ C(k) = ⊥` for every
`k ∈ K#`, and `C(K) ⊓ U ≤ C(k) ⊓ U` for any such `k` (one exists since `K ≠ ⊥`).  `K` is cyclic
of prime order `q = |K|` by Proposition 14.2(g) (type-`P₂`). -/
theorem typeP2_kappaHall_commutator_eq_self [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : IsTypeP2 M) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hKNU : K ≤ Subgroup.normalizer (U : Set G)) :
    (⁅U, K⁆ : Subgroup G) = U := by
  classical
  have hP : IsTypeP M := hP2.1
  -- `|K| = q` is prime (Prop 14.2(g) for type-`P₂`), so `K` is cyclic.
  obtain ⟨-, -, -, -, hP2struct, -, -⟩ := typeP_structure hG hM hP hKM hK hKstar hU
  obtain ⟨-, q, hqprime, hKcard, -⟩ := hP2struct hP2
  have : Fact q.Prime := ⟨hqprime⟩
  have hKcyc : IsCyclic ↥K := isCyclic_of_prime_card hKcard
  have hKne : K ≠ ⊥ := fun h => card_kappaHall_ne_one hP hKM hK (by rw [h, Subgroup.card_bot])
  obtain ⟨k₀, hk₀K, hk₀ne⟩ := (Subgroup.bot_or_exists_ne_one K).resolve_left hKne
  -- `C(K) ⊓ U = ⊥` from Theorem A(4) at `k₀ ∈ K#` (`C(K) ⊓ U ≤ C(k₀) ⊓ U = U ⊓ C(k₀) = ⊥`).
  have hCUK_bot : Subgroup.centralizer (K : Set G) ⊓ U = ⊥ := by
    have hA4 := typeP_hall_inf_centralizer_kappaElement_eq_bot hG hM hP hKM hUM hK hKstar hU
      k₀ hk₀K hk₀ne
    rw [eq_bot_iff, ← hA4]
    exact le_inf inf_le_right
      (inf_le_left.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hk₀K)))
  -- Coprime `|U|` (a `(κ∪σ)'`-number) and `|K|` (a `κ ⊆ κ∪σ` number).
  have hcopUK : Nat.Coprime (Nat.card ↥U) (Nat.card ↥K) :=
    Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) Nat.card_pos.ne' Nat.card_pos.ne'
      (fun p _ => hU.1 p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv]))
      (fun p _ hpc => hpc (Or.inl (hK.1 p
        (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]))))
  -- Collapse the coprime decomposition `U = (C(K) ⊓ U) ⊔ ⁅U, K⁆`.
  have hUcomm_inst : IsMulCommutative ↥U :=
    ⟨⟨fun a b => Subtype.ext (hUab (a : G) a.2 (b : G) b.2)⟩⟩
  have hd := (OddOrder.Isaacs.Ch05.fitting_coprime_abelian_decomp (P := U) (K := K) hKNU hcopUK).2
  rwa [hCUK_bot, bot_sup_eq] at hd

/-- In a finite nilpotent subgroup `N`, a subgroup `P ≤ N` that is self-normalizing in `N`
(`N_G(P) ⊓ N ≤ P`) must be all of `N` — the normalizer condition: proper subgroups of a
nilpotent group grow under normalization.  Generalizes `sylow_coe_eq_of_normalizer_inf_le`
(`P` need not be Sylow, only `N` nilpotent). -/
private theorem eq_of_isNilpotent_normalizer_inf_le [Finite G] {N P : Subgroup G}
    (hN : Group.IsNilpotent ↥N) (hPN : P ≤ N)
    (hle : Subgroup.normalizer (P : Set G) ⊓ N ≤ P) : N = P := by
  have : Group.IsNilpotent ↥N := hN
  have hnc : NormalizerCondition ↥N := Group.normalizerCondition_of_isNilpotent
  have hself : Subgroup.normalizer (P.subgroupOf N) = P.subgroupOf N := by
    rw [← Subgroup.subgroupOf_normalizer_eq hPN]
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_) <;>
      rw [Subgroup.mem_subgroupOf] at hx ⊢
    · exact hle ⟨hx, x.2⟩
    · exact P.le_normalizer hx
  have htop : P.subgroupOf N = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp hnc) _ hself
  exact le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hPN

/-- **BG Corollary 14.12** (mmd L4035): for `M ∈ 𝓜_{P₂}` with `K`, `M*`, `K*` as in
Theorem 14.7 and `U` as in Proposition 14.2(a), `r ∈ π(U)`, `R` the Sylow `r`-subgroup of the
abelian `U`, and `H ∈ 𝓜(N_G(R))`: then `H ∈ 𝓜_F`, `U ⊆ H_σ`, `M ∩ H = U K`, `N_H(U) ⊄ M`,
`K ⊆ F(H ∩ M*)`, and `H ∩ M*` complements `H_σ` in `H`.

**Faithfulness (2026-06-22):** the hypotheses are tightened to BG — `U` is the specific
abelian Hall `(κ(M) ∪ σ(M))'`-factor of Proposition 14.2(a) and `R` is a *Sylow* `r`-subgroup
of `U` (`IsHallSubgroup {r}`), not an arbitrary `U ≤ M`, `R ≤ U` with `R ≠ ⊥` (under which the
conclusion fails).  The conclusion now also delivers `N_H(U) ⊄ M` (the FT-path clause consumed by
BG Theorem C(1) = `theoremC_paired_structure` conjunct 2): `N_H(U) = H ⊓ N_G(U) ≤ N_G(U)`, so
`N_H(U) ⊄ M ⟹ N_G(U) ⊄ M`.  The two remaining BG clauses `K ⊆ F(H ∩ M*)` and `σ(H)'-Hall(H)(H ∩ M*)`
(which require exposing the dual partner `M*` in the signature) are not consumed by any caller and
are omitted; the proof establishes `H ∩ M* = D` internally, so they are derivable if needed.
Translates the Coq `P2type_signalizer` (BGsection14.v L2243).  See `notes/bg/s14_typeP_counting.md`.
-/
theorem typeP2_neighbor_is_typeF_of_mem [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U R H : Subgroup G} {r : ℕ} (hM : M ∈ maximalSubgroups G) (hP2 : IsTypeP2 M)
    (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hr : r ∈ piSet U) (hRU : R ≤ U)
    (hR : Ch03.IsHallSubgroup ({r} : Set ℕ) (R.subgroupOf U))
    (hKNU : K ≤ Subgroup.normalizer (U : Set G))
    (hH : H ∈ maximalSubgroupsContaining (Subgroup.normalizer (R : Set G))) :
      IsTypeF H ∧ U ≤ OddOrder.BG.Ch3.S10.Msigma H ∧ M ⊓ H = U ⊔ K ∧
      ¬ ((H ⊓ Subgroup.normalizer (U : Set G) : Subgroup G) ≤ M) ∧
      ∃ E E₁ E₂ E₃ : Subgroup G,
        OddOrder.BG.Ch3.S12.SubgroupESetup H E E₁ E₂ E₃ ∧ K ≤ E ∧
          K ≤ OddOrder.BG.Ch2.S08.fittingInG E := by
  classical
  have hP : IsTypeP M := hP2.1
  have : Fact r.Prime := ⟨Nat.prime_of_mem_primeFactors hr⟩
  have hrprime : r.Prime := Fact.out
  have hRM : R ≤ M := hRU.trans hUM
  -- `r ∉ σ(M)`: `r ∈ π(U)` and `U` is a `(κ(M) ∪ σ(M))'`-Hall subgroup of `M`.
  have hrU' : r ∈ (Nat.card ↥(U.subgroupOf M)).primeFactors := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv]
  have hrκσ : r ∈ (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ := hU.1 r hrU'
  have hrσM : r ∉ OddOrder.BG.Ch3.S10.sigma M := fun h => hrκσ (Or.inr h)
  -- `R ≠ ⊥`: `r ∣ |U|` and (Hall) `r ∤ [U : R]`, so `r ∣ |R|`.
  have hRne : R ≠ ⊥ := by
    have hlag : Nat.card ↥(R.subgroupOf U) * (R.subgroupOf U).index = Nat.card ↥U :=
      Subgroup.card_mul_index _
    have hridx : ¬ r ∣ (R.subgroupOf U).index := fun hd =>
      hR.2 r (Nat.mem_primeFactors.mpr ⟨hrprime, hd, Subgroup.index_ne_zero_of_finite⟩) rfl
    have hrSub : r ∣ Nat.card ↥(R.subgroupOf U) :=
      ((Nat.Prime.dvd_mul hrprime).mp
        (by rw [hlag]; exact Nat.dvd_of_mem_primeFactors hr)).resolve_right
        hridx
    have hrR : r ∣ Nat.card ↥R := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRU).toEquiv] at hrSub
    intro h; rw [h, Subgroup.card_bot] at hrR
    exact hrprime.one_lt.ne' (Nat.eq_one_of_dvd_one hrR ▸ rfl)
  -- Setup: the dual partner `M*` (Theorem 14.7 / `typeP_duality`).
  set Kstar : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
    with hKstardef
  obtain ⟨Mst, hMstprop, hMstuniq⟩ := (typeP_duality hG hM hP hKM hK hKstardef).2.2
  obtain ⟨hMstmax, hMstP, hMnc, hMstpair, hZcyc, hZti, hP2or, hcover⟩ := hMstprop
  -- `H ∈ 𝓜(N_G(R))` is now a hypothesis (`hH`); extract maximality and `N_G(R) ≤ H`.
  obtain ⟨hHmax, hNRH⟩ := mem_maximalSubgroupsContaining.mp hH
  -- `R ≤ H` (from `N_G(R) ≤ H`).
  have hRH : R ≤ H := (Subgroup.le_normalizer).trans hNRH
  -- `K ≤ H` (Coq `sEH`/`sKH`): `R = O_r(U)` is characteristic in abelian `U` (a normal Sylow
  -- `r`-subgroup), so `K ≤ N(U) ⟹ K ≤ N(R) ≤ H`.  Uses the `kappa_complement` structure
  -- (`group_set (U*K)`, here `hKNU : K ≤ N(U)`).
  have hUcomm : ∀ a b : ↥U, a * b = b * a := fun a b =>
    Subtype.ext (hUab (a : G) a.2 (b : G) b.2)
  -- `R = O_r(U)` is characteristic in abelian `U` (a normal Sylow `r`-subgroup), shared by
  -- `hKH`/`hUH`: `K, U ≤ N(U) ⟹ ≤ N(R) ≤ H`.
  have hRcardU : Nat.card ↥(R.subgroupOf U) = r ^ (Nat.card ↥U).factorization r := by
    have hpow : Nat.card ↥(R.subgroupOf U)
        = r ^ (Nat.card ↥(R.subgroupOf U)).factorization r := by
      apply Nat.eq_pow_of_factorization_eq_single Nat.card_pos.ne'
      apply Finsupp.ext; intro q; rw [Finsupp.single_apply]
      by_cases hq : r = q
      · rw [if_pos hq, hq]
      · rw [if_neg hq]
        by_cases hqp : q.Prime
        · refine Nat.factorization_eq_zero_of_not_dvd (fun hdvd => hq ?_)
          have hmem : q ∈ (Nat.card ↥(R.subgroupOf U)).primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hqp, hdvd, Nat.card_pos.ne'⟩
          exact (Set.mem_singleton_iff.mp (hR.1 q hmem)).symm
        · exact Nat.factorization_eq_zero_of_not_prime _ hqp
    have hfact : (Nat.card ↥U).factorization r
        = (Nat.card ↥(R.subgroupOf U)).factorization r := by
      have hidx : (R.subgroupOf U).index.factorization r = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (fun hdvd =>
          hR.2 r (Nat.mem_primeFactors.mpr ⟨hrprime, hdvd, Subgroup.index_ne_zero_of_finite⟩) rfl)
      have hlag := Subgroup.card_mul_index (R.subgroupOf U)
      rw [← hlag, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
        Finsupp.add_apply, hidx, add_zero]
    rw [hfact]; exact hpow
  have hRUnorm : (R.subgroupOf U).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have heq : g * n * g⁻¹ = n := by
      calc g * n * g⁻¹ = n * g * g⁻¹ := by rw [hUcomm g n]
        _ = n := by group
    rw [heq]; exact hn
  have hPchar : (R.subgroupOf U).Characteristic := by
    have hPn : ((Sylow.ofCard (R.subgroupOf U) hRcardU : Sylow r ↥U) : Subgroup ↥U).Normal := by
      rw [Sylow.coe_ofCard]; exact hRUnorm
    have h := Sylow.characteristic_of_normal (Sylow.ofCard (R.subgroupOf U) hRcardU) hPn
    rwa [Sylow.coe_ofCard] at h
  have hKH : K ≤ H := fun k hk => hNRH (by
    have hmem := OddOrder.BG.Ch1.S03f.mem_normalizer_map_subtype_of_characteristic
      (W := U) (C := R.subgroupOf U) (hKNU hk)
    rwa [Subgroup.map_subgroupOf_eq_of_le hRU] at hmem)
  have hUH : U ≤ H := fun u hu => hNRH (by
    have hmem := OddOrder.BG.Ch1.S03f.mem_normalizer_map_subtype_of_characteristic
      (W := U) (C := R.subgroupOf U) (Subgroup.le_normalizer hu)
    rwa [Subgroup.map_subgroupOf_eq_of_le hRU] at hmem)
  -- `H` is not conjugate to `M` (`r ∈ σ(H) ∖ σ(M)`) nor to its partner `M*` (coprime `K`/`R`).
  -- These two non-conjugacies drive both the type-`F` classification and `σ(H)'`-membership of `K`.
  have notMGH : ¬ IsConjugateSubgroup H M := by
    rintro ⟨a, ha⟩
    -- `|R| = r ^ (|U|).factorization r` (`R` is a Sylow `r`-subgroup of `U`).
    have hSU : Nat.card ↥(R.subgroupOf U) = Nat.card ↥R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRU).toEquiv
    have hRpow : Nat.card ↥R = r ^ (Nat.card ↥R).factorization r := by
      apply Nat.eq_pow_of_factorization_eq_single Nat.card_pos.ne'
      apply Finsupp.ext
      intro q
      rw [Finsupp.single_apply]
      by_cases hq : r = q
      · rw [if_pos hq, hq]
      · rw [if_neg hq]
        by_cases hqp : q.Prime
        · refine Nat.factorization_eq_zero_of_not_dvd (fun hdvd => hq ?_)
          have hmem : q ∈ (Nat.card ↥(R.subgroupOf U)).primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hqp, hSU ▸ hdvd, Nat.card_pos.ne'⟩
          exact (Set.mem_singleton_iff.mp (hR.1 q hmem)).symm
        · exact Nat.factorization_eq_zero_of_not_prime _ hqp
    -- `(|U|).factorization r = (|R|).factorization r` (`r ∤ [U : R]`).
    have hfUR : (Nat.card ↥U).factorization r = (Nat.card ↥R).factorization r := by
      have hidxU : (R.subgroupOf U).index.factorization r = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (fun hdvd =>
          hR.2 r (Nat.mem_primeFactors.mpr ⟨hrprime, hdvd, Subgroup.index_ne_zero_of_finite⟩) rfl)
      have hlag := Subgroup.card_mul_index (R.subgroupOf U)
      rw [← hlag, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
        Finsupp.add_apply, hidxU, add_zero, hSU]
    -- `(|U|).factorization r = (|M|).factorization r` (`r ∤ [M : U]`).
    have hfUM : (Nat.card ↥U).factorization r = (Nat.card ↥M).factorization r := by
      have hidxM : (U.subgroupOf M).index.factorization r = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (fun hdvd =>
          hU.2 r (Nat.mem_primeFactors.mpr ⟨hrprime, hdvd, Subgroup.index_ne_zero_of_finite⟩) hrκσ)
      have hUcard : Nat.card ↥(U.subgroupOf M) = Nat.card ↥U :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv
      have hlag := Subgroup.card_mul_index (U.subgroupOf M)
      rw [← hlag, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
        Finsupp.add_apply, hidxM, add_zero, hUcard]
    -- `|H| = |M|` (conjugate subgroups).
    have hcardHM : Nat.card ↥H = Nat.card ↥M := by
      rw [← ha]; exact (Subgroup.card_map_of_injective (MulAut.conj a).injective).symm
    -- `R` is a Sylow `r`-subgroup of `H`.
    have hRsylH : Nat.card ↥(R.subgroupOf H) = r ^ (Nat.card ↥H).factorization r := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv, hcardHM, ← hfUM, hfUR]
      exact hRpow
    -- `r ∈ σ(H)` (`R` Sylow `r` of `H`, `N_G(R) ≤ H`), hence `r ∈ σ(M)` (conjugacy), contradiction.
    have hrH : r ∈ (Nat.card ↥H).primeFactors := by
      rw [hcardHM]
      exact Nat.mem_primeFactors.mpr ⟨hrprime,
        (Nat.dvd_of_mem_primeFactors hr).trans (Subgroup.card_dvd_of_le hUM), Nat.card_pos.ne'⟩
    have hrσH : r ∈ OddOrder.BG.Ch3.S10.sigma H := by
      rw [OddOrder.BG.Ch3.S10.mem_sigma_iff]
      refine ⟨hrH, Sylow.ofCard (R.subgroupOf H) hRsylH, ?_⟩
      rw [Sylow.coe_ofCard, Subgroup.map_subgroupOf_eq_of_le hRH]
      exact hNRH
    exact hrσM (by have h := OddOrder.BG.Ch3.S10.sigma_conj (M := H) a hrσH; rwa [ha] at h)
  have notMstGH : ¬ IsConjugateSubgroup H Mst := by
    -- `M_σ ∩ M* = K*` (the embedding's conjunct (d) kernel, avoiding the σ(M)-Hall-of-M* clause).
    have hKMsigmaMst : K ≤ OddOrder.BG.Ch3.S10.Msigma Mst :=
      (le_of_eq hMstpair.2.2).trans inf_le_left
    have hMsMst : OddOrder.BG.Ch3.S10.Msigma M ⊓ Mst = Kstar :=
      msigma_inf_partner_eq_kstar hG hM hP2 hKM hKstardef hMstmax hKMsigmaMst hMstpair.1 hMnc
    have hKstarM : Kstar ≤ M := by
      rw [hKstardef]; exact inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le M)
    have hKstarNe : Kstar ≠ ⊥ := (typeP_structure hG hM hP hKM hK hKstardef hU).2.1
    have hKNe : K ≠ ⊥ := fun h => card_kappaHall_ne_one hP hKM hK (by rw [h, Subgroup.card_bot])
    -- `ziMMst : M ⊓ M* = K ⊔ K*` and `sK_uniqMst : K ≤ M*^a ⟹ a ∈ M*`.
    obtain ⟨hziMMst, hsKuniq⟩ := partner_inf_and_uniq hG hMstmax hMstP hMstpair.1 hMstpair.2.1
      hMstpair.2.2 hKMsigmaMst hKM hKstarM hZcyc hKstarNe hKNe hMsMst
    -- `r ∤ |Z|`: `Z = K ⊔ K* = K · K*` (disjoint, commuting), `r ∉ π(K) ⊆ κ(M)`,
    -- `r ∉ π(K*) ⊆ σ(M)`.
    have hKπ : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma M)ᶜ K :=
      kappaHall_isPiSubgroup_sigmaCompl hKM hK
    have hKstarπ : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma M) Kstar :=
      Kstar_isPiSubgroup_sigma hKstardef
    have hrnK : ¬ r ∣ Nat.card ↥K := fun hd => (fun h => hrκσ (Or.inl h))
      (hK.1 r (Nat.mem_primeFactors.mpr ⟨hrprime, by
        rw [Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]; exact hd, Nat.card_pos.ne'⟩))
    have hrnKstar : ¬ r ∣ Nat.card ↥Kstar := fun hd =>
      hrσM (hKstarπ r (Nat.mem_primeFactors.mpr ⟨hrprime, hd, Nat.card_pos.ne'⟩))
    have hKKstar_bot : K ⊓ Kstar = ⊥ := by
      rw [← Subgroup.card_eq_one]
      by_contra hne
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
      have hpσc := hKπ p (Nat.mem_primeFactors.mpr
        ⟨hp, hpd.trans (Subgroup.card_dvd_of_le inf_le_left), Nat.card_pos.ne'⟩)
      have hpσ := hKstarπ p (Nat.mem_primeFactors.mpr
        ⟨hp, hpd.trans (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩)
      exact hpσc hpσ
    have hKcKstar : K ≤ Subgroup.centralizer (Kstar : Set G) := by
      have := hZcyc
      let : CommGroup ↥(K ⊔ Kstar) := IsCyclic.commGroup
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact congrArg Subtype.val (mul_comm (⟨s, Subgroup.mem_sup_right hs⟩ : ↥(K ⊔ Kstar))
        (⟨k, Subgroup.mem_sup_left hk⟩))
    have hcardZ : Nat.card ↥(K ⊔ Kstar) = Nat.card ↥K * Nat.card ↥Kstar :=
      card_sup_eq_mul_of_le_normalizer_of_disjoint
        (hKcKstar.trans (Subgroup.centralizer_le_normalizer _)) hKKstar_bot
    have hrnZ : ¬ r ∣ Nat.card ↥(K ⊔ Kstar) := by
      rw [hcardZ]; exact fun hd => (hrprime.dvd_mul.mp hd).elim hrnK hrnKstar
    have hrR : r ∣ Nat.card ↥R := by
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
        (show Nat.card ↥R ≠ 1 from fun h => hRne (Subgroup.card_eq_one.mp h))
      have hpmem : p ∈ (Nat.card ↥(R.subgroupOf U)).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, by
          rw [Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe hRU).toEquiv]; exact hpd, Nat.card_pos.ne'⟩
      exact (Set.mem_singleton_iff.mp (hR.1 p hpmem)) ▸ hpd
    -- If `H` were conjugate to `M*`, then `K ≤ H` and `sK_uniqMst` force `H = M*`, so
    -- `R ≤ M ⊓ M* = Z`, whence `r ∣ |Z|`, contradicting `r ∤ |Z|`.
    rintro ⟨a, ha⟩
    have hHeq : H = MulAut.conj a⁻¹ • Mst := by
      rw [← ha, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    have haInvMst : a⁻¹ ∈ Mst := hsKuniq a⁻¹ (hHeq ▸ hKH)
    have hHMst : H = Mst := hHeq.trans (Subgroup.conj_smul_eq_self_of_mem haInvMst)
    have hRZ : R ≤ K ⊔ Kstar := hziMMst ▸ le_inf hRM (hHMst ▸ hRH)
    exact hrnZ (hrR.trans (Subgroup.card_dvd_of_le hRZ))
  -- ═══ Shared σ-decomposition infrastructure for conjuncts 2/3/4 (Coq `P2type_signalizer`) ═══
  -- Conjunct 1 (`IsTypeF H`), hoisted (also the `hF` input to Lemma 14.11 below): every type-`P`
  -- maximal is conjugate to `M` or `M*` (`hcover`), and `H` is conjugate to neither.
  have hFmaxH : IsTypeF H := by
    change kappa H = ∅
    rw [← Set.not_nonempty_iff_eq_empty]
    intro hHP
    exact (hcover H hHmax hHP).elim notMGH notMstGH
  -- `|K| = q` is prime (Prop 14.2(g), type-`P₂`), so `K` is cyclic of prime order.
  obtain ⟨-, -, -, -, hP2struct, -, -⟩ := typeP_structure hG hM hP hKM hK hKstardef hU
  obtain ⟨-, q, hqprime, hKcard, -⟩ := hP2struct hP2
  have : Fact q.Prime := ⟨hqprime⟩
  have hKcyc : IsCyclic ↥K := isCyclic_of_prime_card hKcard
  have hKelemq : K ∈ elemAbelianOfRank G q 1 :=
    mem_elemAbelianOfRank.mpr
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hKcard, by rw [hKcard, pow_one]⟩
  -- `defUK : ⁅U, K⁆ = U` (BG `defUK`).
  have defUK : (⁅U, K⁆ : Subgroup G) = U :=
    typeP2_kappaHall_commutator_eq_self hG hM hP2 hKM hUM hK hKstardef hU hUab hKNU
  -- `K ≤ M*_σ` and `K` is a `σ(H)'`-group (Thm 13.9: `σ(H) ∩ σ(M*) = ∅`, `H` not conj. to `M*`).
  have hKMsigmaMst : K ≤ OddOrder.BG.Ch3.S10.Msigma Mst := hMstpair.2.2.le.trans inf_le_left
  have hHMstdisj : Disjoint (OddOrder.BG.Ch3.S10.sigma H) (OddOrder.BG.Ch3.S10.sigma Mst) :=
    sigma_disjoint_of_nonconjugate hG hHmax hMstmax notMstGH
  have hsH_K : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma H)ᶜ K := by
    intro p hp
    rw [Set.mem_compl_iff]
    intro hpσH
    exact (Set.disjoint_left.mp hHMstdisj) hpσH
      (OddOrder.BG.Ch3.S10.Msigma_isPiGroup Mst p
        (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hKMsigmaMst) Nat.card_pos.ne' hp))
  -- `E`: a `σ(H)'`-Hall (E-setup) complement of `H_σ` in `H`, containing `K` (`Hall_superset`).
  obtain ⟨E, E₁, E₂, E₃, hEsetup, hKE, hE_pi⟩ :=
    OddOrder.BG.Ch3.S12.exists_subgroupESetup_with_le hG hHmax hKH hsH_K
  -- `q = |K| ∈ σ(M*)` (`K ≤ M*_σ`).
  have hqσMst : q ∈ OddOrder.BG.Ch3.S10.sigma Mst :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup Mst q
      (Nat.mem_primeFactors.mpr ⟨hqprime, hKcard ▸ Subgroup.card_dvd_of_le hKMsigmaMst,
        Nat.card_pos.ne'⟩)
  -- `𝓜(C(K)) = {Mst}` (Prop 14.2(d) for `Mst`, whose dual `K*` is `K`): `typeP_structure`
  -- conjunct 6 with the rank-one `K ∈ ℰ_q¹`.
  have huniqMst : maximalSubgroupsContaining (Subgroup.centralizer (K : Set G)) = {Mst} := by
    have hMstsol : Group.IsSolvable ↥Mst := hG.isSolvable_of_mem_maximalSubgroups hMstmax
    obtain ⟨UMst, hUMsthall⟩ : ∃ UMst : Subgroup G, Ch03.IsHallSubgroup
        ((kappa Mst ∪ OddOrder.BG.Ch3.S10.sigma Mst)ᶜ) (UMst.subgroupOf Mst) := by
      obtain ⟨U', hU'hall, -⟩ := Ch03.hall_D (G := ↥Mst)
        (π := (kappa Mst ∪ OddOrder.BG.Ch3.S10.sigma Mst)ᶜ) (U := (⊥ : Subgroup ↥Mst))
        (fun p hp => by simp at hp)
      have hUeq : (U'.map Mst.subtype).subgroupOf Mst = U' :=
        Subgroup.comap_map_eq_self_of_injective Mst.subtype_injective U'
      exact ⟨U'.map Mst.subtype, by rw [hUeq]; exact hU'hall⟩
    exact (typeP_structure hG hMstmax hMstP hMstpair.1 hMstpair.2.1 hMstpair.2.2
      hUMsthall).2.2.2.2.2.1 q hqprime K hKelemq le_rfl
  -- `K ⊆ F(E)` (Coq `sK_FD`): otherwise Lemma 14.11 (`exists_maximal_of_typeF_notMem_fitting`)
  -- produces a maximal `M'` with `q ∈ τ₂(M')` and `𝓜(C(K)) = {M'}` (⟹ `M' = Mst`, but
  -- `q ∈ τ₂(Mst) ∩ σ(Mst) = ∅`), or `q ∈ κ(M')` with `M'` type-`P₁` (⟹ `M' ∼ M` makes `M`
  -- type-`P₁` against `M ∈ 𝓜_{P₂}`, or `M' ∼ Mst` gives `q ∈ κ(Mst) ⊆ σ(Mst)ᶜ`).
  have hsK_FE : K ≤ OddOrder.BG.Ch2.S08.fittingInG E := by
    by_contra hnotKFE
    have hqpiE : q ∈ piSet E :=
      Nat.mem_primeFactors.mpr ⟨hqprime, hKcard ▸ Subgroup.card_dvd_of_le hKE, Nat.card_pos.ne'⟩
    obtain ⟨Mstar', hMstar'max, hdich⟩ := exists_maximal_of_typeF_notMem_fitting hG hHmax hFmaxH
      hEsetup.isComplement'_subgroupOf hEsetup.E_le hqpiE hKelemq hKE hnotKFE
    rcases hdich with ⟨hqτ2, huniq'⟩ | ⟨hqκ', hP1'⟩
    · -- Case 1: `Mstar' = Mst` (both `= 𝓜(C(K))`), but `q ∈ τ₂(Mst)` and `q ∈ σ(Mst)`.
      have hMstar'eq : Mstar' = Mst :=
        Set.singleton_eq_singleton_iff.mp (huniq'.symm.trans huniqMst)
      exact tau2_subset_sigma_compl Mst (hMstar'eq ▸ hqτ2) hqσMst
    · -- Case 2: `Mstar'` type-`P₁`; `hcover` makes it conjugate to `M` or `Mst`.
      rcases hcover Mstar' hMstar'max hP1'.1 with ⟨b, hb⟩ | ⟨b, hb⟩
      · exact not_isTypeP1_and_isTypeP2 ⟨hb ▸ (isTypeP1_conj_smul b Mstar').mpr hP1', hP2⟩
      · refine kappa_subset_sigmaCompl (M := Mst) ?_ hqσMst
        rw [← hb, kappa_conj_smul]; exact hqκ'
  -- ═══ Conjunct 2 (`U ≤ M_σ(H)`, Coq `sUHs`), hoisted: also feeds `U ⊆ F(H)` for conjuncts 3/4 ═══
  -- `U = ⁅U,K⁆ ≤ HsDq := M_σ(H) ⊔ O_q(F(E))`, and `M_σ(H)` is the normal `{q}'`-Hall of `HsDq`.
  have hUMsH : U ≤ OddOrder.BG.Ch3.S10.Msigma H := by
    classical
    -- `q ∈ κ(M)`, `q ∉ σ(H)`, and `|U|` is a `{q}'`-number.
    have hqκM : q ∈ kappa M := hK.1 q (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv, hKcard]
      exact Nat.mem_primeFactors.mpr ⟨hqprime, dvd_rfl, hqprime.pos.ne'⟩)
    have hqσ'H : q ∉ OddOrder.BG.Ch3.S10.sigma H :=
      hsH_K q (by rw [hKcard]; exact Nat.mem_primeFactors.mpr ⟨hqprime, dvd_rfl, hqprime.pos.ne'⟩)
    have hUq' : ∀ p ∈ (Nat.card ↥U).primeFactors, p ∈ ({q}ᶜ : Set ℕ) := by
      intro p hp hpq
      exact hU.1 p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv])
        (Or.inl ((Set.mem_singleton_iff.mp hpq) ▸ hqκM))
    -- `O_q(F(E))`, `K ≤ O_q(F(E))`, `E ≤ N(O_q(F(E)))`.
    set Oq : Subgroup G := opiCoreInG ({q} : Set ℕ)
      (OddOrder.BG.Ch2.S08.fittingInG E) with hOqdef
    have hOqE : Oq ≤ E := (opiCoreInG_le _ _).trans
      (OddOrder.BG.Ch2.S08.fittingInG_le E)
    have hKOq : K ≤ Oq := OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent
      (OddOrder.BG.Ch2.S08.fittingInG_isNilpotent E) hsK_FE
        (IsPGroup.of_card (by rw [hKcard, pow_one]))
    have hOqpi : Subgroup.IsPiSubgroup ({q} : Set ℕ) Oq :=
      isPiSubgroup_opiCoreInG _ _
    have hEnOq : E ≤ Subgroup.normalizer (Oq : Set G) := by
      rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hOqE]
      exact OddOrder.BG.Ch2.S08.opiCoreInG_fittingInG_subgroupOf_normal _ _
    -- `HsDq := M_σ(H) ⊔ O_q(F(E))`; `M_σ(H) ◁ H`, `HsDq ≤ H`, `H ≤ N(HsDq)`.
    set HsDq : Subgroup G := OddOrder.BG.Ch3.S10.Msigma H ⊔ Oq with hHsDqdef
    have hHsDqH : HsDq ≤ H := sup_le (OddOrder.BG.Ch3.S10.Msigma_le H) (hOqE.trans hEsetup.E_le)
    have hMsHnorm : ((OddOrder.BG.Ch3.S10.Msigma H).subgroupOf H).Normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    have hHnMsH : H ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (OddOrder.BG.Ch3.S10.Msigma_le H)).mp hMsHnorm
    have hHnHsDq : H ≤ Subgroup.normalizer (HsDq : Set G) := by
      calc H = OddOrder.BG.Ch3.S10.Msigma H ⊔ E := hEsetup.E_compl_sup.symm
        _ ≤ Subgroup.normalizer (HsDq : Set G) :=
          sup_le (le_sup_left.trans Subgroup.le_normalizer)
            (le_normalizer_sup (hEsetup.E_le.trans hHnMsH) hEnOq)
    -- `U = ⁅U,K⁆ ≤ ⁅H, HsDq⁆ ≤ HsDq` (since `HsDq ◁ H`).
    have hUHsDq : U ≤ HsDq := by
      rw [← defUK]
      refine (Subgroup.commutator_mono hUH (hKOq.trans (le_sup_right : Oq ≤ HsDq))).trans ?_
      rw [Subgroup.commutator_comm H HsDq]
      exact Ch04.commutator_le_of_le_normalizer hHnHsDq
    -- `M_σ(H) ⊓ Oq = ⊥` (`σ(H)` vs `{q}`, `q ∉ σ(H)`), so `|HsDq| = |M_σ(H)|·|Oq|`.
    have hMsOqbot : OddOrder.BG.Ch3.S10.Msigma H ⊓ Oq = ⊥ := by
      apply Disjoint.eq_bot
      apply Subgroup.disjoint_of_coprime_natCard
      refine Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl (π := OddOrder.BG.Ch3.S10.sigma H)
        Nat.card_pos.ne' Nat.card_pos.ne' (fun p hp => OddOrder.BG.Ch3.S10.Msigma_isPiGroup H p hp)
        (fun p hp hpσ => ?_)
      exact hqσ'H ((Set.mem_singleton_iff.mp (hOqpi p hp)) ▸ hpσ)
    have hcardHsDq : Nat.card ↥HsDq = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma H) * Nat.card ↥Oq := by
      have hOqnMs : Oq ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma H : Set G) :=
        (hOqE.trans hEsetup.E_le).trans hHnMsH
      have h := card_sup_eq_mul_of_le_normalizer_of_disjoint hOqnMs
        (by rw [inf_comm]; exact hMsOqbot)
      rw [hHsDqdef, sup_comm, h, Nat.mul_comm]
    -- `M_σ(H)` is the normal `{q}'`-Hall of `HsDq`.
    have hMsHsDqnorm : ((OddOrder.BG.Ch3.S10.Msigma H).subgroupOf HsDq).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (hHsDqH.trans hHnMsH)
    have hidxOq : ((OddOrder.BG.Ch3.S10.Msigma H).subgroupOf HsDq).index = Nat.card ↥Oq := by
      have hlag := Subgroup.card_mul_index ((OddOrder.BG.Ch3.S10.Msigma H).subgroupOf HsDq)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left :
        OddOrder.BG.Ch3.S10.Msigma H ≤ HsDq)).toEquiv, hcardHsDq] at hlag
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hlag
    have hMsHall : Ch03.IsHallSubgroup ({q}ᶜ : Set ℕ)
        ((OddOrder.BG.Ch3.S10.Msigma H).subgroupOf HsDq) := by
      refine ⟨fun p hp => ?_, fun p hp => ?_⟩
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left :
          OddOrder.BG.Ch3.S10.Msigma H ≤ HsDq)).toEquiv] at hp
        exact fun hpq => hqσ'H ((Set.mem_singleton_iff.mp hpq) ▸
          OddOrder.BG.Ch3.S10.Msigma_isPiGroup H p hp)
      · rw [hidxOq] at hp
        exact fun hpc => hpc (hOqpi p hp)
    have hUpi : Ch03.Subgroup.IsPiGroup ({q}ᶜ : Set ℕ) (U.subgroupOf HsDq) := by
      intro p hp
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUHsDq).toEquiv] at hp
      exact hUq' p hp
    have hfinal := OddOrder.BG.Ch3.S10.isPiGroup_le_of_normal_isHallSubgroup hMsHall hUpi
    have hmapped := Subgroup.map_mono (f := HsDq.subtype) hfinal
    rwa [Subgroup.map_subgroupOf_eq_of_le hUHsDq, Subgroup.map_subgroupOf_eq_of_le
      (le_sup_left : OddOrder.BG.Ch3.S10.Msigma H ≤ HsDq)] at hmapped
  -- ═══ Shared structure for conjuncts 3/4: `H_σ ⊆ F(H)` and `Fu = O_{(κ∪σ)'(M)}(F(H))` ═══
  -- `q ∉ σ(H)` (`K` is a `σ(H)'`-group, `q ∣ |K|`) and `q ∈ π(H)` (`K ≤ H`, `|K| = q`).
  have hqσ'H : q ∉ OddOrder.BG.Ch3.S10.sigma H :=
    hsH_K q (by rw [hKcard]; exact Nat.mem_primeFactors.mpr ⟨hqprime, dvd_rfl, hqprime.pos.ne'⟩)
  have hqπH : q ∈ piSet H :=
    Nat.mem_primeFactors.mpr ⟨hqprime, hKcard ▸ Subgroup.card_dvd_of_le hKH, Nat.card_pos.ne'⟩
  -- `H_σ ⊆ F(H)` (Coq `sHsFH`): `H` is type-`F`, so `q ∉ κ(H) = ∅`; Lemma 14.1
  -- (`msigma_structure_of_notMem_sigma_kappa`) with a maximal-rank elementary abelian `q`-subgroup
  -- of `H` makes `M_σ(H)` nilpotent, hence `≤ F(H)`.
  have hHsFH : OddOrder.BG.Ch3.S10.Msigma H ≤ OddOrder.BG.Ch2.S08.fittingInG H := by
    have hκH : kappa H = ∅ := hFmaxH
    have hqκH : q ∉ kappa H := by rw [hκH]; exact Set.notMem_empty q
    obtain ⟨B, hBea, hBlog⟩ := exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
      (G := ↥H) (p := q) (n := pRank ↥H q)
      (OddOrder.BG.Ch3.S12.one_le_pRank_of_mem_primeFactors hqπH) (le_refl _)
    obtain ⟨j, hj⟩ := hBea.isPGroup.exists_card_eq
    have hjeq : j = pRank ↥H q := by
      have hsq := le_antisymm (le_pRank B hBea) hBlog
      rwa [hj, Nat.log_pow hqprime.one_lt] at hsq
    have hAmem : B.map H.subtype ∈ elemAbelianOfRank G q (pRank ↥H q) :=
      ⟨Subgroup.IsElementaryAbelian.map H.subtype_injective hBea, by
        rw [Subgroup.card_map_of_injective H.subtype_injective, hj, hjeq]⟩
    have hAH : B.map H.subtype ≤ H := Subgroup.map_subtype_le _
    have h1 : ((OddOrder.BG.Ch3.S10.Msigma H).subgroupOf H).Normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    have h2 : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma H) :=
      (msigma_structure_of_notMem_sigma_kappa hG hHmax hqπH hqσ'H hqκH hAmem hAH).2.2
    have h3 : Group.IsNilpotent ↥((OddOrder.BG.Ch3.S10.Msigma H).subgroupOf H) :=
      Group.nilpotent_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch3.S10.Msigma_le H)).symm
    have h4 : (OddOrder.BG.Ch3.S10.Msigma H).subgroupOf H ≤ OddOrder.Isaacs.Ch01.fitting ↥H :=
      OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
    calc OddOrder.BG.Ch3.S10.Msigma H
        = ((OddOrder.BG.Ch3.S10.Msigma H).subgroupOf H).map H.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le (OddOrder.BG.Ch3.S10.Msigma_le H)).symm
      _ ≤ (OddOrder.Isaacs.Ch01.fitting ↥H).map H.subtype := Subgroup.map_mono h4
      _ = OddOrder.BG.Ch2.S08.fittingInG H := rfl
  -- `Fu := O_{(κ(M)∪σ(M))'}(F(H))`: normal in `H`, contains `U`, and `M ⊓ Fu = U` (Coq `defU`).
  set π : Set ℕ := (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ with hπdef
  set Fu : Subgroup G := opiCoreInG π (OddOrder.BG.Ch2.S08.fittingInG H) with hFudef
  have hFHnil : Group.IsNilpotent ↥(OddOrder.BG.Ch2.S08.fittingInG H) :=
    OddOrder.BG.Ch2.S08.fittingInG_isNilpotent H
  have hUFH : U ≤ OddOrder.BG.Ch2.S08.fittingInG H := hUMsH.trans hHsFH
  have hUπ : Ch03.Subgroup.IsPiGroup π U := by
    intro p hp
    exact hU.1 p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv])
  have hUFu : U ≤ Fu := by
    have hUFHpi : Ch03.Subgroup.IsPiGroup π (U.subgroupOf (OddOrder.BG.Ch2.S08.fittingInG H)) :=
      Ch03.Subgroup.IsPiGroup.subgroupOf hUFH hUπ
    have hHall : Ch03.IsHallSubgroup π
        (Ch03.oPiCore π ↥(OddOrder.BG.Ch2.S08.fittingInG H)) :=
      OddOrder.BG.Ch3.S10.oPiCore_isHall_of_isNilpotent _
    have hle : U.subgroupOf (OddOrder.BG.Ch2.S08.fittingInG H) ≤
        Ch03.oPiCore π ↥(OddOrder.BG.Ch2.S08.fittingInG H) :=
      OddOrder.BG.Ch3.S10.isPiGroup_le_of_normal_isHallSubgroup hHall hUFHpi
    calc U = (U.subgroupOf (OddOrder.BG.Ch2.S08.fittingInG H)).map
              (OddOrder.BG.Ch2.S08.fittingInG H).subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hUFH).symm
      _ ≤ (Ch03.oPiCore π ↥(OddOrder.BG.Ch2.S08.fittingInG H)).map
              (OddOrder.BG.Ch2.S08.fittingInG H).subtype := Subgroup.map_mono hle
      _ = Fu := rfl
  have hFuH : Fu ≤ H :=
    (opiCoreInG_le _ _).trans (OddOrder.BG.Ch2.S08.fittingInG_le H)
  have hHnFu : H ≤ Subgroup.normalizer (Fu : Set G) := by
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hFuH]
    exact OddOrder.BG.Ch2.S08.opiCoreInG_fittingInG_subgroupOf_normal π H
  have hdefU : M ⊓ Fu = U := by
    refine le_antisymm ?_ (le_inf hUM hUFu)
    -- `V := M ⊓ Fu` is a `π`-subgroup of `M` containing the `π`-Hall `U`, so `V = U` (cardinality).
    have hVπ : ∀ p ∈ (Nat.card ↥(M ⊓ Fu)).primeFactors, p ∈ π := by
      intro p hp
      exact (isPiSubgroup_opiCoreInG _ (OddOrder.BG.Ch2.S08.fittingInG H)) p
        (Nat.primeFactors_mono (Subgroup.card_dvd_of_le inf_le_right) Nat.card_pos.ne' hp)
    have hlag : Nat.card ↥U * (U.subgroupOf M).index = Nat.card ↥M := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv]
      exact Subgroup.card_mul_index _
    have hcop : Nat.Coprime (Nat.card ↥(M ⊓ Fu)) (U.subgroupOf M).index := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
      rw [Nat.dvd_gcd_iff] at hpd
      exact (hU.2 p (Nat.mem_primeFactors.mpr ⟨hp, hpd.2, Subgroup.index_ne_zero_of_finite⟩))
        (hVπ p (Nat.mem_primeFactors.mpr ⟨hp, hpd.1, Nat.card_pos.ne'⟩))
    have hVdvdU : Nat.card ↥(M ⊓ Fu) ∣ Nat.card ↥U :=
      hcop.dvd_of_dvd_mul_right (hlag ▸ Subgroup.card_dvd_of_le inf_le_left)
    exact (Subgroup.eq_of_le_of_card_ge (le_inf hUM hUFu)
      (Nat.le_of_dvd Nat.card_pos hVdvdU)).symm.le
  refine ⟨hFmaxH, hUMsH, ?_, ?_, E, E₁, E₂, E₃, hEsetup, hKE, hsK_FE⟩
  · -- Conjunct 3 (`M ⊓ H = U ⊔ K`, Coq L2375-2380): `⊇` is immediate; `⊆` is
    -- `M ⊓ H ⊆ N_M(U) = U ⊔ K` (`defNMU`, BG 6.5(b): `M = M_σ ⋊ (U⊔K)`, `C_{M_σ}(U) = 1`).
    classical
    refine le_antisymm ?_ (sup_le (le_inf hUM hUH) (le_inf hKM hKH))
    -- σ-decomposition `M = M_σ ⊔ (U ⊔ K)`: the σ-Hall `M_σ`, the κ-Hall `K`, and the
    -- `(κ∪σ)'`-Hall `U` cover all primes, so the index of their join in `M` has no prime divisor.
    have hMσHall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M)
        ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) :=
      OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall_of_isHall
        (OddOrder.BG.Ch3.S10.Msigma_isHall hG hM)
    have hJleM : OddOrder.BG.Ch3.S10.Msigma M ⊔ (U ⊔ K) ≤ M :=
      sup_le (OddOrder.BG.Ch3.S10.Msigma_le M) (sup_le hUM hKM)
    have hJM : OddOrder.BG.Ch3.S10.Msigma M ⊔ (U ⊔ K) = M := by
      have hidx1 : ((OddOrder.BG.Ch3.S10.Msigma M ⊔ (U ⊔ K)).subgroupOf M).index = 1 := by
        by_contra hne
        obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
        have hsub : ∀ S : Subgroup G, S ≤ OddOrder.BG.Ch3.S10.Msigma M ⊔ (U ⊔ K) →
            p ∈ (S.subgroupOf M).index.primeFactors := by
          intro S hSJ
          refine Nat.mem_primeFactors.mpr ⟨hp, ?_, Subgroup.index_ne_zero_of_finite⟩
          exact hpdvd.trans (Subgroup.index_dvd_of_le (Subgroup.subgroupOf_mono M hSJ))
        have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M :=
          hMσHall.2 p (hsub _ le_sup_left)
        have hpκσc : p ∉ (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
          hU.2 p (hsub _ (le_sup_right.trans' le_sup_left))
        have hpκ : p ∉ kappa M := hK.2 p (hsub _ (le_sup_right.trans' le_sup_right))
        exact hpκσc (Set.mem_compl (fun h => h.elim hpκ hpσ))
      have htop : (OddOrder.BG.Ch3.S10.Msigma M ⊔ (U ⊔ K)).subgroupOf M = ⊤ :=
        Subgroup.index_eq_one.mp hidx1
      exact le_antisymm hJleM (Subgroup.subgroupOf_eq_top.mp htop)
    -- `C_{M_σ}(U) = ⊥` (Lemma 14.1): `R` is a Sylow `r`-subgroup of `M` (`r ∈ (κ∪σ)'`, `U` Hall),
    -- so a maximal-rank elementary abelian `A ≤ R ≤ U` makes `M_σ ⊓ C(A) = ⊥`; antitonicity lifts
    -- this to `M_σ ⊓ C(U) ≤ M_σ ⊓ C(A) = ⊥`.
    have hRM : R ≤ M := hRU.trans hUM
    have hrπM : r ∈ piSet M :=
      Nat.mem_primeFactors.mpr ⟨hrprime,
        (Nat.dvd_of_mem_primeFactors hr).trans (Subgroup.card_dvd_of_le hUM), Nat.card_pos.ne'⟩
    have hCMsU : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (U : Set G) = ⊥ := by
      have hSU : Nat.card ↥(R.subgroupOf U) = Nat.card ↥R :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRU).toEquiv
      have hRpow : Nat.card ↥R = r ^ (Nat.card ↥R).factorization r := by
        apply Nat.eq_pow_of_factorization_eq_single Nat.card_pos.ne'
        apply Finsupp.ext; intro q; rw [Finsupp.single_apply]
        by_cases hq : r = q
        · rw [if_pos hq, hq]
        · rw [if_neg hq]
          by_cases hqp : q.Prime
          · refine Nat.factorization_eq_zero_of_not_dvd (fun hdvd => hq ?_)
            exact (Set.mem_singleton_iff.mp (hR.1 q (Nat.mem_primeFactors.mpr
              ⟨hqp, hSU ▸ hdvd, Nat.card_pos.ne'⟩))).symm
          · exact Nat.factorization_eq_zero_of_not_prime _ hqp
      have hfUR : (Nat.card ↥U).factorization r = (Nat.card ↥R).factorization r := by
        have hidxU : (R.subgroupOf U).index.factorization r = 0 :=
          Nat.factorization_eq_zero_of_not_dvd (fun hdvd =>
            hR.2 r (Nat.mem_primeFactors.mpr ⟨hrprime, hdvd, Subgroup.index_ne_zero_of_finite⟩) rfl)
        have hlag := Subgroup.card_mul_index (R.subgroupOf U)
        rw [← hlag, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
          Finsupp.add_apply, hidxU, add_zero, hSU]
      have hfUM : (Nat.card ↥U).factorization r = (Nat.card ↥M).factorization r := by
        have hidxM : (U.subgroupOf M).index.factorization r = 0 :=
          Nat.factorization_eq_zero_of_not_dvd (fun hdvd =>
            hU.2 r (Nat.mem_primeFactors.mpr ⟨hrprime, hdvd, Subgroup.index_ne_zero_of_finite⟩)
              hrκσ)
        have hUcard : Nat.card ↥(U.subgroupOf M) = Nat.card ↥U :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv
        have hlag := Subgroup.card_mul_index (U.subgroupOf M)
        rw [← hlag, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
          Finsupp.add_apply, hidxM, add_zero, hUcard]
      have hRsylM : Nat.card ↥(R.subgroupOf M) = r ^ (Nat.card ↥M).factorization r := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv, hRpow, ← hfUR, hfUM]
      have hpRankRM : pRank ↥R r = pRank ↥M r := by
        have h1 : pRank ↥(R.subgroupOf M) r = pRank ↥M r := by
          have := pRank_sylow_eq (Sylow.ofCard (R.subgroupOf M) hRsylM)
          rwa [Sylow.coe_ofCard] at this
        rw [← h1]; exact pRank_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hRM).symm r
      have hRrankpos : 0 < pRank ↥R r := by
        rw [hpRankRM]; exact OddOrder.BG.Ch3.S12.one_le_pRank_of_mem_primeFactors hrπM
      obtain ⟨B, hBea, hBlog⟩ := exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
        (G := ↥R) (p := r) (n := pRank ↥R r) hRrankpos (le_refl _)
      obtain ⟨j, hj⟩ := hBea.isPGroup.exists_card_eq
      have hjeq : j = pRank ↥R r := by
        have hsq := le_antisymm (le_pRank B hBea) hBlog
        rwa [hj, Nat.log_pow hrprime.one_lt] at hsq
      have hAR : B.map R.subtype ≤ R := Subgroup.map_subtype_le _
      have hAmem : B.map R.subtype ∈ elemAbelianOfRank G r (pRank ↥M r) :=
        ⟨Subgroup.IsElementaryAbelian.map R.subtype_injective hBea, by
          rw [Subgroup.card_map_of_injective R.subtype_injective, hj, hjeq, hpRankRM]⟩
      have hrκ : r ∉ kappa M := fun h => hrκσ (Or.inl h)
      exact (msigma_centralizer_eq_bot_of_elemAb_le hG hM hrπM hrσM hrκ hAmem
        (hAR.trans hRM) (hAR.trans hRU)).1
    -- `M ⊓ H ⊆ N_M(U)` (geometric: `M ⊓ H ≤ N(M) ⊓ N(Fu) ≤ N(M ⊓ Fu) = N(U)`).
    have hMHnU : M ⊓ H ≤ Subgroup.normalizer (U : Set G) := by
      rw [← hdefU]
      exact le_normalizer_inf (inf_le_left.trans Subgroup.le_normalizer)
        (inf_le_right.trans hHnFu)
    -- `defNMU`: BG 6.5(b) in `↥M` gives `N_{↥M}(U) = (C(U) ⊓ M_σ) · (N(U) ⊓ (U⊔K))`; the
    -- first factor is `C_{M_σ}(U) = 1`, so every `n ∈ N_M(U)` lies in `U ⊔ K`.
    have hKU : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M ⊔ (U ⊔ K).subgroupOf M = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (OddOrder.BG.Ch3.S10.Msigma_le M) (sup_le hUM hKM), hJM,
        Subgroup.subgroupOf_self]
    have hcop : Nat.Coprime (Nat.card ↥(U.subgroupOf M))
        (Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)) := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
      rw [Nat.dvd_gcd_iff] at hpd
      have hpU : p ∈ (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
        hU.1 p (Nat.mem_primeFactors.mpr ⟨hp, hpd.1, Nat.card_pos.ne'⟩)
      refine hpU (Or.inr (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p ?_))
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch3.S10.Msigma_le M)).toEquiv]
      exact Nat.mem_primeFactors.mpr ⟨hp, hpd.2, Nat.card_pos.ne'⟩
    have hMsol : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
    have hMσMnorm : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    have hlem := OddOrder.BG.Ch1.S06.normalizer_eq_centralizerK_mul_normalizerU (G := ↥M)
      (K := (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (U := (U ⊔ K).subgroupOf M)
      (H := U.subgroupOf M) hKU (Subgroup.subgroupOf_mono M le_sup_left) hcop
    -- The first factor `C(U) ⊓ M_σ` is trivial in `↥M` (`C_{M_σ}(U) = 1`).
    have hfactor1 : Subgroup.centralizer ((U.subgroupOf M : Subgroup ↥M) : Set ↥M) ⊓
        (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M = ⊥ := by
      rw [eq_bot_iff]
      intro c hc
      rw [Subgroup.mem_inf] at hc
      have hcCU : (M.subtype c) ∈ Subgroup.centralizer (U : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro u huU
        have hcomm := (Subgroup.mem_centralizer_iff.mp hc.1) (⟨u, hUM huU⟩ : ↥M)
          (Subgroup.mem_subgroupOf.mpr huU)
        have := congrArg (M.subtype) hcomm
        simpa using this
      have hmem : (M.subtype c) ∈ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (U : Set G) :=
        ⟨Subgroup.mem_subgroupOf.mp hc.2, hcCU⟩
      rw [hCMsU, Subgroup.mem_bot] at hmem
      rw [Subgroup.mem_bot]
      exact M.subtype_injective (by rw [hmem, map_one])
    -- Conclude: `M ⊓ H ⊆ M ⊓ N_G(U)`, and each such `n` lies in `U ⊔ K`.
    refine le_trans (le_inf inf_le_left hMHnU) ?_
    intro n hn
    rw [Subgroup.mem_inf] at hn
    obtain ⟨hnM, hnNU⟩ := hn
    have hnbar : (⟨n, hnM⟩ : ↥M) ∈ Subgroup.normalizer (U.subgroupOf M) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hUM, Subgroup.mem_subgroupOf]; exact hnNU
    have hnbarc := SetLike.mem_coe.mpr hnbar
    rw [hlem] at hnbarc
    obtain ⟨c, hc, u, hu, hcu⟩ := Set.mem_mul.mp hnbarc
    have hc1 : c = 1 :=
      Subgroup.mem_bot.mp (hfactor1 ▸ SetLike.mem_coe.mp hc)
    rw [hc1, one_mul] at hcu
    rw [SetLike.mem_coe, Subgroup.mem_inf] at hu
    have hnUK : (M.subtype u) ∈ U ⊔ K := Subgroup.mem_subgroupOf.mp hu.2
    rw [hcu] at hnUK
    simpa using hnUK
  · -- Conjunct 4 (`N_H(U) ⊄ M`): suppose `N_H(U) = H ⊓ N_G(U) ≤ M`.  Then `N_Fu(U) = N_G(U) ⊓ Fu`
    -- lies in `M ⊓ Fu = U`, so `U` is self-normalizing in the nilpotent `Fu`, forcing `Fu = U`.
    -- Hence `H ≤ N_G(Fu) = N_G(U)`, so `H = H ⊓ N_G(U) ≤ M`, whence `H = M` (both maximal),
    -- contradicting `H` not conjugate to `M`.
    intro hNHU_M
    have hNFuU : Subgroup.normalizer (U : Set G) ⊓ Fu ≤ U := by
      have h1 : Subgroup.normalizer (U : Set G) ⊓ Fu ≤ M :=
        le_trans (le_inf (le_trans inf_le_right hFuH) inf_le_left) hNHU_M
      calc Subgroup.normalizer (U : Set G) ⊓ Fu ≤ M ⊓ Fu := le_inf h1 inf_le_right
        _ = U := hdefU
    have hFunil : Group.IsNilpotent ↥Fu :=
      Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe
        (opiCoreInG_le π (OddOrder.BG.Ch2.S08.fittingInG H)))
    have hFuU : Fu = U := eq_of_isNilpotent_normalizer_inf_le hFunil hUFu hNFuU
    have hHnU : H ≤ Subgroup.normalizer (U : Set G) := hFuU ▸ hHnFu
    have hHM : H ≤ M := le_trans (le_inf le_rfl hHnU) hNHU_M
    have hHeqM : H = M := by
      rcases lt_or_eq_of_le hHM with hlt | heq
      · exact absurd ((mem_maximalSubgroups.mp hHmax).2 M hlt) (mem_maximalSubgroups.mp hM).1
      · exact heq
    exact notMGH (by rw [hHeqM])

/-- **BG Corollary 14.12** (mmd L4230), existential form.  For a type-`P₂` maximal `M` with
`κ`-complement `K` and abelian Hall `(κ ∪ σ)′`-factor `U`, and a Sylow `r`-subgroup `R ≤ U`,
there is a maximal `H ⊇ N_G(R)` that is type-`F`, with `U ≤ H_σ`, `M ⊓ H = U ⊔ K`, and
`N_H(U) ⊄ M`.

Convenience wrapper over `typeP2_neighbor_is_typeF_of_mem`: it picks `H` as a maximal overgroup
of `N_G(R)` (via `eq_top_or_exists_le_coatom`) and drops the `E`-setup export.  Consumers needing
the σ(H)′-Hall `E` / `K ⊆ F(E)` clauses (Theorem 15.8) call `_of_mem` with their own `H`. -/
theorem typeP2_neighbor_is_typeF [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U R : Subgroup G} {r : ℕ} (hM : M ∈ maximalSubgroups G) (hP2 : IsTypeP2 M)
    (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hr : r ∈ piSet U) (hRU : R ≤ U)
    (hR : Ch03.IsHallSubgroup ({r} : Set ℕ) (R.subgroupOf U))
    (hKNU : K ≤ Subgroup.normalizer (U : Set G)) :
    ∃ H : Subgroup G,
      H ∈ maximalSubgroupsContaining (Subgroup.normalizer (R : Set G)) ∧
      IsTypeF H ∧ U ≤ OddOrder.BG.Ch3.S10.Msigma H ∧ M ⊓ H = U ⊔ K ∧
      ¬ ((H ⊓ Subgroup.normalizer (U : Set G) : Subgroup G) ≤ M) := by
  classical
  have : Fact r.Prime := ⟨Nat.prime_of_mem_primeFactors hr⟩
  have hrprime : r.Prime := Fact.out
  have hRM : R ≤ M := hRU.trans hUM
  -- `R ≠ ⊥`: `r ∣ |U|` and (Hall) `r ∤ [U : R]`, so `r ∣ |R|`.
  have hRne : R ≠ ⊥ := by
    have hlag : Nat.card ↥(R.subgroupOf U) * (R.subgroupOf U).index = Nat.card ↥U :=
      Subgroup.card_mul_index _
    have hridx : ¬ r ∣ (R.subgroupOf U).index := fun hd =>
      hR.2 r (Nat.mem_primeFactors.mpr ⟨hrprime, hd, Subgroup.index_ne_zero_of_finite⟩) rfl
    have hrSub : r ∣ Nat.card ↥(R.subgroupOf U) :=
      ((Nat.Prime.dvd_mul hrprime).mp
        (by rw [hlag]; exact Nat.dvd_of_mem_primeFactors hr)).resolve_right hridx
    have hrR : r ∣ Nat.card ↥R := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRU).toEquiv] at hrSub
    intro h; rw [h, Subgroup.card_bot] at hrR
    exact hrprime.one_lt.ne' (Nat.eq_one_of_dvd_one hrR ▸ rfl)
  -- `N_G(R) < ⊤` (since `R ≤ M`, `R ≠ ⊥`, `G` simple), so it has a maximal overgroup `H`.
  have hNR_lt : Subgroup.normalizer (R : Set G) < ⊤ :=
    normalizer_lt_top_of_le_of_ne_bot hG hM hRM hRne
  obtain ⟨H, hHcoatom, hNRH⟩ := (eq_top_or_exists_le_coatom _).resolve_left hNR_lt.ne
  have hH : H ∈ maximalSubgroupsContaining (Subgroup.normalizer (R : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨hHcoatom, hNRH⟩
  obtain ⟨hF, hUMsH, hMH, hnorm, -⟩ :=
    typeP2_neighbor_is_typeF_of_mem hG hM hP2 hKM hUM hK hU hUab hr hRU hR hKNU hH
  exact ⟨H, hH, hF, hUMsH, hMH, hnorm⟩

/-- **Coq `snK_sMst` single step**: if `N ⊆ Mstar`, `K ≤ N`, `L` normalizes `N`, and `K` has
the uniqueness property `∀ a, K ≤ Mstar^a → a ∈ Mstar` (Coq `sK_uniqMst`), then `L ⊆ Mstar`.
For `a ∈ L`, `a` normalizes `N`, so `N^{a⁻¹} = N`, whence `K^{a⁻¹} ≤ N^{a⁻¹} = N ⊆ Mstar`,
i.e. `K ≤ Mstar^a`, so `a ∈ Mstar`. -/
theorem le_partner_of_normalizes_of_le_of_uniq {K Mstar N L : Subgroup G}
    (hNMstar : N ≤ Mstar) (hKN : K ≤ N) (hLN : L ≤ Subgroup.normalizer (N : Set G))
    (huniq : ∀ a : G, K ≤ MulAut.conj a • Mstar → a ∈ Mstar) :
    L ≤ Mstar := by
  intro a ha
  -- `a⁻¹` normalizes `N`, so `conj a⁻¹ • N = N`.
  have haN : MulAut.conj a⁻¹ • N = N :=
    OddOrder.GroupTheory.conj_smul_eq_self_of_mem_normalizer
      (Subgroup.inv_mem _ (hLN ha))
  -- `conj a⁻¹ • K ≤ conj a⁻¹ • N = N ≤ Mstar`.
  have hKconj : MulAut.conj a⁻¹ • K ≤ Mstar :=
    (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hKN).trans (haN.le.trans hNMstar)
  -- Rewrite as `K ≤ conj a • Mstar` and apply the uniqueness hypothesis.
  have hKMstar : K ≤ MulAut.conj a • Mstar := by
    have := Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj a).mpr hKconj
    rwa [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul] at this
  exact huniq a hKMstar

/-- **Coq `snK_sMst`** (BGsection14.v:2283): if `K` is *subnormal* in `L` (`K ≤ L`,
`(K.subgroupOf L).IsSubnormal`), `K ≤ Mstar`, and `K` has the uniqueness property
`∀ a, K ≤ Mstar^a → a ∈ Mstar`, then `L ⊆ Mstar`.  Strong induction on `|L|`: if `K = L`,
done; otherwise peel a proper `↥L`-normal overgroup `N̄` of `K.subgroupOf L`
(`exists_normal_and_le_and_lt_top_of_ne`), so `N := N̄.map L.subtype` is a proper subgroup with
`K ≤ N`, `K` subnormal in `N` (restriction), `L ≤ N_G(N)` (`N̄ ◁ ↥L`); the induction hypothesis
gives `N ⊆ Mstar`, and the single-step lemma lifts it to `L ⊆ Mstar`. -/
theorem le_partner_of_subnormal_of_uniq [Finite G] {K Mstar : Subgroup G}
    (huniq : ∀ a : G, K ≤ MulAut.conj a • Mstar → a ∈ Mstar) (hKMstar : K ≤ Mstar) :
    ∀ L : Subgroup G, K ≤ L → (K.subgroupOf L).IsSubnormal → L ≤ Mstar := by
  intro L
  induction hcard : Nat.card ↥L using Nat.strong_induction_on generalizing L with
  | _ n ih =>
    intro hKL hsub
    by_cases hKLtop : K.subgroupOf L = ⊤
    · -- `K = L` (as `K ≤ L`), so `L = K ≤ Mstar`.
      have hLK : L ≤ K := by
        intro x hx
        have hmem : (⟨x, hx⟩ : ↥L) ∈ K.subgroupOf L := by rw [hKLtop]; exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf).mp hmem
      exact hLK.trans hKMstar
    · -- Peel a proper `↥L`-normal overgroup `N̄` of `K.subgroupOf L`.
      obtain ⟨Nbar, hNbarnorm, hKNbar, hNbarlt⟩ :=
        hsub.exists_normal_and_le_and_lt_top_of_ne hKLtop
      have := hNbarnorm
      set N : Subgroup G := Nbar.map L.subtype with hNdef
      have hNL : N ≤ L := Subgroup.map_subtype_le _
      have hNbar_eq : N.subgroupOf L = Nbar :=
        Subgroup.comap_map_eq_self_of_injective L.subtype_injective Nbar
      -- `K ≤ N`.
      have hKN : K ≤ N := by
        have hmm : (K.subgroupOf L).map L.subtype ≤ N := Subgroup.map_mono hKNbar
        rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKL] at hmm
      -- `|N| < |L|` (proper).
      have hNlt : Nat.card ↥N < Nat.card ↥L := by
        have hNbne : N ≠ L := by
          intro h
          apply hNbarlt.ne
          rw [← hNbar_eq, h, Subgroup.subgroupOf_self]
        refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hNL))
          (fun heq => hNbne (Subgroup.eq_of_le_of_card_ge hNL heq.ge))
      -- `K` subnormal in `N` (restrict the subnormal series along `N ≤ L`).
      have hKNsub : (K.subgroupOf N).IsSubnormal := by
        have hcomap := hsub.comap (Subgroup.inclusion hNL)
        rwa [Subgroup.comap_inclusion_subgroupOf hNL] at hcomap
      -- Induction hypothesis: `N ⊆ Mstar`.
      have hNMstar : N ≤ Mstar := ih (Nat.card ↥N) (hcard ▸ hNlt) N rfl hKN hKNsub
      -- `L ≤ N_G(N)` (`N̄ ◁ ↥L`), so the single-step lemma gives `L ⊆ Mstar`.
      have hLnN : L ≤ Subgroup.normalizer (N : Set G) := by
        rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hNL, hNbar_eq]
        exact hNbarnorm
      exact le_partner_of_normalizes_of_le_of_uniq hNMstar hKN hLnN huniq

/-- **Every subgroup of a finite nilpotent group is subnormal** (mathcomp `nilpotent_subnormal`).
Strong induction on the index: for `H ≠ ⊤` the normalizer condition
(`Group.normalizerCondition_of_isNilpotent`) gives `H < N(H)`, `H ⊴ N(H)` (`normal_in_normalizer`),
and
`[Γ : N(H)] < [Γ : H]` (`index_strictAnti`), so the IH makes `N(H)` subnormal;
then `IsSubnormal.step`. -/
theorem isSubnormal_of_isNilpotent {Γ : Type*} [Group Γ] [Finite Γ] [Group.IsNilpotent Γ]
    (H : Subgroup Γ) : H.IsSubnormal := by
  have hnc : NormalizerCondition Γ := Group.normalizerCondition_of_isNilpotent
  induction hidx : H.index using Nat.strong_induction_on generalizing H with
  | _ n ih =>
    by_cases hHtop : H = ⊤
    · exact hHtop ▸ Subgroup.IsSubnormal.top
    · have hlt : H < Subgroup.normalizer (H : Set Γ) := hnc H (lt_top_iff_ne_top.mpr hHtop)
      have hidxlt : (Subgroup.normalizer (H : Set Γ)).index < n := by
        rw [← hidx]; exact Subgroup.index_strictAnti hlt
      have hstep : (Subgroup.normalizer (H : Set Γ)).IsSubnormal :=
        ih _ hidxlt (Subgroup.normalizer (H : Set Γ)) rfl
      exact Subgroup.IsSubnormal.step H (Subgroup.normalizer (H : Set Γ)) hlt.le hstep
        Subgroup.normal_in_normalizer

/-- **A subgroup contained in a normal, nilpotent subgroup is subnormal** in the ambient group
(mathcomp `nilpotent_subnormal` + `normal_subnormal` + transitivity): `H ≤ N ⊴ Γ` with `N` nilpotent
gives `H.subgroupOf N` subnormal in `↥N` (previous lemma), `N` subnormal in `Γ`
(`Normal.isSubnormal`), so `IsSubnormal.trans`. -/
theorem isSubnormal_of_le_normal_nilpotent {Γ : Type*} [Group Γ] [Finite Γ] {H N : Subgroup Γ}
    (hHN : H ≤ N) (hNnorm : N.Normal) (hNnil : Group.IsNilpotent ↥N) : H.IsSubnormal := by
  have := hNnil
  exact Subgroup.IsSubnormal.trans hHN (isSubnormal_of_isNilpotent (H.subgroupOf N))
    hNnorm.isSubnormal

/-- **Signalizer σ-decomposition `H_σ ⊔ (H ∩ M*) = H` for BG Theorem 15.8** (Coq
`tau2_P2type_signalizer`, `set D := H :&: L` + `sdprod_sigma maxH hallD`, BGsection15.v:1273/1374,
resting on `P2type_signalizer`, BGsection14.v:2283/2374): for the Corollary 14.12 signalizer
neighbour `H` of the type-`P₂` maximal `M` (with `M* ∈ 𝓜(C_G(K))`, `H ∈ 𝓜(N_G(R))`), the
`E`-setup complement `E` of `H_σ` (which contains `K` with `K ⊆ F(E)`, from
`typeP2_neighbor_is_typeF_of_mem`) lies in `M*`, so `H_σ ⊔ (H ∩ M*) ⊇ H_σ ⊔ E = H`.

**Proof (weaker than Coq's exact `H ∩ M* = D`).**  Coq proves the exact identity `H ∩ M* = D` (its
σ(H)′-Hall) via the harder `H_σ ∩ M* = 1` step, needed for its Hall/Fitting clauses.  The repo goal
is only the *join* `H_σ ⊔ (H ∩ M*) = H`, so the easy inclusion `E ⊆ H ∩ M*` suffices.  `E ⊆ M*`
comes from `le_partner_of_subnormal_of_uniq` (Coq `snK_sMst`): `K` is subnormal in `E`
(`K ⊆ F(E)`, `F(E)` normal nilpotent, `isSubnormal_of_le_normal_nilpotent`), `K ⊆ M*`
(`K ⊆ M*_σ`), and the uniqueness `K ≤ M*^a → a ∈ M*` (Coq `sK_uniqMst`, `partner_inf_and_uniq`);
`M* = Mst` (the dual partner) since `𝓜(C(K)) = {Mst}` (Prop 14.2(d)).  (issue 9017 更新 #12/#13.) -/
theorem signalizer_msigma_sup_inf_partner_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M Mstar U K R H : Subgroup G} {r : ℕ}
    (hM : M ∈ maximalSubgroups G) (hP2 : IsTypeP2 M)
    (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.centralizer (K : Set G)))
    (hr : r ∈ piSet U) (hRU : R ≤ U)
    (hR : Ch03.IsHallSubgroup ({r} : Set ℕ) (R.subgroupOf U))
    (hKNU : K ≤ Subgroup.normalizer (U : Set G))
    (hH : H ∈ maximalSubgroupsContaining (Subgroup.normalizer (R : Set G))) :
    OddOrder.BG.Ch3.S10.Msigma H ⊔ (H ⊓ Mstar) = H := by
  classical
  have hP : IsTypeP M := hP2.1
  -- Dual partner `Mst` (Theorem 14.7 / `typeP_duality`).
  set Kstar : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
    with hKstardef
  obtain ⟨Mst, hMstprop, hMstuniq⟩ := (typeP_duality hG hM hP hKM hK hKstardef).2.2
  obtain ⟨hMstmax, hMstP, hMnc, hMstpair, hZcyc, hZti, hP2or, hcover⟩ := hMstprop
  -- Uniqueness `sK_uniqMst : K ≤ Mst^a → a ∈ Mst` (Coq), and `K ≤ M*_σ` (⟹ `K ≤ Mst`).
  have hKMsigmaMst : K ≤ OddOrder.BG.Ch3.S10.Msigma Mst :=
    (le_of_eq hMstpair.2.2).trans inf_le_left
  have hMsMst : OddOrder.BG.Ch3.S10.Msigma M ⊓ Mst = Kstar :=
    msigma_inf_partner_eq_kstar hG hM hP2 hKM hKstardef hMstmax hKMsigmaMst hMstpair.1 hMnc
  have hKstarM : Kstar ≤ M := by
    rw [hKstardef]; exact inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le M)
  have hKstarNe : Kstar ≠ ⊥ := (typeP_structure hG hM hP hKM hK hKstardef hU).2.1
  have hKNe : K ≠ ⊥ := fun h => card_kappaHall_ne_one hP hKM hK (by rw [h, Subgroup.card_bot])
  obtain ⟨hziMMst, hsKuniq⟩ := partner_inf_and_uniq hG hMstmax hMstP hMstpair.1 hMstpair.2.1
    hMstpair.2.2 hKMsigmaMst hKM hKstarM hZcyc hKstarNe hKNe hMsMst
  -- `𝓜(C(K)) = {Mst}` (Prop 14.2(d) for `Mst`), so `Mstar = Mst`.
  obtain ⟨-, -, -, -, hP2struct, -, -⟩ := typeP_structure hG hM hP hKM hK hKstardef hU
  obtain ⟨-, q, hqprime, hKcard, -⟩ := hP2struct hP2
  have : Fact q.Prime := ⟨hqprime⟩
  have hKelemq : K ∈ elemAbelianOfRank G q 1 :=
    mem_elemAbelianOfRank.mpr ⟨Subgroup.IsElementaryAbelian.of_card_prime hKcard,
      by rw [hKcard, pow_one]⟩
  have huniqMst : maximalSubgroupsContaining (Subgroup.centralizer (K : Set G)) = {Mst} := by
    have hMstsol : Group.IsSolvable ↥Mst := hG.isSolvable_of_mem_maximalSubgroups hMstmax
    obtain ⟨UMst, hUMsthall⟩ : ∃ UMst : Subgroup G, Ch03.IsHallSubgroup
        ((kappa Mst ∪ OddOrder.BG.Ch3.S10.sigma Mst)ᶜ) (UMst.subgroupOf Mst) := by
      obtain ⟨U', hU'hall, -⟩ := Ch03.hall_D (G := ↥Mst)
        (π := (kappa Mst ∪ OddOrder.BG.Ch3.S10.sigma Mst)ᶜ) (U := (⊥ : Subgroup ↥Mst))
        (fun p hp => by simp at hp)
      have hUeq : (U'.map Mst.subtype).subgroupOf Mst = U' :=
        Subgroup.comap_map_eq_self_of_injective Mst.subtype_injective U'
      exact ⟨U'.map Mst.subtype, by rw [hUeq]; exact hU'hall⟩
    exact (typeP_structure hG hMstmax hMstP hMstpair.1 hMstpair.2.1 hMstpair.2.2
      hUMsthall).2.2.2.2.2.1 q hqprime K hKelemq le_rfl
  have hMstarEq : Mstar = Mst := by
    have hmem := hMstar; rw [huniqMst] at hmem; exact Set.mem_singleton_iff.mp hmem
  rw [hMstarEq]
  -- `E`-setup from the neighbour lemma: `M_σ(H) ⊔ E = H`, `K ≤ E`, `K ≤ F(E)`.
  obtain ⟨-, -, -, -, E, E₁, E₂, E₃, hEsetup, hKE, hKFE⟩ :=
    typeP2_neighbor_is_typeF_of_mem hG hM hP2 hKM hUM hK hU hUab hr hRU hR hKNU hH
  -- `E ≤ Mst` via subnormal closure (Coq `snK_sMst`): `K ⊴⊴ E`, `K ≤ Mst`, uniqueness.
  have hKMst : K ≤ Mst := hKMsigmaMst.trans (OddOrder.BG.Ch3.S10.Msigma_le Mst)
  have hKsubnormal : (K.subgroupOf E).IsSubnormal := by
    have : Group.IsNilpotent ↥(OddOrder.BG.Ch2.S08.fittingInG E) :=
      OddOrder.BG.Ch2.S08.fittingInG_isNilpotent E
    refine isSubnormal_of_le_normal_nilpotent
      (N := (OddOrder.BG.Ch2.S08.fittingInG E).subgroupOf E) ?_
      (OddOrder.BG.Ch2.S08.fittingInG_subgroupOf_normal E)
      (Group.nilpotent_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch2.S08.fittingInG_le E)).symm)
    exact Subgroup.comap_mono hKFE
  have hEMst : E ≤ Mst := le_partner_of_subnormal_of_uniq hsKuniq hKMst E hKE hKsubnormal
  -- Conclude: `E ⊆ H ∩ Mst` and `M_σ(H) ⊔ E = H`.
  refine le_antisymm (sup_le (OddOrder.BG.Ch3.S10.Msigma_le H) inf_le_left) ?_
  calc H = OddOrder.BG.Ch3.S10.Msigma H ⊔ E := hEsetup.E_compl_sup.symm
    _ ≤ OddOrder.BG.Ch3.S10.Msigma H ⊔ (H ⊓ Mst) :=
        sup_le_sup_left (le_inf hEsetup.E_le hEMst) _

end OddOrder.BG.Ch4.S14


