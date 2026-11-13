-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Lemma128d
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S12_Lemma128d
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:54:24.375795+00:00
-- url     : https://prove2.me/theorems/bdf8d493-8959-4121-933a-d2da06b0a507
-- title:
--   BG §12: Lemma 12.8(d)(e)(f) and assembly
-- statement:
--   Formalizes the second half of Lemma 12.8 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §12: (d) $N_G(A)=N_G(S)=N_G(E_2)=N_G(E_2E_3)=N_G(F(E))$; (e) if $X\in\mathcal{E}^1(E_1)$ and $C_{M_\sigma}(X)=1$ then $E\subseteq C_G(X)$; (f) for $X\le N_G(S)$, $C_S(X)$ and $[S,X]$ are normal in $N_G(S)$; and the assembly of the whole lemma.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 9 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S12_Lemma128d.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S12_Lemma128d.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Lemma128

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- `C_G(H ⊔ K) = C_G(H) ⊓ C_G(K)`. -/
theorem centralizer_sup_eq (H K : Subgroup G) :
    Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G)
      = Subgroup.centralizer (H : Set G) ⊓ Subgroup.centralizer (K : Set G) := by
  refine le_antisymm (le_inf
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right))) ?_
  rintro c ⟨hcH, hcK⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rw [SetLike.mem_coe, Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with hx | hx
      · exact Subgroup.mem_centralizer_iff.mp hcH x hx
      · exact Subgroup.mem_centralizer_iff.mp hcK x hx
  | one => simp
  | mul a b _ _ iha ihb => rw [mul_assoc, ihb, ← mul_assoc, iha, mul_assoc]
  | inv a _ iha =>
      have h1 : a * c = c * a := iha
      calc a⁻¹ * c = a⁻¹ * (c * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * c) * a⁻¹ := by rw [h1]
        _ = c * a⁻¹ := by group

/-- A `π`-subgroup of a finite nilpotent subgroup `H` lies in `O_π(H)`
(general-base version of `piGroup_le_opiCoreInG_fittingInG`). -/
theorem piGroup_le_opiCoreInG_of_nilpotent [Finite G]
    {H : Subgroup G} [Group.IsNilpotent ↥H] {π : Set ℕ}
    {T : Subgroup G} (hT : ∀ r ∈ (Nat.card ↥T).primeFactors, r ∈ π) (hTH : T ≤ H) :
    T ≤ opiCoreInG π H := by
  classical
  have hHall := S10.oPiCore_isHall_of_isNilpotent (K := ↥H) π
  have hTpi : Ch03.Subgroup.IsPiGroup π (T.subgroupOf H) := by
    intro r hr
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv] at hr
    exact hT r hr
  have h1 : T.subgroupOf H ≤ Ch03.oPiCore π ↥H :=
    S10.isPiGroup_le_of_normal_isHallSubgroup hHall hTpi
  calc T = (T.subgroupOf H).map H.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hTH).symm
    _ ≤ (Ch03.oPiCore π ↥H).map H.subtype := Subgroup.map_mono h1
    _ = opiCoreInG π H := rfl

/-- The `π`-core of a finite nilpotent subgroup `H` has `r`-part `0` for `r ∉ π` and the
full `r`-part of `|H|` for primes `r ∈ π`; here we only need the `≤ ν_r(H)` direction
and the vanishing, packaged as divisibility against a target with matching parts. -/
private theorem card_opiCoreInG_dvd_of_nilpotent [Finite G]
    {H : Subgroup G} [Group.IsNilpotent ↥H] {π : Set ℕ} {n : ℕ} (hn : n ≠ 0)
    (hcover : ∀ r : ℕ, r.Prime → r ∈ π →
      (Nat.card ↥H).factorization r ≤ n.factorization r) :
    Nat.card ↥(opiCoreInG π H) ∣ n := by
  classical
  have hHall := S10.oPiCore_isHall_of_isNilpotent (K := ↥H) π
  have hcard_eq : Nat.card ↥(opiCoreInG π H) = Nat.card ↥(Ch03.oPiCore π ↥H) :=
    Subgroup.card_map_of_injective H.subtype_injective
  rw [← Nat.factorization_le_iff_dvd Nat.card_pos.ne' hn]
  intro r
  by_cases hr : r.Prime
  case neg =>
    rw [Nat.factorization_eq_zero_of_not_prime _ hr]
    exact Nat.zero_le _
  case pos =>
    by_cases hrπ : r ∈ π
    · refine le_trans ?_ (hcover r hr hrπ)
      rw [hcard_eq]
      exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
        (Subgroup.card_subgroup_dvd_card _) r
    · have : ¬ r ∣ Nat.card ↥(opiCoreInG π H) := by
        intro hdvd
        rw [hcard_eq] at hdvd
        exact hrπ (hHall.1 r (Nat.mem_primeFactors.mpr ⟨hr, hdvd, Nat.card_pos.ne'⟩))
      rw [Nat.factorization_eq_zero_of_not_dvd this]
      exact Nat.zero_le _

/-- `E₃ ≤ F(E)`: `E₃` is cyclic (12.1(c)), hence nilpotent, and normal in `E`. -/
theorem E3_le_fittingInG [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    E₃ ≤ Ch2.S08.fittingInG E := by
  have hcyc : IsCyclic ↥E₃ := h.E3_isCyclic hG
  let : CommGroup ↥E₃ := IsCyclic.commGroup
  have h1 : (E₃.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.E₃_le).mpr (h.E3_normal hG)
  have h3 : Group.IsNilpotent ↥(E₃.subgroupOf E) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.E₃_le).symm
  calc E₃ = (E₃.subgroupOf E).map E.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le h.E₃_le).symm
    _ ≤ (Ch01.fitting ↥E).map E.subtype :=
        Subgroup.map_mono Ch01.nilpotent_normal_le_fitting
    _ = Ch2.S08.fittingInG E := rfl

/-- **BG Lemma 12.8(d)** (mmd L3278-3280):
`N_G(A) = N_G(S) = N_G(E₂) = N_G(E₂E₃) = N_G(F(E))`. -/
theorem normalizer_chain_of_abelianSylow [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {S : Sylow p G} (hAS : A ≤ (S : Subgroup G))
    (hSab : IsMulCommutative ↥(S : Subgroup G)) :
    Subgroup.normalizer (A : Set G)
      = Subgroup.normalizer ((S : Subgroup G) : Set G) ∧
    Subgroup.normalizer ((S : Subgroup G) : Set G)
      = Subgroup.normalizer ((E₂ : Subgroup G) : Set G) ∧
    Subgroup.normalizer ((E₂ : Subgroup G) : Set G)
      = Subgroup.normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) ∧
    Subgroup.normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G)
      = Subgroup.normalizer ((Ch2.S08.fittingInG E : Subgroup G) : Set G) := by
  classical
  set FE : Subgroup G := Ch2.S08.fittingInG E with hFEdef
  have : Group.IsNilpotent ↥FE := Ch2.S08.fittingInG_isNilpotent E
  have hSE : (S : Subgroup G) ≤ E :=
    (le_centralizer_of_le_of_le hSab le_rfl hAS).trans
      (centralizer_le_E_of_tau2 hG h hp hA hAE).1
  have hSM : (S : Subgroup G) ≤ M := hSE.trans h.E_le
  have hallab : ∀ T : Subgroup G, IsPGroup p ↥T → IsMulCommutative ↥T := by
    intro T hT
    obtain ⟨ST, hTST⟩ := hT.exists_le_sylow
    exact isMulCommutative_of_le
      (sylow_isMulCommutative_of_tau2_of_abelian hG h hp hA hAE hSab hp ST) hTST
  obtain ⟨⟨hE₂ab, hE_norm_E₂⟩, hE₂hallG, hE₂eq⟩ :=
    E2_abelian_normal_hall_of_abelianSylow hG h hp hA hAE hSab
  have hchain := sylow_chain_of_abelianSylow hG h hp hA hAE hAS hSab
  have hS_le_FE : (S : Subgroup G) ≤ FE := hchain.1.trans hchain.2.1
  have hE₂_le_FE : E₂ ≤ FE := by
    rw [hE₂eq]
    exact Subgroup.map_subtype_le _
  have hE₃_le_FE : E₃ ≤ FE := E3_le_fittingInG hG h
  have hE₂nilp : Group.IsNilpotent ↥E₂ :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hE₂_le_FE)
  -- prime-part bookkeeping for `K := E₂ ⊔ E₃`.
  set K : Subgroup G := E₂ ⊔ E₃ with hKdef
  have hE₂pi : ∀ r ∈ (Nat.card ↥E₂).primeFactors, r ∈ tau2 M := fun r hr =>
    hE₂hallG.1 r hr
  have hE₃pi : ∀ r ∈ (Nat.card ↥E₃).primeFactors, r ∈ tau3 M := by
    intro r hr
    have h1 : r ∈ (Nat.card ↥(E₃.subgroupOf E)).primeFactors := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv]
      exact hr
    exact h.E₃_hall.1 r h1
  have hE₂E₃_bot : E₂ ⊓ E₃ = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard (coprime_of_forall_prime_not_dvd ?_)).eq_bot
    intro r hr h1 h2
    have hr2 := hE₂pi r (Nat.mem_primeFactors.mpr ⟨hr, h1, Nat.card_pos.ne'⟩)
    have hr3 := hE₃pi r (Nat.mem_primeFactors.mpr ⟨hr, h2, Nat.card_pos.ne'⟩)
    have ha := tau2_pRank_eq_two hr2
    have hb := tau3_pRank_eq_one hr3
    omega
  have hcard_K : Nat.card ↥K = Nat.card ↥E₂ * Nat.card ↥E₃ :=
    card_sup_eq_mul_of_le_normalizer_of_disjoint
      (h.E₂_le.trans (h.E3_normal hG)) hE₂E₃_bot
  have hK_le_FE : K ≤ FE := sup_le hE₂_le_FE hE₃_le_FE
  have hKnilp : Group.IsNilpotent ↥K :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK_le_FE)
  -- `ν_r(E) = ν_r(E₂)` for `r ∈ τ₂` and `= ν_r(E₃)` for `r ∈ τ₃`.
  have hfacE₂ : ∀ r : ℕ, r.Prime → r ∈ tau2 M →
      (Nat.card ↥E).factorization r = (Nat.card ↥E₂).factorization r := by
    intro r hr hr2
    have hidx : ((E₂.subgroupOf E).index).factorization r = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hdvd
      exact h.E₂_hall.2 r (Nat.mem_primeFactors.mpr
        ⟨hr, hdvd, Subgroup.index_ne_zero_of_finite⟩) hr2
    have hsum : (Nat.card ↥(E₂.subgroupOf E)).factorization r
        + ((E₂.subgroupOf E).index).factorization r
        = (Nat.card ↥E).factorization r := by
      rw [← Subgroup.card_mul_index (E₂.subgroupOf E),
        Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
        Finsupp.add_apply]
    have hcardc : (Nat.card ↥(E₂.subgroupOf E)).factorization r
        = (Nat.card ↥E₂).factorization r := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv]
    omega
  have hfacE₃ : ∀ r : ℕ, r.Prime → r ∈ tau3 M →
      (Nat.card ↥E).factorization r = (Nat.card ↥E₃).factorization r := by
    intro r hr hr3
    have hidx : ((E₃.subgroupOf E).index).factorization r = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hdvd
      exact h.E₃_hall.2 r (Nat.mem_primeFactors.mpr
        ⟨hr, hdvd, Subgroup.index_ne_zero_of_finite⟩) hr3
    have hsum : (Nat.card ↥(E₃.subgroupOf E)).factorization r
        + ((E₃.subgroupOf E).index).factorization r
        = (Nat.card ↥E).factorization r := by
      rw [← Subgroup.card_mul_index (E₃.subgroupOf E),
        Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
        Finsupp.add_apply]
    have hcardc : (Nat.card ↥(E₃.subgroupOf E)).factorization r
        = (Nat.card ↥E₃).factorization r := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv]
    omega
  -- `K = O_{τ₂ ∪ τ₃}(F(E))`.
  have hK_eq : K = opiCoreInG (tau2 M ∪ tau3 M) FE := by
    refine le_antisymm ?_ ?_
    · refine piGroup_le_opiCoreInG_of_nilpotent ?_ hK_le_FE
      intro r hr
      have hr_prime := Nat.prime_of_mem_primeFactors hr
      have hdvd := Nat.dvd_of_mem_primeFactors hr
      rw [hcard_K] at hdvd
      rcases (Nat.Prime.dvd_mul hr_prime).mp hdvd with h1 | h1
      · exact Or.inl (hE₂pi r (Nat.mem_primeFactors.mpr ⟨hr_prime, h1, Nat.card_pos.ne'⟩))
      · exact Or.inr (hE₃pi r (Nat.mem_primeFactors.mpr ⟨hr_prime, h1, Nat.card_pos.ne'⟩))
    · refine le_of_eq (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
      · refine piGroup_le_opiCoreInG_of_nilpotent ?_ hK_le_FE
        intro r hr
        have hr_prime := Nat.prime_of_mem_primeFactors hr
        have hdvd := Nat.dvd_of_mem_primeFactors hr
        rw [hcard_K] at hdvd
        rcases (Nat.Prime.dvd_mul hr_prime).mp hdvd with h1 | h1
        · exact Or.inl (hE₂pi r (Nat.mem_primeFactors.mpr
            ⟨hr_prime, h1, Nat.card_pos.ne'⟩))
        · exact Or.inr (hE₃pi r (Nat.mem_primeFactors.mpr
            ⟨hr_prime, h1, Nat.card_pos.ne'⟩))
      · refine Nat.le_of_dvd Nat.card_pos ?_
        refine card_opiCoreInG_dvd_of_nilpotent Nat.card_pos.ne' ?_
        intro r hr hrτ
        have hfacK : (Nat.card ↥K).factorization r
            = (Nat.card ↥E₂).factorization r + (Nat.card ↥E₃).factorization r := by
          rw [hcard_K, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
            Finsupp.add_apply]
        have hFE_le : (Nat.card ↥FE).factorization r ≤ (Nat.card ↥E).factorization r :=
          (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
            (Subgroup.card_dvd_of_le (Ch2.S08.fittingInG_le E)) r
        rcases hrτ with hr2 | hr3
        · rw [hfacK]
          have := hfacE₂ r hr hr2
          omega
        · rw [hfacK]
          have := hfacE₃ r hr hr3
          omega
  -- `E₂ = O_{τ₂}(K)`.
  have hE₂_eq_K : E₂ = opiCoreInG (tau2 M) K := by
    refine le_antisymm
      (piGroup_le_opiCoreInG_of_nilpotent hE₂pi le_sup_left) ?_
    refine le_of_eq (Subgroup.eq_of_le_of_card_ge
      (piGroup_le_opiCoreInG_of_nilpotent hE₂pi le_sup_left) ?_).symm
    refine Nat.le_of_dvd Nat.card_pos ?_
    refine card_opiCoreInG_dvd_of_nilpotent Nat.card_pos.ne' ?_
    intro r hr hr2
    change (Nat.card ↥K).factorization r ≤ (Nat.card ↥E₂).factorization r
    have hfacK : (Nat.card ↥K).factorization r
        = (Nat.card ↥E₂).factorization r + (Nat.card ↥E₃).factorization r := by
      rw [hcard_K, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
        Finsupp.add_apply]
    have hE₃z : (Nat.card ↥E₃).factorization r = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hdvd
      have hr3 := hE₃pi r (Nat.mem_primeFactors.mpr ⟨hr, hdvd, Nat.card_pos.ne'⟩)
      have ha := tau2_pRank_eq_two hr2
      have hb := tau3_pRank_eq_one hr3
      omega
    omega
  -- `S = O_p(E₂)`.
  have hS_le_E₂ : (S : Subgroup G) ≤ E₂ := by
    rw [hE₂eq]
    refine piGroup_le_opiCoreInG_fittingInG ?_ hS_le_FE
    intro r hr
    rw [Sylow.card_eq_multiplicity] at hr
    have h1 := Nat.prime_of_mem_primeFactors hr
    have h2 := Nat.dvd_of_mem_primeFactors hr
    have : r = p := (Nat.prime_dvd_prime_iff_eq h1 Fact.out).mp (h1.dvd_of_dvd_pow h2)
    rwa [this]
  have hS_eq_E₂ : (S : Subgroup G) = opiCoreInG ({p} : Set ℕ) E₂ := by
    have hSpi : ∀ r ∈ (Nat.card ↥(S : Subgroup G)).primeFactors, r ∈ ({p} : Set ℕ) := by
      intro r hr
      rw [Sylow.card_eq_multiplicity] at hr
      have h1 := Nat.prime_of_mem_primeFactors hr
      have h2 := Nat.dvd_of_mem_primeFactors hr
      have : r = p := (Nat.prime_dvd_prime_iff_eq h1 Fact.out).mp (h1.dvd_of_dvd_pow h2)
      simpa using this
    refine le_antisymm (piGroup_le_opiCoreInG_of_nilpotent hSpi hS_le_E₂) ?_
    refine le_of_eq (Subgroup.eq_of_le_of_card_ge
      (piGroup_le_opiCoreInG_of_nilpotent hSpi hS_le_E₂) ?_).symm
    refine Nat.le_of_dvd Nat.card_pos ?_
    refine card_opiCoreInG_dvd_of_nilpotent Nat.card_pos.ne' ?_
    intro r hr hrp
    have hrp' : r = p := by simpa using hrp
    subst hrp'
    rw [Sylow.card_eq_multiplicity]
    have hps : ((r ^ (Nat.card G).factorization r).factorization) r
        = (Nat.card G).factorization r := by
      rw [Nat.Prime.factorization_pow Fact.out]
      simp
    rw [hps]
    have h1 : Nat.card ↥E₂ ∣ Nat.card G := Subgroup.card_subgroup_dvd_card E₂
    exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr h1 r
  -- the normalizer chain, one inclusion at a time.
  have hT1 : Subgroup.normalizer ((FE : Subgroup G) : Set G)
      ≤ Subgroup.normalizer ((K : Subgroup G) : Set G) := by
    rw [hK_eq]
    exact le_normalizer_opiCoreInG_of_le_normalizer _ le_rfl
  have hT2 : Subgroup.normalizer ((K : Subgroup G) : Set G)
      ≤ Subgroup.normalizer ((E₂ : Subgroup G) : Set G) := by
    rw [hE₂_eq_K]
    exact le_normalizer_opiCoreInG_of_le_normalizer _ le_rfl
  have hT3 : Subgroup.normalizer ((E₂ : Subgroup G) : Set G)
      ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
    rw [hS_eq_E₂]
    exact le_normalizer_opiCoreInG_of_le_normalizer _ le_rfl
  have hT4 : Subgroup.normalizer ((S : Subgroup G) : Set G)
      ≤ Subgroup.normalizer (A : Set G) :=
    (normalizer_sylow_le_normalizer_elemAb hG h hp hA hAE hAS hSM).1
  -- `N_G(A) ≤ N_G(F(E))` via `F(N_G(A)) = F(C_G(A)) = F(E)`.
  have hT5 : Subgroup.normalizer (A : Set G)
      ≤ Subgroup.normalizer ((FE : Subgroup G) : Set G) := by
    set N : Subgroup G := Subgroup.normalizer (A : Set G) with hNdef
    set C : Subgroup G := Subgroup.centralizer (A : Set G) with hCdef
    obtain ⟨_, hFN_le_C, hFN_le_FE⟩ :=
      derivedInG_normalizer_elemAb_le_fittingInG hG h hp hA hAE hallab
    have hC_le_E : C ≤ E := (centralizer_le_E_of_tau2 hG h hp hA hAE).1
    have hC_le_N : C ≤ N := Subgroup.centralizer_le_normalizer _
    have hN_norm_C : N ≤ Subgroup.normalizer ((C : Subgroup G) : Set G) := by
      intro n hn
      refine mem_normalizer_of_conj_smul_eq_self ?_
      rw [hCdef, centralizer_conj_smul, conj_smul_eq_self_of_mem_normalizer hn]
    have hFE_le_C : FE ≤ C :=
      hchain.2.2.1.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAS))
    -- `F(E) ≤ F(C)`.
    have hFE_le_FC : FE ≤ Ch2.S08.fittingInG C := by
      have h1 : (FE.subgroupOf C).Normal := by
        refine (Subgroup.normal_subgroupOf_iff_le_normalizer hFE_le_C).mpr ?_
        intro c hc
        exact Ch2.S08.mem_normalizer_fittingInG_of_mem (hC_le_E hc)
      have h3 : Group.IsNilpotent ↥(FE.subgroupOf C) :=
        Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hFE_le_C).symm
      calc FE = (FE.subgroupOf C).map C.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hFE_le_C).symm
        _ ≤ (Ch01.fitting ↥C).map C.subtype :=
            Subgroup.map_mono Ch01.nilpotent_normal_le_fitting
        _ = Ch2.S08.fittingInG C := rfl
    -- `F(C) ≤ F(N)`.
    have hFC_le_FN : Ch2.S08.fittingInG C ≤ Ch2.S08.fittingInG N := by
      have hFC_le_C : Ch2.S08.fittingInG C ≤ C := Ch2.S08.fittingInG_le C
      have hFC_le_N : Ch2.S08.fittingInG C ≤ N := hFC_le_C.trans hC_le_N
      have h1 : ((Ch2.S08.fittingInG C).subgroupOf N).Normal := by
        refine (Subgroup.normal_subgroupOf_iff_le_normalizer hFC_le_N).mpr ?_
        refine hN_norm_C.trans ?_
        exact AppB.normalizer_le_normalizer_map_of_characteristic
          (K := C) (W := Ch01.fitting ↥C)
      have : Group.IsNilpotent ↥(Ch2.S08.fittingInG C) := Ch2.S08.fittingInG_isNilpotent C
      have h3 : Group.IsNilpotent ↥((Ch2.S08.fittingInG C).subgroupOf N) :=
        Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hFC_le_N).symm
      calc Ch2.S08.fittingInG C
          = ((Ch2.S08.fittingInG C).subgroupOf N).map N.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hFC_le_N).symm
        _ ≤ (Ch01.fitting ↥N).map N.subtype :=
            Subgroup.map_mono Ch01.nilpotent_normal_le_fitting
        _ = Ch2.S08.fittingInG N := rfl
    have hFN_eq_FE : Ch2.S08.fittingInG N = FE :=
      le_antisymm hFN_le_FE (hFE_le_FC.trans hFC_le_FN)
    intro n hn
    have h1 : n ∈ Subgroup.normalizer ((Ch2.S08.fittingInG N : Subgroup G) : Set G) :=
      Ch2.S08.mem_normalizer_fittingInG_of_mem hn
    rwa [hFN_eq_FE] at h1
  refine ⟨le_antisymm (hT5.trans (hT1.trans (hT2.trans hT3))) hT4,
    le_antisymm (hT4.trans (hT5.trans (hT1.trans hT2))) hT3,
    le_antisymm (hT3.trans ((hT4.trans hT5).trans hT1)) hT2,
    le_antisymm (hT2.trans (hT3.trans (hT4.trans hT5))) hT1⟩

/-- **BG Lemma 12.8(f)** (mmd L3282): for any `X ≤ N_G(S)`, both `C_S(X) = S ⊓ C_G(X)`
and `⁅S, X⁆` are normal in `N_G(S)` (stated as normalizer containments).

`H := C_G(S)X` contains `N_G(S)' ⊆ C_G(S)`, hence is normal in `N_G(S)`;
`C_S(X) = C_S(H)` and `⁅S, X⁆ = ⁅S, H⁆` since `C_G(S)` centralizes `S` (and the
commutators `⁅s,x⁆ ∈ S`), and `S ⊓ C_G(H)`, `⁅S, H⁆` are conjugation-invariant. -/
theorem relative_normality_of_abelianSylow [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {S : Sylow p G} (hAS : A ≤ (S : Subgroup G))
    (hSab : IsMulCommutative ↥(S : Subgroup G)) :
    ∀ X : Subgroup G, X ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) →
      Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
        Subgroup.normalizer
          (((S : Subgroup G) ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) ∧
      Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((⁅(S : Subgroup G), X⁆ : Subgroup G) : Set G) := by
  classical
  intro X hX_le_N
  set NS : Subgroup G := Subgroup.normalizer ((S : Subgroup G) : Set G) with hNSdef
  have hchain := sylow_chain_of_abelianSylow hG h hp hA hAE hAS hSab
  have hder_le_C : derivedInG NS ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) :=
    hchain.2.1.trans hchain.2.2.1
  set H : Subgroup G := Subgroup.centralizer ((S : Subgroup G) : Set G) ⊔ X with hHdef
  have hH_le_N : H ≤ NS :=
    sup_le (Subgroup.centralizer_le_normalizer _) hX_le_N
  -- `H ⊴ N_G(S)` (it contains the derived subgroup).
  have hN_norm_H : NS ≤ Subgroup.normalizer ((H : Subgroup G) : Set G) := by
    have : (H.subgroupOf NS).Normal := by
      refine Ch06.normal_of_commutator_le ?_
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_sup_left (hder_le_C ⟨x, hx, rfl⟩)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hH_le_N).mp inferInstance
  have hS_le_CC : (S : Subgroup G) ≤
      Subgroup.centralizer ((Subgroup.centralizer ((S : Subgroup G) : Set G)) : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp hy s hs).symm
  constructor
  · -- `C_S(X) = S ⊓ C_G(H)` is conjugation-invariant.
    have hCSX_eq : (S : Subgroup G) ⊓ Subgroup.centralizer (X : Set G)
        = (S : Subgroup G) ⊓ Subgroup.centralizer ((H : Subgroup G) : Set G) := by
      rw [hHdef, centralizer_sup_eq]
      refine le_antisymm (le_inf inf_le_left (le_inf ?_ inf_le_right)) ?_
      · exact inf_le_left.trans hS_le_CC
      · exact inf_le_inf_left _ inf_le_right
    rw [hCSX_eq]
    intro n hn
    refine mem_normalizer_of_conj_smul_eq_self ?_
    rw [mulAut_smul_eq_map,
      Subgroup.map_inf _ _ (MulAut.conj n).toMonoidHom (MulAut.conj n).injective,
      ← mulAut_smul_eq_map, ← mulAut_smul_eq_map,
      conj_smul_eq_self_of_mem_normalizer hn, centralizer_conj_smul,
      conj_smul_eq_self_of_mem_normalizer (hN_norm_H hn)]
  · -- `⁅S, X⁆ = ⁅S, H⁆` is conjugation-invariant.
    have hcomm_eq : (⁅(S : Subgroup G), X⁆ : Subgroup G) = ⁅(S : Subgroup G), H⁆ := by
      refine le_antisymm (Subgroup.commutator_mono le_rfl le_sup_right) ?_
      rw [Subgroup.commutator_le]
      intro s hs g hg
      -- decompose `g = c * x` inside `↥NS` using `C_G(S) ⊴ N_G(S)`.
      have hCnorm : ((Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
          NS).Normal := by
        refine Ch06.normal_of_commutator_le ?_
        intro y hy
        rw [Subgroup.mem_subgroupOf]
        exact hder_le_C ⟨y, hy, rfl⟩
      have hg' : (⟨g, hH_le_N hg⟩ : ↥NS) ∈ H.subgroupOf NS := Subgroup.mem_subgroupOf.mpr hg
      have hsplit : H.subgroupOf NS
          = (Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf NS
            ⊔ X.subgroupOf NS := by
        rw [hHdef]
        exact Subgroup.subgroupOf_sup (Subgroup.centralizer_le_normalizer _) hX_le_N
      rw [hsplit] at hg'
      have hmul : (⟨g, hH_le_N hg⟩ : ↥NS) ∈
          ((Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf NS : Set ↥NS)
            * (X.subgroupOf NS : Set ↥NS) := by
        rw [← Subgroup.normal_mul]
        exact hg'
      obtain ⟨c, hc, x, hx, hcx⟩ := hmul
      have hgcx : g = (c : G) * (x : G) := by
        have := congrArg Subtype.val hcx
        simpa using this.symm
      have hcC : (c : G) ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) :=
        Subgroup.mem_subgroupOf.mp hc
      have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
      -- `⁅s, c·x⁆ = c ⁅s,x⁆ c⁻¹ = ⁅s,x⁆` (`c` centralizes `s` and `⁅s,x⁆ ∈ S`).
      have hsc : (c : G) * s = s * c :=
        (Subgroup.mem_centralizer_iff.mp hcC s hs).symm
      have hsxS : ⁅s, (x : G)⁆ ∈ (S : Subgroup G) := by
        have hxN : (x : G) ∈ NS := hX_le_N hxX
        have h1 : (x : G) * s⁻¹ * (x : G)⁻¹ ∈ (S : Subgroup G) := by
          have h2 := (Subgroup.mem_normalizer_iff.mp hxN s⁻¹).mp (S.inv_mem' hs)
          exact h2
        have h3 : ⁅s, (x : G)⁆ = s * ((x : G) * s⁻¹ * (x : G)⁻¹) := by
          rw [commutatorElement_def]
          group
        rw [h3]
        exact Subgroup.mul_mem _ hs h1
      have hkey : ⁅s, g⁆ = ⁅s, (x : G)⁆ := by
        rw [hgcx]
        have hcfix : (c : G) * ⁅s, (x : G)⁆ * (c : G)⁻¹ = ⁅s, (x : G)⁆ :=
          by
            have := Subgroup.mem_centralizer_iff.mp hcC _ hsxS
            calc (c : G) * ⁅s, (x : G)⁆ * (c : G)⁻¹
                = ⁅s, (x : G)⁆ * (c : G) * (c : G)⁻¹ := by rw [← this]
              _ = ⁅s, (x : G)⁆ := by group
        calc ⁅s, (c : G) * (x : G)⁆
            = s * ((c : G) * (x : G)) * s⁻¹ * ((c : G) * (x : G))⁻¹ := by
              rw [commutatorElement_def]
          _ = (c : G) * (s * (x : G) * s⁻¹ * (x : G)⁻¹) * (c : G)⁻¹ := by
              rw [show s * ((c : G) * (x : G)) = (c : G) * (s * (x : G)) from by
                rw [← mul_assoc, ← hsc, mul_assoc]]
              group
          _ = (c : G) * ⁅s, (x : G)⁆ * (c : G)⁻¹ := by rw [commutatorElement_def]
          _ = ⁅s, (x : G)⁆ := hcfix
      rw [hkey]
      exact Subgroup.commutator_mem_commutator hs hxX
    rw [hcomm_eq]
    intro n hn
    refine mem_normalizer_of_conj_smul_eq_self ?_
    rw [mulAut_smul_eq_map, Subgroup.map_commutator, ← mulAut_smul_eq_map,
      ← mulAut_smul_eq_map, conj_smul_eq_self_of_mem_normalizer hn,
      conj_smul_eq_self_of_mem_normalizer (hN_norm_H hn)]

/-- `F(E)` centralizes any of its **abelian** `π`-cores: the `O_π'`-part commutes by
coprimality, the `O_π`-part is the core itself. -/
theorem fittingInG_le_centralizer_opiCoreInG [Finite G] {E : Subgroup G} {π : Set ℕ}
    (hab : IsMulCommutative ↥(opiCoreInG π (Ch2.S08.fittingInG E))) :
    Ch2.S08.fittingInG E ≤
      Subgroup.centralizer ((opiCoreInG π (Ch2.S08.fittingInG E) : Subgroup G) : Set G) := by
  classical
  set FE : Subgroup G := Ch2.S08.fittingInG E with hFEdef
  have : Group.IsNilpotent ↥FE := Ch2.S08.fittingInG_isNilpotent E
  set O1 : Subgroup ↥FE := Ch03.oPiCore π ↥FE with hO1def
  set O2 : Subgroup ↥FE := Ch03.oPiCore πᶜ ↥FE with hO2def
  have hO1_le_C : O1.map FE.subtype ≤
      Subgroup.centralizer ((opiCoreInG π FE : Subgroup G) : Set G) :=
    le_centralizer_of_le_of_le hab le_rfl le_rfl
  have hO2_le_C : O2.map FE.subtype ≤
      Subgroup.centralizer ((opiCoreInG π FE : Subgroup G) : Set G) := by
    have hcomm : ⁅O2, O1⁆ = ⊥ := by
      rw [← le_bot_iff]
      calc ⁅O2, O1⁆ ≤ O2 ⊓ O1 := by
            have : O2.Normal := Ch03.oPiCore.normal _ _
            have : O1.Normal := Ch03.oPiCore.normal _ _
            exact le_inf (Subgroup.commutator_le_left _ _)
              (Subgroup.commutator_le_right _ _)
        _ ≤ ⊥ := by
            refine le_of_eq (Subgroup.disjoint_of_coprime_natCard
              (coprime_of_forall_prime_not_dvd ?_)).eq_bot
            intro r hr h1 h2
            have hr1 : r ∈ πᶜ := S10.oPiCore_isHall_of_isNilpotent (K := ↥FE) πᶜ |>.1 r
              (Nat.mem_primeFactors.mpr ⟨hr, h1, Nat.card_pos.ne'⟩)
            have hr2 : r ∈ π := S10.oPiCore_isHall_of_isNilpotent (K := ↥FE) π |>.1 r
              (Nat.mem_primeFactors.mpr ⟨hr, h2, Nat.card_pos.ne'⟩)
            exact hr1 hr2
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    intro y hy
    obtain ⟨y', hy', rfl⟩ := hy
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨b', hb', rfl⟩ := hb
    have h2 := Subgroup.mem_centralizer_iff.mp (hle hy') _ hb'
    exact congrArg Subtype.val h2
  have htop := oPiCore_sup_compl_eq_top ↥FE π
  intro y hy
  have hy' : (⟨y, hy⟩ : ↥FE) ∈ O1 ⊔ O2 := by
    rw [hO1def, hO2def, htop]
    exact Subgroup.mem_top _
  have hmap : y ∈ (O1 ⊔ O2).map FE.subtype := ⟨⟨y, hy⟩, hy', rfl⟩
  rw [Subgroup.map_sup] at hmap
  exact (sup_le hO1_le_C hO2_le_C) hmap

/-- **BG Lemma 12.8(e)** (mmd L3283-3284): if `X ∈ ℰ_q¹(E₁)` and `C_{M_σ}(X) = 1`, then
`X ≤ E` and `E ≤ C_G(X)` (i.e. `X ⊆ Z(E)`).

`K := E₂E₃` is abelian and `F(E) ≤ C_G(K)`, so (as in (f)) `⁅K, X⁆ ⊴ N_G(S)`;
Proposition 10.11(d) gives `M ≤ N_G(⁅K,X⁆)`, so a nontrivial commutator would force
`N_G(S) ≤ N_G(⁅K,X⁆) = M`, contradicting 12.8's basic setup. Hence `K ≤ C_G(X)`,
and `E = E₁ K` with cyclic `E₁ ⊇ X` finishes. -/
theorem central_line_of_abelianSylow [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {S : Sylow p G} (hAS : A ≤ (S : Subgroup G))
    (hSab : IsMulCommutative ↥(S : Subgroup G)) :
    ∀ X : Subgroup G, (∃ q : ℕ, q.Prime ∧ X ∈ elemAbelianOfRank G q 1) → X ≤ E₁ →
      S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) = ⊥ →
      X ≤ E ∧ E ≤ Subgroup.centralizer (X : Set G) := by
  classical
  intro X hXq hXE₁ hCX
  obtain ⟨q, hq_prime, hX⟩ := hXq
  have : Fact q.Prime := ⟨hq_prime⟩
  have hXE : X ≤ E := hXE₁.trans h.E₁_le
  refine ⟨hXE, ?_⟩
  set FE : Subgroup G := Ch2.S08.fittingInG E with hFEdef
  have : Group.IsNilpotent ↥FE := Ch2.S08.fittingInG_isNilpotent E
  obtain ⟨⟨hE₂ab, hE_norm_E₂⟩, hE₂hallG, hE₂eq⟩ :=
    E2_abelian_normal_hall_of_abelianSylow hG h hp hA hAE hSab
  have hchain := sylow_chain_of_abelianSylow hG h hp hA hAE hAS hSab
  set K : Subgroup G := E₂ ⊔ E₃ with hKdef
  have hE₃_le_FE : E₃ ≤ FE := E3_le_fittingInG hG h
  have hE₂_le_FE : E₂ ≤ FE := by rw [hE₂eq]; exact Subgroup.map_subtype_le _
  have hK_le_FE : K ≤ FE := sup_le hE₂_le_FE hE₃_le_FE
  have hK_le_M : K ≤ M := (sup_le h.E₂_le h.E₃_le).trans h.E_le
  -- `q ∈ τ₁(M)`.
  have hXne : X ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hX
  have hq1 : q ∈ tau1 M := by
    have hqdvd : q ∣ Nat.card ↥E₁ := by
      have h1 : Nat.card ↥X = q := by rw [hX.2, pow_one]
      rw [← h1]
      exact Subgroup.card_dvd_of_le hXE₁
    refine h.E₁_hall.1 q (Nat.mem_primeFactors.mpr ⟨hq_prime, ?_, Nat.card_pos.ne'⟩)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv]
  -- `K` is abelian.
  have hE₂E₃_comm : (⁅E₂, E₃⁆ : Subgroup G) = ⊥ := by
    rw [← le_bot_iff]
    have h1 : (⁅E₂, E₃⁆ : Subgroup G) ≤ E₂ ⊓ E₃ := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      constructor
      · have h2 : b * a⁻¹ * b⁻¹ ∈ E₂ := by
          have h3 := (Subgroup.mem_normalizer_iff.mp
            (hE_norm_E₂ (h.E₃_le hb)) a⁻¹).mp (E₂.inv_mem ha)
          exact h3
        have h4 : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by
          rw [commutatorElement_def]; group
        rw [h4]
        exact E₂.mul_mem ha h2
      · have h2 : a * b * a⁻¹ ∈ E₃ := by
          have h3 := (Subgroup.mem_normalizer_iff.mp
            (h.E3_normal hG (h.E₂_le ha)) b).mp hb
          exact h3
        have h4 : ⁅a, b⁆ = (a * b * a⁻¹) * b⁻¹ := by
          rw [commutatorElement_def]
        rw [h4]
        exact E₃.mul_mem h2 (E₃.inv_mem hb)
    refine h1.trans (le_of_eq ?_)
    refine (Subgroup.disjoint_of_coprime_natCard (coprime_of_forall_prime_not_dvd ?_)).eq_bot
    intro r hr h1' h2'
    have hr2 := hE₂hallG.1 r (Nat.mem_primeFactors.mpr ⟨hr, h1', Nat.card_pos.ne'⟩)
    have hr3 : r ∈ tau3 M := by
      refine h.E₃_hall.1 r (Nat.mem_primeFactors.mpr ⟨hr, ?_, Nat.card_pos.ne'⟩)
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv]
    have ha := tau2_pRank_eq_two hr2
    have hb := tau3_pRank_eq_one hr3
    omega
  have hE₃cyc : IsCyclic ↥E₃ := h.E3_isCyclic hG
  let : CommGroup ↥E₃ := IsCyclic.commGroup
  have hE₃ab : IsMulCommutative ↥E₃ := ⟨⟨fun a b => mul_comm a b⟩⟩
  have hKab : IsMulCommutative ↥K := by
    refine isMulCommutative_of_le_centralizer ?_
    rw [hKdef, centralizer_sup_eq]
    refine le_inf (sup_le (le_centralizer_of_le_of_le hE₂ab le_rfl le_rfl) ?_)
      (sup_le ?_ (le_centralizer_of_le_of_le hE₃ab le_rfl le_rfl))
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        ((Subgroup.commutator_comm E₃ E₂).trans hE₂E₃_comm)
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hE₂E₃_comm
  -- `F(E) ≤ C_G(K)`.
  have hE₃eq : E₃ = opiCoreInG (tau3 M) FE := by
    have hE₃pi : ∀ r ∈ (Nat.card ↥E₃).primeFactors, r ∈ tau3 M := by
      intro r hr
      refine h.E₃_hall.1 r ?_
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv]
    refine le_antisymm (piGroup_le_opiCoreInG_of_nilpotent hE₃pi hE₃_le_FE) ?_
    refine le_of_eq (Subgroup.eq_of_le_of_card_ge
      (piGroup_le_opiCoreInG_of_nilpotent hE₃pi hE₃_le_FE) ?_).symm
    refine Nat.le_of_dvd Nat.card_pos ?_
    refine card_opiCoreInG_dvd_of_nilpotent Nat.card_pos.ne' ?_
    intro r hr hr3
    -- `ν_r(F(E)) ≤ ν_r(E) = ν_r(E₃)` for `r ∈ τ₃`.
    have hFE_le : (Nat.card ↥FE).factorization r ≤ (Nat.card ↥E).factorization r :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
        (Subgroup.card_dvd_of_le (Ch2.S08.fittingInG_le E)) r
    have hidx : ((E₃.subgroupOf E).index).factorization r = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hdvd
      exact h.E₃_hall.2 r (Nat.mem_primeFactors.mpr
        ⟨hr, hdvd, Subgroup.index_ne_zero_of_finite⟩) hr3
    have hsum : (Nat.card ↥(E₃.subgroupOf E)).factorization r
        + ((E₃.subgroupOf E).index).factorization r
        = (Nat.card ↥E).factorization r := by
      rw [← Subgroup.card_mul_index (E₃.subgroupOf E),
        Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
        Finsupp.add_apply]
    have hcardc : (Nat.card ↥(E₃.subgroupOf E)).factorization r
        = (Nat.card ↥E₃).factorization r := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv]
    omega
  have hFE_le_CK : FE ≤ Subgroup.centralizer ((K : Subgroup G) : Set G) := by
    rw [hKdef, centralizer_sup_eq]
    refine le_inf ?_ ?_
    · have := fittingInG_le_centralizer_opiCoreInG (E := E) (π := tau2 M)
        (by rw [← hE₂eq]; exact hE₂ab)
      rwa [← hE₂eq] at this
    · have := fittingInG_le_centralizer_opiCoreInG (E := E) (π := tau3 M)
        (by rw [← hE₃eq]; exact hE₃ab)
      rwa [← hE₃eq] at this
  -- `⁅K, X⁆ = ⊥`.
  have hKX_bot : (⁅K, X⁆ : Subgroup G) = ⊥ := by
    by_contra hne
    set NS : Subgroup G := Subgroup.normalizer ((S : Subgroup G) : Set G) with hNSdef
    have hSE : (S : Subgroup G) ≤ E :=
      (le_centralizer_of_le_of_le hSab le_rfl hAS).trans
        (centralizer_le_E_of_tau2 hG h hp hA hAE).1
    have hSM : (S : Subgroup G) ≤ M := hSE.trans h.E_le
    have hS_le_K : (S : Subgroup G) ≤ K := by
      refine le_sup_of_le_left ?_
      rw [hE₂eq]
      refine piGroup_le_opiCoreInG_fittingInG ?_ (hchain.1.trans hchain.2.1)
      intro r hr
      rw [Sylow.card_eq_multiplicity] at hr
      have h1 := Nat.prime_of_mem_primeFactors hr
      have h2 := Nat.dvd_of_mem_primeFactors hr
      have : r = p := (Nat.prime_dvd_prime_iff_eq h1 Fact.out).mp (h1.dvd_of_dvd_pow h2)
      rwa [this]
    have hX_le_NS : X ≤ NS := by
      have hd := normalizer_chain_of_abelianSylow hG h hp hA hAE hAS hSab
      rw [hNSdef, hd.2.1]
      exact hXE.trans hE_norm_E₂
    have hK_norm_NS : NS ≤ Subgroup.normalizer ((K : Subgroup G) : Set G) := by
      have hd := normalizer_chain_of_abelianSylow hG h hp hA hAE hAS hSab
      rw [hNSdef, hd.2.1, hd.2.2.1]
    have hder_le_CK : derivedInG NS ≤ Subgroup.centralizer ((K : Subgroup G) : Set G) :=
      hchain.2.1.trans hFE_le_CK
    set HK : Subgroup G := Subgroup.centralizer ((K : Subgroup G) : Set G) ⊔ X
      with hHKdef
    have hCK_le_NS : Subgroup.centralizer ((K : Subgroup G) : Set G) ≤ NS :=
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hS_le_K)).trans
        (Subgroup.centralizer_le_normalizer _)
    have hHK_le_NS : HK ≤ NS := sup_le hCK_le_NS hX_le_NS
    have hNS_norm_HK : NS ≤ Subgroup.normalizer ((HK : Subgroup G) : Set G) := by
      have : (HK.subgroupOf NS).Normal := by
        refine Ch06.normal_of_commutator_le ?_
        intro y hy
        rw [Subgroup.mem_subgroupOf]
        exact Subgroup.mem_sup_left (hder_le_CK ⟨y, hy, rfl⟩)
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hHK_le_NS).mp inferInstance
    -- `⁅K, HK⁆ = ⁅K, X⁆`.
    have hcomm_eq : (⁅K, HK⁆ : Subgroup G) = ⁅K, X⁆ := by
      refine le_antisymm ?_ (Subgroup.commutator_mono le_rfl le_sup_right)
      rw [Subgroup.commutator_le]
      intro k hk g hg
      have hCnorm : ((Subgroup.centralizer ((K : Subgroup G) : Set G)).subgroupOf
          NS).Normal := by
        refine Ch06.normal_of_commutator_le ?_
        intro y hy
        rw [Subgroup.mem_subgroupOf]
        exact hder_le_CK ⟨y, hy, rfl⟩
      have hg' : (⟨g, hHK_le_NS hg⟩ : ↥NS) ∈ HK.subgroupOf NS :=
        Subgroup.mem_subgroupOf.mpr hg
      have hsplit : HK.subgroupOf NS
          = (Subgroup.centralizer ((K : Subgroup G) : Set G)).subgroupOf NS
            ⊔ X.subgroupOf NS := by
        rw [hHKdef]
        exact Subgroup.subgroupOf_sup hCK_le_NS hX_le_NS
      rw [hsplit] at hg'
      have hmul : (⟨g, hHK_le_NS hg⟩ : ↥NS) ∈
          ((Subgroup.centralizer ((K : Subgroup G) : Set G)).subgroupOf NS : Set ↥NS)
            * (X.subgroupOf NS : Set ↥NS) := by
        rw [← Subgroup.normal_mul]
        exact hg'
      obtain ⟨c, hc, x, hx, hcx⟩ := hmul
      have hgcx : g = (c : G) * (x : G) := by
        have := congrArg Subtype.val hcx
        simpa using this.symm
      have hcC : (c : G) ∈ Subgroup.centralizer ((K : Subgroup G) : Set G) :=
        Subgroup.mem_subgroupOf.mp hc
      have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
      have hkc : (c : G) * k = k * c :=
        (Subgroup.mem_centralizer_iff.mp hcC k hk).symm
      have hkxK : ⁅k, (x : G)⁆ ∈ K := by
        have hxN : (x : G) ∈ Subgroup.normalizer ((K : Subgroup G) : Set G) :=
          hK_norm_NS (hX_le_NS hxX)
        have h1 : (x : G) * k⁻¹ * (x : G)⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp hxN k⁻¹).mp (K.inv_mem hk)
        have h3 : ⁅k, (x : G)⁆ = k * ((x : G) * k⁻¹ * (x : G)⁻¹) := by
          rw [commutatorElement_def]; group
        rw [h3]
        exact K.mul_mem hk h1
      have hkey : ⁅k, g⁆ = ⁅k, (x : G)⁆ := by
        rw [hgcx]
        have hcfix : (c : G) * ⁅k, (x : G)⁆ * (c : G)⁻¹ = ⁅k, (x : G)⁆ := by
          have h0 := Subgroup.mem_centralizer_iff.mp hcC _ hkxK
          calc (c : G) * ⁅k, (x : G)⁆ * (c : G)⁻¹
              = ⁅k, (x : G)⁆ * (c : G) * (c : G)⁻¹ := by rw [← h0]
            _ = ⁅k, (x : G)⁆ := by group
        calc ⁅k, (c : G) * (x : G)⁆
            = k * ((c : G) * (x : G)) * k⁻¹ * ((c : G) * (x : G))⁻¹ := by
              rw [commutatorElement_def]
          _ = (c : G) * (k * (x : G) * k⁻¹ * (x : G)⁻¹) * (c : G)⁻¹ := by
              rw [show k * ((c : G) * (x : G)) = (c : G) * (k * (x : G)) from by
                rw [← mul_assoc, ← hkc, mul_assoc]]
              group
          _ = (c : G) * ⁅k, (x : G)⁆ * (c : G)⁻¹ := by rw [commutatorElement_def]
          _ = ⁅k, (x : G)⁆ := hcfix
      rw [hkey]
      exact Subgroup.commutator_mem_commutator hk hxX
    -- `N_G(S) ≤ N_G(⁅K,X⁆)`.
    have hNS_norm_KX : NS ≤
        Subgroup.normalizer ((⁅K, X⁆ : Subgroup G) : Set G) := by
      rw [← hcomm_eq]
      intro n hn
      refine mem_normalizer_of_conj_smul_eq_self ?_
      rw [mulAut_smul_eq_map, Subgroup.map_commutator, ← mulAut_smul_eq_map,
        ← mulAut_smul_eq_map, conj_smul_eq_self_of_mem_normalizer (hK_norm_NS hn),
        conj_smul_eq_self_of_mem_normalizer (hNS_norm_HK hn)]
    -- Proposition 10.11(d): `M ≤ N_G(⁅K,X⁆)`.
    have hE₂E₃_bot : E₂ ⊓ E₃ = ⊥ := by
      refine (Subgroup.disjoint_of_coprime_natCard (coprime_of_forall_prime_not_dvd ?_)).eq_bot
      intro r hr h1' h2'
      have hr2 := hE₂hallG.1 r (Nat.mem_primeFactors.mpr ⟨hr, h1', Nat.card_pos.ne'⟩)
      have hr3 : r ∈ tau3 M := by
        refine h.E₃_hall.1 r (Nat.mem_primeFactors.mpr ⟨hr, ?_, Nat.card_pos.ne'⟩)
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv]
      have ha := tau2_pRank_eq_two hr2
      have hb := tau3_pRank_eq_one hr3
      omega
    have hcard_K : Nat.card ↥K = Nat.card ↥E₂ * Nat.card ↥E₃ :=
      card_sup_eq_mul_of_le_normalizer_of_disjoint
        (h.E₂_le.trans (h.E3_normal hG)) hE₂E₃_bot
    have hK_primes : ∀ r ∈ (Nat.card ↥K).primeFactors, r ∈ tau2 M ∪ tau3 M := by
      intro r hr
      have hr_prime := Nat.prime_of_mem_primeFactors hr
      have hdvd := Nat.dvd_of_mem_primeFactors hr
      rw [hcard_K] at hdvd
      rcases (Nat.Prime.dvd_mul hr_prime).mp hdvd with h1 | h1
      · exact Or.inl (hE₂hallG.1 r (Nat.mem_primeFactors.mpr
          ⟨hr_prime, h1, Nat.card_pos.ne'⟩))
      · refine Or.inr (h.E₃_hall.1 r (Nat.mem_primeFactors.mpr ⟨hr_prime, ?_,
          Nat.card_pos.ne'⟩))
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv]
    have h1011 := S10.sigma_complement_commutator_cyclic_normal hG h.mem_maximal
      hK_le_M
      (fun r hr => by
        rcases hK_primes r hr with h1 | h1
        · exact tau2_subset_sigma_compl M h1
        · exact tau3_subset_sigma_compl M h1)
      (tau1_subset_sigma_compl M hq1) hX
      (le_inf (hXE.trans (le_normalizer_sup hE_norm_E₂ (h.E3_normal hG)))
        (hXE.trans h.E_le))
      hCX hKab
      (fun r hr => by
        rcases hK_primes r hr with h1 | h1
        · intro hrq
          rw [Set.mem_singleton_iff] at hrq
          subst hrq
          have ha := tau1_pRank_eq_one hq1
          have hb := tau2_pRank_eq_two h1
          omega
        · intro hrq
          rw [Set.mem_singleton_iff] at hrq
          subst hrq
          exact not_mem_tau3_of_mem_tau1 hq1 h1)
    have hM_norm : M ≤ Subgroup.normalizer ((⁅K, X⁆ : Subgroup G) : Set G) :=
      h1011.2.2
    -- maximality forces `N_G(⁅K,X⁆) = M`, contradicting `N_G(S) ⊄ M`.
    have hKX_le_M : (⁅K, X⁆ : Subgroup G) ≤ M := by
      rw [Subgroup.commutator_le]
      intro k hk x hx
      have hkM : k ∈ M := hK_le_M hk
      have hxM : x ∈ M := (hXE.trans h.E_le) hx
      rw [commutatorElement_def]
      exact M.mul_mem (M.mul_mem (M.mul_mem hkM hxM) (M.inv_mem hkM)) (M.inv_mem hxM)
    have hlt := normalizer_lt_top_of_le_of_ne_bot hG h.mem_maximal hKX_le_M hne
    have hN_eq_M : Subgroup.normalizer ((⁅K, X⁆ : Subgroup G) : Set G) = M := by
      rcases (lt_or_eq_of_le hM_norm) with h1 | h1
      · exact absurd ((mem_maximalSubgroups.mp h.mem_maximal).2 _ h1) hlt.ne
      · exact h1.symm
    have hSM' := (normalizer_sylow_le_normalizer_elemAb hG h hp hA hAE hAS hSM).2
    exact hSM' (hN_eq_M ▸ hNS_norm_KX)
  -- conclude.
  have hK_le_CX : K ≤ Subgroup.centralizer (X : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKX_bot
  have hE₁cyc : IsCyclic ↥E₁ := h.E1_isCyclic hG
  let : CommGroup ↥E₁ := IsCyclic.commGroup
  have hE₁ab : IsMulCommutative ↥E₁ := ⟨⟨fun a b => mul_comm a b⟩⟩
  have hE₁_le_CX : E₁ ≤ Subgroup.centralizer (X : Set G) :=
    le_centralizer_of_le_of_le hE₁ab le_rfl hXE₁
  have hEeq : E = E₁ ⊔ K := by
    rw [hKdef, show E = E₁ ⊔ E₂ ⊔ E₃ from h.eq_sup hG, sup_assoc]
  rw [hEeq]
  exact sup_le hE₁_le_CX hK_le_CX

/-- **BG Lemma 12.8** (mmd L3253): `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)`, `S` an **abelian**
Sylow `p`-subgroup of `G` containing `A`. Then
(a) `E₂` is an abelian normal subgroup of `E`;
(b) `E₂` is a Hall `τ₂(M)`-subgroup of `G`;
(c) `S ⊆ N_G(S)' ⊆ F(E) ⊆ C_G(S) ⊆ E`;
(d) `N_G(A) = N_G(S) = N_G(E₂) = N_G(E₂E₃) = N_G(F(E))`;
(e) every `X ∈ ℰ¹(E₁)` with `C_{M_σ}(X) = 1` lies in `Z(E)`; and
(f) for `X ≤ N_G(S)`, both `C_S(X)` and `⁅S,X⁆` are normal in `N_G(S)`. -/
theorem E2_abelian_of_abelianSylow [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    (S : Sylow p G) (hAS : A ≤ (S : Subgroup G))
    (hSab : IsMulCommutative (S : Subgroup G)) :
    (IsMulCommutative ↥E₂ ∧ E ≤ Subgroup.normalizer (E₂ : Set G)) ∧
    Ch03.IsHallSubgroup (tau2 M) E₂ ∧
    ((S : Subgroup G) ≤ derivedInG (Subgroup.normalizer ((S : Subgroup G) : Set G)) ∧
      derivedInG (Subgroup.normalizer ((S : Subgroup G) : Set G)) ≤
        Ch2.S08.fittingInG E ∧
      Ch2.S08.fittingInG E ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) ∧
      Subgroup.centralizer ((S : Subgroup G) : Set G) ≤ E) ∧
    (Subgroup.normalizer (A : Set G) = Subgroup.normalizer ((S : Subgroup G) : Set G) ∧
      Subgroup.normalizer ((S : Subgroup G) : Set G) = Subgroup.normalizer (E₂ : Set G) ∧
      Subgroup.normalizer (E₂ : Set G)
        = Subgroup.normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) ∧
      Subgroup.normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) =
        Subgroup.normalizer ((Ch2.S08.fittingInG E : Subgroup G) : Set G)) ∧
    (∀ X : Subgroup G, (∃ q : ℕ, q.Prime ∧ X ∈ elemAbelianOfRank G q 1) → X ≤ E₁ →
      S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) = ⊥ →
      X ≤ E ∧ E ≤ Subgroup.centralizer (X : Set G)) ∧
    (∀ X : Subgroup G, X ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) →
      Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
        Subgroup.normalizer
          (((S : Subgroup G) ⊓ Subgroup.centralizer (X : Set G)) : Set G) ∧
      Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((⁅(S : Subgroup G), X⁆ : Subgroup G) : Set G)) := by
  obtain ⟨hab, hhall, _⟩ := E2_abelian_normal_hall_of_abelianSylow hG h hp hA hAE hSab
  exact ⟨hab, hhall,
    sylow_chain_of_abelianSylow hG h hp hA hAE hAS hSab,
    normalizer_chain_of_abelianSylow hG h hp hA hAE hAS hSab,
    central_line_of_abelianSylow hG h hp hA hAE hAS hSab,
    relative_normality_of_abelianSylow hG h hp hA hAE hAS hSab⟩

end OddOrder.BG.Ch3.S12


