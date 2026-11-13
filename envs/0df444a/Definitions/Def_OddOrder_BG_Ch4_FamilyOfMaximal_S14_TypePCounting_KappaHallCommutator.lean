-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_KappaHallCommutator
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_KappaHallCommutator
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T09:29:55.991577+00:00
-- url     : https://prove2.me/theorems/a249a9d4-d810-4ab2-a7bb-a055917c6716
-- title:
--   BG §14: $\kappa$-Hall commutator results (Lemma 14.11)
-- statement:
--   A part of the §14 global counting development of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, split off from the global-counting file, around Lemma 14.11: for $M\in\mathcal{M}_F$ and related hypotheses, steps S4–S7 giving a cyclic commutator complement of type $F$, and the degenerate case S5 ($Q\le E$ abelian). It also covers results such as `typeP2_kappaHall_commutator_eq_self` and `typeP2_neighbor_is_typeF`.
--
--   Main declarations: `Q_le_fittingInG_of_commutator_centralizesQ` (BG Lemma 14.11, step S5 (degenerate case)); `exists_typeF_complement_cyclic_commutator`.
--
--   The bundle also proves 15 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/KappaHallCommutator.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/KappaHallCommutator.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_TypePDuality

namespace OddOrder.BG.Ch4.S14

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch3.S13

open scoped Pointwise

variable {G : Type*} [Group G]

/-- Build a `SubgroupESetup` on a *given* `M_σ`-complement `E` (converting the `IsComplement'`
hypothesis to the `M_σ ⊓ E = ⊥`, `M_σ ⊔ E = M` form expected by `subgroupESetup_of_complement`). -/
theorem esetup_of_isComplement [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hE : Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (E.subgroupOf M))
    (hEM : E ≤ M) :
    ∃ E₁ E₂ E₃ : Subgroup G, SubgroupESetup M E E₁ E₂ E₃ := by
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hinf : OddOrder.BG.Ch3.S10.Msigma M ⊓ E = ⊥ := by
    have hd := hE.disjoint
    rw [disjoint_iff] at hd
    have h2 : (OddOrder.BG.Ch3.S10.Msigma M ⊓ E).subgroupOf M = ⊥ := by
      have he : (OddOrder.BG.Ch3.S10.Msigma M ⊓ E).subgroupOf M
          = (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M ⊓ E.subgroupOf M :=
        Subgroup.comap_inf _ _ M.subtype
      rw [he]; exact hd
    have h3 := congrArg (Subgroup.map M.subtype) h2
    rwa [Subgroup.map_subgroupOf_eq_of_le (inf_le_of_left_le hMσM), Subgroup.map_bot] at h3
  have hsup : OddOrder.BG.Ch3.S10.Msigma M ⊔ E = M := by
    have hs := hE.sup_eq_top
    have h3 := congrArg (Subgroup.map M.subtype) hs
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hMσM,
      Subgroup.map_subgroupOf_eq_of_le hEM, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h3
    exact h3
  exact subgroupESetup_of_complement hG hM hEM hinf hsup

/-- BG Lemma 14.11 step S1: `q ∉ τ₂(M)`.  A rank-2 elem abelian `B ∈ ℰ_q²(E)` is normal in `E`
(Cor 12.6(a)) hence `≤ F(E)`; line-membership forces `Q ≤ B ≤ F(E)`, contradicting `Q ⊄ F(E)`. -/
theorem typeF_complement_q_notMem_tau2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ Q : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hsetup : SubgroupESetup M E E₁ E₂ E₃)
    (hQ : Q ∈ elemAbelianOfRank G q 1) (hQE : Q ≤ E)
    (hQF : ¬ Q ≤ OddOrder.BG.Ch2.S08.fittingInG E) :
    q ∉ tau2 M := by
  intro hτ2
  obtain ⟨B, hB, hBE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG hsetup hτ2
  obtain ⟨⟨hENB, hline⟩, _⟩ := elemAb_normal_in_E_of_tau2 hG hsetup hτ2 hB hBE
  have hQB : Q ≤ B := (hline Q hQ).mp hQE
  have hBnorm : (B.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBE).mpr hENB
  have hBpi : Subgroup.IsPiSubgroup ({q} : Set ℕ) B := by
    intro p hp
    rw [hB.2, Nat.primeFactors_prime_pow (by norm_num) (Fact.out : q.Prime),
      Finset.mem_singleton] at hp
    exact hp
  have hBF : B ≤ OddOrder.BG.Ch2.S08.fittingInG E :=
    OddOrder.BG.Ch2.S08.le_fittingInG_of_normal_isPiSubgroup_singleton hBE hBnorm hBpi
  exact hQF (hQB.trans hBF)

/-- BG Lemma 14.11 step S2: `q ∉ τ₃(M)`.  The τ₃-Hall `E₃` is cyclic, normal in `E`, hence `≤ F(E)`
(`E3_le_fittingInG`); a `q`-subgroup with `q ∈ τ₃` lands in `E₃`, so `Q ≤ E₃ ≤ F(E)`. -/
theorem typeF_complement_q_notMem_tau3 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ Q : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hsetup : SubgroupESetup M E E₁ E₂ E₃)
    (hQ : Q ∈ elemAbelianOfRank G q 1) (hQE : Q ≤ E)
    (hQF : ¬ Q ≤ OddOrder.BG.Ch2.S08.fittingInG E) :
    q ∉ tau3 M := by
  intro hτ3
  have hE₃norm : (E₃.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hsetup.E₃_le).mpr (hsetup.E3_normal hG)
  have hQcard : Nat.card ↥Q = q := by rw [hQ.2, pow_one]
  have hQpiG : Ch03.Subgroup.IsPiGroup (tau3 M) (Q.subgroupOf E) := by
    intro r hr
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQE).toEquiv, hQcard,
      (Fact.out : q.Prime).primeFactors, Finset.mem_singleton] at hr
    exact hr ▸ hτ3
  have hle : Q.subgroupOf E ≤ E₃.subgroupOf E :=
    OddOrder.BG.Ch3.S10.isPiGroup_le_of_normal_isHallSubgroup hsetup.E₃_hall hQpiG
  have hQE₃ : Q ≤ E₃ := by
    have := Subgroup.map_mono (f := E.subtype) hle
    rwa [Subgroup.map_subgroupOf_eq_of_le hQE,
      Subgroup.map_subgroupOf_eq_of_le hsetup.E₃_le] at this
  exact hQF (hQE₃.trans (E3_le_fittingInG hG hsetup))

/-- BG Lemma 14.11 steps S1–S3 + gap C: `Q ⊄ F(E)` with `M ∈ 𝓜_F` forces `q ∈ τ₁(M)` and
`C_{M_σ}(Q) = 1`.  (`q ∈ π(E) ⊆ σ(M)'` is τ-covered; S1/S2 rule out τ₂/τ₃; a nontrivial
`C_{M_σ}(Q)` would place `q ∈ κ(M) = ∅`.) -/
theorem typeF_complement_q_tau1_and_centralizer [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ Q : Subgroup G} {q : ℕ}
    (hsetup : SubgroupESetup M E E₁ E₂ E₃) (hF : IsTypeF M)
    (hq : q ∈ piSet E) (hQ : Q ∈ elemAbelianOfRank G q 1) (hQE : Q ≤ E)
    (hQF : ¬ Q ≤ OddOrder.BG.Ch2.S08.fittingInG E) :
    q ∈ tau1 M ∧ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (Q : Set G) = ⊥ := by
  have hqpf : q ∈ (Nat.card ↥E).primeFactors := hq
  have : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hqpf⟩
  have hqτ1 : q ∈ tau1 M := by
    rcases hsetup.mem_tau_union_of_mem_primeFactors hG hqpf with (h | h) | h
    · exact h
    · exact absurd h (typeF_complement_q_notMem_tau2 hG hsetup hQ hQE hQF)
    · exact absurd h (typeF_complement_q_notMem_tau3 hG hsetup hQ hQE hQF)
  have hQM : Q ≤ M := hQE.trans hsetup.E_le
  refine ⟨hqτ1, ?_⟩
  by_contra hne
  exact Set.notMem_empty q (hF ▸ (⟨Fact.out, Or.inl hqτ1, Q, hQ, hQM, hne⟩ : q ∈ kappa M))

open scoped IsMulCommutative commutatorElement in
/-- **BG Lemma 14.11, step S5 (degenerate case).**  If `Q ≤ E` is abelian, `R := ⁅E, Q⁆` is
abelian, and `R` centralizes `Q` (equivalently `⁅⁅E, Q⁆, Q⁆ = 1`), then the normal closure
`Q ⊔ R` of `Q` in `E` is abelian and normal in `E`, hence `Q ≤ F(E)`.  This is used to rule out
`⁅⁅E, Q⁆, Q⁆ = 1` when `Q ⊄ F(E)`: the set of `x` with `⁅x, e⁆ ∈ Q ⊔ R` is a subgroup containing
the generators `Q` and `R`, so `Q ⊔ R` is `E`-normal; it is abelian by `R ≤ C_G(Q)`. -/
private theorem Q_le_fittingInG_of_commutator_centralizesQ [Finite G]
    {E Q : Subgroup G} (hQE : Q ≤ E) (hQab : IsMulCommutative ↥Q)
    (hRab : IsMulCommutative ↥(⁅E, Q⁆ : Subgroup G))
    (hC : (⁅E, Q⁆ : Subgroup G) ≤ Subgroup.centralizer (Q : Set G)) :
    Q ≤ OddOrder.BG.Ch2.S08.fittingInG E := by
  classical
  set R : Subgroup G := ⁅E, Q⁆ with hRdef
  have hRE : R ≤ E := (Subgroup.commutator_mono le_rfl hQE).trans (Subgroup.commutator_le_self E)
  have hNE : Q ⊔ R ≤ E := sup_le hQE hRE
  have hRnorm : E ≤ Subgroup.normalizer (R : Set G) :=
    hRdef ▸ Ch04.subgroup_le_normalizer_commutator_self E Q
  have hRE_comm : (⁅R, E⁆ : Subgroup G) ≤ R := Ch04.commutator_le_of_le_normalizer hRnorm
  have hC' : Q ≤ Subgroup.centralizer (R : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hC
  -- `Q ⊔ R` is normalized by `E`.
  have hEnormN : E ≤ Subgroup.normalizer ((Q ⊔ R : Subgroup G) : Set G) := by
    refine Ch04.le_normalizer_of_commutator_le ?_
    rw [Subgroup.commutator_le]
    intro n hn e he
    let Se : Subgroup G :=
      { carrier := {x | x ∈ (Q ⊔ R : Subgroup G) ∧ ⁅x, e⁆ ∈ (Q ⊔ R : Subgroup G)}
        one_mem' := ⟨one_mem _, by rw [commutatorElement_one_left]; exact one_mem _⟩
        mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
          have hid : ⁅a * b, e⁆ = a * ⁅b, e⁆ * a⁻¹ * ⁅a, e⁆ := by
            simp only [commutatorElement_def]; group
          rw [hid]
          exact mul_mem (mul_mem (mul_mem ha.1 hb.2) (inv_mem ha.1)) ha.2⟩
        inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
          have hid : ⁅a⁻¹, e⁆ = a⁻¹ * ⁅a, e⁆⁻¹ * a := by
            simp only [commutatorElement_def]; group
          rw [hid]
          exact mul_mem (mul_mem (inv_mem ha.1) (inv_mem ha.2)) ha.1⟩ }
    have hQSe : Q ≤ Se := fun x hx => ⟨Subgroup.mem_sup_left hx, by
      refine Subgroup.mem_sup_right ?_
      rw [hRdef, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hx he⟩
    have hRSe : R ≤ Se := fun x hx => ⟨Subgroup.mem_sup_right hx,
      Subgroup.mem_sup_right (hRE_comm (Subgroup.commutator_mem_commutator hx he))⟩
    exact ((sup_le hQSe hRSe : (Q ⊔ R) ≤ Se) hn).2
  have hNnorm : ((Q ⊔ R).subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNE).mpr hEnormN
  have hNab : IsMulCommutative ↥(Q ⊔ R : Subgroup G) := by
    refine isMulCommutative_of_le_centralizer ?_
    rw [centralizer_sup_eq]
    exact le_inf (sup_le (le_centralizer_of_le_of_le hQab le_rfl le_rfl) hC)
      (sup_le hC' (le_centralizer_of_le_of_le hRab le_rfl le_rfl))
  have : IsMulCommutative ↥(Q ⊔ R : Subgroup G) := hNab
  have : Group.IsNilpotent ↥(Q ⊔ R : Subgroup G) := inferInstance
  have : Group.IsNilpotent ↥((Q ⊔ R).subgroupOf E) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNE).symm
  have hfit : (Q ⊔ R).subgroupOf E ≤ OddOrder.Isaacs.Ch01.fitting ↥E :=
    Ch01.nilpotent_normal_le_fitting
  have hNfitG : (Q ⊔ R : Subgroup G) ≤ OddOrder.BG.Ch2.S08.fittingInG E := by
    have hmap := Subgroup.map_mono (f := E.subtype) hfit
    rwa [Subgroup.map_subgroupOf_eq_of_le hNE] at hmap
  exact le_sup_left.trans hNfitG

open OddOrder.BG.Ch3.S10 in
/-- **BG Lemma 14.11, steps S4–S7**: under the Lemma 14.11 hypotheses (`M ∈ 𝓜_F`, `E` a
`M_σ`-complement, `q ∈ π(E)`, `Q ∈ ℰ_q¹(E)`, `Q ⊄ F(E)`), there is a nontrivial cyclic subgroup
`K' = ⁅⁅E, Q⁆, Q⁆ ≤ E` that is normal in `M`, contained in `C_G(M_σ)`, has all primes in `τ₂(M)`
(so `τ₂(M) ≠ ∅`), and on which `Q` acts fixed-point-freely (`C_{K'}(Q) = 1`).

`K := ⁅E, Q⁆` is an abelian (Cor 12.10(b)) `q'`-subgroup of `M` normalized by `Q`; Proposition
10.11(d) makes `K' := ⁅K, Q⁆` cyclic, normal in `M`, and contained in `C_G(M_σ)`.  If `K' = 1`
then `⁅E, Q⁆ ≤ C_G(Q)` and `Q ≤ F(E)` (the S5 helper), contradicting `Q ⊄ F(E)`; so `K' ≠ 1`.
A prime `p ∈ π(K')` lies in `τ₂(M)`: otherwise `p ∈ τ₁(M) ∪ τ₃(M)` has `r_p(M) = 1`, and a line
`A ∈ ℰ_p¹` of `K' ≤ C_G(M_σ)` would have `C_{M_σ}(A) = M_σ ≠ 1`, contradicting Lemma 14.1.  The
`C_{K'}(Q) = 1` fixed-point-freeness comes from the coprime identity `⁅K', Q⁆ = K'` (BG **G** 8.5.4,
`commutator_commutator_right_eq` in `↥E`) and the coprime complement
`fitting_coprime_abelian_decomp`. -/
theorem exists_typeF_complement_cyclic_commutator [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ Q : Subgroup G} {q : ℕ}
    (hsetup : SubgroupESetup M E E₁ E₂ E₃) (hF : IsTypeF M)
    (hq : q ∈ piSet E) (hQ : Q ∈ elemAbelianOfRank G q 1) (hQE : Q ≤ E)
    (hQF : ¬ Q ≤ OddOrder.BG.Ch2.S08.fittingInG E) :
    ∃ K' : Subgroup G,
      K' ≤ E ∧ K' ≠ ⊥ ∧ IsCyclic ↥K' ∧
      K' ≤ Subgroup.centralizer (Msigma M : Set G) ∧
      M ≤ Subgroup.normalizer (K' : Set G) ∧
      (∀ p ∈ (Nat.card ↥K').primeFactors, p ∈ tau2 M) ∧
      Subgroup.centralizer (Q : Set G) ⊓ K' = ⊥ := by
  classical
  have hqpf : q ∈ (Nat.card ↥E).primeFactors := hq
  have : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hqpf⟩
  obtain ⟨hqτ1, hCQ⟩ := typeF_complement_q_tau1_and_centralizer hG hsetup hF hq hQ hQE hQF
  have hQM : Q ≤ M := hQE.trans hsetup.E_le
  -- `K := ⁅E, Q⁆` is an abelian `q'`-subgroup of `M`, `σ(M)'`-subgroup.
  set K : Subgroup G := ⁅E, Q⁆ with hKdef
  have hK_le_derivedE : K ≤ derivedInG E := by
    rw [hKdef, show derivedInG E = ⁅E, E⁆ from Subgroup.map_subtype_commutator E]
    exact Subgroup.commutator_mono le_rfl hQE
  have hKE : K ≤ E := hK_le_derivedE.trans (Subgroup.map_subtype_le _)
  have hKM : K ≤ M := hKE.trans hsetup.E_le
  have hK_le_derivedM : K ≤ derivedInG M := by
    rw [hKdef, show derivedInG M = ⁅M, M⁆ from Subgroup.map_subtype_commutator M]
    exact Subgroup.commutator_mono hsetup.E_le hQM
  have hKab : IsMulCommutative ↥K :=
    isMulCommutative_of_le ((nilpotent_sigmaComplement_abelian hG hsetup).2.1.2) hK_le_derivedE
  have hKσ' : Subgroup.IsPiSubgroup (sigma M)ᶜ K := by
    intro p hp
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    have hpE : p ∈ (Nat.card ↥E).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpp, hpd.trans (Subgroup.card_dvd_of_le hKE), Nat.card_pos.ne'⟩
    rcases hsetup.mem_tau_union_of_mem_primeFactors hG hpE with (h | h) | h
    · exact tau1_subset_sigma_compl M h
    · exact tau2_subset_sigma_compl M h
    · exact tau3_subset_sigma_compl M h
  have hKq' : Subgroup.IsPiSubgroup (({q} : Set ℕ)ᶜ) K := by
    intro p hp
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    have hpM' : p ∈ (Nat.card ↥(derivedInG M)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpp, hpd.trans (Subgroup.card_dvd_of_le hK_le_derivedM),
        Nat.card_pos.ne'⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    exact tau1_not_mem_derived_primeFactors hqτ1 hpM'
  have hQNK : Q ≤ Subgroup.normalizer (K : Set G) ⊓ M :=
    le_inf (hQE.trans (hKdef ▸ Ch04.subgroup_le_normalizer_commutator_self E Q)) hQM
  -- Proposition 10.11(d): `K' := ⁅K, Q⁆ ≤ C_G(M_σ)`, cyclic, `M ≤ N_G(K')`.
  obtain ⟨hK'cent, hK'cyc, hMNK'⟩ :=
    sigma_complement_commutator_cyclic_normal hG hsetup.mem_maximal hKM hKσ' hqτ1.1 hQ hQNK hCQ
      hKab hKq'
  set K' : Subgroup G := ⁅K, Q⁆ with hK'def
  have hK'_le_K : K' ≤ K := hK'def ▸ Ch04.commutator_le_of_le_normalizer (le_inf_iff.mp hQNK).1
  have hK'E : K' ≤ E := hK'_le_K.trans hKE
  -- S5: `K' ≠ ⊥` (else `Q ≤ F(E)`).
  have hK'ne : K' ≠ ⊥ := by
    intro hbot
    apply hQF
    have hQab : IsMulCommutative ↥Q := ⟨⟨hQ.1.comm⟩⟩
    rw [hK'def, Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
    exact Q_le_fittingInG_of_commutator_centralizesQ hQE hQab (hKdef ▸ hKab) (hKdef ▸ hbot)
  -- Every prime of `K'` lies in `τ₂(M)`.
  have hπτ2 : ∀ p ∈ (Nat.card ↥K').primeFactors, p ∈ tau2 M := by
    intro p hp
    obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
    have : Fact p.Prime := ⟨hpp⟩
    by_contra hpτ2
    have hpE : p ∈ (Nat.card ↥E).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpp, hpd.trans (Subgroup.card_dvd_of_le hK'E), Nat.card_pos.ne'⟩
    have hpτ : p ∈ tau1 M ∪ tau2 M ∪ tau3 M := hsetup.mem_tau_union_of_mem_primeFactors hG hpE
    have hr1 : pRank ↥M p = 1 := by
      rcases hpτ with (h | h) | h
      · exact h.2.2
      · exact absurd h hpτ2
      · exact h.2.2
    obtain ⟨a, hacard⟩ := exists_prime_orderOf_dvd_card' (G := ↥K') p hpd
    set A : Subgroup G := Subgroup.zpowers (a : G) with hAdef
    have hAK' : A ≤ K' := by rw [hAdef, Subgroup.zpowers_le]; exact a.2
    have haGcard : orderOf (a : G) = p :=
      (orderOf_injective K'.subtype K'.subtype_injective a).trans hacard
    have hAcard : Nat.card ↥A = p := by rw [hAdef, Nat.card_zpowers]; exact haGcard
    have hAelem : A.IsElementaryAbelian p := Subgroup.IsElementaryAbelian.of_card_prime hAcard
    have hA : A ∈ elemAbelianOfRank G p (pRank ↥M p) := by
      rw [hr1, mem_elemAbelianOfRank]; exact ⟨hAelem, by rw [hAcard, pow_one]⟩
    have hpπ : p ∈ piSet M :=
      Nat.mem_primeFactors.mpr ⟨hpp, hpd.trans (Subgroup.card_dvd_of_le (hK'E.trans hsetup.E_le)),
        Nat.card_pos.ne'⟩
    have hpσ : p ∉ sigma M := by
      rcases hpτ with (h | h) | h
      · exact tau1_subset_sigma_compl M h
      · exact tau2_subset_sigma_compl M h
      · exact tau3_subset_sigma_compl M h
    have hpκ : p ∉ kappa M := by rw [hF]; exact Set.notMem_empty p
    have hAM : A ≤ M := hAK'.trans (hK'E.trans hsetup.E_le)
    obtain ⟨_, hCA, _⟩ := msigma_structure_of_notMem_sigma_kappa hG hsetup.mem_maximal hpπ hpσ hpκ
        hA hAM
    have hAcent : A ≤ Subgroup.centralizer (Msigma M : Set G) := hAK'.trans hK'cent
    have hMσcentA : Msigma M ≤ Subgroup.centralizer (A : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm,
        Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hAcent
    have hinf : Msigma M ⊓ Subgroup.centralizer (A : Set G) = Msigma M :=
      inf_eq_left.mpr hMσcentA
    rw [hCA] at hinf
    exact Msigma_ne_bot hG hsetup.mem_maximal hinf.symm
  -- `Q` acts fixed-point-freely on `K'`: coprime identity `⁅K', Q⁆ = K'`.
  have hqprime : q.Prime := Fact.out
  have hK'ab : IsMulCommutative ↥K' := isMulCommutative_of_le (hKdef ▸ hKab) hK'_le_K
  have hQNK' : Q ≤ Subgroup.normalizer (K' : Set G) := hQM.trans hMNK'
  have hqnK : ¬ q ∣ Nat.card ↥K := fun hdvd =>
    hKq' q (Nat.mem_primeFactors.mpr ⟨hqprime, hdvd, Nat.card_pos.ne'⟩) rfl
  have hQcard : Nat.card ↥Q = q := by rw [hQ.2, pow_one]
  have hcopKQ : Nat.Coprime (Nat.card ↥K) (Nat.card ↥Q) := by
    rw [hQcard]; exact (hqprime.coprime_iff_not_dvd.mpr hqnK).symm
  have hqnK' : ¬ q ∣ Nat.card ↥K' := fun hdvd =>
    hqnK (hdvd.trans (Subgroup.card_dvd_of_le hK'_le_K))
  have hcopK'Q : Nat.Coprime (Nat.card ↥K') (Nat.card ↥Q) := by
    rw [hQcard]; exact (hqprime.coprime_iff_not_dvd.mpr hqnK').symm
  have hident : (⁅K', Q⁆ : Subgroup G) = K' := by
    have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hsetup.mem_maximal
    have : Group.IsSolvable ↥(K ⊔ Q) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (sup_le hKM hQM))
    have hid := commutator_commutator_right_eq_of_le_normalizer (D := K) (Q := Q)
      ‹Group.IsSolvable ↥(K ⊔ Q)› (le_inf_iff.mp hQNK).1 hcopKQ
    rw [← hK'def] at hid
    exact hid
  have hFPF : Subgroup.centralizer (Q : Set G) ⊓ K' = ⊥ := by
    obtain ⟨hdisj, -⟩ :=
      OddOrder.Isaacs.Ch05.fitting_coprime_abelian_decomp (P := K') (K := Q) hQNK' hcopK'Q
    rwa [hident, inf_assoc, inf_idem] at hdisj
  exact ⟨K', hK'E, hK'ne, hK'cyc, hK'cent, hMNK', hπτ2, hFPF⟩

/-- **BG Lemma 14.11, A-choice**: for a normal line `L ◁ M` of order `p` with `p ∈ τ₂(M)` and
`L ≤ E`, there is `A ∈ ℰ_p²(E)` with `L ≤ A`.

`N_G(L) = M` (as `M ≤ N_G(L) < ⊤` and `M` is maximal), so BG Lemma 10.5
(`pRank_eq_two_of_normalizer_le`) yields `A₀ ∈ ℰ_p²(G)` with `L ≤ A₀`; `A₀` is abelian and
contains `L`, so `A₀ ≤ C_G(L) ≤ N_G(L) = M`.  As a `τ₂`-subgroup of `M`, `A₀` conjugates into the
`τ₂`-Hall `E₂ ≤ E` by some `w ∈ M` (`exists_conj_smul_le_hallPiece`); `L` is `M`-invariant so
`L = L^w ≤ A₀^w`, and `A₀^w ∈ ℰ_p²(E)`. -/
theorem exists_elemAb_rank_two_le_E_containing_line [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ L : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hsetup : SubgroupESetup M E E₁ E₂ E₃) (hp : p ∈ tau2 M)
    (hLE : L ≤ E) (hLM_norm : M ≤ Subgroup.normalizer (L : Set G))
    (hL : L ∈ elemAbelianOfRank G p 1) :
    ∃ A ∈ elemAbelianOfRank G p 2, A ≤ E ∧ L ≤ A := by
  classical
  have hLM : L ≤ M := hLE.trans hsetup.E_le
  have hLne : L ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hL
  have hM_coatom : IsCoatom M := hsetup.mem_maximal
  -- `N_G(L) = M`.
  have hNL_lt : Subgroup.normalizer (L : Set G) < ⊤ :=
    normalizer_lt_top_of_le_of_ne_bot hG hsetup.mem_maximal hLM hLne
  have hNLM : Subgroup.normalizer (L : Set G) ≤ M := by
    rcases eq_or_lt_of_le hLM_norm with heq | hlt
    · exact heq.ge
    · exact absurd (hM_coatom.2 _ hlt) hNL_lt.ne
  -- BG Lemma 10.5: `∃ A₀ ∈ ℰ_p²(G), L ≤ A₀`.
  obtain ⟨-, -, A₀, hA₀, hLA₀⟩ :=
    OddOrder.BG.Ch3.S10.pRank_eq_two_of_normalizer_le hG hsetup.mem_maximal
      (tau2_subset_sigma_compl M hp) hL hNLM
  have hA₀card : Nat.card ↥A₀ = p ^ 2 := hA₀.2
  have hA₀ab : IsMulCommutative ↥A₀ := ⟨⟨hA₀.1.comm⟩⟩
  -- `A₀ ≤ M` (abelian, contains `L`).
  have hA₀M : A₀ ≤ M :=
    (le_centralizer_of_le_of_le hA₀ab le_rfl hLA₀).trans
      ((Subgroup.centralizer_le_normalizer _).trans hNLM)
  -- `A₀` is a `τ₂(M)`-subgroup.
  have hA₀pi : Ch03.Subgroup.IsPiGroup (tau2 M) (A₀.subgroupOf M) := by
    intro r hr
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀M).toEquiv, hA₀card] at hr
    obtain ⟨hr_prime, hr_dvd, -⟩ := Nat.mem_primeFactors.mp hr
    rwa [(Nat.prime_dvd_prime_iff_eq hr_prime Fact.out).mp (hr_prime.dvd_of_dvd_pow hr_dvd)]
  -- Conjugate `A₀` into the `τ₂`-Hall `E₂`.
  obtain ⟨w, hwM, hw⟩ :=
    exists_conj_smul_le_hallPiece hG hsetup hsetup.E₂_le hsetup.E₂_hall
      (tau2_subset_sigma_compl M) hA₀M hA₀pi
  refine ⟨MulAut.conj w • A₀, conj_smul_mem_elemAbelianOfRank w hA₀, hw.trans hsetup.E₂_le, ?_⟩
  have hLfix : MulAut.conj w • L = L := conj_smul_eq_self_of_mem_normalizer (hLM_norm hwM)
  calc L = MulAut.conj w • L := hLfix.symm
    _ ≤ MulAut.conj w • A₀ := by
        rw [mulAut_smul_eq_map, mulAut_smul_eq_map]; exact Subgroup.map_mono hLA₀

/-- **BG Lemma 14.11** (mmd L4086): for `M ∈ 𝓜_F` with `E` a complement of `M_σ` in `M`, a
prime `q ∈ π(E)`, and `Q ∈ ℰ_q¹(E)` with `Q ⊄ F(E)`, there is `M* ∈ 𝓜` with either
(1) `q ∈ τ₂(M*)` and `𝓜(C_G(Q)) = {M*}`, or (2) `q ∈ κ(M*)` and `M* ∈ 𝓜_{P₁}`.

"Of independent interest" (BG L4084); used here only by Corollary 14.12.  `F(E)` is the Fitting
subgroup of the complement `E`, taken in `G` via `fittingInG`.

Phase 1 (`q ∈ τ₁(M)`, `C_{M_σ}(Q) = 1`) is `typeF_complement_q_tau1_and_centralizer`.  The
remaining phases — `τ₂(M) ≠ ∅` via the cyclic-normal `⁅E,Q⁆` (Prop 10.11(d) +
`commutator_commutator_right_eq_of_le_normalizer` / a `Q^E`-nilpotent argument for `⁅E,Q⁆ ≠ 1`),
then Cor 12.9 (`commutator_decomp_of_tau1_action`) and the `M*`-dichotomy via Lemma 12.11
(`tau2_transfer_to_maximal`) — are tracked in `issues/7007`. -/
theorem exists_maximal_of_typeF_notMem_fitting [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E Q : Subgroup G} {q : ℕ} (hM : M ∈ maximalSubgroups G) (hF : IsTypeF M)
    (hE : Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (E.subgroupOf M))
    (hEM : E ≤ M)
    (hq : q ∈ piSet E) (hQ : Q ∈ elemAbelianOfRank G q 1) (hQE : Q ≤ E)
    (hQF : ¬ Q ≤ OddOrder.BG.Ch2.S08.fittingInG E) :
    ∃ Mstar : Subgroup G, Mstar ∈ maximalSubgroups G ∧
      ((q ∈ tau2 Mstar ∧
          maximalSubgroupsContaining (Subgroup.centralizer (Q : Set G)) = {Mstar}) ∨
       (q ∈ kappa Mstar ∧ IsTypeP1 Mstar)) := by
  classical
  obtain ⟨E₁, E₂, E₃, hsetup⟩ := esetup_of_isComplement hG hM hE hEM
  have hqpf : q ∈ (Nat.card ↥E).primeFactors := hq
  have : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hqpf⟩
  have hqprime : q.Prime := Fact.out
  obtain ⟨K', hK'E, hK'ne, hK'cyc, hK'cent, hMNK', hπK'τ2, hFPF⟩ :=
    exists_typeF_complement_cyclic_commutator hG hsetup hF hq hQ hQE hQF
  have : IsCyclic ↥K' := hK'cyc
  obtain ⟨p, hpp, hpd⟩ :=
    Nat.exists_prime_and_dvd (show Nat.card ↥K' ≠ 1 from fun h => hK'ne (Subgroup.card_eq_one.mp h))
  have : Fact p.Prime := ⟨hpp⟩
  have hpτ2 : p ∈ tau2 M := hπK'τ2 p (Nat.mem_primeFactors.mpr ⟨hpp, hpd, Nat.card_pos.ne'⟩)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥K') p hpd
  set L : Subgroup G := Subgroup.zpowers (a : G) with hLdef
  have haG : orderOf (a : G) = p :=
    (orderOf_injective K'.subtype K'.subtype_injective a).trans ha
  have hLcard : Nat.card ↥L = p := by rw [hLdef, Nat.card_zpowers, haG]
  have hLK' : L ≤ K' := by rw [hLdef, Subgroup.zpowers_le]; exact a.2
  have hLE : L ≤ E := hLK'.trans hK'E
  have hLelem : L ∈ elemAbelianOfRank G p 1 :=
    mem_elemAbelianOfRank.mpr
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hLcard, by rw [hLcard, pow_one]⟩
  have hLne : L ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hLelem
  have hLM_norm : M ≤ Subgroup.normalizer (L : Set G) := by
    have : (L.subgroupOf K').Characteristic := Ch04.characteristic_of_subgroup_of_isCyclic _
    intro m hm
    have hmem := OddOrder.BG.Ch1.S03f.mem_normalizer_map_subtype_of_characteristic
      (W := K') (C := L.subgroupOf K') (hMNK' hm)
    rwa [Subgroup.map_subgroupOf_eq_of_le hLK'] at hmem
  have hLQ : (⁅L, Q⁆ : Subgroup G) ≠ ⊥ := by
    rw [Ne, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact fun hLc => hLne (le_bot_iff.mp (hFPF ▸ le_inf hLc hLK'))
  obtain ⟨A, hA, hAE, hLA⟩ :=
    exists_elemAb_rank_two_le_E_containing_line hG hsetup hpτ2 hLE hLM_norm hLelem
  have hAQ : (⁅A, Q⁆ : Subgroup G) ≠ ⊥ := fun h =>
    hLQ (le_bot_iff.mp ((Subgroup.commutator_mono hLA le_rfl).trans h.le))
  have hAne : A ≠ ⊥ := by
    intro h; have h2 := hA.2; rw [h, Subgroup.card_bot] at h2
    exact (Nat.one_lt_pow (by norm_num) hpp.one_lt).ne' h2.symm
  obtain ⟨hqτ1, hCQ⟩ := typeF_complement_q_tau1_and_centralizer hG hsetup hF hq hQ hQE hQF
  obtain ⟨-, -, hA₁elem, -, -⟩ :=
    commutator_decomp_of_tau1_action hG hsetup hpτ2 hqτ1 hA hAE hQ hQE hCQ hAQ
  have hA₁ne : A ⊓ Subgroup.centralizer (Q : Set G) ≠ ⊥ :=
    ne_bot_of_mem_elemAbelianOfRank_one hA₁elem
  obtain ⟨⟨hENA, -⟩, -, -⟩ := elemAb_normal_in_E_of_tau2 hG hsetup hpτ2 hA hAE
  have hQNA : Q ≤ Subgroup.normalizer (A : Set G) := hQE.trans hENA
  have hQncA : ¬ Q ≤ Subgroup.centralizer (A : Set G) := fun h =>
    hAQ ((Subgroup.commutator_comm A Q).trans
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h))
  have hNA_lt : Subgroup.normalizer (A : Set G) < ⊤ :=
    normalizer_lt_top_of_le_of_ne_bot hG hM (hAE.trans hsetup.E_le) hAne
  obtain ⟨Mstar, hMstar_coatom, hMstar_le⟩ :=
    (eq_top_or_exists_le_coatom _).resolve_left hNA_lt.ne
  have hMstarmax : Mstar ∈ maximalSubgroups G := hMstar_coatom
  have hMstarmem : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (A : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨hMstar_coatom, hMstar_le⟩
  have hAMstar : A ≤ Mstar := Subgroup.le_normalizer.trans hMstar_le
  have hQMstar : Q ≤ Mstar := hQNA.trans hMstar_le
  have hqidx : q ∈
      (((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).index).primeFactors := by
    set c : Subgroup G := E ⊓ Subgroup.centralizer (A : Set G) with hcdef
    have hcE : c ≤ E := inf_le_left
    have hENc : E ≤ Subgroup.normalizer (c : Set G) :=
      hcdef ▸ le_normalizer_inf Subgroup.le_normalizer
        (hENA.trans (normalizer_le_normalizer_centralizer A))
    have hcnorm : (c.subgroupOf E).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hcE).mpr hENc
    have hQ'qg : IsPGroup q ↥(Q.subgroupOf E) := by
      rw [IsPGroup.iff_card]
      exact ⟨1, by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQE).toEquiv, hQ.2]⟩
    obtain ⟨P, hQ'P⟩ := hQ'qg.exists_le_sylow
    have hQ'nc : ¬ (Q.subgroupOf E ≤ c.subgroupOf E) := by
      intro hle
      apply hQncA
      have hQc : Q ≤ c := by
        have hmm := Subgroup.map_mono (f := E.subtype) hle
        rwa [Subgroup.map_subgroupOf_eq_of_le hQE, Subgroup.map_subgroupOf_eq_of_le hcE] at hmm
      exact hQc.trans inf_le_right
    have hPnc : ¬ (P : Subgroup ↥E) ≤ c.subgroupOf E := fun hPc => hQ'nc (hQ'P.trans hPc)
    exact Nat.mem_primeFactors.mpr
      ⟨hqprime, prime_dvd_index_of_sylow_not_le_of_normal P hPnc, Subgroup.index_ne_zero_of_finite⟩
  obtain ⟨hσβ, hτ12, -⟩ := tau2_transfer_to_maximal hG hsetup hpτ2 hA hAE hMstarmem
  have hpσβ : p ∈ OddOrder.BG.Ch3.S10.sigma Mstar \ OddOrder.BG.Ch3.S10.beta Mstar := hσβ p hpp hpτ2
  have hqτ12 : q ∈ tau1 Mstar ∪ tau2 Mstar := hτ12 q hqidx
  have hApiσ : Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma Mstar) A := by
    intro r hr
    rw [hA.2, Nat.mem_primeFactors] at hr
    exact ((Nat.prime_dvd_prime_iff_eq hr.1 Fact.out).mp (hr.1.dvd_of_dvd_pow hr.2.1)) ▸ hpσβ.1
  have hAMσ : A ≤ OddOrder.BG.Ch3.S10.Msigma Mstar :=
    OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall (OddOrder.BG.Ch3.S10.Msigma_isHall hG
        hMstarmax) hAMstar hApiσ
  have hCMσQ : OddOrder.BG.Ch3.S10.Msigma Mstar ⊓ Subgroup.centralizer (Q : Set G) ≠ ⊥ := fun h =>
    hA₁ne (le_bot_iff.mp (h ▸ inf_le_inf hAMσ le_rfl))
  refine ⟨Mstar, hMstarmax, ?_⟩
  rcases hqτ12 with hτ1 | hτ2
  · refine Or.inr ⟨⟨hqprime, Or.inl hτ1, Q, hQ, hQMstar, hCMσQ⟩, ?_⟩
    have hPtype : IsTypeP Mstar := ⟨q, hqprime, Or.inl hτ1, Q, hQ, hQMstar, hCMσQ⟩
    rcases (isTypeP_iff_isTypeP1_or_isTypeP2).mp hPtype with h1 | h2
    · exact h1
    · exfalso
      have : Group.IsSolvable ↥Mstar := hG.isSolvable_of_mem_maximalSubgroups hMstarmax
      obtain ⟨Ksub, hKsub⟩ := Ch03.hall_E_exists (G := ↥Mstar) (kappa Mstar)
      obtain ⟨Usub, hUsub⟩ :=
        Ch03.hall_E_exists (G := ↥Mstar) ((kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ)
      have hKeq : (Ksub.map Mstar.subtype).subgroupOf Mstar = Ksub :=
        Subgroup.comap_map_eq_self_of_injective Mstar.subtype_injective Ksub
      have hUeq : (Usub.map Mstar.subtype).subgroupOf Mstar = Usub :=
        Subgroup.comap_map_eq_self_of_injective Mstar.subtype_injective Usub
      have hσeqβ :=
        ((typeP_structure hG hMstarmax hPtype (Subgroup.map_subtype_le _)
            (by rw [hKeq]; exact hKsub) rfl (by rw [hUeq]; exact hUsub)).2.2.2.2.1 h2).1
      exact hpσβ.2 (hσeqβ ▸ hpσβ.1)
  · refine Or.inl ⟨hτ2, ?_⟩
    have hQcard : Nat.card ↥Q = q := by rw [hQ.2, pow_one]
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q) q (hQcard ▸ dvd_refl q)
    have hxG : orderOf (x : G) = q := (orderOf_injective Q.subtype Q.subtype_injective x).trans hx
    set X : G := (x : G) with hXdef
    have hXQ : X ∈ Q := x.2
    have hX1 : X ≠ 1 := by
      intro h; rw [h, orderOf_one] at hxG; exact hqprime.ne_one hxG.symm
    have hcl : Subgroup.closure ({X} : Set G) = Q := by
      rw [← Subgroup.zpowers_eq_closure]
      exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hXQ)
        (le_of_eq (by rw [hQcard, Nat.card_zpowers, hxG]))
    have hCeq : Subgroup.centralizer ({X} : Set G) = Subgroup.centralizer (Q : Set G) := by
      rw [← hcl]; exact (Subgroup.centralizer_closure {X}).symm
    have hτ2cl : ∀ r ∈ piSet (Subgroup.closure ({X} : Set G)), r ∈ tau2 Mstar := by
      intro r hr
      rw [hcl, piSet, Set.mem_ofPred_eq, hQcard, Nat.mem_primeFactors] at hr
      exact ((Nat.prime_dvd_prime_iff_eq hr.1 hqprime).mp hr.2.1) ▸ hτ2
    have hsingle := maximalContaining_centralizer_eq_singleton_of_tau2_element hG hMstarmax
      (hQMstar hXQ) hX1 hτ2cl (by rw [hCeq]; exact hCMσQ)
    rwa [hCeq] at hsingle

/-- **BG Theorem A(5), element form** (mmd L4280): for a type-`P` maximal subgroup `M` with cyclic
Hall `κ(M)`-subgroup `K` and `K* = C_{M_σ}(K)`, the `M`-centralizer of every nonidentity `k ∈ K`
is the cyclic product `K ⊔ K*` (BG's `C_M(k) = K × K*`).

This sharpens Proposition 14.2(b1) (`typeP_structure`), which gives `N_M(X) = K ⊔ K*` only for the
rank-one `X ∈ ℰ¹(K)`, to the element-wise centralizer.  Bridge: `K` is cyclic, so `⟨k⟩ ≤ K` is
cyclic and contains a subgroup `X` of prime order `p ∣ |k|` with `X ≤ K`; then
`C_G(k) ≤ C_G(X) ≤ N_G(X)`, so `M ⊓ C_G(k) ≤ N_G(X) ⊓ M = K ⊔ K*`, while `K ≤ C_G(k)` (`K` abelian)
and `K* ≤ C_G(K) ≤ C_G(k)` give the reverse. -/
theorem typeP_centralizer_kappaElement_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    [IsCyclic ↥K] :
    ∀ k ∈ K, k ≠ 1 → M ⊓ Subgroup.centralizer ({k} : Set G) = K ⊔ Kstar := by
  intro k hk hk1
  -- `⟨k⟩ ≤ K`.
  have hzk : Subgroup.zpowers k ≤ K := Subgroup.zpowers_le.mpr hk
  -- A prime `p ∣ |k|` and an element `v ∈ ⟨k⟩` of order `p`.
  have hord1 : orderOf k ≠ 1 := fun h => hk1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpk⟩ := (orderOf k).exists_prime_and_dvd hord1
  have : Fact p.Prime := ⟨hp⟩
  have hpcard : p ∣ Nat.card ↥(Subgroup.zpowers k) := by rw [Nat.card_zpowers]; exact hpk
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' p hpcard
  -- `X = ⟨v⟩` is rank-one elementary abelian and `X ≤ K`.
  set X : Subgroup G := Subgroup.zpowers (v : G) with hXdef
  have hXcard : Nat.card ↥X = p := by
    rw [hXdef, Nat.card_zpowers]
    exact (orderOf_injective _ (Subgroup.zpowers k).subtype_injective v).trans hv
  have hXelem : X ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXzk : X ≤ Subgroup.zpowers k := by rw [hXdef]; exact Subgroup.zpowers_le.mpr v.2
  have hXK : X ≤ K := hXzk.trans hzk
  -- Proposition 14.2(b1): `N_G(X) ⊓ M = K ⊔ K*`.
  obtain ⟨_, _, hb1, _, _, _, _⟩ := typeP_structure hG hM hP hKM hK hKstar hU
  have hNX : Subgroup.normalizer (X : Set G) ⊓ M = K ⊔ Kstar := hb1 p hp X hXelem hXK
  -- `C_G(k) ≤ C_G(X)`: everything centralizing `k` centralizes `⟨k⟩ ⊇ X`.
  have hCkX : Subgroup.centralizer ({k} : Set G) ≤ Subgroup.centralizer (X : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hkCg : k ∈ Subgroup.centralizer ({g} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hg).symm
    have hyCg : y ∈ Subgroup.centralizer ({g} : Set G) :=
      (Subgroup.zpowers_le.mpr hkCg) (hXzk hy)
    exact Subgroup.mem_centralizer_singleton_iff.mp hyCg
  -- Forward `M ⊓ C_G(k) ≤ K ⊔ K*` via `C_G(k) ≤ C_G(X) ≤ N_G(X)`.
  have hfwd : M ⊓ Subgroup.centralizer ({k} : Set G) ≤ K ⊔ Kstar := by
    rw [← hNX]
    exact le_inf
      (inf_le_right.trans (hCkX.trans (Subgroup.centralizer_le_normalizer (X : Set G)))) inf_le_left
  -- Reverse `K ⊔ K* ≤ M ⊓ C_G(k)`.
  have hrev : K ⊔ Kstar ≤ M ⊓ Subgroup.centralizer ({k} : Set G) := by
    refine sup_le (le_inf hKM ?_) ?_
    · -- `K ≤ C_G(k)`: `K` cyclic ⟹ `K ≤ C_G(K) ≤ C_G(k)` (`k ∈ K`).
      exact le_trans (Subgroup.le_centralizer K)
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hk))
    · -- `K* ≤ M_σ ≤ M` and `K* ≤ C_G(K) ≤ C_G(k)`.
      rw [hKstar]
      exact le_inf (inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le M))
        (inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hk)))
  exact le_antisymm hfwd hrev

/-- **σ-part of a κ-branch element lies in `K*`** (the `Ks_y` step of κ→Ẑ): for a type-`P`
maximal `M`, a `σ(M)`-element `y` that centralizes a nonidentity `κ`-Hall element `y' ∈ K^#` lies
in `K* = M_σ ⊓ C_G(K)`.  Chain: `y ∈ M ⊓ C_G(y') = K ⊔ K*` (`typeP_centralizer_kappaElement_eq`,
conjunct (d)); since `K ⊔ K*` is cyclic (`typeP_Z_isCyclic`), `y` centralizes `K`
(`mem_centralizer_of_mem_sup_isCyclic`); with `y ∈ M_σ` this gives `y ∈ K*`. -/
theorem typeP_sigmaElement_mem_Kstar [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar)
    {y y' : G} (hyMsigma : y ∈ OddOrder.BG.Ch3.S10.Msigma M) (hy'K : y' ∈ K) (hy'1 : y' ≠ 1)
    (hcent : y ∈ Subgroup.centralizer ({y'} : Set G)) :
    y ∈ Kstar := by
  have hcycZ : IsCyclic ↥(K ⊔ Kstar) :=
    typeP_Z_isCyclic hG D hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  have hcycK : IsCyclic ↥K :=
    (Subgroup.subgroupOfEquivOfLe (le_sup_left : K ≤ K ⊔ Kstar)).isCyclic.mp inferInstance
  have hyM : y ∈ M := OddOrder.BG.Ch3.S10.Msigma_le M hyMsigma
  have hyMC : y ∈ M ⊓ Subgroup.centralizer ({y'} : Set G) := Subgroup.mem_inf.mpr ⟨hyM, hcent⟩
  rw [typeP_centralizer_kappaElement_eq hG hM hP hKM hK hKstar hU y' hy'K hy'1] at hyMC
  rw [hKstar]
  exact Subgroup.mem_inf.mpr ⟨hyMsigma, mem_centralizer_of_mem_sup_isCyclic hcycZ hyMC⟩

/-- **κ→Ẑ membership, core** (the `y'∈K` form): for a type-`P` maximal `M`, a nonidentity
`σ(M)`-element `y` and a nonidentity `κ`-Hall element `y' ∈ K^#` that commute have product
`y · y' ∈ Ẑ = (K ⊔ K*) ∖ (K ∪ K*)`.  Combines `typeP_sigmaElement_mem_Kstar` (`y ∈ K*`) with
`mem_zTilde_of_mul` (using `K ⊓ K* = ⊥`, `kappaHall_inf_Kstar_eq_bot`).  The general κ-branch
element (Coq `mFT_partition` part 2) reduces to this by conjugating its `κ`-element into `K`. -/
theorem kappa_branch_mem_zTilde [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar)
    {y y' : G} (hyMsigma : y ∈ OddOrder.BG.Ch3.S10.Msigma M) (hy1 : y ≠ 1) (hy'K : y' ∈ K)
    (hy'1 : y' ≠ 1) (hcent : y ∈ Subgroup.centralizer ({y'} : Set G)) :
    y * y' ∈ zTilde K Kstar :=
  mem_zTilde_of_mul (kappaHall_inf_Kstar_eq_bot hKM hK hKstar)
    (typeP_sigmaElement_mem_Kstar hG D hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
      hyMsigma hy'K hy'1 hcent)
    hy1 hy'K hy'1

/-- **κ→Ẑ membership, general form**: lifts `kappa_branch_mem_zTilde` to a `κ(M)`-element `y'` not
necessarily in the chosen Hall `K`, via conjugation.  Since `⟨y'⟩` is a `κ(M)`-subgroup of `M`, an
`a ∈ M` conjugates it into `K` (`exists_conj_smul_le_of_isHall`); then `aᵃ • (y · y')` lies in `Ẑ`
(applying the core to `aᵃ • y ∈ M_σ` and `aᵃ • y' ∈ K`), so `y · y' ∈ 𝒞_G(Ẑ)`.  This is the
κ-branch → `𝒞_G(Ẑ)` step of the NonType-I `G^#` cover (Coq `mFT_partition` part 2). -/
theorem kappa_branch_mem_conjClassSet_zTilde [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G)
    {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar)
    {y y' : G} (hyMsigma : y ∈ OddOrder.BG.Ch3.S10.Msigma M) (hy1 : y ≠ 1) (hy'M : y' ∈ M)
    (hy'1 : y' ≠ 1) (hcent : y ∈ Subgroup.centralizer ({y'} : Set G))
    (hy'kappa : OddOrder.GroupTheory.IsPiElement (kappa M) y') :
    y * y' ∈ conjClassSet (zTilde K Kstar) := by
  classical
  -- `⟨y'⟩` is a `κ(M)`-subgroup of `M`; conjugate it into `K`.
  have hcloseM : Subgroup.closure ({y'} : Set G) ≤ M := by
    rw [Subgroup.closure_le]; exact Set.singleton_subset_iff.mpr hy'M
  have hcard : Nat.card ↥((Subgroup.closure ({y'} : Set G)).subgroupOf M) = orderOf y' := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcloseM).toEquiv,
      ← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
  have hclosepi : Ch03.Subgroup.IsPiGroup (kappa M)
      ((Subgroup.closure ({y'} : Set G)).subgroupOf M) := fun p hp =>
    hy'kappa p (by rwa [hcard] at hp)
  obtain ⟨a, haM, hale⟩ := exists_conj_smul_le_of_isHall hG hM hKM hK hcloseM hclosepi
  have hay'K : MulAut.conj a • y' ∈ K :=
    hale (Subgroup.smul_mem_pointwise_smul y' (MulAut.conj a) _
      (Subgroup.subset_closure (Set.mem_singleton y')))
  -- `aᵃ • y ∈ M_σ`.
  have hMsigmaFix : MulAut.conj a • OddOrder.BG.Ch3.S10.Msigma M = OddOrder.BG.Ch3.S10.Msigma M :=
      by
    rw [← Msigma_conj_smul, Subgroup.conj_smul_eq_self_of_mem haM]
  have hayMsigma : MulAut.conj a • y ∈ OddOrder.BG.Ch3.S10.Msigma M :=
    hMsigmaFix ▸ Subgroup.smul_mem_pointwise_smul y (MulAut.conj a) _ hyMsigma
  have hay1 : MulAut.conj a • y ≠ 1 := fun h => hy1 (by
    rw [MulAut.smul_def] at h; exact (MulAut.conj a).injective (h.trans (map_one _).symm))
  have hay'1 : MulAut.conj a • y' ≠ 1 := fun h => hy'1 (by
    rw [MulAut.smul_def] at h; exact (MulAut.conj a).injective (h.trans (map_one _).symm))
  -- `aᵃ • y` centralizes `aᵃ • y'`.
  have haycent : MulAut.conj a • y ∈ Subgroup.centralizer ({MulAut.conj a • y'} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.mp hz, MulAut.smul_def, MulAut.smul_def, ← map_mul, ← map_mul]
    exact congrArg (MulAut.conj a) (Subgroup.mem_centralizer_iff.mp hcent y' (Set.mem_singleton y'))
  -- `aᵃ • (y·y') = (aᵃ • y)·(aᵃ • y') ∈ Ẑ`, so `y·y' ∈ 𝒞_G(Ẑ)`.
  have hzin : MulAut.conj a • (y * y') ∈ zTilde K Kstar := by
    rw [MulAut.smul_def, map_mul, ← MulAut.smul_def, ← MulAut.smul_def]
    exact kappa_branch_mem_zTilde hG D hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
      hayMsigma hay1 hay'K hay'1 haycent
  exact ⟨MulAut.conj a • (y * y'), hzin, a⁻¹, by
    rw [MulAut.smul_def, MulAut.conj_apply]; group⟩

/-- **Fixed-`W` κ-branch**: the same conclusion as `kappa_branch_dichotomy_mem_conjClassSet_zTilde`,
but landing in the `Ẑ` of a *fixed* reference type-`P` maximal `Mref` (data `Kref, K*ref, Uref`)
rather than in the (existentially produced) type-`P` `N`'s own `Ẑ`.  The dichotomy's `N` is
type-`P`,
so `conjClassSet_zTilde_eq_fixed_of_isTypeP` (fix-`W`) absorbs `N`'s `Ẑ` into `Ẑ(Mref)`. -/
theorem kappa_branch_dichotomy_mem_fixed_conjClassSet_zTilde [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G)
    {Mref Kref Kstarref Uref : Subgroup G}
    (hMref : Mref ∈ maximalSubgroups G) (hMPref : IsTypeP Mref) (hKMref : Kref ≤ Mref)
    (hKref : Ch03.IsHallSubgroup (kappa Mref) (Kref.subgroupOf Mref))
    (hKstarref : Kstarref = OddOrder.BG.Ch3.S10.Msigma Mref ⊓ Subgroup.centralizer (Kref : Set G))
    (hUref : Ch03.IsHallSubgroup ((kappa Mref ∪ OddOrder.BG.Ch3.S10.sigma Mref)ᶜ)
      (Uref.subgroupOf Mref))
    {y g : G} (hyl : D.length y = 1) {N : Subgroup G}
    (hNmem : N ∈ maximalSigmaSubgroupsOfElement y)
    (hsharp : y⁻¹ * g ∈ sharpSubgroup (N ⊓ Subgroup.centralizer ({y} : Set G)))
    (hkappa : OddOrder.GroupTheory.IsPiElement (kappa N) (y⁻¹ * g)) :
    g ∈ conjClassSet (zTilde Kref Kstarref) := by
  obtain ⟨hNmax, hyNsigma⟩ := hNmem
  have hy1 : y ≠ 1 := ((D.length_one_iff y).mp hyl).1
  rw [sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe,
    Subgroup.mem_inf] at hsharp
  obtain ⟨⟨hy'N, hy'cent⟩, hy'1⟩ := hsharp
  have hycent : y ∈ Subgroup.centralizer ({y⁻¹ * g} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]; intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    exact (Subgroup.mem_centralizer_iff.mp hy'cent y (Set.mem_singleton y)).symm
  have hNP : IsTypeP N := by
    obtain ⟨p, hp⟩ : (orderOf (y⁻¹ * g)).primeFactors.Nonempty :=
      Nat.nonempty_primeFactors.mpr (by
        have h1 : orderOf (y⁻¹ * g) ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
        have h0 : 0 < orderOf (y⁻¹ * g) := orderOf_pos _
        omega)
    exact ⟨p, hkappa p hp⟩
  obtain ⟨K, Kstar, U, hKM, hK, hKstar, hU⟩ := exists_typeP_data hG hNmax
  obtain ⟨Mstar, hMstarne, hMstarmem, hpart⟩ := exists_partner hG D hNmax hNP hKM hK hKstar hU
  have hmem : g ∈ conjClassSet (zTilde K Kstar) := by
    have h := kappa_branch_mem_conjClassSet_zTilde hG D hNmax hNP hKM hK hKstar hU hMstarmem
      hMstarne hpart hyNsigma hy1 hy'N hy'1 hycent hkappa
    rwa [mul_inv_cancel_left] at h
  rwa [conjClassSet_zTilde_eq_fixed_of_isTypeP hG hMref hMPref hKMref hKref hKstarref hUref
    hNmax hNP hKM hK hKstar] at hmem

/-- **Fixed-`W` `G^#` cover** (the form BG Corollary 14.9 / the NonTypeICovering struct needs):
every `g ≠ 1` lies in `𝒞_G(M̃)` for some maximal `M`, or in `𝒞_G(Ẑ)` for the *fixed* exceptional
`Ẑ = zTilde Kref K*ref` of a reference type-`P` maximal `Mref`.  Same as
`exists_mem_conjClassSet_Mtilde_or_zTilde_of_ne_one`, but the κ branch is collapsed onto the single
fixed `Ẑ` via `kappa_branch_dichotomy_mem_fixed_conjClassSet_zTilde`. -/
theorem exists_mem_conjClassSet_Mtilde_or_fixed_zTilde [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {Mref Kref Kstarref Uref : Subgroup G}
    (hMref : Mref ∈ maximalSubgroups G) (hMPref : IsTypeP Mref) (hKMref : Kref ≤ Mref)
    (hKref : Ch03.IsHallSubgroup (kappa Mref) (Kref.subgroupOf Mref))
    (hKstarref : Kstarref = OddOrder.BG.Ch3.S10.Msigma Mref ⊓ Subgroup.centralizer (Kref : Set G))
    (hUref : Ch03.IsHallSubgroup ((kappa Mref ∪ OddOrder.BG.Ch3.S10.sigma Mref)ᶜ)
      (Uref.subgroupOf Mref))
    {g : G} (hg : g ≠ 1) :
    (∃ M ∈ maximalSubgroups G,
      g ∈ conjClassSet (Mtilde hG (genuineSigmaDecomposition hG) M))
    ∨ g ∈ conjClassSet (zTilde Kref Kstarref) := by
  set D := genuineSigmaDecomposition hG with hD
  rcases sigma_decomposition_dichotomy hG D hg with
    ⟨y, hyl, hyr⟩ | ⟨y, hyl, N, hNmem, hsharp, hκ⟩
  · obtain ⟨hy1, M, hMmax, hyMσ⟩ := (D.length_one_iff y).mp hyl
    exact Or.inl ⟨M, hMmax, subset_conjClassSet
      (mem_Mtilde_of_mem_coset hG D (Set.mem_sdiff_singleton.mpr ⟨hyMσ, hy1⟩) hyr)⟩
  · exact Or.inr (kappa_branch_dichotomy_mem_fixed_conjClassSet_zTilde hG D hMref hMPref hKMref
      hKref hKstarref hUref hyl hNmem hsharp hκ)

/-- **BG Theorem A(4)** (mmd L4279): `C_U(k) = 1` for `k ∈ K#` — the `(κ(M) ∪ σ(M))'`-Hall
complement `U` meets each `M`-centralizer `C_M(k) = K ⊔ K*` trivially.

**Faithfulness (issue 8017).** BG states A(4) for the *`K`-invariant* complement `U`, but the
conclusion holds for **every** `(κ ∪ σ)'`-Hall `U ≤ M`: by `typeP_centralizer_kappaElement_eq`,
`U ⊓ C_G(k) = U ⊓ (M ⊓ C_G(k)) = U ⊓ (K ⊔ K*)`, and `|U|` (a `(κ ∪ σ)'`-number) is coprime to
`|K ⊔ K*| = |K|·|K*|` (a `(κ ∪ σ)`-number, `K` Hall `κ`, `K* ≤ M_σ` Hall `σ`), so the intersection
is trivial.  No `K`-invariance of `U` is needed; the bug-suspect conjunct is faithful as stated. -/
theorem typeP_hall_inf_centralizer_kappaElement_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    [IsCyclic ↥K] :
    ∀ k ∈ K, k ≠ 1 → U ⊓ Subgroup.centralizer ({k} : Set G) = ⊥ := by
  intro k hk hk1
  -- `C_M(k) = K ⊔ K*`, hence `U ⊓ C_G(k) = U ⊓ (K ⊔ K*)` (`U ≤ M`).
  have hCM := typeP_centralizer_kappaElement_eq hG hM hP hKM hK hKstar hU k hk hk1
  have hstep : U ⊓ Subgroup.centralizer ({k} : Set G) = U ⊓ (K ⊔ Kstar) := by
    rw [← hCM, ← inf_assoc, inf_eq_left.mpr hUM]
  rw [hstep]
  -- `|U|` and `|K ⊔ K*| = |K|·|K*|` are coprime: `(κ∪σ)'` vs `κ∪σ`.
  apply Disjoint.eq_bot
  apply Subgroup.disjoint_of_coprime_natCard
  have hcard : Nat.card ↥(K ⊔ Kstar) = Nat.card ↥K * Nat.card ↥Kstar :=
    card_kappaHall_sup_Kstar hKM hK hKstar
  refine Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
    (π := (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) Nat.card_pos.ne' Nat.card_pos.ne' ?_ ?_
  · -- `|U|` is a `(κ∪σ)'`-number.
    intro p hp
    exact hU.1 p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv])
  · -- every prime of `|K ⊔ K*|` lies in `κ ∪ σ`.
    intro p hp hpcompl
    rw [hcard, Nat.primeFactors_mul Nat.card_pos.ne' Nat.card_pos.ne'] at hp
    rcases Finset.mem_union.mp hp with hpK | hpKstar
    · exact hpcompl (Or.inl (hK.1 p (by
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv])))
    · refine hpcompl (Or.inr (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p ?_))
      have hKstar_le_Mσ : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M := by rw [hKstar]; exact inf_le_left
      exact Nat.primeFactors_mono (Subgroup.card_dvd_of_le hKstar_le_Mσ) Nat.card_pos.ne' hpKstar

/-- **`M_σ ∩ M* = K*`** (BG Theorem 14.7(d) kernel, Coq `defMsMstar`): for a type-`P₂` maximal
`M` with `κ`-Hall `K`, `K* = M_σ ⊓ C(K)`, and the dual partner `M*` (`K ≤ M*_σ`, `K* ≤ M*`, `M`
not conjugate to `M*`), the intersection `M_σ ⊓ M*` equals `K*`.

`⊇` is immediate (`K* ≤ M_σ`, `K* ≤ M*`).  For `⊆`: any `y ∈ M_σ ⊓ M*` has `⁅⟨y⟩, K⁆ ≤ M_σ`
(`K ≤ M ≤ N(M_σ)`, `y ∈ M_σ`) and `⁅⟨y⟩, K⁆ ≤ M*_σ` (`K ≤ M*_σ ◁ M*`, `y ∈ M* ≤ N(M*_σ)`), so
`⁅⟨y⟩, K⁆ ≤ M_σ ⊓ M*_σ = ⊥` (Lemma 10.12, `M_σ` nilpotent for type-`P₂`); hence `y` centralizes
`K`, i.e. `y ∈ M_σ ⊓ C(K) = K*`.  Avoids the embedding's σ(M)-Hall-of-M* clause. -/
theorem msigma_inf_partner_eq_kstar [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP2 : IsTypeP2 M) (hKM : K ≤ M)
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hMstarmax : Mstar ∈ maximalSubgroups G)
    (hKMsigmaMstar : K ≤ OddOrder.BG.Ch3.S10.Msigma Mstar) (hKstarMstar : Kstar ≤ Mstar)
    (hnc : ¬ IsConjugateSubgroup M Mstar) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Mstar = Kstar := by
  classical
  -- `M_σ` nilpotent (type-`P₂`) ⟹ `M_σ ⊓ M*_σ = ⊥` (Lemma 10.12).
  have hdisj : OddOrder.BG.Ch3.S10.Msigma M ⊓ OddOrder.BG.Ch3.S10.Msigma Mstar = ⊥ :=
    ((OddOrder.BG.Ch3.S10.disjoint_of_not_conj hG hM hMstarmax (fun h => hnc h)).2
      (msigma_isNilpotent_of_isTypeP2 hG hM hP2)).1
  have hMN : M ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) := by
    rw [OddOrder.BG.Ch3.S10.Msigma]
    exact le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M
  have hMstarN : Mstar ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma Mstar : Set G) := by
    rw [OddOrder.BG.Ch3.S10.Msigma]
    exact le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma Mstar) Mstar
  apply le_antisymm
  · intro y hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyMσ, hyMstar⟩ := hy
    rw [hKstar, Subgroup.mem_inf]
    refine ⟨hyMσ, ?_⟩
    have hcle : (⁅Subgroup.zpowers y, K⁆ : Subgroup G) ≤ ⊥ := by
      rw [← hdisj, le_inf_iff]
      refine ⟨Subgroup.commutator_le.mpr ?_, Subgroup.commutator_le.mpr ?_⟩
      · intro a ha k hk
        have haMσ : a ∈ OddOrder.BG.Ch3.S10.Msigma M := (Subgroup.zpowers_le.mpr hyMσ) ha
        have hkN := (Subgroup.mem_normalizer_iff.mp (hMN (hKM hk))) a⁻¹
        rw [commutatorElement_def]
        have hconj : k * a⁻¹ * k⁻¹ ∈ OddOrder.BG.Ch3.S10.Msigma M := hkN.mp (inv_mem haMσ)
        have : a * k * a⁻¹ * k⁻¹ = a * (k * a⁻¹ * k⁻¹) := by group
        rw [this]; exact mul_mem haMσ hconj
      · intro a ha k hk
        have haMstarσ : a ∈ Mstar := (Subgroup.zpowers_le.mpr hyMstar) ha
        have hkMσstar : k ∈ OddOrder.BG.Ch3.S10.Msigma Mstar := hKMsigmaMstar hk
        rw [commutatorElement_def]
        have hconj : a * k * a⁻¹ ∈ OddOrder.BG.Ch3.S10.Msigma Mstar :=
          (Subgroup.mem_normalizer_iff.mp (hMstarN haMstarσ) k).mp hkMσstar
        have : a * k * a⁻¹ * k⁻¹ = (a * k * a⁻¹) * k⁻¹ := by group
        rw [this]; exact mul_mem hconj (inv_mem hkMσstar)
    rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer] at hcle
    exact hcle (Subgroup.mem_zpowers y)
  · exact le_inf (hKstar ▸ inf_le_left) hKstarMstar

/-- **The partner intersection `ziMMst` and `K`-uniqueness `sK_uniqMst`** (BG Theorem 14.7,
embedding internals), assembled here for the type-`F` classification of Corollary 14.12.

Applying `typeP_structure` to the partner `M*` (whose `κ`-Hall is `K*`, with `K = M*_σ ⊓ C(K*)`):
the `b1` clause at a characteristic order-`p` line of the cyclic `K*` gives `N_{M*}(K*) = K* ⊔ K`,
whence (via `M_σ ⊓ M* = K*`, here `hMsMst`) `M ⊓ M* = K ⊔ K*`; and the `K`-TI clause gives
`K ≤ M*^a ⟹ a ∈ M*`.  Mirrors Coq `Ptype_embedding`'s `ziMMst`/`sK_uniqMst` (BGsection14.v L1820,
L2278). -/
theorem partner_inf_and_uniq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar Mstar : Subgroup G} (hMstmax : Mstar ∈ maximalSubgroups G) (hMstP : IsTypeP Mstar)
    (hKstarMst : Kstar ≤ Mstar)
    (hKstar_hall : Ch03.IsHallSubgroup (kappa Mstar) (Kstar.subgroupOf Mstar))
    (hK_eq : K = OddOrder.BG.Ch3.S10.Msigma Mstar ⊓ Subgroup.centralizer (Kstar : Set G))
    (hKMsigmaMst : K ≤ OddOrder.BG.Ch3.S10.Msigma Mstar)
    (hKM : K ≤ M) (hKstarM : Kstar ≤ M)
    (hZcyc : IsCyclic ↥(K ⊔ Kstar)) (hKstarNe : Kstar ≠ ⊥) (hKNe : K ≠ ⊥)
    (hMsMst : OddOrder.BG.Ch3.S10.Msigma M ⊓ Mstar = Kstar) :
    M ⊓ Mstar = K ⊔ Kstar ∧ (∀ a : G, K ≤ MulAut.conj a • Mstar → a ∈ Mstar) := by
  classical
  have : Group.IsSolvable ↥Mstar := hG.isSolvable_of_mem_maximalSubgroups hMstmax
  have := hZcyc
  -- A Hall `(κ(M*) ∪ σ(M*))'`-subgroup of `M*`, to feed `typeP_structure`.
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥Mstar)
    ((kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ)
  have hUeq : (U'.map Mstar.subtype).subgroupOf Mstar = U' :=
    Subgroup.comap_map_eq_self_of_injective Mstar.subtype_injective U'
  have hU_Mstar : Ch03.IsHallSubgroup ((kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ)
      ((U'.map Mstar.subtype).subgroupOf Mstar) := by rw [hUeq]; exact hU'
  have hstruct := typeP_structure hG hMstmax hMstP hKstarMst hKstar_hall hK_eq hU_Mstar
  -- `b1`: `N_G(X) ⊓ M* = K* ⊔ K` for rank-one `X ≤ K*`; TI: `g ∉ M* → K ⊓ M*^g = ⊥`.
  have hb1 := hstruct.2.2.1
  have hTI := hstruct.2.2.2.1
  -- `K ≤ C(K*)` (`Z = K ⊔ K*` cyclic ⟹ abelian).
  have hKcKstar : K ≤ Subgroup.centralizer (Kstar : Set G) := by
    let : CommGroup ↥(K ⊔ Kstar) := IsCyclic.commGroup
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hkZ : k ∈ (K ⊔ Kstar : Subgroup G) := Subgroup.mem_sup_left hk
    have hsZ : s ∈ (K ⊔ Kstar : Subgroup G) := Subgroup.mem_sup_right hs
    exact congrArg Subtype.val (mul_comm (⟨s, hsZ⟩ : ↥(K ⊔ Kstar)) (⟨k, hkZ⟩ : ↥(K ⊔ Kstar)))
  -- A characteristic order-`p` line `X ≤ K*` (cyclic `K*`).
  have hKstarcyc : IsCyclic ↥Kstar :=
    (Subgroup.subgroupOfEquivOfLe (le_sup_right : Kstar ≤ K ⊔ Kstar)).isCyclic.mp inferInstance
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
    (show Nat.card ↥Kstar ≠ 1 from fun h => hKstarNe (Subgroup.card_eq_one.mp h))
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Kstar) p hpd
  set X : Subgroup G := Subgroup.zpowers (x : G) with hXdef
  have hxord : orderOf (x : G) = p :=
    (orderOf_injective Kstar.subtype Kstar.subtype_injective x).trans hx
  have hXcard : Nat.card ↥X = p := by rw [hXdef, Nat.card_zpowers, hxord]
  have hXKstar : X ≤ Kstar := by rw [hXdef, Subgroup.zpowers_le]; exact x.2
  have hXelem : X ∈ elemAbelianOfRank G p 1 :=
    mem_elemAbelianOfRank.mpr
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hNKstarX : Subgroup.normalizer (Kstar : Set G) ≤ Subgroup.normalizer (X : Set G) := by
    have : (X.subgroupOf Kstar).Characteristic := Ch04.characteristic_of_subgroup_of_isCyclic _
    intro g hg
    have hmem := OddOrder.BG.Ch1.S03f.mem_normalizer_map_subtype_of_characteristic
      (W := Kstar) (C := X.subgroupOf Kstar) hg
    rwa [Subgroup.map_subgroupOf_eq_of_le hXKstar] at hmem
  -- `N_{M*}(K*) = K* ⊔ K = K ⊔ K*`.
  have hNMst : Subgroup.normalizer (Kstar : Set G) ⊓ Mstar = K ⊔ Kstar := by
    refine le_antisymm ?_ ?_
    · calc Subgroup.normalizer (Kstar : Set G) ⊓ Mstar
          ≤ Subgroup.normalizer (X : Set G) ⊓ Mstar := inf_le_inf hNKstarX le_rfl
        _ = Kstar ⊔ K := hb1 p hp X hXelem hXKstar
        _ = K ⊔ Kstar := sup_comm _ _
    · refine le_inf (sup_le (hKcKstar.trans (Subgroup.centralizer_le_normalizer (Kstar : Set G)))
        Subgroup.le_normalizer) ?_
      exact sup_le (hKMsigmaMst.trans (OddOrder.BG.Ch3.S10.Msigma_le Mstar)) hKstarMst
  -- `ziMMst`: `M ⊓ M* = K ⊔ K*`.
  have hMN : M ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) := by
    rw [OddOrder.BG.Ch3.S10.Msigma]
    exact le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M
  have hziMMst : M ⊓ Mstar = K ⊔ Kstar := by
    refine le_antisymm ?_ (le_inf (sup_le hKM hKstarM)
      (sup_le (hKMsigmaMst.trans (OddOrder.BG.Ch3.S10.Msigma_le Mstar)) hKstarMst))
    have hsub : M ⊓ Mstar ≤ Subgroup.normalizer (Kstar : Set G) := by
      rw [← hMsMst]
      exact le_normalizer_inf (inf_le_left.trans hMN) (inf_le_right.trans Subgroup.le_normalizer)
    calc M ⊓ Mstar ≤ Subgroup.normalizer (Kstar : Set G) ⊓ Mstar := le_inf hsub inf_le_right
      _ = K ⊔ Kstar := hNMst
  -- `sK_uniqMst`: `K ≤ M*^a ⟹ a ∈ M*`.
  refine ⟨hziMMst, fun a hKa => ?_⟩
  by_contra haMst
  exact hKNe (le_bot_iff.mp ((hTI a haMst) ▸ le_inf le_rfl hKa))

end OddOrder.BG.Ch4.S14


