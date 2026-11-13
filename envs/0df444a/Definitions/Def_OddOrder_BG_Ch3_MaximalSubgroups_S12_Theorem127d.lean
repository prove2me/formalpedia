-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Theorem127d
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S12_Theorem127d
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:35:39.376241+00:00
-- url     : https://prove2.me/theorems/0cc49577-ec90-427d-a16b-aa662fbfe2de
-- title:
--   BG §12: Theorem 12.7(d) and assembly, the complement $E_0$ of $A_0$ in $E$
-- statement:
--   Formalizes Theorem 12.7(d) of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §12 and the assembly of the whole theorem: when $G$ has a nonabelian Sylow $p$-subgroup, the canonical line $A_0=A\sqcap C_G(M_\sigma)$ has a complement $E_0$ in $E$, i.e. $E_0\le E$, $A_0\sqcap E_0=\bot$ and $A_0\sqcup E_0=E$.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 8 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S12_Theorem127d.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S12_Theorem127d.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Theorem127
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_OperatorMaschke

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- Two subgroups of a common abelian overgroup centralize each other. -/
theorem le_centralizer_of_le_of_le {K H L : Subgroup G} (hK : IsMulCommutative ↥K)
    (hHK : H ≤ K) (hLK : L ≤ K) : H ≤ Subgroup.centralizer (L : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (hK.is_comm.comm (⟨y, hLK hy⟩ : ↥K) ⟨x, hHK hx⟩)

/-- A subgroup normalizing two subgroups normalizes their join. -/
theorem le_normalizer_sup {H K L : Subgroup G}
    (hK : H ≤ Subgroup.normalizer ((K : Subgroup G) : Set G))
    (hL : H ≤ Subgroup.normalizer ((L : Subgroup G) : Set G)) :
    H ≤ Subgroup.normalizer ((K ⊔ L : Subgroup G) : Set G) := by
  intro a ha
  refine mem_normalizer_of_conj_smul_eq_self ?_
  rw [mulAut_smul_eq_map, Subgroup.map_sup, ← mulAut_smul_eq_map, ← mulAut_smul_eq_map,
    conj_smul_eq_self_of_mem_normalizer (hK ha),
    conj_smul_eq_self_of_mem_normalizer (hL ha)]

/-- Two naturals with no common prime divisor are coprime.
(Public: `S12_Lemma128` reuses this for the `O_π × O_π'` order bookkeeping.) -/
theorem coprime_of_forall_prime_not_dvd {m n : ℕ}
    (h : ∀ r : ℕ, r.Prime → r ∣ m → ¬ r ∣ n) : Nat.Coprime m n := by
  by_contra hne
  obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd hne
  exact h r hr_prime (hr_dvd.trans (Nat.gcd_dvd_left m n))
    (hr_dvd.trans (Nat.gcd_dvd_right m n))

/-- With `τ₂(M)`-primes reduced to `{p}` (12.7(a)), the Hall `τ₂`-subgroup `E₂`
has order `p ^ ν_p(|E|)`, i.e. it is a Sylow `p`-subgroup of `E`. -/
theorem card_E2_eq_pow [Finite G] {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime] (hp : p ∈ tau2 M)
    (hprime_eq : ∀ q : ℕ, q.Prime → q ∈ tau2 M → q = p) :
    Nat.card ↥E₂ = p ^ (Nat.card ↥E).factorization p := by
  have hcard_eq : Nat.card ↥(E₂.subgroupOf E) = Nat.card ↥E₂ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv
  have hpi : ∀ r ∈ (Nat.card ↥E₂).primeFactors, r = p := by
    intro r hr
    have hr' : r ∈ (Nat.card ↥(E₂.subgroupOf E)).primeFactors := by rwa [hcard_eq]
    exact hprime_eq r (Nat.prime_of_mem_primeFactors hr) (h.E₂_hall.1 r hr')
  have hidx : ((E₂.subgroupOf E).index).factorization p = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    exact h.E₂_hall.2 p (Nat.mem_primeFactors.mpr
      ⟨Fact.out, hdvd, Subgroup.index_ne_zero_of_finite⟩) hp
  have hfac : (Nat.card ↥(E₂.subgroupOf E)).factorization p
      + ((E₂.subgroupOf E).index).factorization p = (Nat.card ↥E).factorization p := by
    rw [← Subgroup.card_mul_index (E₂.subgroupOf E),
      Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
      Finsupp.add_apply]
  have h1 : (Nat.card ↥E₂).factorization p = (Nat.card ↥E).factorization p := by
    rw [← hcard_eq]
    omega
  rw [eq_pow_factorization_of_forall_eq Nat.card_pos.ne' hpi, h1]

/-- `A` is absorbed into the Hall `τ₂`-subgroup `E₂`: `A ⊴ E` (12.6(a)) is contained
in every Sylow `p`-subgroup of `E`, and `E₂` is one (12.7(a)). -/
theorem elemAb_le_E2_of_prime_eq [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    (hprime_eq : ∀ q : ℕ, q.Prime → q ∈ tau2 M → q = p) :
    A ≤ E₂ := by
  classical
  have hE₂card : Nat.card ↥(E₂.subgroupOf E) = p ^ (Nat.card ↥E).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv]
    exact card_E2_eq_pow h hp hprime_eq
  set SE₂ : Sylow p ↥E := Sylow.ofCard (E₂.subgroupOf E) hE₂card with hSE₂def
  have hAnormal : (A.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAE).mpr
      (elemAb_normal_in_E_of_tau2 hG h hp hA hAE).1.1
  obtain ⟨TA, hATA⟩ := hA.1.isPGroup.comap_subtype.exists_le_sylow (G := E)
  obtain ⟨e, he⟩ := MulAction.exists_smul_eq ↥E TA SE₂
  intro a ha
  have h1 : (⟨a, hAE ha⟩ : ↥E) ∈ A.subgroupOf E := Subgroup.mem_subgroupOf.mpr ha
  have h2 : e⁻¹ * ⟨a, hAE ha⟩ * e ∈ TA := by
    refine hATA ?_
    have h3 := hAnormal.conj_mem _ h1 e⁻¹
    simpa using h3
  have h4 : (⟨a, hAE ha⟩ : ↥E) ∈ E₂.subgroupOf E := by
    have h5 : (⟨a, hAE ha⟩ : ↥E) ∈ (SE₂ : Subgroup ↥E) := by
      rw [← he, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      exact h2
    rwa [hSE₂def, Sylow.coe_ofCard] at h5
  exact Subgroup.mem_subgroupOf.mp h4

/-- `E₂` is abelian: it has the full `p`-part of `|M|` (`ν_p(E) = ν_p(M)`), hence is a
Sylow `p`-subgroup of `M`, and Theorem 12.5(b) makes those abelian. -/
theorem E2_isMulCommutative_of_prime_eq [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAM : A ≤ M)
    (hprime_eq : ∀ q : ℕ, q.Prime → q ∈ tau2 M → q = p) :
    IsMulCommutative ↥E₂ := by
  have hpσ : p ∉ S10.sigma M := tau2_subset_sigma_compl M hp
  have hE₂cardM : Nat.card ↥(E₂.subgroupOf M) = p ^ (Nat.card ↥M).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E2_le_M).toEquiv,
      card_E2_eq_pow h hp hprime_eq, factorization_card_eq_of_notMem_sigma h hpσ]
  have h125b := (Msigma_nilpotent_of_tau2 hG h.mem_maximal hp hA hAM).2.1.1
    (Sylow.ofCard (E₂.subgroupOf M) hE₂cardM)
  exact S11.isMulCommutative_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe h.E2_le_M) h125b

/-- **BG Theorem 12.7(d)** (mmd L3244): the canonical line `A₀` has a complement
`E₀` in `E`: `E₀ ≤ E`, `A₀ ⊓ E₀ = ⊥`, `A₀ ⊔ E₀ = E`.

`E₂ = C_{S'}(A) = A₀ × Z'` by Lemma 10.13(b) applied to a Sylow `p`-subgroup
`S' ⊇ E₂` of `G`, so `℧¹(E₂) ≤ Z'` misses `A₀`; Maschke
(`exists_aInvariant_complement_in_omega1_quotient`, with `E₁` acting coprimely on
`E₂/℧¹(E₂)`) yields an `E₁`-invariant complement `X` of `A₀` in `E₂`, and
`E₀ := E₁(X)(E₃)` works by the order count `|E₀| = |E|/p`. -/
theorem exists_complement_of_canonical_line [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    (hnonab : ∃ S : Sylow p G, ¬ IsMulCommutative (S : Subgroup G))
    (hprime_eq : ∀ q : ℕ, q.Prime → q ∈ tau2 M → q = p)
    {A₀ : Subgroup G} (hA₀A : A₀ ≤ A) (hA₀card : Nat.card ↥A₀ = p)
    (hMσC : S10.Msigma M ≤ Subgroup.centralizer (A₀ : Set G))
    (hMnorm : M ≤ Subgroup.normalizer (A₀ : Set G)) :
    ∃ E₀ : Subgroup G, E₀ ≤ E ∧ A₀ ⊓ E₀ = ⊥ ∧ A₀ ⊔ E₀ = E := by
  classical
  have hAM : A ≤ M := hAE.trans h.E_le
  have hpσ : p ∉ S10.sigma M := tau2_subset_sigma_compl M hp
  have hAE₂ : A ≤ E₂ := elemAb_le_E2_of_prime_eq hG h hp hA hAE hprime_eq
  have hA₀E₂ : A₀ ≤ E₂ := hA₀A.trans hAE₂
  have hE₂ab : IsMulCommutative ↥E₂ :=
    E2_isMulCommutative_of_prime_eq hG h hp hA hAM hprime_eq
  have hE₂card : Nat.card ↥E₂ = p ^ (Nat.card ↥E).factorization p :=
    card_E2_eq_pow h hp hprime_eq
  have hE₂pg : IsPGroup p ↥E₂ := IsPGroup.of_card hE₂card
  have hE₂cardE : Nat.card ↥(E₂.subgroupOf E) = p ^ (Nat.card ↥E).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv]
    exact hE₂card
  set SE₂ : Sylow p ↥E := Sylow.ofCard (E₂.subgroupOf E) hE₂cardE with hSE₂def
  have hmapSE₂ : ((SE₂ : Subgroup ↥E)).map E.subtype = E₂ := by
    rw [hSE₂def, Sylow.coe_ofCard]
    exact Subgroup.map_subgroupOf_eq_of_le h.E₂_le
  -- `A₀` is a line, and `C_G(A₀) ≤ M`.
  have hA₀mem : A₀ ∈ elemAbelianOfRank G p 1 := by
    refine ⟨Subgroup.IsElementaryAbelian.of_card_prime ?_, ?_⟩
    · rw [hA₀card]
    · rw [hA₀card, pow_one]
  have hMσ_ne : S10.Msigma M ≠ ⊥ := (S10.isHall_Msigma_Malpha hG h.mem_maximal).2.2.2.2
  have hA₀C : S10.Msigma M ⊓ Subgroup.centralizer (A₀ : Set G) ≠ ⊥ := by
    rwa [inf_eq_left.mpr hMσC]
  have hM_single : maximalSubgroupsContaining
      (Subgroup.centralizer (A₀ : Set G)) = {M} :=
    maximalContaining_centralizer_line_eq_singleton hG h hp hA hAE hA₀mem hA₀A hA₀C
  have hCA₀_le_M : Subgroup.centralizer (A₀ : Set G) ≤ M := by
    have hlt : Subgroup.centralizer (A₀ : Set G) < ⊤ :=
      lt_of_le_of_lt (Subgroup.centralizer_le_normalizer _)
        (normalizer_lt_top_of_le_of_ne_bot hG h.mem_maximal (hA₀A.trans hAM)
          (ne_bot_of_mem_elemAbelianOfRank_one hA₀mem))
    obtain ⟨Mst, hco, hle⟩ := (eq_top_or_exists_le_coatom _).resolve_left hlt.ne
    have hmem : Mst ∈ maximalSubgroupsContaining (Subgroup.centralizer (A₀ : Set G)) :=
      mem_maximalSubgroupsContaining.mpr ⟨hco, hle⟩
    rw [hM_single, Set.mem_singleton_iff] at hmem
    exact hmem ▸ hle
  -- a Sylow `p`-subgroup `S' ⊇ E₂` of `G`; it is nonabelian and not inside `M`.
  obtain ⟨S', hE₂S'⟩ := hE₂pg.exists_le_sylow
  have hS'_nonab : ¬ IsMulCommutative ((S' : Sylow p G) : Subgroup G) := by
    obtain ⟨S₀, hS₀⟩ := hnonab
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S₀ S'
    intro hab
    apply hS₀
    have hcoe : (S₀ : Subgroup G) = MulAut.conj g⁻¹ • (S' : Subgroup G) := by
      rw [← hg, Sylow.coe_subgroup_smul, ← mul_smul, ← map_mul, inv_mul_cancel,
        map_one, one_smul]
    rw [hcoe, mulAut_smul_eq_map]
    exact S11.isMulCommutative_of_mulEquiv
      (Subgroup.equivMapOfInjective _ _ (MulAut.conj g⁻¹).injective) hab
  have hS'_not_le_M : ¬ ((S' : Subgroup G) ≤ M) := by
    intro hS'M
    have hS'eq : (S' : Subgroup G) = E₂ :=
      (map_sylow_E_maximal_in_M h hpσ SE₂ (hmapSE₂.le.trans hE₂S') hS'M
        S'.isPGroup').trans hmapSE₂
    exact hS'_nonab (hS'eq ▸ hE₂ab)
  -- `A₀ ≠ Z₀' = Ω₁(Z(S'))` (else `S' ≤ C_G(A₀) ≤ M`).
  set Z₀' : Subgroup G := S10.omega1CenterInG (S' : Subgroup G) p with hZ₀'def
  have hZ₀'_eq : Z₀' = (omega1OfAbelian ↥(S' : Subgroup G)
      (Subgroup.center ↥(S' : Subgroup G)) p
      (fun _ hx y _ => (Subgroup.mem_center_iff.mp hx y).symm)).map
        (S' : Subgroup G).subtype := rfl
  have hS'_cent_Z₀ : (S' : Subgroup G) ≤ Subgroup.centralizer (Z₀' : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [SetLike.mem_coe, hZ₀'_eq, Subgroup.mem_map] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    have hz'c : z' ∈ Subgroup.center ↥(S' : Subgroup G) := (mem_omega1OfAbelian.mp hz').1
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz'c ⟨q, hq⟩)).symm
  have hA₀_ne_Z₀ : A₀ ≠ Z₀' := by
    rintro rfl
    exact hS'_not_le_M (hS'_cent_Z₀.trans hCA₀_le_M)
  -- Lemma 10.13(b): `C_{S'}(A) = A₀ ⊔ Z'` with `Z'` cyclic and `A₀ ⊓ Z' = ⊥`.
  have hAmax : IsMaximalElementaryAbelian p A :=
    (isMaximalElementaryAbelian_of_mem_tau2 hG h.mem_maximal Fact.out hp hAM hA).1
  have hpG : p ∈ (Nat.card G).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨Fact.out, ?_, Nat.card_pos.ne'⟩
    have h1 : (p : ℕ) ∣ Nat.card ↥A := by rw [hA.2]; exact dvd_pow_self p two_ne_zero
    exact h1.trans (Subgroup.card_subgroup_dvd_card A)
  obtain ⟨Z', hZ'S', hZ'cyc, hZ₀Z', hA₀Z'_bot, hCeq⟩ :=
    (S10.nonabelian_pSubgroup_rankTwo_elemAbelian_structure hG hpG hA hAmax
      S'.isPGroup' hS'_nonab (hAE₂.trans hE₂S') ⟨hA₀mem, hA₀A⟩ hA₀_ne_Z₀).2.1
  -- `C_{S'}(A) = E₂`, hence `E₂ = A₀ ⊔ Z'`.
  have hE₂_le_C : E₂ ≤ Subgroup.centralizer (A : Set G) :=
    le_centralizer_of_le_of_le hE₂ab le_rfl hAE₂
  have hCS'_le_M : Subgroup.centralizer (A : Set G) ⊓ (S' : Subgroup G) ≤ M :=
    (inf_le_left.trans (centralizer_le_E_of_tau2 hG h hp hA hAE).1).trans h.E_le
  have hCS'_eq : Subgroup.centralizer (A : Set G) ⊓ (S' : Subgroup G) = E₂ :=
    (map_sylow_E_maximal_in_M h hpσ SE₂
      (hmapSE₂.le.trans (le_inf hE₂_le_C hE₂S')) hCS'_le_M
      S'.isPGroup'.to_inf_right).trans hmapSE₂
  have hE₂_eq_sup : E₂ = A₀ ⊔ Z' := hCS'_eq.symm.trans hCeq
  have hZ'_le_E₂ : Z' ≤ E₂ := hE₂_eq_sup.symm ▸ le_sup_right
  -- `|E₂| = p · |Z'|`, so `Z'` has index `p` in `E₂` and `℧¹(E₂) ≤ Z'`.
  have hA₀_norm_Z' : A₀ ≤ Subgroup.normalizer ((Z' : Subgroup G) : Set G) :=
    (le_centralizer_of_le_of_le hE₂ab hA₀E₂ hZ'_le_E₂).trans
      (Subgroup.centralizer_le_normalizer _)
  have hcardE₂_eq : Nat.card ↥E₂ = p * Nat.card ↥Z' := by
    rw [hE₂_eq_sup,
      card_sup_eq_mul_of_le_normalizer_of_disjoint hA₀_norm_Z' hA₀Z'_bot, hA₀card]
  have hZ''norm : (Z'.subgroupOf E₂).Normal := by
    constructor
    intro n hn g
    have heq : g * n * g⁻¹ = n := by
      rw [hE₂ab.is_comm.comm g n]
      group
    rwa [heq]
  have hZ''idx : (Z'.subgroupOf E₂).index = p := by
    have hmul := Subgroup.card_mul_index (Z'.subgroupOf E₂)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ'_le_E₂).toEquiv, hcardE₂_eq] at hmul
    have h1 : Nat.card ↥Z' * (Z'.subgroupOf E₂).index = Nat.card ↥Z' * p := by
      rw [hmul]; ring
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hAgemo_le : Agemo ↥E₂ p 1 ≤ Z'.subgroupOf E₂ := by
    rw [Agemo, Subgroup.closure_le]
    rintro g ⟨x, rfl⟩
    have h1 := Subgroup.pow_index_mem (Z'.subgroupOf E₂) x
    rw [hZ''idx] at h1
    simpa [pow_one] using h1
  have hA₀_agemo_bot : A₀ ⊓ (Agemo ↥E₂ p 1).map E₂.subtype = ⊥ := by
    rw [← le_bot_iff, ← hA₀Z'_bot]
    refine inf_le_inf_left A₀ ?_
    calc (Agemo ↥E₂ p 1).map E₂.subtype
        ≤ (Z'.subgroupOf E₂).map E₂.subtype := Subgroup.map_mono hAgemo_le
      _ = Z' := Subgroup.map_subgroupOf_eq_of_le hZ'_le_E₂
  -- the conjugation action `φ : ↥E₁ →* MulAut ↥E₂` (`E₁ ≤ N_G(E₂)` by 12.1(e)).
  have hE₁_norm_E₂ : E₁ ≤ Subgroup.normalizer ((E₂ : Subgroup G) : Set G) :=
    le_sup_left.trans (h.E2_normal_in_E12 hG)
  let act : MulDistribMulAction ↥E₁ ↥E₂ :=
    MulDistribMulAction.compHom
      (M := ↥(Subgroup.normalizer ((E₂ : Subgroup G) : Set G))) ↥E₂
      (Subgroup.inclusion hE₁_norm_E₂)
  set φ : ↥E₁ →* MulAut ↥E₂ := MulDistribMulAction.toMulAut ↥E₁ ↥E₂ with hφdef
  have hφ_coe : ∀ (a : ↥E₁) (x : ↥E₂),
      (((φ a) x : ↥E₂) : G) = (↑a) * (↑x : G) * (↑a)⁻¹ := fun _ _ => rfl
  -- Maschke inputs.
  have hpR : p ∣ Nat.card ↥E₂ := by
    rw [hcardE₂_eq]
    exact Dvd.intro _ rfl
  have hcop : Nat.Coprime (Nat.card ↥E₁) (Nat.card ↥E₂) := by
    refine coprime_of_forall_prime_not_dvd ?_
    intro r hr_prime hrE₁ hrE₂
    have hr1 : r ∈ tau1 M := h.E₁_hall.1 r (Nat.mem_primeFactors.mpr ⟨hr_prime, by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv],
      Nat.card_pos.ne'⟩)
    have hrp : r = p := by
      have h1 : r ∣ p ^ (Nat.card ↥E).factorization p := hE₂card ▸ hrE₂
      exact (Nat.prime_dvd_prime_iff_eq hr_prime Fact.out).mp
        (hr_prime.dvd_of_dvd_pow h1)
    have h1 := tau1_pRank_eq_one hr1
    have h2 := tau2_pRank_eq_two hp
    rw [hrp] at h1
    omega
  set Sg : Subgroup ↥E₂ := Agemo ↥E₂ p 1 with hSgdef
  have hS_inv : Ch03.IsAInvariant φ Sg := Ch03.IsAInvariant.of_characteristic φ
  have hQab : ∀ x y : ↥E₂ ⧸ Sg, x * y = y * x := by
    intro x y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective Sg x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective Sg y
    rw [← map_mul, ← map_mul, hE₂ab.is_comm.comm a b]
  set W₀ : Subgroup ↥E₂ := A₀.subgroupOf E₂ with hW₀def
  have hWinv : Ch03.IsAInvariant φ W₀ := by
    rw [Ch03.isAInvariant_iff_smul_mem]
    intro a g hg
    rw [hW₀def, Subgroup.mem_subgroupOf] at hg ⊢
    have haN : (↑a : G) ∈ Subgroup.normalizer (A₀ : Set G) := hMnorm (h.E1_le_M a.2)
    have h1 := (Subgroup.mem_normalizer_iff.mp haN (↑g : G)).mp hg
    rwa [show (((φ a) g : ↥E₂) : G) = (↑a) * (↑g : G) * (↑a)⁻¹ from hφ_coe a g]
  have hWΩ : W₀.map (QuotientGroup.mk' Sg) ≤ Omega (↥E₂ ⧸ Sg) p 1 := by
    rintro _ ⟨g, _, rfl⟩
    refine Omega.mem_of_pow_eq_one ?_
    rw [pow_one, ← map_pow]
    refine (QuotientGroup.eq_one_iff _).mpr ?_
    rw [hSgdef]
    simpa [pow_one] using Agemo.mem_of_eq_pow (G := ↥E₂) (p := p) (n := 1) g
  -- Maschke: an `E₁`-invariant complement `X'` of `Ā₀` in `E₂/℧¹(E₂)`.
  obtain ⟨X', hSX', hX'inv, _hX'Ω, hX'inf, hX'sup⟩ :=
    Ch1_Preliminary.exists_aInvariant_complement_in_omega1_quotient
      hpR hcop hS_inv hQab hWinv hWΩ
  -- the quotient has exponent `p`, so `Ω₁ = ⊤`.
  have hΩtop : Omega (↥E₂ ⧸ Sg) p 1 = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective Sg x
    refine Omega.mem_of_pow_eq_one ?_
    rw [pow_one, ← map_pow]
    refine (QuotientGroup.eq_one_iff _).mpr ?_
    rw [hSgdef]
    simpa [pow_one] using Agemo.mem_of_eq_pow (G := ↥E₂) (p := p) (n := 1) a
  -- descend to `X ≤ E₂`: a complement of `A₀` in `E₂`.
  set X : Subgroup G := X'.map E₂.subtype with hXdef
  have hX_le_E₂ : X ≤ E₂ := Subgroup.map_subtype_le _
  have hA₀X_bot : A₀ ⊓ X = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgA₀, hgX⟩
    obtain ⟨g', hg', hg'eq⟩ := hgX
    have hg'W : g' ∈ W₀ := by
      rw [hW₀def, Subgroup.mem_subgroupOf]
      show (g' : G) ∈ A₀
      rw [show ((g' : ↥E₂) : G) = g from hg'eq]
      exact hgA₀
    have hmk : (QuotientGroup.mk' Sg) g' ∈
        X'.map (QuotientGroup.mk' Sg) ⊓ W₀.map (QuotientGroup.mk' Sg) :=
      ⟨⟨g', hg', rfl⟩, ⟨g', hg'W, rfl⟩⟩
    rw [hX'inf, Subgroup.mem_bot] at hmk
    have hg'S : g' ∈ Sg := (QuotientGroup.eq_one_iff _).mp hmk
    have hmem : g ∈ A₀ ⊓ (Agemo ↥E₂ p 1).map E₂.subtype :=
      ⟨hgA₀, ⟨g', by rwa [← hSgdef], hg'eq⟩⟩
    rwa [hA₀_agemo_bot] at hmem
  have hA₀X_sup : A₀ ⊔ X = E₂ := by
    refine le_antisymm (sup_le hA₀E₂ hX_le_E₂) ?_
    intro x hx
    have hmk_top : (QuotientGroup.mk' Sg) ⟨x, hx⟩ ∈
        (X' ⊔ W₀).map (QuotientGroup.mk' Sg) := by
      rw [Subgroup.map_sup, hX'sup, hΩtop]
      exact Subgroup.mem_top _
    have hx' : (⟨x, hx⟩ : ↥E₂) ∈ X' ⊔ W₀ := by
      have h1 : (⟨x, hx⟩ : ↥E₂) ∈ (X' ⊔ W₀) ⊔ Sg := by
        have h2 : (⟨x, hx⟩ : ↥E₂) ∈
            ((X' ⊔ W₀).map (QuotientGroup.mk' Sg)).comap (QuotientGroup.mk' Sg) :=
          Subgroup.mem_comap.mpr hmk_top
        rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2
      rwa [sup_eq_left.mpr (hSX'.trans le_sup_left)] at h1
    have hmap : x ∈ (X' ⊔ W₀).map E₂.subtype := ⟨⟨x, hx⟩, hx', rfl⟩
    rw [Subgroup.map_sup, hW₀def, Subgroup.map_subgroupOf_eq_of_le hA₀E₂] at hmap
    exact (sup_comm X A₀) ▸ hmap
  -- `E₁` normalizes `X` (transport of the Maschke invariance to `G`).
  have hE₁_norm_X : E₁ ≤ Subgroup.normalizer ((X : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨g', hg', rfl⟩
      refine ⟨(φ ⟨a, ha⟩) g', hX'inv.smul_mem _ hg', ?_⟩
      exact hφ_coe ⟨a, ha⟩ g'
    · intro hgX
      obtain ⟨g', hg', hg'eq⟩ := hgX
      have hg'c : (↑g' : G) = a * g * a⁻¹ := hg'eq
      refine ⟨(φ ⟨a, ha⟩⁻¹) g', hX'inv.smul_mem ⟨a, ha⟩⁻¹ hg', ?_⟩
      change (((φ ⟨a, ha⟩⁻¹) g' : ↥E₂) : G) = g
      rw [hφ_coe ⟨a, ha⟩⁻¹ g', hg'c]
      change a⁻¹ * (a * g * a⁻¹) * a⁻¹⁻¹ = g
      group
  -- order bookkeeping: `|E₀| = |E| / p` for `E₀ := E₁ ⊔ (X ⊔ E₃)`.
  have hX_E₃_bot : X ⊓ E₃ = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard (coprime_of_forall_prime_not_dvd ?_)).eq_bot
    intro r hr hrX hrE₃
    have hrp : r = p := by
      have h1 : r ∣ p ^ (Nat.card ↥E).factorization p :=
        hE₂card ▸ (hrX.trans (Subgroup.card_dvd_of_le hX_le_E₂))
      exact (Nat.prime_dvd_prime_iff_eq hr Fact.out).mp (hr.dvd_of_dvd_pow h1)
    have hr3 : r ∈ tau3 M := h.E₃_hall.1 r (Nat.mem_primeFactors.mpr ⟨hr, by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv],
      Nat.card_pos.ne'⟩)
    have h1 := tau3_pRank_eq_one hr3
    have h2 := tau2_pRank_eq_two hp
    rw [hrp] at h1
    omega
  have hX_norm_E₃ : X ≤ Subgroup.normalizer ((E₃ : Subgroup G) : Set G) :=
    (hX_le_E₂.trans h.E₂_le).trans (h.E3_normal hG)
  have hcard_XE₃ : Nat.card ↥(X ⊔ E₃ : Subgroup G) = Nat.card ↥X * Nat.card ↥E₃ :=
    card_sup_eq_mul_of_le_normalizer_of_disjoint hX_norm_E₃ hX_E₃_bot
  have hE₁_XE₃_bot : E₁ ⊓ (X ⊔ E₃) = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard (coprime_of_forall_prime_not_dvd ?_)).eq_bot
    intro r hr hrE₁ hrXE₃
    have hr1 : r ∈ tau1 M := h.E₁_hall.1 r (Nat.mem_primeFactors.mpr ⟨hr, by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv],
      Nat.card_pos.ne'⟩)
    rw [hcard_XE₃] at hrXE₃
    rcases (Nat.Prime.dvd_mul hr).mp hrXE₃ with hrX | hrE₃
    · have hrp : r = p := by
        have h1 : r ∣ p ^ (Nat.card ↥E).factorization p :=
          hE₂card ▸ (hrX.trans (Subgroup.card_dvd_of_le hX_le_E₂))
        exact (Nat.prime_dvd_prime_iff_eq hr Fact.out).mp (hr.dvd_of_dvd_pow h1)
      have h1 := tau1_pRank_eq_one hr1
      have h2 := tau2_pRank_eq_two hp
      rw [hrp] at h1
      omega
    · have hr3 : r ∈ tau3 M := h.E₃_hall.1 r (Nat.mem_primeFactors.mpr ⟨hr, by
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv],
        Nat.card_pos.ne'⟩)
      exact not_mem_tau3_of_mem_tau1 hr1 hr3
  have hE₁_norm_XE₃ : E₁ ≤ Subgroup.normalizer ((X ⊔ E₃ : Subgroup G) : Set G) :=
    le_normalizer_sup hE₁_norm_X (h.E₁_le.trans (h.E3_normal hG))
  set E₀ : Subgroup G := E₁ ⊔ (X ⊔ E₃) with hE₀def
  have hcard_E₀ : Nat.card ↥E₀ = Nat.card ↥E₁ * (Nat.card ↥X * Nat.card ↥E₃) := by
    rw [hE₀def, card_sup_eq_mul_of_le_normalizer_of_disjoint hE₁_norm_XE₃ hE₁_XE₃_bot,
      hcard_XE₃]
  -- `|E₂| = p · |X|`.
  have hX_norm_A₀ : X ≤ Subgroup.normalizer (A₀ : Set G) :=
    ((hX_le_E₂.trans h.E₂_le).trans h.E_le).trans hMnorm
  have hcardE₂_eq_pX : Nat.card ↥E₂ = p * Nat.card ↥X := by
    have hA₀_norm_X : A₀ ≤ Subgroup.normalizer ((X : Subgroup G) : Set G) :=
      (le_centralizer_of_le_of_le hE₂ab hA₀E₂ hX_le_E₂).trans
        (Subgroup.centralizer_le_normalizer _)
    rw [← hA₀X_sup,
      card_sup_eq_mul_of_le_normalizer_of_disjoint hA₀_norm_X hA₀X_bot, hA₀card]
  -- `|E| = |E₁| · |E₂| · |E₃|`.
  have hE₁E₂_bot : E₁ ⊓ E₂ = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hcard_E₁E₂ : Nat.card ↥(E₁ ⊔ E₂ : Subgroup G)
      = Nat.card ↥E₁ * Nat.card ↥E₂ :=
    card_sup_eq_mul_of_le_normalizer_of_disjoint hE₁_norm_E₂ hE₁E₂_bot
  have hE₁₂_E₃_bot : (E₁ ⊔ E₂) ⊓ E₃ = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard (coprime_of_forall_prime_not_dvd ?_)).eq_bot
    intro r hr hrE₁₂ hrE₃
    have hr3 : r ∈ tau3 M := h.E₃_hall.1 r (Nat.mem_primeFactors.mpr ⟨hr, by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv],
      Nat.card_pos.ne'⟩)
    rw [hcard_E₁E₂] at hrE₁₂
    rcases (Nat.Prime.dvd_mul hr).mp hrE₁₂ with hrE₁ | hrE₂
    · have hr1 : r ∈ tau1 M := h.E₁_hall.1 r (Nat.mem_primeFactors.mpr ⟨hr, by
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv],
        Nat.card_pos.ne'⟩)
      exact not_mem_tau3_of_mem_tau1 hr1 hr3
    · have hrp : r = p := by
        have h1 : r ∣ p ^ (Nat.card ↥E).factorization p := hE₂card ▸ hrE₂
        exact (Nat.prime_dvd_prime_iff_eq hr Fact.out).mp (hr.dvd_of_dvd_pow h1)
      have h1 := tau3_pRank_eq_one hr3
      have h2 := tau2_pRank_eq_two hp
      rw [hrp] at h1
      omega
  have hE₁₂_norm_E₃ : E₁ ⊔ E₂ ≤ Subgroup.normalizer ((E₃ : Subgroup G) : Set G) :=
    h.E12_le_E.trans (h.E3_normal hG)
  have hcard_E : Nat.card ↥E = Nat.card ↥E₁ * Nat.card ↥E₂ * Nat.card ↥E₃ := by
    rw [show E = E₁ ⊔ E₂ ⊔ E₃ from h.eq_sup hG,
      card_sup_eq_mul_of_le_normalizer_of_disjoint hE₁₂_norm_E₃ hE₁₂_E₃_bot,
      hcard_E₁E₂]
  have hcard_E_eq : Nat.card ↥E = p * Nat.card ↥E₀ := by
    rw [hcard_E, hcardE₂_eq_pX, hcard_E₀]
    ring
  -- assembly.
  have hE₀_le_E : E₀ ≤ E :=
    sup_le h.E₁_le (sup_le (hX_le_E₂.trans h.E₂_le) h.E₃_le)
  have hsup : A₀ ⊔ E₀ = E := by
    refine le_antisymm (sup_le (hA₀E₂.trans h.E₂_le) hE₀_le_E) ?_
    rw [show E = E₁ ⊔ E₂ ⊔ E₃ from h.eq_sup hG]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact le_sup_of_le_right le_sup_left
    · rw [← hA₀X_sup]
      exact sup_le le_sup_left
        (le_sup_of_le_right (le_sup_of_le_right le_sup_left))
    · exact le_sup_of_le_right (le_sup_of_le_right le_sup_right)
  have hbot : A₀ ⊓ E₀ = ⊥ := by
    have h1 : Nat.card ↥(A₀ ⊓ E₀ : Subgroup G) ∣ p := by
      rw [← hA₀card]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.Prime.eq_one_or_self_of_dvd Fact.out _ h1) with h2 | h2
    · exact Subgroup.card_eq_one.mp h2
    · exfalso
      have hA₀_le_E₀ : A₀ ≤ E₀ := by
        have h3 : A₀ ⊓ E₀ = A₀ := by
          refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
          rw [hA₀card, h2]
        exact h3 ▸ inf_le_right
      have h4 : Nat.card ↥E = Nat.card ↥E₀ := by
        rw [← hsup, sup_eq_right.mpr hA₀_le_E₀]
      rw [hcard_E_eq] at h4
      have hp1 : p = 1 :=
        Nat.eq_of_mul_eq_mul_right Nat.card_pos (h4.trans (one_mul _).symm)
      exact (Fact.out : p.Prime).one_lt.ne' hp1
  exact ⟨E₀, hE₀_le_E, hbot, hsup⟩

/-- **BG Theorem 12.7** (mmd L3201-3251): `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)`, and `G` has
nonabelian Sylow `p`-subgroups. Then
(a) `p` is the only prime in `τ₂(M)`;
(b) `A₀ = A ⊓ C_G(M_σ)` has order `p`, and `F(M) = M_σ × A₀`;
(c) every other line `X ∈ ℰ_p¹(E)` has `C_{M_σ}(X) = 1` and `C_G(X) ⊄ M`;
(d) `A₀` has a complement `E₀` in `E`; and
(e) `π(C_{E₀}(x)) ⊆ τ₁(M)` for all `x ∈ M_σ#`.

⚠ **(a) の faithful 化**: repo の `tau2` は素数性を要求しないため、集合等式
`tau2 M = {p}` ではなく素数限定形 `∀ q, q.Prime → q ∈ tau2 M → q = p` で述べる
(BG の τ₂ は暗黙に素数集合; 下流が使うのは素数形のみ)。内部直積 `F(M) = M_σ × A₀`
は join + 自明交叉で表現する。 -/
theorem tau2_singleton_of_nonabelianSylow [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    (hnonab : ∃ S : Sylow p G, ¬ IsMulCommutative (S : Subgroup G)) :
    (∀ q : ℕ, q.Prime → q ∈ tau2 M → q = p) ∧
    (∃ A₀ : Subgroup G, A₀ = A ⊓ Subgroup.centralizer (S10.Msigma M : Set G) ∧
      Nat.card ↥A₀ = p ∧
      (Ch2.S08.fittingInG M = S10.Msigma M ⊔ A₀ ∧ S10.Msigma M ⊓ A₀ = ⊥) ∧
      (∀ X ∈ elemAbelianOfRank G p 1, X ≤ E → X ≠ A₀ →
        S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) = ⊥ ∧
        ¬ (Subgroup.centralizer (X : Set G) ≤ M)) ∧
      (∃ E₀ : Subgroup G, E₀ ≤ E ∧ A₀ ⊓ E₀ = ⊥ ∧ A₀ ⊔ E₀ = E ∧
        ∀ x ∈ S10.Msigma M, x ≠ 1 →
          ∀ r ∈ (Nat.card ↥(E₀ ⊓ Subgroup.centralizer ({x} : Set G) :
            Subgroup G)).primeFactors, r ∈ tau1 M)) := by
  have hprime_eq : ∀ q : ℕ, q.Prime → q ∈ tau2 M → q = p := fun q hq_prime hq2 =>
    tau2_prime_eq_of_nonabelianSylow hG h hp hA hAE hnonab hq_prime hq2
  obtain ⟨A₀, hA₀eq, hA₀card, hA₀A, hMσC, hc, habs⟩ :=
    exists_canonical_line_of_nonabelianSylow hG h hp hA hAE hnonab
  obtain ⟨hMnorm, hF, hbotσ⟩ :=
    fitting_eq_sup_of_canonical_line hG h hp hA hAE hprime_eq hA₀eq hA₀card hMσC habs
  obtain ⟨E₀, hE₀E, hbot, hsup⟩ :=
    exists_complement_of_canonical_line hG h hp hA hAE hnonab hprime_eq hA₀A hA₀card
      hMσC hMnorm
  refine ⟨hprime_eq, A₀, hA₀eq, hA₀card, ⟨hF, hbotσ⟩, hc, E₀, hE₀E, hbot, hsup, ?_⟩
  intro x hx hx1
  exact primeFactors_centralizer_le_tau1_of_disjoint hG h hp hA hAE hprime_eq hc
    hE₀E hbot hx hx1

end OddOrder.BG.Ch3.S12


