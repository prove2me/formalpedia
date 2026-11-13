-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Lemma128
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S12_Lemma128
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:50:48.703192+00:00
-- url     : https://prove2.me/theorems/dbb9eb1c-4eb8-4401-b2a9-9c4b7428e817
-- title:
--   BG §12: Lemma 12.8, the abelian Sylow $p$-subgroup case
-- statement:
--   Formalizes Lemma 12.8 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §12, complementary to Theorem 12.7: for $p\in\tau_2(M)$, $A\in\mathcal{E}_p^2(E)$ and an abelian Sylow $p$-subgroup $S\supseteq A$ of $G$, (a) $E_2$ is an abelian normal subgroup of $E$, (b) $E_2$ is a Hall $\tau_2(M)$-subgroup of $G$, (c) $S\subseteq N_G(S)'\subseteq F(E)\subseteq C_G(S)\subseteq E$, with parts (d) and (e) continued in the next file.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 15 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S12_Lemma128.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S12_Lemma128.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Theorem127d

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BG Corollary 10.7(a), complement-free form**: a Sylow `p`-subgroup of `G` lies in
the derived subgroup of its normalizer. The Schur–Zassenhaus complement is supplied by
`S10.exists_sylow_complement_normalizer`. -/
theorem sylow_le_derivedInG_normalizer [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    (P : Subgroup G) ≤ derivedInG (Subgroup.normalizer ((P : Subgroup G) : Set G)) := by
  obtain ⟨V, hV, hinf, hsup⟩ := S10.exists_sylow_complement_normalizer P
  exact ((S10.sylow_structure hG P).1 V hV hinf hsup).2

/-- `derivedInG` is monotone. -/
theorem derivedInG_le_derivedInG {H K : Subgroup G} (hHK : H ≤ K) :
    derivedInG H ≤ derivedInG K := by
  rw [show derivedInG H = ⁅H, H⁆ from Subgroup.map_subtype_commutator H,
    show derivedInG K = ⁅K, K⁆ from Subgroup.map_subtype_commutator K]
  exact Subgroup.commutator_mono hHK hHK

/-- If some Sylow `p`-subgroup of `G` (`p ∈ τ₂(M)`) is abelian, then **every** Sylow
`q`-subgroup of `G` for **every** prime `q ∈ τ₂(M)` is abelian: a nonabelian Sylow
`q`-subgroup would force `τ₂`-primes to equal `q` (Theorem 12.7(a)), i.e. `p = q`,
contradicting Sylow conjugacy with the abelian `S`. -/
theorem sylow_isMulCommutative_of_tau2_of_abelian [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (_hA : A ∈ elemAbelianOfRank G p 2) (_hAE : A ≤ E)
    {S : Sylow p G} (hSab : IsMulCommutative ↥(S : Subgroup G))
    {q : ℕ} [Fact q.Prime] (hq : q ∈ tau2 M) (Sq : Sylow q G) :
    IsMulCommutative ↥(Sq : Subgroup G) := by
  by_contra hnonab
  obtain ⟨B, hB, hBE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG h hq
  have hpq : p = q :=
    tau2_prime_eq_of_nonabelianSylow hG h hq hB hBE ⟨Sq, hnonab⟩ Fact.out hp
  subst hpq
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Sq
  apply hnonab
  have hcoe : (Sq : Subgroup G) = MulAut.conj g • (S : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul]
  rw [hcoe, mulAut_smul_eq_map]
  exact S11.isMulCommutative_of_mulEquiv
    (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective) hSab

/-- For each prime `q ∈ τ₂(M)`, some (abelian) Sylow `q`-subgroup of `G` lies inside
`E`: it contains a rank-two `B ∈ ℰ_q²(E)`, centralizes it (being abelian), and
`C_G(B) ≤ E` by Corollary 12.6(b). -/
theorem exists_sylow_le_E_of_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {S : Sylow p G} (hSab : IsMulCommutative ↥(S : Subgroup G))
    {q : ℕ} [Fact q.Prime] (hq : q ∈ tau2 M) :
    ∃ B ∈ elemAbelianOfRank G q 2, B ≤ E ∧
      ∃ Sq : Sylow q G, B ≤ (Sq : Subgroup G) ∧ (Sq : Subgroup G) ≤ E := by
  obtain ⟨B, hB, hBE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG h hq
  obtain ⟨Sq, hBSq⟩ := hB.1.isPGroup.exists_le_sylow
  refine ⟨B, hB, hBE, Sq, hBSq, ?_⟩
  calc (Sq : Subgroup G)
      ≤ Subgroup.centralizer (B : Set G) :=
        le_centralizer_of_le_of_le
          (sylow_isMulCommutative_of_tau2_of_abelian hG h hp hA hAE hSab hq Sq)
          le_rfl hBSq
    _ ≤ E := (centralizer_le_E_of_tau2 hG h hq hB hBE).1

/-- For each prime `q ∈ τ₂(M)`, the `q`-parts of `|E|` and `|G|` agree (`E` contains a
full Sylow `q`-subgroup of `G`). -/
theorem factorization_card_E_eq_of_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {S : Sylow p G} (hSab : IsMulCommutative ↥(S : Subgroup G))
    {q : ℕ} [Fact q.Prime] (hq : q ∈ tau2 M) :
    (Nat.card ↥E).factorization q = (Nat.card G).factorization q := by
  obtain ⟨B, hB, hBE, Sq, hBSq, hSqE⟩ := exists_sylow_le_E_of_tau2 hG h hp hA hAE hSab hq
  refine le_antisymm ?_ ?_
  · exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
      (Subgroup.card_subgroup_dvd_card E) q
  · rw [← Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne',
      ← Sq.card_eq_multiplicity]
    exact Subgroup.card_dvd_of_le hSqE

/-- A subgroup of an abelian subgroup is abelian. -/
theorem isMulCommutative_of_le {H K : Subgroup G} (hK : IsMulCommutative ↥K)
    (hHK : H ≤ K) : IsMulCommutative ↥H := by
  constructor
  constructor
  intro a b
  have h1 := hK.is_comm.comm (⟨a, hHK a.2⟩ : ↥K) ⟨b, hHK b.2⟩
  have h2 : (a : G) * b = (b : G) * a := congrArg Subtype.val h1
  exact Subtype.ext h2

/-- In a finite nilpotent group, `O_π` and `O_π'` generate: their orders multiply to
`|K|` (both are Hall by `oPiCore_isHall_of_isNilpotent`), so the join is everything. -/
theorem oPiCore_sup_compl_eq_top (K : Type*) [Group K] [Finite K]
    [Group.IsNilpotent K] (π : Set ℕ) :
    Ch03.oPiCore π K ⊔ Ch03.oPiCore πᶜ K = ⊤ := by
  classical
  have hall1 := S10.oPiCore_isHall_of_isNilpotent (K := K) π
  have hall2 := S10.oPiCore_isHall_of_isNilpotent (K := K) πᶜ
  -- coprime orders, hence trivial intersection
  have hcop : Nat.Coprime (Nat.card ↥(Ch03.oPiCore π K))
      (Nat.card ↥(Ch03.oPiCore πᶜ K)) := by
    refine coprime_of_forall_prime_not_dvd ?_
    intro r hr h1 h2
    have hr1 : r ∈ π := hall1.1 r (Nat.mem_primeFactors.mpr ⟨hr, h1, Nat.card_pos.ne'⟩)
    have hr2 : r ∈ πᶜ := hall2.1 r (Nat.mem_primeFactors.mpr ⟨hr, h2, Nat.card_pos.ne'⟩)
    exact hr2 hr1
  have hbot : Ch03.oPiCore π K ⊓ Ch03.oPiCore πᶜ K = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  -- the factorization of `|O_π| · |O_π'|` agrees with that of `|K|` at every prime
  have hcard : Nat.card ↥(Ch03.oPiCore π K) * Nat.card ↥(Ch03.oPiCore πᶜ K)
      = Nat.card K := by
    have hfac : ∀ (π₀ : Set ℕ) (r : ℕ), r.Prime → r ∈ π₀ →
        (Nat.card ↥(Ch03.oPiCore π₀ K)).factorization r = (Nat.card K).factorization r := by
      intro π₀ r hr hrπ
      have hidx : ((Ch03.oPiCore π₀ K).index).factorization r = 0 := by
        apply Nat.factorization_eq_zero_of_not_dvd
        intro hdvd
        exact S10.oPiCore_isHall_of_isNilpotent (K := K) π₀ |>.2 r
          (Nat.mem_primeFactors.mpr ⟨hr, hdvd, Subgroup.index_ne_zero_of_finite⟩) hrπ
      have hsum : (Nat.card ↥(Ch03.oPiCore π₀ K)).factorization r
          + ((Ch03.oPiCore π₀ K).index).factorization r
          = (Nat.card K).factorization r := by
        rw [← Subgroup.card_mul_index (Ch03.oPiCore π₀ K),
          Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
          Finsupp.add_apply]
      omega
    have hzero : ∀ (π₀ : Set ℕ) (r : ℕ), r.Prime → r ∉ π₀ →
        (Nat.card ↥(Ch03.oPiCore π₀ K)).factorization r = 0 := by
      intro π₀ r hr hrπ
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hdvd
      exact hrπ (S10.oPiCore_isHall_of_isNilpotent (K := K) π₀ |>.1 r
        (Nat.mem_primeFactors.mpr ⟨hr, hdvd, Nat.card_pos.ne'⟩))
    refine Nat.eq_of_factorization_eq (Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne')
      Nat.card_pos.ne' ?_
    intro r
    by_cases hr : r.Prime
    case neg =>
      rw [Nat.factorization_eq_zero_of_not_prime _ hr,
        Nat.factorization_eq_zero_of_not_prime _ hr]
    case pos =>
      rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply]
      by_cases hrπ : r ∈ π
      · rw [hfac π r hr hrπ, hzero πᶜ r hr (by simpa using hrπ)]
        omega
      · rw [hfac πᶜ r hr (by simpa using hrπ), hzero π r hr hrπ]
        omega
  -- join has full order
  have hnorm : Ch03.oPiCore π K ≤
      Subgroup.normalizer ((Ch03.oPiCore πᶜ K : Subgroup K) : Set K) := by
    intro x _
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact (Ch03.oPiCore.normal πᶜ K).conj_mem y hy x
    · intro hy
      have h1 := (Ch03.oPiCore.normal πᶜ K).conj_mem _ hy x⁻¹
      simpa [mul_assoc] using h1
  have hsup_card := card_sup_eq_mul_of_le_normalizer_of_disjoint hnorm hbot
  refine Subgroup.eq_top_of_card_eq _ ?_
  rw [hsup_card, hcard]

/-- The normalizer of a Sylow `q`-subgroup `Sq ≤ M` containing `B ∈ ℰ_q²(E)` lands in
`N_G(B)` (`B = Ω₁(Sq)` is characteristic), and escapes `M` (`omega1_eq_of_tau2`). -/
theorem normalizer_sylow_le_normalizer_elemAb [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {q : ℕ} [Fact q.Prime] (hq : q ∈ tau2 M)
    {B : Subgroup G} (hB : B ∈ elemAbelianOfRank G q 2) (hBE : B ≤ E)
    {Sq : Sylow q G} (hBSq : B ≤ (Sq : Subgroup G)) (hSqM : (Sq : Subgroup G) ≤ M) :
    Subgroup.normalizer ((Sq : Subgroup G) : Set G) ≤ Subgroup.normalizer (B : Set G) ∧
    ¬ (Subgroup.normalizer ((Sq : Subgroup G) : Set G) ≤ M) := by
  have hBM : B ≤ M := hBE.trans h.E_le
  have hPsyl : ∀ R : Subgroup G, (Sq : Subgroup G) ≤ R → R ≤ M → IsPGroup q ↥R →
      R = (Sq : Subgroup G) := by
    intro R hSqR _ hRpg
    refine (Subgroup.eq_of_le_of_card_ge hSqR ?_).symm
    obtain ⟨k, hk⟩ := hRpg.exists_card_eq
    rw [Sq.card_eq_multiplicity, hk]
    refine Nat.pow_le_pow_right (Fact.out : q.Prime).pos ?_
    rw [← Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne', ← hk]
    exact Subgroup.card_subgroup_dvd_card R
  obtain ⟨hBeq, hnotle⟩ := omega1_eq_of_tau2 hG h.mem_maximal hq hB hBM
    Sq.isPGroup' hBSq hSqM hPsyl
  refine ⟨?_, hnotle⟩
  rw [hBeq]
  exact AppB.normalizer_le_normalizer_map_of_characteristic

/-- **Fitting chain core**: for `q ∈ τ₂(M)` and `B ∈ ℰ_q²(E)` — assuming every
`q`-subgroup of `G` is abelian — the derived subgroup of `N := N_G(B)` lies in `F(E)`.

`F(N) ≤ C_G(B)` (the `O_q`-part is an abelian `q`-group containing `B`, the
`O_q'`-part commutes with `B` by coprimality), so `F(N) ≤ E` (Corollary 12.6(b)) and
`F(N) ≤ F(E)` (it is a nilpotent subgroup normalized by `E ≤ N`); `N' ≤ F(N)` by
Theorem 4.20(a), since `r(F(N)) ≤ r(E) ≤ 2`. The intermediate facts
`F(N) ≤ C_G(B)` and `F(N) ≤ F(E)` are exported for Lemma 12.8(d). -/
theorem derivedInG_normalizer_elemAb_le_fittingInG [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {q : ℕ} [Fact q.Prime] (hq : q ∈ tau2 M)
    {B : Subgroup G} (hB : B ∈ elemAbelianOfRank G q 2) (hBE : B ≤ E)
    (hallab : ∀ T : Subgroup G, IsPGroup q ↥T → IsMulCommutative ↥T) :
    derivedInG (Subgroup.normalizer (B : Set G)) ≤ Ch2.S08.fittingInG E ∧
    Ch2.S08.fittingInG (Subgroup.normalizer (B : Set G)) ≤
      Subgroup.centralizer (B : Set G) ∧
    Ch2.S08.fittingInG (Subgroup.normalizer (B : Set G)) ≤ Ch2.S08.fittingInG E := by
  classical
  set N : Subgroup G := Subgroup.normalizer (B : Set G) with hNdef
  have hBM : B ≤ M := hBE.trans h.E_le
  have hBne : B ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥B = q ^ 2 := hB.2
    rw [hbot, Subgroup.card_bot] at h1
    exact (Nat.one_lt_pow two_ne_zero (Fact.out : q.Prime).one_lt).ne' h1.symm
  have hNlt : N < ⊤ := normalizer_lt_top_of_le_of_ne_bot hG h.mem_maximal hBM hBne
  have hNsolv : Group.IsSolvable ↥N := hG.isSolvable_of_lt_top N hNlt
  have hBN : B ≤ N := Subgroup.le_normalizer
  have hNnontriv : Nontrivial ↥N := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot
    exact hBne (le_bot_iff.mp (hbot ▸ hBN))
  have hodd : Odd (Nat.card ↥N) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card N)
  -- `B ≤ F(N)`.
  have hBnormal : (B.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBN).mpr le_rfl
  have hB_le_FN : B ≤ Ch2.S08.fittingInG N :=
    Ch2.S08.le_fittingInG_of_normal_isPiSubgroup_singleton hBN hBnormal
      (Subgroup.isPiSubgroup_of_isPGroup_of_mem hB.1.isPGroup rfl)
  set FN : Subgroup G := Ch2.S08.fittingInG N with hFNdef
  have hFNnilp : Group.IsNilpotent ↥FN := Ch2.S08.fittingInG_isNilpotent N
  have hFN_le_N : FN ≤ N := Ch2.S08.fittingInG_le N
  -- `F(N) ≤ C_G(B)` via the `O_q × O_q'` decomposition.
  have hFN_le_C : FN ≤ Subgroup.centralizer (B : Set G) := by
    set O1 : Subgroup ↥FN := Ch03.oPiCore ({q} : Set ℕ) ↥FN with hO1def
    set O2 : Subgroup ↥FN := Ch03.oPiCore (({q} : Set ℕ))ᶜ ↥FN with hO2def
    have hBFN : B ≤ FN := hB_le_FN
    have hB_FN_normal : (B.subgroupOf FN).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hBFN).mpr (hFN_le_N.trans le_rfl)
    have hB_pi : Ch03.Subgroup.IsPiGroup ({q} : Set ℕ) (B.subgroupOf FN) := by
      intro r hr
      have h1 : Nat.card ↥(B.subgroupOf FN) = q ^ 2 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBFN).toEquiv]
        exact hB.2
      rw [h1] at hr
      have h2 := Nat.prime_of_mem_primeFactors hr
      have h3 := (Nat.dvd_of_mem_primeFactors hr)
      exact (Nat.prime_dvd_prime_iff_eq h2 Fact.out).mp (h2.dvd_of_dvd_pow h3)
    have hB_le_O1 : B.subgroupOf FN ≤ O1 := hB_pi.le_oPiCore
    -- `O_q`-part: abelian `q`-group containing `B`.
    have hO1_le_C : O1.map FN.subtype ≤ Subgroup.centralizer (B : Set G) := by
      have hO1pi : ∀ r ∈ (Nat.card ↥(O1.map FN.subtype)).primeFactors, r = q := by
        intro r hr
        rw [Subgroup.card_map_of_injective FN.subtype_injective] at hr
        have h1 := S10.oPiCore_isHall_of_isNilpotent (K := ↥FN) ({q} : Set ℕ) |>.1 r hr
        simpa using h1
      have hO1q : IsPGroup q ↥(O1.map FN.subtype) :=
        IsPGroup.of_card (eq_pow_factorization_of_forall_eq Nat.card_pos.ne' hO1pi)
      have hab := hallab _ hO1q
      refine le_centralizer_of_le_of_le hab le_rfl ?_
      calc B = (B.subgroupOf FN).map FN.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hBFN).symm
        _ ≤ O1.map FN.subtype := Subgroup.map_mono hB_le_O1
    -- `O_q'`-part: commutes with `B` by coprimality.
    have hO2_le_C : O2.map FN.subtype ≤ Subgroup.centralizer (B : Set G) := by
      have hcomm : ⁅O2, B.subgroupOf FN⁆ = ⊥ := by
        rw [← le_bot_iff]
        calc ⁅O2, B.subgroupOf FN⁆
            ≤ O2 ⊓ B.subgroupOf FN := by
              have : O2.Normal := Ch03.oPiCore.normal _ _
              exact le_inf (Subgroup.commutator_le_left _ _)
                (Subgroup.commutator_le_right _ _)
          _ ≤ ⊥ := by
              refine le_of_eq (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
              refine coprime_of_forall_prime_not_dvd ?_
              intro r hr h1 h2
              have hr2 : r ∈ ({q} : Set ℕ) := hB_pi r
                (Nat.mem_primeFactors.mpr ⟨hr, h2, Nat.card_pos.ne'⟩)
              have hr1 : r ∈ (({q} : Set ℕ))ᶜ :=
                S10.oPiCore_isHall_of_isNilpotent (K := ↥FN) (({q} : Set ℕ))ᶜ |>.1 r
                  (Nat.mem_primeFactors.mpr ⟨hr, h1, Nat.card_pos.ne'⟩)
              exact hr1 hr2
      have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      intro x hx
      obtain ⟨x', hx', rfl⟩ := hx
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hb' : (⟨b, hBFN hb⟩ : ↥FN) ∈ B.subgroupOf FN := Subgroup.mem_subgroupOf.mpr hb
      have := Subgroup.mem_centralizer_iff.mp (hle hx') _ hb'
      exact congrArg Subtype.val this
    -- combine via `O_q ⊔ O_q' = ⊤`.
    have htop := oPiCore_sup_compl_eq_top ↥FN ({q} : Set ℕ)
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥FN) ∈ O1 ⊔ O2 := by
      rw [hO1def, hO2def, htop]
      exact Subgroup.mem_top _
    have hmap : x ∈ (O1 ⊔ O2).map FN.subtype := ⟨⟨x, hx⟩, hx', rfl⟩
    rw [Subgroup.map_sup] at hmap
    exact (sup_le hO1_le_C hO2_le_C) hmap
  -- `F(N) ≤ E` and `F(N) ≤ F(E)`.
  have hFN_le_E : FN ≤ E := hFN_le_C.trans (centralizer_le_E_of_tau2 hG h hq hB hBE).1
  have hE_le_N : E ≤ N := (elemAb_normal_in_E_of_tau2 hG h hq hB hBE).1.1
  have hFN_le_FE : FN ≤ Ch2.S08.fittingInG E := by
    have h1 : (FN.subgroupOf E).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hFN_le_E).mpr ?_
      intro e he
      exact Ch2.S08.mem_normalizer_fittingInG_of_mem (hE_le_N he)
    have h3 : Group.IsNilpotent ↥(FN.subgroupOf E) :=
      Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hFN_le_E).symm
    calc FN = (FN.subgroupOf E).map E.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hFN_le_E).symm
      _ ≤ (Ch01.fitting ↥E).map E.subtype :=
          Subgroup.map_mono Ch01.nilpotent_normal_le_fitting
      _ = Ch2.S08.fittingInG E := rfl
  -- Theorem 4.20(a) on `↥N`: `N' ≤ F(N)`.
  have hrankFN : rank ↥(Ch01.fitting ↥N) ≤ 2 := by
    have h1 : rank ↥(Ch01.fitting ↥N) ≤ rank ↥FN :=
      rank_le_of_injective
        (f := (Subgroup.equivMapOfInjective (Ch01.fitting ↥N) N.subtype
          (Subgroup.subtype_injective N)).toMonoidHom)
        (Subgroup.equivMapOfInjective _ _ _).injective
    refine h1.trans ?_
    refine le_trans (rank_le_of_injective (Subgroup.inclusion_injective hFN_le_E)) ?_
    exact h.rank_le_two hG
  have hderived : commutator ↥N ≤ Ch01.fitting ↥N :=
    Ch1.S05.derived_le_fitting_of_rank_fitting_le_two hodd hrankFN
  refine ⟨?_, hFN_le_C, hFN_le_FE⟩
  calc derivedInG N = (commutator ↥N).map N.subtype := rfl
    _ ≤ (Ch01.fitting ↥N).map N.subtype := Subgroup.map_mono hderived
    _ = FN := rfl
    _ ≤ Ch2.S08.fittingInG E := hFN_le_FE

/-- Any `q`-subgroup of `F(E)` lies in `O_q(F(E))` (the unique Sylow `q`-subgroup of the
nilpotent `F(E)`). -/
theorem pGroup_le_opiCoreInG_fittingInG [Finite G]
    {E : Subgroup G} {q : ℕ} [Fact q.Prime]
    {T : Subgroup G} (hT : IsPGroup q ↥T) (hTF : T ≤ Ch2.S08.fittingInG E) :
    T ≤ opiCoreInG ({q} : Set ℕ) (Ch2.S08.fittingInG E) := by
  classical
  set FE : Subgroup G := Ch2.S08.fittingInG E with hFEdef
  have : Group.IsNilpotent ↥FE := Ch2.S08.fittingInG_isNilpotent E
  have hHall := S10.oPiCore_isHall_of_isNilpotent (K := ↥FE) ({q} : Set ℕ)
  have hTpi : Ch03.Subgroup.IsPiGroup ({q} : Set ℕ) (T.subgroupOf FE) := by
    intro r hr
    obtain ⟨k, hk⟩ := hT.exists_card_eq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTF).toEquiv, hk] at hr
    have h2 := Nat.prime_of_mem_primeFactors hr
    have h3 := Nat.dvd_of_mem_primeFactors hr
    have : r = q := (Nat.prime_dvd_prime_iff_eq h2 Fact.out).mp (h2.dvd_of_dvd_pow h3)
    simpa using this
  have h1 : T.subgroupOf FE ≤ Ch03.oPiCore ({q} : Set ℕ) ↥FE :=
    S10.isPiGroup_le_of_normal_isHallSubgroup hHall hTpi
  calc T = (T.subgroupOf FE).map FE.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hTF).symm
    _ ≤ (Ch03.oPiCore ({q} : Set ℕ) ↥FE).map FE.subtype := Subgroup.map_mono h1
    _ = opiCoreInG ({q} : Set ℕ) FE := rfl

/-- **Lemma 12.8, per-prime Sylow structure**: for `q ∈ τ₂(M)`, `B ∈ ℰ_q²(E)`, and a
Sylow `q`-subgroup `Sq` of `G` containing `B` with `Sq ≤ E` (all `q`-subgroups of `G`
assumed abelian), `Sq` is the `q`-core of `F(E)`; consequently `E ≤ N_G(Sq)` and
`F(E) ≤ C_G(Sq)`. -/
theorem sylow_eq_opiCore_fittingInG_of_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {q : ℕ} [Fact q.Prime] (hq : q ∈ tau2 M)
    {B : Subgroup G} (hB : B ∈ elemAbelianOfRank G q 2) (hBE : B ≤ E)
    {Sq : Sylow q G} (hBSq : B ≤ (Sq : Subgroup G)) (hSqE : (Sq : Subgroup G) ≤ E)
    (hallab : ∀ T : Subgroup G, IsPGroup q ↥T → IsMulCommutative ↥T) :
    (Sq : Subgroup G) = opiCoreInG ({q} : Set ℕ) (Ch2.S08.fittingInG E) ∧
    E ≤ Subgroup.normalizer ((Sq : Subgroup G) : Set G) ∧
    Ch2.S08.fittingInG E ≤ Subgroup.centralizer ((Sq : Subgroup G) : Set G) := by
  classical
  set FE : Subgroup G := Ch2.S08.fittingInG E with hFEdef
  have : Group.IsNilpotent ↥FE := Ch2.S08.fittingInG_isNilpotent E
  have hSqM : (Sq : Subgroup G) ≤ M := hSqE.trans h.E_le
  -- `Sq ≤ F(E)` via Corollary 10.7(a) and the Fitting chain through `N_G(B)`.
  have hSq_le_FE : (Sq : Subgroup G) ≤ FE := by
    have hN := normalizer_sylow_le_normalizer_elemAb hG h hq hB hBE hBSq hSqM
    exact (sylow_le_derivedInG_normalizer hG Sq).trans
      ((derivedInG_le_derivedInG hN.1).trans
        (derivedInG_normalizer_elemAb_le_fittingInG hG h hq hB hBE hallab).1)
  -- `Sq = O_q(F(E))` (both are `q`-subgroups of full order in `F(E)`).
  have hSq_le_O : (Sq : Subgroup G) ≤ opiCoreInG ({q} : Set ℕ) FE :=
    pGroup_le_opiCoreInG_fittingInG Sq.isPGroup' hSq_le_FE
  have hO_card : Nat.card ↥(opiCoreInG ({q} : Set ℕ) FE) ∣ Nat.card ↥(Sq : Subgroup G) := by
    rw [Sq.card_eq_multiplicity]
    have hpi : ∀ r ∈ (Nat.card ↥(opiCoreInG ({q} : Set ℕ) FE)).primeFactors, r = q := by
      intro r hr
      have hcardeq : Nat.card ↥(opiCoreInG ({q} : Set ℕ) FE)
          = Nat.card ↥(Ch03.oPiCore ({q} : Set ℕ) ↥FE) :=
        Subgroup.card_map_of_injective FE.subtype_injective
      rw [hcardeq] at hr
      have h1 := S10.oPiCore_isHall_of_isNilpotent (K := ↥FE) ({q} : Set ℕ) |>.1 r hr
      simpa using h1
    rw [eq_pow_factorization_of_forall_eq Nat.card_pos.ne' hpi]
    refine Nat.pow_dvd_pow q ?_
    rw [← Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne',
      ← eq_pow_factorization_of_forall_eq Nat.card_pos.ne' hpi]
    exact Subgroup.card_subgroup_dvd_card _
  have hSq_eq_O : (Sq : Subgroup G) = opiCoreInG ({q} : Set ℕ) FE :=
    Subgroup.eq_of_le_of_card_ge hSq_le_O (Nat.le_of_dvd Nat.card_pos hO_card)
  -- `E` normalizes `Sq` (it normalizes `F(E)` and its characteristic `q`-core).
  have hE_norm_FE : E ≤ Subgroup.normalizer ((FE : Subgroup G) : Set G) := fun e he =>
    Ch2.S08.mem_normalizer_fittingInG_of_mem he
  have hE_norm_Sq : E ≤ Subgroup.normalizer ((Sq : Subgroup G) : Set G) := by
    rw [hSq_eq_O]
    exact le_normalizer_opiCoreInG_of_le_normalizer _ hE_norm_FE
  -- `F(E) ≤ C_G(Sq)` via the `O_q × O_q'` decomposition.
  refine ⟨hSq_eq_O, hE_norm_Sq, ?_⟩
  set O1 : Subgroup ↥FE := Ch03.oPiCore ({q} : Set ℕ) ↥FE with hO1def
  set O2 : Subgroup ↥FE := Ch03.oPiCore (({q} : Set ℕ))ᶜ ↥FE with hO2def
  have hO1_le_C : O1.map FE.subtype ≤ Subgroup.centralizer ((Sq : Subgroup G) : Set G) := by
    have hO1_eq : O1.map FE.subtype = (Sq : Subgroup G) := hSq_eq_O.symm
    rw [hO1_eq]
    exact le_centralizer_of_le_of_le (hallab _ Sq.isPGroup') le_rfl le_rfl
  have hO2_le_C : O2.map FE.subtype ≤ Subgroup.centralizer ((Sq : Subgroup G) : Set G) := by
    have hcomm : ⁅O2, O1⁆ = ⊥ := by
      rw [← le_bot_iff]
      calc ⁅O2, O1⁆ ≤ O2 ⊓ O1 := by
            have : O2.Normal := Ch03.oPiCore.normal _ _
            have : O1.Normal := Ch03.oPiCore.normal _ _
            exact le_inf (Subgroup.commutator_le_left _ _)
              (Subgroup.commutator_le_right _ _)
        _ ≤ ⊥ := by
            refine le_of_eq (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
            refine coprime_of_forall_prime_not_dvd ?_
            intro r hr h1 h2
            have hr1 : r ∈ (({q} : Set ℕ))ᶜ :=
              S10.oPiCore_isHall_of_isNilpotent (K := ↥FE) (({q} : Set ℕ))ᶜ |>.1 r
                (Nat.mem_primeFactors.mpr ⟨hr, h1, Nat.card_pos.ne'⟩)
            have hr2 : r ∈ ({q} : Set ℕ) :=
              S10.oPiCore_isHall_of_isNilpotent (K := ↥FE) ({q} : Set ℕ) |>.1 r
                (Nat.mem_primeFactors.mpr ⟨hr, h2, Nat.card_pos.ne'⟩)
            exact hr1 hr2
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    intro x hx
    obtain ⟨x', hx', rfl⟩ := hx
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbFE : b ∈ FE := hSq_le_FE hb
    have hb' : (⟨b, hbFE⟩ : ↥FE) ∈ O1 := by
      have h0 : b ∈ opiCoreInG ({q} : Set ℕ) FE := hSq_eq_O ▸ hb
      have h1 : b ∈ O1.map FE.subtype := h0
      obtain ⟨b', hb', hbeq⟩ := h1
      have h2 : b' = (⟨b, hbFE⟩ : ↥FE) := Subtype.ext hbeq
      exact h2 ▸ hb'
    have h2 := Subgroup.mem_centralizer_iff.mp (hle hx') _ hb'
    exact congrArg Subtype.val h2
  have htop := oPiCore_sup_compl_eq_top ↥FE ({q} : Set ℕ)
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥FE) ∈ O1 ⊔ O2 := by
    rw [hO1def, hO2def, htop]
    exact Subgroup.mem_top _
  have hmap : x ∈ (O1 ⊔ O2).map FE.subtype := ⟨⟨x, hx⟩, hx', rfl⟩
  rw [Subgroup.map_sup] at hmap
  exact (sup_le hO1_le_C hO2_le_C) hmap

/-- A `π`-subgroup of `F(E)` lies in `O_π(F(E))` (general-`π` version of
`pGroup_le_opiCoreInG_fittingInG`). -/
theorem piGroup_le_opiCoreInG_fittingInG [Finite G]
    {E : Subgroup G} {π : Set ℕ}
    {T : Subgroup G} (hT : ∀ r ∈ (Nat.card ↥T).primeFactors, r ∈ π)
    (hTF : T ≤ Ch2.S08.fittingInG E) :
    T ≤ opiCoreInG π (Ch2.S08.fittingInG E) := by
  classical
  set FE : Subgroup G := Ch2.S08.fittingInG E with hFEdef
  have : Group.IsNilpotent ↥FE := Ch2.S08.fittingInG_isNilpotent E
  have hHall := S10.oPiCore_isHall_of_isNilpotent (K := ↥FE) π
  have hTpi : Ch03.Subgroup.IsPiGroup π (T.subgroupOf FE) := by
    intro r hr
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTF).toEquiv] at hr
    exact hT r hr
  have h1 : T.subgroupOf FE ≤ Ch03.oPiCore π ↥FE :=
    S10.isPiGroup_le_of_normal_isHallSubgroup hHall hTpi
  calc T = (T.subgroupOf FE).map FE.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hTF).symm
    _ ≤ (Ch03.oPiCore π ↥FE).map FE.subtype := Subgroup.map_mono h1
    _ = opiCoreInG π FE := rfl

/-- A subgroup contained in its own centralizer is abelian. -/
theorem isMulCommutative_of_le_centralizer {H : Subgroup G}
    (hH : H ≤ Subgroup.centralizer (H : Set G)) : IsMulCommutative ↥H := by
  constructor
  constructor
  intro a b
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hH b.2) a a.2)

/-- **BG Lemma 12.8(a)(b)** (mmd L3254-3255): with `S` an abelian Sylow `p`-subgroup
of `G` containing `A`, the Hall `τ₂(M)`-subgroup `E₂` equals `O_{τ₂}(F(E))`; it is
an abelian normal subgroup of `E` and a Hall `τ₂(M)`-subgroup of `G`. -/
theorem E2_abelian_normal_hall_of_abelianSylow [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {S : Sylow p G} (hSab : IsMulCommutative ↥(S : Subgroup G)) :
    (IsMulCommutative ↥E₂ ∧ E ≤ Subgroup.normalizer ((E₂ : Subgroup G) : Set G)) ∧
    Ch03.IsHallSubgroup (tau2 M) E₂ ∧
    E₂ = opiCoreInG (tau2 M) (Ch2.S08.fittingInG E) := by
  classical
  set FE : Subgroup G := Ch2.S08.fittingInG E with hFEdef
  have : Group.IsNilpotent ↥FE := Ch2.S08.fittingInG_isNilpotent E
  set W : Subgroup G := opiCoreInG (tau2 M) FE with hWdef
  have hW_le_FE : W ≤ FE := Subgroup.map_subtype_le _
  have hW_le_E : W ≤ E := hW_le_FE.trans (Ch2.S08.fittingInG_le E)
  -- prime factors of `|W|` lie in `τ₂`.
  have hW_pi : ∀ r ∈ (Nat.card ↥W).primeFactors, r ∈ tau2 M := by
    intro r hr
    have hcardeq : Nat.card ↥W = Nat.card ↥(Ch03.oPiCore (tau2 M) ↥FE) :=
      Subgroup.card_map_of_injective FE.subtype_injective
    rw [hcardeq] at hr
    exact S10.oPiCore_isHall_of_isNilpotent (K := ↥FE) (tau2 M) |>.1 r hr
  -- each `τ₂`-prime `r` contributes its full `G`-Sylow to `W`.
  have hSr_le_W : ∀ (r : ℕ), Fact r.Prime → r ∈ tau2 M →
      ∃ Sr : Sylow r G, (Sr : Subgroup G) ≤ W := by
    intro r hrfact hr
    have := hrfact
    obtain ⟨B, hB, hBE, Sr, hBSr, hSrE⟩ :=
      exists_sylow_le_E_of_tau2 hG h hp hA hAE hSab hr
    have hallab : ∀ T : Subgroup G, IsPGroup r ↥T → IsMulCommutative ↥T := by
      intro T hT
      obtain ⟨ST, hTST⟩ := hT.exists_le_sylow
      exact isMulCommutative_of_le
        (sylow_isMulCommutative_of_tau2_of_abelian hG h hp hA hAE hSab hr ST) hTST
    obtain ⟨hSr_eq, _, _⟩ :=
      sylow_eq_opiCore_fittingInG_of_tau2 hG h hr hB hBE hBSr hSrE hallab
    refine ⟨Sr, ?_⟩
    refine piGroup_le_opiCoreInG_fittingInG ?_ ?_
    · intro s hs
      rw [Sr.card_eq_multiplicity] at hs
      have h1 := Nat.prime_of_mem_primeFactors hs
      have h2 := Nat.dvd_of_mem_primeFactors hs
      have : s = r := (Nat.prime_dvd_prime_iff_eq h1 Fact.out).mp (h1.dvd_of_dvd_pow h2)
      rwa [this]
    · rw [hSr_eq]
      exact Subgroup.map_subtype_le _
  -- `ν_r(W) = ν_r(E)` for every `τ₂`-prime `r`.
  have hW_full : ∀ (r : ℕ), r.Prime → r ∈ tau2 M →
      (Nat.card ↥W).factorization r = (Nat.card ↥E).factorization r := by
    intro r hr hr2
    have : Fact r.Prime := ⟨hr⟩
    refine le_antisymm ?_ ?_
    · exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
        (Subgroup.card_dvd_of_le hW_le_E) r
    · obtain ⟨Sr, hSrW⟩ := hSr_le_W r ⟨hr⟩ hr2
      rw [factorization_card_E_eq_of_tau2 hG h hp hA hAE hSab hr2,
        ← Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne',
        ← Sr.card_eq_multiplicity]
      exact Subgroup.card_dvd_of_le hSrW
  -- `E` normalizes `W`.
  have hE_norm_W : E ≤ Subgroup.normalizer ((W : Subgroup G) : Set G) :=
    le_normalizer_opiCoreInG_of_le_normalizer _
      (fun e he => Ch2.S08.mem_normalizer_fittingInG_of_mem he)
  -- `W.subgroupOf E` is a normal Hall `τ₂`-subgroup of `E`, so `E₂ ≤ W`.
  have hW_hall_E : Ch03.IsHallSubgroup (tau2 M) (W.subgroupOf E) := by
    constructor
    · intro r hr
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW_le_E).toEquiv] at hr
      exact hW_pi r hr
    · intro r hr hr2
      exfalso
      have hr_prime := Nat.prime_of_mem_primeFactors hr
      have hsum : (Nat.card ↥(W.subgroupOf E)).factorization r
          + ((W.subgroupOf E).index).factorization r
          = (Nat.card ↥E).factorization r := by
        rw [← Subgroup.card_mul_index (W.subgroupOf E),
          Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
          Finsupp.add_apply]
      have hcard : (Nat.card ↥(W.subgroupOf E)).factorization r
          = (Nat.card ↥E).factorization r := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW_le_E).toEquiv]
        exact hW_full r hr_prime hr2
      have hpos : 0 < ((W.subgroupOf E).index).factorization r :=
        Nat.Prime.factorization_pos_of_dvd hr_prime Subgroup.index_ne_zero_of_finite
          (Nat.dvd_of_mem_primeFactors hr)
      omega
  have hW_normal : (W.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hW_le_E).mpr hE_norm_W
  have hE₂_le_W : E₂ ≤ W := by
    have hE₂pi : Ch03.Subgroup.IsPiGroup (tau2 M) (E₂.subgroupOf E) := by
      intro r hr
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv] at hr
      exact h.isPiGroup_tau2 r hr
    have h1 : E₂.subgroupOf E ≤ W.subgroupOf E :=
      S10.isPiGroup_le_of_normal_isHallSubgroup hW_hall_E hE₂pi
    calc E₂ = (E₂.subgroupOf E).map E.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le h.E₂_le).symm
      _ ≤ (W.subgroupOf E).map E.subtype := Subgroup.map_mono h1
      _ = W := Subgroup.map_subgroupOf_eq_of_le hW_le_E
  -- `|W| ∣ |E₂|`, hence `E₂ = W`.
  have hW_dvd : Nat.card ↥W ∣ Nat.card ↥E₂ := by
    rw [← Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne']
    intro r
    by_cases hr_prime : r.Prime
    case neg =>
      rw [Nat.factorization_eq_zero_of_not_prime _ hr_prime]
      exact Nat.zero_le _
    case pos =>
      by_cases hr2 : r ∈ tau2 M
      · -- `ν_r(W) = ν_r(E) = ν_r(E₂)` (`E₂` is Hall `τ₂` in `E`).
        rw [hW_full r hr_prime hr2]
        have hsum : (Nat.card ↥(E₂.subgroupOf E)).factorization r
            + ((E₂.subgroupOf E).index).factorization r
            = (Nat.card ↥E).factorization r := by
          rw [← Subgroup.card_mul_index (E₂.subgroupOf E),
            Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
            Finsupp.add_apply]
        have hidx : ((E₂.subgroupOf E).index).factorization r = 0 := by
          apply Nat.factorization_eq_zero_of_not_dvd
          intro hdvd
          exact h.E₂_hall.2 r (Nat.mem_primeFactors.mpr
            ⟨hr_prime, hdvd, Subgroup.index_ne_zero_of_finite⟩) hr2
        have hcard : (Nat.card ↥(E₂.subgroupOf E)).factorization r
            = (Nat.card ↥E₂).factorization r := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv]
        omega
      · -- `r ∉ τ₂` cannot divide `|W|`.
        have : ¬ r ∣ Nat.card ↥W := by
          intro hdvd
          exact hr2 (hW_pi r (Nat.mem_primeFactors.mpr ⟨hr_prime, hdvd, Nat.card_pos.ne'⟩))
        rw [Nat.factorization_eq_zero_of_not_dvd this]
        exact Nat.zero_le _
  have hE₂_eq_W : E₂ = W :=
    Subgroup.eq_of_le_of_card_ge hE₂_le_W (Nat.le_of_dvd Nat.card_pos hW_dvd)
  -- normality in `E`.
  have hE_norm_E₂ : E ≤ Subgroup.normalizer ((E₂ : Subgroup G) : Set G) := by
    rw [hE₂_eq_W]
    exact hE_norm_W
  -- abelian: each Sylow `r`-subgroup of `E₂` equals `O_r(F(E))`, which `F(E) ⊇ E₂`
  -- centralizes.
  have hE₂_le_FE : E₂ ≤ FE := hE₂_eq_W ▸ hW_le_FE
  have hE₂nilp : Group.IsNilpotent ↥E₂ :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hE₂_le_FE)
  have hE₂_le_C : E₂ ≤ Subgroup.centralizer ((E₂ : Subgroup G) : Set G) := by
    refine Ch2.S08.le_of_sylow_le_of_nilpotent hE₂nilp ?_
    intro r
    have : Fact (r : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors r.2⟩
    set R : Subgroup G := ((default : Sylow (r : ℕ) ↥E₂) : Subgroup ↥E₂).map E₂.subtype
      with hRdef
    change R ≤ Subgroup.centralizer ((E₂ : Subgroup G) : Set G)
    have hr2 : (r : ℕ) ∈ tau2 M := by
      have h1 : (r : ℕ) ∈ (Nat.card ↥(E₂.subgroupOf E)).primeFactors := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv]
        exact r.2
      exact h.E₂_hall.1 _ h1
    obtain ⟨B, hB, hBE, Sr, hBSr, hSrE⟩ :=
      exists_sylow_le_E_of_tau2 hG h hp hA hAE hSab hr2
    have hallab : ∀ T : Subgroup G, IsPGroup (r : ℕ) ↥T → IsMulCommutative ↥T := by
      intro T hT
      obtain ⟨ST, hTST⟩ := hT.exists_le_sylow
      exact isMulCommutative_of_le
        (sylow_isMulCommutative_of_tau2_of_abelian hG h hp hA hAE hSab hr2 ST) hTST
    obtain ⟨hSr_eq, _, hFE_le_CSr⟩ :=
      sylow_eq_opiCore_fittingInG_of_tau2 hG h hr2 hB hBE hBSr hSrE hallab
    have hR_le_Sr : R ≤ (Sr : Subgroup G) := by
      rw [hSr_eq]
      refine pGroup_le_opiCoreInG_fittingInG ?_ ?_
      · exact ((default : Sylow (r : ℕ) ↥E₂).isPGroup'.map E₂.subtype)
      · exact (Subgroup.map_subtype_le _).trans hE₂_le_FE
    have hE₂_le_CR : E₂ ≤ Subgroup.centralizer (R : Set G) :=
      (hE₂_le_FE.trans hFE_le_CSr).trans
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hR_le_Sr))
    exact le_centralizer_swap hE₂_le_CR
  -- Hall in `G`.
  have hHallG : Ch03.IsHallSubgroup (tau2 M) E₂ := by
    constructor
    · intro r hr
      have h1 : r ∈ (Nat.card ↥(E₂.subgroupOf E)).primeFactors := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv]
        exact hr
      exact h.E₂_hall.1 r h1
    · intro r hr hr2
      exfalso
      have hr_prime := Nat.prime_of_mem_primeFactors hr
      have : Fact r.Prime := ⟨hr_prime⟩
      -- `ν_r(E₂) = ν_r(E) = ν_r(G)`, so `r` cannot divide the index.
      have hsum : (Nat.card ↥E₂).factorization r + (E₂.index).factorization r
          = (Nat.card G).factorization r := by
        rw [← Subgroup.card_mul_index E₂,
          Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
          Finsupp.add_apply]
      have hcard : (Nat.card ↥E₂).factorization r = (Nat.card G).factorization r := by
        have h1 : (Nat.card ↥E₂).factorization r = (Nat.card ↥E).factorization r := by
          have h2 : (Nat.card ↥(E₂.subgroupOf E)).factorization r
              + ((E₂.subgroupOf E).index).factorization r
              = (Nat.card ↥E).factorization r := by
            rw [← Subgroup.card_mul_index (E₂.subgroupOf E),
              Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
              Finsupp.add_apply]
          have h3 : ((E₂.subgroupOf E).index).factorization r = 0 := by
            apply Nat.factorization_eq_zero_of_not_dvd
            intro hdvd
            exact h.E₂_hall.2 r (Nat.mem_primeFactors.mpr
              ⟨hr_prime, hdvd, Subgroup.index_ne_zero_of_finite⟩) hr2
          have h4 : (Nat.card ↥(E₂.subgroupOf E)).factorization r
              = (Nat.card ↥E₂).factorization r := by
            rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv]
          omega
        rw [h1]
        exact factorization_card_E_eq_of_tau2 hG h hp hA hAE hSab hr2
      have hpos : 0 < (E₂.index).factorization r :=
        Nat.Prime.factorization_pos_of_dvd hr_prime Subgroup.index_ne_zero_of_finite
          (Nat.dvd_of_mem_primeFactors hr)
      omega
  exact ⟨⟨isMulCommutative_of_le_centralizer hE₂_le_C, hE_norm_E₂⟩, hHallG, hE₂_eq_W⟩

/-- **BG Lemma 12.8(c)** (mmd L3256): with `S` an abelian Sylow `p`-subgroup of `G`
containing `A`: `S ⊆ N_G(S)' ⊆ F(E) ⊆ C_G(S) ⊆ E`. -/
theorem sylow_chain_of_abelianSylow [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {S : Sylow p G} (hAS : A ≤ (S : Subgroup G))
    (hSab : IsMulCommutative ↥(S : Subgroup G)) :
    (S : Subgroup G) ≤ derivedInG (Subgroup.normalizer ((S : Subgroup G) : Set G)) ∧
    derivedInG (Subgroup.normalizer ((S : Subgroup G) : Set G)) ≤ Ch2.S08.fittingInG E ∧
    Ch2.S08.fittingInG E ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) ∧
    Subgroup.centralizer ((S : Subgroup G) : Set G) ≤ E := by
  have hSE : (S : Subgroup G) ≤ E :=
    (le_centralizer_of_le_of_le hSab le_rfl hAS).trans
      (centralizer_le_E_of_tau2 hG h hp hA hAE).1
  have hSM : (S : Subgroup G) ≤ M := hSE.trans h.E_le
  have hallab : ∀ T : Subgroup G, IsPGroup p ↥T → IsMulCommutative ↥T := by
    intro T hT
    obtain ⟨ST, hTST⟩ := hT.exists_le_sylow
    exact isMulCommutative_of_le
      (sylow_isMulCommutative_of_tau2_of_abelian hG h hp hA hAE hSab hp ST) hTST
  obtain ⟨_, _, hFE_le_C⟩ :=
    sylow_eq_opiCore_fittingInG_of_tau2 hG h hp hA hAE hAS hSE hallab
  refine ⟨sylow_le_derivedInG_normalizer hG S, ?_, hFE_le_C, ?_⟩
  · exact (derivedInG_le_derivedInG
      (normalizer_sylow_le_normalizer_elemAb hG h hp hA hAE hAS hSM).1).trans
      (derivedInG_normalizer_elemAb_le_fittingInG hG h hp hA hAE hallab).1
  · exact (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAS)).trans
      (centralizer_le_E_of_tau2 hG h hp hA hAE).1

end OddOrder.BG.Ch3.S12


