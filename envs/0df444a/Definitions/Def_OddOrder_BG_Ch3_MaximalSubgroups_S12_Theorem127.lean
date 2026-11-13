-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Theorem127
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S12_Theorem127
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:31:22.971404+00:00
-- url     : https://prove2.me/theorems/4470bd56-7e3f-47e1-b700-8ff3f597728e
-- title:
--   BG §12: Theorem 12.7, the nonabelian Sylow $p$-subgroup case
-- statement:
--   Formalizes Theorem 12.7 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §12 (parts a, b, c, e): for $p\in\tau_2(M)$, $A\in\mathcal{E}_p^2(E)$ and a nonabelian Sylow $p$-subgroup of $G$: (a) $\tau_2(M)=\{p\}$; (b) $A_0=C_A(M_\sigma)$ has order $p$ and $F(M)=M_\sigma\times A_0$; (c) for $X\in\mathcal{E}_p^1(E)-\{A_0\}$, $C_{M_\sigma}(X)=1$ and $C_G(X)\not\subseteq M$; (e) $\pi(C_{E_0}(x))\subseteq\tau_1(M)$. Part (d) is in the next file.
--
--   Main declarations: `exists_elemAb_rank_two_le_E_of_tau2`; `exists_canonical_line_of_nonabelianSylow`.
--
--   The bundle also proves 8 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S12_Theorem127.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S12_Theorem127.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Corollary126

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- `|M| = |M_σ| · |E|` for the §12 complement setup. -/
theorem card_Msigma_mul_card_E [Finite G]
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    Nat.card ↥(S10.Msigma M) * Nat.card ↥E = Nat.card ↥M := by
  have h1 := card_sup_eq_mul_of_le_normalizer_of_disjoint
    (A := E) (B := S10.Msigma M)
    (h.E_le.trans (le_normalizer_opiCoreInG _ _))
    (by rw [← h.E_compl_inf, inf_comm])
  rw [sup_comm, h.E_compl_sup] at h1
  rw [h1, Nat.mul_comm]

/-- For `p ∉ σ(M)`, the `p`-parts of `|M|` and `|E|` agree. -/
theorem factorization_card_eq_of_notMem_sigma [Finite G]
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} [Fact p.Prime] (hp : p ∉ S10.sigma M) :
    (Nat.card ↥M).factorization p = (Nat.card ↥E).factorization p := by
  have hcard := card_Msigma_mul_card_E h
  have hMσ : (Nat.card ↥(S10.Msigma M)).factorization p = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    exact hp (S10.Msigma_isPiGroup M p
      (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩))
  rw [← hcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
    Finsupp.add_apply, hMσ, Nat.zero_add]

/-- The image in `G` of a Sylow `p`-subgroup of `E` is `p`-maximal in `M` (`p ∉ σ(M)`). -/
theorem map_sylow_E_maximal_in_M [Finite G]
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} [Fact p.Prime] (hp : p ∉ S10.sigma M) (PE : Sylow p ↥E)
    {T : Subgroup G} (hPT : (PE : Subgroup ↥E).map E.subtype ≤ T) (hTM : T ≤ M)
    (hTp : IsPGroup p ↥T) :
    T = (PE : Subgroup ↥E).map E.subtype := by
  have hcardP : Nat.card ↥((PE : Subgroup ↥E).map E.subtype)
      = p ^ (Nat.card ↥M).factorization p := by
    rw [Subgroup.card_map_of_injective E.subtype_injective, PE.card_eq_multiplicity,
      factorization_card_eq_of_notMem_sigma h hp]
  obtain ⟨k, hk⟩ := hTp.exists_card_eq
  have hk_le : k ≤ (Nat.card ↥M).factorization p := by
    rw [← Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne', ← hk]
    exact Subgroup.card_dvd_of_le hTM
  refine (Subgroup.eq_of_le_of_card_ge hPT ?_).symm
  rw [hcardP, hk]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hk_le

set_option backward.isDefEq.respectTransparency false in
/-- For `q ∈ τ₂(M)` (q prime) there is a rank-two elementary abelian `q`-subgroup
inside `E`: realize one inside `M` from `r_q(M) = 2` and conjugate it into a Sylow
`q`-subgroup of `M` coming from `E`. -/
theorem exists_elemAb_rank_two_le_E_of_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {q : ℕ} [Fact q.Prime] (hq : q ∈ tau2 M) :
    ∃ B ∈ elemAbelianOfRank G q 2, B ≤ E := by
  classical
  have hr2 : pRank ↥M q = 2 := tau2_pRank_eq_two hq
  have hqσ : q ∉ S10.sigma M := tau2_subset_sigma_compl M hq
  -- a rank-two elementary abelian `q`-subgroup `B₁ ≤ M`.
  obtain ⟨B', hB'ea, hB'log⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank (G := ↥M) (p := q) (n := 2)
      (by norm_num) (by rw [hr2])
  have hB'nc : ¬ IsCyclic ↥B' :=
    not_isCyclic_of_isElementaryAbelian_of_two_le_log_card hB'ea hB'log
  have hq_odd : Odd q := by
    obtain ⟨j, hj⟩ := hB'ea.isPGroup.exists_card_eq
    have hj2 : 2 ≤ j := by
      rw [hj, Nat.log_pow (Fact.out : q.Prime).one_lt] at hB'log
      exact hB'log
    have hqdvd : q ∣ Nat.card ↥B' := by
      rw [hj]; exact dvd_pow_self q (by omega)
    exact hG.odd.of_dvd_nat
      ((hqdvd.trans (Subgroup.card_subgroup_dvd_card B')).trans
        (Subgroup.card_subgroup_dvd_card M))
  obtain ⟨B'', hB''ea, hB''card⟩ :=
    OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic
      hB'ea.isPGroup hq_odd hB'nc
  set B₁ : Subgroup G := (B''.map B'.subtype).map M.subtype with hB₁def
  have hB₁M : B₁ ≤ M := Subgroup.map_subtype_le _
  have hB₁mem : B₁ ∈ elemAbelianOfRank G q 2 := by
    refine ⟨?_, ?_⟩
    · exact Subgroup.IsElementaryAbelian.map M.subtype_injective
        (Subgroup.IsElementaryAbelian.map B'.subtype_injective hB''ea)
    · rw [hB₁def, Subgroup.card_map_of_injective M.subtype_injective,
        Subgroup.card_map_of_injective B'.subtype_injective, hB''card]
  -- a Sylow `q`-subgroup of `↥M` containing `B₁`, and one coming from `E`.
  have hB₁pg : IsPGroup q ↥B₁ := hB₁mem.1.isPGroup
  obtain ⟨TM, hB₁TM⟩ := hB₁pg.comap_subtype.exists_le_sylow (G := M)
  obtain ⟨TE⟩ := (inferInstance : Nonempty (Sylow q ↥E))
  set T : Subgroup G := (TE : Subgroup ↥E).map E.subtype with hTdef
  have hT_le_E : T ≤ E := Subgroup.map_subtype_le _
  have hT_le_M : T ≤ M := hT_le_E.trans h.E_le
  have hT_card : Nat.card ↥(T.subgroupOf M) = q ^ (Nat.card ↥M).factorization q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT_le_M).toEquiv, hTdef,
      Subgroup.card_map_of_injective E.subtype_injective, TE.card_eq_multiplicity,
      factorization_card_eq_of_notMem_sigma h hqσ]
  set TS : Sylow q ↥M := Sylow.ofCard (T.subgroupOf M) hT_card with hTSdef
  -- conjugate `TM` onto `TS` inside `↥M`.
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq ↥M TM TS
  refine ⟨MulAut.conj (m : G) • B₁, ⟨?_, ?_⟩, ?_⟩
  · rw [mulAut_smul_eq_map]
    exact Subgroup.IsElementaryAbelian.map (MulAut.conj (m : G)).injective hB₁mem.1
  · rw [mulAut_smul_eq_map, Subgroup.card_map_of_injective (MulAut.conj (m : G)).injective]
    exact hB₁mem.2
  · -- `conj m • B₁ ≤ conj m • TM-image = TS-image = T ≤ E`.
    have hB₁_le_TM : B₁ ≤ (TM : Subgroup ↥M).map M.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hB₁M]
      exact Subgroup.map_mono hB₁TM
    have hsmul_eq : MulAut.conj (m : G) • ((TM : Subgroup ↥M).map M.subtype) = T := by
      have h1 : ((m • TM : Sylow q ↥M) : Subgroup ↥M).map M.subtype = T := by
        rw [hm, hTSdef]
        change (T.subgroupOf M).map M.subtype = T
        exact Subgroup.map_subgroupOf_eq_of_le hT_le_M
      rw [← h1, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def,
        Subgroup.pointwise_smul_def, Subgroup.map_map, Subgroup.map_map]
      rfl
    calc MulAut.conj (m : G) • B₁
        ≤ MulAut.conj (m : G) • ((TM : Subgroup ↥M).map M.subtype) :=
          Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hB₁_le_TM
      _ = T := hsmul_eq
      _ ≤ E := hT_le_E

/-- **BG Theorem 12.7(a)** (mmd L3203, L3216-3218): if `G` has nonabelian Sylow
`p`-subgroups and `p ∈ τ₂(M)`, then `p` is the only **prime** in `τ₂(M)`.
For a second prime `q`, a rank-two `B ∈ ℰ_q²(E)` is normal in `E` alongside `A`
(Corollary 12.6(a)), so `A` centralizes `B`; both are maximal elementary abelian
(Lemma 12.1(g)), so Proposition 10.10(c) plants a full Sylow `p`-subgroup of `G`
inside `C_G(B) ≤ E` (Corollary 12.6(b)) — but then it would be an abelian Sylow
`p`-subgroup of `G` (Theorem 12.5(b)), contradicting the hypothesis. -/
theorem tau2_prime_eq_of_nonabelianSylow [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    (hnonab : ∃ S : Sylow p G, ¬ IsMulCommutative (S : Subgroup G))
    {q : ℕ} (hq_prime : q.Prime) (hq : q ∈ tau2 M) : q = p := by
  classical
  have : Fact q.Prime := ⟨hq_prime⟩
  by_contra hqp
  have hAM : A ≤ M := hAE.trans h.E_le
  -- `B ∈ ℰ_q²(E)`, normal in `E` together with `A`, hence centralized by `A`.
  obtain ⟨B, hB, hBE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG h hq
  have hBM : B ≤ M := hBE.trans h.E_le
  have hAnorm : E ≤ Subgroup.normalizer (A : Set G) :=
    E_le_normalizer_of_tau2 hG h hp hA hAE
  have hBnorm : E ≤ Subgroup.normalizer (B : Set G) :=
    E_le_normalizer_of_tau2 hG h hq hB hBE
  have hAB_bot : A ⊓ B = ⊥ := by
    rw [← Subgroup.card_eq_one]
    have h1 : Nat.card ↥(A ⊓ B : Subgroup G) ∣ p ^ 2 := by
      rw [← hA.2]; exact Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(A ⊓ B : Subgroup G) ∣ q ^ 2 := by
      rw [← hB.2]; exact Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨i, hi2, hicard⟩ := (Nat.dvd_prime_pow Fact.out).mp h1
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rwa [pow_zero] at hicard
    · exfalso
      have hpdvd : p ∣ Nat.card ↥(A ⊓ B : Subgroup G) := by
        rw [hicard]; exact dvd_pow_self p hipos.ne'
      have := (Nat.prime_dvd_prime_iff_eq Fact.out hq_prime).mp
        ((Fact.out : p.Prime).dvd_of_dvd_pow (hpdvd.trans h2))
      exact hqp this.symm
  have hAcentB : A ≤ Subgroup.centralizer (B : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, ← le_bot_iff, ← hAB_bot]
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : b * a⁻¹ * b⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp (hAnorm (hBE hb)) a⁻¹).mp (A.inv_mem ha)
      have h2 : a * (b * a⁻¹ * b⁻¹) ∈ A := A.mul_mem ha h1
      rw [commutatorElement_def]
      simpa [mul_assoc] using h2
    · have h1 : a * b * a⁻¹ ∈ B :=
        (Subgroup.mem_normalizer_iff.mp (hBnorm (hAE ha)) b).mp hb
      have h2 : a * b * a⁻¹ * b⁻¹ ∈ B := B.mul_mem h1 (B.inv_mem hb)
      rwa [commutatorElement_def]
  -- extend `B` to a maximal `A`-invariant `q`-subgroup `Qs` of `G`.
  have hB_inv : B ∈ hInvariant ⊤ A {q} := by
    refine ⟨le_top, hAcentB.trans (Subgroup.centralizer_le_normalizer _), ?_⟩
    exact Subgroup.isPiSubgroup_of_isPGroup_of_mem hB.1.isPGroup rfl
  obtain ⟨Qs, hQs, hBQs⟩ := exists_le_hInvariantStar hB_inv
  -- `q ∈ π(C_G(A))` and `A` is maximal elementary abelian (Lemma 12.1(g)).
  have hBC : B ≤ Subgroup.centralizer (A : Set G) := le_centralizer_swap hAcentB
  have hqc : q ∈ (Nat.card ↥(Subgroup.centralizer (A : Set G))).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨hq_prime, ?_, Nat.card_pos.ne'⟩
    have h1 : (q : ℕ) ∣ Nat.card ↥B := by
      rw [hB.2]; exact dvd_pow_self q two_ne_zero
    exact h1.trans (Subgroup.card_dvd_of_le hBC)
  have hAmax : IsMaximalElementaryAbelian p A :=
    (isMaximalElementaryAbelian_of_mem_tau2 hG h.mem_maximal Fact.out hp hAM hA).1
  have hBmax : IsMaximalElementaryAbelian q B :=
    (isMaximalElementaryAbelian_of_mem_tau2 hG h.mem_maximal hq_prime hq hBM hB).1
  -- Proposition 10.10(c): a full Sylow `p`-subgroup of `G` centralizes `Qs`.
  obtain ⟨P', hAP', -, -, hPcent⟩ :=
    S10.normalizer_factorization hG (Ne.symm hqp) hA hAmax hQs hqc
  have hP'C : (P' : Subgroup G) ≤ Subgroup.centralizer (B : Set G) := by
    refine le_trans (hPcent (Or.inr ?_)) (Subgroup.centralizer_le
      (SetLike.coe_subset_coe.mpr hBQs))
    -- `B.subgroupOf Qs` is maximal elementary abelian of order `q²` inside `↥Qs`.
    refine ⟨B.subgroupOf Qs, ?_, ?_, ?_⟩
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBQs).toEquiv]
      exact hB.2
    · exact OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hBQs).symm hB.1
    · intro F' hF' hBF'
      have hFle : F'.map Qs.subtype ≤ Qs := Subgroup.map_subtype_le _
      have hBF : B ≤ F'.map Qs.subtype := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hBQs]
        exact Subgroup.map_mono hBF'
      have hFea : (F'.map Qs.subtype).IsElementaryAbelian q :=
        Subgroup.IsElementaryAbelian.map Qs.subtype_injective hF'
      have hFeq : F'.map Qs.subtype = B := hBmax.2 _ hFea hBF
      apply Subgroup.map_injective Qs.subtype_injective
      rw [hFeq, Subgroup.map_subgroupOf_eq_of_le hBQs]
  -- `C_G(B) ≤ E` (Corollary 12.6(b)), so `P'` is an abelian Sylow `p`-subgroup of `G`.
  have hP'E : (P' : Subgroup G) ≤ E :=
    hP'C.trans (centralizer_le_E_of_tau2 hG h hq hB hBE).1
  -- but then a Sylow `p`-subgroup of `E` has full `G`-order, and is abelian by 12.5(b),
  -- while all Sylow `p`-subgroups of `G` are nonabelian.
  have hpσ : p ∉ S10.sigma M := tau2_subset_sigma_compl M hp
  obtain ⟨PE, hP'PE⟩ := (P'.isPGroup'.comap_subtype (K := E)).exists_le_sylow
  set Pmap : Subgroup G := (PE : Subgroup ↥E).map E.subtype with hPmapdef
  have hP'_le_Pmap : (P' : Subgroup G) ≤ Pmap := by
    rw [hPmapdef, ← Subgroup.map_subgroupOf_eq_of_le hP'E]
    exact Subgroup.map_mono hP'PE
  have hPmap_card : Nat.card ↥Pmap = p ^ (Nat.card G).factorization p := by
    have hle : Nat.card ↥Pmap ∣ p ^ (Nat.card G).factorization p := by
      obtain ⟨k, hk⟩ := (PE.isPGroup'.map E.subtype).exists_card_eq
      rw [← hPmapdef] at hk
      have hdvd : (p : ℕ) ^ k ∣ Nat.card G := hk ▸ Subgroup.card_subgroup_dvd_card Pmap
      have hk_le : k ≤ (Nat.card G).factorization p :=
        (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp hdvd
      rw [hk]
      exact pow_dvd_pow p hk_le
    have hge : p ^ (Nat.card G).factorization p ∣ Nat.card ↥Pmap := by
      rw [← P'.card_eq_multiplicity]
      exact Subgroup.card_dvd_of_le hP'_le_Pmap
    exact Nat.dvd_antisymm hle hge
  set PS : Sylow p G := Sylow.ofCard Pmap hPmap_card with hPSdef
  -- abelian (Theorem 12.5(b) via the Sylow of `↥M`):
  have hPmap_le_M : Pmap ≤ M := (Subgroup.map_subtype_le _).trans h.E_le
  have hPmap_ab : IsMulCommutative ↥Pmap := by
    have hcardM : Nat.card ↥(Pmap.subgroupOf M) = p ^ (Nat.card ↥M).factorization p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPmap_le_M).toEquiv, hPmapdef,
        Subgroup.card_map_of_injective E.subtype_injective, PE.card_eq_multiplicity,
        factorization_card_eq_of_notMem_sigma h hpσ]
    have h125b := (Msigma_nilpotent_of_tau2 hG h.mem_maximal hp hA hAM).2.1.1
      (Sylow.ofCard (Pmap.subgroupOf M) hcardM)
    have e : ↥(Pmap.subgroupOf M) ≃* ↥Pmap := Subgroup.subgroupOfEquivOfLe hPmap_le_M
    exact S11.isMulCommutative_of_mulEquiv e h125b
  -- nonabelian (hypothesis + Sylow conjugacy):
  obtain ⟨S₀, hS₀⟩ := hnonab
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G PS S₀
  apply hS₀
  have hcoe : (S₀ : Subgroup G) = MulAut.conj g • Pmap := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def,
      Subgroup.pointwise_smul_def]
    rfl
  rw [hcoe, mulAut_smul_eq_map]
  exact S11.isMulCommutative_of_mulEquiv
    (Subgroup.equivMapOfInjective Pmap _ (MulAut.conj g).injective) hPmap_ab

/-- The image of a Sylow `p`-subgroup of `E` is abelian (Theorem 12.5(b) transported). -/
theorem map_sylow_E_isMulCommutative [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAM : A ≤ M)
    (PE : Sylow p ↥E) :
    IsMulCommutative ↥((PE : Subgroup ↥E).map E.subtype) := by
  have hpσ : p ∉ S10.sigma M := tau2_subset_sigma_compl M hp
  set Pmap : Subgroup G := (PE : Subgroup ↥E).map E.subtype with hPmapdef
  have hPmap_le_M : Pmap ≤ M := (Subgroup.map_subtype_le _).trans h.E_le
  have hcardM : Nat.card ↥(Pmap.subgroupOf M) = p ^ (Nat.card ↥M).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPmap_le_M).toEquiv, hPmapdef,
      Subgroup.card_map_of_injective E.subtype_injective, PE.card_eq_multiplicity,
      factorization_card_eq_of_notMem_sigma h hpσ]
  have h125b := (Msigma_nilpotent_of_tau2 hG h.mem_maximal hp hA hAM).2.1.1
    (Sylow.ofCard (Pmap.subgroupOf M) hcardM)
  exact S11.isMulCommutative_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hPmap_le_M) h125b

set_option backward.isDefEq.respectTransparency false in
/-- **BG Theorem 12.7(b)(c), core block**: the canonical line
`A₀ = A ⊓ C_G(M_σ)` of order `p`, with `M_σ ≤ C_G(A₀)` and the dichotomy (c): every
other line `X ∈ ℰ_p¹(E)` has `C_{M_σ}(X) = 1` and `C_G(X) ⊄ M` (mmd L3220-3236).

The dichotomy is by Lemma 10.13(c) applied inside a nonabelian Sylow `p`-subgroup
`S ⊇ P` of `G`: either `X = Ω₁(Z(S))` (then `S ≤ C_G(X)` and `S ⊄ M`), or `X` is
conjugate to `A₀` by some `n ∈ N_S(A) − M`, transporting `ℳ(C_G(A₀)) = {M}` to
`ℳ(C_G(X)) = {M^n} ∌ M`. -/
theorem exists_canonical_line_of_nonabelianSylow [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    (hnonab : ∃ S : Sylow p G, ¬ IsMulCommutative (S : Subgroup G)) :
    ∃ A₀ : Subgroup G,
      A₀ = A ⊓ Subgroup.centralizer (S10.Msigma M : Set G) ∧
      Nat.card ↥A₀ = p ∧ A₀ ≤ A ∧
      S10.Msigma M ≤ Subgroup.centralizer (A₀ : Set G) ∧
      (∀ X ∈ elemAbelianOfRank G p 1, X ≤ E → X ≠ A₀ →
        S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) = ⊥ ∧
        ¬ (Subgroup.centralizer (X : Set G) ≤ M)) ∧
      (∀ W : Subgroup G, M ≤ Subgroup.normalizer (W : Set G) → IsPGroup p ↥W →
        W ≤ M → W ≤ A₀) := by
  classical
  have hAM : A ≤ M := hAE.trans h.E_le
  have hpσ : p ∉ S10.sigma M := tau2_subset_sigma_compl M hp
  have hMσ_ne : S10.Msigma M ≠ ⊥ := (S10.isHall_Msigma_Malpha hG h.mem_maximal).2.2.2.2
  have hMσp : ¬ p ∣ Nat.card ↥(S10.Msigma M) := by
    intro hdvd
    exact hpσ (S10.Msigma_isPiGroup M p
      (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩))
  have hAnormMσ : A ≤ Subgroup.normalizer ((S10.Msigma M : Subgroup G) : Set G) :=
    hAM.trans (le_normalizer_opiCoreInG _ _)
  -- the canonical line `A₀` with `C_{M_σ}(A₀) ≠ 1`, via the generation engine.
  obtain ⟨A₀, hA₀, hA₀A, hA₀C⟩ : ∃ A₀ ∈ elemAbelianOfRank G p 1, A₀ ≤ A ∧
      S10.Msigma M ⊓ Subgroup.centralizer (A₀ : Set G) ≠ ⊥ := by
    by_contra hno
    apply hMσ_ne
    rw [← le_bot_iff]
    refine le_of_forall_line_inf_centralizer_le hA hAnormMσ hMσp ?_
    intro Y hY hYA
    rcases Classical.em (S10.Msigma M ⊓ Subgroup.centralizer (Y : Set G) = ⊥) with hbot | hne
    · exact le_of_eq hbot
    · exact absurd ⟨Y, hY, hYA, hne⟩ hno
  have hM_single : maximalSubgroupsContaining
      (Subgroup.centralizer (A₀ : Set G)) = {M} :=
    maximalContaining_centralizer_line_eq_singleton hG h hp hA hAE hA₀ hA₀A hA₀C
  have hCA₀_le_M : Subgroup.centralizer (A₀ : Set G) ≤ M := by
    have hlt : Subgroup.centralizer (A₀ : Set G) < ⊤ :=
      lt_of_le_of_lt (Subgroup.centralizer_le_normalizer _)
        (normalizer_lt_top_of_le_of_ne_bot hG h.mem_maximal (hA₀A.trans hAM)
          (ne_bot_of_mem_elemAbelianOfRank_one hA₀))
    obtain ⟨Mst, hco, hle⟩ := (eq_top_or_exists_le_coatom _).resolve_left hlt.ne
    have hmem : Mst ∈ maximalSubgroupsContaining (Subgroup.centralizer (A₀ : Set G)) :=
      mem_maximalSubgroupsContaining.mpr ⟨hco, hle⟩
    rw [hM_single, Set.mem_singleton_iff] at hmem
    exact hmem ▸ hle
  -- the Sylow tower `A ≤ P ≤ S` with `P` abelian and `S` nonabelian.
  obtain ⟨PE, hAPE⟩ := hA.1.isPGroup.comap_subtype.exists_le_sylow (G := E)
  set P : Subgroup G := (PE : Subgroup ↥E).map E.subtype with hPdef
  have hAP : A ≤ P := by
    rw [hPdef, ← Subgroup.map_subgroupOf_eq_of_le hAE]
    exact Subgroup.map_mono hAPE
  have hP_le_M : P ≤ M := (Subgroup.map_subtype_le _).trans h.E_le
  have hP_pg : IsPGroup p ↥P := by rw [hPdef]; exact PE.isPGroup'.map _
  have hP_ab : IsMulCommutative ↥P :=
    map_sylow_E_isMulCommutative hG h hp hA hAM PE
  obtain ⟨S, hPS⟩ := hP_pg.exists_le_sylow
  have hS_nonab : ¬ IsMulCommutative ((S : Sylow p G) : Subgroup G) := by
    obtain ⟨S₀, hS₀⟩ := hnonab
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S₀ S
    intro hab
    apply hS₀
    have hcoe : (S₀ : Subgroup G) = MulAut.conj g⁻¹ • (S : Subgroup G) := by
      rw [← hg, Sylow.coe_subgroup_smul, ← mul_smul, ← map_mul, inv_mul_cancel,
        map_one, one_smul]
    rw [hcoe, mulAut_smul_eq_map]
    exact S11.isMulCommutative_of_mulEquiv
      (Subgroup.equivMapOfInjective _ _ (MulAut.conj g⁻¹).injective) hab
  -- `S ⊄ M` (else `S = P` would be an abelian Sylow `p`-subgroup of `G`).
  have hS_not_le_M : ¬ ((S : Subgroup G) ≤ M) := by
    intro hSM
    have hSP : (S : Subgroup G) = P := by
      rw [hPdef]
      exact map_sylow_E_maximal_in_M h hpσ PE (hPdef ▸ hPS) hSM S.isPGroup'
    exact hS_nonab (hSP ▸ hP_ab)
  -- centrality of `Z₀ = Ω₁(Z(S))` in `S`.
  set Z₀ : Subgroup G := S10.omega1CenterInG (S : Subgroup G) p with hZ₀def
  have hZ₀_eq : Z₀ = (omega1OfAbelian ↥(S : Subgroup G)
      (Subgroup.center ↥(S : Subgroup G)) p
      (fun _ hx y _ => (Subgroup.mem_center_iff.mp hx y).symm)).map
        (S : Subgroup G).subtype := rfl
  have hS_cent_Z₀ : (S : Subgroup G) ≤ Subgroup.centralizer (Z₀ : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [SetLike.mem_coe, hZ₀_eq, Subgroup.mem_map] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    have hz'c : z' ∈ Subgroup.center ↥(S : Subgroup G) := (mem_omega1OfAbelian.mp hz').1
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz'c ⟨q, hq⟩)).symm
  -- `A₀ ≠ Z₀` (else `S ≤ C_G(A₀) ≤ M`).
  have hA₀_ne_Z₀ : A₀ ≠ Z₀ := by
    rintro rfl
    exact hS_not_le_M (hS_cent_Z₀.trans hCA₀_le_M)
  -- `N_G(M) = M`.
  have hNM_eq : Subgroup.normalizer (M : Set G) = M := by
    have hMne : M ≠ ⊥ := fun hbot => (ne_bot_of_mem_elemAbelianOfRank_one hA₀)
      (le_bot_iff.mp (hbot ▸ (hA₀A.trans hAM)))
    have hlt := normalizer_lt_top_of_le_of_ne_bot hG h.mem_maximal le_rfl hMne
    by_contra hne
    exact hlt.ne ((mem_maximalSubgroups.mp h.mem_maximal).2 _
      (lt_of_le_of_ne Subgroup.le_normalizer (Ne.symm hne)))
  -- the (c) dichotomy.
  have hAmax : IsMaximalElementaryAbelian p A :=
    (isMaximalElementaryAbelian_of_mem_tau2 hG h.mem_maximal Fact.out hp hAM hA).1
  have hpG : p ∈ (Nat.card G).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨Fact.out, ?_, Nat.card_pos.ne'⟩
    have h1 : (p : ℕ) ∣ Nat.card ↥A := by rw [hA.2]; exact dvd_pow_self p two_ne_zero
    exact h1.trans (Subgroup.card_subgroup_dvd_card A)
  have hc : ∀ X ∈ elemAbelianOfRank G p 1, X ≤ E → X ≠ A₀ →
      S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) = ⊥ ∧
      ¬ (Subgroup.centralizer (X : Set G) ≤ M) := by
    intro X hX hXE hXA₀
    have hXA : X ≤ A := line_le_of_le_E_of_tau2 hG h hp hA hAE hX hXE
    rcases eq_or_ne X Z₀ with heq | hXZ₀
    · -- `X = Z₀`: `S ≤ C_G(X)` and `S ⊄ M`.
      have hSC : (S : Subgroup G) ≤ Subgroup.centralizer (X : Set G) := by
        rw [heq]; exact hS_cent_Z₀
      have hC_not_le : ¬ (Subgroup.centralizer (X : Set G) ≤ M) :=
        fun hcon => hS_not_le_M (hSC.trans hcon)
      refine ⟨?_, hC_not_le⟩
      by_contra hne
      exact hC_not_le (by
        have hsingle := maximalContaining_centralizer_line_eq_singleton hG h hp hA hAE
          hX hXA hne
        have hlt : Subgroup.centralizer (X : Set G) < ⊤ :=
          lt_of_le_of_lt (Subgroup.centralizer_le_normalizer _)
            (normalizer_lt_top_of_le_of_ne_bot hG h.mem_maximal (hXA.trans hAM)
              (ne_bot_of_mem_elemAbelianOfRank_one hX))
        obtain ⟨Mst, hco, hle⟩ := (eq_top_or_exists_le_coatom _).resolve_left hlt.ne
        have hmem : Mst ∈ maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) :=
          mem_maximalSubgroupsContaining.mpr ⟨hco, hle⟩
        rw [hsingle, Set.mem_singleton_iff] at hmem
        exact hmem ▸ hle)
    · -- `X ≠ Z₀`: Lemma 10.13(c) conjugates `A₀` to `X` inside `S`.
      have hA₀_in : S10.elemAbelianOfRankIn p 1 A A₀ := ⟨hA₀, hA₀A⟩
      have hX_in : S10.elemAbelianOfRankIn p 1 A X := ⟨hX, hXA⟩
      have h1013 := (S10.nonabelian_pSubgroup_rankTwo_elemAbelian_structure hG hpG hA
        hAmax S.isPGroup' hS_nonab (hAP.trans hPS) hA₀_in hA₀_ne_Z₀).2.2
      obtain ⟨n, hnNS, hn_eq⟩ := h1013 A₀ X hA₀_in hA₀_ne_Z₀ hX_in hXZ₀
      -- `n ∉ M`: otherwise `n ∈ S ⊓ M = P` is abelian and fixes `A₀`.
      have hn_not_M : n ∉ M := by
        intro hnM
        have hnP : n ∈ P := by
          have hSM_eq : (S : Subgroup G) ⊓ M = P := by
            refine map_sylow_E_maximal_in_M h hpσ PE ?_ inf_le_right ?_
            · rw [← hPdef]
              exact le_inf hPS hP_le_M
            · exact (S.isPGroup'.to_inf_left :
                IsPGroup p ↥((S : Subgroup G) ⊓ M))
          have hmem : n ∈ (S : Subgroup G) ⊓ M := ⟨hnNS.2, hnM⟩
          rwa [hSM_eq] at hmem
        apply hXA₀
        rw [← hn_eq]
        -- `n ∈ P` abelian fixes `A₀ ≤ A ≤ P` pointwise.
        have hfix : ∀ x ∈ A₀, n * x * n⁻¹ = x := by
          intro x hx
          have hxP : x ∈ P := hAP (hA₀A hx)
          have hcomm : n * x = x * n :=
            congrArg Subtype.val (hP_ab.is_comm.comm (⟨n, hnP⟩ : ↥P) ⟨x, hxP⟩)
          calc n * x * n⁻¹ = x * n * n⁻¹ := by rw [hcomm]
            _ = x := by group
        ext z
        rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
        have hinv : ((MulAut.conj n)⁻¹ • z : G) = n⁻¹ * z * n := rfl
        rw [hinv]
        constructor
        · intro hz
          have h1 := hfix _ hz
          have h2 : z = n⁻¹ * z * n := by
            calc z = n * (n⁻¹ * z * n) * n⁻¹ := by group
              _ = n⁻¹ * z * n := h1
          exact h2 ▸ hz
        · intro hz
          have h1 := hfix z hz
          have h2 : n⁻¹ * z * n = z := by
            calc n⁻¹ * z * n = n⁻¹ * (n * z * n⁻¹) * n := by rw [h1]
              _ = z := by group
          rw [h2]
          exact hz
      -- conjugation transport: `C_G(X) = (conj n) • C_G(A₀)`.
      have hCX_eq : Subgroup.centralizer (X : Set G)
          = MulAut.conj n • Subgroup.centralizer (A₀ : Set G) := by
        rw [centralizer_conj_smul, hn_eq]
      have hnM_ne : MulAut.conj n • M ≠ M := by
        intro heq
        exact hn_not_M (hNM_eq ▸ mem_normalizer_of_conj_smul_eq_self heq)
      have hCX_le : Subgroup.centralizer (X : Set G) ≤ MulAut.conj n • M := by
        rw [hCX_eq]
        exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hCA₀_le_M
      have hMn_co : IsCoatom (MulAut.conj n • M) :=
        isCoatom_conj_smul (mem_maximalSubgroups.mp h.mem_maximal)
      constructor
      · -- `C_{M_σ}(X) = 1`.
        by_contra hne
        have hsingle := maximalContaining_centralizer_line_eq_singleton hG h hp hA hAE
          hX hXA hne
        have hmem : MulAut.conj n • M ∈
            maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) :=
          mem_maximalSubgroupsContaining.mpr ⟨hMn_co, hCX_le⟩
        rw [hsingle, Set.mem_singleton_iff] at hmem
        exact hnM_ne hmem
      · -- `C_G(X) ⊄ M`.
        intro hcon
        have hmem : MulAut.conj n⁻¹ • M ∈
            maximalSubgroupsContaining (Subgroup.centralizer (A₀ : Set G)) := by
          refine mem_maximalSubgroupsContaining.mpr
            ⟨isCoatom_conj_smul (mem_maximalSubgroups.mp h.mem_maximal), ?_⟩
          have h1 : Subgroup.centralizer (A₀ : Set G)
              = MulAut.conj n⁻¹ • Subgroup.centralizer (X : Set G) := by
            rw [centralizer_conj_smul]
            congr 1
            rw [← hn_eq, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
          rw [h1]
          exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hcon
        rw [hM_single, Set.mem_singleton_iff] at hmem
        have hninv : (n⁻¹ : G) ∈ M := hNM_eq ▸ mem_normalizer_of_conj_smul_eq_self hmem
        exact hn_not_M (by simpa using M.inv_mem hninv)
  -- `M_σ ≤ C_G(A₀)` by the generation engine and (c).
  have hMσ_cent : S10.Msigma M ≤ Subgroup.centralizer (A₀ : Set G) := by
    refine le_of_forall_line_inf_centralizer_le hA hAnormMσ hMσp ?_
    intro Y hY hYA
    rcases eq_or_ne Y A₀ with rfl | hne
    · exact inf_le_right
    · rw [(hc Y hY (hYA.trans hAE) hne).1]
      exact bot_le
  -- `A₀ = A ⊓ C_G(M_σ)`.
  have hA₀_le_inf : A₀ ≤ A ⊓ Subgroup.centralizer (S10.Msigma M : Set G) :=
    le_inf hA₀A (le_centralizer_swap hMσ_cent)
  have hinf_eq : A ⊓ Subgroup.centralizer (S10.Msigma M : Set G) = A₀ := by
    have hD_le_A : A ⊓ Subgroup.centralizer (S10.Msigma M : Set G) ≤ A := inf_le_left
    have hDdvd : Nat.card
        ↥(A ⊓ Subgroup.centralizer (S10.Msigma M : Set G) : Subgroup G) ∣ p ^ 2 := by
      rw [← hA.2]
      exact Subgroup.card_dvd_of_le hD_le_A
    obtain ⟨i, hi2, hicard⟩ := (Nat.dvd_prime_pow Fact.out).mp hDdvd
    interval_cases i
    · -- `|D| = 1` is impossible: `A₀ ≤ D` has order `p`.
      exfalso
      have h1 : Nat.card ↥A₀ ∣ p ^ 0 := by
        rw [← hicard]
        exact Subgroup.card_dvd_of_le hA₀_le_inf
      rw [pow_zero] at h1
      have h2 : Nat.card ↥A₀ = p := by rw [hA₀.2, pow_one]
      rw [h2] at h1
      exact (Fact.out : p.Prime).one_lt.ne' (Nat.eq_one_of_dvd_one h1)
    · -- `|D| = p`: `D = A₀`.
      refine (Subgroup.eq_of_le_of_card_ge hA₀_le_inf ?_).symm
      rw [hicard, pow_one, hA₀.2, pow_one]
    · -- `|D| = p²`: then `A ≤ C(M_σ)`, contradicting Theorem 12.5(d).
      exfalso
      have hD_eq : A ⊓ Subgroup.centralizer (S10.Msigma M : Set G) = A :=
        Subgroup.eq_of_le_of_card_ge hD_le_A (by rw [hicard, hA.2])
      have hA_cent : A ≤ Subgroup.centralizer (S10.Msigma M : Set G) :=
        hD_eq ▸ inf_le_right
      have h125d := (Msigma_nilpotent_of_tau2 hG h.mem_maximal hp hA hAM).2.2.2.1
      apply hMσ_ne
      rw [← le_bot_iff, ← h125d]
      exact le_inf le_rfl (le_centralizer_swap hA_cent)
  -- `M`-invariant `p`-subgroups land in `A₀` (`C_P(M_σ) = A₀` via the cyclic complement
  -- `Z` of Lemma 10.13(b)).
  have hP_le_E : P ≤ E := by rw [hPdef]; exact Subgroup.map_subtype_le _
  have habs : ∀ W : Subgroup G, M ≤ Subgroup.normalizer (W : Set G) → IsPGroup p ↥W →
      W ≤ M → W ≤ A₀ := by
    -- the decomposition `P = C_S(A) = A₀ ⊔ Z` with `Z` cyclic.
    obtain ⟨Z, hZS, hZcyc, hZ₀Z, hA₀Z, hCSA⟩ :=
      (S10.nonabelian_pSubgroup_rankTwo_elemAbelian_structure hG hpG hA
        hAmax S.isPGroup' hS_nonab (hAP.trans hPS) ⟨hA₀, hA₀A⟩ hA₀_ne_Z₀).2.1
    have hP_eq : Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G) = P := by
      refine map_sylow_E_maximal_in_M h hpσ PE ?_ ?_ ?_
      · rw [← hPdef]
        refine le_inf ?_ hPS
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact congrArg Subtype.val
          (hP_ab.is_comm.comm (⟨a, hAP ha⟩ : ↥P) ⟨x, hx⟩)
      · exact inf_le_left.trans
          ((centralizer_le_E_of_tau2 hG h hp hA hAE).1.trans h.E_le)
      · exact (S.isPGroup'.to_inf_right :
          IsPGroup p ↥(Subgroup.centralizer (A : Set G) ⊓ (S : Subgroup G)))
    have hP_sup : P = A₀ ⊔ Z := by rw [← hP_eq, hCSA]
    have hZ_le_P : Z ≤ P := hP_sup ▸ le_sup_right
    have hA₀_le_P : A₀ ≤ P := hP_sup ▸ le_sup_left
    -- `Z ⊓ C_G(M_σ) = ⊥`: a line in `Z` would violate (c).
    have hZC_bot : Z ⊓ Subgroup.centralizer (S10.Msigma M : Set G) = ⊥ := by
      by_contra hne
      obtain ⟨z, hz, hz1⟩ :=
        ((Z ⊓ Subgroup.centralizer (S10.Msigma M : Set G)).bot_or_exists_ne_one).resolve_left
          hne
      -- pass to a power `y` of order `p`.
      have hzS : z ∈ (S : Subgroup G) := hZS hz.1
      obtain ⟨k, hk⟩ := S.isPGroup' ⟨z, hzS⟩
      have hk_ord : orderOf z ∣ p ^ k := by
        rw [orderOf_dvd_iff_pow_eq_one]
        exact congrArg Subtype.val hk
      obtain ⟨i, hik, hi_ord⟩ := (Nat.dvd_prime_pow Fact.out).mp hk_ord
      have hipos : 0 < i := by
        rcases Nat.eq_zero_or_pos i with rfl | hpos
        · exfalso
          rw [pow_zero, orderOf_eq_one_iff] at hi_ord
          exact hz1 hi_ord
        · exact hpos
      set y : G := z ^ (p ^ (i - 1)) with hydef
      have hyord : orderOf y = p := by
        rw [hydef, orderOf_pow, hi_ord, Nat.gcd_eq_right (pow_dvd_pow p (by omega)),
          Nat.pow_div (by omega) (Fact.out : p.Prime).pos,
          Nat.sub_sub_self (by omega : 1 ≤ i), pow_one]
      have hy1 : y ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hyord
        exact (Fact.out : p.Prime).one_lt.ne hyord
      have hyZ : y ∈ Z := Z.pow_mem hz.1 _
      have hyC : y ∈ Subgroup.centralizer (S10.Msigma M : Set G) :=
        Subgroup.pow_mem _ hz.2 _
      set Xz : Subgroup G := Subgroup.zpowers y with hXzdef
      have hXz_mem : Xz ∈ elemAbelianOfRank G p 1 := by
        refine ⟨Subgroup.IsElementaryAbelian.of_card_prime ?_, ?_⟩
        · rw [hXzdef, Nat.card_zpowers, hyord]
        · rw [hXzdef, Nat.card_zpowers, hyord, pow_one]
      have hXzE : Xz ≤ E := by
        rw [hXzdef, Subgroup.zpowers_le]
        exact (hZ_le_P.trans hP_le_E) hyZ
      have hXz_ne_A₀ : Xz ≠ A₀ := by
        intro heq
        have h1 : y ∈ A₀ ⊓ Z := ⟨heq ▸ Subgroup.mem_zpowers y, hyZ⟩
        rw [hA₀Z] at h1
        exact hy1 (Subgroup.mem_bot.mp h1)
      have hcXz := (hc Xz hXz_mem hXzE hXz_ne_A₀).1
      apply hMσ_ne
      rw [← le_bot_iff, ← hcXz]
      refine le_inf le_rfl ?_
      rw [hXzdef, centralizer_zpowers_eq_singleton]
      intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact (Subgroup.mem_centralizer_iff.mp hyC s (SetLike.mem_coe.mpr hs)).symm
    -- main body of the absorption.
    intro W hWnorm hWp hWM
    -- `W ≤ P` by Sylow conjugacy and `M`-invariance.
    have hWP : W ≤ P := by
      obtain ⟨TW, hWTW⟩ := hWp.comap_subtype.exists_le_sylow (G := M)
      have hPcard : Nat.card ↥(P.subgroupOf M) = p ^ (Nat.card ↥M).factorization p := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le_M).toEquiv, hPdef,
          Subgroup.card_map_of_injective E.subtype_injective, PE.card_eq_multiplicity,
          factorization_card_eq_of_notMem_sigma h hpσ]
      obtain ⟨m, hm⟩ := MulAction.exists_smul_eq ↥M TW (Sylow.ofCard (P.subgroupOf M) hPcard)
      have hW_le_TWmap : W ≤ (TW : Subgroup ↥M).map M.subtype := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hWM]
        exact Subgroup.map_mono hWTW
      have hsmul_eq : MulAut.conj (m : G) • ((TW : Subgroup ↥M).map M.subtype) = P := by
        have h1 : ((m • TW : Sylow p ↥M) : Subgroup ↥M).map M.subtype = P := by
          rw [hm]
          change (P.subgroupOf M).map M.subtype = P
          exact Subgroup.map_subgroupOf_eq_of_le hP_le_M
        rw [← h1, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def,
          Subgroup.pointwise_smul_def, Subgroup.map_map, Subgroup.map_map]
        rfl
      have hWfix : MulAut.conj (m : G) • W = W :=
        conj_smul_eq_self_of_mem_normalizer (hWnorm m.2)
      calc W = MulAut.conj (m : G) • W := hWfix.symm
        _ ≤ MulAut.conj (m : G) • ((TW : Subgroup ↥M).map M.subtype) :=
            Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hW_le_TWmap
        _ = P := hsmul_eq
    -- `W ≤ C_G(M_σ)`.
    have hWMσ_bot : W ⊓ S10.Msigma M = ⊥ := by
      rw [← Subgroup.card_eq_one]
      obtain ⟨k, hk⟩ := hWp.exists_card_eq
      have h1 : Nat.card ↥(W ⊓ S10.Msigma M : Subgroup G) ∣ p ^ k := by
        rw [← hk]
        exact Subgroup.card_dvd_of_le inf_le_left
      have hnp : ¬ p ∣ Nat.card ↥(W ⊓ S10.Msigma M : Subgroup G) := by
        intro hdvd
        exact hMσp (hdvd.trans (Subgroup.card_dvd_of_le inf_le_right))
      exact Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.pow_right k
          ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hnp).symm) h1
    have hWC : W ≤ Subgroup.centralizer (S10.Msigma M : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, ← le_bot_iff, ← hWMσ_bot]
      rw [Subgroup.commutator_le]
      intro w hw s hs
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h1 : s * w⁻¹ * s⁻¹ ∈ W :=
          (Subgroup.mem_normalizer_iff.mp (hWnorm ((S10.Msigma_le M) hs)) w⁻¹).mp
            (W.inv_mem hw)
        have h2 : w * (s * w⁻¹ * s⁻¹) ∈ W := W.mul_mem hw h1
        rw [commutatorElement_def]
        simpa [mul_assoc] using h2
      · have h1 : w * s * w⁻¹ ∈ S10.Msigma M :=
          (Subgroup.mem_normalizer_iff.mp
            ((le_normalizer_opiCoreInG _ _) (hWM hw)) s).mp hs
        have h2 : w * s * w⁻¹ * s⁻¹ ∈ S10.Msigma M :=
          Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hs)
        rwa [commutatorElement_def]
    -- decompose `x ∈ W ≤ P = A₀ ⊔ Z`; the `Z`-part centralizes `M_σ`, hence is trivial.
    intro x hx
    have hxP : x ∈ P := hWP hx
    have hxC : x ∈ Subgroup.centralizer (S10.Msigma M : Set G) := hWC hx
    have hA₀P_norm : (A₀.subgroupOf P).Normal := by
      constructor
      intro n hn g
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have hcomm : (g : G) * (n : G) = (n : G) * (g : G) :=
        congrArg Subtype.val (hP_ab.is_comm.comm (g : ↥P) (n : ↥P))
      have heq : ((g * n * g⁻¹ : ↥P) : G) = (n : G) := by
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
        rw [hcomm]
        group
      rw [heq]
      exact hn
    have hxsub : (⟨x, hxP⟩ : ↥P) ∈ A₀.subgroupOf P ⊔ Z.subgroupOf P := by
      rw [← Subgroup.subgroupOf_sup hA₀_le_P hZ_le_P, ← hP_sup]
      exact Subgroup.mem_subgroupOf.mpr hxP
    have hxsub' : (⟨x, hxP⟩ : ↥P) ∈
        (A₀.subgroupOf P : Set ↥P) * (Z.subgroupOf P : Set ↥P) := by
      rw [← Subgroup.normal_mul]
      exact hxsub
    obtain ⟨a, ha, z, hz', haz⟩ := hxsub'
    have haA₀ : (a : G) ∈ A₀ := Subgroup.mem_subgroupOf.mp ha
    have hzZ : (z : G) ∈ Z := Subgroup.mem_subgroupOf.mp hz'
    have hzeq : (z : G) = ((a : ↥P) : G)⁻¹ * x := by
      have h1 : (z : ↥P) = a⁻¹ * ⟨x, hxP⟩ := by rw [← haz]; group
      calc (z : G) = ((a⁻¹ * ⟨x, hxP⟩ : ↥P) : G) := congrArg Subtype.val h1
        _ = ((a : ↥P) : G)⁻¹ * x := rfl
    have hzC : (z : G) ∈ Z ⊓ Subgroup.centralizer (S10.Msigma M : Set G) := by
      refine ⟨hzZ, ?_⟩
      rw [hzeq]
      exact Subgroup.mul_mem _
        (Subgroup.inv_mem _ ((hA₀_le_inf.trans inf_le_right) haA₀)) hxC
    rw [hZC_bot, Subgroup.mem_bot] at hzC
    have hxa : x = ((a : ↥P) : G) := by
      have h1 : (⟨x, hxP⟩ : ↥P) = a := by
        rw [← haz, show z = 1 from Subtype.ext hzC]
        exact mul_one a
      calc x = ((⟨x, hxP⟩ : ↥P) : G) := rfl
        _ = ((a : ↥P) : G) := congrArg Subtype.val h1
    rw [hxa]
    exact haA₀
  exact ⟨A₀, hinf_eq.symm, by rw [hA₀.2, pow_one], hA₀A, hMσ_cent, hc, habs⟩

/-- A natural number whose prime factors all equal `q` is a power of `q`.
(Public: `S12_Theorem127d` reuses this for the Hall `τ₂`-subgroup `E₂`.) -/
theorem eq_pow_factorization_of_forall_eq {n q : ℕ}
    (hn : n ≠ 0) (hpi : ∀ r ∈ n.primeFactors, r = q) :
    n = q ^ n.factorization q := by
  classical
  have h1 := Nat.prod_factorization_pow_eq_self hn
  rcases Finset.eq_empty_or_nonempty n.primeFactors with hempty | ⟨r, hr⟩
  · have hn1 : n = 1 := by
      rcases Nat.primeFactors_eq_empty.mp hempty with h0 | h1'
      · exact absurd h0 hn
      · exact h1'
    rw [hn1]
    simp
  · have hrq : r = q := hpi r hr
    subst hrq
    have hsupp : n.factorization.support = {r} := by
      rw [Nat.support_factorization]
      exact Finset.eq_singleton_iff_unique_mem.mpr ⟨hr, fun s hs => hpi s hs⟩
    conv_lhs => rw [← h1]
    rw [Finsupp.prod, hsupp, Finset.prod_singleton]

/-- **BG Theorem 12.7(b)** (mmd L3237-3243): with the canonical line
`A₀ = A ⊓ C_G(M_σ)`: `M ≤ N_G(A₀)`, `F(M) = M_σ ⊔ A₀`, and `M_σ ⊓ A₀ = ⊥`.
By (a) and Lemma 12.2(a), `π(F(M)) ⊆ σ(M) ∪ {p}`; the `q`-core of the nilpotent `F(M)`
lands in `M_σ` (`q ∈ σ`) or in `A₀` (`q = p`, by the absorption clause), so
`|F(M)| ∣ |M_σ ⊔ A₀|`, while `M_σ ⊔ A₀ ≤ F(M)` since both factors are normal
nilpotent. -/
theorem fitting_eq_sup_of_canonical_line [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    (hprime_eq : ∀ q : ℕ, q.Prime → q ∈ tau2 M → q = p)
    {A₀ : Subgroup G} (hA₀eq : A₀ = A ⊓ Subgroup.centralizer (S10.Msigma M : Set G))
    (hA₀card : Nat.card ↥A₀ = p)
    (hMσC : S10.Msigma M ≤ Subgroup.centralizer (A₀ : Set G))
    (habs : ∀ W : Subgroup G, M ≤ Subgroup.normalizer (W : Set G) → IsPGroup p ↥W →
      W ≤ M → W ≤ A₀) :
    M ≤ Subgroup.normalizer (A₀ : Set G) ∧
    Ch2.S08.fittingInG M = S10.Msigma M ⊔ A₀ ∧ S10.Msigma M ⊓ A₀ = ⊥ := by
  classical
  have hAM : A ≤ M := hAE.trans h.E_le
  have hA₀A : A₀ ≤ A := hA₀eq ▸ inf_le_left
  have hA₀M : A₀ ≤ M := hA₀A.trans hAM
  have hpσ : p ∉ S10.sigma M := tau2_subset_sigma_compl M hp
  have hMσp : ¬ p ∣ Nat.card ↥(S10.Msigma M) := by
    intro hdvd
    exact hpσ (S10.Msigma_isPiGroup M p
      (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩))
  have hA₀pg : IsPGroup p ↥A₀ := IsPGroup.of_card (by rw [hA₀card, pow_one])
  -- `M ≤ N_G(A₀)`.
  have hA₀_norm : M ≤ Subgroup.normalizer (A₀ : Set G) := by
    rw [← h.E_compl_sup]
    refine sup_le (hMσC.trans (Subgroup.centralizer_le_normalizer _)) ?_
    rw [hA₀eq]
    exact le_normalizer_inf (E_le_normalizer_of_tau2 hG h hp hA hAE)
      ((h.E_le.trans (le_normalizer_opiCoreInG _ _)).trans
        (normalizer_le_normalizer_centralizer _))
  -- `M_σ ⊓ A₀ = ⊥`.
  have hMσA₀_bot : S10.Msigma M ⊓ A₀ = ⊥ := by
    rw [← Subgroup.card_eq_one]
    have h1 : Nat.card ↥(S10.Msigma M ⊓ A₀ : Subgroup G) ∣ p := by
      rw [← hA₀card]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ h1 with h2 | h2
    · exact h2
    · exfalso
      apply hMσp
      rw [← h2]
      exact Subgroup.card_dvd_of_le inf_le_left
  -- `M_σ ⊔ A₀ ≤ F(M)`.
  have hMσ_le_F : S10.Msigma M ≤ Ch2.S08.fittingInG M := by
    have h1 : ((S10.Msigma M).subgroupOf M).Normal := by
      rw [S10.Msigma_subgroupOf]; infer_instance
    have h2 : Group.IsNilpotent ↥(S10.Msigma M) :=
      (Msigma_nilpotent_of_tau2 hG h.mem_maximal hp hA hAM).1
    have h3 : Group.IsNilpotent ↥((S10.Msigma M).subgroupOf M) :=
      Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (S10.Msigma_le M)).symm
    have h4 : (S10.Msigma M).subgroupOf M ≤ Ch01.fitting ↥M :=
      Ch01.nilpotent_normal_le_fitting
    calc S10.Msigma M
        = ((S10.Msigma M).subgroupOf M).map M.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le (S10.Msigma_le M)).symm
      _ ≤ (Ch01.fitting ↥M).map M.subtype := Subgroup.map_mono h4
      _ = Ch2.S08.fittingInG M := rfl
  have hA₀_le_F : A₀ ≤ Ch2.S08.fittingInG M :=
    Ch2.S08.le_fittingInG_of_normal_isPiSubgroup_singleton hA₀M
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hA₀M).mpr hA₀_norm)
      (Subgroup.isPiSubgroup_of_isPGroup_of_mem hA₀pg rfl)
  have hJ_le_F : S10.Msigma M ⊔ A₀ ≤ Ch2.S08.fittingInG M := sup_le hMσ_le_F hA₀_le_F
  -- `|F(M)| ∣ |M_σ ⊔ A₀|`: per-prime analysis of the nilpotent `F(M)`.
  have : Group.IsNilpotent ↥(Ch2.S08.fittingInG M) := Ch2.S08.fittingInG_isNilpotent M
  have hM_norm_F : M ≤ Subgroup.normalizer ((Ch2.S08.fittingInG M : Subgroup G) : Set G) :=
    fun m hm => Ch2.S08.mem_normalizer_fittingInG_of_mem hm
  have hkey : ∀ q : ℕ, q.Prime →
      (Nat.card ↥(Ch2.S08.fittingInG M)).factorization q ≤
        (Nat.card ↥(S10.Msigma M ⊔ A₀ : Subgroup G)).factorization q := by
    intro q hq_prime
    have : Fact q.Prime := ⟨hq_prime⟩
    by_cases hqF : q ∣ Nat.card ↥(Ch2.S08.fittingInG M)
    case neg =>
      rw [Nat.factorization_eq_zero_of_not_dvd hqF]
      exact Nat.zero_le _
    case pos =>
    set Fq : Subgroup G := opiCoreInG ({q} : Set ℕ) (Ch2.S08.fittingInG M) with hFqdef
    have hHall := S10.oPiCore_isHall_of_isNilpotent
      (K := ↥(Ch2.S08.fittingInG M)) ({q} : Set ℕ)
    have hc1 : Nat.card ↥Fq = Nat.card ↥(Ch03.oPiCore ({q} : Set ℕ)
        ↥(Ch2.S08.fittingInG M)) :=
      Subgroup.card_map_of_injective (Ch2.S08.fittingInG M).subtype_injective
    -- `ν_q(|Fq|) = ν_q(|F|)` (Hall `{q}`-subgroup).
    have hFq_card : (Nat.card ↥Fq).factorization q
        = (Nat.card ↥(Ch2.S08.fittingInG M)).factorization q := by
      have hidx : ((Ch03.oPiCore ({q} : Set ℕ)
          ↥(Ch2.S08.fittingInG M)).index).factorization q = 0 := by
        apply Nat.factorization_eq_zero_of_not_dvd
        intro hdvd
        exact hHall.2 q (Nat.mem_primeFactors.mpr
          ⟨hq_prime, hdvd, Subgroup.index_ne_zero_of_finite⟩) rfl
      have hmul := Subgroup.card_mul_index
        (Ch03.oPiCore ({q} : Set ℕ) ↥(Ch2.S08.fittingInG M))
      have hfac : (Nat.card ↥(Ch03.oPiCore ({q} : Set ℕ)
            ↥(Ch2.S08.fittingInG M))).factorization q +
          ((Ch03.oPiCore ({q} : Set ℕ) ↥(Ch2.S08.fittingInG M)).index).factorization q
          = (Nat.card ↥(Ch2.S08.fittingInG M)).factorization q := by
        rw [← hmul, Nat.factorization_mul Nat.card_pos.ne'
          Subgroup.index_ne_zero_of_finite, Finsupp.add_apply]
      rw [hc1]
      omega
    have hFq_le_F : Fq ≤ Ch2.S08.fittingInG M := Subgroup.map_subtype_le _
    have hFq_le_M : Fq ≤ M := hFq_le_F.trans (Ch2.S08.fittingInG_le M)
    -- `Fq` is a `q`-group.
    have hFq_pi : ∀ r ∈ (Nat.card ↥Fq).primeFactors, r = q := by
      intro r hr
      have h1 : r ∈ (Nat.card ↥(Ch03.oPiCore ({q} : Set ℕ)
          ↥(Ch2.S08.fittingInG M))).primeFactors := by rwa [hc1] at hr
      exact hHall.1 r h1
    have hFq_pg : IsPGroup q ↥Fq :=
      IsPGroup.of_card (eq_pow_factorization_of_forall_eq Nat.card_pos.ne' hFq_pi)
    have hFq_ne : Fq ≠ ⊥ := by
      intro hbot
      have h1 : (Nat.card ↥Fq).factorization q = 0 := by
        rw [hbot, Subgroup.card_bot]
        simp
      rw [hFq_card] at h1
      have h2 : 0 < (Nat.card ↥(Ch2.S08.fittingInG M)).factorization q :=
        Nat.Prime.factorization_pos_of_dvd hq_prime Nat.card_pos.ne' hqF
      omega
    have hM_norm_Fq : M ≤ Subgroup.normalizer (Fq : Set G) :=
      le_normalizer_opiCoreInG_of_le_normalizer _ hM_norm_F
    have hNFq_le_M : Subgroup.normalizer (Fq : Set G) ≤ M := by
      have hlt := normalizer_lt_top_of_le_of_ne_bot hG h.mem_maximal hFq_le_M hFq_ne
      obtain ⟨Mst, hco, hle⟩ := (eq_top_or_exists_le_coatom _).resolve_left hlt.ne
      have hMst_eq : Mst = M := by
        have hM_le_Mst : M ≤ Mst := hM_norm_Fq.trans hle
        by_contra hne
        exact hco.1 ((mem_maximalSubgroups.mp h.mem_maximal).2 Mst
          (lt_of_le_of_ne hM_le_Mst (Ne.symm hne)))
      exact hMst_eq ▸ hle
    have h122 := prime_mem_sigma_or_tau2 hG h.mem_maximal hFq_le_M hFq_ne hFq_pg
      (mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp h.mem_maximal,
        hNFq_le_M⟩)
    have hFq_le_J : Fq ≤ S10.Msigma M ⊔ A₀ := by
      rcases h122 with hσ | hτ2
      · refine le_trans ?_ le_sup_left
        exact S10.sigma_subgroup_le_Msigma_of_isHall
          (S10.isHall_Msigma_Malpha hG h.mem_maximal).1 hFq_le_M
          (Subgroup.isPiSubgroup_of_isPGroup_of_mem hFq_pg hσ)
      · have hqp : q = p := hprime_eq q hq_prime hτ2
        subst hqp
        exact le_trans (habs Fq hM_norm_Fq hFq_pg hFq_le_M) le_sup_right
    calc (Nat.card ↥(Ch2.S08.fittingInG M)).factorization q
        = (Nat.card ↥Fq).factorization q := hFq_card.symm
      _ ≤ (Nat.card ↥(S10.Msigma M ⊔ A₀ : Subgroup G)).factorization q := by
          have hdvd := Subgroup.card_dvd_of_le hFq_le_J
          exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne'
            Nat.card_pos.ne').mpr hdvd q
  have hF_dvd : Nat.card ↥(Ch2.S08.fittingInG M) ∣
      Nat.card ↥(S10.Msigma M ⊔ A₀ : Subgroup G) := by
    rw [← Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne']
    intro q
    by_cases hq_prime : q.Prime
    · exact hkey q hq_prime
    · rw [Nat.factorization_eq_zero_of_not_prime _ hq_prime]
      exact Nat.zero_le _
  refine ⟨hA₀_norm, ?_, hMσA₀_bot⟩
  exact (Subgroup.eq_of_le_of_card_ge hJ_le_F
    (Nat.le_of_dvd Nat.card_pos hF_dvd)).symm

/-- **BG Theorem 12.7(e), parametrized core** (mmd L3245): for any `E₀ ≤ E` with
`A₀ ⊓ E₀ = ⊥` and `x ∈ M_σ#`, every prime of `|C_{E₀}(x)|` lies in `τ₁(M)`:
a `τ₃`-element of `E` lies in `E₃` and is excluded by Corollary 12.6(d); a `p`-element
centralizing `x` would give a line `X ≠ A₀` with `C_{M_σ}(X) ∋ x ≠ 1`, contradicting
(c) (or `A₀ ≤ E₀`, contradicting disjointness). -/
theorem primeFactors_centralizer_le_tau1_of_disjoint [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    (hprime_eq : ∀ q : ℕ, q.Prime → q ∈ tau2 M → q = p)
    {A₀ : Subgroup G}
    (hc : ∀ X ∈ elemAbelianOfRank G p 1, X ≤ E → X ≠ A₀ →
      S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) = ⊥ ∧
      ¬ (Subgroup.centralizer (X : Set G) ≤ M))
    {E₀ : Subgroup G} (hE₀E : E₀ ≤ E) (hA₀E₀ : A₀ ⊓ E₀ = ⊥)
    {x : G} (hx : x ∈ S10.Msigma M) (hx1 : x ≠ 1) :
    ∀ r ∈ (Nat.card ↥(E₀ ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G)).primeFactors,
      r ∈ tau1 M := by
  classical
  intro r hr
  have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr
  have : Fact r.Prime := ⟨hr_prime⟩
  -- Cauchy: an element `y` of order `r` in `E₀ ⊓ C_G(x)`.
  obtain ⟨y', hy'ord⟩ := exists_prime_orderOf_dvd_card' r (Nat.mem_primeFactors.mp hr).2.1
  set y : G := ((y' : ↥(E₀ ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G)) : G)
    with hydef
  have hyord : orderOf y = r := by
    rw [hydef, ← hy'ord]
    exact orderOf_injective
      (E₀ ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G).subtype
      (Subgroup.subtype_injective _) y'
  have hyE₀ : y ∈ E₀ := y'.2.1
  have hyC : y ∈ Subgroup.centralizer ({x} : Set G) := y'.2.2
  have hy1 : y ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hyord
    exact hr_prime.one_lt.ne hyord
  have hyE : y ∈ E := hE₀E hyE₀
  -- `x ∈ C_G(⟨y⟩)`.
  have hx_cent : x ∈ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
    rw [centralizer_zpowers_eq_singleton]
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact (Subgroup.mem_centralizer_iff.mp hyC x (Set.mem_singleton x)).symm
  -- `r ∈ τ₁ ∪ τ₂ ∪ τ₃`.
  have hrE : r ∈ (Nat.card ↥E).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨hr_prime, ?_, Nat.card_pos.ne'⟩
    rw [← hyord]
    exact Subgroup.orderOf_dvd_natCard E hyE
  rcases h.mem_tau_union_of_mem_primeFactors hG hrE with (h1 | h2) | h3
  · exact h1
  · -- `r ∈ τ₂`: then `r = p` and `⟨y⟩` is a line violating (c) or the disjointness.
    exfalso
    have hrp : r = p := hprime_eq r hr_prime h2
    subst hrp
    set Xy : Subgroup G := Subgroup.zpowers y with hXydef
    have hXy_mem : Xy ∈ elemAbelianOfRank G r 1 := by
      refine ⟨Subgroup.IsElementaryAbelian.of_card_prime ?_, ?_⟩
      · rw [hXydef, Nat.card_zpowers, hyord]
      · rw [hXydef, Nat.card_zpowers, hyord, pow_one]
    have hXyE : Xy ≤ E := by
      rw [hXydef, Subgroup.zpowers_le]
      exact hyE
    rcases eq_or_ne Xy A₀ with heq | hne
    · have h1 : y ∈ A₀ ⊓ E₀ := ⟨heq ▸ Subgroup.mem_zpowers y, hyE₀⟩
      rw [hA₀E₀, Subgroup.mem_bot] at h1
      exact hy1 h1
    · have hcXy := (hc Xy hXy_mem hXyE hne).1
      have hxmem : x ∈ S10.Msigma M ⊓ Subgroup.centralizer (Xy : Set G) :=
        ⟨hx, hXydef ▸ hx_cent⟩
      rw [hcXy, Subgroup.mem_bot] at hxmem
      exact hx1 hxmem
  · -- `r ∈ τ₃`: then `y ∈ E₃`, contradicting Corollary 12.6(d).
    exfalso
    have hyE₃ : y ∈ E₃ := by
      have hzpE : Subgroup.zpowers y ≤ E := by
        rw [Subgroup.zpowers_le]
        exact hyE
      have hE₃norm : (E₃.subgroupOf E).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer h.E₃_le).mpr (h.E3_normal hG)
      have hzp_pi : Ch03.Subgroup.IsPiGroup (tau3 M)
          ((Subgroup.zpowers y).subgroupOf E) := by
        intro q hq
        have h1 : Nat.card ↥((Subgroup.zpowers y).subgroupOf E) = r := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzpE).toEquiv,
            Nat.card_zpowers, hyord]
        rw [h1] at hq
        have h2 : q = r :=
          (Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hq) hr_prime).mp
            (Nat.mem_primeFactors.mp hq).2.1
        rwa [h2]
      have h1 : (Subgroup.zpowers y).subgroupOf E ≤ E₃.subgroupOf E :=
        S10.isPiGroup_le_of_normal_isHallSubgroup h.E₃_hall hzp_pi
      have h2 : (⟨y, hyE⟩ : ↥E) ∈ (Subgroup.zpowers y).subgroupOf E :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers y)
      exact Subgroup.mem_subgroupOf.mp (h1 h2)
    have h126d := (elemAb_normal_in_E_of_tau2 hG h hp hA hAE).2.2.2.1 y hyE₃ hy1
    have hxmem : x ∈ S10.Msigma M ⊓ Subgroup.centralizer ({y} : Set G) := by
      refine ⟨hx, ?_⟩
      have := hx_cent
      rw [centralizer_zpowers_eq_singleton] at this
      exact this
    rw [h126d, Subgroup.mem_bot] at hxmem
    exact hx1 hxmem

end OddOrder.BG.Ch3.S12


