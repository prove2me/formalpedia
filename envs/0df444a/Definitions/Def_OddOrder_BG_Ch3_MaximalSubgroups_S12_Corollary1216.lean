-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Corollary1216
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S12_Corollary1216
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T08:15:20.902924+00:00
-- url     : https://prove2.me/theorems/232c36d6-8087-4563-be98-95b0f53f858c
-- title:
--   BG §12: Corollary 12.16, $\sigma(M)$-subgroups and interaction with maximal subgroups
-- statement:
--   Formalizes Corollary 12.16 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §12: for a nonidentity $\sigma(M)$-subgroup $Y$ of $G$, a prime $p\in\pi(E)\cap\beta(G)'$ and $H\in\mathcal{M}(Y)$ not conjugate to $M$: (a) $r_p(N_H(Y))\le 1$; (b) if $p\in\tau_1(M)$ then a further restriction holds. It is a downstream leaf.
--
--   The main declaration: `card_derivedInG_conj`.
--
--   The bundle also proves 19 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S12_Corollary1216.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S12_Corollary1216.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Proposition1215

namespace OddOrder.BG.Ch3.S12.Cor1216

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- `2 ≤ pRank H q` (`q` prime) yields a rank-2 elementary abelian `A ∈ ℰ_q²(G)` with `A ≤ H`.
(Replicated from the private helper in `S12_Proposition1215`; the underlying PRank lemmas are
base-level.) -/
private theorem exists_mem_elemAbelianOfRank_two_le_of_two_le_pRank [Finite G] {H : Subgroup G}
    {q : ℕ} (hq_prime : q.Prime) (hpr : 2 ≤ pRank ↥H q) :
    ∃ A ∈ elemAbelianOfRank G q 2, A ≤ H := by
  obtain ⟨B, hB_ea, hB_log⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank (G := ↥H) (p := q) (n := 2) two_pos hpr
  have hB_card : q ^ 2 ≤ Nat.card ↥B :=
    le_trans (Nat.pow_le_pow_right hq_prime.one_lt.le hB_log)
      (Nat.pow_log_le_self q Nat.card_pos.ne')
  obtain ⟨K, hK_ea, hK_card⟩ :=
    IsElementaryAbelian.exists_subgroup_card_prime_sq hq_prime hB_ea hB_card
  refine ⟨(K.map B.subtype).map H.subtype, mem_elemAbelianOfRank.mpr ⟨?_, ?_⟩,
    Subgroup.map_subtype_le _⟩
  · exact Subgroup.IsElementaryAbelian.map H.subtype_injective
      (Subgroup.IsElementaryAbelian.map B.subtype_injective hK_ea)
  · rw [Subgroup.card_map_of_injective H.subtype_injective,
      Subgroup.card_map_of_injective B.subtype_injective]
    exact hK_card

/-- `pRank` is a `MulEquiv` invariant. (Replicated from S12_Proposition1215.) -/
private theorem pRank_eq_of_mulEquiv {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    {r : ℕ} (e : A ≃* B) : pRank A r = pRank B r :=
  le_antisymm (pRank_le_of_injective (f := e.toMonoidHom) e.injective)
    (pRank_le_of_injective (f := e.symm.toMonoidHom) e.symm.injective)

/-- If `A ⊔ N = ⊤` with `N ⊴` and `r ∤ |N|`, then `r ∤ [⊤:A]`. (Replicated from
S12_Proposition1215.) -/
private theorem not_dvd_index_of_sup_top_normal {K' : Type*} [Group K'] [Finite K'] {r : ℕ}
    {A N : Subgroup K'} [N.Normal] (htop : A ⊔ N = ⊤) (hrN : ¬ r ∣ Nat.card ↥N) :
    ¬ r ∣ A.index := by
  have hform := Subgroup.card_HK_mul_card_inf_eq_card_mul_card A N
  rw [show (↑A * ↑N : Set K') = ↑(A ⊔ N : Subgroup K') from (Subgroup.mul_normal A N).symm] at hform
  have hsup_dvd : Nat.card ↥(A ⊔ N : Subgroup K') ∣ Nat.card ↥A * Nat.card ↥N := ⟨_, hform.symm⟩
  rw [htop, Nat.card_congr (Subgroup.topEquiv).toEquiv] at hsup_dvd
  have hidx_dvd : A.index ∣ Nat.card ↥N := by
    have h2 : Nat.card ↥A * A.index ∣ Nat.card ↥A * Nat.card ↥N := by
      rw [A.card_mul_index]; exact hsup_dvd
    exact (Nat.mul_dvd_mul_iff_left (Nat.card_pos)).mp h2
  exact fun h => hrN (h.trans hidx_dvd)

/-- Monotonicity of the ambient derived subgroup. (Replicated from S09_Lemma95.) -/
private theorem derivedInG_mono {H K : Subgroup G} (hHK : H ≤ K) :
    derivedInG H ≤ derivedInG K := by
  rw [show derivedInG H = ⁅(H : Subgroup G), H⁆ from Subgroup.map_subtype_commutator H,
    show derivedInG K = ⁅(K : Subgroup G), K⁆ from Subgroup.map_subtype_commutator K]
  exact Subgroup.commutator_mono hHK hHK

set_option backward.isDefEq.respectTransparency false in
/-- The order of `(g • K)'` equals that of `K'` (conjugation is `G`-card-preserving:
`derivedInG (g • K) = (derivedInG K).map (conj g)`). -/
private theorem card_derivedInG_conj (g : G) (K : Subgroup G) :
    Nat.card ↥(derivedInG (MulAut.conj g • K)) = Nat.card ↥(derivedInG K) := by
  have hmapeq : derivedInG (MulAut.conj g • K) = MulAut.conj g • derivedInG K := by
    have e1 : derivedInG (MulAut.conj g • K)
        = ⁅(MulAut.conj g • K : Subgroup G), MulAut.conj g • K⁆ := Subgroup.map_subtype_commutator _
    have e2 : derivedInG K = ⁅(K : Subgroup G), K⁆ := Subgroup.map_subtype_commutator _
    rw [e1, e2]
    simp only [Subgroup.pointwise_smul_def]
    exact (Subgroup.map_commutator _ _ _).symm
  rw [hmapeq]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

/-- **Derived subgroup of a product**: `K = A·N` (`N ⊴ K`) ⟹ `K' ≤ A' ⊔ N`. (Replicated from
S12_Proposition1215; the d.2/P5 crux.) -/
private theorem commutator_le_commutator_sup_normal {K : Type*} [Group K]
    (A N : Subgroup K) [N.Normal] (hAN : A ⊔ N = ⊤) :
    commutator K ≤ ⁅A, A⁆ ⊔ N := by
  rw [commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  have hg₁ : (g₁ : K) ∈ (A : Set K) * (N : Set K) := by
    rw [← Subgroup.mul_normal, hAN]; exact Subgroup.mem_top _
  have hg₂ : (g₂ : K) ∈ (A : Set K) * (N : Set K) := by
    rw [← Subgroup.mul_normal, hAN]; exact Subgroup.mem_top _
  obtain ⟨a₁, ha₁, n₁, hn₁, rfl⟩ := Set.mem_mul.mp hg₁
  obtain ⟨a₂, ha₂, n₂, hn₂, rfl⟩ := Set.mem_mul.mp hg₂
  have hmod : ⁅a₁ * n₁, a₂ * n₂⁆ * ⁅a₁, a₂⁆⁻¹ ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    have hn1 : (QuotientGroup.mk' N) n₁ = 1 := (QuotientGroup.eq_one_iff n₁).mpr hn₁
    have hn2 : (QuotientGroup.mk' N) n₂ = 1 := (QuotientGroup.eq_one_iff n₂).mpr hn₂
    have e : (QuotientGroup.mk' N) (⁅a₁ * n₁, a₂ * n₂⁆ * ⁅a₁, a₂⁆⁻¹)
        = QuotientGroup.mk (⁅a₁ * n₁, a₂ * n₂⁆ * ⁅a₁, a₂⁆⁻¹) := rfl
    rw [← e, map_mul, map_inv, map_commutatorElement, map_commutatorElement, map_mul, map_mul,
      hn1, hn2, mul_one, mul_one, mul_inv_cancel]
  have hcommA : ⁅a₁, a₂⁆ ∈ ⁅A, A⁆ := Subgroup.commutator_mem_commutator ha₁ ha₂
  have heq : ⁅a₁ * n₁, a₂ * n₂⁆ = (⁅a₁ * n₁, a₂ * n₂⁆ * ⁅a₁, a₂⁆⁻¹) * ⁅a₁, a₂⁆ := by
    rw [inv_mul_cancel_right]
  rw [heq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hmod) (Subgroup.mem_sup_left hcommA)

/-- **Generic Hall lemma** (Hall E–C–D corollary): in a finite solvable group, a `π`-subgroup `Y`
is conjugate into any subgroup `H` whose index is a `π'`-number.  Indeed `H` then contains a Hall
`π`-subgroup `P` of the whole group (its index, dividing `H.index`, is `π'`), all Hall `π`-subgroups
are conjugate (`hall_C`), and `hall_D` puts `Y` inside one of them, hence inside `P^g ≤ H^g`.

Used in the general `σ(M)`-subgroup form of Cor 12.16(a) to push `Y` into the `M ∩ M*` factor. -/
private theorem exists_conj_smul_le_of_index_isPiCompl {G' : Type*} [Group G'] [Finite G']
    [Group.IsSolvable G'] {π : Set ℕ} {H Y : Subgroup G'}
    (hHidx : ∀ p ∈ H.index.primeFactors, p ∉ π)
    (hYπ : ∀ p ∈ (Nat.card ↥Y).primeFactors, p ∈ π) :
    ∃ g : G', MulAut.conj g • Y ≤ H := by
  obtain ⟨Q, hQhall, hYQ⟩ := Ch03.hall_D hYπ
  obtain ⟨Pbar, hPbar⟩ := Ch03.hall_E_exists (G := ↥H) π
  set P : Subgroup G' := Pbar.map H.subtype with hPdef
  have hPle : P ≤ H := Subgroup.map_subtype_le _
  have hPcard : Nat.card ↥P = Nat.card ↥Pbar := by
    rw [hPdef, Subgroup.card_map_of_injective H.subtype_injective]
  have hsub : P.subgroupOf H = Pbar :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hrel : P.relIndex H = Pbar.index := by rw [Subgroup.relIndex, hsub]
  have hPhall : Ch03.IsHallSubgroup π P := by
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · rw [hPcard] at hp; exact hPbar.1 p hp
    · have htower : P.relIndex H * H.index = P.index := Subgroup.relIndex_mul_index hPle
      rw [← htower] at hp
      have hne1 : P.relIndex H ≠ 0 := by rw [hrel]; exact Subgroup.index_ne_zero_of_finite
      have hne2 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      rw [Nat.primeFactors_mul hne1 hne2, Finset.mem_union] at hp
      rcases hp with h | h
      · rw [hrel] at h; exact hPbar.2 p h
      · exact hHidx p h
  obtain ⟨g, hg⟩ := Ch03.hall_C hQhall hPhall
  refine ⟨g, le_trans (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hYQ) ?_⟩
  calc MulAut.conj g • Q = Q.map (MulAut.conj g).toMonoidHom := mulAut_smul_eq_map _ _
    _ = P := hg
    _ ≤ H := hPle

/-- **Shared Case-2 setup** for 12.16(a)/(b): if `Y ⊆ M_σ` is a nonidentity `q`-group (`q ∈ σ(M)`)
with `N_G(Y) ⊄ M`, then there is a maximal `M* ⊇ N_G(Y)`, `M* ≠ M`, with the factorization
`M* = (M ∩ M*)K` (`K = M*_β`/`M*_σ` via Prop 12.15(d)/(e)), `K ⊴ M*`, and `K` a `p'`-group. -/
private theorem exists_Mstar_factorization [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {Y : Subgroup G} (hYne : Y ≠ ⊥) {q : ℕ} [Fact q.Prime] (hYq : IsPGroup q ↥Y)
    (hqσ : q ∈ S10.sigma M) (hYMσ : Y ≤ S10.Msigma M)
    {p : ℕ} [Fact p.Prime] (hpE : p ∈ (Nat.card ↥E).primeFactors) (hpβ : ¬ S10.idealPrime p G)
    (hNYM : ¬ Subgroup.normalizer (Y : Set G) ≤ M) :
    ∃ Mstar K : Subgroup G, Mstar ∈ maximalSubgroups G ∧
      Subgroup.normalizer (Y : Set G) ≤ Mstar ∧ Mstar ≠ M ∧
      Mstar = (M ⊓ Mstar) ⊔ K ∧ (K.subgroupOf Mstar).Normal ∧ ¬ p ∣ Nat.card ↥K := by
  have hM := h.mem_maximal
  have hYM_le : Y ≤ M := hYMσ.trans (S10.Msigma_le M)
  obtain ⟨Mstar, hMstar_max, hMstar_ge⟩ :=
    OddOrder.BG.Ch2.S08.exists_maximalSubgroup_containing_normalizer_of_ne_bot_le_maximal
      hG hM hYne hYM_le
  have hMstarMem : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (Y : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hMstar_max, hMstar_ge⟩
  have hMstarne : Mstar ≠ M := fun he => hNYM (he ▸ hMstar_ge)
  have hYMstar : Y ≤ Mstar := Subgroup.le_normalizer.trans hMstar_ge
  have hYMM : Y ≤ M ⊓ Mstar := le_inf hYM_le hYMstar
  have hYsub_pg : IsPGroup q ↥(Y.subgroupOf (M ⊓ Mstar)) :=
    hYq.of_equiv (Subgroup.subgroupOfEquivOfLe hYMM).symm
  obtain ⟨Psub, hPsub⟩ := hYsub_pg.exists_le_sylow
  set S : Subgroup G := (Psub : Subgroup ↥(M ⊓ Mstar)).map (M ⊓ Mstar).subtype with hSdef
  have hSle : S ≤ M ⊓ Mstar := Subgroup.map_subtype_le _
  have hSq : IsPGroup q ↥S :=
    Psub.2.of_equiv (Subgroup.equivMapOfInjective _ _ (M ⊓ Mstar).subtype_injective)
  have hYS : Y ≤ S := by
    rw [hSdef, ← Subgroup.map_subgroupOf_eq_of_le hYMM]; exact Subgroup.map_mono hPsub
  have hPsubeq : S.subgroupOf (M ⊓ Mstar) = Psub := by
    rw [hSdef]; exact Subgroup.comap_map_eq_self_of_injective (M ⊓ Mstar).subtype_injective _
  have hSmax : ∀ T : Subgroup G, T ≤ M ⊓ Mstar → IsPGroup q ↥T → S ≤ T → S = T := by
    intro T hTle hTq hST
    have hTsub_pg : IsPGroup q ↥(T.subgroupOf (M ⊓ Mstar)) :=
      hTq.of_equiv (Subgroup.subgroupOfEquivOfLe hTle).symm
    have hTeq := Psub.3 hTsub_pg (by rw [← hPsubeq]; exact Subgroup.comap_mono hST)
    rw [hSdef, ← hTeq, Subgroup.map_subgroupOf_eq_of_le hTle]
  have h1215 := sigma_subgroup_maximal_interaction hG hM hqσ hYM_le hYne hYq hMstarMem hMstarne
    hSle hYS hSq hSmax
  obtain ⟨K, hKnorm, hMstarFact, hpK⟩ :
      ∃ K : Subgroup G, (K.subgroupOf Mstar).Normal ∧ Mstar = (M ⊓ Mstar) ⊔ K ∧
        ¬ p ∣ Nat.card ↥K := by
    by_cases hqσMstar : q ∈ S10.sigma Mstar
    · refine ⟨S10.Mbeta Mstar, by rw [S10.Mbeta_subgroupOf]; infer_instance,
        (h1215.2.2.2.1 hqσMstar).1, fun hdvd => hpβ ?_⟩
      exact ((S10.mem_beta_iff Mstar p).mp (S10.Mbeta_isPiGroup Mstar p
        (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩))).2
    · refine ⟨S10.Msigma Mstar, by rw [S10.Msigma_subgroupOf]; infer_instance, ?_,
        fun hdvd => hpβ ?_⟩
      · rw [sup_comm]; exact (h1215.2.2.2.2 hqσMstar).2.2.2.symm
      · have hp_πM : p ∈ (Nat.card ↥M).primeFactors :=
          Nat.primeFactors_mono (Subgroup.card_dvd_of_le h.E_le) Nat.card_pos.ne' hpE
        have hp_σMstar : p ∈ S10.sigma Mstar := S10.Msigma_isPiGroup Mstar p
          (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩)
        exact ((S10.mem_beta_iff Mstar p).mp ((h1215.2.2.2.2 hqσMstar).2.1 p hp_πM hp_σMstar)).2
  exact ⟨Mstar, K, hMstar_max, hMstar_ge, hMstarne, hMstarFact, hKnorm, hpK⟩

/-- **Case-2 setup, σ-flavour** for the *headline* conjugacy of 12.16(a): same factorization
`M* = (M ∩ M*)K`, `K ⊴ M*`, but with `K` exhibited as a `σ(M*)`-group (`K = M*_β ⊆ M*_σ` when
`q ∈ σ(M*)`, or `K = M*_σ` when `q ∈ τ₂(M*)`).  By `σ`-disjointness `K` is then `σ(M)'`, which is
exactly what the Hall conjugation step needs — in place of the single-prime `¬p∣|K|` returned by
`exists_Mstar_factorization`.  Needs only `hM` (no `E`-setup, since no `p ∈ π(E)` is involved). -/
private theorem exists_Mstar_factorization_sigma [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {Y : Subgroup G} (hYne : Y ≠ ⊥) {q : ℕ} [Fact q.Prime] (hYq : IsPGroup q ↥Y)
    (hqσ : q ∈ S10.sigma M) (hYMσ : Y ≤ S10.Msigma M)
    (hNYM : ¬ Subgroup.normalizer (Y : Set G) ≤ M) :
    ∃ Mstar K : Subgroup G, Mstar ∈ maximalSubgroups G ∧
      Subgroup.normalizer (Y : Set G) ≤ Mstar ∧
      (¬ ∃ g : G, MulAut.conj g • M = Mstar) ∧ Mstar ≠ M ∧
      Mstar = (M ⊓ Mstar) ⊔ K ∧ (K.subgroupOf Mstar).Normal ∧
      (∀ r ∈ (Nat.card ↥K).primeFactors, r ∈ S10.sigma Mstar) := by
  have hYM_le : Y ≤ M := hYMσ.trans (S10.Msigma_le M)
  obtain ⟨Mstar, hMstar_max, hMstar_ge⟩ :=
    OddOrder.BG.Ch2.S08.exists_maximalSubgroup_containing_normalizer_of_ne_bot_le_maximal
      hG hM hYne hYM_le
  have hMstarMem : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (Y : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hMstar_max, hMstar_ge⟩
  have hMstarne : Mstar ≠ M := fun he => hNYM (he ▸ hMstar_ge)
  have hYMstar : Y ≤ Mstar := Subgroup.le_normalizer.trans hMstar_ge
  have hYMM : Y ≤ M ⊓ Mstar := le_inf hYM_le hYMstar
  have hYsub_pg : IsPGroup q ↥(Y.subgroupOf (M ⊓ Mstar)) :=
    hYq.of_equiv (Subgroup.subgroupOfEquivOfLe hYMM).symm
  obtain ⟨Psub, hPsub⟩ := hYsub_pg.exists_le_sylow
  set S : Subgroup G := (Psub : Subgroup ↥(M ⊓ Mstar)).map (M ⊓ Mstar).subtype with hSdef
  have hSle : S ≤ M ⊓ Mstar := Subgroup.map_subtype_le _
  have hSq : IsPGroup q ↥S :=
    Psub.2.of_equiv (Subgroup.equivMapOfInjective _ _ (M ⊓ Mstar).subtype_injective)
  have hYS : Y ≤ S := by
    rw [hSdef, ← Subgroup.map_subgroupOf_eq_of_le hYMM]; exact Subgroup.map_mono hPsub
  have hPsubeq : S.subgroupOf (M ⊓ Mstar) = Psub := by
    rw [hSdef]; exact Subgroup.comap_map_eq_self_of_injective (M ⊓ Mstar).subtype_injective _
  have hSmax : ∀ T : Subgroup G, T ≤ M ⊓ Mstar → IsPGroup q ↥T → S ≤ T → S = T := by
    intro T hTle hTq hST
    have hTsub_pg : IsPGroup q ↥(T.subgroupOf (M ⊓ Mstar)) :=
      hTq.of_equiv (Subgroup.subgroupOfEquivOfLe hTle).symm
    have hTeq := Psub.3 hTsub_pg (by rw [← hPsubeq]; exact Subgroup.comap_mono hST)
    rw [hSdef, ← hTeq, Subgroup.map_subgroupOf_eq_of_le hTle]
  have h1215 := sigma_subgroup_maximal_interaction hG hM hqσ hYM_le hYne hYq hMstarMem hMstarne
    hSle hYS hSq hSmax
  obtain ⟨K, hKnorm, hMstarFact, hKσ⟩ :
      ∃ K : Subgroup G, (K.subgroupOf Mstar).Normal ∧ Mstar = (M ⊓ Mstar) ⊔ K ∧
        (∀ r ∈ (Nat.card ↥K).primeFactors, r ∈ S10.sigma Mstar) := by
    by_cases hqσMstar : q ∈ S10.sigma Mstar
    · exact ⟨S10.Mbeta Mstar, by rw [S10.Mbeta_subgroupOf]; infer_instance,
        (h1215.2.2.2.1 hqσMstar).1,
        fun r hr => S10.alpha_subset_sigma hG hMstar_max
          (S10.beta_subset_alpha Mstar (S10.Mbeta_isPiGroup Mstar r hr))⟩
    · exact ⟨S10.Msigma Mstar, by rw [S10.Msigma_subgroupOf]; infer_instance,
        by rw [sup_comm]; exact (h1215.2.2.2.2 hqσMstar).2.2.2.symm,
        fun r hr => S10.Msigma_isPiGroup Mstar r hr⟩
  exact ⟨Mstar, K, hMstar_max, hMstar_ge, h1215.1, hMstarne, hMstarFact, hKnorm, hKσ⟩

/-- Conjugation inside `↥N` transports to `G` along `N.subtype` (replicated private helper;
the same statement appears in `S10_HallStructureCore` / `S12_Proposition1215`). -/
private theorem map_subtype_conj_smul {N : Subgroup G} (c : ↥N) (K : Subgroup ↥N) :
    (MulAut.conj c • K).map N.subtype = MulAut.conj (c : G) • (K.map N.subtype) := by
  have hcomp : (MulAut.conj (c : G)).toMonoidHom.comp N.subtype
      = N.subtype.comp (MulAut.conj c).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
  change (K.map (MulAut.conj c).toMonoidHom).map N.subtype
      = (K.map N.subtype).map (MulAut.conj (c : G)).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map, hcomp]

/-- **`G`-level Hall conjugation**: with `N` solvable, a `π`-subgroup `Y ≤ N` is conjugate (by an
element of `N`) into any `H ≤ N` whose relative index `[N : H]` is a `π'`-number.  Runs
`exists_conj_smul_le_of_index_isPiCompl` inside `↥N` and transports the result back via
`map_subtype_conj_smul`. -/
private theorem exists_conj_smul_le_of_relIndex_isPiCompl [Finite G]
    {N : Subgroup G} [Group.IsSolvable ↥N] {π : Set ℕ} {H Y : Subgroup G}
    (hHN : H ≤ N) (hYN : Y ≤ N)
    (hHidx : ∀ p ∈ (H.relIndex N).primeFactors, p ∉ π)
    (hYπ : ∀ p ∈ (Nat.card ↥Y).primeFactors, p ∈ π) :
    ∃ g ∈ N, MulAut.conj g • Y ≤ H := by
  have hHidx' : ∀ p ∈ (H.subgroupOf N).index.primeFactors, p ∉ π := fun p hp => hHidx p hp
  have hYπ' : ∀ p ∈ (Nat.card ↥(Y.subgroupOf N)).primeFactors, p ∈ π := by
    intro p hp
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYN).toEquiv] at hp
    exact hYπ p hp
  obtain ⟨gN, hgN⟩ := exists_conj_smul_le_of_index_isPiCompl (G' := ↥N) hHidx' hYπ'
  refine ⟨(gN : G), gN.2, ?_⟩
  have hle := Subgroup.map_mono (f := N.subtype) hgN
  rwa [map_subtype_conj_smul, Subgroup.map_subgroupOf_eq_of_le hYN,
    Subgroup.map_subgroupOf_eq_of_le hHN] at hle

/-- **`σ(M)`-prime `q`-subgroup of `G` is `G`-conjugate into `M_σ`** (BG Theorem 10.2 corollary;
`M_σ` contains a Sylow `q` of `G`, then Sylow conjugacy).  Extracted from the inline Step 1 of
`pRank_normalizer_le_one`; the headline form of 12.16(a) uses it to land its characteristic
`q`-subgroup `X` inside `M_σ`. -/
private theorem exists_conj_qSubgroup_le_Msigma [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {q : ℕ} [Fact q.Prime]
    (hqσ : q ∈ S10.sigma M) {Y : Subgroup G} (hYq : IsPGroup q ↥Y) :
    ∃ g : G, MulAut.conj g • Y ≤ S10.Msigma M := by
  obtain ⟨_, P, _⟩ := (S10.mem_sigma_iff M q).mp hqσ
  obtain ⟨SG, hSG⟩ := S10.isSylow_sylowMap_of_mem_sigma hqσ P
  have hPpi : Ch03.Subgroup.IsPiGroup (S10.sigma M) ((P : Subgroup ↥M).map M.subtype) := by
    intro s hs
    have hs_dvd : s ∣ Nat.card ↥((P : Subgroup ↥M).map M.subtype) :=
      (Nat.mem_primeFactors.mp hs).2.1
    rw [Subgroup.card_map_of_injective M.subtype_injective] at hs_dvd
    obtain ⟨n, hn⟩ := (P.2).exists_card_eq
    rw [hn] at hs_dvd
    rwa [(Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hs) Fact.out).mp
      ((Nat.prime_of_mem_primeFactors hs).dvd_of_dvd_pow hs_dvd)]
  have hPMσ : (P : Subgroup ↥M).map M.subtype ≤ S10.Msigma M :=
    S10.sigma_subgroup_le_Msigma_of_isHall (S10.Msigma_isHall hG hM)
      (Subgroup.map_subtype_le _) hPpi
  obtain ⟨Q, hYQ⟩ := hYq.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G SG Q
  refine ⟨g⁻¹, le_trans (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hYQ) ?_⟩
  have hQconj : MulAut.conj g⁻¹ • (Q : Subgroup G) = (P : Subgroup ↥M).map M.subtype := by
    have hQ : (Q : Subgroup G) = MulAut.conj g • (SG : Subgroup G) := by
      rw [← hg]; exact Sylow.coe_subgroup_smul
    rw [hQ, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul, hSG]
  rw [hQconj]; exact hPMσ

/-- **Core of 12.16(a)** with the extra hypothesis `Y ⊆ M_σ` (the conjugated setup). If
`r_p(N_H(Y)) ≥ 2`, a rank-2 `A ∈ ℰ_p²(N_H(Y))` (after moving into `M`) makes `p ∈ τ₂(M)`, and
Thm 12.5(e) gives `M_σ ∩ H* = ⊥` for a maximal `H* ⊇ A` (`≠ M`) — but `1 ⊂ Y ⊆ M_σ ∩ H*`. -/
private theorem pRank_normalizer_le_one_core [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {Y : Subgroup G} (hYne : Y ≠ ⊥) {q : ℕ} [Fact q.Prime] (hYq : IsPGroup q ↥Y)
    (hqσ : q ∈ S10.sigma M) (hYMσ : Y ≤ S10.Msigma M)
    {p : ℕ} [Fact p.Prime] (hpE : p ∈ (Nat.card ↥E).primeFactors) (hpβ : ¬ S10.idealPrime p G)
    {H : Subgroup G} (hHY : H ∈ maximalSubgroupsContaining Y)
    (hHnc : ¬ ∃ g : G, MulAut.conj g • M = H) :
    pRank ↥(H ⊓ Subgroup.normalizer (Y : Set G)) p ≤ 1 := by
  have hM := h.mem_maximal
  have hHmax := mem_maximalSubgroupsContaining.mp hHY
  have hYH : Y ≤ H := hHmax.2
  have hHM : H ≠ M := fun he => hHnc ⟨1, by rw [map_one, one_smul]; exact he.symm⟩
  have hpσ : p ∉ S10.sigma M := h.not_mem_sigma_of_mem_primeFactors hG hpE
  by_contra hge
  obtain ⟨A, hAea, hAN⟩ := exists_mem_elemAbelianOfRank_two_le_of_two_le_pRank
    (Fact.out : p.Prime) (not_le.mp hge)
  have hAH : A ≤ H := hAN.trans inf_le_left
  have hANY : A ≤ Subgroup.normalizer (Y : Set G) := hAN.trans inf_le_right
  -- **Generic contradiction**: any rank-2 `B ≤ M` inside a maximal `H* ≠ M` with `Y ≤ H*` fails —
  -- `B` makes `p ∈ τ₂(M)` (`p ∉ σ(M)` so `p ∉ α(M)`, rank `≤ 2`; `B` gives rank `≥ 2`), then Thm
  -- 12.5(e) yields `M_σ ∩ H* = ⊥`, contradicting `1 ⊂ Y ⊆ M_σ ∩ H*`.
  have hcontra : ∀ (B : Subgroup G), B ∈ elemAbelianOfRank G p 2 → B ≤ M →
      ∀ (Hstar : Subgroup G), Hstar ∈ maximalSubgroupsContaining B → Hstar ≠ M → Y ≤ Hstar →
      False := by
    intro B hBea hBM Hstar hHstar hHstarM hYHstar
    have hpτ2 : p ∈ tau2 M := by
      refine ⟨hpσ, le_antisymm ?_ ?_⟩
      · by_contra h3
        have h3' : 3 ≤ pRank ↥M p := by omega
        exact hpσ (S10.alpha_subset_sigma hG hM ((S10.mem_alpha_iff M p).mpr
          ⟨OddOrder.BG.Ch2.S09.mem_primeFactors_card_of_pos_pRank (H := ↥M) (p := p) (by omega),
            h3'⟩))
      · have hBsubM : (B.subgroupOf M).IsElementaryAbelian p :=
          IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBM).symm
            (mem_elemAbelianOfRank.mp hBea).1
        have hle := le_pRank (B.subgroupOf M) hBsubM
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv,
          (mem_elemAbelianOfRank.mp hBea).2, Nat.log_pow (Fact.out : p.Prime).one_lt] at hle
    exact hYne (le_bot_iff.mp
      ((Msigma_nilpotent_of_tau2 hG hM hpτ2 hBea hBM).2.2.2.2.1 Hstar hHstar hHstarM ▸
        le_inf hYMσ hYHstar))
  by_cases hNYM : Subgroup.normalizer (Y : Set G) ≤ M
  · -- **Case 1**: `N_G(Y) ⊆ M`, so `A ≤ N_H(Y) ⊆ M` directly; take `H* = H`, `B = A`.
    exact hcontra A hAea (hANY.trans hNYM) H
      (mem_maximalSubgroupsContaining.mpr ⟨hHmax.1, hAH⟩) hHM hYH
  · -- **Case 2** (BG L3466-3476): `N_G(Y) ⊄ M`. Use the shared `M*`-factorization, then a fresh
    -- rank-2 `B ∈ ℰ_p²(M ∩ M*)` (`pRank(M ∩ M*) = pRank(M*) ≥ 2`, coprime index) feeds `hcontra`.
    obtain ⟨Mstar, K, hMstar_max, hMstar_ge, hMstarne, hMstarFact, hKnorm, hpK⟩ :=
      exists_Mstar_factorization hG h hYne hYq hqσ hYMσ hpE hpβ hNYM
    have hKle : K ≤ Mstar := hMstarFact ▸ le_sup_right
    have hidx : ¬ p ∣ ((M ⊓ Mstar).subgroupOf Mstar).index := by
      have := hKnorm
      have htop : (M ⊓ Mstar).subgroupOf Mstar ⊔ K.subgroupOf Mstar = ⊤ := by
        rw [← Subgroup.subgroupOf_sup inf_le_right hKle, ← hMstarFact, Subgroup.subgroupOf_self]
      exact not_dvd_index_of_sup_top_normal htop
        (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv]; exact hpK)
    have hAMstar : A ≤ Mstar := hANY.trans hMstar_ge
    have hpRankMstar : 2 ≤ pRank ↥Mstar p := by
      have hAsubMstar : (A.subgroupOf Mstar).IsElementaryAbelian p :=
        IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAMstar).symm
          (mem_elemAbelianOfRank.mp hAea).1
      have hle := le_pRank (A.subgroupOf Mstar) hAsubMstar
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAMstar).toEquiv,
        (mem_elemAbelianOfRank.mp hAea).2, Nat.log_pow (Fact.out : p.Prime).one_lt] at hle
    have hpRankMM : 2 ≤ pRank ↥(M ⊓ Mstar) p := by
      rw [pRank_eq_of_le_of_not_dvd_index inf_le_right hidx]; exact hpRankMstar
    obtain ⟨B, hBea, hBMM⟩ :=
      exists_mem_elemAbelianOfRank_two_le_of_two_le_pRank (Fact.out : p.Prime) hpRankMM
    exact hcontra B hBea (hBMM.trans inf_le_left) Mstar
      (mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hMstar_max, hBMM.trans
          inf_le_right⟩)
      hMstarne (Subgroup.le_normalizer.trans hMstar_ge)

/-- **BG Corollary 12.16(a)** (mmd L3453-3456), **`q`-group specialization**: for a nonidentity
`q`-group `Y` with `q ∈ σ(M)`, `r_p(N_H(Y)) ≤ 1`. The general `σ(M)`-subgroup form
`S12.sigma_subgroup_pRank_normalizer_le_one` (below, in `namespace …S12`) reduces to this via a
characteristic `q`-subgroup `O_q(Y) ⊆ Y` (`N_G(Y) ≤ N_G(O_q(Y))`); `S13_Lemma131` cites that. -/
theorem pRank_normalizer_le_one [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {Y : Subgroup G} (hYne : Y ≠ ⊥) {q : ℕ} [Fact q.Prime] (hYq : IsPGroup q ↥Y)
    (hqσ : q ∈ S10.sigma M)
    {p : ℕ} [Fact p.Prime] (hpE : p ∈ (Nat.card ↥E).primeFactors) (hpβ : ¬ S10.idealPrime p G)
    {H : Subgroup G} (hHY : H ∈ maximalSubgroupsContaining Y)
    (hHnc : ¬ ∃ g : G, MulAut.conj g • M = H) :
    pRank ↥(H ⊓ Subgroup.normalizer (Y : Set G)) p ≤ 1 := by
  -- **Step 1 — conjugate `Y` into `M_σ`**: `Y` is a `q`-group, `q ∈ σ(M)`, and `M_σ` contains a
  -- Sylow `q` of `G` (BG 10.2), so `Y` is `G`-conjugate into `M_σ`.
  obtain ⟨g, hgY⟩ : ∃ g : G, MulAut.conj g • Y ≤ S10.Msigma M := by
    obtain ⟨_, P, _⟩ := (S10.mem_sigma_iff M q).mp hqσ
    obtain ⟨SG, hSG⟩ := S10.isSylow_sylowMap_of_mem_sigma hqσ P
    have hPpi : Ch03.Subgroup.IsPiGroup (S10.sigma M) ((P : Subgroup ↥M).map M.subtype) := by
      intro s hs
      have hs_dvd : s ∣ Nat.card ↥((P : Subgroup ↥M).map M.subtype) :=
        (Nat.mem_primeFactors.mp hs).2.1
      rw [Subgroup.card_map_of_injective M.subtype_injective] at hs_dvd
      obtain ⟨n, hn⟩ := (P.2).exists_card_eq
      rw [hn] at hs_dvd
      rwa [(Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hs) Fact.out).mp
        ((Nat.prime_of_mem_primeFactors hs).dvd_of_dvd_pow hs_dvd)]
    have hPMσ : (P : Subgroup ↥M).map M.subtype ≤ S10.Msigma M :=
      S10.sigma_subgroup_le_Msigma_of_isHall (S10.Msigma_isHall hG h.mem_maximal)
        (Subgroup.map_subtype_le _) hPpi
    obtain ⟨Q, hYQ⟩ := hYq.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G SG Q
    refine ⟨g⁻¹, le_trans (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hYQ) ?_⟩
    have hQconj : MulAut.conj g⁻¹ • (Q : Subgroup G) = (P : Subgroup ↥M).map M.subtype := by
      have hQ : (Q : Subgroup G) = MulAut.conj g • (SG : Subgroup G) := by
        rw [← hg]; exact Sylow.coe_subgroup_smul
      rw [hQ, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul, hSG]
    rw [hQconj]; exact hPMσ
  -- **Step 2**: apply the core to the conjugated setup `Y' = g•Y ⊆ M_σ`, `H' = g•H`, then transport
  -- back (rank is conjugation-invariant; `g•(H ⊓ N_G(Y)) = (g•H) ⊓ N_G(g•Y)`).
  have hY'ne : MulAut.conj g • Y ≠ ⊥ := by
    intro h
    have hc : Nat.card ↥(MulAut.conj g • Y) = Nat.card ↥Y :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    rw [h, Subgroup.card_bot] at hc
    exact hYne (Subgroup.card_eq_one.mp hc.symm)
  have hY'q : IsPGroup q ↥(MulAut.conj g • Y) :=
    hYq.of_equiv (Subgroup.equivMapOfInjective Y (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective)
  have hH'mem : MulAut.conj g • H ∈ maximalSubgroupsContaining (MulAut.conj g • Y) :=
    mem_maximalSubgroupsContaining.mpr
      ⟨isCoatom_conj_smul (mem_maximalSubgroups.mp (mem_maximalSubgroupsContaining.mp hHY).1),
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (mem_maximalSubgroupsContaining.mp hHY).2⟩
  have hH'nc : ¬ ∃ g' : G, MulAut.conj g' • M = MulAut.conj g • H := by
    rintro ⟨g', hg'⟩
    exact hHnc ⟨g⁻¹ * g', by
      rw [map_mul, mul_smul, hg', ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]⟩
  have hcore := pRank_normalizer_le_one_core hG h hY'ne hY'q hqσ hgY hpE hpβ hH'mem hH'nc
  have hnorm : MulAut.conj g • Subgroup.normalizer (Y : Set G)
      = Subgroup.normalizer ((MulAut.conj g • Y : Subgroup G) : Set G) :=
    Subgroup.map_normalizer_eq_of_bijective Y (MulAut.conj g).bijective
  have heq : pRank ↥(H ⊓ Subgroup.normalizer (Y : Set G)) p
      = pRank ↥((MulAut.conj g • H) ⊓
          Subgroup.normalizer ((MulAut.conj g • Y : Subgroup G) : Set G)) p := by
    rw [← hnorm, ← Subgroup.smul_inf]
    exact pRank_eq_of_mulEquiv (Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective)
  rw [heq]; exact hcore

/-- **Core of 12.16(b)** with `Y ⊆ M_σ`. `N := N_H(Y) ≤ M` (Case 1) or `≤ M*` (Case 2); in either
case `deriv N` lies in a `p'`-subgroup (`deriv M = M'` is `p'` by `τ₁`; or `deriv M* ≤ (M∩M*)'⊔K`,
both `p'`), so `p ∉ π(deriv N)`. -/
private theorem not_mem_primeFactors_derived_of_tau1_core [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {Y : Subgroup G} (hYne : Y ≠ ⊥) {q : ℕ} [Fact q.Prime] (hYq : IsPGroup q ↥Y)
    (hqσ : q ∈ S10.sigma M) (hYMσ : Y ≤ S10.Msigma M)
    {p : ℕ} [Fact p.Prime] (hpE : p ∈ (Nat.card ↥E).primeFactors) (hpβ : ¬ S10.idealPrime p G)
    (hpτ1 : p ∈ tau1 M)
    {H : Subgroup G} (_hHY : H ∈ maximalSubgroupsContaining Y)
    (_hHnc : ¬ ∃ g : G, MulAut.conj g • M = H) :
    p ∉ (Nat.card ↥(derivedInG (H ⊓ Subgroup.normalizer (Y : Set G)))).primeFactors := by
  have hpM' : p ∉ (Nat.card ↥(derivedInG M)).primeFactors := ((mem_tau1_iff M p).mp hpτ1).2.1
  intro hpmem
  have hp_dvd : p ∣ Nat.card ↥(derivedInG (H ⊓ Subgroup.normalizer (Y : Set G))) :=
    (Nat.mem_primeFactors.mp hpmem).2.1
  by_cases hNYM : Subgroup.normalizer (Y : Set G) ≤ M
  · -- Case 1: `N_H(Y) ≤ N_G(Y) ≤ M`, so `deriv N ≤ M'` (a `p'`-group by `τ₁`).
    exact hpM' (Nat.mem_primeFactors.mpr ⟨Fact.out, hp_dvd.trans
      (Subgroup.card_dvd_of_le (derivedInG_mono (inf_le_right.trans hNYM))), Nat.card_pos.ne'⟩)
  · -- Case 2: `M*`, `K`. `deriv N ≤ deriv M* ≤ (M∩M*)' ⊔ K`, both `p'`.
    obtain ⟨Mstar, K, hMstar_max, hMstar_ge, hMstarne, hMstarFact, hKnorm, hpK⟩ :=
      exists_Mstar_factorization hG h hYne hYq hqσ hYMσ hpE hpβ hNYM
    have hKle : K ≤ Mstar := hMstarFact ▸ le_sup_right
    have hNMstar : H ⊓ Subgroup.normalizer (Y : Set G) ≤ Mstar := inf_le_right.trans hMstar_ge
    have hpMstar' : ¬ p ∣ Nat.card ↥(derivedInG Mstar) := by
      have := hKnorm
      have hAK_top : (M ⊓ Mstar).subgroupOf Mstar ⊔ K.subgroupOf Mstar = ⊤ := by
        rw [← Subgroup.subgroupOf_sup inf_le_right hKle, ← hMstarFact, Subgroup.subgroupOf_self]
      have hcrux := commutator_le_commutator_sup_normal ((M ⊓ Mstar).subgroupOf Mstar)
        (K.subgroupOf Mstar) hAK_top
      have hpA'' : ¬ p ∣ Nat.card ↥(⁅(M ⊓ Mstar).subgroupOf Mstar,
          (M ⊓ Mstar).subgroupOf Mstar⁆ : Subgroup ↥Mstar) := by
        intro hdvd
        have hmap : (⁅(M ⊓ Mstar).subgroupOf Mstar, (M ⊓ Mstar).subgroupOf Mstar⁆ :
            Subgroup ↥Mstar).map Mstar.subtype = ⁅(M ⊓ Mstar : Subgroup G), M ⊓ Mstar⁆ := by
          rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
        have hle : (⁅(M ⊓ Mstar : Subgroup G), M ⊓ Mstar⁆) ≤ derivedInG M := by
          rw [show derivedInG M = ⁅(M : Subgroup G), M⁆ from Subgroup.map_subtype_commutator M]
          exact Subgroup.commutator_mono inf_le_left inf_le_left
        rw [← Subgroup.card_map_of_injective Mstar.subtype_injective, hmap] at hdvd
        exact hpM' (Nat.mem_primeFactors.mpr
          ⟨Fact.out, hdvd.trans (Subgroup.card_dvd_of_le hle), Nat.card_pos.ne'⟩)
      have hpK'' : ¬ p ∣ Nat.card ↥(K.subgroupOf Mstar) := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv]; exact hpK
      have hsup_dvd : Nat.card ↥(⁅(M ⊓ Mstar).subgroupOf Mstar, (M ⊓ Mstar).subgroupOf Mstar⁆ ⊔
            K.subgroupOf Mstar : Subgroup ↥Mstar)
          ∣ Nat.card ↥(⁅(M ⊓ Mstar).subgroupOf Mstar, (M ⊓ Mstar).subgroupOf Mstar⁆ :
              Subgroup ↥Mstar) * Nat.card ↥(K.subgroupOf Mstar) := by
        have hform := Subgroup.card_HK_mul_card_inf_eq_card_mul_card
          (⁅(M ⊓ Mstar).subgroupOf Mstar, (M ⊓ Mstar).subgroupOf Mstar⁆ : Subgroup ↥Mstar)
          (K.subgroupOf Mstar)
        rw [show (↑(⁅(M ⊓ Mstar).subgroupOf Mstar, (M ⊓ Mstar).subgroupOf Mstar⁆ :
              Subgroup ↥Mstar) * ↑(K.subgroupOf Mstar) : Set ↥Mstar)
            = ↑(⁅(M ⊓ Mstar).subgroupOf Mstar, (M ⊓ Mstar).subgroupOf Mstar⁆ ⊔
                K.subgroupOf Mstar : Subgroup ↥Mstar) from (Subgroup.mul_normal _ _).symm] at hform
        exact ⟨_, hform.symm⟩
      intro hdvd
      have hdvd_comm : p ∣ Nat.card ↥(commutator ↥Mstar) := by
        rwa [show derivedInG Mstar = (commutator ↥Mstar).map Mstar.subtype from rfl,
          Subgroup.card_map_of_injective Mstar.subtype_injective] at hdvd
      rcases (Nat.Prime.dvd_mul Fact.out).mp
          ((hdvd_comm.trans (Subgroup.card_dvd_of_le hcrux)).trans hsup_dvd) with hh | hh
      · exact hpA'' hh
      · exact hpK'' hh
    exact hpMstar' (hp_dvd.trans (Subgroup.card_dvd_of_le (derivedInG_mono hNMstar)))

/-- **BG Corollary 12.16(b)** (mmd L3453, 3456): `p ∈ τ₁(M)` ⟹ `p ∉ π(N_H(Y)')`. 実証明版。 -/
theorem not_mem_primeFactors_derived_of_tau1 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {Y : Subgroup G} (hYne : Y ≠ ⊥) {q : ℕ} [Fact q.Prime] (hYq : IsPGroup q ↥Y)
    (hqσ : q ∈ S10.sigma M)
    {p : ℕ} [Fact p.Prime] (hpE : p ∈ (Nat.card ↥E).primeFactors) (hpβ : ¬ S10.idealPrime p G)
    (hpτ1 : p ∈ tau1 M)
    {H : Subgroup G} (hHY : H ∈ maximalSubgroupsContaining Y)
    (hHnc : ¬ ∃ g : G, MulAut.conj g • M = H) :
    p ∉ (Nat.card ↥(derivedInG (H ⊓ Subgroup.normalizer (Y : Set G)))).primeFactors := by
  -- Step 1: conjugate `Y` into `M_σ` (same as 12.16(a)).
  obtain ⟨g, hgY⟩ : ∃ g : G, MulAut.conj g • Y ≤ S10.Msigma M := by
    obtain ⟨_, P, _⟩ := (S10.mem_sigma_iff M q).mp hqσ
    obtain ⟨SG, hSG⟩ := S10.isSylow_sylowMap_of_mem_sigma hqσ P
    have hPpi : Ch03.Subgroup.IsPiGroup (S10.sigma M) ((P : Subgroup ↥M).map M.subtype) := by
      intro s hs
      have hs_dvd : s ∣ Nat.card ↥((P : Subgroup ↥M).map M.subtype) :=
        (Nat.mem_primeFactors.mp hs).2.1
      rw [Subgroup.card_map_of_injective M.subtype_injective] at hs_dvd
      obtain ⟨n, hn⟩ := (P.2).exists_card_eq
      rw [hn] at hs_dvd
      rwa [(Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hs) Fact.out).mp
        ((Nat.prime_of_mem_primeFactors hs).dvd_of_dvd_pow hs_dvd)]
    have hPMσ : (P : Subgroup ↥M).map M.subtype ≤ S10.Msigma M :=
      S10.sigma_subgroup_le_Msigma_of_isHall (S10.Msigma_isHall hG h.mem_maximal)
        (Subgroup.map_subtype_le _) hPpi
    obtain ⟨Q, hYQ⟩ := hYq.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G SG Q
    refine ⟨g⁻¹, le_trans (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hYQ) ?_⟩
    have hQconj : MulAut.conj g⁻¹ • (Q : Subgroup G) = (P : Subgroup ↥M).map M.subtype := by
      have hQ : (Q : Subgroup G) = MulAut.conj g • (SG : Subgroup G) := by
        rw [← hg]; exact Sylow.coe_subgroup_smul
      rw [hQ, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul, hSG]
    rw [hQconj]; exact hPMσ
  -- Step 2: apply the core to `(Y' = g•Y ⊆ M_σ, H' = g•H)`, transport via
  -- `|deriv(g•K)| = |deriv K|`.
  have hY'ne : MulAut.conj g • Y ≠ ⊥ := by
    intro hb
    have hc : Nat.card ↥(MulAut.conj g • Y) = Nat.card ↥Y :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    rw [hb, Subgroup.card_bot] at hc
    exact hYne (Subgroup.card_eq_one.mp hc.symm)
  have hY'q : IsPGroup q ↥(MulAut.conj g • Y) :=
    hYq.of_equiv (Subgroup.equivMapOfInjective Y (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective)
  have hH'mem : MulAut.conj g • H ∈ maximalSubgroupsContaining (MulAut.conj g • Y) :=
    mem_maximalSubgroupsContaining.mpr
      ⟨isCoatom_conj_smul (mem_maximalSubgroups.mp (mem_maximalSubgroupsContaining.mp hHY).1),
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (mem_maximalSubgroupsContaining.mp hHY).2⟩
  have hH'nc : ¬ ∃ g' : G, MulAut.conj g' • M = MulAut.conj g • H := by
    rintro ⟨g', hg'⟩
    exact hHnc ⟨g⁻¹ * g', by
      rw [map_mul, mul_smul, hg', ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]⟩
  have hcore := not_mem_primeFactors_derived_of_tau1_core hG h hY'ne hY'q hqσ hgY hpE hpβ hpτ1
    hH'mem hH'nc
  have hnorm : MulAut.conj g • Subgroup.normalizer (Y : Set G)
      = Subgroup.normalizer ((MulAut.conj g • Y : Subgroup G) : Set G) :=
    Subgroup.map_normalizer_eq_of_bijective Y (MulAut.conj g).bijective
  have hcardeq : Nat.card ↥(derivedInG ((MulAut.conj g • H) ⊓
        Subgroup.normalizer ((MulAut.conj g • Y : Subgroup G) : Set G)))
      = Nat.card ↥(derivedInG (H ⊓ Subgroup.normalizer (Y : Set G))) := by
    rw [← hnorm, ← Subgroup.smul_inf]
    exact card_derivedInG_conj g (H ⊓ Subgroup.normalizer (Y : Set G))
  rwa [← hcardeq]

end OddOrder.BG.Ch3.S12.Cor1216

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Char `q`-subgroup reduction** for the general `σ(M)`-subgroup form of Cor 12.16: a nonidentity
`σ(M)`-subgroup `Y < ⊤` has a nonidentity characteristic `q`-subgroup `X = O_q(Y)` (`q ∈ σ(M)`)
with `N_G(Y) ≤ N_G(X)`. (`Y` solvable ⟹ `F(Y) ≠ ⊥`; `O_q(F(Y)) ≠ ⊥ ⊆ O_q(Y)` for `q ∣ |F(Y)|`;
`O_q(↥Y)` is characteristic so its normalizer contains `N_G(Y)`.) -/
private theorem exists_char_qSubgroup [Finite G] (hG : IsMinimalSimpleOdd G)
    {M Y : Subgroup G} (hYne : Y ≠ ⊥) (hYlt : Y < ⊤)
    (hYpi : Subgroup.IsPiSubgroup (S10.sigma M) Y) :
    ∃ q : ℕ, q.Prime ∧ ∃ X : Subgroup G,
      X ≤ Y ∧ X ≠ ⊥ ∧ IsPGroup q ↥X ∧ q ∈ S10.sigma M ∧
        Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (X : Set G) := by
  have : Group.IsSolvable ↥Y := hG.isSolvable_of_lt_top Y hYlt
  have : Nontrivial ↥Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hYne
  have hFcard_ne : Nat.card ↥(Ch2.S08.fittingInG Y) ≠ 1 := by
    rw [Ch2.S08.fittingInG, Subgroup.card_map_of_injective Y.subtype_injective]
    exact fun hc => Ch01.fitting_ne_bot_of_isSolvable_nontrivial ↥Y (Subgroup.card_eq_one.mp hc)
  obtain ⟨q, hq_mem⟩ : (Nat.card ↥(Ch2.S08.fittingInG Y)).primeFactors.Nonempty :=
    Nat.nonempty_primeFactors.mpr
      (lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne') (Ne.symm hFcard_ne))
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
  have : Fact q.Prime := ⟨hq_prime⟩
  have hOqFne : opiCoreInG ({q} : Set ℕ) (Ch2.S08.fittingInG Y) ≠ ⊥ :=
    Ch2.S08.opiCoreInG_singleton_fittingInG_ne_bot_of_mem_primeFactors hq_mem
  have hOqYne : opiCoreInG ({q} : Set ℕ) Y ≠ ⊥ := fun hbot =>
    hOqFne (le_bot_iff.mp (hbot ▸ Ch2.S08.opiCoreInG_fittingInG_le_opiCoreInG {q} Y))
  have hqσ : q ∈ S10.sigma M := hYpi q (Nat.mem_primeFactors.mpr
    ⟨hq_prime, (Nat.dvd_of_mem_primeFactors hq_mem).trans
      (Subgroup.card_dvd_of_le (Ch2.S08.fittingInG_le Y)), Nat.card_pos.ne'⟩)
  refine ⟨q, hq_prime, opiCoreInG ({q} : Set ℕ) Y, opiCoreInG_le _ _, hOqYne,
    isPGroup_opiCoreInG_singleton Y, hqσ, ?_⟩
  exact OddOrder.BG.AppB.normalizer_le_normalizer_map_of_characteristic
    (K := Y) (W := Ch03.oPiCore {q} ↥Y)

/-- **BG Corollary 12.16(a)** (general `σ(M)`-subgroup form, mmd L3453-3456): for a nonidentity
`σ(M)`-subgroup `Y`, every `p ∈ π(E) ∩ β(G)'`, and every `H ∈ ℳ(Y)` not conjugate to `M`,
`r_p(N_H(Y)) ≤ 1`. Reduces to the `q`-group form `Cor1216.pRank_normalizer_le_one` via a
characteristic `q`-subgroup `X ⊆ Y` (`N_G(Y) ≤ N_G(X)`, `pRank` monotone). -/
theorem sigma_subgroup_pRank_normalizer_le_one [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {Y : Subgroup G} (hYne : Y ≠ ⊥) (hYpi : Subgroup.IsPiSubgroup (S10.sigma M) Y)
    {p : ℕ} [Fact p.Prime] (hpE : p ∈ (Nat.card ↥E).primeFactors) (hpβ : ¬ S10.idealPrime p G)
    {H : Subgroup G} (hHY : H ∈ maximalSubgroupsContaining Y)
    (hHnc : ¬ ∃ g : G, MulAut.conj g • M = H) :
    pRank ↥(H ⊓ Subgroup.normalizer (Y : Set G)) p ≤ 1 := by
  have hHco : IsCoatom H := (mem_maximalSubgroupsContaining.mp hHY).1
  have hYH : Y ≤ H := (mem_maximalSubgroupsContaining.mp hHY).2
  have hYlt : Y < ⊤ := lt_of_le_of_lt hYH hHco.lt_top
  obtain ⟨q, hq_prime, X, hXY, hXne, hXq, hqσ, hNYX⟩ := exists_char_qSubgroup hG hYne hYlt hYpi
  have : Fact q.Prime := ⟨hq_prime⟩
  have hHX : H ∈ maximalSubgroupsContaining X :=
    mem_maximalSubgroupsContaining.mpr ⟨hHco, hXY.trans hYH⟩
  have hcore := Cor1216.pRank_normalizer_le_one hG h hXne hXq hqσ hpE hpβ hHX hHnc
  exact le_trans (pRank_le_of_injective
    (f := Subgroup.inclusion (inf_le_inf_left H hNYX)) (Subgroup.inclusion_injective _)) hcore

/-- **BG Corollary 12.16(b)** (general `σ(M)`-subgroup form): same setup, if `p ∈ τ₁(M)` then
`p ∉ π(N_H(Y)')`. Reduces to `Cor1216.not_mem_primeFactors_derived_of_tau1` via the same
characteristic `q`-subgroup (`derivedInG` monotone). -/
theorem sigma_subgroup_not_mem_primeFactors_derived_of_tau1 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {Y : Subgroup G} (hYne : Y ≠ ⊥) (hYpi : Subgroup.IsPiSubgroup (S10.sigma M) Y)
    {p : ℕ} [Fact p.Prime] (hpE : p ∈ (Nat.card ↥E).primeFactors) (hpβ : ¬ S10.idealPrime p G)
    (hpτ1 : p ∈ tau1 M)
    {H : Subgroup G} (hHY : H ∈ maximalSubgroupsContaining Y)
    (hHnc : ¬ ∃ g : G, MulAut.conj g • M = H) :
    p ∉ (Nat.card ↥(derivedInG (H ⊓ Subgroup.normalizer (Y : Set G)))).primeFactors := by
  have hHco : IsCoatom H := (mem_maximalSubgroupsContaining.mp hHY).1
  have hYH : Y ≤ H := (mem_maximalSubgroupsContaining.mp hHY).2
  have hYlt : Y < ⊤ := lt_of_le_of_lt hYH hHco.lt_top
  obtain ⟨q, hq_prime, X, hXY, hXne, hXq, hqσ, hNYX⟩ := exists_char_qSubgroup hG hYne hYlt hYpi
  have : Fact q.Prime := ⟨hq_prime⟩
  have hHX : H ∈ maximalSubgroupsContaining X :=
    mem_maximalSubgroupsContaining.mpr ⟨hHco, hXY.trans hYH⟩
  have hcore := Cor1216.not_mem_primeFactors_derived_of_tau1 hG h hXne hXq hqσ hpE hpβ hpτ1 hHX hHnc
  intro hp_mem
  apply hcore
  rw [Nat.mem_primeFactors] at hp_mem ⊢
  exact ⟨hp_mem.1, hp_mem.2.1.trans (Subgroup.card_dvd_of_le
    (Cor1216.derivedInG_mono (inf_le_inf_left H hNYX))), Nat.card_pos.ne'⟩

/-- **BG Corollary 12.16(a)**, *headline form* (mmd L3453, L3474): a nonidentity `σ(M)`-subgroup `Y`
of `G` is conjugate to a subgroup of `M_σ`.  This is BG's foundational `ℓ_σ ≤ 1` tool — "every
`σ(M)`-element is conjugate to an element of `M_σ`" (mmd L3801).

Proof (BG L3458-3474): take a characteristic `q`-subgroup `X ⊆ Y` (`q ∈ σ(M)`) and conjugate by
`g₀` so `X^{g₀} ⊆ M_σ`.  Since `X` is characteristic in `Y`, `N_G(Y^{g₀}) ≤ N_G(X^{g₀})`.
If `N_G(X^{g₀}) ⊆ M` then `Y^{g₀} ⊆ M`, so `Y^{g₀} ⊆ M_σ` because `M_σ` is the normal Hall
`σ(M)`-subgroup of `M`.  Otherwise `M* ∈ ℳ(N_G(X^{g₀}))` is not conjugate to `M` and Proposition
12.15 gives `M* = (M ∩ M*)K` with `K = M*_β`/`M*_σ` a `σ(M*)`-group; by `σ`-disjointness `K` is then
`σ(M)'`, so `[M* : M ∩ M*]` is a `σ(M)'`-number and `hall_D` conjugates the `σ(M)`-subgroup `Y^{g₀}`
into `M ∩ M* ⊆ M`, hence into `M_σ`.

The `σ`-disjointness input `hσdisj` (BG Cor 12.6(f) / Theorem 13.9) is taken as a hypothesis to
avoid an import cycle with §13, where the unconditional form `sigma_disjoint_of_nonconjugate` lives;
callers in §14+ discharge it directly.  `hYlt : Y < ⊤` holds automatically (a `σ(M)`-subgroup is
proper since `G` is non-solvable) and is required by the characteristic-subgroup reduction. -/
theorem sigma_subgroup_conj_into_Msigma_general [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {Y : Subgroup G} (hYne : Y ≠ ⊥) (hYlt : Y < ⊤)
    (hYpi : Subgroup.IsPiSubgroup (S10.sigma M) Y)
    (hσdisj : ∀ {Mstar : Subgroup G}, Mstar ∈ maximalSubgroups G →
      (¬ ∃ g : G, MulAut.conj g • M = Mstar) → Disjoint (S10.sigma M) (S10.sigma Mstar)) :
    ∃ g : G, MulAut.conj g • Y ≤ S10.Msigma M := by
  classical
  obtain ⟨q, hq_prime, X, hXY, hXne, hXq, hqσ, hNYX⟩ := exists_char_qSubgroup hG hYne hYlt hYpi
  have : Fact q.Prime := ⟨hq_prime⟩
  obtain ⟨g₀, hg₀X⟩ := Cor1216.exists_conj_qSubgroup_le_Msigma hG hM hqσ hXq
  -- Reduce to conjugating the already-shifted `g₀ • Y`.
  suffices h : ∃ g : G, MulAut.conj g • (MulAut.conj g₀ • Y) ≤ S10.Msigma M by
    obtain ⟨g, hg⟩ := h
    exact ⟨g * g₀, by rwa [map_mul, mul_smul]⟩
  have hX₀q : IsPGroup q ↥(MulAut.conj g₀ • X) :=
    hXq.of_equiv (Subgroup.equivMapOfInjective X (MulAut.conj g₀).toMonoidHom
      (MulAut.conj g₀).injective)
  have hX₀ne : MulAut.conj g₀ • X ≠ ⊥ := by
    intro h
    have hc : Nat.card ↥(MulAut.conj g₀ • X) = Nat.card ↥X :=
      Subgroup.card_map_of_injective (MulAut.conj g₀).injective
    rw [h, Subgroup.card_bot] at hc
    exact hXne (Subgroup.card_eq_one.mp hc.symm)
  have hY₀pi : Subgroup.IsPiSubgroup (S10.sigma M) (MulAut.conj g₀ • Y) := by
    intro p hp
    rw [mulAut_smul_eq_map, Subgroup.card_map_of_injective (MulAut.conj g₀).injective] at hp
    exact hYpi p hp
  have hNY₀X₀ : Subgroup.normalizer ((MulAut.conj g₀ • Y : Subgroup G) : Set G)
      ≤ Subgroup.normalizer ((MulAut.conj g₀ • X : Subgroup G) : Set G) := by
    have hnormY : MulAut.conj g₀ • Subgroup.normalizer (Y : Set G)
        = Subgroup.normalizer ((MulAut.conj g₀ • Y : Subgroup G) : Set G) :=
      Subgroup.map_normalizer_eq_of_bijective Y (MulAut.conj g₀).bijective
    have hnormX : MulAut.conj g₀ • Subgroup.normalizer (X : Set G)
        = Subgroup.normalizer ((MulAut.conj g₀ • X : Subgroup G) : Set G) :=
      Subgroup.map_normalizer_eq_of_bijective X (MulAut.conj g₀).bijective
    rw [← hnormY, ← hnormX]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hNYX
  by_cases hNX₀M : Subgroup.normalizer ((MulAut.conj g₀ • X : Subgroup G) : Set G) ≤ M
  · -- `N_G(X^{g₀}) ⊆ M`, so `Y^{g₀} ⊆ M`, hence `Y^{g₀} ⊆ M_σ` directly.
    refine ⟨1, ?_⟩
    rw [map_one, one_smul]
    exact S10.sigma_subgroup_le_Msigma_of_isHall (S10.Msigma_isHall hG hM)
      (le_trans (le_trans Subgroup.le_normalizer hNY₀X₀) hNX₀M) hY₀pi
  · -- `N_G(X^{g₀}) ⊄ M`: factorize `M* = (M ∩ M*)K`, then `hall_D` pushes `Y^{g₀}` into `M ∩ M*`.
    obtain ⟨Mstar, K, hMstar_max, hMstar_ge, hnc, hMstarne, hMstarFact, hKnorm, hKσ⟩ :=
      Cor1216.exists_Mstar_factorization_sigma hG hM hX₀ne hX₀q hqσ hg₀X hNX₀M
    have hY₀Mstar : MulAut.conj g₀ • Y ≤ Mstar :=
      le_trans (le_trans Subgroup.le_normalizer hNY₀X₀) hMstar_ge
    have : Group.IsSolvable ↥Mstar := hG.isSolvable_of_mem_maximalSubgroups hMstar_max
    have hidx : ∀ p ∈ ((M ⊓ Mstar).relIndex Mstar).primeFactors, p ∉ S10.sigma M := by
      intro p hp hpσM
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hp_dvd : p ∣ ((M ⊓ Mstar).subgroupOf Mstar).index := Nat.dvd_of_mem_primeFactors hp
      have hpσMstar : p ∉ S10.sigma Mstar := fun hh =>
        Set.disjoint_left.mp (hσdisj hMstar_max hnc) hpσM hh
      have hpK : ¬ p ∣ Nat.card ↥K := fun hdvd =>
        hpσMstar (hKσ p (Nat.mem_primeFactors.mpr ⟨hp_prime, hdvd, Nat.card_pos.ne'⟩))
      have hKle : K ≤ Mstar := hMstarFact ▸ le_sup_right
      have := hKnorm
      have htop : (M ⊓ Mstar).subgroupOf Mstar ⊔ K.subgroupOf Mstar = ⊤ := by
        rw [← Subgroup.subgroupOf_sup inf_le_right hKle, ← hMstarFact, Subgroup.subgroupOf_self]
      exact Cor1216.not_dvd_index_of_sup_top_normal htop
        (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv]; exact hpK) hp_dvd
    obtain ⟨g, _, hg⟩ := Cor1216.exists_conj_smul_le_of_relIndex_isPiCompl
      inf_le_right hY₀Mstar hidx hY₀pi
    refine ⟨g, ?_⟩
    have hgπ : Subgroup.IsPiSubgroup (S10.sigma M) (MulAut.conj g • (MulAut.conj g₀ • Y)) := by
      intro p hp
      rw [mulAut_smul_eq_map, Subgroup.card_map_of_injective (MulAut.conj g).injective] at hp
      exact hY₀pi p hp
    exact S10.sigma_subgroup_le_Msigma_of_isHall (S10.Msigma_isHall hG hM)
      (le_trans hg inf_le_left) hgπ

end OddOrder.BG.Ch3.S12


