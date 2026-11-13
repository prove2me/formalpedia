-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Proposition1215
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S12_Proposition1215
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T08:13:25.322463+00:00
-- url     : https://prove2.me/theorems/e656295d-e922-4c03-8ac1-957e3c988884
-- title:
--   BG §12: Proposition 12.15, interaction of $\sigma(M)$-subgroups and maximal subgroups
-- statement:
--   Formalizes Proposition 12.15 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §12: for $q\in\sigma(M)$, a nontrivial $q$-subgroup $X$ of $M$, $M^*\in\mathcal{M}(N_G(X))-\{M\}$ and a Sylow $q$-subgroup $S$ of $M\cap M^*$ containing $X$: (a) $M^*$ is not conjugate to $M$ in $G$; (b) $N_G(S)\subseteq M$; (c) $S$ is a Sylow $q$-subgroup of $M^*$; and further clauses.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 9 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S12_Proposition1215.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S12_Proposition1215.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Theorem125
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Corollary126
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Corollary1210
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Lemma1211
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Theorem1213
import Definitions.Def_OddOrder_GroupTheory_CyclicSubgroupUniqueness

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- **p-group normalizer condition packaged for BG 12.15(b)/(c)**: if `T'` is a finite `q`-group,
`S ≤ T'`, and `S = T' ⊓ N_G(S)` (i.e. `S` is self-normalizing in `T'`), then `S = T'`. Indeed
`↥T'` is nilpotent, so its normalizer condition forces the self-normalizing `S.subgroupOf T'` to
be `⊤`. -/
private theorem eq_of_isPGroup_of_normalizer_inf_eq [Finite G] {q : ℕ} [Fact q.Prime]
    {S T' : Subgroup G} (hT'q : IsPGroup q ↥T') (hST' : S ≤ T')
    (hS_eq : S = T' ⊓ Subgroup.normalizer (S : Set G)) : S = T' := by
  have : Group.IsNilpotent ↥T' := hT'q.isNilpotent
  have hfix :
      Subgroup.normalizer ((S.subgroupOf T' : Subgroup ↥T') : Set ↥T') = S.subgroupOf T' := by
    rw [← Subgroup.subgroupOf_normalizer_eq hST']
    nth_rewrite 2 [hS_eq]
    rw [Subgroup.inf_subgroupOf_left]
  have htop : S.subgroupOf T' = ⊤ :=
    normalizerCondition_iff_only_full_group_self_normalizing.mp
      Group.normalizerCondition_of_isNilpotent _ hfix
  rw [Subgroup.subgroupOf_eq_top] at htop
  exact le_antisymm hST' htop

/-- `p`-rank is invariant under group isomorphism. (Replicated from the reusable helper in
`S13_Lemma131`, which is in a sibling lane's file and not importable here.) -/
private theorem pRank_eq_of_mulEquiv {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    {p : ℕ} (e : A ≃* B) : pRank A p = pRank B p :=
  le_antisymm (pRank_le_of_injective (f := e.toMonoidHom) e.injective)
    (pRank_le_of_injective (f := e.symm.toMonoidHom) e.symm.injective)

/-- A subgroup `H` with `q`-rank `≥ 2` contains a rank-2 elementary abelian `q`-subgroup of `G`.
Generalizes `exists_mem_elemAbelianOfRank_two_le_of_tau2` (S12_Lemma1211) from a `τ₂`-hypothesis to
the underlying `2 ≤ pRank ↥H q`. (De-private: cited by `S15` for the type-`P` `τ₂` component of
BG Lemma 15.1(e), to obtain a rank-2 elementary abelian inside `Sylow_p(U)`.) -/
theorem exists_mem_elemAbelianOfRank_two_le_of_two_le_pRank [Finite G] {H : Subgroup G}
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

/-- Conjugation by `c ∈ M` commutes with `M.subtype`. (Replicated from the private helpers in
S10_HallStructureCore / S12_Lemma1211; used for the Sylow-conjugacy transport in 12.15(e).2.) -/
private theorem map_subtype_conj_smul {M : Subgroup G} (c : ↥M) (K : Subgroup ↥M) :
    (MulAut.conj c • K).map M.subtype = MulAut.conj (c : G) • (K.map M.subtype) := by
  have hcomp : (MulAut.conj (c : G)).toMonoidHom.comp M.subtype
      = M.subtype.comp (MulAut.conj c).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
  change (K.map (MulAut.conj c).toMonoidHom).map M.subtype
      = (K.map M.subtype).map (MulAut.conj (c : G)).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map, hcomp]

/-- **Derived subgroup of a product** (the d.2 crux): if `K = A·N` with `N ⊴ K`, then
`K' ≤ A' · N`. (In `K⧸N`, the image of `A` is everything, so `(K⧸N)' = image of A'`; pulling
back gives `K' ≤ A'N`.) -/
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
  -- `⁅a₁n₁, a₂n₂⁆ · ⁅a₁,a₂⁆⁻¹ ∈ N` (mod `N`, the `nᵢ` vanish so the commutators agree).
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

/-- If `A ⊔ N = ⊤` in `K'` with `N ⊴ K'`, then `[K':A]` divides `|N|`; in particular `r ∤ |N|`
forces `r ∤ [K':A]`. (Second-isomorphism diamond: `|K'| = |A⊔N| ∣ |A|·|N|`, cancel `|A|`.) -/
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

/-- Build a `SubgroupESetup` from *any* `M_σ`-complement `E` in `M`. This is the Hall-piece
assembly of `S12_Lemma1211.exists_subgroupESetup` (L129-213), factored to accept a prescribed
complement `E` — so `exists_subgroupESetup_with_le` below can choose `E ⊇` a given σ'-subgroup
(via `Ch03.hall_D`). Replicated here (rather than refactoring the shared `exists_subgroupESetup`)
to keep the §12 spine untouched.  De-privatized for cross-file use (BG §14 Lemma 14.11 builds the
E-setup on a *given* complement to keep the `Q ⊄ F(E)` hypothesis on the nose). -/
theorem subgroupESetup_of_complement [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E : Subgroup G} (hM : M ∈ maximalSubgroups G) (hE_le : E ≤ M)
    (hcompl_inf : S10.Msigma M ⊓ E = ⊥) (hcompl_sup : S10.Msigma M ⊔ E = M) :
    ∃ E₁ E₂ E₃ : Subgroup G, SubgroupESetup M E E₁ E₂ E₃ := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have : Group.IsSolvable ↥E :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hE_le)
  obtain ⟨K₀, hK₀⟩ := Ch03.hall_E_exists (G := ↥E) (tau1 M ∪ tau2 M)
  have : Group.IsSolvable ↥K₀ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (le_top (a := K₀)))
  obtain ⟨H₁, hH₁⟩ := Ch03.hall_E_exists (G := ↥K₀) (tau1 M)
  obtain ⟨H₂, hH₂⟩ := Ch03.hall_E_exists (G := ↥K₀) (tau2 M)
  obtain ⟨H₃, hH₃⟩ := Ch03.hall_E_exists (G := ↥E) (tau3 M)
  have hsupH : H₁ ⊔ H₂ = (⊤ : Subgroup ↥K₀) := by
    apply Ch03.sup_eq_top_of_coprime_index
    apply coprime_of_forall_prime_not_dvd
    intro r hr_prime hr1 hr2
    have hπK : ∀ s : ℕ, s.Prime → s ∣ Nat.card ↥K₀ → s ∈ tau1 M ∪ tau2 M := by
      intro s hs_prime hs_dvd
      exact hK₀.1 s (Nat.mem_primeFactors.mpr ⟨hs_prime, hs_dvd, Nat.card_pos.ne'⟩)
    have hr1' : r ∈ tau1 M ∪ tau2 M :=
      hπK r hr_prime (hr1.trans (Subgroup.index_dvd_card H₁))
    have hr1'' : r ∉ tau1 M := fun hmem =>
      hH₁.2 r (Nat.mem_primeFactors.mpr ⟨hr_prime, hr1,
        Subgroup.index_ne_zero_of_finite⟩) hmem
    have hr2'' : r ∉ tau2 M := fun hmem =>
      hH₂.2 r (Nat.mem_primeFactors.mpr ⟨hr_prime, hr2,
        Subgroup.index_ne_zero_of_finite⟩) hmem
    rcases hr1' with h | h
    · exact hr1'' h
    · exact hr2'' h
  set E₁ : Subgroup G := (H₁.map K₀.subtype).map E.subtype with hE₁def
  set E₂ : Subgroup G := (H₂.map K₀.subtype).map E.subtype with hE₂def
  set E₃ : Subgroup G := H₃.map E.subtype with hE₃def
  refine ⟨E₁, E₂, E₃, ?_⟩
  have hE₁_subOf : E₁.subgroupOf E = H₁.map K₀.subtype := by
    rw [hE₁def, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective E.subtype_injective]
  have hE₂_subOf : E₂.subgroupOf E = H₂.map K₀.subtype := by
    rw [hE₂def, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective E.subtype_injective]
  have hE₃_subOf : E₃.subgroupOf E = H₃ := by
    rw [hE₃def, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective E.subtype_injective]
  have hH₁K : Ch03.IsHallSubgroup (tau1 M) ((H₁.map K₀.subtype).subgroupOf K₀) := by
    rwa [Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective K₀.subtype_injective]
  have hH₂K : Ch03.IsHallSubgroup (tau2 M) ((H₂.map K₀.subtype).subgroupOf K₀) := by
    rwa [Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective K₀.subtype_injective]
  have hsup12 : (E₁ ⊔ E₂).subgroupOf E = K₀ := by
    have h1 : E₁ ⊔ E₂ = ((H₁ ⊔ H₂).map K₀.subtype).map E.subtype := by
      rw [hE₁def, hE₂def, ← Subgroup.map_sup, ← Subgroup.map_sup]
    rw [h1, hsupH]
    have h2 : ((⊤ : Subgroup ↥K₀).map K₀.subtype) = K₀ := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [h2, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective E.subtype_injective]
  exact
    { mem_maximal := hM
      E_le := hE_le
      E_compl_inf := hcompl_inf
      E_compl_sup := hcompl_sup
      E₁_le := Subgroup.map_subtype_le _
      E₂_le := Subgroup.map_subtype_le _
      E₃_le := Subgroup.map_subtype_le _
      E₁_hall := by
        rw [hE₁_subOf]
        exact isHallSubgroup_of_isHallSubgroup_of_le Set.subset_union_left hK₀
          (Subgroup.map_subtype_le _) hH₁K
      E₂_hall := by
        rw [hE₂_subOf]
        exact isHallSubgroup_of_isHallSubgroup_of_le Set.subset_union_right hK₀
          (Subgroup.map_subtype_le _) hH₂K
      E₃_hall := by
        rw [hE₃_subOf]
        exact hH₃
      E₁₂_hall := by
        rw [hsup12]
        exact hK₀ }

/-- **`SubgroupESetup` with a prescribed σ'-subgroup inside `E`**: for a `σ(M)'`-subgroup `A ≤ M`,
there is a setup whose complement `E` contains `A`. (`Ch03.hall_D`: `A.subgroupOf M` lies in some
Hall `σ(M)'`-subgroup `H` of `↥M`, which is an `M_σ`-complement; feed it to
`subgroupESetup_of_complement`.) This is the missing piece for BG 12.15(e), where the rank-2 `A`
must lie in *both* `M` (for `N_G(A) ⊆ M`) and the `M_σ`-complement (for Cor 12.6).

Made public (2026-06-15, Lane H): BG §14 Proposition 14.2 needs it for the "choose `E ⊇ K`"
WLOG step, where `K` is a Hall `κ(M)`-subgroup (a `σ(M)'`-subgroup since `κ ⊆ τ₁ ∪ τ₃`). -/
theorem exists_subgroupESetup_with_le [Finite G] (hG : IsMinimalSimpleOdd G)
    {M A : Subgroup G} (hM : M ∈ maximalSubgroups G) (hAM : A ≤ M)
    (hA_pi : Subgroup.IsPiSubgroup ((S10.sigma M)ᶜ) A) :
    ∃ E E₁ E₂ E₃ : Subgroup G,
      SubgroupESetup M E E₁ E₂ E₃ ∧ A ≤ E ∧ Subgroup.IsPiSubgroup ((S10.sigma M)ᶜ) E := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  -- `A.subgroupOf M` is a `σ(M)'`-subgroup of `↥M`.
  have hU : ∀ q ∈ (Nat.card ↥(A.subgroupOf M)).primeFactors, q ∈ (S10.sigma M)ᶜ := by
    intro q hq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv] at hq
    exact hA_pi q hq
  -- Hall's theorem (D): `A.subgroupOf M` lies in a Hall `σ(M)'`-subgroup `H` of `↥M`.
  obtain ⟨H, hH_hall, hAH⟩ := Ch03.hall_D (G := ↥M) (π := (S10.sigma M)ᶜ) hU
  set E : Subgroup G := H.map M.subtype with hEdef
  have hE_le : E ≤ M := Subgroup.map_subtype_le _
  have hAE : A ≤ E := by
    rw [hEdef, ← Subgroup.map_subgroupOf_eq_of_le hAM]
    exact Subgroup.map_mono hAH
  -- `H` is an `M_σ`-complement: σ-Hall `N := M_σ.subgroupOf M` and σ'-Hall `H` are coprime/comp.
  set N : Subgroup ↥M := (S10.Msigma M).subgroupOf M with hNdef
  have hN_hall : Ch03.IsHallSubgroup (S10.sigma M) N := S10.Msigma_subgroupOf_isHall hG hM
  have hNcard : Nat.card ↥N = Nat.card ↥(S10.Msigma M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (S10.Msigma_le M)).toEquiv
  have hEH : Nat.card ↥E = Nat.card ↥H := by
    rw [hEdef]; exact Subgroup.card_map_of_injective M.subtype_injective
  -- prime sets: `M_σ` is a σ-group, `E = H.map` is a σ'-group.
  have hMσ_primes : ∀ p ∈ (Nat.card ↥(S10.Msigma M)).primeFactors, p ∈ S10.sigma M := by
    intro p hp
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (S10.Msigma_le M)).toEquiv] at hp
    exact (S10.Msigma_subgroupOf_isHall hG hM).primeFactors_card_subset p hp
  have hE_primes : ∀ p ∈ (Nat.card ↥E).primeFactors, p ∉ S10.sigma M := by
    intro p hp
    rw [hEdef, Subgroup.card_map_of_injective M.subtype_injective] at hp
    exact hH_hall.primeFactors_card_subset p hp
  have hcop : Nat.Coprime (Nat.card ↥(S10.Msigma M)) (Nat.card ↥E) :=
    Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl Nat.card_pos.ne' Nat.card_pos.ne'
      hMσ_primes hE_primes
  have hcompl_inf : S10.Msigma M ⊓ E = ⊥ := by
    have h1 : Nat.card ↥(S10.Msigma M ⊓ E) ∣ Nat.card ↥(S10.Msigma M) :=
      Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(S10.Msigma M ⊓ E) ∣ Nat.card ↥E :=
      Subgroup.card_dvd_of_le inf_le_right
    exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h1 h2))
  -- `|H| = N.index` (σ'/σ index-parts coprime ⟹ dvd-antisymm) ⟹ `|M_σ| * |E| = |M|`.
  have hcop_idx : Nat.Coprime N.index H.index :=
    Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl (π := (S10.sigma M)ᶜ)
      Subgroup.index_ne_zero_of_finite Subgroup.index_ne_zero_of_finite
      (fun p hp => hN_hall.2 p hp) (fun p hp => hH_hall.2 p hp)
  have hc2 : Nat.Coprime (Nat.card ↥N) (Nat.card ↥H) :=
    Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl (π := S10.sigma M)
      Nat.card_pos.ne' Nat.card_pos.ne'
      (fun p hp => hN_hall.primeFactors_card_subset p hp)
      (fun p hp => hH_hall.primeFactors_card_subset p hp)
  have hHidx : Nat.card ↥H = N.index := by
    refine Nat.dvd_antisymm ?_ ?_
    · exact hc2.symm.dvd_of_dvd_mul_left
        ((Subgroup.card_mul_index N).symm ▸ Subgroup.card_subgroup_dvd_card H)
    · exact hcop_idx.dvd_of_dvd_mul_right
        ((Subgroup.card_mul_index H).symm ▸ Subgroup.index_dvd_card N)
  have hprodM : Nat.card ↥(S10.Msigma M) * Nat.card ↥E = Nat.card ↥M := by
    rw [← hNcard, hEH, hHidx]; exact Subgroup.card_mul_index N
  have hcompl_sup : S10.Msigma M ⊔ E = M := by
    have hle : S10.Msigma M ⊔ E ≤ M := sup_le (S10.Msigma_le M) hE_le
    have hdvdProd : Nat.card ↥(S10.Msigma M) * Nat.card ↥E ∣ Nat.card ↥(S10.Msigma M ⊔ E) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop (Subgroup.card_dvd_of_le le_sup_left)
        (Subgroup.card_dvd_of_le le_sup_right)
    have hcardEq : Nat.card ↥(S10.Msigma M ⊔ E) = Nat.card ↥M :=
      Nat.dvd_antisymm (Subgroup.card_dvd_of_le hle) (hprodM ▸ hdvdProd)
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardEq.symm)
  obtain ⟨E₁, E₂, E₃, hsetup⟩ := subgroupESetup_of_complement hG hM hE_le hcompl_inf hcompl_sup
  exact ⟨E, E₁, E₂, E₃, hsetup, hAE, hE_primes⟩

/-- **BG Proposition 12.15** (mmd L3417): `q ∈ σ(M)`, `X` を `M` の非自明 `q`-部分群、
`M* ∈ ℳ(N_G(X)) - {M}`、`S` を `X` を含む `M ∩ M*` の Sylow `q`-部分群とすると
(a) `M*` は `M` と非共役; (b) `N_G(S) ⊆ M`; (c) `S` は `M*` の Sylow `q`;
(d) `q ∈ σ(M*)` なら `M*=(M∩M*)M*_β`, `τ₁(M*)⊆τ₁(M)∪α(M)`, `M_β=M_α≠1`;
(e) `q ∉ σ(M*)` なら `q ∈ τ₂(M*)`, `π(M)∩σ(M*)⊆β(M*)`, `M∩M*` は `M*_σ` の補群。 -/
theorem sigma_subgroup_maximal_interaction [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {q : ℕ} [Fact q.Prime]
    (hq : q ∈ S10.sigma M) {X : Subgroup G} (hXM : X ≤ M) (hXne : X ≠ ⊥) (hXq : IsPGroup q ↥X)
    {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G)))
    (hMstarne : Mstar ≠ M) {S : Subgroup G} (hSle : S ≤ M ⊓ Mstar) (hXS : X ≤ S)
    (hSq : IsPGroup q ↥S)
    (hSmax : ∀ T : Subgroup G, T ≤ M ⊓ Mstar → IsPGroup q ↥T → S ≤ T → S = T) :
    (¬ ∃ g : G, MulAut.conj g • M = Mstar) ∧
    Subgroup.normalizer (S : Set G) ≤ M ∧
    (∀ T : Subgroup G, T ≤ Mstar → IsPGroup q ↥T → S ≤ T → S = T) ∧
    (q ∈ S10.sigma Mstar →
      Mstar = (M ⊓ Mstar) ⊔ S10.Mbeta Mstar ∧
      (∀ r : ℕ, r.Prime → r ∈ tau1 Mstar → r ∈ tau1 M ∪ S10.alpha M) ∧
      S10.Mbeta M = S10.Malpha M ∧ S10.Malpha M ≠ ⊥) ∧
    (q ∉ S10.sigma Mstar →
      q ∈ tau2 Mstar ∧
      (∀ r ∈ (Nat.card ↥M).primeFactors, r ∈ S10.sigma Mstar → r ∈ S10.beta Mstar) ∧
      S10.Msigma Mstar ⊓ (M ⊓ Mstar) = ⊥ ∧ S10.Msigma Mstar ⊔ (M ⊓ Mstar) = Mstar) := by
  -- `N_G(X) ≤ M*` from `M* ∈ ℳ(N_G(X))`.
  have hNXMstar : Subgroup.normalizer (X : Set G) ≤ Mstar :=
    (mem_maximalSubgroupsContaining.mp hMstar).2
  -- (a) `M*` is not conjugate to `M` — Lemma 12.2(b) applied to the σ(M)-subgroup `X`.
  have ha : ¬ ∃ g : G, MulAut.conj g • M = Mstar :=
    not_conj_of_mem_sigma_of_normalizer_le hG hM hq hXM hXne hXq hNXMstar hMstarne
  have hSM : S ≤ M := hSle.trans inf_le_left
  have hSMstar : S ≤ Mstar := hSle.trans inf_le_right
  -- (b) `N_G(S) ⊆ M` (BG L3425: `S` noncyclic → Cor 12.10(d); `S` cyclic → `S = T` Sylow of `M`).
  have hb : Subgroup.normalizer (S : Set G) ≤ M := by
    by_cases hScyc : IsCyclic ↥S
    · -- `S` cyclic (BG L3425).
      have hScyc' : IsCyclic ↥S := hScyc
      -- Step (1): `X` char `S` (cyclic ⟹ unique subgroup per order) ⟹ `N_G(S) ≤ N_G(X) ≤ M*`.
      have hXcharS : (X.subgroupOf S).Characteristic := by
        rw [Subgroup.characteristic_iff_map_eq]
        intro φ
        exact cyclic_subgroup_eq_of_card_eq
          (Nat.card_congr (Subgroup.equivMapOfInjective _ (φ : ↥S →* ↥S) φ.injective).toEquiv).symm
      have hNS_NX : Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (X : Set G) := by
        have h := OddOrder.BG.AppB.normalizer_le_normalizer_map_of_characteristic
          (K := S) (W := X.subgroupOf S)
        rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXS] at h
      have hNS_Mstar : Subgroup.normalizer (S : Set G) ≤ Mstar := hNS_NX.trans hNXMstar
      -- Step (2): `T := Syl_q(M) ⊇ S`.
      have hSpM : IsPGroup q ↥(S.subgroupOf M) :=
        hSq.of_equiv (Subgroup.subgroupOfEquivOfLe hSM).symm
      obtain ⟨P, hSP⟩ := hSpM.exists_le_sylow
      set T : Subgroup G := (P : Subgroup ↥M).map M.subtype with hTdef
      have hTM : T ≤ M := Subgroup.map_subtype_le _
      have hST : S ≤ T := by
        rw [hTdef, ← Subgroup.map_subgroupOf_eq_of_le hSM]
        exact Subgroup.map_mono hSP
      have hTq : IsPGroup q ↥T :=
        P.isPGroup'.of_equiv (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective)
      -- `N_T(S) := T ⊓ N_G(S) ⊆ M ⊓ M*`, `S ≤ N_T(S)`, `IsPGroup q (N_T(S))` ⟹ `hSmax`:
      -- `S = N_T(S)`.
      have hS_eq_NTS : S = T ⊓ Subgroup.normalizer (S : Set G) :=
        hSmax _ (le_inf (inf_le_left.trans hTM) (inf_le_right.trans hNS_Mstar))
          (hTq.to_le inf_le_left) (le_inf hST Subgroup.le_normalizer)
      -- p-group normalizer condition on `↥T` (q-group ⟹ nilpotent): `S = T`.
      have hST_eq : S = T := eq_of_isPGroup_of_normalizer_inf_eq hTq hST hS_eq_NTS
      -- Step (3): `S = T = P.map`, `q ∈ σ(M)` ⟹ `N_G(S) ⊆ M` (de-privated per-Sylow σ-normalizer).
      rw [hST_eq, hTdef]
      exact S10.normalizer_sylow_map_le_of_mem_sigma hq P
    · -- `S` noncyclic: Corollary 12.10(d).
      obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := exists_subgroupESetup hG hM
      exact (nilpotent_sigmaComplement_abelian hG hsetup).2.2.2.1 q hq S hSM hSq hScyc
  -- (c) `S` is a Sylow `q`-subgroup of `M*` (BG L3425, from (b)): for a `q`-subgroup `T' ≤ M*`
  -- with `S ≤ T'`, `N_{T'}(S) = T' ⊓ N_G(S) ⊆ M ⊓ M*` (⊆M via (b); ⊆M* via `T' ≤ M*`) is a
  -- `q`-subgroup `⊇ S` ⟹ `hSmax` gives `S = T' ⊓ N_G(S)`, so `S = T'` by the normalizer condition.
  have hc : ∀ T : Subgroup G, T ≤ Mstar → IsPGroup q ↥T → S ≤ T → S = T := by
    intro T' hT'Mstar hT'q hST'
    refine eq_of_isPGroup_of_normalizer_inf_eq hT'q hST' ?_
    exact hSmax _ (le_inf (inf_le_right.trans hb) (inf_le_left.trans hT'Mstar))
      (hT'q.to_le inf_le_left) (le_inf hST' Subgroup.le_normalizer)
  -- (d) `q ∈ σ(M*)` branch (BG L3443-3451): `N_G(S) ⊆ M*` (from (b)+(c), as `q ∈ σ(M*)`) ⟹ `S` is
  --   a Sylow `q` of `G`. Cor 10.9(b)
  -- (`S10.beta_factorization_of_sylow_normalizer_in_intersection`):
  --   `M=(M∩M*)·M_α`, `α(M)=β(M)`, symmetrically for `M*` ⟹ `M*=(M∩M*)M*_β` [d.1], `M_β=M_α≠1`
  -- [d.3].
  --   `τ₁(M*)⊆τ₁(M)∪α(M)` [d.2]: `r∈τ₁(M*)`, `R=Syl_r(M∩M*)` Sylow `r` of `M*=(M∩M*)M*_α` w/ normal
  --   complement ⟹ if `r∉α(M)` same for `M=(M∩M*)M_α`.
  have hd : q ∈ S10.sigma Mstar →
      Mstar = (M ⊓ Mstar) ⊔ S10.Mbeta Mstar ∧
      (∀ r : ℕ, r.Prime → r ∈ tau1 Mstar → r ∈ tau1 M ∪ S10.alpha M) ∧
      S10.Mbeta M = S10.Malpha M ∧ S10.Malpha M ≠ ⊥ := by
    intro hqs
    have hMstarmax : Mstar ∈ maximalSubgroups G := (mem_maximalSubgroupsContaining.mp hMstar).1
    have hSMstar : S ≤ Mstar := hSle.trans inf_le_right
    -- Realize `S` as a Sylow `q` of `G`: extend `S.subgroupOf M*` to a Sylow of `↥M*`, map to `G`
    -- (`isSylow_sylowMap_of_mem_sigma`), and identify with `S` by maximality (c).
    have hSsubMstar_pg : IsPGroup q ↥(S.subgroupOf Mstar) :=
      hSq.of_equiv (Subgroup.subgroupOfEquivOfLe hSMstar).symm
    obtain ⟨Psub, hPsub⟩ := hSsubMstar_pg.exists_le_sylow
    obtain ⟨SG, hSG⟩ := S10.isSylow_sylowMap_of_mem_sigma hqs Psub
    have hS_le_SG : S ≤ (SG : Subgroup G) := by
      rw [hSG, ← Subgroup.map_subgroupOf_eq_of_le hSMstar]; exact Subgroup.map_mono hPsub
    have hSG_le_Mstar : (SG : Subgroup G) ≤ Mstar := by rw [hSG]; exact Subgroup.map_subtype_le _
    have hS_eq_SG : S = (SG : Subgroup G) := hc _ hSG_le_Mstar SG.2 hS_le_SG
    -- `N_G(SG) = N_G(S) ⊆ M ⊓ M*` (⊆M* via `q ∈ σ(M*)`; ⊆M via (b)).
    have hN_SG : Subgroup.normalizer ((SG : Subgroup G) : Set G) ≤ M ⊓ Mstar := by
      refine le_inf (hS_eq_SG ▸ hb) ?_
      rw [hSG]; exact S10.normalizer_sylow_map_le_of_mem_sigma hqs Psub
    -- Cor 10.9(b) for the pair `(M*, M)` gives d.1; for `(M, M*)` gives `α(M)=β(M)` ⟹ d.3a.
    have h109_star := S10.beta_factorization_of_sylow_normalizer_in_intersection hG hMstarmax hM
      hMstarne.symm SG hN_SG
    have h109_M := S10.beta_factorization_of_sylow_normalizer_in_intersection hG hM hMstarmax
      hMstarne SG (by rw [inf_comm]; exact hN_SG)
    refine ⟨h109_star.1, ?_, by simp only [S10.Malpha, S10.Mbeta, h109_M.2],
      Malpha_ne_bot_of_sylow_normalizer_le hG hM hMstarmax hMstarne.symm SG hN_SG⟩
    -- d.2: `τ₁(M*) ⊆ τ₁(M) ∪ α(M)` (Sylow-`r` normal-complement transfer through `M∩M*`).
    -- Prime-guarded (BG's `τ₁ ⊆ π(M)` = primes; the repo's `pRank`-based `tau1` is over all `ℕ`,
    -- so we restrict to the BG-faithful prime case where the Sylow argument applies).
    intro r hr_prime hr_mem
    obtain ⟨hr_σMs, hr_πMs, hr_pRankMs⟩ := hr_mem
    have : Fact r.Prime := ⟨hr_prime⟩
    by_cases hrα : r ∈ S10.alpha M
    · exact Or.inr hrα
    · -- `r ∉ α(M) = β(M)`, so `r ∤ |M_β|`.
      have hr_βM : r ∉ S10.beta M := h109_M.2 ▸ hrα
      -- **P5**: `r ∉ π(M')`. Work in `↥M`: `M = (M∩M*)·M_β` with `M_β ⊴ M`, so by the crux
      -- `(↥M)' ≤ ⁅A',A'⁆ ⊔ N'` (`A'=(M∩M*)⁻, N'=M_β⁻`); `r ∤ |⁅A',A'⁆|` (≤ `M*'`) and `r ∤ |N'|`.
      have hπM' : r ∉ (Nat.card ↥(derivedInG M)).primeFactors := by
        intro hr_mem
        have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr_mem
        set A' := (M ⊓ Mstar).subgroupOf M with hA'def
        set N' := (S10.Mbeta M).subgroupOf M with hN'def
        have hN'norm : N'.Normal := by
          rw [hN'def, S10.Mbeta_subgroupOf]; infer_instance
        have hsup_eq : M ⊓ Mstar ⊔ S10.Mbeta M = M := by rw [inf_comm]; exact h109_M.1.symm
        have hAN_top : A' ⊔ N' = ⊤ := by
          rw [hA'def, hN'def, ← Subgroup.subgroupOf_sup inf_le_left (S10.Mbeta_le M), hsup_eq,
            Subgroup.subgroupOf_self]
        have hcrux := commutator_le_commutator_sup_normal A' N' hAN_top
        -- `r ∤ |⁅A',A'⁆|`: map to `G` gives `⁅M∩M*,M∩M*⁆ ≤ ⁅M*,M*⁆ = (M*)'`.
        have hmapA' : (⁅A', A'⁆ : Subgroup ↥M).map M.subtype
            = (⁅(M ⊓ Mstar : Subgroup G), M ⊓ Mstar⁆ : Subgroup G) := by
          rw [Subgroup.map_commutator, hA'def, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
        have hcardA' : Nat.card ↥(⁅A', A'⁆ : Subgroup ↥M)
            = Nat.card ↥(⁅(M ⊓ Mstar : Subgroup G), M ⊓ Mstar⁆ : Subgroup G) := by
          rw [← hmapA', Subgroup.card_map_of_injective M.subtype_injective]
        have hdMs : derivedInG Mstar = (⁅(Mstar : Subgroup G), Mstar⁆ : Subgroup G) :=
          Subgroup.map_subtype_commutator Mstar
        have hr_A' : ¬ r ∣ Nat.card ↥(⁅A', A'⁆ : Subgroup ↥M) := by
          rw [hcardA']
          intro hdvd
          have hle : (⁅(M ⊓ Mstar : Subgroup G), M ⊓ Mstar⁆ : Subgroup G) ≤ derivedInG Mstar := by
            rw [hdMs]; exact Subgroup.commutator_mono inf_le_right inf_le_right
          exact hr_πMs (Nat.mem_primeFactors.mpr
            ⟨hr_prime, hdvd.trans (Subgroup.card_dvd_of_le hle), Nat.card_pos.ne'⟩)
        -- `r ∤ |N'| = |M_β|` (`M_β` is a `β(M)`-group, `r ∉ β(M)`).
        have hcardN' : Nat.card ↥N' = Nat.card ↥(S10.Mbeta M) := by
          rw [hN'def]
          exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (S10.Mbeta_le M)).toEquiv
        have hr_N' : ¬ r ∣ Nat.card ↥N' := by
          rw [hcardN']
          intro hdvd
          exact hr_βM (S10.Mbeta_isPiGroup M r (Nat.mem_primeFactors.mpr
            ⟨hr_prime, hdvd, Nat.card_pos.ne'⟩))
        -- `|⁅A',A'⁆ ⊔ N'| ∣ |⁅A',A'⁆| · |N'|` (`N'` normal), so `r ∤ |⁅A',A'⁆ ⊔ N'|`.
        have hsup_dvd : Nat.card ↥(⁅A', A'⁆ ⊔ N' : Subgroup ↥M)
            ∣ Nat.card ↥(⁅A', A'⁆ : Subgroup ↥M) * Nat.card ↥N' := by
          have hform := Subgroup.card_HK_mul_card_inf_eq_card_mul_card (⁅A', A'⁆ : Subgroup ↥M) N'
          rw [show (↑(⁅A', A'⁆ : Subgroup ↥M) * ↑N' : Set ↥M)
              = ↑(⁅A', A'⁆ ⊔ N' : Subgroup ↥M) from
              (Subgroup.mul_normal (⁅A', A'⁆ : Subgroup ↥M) N').symm] at hform
          exact ⟨_, hform.symm⟩
        have hr_dvd_deriv : r ∣ Nat.card ↥(derivedInG M) := (Nat.mem_primeFactors.mp hr_mem).2.1
        have hr_dvd_comm : r ∣ Nat.card ↥(commutator ↥M) := by
          rwa [show derivedInG M = (commutator ↥M).map M.subtype from rfl,
            Subgroup.card_map_of_injective M.subtype_injective] at hr_dvd_deriv
        have hr_dvd_sup : r ∣ Nat.card ↥(⁅A', A'⁆ ⊔ N' : Subgroup ↥M) :=
          hr_dvd_comm.trans (Subgroup.card_dvd_of_le hcrux)
        rcases (Nat.Prime.dvd_mul hr_prime).mp (hr_dvd_sup.trans hsup_dvd) with h | h
        · exact hr_A' h
        · exact hr_N' h
      -- **P6**: `r ∉ σ(M)` (if `r ∈ σ(M)`, then `r ∣ |M_σ|` and `M_σ ≤ M'`, contra P5).
      have hσM : r ∉ S10.sigma M := by
        intro hr_σM
        obtain ⟨hr_πM, P, _⟩ := (S10.mem_sigma_iff M r).mp hr_σM
        have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr_πM
        have : Fact r.Prime := ⟨hr_prime⟩
        -- `P.map` is an `r`-group `≤ M`, hence a `σ(M)`-subgroup; so `P.map ≤ M_σ`.
        have hP_pi : Ch03.Subgroup.IsPiGroup (S10.sigma M) ((P : Subgroup ↥M).map M.subtype) := by
          intro s hs
          have hs_prime : s.Prime := Nat.prime_of_mem_primeFactors hs
          have hs_dvd : s ∣ Nat.card ↥((P : Subgroup ↥M).map M.subtype) :=
            (Nat.mem_primeFactors.mp hs).2.1
          rw [Subgroup.card_map_of_injective M.subtype_injective] at hs_dvd
          obtain ⟨n, hn⟩ := (P.2).exists_card_eq
          rw [hn] at hs_dvd
          rw [(Nat.prime_dvd_prime_iff_eq hs_prime hr_prime).mp (hs_prime.dvd_of_dvd_pow hs_dvd)]
          exact hr_σM
        have hP_le_Mσ : (P : Subgroup ↥M).map M.subtype ≤ S10.Msigma M :=
          S10.sigma_subgroup_le_Msigma_of_isHall (S10.Msigma_isHall hG hM)
            (Subgroup.map_subtype_le _) hP_pi
        have hr_dvd_P : r ∣ Nat.card ↥((P : Subgroup ↥M).map M.subtype) := by
          rw [Subgroup.card_map_of_injective M.subtype_injective]
          exact P.dvd_card_of_dvd_card (Nat.mem_primeFactors.mp hr_πM).2.1
        exact hπM' (Nat.mem_primeFactors.mpr ⟨hr_prime,
          (hr_dvd_P.trans (Subgroup.card_dvd_of_le hP_le_Mσ)).trans
            (Subgroup.card_dvd_of_le (S10.Msigma_le_derived hG hM)), Nat.card_pos.ne'⟩)
      refine Or.inl ⟨hσM, hπM', ?_⟩
      -- **P3/P4**: `pRank M r = 1` via the shared Sylow `R = Syl_r(M∩M*) = Syl_r(M) = Syl_r(M*)`:
      -- `r ∤ [M:M∩M*]` and `r ∤ [M*:M∩M*]` (the `M_β`/`M*_β` diamonds), so `R` is Sylow `r` of both
      -- `M` and `M*`, whence `pRank M r = pRank (M∩M*) r = pRank M* r = 1`.
      have hr_αMs : r ∉ S10.alpha Mstar := fun h => by
        have := ((S10.mem_alpha_iff Mstar r).mp h).2; omega
      have hr_βMs : r ∉ S10.beta Mstar := h109_star.2 ▸ hr_αMs
      have hidxM : ¬ r ∣ ((M ⊓ Mstar).subgroupOf M).index := by
        have : ((S10.Mbeta M).subgroupOf M).Normal := by rw [S10.Mbeta_subgroupOf]; infer_instance
        refine not_dvd_index_of_sup_top_normal (N := (S10.Mbeta M).subgroupOf M) ?_ ?_
        · rw [← Subgroup.subgroupOf_sup inf_le_left (S10.Mbeta_le M),
            (by rw [inf_comm]; exact h109_M.1.symm : M ⊓ Mstar ⊔ S10.Mbeta M = M),
            Subgroup.subgroupOf_self]
        · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (S10.Mbeta_le M)).toEquiv]
          exact fun h => hr_βM (S10.Mbeta_isPiGroup M r
            (Nat.mem_primeFactors.mpr ⟨hr_prime, h, Nat.card_pos.ne'⟩))
      have hidxMs : ¬ r ∣ ((M ⊓ Mstar).subgroupOf Mstar).index := by
        have : ((S10.Mbeta Mstar).subgroupOf Mstar).Normal := by
          rw [S10.Mbeta_subgroupOf]; infer_instance
        refine not_dvd_index_of_sup_top_normal (N := (S10.Mbeta Mstar).subgroupOf Mstar) ?_ ?_
        · rw [← Subgroup.subgroupOf_sup inf_le_right (S10.Mbeta_le Mstar),
            (h109_star.1.symm : M ⊓ Mstar ⊔ S10.Mbeta Mstar = Mstar), Subgroup.subgroupOf_self]
        · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (S10.Mbeta_le Mstar)).toEquiv]
          exact fun h => hr_βMs (S10.Mbeta_isPiGroup Mstar r
            (Nat.mem_primeFactors.mpr ⟨hr_prime, h, Nat.card_pos.ne'⟩))
      rw [← pRank_eq_of_le_of_not_dvd_index inf_le_left hidxM,
        pRank_eq_of_le_of_not_dvd_index inf_le_right hidxMs]
      exact hr_pRankMs
  -- (e) `q ∉ σ(M*)` branch (BG L3429-3441): Lemma 12.2(a) (`S10`/`prime_mem_sigma_or_tau2`) gives
  --   `q ∈ σ(M*)∪τ₂(M*)`; `N_G(S) ⊄ M*` ⟹ `q ∈ τ₂(M*)` [e.1]. `A∈ℰ²(S)`, `E* := ` complement of
  --   `M*_σ` in `M*` with `A ≤ E*`. Thm 12.5(e) + Cor 12.6(a): `M*_σ∩M=1`, `A ⊴ E*`. Cor 12.10(d):
  --   `E*⊆N_G(A)⊆M` ⟹ `M∩M*=E*` = complement of `M*_σ` [e.3]. `π(M)∩σ(M*)⊆β(M*)` [e.2]: else
  --   `p∈π(M)∩σ(M*)−β(M*)`, `C_G(A)⊆E*` (Cor 12.6(b)) is `p'` ⟹ Cor 10.9(a) `p>q ∧ q>p` 矛盾.
  have he : q ∉ S10.sigma Mstar →
      q ∈ tau2 Mstar ∧
      (∀ r ∈ (Nat.card ↥M).primeFactors, r ∈ S10.sigma Mstar → r ∈ S10.beta Mstar) ∧
      S10.Msigma Mstar ⊓ (M ⊓ Mstar) = ⊥ ∧ S10.Msigma Mstar ⊔ (M ⊓ Mstar) = Mstar := by
    intro hqns
    -- e.1: `q ∈ τ₂(M*)` from Lemma 12.2(a) (`q ∈ σ(M*) ∪ τ₂(M*)`) and `q ∉ σ(M*)`.
    have he1 : q ∈ tau2 Mstar :=
      (prime_mem_sigma_or_tau2 hG hM hXM hXne hXq hMstar).resolve_left hqns
    have hMstarmax : Mstar ∈ maximalSubgroups G := (mem_maximalSubgroupsContaining.mp hMstar).1
    have hSMstar : S ≤ Mstar := hSle.trans inf_le_right
    -- Build `A ∈ ℰ²(S)` (so `A ≤ M` and `A ≤ M*`): `S` is a Sylow `q` of `↥M*` (from (c)), of
    -- `pRank 2` (`q ∈ τ₂(M*)`), hence contains a rank-2 elementary abelian.
    have hSsubMstar_pg : IsPGroup q ↥(S.subgroupOf Mstar) :=
      hSq.of_equiv (Subgroup.subgroupOfEquivOfLe hSMstar).symm
    let SsylMstar : Sylow q ↥Mstar :=
      { toSubgroup := S.subgroupOf Mstar
        isPGroup' := hSsubMstar_pg
        is_maximal' := by
          intro Q hQpg hSQ
          have hTpg : IsPGroup q ↥(Q.map Mstar.subtype) :=
            hQpg.of_equiv (Subgroup.equivMapOfInjective _ _ Mstar.subtype_injective)
          have hST : S ≤ Q.map Mstar.subtype := by
            rw [← Subgroup.map_subgroupOf_eq_of_le hSMstar]; exact Subgroup.map_mono hSQ
          have hSeqT : S = Q.map Mstar.subtype := hc _ (Subgroup.map_subtype_le _) hTpg hST
          rw [show Q = (Q.map Mstar.subtype).subgroupOf Mstar from
            (Subgroup.comap_map_eq_self_of_injective Mstar.subtype_injective Q).symm, ← hSeqT] }
    have hpRankS : 2 ≤ pRank ↥S q := by
      have key : pRank ↥S q = pRank ↥Mstar q := by
        rw [← pRank_eq_of_mulEquiv (p := q) (Subgroup.subgroupOfEquivOfLe hSMstar)]
        exact pRank_sylow_eq SsylMstar
      exact (key.trans (tau2_pRank_eq_two he1)).ge
    obtain ⟨A, hA_mem, hA_le_S⟩ :=
      exists_mem_elemAbelianOfRank_two_le_of_two_le_pRank (Fact.out : q.Prime) hpRankS
    have hA_le_M : A ≤ M := hA_le_S.trans (hSle.trans inf_le_left)
    have hA_le_Mstar : A ≤ Mstar := hA_le_S.trans hSMstar
    -- Shared (e.2/e.3): `M*_σ ⊓ M = ⊥` (12.5(e) conjunct-5), and a setup with `E* ⊇ A`, `E* ⊆ M`.
    have hMsM : S10.Msigma Mstar ⊓ M = ⊥ :=
      (Msigma_nilpotent_of_tau2 hG hMstarmax he1 hA_mem hA_le_Mstar).2.2.2.2.1 M
        (mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hM, hA_le_M⟩) hMstarne.symm
    have hA_ea : A.IsElementaryAbelian q := (mem_elemAbelianOfRank.mp hA_mem).1
    have hA_card : Nat.card ↥A = q ^ 2 := (mem_elemAbelianOfRank.mp hA_mem).2
    have hA_pi : Subgroup.IsPiSubgroup ((S10.sigma Mstar)ᶜ) A := by
      intro p hp
      rw [hA_card, Nat.primeFactors_prime_pow (by norm_num) (Fact.out : q.Prime),
        Finset.mem_singleton] at hp
      rw [hp]; exact tau2_subset_sigma_compl Mstar he1
    obtain ⟨Es, Es1, Es2, Es3, hsetupS, hAEs, hEs_pi⟩ :=
      exists_subgroupESetup_with_le hG hMstarmax hA_le_Mstar hA_pi
    -- `N_G(A) ⊆ M` (Cor 12.10(d): `q ∈ σ(M)`, `A` noncyclic), so `E* ⊆ N_G(A) ⊆ M`.
    have hNAM : Subgroup.normalizer (A : Set G) ≤ M := by
      obtain ⟨EM, EM1, EM2, EM3, hsetupM⟩ := exists_subgroupESetup hG hM
      exact (nilpotent_sigmaComplement_abelian hG hsetupM).2.2.2.1 q hq A hA_le_M hA_ea.isPGroup
        (IsElementaryAbelian.not_isCyclic_of_card_prime_sq Fact.out hA_ea hA_card)
    have hEsM : Es ≤ M :=
      (elemAb_normal_in_E_of_tau2 hG hsetupS he1 hA_mem hAEs).1.1.trans hNAM
    -- `M ∩ M* = E*` (Dedekind for the normal `M*_σ` + `M*_σ ⊓ M = ⊥`).
    have hMM : M ⊓ Mstar = Es := by
      refine le_antisymm (fun x hx => ?_) (le_inf hEsM hsetupS.E_le)
      obtain ⟨hxM, hxMstar⟩ := Subgroup.mem_inf.mp hx
      have : ((S10.Msigma Mstar).subgroupOf Mstar).Normal := by
        rw [S10.Msigma_subgroupOf]; infer_instance
      have hsub : (⟨x, hxMstar⟩ : ↥Mstar) ∈
          (S10.Msigma Mstar).subgroupOf Mstar ⊔ Es.subgroupOf Mstar := by
        rw [← Subgroup.subgroupOf_sup (S10.Msigma_le Mstar) hsetupS.E_le, hsetupS.E_compl_sup]
        exact Subgroup.mem_subgroupOf.mpr hxMstar
      have hsub' : (⟨x, hxMstar⟩ : ↥Mstar) ∈
          ((S10.Msigma Mstar).subgroupOf Mstar : Set ↥Mstar) *
            (Es.subgroupOf Mstar : Set ↥Mstar) := by
        rw [← Subgroup.normal_mul]; exact hsub
      obtain ⟨s, hs, a, ha, hsa⟩ := hsub'
      have hseq : (s : ↥Mstar) = ⟨x, hxMstar⟩ * a⁻¹ := by rw [← hsa]; group
      have hsM : (s : G) ∈ M := by
        have hcoe : (s : G) = x * ((a : ↥Mstar) : G)⁻¹ := by rw [hseq]; rfl
        rw [hcoe]
        exact M.mul_mem hxM (M.inv_mem (hEsM (Subgroup.mem_subgroupOf.mp ha)))
      have hsbot : (s : G) ∈ S10.Msigma Mstar ⊓ M := ⟨Subgroup.mem_subgroupOf.mp hs, hsM⟩
      rw [hMsM, Subgroup.mem_bot] at hsbot
      have hxa : (⟨x, hxMstar⟩ : ↥Mstar) = a := by
        rw [← hsa, show s = 1 from Subtype.ext hsbot]; exact one_mul a
      have hxeq : x = (a : G) := congrArg Subtype.val hxa
      rw [hxeq]; exact Subgroup.mem_subgroupOf.mp ha
    refine ⟨he1, ?_, ?_, ?_⟩
    · -- e.2: `r∈π(M)∩σ(M*) ⟹ r∈β(M*)`. 反証: `r∉β(M*)` 仮定 → Cor 10.9(a) で `r>q ∧ q>r` 矛盾。
      -- 構造 (BG L3433-3441): `r∈σ(M*)−β(M*)`, `q∈τ₂(M*)⟹q∉σ(M*)`; `q∈σ(M)−β(M)` (12.1g+12.6f),
      --   `r∈π(M)−σ(M)` (σ(M)∩σ(M*)=∅)。`C_G(A)⊆E*` (12.6b)、`E*` は `r'`-group (r∈σM*) ⟹ C_G(A) `r'`.
      -- **Fact 1 (clear, ⟹ r>q)**: A は Syl_r(M*_σ) を中心化しない (中心化 S ⟹ S≤C_G(A)⊆E* `r'`、
      --   だが S は Syl_r かつ r∣|M*_σ| ⟹ S≠1 矛盾)。`beta_complement_centralizes` (10.9(a)(1),
      --   `S10_BetaRadical:241`) の対偶: X=A,(r,q),hcase=`r<q` ⟹ A centralizes Syl_r(M*_σ) 矛盾 ⟹
      -- ¬(r<q)⟹r>q.
      -- **Fact 2 (✅ cracked, ⟹ q>r)**: `beta_complement_centralizes` を M 側に p₀=q, q₀=r, X=Syl_r(M)
      --   で対偶適用: Syl_r(M) が Syl_q(M_σ) を中心化しない ⟹ ¬(Syl_r(M)⊆M' ∨ q<r) ⟹ q>r。
      --   「Syl_r(M) は Syl_q(M_σ) を中心化しない」: q∈σ(M) ⟹ Syl_q(M_σ)=Syl_q(M)=Syl_q(G) (full), 全 M-共役。
      --   もし P:=Syl_r(M) が Q:=Syl_q(M_σ) を中心化 ⟹ A (q-群≤M) を m∈M で Q に共役で入れ (A≤m•Q),
      --   m⁻¹•P ⊆ C_G(A) (P centralizes Q ⟹ m⁻¹•P centralizes m⁻¹•Q⊇A), C_G(A) `r'` ⟹ m⁻¹•P=1 ⟹ P=1
      -- 矛盾。
      intro r hr_piM hr_sigmaMstar
      by_contra hr_notbeta
      have : Fact r.Prime := ⟨Nat.prime_of_mem_primeFactors hr_piM⟩
      have hr_ne_q : r ≠ q := fun h => hqns (h ▸ hr_sigmaMstar)
      -- `r ∉ σ(M)` (σ(M) disjoint σ(M*) by 12.6(f), via `elemAb_normal_in_E_of_tau2` last
      -- conjunct).
      have hr_notSigmaM : r ∉ S10.sigma M := by
        have hdisj := ((elemAb_normal_in_E_of_tau2 hG hsetupS he1 hA_mem hAEs).2.2.2.2.2 M
          (mem_maximalSubgroups.mp hM) (not_conj_symm ha)).2
        exact Set.disjoint_left.mp hdisj hr_sigmaMstar
      -- β-conditions: `r ∉ β(M)` (`r∉σ⟹∉α⟹∉β`); `q ∉ β(M*)` (`q∈τ₂⟹rank 2⟹∉α⟹∉β`).
      have hr_notBetaM : r ∉ S10.beta M := fun hr_beta =>
        hr_notSigmaM (S10.alpha_subset_sigma hG hM (S10.beta_subset_alpha M hr_beta))
      have hq_notBetaMstar : q ∉ S10.beta Mstar := fun hq_beta => by
        have h3 := (S10.beta_subset_alpha Mstar hq_beta).2
        rw [tau2_pRank_eq_two he1] at h3; omega
      -- `C_G(A)` is an `r'`-group (`C_G(A) ⊆ E*` (12.6(b)), `E*` is `σ(M*)'`, `r ∈ σ(M*)`).
      have hCAr : r ∉ (Nat.card ↥(Subgroup.centralizer (A : Set G))).primeFactors := by
        intro hr_in
        have hCE : Subgroup.centralizer (A : Set G) ≤ Es :=
          (centralizer_le_E_of_tau2 hG hsetupS he1 hA_mem hAEs).1
        have hr_dvd : r ∣ Nat.card ↥Es :=
          (Nat.mem_primeFactors.mp hr_in).2.1.trans (Subgroup.card_dvd_of_le hCE)
        exact hEs_pi r (Nat.mem_primeFactors.mpr
          ⟨(Nat.mem_primeFactors.mp hr_in).1, hr_dvd, Nat.card_pos.ne'⟩) hr_sigmaMstar
      -- `r ∣ |M*_σ|` (`r ∈ σ(M*)`, `M*_σ` is the σ-Hall).
      have hr_dvd_Msigma : r ∣ Nat.card ↥(S10.Msigma Mstar) := by
        have hN := S10.Msigma_subgroupOf_isHall hG hMstarmax
        have hr_dvd_Mstar : r ∣ Nat.card ↥Mstar := (Nat.mem_primeFactors.mp hr_sigmaMstar.1).2.1
        have hr_not_idx : ¬ r ∣ ((S10.Msigma Mstar).subgroupOf Mstar).index := fun hd =>
          hN.2 r (Nat.mem_primeFactors.mpr ⟨Fact.out, hd, Subgroup.index_ne_zero_of_finite⟩)
            hr_sigmaMstar
        have hmul := Subgroup.card_mul_index ((S10.Msigma Mstar).subgroupOf Mstar)
        have hr_dvd_sub : r ∣ Nat.card ↥((S10.Msigma Mstar).subgroupOf Mstar) := by
          rcases (Nat.Prime.dvd_mul Fact.out).mp (hmul.symm ▸ hr_dvd_Mstar) with h | h
          · exact h
          · exact absurd h hr_not_idx
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (S10.Msigma_le Mstar)).toEquiv]
          at hr_dvd_sub
      -- More shared facts for Fact 2: `q ∉ β(M)` (12.1(g): `q ∈ τ₂(M*) ⟹ ¬idealPrime q`),
      -- `A` is a `σ(M)`-subgroup, hence `A ≤ M_σ` (normal σ-Hall absorbs σ-subgroups).
      have hq_notBetaM : q ∉ S10.beta M := fun hq_beta =>
        (isMaximalElementaryAbelian_of_mem_tau2 hG hMstarmax Fact.out he1 hA_le_Mstar hA_mem).2
          hq_beta.2
      have hA_sigma : Subgroup.IsPiSubgroup (S10.sigma M) A := by
        intro p hp
        rw [hA_card, Nat.primeFactors_prime_pow (by norm_num) (Fact.out : q.Prime),
          Finset.mem_singleton] at hp
        rw [hp]; exact hq
      have hA_Msigma : A ≤ S10.Msigma M :=
        S10.sigma_subgroup_le_Msigma_of_isHall (S10.Msigma_isHall hG hM) hA_le_M hA_sigma
      -- **Fact 1**: `r > q`. Else `r < q`, and Cor 10.9(a)(1) (M*, X=A) gives `A` centralizes a
      -- Sylow `r` of `M*_σ` — but it is an `r`-group `≤ C_G(A)` (`r'`), so `= 1`, contradicting
      -- `r ∣ |M*_σ|`.
      have hrq : q < r := by
        by_contra hle
        rw [not_lt] at hle
        obtain ⟨S, hAS⟩ := (S10.beta_complement_centralizes hG hMstarmax hr_ne_q hr_notbeta
          hq_notBetaMstar hA_le_Mstar hA_ea.isPGroup (Or.inr (lt_of_le_of_ne hle hr_ne_q))).1
        set Sm : Subgroup G := (S : Subgroup ↥(S10.Msigma Mstar)).map (S10.Msigma Mstar).subtype
          with hSmdef
        have hSmC : Sm ≤ Subgroup.centralizer (A : Set G) := Subgroup.le_centralizer_iff.mp hAS
        -- `r ∣ |S|` (Sylow `r` of `M*_σ`, `r ∣ |M*_σ|`), so `r ∣ |Sm| ∣ |C_G(A)|` — contra `hCAr`.
        have hrSm : r ∣ Nat.card ↥Sm := by
          rw [hSmdef, Subgroup.card_map_of_injective (S10.Msigma Mstar).subtype_injective]
          exact S.dvd_card_of_dvd_card hr_dvd_Msigma
        exact hCAr (Nat.mem_primeFactors.mpr
          ⟨Fact.out, hrSm.trans (Subgroup.card_dvd_of_le hSmC), Nat.card_pos.ne'⟩)
      -- **Fact 2**: `r < q`. Else `q < r`, and Cor 10.9(a)(1) (M, X=Syl_r(M)) makes `Syl_r(M)`
      -- centralize a Syl_q `Q` of `M_σ`; conjugating `A` (≤ M_σ) into that Sylow puts a conjugate
      -- of
      -- `Syl_r(M)` inside `C_G(A)` (`r'`), forcing `Syl_r(M) = 1` — impossible (`r ∈ π(M)`).
      have hqr : r < q := by
        by_contra hle
        rw [not_lt] at hle
        obtain ⟨Pr⟩ := (inferInstance : Nonempty (Sylow r ↥M))
        set Prm : Subgroup G := (Pr : Subgroup ↥M).map M.subtype with hPrmdef
        have hPrm_pg : IsPGroup r ↥Prm :=
          Pr.2.of_equiv (Subgroup.equivMapOfInjective _ _ M.subtype_injective)
        obtain ⟨Q, hPrQ⟩ := (S10.beta_complement_centralizes hG hM (Ne.symm hr_ne_q) hq_notBetaM
          hr_notBetaM (Subgroup.map_subtype_le _) hPrm_pg
            (Or.inr (lt_of_le_of_ne hle (Ne.symm hr_ne_q)))).1
        -- `A ≤ M_σ` lies in some Sylow `q` `T` of `↥M_σ`; `T` is `M_σ`-conjugate to `Q`.
        have hAsub_pg : IsPGroup q ↥(A.subgroupOf (S10.Msigma M)) :=
          hA_ea.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hA_Msigma).symm
        obtain ⟨T, hAT⟩ := hAsub_pg.exists_le_sylow
        obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥(S10.Msigma M)) Q T
        -- `A ≤ (↑g) • Q.map` (map the inclusion `A.subgroupOf M_σ ≤ T = g•Q`).
        have hA_le_conj : A ≤ MulAut.conj ((S10.Msigma M).subtype g) •
            ((Q : Subgroup ↥(S10.Msigma M)).map (S10.Msigma M).subtype) := by
          have h1 : A ≤ (T : Subgroup ↥(S10.Msigma M)).map (S10.Msigma M).subtype := by
            rw [← Subgroup.map_subgroupOf_eq_of_le hA_Msigma]; exact Subgroup.map_mono hAT
          have hTQ : (T : Subgroup ↥(S10.Msigma M))
              = MulAut.conj g • (Q : Subgroup ↥(S10.Msigma M)) := by
            rw [← hg]; exact Sylow.coe_subgroup_smul
          rwa [hTQ, map_subtype_conj_smul] at h1
        -- `(↑g)•Prm ≤ C_G(A)` (`r'`-group), so `(↑g)•Prm = 1`, hence `Prm = 1` — but `r ∈ π(M)`.
        have hconjPrm : MulAut.conj ((S10.Msigma M).subtype g) • Prm
            ≤ Subgroup.centralizer (A : Set G) := by
          calc MulAut.conj ((S10.Msigma M).subtype g) • Prm
              ≤ MulAut.conj ((S10.Msigma M).subtype g) •
                  Subgroup.centralizer (((Q : Subgroup ↥(S10.Msigma M)).map
                    (S10.Msigma M).subtype : Subgroup G) : Set G) :=
                Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hPrQ
            _ = Subgroup.centralizer ((MulAut.conj ((S10.Msigma M).subtype g) •
                  ((Q : Subgroup ↥(S10.Msigma M)).map
                    (S10.Msigma M).subtype) : Subgroup G) : Set G) :=
                centralizer_conj_smul _ _
            _ ≤ Subgroup.centralizer (A : Set G) := Subgroup.centralizer_le hA_le_conj
        -- `r ∣ |Prm|` (Sylow `r` of `M`, `r ∈ π(M)`); conjugation preserves card; so
        -- `r ∣ |C_G(A)|`, contra.
        have hr_dvd_Prm : r ∣ Nat.card ↥Prm := by
          rw [hPrmdef, Subgroup.card_map_of_injective M.subtype_injective]
          exact Pr.dvd_card_of_dvd_card (Nat.mem_primeFactors.mp hr_piM).2.1
        have hr_dvd_conj : r ∣ Nat.card ↥(MulAut.conj ((S10.Msigma M).subtype g) • Prm) := by
          have hcard : Nat.card ↥(MulAut.conj ((S10.Msigma M).subtype g) • Prm) = Nat.card ↥Prm :=
            Subgroup.card_map_of_injective (MulAut.conj ((S10.Msigma M).subtype g)).injective
          rw [hcard]; exact hr_dvd_Prm
        exact hCAr (Nat.mem_primeFactors.mpr
          ⟨Fact.out, hr_dvd_conj.trans (Subgroup.card_dvd_of_le hconjPrm), Nat.card_pos.ne'⟩)
      exact absurd hrq (not_lt.mpr hqr.le)
    · -- e.3a: `M*_σ ⊓ (M∩M*) ≤ M*_σ ⊓ M = ⊥`.
      exact le_bot_iff.mp ((inf_le_inf_left _ inf_le_left).trans (le_of_eq hMsM))
    · -- e.3b: `M*_σ ⊔ (M∩M*) = M*_σ ⊔ E* = M*`.
      rw [hMM]; exact hsetupS.E_compl_sup
  exact ⟨ha, hb, hc, hd, he⟩

end OddOrder.BG.Ch3.S12


