-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Lemma1211
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S12_Lemma1211
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:59:49.500978+00:00
-- url     : https://prove2.me/theorems/4ec717b5-d3f8-469b-acf4-e03352a9ccad
-- title:
--   BG §12: Lemma 12.11, transfer of $\tau_2$ to $M^*\in\mathcal{M}(N_G(A))$
-- statement:
--   Formalizes Lemma 12.11 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §12, together with its prerequisite infrastructure: an existence statement `exists_subgroupESetup` giving the subgroup-$E$ setup for any $M\in\mathcal{M}$, which is needed to apply the §12 results (12.5/12.6/12.7/12.10) on the side of $M^*\in\mathcal{M}(N_G(A))$, and Lemma 12.11 itself for $p\in\tau_2(M)$ and $A\in\mathcal{E}_p^2(E)$.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 19 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S12_Lemma1211.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S12_Lemma1211.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Corollary1210

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- Hall-in-Hall: `K` が `G` の Hall `π`-部分群、`H ≤ K` が `K` 内で Hall `ρ`
(`ρ ⊆ π`) なら、`H` は `G` の Hall `ρ`-部分群。index の素因子が
`index_K(H)`-part (`∉ ρ`) と `index_G(K)`-part (`∉ π ⊇ ρ`) に分かれることによる。 -/
theorem isHallSubgroup_of_isHallSubgroup_of_le {G : Type*} [Group G] [Finite G]
    {π ρ : Set ℕ} (hρπ : ρ ⊆ π) {K : Subgroup G} (hK : Ch03.IsHallSubgroup π K)
    {H : Subgroup G} (hHK : H ≤ K) (hH : Ch03.IsHallSubgroup ρ (H.subgroupOf K)) :
    Ch03.IsHallSubgroup ρ H := by
  constructor
  · intro r hr
    apply hH.1 r
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv]
  · intro r hr hrρ
    obtain ⟨hr_prime, hr_dvd, -⟩ := Nat.mem_primeFactors.mp hr
    have hchain := Subgroup.relIndex_mul_relIndex (hHK := hHK) (hKL := le_top (a := K))
    rw [Subgroup.relIndex_top_right, Subgroup.relIndex_top_right] at hchain
    rw [← hchain] at hr_dvd
    rcases hr_prime.dvd_mul.mp hr_dvd with h1 | h1
    · exact hH.2 r (Nat.mem_primeFactors.mpr ⟨hr_prime, h1,
        Subgroup.index_ne_zero_of_finite⟩) hrρ
    · exact hK.2 r (Nat.mem_primeFactors.mpr ⟨hr_prime, h1,
        Subgroup.index_ne_zero_of_finite⟩) (hρπ hrρ)

/-- **`SubgroupESetup` の存在** (BG §12 冒頭, mmd L3025): 任意の `M ∈ ℳ` に対して
`M_σ` の補群 `E` と、`E₁E₂` が部分群になるような Hall `τᵢ(M)`-部分群の組が取れる。
`E₁ ⊔ E₂` の Hall 性は、Hall `τ₁∪τ₂`-部分群 `K₀` の中で `E₁, E₂` を取り、
両者の (`K₀` 内) index が互いに素 (`τ₁`-数 vs `τ₂`-数) であることから
`E₁ ⊔ E₂ = K₀` と同定して得る。 -/
theorem exists_subgroupESetup [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    ∃ E E₁ E₂ E₃ : Subgroup G, SubgroupESetup M E E₁ E₂ E₃ := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  -- `M ≤ N_G(M_σ)`, hence `M_σ.subgroupOf M` is normal.
  have hM_norm_Mσ : M ≤ Subgroup.normalizer ((S10.Msigma M) : Set G) := by
    rw [S10.Msigma, OddOrder.GroupTheory.opiCoreInG]
    have hle := Subgroup.le_normalizer_map
      (H := Ch03.oPiCore (S10.sigma M) ↥M) M.subtype
    rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hle
  set N : Subgroup ↥M := (S10.Msigma M).subgroupOf M with hNdef
  have hN_normal : N.Normal := by
    constructor
    intro n hn g
    rw [hNdef, Subgroup.mem_subgroupOf] at hn ⊢
    have hgn := (Subgroup.mem_normalizer_iff.mp (hM_norm_Mσ g.2) (n : G)).mp hn
    simpa using hgn
  -- Schur–Zassenhaus complement `E₀` to `M_σ` inside `↥M`.
  have hN_hall : Ch03.IsHallSubgroup (S10.sigma M) N := S10.Msigma_subgroupOf_isHall hG hM
  obtain ⟨E₀, hE₀⟩ := Subgroup.exists_right_complement'_of_coprime hN_hall.coprime_index
  set E : Subgroup G := E₀.map M.subtype with hEdef
  have hE_le : E ≤ M := Subgroup.map_subtype_le _
  have hE₀_eq : E.subgroupOf M = E₀ := by
    rw [hEdef, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  -- Complement identities at `G` level.
  have hcompl_inf : S10.Msigma M ⊓ E = ⊥ := by
    have hdisj := hE₀.disjoint
    rw [eq_bot_iff]
    rintro z ⟨hz1, hz2⟩
    have hzM : z ∈ M := hE_le hz2
    have hz1' : (⟨z, hzM⟩ : ↥M) ∈ N := by
      rw [hNdef, Subgroup.mem_subgroupOf]
      exact hz1
    have hz2' : (⟨z, hzM⟩ : ↥M) ∈ E₀ := by
      rw [← hE₀_eq, Subgroup.mem_subgroupOf]
      exact hz2
    have hz_bot := hdisj.le_bot (Subgroup.mem_inf.mpr ⟨hz1', hz2'⟩)
    rw [Subgroup.mem_bot] at hz_bot
    have hz1eq : z = 1 := congrArg Subtype.val hz_bot
    simp [hz1eq]
  have hcompl_sup : S10.Msigma M ⊔ E = M := by
    have hsup := hE₀.sup_eq_top
    apply le_antisymm (sup_le (S10.Msigma_le M) hE_le)
    intro m hm
    have hm' : (⟨m, hm⟩ : ↥M) ∈ N ⊔ E₀ := by rw [hsup]; exact Subgroup.mem_top _
    have h1 : ((N ⊔ E₀).map M.subtype : Subgroup G) ≤ S10.Msigma M ⊔ E := by
      rw [Subgroup.map_sup]
      apply sup_le
      · intro u hu
        obtain ⟨u₀, hu₀, rfl⟩ := hu
        have hu₀' : M.subtype u₀ ∈ S10.Msigma M := hu₀
        exact Subgroup.mem_sup_left hu₀'
      · rw [hEdef]
        exact le_sup_right
    exact h1 ⟨⟨m, hm⟩, hm', rfl⟩
  -- `E` is solvable; fix a Hall `τ₁∪τ₂`-subgroup `K₀` and Hall pieces inside it.
  have : Group.IsSolvable ↥E :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hE_le)
  obtain ⟨K₀, hK₀⟩ := Ch03.hall_E_exists (G := ↥E) (tau1 M ∪ tau2 M)
  have : Group.IsSolvable ↥K₀ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (le_top (a := K₀)))
  obtain ⟨H₁, hH₁⟩ := Ch03.hall_E_exists (G := ↥K₀) (tau1 M)
  obtain ⟨H₂, hH₂⟩ := Ch03.hall_E_exists (G := ↥K₀) (tau2 M)
  obtain ⟨H₃, hH₃⟩ := Ch03.hall_E_exists (G := ↥E) (tau3 M)
  -- τ₁ and τ₂ are disjoint (rank 1 vs rank 2).
  have hτ_disj : ∀ r : ℕ, r ∈ tau1 M → r ∈ tau2 M → False := by
    intro r h1 h2
    have h12 := h1.2.2
    have h22 := h2.2
    omega
  -- `H₁ ⊔ H₂ = K₀` via coprime indices (`τ₂`-number vs `τ₁`-number).
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
  -- Assemble the four subgroups at `G` level.
  set E₁ : Subgroup G := (H₁.map K₀.subtype).map E.subtype with hE₁def
  set E₂ : Subgroup G := (H₂.map K₀.subtype).map E.subtype with hE₂def
  set E₃ : Subgroup G := H₃.map E.subtype with hE₃def
  refine ⟨E, E₁, E₂, E₃, ?_⟩
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
  -- `E₁ ⊔ E₂` corresponds to `K₀`.
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

/-- 共役は `ℰ_p^n(G)` を保つ。 -/
theorem conj_smul_mem_elemAbelianOfRank {p n : ℕ} {A : Subgroup G} (w : G)
    (hA : A ∈ elemAbelianOfRank G p n) :
    (MulAut.conj w • A : Subgroup G) ∈ elemAbelianOfRank G p n := by
  refine mem_elemAbelianOfRank.mpr ⟨?_, ?_⟩
  · rw [mulAut_smul_eq_map]
    exact Subgroup.IsElementaryAbelian.map (MulAut.conj w).injective hA.1
  · rw [mulAut_smul_eq_map, Subgroup.card_map_of_injective (MulAut.conj w).injective]
    exact hA.2

/-- **Hall 断片の `M` 内 Hall 性**: `E` の Hall `π`-部分群 `F` (`π ∩ σ(M) = ∅`) は
`M` の Hall `π`-部分群でもある (Corollary 12.10(e) の内部導出のパラメトリック化)。
`F ≤ E ≤ M` の relIndex 連鎖で、`E` 内の index は `hF` から、`E.relIndex M = |M_σ|` の
素因子は `σ(M)` に入るので `π` と交わらない。 -/
theorem hallPiece_isHall_in_M [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {π : Set ℕ} {F : Subgroup G} (hFE : F ≤ E)
    (hF : Ch03.IsHallSubgroup π (F.subgroupOf E)) (hπσ : π ⊆ (S10.sigma M)ᶜ) :
    Ch03.IsHallSubgroup π (F.subgroupOf M) := by
  have hFM : F ≤ M := hFE.trans h.E_le
  constructor
  · intro r hr
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFM).toEquiv] at hr
    apply hF.1 r
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFE).toEquiv]
  · intro r hr hr2
    obtain ⟨hr_prime, hr_dvd, -⟩ := Nat.mem_primeFactors.mp hr
    have hchain := Subgroup.relIndex_mul_relIndex (hHK := hFE) (hKL := h.E_le)
    have hr_dvd' : r ∣ F.relIndex E * E.relIndex M := by rwa [hchain]
    rcases hr_prime.dvd_mul.mp hr_dvd' with h1 | h1
    · exact hF.2 r (Nat.mem_primeFactors.mpr ⟨hr_prime, h1,
        Subgroup.index_ne_zero_of_finite⟩) hr2
    · have hEM : E.relIndex M = Nat.card ↥(S10.Msigma M) := by
        have hcard := card_Msigma_mul_card_E h
        have h2 := Subgroup.card_mul_index (E.subgroupOf M)
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E_le).toEquiv] at h2
        have h3 : Nat.card ↥E * E.relIndex M
            = Nat.card ↥E * Nat.card ↥(S10.Msigma M) := by
          rw [show E.relIndex M = (E.subgroupOf M).index from rfl, h2, ← hcard]
          ring
        exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h3
      rw [hEM] at h1
      have hrσ : r ∈ S10.sigma M :=
        (S10.Msigma_isHall hG h.mem_maximal).1 r
          (Nat.mem_primeFactors.mpr ⟨hr_prime, h1, Nat.card_pos.ne'⟩)
      exact hπσ hr2 hrσ

/-- **`π`-部分群の Hall 断片への押し込み** (Corollary 12.10(e) の押し込み機構の
パラメトリック化): `X ≤ M` が `π`-群、`F` が `E` の Hall `π`-部分群 (`π ∩ σ(M) = ∅`)
なら `M` 内の共役で `X` は `F` に入る。 -/
theorem exists_conj_smul_le_hallPiece [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {π : Set ℕ} {F : Subgroup G} (hFE : F ≤ E)
    (hF : Ch03.IsHallSubgroup π (F.subgroupOf E)) (hπσ : π ⊆ (S10.sigma M)ᶜ)
    {X : Subgroup G} (hXM : X ≤ M)
    (hXpi : Ch03.Subgroup.IsPiGroup π (X.subgroupOf M)) :
    ∃ w ∈ M, MulAut.conj w • X ≤ F := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups h.mem_maximal
  obtain ⟨H, hH_hall, -, hX_le_H⟩ :=
    Ch1.S01.aInvariant_piSubgroup_le_aInvariant_hall
      (A := Unit) (φ := (1 : Unit →* MulAut ↥M))
      (by rw [Nat.card_unique]; exact Nat.coprime_one_left _)
      hXpi (fun _ => one_smul _ _)
  set HG : Subgroup G := H.map M.subtype with hHGdef
  have hHG_le_M : HG ≤ M := Subgroup.map_subtype_le _
  have hHG_hall : Ch03.IsHallSubgroup π (HG.subgroupOf M) := by
    rwa [hHGdef, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  obtain ⟨w, hwM, hw⟩ :=
    Ch1.S06.exists_conj_eq_of_isHall_subgroupOf inferInstance hHG_le_M
      (hFE.trans h.E_le) hHG_hall (hallPiece_isHall_in_M hG h hFE hF hπσ)
  have hXHG : X ≤ HG := by
    intro x hx
    rw [hHGdef]
    exact Subgroup.mem_map.mpr ⟨⟨x, hXM hx⟩,
      hX_le_H (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  exact ⟨w, hwM, (conj_smul_mono (MulAut.conj w) hXHG).trans hw.le⟩

/-- `p ∈ τ₂(M)` (`p` 素数) なら `M` は rank-2 elementary abelian `p`-部分群を含む
(`pRank ↥M p = 2` の witness 化)。 -/
theorem exists_mem_elemAbelianOfRank_two_le_of_tau2 [Finite G]
    {M : Subgroup G} {p : ℕ} (hp_prime : p.Prime) (hp : p ∈ tau2 M) :
    ∃ A ∈ elemAbelianOfRank G p 2, A ≤ M := by
  have hrank : pRank ↥M p = 2 := tau2_pRank_eq_two hp
  obtain ⟨B, hB_ea, hB_log⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank (G := ↥M) (p := p)
      (n := 2) two_pos (by omega)
  have hB_card : p ^ 2 ≤ Nat.card ↥B :=
    le_trans (Nat.pow_le_pow_right hp_prime.one_lt.le hB_log)
      (Nat.pow_log_le_self p Nat.card_pos.ne')
  obtain ⟨H, hH_ea, hH_card⟩ :=
    IsElementaryAbelian.exists_subgroup_card_prime_sq hp_prime hB_ea hB_card
  refine ⟨(H.map B.subtype).map M.subtype, mem_elemAbelianOfRank.mpr ⟨?_, ?_⟩,
    Subgroup.map_subtype_le _⟩
  · exact Subgroup.IsElementaryAbelian.map M.subtype_injective
      (Subgroup.IsElementaryAbelian.map B.subtype_injective hH_ea)
  · rw [Subgroup.card_map_of_injective M.subtype_injective,
      Subgroup.card_map_of_injective B.subtype_injective]
    exact hH_card

/-- `p ∈ σ(M')` のとき `M'` 内の elementary abelian `p`-部分群は `M'_σ` に入る
(`M'_σ` の `G` 内 Hall 性 `S10.Msigma_isHall` から)。 -/
theorem le_Msigma_of_mem_elemAbelianOfRank_of_mem_sigma [Finite G]
    (hG : IsMinimalSimpleOdd G) {M' : Subgroup G} (hM' : M' ∈ maximalSubgroups G)
    {p : ℕ} (hp_prime : p.Prime) (hpσ : p ∈ S10.sigma M') {n : ℕ}
    {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p n) (hAM' : A ≤ M') :
    A ≤ S10.Msigma M' := by
  refine S10.sigma_subgroup_le_Msigma_of_isHall (S10.Msigma_isHall hG hM') hAM' ?_
  intro r hr
  rw [hA.2] at hr
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn, pow_zero] at hr
    simp at hr
  · rw [Nat.primeFactors_pow p hn.ne', Nat.Prime.primeFactors hp_prime] at hr
    rw [Finset.mem_singleton.mp hr]
    exact hpσ

/-- **Lemma 12.11(a), `p` 自身の部分** (mmd L3322): `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)`,
`M* ∈ ℳ(N_G(A))` なら `p ∈ σ(M*)`。Lemma 12.2(a) で `p ∈ σ(M*) ∪ τ₂(M*)`;
`τ₂(M*)` 側は `A` を `M*` 内共役で `E₂*` に押し込むと Corollary 12.6(b) の
`N_G(A^w) ⊄ M*` が `N_G(A) ≤ M*` と衝突して不発。 -/
theorem mem_sigma_of_tau2_of_mem_maximalContaining [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (_hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (A : Set G))) :
    p ∈ S10.sigma Mstar := by
  classical
  obtain ⟨hMst_co, hNMst⟩ := mem_maximalSubgroupsContaining.mp hMstar
  have hMst_mem : Mstar ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMst_co
  have hAM : A ≤ M := hAE.trans h.E_le
  have hAne : A ≠ ⊥ := by
    intro hbot
    have hcard := hA.2
    rw [hbot, Subgroup.card_bot] at hcard
    exact (Nat.one_lt_pow two_ne_zero (Fact.out : p.Prime).one_lt).ne' hcard.symm
  rcases prime_mem_sigma_or_tau2 hG h.mem_maximal hAM hAne hA.1.isPGroup hMstar with hσ | hτ₂
  · exact hσ
  · exfalso
    obtain ⟨Es, E1s, E2s, E3s, hs⟩ := exists_subgroupESetup hG hMst_mem
    have hAMst : A ≤ Mstar := Subgroup.le_normalizer.trans hNMst
    have hApi : Ch03.Subgroup.IsPiGroup (tau2 Mstar) (A.subgroupOf Mstar) := by
      intro r hr
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAMst).toEquiv, hA.2,
        Nat.primeFactors_pow p two_ne_zero,
        Nat.Prime.primeFactors (Fact.out : p.Prime)] at hr
      rw [Finset.mem_singleton.mp hr]
      exact hτ₂
    obtain ⟨w, hwMst, hwle⟩ := exists_conj_smul_le_hallPiece hG hs hs.E₂_le hs.E₂_hall
      (tau2_subset_sigma_compl Mstar) hAMst hApi
    have hA' := conj_smul_mem_elemAbelianOfRank w hA
    have hA'E : (MulAut.conj w • A : Subgroup G) ≤ Es := hwle.trans hs.E₂_le
    have hnot := (elemAb_normal_in_E_of_tau2 hG hs hτ₂ hA' hA'E).2.1.2.2
    apply hnot
    rw [← normalizer_conj_smul]
    calc MulAut.conj w • Subgroup.normalizer (A : Set G)
        ≤ MulAut.conj w • Mstar := conj_smul_mono _ hNMst
      _ = Mstar := conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hwMst)

/-- **BG Lemma 12.11(a)** (mmd L3318): `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)`, `M* ∈ ℳ(N_G(A))`
のとき、`τ₂(M)` の任意の**素数** `q` は `σ(M*) − β(M*)` に入る。

(repo の `tau2` は pRank 条件のみで合成数を排除しないため、原典の
`τ₂(M) ⊆ σ(M*) − β(M*)` は素数に制限して faithful 化する — 12.3/12.10(c) と同型の訂正。)

`q = p` は `mem_sigma_of_tau2_of_mem_maximalContaining`。`q ≠ p` は `A_q ∈ ℰ_q²(E)` を
押し込みで作り、`A` と `A_q` が `E` の coprime normal 部分群 (Corollary 12.6(a)) として
可換なことから `⊥ ≠ A ≤ C_{M*_σ}(A_q)` を得て、`q ∈ τ₂(M*)` なら Theorem 12.5(d) に
矛盾。rank-2 で `τ₁(M*)/τ₃(M*)` も不可、分割 (12.1) で `q ∈ σ(M*)`。
`β` 除外は Lemma 12.1(g) (`q ∉ β(G)`)。 -/
theorem tau2_prime_mem_sigma_diff_beta [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (A : Set G)))
    {q : ℕ} (hq_prime : q.Prime) (hq : q ∈ tau2 M) :
    q ∈ S10.sigma Mstar \ S10.beta Mstar := by
  classical
  obtain ⟨hMst_co, hNMst⟩ := mem_maximalSubgroupsContaining.mp hMstar
  have hMst_mem : Mstar ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMst_co
  have hEN : E ≤ Subgroup.normalizer (A : Set G) := E_le_normalizer_of_tau2 hG h hp hA hAE
  have hEMst : E ≤ Mstar := hEN.trans hNMst
  -- β 除外: Lemma 12.1(g) — `q ∉ β(G)`、よって `q ∉ β(M*)`。
  obtain ⟨A₁, hA₁, hA₁M⟩ := exists_mem_elemAbelianOfRank_two_le_of_tau2 hq_prime hq
  have hqideal : ¬ S10.idealPrime q G :=
    (isMaximalElementaryAbelian_of_mem_tau2 hG h.mem_maximal hq_prime hq hA₁M hA₁).2
  refine ⟨?_, fun hβ => hqideal hβ.2⟩
  by_cases hqp : q = p
  · subst hqp
    exact mem_sigma_of_tau2_of_mem_maximalContaining hG h hq hA hAE hMstar
  have : Fact q.Prime := ⟨hq_prime⟩
  -- `A_q ∈ ℰ_q²(E)` を押し込みで構成。
  obtain ⟨w, hwM, hwle⟩ := exists_conj_smul_le_hallPiece hG h h.E₂_le h.E₂_hall
    (tau2_subset_sigma_compl M) hA₁M (by
    intro r hr
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₁M).toEquiv, hA₁.2,
      Nat.primeFactors_pow q two_ne_zero, Nat.Prime.primeFactors hq_prime] at hr
    rw [Finset.mem_singleton.mp hr]
    exact hq)
  set Aq : Subgroup G := MulAut.conj w • A₁ with hAqdef
  have hAq : Aq ∈ elemAbelianOfRank G q 2 := conj_smul_mem_elemAbelianOfRank w hA₁
  have hAqE : Aq ≤ E := hwle.trans h.E₂_le
  have hAqMst : Aq ≤ Mstar := hAqE.trans hEMst
  -- `p ∈ σ(M*)`、よって `A ≤ M*_σ`。
  have hpσ : p ∈ S10.sigma Mstar :=
    mem_sigma_of_tau2_of_mem_maximalContaining hG h hp hA hAE hMstar
  have hAMσ : A ≤ S10.Msigma Mstar :=
    le_Msigma_of_mem_elemAbelianOfRank_of_mem_sigma hG hMst_mem
      (Fact.out : p.Prime) hpσ hA (Subgroup.le_normalizer.trans hNMst)
  -- `A ⊓ A_q = ⊥` (coprime cards)。
  have hinf : A ⊓ Aq = ⊥ := by
    rw [← Subgroup.card_eq_one]
    have h1 : Nat.card ↥(A ⊓ Aq : Subgroup G) ∣ p ^ 2 := by
      rw [← hA.2]
      exact Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(A ⊓ Aq : Subgroup G) ∣ q ^ 2 := by
      rw [← hAq.2]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hco : Nat.Coprime (p ^ 2) (q ^ 2) :=
      Nat.Coprime.pow 2 2
        ((Nat.coprime_primes (Fact.out : p.Prime) hq_prime).mpr fun hpq => hqp hpq.symm)
    exact (Nat.Coprime.coprime_dvd_left h1 hco).eq_one_of_dvd h2
  -- `A ≤ C_G(A_q)`: `A, A_q ⊴ E` (Corollary 12.6(a)) の coprime 可換性。
  have hENq : E ≤ Subgroup.normalizer (Aq : Set G) :=
    E_le_normalizer_of_tau2 hG h hq hAq hAqE
  have hAcent : A ≤ Subgroup.centralizer (Aq : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, ← le_bot_iff, ← hinf]
    rw [Subgroup.commutator_le]
    intro a ha t ht
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : t * a⁻¹ * t⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp (hEN (hAqE ht)) a⁻¹).mp (A.inv_mem ha)
      have h2 : a * (t * a⁻¹ * t⁻¹) ∈ A := A.mul_mem ha h1
      rw [commutatorElement_def]
      simpa [mul_assoc] using h2
    · have h1 : a * t * a⁻¹ ∈ Aq :=
        (Subgroup.mem_normalizer_iff.mp (hENq (hAE ha)) t).mp ht
      have h2 : a * t * a⁻¹ * t⁻¹ ∈ Aq := Aq.mul_mem h1 (Aq.inv_mem ht)
      rwa [commutatorElement_def]
  -- 分割 (12.1) と rank で `q ∈ σ(M*)` 以外を排除。
  by_contra hqσ
  obtain ⟨Es, E1s, E2s, E3s, hs⟩ := exists_subgroupESetup hG hMst_mem
  have hqMst : q ∣ Nat.card ↥Mstar := by
    refine dvd_trans ?_ (Subgroup.card_dvd_of_le hAqMst)
    rw [hAq.2]
    exact dvd_pow_self q two_ne_zero
  have hqEs : q ∈ (Nat.card ↥Es).primeFactors := by
    have hsplit := card_Msigma_mul_card_E hs
    have hqdvd : q ∣ Nat.card ↥(S10.Msigma Mstar) * Nat.card ↥Es := by
      rw [hsplit]
      exact hqMst
    rcases hq_prime.dvd_mul.mp hqdvd with hd | hd
    · exact absurd (S10.Msigma_isPiGroup Mstar q
        (Nat.mem_primeFactors.mpr ⟨hq_prime, hd, Nat.card_pos.ne'⟩)) hqσ
    · exact Nat.mem_primeFactors.mpr ⟨hq_prime, hd, Nat.card_pos.ne'⟩
  have hrank2 : 2 ≤ pRank ↥Mstar q := by
    have hle := le_pRank (Aq.subgroupOf Mstar)
      (IsElementaryAbelian.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hAqMst).symm hAq.1)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAqMst).toEquiv, hAq.2,
      Nat.log_pow hq_prime.one_lt] at hle
  rcases hs.mem_tau_union_of_mem_primeFactors hG hqEs with (h1 | h2) | h3
  · have := tau1_pRank_eq_one h1
    omega
  · -- `q ∈ τ₂(M*)`: Theorem 12.5(d) で `M*_σ ⊓ C_G(A_q) = ⊥` だが `⊥ ≠ A` が入る。
    have h125d := (Msigma_nilpotent_of_tau2 hG hMst_mem h2 hAq hAqMst).2.2.2.1
    have hAbot : A ≤ (⊥ : Subgroup G) := by
      rw [← h125d]
      exact le_inf hAMσ hAcent
    have hcard := hA.2
    rw [le_bot_iff.mp hAbot, Subgroup.card_bot] at hcard
    exact (Nat.one_lt_pow two_ne_zero (Fact.out : p.Prime).one_lt).ne' hcard.symm
  · have := tau3_pRank_eq_one h3
    omega

/-- `derivedInG` の単調性 (S09/S10 の private 補題の再掲; hoist は hub 仕事)。 -/
private theorem derivedInG_eq_commutator (H : Subgroup G) :
    derivedInG H = ⁅H, H⁆ := by
  rw [derivedInG, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

private theorem derivedInG_mono {H K : Subgroup G} (hHK : H ≤ K) :
    derivedInG H ≤ derivedInG K := by
  rw [derivedInG_eq_commutator H, derivedInG_eq_commutator K]
  exact Subgroup.commutator_mono hHK hHK

/-- **BG Lemma 12.11(b)** (mmd L3325): `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)`, `M* ∈ ℳ(N_G(A))`
のとき `π(E/C_E(A)) ⊆ τ₁(M*) ∪ τ₂(M*)`。

`r ∈ π(E/C_E(A))` が `σ(M*) ∪ τ₃(M*)` に落ちると仮定すると、`E` の Sylow `r`-部分群
`Q` は (`σ` なら `M*_σ` 経由、`τ₃` なら `E₃*` への押し込み経由で) `M*' = derivedInG M*`
に入る。`p ∉ β(M*)` (12.11(a)) より `M*'` は normal `p`-補群 `K` を持ち (Lemma 10.8(c) =
`isHall_Mbeta` 第 4 成分)、`r ≠ p` から `Q ≤ K`。`A ≤ M*_σ ≤ M*'` と合わせ
`⁅A,Q⁆ ≤ A ⊓ K = ⊥` (各因子が他方を正規化)、よって `Q ≤ C_G(A)` — これは Sylow `r` が
`C_E(A)` に入ることを意味し `r ∣ [E : C_E(A)]` に矛盾。 -/
theorem index_primeFactors_subset_tau1_union_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (A : Set G)))
    {r : ℕ}
    (hr : r ∈ (((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).index).primeFactors) :
    r ∈ tau1 Mstar ∪ tau2 Mstar := by
  classical
  by_contra hr12
  have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr
  have : Fact r.Prime := ⟨hr_prime⟩
  obtain ⟨hMst_co, hNMst⟩ := mem_maximalSubgroupsContaining.mp hMstar
  have hMst_mem : Mstar ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMst_co
  have hEN : E ≤ Subgroup.normalizer (A : Set G) := E_le_normalizer_of_tau2 hG h hp hA hAE
  have hEMst : E ≤ Mstar := hEN.trans hNMst
  have hAMst : A ≤ Mstar := Subgroup.le_normalizer.trans hNMst
  -- `r ∈ τ₁(M)` (Corollary 12.10(c)) ⟹ `r ≠ p`。
  have hrτ₁M : r ∈ tau1 M :=
    ((nilpotent_sigmaComplement_abelian hG h).2.2.1 p (Fact.out : p.Prime) hp A hA hAE).2.2 r hr
  have hrp : r ≠ p := by
    intro he
    have h1 := tau1_pRank_eq_one hrτ₁M
    have h2 := tau2_pRank_eq_two hp
    rw [he] at h1
    omega
  -- `p ∈ σ(M*) − β(M*)` (12.11(a)) と `A ≤ M*_σ ≤ M*'`。
  have hpσ : p ∈ S10.sigma Mstar :=
    mem_sigma_of_tau2_of_mem_maximalContaining hG h hp hA hAE hMstar
  have hpβ : p ∉ S10.beta Mstar :=
    (tau2_prime_mem_sigma_diff_beta hG h hp hA hAE hMstar (Fact.out : p.Prime) hp).2
  have hAD : A ≤ derivedInG Mstar :=
    (le_Msigma_of_mem_elemAbelianOfRank_of_mem_sigma hG hMst_mem (Fact.out : p.Prime)
      hpσ hA hAMst).trans (S10.Msigma_le_derived hG hMst_mem)
  -- `E` の Sylow `r`-部分群 `Q` (G レベル)。
  obtain ⟨Q₀⟩ : Nonempty (Sylow r ↥E) := inferInstance
  set Q : Subgroup G := (Q₀ : Subgroup ↥E).map E.subtype with hQdef
  have hQE : Q ≤ E := Subgroup.map_subtype_le _
  have hQMst : Q ≤ Mstar := hQE.trans hEMst
  -- `r ∣ |E|` (index は |E| を割る) ⟹ `r ∣ |Q₀|`。
  have hrE : r ∣ Nat.card ↥E :=
    (Nat.mem_primeFactors.mp hr).2.1.trans
      (Subgroup.index_dvd_card ((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E))
  have hQ₀card : Nat.card ↥(Q₀ : Subgroup ↥E) = r ^ (Nat.card ↥E).factorization r :=
    Sylow.card_eq_multiplicity Q₀
  have hQcard : Nat.card ↥Q = r ^ (Nat.card ↥E).factorization r := by
    rw [hQdef, Subgroup.card_map_of_injective E.subtype_injective]
    exact hQ₀card
  have hfac_pos : (Nat.card ↥E).factorization r ≠ 0 := by
    intro h0
    have h1 : r ^ 1 ∣ Nat.card ↥E := by rwa [pow_one]
    have h2 := (Nat.Prime.pow_dvd_iff_le_factorization hr_prime
      (Nat.card_pos (α := ↥E)).ne').mp h1
    omega
  have hQpg : IsPGroup r ↥Q := by
    rw [hQdef]
    exact Q₀.2.map E.subtype
  -- `Q ≤ M*' = derivedInG M*`。
  have hQD : Q ≤ derivedInG Mstar := by
    by_cases hrσ : r ∈ S10.sigma Mstar
    · -- `σ(M*)`: `Q ≤ M*_σ ≤ M*'`。
      refine (S10.sigma_subgroup_le_Msigma_of_isHall (S10.Msigma_isHall hG hMst_mem)
        hQMst ?_).trans (S10.Msigma_le_derived hG hMst_mem)
      intro s hs'
      rw [hQcard] at hs'
      rw [Nat.primeFactors_pow r hfac_pos, Nat.Prime.primeFactors hr_prime] at hs'
      rw [Finset.mem_singleton.mp hs']
      exact hrσ
    · -- `σ` 外: 分割で `r ∈ τ₃(M*)`、`E₃*` へ押し込み。
      obtain ⟨Es, E1s, E2s, E3s, hs⟩ := exists_subgroupESetup hG hMst_mem
      have hrMst : r ∣ Nat.card ↥Mstar := hrE.trans (Subgroup.card_dvd_of_le hEMst)
      have hrEs : r ∈ (Nat.card ↥Es).primeFactors := by
        have hsplit := card_Msigma_mul_card_E hs
        have hrdvd : r ∣ Nat.card ↥(S10.Msigma Mstar) * Nat.card ↥Es := by
          rw [hsplit]
          exact hrMst
        rcases hr_prime.dvd_mul.mp hrdvd with hd | hd
        · exact absurd (S10.Msigma_isPiGroup Mstar r
            (Nat.mem_primeFactors.mpr ⟨hr_prime, hd, Nat.card_pos.ne'⟩)) hrσ
        · exact Nat.mem_primeFactors.mpr ⟨hr_prime, hd, Nat.card_pos.ne'⟩
      have hrτ₃ : r ∈ tau3 Mstar := by
        rcases hs.mem_tau_union_of_mem_primeFactors hG hrEs with (h1 | h2) | h3
        · exact absurd (Or.inl h1) hr12
        · exact absurd (Or.inr h2) hr12
        · exact h3
      have hQpi : Ch03.Subgroup.IsPiGroup (tau3 Mstar) (Q.subgroupOf Mstar) := by
        intro s hs'
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQMst).toEquiv, hQcard,
          Nat.primeFactors_pow r hfac_pos, Nat.Prime.primeFactors hr_prime] at hs'
        rw [Finset.mem_singleton.mp hs']
        exact hrτ₃
      obtain ⟨w, hwMst, hwle⟩ := exists_conj_smul_le_hallPiece hG hs hs.E₃_le hs.E₃_hall
        (tau3_subset_sigma_compl Mstar) hQMst hQpi
      have hE3D : E3s ≤ derivedInG Mstar :=
        (hs.E3_le_derived hG).trans (derivedInG_mono hs.E_le)
      have hconj : MulAut.conj w • Q ≤ derivedInG Mstar := hwle.trans hE3D
      -- `M* ≤ N(M*')` で共役を引き戻す。
      have hw' : MulAut.conj w⁻¹ • derivedInG Mstar = derivedInG Mstar :=
        conj_smul_eq_self_of_mem_normalizer
          (S10.le_normalizer_derivedInG Mstar (Mstar.inv_mem hwMst))
      have hpull : MulAut.conj w⁻¹ • (MulAut.conj w • Q)
          ≤ MulAut.conj w⁻¹ • derivedInG Mstar := conj_smul_mono _ hconj
      rwa [hw', smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at hpull
  -- `p ∈ π(M*)` と Lemma 10.8(c): `M*'` の normal `p`-補群 `K`。
  have hpMst : p ∈ (Nat.card ↥Mstar).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨(Fact.out : p.Prime), ?_, Nat.card_pos.ne'⟩
    refine dvd_trans ?_ (Subgroup.card_dvd_of_le hAMst)
    rw [hA.2]
    exact dvd_pow_self p two_ne_zero
  obtain ⟨K, hKnorm, hKcompl⟩ :=
    ((S10.isHall_Mbeta hG hMst_mem).2.2.2 p (Fact.out : p.Prime) hpMst hpβ).1
  have : K.Normal := hKnorm
  set KG : Subgroup G := K.map (derivedInG Mstar).subtype with hKGdef
  -- `Q ≤ K_G`: 商 `D/K` は `p`-群、`Q` は `r ≠ p` の `r`-群。
  have hQKG : Q ≤ KG := by
    have hQ'le : Q.subgroupOf (derivedInG Mstar) ≤ K := by
      have himg : (Q.subgroupOf (derivedInG Mstar)).map (QuotientGroup.mk' K) = ⊥ := by
        rw [← Subgroup.card_eq_one]
        obtain ⟨P⟩ : Nonempty (Sylow p ↥(derivedInG Mstar)) := inferInstance
        have hPcard : ∃ n : ℕ, Nat.card ↥(P : Subgroup ↥(derivedInG Mstar)) = p ^ n :=
          IsPGroup.iff_card.mp P.2
        obtain ⟨n, hPn⟩ := hPcard
        have hidx : K.index = p ^ n := by
          rw [(hKcompl P).symm.index_eq_card, hPn]
        have h1 : Nat.card ↥((Q.subgroupOf (derivedInG Mstar)).map
            (QuotientGroup.mk' K)) ∣ p ^ n := by
          rw [← hidx]
          exact Subgroup.card_subgroup_dvd_card _
        have h2 : Nat.card ↥((Q.subgroupOf (derivedInG Mstar)).map
            (QuotientGroup.mk' K)) ∣ r ^ (Nat.card ↥E).factorization r := by
          refine dvd_trans (Subgroup.card_map_dvd _ _) ?_
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQD).toEquiv]
          exact hQcard.dvd
        have hco : Nat.Coprime (r ^ (Nat.card ↥E).factorization r) (p ^ n) :=
          Nat.Coprime.pow _ _ ((Nat.coprime_primes hr_prime (Fact.out : p.Prime)).mpr hrp)
        exact (hco.coprime_dvd_left h2).eq_one_of_dvd h1
      rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at himg
    intro x hx
    rw [hKGdef]
    exact Subgroup.mem_map.mpr ⟨⟨x, hQD hx⟩, hQ'le (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  -- `⁅A, Q⁆ ≤ A ⊓ K_G = ⊥` ⟹ `Q ≤ C_G(A)`。
  have hD_norm_KG : derivedInG Mstar ≤ Subgroup.normalizer (KG : Set G) := by
    rw [hKGdef]
    have hle := Subgroup.le_normalizer_map (H := K) (derivedInG Mstar).subtype
    rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hle
  have hKG_pcompl : ¬ p ∣ Nat.card ↥KG := by
    intro hdvd
    rw [hKGdef, Subgroup.card_map_of_injective (derivedInG Mstar).subtype_injective] at hdvd
    obtain ⟨P⟩ : Nonempty (Sylow p ↥(derivedInG Mstar)) := inferInstance
    have hcm := (hKcompl P).card_mul_card
    have hPmul : Nat.card ↥(P : Subgroup ↥(derivedInG Mstar))
        = p ^ (Nat.card ↥(derivedInG Mstar)).factorization p :=
      Sylow.card_eq_multiplicity P
    have hfull : p ^ ((Nat.card ↥(derivedInG Mstar)).factorization p + 1)
        ∣ Nat.card ↥(derivedInG Mstar) := by
      have h2 : p ^ (Nat.card ↥(derivedInG Mstar)).factorization p * p
          ∣ Nat.card ↥(P : Subgroup ↥(derivedInG Mstar)) * Nat.card ↥K :=
        mul_dvd_mul hPmul.symm.dvd hdvd
      rw [pow_succ]
      calc p ^ (Nat.card ↥(derivedInG Mstar)).factorization p * p
          ∣ Nat.card ↥(P : Subgroup ↥(derivedInG Mstar)) * Nat.card ↥K := h2
        _ = Nat.card ↥K * Nat.card ↥(P : Subgroup ↥(derivedInG Mstar)) := mul_comm _ _
        _ = Nat.card ↥(derivedInG Mstar) := hcm
    have := (Nat.Prime.pow_dvd_iff_le_factorization (Fact.out : p.Prime)
      (Nat.card_pos (α := ↥(derivedInG Mstar))).ne').mp hfull
    omega
  have hAKG_bot : A ⊓ KG = ⊥ := by
    rw [← Subgroup.card_eq_one]
    have h1 : Nat.card ↥(A ⊓ KG : Subgroup G) ∣ p ^ 2 := by
      rw [← hA.2]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hnp : ¬ p ∣ Nat.card ↥(A ⊓ KG : Subgroup G) := fun hdvd =>
      hKG_pcompl (hdvd.trans (Subgroup.card_dvd_of_le inf_le_right))
    exact Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.pow_right 2
        ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr hnp).symm) h1
  -- `⁅A, Q⁆ ≤ A ⊓ K_G = ⊥` (Q ≤ E ≤ N(A)、A ≤ D ≤ N(K_G))。
  have hcomm : ⁅A, Q⁆ ≤ A ⊓ KG := by
    rw [Subgroup.commutator_le]
    intro a ha t ht
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : t * a⁻¹ * t⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp (hEN (hQE ht)) a⁻¹).mp (A.inv_mem ha)
      have h2 : a * (t * a⁻¹ * t⁻¹) ∈ A := A.mul_mem ha h1
      rw [commutatorElement_def]
      simpa [mul_assoc] using h2
    · have h1 : a * t * a⁻¹ ∈ KG :=
        (Subgroup.mem_normalizer_iff.mp (hD_norm_KG (hAD ha)) t).mp (hQKG ht)
      have h2 : a * t * a⁻¹ * t⁻¹ ∈ KG := KG.mul_mem h1 (KG.inv_mem (hQKG ht))
      rwa [commutatorElement_def]
  have hcomm_bot : ⁅A, Q⁆ = ⊥ := le_bot_iff.mp (hAKG_bot ▸ hcomm)
  have hQC : Q ≤ Subgroup.centralizer (A : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hcomm_bot
  -- Sylow `r` が `C_E(A)` に入る ⟹ `r ∤ [E : C_E(A)]`、`hr` と矛盾。
  have hQ₀le : (Q₀ : Subgroup ↥E) ≤
      (E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_inf.mpr ⟨x.2, hQC (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)⟩
  have hr_idx : r ∣ ((Q₀ : Subgroup ↥E)).index :=
    (Nat.mem_primeFactors.mp hr).2.1.trans (Subgroup.index_dvd_of_le hQ₀le)
  have hr_card : r ∣ Nat.card ↥(Q₀ : Subgroup ↥E) := by
    rw [hQ₀card]
    exact dvd_pow_self r hfac_pos
  have hco := Q₀.card_coprime_index
  exact hr_prime.ne_one (Nat.dvd_one.mp (hco ▸ Nat.dvd_gcd hr_card hr_idx))

private theorem card_conj_smul (g : G) (H : Subgroup G) :
    Nat.card ↥(MulAut.conj g • H) = Nat.card ↥H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

/-- `M.subtype` による像は `↥M` 内 conj-smul と `G` 内 conj-smul を交換する。 -/
private theorem map_subtype_conj_smul {M : Subgroup G} (m : ↥M) (H : Subgroup ↥M) :
    (MulAut.conj m • H).map M.subtype = MulAut.conj (m : G) • (H.map M.subtype) := by
  rw [mulAut_smul_eq_map, mulAut_smul_eq_map, Subgroup.map_map, Subgroup.map_map]
  congr 1

/-- **cyclic `q`-群の最小部分群**: cyclic な `q`-群 `Q` の位数 `q` の部分群 `Q₀` は、
`Q` の任意の非自明部分群 `T` に含まれる。 -/
private theorem le_of_ne_bot_of_le_cyclic {q : ℕ} [Fact q.Prime] [Finite G]
    {Q Q₀ T : Subgroup G} (hQcyc : IsCyclic ↥Q) (hQpg : IsPGroup q ↥Q)
    (hQ₀Q : Q₀ ≤ Q) (hQ₀card : Nat.card ↥Q₀ = q)
    (hTQ : T ≤ Q) (hTne : T ≠ ⊥) : Q₀ ≤ T := by
  classical
  -- `T` は非自明 `q`-群なので位数 `q` の部分群を含む。
  have hTpg : IsPGroup q ↥T := fun t => by
    obtain ⟨k, hk⟩ := hQpg ⟨(t : G), hTQ t.2⟩
    refine ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    exact Subtype.ext (by simpa using this)
  have hqT : q ∣ Nat.card ↥T := by
    rcases IsPGroup.iff_card.mp hTpg with ⟨k, hkcard⟩
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · exact absurd (Subgroup.card_eq_one.mp (by simpa using hkcard)) hTne
    · rw [hkcard]
      exact dvd_pow_self q hkpos.ne'
  obtain ⟨T₀, hT₀card⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := ↥T) q (n := 1) (by rwa [pow_one])
  set T₀' : Subgroup G := T₀.map T.subtype with hT₀'def
  have hT₀'card : Nat.card ↥T₀' = q := by
    rw [hT₀'def, Subgroup.card_map_of_injective T.subtype_injective, hT₀card, pow_one]
  have hT₀'T : T₀' ≤ T := Subgroup.map_subtype_le _
  -- cyclic `Q` 内で位数 `q` の部分群は一意。
  have hQ₀eq : Q₀.subgroupOf Q = T₀'.subgroupOf Q := by
    apply OddOrder.GroupTheory.cyclic_subgroup_eq_of_card_eq (C := ↥Q)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ₀Q).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hT₀'T.trans hTQ)).toEquiv,
      hQ₀card, hT₀'card]
  have heq : Q₀ = T₀' := by
    have h1 := congrArg (fun X : Subgroup ↥Q => X.map Q.subtype) hQ₀eq
    simpa [Subgroup.map_subgroupOf_eq_of_le hQ₀Q,
      Subgroup.map_subgroupOf_eq_of_le (hT₀'T.trans hTQ)] using h1
  rw [heq]
  exact hT₀'T

/-- **no-complement**: cyclic `q`-群 `Q ≤ M*` が位数 `q` の部分群 `Q₀` を真に含み
(`q² ≤ |Q|`)、`K'` が `M*` 内の `Q₀` の補群相当 (`Q₀ ⊓ K' = ⊥`, `|K'|·q = |M*|`)
なら矛盾。`[Q : Q ⊓ K'] ≤ [M* : K']` (`relIndex_le_of_le_right`) による。 -/
private theorem no_complement_of_lt_cyclic [Finite G] {q : ℕ} [Fact q.Prime]
    {Mstar Q Q₀ K' : Subgroup G} (hQcyc : IsCyclic ↥Q) (hQpg : IsPGroup q ↥Q)
    (hQM : Q ≤ Mstar) (hK'M : K' ≤ Mstar)
    (hQ₀Q : Q₀ ≤ Q) (hQ₀card : Nat.card ↥Q₀ = q) (hQbig : q ^ 2 ≤ Nat.card ↥Q)
    (hinf : Q₀ ⊓ K' = ⊥) (hKcard : Nat.card ↥K' * q = Nat.card ↥Mstar) : False := by
  classical
  -- `Q ⊓ K' = ⊥`: さもなくば `Q₀ ≤ Q ⊓ K' ≤ K'` で `Q₀ = ⊥`。
  have hQK' : Q ⊓ K' = ⊥ := by
    by_contra hne
    have hQ₀le : Q₀ ≤ Q ⊓ K' :=
      le_of_ne_bot_of_le_cyclic hQcyc hQpg hQ₀Q hQ₀card inf_le_left hne
    have hbot : Q₀ = ⊥ := by
      rw [← hinf]
      exact le_antisymm (le_inf le_rfl (hQ₀le.trans inf_le_right)) inf_le_left
    rw [hbot, Subgroup.card_bot] at hQ₀card
    exact (Fact.out : q.Prime).one_lt.ne hQ₀card
  -- `[Q : Q ⊓ K'] ≤ [M* : K'] = q` ⟹ `|Q| ≤ q`、`q² ≤ |Q|` と矛盾。
  have hrel_M : K'.relIndex Mstar = q := by
    have h1 : Nat.card ↥(K'.subgroupOf Mstar) * (K'.subgroupOf Mstar).index
        = Nat.card ↥Mstar := Subgroup.card_mul_index _
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK'M).toEquiv] at h1
    have h2 : Nat.card ↥K' * K'.relIndex Mstar = Nat.card ↥K' * q := by
      rw [show K'.relIndex Mstar = (K'.subgroupOf Mstar).index from rfl, h1, hKcard]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h2
  have hrel_Q : K'.relIndex Q = Nat.card ↥Q := by
    have h1 : K'.subgroupOf Q = ⊥ := by
      rw [← Subgroup.inf_subgroupOf_right, inf_comm, hQK', Subgroup.bot_subgroupOf]
    rw [show K'.relIndex Q = (K'.subgroupOf Q).index from rfl, h1, Subgroup.index_bot]
  have hle := Subgroup.relIndex_le_of_le_right hQM (by
    rw [hrel_M]
    exact (Fact.out : q.Prime).pos.ne')
  rw [hrel_Q, hrel_M] at hle
  have hqlt : q < q ^ 2 := by
    have h1 := (Fact.out : q.Prime).one_lt
    nlinarith
  omega

/-- **(c) 用 line パッケージ** (mmd L3328-3330): `q ∈ π([E : C_E(A)]) ∩ π(C_E(A))` のとき、
cyclic な `q`-部分群 `Q ≤ E` (`q² ≤ |Q|`) と位数 `q` の `Q₀ ≤ Q ⊓ C_G(A)` で **Frattini 性**
「`C_G(A) ≤ T` かつ `N_G(Q₀) ≤ T` なら `N_G(A) ≤ T`」を満たすものが存在する。

`Q₀` は `C_G(A)` の Sylow `q`-部分群 `Q₁` の唯一の位数 `q` 部分群 (`q ∈ τ₁(M)` =
Corollary 12.10(c) より `M` の `q`-部分群はすべて cyclic)。Frattini 論法は mathlib の
`Sylow.normalizer_sup_eq_top` を ambient `↥N_G(A)`, normal `C_G(A).subgroupOf N_G(A)` に
適用し、`N_{N_G(A)}(Q₁)` の元が cyclic 一意性 (`le_of_ne_bot_of_le_cyclic`) で `Q₀` も
正規化することによる。`Q` は `Q₁` を含む `E` の Sylow `q`-部分群で、`q ∣ |C_E(A)|` と
`q ∣ [E : C_E(A)]` から `q² ∣ |E|`、よって `q² ≤ |Q|`。 -/
private theorem exists_line_package [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {q : ℕ} [Fact q.Prime]
    (hqi : q ∈ (((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).index).primeFactors)
    (hqc : q ∈ (Nat.card ↥(E ⊓ Subgroup.centralizer (A : Set G))).primeFactors) :
    ∃ Q Q₀ : Subgroup G, Q₀ ≤ Q ∧ Q ≤ E ∧ IsCyclic ↥Q ∧ IsPGroup q ↥Q ∧
      q ^ 2 ≤ Nat.card ↥Q ∧ Q₀ ∈ elemAbelianOfRank G q 1 ∧
      Q₀ ≤ Subgroup.centralizer (A : Set G) ∧
      (∀ T : Subgroup G, Subgroup.centralizer (A : Set G) ≤ T →
        Subgroup.normalizer (Q₀ : Set G) ≤ T →
        Subgroup.normalizer (A : Set G) ≤ T) := by
  classical
  have hq_prime : q.Prime := (Fact.out : q.Prime)
  -- `C_G(A) ≤ E` (Corollary 12.6(b)), so `E ⊓ C_G(A) = C_G(A)`.
  have hCE : Subgroup.centralizer (A : Set G) ≤ E :=
    (centralizer_le_E_of_tau2 hG h hp hA hAE).1
  set C : Subgroup G := Subgroup.centralizer (A : Set G) with hCdef
  set N : Subgroup G := Subgroup.normalizer (A : Set G) with hNdef
  have hEC : E ⊓ C = C := inf_eq_right.mpr hCE
  have hqC : q ∣ Nat.card ↥C := by
    have h1 := (Nat.mem_primeFactors.mp hqc).2.1
    rwa [hEC] at h1
  have hoddq : Odd q :=
    hG.odd.of_dvd_nat (hqC.trans (Subgroup.card_subgroup_dvd_card _))
  -- `q ∈ τ₁(M)` (Corollary 12.10(c)): every `q`-subgroup of `M` is cyclic.
  have hqτ₁ : q ∈ tau1 M :=
    ((nilpotent_sigmaComplement_abelian hG h).2.2.1 p (Fact.out : p.Prime) hp A hA hAE).2.2
      q hqi
  have hcyc_of_le : ∀ X : Subgroup G, X ≤ M → IsPGroup q ↥X → IsCyclic ↥X := by
    intro X hXM hXq
    refine S10.isCyclic_of_pRank_le_one hXq hoddq ?_
    have h1 : pRank ↥X q ≤ pRank ↥M q :=
      pRank_le_of_injective (f := Subgroup.inclusion hXM) (Subgroup.inclusion_injective hXM)
    rwa [tau1_pRank_eq_one hqτ₁] at h1
  -- `C* := C.subgroupOf N` is normal in `↥N` (`N_G(A) ≤ N_G(C_G(A))`).
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  have hCnormal : ((C.subgroupOf N)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr
      (normalizer_le_normalizer_centralizer A)
  -- Sylow `q`-subgroup of `C*` and its `G`-level image `Q₁ ≤ C`.
  obtain ⟨QC⟩ : Nonempty (Sylow q ↥(C.subgroupOf N)) := inferInstance
  set QCbar : Subgroup ↥N :=
    (QC : Subgroup ↥(C.subgroupOf N)).map (C.subgroupOf N).subtype with hQCbardef
  set Q₁ : Subgroup G := QCbar.map N.subtype with hQ₁def
  have hQ₁C : Q₁ ≤ C := by
    rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact z.2
  have hQ₁pg : IsPGroup q ↥Q₁ :=
    (QC.isPGroup'.map (C.subgroupOf N).subtype).map N.subtype
  have hQ₁card_dvd : q ∣ Nat.card ↥Q₁ := by
    have hcard : Nat.card ↥Q₁ = Nat.card ↥(QC : Subgroup ↥(C.subgroupOf N)) := by
      rw [hQ₁def, hQCbardef, Subgroup.card_map_of_injective N.subtype_injective,
        Subgroup.card_map_of_injective (C.subgroupOf N).subtype_injective]
    rw [hcard, Sylow.card_eq_multiplicity]
    refine dvd_pow_self q ?_
    have hCC : Nat.card ↥(C.subgroupOf N) = Nat.card ↥C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv
    have hpos : 0 < (Nat.card ↥(C.subgroupOf N)).factorization q := by
      rw [hCC]
      exact Nat.Prime.factorization_pos_of_dvd hq_prime Nat.card_pos.ne' hqC
    exact hpos.ne'
  have hQ₁M : Q₁ ≤ M := hQ₁C.trans (hCE.trans h.E_le)
  have hQ₁cyc : IsCyclic ↥Q₁ := hcyc_of_le Q₁ hQ₁M hQ₁pg
  -- the line `Q₀ ≤ Q₁` (Cauchy + `zpowers`).
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q₁) q hQ₁card_dvd
  set Q₀ : Subgroup G := Subgroup.zpowers ((x₀ : G)) with hQ₀def
  have hordx₀ : orderOf ((x₀ : G)) = q := by
    rw [← hx₀]
    exact orderOf_injective Q₁.subtype Q₁.subtype_injective x₀
  have hQ₀card : Nat.card ↥Q₀ = q := by
    rw [hQ₀def, Nat.card_zpowers, hordx₀]
  have hQ₀Q₁ : Q₀ ≤ Q₁ := by
    rw [hQ₀def]
    exact Subgroup.zpowers_le.mpr x₀.2
  have hQ₀mem : Q₀ ∈ elemAbelianOfRank G q 1 := by
    refine mem_elemAbelianOfRank.mpr
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hQ₀card, ?_⟩
    rw [pow_one]
    exact hQ₀card
  -- Frattini property.
  have hfrat : ∀ T : Subgroup G, C ≤ T → Subgroup.normalizer (Q₀ : Set G) ≤ T → N ≤ T := by
    intro T hCT hQ₀T
    have hfr := Sylow.normalizer_sup_eq_top (P := QC)
    intro x hx
    have hxtop : (⟨x, hx⟩ : ↥N) ∈
        Subgroup.normalizer (QCbar : Set ↥N) ⊔ C.subgroupOf N := by
      rw [hfr]
      exact Subgroup.mem_top _
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hxtop
    obtain ⟨h₁, hh₁, c₁, hc₁, hxeq⟩ := hxtop
    -- `h₁` normalizes `Q₁` in `G`, hence normalizes its unique line `Q₀`.
    have hh₁Q₁ : MulAut.conj ((h₁ : ↥N) : G) • Q₁ = Q₁ := by
      have hsmul : MulAut.conj h₁ • QCbar = QCbar :=
        conj_smul_eq_self_of_mem_normalizer hh₁
      have hmap := congrArg (fun X : Subgroup ↥N => X.map N.subtype) hsmul
      simp only [map_subtype_conj_smul] at hmap
      rw [hQ₁def]
      exact hmap
    have hh₁Q₀ : MulAut.conj ((h₁ : ↥N) : G) • Q₀ = Q₀ := by
      have hle : (MulAut.conj ((h₁ : ↥N) : G) • Q₀ : Subgroup G) ≤ Q₁ := by
        rw [← hh₁Q₁]
        exact conj_smul_mono _ hQ₀Q₁
      have hne : (MulAut.conj ((h₁ : ↥N) : G) • Q₀ : Subgroup G) ≠ ⊥ := by
        intro hbot
        have hcard := card_conj_smul ((h₁ : ↥N) : G) Q₀
        rw [hbot, Subgroup.card_bot, hQ₀card] at hcard
        exact hq_prime.one_lt.ne hcard
      have hQ₀le : Q₀ ≤ MulAut.conj ((h₁ : ↥N) : G) • Q₀ :=
        le_of_ne_bot_of_le_cyclic hQ₁cyc hQ₁pg hQ₀Q₁ hQ₀card hle hne
      exact (Subgroup.eq_of_le_of_card_ge hQ₀le
        (le_of_eq (card_conj_smul ((h₁ : ↥N) : G) Q₀))).symm
    have hh₁T : ((h₁ : ↥N) : G) ∈ T :=
      hQ₀T (mem_normalizer_of_conj_smul_eq_self hh₁Q₀)
    have hc₁T : ((c₁ : ↥N) : G) ∈ T := hCT (Subgroup.mem_subgroupOf.mp hc₁)
    have hxval : x = ((h₁ : ↥N) : G) * ((c₁ : ↥N) : G) :=
      (congrArg Subtype.val hxeq).symm
    rw [hxval]
    exact T.mul_mem hh₁T hc₁T
  -- `Q`: a Sylow `q`-subgroup of `E` containing `Q₁`.
  have hQ₁E : Q₁ ≤ E := hQ₁C.trans hCE
  obtain ⟨QE, hQ₁QE⟩ :=
    (hQ₁pg.of_equiv (Subgroup.subgroupOfEquivOfLe hQ₁E).symm).exists_le_sylow
  set Q : Subgroup G := (QE : Subgroup ↥E).map E.subtype with hQdef
  have hQE' : Q ≤ E := Subgroup.map_subtype_le _
  have hQpg : IsPGroup q ↥Q :=
    QE.isPGroup'.of_equiv (Subgroup.equivMapOfInjective _ _ E.subtype_injective)
  have hQcyc : IsCyclic ↥Q := hcyc_of_le Q (hQE'.trans h.E_le) hQpg
  have hQ₁Q : Q₁ ≤ Q := by
    intro x hxQ₁
    rw [hQdef]
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hQ₁E hxQ₁⟩, hQ₁QE (Subgroup.mem_subgroupOf.mpr hxQ₁), rfl⟩
  -- `q² ∣ |E|` and `|Q| = q ^ ν_q(E)`, hence `q² ≤ |Q|`.
  have hq2E : q ^ 2 ∣ Nat.card ↥E := by
    have h1 := Subgroup.card_mul_index ((E ⊓ C).subgroupOf E)
    have h2 : Nat.card ↥((E ⊓ C).subgroupOf E) = Nat.card ↥(E ⊓ C : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have hqdvd1 : q ∣ Nat.card ↥(E ⊓ C : Subgroup G) := (Nat.mem_primeFactors.mp hqc).2.1
    have hqdvd2 : q ∣ ((E ⊓ C).subgroupOf E).index := (Nat.mem_primeFactors.mp hqi).2.1
    calc q ^ 2 = q * q := sq q
      _ ∣ Nat.card ↥((E ⊓ C).subgroupOf E) * ((E ⊓ C).subgroupOf E).index :=
          Nat.mul_dvd_mul (h2 ▸ hqdvd1) hqdvd2
      _ = Nat.card ↥E := h1
  have hQbig : q ^ 2 ≤ Nat.card ↥Q := by
    have hcardQ : Nat.card ↥Q = Nat.card ↥(QE : Subgroup ↥E) :=
      Subgroup.card_map_of_injective E.subtype_injective
    rw [hcardQ, Sylow.card_eq_multiplicity]
    exact Nat.pow_le_pow_right hq_prime.one_lt.le
      ((Nat.Prime.pow_dvd_iff_le_factorization hq_prime Nat.card_pos.ne').mp hq2E)
  exact ⟨Q, Q₀, hQ₀Q₁.trans hQ₁Q, hQE', hQcyc, hQpg, hQbig, hQ₀mem, hQ₀Q₁.trans hQ₁C, hfrat⟩

/-- **BG Lemma 12.11(c)** (mmd L3320, 証明 L3328-3334): `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)`,
`M* ∈ ℳ(N_G(A))` で `q ∈ π(E/C_E(A)) ∩ π(C_E(A))` のとき、`q ∈ τ₂(M*)`、`G` のある
Sylow `p`-部分群が `M*` で正規 (`M* ≤ N_G(P)`)、かつ `M*` は `G` の abelian Sylow
`q`-部分群を含む。

証明: line パッケージの `Q₀` (位数 `q`, `≤ C_G(A)`) に対し `M** ∈ ℳ(N_G(Q₀))` を取る。
`A ≤ C_G(Q₀) ≤ M**` から Proposition 12.4(a) で `C_G(A) ≤ M**`、Frattini 性で
`N_G(A) ≤ M**`。(b) と Lemma 12.2(a) (`prime_mem_sigma_or_tau2`) を `M**` に適用して
`q ∈ τ₂(M**)`。(a) より `p ∈ σ(M*) ∩ σ(M**)` なので Corollary 12.6(f) (`M**` 基準) で
`M**` と `M*` は共役、Theorem 10.1(b) の transitivity (`c ∈ C_G(A) ≤ M*`) で `M* = M**`。
`q ∈ τ₂(M*)` から Theorem 12.5(a) で `M*_σ` nilpotent、その Sylow `p` (= `G` の
Sylow `p`、`p ∈ σ(M*)`) は characteristic で `M*` 正規。最後に `G` の Sylow `q` が
abelian なら Lemma 12.8(c) の chain で `S ≤ E* ≤ M*`; nonabelian なら Theorem 12.7 の
canonical line `A₀` と補群 `E₀` から `K' := E₀ ⊔ M*_σ` (`[M* : K'] = q`) を作り、
`Q` を `M*` 内共役で `E₂*` に押し込むと cyclic 一意性で `Q₀^w = A₀` となるが、
`q² ≤ |Q^w|` の cyclic `Q^w` に対し `A₀ = Ω₁(Q^w)` は `M*` に補群を持てず
(`no_complement_of_lt_cyclic`) 矛盾。 -/
theorem tau2_normalSylow_abelianSylow_of_mem_index_card [Finite G]
    (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (A : Set G)))
    {q : ℕ}
    (hqi : q ∈ (((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).index).primeFactors)
    (hqc : q ∈ (Nat.card ↥(E ⊓ Subgroup.centralizer (A : Set G))).primeFactors) :
    q ∈ tau2 Mstar ∧
    (∃ P : Sylow p G, Mstar ≤ Subgroup.normalizer ((P : Subgroup G) : Set G)) ∧
    (∃ Q : Sylow q G, (Q : Subgroup G) ≤ Mstar ∧ IsMulCommutative ↥(Q : Subgroup G)) := by
  classical
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hqi
  have : Fact q.Prime := ⟨hq_prime⟩
  obtain ⟨hMst_co, hNMst⟩ := mem_maximalSubgroupsContaining.mp hMstar
  have hMst_mem : Mstar ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMst_co
  have hAne : A ≠ ⊥ := by
    intro hbot
    have hcard := hA.2
    rw [hbot, Subgroup.card_bot] at hcard
    exact (Nat.one_lt_pow two_ne_zero (Fact.out : p.Prime).one_lt).ne' hcard.symm
  -- line パッケージ。
  obtain ⟨Q, Q₀, hQ₀Q, hQE, hQcyc, hQpg, hQbig, hQ₀mem, hQ₀C, hfrat⟩ :=
    exists_line_package hG h hp hA hAE hqi hqc
  have hQ₀ne : Q₀ ≠ ⊥ := by
    intro hbot
    have hcard := hQ₀mem.2
    rw [hbot, Subgroup.card_bot, pow_one] at hcard
    exact hq_prime.one_lt.ne hcard
  have hQ₀M : Q₀ ≤ M := (hQ₀Q.trans hQE).trans h.E_le
  -- `M** ∈ ℳ(N_G(Q₀))`。
  have hNQ₀lt : Subgroup.normalizer (Q₀ : Set G) < ⊤ :=
    normalizer_lt_top_of_le_of_ne_bot hG h.mem_maximal hQ₀M hQ₀ne
  obtain ⟨Mstst, hMss_co, hNQMss⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer (Q₀ : Set G))).resolve_left hNQ₀lt.ne
  have hMss_mem : Mstst ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMss_co
  -- `A ≤ M**`, `C_G(A) ≤ M**` (Proposition 12.4(a)), `N_G(A) ≤ M**` (Frattini 性)。
  have hACQ₀ : A ≤ Subgroup.centralizer (Q₀ : Set G) := le_centralizer_swap hQ₀C
  have hAMss : A ≤ Mstst :=
    ((hACQ₀.trans (Subgroup.centralizer_le_normalizer _)).trans hNQMss)
  have hCMss : Subgroup.centralizer (A : Set G) ≤ Mstst :=
    centralizer_le_of_elemAb_rank_two hG hMss_mem hA hAMss
  have hNAMss : Subgroup.normalizer (A : Set G) ≤ Mstst := hfrat Mstst hCMss hNQMss
  have hMstar2 : Mstst ∈ maximalSubgroupsContaining (Subgroup.normalizer (A : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨hMss_co, hNAMss⟩
  -- (b) + Lemma 12.2(a) at `M**` ⟹ `q ∈ τ₂(M**)`。
  have hq12 : q ∈ tau1 Mstst ∪ tau2 Mstst :=
    index_primeFactors_subset_tau1_union_tau2 hG h hp hA hAE hMstar2 hqi
  have hqτ₂ss : q ∈ tau2 Mstst := by
    rcases prime_mem_sigma_or_tau2 hG h.mem_maximal hQ₀M hQ₀ne hQ₀mem.1.isPGroup
      (mem_maximalSubgroupsContaining.mpr ⟨hMss_co, hNQMss⟩) with hσ | hτ₂
    · rcases hq12 with h1 | h2
      · exact absurd hσ h1.1
      · exact h2
    · exact hτ₂
  -- (a) at `M*` and `M**`: `p ∈ σ(M*) ∩ σ(M**)`。
  have hpσst : p ∈ S10.sigma Mstar :=
    mem_sigma_of_tau2_of_mem_maximalContaining hG h hp hA hAE hMstar
  have hpσss : p ∈ S10.sigma Mstst :=
    mem_sigma_of_tau2_of_mem_maximalContaining hG h hp hA hAE hMstar2
  -- `M**` 側の E-setup と `A_q ∈ ℰ_q²(E**)` (押し込み)。
  obtain ⟨Es, E1s, E2s, E3s, hs⟩ := exists_subgroupESetup hG hMss_mem
  obtain ⟨A₁, hA₁, hA₁M⟩ := exists_mem_elemAbelianOfRank_two_le_of_tau2 hq_prime hqτ₂ss
  obtain ⟨w₁, hw₁M, hw₁le⟩ := exists_conj_smul_le_hallPiece hG hs hs.E₂_le hs.E₂_hall
    (tau2_subset_sigma_compl Mstst) hA₁M (by
      intro r hr
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₁M).toEquiv, hA₁.2,
        Nat.primeFactors_pow q two_ne_zero, Nat.Prime.primeFactors hq_prime] at hr
      rw [Finset.mem_singleton.mp hr]
      exact hqτ₂ss)
  set Aq : Subgroup G := MulAut.conj w₁ • A₁ with hAqdef
  have hAq : Aq ∈ elemAbelianOfRank G q 2 := conj_smul_mem_elemAbelianOfRank w₁ hA₁
  have hAqEs : Aq ≤ Es := hw₁le.trans hs.E₂_le
  -- Corollary 12.6(f) (`M**` 基準): `p ∈ σ(M**) ∩ σ(M*)` から `M**` と `M*` は共役。
  have hconj : ∃ g : G, MulAut.conj g • Mstst = Mstar := by
    by_contra hnc
    have hdisj :=
      ((elemAb_normal_in_E_of_tau2 hG hs hqτ₂ss hAq hAqEs).2.2.2.2.2 Mstar hMst_mem hnc).2
    exact (Set.disjoint_left.mp hdisj hpσss) hpσst
  obtain ⟨g, hg⟩ := hconj
  -- Theorem 10.1(b) transitivity: `M* = M**`。
  have hA_in_g : A ≤ MulAut.conj g • Mstst := by
    rw [hg]
    exact Subgroup.le_normalizer.trans hNMst
  have hA_in_1 : A ≤ MulAut.conj (1 : G) • Mstst := by
    rw [map_one, one_smul]
    exact hAMss
  obtain ⟨c, hcC, hceq⟩ :=
    (S10.fusion_control_of_mem_sigma hG hMss_mem hpσss hAne hA.1.isPGroup).2.1
      g 1 hA_in_g hA_in_1
  rw [map_one, one_smul, hg] at hceq
  have hcMst : c ∈ Mstar := hNMst (Subgroup.centralizer_le_normalizer _ hcC)
  have hMeq : Mstar = Mstst := by
    rw [← hceq]
    exact (conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hcMst)).symm
  rw [← hMeq] at hs hqτ₂ss
  -- 以後 `M*` 側で作業。Theorem 12.5(a): `M*_σ` nilpotent。
  have hAqMst : Aq ≤ Mstar := hAqEs.trans hs.E_le
  have hnilp : Group.IsNilpotent ↥(S10.Msigma Mstar) :=
    (Msigma_nilpotent_of_tau2 hG hMst_mem hqτ₂ss hAq hAqMst).1
  have hMnormMσ : Mstar ≤ Subgroup.normalizer ((S10.Msigma Mstar) : Set G) :=
    le_normalizer_opiCoreInG _ _
  refine ⟨hqτ₂ss, ?_, ?_⟩
  · -- `G` の Sylow `p`-部分群で `M*` 正規のものが存在 (`O_p(M*) ∈ Syl_p(G)`)。
    obtain ⟨S, hSle, -⟩ := S10.exists_sylow_le_normalizer_le_of_mem_sigma hpσst
    have hSMσ : (S : Subgroup G) ≤ S10.Msigma Mstar := by
      refine S10.sigma_subgroup_le_Msigma_of_isHall (S10.Msigma_isHall hG hMst_mem) hSle ?_
      intro r hr
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
      rw [hn] at hr
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · rw [pow_zero] at hr
        simp at hr
      · rw [Nat.primeFactors_pow p hn0.ne', Nat.Prime.primeFactors (Fact.out : p.Prime)] at hr
        rw [Finset.mem_singleton.mp hr]
        exact hpσst
    set PW : Sylow p ↥(S10.Msigma Mstar) := S.subtype hSMσ with hPWdef
    have hPW_norm : (PW : Subgroup ↥(S10.Msigma Mstar)).Normal := by
      have htfae := (Group.isNilpotent_of_finite_tfae (G := ↥(S10.Msigma Mstar))).out 0 3
      exact htfae.mp hnilp p ⟨Fact.out⟩ PW
    have hPW_char : (PW : Subgroup ↥(S10.Msigma Mstar)).Characteristic :=
      Sylow.characteristic_of_normal PW hPW_norm
    have h1 := OddOrder.BG.AppB.normalizer_le_normalizer_map_of_characteristic
      (K := S10.Msigma Mstar) (W := (PW : Subgroup ↥(S10.Msigma Mstar)))
    have hmapeq : ((PW : Subgroup ↥(S10.Msigma Mstar)).map (S10.Msigma Mstar).subtype)
        = (S : Subgroup G) := by
      rw [hPWdef, Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype, inf_of_le_left hSMσ]
    rw [hmapeq] at h1
    exact ⟨S, hMnormMσ.trans h1⟩
  · -- `M*` は `G` の abelian Sylow `q`-部分群を含む。
    obtain ⟨SylAq, hAqSyl⟩ := hAq.1.isPGroup.exists_le_sylow
    by_cases hab : IsMulCommutative ↥(SylAq : Subgroup G)
    · -- abelian: Lemma 12.8(c) chain `S ≤ N(S)' ≤ F(E*) ≤ C(S) ≤ E* ≤ M*`。
      have hchain := sylow_chain_of_abelianSylow hG hs hqτ₂ss hAq hAqEs hAqSyl hab
      exact ⟨SylAq,
        (hchain.1.trans (hchain.2.1.trans (hchain.2.2.1.trans hchain.2.2.2))).trans hs.E_le,
        hab⟩
    · -- nonabelian: Theorem 12.7 の補群と cyclic 一意性で矛盾。
      exfalso
      obtain ⟨hprime_eq, A₀, hA₀eq, hA₀card, ⟨hF, hbotσ⟩, hc, E₀, hE₀E, hE₀bot, hE₀sup, -⟩ :=
        tau2_singleton_of_nonabelianSylow hG hs hqτ₂ss hAq hAqEs ⟨SylAq, hab⟩
      -- `Q` を `M*` 内共役で `E₂*` に押し込む。
      have hEN : E ≤ Subgroup.normalizer (A : Set G) :=
        E_le_normalizer_of_tau2 hG h hp hA hAE
      have hQMst : Q ≤ Mstar := (hQE.trans hEN).trans hNMst
      obtain ⟨w, hwMst, hwle⟩ := exists_conj_smul_le_hallPiece hG hs hs.E₂_le hs.E₂_hall
        (tau2_subset_sigma_compl Mstar) hQMst (by
          intro r hr
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQMst).toEquiv] at hr
          obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQpg
          rw [hn] at hr
          rcases Nat.eq_zero_or_pos n with rfl | hn0
          · rw [pow_zero] at hr
            simp at hr
          · rw [Nat.primeFactors_pow q hn0.ne', Nat.Prime.primeFactors hq_prime] at hr
            rw [Finset.mem_singleton.mp hr]
            exact hqτ₂ss)
      set Qw : Subgroup G := MulAut.conj w • Q with hQwdef
      set Q₀w : Subgroup G := MulAut.conj w • Q₀ with hQ₀wdef
      have hQ₀wQw : Q₀w ≤ Qw := conj_smul_mono _ hQ₀Q
      have hQ₀w_mem : Q₀w ∈ elemAbelianOfRank G q 1 := conj_smul_mem_elemAbelianOfRank w hQ₀mem
      have hQ₀wEs : Q₀w ≤ Es := (conj_smul_mono _ hQ₀Q).trans (hwle.trans hs.E₂_le)
      -- `⊥ ≠ A^w ≤ M*_σ ⊓ C_G(Q₀^w)`、よって Theorem 12.7(c) から `Q₀^w = A₀`。
      have hAMσ : A ≤ S10.Msigma Mstar :=
        le_Msigma_of_mem_elemAbelianOfRank_of_mem_sigma hG hMst_mem
          (Fact.out : p.Prime) hpσst hA (Subgroup.le_normalizer.trans hNMst)
      have hAwMσ : (MulAut.conj w • A : Subgroup G) ≤ S10.Msigma Mstar := by
        calc (MulAut.conj w • A : Subgroup G)
            ≤ MulAut.conj w • S10.Msigma Mstar := conj_smul_mono _ hAMσ
          _ = S10.Msigma Mstar :=
              conj_smul_eq_self_of_mem_normalizer (hMnormMσ hwMst)
      have hAwC : (MulAut.conj w • A : Subgroup G) ≤ Subgroup.centralizer (Q₀w : Set G) := by
        rw [hQ₀wdef, ← centralizer_conj_smul]
        exact conj_smul_mono _ hACQ₀
      have hAwne : (MulAut.conj w • A : Subgroup G) ≠ ⊥ := by
        intro hbot
        have hcard := card_conj_smul w A
        rw [hbot, Subgroup.card_bot, hA.2] at hcard
        exact (Nat.one_lt_pow two_ne_zero (Fact.out : p.Prime).one_lt).ne hcard
      have hQ₀wA₀ : Q₀w = A₀ := by
        by_contra hne
        refine hAwne ?_
        rw [← le_bot_iff, ← (hc Q₀w hQ₀w_mem hQ₀wEs hne).1]
        exact le_inf hAwMσ hAwC
      -- `K' := E₀ ⊔ M*_σ`: `|K'| · q = |M*|` かつ `A₀ ⊓ K' = ⊥`。
      have hE₀Mst : E₀ ≤ Mstar := hE₀E.trans hs.E_le
      have hE₀Mσ_bot : E₀ ⊓ S10.Msigma Mstar = ⊥ := by
        rw [← le_bot_iff, ← hs.E_compl_inf, inf_comm]
        exact inf_le_inf_left _ hE₀E
      have hcardK' : Nat.card ↥(E₀ ⊔ S10.Msigma Mstar : Subgroup G)
          = Nat.card ↥E₀ * Nat.card ↥(S10.Msigma Mstar) :=
        card_sup_eq_mul_of_le_normalizer_of_disjoint (hE₀Mst.trans hMnormMσ) hE₀Mσ_bot
      have hEsNA₀ : Es ≤ Subgroup.normalizer (A₀ : Set G) := by
        rw [hA₀eq]
        exact le_normalizer_inf (E_le_normalizer_of_tau2 hG hs hqτ₂ss hAq hAqEs)
          ((hs.E_le.trans hMnormMσ).trans (normalizer_le_normalizer_centralizer _))
      have hcardEs : Nat.card ↥Es = Nat.card ↥E₀ * q := by
        have h1 : Nat.card ↥(E₀ ⊔ A₀ : Subgroup G) = Nat.card ↥E₀ * Nat.card ↥A₀ :=
          card_sup_eq_mul_of_le_normalizer_of_disjoint (hE₀E.trans hEsNA₀)
            (by rw [inf_comm]; exact hE₀bot)
        rw [sup_comm, hE₀sup, hA₀card] at h1
        exact h1
      have hsplit := card_Msigma_mul_card_E hs
      have hKcard : Nat.card ↥(E₀ ⊔ S10.Msigma Mstar : Subgroup G) * q
          = Nat.card ↥Mstar := by
        rw [hcardK', ← hsplit, hcardEs]
        ring
      have hK'Mst : E₀ ⊔ S10.Msigma Mstar ≤ Mstar :=
        sup_le hE₀Mst (S10.Msigma_le _)
      have hinfK : A₀ ⊓ (E₀ ⊔ S10.Msigma Mstar) = ⊥ := by
        by_contra hne
        have hA₀le : A₀ ≤ E₀ ⊔ S10.Msigma Mstar := by
          have hcard_inf : Nat.card ↥(A₀ ⊓ (E₀ ⊔ S10.Msigma Mstar) : Subgroup G) ∣ q := by
            rw [← hA₀card]
            exact Subgroup.card_dvd_of_le inf_le_left
          rcases (Nat.dvd_prime hq_prime).mp hcard_inf with h1 | h1
          · exact absurd (Subgroup.card_eq_one.mp h1) hne
          · have heq : A₀ ⊓ (E₀ ⊔ S10.Msigma Mstar) = A₀ :=
              Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hA₀card])
            rw [← heq]
            exact inf_le_right
        have hMle : Mstar ≤ E₀ ⊔ S10.Msigma Mstar := by
          conv_lhs => rw [← hs.E_compl_sup]
          refine sup_le le_sup_right ?_
          rw [← hE₀sup]
          exact sup_le hA₀le le_sup_left
        have hcardle : Nat.card ↥Mstar ≤ Nat.card ↥(E₀ ⊔ S10.Msigma Mstar : Subgroup G) :=
          Subgroup.card_le_of_le hMle
        rw [← hKcard] at hcardle
        have hpos : 0 < Nat.card ↥(E₀ ⊔ S10.Msigma Mstar : Subgroup G) := Nat.card_pos
        nlinarith [hq_prime.one_lt]
      -- `no_complement_of_lt_cyclic` で矛盾。
      have hQwcyc : IsCyclic ↥Qw := by
        rw [hQwdef, mulAut_smul_eq_map]
        exact isCyclic_of_surjective _
          (Subgroup.equivMapOfInjective Q _ (MulAut.conj w).injective).surjective
      have hQwpg : IsPGroup q ↥Qw := by
        rw [hQwdef, mulAut_smul_eq_map]
        exact hQpg.of_equiv (Subgroup.equivMapOfInjective Q _ (MulAut.conj w).injective)
      have hQwMst : Qw ≤ Mstar := (hwle.trans hs.E₂_le).trans hs.E_le
      have hQbig' : q ^ 2 ≤ Nat.card ↥Qw := by
        rw [hQwdef, card_conj_smul]
        exact hQbig
      exact no_complement_of_lt_cyclic hQwcyc hQwpg hQwMst hK'Mst
        (hQ₀wA₀ ▸ hQ₀wQw) hA₀card hQbig' hinfK hKcard

/-- **BG Lemma 12.11** (mmd L3318): `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)`, `M* ∈ ℳ(N_G(A))` のとき
(a) `τ₂(M)` の素数は `σ(M*) − β(M*)` に入る; (b) `π(E/C_E(A)) ⊆ τ₁(M*) ∪ τ₂(M*)`;
(c) `q ∈ π(E/C_E(A)) ∩ π(C_E(A))` なら `q ∈ τ₂(M*)`, `G` のある Sylow `p`-部分群が
`M*` で正規, `M*` は `G` の abelian Sylow `q`-部分群を含む。

((a) は scaffold の `tau2 M ⊆ σ(M*) − β(M*)` から素数限定形へ faithful 化 — repo の
`tau2` は pRank 条件のみで合成数を排除しないため。12.3/12.7(a)/12.10(c) と同型の訂正。) -/
theorem tau2_transfer_to_maximal [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (A : Set G))) :
    (∀ q : ℕ, q.Prime → q ∈ tau2 M → q ∈ S10.sigma Mstar \ S10.beta Mstar) ∧
    (∀ r ∈ (((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).index).primeFactors,
      r ∈ tau1 Mstar ∪ tau2 Mstar) ∧
    (∀ q : ℕ, q ∈ (((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).index).primeFactors →
      q ∈ (Nat.card ↥(E ⊓ Subgroup.centralizer (A : Set G))).primeFactors →
      q ∈ tau2 Mstar ∧
      (∃ P : Sylow p G, Mstar ≤ Subgroup.normalizer ((P : Subgroup G) : Set G)) ∧
      (∃ Q : Sylow q G, (Q : Subgroup G) ≤ Mstar ∧ IsMulCommutative ↥(Q : Subgroup G))) :=
  ⟨fun _q hq_prime hq => tau2_prime_mem_sigma_diff_beta hG h hp hA hAE hMstar hq_prime hq,
   fun _r hr => index_primeFactors_subset_tau1_union_tau2 hG h hp hA hAE hMstar hr,
   fun _q hqi hqc =>
     tau2_normalSylow_abelianSylow_of_mem_index_card hG h hp hA hAE hMstar hqi hqc⟩

end OddOrder.BG.Ch3.S12


