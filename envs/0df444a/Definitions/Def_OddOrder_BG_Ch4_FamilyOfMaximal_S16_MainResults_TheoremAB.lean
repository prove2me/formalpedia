-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TheoremAB
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TheoremAB
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T10:26:00.958836+00:00
-- url     : https://prove2.me/theorems/ed289d96-4900-4ee3-9675-0598e2421e51
-- title:
--   BG §16: Theorems A and B, the component layer
-- statement:
--   The component layer for Theorems A and B of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §16: the ungated conjuncts of Theorem A, the parts of Theorem B (a Sylow abelian $U$ of rank at most 2, the TI-subset statement, tameness) and the bridging lemmas between the $\kappa$- and $\sigma$-complements. It consists of lemmas only.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 10 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/TheoremAB.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/TheoremAB.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_Notation

namespace OddOrder.BG.Ch4.S16

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch4.S14

open OddOrder.BG.Ch4.S15

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BG Theorem A(3) decomposition** (mmd L4276): `M = K U M_σ`.  For a maximal `M` with Hall
`κ`-subgroup `K ≤ M` and Hall `(κ ∪ σ)'`-subgroup `U ≤ M`, the three factors join to all of `M`.

Type-F (`K = ⊥`): `M = U M_σ` from the `K = ⊥` `SubgroupESetup` (`E_compl_sup`).  Type-P (`K ≠ ⊥`):
`M' = U M_σ` and `M'` complements `K` in `M` (`typeP_auxiliary_structure`, Lemma 15.1(b)/Theorem
14.7(h)), so `M = M' K = (U M_σ) K`; the complement's `H ⊔ K = ⊤` is pushed from `M` to `G` via
`Subgroup.map M.subtype`.  This is the standalone proof of conjunct 3 used by
`theoremA_maximal_structure_faithful`. -/
theorem typeP_maximal_eq_kappaHall_sup_U_sup_Msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKM : K ≤ M) (hUM : U ≤ M) (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    M = K ⊔ U ⊔ OddOrder.BG.Ch3.S10.Msigma M := by
  by_cases hKbot : K = ⊥
  · -- Type-F: `M = U M_σ`.
    obtain ⟨_E₁, _E₂, _E₃, hsetup⟩ :=
      subgroupESetup_of_isHall_kappa_eq_bot hG hM hKM hUM hK hKbot hU
    rw [hKbot, bot_sup_eq, sup_comm]
    exact hsetup.E_compl_sup.symm
  · -- Type-P: `M = M' K`, `M' = U M_σ`.
    have haux := typeP_auxiliary_structure hG hM hKM hUM hK rfl hU
    obtain ⟨hM'eq, _, hcompl, _⟩ := haux.2.2.2.2.1 hKbot
    have hMle : derivedInG M ≤ M := Subgroup.map_subtype_le _
    have hMM' : derivedInG M ⊔ K = M := by
      have htop : (derivedInG M ⊔ K).subgroupOf M = ⊤ := by
        rw [Subgroup.subgroupOf_sup hMle hKM]; exact hcompl.sup_eq_top
      exact le_antisymm (sup_le hMle hKM) (Subgroup.subgroupOf_eq_top.mp htop)
    -- `M = M' K = (U M_σ) K = K U M_σ` (a pure `⊔`-AC rewrite, no lattice `whnf`).
    conv_lhs => rw [← hMM']
    rw [hM'eq, sup_comm (U ⊔ OddOrder.BG.Ch3.S10.Msigma M) K, ← sup_assoc]

/-- **BG Theorem A — the ungated conjuncts** (mmd L4274), as a standalone `sorry`-free lemma.

Bundles the conjuncts used by `theoremA_maximal_structure_faithful` whose upstreams are all proved
transitively
(mirroring `theoremB_U_sylow_abelian_rank_le_two` / `sigma_reps_pairwise_disjoint`):

* A(1) `M_σ` is a `σ(M)`-Hall subgroup (`Msigma_isHall`);
* A(2) `K` cyclic (`typeP_auxiliary_structure`, Lemma 15.1(a)/Theorem 14.7(h));
* A(3) `M ≤ N_G(U M_σ)` (`typeP_auxiliary_structure`: `U M_σ = M` for type-F, `= M' ⊴ M`
  for type-P);
* A(4) `C_U(k) = 1` for `k ∈ K#` (`typeP_hall_inf_centralizer_kappaElement_eq_bot`);
* A(5) `Kstar ≠ ⊥` (`S14.typeP_structure`, with `K = ⊥` collapsing `Kstar = M_σ ≠ ⊥`) and the
  element form `C_M(k) = K ⊔ K*` for `K ≠ ⊥`, `k ∈ K#` (`typeP_centralizer_kappaElement_eq`);
* A(6) `M_F ≤ M_σ ≤ M'` (`maxNilpotentNormalHall_le_Msigma`, `Msigma_le_derived`).

The remaining faithful-monolith conjuncts are supplied separately: `M = K U M_σ` by
`typeP_maximal_eq_kappaHall_sup_U_sup_Msigma`, `M'' ≤ F(M)` by
`derivedDerived_le_fittingInAmbient`, and the `M_F ≠ M_σ` extreme A(8) by
`theoremA8_structure`.

As with the Theorem B(1) precedent the explicit `hKM : K ≤ M`, `hUM : U ≤ M` are added (part of the
BG setup `M = K U M_σ` but not forced by the Hall conditions on
`K.subgroupOf M`/`U.subgroupOf M`). -/
theorem theoremA_ungated_conjuncts [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M)) :
    Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M) (OddOrder.BG.Ch3.S10.Msigma M) ∧
      IsCyclic ↥K ∧
      M ≤ Subgroup.normalizer ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) ∧
      (∀ k ∈ K, k ≠ 1 → U ⊓ Subgroup.centralizer ({k} : Set G) = ⊥) ∧
      Kstar ≠ ⊥ ∧
      (K ≠ ⊥ → ∀ k ∈ K, k ≠ 1 → M ⊓ Subgroup.centralizer ({k} : Set G) = K ⊔ Kstar) ∧
      S15.MF M ≤ OddOrder.BG.Ch3.S10.Msigma M ∧
      OddOrder.BG.Ch3.S10.Msigma M ≤ derivedInG M := by
  -- `IsTypeP M` from a nonempty `κ`-Hall, packaged for the type-`P` conjuncts.
  have hPofne : K ≠ ⊥ → S14.IsTypeP M := fun hKne =>
    isTypeP_of_isHall_kappa_subgroupOf_ne_bot hK
      (fun h => hKne (by rw [← Subgroup.map_subgroupOf_eq_of_le hKM, h, Subgroup.map_bot]))
  have haux := typeP_auxiliary_structure hG hM hKM hUM hK hKstar hU
  have hKcyc : IsCyclic ↥K := haux.2.1
  refine ⟨OddOrder.BG.Ch3.S10.Msigma_isHall hG hM, hKcyc, haux.1, ?_, ?_, ?_,
    maxNilpotentNormalHall_le_Msigma hG hM, OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM⟩
  · -- A(4): `C_U(k) = 1`.  Vacuous for `K = ⊥`; else type-`P` element centralizer.
    intro k hk hk1
    by_cases hKbot : K = ⊥
    · rw [hKbot, Subgroup.mem_bot] at hk; exact absurd hk hk1
    · exact typeP_hall_inf_centralizer_kappaElement_eq_bot hG hM (hPofne hKbot) hKM hUM hK hKstar hU
        k hk hk1
  · -- A(5): `Kstar ≠ ⊥`.
    by_cases hKbot : K = ⊥
    · -- type-F: `Kstar = M_σ ⊓ C(1) = M_σ ≠ ⊥`.
      subst hKbot
      have hc : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
        rw [Subgroup.coe_bot, Subgroup.centralizer_eq_top_iff_subset]
        exact Set.singleton_subset_iff.mpr (Subgroup.one_mem _)
      rw [hc, inf_top_eq] at hKstar
      rw [hKstar]
      exact OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
    · exact (S14.typeP_structure hG hM (hPofne hKbot) hKM hK hKstar hU).2.1
  · -- A(5) element form: `C_M(k) = K ⊔ K*` for `K ≠ ⊥`.
    intro hKne k hk hk1
    exact typeP_centralizer_kappaElement_eq hG hM (hPofne hKne) hKM hK hKstar hU k hk hk1

/-- **BG Theorem B(1)** (mmd L4373): every Sylow subgroup of `U` is abelian of rank at most two.

Standalone, `sorry`-free form of the first conjunct of `theoremB_U_and_A_tame`, mirroring
`sigma_reps_pairwise_disjoint` (the Theorem E precedent).  Two faithfulness adjustments over the
scaffold conjunct:

* the explicit hypothesis `hUM : U ≤ M` — the §12 supporting-subgroup reduction
  (`exists_subgroupESetup_with_le`) genuinely needs `U ≤ M`, and `hU` (a Hall condition on
  `U.subgroupOf M`) does not force it; in BG `U ⊆ M` is part of the setup (`M = K U M_σ`);
* the restriction to a *prime* `p` — "Sylow subgroup" means a `p`-group for prime `p`; for a
  composite `p` the bare `IsPGroup p` hypothesis is met by non-abelian `{q, r}`-groups (e.g. a
  Frobenius `7 ⋊ 3`, possible in odd order), so the unrestricted `∀ p : ℕ` form is false.

Proof (cite-only over §12): a `p`-subgroup `P ≤ U` is a `σ(M)'`-subgroup of `M`, hence lies in a
supporting subgroup `E` with `SubgroupESetup M E …` (`exists_subgroupESetup_with_le`); then
`rank P ≤ rank E ≤ 2` (`rank_le_two`) and `P`, a prime `p`-group, is nilpotent, so abelian by
`nilpotent_sigmaComplement_abelian` (a). -/
theorem theoremB_U_sylow_abelian_rank_le_two [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hUM : U ≤ M)
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M)) :
    ∀ p : ℕ, p.Prime → ∀ P : Subgroup G, P ≤ U → IsPGroup p ↥P →
      rank ↥P ≤ 2 ∧ IsMulCommutative ↥P := by
  intro p hp P hPU hPp
  have : Fact p.Prime := ⟨hp⟩
  have hPM : P ≤ M := hPU.trans hUM
  -- `P ≤ U` is a `σ(M)'`-subgroup of `M`.
  have hP_pi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma M)ᶜ) P := by
    intro q hq
    have hqU : q ∈ (Nat.card ↥U).primeFactors :=
      Nat.primeFactors_mono (Subgroup.card_dvd_of_le hPU) Nat.card_pos.ne' hq
    intro hqσ
    exact hU.1 q (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv])
      (Set.mem_union_right _ hqσ)
  -- §12 supporting subgroup `E ⊇ P`.
  obtain ⟨E, _E₁, _E₂, _E₃, hsetup, hPE, _hE_pi⟩ :=
    exists_subgroupESetup_with_le hG hM hPM hP_pi
  refine ⟨?_, ?_⟩
  · rw [rank_le_iff]
    intro q hq
    exact le_trans (pRank_le_of_injective (Subgroup.inclusion_injective hPE))
      ((rank_le_iff.mp (hsetup.rank_le_two hG)) q hq)
  · exact (nilpotent_sigmaComplement_abelian hG hsetup).1 P hPM hP_pi
      (IsPGroup.isNilpotent hPp)

/-- Centralizer of a cyclic subgroup = centralizer of a generator. -/
private theorem centralizer_zpowers_eq_singleton_B5 (z : G) :
    Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G)
      = Subgroup.centralizer ({z} : Set G) := by
  ext c
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro hc y hy
    rw [Set.mem_singleton_iff] at hy; rw [hy]
    exact hc z (SetLike.mem_coe.mpr (Subgroup.mem_zpowers z))
  · intro hc y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (SetLike.mem_coe.mp hy)
    have hzc : Commute z c := hc z (Set.mem_singleton z)
    exact (hzc.zpow_left n).eq

/-- A maximal subgroup of a minimal simple group is self-normalizing (`N_G(M) = M`). -/
private theorem normalizer_eq_self_of_maximal_B5 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    Subgroup.normalizer (M : Set G) = M := by
  have hco : IsCoatom M := hM
  refine le_antisymm ?_ Subgroup.le_normalizer
  by_contra hle
  have hlt : M < Subgroup.normalizer (M : Set G) :=
    lt_of_le_of_ne Subgroup.le_normalizer (fun heq => hle heq.ge)
  have hnormal : M.Normal := Subgroup.normalizer_eq_top_iff.mp (hco.2 _ hlt)
  rcases hG.simple.eq_bot_or_eq_top_of_normal M hnormal with hb | ht
  · exact hG.ne_bot_of_isCoatom hco hb
  · exact hco.1 ht

/-- Conjugation of `M` by one of its own elements fixes `M`. -/
private theorem conj_smul_self_of_mem {M : Subgroup G} {g : G} (hg : g ∈ M) :
    MulAut.conj g • M = M := by
  ext z
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  have hinv : (MulAut.conj g)⁻¹ • z = g⁻¹ * z * g := by
    rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
  rw [hinv]
  constructor
  · intro hz
    have := mul_mem (mul_mem hg hz) (inv_mem hg)
    simpa [mul_assoc] using this
  · intro hz
    exact mul_mem (mul_mem (inv_mem hg) hz) hg

/-- **BG Lemma 15.1(c) / Theorem B(4), general element form**: for a maximal subgroup `M`, a Hall
`(κ ∪ σ)ᶜ`-subgroup `U ≤ M`, and a nonidentity `(κ(M) ∪ σ(M))ᶜ`-element `y ∈ M` whose
`M_σ`-centralizer is nontrivial, `C_G(y)` lies in the unique maximal subgroup `M`:
`ℳ(C_G(y)) = {M}`.

Type-independent core behind both `typeI_centralizer_le_and_unique` (Peterfalvi 8.12.b) and Theorem
B(5).  `⟨y⟩` is a `(κ ∪ σ)ᶜ`-subgroup of solvable `M`, so Hall D/C conjugate it (by `τ ∈ M`) into
`U`; Lemma 15.1(c) (`typeP_hall_small_subgroup_cyclic_tau2`) pins `ℳ(C_G(y^τ)) = {M}`; conjugating
back by `τ ∈ M = N_G(M)` recovers `ℳ(C_G(y)) = {M}`. -/
theorem uniqueMaximal_of_kappaSigmaCompl_element [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hUM : U ≤ M)
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {y : G} (hyM : y ∈ M) (hy1 : y ≠ 1)
    (hyπ : IsPiElement (S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ y)
    (hyC : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({y} : Set G) ≠ ⊥) :
    maximalSubgroupsContaining (Subgroup.centralizer ({y} : Set G)) = {M} := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  set yM : ↥M := ⟨y, hyM⟩ with hyMdef
  -- (i) `⟨y⟩` is a `(κ ∪ σ)ᶜ`-subgroup of `M`.
  have hordeq : orderOf y = orderOf yM :=
    orderOf_injective M.subtype M.subtype_injective yM
  have hZπ : ∀ q ∈ (Nat.card ↥(Subgroup.zpowers yM)).primeFactors,
      q ∈ (S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ := by
    intro q hq
    rw [Nat.card_zpowers, ← hordeq] at hq
    obtain ⟨hqp, hqdvd, -⟩ := Nat.mem_primeFactors.mp hq
    exact hyπ q (Nat.mem_primeFactors.mpr ⟨hqp, hqdvd, (orderOf_pos y).ne'⟩)
  -- (ii) Hall D + C inside `M`: conjugate `y` into `U`.
  obtain ⟨W, hWhall, hZW⟩ := OddOrder.Isaacs.Ch03.hall_D (G := ↥M) hZπ
  obtain ⟨t, htmap⟩ := OddOrder.Isaacs.Ch03.hall_C (G := ↥M) hWhall hU
  set τ : G := (t : G) with hτdef
  have hτM : τ ∈ M := t.2
  set y' : G := τ * y * τ⁻¹ with hy'def
  have hy'U : y' ∈ U := by
    have hyW : yM ∈ W := hZW (Subgroup.mem_zpowers yM)
    have hmem : (MulAut.conj t) yM ∈ W.map (MulAut.conj t).toMonoidHom := ⟨yM, hyW, rfl⟩
    rw [htmap] at hmem
    have := Subgroup.mem_subgroupOf.mp hmem
    simpa [hy'def, hτdef, MulAut.conj_apply] using this
  have hy'1 : y' ≠ 1 := by
    simp only [hy'def, ne_eq, conj_eq_one_iff]; exact hy1
  -- (iii) transported witness `M_σ ⊓ C_G(⟨y'⟩) ≠ ⊥`.
  obtain ⟨z, hzmem, hz1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hyC
  obtain ⟨hzMσ, hzC⟩ := Subgroup.mem_inf.mp hzmem
  have hz'1 : τ * z * τ⁻¹ ≠ 1 := by simpa [conj_eq_one_iff] using hz1
  have hz'Mσ : τ * z * τ⁻¹ ∈ OddOrder.BG.Ch3.S10.Msigma M := by
    have hM_le_NMσ : M ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) := by
      rw [OddOrder.BG.Ch3.S10.Msigma]; exact le_normalizer_opiCoreInG _ _
    have hMσ_norm : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (OddOrder.BG.Ch3.S10.Msigma_le M)).mpr hM_le_NMσ
    have hzMmem : (⟨z, OddOrder.BG.Ch3.S10.Msigma_le M hzMσ⟩ : ↥M) ∈
        (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M := Subgroup.mem_subgroupOf.mpr hzMσ
    have := Subgroup.mem_subgroupOf.mp (hMσ_norm.conj_mem _ hzMmem t)
    simpa [hτdef] using this
  have hz'C : τ * z * τ⁻¹ ∈ Subgroup.centralizer ({y'} : Set G) := by
    have hcomm : Commute y z := Subgroup.mem_centralizer_iff.mp hzC y (Set.mem_singleton y)
    have hcomm' : Commute y' (τ * z * τ⁻¹) := by
      have := hcomm.map (MulAut.conj τ : G →* G)
      simpa [hy'def, MulAut.conj_apply] using this
    exact Subgroup.mem_centralizer_iff.mpr fun w hw => by
      rw [Set.mem_singleton_iff] at hw; subst hw; exact hcomm'.eq
  have hCne : OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer ((Subgroup.zpowers y' : Subgroup G) : Set G) ≠ ⊥ := by
    rw [centralizer_zpowers_eq_singleton_B5]
    intro hbot
    have hmem : τ * z * τ⁻¹ ∈ OddOrder.BG.Ch3.S10.Msigma M ⊓
        Subgroup.centralizer ({y'} : Set G) := Subgroup.mem_inf.mpr ⟨hz'Mσ, hz'C⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hz'1 hmem
  -- (iv) Lemma 15.1(c) pins `ℳ(C_G(y')) = {M}`.
  have hB : maximalSubgroupsContaining (Subgroup.centralizer ({y'} : Set G)) = {M} := by
    have h := (typeP_hall_small_subgroup_cyclic_tau2 hG hM hUM hU
      (Subgroup.zpowers_le.mpr hy'U)
      (by simpa [Subgroup.zpowers_eq_bot] using hy'1) hCne).1
    rwa [centralizer_zpowers_eq_singleton_B5] at h
  -- (v) conjugate back by `τ ∈ M = N_G(M)`.
  have hCconj : Subgroup.centralizer ({y'} : Set G)
      = MulAut.conj τ • Subgroup.centralizer ({y} : Set G) := by
    rw [centralizer_pointwise_smul]
    congr 1
    simp [hy'def, MulAut.conj_apply, Set.image_singleton]
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨⟨hM, ?_⟩, ?_⟩
  · -- `C_G(y) ≤ M`.
    have hCy'M : Subgroup.centralizer ({y'} : Set G) ≤ M := by
      have := hB ▸ (Set.mem_singleton M)
      exact (mem_maximalSubgroupsContaining.mp this).2
    intro c hc
    have hc' : τ * c * τ⁻¹ ∈ Subgroup.centralizer ({y'} : Set G) := by
      rw [hCconj]; exact ⟨c, hc, by simp [MulAut.conj_apply]⟩
    have := hCy'M hc'
    have hback := mul_mem (mul_mem (inv_mem hτM) this) hτM
    simpa [mul_assoc] using hback
  · -- uniqueness.
    intro L hL
    obtain ⟨hLco, hCL⟩ := hL
    have hLconj : MulAut.conj τ • L ∈
        maximalSubgroupsContaining (Subgroup.centralizer ({y'} : Set G)) := by
      refine ⟨isCoatom_pointwise_smul (MulAut.conj τ) hLco, ?_⟩
      rw [hCconj]
      exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hCL
    rw [hB, Set.mem_singleton_iff] at hLconj
    calc L = MulAut.conj τ⁻¹ • (MulAut.conj τ • L) := by
            rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
      _ = MulAut.conj τ⁻¹ • M := by rw [hLconj]
      _ = M := conj_smul_self_of_mem (inv_mem hτM)

/-- **BG Theorem B(5)** (mmd L4373; schematic proof Lemma 15.1(c)): the set `A(M) − M_σ` is a
TI-subset of `G` (with normalizer `M`).

`A(M) = \widehat{M_σ} ∩ U M_σ`; an element `a ∈ A(M) − M_σ` has a nontrivial `(κ ∪ σ)ᶜ`-part
`w = a_π` (nontrivial because `a ∉ M_σ`, using that `a ∈ U M_σ` is a `κ(M)′`-element), and
`ℳ(C_G(w)) = {M}` by `uniqueMaximal_of_kappaSigmaCompl_element` (Lemma 15.1(c)).  If `g` conjugates
`a ∈ A(M) − M_σ` to another such element, then `w` and `g w g⁻¹` are both `π`-parts of elements of
`A(M) − M_σ` (`piPart` is conjugation-equivariant), so `ℳ(C_G(g w g⁻¹)) = {M}` too; but
`C_G(g w g⁻¹) = g C_G(w) g⁻¹`, so `g⁻¹ M g` is a maximal subgroup over `C_G(w)`, forcing
`g⁻¹ M g = M`, i.e. `g ∈ N_G(M) = M`. -/
theorem theoremB_A_minus_Msigma_isTISubset [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    IsTISubset (ASet M U \ (OddOrder.BG.Ch3.S10.Msigma M : Set G)) M := by
  classical
  set π : Set ℕ := (S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ with hπdef
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  -- normality of `U ⊔ M_σ` in `M` (Theorem A(3)), used only for the `κ′`-characterization.
  have hnorm : ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hUM hMσM)).mpr
      (theoremA_ungated_conjuncts hG hM hKM hUM hK rfl hU).2.2.1
  -- **`uniqB`**: for `a ∈ A(M) − M_σ`, the `π`-part `w = a_π` has `ℳ(C_G(w)) = {M}`.
  have huniqB : ∀ a ∈ ASet M U \ (OddOrder.BG.Ch3.S10.Msigma M : Set G),
      maximalSubgroupsContaining (Subgroup.centralizer ({piPart π a} : Set G)) = {M} := by
    intro a ha
    obtain ⟨haA, haMσ⟩ := ha
    simp only [ASet, hatMsigma, Set.mem_inter_iff, Set.mem_ofPred_eq, SetLike.mem_coe] at haA
    obtain ⟨⟨haM, haC⟩, haUMσ⟩ := haA
    -- `w = a_π`, a power of `a`, is a `π`-element of `M`.
    obtain ⟨-, -, -, -, -, hwz, -⟩ := piPart_spec π a
    have hwM : piPart π a ∈ M := (Subgroup.zpowers_le.mpr haM) hwz
    have hwπ : IsPiElement π (piPart π a) := isPiElement_piPart π a
    -- `w ≠ 1`: else `a` is a `(κ ∪ σ)`-element and (being a `κ′`-element of `U M_σ`) a `σ`-element,
    -- hence `a ∈ M_σ`, contradicting `a ∉ M_σ`.
    have hw1 : piPart π a ≠ 1 := by
      intro hw0
      have haκσ : IsPiElement (S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M) a := by
        have := isPiElement_compl_of_piPart_eq_one hw0
        rwa [hπdef, compl_compl] at this
      have haκ' : IsPiElement (S14.kappa M)ᶜ a :=
        (S14.mem_U_sup_Msigma_iff_isPiElement_kappa_compl hG hM hUM hU hnorm haM).mp haUMσ
      have haσ : IsPiElement (OddOrder.BG.Ch3.S10.sigma M) a := by
        intro p hp
        exact (haκσ p hp).resolve_left (haκ' p hp)
      exact haMσ ((S14.mem_Msigma_iff_isPiElement_sigma hG hM haM).mpr haσ)
    -- `M_σ ⊓ C_G(w) ≠ ⊥`: the witness centralizing `a` also centralizes its power `w`.
    have hwC : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({piPart π a} : Set G) ≠ ⊥ := by
      obtain ⟨z, hzmem, hz1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left haC
      obtain ⟨hzMσ, hzC⟩ := Subgroup.mem_inf.mp hzmem
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hwz
      have hzCw : z ∈ Subgroup.centralizer ({piPart π a} : Set G) := by
        refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
        rw [Set.mem_singleton_iff] at hw; subst hw
        have hcomm : Commute a z := Subgroup.mem_centralizer_iff.mp hzC a (Set.mem_singleton a)
        rw [← hn]; exact (hcomm.zpow_left n).eq
      exact fun hbot => hz1 (Subgroup.mem_bot.mp
        (hbot ▸ Subgroup.mem_inf.mpr ⟨hzMσ, hzCw⟩))
    exact uniqueMaximal_of_kappaSigmaCompl_element hG hM hUM hU hwM hw1 hwπ hwC
  -- TI: `g` overlaps `A(M) − M_σ` with its conjugate `⇒ g ∈ M`.
  intro g hg
  obtain ⟨a, ha, hga⟩ := hg
  have hMa := huniqB a ha
  have hMga := huniqB (g * a * g⁻¹) hga
  rw [piPart_conj] at hMga
  set w : G := piPart π a with hwdef
  -- `C_G(g w g⁻¹) = conj g • C_G(w)`.
  have hCconj : Subgroup.centralizer ({g * w * g⁻¹} : Set G)
      = MulAut.conj g • Subgroup.centralizer ({w} : Set G) := by
    rw [centralizer_pointwise_smul]; congr 1
    simp [MulAut.conj_apply, Set.image_singleton]
  rw [hCconj] at hMga
  -- `conj g • C_G(w) ≤ M`, so `C_G(w) ≤ conj g⁻¹ • M`.
  have hCleM : MulAut.conj g • Subgroup.centralizer ({w} : Set G) ≤ M :=
    (mem_maximalSubgroupsContaining.mp (hMga ▸ Set.mem_singleton M)).2
  have hle : Subgroup.centralizer ({w} : Set G) ≤ MulAut.conj g⁻¹ • M := by
    have h := Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj g⁻¹) |>.mpr hCleM
    rwa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h
  -- `conj g⁻¹ • M` is a maximal subgroup over `C_G(w)`; by `ℳ(C_G(w)) = {M}` it equals `M`.
  have hmemM : (MulAut.conj g⁻¹ • M) ∈
      maximalSubgroupsContaining (Subgroup.centralizer ({w} : Set G)) :=
    ⟨isCoatom_pointwise_smul _ hM, hle⟩
  rw [hMa, Set.mem_singleton_iff] at hmemM
  -- `g⁻¹ ∈ N_G(M) = M`, hence `g ∈ M`.
  have hg1norm : g⁻¹ ∈ Subgroup.normalizer (M : Set G) :=
    mem_normalizer_of_conj_smul_eq_self hmemM
  rw [normalizer_eq_self_of_maximal_B5 hG hM] at hg1norm
  simpa using inv_mem hg1norm

/-- **`κ(M) = π(M) ∖ σ(M)` from a trivial Hall `(κ ∪ σ)ᶜ`-complement** (the prime-set half of the
type-`P₁` ⟺ `U = ⊥` characterization).  If the Hall `(κ(M) ∪ σ(M))ᶜ`-subgroup of `M` is trivial,
then `(κ ∪ σ)ᶜ` contains no prime dividing `|M|` (the Hall index condition `hU.2` with index `|M|`),
so `π(M) ⊆ κ(M) ∪ σ(M)`; combined with `κ(M) ⊆ π(M) ∖ σ(M)` (every `κ`-prime is a non-`σ` divisor of
`|M|`) this gives `κ(M) = π(M) ∖ σ(M) = sigmaComplementPrimes M`.

Hoisted above `theoremC_paired_structure` (2026-06-21, lane F) so its conjunct 12 (`U = ⊥ → |K*|`
prime) can derive `IsTypeP1 M` from `U = ⊥`.  Together with
`isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot` (below) it is the prime-set core of BG's
"`M ∈ M_{P₁} ⟺ U = ⊥`": modulo `IsTypeP` (`κ ≠ ∅`), `U = ⊥ ⟺ M` is type `P₁`. -/
theorem kappa_eq_sigmaComplementPrimes_of_hall_subgroupOf_eq_bot [Finite G] {M U : Subgroup G}
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUbot : U.subgroupOf M = ⊥) :
    S14.kappa M = S14.sigmaComplementPrimes M := by
  refine Set.Subset.antisymm (fun p hpκ => ?_) (fun p hpσ' => ?_)
  · -- `κ ⊆ π ∖ σ`: a `κ`-prime is non-`σ` (`τ₁ ∪ τ₃`) and divides `|M|` (rank-one `P ≤ M`).
    obtain ⟨hpp, hτ, P, hPelem, hPM, _⟩ := hpκ
    have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M := by
      rcases hτ with h | h
      · exact ((mem_tau1_iff M p).mp h).1
      · exact ((mem_tau3_iff M p).mp h).1
    have hpπ : p ∈ S14.piSet M := by
      refine Nat.mem_primeFactors.mpr ⟨hpp, ?_, Nat.card_pos.ne'⟩
      have hPcard : Nat.card ↥P = p := by rw [hPelem.2, pow_one]
      exact hPcard ▸ Subgroup.card_dvd_of_le hPM
    exact ⟨hpπ, hpσ⟩
  · -- `π ∖ σ ⊆ κ`: `U = ⊥` forces every `|M|`-prime into `κ ∪ σ`; non-`σ` ones land in `κ`.
    obtain ⟨hpπ, hpσ⟩ := hpσ'
    by_contra hpκ
    refine hU.2 p (by rw [hUbot, Subgroup.index_bot]; exact hpπ) ?_
    rintro (h | h)
    · exact hpκ h
    · exact hpσ h

/-- **`M` is type `P₂` from a nontrivial Hall `(κ ∪ σ)ᶜ`-complement** (the type-`P₂` side of the
`M ∈ M_{P₁} ⟺ U = ⊥` characterization): a type-`P` maximal subgroup whose Hall `(κ(M) ∪ σ(M))ᶜ`-
subgroup `U` is nontrivial has `κ(M) ≠ σ'(M)`, i.e. is type `P₂`.  Dual to
`isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot`: a prime `p ∣ |U|` lies in `(κ ∪ σ)ᶜ ∩ π(M)`,
so if `κ = σ' = π ∖ σ` then `p ∈ κ` (it is a non-`σ` divisor of `|M|`), contradicting `p ∉ κ`. -/
theorem isTypeP2_of_hall_subgroupOf_ne_bot [Finite G] {M U : Subgroup G}
    (hP : S14.IsTypeP M)
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUne : U.subgroupOf M ≠ ⊥) :
    S14.IsTypeP2 M := by
  refine ⟨hP, fun hκσ => ?_⟩
  obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd
    (by rwa [ne_eq, ← Subgroup.card_eq_one] at hUne)
  have hpcompl : p ∈ (S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
    hU.1 p (Nat.mem_primeFactors.mpr ⟨hpp, hpdvd, Nat.card_pos.ne'⟩)
  have hpπ : p ∈ S14.piSet M :=
    Nat.mem_primeFactors.mpr ⟨hpp,
      hpdvd.trans (Subgroup.card_subgroup_dvd_card (U.subgroupOf M)), Nat.card_pos.ne'⟩
  have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M := fun h => hpcompl (Set.mem_union_right _ h)
  have hpκ : p ∈ S14.kappa M := by rw [hκσ]; exact ⟨hpπ, hpσ⟩
  exact hpcompl (Set.mem_union_left _ hpκ)

end OddOrder.BG.Ch4.S16


