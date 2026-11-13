-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_OpicoreCentralizerBasic
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_OpicoreCentralizerBasic
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T10:11:19.429522+00:00
-- url     : https://prove2.me/theorems/51bfbf7d-84f0-47c0-9a77-d746053c0ce2
-- title:
--   BG §15: $O_p$-core centralizer, opening layer
-- statement:
--   The opening layer of the $O_p$-core centralizer part of §15 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*. It consists of lemmas only, mostly about the failure of $F(M)$ to be TI: then $M_F=M_\sigma$, $M'\le F(M)$ and $E_3=1$; conversely $F(M)$ is TI when $M_F\ne M_\sigma$ or for type $\mathcal{P}_2$.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 6 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF/OpicoreCentralizerBasic.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF/OpicoreCentralizerBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_PisetBetaDisjoint

namespace OddOrder.BG.Ch4.S15

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch4.S14

open scoped Pointwise

open scoped IsMulCommutative

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- **BG Theorem 15.7(a), rank-theoretic core** (mmd L4192-4198): if `F(M)` is not a TI-subgroup
of `G`, then no prime divides `M_F` and lies in `β(M)`.

The `≥ 3` side is `three_le_pRank_mf_of_mem_beta` (any `r ∈ π(M_F) ∩ β(M)` has `r_r(M_F) ≥ 3`); the
proof below establishes the complementary `< 3` bound `pRank (M_F) r < 3`, the genuinely deep §15
content.  **Both sides are now fully proved — this theorem is sorry-free and axiom-clean.**

**Building blocks (this file):** the setup
`exists_notMem_inf_conj_fitting_ne_bot_of_not_fittingIsTI` (step 1: `g ∉ M`,
`X = F(M) ⊓ F(M)^g ≠ ⊥`)
and `rank_lt_three_of_le_two_maximals` (step 7 core: a subgroup in two distinct maximals has rank
`< 3`).  The assembly, with the upstream lemmas it uses:

* **(step 3, `p ∈ σ(M)`)** pick `p ∈ π(X)`, `X₁ ≤ X` of order `p`
  (`le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent`: `X₁ ≤ O_p(F(M))`).  If `p ∉ σ(M)` then
  `O_p(F(M)) ≤ O_{σ'}(F(M))` is cyclic (`fitting_decomposition`), so `X₁` is the unique order-`p`
  subgroup, hence characteristic and normal in both `M` and `M^g`;
  `normalizer_eq_of_normal_of_mem_maximal`
  (S08, currently `private`) forces `M^g = M`, contradicting `g ∉ M`. ⟹ `p ∈ σ(M)`. *(fiddly
  sub-step:
  cyclic group ⟹ unique/characteristic order-`p` subgroup.)*
* **(step 5, `p ∉ β(M)`)** `X₁ ≤ O_p(M) ≤ M_σ` (`opiCoreInG_singleton_le_Msigma_of_mem_sigma`) and
  `X₁ ≤ F(M)^g ≤ M^g`, so `X₁ ≤ M_σ ⊓ M^g`; Lemma 12.17 (`Msigma_inf_conj_isBetaCompl`) ⟹
  `p ∉ β(M)`,
  hence `r ≠ p` for the `β`-prime `r` (so the `r = p` case is vacuous).
* **(step 6, `C_G(X₁) ⊄ M`)** `fusion_control_of_mem_sigma` part (e) with `p ∈ σ(M)`, `X₁ ≤ M`,
  `conj g⁻¹ • X₁ ≤ M`.
* **(step 7, `rank C_{M_F}(X₁) < 3`)** `C_G(X₁) < ⊤` (else `X₁ ≤ Z(G) = ⊥`, simple), so a coatom
  `N ⊇ C_G(X₁)` exists with `N ≠ M`; `C_{M_F}(X₁) ≤ M ⊓ N` ⟹ `rank_lt_three_of_le_two_maximals`.
* **(step 8, bridge)** `O_r(M_F) ≤ C_{M_F}(X₁)`
  (`commute_of_coprime_orderOf_of_isNilpotent`, `r ≠ p`,
  both in nilpotent `F(M)`), so `r_r(M_F) = r_r(O_r(M_F)) ≤ rank C_{M_F}(X₁) < 3`.

Combined with `mf_eq_msigma_of_piSet_inf_beta_disjoint` this yields the `M_F = M_σ` conclusion of
Theorem 15.7(a), i.e. the `FittingIsTI` clause of Theorem A(8). -/
theorem piSet_mf_inf_beta_disjoint_of_not_fittingIsTI [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hnotTI : ¬ FittingIsTI M) :
    ∀ q : ℕ, q ∈ S14.piSet (MF M) → q ∉ OddOrder.BG.Ch3.S10.beta M := by
  intro r hrπ hrβ
  -- The `≥ 3` side (proved): `r ∈ π(M_F) ∩ β(M) ⟹ r_r(M_F) ≥ 3`.
  have h3 : 3 ≤ pRank ↥(MF M) r := three_le_pRank_mf_of_mem_beta hG hM hrπ hrβ
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hrπ
  have : Fact r.Prime := ⟨hrp⟩
  refine absurd h3 (not_le.mpr ?_)
  -- Setup: `g ∉ M`, `X = F(M) ⊓ F(M)^g ≠ ⊥`.
  obtain ⟨g, hgM, hXne⟩ := exists_notMem_inf_conj_fitting_ne_bot_of_not_fittingIsTI hnotTI
  -- A prime `p ∈ π(X)`, and `p ∈ σ(M)` (step 3).
  have hXcard : Nat.card ↥(fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M) ≠ 1 :=
    fun h => hXne (Subgroup.card_eq_one.mp h)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hXcard
  have : Fact p.Prime := ⟨hp⟩
  have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M :=
    mem_sigma_of_prime_dvd_card_inf_conj_fitting hG hM hgM hp hpdvd
  -- An order-`p` subgroup `X₁ ≤ X`.
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M)) p hpdvd
  set X₁ : Subgroup G :=
    (Subgroup.zpowers x).map (fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M).subtype
    with hX₁def
  have hX₁leX : X₁ ≤ fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M :=
    hX₁def ▸ Subgroup.map_subtype_le _
  have hX₁card : Nat.card ↥X₁ = p := by
    rw [hX₁def, Subgroup.card_map_of_injective
      (fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M).subtype_injective,
      Nat.card_zpowers, hxord]
  have hX₁ne : X₁ ≠ ⊥ := fun h => hp.one_lt.ne' (by rw [← hX₁card, h, Subgroup.card_bot])
  have hX₁pg : IsPGroup p ↥X₁ := IsPGroup.of_card (n := 1) (by rw [hX₁card, pow_one])
  have hX₁F : X₁ ≤ fittingInAmbient M := hX₁leX.trans inf_le_left
  have hX₁cF : X₁ ≤ MulAut.conj g • fittingInAmbient M := hX₁leX.trans inf_le_right
  have hX₁M : X₁ ≤ M := hX₁F.trans (OddOrder.BG.Ch2.S08.fittingInG_le M)
  -- Step 5: `p ∉ β(M)` (via `X₁ ≤ M_σ ⊓ M^g` and Lemma 12.17), hence `r ≠ p`.
  have hpσ_sub : ({p} : Set ℕ) ⊆ OddOrder.BG.Ch3.S10.sigma M := by
    intro q hq; rw [Set.mem_singleton_iff] at hq; rw [hq]; exact hpσ
  have hX₁Mσ : X₁ ≤ OddOrder.BG.Ch3.S10.Msigma M := by
    have h1 : X₁ ≤ opiCoreInG ({p} : Set ℕ) (fittingInAmbient M) :=
      OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent
        (OddOrder.BG.Ch2.S08.fittingInG_isNilpotent M) hX₁F hX₁pg
    have h2 : opiCoreInG ({p} : Set ℕ) (fittingInAmbient M)
        ≤ opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) (fittingInAmbient M) :=
      Subgroup.map_mono (OddOrder.Isaacs.Ch03.oPiCore_mono hpσ_sub _)
    have h3' : opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) (fittingInAmbient M)
        = fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) :=
      opiCoreInG_sigma_fittingInAmbient_eq_fittingInAmbient_Msigma
    exact (h1.trans h2).trans (h3' ▸ OddOrder.BG.Ch2.S08.fittingInG_le _)
  have hX₁cM : X₁ ≤ MulAut.conj g • M :=
    hX₁cF.trans (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr
      (OddOrder.BG.Ch2.S08.fittingInG_le M))
  have hpβ : p ∉ OddOrder.BG.Ch3.S10.beta M :=
    OddOrder.BG.Ch3.S12.Msigma_inf_conj_isBetaCompl hG hM hgM p
      (Nat.mem_primeFactors.mpr ⟨hp,
        hX₁card ▸ Subgroup.card_dvd_of_le (le_inf hX₁Mσ hX₁cM),
        Nat.card_pos.ne'⟩)
  have hrnep : r ≠ p := fun h => hpβ (h ▸ hrβ)
  -- Step 6: `C_G(X₁) ⊄ M` (Theorem 10.1(e)).
  have hconj_g_inv : MulAut.conj g⁻¹ • X₁ ≤ M := by
    have hle : MulAut.conj g⁻¹ • X₁ ≤ MulAut.conj g⁻¹ • (MulAut.conj g • fittingInAmbient M) :=
      Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hX₁cF
    rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at hle
    exact hle.trans (OddOrder.BG.Ch2.S08.fittingInG_le M)
  have hCGnotM : ¬ Subgroup.centralizer (X₁ : Set G) ≤ M := by
    intro hCG
    have he := (OddOrder.BG.Ch3.S10.fusion_control_of_mem_sigma hG hM hpσ hX₁ne hX₁pg).2.2.2.2
    exact hgM (by simpa using inv_mem (he hX₁M hCG g⁻¹ hconj_g_inv))
  -- Step 7: `rank (C_{M_F}(X₁)) < 3` (`C_{M_F}(X₁)` lies in `M` and in a coatom `N ≠ M`).
  obtain ⟨x₀, hx₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX₁ne
  have hCGlt : Subgroup.centralizer (X₁ : Set G) < ⊤ :=
    lt_of_le_of_lt
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr x₀.2))
      (OddOrder.BG.Ch2.S09.centralizer_singleton_lt_top hG
        (fun h => hx₀ne (Subtype.ext h)))
  obtain ⟨N, hNco, hCGN⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.centralizer (X₁ : Set G))).resolve_left hCGlt.ne
  have hNmax : N ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hNco
  have hNneM : M ≠ N := fun h => hCGnotM (h ▸ hCGN)
  have hrank3 : rank ↥(MF M ⊓ Subgroup.centralizer (X₁ : Set G)) < 3 :=
    rank_lt_three_of_le_two_maximals hG hM hNmax hNneM
      (inf_le_left.trans (maxNilpotentNormalHall_le M)) (inf_le_right.trans hCGN)
  -- Step 8: `r`-elements of `M_F` centralize `X₁` (coprime, `F(M)` nilpotent), so the `r`-Sylow of
  -- `M_F` lies in `C_{M_F}(X₁)`; hence `r ∤ [M_F : C_{M_F}(X₁)]` and
  -- `r_r(M_F) = r_r(C_{M_F}(X₁)) < 3`.
  have : Group.IsNilpotent ↥(fittingInAmbient M) := OddOrder.BG.Ch2.S08.fittingInG_isNilpotent M
  have hcentr : ∀ A : Subgroup G, A ≤ MF M → IsPGroup r ↥A →
      A ≤ Subgroup.centralizer (X₁ : Set G) := by
    intro A hAMF hAr a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have haF : a ∈ fittingInAmbient M := (hAMF.trans (maxNilpotentNormalHall_le_fittingInG M)) ha
    have hyF : y ∈ fittingInAmbient M := hX₁F hy
    obtain ⟨i, hi⟩ := (IsPGroup.iff_orderOf.mp hAr) ⟨a, ha⟩
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hX₁pg) ⟨y, hy⟩
    have e1 : orderOf (⟨a, haF⟩ : ↥(fittingInAmbient M)) = r ^ i :=
      (orderOf_injective (fittingInAmbient M).subtype
        (fittingInAmbient M).subtype_injective ⟨a, haF⟩).symm.trans
        ((orderOf_injective A.subtype A.subtype_injective ⟨a, ha⟩).trans hi)
    have e2 : orderOf (⟨y, hyF⟩ : ↥(fittingInAmbient M)) = p ^ j :=
      (orderOf_injective (fittingInAmbient M).subtype
        (fittingInAmbient M).subtype_injective ⟨y, hyF⟩).symm.trans
        ((orderOf_injective X₁.subtype X₁.subtype_injective ⟨y, hy⟩).trans hj)
    have hcop : Nat.Coprime (orderOf (⟨a, haF⟩ : ↥(fittingInAmbient M)))
        (orderOf (⟨y, hyF⟩ : ↥(fittingInAmbient M))) := by
      rw [e1, e2]; exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hrp hp).mpr hrnep)
    have hcomm := OddOrder.GroupTheory.commute_of_coprime_orderOf_of_isNilpotent
      (x := (⟨a, haF⟩ : ↥(fittingInAmbient M))) (y := ⟨y, hyF⟩) hcop
    have := congrArg (Subtype.val) hcomm.eq
    simpa using this.symm
  -- The `r`-Sylow `P'` of `M_F` lies in `C_{M_F}(X₁) = M_F ⊓ C_G(X₁)`.
  obtain ⟨P⟩ : Nonempty (Sylow r ↥(MF M)) := inferInstance
  set P' : Subgroup G := (P : Subgroup ↥(MF M)).map (MF M).subtype with hP'def
  have hP'MF : P' ≤ MF M := hP'def ▸ Subgroup.map_subtype_le _
  have hP'r : IsPGroup r ↥P' := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.2
    exact IsPGroup.of_card (by
      rw [hP'def, Subgroup.card_map_of_injective (MF M).subtype_injective, hn])
  have hP'C : P' ≤ MF M ⊓ Subgroup.centralizer (X₁ : Set G) :=
    le_inf hP'MF (hcentr P' hP'MF hP'r)
  have hidx : ¬ r ∣ ((MF M ⊓ Subgroup.centralizer (X₁ : Set G)).subgroupOf (MF M)).index := by
    intro hdvd
    have hP'sub : P'.subgroupOf (MF M) ≤ (MF M ⊓ Subgroup.centralizer (X₁ : Set G)).subgroupOf (MF
        M) :=
      Subgroup.subgroupOf_mono (MF M) hP'C
    have hdvd2 : r ∣ (P'.subgroupOf (MF M)).index :=
      hdvd.trans (Subgroup.index_dvd_of_le hP'sub)
    have hPeq : P'.subgroupOf (MF M) = (P : Subgroup ↥(MF M)) :=
      hP'def ▸ Subgroup.comap_map_eq_self_of_injective (MF M).subtype_injective _
    rw [hPeq] at hdvd2
    exact P.not_dvd_index hdvd2
  calc pRank ↥(MF M) r
      = pRank ↥(MF M ⊓ Subgroup.centralizer (X₁ : Set G)) r :=
        (OddOrder.GroupTheory.pRank_eq_of_le_of_not_dvd_index inf_le_left hidx).symm
    _ ≤ rank ↥(MF M ⊓ Subgroup.centralizer (X₁ : Set G)) := pRank_le_rank r
    _ < 3 := hrank3

/-- **`M_F = M_σ` from `¬FittingIsTI`** (the `M_F = M_σ` conclusion of BG Theorem 15.7(a)):
combine the rank-theoretic core `piSet_mf_inf_beta_disjoint_of_not_fittingIsTI` with the
Theorem 15.2(b) endgame `mf_eq_msigma_of_piSet_inf_beta_disjoint`. -/
theorem mf_eq_msigma_of_not_fittingIsTI [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hnotTI : ¬ FittingIsTI M) : MF M = OddOrder.BG.Ch3.S10.Msigma M :=
  mf_eq_msigma_of_piSet_inf_beta_disjoint hG hM
    (piSet_mf_inf_beta_disjoint_of_not_fittingIsTI hG hM hnotTI)

/-- **BG Theorem 15.7(c), `M' ≤ F(M)` for `¬FittingIsTI M`** (Coq `nonTI_Fitting_structure` `sM'F`):
the derived subgroup of a maximal subgroup whose Fitting subgroup is *not* `TI` is nilpotent, hence
`≤ F(M)`.

`M_F = M_σ` (`mf_eq_msigma_of_not_fittingIsTI`), and `M_β ≤ M_σ = M_F` is a `β(M)`-group
(`Mbeta_isPiGroup`; `β ⊆ α ⊆ σ` via `alpha_subset_sigma`), so `π(M_β) ⊆ π(M_F) ∩ β(M) = ∅`
(`piSet_mf_inf_beta_disjoint_of_not_fittingIsTI`), forcing `M_β = 1`. Then `M'/M_β ≅ M'` is
nilpotent
(`derivedQuotientMbeta_isNilpotent`), and the nilpotent normal `M'` lies in the Fitting subgroup
(`le_fittingInAmbient_of_subgroupOf_normal_of_isNilpotent`).  Sole upstream gate of the `E₃ = 1`
chain feeding Corollary 15.9's cyclic Frobenius complement (with
`tau3_eq_empty_of_derivedInG_le_fittingInAmbient` + `E3_eq_bot_of_tau3_eq_empty`). -/
theorem derivedInG_le_fittingInAmbient_of_not_fittingIsTI [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hnotTI : ¬ FittingIsTI M) : derivedInG M ≤ fittingInAmbient M := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hMFMσ : MF M = OddOrder.BG.Ch3.S10.Msigma M := mf_eq_msigma_of_not_fittingIsTI hG hM hnotTI
  -- `M_β ≤ M_σ`: `M_β` is a normal `σ(M)`-subgroup (`β ⊆ α ⊆ σ`).
  have hMβσ : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma M)
      (OddOrder.BG.Ch3.S10.Mbeta M) := fun p hp =>
    OddOrder.BG.Ch3.S10.alpha_subset_sigma hG hM (OddOrder.BG.Ch3.S10.Mbeta_isPiGroup M p hp).1
  have hMβnorm : ((OddOrder.BG.Ch3.S10.Mbeta M).subgroupOf M).Normal := by
    rw [OddOrder.BG.Ch3.S10.Mbeta, OddOrder.BG.Ch3.S10.opiCoreInG_subgroupOf]; infer_instance
  have hMβMσ : OddOrder.BG.Ch3.S10.Mbeta M ≤ OddOrder.BG.Ch3.S10.Msigma M :=
    le_opiCoreInG_of_normal_of_isPiSubgroup (OddOrder.BG.Ch3.S10.Mbeta_le M) hMβnorm hMβσ
  -- `M_β = ⊥`: `π(M_β) ⊆ π(M_F) ∩ β(M) = ∅`.
  have hMβbot : OddOrder.BG.Ch3.S10.Mbeta M = ⊥ := by
    rw [← Subgroup.card_eq_one]
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hpMβ : p ∈ (Nat.card ↥(OddOrder.BG.Ch3.S10.Mbeta M)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd, Nat.card_pos.ne'⟩
    have hpβ : p ∈ OddOrder.BG.Ch3.S10.beta M := OddOrder.BG.Ch3.S10.Mbeta_isPiGroup M p hpMβ
    have hpMF : p ∈ S14.piSet (MF M) := by
      change p ∈ (Nat.card ↥(MF M)).primeFactors
      rw [hMFMσ]
      exact Nat.primeFactors_mono (Subgroup.card_dvd_of_le hMβMσ) Nat.card_pos.ne' hpMβ
    exact piSet_mf_inf_beta_disjoint_of_not_fittingIsTI hG hM hnotTI p hpMF hpβ
  -- `M'` nilpotent: `M'/M_β ≅ M'` (`M_β = ⊥`), and `M'/M_β` is nilpotent (Corollary 10.7).
  have heq : (OddOrder.BG.Ch3.S10.Mbeta M).subgroupOf (derivedInG M) = ⊥ := by
    rw [hMβbot, Subgroup.bot_subgroupOf]
  have hnorm2 : ((OddOrder.BG.Ch3.S10.Mbeta M).subgroupOf (derivedInG M)).Normal := by
    rw [heq]; infer_instance
  have := OddOrder.BG.Ch3.S10.derivedQuotientMbeta_isNilpotent hG hM
  have hM'nil : Group.IsNilpotent ↥(derivedInG M) :=
    Group.nilpotent_of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq heq).trans
        QuotientGroup.quotientBot)
  -- `M'` normal in `M` + nilpotent ⟹ `M' ≤ F(M)`.
  have hid : (derivedInG M).subgroupOf M = commutator ↥M :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective (commutator ↥M)
  have hM'norm : ((derivedInG M).subgroupOf M).Normal := by rw [hid]; infer_instance
  exact le_fittingInAmbient_of_subgroupOf_normal_of_isNilpotent (Subgroup.map_subtype_le _) hM'norm

/-- **BG Theorem 15.7(d), `E₃ = 1`** (Coq `nonTI_Fitting_structure` `E3_1`):
the `τ₃(M)`-Hall factor of
any `σ(M)'`-complement `E`-setup is trivial when `F(M)` is not `TI`.  Composes the three parts:
`M' ≤ F(M)` (`derivedInG_le_fittingInAmbient_of_not_fittingIsTI`, part (c)) → `τ₃(M) = ∅`
(`tau3_eq_empty_of_derivedInG_le_fittingInAmbient`) → `E₃ = ⊥` (`E3_eq_bot_of_tau3_eq_empty`).  With
`τ₂(M) = ∅` (Theorem 15.8) forcing `E₂ = 1` too, `E = E₁` is cyclic (`E1_isCyclic`) — the cyclic
Frobenius complement of Corollary 15.9. -/
theorem E3_eq_bot_of_not_fittingIsTI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (hM : M ∈ maximalSubgroups G) (hnotTI : ¬ FittingIsTI M)
    (hsetup : OddOrder.BG.Ch3.S12.SubgroupESetup M E E₁ E₂ E₃) : E₃ = ⊥ :=
  E3_eq_bot_of_tau3_eq_empty hsetup
    (tau3_eq_empty_of_derivedInG_le_fittingInAmbient hG hM
      (derivedInG_le_fittingInAmbient_of_not_fittingIsTI hG hM hnotTI))

/-- **BG Theorem A(8), the `FittingIsTI` clause** (mmd L4274, schematic proof: Theorem 15.7(a)(b)):
if `M_F ≠ M_σ`, then `F(M)` is a TI-subgroup of `G`.  This is the contrapositive of the
`M_F = M_σ` conclusion of Theorem 15.7(a) (`mf_eq_msigma_of_not_fittingIsTI`): if `F(M)` failed to
be TI, then `M_F` would equal `M_σ`.  Discharges the last (and deepest) conjunct of Theorem A(8),
modulo the single rank-theoretic residual `piSet_mf_inf_beta_disjoint_of_not_fittingIsTI`. -/
theorem fitting_isTI_of_mf_ne_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hne : MF M ≠ OddOrder.BG.Ch3.S10.Msigma M) : FittingIsTI M := by
  by_contra h
  exact hne (mf_eq_msigma_of_not_fittingIsTI hG hM h)

/-- **`IsTypeP2 M → FittingIsTI M`** — the type-classification conjunct (a) of BG Theorem 15.7
(mmd L4244): a type-`P₂` maximal subgroup has a TI Fitting subgroup.  Equivalently, every maximal
`M` with `¬FittingIsTI M` lies in `M_F ∪ M_{P₁}` (is type `F` or `P₁`, never `P₂`) — conjunct (a)
of `fitting_not_ti_cases`, separated out here because it is all that BG's §16 (Theorem C(10) /
Proposition 16.1) needs, and it is provable from the landed §15 pieces alone.

Proof (BG L4244): suppose `¬FittingIsTI M`.  Then `M_F = M_σ`
(`mf_eq_msigma_of_not_fittingIsTI`) and `π(M_F) ∩ β(M) = ∅`
(`piSet_mf_inf_beta_disjoint_of_not_fittingIsTI`).  But a type-`P₂` maximal subgroup has
`σ(M) = β(M)` (Proposition 14.2(g) = the type-`P₂` clause of `typeP_structure`), and `M_σ ≠ 1`
provides a prime `q ∈ π(M_σ) = π(M_F)` with `q ∈ σ(M) = β(M)`, contradicting the disjointness. -/
theorem fittingIsTI_of_isTypeP2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M) :
    FittingIsTI M := by
  classical
  by_contra hnotTI
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  -- Hall `κ(M)`- and `(κ ∪ σ)ᶜ`-subgroups `K`, `U` of `M`, as Proposition 14.2 needs.
  obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
  set K : Subgroup G := K'.map M.subtype with hKdef
  have hKM : K ≤ M := hKdef ▸ Subgroup.map_subtype_le K'
  have hKeq : K.subgroupOf M = K' :=
    hKdef ▸ Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := hKeq ▸ hK'
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M) ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  have hUeq : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUeq]; exact hU'
  -- Proposition 14.2(g): a type-`P₂` maximal subgroup has `σ(M) = β(M)`.
  have hσβ : OddOrder.BG.Ch3.S10.sigma M = OddOrder.BG.Ch3.S10.beta M :=
    ((S14.typeP_structure hG hM hP2.1 hKM hK rfl hU).2.2.2.2.1 hP2).1
  -- `¬FittingIsTI`: `M_F = M_σ` and `π(M_F) ∩ β(M) = ∅`.
  have hMFeq : MF M = OddOrder.BG.Ch3.S10.Msigma M := mf_eq_msigma_of_not_fittingIsTI hG hM hnotTI
  have hdisj := piSet_mf_inf_beta_disjoint_of_not_fittingIsTI hG hM hnotTI
  -- `M_σ ≠ 1` gives a prime `q ∈ π(M_σ) = π(M_F)`, in `σ(M) = β(M)`: the contradiction.
  have hMσne1 : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) ≠ 1 := by
    rw [ne_eq, Subgroup.card_eq_one]; exact OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
  obtain ⟨q, hqp, hqdvd⟩ := Nat.exists_prime_and_dvd hMσne1
  have hqπMσ : q ∈ S14.piSet (OddOrder.BG.Ch3.S10.Msigma M) :=
    Nat.mem_primeFactors.mpr ⟨hqp, hqdvd, Nat.card_pos.ne'⟩
  have hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
    (OddOrder.BG.Ch3.S10.Msigma_isHall hG hM).1 q hqπMσ
  have hqMF : q ∈ S14.piSet (MF M) := by rw [hMFeq]; exact hqπMσ
  exact hdisj q hqMF (hσβ ▸ hqσ)

end OddOrder.BG.Ch4.S15


