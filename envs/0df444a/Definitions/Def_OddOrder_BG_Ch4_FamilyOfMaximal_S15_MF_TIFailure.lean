-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_TIFailure
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_TIFailure
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T10:17:29.673539+00:00
-- url     : https://prove2.me/theorems/cb1ad6d9-a75d-4d89-92ca-eaf6c6061ede
-- title:
--   BG §15: failure of $F(M)$ to be TI (continuation)
-- statement:
--   A continuation of the TI-failure part of §15 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*. It consists of lemmas only, including uniquely-maximal statements for $O_p$-cores and the type-$\mathcal{P}$ partner Sylow subgroup, and containment of $A$ in the Fitting subgroup for type $\mathcal{P}_1$ non-nilpotent.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 12 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF/TIFailure.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF/TIFailure.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_OpicoreCentralizer

namespace OddOrder.BG.Ch4.S15

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch4.S14

open scoped Pointwise

open scoped IsMulCommutative

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- **Phase B/C uniqueness core of BG Theorem 15.8** (Coq `tau2_P2type_signalizer`,
BGsection15.v:1329--1338, the `def_q1` argument): if a uniqueness subgroup `Q ∈ 𝒰`
(`IsUniquelyMaximal Q`) is centralized by a rank-2 elementary abelian `A ∈ ℰ²_{q₁}(G)`, and `A`
lies in two maximal subgroups `H` and `Mstar`, then `H = Mstar`.

This is the engine behind `def_q1`: in the theorem, `Q = O_q(M*)` is a uniqueness subgroup
(Thm 12.13), `A ⊆ C(Q)` (both in the nilpotent `F(M*)`, coprime when `q₁ ≠ q`), and `A ⊆ H`,
`A ⊆ M*`; the conclusion `H = M*` contradicts `H ≠ M*`, forcing `q₁ = q`.

Proof (Coq `cent_uniq_Uniqueness` + `eq_uniq_mmax`): `A` is a rank-2 (`≥ 2`) subgroup of `C_G(Q)`,
so `A ∈ 𝒰` by BG Corollary 9.2 (`isUniquelyMaximal_of_le_centralizer_of_two_le_rank`).  Then both
`H` and `Mstar`, being maximal subgroups over `A`, equal `A.uniqueMaximalSubgroup`, hence are
equal. -/
theorem eq_of_uniquelyMaximal_centralized_by_rank2_le [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {Q A H Mstar : Subgroup G} {q1 : ℕ}
    (hq1prime : q1.Prime)
    (hQU : IsUniquelyMaximal Q) (hACQ : A ≤ Subgroup.centralizer (Q : Set G))
    (hA : A ∈ elemAbelianOfRank G q1 2) (hHmax : H ∈ maximalSubgroups G) (hAH : A ≤ H)
    (hMstarmax : Mstar ∈ maximalSubgroups G) (hAMstar : A ≤ Mstar) :
    H = Mstar := by
  have : Fact q1.Prime := ⟨hq1prime⟩
  -- `A ∈ 𝒰` (BG Corollary 9.2: rank-2 subgroup of `C_G(Q)` with `Q ∈ 𝒰`).
  have hAU : IsUniquelyMaximal A :=
    OddOrder.BG.Ch2.S09.isUniquelyMaximal_of_le_centralizer_of_two_le_rank hG hQU hACQ
      (two_le_rank_of_mem_elemAbelianOfRank_two hA)
  -- Both maximal subgroups over `A` are `A.uniqueMaximalSubgroup`, hence equal.
  have hH := hAU.eq_uniqueMaximalSubgroup_of_isCoatom_of_le (mem_maximalSubgroups.mp hHmax) hAH
  have hMst :=
    hAU.eq_uniqueMaximalSubgroup_of_isCoatom_of_le (mem_maximalSubgroups.mp hMstarmax) hAMstar
  rw [hH, hMst]

/-- **Phase B/C step 6 `def_q1` centralization, `F(L)`-nilpotent form**
(Coq `tau2_P2type_signalizer`, BGsection15.v:1337, the `sub_nilpotent_cent2 (Fitting_nil L)` step):
a `q₁`-subgroup `A ≤ F(L)` and the `q`-core `Q = O_q(L) ≤ F(L)` (`q₁ ≠ q`, `q₁` prime) satisfy
`A ≤ C_G(Q)`.

Unlike `le_centralizer_opiCore_of_msigma_nilpotent` (which needs the σ-core `L_σ` nilpotent — *not*
yet available at the `def_q1` point of Theorem 15.8), this uses **`F(L)` (`fittingInAmbient L`)
nilpotent**, which is *always* true (`fittingInG_isNilpotent`, Coq `Fitting_nil L`).  This is what
breaks the `def_q1`/`nilLs` circularity: `def_q1` is derived *before* `L_σ`-nilpotency.

Proof: working inside the nilpotent `↥(F(L))`, `Q.subgroupOf F(L)` is a *normal* `q`-subgroup
(`Q = O_q(L) ⊴ L ⊇ F(L)`, so normal in `F(L)`; a `q`-group by `isPGroup_opiCoreInG_singleton`) and
`A.subgroupOf F(L)` is a `q₁`-group with `q ∉ π(|A|)` (`q ≠ q₁`);
`commutator_eq_bot_of_isNilpotent_of_normal_isPGroup` gives `⁅Q̄, Ā⁆ = ⊥`, i.e. `Ā ≤ C(Q̄)`, which
pushes out to `A ≤ C_G(Q)`. -/
theorem le_centralizer_opiCore_of_fittingInAmbient_nilpotent [Finite G]
    {L A : Subgroup G} {q q1 : ℕ} [Fact q.Prime]
    (hMnormQ : L ≤ Subgroup.normalizer (opiCoreInG ({q} : Set ℕ) L : Set G))
    (hQFL : opiCoreInG ({q} : Set ℕ) L ≤ fittingInAmbient L)
    (hAFL : A ≤ fittingInAmbient L)
    (hq1prime : q1.Prime) (hq1ne : q1 ≠ q) (hApg : IsPGroup q1 ↥A) :
    A ≤ Subgroup.centralizer (opiCoreInG ({q} : Set ℕ) L : Set G) := by
  classical
  have : Fact q1.Prime := ⟨hq1prime⟩
  set F : Subgroup G := fittingInAmbient L with hFdef
  set Q : Subgroup G := opiCoreInG ({q} : Set ℕ) L with hQdef
  have hFL : F ≤ L := OddOrder.BG.Ch2.S08.fittingInG_le L
  have : Group.IsNilpotent ↥F := OddOrder.BG.Ch2.S08.fittingInG_isNilpotent L
  -- `Q.subgroupOf F` is a normal `q`-subgroup of the nilpotent `↥F`.
  have hFnormQ : F ≤ Subgroup.normalizer (Q : Set G) := hFL.trans hMnormQ
  have hQbarN : (Q.subgroupOf F).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQFL).mpr hFnormQ
  have hQbarpg : IsPGroup q ↥(Q.subgroupOf F) :=
    (isPGroup_opiCoreInG_singleton L (q := q)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hQFL).symm
  -- `A.subgroupOf F` is a `q₁`-group; `q ∉ π(|Ā|)` since `q ≠ q₁`.
  have hAbarpg : IsPGroup q1 ↥(A.subgroupOf F) :=
    hApg.of_equiv (Subgroup.subgroupOfEquivOfLe hAFL).symm
  have hqnotA : q ∉ (Nat.card ↥(A.subgroupOf F)).primeFactors := by
    intro hq
    obtain ⟨n, hn⟩ := hAbarpg.exists_card_eq
    rw [hn, Nat.mem_primeFactors] at hq
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) hq1prime).mp
      (hq.1.dvd_of_dvd_pow hq.2.1)
    exact hq1ne this.symm
  -- `⁅Q̄, Ā⁆ = ⊥` (nilpotent, normal `q`-part vs `q'`-part), so `Ā ≤ C(Q̄)`.
  have hcommbot : ⁅Q.subgroupOf F, A.subgroupOf F⁆ = ⊥ :=
    commutator_eq_bot_of_isNilpotent_of_normal_isPGroup hQbarpg hqnotA
  have hAbarC : A.subgroupOf F ≤
      Subgroup.centralizer ((Q.subgroupOf F : Subgroup ↥F) : Set ↥F) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact hcommbot)
  -- Push out to the ambient: `A ≤ C_G(Q)`.
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have haF : a ∈ F := hAFL ha
  have hgF : g ∈ F := hQFL hg
  have haA : (⟨a, haF⟩ : ↥F) ∈ A.subgroupOf F := Subgroup.mem_subgroupOf.mpr ha
  have hgQ : (⟨g, hgF⟩ : ↥F) ∈ Q.subgroupOf F := Subgroup.mem_subgroupOf.mpr hg
  have haC := hAbarC haA
  have hcomm := Subgroup.mem_centralizer_iff.mp haC (⟨g, hgF⟩ : ↥F) hgQ
  exact congrArg Subtype.val hcomm

/-- **BG Prop 14.2(e) uniqueness (`O_q(L) ∈ 𝒰`)** — the `uniqQ` clause the repo `typeP_structure`
omits, recovered from Lemma 13.6.  Coq `Ptype_structure` clause (e) `uniqQ` (BGsection14.v), used at
the `uniqQ` step of `tau2_P2type_signalizer` (BGsection15.v:1330).  For a type-`P` maximal `L` with
`κ(L)`-Hall `Ks`, `K = L_σ ⊓ C(Ks)`, `q ∈ π(K) ∩ σ(L)`, if `Q = O_q(L)` is a Sylow-`q` of `L`
(`q ∤ [L:Q]`) then `Q` is uniquely maximal.

Proof: `Q ≤ L_σ` is a Sylow-`q` of `L_σ` too (`q ∈ σ ⟹ q ∤ [L:L_σ]`, so `|Q| = q^{v_q|L_σ|}`,
giving the maximal-`q`-subgroup property `hSmax`); a rank-1 `q`-witness `X = ⟨w⟩ ≤ K ≤ L_σ ⊓ C(E₁)`
(as `E₁ ≤ Ks` and `K ≤ C(Ks)`) feeds Lemma 13.6 (`maximalContaining_eq_singleton_of_E1`,
`P = E₁ ≠ ⊥` from the type-`P` `E`-setup) giving `𝓜(Q) = {L}`; conclude via
`IsUniquelyMaximal.of_unique_maximal`.  Avoids the (circular) `nonabelian` route. -/
theorem opiCore_isUniquelyMaximal_of_isSylow [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L Ks K : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hL : L ∈ maximalSubgroups G) (hP : S14.IsTypeP L) (hKsL : Ks ≤ L)
    (hKsHall : Ch03.IsHallSubgroup (S14.kappa L) (Ks.subgroupOf L))
    (hKdef : K = OddOrder.BG.Ch3.S10.Msigma L ⊓ Subgroup.centralizer (Ks : Set G))
    (hqπK : q ∈ S14.piSet K) (hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma L)
    (hQidx : ¬ q ∣ ((opiCoreInG ({q} : Set ℕ) L).subgroupOf L).index) :
    IsUniquelyMaximal (opiCoreInG ({q} : Set ℕ) L) := by
  classical
  set Q : Subgroup G := opiCoreInG ({q} : Set ℕ) L with hQdef
  have hQMσ : Q ≤ OddOrder.BG.Ch3.S10.Msigma L := by
    rw [hQdef]; exact OddOrder.BG.Ch3.S10.opiCoreInG_singleton_le_Msigma_of_mem_sigma hqσ
  have hMσL : OddOrder.BG.Ch3.S10.Msigma L ≤ L := OddOrder.BG.Ch3.S10.Msigma_le L
  have hQL : Q ≤ L := hQMσ.trans hMσL
  have hQpg : IsPGroup q ↥Q := by rw [hQdef]; exact isPGroup_opiCoreInG_singleton L
  -- `|Q| = q ^ v_q(|L|) = q ^ v_q(|L_σ|)` (Sylow of `L`; `q ∈ σ ⟹ q ∤ [L:L_σ]`).
  have hQsubL : IsPGroup q ↥(Q.subgroupOf L) := hQpg.comap_subtype
  have hcardL : Nat.card ↥Q = q ^ (Nat.card ↥L).factorization q := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv]
    have hc := (hQsubL.toSylow hQidx).card_eq_multiplicity
    rwa [hQsubL.toSylow_coe hQidx] at hc
  have hMσHall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma L)
      ((OddOrder.BG.Ch3.S10.Msigma L).subgroupOf L) :=
    OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hL
  have hqidxMσ : ¬ q ∣ ((OddOrder.BG.Ch3.S10.Msigma L).subgroupOf L).index := fun hd =>
    hMσHall.2 q (Nat.mem_primeFactors.mpr ⟨Fact.out, hd, Subgroup.index_ne_zero_of_finite⟩) hqσ
  have hQcard : Nat.card ↥Q = q ^ (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma L)).factorization q := by
    rw [hcardL]
    congr 1
    have hcardmul := Subgroup.card_mul_index ((OddOrder.BG.Ch3.S10.Msigma L).subgroupOf L)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσL).toEquiv] at hcardmul
    rw [← hcardmul, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hqidxMσ, add_zero]
  have hSmax : ∀ T : Subgroup G, T ≤ OddOrder.BG.Ch3.S10.Msigma L → IsPGroup q ↥T →
      Q ≤ T → Q = T :=
    fun T hT hTq hQT =>
      OddOrder.BG.Ch3.S13.eq_of_le_of_isPGroup_card_eq_factorization hQcard hT hTq hQT
  -- Type-`P` `E`-setup and a rank-1 `q`-witness `X = ⟨w⟩ ≤ K`.
  obtain ⟨E, E₁, E₂, E₃, hE, hE1Ks, hKsE, hE1ne⟩ :=
    S14.exists_typePESetup_kappaHall hG hL hP hKsL hKsHall
  have hqdvdK : q ∣ Nat.card ↥K := Nat.dvd_of_mem_primeFactors hqπK
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' q hqdvdK
  have hXcard : Nat.card ↥(Subgroup.zpowers (w : G)) = q := by
    rw [Nat.card_zpowers]; exact (orderOf_injective _ K.subtype_injective w).trans hw
  have hXelem : Subgroup.zpowers (w : G) ∈ elemAbelianOfRank G q 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXK : Subgroup.zpowers (w : G) ≤ K := Subgroup.zpowers_le.mpr w.2
  have hXC : Subgroup.zpowers (w : G) ≤
      OddOrder.BG.Ch3.S10.Msigma L ⊓ Subgroup.centralizer (E₁ : Set G) := by
    refine hXK.trans (le_inf (hKdef ▸ inf_le_left) ?_)
    exact (show K ≤ Subgroup.centralizer (Ks : Set G) from hKdef ▸ inf_le_right).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hE1Ks))
  have hMQ : maximalSubgroupsContaining Q = {L} :=
    (OddOrder.BG.Ch3.S13.maximalContaining_eq_singleton_of_E1 hG hE hqσ (le_refl E₁) hE1ne
      hXelem hXC hQMσ hQpg hSmax).2
  refine IsUniquelyMaximal.of_unique_maximal
    (lt_of_le_of_lt hQL (mem_maximalSubgroups.mp hL).lt_top) hL hQL (fun N hN hQN => ?_)
  have hNmem : N ∈ maximalSubgroupsContaining Q := ⟨mem_maximalSubgroups.mp hN, hQN⟩
  rw [hMQ, Set.mem_singleton_iff] at hNmem
  exact hNmem

/-- **`O_q(L)` is a Sylow-`q` of `L` (`q ∤ [L : O_q(L)]`)** for a type-`P` maximal `L` with
`κ(L)`-Hall `Ks`, `K = L_σ ⊓ C(Ks)`, `q ∈ π(K) ∩ σ(L)` (Coq `sylQ`, `tau2_P2type_signalizer`
BGsection15.v:1319).  Reduces to `q ∤ [L_σ : Q]` (index tower with `q ∤ [L:L_σ]`, `σ`-Hall); the
`q`-core `Q = O_q(L) = O_q(L_σ)` is a Sylow-`q` of `L_σ` in both cases: `L_σ` nilpotent ⟹ `Q` a
Hall `{q}`-subgroup (`oPiCore_isHall_of_isNilpotent`); `L_σ` non-nilpotent ⟹ `L` type-`P₁`
(Thm 15.2) with a `K`-invariant `q'`-complement `D` of `Q` in `L_σ`
(`exists_kInvariant_qComplement`), so `[L_σ:Q] = |D|` is a `q'`-number. -/
theorem opiCore_index_coprime_of_typeP [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L Ks K : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hL : L ∈ maximalSubgroups G) (hP : S14.IsTypeP L) (hKsL : Ks ≤ L)
    (hKs : Ch03.IsHallSubgroup (S14.kappa L) (Ks.subgroupOf L))
    (hKdef : K = OddOrder.BG.Ch3.S10.Msigma L ⊓ Subgroup.centralizer (Ks : Set G))
    (hqπK : q ∈ S14.piSet K) (hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma L) :
    ¬ q ∣ ((opiCoreInG ({q} : Set ℕ) L).subgroupOf L).index := by
  classical
  have : Group.IsSolvable ↥L := hG.isSolvable_of_mem_maximalSubgroups hL
  set Q : Subgroup G := opiCoreInG ({q} : Set ℕ) L with hQdef
  have hMσL : OddOrder.BG.Ch3.S10.Msigma L ≤ L := OddOrder.BG.Ch3.S10.Msigma_le L
  have hQMσ : Q ≤ OddOrder.BG.Ch3.S10.Msigma L := by
    rw [hQdef]; exact OddOrder.BG.Ch3.S10.opiCoreInG_singleton_le_Msigma_of_mem_sigma hqσ
  have hMnormQ : L ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQdef]; exact OddOrder.GroupTheory.le_normalizer_opiCoreInG _ L
  have hQpg : IsPGroup q ↥Q := by rw [hQdef]; exact isPGroup_opiCoreInG_singleton L
  -- `q ∤ [L_σ : Q]`.
  have hqidxMσ : ¬ q ∣ (Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma L)).index := by
    by_cases hnil : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma L)
    · -- nilpotent: `Q = O_q(L_σ)` is a Hall `{q}`-subgroup of `L_σ`.
      have hMnormMσ : L ≤ Subgroup.normalizer ((OddOrder.BG.Ch3.S10.Msigma L : Subgroup G) : Set
          G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hMσL).mp
          (by rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance)
      have hQeqMσ : Q = opiCoreInG ({q} : Set ℕ) (OddOrder.BG.Ch3.S10.Msigma L) := by
        rw [hQdef]; exact opiCoreInG_eq_of_normal_le hMσL hMnormMσ (hQdef ▸ hQMσ)
      have hQsub_eq : Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma L)
          = Ch03.oPiCore ({q} : Set ℕ) ↥(OddOrder.BG.Ch3.S10.Msigma L) := by
        rw [hQeqMσ, OddOrder.BG.Ch3.S10.opiCoreInG_subgroupOf]
      have : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma L) := hnil
      have hHall : Ch03.IsHallSubgroup ({q} : Set ℕ)
          (Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma L)) := by
        rw [hQsub_eq]; exact OddOrder.BG.Ch3.S10.oPiCore_isHall_of_isNilpotent ({q} : Set ℕ)
      exact fun hd => hHall.2 q (Nat.mem_primeFactors.mpr
        ⟨Fact.out, hd, Subgroup.index_ne_zero_of_finite⟩) (Set.mem_singleton q)
    · -- non-nilpotent: type-`P₁`; `Q` has a `K`-invariant `q'`-complement `D` in `L_σ`.
      have hne : MF L ≠ OddOrder.BG.Ch3.S10.Msigma L := fun heq =>
        hnil ((maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hL).mp heq)
      have hP1 : S14.IsTypeP1 L := isTypeP1_of_mf_ne_msigma hG hL hne
      have hKprime : (Nat.card ↥K).Prime :=
        kstar_card_prime_of_inputs hG hL hP1 hKsL hKs hKdef
      have hKcard : Nat.card ↥K = q :=
        ((Nat.prime_dvd_prime_iff_eq Fact.out hKprime).mp (Nat.dvd_of_mem_primeFactors hqπK)).symm
      have hMσderived : OddOrder.BG.Ch3.S10.Msigma L = derivedInG L :=
        typeP1_msigma_eq_derivedInG hG hL hP1 hKsL hKs hKdef
      obtain ⟨hcomplDer, _, _⟩ := S14.typeP_duality hG hL hP hKsL hKs hKdef
      have hcomplMσ : Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma L).subgroupOf L)
          (Ks.subgroupOf L) := by rw [hMσderived]; exact hcomplDer
      have hcop_sub : Nat.Coprime (Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma L).subgroupOf L))
          (Nat.card ↥(Ks.subgroupOf L)) := by
        have h := coprime_card_derived_kappaHall_of_isComplement' hKs hcomplDer
        rwa [← hMσderived] at h
      have hcond2 := actsPrimeManner_subgroupOf_of_typeP hG hL hP hKsL hKs hKdef
      have hqG : (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma L
          ⊓ Subgroup.centralizer (Ks : Set G))).Prime := by rw [← hKdef]; exact hKprime
      have hKstarQ : K ≤ Q := by
        have h := kstar_le_opiCore_of_inputs hG hL hKsL hcomplMσ hcop_sub.symm hcond2 hne hqG
        rw [← hKdef, hKcard, ← hQdef] at h; exact h
      have hcopKMσ : Nat.Coprime (Nat.card ↥Ks) (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma L)) := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσL).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKsL).toEquiv] at hcop_sub
        exact hcop_sub.symm
      have hKMσdisj : Disjoint Ks (OddOrder.BG.Ch3.S10.Msigma L) := by
        rw [disjoint_iff]
        exact Subgroup.card_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcopKMσ
          (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right))
      have hKsne : Ks ≠ ⊥ := by
        intro h0
        apply hnil
        have hKeqMσ : K = OddOrder.BG.Ch3.S10.Msigma L := by
          rw [hKdef, h0]
          have hc : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
            rw [Subgroup.coe_bot]; ext g; simp [Subgroup.mem_centralizer_iff]
          rw [hc, inf_top_eq]
        exact (IsPGroup.of_card (show Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma L) = q ^ 1 by
          rw [pow_one, ← hKcard, hKeqMσ])).isNilpotent
      have hQneMσ : Q ≠ OddOrder.BG.Ch3.S10.Msigma L := fun hQeq =>
        hnil (hQeq ▸ hQpg.isNilpotent)
      obtain ⟨D, hDMσ, -, -, hcomplD, -, -, hDq'⟩ :=
        exists_kInvariant_qComplement hG hL hP hKsL hKs hKdef hQdef hQMσ hMnormQ hKstarQ hQneMσ
          hKsne hKMσdisj hcopKMσ
      rw [hcomplD.symm.index_eq_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDMσ).toEquiv]
      exact fun hd => hDq' (Nat.mem_primeFactors.mpr ⟨Fact.out, hd, Nat.card_pos.ne'⟩)
  -- Tower `[L:Q] = [L_σ:Q]·[L:L_σ]` with `q ∤ [L:L_σ]` (`σ`-Hall).
  have hMσHall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma L)
      ((OddOrder.BG.Ch3.S10.Msigma L).subgroupOf L) :=
    OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hL
  have hqidxMσL : ¬ q ∣ ((OddOrder.BG.Ch3.S10.Msigma L).subgroupOf L).index := fun hd =>
    hMσHall.2 q (Nat.mem_primeFactors.mpr ⟨Fact.out, hd, Subgroup.index_ne_zero_of_finite⟩) hqσ
  intro hd
  have htower : Q.relIndex (OddOrder.BG.Ch3.S10.Msigma L)
      * (OddOrder.BG.Ch3.S10.Msigma L).relIndex L = Q.relIndex L :=
    Subgroup.relIndex_mul_relIndex Q (OddOrder.BG.Ch3.S10.Msigma L) L hQMσ hMσL
  have hd' : q ∣ Q.relIndex (OddOrder.BG.Ch3.S10.Msigma L)
      * (OddOrder.BG.Ch3.S10.Msigma L).relIndex L := htower ▸ hd
  rcases (Nat.Prime.dvd_mul Fact.out).mp hd' with h1 | h2
  · exact hqidxMσ h1
  · exact hqidxMσL h2

/-- **BG Theorem 15.2 `sAFL`, non-nilpotent case** (Coq `tau2_P2type_signalizer` sAFL step,
BGsection15.v:1322 via `Fcore_structure`): for a type-`P` maximal `L` with non-nilpotent `L_σ`
(`M_F ≠ M_σ`, so `L` is type-`P₁`), `κ(L)`-Hall `Ks`, `K = L_σ ⊓ C(Ks)`, a rank-2 elementary
abelian `A ≤ L_σ` lies in `F(L)`.  `A` centralizes the chief factor `Q/Q₀` (`Q = O_q(L)`,
`Q₀ = C_Q(D)`, `D` the `q'`-complement), so `A ⊆ C_{L_σ}(Q/Q₀) = F(L)`
(`centralizer_msigma_quotient_le_fittingInAmbient`).

The hypothesis `A ≤ C(K)` (`K = C_{L_σ}(Ks)`) is Coq's `cKA` — **essential for soundness**: the
bare statement "every rank-2 `A ≤ L_σ` lies in `F(L)`" is *false* when `q1 ≠ q` (an `A ≤ D` in the
`q'`-complement acting non-innerly on `Q` escapes `F(L) = Q·C(Q)`); Coq's `A` centralizes `K`, which
via the chief-factor action forces `A ⊆ C_{L_σ}(Q/Q₀) = F(L)`.

✅ **Landed sorry-free** (2026-07-07, issue 9017 更新 #18; `#print axioms` =
`[propext, Classical.choice, Quot.sound]`).  This was the third `sAFL` clause and the *last* gate of
`typeP_partner_sylow_uniquelyMaximal_bundle` (hence of `tau2_transfer_constraint` = BG Thm 15.8, now
also sorry-free); `sylQ` = `opiCore_index_coprime_of_typeP` and `uniqQ` =
`opiCore_isUniquelyMaximal_of_isSylow` were already proved.

**Proof** (Coq `Fcore_structure` eq3 `C_Ms(Ks/Q₀|'Q)=F(M)`, BGsection15.v:579-593): the repo has eq2
(`centralizer_msigma_quotient_le_fittingInAmbient`: `x∈M_σ` centralizing `Q̄=Q/Q₀` ⟹ `x∈F(L)`); eq3
is derived by the **minimality lifting** `C_{M_σ}(K̄|'Q) = C_{M_σ}(Q̄|'Q)`.  `W = {y∈Q : ∀x∈H, ⁅x,y⁆
∈Q₀}` for `H = C_{M_σ}(K̄) = {x∈M_σ : ∀k∈K, ⁅x,k⁆∈Q₀}` satisfies `K ≤ W`, `Q₀ < W ≤ Q`, and is
`L`-normal, so `hmin` (minimality of the chief factor `Q/Q₀`) forces `Q ≤ W`, i.e. every `x`
centralizing `K̄` centralizes `Q̄`.  The keystone `hWnorm` (`W` is `L`-normal) reduces to `H` being
`L`-normal via the conjugation identity `⁅x, g y g⁻¹⁆ = g ⁅g⁻¹ x g, y⁆ g⁻¹` (`L` normalizes `Q`,
`Q₀`).  `H ⊴ L` splits over `L = M_σ ⊔ Ks` (`hcomplMσ`): (1) `M_σ ≤ N(H)` since
`M_σ' = ⁅M_σ,M_σ⁆ ⊆ Q ⊔ ⁅D,D⁆ ⊆ H ⊆ M_σ` (`derivedInG_le_sup_of_normal`, `hDcomm`,
`commutator_le_iff_le_normalizer`); (2) `Ks ≤ N(H)` since `Ks` centralizes `K` (`K ⊆ C(Ks)`, so
`s⁻¹ k s = k`) and normalizes `M_σ`, `Q₀`.  Then `hACK : A⊆C(K)` ⟹ `Ā` centralizes `K̄` ⟹ (lifting)
`Ā` centralizes `Q̄` ⟹ (eq2) `A⊆F(L)`.  (issue 9017 update #12/#15/#16/#18.) -/
theorem A_le_fittingInAmbient_of_typeP1_nonnil [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L Ks K A : Subgroup G} {q1 : ℕ}
    (hL : L ∈ maximalSubgroups G) (hP : S14.IsTypeP L) (hKsL : Ks ≤ L)
    (hKs : Ch03.IsHallSubgroup (S14.kappa L) (Ks.subgroupOf L))
    (hKdefL : K = OddOrder.BG.Ch3.S10.Msigma L ⊓ Subgroup.centralizer (Ks : Set G))
    (hne : MF L ≠ OddOrder.BG.Ch3.S10.Msigma L)
    (_hA : A ∈ elemAbelianOfRank G q1 2) (hAMσ : A ≤ OddOrder.BG.Ch3.S10.Msigma L)
    (hACK : A ≤ Subgroup.centralizer (K : Set G)) :
    A ≤ fittingInAmbient L := by
  classical
  have : Group.IsSolvable ↥L := hG.isSolvable_of_mem_maximalSubgroups hL
  have hP1 : S14.IsTypeP1 L := isTypeP1_of_mf_ne_msigma hG hL hne
  have hMσnotnil : ¬ Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma L) := fun hnil =>
    hne ((maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hL).mpr hnil)
  -- Chief-factor prime `q = |K|` and `Q = O_q(L)`.
  have hKprime : (Nat.card ↥K).Prime := kstar_card_prime_of_inputs hG hL hP1 hKsL hKs hKdefL
  set q : ℕ := Nat.card ↥K with hqcard
  have : Fact q.Prime := ⟨hKprime⟩
  set Q : Subgroup G := opiCoreInG ({q} : Set ℕ) L with hQdef
  have hMσL : OddOrder.BG.Ch3.S10.Msigma L ≤ L := OddOrder.BG.Ch3.S10.Msigma_le L
  have hKMσ : K ≤ OddOrder.BG.Ch3.S10.Msigma L := by rw [hKdefL]; exact inf_le_left
  have hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma L :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup L q (Nat.mem_primeFactors.mpr
      ⟨hKprime, Subgroup.card_dvd_of_le hKMσ, Nat.card_pos.ne'⟩)
  have hQMσ : Q ≤ OddOrder.BG.Ch3.S10.Msigma L := by
    rw [hQdef]; exact OddOrder.BG.Ch3.S10.opiCoreInG_singleton_le_Msigma_of_mem_sigma hqσ
  have hQL : Q ≤ L := hQMσ.trans hMσL
  have hMnormQ : L ≤ Subgroup.normalizer ((Q : Subgroup G) : Set G) := by
    rw [hQdef]; exact OddOrder.GroupTheory.le_normalizer_opiCoreInG _ L
  have hQpg : IsPGroup q ↥Q := by rw [hQdef]; exact isPGroup_opiCoreInG_singleton L
  -- Complement setup (as in `opiCore_index_coprime_of_typeP` non-nil branch).
  have hMσderived : OddOrder.BG.Ch3.S10.Msigma L = derivedInG L :=
    typeP1_msigma_eq_derivedInG hG hL hP1 hKsL hKs hKdefL
  obtain ⟨hcomplDer, _, _⟩ := S14.typeP_duality hG hL hP hKsL hKs hKdefL
  have hcomplMσ : Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma L).subgroupOf L)
      (Ks.subgroupOf L) := by rw [hMσderived]; exact hcomplDer
  have hcop_sub : Nat.Coprime (Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma L).subgroupOf L))
      (Nat.card ↥(Ks.subgroupOf L)) := by
    have h := coprime_card_derived_kappaHall_of_isComplement' hKs hcomplDer
    rwa [← hMσderived] at h
  have hcond2 := actsPrimeManner_subgroupOf_of_typeP hG hL hP hKsL hKs hKdefL
  have hqG : (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma L
      ⊓ Subgroup.centralizer (Ks : Set G))).Prime := by rw [← hKdefL]; exact hKprime
  have hKstarQ : K ≤ Q := by
    have h := kstar_le_opiCore_of_inputs hG hL hKsL hcomplMσ hcop_sub.symm hcond2 hne hqG
    rw [← hKdefL, ← hqcard, ← hQdef] at h; exact h
  have hcopKMσ : Nat.Coprime (Nat.card ↥Ks) (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma L)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσL).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKsL).toEquiv] at hcop_sub
    exact hcop_sub.symm
  have hKMσdisj : Disjoint Ks (OddOrder.BG.Ch3.S10.Msigma L) := by
    rw [disjoint_iff]
    exact Subgroup.card_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcopKMσ
      (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right))
  have hKsne : Ks ≠ ⊥ := by
    intro h0; apply hMσnotnil
    have hKeqMσ : K = OddOrder.BG.Ch3.S10.Msigma L := by
      rw [hKdefL, h0]
      have hc : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
        rw [Subgroup.coe_bot]; ext g; simp [Subgroup.mem_centralizer_iff]
      rw [hc, inf_top_eq]
    exact (IsPGroup.of_card (show Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma L) = q ^ 1 by
      rw [pow_one, hqcard, hKeqMσ])).isNilpotent
  have hQneMσ : Q ≠ OddOrder.BG.Ch3.S10.Msigma L := fun hQeq =>
    hMσnotnil (hQeq ▸ hQpg.isNilpotent)
  obtain ⟨D, hDMσ, hKnormD, hQDdisj, hcomplD, hDnil, hDne, hDq'⟩ :=
    exists_kInvariant_qComplement hG hL hP hKsL hKs hKdefL hQdef hQMσ hMnormQ hKstarQ hQneMσ
      hKsne hKMσdisj hcopKMσ
  set Q0 : Subgroup G := Q ⊓ Subgroup.centralizer (D : Set G) with hQ0def
  have hQ0Q : Q0 ≤ Q := by rw [hQ0def]; exact inf_le_left
  obtain ⟨hMNQ0, hKstarNotQ0, hQ0ltQ, hmin⟩ :=
    chiefFactor_Q0_normal_minimal_of_inputs hG hL hP1 hKsL hKs hKdefL hQdef hQMσ hMnormQ hKstarQ
      hQneMσ hKsne hKMσdisj hcopKMσ hMσnotnil hDq' hDMσ hKnormD hQDdisj hcomplD hDnil hDne
  have hQ0nQ : (Q0.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ0Q).mpr (hQL.trans hMNQ0)
  obtain ⟨hEA, -⟩ :=
    isElementaryAbelian_chiefFactor_of_minimalNormal hQ0ltQ hQL hQpg hMnormQ hMNQ0 hmin
  have hQab : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Q0 := by
    intro x hxQ y hyQ
    have hcomm := hEA.comm (QuotientGroup.mk (⟨x, hxQ⟩ : ↥Q)) (QuotientGroup.mk (⟨y, hyQ⟩ : ↥Q))
    have h1 : QuotientGroup.mk (⁅(⟨x, hxQ⟩ : ↥Q), (⟨y, hyQ⟩ : ↥Q)⁆) =
        (1 : ↥Q ⧸ Q0.subgroupOf Q) := by
      rw [← QuotientGroup.mk'_apply, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    have h2 : ((⁅(⟨x, hxQ⟩ : ↥Q), (⟨y, hyQ⟩ : ↥Q)⁆ : ↥Q) : G) = ⁅x, y⁆ := by
      push_cast [commutatorElement_def]; rfl
    rwa [h2] at h1
  have hcopDQ : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Q) := by
    obtain ⟨n, hn⟩ := hQpg.exists_card_eq
    rw [hn]
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp
    · rw [Nat.coprime_pow_right_iff h0]
      exact ((Fact.out : q.Prime).coprime_iff_not_dvd.mpr (fun hd =>
        hDq' (Nat.mem_primeFactors.mpr ⟨Fact.out, hd, Nat.card_pos.ne'⟩))).symm
  have hsecFit : ∀ x ∈ OddOrder.BG.Ch3.S10.Msigma L, (∀ y ∈ Q, ⁅x, y⁆ ∈ Q0) →
      x ∈ fittingInAmbient L :=
    centralizer_msigma_quotient_le_fittingInAmbient hG hL hQMσ hDMσ hQ0def hQ0Q hcomplD hMnormQ
      hMNQ0 hQpg hDnil hcopDQ hQab
  -- **Minimality lifting** (Coq `Fcore_structure` eq3, BGsection15.v:579-593): `C_{L_σ}(K̄|'Q) =
  -- C_{L_σ}(Q̄|'Q)`.  `W = {y ∈ Q : ∀ x ∈ C_{L_σ}(K̄), ⁅x,y⁆ ∈ Q₀}` is `M`-normal, `⊇ K ⊋ Q₀`, so
  -- `Q ≤ W` (`hmin`), i.e. every `x` centralizing `K̄` centralizes `Q̄`.  (issue 9017 #16.)
  have hLift : ∀ x ∈ OddOrder.BG.Ch3.S10.Msigma L,
      (∀ k ∈ K, ⁅x, k⁆ ∈ Q0) → (∀ y ∈ Q, ⁅x, y⁆ ∈ Q0) := by
    have hMσnormQ0 : OddOrder.BG.Ch3.S10.Msigma L ≤ Subgroup.normalizer (Q0 : Set G) :=
      hMσL.trans hMNQ0
    have hQnormQ0 : Q ≤ Subgroup.normalizer (Q0 : Set G) := hQMσ.trans hMσnormQ0
    -- `H = C_{M_σ}(K̄)`, the `M_σ`-elements centralizing `K` modulo `Q₀`.
    let H : Subgroup G :=
      { carrier := {x | x ∈ OddOrder.BG.Ch3.S10.Msigma L ∧ ∀ k ∈ K, ⁅x, k⁆ ∈ Q0}
        one_mem' := ⟨(OddOrder.BG.Ch3.S10.Msigma L).one_mem, fun k _ => by
          rw [commutatorElement_one_left]; exact Q0.one_mem⟩
        mul_mem' := fun {x x'} hx hx' => ⟨(OddOrder.BG.Ch3.S10.Msigma L).mul_mem hx.1 hx'.1,
          fun k hk => by
            have heq : ⁅x * x', k⁆ = (x * ⁅x', k⁆ * x⁻¹) * ⁅x, k⁆ := by
              rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]; group
            rw [heq]
            have hxN0 : x ∈ Subgroup.normalizer (Q0 : Set G) := hMσnormQ0 hx.1
            exact Q0.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN0 ⁅x', k⁆).mp (hx'.2 k hk))
              (hx.2 k hk)⟩
        inv_mem' := fun {x} hx => ⟨(OddOrder.BG.Ch3.S10.Msigma L).inv_mem hx.1, fun k hk => by
          have heq : ⁅x⁻¹, k⁆ = x⁻¹ * ⁅x, k⁆⁻¹ * (x⁻¹)⁻¹ := by
            rw [commutatorElement_def, commutatorElement_def]; group
          rw [heq]
          have hxN0 : x ∈ Subgroup.normalizer (Q0 : Set G) := hMσnormQ0 hx.1
          exact (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Q0 : Set G)).inv_mem hxN0)
            ⁅x, k⁆⁻¹).mp (Q0.inv_mem (hx.2 k hk))⟩ }
    have hHle : H ≤ OddOrder.BG.Ch3.S10.Msigma L := fun x hx => hx.1
    -- `W = {y ∈ Q : ∀ x ∈ H, ⁅x,y⁆ ∈ Q₀}`, the `Q̄`-elements fixed by `H`.
    let W : Subgroup G :=
      { carrier := {y | y ∈ Q ∧ ∀ x ∈ H, ⁅x, y⁆ ∈ Q0}
        one_mem' := ⟨Q.one_mem, fun x _ => by rw [commutatorElement_one_right]; exact Q0.one_mem⟩
        mul_mem' := fun {y y'} hy hy' => ⟨Q.mul_mem hy.1 hy'.1, fun x hx => by
          have heq : ⁅x, y * y'⁆ = ⁅x, y⁆ * (y * ⁅x, y'⁆ * y⁻¹) := by
            rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]; group
          rw [heq]
          have hyN0 : y ∈ Subgroup.normalizer (Q0 : Set G) := hQnormQ0 hy.1
          exact Q0.mul_mem (hy.2 x hx)
            ((Subgroup.mem_normalizer_iff.mp hyN0 ⁅x, y'⁆).mp (hy'.2 x hx))⟩
        inv_mem' := fun {y} hy => ⟨Q.inv_mem hy.1, fun x hx => by
          have heq : ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * (y⁻¹)⁻¹ := by
            rw [commutatorElement_def, commutatorElement_def]; group
          rw [heq]
          have hyN0 : y ∈ Subgroup.normalizer (Q0 : Set G) := hQnormQ0 hy.1
          exact (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Q0 : Set G)).inv_mem hyN0)
            ⁅x, y⁆⁻¹).mp (Q0.inv_mem (hy.2 x hx))⟩ }
    have hWle : W ≤ Q := fun y hy => hy.1
    have hKW : K ≤ W := fun k hk => ⟨hKstarQ hk, fun x hx => hx.2 k hk⟩
    have hQ0W : Q0 ≤ W := fun z hz => ⟨hQ0Q hz, fun x hx => by
      have hxN0 : x ∈ Subgroup.normalizer (Q0 : Set G) := hMσnormQ0 (hHle hx)
      rw [commutatorElement_def]
      exact Q0.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN0 z).mp hz) (Q0.inv_mem hz)⟩
    have hQ0ltW : Q0 < W := lt_of_le_of_ne hQ0W (fun heq => hKstarNotQ0 (le_of_le_of_eq hKW
        heq.symm))
    -- `W` is `M`-normal (from the `M`-invariance of `H`); the deep chief-factor step.
    have hWnorm : (W.subgroupOf L).Normal := by
      -- `L` normalizes `M_σ = O_{σ(L)}(L)`.
      have hLnormMσ : L ≤ Subgroup.normalizer
          ((OddOrder.BG.Ch3.S10.Msigma L : Subgroup G) : Set G) :=
        OddOrder.GroupTheory.le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma L) L
      -- `hDcomm`: `⁅D, D⁆` centralizes the chief factor `Q̄` (chief-factor engine).
      obtain ⟨_, _, hDcomm, _⟩ :=
        chiefFactor_engine_of_inputs hG hL hP1 hKsL hKs hKdefL hQdef hQMσ hMnormQ hKstarQ hKsne
          hKMσdisj hcopKMσ hDq' hDMσ hKnormD hQDdisj hDne hQ0def hMNQ0 hKstarNotQ0 hQ0ltQ hmin
      -- **(1) `M_σ ≤ N(H)`.**  `M_σ' = ⁅M_σ, M_σ⁆ ⊆ Q ⊔ ⁅D, D⁆ ⊆ H ⊆ M_σ`, so `H ⊴ M_σ`
      -- (a subgroup between `M_σ'` and `M_σ` is `M_σ`-normal).  `Q`, `⁅D, D⁆` centralize `K̄ ⊆ Q̄`.
      have hQH : Q ≤ H := fun x hxQ => ⟨hQMσ hxQ, fun k hk => hQab x hxQ k (hKstarQ hk)⟩
      have hDDMσ : ⁅D, D⁆ ≤ OddOrder.BG.Ch3.S10.Msigma L := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem (hDMσ ha) (hDMσ hb)) (inv_mem (hDMσ ha))) (inv_mem (hDMσ
            hb))
      have hDDH : ⁅D, D⁆ ≤ H := fun g hg => ⟨hDDMσ hg, fun k hk => hDcomm g hg k (hKstarQ hk)⟩
      have hsup : Q ⊔ D = OddOrder.BG.Ch3.S10.Msigma L := by
        have h := congrArg (Subgroup.map (OddOrder.BG.Ch3.S10.Msigma L).subtype) hcomplD.sup_eq_top
        rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
          inf_eq_left.mpr hQMσ, inf_eq_left.mpr hDMσ, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype] at h
      have hQnMσ : (Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma L)).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hQMσ).mpr (hMσL.trans hMnormQ)
      have hsigmaprime : derivedInG (OddOrder.BG.Ch3.S10.Msigma L) ≤ Q ⊔ ⁅D, D⁆ := by
        have hle := OddOrder.BG.Ch3.S13.derivedInG_le_sup_of_normal hQMσ hDMσ hsup hQnMσ
        rwa [show derivedInG D = ⁅D, D⁆ from Subgroup.map_subtype_commutator D] at hle
      have hMσ'H : derivedInG (OddOrder.BG.Ch3.S10.Msigma L) ≤ H :=
        hsigmaprime.trans (sup_le hQH hDDH)
      have hHMσ' : ⁅H, OddOrder.BG.Ch3.S10.Msigma L⁆ ≤ H := by
        refine (Subgroup.commutator_mono hHle le_rfl).trans ?_
        rw [← show derivedInG (OddOrder.BG.Ch3.S10.Msigma L) =
          ⁅OddOrder.BG.Ch3.S10.Msigma L, OddOrder.BG.Ch3.S10.Msigma L⁆ from
          Subgroup.map_subtype_commutator _]
        exact hMσ'H
      have hMσN : OddOrder.BG.Ch3.S10.Msigma L ≤ Subgroup.normalizer (H : Set G) :=
        OddOrder.Isaacs.Ch04.commutator_le_iff_le_normalizer.mp hHMσ'
      -- **(2) `Ks ≤ N(H)`.**  `Ks` centralizes `K` (`K ⊆ C(Ks)`, so `s⁻¹ k s = k`), normalizes
      -- `M_σ` and `Q₀`; hence conjugation by `Ks` fixes the defining condition of `H`.
      have hKsCentK : ∀ s ∈ Ks, ∀ k ∈ K, s * k = k * s := fun s hs k hk =>
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hKdefL ▸ hk)).2) s hs
      have hconjH_Ks : ∀ s ∈ Ks, ∀ x, x ∈ H → s * x * s⁻¹ ∈ H := by
        intro s hs x hx
        refine ⟨(Subgroup.mem_normalizer_iff.mp (hLnormMσ (hKsL hs)) x).mp hx.1, fun k hk => ?_⟩
        have hskk : s⁻¹ * k * s = k := by rw [mul_assoc, ← hKsCentK s hs k hk]; group
        have hgen : ⁅s * x * s⁻¹, k⁆ = s * ⁅x, s⁻¹ * k * s⁆ * s⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [hgen, hskk]
        exact (Subgroup.mem_normalizer_iff.mp (hMNQ0 (hKsL hs)) ⁅x, k⁆).mp (hx.2 k hk)
      have hKsN : Ks ≤ Subgroup.normalizer (H : Set G) := by
        intro s hs
        rw [Subgroup.mem_normalizer_iff]
        refine fun x => ⟨fun hx => hconjH_Ks s hs x hx, fun hx => ?_⟩
        have hconj := hconjH_Ks s⁻¹ (Ks.inv_mem hs) (s * x * s⁻¹) hx
        have hsimp : s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x := by group
        rwa [hsimp] at hconj
      -- `L = M_σ ⊔ Ks` (complement), so `L ≤ N(H)`.
      have hLsup : OddOrder.BG.Ch3.S10.Msigma L ⊔ Ks = L := by
        have h := congrArg (Subgroup.map L.subtype) hcomplMσ.sup_eq_top
        rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
          inf_eq_left.mpr hMσL, inf_eq_left.mpr hKsL, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype] at h
      have hHnorm : L ≤ Subgroup.normalizer (H : Set G) := by
        rw [← hLsup]; exact sup_le hMσN hKsN
      -- **`W` is `L`-normal** from the `L`-invariance of `H`, `Q`, `Q₀`
      -- (conjugation identity `⁅x, g y g⁻¹⁆ = g ⁅g⁻¹ x g, y⁆ g⁻¹`).
      have hconjW : ∀ g ∈ L, ∀ y, y ∈ W → g * y * g⁻¹ ∈ W := by
        intro g hg y hy
        refine ⟨(Subgroup.mem_normalizer_iff.mp (hMnormQ hg) y).mp hy.1, fun x hxH => ?_⟩
        have hxconj : g⁻¹ * x * g ∈ H := by
          have h := (Subgroup.mem_normalizer_iff.mp
            ((Subgroup.normalizer (H : Set G)).inv_mem (hHnorm hg)) x).mp hxH
          simpa only [inv_inv] using h
        have hgen : ⁅x, g * y * g⁻¹⁆ = g * ⁅g⁻¹ * x * g, y⁆ * g⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [hgen]
        exact (Subgroup.mem_normalizer_iff.mp (hMNQ0 hg) ⁅g⁻¹ * x * g, y⁆).mp
          (hy.2 (g⁻¹ * x * g) hxconj)
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer (hWle.trans hQL)).mpr ?_
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      refine fun y => ⟨fun hy => hconjW g hg y hy, fun hy => ?_⟩
      have hconj := hconjW g⁻¹ (L.inv_mem hg) (g * y * g⁻¹) hy
      have hsimp : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
      rwa [hsimp] at hconj
    have hQW : Q ≤ W := hmin W hQ0ltW hWle hWnorm
    intro x hxMs hxK y hyQ
    exact (hQW hyQ).2 x ⟨hxMs, hxK⟩
  -- `A ⊆ F(L)`: each `a ∈ A` is in `M_σ`, centralizes `K̄` (trivially, `A ⊆ C(K)`), hence by the
  -- lifting centralizes `Q̄`, hence lies in `F(L)` (`hsecFit`).
  intro a ha
  have haMσ : a ∈ OddOrder.BG.Ch3.S10.Msigma L := hAMσ ha
  refine hsecFit a haMσ (hLift a haMσ (fun k hk => ?_))
  have hcomm : a * k = k * a := ((Subgroup.mem_centralizer_iff.mp (hACK ha)) k hk).symm
  rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
  exact Q0.one_mem

/-- **BG Theorem 12.15 / `Ptype_structure` + `Fcore_structure` `sylQ`/`sAFL`/`uniqQ` bundle**
(Coq `tau2_P2type_signalizer`, BGsection15.v:1315--1333): for a type-`P` maximal `L` with
`κ(L)`-Hall `Ks`, `K = L_σ ⊓ C(Ks)` (`|K| = q` prime, `q ∈ σ(L)`), and a rank-2 elementary abelian
`A ≤ L_σ` that is a `q₁`-group (`q₁` prime), one has: (a) `A ≤ F(L)` (Coq `sAFL`, line 1319);
(b) `Q = O_q(L)` is a Sylow-`q` of `L` (Coq `sylQ`, line 1319); (c) `Q ∈ 𝒰` (Coq `uniqQ`, line
1330).

⚠ **This is a genuinely unformalized §12/§15 keystone of BG Theorem 15.8**
(`tau2_transfer_constraint`).
It bundles the three "pre-`def_q1`" facts Coq extracts from `Ptype_structure`/`Fcore_structure`
before proving `q₁ = q`:
* `sAFL`/`sylQ` (line 1319) — in the nilpotent `L_F = L_σ` case, `A ⊆ L_σ = L_F ⊆ F(L)` and
  `Q = O_q(L)` is a Sylow via `Fcore_pcore_Sylow`; in the non-nilpotent case, both flow through
  `Fcore_structure` (= Theorem 15.2), whose repo form (`mf_ne_msigma_typeP1_structure`) does not
  expose the Sylow witness / `A ⊆ F(L)`.
* `uniqQ` (line 1330) — the Sylow-uniqueness clause of Coq `Ptype_structure`
  (`[_ _ _ [_ uniqQ _] _]`), *not* among the six conjuncts of the repo `typeP_structure`.  The
  repo's only `IsUniquelyMaximal` route (`S12.nonabelian_pgroup_isUniquelyMaximal`) needs `Q`
  nonabelian, which itself depends on `def_q1` ⟹ this lemma: **circular**.

All three feed *only* `def_q1` (`A ≤ C(Q)` via `F(L)` nilpotent + `Q, A ⊆ F(L)` + coprimality), so
they are bundled here.  The statement is **sound and non-vacuous** — each conjunct is a genuine
consequence of Coq `Ptype_structure`/`Fcore_structure`. (issue 9017 update #12.) -/
theorem typeP_partner_sylow_uniquelyMaximal_bundle [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L Ks K A : Subgroup G} {q q1 : ℕ} [Fact q.Prime]
    (hL : L ∈ maximalSubgroups G) (hP : S14.IsTypeP L) (hKsL : Ks ≤ L)
    (hKs : Ch03.IsHallSubgroup (S14.kappa L) (Ks.subgroupOf L))
    (hKdefL : K = OddOrder.BG.Ch3.S10.Msigma L ⊓ Subgroup.centralizer (Ks : Set G))
    (hqπ : q ∈ S14.piSet K) (hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma L)
    (_hq1prime : q1.Prime) (hA : A ∈ elemAbelianOfRank G q1 2)
    (hAMσ : A ≤ OddOrder.BG.Ch3.S10.Msigma L)
    (hACK : A ≤ Subgroup.centralizer (K : Set G)) :
    A ≤ fittingInAmbient L ∧
      (∃ P : Sylow q ↥L, opiCoreInG ({q} : Set ℕ) L = (P : Subgroup ↥L).map L.subtype) ∧
      IsUniquelyMaximal (opiCoreInG ({q} : Set ℕ) L) := by
  classical
  have hQidx : ¬ q ∣ ((opiCoreInG ({q} : Set ℕ) L).subgroupOf L).index :=
    opiCore_index_coprime_of_typeP hG hL hP hKsL hKs hKdefL hqπ hqσ
  have hMσL : OddOrder.BG.Ch3.S10.Msigma L ≤ L := OddOrder.BG.Ch3.S10.Msigma_le L
  have hQMσ : opiCoreInG ({q} : Set ℕ) L ≤ OddOrder.BG.Ch3.S10.Msigma L :=
    OddOrder.BG.Ch3.S10.opiCoreInG_singleton_le_Msigma_of_mem_sigma hqσ
  have hQL : opiCoreInG ({q} : Set ℕ) L ≤ L := hQMσ.trans hMσL
  have hMnormQ : L ≤ Subgroup.normalizer ((opiCoreInG ({q} : Set ℕ) L : Subgroup G) : Set G) :=
    OddOrder.GroupTheory.le_normalizer_opiCoreInG _ L
  have hQpg : IsPGroup q ↥(opiCoreInG ({q} : Set ℕ) L) := isPGroup_opiCoreInG_singleton L
  refine ⟨?_, exists_sylow_eq_opiCore rfl hQL hMnormQ hQpg hQidx,
    opiCore_isUniquelyMaximal_of_isSylow hG hL hP hKsL hKs hKdefL hqπ hqσ hQidx⟩
  -- `sAFL`: `A ⊆ F(L)`, by cases on nilpotency of `L_σ`.
  by_cases hnil : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma L)
  · -- nilpotent: `A ≤ L_σ ≤ M_F ≤ F(L)`.
    exact hAMσ.trans ((Msigma_le_maxNilpotentNormalHall_of_nilpotent hG hL hnil).trans
      (maxNilpotentNormalHall_le_fittingInG L))
  · -- non-nilpotent: type-`P₁`; the isolated chief-factor lemma.
    have hne : MF L ≠ OddOrder.BG.Ch3.S10.Msigma L := fun heq =>
      hnil ((maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hL).mp heq)
    exact A_le_fittingInAmbient_of_typeP1_nonnil hG hL hP hKsL hKs hKdefL hne hA hAMσ hACK

/-- **BG `Ptype_structure` "not-`P₁` ⟹ `q ∈ β`" clause** (Coq `tau2_P2type_signalizer` `P1maxL`,
BGsection15.v:1342--1344): a type-`P` maximal `L` with `κ(L)`-Hall `Ks`, `K = L_σ ⊓ C(Ks)`
(`|K| = q` prime), and `q ∉ β(L)` is type-`P₁`.

⚠ **Second genuinely unformalized keystone of BG Theorem 15.8.**  Coq derives `L ∈ 𝓜_'P1` by
`contraR b'q => notP1maxL; Ptype_structure PmaxL hallKs [q ∈ β(L)]` — i.e. the *last* clause of
Coq `Ptype_structure` says a *not*-type-`P₁` type-`P` maximal has its `κ`-prime `q` ideal
(`q ∈ β`).  The repo `typeP_structure` (S14) does **not** expose this "not-`P₁` ⟹ `q ∈ β`"
implication, and it cannot be recovered from the six conjuncts it has.  Needed to obtain
`M*′ = M*_σ` (`typeP1_msigma_eq_derivedInG`, type-`P₁` only) for the `K ⊆ (M*_σ)′` input of
Step 4.  Sound: it is exactly the contrapositive of Coq `Ptype_structure`'s final component.
(issue 9017 update #12.) -/
theorem typeP_isTypeP1_of_not_mem_beta [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L Ks K : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hL : L ∈ maximalSubgroups G) (hP : S14.IsTypeP L) (hKsL : Ks ≤ L)
    (hKs : Ch03.IsHallSubgroup (S14.kappa L) (Ks.subgroupOf L))
    (hKdefL : K = OddOrder.BG.Ch3.S10.Msigma L ⊓ Subgroup.centralizer (Ks : Set G))
    (hKcard : Nat.card ↥K = q)
    (hqβ : q ∉ OddOrder.BG.Ch3.S10.beta L) :
    S14.IsTypeP1 L := by
  classical
  have : Group.IsSolvable ↥L := hG.isSolvable_of_mem_maximalSubgroups hL
  -- `q ∈ σ(L)`: `K = L_σ ⊓ C(Ks) ≤ L_σ`, `|K| = q` prime, and `L_σ` is a `σ(L)`-group.
  have hKMσ : K ≤ OddOrder.BG.Ch3.S10.Msigma L := by rw [hKdefL]; exact inf_le_left
  have hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma L := by
    have hqdvd : q ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma L) := by
      rw [← hKcard]; exact Subgroup.card_dvd_of_le hKMσ
    exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup L q
      (Nat.mem_primeFactors.mpr ⟨Fact.out, hqdvd, Nat.card_pos.ne'⟩)
  -- Type-`P` splits as `P₁ ∨ P₂`; rule out `P₂`, which (Coq `Ptype_structure` final clause,
  -- repo `typeP_structure` conjunct 5) forces `σ(L) = β(L)`, so `q ∈ σ(L) = β(L)` — contradiction.
  rcases S14.isTypeP_iff_isTypeP1_or_isTypeP2.mp hP with hP1 | hP2
  · exact hP1
  · exfalso
    -- a `(κ(L) ∪ σ(L))'`-Hall `U` of the solvable `L` (Hall's theorem), lifted to `U'.map ≤ L`.
    obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥L)
      ((S14.kappa L ∪ OddOrder.BG.Ch3.S10.sigma L)ᶜ)
    have hUeq : (U'.map L.subtype).subgroupOf L = U' :=
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective U'
    have hU : Ch03.IsHallSubgroup ((S14.kappa L ∪ OddOrder.BG.Ch3.S10.sigma L)ᶜ)
        ((U'.map L.subtype).subgroupOf L) := by rw [hUeq]; exact hU'
    obtain ⟨hσβ, _⟩ := (S14.typeP_structure hG hL hP hKsL hKs hKdefL hU).2.2.2.2.1 hP2
    exact hqβ (hσβ ▸ hqσ)

/-- **BG Theorem 15.8** (mmd L4264; Feit--Thompson 1991, `tau2_P2type_signalizer`,
BGsection15.v:1262): in the Corollary 14.12 signalizer setup — a type-`P₂` maximal `M` with
`κ`-complement `K` (a Hall `κ(M)`-subgroup), `U` the abelian Hall `(κ(M)∪σ(M))'`-factor
(Proposition 14.2(a)), `M* ∈ 𝓜(C_G(K))`, `R` a Sylow `r`-subgroup of `U`, and `H ∈ 𝓜(N_G(R))` the
signalizer neighbour — nonempty `τ₂(H)` forces `q := |K|` prime, `τ₂(H) = {q}`, and `τ₂(M) = ∅`.

**Signature correction (2026-07-06, Lane b, authorized).**  The previous scaffold hypothesized
only `(τ₂ H).Nonempty` with **no witness tying `H` to `M`**, under which the conclusion
`τ₂ H = {|K|}` is *not derivable* (an arbitrary maximal `H` with `τ₂(H) ≠ ∅` need not have
`|K| ∈ τ₂(H)`).  The hypotheses are now the genuine Coq `tau2_P2type_signalizer` ones:
`kappa_complement M U K` (unbundled as `hK`/`hU`/`hUM`/`hKM`/`hUab`/`hKNU`, matching
`typeP2_neighbor_is_typeF`), `M* ∈ 𝓜(C_G(K))` (`hMstar`), `r`-Sylow `R ≤ U` (`hr`/`hRU`/`hR`), and
crucially **`H ∈ 𝓜(N_G(R))`** (`hH`) — the missing link making `H` the Cor 14.12 signalizer
neighbour.  `tau2_transfer_constraint` has **zero code consumers** (only docstrings/AxiomsCheck
comments cite it), so the signature change breaks nothing downstream.

**Prime-restricted form (2026-07-06 #6, matching the `S12_Theorem127`/`127d` convention).**  The
repo's `tau2 M := {p | p ∉ σ M ∧ pRank ↥M p = 2}` is `ℕ`-valued, not prime-restricted: a
*composite* odd `p` (e.g. `p = 15`, `A = C₃²×C₅²`, `|A| = 15²`, `pRank = 2` since
`IsElementaryAbelian 15 A`) can lie in `tau2 M` abstractly.  So the literal `tau2 M = ∅` /
`tau2 H = {q}` over-state Coq (whose `\tau2` is implicitly a set of *primes*) and are unprovable by
the `ℰ²`-argument (which needs `Fact p.Prime`).  So the hypothesis and both `tau2` conclusions
are prime-restricted: `∃ p prime ∈ τ₂(H)`; `∀ p prime, p ∉ τ₂(M)`; and `q ∈ τ₂(H)` with every
prime of `τ₂(H)` equal to `q`.  These are faithful to Coq `~~ \tau2(H)^'.-group H` /
`\tau2(M)^'.-group M` / `\tau2(H) =i q`, and sufficient downstream
(`fittingInAmbient_eq_Msigma_of_..._tau2_empty` kills only `Y.primeFactors`, which are primes).
The `ℕ`-valued `tau2` def is a latent shared-infra issue flagged in issue 9017.

Proof spine (Coq `tau2_P2type_signalizer`): pick `q₁ ∈ τ₂(H)`; extract `A ∈ ℰ²_{q₁}(D)` for a
`σ(H)'`-Hall `D ∋ K` of `H` (Cor 14.12 `hallD`, Thm 12.7 `exists_elemAb_rank_two_le_E_of_tau2`);
`A ⊆ C(K)` (Cor 14.12 `sKFD`: `K ⊆ F(D)`, `A ⊴ D`, `F(D)` abelian), so `A ⊆ C(K) ⊆ M*` (Prop
14.2(d)); `q₁ ∉ β(G)` (Uniqueness / Lemma 12.1(g)); `M*` type-`P₁`, `M*_σ` nilpotent; `q₁ = q`;
`Q = O_q(M*)` nonabelian (Thm 12.13 `nonabelian_pgroup_isUniquelyMaximal`) ⟹ `X = C_A(H_σ)` has
`|X| = q` and `τ₂(H) = {q}` (Thm 12.7 `nonabelian_tau2` = `tau2_singleton_of_nonabelianSylow`);
finally `X ≠ K`, `C_G(U) ⊄ M`, and the `τ₂(M)`-Sylow argument give `τ₂(M) = ∅`.

⚠ **Proof status (2026-07-07, issue 9017 更新 #7):** the corrected statement is sound and matches
Coq exactly.  Landed sorry-free, in document order: Phase A (Coq `cKA`) =
`exists_rank2_elemAb_le_centralizer_kappa_of_tau2`; Phase B foundation =
`typeP2_partner_structure_of_mem`; Step 1 = `partner_kappaHall_le_Msigma_of_isTypeP2`; Step 2 =
`mem_sigma_and_le_Msigma_of_rank2_centralizer_kappa`; Step 3 (nilpotent case) =
`exists_sylow_eq_opiCore_of_mem_sigma_of_msigma_nilpotent`; **Step 4** (Coq `not_cQQ`, `Q = O_q(M*)`
nonabelian) = `partner_opiCore_nonabelian` (focal Lemma 6.5(a) inside `↥M*_σ`); **Step 5** (`Q ∈ 𝒰`)
= `S12.nonabelian_pgroup_isUniquelyMaximal` (a nonabelian Sylow-`q` of `G` over `Q`); **Step 6**
`def_q1` centralization (Coq `sub_nilpotent_cent2`) = `le_centralizer_opiCore_of_msigma_nilpotent`
+ engine `eq_of_uniquelyMaximal_centralized_by_rank2_le`; the `τ₂(H) = {q}` singleton =
`S12.tau2_singleton_of_nonabelianSylow`; Phase D core = `centralizer_kappaCompl_le_of_mem_tau2` +
`not_prime_mem_tau2_of_centralizer_kappaCompl_not_le` (given the escape witness `C_G(U) ⊄ M`).

⚠ **Assembly landed: `tau2_transfer_constraint` is sorry-free** (2026-07-07, issue 9017 更新 #12),
citing **three** precisely-isolated genuinely-gated keystones (the brief's premise that only `uniqQ`
gates was too optimistic; three clauses of Coq
`Ptype_structure`/`Fcore_structure`/`P2type_signalizer`
are missing from the repo's §14 API).  The full Coq spine is built inline; dependency graph
(verified non-circular): **Keystone A** `typeP_partner_sylow_uniquelyMaximal_bundle`
(Coq `sAFL`+`sylQ`+`uniqQ`) → `def_q1` (`F(L)` nilpotent via
`le_centralizer_opiCore_of_fittingInAmbient_nilpotent` — *not* `L_σ`-nilpotent, so no circularity —
+ `eq_of_uniquelyMaximal_centralized_by_rank2_le`) → `b'q` (`q ∉ β(M*)`, from
`isMaximalElementaryAbelian_of_mem_tau2`'s `¬ idealPrime` + `mem_beta_iff`) → **Keystone B**
`typeP_isTypeP1_of_not_mem_beta` (Coq `P1maxL`) → `nilLs` (`M*_σ` nilpotent, via the
*contrapositive*
of `mf_ne_msigma_typeP1_structure`'s `q ∈ β(M*)` conjunct) → `sKLs'` (`K ⊆ (M*_σ)′`,
`typeP1_msigma_eq_derivedInG` + `Msigma_inf_centralizer_le_derivedDerived`) → Step 4 `not_cQQ`
(`partner_opiCore_nonabelian`) → `oX`/singleton (`tau2_singleton_of_nonabelianSylow`) → escape
witness `C_G(U) ⊄ M` (**inline**, Coq `not_sXM`/`not_sCUM`: `X = A ⊓ C(H_σ)`, `|X| = q`, `X ≠ K`
via **Keystone C** `signalizer_msigma_sup_inf_partner_eq` = Coq's `H = H_σ ⋊ (H∩M*)`, `X ⊄ M` via
`κ`-Hall maximality `IsHallSubgroup.card_dvd_of_isPiGroup`, `X ⊆ C(U)` via `U ⊆ H_σ`) → Phase D
(`not_prime_mem_tau2_of_centralizer_kappaCompl_not_le`).

✅ **All three keystones A/B/C are now landed sorry-free** (Keystone C/B in earlier commits;
**Keystone A** `A_le_fittingInAmbient_of_typeP1_nonnil` (Coq `Fcore_structure` eq3 minimality
lifting) landed 2026-07-07, issue 9017 更新 #18).  Hence `tau2_transfer_constraint` is **fully
sorry-free**: `#print axioms tau2_transfer_constraint = [propext, Classical.choice, Quot.sound]`. -/
theorem tau2_transfer_constraint [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M Mstar U K R H : Subgroup G} {r : ℕ}
    (hM : M ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M)
    (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.centralizer (K : Set G)))
    (hr : r ∈ S14.piSet U) (hRU : R ≤ U)
    (hR : Ch03.IsHallSubgroup ({r} : Set ℕ) (R.subgroupOf U))
    (hKNU : K ≤ Subgroup.normalizer (U : Set G))
    (hH : H ∈ maximalSubgroupsContaining (Subgroup.normalizer (R : Set G)))
    (hHtau : ∃ p : ℕ, p.Prime ∧ p ∈ tau2 H) :
    (∀ p : ℕ, p.Prime → p ∉ tau2 M) ∧
      ∃ q : ℕ, q.Prime ∧ Nat.card ↥K = q ∧ q ∈ tau2 H ∧
        ∀ p : ℕ, p.Prime → p ∈ tau2 H → p = q := by
  classical
  -- **Setup.**  `L := Mstar` (Coq `L`).  `q := |K|` prime (Theorem 14.7(f)).
  have hMstarmax : Mstar ∈ maximalSubgroups G :=
    mem_maximalSubgroups.mpr (mem_maximalSubgroupsContaining.mp hMstar).1
  have hCKMstar : Subgroup.centralizer (K : Set G) ≤ Mstar :=
    (mem_maximalSubgroupsContaining.mp hMstar).2
  obtain ⟨q, hqprime, hKcard⟩ := card_kappaHall_prime_of_isTypeP2 hG hM hP2 hKM hK
  have : Fact q.Prime := ⟨hqprime⟩
  -- Corollary 14.12 signalizer neighbour: `H` type-`F`, `U ≤ H_σ`, and the `σ(H)'`-Hall
  -- `E`-setup (Coq `D`) with `K ≤ E`, `K ≤ F(E)`.
  obtain ⟨_hHF, hUHs, _hMHUK, _hHNU, E, E₁, E₂, E₃, hEsetup, _hKE, hKFE⟩ :=
    S14.typeP2_neighbor_is_typeF_of_mem hG hM hP2 hKM hUM hK hU hUab hr hRU hR hKNU hH
  have hHmax : H ∈ maximalSubgroups G := hEsetup.mem_maximal
  -- Pick a prime `q₁ ∈ τ₂(H)` (Coq `q1`).
  obtain ⟨q1, hq1prime, hq1⟩ := hHtau
  have : Fact q1.Prime := ⟨hq1prime⟩
  -- **Phase A** (Coq `cKA`, `sAL`): a rank-2 `A ∈ ℰ²_{q₁}(E)` with `A ≤ C(K)`, hence `A ≤ M*`.
  obtain ⟨A, hA_elem, hAE, hACK⟩ :=
    exists_rank2_elemAb_le_centralizer_kappa_of_tau2 hG hEsetup hKFE hq1prime hq1
  have hAMstar : A ≤ Mstar := hACK.trans hCKMstar
  have hAH : A ≤ H := hAE.trans hEsetup.E_le
  -- **Phase B** partner structure (Coq `Ptype_embedding`): `M*` type-`P`, `κ(M*)`-Hall
  -- `Ks := M_σ ⊓ C(K)`, and `K = M*_σ ⊓ C(Ks)` (Coq `defK`).
  set Ks : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) with hKsdef
  obtain ⟨hMstP, hKsHall, hKeq, hKsMstar⟩ :=
    typeP2_partner_structure_of_mem hG hM hP2 hKM hK hMstar
  -- Step 1 (Coq `sKLs`, `sLq`): `K ≤ M*_σ` and `q ∈ σ(M*)`.
  obtain ⟨hKMσstar, hqσfun⟩ := partner_kappaHall_le_Msigma_of_isTypeP2 hG hM hP2 hKM hK hMstar
  have hqσL : q ∈ OddOrder.BG.Ch3.S10.sigma Mstar := hqσfun q hqprime hKcard
  -- Step 2 (Coq `sLq1`, `sALs`): `q₁ ∈ σ(M*)` and `A ≤ M*_σ`.
  obtain ⟨hq1σL, hAMσstar⟩ :=
    mem_sigma_and_le_Msigma_of_rank2_centralizer_kappa hG hMstarmax hqprime hKcard hqσL
      hq1prime hA_elem hACK hAMstar
  -- `q ∈ π(K)` (`|K| = q` prime), used by both keystones.
  have hqπK : q ∈ S14.piSet K := by
    rw [S14.piSet, Set.mem_ofPred_eq, hKcard]
    exact Nat.mem_primeFactors.mpr ⟨hqprime, dvd_refl q, hqprime.ne_zero⟩
  set Q : Subgroup G := opiCoreInG ({q} : Set ℕ) Mstar with hQdef
  have hQMσstar : Q ≤ OddOrder.BG.Ch3.S10.Msigma Mstar := by
    rw [hQdef]; exact OddOrder.BG.Ch3.S10.opiCoreInG_singleton_le_Msigma_of_mem_sigma hqσL
  have hMnormQ : Mstar ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQdef]; exact OddOrder.GroupTheory.le_normalizer_opiCoreInG _ Mstar
  -- **`sAFL` + `sylQ` + `uniqQ`** (Keystone A): `A ≤ F(M*)`, `Q = O_q(M*)` a Sylow of `M*`,
  -- `Q ∈ 𝒰`.
  obtain ⟨hAFL, ⟨P, hPQ⟩, hQU⟩ :=
    typeP_partner_sylow_uniquelyMaximal_bundle hG hMstarmax hMstP hKsMstar hKsHall hKeq hqπK hqσL
      hq1prime hA_elem hAMσstar hACK
  -- **`def_q1`** (Coq lines 1329--1338): `q₁ = q`.  If `q₁ ≠ q`, `A ⊆ C(Q)` (both in the nilpotent
  -- `F(M*)`, coprime) makes `H = M*` (uniqueness engine), contradicting `H ≠ M*`.
  have hneqHL : H ≠ Mstar := fun hHL => tau2_subset_sigma_compl Mstar (hHL ▸ hq1) hq1σL
  have hdef_q1 : q1 = q := by
    by_contra hq1ne
    -- `A ⊆ C(Q)` via `F(M*)` nilpotent (`Q, A ⊆ F(M*)`, coprime since `q₁ ≠ q`).
    have hQFL : Q ≤ fittingInAmbient Mstar := by
      rw [hQdef]; exact OddOrder.BG.Ch2.S08.opiCoreInG_singleton_le_fittingInG Mstar
    have hApg : IsPGroup q1 ↥A := (mem_elemAbelianOfRank.mp hA_elem).1.isPGroup
    have hACQ : A ≤ Subgroup.centralizer (Q : Set G) :=
      le_centralizer_opiCore_of_fittingInAmbient_nilpotent
        (L := Mstar) (q := q) (q1 := q1) hMnormQ hQFL hAFL hq1prime hq1ne hApg
    exact hneqHL
      (eq_of_uniquelyMaximal_centralized_by_rank2_le hG hq1prime hQU hACQ hA_elem
        hHmax hAH hMstarmax hAMstar)
  -- Rewrite the `q₁`-facts to `q` (avoiding `subst`, which would eliminate the `set`-bound `q`).
  rw [hdef_q1] at hq1 hA_elem
  -- Now `A ∈ ℰ²_q`, `q ∈ τ₂(H)`.
  -- **`b'q`** (Coq line 1341): `q ∉ β(M*)`.  From `¬ idealPrime q G` (Lemma 12.1(g)) and
  -- `β(M*) ⊆ {ideal primes}`.
  have hqNotIdeal : ¬ OddOrder.BG.Ch3.S10.idealPrime q G :=
    (isMaximalElementaryAbelian_of_mem_tau2 hG hHmax hqprime hq1 hAH hA_elem).2
  have hqNotBetaL : q ∉ OddOrder.BG.Ch3.S10.beta Mstar := fun hβ =>
    hqNotIdeal ((OddOrder.BG.Ch3.S10.mem_beta_iff Mstar q).mp hβ).2
  -- **`P1maxL`** (Keystone B): `M*` is type-`P₁`.
  have hP1L : S14.IsTypeP1 Mstar :=
    typeP_isTypeP1_of_not_mem_beta hG hMstarmax hMstP hKsMstar hKsHall hKeq hKcard hqNotBetaL
  -- **`nilLs`** (Coq line 1345): `M*_σ` nilpotent.  Contrapositive of Theorem 15.2's `q ∈ β(M*)`
  -- conjunct: `M_F ≠ M_σ ⟹ q ∈ β(M*)`, so `q ∉ β(M*) ⟹ M_F = M_σ ⟹ M_σ` nilpotent.
  have hnilLs : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma Mstar) := by
    by_contra hnotnil
    have hne : MF Mstar ≠ OddOrder.BG.Ch3.S10.Msigma Mstar := fun heq =>
      hnotnil ((maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hMstarmax).mp heq)
    obtain ⟨-, _Q', _Q0', _D', _p', q', _, _hq'prime, _, hKcard', _, hq'β, _⟩ :=
      mf_ne_msigma_typeP1_structure hG hMstarmax hne hKsMstar hKsHall hKeq
    -- `q' = |Kstar_{M*}| = |K| = q` (`hKcard'` binds `Kstar := K`), so `q ∈ β(M*)` — contradiction.
    have hq'q : q' = q := by rw [← hKcard']; exact hKcard
    exact hqNotBetaL (hq'q ▸ hq'β)
  -- **`sKLs'`** (Coq line 1355): `K ≤ (M*_σ)′`.  Type-`P₁` gives `M*′ = M*_σ`, so `(M*_σ)′ = M*″`;
  -- and `K = M*_σ ⊓ C(Ks) ≤ M*″` (the `typeP_duality` complement +
  -- `Msigma_inf_..._derivedDerived`).
  have hMσderiv : OddOrder.BG.Ch3.S10.Msigma Mstar = derivedInG Mstar :=
    typeP1_msigma_eq_derivedInG hG hMstarmax hP1L hKsMstar hKsHall hKeq
  have hKderiv : K ≤ derivedInG (OddOrder.BG.Ch3.S10.Msigma Mstar) := by
    obtain ⟨hcomplMst, hcopMst, _⟩ := typeP_duality hG hMstarmax hMstP hKsMstar hKsHall hKeq
    have hKdd : K ≤ derivedInG (derivedInG Mstar) := by
      rw [hKeq]
      exact Msigma_inf_centralizer_le_derivedDerived_of_isComplement' hG hMstarmax hcomplMst hcopMst
    rwa [hMσderiv]
  -- `K ≤ Q = O_q(M*)` (Coq `sKQ`): `K` a `q`-group in `M*`, absorbed by the normal Sylow `Q`.
  have hKMstar : K ≤ Mstar := hKMσstar.trans (OddOrder.BG.Ch3.S10.Msigma_le Mstar)
  have hQsubOf : Q.subgroupOf Mstar = (P : Subgroup ↥Mstar) := by
    rw [hQdef, hPQ, Subgroup.subgroupOf]
    exact Subgroup.comap_map_eq_self_of_injective Mstar.subtype_injective _
  have hKQ : K ≤ Q := by
    -- `Q.subgroupOf M*` is a Hall `{q}`-subgroup (a Sylow-`q` `P` of `↥M*`), normal (Q ⊴ M*).
    have hQnorm : (Q.subgroupOf Mstar).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (hQMσstar.trans (OddOrder.BG.Ch3.S10.Msigma_le Mstar))).mpr hMnormQ
    have hQHall : Ch03.IsHallSubgroup ({q} : Set ℕ) (Q.subgroupOf Mstar) := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (G := ↥(Q.subgroupOf Mstar))).mp
        (hQsubOf ▸ P.isPGroup')
      refine ⟨fun p' hp' => ?_, fun p' hp' => ?_⟩
      · -- prime factors of `|P| = q^n` are `⊆ {q}` (empty if `n = 0`).
        rw [hn] at hp'
        rw [Set.mem_singleton_iff]
        rcases Nat.eq_zero_or_pos n with hn0 | hn0
        · rw [hn0, pow_zero, Nat.primeFactors_one] at hp'; exact absurd hp' (Finset.notMem_empty _)
        · rw [Nat.primeFactors_prime_pow hn0.ne' Fact.out, Finset.mem_singleton] at hp'; exact hp'
      · rw [hQsubOf] at hp'
        rw [Set.mem_singleton_iff]; rintro rfl
        exact P.not_dvd_index (Nat.mem_primeFactors.mp hp').2.1
    have hKpi : Ch03.Subgroup.IsPiGroup ({q} : Set ℕ) (K.subgroupOf Mstar) := fun p' hp' => by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKMstar).toEquiv, hKcard,
        (Fact.out : q.Prime).primeFactors, Finset.mem_singleton] at hp'
      exact hp' ▸ rfl
    have hsub := OddOrder.BG.Ch3.S10.isPiGroup_le_of_normal_isHallSubgroup hQHall hKpi
    have hmap := Subgroup.map_mono (f := Mstar.subtype) hsub
    rwa [Subgroup.map_subgroupOf_eq_of_le hKMstar,
      Subgroup.map_subgroupOf_eq_of_le (hQMσstar.trans (OddOrder.BG.Ch3.S10.Msigma_le Mstar))]
      at hmap
  -- **Step 4** (Coq `not_cQQ`): `Q` is nonabelian.
  have hnotcQQ : ¬ IsMulCommutative ↥Q :=
    partner_opiCore_nonabelian hG hMstarmax hqσL hnilLs hKcard hKQ hKderiv
  -- A nonabelian Sylow-`q` of `G`: extend `Q` (nonabelian) to a Sylow of `G`.
  have hQpg : IsPGroup q ↥Q := by rw [hQdef]; exact isPGroup_opiCoreInG_singleton Mstar
  obtain ⟨SG, hSGle⟩ := IsPGroup.exists_le_sylow hQpg
  have hnonabG : ∃ S : Sylow q G, ¬ IsMulCommutative (S : Subgroup G) :=
    ⟨SG, fun hSGab => hnotcQQ (OddOrder.BG.Ch3.S12.isMulCommutative_of_le hSGab hSGle)⟩
  -- **`oX`** + **singleton** (Coq `nonabelian_tau2`): `X := A₀ = A ⊓ C(H_σ)`, `|X| = q`, and every
  -- prime of `τ₂(H)` equals `q` (goal conjunct 3).
  obtain ⟨hsingleton, X, hXeq, hXcard, _hXstruct, _hXesc, _hXcmpl⟩ :=
    OddOrder.BG.Ch3.S12.tau2_singleton_of_nonabelianSylow hG hEsetup hq1 hA_elem hAE hnonabG
  refine ⟨?_, q, hqprime, hKcard, hq1, hsingleton⟩
  -- **Escape witness `C_G(U) ⊄ M`** (Coq `not_sXM`/`not_sCUM`), then **Phase D**.
  have : Fact q.Prime := ⟨hqprime⟩
  have hXA : X ≤ A := hXeq ▸ inf_le_left
  have hXcHs : X ≤ Subgroup.centralizer (OddOrder.BG.Ch3.S10.Msigma H : Set G) :=
    hXeq ▸ inf_le_right
  have hXCK : X ≤ Subgroup.centralizer (K : Set G) := hXA.trans hACK
  have hXM : X ≤ H := hXA.trans hAH
  -- `X ≠ K` (Coq `neqXK`): else `H = H_σ ⊔ (H ∩ M*) ⊆ C(K) ⊆ M*`, forcing `H = M*`.
  have hneqXK : X ≠ K := by
    intro hXK
    apply hneqHL
    -- `H_σ ⊆ C(X) = C(K)` (symmetrise `X ⊆ C(H_σ)`), so `H_σ ⊆ M*`.
    have hHsCK : OddOrder.BG.Ch3.S10.Msigma H ≤ Subgroup.centralizer (K : Set G) := by
      rw [← hXK]
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp (hXcHs hz) y hy).symm
    -- `H = H_σ ⊔ (H ∩ M*)`, and both summands are `⊆ M*`.
    have hHsup : OddOrder.BG.Ch3.S10.Msigma H ⊔ (H ⊓ Mstar) = H :=
      S14.signalizer_msigma_sup_inf_partner_eq hG hM hP2 hKM hUM hK hU hUab hMstar hr hRU hR hKNU hH
    have hHMstar : H ≤ Mstar := by
      rw [← hHsup]
      exact sup_le (hHsCK.trans hCKMstar) inf_le_right
    -- `H ≤ M*`, both coatoms ⟹ `H = M*` (else `H < M*` forces `M* = ⊤`).
    rcases eq_or_lt_of_le hHMstar with heq | hlt
    · exact heq
    · exact absurd ((mem_maximalSubgroups.mp hHmax).2 Mstar hlt)
        (mem_maximalSubgroups.mp hMstarmax).1
  -- `X ⊄ M` (Coq `not_sXM`): else `X ⊔ K` a `q`-group `⊆ M` with `K` the `κ`-Hall, so `X = K`.
  have hnotXM : ¬ (X ≤ M) := by
    intro hXMle
    apply hneqXK
    -- `X ⊔ K ⊆ M` is a `q`-group (commuting `q`-groups), and `K` is a `κ`-Hall of `M`; `q ∈ κ(M)`.
    have hqκ : q ∈ S14.kappa M :=
      hK.1 q (by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv, hKcard]
        exact Nat.mem_primeFactors.mpr ⟨hqprime, dvd_refl q, hqprime.ne_zero⟩)
    -- `K ≤ C(X)` (symmetrise `X ⊆ C(K)`); so `K ≤ N(X)`, hence `↑(X ⊔ K) = ↑X * ↑K`.
    have hKCX : K ≤ Subgroup.centralizer (X : Set G) := le_centralizer_swap hXCK
    have hKNX : K ≤ Subgroup.normalizer (X : Set G) :=
      hKCX.trans (Subgroup.centralizer_le_normalizer (X : Set G))
    have hmulsup : (↑(X ⊔ K : Subgroup G) : Set G) = ↑X * ↑K :=
      Subgroup.coe_mul_of_right_le_normalizer_left X K hKNX
    have hXKM : (X ⊔ K : Subgroup G) ≤ M := sup_le hXMle hKM
    -- `(X ⊔ K).subgroupOf M` is a `κ(M)`-group: `|X ⊔ K| · |X ⊓ K| = |X| · |K| = q²`.
    have hXKpi : Ch03.Subgroup.IsPiGroup (S14.kappa M) ((X ⊔ K).subgroupOf M) := by
      intro p' hp'
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXKM).toEquiv] at hp'
      have hcardprod : Nat.card ↥(X ⊔ K : Subgroup G) * Nat.card ↥(X ⊓ K : Subgroup G)
          = Nat.card ↥X * Nat.card ↥K := by
        have h := Subgroup.card_HK_mul_card_inf_eq_card_mul_card X K
        rwa [← hmulsup] at h
      have hdvd : Nat.card ↥(X ⊔ K : Subgroup G) ∣ Nat.card ↥X * Nat.card ↥K :=
        ⟨_, hcardprod.symm⟩
      have hp'q : p' = q := by
        have hmem : p' ∈ (Nat.card ↥X * Nat.card ↥K).primeFactors :=
          Nat.primeFactors_mono hdvd (mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne') hp'
        rw [hXcard, hKcard, ← pow_two, Nat.primeFactors_prime_pow (by norm_num) hqprime,
          Finset.mem_singleton] at hmem
        exact hmem
      exact hp'q ▸ hqκ
    -- `K.subgroupOf M` is the `κ(M)`-Hall; `|X ⊔ K| ∣ |K|` and `K ≤ X ⊔ K` force `X ⊔ K = K`.
    have hcarddvd : Nat.card ↥((X ⊔ K).subgroupOf M) ∣ Nat.card ↥(K.subgroupOf M) :=
      hK.card_dvd_of_isPiGroup hXKpi
    have hcardKle : Nat.card ↥(K.subgroupOf M) ≤ Nat.card ↥((X ⊔ K).subgroupOf M) :=
      Nat.card_le_card_of_injective _
        (Subgroup.inclusion_injective (Subgroup.subgroupOf_mono M (le_sup_right)))
    have hcardeq : Nat.card ↥((X ⊔ K).subgroupOf M) = Nat.card ↥(K.subgroupOf M) :=
      Nat.le_antisymm (Nat.le_of_dvd Nat.card_pos hcarddvd) hcardKle
    -- Transfer `hcardeq` to ambient cardinalities: `|X ⊔ K| = |K|`.
    have hcardeqamb : Nat.card ↥(X ⊔ K : Subgroup G) = Nat.card ↥K := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXKM).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hcardeq
      exact hcardeq
    have hXKeqK : (X ⊔ K : Subgroup G) = K :=
      (Subgroup.eq_of_le_of_card_ge le_sup_right hcardeqamb.le).symm
    -- `X ≤ X ⊔ K = K`; equal cardinality (`|X| = q = |K|`) gives `X = K`.
    exact Subgroup.eq_of_le_of_card_ge (hXKeqK ▸ le_sup_left) (by rw [hXcard, hKcard])
  -- `C_G(U) ⊄ M` (Coq `not_sCUM`): `X ⊆ C(H_σ) ⊆ C(U)` since `U ⊆ H_σ`.
  have hesc : ¬ (Subgroup.centralizer (U : Set G) ≤ M) := by
    intro hCUM
    exact hnotXM ((hXcHs.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hUHs))).trans
      hCUM)
  exact not_prime_mem_tau2_of_centralizer_kappaCompl_not_le hG hM hKM hUM hU hKNU hesc

/-- **`N_G(F(M)) ≤ M` for a maximal `M`** (`F(M)` is "self-normalizing modulo `M`"): the ambient
Fitting subgroup of a maximal subgroup of a minimal simple group has normalizer contained in `M`.

Proof: `M ≤ N_G(F(M))` (any `m ∈ M` normalizes `F(M)`, `mem_normalizer_fittingInG_of_mem`).  If the
containment were strict, maximality (`IsCoatom M`) would force `N_G(F(M)) = ⊤`, i.e. `F(M) ⊴ G`; but
`F(M) ≠ ⊥` (the proper subgroup `M < ⊤` is solvable and nontrivial, so `F(M) = F(↥M).map ι ≠ ⊥` by
`fitting_ne_bot_of_isSolvable_nontrivial`), so a nontrivial normal `F(M) ⊴ G` in a simple `G` must
    be
`⊤`, whence `G ≅ ↥F(M)` is nilpotent — contradicting `¬ Group.IsSolvable G`.  So `N_G(F(M)) = M`.

`F(M) ≠ ⊥` is proved unconditionally (no `M_σ`-nilpotency needed): `↥M` is solvable
(`isSolvable_of_mem_maximalSubgroups`) and nontrivial (`M ≠ ⊥`, else `M` a coatom equal to `⊥` makes
every nontrivial subgroup `⊤`, forcing `G` cyclic hence solvable), so `F(↥M) ≠ ⊥`, and the
injective `M.subtype`-image `fittingInG M` is `≠ ⊥`. -/
theorem normalizer_fittingInG_le_self [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    Subgroup.normalizer ((fittingInAmbient M : Subgroup G) : Set G) ≤ M := by
  have hco : IsCoatom M := mem_maximalSubgroups.mp hM
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  -- `M ≠ ⊥` (a `⊥` coatom would make `G` cyclic, hence solvable).
  have hMne : M ≠ ⊥ := by
    intro hMbot
    have hco' : ∀ b : Subgroup G, ⊥ < b → b = ⊤ := by rw [← hMbot]; exact hco.2
    have : Nontrivial G := hG.simple.toNontrivial
    obtain ⟨g, hg1⟩ := exists_ne (1 : G)
    have hgtop : Subgroup.zpowers g = ⊤ :=
      hco' _ (bot_lt_iff_ne_bot.mpr (fun h => hg1 (Subgroup.zpowers_eq_bot.mp h)))
    exact hG.notSolvable (Group.isSolvable_of_comm fun a b => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgtop ▸ Subgroup.mem_top a)
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgtop ▸ Subgroup.mem_top b)
      rw [← zpow_add, ← zpow_add, add_comm])
  have : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hMne
  -- `M ≤ N_G(F(M))`.
  have hM_le_N : M ≤ Subgroup.normalizer ((fittingInAmbient M : Subgroup G) : Set G) :=
    fun m hm => OddOrder.BG.Ch2.S08.mem_normalizer_fittingInG_of_mem hm
  rcases eq_or_lt_of_le hM_le_N with heq | hlt
  · exact heq.ge
  · exfalso
    -- Strict `⟹` `N_G(F(M)) = ⊤` (maximality), i.e. `F(M) ⊴ G`.
    have hFnorm : (fittingInAmbient M).Normal :=
      Subgroup.normalizer_eq_top_iff.mp (hco.2 _ hlt)
    -- `F(M) ≠ ⊥`: `↥M` solvable + nontrivial ⟹ `F(↥M) ≠ ⊥` ⟹ its injective image `≠ ⊥`.
    have hFne : fittingInAmbient M ≠ ⊥ := by
      have hFMne : OddOrder.Isaacs.Ch01.fitting ↥M ≠ ⊥ :=
        OddOrder.Isaacs.Ch01.fitting_ne_bot_of_isSolvable_nontrivial ↥M
      change OddOrder.BG.Ch2.S08.fittingInG M ≠ ⊥
      rw [OddOrder.BG.Ch2.S08.fittingInG]
      exact fun h => hFMne ((Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp h)
    -- `F(M) ⊴ G`, `F(M) ≠ ⊥`, `G` simple ⟹ `F(M) = ⊤` ⟹ `G` nilpotent ⟹ solvable, contradiction.
    rcases hG.simple.eq_bot_or_eq_top_of_normal (fittingInAmbient M) hFnorm with hbot | htop
    · exact hFne hbot
    · -- `F(M) = ⊤`: `G ≃ ↥F(M)` is nilpotent, hence solvable.
      have : Group.IsNilpotent ↥(fittingInAmbient M) := by
        change Group.IsNilpotent ↥(OddOrder.BG.Ch2.S08.fittingInG M)
        exact OddOrder.BG.Ch2.S08.fittingInG_isNilpotent M
      have : Group.IsNilpotent (↥(⊤ : Subgroup G)) := htop ▸ this
      have : Group.IsNilpotent G := Group.nilpotent_of_mulEquiv Subgroup.topEquiv
      exact hG.notSolvable IsNilpotent.to_isSolvable

/-- **`F(M)` fails to be TI once a centralizer of one of its nonidentity elements escapes `M`**
(BG Corollary 15.9, mmd L4320: *"`x ∈ M_σ ⊆ F(M)` and `C_G(x) ⊄ M`.  Hence `F(M)` is not a
`TI`-subgroup of `G`."*).  Stated in the BG-faithful generality on `x ∈ F(M)^#` (Corollary 15.9
supplies this from `x ∈ M_σ^#` once `M_σ ⊆ F(M)`, i.e. after `M ∈ 𝓜_𝓕` makes `M_σ` nilpotent).

Proof: pick `y ∈ C_G(x) ∖ M`.  As `y` centralizes `x`, `y·x·y⁻¹ = x`; so the *same* nonidentity
`x ∈ F(M)^#` witnesses an overlap `∃ a ∈ F(M)^#, y·a·y⁻¹ ∈ F(M)^#`.  Were `F(M)` a TI-subset with
normalizer-bound `N_G(F(M))`, this would force `y ∈ N_G(F(M)) ≤ M`
(`normalizer_fittingInG_le_self`),
contradicting `y ∉ M`. -/
theorem not_fittingIsTI_of_mem_fittingSharp_of_centralizer_not_le [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {x : G} (hxF : x ∈ fittingSharp M)
    (hesc : ¬ Subgroup.centralizer ({x} : Set G) ≤ M) :
    ¬ FittingIsTI M := by
  intro hTI
  -- `y ∈ C_G(x) ∖ M`.
  obtain ⟨y, hyC, hyM⟩ := Set.not_subset.mp hesc
  -- `y` centralizes `x`: `y·x·y⁻¹ = x` (from `x·y = y·x`).
  have hyx : y * x * y⁻¹ = x := by
    have hxy : x * y = y * x := (Subgroup.mem_centralizer_iff.mp hyC) x (Set.mem_singleton x)
    rw [← hxy, mul_assoc, mul_inv_cancel, mul_one]
  -- The overlap `∃ a ∈ F(M)^#, y·a·y⁻¹ ∈ F(M)^#` (both equal to `x`).
  have hoverlap : ∃ a ∈ fittingSharp M, y * a * y⁻¹ ∈ fittingSharp M :=
    ⟨x, hxF, by rw [hyx]; exact hxF⟩
  -- TI forces `y ∈ N_G(F(M)) ≤ M`, contradicting `y ∉ M`.
  exact hyM (normalizer_fittingInG_le_self hG hM (hTI y hoverlap))

/-- **The `hfratt` input of `mf_hall_centralizer_control_of_inputs`** (BG Corollary 15.3(b),
mmd L4213): when a nonidentity Hall subgroup `H ≤ M_σ` is **not** normal in `M`, the Frattini
factorization `M = N_M(H)·Q` holds for the normal `q`-subgroup `Q = O_q(M)`.

Proof (BG L4213).  `H ⋬ M` forces `M_σ` non-nilpotent
(`hall_subgroupOf_normal_of_msigma_nilpotent`),
i.e. `M_F ≠ M_σ`, so `M` is type `P₁` (`isTypeP1_of_mf_ne_msigma`) and Theorem 15.2's machinery
supplies the normal `q`-subgroup `Q = O_q(M) ≤ M_σ` with `M_σ/Q` nilpotent
(`msigma_quotient_isNilpotent_of_inputs`).  Since `Q = O_q(M_σ)` (`opiCoreInG_eq_of_normal_le`),
`Q.subgroupOf M_σ = O_q(↥M_σ)` is characteristic; with `M_σ/Q` nilpotent and `H` a Hall subgroup,
`characteristic_sup_hall_of_quotient_nilpotent` makes `QH` characteristic in `M_σ`, hence (as
`M_σ ◁ M`) `QH ◁ M` (`normal_subgroupOf_of_characteristic_subgroupOf_le`).  Finally `q ∉ π(H)`
(else `Q = O_q(M_σ) ≤ H` by `normal_isPiGroup_le_isHall`, so `QH = H ◁ M`, contradiction), giving
`Q ∩ H = 1` and `gcd(|Q|, |H|) = 1`, so the Frattini argument (`frattini_factorization`) applies. -/
theorem hfratt_of_hall_not_normal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar H : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hHMσ : H ≤ OddOrder.BG.Ch3.S10.Msigma M)
    (hHhall : Ch03.IsHallSubgroup (S14.piSet H) (H.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)))
    (_hHne : H ≠ ⊥) (hHnotnorm : ¬ (H.subgroupOf M).Normal) :
    ∃ Q : Subgroup G, Q ≤ M ∧ (Q.subgroupOf M).Normal ∧ Disjoint Q H ∧
      ∀ m ∈ M, ∃ n a : G, n ∈ Subgroup.normalizer (H : Set G) ∧ a ∈ Q ∧ m = n * a := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hMnormMσ : M ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) :=
    OddOrder.GroupTheory.le_normalizer_opiCoreInG _ M
  have hHM : H ≤ M := hHMσ.trans hMσM
  -- `M_σ` not nilpotent (else `H ⊴ M`); `M_F ≠ M_σ`.
  have hMσnotnil : ¬ Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) := fun hnil =>
    hHnotnorm (hall_subgroupOf_normal_of_msigma_nilpotent hHMσ hHhall hnil)
  have hne : MF M ≠ OddOrder.BG.Ch3.S10.Msigma M := fun heq =>
    hMσnotnil ((maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mp heq)
  -- **Setup** (= the Theorem 15.2 `Q = O_q(M)` construction, mmd L4188-4202).
  set q : ℕ := Nat.card ↥Kstar with hqdef
  have hP1 : S14.IsTypeP1 M := isTypeP1_of_mf_ne_msigma hG hM hne
  have hP : S14.IsTypeP M := hP1.1
  have hq_prime : q.Prime := kstar_card_prime_of_inputs hG hM hP1 hKM hK hKstar
  have : Fact q.Prime := ⟨hq_prime⟩
  have hMσderived : OddOrder.BG.Ch3.S10.Msigma M = derivedInG M :=
    typeP1_msigma_eq_derivedInG hG hM hP1 hKM hK hKstar
  obtain ⟨hcomplDer, _, _⟩ := S14.typeP_duality hG hM hP hKM hK hKstar
  have hcomplMσ : Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
      (K.subgroupOf M) := by rw [hMσderived]; exact hcomplDer
  have hKstarMσ : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M := by rw [hKstar]; exact inf_le_left
  have hqMσ : q ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
    rw [hqdef]; exact Subgroup.card_dvd_of_le hKstarMσ
  have hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q
      (Nat.mem_primeFactors.mpr ⟨hq_prime, hqMσ, Nat.card_pos.ne'⟩)
  set Q : Subgroup G := opiCoreInG ({q} : Set ℕ) M with hQdef
  have hQMσ : Q ≤ OddOrder.BG.Ch3.S10.Msigma M := by
    rw [hQdef]; exact OddOrder.BG.Ch3.S10.opiCoreInG_singleton_le_Msigma_of_mem_sigma hqσ
  have hMnormQ : M ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQdef]; exact OddOrder.GroupTheory.le_normalizer_opiCoreInG _ M
  have hQM : Q ≤ M := hQMσ.trans hMσM
  have hcop_sub : Nat.Coprime (Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M))
      (Nat.card ↥(K.subgroupOf M)) := by
    have h := coprime_card_derived_kappaHall_of_isComplement' hK hcomplDer
    rwa [hMσderived]
  have hcond2 := actsPrimeManner_subgroupOf_of_typeP hG hM hP hKM hK hKstar
  have hqG : (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M
      ⊓ Subgroup.centralizer (K : Set G))).Prime := by rw [← hKstar]; exact hq_prime
  have hKstarQ : Kstar ≤ Q := by
    have h := kstar_le_opiCore_of_inputs hG hM hKM hcomplMσ hcop_sub.symm hcond2 hne hqG
    rw [← hKstar, ← hqdef, ← hQdef] at h; exact h
  have hcopKMσ : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)) := by
    have e1 : Nat.card ↥(K.subgroupOf M) = Nat.card ↥K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
    have e2 : Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
        = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM).toEquiv
    rw [e1, e2] at hcop_sub; exact hcop_sub.symm
  have hKMσdisj : Disjoint K (OddOrder.BG.Ch3.S10.Msigma M) := by
    rw [disjoint_iff]
    exact Subgroup.card_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcopKMσ
      (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right))
  have hKne : K ≠ ⊥ := by
    intro hK0
    apply hMσnotnil
    have hKstareq : Kstar = OddOrder.BG.Ch3.S10.Msigma M := by
      rw [hKstar, hK0]
      have hc : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
        rw [Subgroup.coe_bot]; ext g; simp [Subgroup.mem_centralizer_iff]
      rw [hc, inf_top_eq]
    have hcardMσ : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) = q ^ 1 := by
      rw [pow_one, hqdef, hKstareq]
    exact (IsPGroup.of_card hcardMσ).isNilpotent
  have hQpg : IsPGroup q ↥Q := by rw [hQdef]; exact isPGroup_opiCoreInG_singleton M
  have hQneMσ : Q ≠ OddOrder.BG.Ch3.S10.Msigma M := by
    intro hQeq; exact hMσnotnil (hQeq ▸ hQpg.isNilpotent)
  -- **`M_σ/Q` nilpotent** (Theorem 15.2 chief-factor engine).
  have hQnMσ : (Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQMσ).mpr (hMσM.trans hMnormQ)
  have hNilMσQ : Group.IsNilpotent (↥(OddOrder.BG.Ch3.S10.Msigma M) ⧸
      Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) :=
    msigma_quotient_isNilpotent_of_inputs hG hM hP hKM hK hKstar hQMσ hMnormQ hKstarQ hQneMσ hKne
      hKMσdisj hcopKMσ
  -- **`Q = O_q(M_σ)`**, so `Q.subgroupOf M_σ` is characteristic in `↥M_σ`.
  have hQeqMσ : opiCoreInG ({q} : Set ℕ) M = opiCoreInG ({q} : Set ℕ)
      (OddOrder.BG.Ch3.S10.Msigma M) :=
    opiCoreInG_eq_of_normal_le hMσM hMnormMσ (hQdef ▸ hQMσ)
  have hQchar : (Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).Characteristic := by
    rw [hQdef, hQeqMσ, OddOrder.BG.Ch3.S10.opiCoreInG_subgroupOf]
    exact Ch03.oPiCore.characteristic _ _
  -- **`QH ◁ M`**: `QH` characteristic in `M_σ`, lifted along `M_σ ◁ M`.
  have hQHchar : (Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)
      ⊔ H.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).Characteristic :=
    characteristic_sup_hall_of_quotient_nilpotent hNilMσQ hHhall
  have hQHnorm : ((Q ⊔ H).subgroupOf M).Normal := by
    refine normal_subgroupOf_of_characteristic_subgroupOf_le hMσM hMnormMσ
      (sup_le hQMσ hHMσ) ?_
    rw [Subgroup.subgroupOf_sup hQMσ hHMσ]; exact hQHchar
  -- **`q ∉ π(H)`** (else `Q ≤ H` and `QH = H ◁ M`).
  have hqnotπH : q ∉ S14.piSet H := by
    intro hqπ
    apply hHnotnorm
    have hQsub_pi : Ch03.Subgroup.IsPiGroup (S14.piSet H)
        (Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) := by
      intro r hr
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQMσ).toEquiv] at hr
      obtain ⟨n, hn⟩ := hQpg.exists_card_eq
      rw [hn, Nat.mem_primeFactors] at hr
      have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hr.1 hq_prime).mp
        (hr.1.dvd_of_dvd_pow hr.2.1)
      rw [hrq]; exact hqπ
    have hQH_sub := normal_isPiGroup_le_isHall hQsub_pi hHhall
    have hQH : Q ≤ H := by
      have hmap := Subgroup.map_mono (f := (OddOrder.BG.Ch3.S10.Msigma M).subtype) hQH_sub
      rwa [Subgroup.map_subgroupOf_eq_of_le hQMσ, Subgroup.map_subgroupOf_eq_of_le hHMσ] at hmap
    exact (sup_eq_right.mpr hQH) ▸ hQHnorm
  -- **`Q ∩ H = 1`, coprime orders, Frattini.**
  have hqndvdH : ¬ q ∣ Nat.card ↥H := fun hdvd => hqnotπH (by
    rw [S14.piSet, Set.mem_ofPred_eq]
    exact Nat.mem_primeFactors.mpr ⟨hq_prime, hdvd, Nat.card_pos.ne'⟩)
  have hcopQH : Nat.Coprime (Nat.card ↥Q) (Nat.card ↥H) := by
    obtain ⟨n, hn⟩ := hQpg.exists_card_eq
    rw [hn]; exact ((Nat.Prime.coprime_iff_not_dvd hq_prime).mpr hqndvdH).pow_left n
  have hdisjQH : Disjoint Q H := by
    rw [disjoint_iff]
    exact Subgroup.card_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcopQH
      (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right))
  have hQnorm : (Q.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mpr hMnormQ
  exact ⟨Q, hQM, hQnorm, hdisjQH,
    frattini_factorization hQM hHM hQnorm hQHnorm hdisjQH hcopQH ‹Group.IsSolvable ↥M›⟩

/-- **BG Corollary 15.3** (mmd L4204): for a nonidentity Hall subgroup `H` of `M_σ`,
(a) `C_M(H) = C_{M_σ}(H)·X` with `X` a cyclic `τ₂(M)`-subgroup, and (b) any two elements of `H`
conjugate in `G` are already conjugate in `N_M(H)` (`N_M(H)`-fusion control).

*sorry-free.*  Discharges the three inputs of `mf_hall_centralizer_control_of_inputs`:
* `ha` ← `mf_centralizer_hall_decomp` (Proposition 14.2(b1)(e) + Lemma 15.1(c));
* `hconj` ← `mf_hall_conj_realized_in_M` (Theorem 14.4 + `N_G(M) = M`);
* `hfratt` ← `hfratt_of_hall_not_normal` (Theorem 15.2's normal `Q = O_q(M)` with `M_σ/Q`
  nilpotent, then the Frattini argument), with a `κ(M)`-Hall `K` produced from the trivial
  `κ`-witness `⊥` (`exists_isHallSubgroup_kappa_ge`).

The `H ≤ M_σ` hypothesis (BG: "`H` a Hall subgroup of `M_σ`") is what the inputs require;
consumers (Corollary 15.4 in `nilpotent_hall_embeds_in_msigma`, Theorem I in §16) supply it
after placing `H ≤ M_σ`. -/
theorem mf_hall_centralizer_control [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hHMσ : H ≤ OddOrder.BG.Ch3.S10.Msigma M)
    (hH : Ch03.IsHallSubgroup (S14.piSet H) (H.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)))
    (hHne : H ≠ ⊥) :
    (∃ X : Subgroup G, IsCyclic ↥X ∧ (↑(Nat.card ↥X).primeFactors ⊆ tau2 M) ∧
      Subgroup.centralizer (H : Set G) ⊓ M =
        (Subgroup.centralizer (H : Set G) ⊓ OddOrder.BG.Ch3.S10.Msigma M) ⊔ X) ∧
    (∀ x ∈ H, ∀ y ∈ H, (∃ g : G, y = g * x * g⁻¹) →
      ∃ n ∈ Subgroup.normalizer (H : Set G), y = n * x * n⁻¹) := by
  refine mf_hall_centralizer_control_of_inputs (hHMσ.trans (OddOrder.BG.Ch3.S10.Msigma_le M))
    (mf_centralizer_hall_decomp hG hM hHMσ hH hHne)
    (mf_hall_conj_realized_in_M hG (dummySigmaDecomposition G) hM hHMσ) ?_
  intro hHnotnorm
  obtain ⟨K, hKM, hK, -⟩ := exists_isHallSubgroup_kappa_ge hG hM (X := ⊥) bot_le (by
    intro q hq; rw [Subgroup.card_bot] at hq; simp at hq)
  exact hfratt_of_hall_not_normal hG hM hKM hK rfl hHMσ hH hHne hHnotnorm

end OddOrder.BG.Ch4.S15


