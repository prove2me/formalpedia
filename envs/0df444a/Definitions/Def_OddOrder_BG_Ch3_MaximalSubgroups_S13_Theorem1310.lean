-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S13_Theorem1310
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S13_Theorem1310
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T08:57:15.207371+00:00
-- url     : https://prove2.me/theorems/e71035d7-4fff-47cc-84db-eca09133bfeb
-- title:
--   BG §13: Theorem 13.9 ($\sigma$-disjointness) and Theorem 13.10 ($E_1$ regular on $E_3$)
-- statement:
--   Formalizes Theorems 13.9 and 13.10 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §13. Theorem 13.9 (`sigma_disjoint_of_nonconjugate`): if $M^*\in\mathcal{M}$ is not conjugate to $M$ then $\sigma(M)$ and $\sigma(M^*)$ are disjoint, a key to Proposition 14.2. Theorem 13.10 (`E1_regular_on_E3_of_noncentralize`): $E_1$ acts regularly on $E_3$ under a non-centralizing condition.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 22 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S13_Theorem1310.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S13_Theorem1310.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S13_Lemma138

namespace OddOrder.BG.Ch3.S13

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

/-- **`E`-不変 Sylow `q`-部分群の存在** (BG Lemma 13.9 step 1 で使用): `SubgroupESetup` の補群
`E` は `M_σ` を coprime に正規化する (`E` は `σ(M)'`-群、`M_σ` は `σ(M)`-群) ので、各素数 `q` に
対し `E`-不変な `M_σ` の Sylow `q`-部分群 `S` (`|S| = q^{v_q(|M_σ|)}`) が取れる。 -/
theorem exists_einvariant_sylow_Msigma [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) (q : ℕ) [Fact q.Prime] :
    ∃ S : Subgroup G, S ≤ S10.Msigma M ∧ IsPGroup q ↥S ∧
      E ≤ Subgroup.normalizer (S : Set G) ∧
      Nat.card ↥S = q ^ (Nat.card ↥(S10.Msigma M)).factorization q := by
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups h.mem_maximal
  have : Group.IsSolvable ↥E :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h.E_le)
  have hEnorm : E ≤ Subgroup.normalizer ((S10.Msigma M : Subgroup G) : Set G) :=
    h.E_le.trans (by rw [S10.Msigma]; exact le_normalizer_opiCoreInG (S10.sigma M) M)
  have hcop : Nat.Coprime (Nat.card ↥E) (Nat.card ↥(S10.Msigma M)) := by
    by_contra hne
    obtain ⟨s, hsp, hsE, hsMσ⟩ := Nat.Prime.not_coprime_iff_dvd.mp hne
    exact (SubgroupESetup.isPiGroup_sigma_compl hG h s
        (Nat.mem_primeFactors.mpr ⟨hsp, hsE, Nat.card_pos.ne'⟩))
      (S10.Msigma_isPiGroup M s (Nat.mem_primeFactors.mpr ⟨hsp, hsMσ, Nat.card_pos.ne'⟩))
  exact exists_aInvariant_sylow_subgroup hEnorm hcop (Or.inl ‹Group.IsSolvable ↥E›) q

/-- **Thm 13.9 tail の核** (BG: "By Lemma 13.6, `C_S(P)=1`; therefore by Lemma 13.1(a),
`p∈τ₁(M*)`"): `M*` 非共役, `p∈π(E)∩π(M*)`, `P ≤ M∩M*` が `p`-群, `S ≤ M_σ∩M*` 非自明で
`C_S(P)=1` (`S ⊓ C(P)=⊥`) のとき `p∈τ₁(M*)`。

`p∉τ₁(M*)` と仮定: `⁅M_σ∩M*, M∩M*⁆` 自明なら `M∩M*` が `M_σ∩M*` を中心化、非自明なら
Lemma 13.1(b) (`not_mem_tau2_of_interaction`) で `p∉τ₂(M*)`、Lemma 13.1(a)
(`pSubgroup_centralizes_Msigma_inf`) で `P` が `M_σ∩M*` を中心化。いずれも `S ≤ C(P)`、
よって `C_S(P)=S=1` で `S≠1` に矛盾。 -/
theorem mem_tau1_Mstar_of_einvariant_sylow [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {Mstar : Subgroup G} (hMstar : Mstar ∈ maximalSubgroups G)
    (hnc : ¬ ∃ g : G, MulAut.conj g • M = Mstar) {p : ℕ} [Fact p.Prime]
    (hpE : p ∈ (Nat.card ↥E).primeFactors) (hpMstar : p ∈ (Nat.card ↥Mstar).primeFactors)
    {P : Subgroup G} (hPM : P ≤ M ⊓ Mstar) (hPp : IsPGroup p ↥P)
    {S : Subgroup G} (hSMsigma : S ≤ S10.Msigma M) (hSMstar : S ≤ Mstar) (hSne : S ≠ ⊥)
    (hCSP : S ⊓ Subgroup.centralizer (P : Set G) = ⊥) :
    p ∈ tau1 Mstar := by
  by_contra hpτ1
  have hcent : P ≤ Subgroup.centralizer ((S10.Msigma M ⊓ Mstar : Subgroup G) : Set G) := by
    by_cases hcomm : ⁅(S10.Msigma M ⊓ Mstar : Subgroup G), (M ⊓ Mstar : Subgroup G)⁆ = ⊥
    · refine hPM.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp ?_)
      rw [Subgroup.commutator_comm]; exact hcomm
    · have hpτ2 : p ∉ tau2 Mstar := not_mem_tau2_of_interaction hG h hMstar hpE hcomm hnc
      exact pSubgroup_centralizes_Msigma_inf hG h hMstar hpE hpMstar hpτ1 hpτ2 hnc hPM hPp
  have hSinf : S ≤ S10.Msigma M ⊓ Mstar := le_inf hSMsigma hSMstar
  have hScP : S ≤ Subgroup.centralizer (P : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hcent hx) s (hSinf hs)).symm
  exact hSne (by rw [← hCSP]; exact le_antisymm (le_inf le_rfl hScP) inf_le_left)

/-- **Thm 13.9 tail: `C_S(P)=1`** (BG: "By Lemma 13.6, `C_S(P)=1`"): `q∈σ(M)`, `P ≤ E₁` 非自明,
`S` が `M_σ` の極大 `q`-部分群で `S ≤ M*` (`M* ≠ M` maximal) のとき `S ⊓ C(P) = 1`。

`S ⊓ C(P) ≠ 1` と仮定すると `ℰ_q¹` 部分群 `X ≤ S ⊓ C(P) ≤ M_σ ⊓ C(P)` が取れ、Lemma 13.6
(`maximalContaining_eq_singleton_of_E1`) の第2結論で `ℳ(S) = {M}`。しかし `S ≤ M*` ゆえ
`M* ∈ ℳ(S) = {M}`、すなわち `M* = M` で `M* ≠ M` に矛盾。 -/
theorem centralizer_sylow_inf_eq_bot [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {q : ℕ} [Fact q.Prime] (hqσ : q ∈ S10.sigma M)
    {P : Subgroup G} (hPE1 : P ≤ E₁) (hPne : P ≠ ⊥)
    {S : Subgroup G} (hSle : S ≤ S10.Msigma M) (hSq : IsPGroup q ↥S)
    (hSmax : ∀ T : Subgroup G, T ≤ S10.Msigma M → IsPGroup q ↥T → S ≤ T → S = T)
    {Mstar : Subgroup G} (hMstar : Mstar ∈ maximalSubgroups G) (hMne : Mstar ≠ M)
    (hSMstar : S ≤ Mstar) :
    S ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
  by_contra hne
  set C : Subgroup G := S ⊓ Subgroup.centralizer (P : Set G) with hC
  have hCq : IsPGroup q ↥C := hSq.to_le inf_le_left
  have hCnt : Nontrivial ↥C := (Subgroup.nontrivial_iff_ne_bot C).mpr hne
  obtain ⟨k, hk⟩ := hCq.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl; rw [pow_zero] at hk
    exact absurd hk (Finite.one_lt_card_iff_nontrivial.mpr hCnt).ne'
  have hqdvd : q ∣ Nat.card ↥C := by rw [hk]; exact dvd_pow_self q hk0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hqdvd
  have hXcard : Nat.card ↥(Subgroup.zpowers (x : G)) = q := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective C.subtype C.subtype_injective x).trans hx
  have hXmem : (Subgroup.zpowers (x : G)) ∈ elemAbelianOfRank G q 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXC : (Subgroup.zpowers (x : G)) ≤ S10.Msigma M ⊓ Subgroup.centralizer (P : Set G) := by
    refine Subgroup.zpowers_le.mpr ?_
    have hxC : (x : G) ∈ S ⊓ Subgroup.centralizer (P : Set G) := x.2
    rw [Subgroup.mem_inf] at hxC ⊢
    exact ⟨hSle hxC.1, hxC.2⟩
  have hMS := (maximalContaining_eq_singleton_of_E1 hG h hqσ hPE1 hPne hXmem hXC hSle hSq hSmax).2
  have hMem : Mstar ∈ maximalSubgroupsContaining S :=
    mem_maximalSubgroupsContaining.mpr ⟨hMstar, hSMstar⟩
  rw [hMS, Set.mem_singleton_iff] at hMem
  exact hMne hMem

/-- **Thm 13.9 WLOG conjugation**: `S` が `G` の Sylow `q`-部分群 (`|S| = q^{v_q(|G|)}`)、`q∈σ(M*)`
なら、`M*` のある共役 `conj g • M*` が `S` を含み `N_G(S) ⊆ conj g • M*`。`M*` の Sylow `q` を
`G` の Sylow `q` `S*` へ写し (`isSylow_sylowMap_of_mem_sigma`、`N_G(S*)⊆M*`)、`S` と `S*` の
Sylow 共役 (`MulAction.exists_smul_eq`) `conj g • S* = S` を取り、`S*≤M*`・`N_G(S*)⊆M*` を共役。 -/
theorem exists_conj_Mstar_normalizer_le [Finite G]
    {Mstar : Subgroup G} {q : ℕ} [Fact q.Prime] (hqσ : q ∈ S10.sigma Mstar)
    {S : Subgroup G} (hScard : Nat.card ↥S = q ^ (Nat.card G).factorization q) :
    ∃ g : G, S ≤ MulAut.conj g • Mstar ∧
      Subgroup.normalizer (S : Set G) ≤ MulAut.conj g • Mstar := by
  set SG : Sylow q G := Sylow.ofCard S hScard with hSGdef
  obtain ⟨Pstar⟩ := (inferInstance : Nonempty (Sylow q ↥Mstar))
  obtain ⟨Sstar, hSstar⟩ := S10.isSylow_sylowMap_of_mem_sigma hqσ Pstar
  have hNSstar : Subgroup.normalizer ((Sstar : Subgroup G) : Set G) ≤ Mstar := by
    rw [hSstar]; exact S10.normalizer_sylow_map_le_of_mem_sigma hqσ Pstar
  have hSstarM : (Sstar : Subgroup G) ≤ Mstar := by rw [hSstar]; exact Subgroup.map_subtype_le _
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Sstar SG
  have hconj : MulAut.conj g • (Sstar : Subgroup G) = S := by
    have h := congr_arg Sylow.toSubgroup hg
    rw [Sylow.coe_subgroup_smul, hSGdef, Sylow.coe_ofCard] at h
    exact h
  refine ⟨g, ?_, ?_⟩
  · rw [← hconj]; exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hSstarM
  · have hnorm : MulAut.conj g • Subgroup.normalizer ((Sstar : Subgroup G) : Set G)
        = Subgroup.normalizer ((MulAut.conj g • (Sstar : Subgroup G) : Subgroup G) : Set G) :=
      Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective
    rw [← hconj, ← hnorm]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hNSstar

/-- **BG Theorem 13.9** (mmd L3662): `M*∈ℳ` が `M` と非共役なら `σ(M)` と `σ(M*)` は disjoint。

証明は `M_σ` の冪零性で場合分け: `M_σ` 冪零なら Lemma 10.12 (`disjoint_of_not_conj` の冪零条項)
が直接与える (これは BG が Cor 12.6(f) = `τ₂≠∅` 経由で出すルートを `Msigma_nilpotent_of_tau2`
の対偶で吸収したもの)。`M_σ` 非冪零なら `Msigma_nilpotent_of_tau2` (Thm 12.5) の対偶で `E₂=⊥`、
Lemma 12.1(c) で `E₁≠⊥`、よって `τ₁(M)≠∅`; `q∈σ(M)∩σ(M*)` を仮定して `E`-不変 Sylow `S`、
Lemma 13.6 で `C_S(P)=1`、Lemma 13.1(a) で `p∈τ₁(M*)`、Lemma 13.8 (`Q=Q*=S`) で矛盾。 -/
theorem sigma_disjoint_of_nonconjugate [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroups G) (hnc : ¬ ∃ g : G, MulAut.conj g • M = Mstar) :
    Disjoint (S10.sigma M) (S10.sigma Mstar) := by
  classical
  -- Nilpotent `M_σ` ⟹ `σ`-disjointness directly (Lemma 10.12).
  by_cases hnil : Group.IsNilpotent ↥(S10.Msigma M)
  · rw [Set.disjoint_iff_inter_eq_empty]
    exact ((S10.disjoint_of_not_conj hG hM hMstar hnc).2 hnil).2
  -- Otherwise `τ₂(M)` carries no prime (Theorem 12.5 ⟹ `M_σ` nilpotent), so `E₂ = 1`.
  obtain ⟨E, E₁, E₂, E₃, h⟩ := exists_subgroupESetup hG hM
  have hE2bot : E₂ = ⊥ := by
    by_contra hE2ne
    have hcard1 : Nat.card ↥E₂ ≠ 1 :=
      (Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot E₂).mpr hE2ne)).ne'
    obtain ⟨p, hpprime, hpdvd⟩ := (Nat.card ↥E₂).exists_prime_and_dvd hcard1
    have : Fact p.Prime := ⟨hpprime⟩
    have hc2 : Nat.card ↥(E₂.subgroupOf E) = Nat.card ↥E₂ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv
    have hpτ2 : p ∈ tau2 M :=
      h.E₂_hall.1 p (by rw [hc2]; exact Nat.mem_primeFactors.mpr ⟨hpprime, hpdvd, Nat.card_pos.ne'⟩)
    obtain ⟨A, hA, hAE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG h hpτ2
    exact hnil (Msigma_nilpotent_of_tau2 hG hM hpτ2 hA (hAE.trans h.E_le)).1
  have hE1ne : E₁ ≠ ⊥ := SubgroupESetup.E1_ne_bot_of_E2_eq_bot hG h hE2bot
  -- `q ∈ σ(M) ∩ σ(M*)` now yields a contradiction (Lemma 13.6 + 13.8 with `Q = Q* = S`).
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
  intro q hq
  rw [Set.mem_inter_iff] at hq
  obtain ⟨hqM, hqMstar⟩ := hq
  have hqfact : Fact q.Prime :=
    ⟨Nat.prime_of_mem_primeFactors ((S10.mem_sigma_iff M q).mp hqM).1⟩
  -- `S` = an `E`-invariant Sylow `q`-subgroup of `M_σ`; it is a Sylow `q` of `G`, maximal, `≠ 1`.
  obtain ⟨S, hSMσ, hSq, hSEnorm, hScard⟩ := exists_einvariant_sylow_Msigma hG h q
  have hSmax : ∀ T : Subgroup G, T ≤ S10.Msigma M → IsPGroup q ↥T → S ≤ T → S = T :=
    fun T hTM hTq hST => eq_of_le_of_isPGroup_card_eq_factorization hScard hTM hTq hST
  have hScardG : Nat.card ↥S = q ^ (Nat.card G).factorization q := by
    rw [hScard, factorization_Msigma_eq_of_mem_sigma hG hM hqM, factorization_M_eq_G_of_mem_sigma
        hqM]
  have hvpos : 0 < (Nat.card ↥(S10.Msigma M)).factorization q := by
    rw [factorization_Msigma_eq_of_mem_sigma hG hM hqM]
    obtain ⟨_, hqdvdM, hMne⟩ := Nat.mem_primeFactors.mp ((S10.mem_sigma_iff M q).mp hqM).1
    exact hqfact.out.factorization_pos_of_dvd hMne hqdvdM
  have hSne : S ≠ ⊥ := by
    intro hb
    have h1 : Nat.card ↥S = 1 := by rw [hb]; exact Subgroup.card_bot
    rw [hScard, Nat.pow_eq_one] at h1
    rcases h1 with h1 | h0
    · exact hqfact.out.ne_one h1
    · omega
  have hSinf_M : S ≤ M := hSMσ.trans (S10.Msigma_le M)
  have hNSM : Subgroup.normalizer (S : Set G) ≤ M :=
    normalizer_einvariant_sylow_le hG hM hqM hSMσ hScard
  -- WLOG: conjugate `M*` to `Mstar' = conj g • M*` with `S ≤ Mstar'`, `N_G(S) ⊆ Mstar'`.
  obtain ⟨g, hSMstar', hNSMstar'⟩ := exists_conj_Mstar_normalizer_le hqMstar hScardG
  set Mstar' : Subgroup G := MulAut.conj g • Mstar with hMstar'def
  have hMstar'mem : Mstar' ∈ maximalSubgroups G :=
    mem_maximalSubgroups.mpr (isCoatom_conj_smul (mem_maximalSubgroups.mp hMstar))
  have hnc' : ¬ ∃ gg : G, MulAut.conj gg • M = Mstar' := by
    rintro ⟨gg, hgg⟩
    refine hnc ⟨g⁻¹ * gg, ?_⟩
    rw [hMstar'def] at hgg
    rw [map_mul, mul_smul, hgg, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hMstar'ne : Mstar' ≠ M := fun heq => hnc' ⟨1, by rw [map_one, one_smul, heq]⟩
  -- `p ∈ τ₁(M)` (from `E₁ ≠ 1`) and `P = ⟨x⟩ ∈ ℰ_p¹(E₁)`.
  have hE1card1 : Nat.card ↥E₁ ≠ 1 :=
    (Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot E₁).mpr hE1ne)).ne'
  obtain ⟨p, hpprime, hpdvd⟩ := (Nat.card ↥E₁).exists_prime_and_dvd hE1card1
  have : Fact p.Prime := ⟨hpprime⟩
  have hc1 : Nat.card ↥(E₁.subgroupOf E) = Nat.card ↥E₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv
  have hpτ1 : p ∈ tau1 M :=
    h.E₁_hall.1 p (by rw [hc1]; exact Nat.mem_primeFactors.mpr ⟨hpprime, hpdvd, Nat.card_pos.ne'⟩)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  have hPcard : Nat.card ↥(Subgroup.zpowers (x : G)) = p := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective E₁.subtype E₁.subtype_injective x).trans hx
  have hPmem : (Subgroup.zpowers (x : G)) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hPcard, by rw [hPcard, pow_one]⟩
  have hPE1 : (Subgroup.zpowers (x : G)) ≤ E₁ := Subgroup.zpowers_le.mpr x.2
  have hP1ne : (Subgroup.zpowers (x : G)) ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hPmem
  have hPp : IsPGroup p ↥(Subgroup.zpowers (x : G)) := (mem_elemAbelianOfRank.mp hPmem).1.isPGroup
  have hPE : (Subgroup.zpowers (x : G)) ≤ E := hPE1.trans h.E₁_le
  have hPinv : (Subgroup.zpowers (x : G)) ≤ Subgroup.normalizer (S : Set G) := hPE.trans hSEnorm
  have hPM : (Subgroup.zpowers (x : G)) ≤ M := hPE.trans h.E_le
  have hPMstar' : (Subgroup.zpowers (x : G)) ≤ Mstar' := hPinv.trans hNSMstar'
  have hPMM' : (Subgroup.zpowers (x : G)) ≤ M ⊓ Mstar' := le_inf hPM hPMstar'
  -- `C_S(P) = 1` (Lemma 13.6 via `ℳ(S) = {M}`).
  have hCSP : S ⊓ Subgroup.centralizer ((Subgroup.zpowers (x : G)) : Set G) = ⊥ :=
    centralizer_sylow_inf_eq_bot hG h hqM hPE1 hP1ne hSMσ hSq hSmax hMstar'mem hMstar'ne hSMstar'
  -- `S` is a maximal `q`-subgroup of `M ⊓ Mstar'` (it is a Sylow `q` of `G`).
  have hScardTop : Nat.card ↥S = q ^ (Nat.card ↥(⊤ : Subgroup G)).factorization q := by
    rw [hScardG, Subgroup.card_top]
  have hQmax : ∀ T : Subgroup G, T ≤ M ⊓ Mstar' → IsPGroup q ↥T → S ≤ T → S = T :=
    fun T _ hTq hST => eq_of_le_of_isPGroup_card_eq_factorization hScardTop le_top hTq hST
  have hSinf : S ≤ M ⊓ Mstar' := le_inf hSinf_M hSMstar'
  -- `p ∈ τ₁(Mstar')`.
  have hpE : p ∈ (Nat.card ↥E).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpprime, hpdvd.trans (Subgroup.card_dvd_of_le h.E₁_le),
        Nat.card_pos.ne'⟩
  have hpMstar : p ∈ (Nat.card ↥Mstar').primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpprime, hPcard ▸ Subgroup.card_dvd_of_le hPMstar', Nat.card_pos.ne'⟩
  have hpτ1star : p ∈ tau1 Mstar' :=
    mem_tau1_Mstar_of_einvariant_sylow hG h hMstar'mem hnc' hpE hpMstar hPMM' hPp hSMσ hSMstar' hSne
        hCSP
  -- Lemma 13.8 with `Q = Q* = S` yields the contradiction.
  exact forbidden_config_impossible hG hM hMstar'mem hnc' hpτ1 hpτ1star hPmem hPMM'
    hSinf hSq hQmax hSinf hSq hQmax hPinv hPinv hCSP hCSP hNSMstar' hNSM

/-- **BG Theorem 13.10, GAP A factorization** (the "Q ∈ Syl_q(M)" hidden step): for `q ∈ τ₃(M)`,
the `q`-part of `|M|` equals the `q`-part of `|E₃|`. Hence the Sylow `q`-subgroup of `E₃` is a
Sylow `q`-subgroup of `M`. Proof: `|M| = |M_σ|·|E|` (`card_Msigma_mul_card_E`), `q ∤ |M_σ|`
(`M_σ` is a `σ(M)`-group and `q ∉ σ(M)` since `τ₃ ∩ σ = ∅`), and `q ∤ [E:E₃]` (`E₃` is a Hall
`τ₃(M)`-subgroup of `E`, so its index is a `τ₃'`-number), so `|E|_q = |E₃|_q`. -/
theorem factorization_M_eq_E3_of_mem_tau3 [Finite G] {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) {q : ℕ} (hqprime : q.Prime) (hq : q ∈ tau3 M) :
    (Nat.card ↥M).factorization q = (Nat.card ↥E₃).factorization q := by
  have hqσ : q ∉ S10.sigma M := tau3_subset_sigma_compl M hq
  have hMσpi : Subgroup.IsPiSubgroup (S10.sigma M) (S10.Msigma M) :=
    isPiSubgroup_opiCoreInG _ _
  have hMσ0 : (Nat.card ↥(S10.Msigma M)).factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun hdvd =>
      hqσ (hMσpi q (Nat.mem_primeFactors.mpr ⟨hqprime, hdvd, Nat.card_pos.ne'⟩)))
  have hME : Nat.card ↥(S10.Msigma M) * Nat.card ↥E = Nat.card ↥M := card_Msigma_mul_card_E h
  have hEE3 : Nat.card ↥E₃ * (E₃.subgroupOf E).index = Nat.card ↥E := by
    have hc := Subgroup.card_mul_index (E₃.subgroupOf E)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv] at hc
  have hidxne : (E₃.subgroupOf E).index ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hEE3; exact Nat.card_pos.ne' hEE3.symm
  have hidx0 : ((E₃.subgroupOf E).index).factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun hdvd =>
      h.E₃_hall.2 q (Nat.mem_primeFactors.mpr ⟨hqprime, hdvd, hidxne⟩) hq)
  have hstep1 : (Nat.card ↥M).factorization q = (Nat.card ↥E).factorization q := by
    rw [← hME, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      hMσ0, zero_add]
  have hstep2 : (Nat.card ↥E).factorization q = (Nat.card ↥E₃).factorization q := by
    rw [← hEE3, Nat.factorization_mul Nat.card_pos.ne' hidxne, Finsupp.add_apply, hidx0, add_zero]
  rw [hstep1, hstep2]

/-- In a cyclic `q`-subgroup `Q ≤ G`, the order-`q` subgroup `Q₀` is contained in **every**
nontrivial subgroup `T ≤ Q` (it is the unique minimal subgroup `Ω₁`). Public replication of the
`Ω₁`-bookkeeping used in §12 (`S12_Lemma1211`'s private `le_of_ne_bot_of_le_cyclic`). -/
theorem line_le_of_ne_bot_of_le_cyclic [Finite G] {q : ℕ} [Fact q.Prime]
    {Q Q₀ T : Subgroup G} (hQcyc : IsCyclic ↥Q) (hQpg : IsPGroup q ↥Q)
    (hQ₀Q : Q₀ ≤ Q) (hQ₀card : Nat.card ↥Q₀ = q)
    (hTQ : T ≤ Q) (hTne : T ≠ ⊥) : Q₀ ≤ T := by
  classical
  have hTpg : IsPGroup q ↥T := fun t => by
    obtain ⟨k, hk⟩ := hQpg ⟨(t : G), hTQ t.2⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  have hqT : q ∣ Nat.card ↥T := by
    rcases IsPGroup.iff_card.mp hTpg with ⟨k, hkcard⟩
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · exact absurd (Subgroup.card_eq_one.mp (by simpa using hkcard)) hTne
    · rw [hkcard]; exact dvd_pow_self q hkpos.ne'
  obtain ⟨T₀, hT₀card⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := ↥T) q (n := 1) (by rwa [pow_one])
  set T₀' : Subgroup G := T₀.map T.subtype with hT₀'def
  have hT₀'card : Nat.card ↥T₀' = q := by
    rw [hT₀'def, Subgroup.card_map_of_injective T.subtype_injective, hT₀card, pow_one]
  have hT₀'T : T₀' ≤ T := Subgroup.map_subtype_le _
  have hQ₀eq : Q₀.subgroupOf Q = T₀'.subgroupOf Q := by
    apply OddOrder.GroupTheory.cyclic_subgroup_eq_of_card_eq (C := ↥Q)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ₀Q).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hT₀'T.trans hTQ)).toEquiv,
      hQ₀card, hT₀'card]
  have heq : Q₀ = T₀' := by
    have h1 := congrArg (fun X : Subgroup ↥Q => X.map Q.subtype) hQ₀eq
    simpa [Subgroup.map_subgroupOf_eq_of_le hQ₀Q,
      Subgroup.map_subgroupOf_eq_of_le (hT₀'T.trans hTQ)] using h1
  rw [heq]; exact hT₀'T

/-- **Coprime-action indecomposability for a cyclic `q`-subgroup**: if `Q ≤ G` is a cyclic
`q`-group, `P` normalizes `Q` with `|P|` coprime to `|Q|`, and `P` does **not** centralize `Q`,
then `P` acts regularly on `Q`, i.e. `Q ⊓ C_G(P) = 1`. (A cyclic `q`-group is directly
indecomposable; coprime action gives `Q = C_Q(P) × [Q,P]`, so `C_Q(P) ∈ {1, Q}`, and the line
`Ω₁(Q)` cannot lie in both `C_Q(P)` and the nontrivial `[Q,P]`.) -/
theorem inf_centralizer_eq_bot_of_coprime_cyclic [Finite G] {q : ℕ} [Fact q.Prime]
    {Q P : Subgroup G} (hQcyc : IsCyclic ↥Q) (hQq : IsPGroup q ↥Q)
    (hPN : P ≤ Subgroup.normalizer (Q : Set G))
    (hcop : Nat.Coprime (Nat.card ↥P) (Nat.card ↥Q))
    (hnc : ¬ Q ≤ Subgroup.centralizer (P : Set G)) :
    Q ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
  classical
  have hQne : Q ≠ ⊥ := fun hb => hnc (hb ▸ bot_le)
  have hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    let : CommGroup ↥Q := IsCyclic.commGroup
    intro a ha b hb
    exact Subtype.ext_iff.mp (mul_comm (⟨a, ha⟩ : ↥Q) (⟨b, hb⟩ : ↥Q))
  have hcomm : ⁅Q, P⁆ ⊓ Subgroup.centralizer (P : Set G) = ⊥ :=
    commutator_inf_centralizer_eq_bot_of_isCommutative hQab hPN hcop
  have hcommQ : ⁅Q, P⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hbN : b ∈ Subgroup.normalizer (Q : Set G) := hPN hb
    have hconj : b * a⁻¹ * b⁻¹ ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp hbN a⁻¹).mp (Q.inv_mem ha)
      simpa using this
    rw [commutatorElement_def]
    have hreg : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [hreg]; exact Q.mul_mem ha hconj
  have hcommne : ⁅Q, P⁆ ≠ ⊥ := fun hb =>
    hnc (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hb)
  have hqQ : q ∣ Nat.card ↥Q := by
    rcases IsPGroup.iff_card.mp hQq with ⟨k, hkcard⟩
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · exact absurd (Subgroup.card_eq_one.mp (by simpa using hkcard)) hQne
    · rw [hkcard]; exact dvd_pow_self q hkpos.ne'
  obtain ⟨Q₀0, hQ₀0card⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := ↥Q) q (n := 1) (by rwa [pow_one])
  set Q₀ : Subgroup G := Q₀0.map Q.subtype with hQ₀def
  have hQ₀Q : Q₀ ≤ Q := Subgroup.map_subtype_le _
  have hQ₀card : Nat.card ↥Q₀ = q := by
    rw [hQ₀def, Subgroup.card_map_of_injective Q.subtype_injective, hQ₀0card, pow_one]
  by_contra hCne
  have hL1 : Q₀ ≤ Q ⊓ Subgroup.centralizer (P : Set G) :=
    line_le_of_ne_bot_of_le_cyclic hQcyc hQq hQ₀Q hQ₀card inf_le_left hCne
  have hL2 : Q₀ ≤ ⁅Q, P⁆ :=
    line_le_of_ne_bot_of_le_cyclic hQcyc hQq hQ₀Q hQ₀card hcommQ hcommne
  have hL2C : Q₀ ≤ ⁅Q, P⁆ ⊓ Subgroup.centralizer (P : Set G) :=
    le_inf hL2 (hL1.trans inf_le_right)
  rw [hcomm, le_bot_iff] at hL2C
  rw [hL2C, Subgroup.card_bot] at hQ₀card
  exact (Fact.out : q.Prime).one_lt.ne' hQ₀card.symm

/-- **BG Theorem 13.10, structural brick** (gap-free): if `P ∈ ℰ_p¹(E₁)` does not centralize the
cyclic Hall subgroup `E₃`, then there is a prime `q ∈ τ₃(M)` and a nontrivial `q`-subgroup
`Q ≤ E₃` on which `P` acts regularly (`Q ⊓ C_G(P) = ⊥`), with `P ≤ N_G(Q)`.

`Q` is an order-`q` subgroup of the commutator `K = ⁅E₃, P⁆ ≤ E₃`, which is nontrivial (else `P`
would centralize `E₃`) and satisfies `K ⊓ C_G(P) = ⊥` by coprime action on the abelian `E₃`
(`commutator_inf_centralizer_eq_bot_of_isCommutative`); `q := (Nat.card K).minFac`, and
`P ≤ N_G(Q)` holds for every `Q ≤ E₃` because `E₃` is cyclic (`E_le_normalizer_of_le_E3`). -/
theorem exists_tau3_regular_qsubgroup_of_not_centralize [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} [Fact p.Prime] {P : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1)
    (hPE1 : P ≤ E₁) (hPnc : ¬ P ≤ Subgroup.centralizer (E₃ : Set G)) :
    ∃ q : ℕ, q.Prime ∧ q ∈ tau3 M ∧ ∃ Q : Subgroup G,
      IsPGroup q ↥Q ∧ Q ≤ E₃ ∧ Q ≠ ⊥ ∧
      Q ⊓ Subgroup.centralizer (P : Set G) = ⊥ ∧
      P ≤ Subgroup.normalizer (Q : Set G) := by
  classical
  have hE3cyc : IsCyclic ↥E₃ := h.E3_isCyclic hG
  have hPcardp : Nat.card ↥P = p := by rw [← pow_one p]; exact hP.2
  -- `P ≤ N_G(E₃)`.
  have hPN3 : P ≤ Subgroup.normalizer (E₃ : Set G) :=
    hPE1.trans (h.E₁_le.trans (h.E3_normal hG))
  have hPE : P ≤ E := hPE1.trans h.E₁_le
  -- `p ∈ τ₁(M)`.
  have hc1 : Nat.card ↥(E₁.subgroupOf E) = Nat.card ↥E₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv
  have hpdvdE1 : p ∣ Nat.card ↥E₁ := hPcardp ▸ Subgroup.card_dvd_of_le hPE1
  have hpτ1 : p ∈ tau1 M :=
    h.E₁_hall.1 p (hc1 ▸ Nat.mem_primeFactors.mpr ⟨Fact.out, hpdvdE1, Nat.card_pos.ne'⟩)
  -- `p ∤ |E₃|`: else `p ∈ τ₃(M)`, contradicting `p ∈ τ₁(M)`.
  have hc3 : Nat.card ↥(E₃.subgroupOf E) = Nat.card ↥E₃ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv
  have hpndvd : ¬ p ∣ Nat.card ↥E₃ := fun hpd =>
    not_mem_tau3_of_mem_tau1 hpτ1
      (h.E₃_hall.1 p (hc3 ▸ Nat.mem_primeFactors.mpr ⟨Fact.out, hpd, Nat.card_pos.ne'⟩))
  have hcop : Nat.Coprime (Nat.card ↥P) (Nat.card ↥E₃) := by
    rw [hPcardp]; exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpndvd
  -- `E₃` abelian.
  have hE3ab : ∀ a ∈ E₃, ∀ b ∈ E₃, a * b = b * a := by
    let : CommGroup ↥E₃ := IsCyclic.commGroup
    intro a ha b hb
    exact Subtype.ext_iff.mp (mul_comm (⟨a, ha⟩ : ↥E₃) (⟨b, hb⟩ : ↥E₃))
  -- `K = ⁅E₃, P⁆`: regular under `P`, nontrivial, `≤ E₃`.
  have hKinfC : ⁅E₃, P⁆ ⊓ Subgroup.centralizer (P : Set G) = ⊥ :=
    commutator_inf_centralizer_eq_bot_of_isCommutative hE3ab hPN3 hcop
  have hKne : ⁅E₃, P⁆ ≠ ⊥ := fun hb =>
    hPnc (Subgroup.le_centralizer_iff.mpr (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hb))
  have hKE3 : ⁅E₃, P⁆ ≤ E₃ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hbN : b ∈ Subgroup.normalizer (E₃ : Set G) := hPN3 hb
    have hconj : b * a⁻¹ * b⁻¹ ∈ E₃ := by
      have := (Subgroup.mem_normalizer_iff.mp hbN a⁻¹).mp (E₃.inv_mem ha)
      simpa using this
    rw [commutatorElement_def]
    have hreg : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [hreg]
    exact E₃.mul_mem ha hconj
  -- pick a prime `q ∣ |K|` and an order-`q` subgroup `Q` of `K`.
  have hn1 : 1 < Nat.card ↥(⁅E₃, P⁆) :=
    Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot _).mpr hKne)
  set q := (Nat.card ↥(⁅E₃, P⁆)).minFac with hq
  have hqprime : q.Prime := Nat.minFac_prime (by omega)
  have : Fact q.Prime := ⟨hqprime⟩
  have hqdvd : q ∣ Nat.card ↥(⁅E₃, P⁆) := Nat.minFac_dvd _
  obtain ⟨Q₀, hQ₀card⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := ↥(⁅E₃, P⁆)) q (n := 1) (by rwa [pow_one])
  refine ⟨q, hqprime, ?_, Q₀.map (⁅E₃, P⁆).subtype, ?_, ?_, ?_, ?_, ?_⟩
  · -- `q ∈ τ₃(M)`.
    have hqE3 : q ∣ Nat.card ↥E₃ := hqdvd.trans (Subgroup.card_dvd_of_le hKE3)
    exact h.E₃_hall.1 q (hc3 ▸ Nat.mem_primeFactors.mpr ⟨hqprime, hqE3, Nat.card_pos.ne'⟩)
  · -- `IsPGroup q Q` (order `q`).
    have hQcard : Nat.card ↥(Q₀.map (⁅E₃, P⁆).subtype) = q := by
      rw [Subgroup.card_map_of_injective (⁅E₃, P⁆).subtype_injective, hQ₀card, pow_one]
    exact IsPGroup.of_card (by rw [hQcard, pow_one])
  · -- `Q ≤ E₃`.
    exact (Subgroup.map_subtype_le _).trans hKE3
  · -- `Q ≠ ⊥`.
    have hQcard : Nat.card ↥(Q₀.map (⁅E₃, P⁆).subtype) = q := by
      rw [Subgroup.card_map_of_injective (⁅E₃, P⁆).subtype_injective, hQ₀card, pow_one]
    intro hb
    rw [hb, Subgroup.card_bot] at hQcard
    exact hqprime.one_lt.ne' hQcard.symm
  · -- `Q ⊓ C_G(P) = ⊥`.
    rw [← le_bot_iff, ← hKinfC]
    exact le_inf (inf_le_left.trans (Subgroup.map_subtype_le _)) inf_le_right
  · -- `P ≤ N_G(Q)`.
    exact hPE.trans (E_le_normalizer_of_le_E3 hG h ((Subgroup.map_subtype_le _).trans hKE3))

/-- **BG Theorem 13.10, full-Sylow brick** (GAP A): if `P ∈ ℰ_p¹(E₁)` does not centralize the
cyclic Hall subgroup `E₃`, then there is a prime `q ∈ τ₃(M)` (`q ≠ p`) and a **Sylow `q`-subgroup
`Q` of `M`** with `Q ≤ E₃`, `Q ⊓ C_G(P) = ⊥` (P acts regularly), and `P ≤ N_G(Q)`.

`Q` is the full Sylow `q`-subgroup of `E₃`; it is a Sylow `q`-subgroup of `M` by
`factorization_M_eq_E3_of_mem_tau3` (so Lemma 12.18 branch 2 fires). Regularity comes from the
rank-1 datum (`exists_tau3_regular_qsubgroup_of_not_centralize`) and coprime indecomposability
(`inf_centralizer_eq_bot_of_coprime_cyclic`): the order-`q` line `Q' ≤ Q` is not centralized by
`P`, so neither is `Q`, hence `C_Q(P) = 1`. -/
theorem exists_tau3_sylowM_regular_of_not_centralize [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} [Fact p.Prime] {P : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1)
    (hPE1 : P ≤ E₁) (hPnc : ¬ P ≤ Subgroup.centralizer (E₃ : Set G)) :
    ∃ q : ℕ, q.Prime ∧ q ∈ tau3 M ∧ q ≠ p ∧ ∃ Q : Subgroup G,
      IsPGroup q ↥Q ∧ Q ≤ E₃ ∧ Q ≠ ⊥ ∧
      Q ⊓ Subgroup.centralizer (P : Set G) = ⊥ ∧
      P ≤ Subgroup.normalizer (Q : Set G) ∧
      (∀ T : Subgroup G, T ≤ M → IsPGroup q ↥T → Q ≤ T → Q = T) := by
  classical
  have hE3cyc : IsCyclic ↥E₃ := h.E3_isCyclic hG
  obtain ⟨q, hqprime, hqτ3, Q', hQ'p, hQ'E3, hQ'ne, hQ'C, hQ'N⟩ :=
    exists_tau3_regular_qsubgroup_of_not_centralize hG h hP hPE1 hPnc
  have : Fact q.Prime := ⟨hqprime⟩
  -- `p ∈ τ₁(M)`, hence `q ≠ p`.
  have hPcardp : Nat.card ↥P = p := by rw [← pow_one p]; exact hP.2
  have hc1 : Nat.card ↥(E₁.subgroupOf E) = Nat.card ↥E₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv
  have hpτ1 : p ∈ tau1 M :=
    h.E₁_hall.1 p (hc1 ▸ Nat.mem_primeFactors.mpr
      ⟨Fact.out, hPcardp ▸ Subgroup.card_dvd_of_le hPE1, Nat.card_pos.ne'⟩)
  have hpq : q ≠ p := fun heq => not_mem_tau3_of_mem_tau1 hpτ1 (heq ▸ hqτ3)
  -- full Sylow `q`-subgroup of `↥E₃`.
  let : CommGroup ↥E₃ := IsCyclic.commGroup
  obtain ⟨S₃⟩ : Nonempty (Sylow q ↥E₃) := inferInstance
  have : (S₃ : Subgroup ↥E₃).Normal := Subgroup.normal_of_isMulCommutative _
  have : Unique (Sylow q ↥E₃) := S₃.unique_of_normal inferInstance
  set Q : Subgroup G := (S₃ : Subgroup ↥E₃).map E₃.subtype with hQdef
  have hQE3 : Q ≤ E₃ := Subgroup.map_subtype_le _
  have hQcardE3 : Nat.card ↥Q = q ^ (Nat.card ↥E₃).factorization q := by
    rw [hQdef, Subgroup.card_map_of_injective E₃.subtype_injective, S₃.card_eq_multiplicity]
  have hQcardM : Nat.card ↥Q = q ^ (Nat.card ↥M).factorization q := by
    rw [hQcardE3, factorization_M_eq_E3_of_mem_tau3 h hqprime hqτ3]
  have hQp : IsPGroup q ↥Q := IsPGroup.iff_card.mpr ⟨_, hQcardE3⟩
  have hQcyc : IsCyclic ↥Q :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hQE3).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hQE3).surjective
  -- `Q' ≤ Q` (the rank-1 line lies in the unique Sylow `q`-subgroup of `E₃`).
  have hQ'Q : Q' ≤ Q := by
    have hQ'pg : IsPGroup q ↥(Q'.subgroupOf E₃) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ'p
      exact IsPGroup.iff_card.mpr
        ⟨k, by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ'E3).toEquiv, hk]⟩
    obtain ⟨S', hS'⟩ := hQ'pg.exists_le_sylow
    have hle : Q'.subgroupOf E₃ ≤ (S₃ : Subgroup ↥E₃) := (Subsingleton.elim S' S₃) ▸ hS'
    calc Q' = (Q'.subgroupOf E₃).map E₃.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hQ'E3).symm
      _ ≤ (S₃ : Subgroup ↥E₃).map E₃.subtype := Subgroup.map_mono hle
      _ = Q := rfl
  -- `¬ (Q ≤ C(P))`, then coprime indecomposability gives `C_Q(P) = ⊥`.
  have hQnc : ¬ Q ≤ Subgroup.centralizer (P : Set G) := by
    intro hQC
    apply hQ'ne
    have heq : Q' ⊓ Subgroup.centralizer (P : Set G) = Q' := inf_eq_left.mpr (hQ'Q.trans hQC)
    rw [hQ'C] at heq
    exact heq.symm
  have hPNQ : P ≤ Subgroup.normalizer (Q : Set G) :=
    (hPE1.trans h.E₁_le).trans (E_le_normalizer_of_le_E3 hG h hQE3)
  have hcop : Nat.Coprime (Nat.card ↥P) (Nat.card ↥Q) := by
    rw [hPcardp, hQcardE3]
    exact ((Nat.coprime_primes Fact.out hqprime).mpr hpq.symm).pow_right _
  have hCQ : Q ⊓ Subgroup.centralizer (P : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_coprime_cyclic hQcyc hQp hPNQ hcop hQnc
  have hqdvdE3 : q ∣ Nat.card ↥E₃ := by
    have hqQ' : q ∣ Nat.card ↥Q' := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ'p
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · rw [pow_zero] at hk; exact absurd (Subgroup.card_eq_one.mp hk) hQ'ne
      · rw [hk]; exact dvd_pow_self q hkpos.ne'
    exact hqQ'.trans (Subgroup.card_dvd_of_le hQ'E3)
  have hQne : Q ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hQcardE3
    have hv : (Nat.card ↥E₃).factorization q ≠ 0 :=
      (Nat.Prime.factorization_pos_of_dvd hqprime Nat.card_pos.ne' hqdvdE3).ne'
    rcases Nat.pow_eq_one.mp hQcardE3.symm with h1 | h0
    · exact hqprime.ne_one h1
    · exact hv h0
  refine ⟨q, hqprime, hqτ3, hpq, Q, hQp, hQE3, hQne, hCQ, hPNQ, ?_⟩
  exact fun T hTM hTq hQT => eq_of_le_of_isPGroup_card_eq_factorization hQcardM hTM hTq hQT

/-- **BG Theorem 13.10, M*-extraction brick** (gap-free): for `q ∈ τ₃(M)` and a nontrivial
`q`-subgroup `Q ≤ E₃`, there is a maximal subgroup `M* ⊇ N_G(Q)` that is not conjugate to `M`
in `G` (hence `M* ≠ M`). This is the `M* ∈ ℳ(N_G(Q))` step of Thm 13.10's proof: `N_G(Q) ≠ G`
(else `Q ◁ G`, impossible in the simple `G` with `Q ≠ 1, ≠ G`), so a maximal `M*` lies over it,
and non-conjugacy is `not_conj_of_mem_tau1_union_tau3_of_normalizer_le` (`q ∈ τ₃ ⊆ τ₁ ∪ τ₃`). -/
theorem exists_maximal_over_normalizer_not_conj_of_le_E3 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {q : ℕ} [Fact q.Prime] (hq : q ∈ tau3 M) {Q : Subgroup G}
    (hQE3 : Q ≤ E₃) (hQne : Q ≠ ⊥) (hQq : IsPGroup q ↥Q) :
    ∃ Mstar : Subgroup G, Mstar ∈ maximalSubgroups G ∧
      Subgroup.normalizer (Q : Set G) ≤ Mstar ∧
      ¬ ∃ g : G, MulAut.conj g • M = Mstar := by
  have hQM : Q ≤ M := hQE3.trans (h.E₃_le.trans h.E_le)
  have hNQne : Subgroup.normalizer (Q : Set G) ≠ ⊤ := by
    intro htop
    have : Q.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hG.simple.eq_bot_or_eq_top_of_normal Q inferInstance with hb | ht
    · exact hQne hb
    · exact (mem_maximalSubgroups.mp h.mem_maximal).1 (top_le_iff.mp (ht ▸ hQM))
  obtain ⟨Mstar, hMstarCo, hNQM⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer (Q : Set G))).resolve_left hNQne
  refine ⟨Mstar, mem_maximalSubgroups.mpr hMstarCo, hNQM, ?_⟩
  exact not_conj_of_mem_tau1_union_tau3_of_normalizer_le hG h.mem_maximal
    (Set.mem_union_right _ hq) hQM hQne hQq hNQM

/-- **BG Theorem 13.10, M_α-interaction package** (GAP A endgame): if `P ∈ ℰ_p¹(E₁)` does not
centralize `E₃`, then `C_{M_α}(P) ≠ 1` and `C_{M_α}(PQ) = 1` for the regular Sylow `q`-subgroup
`Q ≤ E₃` of `M`. Applies Lemma 12.18 branch 2 (`Q ∈ Syl_q(M)` from the full-Sylow brick, `M* ∈
ℳ(N_G(Q))` with `M* ≠ M` from the non-conjugacy brick), which outputs `M_α ≠ 1` and the two
centralizer facts. This feeds (c) (`Malpha_le_Msigma`) and (a) (the non-prime argument). -/
theorem malpha_centralizer_facts_of_not_centralize [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} [Fact p.Prime] {P : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1)
    (hPE1 : P ≤ E₁) (hPnc : ¬ P ≤ Subgroup.centralizer (E₃ : Set G)) :
    ∃ Q : Subgroup G, Q ≤ E₃ ∧ Q ≠ ⊥ ∧
      S10.Malpha M ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ ∧
      S10.Malpha M ⊓ Subgroup.centralizer ((P ⊔ Q : Subgroup G) : Set G) = ⊥ := by
  classical
  obtain ⟨q, hqprime, hqτ3, hpq, Q, hQq, hQE3, hQne, hCQ, hPNQ, hQsyl⟩ :=
    exists_tau3_sylowM_regular_of_not_centralize hG h hP hPE1 hPnc
  have : Fact q.Prime := ⟨hqprime⟩
  have hPcardp : Nat.card ↥P = p := by rw [← pow_one p]; exact hP.2
  have hc1 : Nat.card ↥(E₁.subgroupOf E) = Nat.card ↥E₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv
  have hpτ1 : p ∈ tau1 M :=
    h.E₁_hall.1 p (hc1 ▸ Nat.mem_primeFactors.mpr
      ⟨Fact.out, hPcardp ▸ Subgroup.card_dvd_of_le hPE1, Nat.card_pos.ne'⟩)
  have hPM : P ≤ M := hPE1.trans (h.E₁_le.trans h.E_le)
  have hQM : Q ≤ M := hQE3.trans (h.E₃_le.trans h.E_le)
  obtain ⟨Mstar, hMstarMax, hNQ, hnc⟩ :=
    exists_maximal_over_normalizer_not_conj_of_le_E3 hG h hqτ3 hQE3 hQne hQq
  have hMMstar : M ≠ Mstar := fun heq => hnc ⟨1, by rw [heq, map_one, one_smul]⟩
  have hMNQ : maximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) ≠ {M} := by
    intro hsingle
    have hMstar_mem : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) :=
      mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hMstarMax, hNQ⟩
    rw [hsingle, Set.mem_singleton_iff] at hMstar_mem
    exact hMMstar hMstar_mem.symm
  obtain ⟨_, _, _, hCMαP, hCMαPQ⟩ :=
    (tau1_Malpha_interaction hG h.mem_maximal hpq hpτ1 hP hPM hQM hQne hQq hPNQ hCQ hMNQ).2 hQsyl
  exact ⟨Q, hQE3, hQne, hCMαP, hCMαPQ⟩

/-- **BG Theorem 13.10, GAP B** (the non-prime argument): from `C_{M_α}(P) ≠ 1` and
`C_{M_α}(PQ) = 1` (with `Q ≤ E₃`, `P ≤ E₁`), `E₁E₃` does **not** act in a prime manner on `M_σ`.
Witness: pick `1 ≠ a ∈ C_{M_α}(P)` (so `a ∈ M_σ`, `a` centralizes `P`); since
`C_{M_α}(PQ) = 1`, `a` does not centralize `Q`, so there is `y ∈ Q#` with `a ∉ C_G(y)`. Then for
`x ∈ P#`, `a ∈ C_{M_σ}(x)` but `a ∉ C_{M_σ}(y)`, so `C_{M_σ}(x) ≠ C_{M_σ}(y)` although both
`x, y ∈ (E₁E₃)#`. (`P` and `Q` need not commute — `P` acts regularly on `Q` — so the naive
`⟨xy⟩` argument is avoided.) -/
theorem not_actsPrime_Msigma_of_malpha_facts [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} [Fact p.Prime] {P : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1)
    (hPE1 : P ≤ E₁) {Q : Subgroup G} (hQE3 : Q ≤ E₃)
    (hCMαP : S10.Malpha M ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥)
    (hCMαPQ : S10.Malpha M ⊓ Subgroup.centralizer ((P ⊔ Q : Subgroup G) : Set G) = ⊥) :
    ¬ ActsPrimeOn (S10.Msigma M) (E₁ ⊔ E₃) := by
  classical
  intro hprime
  obtain ⟨⟨a, ha_mem⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCMαP
  have hane : a ≠ 1 := fun hc => ha1 (Subtype.ext (by simpa using hc))
  obtain ⟨haMα, haCP⟩ := Subgroup.mem_inf.mp ha_mem
  have haMσ : a ∈ S10.Msigma M := S10.Malpha_le_Msigma hG h.mem_maximal haMα
  -- `a ∉ C_G(Q)`, else `a ∈ M_α ⊓ C(PQ) = ⊥`.
  have haNCQ : a ∉ Subgroup.centralizer (Q : Set G) := by
    intro haCQ
    have hPle : (P : Subgroup G) ≤ Subgroup.centralizer ({a} : Set G) := by
      intro x hx; rw [Subgroup.mem_centralizer_iff]; intro u hu
      rw [Set.mem_singleton_iff.mp hu]
      exact (Subgroup.mem_centralizer_iff.mp haCP x hx).symm
    have hQle : (Q : Subgroup G) ≤ Subgroup.centralizer ({a} : Set G) := by
      intro x hx; rw [Subgroup.mem_centralizer_iff]; intro u hu
      rw [Set.mem_singleton_iff.mp hu]
      exact (Subgroup.mem_centralizer_iff.mp haCQ x hx).symm
    have haPQ : a ∈ Subgroup.centralizer ((P ⊔ Q : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]; intro g hg
      exact (Subgroup.mem_centralizer_iff.mp (sup_le hPle hQle hg) a (Set.mem_singleton a)).symm
    have hmem : a ∈ S10.Malpha M ⊓ Subgroup.centralizer ((P ⊔ Q : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨haMα, haPQ⟩
    rw [hCMαPQ, Subgroup.mem_bot] at hmem
    exact hane hmem
  -- `∃ y ∈ Q#` with `a ∉ C_G(y)`.
  rw [Subgroup.mem_centralizer_iff] at haNCQ
  push Not at haNCQ
  obtain ⟨y, hyQ, hyne⟩ := haNCQ
  have hy1 : y ≠ 1 := fun hc => hyne (by rw [hc, one_mul, mul_one])
  -- `x ∈ P#`.
  have hPcardp : Nat.card ↥P = p := by rw [← pow_one p]; exact hP.2
  have hPne : P ≠ ⊥ := by
    intro hb; rw [hb, Subgroup.card_bot] at hPcardp
    exact (Fact.out : p.Prime).one_lt.ne' hPcardp.symm
  obtain ⟨⟨x, hxP⟩, hxne1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  have hx1 : x ≠ 1 := fun hc => hxne1 (Subtype.ext (by simpa using hc))
  -- prime action: `C_{M_σ}(x) = C_{M_σ}(y)`.
  have hfx := hprime x ((le_sup_left : E₁ ≤ E₁ ⊔ E₃) (hPE1 hxP)) hx1
  have hfy := hprime y ((le_sup_right : E₃ ≤ E₁ ⊔ E₃) (hQE3 hyQ)) hy1
  have heq : fixedByElement (S10.Msigma M) x = fixedByElement (S10.Msigma M) y := hfx.trans hfy.symm
  -- `a ∈ C_{M_σ}(x)` but `a ∉ C_{M_σ}(y)`.
  have haX : a ∈ fixedByElement (S10.Msigma M) x := by
    rw [fixedByElement_def]
    refine Subgroup.mem_inf.mpr ⟨haMσ, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro u hu; rw [Set.mem_singleton_iff.mp hu]
    exact Subgroup.mem_centralizer_iff.mp haCP x hxP
  have haNY : a ∉ fixedByElement (S10.Msigma M) y := by
    rw [fixedByElement_def]; intro hmem
    obtain ⟨_, haCy⟩ := Subgroup.mem_inf.mp hmem
    exact hyne (Subgroup.mem_centralizer_iff.mp haCy y (Set.mem_singleton y))
  rw [heq] at haX
  exact haNY haX

/-- **BG Theorem 13.10, GAP C helper**: if `E₃` acts in a prime manner on `M_σ` (Cor 13.3(b)),
then `C_{M_σ}(E₃) = C_{M_σ}(Q)` for every nontrivial `Q ≤ E₃`. (`⊆`: pick `g ∈ Q#`; then
`C_{M_σ}(Q) ≤ C_{M_σ}(g) = C_{M_σ}(E₃)` by prime action. `⊇`: centralizer antitone.) -/
theorem centralizer_Msigma_eq_of_le_E3_of_actsPrime [Finite G]
    {M E₃ : Subgroup G} (hprime : ActsPrimeOn (S10.Msigma M) E₃)
    {Q : Subgroup G} (hQE3 : Q ≤ E₃) (hQne : Q ≠ ⊥) :
    S10.Msigma M ⊓ Subgroup.centralizer (E₃ : Set G) =
      S10.Msigma M ⊓ Subgroup.centralizer (Q : Set G) := by
  apply le_antisymm
  · exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hQE3))
  · obtain ⟨⟨g, hgQ⟩, hgne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQne
    have hg1 : g ≠ 1 := fun hc => hgne (Subtype.ext (by simpa using hc))
    have hpr := hprime g (hQE3 hgQ) hg1
    rw [fixedByElement_def, fixedBy_def] at hpr
    intro a ha
    obtain ⟨haMσ, haCQ⟩ := Subgroup.mem_inf.mp ha
    have haCg : a ∈ S10.Msigma M ⊓ Subgroup.centralizer ({g} : Set G) :=
      Subgroup.mem_inf.mpr ⟨haMσ,
        Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hgQ) haCQ⟩
    rw [hpr] at haCg
    exact haCg

/-- **BG Theorem 13.10, GAP C helper**: for the regular Sylow `Q` (`q ∈ τ₃(M)`, `Q ≤ E`,
`N_G(Q) ≤ M*`), `M_σ ∩ M* = C_{M_σ}(Q)`. (`⊇`: `C_{M_σ}(Q) ≤ N_G(Q) ≤ M*`. `⊆`: Cor 13.2(a)
shows `Q` centralizes `M_σ ∩ M*`, i.e. `M_σ ∩ M* ≤ C_G(Q)`.) -/
theorem inf_Msigma_Mstar_eq_centralizer_Q [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {q : ℕ} [Fact q.Prime] (hqτ3 : q ∈ tau3 M)
    {Q : Subgroup G} (hQE : Q ≤ E) (hQne : Q ≠ ⊥) (hQq : IsPGroup q ↥Q)
    {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (Q : Set G))) :
    S10.Msigma M ⊓ Mstar = S10.Msigma M ⊓ Subgroup.centralizer (Q : Set G) := by
  have hQM : Q ≤ M := hQE.trans h.E_le
  obtain ⟨hMstarCo, hNQM⟩ := mem_maximalSubgroupsContaining.mp hMstar
  have hcor : Q ≤ Subgroup.centralizer ((S10.Msigma M ⊓ Mstar : Subgroup G) : Set G) :=
    (tau13_pSubgroup_centralizes hG h (Set.mem_union_right _ hqτ3) hQM hQne hQq hMstar).1 Q
      (le_inf hQM (Subgroup.le_normalizer.trans hNQM)) hQq
  apply le_antisymm
  · exact le_inf inf_le_left (Subgroup.le_centralizer_iff.mp hcor)
  · exact le_inf inf_le_left
      (inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans hNQM))

/-- **BG Theorem 13.10, GAP C helper**: an `E`-invariant Sylow `q`-subgroup `Q*` of `M_σ ∩ M*`
(for any `M*` with `E ≤ M*`). `E` normalizes `M_σ` and `M*`, hence `M_σ ∩ M*`; `|E|` is coprime to
`|M_σ ∩ M*|` (it divides `|M_σ|`, coprime to `|E|`), so `exists_aInvariant_sylow_subgroup`
applies. Mirrors `exists_E1inv_sylow_centralizing_derivedE`. -/
theorem exists_Einvariant_sylow_inf_Msigma_Mstar [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {Mstar : Subgroup G} (hEMstar : E ≤ Mstar) (q : ℕ) [Fact q.Prime] :
    ∃ Qstar : Subgroup G, Qstar ≤ S10.Msigma M ⊓ Mstar ∧ IsPGroup q ↥Qstar ∧
      E ≤ Subgroup.normalizer (Qstar : Set G) ∧
      Nat.card ↥Qstar = q ^ (Nat.card ↥(S10.Msigma M ⊓ Mstar)).factorization q := by
  classical
  set N : Subgroup G := S10.Msigma M ⊓ Mstar with hNdef
  have hNMσ : N ≤ S10.Msigma M := inf_le_left
  have hMσM : S10.Msigma M ≤ M := S10.Msigma_le M
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups h.mem_maximal
  have hNsolv : Group.IsSolvable ↥N :=
    Group.isSolvable_of_surjective (f :=
      (Subgroup.subgroupOfEquivOfLe (hNMσ.trans hMσM)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (hNMσ.trans hMσM)).surjective
  have hENMσ : E ≤ Subgroup.normalizer ((S10.Msigma M : Subgroup G) : Set G) :=
    h.E_le.trans (le_normalizer_opiCoreInG (S10.sigma M) M)
  have hENMstar : E ≤ Subgroup.normalizer (Mstar : Set G) := hEMstar.trans Subgroup.le_normalizer
  have hENN : E ≤ Subgroup.normalizer (N : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]; intro x; rw [hNdef]
    simp only [Subgroup.mem_inf]
    rw [Subgroup.mem_normalizer_iff.mp (hENMσ hg) x, Subgroup.mem_normalizer_iff.mp (hENMstar hg) x]
  have hcop_MσE : Nat.Coprime (Nat.card ↥(S10.Msigma M)) (Nat.card ↥E) := by
    have h1 := (S10.Msigma_subgroupOf_isHall hG h.mem_maximal).coprime_index
    rw [h.isComplement'_subgroupOf.symm.index_eq_card] at h1
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E_le).toEquiv] at h1
  have hcop : Nat.Coprime (Nat.card ↥E) (Nat.card ↥N) :=
    hcop_MσE.symm.coprime_dvd_right (Subgroup.card_dvd_of_le hNMσ)
  exact exists_aInvariant_sylow_subgroup hENN hcop (Or.inr hNsolv) q

/-- **BG Theorem 13.10, GAP C helper**: a Sylow `q`-subgroup `Q*` of `M_σ ∩ M*` (`q ∈ σ(M)`) is a
maximal `q`-subgroup of `M ∩ M*`. (Any `q`-subgroup `T ≤ M ∩ M*` is a `σ(M)`-subgroup of `M`,
hence `≤ M_σ` since `M_σ` is a normal Hall `σ`-subgroup, so `T ≤ M_σ ∩ M*`, where `Q*` is already
Sylow.) -/
theorem sylow_Msigma_Mstar_maximal_in_inf [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {Mstar : Subgroup G} {q : ℕ} [Fact q.Prime] (hqσ : q ∈ S10.sigma M)
    {Qstar : Subgroup G}
    (hQstarcard : Nat.card ↥Qstar = q ^ (Nat.card ↥(S10.Msigma M ⊓ Mstar)).factorization q) :
    ∀ T : Subgroup G, T ≤ M ⊓ Mstar → IsPGroup q ↥T → Qstar ≤ T → Qstar = T := by
  intro T hTMM hTq hQT
  have hTpi : Subgroup.IsPiSubgroup (S10.sigma M) T := by
    intro r hr
    obtain ⟨hrp, hrdvd, _⟩ := Nat.mem_primeFactors.mp hr
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hTq
    have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hrp Fact.out).mp
      (hrp.dvd_of_dvd_pow (hk ▸ hrdvd))
    rw [hrq]; exact hqσ
  have hTMσ : T ≤ S10.Msigma M := S10.sigma_subgroup_le_Msigma_of_isHall
    (S10.isHall_Msigma_Malpha hG h.mem_maximal).1 (hTMM.trans inf_le_left) hTpi
  exact eq_of_le_of_isPGroup_card_eq_factorization hQstarcard
    (le_inf hTMσ (hTMM.trans inf_le_right)) hTq hQT

/-- **BG Theorem 13.10, displayed eq (13.5)**: if `P, Q ≤ E` with `P` acting regularly on `Q`
(`Q ⊓ C_G(P) = ⊥`, coprime, `P ≤ N_G(Q)`, `P` solvable), then `Q = [Q,P] ⊆ E'`. Coprime action
gives `Q ≤ ⁅P,Q⁆` (`le_commutator_of_coprime_inf_centralizer_eq_bot`), and `⁅P,Q⁆ ≤ ⁅E,E⁆ =
derivedInG E` by monotonicity. -/
theorem le_derivedInG_E_of_inf_centralizer_eq_bot [Finite G] {E P Q : Subgroup G}
    (hPE : P ≤ E) (hQE : Q ≤ E) [Group.IsSolvable ↥P]
    (hPN : P ≤ Subgroup.normalizer (Q : Set G)) (hcop : Nat.Coprime (Nat.card ↥P) (Nat.card ↥Q))
    (hCQ : Q ⊓ Subgroup.centralizer (P : Set G) = ⊥) :
    Q ≤ derivedInG E := by
  have hQPQ : Q ≤ ⁅P, Q⁆ :=
    Ch2.S08.le_commutator_of_coprime_inf_centralizer_eq_bot hPN hcop hCQ
  have hde : derivedInG E = ⁅E, E⁆ := Subgroup.map_subtype_commutator E
  rw [hde]
  exact hQPQ.trans (Subgroup.commutator_mono hPE hQE)

/-- **BG Theorem 13.10, GAP C key step** (Lemma 12.19): for `Q ≤ E'` and a prime `q ∉ β(M)`, the
`q`-part of `C_{M_σ}(Q) = M_σ ⊓ C_G(Q)` is full, i.e. equals the `q`-part of `M_σ`. By Lemma 12.19
`E'` centralizes a Hall `β(M)'`-subgroup `W ≤ M_σ`; since `Q ≤ E'`, `W ≤ C_G(Q)`, so
`W ≤ M_σ ⊓ C_G(Q)`. As `q ∉ β`, `W` has full `q`-part (`v_q(W) = v_q(M_σ)`), and squeezing
`W ≤ M_σ ⊓ C_G(Q) ≤ M_σ` forces equality. -/
theorem factorization_inf_centralizer_Q_eq_of_not_beta [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {Q : Subgroup G} (hQderived : Q ≤ derivedInG E) {q : ℕ} [Fact q.Prime] (hqβ : q ∉ S10.beta M) :
    (Nat.card ↥(S10.Msigma M ⊓ Subgroup.centralizer (Q : Set G))).factorization q
      = (Nat.card ↥(S10.Msigma M)).factorization q := by
  obtain ⟨W, hWMσ, hWhall, hE'CW⟩ := derivedE_centralizes_betaComplement hG h
  have hWN : W ≤ S10.Msigma M ⊓ Subgroup.centralizer (Q : Set G) :=
    le_inf hWMσ (Subgroup.le_centralizer_iff.mp (hQderived.trans hE'CW))
  have hidxne : (W.subgroupOf (S10.Msigma M)).index ≠ 0 := by
    have hc := Subgroup.card_mul_index (W.subgroupOf (S10.Msigma M))
    intro h0; rw [h0, mul_zero] at hc; exact Nat.card_pos.ne' hc.symm
  have hidx0 : ((W.subgroupOf (S10.Msigma M)).index).factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun hd =>
      hWhall.2 q (Nat.mem_primeFactors.mpr ⟨Fact.out, hd, hidxne⟩) hqβ)
  have hcardW : Nat.card ↥(W.subgroupOf (S10.Msigma M)) = Nat.card ↥W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWMσ).toEquiv
  have hvW : (Nat.card ↥W).factorization q = (Nat.card ↥(S10.Msigma M)).factorization q := by
    have hmul := Subgroup.card_mul_index (W.subgroupOf (S10.Msigma M))
    rw [hcardW] at hmul
    rw [← hmul, Nat.factorization_mul Nat.card_pos.ne' hidxne, Finsupp.add_apply, hidx0, add_zero]
  have hle1 : (Nat.card ↥W).factorization q ≤
      (Nat.card ↥(S10.Msigma M ⊓ Subgroup.centralizer (Q : Set G))).factorization q :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
      (Subgroup.card_dvd_of_le hWN) q
  have hle2 : (Nat.card ↥(S10.Msigma M ⊓ Subgroup.centralizer (Q : Set G))).factorization q ≤
      (Nat.card ↥(S10.Msigma M)).factorization q :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
      (Subgroup.card_dvd_of_le inf_le_left) q
  omega

/-- **BG Theorem 13.10, GAP C step 6** (`C_{Q*}(P) = 1`): the regular-action Sylow `Q*` of
`M_σ ∩ M*` satisfies `Q* ⊓ C_G(P) = ⊥`. Dichotomy on `q* ∈ β(M)`: if `q* ∉ β`, `Q*` is a full
Sylow `q*`-subgroup of `M_σ` (by `factorization_inf_centralizer_Q_eq_of_not_beta` and the C2
equality `M_σ ∩ M* = C_{M_σ}(Q)`), so Lemma 13.6 applies (`centralizer_sylow_inf_eq_bot`); if
`q* ∈ β ⊆ α`, then `Q* ≤ M_α` (`M_α` Hall `α`) and `Q* ≤ C_G(Q)`, so `C_{Q*}(P) ≤ C_{M_α}(PQ) =
1`. -/
theorem centralizer_Qstar_P_eq_bot [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {P : Subgroup G} (hPE1 : P ≤ E₁) (hPne : P ≠ ⊥)
    {Q : Subgroup G} (hQderived : Q ≤ derivedInG E)
    (hCMαPQ : S10.Malpha M ⊓ Subgroup.centralizer ((P ⊔ Q : Subgroup G) : Set G) = ⊥)
    {Mstar : Subgroup G} (hMstarMax : Mstar ∈ maximalSubgroups G) (hMMstar : M ≠ Mstar)
    (hMσMstar_eq : S10.Msigma M ⊓ Mstar = S10.Msigma M ⊓ Subgroup.centralizer (Q : Set G))
    {qs : ℕ} [Fact qs.Prime] (hqsσ : qs ∈ S10.sigma M)
    {Qstar : Subgroup G} (hQstarMσMstar : Qstar ≤ S10.Msigma M ⊓ Mstar)
    (hQstarcard : Nat.card ↥Qstar = qs ^ (Nat.card ↥(S10.Msigma M ⊓ Mstar)).factorization qs) :
    Qstar ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
  have hQstarMσ : Qstar ≤ S10.Msigma M := hQstarMσMstar.trans inf_le_left
  by_cases hqsβ : qs ∈ S10.beta M
  · -- `q* ∈ β`: `Q* ≤ M_α` and `Q* ≤ C_G(Q)`, so `C_{Q*}(P) ≤ C_{M_α}(PQ) = ⊥`.
    have hQstarpiα : Subgroup.IsPiSubgroup (S10.alpha M) Qstar := by
      intro r hr
      obtain ⟨hrp, hrdvd, _⟩ := Nat.mem_primeFactors.mp hr
      have hrqs : r = qs := (Nat.prime_dvd_prime_iff_eq hrp Fact.out).mp
        (hrp.dvd_of_dvd_pow (hQstarcard ▸ hrdvd))
      rw [hrqs]; exact S10.beta_subset_alpha M hqsβ
    have hQstarMα : Qstar ≤ S10.Malpha M :=
      S10.piSubgroup_le_opiCoreInG_of_isHall (S10.isHall_Msigma_Malpha hG h.mem_maximal).2.1
        (hQstarMσ.trans (S10.Msigma_le M)) hQstarpiα
    have hQstarCQ : Qstar ≤ Subgroup.centralizer (Q : Set G) :=
      le_trans (hMσMstar_eq ▸ hQstarMσMstar) inf_le_right
    rw [← le_bot_iff, ← hCMαPQ]
    intro a ha
    obtain ⟨haQstar, haCP⟩ := Subgroup.mem_inf.mp ha
    refine Subgroup.mem_inf.mpr ⟨hQstarMα haQstar, ?_⟩
    have hPle : (P : Subgroup G) ≤ Subgroup.centralizer ({a} : Set G) := by
      intro x hx; rw [Subgroup.mem_centralizer_iff]; intro u hu
      rw [Set.mem_singleton_iff.mp hu]
      exact (Subgroup.mem_centralizer_iff.mp haCP x hx).symm
    have hQle : (Q : Subgroup G) ≤ Subgroup.centralizer ({a} : Set G) := by
      intro x hx; rw [Subgroup.mem_centralizer_iff]; intro u hu
      rw [Set.mem_singleton_iff.mp hu]
      exact (Subgroup.mem_centralizer_iff.mp (hQstarCQ haQstar) x hx).symm
    rw [Subgroup.mem_centralizer_iff]; intro g hg
    exact (Subgroup.mem_centralizer_iff.mp (sup_le hPle hQle hg) a (Set.mem_singleton a)).symm
  · -- `q* ∉ β`: `Q*` is a full Sylow `q*`-subgroup of `M_σ`, so Lemma 13.6 applies.
    have hcardMσ : Nat.card ↥Qstar = qs ^ (Nat.card ↥(S10.Msigma M)).factorization qs := by
      rw [hQstarcard, hMσMstar_eq, factorization_inf_centralizer_Q_eq_of_not_beta hG h hQderived
          hqsβ]
    have hQstarmaxMσ : ∀ T : Subgroup G, T ≤ S10.Msigma M → IsPGroup qs ↥T → Qstar ≤ T → Qstar =
        T :=
      fun T hT hTq hQT => eq_of_le_of_isPGroup_card_eq_factorization hcardMσ hT hTq hQT
    exact centralizer_sylow_inf_eq_bot hG h hqsσ hPE1 hPne hQstarMσ
      (IsPGroup.iff_card.mpr ⟨_, hcardMσ⟩) hQstarmaxMσ hMstarMax hMMstar.symm
      (hQstarMσMstar.trans inf_le_right)

/-- **BG Theorem 13.10, GAP C step 5** (`N_G(Q*) ⊆ M`): for the regular-action Sylow `Q*` of
`M_σ ∩ M*`, `N_G(Q*) ⊆ M`. If `q* ∈ β(M)`, `Q*` is a nontrivial `β`-subgroup, so Prop 10.14(d).
If `q* ∉ β`, `Q*` is a full Sylow `q*`-subgroup of `M_σ` (same factorization argument as step 6),
so `normalizer_einvariant_sylow_le` (via the definition of `σ(M)`). -/
theorem normalizer_Qstar_le_M [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {Q : Subgroup G} (hQderived : Q ≤ derivedInG E)
    {Mstar : Subgroup G}
    (hMσMstar_eq : S10.Msigma M ⊓ Mstar = S10.Msigma M ⊓ Subgroup.centralizer (Q : Set G))
    {qs : ℕ} [Fact qs.Prime] (hqsσ : qs ∈ S10.sigma M)
    {Qstar : Subgroup G} (hQstarMσMstar : Qstar ≤ S10.Msigma M ⊓ Mstar) (hQstarne : Qstar ≠ ⊥)
    (hQstarcard : Nat.card ↥Qstar = qs ^ (Nat.card ↥(S10.Msigma M ⊓ Mstar)).factorization qs) :
    Subgroup.normalizer (Qstar : Set G) ≤ M := by
  have hQstarMσ : Qstar ≤ S10.Msigma M := hQstarMσMstar.trans inf_le_left
  by_cases hqsβ : qs ∈ S10.beta M
  · have hQstarpiβ : Subgroup.IsPiSubgroup (S10.beta M) Qstar := by
      intro r hr
      obtain ⟨hrp, hrdvd, _⟩ := Nat.mem_primeFactors.mp hr
      have hrqs : r = qs := (Nat.prime_dvd_prime_iff_eq hrp Fact.out).mp
        (hrp.dvd_of_dvd_pow (hQstarcard ▸ hrdvd))
      rw [hrqs]; exact hqsβ
    exact S10.normalizer_le_of_nontrivial_beta_subgroup hG h.mem_maximal
      (hQstarMσ.trans (S10.Msigma_le M)) hQstarne hQstarpiβ
  · have hcardMσ : Nat.card ↥Qstar = qs ^ (Nat.card ↥(S10.Msigma M)).factorization qs := by
      rw [hQstarcard, hMσMstar_eq, factorization_inf_centralizer_Q_eq_of_not_beta hG h hQderived
          hqsβ]
    exact normalizer_einvariant_sylow_le hG h.mem_maximal hqsσ hQstarMσ hcardMσ

/-- **BG Theorem 13.10** (mmd L3672; 結論は PDF p.102 から画像読みで復元):
ある `P∈ℰ_p¹(E₁)` が `E₃` を中心化しないなら (a) `E₁` は `E₃` に regular 作用;
(b) `E₃` は `M_σ` に regular 作用; (c) その `P` について `C_{M_σ}(P) ≠ 1`。

§10 gates visible for proof-fill: `S10.normalizer_le_of_nontrivial_beta_subgroup`
(Prop 10.14(d)) supplies `N_G(Q*)⊆M` in the `q*∈β(M)` branch; the remaining branch uses
`σ(M)` by definition. Lemma 12.18 / Lemma 12.19 carry the Cor 10.9 β-complement input.

`p` is required prime (`ℰ_p¹` is BG's rank-1 *elementary abelian* family with `p` prime; the
Lean `elemAbelianOfRank` predicate alone does not force it, e.g. `ℤ/p²`). -/
theorem E1_regular_on_E3_of_noncentralize [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    (hP : ∃ p : ℕ, p.Prime ∧ ∃ P : Subgroup G, P ∈ elemAbelianOfRank G p 1 ∧ P ≤ E₁ ∧
      ¬ (P ≤ Subgroup.centralizer (E₃ : Set G))) :
    ActsRegularlyOn E₃ E₁ ∧ ActsRegularlyOn (S10.Msigma M) E₃ ∧
    (∀ p : ℕ, p.Prime → ∀ P : Subgroup G, P ∈ elemAbelianOfRank G p 1 → P ≤ E₁ →
      ¬ (P ≤ Subgroup.centralizer (E₃ : Set G)) →
      S10.Msigma M ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥) := by
  classical
  obtain ⟨p, hpprime, P, hPmem, hPE1, hPnc⟩ := hP
  have : Fact p.Prime := ⟨hpprime⟩
  refine ⟨?_, ?_, ?_⟩
  · -- (a) `E₁` acts regularly on `E₃`: `E₁E₃` not prime on `M_σ` (GAP B) ⟹ Lemma 13.7
    -- contrapositive.
    obtain ⟨Q, hQE3, hQne, hCMαP, hCMαPQ⟩ :=
      malpha_centralizer_facts_of_not_centralize hG h hPmem hPE1 hPnc
    have hnotprime := not_actsPrime_Msigma_of_malpha_facts hG h hPmem hPE1 hQE3 hCMαP hCMαPQ
    have hE1ne : E₁ ≠ ⊥ := fun hb =>
      ne_bot_of_mem_elemAbelianOfRank_one hPmem (le_bot_iff.mp (hb ▸ hPE1))
    exact not_not.mp (mt (E1E3_actsPrime hG h hE1ne) hnotprime)
  · -- (b) `E₃` acts regularly on `M_σ` (GAP C — Lemma 13.8 endgame).
    by_contra hreg
    have hE3prime : ActsPrimeOn (S10.Msigma M) E₃ := (cyclicSylow_actsPrime hG h).2
    obtain ⟨q, hqprime, hqτ3, hpq, Q, hQq, hQE3, hQne, hCQ, hPNQ, hQsyl⟩ :=
      exists_tau3_sylowM_regular_of_not_centralize hG h hPmem hPE1 hPnc
    have : Fact q.Prime := ⟨hqprime⟩
    obtain ⟨Mstar, hMstarMax, hNQM, hnc⟩ :=
      exists_maximal_over_normalizer_not_conj_of_le_E3 hG h hqτ3 hQE3 hQne hQq
    have hMMstar : M ≠ Mstar := fun heq => hnc ⟨1, by rw [heq, map_one, one_smul]⟩
    have hMstar_mem : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) :=
      mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hMstarMax, hNQM⟩
    have hQE : Q ≤ E := hQE3.trans h.E₃_le
    have hQM : Q ≤ M := hQE.trans h.E_le
    have hPM : P ≤ M := hPE1.trans (h.E₁_le.trans h.E_le)
    have hEMstar : E ≤ Mstar := (E_le_normalizer_of_le_E3 hG h hQE3).trans hNQM
    have hPcardp : Nat.card ↥P = p := by rw [← pow_one p]; exact (mem_elemAbelianOfRank.mp hPmem).2
    have hc1 : Nat.card ↥(E₁.subgroupOf E) = Nat.card ↥E₁ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv
    have hpτ1 : p ∈ tau1 M :=
      h.E₁_hall.1 p (hc1 ▸ Nat.mem_primeFactors.mpr
        ⟨hpprime, hPcardp ▸ Subgroup.card_dvd_of_le hPE1, Nat.card_pos.ne'⟩)
    have hMNQ : maximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) ≠ {M} := by
      intro hsingle; rw [hsingle, Set.mem_singleton_iff] at hMstar_mem
      exact hMMstar hMstar_mem.symm
    obtain ⟨_, _, _, hCMαP, hCMαPQ⟩ :=
      (tau1_Malpha_interaction hG h.mem_maximal hpq hpτ1 hPmem hPM hQM hQne hQq hPNQ hCQ hMNQ).2
          hQsyl
    have hPsolv : Group.IsSolvable ↥P :=
      Group.isSolvable_of_comm (mem_elemAbelianOfRank.mp hPmem).1.1
    obtain ⟨kq, hQk⟩ := IsPGroup.iff_card.mp hQq
    have hcopPQ : Nat.Coprime (Nat.card ↥P) (Nat.card ↥Q) := by
      rw [hPcardp, hQk]; exact ((Nat.coprime_primes hpprime hqprime).mpr hpq.symm).pow_right kq
    have hQderived : Q ≤ derivedInG E :=
      le_derivedInG_E_of_inf_centralizer_eq_bot (hPE1.trans h.E₁_le) hQE hPNQ hcopPQ hCQ
    have hMσMstar_eq : S10.Msigma M ⊓ Mstar = S10.Msigma M ⊓ Subgroup.centralizer (Q : Set G) :=
      inf_Msigma_Mstar_eq_centralizer_Q hG h hqτ3 hQE hQne hQq hMstar_mem
    rw [ActsRegularlyOn] at hreg; push Not at hreg
    obtain ⟨g, hgE3, hg1, hfix⟩ := hreg
    have hCE3 : S10.Msigma M ⊓ Subgroup.centralizer (E₃ : Set G) ≠ ⊥ := by
      have hpr := hE3prime g hgE3 hg1
      rw [fixedByElement_def, fixedBy_def] at hpr
      rw [← hpr]; exact hfix
    have hMσMstarne : S10.Msigma M ⊓ Mstar ≠ ⊥ := by
      rw [hMσMstar_eq, ← centralizer_Msigma_eq_of_le_E3_of_actsPrime hE3prime hQE3 hQne]
      exact hCE3
    have hcardne1 : Nat.card ↥(S10.Msigma M ⊓ Mstar) ≠ 1 := by
      rw [Ne, Subgroup.card_eq_one]; exact hMσMstarne
    obtain ⟨qs, hqsprime, hqsdvd⟩ :=
      (Nat.card ↥(S10.Msigma M ⊓ Mstar)).exists_prime_and_dvd hcardne1
    have : Fact qs.Prime := ⟨hqsprime⟩
    have hqsσ : qs ∈ S10.sigma M :=
      isPiSubgroup_opiCoreInG (S10.sigma M) M qs (Nat.mem_primeFactors.mpr
        ⟨hqsprime, hqsdvd.trans (Subgroup.card_dvd_of_le inf_le_left), Nat.card_pos.ne'⟩)
    obtain ⟨Qstar, hQstarMσMstar, hQstarq, hQstarinv, hQstarcard⟩ :=
      exists_Einvariant_sylow_inf_Msigma_Mstar hG h hEMstar qs
    have hQstarne : Qstar ≠ ⊥ := by
      intro hb; rw [hb, Subgroup.card_bot] at hQstarcard
      have hv : (Nat.card ↥(S10.Msigma M ⊓ Mstar)).factorization qs ≠ 0 :=
        (Nat.Prime.factorization_pos_of_dvd hqsprime Nat.card_pos.ne' hqsdvd).ne'
      rcases Nat.pow_eq_one.mp hQstarcard.symm with h1 | h0
      · exact hqsprime.ne_one h1
      · exact hv h0
    have hNQstar : Subgroup.normalizer (Qstar : Set G) ≤ M :=
      normalizer_Qstar_le_M hG h hQderived hMσMstar_eq hqsσ hQstarMσMstar hQstarne hQstarcard
    have hCQstar : Qstar ⊓ Subgroup.centralizer (P : Set G) = ⊥ :=
      centralizer_Qstar_P_eq_bot hG h hPE1 (ne_bot_of_mem_elemAbelianOfRank_one hPmem) hQderived
        hCMαPQ hMstarMax hMMstar hMσMstar_eq hqsσ hQstarMσMstar hQstarcard
    have hpE : p ∈ (Nat.card ↥E).primeFactors :=
      Nat.mem_primeFactors.mpr
        ⟨hpprime, hPcardp ▸ Subgroup.card_dvd_of_le (hPE1.trans h.E₁_le), Nat.card_pos.ne'⟩
    have hPMstar : P ≤ Mstar := hPE1.trans (h.E₁_le.trans hEMstar)
    have hpMstar : p ∈ (Nat.card ↥Mstar).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpprime, hPcardp ▸ Subgroup.card_dvd_of_le hPMstar,
          Nat.card_pos.ne'⟩
    have hPMM : P ≤ M ⊓ Mstar := le_inf hPM hPMstar
    have hpτ1star : p ∈ tau1 Mstar :=
      mem_tau1_Mstar_of_einvariant_sylow hG h hMstarMax hnc hpE hpMstar hPMM
        (mem_elemAbelianOfRank.mp hPmem).1.isPGroup (hQstarMσMstar.trans inf_le_left)
        (hQstarMσMstar.trans inf_le_right) hQstarne hCQstar
    exact forbidden_config_impossible hG h.mem_maximal hMstarMax hnc hpτ1 hpτ1star hPmem hPMM
      (le_inf hQM (Subgroup.le_normalizer.trans hNQM)) hQq
      (fun T hT hTq hQT => hQsyl T (hT.trans inf_le_left) hTq hQT)
      (le_inf ((hQstarMσMstar.trans inf_le_left).trans (S10.Msigma_le M))
        (hQstarMσMstar.trans inf_le_right)) hQstarq
      (sylow_Msigma_Mstar_maximal_in_inf hG h hqsσ hQstarcard)
      hPNQ ((hPE1.trans h.E₁_le).trans hQstarinv) hCQ hCQstar hNQM hNQstar
  · -- (c) `C_{M_σ}(P) ≠ 1` for every such `P`: from `C_{M_α}(P) ≠ 1` and `M_α ≤ M_σ`.
    intro p' hp'prime P' hP'mem hP'E1 hP'nc
    have : Fact p'.Prime := ⟨hp'prime⟩
    obtain ⟨_, _, _, hCMαP', _⟩ :=
      malpha_centralizer_facts_of_not_centralize hG h hP'mem hP'E1 hP'nc
    intro hbot
    exact hCMαP' (le_bot_iff.mp (hbot ▸
      inf_le_inf_right (Subgroup.centralizer (P' : Set G)) (S10.Malpha_le_Msigma hG h.mem_maximal)))

end OddOrder.BG.Ch3.S13


