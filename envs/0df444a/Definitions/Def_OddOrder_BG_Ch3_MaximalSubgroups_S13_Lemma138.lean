-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S13_Lemma138
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S13_Lemma138
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T08:55:49.125685+00:00
-- url     : https://prove2.me/theorems/106a1e12-363d-4722-bb2d-4e9738c71082
-- title:
--   BG §13: Lemma 13.8 (the forbidden configuration is impossible)
-- statement:
--   Formalizes Lemma 13.8 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §13 (`forbidden_config_impossible`): a symmetric configuration with $M^*\in\mathcal{M}$ nonconjugate to $M$ and a maximal $q$-subgroup and $q^*$-subgroup cannot occur. It depends on the Uniqueness Theorem, Theorems 10.1(b)/10.2, Lemma 12.18, Proposition 10.14(d) and Theorem 13.4.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 33 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S13_Lemma138.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S13_Lemma138.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S13_Lemma137

namespace OddOrder.BG.Ch3.S13

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

/-- **有限 `q`-群の normalizer-growth**: `T` が有限 `q`-群で `Q < T` なら、`Q` はその
`T` 内 normalizer `T ⊓ N_G(Q)` に真に含まれる。冪零群の normalizer condition の帰結
(`Group.normalizerCondition_of_isNilpotent`)。

Lemma 13.8 GAP 1.3 の核 — 「`M ∩ M*` の極大 `q`-部分群 `Q` で `N_G(Q) ⊆ M*` なら `Q` は
`M` の極大 `q`-部分群」を示すのに使う: `Q < T ≤ M` を仮定すると `T ⊓ N_G(Q) ⊆ M ⊓ M*` の
`q`-部分群が `Q` を真に含み、極大性に反する。 -/
theorem lt_inf_normalizer_of_lt_of_pgroup [Finite G] {q : ℕ} [Fact q.Prime]
    {Q T : Subgroup G} (hTq : IsPGroup q ↥T) (hQT : Q < T) :
    Q < T ⊓ Subgroup.normalizer (Q : Set G) := by
  have hQTle : Q ≤ T := hQT.le
  have hne_top : Q.subgroupOf T ≠ ⊤ := fun htop =>
    hQT.ne (le_antisymm hQTle (Subgroup.subgroupOf_eq_top.mp htop))
  have : Group.IsNilpotent ↥T := IsPGroup.isNilpotent hTq
  have hNC : NormalizerCondition ↥T := Group.normalizerCondition_of_isNilpotent
  have hgrow := hNC (Q.subgroupOf T) (lt_top_iff_ne_top.mpr hne_top)
  rw [← Subgroup.subgroupOf_normalizer_eq hQTle] at hgrow
  refine lt_of_le_of_ne (le_inf hQTle Subgroup.le_normalizer) (fun heq => hgrow.ne ?_)
  conv_lhs => rw [heq]
  rw [Subgroup.inf_subgroupOf_left]

/-- **Lemma 13.8 GAP 1** (`M`-side engine): 13.8 の配置 (片側) から Lemma 12.18(b) の出力を導く。
`M ∩ M*` の極大 `q`-部分群 `Q` (`P`-不変, `C_Q(P)=1`, `N_G(Q) ⊆ M*`, `M ≠ M*`) について:

* `q ≠ p` (GAP 1.2 — `q=p` なら `P ≤ P⊔Q = Q`, `P ≤ C_Q(P)=1` で矛盾),
* `Q ≠ 1` (GAP 1.1 — `Q=1` なら `N_G(Q)=G ⊆ M*` で `M*` が極大に反する),
* `Q` は `M` の極大 `q`-部分群 (GAP 1.3 — `lt_inf_normalizer_of_lt_of_pgroup` + `N_G(Q) ⊆ M*`),
* `ℳ(N_G(Q)) ≠ {M}` (`M* ∈ ℳ(N_G(Q))`, `M* ≠ M`)

を経由して Lemma 12.18(b) (`tau1_Malpha_interaction`) を適用し
`α(M)=β(M) ∧ M_α≠1 ∧ q∉α(M) ∧ C_{M_α}(P)≠1 ∧ C_{M_α}(PQ)=1` を得る。
`M*`-side は `M ↔ M*`, `Q ↔ Q*` を入れ替えて同じ補題を再適用する。 -/
theorem forbidden_config_step1 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hMstar : Mstar ∈ maximalSubgroups G)
    (hMMstar : M ≠ Mstar) {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : p ∈ tau1 M)
    {P : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1) (hPMM : P ≤ M ⊓ Mstar)
    {Q : Subgroup G} (hQle : Q ≤ M ⊓ Mstar) (hQq : IsPGroup q ↥Q)
    (hQmax : ∀ T : Subgroup G, T ≤ M ⊓ Mstar → IsPGroup q ↥T → Q ≤ T → Q = T)
    (hQinv : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : Q ⊓ Subgroup.centralizer (P : Set G) = ⊥)
    (hNQ : Subgroup.normalizer (Q : Set G) ≤ Mstar) :
    q ≠ p ∧ Q ≠ ⊥ ∧
    S10.alpha M = S10.beta M ∧ S10.Malpha M ≠ ⊥ ∧ q ∉ S10.alpha M ∧
    S10.Malpha M ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ ∧
    S10.Malpha M ⊓ Subgroup.centralizer ((P ⊔ Q : Subgroup G) : Set G) = ⊥ := by
  obtain ⟨hPea, hPcard1⟩ := mem_elemAbelianOfRank.mp hP
  have hPp : IsPGroup p ↥P := hPea.isPGroup
  have hPcard : Nat.card ↥P = p := by rw [hPcard1, pow_one]
  have hPM : P ≤ M := hPMM.trans inf_le_left
  have hQM : Q ≤ M := hQle.trans inf_le_left
  -- GAP 1.1: `Q ≠ 1`.
  have hQne : Q ≠ ⊥ := by
    rintro rfl
    have htop : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr inferInstance
    rw [htop, top_le_iff] at hNQ
    exact (mem_maximalSubgroups.mp hMstar).1 hNQ
  -- GAP 1.2: `q ≠ p`.
  have hP_le_cP : P ≤ Subgroup.centralizer (P : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr ⟨⟨hPea.comm⟩⟩
  have hqp : q ≠ p := by
    rintro rfl
    have hPQp : IsPGroup q ↥(P ⊔ Q : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' hPp hQq hQinv
    have hQeq : Q = (P ⊔ Q : Subgroup G) := hQmax _ (sup_le hPMM hQle) hPQp le_sup_right
    have hP_le_Q : P ≤ Q := le_sup_left.trans hQeq.ge
    have hP_bot : P ≤ ⊥ := hCQ ▸ le_inf hP_le_Q hP_le_cP
    rw [le_bot_iff] at hP_bot
    rw [hP_bot, Subgroup.card_bot] at hPcard
    exact (Fact.out : Nat.Prime q).one_lt.ne hPcard
  -- GAP 1.3: `Q` is a maximal `q`-subgroup of `M`.
  have hQsyl : ∀ T : Subgroup G, T ≤ M → IsPGroup q ↥T → Q ≤ T → Q = T := by
    intro T hTM hTq hQT
    by_contra hne
    have hlt : Q < T := lt_of_le_of_ne hQT hne
    have hgrow := lt_inf_normalizer_of_lt_of_pgroup hTq hlt
    have hNT_le : T ⊓ Subgroup.normalizer (Q : Set G) ≤ M ⊓ Mstar :=
      le_inf (inf_le_left.trans hTM) (inf_le_right.trans hNQ)
    have hNT_q : IsPGroup q ↥(T ⊓ Subgroup.normalizer (Q : Set G)) := hTq.to_le inf_le_left
    exact hgrow.ne (hQmax _ hNT_le hNT_q hgrow.le)
  -- `ℳ(N_G(Q)) ≠ {M}` (since `M* ∈ ℳ(N_G(Q))` and `M* ≠ M`).
  have hMNQ : maximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) ≠ {M} := by
    intro hsingle
    have hMstar_mem : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) :=
      mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hMstar, hNQ⟩
    rw [hsingle, Set.mem_singleton_iff] at hMstar_mem
    exact hMMstar hMstar_mem.symm
  -- apply Lemma 12.18(b).
  obtain ⟨hαβ, hMαne, hqα, hCMαP, hCMαPQ⟩ :=
    (tau1_Malpha_interaction hG hM hqp hp hP hPM hQM hQne hQq hQinv hCQ hMNQ).2 hQsyl
  exact ⟨hqp, hQne, hαβ, hMαne, hqα, hCMαP, hCMαPQ⟩

/-- **Theorem 10.1(b) collapse** (Lemma 13.8 GAP 2.8 の核): `t ∈ σ(M)`, `Y` を `M` の非自明
`t`-部分群で `N_G(Y) ⊆ M` とすると、`Y` を含む任意の極大共役 `M^g` は `M` に等しい。

`C_G(Y)` が `{M^u ∣ Y ≤ M^u}` に推移作用する (Theorem 10.1(b) =
`S10.fusion_control_of_mem_sigma .2.1`) ことから `∃ c ∈ C_G(Y)`, `M^g = M^c`; さらに
`C_G(Y) ⊆ N_G(Y) ⊆ M` ゆえ `c ∈ M` が `M` を固定し `M^g = M`。 -/
theorem conj_eq_self_of_sigma_pSubgroup_normalizer_le [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {t : ℕ} [Fact t.Prime]
    (htσ : t ∈ S10.sigma M) {Y : Subgroup G} (hYne : Y ≠ ⊥) (hYt : IsPGroup t ↥Y)
    (hNY : Subgroup.normalizer (Y : Set G) ≤ M) {g : G}
    (hYM : Y ≤ M) (hYg : Y ≤ MulAut.conj g • M) :
    MulAut.conj g • M = M := by
  have hY1 : Y ≤ MulAut.conj (1 : G) • M := by rw [map_one, one_smul]; exact hYM
  obtain ⟨c, hcC, hceq⟩ :=
    (S10.fusion_control_of_mem_sigma hG hM htσ hYne hYt).2.1 g 1 hYg hY1
  rw [map_one, one_smul] at hceq
  have hcM : c ∈ M := hNY ((Subgroup.centralizer_le_normalizer (Y : Set G)) hcC)
  have e1 : MulAut.conj c⁻¹ • (MulAut.conj c • (MulAut.conj g • M)) = MulAut.conj g • M := by
    rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  rw [hceq, conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer (M.inv_mem hcM))] at e1
  exact e1.symm

/-- **`σ(M)`-prime の `q`-部分群は `M_σ` へ共役** (BG Theorem 10.2 の帰結): `q ∈ σ(M)`, `Y` を
`q`-群とすると、ある `g` で `Y^g ⊆ M_σ`。`M_σ` が `G` の Sylow `q`-部分群を含む
(`isSylow_sylowMap_of_mem_sigma`) ことと Sylow 共役による。Lemma 13.8 GAP 2.5
(`X = O_s(H)` を `M^g` へ入れる) の核。`S12_Corollary1216.pRank_normalizer_le_one` Step 1
のインライン論法を `hM` 直接版に切り出したもの。 -/
theorem exists_conj_smul_le_Msigma_of_pSubgroup [Finite G] (hG : IsMinimalSimpleOdd G)
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

/-- **Lemma 13.8 GAP 2 の核 (H ≤ M, M-side, 向き付き)**: `s ∈ β(M)` が `F(H)` を割り、`Y` を
`M ∩ H` の非自明 `β(M)`-部分群 (`t`-群, `t ∈ β(M)`) とすると `H ≤ M`。

`X = O_s(H)` は `H` に characteristic (`H ≤ N_G(X)`) な `s`-群。`s ∈ β(M) ⊆ σ(M)` ゆえ
`exists_conj_smul_le_Msigma_of_pSubgroup` で `X^a ⊆ M_σ ⊆ M`; その `X' = X^a` に Prop 10.14(d)
を `M` 側で適用 (`N_G(X') ⊆ M`) し、共役で戻すと `H ⊆ M^{a⁻¹}`。一方 `Y ⊆ M ∩ M^{a⁻¹}` で
`conj_eq_self_of_sigma_pSubgroup_normalizer_le` (collapse) により `M^{a⁻¹} = M`、ゆえ `H ⊆ M`。

(`Y` は呼出側で `Y = O_t(C_{M_β}(P))` を渡す。β の共役不変性を要しないのが要点。) -/
theorem hall_le_of_fitting_prime [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {s : ℕ} [Fact s.Prime]
    (hsβ : s ∈ S10.beta M) {H : Subgroup G}
    (hsF : s ∈ (Nat.card ↥(Ch2.S08.fittingInG H)).primeFactors)
    {t : ℕ} [Fact t.Prime] (htβ : t ∈ S10.beta M) {Y : Subgroup G}
    (hYne : Y ≠ ⊥) (hYt : IsPGroup t ↥Y) (hYM : Y ≤ M) (hYH : Y ≤ H) :
    H ≤ M := by
  -- `X = O_s(H)`: nonidentity `s`-group, characteristic in `H`.
  have hXne : opiCoreInG ({s} : Set ℕ) H ≠ ⊥ :=
    Ch2.S08.opiCoreInG_singleton_ne_bot_of_mem_primeFactors_fittingInG hsF
  have hHNX : H ≤ Subgroup.normalizer ((opiCoreInG ({s} : Set ℕ) H : Subgroup G) : Set G) :=
    le_normalizer_opiCoreInG _ _
  have hXs : IsPGroup s ↥(opiCoreInG ({s} : Set ℕ) H) :=
    isPGroup_of_isPiSubgroup_singleton (isPiSubgroup_opiCoreInG _ _)
  have hsσ : s ∈ S10.sigma M := S10.alpha_subset_sigma hG hM (S10.beta_subset_alpha M hsβ)
  -- conjugate `X` into `M_σ`.
  obtain ⟨a, haX⟩ := exists_conj_smul_le_Msigma_of_pSubgroup hG hM hsσ hXs
  have hX'M : MulAut.conj a • (opiCoreInG ({s} : Set ℕ) H) ≤ M := haX.trans (S10.Msigma_le M)
  have hX'ne : MulAut.conj a • (opiCoreInG ({s} : Set ℕ) H) ≠ ⊥ := by
    intro hb
    apply hXne
    have h := congrArg (fun K => MulAut.conj a⁻¹ • K) hb
    simpa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul, Subgroup.smul_bot] using h
  have hX's : IsPGroup s ↥(MulAut.conj a • (opiCoreInG ({s} : Set ℕ) H)) :=
    hXs.of_equiv (Subgroup.equivMapOfInjective _ (MulAut.conj a).toMonoidHom
      (MulAut.conj a).injective)
  have hNX'M : Subgroup.normalizer
      ((MulAut.conj a • (opiCoreInG ({s} : Set ℕ) H) : Subgroup G) : Set G) ≤ M :=
    S10.normalizer_le_of_nontrivial_beta_subgroup hG hM hX'M hX'ne
      (Subgroup.isPiSubgroup_of_isPGroup_of_mem hX's hsβ)
  -- `conj a • H ≤ N_G(X') ≤ M`, hence `H ≤ M^{a⁻¹}`.
  have hconjH : MulAut.conj a • H ≤ M := by
    have h1 : MulAut.conj a • H ≤
        MulAut.conj a • Subgroup.normalizer ((opiCoreInG ({s} : Set ℕ) H : Subgroup G) : Set G) :=
      Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hHNX
    have hnorm : MulAut.conj a •
          Subgroup.normalizer ((opiCoreInG ({s} : Set ℕ) H : Subgroup G) : Set G)
        = Subgroup.normalizer
          ((MulAut.conj a • (opiCoreInG ({s} : Set ℕ) H) : Subgroup G) : Set G) :=
      Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj a).bijective
    rw [hnorm] at h1
    exact h1.trans hNX'M
  have hHg : H ≤ MulAut.conj a⁻¹ • M := by
    have hid : MulAut.conj a⁻¹ • (MulAut.conj a • H) = H := by
      rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    calc H = MulAut.conj a⁻¹ • (MulAut.conj a • H) := hid.symm
      _ ≤ MulAut.conj a⁻¹ • M := Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hconjH
  -- collapse with `Y`.
  have htσ : t ∈ S10.sigma M := S10.alpha_subset_sigma hG hM (S10.beta_subset_alpha M htβ)
  have hNY : Subgroup.normalizer (Y : Set G) ≤ M :=
    S10.normalizer_le_of_nontrivial_beta_subgroup hG hM hYM hYne
      (Subgroup.isPiSubgroup_of_isPGroup_of_mem hYt htβ)
  have hcollapse : MulAut.conj a⁻¹ • M = M :=
    conj_eq_self_of_sigma_pSubgroup_normalizer_le hG hM htσ hYne hYt hNY hYM (hYH.trans hHg)
  rwa [hcollapse] at hHg

/-- **`C_G(P)` は可解** (`P ≠ 1`): minimal simple `G` の真部分群はすべて可解 (`isSolvable_of_lt_top`)
ゆえ、`C_G(P) < ⊤` を示せばよい。`C_G(P) = ⊤` なら `P ≤ Z(G)`; `G` 単純で `Z(G) = ⊥`
(`Z(G) = ⊤` なら `G` 可換 → 可解、`notSolvable` に反す) ゆえ `P = ⊥`、仮定に反す。
Lemma 13.8 GAP 2 で `C_G(P)` の Hall θ-部分群を取るのに必要。 -/
theorem centralizer_isSolvable_of_ne_bot [Finite G] (hG : IsMinimalSimpleOdd G)
    {P : Subgroup G} (hP : P ≠ ⊥) :
    Group.IsSolvable ↥(Subgroup.centralizer (P : Set G)) := by
  apply hG.isSolvable_of_lt_top
  rw [lt_top_iff_ne_top]
  intro htop
  rcases hG.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with hc | hc
  · apply hP
    rw [eq_bot_iff, ← hc]
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer (P : Set G) := htop ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.mp hg x hx).symm
  · apply hG.notSolvable
    apply Group.isSolvable_of_comm
    intro a b
    have ha : a ∈ Subgroup.center G := hc ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm

/-- **`C_G(P)` の Hall `θ`-部分群で指定 `θ`-部分群 `U` を含むもの** (`P ≠ 1`): 可解群の Hall
D-定理 (`Ch03.hall_D`) を `↥C_G(P)` に適用。Lemma 13.8 GAP 2 で `H ⊇ C_{M_β}(P)` (M 側) /
`H ⊇ C_{M*_β}(P)` (M* 側) を取るのに使う。 -/
theorem exists_hall_theta_ge [Finite G] (hG : IsMinimalSimpleOdd G) {P : Subgroup G} (hP : P ≠ ⊥)
    {θ : Set ℕ} {U : Subgroup G} (hUC : U ≤ Subgroup.centralizer (P : Set G))
    (hUθ : Subgroup.IsPiSubgroup θ U) :
    ∃ H : Subgroup G, H ≤ Subgroup.centralizer (P : Set G) ∧
      Ch03.IsHallSubgroup θ (H.subgroupOf (Subgroup.centralizer (P : Set G))) ∧ U ≤ H := by
  have : Group.IsSolvable ↥(Subgroup.centralizer (P : Set G)) :=
    centralizer_isSolvable_of_ne_bot hG hP
  have hcond : ∀ q ∈ (Nat.card ↥(U.subgroupOf (Subgroup.centralizer (P : Set G)))).primeFactors,
      q ∈ θ := by
    intro q hq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUC).toEquiv] at hq
    exact hUθ q hq
  obtain ⟨H₀, hH₀hall, hUH₀⟩ :=
    Ch03.hall_D (G := ↥(Subgroup.centralizer (P : Set G))) (π := θ)
      (U := U.subgroupOf (Subgroup.centralizer (P : Set G))) hcond
  refine ⟨H₀.map (Subgroup.centralizer (P : Set G)).subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · have heq : (H₀.map (Subgroup.centralizer (P : Set G)).subtype).subgroupOf
        (Subgroup.centralizer (P : Set G)) = H₀ :=
      Subgroup.comap_map_eq_self_of_injective
        (Subgroup.centralizer (P : Set G)).subtype_injective H₀
    rw [heq]; exact hH₀hall
  · intro x hxU
    have hxC : x ∈ Subgroup.centralizer (P : Set G) := hUC hxU
    rw [Subgroup.mem_map]
    exact ⟨⟨x, hxC⟩, hUH₀ (Subgroup.mem_subgroupOf.mpr hxU), rfl⟩

/-- **非自明可解部分群の Fitting には素数がある**: `H ≠ 1` が可解なら `F(H) ≠ 1`
(`fitting_ne_bot_of_isSolvable_nontrivial`) ゆえ `|F(H)|` を割る素数が存在。Lemma 13.8 GAP 2 で
`s ∈ π(F(H))` (X = O_s(H) 用) と `t ∈ π(F(C_{M_β}(P)))` (Y = O_t 用) を取るのに使う。 -/
theorem exists_mem_primeFactors_fittingInG [Finite G] {H : Subgroup G}
    (hHsolv : Group.IsSolvable ↥H) (hH : H ≠ ⊥) :
    ∃ s : ℕ, s ∈ (Nat.card ↥(Ch2.S08.fittingInG H)).primeFactors := by
  have := hHsolv
  have : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hH
  have hFne : Ch01.fitting ↥H ≠ ⊥ := Ch01.fitting_ne_bot_of_isSolvable_nontrivial ↥H
  have : Nontrivial ↥(Ch01.fitting ↥H) := (Subgroup.nontrivial_iff_ne_bot _).mpr hFne
  have hcard : Nat.card ↥(Ch2.S08.fittingInG H) = Nat.card ↥(Ch01.fitting ↥H) :=
    Subgroup.card_map_of_injective H.subtype_injective
  have hgt : 1 < Nat.card ↥(Ch2.S08.fittingInG H) := by
    rw [hcard]; exact Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  obtain ⟨s, hsp, hsd⟩ := (Nat.card ↥(Ch2.S08.fittingInG H)).exists_prime_and_dvd (by omega)
  exact ⟨s, Nat.mem_primeFactors.mpr ⟨hsp, hsd, Nat.card_pos.ne'⟩⟩

/-- **Lemma 13.8 GAP 2 の `r` 抽出** (`H ≤ M` 確立後): `H` を `C_G(P)` の Hall
`(β(M)∪β(M*))`-部分群で `H ≤ M`, `Y₀* = C_{M*_β}(P)` を `C_G(P)` の非自明 `β(M*)`-部分群と
すると、ある素数 `r ∈ β(M*)` が `|C_M(P)|` を割り `r ∉ σ(M)`。

`r ∈ π(Y₀*) ⊆ β(M*)` を取る; `r ∈ θ` かつ `H` Hall θ ゆえ `r ∤ [C:H]` (`index_no_pi`)、
`|C| = |H|·[C:H]` で `r ∣ |H| ∣ |C_M(P)|`。`r ∉ σ(M)` は Lemma 10.12(a)
(`disjoint_of_not_conj`, `α(M*)∩σ(M)=∅`)。 -/
theorem exists_prime_betastar_dvd_of_hall_le [Finite G] (hG : IsMinimalSimpleOdd G)
    {M Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hMstar : Mstar ∈ maximalSubgroups G)
    (hnc' : ¬ ∃ g : G, MulAut.conj g • Mstar = M) {P H : Subgroup G}
    (hHC : H ≤ Subgroup.centralizer (P : Set G)) (hHM : H ≤ M)
    (hHhall : Ch03.IsHallSubgroup (S10.beta M ∪ S10.beta Mstar)
      (H.subgroupOf (Subgroup.centralizer (P : Set G))))
    {Y₀star : Subgroup G} (hY₀starne : Y₀star ≠ ⊥)
    (hY₀starC : Y₀star ≤ Subgroup.centralizer (P : Set G))
    (hY₀starβ : Subgroup.IsPiSubgroup (S10.beta Mstar) Y₀star) :
    ∃ r : ℕ, r.Prime ∧ r ∈ S10.beta Mstar ∧
      r ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (P : Set G)) ∧ r ∉ S10.sigma M := by
  have : Nontrivial ↥Y₀star := (Subgroup.nontrivial_iff_ne_bot _).mpr hY₀starne
  obtain ⟨r, hrp, hrd⟩ := (Nat.card ↥Y₀star).exists_prime_and_dvd
    (by have := Finite.one_lt_card_iff_nontrivial.mpr ‹Nontrivial ↥Y₀star›; omega)
  have hrβstar : r ∈ S10.beta Mstar :=
    hY₀starβ r (Nat.mem_primeFactors.mpr ⟨hrp, hrd, Nat.card_pos.ne'⟩)
  have hrC : r ∣ Nat.card ↥(Subgroup.centralizer (P : Set G)) :=
    hrd.trans (Subgroup.card_dvd_of_le hY₀starC)
  -- `r ∤ [C:H]` because `r ∈ θ` and `H` is a Hall θ-subgroup.
  have hr_ndvd_idx : ¬ r ∣ (H.subgroupOf (Subgroup.centralizer (P : Set G))).index := by
    intro hdvd
    exact (hHhall.index_no_pi r
      (Nat.mem_primeFactors.mpr ⟨hrp, hdvd, Subgroup.index_ne_zero_of_finite⟩)) (Or.inr hrβstar)
  -- `|C| = |H| · [C:H]`, so `r ∣ |H|`.
  have hcardeq : Nat.card ↥(H.subgroupOf (Subgroup.centralizer (P : Set G))) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHC).toEquiv
  have hlag : Nat.card ↥H * (H.subgroupOf (Subgroup.centralizer (P : Set G))).index =
      Nat.card ↥(Subgroup.centralizer (P : Set G)) := by
    rw [← hcardeq]; exact Subgroup.card_mul_index _
  have hrH : r ∣ Nat.card ↥H := by
    rw [← hlag] at hrC
    exact (hrp.dvd_mul.mp hrC).resolve_right hr_ndvd_idx
  have hrMC : r ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (P : Set G)) :=
    hrH.trans (Subgroup.card_dvd_of_le (le_inf hHM hHC))
  have hrσ : r ∉ S10.sigma M := by
    intro hrσM
    have hdisj := (S10.disjoint_of_not_conj hG hMstar hM hnc').1.2
    have hmem : r ∈ S10.alpha Mstar ∩ S10.sigma M :=
      ⟨S10.beta_subset_alpha Mstar hrβstar, hrσM⟩
    rw [hdisj] at hmem
    simp at hmem
  exact ⟨r, hrp, hrβstar, hrMC, hrσ⟩

/-- **Lemma 13.8 GAP 2 (M-oriented 全体)**: `H ⊇ Y₀ = C_{M_β}(P)` を `C_G(P)` の Hall
`(β(M)∪β(M*))`-部分群、`s ∈ β(M) ∩ π(F(H))`, `Y₀*` = `C_{M*_β}(P)` を非自明 `β(M*)`-部分群
とすると、ある素数 `r ∈ β(M*)` が `|C_M(P)|` を割り `r ∉ σ(M)`。

`Y = O_t(Y₀)` (`t ∈ π(F(Y₀)) ⊆ β(M)`) を bridge に `hall_le_of_fitting_prime` で `H ≤ M`、
`exists_prime_betastar_dvd_of_hall_le` で `r` を抽出。本体 `forbidden_config_impossible` は
`s ∈ π(F(H))` が `β(M)` / `β(M*)` どちらに落ちるかで本補題を向きを変えて適用する (WLOG)。 -/
theorem oriented_r_existence [Finite G] (hG : IsMinimalSimpleOdd G)
    {M Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hMstar : Mstar ∈ maximalSubgroups G)
    (hnc' : ¬ ∃ g : G, MulAut.conj g • Mstar = M) {P H : Subgroup G}
    (hHC : H ≤ Subgroup.centralizer (P : Set G))
    (hHhall : Ch03.IsHallSubgroup (S10.beta M ∪ S10.beta Mstar)
      (H.subgroupOf (Subgroup.centralizer (P : Set G))))
    {s : ℕ} [Fact s.Prime] (hsβ : s ∈ S10.beta M)
    (hsF : s ∈ (Nat.card ↥(Ch2.S08.fittingInG H)).primeFactors)
    {Y₀ : Subgroup G} (hY₀ne : Y₀ ≠ ⊥) (hY₀M : Y₀ ≤ M) (hY₀H : Y₀ ≤ H)
    (hY₀β : Subgroup.IsPiSubgroup (S10.beta M) Y₀)
    {Y₀star : Subgroup G} (hY₀starne : Y₀star ≠ ⊥)
    (hY₀starC : Y₀star ≤ Subgroup.centralizer (P : Set G))
    (hY₀starβ : Subgroup.IsPiSubgroup (S10.beta Mstar) Y₀star) :
    ∃ r : ℕ, r.Prime ∧ r ∈ S10.beta Mstar ∧
      r ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (P : Set G)) ∧ r ∉ S10.sigma M := by
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hY₀solv : Group.IsSolvable ↥Y₀ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hY₀M)
  obtain ⟨t, htF⟩ := exists_mem_primeFactors_fittingInG hY₀solv hY₀ne
  have : Fact t.Prime := ⟨Nat.prime_of_mem_primeFactors htF⟩
  have htβ : t ∈ S10.beta M := by
    apply hY₀β
    have hdvd : t ∣ Nat.card ↥Y₀ :=
      (Nat.mem_primeFactors.mp htF).2.1.trans
        (Subgroup.card_dvd_of_le (Ch2.S08.fittingInG_le Y₀))
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors htF, hdvd, Nat.card_pos.ne'⟩
  have hYne : opiCoreInG ({t} : Set ℕ) Y₀ ≠ ⊥ :=
    Ch2.S08.opiCoreInG_singleton_ne_bot_of_mem_primeFactors_fittingInG htF
  have hYt : IsPGroup t ↥(opiCoreInG ({t} : Set ℕ) Y₀) :=
    isPGroup_of_isPiSubgroup_singleton (isPiSubgroup_opiCoreInG _ _)
  have hYY₀ : opiCoreInG ({t} : Set ℕ) Y₀ ≤ Y₀ := opiCoreInG_le _ _
  have hHM : H ≤ M :=
    hall_le_of_fitting_prime hG hM hsβ hsF htβ hYne hYt (hYY₀.trans hY₀M) (hYY₀.trans hY₀H)
  exact exists_prime_betastar_dvd_of_hall_le hG hM hMstar hnc' hHC hHM hHhall
    hY₀starne hY₀starC hY₀starβ

/-- **Lemma 13.8 GAP 3 の最終矛盾 (assembly)**: `X = C_{M_α}(P) ≠ 1` で `⁅X, Q⁆ ≤ M*_α`
(GAP 3 の elision (iv) の出力)、`M_α ⊓ M*_α = 1` (Lemma 10.12), `C_{M_α}(PQ) = 1`
(Lemma 12.18, step1 punchline) とすると矛盾。

`⁅X,Q⁆ ≤ M_α` (X ≤ M_α が `M` で正規) かつ `≤ M*_α` ゆえ `⁅X,Q⁆ = 1` (M_α∩M*_α=1)、よって
`X ≤ C(Q)`; `X ≤ C(P)` (定義) と合わせ `X ≤ C(P⊔Q)`、`X ≤ M_α ⊓ C(PQ) = 1`、`X ≠ 1` に反す。 -/
theorem gap3_assembly [Finite G] {M Mstar Q P : Subgroup G} (hQM : Q ≤ M)
    (hXne : S10.Malpha M ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥)
    (hXQ : ⁅S10.Malpha M ⊓ Subgroup.centralizer (P : Set G), Q⁆ ≤ S10.Malpha Mstar)
    (hMαMstarα : S10.Malpha M ⊓ S10.Malpha Mstar = ⊥)
    (hCMαPQ : S10.Malpha M ⊓ Subgroup.centralizer ((P ⊔ Q : Subgroup G) : Set G) = ⊥) :
    False := by
  have hMnorm : M ≤ Subgroup.normalizer ((S10.Malpha M : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (S10.Malpha_le M)).mp
      (S10.Malpha_subgroupOf_normal M)
  have hXQ_Mα : ⁅S10.Malpha M ⊓ Subgroup.centralizer (P : Set G), Q⁆ ≤ S10.Malpha M := by
    rw [Subgroup.commutator_le]
    intro a ha m hm
    have haMα : a ∈ S10.Malpha M := (Subgroup.mem_inf.mp ha).1
    have hmnorm := hMnorm (hQM hm)
    have h1 : m * a⁻¹ * m⁻¹ ∈ S10.Malpha M :=
      (Subgroup.mem_normalizer_iff.mp hmnorm a⁻¹).mp ((S10.Malpha M).inv_mem haMα)
    rw [commutatorElement_def]
    have heq : a * m * a⁻¹ * m⁻¹ = a * (m * a⁻¹ * m⁻¹) := by group
    rw [heq]
    exact (S10.Malpha M).mul_mem haMα h1
  have hXQ_bot : ⁅S10.Malpha M ⊓ Subgroup.centralizer (P : Set G), Q⁆ = ⊥ :=
    le_bot_iff.mp (hMαMstarα ▸ le_inf hXQ_Mα hXQ)
  have hXCQ : S10.Malpha M ⊓ Subgroup.centralizer (P : Set G) ≤
      Subgroup.centralizer (Q : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hXQ_bot
  have hXCPQ : S10.Malpha M ⊓ Subgroup.centralizer (P : Set G) ≤
      Subgroup.centralizer ((P ⊔ Q : Subgroup G) : Set G) := by
    rw [Subgroup.centralizer_sup]
    exact le_inf inf_le_right hXCQ
  exact hXne (le_bot_iff.mp (hCMαPQ ▸ le_inf inf_le_left hXCPQ))

/-- **`p`-core の像 ≤ `p`-core** (群同型 `e`): `(O_p(A)).map e ≤ O_p(B)`。像は正規 `p`-部分群
ゆえ `normal_pgroup_le_opCore`。 -/
theorem opCore_map_le_of_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    {p : ℕ} [Fact p.Prime] (e : A ≃* B) :
    (Ch01.opCore p A).map e.toMonoidHom ≤ Ch01.opCore p B := by
  have : ((Ch01.opCore p A).map e.toMonoidHom).Normal :=
    (Ch01.opCore.normal p A).map e.toMonoidHom e.surjective
  exact Ch01.normal_pgroup_le_opCore
    ((Ch01.opCore_isPGroup p A).of_equiv
      (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective))

/-- **`p`-core は群同型で保たれる**: `e : A ≃* B` なら `(O_p(A)).map e = O_p(B)`。 -/
theorem opCore_map_of_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    {p : ℕ} [Fact p.Prime] (e : A ≃* B) :
    (Ch01.opCore p A).map e.toMonoidHom = Ch01.opCore p B := by
  refine le_antisymm (opCore_map_le_of_mulEquiv e) ?_
  have h2 := opCore_map_le_of_mulEquiv (p := p) e.symm
  have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id B := by ext x; simp
  calc Ch01.opCore p B
      = (Ch01.opCore p B).map (MonoidHom.id B) := (Subgroup.map_id _).symm
    _ = ((Ch01.opCore p B).map e.symm.toMonoidHom).map e.toMonoidHom := by
        rw [← hid, Subgroup.map_map]
    _ ≤ (Ch01.opCore p A).map e.toMonoidHom := Subgroup.map_mono h2

/-- **Fitting 部分群の位数は群同型で不変**: `e : A ≃* B` なら `|F(A)| = |F(B)|`。
`F = ⨆ O_p` を `opCore_map_of_mulEquiv` + `map_iSup` で写し、`card_map_of_injective`。 -/
theorem fitting_card_eq_of_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) : Nat.card ↥(Ch01.fitting A) = Nat.card ↥(Ch01.fitting B) := by
  have hmap : (Ch01.fitting A).map e.toMonoidHom = Ch01.fitting B := by
    unfold Ch01.fitting
    rw [Subgroup.map_iSup]
    refine iSup_congr (fun p => ?_)
    have : Fact (p : ℕ).Prime := ⟨p.2⟩
    exact opCore_map_of_mulEquiv e
  rw [← hmap, Subgroup.card_map_of_injective e.injective]

/-- **共役 Hall 部分群の `F`-素因子は一致** (Lemma 13.8 dispatch の核): `C` 可解で `H, K` が
`C` の Hall `θ`-部分群 (相対) なら `π(F(H)) = π(F(K))`。`hall_C` で `H, K` は `C` 内共役、
`fitting_card_eq_of_mulEquiv` で `|F(H)| = |F(K)|`。

13.8 main: `s ∈ π(F(H))` (`H ⊇ C_{M_β}(P)`) を `π(F(H*))` (`H* ⊇ C_{M*_β}(P)`) へ移送し
WLOG `s ∈ β(M)` / `β(M*)` の向き切替を可能にする。 -/
theorem fittingInG_primeFactors_eq_of_isHall_subgroupOf [Finite G] {C H K : Subgroup G}
    [Group.IsSolvable ↥C] {θ : Set ℕ} (hHC : H ≤ C) (hKC : K ≤ C)
    (hH : Ch03.IsHallSubgroup θ (H.subgroupOf C)) (hK : Ch03.IsHallSubgroup θ (K.subgroupOf C)) :
    (Nat.card ↥(Ch2.S08.fittingInG H)).primeFactors
      = (Nat.card ↥(Ch2.S08.fittingInG K)).primeFactors := by
  obtain ⟨c, hc⟩ := Ch03.hall_C hH hK
  have ehk : ↥(H.subgroupOf C) ≃* ↥(K.subgroupOf C) := by
    rw [← hc]
    exact Subgroup.equivMapOfInjective _ (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
  have e : ↥H ≃* ↥K :=
    (Subgroup.subgroupOfEquivOfLe hHC).symm.trans (ehk.trans (Subgroup.subgroupOfEquivOfLe hKC))
  have h1 : Nat.card ↥(Ch2.S08.fittingInG H) = Nat.card ↥(Ch01.fitting ↥H) :=
    Subgroup.card_map_of_injective H.subtype_injective
  have h2 : Nat.card ↥(Ch2.S08.fittingInG K) = Nat.card ↥(Ch01.fitting ↥K) :=
    Subgroup.card_map_of_injective K.subtype_injective
  rw [h1, h2, fitting_card_eq_of_mulEquiv e]

/-- **Lemma 13.8 GAP 2 capstone (WLOG dispatch)**: step1 出力 (`α=β`, `C_{M_α}(P)≠1`,
`C_{M*_α}(P)≠1`) から、`r ∈ β(M*)` が `|C_M(P)|` を割り `r∉σ(M)`、**または** 対称な
`r ∈ β(M)` が `|C_{M*}(P)|` を割り `r∉σ(M*)`。

`H ⊇ C_{M_β}(P)` を `C_G(P)` の Hall `θ`-部分群 (`θ=β(M)∪β(M*)`) に取り `s∈π(F(H))⊆θ` で場合分け:
`s∈β(M)` なら `oriented_r_existence`(M,M*); `s∈β(M*)` なら `H*⊇C_{M*_β}(P)` を取り
`fittingInG_primeFactors_eq` で `s∈π(F(H*))` 移送し `oriented_r_existence`(M*,M)。 -/
theorem exists_prime_betastar_dvd_or [Finite G] (hG : IsMinimalSimpleOdd G)
    {M Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hMstar : Mstar ∈ maximalSubgroups G)
    (hnc : ¬ ∃ g : G, MulAut.conj g • M = Mstar) {P : Subgroup G} (hP1 : P ≠ ⊥)
    (hαβ : S10.alpha M = S10.beta M) (hαβstar : S10.alpha Mstar = S10.beta Mstar)
    (hCMαP : S10.Malpha M ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥)
    (hCMstarαP : S10.Malpha Mstar ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥) :
    (∃ r : ℕ, r.Prime ∧ r ∈ S10.beta Mstar ∧
      r ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (P : Set G)) ∧ r ∉ S10.sigma M) ∨
    (∃ r : ℕ, r.Prime ∧ r ∈ S10.beta M ∧
      r ∣ Nat.card ↥(Mstar ⊓ Subgroup.centralizer (P : Set G)) ∧ r ∉ S10.sigma Mstar) := by
  classical
  have : Group.IsSolvable ↥(Subgroup.centralizer (P : Set G)) :=
    centralizer_isSolvable_of_ne_bot hG hP1
  -- `C_{M_α}(P)` / `C_{M*_α}(P)` は `β`-部分群 (`Malpha_isPiGroup` + `α=β`)。
  have hbeta : ∀ {N : Subgroup G}, S10.alpha N = S10.beta N →
      Subgroup.IsPiSubgroup (S10.beta N) (S10.Malpha N ⊓ Subgroup.centralizer (P : Set G)) := by
    intro N hN p hp
    have hp' : p ∈ (Nat.card ↥(S10.Malpha N)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hp).1,
        (Nat.mem_primeFactors.mp hp).2.1.trans (Subgroup.card_dvd_of_le inf_le_left),
        Nat.card_pos.ne'⟩
    rw [← hN]; exact S10.Malpha_isPiGroup N p hp'
  have hYMβ := hbeta hαβ
  have hYMstarβ := hbeta hαβstar
  have hYMθ : Subgroup.IsPiSubgroup (S10.beta M ∪ S10.beta Mstar)
      (S10.Malpha M ⊓ Subgroup.centralizer (P : Set G)) :=
    fun p hp => Set.mem_union_left _ (hYMβ p hp)
  have hYMstarθ : Subgroup.IsPiSubgroup (S10.beta M ∪ S10.beta Mstar)
      (S10.Malpha Mstar ⊓ Subgroup.centralizer (P : Set G)) :=
    fun p hp => Set.mem_union_right _ (hYMstarβ p hp)
  have hCMαP_le : S10.Malpha M ⊓ Subgroup.centralizer (P : Set G) ≤ Subgroup.centralizer (P:Set
      G) :=
    inf_le_right
  have hCMstarαP_le :
      S10.Malpha Mstar ⊓ Subgroup.centralizer (P : Set G) ≤ Subgroup.centralizer (P:Set G) :=
    inf_le_right
  -- `nc` symmetry: `¬∃g, conj g•Mstar=M`.
  have hnc' : ¬ ∃ g : G, MulAut.conj g • Mstar = M := by
    rintro ⟨g, hg⟩
    exact hnc ⟨g⁻¹, by rw [← hg, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]⟩
  -- build `H ⊇ C_{M_β}(P)`, Hall `θ`.
  obtain ⟨H, hHC, hHhall, hYH⟩ :=
    exists_hall_theta_ge hG hP1 hCMαP_le hYMθ (θ := S10.beta M ∪ S10.beta Mstar)
  have : Group.IsSolvable ↥H :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hHC)
  have hHne : H ≠ ⊥ := fun h => hCMαP (le_bot_iff.mp (h ▸ hYH))
  obtain ⟨s, hsF⟩ := exists_mem_primeFactors_fittingInG ‹Group.IsSolvable ↥H› hHne
  have : Fact s.Prime := ⟨Nat.prime_of_mem_primeFactors hsF⟩
  -- `s ∈ θ` (F(H) ≤ H, H Hall θ).
  have hsθ : s ∈ S10.beta M ∪ S10.beta Mstar := by
    have hsH : s ∈ (Nat.card ↥H).primeFactors := by
      refine Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hsF, ?_, Nat.card_pos.ne'⟩
      exact (Nat.mem_primeFactors.mp hsF).2.1.trans
        (Subgroup.card_dvd_of_le (Ch2.S08.fittingInG_le H))
    have := hHhall.primeFactors_card_subset s
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHC).toEquiv] at this
    exact this hsH
  rcases hsθ with hsM | hsMstar
  · -- `s ∈ β(M)`: M-side.
    exact Or.inl (oriented_r_existence hG hM hMstar hnc' hHC hHhall hsM hsF hCMαP
      (inf_le_left.trans (S10.Malpha_le M)) hYH hYMβ hCMstarαP hCMstarαP_le hYMstarβ)
  · -- `s ∈ β(M*)`: M*-side. build `H* ⊇ C_{M*_β}(P)`, transport `s ∈ π(F(H*))`.
    obtain ⟨Hs, hHsC, hHshall, hYHs⟩ :=
      exists_hall_theta_ge hG hP1 hCMstarαP_le hYMstarθ (θ := S10.beta M ∪ S10.beta Mstar)
    have hsFs : s ∈ (Nat.card ↥(Ch2.S08.fittingInG Hs)).primeFactors := by
      rw [← fittingInG_primeFactors_eq_of_isHall_subgroupOf hHC hHsC hHhall hHshall]; exact hsF
    have hHshall' : Ch03.IsHallSubgroup (S10.beta Mstar ∪ S10.beta M)
        (Hs.subgroupOf (Subgroup.centralizer (P : Set G))) := by
      rwa [Set.union_comm] at hHshall
    exact Or.inr (oriented_r_existence hG hMstar hM hnc hHsC hHshall' hsMstar hsFs hCMstarαP
      (inf_le_left.trans (S10.Malpha_le Mstar)) hYHs hYMstarβ hCMαP hCMαP_le hYMβ)

/-- **Lemma 13.8 head — `Q = [Q,P] ⊆ M' ∩ M*'`**: `P` が `Q` を coprime に作用し `C_Q(P)=1` なら
`Q ≤ ⁅P,Q⁆` (`le_commutator_of_coprime_inf_centralizer_eq_bot`); `P,Q ⊆ M` (resp. `M*`) ゆえ
`⁅P,Q⁆ ⊆ ⁅M,M⁆ = M'` (resp. `M*'`)。 -/
theorem pSubgroup_le_derived_inf [Finite G] {M Mstar P Q : Subgroup G}
    [Group.IsSolvable ↥P] (hPN : P ≤ Subgroup.normalizer (Q : Set G))
    (hcop : Nat.Coprime (Nat.card ↥P) (Nat.card ↥Q))
    (hCQ : Q ⊓ Subgroup.centralizer (P : Set G) = ⊥)
    (hPM : P ≤ M) (hQM : Q ≤ M) (hPMs : P ≤ Mstar) (hQMs : Q ≤ Mstar) :
    Q ≤ derivedInG M ⊓ derivedInG Mstar := by
  have hQcomm : Q ≤ ⁅P, Q⁆ :=
    Ch2.S08.le_commutator_of_coprime_inf_centralizer_eq_bot hPN hcop hCQ
  have hM : ⁅P, Q⁆ ≤ derivedInG M := by
    have h := Subgroup.commutator_mono hPM hQM
    rwa [← Subgroup.map_subtype_commutator M] at h
  have hMs : ⁅P, Q⁆ ≤ derivedInG Mstar := by
    have h := Subgroup.commutator_mono hPMs hQMs
    rwa [← Subgroup.map_subtype_commutator Mstar] at h
  exact le_inf (hQcomm.trans hM) (hQcomm.trans hMs)

/-- **極大 `q`-部分群は Sylow `q`-部分群**: `Q` が `H` の `q`-部分群で `q`-部分群について極大なら
`Q` は Sylow。`Sylow` の `is_maximal'` フィールドで直接構成。 -/
theorem sylow_of_maximal_pSubgroup {H : Type*} [Group H] [Finite H] {q : ℕ} [Fact q.Prime]
    {Q : Subgroup H} (hQq : IsPGroup q ↥Q)
    (hmax : ∀ T : Subgroup H, IsPGroup q ↥T → Q ≤ T → T = Q) :
    ∃ S : Sylow q H, (S : Subgroup H) = Q :=
  ⟨⟨Q, hQq, fun hTq hQT => hmax _ hTq hQT⟩, rfl⟩

/-- **Lemma 13.8 head Frattini の正規性核**: `Q` を `M` の Sylow `q`-部分群 (`q∉β(M)`),
`Q ⊆ M'` とすると `M ≤ N_G(M_β ⊔ Q)` (すなわち `M_β·Q ⊲ M`)。

`M_β·Q ⊲ M'` (`normal_sup_sylow_of_quotient_nilpotent`, `M'/M_β` nilpotent) を取り、
`m ∈ M` について `Q^m` は `M'` の Sylow `q` ゆえ `M'` 内で `Q` に共役 (`Q^m = Q^c`, `c∈M'`)、
`Q^c ⊆ (M_β·Q)^c = M_β·Q` (`M_β·Q ⊲ M'`)。商を経由しない char-step。 -/
theorem QMbeta_sup_normal_in_M [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {q : ℕ} [Fact q.Prime] {Q : Subgroup G}
    (hQq : IsPGroup q ↥Q)
    (hQmaxM : ∀ T : Subgroup G, T ≤ M → IsPGroup q ↥T → Q ≤ T → Q = T)
    (hqβ : q ∉ S10.beta M) (hQderiv : Q ≤ derivedInG M) :
    M ≤ Subgroup.normalizer ((S10.Mbeta M ⊔ Q : Subgroup G) : Set G) := by
  classical
  have hDM : derivedInG M ≤ M := Subgroup.map_subtype_le _
  -- `Q.subgroupOf M'` is a Sylow `q` of `↥M'`.
  have hQDq : IsPGroup q ↥(Q.subgroupOf (derivedInG M)) :=
    hQq.of_equiv (Subgroup.subgroupOfEquivOfLe hQderiv).symm
  have hQDmax : ∀ T : Subgroup ↥(derivedInG M), IsPGroup q ↥T →
      Q.subgroupOf (derivedInG M) ≤ T → T = Q.subgroupOf (derivedInG M) := by
    intro T hTq hQT
    have hQT' : Q ≤ T.map (derivedInG M).subtype := by
      have h : (Q.subgroupOf (derivedInG M)).map (derivedInG M).subtype ≤
          T.map (derivedInG M).subtype := Subgroup.map_mono hQT
      rwa [Subgroup.subgroupOf_map_subtype Q (derivedInG M), inf_eq_left.mpr hQderiv] at h
    have heq := hQmaxM (T.map (derivedInG M).subtype)
      ((Subgroup.map_subtype_le T).trans hDM)
      (hTq.of_equiv (Subgroup.equivMapOfInjective T (derivedInG M).subtype
        (derivedInG M).subtype_injective)) hQT'
    calc T = (T.map (derivedInG M).subtype).subgroupOf (derivedInG M) :=
          (Subgroup.comap_map_eq_self_of_injective (derivedInG M).subtype_injective T).symm
      _ = Q.subgroupOf (derivedInG M) := by rw [← heq]
  obtain ⟨QD, hQDeq⟩ := sylow_of_maximal_pSubgroup hQDq hQDmax
  -- `M_β ⊔ Q ⊲ M'`.
  have hMβD : S10.Mbeta M ≤ derivedInG M := Mbeta_le_derived hG hM
  have hMβnorm : ((S10.Mbeta M).subgroupOf (derivedInG M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMβD).mpr
      (hDM.trans (le_normalizer_opiCoreInG (S10.beta M) M))
  have hnilp : Group.IsNilpotent (↥(derivedInG M) ⧸ (S10.Mbeta M).subgroupOf (derivedInG M)) :=
    S10.derivedQuotientMbeta_isNilpotent hG hM
  have hNq' : ¬ q ∣ Nat.card ↥((S10.Mbeta M).subgroupOf (derivedInG M)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMβD).toEquiv]
    intro hdvd
    have hqpf : q ∈ (Nat.card ↥(S10.Mbeta M)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, (Nat.card_pos (α := ↥(S10.Mbeta M))).ne'⟩
    exact hqβ (S10.Mbeta_isPiGroup M q hqpf)
  have hNorm : ((S10.Mbeta M).subgroupOf (derivedInG M) ⊔
      (QD : Subgroup ↥(derivedInG M))).Normal :=
    S10.normal_sup_sylow_of_quotient_nilpotent hnilp hNq' QD
  -- transport: `(M_β ⊔ Q).subgroupOf M' = M_β.subgroupOf M' ⊔ QD` ⟹ `⊲ ↥M'`.
  have hQMβsub : (S10.Mbeta M ⊔ Q).subgroupOf (derivedInG M) =
      (S10.Mbeta M).subgroupOf (derivedInG M) ⊔ (QD : Subgroup ↥(derivedInG M)) := by
    rw [Subgroup.subgroupOf_sup hMβD hQderiv, hQDeq]
  have hQMβnorm : ((S10.Mbeta M ⊔ Q).subgroupOf (derivedInG M)).Normal := hQMβsub ▸ hNorm
  -- `|Q| = q ^ v_q(|M'|)` (Q is a Sylow `q` of `↥M'`).
  have hQcard : Nat.card ↥Q = q ^ (Nat.card ↥(derivedInG M)).factorization q := by
    rw [← Sylow.card_eq_multiplicity QD, hQDeq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQderiv).toEquiv]
  have hMβQM' : S10.Mbeta M ⊔ Q ≤ derivedInG M := sup_le hMβD hQderiv
  have hM'normMβQ : derivedInG M ≤ Subgroup.normalizer ((S10.Mbeta M ⊔ Q : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMβQM').mp hQMβnorm
  -- char-step: `m ∈ M ⟹ conj m • (M_β ⊔ Q) = M_β ⊔ Q`.
  intro m hm
  apply mem_normalizer_of_conj_smul_eq_self
  have hmM' : MulAut.conj m • derivedInG M = derivedInG M :=
    conj_smul_eq_self_of_mem_normalizer (S10.le_normalizer_derivedInG M hm)
  have hmMβ : MulAut.conj m • S10.Mbeta M = S10.Mbeta M :=
    conj_smul_eq_self_of_mem_normalizer (le_normalizer_opiCoreInG (S10.beta M) M hm)
  have hmQ_le : MulAut.conj m • Q ≤ derivedInG M :=
    hmM' ▸ Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hQderiv
  -- `conj m • Q` is a Sylow `q` of `↥M'`.
  have hmQcard : Nat.card ↥((MulAut.conj m • Q).subgroupOf (derivedInG M)) =
      q ^ (Nat.card ↥(derivedInG M)).factorization q := by
    have e2 : Nat.card ↥(MulAut.conj m • Q) = Nat.card ↥Q :=
      Nat.card_congr (Subgroup.equivMapOfInjective Q (MulAut.conj m).toMonoidHom
        (MulAut.conj m).injective).symm.toEquiv
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hmQ_le).toEquiv, e2, hQcard]
  set Qm : Sylow q ↥(derivedInG M) :=
    Sylow.ofCard ((MulAut.conj m • Q).subgroupOf (derivedInG M)) hmQcard with hQmdef
  -- Sylow conjugacy in `↥M'`: `c • QD = Qm`.
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥(derivedInG M) QD Qm
  -- transport: `conj ↑c • Q = conj m • Q`.
  have hmapconj : ∀ (K : Subgroup ↥(derivedInG M)),
      (MulAut.conj c • K).map (derivedInG M).subtype
        = MulAut.conj (c : G) • (K.map (derivedInG M).subtype) := by
    intro K
    have hcomp : (MulAut.conj (c : G)).toMonoidHom.comp (derivedInG M).subtype
        = (derivedInG M).subtype.comp (MulAut.conj c).toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
    change (K.map (MulAut.conj c).toMonoidHom).map (derivedInG M).subtype
        = (K.map (derivedInG M).subtype).map (MulAut.conj (c : G)).toMonoidHom
    rw [Subgroup.map_map, Subgroup.map_map, hcomp]
  have hcQ : MulAut.conj (c : G) • Q = MulAut.conj m • Q := by
    have hsmul : MulAut.conj c • Q.subgroupOf (derivedInG M) =
        (MulAut.conj m • Q).subgroupOf (derivedInG M) := by
      have h : ((c • QD : Sylow q ↥(derivedInG M)) : Subgroup ↥(derivedInG M))
          = (Qm : Subgroup ↥(derivedInG M)) := by rw [hc]
      rwa [Sylow.coe_subgroup_smul, hQDeq, hQmdef, Sylow.coe_ofCard] at h
    have hmap := congrArg (fun (X : Subgroup ↥(derivedInG M)) => X.map (derivedInG M).subtype) hsmul
    simpa only [hmapconj, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hQderiv, inf_of_le_left hmQ_le] using hmap
  have hcMβQ : MulAut.conj (c : G) • (S10.Mbeta M ⊔ Q) = S10.Mbeta M ⊔ Q :=
    conj_smul_eq_self_of_mem_normalizer (hM'normMβQ c.2)
  have hkey : MulAut.conj m • Q ≤ S10.Mbeta M ⊔ Q := by
    rw [← hcQ, ← hcMβQ]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr le_sup_right
  have hle : MulAut.conj m • (S10.Mbeta M ⊔ Q) ≤ S10.Mbeta M ⊔ Q := by
    rw [Subgroup.smul_sup, hmMβ]; exact sup_le le_sup_left hkey
  exact Subgroup.eq_of_le_of_card_ge hle
    (Nat.card_congr (Subgroup.equivMapOfInjective (S10.Mbeta M ⊔ Q)
      (MulAut.conj m).toMonoidHom (MulAut.conj m).injective).symm.toEquiv).ge

/-- **Lemma 13.8 head Frattini 結論** `M = N_M(Q) · M_β`: `Q` を `M` の Sylow `q`-部分群
(`q∉β(M)`), `Q ⊆ M'` とすると `M = (M ⊓ N_G(Q)) ⊔ M_β`。`M_β ⊔ Q ⊲ M`
(`QMbeta_sup_normal_in_M`) と `Q` が `M_β ⊔ Q` の Sylow `q` であることから Frattini argument
(`Sylow.normalizer_sup_eq_top`)。 -/
theorem M_eq_normalizer_sup_Mbeta [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {q : ℕ} [Fact q.Prime] {Q : Subgroup G} (hQM : Q ≤ M)
    (hQq : IsPGroup q ↥Q)
    (hQmaxM : ∀ T : Subgroup G, T ≤ M → IsPGroup q ↥T → Q ≤ T → Q = T)
    (hqβ : q ∉ S10.beta M) (hQderiv : Q ≤ derivedInG M) :
    M = (M ⊓ Subgroup.normalizer (Q : Set G)) ⊔ S10.Mbeta M := by
  have hMβM : S10.Mbeta M ≤ M := S10.Mbeta_le M
  have hMβQM : S10.Mbeta M ⊔ Q ≤ M := sup_le hMβM hQM
  have hNorm : ((S10.Mbeta M ⊔ Q).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMβQM).mpr
      (QMbeta_sup_normal_in_M hG hM hQq hQmaxM hqβ hQderiv)
  -- `Q.subgroupOf M` is a Sylow `q` of `↥M`.
  have hQMmax : ∀ T : Subgroup ↥M, IsPGroup q ↥T → Q.subgroupOf M ≤ T → T = Q.subgroupOf M := by
    intro T hTq hQT
    have hQT' : Q ≤ T.map M.subtype := by
      have h : (Q.subgroupOf M).map M.subtype ≤ T.map M.subtype := Subgroup.map_mono hQT
      rwa [Subgroup.subgroupOf_map_subtype Q M, inf_eq_left.mpr hQM] at h
    have heq := hQmaxM (T.map M.subtype) (Subgroup.map_subtype_le T)
      (hTq.of_equiv (Subgroup.equivMapOfInjective T M.subtype M.subtype_injective)) hQT'
    calc T = (T.map M.subtype).subgroupOf M :=
          (Subgroup.comap_map_eq_self_of_injective M.subtype_injective T).symm
      _ = Q.subgroupOf M := by rw [← heq]
  obtain ⟨QMs, hQMseq⟩ :=
    sylow_of_maximal_pSubgroup (hQq.of_equiv (Subgroup.subgroupOfEquivOfLe hQM).symm) hQMmax
  have hPN : (QMs : Subgroup ↥M) ≤ (S10.Mbeta M ⊔ Q).subgroupOf M := by
    rw [hQMseq]; exact Subgroup.subgroupOf_mono M le_sup_right
  have hFrattini := Sylow.normalizer_sup_eq_top' QMs hPN
  rw [← Sylow.coe_coe, hQMseq, ← Subgroup.subgroupOf_normalizer_eq hQM] at hFrattini
  have hmap := congrArg (Subgroup.map M.subtype) hFrattini
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype, inf_eq_left.mpr hMβQM] at hmap
  -- hmap : (N_G(Q) ⊓ M) ⊔ (M_β ⊔ Q) = M
  have hQA : Q ≤ M ⊓ Subgroup.normalizer (Q : Set G) := le_inf hQM Subgroup.le_normalizer
  have hlat : Subgroup.normalizer (Q : Set G) ⊓ M ⊔ (S10.Mbeta M ⊔ Q)
      = M ⊓ Subgroup.normalizer (Q : Set G) ⊔ S10.Mbeta M := by
    rw [inf_comm, sup_comm (S10.Mbeta M) Q, ← sup_assoc, sup_eq_left.mpr hQA]
  rw [hlat] at hmap
  exact hmap.symm

/-- **coprime commutator 恒等式の `Q`-invariant 版** (BG Prop 1.6(b) を `D` 非正規へ一般化):
`Q` が `D` を正規化し、`D ⊔ Q` が可解、`|D|,|Q|` 互素なら `⁅⁅D, Q⁆, Q⁆ = ⁅D, Q⁆`。
`D` は `G` で正規でなくてよい — ambient `D ⊔ Q` (ここで `D ⊴ D⊔Q`) で
`OperatorQuotientAction.commutator_commutator_right_eq` を適用し `D⊔Q ↪ G` で戻す。 -/
theorem commutator_commutator_right_eq_of_le_normalizer [Finite G] {D Q : Subgroup G}
    (hsolv : Group.IsSolvable ↥(D ⊔ Q)) (hQD : Q ≤ Subgroup.normalizer (D : Set G))
    (hcop : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Q)) :
    ⁅⁅D, Q⁆, Q⁆ = ⁅D, Q⁆ := by
  set DQ : Subgroup G := D ⊔ Q with hDQdef
  have hD_le : D ≤ DQ := le_sup_left
  have hQ_le : Q ≤ DQ := le_sup_right
  have hDQnorm : DQ ≤ Subgroup.normalizer (D : Set G) := sup_le Subgroup.le_normalizer hQD
  have : Group.IsSolvable ↥DQ := hsolv
  have : (D.subgroupOf DQ).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hDQnorm
  have hcop' : Nat.Coprime (Nat.card ↥(D.subgroupOf DQ)) (Nat.card ↥(Q.subgroupOf DQ)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le).toEquiv]
    exact hcop
  have h2 := OddOrder.BG.Ch1.OperatorQuotientAction.commutator_commutator_right_eq
    (D.subgroupOf DQ) (Q.subgroupOf DQ) hcop'
  have hDmap : (D.subgroupOf DQ).map DQ.subtype = D := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hD_le]
  have hQmap : (Q.subgroupOf DQ).map DQ.subtype = Q := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQ_le]
  have h3 := congrArg (Subgroup.map DQ.subtype) h2
  simp only [Subgroup.map_commutator] at h3
  rw [hDmap, hQmap] at h3
  exact h3

/-- **nilpotent 商で coprime 部分群の commutator は `M*_α` へ** (Lemma 13.8 (iv) の核):
`A, B ≤ M*'` で `|A|, |B|` 互素なら `⁅A, B⁆ ≤ M*_α`。`M*'/M*_α` nilpotent (Thm 10.2,
`derived_quotient_Malpha_le_fitting`) より `↥M*/M*_α` の Fitting は冪零で、`A,B` の像は coprime
位数ゆえ可換 (`commute_of_coprime_orderOf_of_isNilpotent`)、よって `⁅A,B⁆` は `mk'` の核 `M*_α`。 -/
theorem commutator_le_Malpha_of_coprime_le_derived [Finite G] (hG : IsMinimalSimpleOdd G)
    {Mstar : Subgroup G} (hMstar : Mstar ∈ maximalSubgroups G) {A B : Subgroup G}
    (hA : A ≤ derivedInG Mstar) (hB : B ≤ derivedInG Mstar)
    (hcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥B)) :
    ⁅A, B⁆ ≤ S10.Malpha Mstar := by
  classical
  have hder_le : derivedInG Mstar ≤ Mstar := Subgroup.map_subtype_le _
  set N : Subgroup ↥Mstar := (S10.Malpha Mstar).subgroupOf Mstar with hNdef
  have : N.Normal := S10.Malpha_subgroupOf_normal Mstar
  set π : ↥Mstar →* (↥Mstar ⧸ N) := QuotientGroup.mk' N with hπdef
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hcommmap : (commutator ↥Mstar).map π = commutator (↥Mstar ⧸ N) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective π hsurj]
  have hcomm_fit : commutator (↥Mstar ⧸ N) ≤ Ch01.fitting (↥Mstar ⧸ N) :=
    S10.derived_quotient_Malpha_le_fitting hG hMstar
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have haM : a ∈ Mstar := hder_le (hA ha)
  have hbM : b ∈ Mstar := hder_le (hB hb)
  have haC : (⟨a, haM⟩ : ↥Mstar) ∈ commutator ↥Mstar := by
    have h := hA ha
    rw [derivedInG, Subgroup.mem_map] at h
    obtain ⟨y, hy, hya⟩ := h
    have hye : y = (⟨a, haM⟩ : ↥Mstar) := Subtype.ext hya
    rwa [hye] at hy
  have hbC : (⟨b, hbM⟩ : ↥Mstar) ∈ commutator ↥Mstar := by
    have h := hB hb
    rw [derivedInG, Subgroup.mem_map] at h
    obtain ⟨y, hy, hyb⟩ := h
    have hye : y = (⟨b, hbM⟩ : ↥Mstar) := Subtype.ext hyb
    rwa [hye] at hy
  have haF : π ⟨a, haM⟩ ∈ Ch01.fitting (↥Mstar ⧸ N) :=
    hcomm_fit (hcommmap ▸ Subgroup.mem_map_of_mem π haC)
  have hbF : π ⟨b, hbM⟩ ∈ Ch01.fitting (↥Mstar ⧸ N) :=
    hcomm_fit (hcommmap ▸ Subgroup.mem_map_of_mem π hbC)
  have hord_a : orderOf (π ⟨a, haM⟩) ∣ Nat.card ↥A := by
    refine (orderOf_map_dvd π _).trans ?_
    rw [Subgroup.orderOf_mk]
    have := orderOf_dvd_natCard (⟨a, ha⟩ : ↥A)
    rwa [Subgroup.orderOf_mk] at this
  have hord_b : orderOf (π ⟨b, hbM⟩) ∣ Nat.card ↥B := by
    refine (orderOf_map_dvd π _).trans ?_
    rw [Subgroup.orderOf_mk]
    have := orderOf_dvd_natCard (⟨b, hb⟩ : ↥B)
    rwa [Subgroup.orderOf_mk] at this
  have hcop_ord : Nat.Coprime (orderOf (π ⟨a, haM⟩)) (orderOf (π ⟨b, hbM⟩)) :=
    (hcop.coprime_dvd_left hord_a).coprime_dvd_right hord_b
  have hcommF : Commute (π ⟨a, haM⟩) (π ⟨b, hbM⟩) := by
    have hcop' : Nat.Coprime
        (orderOf (⟨π ⟨a, haM⟩, haF⟩ : ↥(Ch01.fitting (↥Mstar ⧸ N))))
        (orderOf (⟨π ⟨b, hbM⟩, hbF⟩ : ↥(Ch01.fitting (↥Mstar ⧸ N)))) := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]; exact hcop_ord
    have hc := OddOrder.GroupTheory.commute_of_coprime_orderOf_of_isNilpotent
      (L := ↥(Ch01.fitting (↥Mstar ⧸ N))) hcop'
    exact hc.map (Ch01.fitting (↥Mstar ⧸ N)).subtype
  have hker : π ⁅(⟨a, haM⟩ : ↥Mstar), (⟨b, hbM⟩ : ↥Mstar)⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr hcommF
  have hker_eq : π.ker = N := QuotientGroup.ker_mk' N
  have hmemN : ⁅(⟨a, haM⟩ : ↥Mstar), (⟨b, hbM⟩ : ↥Mstar)⁆ ∈ N :=
    hker_eq ▸ (MonoidHom.mem_ker.mpr hker)
  rw [hNdef, Subgroup.mem_subgroupOf] at hmemN
  have hcoe : ((⁅(⟨a, haM⟩ : ↥Mstar), (⟨b, hbM⟩ : ↥Mstar)⁆ : ↥Mstar) : G) = ⁅a, b⁆ := by
    simp [commutatorElement_def]
  rwa [hcoe] at hmemN

/-- **Lemma 13.8 GAP 3 elision (iv)** (mmd L3690): `⁅M_α ∩ M*, Q⁆ ⊆ M*_α`。
BG の理由: `Q ⊆ M*'`、`M*'/M*_α` は nilpotent (Thm 10.2)、`M_α ∩ M*` は `Q`-不変な `q'`-部分群
(`q ∉ α(M) ⟹ q ∤ |M_α|`)。nilpotent quotient + coprime で commutator が radical へ落ちる。

これは BG が "because …" で省略する genuine elision (ChatGPT 再構成プロンプト 3c)。 -/
theorem gap3_commutator_inf_le_Malpha_star [Finite G] (hG : IsMinimalSimpleOdd G)
    {M Mstar : Subgroup G} (_hM : M ∈ maximalSubgroups G) (hMstar : Mstar ∈ maximalSubgroups G)
    {q : ℕ} [Fact q.Prime] {Q : Subgroup G} (hQM : Q ≤ M) (hQMstar : Q ≤ Mstar)
    (hQq : IsPGroup q ↥Q) (hqα : q ∉ S10.alpha M) (hQderivStar : Q ≤ derivedInG Mstar) :
    ⁅S10.Malpha M ⊓ Mstar, Q⁆ ≤ S10.Malpha Mstar := by
  classical
  set D : Subgroup G := S10.Malpha M ⊓ Mstar with hDdef
  have hD_Mα : D ≤ S10.Malpha M := inf_le_left
  have hD_Mstar : D ≤ Mstar := inf_le_right
  -- `M` normalizes `M_α`.
  have hMnorm_Mα : M ≤ Subgroup.normalizer ((S10.Malpha M : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (S10.Malpha_le M)).mp
      (S10.Malpha_subgroupOf_normal M)
  -- `D = M_α ∩ M*` is `Q`-invariant.
  have hQD : Q ≤ Subgroup.normalizer (D : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hgMα := hMnorm_Mα (hQM hg)
    have hgMs := Subgroup.le_normalizer (hQMstar hg)
    rw [hDdef]
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hgMα h).mp h1,
        (Subgroup.mem_normalizer_iff.mp hgMs h).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hgMα h).mpr h1,
        (Subgroup.mem_normalizer_iff.mp hgMs h).mpr h2⟩
  -- `q ∤ |D|` (since `D ≤ M_α`, an `α(M)`-group, and `q ∉ α(M)`).
  have hq_nd_D : ¬ (q ∣ Nat.card ↥D) := by
    intro hdvd
    have hdvdMα : q ∣ Nat.card ↥(S10.Malpha M) := hdvd.trans (Subgroup.card_dvd_of_le hD_Mα)
    exact hqα (S10.Malpha_isPiGroup M q
      (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvdMα, Nat.card_pos.ne'⟩))
  -- coprime `|D|, |Q|`.
  have hcopDQ : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Q) := by
    obtain ⟨k, hk⟩ := hQq.exists_card_eq
    rw [hk]
    exact (((Fact.out : q.Prime).coprime_iff_not_dvd.mpr hq_nd_D).symm).pow_right k
  -- `D ⊔ Q ≤ M*` is solvable.
  have hDQ_le : D ⊔ Q ≤ Mstar := sup_le hD_Mstar hQMstar
  have : Group.IsSolvable ↥Mstar := hG.isSolvable_of_mem_maximalSubgroups hMstar
  have : Group.IsSolvable ↥(D ⊔ Q) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hDQ_le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hDQ_le).surjective
  -- coprime identity `⁅⁅D, Q⁆, Q⁆ = ⁅D, Q⁆`.
  have hid : ⁅⁅D, Q⁆, Q⁆ = ⁅D, Q⁆ :=
    commutator_commutator_right_eq_of_le_normalizer ‹Group.IsSolvable ↥(D ⊔ Q)› hQD hcopDQ
  -- `⁅D, Q⁆ ≤ M*'` (since `D, Q ≤ M*`).
  have heqder : derivedInG Mstar = ⁅(Mstar : Subgroup G), Mstar⁆ :=
    Subgroup.map_subtype_commutator Mstar
  have hL_der : ⁅D, Q⁆ ≤ derivedInG Mstar := by
    rw [heqder]; exact Subgroup.commutator_mono hD_Mstar hQMstar
  -- `⁅D, Q⁆ ≤ D` (`Q`-invariance), so coprime `|⁅D,Q⁆|, |Q|`.
  have hLD : ⁅D, Q⁆ ≤ D := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hyx : y * x⁻¹ * y⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp (hQD hy) x⁻¹).mp (D.inv_mem hx)
    rw [commutatorElement_def]
    have he : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
    rw [he]; exact D.mul_mem hx hyx
  have hcopLQ : Nat.Coprime (Nat.card ↥(⁅D, Q⁆)) (Nat.card ↥Q) :=
    hcopDQ.coprime_dvd_left (Subgroup.card_dvd_of_le hLD)
  -- (iv) core: `⁅⁅D, Q⁆, Q⁆ ≤ M*_α`.
  have h2 : ⁅⁅D, Q⁆, Q⁆ ≤ S10.Malpha Mstar :=
    commutator_le_Malpha_of_coprime_le_derived hG hMstar hL_der hQderivStar hcopLQ
  rw [← hid]; exact h2

/-- **Lemma 13.8 GAP 3 elision (ii)** (mmd L3686): `M = N_M(Q) M_β`, `r ∣ |C_M(P)|`,
`r ∤ |M_β|`, `P ≤ N_M(Q)` のとき `P`-中心化された位数 `r` の `R ≤ N_M(Q)` が存在。

`C_M(P)` の `r`-元 `y` (Cauchy) を `M = (M⊓N_G(Q))·M_β` で `y = h₀·a₀` 分解し、
coprime quotient cover (`coprime_fixedPoints_quotient_of_coprime_normal`, `P` の `↥(M⊓N_G(Q))`
への共役作用 + 正規核 `(M_β).subgroupOf`) で `h₀` を `P`-fixed な `c ∈ C_{N_M(Q)}(P)` へ持ち上げる。
`c ≡ y (mod M_β)` ゆえ `r ∣ orderOf c`、`R = ⟨c^(orderOf c / r)⟩`。 -/
theorem exists_order_r_le_normalizer_centralizer [Finite G]
    {M : Subgroup G} {p : ℕ} [Fact p.Prime] {P : Subgroup G} (hPp : IsPGroup p ↥P)
    (hPM : P ≤ M) {Q : Subgroup G} (hQinv : P ≤ Subgroup.normalizer (Q : Set G))
    (hFrat : M = (M ⊓ Subgroup.normalizer (Q : Set G)) ⊔ S10.Mbeta M)
    (hp_nMβ : ¬ p ∣ Nat.card ↥(S10.Mbeta M)) {r : ℕ} [Fact r.Prime]
    (hrC : r ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (P : Set G)))
    (hr_nMβ : ¬ r ∣ Nat.card ↥(S10.Mbeta M)) (_hsolvM : Group.IsSolvable ↥M) :
    ∃ R : Subgroup G, Nat.card ↥R = r ∧ R ≤ M ⊓ Subgroup.normalizer (Q : Set G)
      ∧ R ≤ Subgroup.centralizer (P : Set G) := by
  classical
  set H : Subgroup G := M ⊓ Subgroup.normalizer (Q : Set G) with hHdef
  have hPH : P ≤ H := le_inf hPM hQinv
  have hH_le_M : H ≤ M := inf_le_left
  -- `P` acts on `G` by conjugation; `H` and `M_β` are `P`-invariant.
  set ψ : ↥P →* MulAut G := MulAut.conj.comp P.subtype with hψ
  have hHinv : OddOrder.Isaacs.Ch03.IsAInvariant ψ H := fun a =>
    Subgroup.conj_smul_eq_self_of_mem (hPH a.2)
  have hMnorm_Mβ : M ≤ Subgroup.normalizer ((S10.Mbeta M : Subgroup G) : Set G) :=
    le_normalizer_opiCoreInG (S10.beta M) M
  have hMβinv : OddOrder.Isaacs.Ch03.IsAInvariant ψ (S10.Mbeta M) := fun a =>
    conj_smul_eq_self_of_mem_normalizer (hMnorm_Mβ (hPM a.2))
  have hN_inv : OddOrder.Isaacs.Ch03.IsAInvariant hHinv.restrict ((S10.Mbeta M).subgroupOf H) :=
    hHinv.subgroupOf hMβinv
  have : ((S10.Mbeta M).subgroupOf H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hH_le_M.trans hMnorm_Mβ)
  -- coprimeness `(|P|, |(M_β).subgroupOf H|) = 1`.
  have hN_card : Nat.card ↥((S10.Mbeta M).subgroupOf H) = Nat.card ↥(S10.Mbeta M ⊓ H) := by
    rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective H.subtype_injective]
  have hN_dvd : Nat.card ↥((S10.Mbeta M).subgroupOf H) ∣ Nat.card ↥(S10.Mbeta M) := by
    rw [hN_card]; exact Subgroup.card_dvd_of_le inf_le_left
  have hCop : Nat.Coprime (Nat.card ↥P) (Nat.card ↥((S10.Mbeta M).subgroupOf H)) := by
    obtain ⟨k, hk⟩ := hPp.exists_card_eq
    rw [hk]
    refine (((Fact.out : p.Prime).coprime_iff_not_dvd.mpr ?_)).pow_left k
    exact fun hpd => hp_nMβ (hpd.trans hN_dvd)
  have : Group.IsSolvable ↥P := by have := hPp.isNilpotent; infer_instance
  have hSolv : Group.IsSolvable ↥P ∨ Group.IsSolvable ↥((S10.Mbeta M).subgroupOf H) := Or.inl ‹_›
  -- Cauchy: an order-`r` element `y ∈ C_M(P)`.
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' r hrC
  set y : G := (y₀ : G) with hy
  have hyMC : y ∈ M ⊓ Subgroup.centralizer (P : Set G) := y₀.2
  have hyM : y ∈ M := (Subgroup.mem_inf.mp hyMC).1
  have hyC : y ∈ Subgroup.centralizer (P : Set G) := (Subgroup.mem_inf.mp hyMC).2
  have hy_ord : orderOf y = r := by
    rw [hy]
    exact (orderOf_injective (M ⊓ Subgroup.centralizer (P : Set G)).subtype
      (M ⊓ Subgroup.centralizer (P : Set G)).subtype_injective y₀).trans hy₀
  -- decompose `y = h₀ · a₀` with `h₀ ∈ H`, `a₀ ∈ M_β` (using `M_β ⊴ M`, inside `↥M`).
  have : ((S10.Mbeta M).subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hMnorm_Mβ
  have hyM' : (⟨y, hyM⟩ : ↥M) ∈ (H.subgroupOf M) ⊔ ((S10.Mbeta M).subgroupOf M) := by
    rw [← Subgroup.subgroupOf_sup hH_le_M (S10.Mbeta_le M), ← hFrat, Subgroup.subgroupOf_self]
    exact Subgroup.mem_top _
  obtain ⟨h', hh', a', ha', hya'⟩ := Subgroup.mem_sup_of_normal_right.mp hyM'
  have hh₀H : (h' : G) ∈ H := Subgroup.mem_subgroupOf.mp hh'
  have ha₀ : (a' : G) ∈ S10.Mbeta M := Subgroup.mem_subgroupOf.mp ha'
  have hya : (h' : G) * (a' : G) = y := by
    have := congrArg (Subtype.val) hya'
    simpa using this
  set h₀ : G := (h' : G) with hh₀eq
  set a₀ : G := (a' : G) with ha₀eq
  set g : ↥H := ⟨h₀, hh₀H⟩ with hg
  -- the coset `g · N` is `P`-fixed.
  have hgfix : ∀ a : ↥P, ∃ n ∈ (S10.Mbeta M).subgroupOf H, (hHinv.restrict a) g = g * n := by
    intro a
    refine ⟨g⁻¹ * (hHinv.restrict a) g, ?_, (mul_inv_cancel_left g _).symm⟩
    refine Subgroup.mem_subgroupOf.mpr ?_
    have hval : ((g⁻¹ * (hHinv.restrict a) g : ↥H) : G) = h₀⁻¹ * ((a : G) * h₀ * (a : G)⁻¹) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hHinv.restrict_apply_val]
      simp [hg, hψ, MulAut.conj_apply]
    rw [hval]
    -- `a · y · a⁻¹ = y` (since `y` centralises `P`).
    have hcent : (a : G) * (h₀ * a₀) = (h₀ * a₀) * (a : G) := by
      have := Subgroup.mem_centralizer_iff.mp hyC (a : G) a.2
      rwa [← hya] at this
    have hconj_y : (a : G) * (h₀ * a₀) * (a : G)⁻¹ = h₀ * a₀ := by
      rw [hcent]; group
    -- `h₀⁻¹ (a h₀ a⁻¹) = a₀ · (a a₀⁻¹ a⁻¹) ∈ M_β`.
    have heq : h₀⁻¹ * ((a : G) * h₀ * (a : G)⁻¹) = a₀ * ((a : G) * a₀⁻¹ * (a : G)⁻¹) := by
      have e1 : (a : G) * h₀ * (a : G)⁻¹
          = ((a : G) * (h₀ * a₀) * (a : G)⁻¹) * ((a : G) * a₀⁻¹ * (a : G)⁻¹) := by group
      rw [e1, hconj_y]; group
    rw [heq]
    refine (S10.Mbeta M).mul_mem ha₀ ?_
    have hsm := hMβinv.smul_mem a ((S10.Mbeta M).inv_mem ha₀)
    have : (ψ a) a₀⁻¹ = (a : G) * a₀⁻¹ * (a : G)⁻¹ := by simp [hψ, MulAut.conj_apply]
    rwa [this] at hsm
  -- lift to a `P`-fixed representative `c`.
  obtain ⟨c, hc_fix, n, hn, hcn⟩ :=
    OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient_of_coprime_normal hCop hSolv hN_inv hgfix
  -- `c ∈ C(P)`.
  have hcC : (c : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hfx := congrArg Subtype.val (hc_fix ⟨x, hx⟩)
    rw [hHinv.restrict_apply_val] at hfx
    have hconj : x * (c : G) * x⁻¹ = (c : G) := by
      simpa only [hψ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conj_apply] using hfx
    calc x * (c : G) = x * (c : G) * x⁻¹ * x := by group
      _ = (c : G) * x := by rw [hconj]
  -- order/`R` construction (c ≡ y mod M_β ⟹ r ∣ orderOf c).
  have hcM : (c : G) ∈ M := hH_le_M c.2
  set cM : ↥M := ⟨(c : G), hcM⟩ with hcMdef
  set yM : ↥M := ⟨y, hyM⟩ with hyMdef
  -- `r ∣ orderOf c`, proved in the quotient `↥M ⧸ (M_β).subgroupOf M`.
  have hr_ord : r ∣ orderOf (c : G) := by
    -- `c ≡ y (mod M_β)`: `c⁻¹ y = n⁻¹ a₀ ∈ M_β`.
    have hcG : (c : G) = h₀ * (n : G) := by
      have := congrArg (Subtype.val) hcn
      simpa [hg] using this
    have hnMβ : (n : G) ∈ S10.Mbeta M := Subgroup.mem_subgroupOf.mp hn
    have hcoset : cM⁻¹ * yM ∈ (S10.Mbeta M).subgroupOf M := by
      rw [Subgroup.mem_subgroupOf]
      have hval : ((cM⁻¹ * yM : ↥M) : G) = (c : G)⁻¹ * y := by simp [hcMdef, hyMdef]
      rw [hval, hcG, ← hya]
      have hgrp : (h₀ * (n : G))⁻¹ * (h₀ * a₀) = (n : G)⁻¹ * a₀ := by group
      rw [hgrp]
      exact (S10.Mbeta M).mul_mem ((S10.Mbeta M).inv_mem hnMβ) ha₀
    have hπ : (QuotientGroup.mk' ((S10.Mbeta M).subgroupOf M)) cM
        = (QuotientGroup.mk' ((S10.Mbeta M).subgroupOf M)) yM := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      exact hcoset
    -- `orderOf (π yM) = r` (`r`-part survives since `r ∤ |M_β|`).
    have hyM_ord : orderOf yM = r := by
      rw [hyMdef]
      exact (orderOf_injective M.subtype M.subtype_injective ⟨y, hyM⟩).symm.trans hy_ord
    have hπy_ne : (QuotientGroup.mk' ((S10.Mbeta M).subgroupOf M)) yM ≠ 1 := by
      rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
      intro hmem
      have hyβ : y ∈ S10.Mbeta M := by
        rw [hyMdef] at hmem; exact Subgroup.mem_subgroupOf.mp hmem
      refine hr_nMβ ?_
      calc r = orderOf y := hy_ord.symm
        _ = orderOf (⟨y, hyβ⟩ : ↥(S10.Mbeta M)) :=
              orderOf_injective (S10.Mbeta M).subtype (S10.Mbeta M).subtype_injective ⟨y, hyβ⟩
        _ ∣ Nat.card ↥(S10.Mbeta M) := orderOf_dvd_natCard _
    have hπy_ord : orderOf ((QuotientGroup.mk' ((S10.Mbeta M).subgroupOf M)) yM) = r := by
      have hdvd : orderOf ((QuotientGroup.mk' ((S10.Mbeta M).subgroupOf M)) yM) ∣ r := by
        rw [← hyM_ord]; exact orderOf_map_dvd _ _
      rcases (Nat.dvd_prime (Fact.out : r.Prime)).mp hdvd with h1 | hr
      · exact absurd (orderOf_eq_one_iff.mp h1) hπy_ne
      · exact hr
    -- transport to `cM`, then to `(c : G)`.
    have hπc_ord : orderOf ((QuotientGroup.mk' ((S10.Mbeta M).subgroupOf M)) cM) = r := by
      rw [hπ]; exact hπy_ord
    have hr_cM : r ∣ orderOf cM := hπc_ord ▸ orderOf_map_dvd _ _
    have hconv : orderOf cM = orderOf (c : G) :=
      (orderOf_injective M.subtype M.subtype_injective cM).symm
    rwa [hconv] at hr_cM
  -- Cauchy inside `⟨c⟩`: an order-`r` element `z`, set `R = ⟨z⟩`.
  have hcard : r ∣ Nat.card ↥(Subgroup.zpowers (c : G)) := by
    rw [Nat.card_zpowers]; exact hr_ord
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' r hcard
  set z : G := (z₀ : G) with hzdef
  have hz_ord : orderOf z = r := by
    rw [hzdef]
    exact (orderOf_injective (Subgroup.zpowers (c : G)).subtype
      (Subgroup.zpowers (c : G)).subtype_injective z₀).trans hz₀
  have hz_mem : z ∈ Subgroup.zpowers (c : G) := z₀.2
  refine ⟨Subgroup.zpowers z, ?_, ?_, ?_⟩
  · rw [Nat.card_zpowers, hz_ord]
  · rw [Subgroup.zpowers_le]
    exact (Subgroup.zpowers_le.mpr c.2) hz_mem
  · rw [Subgroup.zpowers_le]
    exact (Subgroup.zpowers_le.mpr hcC) hz_mem

/-- 可換 (`R ≤ C(P)`) な `π`-部分群 `P, R` の join `P ⊔ R` も `π`-部分群。
可換性から `P, R` は互いに正規化するので `↥(P⊔R)` 内では両者とも正規になり、
`IsPiGroup.sup_of_normal` が適用できる。 -/
private theorem isPiGroup_sup_of_le_centralizer [Finite G] {π : Set ℕ} {P R : Subgroup G}
    (hP : Ch03.Subgroup.IsPiGroup π P) (hR : Ch03.Subgroup.IsPiGroup π R)
    (hcomm : R ≤ Subgroup.centralizer (P : Set G)) :
    Ch03.Subgroup.IsPiGroup π (P ⊔ R) := by
  have hPcR : P ≤ Subgroup.centralizer (R : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (hcomm hy) x hx).symm
  have hPle : P ≤ P ⊔ R := le_sup_left
  have hRle : R ≤ P ⊔ R := le_sup_right
  have : (P.subgroupOf (P ⊔ R)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (sup_le Subgroup.le_normalizer (hcomm.trans (Subgroup.centralizer_le_normalizer _)))
  have : (R.subgroupOf (P ⊔ R)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (sup_le (hPcR.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer)
  have hPpi : Ch03.Subgroup.IsPiGroup π (P.subgroupOf (P ⊔ R)) := by
    intro s hs
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).toEquiv] at hs
    exact hP s hs
  have hRpi : Ch03.Subgroup.IsPiGroup π (R.subgroupOf (P ⊔ R)) := by
    intro s hs
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRle).toEquiv] at hs
    exact hR s hs
  have hsup := Ch03.Subgroup.IsPiGroup.sup_of_normal hPpi hRpi
  rw [← Subgroup.subgroupOf_sup hPle hRle, Subgroup.subgroupOf_self] at hsup
  intro s hs
  apply hsup
  rwa [Nat.card_congr (Subgroup.topEquiv (G := ↥(P ⊔ R))).toEquiv]

/-- **Theorem 13.4 の `E` 外への共役拡張**: `P, R ≤ M` が可換 (`R ≤ C(P)`),
`P ∈ ℰ_p¹` (`p ∈ τ₁(M)`), `R ∈ ℰ_r¹` (`r ∉ σ(M)`) なら `C_{M_σ}(P) ⊆ C_{M_σ}(R)`。

BG Lemma 13.8 の "`PR` is conjugate in `M` to an abelian subgroup of `E`, Theorem 13.4 yields …"。
証明: `PR`（`σ(M)'`-部分群）を Hall 補群 `E` へ `M`-共役 (`exists_conj_smul_le_hallPiece`)、
共役した対に Thm 13.4 を適用、`M_σ ⊴ M` の共役同変性で戻す。 -/
theorem centralizer_msigma_le_of_commute_tau1 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hp : p ∈ tau1 M) (hrσ : r ∉ S10.sigma M)
    {P R : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1) (hR : R ∈ elemAbelianOfRank G r 1)
    (hPM : P ≤ M) (hRM : R ≤ M) (hcomm : R ≤ Subgroup.centralizer (P : Set G)) :
    S10.Msigma M ⊓ Subgroup.centralizer (P : Set G) ≤
      S10.Msigma M ⊓ Subgroup.centralizer (R : Set G) := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  obtain ⟨-, hPcardp⟩ := mem_elemAbelianOfRank.mp hP
  obtain ⟨-, hRcardr⟩ := mem_elemAbelianOfRank.mp hR
  have hPcardp' : Nat.card ↥P = p := by rw [← pow_one p]; exact hPcardp
  have hRcardr' : Nat.card ↥R = r := by rw [← pow_one r]; exact hRcardr
  -- `E` and its `σ'`-Hall structure (`⊤` is a Hall `σ(M)'`-subgroup of `E`).
  obtain ⟨E, E₁, E₂, E₃, hE⟩ := exists_subgroupESetup hG hM
  have hEhall : Ch03.IsHallSubgroup (S10.sigma M)ᶜ (E.subgroupOf E) := by
    rw [Subgroup.subgroupOf_self]
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · apply SubgroupESetup.isPiGroup_sigma_compl hG hE
      rwa [Nat.card_congr (Subgroup.topEquiv (G := ↥E)).toEquiv] at hs
    · rw [Subgroup.index_top, Nat.primeFactors_one] at hs
      simp at hs
  -- `P ⊔ R` is a `σ(M)'`-subgroup of `M`.
  have hp_sigma : p ∈ (S10.sigma M)ᶜ := tau1_subset_sigma_compl M hp
  have hP_pi : Ch03.Subgroup.IsPiGroup (S10.sigma M)ᶜ P := by
    intro s hs
    rw [hPcardp', (Fact.out : p.Prime).primeFactors, Finset.mem_singleton] at hs
    exact hs ▸ hp_sigma
  have hR_pi : Ch03.Subgroup.IsPiGroup (S10.sigma M)ᶜ R := by
    intro s hs
    rw [hRcardr', (Fact.out : r.Prime).primeFactors, Finset.mem_singleton] at hs
    exact hs ▸ (Set.mem_compl_iff _ _).mpr hrσ
  have hPRpi : Ch03.Subgroup.IsPiGroup (S10.sigma M)ᶜ ((P ⊔ R).subgroupOf M) := by
    intro s hs
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le hPM hRM)).toEquiv] at hs
    exact isPiGroup_sup_of_le_centralizer hP_pi hR_pi hcomm s hs
  -- conjugate `P ⊔ R` into `E` by some `w ∈ M`.
  obtain ⟨w, hwM, hwle⟩ :=
    exists_conj_smul_le_hallPiece hG hE le_rfl hEhall (subset_refl _) (sup_le hPM hRM) hPRpi
  have hPwE : (MulAut.conj w • P : Subgroup G) ≤ E :=
    (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr le_sup_left).trans hwle
  have hRwE : (MulAut.conj w • R : Subgroup G) ≤ E :=
    (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr le_sup_right).trans hwle
  -- conjugated data for Theorem 13.4.
  have hPw_mem : (MulAut.conj w • P : Subgroup G) ∈ elemAbelianOfRank G p 1 :=
    conj_smul_mem_elemAbelianOfRank w hP
  have hRw_mem : (MulAut.conj w • R : Subgroup G) ∈ elemAbelianOfRank G r 1 :=
    conj_smul_mem_elemAbelianOfRank w hR
  have hRw_comm : (MulAut.conj w • R : Subgroup G) ≤
      Subgroup.centralizer ((MulAut.conj w • P : Subgroup G) : Set G) := by
    rw [← centralizer_conj_smul]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hcomm
  have hr_pf : r ∈ (Nat.card ↥E).primeFactors := by
    have hRw_card : Nat.card ↥(MulAut.conj w • R : Subgroup G) = r := by
      rw [← pow_one r]; exact (mem_elemAbelianOfRank.mp hRw_mem).2
    refine Nat.mem_primeFactors.mpr ⟨Fact.out, ?_, Nat.card_pos.ne'⟩
    rw [← hRw_card]; exact Subgroup.card_dvd_of_le hRwE
  -- Theorem 13.4 on the conjugated pair.
  have hT134 : S10.Msigma M ⊓ Subgroup.centralizer ((MulAut.conj w • P : Subgroup G) : Set G) ≤
      S10.Msigma M ⊓ Subgroup.centralizer ((MulAut.conj w • R : Subgroup G) : Set G) :=
    centralizer_le_centralizer_of_tau1 hG hE hp hr_pf hPw_mem hPwE hRw_mem (le_inf hRwE hRw_comm)
  -- transfer back by `conj w⁻¹` (`M_σ` is `M`-invariant).
  have hMnorm : M ≤ Subgroup.normalizer ((S10.Msigma M : Subgroup G) : Set G) := by
    rw [S10.Msigma]; exact le_normalizer_opiCoreInG (S10.sigma M) M
  have hMσfix : MulAut.conj w⁻¹ • S10.Msigma M = S10.Msigma M :=
    conj_smul_eq_self_of_mem_normalizer (hMnorm (M.inv_mem hwM))
  have hPback : MulAut.conj w⁻¹ • (MulAut.conj w • P) = P := by
    rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hRback : MulAut.conj w⁻¹ • (MulAut.conj w • R) = R := by
    rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have key := (Subgroup.pointwise_smul_le_pointwise_smul_iff
    (a := MulAut.conj w⁻¹)).mpr hT134
  rw [Subgroup.smul_inf, Subgroup.smul_inf, hMσfix, centralizer_conj_smul,
    centralizer_conj_smul, hPback, hRback] at key
  exact key

/-- **Lemma 13.8 GAP 3 elision (ii)+(iii)** (mmd L3686): `C_{M_α}(P) ⊆ M*`。
BG の理由: `M = N_M(Q) M_α` と `r ∣ |C_M(P)|`, `r ∉ σ(M)` から `P`-中心化された位数 `r` の
`R ⊆ N_M(Q)` が存在 (coprime action; (ii))、`R ⊆ N_G(Q) ⊆ M*` かつ `N_G(R) ⊆ M*` (Prop 10.14d)。
`PR` は `M` 内で `E` の可換部分群に共役ゆえ Thm 13.4 で
`1 ⊂ X = C_{M_σ}(P) ⊆ C_{M_σ}(R) ⊆ C_G(R) ⊆ N_G(R) ⊆ M*` (iii)。`X = C_{M_α}(P) ⊆ C_{M_σ}(P)`。

genuine elision (ChatGPT 再構成プロンプト 3a/3b)。 -/
theorem gap3_centralizer_Malpha_P_le_Mstar [Finite G] (hG : IsMinimalSimpleOdd G)
    {M Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hMstar : Mstar ∈ maximalSubgroups G)
    {p : ℕ} [Fact p.Prime] (hp : p ∈ tau1 M) {P : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1)
    (hPM : P ≤ M) {Q : Subgroup G} (_hQM : Q ≤ M)
    (hQinv : P ≤ Subgroup.normalizer (Q : Set G)) (hNQ : Subgroup.normalizer (Q : Set G) ≤ Mstar)
    (_hαβ : S10.alpha M = S10.beta M)
    (hFrat : M = (M ⊓ Subgroup.normalizer (Q : Set G)) ⊔ S10.Mbeta M)
    {r : ℕ} [Fact r.Prime] (hrβ : r ∈ S10.beta Mstar)
    (hrC : r ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (P : Set G))) (hrσ : r ∉ S10.sigma M) :
    S10.Malpha M ⊓ Subgroup.centralizer (P : Set G) ≤ Mstar := by
  classical
  obtain ⟨hPea, -⟩ := mem_elemAbelianOfRank.mp hP
  have hPp : IsPGroup p ↥P := hPea.isPGroup
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  -- `p, r ∉ σ(M)`, hence `∉ β(M)`, hence `∤ |M_β|`.
  have hpσ : p ∉ S10.sigma M := tau1_subset_sigma_compl M hp
  have hp_nMβ : ¬ p ∣ Nat.card ↥(S10.Mbeta M) := fun hpd =>
    hpσ (S10.alpha_subset_sigma hG hM (S10.beta_subset_alpha M
      (S10.Mbeta_isPiGroup M p (Nat.mem_primeFactors.mpr ⟨Fact.out, hpd, Nat.card_pos.ne'⟩))))
  have hr_nMβ : ¬ r ∣ Nat.card ↥(S10.Mbeta M) := fun hrd =>
    hrσ (S10.alpha_subset_sigma hG hM (S10.beta_subset_alpha M
      (S10.Mbeta_isPiGroup M r (Nat.mem_primeFactors.mpr ⟨Fact.out, hrd, Nat.card_pos.ne'⟩))))
  -- (ii): an order-`r` subgroup `R ≤ N_M(Q)` centralized by `P` (coprime action).
  obtain ⟨R, hRcard, hRNQ, hRC⟩ :=
    exists_order_r_le_normalizer_centralizer hPp hPM hQinv hFrat hp_nMβ hrC hr_nMβ ‹Group.IsSolvable
        ↥M›
  have hRM : R ≤ M := hRNQ.trans inf_le_left
  have hRMstar : R ≤ Mstar := (hRNQ.trans inf_le_right).trans hNQ
  have hRne : R ≠ ⊥ := by
    intro hb; rw [hb, Subgroup.card_bot] at hRcard
    exact (Fact.out : r.Prime).one_lt.ne hRcard
  have hRr : IsPGroup r ↥R := IsPGroup.of_card (by rw [hRcard, pow_one])
  have hRmem : R ∈ elemAbelianOfRank G r 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hRcard, by rw [hRcard, pow_one]⟩
  -- (iii) `N_G(R) ⊆ M*` (Prop 10.14(d): `R` a nonidentity `β(M*)`-subgroup of `M*`).
  have hNGR : Subgroup.normalizer (R : Set G) ≤ Mstar :=
    S10.normalizer_le_of_nontrivial_beta_subgroup hG hMstar hRMstar hRne
      (Subgroup.isPiSubgroup_of_isPGroup_of_mem hRr hrβ)
  -- (iii) chain: `M_α ⊓ C(P) ≤ M_σ ⊓ C(P) ≤ M_σ ⊓ C(R) ≤ C(R) ≤ N_G(R) ≤ M*`.
  have h134 := centralizer_msigma_le_of_commute_tau1 hG hM hp hrσ hP hRmem hPM hRM hRC
  exact (inf_le_inf_right (Subgroup.centralizer (P : Set G)) (S10.Malpha_le_Msigma hG hM)).trans
    (h134.trans (inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans hNGR)))

/-- **Lemma 13.8 GAP 3 capstone (M-oriented)**: 配置 + step1 出力 (`α=β`, `C_{M_α}(P)≠1`,
`C_{M_α}(PQ)=1`) + GAP 2 の `r` (`r∈β(M*)`, `r∣|C_M(P)|`, `r∉σ(M)`) から矛盾。

GAP 3 本体: (i) Frattini `M=N_M(Q)M_β` (α=β で M_β 機構)、(ii) coprime で `R⊆N_M(Q)` 位数 `r`
`P`-中心化、(iii) `PR` を Hall `E` へ共役 + Thm 13.4 で `X=C_{M_α}(P)⊆C_{M_σ}(R)⊆M*`、
(iv) nilpotent で `[M_α∩M*,Q]⊆M*_α` → `gap3_assembly`。

本体 `forbidden_config_impossible` は GAP 2 の disjunction の各 disjunct に M↔M* を入替えて適用。 -/
theorem gap3_false_from_r [Finite G] (hG : IsMinimalSimpleOdd G)
    {M Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hMstar : Mstar ∈ maximalSubgroups G)
    (hnc : ¬ ∃ g : G, MulAut.conj g • M = Mstar) {p : ℕ} [Fact p.Prime] (hp : p ∈ tau1 M)
    {P : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1) (hPMM : P ≤ M ⊓ Mstar)
    {q : ℕ} [Fact q.Prime] {Q : Subgroup G} (hQle : Q ≤ M ⊓ Mstar) (hQq : IsPGroup q ↥Q)
    (hQmax : ∀ T : Subgroup G, T ≤ M ⊓ Mstar → IsPGroup q ↥T → Q ≤ T → Q = T)
    (hQinv : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : Q ⊓ Subgroup.centralizer (P : Set G) = ⊥)
    (hNQ : Subgroup.normalizer (Q : Set G) ≤ Mstar)
    (hqp : q ≠ p) (hqα : q ∉ S10.alpha M) (hαβ : S10.alpha M = S10.beta M)
    (hCMαP : S10.Malpha M ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥)
    (hCMαPQ : S10.Malpha M ⊓ Subgroup.centralizer ((P ⊔ Q : Subgroup G) : Set G) = ⊥)
    {r : ℕ} [Fact r.Prime] (hrβ : r ∈ S10.beta Mstar)
    (hrC : r ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (P : Set G))) (hrσ : r ∉ S10.sigma M) :
    False := by
  classical
  have hPM : P ≤ M := hPMM.trans inf_le_left
  have hPMstar : P ≤ Mstar := hPMM.trans inf_le_right
  have hQM : Q ≤ M := hQle.trans inf_le_left
  have hQMstar : Q ≤ Mstar := hQle.trans inf_le_right
  obtain ⟨hPea, hPcard1⟩ := mem_elemAbelianOfRank.mp hP
  have hPp : IsPGroup p ↥P := hPea.isPGroup
  have : Group.IsSolvable ↥P := Group.isSolvable_of_comm hPea.comm
  -- `Q` is a maximal `q`-subgroup of `M` (GAP 1.3).
  have hQmaxM : ∀ T : Subgroup G, T ≤ M → IsPGroup q ↥T → Q ≤ T → Q = T := by
    intro T hTM hTq hQT
    by_contra hne
    have hlt : Q < T := lt_of_le_of_ne hQT hne
    have hgrow := lt_inf_normalizer_of_lt_of_pgroup hTq hlt
    have hNT_le : T ⊓ Subgroup.normalizer (Q : Set G) ≤ M ⊓ Mstar :=
      le_inf (inf_le_left.trans hTM) (inf_le_right.trans hNQ)
    exact hgrow.ne (hQmax _ hNT_le (hTq.to_le inf_le_left) hgrow.le)
  -- `Q = [Q,P] ⊆ M' ∩ M*'`.
  have hcop : Nat.Coprime (Nat.card ↥P) (Nat.card ↥Q) :=
    IsPGroup.coprime_card_of_ne p q (Ne.symm hqp) P Q hPp hQq
  have hQderiv : Q ≤ derivedInG M ⊓ derivedInG Mstar :=
    pSubgroup_le_derived_inf hQinv hcop hCQ hPM hQM hPMstar hQMstar
  have hqβ : q ∉ S10.beta M := fun h => hqα (hαβ.symm ▸ h)
  -- `M = N_M(Q) · M_β` (head Frattini).
  have hFrat : M = (M ⊓ Subgroup.normalizer (Q : Set G)) ⊔ S10.Mbeta M :=
    M_eq_normalizer_sup_Mbeta hG hM hQM hQq hQmaxM hqβ (hQderiv.trans inf_le_left)
  -- (ii)+(iii): `X = C_{M_α}(P) ⊆ M*`.
  have hXMstar : S10.Malpha M ⊓ Subgroup.centralizer (P : Set G) ≤ Mstar :=
    gap3_centralizer_Malpha_P_le_Mstar hG hM hMstar hp hP hPM hQM hQinv hNQ hαβ hFrat hrβ hrC hrσ
  -- `X ⊆ M_α ∩ M*`.
  have hXinf : S10.Malpha M ⊓ Subgroup.centralizer (P : Set G) ≤ S10.Malpha M ⊓ Mstar :=
    le_inf inf_le_left hXMstar
  -- (iv): `⁅M_α ∩ M*, Q⁆ ⊆ M*_α`.
  have hivQ : ⁅S10.Malpha M ⊓ Mstar, Q⁆ ≤ S10.Malpha Mstar :=
    gap3_commutator_inf_le_Malpha_star hG hM hMstar hQM hQMstar hQq hqα (hQderiv.trans inf_le_right)
  -- `⁅X, Q⁆ ⊆ M*_α`.
  have hXQ : ⁅S10.Malpha M ⊓ Subgroup.centralizer (P : Set G), Q⁆ ≤ S10.Malpha Mstar :=
    (Subgroup.commutator_mono hXinf le_rfl).trans hivQ
  -- `M_α ∩ M*_α = ⊥` (Lemma 10.12, via `M_α ⊓ M*_σ = ⊥`).
  have hMαMstarα : S10.Malpha M ⊓ S10.Malpha Mstar = ⊥ := by
    have h1 : S10.Malpha M ⊓ S10.Msigma Mstar = ⊥ :=
      (S10.disjoint_of_not_conj hG hM hMstar hnc).1.1
    have h2 : S10.Malpha M ⊓ S10.Malpha Mstar ≤ S10.Malpha M ⊓ S10.Msigma Mstar :=
      inf_le_inf_left _ (S10.Malpha_le_Msigma hG hMstar)
    exact le_bot_iff.mp (h1 ▸ h2)
  exact gap3_assembly hQM hCMαP hXQ hMαMstarα hCMαPQ

/-- **BG Lemma 13.8** (mmd L3630): 次の配置は不可能 — `M*∈ℳ` (`M`と非共役),
`p∈τ₁(M)∩τ₁(M*)`, `P∈ℰ_p¹(M∩M*)`, `Q,Q*` を `M∩M*` の `P`-不変 Sylow 部分群
(素数は異なってよい), `C_Q(P)=C_{Q*}(P)=1`, `N_G(Q)⊆M*`, `N_G(Q*)⊆M`。

§10 gates visible for proof-fill: Theorem 10.2's `M'/M_α` nilpotence tail,
`S10.disjoint_of_not_conj` (Lemma 10.12), and
`S10.normalizer_le_of_nontrivial_beta_subgroup` (Prop 10.14(d)). The Hall/Frattini pieces
used through §12 must remain upstream theorem calls, not new hypotheses on this statement. -/
theorem forbidden_config_impossible [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroups G) (hnc : ¬ ∃ g : G, MulAut.conj g • M = Mstar)
    {p : ℕ} [Fact p.Prime] (hp : p ∈ tau1 M) (hpstar : p ∈ tau1 Mstar)
    {P : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1) (hPM : P ≤ M ⊓ Mstar)
    {q qstar : ℕ} [Fact q.Prime] [Fact qstar.Prime] {Q Qstar : Subgroup G}
    (hQle : Q ≤ M ⊓ Mstar) (hQq : IsPGroup q ↥Q)
    (hQmax : ∀ T : Subgroup G, T ≤ M ⊓ Mstar → IsPGroup q ↥T → Q ≤ T → Q = T)
    (hQstarle : Qstar ≤ M ⊓ Mstar) (hQstarq : IsPGroup qstar ↥Qstar)
    (hQstarmax : ∀ T : Subgroup G, T ≤ M ⊓ Mstar → IsPGroup qstar ↥T → Qstar ≤ T → Qstar = T)
    (hQinv : P ≤ Subgroup.normalizer (Q : Set G))
    (hQstarinv : P ≤ Subgroup.normalizer (Qstar : Set G))
    (hCQ : Q ⊓ Subgroup.centralizer (P : Set G) = ⊥)
    (hCQstar : Qstar ⊓ Subgroup.centralizer (P : Set G) = ⊥)
    (hNQ : Subgroup.normalizer (Q : Set G) ≤ Mstar)
    (hNQstar : Subgroup.normalizer (Qstar : Set G) ≤ M) :
    False := by
  have hMMstar : M ≠ Mstar := fun h => hnc ⟨1, by rw [h, map_one, one_smul]⟩
  have hP1 : P ≠ ⊥ := by
    intro hb
    have hc := (mem_elemAbelianOfRank.mp hP).2
    rw [hb, Subgroup.card_bot, pow_one] at hc
    exact (Fact.out : Nat.Prime p).one_lt.ne hc
  -- step1 (M-side and M*-side).
  obtain ⟨hqp, _, hαβ, _, hqα, hCMαP, hCMαPQ⟩ :=
    forbidden_config_step1 hG hM hMstar hMMstar hp hP hPM hQle hQq hQmax hQinv hCQ
      hNQ
  have hPMstar : P ≤ Mstar ⊓ M := by rw [inf_comm]; exact hPM
  have hQstarle' : Qstar ≤ Mstar ⊓ M := by rw [inf_comm]; exact hQstarle
  have hQstarmax' : ∀ T : Subgroup G, T ≤ Mstar ⊓ M → IsPGroup qstar ↥T → Qstar ≤ T → Qstar = T :=
      by
    intro T hT hTq hQT; rw [inf_comm] at hT; exact hQstarmax T hT hTq hQT
  obtain ⟨hqpstar, _, hαβstar, _, hqαstar, hCMstarαP, hCMstarαPQ⟩ :=
    forbidden_config_step1 hG hMstar hM (Ne.symm hMMstar) hpstar hP hPMstar hQstarle' hQstarq
      hQstarmax' hQstarinv hCQstar hNQstar
  -- `nc` symmetry for the M*-oriented branch.
  have hnc' : ¬ ∃ g : G, MulAut.conj g • Mstar = M := by
    rintro ⟨g, hg⟩
    exact hnc ⟨g⁻¹, by rw [← hg, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]⟩
  -- GAP 2: extract `r`.
  rcases exists_prime_betastar_dvd_or hG hM hMstar hnc hP1 hαβ hαβstar hCMαP hCMstarαP with
    ⟨r, hrp, hrβ, hrC, hrσ⟩ | ⟨r, hrp, hrβ, hrC, hrσ⟩
  · have : Fact r.Prime := ⟨hrp⟩
    exact gap3_false_from_r hG hM hMstar hnc hp hP hPM hQle hQq hQmax hQinv hCQ hNQ
      hqp hqα hαβ hCMαP hCMαPQ hrβ hrC hrσ
  · have : Fact r.Prime := ⟨hrp⟩
    exact gap3_false_from_r hG hMstar hM hnc' hpstar hP hPMstar hQstarle' hQstarq
      hQstarmax' hQstarinv hCQstar hNQstar hqpstar hqαstar hαβstar hCMstarαP hCMstarαPQ hrβ hrC hrσ

/-- `q ∈ σ(M)` なら `M_σ` の `q`-part は `M` のそれに等しい: `M_σ` は `M` の Hall `σ(M)`-部分群
(`Msigma_subgroupOf_isHall`) なので `q ∈ σ(M)` は指数を割らず、`v_q(|M|) = v_q(|M_σ|)`。
⟹ `M_σ` の Sylow `q`-部分群は `M` (そして `G`) の Sylow `q`-部分群。 -/
theorem factorization_Msigma_eq_of_mem_sigma [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {q : ℕ} (hqσ : q ∈ S10.sigma M) :
    (Nat.card ↥(S10.Msigma M)).factorization q = (Nat.card ↥M).factorization q := by
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors ((S10.mem_sigma_iff M q).mp hqσ).1
  have hHall := S10.Msigma_subgroupOf_isHall hG hM
  have hcardMσ : Nat.card ↥((S10.Msigma M).subgroupOf M) = Nat.card ↥(S10.Msigma M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (S10.Msigma_le M)).toEquiv
  have hidx_ne : ((S10.Msigma M).subgroupOf M).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcard_ne : Nat.card ↥((S10.Msigma M).subgroupOf M) ≠ 0 := Nat.card_pos.ne'
  have hqidx : ¬ q ∣ ((S10.Msigma M).subgroupOf M).index := fun hd =>
    hHall.2 q (Nat.mem_primeFactors.mpr ⟨hqprime, hd, hidx_ne⟩) hqσ
  have hmul := Subgroup.card_mul_index ((S10.Msigma M).subgroupOf M)
  calc (Nat.card ↥(S10.Msigma M)).factorization q
      = (Nat.card ↥((S10.Msigma M).subgroupOf M)).factorization q := by rw [hcardMσ]
    _ = (Nat.card ↥M).factorization q := by
        rw [← hmul, Nat.factorization_mul hcard_ne hidx_ne, Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd hqidx, add_zero]

/-- `q ∈ σ(M)` なら `M` の `q`-part は `G` のそれに等しい: `q∈σ(M)` の Sylow `q` of `M` は
`G` の Sylow `q` (`isSylow_sylowMap_of_mem_sigma`)、ゆえ `q^{v_q(|M|)} = q^{v_q(|G|)}`。 -/
theorem factorization_M_eq_G_of_mem_sigma [Finite G] {M : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hqσ : q ∈ S10.sigma M) :
    (Nat.card ↥M).factorization q = (Nat.card G).factorization q := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow q ↥M))
  obtain ⟨SG, hSG⟩ := S10.isSylow_sylowMap_of_mem_sigma hqσ P
  have e1 : Nat.card ↥(SG : Subgroup G) = q ^ (Nat.card ↥M).factorization q := by
    rw [hSG, Subgroup.card_map_of_injective M.subtype_injective]; exact P.card_eq_multiplicity
  have e2 : Nat.card ↥(SG : Subgroup G) = q ^ (Nat.card G).factorization q :=
      SG.card_eq_multiplicity
  exact Nat.pow_right_injective (Fact.out : q.Prime).two_le (e1.symm.trans e2)

/-- **σ-Sylow uniqueness for `M_σ`-Sylows** (Prop 10.14-flavoured): `q ∈ σ(M)`, `S ≤ M_σ` with
`|S| = q^{v_q(|M_σ|)}` (a Sylow `q` of `M_σ`) ⟹ `N_G(S) ⊆ M`. `S.subgroupOf M` is a Sylow `q` of
`M` (card `= q^{v_q(|M|)}` by the `v_q` equality), and `normalizer_sylow_map_le_of_mem_sigma`
(no normalizer growth out of `M` for `σ`-Sylows) gives `N_G(S) ⊆ M`. -/
theorem normalizer_einvariant_sylow_le [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {q : ℕ} [Fact q.Prime] (hqσ : q ∈ S10.sigma M)
    {S : Subgroup G} (hSMσ : S ≤ S10.Msigma M)
    (hScard : Nat.card ↥S = q ^ (Nat.card ↥(S10.Msigma M)).factorization q) :
    Subgroup.normalizer (S : Set G) ≤ M := by
  have hSM : S ≤ M := hSMσ.trans (S10.Msigma_le M)
  have hcardSM : Nat.card ↥(S.subgroupOf M) = q ^ (Nat.card ↥M).factorization q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv, hScard,
      factorization_Msigma_eq_of_mem_sigma hG hM hqσ]
  set PM : Sylow q ↥M := Sylow.ofCard (S.subgroupOf M) hcardSM with hPMdef
  have hmap : (PM : Subgroup ↥M).map M.subtype = S := by
    rw [Sylow.coe_ofCard, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSM]
  rw [← hmap]
  exact S10.normalizer_sylow_map_le_of_mem_sigma hqσ PM

/-- フル `q`-part を持つ `q`-部分群は極大 `q`-部分群: `S ≤ N`, `|S| = q^{v_q(|N|)}` で `S ≤ T ≤ N`
が `q`-群なら `S = T` (`|T| = q^k ∣ |N| ⟹ k ≤ v_q(|N|) ⟹ |T| ≤ |S|`, `S ≤ T` と合わせて等しい)。 -/
theorem eq_of_le_of_isPGroup_card_eq_factorization [Finite G] {q : ℕ} [Fact q.Prime]
    {N S T : Subgroup G} (hScard : Nat.card ↥S = q ^ (Nat.card ↥N).factorization q)
    (hTN : T ≤ N) (hTq : IsPGroup q ↥T) (hST : S ≤ T) : S = T := by
  obtain ⟨k, hk⟩ := hTq.exists_card_eq
  have hN0 : Nat.card ↥N ≠ 0 := Nat.card_pos.ne'
  have hdvd : q ^ k ∣ Nat.card ↥N := by rw [← hk]; exact Subgroup.card_dvd_of_le hTN
  have hkle : k ≤ (Nat.card ↥N).factorization q :=
    (Nat.Prime.pow_dvd_iff_le_factorization (Fact.out : q.Prime) hN0).mp hdvd
  have hTleS : Nat.card ↥T ≤ Nat.card ↥S := by
    rw [hk, hScard]; exact Nat.pow_le_pow_right (Fact.out : q.Prime).pos hkle
  exact Subgroup.eq_of_le_of_card_ge hST hTleS

end OddOrder.BG.Ch3.S13


