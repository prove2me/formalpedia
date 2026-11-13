-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S11_MsigmaANormal
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S11_MsigmaANormal
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:19:21.283084+00:00
-- url     : https://prove2.me/theorems/d0c53b3c-a94e-410b-8efc-e4cb1965e36d
-- title:
--   BG Theorem 11.7: $M_\sigma A\trianglelefteq M$
-- statement:
--   Formalizes Theorem 11.7 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §11, the climax of the section: $M_\sigma A\trianglelefteq M$. It is a single-theorem leaf consuming Hypothesis 11.1, Theorem 11.5 and Corollary 11.6 from the exceptional-maximal-subgroup file, with $E$ a complement of $M_\sigma$ in $M$ containing $A$ obtained from Schur–Zassenhaus.
--
--   The main declaration: `of_sylow`, a change of Sylow subgroup for `Hypothesis111`: Hypothesis 11.1 also holds for another Sylow $p$-subgroup $P'$ containing $A$.
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S11_MsigmaANormal.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S11_MsigmaANormal.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S11_ExceptionalMaximal
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S05b_Thm420Hall
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_Main

namespace OddOrder.BG.Ch3.S11

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

/-- `p`-極大性の relindex 判定: `X ≤ M` が `p`-群で `p ∤ [M : X]` なら、`X` と `M` に
挟まれた `p`-群は `X` 自身 (BG では「`X` は `M` の Sylow `p`-部分群」)。`[X:R]`-鎖が
`p`-冪かつ `p`-free な `[M:X]` を割ることから従う。 -/
private theorem eq_of_le_of_isPGroup_of_not_dvd_relIndex [Finite G] {p : ℕ} [Fact p.Prime]
    {X M : Subgroup G} (hndvd : ¬ p ∣ X.relIndex M) :
    ∀ R : Subgroup G, X ≤ R → R ≤ M → IsPGroup p ↥R → R = X := by
  intro R hXR hRM hRpg
  have hchain : X.relIndex R * R.relIndex M = X.relIndex M :=
    Subgroup.relIndex_mul_relIndex (hHK := hXR) (hKL := hRM)
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hRpg
  have hdvd_pow : X.relIndex R ∣ p ^ j := by
    rw [← hj]
    exact Subgroup.index_dvd_card (X.subgroupOf R)
  have h1 : X.relIndex R = 1 := by
    rcases (Nat.dvd_prime_pow Fact.out).mp hdvd_pow with ⟨k, -, hk⟩
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simpa using hk
    · exfalso
      apply hndvd
      calc p ∣ p ^ k := dvd_pow_self p hkpos.ne'
        _ = X.relIndex R := hk.symm
        _ ∣ X.relIndex M := ⟨R.relIndex M, hchain.symm⟩
  exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hXR

/-- 可換 `A = A₁ ⊔ A₂` の commutator 分配: `A` が abelian で `Q₀` を正規化するとき
`⁅Q₀, A⁆ ≤ ⁅Q₀, A₁⁆ ⊔ ⁅Q₀, A₂⁆`。生成元の分解 `⁅x, ab⁆ = ⁅x,a⁆ · (a⁅x,b⁆a⁻¹)` と
`a⁅x,b⁆a⁻¹ = ⁅axa⁻¹, b⁆` (`A` abelian) を部分群化した induction で示す。 -/
private theorem commutator_le_sup_of_abelian {Q₀ A A₁ A₂ : Subgroup G}
    (hA_comm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hsup : A₁ ⊔ A₂ = A)
    (hnorm : A ≤ Subgroup.normalizer (Q₀ : Set G)) :
    ⁅Q₀, A⁆ ≤ ⁅Q₀, A₁⁆ ⊔ ⁅Q₀, A₂⁆ := by
  have hA₁A : A₁ ≤ A := hsup ▸ le_sup_left
  have hA₂A : A₂ ≤ A := hsup ▸ le_sup_right
  set R : Subgroup G := ⁅Q₀, A₁⁆ ⊔ ⁅Q₀, A₂⁆ with hRdef
  -- conjugation of `Q₀` by elements of `A`.
  have hconjQ : ∀ a ∈ A, ∀ x ∈ Q₀, a * x * a⁻¹ ∈ Q₀ := fun a ha x hx =>
    (Subgroup.mem_normalizer_iff.mp (hnorm ha) x).mp hx
  -- the elements of `A` whose commutators with `Q₀` all land in `R` form a subgroup.
  set SG : Subgroup G :=
    { carrier := {a : G | a ∈ A ∧ ∀ x ∈ Q₀, ⁅x, a⁆ ∈ R}
      one_mem' := ⟨A.one_mem, fun x _ => by
        rw [commutatorElement_def]
        simp⟩
      mul_mem' := by
        rintro a b ⟨haA, haP⟩ ⟨hbA, hbP⟩
        refine ⟨A.mul_mem haA hbA, fun x hx => ?_⟩
        have hkey : ⁅x, a * b⁆ = ⁅x, a⁆ * (⁅a * x * a⁻¹, a * b * a⁻¹⁆) := by
          simp only [commutatorElement_def]
          group
        rw [hkey, hA_comm a haA b hbA, mul_inv_cancel_right]
        exact R.mul_mem (haP x hx) (hbP _ (hconjQ a haA x hx))
      inv_mem' := by
        rintro a ⟨haA, haP⟩
        refine ⟨A.inv_mem haA, fun x hx => ?_⟩
        have hxa : a⁻¹ * x * a ∈ Q₀ := by
          have := hconjQ a⁻¹ (A.inv_mem haA) x hx
          simpa using this
        have hkey : ⁅x, a⁻¹⁆ = (⁅a⁻¹ * x * a, a⁆)⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [hkey]
        exact R.inv_mem (haP _ hxa) } with hSGdef
  have hA₁_le : A₁ ≤ SG := fun a ha =>
    ⟨hA₁A ha, fun x hx => Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hx ha)⟩
  have hA₂_le : A₂ ≤ SG := fun a ha =>
    ⟨hA₂A ha, fun x hx => Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hx ha)⟩
  have hA_le : A ≤ SG := hsup ▸ sup_le hA₁_le hA₂_le
  rw [Subgroup.commutator_le]
  intro x hx a ha
  exact (hA_le ha).2 x hx

/-- `A`-不変 Sylow の相対指数: `IsAInvSylowIn q A Q H` なら `q ∤ [H : Q]`
(`Q.subgroupOf H` が `↥H` の Sylow `q`-部分群になることの移送)。 -/
private theorem not_dvd_relIndex_of_isAInvSylowIn [Finite G] {q : ℕ} [Fact q.Prime]
    {A Q H : Subgroup G} (h : IsAInvSylowIn q A Q H) : ¬ q ∣ Q.relIndex H := by
  have hmax : ∀ {R : Subgroup ↥H}, IsPGroup q ↥R → Q.subgroupOf H ≤ R → R = Q.subgroupOf H := by
    intro R hRpg hQR
    have hmap : R.map H.subtype = Q := by
      refine h.2.2.2 _ ?_ (Subgroup.map_subtype_le _) (hRpg.map H.subtype)
      rw [← Subgroup.map_subgroupOf_eq_of_le h.1]
      exact Subgroup.map_mono hQR
    rw [← hmap, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  exact (⟨Q.subgroupOf H, h.2.1.comap_subtype, hmax⟩ : Sylow q ↥H).not_dvd_index

/-- 巡回群では位数 `q` の元の生成する部分群が `{g | g ^ q = 1}` 全体を吸収する
(`IsCyclic.card_pow_eq_one_le` の計数比較)。BG Thm 11.7 では「`Q` cyclic なら位数 `q` の
中心化元が `Ω₁(Q)` を張り `A` の作用が消える」段で使う。 -/
private theorem mem_zpowers_of_pow_prime_eq_one {Q : Type*} [Group Q] [Finite Q]
    [IsCyclic Q] {q : ℕ} (hq : q.Prime) {y : Q} (hy : orderOf y = q)
    {g : Q} (hg : g ^ q = 1) : g ∈ Subgroup.zpowers y := by
  classical
  have := Fintype.ofFinite Q
  have hsub : ((Subgroup.zpowers y : Subgroup Q) : Set Q).toFinset ⊆
      ({a : Q | a ^ q = 1} : Finset Q) := by
    intro a ha
    rw [Set.mem_toFinset] at ha
    obtain ⟨n, rfl⟩ := ha
    have : (y ^ q) ^ n = 1 := by
      rw [← hy, pow_orderOf_eq_one, one_zpow]
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    exact this
  have hcard_z : ((Subgroup.zpowers y : Subgroup Q) : Set Q).toFinset.card = q := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, SetLike.coe_sort_coe,
      Nat.card_zpowers, hy]
  have hcard_le : ({a : Q | a ^ q = 1} : Finset Q).card ≤ q :=
    IsCyclic.card_pow_eq_one_le hq.pos
  have heq : ((Subgroup.zpowers y : Subgroup Q) : Set Q).toFinset
      = ({a : Q | a ^ q = 1} : Finset Q) :=
    Finset.eq_of_subset_of_card_le hsub (hcard_le.trans_eq hcard_z.symm)
  have hg_mem : g ∈ ({a : Q | a ^ q = 1} : Finset Q) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hg⟩
  rw [← heq, Set.mem_toFinset] at hg_mem
  exact hg_mem

set_option backward.isDefEq.respectTransparency false in
/-- `Hypothesis111` の Sylow 取替え: `A` を含む別の Sylow `p`-部分群 `P'` でも
Hypothesis 11.1 が成立する。`P, P'` は `M` 内共役なので `N_G(P') ⊆ M ⟺ N_G(P) ⊆ M`。 -/
theorem Hypothesis111.of_sylow [Finite G] {M : Subgroup G} {p : ℕ} {A₀ A P : Subgroup G}
    (h : Hypothesis111 M p A₀ A P) {P' : Subgroup G} (hP'pg : IsPGroup p ↥P')
    (hAP' : A ≤ P') (hP'M : P' ≤ M)
    (hP'syl : ∀ R : Subgroup G, P' ≤ R → R ≤ M → IsPGroup p ↥R → R = P') :
    Hypothesis111 M p A₀ A P' := by
  have : Fact p.Prime := ⟨h.prime⟩
  refine ⟨h.mem_maximal, h.prime, h.notMem_sigma, h.A₀_mem, h.A₀_le, h.normalizer_A₀_le,
    h.A_mem, h.A_le, h.A₀_le_A, hP'pg, hAP', hP'M, hP'syl, ?_, h.A_maximal⟩
  -- realize `P` and `P'` as Sylow subgroups of `↥M`, conjugate by some `m ∈ M`.
  obtain ⟨T, hPT⟩ := h.P_pgroup.comap_subtype.exists_le_sylow (G := M)
  have hTmap : (T : Subgroup ↥M).map M.subtype = P := by
    refine h.P_sylow _ ?_ (Subgroup.map_subtype_le _) (T.2.map M.subtype)
    rw [← Subgroup.map_subgroupOf_eq_of_le h.P_le]
    exact Subgroup.map_mono hPT
  obtain ⟨T', hPT'⟩ := hP'pg.comap_subtype.exists_le_sylow (G := M)
  have hT'map : (T' : Subgroup ↥M).map M.subtype = P' := by
    refine hP'syl _ ?_ (Subgroup.map_subtype_le _) (T'.2.map M.subtype)
    rw [← Subgroup.map_subgroupOf_eq_of_le hP'M]
    exact Subgroup.map_mono hPT'
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq ↥M T T'
  have hP'm : MulAut.conj (m : G) • P = P' := by
    rw [← hTmap, ← hT'map, ← hm, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def,
      Subgroup.pointwise_smul_def, Subgroup.map_map, Subgroup.map_map]
    rfl
  -- transport `N_G(P) ⊄ M` along the conjugation.
  intro hcon
  apply h.normalizer_P_not_le
  intro g hg
  have hgm : (m : G) * g * (m : G)⁻¹ ∈ Subgroup.normalizer (P' : Set G) := by
    rw [← hP'm]
    rw [Subgroup.mem_normalizer_iff] at hg ⊢
    intro y
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have := hg ((m : G)⁻¹ * y * (m : G))
    constructor
    · intro hy
      have h1 := this.mp (by simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hy)
      simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using h1
    · intro hy
      have h1 := this.mpr (by simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hy)
      simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using h1
  have hgmM : (m : G) * g * (m : G)⁻¹ ∈ M := hcon hgm
  have := M.mul_mem (M.mul_mem (M.inv_mem m.2) hgmM) m.2
  simpa [mul_assoc] using this

/-- **BG Theorem 11.7** (mmd L2997): `M_σ A ⊴ M`。§11 の主結果。 -/
theorem MsigmaA_normal [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} {p : ℕ} {A₀ A P : Subgroup G} (h : Hypothesis111 M p A₀ A P) :
    M ≤ Subgroup.normalizer ((S10.Msigma M ⊔ A : Subgroup G) : Set G) := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have hM := h.mem_maximal
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  -- `M` normalises `M_σ`.
  have hM_norm_Mσ : M ≤ Subgroup.normalizer ((S10.Msigma M) : Set G) := by
    rw [S10.Msigma, OddOrder.GroupTheory.opiCoreInG]
    have hle := Subgroup.le_normalizer_map (H := Ch03.oPiCore (S10.sigma M) ↥M) M.subtype
    rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hle
  -- ## the complement `E` to `M_σ` in `M` containing `A`
  set N : Subgroup ↥M := (S10.Msigma M).subgroupOf M with hNdef
  have hN_normal : N.Normal := by
    constructor
    intro n hn g
    rw [hNdef, Subgroup.mem_subgroupOf] at hn ⊢
    have hgn := (Subgroup.mem_normalizer_iff.mp (hM_norm_Mσ g.2) (n : G)).mp hn
    simpa using hgn
  have hN_hall : Ch03.IsHallSubgroup (S10.sigma M) N := S10.Msigma_subgroupOf_isHall hG hM
  have hN_cop : Nat.Coprime (Nat.card ↥N) N.index := hN_hall.coprime_index
  obtain ⟨E₀, hE₀⟩ := Subgroup.exists_right_complement'_of_coprime hN_cop
  have hN_card : Nat.card ↥N = Nat.card ↥(S10.Msigma M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (S10.Msigma_le M)).toEquiv
  have hp_not_in_N : ¬ p ∣ Nat.card ↥N := by
    intro hdvd
    rw [hN_card] at hdvd
    exact h.notMem_sigma (S10.Msigma_isPiGroup M p
      (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩))
  have hA_sub_card : Nat.card ↥(A.subgroupOf M) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.A_le).toEquiv, h.A_mem.2]
  have hcop_AN : Nat.Coprime (Nat.card ↥(A.subgroupOf M)) (Nat.card ↥N) := by
    rw [hA_sub_card]
    exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hp_not_in_N).pow_left 2
  obtain ⟨x, hx⟩ := Ch03.exists_conj_le_of_isComplement'_of_coprime inferInstance hE₀ hcop_AN
  set E₁ : Subgroup ↥M := E₀.map (MulAut.conj x).toMonoidHom with hE₁def
  have hE₁compl : N.IsComplement' E₁ := by
    have hcard₀ : Nat.card ↥E₁ = Nat.card ↥E₀ := by
      rw [hE₁def, Subgroup.card_map_of_injective (MulAut.conj x).injective]
    refine Subgroup.isComplement'_of_coprime ?_ ?_
    · rw [hcard₀]
      exact hE₀.card_mul_card
    · rw [hcard₀, (hE₀.symm.index_eq_card).symm]
      exact hN_cop
  set Esub : Subgroup G := E₁.map M.subtype with hEdef
  have hE_le_M : Esub ≤ M := by rw [hEdef]; exact Subgroup.map_subtype_le _
  have hA_le_E : A ≤ Esub := by
    rw [hEdef, ← Subgroup.map_subgroupOf_eq_of_le h.A_le]
    exact Subgroup.map_mono hx
  have hE_card_idx : Nat.card ↥Esub = N.index := by
    rw [hEdef, Subgroup.card_map_of_injective M.subtype_injective,
      hE₁def, Subgroup.card_map_of_injective (MulAut.conj x).injective]
    exact (hE₀.symm.index_eq_card).symm
  -- primes of `|E|` avoid `σ(M)`.
  have hE_pi' : ∀ r ∈ (Nat.card ↥Esub).primeFactors, r ∉ S10.sigma M := by
    intro r hr
    rw [hE_card_idx] at hr
    exact hN_hall.2 r hr
  -- `M = M_σ ⊔ E`.
  have hE_sup : S10.Msigma M ⊔ Esub = M := by
    have h1 : N ⊔ E₁ = ⊤ := hE₁compl.sup_eq_top
    have h2 : (N ⊔ E₁).map M.subtype = (⊤ : Subgroup ↥M).map M.subtype := by rw [h1]
    rw [Subgroup.map_sup, hNdef, Subgroup.map_subgroupOf_eq_of_le (S10.Msigma_le M),
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
    rw [← hEdef] at h2
    exact h2
  -- solvability, oddness, rank of `E`.
  have hE_solv : Group.IsSolvable ↥Esub := by
    have e : ↥E₁ ≃* ↥Esub := Subgroup.equivMapOfInjective E₁ M.subtype M.subtype_injective
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  have hE_odd : Odd (Nat.card ↥Esub) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card Esub)
  have hE_rank : rank ↥Esub ≤ 2 := by
    rw [rank_le_iff]
    intro r hr_prime
    have : Fact r.Prime := ⟨hr_prime⟩
    by_cases hr_dvd : r ∣ Nat.card ↥Esub
    · have hrM : pRank ↥Esub r ≤ pRank ↥M r :=
        pRank_le_of_injective (f := Subgroup.inclusion hE_le_M)
          (Subgroup.inclusion_injective hE_le_M)
      have hr_not_sigma : r ∉ S10.sigma M :=
        hE_pi' r (Nat.mem_primeFactors.mpr ⟨hr_prime, hr_dvd, Nat.card_pos.ne'⟩)
      have hr_not_alpha : r ∉ S10.alpha M := fun ha =>
        hr_not_sigma (S10.alpha_subset_sigma hG hM ha)
      have hrM2 : pRank ↥M r ≤ 2 := by
        by_contra hgt
        refine hr_not_alpha ⟨Nat.mem_primeFactors.mpr ⟨hr_prime, ?_, Nat.card_pos.ne'⟩,
          by omega⟩
        exact dvd_trans hr_dvd (Subgroup.card_dvd_of_le hE_le_M)
      exact le_trans hrM hrM2
    · rw [pRank_le_iff]
      intro B hB
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hB.isPGroup
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · rw [hk, pow_zero]
        simp
      · exfalso
        apply hr_dvd
        calc r ∣ p ^ 0 * r ^ k := by
              rw [pow_zero, one_mul]
              exact dvd_pow_self r hkpos.ne'
          _ = Nat.card ↥B := by rw [pow_zero, one_mul, hk]
          _ ∣ Nat.card ↥Esub := Subgroup.card_subgroup_dvd_card B
  have hE_frank : rank ↥(Ch01.fitting ↥Esub) ≤ 2 :=
    le_trans (rank_le_of_injective (f := (Ch01.fitting ↥Esub).subtype)
      (Ch01.fitting ↥Esub).subtype_injective) hE_rank
  -- ## the Hall radicals `K = O_τ(E)` and `W = O_{τ∪{p}}(E)` (Theorem 4.20(c), S05b)
  have hτ_up : IsUpperSet {q : ℕ | p < q} := fun a b hab ha => lt_of_lt_of_le ha hab
  have hτp_up : IsUpperSet {q : ℕ | p ≤ q} := fun a b hab ha => le_trans ha hab
  obtain ⟨hK_pi, hK_idx⟩ :=
    Ch1.S05.isHall_oPiCore_of_isUpperSet_of_rank_fitting_le_two hE_odd hE_frank hτ_up
  obtain ⟨hW_pi, hW_idx⟩ :=
    Ch1.S05.isHall_oPiCore_of_isUpperSet_of_rank_fitting_le_two hE_odd hE_frank hτp_up
  set K_g : Subgroup G := (Ch03.oPiCore {q : ℕ | p < q} ↥Esub).map Esub.subtype with hKgdef
  set W_g : Subgroup G := (Ch03.oPiCore {q : ℕ | p ≤ q} ↥Esub).map Esub.subtype with hWgdef
  have hKg_le_E : K_g ≤ Esub := by rw [hKgdef]; exact Subgroup.map_subtype_le _
  have hWg_le_E : W_g ≤ Esub := by rw [hWgdef]; exact Subgroup.map_subtype_le _
  have hE_norm_Kg : Esub ≤ Subgroup.normalizer (K_g : Set G) := by
    rw [hKgdef]
    have hle := Subgroup.le_normalizer_map (H := Ch03.oPiCore {q : ℕ | p < q} ↥Esub) Esub.subtype
    rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hle
  have hE_norm_Wg : Esub ≤ Subgroup.normalizer (W_g : Set G) := by
    rw [hWgdef]
    have hle := Subgroup.le_normalizer_map (H := Ch03.oPiCore {q : ℕ | p ≤ q} ↥Esub) Esub.subtype
    rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hle
  have hKg_card : Nat.card ↥K_g = Nat.card ↥(Ch03.oPiCore {q : ℕ | p < q} ↥Esub) := by
    rw [hKgdef, Subgroup.card_map_of_injective Esub.subtype_injective]
  have hKg_pi : ∀ r ∈ (Nat.card ↥K_g).primeFactors, p < r := by
    rw [hKg_card]
    exact hK_pi
  -- `p ∤ [M : E]` (the index is `|M_σ|`, a `σ`-number).
  have hp_relE : ¬ p ∣ Esub.relIndex M := by
    intro hdvd
    apply hp_not_in_N
    have h1 : Esub.subgroupOf M = E₁ := by
      rw [hEdef, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    have h2 : Esub.relIndex M = Nat.card ↥N := by
      have hrfl : Esub.relIndex M = (Esub.subgroupOf M).index := rfl
      rw [hrfl, h1]
      exact hE₁compl.index_eq_card
    rwa [h2] at hdvd
  -- `p ∤ [E : W]` (the index of the Hall `τ∪{p}`-radical avoids `p`).
  have hp_relW : ¬ p ∣ W_g.relIndex Esub := by
    intro hdvd
    have h1 : W_g.subgroupOf Esub = Ch03.oPiCore {q : ℕ | p ≤ q} ↥Esub := by
      rw [hWgdef, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective Esub.subtype_injective]
    have h2 : W_g.relIndex Esub = (Ch03.oPiCore {q : ℕ | p ≤ q} ↥Esub).index := by
      have hrfl : W_g.relIndex Esub = (W_g.subgroupOf Esub).index := rfl
      rw [hrfl, h1]
    rw [h2] at hdvd
    exact hW_idx p (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd,
      Subgroup.index_ne_zero_of_finite⟩) (le_refl p)
  have hp_relWM : ¬ p ∣ W_g.relIndex M := by
    intro hdvd
    have hchain : W_g.relIndex Esub * Esub.relIndex M = W_g.relIndex M :=
      Subgroup.relIndex_mul_relIndex (hHK := hWg_le_E) (hKL := hE_le_M)
    rw [← hchain] at hdvd
    rcases (Fact.out : p.Prime).dvd_mul.mp hdvd with h | h
    · exact hp_relW h
    · exact hp_relE h
  -- ## case split: does `A` centralise `K`?
  by_cases hcent : K_g ≤ Subgroup.centralizer (A : Set G)
  · -- `A` centralises `K`: `A = Ω₁(O_p(W)) ⊴ E`, hence `M_σ A ⊴ M`.
    -- `A ≤ W` (a `p`-subgroup lies in the normal Hall `τ∪{p}`-subgroup).
    have hA_le_W : A ≤ W_g := by
      have hA_sub : A.subgroupOf Esub ≤ Ch03.oPiCore {q : ℕ | p ≤ q} ↥Esub := by
        have : (Ch03.oPiCore {q : ℕ | p ≤ q} ↥Esub).Normal := inferInstance
        refine S10.le_of_coprime_card_index ?_
        have hcardA : Nat.card ↥(A.subgroupOf Esub) = p ^ 2 := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_le_E).toEquiv, h.A_mem.2]
        rw [hcardA]
        refine Nat.Coprime.pow_left 2 ?_
        refine (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr ?_
        intro hdvd
        exact hW_idx p (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd,
          Subgroup.index_ne_zero_of_finite⟩) (le_refl p)
      calc A = (A.subgroupOf Esub).map Esub.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hA_le_E).symm
        _ ≤ W_g := by rw [hWgdef]; exact Subgroup.map_mono hA_sub
    -- the `τ`-radical sits inside `W`.
    have hKg_le_W : K_g ≤ W_g := by
      rw [hKgdef, hWgdef]
      exact Subgroup.map_mono
        (Ch03.oPiCore_mono (fun r (hr : p < r) => le_of_lt hr) ↥Esub)
    have hW_norm_Kg : W_g ≤ Subgroup.normalizer (K_g : Set G) := hWg_le_E.trans hE_norm_Kg
    set K' : Subgroup ↥W_g := K_g.subgroupOf W_g with hK'def
    have hK'_normal : K'.Normal := by
      constructor
      intro n hn g
      rw [hK'def, Subgroup.mem_subgroupOf] at hn ⊢
      have hgn := (Subgroup.mem_normalizer_iff.mp (hW_norm_Kg g.2) (n : G)).mp hn
      simpa using hgn
    have hK'_card : Nat.card ↥K' = Nat.card ↥K_g :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKg_le_W).toEquiv
    have hp_not_K' : ¬ p ∣ Nat.card ↥K' := by
      intro hdvd
      rw [hK'_card] at hdvd
      exact lt_irrefl p (hKg_pi p (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩))
    -- every prime factor of `[W : K]` is `p` (it divides `|W|`, so lies in `τ∪{p}`,
    -- and it divides `[E : K]`, so avoids `τ`).
    have hK'_idx_primes : ∀ r ∈ K'.index.primeFactors, r = p := by
      intro r hr
      obtain ⟨hr_prime, hr_dvd, -⟩ := Nat.mem_primeFactors.mp hr
      have hr_W : p ≤ r := by
        have hdvd_W : r ∣ Nat.card ↥W_g := hr_dvd.trans (Subgroup.index_dvd_card K')
        have hcard_W : Nat.card ↥W_g = Nat.card ↥(Ch03.oPiCore {q : ℕ | p ≤ q} ↥Esub) := by
          rw [hWgdef, Subgroup.card_map_of_injective Esub.subtype_injective]
        rw [hcard_W] at hdvd_W
        exact hW_pi r (Nat.mem_primeFactors.mpr ⟨hr_prime, hdvd_W, Nat.card_pos.ne'⟩)
      have hr_not_τ : ¬ p < r := by
        intro hlt
        have hKidx : K'.index = K_g.relIndex W_g := rfl
        have hchain : K_g.relIndex W_g * W_g.relIndex Esub = K_g.relIndex Esub :=
          Subgroup.relIndex_mul_relIndex (hHK := hKg_le_W) (hKL := hWg_le_E)
        have hdvd_rel : r ∣ K_g.relIndex Esub := by
          rw [← hchain]
          exact Dvd.dvd.mul_right (hKidx ▸ hr_dvd) _
        have h1 : K_g.subgroupOf Esub = Ch03.oPiCore {q : ℕ | p < q} ↥Esub := by
          rw [hKgdef, Subgroup.subgroupOf,
            Subgroup.comap_map_eq_self_of_injective Esub.subtype_injective]
        have h2 : K_g.relIndex Esub = (Ch03.oPiCore {q : ℕ | p < q} ↥Esub).index := by
          have hrfl : K_g.relIndex Esub = (K_g.subgroupOf Esub).index := rfl
          rw [hrfl, h1]
        rw [h2] at hdvd_rel
        exact hK_idx r (Nat.mem_primeFactors.mpr ⟨hr_prime, hdvd_rel,
          Subgroup.index_ne_zero_of_finite⟩) hlt
      omega
    -- a Sylow `p`-subgroup `S` of `W` containing `A`, complementing `K'` in `W`.
    have hA_W_pg : IsPGroup p ↥(A.subgroupOf W_g) := h.A_mem.1.isPGroup.comap_subtype
    obtain ⟨S, hAS⟩ := hA_W_pg.exists_le_sylow (G := ↥W_g)
    have hcompl : K'.IsComplement' (S : Subgroup ↥W_g) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp S.isPGroup'
      have hcop : Nat.Coprime (Nat.card ↥K') (Nat.card ↥(S : Subgroup ↥W_g)) := by
        rw [hk]
        exact Nat.Coprime.pow_right k
          ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hp_not_K').symm
      refine Subgroup.isComplement'_of_coprime ?_ hcop
      have hSidx : Nat.card ↥(S : Subgroup ↥W_g) = K'.index := by
        refine Nat.dvd_antisymm ?_ ?_
        · have hdvd : Nat.card ↥(S : Subgroup ↥W_g) ∣ Nat.card ↥K' * K'.index := by
            rw [Subgroup.card_mul_index]
            exact Subgroup.card_subgroup_dvd_card _
          exact Nat.Coprime.dvd_of_dvd_mul_left hcop.symm hdvd
        · have hcop2 : Nat.Coprime K'.index (S : Subgroup ↥W_g).index := by
            rw [Nat.coprime_iff_gcd_eq_one]
            by_contra hne
            obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd hne
            rw [Nat.dvd_gcd_iff] at hr_dvd
            have hrp : r = p := hK'_idx_primes r (Nat.mem_primeFactors.mpr
              ⟨hr_prime, hr_dvd.1, Subgroup.index_ne_zero_of_finite⟩)
            exact S.not_dvd_index (hrp ▸ hr_dvd.2)
          have hdvd : K'.index ∣
              Nat.card ↥(S : Subgroup ↥W_g) * (S : Subgroup ↥W_g).index := by
            rw [Subgroup.card_mul_index]
            exact Subgroup.index_dvd_card _
          exact Nat.Coprime.dvd_of_dvd_mul_right hcop2 hdvd
      rw [hSidx]
      exact Subgroup.card_mul_index _
    -- `P_W` := the `G`-image of `S` is a Sylow `p`-subgroup of `M` containing `A`.
    set P_W : Subgroup G := (S : Subgroup ↥W_g).map W_g.subtype with hPWdef
    have hPW_pg : IsPGroup p ↥P_W := S.2.map W_g.subtype
    have hA_le_PW : A ≤ P_W := by
      rw [hPWdef, ← Subgroup.map_subgroupOf_eq_of_le hA_le_W]
      exact Subgroup.map_mono hAS
    have hPW_le_W : P_W ≤ W_g := by rw [hPWdef]; exact Subgroup.map_subtype_le _
    have hPW_le_M : P_W ≤ M := hPW_le_W.trans (hWg_le_E.trans hE_le_M)
    have hp_relPW : ¬ p ∣ P_W.relIndex M := by
      intro hdvd
      have hchain : P_W.relIndex W_g * W_g.relIndex M = P_W.relIndex M :=
        Subgroup.relIndex_mul_relIndex (hHK := hPW_le_W) (hKL := hWg_le_E.trans hE_le_M)
      rw [← hchain] at hdvd
      rcases (Fact.out : p.Prime).dvd_mul.mp hdvd with h' | h'
      · have h1 : P_W.subgroupOf W_g = (S : Subgroup ↥W_g) := by
          rw [hPWdef, Subgroup.subgroupOf,
            Subgroup.comap_map_eq_self_of_injective W_g.subtype_injective]
        have h2 : P_W.relIndex W_g = (S : Subgroup ↥W_g).index := by
          have hrfl : P_W.relIndex W_g = (P_W.subgroupOf W_g).index := rfl
          rw [hrfl, h1]
        rw [h2] at h'
        exact S.not_dvd_index h'
      · exact hp_relWM h'
    have hPW_syl := eq_of_le_of_isPGroup_of_not_dvd_relIndex hp_relPW
    have h' : Hypothesis111 M p A₀ A P_W := h.of_sylow hPW_pg hA_le_PW hPW_le_M hPW_syl
    -- Theorem 11.5 + Corollary 11.6(a) at `P_W`: abelian Sylow with `A = Ω₁(P_W)`.
    obtain ⟨ha_eq, -⟩ := omega1_eq_and_centralizer_trivial hG h'
    have hPWab : IsMulCommutative ↥P_W := by
      obtain ⟨T, hPT⟩ := hPW_pg.comap_subtype.exists_le_sylow (G := M)
      have hTmap : (T : Subgroup ↥M).map M.subtype = P_W := by
        refine hPW_syl _ ?_ (Subgroup.map_subtype_le _) (T.2.map M.subtype)
        rw [← Subgroup.map_subgroupOf_eq_of_le hPW_le_M]
        exact Subgroup.map_mono hPT
      have hTab := sylow_p_isCommutative hG h' T
      have e : ↥(T : Subgroup ↥M) ≃* ↥P_W := by
        rw [← hTmap]
        exact Subgroup.equivMapOfInjective _ _ M.subtype_injective
      exact isMulCommutative_of_mulEquiv e hTab
    have hPWcomm : ∀ u ∈ P_W, ∀ v ∈ P_W, u * v = v * u := by
      intro u hu v hv
      have hc := hPWab.is_comm.comm (⟨u, hu⟩ : ↥P_W) ⟨v, hv⟩
      simpa using congrArg Subtype.val hc
    -- the `Ω₁`-trap: exponent-`p` elements of `P_W` lie in `A`.
    have htrap : ∀ z ∈ P_W, z ^ p = 1 → z ∈ A := by
      intro z hz hzp
      rw [ha_eq]
      refine ⟨⟨z, hz⟩, Omega.mem_of_pow_eq_one ?_, rfl⟩
      rw [pow_one]
      refine Subtype.ext ?_
      rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      exact hzp
    -- `W` centralises `A`: `w = k·s` with `k ∈ K ≤ C_G(A)` and `s ∈ P_W ⊇ A` abelian.
    have hW_cent_A : ∀ w ∈ W_g, ∀ a ∈ A, w * a * w⁻¹ = a := by
      intro w hw a ha
      have hw_mem : (⟨w, hw⟩ : ↥W_g) ∈
          ((K' ⊔ (S : Subgroup ↥W_g) : Subgroup ↥W_g) : Set ↥W_g) := by
        rw [hcompl.sup_eq_top]
        exact Subgroup.mem_top _
      rw [Subgroup.normal_mul] at hw_mem
      obtain ⟨k, hk, s, hs, hks⟩ := hw_mem
      have hwG : w = (↑k : G) * (↑s : G) := by
        have h1 := congrArg (fun z : ↥W_g => (z : G)) hks
        simpa using h1.symm
      have hkA : ∀ b ∈ A, (↑k : G) * b * (↑k : G)⁻¹ = b := by
        intro b hb
        have hkK : (↑k : G) ∈ K_g := Subgroup.mem_subgroupOf.mp hk
        have hcomm := Subgroup.mem_centralizer_iff.mp (hcent hkK) b hb
        rw [← hcomm, mul_inv_cancel_right]
      have hsA : ∀ b ∈ A, (↑s : G) * b * (↑s : G)⁻¹ = b := by
        intro b hb
        have hsP : (↑s : G) ∈ P_W := by
          rw [hPWdef]
          exact ⟨s, hs, rfl⟩
        rw [hPWcomm _ hsP _ (hA_le_PW hb), mul_inv_cancel_right]
      rw [hwG]
      have h1 : ((↑k : G) * ↑s) * a * ((↑k : G) * ↑s)⁻¹
          = (↑k : G) * ((↑s : G) * a * (↑s : G)⁻¹) * (↑k : G)⁻¹ := by
        group
      rw [h1, hsA a ha, hkA a ha]
    -- hence `A ≤ O_p(W)`, and `A = Ω₁(O_p(W))` is characteristically pinned in `W`.
    set Op : Subgroup ↥W_g := Ch03.oPiCore {p} ↥W_g with hOpdef
    set Op_g : Subgroup G := Op.map W_g.subtype with hOpgdef
    have hA_le_Opg : A ≤ Op_g := by
      have hA_sub_norm : (A.subgroupOf W_g).Normal := by
        constructor
        intro n hn g
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        have := hW_cent_A (g : G) g.2 (n : G) hn
        have hcoe : ((g * n * g⁻¹ : ↥W_g) : G) = (g : G) * (n : G) * (g : G)⁻¹ := by
          simp
        rw [hcoe, this]
        exact hn
      have hA_sub_pi : Ch03.Subgroup.IsPiGroup {p} (A.subgroupOf W_g) := by
        intro r hr
        obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hA_W_pg
        rw [hj] at hr
        obtain ⟨hr_prime, hr_dvd, -⟩ := Nat.mem_primeFactors.mp hr
        exact Set.mem_singleton_iff.mpr
          ((Nat.prime_dvd_prime_iff_eq hr_prime Fact.out).mp (hr_prime.dvd_of_dvd_pow hr_dvd))
      have h1 : A.subgroupOf W_g ≤ Op := Ch03.Subgroup.IsPiGroup.le_oPiCore hA_sub_pi
      calc A = (A.subgroupOf W_g).map W_g.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hA_le_W).symm
        _ ≤ Op_g := by rw [hOpgdef]; exact Subgroup.map_mono h1
    have hOpg_le_PW : Op_g ≤ P_W := by
      -- `O_p(W)` is a normal `p`-subgroup, hence lies in the Sylow `S`.
      have hOp_pg : IsPGroup p ↥Op :=
        Ch04.isPGroup_of_isPiGroup_singleton (Ch03.oPiCore.isPiGroup {p})
      have hOp_le_S : Op ≤ (S : Subgroup ↥W_g) :=
        (Ch01.normal_pgroup_le_opCore hOp_pg).trans (Ch01.opCore_le S)
      rw [hOpgdef, hPWdef]
      exact Subgroup.map_mono hOp_le_S
    -- `A = Ω₁(O_p(W))` (as subgroups of `G`).
    have hA_om : A = (Omega ↥Op_g p 1).map Op_g.subtype := by
      apply le_antisymm
      · intro a ha
        refine ⟨⟨a, hA_le_Opg ha⟩, Omega.mem_of_pow_eq_one ?_, rfl⟩
        rw [pow_one]
        refine Subtype.ext ?_
        rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
        have h1 := congrArg Subtype.val (h.A_mem.1.2 ⟨a, ha⟩)
        rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h1
      · rw [Subgroup.map_le_iff_le_comap, Omega, Subgroup.closure_le]
        intro z hz
        rw [Set.mem_ofPred_eq, pow_one] at hz
        rw [SetLike.mem_coe, Subgroup.mem_comap]
        refine htrap (Op_g.subtype z) (hOpg_le_PW z.2) ?_
        rw [← map_pow, hz, map_one]
    -- `E` normalises `A` (characteristic chain `A = Ω₁(O_p(W))`, `W ⊴ E`).
    have hA_E_inv : ∀ e ∈ Esub, MulAut.conj e • A = A := by
      intro e he
      have h1 : e ∈ Subgroup.normalizer (Op_g : Set G) := by
        rw [hOpgdef, hOpdef]
        exact OddOrder.BG.AppB.normalizer_le_normalizer_map_of_characteristic
          (K := W_g) (W := Ch03.oPiCore {p} ↥W_g) (hE_norm_Wg he)
      have h2 : e ∈ Subgroup.normalizer (((Omega ↥Op_g p 1).map Op_g.subtype : Subgroup G)
          : Set G) :=
        OddOrder.BG.AppB.normalizer_le_normalizer_map_of_characteristic
          (K := Op_g) (W := Omega ↥Op_g p 1) h1
      rw [hA_om]
      exact conj_smul_eq_self_of_mem_normalizer h2
    -- assemble: every `m = n·e ∈ M_σ E` normalises `M_σ ⊔ A`.
    intro m hm
    have hm_mem : (⟨m, hm⟩ : ↥M) ∈ ((N ⊔ E₁ : Subgroup ↥M) : Set ↥M) := by
      rw [hE₁compl.sup_eq_top]
      exact Subgroup.mem_top _
    rw [Subgroup.normal_mul] at hm_mem
    obtain ⟨n, hn, e, he, hne⟩ := hm_mem
    have hmG : m = (↑n : G) * (↑e : G) := by
      have h1 := congrArg (fun z : ↥M => (z : G)) hne
      simpa using h1.symm
    have hnMσ : (↑n : G) ∈ S10.Msigma M := Subgroup.mem_subgroupOf.mp hn
    have heE : (↑e : G) ∈ Esub := by
      rw [hEdef]
      exact ⟨e, he, rfl⟩
    rw [hmG]
    refine Subgroup.mul_mem _ ?_ ?_
    · exact Subgroup.le_normalizer (Subgroup.mem_sup_left hnMσ)
    · refine mem_normalizer_of_conj_smul_eq_self ?_
      rw [Subgroup.smul_sup, hA_E_inv _ heE,
        conj_smul_eq_self_of_mem_normalizer (hM_norm_Mσ (hE_le_M heE))]
  · -- `A` does not centralise `K`: BG works toward the contradiction `q ∈ σ(M)`.
    exfalso
    -- ## a prime `q ∣ [K : C_K(A)]` and an `A`-invariant Sylow `q`-subgroup `Q` of `K`
    have hA_pg : IsPGroup p ↥A := h.A_mem.1.isPGroup
    have hA_norm_Kg : A ≤ Subgroup.normalizer (K_g : Set G) := hA_le_E.trans hE_norm_Kg
    have hAcard : Nat.card ↥A = p ^ 2 := h.A_mem.2
    have hp_ndvd_Kg : ¬ p ∣ Nat.card ↥K_g := fun hdvd =>
      lt_irrefl p (hKg_pi p (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩))
    have hcop_A_Kg : Nat.Coprime (Nat.card ↥A) (Nat.card ↥K_g) := by
      rw [hAcard]
      exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hp_ndvd_Kg).pow_left 2
    -- some prime `q` divides `[K : C_K(A)]` (`K ⊄ C_G(A)`).
    have hrel_ne_one : (K_g ⊓ Subgroup.centralizer (A : Set G)).relIndex K_g ≠ 1 := by
      intro h1
      exact hcent (le_trans (Subgroup.relIndex_eq_one.mp h1) inf_le_right)
    obtain ⟨q, hq_prime, hq_dvd_rel⟩ := Nat.exists_prime_and_dvd hrel_ne_one
    have : Fact q.Prime := ⟨hq_prime⟩
    have hq_dvd_Kg : q ∣ Nat.card ↥K_g :=
      hq_dvd_rel.trans (Subgroup.index_dvd_card
        ((K_g ⊓ Subgroup.centralizer (A : Set G)).subgroupOf K_g))
    have hq_gt_p : p < q :=
      hKg_pi q (Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd_Kg, Nat.card_pos.ne'⟩)
    have hq_not_sigma : q ∉ S10.sigma M := by
      refine hE_pi' q (Nat.mem_primeFactors.mpr ⟨hq_prime, ?_, Nat.card_pos.ne'⟩)
      exact hq_dvd_Kg.trans (Subgroup.card_dvd_of_le hKg_le_E)
    -- the `A`-invariant Sylow `q`-subgroup `Q` of `K` (Isaacs Cor 3.25 via `S11`).
    have hbot_inv : A ≤ Subgroup.normalizer (((⊥ : Subgroup G) : Set G)) := by
      rw [Subgroup.normalizer_eq_top]
      exact le_top
    obtain ⟨Q, hQ_syl, -⟩ :=
      exists_isAInvSylowIn hA_pg hA_norm_Kg hcop_A_Kg (IsPGroup.of_bot (p := q)) bot_le hbot_inv
    -- `q ∤ [K : Q]`, and `A` does not centralise `Q`.
    have hQ_relK : ¬ q ∣ Q.relIndex K_g := not_dvd_relIndex_of_isAInvSylowIn hQ_syl
    have hQ_ncent : ¬ Q ≤ Subgroup.centralizer (A : Set G) := by
      intro hle
      apply hQ_relK
      have hQC : Q ≤ K_g ⊓ Subgroup.centralizer (A : Set G) := le_inf hQ_syl.le hle
      have hchain : Q.relIndex (K_g ⊓ Subgroup.centralizer (A : Set G)) *
          (K_g ⊓ Subgroup.centralizer (A : Set G)).relIndex K_g = Q.relIndex K_g :=
        Subgroup.relIndex_mul_relIndex (hHK := hQC) (hKL := inf_le_left)
      exact hq_dvd_rel.trans (hchain ▸ dvd_mul_left _ _)
    have hq_odd : Odd q :=
      hG.odd.of_dvd_nat (hq_dvd_Kg.trans (Subgroup.card_subgroup_dvd_card K_g))
    have hq_ne2 : q ≠ 2 := by
      have := (Fact.out : p.Prime).two_le
      omega
    have hq_ndvd_A : ¬ q ∣ Nat.card ↥A := by
      rw [hAcard]
      intro hdvd
      exact (lt_irrefl p) (((Nat.prime_dvd_prime_iff_eq hq_prime Fact.out).mp
        (hq_prime.dvd_of_dvd_pow hdvd)) ▸ hq_gt_p)
    -- ## `C_Q(A) = 1` (else Proposition 10.10(c) forces `[A,Q] = 1`)
    have hCQA_bot : Q ⊓ Subgroup.centralizer (A : Set G) = ⊥ := by
      by_contra hne
      -- (a) `Q` is not cyclic: otherwise the order-`q` elements of `C_Q(A)` span the unique
      -- order-`q` subgroup of `Q` and Corollary 1.12 makes the `A`-action on `Q` trivial.
      have hq_dvd_inf : q ∣ Nat.card ↥(Q ⊓ Subgroup.centralizer (A : Set G)) := by
        obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (hQ_syl.isPGroup.to_inf_left
          (K := Subgroup.centralizer (A : Set G)))
        have hj_ne : j ≠ 0 := by
          intro h0
          apply hne
          rw [h0, pow_zero] at hj
          exact Subgroup.card_eq_one.mp hj
        rw [hj]
        exact dvd_pow_self q hj_ne
      have hQ_nc : ¬ IsCyclic ↥Q := by
        intro hcyc
        apply hQ_ncent
        -- an order-`q` element `y` of `C_Q(A)` (Cauchy in the nontrivial `q`-group `Q ⊓ C`).
        obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' q hq_dvd_inf
        set y : ↥Q := ⟨(y₀ : G),
          (inf_le_left : Q ⊓ Subgroup.centralizer (A : Set G) ≤ Q) y₀.2⟩ with hydef
        have hy_ord : orderOf y = q := by
          rw [← hy₀]
          exact (orderOf_injective Q.subtype (Subgroup.subtype_injective Q) y).symm.trans
            (orderOf_injective _ (Subgroup.subtype_injective _) y₀)
        -- conjugation action of `↥A` on `↥Q`.
        let act : MulDistribMulAction ↥A ↥Q :=
          MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (Q : Set G))) ↥Q
            (Subgroup.inclusion hQ_syl.A_le_normalizer)
        set φ : ↥A →* MulAut ↥Q := MulDistribMulAction.toMulAut ↥A ↥Q with hφ_def
        have hφ_coe : ∀ (a : ↥A) (z : ↥Q),
            ((((φ a) z) : ↥Q) : G) = (↑a) * ((z : ↥Q) : G) * (↑a)⁻¹ := fun _ _ => rfl
        -- the order-`q` line `E = ⟨y⟩` is elementary abelian and `A`-fixed.
        have hE_ea : (Subgroup.zpowers y).IsElementaryAbelian q := by
          refine Subgroup.IsElementaryAbelian.of_card_prime ?_
          rw [Nat.card_zpowers, hy_ord]
        have hfix : ∀ a : ↥A,
            ∀ g ∈ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup ↥Q) : Set ↥Q),
            g ^ q = 1 → φ a g = g := by
          intro a g _ hgq
          obtain ⟨n, rfl⟩ := mem_zpowers_of_pow_prime_eq_one hq_prime hy_ord hgq
          rw [map_zpow]
          congr 1
          refine Subtype.ext ?_
          rw [hφ_coe a y]
          change (↑a : G) * (y₀ : G) * (↑a : G)⁻¹ = (y₀ : G)
          have hcomm : (↑a : G) * (y₀ : G) = (y₀ : G) * (↑a : G) :=
            Subgroup.mem_centralizer_iff.mp
              ((inf_le_right : Q ⊓ Subgroup.centralizer (A : Set G) ≤
                Subgroup.centralizer (A : Set G)) y₀.2) (↑a) a.2
          rw [hcomm, mul_inv_cancel_right]
        -- Corollary 1.12: the `A`-action on `Q` is trivial, i.e. `Q ≤ C_G(A)`.
        have htriv := OddOrder.BG.Ch1.S01.actsTrivially_of_fixes_omega1_centralizer
          hq_ne2 hQ_syl.isPGroup hq_ndvd_A φ hE_ea hfix
        intro w hw
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        have h2 := congrArg Subtype.val (htriv ⟨b, hb⟩ ⟨w, hw⟩)
        rw [hφ_coe ⟨b, hb⟩ ⟨w, hw⟩] at h2
        exact (mul_inv_eq_iff_eq_mul.mp h2)
      -- (b) `B ∈ ℰ²(Q)`: the noncyclic odd `q`-group `Q` has an elem-ab `q²`-subgroup.
      obtain ⟨B₀, hB₀ea, hB₀card⟩ :=
        OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic
          hQ_syl.isPGroup hq_odd hQ_nc
      set B : Subgroup G := B₀.map Q.subtype with hBdef
      have hB_le_Q : B ≤ Q := by rw [hBdef]; exact Subgroup.map_subtype_le _
      have hB_ea : B.IsElementaryAbelian q := hB₀ea.map Q.subtype_injective
      have hB_card : Nat.card ↥B = q ^ 2 := by
        rw [hBdef, Subgroup.card_map_of_injective Q.subtype_injective, hB₀card]
      have hB_le_M : B ≤ M := hB_le_Q.trans (hQ_syl.le.trans (hKg_le_E.trans hE_le_M))
      -- (c) `pRank ↥M q = 2` and `B` is maximal elementary abelian in `G` (Lemma 10.4(c)).
      have hq_dvd_M : q ∣ Nat.card ↥M :=
        hq_dvd_Kg.trans ((Subgroup.card_dvd_of_le hKg_le_E).trans
          (Subgroup.card_dvd_of_le hE_le_M))
      have hq_rank2 : pRank ↥M q = 2 := by
        refine le_antisymm ?_ ?_
        · by_contra hgt
          push Not at hgt
          exact hq_not_sigma (S10.alpha_subset_sigma hG hM
            ⟨Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd_M, Nat.card_pos.ne'⟩, by omega⟩)
        · have hsub_ea : (B.subgroupOf M).IsElementaryAbelian q := by
            refine Subgroup.IsElementaryAbelian.of_map M.subtype_injective ?_
            rw [Subgroup.map_subgroupOf_eq_of_le hB_le_M]
            exact hB_ea
          have hlog := le_pRank (B.subgroupOf M) hsub_ea
          rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB_le_M).toEquiv, hB_card,
            Nat.log_pow hq_prime.one_lt] at hlog
      have hB_max : IsMaximalElementaryAbelian q B :=
        ((S10.alpha_criterion hG hM).2 q hq_prime hq_not_sigma hq_rank2).2 B hB_le_M
          ⟨hB_ea, hB_card⟩
      -- (d) a maximal `A`-invariant `q`-subgroup `Q* ⊇ Q` of `G`.
      have hQ_mem : Q ∈ hInvariant ⊤ A {q} := by
        rw [mem_hInvariant]
        refine ⟨le_top, hQ_syl.A_le_normalizer, fun r hr => ?_⟩
        obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hQ_syl.isPGroup
        rw [hj] at hr
        obtain ⟨hr_prime, hr_dvd, -⟩ := Nat.mem_primeFactors.mp hr
        exact Set.mem_singleton_iff.mpr
          ((Nat.prime_dvd_prime_iff_eq hr_prime hq_prime).mp (hr_prime.dvd_of_dvd_pow hr_dvd))
      obtain ⟨Qs, hQs_star, hQQs⟩ := exists_le_hInvariantStar hQ_mem
      -- (e) `q ∈ π(C_G(A))` (the nontrivial `q`-group `Q ⊓ C_G(A)` sits inside `C_G(A)`).
      have hq_cga : q ∈ (Nat.card ↥(Subgroup.centralizer (A : Set G))).primeFactors := by
        refine Nat.mem_primeFactors.mpr ⟨hq_prime, ?_, Nat.card_pos.ne'⟩
        exact hq_dvd_inf.trans (Subgroup.card_dvd_of_le inf_le_right)
      -- (f) Proposition 10.10(c): a Sylow `p` over `A` centralises `Q*`, hence `Q ≤ C_G(A)`.
      obtain ⟨Ps, hAPs, -, -, hPsc⟩ :=
        S10.normalizer_factorization hG (ne_of_lt hq_gt_p) h.A_mem h.A_maximal hQs_star hq_cga
      have hB_le_Qs : B ≤ Qs := hB_le_Q.trans hQQs
      have hPs_cent : (Ps : Subgroup G) ≤ Subgroup.centralizer (Qs : Set G) := by
        refine hPsc (Or.inr ⟨B.subgroupOf Qs, ?_, ?_, ?_⟩)
        · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB_le_Qs).toEquiv, hB_card]
        · refine Subgroup.IsElementaryAbelian.of_map Qs.subtype_injective ?_
          rw [Subgroup.map_subgroupOf_eq_of_le hB_le_Qs]
          exact hB_ea
        · intro F hF_ea hBF
          have hFmap : F.map Qs.subtype = B := by
            refine hB_max.2 _ (hF_ea.map Qs.subtype_injective) ?_
            rw [← Subgroup.map_subgroupOf_eq_of_le hB_le_Qs]
            exact Subgroup.map_mono hBF
          refine Subgroup.map_injective Qs.subtype_injective ?_
          rw [hFmap, Subgroup.map_subgroupOf_eq_of_le hB_le_Qs]
      apply hQ_ncent
      have hQs_cent : Qs ≤ Subgroup.centralizer (A : Set G) :=
        Subgroup.le_centralizer_iff.mp (hAPs.trans hPs_cent)
      exact hQQs.trans hQs_cent
    -- ## `Q₀ := Z(Q)` satisfies `Q₀ = [Q₀, A]` (Proposition 1.6(d))
    have hQ_le_M : Q ≤ M := hQ_syl.le.trans (hKg_le_E.trans hE_le_M)
    have hQ_ne_bot : Q ≠ ⊥ := by
      intro hbot
      apply hQ_ncent
      rw [hbot]
      exact bot_le
    have hQ_nontriv : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ_ne_bot
    set Q₀ : Subgroup G := (Subgroup.center ↥Q).map Q.subtype with hQ₀def
    have hQ₀_le_Q : Q₀ ≤ Q := by rw [hQ₀def]; exact Subgroup.map_subtype_le _
    have hQ₀_pg : IsPGroup q ↥Q₀ := hQ_syl.isPGroup.to_le hQ₀_le_Q
    have hQ₀_ne_bot : Q₀ ≠ ⊥ := by
      intro hbot
      have hcb : Subgroup.center ↥Q = ⊥ := by
        apply Subgroup.map_injective Q.subtype_injective
        rw [Subgroup.map_bot]
        rw [hQ₀def] at hbot
        exact hbot
      exact hQ_syl.isPGroup.bot_lt_center.ne' hcb
    have hQ₀_comm : IsMulCommutative ↥Q₀ :=
      isMulCommutative_of_mulEquiv
        (Subgroup.equivMapOfInjective _ _ Q.subtype_injective) inferInstance
    have := hQ₀_comm
    -- `Z(Q)` is characteristic in `Q`, so `N_G(Q) ≤ N_G(Q₀)`; in particular `A ≤ N_G(Q₀)`.
    have hN_le : Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (Q₀ : Set G) := by
      rw [hQ₀def]
      exact OddOrder.BG.AppB.normalizer_le_normalizer_map_of_characteristic
    have hA_norm_Q₀ : A ≤ Subgroup.normalizer (Q₀ : Set G) :=
      hQ_syl.A_le_normalizer.trans hN_le
    have hcop_Q₀_A : Nat.Coprime (Nat.card ↥Q₀) (Nat.card ↥A) := by
      obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hQ₀_pg
      rw [hj, hAcard]
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hq_prime Fact.out).mpr (ne_of_gt hq_gt_p))
    obtain ⟨-, hdec_sup⟩ :=
      OddOrder.Isaacs.Ch05.fitting_coprime_abelian_decomp (P := Q₀) (K := A)
        hA_norm_Q₀ hcop_Q₀_A
    have hCA_Q₀_bot : Subgroup.centralizer (A : Set G) ⊓ Q₀ = ⊥ := by
      rw [← le_bot_iff, ← hCQA_bot, inf_comm]
      exact inf_le_inf_right _ hQ₀_le_Q
    have hQ₀_eq_comm : Q₀ = ⁅Q₀, A⁆ := by
      have h1 := hdec_sup
      rw [hCA_Q₀_bot, bot_sup_eq] at h1
      exact h1.symm
    -- ## the two conjugate lines `A = A₁A₂` (Corollary 11.6(c)) split the commutator
    obtain ⟨A₁, A₂, hA₁A, hA₂A, -, hcard1, hcard2, hsup12, -, hc1, hc2⟩ :=
      exists_distinct_conj_lines hG h
    have hA_comm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
      intro x hx y hy
      exact congrArg Subtype.val (h.A_mem.1.comm (⟨x, hx⟩ : ↥A) ⟨y, hy⟩)
    have hQ₀_eq2 : Q₀ = ⁅Q₀, A₁⁆ ⊔ ⁅Q₀, A₂⁆ := by
      refine le_antisymm ?_ (sup_le ?_ ?_)
      · calc Q₀ = ⁅Q₀, A⁆ := hQ₀_eq_comm
          _ ≤ ⁅Q₀, A₁⁆ ⊔ ⁅Q₀, A₂⁆ :=
            commutator_le_sup_of_abelian hA_comm hsup12 hA_norm_Q₀
      · calc ⁅Q₀, A₁⁆ ≤ ⁅Q₀, A⁆ := Subgroup.commutator_mono le_rfl hA₁A
          _ = Q₀ := hQ₀_eq_comm.symm
      · calc ⁅Q₀, A₂⁆ ≤ ⁅Q₀, A⁆ := Subgroup.commutator_mono le_rfl hA₂A
          _ = Q₀ := hQ₀_eq_comm.symm
    -- ## Proposition 10.11(d) at `A₁`, `A₂`: both `[Q₀, Aᵢ]` are normal in `M`
    have hQ₀_le_M : Q₀ ≤ M := hQ₀_le_Q.trans hQ_le_M
    have hQ₀_pi_sigma' : Subgroup.IsPiSubgroup (S10.sigma M)ᶜ Q₀ := by
      intro r hr
      obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hQ₀_pg
      rw [hj] at hr
      obtain ⟨hr_prime, hr_dvd, -⟩ := Nat.mem_primeFactors.mp hr
      rw [(Nat.prime_dvd_prime_iff_eq hr_prime hq_prime).mp (hr_prime.dvd_of_dvd_pow hr_dvd)]
      exact hq_not_sigma
    have hQ₀_pi_p' : Subgroup.IsPiSubgroup (({p} : Set ℕ)ᶜ) Q₀ := by
      intro r hr
      obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hQ₀_pg
      rw [hj] at hr
      obtain ⟨hr_prime, hr_dvd, -⟩ := Nat.mem_primeFactors.mp hr
      rw [(Nat.prime_dvd_prime_iff_eq hr_prime hq_prime).mp (hr_prime.dvd_of_dvd_pow hr_dvd)]
      exact fun hmem => (ne_of_gt hq_gt_p) (Set.mem_singleton_iff.mp hmem)
    have hA₁_mem : A₁ ∈ elemAbelianOfRank G p 1 := by
      refine ⟨Subgroup.IsElementaryAbelian.of_card_prime hcard1, ?_⟩
      rw [hcard1, pow_one]
    have hA₂_mem : A₂ ∈ elemAbelianOfRank G p 1 := by
      refine ⟨Subgroup.IsElementaryAbelian.of_card_prime hcard2, ?_⟩
      rw [hcard2, pow_one]
    obtain ⟨-, -, hMnorm₁⟩ :=
      S10.sigma_complement_commutator_cyclic_normal hG hM hQ₀_le_M hQ₀_pi_sigma'
        h.notMem_sigma hA₁_mem (le_inf (hA₁A.trans hA_norm_Q₀) (hA₁A.trans h.A_le))
        (by rw [inf_comm]; exact hc1) hQ₀_comm hQ₀_pi_p'
    obtain ⟨-, -, hMnorm₂⟩ :=
      S10.sigma_complement_commutator_cyclic_normal hG hM hQ₀_le_M hQ₀_pi_sigma'
        h.notMem_sigma hA₂_mem (le_inf (hA₂A.trans hA_norm_Q₀) (hA₂A.trans h.A_le))
        (by rw [inf_comm]; exact hc2) hQ₀_comm hQ₀_pi_p'
    -- ## `M = N_G(Q₀)`, hence `N_G(Q) ≤ M`
    have hM_norm_Q₀ : M ≤ Subgroup.normalizer (Q₀ : Set G) := by
      intro m hm
      refine mem_normalizer_of_conj_smul_eq_self ?_
      rw [hQ₀_eq2, Subgroup.smul_sup,
        conj_smul_eq_self_of_mem_normalizer (hMnorm₁ hm),
        conj_smul_eq_self_of_mem_normalizer (hMnorm₂ hm)]
    have hNQ₀_eq_M : Subgroup.normalizer (Q₀ : Set G) = M := by
      by_contra hne'
      have hlt : M < Subgroup.normalizer (Q₀ : Set G) :=
        lt_of_le_of_ne hM_norm_Q₀ (Ne.symm hne')
      have hnormal : Q₀.Normal := Subgroup.normalizer_eq_top_iff.mp (hM.2 _ hlt)
      rcases hG.simple.eq_bot_or_eq_top_of_normal _ hnormal with hbot | htop'
      · exact hQ₀_ne_bot hbot
      · exact hM.1 (top_le_iff.mp (htop' ▸ hQ₀_le_M))
    have hNQ_le_M : Subgroup.normalizer (Q : Set G) ≤ M := hNQ₀_eq_M ▸ hN_le
    -- ## `q ∤ [M : Q]`: `Q` is a Sylow `q`-subgroup of `M`, so `q ∈ σ(M)` — contradiction
    have hq_relKE : ¬ q ∣ K_g.relIndex Esub := by
      intro hdvd
      have h1 : K_g.subgroupOf Esub = Ch03.oPiCore {r : ℕ | p < r} ↥Esub := by
        rw [hKgdef, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective Esub.subtype_injective]
      have h2 : K_g.relIndex Esub = (Ch03.oPiCore {r : ℕ | p < r} ↥Esub).index := by
        have hrfl : K_g.relIndex Esub = (K_g.subgroupOf Esub).index := rfl
        rw [hrfl, h1]
      rw [h2] at hdvd
      exact hK_idx q (Nat.mem_primeFactors.mpr ⟨hq_prime, hdvd,
        Subgroup.index_ne_zero_of_finite⟩) hq_gt_p
    have hq_relEM : ¬ q ∣ Esub.relIndex M := by
      intro hdvd
      have h1 : Esub.subgroupOf M = E₁ := by
        rw [hEdef, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
      have h2 : Esub.relIndex M = Nat.card ↥N := by
        have hrfl : Esub.relIndex M = (Esub.subgroupOf M).index := rfl
        rw [hrfl, h1]
        exact hE₁compl.index_eq_card
      rw [h2, hN_card] at hdvd
      exact hq_not_sigma (S10.Msigma_isPiGroup M q
        (Nat.mem_primeFactors.mpr ⟨hq_prime, hdvd, Nat.card_pos.ne'⟩))
    have hq_relQM : ¬ q ∣ Q.relIndex M := by
      intro hdvd
      have hchain1 : Q.relIndex K_g * K_g.relIndex Esub = Q.relIndex Esub :=
        Subgroup.relIndex_mul_relIndex (hHK := hQ_syl.le) (hKL := hKg_le_E)
      have hchain2 : Q.relIndex Esub * Esub.relIndex M = Q.relIndex M :=
        Subgroup.relIndex_mul_relIndex (hHK := hQ_syl.le.trans hKg_le_E) (hKL := hE_le_M)
      rw [← hchain2, ← hchain1] at hdvd
      rcases (Fact.out : q.Prime).dvd_mul.mp hdvd with h' | h'
      · rcases (Fact.out : q.Prime).dvd_mul.mp h' with h'' | h''
        · exact hQ_relK h''
        · exact hq_relKE h''
      · exact hq_relEM h'
    apply hq_not_sigma
    have hq_dvd_M : q ∣ Nat.card ↥M :=
      hq_dvd_Kg.trans ((Subgroup.card_dvd_of_le hKg_le_E).trans
        (Subgroup.card_dvd_of_le hE_le_M))
    have hQsylM := eq_of_le_of_isPGroup_of_not_dvd_relIndex hq_relQM
    have hmaxM : ∀ {R : Subgroup ↥M}, IsPGroup q ↥R → Q.subgroupOf M ≤ R →
        R = Q.subgroupOf M := by
      intro R hRpg hQR
      have hmap : R.map M.subtype = Q := by
        refine hQsylM _ ?_ (Subgroup.map_subtype_le _) (hRpg.map M.subtype)
        rw [← Subgroup.map_subgroupOf_eq_of_le hQ_le_M]
        exact Subgroup.map_mono hQR
      rw [← hmap, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    rw [S10.mem_sigma_iff]
    refine ⟨Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd_M, Nat.card_pos.ne'⟩,
      ⟨Q.subgroupOf M, hQ_syl.isPGroup.comap_subtype, hmaxM⟩, ?_⟩
    rw [Subgroup.map_subgroupOf_eq_of_le hQ_le_M]
    exact hNQ_le_M

end OddOrder.BG.Ch3.S11


