-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S11_ExceptionalMaximal
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S11_ExceptionalMaximal
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:12:57.084422+00:00
-- url     : https://prove2.me/theorems/ce8af0ab-9730-4bd8-ac40-e13ccd2a67e7
-- title:
--   BG §11: exceptional maximal subgroups
-- statement:
--   Formalizes Chapter III §11 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*: Lemma 11.1, Theorems 11.3, 11.5, 11.7 and Corollaries 11.2, 11.4, 11.6. Under Hypothesis 11.1 ($M\in\mathcal{M}$, $p\in\sigma(M)'$, $A_0\in\mathcal{E}_p^1(M)$, $N_G(A_0)\subseteq M$) it studies exceptional maximal subgroups $M$, those for which $r(H/H_\sigma)=1$ fails.
--
--   Main declarations: `Hypothesis111` (BG Hypothesis 11.1 together with derived data: $M\in\mathcal{M}$, $p\in\sigma(M)'$, $A_0\in\mathcal{E}_p^1(M)$, $N_G(A_0)\subseteq M$); `IsAInvSylowIn` (an $A$-invariant Sylow $q$-subgroup $Q$ of $H$: $Q\le H$, a $q$-group, $A$-invariant and $q$-maximal in $H$).
--
--   The bundle also proves 25 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S11_ExceptionalMaximal.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S11_ExceptionalMaximal.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03c_Thm37
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_Setup
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S10_HallStructure
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S10_LocalLemmas
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S10_BetaRadical
import Definitions.Def_OddOrder_GroupTheory_MaximalSubgroup
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelianFamily
import Definitions.Def_OddOrder_GroupTheory_NarrowPGroup
import Definitions.Def_OddOrder_GroupTheory_OmegaSubgroup
import Definitions.Def_OddOrder_GroupTheory_PRank

namespace OddOrder.BG.Ch3.S11

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BG Hypothesis 11.1** (mmd L2917) + 導出データ: `M ∈ ℳ`, `p ∈ σ(M)'`, `A₀ ∈ ℰ_p¹(M)`,
`N_G(A₀) ⊆ M`; さらに Lem 10.5 から `A ∈ ℰ_p²(M)` (`A₀⊆A`), `A ⊆ P ∈ Syl_p(M)`, `N_G(P)⊄M`,
`A ∈ ℰ_p*(G)`。§11 全体の standing assumption。 -/
structure Hypothesis111 (M : Subgroup G) (p : ℕ) (A₀ A P : Subgroup G) : Prop where
  mem_maximal : M ∈ maximalSubgroups G
  prime : p.Prime
  notMem_sigma : p ∉ S10.sigma M
  A₀_mem : A₀ ∈ elemAbelianOfRank G p 1
  A₀_le : A₀ ≤ M
  normalizer_A₀_le : Subgroup.normalizer (A₀ : Set G) ≤ M
  A_mem : A ∈ elemAbelianOfRank G p 2
  A_le : A ≤ M
  A₀_le_A : A₀ ≤ A
  P_pgroup : IsPGroup p ↥P
  A_le_P : A ≤ P
  P_le : P ≤ M
  /-- `P` is a Sylow `p`-subgroup of `M` (`p`-maximality inside `M`; the literal
  `P ∈ Syl_p(M)` of BG Hypothesis 11.1, produced by Lemma 10.5). -/
  P_sylow : ∀ R : Subgroup G, P ≤ R → R ≤ M → IsPGroup p ↥R → R = P
  normalizer_P_not_le : ¬ Subgroup.normalizer (P : Set G) ≤ M
  A_maximal : IsMaximalElementaryAbelian p A

namespace Hypothesis111

variable {M : Subgroup G} {p : ℕ} {A₀ A P : Subgroup G}

theorem A0_le_P (h : Hypothesis111 M p A₀ A P) : A₀ ≤ P :=
  h.A₀_le_A.trans h.A_le_P

end Hypothesis111

/-- `Q` は `H` の `A`-不変 Sylow `q`-部分群 (= `Q ≤ H`, `q`-群, `A`-不変, `H` 内で `q`-極大)。 -/
def IsAInvSylowIn (q : ℕ) (A Q H : Subgroup G) : Prop :=
  Q ≤ H ∧ IsPGroup q ↥Q ∧ A ≤ Subgroup.normalizer (Q : Set G) ∧
    ∀ R : Subgroup G, Q ≤ R → R ≤ H → IsPGroup q ↥R → R = Q

@[simp] theorem isAInvSylowIn_iff (q : ℕ) (A Q H : Subgroup G) :
    IsAInvSylowIn q A Q H ↔
      Q ≤ H ∧ IsPGroup q ↥Q ∧ A ≤ Subgroup.normalizer (Q : Set G) ∧
        ∀ R : Subgroup G, Q ≤ R → R ≤ H → IsPGroup q ↥R → R = Q :=
  Iff.rfl

namespace IsAInvSylowIn

variable {q : ℕ} {A Q H : Subgroup G}

theorem le (h : IsAInvSylowIn q A Q H) : Q ≤ H :=
  h.1

theorem isPGroup (h : IsAInvSylowIn q A Q H) : IsPGroup q ↥Q :=
  h.2.1

theorem A_le_normalizer (h : IsAInvSylowIn q A Q H) :
    A ≤ Subgroup.normalizer (Q : Set G) :=
  h.2.2.1

/-- The `A`-slot of `IsAInvSylowIn` is antitone: a `B`-invariant Sylow is `A`-invariant for
`A ≤ B`. -/
theorem of_le {B : Subgroup G} (h : IsAInvSylowIn q B Q H) (hAB : A ≤ B) :
    IsAInvSylowIn q A Q H :=
  ⟨h.1, h.2.1, hAB.trans h.2.2.1, h.2.2.2⟩

end IsAInvSylowIn

/-- `φ • H = H.map φ`: the pointwise `MulAut`-action on a subgroup is its image under the
corresponding monoid hom. -/
private theorem mulAut_smul_eq_map (φ : MulAut G) (H : Subgroup G) :
    φ • H = H.map (φ : G →* G) := by
  rw [Subgroup.pointwise_smul_def]
  rfl

/-- Conjugation commutes with taking normalizers: `N_G(H)^g = N_G(H^g)`. -/
private theorem normalizer_conj_smul (g : G) (H : Subgroup G) :
    MulAut.conj g • Subgroup.normalizer (H : Set G)
      = Subgroup.normalizer ((MulAut.conj g • H : Subgroup G) : Set G) := by
  rw [mulAut_smul_eq_map, mulAut_smul_eq_map]
  exact Subgroup.map_normalizer_eq_of_bijective H (MulAut.conj g).bijective

/-- A `π`-Hall subgroup stays `π`-Hall after conjugation (cardinality and index are
preserved by the inner automorphism `MulAut.conj g`). -/
private theorem isHallSubgroup_conj_smul {π : Set ℕ} {H : Subgroup G} (g : G)
    (hH : Ch03.IsHallSubgroup π H) : Ch03.IsHallSubgroup π (MulAut.conj g • H) := by
  rw [mulAut_smul_eq_map]
  refine ⟨?_, ?_⟩
  · -- card preserved
    have hcard : Nat.card ↥(H.map (MulAut.conj g : G →* G)) = Nat.card ↥H :=
      (Nat.card_congr (Subgroup.equivMapOfInjective H _ (MulAut.conj g).injective).toEquiv).symm
    rw [hcard]; exact hH.1
  · -- index preserved
    have hidx : (H.map (MulAut.conj g : G →* G)).index = H.index :=
      Subgroup.index_map_equiv H (MulAut.conj g)
    rw [hidx]; exact hH.2

/-- **STEP2 bridge** (auxiliary): an `A`-invariant Sylow `q`-subgroup `Q` of a `σ(M)`-Hall
subgroup `H` of `G` (with `q ∈ σ(M)`) is a *maximal* `A`-invariant `q`-subgroup of `G`, i.e.
`Q ∈ ℋ_G*(A;q)`.

Reason: the 4th conjunct of `IsAInvSylowIn` makes `Q` a maximal `q`-subgroup of `↥H`
(= Sylow `q` of `↥H`), so `q ∤ [H : Q]`. As `q ∈ σ(M)` and `H` is `σ(M)`-Hall, `q ∤ [G : H]`,
hence `q ∤ [G : Q]` by the index tower law; thus `Q` is a Sylow `q`-subgroup of `G`, so no
larger `q`-subgroup (a fortiori no larger `A`-invariant one) exists. We return both the
Sylow witness (`Q` is Sylow `q` of `G`) and the `ℋ_G*(A;q)`-membership. -/
private theorem isSylow_and_mem_hInvariantStar_of_isAInvSylowIn [Finite G]
    {M A H Q : Subgroup G} {q : ℕ}
    [Fact q.Prime] (hHall : Ch03.IsHallSubgroup (S10.sigma M) H) (hq : q ∈ S10.sigma M)
    (hQ : IsAInvSylowIn q A Q H) :
    (∃ QS : Sylow q G, (QS : Subgroup G) = Q) ∧ Q ∈ hInvariantStar ⊤ A {q} := by
  obtain ⟨hQH, hQp, hAQ, hQmax⟩ := hQ
  -- `q ∤ [G : Q]`: Sylow of `↥H` index times Hall index, both `q`-prime.
  have hQidx : ¬ q ∣ Q.index := by
    -- Land `Q.subgroupOf H` in a Sylow `S` of `↥H`; map back and use maximality `Q = S.map`.
    obtain ⟨S, hS⟩ := hQp.comap_subtype.exists_le_sylow (G := H)
    -- `S.map H.subtype` is an `q`-subgroup of `H` containing `Q`, so it equals `Q` by maximality.
    have hSmaple : (S : Subgroup ↥H).map H.subtype ≤ H := Subgroup.map_subtype_le _
    have hSmapp : IsPGroup q ↥((S : Subgroup ↥H).map H.subtype) := S.2.map H.subtype
    have hQle : Q ≤ (S : Subgroup ↥H).map H.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hQH]
      exact Subgroup.map_mono hS
    have hSeqQ : (S : Subgroup ↥H).map H.subtype = Q := hQmax _ hQle hSmaple hSmapp
    -- Hence `Q.subgroupOf H = S` (as a subgroup of `↥H`).
    have hsubOf : Q.subgroupOf H = (S : Subgroup ↥H) := by
      rw [← hSeqQ, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    -- Index tower: `[G : Q] = [H : Q]·[G : H]`, both factors `q`-prime.
    have htower : (Q.subgroupOf H).index * H.index = Q.index :=
      Subgroup.relIndex_mul_index hQH
    rw [hsubOf] at htower
    -- `q ∤ [↥H : S]` (Sylow of finite `↥H`) and `q ∤ [G : H]` (Hall, `q ∈ σ(M)`).
    have : (S : Subgroup ↥H).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
    have hSidx : ¬ q ∣ (S : Subgroup ↥H).index := by
      have := S.not_dvd_index; simpa using this
    have hHidx : ¬ q ∣ H.index := fun hdvd =>
      hHall.2 q (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Subgroup.index_ne_zero_of_finite⟩) hq
    rw [← htower]
    exact (Fact.out (p := q.Prime)).not_dvd_mul hSidx hHidx
  -- Upgrade `Q` to a Sylow `q`-subgroup of `G`.
  have : Q.FiniteIndex := ⟨fun h => hQidx (h ▸ dvd_zero q)⟩
  let QS : Sylow q G := hQp.toSylow hQidx
  have hQS : (QS : Subgroup G) = Q := hQp.toSylow_coe hQidx
  refine ⟨⟨QS, hQS⟩, ⟨le_top, hAQ, ?_⟩, ?_⟩
  · -- `Q` is a `{q}`-subgroup.
    intro r hr
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (G := Q)).mp hQp
    rw [hn] at hr
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · simp [hn0] at hr
    · rw [Nat.primeFactors_prime_pow hn0.ne' Fact.out] at hr; simpa using hr
  · -- Maximality among `A`-invariant `q`-subgroups: any larger `q`-subgroup equals `Q`.
    intro Q' hQ' hQQ'
    obtain ⟨-, -, hQ'pi⟩ := hQ'
    have hQ'p : IsPGroup q Q' := OddOrder.Isaacs.Ch04.isPGroup_of_isPiGroup_singleton hQ'pi
    -- `QS` is a Sylow `q`-subgroup, so it is `≤`-maximal among `q`-subgroups.
    have heq : Q' = (QS : Subgroup G) := QS.3 hQ'p (hQS ▸ hQQ')
    rw [heq, hQS]

/-- **BG Lemma 11.1** (mmd L2939): Hyp 11.1 のもと、`g ∈ G−M`, `A ⊆ M^g`, `q ∈ σ(M)`、`Q₁`/`Q₂`
を `M_σ`/`M_σ^g` の `A`-不変 Sylow `q`-部分群とする。すると (a) `Q₁ ⊓ Q₂ = 1`、(b) 各 `X ∈ ℰ¹(A)`
で `C_{Q₁}(X) = 1` または `C_{Q₂}(X) = 1`。 -/
theorem invariant_sylow_disjoint [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} {p : ℕ} {A₀ A P : Subgroup G} (h : Hypothesis111 M p A₀ A P)
    {g : G} (hg : g ∉ M) (hAg : A ≤ MulAut.conj g • M) {q : ℕ} [Fact q.Prime]
    (hq : q ∈ S10.sigma M) {Q₁ Q₂ : Subgroup G}
    (hQ₁ : IsAInvSylowIn q A Q₁ (S10.Msigma M))
    (hQ₂ : IsAInvSylowIn q A Q₂ (MulAut.conj g • S10.Msigma M)) :
    Q₁ ⊓ Q₂ = ⊥ ∧
    ∀ X : Subgroup G, X ∈ elemAbelianOfRank G p 1 → X ≤ A →
      Subgroup.centralizer (X : Set G) ⊓ Q₁ = ⊥ ∨
      Subgroup.centralizer (X : Set G) ⊓ Q₂ = ⊥ := by
  have : Fact p.Prime := ⟨h.prime⟩
  -- Basic facts about `A`.
  have hAelem : A.IsElementaryAbelian p := h.A_mem.1
  have hAcomm : IsMulCommutative ↥A := ⟨⟨fun x y => hAelem.comm x y⟩⟩
  have hAcard : Nat.card ↥A = p ^ 2 := h.A_mem.2
  -- `p ∣ |G|` (Lagrange via `A ≤ G`, `|A| = p²`).
  have hpG : p ∣ Nat.card G := by
    have hdvd : Nat.card ↥A ∣ Nat.card G := Subgroup.card_subgroup_dvd_card A
    rw [hAcard] at hdvd
    exact dvd_trans (dvd_pow_self p (by norm_num)) hdvd
  -- STEP1: `A` satisfies Hypothesis 7.1 (Prop 7.5, case (1)).
  have hHyp71 : Ch2.S07.Hypothesis71 A := by
    refine Ch2.S07.hypothesis71_of_scn2_or_pLengthOne hG hpG A hAcomm hAelem.isPGroup
      (Or.inl ⟨?_, fun N hN => S10.proper_hasPLengthOne hG N hN⟩)
    -- `(A : Set G) = {x | x ∈ C_G(A) ∧ x ^ p = 1}` (= `A = Ω₁(C_G(A))`).
    ext x
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe]
    constructor
    · -- `x ∈ A ⟹ x ∈ C_G(A) ∧ x ^ p = 1`.
      intro hx
      have := hAcomm
      refine ⟨Subgroup.le_centralizer (H := A) hx, ?_⟩
      have hxp1 : (⟨x, hx⟩ : ↥A) ^ p = 1 := hAelem.2 _
      have := congrArg (Subgroup.subtype A) hxp1
      simpa using this
    · -- `x ∈ C_G(A) ∧ x ^ p = 1 ⟹ x ∈ A` (maximality of `A`).
      rintro ⟨hxc, hxp⟩
      -- `B := closure(A ∪ {x})` is `p`-elementary abelian and contains `A`, so `B = A`.
      -- Generating set `A ∪ {x}` consists of pairwise-commuting elements.
      have hgen_comm : ∀ a ∈ (A : Set G) ∪ {x}, ∀ b ∈ (A : Set G) ∪ {x}, a * b = b * a := by
        rintro a (ha | ha) b (hb | hb)
        · have := hAelem.comm ⟨a, ha⟩ ⟨b, hb⟩
          simpa using congrArg (Subgroup.subtype A) this
        · rw [Set.mem_singleton_iff] at hb; subst hb; exact hxc a ha
        · rw [Set.mem_singleton_iff] at ha; subst ha; exact (hxc b hb).symm
        · rw [Set.mem_singleton_iff] at ha hb; subst ha; subst hb; rfl
      set B : Subgroup G := Subgroup.closure ((A : Set G) ∪ {x}) with hB_def
      have hBcomm : IsMulCommutative ↥B := Subgroup.isMulCommutative_closure hgen_comm
      -- Every generator is `p`-torsion; in the commutative `B`, so is every element.
      have hgen_pow : ∀ w ∈ (A : Set G) ∪ {x}, w ^ p = 1 := by
        rintro w (hw | hw)
        · have := hAelem.2 ⟨w, hw⟩; simpa using congrArg (Subgroup.subtype A) this
        · rw [Set.mem_singleton_iff] at hw; subst hw; exact hxp
      -- Commutativity inside the closure `B` (lifted from `IsMulCommutative ↥B`).
      have hBclos_comm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb => by
        have := hBcomm.is_comm.comm (⟨a, ha⟩ : ↥B) ⟨b, hb⟩
        simpa using congrArg (Subgroup.subtype B) this
      -- Every element of the closure is `p`-torsion.
      have hclos_pow : ∀ y ∈ Subgroup.closure ((A : Set G) ∪ {x}), y ^ p = 1 := by
        intro y hy
        induction hy using Subgroup.closure_induction with
        | mem z hz => exact hgen_pow z hz
        | one => simp
        | mul z₁ z₂ hz₁ hz₂ h₁ h₂ =>
            have hc : Commute z₁ z₂ := hBclos_comm z₁ hz₁ z₂ hz₂
            rw [hc.mul_pow, h₁, h₂, mul_one]
        | inv z _ h => rw [inv_pow, h, inv_one]
      have hB_pow : ∀ u : ↥B, u ^ p = 1 := fun u =>
        Subtype.ext (by simpa using hclos_pow (u : G) u.2)
      -- `B` is `p`-elementary abelian; maximality collapses it to `A`.
      have hBelem : B.IsElementaryAbelian p := ⟨fun u v => hBcomm.is_comm.comm u v, hB_pow⟩
      have hAleB : A ≤ B := fun z hz => Subgroup.subset_closure (Or.inl hz)
      have hBeqA : B = A := h.A_maximal.2 B hBelem hAleB
      have hxB : x ∈ B := by
        rw [hB_def]; exact Subgroup.subset_closure (Or.inr rfl)
      rw [hBeqA] at hxB
      exact hxB
  -- STEP2: bridge `IsAInvSylowIn` to `ℋ_G*(A;q)` for `Q₁` (in `M_σ`) and `Q₂` (in `M_σ^g`).
  have : Fact q.Prime := ‹Fact q.Prime›
  have hHallMsigma : Ch03.IsHallSubgroup (S10.sigma M) (S10.Msigma M) :=
    (S10.isHall_Msigma_Malpha hG h.mem_maximal).1
  have hHallConj : Ch03.IsHallSubgroup (S10.sigma M) (MulAut.conj g • S10.Msigma M) :=
    isHallSubgroup_conj_smul g hHallMsigma
  obtain ⟨⟨Q₁S, hQ₁S⟩, hQ₁star⟩ :=
    isSylow_and_mem_hInvariantStar_of_isAInvSylowIn (M := M) hHallMsigma hq hQ₁
  obtain ⟨⟨Q₂S, hQ₂S⟩, hQ₂star⟩ :=
    isSylow_and_mem_hInvariantStar_of_isAInvSylowIn (M := M) hHallConj hq hQ₂
  -- `q ∈ π(A)' = {p}ᶜ` because `q ∈ σ(M)` but `p ∉ σ(M)`, so `q ≠ p`.
  have hqp : q ≠ p := by rintro rfl; exact h.notMem_sigma hq
  have hqπ' : q ∈ (Ch2.S07.primesOf A)ᶜ := by
    simp only [Ch2.S07.primesOf, Set.mem_compl_iff, Set.mem_ofPred_eq]
    intro hmem
    rw [hAcard, Nat.primeFactors_prime_pow (by norm_num) h.prime, Finset.mem_singleton] at hmem
    exact hqp hmem
  -- `C_G(A) ⊆ M` (via `C_G(A) ≤ C_G(A₀) ≤ N_G(A₀) ≤ M`).
  have hCAM : Subgroup.centralizer (A : Set G) ≤ M := by
    have h1 : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (A₀ : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr h.A₀_le_A)
    exact le_trans (le_trans h1 (Subgroup.centralizer_le_normalizer _)) h.normalizer_A₀_le
  -- `kSubgroup A ≤ C_G(A) ⊆ M`.
  have hKM : Ch2.S07.kSubgroup A ≤ M :=
    le_trans (Subgroup.map_subtype_le _) hCAM
  -- STEP3-5: prove both conjuncts by contradiction via the inductive lemma.
  -- A reusable contradiction: if some proper `H ⊇ A` meets both `Q₁` and `Q₂` nontrivially,
  -- the inductive lemma forces `Q₂ = Q₁^k` with `k ∈ K ⊆ M`, so `Q₂ ⊆ M`; then `g ∈ M`.
  have key : ∀ H : Subgroup G, H < ⊤ → A ≤ H → H ⊓ Q₁ ≠ ⊥ → H ⊓ Q₂ ≠ ⊥ → False := by
    intro H hHproper hAH hHQ₁ hHQ₂
    obtain ⟨k, hk, hkconj⟩ :=
      Ch2.S07.inductiveLemma hG hHyp71 hqπ' hQ₁star hQ₂star H hHproper hAH hHQ₁ hHQ₂
    -- `Q₂ = Q₁^k ≤ M^? ` — actually `Q₂ ≤ M`: `Q₂ = conj k • Q₁`, `Q₁ ≤ M_σ ≤ M`, `k ∈ M`.
    have hkM : k ∈ M := hKM hk
    have hQ₁M : Q₁ ≤ M := le_trans hQ₁.1 (Subgroup.map_subtype_le _)
    have hQ₂M : Q₂ ≤ M := by
      rw [← hkconj]
      intro y hy
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
      have hmem : k⁻¹ * y * k⁻¹⁻¹ ∈ M := by
        have hy' : (MulAut.conj k)⁻¹ y ∈ Q₁ := hy
        rw [← map_inv, MulAut.conj_apply] at hy'
        exact hQ₁M hy'
      have hres : k * (k⁻¹ * y * k⁻¹⁻¹) * k⁻¹ ∈ M :=
        M.mul_mem (M.mul_mem hkM hmem) (M.inv_mem hkM)
      simpa [inv_inv, mul_assoc] using hres
    -- `R := Q₂^{g⁻¹}` is a Sylow `q`-subgroup of `G` inside `M_σ ⊆ M`, and `R^g = Q₂ ⊆ M`.
    -- By Theorem 10.1(d) applied to the Sylow `q`-subgroup `R` of `M`, `g ∈ M` — contradiction.
    set R : Subgroup G := (MulAut.conj g)⁻¹ • Q₂ with hR_def
    -- `R ≤ M_σ` (because `Q₂ ≤ M_σ^g`).
    have hRMsigma : R ≤ S10.Msigma M := by
      have hQ₂g : Q₂ ≤ MulAut.conj g • S10.Msigma M := hQ₂.1
      rw [hR_def]
      have := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := (MulAut.conj g)⁻¹)).mpr hQ₂g
      rwa [inv_smul_smul] at this
    have hRM : R ≤ M := le_trans hRMsigma (Subgroup.map_subtype_le _)
    -- `conj g • R = Q₂`.
    have hconjR : MulAut.conj g • R = Q₂ := by rw [hR_def, smul_inv_smul]
    -- `R = Q₂^{g⁻¹}` as the image of `Q₂` under the automorphism `(MulAut.conj g)⁻¹`.
    have hReqmap : R = Q₂.map (((MulAut.conj g)⁻¹ : MulAut G) : G →* G) := by
      rw [hR_def, mulAut_smul_eq_map]
    -- `R` is a `q`-group (conjugate of the `q`-group `Q₂`).
    have hRp : IsPGroup q ↥R := by
      rw [hReqmap]
      exact hQ₂.2.1.of_equiv (Subgroup.equivMapOfInjective Q₂ _ (MulAut.conj g)⁻¹.injective)
    -- `R` Sylow of `G`: `R.index = Q₂.index` (conjugation), and `Q₂ = Q₂S` is Sylow of `G`.
    have hRidxG : ¬ q ∣ R.index := by
      have hRidx_eq : R.index = Q₂.index := by
        rw [hReqmap, Subgroup.index_map_equiv Q₂ (MulAut.conj g)⁻¹]
      rw [hRidx_eq, ← hQ₂S]
      have : (Q₂S : Subgroup G).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
      exact Q₂S.not_dvd_index
    -- Build the Sylow `q`-subgroup of `↥M` whose image is `R`.
    have hRsubM_idx : ¬ q ∣ (R.subgroupOf M).index := by
      have htower : (R.subgroupOf M).index * M.index = R.index := Subgroup.relIndex_mul_index hRM
      exact fun hdvd => hRidxG (htower ▸ Dvd.dvd.mul_right hdvd M.index)
    have : (R.subgroupOf M).FiniteIndex := ⟨fun h => hRsubM_idx (h ▸ dvd_zero q)⟩
    let RM : Sylow q ↥M := (hRp.comap_subtype (K := M)).toSylow hRsubM_idx
    have hRM_coe : (RM : Subgroup ↥M).map M.subtype = R := by
      change ((hRp.comap_subtype (K := M)).toSylow hRsubM_idx : Subgroup ↥M).map M.subtype = R
      rw [(hRp.comap_subtype (K := M)).toSylow_coe hRsubM_idx, Subgroup.comap_subtype,
        Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRM]
    -- `R ≠ ⊥`: else `R.index = |G|`, which `q` divides (`q ∈ σ(M) ⊆ π(G)`), contradicting `hRidxG`.
    have hqG : q ∣ Nat.card G :=
      dvd_trans (Nat.dvd_of_mem_primeFactors hq.1) (Subgroup.card_subgroup_dvd_card M)
    have hRnebot : R ≠ ⊥ := fun hRbot => hRidxG (by rw [hRbot, Subgroup.index_bot]; exact hqG)
    -- Theorem 10.1(d): `R` Sylow `q` of `M`, `R^g ⊆ M` ⇒ `g ∈ M`.
    have hgM : g ∈ M := by
      have hfusion := (S10.fusion_control_of_mem_sigma hG h.mem_maximal hq
        (X := R) hRnebot hRp).2.2.2.1
      exact hfusion ⟨RM, hRM_coe.symm⟩ g (hconjR ▸ hQ₂M)
    exact hg hgM
  -- `Z(G) = 1` (simple nonabelian) — used for `C_G(X) < ⊤`.
  have hZbot : Subgroup.center G = ⊥ := by
    have : IsSimpleGroup G := hG.simple
    refine (Subgroup.Normal.eq_bot_or_eq_top Subgroup.instNormalCenter).resolve_right
      (fun htop => ?_)
    exact hG.notSolvable (Group.isSolvable_of_comm (fun a b =>
      (Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top a) b).symm))
  -- `M < ⊤`.
  have hMlt : M < ⊤ := lt_top_iff_ne_top.mpr h.mem_maximal.1
  -- `M^g ⊓ M < ⊤` and `A ≤ M^g ⊓ M`.
  have hHmm_le : (MulAut.conj g • M) ⊓ M ≤ M := inf_le_right
  have hHmm_lt : (MulAut.conj g • M) ⊓ M < ⊤ := lt_of_le_of_lt hHmm_le hMlt
  have hAHmm : A ≤ (MulAut.conj g • M) ⊓ M := le_inf hAg h.A_le
  -- `Q₁ ≤ M` and `Q₂ ≤ M^g`.
  have hQ₁leM : Q₁ ≤ M := le_trans hQ₁.1 (Subgroup.map_subtype_le _)
  have hQ₂leMg : Q₂ ≤ MulAut.conj g • M := by
    refine le_trans hQ₂.1 ?_
    exact (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj g)).mpr
      (Subgroup.map_subtype_le _)
  refine ⟨?_, ?_⟩
  · -- (a) `Q₁ ⊓ Q₂ = ⊥`.
    by_contra hne
    -- `Q₁ ⊓ Q₂ ≤ (M^g ⊓ M) ⊓ Q₁` and `≤ (M^g ⊓ M) ⊓ Q₂`, both nonbot.
    refine key ((MulAut.conj g • M) ⊓ M) hHmm_lt hAHmm ?_ ?_
    · refine fun hbot => hne (le_bot_iff.mp ?_)
      calc Q₁ ⊓ Q₂ ≤ ((MulAut.conj g • M) ⊓ M) ⊓ Q₁ :=
            le_inf (le_inf (le_trans inf_le_right hQ₂leMg) (le_trans inf_le_left hQ₁leM))
              inf_le_left
        _ = ⊥ := hbot
    · refine fun hbot => hne (le_bot_iff.mp ?_)
      calc Q₁ ⊓ Q₂ ≤ ((MulAut.conj g • M) ⊓ M) ⊓ Q₂ :=
            le_inf (le_inf (le_trans inf_le_right hQ₂leMg) (le_trans inf_le_left hQ₁leM))
              inf_le_right
        _ = ⊥ := hbot
  · -- (b) for each `X ∈ ℰ¹(A)` with `X ≤ A`: `C_{Q₁}(X) = ⊥` or `C_{Q₂}(X) = ⊥`.
    intro X hX hXA
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    -- `X ≠ ⊥` (`|X| = p`).
    have hXne : X ≠ ⊥ := by
      rintro rfl
      have := hX.2; simp only [Subgroup.card_bot] at this
      exact h.prime.one_lt.ne' (by simpa using this.symm)
    -- `A ≤ C_G(X)` (`A` abelian, `X ≤ A`).
    have hAcX : A ≤ Subgroup.centralizer (X : Set G) := by
      have := hAcomm
      exact le_trans (Subgroup.le_centralizer (H := A))
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXA))
    -- `C_G(X) < ⊤` (else `X ≤ Z(G) = ⊥`, contradicting `X ≠ ⊥`).
    have hCXlt : Subgroup.centralizer (X : Set G) < ⊤ := by
      refine lt_of_le_of_ne le_top (fun htop => hXne (le_bot_iff.mp ?_))
      rw [← hZbot, ← SetLike.coe_subset_coe]
      exact (Subgroup.centralizer_eq_top_iff_subset.mp htop)
    exact key (Subgroup.centralizer (X : Set G)) hCXlt hAcX hc1 hc2

/-- A `σ(M)`-subgroup `L` of the maximal subgroup `M` is contained in `M_σ = O_{σ(M)}(M)`.
Reason: `M_σ` is a normal `σ(M)`-Hall subgroup of `M` (Thm 10.2), so it absorbs every
`σ(M)`-subgroup of `M`. -/
private theorem sigma_subgroup_le_Msigma [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {L : Subgroup G} (hLM : L ≤ M)
    (hLpi : Ch03.Subgroup.IsPiGroup (S10.sigma M) L) : L ≤ S10.Msigma M :=
  S10.sigma_subgroup_le_Msigma_of_isHall ((S10.isHall_Msigma_Malpha hG hM).1) hLM hLpi

/-- **`A`-invariant Sylow `q`-subgroup constructor** (Isaacs Cor 3.25 inside `↥H`): if a
`p`-group `A` normalizes a finite subgroup `H` of coprime order and `P₀ ≤ H` is an
`A`-invariant `q`-subgroup, there is a `Q ∈ ℋ_H*(A;q)` (`IsAInvSylowIn q A Q H`) with `P₀ ≤ Q`.

The `↥A`-action on `↥H` is conjugation (`A ≤ N_G(H)`); `Cor 3.25` produces a conjugation-invariant
Sylow `q` of `↥H` containing `P₀.subgroupOf H`, which maps back to the required `Q`. -/
theorem exists_isAInvSylowIn [Finite G] {A : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hAp : IsPGroup p ↥A) {H : Subgroup G} (hAH : A ≤ Subgroup.normalizer (H : Set G))
    {q : ℕ} [Fact q.Prime] (hCop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥H))
    {P₀ : Subgroup G} (hP₀q : IsPGroup q ↥P₀) (hP₀H : P₀ ≤ H)
    (hP₀inv : A ≤ Subgroup.normalizer (P₀ : Set G)) :
    ∃ Q : Subgroup G, IsAInvSylowIn q A Q H ∧ P₀ ≤ Q := by
  have : Finite ↥A := Subtype.finite
  have : Group.IsNilpotent ↥A := hAp.isNilpotent
  have : Group.IsSolvable ↥A := inferInstance
  -- Conjugation action of `↥A` on `↥H` (`A ≤ N_G(H)`), as a `MulAut`-hom `φ`.
  let act : MulDistribMulAction ↥A ↥H :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (H : Set G))) ↥H
      (Subgroup.inclusion hAH)
  set φ : ↥A →* MulAut ↥H := MulDistribMulAction.toMulAut ↥A ↥H with hφ_def
  have hφ_coe : ∀ (a : ↥A) (x : ↥H), (H.subtype ((φ a) x)) = (↑a) * (H.subtype x) * (↑a)⁻¹ :=
    fun _ _ => rfl
  -- `(φ a)⁻¹` is `φ a⁻¹`, acting by conjugation by `(↑a)⁻¹`.
  have hφ_inv_coe : ∀ (a : ↥A) (x : ↥H),
      (H.subtype (((φ a)⁻¹) x)) = (↑a)⁻¹ * (H.subtype x) * (↑a) := by
    intro a x
    rw [← map_inv]
    have := hφ_coe a⁻¹ x
    simpa using this
  -- `P₀.subgroupOf H` is an `A`-invariant `q`-subgroup of `↥H`.
  have hP₀sub_q : IsPGroup q ↥(P₀.subgroupOf H) := hP₀q.comap_subtype
  have hP₀sub_inv : Ch03.IsAInvariant φ (P₀.subgroupOf H) := by
    rw [Ch03.isAInvariant_iff_smul_mem]
    intro a x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have ha : (↑a : G) ∈ A := a.2
    change H.subtype ((φ a) x) ∈ P₀
    rw [hφ_coe a x]
    exact ((Subgroup.mem_normalizer_iff.mp (hP₀inv ha)) (H.subtype x)).mp hx
  -- Cor 3.25 inside `↥H`: an `A`-invariant Sylow `q` of `↥H` containing `P₀.subgroupOf H`.
  obtain ⟨S, hS_inv, hP₀S⟩ :=
    OddOrder.Isaacs.Ch04.aInvariant_pSubgroup_le_aInvariant_sylow (G := ↥H) (A := ↥A) (φ := φ)
      hCop (Or.inl inferInstance) hP₀sub_q hP₀sub_inv
  -- Map the Sylow back to `G`.
  refine ⟨(S : Subgroup ↥H).map H.subtype, ⟨Subgroup.map_subtype_le _, S.2.map H.subtype, ?_, ?_⟩,
      ?_⟩
  · -- `A ≤ N_G(Q)` from conjugation-invariance of `S`.
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨x, hxS, rfl⟩
      -- `a * ↑x * a⁻¹ = ↑((φ ⟨a,ha⟩) x) ∈ S.map subtype`.
      exact ⟨(φ ⟨a, ha⟩) x, hS_inv.smul_mem ⟨a, ha⟩ hxS, hφ_coe ⟨a, ha⟩ x⟩
    · rintro ⟨x, hxS, hx⟩
      -- `y = a⁻¹ * ↑x * a = ↑((φ ⟨a,ha⟩)⁻¹ x) ∈ S.map subtype`.
      refine ⟨((φ ⟨a, ha⟩)⁻¹) x, hS_inv.inv_smul_mem ⟨a, ha⟩ hxS, ?_⟩
      rw [hφ_inv_coe ⟨a, ha⟩ x, hx]
      change a⁻¹ * (a * y * a⁻¹) * a = y
      group
  · -- Maximality: any `q`-subgroup `R` with `Q ≤ R ≤ H` equals `Q` (Sylow `q` of `↥H`).
    intro R hQR hRH hRq
    have hRsub_q : IsPGroup q ↥(R.subgroupOf H) := hRq.comap_subtype
    have hS_le : (S : Subgroup ↥H) ≤ R.subgroupOf H := by
      intro x hxS
      rw [Subgroup.mem_subgroupOf]
      exact hQR ⟨x, hxS, rfl⟩
    have hRsubOf : R.subgroupOf H = (S : Subgroup ↥H) := S.3 hRsub_q hS_le
    -- `R = (R.subgroupOf H).map subtype = S.map subtype`.
    calc R = (R.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hRH).symm
      _ = (S : Subgroup ↥H).map H.subtype := by rw [hRsubOf]
  · -- `P₀ ≤ Q`.
    calc P₀ = (P₀.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hP₀H).symm
      _ ≤ (S : Subgroup ↥H).map H.subtype := Subgroup.map_mono hP₀S

/-- A member `Q ∈ ℋ_H*(A;q)` is a *Sylow* `q`-subgroup of `↥H`, so if `q ∣ |H|` then
`q ∣ |Q|`; in particular `Q ≠ ⊥`. (The 4th conjunct of `IsAInvSylowIn` makes `Q.subgroupOf H`
a maximal — hence Sylow — `q`-subgroup of `↥H`.) -/
private theorem isAInvSylowIn_card_dvd [Finite G] {A H Q : Subgroup G} {q : ℕ}
    [Fact q.Prime] (hQ : IsAInvSylowIn q A Q H) (hqH : q ∣ Nat.card ↥H) :
    q ∣ Nat.card ↥Q := by
  obtain ⟨hQH, hQp, _, hQmax⟩ := hQ
  -- `Q.subgroupOf H` is a Sylow `q`-subgroup of `↥H`.
  obtain ⟨T, hT⟩ := hQp.comap_subtype.exists_le_sylow (G := H)
  have hTmaple : (T : Subgroup ↥H).map H.subtype ≤ H := Subgroup.map_subtype_le _
  have hTmapp : IsPGroup q ↥((T : Subgroup ↥H).map H.subtype) := T.2.map H.subtype
  have hQle : Q ≤ (T : Subgroup ↥H).map H.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hQH]; exact Subgroup.map_mono hT
  have hTeqQ : (T : Subgroup ↥H).map H.subtype = Q := hQmax _ hQle hTmaple hTmapp
  have hsubOf : Q.subgroupOf H = (T : Subgroup ↥H) := by
    rw [← hTeqQ, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  -- `q ∤ [↥H : T]`, `|↥H| = |T|·[↥H : T]`, `q ∣ |↥H|` ⟹ `q ∣ |T| = |Q|`.
  have : (T : Subgroup ↥H).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hTidx : ¬ q ∣ (T : Subgroup ↥H).index := by have := T.not_dvd_index; simpa using this
  have hcardH : Nat.card ↥(T : Subgroup ↥H) * (T : Subgroup ↥H).index = Nat.card ↥H :=
    Subgroup.card_mul_index _
  have hcardQT : Nat.card ↥(Q.subgroupOf H) = Nat.card ↥Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
  have hqT : q ∣ Nat.card ↥(T : Subgroup ↥H) := by
    rcases (Nat.Prime.dvd_mul Fact.out).mp (hcardH ▸ hqH) with h | h
    · exact h
    · exact absurd h hTidx
  rw [← hcardQT, hsubOf]; exact hqT

/-- **BG Corollary 11.2** (mmd L2946): `g ∈ G−M`, `A ⊆ M^g` ⇒ (a) `M_σ ⊓ M^g = 1`、
(b) `M_σ ⊓ C_G(A₀^g) = 1`。 -/
theorem Msigma_meet_conjugate [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} {p : ℕ} {A₀ A P : Subgroup G} (h : Hypothesis111 M p A₀ A P)
    {g : G} (hg : g ∉ M) (hAg : A ≤ MulAut.conj g • M) :
    S10.Msigma M ⊓ MulAut.conj g • M = ⊥ ∧
    S10.Msigma M ⊓ Subgroup.centralizer ((MulAut.conj g • A₀ : Subgroup G) : Set G) = ⊥ := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hApg : IsPGroup p ↥A := h.A_mem.1.isPGroup
  have hAcard : Nat.card ↥A = p ^ 2 := h.A_mem.2
  -- `M_σ` is a `σ(M)`-group, and `p ∉ σ(M)`, so `p ∤ |M_σ|`.
  have hMsM_pi : Ch03.Subgroup.IsPiGroup (S10.sigma M) (S10.Msigma M) :=
    S10.Msigma_isPiGroup M
  have hp_ndvd_Msigma : ¬ p ∣ Nat.card ↥(S10.Msigma M) := fun hdvd =>
    h.notMem_sigma (hMsM_pi p (Nat.mem_primeFactors.mpr ⟨h.prime, hdvd, Nat.card_pos.ne'⟩))
  -- Cardinality is preserved by any automorphism (used for `conj g` and `(conj g)⁻¹`).
  have hcard_conj : ∀ (φ : MulAut G) (K : Subgroup G),
      Nat.card ↥(φ • K) = Nat.card ↥K := fun φ K => by
    rw [mulAut_smul_eq_map]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective K _ φ.injective).toEquiv).symm
  -- `M` normalizes `M_σ` (`M_σ ⊴ M`: image of the normal core `O_σ(↥M)`).
  have hMnormMsM : M ≤ Subgroup.normalizer ((S10.Msigma M) : Set G) := by
    rw [S10.Msigma, OddOrder.GroupTheory.opiCoreInG]
    have hle := Subgroup.le_normalizer_map (H := Ch03.oPiCore (S10.sigma M) ↥M) M.subtype
    rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hle
  -- `A` normalizes `M_σ` (`A ≤ M ≤ N_G(M_σ)`).
  have hAnormMsM : A ≤ Subgroup.normalizer ((S10.Msigma M) : Set G) :=
    le_trans h.A_le hMnormMsM
  -- `A` normalizes `M_σ^g` (`A^{g⁻¹} ≤ M ≤ N_G(M_σ)`, conjugated back).
  have hAnormConj : A ≤ Subgroup.normalizer ((MulAut.conj g • S10.Msigma M : Subgroup G) : Set G) :=
      by
    rw [← normalizer_conj_smul g (S10.Msigma M)]
    have hconjA : (MulAut.conj g)⁻¹ • A ≤ M := by
      have := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := (MulAut.conj g)⁻¹)).mpr hAg
      rwa [inv_smul_smul] at this
    have hstep : (MulAut.conj g)⁻¹ • A ≤ Subgroup.normalizer ((S10.Msigma M) : Set G) :=
      le_trans hconjA hMnormMsM
    have := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj g)).mpr hstep
    rwa [smul_inv_smul] at this
  -- Part (b) reduces to (a): `C_G(A₀^g) ≤ M^g`, hence `M_σ ⊓ C_G(A₀^g) ≤ M_σ ⊓ M^g`.
  have hCAconj : Subgroup.centralizer ((MulAut.conj g • A₀ : Subgroup G) : Set G) ≤
      MulAut.conj g • M := by
    intro y hy
    rw [mulAut_smul_eq_map, Subgroup.mem_map]
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · -- `g⁻¹ y g ∈ M`: it centralizes `A₀`, and `C_G(A₀) ≤ N_G(A₀) ≤ M`.
      apply h.normalizer_A₀_le
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro a ha
      have hgag : (g * a * g⁻¹) ∈ (MulAut.conj g • A₀ : Subgroup G) := by
        rw [mulAut_smul_eq_map]; exact Subgroup.mem_map_of_mem _ ha
      have hya : (g * a * g⁻¹) * y = y * (g * a * g⁻¹) := hy (g * a * g⁻¹) hgag
      calc a * (g⁻¹ * y * g)
          = g⁻¹ * ((g * a * g⁻¹) * y) * g := by group
        _ = g⁻¹ * (y * (g * a * g⁻¹)) * g := by rw [hya]
        _ = (g⁻¹ * y * g) * a := by group
    · -- `(conj g)(g⁻¹ y g) = y`.
      change g * (g⁻¹ * y * g) * g⁻¹ = y
      group
  -- Main claim (a): `M_σ ⊓ M^g = ⊥`.
  have hpartA : S10.Msigma M ⊓ MulAut.conj g • M = ⊥ := by
    by_contra hne
    -- Pick a prime `q ∣ |M_σ ⊓ M^g|`; it lies in `σ(M)`.
    obtain ⟨q, hq_pf⟩ := Nat.exists_prime_and_dvd
      (show Nat.card ↥(S10.Msigma M ⊓ MulAut.conj g • M) ≠ 1 from fun h1 => hne
        (Subgroup.eq_bot_of_card_eq _ h1))
    obtain ⟨hq_prime, hq_dvd⟩ := hq_pf
    have : Fact q.Prime := ⟨hq_prime⟩
    have hq_dvd_Msigma : q ∣ Nat.card ↥(S10.Msigma M) :=
      dvd_trans hq_dvd (Subgroup.card_dvd_of_le inf_le_left)
    have hq_sigma : q ∈ S10.sigma M :=
      hMsM_pi q (Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd_Msigma, Nat.card_pos.ne'⟩)
    have hqp : q ≠ p := by rintro rfl; exact h.notMem_sigma hq_sigma
    -- `D := M_σ ⊓ M^g = M_σ ⊓ M_σ^g =: D'` (`M_σ ⊓ M^g ≤ M_σ^g` via normal-Hall absorption).
    have hDconj : S10.Msigma M ⊓ MulAut.conj g • M ≤ MulAut.conj g • S10.Msigma M := by
      have hconjD : (MulAut.conj g)⁻¹ • (S10.Msigma M ⊓ MulAut.conj g • M) ≤ S10.Msigma M := by
        apply sigma_subgroup_le_Msigma hG h.mem_maximal
        · -- `≤ M`
          rw [Subgroup.smul_inf, inv_smul_smul]
          exact inf_le_right
        · -- `IsPiGroup (σ(M))` (sub of the conjugate `σ`-group `M_σ^{g⁻¹}`).
          refine Ch03.Subgroup.IsPiGroup.le (K := (MulAut.conj g)⁻¹ • S10.Msigma M) ?_ ?_
          · rw [Subgroup.smul_inf, inv_smul_smul]; exact inf_le_left
          · intro r hr
            rw [hcard_conj] at hr; exact hMsM_pi r hr
      have := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj g)).mpr hconjD
      rwa [smul_inv_smul] at this
    set D' : Subgroup G := S10.Msigma M ⊓ MulAut.conj g • S10.Msigma M with hD'_def
    have hD_eq : S10.Msigma M ⊓ MulAut.conj g • M = D' := by
      refine le_antisymm (le_inf inf_le_left hDconj) ?_
      exact inf_le_inf_left _ ((Subgroup.pointwise_smul_le_pointwise_smul_iff
        (a := MulAut.conj g)).mpr (Subgroup.map_subtype_le _))
    have hq_dvd_D' : q ∣ Nat.card ↥D' := hD_eq ▸ hq_dvd
    -- `A` normalizes `D'` (intersection of two `A`-normalized subgroups).
    have hAnormD' : A ≤ Subgroup.normalizer (D' : Set G) :=
      le_trans (le_inf hAnormMsM hAnormConj)
        (Subgroup.inf_normalizer_le_normalizer_inf
          (H := S10.Msigma M) (K := MulAut.conj g • S10.Msigma M))
    -- Coprimality of `|A| = p²` with the `σ(M)`-orders below.
    have hCop : ∀ K : Subgroup G, ¬ p ∣ Nat.card ↥K →
        Nat.Coprime (Nat.card ↥A) (Nat.card ↥K) := fun K hK => by
      rw [hAcard]
      exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd h.prime).mpr hK)
    have hp_ndvd_conj : ¬ p ∣ Nat.card ↥(MulAut.conj g • S10.Msigma M) := by
      rw [hcard_conj]; exact hp_ndvd_Msigma
    have hp_ndvd_D' : ¬ p ∣ Nat.card ↥D' := fun hdvd =>
      hp_ndvd_Msigma (dvd_trans hdvd (Subgroup.card_dvd_of_le inf_le_left))
    -- `A`-invariant Sylow `q` `Q₀` of `D'`; nonbot since `q ∣ |D'|`.
    obtain ⟨Q₀, hQ₀, -⟩ := exists_isAInvSylowIn hApg hAnormD' (hCop D' hp_ndvd_D')
      (IsPGroup.of_bot (p := q)) bot_le (by rw [Subgroup.normalizer_eq_top]; exact le_top)
    have hQ₀_le_Msigma : Q₀ ≤ S10.Msigma M := le_trans hQ₀.1 inf_le_left
    have hQ₀_le_conj : Q₀ ≤ MulAut.conj g • S10.Msigma M := le_trans hQ₀.1 inf_le_right
    have hQ₀ne : Q₀ ≠ ⊥ := by
      intro hbot
      have := isAInvSylowIn_card_dvd hQ₀ hq_dvd_D'
      rw [hbot, Subgroup.card_bot] at this
      exact hq_prime.one_lt.ne' (Nat.eq_one_of_dvd_one this)
    -- Enlarge `Q₀` to `A`-inv Sylow `q` of `M_σ` and of `M_σ^g`.
    obtain ⟨Q₁, hQ₁, hQ₀Q₁⟩ := exists_isAInvSylowIn hApg hAnormMsM (hCop _ hp_ndvd_Msigma)
      hQ₀.2.1 hQ₀_le_Msigma hQ₀.2.2.1
    obtain ⟨Q₂, hQ₂, hQ₀Q₂⟩ := exists_isAInvSylowIn hApg hAnormConj (hCop _ hp_ndvd_conj)
      hQ₀.2.1 hQ₀_le_conj hQ₀.2.2.1
    -- Lemma 11.1(a): `Q₁ ⊓ Q₂ = ⊥`, but `Q₀ ≤ Q₁ ⊓ Q₂` and `Q₀ ≠ ⊥`. Contradiction.
    have hdisj := (invariant_sylow_disjoint hG h hg hAg hq_sigma hQ₁ hQ₂).1
    exact hQ₀ne (le_bot_iff.mp (hdisj ▸ le_inf hQ₀Q₁ hQ₀Q₂))
  exact ⟨hpartA, le_bot_iff.mp (le_trans (inf_le_inf_left _ hCAconj) hpartA.le)⟩

/-- **BG Theorem 11.3** (mmd L2955): `M_σ` は nilpotent。

証明 (BG): `g ∈ N_G(P) − N_M(P)` をとると `A₀^g ⊆ P ⊆ M` で、`A₀^g` は Corollary 11.2(b) により
`M_σ` 上に不動点自由に作用する。`A₀^g` は素数位数 `p` なので、`M_σ ⋊ A₀^g` は Frobenius 群であり、
Theorem 3.7 (`frobeniusKernelIsNilpotent`) から kernel `M_σ` は nilpotent。 -/
theorem Msigma_isNilpotent [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} {p : ℕ} {A₀ A P : Subgroup G} (h : Hypothesis111 M p A₀ A P) :
    Group.IsNilpotent ↥(S10.Msigma M) := by
  have : Fact p.Prime := ⟨h.prime⟩
  -- If `M_σ` is trivial it is nilpotent; otherwise build the Frobenius structure.
  by_cases hMsbot : S10.Msigma M = ⊥
  · rw [hMsbot]; infer_instance
  -- BG: take `g ∈ N_G(P) − N_M(P)` (here it suffices that `g ∈ N_G(P)` and `g ∉ M`).
  obtain ⟨g, hgN, hgM⟩ := SetLike.not_le_iff_exists.mp h.normalizer_P_not_le
  have hgP : MulAut.conj g • P = P := conj_smul_eq_self_of_mem_normalizer hgN
  -- `A₀^g`, contained in `P ⊆ M` since `g` normalizes `P`.
  set Ag : Subgroup G := MulAut.conj g • A₀ with hAg_def
  have hAgP : Ag ≤ P := by
    rw [hAg_def, ← hgP]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr h.A0_le_P
  have hAgM : Ag ≤ M := hAgP.trans h.P_le
  -- `A ⊆ M^g` (as `A ⊆ P = P^g ⊆ M^g`), so Corollary 11.2 applies to this `g`.
  have hAMg : A ≤ MulAut.conj g • M := by
    have hAP : A ≤ MulAut.conj g • P := by rw [hgP]; exact h.A_le_P
    exact hAP.trans (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr h.P_le)
  -- `|A₀^g| = |A₀| = p`.
  have hcard_conj : ∀ (φ : MulAut G) (K : Subgroup G), Nat.card ↥(φ • K) = Nat.card ↥K :=
    fun φ K => by
      rw [mulAut_smul_eq_map]
      exact (Nat.card_congr (Subgroup.equivMapOfInjective K _ φ.injective).toEquiv).symm
  have hAgcard : Nat.card ↥Ag = p := by rw [hAg_def, hcard_conj, h.A₀_mem.2, pow_one]
  have hAgne : Ag ≠ ⊥ := by
    intro hbot; rw [hbot, Subgroup.card_bot] at hAgcard
    exact h.prime.one_lt.ne' hAgcard.symm
  -- Corollary 11.2(b): `M_σ ∩ C_G(A₀^g) = 1` (the fixed-point-free condition).
  have hFPFcard := (Msigma_meet_conjugate hG h hgM hAMg).2
  rw [← hAg_def] at hFPFcard
  -- `p ∤ |M_σ|` (as `p ∉ σ(M)`), so `M_σ` and `A₀^g` are disjoint of coprime order.
  have hp_ndvd : ¬ p ∣ Nat.card ↥(S10.Msigma M) := fun hdvd =>
    h.notMem_sigma ((S10.Msigma_isPiGroup M) p
      (Nat.mem_primeFactors.mpr ⟨h.prime, hdvd, Nat.card_pos.ne'⟩))
  have hcop : Nat.Coprime (Nat.card ↥(S10.Msigma M)) (Nat.card ↥Ag) := by
    rw [hAgcard]; exact ((Nat.Prime.coprime_iff_not_dvd h.prime).mpr hp_ndvd).symm
  have hdisj : Disjoint (S10.Msigma M) Ag :=
    Subgroup.disjoint_of_coprime_natCard hcop
  -- `A₀^g ⊆ M ⊆ N_G(M_σ)` (since `M_σ ⊴ M`).
  have hMnormMsM : M ≤ Subgroup.normalizer ((S10.Msigma M) : Set G) := by
    rw [S10.Msigma, OddOrder.GroupTheory.opiCoreInG]
    have hle := Subgroup.le_normalizer_map (H := Ch03.oPiCore (S10.sigma M) ↥M) M.subtype
    rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hle
  have hAgnorm : Ag ≤ Subgroup.normalizer ((S10.Msigma M) : Set G) := hAgM.trans hMnormMsM
  -- `M_σ ⊔ A₀^g ⊆ M` is solvable (proper subgroup of a minimal simple group).
  have hMsol : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups h.mem_maximal
  have hsupleM : S10.Msigma M ⊔ Ag ≤ M := sup_le (S10.Msigma_le M) hAgM
  have : Group.IsSolvable ↥(S10.Msigma M ⊔ Ag) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hsupleM).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hsupleM).surjective
  -- Fixed-point-freeness as `r * n * r⁻¹ ≠ n` (using `|A₀^g| = p` prime and Cor 11.2(b)):
  -- if `n ∈ M_σ` commutes with `r ∈ A₀^g − 1`, it commutes with `⟨r⟩ = A₀^g`, so `n ∈ C_G(A₀^g)`.
  have hFPF : ∀ r ∈ Ag, r ≠ 1 → ∀ n ∈ S10.Msigma M, n ≠ 1 → r * n * r⁻¹ ≠ n := by
    intro r hrAg hr1 n hnM hn1 hcontra
    have hcomm : Commute r n := mul_inv_eq_iff_eq_mul.mp hcontra
    have hzple : Subgroup.zpowers r ≤ Ag := Subgroup.zpowers_le.mpr hrAg
    have hdvd : Nat.card ↥(Subgroup.zpowers r) ∣ p := by
      rw [← hAgcard]; exact Subgroup.card_dvd_of_le hzple
    have hne1 : Nat.card ↥(Subgroup.zpowers r) ≠ 1 := fun hh =>
      hr1 (Subgroup.zpowers_eq_bot.mp (Subgroup.eq_bot_of_card_eq _ hh))
    have hcardzp : Nat.card ↥(Subgroup.zpowers r) = p :=
      (h.prime.eq_one_or_self_of_dvd _ hdvd).resolve_left hne1
    have hzp : Subgroup.zpowers r = Ag :=
      Subgroup.eq_of_le_of_card_ge hzple (hAgcard.trans hcardzp.symm).le
    have hnC : n ∈ Subgroup.centralizer (↑Ag : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      rw [← hzp] at hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact Commute.zpow_left hcomm k
    have hmem : n ∈ S10.Msigma M ⊓ Subgroup.centralizer (↑Ag : Set G) := ⟨hnM, hnC⟩
    rw [hFPFcard] at hmem
    exact hn1 (by simpa using hmem)
  -- Apply the subgroup form of BG Theorem 3.7.
  exact OddOrder.BG.Ch1.S03c.isNilpotent_of_normalizing_primeOrder_fixedPointFree
    hAgnorm hdisj hMsbot hAgne ⟨p, h.prime, hAgcard⟩ hFPF

/-- **BG Corollary 11.4** (mmd L2959): `H ∈ ℳ(A)` で `M_σ ⊓ H_σ ≠ 1` なら `M = H`。

証明 (BG): Theorem 11.3 で `M_σ` は nilpotent。`M_σ ⊓ H_σ ≠ 1` なので Lemma 10.12(b) の対偶により
`M`, `H` は共役 (`∃ g, M^g = H`)。`H ∈ ℳ(A)` から `A ⊆ H = M^g` で、さらに `M_σ ⊓ M^g ⊇ M_σ ⊓ H_σ ≠ 1`
なので Corollary 11.2(a) の対偶から `g ∈ M`。よって `M^g = M = H`。 -/
theorem eq_of_Msigma_meet_Hsigma [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} {p : ℕ} {A₀ A P : Subgroup G} (h : Hypothesis111 M p A₀ A P)
    {H : Subgroup G} (hH : H ∈ maximalSubgroupsContaining A)
    (hne : S10.Msigma M ⊓ S10.Msigma H ≠ ⊥) :
    M = H := by
  -- Theorem 11.3: `M_σ` is nilpotent.
  have hMσnil : Group.IsNilpotent ↥(S10.Msigma M) := Msigma_isNilpotent hG h
  -- Lemma 10.12(b) contrapositive: `M_σ` nilpotent and `M_σ ⊓ H_σ ≠ ⊥` force `M`, `H` conjugate.
  obtain ⟨g, hgMH⟩ : ∃ g : G, MulAut.conj g • M = H := by
    by_contra hnc
    exact hne ((S10.disjoint_of_not_conj hG h.mem_maximal hH.1 hnc).2 hMσnil).1
  -- `A ≤ H = M^g`, so Corollary 11.2(a) applies to this `g`.
  have hAg : A ≤ MulAut.conj g • M := by rw [hgMH]; exact hH.2
  -- `M_σ ⊓ M^g ≠ ⊥`: it dominates the nonbot `M_σ ⊓ H_σ` (`H_σ ≤ H = M^g`).
  have hmeet_ne : S10.Msigma M ⊓ MulAut.conj g • M ≠ ⊥ := by
    rw [hgMH]
    intro hbot
    apply hne
    have hle : S10.Msigma M ⊓ S10.Msigma H ≤ S10.Msigma M ⊓ H :=
      inf_le_inf_left (S10.Msigma M) (S10.Msigma_le H)
    rw [hbot] at hle
    exact le_bot_iff.mp hle
  -- Corollary 11.2(a) contrapositive: `g ∈ M`.
  have hgM : g ∈ M := by
    by_contra hgM
    exact hmeet_ne (Msigma_meet_conjugate hG h hgM hAg).1
  -- `g ∈ M ⊆ N_G(M)`, so `M^g = M`; hence `M = M^g = H`.
  calc M = MulAut.conj g • M :=
        (conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hgM)).symm
    _ = H := hgMH

/-- Conjugation commutes with centralizers of subgroups: `C_G(H)^g = C_G(H^g)`. -/
private theorem centralizer_conj_smul (g : G) (H : Subgroup G) :
    MulAut.conj g • Subgroup.centralizer ((H : Subgroup G) : Set G)
      = Subgroup.centralizer ((MulAut.conj g • H : Subgroup G) : Set G) := by
  ext c
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [Subgroup.mem_centralizer_iff]
  have hinv : ∀ d : G, (MulAut.conj g)⁻¹ • d = g⁻¹ * d * g := by
    intro d
    rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
  constructor
  · intro hc y hy
    rw [mulAut_smul_eq_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have h1 := hc x hx
    rw [hinv c] at h1
    change (MulAut.conj g) x * c = c * (MulAut.conj g) x
    rw [MulAut.conj_apply]
    calc g * x * g⁻¹ * c = g * (x * (g⁻¹ * c * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * c * g) * x) * g⁻¹ := by rw [h1]
      _ = c * (g * x * g⁻¹) := by group
  · intro hc y hy
    have hgy : (MulAut.conj g) y ∈ (MulAut.conj g • H : Subgroup G) := by
      rw [mulAut_smul_eq_map]
      exact ⟨y, hy, rfl⟩
    have h1 := hc _ hgy
    rw [MulAut.conj_apply] at h1
    rw [hinv c]
    calc y * (g⁻¹ * c * g) = g⁻¹ * ((g * y * g⁻¹) * c) * g := by group
      _ = g⁻¹ * (c * (g * y * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * c * g * y := by group

/-- A conjugate of a nontrivial subgroup is nontrivial. -/
private theorem conj_smul_ne_bot {H : Subgroup G} (g : G) (hH : H ≠ ⊥) :
    MulAut.conj g • H ≠ ⊥ := by
  intro hbot
  apply hH
  rw [mulAut_smul_eq_map] at hbot
  rwa [Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective] at hbot

/-- `C_G(⟨x⟩) = C_G(x)`. -/
private theorem centralizer_zpowers_eq_singleton (x : G) :
    Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)
      = Subgroup.centralizer ({x} : Set G) := by
  ext c
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro hc y hy
    rw [Set.mem_singleton_iff] at hy
    exact hy ▸ hc x (Subgroup.mem_zpowers x)
  · intro hc y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((show Commute x c from hc x rfl).zpow_left k).eq

/-- `IsAInvSylowIn` transports along conjugation. -/
private theorem isAInvSylowIn_conj_smul {q : ℕ} {A Q H : Subgroup G} (g : G)
    (h : IsAInvSylowIn q A Q H) :
    IsAInvSylowIn q (MulAut.conj g • A) (MulAut.conj g • Q) (MulAut.conj g • H) := by
  obtain ⟨hQH, hQp, hAN, hmax⟩ := h
  refine ⟨Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hQH, ?_, ?_, ?_⟩
  · rw [mulAut_smul_eq_map]
    exact hQp.of_equiv (Subgroup.equivMapOfInjective Q _ (MulAut.conj g).injective)
  · rw [← normalizer_conj_smul]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hAN
  · intro R hQR hRH hRq
    have h1 : Q ≤ (MulAut.conj g)⁻¹ • R := by
      have h0 : (MulAut.conj g)⁻¹ • (MulAut.conj g • Q) ≤ (MulAut.conj g)⁻¹ • R :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hQR
      rwa [inv_smul_smul] at h0
    have h2 : (MulAut.conj g)⁻¹ • R ≤ H := by
      have h0 : (MulAut.conj g)⁻¹ • R ≤ (MulAut.conj g)⁻¹ • (MulAut.conj g • H) :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hRH
      rwa [inv_smul_smul] at h0
    have h3 : IsPGroup q ↥((MulAut.conj g)⁻¹ • R) := by
      rw [← map_inv, mulAut_smul_eq_map]
      exact hRq.of_equiv (Subgroup.equivMapOfInjective R _ (MulAut.conj g⁻¹).injective)
    have h4 := hmax _ h1 h2 h3
    rw [← h4, smul_inv_smul]

/-- Commutativity transports along a group isomorphism. -/
theorem isMulCommutative_of_mulEquiv {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) (hH : IsMulCommutative H) : IsMulCommutative K :=
  ⟨⟨fun a b => by
    have := congrArg e (hH.is_comm.comm (e.symm a) (e.symm b))
    rwa [map_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply] at this⟩⟩

/-- **BG Theorem 11.5** (mmd L2963): `M` の Sylow `p`-部分群は abelian。

証明: `P` が nonabelian と仮定。`g ∈ N_G(P) − M`、`q ∈ σ(M)`、`Q₁` を `M_σ` の `P`-不変
Sylow `q`-部分群、`Q₂ = Q₁^g` とする (`g ∈ N_G(P)` ゆえ `Q₂` も `P`-不変、特に `A`-不変)。
Prop 1.16 (`exists_mem_inf_centralizer_ne_bot_of_not_isCyclic`) で `C_{Q₁}(X₁) ≠ 1`,
`C_{Q₂}(X₂) ≠ 1` なる `X₁, X₂ ∈ ℰ¹(A)` が取れ、Lemma 11.1(b) から `C_{Q₁}(X₂) = 1`、
よって `X₂` は `X₁` と `P`-共役でない (`Q₁` は `P`-不変)。Lemma 10.13(c) により
`ℰ¹(A) − {Z₀ = Ω₁(Z(P))}` は `P`-共役で推移的なので `X₁ = Z₀` または `X₂ = Z₀`。しかし
`Z₀` は `g`-不変なので `C(Z₀) ⊓ Q₂ = (C(Z₀) ⊓ Q₁)^g` となり、どちらの場合も
`C(Z₀) ⊓ Q₁ ≠ 1 ≠ C(Z₀) ⊓ Q₂` — Lemma 11.1(b) に矛盾。最後に `P` は `M` の Sylow
(`P_sylow`) なので Sylow 共役で任意の `S ∈ Syl_p(M)` が abelian。 -/
theorem sylow_p_isCommutative [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} {p : ℕ} {A₀ A P : Subgroup G} (h : Hypothesis111 M p A₀ A P)
    (S : Sylow p ↥M) :
    IsMulCommutative (S : Subgroup ↥M) := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have hAea : A.IsElementaryAbelian p := h.A_mem.1
  have hAcard : Nat.card ↥A = p ^ 2 := h.A_mem.2
  -- Step 1: the distinguished Sylow `P` is abelian.
  have hPcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    by_contra hPnc
    have hPnonab : ¬ IsMulCommutative ↥P := by
      intro hab
      apply hPnc
      intro x hx y hy
      have hc := hab.is_comm.comm (⟨x, hx⟩ : ↥P) ⟨y, hy⟩
      simpa using congrArg Subtype.val hc
    obtain ⟨g, hgN, hgM⟩ := SetLike.not_le_iff_exists.mp h.normalizer_P_not_le
    -- `q ∈ σ(M)` via `M_σ ≠ ⊥`.
    have hMσne : S10.Msigma M ≠ ⊥ := S10.Msigma_ne_bot hG h.mem_maximal
    have : Nontrivial ↥(S10.Msigma M) := (Subgroup.nontrivial_iff_ne_bot _).mpr hMσne
    obtain ⟨q, hq⟩ : ∃ q, q ∈ (Nat.card ↥(S10.Msigma M)).primeFactors := by
      rcases (Nat.card ↥(S10.Msigma M)).primeFactors.eq_empty_or_nonempty with h0 | h0
      · rcases Nat.primeFactors_eq_empty.mp h0 with h1 | h1
        · exact absurd h1 Nat.card_pos.ne'
        · exact absurd h1 Finite.one_lt_card.ne'
      · exact h0
    have : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hq⟩
    have hqσ : q ∈ S10.sigma M := S10.Msigma_isPiGroup M q hq
    have hpq : p ≠ q := fun hpq => h.notMem_sigma (hpq ▸ hqσ)
    -- `P` normalizes `M_σ`, coprimely.
    have hM_norm_Mσ : M ≤ Subgroup.normalizer ((S10.Msigma M) : Set G) := by
      rw [S10.Msigma, OddOrder.GroupTheory.opiCoreInG]
      have hle := Subgroup.le_normalizer_map (H := Ch03.oPiCore (S10.sigma M) ↥M) M.subtype
      rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hle
    have hP_norm_Mσ : P ≤ Subgroup.normalizer ((S10.Msigma M) : Set G) :=
      h.P_le.trans hM_norm_Mσ
    have hp_ndvd_Mσ : ¬ p ∣ Nat.card ↥(S10.Msigma M) := fun hdvd =>
      h.notMem_sigma (S10.Msigma_isPiGroup M p
        (Nat.mem_primeFactors.mpr ⟨h.prime, hdvd, Nat.card_pos.ne'⟩))
    have hcopP : Nat.Coprime (Nat.card ↥P) (Nat.card ↥(S10.Msigma M)) := by
      obtain ⟨n, hn⟩ := h.P_pgroup.exists_card_eq
      rw [hn]
      exact ((Nat.Prime.coprime_iff_not_dvd h.prime).mpr hp_ndvd_Mσ).pow_left n
    -- `Q₁`: a `P`-invariant Sylow `q`-subgroup of `M_σ`; `Q₂ := Q₁^g`.
    have hbot_pg : IsPGroup q ↥(⊥ : Subgroup G) :=
      IsPGroup.of_card (n := 0) (by rw [Subgroup.card_bot, pow_zero])
    obtain ⟨Q₁, hQ₁P, -⟩ := exists_isAInvSylowIn h.P_pgroup hP_norm_Mσ hcopP
      (P₀ := ⊥) hbot_pg bot_le
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
    have hQ₁A : IsAInvSylowIn q A Q₁ (S10.Msigma M) := hQ₁P.of_le h.A_le_P
    have hgP : MulAut.conj g • P = P := conj_smul_eq_self_of_mem_normalizer hgN
    have hQ₂P : IsAInvSylowIn q P (MulAut.conj g • Q₁)
        (MulAut.conj g • S10.Msigma M) := by
      have htr := isAInvSylowIn_conj_smul g hQ₁P
      rwa [hgP] at htr
    have hQ₂A : IsAInvSylowIn q A (MulAut.conj g • Q₁)
        (MulAut.conj g • S10.Msigma M) := hQ₂P.of_le h.A_le_P
    -- `A ⊆ M^g` and Lemma 11.1.
    have hAgM : A ≤ MulAut.conj g • M := by
      refine le_trans h.A_le_P (le_trans (le_of_eq hgP.symm) ?_)
      exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr h.P_le
    obtain ⟨-, hkey⟩ := invariant_sylow_disjoint hG h hgM hAgM hqσ hQ₁A hQ₂A
    -- `A` is noncyclic abelian, coprime to the `Qᵢ`.
    have hAcommI : IsMulCommutative ↥A := ⟨⟨fun x y => hAea.1 x y⟩⟩
    have hAnc : ¬ IsCyclic ↥A := by
      intro hcyc
      have hexp : Monoid.exponent ↥A = p ^ 2 := by
        rw [IsCyclic.exponent_eq_card, hAcard]
      have hdvd : Monoid.exponent ↥A ∣ p :=
        Monoid.exponent_dvd_of_forall_pow_eq_one hAea.2
      rw [hexp] at hdvd
      have h1 := Nat.le_of_dvd h.prime.pos hdvd
      have h2 := h.prime.one_lt
      nlinarith
    have hQcop : ∀ {Q : Subgroup G}, IsPGroup q ↥Q →
        Nat.Coprime (Nat.card ↥A) (Nat.card ↥Q) := by
      intro Q hQpg
      obtain ⟨k, hk⟩ := hQpg.exists_card_eq
      rw [hAcard, hk]
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes h.prime Fact.out).mpr hpq)
    -- `Q₁ ≠ ⊥ ≠ Q₂`.
    have hq_dvd_Mσ : q ∣ Nat.card ↥(S10.Msigma M) := (Nat.mem_primeFactors.mp hq).2.1
    have hQ₁ne : Q₁ ≠ ⊥ := by
      intro hbot
      have hd := isAInvSylowIn_card_dvd hQ₁A hq_dvd_Mσ
      rw [hbot, Subgroup.card_bot] at hd
      exact (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp hd)
    have hQ₂ne : MulAut.conj g • Q₁ ≠ ⊥ := conj_smul_ne_bot g hQ₁ne
    -- `X₁, X₂ ∈ ℰ¹(A)` with nontrivial centralizers in `Q₁`, `Q₂` (Prop 1.16).
    obtain ⟨x₁, hx₁A, hx₁ne, hx₁C⟩ :=
      Ch2.S07.exists_mem_inf_centralizer_ne_bot_of_not_isCyclic hQ₁A.2.2.1 hAnc
        (hQcop hQ₁A.2.1) hQ₁ne
    obtain ⟨x₂, hx₂A, hx₂ne, hx₂C⟩ :=
      Ch2.S07.exists_mem_inf_centralizer_ne_bot_of_not_isCyclic hQ₂A.2.2.1 hAnc
        (hQcop hQ₂A.2.1) hQ₂ne
    have hordx : ∀ x ∈ A, x ≠ (1 : G) → Nat.card ↥(Subgroup.zpowers x) = p := by
      intro x hx hxne
      rw [Nat.card_zpowers]
      refine orderOf_eq_prime ?_ hxne
      have h1 := congrArg Subtype.val (hAea.2 ⟨x, hx⟩)
      rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h1
    have hX₁mem : Subgroup.zpowers x₁ ∈ elemAbelianOfRank G p 1 :=
      ⟨Subgroup.IsElementaryAbelian.of_card_prime (hordx x₁ hx₁A hx₁ne),
        by rw [pow_one]; exact hordx x₁ hx₁A hx₁ne⟩
    have hX₂mem : Subgroup.zpowers x₂ ∈ elemAbelianOfRank G p 1 :=
      ⟨Subgroup.IsElementaryAbelian.of_card_prime (hordx x₂ hx₂A hx₂ne),
        by rw [pow_one]; exact hordx x₂ hx₂A hx₂ne⟩
    -- Lemma 10.13(c): transitivity off `Z₀ = Ω₁(Z(P))`.
    have hpG' : p ∈ (Nat.card G).primeFactors := by
      refine Nat.mem_primeFactors.mpr ⟨h.prime, ?_, Nat.card_pos.ne'⟩
      refine dvd_trans ?_ (Subgroup.card_subgroup_dvd_card A)
      rw [hAcard]
      exact dvd_pow_self p two_ne_zero
    have hA₀ne : A₀ ≠ S10.omega1CenterInG P p := by
      intro heq
      apply hgM
      apply h.normalizer_A₀_le
      rw [heq]
      exact S10.normalizer_le_normalizer_omega1CenterInG P p hgN
    obtain ⟨hZ₀line, -, htrans⟩ :=
      S10.nonabelian_pSubgroup_rankTwo_elemAbelian_structure hG hpG' h.A_mem h.A_maximal
        h.P_pgroup hPnonab h.A_le_P ⟨h.A₀_mem, h.A₀_le_A⟩ hA₀ne
    -- The two centralizer intersections, in subgroup-of-`A` form.
    have hX₁Q₁ne : Subgroup.centralizer
        ((Subgroup.zpowers x₁ : Subgroup G) : Set G) ⊓ Q₁ ≠ ⊥ := by
      rw [centralizer_zpowers_eq_singleton, inf_comm]
      exact hx₁C
    have hX₂Q₂ne : Subgroup.centralizer
        ((Subgroup.zpowers x₂ : Subgroup G) : Set G) ⊓ (MulAut.conj g • Q₁) ≠ ⊥ := by
      rw [centralizer_zpowers_eq_singleton, inf_comm]
      exact hx₂C
    have hX₂Q₁ : Subgroup.centralizer
        ((Subgroup.zpowers x₂ : Subgroup G) : Set G) ⊓ Q₁ = ⊥ :=
      (hkey _ hX₂mem (Subgroup.zpowers_le.mpr hx₂A)).resolve_right hX₂Q₂ne
    -- `X₁ = Z₀` or `X₂ = Z₀` (otherwise Lemma 10.13(c) would conjugate `X₁` to `X₂` in `P`).
    have hcases : Subgroup.zpowers x₁ = S10.omega1CenterInG P p ∨
        Subgroup.zpowers x₂ = S10.omega1CenterInG P p := by
      by_contra hcon
      push Not at hcon
      obtain ⟨n, hnNA, hn⟩ := htrans _ _
        ⟨hX₁mem, Subgroup.zpowers_le.mpr hx₁A⟩ hcon.1
        ⟨hX₂mem, Subgroup.zpowers_le.mpr hx₂A⟩ hcon.2
      have hnQ₁ : MulAut.conj n • Q₁ = Q₁ :=
        conj_smul_eq_self_of_mem_normalizer (hQ₁P.2.2.1 hnNA.2)
      have heq2 : Subgroup.centralizer
          ((Subgroup.zpowers x₂ : Subgroup G) : Set G) ⊓ Q₁
          = MulAut.conj n • (Subgroup.centralizer
            ((Subgroup.zpowers x₁ : Subgroup G) : Set G) ⊓ Q₁) := by
        rw [Subgroup.smul_inf, hnQ₁, centralizer_conj_smul, hn]
      rw [heq2] at hX₂Q₁
      exact conj_smul_ne_bot n hX₁Q₁ne hX₂Q₁
    -- `Z₀` is `g`-stable, so both `C(Z₀) ⊓ Q₁` and `C(Z₀) ⊓ Q₂` are nontrivial — contradiction.
    have hgZ₀ : MulAut.conj g • S10.omega1CenterInG P p = S10.omega1CenterInG P p :=
      conj_smul_eq_self_of_mem_normalizer
        (S10.normalizer_le_normalizer_omega1CenterInG P p hgN)
    have heqZ : Subgroup.centralizer
        ((S10.omega1CenterInG P p : Subgroup G) : Set G) ⊓ (MulAut.conj g • Q₁)
        = MulAut.conj g • (Subgroup.centralizer
          ((S10.omega1CenterInG P p : Subgroup G) : Set G) ⊓ Q₁) := by
      rw [Subgroup.smul_inf, centralizer_conj_smul, hgZ₀]
    have hkeyZ₀ := hkey _ hZ₀line.1 hZ₀line.2
    rcases hcases with hc1 | hc2
    · rw [hc1] at hX₁Q₁ne
      rcases hkeyZ₀ with hk | hk
      · exact hX₁Q₁ne hk
      · rw [heqZ] at hk
        exact conj_smul_ne_bot g hX₁Q₁ne hk
    · rw [hc2] at hX₂Q₂ne hX₂Q₁
      rw [heqZ, hX₂Q₁, mulAut_smul_eq_map, Subgroup.map_bot] at hX₂Q₂ne
      exact hX₂Q₂ne rfl
  -- Step 2: `P` is the Sylow `p`-subgroup of `M` up to conjugacy; transfer commutativity.
  have hPab : IsMulCommutative ↥P :=
    ⟨⟨fun x y => Subtype.ext (by
      simp only [Subgroup.coe_mul]
      exact hPcomm x x.2 y y.2)⟩⟩
  obtain ⟨T, hPT⟩ := h.P_pgroup.comap_subtype.exists_le_sylow (G := M)
  have hTmap : (T : Subgroup ↥M).map M.subtype = P := by
    refine h.P_sylow _ ?_ (Subgroup.map_subtype_le _) (T.2.map M.subtype)
    rw [← Subgroup.map_subgroupOf_eq_of_le h.P_le]
    exact Subgroup.map_mono hPT
  have hTeq : (T : Subgroup ↥M) = P.subgroupOf M := by
    rw [← hTmap, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  have hTab : IsMulCommutative ↥(T : Subgroup ↥M) := by
    rw [hTeq]
    exact isMulCommutative_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.P_le).symm hPab
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq ↥M T S
  have hSeq : (S : Subgroup ↥M) = (T : Subgroup ↥M).map (MulAut.conj m : ↥M →* ↥M) := by
    rw [← hm, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  rw [hSeq]
  exact isMulCommutative_of_mulEquiv
    (Subgroup.equivMapOfInjective _ _ (MulAut.conj m).injective) hTab

/-- **BG Corollary 11.6 (a)(b)** (mmd L2977): (a) `A = Ω₁(P)`、(b) `C_{M_σ}(A) = 1`。
原典 (c) は同ファイルの `exists_distinct_conj_lines`、3 条項を書籍の形に束ねたものが
`bgCor116` (本ファイル末尾)。

証明: Theorem 11.5 で `P` は abelian。(a) `Ω₁(P)` の生成元 (exp-`p` 元) は `A` を中心化する
ので極大性により `A` に落ち、逆向きは自明。(b) `g ∈ N_G(P) − M` を取ると `Ω₁(P)` は
characteristic ゆえ `g` は `A` を正規化し、`A₀^g ≤ A`; Corollary 11.2(b) の
`M_σ ⊓ C_G(A₀^g) = 1` に `C_G(A) ≤ C_G(A₀^g)` を合わせる。 -/
theorem omega1_eq_and_centralizer_trivial [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} {p : ℕ} {A₀ A P : Subgroup G} (h : Hypothesis111 M p A₀ A P) :
    A = (Omega ↥P p 1).map P.subtype ∧
    Subgroup.centralizer (A : Set G) ⊓ S10.Msigma M = ⊥ := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have hAea : A.IsElementaryAbelian p := h.A_mem.1
  -- `P` is abelian (Theorem 11.5, transported from the Sylow `T` with `T.map = P`).
  obtain ⟨T, hPT⟩ := h.P_pgroup.comap_subtype.exists_le_sylow (G := M)
  have hTmap : (T : Subgroup ↥M).map M.subtype = P := by
    refine h.P_sylow _ ?_ (Subgroup.map_subtype_le _) (T.2.map M.subtype)
    rw [← Subgroup.map_subgroupOf_eq_of_le h.P_le]
    exact Subgroup.map_mono hPT
  have hPab : IsMulCommutative ↥P := by
    have hTab := sylow_p_isCommutative hG h T
    have e : ↥(T : Subgroup ↥M) ≃* ↥P := by
      rw [← hTmap]
      exact Subgroup.equivMapOfInjective _ _ M.subtype_injective
    exact isMulCommutative_of_mulEquiv e hTab
  have hPcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have hc := hPab.is_comm.comm (⟨x, hx⟩ : ↥P) ⟨y, hy⟩
    simpa using congrArg Subtype.val hc
  -- exp-`p` elements of `P` lie in `A` (maximality of `A`, `P` abelian).
  have htrap : ∀ x ∈ P, x ^ p = 1 → x ∈ A := by
    intro x hx hxp
    rcases eq_or_ne x 1 with rfl | hxne
    · exact A.one_mem
    have hzx : (Subgroup.zpowers x).IsElementaryAbelian p :=
      Subgroup.IsElementaryAbelian.of_card_prime
        (by rw [Nat.card_zpowers, orderOf_eq_prime hxp hxne])
    have hA_le_C : A ≤ Subgroup.centralizer
        ((Subgroup.zpowers x : Subgroup G) : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((show Commute x a from hPcomm x hx a (h.A_le_P ha)).zpow_left k).eq
    have hsup : (A ⊔ Subgroup.zpowers x).IsElementaryAbelian p :=
      hAea.sup_of_le_centralizer hzx hA_le_C
    have heq := h.A_maximal.2 _ hsup le_sup_left
    exact heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  -- (a)
  have ha_eq : A = (Omega ↥P p 1).map P.subtype := by
    apply le_antisymm
    · intro a ha
      refine ⟨⟨a, h.A_le_P ha⟩, Omega.mem_of_pow_eq_one ?_, rfl⟩
      rw [pow_one]
      refine Subtype.ext ?_
      rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      have h1 := congrArg Subtype.val (hAea.2 ⟨a, ha⟩)
      rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h1
    · rw [Subgroup.map_le_iff_le_comap, Omega, Subgroup.closure_le]
      intro z hz
      rw [Set.mem_ofPred_eq, pow_one] at hz
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      refine htrap (P.subtype z) z.2 ?_
      rw [← map_pow, hz, map_one]
  refine ⟨ha_eq, ?_⟩
  -- (b)
  obtain ⟨g, hgN, hgM⟩ := SetLike.not_le_iff_exists.mp h.normalizer_P_not_le
  have hgA : MulAut.conj g • A = A := by
    rw [ha_eq]
    exact conj_smul_eq_self_of_mem_normalizer
      (OddOrder.BG.AppB.normalizer_le_normalizer_map_of_characteristic (K := P)
        (W := Omega ↥P p 1) hgN)
  have hA₀gA : MulAut.conj g • A₀ ≤ A := by
    rw [← hgA]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr h.A₀_le_A
  have hAgM : A ≤ MulAut.conj g • M := by
    have hgP : MulAut.conj g • P = P := conj_smul_eq_self_of_mem_normalizer hgN
    refine le_trans h.A_le_P (le_trans (le_of_eq hgP.symm) ?_)
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr h.P_le
  have h112 := (Msigma_meet_conjugate hG h hgM hAgM).2
  rw [eq_bot_iff]
  intro c hc
  have hcC : c ∈ S10.Msigma M ⊓ Subgroup.centralizer
      ((MulAut.conj g • A₀ : Subgroup G) : Set G) :=
    ⟨hc.2, Subgroup.centralizer_le (fun y hy => hA₀gA hy) hc.1⟩
  rw [h112] at hcC
  exact hcC

/-- **BG Corollary 11.6(c)** (mmd L2977): there are `A₁ = A₀^{g₁} ≠ A₂ = A₀^{g₂}`
(`g₁, g₂ ∈ N_G(P) − M`) with `A = A₁ × A₂` and `C_{M_σ}(A₁) = C_{M_σ}(A₂) = 1`.

`|N_G(P) : N_M(P)|` is odd (it divides the odd `|G|`) and `> 1` (`N_G(P) ⊄ M`), hence `≥ 3`;
so there are `g₁, g₂ ∈ N_G(P) − M` in distinct cosets of `N_G(P) ⊓ M`, giving
`g₂⁻¹g₁ ∉ M ⊇ N_G(A₀)` and `A₀^{g₁} ≠ A₀^{g₂}`. Both lie in `A = Ω₁(P) ⊴ N_G(P)`
(Corollary 11.6(a)), and Corollary 11.2(b) kills both `M_σ`-centralizers. -/
theorem exists_distinct_conj_lines [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} {p : ℕ} {A₀ A P : Subgroup G} (h : Hypothesis111 M p A₀ A P) :
    ∃ A₁ A₂ : Subgroup G, A₁ ≤ A ∧ A₂ ≤ A ∧ A₁ ≠ A₂ ∧
      Nat.card ↥A₁ = p ∧ Nat.card ↥A₂ = p ∧ A₁ ⊔ A₂ = A ∧ A₁ ⊓ A₂ = ⊥ ∧
      Subgroup.centralizer (A₁ : Set G) ⊓ S10.Msigma M = ⊥ ∧
      Subgroup.centralizer (A₂ : Set G) ⊓ S10.Msigma M = ⊥ := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have hAcard : Nat.card ↥A = p ^ 2 := h.A_mem.2
  set N : Subgroup G := Subgroup.normalizer (P : Set G) with hNdef
  set H : Subgroup ↥N := (N ⊓ M).subgroupOf N with hHdef
  -- `[N_G(P) : N_G(P) ⊓ M] ≥ 3`.
  have hidx_ne_one : H.index ≠ 1 := by
    intro h1
    apply h.normalizer_P_not_le
    intro x hx
    have hxH : (⟨x, hx⟩ : ↥N) ∈ H := by
      rw [Subgroup.index_eq_one] at h1
      rw [h1]
      exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp hxH).2
  have hidx_odd : Odd H.index := by
    refine (hG.odd.of_dvd_nat ?_)
    exact (Subgroup.index_dvd_card H).trans (Subgroup.card_subgroup_dvd_card N)
  have hidx3 : 3 ≤ H.index := by
    obtain ⟨k, hk⟩ := hidx_odd
    have h1 : H.index ≠ 1 := hidx_ne_one
    omega
  -- two elements of `N − M` in distinct `H`-cosets.
  obtain ⟨g₁, hg₁N, hg₁M, g₂, hg₂N, hg₂M, hg₁₂⟩ :
      ∃ g₁ ∈ N, g₁ ∉ M ∧ ∃ g₂ ∈ N, g₂ ∉ M ∧ g₂⁻¹ * g₁ ∉ M := by
    by_contra hcon
    push Not at hcon
    -- then `N` is covered by two cosets of `H`, so the index is `≤ 2`.
    obtain ⟨w, hwN, hwM⟩ : ∃ w ∈ N, w ∉ M := by
      by_contra hcov
      push Not at hcov
      exact h.normalizer_P_not_le (fun x hx => hcov x hx)
    have hsurj : Function.Surjective (Fin.cases (motive := fun _ => ↥N ⧸ H)
        (QuotientGroup.mk 1) (fun _ => QuotientGroup.mk ⟨w, hwN⟩) : Fin 2 → ↥N ⧸ H) := by
      intro x
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      by_cases hgM : (g : G) ∈ M
      · refine ⟨0, ?_⟩
        rw [Fin.cases_zero]
        apply (QuotientGroup.eq (s := H)).mpr
        refine Subgroup.mem_subgroupOf.mpr ⟨((1 : ↥N)⁻¹ * g).2, ?_⟩
        simpa using hgM
      · refine ⟨1, ?_⟩
        rw [show ((1 : Fin 2)) = Fin.succ 0 from rfl, Fin.cases_succ]
        apply (QuotientGroup.eq (s := H)).mpr
        have hmem : w⁻¹ * (g : G) ∈ M := hcon g g.2 hgM w hwN hwM
        refine Subgroup.mem_subgroupOf.mpr ⟨((⟨w, hwN⟩ : ↥N)⁻¹ * g).2, ?_⟩
        simpa using hmem
    have hcard_le := Nat.card_le_card_of_surjective _ hsurj
    have h2 : Nat.card (Fin (1 + 1)) = 2 := by simp
    have hidx_eq : H.index = Nat.card (↥N ⧸ H) := rfl
    omega
  -- `g₁, g₂` normalize `A` (Corollary 11.6(a): `A = Ω₁(P)` is characteristic).
  obtain ⟨haΩ, -⟩ := omega1_eq_and_centralizer_trivial hG h
  have hgA : ∀ g ∈ N, MulAut.conj g • A = A := by
    intro g hg
    rw [haΩ]
    exact conj_smul_eq_self_of_mem_normalizer
      (OddOrder.BG.AppB.normalizer_le_normalizer_map_of_characteristic (K := P)
        (W := Omega ↥P p 1) hg)
  have hA₀card : Nat.card ↥A₀ = p := by
    have := h.A₀_mem.2
    rwa [pow_one] at this
  have hconj_card : ∀ g : G, Nat.card ↥(MulAut.conj g • A₀ : Subgroup G) = p := by
    intro g
    rw [mulAut_smul_eq_map,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hA₀card
  have hconj_le : ∀ g ∈ N, MulAut.conj g • A₀ ≤ A := by
    intro g hg
    rw [← hgA g hg]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr h.A₀_le_A
  -- the two conjugate lines are distinct.
  have hne : MulAut.conj g₁ • A₀ ≠ MulAut.conj g₂ • A₀ := by
    intro heq
    apply hg₁₂
    apply h.normalizer_A₀_le
    have hstab : MulAut.conj (g₂⁻¹ * g₁) • A₀ = A₀ := by
      rw [map_mul, mul_smul, heq, map_inv, inv_smul_smul]
    exact mem_normalizer_of_conj_smul_eq_self hstab
  -- `A = A₁ ⊔ A₂` and `A₁ ⊓ A₂ = ⊥` (two distinct order-`p` lines in the `p²`-group `A`).
  have hinf : MulAut.conj g₁ • A₀ ⊓ MulAut.conj g₂ • A₀ = ⊥ := by
    by_contra hbot
    obtain ⟨x, hx, hx1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hbot
    have hzle₁ : Subgroup.zpowers x ≤ MulAut.conj g₁ • A₀ := Subgroup.zpowers_le.mpr hx.1
    have hzle₂ : Subgroup.zpowers x ≤ MulAut.conj g₂ • A₀ := Subgroup.zpowers_le.mpr hx.2
    have hzcard : Nat.card ↥(Subgroup.zpowers x) = p := by
      have hdvd : Nat.card ↥(Subgroup.zpowers x) ∣ p := by
        rw [← hconj_card g₁]
        exact Subgroup.card_dvd_of_le hzle₁
      rcases (Nat.dvd_prime Fact.out).mp hdvd with h1 | hp
      · exact absurd (Subgroup.card_eq_one.mp h1)
          (fun hb => hx1 (Subgroup.zpowers_eq_bot.mp hb))
      · exact hp
    exact hne ((Subgroup.eq_of_le_of_card_ge hzle₁
        (by rw [hconj_card, hzcard])).symm.trans
      (Subgroup.eq_of_le_of_card_ge hzle₂ (by rw [hconj_card, hzcard])))
  have hsup : MulAut.conj g₁ • A₀ ⊔ MulAut.conj g₂ • A₀ = A := by
    have hsupA : MulAut.conj g₁ • A₀ ⊔ MulAut.conj g₂ • A₀ ≤ A :=
      sup_le (hconj_le g₁ hg₁N) (hconj_le g₂ hg₂N)
    have hdvd1 : p ∣ Nat.card ↥(MulAut.conj g₁ • A₀ ⊔ MulAut.conj g₂ • A₀) := by
      rw [← hconj_card g₁]
      exact Subgroup.card_dvd_of_le le_sup_left
    have hdvd2 : Nat.card ↥(MulAut.conj g₁ • A₀ ⊔ MulAut.conj g₂ • A₀) ∣ p ^ 2 := by
      rw [← hAcard]
      exact Subgroup.card_dvd_of_le hsupA
    obtain ⟨k, hk2, hkeq⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd2
    interval_cases k
    · rw [hkeq, pow_zero] at hdvd1
      exact absurd (Nat.dvd_one.mp hdvd1) (Fact.out : p.Prime).ne_one
    · exfalso
      have hXeq : MulAut.conj g₁ • A₀ = MulAut.conj g₁ • A₀ ⊔ MulAut.conj g₂ • A₀ :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hconj_card, hkeq, pow_one])
      have hYX : MulAut.conj g₂ • A₀ ≤ MulAut.conj g₁ • A₀ := hXeq ▸ le_sup_right
      exact hne (Subgroup.eq_of_le_of_card_ge hYX
        (by rw [hconj_card, hconj_card])).symm
    · exact Subgroup.eq_of_le_of_card_ge hsupA (by rw [hAcard, hkeq])
  -- Corollary 11.2(b) kills both centralizers.
  have hcent : ∀ g ∈ N, g ∉ M →
      Subgroup.centralizer ((MulAut.conj g • A₀ : Subgroup G) : Set G)
        ⊓ S10.Msigma M = ⊥ := by
    intro g hg hgM
    have hAgM : A ≤ MulAut.conj g • M := by
      have hgP : MulAut.conj g • P = P := conj_smul_eq_self_of_mem_normalizer hg
      refine le_trans h.A_le_P (le_trans (le_of_eq hgP.symm) ?_)
      exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr h.P_le
    have h112 := (Msigma_meet_conjugate hG h hgM hAgM).2
    rw [inf_comm]
    exact h112
  exact ⟨MulAut.conj g₁ • A₀, MulAut.conj g₂ • A₀,
    hconj_le g₁ hg₁N, hconj_le g₂ hg₂N, hne, hconj_card g₁, hconj_card g₂,
    hsup, hinf, hcent g₁ hg₁N hg₁M, hcent g₂ hg₂N hg₂M⟩

end OddOrder.BG.Ch3.S11


