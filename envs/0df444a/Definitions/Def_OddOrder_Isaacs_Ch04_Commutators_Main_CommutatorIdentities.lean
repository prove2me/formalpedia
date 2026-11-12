-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorIdentities
-- name    : OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorIdentities
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:07:24.888476+00:00
-- url     : https://prove2.me/theorems/503fb69b-9a9b-4fe2-90bc-0474def263d1
-- title:
--   Isaacs §4A (part 1): commutator identities, Lemmas 4.5 and 4.6
-- statement:
--   Formalizes the first part of Isaacs, *Finite Group Theory*, §4A (pp. 113–122): commutator identities, coatom lemmas, and Lemmas 4.5 and 4.6.
--
--   Main definitions: `frattini_le_of_isElementaryAbelian_quotient_of_pgroup` (Lemma 4.5 forward direction: for a finite $p$-group $P$ and $N\trianglelefteq P$ with $P/N$ elementary abelian, the Frattini subgroup lies in $N$) and `commutatorRightHom` (Lemma 4.6: the right-commutator homomorphism for an abelian normal subgroup $A\trianglelefteq G$ and any $g\in G$).
--
--   The bundle also proves 31 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch04_Commutators/Main/CommutatorIdentities.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch04_Commutators/Main/CommutatorIdentities.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Main
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
import Definitions.Def_OddOrder_Mathlib_SemidirectProduct
import Definitions.Def_OddOrder_Mathlib_Subgroup
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Solvable
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace OddOrder.Isaacs.Ch04

open scoped commutatorElement

variable {G : Type*} [Group G]

section

/-- Helper: `g * ⁅a, b⁆ * g⁻¹ = ⁅g * a, b⁆ * ⁅b, g⁆`. -/
private lemma conj_commutator_split (g a b : G) :
    g * ⁅a, b⁆ * g⁻¹ = ⁅g * a, b⁆ * ⁅b, g⁆ := by
  simp only [commutatorElement_def]
  group

/-- **Isaacs Lemma 4.1**: `H, K ≤ G` のとき `H` は `⁅H, K⁆` を正規化する.
**仮定なし版** (H, K の正規性を要求しない).

証明: 一般 identity `g · ⁅a, b⁆ · g⁻¹ = ⁅g a, b⁆ · ⁅b, g⁆` を使用. h ∈ H に対して
`h · ⁅h', k⁆ · h⁻¹ = ⁅h h', k⁆ · ⁅k, h⁆`. 両因子は `⁅H, K⁆` 内. 生成元から
closure_induction で一般元へ. -/
theorem subgroup_le_normalizer_commutator_self (H K : Subgroup G) :
    H ≤ Subgroup.normalizer (⁅H, K⁆ : Subgroup G) := by
  -- For h ∈ H and x ∈ ⁅H,K⁆, both h x h⁻¹ ∈ ⁅H,K⁆ and h⁻¹ x h ∈ ⁅H,K⁆ hold by the
  -- same closure induction (since h⁻¹ ∈ H as well).
  have key : ∀ h ∈ H, ∀ x ∈ (⁅H, K⁆ : Subgroup G),
      h * x * h⁻¹ ∈ (⁅H, K⁆ : Subgroup G) := by
    intro h hh x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with ⟨h', hh', k, hk, rfl⟩
      rw [conj_commutator_split]
      refine Subgroup.mul_mem _ ?_ ?_
      · exact Subgroup.commutator_mem_commutator (H.mul_mem hh hh') hk
      · -- ⁅k, h⁆ ∈ ⁅K, H⁆ = ⁅H, K⁆.
        have hKH : ⁅k, h⁆ ∈ (⁅K, H⁆ : Subgroup G) :=
          Subgroup.commutator_mem_commutator hk hh
        rwa [Subgroup.commutator_comm] at hKH
    | one => simp
    | mul x y _ _ ihx ihy =>
      have eq : h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) := by group
      rw [eq]
      exact Subgroup.mul_mem _ ihx ihy
    | inv x _ ihx =>
      have eq : h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ := by group
      rw [eq]
      exact Subgroup.inv_mem _ ihx
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key h hh x, fun hx => ?_⟩
  -- (⇐): conjugate `h * x * h⁻¹` back by `h⁻¹`.
  have hh_inv : h⁻¹ ∈ H := H.inv_mem hh
  have := key h⁻¹ hh_inv (h * x * h⁻¹) hx
  have eq : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
  rwa [eq] at this

/-- **Isaacs Lemma 4.1** (symmetric form): `K` も `⁅H, K⁆` を正規化する.
`⁅H, K⁆ = ⁅K, H⁆` 経由で上記から導出. -/
theorem subgroup_le_normalizer_commutator_self_right (H K : Subgroup G) :
    K ≤ Subgroup.normalizer (⁅H, K⁆ : Subgroup G) := by
  rw [Subgroup.commutator_comm]
  exact subgroup_le_normalizer_commutator_self K H

/-- **Isaacs Lem 4.1 系**: `H ⊔ K = ⊤` ⇒ `⁅H, K⁆` は G で normal.
`H` も `K` も `⁅H, K⁆` を正規化 (Lem 4.1) ⇒ `H ⊔ K ≤ N(⁅H, K⁆)`, `⊤ ≤ N(⁅H, K⁆)`,
よって `⁅H, K⁆.Normal`. mathlib `commutator_normal` instance は `H, K` 両方 G で normal
を要求するが, ここでは生成集合の `⊔` だけで十分. -/
theorem commutator_normal_of_sup_eq_top {H K : Subgroup G} (hsup : H ⊔ K = ⊤) :
    (⁅H, K⁆ : Subgroup G).Normal := by
  refine Subgroup.normalizer_eq_top_iff.mp ?_
  rw [← top_le_iff, ← hsup]
  exact sup_le (subgroup_le_normalizer_commutator_self H K)
    (subgroup_le_normalizer_commutator_self_right H K)

/-- **Isaacs Lemma 4.3** (片向き): `⁅H, K⁆ ≤ H` ⇒ `K ≤ N(H)`. -/
theorem le_normalizer_of_commutator_le {H K : Subgroup G}
    (h : ⁅H, K⁆ ≤ H) : K ≤ Subgroup.normalizer H := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    -- k * x * k⁻¹ = ⁅k, x⁆ * x. ⁅k, x⁆ ∈ ⁅K, H⁆ = ⁅H, K⁆ ≤ H.
    have eq : k * x * k⁻¹ = ⁅k, x⁆ * x := by
      simp only [commutatorElement_def]; group
    rw [eq]
    refine H.mul_mem ?_ hx
    have hcomm : ⁅k, x⁆ ∈ (⁅H, K⁆ : Subgroup G) := by
      have := Subgroup.commutator_mem_commutator hk hx (H₁ := K) (H₂ := H)
      rwa [Subgroup.commutator_comm] at this
    exact h hcomm
  · intro hx
    -- (⇐) reverse direction via k⁻¹.
    have hk_inv : k⁻¹ ∈ K := K.inv_mem hk
    have eq : k⁻¹ * (k * x * k⁻¹) * k = x := by group
    have : k⁻¹ * (k * x * k⁻¹) * (k⁻¹)⁻¹ ∈ H := by
      simp only [inv_inv]
      have heq : k⁻¹ * (k * x * k⁻¹) * k = ⁅k⁻¹, k * x * k⁻¹⁆ * (k * x * k⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [heq]
      refine H.mul_mem ?_ hx
      have hcomm : ⁅k⁻¹, k * x * k⁻¹⁆ ∈ (⁅H, K⁆ : Subgroup G) := by
        have := Subgroup.commutator_mem_commutator hk_inv hx (H₁ := K) (H₂ := H)
        rwa [Subgroup.commutator_comm] at this
      exact h hcomm
    simpa [eq] using this

/-- **Isaacs Lemma 4.3** (逆向き): `K ≤ N(H)` ⇒ `⁅H, K⁆ ≤ H`. -/
theorem commutator_le_of_le_normalizer {H K : Subgroup G}
    (h : K ≤ Subgroup.normalizer H) : ⁅H, K⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro h' hh' k hk
  -- ⁅h', k⁆ = h' * (k * h'⁻¹ * k⁻¹). k normalizes H, so k * h'⁻¹ * k⁻¹ ∈ H.
  have hk_in_N : k ∈ Subgroup.normalizer H := h hk
  rw [Subgroup.mem_normalizer_iff] at hk_in_N
  have h_inv : h'⁻¹ ∈ H := H.inv_mem hh'
  have h_kh : k * h'⁻¹ * k⁻¹ ∈ H := (hk_in_N h'⁻¹).mp h_inv
  have eq : ⁅h', k⁆ = h' * (k * h'⁻¹ * k⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [eq]
  exact H.mul_mem hh' h_kh

/-- **Isaacs Lemma 4.3** (iff 版): `⁅H, K⁆ ≤ H ↔ K ≤ N(H)`. -/
theorem commutator_le_iff_le_normalizer {H K : Subgroup G} :
    ⁅H, K⁆ ≤ H ↔ K ≤ Subgroup.normalizer H :=
  ⟨le_normalizer_of_commutator_le, commutator_le_of_le_normalizer⟩

/-- General commutator identity (no hypothesis):
`⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆`. -/
private lemma commutatorElement_mul_left_eq (x y z : G) :
    ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
  simp only [commutatorElement_def]
  group

/-- Helper: `⁅x, y⁆ ∈ commutator G` for all `x, y : G`. -/
lemma commutatorElement_mem_commutator_top (x y : G) :
    ⁅x, y⁆ ∈ _root_.commutator G := by
  rw [_root_.commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)

/-- In class ≤ 2 (`commutator G ≤ Z(G)`), the map `⁅·, z⁆ : G → G'` is a
homomorphism on the left: `⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆`.

**証明**: 一般 identity `⁅x*y, z⁆ = x · ⁅y, z⁆ · x⁻¹ · ⁅x, z⁆` で `⁅y, z⁆` 中心
⇒ `x · ⁅y, z⁆ = ⁅y, z⁆ · x` ⇒ `x · ⁅y, z⁆ · x⁻¹ = ⁅y, z⁆`. 結果 `⁅y, z⁆ · ⁅x, z⁆`
を `⁅x, z⁆` 中心で swap. -/
lemma commutatorElement_mul_left_of_class_le_two
    (hC : _root_.commutator G ≤ Subgroup.center G) (x y z : G) :
    ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have h_yz : ⁅y, z⁆ ∈ Subgroup.center G :=
    hC (commutatorElement_mem_commutator_top y z)
  have h_xz : ⁅x, z⁆ ∈ Subgroup.center G :=
    hC (commutatorElement_mem_commutator_top x z)
  rw [commutatorElement_mul_left_eq]
  rw [show x * ⁅y, z⁆ = ⁅y, z⁆ * x from Subgroup.mem_center_iff.mp h_yz x]
  rw [mul_inv_cancel_right]
  exact Subgroup.mem_center_iff.mp h_xz ⁅y, z⁆

/-- In class ≤ 2, `⁅x^n, z⁆ = ⁅x, z⁆^n` for all `n : ℕ`. 帰納で `*` 版から従う. -/
lemma commutatorElement_pow_left_of_class_le_two
    (hC : _root_.commutator G ≤ Subgroup.center G) (x z : G) (n : ℕ) :
    ⁅x^n, z⁆ = ⁅x, z⁆^n := by
  induction n with
  | zero => simp [commutatorElement_def]
  | succ k ih =>
    rw [pow_succ, commutatorElement_mul_left_of_class_le_two hC, ih, pow_succ]

/-- Helper: For finite `p`-group `P` and maximal subgroup `M`, `M.index = p`.

**証明**: `M` 正規 (nilpotent + max). `|P/M| = p^k`. `k = 1` を示す:
- `k = 0` ⇒ `M = ⊤`, 矛盾.
- `k ≥ 2` ⇒ Cauchy で `P/M` に order `p` の元 `g` 存在 ⇒ `⟨g⟩` は order `p` の subgroup.
  pull back で `M < H' < ⊤` (M maximal と矛盾). -/
private lemma index_eq_prime_of_isCoatom_of_pgroup
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p P) {M : Subgroup P} (hMax : IsCoatom M) : M.index = p := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hMnormal : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom M
      (Group.normalizerCondition_of_isNilpotent (G := P)) hMax
  have := hMnormal
  have hPQuot : IsPGroup p (P ⧸ M) := hP.to_quotient M
  obtain ⟨k, hk⟩ := hPQuot.exists_card_eq
  have h_idx : M.index = Nat.card (P ⧸ M) := Subgroup.index_eq_card _
  have hM_ne_top : M ≠ ⊤ := hMax.1
  -- k ≥ 1 (else |P/M| = 1, so M = ⊤)
  have hk_pos : 1 ≤ k := by
    by_contra h
    push Not at h
    interval_cases k
    rw [pow_zero] at hk
    have hsub : Subsingleton (P ⧸ M) := Nat.card_eq_one_iff_unique.mp hk |>.1
    apply hM_ne_top
    rw [Subgroup.eq_top_iff']
    intro x
    have h1 : (QuotientGroup.mk x : P ⧸ M) = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff x).mp h1
  -- Suppose k ≥ 2 for contradiction
  by_contra h_idx_ne
  have hk_ne_1 : k ≠ 1 := fun h_eq => h_idx_ne (by rw [h_idx, hk, h_eq, pow_one])
  have hk_ge_2 : 2 ≤ k := Nat.lt_of_le_of_ne hk_pos (Ne.symm hk_ne_1)
  -- Cauchy: ∃ g : P/M, orderOf g = p
  have hp_dvd : p ∣ Nat.card (P ⧸ M) := by
    rw [hk]; exact dvd_pow_self p (Nat.one_le_iff_ne_zero.mp hk_pos)
  obtain ⟨g, hg_ord⟩ := exists_prime_orderOf_dvd_card' p hp_dvd
  -- ⟨g⟩ has order p
  let H : Subgroup (P ⧸ M) := Subgroup.zpowers g
  have hH_card : Nat.card H = p := by rw [Nat.card_zpowers, hg_ord]
  -- |P/M| = p^k > p for k ≥ 2
  have hp_lt : p < Nat.card (P ⧸ M) := by
    rw [hk]
    calc p = p^1 := (pow_one p).symm
      _ < p^k := by apply pow_lt_pow_right₀ hp.out.one_lt; omega
  have hH_ne_top : H ≠ ⊤ := by
    intro hH_top
    have hcard_eq : Nat.card H = Nat.card (P ⧸ M) := by
      rw [hH_top]; exact Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [hH_card] at hcard_eq
    omega
  have hH_ne_bot : H ≠ ⊥ := by
    intro hH_bot
    have : Nat.card H = 1 := Subgroup.card_eq_one.mpr hH_bot
    rw [hH_card] at this
    exact hp.out.one_lt.ne this.symm
  -- Pull back H to subgroup of P
  let H' : Subgroup P := H.comap (QuotientGroup.mk' M)
  -- M ≤ H'
  have h_M_le_H' : M ≤ H' := by
    intro x hx
    change (QuotientGroup.mk' M) x ∈ H
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact Subgroup.one_mem H
  -- H' < ⊤ (else H = ⊤ via mk' surjective)
  have h_H'_lt_top : H' < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h_H'_top
    apply hH_ne_top
    rw [Subgroup.eq_top_iff']
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hxH' : x ∈ H' := h_H'_top ▸ Subgroup.mem_top x
    exact hxH'
  -- M < H' (else H = ⊥)
  have h_M_lt_H' : M < H' := by
    rw [lt_iff_le_and_ne]
    refine ⟨h_M_le_H', ?_⟩
    intro h_eq
    apply hH_ne_bot
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx_H
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    have hy_H' : y ∈ H' := hx_H
    rw [← h_eq] at hy_H'
    exact (QuotientGroup.eq_one_iff y).mpr hy_H'
  -- hMax.2 gives H' = ⊤, contradicting H' < ⊤
  exact h_H'_lt_top.ne (hMax.2 H' h_M_lt_H')

/-- For finite `p`-group `P` and maximal `M`, `commutator P ≤ M` (`P/M` is order `p`, abelian). -/
private lemma commutator_le_of_isCoatom_of_pgroup
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p P) {M : Subgroup P} (hMax : IsCoatom M) :
    _root_.commutator P ≤ M := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hMnormal : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom M
      (Group.normalizerCondition_of_isNilpotent (G := P)) hMax
  have := hMnormal
  have h_idx : M.index = p := index_eq_prime_of_isCoatom_of_pgroup hP hMax
  have h_card_quot : Nat.card (P ⧸ M) = p := by
    rw [← Subgroup.index_eq_card]; exact h_idx
  have : Fact (Nat.card (P ⧸ M)).Prime := ⟨h_card_quot ▸ hp.out⟩
  have : IsCyclic (P ⧸ M) := isCyclic_of_prime_card h_card_quot
  -- commutator P ≤ M iff P/M abelian
  rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
  let := IsCyclic.commGroup (α := P ⧸ M)
  exact ⟨⟨mul_comm⟩⟩

/-- For finite `p`-group `P` and maximal `M`, `x^p ∈ M` for all `x : P`. -/
private lemma pow_p_mem_of_isCoatom_of_pgroup
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p P) {M : Subgroup P} (hMax : IsCoatom M) (x : P) :
    x^p ∈ M := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hMnormal : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom M
      (Group.normalizerCondition_of_isNilpotent (G := P)) hMax
  have := hMnormal
  have h_idx : M.index = p := index_eq_prime_of_isCoatom_of_pgroup hP hMax
  have h_card_quot : Nat.card (P ⧸ M) = p := by
    rw [← Subgroup.index_eq_card]; exact h_idx
  -- In P/M of order p, q^p = 1 for any q. So x^p ∈ M.
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
  rw [← h_card_quot]
  exact pow_card_eq_one'

/-- **For finite `p`-group `P`, `commutator P ≤ frattini P`**. -/
theorem commutator_le_frattini_of_pgroup
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P) :
    _root_.commutator P ≤ frattini P := by
  refine le_iInf fun M => ?_
  refine le_iInf fun hM => ?_
  exact commutator_le_of_isCoatom_of_pgroup hP hM

/-- **For finite `p`-group `P`, `x^p ∈ frattini P` for all `x : P`**. -/
theorem pow_p_mem_frattini_of_pgroup
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P) (x : P) :
    x^p ∈ frattini P := by
  refine Subgroup.mem_iInf.mpr fun M => Subgroup.mem_iInf.mpr fun hM => ?_
  exact pow_p_mem_of_isCoatom_of_pgroup hP hM x

/-- **Isaacs Lemma 4.5 backward**: For finite `p`-group `P` and `N ⊴ P`,
`Φ(P) ⊆ N` ⇒ `P/N` is `p`-elementary abelian.

**証明**: `commutator P ≤ Φ(P) ⊆ N` ⇒ `P/N` abelian.
`∀ x, x^p ∈ Φ(P) ⊆ N` ⇒ `∀ q : P/N, q^p = 1`. -/
theorem isElementaryAbelian_quotient_of_frattini_le_of_pgroup
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P)
    {N : Subgroup P} [N.Normal] (hΦ : frattini P ≤ N) :
    OddOrder.GroupTheory.IsElementaryAbelian p (P ⧸ N) := by
  refine ⟨?_, ?_⟩
  · -- P/N abelian
    have h_comm_le : _root_.commutator P ≤ N :=
      le_trans (commutator_le_frattini_of_pgroup hP) hΦ
    exact (Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr h_comm_le).is_comm.comm
  · -- ∀ q : P/N, q^p = 1
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hΦ (pow_p_mem_frattini_of_pgroup hP x)

/-- **Helper**: For any group `G` and subgroup `M ≤ G` with prime index, `M` is a coatom
(maximal proper subgroup) in the subgroup lattice.

**証明**: M.index = p ≥ 2 ⇒ M ≠ ⊤. For M < K, by `relIndex_mul_index`,
`M.relIndex K * K.index = M.index = p`, so K.index = 1 or p. If K.index = p, then
`M.relIndex K = 1` so K = M, contradicting M < K. Hence K.index = 1, K = ⊤. -/
private lemma isCoatom_of_index_prime {G : Type*} [Group G] {M : Subgroup G}
    {p : ℕ} (hp : p.Prime) (h_idx : M.index = p) : IsCoatom M := by
  refine ⟨?_, ?_⟩
  · -- M ≠ ⊤
    intro h_top
    rw [h_top, Subgroup.index_top] at h_idx
    exact hp.one_lt.ne' h_idx.symm
  · -- ∀ K, M < K → K = ⊤
    intro K hMK
    by_contra h_K_ne_top
    -- M ≤ K, use relIndex_mul_index
    have hMK_le : M ≤ K := hMK.le
    have h_eq : M.relIndex K * K.index = M.index :=
      Subgroup.relIndex_mul_index hMK_le
    rw [h_idx] at h_eq
    -- K.index ∣ p, so K.index = 1 or p
    have h_dvd : K.index ∣ p := by
      refine ⟨M.relIndex K, ?_⟩
      linarith [h_eq, Nat.mul_comm K.index (M.relIndex K)]
    rcases hp.eq_one_or_self_of_dvd _ h_dvd with h1 | hp_eq
    · -- K.index = 1 ⇒ K = ⊤
      have hK_top : K = ⊤ := Subgroup.index_eq_one.mp h1
      exact h_K_ne_top hK_top
    · -- K.index = p ⇒ M.relIndex K = 1 ⇒ M = K, contradicting M < K
      rw [hp_eq] at h_eq
      have h_rel_one : M.relIndex K = 1 := by
        have hp_pos : 0 < p := hp.pos
        have : M.relIndex K * p = 1 * p := by rw [h_eq, one_mul]
        exact Nat.eq_of_mul_eq_mul_right hp_pos this
      have hM_eq_K : M = K := by
        -- M.relIndex K = 1 ⇒ M.subgroupOf K = ⊤
        have := Subgroup.relIndex_eq_one.mp h_rel_one
        -- this : K ≤ M (since M.subgroupOf K = ⊤ means everything in K is in M)
        exact le_antisymm hMK_le this
      exact absurd hM_eq_K (ne_of_lt hMK)

open scoped IsMulCommutative in
/-- **Isaacs Lemma 4.5 forward**: For finite `p`-group `P` and `N ⊴ P`,
`P/N` is `p`-elementary abelian ⇒ `Φ(P) ⊆ N`.

**証明**: For each `x ∈ Φ(P)`, suppose `x ∉ N`. Construct a maximal `M ≤ P` with
`N ≤ M` and `x ∉ M`, contradicting `Φ(P) ⊆ M`.

`P/N` elementary abelian ⇒ `(P/N)` is a `ZMod p`-vector space (`AddCommGroup.zmodModule`
on `Additive (P/N)`). For `xa := xN ≠ 1`, `Projective.exists_dual_ne_zero` gives
a linear functional `f : (Additive (P/N)) →ₗ[ZMod p] ZMod p` with `f xa ≠ 0`.
Convert to `φ : (P/N) →* Multiplicative (ZMod p)` via `AddMonoidHom.toMultiplicativeRight`.
`φ.ker.comap (mk' N) : Subgroup P` is the desired maximal subgroup (index `p`,
`x ∉ M`, `N ≤ M`). -/
theorem frattini_le_of_isElementaryAbelian_quotient_of_pgroup
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime] (_hP : IsPGroup p P)
    {N : Subgroup P} [N.Normal]
    (hN : OddOrder.GroupTheory.IsElementaryAbelian p (P ⧸ N)) :
    frattini P ≤ N := by
  intro x hx_frat
  by_contra hx_notN
  -- Set up: P/N as CommGroup (via IsMulCommutative instance → CommGroup.ofIsMulCommutative)
  have hPN_comm : IsMulCommutative (P ⧸ N) := ⟨⟨hN.comm⟩⟩
  -- Set up: Additive (P/N) as ZMod p-module (vector space over the field ZMod p)
  have hp_smul : ∀ a : Additive (P ⧸ N), (p : ℕ) • a = 0 := fun a => by
    apply Additive.toMul.injective
    show (p • a).toMul = (0 : Additive _).toMul
    rw [toMul_nsmul, toMul_zero]
    exact hN.pow_eq_one _
  have hMod : Module (ZMod p) (Additive (P ⧸ N)) := AddCommGroup.zmodModule hp_smul
  have hFree : Module.Free (ZMod p) (Additive (P ⧸ N)) :=
    @Module.Free.of_divisionRing (ZMod p) (Additive (P ⧸ N)) _ _ inferInstance
  have hProj : Module.Projective (ZMod p) (Additive (P ⧸ N)) := Module.Projective.of_free
  -- xa : Additive (P/N) is nonzero (corresponds to x ∉ N)
  set xa : Additive (P ⧸ N) := Additive.ofMul ((x : P ⧸ N)) with hxa_def
  have hxa_ne_zero : xa ≠ 0 := by
    intro h_eq
    apply hx_notN
    have h_mul_one : (x : P ⧸ N) = 1 := by
      have := congr_arg Additive.toMul h_eq
      rwa [toMul_ofMul, toMul_zero] at this
    exact (QuotientGroup.eq_one_iff x).mp h_mul_one
  -- Find linear functional f with f xa ≠ 0
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (ZMod p) hxa_ne_zero
  -- Convert to MonoidHom φ : (P/N) →* Multiplicative (ZMod p)
  let φ : (P ⧸ N) →* Multiplicative (ZMod p) :=
    AddMonoidHom.toMultiplicativeRight f.toAddMonoidHom
  -- Define M_quot := ker φ : Subgroup (P/N), and M := M_quot.comap (mk' N) : Subgroup P
  let M_quot : Subgroup (P ⧸ N) := φ.ker
  let M : Subgroup P := M_quot.comap (QuotientGroup.mk' N)
  -- N ≤ M: y ∈ N ⇒ mk' N y = 1 ⇒ φ 1 = 1
  have hN_le_M : N ≤ M := by
    intro y hy
    change QuotientGroup.mk' N y ∈ M_quot
    change φ (QuotientGroup.mk' N y) = 1
    have h_eq_one : QuotientGroup.mk' N y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
    rw [h_eq_one, map_one]
  -- x ∉ M: φ (xN) = ofAdd (f xa), and f xa ≠ 0 ⇒ ofAdd ... ≠ 1
  have hx_notM : x ∉ M := by
    intro hx_M
    apply hf
    -- hx_M : x ∈ M = M_quot.comap (mk' N), so mk' N x ∈ M_quot = φ.ker
    -- i.e., φ (xN) = 1, i.e., ofAdd (f xa) = 1, i.e., f xa = 0
    have hx_in : φ ((x : P ⧸ N)) = 1 := hx_M
    -- φ ↑x = ofAdd (f xa) by def
    change Multiplicative.ofAdd (f xa) = 1 at hx_in
    rwa [show (1 : Multiplicative (ZMod p)) = Multiplicative.ofAdd 0 from rfl,
         Multiplicative.ofAdd.injective.eq_iff] at hx_in
  -- φ.range = ⊤ (since f ≠ 0 ⇒ range f = ⊤ in ZMod p, simple module)
  have hf_range_top : LinearMap.range f = ⊤ := by
    have h_ne_bot : LinearMap.range f ≠ ⊥ := fun h_bot => hf <| by
      have h_in : f xa ∈ LinearMap.range f := ⟨xa, rfl⟩
      rw [h_bot] at h_in
      exact (Submodule.mem_bot _).mp h_in
    rcases eq_bot_or_eq_top (LinearMap.range f) with h | h
    · exact absurd h h_ne_bot
    · exact h
  have hφ_surj : Function.Surjective φ := by
    intro y
    -- y : Multiplicative (ZMod p), need x' : P/N with φ x' = y
    -- y.toAdd ∈ ZMod p = range f (= ⊤), so ∃ a : Additive (P/N), f a = y.toAdd
    have h_in_top : y.toAdd ∈ LinearMap.range f := hf_range_top.symm ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := h_in_top
    refine ⟨a.toMul, ?_⟩
    change Multiplicative.ofAdd (f (Additive.ofMul (a.toMul))) = y
    rw [ofMul_toMul, ha, ofAdd_toAdd]
  -- M_quot.index = Nat.card (P/N) / Nat.card range = Nat.card Multiplicative (ZMod p) = p
  -- Use Subgroup.index_ker for surjective φ
  have h_M_quot_index : M_quot.index = p := by
    -- Use: φ surjective ⇒ (P/N) ⧸ φ.ker ≃* Multiplicative (ZMod p)
    -- Nat.card (Multiplicative (ZMod p)) = Nat.card (ZMod p) = p
    have h_quot_card : Nat.card ((P ⧸ N) ⧸ M_quot) = p := by
      have e : ((P ⧸ N) ⧸ φ.ker) ≃* Multiplicative (ZMod p) :=
        QuotientGroup.quotientKerEquivOfSurjective φ hφ_surj
      rw [Nat.card_congr e.toEquiv]
      exact Nat.card_zmod p
    rw [Subgroup.index, h_quot_card]
  -- M.index = p (via comap of surjective mk' N)
  have h_M_index : M.index = p := by
    rw [show M = M_quot.comap (QuotientGroup.mk' N) from rfl]
    rw [Subgroup.index_comap_of_surjective _ QuotientGroup.mk_surjective]
    exact h_M_quot_index
  -- M is a coatom (maximal proper subgroup)
  have h_M_coatom : IsCoatom M := isCoatom_of_index_prime hp.out h_M_index
  -- Φ(P) ⊆ M
  have hfrat_le_M : frattini P ≤ M := frattini_le_coatom h_M_coatom
  -- Contradiction: x ∈ Φ(P) ⊆ M but x ∉ M
  exact hx_notM (hfrat_le_M hx_frat)

/-- **Isaacs Lemma 4.5** (full equivalence): For finite `p`-group `P` and `N ⊴ P`,
`Φ(P) ⊆ N ↔ P/N is p-elementary abelian`. -/
theorem frattini_le_iff_isElementaryAbelian_quotient_of_pgroup
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P)
    {N : Subgroup P} [N.Normal] :
    frattini P ≤ N ↔ OddOrder.GroupTheory.IsElementaryAbelian p (P ⧸ N) :=
  ⟨isElementaryAbelian_quotient_of_frattini_le_of_pgroup hP,
   frattini_le_of_isElementaryAbelian_quotient_of_pgroup hP⟩

/-- **Isaacs Lemma 4.6 easy direction**: `⁅A, ⊤⁆ ≤ G'` (任意 `A ≤ G` で常時成立).

`commutator_mono` で `A ≤ ⊤ ∧ ⊤ ≤ ⊤ ⇒ ⁅A, ⊤⁆ ≤ ⁅⊤, ⊤⁆ = commutator G`. -/
theorem commutator_top_subgroup_le_commutator (A : Subgroup G) :
    ⁅A, (⊤ : Subgroup G)⁆ ≤ _root_.commutator G := by
  rw [_root_.commutator_def]
  exact Subgroup.commutator_mono le_top le_rfl

/-- **Isaacs Lemma 4.6** ⭐ (章内 5 引用 + Ch.5/7/10 で多用 — 章内ハブ):
`A ⊴ G` abelian + `G/A` cyclic ⇒ `G' = ⁅A, ⊤⁆` (commutator subgroup).

(本 statement は前半. 後半 `G' ≅ A / (A ∩ Z(G))` の同型は別途 statement 化予定.)

**証明** (Isaacs p.118): `MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center` 経由.
- (≥) 部分 = `commutator_top_subgroup_le_commutator` (上記, 仮定不要).
- (≤) 部分: `Q := G/⁅A, ⊤⁆` が abelian を示す.
  - lift `f : Q →* G/A` (mk' A の lift, 可能なのは `⁅A, ⊤⁆ ≤ A` (Lem 4.3 + A 正規)).
  - `f.ker = image(A) in Q ≤ center(Q)` (`⁅a, g⁆ ∈ ⁅A, ⊤⁆` で Q では `ag = ga`).
  - codomain `G/A` cyclic (hypothesis).
  - `MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center`
    ⇒ Q commutative ⇒ commutator G ≤ ⁅A, ⊤⁆. -/
theorem commutator_eq_commutator_of_normal_abelian_cyclic_quotient
    {A : Subgroup G} [A.Normal]
    (_hAb : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hCyclic : IsCyclic (G ⧸ A)) :
    _root_.commutator G = ⁅A, (⊤ : Subgroup G)⁆ := by
  refine le_antisymm ?_ (commutator_top_subgroup_le_commutator A)
  -- (≤) direction: G/⁅A,⊤⁆ が abelian であることを示し commutator G ⊆ ⁅A,⊤⁆ を導出.
  set H : Subgroup G := ⁅A, (⊤ : Subgroup G)⁆ with hHeq
  -- Step 1: H ≤ A.
  have hHleA : H ≤ A := by
    change ⁅A, (⊤ : Subgroup G)⁆ ≤ A
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_top_left_le_iff (H := A)).mpr ‹A.Normal›
  -- Step 2: lift f : G/H →* G/A.
  let f : G ⧸ H →* G ⧸ A :=
    QuotientGroup.lift H (QuotientGroup.mk' A) (fun x hx => by
      simp only [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hHleA hx)
  -- Step 3: f.ker ≤ center(G/H).
  have hker_central : f.ker ≤ Subgroup.center (G ⧸ H) := by
    intro q hq
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    -- hq : f ↑y = 1. f ↑y = (mk' A) y by lift_mk'.
    have hyA : y ∈ A := by
      have hfy : f ((y : G) : G ⧸ H) = ((y : G) : G ⧸ A) := by
        change QuotientGroup.lift H (QuotientGroup.mk' A) _ ((y : G) : G ⧸ H) = _
        exact QuotientGroup.lift_mk' _ _ y
      rw [MonoidHom.mem_ker, hfy, QuotientGroup.eq_one_iff] at hq
      exact hq
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    -- Goal: (g : G ⧸ H) * (y : G ⧸ H) = (y : G ⧸ H) * (g : G ⧸ H).
    show ((g : G) : G ⧸ H) * ((y : G) : G ⧸ H) = ((y : G) : G ⧸ H) * ((g : G) : G ⧸ H)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rw [QuotientGroup.eq_iff_div_mem]
    -- (g * y) / (y * g) ∈ H. Compute (g*y)*(y*g)⁻¹ = g*y*g⁻¹*y⁻¹ = ⁅g, y⁆ = ⁅y, g⁆⁻¹.
    have heq : g * y / (y * g) = ⁅g, y⁆ := by
      simp only [div_eq_mul_inv, commutatorElement_def]; group
    rw [heq]
    -- ⁅g, y⁆ ∈ ⁅⊤, A⁆ = ⁅A, ⊤⁆ = H.
    rw [hHeq, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) hyA
  -- Step 4: G/H is abelian.
  have habelian : ∀ a b : G ⧸ H, a * b = b * a :=
    (f.isMulCommutative_of_isCyclic_of_ker_le_center hker_central).is_comm.comm
  -- Step 5: commutator G ⊆ H.
  rw [_root_.commutator_def, Subgroup.commutator_def, Subgroup.closure_le]
  rintro _ ⟨a, _, b, _, rfl⟩
  change ⁅a, b⁆ ∈ H
  rw [← QuotientGroup.eq_one_iff (N := H)]
  show ((⁅a, b⁆ : G) : G ⧸ H) = 1
  rw [show ((⁅a, b⁆ : G) : G ⧸ H) = ⁅(a : G ⧸ H), (b : G ⧸ H)⁆ by
    simp only [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv]]
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact habelian _ _

/-- Helper: For `A ⊴ G` and `b ∈ A`, `⁅b, g⁆ ∈ A` for any `g : G`.

`⁅b, g⁆ = b · (g · b⁻¹ · g⁻¹)`. `b⁻¹ ∈ A` + A normal ⇒ `g · b⁻¹ · g⁻¹ ∈ A`. -/
private lemma commutatorElement_mem_of_normal {A : Subgroup G} [A.Normal]
    {b : G} (hb : b ∈ A) (g : G) : ⁅b, g⁆ ∈ A := by
  have heq : ⁅b, g⁆ = b * (g * b⁻¹ * g⁻¹) := by
    rw [commutatorElement_def]; group
  rw [heq]
  exact A.mul_mem hb (‹A.Normal›.conj_mem _ (A.inv_mem hb) g)

/-- **Lemma 4.6 hom** (右 commutator hom): For `A ⊴ G` abelian and any `g : G`,
the map `θ : A → G` by `θ a = ⁅a, g⁆` is a monoid homomorphism.

`map_mul`: general identity `⁅ab, g⁆ = a · ⁅b, g⁆ · a⁻¹ · ⁅a, g⁆`. `⁅b, g⁆ ∈ A`
(A normal) + A abelian ⇒ `a · ⁅b, g⁆ · a⁻¹ = ⁅b, g⁆`. Result `⁅b, g⁆ · ⁅a, g⁆`
を A 内 swap で `⁅a, g⁆ · ⁅b, g⁆`. -/
def commutatorRightHom {A : Subgroup G} [A.Normal]
    (hAb : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (g : G) : A →* G where
  toFun a := ⁅(a : G), g⁆
  map_one' := by
    change ⁅((1 : A) : G), g⁆ = 1
    rw [Subgroup.coe_one]
    exact commutatorElement_one_left g
  map_mul' a b := by
    change ⁅((a * b : A) : G), g⁆ = ⁅((a : A) : G), g⁆ * ⁅((b : A) : G), g⁆
    rw [Subgroup.coe_mul, commutatorElement_mul_left_eq]
    have hbg : ⁅(b : G), g⁆ ∈ A := commutatorElement_mem_of_normal b.2 g
    have hag : ⁅(a : G), g⁆ ∈ A := commutatorElement_mem_of_normal a.2 g
    have h1 : (a : G) * ⁅(b : G), g⁆ * (a : G)⁻¹ = ⁅(b : G), g⁆ := by
      rw [hAb _ a.2 _ hbg, mul_assoc, mul_inv_cancel, mul_one]
    rw [h1]
    exact hAb _ hbg _ hag

/-- The range of `commutatorRightHom hAb g` is contained in `commutator G`. -/
theorem commutatorRightHom_range_le_commutator {A : Subgroup G} [A.Normal]
    (hAb : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (g : G) :
    (commutatorRightHom hAb g).range ≤ _root_.commutator G := by
  rintro x ⟨a, rfl⟩
  change ⁅((a : A) : G), g⁆ ∈ _root_.commutator G
  exact commutatorElement_mem_commutator_top _ _

/-- For `g : G` such that `g · A` generates `G ⧸ A`, `A ⊔ ⟨g⟩ = ⊤`. -/
private lemma sup_zpowers_eq_top_of_generator_quot
    {A : Subgroup G} [A.Normal] {g : G}
    (hgen : ∀ x : G ⧸ A, x ∈ Subgroup.zpowers ((g : G ⧸ A))) :
    A ⊔ Subgroup.zpowers g = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨k, hk⟩ := hgen (x : G ⧸ A)
  -- hk : (↑g : G ⧸ A)^k = (↑x : G ⧸ A)
  -- So (↑(g^k) : G ⧸ A) = (↑x : G ⧸ A), i.e., x * (g^k)⁻¹ ∈ A.
  have hk' : ((g^k : G) : G ⧸ A) = ((x : G) : G ⧸ A) := by
    rw [← hk]
    exact (map_zpow (QuotientGroup.mk' A) g k).symm
  -- From hk': (g^k : G ⧸ A) = (x : G ⧸ A), so g^k / x ∈ A by QuotientGroup.eq_iff_div_mem
  have h_div : g^k / x ∈ A := (QuotientGroup.eq_iff_div_mem (N := A)).mp hk'
  -- Hence x * (g^k)⁻¹ = (g^k / x)⁻¹ ∈ A
  have hxgk : x * (g^k)⁻¹ ∈ A := by
    have heq : x * (g^k)⁻¹ = (g^k / x)⁻¹ := by rw [div_eq_mul_inv]; group
    rw [heq]
    exact A.inv_mem h_div
  -- x = (x * (g^k)⁻¹) * g^k ∈ A · ⟨g⟩
  have hx_eq : x = (x * (g^k)⁻¹) * g^k := by group
  rw [hx_eq]
  exact Subgroup.mul_mem_sup hxgk (Subgroup.zpow_mem_zpowers g k)

/-- For `g : G` such that `g · A` generates `G ⧸ A`, and `A` is abelian normal:
`a ∈ A` is in the kernel of `commutatorRightHom hAb g` iff `(a : G) ∈ Z(G)`. -/
theorem commutatorRightHom_mem_ker_iff {A : Subgroup G} [A.Normal]
    (hAb : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {g : G} (hgen : ∀ x : G ⧸ A, x ∈ Subgroup.zpowers ((g : G ⧸ A))) (a : A) :
    a ∈ (commutatorRightHom hAb g).ker ↔ (a : G) ∈ Subgroup.center G := by
  constructor
  · -- Forward: a ∈ ker (commutes with g) + A abelian ⇒ a commutes with A ⊔ ⟨g⟩ = G
    intro ha
    rw [MonoidHom.mem_ker] at ha
    -- ha : ⁅(a : G), g⁆ = 1, i.e., a · g = g · a
    have ha_g : (a : G) * g = g * (a : G) :=
      commutatorElement_eq_one_iff_mul_comm.mp ha
    rw [Subgroup.mem_center_iff]
    intro x
    -- S := { x : G | (a : G) · x = x · (a : G) } = centralizer {a}
    let S : Subgroup G := Subgroup.centralizer ({(a : G)} : Set G)
    -- A ≤ S (A abelian, a ∈ A)
    have hAS : A ≤ S := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      rintro z (rfl : z = (a : G))
      exact hAb _ a.2 _ hy
    -- g ∈ S
    have hgS : g ∈ S := by
      rw [Subgroup.mem_centralizer_iff]
      rintro z (rfl : z = (a : G))
      exact ha_g
    -- ⟨g⟩ ≤ S
    have hzpgS : Subgroup.zpowers g ≤ S := by
      rw [Subgroup.zpowers_eq_closure]
      exact Subgroup.closure_le _ |>.mpr (by rintro _ (rfl : _ = g); exact hgS)
    -- A ⊔ ⟨g⟩ ≤ S
    have hsupS : A ⊔ Subgroup.zpowers g ≤ S := sup_le hAS hzpgS
    -- ⊤ ≤ S
    have hsupTop : A ⊔ Subgroup.zpowers g = ⊤ := sup_zpowers_eq_top_of_generator_quot hgen
    have hTopS : (⊤ : Subgroup G) ≤ S := hsupTop ▸ hsupS
    -- x ∈ S
    have hxS : x ∈ S := hTopS (Subgroup.mem_top x)
    rw [Subgroup.mem_centralizer_iff] at hxS
    exact (hxS _ rfl).symm
  · intro ha
    rw [MonoidHom.mem_ker]
    change ⁅(a : G), g⁆ = 1
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp ha g).symm

/-- General identity (no hypothesis): `g · ⁅a, g⁆ · g⁻¹ = ⁅g · a · g⁻¹, g⁆`.
共役 conjugation を交換子内に push. -/
private lemma conj_commutatorElement_right (a g : G) :
    g * ⁅a, g⁆ * g⁻¹ = ⁅g * a * g⁻¹, g⁆ := by
  simp only [commutatorElement_def]; group

/-- General identity (no hypothesis): `g⁻¹ · ⁅a, g⁆ · g = ⁅g⁻¹ · a · g, g⁆`. -/
private lemma inv_conj_commutatorElement_right (a g : G) :
    g⁻¹ * ⁅a, g⁆ * g = ⁅g⁻¹ * a * g, g⁆ := by
  simp only [commutatorElement_def]; group

/-- The range of `commutatorRightHom hAb g` is normal in `G` when `g · A` generates
`G ⧸ A`. A 共役: A abelian + range ⊆ A ⇒ A fixes range pointwise. g 共役:
`g · ⁅a, g⁆ · g⁻¹ = ⁅g a g⁻¹, g⁆` ∈ range (A normal ⇒ `g a g⁻¹ ∈ A`). -/
theorem commutatorRightHom_range_normal {A : Subgroup G} [A.Normal]
    (hAb : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {g : G} (hgen : ∀ x : G ⧸ A, x ∈ Subgroup.zpowers ((g : G ⧸ A))) :
    ((commutatorRightHom hAb g).range).Normal := by
  refine ⟨?_⟩
  intro y hy x
  -- Goal: x * y * x⁻¹ ∈ range
  -- Strategy: show normalizer(range) ⊇ A ⊔ ⟨g⟩ = ⊤
  let N : Subgroup G := Subgroup.normalizer (commutatorRightHom hAb g).range
  suffices hxN : x ∈ N by
    rw [Subgroup.mem_normalizer_iff] at hxN
    exact (hxN y).mp hy
  -- Helper: range ⊆ A
  have h_range_le_A : ∀ z, z ∈ (commutatorRightHom hAb g).range → z ∈ A := by
    intro z hz
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hz
    exact commutatorElement_mem_of_normal b.2 g
  -- A ≤ N: A abelian + range ⊆ A ⇒ A fixes range pointwise under conjugation
  have hAN : A ≤ N := by
    intro a' ha'
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have hz_in_A : z ∈ A := h_range_le_A z hz
      have h_eq : a' * z * a'⁻¹ = z := by
        rw [hAb _ ha' _ hz_in_A, mul_assoc, mul_inv_cancel, mul_one]
      rw [h_eq]; exact hz
    · intro hz
      have hz_conj_in_A : a' * z * a'⁻¹ ∈ A := h_range_le_A _ hz
      -- z = a'⁻¹ * (a' * z * a'⁻¹) * a' ∈ A
      have hz_in_A : z ∈ A := by
        have heq : z = a'⁻¹ * (a' * z * a'⁻¹) * a' := by group
        rw [heq]
        exact A.mul_mem (A.mul_mem (A.inv_mem ha') hz_conj_in_A) ha'
      have h_eq : a' * z * a'⁻¹ = z := by
        rw [hAb _ ha' _ hz_in_A, mul_assoc, mul_inv_cancel, mul_one]
      rw [← h_eq]; exact hz
  -- g ∈ N: uses identity g · ⁅b, g⁆ · g⁻¹ = ⁅g · b · g⁻¹, g⁆ + A normal.
  have hgN : g ∈ N := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hz
      -- hb : (commutatorRightHom hAb g) b = z
      have hgbg : g * (b : G) * g⁻¹ ∈ A := ‹A.Normal›.conj_mem _ b.2 g
      refine MonoidHom.mem_range.mpr ⟨⟨g * (b : G) * g⁻¹, hgbg⟩, ?_⟩
      change ⁅g * (b : G) * g⁻¹, g⁆ = g * z * g⁻¹
      rw [show z = ⁅((b : A) : G), g⁆ from hb.symm]
      exact (conj_commutatorElement_right (b : G) g).symm
    · intro hz
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hz
      -- hb : (commutatorRightHom hAb g) b = g * z * g⁻¹, i.e., ⁅↑b, g⁆ = g * z * g⁻¹
      have hgbg : g⁻¹ * (b : G) * g ∈ A := by
        have := ‹A.Normal›.conj_mem _ b.2 g⁻¹
        simpa using this
      refine MonoidHom.mem_range.mpr ⟨⟨g⁻¹ * (b : G) * g, hgbg⟩, ?_⟩
      change ⁅g⁻¹ * (b : G) * g, g⁆ = z
      have hb' : ⁅((b : A) : G), g⁆ = g * z * g⁻¹ := hb
      have hz_eq : z = g⁻¹ * ⁅((b : A) : G), g⁆ * g := by
        rw [hb']; group
      rw [hz_eq]
      exact (inv_conj_commutatorElement_right (b : G) g).symm
  -- ⟨g⟩ ≤ N
  have h_zpgN : Subgroup.zpowers g ≤ N := by
    rw [Subgroup.zpowers_eq_closure]
    exact Subgroup.closure_le _ |>.mpr (by rintro _ (rfl : _ = g); exact hgN)
  -- A ⊔ ⟨g⟩ ≤ N
  have hsupN : A ⊔ Subgroup.zpowers g ≤ N := sup_le hAN h_zpgN
  -- ⊤ ≤ N
  have hsupTop : A ⊔ Subgroup.zpowers g = ⊤ := sup_zpowers_eq_top_of_generator_quot hgen
  exact (hsupTop ▸ hsupN) (Subgroup.mem_top x)

/-- **Isaacs Lemma 4.6 後半**: For `A ⊴ G` abelian and `G ⧸ A` cyclic generated by `g · A`,
`(commutatorRightHom hAb g).range = commutator G`.

**証明**: `≤` direction trivial (`commutatorRightHom_range_le_commutator`).
`≥`: `commutator G = ⁅A, ⊤⁆` (Lem 4.6 main) で `⁅A, ⊤⁆ ≤ range` を示す.
`Subgroup.commutator_le` ⇒ `∀ a ∈ A, ∀ y : G, ⁅a, y⁆ ∈ range`.
`y ∈ ⊤ = A ⊔ ⟨g⟩ = closure ((A : Set G) ∪ {g})` で closure induction:
* base `y ∈ A`: `⁅a, y⁆ = 1` (A abelian).
* base `y = g`: `⁅a, g⁆ = θ(a) ∈ range` (定義).
* `y = 1`: `⁅a, 1⁆ = 1`.
* `y = y₁·y₂`: identity `⁅a, y₁y₂⁆ = ⁅a, y₁⁆·(y₁·⁅a, y₂⁆·y₁⁻¹)` + range Normal.
* `y = y₀⁻¹`: identity `⁅a, y₀⁻¹⁆ = y₀⁻¹·⁅a, y₀⁆⁻¹·y₀` + range Normal + inv_mem. -/
theorem commutatorRightHom_range_eq_commutator {A : Subgroup G} [A.Normal]
    (hAb : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {g : G} (hgen : ∀ x : G ⧸ A, x ∈ Subgroup.zpowers ((g : G ⧸ A))) :
    (commutatorRightHom hAb g).range = _root_.commutator G := by
  have := commutatorRightHom_range_normal hAb hgen
  have hCyc : IsCyclic (G ⧸ A) := ⟨⟨(g : G ⧸ A), hgen⟩⟩
  refine le_antisymm (commutatorRightHom_range_le_commutator hAb g) ?_
  -- commutator G = ⁅A, ⊤⁆ (Lem 4.6 main)
  rw [commutator_eq_commutator_of_normal_abelian_cyclic_quotient hAb hCyc]
  -- Goal: ⁅A, ⊤⁆ ≤ range
  rw [Subgroup.commutator_le]
  -- Sup と closure 等式
  have hsupTop : A ⊔ Subgroup.zpowers g = ⊤ := sup_zpowers_eq_top_of_generator_quot hgen
  have hcl_eq : Subgroup.closure ((A : Set G) ∪ {g}) = (⊤ : Subgroup G) := by
    rw [← hsupTop]
    refine le_antisymm ?_ ?_
    · rw [Subgroup.closure_le]
      rintro x (hxA | hxg)
      · exact (le_sup_left : A ≤ A ⊔ Subgroup.zpowers g) hxA
      · rw [Set.mem_singleton_iff] at hxg
        rw [hxg]
        exact (le_sup_right : Subgroup.zpowers g ≤ A ⊔ _) (Subgroup.mem_zpowers g)
    · refine sup_le ?_ ?_
      · intro x hx; exact Subgroup.subset_closure (Or.inl hx)
      · rw [Subgroup.zpowers_eq_closure, Subgroup.closure_le]
        intro x hx
        exact Subgroup.subset_closure (Or.inr hx)
  -- メイン induction: ∀ y ∈ closure (↑A ∪ {g}), ⁅a, y⁆ ∈ range
  suffices h_main : ∀ a ∈ A, ∀ y ∈ Subgroup.closure ((A : Set G) ∪ {g}),
      ⁅(a : G), y⁆ ∈ (commutatorRightHom hAb g).range by
    intro a ha y _hy_top
    exact h_main a ha y (hcl_eq.symm ▸ Subgroup.mem_top y)
  intro a ha y hy
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hxA | hxg
    · -- x ∈ A: ⁅a, x⁆ = 1 (A abelian)
      have heq : ⁅(a : G), x⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact hAb _ ha _ hxA
      rw [heq]; exact Subgroup.one_mem _
    · -- x = g
      rw [Set.mem_singleton_iff] at hxg; subst hxg
      exact MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩
  | one =>
    rw [commutatorElement_one_right]; exact Subgroup.one_mem _
  | mul y₁ y₂ _ _ hy₁ hy₂ =>
    -- ⁅a, y₁·y₂⁆ = ⁅a, y₁⁆ · (y₁·⁅a, y₂⁆·y₁⁻¹)
    have hid : ⁅(a : G), y₁ * y₂⁆ = ⁅(a : G), y₁⁆ * (y₁ * ⁅(a : G), y₂⁆ * y₁⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [hid]
    refine Subgroup.mul_mem _ hy₁ ?_
    exact ‹((commutatorRightHom hAb g).range).Normal›.conj_mem _ hy₂ y₁
  | inv y₀ _ hy₀ =>
    -- ⁅a, y₀⁻¹⁆ = y₀⁻¹ · ⁅a, y₀⁆⁻¹ · y₀
    have hid : ⁅(a : G), y₀⁻¹⁆ = y₀⁻¹ * ⁅(a : G), y₀⁆⁻¹ * y₀ := by
      simp only [commutatorElement_def]; group
    rw [hid]
    have h_inv : ⁅(a : G), y₀⁆⁻¹ ∈ (commutatorRightHom hAb g).range :=
      Subgroup.inv_mem _ hy₀
    have h_conj := ‹((commutatorRightHom hAb g).range).Normal›.conj_mem _ h_inv y₀⁻¹
    simpa using h_conj

/-- **Lem 4.6 後半 kernel as subgroup**: ker of `commutatorRightHom hAb g` (as a subgroup
of `A`) equals `(A ⊓ Subgroup.center G).subgroupOf A`. -/
theorem commutatorRightHom_ker_eq {A : Subgroup G} [A.Normal]
    (hAb : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {g : G} (hgen : ∀ x : G ⧸ A, x ∈ Subgroup.zpowers ((g : G ⧸ A))) :
    (commutatorRightHom hAb g).ker = (A ⊓ Subgroup.center G).subgroupOf A := by
  ext a
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro ha
    exact ⟨a.2, (commutatorRightHom_mem_ker_iff hAb hgen a).mp ha⟩
  · intro ha
    exact (commutatorRightHom_mem_ker_iff hAb hgen a).mpr ha.2

/-- **Lem 4.6 cardinality form**: `A ⊴ G` abelian + `G ⧸ A` cyclic ⇒
`|commutator G| · |A ⊓ Z(G)| = |A|`. 第一同型定理 + Lagrange (`Subgroup.card_mul_index`).

書籍は `A` が有限のときの主張として述べるが, `Nat.card` は無限を `0` に潰すので
**有限性仮定なし**で成立する (2026-07-19 に旧 `[Finite G]` を除去). -/
theorem card_commutator_mul_card_inf_center_eq_card_of_normal_abelian_cyclic_quotient
    {A : Subgroup G} [A.Normal]
    (hAb : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hCyc : IsCyclic (G ⧸ A)) :
    Nat.card (_root_.commutator G) * Nat.card (A ⊓ Subgroup.center G : Subgroup G)
      = Nat.card A := by
  obtain ⟨γ, hγ⟩ := hCyc.exists_generator
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
  -- Apply Lagrange to θ := commutatorRightHom hAb g
  have h_ker := commutatorRightHom_ker_eq hAb hγ
  have h_range := commutatorRightHom_range_eq_commutator hAb hγ
  have h_lag : Nat.card (commutatorRightHom hAb g).ker *
      (commutatorRightHom hAb g).ker.index = Nat.card A :=
    Subgroup.card_mul_index _
  rw [Subgroup.index_ker, h_range, h_ker] at h_lag
  -- Convert Nat.card ((A ⊓ Z(G)).subgroupOf A) = Nat.card (A ⊓ Z(G))
  have h_card_eq : Nat.card ((A ⊓ Subgroup.center G).subgroupOf A) =
      Nat.card (A ⊓ Subgroup.center G : Subgroup G) := by
    refine Nat.card_congr ?_
    refine {
      toFun := fun x => ⟨((x : A) : G), (Subgroup.mem_subgroupOf.mp x.2)⟩
      invFun := fun y => ⟨⟨(y : G), y.2.1⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_
    }
    · -- ⟨y, y.2.1⟩ ∈ (A ⊓ Z(G)).subgroupOf A
      rw [Subgroup.mem_subgroupOf]
      exact y.2
    · intro x; rfl
    · intro y; rfl
  rw [h_card_eq] at h_lag
  rw [mul_comm]
  exact h_lag

end

end OddOrder.Isaacs.Ch04


