-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusActionTI
-- name    : OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusActionTI
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:29:16.383657+00:00
-- url     : https://prove2.me/theorems/7e34f2db-abb9-45f3-a2cc-bce881e9acb7
-- title:
--   Isaacs Ch. 6: Lemma 6.5 TI counting and subgroup partitions
-- statement:
--   Part of the Isaacs, *Finite Group Theory*, Chapter 6 (Frobenius actions) formalization (pp. 177–183): Frobenius action basics, the TI counting argument of Lemma 6.5, and a helper for partitions of a group into subgroups.
--
--   Main definitions: `SubgroupPartition` (a finite partition of a group by proper nonidentity subgroups), `partOfNeOne` (the unique part containing a nonidentity element), `nonidentitySigmaTo`, `subgroupsOfCard`, `notConjugateSet` (elements not conjugate to a nonidentity element of a given subgroup), and `elementaryAbelianPrimeSquare` (the textbook partition of an elementary abelian group of order $p^2$ into its subgroups of order $p$).
--
--   The bundle also proves 50 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch06_FrobeniusActions/FrobeniusActionTI.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch06_FrobeniusActions/FrobeniusActionTI.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_SemiDihedral
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorBasics
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ChainNilpotent
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusActionBasics
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.FixedPointFree
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.NumberTheory.Multiplicity
import Mathlib.SetTheory.Cardinal.Finite

namespace OddOrder.Isaacs.Ch06

section

open scoped Pointwise

variable {G : Type*} [Group G]

/-- Auxiliary: the set of elements of `G` **not conjugate to any nonidentity element of `A`**. -/
def notConjugateSet (A : Subgroup G) : Set G :=
  { x : G | ∀ a ∈ A, a ≠ 1 → ¬ IsConj a x }

/-- Helper for Lem 6.5: under the TI condition, the normalizer of `A` is `A` itself
(provided `A ≠ ⊥`). -/
private lemma normalizer_eq_self_of_TI
    {A : Subgroup G} (hA_ne : A ≠ ⊥)
    (h_TI : ∀ g : G, g ∉ A → A ⊓ (MulAut.conj g • A) = ⊥) :
    Subgroup.normalizer A = A := by
  refine le_antisymm ?_ A.le_normalizer
  intro g hg
  by_contra hgA
  -- `g ∈ N_G(A)` means conjugation by `g` preserves `A`, so `MulAut.conj g • A = A`.
  have hconj : MulAut.conj g • A = A := by
    have hgN : g ∈ Subgroup.normalizer A := hg
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    change (MulAut.conj g).symm x ∈ A ↔ x ∈ A
    rw [MulAut.conj_symm_apply]
    -- Goal: `g⁻¹ * x * g ∈ A ↔ x ∈ A`, which is `mem_normalizer_iff''`.
    exact ((Subgroup.mem_normalizer_iff''.mp hgN) x).symm
  -- Then `A ⊓ MulAut.conj g • A = A`, but TI gives `⊥`, so `A = ⊥`, contradicting `hA_ne`.
  have h_eq : A ⊓ (MulAut.conj g • A) = A := by rw [hconj]; exact inf_idem A
  have h_bot : A ⊓ (MulAut.conj g • A) = ⊥ := h_TI g hgA
  exact hA_ne (h_eq.symm.trans h_bot)

/-- Helper for Lem 6.5: the carrier set `(B : Set G)` of any conjugate `B = MulAut.conj h • A`
satisfies the same TI hypothesis with respect to elements outside `B`. (This is just a relabelling
of the TI assumption.) Used to show distinct conjugates are disjoint outside `{1}`. -/
lemma TI_conjugate
    {A : Subgroup G}
    (h_TI : ∀ g : G, g ∉ A → A ⊓ (MulAut.conj g • A) = ⊥)
    (h k : G) (hhk : (MulAut.conj h • A : Subgroup G) ≠ MulAut.conj k • A) :
    (MulAut.conj h • A : Subgroup G) ⊓ (MulAut.conj k • A) = ⊥ := by
  -- Let `g := h⁻¹ * k`.  If `g ∈ A`, then `MulAut.conj h • A = MulAut.conj k • A`, contradiction.
  set g : G := h⁻¹ * k with hg_def
  have hg_notmem : g ∉ A := by
    intro hgA
    apply hhk
    -- `k = h * g`, so `MulAut.conj k • A = MulAut.conj h • (MulAut.conj g • A)`.
    have hk_eq : k = h * g := by simp [hg_def]
    have hconjg : MulAut.conj g • A = A :=
      Subgroup.conj_smul_eq_self_of_mem hgA
    calc (MulAut.conj h • A : Subgroup G)
        = MulAut.conj h • (MulAut.conj g • A) := by rw [hconjg]
      _ = MulAut.conj (h * g) • A := by rw [← mul_smul, ← map_mul]
      _ = MulAut.conj k • A := by rw [← hk_eq]
  -- Now apply TI for `g` and conjugate by `h`.
  have h_TI_g : A ⊓ (MulAut.conj g • A) = ⊥ := h_TI g hg_notmem
  -- Conjugating by `h`: `MulAut.conj h` is a `MulEquiv`, so it preserves `⊓` and `⊥`.
  have hsmul : MulAut.conj h • (A ⊓ (MulAut.conj g • A) : Subgroup G)
      = (MulAut.conj h • A) ⊓ (MulAut.conj h • (MulAut.conj g • A)) :=
    Subgroup.smul_inf _ _ _
  have hsmul_bot : MulAut.conj h • (⊥ : Subgroup G) = (⊥ : Subgroup G) := Subgroup.smul_bot _
  -- `MulAut.conj h • (MulAut.conj g • A) = MulAut.conj k • A` (since `h * g = k`).
  have hk_smul : MulAut.conj h • (MulAut.conj g • A) = MulAut.conj k • A := by
    rw [← mul_smul]
    congr 1
    rw [← map_mul]
    congr 1
    simp [hg_def]
  rw [h_TI_g, hsmul_bot] at hsmul
  rw [← hk_smul]
  exact hsmul.symm

/-- Under the TI condition, the number of conjugates of `A` is `[G : A]`.

This is the conjugate-counting part of Isaacs Lemma 6.5, extracted because the same count is
also the cardinality calculation for the Frobenius-group partition in §6B. -/
theorem ncard_conjugates_eq_index_of_TI [Finite G]
    {A : Subgroup G} (hA_ne : A ≠ ⊥)
    (h_TI : ∀ g : G, g ∉ A → A ⊓ (MulAut.conj g • A) = ⊥) :
    (Set.range (fun g : G => MulAut.conj g • A)).ncard = A.index := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hNGA : Subgroup.normalizer A = A := normalizer_eq_self_of_TI hA_ne h_TI
  set conjs : Set (Subgroup G) := Set.range (fun g : G => MulAut.conj g • A) with hconjs_def
  -- Define `f : G → conjs` by `g ↦ ⟨MulAut.conj g • A, ⟨g, rfl⟩⟩`.
  -- `f g₁ = f g₂ ↔ g₂⁻¹ * g₁ ∈ N_G(A) = A ↔ g₁, g₂ in the same left coset of `A`.
  let f : G → conjs := fun g => ⟨MulAut.conj g • A, ⟨g, rfl⟩⟩
  have hf_lift : ∀ g₁ g₂ : G, (QuotientGroup.leftRel A) g₁ g₂ → f g₁ = f g₂ := by
    intro g₁ g₂ hrel
    rw [QuotientGroup.leftRel_apply] at hrel
    have h_in_N : g₁⁻¹ * g₂ ∈ Subgroup.normalizer A := by rw [hNGA]; exact hrel
    have h_conj : MulAut.conj (g₁⁻¹ * g₂) • A = A :=
      Subgroup.conj_smul_eq_self_of_mem (by rw [hNGA] at h_in_N; exact h_in_N)
    ext1
    simp only [f]
    have heq : MulAut.conj g₂ = MulAut.conj g₁ * MulAut.conj (g₁⁻¹ * g₂) := by
      rw [← map_mul]; congr 1; group
    calc (MulAut.conj g₁ • A : Subgroup G)
        = MulAut.conj g₁ • (MulAut.conj (g₁⁻¹ * g₂) • A) := by rw [h_conj]
      _ = (MulAut.conj g₁ * MulAut.conj (g₁⁻¹ * g₂)) • A := by rw [mul_smul]
      _ = MulAut.conj g₂ • A := by rw [← heq]
  let f' : G ⧸ A → conjs := Quotient.lift f (fun a b => hf_lift a b)
  have hf_surj : Function.Surjective f' := by
    rintro ⟨B, g, rfl⟩
    exact ⟨⟦g⟧, rfl⟩
  have hf_inj : Function.Injective f' := by
    rintro ⟨g₁⟩ ⟨g₂⟩ hfeq
    change f g₁ = f g₂ at hfeq
    have hsub : (MulAut.conj g₁ • A : Subgroup G) = MulAut.conj g₂ • A := by
      exact Subtype.ext_iff.mp hfeq
    have h_step : (MulAut.conj (g₂⁻¹ * g₁) • A : Subgroup G) = A := by
      have heq : MulAut.conj (g₂⁻¹ * g₁) = MulAut.conj g₂⁻¹ * MulAut.conj g₁ := by
        rw [← map_mul]
      rw [heq, mul_smul, hsub, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    have h_mem : g₂⁻¹ * g₁ ∈ Subgroup.normalizer A := by
      rw [Subgroup.mem_normalizer_iff'']
      intro y
      have hmem : y ∈ MulAut.conj (g₂⁻¹ * g₁) • A ↔ y ∈ A := by rw [h_step]
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hmem
      have hcalc : (MulAut.conj (g₂⁻¹ * g₁))⁻¹ • y = (g₂⁻¹ * g₁)⁻¹ * y * (g₂⁻¹ * g₁) := by
        change (MulAut.conj (g₂⁻¹ * g₁)).symm y = _
        rw [MulAut.conj_symm_apply]
      rw [hcalc] at hmem
      exact hmem.symm
    rw [hNGA] at h_mem
    apply Quotient.sound
    change (QuotientGroup.leftRel A) g₁ g₂
    rw [QuotientGroup.leftRel_apply]
    have : (g₂⁻¹ * g₁)⁻¹ ∈ A := A.inv_mem h_mem
    simpa [mul_inv_rev] using this
  have hbij : Function.Bijective f' := ⟨hf_inj, hf_surj⟩
  have h_card_eq : Nat.card conjs = Nat.card (G ⧸ A) :=
    (Nat.card_congr (Equiv.ofBijective f' hbij)).symm
  have h_card_conjs : conjs.ncard = A.index := by
    rw [← Nat.card_coe_set_eq, h_card_eq, ← Subgroup.index]
  simpa [hconjs_def] using h_card_conjs

/-- **Isaacs Lemma 6.5**: Let `A` be a subgroup of a finite group `G`, and suppose `A ∩ A^g = 1`
for all `g ∈ G \ A`. Then the set of elements of `G` not conjugate to any nonidentity element of `A`
has cardinality `|G : A|`. -/
theorem card_notConjugateSet_eq_index [Finite G]
    (A : Subgroup G)
    (h_TI : ∀ g : G, g ∉ A → A ⊓ (MulAut.conj g • A) = ⊥) :
    (notConjugateSet A).ncard = A.index := by
  classical
  have : Fintype G := Fintype.ofFinite G
  rcases eq_or_ne A ⊥ with rfl | hA_ne
  · -- Case `A = ⊥`: every element of `G` lies in `notConjugateSet ⊥`.
    have h_univ : notConjugateSet (⊥ : Subgroup G) = Set.univ := by
      ext x
      simp only [notConjugateSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      intro a ha h_ne
      rw [Subgroup.mem_bot] at ha
      exact absurd ha h_ne
    rw [h_univ, Set.ncard_univ, Subgroup.index_bot]
  · -- Case `A ≠ ⊥`.  Build the orbit of `A` under conjugation; counted to give `A.index`.
    -- The complement of `notConjugateSet A` is `⋃_{B ∈ orbit} (B.carrier \ {1})`.
    -- Pairwise disjoint outside `{1}`; sum gives `index · (|A| - 1)`.
    -- The set of conjugates of `A` (indexed as subgroups of `G`).
    set conjs : Set (Subgroup G) := Set.range (fun g : G => MulAut.conj g • A) with hconjs_def
    -- (Step a) Identify the complement.
    have h_compl :
        (notConjugateSet A)ᶜ = ⋃ B ∈ conjs, ((B : Set G) \ {1}) := by
      ext x
      constructor
      · -- `x ∈ Xᶜ`: exists `a ∈ A`, `a ≠ 1`, `IsConj a x`.
        intro hx
        rw [Set.mem_compl_iff, notConjugateSet, Set.mem_ofPred_eq] at hx
        push Not at hx
        obtain ⟨a, haA, ha_ne, hIsConj⟩ := hx
        -- `IsConj a x` means `∃ c, c * a * c⁻¹ = x`.
        rcases (isConj_iff (a := a) (b := x)).1 hIsConj with ⟨c, hcax⟩
        rw [Set.mem_iUnion]
        refine ⟨MulAut.conj c • A, ?_⟩
        rw [Set.mem_iUnion]
        refine ⟨⟨c, rfl⟩, ?_, ?_⟩
        · -- `x = c * a * c⁻¹ ∈ MulAut.conj c • A`.
          rw [← hcax]
          have hca : c * a * c⁻¹ = MulAut.conj c a := by simp [MulAut.conj_apply]
          rw [hca, Subgroup.coe_pointwise_smul]
          exact Set.smul_mem_smul_set haA
        · -- `x ≠ 1` since `a ≠ 1` and `x = c a c⁻¹`.
          rw [Set.mem_singleton_iff]
          rw [← hcax]
          intro hcax_one
          apply ha_ne
          have heq : c⁻¹ * (c * a * c⁻¹) * c = a := by group
          rw [hcax_one] at heq
          group at heq
          exact heq.symm
      · -- `x ∈ ⋃...`: extract `c`, get `IsConj a x`.
        intro hx
        rw [Set.mem_iUnion] at hx
        obtain ⟨B, hB⟩ := hx
        rw [Set.mem_iUnion] at hB
        obtain ⟨hBconj, hxB_diff⟩ := hB
        rw [hconjs_def, Set.mem_range] at hBconj
        obtain ⟨c, rfl⟩ := hBconj
        obtain ⟨hxB, hx_ne⟩ := hxB_diff
        rw [Set.mem_singleton_iff] at hx_ne
        rw [Subgroup.coe_pointwise_smul] at hxB
        rcases hxB with ⟨a, haA, hax⟩
        rw [Set.mem_compl_iff]
        intro h_all
        apply h_all a haA
        · -- `a ≠ 1` since `x ≠ 1` and `x = MulAut.conj c a`.
          intro ha_one
          apply hx_ne
          rw [← hax, ha_one]; simp
        · -- `IsConj a x` from `x = MulAut.conj c a = c * a * c⁻¹`.
          refine (isConj_iff (a := a) (b := x)).2 ⟨c, ?_⟩
          rw [← hax]; simp [MulAut.conj_apply]
    -- (Step b) `conjs` is finite (image of finite type).
    have h_conjs_fin : conjs.Finite := by
      rw [hconjs_def]; exact Set.finite_range _
    -- (Step c) Pairwise disjoint outside `{1}`.
    have h_disj : conjs.PairwiseDisjoint (fun B : Subgroup G => (B : Set G) \ {1}) := by
      intro B hB B' hB' hBB'
      simp only [hconjs_def, Set.mem_range] at hB hB'
      obtain ⟨h, rfl⟩ := hB
      obtain ⟨k, rfl⟩ := hB'
      have h_inter_bot : (MulAut.conj h • A : Subgroup G) ⊓ (MulAut.conj k • A) = ⊥ :=
        TI_conjugate h_TI h k hBB'
      -- Now derive Set-level disjointness of the `\ {1}` subsets.
      rw [Function.onFun, Set.disjoint_left]
      intro x hxB hxB'
      have hx_inter : x ∈ ((MulAut.conj h • A : Subgroup G) ⊓ (MulAut.conj k • A) :
          Subgroup G) := by
        rw [Subgroup.mem_inf]
        exact ⟨hxB.1, hxB'.1⟩
      rw [h_inter_bot, Subgroup.mem_bot] at hx_inter
      exact hxB.2 hx_inter
    -- (Step d) Cardinality of each diff is `Nat.card A - 1` (independent of conjugate).
    have h_card_each : ∀ B ∈ conjs, ((B : Set G) \ {1}).ncard = Nat.card A - 1 := by
      intro B hB
      simp only [hconjs_def, Set.mem_range] at hB
      obtain ⟨g, rfl⟩ := hB
      -- `MulAut.conj g • A` has the same cardinality as `A` (subgroup map is a MulEquiv).
      have h_card_B : ((MulAut.conj g • A : Subgroup G) : Set G).ncard = Nat.card A := by
        rw [← Nat.card_coe_set_eq]
        exact (Nat.card_congr (Subgroup.equivSMul (MulAut.conj g) A).toEquiv).symm
      -- Now `(B.carrier \ {1}).ncard = |B| - 1`.
      have h1_mem : (1 : G) ∈ ((MulAut.conj g • A : Subgroup G) : Set G) :=
        Subgroup.one_mem _
      rw [Set.ncard_sdiff (Set.singleton_subset_iff.mpr h1_mem) (Set.finite_singleton _),
          Set.ncard_singleton, h_card_B]
    -- (Step e) Cardinality of `conjs` is `A.index`.
    have h_card_conjs : conjs.ncard = A.index := by
      simpa [hconjs_def] using ncard_conjugates_eq_index_of_TI hA_ne h_TI
    -- (Step f) Apply `Set.Finite.ncard_biUnion` (disjoint union counting).
    have h_card_union :
        (⋃ B ∈ conjs, ((B : Set G) \ {1})).ncard = ∑ᶠ B ∈ conjs, ((B : Set G) \ {1}).ncard :=
      Set.Finite.ncard_biUnion h_conjs_fin (fun _ _ => Set.toFinite _) h_disj
    -- (Step g) The finsum is `conjs.ncard * (Nat.card A - 1)`.
    have h_finsum :
        ∑ᶠ B ∈ conjs, ((B : Set G) \ {1}).ncard = conjs.ncard * (Nat.card A - 1) := by
      rw [finsum_mem_eq_finite_toFinset_sum _ h_conjs_fin]
      rw [Finset.sum_congr rfl (fun B hB => h_card_each B
            ((Set.Finite.mem_toFinset h_conjs_fin).mp hB))]
      rw [Finset.sum_const, smul_eq_mul]
      congr 1
      rw [Set.ncard_eq_toFinset_card _ h_conjs_fin]
    -- (Step h) Combine: |Xᶜ| = |G| - |X| = A.index · (|A| - 1).  Solve for |X| = A.index.
    have hX_fin : (notConjugateSet A).Finite := Set.toFinite _
    have hXc_fin : (notConjugateSet A)ᶜ.Finite := Set.toFinite _
    have h_total : (notConjugateSet A).ncard + ((notConjugateSet A)ᶜ).ncard = Nat.card G :=
      Set.ncard_add_ncard_compl _ hX_fin hXc_fin
    rw [h_compl, h_card_union, h_finsum, h_card_conjs] at h_total
    -- |G| = A.index * |A| (Lagrange).
    have h_lagrange : A.index * Nat.card A = Nat.card G := by
      rw [mul_comm]; exact Subgroup.card_mul_index A
    -- |A| ≥ 1 since A is a subgroup.
    have hA_pos : 0 < Nat.card A := Nat.card_pos
    -- Rewrite `A.index * (|A| - 1) = A.index * |A| - A.index` so omega can finish.
    have h_expand : A.index * (Nat.card A - 1) = A.index * Nat.card A - A.index := by
      rw [Nat.mul_sub_one]
    rw [h_expand, h_lagrange] at h_total
    -- h_total : (notConjugateSet A).ncard + (Nat.card G - A.index) = Nat.card G
    -- and A.index ≤ Nat.card G (from h_lagrange and hA_pos), so:
    have hA_index_le : A.index ≤ Nat.card G := by
      have := h_lagrange
      nlinarith
    omega

end

section

/-- A finite partition of a group by proper nonidentity subgroups, in the sense of Isaacs §6B.

The parts are a `Finset` because Lemma 6.8 uses the cardinality of the partition. -/
structure SubgroupPartition (G : Type*) [Group G] where
  /-- The finite set of subgroup parts. -/
  parts : Finset (Subgroup G)
  /-- Every part is nonidentity. -/
  nontrivial : ∀ X, X ∈ parts → X ≠ ⊥
  /-- Every part is proper. -/
  proper : ∀ X, X ∈ parts → X ≠ ⊤
  /-- The parts cover the whole group. -/
  cover : ∀ g : G, ∃ X, X ∈ parts ∧ g ∈ X
  /-- Distinct parts intersect trivially. -/
  inf_eq_bot_of_ne : ∀ {X Y}, X ∈ parts → Y ∈ parts → X ≠ Y → X ⊓ Y = ⊥

namespace SubgroupPartition

private theorem finite_subgroups_of_finite {G : Type*} [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

private noncomputable def subgroupsOfCard (G : Type*) [Group G] [Finite G] (n : ℕ) :
    Finset (Subgroup G) := by
  classical
  haveI : Finite (Subgroup G) := finite_subgroups_of_finite (G := G)
  haveI : Fintype (Subgroup G) := Fintype.ofFinite (Subgroup G)
  exact Finset.univ.filter fun H => Nat.card H = n

private theorem mem_subgroupsOfCard {G : Type*} [Group G] [Finite G] {n : ℕ}
    {H : Subgroup G} :
    H ∈ subgroupsOfCard G n ↔ Nat.card H = n := by
  classical
  unfold subgroupsOfCard
  have : Finite (Subgroup G) := finite_subgroups_of_finite (G := G)
  have : Fintype (Subgroup G) := Fintype.ofFinite (Subgroup G)
  simp

variable {G : Type*} [Group G] (partn : SubgroupPartition G)

/-- The set of parts is nonempty. -/
theorem parts_card_pos : 0 < partn.parts.card := by
  obtain ⟨X, hX, _⟩ := partn.cover (1 : G)
  exact Finset.card_pos.mpr ⟨X, hX⟩

/-- A nonidentity element cannot lie in two distinct parts. -/
theorem eq_of_mem_ne_one {X Y : Subgroup G}
    (hX : X ∈ partn.parts) (hY : Y ∈ partn.parts)
    {g : G} (hgX : g ∈ X) (hgY : g ∈ Y) (hg : g ≠ 1) :
    X = Y := by
  by_contra hXY
  have hInf : X ⊓ Y = ⊥ := partn.inf_eq_bot_of_ne hX hY hXY
  have hgInf : g ∈ X ⊓ Y := ⟨hgX, hgY⟩
  have hg_one : g = 1 := by
    simpa [hInf] using hgInf
  exact hg hg_one

/-- Every nonidentity element lies in a unique partition part. -/
theorem existsUnique_part_of_ne_one {g : G} (hg : g ≠ 1) :
    ∃! X : Subgroup G, X ∈ partn.parts ∧ g ∈ X := by
  obtain ⟨X, hX, hgX⟩ := partn.cover g
  refine ⟨X, ⟨hX, hgX⟩, ?_⟩
  intro Y hY
  exact partn.eq_of_mem_ne_one hY.1 hX hY.2 hgX hg

/-- The unique partition part containing a nonidentity element. -/
noncomputable def partOfNeOne (g : {g : G // g ≠ 1}) :
    {X : Subgroup G // X ∈ partn.parts} :=
  ⟨(partn.existsUnique_part_of_ne_one g.2).choose,
    (partn.existsUnique_part_of_ne_one g.2).choose_spec.1.1⟩

/-- The chosen part really contains the nonidentity element. -/
theorem mem_partOfNeOne (g : {g : G // g ≠ 1}) :
    (g : G) ∈ (partn.partOfNeOne g).1 :=
  (partn.existsUnique_part_of_ne_one g.2).choose_spec.1.2

/-- Forget the partition part from a partition-indexed nonidentity element. -/
def nonidentitySigmaTo
    (p : Σ X : {X : Subgroup G // X ∈ partn.parts}, {x : X.1 // x ≠ 1}) :
    {g : G // g ≠ 1} :=
  ⟨(p.2.1 : G), fun hg => p.2.2 (Subtype.ext hg)⟩

/-- Forgetting the partition part is injective because nonidentity elements occur in a unique
part. -/
theorem nonidentitySigmaTo_injective :
    Function.Injective partn.nonidentitySigmaTo := by
  intro p q hpq
  rcases p with ⟨X, x⟩
  rcases q with ⟨Y, y⟩
  have hxyA : ((x.1 : X.1) : G) = ((y.1 : Y.1) : G) :=
    congrArg Subtype.val hpq
  have hx_ne : ((x.1 : X.1) : G) ≠ 1 := fun hx => x.2 (Subtype.ext hx)
  have hY_mem_x : ((x.1 : X.1) : G) ∈ Y.1 := by
    simp [hxyA]
  have hXY : X = Y := by
    apply Subtype.ext
    exact partn.eq_of_mem_ne_one X.2 Y.2 x.1.2 hY_mem_x hx_ne
  cases hXY
  have hxy : x = y := by
    apply Subtype.ext
    apply Subtype.ext
    exact hxyA
  cases hxy
  rfl

/-- Forgetting the partition part is surjective: choose the unique part containing `g`. -/
theorem nonidentitySigmaTo_surjective :
    Function.Surjective partn.nonidentitySigmaTo := by
  intro g
  refine ⟨⟨partn.partOfNeOne g,
    ⟨⟨g.1, partn.mem_partOfNeOne g⟩, ?_⟩⟩, ?_⟩
  · intro h
    exact g.2 (congrArg Subtype.val h)
  · ext
    rfl

/-- The number of nonidentity elements in a finite group, as a subtype. -/
private theorem card_ne_one_subtype {G : Type*} [Group G] [Finite G] :
    Nat.card {g : G // g ≠ 1} = Nat.card G - 1 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hfilter :
      (Finset.univ.filter fun g : G => g ≠ 1) = Finset.univ.erase 1 := by
    ext g
    simp
  calc
    Nat.card {g : G // g ≠ 1}
        = Fintype.card {g : G // g ≠ 1} := Nat.card_eq_fintype_card
    _ = (Finset.univ.filter fun g : G => g ≠ 1).card := Fintype.card_subtype _
    _ = Fintype.card G - 1 := by
      rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ (1 : G)), Finset.card_univ]
    _ = Nat.card G - 1 := by rw [Nat.card_eq_fintype_card]

/-- Counting nonidentity elements through a subgroup partition. If every part has size `c`,
then `|Π| * (c - 1) = |G| - 1`. -/
theorem parts_card_mul_sub_one_eq_card_sub_one [Finite G] {c : ℕ}
    (hcard : ∀ X, X ∈ partn.parts → Nat.card X = c) :
    partn.parts.card * (c - 1) = Nat.card G - 1 := by
  classical
  let domain :=
    Σ X : {X : Subgroup G // X ∈ partn.parts}, {x : X.1 // x ≠ 1}
  let codomain := {g : G // g ≠ 1}
  have : Fintype {X : Subgroup G // X ∈ partn.parts} := inferInstance
  have hdomain_sigma :
      Nat.card domain =
        ∑ X : {X : Subgroup G // X ∈ partn.parts}, Nat.card {x : X.1 // x ≠ 1} := by
    rw [Nat.card_sigma]
  have hdomain_const :
      Nat.card domain = partn.parts.card * (c - 1) := by
    calc
      Nat.card domain
          = ∑ X : {X : Subgroup G // X ∈ partn.parts},
              Nat.card {x : X.1 // x ≠ 1} := hdomain_sigma
      _ = ∑ _X : {X : Subgroup G // X ∈ partn.parts}, (c - 1) := by
        refine Finset.sum_congr rfl ?_
        intro X _hX
        rw [card_ne_one_subtype (G := X.1), hcard X.1 X.2]
      _ = Fintype.card {X : Subgroup G // X ∈ partn.parts} * (c - 1) := by
        simp
      _ = partn.parts.card * (c - 1) := by
        rw [Fintype.card_coe partn.parts]
  have hbij : Function.Bijective partn.nonidentitySigmaTo :=
    ⟨partn.nonidentitySigmaTo_injective, partn.nonidentitySigmaTo_surjective⟩
  have hdomain_codomain : Nat.card domain = Nat.card codomain :=
    Nat.card_congr (Equiv.ofBijective partn.nonidentitySigmaTo hbij)
  rw [hdomain_const, card_ne_one_subtype (G := G)] at hdomain_codomain
  exact hdomain_codomain

/-- The textbook partition of an elementary abelian group of order `p^2`: its parts are all
subgroups of order `p`. -/
noncomputable def elementaryAbelianPrimeSquare
    {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hElem : OddOrder.GroupTheory.IsElementaryAbelian p G) (hCard : Nat.card G = p ^ 2) :
    SubgroupPartition G where
  parts := subgroupsOfCard G p
  nontrivial := by
    intro X hX hX_bot
    have hX_card : Nat.card X = p := mem_subgroupsOfCard.mp hX
    have hp_eq_one : p = 1 := by
      rw [← hX_card, hX_bot, Subgroup.card_bot]
    exact hp.ne_one hp_eq_one
  proper := by
    intro X hX hX_top
    have hX_card : Nat.card X = p := mem_subgroupsOfCard.mp hX
    have hp_eq_sq : p = p ^ 2 := by
      calc p = Nat.card X := hX_card.symm
        _ = Nat.card G := by rw [hX_top, Subgroup.card_top]
        _ = p ^ 2 := hCard
    have hp_lt_sq : p < p ^ 2 := by
      nth_rewrite 1 [← pow_one p]
      exact pow_lt_pow_right₀ hp.one_lt (by norm_num : (1 : ℕ) < 2)
    exact (ne_of_lt hp_lt_sq) hp_eq_sq
  cover := by
    have : Fact p.Prime := ⟨hp⟩
    intro g
    by_cases hg : g = 1
    · have hCard_gt_one : 1 < Nat.card G := by
        rw [hCard]
        exact one_lt_pow₀ hp.one_lt two_ne_zero
      have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp hCard_gt_one
      obtain ⟨x, hx_ne⟩ := exists_ne (1 : G)
      let X : Subgroup G := Subgroup.zpowers x
      have hX_card : Nat.card X = p := by
        rw [show X = Subgroup.zpowers x from rfl, Nat.card_zpowers,
          orderOf_eq_prime (hElem.pow_eq_one x) hx_ne]
      refine ⟨X, mem_subgroupsOfCard.mpr hX_card, ?_⟩
      rw [hg]
      exact X.one_mem
    · let X : Subgroup G := Subgroup.zpowers g
      have hX_card : Nat.card X = p := by
        rw [show X = Subgroup.zpowers g from rfl, Nat.card_zpowers,
          orderOf_eq_prime (hElem.pow_eq_one g) hg]
      exact ⟨X, mem_subgroupsOfCard.mpr hX_card, Subgroup.mem_zpowers g⟩
  inf_eq_bot_of_ne := by
    intro X Y hX hY hXY
    have hX_card : Nat.card X = p := mem_subgroupsOfCard.mp hX
    have hY_card : Nat.card Y = p := mem_subgroupsOfCard.mp hY
    by_contra hInf_ne
    have hInf_gt_one : 1 < Nat.card (X ⊓ Y : Subgroup G) := by
      have hpos : 0 < Nat.card (X ⊓ Y : Subgroup G) := Nat.card_pos
      have hne_one : Nat.card (X ⊓ Y : Subgroup G) ≠ 1 := by
        intro hcard
        exact hInf_ne (Subgroup.eq_bot_of_card_eq (X ⊓ Y : Subgroup G) hcard)
      omega
    have hInf_dvd_X : Nat.card (X ⊓ Y : Subgroup G) ∣ Nat.card X :=
      Subgroup.card_dvd_of_le inf_le_left
    have hInf_card : Nat.card (X ⊓ Y : Subgroup G) = p := by
      rw [hX_card] at hInf_dvd_X
      rcases (Nat.dvd_prime hp).mp hInf_dvd_X with h | h
      · exact False.elim ((not_lt_of_ge (le_of_eq h)) hInf_gt_one)
      · exact h
    have hInf_eq_X : X ⊓ Y = X := by
      apply Subgroup.eq_of_le_of_card_ge inf_le_left
      rw [hX_card, hInf_card]
    have hX_le_Y : X ≤ Y := by
      intro x hx
      have hxInf : x ∈ X ⊓ Y := by simpa [hInf_eq_X] using hx
      exact hxInf.2
    have hXY_eq : X = Y := by
      apply Subgroup.eq_of_le_of_card_ge hX_le_Y
      rw [hX_card, hY_card]
    exact hXY hXY_eq

/-- The elementary abelian `p^2` partition has the textbook cardinality `p + 1`. -/
theorem elementaryAbelianPrimeSquare_parts_card
    {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hElem : OddOrder.GroupTheory.IsElementaryAbelian p G) (hCard : Nat.card G = p ^ 2) :
    (elementaryAbelianPrimeSquare hp hElem hCard).parts.card = p + 1 := by
  let partn := elementaryAbelianPrimeSquare hp hElem hCard
  have hcount :
      partn.parts.card * (p - 1) = Nat.card G - 1 :=
    parts_card_mul_sub_one_eq_card_sub_one (partn := partn)
      (fun X hX => mem_subgroupsOfCard.mp hX)
  have hfactor : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    simpa using (Nat.sq_sub_sq p 1)
  have hmul : partn.parts.card * (p - 1) = (p + 1) * (p - 1) := by
    rw [hcount, hCard, hfactor]
  exact Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hp.one_lt) hmul

end SubgroupPartition

/-- Fixed points of the subgroup `H` under an action encoded by `φ : A →* MulAut U`. -/
def actionFixedPoints {A U : Type*} [Group A] [Group U]
    (φ : A →* MulAut U) (H : Subgroup A) : Subgroup U :=
  Subgroup.fixedPointsOfMulAut (φ.comp H.subtype)

@[simp]
theorem mem_actionFixedPoints {A U : Type*} [Group A] [Group U]
    {φ : A →* MulAut U} {H : Subgroup A} {u : U} :
    u ∈ actionFixedPoints φ H ↔ ∀ h : H, (φ h) u = u :=
  Iff.rfl

/-- Fixed points of a single acting element, i.e. the action-centralizer `C_U(a)`. -/
def actionFixedBy {A U : Type*} [Group A] [Group U]
    (φ : A →* MulAut U) (a : A) : Subgroup U where
  carrier := {u | (φ a) u = u}
  one_mem' := map_one (φ a)
  mul_mem' := by
    intro u v hu hv
    change (φ a) (u * v) = u * v
    rw [map_mul, hu, hv]
  inv_mem' := by
    intro u hu
    change (φ a) u⁻¹ = u⁻¹
    rw [map_inv, hu]

@[simp]
theorem mem_actionFixedBy {A U : Type*} [Group A] [Group U]
    {φ : A →* MulAut U} {a : A} {u : U} :
    u ∈ actionFixedBy φ a ↔ (φ a) u = u :=
  Iff.rfl

/-- The centralizer of an element equals the fixed subgroup of its cyclic closure. -/
theorem actionFixedBy_eq_actionFixedPoints_zpowers
    {A U : Type*} [Group A] [Group U] (φ : A →* MulAut U) (a : A) :
    actionFixedBy φ a = actionFixedPoints φ (Subgroup.zpowers a) := by
  ext u
  constructor
  · intro hu h
    have hh : (h : A) ∈ Subgroup.closure ({a} : Set A) := by
      simpa [Subgroup.zpowers_eq_closure] using h.property
    refine Subgroup.closure_induction
      (p := fun b _ => (φ b) u = u) ?mem ?one ?mul ?inv hh
    · intro b hb
      rw [Set.mem_singleton_iff.mp hb]
      exact hu
    · simp
    · intro b c _ _ hb hc
      simp [map_mul, hc, hb]
    · intro b _ hb
      calc
        (φ b⁻¹) u = (φ b)⁻¹ u := by rw [map_inv]
        _ = (φ b)⁻¹ ((φ b) u) := by rw [hb]
        _ = u := by simp
  · intro hu
    exact hu ⟨a, Subgroup.mem_zpowers a⟩

/-- `K = ⟨ C_U(a) | 1 ≠ a ∈ A ⟩`, the subgroup generated by all nontrivial
single-element action-centralizers. This is the subgroup denoted `K` in Isaacs Thm 6.21. -/
def nontrivialActionFixedByClosure {A U : Type*} [Group A] [Group U]
    (φ : A →* MulAut U) : Subgroup U :=
  Subgroup.closure {u | ∃ a : A, a ≠ 1 ∧ u ∈ actionFixedBy φ a}

/-- Each nonidentity element's action-centralizer is contained in the generated subgroup `K`. -/
theorem actionFixedBy_le_nontrivialActionFixedByClosure
    {A U : Type*} [Group A] [Group U] {φ : A →* MulAut U} {a : A} (ha : a ≠ 1) :
    actionFixedBy φ a ≤ nontrivialActionFixedByClosure φ := by
  intro u hu
  exact Subgroup.subset_closure ⟨a, ha, hu⟩

/-- To show `K ≤ L`, it is enough and necessary to show `C_U(a) ≤ L` for every `a ≠ 1`. -/
theorem nontrivialActionFixedByClosure_le_iff
    {A U : Type*} [Group A] [Group U] {φ : A →* MulAut U} {L : Subgroup U} :
    nontrivialActionFixedByClosure φ ≤ L ↔
      ∀ a : A, a ≠ 1 → actionFixedBy φ a ≤ L := by
  constructor
  · intro h a ha
    exact (actionFixedBy_le_nontrivialActionFixedByClosure (φ := φ) ha).trans h
  · intro h
    rw [nontrivialActionFixedByClosure]
    exact (Subgroup.closure_le _).mpr (by
      rintro u ⟨a, ha, hu⟩
      exact h a ha hu)

/-- If an invariant subgroup satisfies the Isaacs 6.21 generated-centralizer conclusion
internally, then it lies in the ambient generated-centralizer subgroup. -/
theorem subgroup_le_nontrivialActionFixedByClosure_of_closure_eq_top
    {A N : Type*} [Group A] [Group N] [MulDistribMulAction A N]
    {M : Subgroup N} [MulDistribMulAction A M]
    (hcompat : ∀ a : A, ∀ m : M, ((a • m : M) : N) = a • (m : N))
    (hMtop : nontrivialActionFixedByClosure (MulDistribMulAction.toMulAut A M) = ⊤) :
    M ≤ nontrivialActionFixedByClosure (MulDistribMulAction.toMulAut A N) := by
  let φM : A →* MulAut M := MulDistribMulAction.toMulAut A M
  let φN : A →* MulAut N := MulDistribMulAction.toMulAut A N
  let K : Subgroup N := nontrivialActionFixedByClosure φN
  intro n hn
  let m : M := ⟨n, hn⟩
  have hm : m ∈ nontrivialActionFixedByClosure φM := by
    rw [hMtop]
    exact Subgroup.mem_top m
  rw [nontrivialActionFixedByClosure] at hm
  have hmK : (m : N) ∈ K := by
    refine Subgroup.closure_induction
      (p := fun (x : M) _ => (x : N) ∈ K) ?mem ?one ?mul ?inv hm
    · rintro x ⟨a, ha, hx⟩
      have hxN : a • (x : N) = (x : N) := by
        have hx' := congrArg (fun y : M => (y : N)) hx
        simpa [φM, hcompat a x] using hx'
      exact Subgroup.subset_closure ⟨a, ha, by simpa [φN] using hxN⟩
    · simp [K]
    · intro x y _ _ hx hy
      exact K.mul_mem hx hy
    · intro x _ hx
      exact K.inv_mem hx
  change (m : N) ∈ K
  exact hmK

/-- If two acting elements commute, the second preserves the fixed subgroup of the first. -/
theorem actionFixedBy_invariant_of_commute
    {A U : Type*} [Group A] [Group U] {φ : A →* MulAut U}
    {a b : A} (hab : a * b = b * a) :
    ∀ u ∈ actionFixedBy φ a, (φ b) u ∈ actionFixedBy φ a := by
  intro u hu
  calc
    (φ a) ((φ b) u) = (φ (a * b)) u := by simp [map_mul]
    _ = (φ (b * a)) u := by rw [hab]
    _ = (φ b) ((φ a) u) := by simp [map_mul]
    _ = (φ b) u := by rw [hu]

/-- For abelian `A`, Isaacs's subgroup `K = ⟨C_U(a) | a ≠ 1⟩` is invariant under `A`. -/
theorem nontrivialActionFixedByClosure_invariant_of_commutative
    {A U : Type*} [Group A] [Group U] [IsMulCommutative A] (φ : A →* MulAut U) :
    ∀ b : A, ∀ u ∈ nontrivialActionFixedByClosure φ,
      (φ b) u ∈ nontrivialActionFixedByClosure φ := by
  intro b u hu
  rw [nontrivialActionFixedByClosure] at hu ⊢
  refine Subgroup.closure_induction
    (p := fun u _ => (φ b) u ∈
      Subgroup.closure {u | ∃ a : A, a ≠ 1 ∧ u ∈ actionFixedBy φ a})
    ?mem ?one ?mul ?inv hu
  · rintro u ⟨a, ha, hu⟩
    exact Subgroup.subset_closure
      ⟨a, ha, actionFixedBy_invariant_of_commute (φ := φ)
        (‹IsMulCommutative A›.is_comm.comm a b) u hu⟩
  · simp
  · intro u v _ _ hu hv
    simpa [map_mul] using Subgroup.mul_mem _ hu hv
  · intro u _ hu
    simpa [map_inv] using Subgroup.inv_mem _ hu

/-- If every nonidentity fixed subgroup lies in an invariant normal subgroup `M`, then the
induced action on `N/M` is Frobenius.

This is the formal "fixed points come from fixed points" step in Isaacs Thm 6.21. -/
theorem quotient_isFrobeniusAction_of_fixedBy_le
    {A N : Type*} [Group A] [Finite A] [Group N] [Finite N] [MulDistribMulAction A N]
    {M : Subgroup N} [M.Normal]
    (hM : ∀ a : A, ∀ m ∈ M, a • m ∈ M)
    (hCopAM : Nat.Coprime (Nat.card A) (Nat.card M))
    (hfixed : ∀ a : A, a ≠ 1 →
      actionFixedBy (MulDistribMulAction.toMulAut A N) a ≤ M) :
    @IsFrobeniusAction A (N ⧸ M) _ _
      (IsFrobeniusAction.invariantQuotientMulDistribMulAction M hM) := by
  classical
  let : MulDistribMulAction A (N ⧸ M) :=
    IsFrobeniusAction.invariantQuotientMulDistribMulAction M hM
  intro a ha q hq_ne hfix
  revert hq_ne hfix
  refine QuotientGroup.induction_on q ?_
  intro n hq_ne hfix
  let φ : A →* MulAut N := MulDistribMulAction.toMulAut A N
  let P : Subgroup A :=
    { carrier := {b | ∃ m ∈ M, φ b n = n * m}
      one_mem' := by
        refine ⟨1, M.one_mem, ?_⟩
        simp [φ]
      mul_mem' := by
        intro b c hb hc
        rcases hb with ⟨mb, hmb, hb⟩
        rcases hc with ⟨mc, hmc, hc⟩
        refine ⟨mb * (φ b) mc, M.mul_mem hmb (hM b mc hmc), ?_⟩
        calc
          φ (b * c) n = φ b (φ c n) := by
            change (b * c) • n = b • c • n
            rw [mul_smul]
          _ = φ b (n * mc) := by rw [hc]
          _ = φ b n * φ b mc := by simp
          _ = n * (mb * φ b mc) := by rw [hb]; group
      inv_mem' := by
        intro b hb
        rcases hb with ⟨m, hm, hb⟩
        refine ⟨((φ b⁻¹) m)⁻¹, M.inv_mem (hM b⁻¹ m hm), ?_⟩
        have hb' : n = φ b⁻¹ n * φ b⁻¹ m := by
          calc
            n = φ b⁻¹ (φ b n) := by simp [φ]
            _ = φ b⁻¹ (n * m) := by rw [hb]
            _ = φ b⁻¹ n * φ b⁻¹ m := by simp
        calc
          φ b⁻¹ n = (φ b⁻¹ n * φ b⁻¹ m) * (φ b⁻¹ m)⁻¹ := by group
          _ = n * (φ b⁻¹ m)⁻¹ := by rw [← hb'] }
  have haP : a ∈ P := by
    have hfix' : ((a • n : N) : N ⧸ M) = (n : N ⧸ M) := hfix
    have hdiv : (a • n) / n ∈ M := (QuotientGroup.eq_iff_div_mem (N := M)).mp hfix'
    have hMN : M.Normal := inferInstance
    have hm : n⁻¹ * (a • n) ∈ M := by
      rw [← hMN.mem_comm_iff]
      simpa [div_eq_mul_inv] using hdiv
    refine ⟨n⁻¹ * (a • n), hm, ?_⟩
    simp [φ]
  let C : Subgroup A := Subgroup.zpowers a
  let φC : C →* MulAut N := φ.comp C.subtype
  have hC_le_P : C ≤ P := Subgroup.zpowers_le.mpr haP
  have hM_inv_C : OddOrder.Isaacs.Ch03.IsAInvariant φC M := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro c m hm
    exact hM (c : A) m hm
  have hCopCM : Nat.Coprime (Nat.card C) (Nat.card M) :=
    hCopAM.coprime_dvd_left (Subgroup.card_subgroup_dvd_card C)
  have : IsCyclic C := Subgroup.isCyclic_zpowers a
  let : CommGroup C := IsCyclic.commGroup
  have hSolvC : Group.IsSolvable C ∨ Group.IsSolvable M := Or.inl inferInstance
  have hg_fix_C : ∀ c : C, ∃ m ∈ M, φC c n = n * m := by
    intro c
    simpa [φC, P] using hC_le_P c.2
  obtain ⟨x, hx_fixed, hx_coset⟩ :=
    OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient_of_coprime_normal
      (A := C) (G := N) (φ := φC) hCopCM hSolvC hM_inv_C hg_fix_C
  have hxM : x ∈ M :=
    hfixed a ha (by
      have := hx_fixed ⟨a, Subgroup.mem_zpowers a⟩
      simpa [φC, φ] using this)
  rcases hx_coset with ⟨m, hm, hx_eq⟩
  have hnM : n ∈ M := by
    have hxm : x * m⁻¹ ∈ M := M.mul_mem hxM (M.inv_mem hm)
    convert hxm using 1
    rw [hx_eq]
    group
  exact hq_ne ((QuotientGroup.eq_one_iff n).mpr hnM)

/-- A subgroup containing the commutator subgroup is normal.

This is the group-theoretic step used in Isaacs Thm 6.21 after proving `N' ≤ K`. -/
theorem normal_of_commutator_le {G : Type*} [Group G] {K : Subgroup G}
    (hcomm : _root_.commutator G ≤ K) : K.Normal := by
  rw [_root_.commutator_def] at hcomm
  exact (Subgroup.commutator_top_left_le_iff (H := K)).mp
    ((Subgroup.commutator_mono le_rfl (show K ≤ (⊤ : Subgroup G) from le_top)).trans hcomm)

/-- If `p` divides the index of `K`, no Sylow `p`-subgroup can lie inside `K`. -/
theorem sylow_not_le_of_prime_dvd_index
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {K : Subgroup G} (hpK : p ∣ K.index) :
    ¬ (P : Subgroup G) ≤ K := by
  intro hPK
  exact P.not_dvd_index (hpK.trans (Subgroup.index_dvd_of_le hPK))

/-- The Sylow step in Isaacs Thm 6.21.

If every proper `A`-invariant subgroup of `N` lies in `K`, and `p ∣ |N : K|`, then the
`A`-invariant Sylow `p`-subgroup supplied by Isaacs Thm 3.23(a) is all of `N`. -/
theorem exists_aInvariant_sylow_eq_top_of_prime_dvd_index_of_proper_invariant_le
    {A N : Type*} [Group A] [Finite A] [Group N] [Finite N] [MulDistribMulAction A N]
    {K : Subgroup N} {p : ℕ} [Fact p.Prime]
    (hCop : Nat.Coprime (Nat.card A) (Nat.card N))
    (hSolv : Group.IsSolvable A ∨ Group.IsSolvable N)
    (hpK : p ∣ K.index)
    (hproper : ∀ P : Subgroup N,
      (∀ a : A, ∀ n ∈ P, a • n ∈ P) → P ≠ ⊤ → P ≤ K) :
    ∃ P : Sylow p N,
      OddOrder.Isaacs.Ch03.IsAInvariant (MulDistribMulAction.toMulAut A N) (P : Subgroup N) ∧
        (P : Subgroup N) = ⊤ := by
  let φ : A →* MulAut N := MulDistribMulAction.toMulAut A N
  obtain ⟨P, hP_inv⟩ :=
    OddOrder.Isaacs.Ch04.exists_aInvariant_sylow (G := N) (A := A) (φ := φ)
      hCop hSolv p
  refine ⟨P, hP_inv, ?_⟩
  by_contra hP_top
  have hP_smul : ∀ a : A, ∀ n ∈ (P : Subgroup N), a • n ∈ (P : Subgroup N) := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem] at hP_inv
    intro a n hn
    simpa [φ] using hP_inv a n hn
  have hP_le_K : (P : Subgroup N) ≤ K :=
    hproper (P : Subgroup N) hP_smul hP_top
  exact sylow_not_le_of_prime_dvd_index P hpK hP_le_K

/-- The commutator subgroup is the proper invariant subgroup used in Isaacs Thm 6.21.

In the theorem's p-group case, `N` is solvable, so `N' < N`; invariance is functorial under
automorphisms. -/
theorem commutator_le_of_proper_invariant_le_of_isSolvable
    {A N : Type*} [Group A] [Group N] [Finite N] [Nontrivial N] [Group.IsSolvable N]
    [MulDistribMulAction A N] {K : Subgroup N}
    (hproper : ∀ P : Subgroup N,
      (∀ a : A, ∀ n ∈ P, a • n ∈ P) → P ≠ ⊤ → P ≤ K) :
    _root_.commutator N ≤ K := by
  let φ : A →* MulAut N := MulDistribMulAction.toMulAut A N
  have hcomm_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ (_root_.commutator N) :=
    OddOrder.Isaacs.Ch03.IsAInvariant.commutator_self φ
  have hcomm_smul :
      ∀ a : A, ∀ n ∈ _root_.commutator N, a • n ∈ _root_.commutator N := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem] at hcomm_inv
    intro a n hn
    simpa [φ] using hcomm_inv a n hn
  exact hproper (_root_.commutator N) hcomm_smul
    (Group.IsSolvable.commutator_lt_top_of_nontrivial N).ne

/-- Isaacs's product `u_H = ∏_{h ∈ H} u^h`, written for an action by automorphisms. -/
noncomputable def orbitProduct {A U : Type*} [Group A] [CommGroup U]
    (φ : A →* MulAut U) (H : Subgroup A) [Fintype H] (u : U) : U :=
  ∏ h : H, (φ h) u

/-- The orbit product over the nonidentity elements of a subgroup. -/
noncomputable def subgroupNonidentityOrbitProduct
    {A U : Type*} [Group A] [CommGroup U]
    (φ : A →* MulAut U) (H : Subgroup A) [Fintype H] (u : U) : U :=
  by
    classical
    exact ∏ h : {h : H // h ≠ 1}, (φ (h.1 : A)) u

/-- The orbit product over the nonidentity elements of the whole group. -/
noncomputable def nonidentityOrbitProduct
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (u : U) : U :=
  by
    classical
    letI : Fintype A := Fintype.ofFinite A
    exact ∏ a : {a : A // a ≠ 1}, (φ a.1) u

/-- The orbit product `u_H` is fixed by every element of `H`. -/
theorem orbitProduct_mem_actionFixedPoints {A U : Type*} [Group A] [CommGroup U]
    (φ : A →* MulAut U) (H : Subgroup A) [Fintype H] (u : U) :
    orbitProduct φ H u ∈ actionFixedPoints φ H := by
  intro x
  calc
    (φ (x : A)) (orbitProduct φ H u)
        = ∏ h : H, (φ (x : A)) ((φ h) u) := by
            simp [orbitProduct]
    _ = ∏ h : H, (φ ((x * h : H) : A)) u := by
          refine Finset.prod_congr rfl ?_
          intro h _hh
          simp [map_mul]
    _ = ∏ h : H, (φ (h : A)) u := by
          exact Fintype.prod_equiv (Equiv.mulLeft x)
            (fun h : H => (φ ((x * h : H) : A)) u)
            (fun h : H => (φ (h : A)) u)
            (fun h => rfl)

/-- Split an orbit product into the identity contribution and the nonidentity contributions. -/
theorem orbitProduct_eq_mul_subgroupNonidentityOrbitProduct
    {A U : Type*} [Group A] [CommGroup U]
    (φ : A →* MulAut U) (H : Subgroup A) [Fintype H] (u : U) :
    orbitProduct φ H u = u * subgroupNonidentityOrbitProduct φ H u := by
  classical
  rw [orbitProduct, subgroupNonidentityOrbitProduct]
  simpa using Fintype.prod_eq_mul_prod_subtype_ne
    (fun h : H => (φ (h : A)) u) (1 : H)

/-- Fixed points are antitone in the acting subgroup. -/
theorem actionFixedPoints_antitone {A U : Type*} [Group A] [Group U]
    {φ : A →* MulAut U} {H K : Subgroup A} (hHK : H ≤ K) :
    actionFixedPoints φ K ≤ actionFixedPoints φ H := by
  intro u hu h
  exact hu ⟨h, hHK h.property⟩

/-- If the fixed points of `H` are trivial, then Isaacs's orbit product over `H` is `1`. -/
theorem orbitProduct_eq_one_of_actionFixedPoints_eq_bot
    {A U : Type*} [Group A] [CommGroup U]
    (φ : A →* MulAut U) (H : Subgroup A) [Fintype H] (u : U)
    (hH : actionFixedPoints φ H = ⊥) :
    orbitProduct φ H u = 1 := by
  have hmem := orbitProduct_mem_actionFixedPoints φ H u
  have : orbitProduct φ H u ∈ (⊥ : Subgroup U) := by
    simpa [hH] using hmem
  simpa using this

/-- The product over all partition parts of the orbit products. -/
noncomputable def partitionOrbitProduct
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (partn : SubgroupPartition A) (u : U) : U :=
  ∏ x ∈ partn.parts,
    (letI : Fintype x := Fintype.ofFinite x
     orbitProduct φ x u)

/-- The product over all partition parts and all nonidentity elements in those parts. -/
noncomputable def partitionNonidentityOrbitProduct
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (partn : SubgroupPartition A) (u : U) : U :=
  ∏ X ∈ partn.parts,
    (letI : Fintype X := Fintype.ofFinite X
     subgroupNonidentityOrbitProduct φ X u)

/-- The same nonidentity product, indexed by the sigma type of partition parts and
nonidentity elements in each part. The finite instances are supplied internally so callers do
not need to expose dependent `Fintype` arguments. -/
noncomputable def partitionSigmaNonidentityOrbitProduct
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (partn : SubgroupPartition A) (u : U) : U := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype {X : Subgroup A // X ∈ partn.parts} := Fintype.ofFinite _
  letI : ∀ X : {X : Subgroup A // X ∈ partn.parts}, Fintype X.1 :=
    fun X => Fintype.ofFinite X.1
  letI :
      ∀ X : {X : Subgroup A // X ∈ partn.parts}, Fintype {x : X.1 // x ≠ 1} :=
    fun X => Subtype.fintype (fun x : X.1 => x ≠ 1)
  exact ∏ p : (Σ X : {X : Subgroup A // X ∈ partn.parts}, {x : X.1 // x ≠ 1}),
    (φ ((p.2.1 : p.1.1) : A)) u

/-- The partition nonidentity product is the sigma-indexed nonidentity product. -/
theorem partitionNonidentityOrbitProduct_eq_partitionSigmaNonidentityOrbitProduct
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (partn : SubgroupPartition A) (u : U) :
    partitionNonidentityOrbitProduct φ partn u =
      partitionSigmaNonidentityOrbitProduct φ partn u := by
  classical
  rw [partitionNonidentityOrbitProduct, partitionSigmaNonidentityOrbitProduct]
  let : Fintype A := Fintype.ofFinite A
  let : Fintype {X : Subgroup A // X ∈ partn.parts} := Fintype.ofFinite _
  let : ∀ X : {X : Subgroup A // X ∈ partn.parts}, Fintype X.1 :=
    fun X => Fintype.ofFinite X.1
  let :
      ∀ X : {X : Subgroup A // X ∈ partn.parts}, Fintype {x : X.1 // x ≠ 1} :=
    fun X => Subtype.fintype (fun x : X.1 => x ≠ 1)
  rw [Finset.prod_subtype partn.parts (fun X => Iff.rfl)
    (fun X : Subgroup A =>
      (letI : Fintype X := Fintype.ofFinite X
       subgroupNonidentityOrbitProduct φ X u))]
  change (∏ X : {X : Subgroup A // X ∈ partn.parts},
      (letI : Fintype X.1 := Fintype.ofFinite X.1
       subgroupNonidentityOrbitProduct φ X.1 u)) =
    ∏ p : (Σ X : {X : Subgroup A // X ∈ partn.parts}, {x : X.1 // x ≠ 1}),
      (φ ((p.2.1 : p.1.1) : A)) u
  simpa [subgroupNonidentityOrbitProduct] using
    (Fintype.prod_sigma
      (fun p : (Σ X : {X : Subgroup A // X ∈ partn.parts}, {x : X.1 // x ≠ 1}) =>
        (φ ((p.2.1 : p.1.1) : A)) u)).symm

/-- The sigma-indexed nonidentity product over a partition is the ordinary nonidentity product:
nonidentity elements occur in exactly one partition part. -/
theorem partitionSigmaNonidentityOrbitProduct_eq_nonidentityOrbitProduct
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (partn : SubgroupPartition A) (u : U) :
    partitionSigmaNonidentityOrbitProduct φ partn u =
      nonidentityOrbitProduct φ u := by
  classical
  rw [partitionSigmaNonidentityOrbitProduct, nonidentityOrbitProduct]
  let : Fintype A := Fintype.ofFinite A
  let : Fintype {X : Subgroup A // X ∈ partn.parts} := Fintype.ofFinite _
  let : ∀ X : {X : Subgroup A // X ∈ partn.parts}, Fintype X.1 :=
    fun X => Fintype.ofFinite X.1
  let :
      ∀ X : {X : Subgroup A // X ∈ partn.parts}, Fintype {x : X.1 // x ≠ 1} :=
    fun X => Subtype.fintype (fun x : X.1 => x ≠ 1)
  exact Fintype.prod_bijective partn.nonidentitySigmaTo
    ⟨partn.nonidentitySigmaTo_injective, partn.nonidentitySigmaTo_surjective⟩
    (fun p : (Σ X : {X : Subgroup A // X ∈ partn.parts}, {x : X.1 // x ≠ 1}) =>
      (φ ((p.2.1 : p.1.1) : A)) u)
    (fun a : {a : A // a ≠ 1} => (φ a.1) u)
    (fun _ => rfl)

/-- The nonidentity factors over a subgroup partition multiply to the nonidentity factors over
the whole group. -/
theorem partitionNonidentityOrbitProduct_eq_nonidentityOrbitProduct
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (partn : SubgroupPartition A) (u : U) :
    partitionNonidentityOrbitProduct φ partn u =
      nonidentityOrbitProduct φ u := by
  rw [partitionNonidentityOrbitProduct_eq_partitionSigmaNonidentityOrbitProduct φ partn u,
    partitionSigmaNonidentityOrbitProduct_eq_nonidentityOrbitProduct φ partn u]

/-- The orbit product over the top subgroup, with the finite instance supplied from `A`. -/
noncomputable def topOrbitProduct
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (u : U) : U :=
  letI : Fintype (⊤ : Subgroup A) := Fintype.ofFinite (⊤ : Subgroup A)
  orbitProduct φ (⊤ : Subgroup A) u

/-- Split the top orbit product into the identity contribution and nonidentity contributions. -/
theorem topOrbitProduct_eq_mul_nonidentityOrbitProduct
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (u : U) :
    topOrbitProduct φ u = u * nonidentityOrbitProduct φ u := by
  classical
  rw [topOrbitProduct, orbitProduct, nonidentityOrbitProduct]
  let : Fintype A := Fintype.ofFinite A
  let : Fintype (⊤ : Subgroup A) := Fintype.ofFinite (⊤ : Subgroup A)
  calc
    (∏ h : (⊤ : Subgroup A), (φ (h : A)) u)
        = ∏ a : A, (φ a) u := by
            exact Fintype.prod_equiv Subgroup.topEquiv.toEquiv
              (fun h : (⊤ : Subgroup A) => (φ (h : A)) u)
              (fun a : A => (φ a) u)
              (fun _ => rfl)
    _ = u * ∏ a : {a : A // a ≠ 1}, (φ a.1) u := by
          simpa using Fintype.prod_eq_mul_prod_subtype_ne
            (fun a : A => (φ a) u) (1 : A)

/-- Split the partition product into the identity contributions and the nonidentity
contributions. -/
theorem partitionOrbitProduct_eq_pow_mul_partitionNonidentityOrbitProduct
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (partn : SubgroupPartition A) (u : U) :
    partitionOrbitProduct φ partn u =
      u ^ partn.parts.card * partitionNonidentityOrbitProduct φ partn u := by
  classical
  rw [partitionOrbitProduct, partitionNonidentityOrbitProduct]
  calc
    (∏ X ∈ partn.parts,
      (letI : Fintype X := Fintype.ofFinite X
       orbitProduct φ X u))
        = ∏ X ∈ partn.parts,
            (u *
              (letI : Fintype X := Fintype.ofFinite X
               subgroupNonidentityOrbitProduct φ X u)) := by
            refine Finset.prod_congr rfl ?_
            intro X hX
            let : Fintype X := Fintype.ofFinite X
            exact orbitProduct_eq_mul_subgroupNonidentityOrbitProduct φ X u
    _ = (∏ X ∈ partn.parts, u) *
          ∏ X ∈ partn.parts,
            (letI : Fintype X := Fintype.ofFinite X
             subgroupNonidentityOrbitProduct φ X u) := by
            simp_rw [Finset.prod_mul_distrib]
    _ = u ^ partn.parts.card *
          ∏ X ∈ partn.parts,
            (letI : Fintype X := Fintype.ofFinite X
             subgroupNonidentityOrbitProduct φ X u) := by
            simp

/-- Isaacs 6.8 counting identity for orbit products over a subgroup partition. -/
theorem partitionOrbitProduct_identity
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (partn : SubgroupPartition A) (u : U) :
    partitionOrbitProduct φ partn u =
      topOrbitProduct φ u * u ^ (partn.parts.card - 1) := by
  classical
  have hcard : partn.parts.card = partn.parts.card.pred.succ :=
    (Nat.succ_pred_eq_of_pos partn.parts_card_pos).symm
  have hpow : u ^ partn.parts.card = u * u ^ (partn.parts.card - 1) := by
    calc
      u ^ partn.parts.card
          = u ^ partn.parts.card.pred.succ := by
              exact congrArg (fun n => u ^ n) hcard
      _ = u ^ partn.parts.card.pred * u := by
            rw [pow_succ]
      _ = u ^ (partn.parts.card - 1) * u := by
            rw [Nat.pred_eq_sub_one]
      _ = u * u ^ (partn.parts.card - 1) := by
            rw [mul_comm]
  calc
    partitionOrbitProduct φ partn u
        = u ^ partn.parts.card * partitionNonidentityOrbitProduct φ partn u := by
            exact partitionOrbitProduct_eq_pow_mul_partitionNonidentityOrbitProduct φ partn u
    _ = u ^ partn.parts.card * nonidentityOrbitProduct φ u := by
          rw [partitionNonidentityOrbitProduct_eq_nonidentityOrbitProduct φ partn u]
    _ = (u * u ^ (partn.parts.card - 1)) * nonidentityOrbitProduct φ u := by
          rw [hpow]
    _ = (u * nonidentityOrbitProduct φ u) * u ^ (partn.parts.card - 1) := by
          ac_rfl
    _ = topOrbitProduct φ u * u ^ (partn.parts.card - 1) := by
          rw [← topOrbitProduct_eq_mul_nonidentityOrbitProduct φ u]

/-- If every partition part has trivial fixed points, then every part orbit product is `1`. -/
theorem partitionOrbitProduct_eq_one_of_parts_fixedPoints_eq_bot
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (partn : SubgroupPartition A) (u : U)
    (hfix : ∀ X, X ∈ partn.parts → actionFixedPoints φ X = ⊥) :
    partitionOrbitProduct φ partn u = 1 := by
  classical
  rw [partitionOrbitProduct, Finset.prod_eq_one]
  intro X hX
  let : Fintype X := Fintype.ofFinite X
  exact orbitProduct_eq_one_of_actionFixedPoints_eq_bot φ X u (hfix X hX)

/-- If every partition part has trivial fixed points, then the full fixed-point subgroup is
trivial. -/
theorem actionFixedPoints_top_eq_bot_of_parts_fixedPoints_eq_bot
    {A U : Type*} [Group A] [Group U]
    (φ : A →* MulAut U) (partn : SubgroupPartition A)
    (hfix : ∀ X, X ∈ partn.parts → actionFixedPoints φ X = ⊥) :
    actionFixedPoints φ (⊤ : Subgroup A) = ⊥ := by
  apply eq_bot_iff.mpr
  intro u hu
  obtain ⟨X, hX, _h1X⟩ := partn.cover (1 : A)
  have huX : u ∈ actionFixedPoints φ X :=
    actionFixedPoints_antitone (show X ≤ (⊤ : Subgroup A) from le_top) hu
  simpa [hfix X hX] using huX

/-- Once the Isaacs 6.8 counting identity is known, some part has nontrivial fixed points.

This packages the non-counting half of Lemma 6.8: assuming the product identity
`∏_{X∈Π} u_X = u_A * u^(|Π|-1)`, any `u` with `u^(|Π|-1) ≠ 1` forces a partition
part whose action on `U` has nontrivial fixed points. -/
theorem exists_part_actionFixedPoints_ne_bot_of_orbitProduct_identity
    {A U : Type*} [Group A] [Finite A] [CommGroup U]
    (φ : A →* MulAut U) (partn : SubgroupPartition A)
    (hidentity : ∀ u : U,
      partitionOrbitProduct φ partn u =
        topOrbitProduct φ u * u ^ (partn.parts.card - 1))
    {u : U} (hu : u ^ (partn.parts.card - 1) ≠ 1) :
    ∃ X, X ∈ partn.parts ∧ actionFixedPoints φ X ≠ ⊥ := by
  by_contra hnone
  have hfix : ∀ X, X ∈ partn.parts → actionFixedPoints φ X = ⊥ := by
    intro X hX
    by_contra hne
    exact hnone ⟨X, hX, hne⟩
  have hprod :
      partitionOrbitProduct φ partn u = 1 :=
    partitionOrbitProduct_eq_one_of_parts_fixedPoints_eq_bot φ partn u hfix
  have htop :
      actionFixedPoints φ (⊤ : Subgroup A) = ⊥ :=
    actionFixedPoints_top_eq_bot_of_parts_fixedPoints_eq_bot φ partn hfix
  have htop_one :
      topOrbitProduct φ u = 1 := by
    rw [topOrbitProduct]
    let : Fintype (⊤ : Subgroup A) := Fintype.ofFinite (⊤ : Subgroup A)
    exact orbitProduct_eq_one_of_actionFixedPoints_eq_bot φ (⊤ : Subgroup A) u htop
  have hident := hidentity u
  rw [hprod, htop_one, one_mul] at hident
  exact hu hident.symm

/-- A nontrivial acting subgroup has trivial fixed points under a Frobenius action. -/
theorem actionFixedPoints_eq_bot_of_isFrobeniusAction
    {A U : Type*} [Group A] [Group U] [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) {H : Subgroup A} (hH : H ≠ ⊥) :
    actionFixedPoints (MulDistribMulAction.toMulAut A U) H = ⊥ := by
  apply eq_bot_iff.mpr
  intro u hu
  by_contra hu_ne
  obtain ⟨a, haH, ha_ne⟩ : ∃ a : A, a ∈ H ∧ a ≠ 1 := by
    by_contra hnone
    push Not at hnone
    apply hH
    ext a
    constructor
    · intro ha
      rw [hnone a ha]
      exact Subgroup.one_mem ⊥
    · intro ha
      rw [Subgroup.mem_bot] at ha
      rw [ha]
      exact H.one_mem
  have hfix := hu ⟨a, haH⟩
  have hsmul : a • u = u := by
    simpa using hfix
  exact hFrob a ha_ne u hu_ne hsmul

/-- In a finite group, an element whose order is coprime to `n` cannot satisfy `u ^ n = 1`. -/
theorem pow_ne_one_of_ne_one_of_coprime_natCard
    {U : Type*} [Group U] [Finite U] {n : ℕ}
    (hcop : n.Coprime (Nat.card U)) {u : U} (hu : u ≠ 1) :
    u ^ n ≠ 1 := by
  intro hpow
  have horder_n : orderOf u ∣ n := orderOf_dvd_of_pow_eq_one hpow
  have horder_card : orderOf u ∣ Nat.card U := orderOf_dvd_natCard u
  have horder_eq_one : orderOf u = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop.symm horder_card horder_n
  exact hu (orderOf_eq_one_iff.mp horder_eq_one)

/-- A nontrivial finite group has an element with `u ^ n ≠ 1` whenever `n` is coprime to
its order. -/
theorem exists_pow_ne_one_of_nontrivial_coprime_natCard
    {U : Type*} [Group U] [Finite U] [Nontrivial U] {n : ℕ}
    (hcop : n.Coprime (Nat.card U)) :
    ∃ u : U, u ^ n ≠ 1 := by
  obtain ⟨u, hu⟩ := exists_ne (1 : U)
  exact ⟨u, pow_ne_one_of_ne_one_of_coprime_natCard hcop hu⟩

/-- Lemma 6.8 immediately contradicts a Frobenius action once the counting identity supplies
a suitable element. -/
theorem false_of_frobeniusAction_orbitProduct_identity
    {A U : Type*} [Group A] [Finite A] [CommGroup U] [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (partn : SubgroupPartition A)
    (hidentity : ∀ u : U,
      partitionOrbitProduct (MulDistribMulAction.toMulAut A U) partn u =
        topOrbitProduct (MulDistribMulAction.toMulAut A U) u * u ^ (partn.parts.card - 1))
    {u : U} (hu : u ^ (partn.parts.card - 1) ≠ 1) :
    False := by
  obtain ⟨X, hX, hXfix_ne⟩ :=
    exists_part_actionFixedPoints_ne_bot_of_orbitProduct_identity
      (MulDistribMulAction.toMulAut A U) partn hidentity hu
  have hXfix_eq :
      actionFixedPoints (MulDistribMulAction.toMulAut A U) X = ⊥ :=
    actionFixedPoints_eq_bot_of_isFrobeniusAction hFrob (partn.nontrivial X hX)
  exact hXfix_ne hXfix_eq

/-- Lemma 6.8 rules out a Frobenius action whenever a subgroup partition has a part-count
exponent detected by some element of `U`. -/
theorem false_of_frobeniusAction_partition_of_nontrivial_power
    {A U : Type*} [Group A] [Finite A] [CommGroup U] [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (partn : SubgroupPartition A)
    {u : U} (hu : u ^ (partn.parts.card - 1) ≠ 1) :
    False :=
  false_of_frobeniusAction_orbitProduct_identity hFrob partn
    (fun u => partitionOrbitProduct_identity (MulDistribMulAction.toMulAut A U) partn u) hu

/-- Lemma 6.8 in the coprime form used in Theorem 6.9, with the counting identity discharged. -/
theorem false_of_frobeniusAction_partition_of_coprime_card
    {A U : Type*} [Group A] [Finite A] [CommGroup U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (partn : SubgroupPartition A)
    (hcop : (partn.parts.card - 1).Coprime (Nat.card U)) :
    False := by
  obtain ⟨u, hu⟩ :=
    exists_pow_ne_one_of_nontrivial_coprime_natCard (U := U) hcop
  exact false_of_frobeniusAction_partition_of_nontrivial_power hFrob partn hu

/-- Isaacs Theorem 6.9 contradiction package: if the acting group has a subgroup partition
whose part count is `1 + n` with `n ∣ |A|`, then it cannot act Frobeniusly on a nontrivial
finite abelian group. -/
theorem false_of_frobeniusAction_partition_of_sub_one_dvd_actor_card
    {A U : Type*} [Group A] [Finite A] [CommGroup U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (partn : SubgroupPartition A)
    (hdvd : partn.parts.card - 1 ∣ Nat.card A) :
    False := by
  have hcop_AU : (Nat.card A).Coprime (Nat.card U) := by
    classical
    have : Fintype A := Fintype.ofFinite A
    have : Fintype U := Fintype.ofFinite U
    simpa only [Fintype.card_eq_nat_card] using
      (IsFrobeniusAction.coprime_card (A := A) (N := U) hFrob).symm
  exact false_of_frobeniusAction_partition_of_coprime_card hFrob partn
    (hcop_AU.coprime_dvd_left hdvd)

/-- Same contradiction package, in the textual `|Π| = 1 + n` form used in Isaacs 6.9. -/
theorem false_of_frobeniusAction_partition_of_card_eq_succ_and_dvd_actor_card
    {A U : Type*} [Group A] [Finite A] [CommGroup U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (partn : SubgroupPartition A) {n : ℕ}
    (hcard : partn.parts.card = n + 1) (hdvd : n ∣ Nat.card A) :
    False := by
  apply false_of_frobeniusAction_partition_of_sub_one_dvd_actor_card hFrob partn
  rwa [hcard, Nat.add_sub_cancel]

/-- **Isaacs Thm 6.9**: a Frobenius actor cannot be elementary abelian of order `p^2`. -/
theorem false_of_frobeniusAction_isElementaryAbelian_card_prime_sq
    {A U : Type*} [Group A] [Finite A] [CommGroup U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) {p : ℕ} (hp : p.Prime)
    (hElem : OddOrder.GroupTheory.IsElementaryAbelian p A) (hCard : Nat.card A = p ^ 2) :
    False := by
  let partn := SubgroupPartition.elementaryAbelianPrimeSquare hp hElem hCard
  have hparts :
      partn.parts.card = p + 1 :=
    SubgroupPartition.elementaryAbelianPrimeSquare_parts_card hp hElem hCard
  have hdvd : p ∣ Nat.card A := by
    rw [hCard, pow_two]
    exact dvd_mul_right p p
  exact false_of_frobeniusAction_partition_of_card_eq_succ_and_dvd_actor_card
    hFrob partn hparts hdvd

end

end OddOrder.Isaacs.Ch06


