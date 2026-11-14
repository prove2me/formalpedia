-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Submod_Supermodular
-- name    : BCFGJPSSV26_Stable_Submod_Supermodular
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:07.197557+00:00
-- url     : https://prove2.me/theorems/d0ed2aa1-ef90-45ae-ae89-735d81122307
-- title:
--   BCFGJPSSV26.Stable.Submod.Supermodular — Submodularity of minimum-type functions
-- statement:
--   This is module `BCFGJPSSV26.Stable.Submod.Supermodular` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   Abstract facts behind [BCFGJPSSV26b, Section 5]:
--
--   * **Submodular and monotone set functions** (`BCFGJPSSV26.Stable.IsSubmod`,
--     `BCFGJPSSV26.Stable.IsMonoF`).
--   * **Minima** ([BCFGJPSSV26b, Claim B.1]): `X ↦ min(V, min_{i ∈ X} aᵢ)` has decreasing marginal
--     decreases (`BCFGJPSSV26.Stable.minOver_supermod`).
--   * **Sums of the `z` smallest values** (in place of [BCFGJPSSV26b, Claims B.3–B.5]):
--     `s_z(v) = min_{|Z| = z} ∑_{c ∈ Z} v_c` (`BCFGJPSSV26.Stable.sumSmallest`) satisfies the
--     exchange inequality `s_z(u') + s_z(u ∧ b) ≤ s_z(u) + s_z(u' ∧ b)` for `u' ≤ u`
--     (`BCFGJPSSV26.Stable.sumSmallest_exchange`), proved by pairing the elements of two minimizers.
--     Applied with `u = h(X)`, `u' = h(Y)` for `X ⊆ Y` and `b` the values after adding an element,
--     it says that the sum of the `z` smallest of functions of the minimum type is supermodular.
--
--   **Contents.** The module is published as a whole: 12 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Submod_Supermodular`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Submod/Supermodular.lean

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Submod.Supermodular` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Submodularity of minimum-type functions

Abstract facts behind [BCFGJPSSV26b, Section 5]:

* **Submodular and monotone set functions** (`BCFGJPSSV26.Stable.IsSubmod`,
  `BCFGJPSSV26.Stable.IsMonoF`).
* **Minima** ([BCFGJPSSV26b, Claim B.1]): `X ↦ min(V, min_{i ∈ X} aᵢ)` has decreasing marginal
  decreases (`BCFGJPSSV26.Stable.minOver_supermod`).
* **Sums of the `z` smallest values** (in place of [BCFGJPSSV26b, Claims B.3–B.5]):
  `s_z(v) = min_{|Z| = z} ∑_{c ∈ Z} v_c` (`BCFGJPSSV26.Stable.sumSmallest`) satisfies the
  exchange inequality `s_z(u') + s_z(u ∧ b) ≤ s_z(u) + s_z(u' ∧ b)` for `u' ≤ u`
  (`BCFGJPSSV26.Stable.sumSmallest_exchange`), proved by pairing the elements of two minimizers.
  Applied with `u = h(X)`, `u' = h(Y)` for `X ⊆ Y` and `b` the values after adding an element,
  it says that the sum of the `z` smallest of functions of the minimum type is supermodular.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

variable {U : Type*} [DecidableEq U]

/-- A **submodular** set function: adding `e` gains less on a larger set. -/
def IsSubmod (f : Finset U → ℝ) : Prop :=
  ∀ A B : Finset U, A ⊆ B → ∀ e, f (insert e B) - f B ≤ f (insert e A) - f A

/-- A **monotone** set function. -/
def IsMonoF (f : Finset U → ℝ) : Prop := ∀ A B : Finset U, A ⊆ B → f A ≤ f B

/-- `min(V, min_{i ∈ X} aᵢ)`. -/
noncomputable def minOver (V : ℝ) (a : U → ℝ) (X : Finset U) : ℝ := X.fold min V a

theorem minOver_insert (V : ℝ) (a : U → ℝ) (X : Finset U) (e : U) :
    minOver V a (insert e X) = min (a e) (minOver V a X) := by
  unfold minOver
  by_cases he : e ∈ X
  · rw [insert_eq_of_mem he]
    refine (min_eq_right ?_).symm
    exact (Finset.fold_min_le _).2 (Or.inr ⟨e, he, le_rfl⟩)
  · rw [fold_insert he]

omit [DecidableEq U] in
theorem minOver_anti (V : ℝ) (a : U → ℝ) {X Y : Finset U} (hXY : X ⊆ Y) :
    minOver V a Y ≤ minOver V a X := by
  unfold minOver
  refine (Finset.le_fold_min _).2 ⟨(Finset.fold_min_le _).2 (Or.inl le_rfl), fun x hx ↦ ?_⟩
  exact (Finset.fold_min_le _).2 (Or.inr ⟨x, hXY hx, le_rfl⟩)

/-- **Minima** ([BCFGJPSSV26b, Claim B.1]): `min(V, min_{i ∈ X} aᵢ)` is non-increasing, and its
decrease on adding `e` is larger on smaller sets. -/
theorem minOver_supermod (V : ℝ) (a : U → ℝ) {X Y : Finset U} (hXY : X ⊆ Y) (e : U) :
    minOver V a Y ≤ minOver V a X ∧
      minOver V a Y - minOver V a (insert e Y) ≤ minOver V a X - minOver V a (insert e X) := by
  have h := minOver_anti V a hXY
  refine ⟨h, ?_⟩
  rw [minOver_insert, minOver_insert, min_def, min_def]
  split_ifs <;> linarith

/-! ### Sums of the smallest values -/

variable {ι : Type*}

/-- The sum of the `z` smallest values of `v` on `A` (`0` if `z > |A|`). -/
noncomputable def sumSmallest (z : ℕ) (A : Finset ι) (v : ι → ℝ) : ℝ :=
  if h : (A.powersetCard z).Nonempty then (A.powersetCard z).inf' h fun Z ↦ ∑ c ∈ Z, v c else 0

theorem exists_sumSmallest_eq {z : ℕ} {A : Finset ι} (hz : z ≤ A.card) (v : ι → ℝ) :
    ∃ Z ⊆ A, Z.card = z ∧ ∑ c ∈ Z, v c = sumSmallest z A v := by
  have hne : (A.powersetCard z).Nonempty := powersetCard_nonempty.2 hz
  obtain ⟨Z, hZ, h⟩ := exists_mem_eq_inf' hne fun Z ↦ ∑ c ∈ Z, v c
  obtain ⟨hZA, hZc⟩ := mem_powersetCard.1 hZ
  refine ⟨Z, hZA, hZc, ?_⟩
  unfold sumSmallest
  rw [dif_pos hne, h]

theorem sumSmallest_le {z : ℕ} {A Z : Finset ι} (hZ : Z ⊆ A) (hZz : Z.card = z) (v : ι → ℝ) :
    sumSmallest z A v ≤ ∑ c ∈ Z, v c := by
  have hmem : Z ∈ A.powersetCard z := mem_powersetCard.2 ⟨hZ, hZz⟩
  unfold sumSmallest
  rw [dif_pos ⟨Z, hmem⟩]
  exact inf'_le _ hmem

theorem sumSmallest_mono {z : ℕ} {A : Finset ι} {u v : ι → ℝ} (h : ∀ c ∈ A, u c ≤ v c) :
    sumSmallest z A u ≤ sumSmallest z A v := by
  unfold sumSmallest
  split_ifs with hne
  · refine le_inf' hne _ fun Z hZ ↦ (inf'_le _ hZ).trans ?_
    exact sum_le_sum fun c hc ↦ h c ((mem_powersetCard.1 hZ).1 hc)
  · exact le_rfl

/-- The exchange step: two `z`-sets for `u` and `u' ∧ b` give two `z`-sets for `u'` and
`u ∧ b`, inside their union, with no larger total. -/
private theorem exchange_aux [DecidableEq ι] {A : Finset ι} {u u' : ι → ℝ} (b : ι → ℝ)
    (h : ∀ c ∈ A, u' c ≤ u c) (n : ℕ) :
    ∀ Z₁ Z₂ : Finset ι, Z₁ ⊆ A → Z₂ ⊆ A → (Z₁ \ Z₂).card = n → Z₁.card = Z₂.card →
      ∃ Z₃ Z₄ : Finset ι, Z₃ ⊆ Z₁ ∪ Z₂ ∧ Z₄ ⊆ Z₁ ∪ Z₂ ∧ Z₃.card = Z₁.card ∧
        Z₄.card = Z₂.card ∧
        ∑ c ∈ Z₃, u' c + ∑ c ∈ Z₄, min (u c) (b c) ≤
          ∑ c ∈ Z₁, u c + ∑ c ∈ Z₂, min (u' c) (b c) := by
  induction n with
  | zero =>
    intro Z₁ Z₂ h1 h2 hn hc
    have hsub : Z₁ ⊆ Z₂ := by rwa [card_eq_zero, sdiff_eq_empty_iff_subset] at hn
    have heq : Z₁ = Z₂ := eq_of_subset_of_card_le hsub hc.ge
    subst heq
    refine ⟨Z₁, Z₁, subset_union_left, subset_union_left, rfl, rfl, ?_⟩
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_le_sum fun c hc ↦ ?_
    have := h c (h1 hc)
    rw [min_def, min_def]
    split_ifs <;> linarith
  | succ n ih =>
    intro Z₁ Z₂ h1 h2 hn hc
    obtain ⟨c, hc1⟩ : (Z₁ \ Z₂).Nonempty := by rw [← card_pos, hn]; omega
    have hcard : (Z₂ \ Z₁).card = (Z₁ \ Z₂).card := by
      have e1 := card_sdiff_add_card_inter Z₁ Z₂
      have e2 := card_sdiff_add_card_inter Z₂ Z₁
      rw [inter_comm] at e2
      omega
    obtain ⟨c', hc2⟩ : (Z₂ \ Z₁).Nonempty := by rw [← card_pos, hcard, hn]; omega
    rw [mem_sdiff] at hc1 hc2
    have hn' : (Z₁.erase c \ Z₂.erase c').card = n := by
      have : Z₁.erase c \ Z₂.erase c' = (Z₁ \ Z₂).erase c := by
        ext x
        simp only [mem_sdiff, mem_erase]
        constructor
        · rintro ⟨⟨hxc, hx1⟩, hx2⟩
          refine ⟨hxc, hx1, fun hx ↦ hx2 ⟨?_, hx⟩⟩
          rintro rfl
          exact hc2.2 hx1
        · rintro ⟨hxc, hx1, hx2⟩
          exact ⟨⟨hxc, hx1⟩, fun hx ↦ hx2 hx.2⟩
      rw [this, card_erase_of_mem (mem_sdiff.2 hc1), hn]
      rfl
    have hc' : (Z₁.erase c).card = (Z₂.erase c').card := by
      rw [card_erase_of_mem hc1.1, card_erase_of_mem hc2.1, hc]
    obtain ⟨Z₃, Z₄, h3, h4, hc3, hc4, hs⟩ := ih (Z₁.erase c) (Z₂.erase c')
      ((erase_subset _ _).trans h1) ((erase_subset _ _).trans h2) hn' hc'
    have hcU : c ∉ Z₁.erase c ∪ Z₂.erase c' := by
      simp only [mem_union, mem_erase, not_or, not_and]
      exact ⟨fun h ↦ absurd rfl h, fun _ h ↦ hc1.2 h⟩
    have hc'U : c' ∉ Z₁.erase c ∪ Z₂.erase c' := by
      simp only [mem_union, mem_erase, not_or, not_and]
      exact ⟨fun _ h ↦ hc2.2 h, fun h ↦ absurd rfl h⟩
    have hc3' : c ∉ Z₃ := fun h ↦ hcU (h3 h)
    have hc4' : c ∉ Z₄ := fun h ↦ hcU (h4 h)
    have hc'3 : c' ∉ Z₃ := fun h ↦ hc'U (h3 h)
    have hc'4 : c' ∉ Z₄ := fun h ↦ hc'U (h4 h)
    have hU : Z₁.erase c ∪ Z₂.erase c' ⊆ Z₁ ∪ Z₂ :=
      union_subset_union (erase_subset _ _) (erase_subset _ _)
    have hs1 := add_sum_erase Z₁ u hc1.1
    have hs2 := add_sum_erase Z₂ (fun c ↦ min (u' c) (b c)) hc2.1
    have hpos1 : 0 < Z₁.card := card_pos.2 ⟨c, hc1.1⟩
    have hpos2 : 0 < Z₂.card := card_pos.2 ⟨c', hc2.1⟩
    rw [card_erase_of_mem hc1.1] at hc3
    rw [card_erase_of_mem hc2.1] at hc4
    have huc := h c (h1 hc1.1)
    by_cases hb : u' c' ≤ b c'
    · refine ⟨insert c' Z₃, insert c Z₄, insert_subset (mem_union_right _ hc2.1) (h3.trans hU),
        insert_subset (mem_union_left _ hc1.1) (h4.trans hU), ?_, ?_, ?_⟩
      · rw [card_insert_of_notMem hc'3]; omega
      · rw [card_insert_of_notMem hc4']; omega
      · rw [sum_insert hc'3, sum_insert hc4', ← hs1, ← hs2, min_eq_left hb]
        have := min_le_left (u c) (b c)
        linarith
    · push Not at hb
      refine ⟨insert c Z₃, insert c' Z₄, insert_subset (mem_union_left _ hc1.1) (h3.trans hU),
        insert_subset (mem_union_right _ hc2.1) (h4.trans hU), ?_, ?_, ?_⟩
      · rw [card_insert_of_notMem hc3']; omega
      · rw [card_insert_of_notMem hc'4]; omega
      · rw [sum_insert hc3', sum_insert hc'4, ← hs1, ← hs2, min_eq_right hb.le]
        have := min_le_right (u c') (b c')
        linarith

/-- **The exchange inequality**: for `u' ≤ u` and any `b`,
`s_z(u') + s_z(u ∧ b) ≤ s_z(u) + s_z(u' ∧ b)`. -/
theorem sumSmallest_exchange (z : ℕ) (A : Finset ι) {u u' : ι → ℝ} (b : ι → ℝ)
    (h : ∀ c ∈ A, u' c ≤ u c) :
    sumSmallest z A u' + sumSmallest z A (fun c ↦ min (u c) (b c)) ≤
      sumSmallest z A u + sumSmallest z A (fun c ↦ min (u' c) (b c)) := by
  classical
  by_cases hz : z ≤ A.card
  · obtain ⟨Z₁, h1, hc1, hs1⟩ := exists_sumSmallest_eq hz u
    obtain ⟨Z₂, h2, hc2, hs2⟩ := exists_sumSmallest_eq hz fun c ↦ min (u' c) (b c)
    obtain ⟨Z₃, Z₄, h3, h4, hc3, hc4, hs⟩ :=
      exchange_aux b h _ Z₁ Z₂ h1 h2 rfl (hc1.trans hc2.symm)
    have e3 := sumSmallest_le (h3.trans (union_subset h1 h2)) (hc3.trans hc1) u'
    have e4 := sumSmallest_le (h4.trans (union_subset h1 h2)) (hc4.trans hc2)
      fun c ↦ min (u c) (b c)
    rw [← hs1, ← hs2]
    linarith
  · have hne : ¬ (A.powersetCard z).Nonempty := by
      rw [powersetCard_nonempty]
      exact hz
    unfold sumSmallest
    simp only [hne, dite_false]
    norm_num

end BCFGJPSSV26.Stable


