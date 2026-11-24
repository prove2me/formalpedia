-- Prove2me | Definitions.Def_BalanceSpecificaton_BlockEntropy
-- name    : BalanceSpecificaton_BlockEntropy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:08:45.84318+00:00
-- url     : https://prove2.me/theorems/62b23364-07bb-4559-bf57-ba584d75f16c
-- title:
--   Block Entropy
-- statement:
--   Definitions and structural lemmas for Block Entropy, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/BlockEntropy.lean

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_EntropyAlgebra
public import Mathlib.Tactic
public import Theorems.Thm_BalanceSpecification_FiniteEntropy_shannon_joint_le
public import Theorems.Thm_BalanceSpecification_IsInvariant_cylinder_real_eq_zero
public import Theorems.Thm_BalanceSpecification_block_mem_language
public import Theorems.Thm_BalanceSpecification_cylinder_append
public import Theorems.Thm_BalanceSpecification_cylinder_eq_empty_of_not_mem_language
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_disjoint_cylinder
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_language_factorial
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_measurableSet_cylinder
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_sum_cylinder_real_eq_one
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.cylinder_nil
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage


set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification
open MeasureTheory Filter
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
def blockDistribution (μ : ProbabilityMeasure X.carrier) (n : ℕ) :
    ↥(wordFinset (language X) n) → ℝ :=
  fun w => (μ : Measure X.carrier).real (cylinder X w.val 0)
def blockEntropy (μ : ProbabilityMeasure X.carrier) (n : ℕ) : ℝ :=
  ∑ w ∈ wordFinset (language X) n,
    -(μ : Measure X.carrier).real (cylinder X w 0) *
      Real.log ((μ : Measure X.carrier).real (cylinder X w 0))
theorem blockDistribution_sum (μ : ProbabilityMeasure X.carrier) (n : ℕ) :
    ∑ w, blockDistribution μ n w = 1 := by
  change (∑ w : ↥(wordFinset (language X) n),
    (μ : Measure X.carrier).real (cylinder X w.val 0)) = 1
  calc
    _ = ∑ w ∈ wordFinset (language X) n,
        (μ : Measure X.carrier).real (cylinder X w 0) := Finset.sum_coe_sort _ _
    _ = 1 := sum_cylinder_real_eq_one X μ n 0
omit [DiscreteTopology A] [BorelSpace A] in
theorem blockEntropy_eq_shannon (μ : ProbabilityMeasure X.carrier) (n : ℕ) :
    blockEntropy μ n = FiniteEntropy.shannon (blockDistribution μ n) := by
  symm
  exact Finset.sum_coe_sort (wordFinset (language X) n)
    (fun w : Word A => -(μ : Measure X.carrier).real (cylinder X w 0) *
      Real.log ((μ : Measure X.carrier).real (cylinder X w 0)))
omit [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A] in
/-- Adjacent right-cylinder refinements partition the cylinder of their prefix. -/
theorem iUnion_cylinder_append_right (u : Word A) (n : ℕ) (k : ℤ) :
    (⋃ v ∈ wordFinset (language X) n, cylinder X (u ++ v) k) = cylinder X u k := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hx
    rw [cylinder_append] at hxv
    exact hxv.1
  · intro hx
    let v := block x.val (k + u.length) n
    have hv : v ∈ wordFinset (language X) n := mem_wordFinset.mpr
      ⟨block_mem_language x.property _ _, length_block _ _ _⟩
    apply Set.mem_iUnion₂.mpr
    refine ⟨v, hv, ?_⟩
    rw [cylinder_append]
    refine ⟨hx, ?_⟩
    change block x.val (k + u.length) v.length = v
    rw [length_block]
omit [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A] in
/-- Adjacent left-cylinder refinements partition the cylinder of their suffix. -/
theorem iUnion_cylinder_append_left (v : Word A) (m : ℕ) (k : ℤ) :
    (⋃ u ∈ wordFinset (language X) m, cylinder X (u ++ v) k) = cylinder X v (k + m) := by
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu, hxu⟩ := Set.mem_iUnion₂.mp hx
    rw [cylinder_append] at hxu
    simpa only [(mem_wordFinset.mp hu).2] using hxu.2
  · intro hx
    let u := block x.val k m
    have hu : u ∈ wordFinset (language X) m := mem_wordFinset.mpr
      ⟨block_mem_language x.property _ _, length_block _ _ _⟩
    apply Set.mem_iUnion₂.mpr
    refine ⟨u, hu, ?_⟩
    rw [cylinder_append]
    constructor
    · change block x.val k u.length = u
      rw [length_block]
    · simpa only [u, length_block] using hx
theorem sum_cylinder_append_right (μ : ProbabilityMeasure X.carrier)
    (u : Word A) (n : ℕ) (k : ℤ) :
    (∑ v ∈ wordFinset (language X) n,
      (μ : Measure X.carrier).real (cylinder X (u ++ v) k)) =
        (μ : Measure X.carrier).real (cylinder X u k) := by
  have hd : Set.PairwiseDisjoint (wordFinset (language X) n : Set (Word A))
      (fun v => cylinder X (u ++ v) k) := by
    intro v hv w hw hvw
    apply Set.disjoint_left.mpr
    intro x hx hy
    dsimp only at hx hy
    rw [cylinder_append] at hx hy
    exact Set.disjoint_left.mp
      (disjoint_cylinder X ((mem_wordFinset.mp hv).2.trans (mem_wordFinset.mp hw).2.symm)
        hvw (k + u.length)) hx.2 hy.2
  rw [← measureReal_biUnion_finset hd (fun v _ => measurableSet_cylinder X (u ++ v) k),
    iUnion_cylinder_append_right]
theorem sum_cylinder_append_left (μ : ProbabilityMeasure X.carrier)
    (v : Word A) (m : ℕ) (k : ℤ) :
    (∑ u ∈ wordFinset (language X) m,
      (μ : Measure X.carrier).real (cylinder X (u ++ v) k)) =
        (μ : Measure X.carrier).real (cylinder X v (k + m)) := by
  have hd : Set.PairwiseDisjoint (wordFinset (language X) m : Set (Word A))
      (fun u => cylinder X (u ++ v) k) := by
    intro u hu w hw huw
    apply Set.disjoint_left.mpr
    intro x hx hy
    dsimp only at hx hy
    rw [cylinder_append] at hx hy
    exact Set.disjoint_left.mp
      (disjoint_cylinder X ((mem_wordFinset.mp hu).2.trans (mem_wordFinset.mp hw).2.symm)
        huw k) hx.1 hy.1
  rw [← measureReal_biUnion_finset hd (fun u _ => measurableSet_cylinder X (u ++ v) k),
    iUnion_cylinder_append_left]
def jointBlockDistribution (μ : ProbabilityMeasure X.carrier) (m n : ℕ) :
    ↥(wordFinset (language X) m) × ↥(wordFinset (language X) n) → ℝ :=
  fun uv => (μ : Measure X.carrier).real (cylinder X (uv.1.val ++ uv.2.val) 0)
theorem jointBlockDistribution_row (μ : ProbabilityMeasure X.carrier) (m n : ℕ)
    (u : ↥(wordFinset (language X) m)) :
    ∑ v, jointBlockDistribution μ m n (u, v) = blockDistribution μ m u := by
  calc
    _ = ∑ v ∈ wordFinset (language X) n,
        (μ : Measure X.carrier).real (cylinder X (u.val ++ v) 0) := Finset.sum_coe_sort _ _
    _ = _ := sum_cylinder_append_right μ u.val n 0
theorem jointBlockDistribution_col {μ : ProbabilityMeasure X.carrier} (hInv : IsInvariant μ)
    (m n : ℕ) (v : ↥(wordFinset (language X) n)) :
    ∑ u, jointBlockDistribution μ m n (u, v) = blockDistribution μ n v := by
  calc
    _ = ∑ u ∈ wordFinset (language X) m,
        (μ : Measure X.carrier).real (cylinder X (u ++ v.val) 0) := Finset.sum_coe_sort _ _
    _ = (μ : Measure X.carrier).real (cylinder X v.val (0 + (m : ℤ))) :=
      sum_cylinder_append_left μ v.val m 0
    _ = _ := hInv.cylinder_real_eq_zero v.val (0 + (m : ℤ))
theorem jointBlockDistribution_sum (μ : ProbabilityMeasure X.carrier) (m n : ℕ) :
    ∑ uv, jointBlockDistribution μ m n uv = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [jointBlockDistribution_row]
  exact blockDistribution_sum μ m
omit [DiscreteTopology A] [BorelSpace A] in
/-- Reindexing by concatenation identifies joint entropy with the longer block entropy. -/
theorem shannon_jointBlockDistribution (μ : ProbabilityMeasure X.carrier) (m n : ℕ) :
    FiniteEntropy.shannon (jointBlockDistribution μ m n) = blockEntropy μ (m + n) := by
  classical
  let f : Word A → ℝ := fun w => -(μ : Measure X.carrier).real (cylinder X w 0) *
    Real.log ((μ : Measure X.carrier).real (cylinder X w 0))
  change (∑ uv : ↥(wordFinset (language X) m) × ↥(wordFinset (language X) n),
    f (uv.1.val ++ uv.2.val)) = ∑ w ∈ wordFinset (language X) (m + n), f w
  rw [Fintype.sum_prod_type]
  trans ∑ u ∈ wordFinset (language X) m, ∑ v ∈ wordFinset (language X) n, f (u ++ v)
  · trans ∑ u ∈ wordFinset (language X) m,
        ∑ v : ↥(wordFinset (language X) n), f (u ++ v.val)
    · exact Finset.sum_coe_sort (wordFinset (language X) m)
        (fun u : Word A => ∑ v : ↥(wordFinset (language X) n), f (u ++ v.val))
    · apply Finset.sum_congr rfl
      intro u hu
      exact Finset.sum_coe_sort (wordFinset (language X) n) (fun v : Word A => f (u ++ v))
  rw [← Finset.sum_product (wordFinset (language X) m) (wordFinset (language X) n)
    (fun uv : Word A × Word A => f (uv.1 ++ uv.2))]
  refine Finset.sum_bij_ne_zero (fun uv _ _ => uv.1 ++ uv.2) ?_ ?_ ?_ ?_
  · intro uv huv hweight
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
    apply mem_wordFinset.mpr
    refine ⟨?_, by simp only [List.length_append, (mem_wordFinset.mp hu).2,
      (mem_wordFinset.mp hv).2]⟩
    by_contra hnot
    change -(μ : Measure X.carrier).real (cylinder X (uv.1 ++ uv.2) 0) *
      Real.log ((μ : Measure X.carrier).real (cylinder X (uv.1 ++ uv.2) 0)) ≠ 0 at hweight
    rw [cylinder_eq_empty_of_not_mem_language X hnot, measureReal_empty, neg_zero,
      zero_mul] at hweight
    exact hweight rfl
  · intro uv huv hweight u'v' hu'v' hweight' happend
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
    obtain ⟨hu', hv'⟩ := Finset.mem_product.mp hu'v'
    obtain ⟨hfirst, hsecond⟩ := List.append_inj happend
      ((mem_wordFinset.mp hu).2.trans (mem_wordFinset.mp hu').2.symm)
    exact Prod.ext hfirst hsecond
  · intro w hw hweight
    obtain ⟨hwL, hwlen⟩ := mem_wordFinset.mp hw
    have hu : w.take m ∈ wordFinset (language X) m := mem_wordFinset.mpr
      ⟨language_factorial X (List.take_prefix m w).isInfix hwL,
        by simp only [List.length_take, hwlen]; omega⟩
    have hv : w.drop m ∈ wordFinset (language X) n := mem_wordFinset.mpr
      ⟨language_factorial X (List.drop_suffix m w).isInfix hwL,
        by simp only [List.length_drop, hwlen]; omega⟩
    refine ⟨(w.take m, w.drop m), Finset.mem_product.mpr ⟨hu, hv⟩, ?_,
      List.take_append_drop m w⟩
    simpa only [List.take_append_drop] using hweight
  · intro uv huv hweight
    rfl
theorem blockEntropy_subadditive {μ : ProbabilityMeasure X.carrier} (hInv : IsInvariant μ) :
    Subadditive (blockEntropy μ) := by
  intro m n
  have h := FiniteEntropy.shannon_joint_le
    (p := jointBlockDistribution μ m n) (fun _ => measureReal_nonneg)
    (jointBlockDistribution_sum μ m n)
  simp only [jointBlockDistribution_row, jointBlockDistribution_col hInv,
    shannon_jointBlockDistribution, ← blockEntropy_eq_shannon] at h
  exact h
def measureEntropy (μ : ProbabilityMeasure X.carrier) (hInv : IsInvariant μ) : ℝ :=
  (blockEntropy_subadditive hInv).lim
end BalanceSpecification


