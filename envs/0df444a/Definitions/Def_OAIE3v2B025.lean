-- Prove2me | Definitions.Def_OAIE3v2B025
-- name    : OAIE3v2B025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:59:15.356839+00:00
-- url     : https://prove2.me/theorems/3331ffef-f03f-49ff-8551-a235195f06a9
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 26 of 311
-- statement:
--   Definitions bundle 26 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Estimates/BinaryTupleSorting.lean`, `Estimates/CoefficientTensorApproximation.lean`, `Estimates/CommonCoefficientFourAnnihilators.lean`, `Estimates/ComplexFiniteMeans.lean`, `Estimates/ComplexPolarization.lean`, `Estimates/CorrelationDerivative.lean`, `Estimates/CubicPairPartitionPrecision.lean`, `Estimates/CyclicCutNeighborhood.lean`, `Estimates/CyclicMixedReflection.lean`, `Estimates/DiagonalRowTransfer.lean`, `Estimates/DiagonalWrapComparison.lean`, `Estimates/FiniteConvolution.lean`, `Estimates/FiniteGraphEnergy.lean`, `Estimates/FiniteTupleFibers.lean`, `Estimates/LieTreeMultidegree.lean`, `Estimates/MixedFrozenMiddleRows.lean`, `Estimates/MixedPermutationTensor.lean`, `Estimates/MixedRootLosses.lean`, `Estimates/MultilinearFirstOrder.lean`, `Estimates/NativeBinaryAssignments.lean`, `Estimates/NativeGraphSmallDifference.lean`, `Estimates/NativeMeanRowCorrelation.lean`, `Estimates/NativeRoundedGraphEnergy.lean`, `Estimates/PetalComparisonTree.lean`, `Estimates/PositiveCyclicCorrelation.lean`, `Estimates/PrescribedInvariantUnit.lean`, `Estimates/QuarticRootExchange.lean`, `Estimates/QuotientSubspaceFunctional.lean`, `Estimates/SharedFreeComparisonLift.lean`, `Estimates/UnitVerticalCyclicDifference.lean`, `Estimates/UnitVerticalMeanRowCorrelation.lean`, `Fourier/NativeMixedFourierProfiles.lean`, `Geometry/BinaryWordSupports.lean`, `Geometry/BoxBlockBudget.lean`, `Geometry/BoxCornerMean.lean`, `Geometry/BoxDifferenceHom.lean`, `Geometry/FiniteSumCoordinate.lean`, `Geometry/MissingCoordinateDownsets.lean`, `Lattices/FourAffineRefinement.lean`, `Lattices/ProperAffineBoxRestriction.lean`, `Linear/FourBalancedDual.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BinaryTupleSorting
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem binary_eq_zero_of_ne_one (b : Fin 2) (h : b ≠ 1) : b = 0 := by
  apply Fin.ext
  have hb := b.isLt
  have hn : b.val ≠ 1 := fun heq => h (Fin.ext heq)
  change b.val = 0
  omega

theorem binary_eq_one_of_ne_zero (b : Fin 2) (h : b ≠ 0) : b = 1 := by
  apply Fin.ext
  have hb := b.isLt
  have hn : b.val ≠ 0 := fun heq => h (Fin.ext heq)
  change b.val = 1
  omega

def binaryZeroCount {n : ℕ} (f : Fin n → Fin 2) : ℕ :=
  Fintype.card {i : Fin n // f i = 0}

def binarySorted {n : ℕ} (f : Fin n → Fin 2) : Fin n → Fin 2 := f ∘ Tuple.sort f

theorem binaryZeroCount_comp {n : ℕ} (f : Fin n → Fin 2) (e : Equiv.Perm (Fin n)) :
    binaryZeroCount (f ∘ e) = binaryZeroCount f := by
  exact Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))

theorem binarySorted_comp {n : ℕ} (f : Fin n → Fin 2) (e : Equiv.Perm (Fin n)) :
    binarySorted (f ∘ e) = binarySorted f :=
  Tuple.comp_perm_comp_sort_eq_comp_sort

theorem binarySorted_threshold {n : ℕ} (f : Fin n → Fin 2) (k : Fin n) :
    binarySorted f k = if k.val < binaryZeroCount f then 0 else 1 := by
  have hle (a : Fin 2) : a ≤ 0 ↔ a = 0 :=
    ⟨fun h => le_antisymm h (Fin.zero_le _), fun h => h ▸ le_rfl⟩
  have hiff : k.val < binaryZeroCount (binarySorted f) ↔ binarySorted f k = 0 := by
    have H := Tuple.lt_card_le_iff_apply_le_of_monotone
      (f := binarySorted f) (j := k) (a := (0 : Fin 2)) (Tuple.monotone_sort f)
    unfold binaryZeroCount
    rw [Fintype.card_subtype]
    have hfilter : (Finset.univ.filter (fun i : Fin n => binarySorted f i = 0)) =
        Finset.univ.filter (fun i : Fin n => binarySorted f i ≤ 0) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hle]
    rw [hfilter]
    exact H.trans (hle _)
  have hcount : binaryZeroCount (binarySorted f) = binaryZeroCount f :=
    binaryZeroCount_comp f (Tuple.sort f)
  rw [hcount] at hiff
  split_ifs with hk
  · exact hiff.mp hk
  · exact binary_eq_one_of_ne_zero _ (fun h => hk (hiff.mpr h))

def zeroFixedPermutation {n : ℕ} (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) where
  toFun := Fin.cases 0 (fun j => (e j).succ)
  invFun := Fin.cases 0 (fun j => (e.symm j).succ)
  left_inv j := by
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · simp only [Fin.cases_succ, Equiv.symm_apply_apply]
  right_inv j := by
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · simp only [Fin.cases_succ, Equiv.apply_symm_apply]

theorem binarySorted_tail {n : ℕ} (f : Fin (n + 1) → Fin 2) (h0 : f 0 = 0) :
    binarySorted f = f ∘ zeroFixedPermutation (Tuple.sort (fun j => f j.succ)) := by
  have hm : Monotone (f ∘ zeroFixedPermutation (Tuple.sort (fun j => f j.succ))) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j _
      change f 0 ≤ _
      rw [h0]
      exact Fin.zero_le _
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro hij
        have hi : ¬ i.succ ≤ (0 : Fin (n + 1)) := by
          intro h
          simp only [Fin.le_def, Fin.val_succ, Fin.val_zero] at h
          omega
        exact (hi hij).elim
      · intro hij
        exact (Tuple.monotone_sort (fun j : Fin n => f j.succ))
          (by simpa only [Fin.succ_le_succ_iff] using hij)
  exact Tuple.unique_monotone (Tuple.monotone_sort f) hm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexFiniteMeans
namespace OAI

section

open scoped BigOperators

namespace Erdos3

theorem expect_fin_cons {G M : Type*} [Fintype G] [AddCommMonoid M] [Module ℚ≥0 M]
    {n : ℕ} (F : (Fin (n + 1) → G) → M) :
    (𝔼 x, F x) = 𝔼 a : G, 𝔼 y : Fin n → G, F (Fin.cons a y) := by
  calc
    (𝔼 x, F x) = 𝔼 p : G × (Fin n → G), F (Fin.cons p.1 p.2) := by
      apply Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (n + 1) ↦ G)).symm
      intro x
      congr 1
      simp
    _ = _ := by
      simpa using (Finset.expect_product' (Finset.univ : Finset G)
        (Finset.univ : Finset (Fin n → G)) (fun a y ↦ F (Fin.cons a y)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorrelationDerivative
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem expect_translate (f : H → ℂ) (x : H) : (𝔼 h, f (x + h)) = 𝔼 h, f h := by
  exact Fintype.expect_equiv (Equiv.addLeft x) _ f (fun _ ↦ rfl)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxBlockBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem expect_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
    [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)] (i : ι) (f : X i → ℝ) :
    (𝔼 x : (∀ j, X j), f (x i)) = 𝔼 a, f a := by
  have h := Fintype.expect_equiv (Equiv.piSplitAt i X)
    (fun x => f (x i)) (fun x => f x.1) (fun _ => rfl)
  rw [h]
  simpa using Finset.expect_product' (Finset.univ : Finset (X i))
    (Finset.univ : Finset (∀ j : {j // j ≠ i}, X j)) (fun a _ => f a)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def coordinateExceptional {ι X : Type*} [Fintype ι] [Fintype X]
    (B : Finset X) : Finset (ι → X) := by
  classical
  exact Finset.univ.filter (fun x => ∃ i, x i ∈ B)

theorem not_mem_coordinateExceptional {ι X : Type*} [Fintype ι] [Fintype X]
    (B : Finset X) (x : ι → X) : x ∉ coordinateExceptional B ↔ ∀ i, x i ∉ B := by
  classical
  simp [coordinateExceptional]

theorem coordinateExceptional_density_le {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype X] [Nonempty X] (B : Finset X) :
    ((coordinateExceptional (ι := ι) B).card : ℝ) / Fintype.card (ι → X) ≤
      (Fintype.card ι : ℝ) * (B.card : ℝ) / Fintype.card X := by
  classical
  have hpoint (x : ι → X) : (if ∃ i, x i ∈ B then (1 : ℝ) else 0) ≤
      ∑ i, if x i ∈ B then (1 : ℝ) else 0 := by
    by_cases h : ∃ i, x i ∈ B
    · obtain ⟨i, hi⟩ := h
      rw [if_pos ⟨i, hi⟩]
      calc
        (1 : ℝ) = if x i ∈ B then 1 else 0 := by rw [if_pos hi]
        _ ≤ _ := Finset.single_le_sum
          (f := fun j : ι => if x j ∈ B then (1 : ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
    · rw [if_neg h]
      exact Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)
  calc
    _ = 𝔼 x : ι → X, if ∃ i, x i ∈ B then (1 : ℝ) else 0 := by
      simp [coordinateExceptional, Fintype.expect_eq_sum_div_card]
      congr 1
      ext x
      simp
    _ ≤ 𝔼 x : ι → X, ∑ i, if x i ∈ B then (1 : ℝ) else 0 :=
      Finset.expect_le_expect (fun x _ => hpoint x)
    _ = ∑ i, 𝔼 x : ι → X, if x i ∈ B then (1 : ℝ) else 0 := Finset.expect_sum_comm _ _ _
    _ = ∑ _i : ι, (B.card : ℝ) / Fintype.card X := by
      congr 1
      funext i
      rw [expect_coordinate (X := fun _ : ι => X) i (fun x : X => if x ∈ B then (1 : ℝ) else 0)]
      simp [Fintype.expect_eq_sum_div_card, Finset.sum_ite_mem]
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteConvolution
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

noncomputable def finiteConvolution (f g : H → ℂ) (x : H) : ℂ :=
  𝔼 y, f y * g (x - y)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicCutNeighborhood
namespace OAI

section

namespace Erdos3

theorem exists_smoothing_scale {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ K : ℕ, 0 < K ∧ K ≤ N ∧ ((K - 1 : ℕ) : ℝ) ≤ δ * N ∧
      (N : ℝ) / K ≤ 2 / δ := by
  let K := max 1 ⌊δ * N⌋₊
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hfloor : (⌊δ * N⌋₊ : ℝ) ≤ δ * N := Nat.floor_le (by positivity)
  have hfloorN : ⌊δ * N⌋₊ ≤ N := by
    exact_mod_cast hfloor.trans (by nlinarith : δ * N ≤ (N : ℝ))
  have hk : 1 ≤ K := le_max_left _ _
  have hkfloor : ⌊δ * N⌋₊ ≤ K := le_max_right _ _
  have hk1 : (1 : ℝ) ≤ K := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < K := by linarith
  have hfK : (⌊δ * N⌋₊ : ℝ) ≤ K := by exact_mod_cast hkfloor
  have hlt : δ * N < (⌊δ * N⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨K, by omega, max_le (by omega) hfloorN, ?_, ?_⟩
  · have hh : K - 1 ≤ ⌊δ * N⌋₊ := by dsimp [K]; omega
    exact (Nat.cast_le.mpr hh).trans hfloor
  · apply (div_le_div_iff₀ hkpos hδ).mpr
    nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxDifferenceHom
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def boxAnchorFactor {X : Type*} (K : X → X → ℂ)
    (a z : Fin 2 → X) : ℂ :=
  star (K (a 0) (z 1)) * star (K (z 0) (a 1)) * K (a 0) (a 1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxCornerMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_true_of_ne_false {n : ℕ} {ω : Fin n → Bool}
    (h : ω ≠ fun _ => false) : ∃ k, ω k = true := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp h
  refine ⟨k, ?_⟩
  cases he : ω k <;> simp_all

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MultilinearFirstOrder
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {R I L E : Type*} [CommRing R] [Fintype I] [DecidableEq I]
  [AddCommGroup L] [Module R L] [AddCommGroup E] [Module R E]

theorem multilinear_eq_first_order_of_two_vanish
    (f : MultilinearMap R (fun _ : I => L) E) (C D : I → Submodule R L)
    (hDC : ∀ i, D i ≤ C i)
    (hvanish : ∀ v : I → L, (∀ i, v i ∈ C i) → ∀ i j, i ≠ j →
      v i ∈ D i → v j ∈ D j → f v = 0)
    (x y : I → L) (hx : ∀ i, x i ∈ C i) (hy : ∀ i, y i ∈ D i) :
    f (x + y) = f x + f.linearDeriv x y := by
  classical
  rw [f.map_add_eq_map_add_linearDeriv_add]
  have hsum : (∑ s : Finset I with 2 ≤ s.card, f (s.piecewise y x)) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    have hs' : 1 < s.card := (Finset.mem_filter.mp hs).2
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hs'
    refine hvanish _ ?_ i j hij ?_ ?_
    · intro k
      by_cases hk : k ∈ s
      · simpa only [s.piecewise_eq_of_mem _ _ hk] using hDC k (hy k)
      · simpa only [s.piecewise_eq_of_notMem _ _ hk] using hx k
    · simpa only [s.piecewise_eq_of_mem _ _ hi] using hy i
    · simpa only [s.piecewise_eq_of_mem _ _ hj] using hy j
  rw [hsum, add_zero]

theorem exists_linear_expansion_of_two_vanish
    (f : MultilinearMap R (fun _ : I => L) E) (C D : I → Submodule R L)
    (hDC : ∀ i, D i ≤ C i)
    (hvanish : ∀ v : I → L, (∀ i, v i ∈ C i) → ∀ i j, i ≠ j →
      v i ∈ D i → v j ∈ D j → f v = 0)
    (x : I → L) (hx : ∀ i, x i ∈ C i) :
    ∃ A : (∀ i, D i) →ₗ[R] E, ∀ y : ∀ i, D i,
      f (fun i => x i + (y i : L)) = f x + A y := by
  classical
  let inclusion : (∀ i, D i) →ₗ[R] (I → L) :=
    LinearMap.pi (fun i => (D i).subtype.comp (LinearMap.proj i))
  refine ⟨(f.linearDeriv x).comp inclusion, ?_⟩
  intro y
  exact multilinear_eq_first_order_of_two_vanish f C D hDC hvanish x
    (fun i => y i) hx (fun i => (y i).property)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LieTreeMultidegree
namespace OAI

section

namespace Erdos3

variable {R I J L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

noncomputable def bracketMultilinear
    (f : MultilinearMap R (fun _ : I => L) L)
    (g : MultilinearMap R (fun _ : J => L) L) :
    MultilinearMap R (fun _ : I ⊕ J => L) L :=
  MultilinearMap.uncurrySum
    { toFun := fun m =>
        ({ toFun := fun y => ⁅f m, y⁆
           map_add' := fun y z => lie_add (f m) y z
           map_smul' := fun c y => lie_smul c (f m) y } : L →ₗ[R] L).compMultilinearMap g
      map_update_add' m i x y := by
        ext v
        change ⁅f (Function.update m i (x + y)), g v⁆ =
          ⁅f (Function.update m i x), g v⁆ + ⁅f (Function.update m i y), g v⁆
        rw [f.map_update_add, add_lie]
      map_update_smul' m i c x := by
        ext v
        change ⁅f (Function.update m i (c • x)), g v⁆ = c • ⁅f (Function.update m i x), g v⁆
        rw [f.map_update_smul, smul_lie] }

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientTensorApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_prod_sub_prod_le_sum_error {I : Type*} (S : Finset I) (f g : I → ℂ)
    {B : ℝ} (hB : 1 ≤ B) (hf : ∀ i ∈ S, ‖f i‖ ≤ B) (hg : ∀ i ∈ S, ‖g i‖ ≤ B) :
    ‖(∏ i ∈ S, f i) - ∏ i ∈ S, g i‖ ≤ B ^ S.card * ∑ i ∈ S, ‖f i - g i‖ := by
  classical
  revert hf hg
  induction S using Finset.induction_on with
  | empty => intro _ _; simp
  | @insert i S hi ih =>
    intro hf hg
    have hrec := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hg j (Finset.mem_insert_of_mem hj))
    have hprod : ‖∏ j ∈ S, g j‖ ≤ B ^ S.card := by
      rw [norm_prod]
      calc
        _ ≤ ∏ _j ∈ S, B := Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          (fun j hj => hg j (Finset.mem_insert_of_mem hj))
        _ = _ := by simp
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi,
      Finset.sum_insert hi]
    calc
      _ = ‖f i * ((∏ j ∈ S, f j) - ∏ j ∈ S, g j) +
          (f i - g i) * ∏ j ∈ S, g j‖ := by congr 1; ring
      _ ≤ ‖f i‖ * ‖(∏ j ∈ S, f j) - ∏ j ∈ S, g j‖ +
          ‖f i - g i‖ * ‖∏ j ∈ S, g j‖ := by
        simpa only [norm_mul] using norm_add_le
          (f i * ((∏ j ∈ S, f j) - ∏ j ∈ S, g j)) ((f i - g i) * ∏ j ∈ S, g j)
      _ ≤ B * (B ^ S.card * ∑ j ∈ S, ‖f j - g j‖) + ‖f i - g i‖ * B ^ S.card :=
        add_le_add (mul_le_mul (hf i (Finset.mem_insert_self _ _)) hrec
          (norm_nonneg _) (zero_le_one.trans hB))
          (mul_le_mul_of_nonneg_left hprod (norm_nonneg _))
      _ = B ^ (S.card + 1) * (∑ j ∈ S, ‖f j - g j‖) + ‖f i - g i‖ * B ^ S.card := by
        rw [pow_succ]
        ring
      _ ≤ B ^ (S.card + 1) * (∑ j ∈ S, ‖f j - g j‖) + ‖f i - g i‖ * B ^ (S.card + 1) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hB (Nat.le_succ _)) (norm_nonneg _))
      _ = _ := by ring

theorem mean_prod_error_le {I X : Type*} [Fintype I] [Fintype X]
    (f g : I → X → ℂ) {B ε : ℝ} (hB : 1 ≤ B)
    (hf : ∀ i x, ‖f i x‖ ≤ B) (hg : ∀ i x, ‖g i x‖ ≤ B)
    (herr : ∀ i, (𝔼 x, ‖f i x - g i x‖) ≤ ε) :
    (𝔼 x, ‖(∏ i, f i x) - ∏ i, g i x‖) ≤ B ^ Fintype.card I * ((Fintype.card I : ℝ) * ε) := by
  calc
    _ ≤ 𝔼 x, B ^ Fintype.card I * ∑ i, ‖f i x - g i x‖ :=
      Finset.expect_le_expect (fun x _ => by
        simpa only [Finset.card_univ] using norm_prod_sub_prod_le_sum_error Finset.univ
          (fun i => f i x) (fun i => g i x) hB (fun i _ => hf i x) (fun i _ => hg i x))
    _ = B ^ Fintype.card I * ∑ i, 𝔼 x, ‖f i x - g i x‖ := by
      rw [← Finset.mul_expect, Finset.expect_sum_comm]
    _ ≤ B ^ Fintype.card I * ∑ _ : I, ε :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => herr i))
        (pow_nonneg (zero_le_one.trans hB) _)
    _ = _ := by simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FourBalancedDual
namespace OAI

section

namespace Erdos3

variable {R V E : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup E] [Module R E]

def fourDiagonalMap : V →ₗ[R] (Fin 4 → V) := LinearMap.pi (fun _ => LinearMap.id)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PetalComparisonTree
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem realification_sup (P Q : Submodule ℚ V) :
    (P ⊔ Q).baseChange ℝ = P.baseChange ℝ ⊔ Q.baseChange ℝ := by
  apply le_antisymm
  · rw [Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    change (1 : ℝ) ⊗ₜ[ℚ] (a + b) ∈ _
    rw [TensorProduct.tmul_add]
    exact Submodule.add_mem_sup (Submodule.tmul_mem_baseChange_of_mem _ ha)
      (Submodule.tmul_mem_baseChange_of_mem _ hb)
  · exact sup_le (Submodule.baseChange_mono ℝ le_sup_left)
      (Submodule.baseChange_mono ℝ le_sup_right)

theorem real_four_projection (x : ℝ ⊗[ℚ] (Fin 4 → V)) (k : Fin 4) :
    (LinearMap.proj k).baseChange ℝ x =
      (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)) x k := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem real_pair_projection (x : ℝ ⊗[ℚ] (Fin 2 → V)) (k : Fin 2) :
    (LinearMap.proj k).baseChange ℝ x =
      (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 2 => V)) x k := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuotientSubspaceFunctional
namespace OAI

section

namespace Erdos3

theorem exists_quotient_functional_preserving_subspace
    {K V A : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup A] [Module K A]
    (U I : Submodule K V) (η : V →ₗ[K] A) (hη : U ⊓ I ≤ η.ker) :
    ∃ ξ : (V ⧸ I) →ₗ[K] A, ∀ x ∈ U, ξ (I.mkQ x) = η x := by
  let q : U →ₗ[K] V ⧸ I := I.mkQ.comp U.subtype
  let f : U →ₗ[K] A := η.comp U.subtype
  have hk : q.ker ≤ f.ker := by
    intro x hx
    have hxI : x.val ∈ I := (Submodule.Quotient.mk_eq_zero I).mp hx
    exact hη ⟨x.property, hxI⟩
  let fbar := q.ker.liftQ f hk
  let φ : q.range →ₗ[K] A := fbar.comp q.quotKerEquivRange.symm.toLinearMap
  obtain ⟨ξ, hξ⟩ := φ.exists_extend
  refine ⟨ξ, ?_⟩
  intro x hx
  let u : U := ⟨x, hx⟩
  have he := LinearMap.congr_fun hξ (q.rangeRestrict u)
  change ξ (q u) = fbar (q.quotKerEquivRange.symm (q.rangeRestrict u)) at he
  have hq : q.quotKerEquivRange.symm (q.rangeRestrict u) = q.ker.mkQ u :=
    q.quotKerEquivRange_symm_apply_image u _
  rw [hq] at he
  exact he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveCyclicCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def cubeRepresentativeSum {d N : ℕ} (k : Fin d → ZMod N) (ω : Fin d → Bool) : ℕ :=
  ∑ i, if ω i then (k i).val else 0

theorem cubeRepresentativeSum_le {d N : ℕ} [NeZero N]
    (k : Fin d → ZMod N) (ω : Fin d → Bool) : cubeRepresentativeSum k ω ≤ d * N := by
  calc
    _ ≤ ∑ _i : Fin d, N := Finset.sum_le_sum (fun i _ => by
      split_ifs <;> [exact (k i).val_lt.le; exact Nat.zero_le _])
    _ = _ := by simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrescribedInvariantUnit
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem sqrt_complement_lipschitz {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hrhalf : r ≤ 1 / 2) (hthalf : t ≤ 1 / 2) :
    |Real.sqrt (1 - r ^ 2) - Real.sqrt (1 - t ^ 2)| ≤ |r - t| := by
  let a := Real.sqrt (1 - r ^ 2)
  let b := Real.sqrt (1 - t ^ 2)
  have hrq : 0 ≤ 1 - r ^ 2 := by nlinarith
  have htq : 0 ≤ 1 - t ^ 2 := by nlinarith
  have ha : 1 / 2 ≤ a := Real.le_sqrt_of_sq_le (by nlinarith)
  have hb : 1 / 2 ≤ b := Real.le_sqrt_of_sq_le (by nlinarith)
  have ha2 : a ^ 2 = 1 - r ^ 2 := Real.sq_sqrt hrq
  have hb2 : b ^ 2 = 1 - t ^ 2 := Real.sq_sqrt htq
  have heq : |a - b| * (a + b) = |r - t| * (r + t) := by
    calc
      _ = |(a - b) * (a + b)| := by rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ a + b)]
      _ = |(t - r) * (r + t)| := congrArg abs (by nlinarith)
      _ = _ := by rw [abs_mul, abs_sub_comm t r, abs_of_nonneg (by linarith : 0 ≤ r + t)]
  calc
    _ ≤ |a - b| * (a + b) := le_mul_of_one_le_right (abs_nonneg _) (by linarith)
    _ = |r - t| * (r + t) := heq
    _ ≤ _ := mul_le_of_le_one_right (abs_nonneg _) (by linarith)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteSumCoordinate
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} [DecidableEq σ] {n : ℕ}

def finiteSumCoordinateInput (i : σ) (x : (σ ⊕ Fin n) → ℤ) : σ → ℤ :=
  Function.update (fun j => x (Sum.inl j)) i (∑ a : Fin n, x (Sum.inr a))

def finiteTermCoordinateInput (i : σ) (a : Fin n) (x : (σ ⊕ Fin n) → ℤ) : σ → ℤ :=
  Function.update (fun j => x (Sum.inl j)) i (x (Sum.inr a))

def finiteTermCoordinateHom (i : σ) (a : Fin n) (j : σ) : (((σ ⊕ Fin n) → ℤ) →+ ℤ) where
  toFun x := finiteTermCoordinateInput i a x j
  map_zero' := by simp [finiteTermCoordinateInput]
  map_add' x y := by
    simp only [finiteTermCoordinateInput, Function.update_apply, Pi.add_apply]
    split_ifs <;> rfl

theorem finiteSumCoordinateInput_one (i : σ) (x : (σ ⊕ Fin 1) → ℤ) :
    finiteSumCoordinateInput i x = finiteTermCoordinateInput i 0 x := by
  simp only [finiteSumCoordinateInput, finiteTermCoordinateInput, Fin.sum_univ_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeBinaryAssignments
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ I : Type*} [DecidableEq σ] {n : ℕ}

def finiteChoiceCoordinateInput (l : List σ) (x : (Fin (n + 1) × σ) → ℤ) (j : σ) : ℤ :=
  if j ∈ l then ∑ a : Fin (n + 1), x (a, j) else x (0, j)

def finiteChoiceCoordinateHom (l : List σ) (j : σ) : (((Fin (n + 1) × σ) → ℤ) →+ ℤ) where
  toFun x := finiteChoiceCoordinateInput l x j
  map_zero' := by simp [finiteChoiceCoordinateInput]
  map_add' x y := by
    simp only [finiteChoiceCoordinateInput, Pi.add_apply, Finset.sum_add_distrib]
    split_ifs <;> rfl

def finiteChoiceReplaceIndex (i : σ) (a : Fin (n + 1)) (j : Fin (n + 1) × σ) : Fin (n + 1) × σ :=
  if j = (0, i) then (a, i) else j

def finiteChoiceReplaceInput (i : σ) (a : Fin (n + 1))
    (x : (Fin (n + 1) × σ) → ℤ) : (Fin (n + 1) × σ) → ℤ :=
  fun j => x (finiteChoiceReplaceIndex i a j)

theorem finiteChoiceCoordinateInput_replace (l : List σ) (i : σ) (hi : i ∉ l)
    (a : Fin (n + 1)) (x : (Fin (n + 1) × σ) → ℤ) :
    finiteChoiceCoordinateInput l (finiteChoiceReplaceInput i a x) =
      Function.update (finiteChoiceCoordinateInput l x) i (x (a, i)) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [finiteChoiceCoordinateInput, finiteChoiceReplaceInput, finiteChoiceReplaceIndex, hi]
  · simp [finiteChoiceCoordinateInput, finiteChoiceReplaceInput, finiteChoiceReplaceIndex, hj]

theorem finiteChoiceCoordinateInput_cons (l : List σ) (i : σ)
    (x : (Fin (n + 1) × σ) → ℤ) :
    finiteChoiceCoordinateInput (i :: l) x = Function.update (finiteChoiceCoordinateInput l x) i
      (∑ a : Fin (n + 1), x (a, i)) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [finiteChoiceCoordinateInput]
  · simp [finiteChoiceCoordinateInput, hj]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MissingCoordinateDownsets
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def missingCoordinateBound (s : ℕ) (i j : Fin (s + 1)) : ℕ :=
  if j = i then 0 else s

def missingCoordinateDownset (s : ℕ) (i : Fin (s + 1)) : Set (Fin (s + 1) →₀ ℕ) :=
  {a | ∀ j, a j ≤ missingCoordinateBound s i j}

theorem missingCoordinateBound_le (s : ℕ) (i : Fin (s + 1)) :
    missingCoordinateBound s i ≤ fun _ => s := by
  intro j
  by_cases h : j = i <;> simp [missingCoordinateBound, h]

theorem missingCoordinateDownset_lower (s : ℕ) (i : Fin (s + 1)) :
    IsLowerSet (missingCoordinateDownset s i) :=
  fun _ _ hab hb j => (hab j).trans (hb j)

theorem missingCoordinateDownset_covers (s : ℕ) (a : Fin (s + 1) →₀ ℕ)
    (ha : (∑ j, a j) ≤ s) : ∃ i, a ∈ missingCoordinateDownset s i := by
  classical
  have hall (j : Fin (s + 1)) : a j ≤ s :=
    (Finset.single_le_sum (fun k _ => Nat.zero_le (a k)) (Finset.mem_univ j)).trans ha
  have hz : ∃ i, a i = 0 := by
    by_contra hn
    push Not at hn
    have hsum : s + 1 ≤ ∑ i, a i := by
      calc
        _ = ∑ _i : Fin (s + 1), 1 := by simp
        _ ≤ _ := Finset.sum_le_sum fun i _ => Nat.one_le_iff_ne_zero.mpr (hn i)
    omega
  obtain ⟨i, hi⟩ := hz
  refine ⟨i, fun j => ?_⟩
  by_cases hji : j = i
  · subst j
    simp [missingCoordinateBound, hi]
  · simpa [missingCoordinateBound, hji] using hall j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMeanRowCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

theorem exists_large_nonnegative_weighted_term {I : Type*} [Fintype I]
    (w z : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hz : ∀ i, 0 ≤ z i)
    {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 < M)
    (hcost : ∑ i, w i ≤ M) (hmass : ρ ≤ ∑ i, w i * z i) :
    ∃ i, ρ / M ≤ z i := by
  classical
  have hI : (Finset.univ : Finset I).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hmass
    linarith
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ z hI
  refine ⟨i, (div_le_iff₀ hM).mpr ?_⟩
  calc
    ρ ≤ ∑ j, w j * z j := hmass
    _ ≤ ∑ j, w j * z i := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hi j (Finset.mem_univ j)) (hw j))
    _ = (∑ j, w j) * z i := (Finset.sum_mul _ _ _).symm
    _ ≤ M * z i := mul_le_mul_of_nonneg_right hcost (hz i)
    _ = z i * M := mul_comm _ _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mean_row_correlation_scale {H X : Type*} [Fintype H] [Fintype X]
    (f g : H → X → ℂ) {a : ℝ} (ha : 0 ≤ a) :
    (𝔼 h, ‖𝔼 x, f h x * star ((a : ℂ) * g h x)‖) =
      a * (𝔼 h, ‖𝔼 x, f h x * star (g h x)‖) := by
  have heq (h : H) : (𝔼 x, f h x * star ((a : ℂ) * g h x)) =
      (a : ℂ) * (𝔼 x, f h x * star (g h x)) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  simp only [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha,
    ← Finset.mul_expect]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalMeanRowCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def cyclicDivision (d : ℕ) {N : ℕ} (x : ZMod N) : ZMod N := (x.val / d : ℕ)

theorem cyclicDivision_val (d : ℕ) {N : ℕ} [NeZero N] (x : ZMod N) :
    (cyclicDivision d x).val = x.val / d :=
  ZMod.val_natCast_of_lt ((Nat.div_le_self _ _).trans_lt x.val_lt)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def cyclicHalf {N : ℕ} (x : ZMod N) : ZMod N := (x.val / 2 : ℕ)

theorem cyclicHalf_val {N : ℕ} [NeZero N] (x : ZMod N) :
    (cyclicHalf x).val = x.val / 2 := by
  exact ZMod.val_natCast_of_lt ((Nat.div_le_self _ _).trans_lt x.val_lt)

theorem cyclicHalf_with_parity_injective {N : ℕ} [NeZero N] :
    Function.Injective (fun x : ZMod N => (cyclicHalf x, (x.val : ZMod 2))) := by
  intro x y h
  have hq := congrArg (fun z : ZMod N × ZMod 2 => z.1.val) h
  have hr := congrArg (fun z : ZMod N × ZMod 2 => z.2.val) h
  simp only [cyclicHalf_val] at hq
  simp only [ZMod.val_natCast] at hr
  apply ZMod.val_injective
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexPolarization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def polarizationPhase : Fin 4 → ℂ := ![1, -1, Complex.I, -Complex.I]

noncomputable def polarizationWeight (k : Fin 4) : ℂ := polarizationPhase k / 4

theorem polarizationPhase_norm (k : Fin 4) : ‖polarizationPhase k‖ = 1 := by
  fin_cases k <;> norm_num [polarizationPhase]

theorem polarizationWeight_norm (k : Fin 4) : ‖polarizationWeight k‖ = (1 : ℝ) / 4 := by
  simp only [polarizationWeight, norm_div, polarizationPhase_norm]
  norm_num

theorem polarizationWeight_cost : (∑ k, ‖polarizationWeight k‖) = 1 := by
  simp only [polarizationWeight_norm, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num

theorem complex_mixed_polarization (a b c d : ℂ) :
    a * star d = ∑ k, polarizationWeight k *
      ((a + polarizationPhase k * b) * star (c + polarizationPhase k * d)) := by
  norm_num [Fin.sum_univ_succ, polarizationWeight, polarizationPhase,
    star_add, star_mul, Complex.star_def]
  ring_nf
  norm_num [Complex.I_sq]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FourAffineRefinement
namespace OAI

section

namespace Erdos3

variable {R I E : Type*} {V : I → Type*} [CommRing R]
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
  [AddCommGroup E] [Module R E]

def fourFunctionDifference (f : (∀ i, V i) → E) (v : ∀ i, Fin 4 → V i) : E :=
  f (fun i => v i 0) + f (fun i => v i 1) - f (fun i => v i 2) - f (fun i => v i 3)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonCoefficientFourAnnihilators
namespace OAI

section

namespace Erdos3

open Module

variable {V μ : Type*} [AddCommGroup V] [Module ℚ V] [Fintype μ]

theorem four_submodule_finrank_le (e : Basis μ ℚ V)
    (U : Submodule ℚ (Fin 4 → V)) : finrank ℚ U ≤ 4 * Fintype.card μ := by
  let e4 := Pi.basis (fun _ : Fin 4 => e)
  let : FiniteDimensional ℚ (Fin 4 → V) := e4.finiteDimensional_of_finite
  calc
    finrank ℚ U ≤ finrank ℚ (Fin 4 → V) := U.finrank_le
    _ = Fintype.card (Σ _ : Fin 4, μ) := finrank_eq_card_basis e4
    _ = 4 * Fintype.card μ := by simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteTupleFibers
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem assemble_tuple_fibers {G : Type*} (d : ℕ)
    (A : Finset G) (P : A → Finset (Fin d → G)) :
    ∃ Q : Finset (Fin (d + 1) → G), Q.card = ∑ a : A, (P a).card ∧
      ∀ t, t ∈ Q ↔ ∃ a : A, a.val = t 0 ∧ Fin.tail t ∈ P a := by
  classical
  let e : (Σ _ : A, Fin d → G) ↪ (Fin (d + 1) → G) := {
    toFun := fun t => Fin.cons t.1.val t.2
    inj' := by
      rintro ⟨a, u⟩ ⟨b, v⟩ h
      have hab : a = b := Subtype.ext (congrFun h 0)
      have huv : u = v := by funext i; exact congrFun h i.succ
      cases hab
      cases huv
      rfl }
  refine ⟨(Finset.univ.sigma P).map e, ?_, ?_⟩
  · simp only [Finset.card_map, Finset.card_sigma]
  · intro t
    constructor
    · intro ht
      obtain ⟨⟨a, u⟩, hau, heq⟩ := Finset.mem_map.mp ht
      have hu := (Finset.mem_sigma.mp hau).2
      have hut : u = Fin.tail t := by funext i; exact congrFun heq i.succ
      exact ⟨a, congrFun heq 0, hut ▸ hu⟩
    · rintro ⟨a, ha, ht⟩
      apply Finset.mem_map.mpr
      refine ⟨⟨a, Fin.tail t⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, ht⟩, ?_⟩
      funext i
      refine Fin.cases ?_ (fun _ => rfl) i
      exact ha

theorem dense_tuple_fibers {G : Type*} [Fintype G] (d : ℕ)
    (A : Finset G) (P : A → Finset (Fin d → G)) {α β : ℝ}
    (hβ : 0 ≤ β) (hA : α * (Fintype.card G : ℝ) ≤ A.card)
    (hP : ∀ a : A, β * (Fintype.card G : ℝ) ^ d ≤ (P a).card) :
    ∃ Q : Finset (Fin (d + 1) → G),
      α * β * (Fintype.card G : ℝ) ^ (d + 1) ≤ (Q.card : ℝ) ∧
      ∀ t, t ∈ Q ↔ ∃ a : A, a.val = t 0 ∧ Fin.tail t ∈ P a := by
  obtain ⟨Q, hcard, hmem⟩ := assemble_tuple_fibers d A P
  refine ⟨Q, ?_, hmem⟩
  calc
    _ = (α * Fintype.card G) * (β * (Fintype.card G : ℝ) ^ d) := by rw [pow_succ]; ring
    _ ≤ (A.card : ℝ) * (β * (Fintype.card G : ℝ) ^ d) :=
      mul_le_mul_of_nonneg_right hA (mul_nonneg hβ (pow_nonneg (Nat.cast_nonneg _) _))
    _ = ∑ _a : A, β * (Fintype.card G : ℝ) ^ d := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ ∑ a : A, ((P a).card : ℝ) := Finset.sum_le_sum (fun a _ => hP a)
    _ = (Q.card : ℝ) := by rw [hcard, Nat.cast_sum]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DiagonalWrapComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def cyclicCarry {N : ℕ} (h n : ZMod N) : ℝ :=
  if N ≤ h.val + n.val then 1 else 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalCyclicDifference
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem norm_smoothed_branch_error (c w : ℝ) (hw : 0 ≤ w ∧ w ≤ 1)
    (a b u v : ℂ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖((1 - c : ℝ) : ℂ) * a + (c : ℂ) * b -
      (((1 - w : ℝ) : ℂ) * u + (w : ℂ) * v)‖ ≤
      ‖a - u‖ + ‖b - v‖ + 2 * |c - w| := by
  have heq : ((1 - c : ℝ) : ℂ) * a + (c : ℂ) * b -
      (((1 - w : ℝ) : ℂ) * u + (w : ℂ) * v) =
      (((1 - w : ℝ) : ℂ) * (a - u) + (w : ℂ) * (b - v)) +
        ((c - w : ℝ) : ℂ) * (b - a) := by push_cast; ring
  have hba : ‖b - a‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  rw [heq]
  calc
    _ ≤ ‖((1 - w : ℝ) : ℂ) * (a - u)‖ + ‖(w : ℂ) * (b - v)‖ +
        ‖((c - w : ℝ) : ℂ) * (b - a)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = (1 - w) * ‖a - u‖ + w * ‖b - v‖ + |c - w| * ‖b - a‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : 0 ≤ 1 - w), abs_of_nonneg hw.1]
    _ ≤ ‖a - u‖ + ‖b - v‖ + |c - w| * 2 :=
      add_le_add (add_le_add (mul_le_of_le_one_left (norm_nonneg _) (by linarith))
        (mul_le_of_le_one_left (norm_nonneg _) hw.2))
        (mul_le_mul_of_nonneg_left hba (abs_nonneg _))
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def integerSecondDifference (u v : (Fin 2 → ℤ) → ℂ) (k : ℤ)
    (x : Fin 2 → ℤ) : ℂ := u x * star (v ![x 0, x 1 + k])

theorem integerSecondDifference_norm (u v : (Fin 2 → ℤ) → ℂ)
    (hu : ∀ x, ‖u x‖ ≤ 1) (hv : ∀ x, ‖v x‖ ≤ 1) (k : ℤ) (x : Fin 2 → ℤ) :
    ‖integerSecondDifference u v k x‖ ≤ 1 := by
  rw [integerSecondDifference, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hu _)).trans (hv _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteGraphEnergy
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def shiftedAdditiveQuadruples (A : Finset G) (d : G) : Finset ((G × G) × (G × G)) :=
  ((A ×ˢ A) ×ˢ (A ×ˢ A)).filter
    (fun x => x.1.1 + x.1.2 = x.2.1 + x.2.2 + d)

theorem shiftedAdditiveQuadruples_card (A : Finset G) (d : G) :
    (shiftedAdditiveQuadruples A d).card =
      ∑ r : G, ((A ×ˢ A).filter (fun x => x.1 + x.2 = r)).card *
        ((A ×ˢ A).filter (fun x => x.1 + x.2 = r - d)).card := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun x : (G × G) × (G × G) => x.1.1 + x.1.2)
    (t := Finset.univ) (by intro x _; exact Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro r _
  have heq : (shiftedAdditiveQuadruples A d).filter
      (fun x => x.1.1 + x.1.2 = r) =
        ((A ×ˢ A).filter (fun x => x.1 + x.2 = r)) ×ˢ
          ((A ×ˢ A).filter (fun x => x.1 + x.2 = r - d)) := by
    ext x
    simp only [shiftedAdditiveQuadruples, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨h₁, h₂⟩, hsum⟩, hr⟩
      exact ⟨⟨h₁, hr⟩, h₂, (eq_sub_iff_add_eq).mpr (hsum.symm.trans hr)⟩
    · rintro ⟨⟨h₁, hr⟩, h₂, hd⟩
      exact ⟨⟨⟨h₁, h₂⟩, hr.trans ((eq_sub_iff_add_eq).mp hd).symm⟩, hr⟩
  rw [heq, Finset.card_product]

theorem shiftedAdditiveQuadruples_card_le_energy (A : Finset G) (d : G) :
    (shiftedAdditiveQuadruples A d).card ≤ Finset.addEnergy A A := by
  rw [shiftedAdditiveQuadruples_card, Finset.addEnergy_eq_sum_sq]
  let f : G → ℕ := fun r => ((A ×ˢ A).filter (fun x => x.1 + x.2 = r)).card
  change (∑ r : G, f r * f (r - d)) ≤ ∑ r : G, f r ^ 2
  have hshift : (∑ r : G, f (r - d) ^ 2) = ∑ r : G, f r ^ 2 :=
    Fintype.sum_equiv (Equiv.subRight d) _ _ (fun _ => rfl)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f (fun r => f (r - d))
  rw [hshift] at hcs
  exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp (by simpa only [pow_two] using hcs)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G K : Type*} [AddCommGroup G] [AddCommGroup K]
  [Fintype G] [Fintype K] [DecidableEq G] [DecidableEq K]

def additiveGraph (H : Finset G) (b : G → K) : Finset (G × K) :=
  H.image (fun h => (h, b h))

omit [AddCommGroup G] [AddCommGroup K] [Fintype G] [Fintype K] in
theorem additiveGraph_card (H : Finset G) (b : G → K) :
    (additiveGraph H b).card = H.card :=
  Finset.card_image_of_injective H (fun _ _ h => congrArg Prod.fst h)

def additiveGraphQuadruple (b : G → K) (t : G × G × G) :
    ((G × K) × (G × K)) × ((G × K) × (G × K)) :=
  (((t.2.1 - t.1, b (t.2.1 - t.1)), (t.2.2, b t.2.2)),
    ((t.2.1, b t.2.1), (t.2.2 - t.1, b (t.2.2 - t.1))))

omit [AddCommGroup K] [Fintype G] [Fintype K] [DecidableEq G] [DecidableEq K] in
theorem additiveGraphQuadruple_injective (b : G → K) :
    Function.Injective (additiveGraphQuadruple b) := by
  intro t u h
  have hh : t.2.1 = u.2.1 := congrArg (fun x => x.2.1.1) h
  have hk : t.2.2 = u.2.2 := congrArg (fun x => x.1.2.1) h
  have hs : t.2.1 - t.1 = u.2.1 - u.1 := congrArg (fun x => x.1.1.1) h
  rw [hh, sub_eq_add_neg, sub_eq_add_neg] at hs
  exact Prod.ext (neg_injective (add_left_cancel hs)) (Prod.ext hh hk)

theorem graph_energy_of_few_quadruple_differences
    (H : Finset G) (S : Finset (G × G × G)) (b : G → K) (D : Finset K)
    (hH : ∀ t ∈ S, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H)
    (hD : ∀ t ∈ S, b (t.2.1 - t.1) + b t.2.2 - b t.2.1 - b (t.2.2 - t.1) ∈ D) :
    S.card ≤ D.card * Finset.addEnergy (additiveGraph H b) (additiveGraph H b) := by
  let δ : G × G × G → K := fun t =>
    b (t.2.1 - t.1) + b t.2.2 - b t.2.1 - b (t.2.2 - t.1)
  have hcard (d : K) : (S.filter (fun t => δ t = d)).card ≤
      (shiftedAdditiveQuadruples (additiveGraph H b) (0, d)).card := by
    apply Finset.card_le_card_of_injOn (additiveGraphQuadruple b) _
      (fun _ _ _ _ h => additiveGraphQuadruple_injective b h)
    intro t ht
    obtain ⟨htS, hδ⟩ := Finset.mem_filter.mp ht
    obtain ⟨h₀, h₁, h₂, h₃⟩ := hH t htS
    have hmem (x : G) (hx : x ∈ H) : (x, b x) ∈ additiveGraph H b :=
      Finset.mem_image.mpr ⟨x, hx, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨hmem _ h₁, hmem _ h₂⟩,
        Finset.mem_product.mpr ⟨hmem _ h₀, hmem _ h₃⟩⟩, ?_⟩
    apply Prod.ext
    · change (t.2.1 - t.1) + t.2.2 = (t.2.1 + (t.2.2 - t.1)) + 0
      abel
    · change b (t.2.1 - t.1) + b t.2.2 = (b t.2.1 + b (t.2.2 - t.1)) + d
      rw [← hδ]
      dsimp only [δ]
      abel
  calc
    S.card = ∑ d ∈ D, (S.filter (fun t => δ t = d)).card :=
      Finset.card_eq_sum_card_fiberwise hD
    _ ≤ ∑ d ∈ D, (shiftedAdditiveQuadruples (additiveGraph H b) (0, d)).card :=
      Finset.sum_le_sum (fun d _ => hcard d)
    _ ≤ ∑ _d ∈ D, Finset.addEnergy (additiveGraph H b) (additiveGraph H b) :=
      Finset.sum_le_sum (fun d _ => shiftedAdditiveQuadruples_card_le_energy _ (0, d))
    _ = _ := by simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeRoundedGraphEnergy
namespace OAI

section

namespace Erdos3

theorem floor_four_difference_bound (c x₀ x₁ x₂ x₃ : ℝ) (z : ℤ)
    (h : |c + (x₁ + x₂ - x₀ - x₃) - z| ≤ 1) :
    |⌊c⌋ + (⌊x₁⌋ + ⌊x₂⌋ - ⌊x₀⌋ - ⌊x₃⌋) - z| ≤ 6 := by
  have hc := Int.floor_le c
  have hc' := Int.sub_one_lt_floor c
  have h₀ := Int.floor_le x₀
  have h₀' := Int.sub_one_lt_floor x₀
  have h₁ := Int.floor_le x₁
  have h₁' := Int.sub_one_lt_floor x₁
  have h₂ := Int.floor_le x₂
  have h₂' := Int.sub_one_lt_floor x₂
  have h₃ := Int.floor_le x₃
  have h₃' := Int.sub_one_lt_floor x₃
  obtain ⟨hl, hu⟩ := abs_le.mp h
  have hh : |((⌊c⌋ + (⌊x₁⌋ + ⌊x₂⌋ - ⌊x₀⌋ - ⌊x₃⌋) - z : ℤ) : ℝ)| ≤ 6 := by
    rw [abs_le]
    push_cast
    constructor <;> linarith
  exact_mod_cast hh

end Erdos3

end

section

namespace Erdos3

def coordinateDenominatorGrid {I : Type*} (l : I → ℕ) : Set (I → ℝ) :=
  {q | ∃ z : I → ℤ, ∀ i, (z i : ℝ) = (l i : ℝ) * q i}

noncomputable def variableRoundedCoefficient {I : Type*} (M l : I → ℕ)
    (a : I → ℝ) : ∀ i, ZMod (M i) :=
  fun i => ((⌊(M i : ℝ) * l i * a i⌋ : ℤ) : ZMod (M i))

noncomputable def variableRoundingErrors {I : Type*} [Fintype I]
    (M l : I → ℕ) (c : I → ℝ) : Finset (∀ i, ZMod (M i)) := by
  classical
  exact (Fintype.piFinset (fun _ : I => Finset.Icc (-6 : ℤ) 6)).image
    (fun b i => (b i : ZMod (M i)) - ((⌊(M i : ℝ) * l i * c i⌋ : ℤ) : ZMod (M i)))

theorem variableRoundingErrors_card_le {I : Type*} [Fintype I]
    (M l : I → ℕ) (c : I → ℝ) :
    (variableRoundingErrors M l c).card ≤ 13 ^ Fintype.card I := by
  classical
  calc
    _ ≤ (Fintype.piFinset (fun _ : I => Finset.Icc (-6 : ℤ) 6)).card := Finset.card_image_le
    _ = _ := by simp

theorem variableRoundedCoefficient_four_mem {I : Type*} [Fintype I]
    (M l : I → ℕ) (c : I → ℝ) (a : Fin 4 → I → ℝ) (q ε : I → ℝ)
    (hgrid : q ∈ coordinateDenominatorGrid l)
    (hsmall : ∀ i, (M i : ℝ) * l i * ε i ≤ 1)
    (herror : ∀ i, |c i + (a 1 i + a 2 i - a 0 i - a 3 i) - q i| ≤ ε i) :
    variableRoundedCoefficient M l (a 1) + variableRoundedCoefficient M l (a 2) -
      variableRoundedCoefficient M l (a 0) - variableRoundedCoefficient M l (a 3) ∈
        variableRoundingErrors M l c := by
  classical
  obtain ⟨z, hz⟩ := hgrid
  let k : I → ℝ := fun i => (M i : ℝ) * l i
  let b : I → ℤ := fun i => ⌊k i * c i⌋ +
    (⌊k i * a 1 i⌋ + ⌊k i * a 2 i⌋ - ⌊k i * a 0 i⌋ - ⌊k i * a 3 i⌋) - (M i : ℤ) * z i
  have hb (i : I) : b i ∈ Finset.Icc (-6 : ℤ) 6 := by
    have hk : 0 ≤ k i := by dsimp [k]; positivity
    have heq : k i * (c i + (a 1 i + a 2 i - a 0 i - a 3 i) - q i) =
        k i * c i + (k i * a 1 i + k i * a 2 i - k i * a 0 i - k i * a 3 i) -
          (M i : ℝ) * z i := by
      rw [hz i]
      dsimp [k]
      ring
    have hh : |k i * c i + (k i * a 1 i + k i * a 2 i - k i * a 0 i - k i * a 3 i) -
        (M i : ℝ) * z i| ≤ 1 := by
      rw [← heq, abs_mul, abs_of_nonneg hk]
      exact (mul_le_mul_of_nonneg_left (herror i) hk).trans (hsmall i)
    have hf := floor_four_difference_bound (k i * c i) (k i * a 0 i) (k i * a 1 i)
      (k i * a 2 i) (k i * a 3 i) ((M i : ℤ) * z i)
      (by simpa only [Int.cast_mul, Int.cast_natCast] using hh)
    exact Finset.mem_Icc.mpr (abs_le.mp hf)
  apply Finset.mem_image.mpr
  refine ⟨b, Fintype.mem_piFinset.mpr hb, ?_⟩
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, variableRoundedCoefficient, b, k, Int.cast_sub,
    Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, sub_zero]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteCoefficientLift {I : Type*} {M : ℕ}
    (l : ℕ) (b : I → ZMod M) : I → ℝ :=
  fun i => ((b i).val : ℝ) / ((M : ℝ) * l)

end Erdos3

end

section

namespace Erdos3

variable {G I : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] [Fintype I]

theorem variable_graph_energy (H : Finset G) (S : Finset (G × G × G))
    (a : G → I → ℝ) (c : I → ℝ) (M l : I → ℕ) [∀ i, NeZero (M i)] (ε : I → ℝ)
    (hH : ∀ t ∈ S, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H)
    (hsmall : ∀ i, (M i : ℝ) * l i * ε i ≤ 1)
    (hnear : ∀ t ∈ S, ∃ q ∈ coordinateDenominatorGrid l,
      ∀ i, |c i + (a (t.2.1 - t.1) i + a t.2.2 i - a t.2.1 i - a (t.2.2 - t.1) i) - q i| ≤ ε i) :
    S.card ≤ 13 ^ Fintype.card I *
      Finset.addEnergy (additiveGraph H (fun h => variableRoundedCoefficient M l (a h)))
        (additiveGraph H (fun h => variableRoundedCoefficient M l (a h))) := by
  classical
  have h := graph_energy_of_few_quadruple_differences H S
    (fun h => variableRoundedCoefficient M l (a h)) (variableRoundingErrors M l c) hH (by
      intro t ht
      obtain ⟨q, hq, herr⟩ := hnear t ht
      exact variableRoundedCoefficient_four_mem M l c
        ![a t.2.1, a (t.2.1 - t.1), a t.2.2, a (t.2.2 - t.1)] q ε hq hsmall herr)
  exact h.trans (Nat.mul_le_mul_right _ (variableRoundingErrors_card_le M l c))

theorem variable_graph_energy_density (H : Finset G) (S : Finset (G × G × G))
    (a : G → I → ℝ) (c : I → ℝ) (M l : I → ℕ) [∀ i, NeZero (M i)] (ε : I → ℝ) {p : ℝ}
    (hH : ∀ t ∈ S, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H)
    (hsmall : ∀ i, (M i : ℝ) * l i * ε i ≤ 1)
    (hnear : ∀ t ∈ S, ∃ q ∈ coordinateDenominatorGrid l,
      ∀ i, |c i + (a (t.2.1 - t.1) i + a t.2.2 i - a t.2.1 i - a (t.2.2 - t.1) i) - q i| ≤ ε i)
    (hdensity : Real.exp (-p) * (H.card : ℝ) ^ 3 ≤ S.card) :
    Real.exp (-(p + 13 * Fintype.card I)) * (H.card : ℝ) ^ 3 ≤
      (Finset.addEnergy (additiveGraph H (fun h => variableRoundedCoefficient M l (a h)))
        (additiveGraph H (fun h => variableRoundedCoefficient M l (a h))) : ℝ) := by
  classical
  let E := Finset.addEnergy (additiveGraph H (fun h => variableRoundedCoefficient M l (a h)))
    (additiveGraph H (fun h => variableRoundedCoefficient M l (a h)))
  have hcard := variable_graph_energy H S a c M l ε hH hsmall hnear
  have hcount : (13 : ℝ) ^ Fintype.card I ≤ Real.exp (13 * Fintype.card I) := by
    calc
      _ ≤ (Real.exp 13) ^ Fintype.card I :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (13 : ℝ)]) _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hlarge : Real.exp (-p) * (H.card : ℝ) ^ 3 ≤
      Real.exp (13 * Fintype.card I) * E := by
    apply hdensity.trans
    have hc := (Nat.cast_le (α := ℝ)).mpr hcard
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hc
    exact hc.trans (mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg E))
  calc
    _ = Real.exp (-(13 * Fintype.card I)) * (Real.exp (-p) * (H.card : ℝ) ^ 3) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-(13 * Fintype.card I)) * (Real.exp (13 * Fintype.card I) * E) :=
      mul_le_mul_of_nonneg_left hlarge (Real.exp_nonneg _)
    _ = E := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeGraphSmallDifference
namespace OAI

section

namespace Erdos3

open scoped Pointwise

variable {G V : Type*} [DecidableEq G] [DecidableEq V]

theorem mem_additiveGraph_iff (H : Finset G) (b : G → V) (x : G × V) :
    x ∈ additiveGraph H b ↔ x.1 ∈ H ∧ x.2 = b x.1 := by
  rw [additiveGraph, Finset.mem_image]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨hh, rfl⟩
  · intro hx
    exact ⟨x.1, hx.1, Prod.ext rfl hx.2.symm⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ProperAffineBoxRestriction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def centeredScalarBlock (R k : ℕ) (x : ℤ) : ℕ :=
  (x + (R : ℤ)).toNat / (2 * (R / (2 * k)) + 1)

theorem centeredScalarBlock_lt (R k : ℕ) (hk : 0 < k) (x : ℤ)
    (hx : |x| ≤ (R : ℤ)) : centeredScalarBlock R k x < 4 * k := by
  have htwo : 0 < 2 * k := by omega
  have hR := Nat.lt_mul_div_succ R htwo
  have ht : (x + (R : ℤ)).toNat ≤ 2 * R := by
    have h := abs_le.mp hx
    omega
  have hku : 0 ≤ k * (R / (2 * k)) := Nat.zero_le _
  have hcover : 2 * R < 4 * k * (2 * (R / (2 * k)) + 1) := by
    nlinarith only [hR, hku]
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * (R / (2 * k)) + 1)).mpr
  exact ht.trans_lt hcover

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicMixedReflection
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def tripleCyclicEmbed {N : ℕ} (x : ZMod N) : ZMod (3 * N) := (x.val : ℕ)

theorem tripleCyclicEmbed_injective {N : ℕ} [NeZero N] :
    Function.Injective (tripleCyclicEmbed (N := N)) := by
  intro x y hxy
  have hN := NeZero.pos N
  have hx : x.val < 3 * N := by have := x.val_lt; omega
  have hy : y.val < 3 * N := by have := y.val_lt; omega
  have hv := congrArg ZMod.val hxy
  simp only [tripleCyclicEmbed, ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy] at hv
  exact ZMod.val_injective N hv

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def tripleCarryStart (N : ℕ) : Fin 3 → ℕ := ![0, 2 * N, N]

theorem triple_difference_val {N : ℕ} [NeZero N] (z x y : ZMod N) :
    ((tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y).val : ℤ) =
      if 0 ≤ (z.val : ℤ) - x.val - y.val then (z.val : ℤ) - x.val - y.val
      else (z.val : ℤ) - x.val - y.val + 3 * N := by
  let t : ℤ := (z.val : ℤ) - x.val - y.val
  have hN := NeZero.pos N
  have hz := z.val_lt
  have hx := x.val_lt
  have hy := y.val_lt
  have hlo : -(2 * (N : ℤ)) < t := by dsimp [t]; omega
  have hhi : t < (N : ℤ) := by dsimp [t]; omega
  have hcast : (t : ZMod (3 * N)) =
      tripleCyclicEmbed z - tripleCyclicEmbed x - tripleCyclicEmbed y := by
    simp [t, tripleCyclicEmbed]
  rw [← hcast, ZMod.val_intCast]
  change t % (3 * (N : ℤ)) = if 0 ≤ t then t else t + 3 * N
  by_cases ht : 0 ≤ t
  · rw [if_pos ht, Int.emod_eq_of_lt ht (by omega)]
  · rw [if_neg ht]
    calc
      t % (3 * (N : ℤ)) = (t + 3 * N) % (3 * (N : ℤ)) := by simp
      _ = t + 3 * N := Int.emod_eq_of_lt (by omega) (by omega)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPermutationTensor
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finite_product_unit_vector {A I : Type*} [Fintype A] [DecidableEq A] [Fintype I]
    (f : A → I → ℂ) (hf : ∀ a, ∑ i, ‖f a i‖ ^ 2 = 1) :
    ∑ v : A → I, ‖∏ a, f a (v a)‖ ^ 2 = 1 := by
  simp only [norm_prod, ← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun (a : A) (i : I) => ‖f a i‖ ^ 2)]
  simp only [hf, Finset.prod_const_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def mixedPermutationIndex (s : ℕ) : Equiv.Perm (Fin s) ≃ Fin s.factorial :=
  Fintype.equivFinOfCardEq (by simp only [Fintype.card_perm, Fintype.card_fin])

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuarticRootExchange
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def complexCrossContraction {K L : Type*} [Fintype K] [Fintype L]
    (a b : ℂ) (u : K → ℂ) (v : L → ℂ) (G : K → L → ℂ) : ℂ :=
  ∑ kl : K × L, (a * star (u kl.1)) * star (b * star (v kl.2)) * G kl.1 kl.2

theorem complexCrossContraction_rank_one {K L : Type*} [Fintype K] [Fintype L]
    (a b : ℂ) (u f : K → ℂ) (v g : L → ℂ) :
    complexCrossContraction a b u v (fun k l => f k * star (g l)) =
      (a * star b) * (∑ k, star (u k) * f k) * star (∑ l, star (v l) * g l) := by
  simp only [complexCrossContraction, Fintype.sum_prod_type, star_sum,
    star_mul, star_star, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem norm_complexCrossContraction_le_card {K L : Type*} [Fintype K] [Fintype L]
    (a b : ℂ) (u : K → ℂ) (v : L → ℂ) (G : K → L → ℂ) {B : ℝ}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hu : ∀ k, ‖u k‖ ≤ 1) (hv : ∀ l, ‖v l‖ ≤ 1) (hG : ∀ k l, ‖G k l‖ ≤ B) :
    ‖complexCrossContraction a b u v G‖ ≤ (Fintype.card (K × L) : ℝ) * B := by
  unfold complexCrossContraction
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : K × L, B := by
      apply Finset.sum_le_sum
      intro kl _
      rw [norm_mul]
      apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hG kl.1 kl.2)
      rw [norm_mul, norm_star, norm_mul, norm_star, norm_mul, norm_star]
      refine (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_).trans ?_
      · exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans (hu kl.1)
      · exact (mul_le_of_le_one_left (norm_nonneg _) hb).trans (hv kl.2)
    _ = _ := by simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeComparisonLift
namespace OAI

section

namespace Erdos3

theorem four_projection_petal_add_invariant
    {R I E : Type*} {V : I → Type*} [CommRing R]
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] [AddCommGroup E]
    (f : (∀ i, V i) → E) (K : ∀ i, Submodule R (Fin 4 → V i))
    (hK : ∀ z : ∀ i, Fin 4 → V i, (∀ i, z i ∈ K i) → fourFunctionDifference f z = 0)
    (x p : ∀ i, V i) (hx : ∀ i, x i ∈ (K i).map (LinearMap.proj 0))
    (hp : ∀ i, LinearMap.single R (fun _ : Fin 4 => V i) 0 (p i) ∈ K i) :
    f (x + p) = f x := by
  classical
  have hlift (i : I) : ∃ z ∈ K i, z 0 = x i := hx i
  choose z hz hz0 using hlift
  let y (i : I) := z i + LinearMap.single R (fun _ : Fin 4 => V i) 0 (p i)
  have hy (i : I) : y i ∈ K i := (K i).add_mem (hz i) (hp i)
  have hy0 : (fun i => y i 0) = x + p := by
    funext i
    simp only [y, Pi.add_apply, LinearMap.single_apply, Pi.single_eq_same, hz0]
  have hy1 : (fun i => y i 1) = fun i => z i 1 := by
    funext i
    simp [y, LinearMap.single_apply]
  have hy2 : (fun i => y i 2) = fun i => z i 2 := by
    funext i
    simp [y, LinearMap.single_apply]
  have hy3 : (fun i => y i 3) = fun i => z i 3 := by
    funext i
    simp [y, LinearMap.single_apply]
  have h₀ := hK z hz
  have h₁ := hK y hy
  rw [fourFunctionDifference, hy0, hy1, hy2, hy3] at h₁
  rw [fourFunctionDifference, show (fun i => z i 0) = x from funext hz0] at h₀
  simp only [sub_eq_add_neg] at h₀ h₁
  exact add_right_cancel (add_right_cancel (add_right_cancel (h₁.trans h₀.symm)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DiagonalRowTransfer
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_mul_star_sub_mul_star_le_of_le_one {a b c d : ℂ}
    (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    ‖a * star b - c * star d‖ ≤ ‖a - c‖ + ‖b - d‖ := by
  calc
    _ = ‖(a - c) * star b + c * star (b - d)‖ := by
      congr 1
      simp only [star_sub]
      ring
    _ ≤ ‖(a - c) * star b‖ + ‖c * star (b - d)‖ := norm_add_le _ _
    _ = ‖a - c‖ * ‖b‖ + ‖c‖ * ‖b - d‖ := by simp only [norm_mul, norm_star]
    _ ≤ _ := add_le_add (mul_le_of_le_one_right (norm_nonneg _) hb)
      (mul_le_of_le_one_left (norm_nonneg _) hc)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.NativeMixedFourierProfiles
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mean_twisted_nat_translate_error {N : ℕ} [NeZero N]
    (q : ZMod N → ℂ) (ζ : ℂ) (hζ : ‖ζ‖ ≤ 1) {ε : ℝ}
    (hstep : (𝔼 n : ZMod N, ‖q (n + 1) - ζ * q n‖) ≤ ε) (m : ℕ) :
    (𝔼 n : ZMod N, ‖q (n + m) - ζ ^ m * q n‖) ≤ (m : ℝ) * ε := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hpoint (n : ZMod N) :
        ‖q (n + (m + 1 : ℕ)) - ζ ^ (m + 1) * q n‖ ≤
          ‖q ((n + m) + 1) - ζ * q (n + m)‖ + ‖q (n + m) - ζ ^ m * q n‖ := by
      calc
        _ = ‖(q ((n + m) + 1) - ζ * q (n + m)) +
            ζ * (q (n + m) - ζ ^ m * q n)‖ := by
          simp only [Nat.cast_add, Nat.cast_one, add_assoc, pow_succ]
          congr 1
          ring
        _ ≤ ‖q ((n + m) + 1) - ζ * q (n + m)‖ +
            ‖ζ * (q (n + m) - ζ ^ m * q n)‖ := norm_add_le _ _
        _ ≤ _ := by
          rw [norm_mul]
          exact add_le_add le_rfl (mul_le_of_le_one_left (norm_nonneg _) hζ)
    have hshift : (𝔼 n : ZMod N, ‖q ((n + m) + 1) - ζ * q (n + m)‖) =
        𝔼 n : ZMod N, ‖q (n + 1) - ζ * q n‖ := by
      exact Fintype.expect_equiv (Equiv.addRight (m : ZMod N)) _ _ (fun _ => rfl)
    calc
      _ ≤ (𝔼 n : ZMod N, ‖q ((n + m) + 1) - ζ * q (n + m)‖) +
          (𝔼 n : ZMod N, ‖q (n + m) - ζ ^ m * q n‖) := by
        rw [← Finset.expect_add_distrib]
        exact Finset.expect_le_expect (fun n _ => hpoint n)
      _ ≤ ε + (m : ℝ) * ε := by rw [hshift]; exact add_le_add hstep ih
      _ = ((m + 1 : ℕ) : ℝ) * ε := by push_cast; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubicPairPartitionPrecision
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_sub_positive_sum_le_weighted {I : Type*} [Fintype I]
    (w : I → ℝ) (c : I → ℂ) (t : ℂ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    ‖t - ∑ i, (w i : ℂ) * c i‖ ≤ ∑ i, w i * ‖t - c i‖ := by
  have hsumC : (∑ i, (w i : ℂ)) = 1 := by exact_mod_cast hsum
  have hid : t - ∑ i, (w i : ℂ) * c i = ∑ i, (w i : ℂ) * (t - c i) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsumC, one_mul]
  rw [hid]
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedRootLosses
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def mixedCornerSample {s : ℕ} (v : Fin (s + 3) → Fin 2) : Fin (s + 3) → Fin 2 :=
  fun k => (v k).rev

def mixedTailSortPermutation {s : ℕ} (v : Fin (s + 3) → Fin 2) : Equiv.Perm (Fin (s + 2)) :=
  Tuple.sort (fun j => mixedCornerSample v j.succ)

noncomputable def mixedHeadIndex {s : ℕ} (v : Fin (s + 3) → Fin 2) : Fin (s + 2) :=
  if h : ∃ j : Fin (s + 2), v j.succ = 1 then Classical.choose h else 0

noncomputable def mixedHeadPermutation {s : ℕ} (v : Fin (s + 3) → Fin 2) :
    Equiv.Perm (Fin (s + 2)) := Equiv.swap 0 (mixedHeadIndex v)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem root_corner_loss_identity (D : ℝ) (n m q : ℕ) (ε : ℝ) :
    (D ^ n) ^ m * (((D ^ n) ^ 2 * D ^ (2 * n)) ^ m *
      ((m : ℝ) * ((D ^ n) ^ 2 * (D ^ (2 * n) *
        ((n : ℝ) * ((q : ℝ) ^ 2 * D ^ 2 * ε)))))) =
      ((m * n * q ^ 2 : ℕ) : ℝ) * D ^ (5 * n * m + 4 * n + 2) * ε := by
  have hp0 : (D ^ n) ^ m = D ^ (n * m) := (pow_mul D n m).symm
  have hp1 : ((D ^ n) ^ 2 * D ^ (2 * n)) ^ m = D ^ ((n * 2 + 2 * n) * m) := by
    simp only [← pow_mul, ← pow_add]
  have hp2 : (D ^ n) ^ 2 = D ^ (n * 2) := (pow_mul D n 2).symm
  have hp : D ^ (n * m) * D ^ ((n * 2 + 2 * n) * m) * D ^ (n * 2) * D ^ (2 * n) * D ^ 2 =
      D ^ (5 * n * m + 4 * n + 2) := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    ring
  rw [hp0, hp1, hp2]
  calc
    _ = ((m : ℝ) * n * (q : ℝ) ^ 2) *
        (D ^ (n * m) * D ^ ((n * 2 + 2 * n) * m) * D ^ (n * 2) * D ^ (2 * n) * D ^ 2) * ε := by ring
    _ = _ := by rw [hp]; simp only [Nat.cast_mul, Nat.cast_pow]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BinaryWordSupports
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def binaryWordSupport {n : ℕ} (v : Fin n → Fin 2) : Finset (Fin n) :=
  Finset.univ.filter (fun i => v i = 1)

def binaryWordSupportEquiv (n : ℕ) : (Fin n → Fin 2) ≃ Finset (Fin n) where
  toFun := binaryWordSupport
  invFun S i := if i ∈ S then 1 else 0
  left_inv v := by
    funext i
    by_cases h : v i = 1
    · simp [binaryWordSupport, h]
    · simpa only [binaryWordSupport, Finset.mem_filter, Finset.mem_univ, true_and,
        if_neg h] using (binary_eq_zero_of_ne_one (v i) h).symm
  right_inv S := by
    ext i
    simp [binaryWordSupport]

theorem binaryWordSupport_card {n : ℕ} (v : Fin n → Fin 2) :
    (binaryWordSupport v).card = ∑ i, (v i).val := by
  rw [binaryWordSupport, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : v i = 1
  · simp [h]
  · rw [if_neg h, binary_eq_zero_of_ne_one (v i) h]
    rfl

theorem binaryWordSupport_zero (n : ℕ) :
    binaryWordSupport (fun _ : Fin n => 0) = ∅ := by
  ext i
  simp [binaryWordSupport]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedFrozenMiddleRows
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def mixedWeightSample (s : ℕ) (k : Fin (s + 3)) : Fin (s + 3) → Fin 2 :=
  fun j => if j.val < k.val + 1 then 0 else 1

end Erdos3

end

end OAI
end


