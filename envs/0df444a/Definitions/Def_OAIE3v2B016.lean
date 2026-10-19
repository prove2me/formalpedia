-- Prove2me | Definitions.Def_OAIE3v2B016
-- name    : OAIE3v2B016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:58:13.175751+00:00
-- url     : https://prove2.me/theorems/9d639d8d-ff9a-4c95-b4d8-b06476d7d59a
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 17 of 311
-- statement:
--   Definitions bundle 17 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/MultilinearityBudgets.lean`, `Estimates/BlockSubsetCount.lean`, `Estimates/CommonRefilteredFactorization.lean`, `Estimates/FiniteAssignmentPartition.lean`, `Estimates/FlatWeightedComparison.lean`, `Estimates/MixedFrozenMiddleRows.lean`, `Estimates/MixedRootLosses.lean`, `Estimates/MultidegreePredecessor.lean`, `Estimates/NativeLocalPivotVerticalPartners.lean`, `Estimates/OriginalMixedRootEquivalence.lean`, `Estimates/PowerIndexFromOrderedGenerators.lean`, `Estimates/ProductiveFrozenLocalMajorFamily.lean`, `Estimates/RealFiniteZeroExtension.lean`, `Estimates/RealSubquotientEquiv.lean`, `Estimates/SaturatedFlag.lean`, `Estimates/SquarefreeSplitCount.lean`, `Estimates/SubmoduleSupRestriction.lean`, `Geometry/MultidegreeCoordinateFreezing.lean`, `Geometry/NativeTernaryCoordinate.lean`, `Geometry/RealifiedPairCoordinates.lean`, `Lattices/AffineIntervalNormalizedBounds.lean`, `Lattices/CRTProgressionVanishing.lean`, `Lattices/IntegerAffineSubstitution.lean`, `Lattices/IntegerIntervalOverlap.lean`, `Lattices/IntegerRowInterpolationMixture.lean`, `Lattices/MixedArrayIntegerImage.lean`, `Linear/BoundedAdaptedBasis.lean`, `Linear/KernelProjectionPresentPivotIdeal.lean`, `Linear/OrderedBasisCoordinates.lean`, `Linear/ProperCyclicKernelBasis.lean`, `Linear/RationalSpanCoordinates.lean`, `Nilpotent/NiltestComplement.lean`, `Nilpotent/SquarefreeBracketHeight.lean`, `Polynomial/MarkedPolynomialGenerators.lean`, `Polynomial/RealPositivePolynomialEvaluation.lean`, `Polynomial/WeightedPolynomialRestriction.lean`, `Probability/LowDensityAmplification.lean`, `Probability/ProductSliceAxisDensity.lean`, `Sampling/RationalSpanGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalSpanGrid
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ V : Type*} [Fintype ι] [Fintype κ] [AddCommGroup V] [Module ℚ V]

noncomputable def spanningCoordinateMatrix (e : Basis ι ℚ V) (v : κ → V) : Matrix ι κ ℚ :=
  fun i j => e.repr (v j) i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSubquotientEquiv
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {V W Z : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] [AddCommGroup Z] [Module ℚ Z]

theorem realification_prod (f : V →ₗ[ℚ] W) (g : V →ₗ[ℚ] Z) (x : ℝ ⊗[ℚ] V) :
    TensorProduct.prodRight ℚ ℝ ℝ W Z ((f.prod g).baseChange ℝ x) =
      (f.baseChange ℝ x, g.baseChange ℝ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp <;> rfl
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]; rfl

theorem realification_prod_eq_zero_iff (f : V →ₗ[ℚ] W) (g : V →ₗ[ℚ] Z)
    (x : ℝ ⊗[ℚ] V) :
    (f.prod g).baseChange ℝ x = 0 ↔ f.baseChange ℝ x = 0 ∧ g.baseChange ℝ x = 0 := by
  constructor
  · intro h
    have he := congrArg (TensorProduct.prodRight ℚ ℝ ℝ W Z) h
    rw [realification_prod, map_zero] at he
    exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
  · intro h
    apply (TensorProduct.prodRight ℚ ℝ ℝ W Z).injective
    rw [realification_prod, map_zero, h.1, h.2]
    rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalSpanCoordinates
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem span_submodule_basis (P : Submodule ℚ L) (b : Basis κ ℚ P) :
    Submodule.span ℚ (Set.range (fun j => (b j : L))) = P := by
  change Submodule.span ℚ (Set.range (P.subtype ∘ b)) = P
  rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BlockSubsetCount
namespace OAI

section

namespace Erdos3

variable {ι σ : Type*} [Fintype σ] [DecidableEq ι] [DecidableEq σ]

def blockSubsetUnion (f : σ → Finset ι) : Finset ι := Finset.univ.biUnion f

omit [DecidableEq σ] in
theorem blockSubsetUnion_subset (f : σ → Finset ι) (S : Finset ι)
    (h : ∀ i, f i ⊆ S) : blockSubsetUnion f ⊆ S := by
  intro x hx
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
  exact h i hi

theorem blockSubsetUnion_filter (π : ι → σ) (f : σ → Finset ι)
    (h : ∀ i, ∀ x ∈ f i, π x = i) (i : σ) :
    (blockSubsetUnion f).filter (fun x => π x = i) = f i := by
  ext x
  constructor
  · intro hx
    obtain ⟨hx, hxi⟩ := Finset.mem_filter.mp hx
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hx
    have hji : j = i := (h j x hj).symm.trans hxi
    exact hji ▸ hj
  · intro hx
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩, h i x hx⟩

theorem blockSubsetUnion_filters (π : ι → σ) (S : Finset ι) :
    blockSubsetUnion (fun i => S.filter fun x => π x = i) = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp hi).1
  · intro hx
    exact Finset.mem_biUnion.mpr
      ⟨π x, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype σ] [DecidableEq ι] [DecidableEq σ]

noncomputable def blockSubsetEquiv (π : ι → σ) (S : Finset ι) (a : σ → ℕ) :
    {T : Finset ι // T ⊆ S ∧ ∀ i, (T.filter fun j => π j = i).card = a i} ≃
      (∀ i, {T : Finset ι // T ∈ (S.filter fun j => π j = i).powersetCard (a i)}) where
  toFun T i := ⟨T.val.filter (fun j => π j = i), Finset.mem_powersetCard.mpr ⟨by
    intro j hj
    exact Finset.mem_filter.mpr
      ⟨T.property.1 (Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2⟩,
    T.property.2 i⟩⟩
  invFun f := ⟨blockSubsetUnion (fun i => (f i).val), by
    have hf : ∀ i, (f i).val ⊆ S.filter (fun j => π j = i) :=
      fun i => (Finset.mem_powersetCard.mp (f i).property).1
    refine ⟨blockSubsetUnion_subset _ S (fun i j hj => (Finset.mem_filter.mp (hf i hj)).1), ?_⟩
    intro i
    rw [blockSubsetUnion_filter π _ (fun i j hj => (Finset.mem_filter.mp (hf i hj)).2)]
    exact (Finset.mem_powersetCard.mp (f i).property).2⟩
  left_inv T := Subtype.ext (blockSubsetUnion_filters π T.val)
  right_inv f := by
    funext i
    apply Subtype.ext
    exact blockSubsetUnion_filter π _
      (fun i j hj => (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp (f i).property).1 hj)).2) i

theorem card_blockSubsets [Fintype ι] (π : ι → σ) (S : Finset ι) (a : σ → ℕ) :
    Fintype.card {T : Finset ι // T ⊆ S ∧ ∀ i, (T.filter fun j => π j = i).card = a i} =
      ∏ i, ((S.filter fun j => π j = i).card).choose (a i) := by
  classical
  rw [Fintype.card_congr (blockSubsetEquiv π S a), Fintype.card_pi]
  simp only [Fintype.card_coe, Finset.card_powersetCard]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeSplitCount
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [Fintype σ]

def multidegreeFactorial (a : σ → ℕ) : ℕ := ∏ i, (a i).factorial

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} [Fintype σ]

def blockSplitMultiplicity (a b : σ → ℕ) : ℕ := ∏ i, (a i + b i).choose (a i)

theorem multidegreeFactorial_split (a b : σ → ℕ) :
    multidegreeFactorial a * multidegreeFactorial b * blockSplitMultiplicity a b =
      multidegreeFactorial (a + b) := by
  simp only [multidegreeFactorial, blockSplitMultiplicity, ← Finset.prod_mul_distrib, Pi.add_apply]
  apply Finset.prod_congr rfl
  intro i _
  have h := Nat.add_choose_mul_factorial_mul_factorial (b i) (a i)
  rw [Nat.add_comm (b i) (a i)] at h
  calc
    (a i).factorial * (b i).factorial * (a i + b i).choose (a i) =
        (a i + b i).choose (a i) * (b i).factorial * (a i).factorial := by ac_rfl
    _ = _ := h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FlatWeightedComparison
namespace OAI


namespace Erdos3

open scoped BigOperators

variable {ι : Type*}

noncomputable def finiteSetLp (s : Finset ι) (f : ι → ℝ) (p : ℕ) : ℝ :=
  if p = 0 then 0 else (𝔼 i ∈ s, |f i| ^ p) ^ (1 / (p : ℝ))

end Erdos3


namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def convolution (L : Finset G) (f g : G → ℝ) (t : G) : ℝ :=
  (∑ x, f x * g (t - x)) / L.card

noncomputable def correlation (L : Finset G) (f g : G → ℝ) (t : G) : ℝ :=
  (∑ x, f (x + t) * g x) / L.card

noncomputable def sumMoment (S : Finset G) (f : G → ℝ) (j : ℕ) : ℝ :=
  𝔼 s ∈ S, 𝔼 t ∈ S, f (s + t) ^ j

noncomputable def differenceMoment (S : Finset G) (f : G → ℝ) (j : ℕ) : ℝ :=
  𝔼 s ∈ S, 𝔼 t ∈ S, f (s - t) ^ j

noncomputable def momentVector (S : Finset G) (f : G → ℝ) (j : ℕ) (v : Fin j → G) : ℝ :=
  𝔼 s ∈ S, ∏ i, f (s - v i)

noncomputable def plusMomentVector (S : Finset G) (f : G → ℝ) (j : ℕ) (v : Fin j → G) : ℝ :=
  𝔼 s ∈ S, ∏ i, f (s + v i)

end Erdos3.LocalConvolution


namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

noncomputable def sumLp (S : Finset G) (f : G → ℝ) (p : ℕ) : ℝ :=
  finiteSetLp (S ×ˢ S) (fun x => f (x.1 + x.2)) p

noncomputable def differenceLp (S : Finset G) (f : G → ℝ) (p : ℕ) : ℝ :=
  finiteSetLp (S ×ˢ S) (fun x => f (x.1 - x.2)) p

end Erdos3.LocalConvolution


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BoundedAdaptedBasis
namespace OAI

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {d : ℕ}

def realBasisTail (e : Basis (Fin d) ℝ L) (i : ℕ) : Submodule ℝ L where
  carrier := {x | ∀ j : Fin d, j.val < i → e.repr x j = 0}
  zero_mem' := by simp
  add_mem' hx hy := by
    intro j hj
    simp only [map_add, Finsupp.add_apply, hx j hj, hy j hj, zero_add]
  smul_mem' c x hx := by
    intro j hj
    simp only [map_smul, Finsupp.smul_apply, hx j hj, smul_zero]

theorem realBasisTail_antitone (e : Basis (Fin d) ℝ L) : Antitone (realBasisTail e) :=
  fun _ _ hij _ hx k hk => hx k (lt_of_lt_of_le hk hij)

def IsRealCentralLieBasis (e : Basis (Fin d) ℝ L) : Prop :=
  ∀ (j : Fin d) (a : L), ⁅a, e j⁆ ∈ realBasisTail e (j.val + 1)

namespace IsRealCentralLieBasis

variable {e : Basis (Fin d) ℝ L} (he : IsRealCentralLieBasis e)
include he

theorem lie_mem_tail_succ (i : ℕ) (a : L) {b : L} (hb : b ∈ realBasisTail e i) :
    ⁅a, b⁆ ∈ realBasisTail e (i + 1) := by
  classical
  rw [← e.sum_repr b, lie_sum]
  apply Submodule.sum_mem
  intro j _
  rw [lie_smul]
  by_cases hj : j.val < i
  · rw [hb j hj, zero_smul]
    exact (realBasisTail e (i + 1)).zero_mem
  · exact (realBasisTail e (i + 1)).smul_mem _
      (realBasisTail_antitone e (Nat.add_le_add_right (Nat.le_of_not_gt hj) 1) (he j a))

end IsRealCentralLieBasis

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.OrderedBasisCoordinates
namespace OAI

section

namespace Erdos3

open Module

theorem mem_drop_finRange_iff {d i : ℕ} {j : Fin d} :
    j ∈ (List.finRange d).drop i ↔ i ≤ j.val := by
  rw [List.mem_drop_iff_getElem]
  constructor
  · rintro ⟨k, hk, heq⟩
    have hval : i + k = j.val := by simpa using congrArg Fin.val heq
    omega
  · intro hij
    refine ⟨j.val - i, ?_, ?_⟩
    · simp only [List.length_finRange]
      omega
    · apply Fin.ext
      simp only [List.getElem_finRange, Fin.val_cast]
      omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PowerIndexFromOrderedGenerators
namespace OAI

section

namespace Erdos3

variable {G : Type*} [Group G] {d : ℕ}

def orderedGroupTailProduct (a : Fin d → G) (i : ℕ) : G :=
  (((List.finRange d).drop i).map a).prod

def orderedGroupProduct (a : Fin d → G) : G := orderedGroupTailProduct a 0

def orderedZpowProduct (a : Fin d → G) (z : Fin d → ℤ) : G :=
  orderedGroupProduct (fun j => a j ^ z j)

theorem orderedGroupTailProduct_terminal (a : Fin d → G) {i : ℕ} (hi : d ≤ i) :
    orderedGroupTailProduct a i = 1 := by
  simp only [orderedGroupTailProduct,
    List.drop_eq_nil_of_le (as := List.finRange d) (i := i) (by simpa using hi),
    List.map_nil, List.prod_nil]

theorem orderedGroupTailProduct_step (a : Fin d → G) (j : Fin d) :
    orderedGroupTailProduct a j.val = a j * orderedGroupTailProduct a (j.val + 1) := by
  unfold orderedGroupTailProduct
  rw [List.drop_eq_getElem_cons (by simp), List.map_cons, List.prod_cons]
  simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]

theorem orderedGroupTailProduct_congr (i : ℕ) {a b : Fin d → G}
    (h : ∀ j : Fin d, i ≤ j.val → a j = b j) :
    orderedGroupTailProduct a i = orderedGroupTailProduct b i := by
  apply congrArg List.prod
  apply List.map_congr_left
  intro j hj
  exact h j (mem_drop_finRange_iff.mp hj)

theorem orderedGroupProduct_map {H : Type*} [Group H] (f : G →* H) (a : Fin d → G) :
    f (orderedGroupProduct a) = orderedGroupProduct (fun j => f (a j)) := by
  simp only [orderedGroupProduct, orderedGroupTailProduct, List.drop_zero,
    map_list_prod, List.map_map, Function.comp_def]

theorem orderedZpowProduct_map {H : Type*} [Group H] (f : G →* H)
    (a : Fin d → G) (z : Fin d → ℤ) :
    f (orderedZpowProduct a z) = orderedZpowProduct (fun j => f (a j)) z := by
  simp only [orderedZpowProduct, orderedGroupProduct_map, map_zpow]

theorem exists_bounded_ordered_exponents (a : Fin d → G) (m : ℕ) (hm : 0 < m)
    (ha : ∀ j, a j ^ m = 1) (z : Fin d → ℤ) :
    ∃ r : Fin d → Fin m, orderedGroupProduct (fun j => a j ^ (r j).val) =
      orderedZpowProduct a z := by
  have hmz : (0 : ℤ) < m := by exact_mod_cast hm
  have hnonneg (j : Fin d) : 0 ≤ z j % (m : ℤ) := Int.emod_nonneg _ (ne_of_gt hmz)
  let r : Fin d → Fin m := fun j => ⟨(z j % (m : ℤ)).toNat, by
    have hlt := Int.emod_lt_of_pos (z j) hmz
    omega⟩
  refine ⟨r, ?_⟩
  unfold orderedZpowProduct
  apply congrArg orderedGroupProduct
  funext j
  rw [zpow_eq_zpow_emod' (z j) (ha j)]
  change a j ^ (z j % (m : ℤ)).toNat = a j ^ (z j % (m : ℤ))
  rw [← zpow_natCast, Int.toNat_of_nonneg (hnonneg j)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.SquarefreeBracketHeight
namespace OAI

section

namespace Erdos3

open Module

def squarefreeBracketHeight (n H : ℕ) : ℕ := (n ^ 2 + 1) * (H * H * H) ^ (n ^ 2)

theorem squarefreeBracketHeight_pos (n : ℕ) {H : ℕ} (hH : 1 ≤ H) :
    0 < squarefreeBracketHeight n H := by
  have hHpos : 0 < H := by omega
  unfold squarefreeBracketHeight
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedPolynomialRestriction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} [DecidableEq σ]

def omittedCoordinateWeight (i j : σ) : ℕ := if j = i then 0 else 1

theorem omittedCoordinateWeight_le_one (i j : σ) : omittedCoordinateWeight i j ≤ 1 := by
  unfold omittedCoordinateWeight
  split_ifs <;> omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MultidegreeCoordinateFreezing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} [DecidableEq σ]

def retainedCoordinateWeight (S : Finset σ) (i : σ) : ℕ := if i ∈ S then 1 else 0

def freezeCoordinates (S : Finset σ) (b : σ → ℤ) (x : S → ℤ) (i : σ) : ℤ :=
  if h : i ∈ S then x ⟨i, h⟩ else b i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SubmoduleSupRestriction
namespace OAI

section

namespace Erdos3

theorem submodule_comap_iSup_of_le_range {R M N : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {I : Sort*} (f : M →ₗ[R] N) (hf : Function.Injective f)
    (P : I → Submodule R N) (hP : ∀ i, P i ≤ LinearMap.range f) :
    (⨆ i, P i).comap f = ⨆ i, (P i).comap f := by
  apply Submodule.map_injective_of_injective hf
  rw [Submodule.map_comap_eq_of_le (iSup_le hP), Submodule.map_iSup]
  exact iSup_congr (fun i => (Submodule.map_comap_eq_of_le (hP i)).symm)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MultidegreePredecessor
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem multidegree_exists_predecessor {σ : Type*} [Fintype σ] [DecidableEq σ]
    (b : σ → ℕ) (hb : 0 < ∑ i, b i) :
    ∃ a : σ → ℕ, a < b ∧ (∑ i, a i) + 1 = ∑ i, b i := by
  have hne : b ≠ 0 := by intro h; simp only [h, Pi.zero_apply, Finset.sum_const_zero] at hb; omega
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have hbi : b i ≠ 0 := by simpa only [Pi.zero_apply] using hi
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hbi
  let a : σ → ℕ := Function.update b i k
  have heq : b = a + Pi.single i 1 := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [a, hk]
    · simp [a, Function.update_of_ne hji, Pi.single_eq_of_ne hji]
  have hle : a ≤ b := by rw [heq]; exact fun j => Nat.le_add_right _ _
  have hnot : ¬b ≤ a := by
    intro h
    have hh := h i
    simp only [a, Function.update_self, hk] at hh
    omega
  refine ⟨a, lt_iff_le_not_ge.mpr ⟨hle, hnot⟩, ?_⟩
  rw [heq]
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  congr 1
  simp

theorem multidegree_exists_predecessor_above {σ : Type*} [Fintype σ] [DecidableEq σ]
    (b : σ → ℕ) (n : ℕ) (hb : n + 1 ≤ ∑ i, b i) :
    ∃ a : σ → ℕ, a < b ∧ n ≤ ∑ i, a i := by
  obtain ⟨a, hab, ha⟩ := multidegree_exists_predecessor b (by omega)
  exact ⟨a, hab, by omega⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerAffineSubstitution
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ τ : Type*} [Fintype τ]

theorem integerLinearForm_eq_sum [DecidableEq τ] (f : (τ → ℤ) →+ ℤ) (x : τ → ℤ) :
    f x = ∑ j, f (Pi.single j 1) * x j := by
  conv_lhs => rw [pi_eq_sum_univ' x]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_zsmul]
  change x j * f (Pi.single j 1) = f (Pi.single j 1) * x j
  exact mul_comm _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ProductSliceAxisDensity
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem piFinset_axis_subset {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
    (A B : ∀ i, Finset (X i)) (hA : ∀ i, (A i).Nonempty)
    (hsub : Fintype.piFinset A ⊆ Fintype.piFinset B) (i : I) : A i ⊆ B i := by
  have hi := Finset.image_subset_image (f := fun x : ∀ i, X i => x i) hsub
  rw [Fintype.eval_image_piFinset A i (fun j _ => hA j)] at hi
  exact hi.trans (Fintype.eval_image_piFinset_subset B i)

theorem piFinset_card_ratio_le_axis {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
    (A B : ∀ i, Finset (X i)) (hA : ∀ i, (A i).Nonempty) (hB : ∀ i, (B i).Nonempty)
    (hsub : Fintype.piFinset A ⊆ Fintype.piFinset B) (i : I) :
    ((Fintype.piFinset A).card : ℝ) / (Fintype.piFinset B).card ≤
      ((A i).card : ℝ) / (B i).card := by
  let r : I → ℝ := fun j => ((A j).card : ℝ) / (B j).card
  have hr (j : I) : 0 ≤ r j ∧ r j ≤ 1 := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
    apply (div_le_one (by exact_mod_cast (hB j).card_pos : (0 : ℝ) < (B j).card)).mpr
    exact_mod_cast Finset.card_le_card (piFinset_axis_subset A B hA hsub j)
  have he : ((Fintype.piFinset A).card : ℝ) / (Fintype.piFinset B).card = ∏ j, r j := by
    simp only [Fintype.card_piFinset, Nat.cast_prod, Finset.prod_div_distrib, r]
  rw [he, ← Finset.mul_prod_erase Finset.univ r (Finset.mem_univ i)]
  exact mul_le_of_le_one_right (hr i).1 (Finset.prod_le_one (fun j _ => (hr j).1) (fun j _ => (hr j).2))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SaturatedFlag
namespace OAI

section

namespace Erdos3.IntegerBasisReduction.SaturatedFlag

open scoped BigOperators
open Function _root_.Set Submodule
open Module

variable {M : Type*} [AddCommGroup M]

def IsSaturated (P : Submodule ℤ M) : Prop :=
  ∀ (a : ℤ) (x : M), a ≠ 0 → a • x ∈ P → x ∈ P

@[simp] theorem isSaturated_bot [Module.IsTorsionFree ℤ M] :
    IsSaturated (⊥ : Submodule ℤ M) := by
  intro a x ha hx
  rw [Submodule.mem_bot] at hx ⊢
  exact (smul_eq_zero.mp hx).resolve_left ha

@[simp] theorem isSaturated_top : IsSaturated (⊤ : Submodule ℤ M) := by
  intro _ _ _ _
  exact Submodule.mem_top

theorem IsSaturated.comap_subtype {P O : Submodule ℤ M}
    (hP : IsSaturated P) (_hPO : P ≤ O) :
    IsSaturated (P.comap O.subtype) := by
  intro a x ha hx
  change (a • (x : M)) ∈ P at hx
  change (x : M) ∈ P
  exact hP a x ha hx

def realEmbed (d : ℕ) : (Fin d → ℤ) →ₗ[ℤ] (Fin d → ℝ) where
  toFun x i := (x i : ℝ)
  map_add' x y := by
    ext i
    simp
  map_smul' a x := by
    ext i
    simp

@[simp] theorem realEmbed_apply {d : ℕ} (x : Fin d → ℤ) (i : Fin d) :
    realEmbed d x i = (x i : ℝ) := rfl

theorem realEmbed_zsmul {d : ℕ} (a : ℤ) (x : Fin d → ℤ) :
    realEmbed d (a • x) = (a : ℝ) • realEmbed d x := by
  ext i
  simp [realEmbed]

def realPrefixLattice {d n : ℕ} (x : Fin n → (Fin d → ℤ)) (i : Fin n) :
    Submodule ℤ (Fin d → ℤ) :=
  ((Submodule.span ℝ (realEmbed d '' (x '' Set.Iic i))).restrictScalars ℤ).comap
    (realEmbed d)

@[simp] theorem mem_realPrefixLattice {d n : ℕ}
    {x : Fin n → (Fin d → ℤ)} {i : Fin n} {z : Fin d → ℤ} :
    z ∈ realPrefixLattice x i ↔
      realEmbed d z ∈
        Submodule.span ℝ (realEmbed d '' (x '' Set.Iic i)) :=
  Iff.rfl

theorem isSaturated_realPrefixLattice {d n : ℕ}
    (x : Fin n → (Fin d → ℤ)) (i : Fin n) :
    IsSaturated (realPrefixLattice x i) := by
  intro a z ha hz
  rw [mem_realPrefixLattice] at hz ⊢
  have haz : (a : ℝ) • realEmbed d z ∈
      Submodule.span ℝ (realEmbed d '' (x '' Set.Iic i)) := by
    rw [← realEmbed_zsmul]
    exact hz
  have hinv :=
    (Submodule.span ℝ (realEmbed d '' (x '' Set.Iic i))).smul_mem
      (a : ℝ)⁻¹ haz
  simpa [smul_smul, ha] using hinv

theorem monotone_realPrefixLattice {d n : ℕ}
    (x : Fin n → (Fin d → ℤ)) : Monotone (realPrefixLattice x) := by
  intro i j hij z hz
  rw [mem_realPrefixLattice] at hz ⊢
  apply Submodule.span_mono (Set.image_mono (Set.image_mono ?_)) hz
  intro k hk
  exact hk.trans hij

theorem self_mem_realPrefixLattice {d n : ℕ}
    (x : Fin n → (Fin d → ℤ)) (i : Fin n) :
    x i ∈ realPrefixLattice x i := by
  rw [mem_realPrefixLattice]
  apply Submodule.subset_span
  exact ⟨x i, ⟨i, Set.mem_Iic.mpr le_rfl, rfl⟩, rfl⟩

section Smith

variable {ι : Type*} [Finite ι]

omit [Finite ι] in

theorem smithVector_mem_of_isSaturated (_b : Basis ι ℤ M)
    (P : Submodule ℤ M) (hP : IsSaturated P) {n : ℕ}
    (snf : Basis.SmithNormalForm P ι n) (i : Fin n) :
    snf.bM (snf.f i) ∈ P := by
  classical
  have hai : snf.a i ≠ 0 := by
    intro hai
    apply (snf.bN.ne_zero i)
    apply Subtype.ext
    simp [snf.snf i, hai]
  exact hP (snf.a i) (snf.bM (snf.f i)) hai <| by
    simpa [snf.snf i] using (snf.bN i).property

theorem exists_isCompl_of_isSaturated (b : Basis ι ℤ M)
    (P : Submodule ℤ M) (hP : IsSaturated P) :
    ∃ Q : Submodule ℤ M, IsCompl P Q := by
  classical
  let snf := P.smithNormalForm b
  let selected : Set ι := Set.range snf.2.f
  let Q : Submodule ℤ M :=
    Submodule.span ℤ (snf.2.bM '' selectedᶜ)
  have hselected :
      P = Submodule.span ℤ (snf.2.bM '' selected) := by
    apply le_antisymm
    · intro x hx
      let xp : P := ⟨x, hx⟩
      have hxp : xp ∈ Submodule.span ℤ (Set.range snf.2.bN) := by
        rw [snf.2.bN.span_eq]
        exact Submodule.mem_top
      exact Submodule.span_induction (R := ℤ) (s := Set.range snf.2.bN)
        (p := fun y _ ↦ (y : M) ∈
          Submodule.span ℤ (snf.2.bM '' selected))
        (fun y hy ↦ by
          obtain ⟨i, rfl⟩ := hy
          rw [snf.2.snf i]
          apply Submodule.smul_mem
          apply Submodule.subset_span
          exact ⟨snf.2.f i, ⟨i, rfl⟩, rfl⟩)
        (Submodule.zero_mem _)
        (fun _ _ _ _ hy hz ↦ Submodule.add_mem _ hy hz)
        (fun a _ _ hy ↦ Submodule.smul_mem _ a hy)
        hxp
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, ⟨i, rfl⟩, rfl⟩
      exact smithVector_mem_of_isSaturated b P hP snf.2 i
  refine ⟨Q, ?_⟩
  rw [hselected]
  exact snf.2.bM.linearIndependent.isCompl_span_image
    snf.2.bM.span_eq (isCompl_compl)

theorem span_image_inl_eq_of_span_comap_eq
    {P R : Submodule ℤ M} (hRP : R ≤ P)
    {κ μ : Type*} (bP : Basis κ ℤ P) (bM : Basis (κ ⊕ μ) ℤ M)
    (hext : ∀ i, bM (Sum.inl i) = (bP i : M)) (s : Set κ)
    (hspan : R.comap P.subtype = Submodule.span ℤ (bP '' s)) :
    R = Submodule.span ℤ (bM '' (Sum.inl '' s)) := by
  have himage : P.subtype '' (bP '' s) = bM '' (Sum.inl '' s) := by
    ext x
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨Sum.inl i, ⟨i, hi, rfl⟩, hext i⟩
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨bP i, ⟨i, hi, rfl⟩, (hext i).symm⟩
  calc
    R = (R.comap P.subtype).map P.subtype :=
      (Submodule.map_comap_eq_self (by
        simpa [Submodule.range_subtype] using hRP)).symm
    _ = (Submodule.span ℤ (bP '' s)).map P.subtype := by rw [hspan]
    _ = Submodule.span ℤ (P.subtype '' (bP '' s)) := by
      rw [Submodule.map_span]
    _ = Submodule.span ℤ (bM '' (Sum.inl '' s)) := by rw [himage]

theorem span_range_inl_prod_eq {P Q : Submodule ℤ M} (hPQ : IsCompl P Q)
    {κ μ : Type*}
    (bP : Basis κ ℤ P) (bQ : Basis μ ℤ Q) :
    let bM := (bP.prod bQ).map (P.prodEquivOfIsCompl Q hPQ)
    P = Submodule.span ℤ (bM '' Set.range Sum.inl) := by
  classical
  let bM := (bP.prod bQ).map (P.prodEquivOfIsCompl Q hPQ)
  apply le_antisymm
  · intro x hx
    let xp : P := ⟨x, hx⟩
    have hxp : xp ∈ Submodule.span ℤ (Set.range bP) := by
      rw [bP.span_eq]
      exact Submodule.mem_top
    exact Submodule.span_induction (R := ℤ) (s := Set.range bP)
      (p := fun y _ ↦ (y : M) ∈
        Submodule.span ℤ (bM '' Set.range Sum.inl))
      (fun y hy ↦ by
        obtain ⟨i, rfl⟩ := hy
        apply Submodule.subset_span
        refine ⟨Sum.inl i, ⟨i, rfl⟩, ?_⟩
        simp [bM])
      (Submodule.zero_mem _)
      (fun _ _ _ _ hy hz ↦ Submodule.add_mem _ hy hz)
      (fun a _ _ hy ↦ Submodule.smul_mem _ a hy)
      hxp
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simp

end Smith

universe u

theorem exists_basis_with_nested_supports_of_saturated_flag (n : ℕ) :
    ∀ {N : Type u} [AddCommGroup N] {ι : Type} [Finite ι],
      (b₀ : Basis ι ℤ N) →
      (P : Fin n → Submodule ℤ N) →
      (∀ i, IsSaturated (P i)) → Antitone P →
      ∃ (κ : Type) (_ : Fintype κ) (b : Basis κ ℤ N)
        (s : Fin n → Set κ), Antitone s ∧
          ∀ i, P i = Submodule.span ℤ (b '' s i) := by
  induction n with
  | zero =>
      intro N _ ι _ b₀ P _ _
      classical
      let := Fintype.ofFinite ι
      let b : Basis (Fin (Fintype.card ι)) ℤ N :=
        b₀.reindex (Fintype.equivFin ι)
      let s : Fin 0 → Set (Fin (Fintype.card ι)) := Fin.elim0
      exact ⟨Fin (Fintype.card ι), inferInstance, b, s,
        fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩
  | succ n ih =>
      intro N _ ι _ b₀ P hsat hanti
      classical
      let P₀ : Submodule ℤ N := P 0
      obtain ⟨p, bP₀⟩ := Submodule.basisOfPid b₀ P₀
      let tail : Fin n → Submodule ℤ P₀ :=
        fun i ↦ (P i.succ).comap P₀.subtype
      have htail_sat : ∀ i, IsSaturated (tail i) := by
        intro i
        apply (hsat i.succ).comap_subtype
        exact hanti (Fin.zero_le i.succ)
      have htail_anti : Antitone tail := by
        intro i j hij
        apply Submodule.comap_mono
        exact hanti (by simpa using hij)
      obtain ⟨κ, instκ, bP, sP, hsPanti, hbP⟩ :=
        ih (N := P₀) (ι := Fin p) bP₀ tail htail_sat htail_anti
      let : Fintype κ := instκ
      obtain ⟨Q, hP₀Q⟩ :=
        exists_isCompl_of_isSaturated b₀ P₀ (hsat 0)
      obtain ⟨m, bQ⟩ := Submodule.basisOfPid b₀ Q
      let e : (P₀ × Q) ≃ₗ[ℤ] N := P₀.prodEquivOfIsCompl Q hP₀Q
      let b : Basis (κ ⊕ Fin m) ℤ N := (bP.prod bQ).map e
      let s : Fin (n + 1) → Set (κ ⊕ Fin m) :=
        fun i ↦ Fin.cases (Set.range Sum.inl)
          (fun j ↦ Sum.inl '' sP j) i
      refine ⟨κ ⊕ Fin m, inferInstance, b, s, ?_, ?_⟩
      · intro i j hij
        obtain rfl | ⟨i', rfl⟩ := i.eq_zero_or_eq_succ
        · obtain rfl | ⟨j', rfl⟩ := j.eq_zero_or_eq_succ
          · exact fun _ hx ↦ hx
          · rintro x ⟨k, hk, rfl⟩
            exact Set.mem_range.mpr ⟨k, rfl⟩
        · obtain rfl | ⟨j', rfl⟩ := j.eq_zero_or_eq_succ
          · exact False.elim ((not_le_of_gt (Fin.succ_pos i')) hij)
          · exact Set.image_mono (hsPanti (by simpa using hij))
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact span_range_inl_prod_eq hP₀Q bP bQ
        · apply span_image_inl_eq_of_span_comap_eq
            (P := P₀) (R := P j.succ) (hanti (Fin.zero_le j.succ))
            bP b (fun k ↦ by simp [b, e]) (sP j)
          simpa [tail, P₀] using hbP j

theorem exists_basis_with_nested_supports_of_monotone_saturated_flag
    (n : ℕ) {N : Type u} [AddCommGroup N] {ι : Type} [Finite ι]
    (b₀ : Basis ι ℤ N) (P : Fin n → Submodule ℤ N)
    (hsat : ∀ i, IsSaturated (P i)) (hmono : Monotone P) :
    ∃ (κ : Type) (_ : Fintype κ) (b : Basis κ ℤ N)
      (s : Fin n → Set κ), Monotone s ∧
        ∀ i, P i = Submodule.span ℤ (b '' s i) := by
  let Prev : Fin n → Submodule ℤ N := fun i ↦ P i.rev
  have hPrev : Antitone Prev := by
    intro i j hij
    exact hmono (Fin.rev_anti hij)
  obtain ⟨κ, instκ, b, t, htanti, ht⟩ :=
    exists_basis_with_nested_supports_of_saturated_flag n b₀ Prev
      (fun i ↦ hsat i.rev) hPrev
  let s : Fin n → Set κ := fun i ↦ t i.rev
  refine ⟨κ, instκ, b, s, ?_, ?_⟩
  · intro i j hij
    exact htanti (Fin.rev_anti hij)
  · intro i
    simpa [s, Prev] using ht i.rev

theorem repr_eq_zero_of_mem_span_image {N : Type*} [AddCommGroup N]
    {κ : Type*} (b : Basis κ ℤ N) (s : Set κ) {x : N}
    (hx : x ∈ Submodule.span ℤ (b '' s)) {j : κ} (hj : j ∉ s) :
    b.repr x j = 0 := by
  have hsupp := b.repr_support_subset_of_mem_span s hx
  by_contra hne
  exact hj (hsupp (Finsupp.mem_support_iff.mpr hne))

theorem exists_basis_with_nested_supports_realPrefixLattice
    {d n : ℕ} (x : Fin n → (Fin d → ℤ)) :
    ∃ (κ : Type) (_ : Fintype κ) (b : Basis κ ℤ (Fin d → ℤ))
      (s : Fin n → Set κ), Monotone s ∧
        ∀ i, realPrefixLattice x i =
          Submodule.span ℤ (b '' s i) := by
  exact exists_basis_with_nested_supports_of_monotone_saturated_flag n
    (Pi.basisFun ℤ (Fin d)) (realPrefixLattice x)
    (isSaturated_realPrefixLattice x) (monotone_realPrefixLattice x)

theorem exists_fin_basis_with_nested_supports_realPrefixLattice
    {n : ℕ} (x : Fin n → (Fin n → ℤ)) :
    ∃ (b : Basis (Fin n) ℤ (Fin n → ℤ)) (s : Fin n → Set (Fin n)),
      Monotone s ∧
      (∀ i, realPrefixLattice x i =
        Submodule.span ℤ (b '' s i)) ∧
      ∀ i j, j ∉ s i → b.repr (x i) j = 0 := by
  classical
  obtain ⟨κ, instκ, bκ, sκ, hsmono, hs⟩ :=
    exists_basis_with_nested_supports_realPrefixLattice x
  let : Fintype κ := instκ
  let e : κ ≃ Fin n := bκ.indexEquiv (Pi.basisFun ℤ (Fin n))
  let b : Basis (Fin n) ℤ (Fin n → ℤ) := bκ.reindex e
  let s : Fin n → Set (Fin n) := fun i ↦ e '' sκ i
  have himage (i : Fin n) : b '' s i = bκ '' sκ i := by
    ext y
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, by simp [b, e]⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨e k, ⟨k, hk, rfl⟩, by simp [b, e]⟩
  have hspan (i : Fin n) : realPrefixLattice x i =
      Submodule.span ℤ (b '' s i) := by
    rw [himage]
    exact hs i
  refine ⟨b, s, ?_, hspan, ?_⟩
  · intro i j hij
    exact Set.image_mono (hsmono hij)
  · intro i j hj
    apply repr_eq_zero_of_mem_span_image b (s i)
    · rw [← hspan i]
      exact self_mem_realPrefixLattice x i
    · exact hj

theorem exists_prefix_adapted_basis_realPrefixLattice
    {n : ℕ} (x : Fin n → (Fin n → ℤ))
    (hli : LinearIndependent ℝ (fun i ↦ realEmbed n (x i))) :
    ∃ b : Basis (Fin n) ℤ (Fin n → ℤ),
      (∀ i, realPrefixLattice x i =
        Submodule.span ℤ (b '' Set.Iic i)) ∧
      (∀ i j, i < j → b.repr (x i) j = 0) ∧
      ∀ i, b.repr (x i) i ≠ 0 := by
  classical
  obtain ⟨b, s, hsmono, hspan, hzero⟩ :=
    exists_fin_basis_with_nested_supports_realPrefixLattice x
  have hpivot : ∀ i : Fin n, ∃ j : Fin n,
      j ∈ s i ∧ b.repr (x i) j ≠ 0 ∧
        ∀ hi : 0 < i.val,
          j ∉ s (⟨i.val - 1, by omega⟩ : Fin n) := by
    intro i
    by_cases hi : 0 < i.val
    · let ip : Fin n := ⟨i.val - 1, by omega⟩
      have hset : Set.Iic ip = Set.Iio i := by
        ext k
        simp only [Set.mem_Iic, Set.mem_Iio, Fin.le_iff_val_le_val,
          Fin.lt_def, ip]
        omega
      have hnot : x i ∉ realPrefixLattice x ip := by
        intro hmem
        have him := (mem_realPrefixLattice.mp hmem)
        apply hli.notMem_span_image (s := Set.Iio i) (lt_irrefl i)
        simpa [Set.image_image, Function.comp_def, hset] using him
      have hnotspan : x i ∉ Submodule.span ℤ (b '' s ip) := by
        rw [← hspan ip]
        exact hnot
      have hnsub : ¬ ((b.repr (x i)).support : Set (Fin n)) ⊆ s ip := by
        simpa [b.mem_span_image] using hnotspan
      obtain ⟨j, hjmem, hjnot⟩ := Set.not_subset.mp hnsub
      have hjne : b.repr (x i) j ≠ 0 := Finsupp.mem_support_iff.mp hjmem
      have hjcur : j ∈ s i := by
        by_contra hj
        exact hjne (hzero i j hj)
      refine ⟨j, hjcur, hjne, ?_⟩
      intro _hi
      simpa [ip] using hjnot
    · have hxne : x i ≠ 0 := by
        intro hx
        apply hli.ne_zero i
        simp [hx]
      have hrepr : b.repr (x i) ≠ 0 := by
        intro hr
        apply hxne
        apply b.repr.injective
        simpa using hr
      obtain ⟨j, hjmem⟩ := Finsupp.support_nonempty_iff.mpr hrepr
      have hjne : b.repr (x i) j ≠ 0 := Finsupp.mem_support_iff.mp hjmem
      have hjcur : j ∈ s i := by
        by_contra hj
        exact hjne (hzero i j hj)
      exact ⟨j, hjcur, hjne, fun h ↦ (hi h).elim⟩
  choose p hp_mem hp_ne hp_prev using hpivot
  have hp_injective : Function.Injective p := by
    intro i j hpij
    by_contra hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · have hjpos : 0 < j.val := lt_of_le_of_lt (Nat.zero_le _) hijlt
      let jp : Fin n := ⟨j.val - 1, by omega⟩
      have hijp : i ≤ jp := by
        apply Fin.le_iff_val_le_val.mpr
        change i.val ≤ j.val - 1
        omega
      have hpimem : p i ∈ s jp := hsmono hijp (hp_mem i)
      have hpjnot : p j ∉ s jp := by
        simpa [jp] using hp_prev j hjpos
      exact hpjnot (hpij ▸ hpimem)
    · have hipos : 0 < i.val := lt_of_le_of_lt (Nat.zero_le _) hjilt
      let ip : Fin n := ⟨i.val - 1, by omega⟩
      have hjip : j ≤ ip := by
        apply Fin.le_iff_val_le_val.mpr
        change j.val ≤ i.val - 1
        omega
      have hpjmem : p j ∈ s ip := hsmono hjip (hp_mem j)
      have hpinot : p i ∉ s ip := by
        simpa [ip] using hp_prev i hipos
      exact hpinot (hpij.symm ▸ hpjmem)
  have hp_bijective : Function.Bijective p :=
    (Fintype.bijective_iff_injective_and_card p).mpr
      ⟨hp_injective, rfl⟩
  let ep : Fin n ≃ Fin n := Equiv.ofBijective p hp_bijective
  have hs_eq (i : Fin n) : p '' Set.Iic i = s i := by
    apply Set.Subset.antisymm
    · rintro _ ⟨k, hk, rfl⟩
      exact hsmono (Set.mem_Iic.mp hk) (hp_mem k)
    · intro q hq
      obtain ⟨k, rfl⟩ := hp_bijective.2 q
      refine ⟨k, ?_, rfl⟩
      apply Set.mem_Iic.mpr
      by_contra hki
      have hik : i < k := lt_of_not_ge hki
      have hkpos : 0 < k.val := lt_of_le_of_lt (Nat.zero_le _) hik
      let kp : Fin n := ⟨k.val - 1, by omega⟩
      have hikp : i ≤ kp := by
        apply Fin.le_iff_val_le_val.mpr
        change i.val ≤ k.val - 1
        omega
      exact (hp_prev k hkpos) (hsmono hikp hq)
  let b' : Basis (Fin n) ℤ (Fin n → ℤ) := b.reindex ep.symm
  have hbimage (i : Fin n) : b' '' Set.Iic i = b '' s i := by
    rw [← hs_eq i]
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨p k, ⟨k, hk, rfl⟩, by simp [b', ep]⟩
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, by simp [b', ep]⟩
  have hspan' (i : Fin n) : realPrefixLattice x i =
      Submodule.span ℤ (b' '' Set.Iic i) := by
    rw [hbimage]
    exact hspan i
  refine ⟨b', hspan', ?_, ?_⟩
  · intro i j hij
    apply repr_eq_zero_of_mem_span_image b' (Set.Iic i)
    · rw [← hspan' i]
      exact self_mem_realPrefixLattice x i
    · exact fun hj ↦ (not_le_of_gt hij) (Set.mem_Iic.mp hj)
  · intro i
    simpa [b', ep] using hp_ne i

end Erdos3.IntegerBasisReduction.SaturatedFlag

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProperCyclicKernelBasis
namespace OAI

section

namespace Erdos3.IntegerBasisReduction.Mahler

open scoped BigOperators
open Module

noncomputable def centeredStep {n : ℕ} (r u : Fin n → ℝ) (j : Fin n) :
    Fin n → ℝ :=
  fun h ↦ r h - (round (r j / u j) : ℝ) * u h

theorem abs_centeredStep_apply_self_le {n : ℕ}
    (r u : Fin n → ℝ) (j : Fin n)
    (hdiag_ne : u j ≠ 0) (hdiag_le : |u j| ≤ 1) :
    |centeredStep r u j j| ≤ (1 : ℝ) / 2 := by
  have heq : centeredStep r u j j =
      u j * (r j / u j - (round (r j / u j) : ℝ)) := by
    rw [centeredStep]
    field_simp
  rw [heq, abs_mul]
  calc
    |u j| * |r j / u j - (round (r j / u j) : ℝ)| ≤
        1 * ((1 : ℝ) / 2) :=
      mul_le_mul hdiag_le (abs_sub_round (r j / u j))
        (abs_nonneg _) (by positivity)
    _ = (1 : ℝ) / 2 := one_mul _

theorem exists_integerCombination_abs_le_half : ∀ {n : ℕ}
    (u : Fin n → Fin n → ℝ),
    (∀ j h, j < h → u j h = 0) →
    (∀ j, u j j ≠ 0) →
    (∀ j, |u j j| ≤ (1 : ℝ)) →
    ∀ r : Fin n → ℝ,
      ∃ t : Fin n → ℤ,
        ∀ h, |r h + ∑ j, (t j : ℝ) * u j h| ≤ (1 : ℝ) / 2 := by
  intro n
  induction n with
  | zero =>
      intro u _htri _hne _hle r
      refine ⟨fun i ↦ Fin.elim0 i, ?_⟩
      intro h
      exact Fin.elim0 h
  | succ n ih =>
      intro u htri hne hle r
      let last : Fin (n + 1) := Fin.last n
      let q : ℤ := -round (r last / u last last)
      let rHead : Fin n → ℝ := fun h ↦
        r h.castSucc + (q : ℝ) * u last h.castSucc
      let uHead : Fin n → Fin n → ℝ := fun j h ↦
        u j.castSucc h.castSucc
      have htriHead : ∀ j h, j < h → uHead j h = 0 := by
        intro j h hjh
        exact htri j.castSucc h.castSucc (Fin.castSucc_lt_castSucc_iff.mpr hjh)
      have hneHead : ∀ j, uHead j j ≠ 0 := fun j ↦ hne j.castSucc
      have hleHead : ∀ j, |uHead j j| ≤ (1 : ℝ) := fun j ↦ hle j.castSucc
      obtain ⟨tHead, htHead⟩ := ih uHead htriHead hneHead hleHead rHead
      let t : Fin (n + 1) → ℤ := Fin.lastCases q tHead
      refine ⟨t, ?_⟩
      intro h
      refine Fin.lastCases ?_ (fun h ↦ ?_) h
      · have hzero :
            ∑ j : Fin n, (t j.castSucc : ℝ) * u j.castSucc last = 0 := by
          apply Finset.sum_eq_zero
          intro j _hj
          rw [htri j.castSucc last (Fin.castSucc_lt_last j)]
          simp
        rw [Fin.sum_univ_castSucc, hzero, zero_add]
        have hstep := abs_centeredStep_apply_self_le
          r (u last) last (hne last) (hle last)
        simpa [t, q, last, centeredStep, sub_eq_add_neg] using hstep
      · have hh := htHead h
        simpa [Fin.sum_univ_castSucc, t, rHead, uHead, q,
          add_assoc, add_comm, add_left_comm] using hh

noncomputable def basisOfUpperTriangularUnits {n : ℕ} {M : Type*}
    [AddCommGroup M] (b : Basis (Fin n) ℤ M)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hupper : A.IsUpperTriangular) (hdiag : ∀ i, IsUnit (A i i)) :
    Basis (Fin n) ℤ M := by
  have hdet : IsUnit A.det := by
    rw [Matrix.det_of_isUpperTriangular hupper]
    exact IsUnit.prod_univ_iff.mpr hdiag
  exact b.map (A.toLinearEquiv b hdet)

theorem basisOfUpperTriangularUnits_apply {n : ℕ} {M : Type*}
    [AddCommGroup M] (b : Basis (Fin n) ℤ M)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hupper : A.IsUpperTriangular) (hdiag : ∀ i, IsUnit (A i i))
    (i : Fin n) :
    basisOfUpperTriangularUnits b A hupper hdiag i = ∑ j, A j i • b j := by
  simp [basisOfUpperTriangularUnits, Matrix.toLinearEquiv_apply,
    Matrix.toLin_self]

end Erdos3.IntegerBasisReduction.Mahler

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRowInterpolationMixture
namespace OAI

section

namespace Erdos3

def IsIntegerMassInterpolation (K : ℝ) (p : PMF ℤ) (B L : ℝ) (f : ℝ → ℝ) : Prop :=
  (∀ k : ℤ, f ((k : ℝ) / K) = K * (p k).toReal) ∧
  (∀ x, 0 ≤ f x ∧ f x ≤ B) ∧
  (∀ x y, |f x - f y| ≤ L * |x - y|)

theorem IsIntegerMassInterpolation.lipschitz {K B L : ℝ} {p : PMF ℤ} {f : ℝ → ℝ}
    (h : IsIntegerMassInterpolation K p B L f) (hL : 0 ≤ L) :
    LipschitzWith (Real.toNNReal L) f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq, Real.coe_toNNReal _ hL] using h.2.2 x y

theorem IsIntegerMassInterpolation.mono {K B L B' L' : ℝ} {p : PMF ℤ} {f : ℝ → ℝ}
    (h : IsIntegerMassInterpolation K p B L f) (hB : B ≤ B') (hL : L ≤ L') :
    IsIntegerMassInterpolation K p B' L' f :=
  ⟨h.1, fun x => ⟨(h.2.1 x).1, (h.2.1 x).2.trans hB⟩,
    fun x y => (h.2.2 x y).trans (mul_le_mul_of_nonneg_right hL (abs_nonneg _))⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealFiniteZeroExtension
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem expect_finset_subtype {X : Type*} (S : Finset X) (f : X → ℂ) :
    (𝔼 x : S, f x.val) = 𝔼 x ∈ S, f x := by
  rw [Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, Fintype.card_coe,
    Finset.sum_coe_sort]

end Erdos3

end

section

namespace Erdos3

open scoped Classical

noncomputable def realZeroExtendFinset {X : Type*} (S : Finset X) (f : X → ℝ) (x : X) : ℝ :=
  if x ∈ S then f x else 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CRTProgressionVanishing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def IntegerVectorAPFree {J : Type*} (A : Set (J → ℤ)) (k : ℕ) : Prop :=
  ∀ a d : J → ℤ, d ≠ 0 → ∃ i : Fin k, a + (i.val : ℤ) • d ∉ A

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.LowDensityAmplification
namespace OAI

section

namespace Erdos3

open Filter

def LowDensityThreshold (H a : ℝ) : Prop := 0 < a ∧ H ^ 2 * a ≤ 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MixedArrayIntegerImage
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix

variable {D I J O Z : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}

noncomputable def mixedArrayIntegerImage (A : Matrix O J ℤ)
    (x : (I → J → ℝ) × (Z → J → ℤ)) : (I → O → ℝ) × (Z → O → ℤ) :=
  (fun i => (A.map (Int.cast : ℤ → ℝ)) *ᵥ x.1 i, fun z => A *ᵥ x.2 z)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonRefilteredFactorization
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*}
  [Fintype σ]
  [DecidableEq σ]
  [LieRing L]
  [LieAlgebra ℚ L]
  {s d : ℕ}
  {bound : σ → ℕ}

noncomputable def additiveTripleGeometryBudget (p : ℝ) : ℝ :=
  ((p + 6) ^ 2 + ((p + 4) ^ 2 + 2) ^ 63 + 6) ^ 11

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.MultilinearityBudgets
namespace OAI

section

namespace Erdos3.MultilinearityBudget

open RationalFilteredNilmanifold.MultidegreeStructure
open scoped NNReal

noncomputable def coordinates (p : ℝ) : ℝ := ((p + 4) ^ 2 + 2) ^ 63 + 3

noncomputable def ambient (p : ℝ) : ℝ := p + additiveTripleGeometryBudget p + coordinates p

noncomputable def quotient (p : ℝ) : ℝ := (ambient p + 3) ^ 11

noncomputable def observable (C : ℕ) (p : ℝ) : ℝ := p + (p + C) ^ C + (ambient p + 3) ^ 2 + 2

noncomputable def reconstruction (C : ℕ) (p : ℝ) : ℝ := ambient p + quotient p + observable C p + 1

noncomputable def total (C N : ℕ) (p : ℝ) : ℝ := quotient p + (reconstruction C p + N) ^ N + 4

theorem ambient_bounds {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ ambient p ∧ p ≤ ambient p ∧ additiveTripleGeometryBudget p ≤ ambient p ∧
      coordinates p ≤ ambient p := by
  have hG : 0 ≤ additiveTripleGeometryBudget p := by unfold additiveTripleGeometryBudget; positivity
  have hC : 0 ≤ coordinates p := by unfold coordinates; positivity
  refine ⟨add_nonneg (add_nonneg hp hG) hC, ?_, ?_, ?_⟩
  · exact (le_add_of_nonneg_right hG).trans (le_add_of_nonneg_right hC)
  · exact (le_add_of_nonneg_left hp).trans (le_add_of_nonneg_right hC)
  · exact le_add_of_nonneg_left (add_nonneg hp hG)

theorem quotient_bounds {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ quotient p ∧ ambient p ≤ quotient p ∧ (ambient p + 3) ^ 5 ≤ quotient p := by
  have hR := (ambient_bounds hp).1
  have hbase : 1 ≤ ambient p + 3 :=
    (by norm_num : (1 : ℝ) ≤ 3).trans (le_add_of_nonneg_left hR)
  have hpow : ambient p + 3 ≤ (ambient p + 3) ^ 11 := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (by decide : 1 ≤ 11)
  exact ⟨pow_nonneg (add_nonneg hR (by norm_num)) _,
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 3)).trans hpow,
    pow_le_pow_right₀ hbase (by decide : 5 ≤ 11)⟩

theorem observable_nonneg (C : ℕ) {p : ℝ} (hp : 0 ≤ p) : 0 ≤ observable C p := by
  unfold observable
  positivity

theorem reconstruction_bounds (C : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ reconstruction C p ∧ ambient p ≤ reconstruction C p ∧
      quotient p + 1 ≤ reconstruction C p ∧ observable C p ≤ reconstruction C p := by
  have hR := (ambient_bounds hp).1
  have hQ := (quotient_bounds hp).1
  have hO := observable_nonneg C hp
  refine ⟨add_nonneg (add_nonneg (add_nonneg hR hQ) hO) zero_le_one, ?_, ?_, ?_⟩
  · exact ((le_add_of_nonneg_right hQ).trans (le_add_of_nonneg_right hO)).trans
      (le_add_of_nonneg_right zero_le_one)
  · have h : quotient p ≤ ambient p + quotient p + observable C p :=
      (le_add_of_nonneg_left hR).trans (le_add_of_nonneg_right hO)
    exact add_le_add h (le_refl 1)
  · exact (le_add_of_nonneg_left (add_nonneg hR hQ)).trans (le_add_of_nonneg_right zero_le_one)

theorem total_bounds (C N : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    quotient p ≤ total C N p ∧ (reconstruction C p + N) ^ N + 4 ≤ total C N p := by
  have hQ := (quotient_bounds hp).1
  have hB := (reconstruction_bounds C hp).1
  have hN : 0 ≤ (reconstruction C p + N) ^ N := pow_nonneg (add_nonneg hB (Nat.cast_nonneg N)) _
  refine ⟨(le_add_of_nonneg_right hN).trans (le_add_of_nonneg_right (by norm_num)), ?_⟩
  exact add_le_add (show (reconstruction C p + N) ^ N ≤ quotient p + (reconstruction C p + N) ^ N
    from le_add_of_nonneg_left hQ) (le_refl 4)

theorem observable_bound (C : ℕ) (p : ℝ) (K A : ℝ≥0)
    (hK : (K : ℝ) ≤ Real.exp p) (hA : (A : ℝ) ≤ Real.exp ((p + C) ^ C)) :
    (3 : ℝ) * (K * (A * Real.exp ((ambient p + 3) ^ 2))) ≤ Real.exp (observable C p) := by
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hP : 0 ≤ Real.exp ((ambient p + 3) ^ 2) := (Real.exp_pos _).le
  have h := mul_le_mul h3
    (mul_le_mul hK (mul_le_mul_of_nonneg_right hA hP)
      (mul_nonneg A.coe_nonneg hP) (Real.exp_pos p).le)
    (mul_nonneg K.coe_nonneg (mul_nonneg A.coe_nonneg hP)) (Real.exp_pos 2).le
  simpa only [observable, Real.exp_add, mul_assoc, mul_comm, mul_left_comm] using h

end Erdos3.MultilinearityBudget

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteAssignmentPartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

abbrev MissingAssignment (s : ℕ) := {v : Fin s → Fin s // ¬Function.Surjective v}

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelProjectionPresentPivotIdeal
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct Classical

def KernelProjectionPresentPivot {J : Type*} {r : ℕ}
    (code : Fin r → Option J) := {i : Fin r // ∃ j, code i = some j}

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestComplement
namespace OAI

section

namespace Erdos3

def raisedNiltestBudget (p : ℝ) : ℝ := p + (p + 2) ^ 2 + 3

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealifiedPairCoordinates
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [AddCommGroup L] [Module ℚ L]

noncomputable def realPairEquiv :
    (ℝ ⊗[ℚ] (L × L)) ≃ₗ[ℝ] ((ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L)) :=
  TensorProduct.prodRight ℚ ℝ ℝ L L

@[simp] theorem realPairEquiv_tmul (r : ℝ) (x : L × L) :
    realPairEquiv (r ⊗ₜ[ℚ] x) = (r ⊗ₜ[ℚ] x.1, r ⊗ₜ[ℚ] x.2) := rfl

theorem realPairEquiv_first (x : ℝ ⊗[ℚ] (L × L)) :
    (realPairEquiv x).1 = (LinearMap.fst ℚ L L).baseChange ℝ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, Prod.fst_add, hx, hy]

theorem realPairEquiv_second (x : ℝ ⊗[ℚ] (L × L)) :
    (realPairEquiv x).2 = (LinearMap.snd ℚ L L).baseChange ℝ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, Prod.snd_add, hx, hy]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPositivePolynomialEvaluation
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ}

abbrev BoxedDegreeIndex (bound : σ → ℕ) := ∀ i, Fin (bound i + 1)

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeTernaryCoordinate
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ I : Type*} [DecidableEq σ]

def coordinateReplaceIndex (i : σ) (j : Option σ) : Option σ :=
  if j = some i then none else j

def coordinateReplaceInput (i : σ) (x : Option σ → ℤ) : Option σ → ℤ :=
  fun j => x (coordinateReplaceIndex i j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerIntervalOverlap
namespace OAI

section

namespace Erdos3

theorem integerIco_card (c len : ℕ) :
    (Finset.Ico (c : ℤ) (c + len)).card = len := by
  simp

theorem integerIco_subset_range (c len N : ℕ) (hN : c + len ≤ N) :
    Finset.Ico (c : ℤ) (c + len) ⊆ Finset.Ico (0 : ℤ) N := by
  intro x hx
  obtain ⟨hx₀, hx₁⟩ := Finset.mem_Ico.mp hx
  exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeLocalPivotVerticalPartners
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exp_scaled_norm_le_one {b : ℝ} {z : ℂ} (hz : ‖z‖ ≤ Real.exp b) :
    ‖(Real.exp (-b) : ℂ) * z‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-b) * Real.exp b := mul_le_mul_of_nonneg_left hz (Real.exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OriginalMixedRootEquivalence
namespace OAI

section

namespace Erdos3

open scoped BigOperators

abbrev MixedNonconstantCorner (s : ℕ) := {v : Fin (s + 3) → Fin 2 // v ≠ fun _ => 0}

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

def mixedCornerWeight {s : ℕ} (v : Fin (s + 3) → Fin 2) : ℕ := ∑ k, (v k).val

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

abbrev MixedWeightCorner (s k : ℕ) :=
  {v : Fin (s + 3) → Fin 2 // mixedCornerWeight v = k}

end Erdos3

end

section

namespace Erdos3

abbrev MixedWeightBlock (s : ℕ) := (k : Fin (s + 3)) × MixedWeightCorner s (k.val + 1)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

abbrev MixedHigherCorner (s : ℕ) := (k : Fin (s + 2)) × MixedWeightCorner s (k.val + 2)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

abbrev MixedMiddleCorner (s : ℕ) := (k : Fin (s + 1)) × MixedWeightCorner s (k.val + 2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MarkedPolynomialGenerators
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators

noncomputable def markedParameterExponents (σ : Type*) [Fintype σ] (s : ℕ) : Finset (σ →₀ ℕ) :=
  (Finsupp.finite_of_nat_weight_le (fun _ : σ => 1) (by simp) s).toFinset

@[simp] theorem mem_markedParameterExponents {σ : Type*} [Fintype σ] (s : ℕ) (α : σ →₀ ℕ) :
    α ∈ markedParameterExponents σ s ↔ Finsupp.weight (fun _ : σ => 1) α ≤ s := by
  classical
  simp only [markedParameterExponents, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductiveFrozenLocalMajorFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

variable {V : Type*} (Long : V → Prop) [DecidablePred Long]

def frozenLongExtension (fixed : V → ℕ) (x : {i // Long i} → ℤ) : V → ℤ :=
  fun i => if hi : Long i then x ⟨i, hi⟩ else (fixed i : ℤ)

@[simp] theorem frozenLongExtension_long (fixed : V → ℕ)
    (x : {i // Long i} → ℤ) (i : {i // Long i}) :
    frozenLongExtension Long fixed x i.val = x i := by
  simp [frozenLongExtension, i.property]

theorem frozenLongExtension_injective (fixed : V → ℕ) :
    Function.Injective (frozenLongExtension Long fixed) := by
  intro x y h
  funext i
  simpa only [frozenLongExtension_long] using congrFun h i.val

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineIntervalNormalizedBounds
namespace OAI

section

namespace Erdos3

theorem affineInterval_normalized_bounds
    {L H step : ℕ} {start : ℤ}
    (hL : 0 < L) (hH : 2 ≤ H) (hstep : 0 < step)
    (hinside : ∀ t : Fin H, 0 ≤ start + step * (t.val : ℤ) ∧
      start + step * (t.val : ℤ) < L) :
    0 ≤ (start : ℝ) / L ∧
      0 < (step : ℝ) * ((H - 1 : ℕ) : ℝ) / L ∧
      (start : ℝ) / L + (step : ℝ) * ((H - 1 : ℕ) : ℝ) / L < 1 ∧
      (step : ℝ) * ((H - 1 : ℕ) : ℝ) / L ≤ 1 := by
  have hHpos : 0 < H := by omega
  have hlast : H - 1 < H := Nat.sub_lt hHpos (by norm_num)
  have hstartZ : 0 ≤ start := by
    simpa only [Nat.cast_zero, mul_zero, add_zero] using (hinside ⟨0, hHpos⟩).1
  have hendZ := (hinside ⟨H - 1, hlast⟩).2
  have hstart : (0 : ℝ) ≤ start := by exact_mod_cast hstartZ
  have hend : (start : ℝ) + (step : ℝ) * ((H - 1 : ℕ) : ℝ) < L := by
    exact_mod_cast hendZ
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hstepreal : (0 : ℝ) < step := by exact_mod_cast hstep
  have hHreal : (0 : ℝ) < ((H - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < H - 1 by omega)
  have hlower := div_nonneg hstart hLreal.le
  have hwidth := div_pos (mul_pos hstepreal hHreal) hLreal
  have hsum : (start : ℝ) / L + (step : ℝ) * ((H - 1 : ℕ) : ℝ) / L < 1 := by
    rw [← add_div]
    exact (div_lt_one hLreal).mpr hend
  exact ⟨hlower, hwidth, hsum, by linarith⟩

end Erdos3

end

end OAI
end


