-- Prove2me | Definitions.Def_OAIE3v2B249
-- name    : OAIE3v2B249
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T05:20:06.292084+00:00
-- url     : https://prove2.me/theorems/42b8d075-d457-4655-b12a-5e60902d9d8d
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 254 of 311
-- statement:
--   Definitions bundle 254 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B238`, `OAIE3v2B239`, `OAIE3v2B240`, `OAIE3v2B241` of this split.
--
--   Modules: `Estimates/CommonDependentCoveredModel.lean`, `Estimates/CommonDependentIntegralModel.lean`, `Estimates/CommonFreeSunflower.lean`, `Estimates/FreeCorrelationRelationRefinement.lean`, `Estimates/MixedAnchorExpansion.lean`, `Estimates/MixedPermutationTensor.lean`, `Estimates/NativeMixedSeparatedFamily.lean`, `Estimates/OriginalDiagonalComparison.lean`, `Estimates/SharedFreeComparisonLift.lean`, `Estimates/SharedFreeFrozenComparison.lean`, `Estimates/SharedFreeLowerFactorization.lean`, `Fourier/CommonDependentWordFrequency.lean`, `Geometry/NativeMixedCoordinateSlices.lean`, `Lattices/ActualFixedSpatialGoodPrimeDeletion.lean`, `Linear/CommonFreeSpanBounds.lean`, `Linear/MixedSumKernelCorrelation.lean`, `Linear/SharedFreeComparisonKernel.lean`, `Polynomial/LocalPhaseMarkedObservable.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B238
import Definitions.Def_OAIE3v2B239
import Definitions.Def_OAIE3v2B240
import Definitions.Def_OAIE3v2B241

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonFreeSunflower
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem coefficient_four_frequency (n : ℕ) (d : Fin n → Fin (s + 1))
    (a : FreeMagma (Fin n)) (hd : lieTreeWeight (fun j => (d j).val) a = s)
    (hr : a.length = r) (v : Fin n → Fin 4 → W.L)
    (hv : ∀ j, v j ∈ D.coefficientFourSpace (d j)) :
    fourFunctionDifference (fun x => W.vertical.frequency (lieTreeEval x a)) v = 0 := by
  classical
  have hlift (j : Fin n) : ∃ w : W.rank.filtration.fourHorizontalLayer (d j).val,
      W.rank.filtration.fourHorizontalMap (d j).val w ∈ D.horizontal (d j) ∧ w.val = v j :=
    hv j
  choose w hw he using hlift
  have hvalue (k : Fin 4) :
      W.rank.filtration.horizontalTreeValue (fun j => (d j).val) a
          (fun j => W.rank.filtration.fourHorizontalMap (d j).val (w j) k) =
        lieTreeEval (fun j => v j k) a := by
    let u (j : Fin n) : W.rank.filtration.layer (d j).val 1 :=
      ⟨(w j).val k, (W.rank.filtration.mem_fourHorizontalLayer _ _).mp (w j).property k⟩
    change W.rank.filtration.horizontalTreeValue (fun j => (d j).val) a
      (fun j => W.rank.filtration.higherHorizontalMk (d j).val (u j)) = _
    rw [W.rank.filtration.horizontalTreeValue_mk _ a hd hr u]
    congr 1
    funext j
    exact congrFun (he j) k
  have h := D.horizontal_frequency n d a hd hr
    (fun j => W.rank.filtration.fourHorizontalMap (d j).val (w j)) hw
  simpa only [fourFunctionDifference, hvalue] using h

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.freeEvaluation_commonFreeSpan (d : Fin s) :
    (D.commonFreeSpan d).map (B.freeEvaluation D).toLinearMap =
      D.commonCoefficientSpace ⟨d.val + 1, by omega⟩ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := (B.commonFreeLift_range D d).ge hy
    change B.freeEvaluation D (B.commonFreeLift D d z) ∈ _
    rw [B.freeEvaluation_commonFreeLift]
    exact z.property
  · intro hx
    refine ⟨B.commonFreeLift D d ⟨x, hx⟩,
      (B.commonFreeLift_range D d).le ⟨⟨x, hx⟩, rfl⟩, ?_⟩
    exact B.freeEvaluation_commonFreeLift D d ⟨x, hx⟩

theorem CoefficientBases.freeEvaluation_dependentFreeSpan (d : Fin s) :
    (D.dependentFreeSpan d).map (B.freeEvaluation D).toLinearMap =
      D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := (B.dependentFreeLift_range D d).ge hy
    change B.freeEvaluation D (B.dependentFreeLift D d z) ∈ _
    rw [B.freeEvaluation_dependentFreeLift]
    exact z.property
  · intro hx
    refine ⟨B.dependentFreeLift D d ⟨x, hx⟩,
      (B.dependentFreeLift_range D d).le ⟨⟨x, hx⟩, rfl⟩, ?_⟩
    exact B.freeEvaluation_dependentFreeLift D d ⟨x, hx⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonFreeSpanBounds
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

variable {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.freeEvaluation_coefficientFreeSpan (d : Fin s) :
    (D.coefficientFreeSpan d).map (B.freeEvaluation D).toLinearMap =
      D.commonCoefficientSpace ⟨d.val + 1, by omega⟩ := by
  rw [coefficientFreeSpan, Submodule.map_sup, B.freeEvaluation_commonFreeSpan D,
    B.freeEvaluation_dependentFreeSpan D]
  exact sup_eq_left.mpr (D.dependentCoefficientSpace_le_common _)

theorem CoefficientBases.combined_free_sunflower (n : ℕ) (d : Fin n → Fin s)
    (a : FreeMagma (Fin n)) (hd : lieTreeWeight (fun i => (d i).val + 1) a = s)
    (hr : a.length = r) (v : Fin n → D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ D.coefficientFreeSpan (d i))
    (j k : Fin n) (hjk : j ≠ k) (hj : j ∈ lieTreeSupport a) (hk : k ∈ lieTreeSupport a)
    (hvj : v j ∈ D.dependentFreeSpan (d j)) (hvk : v k ∈ D.dependentFreeSpan (d k)) :
    B.freeFrequency D (lieTreeEval v a) = 0 := by
  have h := D.coefficient_sunflower n (fun i => ⟨(d i).val + 1, by omega⟩) a hd hr
    (fun i => B.freeEvaluation D (v i))
    (fun i => (B.freeEvaluation_coefficientFreeSpan D (d i)).le ⟨v i, hv i, rfl⟩)
    j k hjk hj hk
    ((B.freeEvaluation_dependentFreeSpan D (d j)).le ⟨v j, hvj, rfl⟩)
    ((B.freeEvaluation_dependentFreeSpan D (d k)).le ⟨v k, hvk, rfl⟩)
  change W.vertical.frequency (B.freeEvaluation D (lieTreeEval v a)) = 0
  rw [map_lieTreeEval]
  exact h

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreeCorrelationRelationRefinement
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.finite_combined_free_sunflower {J : Type*} [Fintype J]
    (d : J → Fin s) (a : FreeMagma J)
    (hd : lieTreeWeight (fun i => (d i).val + 1) a = s) (hr : a.length = r)
    (v : J → D.CoefficientFreeLieAlgebra) (hv : ∀ i, v i ∈ D.coefficientFreeSpan (d i))
    (i j : J) (hij : i ≠ j) (hi : i ∈ lieTreeSupport a) (hj : j ∈ lieTreeSupport a)
    (hvi : v i ∈ D.dependentFreeSpan (d i)) (hvj : v j ∈ D.dependentFreeSpan (d j)) :
    B.freeFrequency D (lieTreeEval v a) = 0 := by
  classical
  let e := Fintype.equivFin J
  have hweight : lieTreeWeight (fun k => (d (e.symm k)).val + 1) (FreeMagma.map e a) = s := by
    rw [lieTreeWeight_relabel]
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using hd
  have hsupp (k : J) (hk : k ∈ lieTreeSupport a) : e k ∈ lieTreeSupport (FreeMagma.map e a) := by
    rw [lieTreeSupport_relabel]
    exact ⟨k, hk, rfl⟩
  have h := B.combined_free_sunflower D (Fintype.card J) (fun k => d (e.symm k))
    (FreeMagma.map e a) hweight ((lieTreeLength_relabel e a).trans hr)
    (fun k => v (e.symm k)) (fun k => hv (e.symm k)) (e i) (e j)
    (fun h => hij (e.injective h)) (hsupp i hi) (hsupp j hj)
    (by simpa only [Equiv.symm_apply_apply] using hvi)
    (by simpa only [Equiv.symm_apply_apply] using hvj)
  simpa only [lieTreeEval_relabel, Function.comp_def, Equiv.symm_apply_apply] using h

theorem CoefficientBases.exists_free_tree_linearization {J : Type*}
    (d : J → Fin s) (a : FreeMagma J)
    (hd : lieTreeWeight (fun i => (d i).val + 1) a = s) (hr : a.length = r)
    (x : J → D.CoefficientFreeLieAlgebra) (hx : ∀ i, x i ∈ D.coefficientFreeSpan (d i)) :
    ∃ A : (∀ i, D.dependentFreeSpan (d i)) →ₗ[ℚ] ℚ, ∀ y : ∀ i, D.dependentFreeSpan (d i),
      B.freeFrequency D (lieTreeEval (fun i => x i + (y i : D.CoefficientFreeLieAlgebra)) a) =
        B.freeFrequency D (lieTreeEval x a) + A y := by
  apply exists_linear_lieTree_expansion (B.freeFrequency D)
    (fun i => D.coefficientFreeSpan (d i)) (fun i => D.dependentFreeSpan (d i))
    (fun i => D.dependentFreeSpan_le_coefficientFreeSpan (d i)) a x hx
  intro v hv i j hij hi hj
  exact B.finite_combined_free_sunflower D (fun k => d (lieTreeOccurrenceLabel a k))
    (lieTreeOccurrenceTree a)
    ((lieTreeOccurrenceTree_weight (fun k => (d k).val + 1) a).trans hd)
    ((lieTreeOccurrenceTree_length a).trans hr) v hv i j hij
    (by rw [lieTreeOccurrenceTree_support]; trivial)
    (by rw [lieTreeOccurrenceTree_support]; trivial) hi hj

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.free_refined_four_identity {J : Type*}
    (d : J → Fin s) (a : FreeMagma J)
    (hd : lieTreeWeight (fun i => (d i).val + 1) a = s) (hr : a.length = r)
    (K : J → Submodule ℚ (Fin 4 → D.CoefficientFreeLieAlgebra))
    (hK : ∀ v, (∀ i, v i ∈ K i) →
      fourFunctionDifference (fun x => B.freeFrequency D (lieTreeEval x a)) v = 0)
    (v : J → Fin 4 → D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ fourRefinedRelation (D.coefficientFreeSpan (d i))
      (D.dependentFreeSpan (d i)) (K i)) :
    fourFunctionDifference (fun x => B.freeFrequency D (lieTreeEval x a)) v = 0 :=
  four_refined_affine_identity _ _ _
    (fun x hx => B.exists_free_tree_linearization D d a hd hr x hx) K hK v hv

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

theorem CoefficientBases.correlation_four_frequency
    (hfreq : V.frequency = B.freeFrequency D) (n : ℕ) (d : Fin n → Fin s)
    (a : FreeMagma (Fin n)) (hd : lieTreeWeight (fun i => (d i).val + 1) a = s)
    (hr : a.length = r) (v : Fin n → Fin 4 → D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ D'.coefficientFourSpace ⟨(d i).val + 1, by omega⟩) :
    fourFunctionDifference (fun x => B.freeFrequency D (lieTreeEval x a)) v = 0 := by
  have h := D'.coefficient_four_frequency n (fun i => ⟨(d i).val + 1, by omega⟩)
    a hd hr v hv
  change fourFunctionDifference (fun x => V.frequency (lieTreeEval x a)) v = 0 at h
  simpa only [hfreq] using h

theorem CoefficientBases.correlation_refined_four_identity
    (hfreq : V.frequency = B.freeFrequency D) (n : ℕ) (d : Fin n → Fin s)
    (a : FreeMagma (Fin n)) (hd : lieTreeWeight (fun i => (d i).val + 1) a = s)
    (hr : a.length = r) (v : Fin n → Fin 4 → D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ fourRefinedRelation (D.coefficientFreeSpan (d i))
      (D.dependentFreeSpan (d i)) (D'.coefficientFourSpace ⟨(d i).val + 1, by omega⟩)) :
    fourFunctionDifference (fun x => B.freeFrequency D (lieTreeEval x a)) v = 0 :=
  B.free_refined_four_identity D d a hd hr _
    (B.correlation_four_frequency D E T hbQ hT V g hg D' hfreq n d a hd hr) v hv

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CommonDependentWordFrequency
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.dependent_word_frequency_zero (a : FreeMagma D.CoefficientAlphabet)
    (hd : lieTreeWeight D.coefficientWeight a = s) (hr : a.length = r)
    (ha : 2 ≤ lieTreeMarkedCount D.coefficientIsDependent a) :
    B.freeFrequency D (lieTreeEval D.coefficientFreeGenerator a) = 0 := by
  obtain ⟨i, j, hij, hi, hj⟩ := exists_two_marked_occurrences D.coefficientIsDependent a ha
  have hweight :
      lieTreeWeight (fun k => (D.coefficientLayerIndex (lieTreeOccurrenceLabel a k)).val + 1)
        (lieTreeOccurrenceTree a) = s := by
    simp only [← D.coefficientWeight_eq_layerIndex]
    exact (lieTreeOccurrenceTree_weight D.coefficientWeight a).trans hd
  have h := B.finite_combined_free_sunflower D
    (fun k => D.coefficientLayerIndex (lieTreeOccurrenceLabel a k))
    (lieTreeOccurrenceTree a) hweight ((lieTreeOccurrenceTree_length a).trans hr)
    (D.coefficientFreeGenerator ∘ lieTreeOccurrenceLabel a)
    (fun k => D.coefficientFreeGenerator_mem_combined (lieTreeOccurrenceLabel a k))
    i j hij (by rw [lieTreeOccurrenceTree_support]; trivial)
    (by rw [lieTreeOccurrenceTree_support]; trivial)
    (D.coefficientFreeGenerator_mem_dependent _ hi)
    (D.coefficientFreeGenerator_mem_dependent _ hj)
  rwa [lieTreeOccurrenceTree_eval] at h

theorem CoefficientBases.dependentWordLayer_top_le_ker :
    D.dependentWordLayer s 2 r ≤ (B.freeFrequency D).ker :=
  markedLieSpan_top_le_ker D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientFreeGenerator_mem_layer
    2 (B.freeFrequency D) (B.dependent_word_frequency_zero D)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonDependentIntegralModel
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem top_inter_dependentWordIdeal (k : ℕ) :
    D.coefficientFreeFiltration.layer s r ⊓ (D.dependentWordIdeal 0 k 0).toSubmodule =
      D.dependentWordLayer s k r :=
  FreeDegreeRankLieAlgebra.topLayer_inter_markedIdeal D.CoefficientAlphabet s r D.coefficientWeight
    D.coefficientWeight_pos D.coefficientIsDependent W.rank.filtration.rank_le_degree k

variable {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.top_inter_dependentWordIdeal_le_ker :
    D.coefficientFreeFiltration.layer s r ⊓ (D.dependentWordIdeal 0 2 0).toSubmodule ≤
      (B.freeFrequency D).ker := by
  rw [D.top_inter_dependentWordIdeal]
  exact B.dependentWordLayer_top_le_ker D

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

noncomputable def dependentQuotientFiltration : DegreeRankLieFiltration D.DependentQuotient s r :=
  D.coefficientFreeFiltration.quotientLie (D.dependentWordIdeal 0 2 0)
    D.coefficientFreeFiltration.rank_le_degree (by
      rw [D.coefficientFreeFiltration.terminal]
      exact bot_le)

theorem dependentQuotientMap_mem_layer {d i : ℕ} {x : D.CoefficientFreeLieAlgebra}
    (hx : x ∈ D.coefficientFreeFiltration.layer d i) :
    D.dependentQuotientMap x ∈ D.dependentQuotientFiltration.layer d i := ⟨x, hx, rfl⟩

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_uniform_dependentQuotient_comparison (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p q P M Q : ℝ}
      {W : NativeDegreeRankFamily s (r + 1) (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P) (B : D.CoefficientBases M)
      {d e : ℕ} (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s d)
      (F : RationalFilteredNilmanifold D.DependentQuotient s e)
      (T : E.DegreeRankStructure (r + 1)) (S : F.DegreeRankStructure (r + 1))
      [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ] D.DependentQuotient)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.DependentQuotient)]
      [T2Space (ℝ ⊗[ℚ] D.DependentQuotient)]
      (I J σ : Type) [Fintype I] [Fintype J]
      (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) I Q)
      (U : F.UnitVerticalObservable (S.realSubgroup s (r + 1)) J Q)
      (hmap : E.lattice ≤ F.lattice.comap (mapOfSteps
        (hL := E.filtration.lowerCentralSeries_eq_bot)
        (hM := F.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap)),
      T.filtration = D.coefficientFreeFiltration →
      S.filtration = D.dependentQuotientFiltration →
      0 ≤ Q → T.ComplexityLE Q → S.ComplexityLE Q →
      (∀ i j, rationalLogHeight (F.basis.repr (D.dependentQuotientMap (E.basis j)) i) ≤ Q) →
      V.frequency = B.freeFrequency D →
      (∀ x ∈ D.coefficientFreeFiltration.layer s (r + 1),
        U.frequency (D.dependentQuotientMap x) = B.freeFrequency D x) →
      ∀ w : σ → ℕ,
        E.HasUniformLowerRankUnitFamily T
          (mapDifferenceObservable V U D.dependentQuotientMap hmap) w ((Q + C) ^ C) := by
  obtain ⟨C, hC, hcomparison⟩ := exists_uniform_lower_rank_map_difference s
  refine ⟨C, hC, ?_⟩
  intro r N _ b p q P M Q W out H R D B d e E F T S _ _ _ _ _ _ _ _
    I J σ _ _ V U hmap hT hS hQ hTc hSc hentries hV hU w
  apply hcomparison E F T S D.dependentQuotientMap hmap V U hQ hTc hSc hentries
  · intro x hx
    rw [hS]
    apply D.dependentQuotientMap_mem_layer
    rwa [hT] at hx
  · intro x hx
    rw [hT] at hx
    rw [hV]
    exact (hU x hx).symm

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H₀ : Finset (ZMod N)} {R : NativeRankRelation W out H₀ p q} (D : R.CommonData P)
  (B : D.CoefficientBases Q) {n : ℕ}
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
  (T : E.DegreeRankStructure r) (hT : T.filtration = D.coefficientFreeFiltration)
  {H : ℕ} (hH : 1 ≤ H)
  (hbracket : ∀ i j k, RationalHeightLE (lieStructureConstants E.basis i j k) H)
  (hdegree : ∀ i a j, RationalHeightLE (E.basis.repr (E.layerBasis i a).val j) H)
  (hrank : ∀ i j a k, RationalHeightLE (E.basis.repr (T.basis i j a).val k) H)
  (hgen : ∀ i j, RationalHeightLE (E.basis.repr (D.coefficientFreeGenerator i) j) H)
  (hfreq : ∀ i, RationalHeightLE (B.freeFrequency D (E.basis i)) H)

include T hT hH hbracket hdegree hrank hgen hfreq in
theorem CoefficientBases.exists_dependentQuotient_integral_model (l : ℕ) (hl : 0 < l) :
    ∃ m : ℕ, m ≤ n ∧ ∃ d : ℕ, d ≤ n ∧ ∃ u : ℕ, u ≤ d ∧
      let K := rankQuotientHeight n m d u (lieTreeHeight n H s)
      ∃ G : RationalFilteredNilmanifold D.DependentQuotient s d,
        ∃ S : G.DegreeRankStructure r,
          S.filtration = D.dependentQuotientFiltration ∧
          l ∣ G.grid ∧
          G.grid ≤ bchIntegralDenominatorBound s * K ^ (d ^ 3) * (l * K ^ d) ∧
          bchSubgroupCoordinates G.basis G.lattice = scaledIntegerGrid G.grid ∧
          (∀ i j, RationalHeightLE (G.basis.repr (D.dependentQuotientMap (E.basis j)) i) K) ∧
          ∃ ξ : D.DependentQuotient →ₗ[ℚ] ℚ,
            (∀ x ∈ D.coefficientFreeFiltration.layer s r,
              ξ (D.dependentQuotientMap x) = B.freeFrequency D x) ∧
            (∀ i, RationalHeightLE (ξ (G.basis i)) K) ∧
            (∀ z : G.filtration.Group, z ∈ G.lattice → ∃ a : ℤ, ξ z.coord = a) ∧
            ∀ v : ℝ, (d : ℝ) ≤ v → (G.grid : ℝ) ≤ Real.exp v →
              (K : ℝ) ≤ Real.exp v → S.ComplexityLE v := by
  classical
  let I := D.dependentWordIdeal 0 2 0
  let H' := lieTreeHeight n H s
  have hHH' : H ≤ H' := lieTreeHeight_ge_input n H s
  have hb : ∃ b' : ∀ i : Fin (s + 1),
      Basis (Fin (finrank ℚ (T.filtration.associatedDegree.layer (i.val + 1)))) ℚ
        (T.filtration.associatedDegree.layer (i.val + 1)),
      ∀ i a j, RationalHeightLE (E.basis.repr (b' i a).val j) H' := by
    rw [T.associated]
    exact ⟨E.layerBasis, fun i a j => (hdegree i a j).mono hHH'⟩
  obtain ⟨b', hb'⟩ := hb
  obtain ⟨a, ha⟩ := exists_markedLieSpan_bounded_basis D.coefficientFreeFiltration E.basis
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
    D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer hbracket hgen 0 2 0
  change Basis (Fin (finrank ℚ I.toSubmodule)) ℚ I at a
  have ha' : ∀ i j, RationalHeightLE (E.basis.repr (a i).val j) H' := by
    intro i j
    have h := ha i j
    change RationalHeightLE (E.basis.repr (a i).val j)
      (lieTreeHeight (Fintype.card (Fin n)) H s) at h
    simpa only [Fintype.card_fin, H'] using h
  have hann : T.filtration.layer s r ⊓ I.toSubmodule ≤ (B.freeFrequency D).ker := by
    rw [hT]
    exact B.top_inter_dependentWordIdeal_le_ker D
  obtain ⟨m, hm, d, hd, u, hu, f, hproj, hc, hbq, hrq, ξ, hξ, hξH⟩ :=
    exists_bounded_rank_quotient_data T.filtration E.basis b' T.basis I a
      (B.freeFrequency D) hann (hH.trans hHH') hb'
      (fun i j a k => (hrank i j a k).mono hHH') ha'
      (fun i j k => (hbracket i j k).mono hHH') (fun i => (hfreq i).mono hHH')
  let K := rankQuotientHeight n m d u H'
  have hm' : m ≤ n := by
    let _ : FiniteDimensional ℚ D.CoefficientFreeLieAlgebra := E.basis.finiteDimensional_of_finite
    have hn : finrank ℚ D.CoefficientFreeLieAlgebra = n := by
      simpa only [Fintype.card_fin] using finrank_eq_card_basis E.basis
    exact hm.trans ((Submodule.finrank_le I.toSubmodule).trans_eq hn)
  have hbq' : ∀ i : Fin (s + 1), ∃ bq : Basis
      (Fin (finrank ℚ (D.dependentQuotientFiltration.associatedDegree.layer (i.val + 1)))) ℚ
        (D.dependentQuotientFiltration.associatedDegree.layer (i.val + 1)),
      ∀ a j, RationalHeightLE (f.repr (bq a).val j) K := by
    intro i
    have h := hbq i
    rw [hT] at h
    exact h
  have hrq' : ∀ i j : Fin (s + 1), ∃ cq : Basis
      (Fin (finrank ℚ (D.dependentQuotientFiltration.layer i.val j.val))) ℚ
        (D.dependentQuotientFiltration.layer i.val j.val),
      ∀ a k, RationalHeightLE (f.repr (cq a).val k) K := by
    intro i j
    have h := hrq i j
    rw [hT] at h
    exact h
  choose bq hbqH using hbq'
  choose cq hcqH using hrq'
  obtain ⟨grid, hgrid, hdiv, hbound, G, S, hSF, hGf, hGgrid, hcoords, hint, hcomplex⟩ :=
    D.dependentQuotientFiltration.exists_bounded_rank_integral_model_with_frequency
      f bq cq hbqH hcqH hc ξ hξH l hl
  refine ⟨m, hm', d, hd, u, hu, G, S, hSF, hGgrid.symm ▸ hdiv,
    hGgrid.symm ▸ hbound, ?_, ?_, ξ, ?_, ?_, hint, ?_⟩
  · rwa [hGgrid]
  · intro i j
    rw [hGf]
    exact hproj i j
  · intro x hx
    apply hξ x
    rwa [hT]
  · intro i
    rw [hGf]
    exact hξH i
  · intro v hdv hgv hKv
    apply hcomplex v hdv
    · rwa [← hGgrid]
    · exact hKv

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonDependentCoveredModel
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_controlled_dependentQuotient_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p q P Q v : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P) (B : D.CoefficientBases Q) {n : ℕ}
      (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
      (T : E.DegreeRankStructure r), T.filtration = D.coefficientFreeFiltration →
      0 ≤ v → T.ComplexityLE v →
      (∀ i j, rationalLogHeight (E.basis.repr (D.coefficientFreeGenerator i) j) ≤ v) →
      (∀ i, rationalLogHeight (B.freeFrequency D (E.basis i)) ≤ v) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp v →
      ∃ d : ℕ, d ≤ n ∧ ∃ G : RationalFilteredNilmanifold D.DependentQuotient s d,
        ∃ S : G.DegreeRankStructure r,
          S.filtration = D.dependentQuotientFiltration ∧ S.ComplexityLE ((v + C) ^ C) ∧
          l ∣ G.grid ∧ bchSubgroupCoordinates G.basis G.lattice = scaledIntegerGrid G.grid ∧
          (∀ i j, rationalLogHeight (G.basis.repr (D.dependentQuotientMap (E.basis j)) i) ≤
            (v + C) ^ C) ∧
          ∃ ξ : D.DependentQuotient →ₗ[ℚ] ℚ,
            (∀ x ∈ D.coefficientFreeFiltration.layer s r,
              ξ (D.dependentQuotientMap x) = B.freeFrequency D x) ∧
            (∀ i, rationalLogHeight (ξ (G.basis i)) ≤ (v + C) ^ C) ∧
            ∀ z : G.RealGroup, z ∈ G.realLattice → ∃ a : ℤ, realifyFunctional ξ z.coord = a := by
  let k := (6 * s + 4) * 424
  let a := bchIntegralDenominatorBound s + 5
  let P₀ : Polynomial ℕ := (Polynomial.X + 3) ^ k
  let R₀ := ((P₀ + 2) ^ 2 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P₀ + R₀)
  refine ⟨C, hC, ?_⟩
  intro r N _ b p q P Q v W out H R D B n E T hT hv hcomplex hgen hfreq l hl hlv
  let H₁ := ⌈Real.exp v⌉₊
  obtain ⟨m, hm, d, hd, u, hu, G, S, hSF, hdiv, hgrid, hcoords, hproj,
      ξ, hξ, hξH, hint, hSc⟩ :=
    B.exists_dependentQuotient_integral_model D E T hT (one_le_ceil_exp v)
      (fun i j k => rationalHeightLE_ceil_exp (hcomplex.1.2.2.1 i j k))
      (fun i a j => rationalHeightLE_ceil_exp (hcomplex.1.2.2.2 i a j))
      (fun i j a k => rationalHeightLE_ceil_exp (hcomplex.2 i j a k))
      (fun i j => rationalHeightLE_ceil_exp (hgen i j))
      (fun i => rationalHeightLE_ceil_exp (hfreq i)) l hl
  let K := rankQuotientHeight n m d u (lieTreeHeight n H₁ s)
  let P₁ := (v + 3) ^ k
  let R₁ := ((P₁ + 2) ^ 2 + a) ^ a
  have hv1 : 0 ≤ v + 1 := by linarith
  have hn : (n : ℝ) ≤ v + 1 := hcomplex.1.1.trans (by linarith)
  have hm' : (m : ℝ) ≤ v + 1 := (Nat.cast_le.mpr hm).trans hn
  have hd' : (d : ℝ) ≤ v + 1 := (Nat.cast_le.mpr hd).trans hn
  have hu' : (u : ℝ) ≤ v + 1 := (Nat.cast_le.mpr hu).trans hd'
  have hK : (K : ℝ) ≤ Real.exp P₁ := by
    have h := dependentQuotientHeight_le_exp s n m d u H₁ hv1 hn hm' hd' hu'
      (ceil_exp_le_exp_add_one hv)
    simpa only [show v + 1 + 2 = v + 3 by ring] using h
  have hvP : v ≤ P₁ := by
    have h := le_power_budget hv1 (show 1 ≤ k by dsimp [k]; omega)
    exact (show v ≤ v + 1 by linarith).trans (by
      simpa only [show v + 1 + 2 = v + 3 by ring] using h)
  have hP : 0 ≤ P₁ := hv.trans hvP
  have hdP : (d : ℝ) ≤ P₁ := (Nat.cast_le.mpr hd).trans (hcomplex.1.1.trans hvP)
  have hgrid' : (G.grid : ℝ) ≤ Real.exp R₁ :=
    (Nat.cast_le.mpr hgrid).trans (integral_frequency_grid_allowance_le_exp
      (bchIntegralDenominatorBound s) d K l hP hdP hK
      (hlv.trans (Real.exp_le_exp.mpr hvP)))
  have htotal : P₁ + R₁ ≤ (v + C) ^ C := by
    simpa [P₀, R₀, P₁, R₁, Polynomial.eval₂_pow] using hbudget v hv
  have hPC : P₁ ≤ (v + C) ^ C :=
    (le_add_of_nonneg_right (by dsimp [R₁]; positivity)).trans htotal
  have hRC : R₁ ≤ (v + C) ^ C := (le_add_of_nonneg_left hP).trans htotal
  refine ⟨d, hd, G, S, hSF, hSc _ (hdP.trans hPC)
    (hgrid'.trans (Real.exp_le_exp.mpr hRC)) (hK.trans (Real.exp_le_exp.mpr hPC)),
    hdiv, hcoords, ?_, ξ, hξ, ?_, G.realLattice_functional_integral ξ hint⟩
  · intro i j
    exact (rationalLogHeight_le_of_height (hproj i j) hK).trans hPC
  · intro i
    exact (rationalLogHeight_le_of_height (hξH i) hK).trans hPC

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_dependentQuotient_unit_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p q P Q v : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P) (B : D.CoefficientBases Q) {n : ℕ}
      (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
      (T : E.DegreeRankStructure r), T.filtration = D.coefficientFreeFiltration →
      0 ≤ v → T.ComplexityLE v →
      (∀ i j, rationalLogHeight (E.basis.repr (D.coefficientFreeGenerator i) j) ≤ v) →
      (∀ i, rationalLogHeight (B.freeFrequency D (E.basis i)) ≤ v) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp v →
      ∃ d : ℕ, d ≤ n ∧ ∃ G : RationalFilteredNilmanifold D.DependentQuotient s d,
        ∃ S : G.DegreeRankStructure r,
          S.filtration = D.dependentQuotientFiltration ∧ S.ComplexityLE ((v + C) ^ C) ∧
          l ∣ G.grid ∧ bchSubgroupCoordinates G.basis G.lattice = scaledIntegerGrid G.grid ∧
          (∀ i j, rationalLogHeight (G.basis.repr (D.dependentQuotientMap (E.basis j)) i) ≤
            (v + C) ^ C) ∧
          ∃ ξ : D.DependentQuotient →ₗ[ℚ] ℚ,
            (∀ x ∈ D.coefficientFreeFiltration.layer s r,
              ξ (D.dependentQuotientMap x) = B.freeFrequency D x) ∧
            (∀ i, rationalLogHeight (ξ (G.basis i)) ≤ (v + C) ^ C) ∧
            (∀ z : G.RealGroup, z ∈ G.realLattice → ∃ a : ℤ, realifyFunctional ξ z.coord = a) ∧
            (letI := moduleTopology ℝ (ℝ ⊗[ℚ] D.DependentQuotient)
             letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient) :=
               IsModuleTopology.topologicalAddGroup ℝ _
             letI := realification_moduleTopology_t2 G.basis
             ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ Real.exp ((v + C) ^ C) ∧
               ∃ U : G.UnitVerticalObservable (S.realSubgroup s r) (Fin k) ((v + C) ^ C),
                 U.frequency = ξ) := by
  obtain ⟨a, _, hmodel⟩ := exists_controlled_dependentQuotient_model s
  obtain ⟨c, _, hunit⟩ := RationalFilteredNilmanifold.exists_native_prescribed_unit s
  let A₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (A₀ + (A₀ + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro r N _ b p q P Q v W out H R D B n E T hT hv hcomplex hgen hfreq l hl hlv
  obtain ⟨d, hd, G, S, hSF, hSc, hdiv, hcoords, hproj, ξ, hξ, hξH, hint⟩ :=
    hmodel D B E T hT hv hcomplex hgen hfreq l hl hlv
  let A := (v + a) ^ a
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have htotal : A + (A + c) ^ c ≤ (v + C) ^ C := by
    simpa [A₀, A, Polynomial.eval₂_pow] using hbudget v hv
  have hAC : A ≤ (v + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (A + c) ^ c)).trans htotal
  have hUC : (A + c) ^ c ≤ (v + C) ^ C := (le_add_of_nonneg_left hA).trans htotal
  refine ⟨d, hd, G, S, hSF, hSc.mono S hAC, hdiv, hcoords,
    (fun i j => (hproj i j).trans hAC), ξ, hξ, (fun i => (hξH i).trans hAC), hint, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.DependentQuotient)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 G.basis
  obtain ⟨k, hk, hkbound, U, hU⟩ := hunit G hA hSc.1 ξ hξH hint
  refine ⟨k, hk, hkbound.trans (Real.exp_le_exp.mpr hUC),
    (U.restrictVertical (S.realSubgroup s r) (S.realSubgroup_le_degree s r)).mono hUC, ?_⟩
  exact hU

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

def HasCoveredDependentComparison {s r N : ℕ} [NeZero N] {b p q P v : ℝ}
    {W : NativeDegreeRankFamily s (r + 1) (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
    (D : R.CommonData P) {n : ℕ}
    (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
    (T : E.DegreeRankStructure (r + 1)) {I : Type} [Fintype I]
    [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) I v) (l : ℕ) (Q : ℝ) : Prop :=
  ∃ d : ℕ, d ≤ n ∧ ∃ G : RationalFilteredNilmanifold D.DependentQuotient s d,
    ∃ S : G.DegreeRankStructure (r + 1),
      S.filtration = D.dependentQuotientFiltration ∧ S.ComplexityLE Q ∧
      l ∣ G.grid ∧ bchSubgroupCoordinates G.basis G.lattice = scaledIntegerGrid G.grid ∧
      (∀ i j, rationalLogHeight (G.basis.repr (D.dependentQuotientMap (E.basis j)) i) ≤ Q) ∧
      ∃ Λ : Subgroup E.filtration.Group, Λ ≤ E.lattice ∧
        (Λ.subgroupOf E.lattice).Characteristic ∧ (Λ.subgroupOf E.lattice).Normal ∧
        (Λ.subgroupOf E.lattice).FiniteIndex ∧ (Λ.relIndex E.lattice : ℝ) ≤ Real.exp Q ∧
        ∃ (m : ℕ) (hm : 0 < m)
          (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates E.basis Λ)
          (hout : bchSubgroupCoordinates E.basis Λ ⊆ denominatorGrid m),
          (T.withLattice Λ m hm hin hout).ComplexityLE Q ∧
          ∃ hmap : Λ ≤ G.lattice.comap (mapOfSteps
              (hL := E.filtration.lowerCentralSeries_eq_bot)
              (hM := G.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap),
            ∃ V₀ : (E.withLattice Λ m hm hin hout).UnitVerticalObservable
                ((T.withLattice Λ m hm hin hout).realSubgroup s (r + 1)) I Q,
              V₀.frequency = V.frequency ∧ V₀.lipBound = V.lipBound ∧
              (∀ i x, V₀.observable i (QuotientGroup.mk x) = V.observable i (QuotientGroup.mk x)) ∧
              (letI := moduleTopology ℝ (ℝ ⊗[ℚ] D.DependentQuotient)
               letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient) :=
                 IsModuleTopology.topologicalAddGroup ℝ _
               letI := realification_moduleTopology_t2 G.basis
               ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ Real.exp Q ∧
                 ∃ U : G.UnitVerticalObservable (S.realSubgroup s (r + 1)) (Fin k) Q,
                   (∀ x ∈ D.coefficientFreeFiltration.layer s (r + 1),
                     U.frequency (D.dependentQuotientMap x) = V.frequency x) ∧
                   (∀ z : G.RealGroup, z ∈ G.realLattice →
                     ∃ a : ℤ, realifyFunctional U.frequency z.coord = a) ∧
                   ∀ (σ : Type) (w : σ → ℕ),
                     (E.withLattice Λ m hm hin hout).HasUniformLowerRankUnitFamily
                       (T.withLattice Λ m hm hin hout)
                       (mapDifferenceObservable V₀ U D.dependentQuotientMap hmap) w Q)

theorem exists_covered_dependentQuotient_comparison (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p q P Q v : ℝ}
      {W : NativeDegreeRankFamily s (r + 1) (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P) (J : D.CoefficientBases Q) {n : ℕ}
      (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
      (T : E.DegreeRankStructure (r + 1)) {I : Type} [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) I v),
      T.filtration = D.coefficientFreeFiltration → 0 ≤ v → T.ComplexityLE v →
      (∀ i j, rationalLogHeight (E.basis.repr (D.coefficientFreeGenerator i) j) ≤ v) →
      V.frequency = J.freeFrequency D →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp v →
        D.HasCoveredDependentComparison E T V l ((v + C) ^ C) := by
  obtain ⟨a, ha, hmodel⟩ := exists_native_dependentQuotient_unit_model s
  obtain ⟨c, hc, hcover⟩ := exists_native_source_unit_cover
  obtain ⟨b, _, hcomparison⟩ := exists_uniform_dependentQuotient_comparison s
  let A₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let K₀ := (A₀ + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (K₀ + (K₀ + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro r N _ b₀ p q P Q v W out H R D J n E T I _ _ _ _ _ V hT hv hTc hgen hV l hl hlv
  have hshift (x : ℝ) (hx : 0 ≤ x) (a : ℕ) (ha : 2 ≤ a) : x ≤ (x + a) ^ a := by
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
    calc
      x ≤ x + a := le_add_of_nonneg_right (Nat.cast_nonneg _)
      _ = (x + a) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega : 1 ≤ a)
  let A := (v + a) ^ a
  let K := (A + c) ^ c
  have hvA : v ≤ A := hshift v hv a ha
  have hA : 0 ≤ A := hv.trans hvA
  have hAK : A ≤ K := hshift A hA c hc
  have hK : 0 ≤ K := hA.trans hAK
  have htotal : K + (K + b) ^ b ≤ (v + C) ^ C := by
    simpa [A₀, K₀, A, K, Polynomial.eval₂_pow] using hbudget v hv
  have hKC : K ≤ (v + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (K + b) ^ b)).trans htotal
  have hAC : A ≤ (v + C) ^ C := hAK.trans hKC
  have hcomparisonC : (K + b) ^ b ≤ (v + C) ^ C := (le_add_of_nonneg_left hK).trans htotal
  obtain ⟨d, hd, G, S, hSF, hSc, hdiv, hcoords, hproj, ξ, hξ, _, hint, hunit⟩ :=
    hmodel D J E T hT hv hTc hgen (fun i => by rw [← hV]; exact V.height i) l hl hlv
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, m, hm, hin, hout, hcoverT, hmap, hpreserve⟩ :=
    hcover (I := I) E T G D.dependentQuotientMap hA (hTc.mono T hvA) hSc.1 hproj
  obtain ⟨V₀, hV₀, hVlip, hVobs⟩ := hpreserve (V.mono hvA)
  refine ⟨d, hd, G, S, hSF, hSc.mono S hAC, hdiv, hcoords,
    (fun i j => (hproj i j).trans hAC), Λ, hΛ, hchar, hnormal, hfinite,
    hindex.trans (Real.exp_le_exp.mpr hKC), m, hm, hin, hout,
    hcoverT.mono _ hKC, hmap, V₀.mono hKC, hV₀, hVlip, hVobs, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.DependentQuotient)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 G.basis
  obtain ⟨k, hk, hkbound, U, hU⟩ := hunit
  refine ⟨k, hk, hkbound.trans (Real.exp_le_exp.mpr hAC), U.mono hAC, ?_, ?_, ?_⟩
  · intro x hx
    change U.frequency (D.dependentQuotientMap x) = V.frequency x
    rw [hU, hV]
    exact hξ x hx
  · intro z hz
    change ∃ a : ℤ, realifyFunctional U.frequency z.coord = a
    rw [hU]
    exact hint z hz
  · intro σ w
    have hfreq₀ : V₀.frequency = J.freeFrequency D := hV₀.trans hV
    have hfreqU : ∀ x ∈ D.coefficientFreeFiltration.layer s (r + 1),
        (U.mono hAK).frequency (D.dependentQuotientMap x) = J.freeFrequency D x := by
      intro x hx
      change U.frequency (D.dependentQuotientMap x) = _
      rw [hU]
      exact hξ x hx
    have h := hcomparison D J (E.withLattice Λ m hm hin hout) G
      (T.withLattice Λ m hm hin hout) S I (Fin k) σ V₀ (U.mono hAK) hmap
      hT hSF hK hcoverT (hSc.mono S hAK) (fun i j => (hproj i j).trans hAK)
      hfreq₀ hfreqU w
    exact h.mono hcomparisonC

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPermutationTensor
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_finite_assignment_expansion (s n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex s => 1) p),
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun k (x : Fin (n + 2) → ℤ) => W.eval k
          (mixedReplicatedInput (x 0) (fun _ : Fin s => ∑ a : Fin (n + 1), x a.succ)))
        (fun a : (Fin s → Fin (n + 1)) → Fin W.outputDim => fun x =>
          ∏ v : Fin s → Fin (n + 1), W.eval (a v)
            (mixedReplicatedInput (x 0) (fun j => x (v j).succ))) := by
  let : Nonempty (MixedReplicatedIndex s) := replicatedMixed_nonempty s
  obtain ⟨A, _, hexpand⟩ := exists_finite_assignment_equivalence n (mixedRepeatedCoordinates s)
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + Polynomial.C ((n + 1) ^ s) * X + X)
  refine ⟨C, hC, ?_⟩
  intro p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hsum : (p + A) ^ A + ((n + 1) ^ s : ℕ) * p + p ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (p + A) ^ A := by positivity
  have hnp : 0 ≤ ((n + 1) ^ s : ℕ) * p := mul_nonneg (Nat.cast_nonneg _) hp
  have hAC : (p + A) ^ A ≤ (p + C) ^ C := by linarith
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hnC : ((n + 1) ^ s : ℕ) * p ≤ (p + C) ^ C := by linarith
  let M (j : Fin (n + 1) × MixedReplicatedIndex s) : ((Fin (n + 2) → ℤ) →+ ℤ) :=
    { toFun := fun x => mixedChoiceSample (x 0) (fun a => x a.succ) j
      map_zero' := by rcases j with ⟨a, b, k⟩; fin_cases b <;> rfl
      map_add' := by intro x y; rcases j with ⟨a, b, k⟩; fin_cases b <;> rfl }
  have hM (x : Fin (n + 2) → ℤ) :
      (fun j => M j x) = mixedChoiceSample (x 0) (fun a => x a.succ) := rfl
  have E := (hexpand W (mixedRepeatedCoordinates_nodup s)).linearPullbackHom M
  have H : NativeIntegerVectorEquivalence s ((p + A) ^ A)
      (fun k (x : Fin (n + 2) → ℤ) => W.eval k
        (mixedReplicatedInput (x 0) (fun _ : Fin s => ∑ a : Fin (n + 1), x a.succ)))
      (fun a : (Fin (mixedRepeatedCoordinates s).length → Fin (n + 1)) → Fin W.outputDim =>
        fun x => ∏ v, W.eval (a v)
          (mixedReplicatedInput (x 0) (fun j => x (mixedChoiceAssignmentEquiv s n v j).succ))) := by
    simpa only [hM, finiteChoiceExpansion, mixedChoiceSample_sum, mixedChoiceSample_leaf,
      replicatedMixed_card, Nat.add_sub_cancel] using E
  have hdim : (Fintype.card ((Fin s → Fin (n + 1)) → Fin W.outputDim) : ℝ) ≤
      Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp p ^ ((n + 1) ^ s) := pow_le_pow_left₀ (Nat.cast_nonneg _) W.output_bound _
      _ = Real.exp (((n + 1) ^ s : ℕ) * p) := (Real.exp_nat_mul p ((n + 1) ^ s)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hnC
  apply H.of_coordinate_maps _ _ id (fun a v => a (mixedChoiceAssignmentEquiv s n v))
    (fun _ _ => rfl) _ _ hdim hAC
  · intro a x
    exact ((mixedChoiceAssignmentEquiv s n).prod_comp (fun v : Fin s → Fin (n + 1) =>
      W.eval (a v) (mixedReplicatedInput (x 0) (fun j => x (v j).succ)))).symm
  · simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpC)

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_permutation_partition_expansion (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex s => 1) p),
      (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
        W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) = W.eval k x) →
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun k (x : Fin (s + 1) → ℤ) => W.eval k
          (mixedReplicatedInput (x 0) (fun _ : Fin s => ∑ j : Fin s, x j.succ)))
        (fun a : Equiv.Perm (Fin s) ⊕ MissingAssignment s → Fin W.outputDim => fun x =>
          (∏ e : Equiv.Perm (Fin s), W.eval (a (Sum.inl e))
            (mixedReplicatedInput (x 0) (fun j => x j.succ))) *
          ∏ v : MissingAssignment s, W.eval (a (Sum.inr v))
            (mixedReplicatedInput (x 0) (fun j => x (v.val j).succ))) := by
  cases s with
  | zero => omega
  | succ n =>
      obtain ⟨C, hC, hexpand⟩ := exists_mixed_finite_assignment_expansion (n + 1) n
      refine ⟨C, hC, ?_⟩
      intro p W hsym
      classical
      have E := hexpand W
      apply E.of_coordinate_maps _ _ id
        (fun a v => a ((assignmentSplitEquiv (n + 1)).symm v))
        (fun _ _ => rfl) _ E.left_dimension _ le_rfl
      · intro a x
        exact (W.mixed_assignment_product_grouped hsym (x 0) (fun j => x j.succ) a).symm
      · have hcard : Fintype.card (Equiv.Perm (Fin (n + 1)) ⊕ MissingAssignment (n + 1)) =
            Fintype.card (Fin (n + 1) → Fin (n + 1)) :=
          Fintype.card_congr (assignmentSplitEquiv (n + 1))
        simpa only [Fintype.card_fun, hcard] using E.right_dimension

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeMixedCoordinateSlices
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open Module
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_mixed_scalar_coordinate_slice (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      (out : Fin W.outputDim) (d : Fin (n + 2)) (c : ℤ),
      Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) ((p + C) ^ C)
        (fun x => let z := Function.update x d c
          W.eval out (mixedSlotInput (z 0) (z 1) (fun l => z l.succ.succ)))) := by
  obtain ⟨C, hC, hfreeze⟩ := exists_mixed_frozen_affine_expansion n
  refine ⟨C, hC, ?_⟩
  intro p W out d c
  let coord := mixedInputCoordinate n
  let index := mixedCoordinateIndex n
  have hindex (k : Fin (n + 2)) : coord (index k) = k := mixedInputCoordinate_index n k
  let A : MixedReplicatedIndex (n + 1) → Fin (n + 2) → ℤ := fun j k =>
    if coord j = d then 0 else if k = coord j then 1 else 0
  let b : MixedReplicatedIndex (n + 1) → ℤ := fun j => if coord j = d then c else 0
  obtain ⟨E⟩ := hfreeze W (index d) A b out (by intro k; simp [A, hindex])
  have hmap (x : Fin (n + 2) → ℤ) (j : MixedReplicatedIndex (n + 1)) :
      integerAffineMap A b x j = (Function.update x d c) (coord j) := by
    by_cases hj : coord j = d <;> simp [integerAffineMap, A, b, hj, ite_mul]
  have heq (x : Fin (n + 2) → ℤ) : integerAffineMap A b x =
      mixedSlotInput ((Function.update x d c) 0) ((Function.update x d c) 1)
        (fun l => (Function.update x d c) l.succ.succ) := by
    funext j
    rw [hmap]
    exact congrFun (mixedInputCoordinate_eval n (Function.update x d c)) j
  exact ⟨by simpa only [heq] using E⟩

theorem exists_mixed_kernel_coordinate_slice (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      (i j : Fin W.outputDim) (d : Fin (n + 2)) (c : ℤ),
      Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) ((p + C) ^ C)
        (fun x => W.mixedAntisymmetric i j (Function.update x d c))) := by
  obtain ⟨A, _, hscalar⟩ := exists_mixed_scalar_coordinate_slice n
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W i j d c
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  let e := mixedExchangeCoordinate n
  have he0 : e 0 = 1 := rfl
  have he1 : e 1 = 0 := rfl
  have hetail (l : Fin n) : e l.succ.succ = l.succ.succ := rfl
  have hswap (x : Fin (n + 2) → ℤ) : Function.update (fun k => x (e k)) (e d) c =
      fun k => (Function.update x d c) (e k) := mixedExchangeCoordinate_update n x d c
  obtain ⟨L⟩ := hscalar W i d c
  obtain ⟨R⟩ := hscalar W j (e d) c
  have R' : NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) q
      (fun x => let z := Function.update x d c
        W.eval j (mixedSlotInput (z 1) (z 0) (fun l => z l.succ.succ))) := by
    have E : NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) q
        (fun x => let z := Function.update (fun k => x (e k)) (e d) c
          W.eval j (mixedSlotInput (z 0) (z 1) (fun l => z l.succ.succ))) :=
      R.linearPullbackHom (fun k => ⟨⟨fun x => x (e k), rfl⟩, fun _ _ => rfl⟩)
    simpa only [hswap, he0, he1, hetail] using E
  obtain ⟨F⟩ := hmul hq L R'.conjugate
  have hcost : (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨F.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedAnchorExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem NativeMultidegreeNilcharacter.exists_mixed_corner_expansion (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      (i j : Fin W.outputDim) (a : Fin (n + 2) → ℤ) (ω : Fin (n + 2) → Bool),
      ω ≠ (fun _ => false) →
      Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) ((p + C) ^ C)
        (fun x => W.mixedAntisymmetric i j (boxCorner x a ω))) := by
  obtain ⟨C, hC, hslice⟩ := NativeMultidegreeNilcharacter.exists_mixed_kernel_coordinate_slice n
  refine ⟨C, hC, ?_⟩
  intro p W i j a ω hω
  obtain ⟨k, hk⟩ := exists_true_of_ne_false hω
  obtain ⟨E⟩ := hslice W i j k (a k)
  have hupdate (x : Fin (n + 2) → ℤ) :
      Function.update (boxCorner x a ω) k (a k) = boxCorner x a ω := by
    funext l
    by_cases h : l = k
    · subst l
      simp [boxCorner, hk]
    · simp [h]
  exact ⟨by simpa only [hupdate] using E.boxCornerPullback a ω⟩

theorem NativeMultidegreeNilcharacter.exists_mixed_anchor_expansion (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      (i j : Fin W.outputDim) (a : Fin (n + 2) → ℤ),
      Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) ((p + C) ^ C)
        (boxCornerAnchor (W.mixedAntisymmetric i j) a)) := by
  obtain ⟨A, _, hcorner⟩ := NativeMultidegreeNilcharacter.exists_mixed_corner_expansion n
  obtain ⟨B, _, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget (2 ^ (n + 2) - 1)
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W i j a
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  let S : Finset (Fin (n + 2) → Bool) := Finset.univ.erase (fun _ => false)
  have hS : Fintype.card S = 2 ^ (n + 2) - 1 := by simp [S]
  let e : Fin (2 ^ (n + 2) - 1) ≃ S := (Fintype.equivFinOfCardEq hS).symm
  let f : Fin (2 ^ (n + 2) - 1) → (Fin (n + 2) → ℤ) → ℂ := fun l x =>
    conjugationPower (booleanWeight (e l).val)
      (W.mixedAntisymmetric i j (boxCorner x a (e l).val))
  have hf (l : Fin (2 ^ (n + 2) - 1)) : Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) q (f l)) := by
    have hne : (e l).val ≠ (fun _ => false) := (Finset.mem_erase.mp (e l).property).1
    obtain ⟨E⟩ := hcorner W i j a (e l).val hne
    exact ⟨E.conjugationPower (booleanWeight (e l).val)⟩
  obtain ⟨E⟩ := hprod f hq hf
  have hcost : (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have heq (x : Fin (n + 2) → ℤ) : (∏ l, f l x) = boxCornerAnchor (W.mixedAntisymmetric i j) a x := by
    exact boxCornerAnchor_prod_equiv e (W.mixedAntisymmetric i j) a x
  exact ⟨by simpa only [heq] using E.mono hcost⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMixedSeparatedFamily
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_separated_family (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex s => 1) p),
      (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
        W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) = W.eval k x) →
      ∀ {G Ω : Type*} (H : Finset G), H.Nonempty →
      ∀ (S : G → Finset Ω), (∀ h ∈ H, (S h).Nonempty) →
      ∀ (sample : G → Ω → Fin (s + 1) → ℤ) (f : G → Ω → ℂ),
      (∀ h ∈ H, ∀ u ∈ S h, ‖f h u‖ ≤ 1) →
      ∀ (j : Fin W.outputDim) (A : Fin (s + 1) → (Fin (s + 1) → ℤ) → ℂ),
      (∀ i x, ‖A i x‖ ≤ 1) →
      (∀ i x y, (∀ l, l ≠ i → x l = y l) → A i x = A i y) →
      (∀ h ∈ H, Real.exp (-p) ≤ ‖𝔼 u ∈ S h, f h u * star (W.eval j
        (mixedReplicatedInput (sample h u 0) (fun _ : Fin s => ∑ l : Fin s, sample h u l.succ))) *
          ∏ i, A i (sample h u)‖) →
      ∃ (a : Equiv.Perm (Fin s) → Fin W.outputDim)
        (B : Fin (s + 1) → (Fin (s + 1) → ℤ) → ℂ),
        (∀ i x, ‖B i x‖ ≤ 1) ∧
        (∀ i x y, (∀ l, l ≠ i → x l = y l) → B i x = B i y) ∧
        ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (H.card : ℝ) ≤ (H'.card : ℝ) ∧
          ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 u ∈ S h, f h u * star (mixedPermutationProduct W.eval a (sample h u)) *
              ∏ i, B i (sample h u)‖ := by
  obtain ⟨a, _, hexpand⟩ := exists_mixed_permutation_partition_expansion s hs
  obtain ⟨b, _, htransfer⟩ := exists_separated_family_correlation s
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Q + 2 + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p W hsym G Ω H hH S hS sample f hf j A hA hAind hcorr
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + a) ^ a
  let r := p + q + 2
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hpr : p ≤ r := by dsimp only [r]; linarith
  have hqr : q ≤ r := by dsimp only [r]; linarith
  have E : NativeIntegerVectorEquivalence s q
      (fun i (x : Fin (s + 1) → ℤ) => W.eval i
        (mixedReplicatedInput (x 0) (fun _ : Fin s => ∑ l : Fin s, x l.succ)))
      (mixedAssignmentPartitionVector W.eval) := hexpand W hsym
  obtain ⟨k, B, hB, hBind, H', hsub, hH', hsize, hBcorr⟩ := htransfer hr (E.mono hqr)
    (mixedAssignmentPartitionVector_unit W.eval W.unit_eval) H hH S hS sample f hf j A hA hAind
    (fun h hh => (Real.exp_le_exp.mpr (neg_le_neg hpr)).trans (hcorr h hh))
  obtain ⟨D, hD, hDind, hDprod⟩ := W.exists_mixed_missing_factors (fun v => k (Sum.inr v))
  have hcost : (r + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, Q, q, r, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨(fun e => k (Sum.inl e)), (fun i x => B i x * star (D i x)),
    ?_, ?_, H', hsub, hH', ?_, ?_⟩
  · intro i x
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hB i x)).trans (hD i x)
  · intro i x y hxy
    change B i x * star (D i x) = B i y * star (D i y)
    rw [hBind i x y hxy, hDind i x y hxy]
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcost))
      (Nat.cast_nonneg _)).trans hsize
  · intro h hh
    simp only [Finset.prod_mul_distrib, ← star_prod, hDprod]
    simpa only [mixedAssignmentPartitionVector, star_mul, mul_comm, mul_left_comm, mul_assoc] using
      (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans (hBcorr h hh)

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OriginalDiagonalComparison
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

theorem exists_originalDiagonalCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p), 0 ≤ q →
      ∀ F : (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
        (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
        (Fin 2 → ℤ) → ℂ,
      (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q (F a b))) →
      ∀ a i c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + C) ^ C)
        (W.originalDiagonalCorrection F a i c)) := by
  obtain ⟨A, _, hequiv⟩ := exists_explicit_quadratic_root_equivalence
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + X + 3 * (X + 1) + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B + 6 * (X + 1))
  refine ⟨C, hC, ?_⟩
  intro p q W hq F hF a i c
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q
  let t := (v + A) ^ A + v + 3 * (v + 1) + 2
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hqr : q ≤ t := by
    have hh : 0 ≤ (v + A) ^ A := by positivity
    dsimp [v] at hh
    dsimp [t, v]
    linarith
  have hAr : (p + A) ^ A ≤ t := by
    apply (pow_le_pow_left₀ (by positivity) (show p + A ≤ v + A by dsimp [v]; linarith) A).trans
    dsimp [t]
    linarith
  have hcost : (t + B) ^ B + 6 * (v + 1) ≤ (p + q + C) ^ C := by
    simpa [T, X, t, v, Polynomial.eval₂_pow] using hbudget v hv
  have hterm (b : Fin 2 → Fin W.quadraticRoot.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((t + B) ^ B)
        (fun x => (W.eval i x * star (tensorVector W.quadraticRoot.eval 2 b x)) * F a (b 0, b 1, c) x)) :=
    hmul ht ((Classical.choice ((hequiv W).expansion i b)).mono hAr)
      ((Classical.choice (hF a (b 0, b 1, c))).mono hqr)
  have hcard : (Fintype.card (Fin 2 → Fin W.quadraticRoot.outputDim) : ℝ) ≤ Real.exp (6 * (v + 1)) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp (tensorPowerBudget 2 p) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) W.quadraticRoot.output_bound _
      _ = Real.exp (2 * tensorPowerBudget 2 p) := by
        simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul (tensorPowerBudget 2 p) 2).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        norm_num [tensorPowerBudget]
        dsimp [v]
        linarith
  have hcoeff : (∑ _ : Fin 2 → Fin W.quadraticRoot.outputDim, ‖(1 : ℂ)‖) ≤ Real.exp (6 * (v + 1)) := by
    simpa using hcard
  have E := (NativeIntegerExpansion.weightedSum (fun b => Classical.choice (hterm b))
    (fun _ => (1 : ℂ)) (by positivity : 0 ≤ 6 * (v + 1)) hcard hcoeff).mono hcost
  refine ⟨?_⟩
  change NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + C) ^ C)
    (fun x => W.originalDiagonalCorrection F a i c x)
  simpa only [originalDiagonalCorrection, one_mul] using E

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeComparisonLift
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

theorem CoefficientBases.comparison_space_top_frequency
    (hfreq : V.frequency = B.freeFrequency D) (n : ℕ) (d : Fin n → Fin s)
    (a : FreeMagma (Fin n)) (hd : lieTreeWeight (fun i => (d i).val + 1) a = s)
    (hr : a.length = r) (z : Fin n → Fin 2 → D.CoefficientFreeLieAlgebra)
    (hz : ∀ i, z i ∈ petalComparisonSpace
      ((fourRefinedRelation (D.coefficientFreeSpan (d i)) (D.dependentFreeSpan (d i))
        (D'.coefficientFourSpace ⟨(d i).val + 1, by omega⟩)).map (LinearMap.proj 0))
      (fourPetalSpace (D.dependentFreeSpan (d i))
        (fourRefinedRelation (D.coefficientFreeSpan (d i)) (D.dependentFreeSpan (d i))
          (D'.coefficientFourSpace ⟨(d i).val + 1, by omega⟩)))
      (D.coefficientFreeFiltration.layer ((d i).val + 1) 2)) :
    pairDifferenceFunctional (B.freeFrequency D) (lieTreeEval z a) = 0 := by
  have hC (j : Fin s) :
      (fourRefinedRelation (D.coefficientFreeSpan j) (D.dependentFreeSpan j)
        (D'.coefficientFourSpace ⟨j.val + 1, by omega⟩)).map (LinearMap.proj 0) ≤
          D.coefficientFreeFiltration.layer (j.val + 1) 1 :=
    (refined_firstProjection_le_common _ _ (D.dependentFreeSpan_le_coefficientFreeSpan j) _).trans
      (D.coefficientFreeSpan_le_layer j)
  apply petalComparisonSpace_top_tree D.coefficientFreeFiltration (fun i => (d i).val + 1)
    _ _ (fun i => hC (d i))
    (fun i => (fourPetalSpace_le_first _ _).trans (hC (d i))) (B.freeFrequency D) a hd hr _ z hz
  intro c p hc hp
  apply four_projection_petal_add_invariant
    (fun x => B.freeFrequency D (lieTreeEval x a))
    (fun i => fourRefinedRelation (D.coefficientFreeSpan (d i)) (D.dependentFreeSpan (d i))
      (D'.coefficientFourSpace ⟨(d i).val + 1, by omega⟩))
    (B.correlation_refined_four_identity D E T hbQ hT V g hg D' hfreq n d a hd hr) c p hc
  exact fun i => ((mem_fourPetalSpace _ _ _).mp (hp i)).2

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

theorem comparisonCoefficientSpace_le_layer
    (hTfil : T.filtration = D.coefficientFreeFiltration) (d : Fin s) :
    D.comparisonCoefficientSpace E T hbQ hT V g hg D' d ≤
      (RationalFilteredNilmanifold.piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration.layer
        (d.val + 1) 0 := by
  have hC : (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
      (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0) ≤
      D.coefficientFreeFiltration.layer (d.val + 1) 1 :=
    (refined_firstProjection_le_common _ _ (D.dependentFreeSpan_le_coefficientFreeSpan d) _).trans
      (D.coefficientFreeSpan_le_layer d)
  change petalComparisonSpace _ _ _ ≤
    Submodule.pi Set.univ (fun _ : Fin 2 => T.filtration.layer (d.val + 1) 0)
  rw [hTfil, D.coefficientFreeFiltration.rank_zero_eq_one]
  exact petalComparisonSpace_le_pi _ _ _ _ hC
    ((fourPetalSpace_le_first _ _).trans hC)
    (D.coefficientFreeFiltration.lex_antitone (Or.inr ⟨rfl, by omega⟩))

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_native_comparison_model
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P') :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    let hS := D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil
    ∃ B : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j),
      (∀ j a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => E.basis)).repr
        (B j a : Fin 2 → D.CoefficientFreeLieAlgebra) i) ≤ sharedFreeComparisonBasisBudget Q P') ∧
      let φ := SubspaceFreeLift.evaluation S B (piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration hS
      ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S r) s
          (finrank ℚ (SubspaceFreeLift.Algebra S r)),
        ∃ U : M.DegreeRankStructure r,
          U.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
          U.ComplexityLE (sharedFreeComparisonModelBudget s Q P') ∧ IsCentralLieBasis M.basis ∧
          Nonempty (FreeCoordinateFrame M.basis (sharedFreeComparisonModelBudget s Q P')) ∧
          (∀ i j, rationalLogHeight ((pi (fun _ : Fin 2 => E)).basis.repr
            (φ (M.basis j)) i) ≤ sharedFreeComparisonModelBudget s Q P') ∧
          M.lattice ≤ (pi (fun _ : Fin 2 => E)).lattice.comap (mapOfSteps
            (hL := M.filtration.lowerCentralSeries_eq_bot)
            (hM := (pi (fun _ : Fin 2 => E)).filtration.lowerCentralSeries_eq_bot) φ) ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S r)
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S r) :=
             IsModuleTopology.topologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 M.basis
           ∃ Z : M.UnitVerticalObservable (U.realSubgroup s r)
               (Fin W.family.outputDim × Fin W.family.outputDim) (sharedFreeComparisonModelBudget s Q P'),
             Z.frequency = (pairDifferenceFunctional V.frequency).comp φ.toLinearMap ∧
             ∀ i x, Z.observable i (QuotientGroup.mk x) =
               V.pairedObservable T i (QuotientGroup.mk (realificationMap
                 (hnil := M.filtration.lowerCentralSeries_eq_bot)
                 (hM := (pi (fun _ : Fin 2 => E)).filtration.lowerCentralSeries_eq_bot) φ x))) := by
  intro S hS
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  have hH := sharedFreeComparisonBasisBudget_nonneg hQ hP'
  let K := Q + 2 + sharedFreeComparisonBasisBudget Q P'
  have h2 : 2 ≤ K := by dsimp only [K]; linarith
  have hQK : Q ≤ K := by dsimp only [K]; linarith
  have hHK : sharedFreeComparisonBasisBudget Q P' ≤ K := by dsimp only [K]; linarith
  obtain ⟨B, hB⟩ := D.exists_comparisonCoefficientBases E T hbQ hT F V g hg D' hTfil hs hP' hQP'
  refine ⟨B, hB, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (Fin 2 → D.CoefficientFreeLieAlgebra))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 2 → D.CoefficientFreeLieAlgebra)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (Pi.basis (fun _ : Fin 2 => E.basis))
  exact (SubspaceFreeLift.exists_native_pair_model s).choose_spec.2
    D.CoefficientFreeLieAlgebra (Fin W.family.outputDim) r _ E T S B hS K h2
    (hT.mono T hQK) (fun j a i => (hB j a i).trans hHK) (V.mono hQK)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

theorem exists_native_factored_comparison_orbit
    (hTfil : T.filtration = D.coefficientFreeFiltration) (hs : 1 ≤ s)
    (A K U : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hA0 : E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 A = 1)
    (hK0 : E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 K = 1)
    (hU0 : E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 U = 1)
    (hA : ∀ d : Fin s, coefficients A.log (Finsupp.single () (d.val + 1)) ∈
      ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
        (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ)
    (hK : ∀ d : Fin s, coefficients K.log (Finsupp.single () (d.val + 1)) ∈
      (T.filtration.layer (d.val + 1) 2).baseChange ℝ)
    (hU : ∀ d : Fin s, coefficients U.log (Finsupp.single () (d.val + 1)) ∈
      (fourPetalSpace (D.dependentFreeSpan d)
        (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ) :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    let hS := D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil
    let a : Fin 2 → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1) := ![A * K * U, A]
    ∀ (B : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j))
      (M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S r) s
        (finrank ℚ (SubspaceFreeLift.Algebra S r))) (Q' : M.DegreeRankStructure r),
      Q'.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree →
      let φ := SubspaceFreeLift.evaluation S B
        (RationalFilteredNilmanifold.piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration hS
      ∃ u : M.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
        M.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 u = 1 ∧
        (∀ j : Fin s, coefficients u.log (Finsupp.single () (j.val + 1)) ∈
          (SubspaceFreeLift.generatorSpan S r j).baseChange ℝ) ∧
        ∀ i x, RationalFilteredNilmanifold.productProjectionHom (fun _ : Fin 2 => E) i
          (NilpotentLieBCHGroup.realificationMap (hnil := M.filtration.lowerCentralSeries_eq_bot)
            (hM := (RationalFilteredNilmanifold.pi (fun _ : Fin 2 => E)).filtration.lowerCentralSeries_eq_bot) φ
            (M.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x u)) =
          E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (a i) := by
  intro S hS a B M Q' hQ' φ
  apply SubspaceFreeLift.exists_native_pair_orbit E T S B hS M Q' hQ' a
  · intro i
    fin_cases i
    · change E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (A * K * U) = 1
      rw [map_mul, map_mul, hA0, hK0, hU0, mul_one, mul_one]
    · exact hA0
  · intro j
    have h := D.paired_affine_orbit_coefficient_mem_comparison E T hbQ hT V g hg D'
      hTfil hs A K U hA hK hU j
    have heq : (fun i => coefficients (a i).log (Finsupp.single () (j.val + 1))) =
        ![coefficients (A * K * U).log (Finsupp.single () (j.val + 1)),
          coefficients A.log (Finsupp.single () (j.val + 1))] := by
      funext i
      fin_cases i <;> rfl
    rw [heq]
    exact h

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SharedFreeComparisonKernel
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

theorem CoefficientBases.comparison_free_top_frequency
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B.freeFrequency D) :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    let hS := D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil
    ∀ (J : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j))
      (x : SubspaceFreeLift.Algebra S r),
      x ∈ (SubspaceFreeLift.filtration S T.filtration.rank_le_degree).layer s r →
      pairDifferenceFunctional V.frequency
        (SubspaceFreeLift.evaluation S J
          (RationalFilteredNilmanifold.piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration hS x) = 0 := by
  intro S hS J x hx
  apply FreeDegreeRankLieAlgebra.lift_top_frequency_zero
    (RationalFilteredNilmanifold.piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration
    (SubspaceFreeLift.weight S) (SubspaceFreeLift.weight_pos S)
    (fun a => (J a.1 a.2).val) (fun a => hS a.1 (J a.1 a.2).property)
    (pairDifferenceFunctional V.frequency) _ hx
  intro a hd hr
  classical
  let e := Fintype.equivFin (SubspaceFreeLift.Alphabet S)
  let d : Fin (Fintype.card (SubspaceFreeLift.Alphabet S)) → Fin s := fun i => (e.symm i).1
  let z : Fin (Fintype.card (SubspaceFreeLift.Alphabet S)) → Fin 2 → D.CoefficientFreeLieAlgebra :=
    fun i => (J (e.symm i).1 (e.symm i).2).val
  have hd' : lieTreeWeight (fun i => (d i).val + 1) (FreeMagma.map e a) = s := by
    have heq : (fun i => (d i).val + 1) ∘ e = SubspaceFreeLift.weight S := by
      funext i
      change (e.symm (e i)).1.val + 1 = i.1.val + 1
      rw [e.symm_apply_apply]
    rw [lieTreeWeight_relabel, heq]
    exact hd
  have hr' : (FreeMagma.map e a).length = r := (lieTreeLength_relabel e a).trans hr
  have hz : ∀ i, z i ∈ S (d i) := fun i => (J (e.symm i).1 (e.symm i).2).property
  have h := B.comparison_space_top_frequency D E T hbQ hT V g hg D' hfreq
    (Fintype.card (SubspaceFreeLift.Alphabet S)) d (FreeMagma.map e a) hd' hr' z hz
  have heq : z ∘ e = (fun a : SubspaceFreeLift.Alphabet S => (J a.1 a.2).val) := by
    funext i
    change (J (e.symm (e i)).1 (e.symm (e i)).2).val = (J i.1 i.2).val
    rw [e.symm_apply_apply]
  rw [lieTreeEval_relabel, heq] at h
  rw [hfreq]
  exact h

theorem CoefficientBases.native_comparison_frequency_zero
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B.freeFrequency D) :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    let hS := D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil
    ∀ (J : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j))
      (M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S r) s
        (finrank ℚ (SubspaceFreeLift.Algebra S r))) (U : M.DegreeRankStructure r),
      U.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree →
      ∀ η : SubspaceFreeLift.Algebra S r →ₗ[ℚ] ℚ,
        η = (pairDifferenceFunctional V.frequency).comp
          (SubspaceFreeLift.evaluation S J
            (RationalFilteredNilmanifold.piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration hS).toLinearMap →
        ∀ x ∈ U.filtration.layer s r, η x = 0 := by
  intro S hS J M U hU η hη x hx
  rw [hη]
  change pairDifferenceFunctional V.frequency (SubspaceFreeLift.evaluation S J _ hS x) = 0
  apply B.comparison_free_top_frequency D E T hbQ hT V g hg D' hTfil hfreq J x
  simpa only [hU] using hx

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeFrozenComparison
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B₀ : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem CoefficientBases.exists_covered_comparison
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P')
    (Λ : Subgroup E.filtration.Group) (m : ℕ) (hm : 0 < m)
    (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates E.basis Λ)
    (hout : bchSubgroupCoordinates E.basis Λ ⊆ denominatorGrid m)
    {p₁ : ℝ} (hp₁ : 0 ≤ p₁) (hT₁ : (T.withLattice Λ m hm hin hout).ComplexityLE p₁)
    (V₁ : (E.withLattice Λ m hm hin hout).UnitVerticalObservable
      ((T.withLattice Λ m hm hin hout).realSubgroup s (r + 1)) (Fin W.family.outputDim) p₁)
    (hV₁ : V₁.frequency = V.frequency) :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    let hS := D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil
    let q₁ := p₁ + sharedFreeComparisonBasisBudget Q P' + 2
    let E₁ := E.withLattice Λ m hm hin hout
    let T₁ := T.withLattice Λ m hm hin hout
    let pM := (q₁ + nativePairModelConstant s) ^ nativePairModelConstant s
    ∃ J : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j),
      (∀ j a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => E.basis)).repr
        (J j a : Fin 2 → D.CoefficientFreeLieAlgebra) i) ≤ sharedFreeComparisonBasisBudget Q P') ∧
      let φ := SubspaceFreeLift.evaluation S J (piRank (fun _ : Fin 2 => E₁) (fun _ => T₁)).filtration hS
      ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S (r + 1)) s
          (finrank ℚ (SubspaceFreeLift.Algebra S (r + 1))),
        ∃ U : M.DegreeRankStructure (r + 1),
          U.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
          U.ComplexityLE pM ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1))
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1)) :=
             IsModuleTopology.topologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 M.basis
           ∃ Z : M.UnitVerticalObservable (U.realSubgroup s (r + 1))
               (Fin W.family.outputDim × Fin W.family.outputDim) pM,
             (∀ i x, Z.observable i (QuotientGroup.mk x) =
               V₁.pairedObservable T₁ i (QuotientGroup.mk (realificationMap
                 (hnil := M.filtration.lowerCentralSeries_eq_bot)
                 (hM := (pi (fun _ : Fin 2 => E₁)).filtration.lowerCentralSeries_eq_bot) φ x))) ∧
             M.HasUniformLowerRankUnitFamily U Z.observable (fun _ : Unit => 1)
               (nativeLowerPairModelBudget s q₁)) := by
  intro S hS q₁ E₁ T₁ pM
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  have hB := sharedFreeComparisonBasisBudget_nonneg hQ hP'
  have hq : 2 ≤ q₁ := by dsimp only [q₁]; linarith
  have hpq : p₁ ≤ q₁ := by dsimp only [q₁]; linarith
  have hBq : sharedFreeComparisonBasisBudget Q P' ≤ q₁ := by dsimp only [q₁]; linarith
  obtain ⟨J, hJ⟩ := D.exists_comparisonCoefficientBases E T hbQ hT F V g hg D'
    hTfil hs hP' hQP'
  refine ⟨J, hJ, ?_⟩
  apply SubspaceFreeLift.exists_uniform_lower_pair_model E₁ T₁ S J hS hq
    (hT₁.mono T₁ hpq) (fun j a i => (hJ j a i).trans hBq) (V₁.mono hpq)
  intro x hx
  change pairDifferenceFunctional V₁.frequency
    (SubspaceFreeLift.evaluation S J (piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration hS x) = 0
  rw [hV₁]
  exact B₀.comparison_free_top_frequency D E T hbQ hT V g hg D' hTfil hfreq J x hx

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B₀ : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem CoefficientBases.exists_covered_factored_family {τ : Type*}
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P')
    (Λ : Subgroup E.filtration.Group) (m : ℕ) (hm : 0 < m)
    (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates E.basis Λ)
    (hout : bchSubgroupCoordinates E.basis Λ ⊆ denominatorGrid m)
    {p₁ : ℝ} (hp₁ : 0 ≤ p₁) (hT₁ : (T.withLattice Λ m hm hin hout).ComplexityLE p₁)
    (V₁ : (E.withLattice Λ m hm hin hout).UnitVerticalObservable
      ((T.withLattice Λ m hm hin hout).realSubgroup s (r + 1)) (Fin W.family.outputDim) p₁)
    (hV₁ : V₁.frequency = V.frequency)
    (A K U : τ → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hA0 : ∀ t, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (A t) = 1)
    (hK0 : ∀ t, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (K t) = 1)
    (hU0 : ∀ t, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (U t) = 1)
    (hA : ∀ t (d : Fin s), coefficients (A t).log (Finsupp.single () (d.val + 1)) ∈
      ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
        (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ)
    (hK : ∀ t (d : Fin s), coefficients (K t).log (Finsupp.single () (d.val + 1)) ∈
      (T.filtration.layer (d.val + 1) 2).baseChange ℝ)
    (hU : ∀ t (d : Fin s), coefficients (U t).log (Finsupp.single () (d.val + 1)) ∈
      (fourPetalSpace (D.dependentFreeSpan d)
        (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ) :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    let q₁ := p₁ + sharedFreeComparisonBasisBudget Q P' + 2
    ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S (r + 1)) s
        (finrank ℚ (SubspaceFreeLift.Algebra S (r + 1))),
      ∃ Tm : M.DegreeRankStructure (r + 1),
        Tm.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
        Tm.ComplexityLE ((q₁ + nativePairModelConstant s) ^ nativePairModelConstant s) ∧
        M.HasLowerRankOrbitFamily Tm (fun _ : Unit => 1)
          (fun t (i : Fin W.family.outputDim × Fin W.family.outputDim) x =>
            V₁.observable i.1 (QuotientGroup.mk
              (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (A t * K t * U t))) *
            star (V₁.observable i.2 (QuotientGroup.mk
              (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (A t)))))
          (nativeLowerPairModelBudget s q₁) := by
  intro S q₁
  let E₁ := E.withLattice Λ m hm hin hout
  let T₁ := T.withLattice Λ m hm hin hout
  obtain ⟨J, _, M, Tm, hTm, hTmc, hZ⟩ :=
    B₀.exists_covered_comparison D E T hbQ hT F V g hg D'
      hTfil hfreq hs hP' hQP' Λ m hm hin hout hp₁ hT₁ V₁ hV₁
  refine ⟨M, Tm, hTm, hTmc, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 M.basis
  obtain ⟨Z, hobs, huniform⟩ := hZ
  apply huniform.realizeFamily
  intro t
  obtain ⟨u, hu0, _, hu⟩ := D.exists_native_factored_comparison_orbit E T hbQ hT V g hg D'
    hTfil (by omega) (A t) (K t) (U t) (hA0 t) (hK0 t) (hU0 t) (hA t) (hK t) (hU t)
    J M Tm hTm
  refine ⟨u, hu0, ?_⟩
  intro i x
  exact SubspaceFreeLift.native_pair_observable_eval E₁ T₁ S J
    (D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil)
    M Tm V₁ Z hobs ![A t * K t * U t, A t] u hu i x

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeLowerFactorization
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B₀ : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem CoefficientBases.exists_invariant_native_comparison_model
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P') :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    let hS := D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil
    ∃ B : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j),
      (∀ j a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => E.basis)).repr
        (B j a : Fin 2 → D.CoefficientFreeLieAlgebra) i) ≤ sharedFreeComparisonBasisBudget Q P') ∧
      let φ := SubspaceFreeLift.evaluation S B (piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration hS
      ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S r) s
          (finrank ℚ (SubspaceFreeLift.Algebra S r)),
        ∃ U : M.DegreeRankStructure r,
          U.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
          U.ComplexityLE (sharedFreeComparisonModelBudget s Q P') ∧ IsCentralLieBasis M.basis ∧
          Nonempty (FreeCoordinateFrame M.basis (sharedFreeComparisonModelBudget s Q P')) ∧
          (∀ i j, rationalLogHeight ((pi (fun _ : Fin 2 => E)).basis.repr
            (φ (M.basis j)) i) ≤ sharedFreeComparisonModelBudget s Q P') ∧
          M.lattice ≤ (pi (fun _ : Fin 2 => E)).lattice.comap (mapOfSteps
            (hL := M.filtration.lowerCentralSeries_eq_bot)
            (hM := (pi (fun _ : Fin 2 => E)).filtration.lowerCentralSeries_eq_bot) φ) ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S r)
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S r) :=
             IsModuleTopology.topologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 M.basis
           ∃ Z : M.UnitVerticalObservable (U.realSubgroup s r)
               (Fin W.family.outputDim × Fin W.family.outputDim) (sharedFreeComparisonModelBudget s Q P'),
             Z.frequency = (pairDifferenceFunctional V.frequency).comp φ.toLinearMap ∧
             (∀ x ∈ U.filtration.layer s r, Z.frequency x = 0) ∧
             (∀ i z, z ∈ U.realSubgroup s r → ∀ x, Z.observable i (z • x) = Z.observable i x) ∧
             ∀ i x, Z.observable i (QuotientGroup.mk x) =
               V.pairedObservable T i (QuotientGroup.mk (realificationMap
                 (hnil := M.filtration.lowerCentralSeries_eq_bot)
                 (hM := (pi (fun _ : Fin 2 => E)).filtration.lowerCentralSeries_eq_bot) φ x))) := by
  intro S hS
  obtain ⟨J, hJ, M, U, hU, hUc, hcentral, hframe, hmatrix, hlattice, hZ⟩ :=
    D.exists_native_comparison_model E T hbQ hT F V g hg D' hTfil hs hP' hQP'
  refine ⟨J, hJ, M, U, hU, hUc, hcentral, hframe, hmatrix, hlattice, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S r)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S r) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 M.basis
  obtain ⟨Z, hfreqZ, hobs⟩ := hZ
  have hzero := B₀.native_comparison_frequency_zero D E T hbQ hT V g hg D'
    hTfil hfreq J M U hU Z.frequency hfreqZ
  exact ⟨Z, hfreqZ, hzero,
    (fun i z hz x => Z.rank_invariant_of_frequency_zero U hzero z hz i x), hobs⟩

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B₀ : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem CoefficientBases.exists_uniform_lower_comparison_model
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P') :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    let hS := D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil
    ∃ B : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j),
      (∀ j a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => E.basis)).repr
        (B j a : Fin 2 → D.CoefficientFreeLieAlgebra) i) ≤ sharedFreeComparisonBasisBudget Q P') ∧
      let φ := SubspaceFreeLift.evaluation S B (piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration hS
      ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S (r + 1)) s
          (finrank ℚ (SubspaceFreeLift.Algebra S (r + 1))),
        ∃ U : M.DegreeRankStructure (r + 1),
          U.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
          U.ComplexityLE (sharedFreeComparisonModelBudget s Q P') ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1))
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1)) :=
             IsModuleTopology.topologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 M.basis
           ∃ Z : M.UnitVerticalObservable (U.realSubgroup s (r + 1))
               (Fin W.family.outputDim × Fin W.family.outputDim) (sharedFreeComparisonModelBudget s Q P'),
             (∀ i x, Z.observable i (QuotientGroup.mk x) =
               V.pairedObservable T i (QuotientGroup.mk (realificationMap
                 (hnil := M.filtration.lowerCentralSeries_eq_bot)
                 (hM := (pi (fun _ : Fin 2 => E)).filtration.lowerCentralSeries_eq_bot) φ x))) ∧
             M.HasUniformLowerRankUnitFamily U Z.observable (fun _ : Unit => 1)
               (sharedFreeLowerComparisonBudget s Q P')) := by
  intro S hS
  obtain ⟨J, hJ, M, U, hU, hUc, _, _, _, _, hZ⟩ :=
    B₀.exists_invariant_native_comparison_model D E T hbQ hT F V g hg D'
      hTfil hfreq hs hP' hQP'
  refine ⟨J, hJ, M, U, hU, hUc, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 M.basis
  obtain ⟨Z, _, hzero, _, hobs⟩ := hZ
  refine ⟨Z, hobs, ?_⟩
  have hpM : 0 ≤ sharedFreeComparisonModelBudget s Q P' :=
    (Nat.cast_nonneg _).trans hUc.1.1
  exact UnitVerticalObservable.hasUniformLowerRankUnitFamily M U Z
    (fun _ : Unit => 1) hpM hUc hzero

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LocalPhaseMarkedObservable
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P) (t : ℕ)

noncomputable def markedDependentEvaluation (a : Fin t → ℚ) :
    MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t →ₗ[ℚ] D.DependentQuotient :=
  markedBaseEvaluation D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t (D.dependentWordIdeal 0 2 0) le_rfl a

theorem markedDependentEvaluation_real_map (a : Fin t → ℚ)
    (z : ℝ ⊗[ℚ] markedShiftSubalgebra D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t) :
    (D.markedDependentEvaluation t a).baseChange ℝ
        ((lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ z) =
      D.dependentQuotientMap.toLinearMap.baseChange ℝ
        ((markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent t a).baseChange ℝ z) :=
  markedBaseEvaluation_real_map D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t (D.dependentWordIdeal 0 2 0) le_rfl a z

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MixedSumKernelCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_mixed_kernel_correlation (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 0 ≤ p →
      ∀ (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
        {N : ℕ} [NeZero N] (i j : Fin W.outputDim),
      Real.exp (-p) ≤ (boxPhaseMoment (n + 2) (fun x : Fin (n + 2) → ZMod N =>
        W.mixedAntisymmetric i j (fun k => ((x k).val : ℤ)))).re →
      Nonempty (NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) ((p + C) ^ C)
        Finset.univ (fun x : Fin (n + 2) → ZMod N => fun k => ((x k).val : ℤ))
        (fun x => W.mixedAntisymmetric i j (fun k => ((x k).val : ℤ)))) := by
  obtain ⟨A, _, hanchor⟩ := NativeMultidegreeNilcharacter.exists_mixed_anchor_expansion n
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + (X + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro p hp W N _ i j hbias
  let K := W.mixedAntisymmetric i j
  let Kc := fun x : Fin (n + 2) → ZMod N => K (fun k => ((x k).val : ℤ))
  obtain ⟨a, ha⟩ := exists_box_corner_anchor_correlation Kc
  obtain ⟨E⟩ := hanchor W i j (fun k => ((a k).val : ℤ))
  have hmap (x : Fin (n + 2) → ZMod N) : boxCornerAnchor Kc a x =
      boxCornerAnchor K (fun k => ((a k).val : ℤ)) (fun k => ((x k).val : ℤ)) :=
    boxCornerAnchor_map (fun z : ZMod N => (z.val : ℤ)) K a x
  have hcorr : Real.exp (-p) ≤ ‖𝔼 x : Fin (n + 2) → ZMod N,
      K (fun k => ((x k).val : ℤ)) *
        star (star (boxCornerAnchor K (fun k => ((a k).val : ℤ))
          (fun k => ((x k).val : ℤ))))‖ := by
    have h := hbias.trans ha
    simp_rw [hmap] at h
    simpa only [Kc, star_star] using h
  obtain ⟨S⟩ := NativeSampleCorrelation.exists_of_expansion E.conjugate hp hcorr
  have hcost : p + (p + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨S.mono hcost⟩

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_sum_kernel_correlation (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      {N : ℕ} [NeZero N] (f : ZMod N → ℂ), (∀ x, ‖f x‖ ≤ 1) →
      ∀ (i : Fin W.outputDim) (A : Fin (n + 2) → (Fin (n + 2) → ZMod N) → ℂ),
      (∀ j x, ‖A j x‖ ≤ 1) → (∀ j, MissesBoxCoordinate (A j) j) →
      Real.exp (-p) ≤ ‖𝔼 u : Fin n → ZMod N, 𝔼 m : ZMod N, 𝔼 h : ZMod N,
        f (m + h + ∑ j, u j) * star (W.eval i (mixedSlotInput (h.val : ℤ) m.val (fun j => (u j).val))) *
          ∏ j, A j (Fin.cons h (Fin.cons m u))‖ →
      ∃ j k : Fin W.outputDim,
        Nonempty (NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) ((p + C) ^ C)
          Finset.univ (fun x : Fin (n + 2) → ZMod N => fun l => ((x l).val : ℤ))
          (fun x => W.mixedAntisymmetric j k (fun l => ((x l).val : ℤ)))) := by
  obtain ⟨a, _, hbox⟩ := exists_mixed_sum_antisymmetric_box n
  obtain ⟨b, _, hkernel⟩ := exists_mixed_kernel_correlation n
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a
  let R := X + Q + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p W N _ f hf i A hA hmiss hcorr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + a) ^ a
  let r := p + q + 2
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hpr : p ≤ r := by dsimp only [r]; linarith
  have hqr : q ≤ r := by dsimp only [r]; linarith
  have hr : 0 ≤ r := hp.trans hpr
  obtain ⟨j, k, hmoment⟩ := hbox W f hf i A hA hmiss hcorr
  have hmono (x : Fin (n + 2) → ℤ) :
      (W.mono hpr).mixedAntisymmetric j k x = W.mixedAntisymmetric j k x := rfl
  have hinput : Real.exp (-r) ≤
      (boxPhaseMoment (n + 2) (fun x : Fin (n + 2) → ZMod N =>
        (W.mono hpr).mixedAntisymmetric j k (fun l => (x l).val))).re := by
    simpa only [hmono] using (Real.exp_le_exp.mpr (neg_le_neg hqr)).trans hmoment
  obtain ⟨S⟩ := hkernel hr (W.mono hpr) j k hinput
  have hcost : (r + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, Q, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨j, k, ⟨S.mono hcost⟩⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ActualFixedSpatialGoodPrimeDeletion
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.retainedReferencePrimeNeZero
noncomputable def referenceRetainedModulus (cutoff : ℕ) : ℕ :=
  ∏ p ∈ path.referenceRetainedPrimes cutoff, p.val ^ path.exponent p.val

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end


