-- Prove2me | Definitions.Def_OAIQ075A030
-- name    : OAIQ075A030
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:33:38.574429+00:00
-- url     : https://prove2.me/theorems/7fd006d2-59c0-4156-93c5-fa99f1fc3e94
-- title:
--   Definitions bundle OAIQ075A030 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 29 declarations of OpenAI's Lean: 13 definitions and 16 theorems. The definitions and types are `OAI.KadisonSimilarity.generatedAlgebraCStar`, `OAI.KadisonSimilarity.generatedAlgebraOrder`, `OAI.KadisonSimilarity.generatedGNSNorm`, `OAI.KadisonSimilarity.generatedPreGNSNorm`, `OAI.KadisonSimilarity.grothendieckCorner00`, `OAI.KadisonSimilarity.grothendieckCorner11`, `OAI.KadisonSimilarity.grothendieckEntry`, `OAI.KadisonSimilarity.grothendieckMatrixMap`, `OAI.KadisonSimilarity.grothendieckOffDiagonal`, `OAI.KadisonSimilarity.grothendieckState00`, `OAI.KadisonSimilarity.grothendieckState11`, `OAI.KadisonSimilarity.matrixGNSLiftOperator`, `OAI.KadisonSimilarity.tracialOrthogonalWordLevels`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`KadisonSimilarity_Derivation_GrothendieckMatrix`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Derivation/GrothendieckMatrix.lean), [`KadisonSimilarity_FreeProduct_FreeCreationOperators`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/FreeCreationOperators.lean), [`KadisonSimilarity_FreeProduct_TracialHomCompression`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialHomCompression.lean), [`KadisonSimilarity_FreeProduct_TracialWordIsometry`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialWordIsometry.lean), [`KadisonSimilarity_Tracial_MatrixSmallCorner`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/MatrixSmallCorner.lean), [`KadisonSimilarity_Tracial_UltrapowerGeneratedTransfer`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/Tracial/UltrapowerGeneratedTransfer.lean).
--
--   **Imports.** It imports the published bundle `Def_KadisonSimilarity`; the bundle `OAIQ075A023` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A034` and `OAIQ075A037`; the statement `OAI.KadisonSimilarity.finite_standard_estimate_of_centered_tests`; the proofs of `OAI_KadisonSimilarity_ae_joint_fiber_scalar_center`, `OAI.KadisonSimilarity.dicksonTwoBound_proved`, `OAI.KadisonSimilarity.finite_standard_estimate_of_centered_tests`, `OAI.KadisonSimilarity.list_equal_square_orbit_comparison` and `OAI_KadisonSimilarity_normal_standard_embedding_of_normal_gns`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A023

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_GrothendieckMatrix
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.HochschildMatrixDilation.diag_pow _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.representedDoubleMatrix_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A four-by-four matrix corner supplies unitary norm-attaining tests for
an arbitrary bounded linear map without an additional convexity theorem. -/

noncomputable section
namespace KadisonSimilarity
open HochschildMatrixDilation Filter
open scoped ComplexOrder Topology

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nontrivial A] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Extract an entry with its actual C-star matrix norm bound. -/
def grothendieckEntry (i j : Fin 2) : Mat A →L[ℂ] A :=
  ({ toFun := fun X => X i j
     map_add' := fun X Y => rfl
     map_smul' := fun c X => rfl } : Mat A →ₗ[ℂ] A).mkContinuous 1
    (fun X => by
      change ‖X i j‖ ≤ 1 * ‖X‖
      simpa only [one_mul] using (CStarMatrix.norm_entry_le_norm (M := X) (i := i) (j := j)))

/-- The original map applied to the distinguished off-diagonal entry. -/
def grothendieckMatrixMap (T : A →L[ℂ] H) : Mat (Mat A) →L[ℂ] H :=
  T.comp ((grothendieckEntry 0 1).comp (grothendieckEntry 0 1))

omit [Nontrivial A] in
@[simp] theorem grothendieckMatrixMap_apply (T : A →L[ℂ] H) (X : Mat (Mat A)) :
    grothendieckMatrixMap T X = T (X 0 1 0 1) := rfl

/-- The two diagonal corner maps used for the two states. -/
def grothendieckCorner00 : A →ₗ[ℂ] Mat (Mat A) where
  toFun a := diag (diag a 0) 0
  map_add' a b := by simp only [← diag_add, add_zero]
  map_smul' c a := by simp only [← diag_smul, smul_zero, RingHom.id_apply]

def grothendieckCorner11 : A →ₗ[ℂ] Mat (Mat A) where
  toFun a := diag 0 (diag 0 a)
  map_add' a b := by simp only [← diag_add, add_zero]
  map_smul' c a := by simp only [← diag_smul, smul_zero, RingHom.id_apply]

/-- The distinguished off-diagonal corner. -/
def grothendieckOffDiagonal (a : A) : Mat (Mat A) := offdiag (offdiag a 0) 0

omit [Nontrivial A] in
@[simp] theorem grothendieckOffDiagonal_entry (a : A) :
    grothendieckOffDiagonal a 0 1 0 1 = a := rfl

lemma grothendieck_diag_nonneg {D : Type*} [CStarAlgebra D] [PartialOrder D]
    [StarOrderedRing D] {a b : D} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ diag a b := by
  obtain ⟨c, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  obtain ⟨d, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hb
  rw [← diag_mul, ← star_diag]
  exact star_mul_self_nonneg _

omit [Nontrivial A] in
theorem grothendieckCorner00_nonneg {a : A} (ha : 0 ≤ a) :
    0 ≤ grothendieckCorner00 a :=
  grothendieck_diag_nonneg (grothendieck_diag_nonneg ha le_rfl) le_rfl

omit [Nontrivial A] in
theorem grothendieckCorner11_nonneg {a : A} (ha : 0 ≤ a) :
    0 ≤ grothendieckCorner11 a :=
  grothendieck_diag_nonneg le_rfl (grothendieck_diag_nonneg le_rfl ha)

omit [Nontrivial A] in
@[simp] theorem grothendieckOffDiagonal_star_mul (a : A) :
    star (grothendieckOffDiagonal a) * grothendieckOffDiagonal a =
      grothendieckCorner11 (star a * a) := by
  simp [grothendieckOffDiagonal, grothendieckCorner11, star_offdiag, offdiag_mul]

omit [Nontrivial A] in
@[simp] theorem grothendieckOffDiagonal_mul_star (a : A) :
    grothendieckOffDiagonal a * star (grothendieckOffDiagonal a) =
      grothendieckCorner00 (a * star a) := by
  simp [grothendieckOffDiagonal, grothendieckCorner00, star_offdiag, offdiag_mul]

/-- Restrict the first matrix state to its supporting corner. -/
def grothendieckState11 (f : Mat (Mat A) →ₚ[ℂ] ℂ) : A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (f.toLinearMap.comp grothendieckCorner11)
    (fun _ ha => f.map_nonneg (grothendieckCorner11_nonneg ha))

def grothendieckState00 (f : Mat (Mat A) →ₚ[ℂ] ℂ) : A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (f.toLinearMap.comp grothendieckCorner00)
    (fun _ ha => f.map_nonneg (grothendieckCorner00_nonneg ha))

omit [Nontrivial A] in
@[simp] theorem grothendieckState11_apply (f : Mat (Mat A) →ₚ[ℂ] ℂ) (a : A) :
    grothendieckState11 f a = f (grothendieckCorner11 a) := rfl

omit [Nontrivial A] in
@[simp] theorem grothendieckState00_apply (f : Mat (Mat A) →ₚ[ℂ] ℂ) (a : A) :
    grothendieckState00 f a = f (grothendieckCorner00 a) := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialWordIsometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construction of the completed free-product word inclusions from the
proved Gram identities and totality of elementary tensors. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

theorem tracialWordInclusion_orthogonal (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace D A) (n m : ℕ) (hnm : n ≠ m)
    (x : MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1)) n)
    (y : MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1)) m) :
    inner ℂ (tracialWordInclusion G A D hτ hf n x)
      (tracialWordInclusion G A D hτ hf m y) = 0 := by
  have hp (p : TracialWordParameter G A D n) :
      (innerSL ℂ (tracialWordInclusion G A D hτ hf n (tracialTensorFamily G A D n p))).comp
        (tracialWordInclusion G A D hτ hf m).toContinuousLinearMap = 0 := by
    apply continuousLinearMap_eq_zero_of_total (tracialTensorFamily G A D m)
      (tracialTensorFamily_dense G A D hτ m)
    intro q
    change inner ℂ (tracialWordInclusion G A D hτ hf n (tracialTensorFamily G A D n p))
      (tracialWordInclusion G A D hτ hf m (tracialTensorFamily G A D m q)) = 0
    rw [tracialWordInclusion_family, tracialWordInclusion_family]
    exact inner_reducedWord_ne G A D hτ hf n m hnm p.2.1 q.2.1 p.1.2 q.1.2
      (fun i => (p.1.1 i).1) (fun i => (p.2.2 i).1)
      (fun i => (q.1.1 i).1) (fun i => (q.2.2 i).1)
      (fun i => (p.1.1 i).2) (fun i => (q.1.1 i).2)
      (fun i => (p.2.2 i).2) (fun i => (q.2.2 i).2)
  have hy : (innerSL ℂ (tracialWordInclusion G A D hτ hf m y)).comp
      (tracialWordInclusion G A D hτ hf n).toContinuousLinearMap = 0 := by
    apply continuousLinearMap_eq_zero_of_total (tracialTensorFamily G A D n)
      (tracialTensorFamily_dense G A D hτ n)
    intro p
    apply inner_eq_zero_symm.mp
    exact congrArg (fun f => f y) (hp p)
  apply inner_eq_zero_symm.mp
  exact congrArg (fun f => f x) hy

theorem tracialWordInclusion_dense_span (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace D A) (hgen : ReducedWordGenerated G A D) :
    (Submodule.span ℂ (⋃ n, Set.range (tracialWordInclusion G A D hτ hf n))).topologicalClosure =
      ⊤ := by
  apply top_unique
  rw [← hgen]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  rintro _ ⟨n, d, b, a, c, ha, hc, rfl⟩
  let p : TracialWordParameter G A D n :=
    (((fun i => ⟨a i, ha i⟩), b), (d, (fun i => ⟨c i, hc i⟩)))
  apply Set.mem_iUnion.mpr
  refine ⟨n, tracialTensorFamily G A D n p, ?_⟩
  exact tracialWordInclusion_family G A D hτ hf n p

/-- The completed orthogonal word decomposition, built from freeness. -/
def tracialOrthogonalWordLevels (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace D A) (hgen : ReducedWordGenerated G A D) :
    OrthogonalWordLevels
      (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
        (centeredSubspace (G.baseVector D 1))) H where
  inclusion := tracialWordInclusion G A D hτ hf
  orthogonal := tracialWordInclusion_orthogonal G A D hτ hf
  dense_span := tracialWordInclusion_dense_span G A D hτ hf hgen

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeCreationOperators
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered-letter creation maps on the actual leading-word subspaces. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D B : StarSubalgebra ℂ P)
  [IsClosed (B : Set P)] (side : Bool) (hB : B = if side then A else D)

include hB

theorem freeCreationIsometry_mem (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace A D)
    (z : HilbertTensor (centeredSubspace (G.baseVector B 1))
      (centeredWordSpace G A D (!side))) :
    freeCreationIsometry G A D B side hB hτ hf z ∈ leadingWordSpace G A D side := by
  apply map_mem_of_total (freeCreationTensor G A D B side)
    (freeCreationTensor_total G A D B side hτ)
    (freeCreationIsometry G A D B side hB hτ hf).toContinuousLinearMap
  intro p
  change freeCreationIsometry G A D B side hB hτ hf (freeCreationTensor G A D B side p) ∈
    leadingWordSpace G A D side
  rw [freeCreationIsometry_tensor]
  have hp : (p.1.1 : P) ∈ if side then A else D := by rw [← hB]; exact p.1.1.property
  have hx := AlternatingCenteredWord.cons hp p.1.2 p.2.2
  exact (closedFamilyVector (leadingWordFamily G A D side)
    ⟨⟨(p.1.1 : P) :: p.2.1, hx⟩, List.cons_ne_nil _ _⟩).property

theorem freeCreationIsometry_left (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace A D)
    (a : B) (ha : G.trace (a : P) = 0) (y : centeredWordSpace G A D (!side)) :
    freeCreationIsometry G A D B side hB hτ hf
      (hilbertTensorInsert (G.baseSymmetryLetter B a ha) y) = G.left (a : P) (y : H) := by
  let f := (freeCreationIsometry G A D B side hB hτ hf).toContinuousLinearMap.comp
      (hilbertTensorInsert (G.baseSymmetryLetter B a ha)) -
    (G.left (a : P)).comp (centeredWordSpace G A D (!side)).subtypeL
  have he : f = 0 := continuousLinearMap_eq_zero_of_total
    (closedFamilyVector (centeredWordFamily G A D (!side))) (closedFamilyVector_total _) f (by
      intro xs
      change freeCreationIsometry G A D B side hB hτ hf
          (freeCreationTensor G A D B side (⟨a, ha⟩, xs)) -
        G.left (a : P) (G.vector xs.1.prod) = 0
      rw [freeCreationIsometry_tensor, freeCreationVector, G.left_vector, sub_self])
  exact sub_eq_zero.mp (congrArg (fun f => f y) he)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialHomCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact recovery of a commutator through trace-preserving embeddings.
This is the final direction of the ultrapower transfer: a bound on the
constant subalgebra's compressed commutator bounds the original operator. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (hφ : ∀ a, τB (φ a) = τA a)

local notation "G" => gnsTracialGeometry τB trB

include hφ in
omit [StarOrderedRing A] in
theorem gnsGeometry_preserves_trace :
    ∀ a, (G).trace (φ a) = τA a := hφ

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixSmallCorner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinguished scalar matrix corner has the original algebra's
commutator estimate on a finite standard multiplicity. The proof uses
actual coordinate insertion/projection and then transports the estimate
to the normalized matrix GNS space. -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {n : ℕ} [NeZero n]

omit [PartialOrder A] [StarOrderedRing A] [NeZero n] in
theorem matrixCornerProjection_isStarProjection (i : Fin n) :
    IsStarProjection (matrixCornerProjection (A := A) i) := by
  let E : Matrix (Fin n) (Fin n) A ≃⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A :=
    CStarMatrix.ofMatrixStarAlgEquiv
  constructor
  · change E (Matrix.single i i 1) * E (Matrix.single i i 1) = E (Matrix.single i i 1)
    rw [← map_mul]
    congr 1
    simp
  · change star (E (Matrix.single i i 1)) = E (Matrix.single i i 1)
    rw [← map_star]
    congr 1
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, star_one]

/-- The amplified standard-copy operator transported to matrix GNS. -/
def matrixGNSLiftOperator (τ : A →ₚ[ℂ] ℂ)
    (Y : HilbertCopies τ.GNS n →L[ℂ] HilbertCopies τ.GNS n) :
    (normalizedMatrixTrace τ n).GNS →L[ℂ] (normalizedMatrixTrace τ n).GNS :=
  (matrixGNSUnitary τ n).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((amplify Y n).comp (matrixGNSUnitary τ n).toContinuousLinearEquiv.toContinuousLinearMap)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_UltrapowerGeneratedTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two compressions used in the finite-factor argument are combined
here. The resulting operator on the generated algebra retains commutation,
all prescribed small-corner bounds, and the original commutator norm. -/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower
open scoped ComplexOrder

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hA : τA 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trA : ∀ a b : A, τA (a * b) = τA (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (hφ : ∀ a, τB (φ a) = τA a)

variable (L D : StarSubalgebra ℂ (Ultrapower τB hB ω trB))
  [IsClosed (L : Set (Ultrapower τB hB ω trB))]

local instance generatedAlgebraCStar : CStarAlgebra L := inferInstance
local instance generatedAlgebraOrder : PartialOrder L := inferInstance
local instance generatedAlgebraStarOrder : StarOrderedRing L := inferInstance
local instance generatedPreGNSNorm :
    SeminormedAddCommGroup (restrictedPositiveTrace (quotientTrace τB hB ω trB) L).PreGNS :=
  inferInstance
local instance generatedGNSNorm :
    NormedAddCommGroup (restrictedPositiveTrace (quotientTrace τB hB ω trB) L).GNS :=
  inferInstance

end KadisonSimilarity

end

end OAI
end


