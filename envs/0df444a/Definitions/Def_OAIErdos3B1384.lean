-- Prove2me | Definitions.Def_OAIErdos3B1384
-- name    : OAIErdos3B1384
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-16T04:42:14.573983+00:00
-- url     : https://prove2.me/theorems/8e4fed05-d29f-41da-93bc-15539fbbb5b0
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1385 of 1396
-- statement:
--   Definitions bundle 1385 of 1396 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1383`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1385 available.
--
--   Modules: `OAI.Erdos3.ResidueBoxSlice.fiberSliceLaw_affine_complexMean`, `OAI.Erdos3.ResidueBoxSlice.fiberSliceLaw_affine_sum_complexMean`, `OAI.Erdos3.ResidueBoxSlice.fiberSliceLaw_complexMean`, `OAI.Erdos3.VectorPolynomial.allocatedCoveredFixedTest_measurable`, `OAI.Erdos3.VectorPolynomial.allocatedCoveredFixedTest_norm_le`, `OAI.Erdos3.VectorPolynomial.allocatedMixedJetReconstruct_measurable`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleFullSliceMap_eq_eval`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleInactiveCoefficients_supported`, `OAI.Erdos3.VectorPolynomial.allocatedPartitionedJetMatrix_image_eq_of_residue_both`, `OAI.Erdos3.VectorPolynomial.allocatedPartitionedJetMatrix_residue_both`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalDeckJet_law_eq_of_residue_both`, `OAI.Erdos3.VectorPolynomial.allocatedResidueLabel_card`, `OAI.Erdos3.VectorPolynomial.allocatedResidueLabels_le_exp`, `OAI.Erdos3.VectorPolynomial.allocatedSampleRestrictedProfileNoise_short_abs_le`, `OAI.Erdos3.VectorPolynomial.allocatedShortIntegerSelection_small`, `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedDeck_law_constant`, `OAI.Erdos3.VectorPolynomial.allocatedWholeJetMatrix_kernel_range_le`, `OAI.Erdos3.VectorPolynomial.coefficientDeckJetDensity_integral`, `OAI.Erdos3.VectorPolynomial.coefficientJetAxisEquiv_measurePreserving`, `OAI.Erdos3.VectorPolynomial.coefficientJetAxisSplit_measurePreserving`, `OAI.Erdos3.VectorPolynomial.coefficientLatticeBasis_card_le`, `OAI.Erdos3.containedProgressionResidueLaw_label_eq`, `OAI.Erdos3.containedProgressionResidueLaw_matrix`, `OAI.Erdos3.containedProgressionResidueLaw_mean`, `OAI.Erdos3.containedSupportedProgressionLaw_integral_comparison`, `OAI.Erdos3.containedSupportedProgressionLaw_partition`, `OAI.Erdos3.containedSupportedProgressionLaw_partition_comparison`, `OAI.Erdos3.polynomialPerturbationScale_antitone`, `OAI.Erdos3.principalAffineIntervalLaw_complexMean`, `OAI.Erdos3.principalResidueCell_pos_of_cube`, `OAI.Erdos3.principalTupleWeights_weight_pos_of_cube`, `OAI.Erdos3.retained_density_nested_test_error`, `OAI.Erdos3.slicedEndpointUniformScale_spec`, `OAI.Erdos3.slicedPrincipalBoundaryRadius_antitone`, `OAI.Erdos3.slicedPrincipalC2Tolerance_antitone`, `OAI.Erdos3.slicedPrincipalC2Tolerance_pos_le_one`, `OAI.Erdos3.slicedPrincipalComparisonBudget_mono`, `OAI.Erdos3.uniformDependentFin_expect`, `OAI.Erdos3.uniformDependentSum_expect`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1376
import Definitions.Def_OAIErdos3B1383

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedWholeDeckLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v w : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "root" z => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x z
local notation "dirs" z => allocatedPhysicalCubeDirections B U b S x z

omit [∀ j, Fintype (O j)] in
theorem allocatedWholeJetMatrix_kernel_range_le (j : Fin m) :
    (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range ≤
      (boundedCoefficientJetMatrix (root y) (dirs y) (j.val + 1) (rows j)).mulVecLin.range := by
  have h := allocatedPartitionedJetMatrix_kernel_range_le B U b S x
    (principalAxisRestrict grid y) (principalAxisRestrict (fun a => ¬grid a) y) rows j
  rw [allocatedPartitionedJetMatrix_eq_physical, principalAxisJoin_restrict] at h
  exact h

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCoveredFixedTest
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]

theorem coefficientDeckJetDensity_integral
    (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
    (d : ℕ) [NeZero d] (φ : (∀ j, O j → B j → ZMod d) → ℂ) :
    (∫ r, φ (coefficientDeckJetMap root A rows d r)
      ∂(PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure) =
    ∫ r, (coefficientDeckJetDensity root A rows d r : ℂ) * φ r
      ∂(PMF.uniformOfFintype (∀ j, O j → B j → ZMod d)).toMeasure := by
  rw [finitePMF_integral_comp _ (coefficientDeckJetMap root A rows d) φ,
    coefficientDeckJetDensity_law root A rows d,
    realDensityMeasure_integral_complex _ _ (measurable_of_finite _)
      (coefficientDeckJetDensity_nonneg root A rows d)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v w : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "axis" => coefficientJetAxisEquiv O I n
local notation "join" => MeasurableEquiv.piEquivPiSubtypeProd (CoefficientJetAxisRow O) grid

theorem allocatedMixedJetReconstruct_measurable [∀ j, Fintype (O j)] :
    Measurable (fun p : AllocatedFrozenCoefficients B U b S × AllocatedLongJetRows B U b S O =>
      allocatedMixedJetReconstruct B U b S x u w rows p.1 p.2) :=
  (axis).symm.measurable.comp ((join).symm.measurable.comp
    (((allocatedFrozenJetMap_measurable B U b S x u w rows).comp measurable_fst).prodMk measurable_snd))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α) (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)
variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

variable (φ : (AllocatedFrozenCoefficients B U b S ×
  (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))) × (∀ j, O j → Q j → ZMod d) → ℂ)

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : AllocatedFrozenCoefficients B U b S × EuclideanJetLayers U O → ℂ)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "pullback" => (fun p : (AllocatedFrozenCoefficients B U b S ×
  (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))) × (∀ j, O j → Q j → ZMod d) =>
  F (Prod.fst (Prod.fst p), coveredJetChart U b hb bW d
    (mixedCoveredJetCoordinates U o d (Prod.snd (Prod.fst p), Prod.snd p))))

omit [Fintype α] [∀ j, DecidableEq (O j)] in
theorem allocatedCoveredFixedTest_measurable (hF : Measurable F) :
    Measurable (fun p : AllocatedFrozenCoefficients B U b S × AllocatedLongJetRows B U b S O =>
      allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d F p.1 p.2) :=
  (allocatedDeckMixedTest_measurable B U b S x u v₀ rows Q d pullback
    (allocatedCoveredPullback_measurable B U b S Q hb o bW d F hF)).comp
      (measurable_fst.prodMk (allocatedMixedJetReconstruct_measurable B U b S x u v₀ rows))

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedCoveredFixedTest_norm_le {C : ℝ} (hF : ∀ p, ‖F p‖ ≤ C)
    (a₀ : AllocatedFrozenCoefficients B U b S) (z : AllocatedLongJetRows B U b S O) :
    ‖allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d F a₀ z‖ ≤ C :=
  allocatedDeckMixedTest_norm_le B U b S x u v₀ rows Q d pullback (fun _ => hF _) a₀ _

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ContainedFullIntervalResidueIdentity
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (modulus : ℕ) (hm : 0 < modulus)
variable (r : PrincipalTupleIndex B h → Option α → ZMod modulus)
variable (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)

local notation "weights" => principalResidueWeights B h H hH modulus hm r hsize

theorem containedProgressionResidueLaw_mean (f : (JointBlockParameter B h α → ℝ) → ℝ) :
    (containedProgressionResidueLaw B h L H step c hL hH hsubset modulus hm r hsize).mean
        (fun v => f (principalTupleNormalized L v)) =
      (weights).mean (fun v => f (principalTupleFlatten B h α
        (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j))) := by
  exact containedProgressionTupleLaw_mean B h L H step c hL hsubset weights
    (principalResidueWeights_cube_support B h H hH modulus hm r hsize) f

theorem containedProgressionResidueLaw_matrix {Z K I N : Type*}
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ JointBlockParameter B h α)
    (z : Z → ℤ) (rows : I → Finset α)
    (v v₀ : PrincipalIntegerTuples B h α L)
    (hv : (containedProgressionResidueLaw B h L H step c hL hH hsubset modulus hm r hsize).weight v ≠ 0)
    (hv₀ : (containedProgressionResidueLaw B h L H step c hL hH hsubset modulus hm r hsize).weight v₀ ≠ 0) :
    integerResidueMatrix (integerMappedJetMatrix e input z rows (principalTupleIntegers v)) modulus =
      integerResidueMatrix (integerMappedJetMatrix e input z rows (principalTupleIntegers v₀)) modulus := by
  apply integerMappedJetMatrix_residue
  funext a
  change ((v ⟨a.1,a.2.1,a.2.2.1⟩ a.2.2.2 : ℤ) : ZMod modulus) =
    ((v₀ ⟨a.1,a.2.1,a.2.2.1⟩ a.2.2.2 : ℤ) : ZMod modulus)
  rw [containedProgressionResidueLaw_support B h L H step c hL hH hsubset modulus hm r hsize v hv,
    containedProgressionResidueLaw_support B h L H step c hL hH hsubset modulus hm r hsize v₀ hv₀]

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem containedProgressionResidueLaw_label_eq
    {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
    (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (modulus : ℕ) (hm : 0 < modulus)
    (r : PrincipalTupleIndex B h → Option α → ZMod modulus)
    (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)
    (v v₀ : PrincipalIntegerTuples B h α L)
    (hv : (containedProgressionResidueLaw B h L H step c hL hH hsubset modulus hm r hsize).weight v ≠ 0)
    (hv₀ : (containedProgressionResidueLaw B h L H step c hL hH hsubset modulus hm r hsize).weight v₀ ≠ 0) :
    principalResidueLabel modulus v = principalResidueLabel modulus v₀ := by
  funext j i
  exact (containedProgressionResidueLaw_support B h L H step c hL hH hsubset modulus hm r hsize v hv j i).trans
    (containedProgressionResidueLaw_support B h L H step c hL hH hsubset modulus hm r hsize v₀ hv₀ j i).symm

end Erdos3

end

section

namespace Erdos3

open scoped Classical NNReal

variable {D α : Type*} [Fintype α] [DecidableEq α]
variable (B : D → Type*) (h : D → ℕ)
variable (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hsize : ∀ t, (Fintype.card α + 1) * q ≤ L t)

variable [Fintype D] [DecidableEq D] [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hsize : ∀ t, (Fintype.card α + 1) * q ≤ L t) (a : D)


end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hsize : ∀ t, (Fintype.card α + 1) * q ≤ L t) (a : D)
variable (c : B a → NormalizedScalarCubeSource Empty) (rows : Finset (Finset α))
variable (offset : B a → ℤ) (shift : rows → ℤ)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (H : PrincipalTupleIndex B h → ℕ) (hH : ∀ j, 0 < H j)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleQuadratureUniformBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "grid" => allocatedShortAxis (I := I) U basis S.value
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

include hR hσ in
theorem allocatedSampleRestrictedProfileNoise_short_abs_le (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (e : ActiveProfileCoefficientIndex G B degree grid) :
    |allocatedSampleRestrictedProfileNoise B U basis S grid sample e| ≤ 1 := by
  rcases e with ⟨⟨⟨j, i⟩, ha⟩, e⟩
  have hrows := (mixedArraySupported_iff_rows _ _ _ (sample j)).mp (hs j)
  cases i with
  | inl i =>
    exact allocatedSampleProfileNoise_continuous_bound B U basis hR hσ S sample j i (hrows.1 i) e
  | inr i =>
    exact allocatedSampleProfileNoise_active_integer_bound B U basis hR hσ S sample j i
      (Nat.lt_of_not_ge ha) (hrows.2 i) e

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

include hR hσ in
theorem allocatedOriginalSampleInactiveCoefficients_supported
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample j)) :
    ∀ a d, allocatedOriginalSampleInactiveCoefficients B selected sample a d ∈
      (allocatedLayerIntegerPMFs B U b hR hσ S (selected a).1 (selected a).2 d).support := by
  intro a d
  exact ((mixedArraySupported_iff_rows _ _ _ (sample (selected a).1)).mp
    (hs (selected a).1)).2 (selected a).2 d

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

theorem allocatedShortIntegerSelection_small (a : AllocatedShortIntegerAxis U b L) :
    basisAxisScale (b (allocatedShortIntegerSelection U b L a).1)
      (allocatedShortIntegerSelection U b L a).2 ≤
      L ^ ((allocatedShortIntegerSelection U b L a).1.val + 1) := a.property

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "activeB" => (fun a : Active => B (Subtype.val a))
local notation "activeDegree" => (fun a : Active => degree (Subtype.val a))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "Active" => {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleFullSliceLipschitz
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n
local notation "sides" => allocatedPrincipalSides B U basis S

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))
variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

theorem allocatedOriginalSampleFullSliceMap_eq_eval (sample : Sample) (y : Input → ℝ) (o : Output) :
    allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y o =
      MvPolynomial.eval (allocatedOriginalSampleSliceInput B U basis S x u lower width y)
        (monomialArrayPolynomial Subtype.val (allocatedSampleNormalizedCoefficients B U basis S sample o.1.val)) /
          R o.1.val.1 := by
  simp only [allocatedOriginalSampleFullSliceMap, allocatedOriginalSampleSliceSubstitution_eval]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JetAxisReference
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {m : ℕ} (O I : Fin m → Type*) (n : Fin m → ℕ)
variable [∀ j, Fintype (O j)] [∀ j, Fintype (I j)]

theorem coefficientJetAxisEquiv_measurePreserving :
    MeasurePreserving (coefficientJetAxisEquiv O I n)
      (Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j)))
      (Measure.pi (coefficientJetAxisReference O)) := by
  let laws := coefficientJetAxisReference (I := I) (n := n) O
  have hinner (j : Fin m) : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi
        (fun a : I j ⊕ Fin (n j) => CoefficientJetAxisRow O ⟨j, a⟩)).symm
      (mixedArrayReference (I j) (Fin (n j)) (O j))
      (Measure.pi (fun a : I j ⊕ Fin (n j) => laws ⟨j, a⟩)) := by
    have hc : (Measure.pi (fun _ : Fin (n j) => (Measure.count : Measure (O j → ℤ)))) =
        Measure.count := pi_count_measure
    have h := measurePreserving_sumPiEquivProdPi_symm
      (fun a : I j ⊕ Fin (n j) => laws ⟨j, a⟩)
    change MeasurePreserving _
      ((Measure.pi (fun _ : I j => (volume : Measure (O j → ℝ)))).prod
        (Measure.pi (fun _ : Fin (n j) => (Measure.count : Measure (O j → ℤ))))) _ at h
    rw [hc] at h
    change MeasurePreserving _
      ((volume : Measure (I j → O j → ℝ)).prod
        (Measure.count : Measure (Fin (n j) → O j → ℤ))) _
    rw [volume_pi]
    exact h
  have houter := measurePreserving_pi
    (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))
    (fun j => Measure.pi (fun a : I j ⊕ Fin (n j) => laws ⟨j, a⟩)) hinner
  have hflat : MeasurePreserving
      (MeasurableEquiv.piCurry
        (fun j (a : I j ⊕ Fin (n j)) => CoefficientJetAxisRow O ⟨j, a⟩)).symm
      (Measure.pi (fun j => Measure.pi (fun a : I j ⊕ Fin (n j) => laws ⟨j, a⟩)))
      (Measure.pi laws) :=
    ⟨(MeasurableEquiv.piCurry
      (fun j (a : I j ⊕ Fin (n j)) => CoefficientJetAxisRow O ⟨j, a⟩)).symm.measurable,
      sigmaFiniteProductMeasure_flatten laws⟩
  exact hflat.comp houter

theorem coefficientJetAxisSplit_measurePreserving
    (P : LayerSamplerAxis I n → Prop) [DecidablePred P] :
    MeasurePreserving (coefficientJetAxisSplit O I n P)
      (Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j)))
      ((Measure.pi (fun a : {a // P a} => coefficientJetAxisReference O a.val)).prod
        (Measure.pi (fun a : {a // ¬P a} => coefficientJetAxisReference O a.val))) :=
  (measurePreserving_piEquivPiSubtypeProd (coefficientJetAxisReference O) P).comp
    (coefficientJetAxisEquiv_measurePreserving O I n)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedResidueLabelCount
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {n : Fin m → ℕ}
variable {J E : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

include hb bW in
theorem allocatedResidueLabel_card (period : ℕ) [NeZero period] :
    Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) =
      period ^ (∑ j, Fintype.card (J j)) := by
  have hc (j) : n j + Fintype.card (E j) = Fintype.card (J j) := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using
      standardLatticeCoordinates_card (euclideanSubspace (U j)) (bW j) (b j) (hb j)
  simp only [Fintype.card_prod, Fintype.card_pi, ZMod.card,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.prod_mul_distrib]
  simp_rw [← pow_add, hc]
  exact Finset.prod_pow_eq_pow_sum _ _ _

include hb bW in
theorem allocatedResidueLabels_le_exp {S : Type*} [Fintype S]
    (period : ℕ) [NeZero period] {P : ℝ} (hperiod : (period : ℝ) ≤ Real.exp P) :
    (Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^ Fintype.card S ≤
      Real.exp (Fintype.card S * ((∑ j, Fintype.card (J j) : ℕ) * P)) := by
  rw [allocatedResidueLabel_card U b hb bW, Nat.cast_pow, Real.exp_nat_mul, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by positivity)
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hperiod _) _

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PrincipalCubeSupportedCell
namespace OAI

section

namespace Erdos3
open scoped Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (P : D → Prop) [DecidablePred P]

local notation "BP" => (fun a : {a // P a} => B (Subtype.val a))
local notation "hP" => (fun a : {a // P a} => h (Subtype.val a))
local notation "embed" => (fun j : PrincipalTupleIndex BP hP => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B h))

end Erdos3

end

section

namespace Erdos3
open scoped Classical BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (P : D → Prop) [DecidablePred P]

local notation "BP" => (fun a : {a // P a} => B (Subtype.val a))
local notation "hP" => (fun a : {a // P a} => h (Subtype.val a))
local notation "embed" => (fun j : PrincipalTupleIndex BP hP => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B h))
local notation "conditioned" => FiniteProbabilityWeights.condition (principalTupleWeights B h H hH)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

theorem containedSupportedProgressionLaw_partition (f : PrincipalIntegerTuples B h α L → ℂ) :
    (containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell).complexMean f =
      (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).complexMean (fun u =>
        (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell (fun a => ¬P a)).complexMean
          (fun v => f (principalAxisJoin P u v))) := by
  let w := principalSupportedCoordinateWeights B h H hH q r hcell
  let map := containedProgressionTupleMap (α := α) B h L H step c hL hsubset
  let wL := FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex BP hP => w (embed j))
  let wR := FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex
    (fun a : {a // ¬P a} => B a.val) (fun a => h a.val) => w ⟨j.1.val,j.2⟩)
  let mapL := containedProgressionTupleMap (α := α) BP hP (principalAxisLength P L) (principalAxisLength P H)
    (principalAxisLength P step) (fun j => c (embed j)) (fun j => hL (embed j)) (fun j => hsubset (embed j))
  let mapR := containedProgressionTupleMap (α := α) (fun a : {a // ¬P a} => B a.val) (fun a => h a.val)
    (principalAxisLength (fun a => ¬P a) L) (principalAxisLength (fun a => ¬P a) H)
    (principalAxisLength (fun a => ¬P a) step) (fun j => c ⟨j.1.val,j.2⟩)
    (fun j => hL ⟨j.1.val,j.2⟩) (fun j => hsubset ⟨j.1.val,j.2⟩)
  have hjoin (u : PrincipalAxisTuples (α := α) P H) (v : PrincipalAxisTuples (α := α) (fun a => ¬P a) H) :
      map (principalAxisJoin P u v) = principalAxisJoin P (mapL u) (mapR v) := by
    funext j
    rcases j with ⟨a, bv⟩
    by_cases ha : P a <;>
      simp only [map, mapL, mapR, containedProgressionTupleMap, principalAxisJoin, ha, ↓reduceDIte] <;> rfl
  have hpart := principalCoordinateWeights_partition P H w (fun y => f (map y))
  have hpart' := hpart.trans (congrArg (fun g => wL.complexMean g) (funext (fun u =>
    congrArg (fun g => wR.complexMean g) (funext (fun v => congrArg f (hjoin u v))))))
  have hleft := (conditioned).fiberLaw_complexMean map f
  have hright := wL.fiberLaw_complexMean mapL (fun u =>
    (wR.fiberLaw mapR).complexMean (fun v => f (principalAxisJoin P u v)))
  have hinner (u : PrincipalAxisTuples (α := α) P L) :=
    wR.fiberLaw_complexMean mapR (fun v => f (principalAxisJoin P u v))
  have hright' := hright.trans (congrArg (fun g => wL.complexMean g)
    (funext (fun u => hinner (mapL u))))
  exact hleft.trans ((congrArg (fun p => p.complexMean (fun y => f (map y)))
    (principalSupportedResidueWeights_eq_pi B h H hH q r hcell)).trans (hpart'.trans hright'.symm))

theorem containedSupportedProgressionLaw_partition_comparison
    (f : PrincipalIntegerTuples B h α L → ℂ) (g : PrincipalAxisTuples (α := α) P L → ℂ) {E : ℝ}
    (hpoint : ∀ u,
      (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).weight u ≠ 0 →
      ‖(containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell (fun a => ¬P a)).complexMean
        (fun v => f (principalAxisJoin P u v)) - g u‖ ≤ E) :
    ‖(containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell).complexMean f -
      (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).complexMean g‖ ≤ E := by
  rw [containedSupportedProgressionLaw_partition B h L H step c hL hH hsubset q r hcell P f]
  exact ((containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).norm_complexMean_sub_le
    _ _ (fun _ => E) hpoint).trans_eq (FiniteProbabilityWeights.mean_const _ E)

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped Classical BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (P : D → Prop) [DecidablePred P]

local notation "BP" => (fun a : {a // P a} => B (Subtype.val a))
local notation "hP" => (fun a : {a // P a} => h (Subtype.val a))
local notation "embed" => (fun j : PrincipalTupleIndex BP hP => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B h))

theorem containedSupportedProgressionLaw_integral_comparison
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → PrincipalIntegerTuples B h α L → ℂ) (hf : ∀ y, Integrable (fun p => f p y) μ)
    (g : PrincipalAxisTuples (α := α) P L → ℂ) {E : ℝ}
    (hpoint : ∀ u,
      (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).weight u ≠ 0 →
      ‖(∫ p, (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell (fun a => ¬P a)).complexMean
        (fun v => f p (principalAxisJoin P u v)) ∂μ) - g u‖ ≤ E) :
    ‖(∫ p, (containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell).complexMean (f p) ∂μ) -
      (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).complexMean g‖ ≤ E := by
  rw [FiniteProbabilityWeights.integral_complexMean _ μ f hf]
  apply containedSupportedProgressionLaw_partition_comparison B h L H step c hL hH hsubset q r hcell P
  intro u hu
  have he := (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell (fun a => ¬P a)).integral_complexMean
    μ (fun p v => f p (principalAxisJoin P u v)) (fun v => hf (principalAxisJoin P u v))
  exact he ▸ hpoint u hu

end Erdos3

end

section

namespace Erdos3
open scoped Classical BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)

theorem principalTupleWeights_weight_pos_of_cube (y : PrincipalIntegerTuples B h α L)
    (hy : ∀ j, IntegerScalarCube (L j) (fun a => (y j a : ℤ))) :
    0 < (principalTupleWeights B h L hL).weight y := by
  apply Finset.prod_pos
  intro j _
  apply (FiniteProbabilityWeights.condition_weight_pos_iff _ _ _ (y j)).mpr
  refine ⟨(mem_integerScalarCubeSet (L j) (y j)).mpr (hy j), ?_⟩
  let : Nonempty (IntegerScalarCubeBox α (L j)) := ⟨y j⟩
  change 0 < (Fintype.card (IntegerScalarCubeBox α (L j)) : ℝ)⁻¹
  positivity

theorem principalResidueCell_pos_of_cube (q : ℕ) (y : PrincipalIntegerTuples B h α L)
    (hy : ∀ j, IntegerScalarCube (L j) (fun a => (y j a : ℤ))) :
    0 < (principalTupleWeights B h L hL).mass
      (Finset.univ.filter (fun z => principalResidueLabel q z = principalResidueLabel q y)) := by
  apply lt_of_lt_of_le (principalTupleWeights_weight_pos_of_cube B h L hL y hy)
  exact Finset.single_le_sum (fun z _ => (principalTupleWeights B h L hL).nonneg z)
    (by simp : y ∈ Finset.univ.filter (fun z => principalResidueLabel q z = principalResidueLabel q y))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UniformDependentSumCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem uniformDependentSum_expect
    {G P : Type*} [Fintype G] [Fintype P] [DecidableEq G] [DecidableEq P]
    (A : G ⊕ P → Type*) [∀ k, Fintype (A k)] (f : (∀ k, A k) → ℂ) :
    (𝔼 u : ∀ k, A k, f u) =
      𝔼 g : ∀ i, A (Sum.inl i), 𝔼 p : ∀ j, A (Sum.inr j), f (Sum.rec g p) := by
  calc
    _ = 𝔼 gp : (∀ i, A (Sum.inl i)) × (∀ j, A (Sum.inr j)), f (Sum.rec gp.1 gp.2) := by
      apply Fintype.expect_equiv (Equiv.sumPiEquivProdPi A)
      intro u
      congr 1
      funext k
      cases k <;> rfl
    _ = _ := by
      simpa only [Finset.univ_product_univ] using
        Finset.expect_product' (Finset.univ : Finset (∀ i, A (Sum.inl i)))
          (Finset.univ : Finset (∀ j, A (Sum.inr j)))
          (fun g p => f (Sum.rec g p))

theorem uniformDependentFin_expect
    {G P : Type*} [Fintype G] [Fintype P] [DecidableEq G] [DecidableEq P]
    (L : G ⊕ P → ℕ) (f : (∀ k, Fin (L k)) → ℂ) :
    (𝔼 u : ∀ k, Fin (L k), f u) =
      𝔼 g : ∀ i, Fin (L (Sum.inl i)), 𝔼 p : ∀ j, Fin (L (Sum.inr j)), f (Sum.rec g p) :=
  uniformDependentSum_expect (fun k => Fin (L k)) f

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RelativeSliceAffineThreeFactorLaw
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {keep : X → Prop} [DecidablePred keep] {N : X → ℕ} {q : ℕ}

theorem fiberSliceLaw_complexMean
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (test : integerBox N → ℂ) :
    (S.fiberSliceLaw hlen fixed hfixed).complexMean test =
      𝔼 u, test (S.fiberPointInBox fixed hfixed u) := by
  let : ∀ k, Nonempty (Fin (S.length k)) := fun k => ⟨⟨0, hlen k⟩⟩
  exact FiniteProbabilityWeights.uniform_finitePushforward_complexMean _ _

theorem fiberSliceLaw_affine_complexMean
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (test : integerBox N → ℂ) :
    (S.fiberSliceLaw hlen fixed hfixed).complexMean test =
      𝔼 v : (∀ i, Fin (S.fiberParameterLength i)), test (S.fiberAffinePointInBox fixed hfixed v) := by
  rw [fiberSliceLaw_complexMean]
  apply Fintype.expect_equiv S.fiberFullParameterEquiv
  intro u
  congr 1
  apply Subtype.ext
  change S.fiberIntegerPoint fixed u =
    S.fiberAffineIntegerPoint fixed (S.fiberFullParameterEquiv u)
  rw [fiberAffineIntegerPoint_eq]
  exact congrArg (S.fiberIntegerPoint fixed) (S.fiberFullParameterEquiv.left_inv u).symm

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (start : PrincipalTupleIndex B h → ℤ)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < L j)

variable (hH : ∀ j, 0 < H j)

theorem principalAffineIntervalLaw_complexMean (f : PrincipalIntegerTuples B h Empty L → ℂ) :
    (principalAffineIntervalLaw B h L H step start hinside hH).complexMean f =
      𝔼 t : (∀ j, Fin (H j)), f (principalAffineIntervalPoint B h L H step start hinside t) := by
  let : ∀ j, Nonempty (Fin (H j)) := fun j => ⟨⟨0, hH j⟩⟩
  exact FiniteProbabilityWeights.uniform_finitePushforward_complexMean _ _

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {keep : X → Prop} [DecidablePred keep] {N : X → ℕ} {q : ℕ}

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {G P : Type*} [Fintype G] [Fintype P] [DecidableEq G] [DecidableEq P]
variable {keep : G ⊕ P → Prop} [DecidablePred keep] {N : G ⊕ P → ℕ} {q : ℕ}

theorem fiberSliceLaw_affine_sum_complexMean
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (test : integerBox N → ℂ) :
    (S.fiberSliceLaw hlen fixed hfixed).complexMean test =
      𝔼 g : (∀ i, Fin (S.fiberParameterLength (Sum.inl i))),
        𝔼 p : (∀ j, Fin (S.fiberParameterLength (Sum.inr j))),
          test (S.fiberAffinePointInBox fixed hfixed (Sum.rec g p)) := by
  rw [fiberSliceLaw_affine_complexMean]
  exact uniformDependentFin_expect S.fiberParameterLength _

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ)

variable {keep : PrincipalTupleIndex B h → Prop} [DecidablePred keep] {q : ℕ}
variable (S : ResidueBoxSlice (fun j : {j // keep j} => L j.val) q)
variable (hlen : ∀ j, 0 < S.length j)
variable (fixed : {j // ¬keep j} → ℤ)
variable (hfixed : ∀ j, 0 ≤ fixed j ∧ fixed j < (L j.val : ℤ))

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {G P : Type*} [Fintype G] [Fintype P] [DecidableEq G] [DecidableEq P]
variable {keep : G ⊕ P → Prop} [DecidablePred keep] {N : G ⊕ P → ℕ} {q : ℕ}

end Erdos3.ResidueBoxSlice

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSupportedSlicedResidue
namespace OAI

section

namespace Erdos3
open scoped Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (H : PrincipalTupleIndex B h → ℕ) (hH : ∀ j, 0 < H j)

variable (L step : PrincipalTupleIndex B h → ℕ) (start : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < L j)
variable (hsubset : ∀ j, integerProgressionSupport (start j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (start : PrincipalTupleIndex B h → ℤ)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < L j)
variable (hH : ∀ j, 0 < H j) (P : D → Prop)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : ℕ) (hM : 0 < M)
variable (r : PrincipalTupleIndex
  (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
  (fun a => layerSamplerDegree I n a.val) → Option α → ZMod M)
variable (hsize : ∀ d, (Fintype.card α + 1) * M ≤
  principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
    (allocatedPrincipalSides B U b S) d)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
local notation "grid" => allocatedGridAxis (I := I) U b S.value
variable (u u₀ : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (v v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α) (q : ℕ)
variable (hu : principalResidueLabel q u = principalResidueLabel q u₀)
variable (hv : principalResidueLabel q v = principalResidueLabel q v₀)

include hu hv

theorem allocatedPartitionedJetMatrix_residue_both (j : Fin m) :
    integerResidueMatrix (allocatedPartitionedJetMatrix B U b S x u v rows j) q =
      integerResidueMatrix (allocatedPartitionedJetMatrix B U b S x u₀ v₀ rows j) q := by
  apply integerMappedJetMatrix_residue_both
  · funext z
    cases z with
    | inl z => rfl
    | inr z => exact congrFun (congrArg principalTupleResidues hu) z
  · exact congrArg principalTupleResidues hv

variable [∀ j, Fintype (O j)]

theorem allocatedPartitionedJetMatrix_image_eq_of_residue_both
    (hperiod : ∀ j, integerScalarLattice (O j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range) (j : Fin m) :
    (allocatedPartitionedJetMatrix B U b S x u v rows j).mulVecLin.range =
      (allocatedPartitionedJetMatrix B U b S x u₀ v₀ rows j).mulVecLin.range := by
  apply integerMatrixImage_eq_of_residueMatrix _ _ q
  · exact (hperiod j).trans (allocatedPartitionedJetMatrix_kernel_range_le B U b S x u v rows j)
  · exact (hperiod j).trans (allocatedPartitionedJetMatrix_kernel_range_le B U b S x u₀ v₀ rows j)
  · exact allocatedPartitionedJetMatrix_residue_both B U b S x u u₀ v v₀ rows q hu hv j

theorem allocatedPhysicalDeckJet_law_eq_of_residue_both
    (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
    (hperiod : ∀ j, integerScalarLattice (O j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (d : ℕ) [NeZero d] :
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).map
      (coefficientDeckJetMap (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) rows d) =
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).map
      (coefficientDeckJetMap (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u₀ v₀))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u₀ v₀)) rows d) := by
  have hr (j : Fin m) :
      (boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) (j.val + 1) (rows j)).mulVecLin.range =
      (boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u₀ v₀))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u₀ v₀)) (j.val + 1) (rows j)).mulVecLin.range := by
    rw [← allocatedPartitionedJetMatrix_eq_physical B U b S x u v rows j,
      ← allocatedPartitionedJetMatrix_eq_physical B U b S x u₀ v₀ rows j]
    exact allocatedPartitionedJetMatrix_image_eq_of_residue_both B U b S x u u₀ v v₀ rows q hu hv hperiod j
  exact uniformPMF_map_hom_eq_of_range_eq _ _
    (coefficientDeckJetMap_range_eq_of_integer_range_eq
      (α := α) (K := LayerSamplerVariables G I n B) (O := O) (B := Q) _ _ rows _ _ hr d)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) ((allocatedPrincipalSides B U b S) j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (u u₀ : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (hu : ((containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell (allocatedGridAxis (I := I) U b S.value))).weight u ≠ 0) (hu₀ : ((containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell (allocatedGridAxis (I := I) U b S.value))).weight u₀ ≠ 0)
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

include hu hu₀

variable [∀ j, Fintype (O j)]

theorem allocatedSupportedSlicedDeck_law_constant
    (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
    (hperiod : ∀ j, integerScalarLattice (O j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (d : ℕ) [NeZero d] :
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).map
      (coefficientDeckJetMap (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v₀))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v₀)) rows d) =
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).map
      (coefficientDeckJetMap (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u₀ v₀))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u₀ v₀)) rows d) := by
  have hlabel := containedSupportedProgressionAxisLaw_residue_eq B (layerSamplerDegree I n) sides H step c
    (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid u u₀ hu hu₀
  exact allocatedPhysicalDeckJet_law_eq_of_residue_both B U b S x u u₀ v₀ v₀ rows q hlabel rfl Q hperiod d

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RetainedDensityNestedTest
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem retained_density_nested_test_error {Z X : Type*}
    [MeasurableSpace Z] [MeasurableSpace X]
    (μ : Measure Z) [IsProbabilityMeasure μ] (ν : Measure X) [SigmaFinite ν]
    (f g : X → ℝ) (hf : Integrable f ν) (hg : Integrable g ν)
    (φ : Z × X → ℂ) (hφ : Measurable φ) {B : ℝ} (hb : ∀ p, ‖φ p‖ ≤ B) :
    ‖(∫ z, ∫ x, (f x : ℂ) * φ (z, x) ∂ν ∂μ) -
      ∫ z, ∫ x, (g x : ℂ) * φ (z, x) ∂ν ∂μ‖ ≤ B * ∫ x, |f x - g x| ∂ν := by
  have hfi := integrable_snd_probability μ ν f hf
  have hgi := integrable_snd_probability μ ν g hg
  have hF : Integrable (fun p : Z × X => (f p.2 : ℂ) * φ p) (μ.prod ν) :=
    hfi.ofReal.mul_bdd hφ.aestronglyMeasurable (ae_of_all _ hb)
  have hG : Integrable (fun p : Z × X => (g p.2 : ℂ) * φ p) (μ.prod ν) :=
    hgi.ofReal.mul_bdd hφ.aestronglyMeasurable (ae_of_all _ hb)
  rw [← integral_prod _ hF, ← integral_prod _ hG]
  have he := density_bounded_complex_test_error (μ.prod ν) (fun p => f p.2) (fun p => g p.2)
    hfi hgi φ hφ hb
  rwa [integral_snd_probability μ ν (fun x => |f x - g x|) (hf.sub hg).abs] at he

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalJetCoverCancellation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d period : ℕ) [NeZero d] [NeZero period]
variable (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)

include hperiod

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset α)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

theorem coefficientLatticeBasis_card_le {m : ℕ} {J Q : Fin m → Type*}
    [∀ j, Fintype (J j)] [∀ j, Fintype (Q j)] {n : Fin m → ℕ}
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (j : Fin m) : Fintype.card (Q j) ≤ Fintype.card (J j) := by
  have h := standardLatticeCoordinates_card (euclideanSubspace (U j)) (bW j) (b j) (hb j)
  rw [Fintype.card_sum, Fintype.card_fin] at h
  omega

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

end Erdos3.VectorPolynomial

namespace Erdos3.BooleanCubeKernel

open Module Submodule VectorPolynomial
open scoped BigOperators Classical NNReal

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SlicedToleranceMonotonicity
namespace OAI

section

namespace Erdos3

theorem slicedPrincipalBoundaryRadius_antitone {N N' : ℕ} (hN : N ≤ N')
    {η : ℝ} (hη : 0 ≤ η) :
    slicedPrincipalBoundaryRadius N' η ≤ slicedPrincipalBoundaryRadius N η := by
  unfold slicedPrincipalBoundaryRadius
  apply min_le_min le_rfl
  apply div_le_div_of_nonneg_left hη (by positivity)
  gcongr

theorem slicedPrincipalComparisonBudget_mono {N N' m : ℕ} (hN : N ≤ N')
    {C A r r' κ κ' : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hr' : 0 < r') (hr : r' ≤ r) (hκ' : 0 < κ') (hκ : κ' ≤ κ) :
    slicedPrincipalComparisonBudget N m C A r κ ≤
      slicedPrincipalComparisonBudget N' m C A r' κ' := by
  have hri : 0 < r := hr'.trans_le hr
  have hκi : 0 < κ := hκ'.trans_le hκ
  have hi : κ⁻¹ ≤ κ'⁻¹ := inv_anti₀ hκ' hκ
  unfold slicedPrincipalComparisonBudget
  gcongr

theorem polynomialPerturbationScale_antitone {K K' M Q Q' τ : ℝ} {O O' : ℕ}
    (hK : 0 ≤ K) (hKK : K ≤ K') (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hQQ : Q ≤ Q')
    (hO : O ≤ O') :
    polynomialPerturbationScale K' M Q' τ O' ≤ polynomialPerturbationScale K M Q τ O := by
  unfold polynomialPerturbationScale
  apply min_le_min le_rfl
  apply min_le_min
  · apply div_le_div_of_nonneg_left zero_le_one (by positivity)
    gcongr
  · apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    gcongr

theorem slicedPrincipalC2Tolerance_antitone {N N' O O' m : ℕ} (hN : N ≤ N') (hO : O ≤ O')
    {C a δ A η : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hδ : 0 < δ) (hA : 0 ≤ A) (hη : 0 < η) :
    slicedPrincipalC2Tolerance N' O' m C a δ A η ≤ slicedPrincipalC2Tolerance N O m C a δ A η := by
  let r := slicedPrincipalBoundaryRadius N η
  let r' := slicedPrincipalBoundaryRadius N' η
  have hr : 0 < r := (slicedPrincipalBoundaryRadius_spec N hη).1
  have hr' : 0 < r' := (slicedPrincipalBoundaryRadius_spec N' hη).1
  have hrr : r' ≤ r := slicedPrincipalBoundaryRadius_antitone hN hη.le
  let κ := a * δ * (δ * r) ^ m
  let κ' := a * δ * (δ * r') ^ m
  have hκ : 0 < κ := mul_pos (mul_pos ha hδ) (pow_pos (mul_pos hδ hr) _)
  have hκ' : 0 < κ' := mul_pos (mul_pos ha hδ) (pow_pos (mul_pos hδ hr') _)
  have hκκ : κ' ≤ κ := by
    dsimp only [κ, κ']
    gcongr
  exact polynomialPerturbationScale_antitone (inv_nonneg.mpr hκ.le) (inv_anti₀ hκ' hκκ)
    zero_le_one (slicedPrincipalComparisonBudget_nonneg N m hC hA hr hκ)
    (slicedPrincipalComparisonBudget_mono hN hC hA hr' hrr hκ' hκκ) hO

theorem slicedPrincipalC2Tolerance_pos_le_one (N O m : ℕ)
    {C a δ A η : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hδ : 0 < δ) (hA : 0 ≤ A) (hη : 0 < η) :
    0 < slicedPrincipalC2Tolerance N O m C a δ A η ∧
      slicedPrincipalC2Tolerance N O m C a δ A η ≤ 1 := by
  let r := slicedPrincipalBoundaryRadius N η
  have hr : 0 < r := (slicedPrincipalBoundaryRadius_spec N hη).1
  have hκ : 0 < a * δ * (δ * r) ^ m := mul_pos (mul_pos ha hδ) (pow_pos (mul_pos hδ hr) _)
  have ht := polynomialPerturbationScale_spec (inv_nonneg.mpr hκ.le) zero_le_one
    (slicedPrincipalComparisonBudget_nonneg N m hC hA hr hκ) (half_pos hη) O
  exact ⟨ht.1, ht.2.1⟩

theorem slicedEndpointUniformScale_spec (N O m : ℕ)
    {a δ A η : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hA : 0 ≤ A) (hη : 0 < η) :
    let t := slicedPolynomialScale N O N m m 1 1 a δ A η
    0 < t ∧ t ≤ 1 ∧
      ∀ (N' O' : ℕ), N' ≤ N → O' ≤ O → ∀ s : ℝ, |s| ≤ t →
        |s| * polynomialMassC2Budget N' m 1 ≤ slicedPrincipalC2Tolerance N' O' m 1 a δ A η := by
  let ε := slicedPrincipalC2Tolerance N O m 1 a δ A η
  have hε := slicedPrincipalC2Tolerance_pos_le_one N O m zero_le_one ha hδ hA hη
  have hM : 0 ≤ polynomialMassC2Budget N m 1 := polynomialMassC2Budget_nonneg N m zero_le_one
  have ht : 0 < ε / (1 + polynomialMassC2Budget N m 1) := div_pos hε.1 (by positivity)
  have htε : ε / (1 + polynomialMassC2Budget N m 1) ≤ ε := div_le_self hε.1.le (by linarith)
  refine ⟨ht, htε.trans hε.2, ?_⟩
  intro N' O' hN hO s hs
  have hMN : polynomialMassC2Budget N' m 1 ≤ polynomialMassC2Budget N m 1 := by
    unfold polynomialMassC2Budget
    gcongr
  have hh := (le_div_iff₀ (by positivity : 0 < 1 + polynomialMassC2Budget N m 1)).mp hs
  have hsmall : |s| * polynomialMassC2Budget N m 1 ≤ ε := by nlinarith [abs_nonneg s]
  exact ((mul_le_mul_of_nonneg_left hMN (abs_nonneg s)).trans hsmall).trans
    (slicedPrincipalC2Tolerance_antitone hN hO zero_le_one ha hδ hA hη)

end Erdos3

end

end OAI

end


