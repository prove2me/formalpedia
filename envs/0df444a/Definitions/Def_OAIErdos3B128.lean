-- Prove2me | Definitions.Def_OAIErdos3B128
-- name    : OAIErdos3B128
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T06:58:27.768408+00:00
-- url     : https://prove2.me/theorems/3fb7d354-bc0b-4c83-9310-f34c2d05b27d
-- title:
--   OpenAI Erdős-3 split, definitions bundle 129 of 132
-- statement:
--   Definitions bundle 129 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B127`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 129 available.
--
--   Modules: `OAI.Erdos3.DilationBudget.niltest_complexity`, `OAI.Erdos3.FiniteProbabilityWeights.prod_reweightPositive_mean_le_of_conditional`, `OAI.Erdos3.MultilinearityBudget.niltest_complexity`, `OAI.Erdos3.MultilinearityBudget.reconstructionExponent`, `OAI.Erdos3.MultilinearityBudget.reconstructionExponent_control`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_freezing_niltest`, `OAI.Erdos3.NativeTwoVariableSplit.exists_second_expansion_budget`, `OAI.Erdos3.NativeTwoVariableSplit.first_eval_eq`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.DownsetSplittingStatement`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.TwoDownsetSplittingStatement`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_controlled_frozen_niltest`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_controlled_multidegree_basepoint_normalization`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_multidegree_downset_splitting`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_two_downset_splitting`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.freezingExponent`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.freezingExponent_control`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.freezingExponent_ge_two`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_basepoint_normalization`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_group_normalization`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_normalized_common_correlators`, `OAI.Erdos3.RationalHorizontalLift.casesOn`, `OAI.Erdos3.VectorPolynomial.MixedCoveredJetSource`, `OAI.Erdos3.VectorPolynomial.coefficientDeckPeriodCap`, `OAI.Erdos3.VectorPolynomial.coefficientDeckPeriodCap_nonneg`, `OAI.Erdos3.VectorPolynomial.coefficientDeckSiteMask`, `OAI.Erdos3.VectorPolynomial.coefficientDeckSmallPeriodDensity`, `OAI.Erdos3.VectorPolynomial.coefficientJetAxisSplit`, `OAI.Erdos3.VectorPolynomial.coveredBooleanSiteValue`, `OAI.Erdos3.VectorPolynomial.coveredJetArrayReference`, `OAI.Erdos3.VectorPolynomial.coveredJetArrayScale`, `OAI.Erdos3.VectorPolynomial.coveredJetArrayScale_pos`, `OAI.Erdos3.VectorPolynomial.coveredJetReference`, `OAI.Erdos3.VectorPolynomial.coveredRowsSiteValue`, `OAI.Erdos3.VectorPolynomial.mixedCoveredJetChart`, `OAI.Erdos3.VectorPolynomial.mixedCoveredJetCoordinates`, `OAI.Erdos3.VectorPolynomial.mixedCoveredJetCoordinatesEquiv`, `OAI.Erdos3.VectorPolynomial.mixedCoveredJetEquiv`, `OAI.Erdos3.VectorPolynomial.mixedCoveredJetIntegerImage`, `OAI.Erdos3.VectorPolynomial.mixedCoveredJetRawReference`, `OAI.Erdos3.VectorPolynomial.mixedCoveredJetRawReference_isFiniteMeasureOnCompacts`, `OAI.Erdos3.VectorPolynomial.mixedCoveredJetRegion`, `OAI.Erdos3.VectorPolynomial.mixedCoveredRowsOfSites`, `OAI.Erdos3.VectorPolynomial.mixedCoveredRowsSiteValue`, `OAI.Erdos3.VectorPolynomial.mixedCoveredSiteArray`, `OAI.Erdos3.allocated_native_approximation_error`, `OAI.Erdos3.assemble_rational_horizontal_lift`, `OAI.Erdos3.euclideanDerivative_horizontal_lifts`, `OAI.Erdos3.euclideanDerivative_horizontal_norm_bound`, `OAI.Erdos3.euclideanVerticalMap_norm_eq`, `OAI.Erdos3.exists_basis_linear_lift`, `OAI.Erdos3.graph_derivative_decomposition`, `OAI.Erdos3.indexed_derivative_decomposition`, `OAI.Erdos3.positiveProjectionAccuracy_mass_bound`, `OAI.Erdos3.positiveProjectionAccuracy_normalizer`, `OAI.Erdos3.rowRestrictedSiteMatrix`, `OAI.Erdos3.selectedJointDensityMass`, `OAI.Erdos3.selectedJointDensityMass_bounds`, `OAI.Erdos3.selectedJointDensityMass_close`, `OAI.Erdos3.selectedJointDensityMass_positive_accuracy`, `OAI.Erdos3.selectedJointFiniteLaw`, `OAI.Erdos3.selectedJointFiniteLaw_complexMean`, `OAI.Erdos3.selectedJointFiniteLaw_conditional_event_le`, `OAI.Erdos3.selectedJointFiniteLaw_weight`, `OAI.Erdos3.selectedJointReference`, `OAI.Erdos3.selectedJointReference_densityMass`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B049
import Definitions.Def_OAIErdos3B124

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredJetReference
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical

namespace VectorPolynomial

variable {m : ℕ} {O J B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coveredJetReference (d : ℕ) [NeZero d] :
    Measure (CoveredJetChartSource U O B n d) :=
  Measure.pi (fun j => Measure.pi (fun _ : O j =>
    normalizedCoveredReference (R := B j) (n := n j) (euclideanSubspace (U j)) d))

variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end VectorPolynomial

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CoveredJetSampler
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical Matrix

namespace VectorPolynomial

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def mixedCoveredJetCoordinates (d : ℕ)
    (p : (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) ×
      (∀ j, O j → B j → ZMod d)) : CoveredJetChartSource U O B n d :=
  fun j t => (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (p.1 j) t), p.2 j t)

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

variable [∀ j, Fintype (B j)]
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

variable [∀ j, Fintype (O j)]

end VectorPolynomial

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoveredChart
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped Classical

abbrev MixedCoveredJetSource {m : ℕ} (I O E : Fin m → Type*) (n : Fin m → ℕ) (d : ℕ) :=
  (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) × (∀ j, O j → E j → ZMod d)

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def mixedCoveredJetCoordinatesEquiv (d : ℕ) :
    MixedCoveredJetSource I O E n d ≃ CoveredJetChartSource U O E n d where
  toFun := mixedCoveredJetCoordinates U o d
  invFun z := (fun j => (mixedArrayRegroup (I j) (Fin (n j)) (O j)).symm
    (fun t => (orthonormalMixedChart (o j)).symm (z j t).1), fun j t => (z j t).2)
  left_inv z := by
    apply Prod.ext
    · funext j
      simp only [mixedCoveredJetCoordinates, MeasurableEquiv.symm_apply_apply]
    · rfl
  right_inv z := by
    funext j t
    simp only [mixedCoveredJetCoordinates, MeasurableEquiv.apply_symm_apply]

variable [∀ j, Fintype (E j)]
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

noncomputable def mixedCoveredJetChart : MixedCoveredJetSource I O E n d → EuclideanJetLayers U O :=
  fun z => coveredJetChart U b hb bW d (mixedCoveredJetCoordinates U o d z)

def mixedCoveredJetRegion (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j))) :
    Set (MixedCoveredJetSource I O E n d) :=
  mixedCoveredJetCoordinates U o d ⁻¹' coveredJetSourceRegion U b d Ω

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MixedCoveredIntegerReconstruction
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

variable {D Q : Type*} [Fintype D] [Fintype Q] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (bW : Basis Q ℤ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup)
variable (d : ℕ) [NeZero d]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {I O P J Q : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (Q j)]

noncomputable def mixedCoveredJetIntegerImage (d : ℕ)
    (A : ∀ j, Matrix (P j) (O j) ℤ) (z : MixedCoveredJetSource I O Q n d) :
    MixedCoveredJetSource I P Q n d :=
  (fun j => mixedArrayIntegerImage (A j) (z.1 j),
    fun j t k => ∑ r, A j t r • z.2 j r k)

variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RowRestrictedDeckSiteMask
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

noncomputable def coefficientDeckPeriodCap {m : ℕ} (O B : Fin m → Type*)
    [∀ j, Fintype (O j)] [∀ j, Fintype (B j)] (period : ℕ) : ℝ :=
  ∏ j, ∏ _i : B j, (period : ℝ) ^ Fintype.card (O j)

theorem coefficientDeckPeriodCap_nonneg {m : ℕ} (O B : Fin m → Type*)
    [∀ j, Fintype (O j)] [∀ j, Fintype (B j)] (period : ℕ) :
    0 ≤ coefficientDeckPeriodCap O B period := by
  unfold coefficientDeckPeriodCap
  positivity

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
variable (d period : ℕ) [NeZero d]

noncomputable def coefficientDeckSmallPeriodDensity
    (r : ∀ j, O j → B j → ZMod period) : ℝ :=
  ∏ j, ∏ i : B j, uniformResidueSmallPeriodDensity
    (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) d period (fun t => r j t i)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
variable (d period : ℕ) [NeZero d] [NeZero period]

noncomputable def coefficientDeckSiteMask
    (r : Finset α → ∀ j, B j → ZMod period) : ℝ :=
  coefficientDeckSmallPeriodDensity root D rows d period (fun j t i =>
    (integerResidueMatrix (booleanJetExtractionMatrix (rows j)) period *ᵥ (fun s => r s j i)) t)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {I J Q : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] [∀ j, Fintype (Q j)]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))

variable (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coveredBooleanSiteValue
    (y : EuclideanJetLayers U jets) (s : Finset α) : EuclideanJetLayers U (fun _ => Unit) :=
  fun j _ => ∑ r, boundedBooleanReconstructionMatrix α (j.val + 1) s r • y j r

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def rowRestrictedSiteMatrix (rows : Finset (Finset α)) :
    Matrix (Finset α) rows ℤ := fun s t => booleanReconstructionMatrix α s t.val

namespace VectorPolynomial

open Module Submodule

variable {m : ℕ} {I J E : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rows" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

noncomputable def mixedCoveredRowsSiteValue (d : ℕ)
    (z : MixedCoveredJetSource I rows E n d) (s : Finset α) :
    MixedCoveredJetSource I (fun _ => Unit) E n d :=
  mixedCoveredJetIntegerImage d (fun j (_ : Unit) => rowRestrictedSiteMatrix (rowSets j) s) z

variable (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coveredRowsSiteValue (y : EuclideanJetLayers U rows) (s : Finset α) :
    EuclideanJetLayers U (fun _ => Unit) :=
  fun j _ => ∑ t, rowRestrictedSiteMatrix (rowSets j) s t • y j t

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped Classical BigOperators Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (root : K → ℤ) (D : Matrix α K ℤ)
variable (d period : ℕ) [NeZero d] [NeZero period]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α (Fin.val j + 1))
local notation "rows" => (fun j : Fin m => (Subtype.val : jets j → Finset α))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace VectorPolynomial

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace VectorPolynomial

variable {K : Type*} [Fintype K] {m : ℕ}
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (root : K → ℤ) (D : Matrix α K ℤ)
variable (rowSets : Fin m → Finset (Finset α))
variable (d period : ℕ) [NeZero d] [NeZero period]

local notation "rows" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rowMap" => (fun j => (Subtype.val : rows j → Finset α))

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PositiveDensityNormalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {B K I : Type*} [Fintype K] [Fintype I]
variable (A : Finset B) (hA : A.Nonempty)
variable (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
variable (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)

noncomputable def selectedJointDensityMass (D : B → (K × I → ℤ) → ℝ) : ℝ :=
  𝔼 a ∈ A, selectedResidueDensityMass modulus T W (D a)

noncomputable def selectedJointReference :
    FiniteProbabilityWeights (A × rectangularWeightIndices 0 W 1) :=
  (FiniteProbabilityWeights.uniformFinset A hA).prod (selectedResidueFiniteLaw modulus T W hW hZ)

theorem selectedJointReference_densityMass (D : B → (K × I → ℤ) → ℝ) :
    (selectedJointReference A hA modulus T W hW hZ).mean (fun z => D z.1.val z.2.val) =
      selectedJointDensityMass A modulus T W D := by
  rw [selectedJointReference, FiniteProbabilityWeights.mean_prod]
  simp_rw [selectedResidueFiniteLaw_densityMass]
  exact FiniteProbabilityWeights.uniformFinset_mean A hA
    (fun a => selectedResidueDensityMass modulus T W (D a))

include hA in
theorem selectedJointDensityMass_bounds (D : B → (K × I → ℤ) → ℝ) {a b : ℝ}
    (hD : ∀ x, selectedResidueDensityMass modulus T W (D x) ∈ Set.Icc a b) :
    selectedJointDensityMass A modulus T W D ∈ Set.Icc a b := by
  rw [selectedJointDensityMass, ← FiniteProbabilityWeights.uniformFinset_mean A hA]
  exact (FiniteProbabilityWeights.uniformFinset A hA).mean_mem_Icc _ (fun x => hD x.val)

include hA in
theorem selectedJointDensityMass_close (D : B → (K × I → ℤ) → ℝ) {ε : ℝ}
    (hD : ∀ x, |selectedResidueDensityMass modulus T W (D x)-1| ≤ ε) :
    |selectedJointDensityMass A modulus T W D-1| ≤ ε := by
  rw [selectedJointDensityMass, ← FiniteProbabilityWeights.uniformFinset_mean A hA]
  exact (FiniteProbabilityWeights.uniformFinset A hA).abs_mean_sub_const_le _ 1 ε (fun x => hD x.val)

noncomputable def selectedJointFiniteLaw (D : B → (K × I → ℤ) → ℝ)
    (hD0 : ∀ a z, 0 ≤ D a z) (hD : 0 < selectedJointDensityMass A modulus T W D) :
    FiniteProbabilityWeights (A × rectangularWeightIndices 0 W 1) :=
  (selectedJointReference A hA modulus T W hW hZ).reweightPositive
    (fun z => D z.1.val z.2.val) (fun z => hD0 z.1.val z.2.val)
    (by rw [selectedJointReference_densityMass]; exact hD)

theorem selectedJointFiniteLaw_weight (D : B → (K × I → ℤ) → ℝ)
    (hD0 : ∀ a z, 0 ≤ D a z) (hD : 0 < selectedJointDensityMass A modulus T W D)
    (z : A × rectangularWeightIndices 0 W 1) :
    (selectedJointFiniteLaw A hA modulus T W hW hZ D hD0 hD).weight z =
      (A.card : ℝ)⁻¹ * (selectedResidueSmoothPMF modulus T W hW hZ z.2.val).toReal *
        D z.1.val z.2.val / selectedJointDensityMass A modulus T W D := by
  rw [selectedJointFiniteLaw, FiniteProbabilityWeights.reweightPositive_weight,
    selectedJointReference_densityMass, selectedResidueSmoothPMF_toReal]
  simp only [selectedJointReference, FiniteProbabilityWeights.prod,
    FiniteProbabilityWeights.uniformFinset, FiniteProbabilityWeights.uniform, Fintype.card_coe,
    selectedResidueFiniteLaw, finiteSupportProbability]

theorem selectedJointFiniteLaw_complexMean (D : B → (K × I → ℤ) → ℝ)
    (hD0 : ∀ a z, 0 ≤ D a z) (hD : 0 < selectedJointDensityMass A modulus T W D)
    (f : B → (K × I → ℤ) → ℂ) :
    (selectedJointFiniteLaw A hA modulus T W hW hZ D hD0 hD).complexMean
      (fun z => f z.1.val z.2.val) =
      (selectedJointReference A hA modulus T W hW hZ).normalizedDensityTest
        (fun z => D z.1.val z.2.val) (fun z => f z.1.val z.2.val) := by
  rw [selectedJointFiniteLaw, FiniteProbabilityWeights.reweightPositive_complexMean_eq_normalizedDensityTest]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

namespace FiniteProbabilityWeights

theorem prod_reweightPositive_mean_le_of_conditional
    {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (D : X × Y → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hglobal : 0 < (p.prod q).mean D)
    (hlocal : ∀ x, 0 < q.mean (fun y => D (x, y)))
    (f : X × Y → ℝ) {ε : ℝ}
    (hbound : ∀ x,
      (q.reweightPositive (fun y => D (x, y)) (fun y => hD0 (x, y)) (hlocal x)).mean
        (fun y => f (x, y)) ≤ ε) :
    ((p.prod q).reweightPositive D hD0 hglobal).mean f ≤ ε := by
  have hraw (x) : q.mean (fun y => D (x, y) * f (x, y)) ≤
      ε * q.mean (fun y => D (x, y)) := by
    exact (div_le_iff₀ (hlocal x)).mp (by simpa only [reweightPositive_mean] using hbound x)
  rw [reweightPositive_mean]
  apply (div_le_iff₀ hglobal).mpr
  rw [mean_prod, mean_prod]
  calc
    _ ≤ p.mean (fun x => ε * q.mean (fun y => D (x, y))) := p.mean_mono hraw
    _ = _ := by
      change (∑ x, p.weight x * (ε * q.mean (fun y => D (x, y)))) =
        ε * ∑ x, p.weight x * q.mean (fun y => D (x, y))
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

end FiniteProbabilityWeights

theorem selectedJointFiniteLaw_conditional_event_le
    {B K I : Type*} [Fintype K] [Fintype I]
    (A : Finset B) (hA : A.Nonempty)
    (modulus : I → ℕ) (cells : Finset (ColumnResiduePattern K I modulus))
    (width : K × I → ℝ) (hwidth : ∀ z, 0 < width z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus cells width z)
    (D : B → (K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
    (hD : 0 < selectedJointDensityMass A modulus cells width D)
    (hlocal : ∀ a, 0 < selectedResidueDensityMass modulus cells width (D a))
    (event : B → (K × I → ℤ) → Prop) {ε : ℝ}
    (hbound : ∀ a,
      (∑' z, (selectedResidueDensityPMF modulus cells width hwidth hZ
        (D a) (hD0 a) (hlocal a) z).toReal * (if event a z then 1 else 0)) ≤ ε) :
    (selectedJointFiniteLaw A hA modulus cells width hwidth hZ D hD0 hD).mean
      (fun z => if event z.1.val z.2.val then 1 else 0) ≤ ε := by
  let p := FiniteProbabilityWeights.uniformFinset A hA
  let q := selectedResidueFiniteLaw modulus cells width hwidth hZ
  have hlocal' (a : A) : 0 < q.mean (fun z => D a.val z.val) := by
    rw [selectedResidueFiniteLaw_densityMass]
    exact hlocal a.val
  have hglobal : 0 < (p.prod q).mean (fun z => D z.1.val z.2.val) := by
    change 0 < (selectedJointReference A hA modulus cells width hwidth hZ).mean _
    rw [selectedJointReference_densityMass]
    exact hD
  apply FiniteProbabilityWeights.prod_reweightPositive_mean_le_of_conditional p q
    (fun z => D z.1.val z.2.val) (fun z => hD0 z.1.val z.2.val) hglobal hlocal'
    (fun z => if event z.1.val z.2.val then 1 else 0)
  intro a
  change (selectedResidueTiltedFiniteLaw modulus cells width hwidth hZ
    (D a.val) (hD0 a.val) (hlocal a.val)).mean (fun z => if event a.val z.val then 1 else 0) ≤ ε
  rw [selectedResidueTiltedFiniteLaw_mean modulus cells width hwidth hZ (D a.val)
    (hD0 a.val) (hlocal a.val) (fun z => if event a.val z then 1 else 0)]
  exact hbound a.val

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {B K I : Type*} [Fintype K] [Fintype I]
variable (A : Finset B) (hA : A.Nonempty)
variable (modulus : I → ℕ) (cells : Finset (ColumnResiduePattern K I modulus))
variable (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus cells W z)
variable (D : B → (K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
variable (hD : 0 < selectedJointDensityMass A modulus cells W D)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {B K I Y : Type*} [Fintype K] [Fintype I] [Fintype Y]
variable (A : Finset B) (hA : A.Nonempty)
variable (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
variable (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
variable (D : B → (K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
variable (hD : 0 < selectedJointDensityMass A modulus T W D)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {B K X : Type*} [Fintype K] [Fintype X]
variable (A : Finset B) (hA : A.Nonempty)
variable (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
variable (T : Finset (ColumnResiduePattern K X modulus))
variable (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
variable (hc : ∀ r : T, 0 < shiftedSmoothProductMass
  (residueProfileCenter (columnResidueRepresentative modulus r.val) modulus)
  (residueProfileWidth modulus V))

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

theorem positiveProjectionAccuracy_mass_bound {p : ℝ} (hp : 0 ≤ p) :
    3 * positiveProjectionAccuracy p ≤ Real.exp (-p) ∧
      3 * positiveProjectionAccuracy p ≤ 1 / 2 := by
  have hfour : (3 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have htwo : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hnine : (9 : ℝ) ≤ Real.exp 4 := by
    rw [show (4 : ℝ) = 2 + 2 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos (2 : ℝ)]
  have hsix : (6 : ℝ) ≤ Real.exp (2 * p + 4) :=
    (by linarith : (6 : ℝ) ≤ Real.exp 4).trans (Real.exp_le_exp.mpr (by linarith))
  constructor
  · calc
      _ ≤ Real.exp 4 * Real.exp (-(2 * p + 4)) :=
        mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
      _ = Real.exp (-(2 * p)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-p) := Real.exp_le_exp.mpr (by linarith)
  · calc
      _ = 3 / Real.exp (2 * p + 4) := by
        simp only [positiveProjectionAccuracy, Real.exp_neg, div_eq_mul_inv]
      _ ≤ 3 / (6 : ℝ) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsix
      _ = 1 / 2 := by norm_num

theorem positiveProjectionAccuracy_normalizer {p Z : ℝ} (hp : 0 ≤ p)
    (hZ : |Z - 1| ≤ 3 * positiveProjectionAccuracy p) :
    |Z - 1| ≤ Real.exp (-p) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
      0 < Z ∧ Z⁻¹ ≤ 2 := by
  have he := positiveProjectionAccuracy_mass_bound hp
  have hhalf := hZ.trans he.2
  have hlo : 1 / 2 ≤ Z := by have h := (abs_le.mp hhalf).1; linarith
  have hhi : Z ≤ 3 / 2 := by have h := (abs_le.mp hhalf).2; linarith
  have hpos : 0 < Z := by linarith
  refine ⟨hZ.trans he.1, ⟨hlo, hhi⟩, hpos, ?_⟩
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hlo
  simpa only [one_div, inv_div, inv_one, div_one, inv_inv] using h

theorem selectedJointDensityMass_positive_accuracy {B K I : Type*} [Fintype K] [Fintype I]
    (A : Finset B) (hA : A.Nonempty) (modulus : I → ℕ)
    (T : Finset (ColumnResiduePattern K I modulus)) (W : K × I → ℝ)
    (D : B → (K × I → ℤ) → ℝ) {p : ℝ} (hp : 0 ≤ p)
    (hD : ∀ a, |selectedResidueDensityMass modulus T W (D a) - 1| ≤
      3 * positiveProjectionAccuracy p) :
    let Z := selectedJointDensityMass A modulus T W D
    |Z - 1| ≤ Real.exp (-p) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
      0 < Z ∧ Z⁻¹ ≤ 2 :=
  positiveProjectionAccuracy_normalizer hp (selectedJointDensityMass_close A hA modulus T W D hD)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedApproximationError
namespace OAI

section

namespace Erdos3

theorem allocated_native_approximation_error
    {u p Q P K cap tau ε : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hQ : 0 ≤ Q)
    (hK : 0 ≤ K) (hcap : 0 ≤ cap)
    (hKP : K ≤ Real.exp p) (hcapP : cap ≤ Real.exp p)
    (htau : tau ≤ Real.exp (-(u + 3)))
    (hP : u + 2 * p + Q + 30 ≤ P)
    (hε : ε ≤ 6 * positiveProjectionAccuracy P) :
    2 * tau + 2 * K * (cap + 2 / Real.exp (-Q)) * ε ≤ Real.exp (-u) := by
  have hP0 : 0 ≤ P := by linarith
  have hεP : ε ≤ 2 * Real.exp (-P) := by
    have h := (positiveProjectionAccuracy_mass_bound hP0).1
    linarith
  have hcapQ : cap + 2 / Real.exp (-Q) ≤ 3 * Real.exp (p + Q) := by
    have h1 := Real.exp_le_exp.mpr (le_add_of_nonneg_right hQ : p ≤ p + Q)
    have h2 := Real.exp_le_exp.mpr (le_add_of_nonneg_left hp : Q ≤ p + Q)
    simp only [Real.exp_neg, div_eq_mul_inv, inv_inv]
    linarith
  have htail : 2 * K * (cap + 2 / Real.exp (-Q)) * ε ≤
      12 * Real.exp (2 * p + Q - P) := by
    calc
      _ ≤ 2 * K * (cap + 2 / Real.exp (-Q)) * (2 * Real.exp (-P)) :=
        mul_le_mul_of_nonneg_left hεP (by positivity)
      _ ≤ 2 * Real.exp p * (3 * Real.exp (p + Q)) * (2 * Real.exp (-P)) := by
        gcongr
      _ = 12 * (Real.exp p * Real.exp (p + Q) * Real.exp (-P)) := by ring
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring
  have h3 : 2 * Real.exp (-3 : ℝ) ≤ 1 / 2 := by
    have he : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
    calc
      _ = 2 / Real.exp 3 := by rw [Real.exp_neg, div_eq_mul_inv]
      _ ≤ 2 / (4 : ℝ) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) he
      _ = _ := by norm_num
  have h30 : 12 * Real.exp (-30 : ℝ) ≤ 1 / 2 := by
    have he : (24 : ℝ) ≤ Real.exp 30 := by linarith [Real.add_one_le_exp (30 : ℝ)]
    calc
      _ = 12 / Real.exp 30 := by rw [Real.exp_neg, div_eq_mul_inv]
      _ ≤ 12 / (24 : ℝ) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) he
      _ = _ := by norm_num
  have hsmall : 2 * tau ≤ Real.exp (-u) / 2 := by
    calc
      _ ≤ 2 * Real.exp (-(u + 3)) := mul_le_mul_of_nonneg_left htau (by norm_num)
      _ = Real.exp (-u) * (2 * Real.exp (-3)) := by rw [neg_add, Real.exp_add]; ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left h3 (Real.exp_nonneg (-u))]
  have htail' : 2 * K * (cap + 2 / Real.exp (-Q)) * ε ≤ Real.exp (-u) / 2 := by
    apply htail.trans
    calc
      _ ≤ 12 * Real.exp (-u - 30) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
      _ = Real.exp (-u) * (12 * Real.exp (-30)) := by rw [sub_eq_add_neg, Real.exp_add]; ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left h30 (Real.exp_nonneg (-u))]
  linarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DerivativeHorizontalLifts
namespace OAI

section

namespace Erdos3

structure RationalHorizontalLift {E : Type*} [AddCommGroup E] [Module ℝ E]
    {m a : ℕ} (k : ℕ) (P : E →ₗ[ℝ] (Fin a → ℝ)) (ha : a ≤ m)
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ)) (scale : Fin m → ℝ)
    (normBound : ℝ) (heightBound : ℕ) where
  denominator : ℕ
  denominator_pos : 0 < denominator
  denominator_le : denominator ≤ heightBound
  basisMatrix : Matrix (Fin a) (Fin k) ℚ
  basis_height : ∀ i j, RationalHeightLE (basisMatrix i j) heightBound
  independent_rat : LinearIndependent ℚ basisMatrix.col
  independent_real : LinearIndependent ℝ (basisMatrix.map (Rat.castHom ℝ)).col
  span_eq : LinearMap.range P =
    Submodule.span ℝ (Set.range (basisMatrix.map (Rat.castHom ℝ)).col)
  rationalLift : LinearMap.range P →ₗ[ℝ] (Fin m → ℝ)
  geometricLift : LinearMap.range P →ₗ[ℝ] (Fin m → ℝ)
  factorization : geometricLift = A.toLinearMap.comp rationalLift
  rational_horizontal : ∀ x i, rationalLift x (Fin.castLE ha i) = x.val i
  geometric_horizontal : ∀ x i, geometricLift x (Fin.castLE ha i) = x.val i
  norm_scaled : ∀ x,
    ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * geometricLift x j)‖ ≤
      normBound * ‖x‖
  rational_on_basis : ∀ j, ∃ x : LinearMap.range P,
    x.val = (basisMatrix.map (Rat.castHom ℝ)).col j ∧
    rationalLift x ∈ realDenominatorGrid denominator

end Erdos3

end

section

namespace Erdos3

theorem exists_basis_linear_lift {K E F G ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
    [AddCommGroup G] [Module K G]
    (b : Module.Basis ι K E) (f : E →ₗ[K] F) (W : G →ₗ[K] F)
    (v : ι → G) (hrep : ∀ j, f (b j) = W (v j)) :
    ∃ g : E →ₗ[K] G, (∀ j, g (b j) = v j) ∧ W.comp g = f := by
  refine ⟨b.constr K v, fun j => b.constr_basis K v j, ?_⟩
  apply b.ext
  intro j
  change W ((b.constr K v) (b j)) = f (b j)
  rw [Module.Basis.constr_basis]
  exact (hrep j).symm

theorem euclideanVerticalMap_norm_eq {σ κ : Type*} [Fintype σ] [Fintype κ]
    (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (x : κ → ℝ) :
    ‖euclideanVerticalMap (σ := σ) scale hscale A x‖ =
      ‖(EuclideanSpace.equiv κ ℝ).symm (fun j => scale j * A x j)‖ := by
  have hs : ‖euclideanVerticalMap (σ := σ) scale hscale A x‖ ^ 2 =
      ‖(EuclideanSpace.equiv κ ℝ).symm (fun j => scale j * A x j)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp only [Fintype.sum_sum_type, euclideanVerticalMap_apply_inl,
      euclideanVerticalMap_apply_inr, norm_zero, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero, zero_add]
    rfl
  nlinarith [norm_nonneg (euclideanVerticalMap (σ := σ) scale hscale A x),
    norm_nonneg ((EuclideanSpace.equiv κ ℝ).symm (fun j => scale j * A x j))]

end Erdos3

end

section

namespace Erdos3

theorem graph_derivative_decomposition
    {σ : Type*} [Fintype σ] {m a k : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : Fin m → ℝ) (hs : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ Fin m)))
    (ha : a ≤ m) (N : ℝ) (H : ℕ) :
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
    ∀ (lifts : RationalHorizontalLift k P ha A scale N H),
      (∀ v : V, euclideanVerticalMap scale hs A (lifts.rationalLift ⟨P v, v, rfl⟩) = v.val.val) →
      ∀ (G : (σ → ℝ) →ₗ[ℝ] Z), (∀ y i, (G y).val (Sum.inl i) = y i) →
      ∀ (x : Z) (y : σ → ℝ) (r : Fin m → ℝ),
        (∀ j, x.val (Sum.inr j) = scale j * (Y y j - A r j)) →
        ∃ (s : Fin m → ℝ) (q : LinearMap.range P),
          Y y = s + A r + lifts.geometricLift q ∧
          ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * s j)‖ ≤
            ‖G (fun i => x.val (Sum.inl i))‖ := by
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
  dsimp only
  intro lifts hrecovers G hG x y r hx
  let w := G (fun i => x.val (Sum.inl i))
  let v : V := ⟨x - w, euclidean_graph_residual_mem_kernel T hT Z G hG x⟩
  let q : LinearMap.range P := ⟨P v, v, rfl⟩
  let s : Fin m → ℝ := fun j => w.val (Sum.inr j) / scale j
  have hscale (j) : scale j * s j = w.val (Sum.inr j) := mul_div_cancel₀ _ (hs j)
  have hS (j) : scale j * lifts.geometricLift q j =
      x.val (Sum.inr j) - w.val (Sum.inr j) := by
    calc
      _ = euclideanVerticalMap scale hs A (lifts.rationalLift q) (Sum.inr j) := by
        rw [lifts.factorization]
        rfl
      _ = v.val.val (Sum.inr j) := congrArg (fun z => z (Sum.inr j)) (hrecovers v)
      _ = _ := rfl
  refine ⟨s, q, ?_, ?_⟩
  · funext j
    change Y y j = s j + A r j + lifts.geometricLift q j
    apply mul_left_cancel₀ (hs j)
    nlinarith [hS j, hscale j, hx j]
  · have he : (fun j => scale j * s j) = fun j => w.val (Sum.inr j) := funext hscale
    rw [he]
    exact euclideanVerticalProjection_norm_le w.val

end Erdos3

end

section

namespace Erdos3

theorem assemble_rational_horizontal_lift
    {E σ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype σ]
    {m a k : ℕ} (b : Module.Basis (Fin k) ℝ E)
    (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ (σ ⊕ Fin m))
    (P : E →ₗ[ℝ] (Fin a → ℝ)) (hPinj : Function.Injective P) (ha : a ≤ m)
    (hP : ∀ v i, P v i = f v (Sum.inr (Fin.castLE ha i)))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hAhor : ∀ x i, A x (Fin.castLE ha i) = x (Fin.castLE ha i))
    (scale : Fin m → ℝ) (hs0 : ∀ j, scale j ≠ 0)
    (hscalehor : ∀ i : Fin a, scale (Fin.castLE ha i) = 1)
    (B : Matrix (Fin m) (Fin k) ℝ)
    (hrep : ∀ j, f (b j) = euclideanVerticalMap scale hs0 A (B.col j))
    (p : Fin k → Fin a) (hp : (B.submatrix (Fin.castLE ha ∘ p) id).det ≠ 0)
    (Q : Matrix (Fin m) (Fin k) ℚ)
    (hQ : Q.map (Rat.castHom ℝ) = B * (B.submatrix (Fin.castLE ha ∘ p) id)⁻¹)
    (hQid : Q.submatrix (Fin.castLE ha ∘ p) id = 1)
    (D H : ℕ) (hD : 0 < D) (hDH : D ≤ H)
    (hgrid : ∀ j, Q.col j ∈ denominatorGrid D)
    (hheight : ∀ i j, RationalHeightLE (Q (Fin.castLE ha i) j) H)
    (N : ℝ) (hnorm : ∀ v, ‖v‖ ≤ N * ‖P v‖) :
    ∃ lifts : RationalHorizontalLift k P ha A scale N H,
      ∀ v, euclideanVerticalMap scale hs0 A (lifts.rationalLift ⟨P v, v, rfl⟩) = f v := by
  let W := euclideanVerticalMap (σ := σ) scale hs0 A
  obtain ⟨g, hgb, hgf⟩ := exists_basis_linear_lift b f.toLinearMap W B.col hrep
  have hW (v) : W (g v) = f v := LinearMap.congr_fun hgf v
  have hhor (v) (i : Fin a) : g v (Fin.castLE ha i) = P v i := by
    calc
      _ = A (g v) (Fin.castLE ha i) := (hAhor (g v) i).symm
      _ = W (g v) (Sum.inr (Fin.castLE ha i)) := by
        change _ = scale (Fin.castLE ha i) * A (g v) (Fin.castLE ha i)
        rw [hscalehor, one_mul]
      _ = f v (Sum.inr (Fin.castLE ha i)) := congrArg (fun z => z (Sum.inr (Fin.castLE ha i))) (hW v)
      _ = P v i := (hP v i).symm
  have hbound (v) : ‖W (g v)‖ ≤ N * ‖P v‖ := by
    rw [hW, f.norm_map]
    exact hnorm v
  have hB (i j) : B i j = g (b j) i := (congrFun (hgb j) i).symm
  obtain ⟨R, hRhor, hRbound, hRsection, hspan, hLIreal, hLIrat, hRbasis⟩ :=
    exists_bounded_rational_projection_lift b P hPinj g (Fin.castLE ha) hhor W N hbound
      B hB p hp Q hQ hQid
  refine ⟨{
    denominator := D
    denominator_pos := hD
    denominator_le := hDH
    basisMatrix := Q.submatrix (Fin.castLE ha) id
    basis_height := hheight
    independent_rat := hLIrat
    independent_real := hLIreal
    span_eq := hspan
    rationalLift := R
    geometricLift := A.toLinearMap.comp R
    factorization := rfl
    rational_horizontal := hRhor
    geometric_horizontal := ?_
    norm_scaled := ?_
    rational_on_basis := ?_
  }, ?_⟩
  · intro x i
    change A (R x) (Fin.castLE ha i) = x.val i
    rw [hAhor, hRhor]
  · intro x
    have h := hRbound x
    change ‖euclideanVerticalMap (σ := σ) scale hs0 A (R x)‖ ≤ N * ‖x‖ at h
    rw [euclideanVerticalMap_norm_eq] at h
    exact h
  · intro j
    obtain ⟨x, hx, hrx⟩ := hRbasis j
    refine ⟨x, hx, ?_⟩
    rw [hrx]
    exact (real_cast_mem_denominatorGrid_iff D (Q.col j)).mpr (hgrid j)
  · intro v
    change W (R ⟨P v, v, rfl⟩) = f v
    rw [hRsection]
    exact hW v

end Erdos3

end

section

namespace Erdos3

theorem indexed_derivative_decomposition
    {σ : Type*} [Fintype σ] [DecidableEq σ] {m a k : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (hTpos : ∀ i, 0 < T i)
    (scale : Fin m → ℝ) (hs : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ)) (l : ℕ) (hl : 0 < l)
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ Fin m)))
    (ha : a ≤ m) (N B : ℝ) (H : ℕ) :
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
    ∀ (lifts : RationalHorizontalLift k P ha A scale N H),
      (∀ v : V, euclideanVerticalMap scale hs A (lifts.rationalLift ⟨P v, v, rfl⟩) = v.val.val) →
      ∀ (G : (σ → ℝ) →ₗ[ℝ] Z), (∀ y i, (G y).val (Sum.inl i) = y i) →
      (∀ i, ‖G (Pi.basisFun ℝ σ i)‖ ≤ B) →
      ∀ (I : ℕ), 0 < I →
      (∀ i, ∃ v : Z, v.val ∈ euclideanDerivativeLattice T hT scale hs Y A l hl ∧
        euclideanDerivativeShiftMap T hT v.val = (I : ℝ) • Pi.basisFun ℝ σ i) →
      ∀ i, ∃ (s r : Fin m → ℝ) (q : LinearMap.range P),
        Y (Pi.basisFun ℝ σ i) = s + A r + lifts.geometricLift q ∧
        r ∈ realDenominatorGrid (l * I) ∧
        ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => scale j * s j)‖ ≤ B / T i := by
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
  dsimp only
  intro lifts hrecovers G hG hGB I hI hI_lifts i
  obtain ⟨v, hv, hshift⟩ := hI_lifts i
  let x : Z := (I : ℝ)⁻¹ • v
  obtain ⟨r, hr, hright⟩ := divided_derivative_lattice_coordinates T hT scale hs Y A l hl
    I hI (Pi.basisFun ℝ σ i) v.val hv hshift
  obtain ⟨s, q, heq, hsmall⟩ := graph_derivative_decomposition T hT scale hs Y A Z ha N H
    lifts hrecovers G hG x (Pi.basisFun ℝ σ i) r hright
  refine ⟨s, r, q, heq, hr, ?_⟩
  have hleft : (fun j => x.val (Sum.inl j)) =
      fun j => (Pi.basisFun ℝ σ i) j / T j :=
    funext (divided_derivative_horizontal_coordinates T hT I hI (Pi.basisFun ℝ σ i) v.val hshift)
  rw [hleft] at hsmall
  exact hsmall.trans (linearMap_divided_basis_norm_le G T i (hTpos i) B (hGB i))

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_horizontal_norm_bound
    {σ : Type*} [Fintype σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R : ℝ) (a : ℕ) (ha : a ≤ m) (Tmin C : ℝ)
    (hscalehor : ∀ j, j.val < a → scale j = 1)
    (hblock : ∀ i j, i.val < a → j.val < a →
      (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (hfar : ∀ i, a ≤ i.val → Tmin ≤ scale i) (hlarge : C * (l : ℝ) ^ m < Tmin) :
    let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
    let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
    let Z := shortVectorSpan Λ R
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let L := latticeKernel (shortVectorLattice Λ R) π
    let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
    let k := Module.finrank ℝ V
    ZLattice.covolume L (MeasureTheory.volume (α := V)) ≤ C →
      ∀ v : V, ‖v‖ ≤ (Fintype.card (σ ⊕ Fin m) : ℝ) * k *
        (C * (l : ℝ) ^ k) * ‖P v‖ := by
  let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
  let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
  let Z := shortVectorSpan Λ R
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let L := latticeKernel (shortVectorLattice Λ R) π
  let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
  let k := Module.finrank ℝ V
  change ZLattice.covolume L (MeasureTheory.volume (α := V)) ≤ C →
    ∀ v : V, ‖v‖ ≤ (Fintype.card (σ ⊕ Fin m) : ℝ) * k *
      (C * (l : ℝ) ^ k) * ‖P v‖
  intro hupper v
  let : IsZLattice ℝ L := euclideanDerivative_vertical_lattice_full T hT scale hs0 Y A l hl R
  obtain ⟨b, B, _, hgrid, hrep, p, _, hdet⟩ := euclideanDerivative_horizontal_basis_data
    T hT scale hscale Y A hA hdiag l hl R a ha Tmin C hfar hlarge hupper
  let f : V →ₗᵢ[ℝ] EuclideanSpace ℝ (σ ⊕ Fin m) := Z.subtypeₗᵢ.comp V.subtypeₗᵢ
  let e : Fin a → σ ⊕ Fin m := fun i => Sum.inr (Fin.castLE ha i)
  let H := B.submatrix (Fin.castLE ha) id
  have hH (i j) : H i j = f (b j).val (e i) := by
    change B (Fin.castLE ha i) j = (b j).val.val.val (Sum.inr (Fin.castLE ha i))
    rw [hrep]
    exact (euclideanVerticalMap_horizontal scale hs0 hscalehor A hA hblock (B.col j)
      (Fin.castLE ha i) i.isLt).symm
  have hHgrid (j) : H.col j ∈ realDenominatorGrid l := by
    obtain ⟨z, hz⟩ := hgrid j
    refine ⟨fun i => z (Fin.castLE ha i), ?_⟩
    funext i
    exact congrFun hz (Fin.castLE ha i)
  have hdetH : (H.submatrix p id).det ≠ 0 := hdet
  have hn := lattice_norm_le_projection_of_grid_minor
    (ι := σ ⊕ Fin m) (κ := Fin a) (E := V) (k := k)
    L b f e l hl H hH hHgrid p hdetH C hupper v
  have heP : (fun i => f v (e i)) = P v := rfl
  rw [heP] at hn
  exact hn

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_horizontal_lifts
    {σ : Type*} [Fintype σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R : ℝ) (a : ℕ) (ha : a ≤ m) (Tmin C : ℝ)
    (hscalehor : ∀ j, j.val < a → scale j = 1)
    (hblock : ∀ i j, i.val < a → j.val < a →
      (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (hfar : ∀ i, a ≤ i.val → Tmin ≤ scale i) (hlarge : C * (l : ℝ) ^ m < Tmin) :
    let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
    let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
    let Z := shortVectorSpan Λ R
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let L := latticeKernel (shortVectorLattice Λ R) π
    let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
    let k := Module.finrank ℝ V
    let N := (Fintype.card (σ ⊕ Fin m) : ℝ) * k * (C * (l : ℝ) ^ k)
    let H := Nat.ceil (C * (l : ℝ) ^ k)
    ZLattice.covolume L (MeasureTheory.volume (α := V)) ≤ C →
      ∃ lifts : RationalHorizontalLift k P ha A scale N H,
        ∀ v : V, euclideanVerticalMap scale hs0 A (lifts.rationalLift ⟨P v, v, rfl⟩) = v.val.val := by
  let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
  let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
  let Z := shortVectorSpan Λ R
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let L := latticeKernel (shortVectorLattice Λ R) π
  let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
  let k := Module.finrank ℝ V
  let N := (Fintype.card (σ ⊕ Fin m) : ℝ) * k * (C * (l : ℝ) ^ k)
  let H := Nat.ceil (C * (l : ℝ) ^ k)
  change ZLattice.covolume L (MeasureTheory.volume (α := V)) ≤ C →
    ∃ lifts : RationalHorizontalLift k P ha A scale N H,
      ∀ v : V, euclideanVerticalMap scale hs0 A (lifts.rationalLift ⟨P v, v, rfl⟩) = v.val.val
  intro hupper
  let : IsZLattice ℝ L := euclideanDerivative_vertical_lattice_full T hT scale hs0 Y A l hl R
  obtain ⟨b, B, p, _, hrep, hp, D, hD, hDH, Q, hgrid, hQ, hQid, hheight⟩ :=
    euclideanDerivative_rational_lift_matrix_data T hT scale hscale Y A hA hdiag
      l hl R a ha Tmin C hscalehor hblock hfar hlarge hupper
  let bR := b.ofZLatticeBasis ℝ L
  let f : V →ₗᵢ[ℝ] EuclideanSpace ℝ (σ ⊕ Fin m) := Z.subtypeₗᵢ.comp V.subtypeₗᵢ
  have hbrep (j) : f (bR j) = euclideanVerticalMap scale hs0 A (B.col j) := by
    simp only [bR, Module.Basis.ofZLatticeBasis_apply]
    exact hrep j
  have hP : ∀ v i, P v i = f v (Sum.inr (Fin.castLE ha i)) := fun _ _ => rfl
  have hPinj : Function.Injective P := euclideanDerivative_horizontal_injective
    T hT scale hscale Y A hA hdiag l hl R a ha Tmin C hscalehor hblock hfar hlarge hupper
  have hAhor (x) (i : Fin a) : A x (Fin.castLE ha i) = x (Fin.castLE ha i) := by
    have h := euclideanVerticalMap_horizontal (σ := σ) scale hs0 hscalehor A hA hblock
      x (Fin.castLE ha i) i.isLt
    rw [euclideanVerticalMap_apply_inr, hscalehor (Fin.castLE ha i) i.isLt, one_mul] at h
    exact h
  have hn : ∀ v : V, ‖v‖ ≤ N * ‖P v‖ := euclideanDerivative_horizontal_norm_bound
    T hT scale hscale Y A hA hdiag l hl R a ha Tmin C hscalehor hblock hfar hlarge hupper
  exact assemble_rational_horizontal_lift (E := V) (σ := σ) (m := m) (a := a) (k := k)
    bR f P hPinj ha hP A hAhor scale hs0 (fun i => hscalehor _ i.isLt)
    B hbrep p hp Q hQ hQid D H hD hDH hgrid hheight N hn

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DilationCost
namespace OAI

section

namespace Erdos3.MultilinearityBudget

open scoped TensorProduct NNReal

noncomputable def reconstructionExponent (s : ℕ) : ℕ :=
  Classical.choose (exists_rationalReconstructionLipschitzBound_exp s)

theorem reconstructionExponent_control (s d n H : ℕ) (A B : ℝ≥0) (p : ℝ)
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p)
    (hA : (A : ℝ) ≤ Real.exp p) (hB : (B : ℝ) ≤ Real.exp p) :
    (rationalReconstructionLipschitzBound s d n H A B : ℝ) ≤
      Real.exp ((p + reconstructionExponent s) ^ reconstructionExponent s) :=
  (Classical.choose_spec (exists_rationalReconstructionLipschitzBound_exp s)).2 d n H A B p
    hp hd hn hH hA hB

theorem niltest_complexity {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s n : ℕ} (Q : RationalFilteredNilmanifold L s n) {w : σ → ℕ} (T : Q.Niltest w)
    (C d H : ℕ) (A : ℝ≥0) {p : ℝ} (hp : 0 ≤ p)
    (hQ : Q.GeometryComplexityLE (quotient p))
    (hd : (d : ℝ) ≤ reconstruction C p) (hH : (H : ℝ) ≤ Real.exp (reconstruction C p))
    (hA : (A : ℝ) ≤ Real.exp (reconstruction C p))
    (hnorm : T.normBound = 1) (hlip : T.lipBound = rationalReconstructionLipschitzBound s d n H A 1) :
    T.ComplexityLE (total C (reconstructionExponent s) p) := by
  have hR := reconstruction_bounds C hp
  have hQle : quotient p ≤ reconstruction C p :=
    (le_add_of_nonneg_right zero_le_one).trans hR.2.2.1
  have hTlip : (T.lipBound : ℝ) ≤
      Real.exp ((reconstruction C p + reconstructionExponent s) ^ reconstructionExponent s) := by
    rw [hlip]
    exact reconstructionExponent_control s d n H A 1 _ hR.1 hd (hQ.1.trans hQle) hH hA
      (by simpa only [NNReal.coe_one] using Real.one_le_exp hR.1)
  have hpower : 0 ≤ (reconstruction C p + reconstructionExponent s) ^ reconstructionExponent s :=
    pow_nonneg (add_nonneg hR.1 (Nat.cast_nonneg _)) _
  have hlog := niltest_log_bound_of_exp T.normBound T.lipBound (a := 0) (by norm_num) hpower
    (by simp only [hnorm, NNReal.coe_one, Real.exp_zero, le_refl]) hTlip
  refine ⟨hQ.mono Q (total_bounds C (reconstructionExponent s) hp).1, ?_⟩
  have hlog' : Real.log (2 + (T.normBound : ℝ) + T.lipBound) ≤
      (reconstruction C p + reconstructionExponent s) ^ reconstructionExponent s + 4 := by
    simpa only [zero_add] using hlog
  exact hlog'.trans (total_bounds C (reconstructionExponent s) hp).2

end Erdos3.MultilinearityBudget

end

section

namespace Erdos3.DilationBudget

open scoped TensorProduct NNReal

theorem niltest_complexity {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s n : ℕ} (Q : RationalFilteredNilmanifold L s n) {w : σ → ℕ} (T : Q.Niltest w)
    (t : ℕ) (q : ℤ) (d H : ℕ) (A : ℝ≥0) {p : ℝ} (hp : 0 ≤ p)
    (hQ : Q.GeometryComplexityLE p) (hd : (d : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp (p + 1))
    (hA : (A : ℝ) ≤ Real.exp (reconstruction t q p))
    (hnorm : T.normBound = 1)
    (hlip : T.lipBound = rationalReconstructionLipschitzBound s d n H A 1) :
    T.ComplexityLE (total t q (MultilinearityBudget.reconstructionExponent s) p) := by
  have hR := reconstruction_bounds t q hp
  have hpR : p ≤ reconstruction t q p := (by linarith : p ≤ p + 1).trans hR.2
  have hTlip : (T.lipBound : ℝ) ≤ Real.exp
      ((reconstruction t q p + MultilinearityBudget.reconstructionExponent s) ^
        MultilinearityBudget.reconstructionExponent s) := by
    rw [hlip]
    exact MultilinearityBudget.reconstructionExponent_control s d n H A 1 _ hR.1
      (hd.trans hpR) (hQ.1.trans hpR) (hH.trans (Real.exp_le_exp.mpr hR.2)) hA
      (by simpa only [NNReal.coe_one] using Real.one_le_exp hR.1)
  have hpower : 0 ≤ (reconstruction t q p + MultilinearityBudget.reconstructionExponent s) ^
      MultilinearityBudget.reconstructionExponent s :=
    pow_nonneg (add_nonneg hR.1 (Nat.cast_nonneg _)) _
  have hlog := niltest_log_bound_of_exp T.normBound T.lipBound (a := 0) (by norm_num) hpower
    (by simp only [hnorm, NNReal.coe_one, Real.exp_zero, le_refl]) hTlip
  refine ⟨hQ.mono Q (total_bounds t q _ hp).1, ?_⟩
  have hlog' : Real.log (2 + (T.normBound : ℝ) + T.lipBound) ≤
      (reconstruction t q p + MultilinearityBudget.reconstructionExponent s) ^
        MultilinearityBudget.reconstructionExponent s + 4 := by
    simpa only [zero_add] using hlog
  exact hlog'.trans (total_bounds t q _ hp).2

end Erdos3.DilationBudget

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

def coefficientJetAxisSplit (P : LayerSamplerAxis I n → Prop) [DecidablePred P] :
    (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) ≃ᵐ
      (∀ a : {a // P a}, CoefficientJetAxisRow O a.val) ×
        (∀ a : {a // ¬P a}, CoefficientJetAxisRow O a.val) :=
  (coefficientJetAxisEquiv O I n).trans
    (MeasurableEquiv.piEquivPiSubtypeProd (CoefficientJetAxisRow O) P)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedCoveredRowReindex
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def mixedCoveredJetEquiv (d : ℕ) :
    ((∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) ×
      (∀ j, O j → B j → ZMod d)) ≃ᵐ CoveredJetChartSource U O B n d :=
  (dependentPiProd (Fin m)
    (fun j => (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))
    (fun j => O j → B j → ZMod d)).symm.trans
      (MeasurableEquiv.piCongrRight (fun j =>
        arrayResidueChart (O := O j) (Z := Fin (n j)) (R := B j → ZMod d) (o j)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical BigOperators ENNReal

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
variable [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coveredJetArrayReference (d : ℕ) [NeZero d] :
    Measure ((∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) ×
      (∀ j, O j → B j → ZMod d)) :=
  (Measure.pi (fun j =>
    (ENNReal.ofReal (ZLattice.covolume
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))))⁻¹ ^
        Fintype.card (O j) • mixedArrayReference (I j) (Fin (n j)) (O j))).prod
    (PMF.uniformOfFintype (∀ j, O j → B j → ZMod d)).toMeasure

variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coveredJetArrayScale : ℝ :=
  ∏ j, (ZLattice.covolume
    (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))⁻¹ ^ Fintype.card (O j)

variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem coveredJetArrayScale_pos : 0 < coveredJetArrayScale (O := O) U :=
  Finset.prod_pos (fun _ _ => pow_pos (inv_pos.mpr (ZLattice.covolume_pos _ volume)) _)

variable [∀ j, Fintype (I j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical ENNReal

namespace VectorPolynomial

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (B j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set
open scoped Classical BigOperators

variable {m : ℕ} {I O O' E J : Fin m → Type*} {n : Fin m → ℕ}
variable (e : ∀ j, O' j ≃ O j)

variable [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))

variable [∀ j, Fintype (O j)] [∀ j, Fintype (O' j)]

variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.MixedCoveredDensityMass
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
variable [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set
open scoped Classical

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩm : ∀ j t, MeasurableSet (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

noncomputable def mixedCoveredJetRawReference : Measure (MixedCoveredJetSource I O E n d) :=
  (Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))).prod
    (PMF.uniformOfFintype (∀ j, O j → E j → ZMod d)).toMeasure

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d Ω
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := O) (E := E) (n := n) d

include hΩm hΩ

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoveredChartCompact
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped Classical

namespace VectorPolynomial

variable {m : ℕ} {O J B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

variable [∀ j, Fintype (O j)] [∀ j, Fintype (E j)]

instance mixedCoveredJetRawReference_isFiniteMeasureOnCompacts (d : ℕ) [NeZero d] :
    IsFiniteMeasureOnCompacts
      (mixedCoveredJetRawReference (I := I) (O := O) (E := E) (n := n) d) := by
  let hc : ∀ j, IsFiniteMeasureOnCompacts
      (Measure.count : Measure (Fin (n j) → O j → ℤ)) := fun j => by
    constructor
    intro K hK
    exact Measure.count_apply_lt_top.mpr hK.finite_of_discrete
  let hm : ∀ j, IsFiniteMeasureOnCompacts
      (mixedArrayReference (I j) (Fin (n j)) (O j)) := fun j => by
    unfold mixedArrayReference
    infer_instance
  unfold mixedCoveredJetRawReference
  infer_instance

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedCoveredSiteExtraction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {I J Q : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (d : ℕ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {I J E : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable (rowSets : Fin m → Finset (Finset α))
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ) (d : ℕ)

local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set
open scoped BigOperators Classical

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {I J E : Fin m → Type*} {n : Fin m → ℕ}
variable (rowSets : Fin m → Finset (Finset α)) (d : ℕ)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "single" => (fun _ : Fin m => Unit)

noncomputable def mixedCoveredSiteArray
    (w : Finset α → MixedCoveredJetSource I single E n d) :
    MixedCoveredJetSource I (fun _ => Finset α) E n d :=
  (fun j => (fun i s => ((w s).1 j).1 i (), fun i s => ((w s).1 j).2 i ()),
    fun j s i => (w s).2 j () i)

noncomputable def mixedCoveredRowsOfSites
    (w : Finset α → MixedCoveredJetSource I single E n d) :
    MixedCoveredJetSource I rowTypes E n d :=
  mixedCoveredJetIntegerImage d (fun j => booleanJetExtractionMatrix (Subtype.val : rowTypes j → Finset α))
    (mixedCoveredSiteArray d w)

variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [NeZero d]

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeTwoVariableSplitFreezing
namespace OAI

section

namespace Erdos3.NativeTwoVariableSplit

open scoped TensorProduct

attribute [local instance] NativeTwoVariableSplit.lie NativeTwoVariableSplit.algebra NativeTwoVariableSplit.topology NativeTwoVariableSplit.topologicalAdd NativeTwoVariableSplit.continuousSMul NativeTwoVariableSplit.hausdorff

theorem first_eval_eq {s d : ℕ} {p epsilon : ℝ} {f : (Fin 2 → ℤ) → ℂ}
    (R : NativeTwoVariableSplit s d p epsilon f) (j : Fin R.count)
    (x y : Fin 2 → ℤ) (hxy : x 1 = y 1) :
    (R.test false j).eval x = (R.test false j).eval y := by
  unfold RationalFilteredNilmanifold.Niltest.eval
  rw [R.test_orbit false j, (R.multi false).orbitToOrdinary_eval,
    (R.multi false).orbitToOrdinary_eval]
  apply congrArg (R.test false j).observable
  apply congrArg QuotientGroup.mk
  apply (R.multi false).filtration.realification.polynomialOrbitEval_eq_of_zero_coordinate
    0 (show totalDegreeSplitBound s false 0 = 0 from rfl) (R.orbit false) x y
  intro i hi
  fin_cases i
  · exact (hi rfl).elim
  · exact hxy

end Erdos3.NativeTwoVariableSplit

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal

theorem exists_controlled_basepoint_normalization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ} (T : D.Niltest w)
      {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      ∃ U : D.Niltest w, U.normBound = T.normBound ∧ U.ComplexityLE ((p + C) ^ C) ∧
        D.filtration.realification.polynomialOrbitEval w 0 U.orbit = 1 ∧
        ∀ x : σ → ℤ, U.eval x = T.eval x := by
  obtain ⟨a, _, hrep⟩ := Erdos3.exists_realification_representatives_exp_bound s
  obtain ⟨b, _, hleft⟩ := exists_bounded_normalization_left_lipschitz s a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + (X + Polynomial.C a + 2 + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ d D w T p hp hT
  have hcost : p + normalizedSquareLeftBudget a b p ≤ (p + C) ^ C := by
    simpa [X, normalizedSquareLeftBudget, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨A, _, hA, hLip⟩ := hleft D p hp hT.1
  obtain ⟨ε, hε, γ, hγ, hfactor⟩ :=
    hrep D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice D.grid
      ⌈Real.exp p⌉₊ (p + 1) D.grid_pos D.inner_grid
      (fun i j k => rationalHeightLE_ceil_exp (hT.1.2.2.1 i j k))
      (by linarith) (by simpa only [Fintype.card_fin] using hT.1.1.trans (show p ≤ p + 1 by linarith))
      (ceil_exp_le_exp_add_one hp) (hT.1.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
      (D.filtration.realification.polynomialOrbitEval w 0 T.orbit)
  let U := T.normalizeBasepoint ε γ A (hLip ε hε)
  refine ⟨U, rfl, ?_, ?_, ?_⟩
  · exact (T.normalizeBasepoint_complexity ε γ A (hLip ε hε) hT
      (normalizedSquareLeftBudget_nonneg a b hp) hA).mono hcost
  · exact T.normalizeBasepoint_zero ε γ A (hLip ε hε) hfactor
  · intro x
    exact T.normalizeBasepoint_eval ε γ A (hLip ε hε) hγ x

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_controlled_group_normalization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      ∀ g : D.RealGroup, ∃ (ε γ : D.RealGroup) (A : ℝ≥0),
        γ ∈ D.realLattice ∧ g = ε * γ ∧ 0 < A ∧ (A : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        letI := D.metricSpace
        LipschitzWith A (fun x : D.Space => ε • x) := by
  obtain ⟨a, _, hrep⟩ := Erdos3.exists_realification_representatives_exp_bound s
  obtain ⟨b, _, hleft⟩ := exists_bounded_normalization_left_lipschitz s a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a + 2 + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p hp hD g
  have hcost : normalizedSquareLeftBudget a b p ≤ (p + C) ^ C := by
    simpa [X, normalizedSquareLeftBudget, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨A, hApos, hA, hLip⟩ := hleft D p hp hD
  obtain ⟨ε, hε, γ, hγ, hfactor⟩ :=
    hrep D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice D.grid
      ⌈Real.exp p⌉₊ (p + 1) D.grid_pos D.inner_grid
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
      (by linarith) (by simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 1 by linarith))
      (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith))) g
  exact ⟨ε, γ, A, hγ, hfactor, hApos, hA.trans (Real.exp_le_exp.mpr hcost), hLip ε hε⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped TensorProduct NNReal

theorem exists_controlled_multidegree_basepoint_normalization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p →
      ∀ g : M.filtration.realification.PolynomialOrbit,
      ∃ (ε : D.RealGroup) (A : ℝ≥0), (A : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x)) ∧
        ∃ g' : M.filtration.realification.PolynomialOrbit,
          M.filtration.realification.polynomialOrbitEval 0 g' = 1 ∧
          ∀ x, ε • (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g') : D.Space) =
            QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g) := by
  obtain ⟨a, _, hrep⟩ := Erdos3.exists_realification_representatives_exp_bound s
  obtain ⟨b, _, hleft⟩ := exists_bounded_normalization_left_lipschitz s a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a + 2 + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D bound M p hp hD g
  have hcost : normalizedSquareLeftBudget a b p ≤ (p + C) ^ C := by
    simpa [X, normalizedSquareLeftBudget, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨A, _, hA, hLip⟩ := hleft D p hp hD
  obtain ⟨ε, hε, γ, hγ, hfactor⟩ :=
    hrep D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice D.grid
      ⌈Real.exp p⌉₊ (p + 1) D.grid_pos D.inner_grid
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
      (by linarith) (by simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 1 by linarith))
      (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
      (M.filtration.realification.polynomialOrbitEval 0 g)
  refine ⟨ε, A, hA.trans (Real.exp_le_exp.mpr hcost), hLip ε hε,
    M.filtration.realification.normalizeMultidegreeOrbit g ε γ,
    M.filtration.realification.normalizeMultidegreeOrbit_zero g ε γ hfactor, ?_⟩
  intro x
  rw [M.filtration.realification.normalizeMultidegreeOrbit_eval]
  simp only [MulAction.Quotient.smul_mk, smul_eq_mul, ← mul_assoc, mul_inv_cancel, one_mul]
  exact QuotientGroup.mk_mul_of_mem _ (D.realLattice.inv_mem hγ)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_normalized_common_correlators (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d)
      (T : G → D.Niltest (fun _ : Unit => 1)) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p →
      (∀ h, (T h).ComplexityLE p) → (∀ h ∈ H, (T h).normBound ≤ 1) →
      ∀ {N : ℕ} [NeZero N] (weight : G → ZMod N → ℂ),
      (∀ h ∈ H, ∀ x, ‖weight h x‖ ≤ 1) →
      (∀ h ∈ H, Real.exp (-p) ≤
        ‖𝔼 x, weight h x * star ((T h).evalCyclic N (fun _ => x))‖) →
      ∃ (H' : Finset G) (S : G → D.Niltest (fun _ : Unit => 1)),
        H' ⊆ H ∧ H'.Nonempty ∧ Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
        (∀ h, (S h).normBound ≤ 1 ∧ (S h).UnitIntervalValued ∧
          (S h).ComplexityLE ((p + C) ^ C) ∧
          D.filtration.realification.polynomialOrbitEval (fun _ => 1) 0 (S h).orbit = 1) ∧
        (∀ h k, (S h).observable = (S k).observable) ∧
        ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
          ‖𝔼 x, weight h x * star ((S h).evalCyclic N (fun _ => x))‖ := by
  obtain ⟨a, _, hnormalize⟩ := exists_controlled_basepoint_normalization s
  obtain ⟨b, _, hfixed⟩ := exists_fixed_observable_correlators s
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + Polynomial.C a) ^ a + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + Polynomial.C b) ^ b + 2)
  refine ⟨C, hC, ?_⟩
  intro G L _ _ _ _ _ _ d D T H hH p hp hD hT hcap N _ weight hweight hcorr
  let q := p + (p + a) ^ a + 2
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hnormq : (p + a) ^ a ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hcost : q + (q + b) ^ b + 2 ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hfixedC : (q + b) ^ b ≤ (p + C) ^ C := by linarith
  choose R hRn hRc hRzero hRvalue using fun h => hnormalize D (T h) hp (hT h)
  have hReval (h : G) (x : ZMod N) :
      (R h).evalCyclic N (fun _ => x) = (T h).evalCyclic N (fun _ => x) := hRvalue h _
  obtain ⟨H', S, hsub, hnonempty, hdense, hS, hsame, hcS⟩ :=
    hfixed D R H hH hq (hD.mono D hpq) (fun h _ => (hRc h).mono hnormq)
      (fun h hh => by rw [hRn h]; exact hcap h hh) weight hweight
      (fun h hh => by
        simp_rw [hReval h]
        exact (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans (hcorr h hh))
  refine ⟨H', S, hsub, hnonempty, ?_, ?_, hsame, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hfixedC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h
    refine ⟨(hS h).2.1, (hS h).2.2.1, (hS h).2.2.2.mono hfixedC, ?_⟩
    rw [(hS h).1]
    exact hRzero h
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hfixedC)).trans (hcS h hh)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

universe u v

open Module
open scoped TensorProduct NNReal

theorem exists_controlled_frozen_niltest (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} {bound : σ → ℕ} (D : RationalFilteredNilmanifold L s d)
      (M : D.MultidegreeStructure bound) (S : Finset σ) (b : σ → ℤ)
      (g : M.filtration.realification.PolynomialOrbit)
      (u : D.Space → ℂ) (ℓ B : ℝ≥0)
      (_hu : letI := D.metricSpace; LipschitzWith ℓ u) (_hub : ∀ x, ‖u x‖ ≤ B)
      {p : ℝ}, M.ComplexityLE p → (ℓ : ℝ) ≤ Real.exp p → (B : ℝ) ≤ Real.exp p →
      ∃ E : RationalFilteredNilmanifold
          (M.filtration.weightedSubalgebra (retainedCoordinateWeight S))
          (multidegreeWeight (retainedCoordinateWeight S) bound)
          (finrank ℚ (M.filtration.weightedSubalgebra (retainedCoordinateWeight S))),
        E.filtration = M.filtration.weightedFiltration (retainedCoordinateWeight S) ∧
        E.lattice = D.lattice.comap
          (NilpotentLieBCHGroup.mapOfSteps
            (M.filtration.weightedSubalgebra (retainedCoordinateWeight S)).incl) ∧
        letI := moduleTopology ℝ
          (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S))
        letI : IsTopologicalAddGroup
            (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S)) :=
          IsModuleTopology.topologicalAddGroup ℝ _
        letI : T2Space (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S)) :=
          realification_moduleTopology_t2 E.basis
        ∃ T : E.Niltest (fun _ : S => 1), T.normBound = B ∧
          T.ComplexityLE ((p + C) ^ C) ∧
          E.filtration.realification.polynomialOrbitEval _ 0 T.orbit = 1 ∧
          ∀ x, T.eval x = u (QuotientGroup.mk
            (M.filtration.realification.polynomialOrbitEval (freezeCoordinates S b x) g)) := by
  obtain ⟨a, _, hrep⟩ := Erdos3.exists_realification_representatives_exp_bound s
  obtain ⟨k, _, hleft⟩ := exists_bounded_normalization_left_lipschitz s a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget
    ((X + 3) ^ 11 + 2 * X + (X + Polynomial.C a + 2 + Polynomial.C k) ^ k + (X + 4) ^ 2 + 4)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ _ d bound D M S b g u ℓ B hu hub p hM hℓ hB
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let c := retainedCoordinateWeight S
  let K := M.filtration.weightedSubalgebra c
  let r := normalizedSquareLeftBudget a k p
  have hr : 0 ≤ r := normalizedSquareLeftBudget_nonneg a k hp
  have hcost : (p + 3) ^ 11 + (2 * p + r + (p + 4) ^ 2 + 4) ≤ (p + C) ^ C := by
    convert hpoly p hp using 1
    simp [X, r, normalizedSquareLeftBudget, Polynomial.eval₂_pow]
    ring
  have hgeom : (p + 3) ^ 11 ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ 2 * p + r + (p + 4) ^ 2 + 4)).trans hcost
  have hobs : 2 * p + r + (p + 4) ^ 2 + 4 ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity : 0 ≤ (p + 3) ^ 11)).trans hcost
  obtain ⟨E, hEF, hEL, hE, he⟩ := M.exists_weighted_model c hM
  obtain ⟨A, _, hAb, hA⟩ := hleft D p hp hM.1
  obtain ⟨ε, hε, γ, hγ, hfactor⟩ :=
    hrep D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice D.grid
      ⌈Real.exp p⌉₊ (p + 1) D.grid_pos D.inner_grid
      (fun i j k => rationalHeightLE_ceil_exp (hM.1.2.2.1 i j k))
      (by linarith) (by simpa only [Fintype.card_fin] using hM.1.1.trans (show p ≤ p + 1 by linarith))
      (ceil_exp_le_exp_add_one hp) (hM.1.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
      (M.filtration.realification.polynomialOrbitEval (freezeCoordinates S b 0) g)
  refine ⟨E, hEF, hEL, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 E.basis
  let H := ⌈Real.exp (p + 1)⌉₊
  obtain ⟨T, hTnorm, hTlip, hTzero, hTeval⟩ := M.exists_frozen_niltest S E hEF hEL b g
    u ℓ B hu hub ε γ hγ hfactor A (hA ε hε) H
    (fun i j => rationalHeightLE_ceil_exp (he i j))
  have hdim : (finrank ℚ K : ℝ) ≤ p :=
    (Nat.cast_le.mpr (lie_subalgebra_finrank_le D.basis K)).trans
      (by simpa only [Fintype.card_fin] using hM.1.1)
  have hH : (H : ℝ) ≤ Real.exp (p + 2) := by
    simpa only [show p + 1 + 1 = p + 2 by ring] using
      ceil_exp_le_exp_add_one (by linarith : 0 ≤ p + 1)
  have hP : (coordinateLipschitzBound d (finrank ℚ K) H : ℝ) ≤ Real.exp ((p + 4) ^ 2) := by
    simpa only [NNReal.coe_natCast, show p + 2 + 2 = p + 4 by ring] using
      coordinateLipschitzBound_le_exp d (finrank ℚ K) H (by linarith : 0 ≤ p + 2)
        (hM.1.1.trans (by linarith)) (hdim.trans (by linarith)) hH
  have hTL : (T.lipBound : ℝ) ≤ Real.exp (p + r + (p + 4) ^ 2) := by
    rw [hTlip]
    change (ℓ : ℝ) * ((A : ℝ) * (coordinateLipschitzBound d (finrank ℚ K) H : ℝ)) ≤ _
    calc
      _ ≤ Real.exp p * (Real.exp r * Real.exp ((p + 4) ^ 2)) := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  refine ⟨T, hTnorm, ⟨hE.mono E hgeom, ?_⟩, hTzero, hTeval⟩
  have hn : (T.normBound : ℝ) ≤ Real.exp p := by rw [hTnorm]; exact hB
  have hb := niltest_log_bound_of_exp T.normBound T.lipBound hp
    (by positivity : 0 ≤ p + r + (p + 4) ^ 2) hn hTL
  exact hb.trans (by linarith)

noncomputable def freezingExponent (s : ℕ) : ℕ :=
  Classical.choose (exists_controlled_frozen_niltest.{u, v} s)

theorem freezingExponent_ge_two (s : ℕ) : 2 ≤ freezingExponent.{u, v} s :=
  (Classical.choose_spec (exists_controlled_frozen_niltest.{u, v} s)).1

theorem freezingExponent_control {σ : Type u} {L : Type v} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d : ℕ} {bound : σ → ℕ} (D : RationalFilteredNilmanifold L s d)
    (M : D.MultidegreeStructure bound) (S : Finset σ) (b : σ → ℤ)
    (g : M.filtration.realification.PolynomialOrbit)
    (f : D.Space → ℂ) (ℓ B : ℝ≥0)
    (hf : letI := D.metricSpace; LipschitzWith ℓ f) (hfb : ∀ x, ‖f x‖ ≤ B)
    {p : ℝ} (hM : M.ComplexityLE p) (hℓ : (ℓ : ℝ) ≤ Real.exp p) (hB : (B : ℝ) ≤ Real.exp p) :
    ∃ E : RationalFilteredNilmanifold
        (M.filtration.weightedSubalgebra (retainedCoordinateWeight S))
        (multidegreeWeight (retainedCoordinateWeight S) bound)
        (finrank ℚ (M.filtration.weightedSubalgebra (retainedCoordinateWeight S))),
      E.filtration = M.filtration.weightedFiltration (retainedCoordinateWeight S) ∧
      E.lattice = D.lattice.comap
        (NilpotentLieBCHGroup.mapOfSteps
          (M.filtration.weightedSubalgebra (retainedCoordinateWeight S)).incl) ∧
      letI := moduleTopology ℝ
        (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S))
      letI : IsTopologicalAddGroup
          (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S)) :=
        IsModuleTopology.topologicalAddGroup ℝ _
      letI : T2Space (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S)) :=
        realification_moduleTopology_t2 E.basis
      ∃ T : E.Niltest (fun _ : S => 1), T.normBound = B ∧
        T.ComplexityLE ((p + freezingExponent.{u, v} s) ^ freezingExponent.{u, v} s) ∧
        E.filtration.realification.polynomialOrbitEval _ 0 T.orbit = 1 ∧
        ∀ x, T.eval x = f (QuotientGroup.mk
          (M.filtration.realification.polynomialOrbitEval (freezeCoordinates S b x) g)) :=
  (Classical.choose_spec (exists_controlled_frozen_niltest.{u, v} s)).2
    D M S b g f ℓ B hf hfb hM hℓ hB

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

universe u

open Module
open RationalFilteredNilmanifold.MultidegreeStructure
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_freezing_niltest {σ : Type u} [Fintype σ] [DecidableEq σ] (bound : σ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p)
      (S : Finset σ) (b : σ → ℤ) (i : Fin W.outputDim),
      ∃ t n : ℕ, t = (∑ j ∈ S, bound j) ∧ n ≤ W.dim ∧
        ∃ E : RationalFilteredNilmanifold
          (W.multi.filtration.weightedSubalgebra (retainedCoordinateWeight S)) t n,
          letI := moduleTopology ℝ
            (ℝ ⊗[ℚ] W.multi.filtration.weightedSubalgebra (retainedCoordinateWeight S))
          letI : IsTopologicalAddGroup
              (ℝ ⊗[ℚ] W.multi.filtration.weightedSubalgebra (retainedCoordinateWeight S)) :=
            IsModuleTopology.topologicalAddGroup ℝ _
          letI : T2Space
              (ℝ ⊗[ℚ] W.multi.filtration.weightedSubalgebra (retainedCoordinateWeight S)) :=
            realification_moduleTopology_t2 E.basis
          ∃ T : E.Niltest (fun _ : S => 1), T.normBound = 1 ∧
            T.ComplexityLE ((p + C) ^ C) ∧
            E.filtration.realification.polynomialOrbitEval _ 0 T.orbit = 1 ∧
            ∀ x, T.eval x = W.eval i (freezeCoordinates S b x) := by
  refine ⟨freezingExponent.{u, 0} (∑ j, bound j), freezingExponent_ge_two.{u, 0} _, ?_⟩
  intro p W S b i
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨E, _, _, hE⟩ := freezingExponent_control W.model W.multi S b W.orbit (W.vertical.observable i)
    W.vertical.lipBound 1 (W.vertical.lipschitz i) (W.vertical.norm i) W.complexity
    W.vertical.lip_bound (by simpa only [NNReal.coe_one] using Real.one_le_exp hp)
  refine ⟨multidegreeWeight (retainedCoordinateWeight S) bound,
    finrank ℚ (W.multi.filtration.weightedSubalgebra (retainedCoordinateWeight S)),
    retainedCoordinate_degree S bound, ?_, E, hE⟩
  simpa only [Fintype.card_fin] using
    lie_subalgebra_finrank_le W.model.basis
      (W.multi.filtration.weightedSubalgebra (retainedCoordinateWeight S))

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeTwoVariableSplit

open Module RationalFilteredNilmanifold.MultidegreeStructure
open scoped TensorProduct BigOperators

attribute [local instance] NativeTwoVariableSplit.lie NativeTwoVariableSplit.algebra NativeTwoVariableSplit.topology NativeTwoVariableSplit.topologicalAdd NativeTwoVariableSplit.continuousSMul NativeTwoVariableSplit.hausdorff

theorem exists_second_expansion_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {d : ℕ} {p epsilon : ℝ} {f : (Fin 2 → ℤ) → ℂ}
      (R : NativeTwoVariableSplit s d p epsilon f) (j : Fin R.count) (h : ℤ),
      ∃ E : NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) ((p + C) ^ C)
          (fun x => (R.test true j).eval ![h, x ()]), E.count = 1 := by
  obtain ⟨C, hC, hfreeze⟩ := exists_controlled_frozen_niltest (∑ _ : Fin 2, s)
  refine ⟨C, hC, ?_⟩
  intro d p epsilon f R j h
  classical
  let S : Finset (Fin 2) := {1}
  have hp : 0 ≤ p := (Nat.cast_nonneg (R.dim true)).trans (R.complexity true).1.1
  have hlip : ((R.test true j).lipBound : ℝ) ≤ Real.exp p := by
    have hb := (R.test true j).observable_budget (R.test_complexity true j)
    have hn := (R.test true j).normBound.coe_nonneg
    linarith
  have hub : ∀ x, ‖(R.test true j).observable x‖ ≤ (1 : ℝ) := fun x =>
    ((R.test true j).norm_le x).trans
      (show ((R.test true j).normBound : ℝ) ≤ 1 from R.test_norm true j)
  obtain ⟨E, _, _, hE⟩ := hfreeze (R.model true) (R.multi true) S ![h, 0]
    (R.orbit true) (R.test true j).observable (R.test true j).lipBound 1
    (R.test true j).lipschitz hub (R.complexity true) hlip
    (by simpa only [NNReal.coe_one] using Real.one_le_exp hp)
  let K := (R.multi true).filtration.weightedSubalgebra (retainedCoordinateWeight S)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 E.basis
  obtain ⟨T, _, hT, _, hTeval⟩ := hE
  let U := T.affinePullback (fun _ (_ : Unit) => (1 : ℤ)) 0
  have hU : U.ComplexityLE ((p + C) ^ C) := hT
  have hval (x : Unit → ℤ) : U.eval x = (R.test true j).eval ![h, x ()] := by
    rw [RationalFilteredNilmanifold.Niltest.eval_affinePullback, hTeval]
    unfold RationalFilteredNilmanifold.Niltest.eval
    rw [R.test_orbit true j, (R.multi true).orbitToOrdinary_eval]
    congr 2
    apply congrArg (fun z => (R.multi true).filtration.realification.polynomialOrbitEval z
      (R.orbit true))
    funext i
    fin_cases i <;> simp [S, freezeCoordinates, integerAffineMap]
  have hdegree : multidegreeWeight (retainedCoordinateWeight S) (totalDegreeSplitBound s true) =
      s - 1 := by
    rw [retainedCoordinate_degree]
    simp [S, totalDegreeSplitBound]
  have hresult : ∃ Q : NativeIntegerExpansion (fun _ : Unit => 1)
      (multidegreeWeight (retainedCoordinateWeight S) (totalDegreeSplitBound s true))
      ((p + C) ^ C) (fun x => (R.test true j).eval ![h, x ()]), Q.count = 1 :=
    ⟨NativeIntegerExpansion.ofTest U hU (fun x => (hval x).symm), rfl⟩
  exact hdegree ▸ hresult

end Erdos3.NativeTwoVariableSplit

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TwoDownsetPrecision
namespace OAI

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module NilpotentLieBCHGroup VectorPolynomial
open scoped BigOperators TensorProduct NNReal

def DownsetSplittingStatement (s t a C : ℕ) : Prop :=
    ∀ {I α σ L : Type*} [Fintype I] [Fintype α] [DecidableEq α]
      [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
      {d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) (J : α → Set (σ →₀ ℕ))
      [∀ i, DecidablePred (· ∈ J i)] (hJ : ∀ i, IsLowerSet (J i))
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (p : ℝ), (∑ i, bound i) = t → M.ComplexityLE p →
      (Fintype.card α : ℝ) ≤ p + 2 →
      (∀ c, c ≠ 0 → (∀ i, c ∉ J i) → M.filtration.layer (fun j => c j) = ⊥) →
      ∀ g : M.filtration.realification.PolynomialOrbit,
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ a) →
      (Fintype.card I : ℝ) ≤ Real.exp p →
      letI : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
        fun _ => moduleTopology ℝ _
      letI : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
        fun _ => IsModuleTopology.topologicalAddGroup ℝ _
      letI : ∀ i, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
        fun i => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J i) (hJ i) p)
      ∃ r : ℝ, p ≤ r ∧ r ≤ (p + C) ^ C ∧
      ∃ (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable r B),
        (∀ i, (M.positivePolynomialDownsetModelMultidegree (J i) (hJ i) r B hB hstable).ComplexityLE ((p + C) ^ C)) ∧
        (∀ i, Fintype.card (M.PositivePolynomialDownsetIndex (J i)) ≤ 2 ^ t * d) ∧
        ∃ h : M.filtration.positivePolynomialMultidegree.realification.PolynomialOrbit,
          M.filtration.positivePolynomialMultidegree.realification.polynomialOrbitEval 0 h = 1 ∧
          ∃ n : α → ℕ, (∀ i, 0 < n i) ∧
            (∀ i, (n i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
            (Fintype.card (∀ i, Fin (n i)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
            ∃ T : ∀ i, Fin (n i) → (M.positivePolynomialDownsetModel (J i) (hJ i) r B hB hstable).Niltest (fun _ : σ => 1),
              (∀ i j, (T i j).normBound = 1) ∧ (∀ i j, (T i j).UnitIntervalValued) ∧
              (∀ i j, (T i j).ComplexityLE ((p + C) ^ C)) ∧
              (∀ i j, (T i j).orbit =
                (M.positivePolynomialDownsetModelMultidegree (J i) (hJ i) r B hB hstable).orbitToOrdinary
                  (M.filtration.positivePolynomialDownsetOrbit (J i) (hJ i) h)) ∧
              ∀ (u : I → D.Space → ℂ) (ell : ℝ≥0), (ell : ℝ) ≤ Real.exp p →
                (letI := D.metricSpace; ∀ k, LipschitzWith ell (u k)) →
                (∀ k x, ‖u k x‖ ≤ 1) →
                ∃ c : (∀ i, Fin (n i)) → EuclideanSpace ℂ I,
                  (∀ j k, ‖c j k‖ ≤ 2) ∧ (∀ j, ‖c j‖ ≤ Real.exp ((p + C) ^ C)) ∧
                  ∀ x, ‖(WithLp.toLp 2 (fun k => u k
                      (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g))) : EuclideanSpace ℂ I) -
                    ∑ j, (∏ i, (T i (j i)).eval x) • c j‖ ≤ epsilon

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module NilpotentLieBCHGroup VectorPolynomial
open scoped BigOperators TensorProduct NNReal

theorem exists_multidegree_downset_splitting (s t a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ DownsetSplittingStatement s t a C := by
  obtain ⟨b, _, hnormalize⟩ := exists_controlled_multidegree_basepoint_normalization s
  obtain ⟨c, _, hsplit⟩ := exists_canonical_positivePolynomial_splitting t a
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C b) ^ b + 2
  let P : Polynomial ℕ := Q + (Q + Polynomial.C c) ^ c + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro I α σ L _ _ _ _ _ _ _ d D bound M J _ hJ _ _ _ _
    p ht hM hα hcover g epsilon hepsilon hscale hI
  let : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun _ => moduleTopology ℝ _
  let : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ i, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun i => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J i) (hJ i) p)
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let r := p + (p + b) ^ b + 2
  have hnormal_nonneg : 0 ≤ (p + b) ^ b := by positivity
  have hpr : p ≤ r := by dsimp [r]; linarith only [hnormal_nonneg]
  have hr : 0 ≤ r := hp.trans hpr
  have hcost : r + (r + c) ^ c + 2 ≤ (p + C) ^ C := by
    simpa [P, Q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (r + c) ^ c := by positivity
  have hr_cost : r ≤ (p + C) ^ C := by linarith only [hcost, hpow]
  have hpower_cost : (r + c) ^ c ≤ (p + C) ^ C := by linarith only [hcost, hr]
  obtain ⟨ε, A, hA, hLip, g', hg', heval⟩ := hnormalize M hp hM.1 g
  have hshift : p + 2 ≤ r + 2 := by linarith only [hpr]
  have hscale_r : 1 / epsilon ≤ Real.exp ((r + 2) ^ a) :=
    hscale.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) hshift a))
  obtain ⟨B, hB, hstable, hresult⟩ :=
    hsplit (I := I) (α := α) (σ := σ) (L := L) M J hJ r ht (hM.mono M hpr) (hα.trans hshift) hcover g' hg'
      epsilon hepsilon hscale_r (hI.trans (Real.exp_le_exp.mpr hpr))
  obtain ⟨hE, h, hh, hresult⟩ := hresult
  obtain ⟨n, hn, hnb, hcount, T, hresult⟩ := hresult
  obtain ⟨hTnorm, hTunit, hT, hTorbit, happrox⟩ := hresult
  have hdim (i) : Fintype.card (M.PositivePolynomialDownsetIndex (J i)) ≤ 2 ^ t * d := by
    apply (M.positivePolynomialDownsetIndex_card_le (J i)).trans
    simpa only [ht] using M.positivePolynomialBasisIndex_card_le r
  refine ⟨r, hpr, hr_cost, B, hB, hstable, fun i => (hE i).mono _ hpower_cost,
    hdim, h, hh, n, hn, fun i => (hnb i).trans (Real.exp_le_exp.mpr hpower_cost),
    hcount.trans (Real.exp_le_exp.mpr hpower_cost), T, hTnorm, hTunit,
    fun i j => (hT i j).mono hpower_cost, hTorbit, ?_⟩
  let := D.metricSpace
  have htranslated_bound : Real.exp p * (A : ℝ) ≤ Real.exp r := by
    calc
      _ ≤ Real.exp p * Real.exp ((p + b) ^ b) :=
        mul_le_mul_of_nonneg_left hA (Real.exp_nonneg _)
      _ = Real.exp (p + (p + b) ^ b) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [r]; exact le_add_of_nonneg_right (by norm_num))
  exact vector_approximation_precompose (I := I) (J := ∀ i, Fin (n i))
    (S := σ → ℤ) (X := D.Space) (A := A) (p := p) (q := r)
    (B := Real.exp ((r + c) ^ c)) (B' := Real.exp ((p + C) ^ C))
    (epsilon := epsilon) (fun y : D.Space => ε • y)
    (fun x => QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g'))
    (fun x => QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g))
    (fun j x => ∏ i, (T i (j i)).eval x) hLip heval htranslated_bound
    (Real.exp_le_exp.mpr hpower_cost) happrox

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module VectorPolynomial
open scoped BigOperators TensorProduct NNReal

def TwoDownsetSplittingStatement (s t a C : ℕ) : Prop :=
    ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
      {d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
      (M : D.MultidegreeStructure bound) (J : Bool → Set (σ →₀ ℕ))
      [∀ b, DecidablePred (· ∈ J b)] (hJ : ∀ b, IsLowerSet (J b))
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (p : ℝ), (∑ i, bound i) = t → M.ComplexityLE p →
      (∀ c, c ≠ 0 → c ∉ J false ∪ J true → M.filtration.layer (fun i => c i) = ⊥) →
      ∀ g : M.filtration.realification.PolynomialOrbit,
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ a) →
      letI : ∀ b, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J b) (hJ b))) :=
        fun _ => moduleTopology ℝ _
      letI : ∀ b, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J b) (hJ b))) :=
        fun _ => IsModuleTopology.topologicalAddGroup ℝ _
      letI : ∀ b, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J b) (hJ b))) :=
        fun b => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J b) (hJ b) p)
      ∃ r : ℝ, p ≤ r ∧ r ≤ (p + C) ^ C ∧
      ∃ (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable r B),
        let E := fun b => M.positivePolynomialDownsetModel (J b) (hJ b) r B hB hstable
        (∀ b, (M.positivePolynomialDownsetModelMultidegree (J b) (hJ b) r B hB hstable).ComplexityLE ((p + C) ^ C)) ∧
        (∀ b, Fintype.card (M.PositivePolynomialDownsetIndex (J b)) ≤ 2 ^ t * d) ∧
        (∀ b c, c ∉ J b →
          (M.positivePolynomialDownsetModelMultidegree (J b) (hJ b) r B hB hstable).filtration.layer (fun i => c i) = ⊥) ∧
        ∃ h : M.filtration.positivePolynomialMultidegree.realification.PolynomialOrbit,
          M.filtration.positivePolynomialMultidegree.realification.polynomialOrbitEval 0 h = 1 ∧
          ∀ (u : D.Space → ℂ) (ell : ℝ≥0), (ell : ℝ) ≤ Real.exp p →
            (letI := D.metricSpace; LipschitzWith ell u) → (∀ x, ‖u x‖ ≤ 1) →
            ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              ∃ (A : Fin N → (E false).Niltest (fun _ : σ => 1))
                (B' : Fin N → (E true).Niltest (fun _ : σ => 1)),
                (∀ j, (A j).normBound ≤ 1) ∧ (∀ j, (B' j).normBound ≤ 1) ∧
                (∀ j, (A j).ComplexityLE ((p + C) ^ C)) ∧
                (∀ j, (B' j).ComplexityLE ((p + C) ^ C)) ∧
                (∀ j, (A j).orbit =
                  (M.positivePolynomialDownsetModelMultidegree (J false) (hJ false) r B hB hstable).orbitToOrdinary
                    (M.filtration.positivePolynomialDownsetOrbit (J false) (hJ false) h)) ∧
                (∀ j, (B' j).orbit =
                  (M.positivePolynomialDownsetModelMultidegree (J true) (hJ true) r B hB hstable).orbitToOrdinary
                    (M.filtration.positivePolynomialDownsetOrbit (J true) (hJ true) h)) ∧
                ∀ x, ‖u (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)) -
                  ∑ j, (A j).eval x * (B' j).eval x‖ ≤ epsilon

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module VectorPolynomial
open scoped BigOperators TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module VectorPolynomial
open scoped BigOperators TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module VectorPolynomial
open scoped BigOperators TensorProduct

theorem exists_two_downset_splitting (s t a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ TwoDownsetSplittingStatement s t a C := by
  obtain ⟨b, _, hsplit⟩ := exists_multidegree_downset_splitting s t a
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C b) ^ b + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ d D bound M J _ hJ _ _ _ _ p ht hM hcover g epsilon hepsilon hscale
  classical
  let : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun _ => moduleTopology ℝ _
  let : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ i, T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
      restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i))) :=
    fun i => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J i) (hJ i) p)
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  have hcost : (p + b) ^ b + 1 ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  have hcost' : (p + b) ^ b ≤ (p + C) ^ C := by linarith only [hcost]
  have hfamily : (Fintype.card Bool : ℝ) ≤ p + 2 := by
    simp only [Fintype.card_bool, Nat.cast_ofNat]
    linarith only [hp]
  have hsupport : ∀ c, c ≠ 0 → (∀ i, c ∉ J i) → M.filtration.layer (fun j => c j) = ⊥ := by
    intro c hc hout
    apply hcover c hc
    rintro (hl | hr)
    · exact hout false hl
    · exact hout true hr
  obtain ⟨r, hpr, hr, B, hB, hstable, hresult⟩ :=
    hsplit (I := Unit) (α := Bool) (σ := σ) (L := L) M J hJ p ht hM hfamily hsupport
      g epsilon hepsilon hscale (by simpa using Real.one_le_exp hp)
  obtain ⟨hE, hdim, h, hh, hresult⟩ := hresult
  obtain ⟨n, hn, hnb, hcount, T, hresult⟩ := hresult
  obtain ⟨hTnorm, hTunit, hT, hTorbit, happrox⟩ := hresult
  let E := fun i => M.positivePolynomialDownsetModel (J i) (hJ i) r B hB hstable
  have hterminal : ∀ i c, c ∉ J i →
      (M.positivePolynomialDownsetModelMultidegree (J i) (hJ i) r B hB hstable).filtration.layer
        (fun j => c j) = ⊥ := by
    intro i c hc
    exact M.filtration.positivePolynomialDownsetQuotient_terminal (J i) (hJ i) c hc
  refine ⟨r, hpr, hr.trans hcost', B, hB, hstable,
    fun i => (hE i).mono _ hcost', hdim, hterminal, h, hh, ?_⟩
  intro u ell hell hu hub
  let coefficients := happrox (fun _ : Unit => u) ell hell (fun _ => hu) (fun _ => hub)
  let coeff := coefficients.choose
  have hcoeff := coefficients.choose_spec.1
  have herr := coefficients.choose_spec.2.2
  have hscalar := scalar_error_le_of_vector_error (I := Unit) (J := ∀ i, Fin (n i))
    (S := σ → ℤ) (epsilon := epsilon)
    (fun _ : Unit => fun x => u (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)))
    (fun j x => ∏ i, (T i (j i)).eval x) coeff herr ()
  let : Nonempty (∀ i, Fin (n i)) := ⟨fun i => ⟨0, hn i⟩⟩
  let pairSum := exists_bounded_niltest_pair_sum (J := ∀ i, Fin (n i)) (σ := σ)
      (p := (p + b) ^ b) (E false) (E true) (fun _ : σ => 1)
      ((M.positivePolynomialDownsetModelMultidegree (J false) (hJ false) r B hB hstable).orbitToOrdinary
        (M.filtration.positivePolynomialDownsetOrbit (J false) (hJ false) h))
      ((M.positivePolynomialDownsetModelMultidegree (J true) (hJ true) r B hB hstable).orbitToOrdinary
        (M.filtration.positivePolynomialDownsetOrbit (J true) (hJ true) h))
      (fun j => T false (j false)) (fun j => T true (j true)) (fun j => coeff j ())
      (fun j => (hTnorm false (j false)).le) (fun j => (hTnorm true (j true)).le)
      (fun j => hT false (j false)) (fun j => hT true (j true))
      (fun j => hTorbit false (j false)) (fun j => hTorbit true (j true)) (fun j => hcoeff j ())
  let N := pairSum.choose
  have hNpos := pairSum.choose_spec.1
  have hN : N = 2 * Fintype.card (∀ i, Fin (n i)) := pairSum.choose_spec.2.1
  let leftTests := pairSum.choose_spec.2.2
  let A := leftTests.choose
  let rightTests := leftTests.choose_spec
  let B' := rightTests.choose
  have hdata := rightTests.choose_spec
  have hAnorm := hdata.1
  have hBnorm := hdata.2.1
  have hA := hdata.2.2.1
  have hB' := hdata.2.2.2.1
  have hAg := hdata.2.2.2.2.1
  have hBg := hdata.2.2.2.2.2.1
  have heval := hdata.2.2.2.2.2.2
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
  have hNbound : (N : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    rw [hN, Nat.cast_mul, Nat.cast_ofNat]
    calc
      _ ≤ 2 * Real.exp ((p + b) ^ b) := mul_le_mul_of_nonneg_left hcount (by norm_num)
      _ = Real.exp ((p + b) ^ b) * 2 := mul_comm _ _
      _ ≤ Real.exp ((p + b) ^ b) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg _)
      _ = Real.exp ((p + b) ^ b + 1) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hcost
  refine ⟨N, hNpos, hNbound, A, B', hAnorm, hBnorm,
    fun j => (hA j).mono hcost', fun j => (hB' j).mono hcost', hAg, hBg, ?_⟩
  intro x
  rw [heval x]
  convert hscalar x using 1
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  rw [Fintype.prod_bool, mul_comm ((T true (j true)).eval x) ((T false (j false)).eval x)]

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module VectorPolynomial
open scoped BigOperators TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module VectorPolynomial
open scoped BigOperators TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end OAI

end


