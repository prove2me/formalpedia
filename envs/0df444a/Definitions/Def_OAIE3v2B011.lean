-- Prove2me | Definitions.Def_OAIE3v2B011
-- name    : OAIE3v2B011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:57:25.878987+00:00
-- url     : https://prove2.me/theorems/9c967931-e0e5-4aed-86c1-30bcbaf6a99c
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 12 of 311
-- statement:
--   Definitions bundle 12 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/FixedRefinementBudget.lean`, `Dynamics/PeelingReplacementPotential.lean`, `Dynamics/ReplacementCellPotential.lean`, `Dynamics/SpectralLogBudget.lean`, `Dynamics/UnbalancedWidthBudget.lean`, `Dynamics/VectorSiteBudget.lean`, `Estimates/AllocatedNormalizedSiteTwist.lean`, `Estimates/AllocatedReferenceJetWindow.lean`, `Estimates/BufferedSiteExpansion.lean`, `Estimates/CoefficientRowReindex.lean`, `Estimates/ComplexFiniteMeans.lean`, `Estimates/FiniteCellRefinement.lean`, `Estimates/FiniteInnerProgressionFamily.lean`, `Estimates/FiniteReciprocalTenthTail.lean`, `Estimates/FlatWeightedComparison.lean`, `Estimates/GroupedSiteTensor.lean`, `Estimates/IndependentReturnScale.lean`, `Estimates/LocalBoostedAlmostPeriods.lean`, `Estimates/LocalMomentScale.lean`, `Estimates/LocalizedAverageScaleOrder.lean`, `Estimates/LocalizedSiftingAlmostPeriods.lean`, `Estimates/MatchedFlatDecay.lean`, `Estimates/NormalizedCutoffs.lean`, `Estimates/PeelingChildBound.lean`, `Estimates/PeelingDecomposition.lean`, `Estimates/PeriodicIsometricAction.lean`, `Estimates/PhysicalCubeNativeDetection.lean`, `Estimates/PhysicalRowsSiteReconstruction.lean`, `Estimates/PositiveNormalizationError.lean`, `Estimates/ProductPMFMap.lean`, `Estimates/QuantitativeNoninjectivity.lean`, `Estimates/RefinementEnlargement.lean`, `Estimates/RefinementMatchingGeometry.lean`, `Estimates/RepresentativeWindowPatch.lean`, `Estimates/SelectedCoefficientEvaluation.lean`, `Estimates/UniformCommutingCircleDecomposition.lean`, `Estimates/WeightedSummandCorrelation.lean`, `FixedDensity/GeneratorCells.lean`, `Fourier/CoordinatedBohrMatching.lean`, `Fourier/FiniteFourierSmoothing.lean`, `Fourier/RectangularGridCharacter.lean`, `Fourier/UnbalancedBohrShape.lean`, `Geometry/BoxBlockBudget.lean`, `Geometry/CoordinateProductCap.lean`, `Geometry/CoordinateTreeTrace.lean`, `Geometry/CoordinatedMatchingScale.lean`, `Geometry/PhysicalSpatialScales.lean`, `Geometry/PhysicalSupportedCubes.lean`, `Geometry/QuantitativeMetricPartition.lean`, `Geometry/SpatialPivotNormalization.lean`, `Geometry/SpatialSiteShift.lean`, `Geometry/SpatialStarCoordinates.lean`, `Lattices/BoundedPrimeDepthBudget.lean`, `Lattices/IntegerAffineSubstitution.lean`, `Lattices/IntegerFiberUniformBound.lean`, `Lattices/NaturalScaleIntegerWindow.lean`, `Lattices/PhysicalSpatialResidueSupport.lean`, `Lattices/PhysicalSubboxResidueSlice.lean`, `Lattices/ResidueIntervalFactors.lean`, `Lattices/ResidueLinearPointCap.lean`, `Lattices/ResidueRefinedPeriod.lean`, `Linear/CanonicalJointFrameGeometry.lean`, `Linear/ExternalFamilyCircleProjection.lean`, `Linear/MatrixSupInverse.lean`, `Linear/PivotNormalizedMatrix.lean`, `Linear/RootDifferenceMatrix.lean`, `Polynomial/AffinePhaseBias.lean`, `Probability/ObservedProductDensity.lean`, `Probability/UniformSelectedCoefficientProductLaw.lean`, `Sampling/AmbientL1SamplingBudget.lean`, `Sampling/L1SamplingSurrogate.lean`, `Sampling/NormalizedRealBoxHalfGrid.lean`, `Sampling/PrecenterForecastNativePartners.lean`, `Sampling/QuarticSamplingBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexFiniteMeans
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*}

noncomputable def cellAverage [Add G] (C : Finset G) (f : G → ℝ) (x : G) : ℝ :=
  𝔼 c ∈ C, f (x + c)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalizedAverageScaleOrder
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def localizedAverageScale (rank : ℕ) (R epsilon : ℝ) : ℝ≥0 :=
  (min ((1 : ℝ) / (200 * (max rank 1 : ℕ)))
    (epsilon / (400 * (max rank 1 : ℕ) * (R + 1)))).toNNReal

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FlatWeightedComparison
namespace OAI


namespace Erdos3.LocalConvolution

open scoped BigOperators

noncomputable def momentAmplificationFactor (delta : ℝ) : ℕ := ⌈2 / delta⌉₊ + 1

noncomputable def momentAmplificationGain (delta : ℝ) : ℝ :=
  (2 : ℝ) ^ (1 / (momentAmplificationFactor delta : ℝ)) - 1

end Erdos3.LocalConvolution


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeelingDecomposition
namespace OAI


namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

def remainder (C : Finset G) (f : G → ℝ) (x : G) : ℝ := if x ∈ C then 0 else f x

def slice (C : Finset G) (f : G → ℝ) (x : G) : ℝ := if x ∈ C then f x else 0

end Erdos3.Peeling


namespace Erdos3

open scoped BigOperators

namespace CellRefinement

variable {G : Type*} [AddCommGroup G]

noncomputable def bilinearIntegral (A B : Finset G) (a f g : G → ℝ) : ℝ :=
  𝔼 x ∈ A, 𝔼 y ∈ B, f x * g y * a (x + y)

end CellRefinement
end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedSummandCorrelation
namespace OAI

section

open scoped BigOperators

namespace Erdos3

noncomputable def finiteCorrelation {Ω : Type*} (Q : Finset Ω) (f u : Ω → ℂ) : ℂ :=
  𝔼 x ∈ Q, f x * star (u x)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BufferedSiteExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem siteFactorTensor_factor_bound {D U : Type*} [Fintype D] (f : D → U → ℂ)
    (hf : ∀ d x, ‖f d x‖ ≤ 1) (x : D → U) : ‖∏ d, f d (x d)‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun d _ => hf d (x d))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FiniteFourierSmoothing
namespace OAI

section

open _root_.Finset Function Real
open scoped BigOperators ComplexConjugate NNReal

namespace Erdos3.Chang

variable {G : Type*} [Fintype G] [AddCommGroup G]

noncomputable def spectrumSum (A : Finset G) (psi : AddChar G ℂ) : ℂ :=
  ∑ x ∈ A, psi x

noncomputable def largeSpectrum (A : Finset G) (eta : ℝ) : Finset (AddChar G ℂ) :=
  Finset.univ.filter fun psi ↦ eta * A.card ≤ ‖spectrumSum A psi‖

@[simp]
theorem mem_largeSpectrum {A : Finset G} {eta : ℝ} {psi : AddChar G ℂ} :
    psi ∈ largeSpectrum A eta ↔ eta * A.card ≤ ‖spectrumSum A psi‖ := by
  simp [largeSpectrum]

end Erdos3.Chang

end

section

namespace Erdos3.Chang

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

omit [Fintype G] in
theorem spectrumSum_map_subRight (T : Finset G) (z : G) (psi : AddChar G ℂ) :
    spectrumSum (T.map (Equiv.subRight z).toEmbedding) psi =
      spectrumSum T psi * psi (-z) := by
  unfold spectrumSum
  rw [Finset.sum_map]
  simp only [Equiv.toEmbedding_apply, Equiv.subRight_apply,
    sub_eq_add_neg, AddChar.map_add_eq_mul]
  rw [Finset.sum_mul]

theorem norm_spectrumSum_map_subRight (T : Finset G) (z : G) (psi : AddChar G ℂ) :
    ‖spectrumSum (T.map (Equiv.subRight z).toEmbedding) psi‖ = ‖spectrumSum T psi‖ := by
  rw [spectrumSum_map_subRight, norm_mul, AddChar.norm_apply, mul_one]

theorem mem_largeSpectrum_map_subRight_iff
    (T : Finset G) (z : G) (eta : ℝ) (psi : AddChar G ℂ) :
    psi ∈ largeSpectrum (T.map (Equiv.subRight z).toEmbedding) eta ↔
      psi ∈ largeSpectrum T eta := by
  rw [mem_largeSpectrum, mem_largeSpectrum, Finset.card_map, norm_spectrumSum_map_subRight]

end Erdos3.Chang

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalMomentScale
namespace OAI

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

noncomputable def localMomentGain (delta : ℝ) : ℝ :=
  momentAmplificationGain (delta ^ 2 / 8) / 2

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

noncomputable def replacementIntegral (D Q C : Finset G) (a f g : G → ℝ) : ℝ :=
  𝔼 z ∈ Q, 𝔼 x ∈ D, 𝔼 t ∈ C, f x * g (z + t) * a (x + (z + t))

end Erdos3.CellRefinement

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RectangularGridCharacter
namespace OAI

section

namespace Erdos3.CircleFourier

open scoped Real NNReal

noncomputable def characterLipConstant : ℝ≥0 := ⟨2 * Real.pi, by positivity⟩

theorem coe_characterLipConstant : (characterLipConstant : ℝ) = 2 * Real.pi := rfl

end Erdos3.CircleFourier

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

def integerAffineMap (A : σ → τ → ℤ) (b : σ → ℤ) (x : τ → ℤ) (i : σ) : ℤ :=
  b i + ∑ j, A i j * x j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ReplacementCellPotential
namespace OAI

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

noncomputable def replacementPotential (D Q C : Finset G) (f g : G → ℝ) : ℝ :=
  𝔼 z ∈ Q, ((𝔼 x ∈ D, f x) * cellAverage C g z) ^ (1 / 4 : ℝ)

end Erdos3.CellRefinement

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteCellRefinement
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def matchedCellSpace (L S : Finset G) : Finset (G × (G × G)) := L ×ˢ (S ×ˢ S)

noncomputable def matchedFirstCell (C : Finset G) (f : G → ℝ) (z : G × (G × G)) : ℝ :=
  cellAverage C f z.1

noncomputable def matchedSecondCell (C : Finset G) (f : G → ℝ) (z : G × (G × G)) : ℝ :=
  cellAverage C f (-z.1 + z.2.1 + z.2.2)

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

noncomputable def matchedPairAverage (L S : Finset G) (F : G → G → ℝ) : ℝ :=
  𝔼 r ∈ L, 𝔼 s ∈ S, 𝔼 t ∈ S, F r (-r + s + t)

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

noncomputable def matchedIndependentAverage (L S C : Finset G) (F : G → G → ℝ) : ℝ :=
  𝔼 u ∈ C, 𝔼 v ∈ C, matchedPairAverage L S (fun x y => F (x + u) (y + v))

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G]

noncomputable def matchedIntegral (L S : Finset G) (a f g : G → ℝ) : ℝ :=
  matchedPairAverage L S (fun x y => f x * g y * a (x + y))

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G]

noncomputable def parentMatchedAverage (A B L S : Finset G) (F : G → G → ℝ) : ℝ :=
  𝔼 x ∈ A, 𝔼 y ∈ B, matchedPairAverage L S (fun r q => F (x + r) (y + q))

variable [DecidableEq G]

noncomputable def parentTruncatedIntegral (A B L S : Finset G) (a f g : G → ℝ) : ℝ :=
  𝔼 x ∈ A, 𝔼 y ∈ B, matchedIntegral L S (fun z => a (x + y + z))
    (Peeling.slice L (fun r => f (x + r))) (Peeling.slice L (fun q => g (y + q)))

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def centerSlice (L : Finset G) (f : G → ℝ) (x : G) : G → ℝ :=
  Peeling.slice L (fun r => f (x + r))

noncomputable def centerPotential (L : Finset G) (f g : G → ℝ) (z : G × G) : ℝ :=
  (cellAverage L f z.1 * cellAverage L g z.2) ^ (1 / 4 : ℝ)

noncomputable def centerMatchedIntegral (L S : Finset G) (a f g : G → ℝ) (z : G × G) : ℝ :=
  matchedIntegral L S (fun r => a (z.1 + z.2 + r)) (centerSlice L f z.1) (centerSlice L g z.2)

noncomputable def centerChildIntegral (L S : Finset G) (a f g : G → ℝ)
    (z : G × G) (C : Finset G) : ℝ :=
  𝔼 t ∈ matchedCellSpace L S,
    bilinearIntegral (C.image (fun r => t.1 + r))
      (C.image (fun r => (-t.1 + t.2.1 + t.2.2) + r))
      (fun r => a (z.1 + z.2 + r)) (centerSlice L f z.1) (centerSlice L g z.2)

noncomputable def centerChildPotential (L S : Finset G) (f g : G → ℝ)
    (z : G × G) (C : Finset G) : ℝ :=
  𝔼 t ∈ matchedCellSpace L S,
    (matchedFirstCell C (centerSlice L f z.1) t *
      matchedSecondCell C (centerSlice L g z.2) t) ^ (1 / 4 : ℝ)

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

def CellBilinearBound (C : Finset G) (a : G → ℝ) (T : ℝ) : Prop :=
  ∀ origin : G, ∀ f g : G → ℝ,
    (∀ x, 0 ≤ f x ∧ f x ≤ 1) → (∀ x, 0 ≤ g x ∧ g x ≤ 1) →
    (∀ x, x ∉ C → f x = 0) → (∀ x, x ∉ C → g x = 0) →
    bilinearIntegral C C (fun x => a (origin + x)) f g ≤
      T * ((𝔼 x ∈ C, f x) * (𝔼 x ∈ C, g x)) ^ (1 / 4 : ℝ)

end Erdos3.CellRefinement

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndependentReturnScale
namespace OAI

section

namespace Erdos3.CellRefinement

open scoped NNReal

noncomputable def outerMatchingScale (rank : ℕ) (W epsilon : ℝ) (scale : ℝ≥0) : ℝ≥0 :=
  min scale (localizedAverageScale rank W (epsilon / 4))

noncomputable def outerMatchingScaleLoss (rank : ℕ) (A E T : ℝ) : ℝ :=
  T + rank + A + E + 1602

end Erdos3.CellRefinement

end

section

namespace Erdos3.LocalConvolution

open scoped NNReal

noncomputable def controlledLocalMomentScale (rank : ℕ) (M delta : ℝ) : ℝ≥0 :=
  localizedAverageScale rank M (min (delta / 2) (localMomentGain delta) / 3) / 2

noncomputable def localMomentErrorBudget (delta : ℝ) : ℝ :=
  -Real.log (2 * min (delta / 2) (localMomentGain delta) / 3)

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators NNReal

noncomputable def independentReturnScale (rank : ℕ) (M epsilon : ℝ) : ℝ≥0 :=
  localizedAverageScale rank M (epsilon / 2) / 2

end Erdos3.CellRefinement

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalBoostedAlmostPeriods
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

open _root_.Finset
open scoped BigOperators

variable {N : ℕ} [NeZero N]

def realSetIndicator (M : Finset (ZMod N)) (x : ZMod N) : ℝ := if x ∈ M then 1 else 0

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SpectralLogBudget
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

noncomputable def spectralIterationFactor (epsilon : ℝ) : ℝ :=
  (1 + Real.log (16 / epsilon)) / Real.log 2 + 2

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.QuarticSamplingBudget
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

noncomputable def samplingCubicFactor (epsilon : ℝ) : ℝ :=
  2 * (256 * Real.exp 1 ^ 2 / (epsilon / 8) ^ 2) * spectralIterationFactor epsilon ^ 2 + 1

noncomputable def rankQuarticFactor (epsilon : ℝ) : ℝ :=
  8 * (1 + Real.log 4 + samplingCubicFactor epsilon)

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalizedSiftingAlmostPeriods
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

open scoped NNReal Pointwise

noncomputable def almostPeriodicityWidthConstant (epsilon : ℝ) : ℝ :=
  10240000000 * (rankQuarticFactor epsilon + 1) / epsilon + 8

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MatchedFlatDecay
namespace OAI

section

namespace Erdos3

noncomputable def flatComparisonDelta (epsilon : ℝ) : ℝ := epsilon / (4 * (2 + epsilon))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PeelingReplacementPotential
namespace OAI

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

noncomputable def replacementPotentialSum (A Q : Finset G) (shape : Finset G → Finset G)
    (g : G → ℝ) : (G → ℝ) → List (Finset G) → ℝ
  | _, [] => 0
  | f, D :: ds => (D.card : ℝ) / A.card * replacementPotential D Q (shape D) f g +
      replacementPotentialSum A Q shape g (Peeling.remainder D f) ds

end Erdos3.CellRefinement

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeelingChildBound
namespace OAI

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

noncomputable def replacementIntegralSum (A Q : Finset G) (shape : Finset G → Finset G)
    (a g : G → ℝ) : (G → ℝ) → List (Finset G) → ℝ
  | _, [] => 0
  | f, D :: ds => (D.card : ℝ) / A.card * replacementIntegral D Q (shape D) a f g +
      replacementIntegralSum A Q shape a g (Peeling.remainder D f) ds

end Erdos3.CellRefinement

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UnbalancedBohrShape
namespace OAI

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

noncomputable def unbalancedRankExtra (c p H : ℝ) : ℕ :=
  ⌈almostPeriodicityWidthConstant (c / 64) * (1 + (3 * H + 1) * p ^ 2) ^ 4⌉₊

end Erdos3.LocalConvolution

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.UnbalancedWidthBudget
namespace OAI

section

namespace Erdos3.LocalConvolution

open CyclicCrootSisask

noncomputable def unbalancedErrorBudget (c : ℝ) : ℝ := -Real.log (c / 32)

noncomputable def unbalancedWidthLoss (rank : ℕ) (c p H : ℝ) : ℝ :=
  ((rank : ℝ) + 2 * H * p ^ 2 + unbalancedErrorBudget c + 1600) +
    (((rank + unbalancedRankExtra c p H : ℕ) : ℝ) + 2 * p + unbalancedErrorBudget c + 1600) +
    8 + almostPeriodicityWidthConstant (c / 64) *
      (1 + (3 * H + 1) * p ^ 2 + Real.log (2 + rank))

end Erdos3.LocalConvolution

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinatedMatchingScale
namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped NNReal

noncomputable def coordinatedMatchingScale (rank : ℕ) (M delta c : ℝ)
    (kappa : ℝ≥0) : ℝ≥0 :=
  min (kappa / 2) (min (controlledLocalMomentScale rank M delta)
    (localizedAverageScale rank (M ^ 2) (c / 32) / 2))

noncomputable def coordinatedMatchingScaleLoss (rank : ℕ) (P K delta c : ℝ) : ℝ :=
  K + rank + 2 * P + localMomentErrorBudget delta + unbalancedErrorBudget c + 1604

end Erdos3.CellRefinement

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CoordinatedBohrMatching
namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

noncomputable def matchingWidthLoss (rank : ℕ) (P K delta c : ℝ) : ℝ :=
  K + coordinatedMatchingScaleLoss rank P K delta c + 12

end Erdos3.CellRefinement

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RefinementMatchingGeometry
namespace OAI

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

noncomputable def unbalancedReturnWidthLoss (rank : ℕ) (c p H A E : ℝ) : ℝ :=
  (rank : ℝ) + A + E + 1602 + unbalancedWidthLoss rank c p H

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

noncomputable def refinementMatchingWidthLoss (rank : ℕ) (p H Q E J T delta : ℝ) : ℝ :=
  matchingWidthLoss rank p (outerMatchingScaleLoss rank Q E T) delta (localMomentGain delta) +
    unbalancedReturnWidthLoss rank (localMomentGain delta) p H Q J

end Erdos3.CellRefinement

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedCutoffs
namespace OAI

section

namespace Erdos3

theorem abs_div_sub_div_bound {a b u v r D M E : ℝ} (hr : 0 < r)
    (hu : r ≤ u) (hv : r ≤ v) (hD : 0 ≤ D) (hM : 0 ≤ M) (hE : 0 ≤ E)
    (hab : |a - b| ≤ D) (hb : |b| ≤ M) (huv : |u - v| ≤ E) :
    |a / u - b / v| ≤ D / r + M * E / (r * r) := by
  have hu0 : 0 < u := hr.trans_le hu
  have hv0 : 0 < v := hr.trans_le hv
  have heq : a / u - b / v = (a - b) / u + b * (v - u) / (u * v) := by
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ |(a - b) / u| + |b * (v - u) / (u * v)| := abs_add_le _ _
    _ = |a - b| / u + |b| * |u - v| / (u * v) := by
      rw [abs_div, abs_div, abs_mul, abs_of_pos hu0, abs_of_pos (mul_pos hu0 hv0), abs_sub_comm v u]
    _ ≤ D / r + M * E / (r * r) :=
      add_le_add (div_le_div₀ hD hab hr hu)
        (div_le_div₀ (mul_nonneg hM hE) (mul_le_mul hb huv (abs_nonneg _) hM)
          (mul_pos hr hr) (mul_le_mul hu hv hr.le hu0.le))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.NormalizedRealBoxHalfGrid
namespace OAI

section

namespace Erdos3

noncomputable def uniformIntervalGrid (B : ℝ) (N : ℕ) (k : Fin (N + 1)) : ℝ :=
  -B + (2 * B / N) * k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.QuantitativeMetricPartition
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {ι X : Type*} [Fintype ι] [PseudoMetricSpace X]

noncomputable def boxCoverMeshCount (B : ℝ) (K : ℝ≥0) (ε : ℝ) : ℕ :=
  ⌈2 * B * K / ε⌉₊ + 1

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {X : Type*} [PseudoMetricSpace X]

noncomputable def metricTent (c : X) (r : ℝ) (x : X) : ℝ := max 0 (2 * r - dist x c)

theorem metricTent_nonneg (c : X) (r : ℝ) (x : X) : 0 ≤ metricTent c r x := le_max_left _ _

theorem metricTent_le (c : X) {r : ℝ} (hr : 0 ≤ r) (x : X) : metricTent c r x ≤ 2 * r :=
  max_le (by linarith) (by linarith [dist_nonneg (x := x) (y := c)])

theorem abs_metricTent_sub_le (c : X) (r : ℝ) (x y : X) :
    |metricTent c r x - metricTent c r y| ≤ dist x y := by
  calc
    _ = |max (2 * r - dist x c) 0 - max (2 * r - dist y c) 0| := by
      simp only [metricTent, max_comm]
    _ ≤ |(2 * r - dist x c) - (2 * r - dist y c)| := abs_max_sub_max_le_abs _ _ _
    _ = |dist x c - dist y c| := by
      rw [show (2 * r - dist x c) - (2 * r - dist y c) = -(dist x c - dist y c) by ring, abs_neg]
    _ ≤ dist x y := abs_dist_sub_le x y c

variable {ι : Type*} [Fintype ι]

noncomputable def metricTentSum (c : ι → X) (r : ℝ) (x : X) : ℝ := ∑ i, metricTent (c i) r x

theorem abs_metricTentSum_sub_le (c : ι → X) (r : ℝ) (x y : X) :
    |metricTentSum c r x - metricTentSum c r y| ≤ Fintype.card ι * dist x y := by
  unfold metricTentSum
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |metricTent (c i) r x - metricTent (c i) r y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, dist x y := Finset.sum_le_sum fun i _ => abs_metricTent_sub_le (c i) r x y
    _ = _ := by simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxBlockBudget
namespace OAI

section

namespace Erdos3.BoxProgressionPartition

variable {ι : Type*}
  [Fintype ι]
  [DecidableEq ι]
  {N : ι → ℕ}

noncomputable def normalizedPoint (x : ∀ i, Fin (N i)) : ι → ℝ :=
  fun i => (x i).val / (N i : ℝ)

end Erdos3.BoxProgressionPartition

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

def residueMatrixShift {I J : Type*} [Fintype J]
    (C D : Matrix I J ℤ) (q : ℕ) (r : J → ℤ) : I → ℤ :=
  fun i => ((C - D) *ᵥ r) i / (q : ℤ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductPMFMap
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def independentProductPMF {D X : Type*} [Fintype D] [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : D → PMF X) : PMF (D → X) :=
  (Measure.pi (fun d => (p d).toMeasure)).toPMF

theorem independentProductPMF_apply {D X : Type*} [Fintype D] [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : D → PMF X) (x : D → X) :
    independentProductPMF p x = ∏ d, p d (x d) := by
  simp only [independentProductPMF, Measure.toPMF_apply, Measure.pi_singleton]
  exact Finset.prod_congr rfl (fun d _ => (p d).toMeasure_apply_singleton (x d) (measurableSet_singleton _))

theorem independentProductPMF_toReal {D X : Type*} [Fintype D] [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : D → PMF X) (x : D → X) :
    (independentProductPMF p x).toReal = ∏ d, (p d (x d)).toReal := by
  rw [independentProductPMF_apply, ENNReal.toReal_prod]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MatrixSupInverse
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def matrixSupCLM {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) : (κ → ℝ) →L[ℝ] (ι → ℝ) :=
  A.mulVecLin.toContinuousLinearMap

theorem matrixSupCLM_norm_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) {H : ℝ} (hH : 0 ≤ H) (hA : ∀ i j, |A i j| ≤ H) :
    ‖matrixSupCLM A‖ ≤ Fintype.card κ * H := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change ‖∑ j, A i j * x j‖ ≤ _
  rw [Real.norm_eq_abs]
  calc
    _ ≤ ∑ j, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : κ, H * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      have hx : |x j| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
      exact mul_le_mul (hA i j) hx (abs_nonneg _) hH
    _ = _ := by simp [mul_assoc]

theorem matrixSupCLM_mul {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (A : Matrix ι κ ℝ) (B : Matrix κ ν ℝ) :
    matrixSupCLM (A * B) = (matrixSupCLM A).comp (matrixSupCLM B) := by
  ext x i
  change ((A * B).mulVec x) i = (A.mulVec (B.mulVec x)) i
  rw [Matrix.mulVec_mulVec]

theorem matrixSupCLM_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    matrixSupCLM (1 : Matrix ι ι ℝ) = ContinuousLinearMap.id ℝ (ι → ℝ) := by
  ext x i
  change ((1 : Matrix ι ι ℝ).mulVec x) i = x i
  simp

theorem matrixSupCLM_inverse_spec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.det ≠ 0) :
    (matrixSupCLM A).IsInvertible ∧ (matrixSupCLM A).inverse = matrixSupCLM A⁻¹ := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hright : (matrixSupCLM A).comp (matrixSupCLM A⁻¹) = ContinuousLinearMap.id ℝ (ι → ℝ) := by
    rw [← matrixSupCLM_mul, A.mul_nonsing_inv hunit, matrixSupCLM_one]
  have hleft : (matrixSupCLM A⁻¹).comp (matrixSupCLM A) = ContinuousLinearMap.id ℝ (ι → ℝ) := by
    rw [← matrixSupCLM_mul, A.nonsing_inv_mul hunit, matrixSupCLM_one]
  exact ⟨ContinuousLinearMap.IsInvertible.of_inverse hright hleft,
    ContinuousLinearMap.inverse_eq hright hleft⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteReciprocalTenthTail
namespace OAI

section

namespace Erdos3

theorem one_sub_sum_le_positive_prod {ι : Type*} (S : Finset ι) (f e : ι → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) (he : ∀ i ∈ S, e i ∈ Set.Icc (0 : ℝ) 1)
    (hlower : ∀ i ∈ S, 1 - e i ≤ f i) :
    1 - ∑ i ∈ S, e i ≤ ∏ i ∈ S, f i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hfS := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have heS := fun i hi => he i (Finset.mem_insert_of_mem hi)
    have hlS := fun i hi => hlower i (Finset.mem_insert_of_mem hi)
    have hea := he a (Finset.mem_insert_self _ _)
    have hs := Finset.sum_nonneg (fun i hi => (heS i hi).1)
    have h₁ := mul_le_mul_of_nonneg_left (ih hfS heS hlS) (sub_nonneg.mpr hea.2)
    have h₂ := mul_le_mul_of_nonneg_right (hlower a (Finset.mem_insert_self _ _))
      (Finset.prod_nonneg hfS)
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    nlinarith [mul_nonneg hea.1 hs]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PivotNormalizedMatrix
namespace OAI

section

namespace Erdos3

open scoped Matrix BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def normalizedIntegerPivot (A : Matrix I I ℤ) (S P : I → ℝ) : Matrix I I ℝ :=
  Matrix.diagonal (fun i => (P i)⁻¹) * A.map (Int.castRingHom ℝ) * Matrix.diagonal S

theorem normalizedIntegerPivot_entry (A : Matrix I I ℤ) (S P : I → ℝ) (i j : I) :
    normalizedIntegerPivot A S P i j = (A i j : ℝ) * S j / P i := by
  simp only [normalizedIntegerPivot, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.map_apply, Int.coe_castRingHom, div_eq_mul_inv]
  ring

theorem normalizedIntegerPivot_abs_det (A : Matrix I I ℤ) (S P : I → ℝ)
    (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) :
    |(normalizedIntegerPivot A S P).det| =
      (A.det.natAbs : ℝ) * (∏ i, S i) / (∏ i, P i) := by
  have hprodS : 0 < ∏ i, S i := Finset.prod_pos fun i _ => hS i
  have hprodP : 0 < ∏ i, P i := Finset.prod_pos fun i _ => hP i
  have hd : (A.map (Int.castRingHom ℝ)).det = (A.det : ℝ) :=
    (RingHom.map_det (Int.castRingHom ℝ) A).symm
  simp only [normalizedIntegerPivot, Matrix.det_mul, Matrix.det_diagonal,
    hd, Finset.prod_inv_distrib, abs_mul, abs_inv, abs_of_pos hprodS, abs_of_pos hprodP,
    Nat.cast_natAbs, Int.cast_abs, div_eq_mul_inv]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerFiberUniformBound
namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable def normalizedIntegerColumns (B : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ) :
    Matrix I J ℝ :=
  Matrix.diagonal (fun i => (P i)⁻¹) * B.map (Int.castRingHom ℝ) * Matrix.diagonal T

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev BoxAmbient (T : ι → ℕ) := ∀ i, ZMod (4 * T i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AffinePhaseBias
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem expect_pi_product {ι : Type*} {κ : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)]
    (f : ∀ i, κ i → ℂ) :
    (𝔼 x : ∀ i, κ i, ∏ i, f i (x i)) = ∏ i, 𝔼 y : κ i, f i y := by
  classical
  simp_rw [Fintype.expect_eq_sum_div_card]
  rw [Finset.prod_div_distrib, Fintype.prod_sum, Fintype.card_pi, Nat.cast_prod]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RootDifferenceMatrix
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

def rootDifferenceMatrix {I J R : Type*} [CommRing R]
    (root : J → R) (D : Matrix I J R) : Matrix (Unit ⊕ I) (Unit ⊕ J) R :=
  Matrix.fromBlocks (1 : Matrix Unit Unit R) (Matrix.of (fun (_ : Unit) j => root j)) (0 : Matrix I Unit R) D

theorem rootDifferenceMatrix_det {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (root : I → R) (A : Matrix I I R) : (rootDifferenceMatrix root A).det = A.det := by
  change (Matrix.fromBlocks (1 : Matrix Unit Unit R) (Matrix.of (fun (_ : Unit) j => root j))
    (0 : Matrix I Unit R) A).det = A.det
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialPivotNormalization
namespace OAI

section

namespace Erdos3

open scoped Matrix

def selectedSpatialPivot {I J R : Type*} [CommRing R]
    (root : J → R) (D : Matrix I J R) (s : I ↪ J) : Matrix (Unit ⊕ I) (Unit ⊕ I) R :=
  rootDifferenceMatrix (fun i => root (s i)) (D.submatrix id s)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedCoefficientEvaluation
namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {I J N : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]

theorem normalizedIntegerColumns_entry (B : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ)
    (i : I) (j : J) : normalizedIntegerColumns B T P i j = (P i)⁻¹ * B i j * T j := by
  simp [normalizedIntegerColumns, Matrix.diagonal_mul, Matrix.mul_diagonal]

end Erdos3

end

section

namespace Erdos3

theorem normalizedIntegerColumns_entry_div {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ) (i : I) (j : J) :
    normalizedIntegerColumns A T P i j = (A i j : ℝ) * T j / P i := by
  rw [normalizedIntegerColumns_entry]
  simp only [div_eq_mul_inv]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.UniformSelectedCoefficientProductLaw
namespace OAI

section

namespace Erdos3

open scoped ENNReal Classical

theorem pmf_bind_point_cap {X Y : Type*} (p : PMF X) (q : X → PMF Y)
    {C : ℝ≥0∞} (y : Y) (hq : ∀ x, q x y ≤ C) : p.bind q y ≤ C := by
  rw [PMF.bind_apply]
  calc
    _ ≤ ∑' x, p x * C := ENNReal.tsum_le_tsum (fun x => by gcongr; exact hq x)
    _ = C := by rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

theorem pmf_map_toReal_indicator {X Y : Type*} [DecidableEq Y] (p : PMF X) (f : X → Y) (y : Y) :
    (p.map f y).toReal = ∑' x, (p x).toReal * (if f x = y then 1 else 0) := by
  rw [PMF.map_apply, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro x
    by_cases h : y = f x
    · simp [h]
    · simp [h, Ne.symm h]
  · intro x
    split_ifs <;> first | exact p.apply_ne_top x | exact ENNReal.zero_ne_top

theorem pmf_point_indicator_norm {X Y : Type*} [DecidableEq Y] (p : PMF X) (f : X → Y) (y : Y) :
    ‖∑' x, ((p x).toReal : ℂ) * (if f x = y then 1 else 0)‖ = (p.map f y).toReal := by
  calc
    _ = ‖((∑' x, (p x).toReal * (if f x = y then 1 else 0) : ℝ) : ℂ)‖ := by
      simp only [Complex.ofReal_tsum, Complex.ofReal_mul, apply_ite, Complex.ofReal_one, Complex.ofReal_zero]
    _ = _ := by rw [← pmf_map_toReal_indicator, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialStarCoordinates
namespace OAI

section

namespace Erdos3

def spatialStar {I R : Type*} [Add R] (v : (Unit ⊕ I) → R) : (Unit ⊕ I) → R :=
  Sum.elim (fun _ => v (.inl ())) (fun i => v (.inl ()) + v (.inr i))

def spatialUnstar {I R : Type*} [Sub R] (v : (Unit ⊕ I) → R) : (Unit ⊕ I) → R :=
  Sum.elim (fun _ => v (.inl ())) (fun i => v (.inr i) - v (.inl ()))

theorem spatialUnstar_star {I R : Type*} [AddCommGroup R] (v : (Unit ⊕ I) → R) :
    spatialUnstar (spatialStar v) = v := by
  funext i
  cases i with
  | inl i => cases i; rfl
  | inr i => simp [spatialUnstar, spatialStar]

theorem spatialStar_unstar {I R : Type*} [AddCommGroup R] (v : (Unit ⊕ I) → R) :
    spatialStar (spatialUnstar v) = v := by
  funext i
  cases i with
  | inl i => cases i; rfl
  | inr i => simp [spatialUnstar, spatialStar]

def spatialStarVertex {I : Type*} : (Unit ⊕ I) → Finset I :=
  Sum.elim (fun _ => ∅) (fun i => {i})

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientRowReindex
namespace OAI


namespace Erdos3


open MeasureTheory
open scoped BigOperators NNReal

structure CoefficientFiberControl {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (S : J → ℝ) (H L : ℝ) (h : ℕ) (C U G : ℝ) : Prop where
  det_ne_zero : (A.submatrix id s).det ≠ 0
  scale_lower : ∀ j, H / L ^ h ≤ S j
  integer_entry_bound : ∀ i j, |(A i (s j) : ℝ)| ≤ C * L ^ h
  normalized_entry_bound : ∀ i j, |normalizedIntegerColumns A S (fun _ => H) i j| ≤ C
  inverse_bound : ‖(matrixSupCLM (normalizedIntegerPivot (A.submatrix id s)
    (fun i => S (s i)) (fun _ => H))).inverse‖ ≤ U
  index_bound : (A.mulVecLin.range.toAddSubgroup.index : ℝ) ≤ G

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeriodicIsometricAction
namespace OAI

section

namespace Erdos3.CircleFourier

theorem fejer_cutoff_bound {L δ p : ℝ} (hp : 0 ≤ p) (hL : 0 ≤ L)
    (hδ : 0 < δ) (hLp : L ≤ Real.exp p) (hδp : δ⁻¹ ≤ Real.exp p) :
    (L + 1) ^ 3 / δ ^ 3 + 2 ≤ Real.exp ((p + 2) ^ 4) := by
  have hexp : 1 ≤ Real.exp p := Real.one_le_exp hp
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hS : L + 1 ≤ Real.exp (p + 1) := by
    rw [Real.exp_add]
    nlinarith
  have hR : (L + 1) ^ 3 / δ ^ 3 ≤ Real.exp (6 * p + 3) := by
    calc
      _ = (L + 1) ^ 3 * (δ⁻¹) ^ 3 := by rw [div_eq_mul_inv, inv_pow]
      _ ≤ (Real.exp (p + 1)) ^ 3 * (Real.exp p) ^ 3 := by gcongr
      _ = Real.exp (6 * p + 3) := by rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  have hbase : 1 ≤ Real.exp (6 * p + 3) := Real.one_le_exp (by linarith)
  calc
    _ ≤ Real.exp (6 * p + 3) * Real.exp 2 := by nlinarith
    _ = Real.exp (6 * p + 5) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp ((p + 2) ^ 4) := by
      apply Real.exp_le_exp.mpr
      have hsq : 4 ≤ (p + 2) ^ 2 := by nlinarith
      nlinarith [sq_nonneg p, mul_nonneg (sub_nonneg.mpr hsq) (sq_nonneg (p + 2))]

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveNormalizationError
namespace OAI

section

namespace Erdos3

theorem complex_remove_normalization {N : ℂ} {Z : ℝ} (hZ : 0 < Z) (hN : ‖N‖ ≤ Z) :
    ‖N/(Z : ℂ)-N‖ ≤ |Z-1| := by
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  have hunit : ‖N/(Z : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hZ.le]
    exact (div_le_one hZ).mpr hN
  have he : N/(Z : ℂ)-N = (N/(Z : ℂ))*(1-(Z : ℂ)) := by field_simp
  rw [he, norm_mul]
  calc
    _ ≤ 1 * ‖1-(Z : ℂ)‖ := mul_le_mul_of_nonneg_right hunit (norm_nonneg _)
    _ = |Z-1| := by
      rw [one_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_sub_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X I : Type*} [PseudoMetricSpace X] [Fintype I]

noncomputable def regularizedTentPartition (c : I → X) (r : ℝ) (i : I) (x : X) : ℝ :=
  metricTent (c i) r x / max r (metricTentSum c r x)

theorem regularizedTentPartition_range (c : I → X) {r : ℝ} (hr : 0 < r) (i : I) (x : X) :
    0 ≤ regularizedTentPartition c r i x ∧ regularizedTentPartition c r i x ≤ 1 := by
  have hd : 0 < max r (metricTentSum c r x) := hr.trans_le (le_max_left _ _)
  refine ⟨div_nonneg (metricTent_nonneg _ _ _) hd.le, (div_le_one hd).mpr ?_⟩
  exact (Finset.single_le_sum (fun j _ => metricTent_nonneg (c j) r x)
    (Finset.mem_univ i)).trans (le_max_right _ _)

theorem regularizedTentPartition_lipschitz (c : I → X) {r : ℝ≥0} (hr : 0 < r) (i : I) :
    LipschitzWith ((2 * Fintype.card I + 1) / r) (regularizedTentPartition c r i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hd : |max (r : ℝ) (metricTentSum c r x) - max (r : ℝ) (metricTentSum c r y)| ≤
      Fintype.card I * dist x y := by
    rw [max_comm (r : ℝ), max_comm (r : ℝ)]
    exact (abs_max_sub_max_le_abs _ _ _).trans (abs_metricTentSum_sub_le c r x y)
  have hb : |metricTent (c i) (r : ℝ) y| ≤ 2 * (r : ℝ) := by
    rw [abs_of_nonneg (metricTent_nonneg _ _ _)]
    exact metricTent_le (c i) r.coe_nonneg y
  have h := abs_div_sub_div_bound (show (0 : ℝ) < r from hr)
    (le_max_left _ _) (le_max_left _ _) dist_nonneg
    (by positivity : (0 : ℝ) ≤ 2 * r) (by positivity : (0 : ℝ) ≤ Fintype.card I * dist x y)
    (abs_metricTent_sub_le (c i) r x y) hb hd
  rw [Real.dist_eq]
  apply h.trans_eq
  push_cast
  field_simp
  ring

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def intervalSiteCount (B r : ℝ) : ℕ := boxCoverMeshCount B 1 r + 1

noncomputable def intervalSiteCenter (B r : ℝ) (i : Fin (intervalSiteCount B r)) : ℝ :=
  uniformIntervalGrid B (boxCoverMeshCount B 1 r) i

noncomputable def intervalSiteWeight (B r : ℝ) : Fin (intervalSiteCount B r) → ℝ → ℝ :=
  regularizedTentPartition (intervalSiteCenter B r) r

theorem intervalSiteWeight_range (B : ℝ) {r : ℝ} (hr : 0 < r)
    (i : Fin (intervalSiteCount B r)) (x : ℝ) :
    0 ≤ intervalSiteWeight B r i x ∧ intervalSiteWeight B r i x ≤ 1 :=
  regularizedTentPartition_range _ hr i x

theorem intervalSiteWeight_lipschitz (B : ℝ) {r : ℝ≥0} (hr : 0 < r)
    (i : Fin (intervalSiteCount B r)) :
    LipschitzWith ((2 * intervalSiteCount B r + 1) / r) (intervalSiteWeight B r i) := by
  have h := regularizedTentPartition_lipschitz (intervalSiteCenter B r) hr i
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (regularizedTentPartition (intervalSiteCenter B r) r i x)
    (regularizedTentPartition (intervalSiteCenter B r) r i y) ≤ _
  simpa only [Fintype.card_fin] using h.dist_le_mul x y

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteInnerProgressionFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_finset_expect_le_one {X : Type*} (A : Finset X) (f : X → ℂ)
    (hf : ∀ x ∈ A, ‖f x‖ ≤ 1) : ‖𝔼 x ∈ A, f x‖ ≤ 1 := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp
  · exact (RCLike.norm_expect_le (K := ℂ)).trans (Finset.expect_le hA hf)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ExternalFamilyCircleProjection
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_weighted_mean_sub_le {G : Type*} [Fintype G] [Nonempty G]
    (w f g : G → ℂ) {B rho : ℝ} (hB : 0 ≤ B)
    (hw : ∀ n, ‖w n‖ ≤ B) (hfg : ∀ n, ‖f n - g n‖ ≤ rho) :
    ‖(𝔼 n, w n * f n) - (𝔼 n, w n * g n)‖ ≤ B * rho := by
  rw [← Finset.expect_sub_distrib]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply (Finset.expect_le_expect _).trans_eq (Finset.expect_const Finset.univ_nonempty _)
  intro n _
  rw [← mul_sub, norm_mul]
  exact mul_le_mul (hw n) (hfg n) (norm_nonneg _) hB

theorem finite_projection_tested_error {G J : Type*} [Fintype G] [Nonempty G] [Fintype J]
    (w f projected : G → ℂ) (v : J → G → ℂ) (keep : J → Prop) [DecidablePred keep]
    {B rho tau : ℝ} (hB : 0 ≤ B) (htau : 0 ≤ tau)
    (hw : ∀ n, ‖w n‖ ≤ B)
    (hfull : ∀ n, ‖f n - ∑ j, v j n‖ ≤ rho)
    (hprojected : ∀ n, ‖(∑ j, if keep j then v j n else 0) - projected n‖ ≤ rho)
    (hdiscard : ∀ j, ¬ keep j → ‖𝔼 n, w n * v j n‖ ≤ tau) :
    ‖(𝔼 n, w n * f n) - (𝔼 n, w n * projected n)‖ ≤
      2 * B * rho + Fintype.card J * tau := by
  have hfirst := norm_weighted_mean_sub_le w f (fun n => ∑ j, v j n) hB hw hfull
  have hlast := norm_weighted_mean_sub_le w
    (fun n => ∑ j, if keep j then v j n else 0) projected hB hw hprojected
  have hid : (𝔼 n, w n * ∑ j, v j n) -
      (𝔼 n, w n * ∑ j, if keep j then v j n else 0) =
      ∑ j, if keep j then 0 else (𝔼 n, w n * v j n) := by
    calc
      _ = 𝔼 n, w n * ((∑ j, v j n) - ∑ j, if keep j then v j n else 0) := by
        simp only [mul_sub, Finset.expect_sub_distrib]
      _ = 𝔼 n, ∑ j, if keep j then 0 else w n * v j n := by
        apply Finset.expect_congr rfl
        intro n _
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : keep j <;> simp [hj]
      _ = ∑ j, 𝔼 n, if keep j then 0 else w n * v j n := Finset.expect_sum_comm _ _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : keep j <;> simp [hj]
  have hmiddle : ‖(𝔼 n, w n * ∑ j, v j n) -
      (𝔼 n, w n * ∑ j, if keep j then v j n else 0)‖ ≤ Fintype.card J * tau := by
    rw [hid]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j : J, tau := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : keep j
        · simpa only [hj, ite_true, norm_zero] using htau
        · simpa only [hj, ite_false] using hdiscard j hj
      _ = _ := by simp
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (𝔼 n, w n * f n) (𝔼 n, w n * ∑ j, v j n) (𝔼 n, w n * projected n)
  have htriangle' := norm_sub_le_norm_sub_add_norm_sub
    (𝔼 n, w n * ∑ j, v j n) (𝔼 n, w n * ∑ j, if keep j then v j n else 0)
    (𝔼 n, w n * projected n)
  linarith

end Erdos3

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

theorem lipschitz_finite_complex_sum {X J : Type*} [PseudoMetricSpace X] [Fintype J]
    (v : J → X → ℂ) (L : J → ℝ≥0) (hv : ∀ j, LipschitzWith (L j) (v j)) :
    LipschitzWith (∑ j, L j) (fun x => ∑ j, v j x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, ‖v j x - v j y‖ := norm_sum_le _ _
    _ ≤ ∑ j, (L j : ℝ) * dist x y := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [dist_eq_norm] using (hv j).dist_le_mul x y
    _ = _ := by simp only [NNReal.coe_sum, Finset.sum_mul]

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NaturalScaleIntegerWindow
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι G : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup G]

noncomputable def centeredIntegerBox (R : ι → ℕ) : Finset (ι → ℤ) :=
  Fintype.piFinset (fun i => Finset.Icc (-(R i : ℤ)) (R i : ℤ))

@[simp] theorem mem_centeredIntegerBox (R : ι → ℕ) (x : ι → ℤ) :
    x ∈ centeredIntegerBox R ↔ ∀ i, |x i| ≤ (R i : ℤ) := by
  simp only [centeredIntegerBox, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

@[simp] theorem card_centeredIntegerBox (R : ι → ℕ) :
    (centeredIntegerBox R).card = ∏ i, (2 * R i + 1) := by
  rw [centeredIntegerBox, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro i _
  rw [Int.card_Icc]
  omega

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integerSites_card_le {K S : Type*} [Fintype K] [Fintype S]
    (site : S → K → ℤ) (hsite : Function.Injective site) (R : ℕ)
    (hbound : ∀ s k, |site s k| ≤ (R : ℤ)) :
    Fintype.card S ≤ (2*R+1)^Fintype.card K := by
  classical
  let f : S → ↥(centeredIntegerBox (fun _ : K => R)) :=
    fun s => ⟨site s, (mem_centeredIntegerBox _ _).mpr (hbound s)⟩
  have hf : Function.Injective f := fun s t h => hsite (congrArg Subtype.val h)
  simpa only [Fintype.card_coe, card_centeredIntegerBox, Finset.prod_const,
    Finset.card_univ] using Fintype.card_le_of_injective f hf

theorem integerSites_card_le_exp {K S : Type*} [Fintype K] [Fintype S]
    (site : S → K → ℤ) (hsite : Function.Injective site) {P : ℝ} (hP : 0 ≤ P)
    (hK : (Fintype.card K : ℝ) ≤ P)
    (hbound : ∀ s k, |(site s k : ℝ)| ≤ Real.exp P) :
    (Fintype.card S : ℝ) ≤ Real.exp (P*(P+5)) := by
  have hcard := integerSites_card_le site hsite ⌈Real.exp P⌉₊ (fun s k => by
    exact_mod_cast (hbound s k).trans (Nat.le_ceil (Real.exp P)))
  have hceil := (Nat.ceil_lt_add_one (Real.exp_pos P).le).le
  have h1 : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have h5 : (5 : ℝ) ≤ Real.exp 5 := by linarith [Real.add_one_le_exp (5 : ℝ)]
  have hbase : (2*⌈Real.exp P⌉₊+1 : ℝ) ≤ Real.exp (P+5) := by
    calc
      _ ≤ 5*Real.exp P := by linarith
      _ ≤ Real.exp P*Real.exp 5 := by nlinarith [Real.exp_pos P]
      _ = _ := (Real.exp_add P 5).symm
  calc
    _ ≤ ((2*⌈Real.exp P⌉₊+1 : ℕ) : ℝ)^Fintype.card K := by exact_mod_cast hcard
    _ ≤ (Real.exp (P+5))^Fintype.card K :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by simpa only [Nat.cast_add,
        Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hbase) _
    _ = Real.exp ((Fintype.card K : ℝ)*(P+5)) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hK (by linarith))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RefinementEnlargement
namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution

noncomputable def refinementContraction (epsilon : ℝ) : ℝ :=
  1 - localMomentGain (flatComparisonDelta epsilon) / 1081600

end Erdos3.CellRefinement

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FixedRefinementBudget
namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped NNReal

noncomputable def refinementScaleLoss (rank : ℕ) (p : ℝ) : ℝ :=
  (rank : ℝ) + p / 8 + 3 * p + 1600

noncomputable def refinementMatchingLoss (rank : ℕ) (p epsilon : ℝ) : ℝ :=
  5 * rank + (25 / 2 : ℝ) * p + localMomentErrorBudget (flatComparisonDelta epsilon) +
    unbalancedErrorBudget (localMomentGain (flatComparisonDelta epsilon)) + 8020

noncomputable def refinementRoundLoss (rank : ℕ) (p H epsilon : ℝ) : ℝ :=
  refinementMatchingLoss rank p epsilon +
    unbalancedReturnWidthLoss rank (localMomentGain (flatComparisonDelta epsilon)) p H (p / 8) (2 * p)

noncomputable def refinementComparisonBudget (rank : ℕ) (p R epsilon : ℝ) : ℝ :=
  max (2 * rank + p + ((1 / 4 : ℝ) + 2) * p +
      (R + refinementMatchingLoss rank p epsilon) + 1612)
    (((1 / 4 : ℝ) + 2) * p + 2 +
      rank * (R + refinementMatchingLoss rank p epsilon + 10))

end Erdos3.CellRefinement

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformCommutingCircleDecomposition
namespace OAI

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

theorem sum_fin_tuple_cons {β : Type*} [Fintype β] (n : ℕ) (f : (Fin (n + 1) → β) → ℂ) :
    ∑ k, f k = ∑ b : β, ∑ k : Fin n → β, f (Fin.cons b k) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => β)).sum_comp f]
  exact Fintype.sum_prod_type _

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ObservedProductDensity
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def productFiberIndicator {I : Type*} {X : I → Type*}
    (S : Finset I) (x y : ∀ i, X i) : ℝ :=
  if ∀ i ∈ S, y i = x i then 1 else 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateProductCap
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def coordinateJoin {D X : Type*} [DecidableEq D] (j : D)
    (tail : {d : D // d ≠ j} → X) (x : X) : D → X :=
  fun d => if h : d = j then x else tail ⟨d,h⟩

@[simp] theorem coordinateJoin_pivot {D X : Type*} [DecidableEq D] (j : D)
    (tail : {d : D // d ≠ j} → X) (x : X) : coordinateJoin j tail x j = x := by
  simp [coordinateJoin]

@[simp] theorem coordinateJoin_other {D X : Type*} [DecidableEq D] (j : D)
    (tail : {d : D // d ≠ j} → X) (x : X) (d : {d : D // d ≠ j}) :
    coordinateJoin j tail x d.val = tail d := by
  simp [coordinateJoin, d.property]

theorem coordinateJoin_eta {D X : Type*} [DecidableEq D] (j : D) (z : D → X) :
    coordinateJoin j (fun d => z d.val) (z j) = z := by
  funext d
  by_cases h : d = j <;> simp [coordinateJoin, h]

theorem coordinateJoin_injective {D X : Type*} [DecidableEq D] (j : D)
    (tail : {d : D // d ≠ j} → X) : Function.Injective (coordinateJoin j tail) := by
  intro x y h
  simpa only [coordinateJoin_pivot] using congrFun h j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueLinearPointCap
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def integerArrayLinearForm {D : Type*} [Fintype D] (c z : D → ℤ) : ℤ := ∑ d, c d * z d

theorem integerArrayLinearForm_affine_join {D : Type*} [Fintype D] [DecidableEq D]
    (c a q : D → ℤ) (j : D) (tail : {d : D // d ≠ j} → ℤ) (x : ℤ) :
    integerArrayLinearForm c (fun d => a d + q d * coordinateJoin j tail x d) =
      c j * (a j + q j * x) + ∑ d : {d : D // d ≠ j}, c d.val * (a d.val + q d.val * tail d) := by
  rw [integerArrayLinearForm, Fintype.sum_eq_add_sum_subtype_ne _ j]
  simp only [coordinateJoin_pivot, coordinateJoin_other]

theorem integerArrayLinearForm_pivot_injective {D : Type*} [Fintype D] [DecidableEq D]
    (c a q : D → ℤ) (j : D) (hc : c j ≠ 0) (hq : q j ≠ 0)
    (tail : {d : D // d ≠ j} → ℤ) :
    Function.Injective (fun x => integerArrayLinearForm c
      (fun d => a d + q d * coordinateJoin j tail x d)) := by
  intro x y h
  simp only [integerArrayLinearForm_affine_join] at h
  exact mul_left_cancel₀ hq (add_left_cancel (mul_left_cancel₀ hc (add_right_cancel h)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuantitativeNoninjectivity
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def noninjectivityIndicator {J Y : Type*} (f : J → Y) : ℝ :=
  if Function.Injective f then 0 else 1

theorem noninjectivityIndicator_nonneg {J Y : Type*} (f : J → Y) :
    0 ≤ noninjectivityIndicator f := by
  unfold noninjectivityIndicator
  split_ifs <;> norm_num

theorem noninjectivityIndicator_le_pairs {J Y : Type*} [Fintype J] [DecidableEq J]
    [DecidableEq Y] (f : J → Y) :
    noninjectivityIndicator f ≤ ∑ j, ∑ k, if j = k then 0 else if f j = f k then (1 : ℝ) else 0 := by
  have hn (j k : J) : 0 ≤ (if j = k then 0 else if f j = f k then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  by_cases hf : Function.Injective f
  · simp only [noninjectivityIndicator, if_pos hf]
    exact Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => hn j k))
  · have hpair : ∃ j k, j ≠ k ∧ f j = f k := by
      by_contra h
      apply hf
      intro j k he
      by_contra hne
      exact h ⟨j,k,hne,he⟩
    obtain ⟨j,k,hjk,he⟩ := hpair
    simp only [noninjectivityIndicator, if_neg hf]
    calc
      (1 : ℝ) = (if j = k then 0 else if f j = f k then 1 else 0) := by simp [hjk,he]
      _ ≤ ∑ l, if j = l then 0 else if f j = f l then (1 : ℝ) else 0 :=
        Finset.single_le_sum (fun l _ => hn j l) (Finset.mem_univ k)
      _ ≤ _ := Finset.single_le_sum
        (fun l _ => Finset.sum_nonneg (fun k _ => hn l k)) (Finset.mem_univ j)

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

def rowDifferenceCoefficients {K I : Type*} [DecidableEq I]
    (r s : K → ℤ) (i : I) (z : Option K × I) : ℤ :=
  if z.2 = i then z.1.elim 0 (fun k => r k - s k) else 0

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueIntervalFactors
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def residueSiteIndicator {m : ℕ} (r : ZMod m) (u : ℤ) : ℝ :=
  if (u : ZMod m) = r then 1 else 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GroupedSiteTensor
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def vectorIntervalSiteWeight {D : Type*} [Fintype D] (b r : ℝ)
    (k : D → Fin (intervalSiteCount b r)) (x : D → ℝ) : ℂ :=
  ∏ d, (intervalSiteWeight b r (k d) (x d) : ℂ)

theorem vectorIntervalSiteWeight_bound {D : Type*} [Fintype D] (b : ℝ)
    {r : ℝ} (hr : 0 < r) (k : D → Fin (intervalSiteCount b r)) (x : D → ℝ) :
    ‖vectorIntervalSiteWeight b r k x‖ ≤ 1 := by
  unfold vectorIntervalSiteWeight
  apply siteFactorTensor_factor_bound (fun d y => (intervalSiteWeight b r (k d) y : ℂ))
  intro d y
  rw [Complex.norm_real, Real.norm_of_nonneg (intervalSiteWeight_range b hr _ _).1]
  exact (intervalSiteWeight_range b hr _ _).2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialSiteShift
namespace OAI

section

namespace Erdos3

open scoped BigOperators

abbrev SpatialSiteLabel (I : Type*) (m : ℕ) (b r : ℝ) :=
  ((Unit ⊕ I) → ZMod m) × ((Unit ⊕ I) → Fin (intervalSiteCount b r))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.VectorSiteBudget
namespace OAI

section

namespace Erdos3

theorem intervalSiteCount_bound {B r : ℝ} (hB : 0 ≤ B) (hr : 0 < r) :
    (intervalSiteCount B r : ℝ) ≤ 2 * B / r + 3 := by
  have h := (Nat.ceil_lt_add_one (show 0 ≤ 2 * B / r by positivity)).le
  simp only [intervalSiteCount, boxCoverMeshCount, NNReal.coe_one, mul_one, Nat.cast_add, Nat.cast_one]
  linarith

theorem intervalSiteCount_le_exp {B r P : ℝ} (hB0 : 0 ≤ B) (hr : 0 < r) (hP : 0 ≤ P)
    (hB : B ≤ Real.exp P) (hri : 1 / r ≤ Real.exp P) :
    (intervalSiteCount B r : ℝ) ≤ Real.exp (2 * P + 4) := by
  have he : 1 ≤ Real.exp (2 * P) := Real.one_le_exp_iff.mpr (by positivity)
  have hb : 2 * B / r ≤ 2 * Real.exp (2 * P) := by
    calc
      _ = 2 * B * (1 / r) := by ring
      _ ≤ 2 * Real.exp P * Real.exp P := by gcongr
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  calc
    _ ≤ 2 * B / r + 3 := intervalSiteCount_bound hB0 hr
    _ ≤ 5 * Real.exp (2 * P) := by linarith
    _ ≤ Real.exp 4 * Real.exp (2 * P) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      linarith [Real.add_one_le_exp (4 : ℝ)]
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem intervalSiteLipschitz_le_exp {B r P : ℝ} (hB0 : 0 ≤ B) (hr : 0 < r) (hP : 0 ≤ P)
    (hB : B ≤ Real.exp P) (hri : 1 / r ≤ Real.exp P) :
    (2 * (intervalSiteCount B r : ℝ) + 1) / r ≤ Real.exp (3 * P + 6) := by
  have hn := intervalSiteCount_le_exp hB0 hr hP hB hri
  have he : 1 ≤ Real.exp (2 * P + 4) := Real.one_le_exp_iff.mpr (by positivity)
  have hnum : 2 * (intervalSiteCount B r : ℝ) + 1 ≤ 3 * Real.exp (2 * P + 4) := by linarith
  calc
    _ = (2 * (intervalSiteCount B r : ℝ) + 1) * (1 / r) := by ring
    _ ≤ (3 * Real.exp (2 * P + 4)) * Real.exp P := by gcongr
    _ = 3 * Real.exp (3 * P + 4) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ Real.exp 2 * Real.exp (3 * P + 4) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      linarith [Real.add_one_le_exp (2 : ℝ)]
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalSpatialScales
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

def physicalCubeOptionEquiv (K : Type*) : (Unit ⊕ K) ≃ Option K where
  toFun := Sum.elim (fun _ => none) some
  invFun := Option.elim' (.inl ()) Sum.inr
  left_inv x := by cases x with | inl x => cases x; rfl | inr x => rfl
  right_inv x := by cases x <;> rfl

def physicalCubePivotIndex {α K : Type*} (s : α ↪ K) : (Unit ⊕ α) ↪ Option K where
  toFun := Sum.elim (fun _ => none) (fun i => some (s i))
  inj' := by
    intro i j h
    cases i with
    | inl i => cases j with
      | inl j => cases i; cases j; rfl
      | inr j => cases h
    | inr i => cases j with
      | inl j => cases h
      | inr j => exact congrArg Sum.inr (s.injective (Option.some.inj h))

theorem physicalCubePivotIndex_inl {α K : Type*} (s : α ↪ K) (i : Unit) :
    physicalCubePivotIndex s (.inl i) = none := rfl

theorem physicalCubePivotIndex_inr {α K : Type*} (s : α ↪ K) (i : α) :
    physicalCubePivotIndex s (.inr i) = some (s i) := rfl

noncomputable def physicalSpatialInputScale (K : Type*) (A R : ℝ) : Option K → ℝ :=
  Option.elim' A (fun _ => R)

noncomputable def physicalSpatialOutputScale (α : Type*) (A R L : ℝ) : (Unit ⊕ α) → ℝ :=
  Sum.elim (fun _ => A) (fun _ => L * R)

theorem physicalSpatialInputScale_pos (K : Type*) {A R : ℝ} (hA : 0 < A) (hR : 0 < R) :
    ∀ k, 0 < physicalSpatialInputScale K A R k := by
  intro k
  cases k
  · exact hA
  · exact hR

theorem physicalSpatialOutputScale_pos (α : Type*) {A R L : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L) :
    ∀ i, 0 < physicalSpatialOutputScale α A R L i := by
  intro i
  cases i
  · exact hA
  · exact mul_pos hL hR

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory
open scoped BigOperators NNReal

noncomputable def physicalSpatialInverseBound (α : Type*) [Fintype α] (κ : ℝ) : ℝ :=
  (Fintype.card (Unit ⊕ α) : ℝ) * (Fintype.card (Unit ⊕ α)).factorial / κ

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

noncomputable def trimmedSpatialRootScale {X : Type*} (τ : ℝ) (N modulus : X → ℕ) (x : X) : ℝ :=
  τ * (N x : ℝ) / 8 / modulus x

noncomputable def trimmedSpatialSlopeScale {X : Type*} (B τ : ℝ) (N modulus : X → ℕ) (x : X) : ℝ :=
  τ * (N x : ℝ) / (8 * (1 + B)) / modulus x

theorem trimmedSpatial_scales_pos {X : Type*} {B τ : ℝ} (hB : 0 ≤ B) (hτ : 0 < τ)
    (N modulus : X → ℕ) (x : X) (hN : 0 < N x) (hq : 0 < modulus x) :
    0 < trimmedSpatialRootScale τ N modulus x ∧ 0 < trimmedSpatialSlopeScale B τ N modulus x := by
  have hn : (0 : ℝ) < N x := by exact_mod_cast hN
  have hq' : (0 : ℝ) < modulus x := by exact_mod_cast hq
  unfold trimmedSpatialRootScale trimmedSpatialSlopeScale
  constructor <;> positivity

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalRowsSiteReconstruction
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

noncomputable def starVertexSiteFactor {α V : Type*} [Fintype α]
    (factor : Unit ⊕ α → V → ℂ) (s : Finset α) (v : V) : ℂ :=
  ∏ i, if spatialStarVertex i = s then factor i v else 1

theorem starVertexSiteFactor_bound {α V : Type*} [Fintype α]
    (factor : Unit ⊕ α → V → ℂ) (hfactor : ∀ i v, ‖factor i v‖ ≤ 1)
    (s : Finset α) (v : V) : ‖starVertexSiteFactor factor s v‖ ≤ 1 := by
  rw [starVertexSiteFactor, norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro i _
  split_ifs
  · exact hfactor i v
  · simp

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedReferenceJetWindow
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

noncomputable def referenceJetEnvelopeWidths {X : Type*} {q : ℕ}
    (stride : X → ℕ) (H : X → ℝ) : Option (Fin q) × X → ℝ :=
  fun z => 20 * (stride z.2 : ℝ) * H z.2

theorem referenceJetEnvelopeWidths_pos {X : Type*} {q : ℕ}
    (stride : X → ℕ) (hs : ∀ x, 0 < stride x) (H : X → ℝ) (hH : ∀ x, 0 < H x)
    (z : Option (Fin q) × X) : 0 < referenceJetEnvelopeWidths stride H z := by
  exact mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr (hs z.2))) (hH z.2)

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSpatialResidueSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def affineResidueIntervalSiteWeight (b r H : ℝ) (q : ℕ)
    (offset : ℤ) {m : ℕ} (a : ZMod m) (k : Fin (intervalSiteCount b r)) (u : ℤ) : ℝ :=
  residueSiteIndicator (m := q * m)
      ((offset + (q : ℤ) * (a.val : ℤ) : ℤ) : ZMod (q * m)) u *
    intervalSiteWeight b r k (((u : ℝ) - offset) / ((q : ℝ) * H))

noncomputable def affineVectorResidueSiteWeight {X : Type*} [Fintype X]
    (b r : ℝ) (H : X → ℝ) (q : X → ℕ) (offset : X → ℤ)
    {m : ℕ} (a : X → ZMod m) (k : X → Fin (intervalSiteCount b r)) (u : X → ℤ) : ℂ :=
  ∏ x, (affineResidueIntervalSiteWeight b r (H x) (q x) (offset x) (a x) (k x) (u x) : ℂ)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem affineVectorResidueSiteWeight_factorization {X : Type*} [Fintype X]
    (b r : ℝ) (H : X → ℝ) (q : X → ℕ) (offset : X → ℤ)
    {m : ℕ} (a : X → ZMod m) (k : X → Fin (intervalSiteCount b r)) (u : X → ℤ) :
    affineVectorResidueSiteWeight b r H q offset a k u =
      (∏ x, (residueSiteIndicator (m := q x * m)
        ((offset x + (q x : ℤ) * ((a x).val : ℤ) : ℤ) : ZMod (q x * m)) (u x) : ℂ)) *
      vectorIntervalSiteWeight b r k (fun x => ((u x : ℝ) - offset x) / ((q x : ℝ) * H x)) := by
  simp only [affineVectorResidueSiteWeight, affineResidueIntervalSiteWeight,
    vectorIntervalSiteWeight, Complex.ofReal_mul, Finset.prod_mul_distrib]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalSupportedCubes
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

def physicalCubeParametersEquiv (X : Type*) (dim : ℕ) :
    (X → (Unit ⊕ Fin dim) → ℤ) ≃ (Fin dim → X → ℤ) × (X → ℤ) where
  toFun v := (fun i x => v x (.inr i), fun x => v x (.inl ()))
  invFun p := fun x => Sum.elim (fun _ => p.2 x) (fun i => p.1 i x)
  left_inv v := by
    funext x i
    cases i with
    | inl i => cases i; rfl
    | inr i => rfl
  right_inv p := rfl

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalCubeNativeDetection
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace BooleanCubeKernel

def vertexFinsetEquiv (j : ℕ) : (Fin j → Bool) ≃ Finset (Fin j) where
  toFun ω := Finset.univ.filter (fun i => ω i)
  invFun s := fun i => decide (i ∈ s)
  left_inv ω := by funext i; simp
  right_inv s := by ext i; simp

end BooleanCubeKernel
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AmbientL1SamplingBudget
namespace OAI

section

namespace Erdos3
open scoped NNReal

noncomputable def ambientL1FourierInput {A : Type*} [Semiring A] (T : A) : A := 2 * T + 1
noncomputable def ambientL1SamplingBudget {A : Type*} [Semiring A] (T : A) : A :=
  let Q := ambientL1FourierInput T
  T + (2 * Q + 1) * (2 * Q + 2) ^ 4 + Q

theorem ambientL1SamplingBudget_bounds {T : ℝ} (hT : 0 ≤ T)
    {Lf Lg Cf Cg Ljet : ℝ≥0} {η : ℝ}
    (hf : (Lf : ℝ) ≤ Real.exp T) (hg : (Lg : ℝ) ≤ Real.exp T)
    (hcf : (Cf : ℝ) ≤ Real.exp T) (hcg : (Cg : ℝ) ≤ Real.exp T)
    (hjet : (Ljet : ℝ) ≤ Real.exp T) (hη : η⁻¹ ≤ Real.exp T) :
    let Q := ambientL1FourierInput T
    let P := ambientL1SamplingBudget T
    0 ≤ Q ∧ T ≤ Q ∧ T ≤ P ∧
      (((Lf + Lg) * Ljet : ℝ≥0) : ℝ) ≤ Real.exp Q ∧ η⁻¹ ≤ Real.exp Q ∧
      Real.exp ((2 * Q + 2) ^ 4) ≤ Real.exp P ∧
      Real.exp (2 * Q * (2 * Q + 2) ^ 4) * (Cf + Cg : ℝ≥0) ≤ Real.exp P := by
  intro Q P
  have hTQ : T ≤ Q := by dsimp [Q, ambientL1FourierInput]; linarith
  have hQ : 0 ≤ Q := hT.trans hTQ
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hsum {a b : ℝ≥0} (ha : (a : ℝ) ≤ Real.exp T) (hb : (b : ℝ) ≤ Real.exp T) :
      ((a + b : ℝ≥0) : ℝ) ≤ Real.exp (T + 1) := by
    rw [NNReal.coe_add, Real.exp_add]
    calc
      _ ≤ 2 * Real.exp T := by linarith
      _ ≤ _ := by nlinarith [Real.exp_pos T]
  have hl : (((Lf + Lg) * Ljet : ℝ≥0) : ℝ) ≤ Real.exp Q := by
    rw [NNReal.coe_mul]
    apply (mul_le_mul (hsum hf hg) hjet (NNReal.coe_nonneg _) (Real.exp_nonneg _)).trans_eq
    rw [← Real.exp_add]
    congr 1
    dsimp [Q, ambientL1FourierInput]
    ring
  have hc : ((Cf + Cg : ℝ≥0) : ℝ) ≤ Real.exp Q :=
    (hsum hcf hcg).trans (Real.exp_le_exp.mpr (by dsimp [Q, ambientL1FourierInput]; linarith))
  have hpow : 0 ≤ (2 * Q + 2) ^ 4 := by positivity
  have hprod : 0 ≤ 2 * Q * (2 * Q + 2) ^ 4 := by positivity
  have hTP : T ≤ P := by
    change T ≤ T + (2 * Q + 1) * (2 * Q + 2) ^ 4 + Q
    nlinarith
  have hfreq : (2 * Q + 2) ^ 4 ≤ P := by
    change (2 * Q + 2) ^ 4 ≤ T + (2 * Q + 1) * (2 * Q + 2) ^ 4 + Q
    nlinarith
  have hcoeff : 2 * Q * (2 * Q + 2) ^ 4 + Q ≤ P := by
    change _ ≤ T + (2 * Q + 1) * (2 * Q + 2) ^ 4 + Q
    nlinarith
  refine ⟨hQ, hTQ, hTP, hl, hη.trans (Real.exp_le_exp.mpr hTQ), Real.exp_le_exp.mpr hfreq, ?_⟩
  calc
    _ ≤ Real.exp (2 * Q * (2 * Q + 2) ^ 4) * Real.exp Q :=
      mul_le_mul_of_nonneg_left hc (Real.exp_nonneg _)
    _ = _ := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hcoeff

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedNormalizedSiteTwist
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.Set
open scoped BigOperators Classical NNReal

def normalizedSiteTwistProduct {X Y : Type*} (f : X → ℂ) (g : Y → ℂ) (v : X × Y) : ℂ :=
  f v.1 * g v.2

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.GeneratorCells
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

abbrev BooleanCutTest (Ω : Type*) [DecidableEq Ω] :=
  Finset Ω

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateTreeTrace
namespace OAI

section

namespace Erdos3

universe u v

inductive CoordinateDecisionTree (ι : Type u) (Value : ι → Type v) : Type (max u v)
  | leaf : CoordinateDecisionTree ι Value
  | split (i : ι) (children : Value i → CoordinateDecisionTree ι Value) : CoordinateDecisionTree ι Value

end Erdos3

end

section

namespace Erdos3.CoordinateDecisionTree

universe u v

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

def trace : CoordinateDecisionTree ι Value → Finset ι → (∀ i, Value i) → (∀ i, Value i) →
    Finset ι × (∀ i, Value i)
  | .leaf, I, x, _ => (I, x)
  | .split i children, I, x, input =>
    trace (children (input i)) (insert i I) (Function.update x i (input i)) input

end Erdos3.CoordinateDecisionTree

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoundedPrimeDepthBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def boundedPrimes (Q : ℕ) : Finset ℕ := (Finset.range (Q + 1)).filter Nat.Prime

abbrev BoundedPrime (Q : ℕ) := {p // p ∈ boundedPrimes Q}

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CanonicalJointFrameGeometry
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open scoped Classical

noncomputable def jointFrameSourceLo {K I : Type*} (width : Option K × I → ℝ) :
    Option K × I → ℤ :=
  fun t => match t.1 with
    | none => 0
    | some _ => -⌈width t⌉

noncomputable def jointFrameSourceHi {K I : Type*} (N : I → ℕ)
    (width : Option K × I → ℝ) : Option K × I → ℤ :=
  fun t => match t.1 with
    | none => N t.2
    | some _ => ⌈width t⌉ + 1

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.L1SamplingSurrogate
namespace OAI

section

namespace Erdos3
open MeasureTheory

theorem l1_sampling_via_uniform_surrogate
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : Y → X) (f ideal g : X → ℂ)
    (hf : Integrable f μ) (hi : Integrable ideal μ) (hg : Integrable g μ)
    (hfs : Integrable (fun y => f (s y)) ν)
    (his : Integrable (fun y => ideal (s y)) ν)
    (hgs : Integrable (fun y => g (s y)) ν)
    {E δ ε : ℝ} (happrox : ∀ x, ‖ideal x - g x‖ ≤ δ)
    (hmass : (∫ x, ‖f x - ideal x‖ ∂μ) ≤ E)
    (hsample : (∫ y, ‖f (s y) - g (s y)‖ ∂ν) ≤
      (∫ x, ‖f x - g x‖ ∂μ) + ε) :
    (∫ y, ‖f (s y) - ideal (s y)‖ ∂ν) ≤ E + 2 * δ + ε := by
  have hhaar : (∫ x, ‖f x - g x‖ ∂μ) ≤ E + δ := by
    calc
      _ ≤ ∫ x, ‖f x - ideal x‖ + δ ∂μ :=
        integral_mono (hf.sub hg).norm ((hf.sub hi).norm.add (integrable_const δ))
          (fun x => (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
            (add_le_add le_rfl (happrox x)))
      _ = (∫ x, ‖f x - ideal x‖ ∂μ) + δ := by
        simpa [Pi.sub_apply] using
          (integral_add (hf.sub hi).norm (integrable_const δ))
      _ ≤ E + δ := add_le_add hmass le_rfl
  calc
    _ ≤ ∫ y, ‖f (s y) - g (s y)‖ + δ ∂ν :=
      integral_mono (hfs.sub his).norm ((hfs.sub hgs).norm.add (integrable_const δ))
        (fun y => (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
          (add_le_add le_rfl (by simpa only [norm_sub_rev] using happrox (s y))))
    _ = (∫ y, ‖f (s y) - g (s y)‖ ∂ν) + δ := by
      simpa [Pi.sub_apply] using
        (integral_add (hfs.sub hgs).norm (integrable_const δ))
    _ ≤ ((E + δ) + ε) + δ :=
      add_le_add (hsample.trans (add_le_add hhaar le_rfl)) le_rfl
    _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PrecenterForecastNativePartners
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

structure CenteredForecastModel (X : Type*) where
  nterms : ℕ
  positive : 0 < nterms
  models : Fin nterms → X → ℂ
  coefficient : Fin nterms → ℝ
  residual : X → ℂ

end Erdos3

end

end OAI
end


