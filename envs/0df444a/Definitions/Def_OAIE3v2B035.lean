-- Prove2me | Definitions.Def_OAIE3v2B035
-- name    : OAIE3v2B035
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:00:09.454216+00:00
-- url     : https://prove2.me/theorems/58d25d72-d593-48ec-a5be-fa707813ffb8
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 36 of 311
-- statement:
--   Definitions bundle 36 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/AdaptiveShellLogBudget.lean`, `Dynamics/AllocatedFixedPathSlicedSourceErrorBudget.lean`, `Dynamics/AmplificationSourceResourceBudget.lean`, `Dynamics/BooleanCanonicalLogBudget.lean`, `Dynamics/CyclicProductBudget.lean`, `Dynamics/NativeTwistedSliceBudget.lean`, `Dynamics/NormalizedTwistUniformAmbientBudget.lean`, `Dynamics/PreparedPerturbativeSeedPowerBudget.lean`, `Dynamics/PreparedRelativeEndpointComparisonBudget.lean`, `Dynamics/ScalarCubeBoundaryLogBudget.lean`, `Estimates/ActiveAveragedProfileComparison.lean`, `Estimates/AllocatedRecoveredPreparedFreeze.lean`, `Estimates/ApproxMomentEnvelope.lean`, `Estimates/BooleanMinorDimension.lean`, `Estimates/BooleanSelectedDerivativeBound.lean`, `Estimates/BoundedInequalityGoodCutoff.lean`, `Estimates/BufferedSiteExpansion.lean`, `Estimates/CanonicalCubeMinorThreshold.lean`, `Estimates/CappedDistanceReconstruction.lean`, `Estimates/CoefficientRowReindex.lean`, `Estimates/CoefficientScaleGap.lean`, `Estimates/ComplexFiniteMeans.lean`, `Estimates/ComplexPositiveMasks.lean`, `Estimates/ConditioningShellError.lean`, `Estimates/CountingDeficitDetection.lean`, `Estimates/DependentPiProduct.lean`, `Estimates/FiniteHypergraphAbstract.lean`, `Estimates/FiniteSectionPermutation.lean`, `Estimates/LayeredCoverSiteExtension.lean`, `Estimates/LocalWeightedSifting.lean`, `Estimates/MixedArrayReference.lean`, `Estimates/NonprincipalDilation.lean`, `Estimates/PositiveShiftProductData.lean`, `Estimates/PreparedFiniteNestedForwardCanonicalFixedCenterSource.lean`, `Estimates/PreparedModularProductivityPrecision.lean`, `Estimates/PreparedRelativeEndpointNumericalBounds.lean`, `Estimates/PreparedRelativeEndpointSourceBounds.lean`, `Estimates/PreparedRelativeFinalPower.lean`, `Estimates/PreparedScalarFiniteScheduleCandidateDetection.lean`, `Estimates/ProductMeanPullback.lean`, `Estimates/ProductPMFMap.lean`, `Estimates/ProductTensorSectionPointwise.lean`, `Estimates/ScalarCubeDomain.lean`, `Estimates/SelectedWindowIndicator.lean`, `Estimates/SiteTwistCommonModulus.lean`, `Estimates/SmoothHalfspaceCutoff.lean`, `Estimates/SmoothSublevelCutoff.lean`, `Estimates/UniformProfileRadiusLog.lean`, `Fourier/FiniteFourierSmoothing.lean`, `Fourier/FourierWeightedCounting.lean`, `Fourier/PrimePowerCharacterScaling.lean`, `Fourier/RectangularGridCharacter.lean`, `Fourier/TorusCellBudget.lean`, `Fourier/UniformSpectrumAbsoluteCap.lean`, `Geometry/AllocatedExternalCandidateSpatialNativeLongCommonFactors.lean`, `Geometry/AllocatedNarrowSpatialCanonicalComparison.lean`, `Geometry/AllocatedRowSlicedIdealCoordinates.lean`, `Geometry/ContinuousOutputBox.lean`, `Geometry/CoordinateInjection.lean`, `Geometry/DivergenceSupport.lean`, `Geometry/FixedSupportRawArray.lean`, `Geometry/ProductEquivTransport.lean`, `Lattices/AbsoluteCRTWindow.lean`, `Lattices/AffineBooleanCubeComparison.lean`, `Lattices/AffineCubeCoordinates.lean`, `Lattices/AffineKernelEndpointGeometry.lean`, `Lattices/AffinePrimitiveLogBudget.lean`, `Lattices/AffineResidueAccuracy.lean`, `Lattices/AffineResidueCoordinateEquiv.lean`, `Lattices/AffineSampleAlphabet.lean`, `Lattices/AllocatedAffineFixedPathRationalReference.lean`, `Lattices/AllocatedModularRankAffineProbability.lean`, `Lattices/BoundedPrimeResidual.lean`, `Lattices/CRTProgressionVanishing.lean`, `Lattices/DenseResidueMeshExponentialBudget.lean`, `Lattices/IntegerAffineResidues.lean`, `Lattices/IntegerBoxCoordinateEquiv.lean`, `Lattices/IntegerFiberUniformBound.lean`, `Lattices/IntegerImageProbabilityLaw.lean`, `Lattices/JointAffineBooleanSource.lean`, `Lattices/LargestBadPrimeProduct.lean`, `Lattices/LatticeHyperplaneBasis.lean`, `Lattices/ResidueRefinedPeriod.lean`, `Lattices/ResidueSliceUpperFailure.lean`, `Lattices/SmoothAffinePairLaw.lean`, `Lattices/SmoothBadPrimeProduct.lean`, `Lattices/UniformBoxResidueMass.lean`, `Linear/AnisotropicGoodKernelComparison.lean`, `Linear/ContainedKernelPhysicalDisplacement.lean`, `Linear/CountingKernelOuter.lean`, `Linear/FiniteKernelRestriction.lean`, `Linear/KernelMixtureControl.lean`, `Linear/ProductANOVASectionNormalizedBound.lean`, `Polynomial/AffineSidePolynomialBudget.lean`, `Polynomial/CRTPolynomialInputStepLaw.lean`, `Polynomial/CandidateFrontFactorPolynomialBudget.lean`, `Polynomial/IntegerPolynomialActiveProfileSupport.lean`, `Polynomial/JointBooleanPolynomialPerturbation.lean`, `Polynomial/PolynomialPerturbationScaleBudget.lean`, `Polynomial/PreparedComparisonGridPolynomialBudget.lean`, `Polynomial/RestrictedDegreeSupports.lean`, `Polynomial/SchmidtShortDualVector.lean`, `Probability/AllocatedJointMaskedDensityComparison.lean`, `Probability/AllocatedMaskedCoefficientHaarLaw.lean`, `Probability/AnisotropicCanonicalDensity.lean`, `Probability/AnisotropicSpatialLaw.lean`, `Probability/BooleanJetMassBudget.lean`, `Probability/CandidateFrontFactorMassBlockBudget.lean`, `Probability/RelativeSourceDensityParameter.lean`, `Sampling/ActualSlicedForecastLateData.lean`, `Sampling/AllocatedForecastShortRawDependence.lean`, `Sampling/ForecastInactiveSlicedCappedContinuousSource.lean`, `Sampling/ForecastLawPhysicalAmbientHaarComparison.lean`, `Sampling/ForecastRawSpatialBoxReorder.lean`, `Sampling/ForecastShortGridEquiv.lean`, `Sampling/PreparedActualForecastSetup.lean`, `Sampling/PreparedActualSlicedForecastSetup.lean`, `Sampling/PreparedCenteredForecastSpatialBounds.lean`, `Sampling/PreparedSlicedForecastComparisonLogs.lean`.
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

noncomputable def orderedProductTail {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∏ j, if i < j then x j else 1

noncomputable def axisProduct {G : Type*} [Add G] {n : ℕ}
    (f : Fin n → G → ℝ) (t : Fin n → G) (y : G) : ℝ := ∏ i, f i (y + t i)

noncomputable def axisSuffix {G : Type*} [Add G] {n : ℕ}
    (f : Fin n → G → ℝ) (t : Fin n → G) (i : Fin n) (y : G) : ℝ :=
  orderedProductTail (fun j => f j (y + t j)) i

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

variable {S T U D : Type*} [Fintype S] [Fintype T]

def bufferedSiteFactor (y : S → U → D → ℝ) (χ : S → U → ℂ)
    (f : T → S → (D → ℝ) → ℂ) (k : T) (s : S) (u : U) : ℂ :=
  χ s u*f k s (y s u)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteSectionPermutation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

noncomputable def finiteWeightedLp (w : X → ℝ) (p : ℝ) (f : X → ℝ) : ℝ :=
  (∑ x, w x * |f x| ^ p) ^ (1 / p)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteHypergraphAbstract
namespace OAI

section

namespace Erdos3

variable {n k : ℕ}

noncomputable def finiteSlotMask (a : Fin k → Fin n) (i : ℕ) : Bool := by
  classical
  exact decide (∃ j, (a j).val = i)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {J X : Type*} [Fintype J] [Fintype X]

def finiteFactorMultiplicity (b : J → Bool) : ℕ :=
  (Finset.univ.filter (fun j => b j = true)).card

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RectangularGridCharacter
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def integerGridResidue {J : Type*} (M : ℕ) (y : J → ℤ) : J → ZMod M := fun j => (y j : ZMod M)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FiniteFourierSmoothing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

noncomputable def additiveCharacterKernel (χ : AddChar G ℂ) : AddSubgroup G where
  carrier := {x | χ x = 1}
  zero_mem' := χ.map_zero_eq_one
  add_mem' := by
    intro x y hx hy
    change χ (x + y) = 1
    rw [AddChar.map_add_eq_mul, hx, hy, one_mul]
  neg_mem' := by
    intro x hx
    change χ (-x) = 1
    rw [AddChar.map_neg_eq_inv, hx, inv_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PrimePowerCharacterScaling
namespace OAI

section

namespace Erdos3

def characterPullback {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) : AddChar H ℂ →* AddChar G ℂ where
  toFun χ := χ.compAddMonoidHom f
  map_one' := rfl
  map_mul' _ _ := rfl

theorem characterPullback_order {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) (hf : Function.Surjective f) (χ : AddChar H ℂ) :
    orderOf (characterPullback f χ) = orderOf χ :=
  orderOf_injective (characterPullback f) (AddChar.compAddMonoidHom_injective_left f hf) χ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
namespace OAI

section

namespace Erdos3

open scoped Matrix

def pivotFullImage {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) : Submodule ℤ (I → ℤ) :=
  A.mulVecLin.range ⊔ B.mulVecLin.range

end Erdos3

end

section

namespace Erdos3

noncomputable def additiveResidueEquiv {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G) : G ≃ (G ⧸ H) × H where
  toFun x := ⟨(x : G ⧸ H), ⟨x - Quotient.out (x : G ⧸ H),
    QuotientAddGroup.eq_iff_sub_mem.mp (Quotient.out_eq' _).symm⟩⟩
  invFun p := p.1.out + p.2.val
  left_inv x := by simp
  right_inv := by
    rintro ⟨r, n⟩
    have h : ((r.out + n.val : G) : G ⧸ H) = r := by
      calc
        _ = (r.out : G ⧸ H) := QuotientAddGroup.eq_iff_sub_mem.mpr (by simp)
        _ = r := Quotient.out_eq' r
    apply Prod.ext
    · exact h
    · apply Subtype.ext
      change r.out + n.val - Quotient.out ((r.out + n.val : G) : G ⧸ H) = n.val
      rw [h]
      simp

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

noncomputable def dependentProductPMF {D : Type*} [Fintype D] {X : D → Type*}
    [∀ d, Countable (X d)] [∀ d, MeasurableSpace (X d)] [∀ d, MeasurableSingletonClass (X d)]
    (p : ∀ d, PMF (X d)) : PMF (∀ d, X d) :=
  (Measure.pi (fun d => (p d).toMeasure)).toPMF

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerAffineResidues
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def realAffineCube {α K : Type*} (root : K → ℝ) (difference : α → K → ℝ)
    (t : Finset α) : K → ℝ := fun k => root k + ∑ r ∈ t, difference r k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelMixtureControl
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def kernelAverage {X T : Type*} [MeasurableSpace T]
    (μ : Measure T) (K : X → T → ℝ) (g : T → ℝ) (x : X) : ℝ := ∫ t, K x t * g t ∂μ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothSublevelCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

noncomputable def sublevelCutoff {E : Type*} (ψ : ℝ → ℝ) (r : ℝ) (d : E → ℝ) (x : E) : ℝ :=
  ψ (d x / r)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerFiberUniformBound
namespace OAI

section

namespace Erdos3

open scoped Matrix NNReal

noncomputable def integerFiberErrorConstant (j d : ℕ) (G U V R : ℝ) (K : ℝ≥0) : ℝ :=
  G * (j.factorial * U ^ j) * (2 * R + 2) ^ d * K * max 1 (U * V)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanMinorDimension
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def productMinorEntryBound (q h : ℕ) (C R : ℝ) : ℝ :=
  C * ((2 : ℝ) ^ h * (((q : ℝ) + 1) * R) ^ (h - 1))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def productMinorPartialBound (q h : ℕ) (C R : ℝ) : ℝ :=
  C * ((2 : ℝ) ^ h * (h * (((q : ℝ) + 1) * R) ^ h))

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

def productMinorDeterminantDerivativeBound (n j q h : ℕ) (C R : ℝ) : ℝ :=
  n * (j.factorial * (j * productMinorPartialBound q h C R *
    (1 + productMinorEntryBound q h C R) ^ j))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothHalfspaceCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

noncomputable def halfspaceCutoff {E : Type*} (r : ℝ) (d : E → ℝ) (x : E) : ℝ :=
  Real.smoothTransition (d x / r - 1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarCubeDomain
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff NNReal

noncomputable def inequalityBoundaryCutoff {I E : Type*} [Fintype I]
    (r : I → ℝ) (d : I → E → ℝ) (x : E) : ℝ :=
  ∏ i, halfspaceCutoff (r i) (d i) x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScalarCubeBoundaryLogBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

def scalarCubeBoundaryLog (q : ℕ) : ℝ := ((q : ℝ)+1)^2+2*q+2
def scalarCubeDerivativeLog (q : ℕ) (P : ℝ) : ℝ := P+3*q+1+scalarCubeBoundaryLog q

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DivergenceSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def coordinateDivergence (Q : ι → (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, fderiv ℝ (Q i) x (Pi.single i 1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateInjection
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def coordinateInjection {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (f : ι → κ) : (ι → ℝ) →L[ℝ] (κ → ℝ) :=
  ∑ i, (ContinuousLinearMap.single ℝ (fun _ : κ => ℝ) (f i)).comp (ContinuousLinearMap.proj i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanSelectedDerivativeBound
namespace OAI

section

namespace Erdos3

noncomputable def productMinorInverseBound (j q h : ℕ) (C R κ : ℝ) : ℝ :=
  j * (j.factorial * (productMinorEntryBound q h C R) ^ (j - 1) / κ)

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

def productMinorDerivativeBound (n j q h : ℕ) (C R : ℝ) : ℝ :=
  n * (j * productMinorPartialBound q h C R)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedInequalityGoodCutoff
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

noncomputable def goodDomainCutoff {ι E : Type*} [Fintype ι]
    (ψ : ℝ → ℝ) (r : ι → ℝ) (d : ι → E → ℝ) (b : E → ℝ) (x : E) : ℝ :=
  b x * ∏ i, sublevelCutoff ψ (r i) (d i) x

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

noncomputable def sublevelCutoffProduct {J E : Type*} [Fintype J]
    (ψ : ℝ → ℝ) (κ : J → ℝ) (d : J → E → ℝ) (x : E) : ℝ :=
  ∏ i, sublevelCutoff ψ (κ i) (d i) x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.JointBooleanPolynomialPerturbation
namespace OAI

section

namespace Erdos3

noncomputable def polynomialC2BoxBudget (N d : ℕ) (C : ℝ) : ℝ :=
  (1 + (N : ℝ) * d) ^ 2 * (d + 1 : ℝ) ^ N * C

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.BooleanJetMassBudget
namespace OAI

section

namespace Erdos3

noncomputable def booleanJetMassBudget (q h : ℕ) (W : ℝ) : ℝ :=
  (2 : ℝ) ^ q * (W * ((q : ℝ) + 1) ^ h)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerImageProbabilityLaw
namespace OAI


namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal BigOperators

noncomputable def normalizedFiberErrorConstant (j d : ℕ) (G U V R H : ℝ) (K : ℝ≥0) : ℝ :=
  2 * integerFiberErrorConstant j d G U V R K +
    2 * (G * (j.factorial * U ^ j) * H * (2 * R) ^ d) * ((2 * R + 2) ^ (j + d) * K)

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothAffinePairLaw
namespace OAI


namespace Erdos3

open scoped BigOperators Matrix Classical

def affinePairMatrix {J : Type*} (t u : J → ℤ) : Matrix (Fin 2) (Option J) ℤ :=
  fun i c => match c with
    | none => 1
    | some j => ![t j, u j] i

def affinePairImage {J : Type*} [Fintype J] (t u : J → ℤ) : Submodule ℤ (Fin 2 → ℤ) :=
  (affinePairMatrix t u).mulVecLin.range

end Erdos3


namespace Erdos3

open scoped Matrix Classical

def affinePairPivot {J : Type*} (t u : J → ℤ) (k : J) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, t k; 1, u k]

def affinePairFree {J : Type*} (t u : J → ℤ) (k : J) :
    Matrix (Fin 2) {j : J // j ≠ k} ℤ := fun i j => ![t j.val, u j.val] i

def affinePairColumnEquiv {J : Type*} [DecidableEq J] (k : J) :
    (Fin 2 ⊕ {j : J // j ≠ k}) ≃ Option J where
  toFun c := match c with
    | Sum.inl i => if i = 0 then none else some k
    | Sum.inr j => some j.val
  invFun c := match c with
    | none => Sum.inl 0
    | some j => if h : j = k then Sum.inl 1 else Sum.inr ⟨j, h⟩
  left_inv c := by
    rcases c with i | j
    · fin_cases i <;> simp
    · simp [j.property]
  right_inv c := by
    cases c with
    | none => rfl
    | some j => by_cases h : j = k <;> simp [h]

theorem affinePairPivot_det {J : Type*} (t u : J → ℤ) (k : J) :
    (affinePairPivot t u k).det = u k - t k := by
  simp [affinePairPivot, Matrix.det_fin_two]

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RestrictedDegreeSupports
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

def degreeTailSupports (J : Finset ι) (r b : ℕ) : Finset (Finset ι) :=
  J.powerset.filter (fun S => r < S.card ∧ S.card ≤ b)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LargestBadPrimeProduct
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

def badPrimeModulusEvent {Ω : Type*} (S : Finset ℕ) (A : ℕ → ℕ) (Qs : ℕ)
    (bad : ℕ → ℕ → Ω → Prop) (d : ℕ) (x : Ω) : Prop :=
  (∀ p ∈ d.primeFactors, p ∈ S ∧ 0 < d.factorization p ∧
    d.factorization p ≤ A p ∧ Qs ≤ p ^ d.factorization p) ∧
  (∀ p ∈ d.primeFactors, bad p (d.factorization p) x)

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

noncomputable def coefficientImageMask {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (P : I → ℝ) (f : (I → ℝ) → ℝ) (v : I → ℤ) : ℝ := by
  classical
  exact if v ∈ A.mulVecLin.range then
    (A.mulVecLin.range.toAddSubgroup.index : ℝ) * f (fun i => (v i : ℝ) / P i) else 0

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ContinuousOutputBox
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

def continuousOutputBox (I : Type*) (R : ℝ≥0) : Set (I → ℝ) :=
  Set.Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ))

noncomputable def continuousOutputBoxMeasure (I : Type*) [Fintype I] (R : ℝ≥0) : Measure (I → ℝ) :=
  volume.restrict (continuousOutputBox I R)

instance continuousOutputBoxMeasure_finite (I : Type*) [Fintype I] (R : ℝ≥0) :
    IsFiniteMeasure (continuousOutputBoxMeasure I R) := by
  apply isFiniteMeasure_restrict.mpr
  rw [continuousOutputBox, Real.volume_Icc_pi]
  exact ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.TorusCellBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def ambientTorusTent {J : Type*} [Fintype J] (q : ℕ) (x : J → UnitAddCircle) : ℝ :=
  max 0 (1 - (q : ℝ) / 4 * ‖x‖)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def centeredTorusTent {J : Type*} [Fintype J] (q : ℕ)
    (c x : J → UnitAddCircle) : ℝ := ambientTorusTent q (x - c)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CRTProgressionVanishing
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def progressionTorusCenter {J : Type*} (k : ℕ) : J × Bool → UnitAddCircle :=
  fun t => if t.2 then ((1 / (4 * (k : ℝ)) : ℝ) : UnitAddCircle) else ((1 / 4 : ℝ) : UnitAddCircle)

noncomputable def progressionTorusCutoff {J : Type*} [Fintype J] (k : ℕ)
    (w : J × Bool → UnitAddCircle) : ℝ :=
  centeredTorusTent (64 * k) (progressionTorusCenter k) w

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformBoxResidueMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

def affinePairLocations {I : Type*} (v : I → Fin 2 → ℤ) : (I → ℤ) × (I → ℤ) :=
  (fun i => v i 0, fun i => v i 1)

def affinePairRowsOfLocations {I : Type*} (xy : (I → ℤ) × (I → ℤ)) : I → Fin 2 → ℤ :=
  fun i => ![xy.1 i, xy.2 i]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineResidueCoordinateEquiv
namespace OAI

section

namespace Erdos3

noncomputable def affineResidueCoordinateEquiv {σ : Type*} (M q : ℕ) (a : σ → ℤ)
    (hcop : M.Coprime q) : (σ → ZMod q) ≃ (σ → ZMod q) :=
  Equiv.piCongrRight fun j =>
    (ZMod.unitOfCoprime M hcop).mulLeft.trans (Equiv.addLeft (a j : ZMod q))

theorem affineResidueCoordinateEquiv_apply {σ : Type*} (M q : ℕ) (a : σ → ℤ)
    (hcop : M.Coprime q) (x : σ → ZMod q) (j : σ) :
    affineResidueCoordinateEquiv M q a hcop x j = (a j : ZMod q) + (M : ZMod q) * x j := rfl

theorem affineResidueCoordinateEquiv_intCast {σ : Type*} (M q : ℕ) (a : σ → ℤ)
    (hcop : M.Coprime q) (z : σ → ℤ) :
    affineResidueCoordinateEquiv M q a hcop (fun j => (z j : ZMod q)) =
      (fun j => ((a j + (M : ℤ) * z j : ℤ) : ZMod q)) := by
  funext j
  simp only [affineResidueCoordinateEquiv_apply, Int.cast_add, Int.cast_mul, Int.cast_natCast]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeHyperplaneBasis
namespace OAI

section

namespace Erdos3

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem lattice_gaussian_summable (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    {t : ℝ} (ht : 0 < t) (x : E) :
    Summable (fun m : Λ => Real.exp (-Real.pi * t * ‖x - (m : E)‖ ^ 2)) := by
  let r : ℝ := -(Module.finrank ℤ Λ : ℝ) - 1
  have hr : r < -(Module.finrank ℤ Λ : ℝ) := by dsimp [r]; linarith
  have hs := ZLattice.summable_norm_sub_rpow Λ r hr x
  have hc : IsClosed (Λ : Set E) := @AddSubgroup.isClosed_of_discrete E _ _ _ _
    Λ.toAddSubgroup (inferInstanceAs (DiscreteTopology Λ))
  have he : Topology.IsClosedEmbedding (fun m : Λ => (m : E) - x) := by
    exact (Homeomorph.subRight x).isClosedEmbedding.comp (Λ.isClosedEmbedding_subtype hc)
  have hn : Tendsto (fun m : Λ => ‖(m : E) - x‖) cofinite atTop :=
    tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding he
  have hd := (rexp_neg_quadratic_isLittleO_rpow_atTop
    (show -Real.pi * t < 0 by nlinarith [Real.pi_pos]) 0 r).isBigO.comp_tendsto hn
  have hsum := summable_of_isBigO hs hd
  simpa only [Function.comp_def, zero_mul, add_zero, norm_sub_rev] using hsum

noncomputable def latticeGaussianMass (Λ : Submodule ℤ E) (t : ℝ) (x : E) : ℝ :=
  ∑' m : Λ, Real.exp (-Real.pi * t * ‖x - (m : E)‖ ^ 2)

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem gaussian_translate_bound (t R : ℝ) (ht : 0 ≤ t) (hR : 0 ≤ R)
    (x m : E) (hx : ‖x‖ ≤ R) :
    Real.exp (-Real.pi * t * ‖x - m‖ ^ 2) ≤
      Real.exp (Real.pi * t * R ^ 2) * Real.exp (-Real.pi * (t / 2) * ‖m‖ ^ 2) := by
  have htriangle : ‖m‖ ≤ ‖x - m‖ + ‖x‖ := by
    calc
      ‖m‖ = ‖(m - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖m - x‖ + ‖x‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev]
  have hsquare : ‖m‖ ^ 2 ≤ 2 * ‖x - m‖ ^ 2 + 2 * R ^ 2 := by
    have hx0 := norm_nonneg x
    have hm0 := norm_nonneg m
    have hxm0 := norm_nonneg (x - m)
    nlinarith [sq_nonneg (‖x - m‖ - ‖x‖)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le ht)
    (sub_nonneg.mpr hsquare)]

variable [FiniteDimensional ℝ E]

theorem continuousOn_latticeGaussianMass (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    {t : ℝ} (ht : 0 < t) (R : ℝ) (hR : 0 ≤ R) :
    ContinuousOn (latticeGaussianMass Λ t) (Metric.closedBall 0 R) := by
  have hs := (lattice_gaussian_summable Λ (half_pos ht) 0).mul_left
    (Real.exp (Real.pi * t * R ^ 2))
  apply continuousOn_tsum (fun _ => (by fun_prop : Continuous _).continuousOn) hs
  intro m x hx
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), zero_sub, norm_neg]
  exact gaussian_translate_bound t R ht.le hR x m (by simpa using hx)

theorem continuous_latticeGaussianMass (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    {t : ℝ} (ht : 0 < t) : Continuous (latticeGaussianMass Λ t) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (continuousOn_latticeGaussianMass Λ ht (‖x‖ + 1) (by positivity)).continuousAt
    (Metric.closedBall_mem_nhds_of_mem (by simp))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FixedSupportRawArray
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def fixedNonprincipalExponents {K J : Type*} [Fintype J]
    (S : Finset (K →₀ ℕ)) (principal : J → K →₀ ℕ) : Finset (K →₀ ℕ) := by
  classical
  exact S \ insert 0 (Finset.univ.image principal)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientScaleGap
namespace OAI

section

namespace Erdos3

theorem exists_unoccupied_coefficient_gap {I : Type*} [Fintype I]
    (x : I → ℝ) (b : I → ℕ → ℝ) (hb : ∀ i, Monotone (b i)) :
    ∃ j : Fin (Fintype.card I + 1), ∀ i, ¬(b i j.val < x i ∧ x i < b i (j.val + 1)) := by
  classical
  by_contra h
  push Not at h
  choose f hf using h
  have hinj : Function.Injective f := by
    intro a c hac
    apply Fin.ext
    rcases lt_trichotomy a.val c.val with hlt | heq | hgt
    · have hstep := hb (f a) (show a.val + 1 ≤ c.val by omega)
      have hc := (hf c).1
      rw [← hac] at hc
      linarith [(hf a).2]
    · exact heq
    · have hstep := hb (f c) (show c.val + 1 ≤ a.val by omega)
      have ha := (hf a).1
      rw [hac] at ha
      linarith [(hf c).2]
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hcard
  omega

theorem exists_integer_coefficient_scale_gap {I : Type*} [Fintype I]
    (K : I → ℝ) (h : I → ℕ) (L₀ A : ℕ) (hL₀ : 0 < L₀) (hA : 1 ≤ A) :
    ∃ L : ℕ, 0 < L ∧ L₀ ≤ L ∧ L ≤ L₀ * A ^ Fintype.card I ∧
      ∀ i, (L : ℝ) ^ h i < K i → ((A : ℝ) * L) ^ h i ≤ K i := by
  let b : I → ℕ → ℝ := fun i j => ((L₀ * A ^ j : ℕ) : ℝ) ^ h i
  have hb : ∀ i, Monotone (b i) := by
    intro i j k hjk
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    exact_mod_cast Nat.mul_le_mul_left L₀ (Nat.pow_le_pow_right (by omega : 0 < A) hjk)
  obtain ⟨j, hj⟩ := exists_unoccupied_coefficient_gap K b hb
  refine ⟨L₀ * A ^ j.val, Nat.mul_pos hL₀ (pow_pos (by omega) _), ?_, ?_, ?_⟩
  · have hp : 1 ≤ A ^ j.val := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
    nlinarith
  · exact Nat.mul_le_mul_left L₀ (Nat.pow_le_pow_right (by omega) (by omega : j.val ≤ Fintype.card I))
  · intro i hi
    have hbound : b i (j.val + 1) ≤ K i := le_of_not_gt (fun hlt => hj i ⟨hi, hlt⟩)
    have he : ((L₀ * A ^ (j.val + 1) : ℕ) : ℝ) = (A : ℝ) * (L₀ * A ^ j.val : ℕ) := by
      push_cast
      rw [pow_succ]
      ring
    simpa only [b, he] using hbound

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialActiveProfileSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def monomialExponentSet {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) : Finset (K →₀ ℕ) := by
  classical
  exact Finset.univ.image e

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedArrayReference
namespace OAI

section

namespace Erdos3

open MeasureTheory Module
open scoped BigOperators ENNReal

noncomputable def mixedArrayReference (I Z O : Type*) [Fintype I] [Fintype O] :
    Measure ((I → O → ℝ) × (Z → O → ℤ)) :=
  (volume : Measure (I → O → ℝ)).prod (Measure.count : Measure (Z → O → ℤ))

instance mixedArrayReference_sigmaFinite (I Z O : Type*) [Fintype I] [Fintype Z] [Fintype O] :
    SigmaFinite (mixedArrayReference I Z O) := by
  unfold mixedArrayReference
  infer_instance

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCubeCoordinates
namespace OAI

section

namespace Erdos3

def affineCubeCoordinates {I : Type*} (u : Option I → ℝ) (v : Option I → ℕ)
    (x : Option I → ℝ) : Option I → ℝ := fun i => u i + (v i : ℝ) * x i

def affineIntegerCubeCoordinates {I : Type*} (u : Option I → ℤ) (v : Option I → ℕ)
    (x : Option I → ℤ) : Option I → ℤ := fun i => u i + (v i : ℤ) * x i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformSpectrumAbsoluteCap
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def gridJetFrequency {I : Type*} [DecidableEq I]
    (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) (S : Finset I) : ℝ :=
  if h : S ∈ J then ((k ⟨S, h⟩).val : ℝ) / M else 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductMeanPullback
namespace OAI

section

namespace Erdos3

variable {I : Type*} [DecidableEq I] {X : I → Type*}

def productSubtypePoint (S : Finset I) (z : ∀ i : S, X i) (base : ∀ i, X i) : ∀ i, X i :=
  fun i => if h : i ∈ S then z ⟨i, h⟩ else base i

theorem productSubtypePoint_apply_mem (S : Finset I) (z : ∀ i : S, X i)
    (base : ∀ i, X i) (i : S) : productSubtypePoint S z base i = z i := by
  simp only [productSubtypePoint, dif_pos i.property]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteKernelRestriction
namespace OAI

section

namespace Erdos3

open MeasureTheory Topology
open scoped BigOperators

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]
variable (C : G →+ H) [Fintype C.ker]

noncomputable def finiteFiberAverage (f : G → ℝ) (x : G) : ℝ :=
  (Fintype.card C.ker : ℝ)⁻¹ * ∑ k : C.ker, f (x + k.val)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalCubeMinorThreshold
namespace OAI

section

namespace Erdos3

noncomputable def cubeMinorProbabilityScale (O : Type*) [Fintype O] (N d : ℕ) (c₀ : ℝ) : ℝ :=
  (d + 1 : ℝ) ^ N / c₀ ^ Fintype.card O

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.BooleanCanonicalLogBudget
namespace OAI

section

namespace Erdos3

def productMinorPartialLog (q h : ℕ) (P : ℝ) : ℝ := P+2*h+(h : ℝ)*q
def productMinorDerivativeLog (n j q h : ℕ) (P : ℝ) : ℝ :=
  n+j+productMinorPartialLog q h P

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPerturbationScaleBudget
namespace OAI

section

namespace Erdos3

noncomputable def polynomialPerturbationScale (K M Q τ : ℝ) (m : ℕ) : ℝ :=
  min 1 (min (1 / (2 * (1 + K) * (1 + M)))
    (τ ^ 2 / (16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M))))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBoxCoordinateEquiv
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X Y : Type*}

def coordinateReindexedFunction (e : X ≃ Y) (f : (X → ℤ) → ℝ) : (Y → ℤ) → ℝ :=
  fun y => f (fun x => y (e x))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CappedDistanceReconstruction
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def cappedDistanceTest {X : Type*} [PseudoMetricSpace X] (a x : X) : ℂ :=
  (min 1 (dist a x) : ℝ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveShiftProductData
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

noncomputable def anchoredOptionInputs {J : Type*} (j : J) : Finset (Option (Option J ⊕ J)) := by
  classical
  exact {none, some (.inl none), some (.inl (some j)), some (.inr j)}

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffinePrimitiveLogBudget
namespace OAI

section

namespace Erdos3

noncomputable def affineComparisonMoment (P : ℝ) : ℕ :=
  2 * (Nat.floor (P / 2) + 1)

end Erdos3

end

section

namespace Erdos3

noncomputable def affinePrimitiveLogBudget (P : ℝ) : ℝ := 16 * (P + 3)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProductEquivTransport
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

omit [DecidableEq ι] [∀ i, Fintype (Y i)] in
theorem productCoordinate_indicator (x y : ∀ i, Y i) :
    (if x = y then (1 : ℝ) else 0) = ∏ i, if x i = y i then (1 : ℝ) else 0 := by
  classical
  by_cases h : x = y
  · subst y
    simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hn
      push Not at hn
      exact h (funext hn)
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ConditioningShellError
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def conditioningCoreSupports (I : Finset ι) (b : ℕ) : Finset (Finset ι) :=
  Iᶜ.powerset.filter (fun B => B.card ≤ b - I.card)

def conditioningShellSupports (I A : Finset ι) (b : ℕ) : Finset (Finset ι) :=
  Iᶜ.powerset.filter (fun B => b - I.card < B.card ∧ A.card + B.card ≤ b)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineSampleAlphabet
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {q : ℕ} [NeZero q] {J G : Type*} [Fintype J]
  [AddCommGroup G] [Module (ZMod q) G]

noncomputable def residueColumnMap (V : J → G) : (J → ZMod q) →+ G where
  toFun t := ∑ j, t j • V j
  map_zero' := by simp
  map_add' t u := by simp [add_smul, Finset.sum_add_distrib]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {q : ℕ} [NeZero q] {J G : Type*} [Fintype J]
  [AddCommGroup G] [Module (ZMod q) G]

noncomputable def residueColumnRealAverage (V : J → G) (f : G → ℝ) (x : G) : ℝ :=
  𝔼 t : J → ZMod q, f (x + residueColumnMap (q := q) V t)

variable [Fintype G]

theorem residueColumnRealAverage_mean (V : J → G) (f : G → ℝ) :
    (𝔼 x : G, residueColumnRealAverage (q := q) V f x) = 𝔼 x : G, f x := by
  unfold residueColumnRealAverage
  rw [Finset.expect_comm]
  have hshift (t : J → ZMod q) : (𝔼 x : G, f (x + residueColumnMap (q := q) V t)) = 𝔼 x : G, f x :=
    Fintype.expect_equiv (Equiv.addRight (residueColumnMap (q := q) V t)) _ _ (fun _ => rfl)
  simp only [hshift, Fintype.expect_const]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ApproxMomentEnvelope
namespace OAI

section

namespace Erdos3

def approxMomentEnvelope (N r : ℕ) (M : ℝ) : ℝ :=
  (2 : ℝ) ^ (r + 1) * (2 + (N : ℝ)) ^ r * (2 + M)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductANOVASectionNormalizedBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*}
  [Fintype I]
  [LinearOrder I]
  {X : I → Type*}
  [∀ i, Fintype (X i)]

def disjointCoordinateLevel (T : Finset I) (d : ℕ) : Finset (Finset I) :=
  (Finset.univ.powersetCard d).filter (fun U => Disjoint T U)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductTensorSectionPointwise
namespace OAI

section

namespace Erdos3

variable {I : Type*} [DecidableEq I] {X : I → Type*}

def finiteFixedTagSet (n : ℕ) (s : Fin n → Bool) (z : Fin n → Sigma X) : Finset I :=
  Finset.univ.image (fun i : {i : Fin n // s i = true} => (z i).1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceUpperFailure
namespace OAI

section

namespace Erdos3

noncomputable def affineStabilityTolerance (T : ℝ) : ℝ := Real.exp (-(T + 4))

noncomputable def affineIncrementTolerance (L T : ℝ) : ℝ := Real.exp (-(L + T + 4))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoundedPrimeResidual
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι σ : Type*} (q : ι → ℕ) (I : Finset ι)
  (hpair : Pairwise (fun i j => (q i).Coprime (q j)))

noncomputable def selectedPrimeCRT :
    ZMod (∏ i : I, q i.val) ≃+* (∀ i : I, ZMod (q i.val)) :=
  ZMod.prodEquivPi (fun i : I => q i.val)
    (fun i j hij => hpair (by intro h; exact hij (Subtype.ext h)))

noncomputable def primeCoordinatesMod (m : ℕ) (hd : m ∣ ∏ i : I, q i.val) :
    (∀ i, σ → ZMod (q i)) →+ (σ → ZMod m) where
  toFun x k := (ZMod.castHom hd (ZMod m))
    ((selectedPrimeCRT q I hpair).symm (fun i : I => x i.val k))
  map_zero' := by
    ext k
    change (ZMod.castHom hd (ZMod m)) ((selectedPrimeCRT q I hpair).symm 0) = 0
    rw [map_zero, map_zero]
  map_add' := by
    intro x y
    ext k
    change (ZMod.castHom hd (ZMod m)) ((selectedPrimeCRT q I hpair).symm
      ((fun i : I => x i.val k) + (fun i : I => y i.val k))) = _
    rw [map_add, map_add]
    rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def coarseResidueIndicator {ι σ : Type*}
    (q : ι → ℕ) (I : Finset ι) (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (m : ℕ) (hd : m ∣ ∏ i : I, q i.val) (r : σ → ZMod m) (x : ∀ i, σ → ZMod (q i)) : ℝ :=
  if primeCoordinatesMod q I hpair m hd x = r then 1 else 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineResidueAccuracy
namespace OAI

section

namespace Erdos3

noncomputable def affineComparisonAccuracyLog (b : ℕ) (P L T : ℝ) : ℝ :=
  (P + 3) ^ 3 + 2 * (b : ℝ) * (P + 2) + L + T + 4

noncomputable def affineComparisonAccuracy (b : ℕ) (P L T : ℝ) : ℝ :=
  Real.exp (-affineComparisonAccuracyLog b P L T)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AdaptiveShellLogBudget
namespace OAI

section

namespace Erdos3

noncomputable def affineCountLogBudget (P : ℝ) : ℝ :=
  P * (affinePrimitiveLogBudget P + 2 * P ^ 2 + 1)

noncomputable def affineShellLogBudget (P : ℝ) : ℝ := P + affineCountLogBudget P

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineKernelEndpointGeometry
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J I : Type*} [Fintype J] [Fintype I]

def affineCubeTuple (lower width : J → ℝ) (x : J → Option I → ℝ) : J → Option I → ℝ :=
  fun j i => (if i = none then lower j else 0) + width j * x j i

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal Classical
variable {G : Type*} [Fintype G]

noncomputable def affineKernelContinuousPoint (lower : G → ℝ) (step S : ℝ) (H : G → ℕ)
    (x : G → Option Empty → ℝ) : G → ℝ :=
  fun g => (lower g + step * ((H g - 1 : ℕ) : ℝ) * x g none) / S

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NonprincipalDilation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def nonprincipalCoefficientSlots {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) : Finset C := by
  classical
  exact Finset.univ.filter (fun j => e j ∈ fixedNonprincipalExponents (monomialExponentSet e) principal)

end Erdos3

end

section

namespace Erdos3

noncomputable def nonprincipalDilation {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (t : ℝ) (j : C) : ℝ := by
  classical
  exact if j ∈ nonprincipalCoefficientSlots e principal then t else 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularProductivityPrecision
namespace OAI

section

namespace Erdos3

theorem productivity_exp_eight : (256 : ℝ) ≤ Real.exp 8 := by
  have h : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h 8
  norm_num [← Real.exp_nat_mul] at hp ⊢
  exact hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ActiveAveragedProfileComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {S R T U : Type*} [Fintype S] [Fintype R] [Fintype T]

noncomputable def maskedSiteFactor (label : S → U → R) (r : S → R)
    (f : T → S → U → ℂ) (k : T) (s : S) (u : U) : ℂ :=
  if label s u = r s then f k s u else 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LayeredCoverSiteExtension
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable (q : ℕ) [NeZero q]

noncomputable def circleQuarterCover (a : ZMod q) (x : ℝ) : UnitAddCircle :=
  ZMod.toAddCircle a + ((x / q : ℝ) : UnitAddCircle)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DependentPiProduct
namespace OAI

section

namespace Erdos3

open MeasureTheory MeasureTheory.Measure MeasurableSpace

def dependentPiProd (I : Type*) (X Y : I → Type*)
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)] :
    (∀ i, X i × Y i) ≃ᵐ ((∀ i, X i) × (∀ i, Y i)) where
  toFun x := (fun i => (x i).1, fun i => (x i).2)
  invFun x i := (x.1 i, x.2 i)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := (measurable_pi_iff.mpr (fun index =>
    measurable_fst.comp (measurable_pi_apply index))).prodMk
      (measurable_pi_iff.mpr (fun index => measurable_snd.comp (measurable_pi_apply index)))
  measurable_invFun := measurable_pi_iff.mpr (fun index =>
    ((measurable_pi_apply index).comp measurable_fst).prodMk
      ((measurable_pi_apply index).comp measurable_snd))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AnisotropicSpatialLaw
namespace OAI

section

namespace Erdos3

noncomputable def anisotropicSpatialScale (I : Type*) (A R : ℝ) : Unit ⊕ I → ℝ :=
  Sum.elim (fun _ => A) (fun _ => R)

theorem anisotropicSpatialScale_pos (I : Type*) {A R : ℝ} (hA : 0 < A) (hR : 0 < R) :
    ∀ i, 0 < anisotropicSpatialScale I A R i := by
  rintro (i | i)
  · exact hA
  · exact hR

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AnisotropicGoodKernelComparison
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

noncomputable def anisotropicSpatialDetAllowance (I : Type*) [Fintype I] (C : ℝ) : ℝ :=
  (Fintype.card (Unit ⊕ I)).factorial * C ^ Fintype.card (Unit ⊕ I)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AnisotropicCanonicalDensity
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def coordinateRescaledDensity {I : Type*} (a : I → ℝ)
    (f : (I → ℝ) → ℝ) (x : I → ℝ) : ℝ := f (fun i => a i * x i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SiteTwistCommonModulus
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {A D S : Type*} [Fintype A] [Fintype D]

def scaledSiteCoordinates (selected : A → D) (scale : A → ℝ) (x : D → ℝ) : A → ℝ :=
  fun a => scale a * x (selected a)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedWindowIndicator
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {A : Type*} [Fintype A] {X : A → Type*}
variable (selected : A → Prop) [DecidablePred selected]

noncomputable def selectedProductExtension (p : ∀ a, X a → ℝ)
    (g : (∀ a : {a // selected a}, X a.val) → ℂ) (N : ℝ) (z : ∀ a, X a) : ℂ :=
  g (fun a => z a.val) / (N : ℂ) * ((∏ a : {a // ¬selected a}, p a.val (z a.val) : ℝ) : ℂ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformProfileRadiusLog
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {D : Type*} [Fintype D] {B : D → Type*} [∀ d, Fintype (B d)]

noncomputable def unitProfileCoefficientLog (A T : ℝ≥0) : ℝ :=
  (∑ d, (Fintype.card (B d) : ℝ)) + A + T + 7

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedPerturbativeSeedPowerBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def fixedPathPerturbationLog (D P E : ℝ) (m : ℕ) : ℝ :=
  let Q := D + P + E + m + 2
  48 * ((3 * Q + 4) * m + 5 * Q + 10) + 2 * Q + 2 * m + 47

theorem fixedPathPerturbationLog_nonneg {D P E : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (m : ℕ) :
    0 ≤ fixedPathPerturbationLog D P E m := by
  unfold fixedPathPerturbationLog
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedSourceErrorBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal Classical

noncomputable def fixedPathSlicedPerturbationLog (D P Pslice E : ℝ) (m : ℕ) : ℝ :=
  fixedPathPerturbationLog D (P + Pslice) E m

theorem fixedPathSlicedPerturbationLog_nonneg {D P Pslice E : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hPslice : 0 ≤ Pslice) (hE : 0 ≤ E) (m : ℕ) :
    0 ≤ fixedPathSlicedPerturbationLog D P Pslice E m :=
  fixedPathPerturbationLog_nonneg hD (add_nonneg hP hPslice) hE m

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AmplificationSourceResourceBudget
namespace OAI

section

namespace Erdos3

noncomputable def amplificationSourceLogCoefficient (D E : ℕ) : ℝ :=
  (E : ℝ) * ((D : ℝ) + 3)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CyclicProductBudget
namespace OAI

section

namespace Erdos3

def cyclicProductVolumeBudget (p : ℝ) : ℝ := p ^ 2 + 3 * p + 16

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexPositiveMasks
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

def complexMaskComponent (b : Bool) (z : ℂ) : ℝ := if b then z.re else z.im

def complexMaskSign (b : Bool) : ℝ := if b then 1 else -1

noncomputable def complexPositiveMask (t : Bool × Bool) (z : ℂ) : ℝ :=
  (1 + complexMaskSign t.2 * complexMaskComponent t.1 z) / 2

def complexMaskCoefficient (t : Bool × Bool) : ℂ :=
  (complexMaskSign t.2 : ℂ) * (if t.1 then 1 else Complex.I)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CountingKernelOuter
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def countingFeature (b t : ℝ) (sigma : Bool) (u : ℝ) : ℝ :=
  1 + (b + if sigma then t else -t) * (u - 1)

noncomputable def countingKernel (b u v : ℝ) : ℝ :=
  1 + b * (u + v - 2) + (2 * b ^ 2 - b) * (u - 1) * (v - 1)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def countingFeatureProduct {I X : Type*} [Fintype I] [DecidableEq I]
    (b t : ℝ) (f : I → X → ℝ) (sigma : I → Bool) (x : X) : ℝ :=
  ∏ i, countingFeature b t (sigma i) (f i x)

noncomputable def countingKernelProductAverage {I X Y : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y] (b : ℝ) (f : I → X → ℝ) (g : I → Y → ℝ) : ℝ :=
  𝔼 x, 𝔼 y, ∏ i, countingKernel b (f i x) (g i y)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CountingDeficitDetection
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def countingKernelAverage {X : Type*} [Fintype X]
    (b : ℝ) (w f g : X → ℝ) : ℝ := 𝔼 x, w x * countingKernel b (f x) (g x)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalWeightedSifting
namespace OAI

section

namespace Erdos3.WeightedSifting

open scoped BigOperators

variable {Ω ι κ : Type*}

noncomputable def sampleWeight (P : Ω → ι → ℝ) {q : ℕ} (t : Fin q → Ω) (a : ι) : ℝ :=
  ∏ i, P (t i) a

end Erdos3.WeightedSifting

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FourierWeightedCounting
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def configurationFourierWeight {R J : Type*} [AddMonoid R] [Fintype J]
    (c : J → ℂ) (Psi : J → AddChar (R × R) ℂ) (z : R × R) : ℂ :=
  ∑ j, c j * Psi j z

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AbsoluteCRTWindow
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem distinct_prime_moduli_coprime {J : Type*} (N : J → ℕ)
    (hprime : ∀ j, (N j).Prime) (hinj : Function.Injective N) :
    Pairwise (fun i j => Nat.Coprime (N i) (N j)) := by
  intro i j hij
  exact (Nat.coprime_primes (hprime i) (hprime j)).mpr (fun h => hij (hinj h))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NativeTwistedSliceBudget
namespace OAI

section

namespace Erdos3

theorem nativeTwistedSlice_freezing_error {p L mass : ℝ}
    (hp : 0 ≤ p) (_hL : 0 ≤ L) (hLp : L ≤ Real.exp p)
    (hmass : 0 ≤ mass) (hmass1 : mass ≤ 1) :
    Real.exp p * (2 * L * (Real.exp (-(2 * (2 * p + 2))) / 4) * mass) ≤
      Real.exp (-p) / 4 := by
  have h2 : (2 : ℝ) ≤ Real.exp 4 := by
    have := Real.add_one_le_exp 4
    linarith
  have hsmall : 2 * Real.exp (-4) ≤ 1 := by
    rw [Real.exp_neg]
    exact (mul_inv_le_iff₀ (Real.exp_pos 4)).mpr (by simpa using h2)
  calc
    _ ≤ Real.exp p * (2 * Real.exp p * (Real.exp (-(2 * (2 * p + 2))) / 4) * 1) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLp (by norm_num)) (by positivity)
      · exact hmass1
      · exact hmass
      · positivity
    _ = 2 * Real.exp (-4) * Real.exp (-2 * p) / 4 := by
      rw [mul_one]
      have he : Real.exp p * Real.exp p * Real.exp (-(2 * (2 * p + 2))) =
          Real.exp (-4) * Real.exp (-2 * p) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        _ = 2 * (Real.exp p * Real.exp p * Real.exp (-(2 * (2 * p + 2)))) / 4 := by ring
        _ = _ := by rw [he]; ring
    _ ≤ Real.exp (-p) / 4 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      calc
        _ ≤ 1 * Real.exp (-2 * p) := mul_le_mul_of_nonneg_right hsmall (Real.exp_nonneg _)
        _ ≤ Real.exp (-p) := by rw [one_mul]; exact Real.exp_le_exp.mpr (by linarith)

theorem nativeTwistedSlice_bias_precision (p : ℝ) :
    Real.exp (-(p + 2)) ≤ Real.exp (-p) / 4 := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; norm_num at this ⊢; exact this
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 2
    norm_num only [pow_two, mul_comm, ← Real.exp_add] at h
    exact h
  rw [show -(p + 2) = -p - 2 by ring, Real.exp_sub]
  exact div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num) hfour

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NormalizedTwistUniformAmbientBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

noncomputable def normalizedTwistAmbientRankInput {R : Type*} [Semiring R] (z : R) : R :=
  let Q := 2 * z + 4
  2 * Q * (2 * Q + 2) ^ 4 + (2 * Q + 2) ^ 4 + 4 * Q + 16

theorem normalizedTwistAmbient_error_budget {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    {L : ℝ≥0} (hL : (L : ℝ) ≤ Real.exp P) :
    let Q := 2 * max P E + 4
    let p := normalizedTwistAmbientRankInput (max P E)
    2 * Real.exp (-Q) + Real.exp (2 * Q * (2 * Q + 2) ^ 4 - p) +
      (L : ℝ) * Real.exp (-2 * Q) / 2 ≤ Real.exp (-E) := by
  dsimp only
  let Q := 2 * max P E + 4
  let p := normalizedTwistAmbientRankInput (max P E)
  have hz : 0 ≤ max P E := hP.trans (le_max_left _ _)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hPQ : P ≤ Q := by dsimp [Q]; linarith [le_max_left P E]
  have hEQ : E + 4 ≤ Q := by dsimp [Q]; linarith only [le_max_right P E, hE]
  have hp : 2 * Q * (2 * Q + 2) ^ 4 + Q ≤ p := by
    dsimp [p, normalizedTwistAmbientRankInput, Q]
    nlinarith [pow_nonneg (show 0 ≤ 2 * (2 * max P E + 4) + 2 by positivity) 4]
  have ht : Real.exp (2 * Q * (2 * Q + 2) ^ 4 - p) ≤ Real.exp (-Q) :=
    Real.exp_le_exp.mpr (by linarith)
  have hl : (L : ℝ) * Real.exp (-2 * Q) ≤ Real.exp (-Q) := by
    calc
      _ ≤ Real.exp Q * Real.exp (-2 * Q) :=
        mul_le_mul_of_nonneg_right (hL.trans (Real.exp_le_exp.mpr hPQ)) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have he : 4 * Real.exp (-Q) ≤ Real.exp (-E) := by
    calc
      _ ≤ Real.exp 4 * Real.exp (-Q) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
      _ = Real.exp (4 - Q) := by rw [← Real.exp_add]; rfl
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  change 2 * Real.exp (-Q) + Real.exp (2 * Q * (2 * Q + 2) ^ 4 - p) +
    (L : ℝ) * Real.exp (-2 * Q) / 2 ≤ _
  linarith [Real.exp_pos (-Q)]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedRelativeEndpointComparisonBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

def preparedRelativeEndpointTestLog (localBudget earlyNative : ℝ) : ℝ :=
  max localBudget (3 * earlyNative + 3)

def preparedRelativeEndpointComparisonLog
    (localBudget earlyNative earlyMass u p cost : ℝ) : ℝ :=
  max (preparedRelativeEndpointTestLog localBudget earlyNative)
    (2 * u + 4 * p + max 0 earlyMass + 20) + 2 + cost + cost + 8

def preparedRelativeEndpointSourceLog (D primitiveCap Ptest : ℝ) : ℝ :=
  2 + D ^ 2 + primitiveCap + max 0 Ptest

def preparedRelativeEndpointCoarseLog (D primitiveCap Ptest Ecompare : ℝ) : ℝ :=
  2 * preparedRelativeEndpointSourceLog D primitiveCap Ptest + Ecompare + 18

noncomputable def preparedRelativeEndpointSigmaLog
    (D primitiveCap Ptest Ecompare cost : ℝ) (m : ℕ) : ℝ :=
  fixedPathSlicedPerturbationLog D
    (D + preparedRelativeEndpointSourceLog D primitiveCap Ptest + 4) (cost + 1)
    (preparedRelativeEndpointCoarseLog D primitiveCap Ptest Ecompare) m

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedRowSlicedIdealCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def realRowsSiteValue (rows : Finset (Finset α))
    (v : rows → ℝ) (s : Finset α) : ℝ :=
  ∑ t : rows, v t * (if t.val ⊆ s then 1 else 0)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedNarrowSpatialCanonicalComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

def canonicalZeroSpatialNarrowInput {G N X : Type*} (ξ : ℝ)
    (u : Option (G ⊕ N) × X → ℝ) : Option (G ⊕ N) × X → ℝ :=
  fun a => match a.1 with
    | some (.inr _) => ξ * u a
    | _ => u a

@[simp] theorem canonicalZeroSpatialNarrowInput_none {G N X : Type*} (ξ : ℝ)
    (u : Option (G ⊕ N) × X → ℝ) (x : X) :
    canonicalZeroSpatialNarrowInput ξ u (none, x) = u (none, x) := rfl

@[simp] theorem canonicalZeroSpatialNarrowInput_inl {G N X : Type*} (ξ : ℝ)
    (u : Option (G ⊕ N) × X → ℝ) (g : G) (x : X) :
    canonicalZeroSpatialNarrowInput ξ u (some (.inl g), x) = u (some (.inl g), x) := rfl

@[simp] theorem canonicalZeroSpatialNarrowInput_inr {G N X : Type*} (ξ : ℝ)
    (u : Option (G ⊕ N) × X → ℝ) (n : N) (x : X) :
    canonicalZeroSpatialNarrowInput ξ u (some (.inr n), x) = ξ * u (some (.inr n), x) := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothBadPrimeProduct
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def coefficientCRTEquiv {L J : Type*} [Fintype L]
    (q : L → ℕ) (hq : Pairwise (fun l k => (q l).Coprime (q k))) :
    (J → ZMod (∏ l, q l)) ≃+ (∀ l, J → ZMod (q l)) where
  toFun x l j := ZMod.prodEquivPi q hq (x j) l
  invFun y j := (ZMod.prodEquivPi q hq).symm (fun l => y l j)
  left_inv x := by funext j; exact (ZMod.prodEquivPi q hq).symm_apply_apply (x j)
  right_inv y := by
    funext l j
    exact congrFun ((ZMod.prodEquivPi q hq).apply_symm_apply (fun l => y l j)) l
  map_add' x y := by
    funext l j
    exact congrFun (map_add (ZMod.prodEquivPi q hq) (x j) (y j)) l

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialInputStepLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {L V : Type*} [Fintype L]

local instance arbitraryStepCRTModulusNeZero (p A : L → ℕ) [∀ l, NeZero (p l)] :
    NeZero (∏ l, p l ^ A l) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedCappedContinuousSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

variable {Vact Out : Type*} [Fintype Vact] [DecidableEq Vact] [Fintype Out] [DecidableEq Out]

local instance instNeZeroNatOrderOfAddCharForallZModComplex_1 (N : ℕ) [NeZero N] (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
  ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

variable {Vact Out : Type*} [Fintype Vact] [DecidableEq Vact] [Fintype Out] [DecidableEq Out]

local instance instNeZeroNatOrderOfAddCharForallZModComplex_2 (N : ℕ) [NeZero N] (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
  ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

variable {Vact Out : Type*} [Fintype Vact] [DecidableEq Vact] [Fintype Out] [DecidableEq Out]

local instance instNeZeroNatOrderOfAddCharForallZModComplex_3 (N : ℕ) [NeZero N] (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
  ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SchmidtShortDualVector
namespace OAI

section

namespace Erdos3

open Polynomial
open scoped NNReal

noncomputable def affinePhaseRemainder (P : Polynomial ℝ) (k : ℕ) (a q : ℝ) :
    Polynomial ℝ := (P.comp (C q * X + C a)).erase k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedJointMaskedDensityComparison
namespace OAI

section

namespace Erdos3
open MeasureTheory

noncomputable def dominatedDensityRatio {X : Type*} (D A : X → ℝ) (x : X) : ℂ :=
  (A x / D x : ℝ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedMaskedCoefficientHaarLaw
namespace OAI

section

namespace Erdos3

noncomputable def allocatedUniformPMFCanonical (α : Type*) [Finite α] [Nonempty α] : PMF α :=
  @PMF.uniformOfFintype α (Fintype.ofFinite α) inferInstance

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankAffineProbability
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

noncomputable def affineSpatialCoefficients {A B R : Type*} [Semiring R]
    (spatial : B → Prop) (stride : B → ℕ) (offset : B → A → R)
    (c : B → A → R) : B → A → R :=
  fun b i => if spatial b then (stride b : R) * c b i + offset b i else c b i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRecoveredPreparedFreeze
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped Classical

variable {G X : Type*} {I E J : Fin 0 → Type*} {n : Fin 0 → ℕ}

variable [Fintype G]
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

def allocatedZeroLayerCenterLift : ∀ j, U j := fun j => Fin.elim0 j

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineBooleanCubeComparison
namespace OAI

section

namespace Erdos3

variable {I O : Type*} [Fintype I] [fintypeO : Fintype O]

noncomputable def affineSelectedInjection (L : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (J : (O → ℝ) →L[ℝ] (I → ℝ)) (δ : ℝ) : (O → ℝ) →L[ℝ] (I → ℝ) :=
  δ • (L.symm.toContinuousLinearMap.comp J)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.JointAffineBooleanSource
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {D α : Type*} [Fintype D] [Fintype α] [decidableEqAlpha : DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

noncomputable def jointAffineBooleanInverseBudget (h : D → ℕ) (C κ : D → ℝ) (δ : ℝ) : ℝ≥0 :=
  ∑ d, Real.toNNReal (δ⁻¹ * productMinorInverseBound (Fintype.card (O d)) (Fintype.card α)
    (h d) (C d) 1 (κ d))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedForecastShortRawDependence
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ}
  {G X : Type*}
  {I E : Fin m → Type*}
  {n : Fin m → ℕ}
  [Fintype G]
  [Fintype X]
  [∀ j, Fintype (I j)]
  [∀ j, Fintype (E j)]

local instance forecastProductModulusNeZero (Pr : Finset ℕ) (A : ℕ → ℕ)
    [∀ p : Pr, NeZero p.val] : NeZero (∏ p : Pr, p.val ^ A p.val) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ContainedKernelPhysicalDisplacement
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical NNReal
variable {G X : Type*} [Fintype G] [Fintype X]

noncomputable def fixedSpatialKernelMap (W L : ℝ) (z : Option G × X → ℝ)
    (t : G → ℝ) : (Σ _ : X, Unit ⊕ Empty) → ℝ :=
  fun a => z (none, a.1) + (L / (1 + W)) * ∑ g, z (some g, a.1) * t g

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastRawSpatialBoxReorder
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

noncomputable def mixedCoveredJetDeckReference {m : ℕ} (O E : Fin m → Type*)
    [∀ j, Fintype (O j)] [∀ j, Fintype (E j)] (N : ℕ) [NeZero N] :
    Measure (∀ j, O j → E j → ZMod N) :=
  (PMF.uniformOfFintype (∀ j, O j → E j → ZMod N)).toMeasure

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

noncomputable local instance instDecidableEqUnit : DecidableEq Unit := Classical.decEq Unit

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineFixedPathRationalReference
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {L V Short Out : Type*} [Fintype L] [Fintype V]
  [Fintype Out] [DecidableEq Out]

local instance arbitraryStepForecastModulusNeZero (p e : L → ℕ) [∀ l, NeZero (p l)] :
    NeZero (∏ l, p l ^ e l) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastShortGridEquiv
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def forecastShortGridEquiv (A : Type*) :
    (A → ℤ) ≃ (A → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) where
  toFun k a _ := k a
  invFun k a := k a ⟨∅, Finset.mem_univ _⟩
  left_inv _ := rfl
  right_inv k := by
    funext a row
    exact congrArg (k a) (Subsingleton.elim _ _)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastLawPhysicalAmbientHaarComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

theorem nativeFiniteExpansion_mean_comparison {Ω T : Type*} [Fintype T]
    (s : Finset Ω) (hs : s.Nonempty) (w H : Ω → ℂ) (f : T → Ω → ℂ)
    (c ref : T → ℂ) {δ ε M : ℝ} (hε : 0 ≤ ε)
    (hw : ∀ x ∈ s, ‖w x‖ ≤ 1)
    (happ : ∀ x ∈ s, ‖H x - ∑ i, c i * f i x‖ ≤ δ)
    (hcomp : ∀ i, ‖(𝔼 x ∈ s, w x * f i x) - ref i‖ ≤ ε)
    (hmass : ∑ i, ‖c i‖ ≤ M) :
    ‖(𝔼 x ∈ s, w x * H x) - ∑ i, c i * ref i‖ ≤ δ + M * ε := by
  have hexpand (x : Ω) : w x * (∑ i, c i * f i x) =
      ∑ i, c i * (w x * f i x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have happmean : ‖(𝔼 x ∈ s, w x * H x) -
      (𝔼 x ∈ s, ∑ i, c i * (w x * f i x))‖ ≤ δ := by
    rw [← Finset.expect_sub_distrib]
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le hs
    intro x hx
    rw [← hexpand, ← mul_sub, norm_mul]
    exact (mul_le_mul_of_nonneg_right (hw x hx) (norm_nonneg _)).trans
      (by simpa only [one_mul] using happ x hx)
  have hsum : ‖(∑ i, c i * (𝔼 x ∈ s, w x * f i x)) -
      ∑ i, c i * ref i‖ ≤ M * ε := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i, ‖c i * (𝔼 x ∈ s, w x * f i x) - c i * ref i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖c i‖ * ε := by
        apply Finset.sum_le_sum
        intro i _
        rw [← mul_sub, norm_mul]
        exact mul_le_mul_of_nonneg_left (hcomp i) (norm_nonneg _)
      _ = (∑ i, ‖c i‖) * ε := (Finset.sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hmass hε
  have hlinear : (𝔼 x ∈ s, ∑ i, c i * (w x * f i x)) =
      ∑ i, c i * (𝔼 x ∈ s, w x * f i x) := by
    rw [Finset.expect_sum_comm]
    simp only [Finset.mul_expect]
  rw [hlinear] at happmean
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add happmean hsum)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedCenteredForecastSpatialBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {G J X : Type*}

theorem preparedCenteredForecast_scaled_det_reciprocal
    {scale κ p K D : ℝ} (n : ℕ) (hscale : 0 < scale) (hκ : 0 < κ)
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ D)
    (hscaleinv : scale⁻¹ ≤ Real.exp p) (hκinv : κ⁻¹ ≤ Real.exp K) :
    0 < scale ^ n * κ ∧ (scale ^ n * κ)⁻¹ ≤ Real.exp (D * p + K) := by
  refine ⟨mul_pos (pow_pos hscale _) hκ, ?_⟩
  rw [mul_inv_rev, ← inv_pow]
  calc
    _ ≤ Real.exp K * (Real.exp p) ^ n :=
      mul_le_mul hκinv (pow_le_pow_left₀ (inv_nonneg.mpr hscale.le) hscaleinv _)
        (pow_nonneg (inv_nonneg.mpr hscale.le) _) (Real.exp_nonneg _)
    _ = Real.exp ((n : ℝ) * p + K) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hn hp])

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedActualForecastSetup
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped Classical BigOperators

section Generic
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}
variable {X : Type*} [Fintype X]

theorem ratioJacobian_product_le_exp {A : Type*} [Fintype A] {P : ℝ}
    (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) (hb : ∀ a, f a ≤ Real.exp P) :
    (∏ a, f a) ≤ Real.exp ((Fintype.card A : ℝ) * P) := by
  calc
    _ ≤ ∏ _a : A, Real.exp P := Finset.prod_le_prod (fun a _ => hf a) (fun a _ => hb a)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Real.exp_nat_mul]

end Generic

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedActualSlicedForecastSetup
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical NNReal

theorem and_rec_projection_p0 {p q : Prop} {α : Sort*}
    (f : p → q → α) (h : p ∧ q) : And.rec f h = f h.1 h.2 := by
  cases h
  rfl

noncomputable def preparedSlicedForecastJacobianLog (m M nX : ℕ)
    (pRadius gainLog Pchart : ℝ) : ℝ :=
  ((nX + m + m * M : ℕ) : ℝ) * (pRadius + gainLog + nX + Pchart + 11)

theorem preparedSliceWidth_inverse (cost : ℝ) :
    (Real.exp (-cost) / 2)⁻¹ ≤ Real.exp (cost + 1) := by
  rw [inv_div, div_eq_mul_inv, ← Real.exp_neg, neg_neg, Real.exp_add]
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
  nlinarith only [mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg cost)]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualSlicedForecastLateData
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

variable {Vact Out : Type*} [Fintype Vact] [DecidableEq Vact] [Fintype Out] [DecidableEq Out]

local instance instNeZeroNatOrderOfAddCharForallZModComplex_9 (N : ℕ) [NeZero N] (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
  ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedComparisonGridPolynomialBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

def preparedComparisonSourcePolynomial (t : ℝ) : ℝ :=
  2 + t * t + 2 * t

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedSlicedForecastComparisonLogs
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedSlicedForecastDensity (cost : ℝ) : ℝ :=
  Real.exp (-cost)

def preparedSlicedForecastKernelLog (cost : ℝ) : ℝ := cost + 1

noncomputable def preparedSlicedForecastChildSize (childLog : ℝ) : ℕ :=
  ⌈Real.exp childLog⌉₊

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedSlicedForecastCommonFloorExponent
    (periodLog childLog cost comparisonLog : ℝ) : ℝ :=
  max 0 (max periodLog (max childLog (max (cost + 1) comparisonLog)))

noncomputable def preparedSlicedForecastCommonFloor
    (periodLog childLog cost comparisonLog : ℝ) : ℕ :=
  ⌈Real.exp (preparedSlicedForecastCommonFloorExponent
    periodLog childLog cost comparisonLog)⌉₊

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeEndpointSourceBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedRelativeEndpointMinimumScale
    (seed periodLog childLog cost comparisonLog : ℝ) : ℕ :=
  max ⌈Real.exp seed⌉₊
    (preparedSlicedForecastCommonFloor periodLog childLog cost comparisonLog)

noncomputable def preparedRelativeEndpointMinimumLog
    (seed periodLog childLog cost comparisonLog : ℝ) : ℝ :=
  max (seed + 1)
    (preparedSlicedForecastCommonFloorExponent periodLog childLog cost comparisonLog + 1)

noncomputable def preparedRelativeEndpointGoodCutoff (Ptest : ℝ) : ℕ :=
  ⌈Real.exp (2 * Ptest)⌉₊

def preparedRelativeEndpointGoodLog (Ptest : ℝ) : ℝ := 2 * Ptest + 1

def preparedRelativeEndpointAmbientLog (modelRequired nativeAmbient gridAmbient : ℝ) : ℝ :=
  max modelRequired (max nativeAmbient gridAmbient)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeFinalPower
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedRelativeFinalEnvelope
    (degree basePower inputPower preparationPower requiredPower : ℕ)
    (discount p : ℝ) : ℝ :=
  2 + (p + 2) ^ preparationPower + (p + 2) ^ requiredPower +
    ((p + 2) ^ basePower + 2) ^ inputPower + (⌈discount⁻¹⌉₊ : ℝ) +
      (p + 2) ^ basePower + degree * p

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.DenseResidueMeshExponentialBudget
namespace OAI

section

namespace Erdos3

noncomputable def denseResidueMeshCap (n : ℕ) (δ ε C : ℝ) : ℕ :=
  ⌈16 * ((n : ℝ) + 1) * C / (ε * δ)⌉₊ + 1

noncomputable def denseResidueMeshStep (n : ℕ) (δ ε L : ℝ) : ℕ :=
  ⌊ε * δ * L / (8 * ((n : ℝ) + 1))⌋₊

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AffineSidePolynomialBudget
namespace OAI

section

namespace Erdos3

noncomputable def affineLocalDegreeInputBudget (P : ℝ) : ℝ :=
  affinePrimitiveLogBudget P * (affinePrimitiveLogBudget P + 2 * P ^ 2 + 2) + 3 * P + 11

noncomputable def affineOuterDegreeInputBudget (P : ℝ) : ℝ := P * (2 * P ^ 2 + 1) + 4

noncomputable def affineLocalDegreeBudget (P : ℝ) : ℝ :=
  affinePrimitiveLogBudget P + 2 * (affineLocalDegreeInputBudget P + affineShellLogBudget P + 4) + 2

noncomputable def affineAdaptiveDegreeBudget (P : ℝ) : ℝ :=
  P + affineLocalDegreeBudget P + 2 * (affineOuterDegreeInputBudget P + affineShellLogBudget P + 4) + 2

end Erdos3

end

section

namespace Erdos3

noncomputable def affineOrderPolynomialBudget (P : ℝ) : ℝ :=
  affinePrimitiveLogBudget P * (affinePrimitiveLogBudget P + 3) +
    2 * affineAdaptiveDegreeBudget P + affinePrimitiveLogBudget P

noncomputable def affineAccuracyPolynomialBudget (P : ℝ) : ℝ :=
  (affinePrimitiveLogBudget P + 3) ^ 3 +
    2 * affineAdaptiveDegreeBudget P * (affinePrimitiveLogBudget P + 2) + 2 * P + 4

noncomputable def affineSidePolynomialBudget (P : ℝ) : ℝ :=
  P ^ 2 + P * affineOrderPolynomialBudget P + affineAccuracyPolynomialBudget P + P + 3

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedScalarFiniteScheduleCandidateDetection
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX : ℕ}
noncomputable local instance fixedSourceFinDecidableEq : DecidableEq (Fin nX) := Classical.decEq _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteNestedForwardCanonicalFixedCenterSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX M : ℕ} {X₀ J₀ : Type}
noncomputable local instance productiveFixedSourceFinDecidableEq : DecidableEq (Fin nX) := Classical.decEq _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeEndpointNumericalBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedRelativeEndpointInputBase (earlyPower : ℕ) (B : ℝ) : ℝ :=
  (B + 2) ^ earlyPower + B + 1

theorem preparedRelativeEndpointInputBase_bounds (earlyPower : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    1 ≤ preparedRelativeEndpointInputBase earlyPower B ∧
    B ≤ preparedRelativeEndpointInputBase earlyPower B ∧
    (B + 2) ^ earlyPower + 1 ≤ preparedRelativeEndpointInputBase earlyPower B := by
  have hp : 0 ≤ (B + 2) ^ earlyPower := by positivity
  unfold preparedRelativeEndpointInputBase
  exact ⟨by linarith only [hp, hB], by linarith only [hp], by linarith only [hB]⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeLongCommonFactors
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical TensorProduct NNReal

noncomputable section

variable {m : ℕ}
  {G X : Type*}
  [Fintype G]
  [Fintype X]
  {I J : Fin m → Type*}
  [∀ j, Fintype (I j)]
  [∀ j, Fintype (J j)]
  {n : Fin m → ℕ}
  {U : ∀ j, Submodule ℝ (J j → ℝ)}
  {R σ : Fin m → ℝ}
  {hR : ∀ j, 0 < R j}
  {hσ : ∀ j, 0 < σ j}
  {N : X → ℕ}
  {τ ξ : ℝ}
  {stride : X → ℕ}

theorem compose_exponential_mass_losses_p1 {a b x y z : ℝ}
    (hfirst : Real.exp (-a) * x ≤ y) (hsecond : Real.exp (-b) * y ≤ z) :
    Real.exp (-(a + b)) * x ≤ z := by
  calc
    _ = Real.exp (-b) * (Real.exp (-a) * x) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hfirst (Real.exp_pos _).le).trans hsecond

end

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CandidateFrontFactorPolynomialBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem bounds_of_sum {ci fa lt ml B : ℝ}
    (hci : 0 ≤ ci) (hfa : 0 ≤ fa) (hlt : 0 ≤ lt) (hml : 0 ≤ ml)
    (hciFast : ci ≤ fa) (hsum : fa + lt + ml ≤ B) :
    ci ∈ Set.Icc 0 B ∧ fa ∈ Set.Icc 0 B ∧
      lt ∈ Set.Icc 0 B ∧ ml ∈ Set.Icc 0 B := by
  exact ⟨⟨hci, by linarith⟩, ⟨hfa, by linarith⟩,
    ⟨hlt, by linarith⟩, ⟨hml, by linarith⟩⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CandidateFrontFactorMassBlockBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem candidateFrontFactor_uniform_block_le_power (s Ctotal : ℕ)
    {m : ℕ} {p markInput ci : ℝ} (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p)
    (hmark : markInput ≤ ci) (hci : ci ≤ (p + 2) ^ Ctotal) :
    (s : ℝ) * (markInput * m) ≤ (p + 2) ^ (Ctotal + s + 1) := by
  have hbase : 0 ≤ p + 2 := by linarith only [hp]
  have htwo : (s : ℝ) ≤ (2 : ℝ) ^ s := by
    exact_mod_cast (show s < 2 ^ s from Nat.lt_two_pow_self).le
  have hs : (s : ℝ) ≤ (p + 2) ^ s :=
    htwo.trans (pow_le_pow_left₀ (by norm_num) (by linarith only [hp]) s)
  have hcoefficient : (s : ℝ) * m ≤ (p + 2) ^ s * (p + 2) :=
    mul_le_mul hs (by linarith only [hm]) (Nat.cast_nonneg _) (pow_nonneg hbase _)
  calc
    _ = ((s : ℝ) * m) * markInput := by ring
    _ ≤ ((s : ℝ) * m) * (p + 2) ^ Ctotal :=
      mul_le_mul_of_nonneg_left (hmark.trans hci) (by positivity)
    _ ≤ ((p + 2) ^ s * (p + 2)) * (p + 2) ^ Ctotal :=
      mul_le_mul_of_nonneg_right hcoefficient (pow_nonneg hbase _)
    _ = (p + 2) ^ (Ctotal + s + 1) := by
      rw [← pow_succ, ← pow_add]
      congr 1
      omega

theorem candidateFrontFactor_massLog_le
    {v V n p qCommon common mass0 : ℝ}
    (hv0 : 0 ≤ v) (hv : v ≤ V) (hn0 : 0 ≤ n) (hn : n ≤ p)
    (hq0 : 0 ≤ qCommon) (hq : qCommon ≤ common) (hmass : mass0 ≤ p) :
    v * n + ((qCommon + 2) ^ 5 + qCommon) + mass0 ≤
      p + V * p + ((common + 2) ^ 5 + common) := by
  have hproduct : v * n ≤ V * p := mul_le_mul hv hn hn0 (hv0.trans hv)
  have hpower : (qCommon + 2) ^ 5 ≤ (common + 2) ^ 5 :=
    pow_le_pow_left₀ (by linarith only [hq0]) (by linarith only [hq]) 5
  linarith only [hproduct, hpower, hq, hmass]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RelativeSourceDensityParameter
namespace OAI

section

namespace Erdos3

noncomputable def cyclicIntervalSet (S : Finset ℕ) (m : ℕ) [NeZero m] : Finset (ZMod m) := by
  classical
  exact Finset.univ.filter fun x => x.val ∈ S

end Erdos3

end

end OAI
end


