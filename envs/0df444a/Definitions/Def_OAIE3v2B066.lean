-- Prove2me | Definitions.Def_OAIE3v2B066
-- name    : OAIE3v2B066
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:17:13.879783+00:00
-- url     : https://prove2.me/theorems/0e88beba-e0c0-4a74-adea-d58b2f25bfdc
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 67 of 311
-- statement:
--   Definitions bundle 67 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B000`, `OAIE3v2B001`, `OAIE3v2B002`, `OAIE3v2B004`, `OAIE3v2B005`, `OAIE3v2B006`, `OAIE3v2B008`, `OAIE3v2B009`, `OAIE3v2B010`, `OAIE3v2B011`, `OAIE3v2B012`, `OAIE3v2B015`, `OAIE3v2B016`, `OAIE3v2B019`, `OAIE3v2B027`, `OAIE3v2B028`, `OAIE3v2B029`, `OAIE3v2B030`, `OAIE3v2B031`, `OAIE3v2B032`, `OAIE3v2B033`, `OAIE3v2B034`, `OAIE3v2B035`, `OAIE3v2B036` of this split.
--
--   Modules: `Dynamics/AllocatedFixedPathSlicedNativeAmbientComparison.lean`, `Dynamics/BooleanCanonicalLogBudget.lean`, `Dynamics/CandidateCommonFastBudgetMonotonicity.lean`, `Dynamics/CyclicProductBudget.lean`, `Dynamics/JointBooleanWeightBudget.lean`, `Dynamics/PhysicalBadProductErrorBudget.lean`, `Estimates/AllocatedExternalCandidateTaggedPairUniformFactors.lean`, `Estimates/AmplificationFinalCostGrowth.lean`, `Estimates/AnisotropicTupleErrorChoice.lean`, `Estimates/BooleanCubeModeWitness.lean`, `Estimates/BooleanMinorDimension.lean`, `Estimates/BooleanSelectedDerivativeBound.lean`, `Estimates/CanonicalScalarSourceEnvelope.lean`, `Estimates/CoefficientNormalization.lean`, `Estimates/CopiedLayerSpace.lean`, `Estimates/FiniteSectionPermutation.lean`, `Estimates/MaskedIntervalApproximation.lean`, `Estimates/MixedArrayReference.lean`, `Estimates/MixedCoveredSiteExtraction.lean`, `Estimates/NativePhysicalHaarExpansion.lean`, `Estimates/PreparedFiniteScheduleLocalScalarConstruction.lean`, `Estimates/PreparedModularProductivityPrecision.lean`, `Estimates/PrincipalCoefficientMarginal.lean`, `Estimates/ProductCutoffLipschitz.lean`, `Estimates/ProductMeanPullback.lean`, `Estimates/ScalarCubeFaceSlab.lean`, `Estimates/SlicedPrincipalInverse.lean`, `Fourier/CRTConfigurationTorus.lean`, `Fourier/MonomialCharacterMean.lean`, `Fourier/PlateauFourierMode.lean`, `Fourier/PrimePowerCharacterScaling.lean`, `Geometry/ActualFixedSpatialSlicedTargetReal.lean`, `Geometry/AllocatedFullSiteSupport.lean`, `Geometry/BoxTestSmoothing.lean`, `Geometry/NormalizedSupportPlateau.lean`, `Geometry/PreparedEarlySpatialWidth.lean`, `Geometry/PreparedModularGeneralDetectorFreeSpatialBounds.lean`, `Geometry/PrincipalSpatialSiteComparison.lean`, `Geometry/SmoothSpatialCostBudget.lean`, `Geometry/SpatialPivotNormalization.lean`, `Geometry/SpatialSiteShift.lean`, `Geometry/UnconditionedSpatialWidthBudget.lean`, `Lattices/AffineBoxTest.lean`, `Lattices/AffineCommonReferenceBudget.lean`, `Lattices/AffineKernelEndpointGeometry.lean`, `Lattices/AffineMeshRetention.lean`, `Lattices/AffineModeratePlateauModel.lean`, `Lattices/AffinePrimitiveLogBudget.lean`, `Lattices/AffineSampleAlphabet.lean`, `Lattices/AllocatedModularRankAffineFullWitness.lean`, `Lattices/BoundedPrimeDepthBudget.lean`, `Lattices/BoxResiduePartition.lean`, `Lattices/CRTIntegerRepresentative.lean`, `Lattices/CRTProgressionVanishing.lean`, `Lattices/EuclideanDerivativeLattice.lean`, `Lattices/ForecastOriginalSampleResidueFactor.lean`, `Lattices/InitialMaskedAffineComparison.lean`, `Lattices/IntegerBoxObservedMean.lean`, `Lattices/IntegerRowInterpolationMixture.lean`, `Lattices/LatticeDualCoordinates.lean`, `Lattices/MixedCoveredIntegerReconstruction.lean`, `Lattices/NormalizedLatticeSheet.lean`, `Lattices/PartitionedAffineLogEnvelope.lean`, `Lattices/PrimeCoordinateCells.lean`, `Lattices/PrimeFamilyCutoff.lean`, `Lattices/ResidueIntervalFactors.lean`, `Lattices/ResidueRefinedPeriod.lean`, `Lattices/ResidueSliceCountingCost.lean`, `Lattices/RetainedPhysicalCRT.lean`, `Lattices/ScalarCubeLatticeGeometry.lean`, `Lattices/SmoothAffinePairLaw.lean`, `Lattices/StrideSelectedResidueBadProduct.lean`, `Lattices/UniformBoxResidueMass.lean`, `Lattices/WeightedCubeIntegerSupport.lean`, `Linear/AllocatedFixedKernelReplacement.lean`, `Linear/AmplificationSourceRankBudget.lean`, `Linear/AnisotropicGoodKernelComparison.lean`, `Linear/KernelScalarEnvelope.lean`, `Linear/PreparedSpatialKernelBlocks.lean`, `Linear/RankPreparationSizes.lean`, `Linear/RealKernelJetInverse.lean`, `Polynomial/AffineDegreeChoice.lean`, `Polynomial/BooleanBlockCoefficientPhase.lean`, `Polynomial/BoundedRealPolynomialBasis.lean`, `Polynomial/CRTPolynomialChargeBound.lean`, `Polynomial/CRTPolynomialInputAffineLaw.lean`, `Polynomial/CommonPolynomialScale.lean`, `Polynomial/ForecastSlicedEarlyUnrestrictedPolynomialBudget.lean`, `Polynomial/GlobalAffineDegreeChoice.lean`, `Polynomial/PolynomialDeterminantDerivativeBound.lean`, `Polynomial/PreparedComparisonGridPolynomialBudget.lean`, `Polynomial/PreparedFiniteNestedForwardAllDegreePaddedSource.lean`, `Probability/AnisotropicSpatialLaw.lean`, `Probability/CanonicalZeroSpatialDensity.lean`, `Probability/CanonicalZeroSpatialInputLaw.lean`, `Probability/CoefficientJetDensityFactors.lean`, `Probability/DiagonalDensityTransport.lean`, `Probability/MixedCoveredDensityMass.lean`, `Probability/ScalarCubeDensityBudget.lean`, `Probability/ScaledCubeProductMeasure.lean`, `Probability/SelectedDependentMeasure.lean`, `Sampling/ActualForecastModelPrecision.lean`, `Sampling/AllocatedSamplerRelativeInduction.lean`, `Sampling/CanonicalSamplerTuple.lean`, `Sampling/ForecastJointScaleNormalization.lean`, `Sampling/ForecastModularCutoff.lean`, `Sampling/ForecastOriginalSampleUniformBudget.lean`, `Sampling/ForecastRawSpatialBoxReorder.lean`, `Sampling/LayerSamplerWitnessScale.lean`, `Sampling/PreparedActualSlicedForecastSetup.lean`, `Sampling/PreparedCenteredForecastPathLogEnvelope.lean`, `Sampling/PreparedSlicedForecastComparisonLogs.lean`, `Sampling/SmoothSplitSampling.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B000
import Definitions.Def_OAIE3v2B001
import Definitions.Def_OAIE3v2B002
import Definitions.Def_OAIE3v2B004
import Definitions.Def_OAIE3v2B005
import Definitions.Def_OAIE3v2B006
import Definitions.Def_OAIE3v2B008
import Definitions.Def_OAIE3v2B009
import Definitions.Def_OAIE3v2B010
import Definitions.Def_OAIE3v2B011
import Definitions.Def_OAIE3v2B012
import Definitions.Def_OAIE3v2B015
import Definitions.Def_OAIE3v2B016
import Definitions.Def_OAIE3v2B019
import Definitions.Def_OAIE3v2B027
import Definitions.Def_OAIE3v2B028
import Definitions.Def_OAIE3v2B029
import Definitions.Def_OAIE3v2B030
import Definitions.Def_OAIE3v2B031
import Definitions.Def_OAIE3v2B032
import Definitions.Def_OAIE3v2B033
import Definitions.Def_OAIE3v2B034
import Definitions.Def_OAIE3v2B035
import Definitions.Def_OAIE3v2B036

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceCountingCost
namespace OAI

section

namespace Erdos3

noncomputable instance compatibleAuxResidueFintype (M d : ℕ) (u : ℤ) :
    Fintype (CompatibleAuxResidue M d u) := Fintype.ofFinite _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoxResiduePartition
namespace OAI

section

namespace Erdos3

theorem integerIntervalEquivFin_val (a : ℤ) (N : ℕ) (x : ↥(Finset.Ico a (a + N))) :
    ((integerIntervalEquivFin a N x).val : ℤ) = x.val - a := by
  have hx := Finset.mem_Ico.mp x.property
  change (((x.val - a).toNat : ℕ) : ℤ) = x.val - a
  omega

end Erdos3

end

section

namespace Erdos3

noncomputable def intervalCellLower (a : ℤ) {N : ℕ} (P : FiniteProgressionPartition N) (k : P.Label) : ℤ :=
  a + P.start k

noncomputable def intervalCellUpper (a : ℤ) {N : ℕ} (P : FiniteProgressionPartition N) (k : P.Label) : ℤ :=
  a + P.start k + P.length k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineBoxTest
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {ι : Type*} [Fintype ι]

noncomputable def affineBoxIntegrand (ℓ : ι → ℝ) (A : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (g : (ι → ℝ) → ℝ) (p : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  boxProbabilityWindow ℓ 0 p.2 * g (p.1 + A p.2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxTestSmoothing
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def boxTestAverage (δ : ℝ) (φ : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  kernelAverage volume (boxProbabilityWindow (fun _ => δ)) φ

noncomputable def boxTestLipschitz (δ : ℝ) (hδ : 0 < δ) : ℝ≥0 :=
  boxWindowTranslationBound (fun _ : ι => δ) (fun _ => hδ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PrimePowerCharacterScaling
namespace OAI

section

namespace Erdos3

theorem zmodPiReduction_surjective {I : Type*} {n m : ℕ} (h : m ∣ n) :
    Function.Surjective (zmodPiReduction (I := I) h) := by
  intro y
  choose x hx using fun i => ZMod.castHom_surjective h (y i)
  exact ⟨x, funext hx⟩

theorem zmodPiReduction_kernel_nsmul {I : Type*} {n m : ℕ} [NeZero n]
    (h : m ∣ n) (x : I → ZMod n) (hx : zmodPiReduction h x = 0) :
    ∃ y : I → ZMod n, m • y = x := by
  have hdvd (i : I) : m ∣ (x i).val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    have hi := congrFun hx i
    simpa only [zmodPiReduction_apply, ZMod.castHom_apply, ZMod.cast_eq_val,
      Pi.zero_apply] using hi
  choose w hw using hdvd
  refine ⟨fun i => (w i : ZMod n), ?_⟩
  funext i
  change m • (w i : ZMod n) = x i
  rw [nsmul_eq_mul, ← Nat.cast_mul, ← hw i, ZMod.natCast_zmod_val]

theorem zmodPiReduction_kernel_character {I : Type*} {n m : ℕ} [NeZero n]
    (h : m ∣ n) (χ : AddChar (I → ZMod n) ℂ) (hχ : χ ^ m = 1)
    (x : I → ZMod n) (hx : zmodPiReduction h x = 0) : χ x = 1 := by
  obtain ⟨y, hy⟩ := zmodPiReduction_kernel_nsmul h x hx
  rw [← hy, AddChar.map_nsmul_eq_pow]
  exact congrArg (fun ψ : AddChar (I → ZMod n) ℂ => ψ y) hχ

theorem exists_zmodPiReduction_character {I : Type*} {n m : ℕ} [NeZero n]
    (h : m ∣ n) (χ : AddChar (I → ZMod n) ℂ) (hχ : χ ^ m = 1) :
    ∃ ψ : AddChar (I → ZMod m) ℂ,
      characterPullback (zmodPiReduction h) ψ = χ ∧ orderOf ψ = orderOf χ := by
  let q := zmodPiReduction (I := I) h
  let f := q.toMultiplicative
  have hf : Function.Surjective f := zmodPiReduction_surjective h
  let g := χ.toMonoidHom.toHomUnits
  have hker : f.ker ≤ g.ker := by
    intro x hx
    apply Units.ext
    change χ x.toAdd = 1
    exact zmodPiReduction_kernel_character h χ hχ x.toAdd hx
  let lifted := f.liftOfSurjective hf ⟨g, hker⟩
  let ψ : AddChar (I → ZMod m) ℂ :=
    AddChar.toMonoidHomEquiv.symm ((Units.coeHom ℂ).comp lifted)
  have heq : characterPullback q ψ = χ := by
    apply AddChar.ext
    intro x
    change (lifted (f (Multiplicative.ofAdd x)) : ℂ) = χ x
    simp only [lifted, MonoidHom.liftOfSurjective,
      MonoidHom.liftOfRightInverse_comp_apply]
    rfl
  refine ⟨ψ, heq, ?_⟩
  rw [← characterPullback_order q (zmodPiReduction_surjective h) ψ, heq]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
namespace OAI

section

namespace Erdos3

def residueLatticeImage {I : Type*} (L : Submodule ℤ (I → ℤ)) (m : ℕ) :
    Submodule ℤ (I → ZMod m) := L.map (integerResidueMap I m)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.EuclideanDerivativeLattice
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {σ κ : Type*} [Fintype σ] [Fintype κ]

variable (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
  (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (l : ℕ) (hl : 0 < l)

instance derivativeLattice_discrete : DiscreteTopology (derivativeLattice T hT scale hscale Y A l hl) :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ
    (Set.range (derivativeLatticeBasis T hT scale hscale Y A l hl))))

instance derivativeLattice_full : IsZLattice ℝ (derivativeLattice T hT scale hscale Y A l hl) :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ
    (Set.range (derivativeLatticeBasis T hT scale hscale Y A l hl))))

end Erdos3

end

section

namespace Erdos3

open Module

variable {σ κ : Type*} [Fintype σ] [Fintype κ]
  (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
  (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (l : ℕ) (hl : 0 < l)

instance euclideanDerivativeLattice_full :
    IsZLattice ℝ (euclideanDerivativeLattice T hT scale hscale Y A l hl) :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ
    (Set.range (euclideanDerivativeLatticeBasis T hT scale hscale Y A l hl))))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DiagonalDensityTransport
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {ι : Type*}

theorem inverseJacobian_eq (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) :
    inverseJacobian A = |LinearMap.det A.toLinearEquiv.toLinearMap|⁻¹ := by
  unfold inverseJacobian
  rw [show A.symm.toLinearEquiv = A.toLinearEquiv.symm from rfl,
    LinearEquiv.det_coe_symm, abs_inv]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)

noncomputable def diagonalDensityTransport (f : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  linearDensityPullback (coordinateScaleEquiv a ha).toContinuousLinearEquiv f

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeModeWitness
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def booleanSiteJets {D α : Type*} [DecidableEq α]
    {O : D → Type*} (sets : ∀ d, O d → Finset α) (x : Finset α → D → ℝ) : (Σ d, O d) → ℝ :=
  fun o => booleanCoefficient (fun s => x s o.1) (sets o.1 o.2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDeterminantDerivativeBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def blockSpecialization {B F α : Type*} [DecidableEq α]
    (label : B → F → Option α) (z : BlockParameter B F α) : ℝ :=
  if z.2.2 = label z.1 z.2.1 then 1 else 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CRTConfigurationTorus
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def crtConfigurationCharacter {J : Type*} [Fintype J] (N : J → ℕ)
    [∀ j, NeZero (N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j))) (frequency : J × Bool → ℤ) :
    AddChar (ZMod (∏ j, N j) × ZMod (∏ j, N j)) ℂ where
  toFun z := ∏ t, CircleFourier.character (frequency t • crtConfigurationTorus N hN z t)
  map_zero_eq_one' := by simp
  map_add_eq_mul' z v := by
    simp only [map_add, Pi.add_apply, smul_add, CircleFourier.character_add, Finset.prod_mul_distrib]

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

noncomputable def crtProgressionWeight {J : Type*} [Fintype J] (N : J → ℕ)
    [∀ j, NeZero (N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j))) (k : ℕ)
    (z : ZMod (∏ j, N j) × ZMod (∏ j, N j)) : ℝ :=
  progressionTorusCutoff k (crtConfigurationTorus N hN z)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BoundedRealPolynomialBasis
namespace OAI

section

namespace Erdos3

open scoped BigOperators

instance boundedIntegerExponentInhabited (K : Type*) (h : ℕ) :
    Inhabited (BoundedIntegerExponent K h) := ⟨⟨0, by simp⟩⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealKernelJetInverse
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def realJetMatrix {α K O J : Type*} [DecidableEq α]
    (basis : J → MvPolynomial K ℝ) (vertices : Finset α → K → ℝ)
    (rows : O → Finset α) : Matrix O J ℝ :=
  fun o j => booleanCoefficient (fun t => MvPolynomial.eval (vertices t) (basis j)) (rows o)

noncomputable def boundedDegreeRealJetMatrix {α K O : Type*} [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ) (h : ℕ)
    (rows : O → Finset α) : Matrix O (BoundedIntegerExponent K h) ℝ :=
  realJetMatrix (fun e => MvPolynomial.monomial e.val 1)
    (realAffineCube root difference) rows

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BooleanBlockCoefficientPhase
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def booleanBlockValue {G α : Type*} [Fintype G] [Fintype α] [DecidableEq α]
    (a : G → Option α → ℝ) (t : Finset α) : ℝ :=
  ∏ g, ∑ r, (booleanFeature r t : ℝ)*a g r

noncomputable def booleanBlockPhase {G α : Type*} [Fintype G] [Fintype α] [DecidableEq α]
    (ξ : Finset α → ℝ) (a : G → Option α → ℝ) : ℝ :=
  ∑ s, ξ s * booleanCoefficient (booleanBlockValue a) s

def frozenBooleanConstant {G α : Type*} [Fintype α] [DecidableEq α]
    (label : G → Option α) (c : G → Option α → ℝ) (t : Finset α) (g : G) : ℝ :=
  ∑ r ∈ Finset.univ.erase (label g), (booleanFeature r t : ℝ)*c g r

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanMinorDimension
namespace OAI

section

namespace Erdos3

theorem blockParameter_card {B α : Type*} [Fintype B] [Fintype α] (h : ℕ) :
    Fintype.card (BlockParameter B (Fin h) α) = Fintype.card B * (h * (Fintype.card α + 1)) := by
  simp only [BlockParameter, Fintype.card_prod, Fintype.card_fin, Fintype.card_option]

end Erdos3

end

section

namespace Erdos3

noncomputable def booleanBlockParameterEquiv (O α : Type*) [Fintype O] [Fintype α] (h : ℕ) :
    BlockParameter O (Fin h) α ≃ Fin (Fintype.card O * (h * (Fintype.card α + 1))) :=
  Fintype.equivFinOfCardEq (blockParameter_card h)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarCubeFaceSlab
namespace OAI

section

namespace Erdos3

open MeasureTheory

def closedScalarCubeDomain (α : Type*) [Fintype α] [DecidableEq α] : Set (Option α → ℝ) :=
  {a | ∀ t : Finset α, scalarCubeValue a t ∈ Set.Icc (0 : ℝ) 1}

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScaledCubeProductMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

def scalarCubeProductDomain (ι α : Type*) [Fintype ι] [Fintype α] [DecidableEq α] :
    Set (ι → Option α → ℝ) := Set.univ.pi (fun _ => scalarCubeDomain α)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductCutoffLipschitz
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def finiteRectangleRefinement {I : Type*} (K N : I → ℕ) :
    ((∀ i, Fin (K i)) × (∀ i, Fin (N i))) ≃ (∀ i, Fin (K i * N i)) where
  toFun x i := finProdFinEquiv (x.1 i, x.2 i)
  invFun y := (fun i => (finProdFinEquiv.symm (y i)).1,
    fun i => (finProdFinEquiv.symm (y i)).2)
  left_inv x := by
    apply Prod.ext <;> funext i <;> simp
  right_inv y := by
    funext i
    exact finProdFinEquiv.apply_symm_apply (y i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarCubeLatticeGeometry
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem scalarCubeValue_formula {I : Type*} [Fintype I] [DecidableEq I]
    (x : Option I → ℝ) (t : Finset I) :
    scalarCubeValue x t = x none + ∑ i ∈ t, x (some i) := by
  simp [scalarCubeValue, Fintype.sum_option, booleanFeature, ite_mul]

theorem scalarCubeValue_sub_bound {I : Type*} [Fintype I] [DecidableEq I]
    (x y : Option I → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (he : ‖x-y‖ ≤ δ) (t : Finset I) :
    |scalarCubeValue x t - scalarCubeValue y t| ≤ (Fintype.card I + 1 : ℝ)*δ := by
  have hi (i : Option I) : |x i-y i| ≤ δ := (norm_le_pi_norm (x-y) i).trans he
  have hsum : |∑ i ∈ t, (x (some i)-y (some i))| ≤ (t.card : ℝ)*δ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum (fun i (_ : i ∈ t) => hi (some i))
  have hcard : (t.card : ℝ) ≤ Fintype.card I := by exact_mod_cast t.card_le_univ
  have hid : scalarCubeValue x t - scalarCubeValue y t =
      (x none-y none) + ∑ i ∈ t, (x (some i)-y (some i)) := by
    simp only [scalarCubeValue_formula, Finset.sum_sub_distrib]
    ring
  rw [hid]
  exact (abs_add_le _ _).trans ((add_le_add (hi none) hsum).trans (by nlinarith))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeDensityBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def scalarCubeInnerBox (I : Type*) [Fintype I] : Set (Option I → ℝ) :=
  Set.Icc (fun i => scalarCubeCenter I i-1/(4*((Fintype.card I : ℝ)+1)))
    (fun i => scalarCubeCenter I i+1/(4*((Fintype.card I : ℝ)+1)))

theorem scalarCubeInnerBox_volume (I : Type*) [Fintype I] :
    volume.real (scalarCubeInnerBox I) = (1/(2*((Fintype.card I : ℝ)+1)))^(Fintype.card I+1) := by
  have hr : 0 ≤ 1/(4*((Fintype.card I : ℝ)+1)) := by positivity
  have ho : (fun i => scalarCubeCenter I i-1/(4*((Fintype.card I : ℝ)+1))) ≤
      (fun i => scalarCubeCenter I i+1/(4*((Fintype.card I : ℝ)+1))) := fun i => by linarith
  have he (i : Option I) : scalarCubeCenter I i+1/(4*((Fintype.card I : ℝ)+1))-
      (scalarCubeCenter I i-1/(4*((Fintype.card I : ℝ)+1))) = 1/(2*((Fintype.card I : ℝ)+1)) := by
    field_simp
    ring
  simp only [measureReal_def, scalarCubeInnerBox, Real.volume_Icc_pi_toReal ho, he,
    Finset.prod_const, Finset.card_univ, Fintype.card_option]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanSelectedDerivativeBound
namespace OAI

section

namespace Erdos3

noncomputable def booleanSelectedInjection {B O F α : Type*}
    [Fintype O] [DecidableEq B] [DecidableEq F] [DecidableEq α]
    (block : O → B) (v : F) (r : O → Option α) :
    (O → ℝ) →L[ℝ] (BlockParameter B F α → ℝ) :=
  coordinateInjection (fun col => (block col, v, r col))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientNormalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def normalizedCoefficientTailValue {T K Z I α : Type*} [Fintype α] [DecidableEq α]
    (terms : Finset T) (weight : T → ℝ) (exponent : T → K →₀ ℕ)
    (coefficientIndex : T → Z) (inputIndex : K → Option α → Z ⊕ I)
    (z : Z → ℝ) (x : I → ℝ) (s : Finset α) : ℝ :=
  booleanCoefficient (fun t => ∑ n ∈ terms, (weight n * z (coefficientIndex n)) *
    ∏ k ∈ (exponent n).support,
      (∑ r, (booleanFeature r t : ℝ) * Sum.elim z x (inputIndex k r)) ^ exponent n k) s

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CanonicalSamplerTuple
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def normalizedCubeTuple {K Z I α : Type*} [Fintype α] [DecidableEq α]
    (input : K → Option α → Z ⊕ I) (z : Z → ℝ) (x : I → ℝ) (vertex : Finset α) (k : K) : ℝ :=
  ∑ r : Option α, (booleanFeature r vertex : ℝ) * Sum.elim z x (input k r)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalCoefficientMarginal
namespace OAI

section

namespace Erdos3

open VectorPolynomial

noncomputable def principalCoefficientChoice {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) :
    Option (B d) → BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d)
  | none => constantCoefficientSlot _ _
  | some b => principalCoefficientSlot h d b

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

def selectedSpatialFreeColumns {I J R : Type*} [CommRing R]
    (root : J → R) (D : Matrix I J R) (s : I ↪ J) : Matrix (Unit ⊕ I) (UnselectedColumn s) R :=
  Matrix.of (fun i j => Sum.elim (fun _ : Unit => root j.val) (fun i => D i j.val) i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SmoothSplitSampling
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

noncomputable def smoothSampleSum (S : ℝ) : ℝ :=
  ∑' k : ℤ, smoothProbabilityProfile ((k : ℝ) / S)

theorem smoothProfileSamples_summable {S : ℝ} (hS : 0 < S) :
    Summable (fun k : ℤ => smoothProbabilityProfile ((k : ℝ) / S)) := by
  have h : Summable (sampledWeight smoothProbabilityProfile 0 S) :=
    (hasSum_sum_of_ne_finset_zero (sampledWeight_zero_off_indices smoothProbabilityProfile
      (a := 0) hS smoothProbabilityProfile_zero_outside)).summable
  change Summable (fun k : ℤ => smoothProbabilityProfile (((k : ℝ) - 0) / S)) at h
  simpa only [sub_zero] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothAffinePairLaw
namespace OAI


namespace Erdos3

open scoped Classical

noncomputable def latticeStarMask {I : Type*}
    (L : Submodule ℤ ((Unit ⊕ I) → ℤ)) (m : ℕ) (a : (Unit ⊕ I) → ZMod m) : ℂ := by
  classical
  exact if spatialUnstar a ∈ residueLatticeImage L m then (L.toAddSubgroup.index : ℂ) else 0

end Erdos3


namespace Erdos3

open scoped Matrix

theorem affinePairScale_pos {H L : ℝ} (hH : 0 < H) (hL : 0 < L) :
    ∀ i, 0 < affinePairScale H L i := by
  intro i
  fin_cases i
  · exact hH
  · exact div_pos hH hL

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialChargeBound
namespace OAI


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

noncomputable def crtPrimePowerPolynomialMap {s : ℕ} {J : Fin s → Type*}
    (p A e : L → ℕ) (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (F : ∀ j, J j → MvPolynomial V ℤ) (r : ∀ l, V → ZMod (p l ^ A l))
    (x : ∀ l, V → ZMod (p l ^ A l)) (j : Fin s) (i : J j) : ZMod (∏ l, p l ^ A l) :=
  eval₂ (Int.castRingHom (ZMod (∏ l, p l ^ A l)))
    (crtInput (fun l => p l ^ A l) hq
      (fun l v => r l v + (p l : ZMod (p l ^ A l)) ^ e l * x l v)) (F j i)

noncomputable def crtPolynomialCharge (p b e : L → ℕ) (s : ℕ) (C : ℝ) : ℝ :=
  (∏ l, ((p l ^ (b l + e l) : ℕ) : ℝ)) ^
    (modularRankDecayExponent s C * modularRankChargeFactor s)

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AmplificationFinalCostGrowth
namespace OAI

section

open Filter

namespace Erdos3

def amplificationResource (p : ℝ) (D K : ℕ) : ℕ → ℝ
  | 0 => (2 + p) ^ D
  | j + 1 => (2 + amplificationResource p D K j) ^ K

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRowInterpolationMixture
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {O : Type*} [Fintype O]

noncomputable def integerRowMassTent (K : ℝ) (z : O → ℤ) (x : O → ℝ) : ℝ :=
  ∏ i, integerMassTent K (z i) (x i)

noncomputable def integerRowMassInterpolation (K : ℝ) (p : PMF (O → ℤ)) (x : O → ℝ) : ℝ :=
  ∫ z, integerRowMassTent K z x ∂p.toMeasure

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {O : Type*} [Fintype O]

noncomputable def normalizedIntegerRowInterpolation (K : ℝ) (p : PMF (O → ℤ))
    (x : O → ℝ) : ℝ := integerRowMassInterpolation K p x / K ^ Fintype.card O

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineMeshRetention
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def affineParameterBadPair {J : Type*} [Fintype J]
    (D Q r : ℕ) (a x y : J → ℤ) : Prop :=
  Q < (BohrLattice.Primitive.content
    (fun j => (a j + (D : ℤ) * y j) - (a j + (D : ℤ) * x j))).natAbs ∨
    ∀ j, |y j - x j| ≤ (r : ℤ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformBoxResidueMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def affinePairModulus {J : Type*} [Fintype J] (t u : J → ℤ) : ℕ :=
  (BohrLattice.Primitive.content (fun j => u j - t j)).natAbs

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastModularCutoff
namespace OAI

section

namespace Erdos3

noncomputable def forecastJointGridMesh (d : ℕ) (P E : ℝ) : ℝ :=
  Real.exp (-forecastJointGridMeshLog d P E)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedCubeIntegerSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def integerBooleanBlockValue {G I : Type*} [Fintype G] [Fintype I] [DecidableEq I]
    (x : G → Option I → ℤ) (t : Finset I) : ℤ :=
  ∏ g, ∑ r, (booleanFeature r t : ℤ) * x g r

noncomputable def integerBooleanBlockJet {G I : Type*} [Fintype G] [Fintype I] [DecidableEq I]
    (x : G → Option I → ℤ) (S : Finset I) : ℤ :=
  booleanCoefficient (integerBooleanBlockValue x) S

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedSupportPlateau
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {J : Type*} [Fintype J]

noncomputable def normalizedSupportPlateau (H : ℝ) (x : J → ℝ) : ℝ :=
  linearCutoff H (1 / 4) ‖x‖

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PlateauFourierMode
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {J : Type*} [Fintype J]

noncomputable def rationalGridPhase (D : ℕ) [NeZero D] (a : J → ℤ) (r : J → ZMod D) : ℂ :=
  CircleFourier.character (ZMod.toAddCircle (∑ j, (a j : ZMod D) * r j))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedLatticeSheet
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ E]

instance euclideanDualLattice_isZLattice (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] : IsZLattice ℝ (euclideanDualLattice Λ) := by
  constructor
  rw [euclideanDualLattice_eq_span_dualBasis Λ]
  exact IsZLattice.span_top (K := ℝ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductMeanPullback
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]

omit [Fintype ι] [∀ i, Fintype (X i)] in
theorem productFiberIndicator_subtype (I : Finset ι) (a : ∀ i : I, X i)
    (base x : ∀ i, X i) :
    productFiberIndicator I (productSubtypePoint I a base) x =
      if (fun i : I => x i) = a then 1 else 0 := by
  have he : (∀ i ∈ I, x i = productSubtypePoint I a base i) ↔
      (fun i : I => x i) = a := by
    constructor
    · intro h
      funext i
      exact (h i i.property).trans (productSubtypePoint_apply_mem I a base i)
    · intro h i hi
      exact (congrFun h ⟨i, hi⟩).trans (productSubtypePoint_apply_mem I a base ⟨i, hi⟩).symm
  simp only [productFiberIndicator, he]

omit [Fintype ι] in
theorem productFiberIndicator_sum_subtype (I : Finset ι) (base x : ∀ i, X i) :
    (∑ a : ∀ i : I, X i, productFiberIndicator I (productSubtypePoint I a base) x) = 1 := by
  simp [productFiberIndicator_subtype]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalScalarSourceEnvelope
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

noncomputable def scalarSourceTransitionBound : ℝ≥0 :=
  Classical.choose exists_smoothTransition_lipschitz

theorem scalarSourceTransitionBound_spec :
    1 ≤ scalarSourceTransitionBound ∧
      LipschitzWith scalarSourceTransitionBound Real.smoothTransition :=
  Classical.choose_spec exists_smoothTransition_lipschitz

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CommonPolynomialScale
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def integerPolynomialInitialScale (ε : ℝ) : ℕ :=
  max 1 ⌈8 * (probabilityProfileLipschitz : ℝ) / ε⌉₊

theorem integerPolynomialInitialScale_width {ε : ℝ} (hε : 0 < ε) :
    8 * (probabilityProfileLipschitz : ℝ) ≤ ε * integerPolynomialInitialScale ε := by
  have hb : 8 * (probabilityProfileLipschitz : ℝ) / ε ≤ (integerPolynomialInitialScale ε : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈8 * (probabilityProfileLipschitz : ℝ) / ε⌉₊))
  have hm := (div_le_iff₀ hε).mp hb
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def commonPolynomialGapRatio {I : Type*} [Fintype I] (γ : I → ℝ) : ℕ :=
  max 1 (Finset.univ.sup (fun i => principalSamplingGapRatio (γ i)))

theorem commonPolynomialGapRatio_one_le {I : Type*} [Fintype I] (γ : I → ℝ) :
    1 ≤ commonPolynomialGapRatio γ := le_max_left _ _

theorem commonPolynomialGapRatio_le {I : Type*} [Fintype I] (γ : I → ℝ) (i : I) :
    principalSamplingGapRatio (γ i) ≤ commonPolynomialGapRatio γ := by
  classical
  exact (Finset.le_sup (f := fun i => principalSamplingGapRatio (γ i)) (Finset.mem_univ i)).trans
    (le_max_right _ _)

noncomputable def commonPolynomialInitialScale {J : Type*} [Fintype J]
    (L₀ : ℕ) (ε : J → ℝ) : ℕ :=
  max L₀ (max 1 (Finset.univ.sup (fun j => integerPolynomialInitialScale (ε j))))

theorem commonPolynomialInitialScale_pos {J : Type*} [Fintype J] (L₀ : ℕ) (ε : J → ℝ) :
    0 < commonPolynomialInitialScale L₀ ε :=
  Nat.zero_lt_one.trans_le ((le_max_left _ _).trans (le_max_right _ _))

theorem commonPolynomialInitialScale_le {J : Type*} [Fintype J]
    (L₀ : ℕ) (ε : J → ℝ) (j : J) :
    integerPolynomialInitialScale (ε j) ≤ commonPolynomialInitialScale L₀ ε := by
  classical
  exact (Finset.le_sup (f := fun j => integerPolynomialInitialScale (ε j)) (Finset.mem_univ j)).trans
    ((le_max_right _ _).trans (le_max_right _ _))

theorem exists_common_polynomial_scale {I J : Type*} [Fintype I] [Fintype J]
    (K h : I → ℕ) (γ : I → ℝ) (ε : J → ℝ) (hε : ∀ j, 0 < ε j) (L₀ : ℕ) :
    ∃ L : ℕ, 0 < L ∧ L₀ ≤ L ∧
      L ≤ commonPolynomialInitialScale L₀ ε * commonPolynomialGapRatio γ ^ Fintype.card I ∧
      (∀ j, 8 * (probabilityProfileLipschitz : ℝ) ≤ ε j * L) ∧
      ∀ i, L ^ h i < K i → (principalSamplingGapRatio (γ i) * L) ^ h i ≤ K i := by
  obtain ⟨L, hL, hlo, hhi, hgap⟩ := exists_integer_coefficient_scale_gap
    (fun i => (K i : ℝ)) h (commonPolynomialInitialScale L₀ ε) (commonPolynomialGapRatio γ)
    (commonPolynomialInitialScale_pos L₀ ε) (commonPolynomialGapRatio_one_le γ)
  refine ⟨L, hL, (le_max_left _ _).trans hlo, hhi, ?_, ?_⟩
  · intro j
    apply (integerPolynomialInitialScale_width (hε j)).trans
    apply mul_le_mul_of_nonneg_left _ (hε j).le
    exact_mod_cast (commonPolynomialInitialScale_le L₀ ε j).trans hlo
  · intro i hi
    have hb : (commonPolynomialGapRatio γ * L) ^ h i ≤ K i := by
      have hg := hgap i (by exact_mod_cast hi)
      exact_mod_cast hg
    exact (Nat.pow_le_pow_left (Nat.mul_le_mul_right L (commonPolynomialGapRatio_le γ i)) (h i)).trans hb

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

variable {E I Z O : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable [Fintype I] [Fintype Z] (o : OrthonormalBasis I ℝ E)

noncomputable def orthonormalArrayChart :
    ((I → O → ℝ) × (Z → O → ℤ)) ≃ᵐ (O → E × (Z → ℤ)) :=
  (mixedArrayRegroup I Z O).trans
    (MeasurableEquiv.piCongrRight (fun _ : O => orthonormalMixedChart (J := Z) o))

variable [Fintype O]

noncomputable def arrayResidueChart {R : Type*} [MeasurableSpace R] :
    (((I → O → ℝ) × (Z → O → ℤ)) × (O → R)) ≃ᵐ (O → (E × (Z → ℤ)) × R) :=
  ((orthonormalArrayChart o).prodCongr (MeasurableEquiv.refl _)).trans
    (MeasurableEquiv.arrowProdEquivProdArrow (E × (Z → ℤ)) R O).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.LayerSamplerWitnessScale
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

noncomputable def layerSamplerScaleBound (R σ : Fin m → ℝ) (L₀ : ℕ) : ℕ :=
  commonPolynomialInitialScale L₀ (layerSamplerTailWidth (G := G) B R σ) *
    commonPolynomialGapRatio (layerSamplerGapWidth (G := G) B R) ^ Fintype.card (Σ j, Fin (n j))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial
open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

noncomputable def layerSamplerWitnessScaleBound (R σ : Fin m → ℝ) (L₀ : ℕ) (W : ℝ) : ℕ :=
  commonPolynomialInitialScale L₀ (layerSamplerTailWidth (G := G) B R σ) *
    commonPolynomialGapRatio (fun a => layerSamplerGapWidth (G := G) B R a / W) ^
      Fintype.card (Σ j, Fin (n j))

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.BooleanCanonicalLogBudget
namespace OAI

section

namespace Erdos3

def productMinorInverseLog (j q h : ℕ) (P E : ℝ) : ℝ :=
  j+(j : ℝ)^2+(j-1 : ℕ)*productMinorEntryLog q h P+E
def productMinorDeterminantLog (n j q h : ℕ) (P : ℝ) : ℝ :=
  n+(j : ℝ)^2+j+productMinorPartialLog q h P+j*(productMinorEntryLog q h P+1)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {D α : Type*} [Fintype D] [Fintype α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

noncomputable def jointBooleanDerivativeBudget (h : D → ℕ) (C : D → ℝ) : ℝ≥0 :=
  ∑ d, Real.toNNReal (productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
    (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def jointBooleanDerivativeLog {D α : Type*} [Fintype D] [Fintype α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] (h : D → ℕ) (P : ℝ) : ℝ :=
  Fintype.card D+∑ d, productMinorDerivativeLog (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
    (Fintype.card (O d)) (Fintype.card α) (h d) P

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.JointBooleanWeightBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

variable {D α : Type*} [Fintype D] [Fintype α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

noncomputable def jointBooleanWeightBudget (h : D → ℕ) (C : D → ℝ) (A T : ℝ≥0)
    (r : ∀ d, B d × Fin (h d) → ℝ) (κ : D → ℝ) : ℝ :=
  ∑ d, ((∑ i, ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) *
    ((Fintype.card α : ℝ) + 1) ^ 2 * T / r d i) +
    (Fintype.card (BlockParameter (B d) (Fin (h d)) α) : ℝ) * ((A : ℝ) / κ d *
      productMinorDeterminantDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
        (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SlicedPrincipalInverse
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff BigOperators

variable {B F : Type*} [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F]

noncomputable def principalSliceSingleton (c : B → ℝ) (lower width : B × F → ℝ)
    (x : B × F → ℝ) : Unit → ℝ := fun _ => principalSliceValue c lower width x

section Joint

variable {D : Type*} [Fintype D]
variable {B F : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
variable [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]

noncomputable def jointSlicedPrincipal (c : ∀ d, B d → ℝ)
    (lower width : ∀ d, B d × F d → ℝ) :=
  sigmaAxisSampler (fun d => principalSliceSingleton (c d) (lower d) (width d))

end Joint

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CoefficientJetDensityFactors
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Matrix

variable {I Z O J : Type*} [Fintype I] [Fintype Z]
variable [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]
variable (A : Matrix O J ℤ) (s : O ↪ J) (hA : (A.submatrix id s).det ≠ 0)

noncomputable def integerMatrixImagePMF (p : J → PMF ℤ) : PMF (O → ℤ) :=
  (independentProductPMF p).map (fun z => A *ᵥ z)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineKernelEndpointGeometry
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal Classical
variable {G : Type*} [Fintype G]

noncomputable def affineKernelDiscretePoint (lower : G → ℝ) (step S : ℝ) {H : G → ℕ}
    (z : ∀ g, IntegerScalarCubeBox Empty (H g)) : G → ℝ :=
  fun g => (lower g + step * (z g none : ℝ)) / S

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBoxObservedMean
namespace OAI

section

namespace Erdos3

def integerBaseTranslation {K I : Type*} (b : I → ℤ) : Option K × I → ℤ :=
  baseArrayJoin 0 b

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnconditionedSpatialWidthBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem spatial_scale_of_exp_size {P τ H q : ℝ} (hP : 0 ≤ P) (hτ : 0 < τ)
    (hτP : τ⁻¹ ≤ Real.exp P) (hq0 : 0 ≤ q) (hq : q ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hH : Real.exp (5*P+128) ≤ H) :
    64*(probabilityProfileLipschitz : ℝ)*q*(1+Real.exp (2*P)) ≤ τ*H := by
  have h1 : 1+Real.exp (2*P) ≤ 2*Real.exp (2*P) := by
    have := Real.one_le_exp_iff.mpr (show 0 ≤ 2*P by positivity)
    linarith
  have h128 : (128 : ℝ) ≤ Real.exp 128 := by linarith [Real.add_one_le_exp (128 : ℝ)]
  have hexp : Real.exp P*Real.exp P*Real.exp (2*P)*Real.exp P = Real.exp (5*P) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [mul_comm τ H]
  apply (div_le_iff₀ hτ).mp
  calc
    _ = 64*(probabilityProfileLipschitz : ℝ)*q*(1+Real.exp (2*P))*τ⁻¹ := div_eq_mul_inv _ _
    _ ≤ 64*Real.exp P*Real.exp P*(2*Real.exp (2*P))*Real.exp P := by
      gcongr
    _ = 128*Real.exp (5*P) := by rw [show
        64*Real.exp P*Real.exp P*(2*Real.exp (2*P))*Real.exp P =
          128*(Real.exp P*Real.exp P*Real.exp (2*P)*Real.exp P) by ring, hexp]
    _ ≤ Real.exp 128*Real.exp (5*P) := mul_le_mul_of_nonneg_right h128 (by positivity)
    _ = Real.exp (5*P+128) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ H := hH

end Erdos3

end

section

namespace Erdos3

theorem trimmedSpatialWidths_scale {K I : Type*} {B τ : ℝ} (hB : 0 ≤ B)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i) (N : I → ℕ)
    (hsize : ∀ i, 64*(probabilityProfileLipschitz : ℝ)*(modulus i : ℝ)*(1+B) ≤ τ*(N i : ℝ))
    (z : Option K × I) :
    8*(probabilityProfileLipschitz : ℝ) ≤
      residueProfileWidth modulus (trimmedSpatialWidths B τ N) z := by
  rcases z with ⟨k,i⟩
  have hm : (0 : ℝ) < modulus i := by exact_mod_cast hmodulus i
  change 8*(probabilityProfileLipschitz : ℝ) ≤ trimmedSpatialWidths B τ N (k,i)/(modulus i : ℝ)
  apply (le_div_iff₀ hm).mpr
  cases k with
  | none =>
    change _ ≤ τ*((N i : ℝ)/8)
    have hl : 64*(probabilityProfileLipschitz : ℝ)*(modulus i : ℝ) ≤
        64*(probabilityProfileLipschitz : ℝ)*(modulus i : ℝ)*(1+B) := by
      apply le_mul_of_one_le_right (by positivity)
      linarith
    nlinarith [hsize i]
  | some k =>
    change _ ≤ τ*(1*(N i : ℝ)/(8*(1+B)))
    rw [one_mul, ← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : (0 : ℝ)<8*(1+B))).mpr
    nlinarith [hsize i]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StrideSelectedResidueBadProduct
namespace OAI

section

namespace Erdos3

theorem quantitativeBadPrimeRadius_bounds {E : ℝ} (hE : 0 ≤ E) :
    0 < quantitativeBadPrimeRadius E ∧
      (quantitativeBadPrimeRadius E : ℝ) ≤ Real.exp (E + 3) ∧
      2 / (9 * (quantitativeBadPrimeRadius E : ℝ) ^ 9) ≤ Real.exp (-E) / 2 := by
  let R := quantitativeBadPrimeRadius E
  have hR : 0 < R := Nat.succ_pos _
  have hexp : 1 ≤ Real.exp E := Real.one_le_exp hE
  have hlo : 4 * Real.exp E ≤ (R : ℝ) := by
    have hc := Nat.le_ceil (4 * Real.exp E)
    dsimp [R, quantitativeBadPrimeRadius]
    push_cast
    linarith
  have hhi : (R : ℝ) ≤ 4 * Real.exp E + 2 := by
    have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ 4 * Real.exp E)
    dsimp [R, quantitativeBadPrimeRadius]
    push_cast
    linarith
  have hexp3 : (6 : ℝ) ≤ Real.exp 3 := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have h2 : (4 : ℝ) ≤ Real.exp 1 * Real.exp 1 := by nlinarith
    have h3 : (8 : ℝ) ≤ Real.exp 1 * Real.exp 1 * Real.exp 1 := by nlinarith
    have he : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      norm_num
    rw [he]
    linarith
  have hbudget : (R : ℝ) ≤ Real.exp (E + 3) := by
    rw [Real.exp_add]
    have := mul_le_mul_of_nonneg_left hexp3 (Real.exp_pos E).le
    nlinarith
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hRp : (R : ℝ) ≤ (R : ℝ) ^ 9 := by
    calc
      _ = (R : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hR1 (by omega)
  have hprod : 4 ≤ Real.exp (-E) * (R : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hlo (Real.exp_pos (-E)).le
    have he : Real.exp (-E) * Real.exp E = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have htail : 2 / (9 * (R : ℝ) ^ 9) ≤ Real.exp (-E) / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 9 * (R : ℝ) ^ 9)).mpr
    have hh := mul_le_mul_of_nonneg_left hRp (Real.exp_pos (-E)).le
    nlinarith
  exact ⟨hR, hbudget, htail⟩

theorem quantitativeBadPrimeRadius_witness_budget {E V : ℝ}
    (hE : 0 ≤ E) (hV : 0 ≤ V) (Q : ℕ) (hQ : (Q : ℝ) ≤ Real.exp V) :
    let R := quantitativeBadPrimeRadius E
    (max Q (R ^ 2) : ℕ) ≤ Real.exp (V + 2 * E + 6) ∧
    1 / (Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2))) ≤
      Real.exp (V + 3 * E + 8) := by
  dsimp only
  let R := quantitativeBadPrimeRadius E
  have hR := (quantitativeBadPrimeRadius_bounds hE).2.1
  have hR2 : (R : ℝ) ^ 2 ≤ Real.exp (2 * E + 6) := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ R) hR 2
    have he : (Real.exp (E + 3)) ^ 2 = Real.exp (2 * E + 6) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    exact hh.trans_eq he
  have hQbig : (Q : ℝ) ≤ Real.exp (V + 2 * E + 6) :=
    hQ.trans (Real.exp_le_exp.mpr (by linarith))
  have hRbig : (R : ℝ) ^ 2 ≤ Real.exp (V + 2 * E + 6) :=
    hR2.trans (Real.exp_le_exp.mpr (by linarith))
  constructor
  · rw [Nat.cast_max, Nat.cast_pow]
    exact max_le hQbig hRbig
  · have hne : Real.exp (-E) ≠ 0 := ne_of_gt (Real.exp_pos _)
    have hrec : 1 / (Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2))) =
        2 * ((Q : ℝ) + (R : ℝ) ^ 2) * Real.exp E := by
      rw [one_div_div, Real.exp_neg, div_inv_eq_mul]
    rw [hrec]
    have h4 : (4 : ℝ) ≤ Real.exp 2 := by
      have h1 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      rw [he]
      nlinarith
    calc
      _ ≤ 4 * Real.exp (V + 2 * E + 6) * Real.exp E := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos E).le
        linarith
      _ ≤ Real.exp 2 * Real.exp (V + 2 * E + 6) * Real.exp E := by
        gcongr
      _ = Real.exp (V + 3 * E + 8) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueIntervalFactors
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def residueIntervalSiteWeight (B r H : ℝ) {m : ℕ}
    (a : ZMod m) (k : Fin (intervalSiteCount B r)) (u : ℤ) : ℝ :=
  residueSiteIndicator a u * intervalSiteWeight B r k ((u : ℝ) / H)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MaskedIntervalApproximation
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

noncomputable def maskedIntervalApprox {S : Type*} [Fintype S] [DecidableEq S]
    (B r H : ℝ) (m : ℕ) [NeZero m]
    (F : (S → ℝ) → ℂ) (M : (S → ZMod m) → ℂ) (u : S → ℤ) : ℂ :=
  ∑ a : S → ZMod m, ∑ k : S → Fin (intervalSiteCount B r),
    (M a * F (fun i => intervalSiteCenter B r (k i))) *
      ((∏ i, residueIntervalSiteWeight B r H (a i) (k i) (u i) : ℝ) : ℂ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialSiteShift
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

noncomputable def spatialStarDensity {I : Type*} (f : ((Unit ⊕ I) → ℝ) → ℝ)
    (y : (Unit ⊕ I) → ℝ) : ℂ := f (spatialUnstar y)

noncomputable def spatialSiteApprox {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m] (f : ((Unit ⊕ I) → ℝ) → ℝ) (H b r : ℝ)
    (v : (Unit ⊕ I) → ℤ) : ℂ :=
  maskedIntervalApprox b r H m (spatialStarDensity f) (latticeStarMask (pivotFullImage A B) m)
    (spatialStar v)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def spatialSiteCoefficient {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) (f : ((Unit ⊕ I) → ℝ) → ℝ) (b r : ℝ) (t : SpatialSiteLabel I m b r) : ℂ :=
  latticeStarMask (pivotFullImage A B) m t.1 *
    spatialStarDensity f (fun i => intervalSiteCenter b r (t.2 i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SmoothSpatialCostBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def smoothSpatialDiscretizationCost {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) (M L : ℕ) : ℝ :=
  (normalizedFiberErrorConstant (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s ⊕ N))
    (scalarSpatialIndexAllowance I M) (scalarSpatialInverseAllowance I M)
    (Fintype.card (UnselectedColumn s ⊕ N)) 1 1
    ((Fintype.card (UnselectedColumn s ⊕ N)+Fintype.card (Unit ⊕ I))*probabilityProfileLipschitz) *
      (Fintype.card (Unit ⊕ I)).factorial) * (L : ℝ)^Fintype.card (Unit ⊕ I)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PrincipalSpatialSiteComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

def principalSpatialResidueColumns {D α N : Type*} {B : D → Type*} {h : D → ℕ}
    (m : ℕ) (c : N → ℤ) (index : N → PrincipalTupleIndex B h)
    (r : PrincipalTupleIndex B h → Option α → ZMod m) : Matrix (Unit ⊕ α) N (ZMod m) :=
  fun i n => Sum.elim (fun _ => (c n : ZMod m)+r (index n) none)
    (fun j => r (index n) (some j)) i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFixedKernelReplacement
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem allocatedKernelLog_bounds (G α : Type*) [Fintype G] [Fintype α]
    {m : ℕ} (O : Fin m → Type*) [∀ j, Fintype (O j)] {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ allocatedKernelLog G α O P ∧ P ≤ allocatedKernelLog G α O P ∧
    (m*2^(m+1) : ℕ)*P ≤ allocatedKernelLog G α O P ∧
    (Fintype.card α : ℝ)*(m+1) ≤ allocatedKernelLog G α O P ∧
    ∀ j, kernelInverseLog (Fintype.card α) (Fintype.card G) (Fintype.card (O j)) (j.val+1) P ≤
      allocatedKernelLog G α O P := by
  have hi (j : Fin m) : 0 ≤ kernelInverseLog
      (Fintype.card α) (Fintype.card G) (Fintype.card (O j)) (j.val+1) P := by
    unfold kernelInverseLog
    positivity
  have hs := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hi j)
  have hidx : 0 ≤ (m*2^(m+1) : ℕ)*(P : ℝ) := by positivity
  have hentry : 0 ≤ (Fintype.card α : ℝ)*(m+1) := by positivity
  unfold allocatedKernelLog
  refine ⟨by positivity, by linarith, by linarith, by linarith, ?_⟩
  intro j
  have hj := Finset.single_le_sum (fun k _ => hi k) (Finset.mem_univ j)
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularProductivityPrecision
namespace OAI

section

namespace Erdos3

theorem preparedModularProductivity_precision {Pprod Pphysical gainLog gain : ℝ}
    (d : ℕ) (hg : 0 ≤ gainLog)
    (hprod : gainLog + 8 ≤ Pprod)
    (hphysical : gainLog + (d : ℝ) + 8 ≤ Pphysical)
    (hgain : Real.exp (-gainLog) ≤ gain) :
    Real.exp (-Pprod) ≤ gain / 16 ∧
      12 * positiveProjectionAccuracy Pprod +
        2 * (d : ℝ) * Real.exp (-Pphysical) ≤ gain / 8 := by
  have he : 0 < Real.exp (-gainLog) := Real.exp_pos _
  have hshift : Real.exp (-(gainLog + 8)) ≤ Real.exp (-gainLog) / 256 := by
    rw [neg_add, Real.exp_add, Real.exp_neg (8 : ℝ), ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left he.le (by norm_num) productivity_exp_eight
  have hprodExp : Real.exp (-Pprod) ≤ Real.exp (-gainLog) / 256 :=
    (Real.exp_le_exp.mpr (neg_le_neg hprod)).trans hshift
  have haccuracy : positiveProjectionAccuracy Pprod ≤ Real.exp (-Pprod) := by
    apply Real.exp_le_exp.mpr
    linarith only [hg, hprod]
  have hd : (d : ℝ) ≤ Real.exp d := by linarith [Real.add_one_le_exp (d : ℝ)]
  have hspatial : (d : ℝ) * Real.exp (-Pphysical) ≤ Real.exp (-gainLog) / 256 := by
    calc
      _ ≤ Real.exp d * Real.exp (-(gainLog + (d : ℝ) + 8)) :=
        mul_le_mul hd (Real.exp_le_exp.mpr (neg_le_neg hphysical))
          (Real.exp_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (-(gainLog + 8)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := hshift
  constructor
  · linarith
  · linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MixedCoveredIntegerReconstruction
namespace OAI

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

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.MixedCoveredDensityMass
namespace OAI

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
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩm : ∀ j t, MeasurableSet (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

noncomputable def mixedCoveredJetRawReference : Measure (MixedCoveredJetSource I O E n d) :=
  (Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))).prod
    (PMF.uniformOfFintype (∀ j, O j → E j → ZMod d)).toMeasure

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AnisotropicSpatialLaw
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel

theorem anisotropicSpatialScale_physicalPivot {I J : Type*} (s : I ↪ J) (A R : ℝ) :
    (fun i => physicalSpatialInputScale J A R (physicalCubePivotIndex s i)) =
      anisotropicSpatialScale I A R := by
  funext i
  cases i <;> rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AnisotropicGoodKernelComparison
namespace OAI

section

namespace Erdos3

open MeasureTheory BooleanCubeKernel
open scoped BigOperators NNReal

noncomputable def anisotropicSpatialMeshThreshold {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (N : Type*) [Fintype N] (C : ℝ) : ℝ :=
  2 * (1 + 4 ^ (Fintype.card (Unit ⊕ I) + Fintype.card (UnselectedColumn s ⊕ N)) *
    ((Fintype.card (UnselectedColumn s ⊕ N) + Fintype.card (Unit ⊕ I) : ℝ) * probabilityProfileLipschitz)) *
      anisotropicSpatialDetAllowance I C

noncomputable def anisotropicSpatialError {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (N : Type*) [Fintype N] (B : ℕ) (κ C ρ ξ : ℝ) : ℝ :=
  normalizedFiberErrorConstant (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s ⊕ N))
    ((B : ℝ) ^ (Fintype.card I + 1)) (physicalSpatialInverseBound I κ)
    (Fintype.card (UnselectedColumn s ⊕ N)) 1 1
    ((Fintype.card (UnselectedColumn s ⊕ N) + Fintype.card (Unit ⊕ I)) * probabilityProfileLipschitz) *
      anisotropicSpatialDetAllowance I C / ρ +
  (B : ℝ) ^ (Fintype.card I + 1) *
    (spatialKernelErrorConstant (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s))
      (physicalSpatialInverseBound I κ) 1
      ((Fintype.card (UnselectedColumn s) + Fintype.card (Unit ⊕ I)) * probabilityProfileLipschitz) *
        (Fintype.card N * ξ))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineModeratePlateauModel
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {A J : Type*} [Fintype A] [Fintype J]
variable (D : A → ℕ) [∀ a, NeZero (D a)] (frequency : A → J → ℤ)
variable (coefficient : A → ℂ) (mode : A → (J → ℝ) → ℂ)

noncomputable def finiteResidueModeModel (residue : ∀ a, J → ZMod (D a)) (x : J → ℝ) : ℂ :=
  ∑ a, coefficient a * (star (rationalGridPhase (D a) (frequency a) (residue a)) * mode a x)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CRTIntegerRepresentative
namespace OAI

section

namespace Erdos3

open scoped BigOperators
open _root_.MvPolynomial

variable {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
  [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))

noncomputable def crtIntegerRepresentative (u : J → ℤ) : ℤ :=
  ∑ j, crtIntegerCoefficient N hN j * u j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelScalarEnvelope
namespace OAI

section

namespace Erdos3

theorem kernelInverseLog_le_envelope {q n j d : ℕ} {D p : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hq : (q : ℝ) ≤ D) (hn : (n : ℝ) ≤ D)
    (hj : (j : ℝ) ≤ D) (hd : (d : ℝ) ≤ D) :
    kernelInverseLog q n j d p ≤ kernelInverseEnvelope D p := by
  have hj' : ((j-1 : ℕ) : ℝ) ≤ D := (Nat.cast_le.mpr (Nat.sub_le j 1)).trans hj
  unfold kernelInverseLog kernelInverseEnvelope
  gcongr

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AnisotropicTupleErrorChoice
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

noncomputable def anisotropicSpatialDiscretizationCost {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) (M : ℕ) (C : ℝ) : ℝ :=
  smoothSpatialDiscretizationCost N s M 1 * C ^ Fintype.card (Unit ⊕ I)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CyclicProductBudget
namespace OAI

section

namespace Erdos3

def cyclicProductInputBudget (p : ℝ) : ℝ := productNiltestBudget p + 3 * p + 17

def cyclicProductCutoffBudget (s c : ℕ) (p : ℝ) : ℝ :=
  ((s + 3) ^ (s + 3) : ℕ) + (s + 3 : ℕ) * cyclicProductVolumeBudget p +
    (2 ^ (s + 2) : ℕ) * (cyclicProductInputBudget p + c) ^ c

def cyclicProductDetectionBudget (s c : ℕ) (p : ℝ) : ℝ :=
  (2 ^ (s + 2) + 1 : ℕ) * (cyclicProductCutoffBudget s c p + 1) + 4

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastJointScaleNormalization
namespace OAI

section

namespace Erdos3

noncomputable def forecastJointGridAmbientLog (d : ℕ) (P E Q Pτ : ℝ) : ℝ :=
  Q + (P + E + 5) + Pτ + forecastJointGridMeshLog d P E + 3

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PhysicalBadProductErrorBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def physicalBadProductGap (N : ℕ) (E Vlog : ℝ) (Q : ℕ) : ℝ :=
  (2 * (N : ℝ) + 1) * (max Q ((quantitativeBadPrimeRadius E) ^ 2) : ℕ) /
    physicalBadProductAccuracy E Vlog

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CanonicalZeroSpatialDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory BooleanCubeKernel
open scoped Matrix NNReal BigOperators

variable {I J X : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype X]
variable (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

noncomputable def canonicalSpatialKernelMap
    (p : (UnselectedColumn s → ℝ) × ((Unit ⊕ I) → ℝ)) : (Unit ⊕ I) → ℝ :=
  normalizedIntegerPivot (selectedSpatialPivot root D s)
      (anisotropicSpatialScale I (1 + W) 1) (physicalSpatialOutputScale I (1 + W) 1 L) *ᵥ p.2 +
    normalizedIntegerColumns (selectedSpatialFreeColumns root D s) (fun _ => 1)
      (physicalSpatialOutputScale I (1 + W) 1 L) *ᵥ p.1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SelectedDependentMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] (s : I ↪ J)
variable (X : J → Type*) [∀ j, MeasurableSpace (X j)]

noncomputable def selectedDependentEquiv :
    ((∀ j : UnselectedColumn s, X j.val) × (∀ i, X (s i))) ≃ᵐ (∀ j, X j) :=
  (MeasurableEquiv.sumPiEquivProdPi
    (fun j : UnselectedColumn s ⊕ I => X (selectedFreeFirstEquiv s j))).symm.trans
      (MeasurableEquiv.piCongrLeft X (selectedFreeFirstEquiv s))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedCoveredSiteExtraction
namespace OAI

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

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedFullSiteSupport
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped NNReal

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

def singleSiteFromLayered (v : (Σ j, J j) → ℝ) :
    JetAmbientIndex (fun _ : Fin m => Unit) J → ℝ := fun a => v ⟨a.1, a.2.2⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativePhysicalHaarExpansion
namespace OAI

section

namespace Erdos3
open scoped NNReal

namespace VectorPolynomial
variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

noncomputable def physicalFactorCoverMap (period gridPeriod : ℕ)
    (z : (Σ j, J j) → UnitAddCircle) :
    (((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle)) ×
      ((Σ j, J j) → UnitAddCircle)) :=
  ((fun a => (period * gridPeriod) • z ⟨a.1, a.2.2⟩, fun a => gridPeriod • z a),
    fun a => period • z a)

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CanonicalZeroSpatialInputLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {X Zsp : Type*} [Fintype X] [Fintype Zsp] [DecidableEq Zsp]
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ) (W L : ℝ)

noncomputable def canonicalZeroSpatialInputMap
    (u : Option Zsp × X → ℝ) (a : Σ _ : X, Unit ⊕ Empty) : ℝ :=
  canonicalSpatialKernelMap s root D (W := W) (L := L)
    ((fun j => u (some j.val, a.1)),
      (fun i => match i with | .inl _ => u (none, a.1) | .inr e => Empty.elim e)) a.2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialInputAffineLaw
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

noncomputable def crtInputAddEquiv (q : L → ℕ)
    (hq : Pairwise (fun l k => (q l).Coprime (q k))) :
    (∀ l, V → ZMod (q l)) ≃+ (V → ZMod (∏ l, q l)) where
  toFun := crtInput q hq
  invFun x l v := ZMod.prodEquivPi q hq (x v) l
  left_inv x := by
    funext l v
    exact congrFun ((ZMod.prodEquivPi q hq).apply_symm_apply (fun k => x k v)) l
  right_inv x := by
    funext v
    exact (ZMod.prodEquivPi q hq).symm_apply_apply (x v)
  map_add' x y := by
    funext v
    exact map_add (ZMod.prodEquivPi q hq).symm (fun l => x l v) (fun l => y l v)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget
namespace OAI

section

namespace Erdos3

theorem uniformProductAccuracyLog_mono {D T E D' T' E' : ℝ}
    (hD0 : 0 ≤ D) (hT0 : 0 ≤ T)
    (hD : D ≤ D') (hT : T ≤ T') (hE : E ≤ E') :
    uniformProductAccuracyLog D T E ≤ uniformProductAccuracyLog D' T' E' := by
  have hD'0 : 0 ≤ D' := hD0.trans hD
  unfold uniformProductAccuracyLog
  gcongr

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedEarlySpatialWidth
namespace OAI

section

namespace Erdos3

theorem preparedEarlySpatialWidth (d : ℕ) {gainLog : ℝ} (hg : 0 ≤ gainLog) :
    let Pτ := gainLog + (d : ℝ) + 8
    let τ := Real.exp (-Pτ)
    0 ≤ Pτ ∧ 0 < τ ∧ τ ≤ 1 / 2 ∧ (d : ℝ) * τ ≤ 1 / 2 ∧
      τ⁻¹ = Real.exp Pτ ∧
      (∀ Pmaster : ℝ, Pτ ≤ Pmaster → τ⁻¹ ≤ Real.exp Pmaster) ∧
      (∀ Pprod gain : ℝ, gainLog + 8 ≤ Pprod → Real.exp (-gainLog) ≤ gain →
        Real.exp (-Pprod) ≤ gain / 16 ∧
          12 * positiveProjectionAccuracy Pprod + 2 * (d : ℝ) * τ ≤ gain / 8) := by
  dsimp only
  have hnonneg : 0 ≤ gainLog + (d : ℝ) + 8 := by positivity
  have hexp : Real.exp (-gainLog) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hg)
  have hprecision := preparedModularProductivity_precision d hg
    (Pprod := gainLog + 8) (Pphysical := gainLog + (d : ℝ) + 8)
    (gain := Real.exp (-gainLog)) le_rfl le_rfl le_rfl
  have hτhalf : Real.exp (-(gainLog + (d : ℝ) + 8)) ≤ 1 / 2 := by
    calc
      _ ≤ Real.exp (-1 : ℝ) := Real.exp_le_exp.mpr (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
      _ ≤ 1 / 2 := by
        rw [Real.exp_neg, ← one_div]
        exact div_le_div_of_nonneg_left (by norm_num) (by norm_num)
          (by linarith [Real.add_one_le_exp (1 : ℝ)])
  have hτdim : (d : ℝ) * Real.exp (-(gainLog + (d : ℝ) + 8)) ≤ 1 / 2 := by
    have ha : 0 ≤ positiveProjectionAccuracy (gainLog + 8) := Real.exp_nonneg _
    linarith only [hprecision.2, hexp, ha]
  have hinv : (Real.exp (-(gainLog + (d : ℝ) + 8)))⁻¹ =
      Real.exp (gainLog + (d : ℝ) + 8) := by rw [Real.exp_neg, inv_inv]
  refine ⟨hnonneg, Real.exp_pos _, hτhalf, hτdim, hinv, ?_, ?_⟩
  · intro Pmaster hmaster
    rw [hinv]
    exact Real.exp_le_exp.mpr hmaster
  · intro Pprod gain hprod hgain
    exact preparedModularProductivity_precision d hg hprod le_rfl hgain

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CopiedLayerSpace
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

noncomputable def copiedLayerSpaceEquiv {J K : Type*}
    (W : Submodule ℝ (J → ℝ)) (V : Submodule ℝ (K → ℝ)) :
    copiedLayerSpace W V ≃ₗ[ℝ] W × V where
  toFun x := (⟨fun j => x.val (.inl j), x.property.1⟩, ⟨fun k => x.val (.inr k), x.property.2⟩)
  invFun x := ⟨Sum.elim x.1.val x.2.val, x.1.property, x.2.property⟩
  left_inv x := by ext j; cases j <;> rfl
  right_inv x := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankPreparationSizes
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct

def rankCutDirectionHeight (ambient columns rows H R : ℕ) : ℕ :=
  (columns + 1) *
    (H * rationalKernelHeight (rows + 1) ((ambient + 1) * (R * H) ^ ambient)) ^ columns

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedSpatialKernelBlocks
namespace OAI

section

namespace Erdos3

theorem modularInitialBlockCount_two_dimensions (m d : ℕ) :
    2 * d ≤ modularInitialBlockCount m d := by
  have ha : 1 ≤ 2 ^ (2 * m) * m.factorial := Nat.succ_le_of_lt (by positivity)
  have hb : 1 ≤ 2 ^ m := Nat.succ_le_of_lt (by positivity)
  have hr : d + 2 ≤ modularInitialRankStrength m d := by
    unfold modularInitialRankStrength
    nlinarith
  unfold modularInitialBlockCount
  nlinarith

namespace VectorPolynomial

def preparedSpatialKernelBlocks (m M nX : ℕ) :
    Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)) where
  toFun z := ⟨(m + 1) * (m + 3) + (finProdFinEquiv z).val, by
    have hz := (finProdFinEquiv z).isLt
    have hdim := modularInitialBlockCount_two_dimensions m (nX + m * M)
    have hmul : modularInitialBlockCount m (nX + m * M) ≤
        (m + 1) * modularInitialBlockCount m (nX + m * M) := by
      exact Nat.le_mul_of_pos_left _ (Nat.succ_pos m)
    omega⟩
  inj' := by
    intro z w h
    apply finProdFinEquiv.injective
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp only at hv
    omega

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankAffineFullWitness
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical
open FiniteProbabilityWeights

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

noncomputable local instance affineWitnessDeckIndexFintype :
    Fintype (AllocatedDeckRankCoefficientIndex E L) := inferInstance
noncomputable local instance affineWitnessDeckIndexDecidableEq :
    DecidableEq (AllocatedDeckRankCoefficientIndex E L) := Classical.decEq _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical
open FiniteProbabilityWeights
attribute [local irreducible] independentProductPMF

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

noncomputable local instance affineFullWitnessSelectedDeckFintype :
    Fintype (AllocatedDeckRankCoefficientIndex E L) := inferInstance

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastOriginalSampleUniformBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem forecastOriginalSmoothBudget_bounds (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    let Q := ((m : ℝ) + 2) * P + 4 * m + 8
    0 ≤ forecastOriginalSmoothBudget m P ∧
      P * (2 * P + 1) + P * (Q + 1) + 1 ≤ forecastOriginalSmoothBudget m P ∧
      2 * P * (2 * P + 1) + 2 * P * (Q + 1) + 2 * P + (4 * P + 2) +
        2 * Q + 2 ≤ forecastOriginalSmoothBudget m P := by
  intro Q
  refine ⟨?_, ?_, ?_⟩
  · unfold forecastOriginalSmoothBudget
    positivity
  · apply sub_nonneg.mp
    have he : forecastOriginalSmoothBudget m P -
        (P * (2 * P + 1) + P * (Q + 1) + 1) =
        (9 * (m : ℝ) + 26) * P ^ 2 + (16 * m + 50) * P + (10 * m + 29) := by
      unfold forecastOriginalSmoothBudget Q
      ring
    rw [he]
    positivity
  · apply sub_nonneg.mp
    have he : forecastOriginalSmoothBudget m P -
        (2 * P * (2 * P + 1) + 2 * P * (Q + 1) + 2 * P + (4 * P + 2) + 2 * Q + 2) =
        (8 * (m : ℝ) + 22) * P ^ 2 + (10 * m + 30) * P + (2 * m + 10) := by
      unfold forecastOriginalSmoothBudget Q
      ring
    rw [he]
    positivity

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualForecastModelPrecision
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace VectorPolynomial

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

noncomputable def forecastCoverCutoffInput (period : ℕ)
    (z : (Σ j, J j) → UnitAddCircle) :
    JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle :=
  fun a => period • z ⟨a.1, a.2.2⟩

end VectorPolynomial
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

variable {m : ℕ} (I E : Fin m → Type*) [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable (n : Fin m → ℕ) (N : ℕ) [NeZero N]

local notation "single" => (fun _ : Fin m => Unit)
local notation "RealAxis" => (Σ j, I j)
local notation "IntAxis" => (Σ j, Fin (n j))

noncomputable def forecastSingleMixedRawEquiv :
    MixedCoveredJetSource I single E n N ≃ᵐ
      (((RealAxis → ℝ) × (IntAxis → ℤ)) × (∀ j, Unit → E j → ZMod N)) where
  toFun z := ((fun a => (z.1 a.1).1 a.2 (), fun a => (z.1 a.1).2 a.2 ()), z.2)
  invFun p := (fun j => (fun i _ => p.1.1 ⟨j, i⟩, fun i _ => p.1.2 ⟨j, i⟩), p.2)
  left_inv z := by
    apply Prod.ext
    · funext j
      apply Prod.ext <;> funext i t <;> cases t <;> rfl
    · rfl
  right_inv p := rfl
  measurable_toFun := by
    change Measurable (fun z : MixedCoveredJetSource I single E n N =>
      ((fun a : RealAxis => (z.1 a.1).1 a.2 (),
        fun a : IntAxis => (z.1 a.1).2 a.2 ()), z.2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : ((RealAxis → ℝ) × (IntAxis → ℤ)) × (∀ j, Unit → E j → ZMod N) =>
      (fun j => (fun i (_ : Unit) => p.1.1 ⟨j, i⟩,
        fun i (_ : Unit) => p.1.2 ⟨j, i⟩), p.2))
    fun_prop

noncomputable def forecastSingleMixedRawPoint (v : RealAxis → ℝ) (k : IntAxis → ℤ)
    (deck : (∀ j, Unit → E j → ZMod N)) : MixedCoveredJetSource I single E n N :=
  (fun j => (fun i _ => v ⟨j, i⟩, fun i _ => k ⟨j, i⟩), deck)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} (E : Fin m → Type*) (N : ℕ)

attribute [local instance] OAI.Erdos3.VectorPolynomial.instDecidableEqUnit
def forecastSingleDeckEquiv :
    ForecastSingleDeckResidues E N ≃ ((Σ j, E j) → ZMod N) where
  toFun deck a := deck a.1 () a.2
  invFun r j _ e := r ⟨j, e⟩
  left_inv deck := by funext j u e; cases u; rfl
  right_inv r := rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ForecastOriginalSampleResidueFactor
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal BigOperators

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (P : LayerSamplerAxis I n → Prop)
variable {A Y Site : Type*} [Fintype A] [Fintype Y]
variable (selected : A → Σ j : Fin m, Fin (n j)) (R : Fin m → ℝ)
variable (e : A → ScalarSiteExpansion Site) (k : ∀ a, (e a).Term) (site : Site)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (M : ℕ) (hd : ∀ a, (e a).period (k a) ∣ M)

noncomputable def forecastNormalizedResidues
    (label : ∀ j, Fin (n j) ⊕ E j → ZMod M) : ∀ a, ZMod ((e a).period (k a)) :=
  fun a => ZMod.castHom (hd a) (ZMod ((e a).period (k a)))
    (label (selected a).1 (.inl (selected a).2))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedNativeAmbientComparison
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal Classical

noncomputable def allocatedFixedPathSlicedAmbientFloorLog
    (d : ℕ) (D P V cost E Pg PR : ℝ) : ℝ :=
  max (D + 2 * P + V + cost + E + 32)
    (forecastJointGridSamplerLog d Pg (E + 4) V PR + 1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CandidateCommonFastBudgetMonotonicity
namespace OAI

section

namespace Erdos3

theorem allocatedCandidateCommonFastSectionInput_mono {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) :
    allocatedCandidateCommonFastSectionInput p ≤ allocatedCandidateCommonFastSectionInput q := by
  unfold allocatedCandidateCommonFastSectionInput
  exact add_le_add
    (pow_le_pow_left₀ (by positivity : 0 ≤ p + 2) (add_le_add hpq (le_refl 2)) 4) (le_refl 1)

theorem quotientInducedMarkHeightBudget_mono {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) :
    quotientInducedMarkHeightBudget p ≤ quotientInducedMarkHeightBudget q := by
  have hseven := pow_le_pow_left₀ (by positivity : 0 ≤ p + 3) (add_le_add hpq (le_refl 3)) 7
  unfold quotientInducedMarkHeightBudget
  exact pow_le_pow_left₀ (by positivity : 0 ≤ p + (p + 3) ^ 7 + 3)
    (add_le_add (add_le_add hpq hseven) (le_refl 3)) 4

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.MonomialCharacterMean
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def euclideanCharacter (ξ x : E) : ℂ :=
  CircleFourier.character ((inner ℝ ξ x : ℝ) : CircleFourier.Circle)

@[simp]
theorem euclideanCharacter_zero (ξ : E) : euclideanCharacter ξ 0 = 1 := by
  simp [euclideanCharacter]

@[simp]
theorem euclideanCharacter_add (ξ x y : E) :
    euclideanCharacter ξ (x + y) = euclideanCharacter ξ x * euclideanCharacter ξ y := by
  simp [euclideanCharacter, inner_add_right]

@[simp]
theorem euclideanCharacter_neg (ξ x : E) :
    euclideanCharacter ξ (-x) = star (euclideanCharacter ξ x) := by
  simp [euclideanCharacter]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeDualCoordinates
namespace OAI

section

namespace Erdos3

open Module

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

noncomputable def latticeDualBasis (b : Basis ι ℤ Λ) : Basis ι ℝ E := by
  classical
  exact LinearMap.BilinForm.dualBasis (innerₗ E) realInner_nondegenerate (b.ofZLatticeBasis ℝ Λ)

theorem euclideanDualLattice_eq_span (b : Basis ι ℤ Λ) :
    euclideanDualLattice Λ = Submodule.span ℤ (Set.range (latticeDualBasis Λ b)) := by
  classical
  have h := LinearMap.BilinForm.dualSubmodule_span_of_basis (R := ℤ) (innerₗ E)
    realInner_nondegenerate (b.ofZLatticeBasis ℝ Λ)
  simpa only [euclideanDualLattice, latticeDualBasis, Basis.ofZLatticeBasis_span] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairUniformFactors
namespace OAI

universe u

section

namespace Erdos3

namespace VectorPolynomial

open RationalFilteredNilmanifold

theorem allocatedFrozenTaggedFamilyInputBudget_mono {b b' t t' : ℝ}
    (hb : 0 ≤ b) (hbb : b ≤ b') (htt : t ≤ t') :
    allocatedFrozenTaggedFamilyInputBudget b t ≤
      allocatedFrozenTaggedFamilyInputBudget b' t' := by
  unfold allocatedFrozenTaggedFamilyInputBudget
  gcongr

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteSectionPermutation
namespace OAI

section

namespace Erdos3

variable {X : Type*} [Fintype X]

noncomputable def finiteMixedLp (w : ℕ → X → ℝ) (p : ℕ → ℝ) :
    (n : ℕ) → ((Fin n → X) → ℝ) → ℝ
  | 0, f => |f (fun i => Fin.elim0 i)|
  | n + 1, f => finiteMixedLp w p n
      (fun v => finiteWeightedLp (w n) (p n) (fun a => f (Fin.snoc v a)))

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

noncomputable def finiteMaskedLpStep (w : X → ℝ) (p : ℝ) (b : Bool) (x₀ : X)
    (n : ℕ) (f : (Fin (n + 1) → X) → ℝ) (v : Fin n → X) : ℝ :=
  if b then finiteWeightedLp w p (fun a => f (Fin.snoc v a)) else f (Fin.snoc v x₀)

noncomputable def finiteMaskedMixedLp (w : ℕ → X → ℝ) (p : ℕ → ℝ)
    (s : ℕ → Bool) (x₀ : X) : (n : ℕ) → ((Fin n → X) → ℝ) → ℝ
  | 0, f => |f (fun i => Fin.elim0 i)|
  | n + 1, f => finiteMaskedMixedLp w p s x₀ n (finiteMaskedLpStep (w n) (p n) (s n) x₀ n f)

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

def finiteSectionL2Control (w : ℕ → X → ℝ) :
    (n : ℕ) → ((Fin n → X) → ℝ) → (ℕ → ℝ) → Prop
  | 0, f, E => |f (fun i => Fin.elim0 i)| ≤ E 0
  | n + 1, f, E =>
      (∀ a, finiteSectionL2Control w n (fun v => f (Fin.snoc v a))
        (fun j => E (j + 1))) ∧
      finiteSectionL2Control w n
        (fun v => finiteWeightedLp (w n) 2 (fun a => f (Fin.snoc v a))) E

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteSectionFill {X : Type*} (n : ℕ) (s : Fin n → Bool)
    (z : Fin n → X) (v : Fin (n - finiteSectionCount s) → X) : Fin n → X :=
  finiteSplitPoint (fun i => s i = true) (fun i => z i)
    (fun i => v ((finiteSectionFreeOrder n s).symm i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PartitionedAffineLogEnvelope
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal

noncomputable def jointAffineInverseLog {D α : Type*} [Fintype D] [Fintype α]
    {O : D → Type*} [∀ d, Fintype (O d)] (h : D → ℕ) (P E F : ℝ) : ℝ :=
  Fintype.card D + ∑ d, (F + productMinorInverseLog (Fintype.card (O d)) (Fintype.card α) (h d) P
    (canonicalAffineMinorLog (O d) α (h d) P E F))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def affineBooleanAxisWeightLog (B O α : Type*) [Fintype B] [Fintype O] [Fintype α]
    (h : ℕ) (P E F : ℝ) : ℝ :=
  (scalarCubeDerivativeLog (Fintype.card α) P+2*Fintype.card (B × Fin h)+E+1)+
  (Fintype.card (BlockParameter B (Fin h) α)+P+canonicalAffineMinorLog O α h P E F+
    productMinorDeterminantLog (Fintype.card (BlockParameter B (Fin h) α))
      (Fintype.card O) (Fintype.card α) h P)+1

noncomputable def jointAffineBooleanWeightLog {D α : Type*} [Fintype D] [Fintype α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (h : D → ℕ) (P E F : ℝ) : ℝ :=
  Fintype.card D + ∑ d, affineBooleanAxisWeightLog (B d) (O d) α (h d) P E F

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoundedPrimeDepthBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def boundedPrime (Q : ℕ) (p : BoundedPrime Q) : ℕ := p.val

def boundedPrimeExponent (Q : ℕ) (p : BoundedPrime Q) : ℕ := Nat.log p.val Q

def boundedPrimePower (Q : ℕ) (p : BoundedPrime Q) : ℕ := p.val ^ boundedPrimeExponent Q p

theorem mem_boundedPrimes (Q p : ℕ) : p ∈ boundedPrimes Q ↔ p.Prime ∧ p ≤ Q := by
  simp only [boundedPrimes, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, and_comm]

theorem boundedPrime_prime (Q : ℕ) (p : BoundedPrime Q) : (boundedPrime Q p).Prime :=
  ((mem_boundedPrimes Q p.val).mp p.property).1

theorem boundedPrimePower_pos (Q : ℕ) (p : BoundedPrime Q) : 0 < boundedPrimePower Q p :=
  pow_pos (boundedPrime_prime Q p).pos _

instance boundedPrimePower_neZero (Q : ℕ) (p : BoundedPrime Q) : NeZero (boundedPrimePower Q p) :=
  ⟨(boundedPrimePower_pos Q p).ne'⟩

theorem boundedPrime_card_le (Q : ℕ) : Fintype.card (BoundedPrime Q) ≤ Q := by
  have hsub : boundedPrimes Q ⊆ (Finset.range (Q + 1)).erase 0 := by
    intro p hp
    have h := (mem_boundedPrimes Q p).mp hp
    exact Finset.mem_erase.mpr ⟨h.1.ne_zero, Finset.mem_range.mpr (by omega)⟩
  calc
    _ = (boundedPrimes Q).card := Fintype.card_coe _
    _ ≤ ((Finset.range (Q + 1)).erase 0).card := Finset.card_le_card hsub
    _ = Q := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def boundedPrimeProduct (Q : ℕ) : ℕ := ∏ p : BoundedPrime Q, boundedPrimePower Q p

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedCenteredForecastPathLogEnvelope
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem preparedCenteredForecast_badRadius_bound
    {X : Type*} [Fintype X] (m : ℕ) (stride : X → ℕ)
    {gainLog Qstride : ℝ} (hgainLog : 0 ≤ gainLog)
    (hstride : ∀ x, (stride x : ℝ) ≤ Real.exp Qstride) :
    (((∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) *
      quantitativeBadPrimeRadius (gainLog + 8)) : ℕ) : ℝ) ≤
      Real.exp (2 * Fintype.card X * Qstride +
        (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11) := by
  let correction := smallPrimePowerCorrection (modularCoefficientPrimeThreshold m)
  have hprod : ((∏ x, stride x : ℕ) : ℝ) ≤ Real.exp (Fintype.card X * Qstride) := by
    calc
      _ = ∏ x, (stride x : ℝ) := by simp only [Nat.cast_prod]
      _ ≤ ∏ _x : X, Real.exp Qstride :=
        Finset.prod_le_prod (fun x _ => Nat.cast_nonneg (stride x)) (fun x _ => hstride x)
      _ = Real.exp (Fintype.card X * Qstride) := by
        rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
  have hcorrection : (correction : ℝ) ≤ Real.exp correction := by
    linarith [Real.add_one_le_exp (correction : ℝ)]
  have hradius : (quantitativeBadPrimeRadius (gainLog + 8) : ℝ) ≤ Real.exp (gainLog + 11) := by
    simpa only [show gainLog + 8 + 3 = gainLog + 11 by ring] using
      (quantitativeBadPrimeRadius_bounds (show 0 ≤ gainLog + 8 by linarith)).2.1
  have hproduct := mul_le_mul
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hprod 2)
    (mul_le_mul hcorrection hradius (Nat.cast_nonneg _) (Real.exp_nonneg _))
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (sq_nonneg (Real.exp (Fintype.card X * Qstride)))
  calc
    _ = ((∏ x, stride x : ℕ) : ℝ) ^ 2 *
        ((correction : ℝ) * (quantitativeBadPrimeRadius (gainLog + 8) : ℝ)) := by
      simp only [Nat.cast_mul, Nat.cast_pow, correction]
    _ ≤ (Real.exp (Fintype.card X * Qstride)) ^ 2 *
        (Real.exp correction * Real.exp (gainLog + 11)) := hproduct
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp only [correction]
      ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedActualSlicedForecastSetup
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

noncomputable def preparedSlicedForecastBadLog (m nX : ℕ) (Qstride gainLog : ℝ) : ℝ :=
  2 * nX * Qstride + (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedTargetReal
namespace OAI

section

namespace Erdos3

theorem boundedPrimes_prime (Q : ℕ) :
    ∀ p ∈ boundedPrimes Q, p.Prime := by
  intro p hp
  exact ((mem_boundedPrimes Q p).mp hp).1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedComparisonGridPolynomialBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

def preparedComparisonGridPolynomial (m : ℕ) (t : ℝ) : ℝ :=
  preparedComparisonSourcePolynomial t +
    (10 * t + 30) * (t + (t + 1) * (t + 1) + 1) ^ 2 +
    (2 * t) * (t + 2) * (modularRankChargeFactor m : ℝ)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedSlicedForecastComparisonLogs
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedSlicedForecastPrimitiveCap : ℝ :=
  max 1 (scalarCubePrimitiveEnvelope Empty scalarSourceTransitionBound 1 0 1)

noncomputable def preparedSlicedForecastTailCap (cost : ℝ) : ℝ :=
  max preparedSlicedForecastPrimitiveCap (2 * Real.exp cost)

noncomputable def preparedSlicedForecastTailLog (cost : ℝ) : ℝ :=
  preparedSlicedForecastPrimitiveCap + cost + 1

theorem preparedSlicedForecastPrimitiveCap_one_le :
    1 ≤ preparedSlicedForecastPrimitiveCap := le_max_left _ _

theorem preparedSlicedForecastTailLog_nonneg {cost : ℝ} (hcost : 0 ≤ cost) :
    0 ≤ preparedSlicedForecastTailLog cost := by
  unfold preparedSlicedForecastTailLog
  linarith only [hcost, preparedSlicedForecastPrimitiveCap_one_le]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedModularGeneralDetectorFreeSpatialBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

structure PreparedModularGeneralDetectorFreeSpatialBounds
    (r : PreparedModularCanonicalDetectorResources ℝ) (τ : ℝ) : Prop where
  tau_pos : 0 < τ
  tau_sample : 1 / τ ≤ Real.exp r.Psample
  tau_mass : 1 / τ ≤ Real.exp r.Pmass
  tau_projection : τ⁻¹ ≤ Real.exp r.Pproj
  tau_native : τ⁻¹ ≤ Real.exp r.Pnative
  tau_side : τ⁻¹ ≤ Real.exp r.Pside

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleLocalScalarConstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

noncomputable def preparedFiniteScheduleDirectMaster {K : Type*} [Fintype K]
    (Pchart D pRadius Qstride Pphysical : ℝ)
    (u pModel Prho target gainLog : K → ℝ) : ℝ :=
  Pchart + D + pRadius + Qstride + Pphysical +
    ∑ k, (u k + pModel k + allocatedModelTestLog (u k) (pModel k) +
      Prho k + target k + gainLog k + 32)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AffineDegreeChoice
namespace OAI

section

namespace Erdos3

noncomputable def affineRemovalDepth (T : ℝ) : ℕ := CyclicCrootSisask.spectralIterations 1 T

noncomputable def affineFinalDegree (j r : ℕ) (shell Q : ℝ) : ℕ :=
  j + max r (CyclicCrootSisask.spectralIterations shell Q)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffinePrimitiveLogBudget
namespace OAI

section

namespace Erdos3

noncomputable def affineComparisonTail (ε L T : ℝ) : ℕ :=
  CyclicCrootSisask.spectralIterations (ε / (2 + ε)) (L + 2 * T + 4)

noncomputable def affineComparisonScale (ε L T C : ℝ) : ℝ :=
  L + T + 2 + (affineRemovalDepth T + affineComparisonTail ε L T : ℕ) + C

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrimeCoordinateCells
namespace OAI

section

namespace Erdos3

noncomputable def affineComparisonPrimeThreshold (ξ P : ℝ) : ℝ :=
  (P + 2) ^ (4 + CyclicCrootSisask.spectralIterations ξ 18)

noncomputable def affineComparisonContraction (ξ P : ℝ) : ℝ :=
  (affineComparisonPrimeThreshold ξ P)⁻¹

end Erdos3

end

section

namespace Erdos3

open scoped Classical

noncomputable def affineMandatoryPrimes {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (ξ P : ℝ) : Finset ι :=
  Finset.univ.filter (fun i => (prime i : ℝ) ≤ affineComparisonPrimeThreshold ξ P)

end Erdos3

end

section

namespace Erdos3

open scoped Classical

noncomputable def affineInitialPrimeMask {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (ξ P : ℝ) (sourceM siteM : ℕ) : Finset ι :=
  (affineMandatoryPrimes prime ξ P ∪ periodPrimeCoordinates prime sourceM) ∪
    periodPrimeCoordinates prime siteM

end Erdos3

end

section

namespace Erdos3

open scoped Classical

noncomputable def affineSamplerPrimeMask {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (ξ P : ℝ) (sourceM siteM D : ℕ) : Finset ι :=
  affineInitialPrimeMask prime ξ P sourceM siteM ∪ periodPrimeCoordinates prime D

end Erdos3

end

section

namespace Erdos3

noncomputable def affineReferencePower (epsilon : ℝ) : ℕ :=
  4 + CyclicCrootSisask.spectralIterations (epsilon / (2 + epsilon)) 18

noncomputable def affineReferenceInput (epsilon U : ℝ) : ℝ :=
  (affinePrimitiveLogBudget U + 2) ^ affineReferencePower epsilon +
    affinePrimitiveLogBudget U + 3 * U + 10

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

def affineSampleAlphabetEquiv {J I R : Type*} :
    (Option J × I → R) ≃ (J → I → R) × (I → R) where
  toFun z := (fun j i => z (some j, i), fun i => z (none, i))
  invFun z := baseArrayJoin (fun k => z.1 k.1 k.2) z.2
  left_inv z := baseArrayJoin_eta z
  right_inv _ := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedPhysicalCRT
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J I : Type*} [Fintype J] [Fintype I]
  (q : ι → ℕ) [∀ i, NeZero (q i)]

noncomputable def affinePeriodResidueSample (D : ℕ) (a : J → ℤ)
    (z : ∀ i, Option J × I → ZMod (q i)) (s : ∀ i, J → ZMod (q i)) :
    ∀ i, I → ZMod (q i) :=
  fun i => (affineSampleAlphabetEquiv (z i)).2 +
    residueColumnMap (q := q i) (affineSampleAlphabetEquiv (z i)).1
      (fun j => (a j : ZMod (q i)) + (D : ZMod (q i)) * s i j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.InitialMaskedAffineComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def affineComparisonDegree (sourceDim siteDim : ℕ) (ε L T C shell modLog : ℝ) : ℕ :=
  let j := affineRemovalDepth T
  let r := affineComparisonTail ε L T
  let P := affineComparisonScale ε L T C
  affineFinalDegree j r shell
    ((j : ℝ) * (P + (sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 2) + ε + L + 2 * T + 10)

end Erdos3

end

section

namespace Erdos3

noncomputable def affineComparisonRequiredOrder (b : ℕ) (ε L T C : ℝ) : ℕ :=
  max ((affineRemovalDepth T + affineComparisonTail ε L T) *
    (affineComparisonMoment (affineComparisonScale ε L T C) + 1))
    (2 * b + affineRemovalDepth T)

noncomputable def affineComparisonLengthLog (b : ℕ) (ε L T C modLog dimLog : ℝ) : ℝ :=
  modLog * (affineComparisonRequiredOrder b ε L T C : ℕ) +
    affineComparisonAccuracyLog b (affineComparisonScale ε L T C) L T + dimLog + 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.GlobalAffineDegreeChoice
namespace OAI

section

namespace Erdos3

noncomputable def affineGlobalComparisonDegree (A sourceDim siteDim : ℕ)
    (ε L T C shell modLog countLog : ℝ) : ℕ :=
  A + max (affineComparisonDegree sourceDim siteDim ε L T C shell modLog)
    (CyclicCrootSisask.spectralIterations shell
      ((A : ℝ) * ((sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1) + 4 + countLog))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrimeFamilyCutoff
namespace OAI

section

namespace Erdos3

noncomputable def adaptiveAffineCountLog (A sourceDim siteDim : ℕ)
    (ε L T C modLog : ℝ) : ℝ :=
  (A : ℝ) * (affineComparisonScale ε L T C +
    (sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1)

noncomputable def adaptiveAffineShell (A sourceDim siteDim : ℕ)
    (ε L T C totalShell modLog : ℝ) : ℝ :=
  totalShell * Real.exp (-adaptiveAffineCountLog A sourceDim siteDim ε L T C modLog)

noncomputable def adaptiveAffineCutoff (A sourceDim siteDim : ℕ)
    (ε L T C totalShell modLog : ℝ) : ℕ :=
  affineGlobalComparisonDegree A sourceDim siteDim ε L T C
    (adaptiveAffineShell A sourceDim siteDim ε L T C totalShell modLog) modLog 0

noncomputable def adaptiveAffineSideLog (A sourceDim siteDim : ℕ)
    (ε L T C totalShell modLog dimLog : ℝ) : ℝ :=
  modLog * A + affineComparisonLengthLog
    (adaptiveAffineCutoff A sourceDim siteDim ε L T C totalShell modLog)
    ε L T C modLog dimLog + 2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCommonReferenceBudget
namespace OAI

section

namespace Erdos3

noncomputable def affineCommonReferenceBudget (E : ℕ) (epsilon U : ℝ) : ℝ :=
  2 * (affineReferenceInput epsilon U + 2) ^ E

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AmplificationSourceRankBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def amplificationSourceRankLogConstant (b C : ℕ) (K : ℝ) : ℝ :=
  1 + levelCoefficient K * Real.log b + C

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedFiniteNestedForwardAllDegreePaddedSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem preparedFiniteNestedForwardAllDegreeDegree_le {outerDepth innerDepth cutoff m : ℕ}
    (hcutoff : cutoff ≤ m)
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) :
    preparedFiniteNestedForwardAllDegreeDegree k ≤ m :=
  (Nat.le_of_lt_succ k.2.2.1.isLt).trans hcutoff

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSamplerRelativeInduction
namespace OAI

section

namespace Erdos3

def finiteSplitPoint_linearPart {K : Type*} (keep : K → Prop) [DecidablePred keep] :
    ({k // keep k} → ℤ) →+ (K → ℤ) where
  toFun x := finiteSplitPoint keep x 0
  map_zero' := by
    funext k
    by_cases hk : keep k <;> simp [finiteSplitPoint, hk]
  map_add' x y := by
    funext k
    by_cases hk : keep k <;> simp [finiteSplitPoint, hk]

end Erdos3

end

end OAI
end


