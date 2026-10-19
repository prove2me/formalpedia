-- Prove2me | Definitions.Def_OAIE3v2B100
-- name    : OAIE3v2B100
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:33:28.457992+00:00
-- url     : https://prove2.me/theorems/fbb31af5-4be9-46ef-a5d0-ffb5070207eb
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 102 of 311
-- statement:
--   Definitions bundle 102 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B068`, `OAIE3v2B069`, `OAIE3v2B070`, `OAIE3v2B071`, `OAIE3v2B073`, `OAIE3v2B074`, `OAIE3v2B080`, `OAIE3v2B081`, `OAIE3v2B082`, `OAIE3v2B083`, `OAIE3v2B084`, `OAIE3v2B085`, `OAIE3v2B086` of this split.
--
--   Modules: `Dynamics/JointPivotProfileBudget.lean`, `Dynamics/PreparedNestedEndpointDimensionBudget.lean`, `Estimates/CanonicalCoefficientCoverLift.lean`, `Estimates/CoefficientDeckImageCongruence.lean`, `Estimates/CoefficientRowReindex.lean`, `Estimates/CoefficientTailScaling.lean`, `Estimates/CoveredJetReference.lean`, `Estimates/CoveredMixedArrayImage.lean`, `Estimates/DenseProgressionInnerFamily.lean`, `Estimates/GaussianTailRadius.lean`, `Estimates/JointBooleanGoodWeight.lean`, `Estimates/MixedCoveredRowReindex.lean`, `Estimates/PhysicalBoundaryLabels.lean`, `Estimates/ProductCutoffLipschitz.lean`, `Estimates/RegularCylinderDecomposition.lean`, `Estimates/ReindexedCubeDomain.lean`, `Estimates/RepresentativeWindowPatch.lean`, `Estimates/RetainedSlicedCoefficientSource.lean`, `Estimates/SelectedCoefficientEvaluation.lean`, `Estimates/StableReferenceMean.lean`, `Fourier/CoefficientFourierTranslation.lean`, `Fourier/FixedPrincipalCoefficientSpectrum.lean`, `Fourier/MonomialCharacterMean.lean`, `Fourier/TorusCellBudget.lean`, `Geometry/AuxiliaryBoxPartition.lean`, `Geometry/CoefficientDeckChartRecovery.lean`, `Geometry/MixedArraySourceSupport.lean`, `Geometry/MixedCoefficientSmallSupport.lean`, `Geometry/PhysicalBoxPartition.lean`, `Geometry/ScalarSpatialScaleBounds.lean`, `Lattices/AffineCubeMinorGoodMass.lean`, `Lattices/AffineMeshRetention.lean`, `Lattices/AllocatedCoefficientIntegerMarginal.lean`, `Lattices/AllocatedResidueLabelCount.lean`, `Lattices/CoefficientDeckResidueMask.lean`, `Lattices/CoprimeResiduePhysicalStability.lean`, `Lattices/JointAffineBooleanSource.lean`, `Lattices/JointAffineBooleanTolerance.lean`, `Lattices/PartitionedAffineLogEnvelope.lean`, `Lattices/PrimeCoordinateCells.lean`, `Lattices/PrincipalResidueMixture.lean`, `Lattices/RecoveredLatticeMatrixInvariance.lean`, `Lattices/ResidueSliceUpperFailure.lean`, `Lattices/StandardLatticeCoordinates.lean`, `Linear/AllocatedModularRankMixedUniform.lean`, `Linear/ContainedKernelPhysicalDisplacement.lean`, `Linear/FixedSpatialKernelSliceDensity.lean`, `Linear/OrderedBasisCoordinates.lean`, `Linear/RealOrderedBasisProduct.lean`, `Linear/SmoothPairKernel.lean`, `Linear/WeightedParameterPatchRankPadding.lean`, `Polynomial/CRTPolynomialChargeBound.lean`, `Polynomial/JointAffinePolynomialSource.lean`, `Polynomial/PolynomialCoordinatePartition.lean`, `Polynomial/SchmidtShortDualVector.lean`, `Probability/AllocatedSpatialCoefficientReferenceLaw.lean`, `Probability/CanonicalPairPointLaw.lean`, `Probability/NormalizedCoveredDensity.lean`, `Probability/ScalarCubeHistogramMeasure.lean`, `Probability/ShiftedProductCoordinateLaw.lean`, `Sampling/FixedPathSlicedGridMeshBudget.lean`, `Sampling/JointMeasureProductiveNarrowSampler.lean`, `Sampling/PreparedActualForecastSetup.lean`, `Sampling/PreparedModularCanonicalDetectorSamplingBounds.lean`, `Sampling/PreparedModularGeneralDetectorSamplingBounds.lean`, `Sampling/SmoothSplitSampling.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B068
import Definitions.Def_OAIE3v2B069
import Definitions.Def_OAIE3v2B070
import Definitions.Def_OAIE3v2B071
import Definitions.Def_OAIE3v2B073
import Definitions.Def_OAIE3v2B074
import Definitions.Def_OAIE3v2B080
import Definitions.Def_OAIE3v2B081
import Definitions.Def_OAIE3v2B082
import Definitions.Def_OAIE3v2B083
import Definitions.Def_OAIE3v2B084
import Definitions.Def_OAIE3v2B085
import Definitions.Def_OAIE3v2B086

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductCutoffLipschitz
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

noncomputable def scalarCubeBoundaryWeight (α : Type*) [Fintype α] [DecidableEq α]
    (r : ℝ) : (Option α → ℝ) → ℝ :=
  scalarCubeCutoffWeight (inequalityBoundaryCutoff (fun _ : Bool × Finset α => r) scalarCubeFace)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

noncomputable def scalarCubeProductWeight {ι : Type*} [Fintype ι]
    (α : Type*) [Fintype α] [DecidableEq α] (r : ι → ℝ) : (ι → Option α → ℝ) → ℝ :=
  tensorCutoffWeight (fun i => scalarCubeBoundaryWeight α (r i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointBooleanGoodWeight
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

noncomputable def scalarCubeGoodWeight {I J : Type*} [Fintype I] [Fintype J]
    (α : Type*) [Fintype α] [DecidableEq α] (ψ : ℝ → ℝ) (r : I → ℝ) (κ : J → ℝ)
    (d : J → (I → Option α → ℝ) → ℝ) (x : I → Option α → ℝ) : ℝ :=
  scalarCubeProductWeight α r x * sublevelCutoffProduct ψ κ d x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientTailScaling
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {D K Z α : Type*} [Fintype α] [DecidableEq α]
  {B O T : D → Type*} [∀ d, Fintype (B d)]

noncomputable def coefficientArraySampler (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (terms : ∀ d, Finset (T d))
    (weight : ∀ d, T d → ℝ) (exponent : ∀ d, T d → K →₀ ℕ)
    (coefficientIndex : ∀ d, T d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α)
    (t : ℝ) (z : Z → ℝ) (x : JointBlockParameter B h α → ℝ) (o : Σ d, O d) : ℝ :=
  jointBooleanSampler h c sets x o + t * normalizedCoefficientTailValue
    (terms o.1) (weight o.1) (exponent o.1) (coefficientIndex o.1) inputIndex z x (sets o.1 o.2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedCoefficientEvaluation
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

theorem smoothSplitProfile_join (J I : Type*) [Fintype J] [Fintype I]
    (p : (J → ℝ) × (I → ℝ)) :
    smoothSplitProfile J I p = smoothProductProfile (J ⊕ I) (Sum.elim p.1 p.2) :=
  (smoothProductProfile_sum J I p.1 p.2).symm

theorem smoothSplitProfile_range (J I : Type*) [Fintype J] [Fintype I]
    (p : (J → ℝ) × (I → ℝ)) :
    0 ≤ smoothSplitProfile J I p ∧ smoothSplitProfile J I p ≤ 1 := by
  rw [smoothSplitProfile_join]
  exact smoothProductProfile_range _ _

theorem smoothSplitProfile_zero_outside (J I : Type*) [Fintype J] [Fintype I]
    (p : (J → ℝ) × (I → ℝ)) (hp : 1 < ‖p‖) : smoothSplitProfile J I p = 0 := by
  rw [smoothSplitProfile_join]
  exact smoothProductProfile_zero_outside _ _ (by rwa [sumElim_norm])

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

noncomputable def smoothCoefficientPMF (S : ℝ) (hS : 0 < S) : PMF ℤ :=
  realWeightPMF (fun k => smoothProbabilityProfile ((k : ℝ) / S))
    (fun _ => (smoothProbabilityProfile_range _).1)
    (smoothProfileSamples_summable hS) (smoothSampleSum_pos hS)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem splitInputProfile_smooth (J I : Type*) [Fintype J] [Fintype I] :
    splitInputProfile (smoothSplitProfile J I) = smoothProductProfile (J ⊕ I) := by
  funext x
  unfold splitInputProfile
  rw [smoothSplitProfile_join]
  congr 1
  funext k
  cases k <;> rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarSpatialScaleBounds
namespace OAI


namespace Erdos3


theorem goodScalarKernelTuple_spatial_det_ne_zero {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] {L B : ℕ} {κ : ℝ}
    (s : I ↪ J) (x : J → IntegerScalarCubeBox I L) (root : J → ℤ)
    (hκ : 0 < κ) (hx : GoodScalarKernelTuple s κ B x) :
    (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s).det ≠ 0 := by
  rw [selectedSpatialPivot, rootDifferenceMatrix_det]
  intro hz
  have h := hx.1
  rw [normalizedScalarCubeMinor, hz, Int.cast_zero, zero_div, abs_zero] at h
  exact (not_lt_of_ge hκ.le) h

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ShiftedProductCoordinateLaw
namespace OAI


namespace Erdos3

open scoped Matrix

noncomputable def coefficientImagePMF {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (f : (J → ℝ) → ℝ) (hf : ∀ x, 0 ≤ f x)
    (S : J → ℝ) (hS : ∀ j, 0 < S j) {R : ℝ}
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) (hZ : 0 < coefficientWeightSum f S) : PMF (I → ℤ) :=
  (coefficientPMF f hf S hS hsupport hZ).map (fun z => A *ᵥ z)

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientRowReindex
namespace OAI


namespace Erdos3


open MeasureTheory
open scoped BigOperators NNReal

noncomputable def selectedCoefficientDensity {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i)
    (f : (J → ℝ) → ℝ) : (I → ℝ) → ℝ :=
  normalizedFiberDensity (A.submatrix id s) hA (remainingMatrixColumns A s)
    (fun i => S (s i)) P (fun j => S j.val) (fun i => hS (s i)) hP (selectedCoefficientProfile s f)

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialChargeBound
namespace OAI


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {I R : Type*} [CommRing R]

noncomputable def polynomialAffineClass (r : I → R) (c : R) :
    MvPolynomial I R →ₐ[R] MvPolynomial I R :=
  (polynomialCommonScale c).comp (polynomialTranslate r)

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.JointPivotProfileBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem affineCoefficientCommonBudget_nonneg (n d : ℕ) {b t : ℝ}
    (hb : 0 ≤ b) (ht : 0 ≤ t) : 0 ≤ affineCoefficientCommonBudget n d b t := by
  unfold affineCoefficientCommonBudget
  positivity [affineProfileLogBound_nonneg n ht]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProgressionInnerFamily
namespace OAI

section

namespace Erdos3

theorem progression_slice_endpoint_geometry {L step H : ℕ} (c : ℤ)
    (hL : 0 < L) (hstep : 0 < step) (hH : 2 ≤ H) {δ : ℝ} (hδ : 0 < δ)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (hdense : δ * L ≤ ((integerProgressionSupport c (step : ℤ) H).card : ℝ)) :
    let lower := (c : ℝ) / L
    let width := (step : ℝ) * ((H : ℝ) - 1) / L
    0 ≤ lower ∧ δ / 2 ≤ width ∧ |lower| + |width| ≤ 1 ∧
      (step : ℝ) / L ≤ 2 / ((H : ℝ) - 1) := by
  have hbase := hsubset (integerProgressionSupport_point c step H hstep 0 (by omega))
  have hlast := hsubset (integerProgressionSupport_point c step H hstep (H - 1) (by omega))
  have hc : (0 : ℝ) ≤ c := by
    have hh : 0 ≤ c := by simpa using (Finset.mem_Ico.mp hbase).1
    exact_mod_cast hh
  have hh : (c : ℝ) + (step : ℝ) * ((H : ℝ) - 1) < L := by
    have hh := (Finset.mem_Ico.mp hlast).2
    have he : (c : ℝ) + (step : ℝ) * ((H - 1 : ℕ) : ℝ) < L := by exact_mod_cast hh
    simpa only [Nat.cast_sub (by omega : 1 ≤ H), Nat.cast_one] using he
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hstep1 : (1 : ℝ) ≤ step := by exact_mod_cast hstep
  have hH2 : (2 : ℝ) ≤ H := by exact_mod_cast hH
  rw [card_integerProgressionSupport c step H hstep] at hdense
  have hwidth : δ / 2 ≤ (step : ℝ) * ((H : ℝ) - 1) / L := by
    apply (le_div_iff₀ hLp).mpr
    have h1 : (H : ℝ) / 2 ≤ (H : ℝ) - 1 := by linarith
    have h2 : (H : ℝ) - 1 ≤ (step : ℝ) * ((H : ℝ) - 1) := by nlinarith
    nlinarith
  have hw0 : 0 ≤ (step : ℝ) * ((H : ℝ) - 1) / L := (half_pos hδ).le.trans hwidth
  refine ⟨div_nonneg hc hLp.le, hwidth, ?_, ?_⟩
  · rw [abs_of_nonneg (div_nonneg hc hLp.le), abs_of_nonneg hw0, ← add_div]
    exact (div_le_one hLp).mpr hh.le
  · apply (le_div_iff₀ (by linarith : 0 < (H : ℝ) - 1)).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hLp).mpr
    linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrincipalResidueMixture
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem principalResidueCell_eq {D α : Type*} [Fintype D] [DecidableEq D]
    [Fintype α] [DecidableEq α] (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (m : ℕ)
    (r : PrincipalTupleIndex B h → Option α → ZMod m) :
    Finset.univ.filter (fun y : PrincipalIntegerTuples B h α L => principalResidueLabel m y = r) =
      FiniteProbabilityWeights.piRestrictionSet
        (fun j => scalarCubeResidueSet α (L j) (fun _ => m) (r j)) := by
  classical
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    FiniteProbabilityWeights.mem_piRestrictionSet, mem_scalarCubeResidueSet]
  exact ⟨fun he j i => congrFun (congrFun he j) i, fun he => funext (fun j => funext (he j))⟩

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

theorem intervalSiteWeight_near (B r : ℝ) (i : Fin (intervalSiteCount B r)) (x : ℝ)
    (hx : 0 < intervalSiteWeight B r i x) : dist x (intervalSiteCenter B r i) < 2 * r := by
  by_contra! hn
  exact hx.ne' (regularizedTentPartition_zero _ _ i x hn)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def localizedRepresentativeWindow (eta : ℝ≥0) (heta : 0 < eta)
    (i : Fin representativeWindowCount) : RepresentativeWindow where
  center := intervalSiteCenter 1 (1 / 16) i
  value x := interiorIntervalCutoff eta x * intervalSiteWeight 1 (1 / 16) i x
  lip := eta⁻¹ + representativeWindowPartitionLip
  nonneg x := mul_nonneg (interiorIntervalCutoff_range eta x).1
    (intervalSiteWeight_range 1 (by norm_num : (0 : ℝ) < 1 / 16) i x).1
  le_one x := (mul_le_of_le_one_right (interiorIntervalCutoff_range eta x).1
    (intervalSiteWeight_range 1 (by norm_num : (0 : ℝ) < 1 / 16) i x).2).trans
      (interiorIntervalCutoff_range eta x).2
  interior x hx := by
    have h := interiorIntervalCutoff_support eta (mul_ne_zero_iff.mp hx).1
    exact ⟨lt_trans (show (0 : ℝ) < eta from heta) h.1, by linarith [eta.coe_nonneg]⟩
  small x hx := by
    have hi : 0 < intervalSiteWeight 1 (1 / 16) i x :=
      lt_of_le_of_ne (intervalSiteWeight_range 1 (by norm_num : (0 : ℝ) < 1 / 16) i x).1
        (Ne.symm (mul_ne_zero_iff.mp hx).2)
    have h := intervalSiteWeight_near 1 (1 / 16) i x hi
    rw [Real.dist_eq] at h
    linarith
  lipschitz := by
    have h := bounded_weight_cutoff_lipschitz (interiorIntervalCutoff eta)
      (intervalSiteWeight 1 (1 / 16) i) (B := 1)
      (fun x => by rw [abs_of_nonneg (interiorIntervalCutoff_range eta x).1]
                   exact (interiorIntervalCutoff_range eta x).2)
      (fun x => by rw [abs_of_nonneg (intervalSiteWeight_range 1 (by norm_num : (0 : ℝ) < 1 / 16) i x).1]
                   exact (intervalSiteWeight_range 1 (by norm_num : (0 : ℝ) < 1 / 16) i x).2)
      (interiorIntervalCutoff_lipschitz eta heta)
      (intervalSiteWeight_lipschitz 1 (by norm_num : (0 : ℝ≥0) < 1 / 16) i)
    simpa only [one_mul, representativeWindowPartitionLip, representativeWindowCount,
      NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalBoxPartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem comparableBoxPartitions_length {I : Type*} (N H : I → ℕ)
    (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i) (i : I)
    (k : (comparableBoxPartitions N H hH hHN i).Label) :
    H i ≤ (comparableBoxPartitions N H hH hHN i).length k ∧
      (comparableBoxPartitions N H hH hHN i).length k < 2 * H i :=
  FiniteProgressionPartition.mergedIntervals_length_bounds (N i) (H i) (hH i) (hHN i) k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalBoundaryLabels
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def physicalBoxClassify (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (x : I → ℤ) : Option (∀ i, (P i).Label) :=
  if hx : x ∈ translatedIntegerBox lo N then some (physicalBoxCell lo N P ⟨x, hx⟩) else none

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedParameterPatchRankPadding
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem localTentKernel_ge_half {d q : ℕ} (hq : 8 ≤ q) (x : Fin d → ℝ)
    (hx : dist x 0 ≤ 1 / (q : ℝ)) : 1 / 2 ≤ (localTentKernel d q hq).value x := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hmul : (q : ℝ) * dist x 0 ≤ 1 := by
    simpa only [mul_comm] using (le_div_iff₀ hqR).mp hx
  exact (by linarith : (1 : ℝ) / 2 ≤ 1 - (q : ℝ) / 2 * dist x 0).trans (le_max_right _ _)

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

theorem localTent_translateSum_ge_half (d q : ℕ) (hq : 8 ≤ q) (x : Fin d → ℝ) :
    1 / 2 ≤ (localTentKernel d q hq).translateSum (torusGridCenter q) x := by
  obtain ⟨a, b, hab⟩ := torusGrid_cover (show 0 < q by omega) x
  exact (localTentKernel_ge_half hq _ hab).trans
    (((localTentKernel d q hq).kernel_le_periodicValue (x - torusGridCenter q a) b).trans
      ((localTentKernel d q hq).periodicValue_le_translateSum (torusGridCenter q) a x))

noncomputable def torusGridKernel (d q : ℕ) (hq : 8 ≤ q) (a : Fin d → Fin q) : PatchKernel d :=
  (localTentKernel d q hq).normalizedTranslate (torusGridCenter q) (1 / 2) (by norm_num)
    (fun x => by simpa using localTent_translateSum_ge_half d q hq x) a

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators NNReal

variable {σ : Type*} {s d : ℕ}

noncomputable def polynomialTorusCell (w : Fin d → ℕ) (hw : ∀ i, 1 ≤ w i)
    (hws : ∀ i, w i ≤ s) (hmono : Monotone w) (P : Fin d → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) (w i))
    (q : ℕ) (hq : 8 ≤ q) (a : Fin d → Fin q) : PolynomialPatch σ s d :=
  PolynomialPatch.ofCoordinates w hw hws hmono (fun i => P i - C (torusGridCenter q a i))
    (fun i => (weightedSupportLE _ _).sub_mem (hP i) (weightedSupportLE_C _ _ _))
    (torusGridKernel d q hq a)

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

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (e : Basis (Fin d) ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

noncomputable def orderedBasisTailProduct (i : ℕ) (t : Fin d → ℚ) :
    NilpotentLieBCHGroup L s hnil :=
  (((List.finRange d).drop i).map fun j => (⟨t j • e j⟩ : NilpotentLieBCHGroup L s hnil)).prod

noncomputable def orderedBasisProduct (t : Fin d → ℚ) : NilpotentLieBCHGroup L s hnil :=
  orderedBasisTailProduct e hnil 0 t

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

noncomputable def physicalBoundaryBudget {I : Type*} [Fintype I]
    (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i)) (r : I → ℕ) (width : I → ℝ) : ℝ :=
  ∑ i, 2 * (Fintype.card (P i).Label : ℝ) * (2 * (r i : ℝ) + 1) / width i

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def physicalMeshCrossing {I X M : Type*} [Fintype I] [DecidableEq I]
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (mesh : X → M) (location : X → I → ℤ) (x : X) : Prop :=
  ∃ y, mesh y = mesh x ∧ physicalBoxClassify lo N P (location x) ≠ physicalBoxClassify lo N P (location y)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedPathSlicedGridMeshBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

noncomputable def scalarCubeGridHistogram (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) : (Option I → ℝ) → ℝ :=
  rectangularWeightHistogram (scalarCubeIndicator I) a S 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeHistogramMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def scalarCubeGridDensity (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (x : Option I → ℝ) : ℝ :=
  scalarCubeGridHistogram I a S x / (∫ y, scalarCubeGridHistogram I a S y)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StandardLatticeCoordinates
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped Matrix

variable {D I J : Type*} [Fintype D] [Fintype I] [Fintype J]

theorem standardLatticeCoordinates_residue [DecidableEq D]
    (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
    (bP : Basis J ℝ Wᗮ) (hP : span ℤ (Set.range bP) = projectedIntegerLattice W)
    (M : ℕ) [NeZero M] :
    ∃ A : Matrix (J ⊕ I) D ℤ,
      (∀ i j, 0 ≤ A i j ∧ A i j < M) ∧
      ∀ β, integerResidueMap (J ⊕ I) M (standardLatticeCoordinates W bW bP hP β) =
        integerResidueMatrix A M *ᵥ integerResidueMap D M β :=
  exists_bounded_integerMap_residue_matrix (standardLatticeCoordinates W bW bP hP).toLinearMap M

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoefficientSmallSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule

variable {D : Type*} [Fintype D] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)

noncomputable def normalizedChartReference (Ω : Set (EuclideanSpace ℝ D)) :
    Measure (W × (Fin n → ℤ)) :=
  (ENNReal.ofReal (ZLattice.covolume (latticeSection (standardEuclideanLattice D) W)))⁻¹ •
    (volume.prod (Measure.count : Measure (Fin n → ℤ))).restrict
      (normalizedLatticePoint W b ⁻¹' Ω)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedArraySourceSupport
namespace OAI

section

namespace Erdos3

open Module Submodule _root_.Set
open scoped BigOperators

theorem mixedArrayQuotient_injOn_chart {D I J : Type*} [Fintype D] [Fintype I] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W) :
    Set.InjOn (mixedArrayQuotient (J := J) W b hb o) {x | mixedArrayInChart W b o x} := by
  intro x hx y hy he
  apply (mixedArrayRegroup I (Fin n) J).injective
  funext j
  apply (orthonormalMixedChart o).injective
  exact normalizedLatticeQuotient_injOn W b hb (Subset.rfl) (hx j) (hy j) (congrFun he j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReindexedCubeDomain
namespace OAI

section

namespace Erdos3

open MeasureTheory

def reindexedBlockCubeDomain {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    [DecidableEq α] {N : ℕ} (e : BlockParameter B F α ≃ Fin N) : Set (Fin N → ℝ) :=
  (fun x => x ∘ e) ⁻¹' blockCubeDomain B F α

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalCoefficientCoverLift
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D : Type*} [Fintype D] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

theorem normalizedLatticeRepresentative_continuous :
    Continuous (normalizedLatticeRepresentative W b hb) := by
  have hc : Continuous (standardLatticeIntegerLift W b hb) := continuous_of_discreteTopology
  exact continuous_fst.sub (W.orthogonalProjectionOnto.continuous.comp
    (continuous_subtype_val.comp (hc.comp continuous_snd)))

theorem normalizedCoverLift_continuous (d : ℕ) :
    Continuous (normalizedCoverLift W b hb d) := by
  have hc : Continuous (fun _ : W × (Fin n → ℤ) => (d : ℝ)⁻¹) := continuous_const
  exact QuotientAddGroup.continuous_mk.comp
    (hc.smul (normalizedLatticeRepresentative_continuous W b hb))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientDeckImageCongruence
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

attribute [local irreducible] coefficientDeckKernelEquiv

variable {K : Type*} [Fintype K] {m : ℕ} {J I B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

omit [Fintype K] in
theorem canonicalCoefficientDeckSample_coordinate (d : ℕ) (hd : 0 < d)
    (x : CoefficientSamplerArrays (K := K) I n) (r : CoefficientDeckResidues (K := K) B d)
    (j : Fin m) (e : BoundedCoefficientExponent K (j.val + 1)) :
    euclideanCoefficientEquiv U (canonicalCoefficientDeckSample U bW b hb o d hd x r) j e =
      normalizedCoverLift (euclideanSubspace (U j)) (b j) (hb j) d
        (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (x j) e)) +
      (coverKernelBasisEquiv
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup
        (bW j) d hd (r j e)).val := by
  simp only [canonicalCoefficientDeckSample, map_add, Pi.add_apply,
    coefficientDeckKernelEquiv_coordinate, canonicalCoefficientCoverLift, AddEquiv.apply_symm_apply]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientDeckChartRecovery
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))
variable (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
variable (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

noncomputable def latticeDeckInteger (z : Fin n → ℤ) (w : I → ℤ) : D → ℤ :=
  (standardLatticeCoordinates W bW b hb).symm (Sum.elim z w)

theorem normalizedCoverLift_add_deck (d : ℕ) (hd : 0 < d)
    (x : W × (Fin n → ℤ)) (w : I → ℤ) :
    normalizedCoverLift W b hb d x +
        (coverKernelBasisEquiv (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
          bW d hd (integerResidueMap I d w)).val =
      QuotientAddGroup.mk' _ ((d : ℝ)⁻¹ •
        (normalizedLatticeRepresentative W b hb x + (bW.equivFun.symm w).val)) := by
  have hr : integerResidueMap I d w =
      latticeBasisResidue (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
        bW d (bW.equivFun.symm w) := by
    change integerResidueMap I d w = integerResidueMap I d (bW.equivFun (bW.equivFun.symm w))
    rw [LinearEquiv.apply_symm_apply]
  rw [hr, coverKernelBasisEquiv_residue, coverLatticePoint_val, smul_add, map_add]
  rfl

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule

variable {K : Type*} [Fintype K] {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def coefficientSamplerDeckInteger
    (x : CoefficientSamplerArrays (K := K) I n)
    (w : ∀ j, BoundedCoefficientExponent K (j.val + 1) → E j → ℤ) :
    CoefficientAmbientIndex K J → ℤ :=
  fun a => latticeDeckInteger (euclideanSubspace (U a.1.1)) (bW a.1.1) (b a.1.1) (hb a.1.1)
    (fun i => (x a.1.1).2 i a.1.2) (w a.1.1 a.1.2) a.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical
attribute [local irreducible] coefficientDeckKernelEquiv

variable {K : Type*} {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem canonicalCoefficientDeckSample_residue_injective (q : ℕ) (hq : 0 < q)
    (x : CoefficientSamplerArrays (K := K) I n) :
    Function.Injective (canonicalCoefficientDeckSample U bW b hb o q hq x) := by
  intro r s h
  apply (coefficientDeckKernelEquiv U bW q hq).injective
  apply Subtype.ext
  exact add_left_cancel h

theorem canonicalCoefficientSample_injOn_chart :
    Set.InjOn (canonicalCoefficientSample (K := K) U b hb o)
      {x | ∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (x j)} := by
  intro x hx y hy h
  have h' := congrArg (euclideanCoefficientEquiv U) h
  simp only [canonicalCoefficientSample, AddEquiv.apply_symm_apply] at h'
  funext j
  exact mixedArrayQuotient_injOn_chart (euclideanSubspace (U j)) (b j) (hb j) (o j)
    (hx j) (hy j) (congrFun h' j)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredMixedArrayImage
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix

variable {D : Type*} [Fintype D] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

noncomputable def normalizedLatticeRepresentativeHom : (W × (Fin n → ℤ)) →+ W where
  toFun := normalizedLatticeRepresentative W b hb
  map_zero' := by simp [normalizedLatticeRepresentative]
  map_add' x y := by
    simp only [normalizedLatticeRepresentative, Prod.fst_add, Prod.snd_add,
      map_add, Submodule.coe_add]
    abel

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.NormalizedCoveredDensity
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped Classical

variable {D R : Type*} [Fintype D] [Fintype R] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))

noncomputable def normalizedCoveredReference (d : ℕ) [NeZero d] :
    Measure ((W × (Fin n → ℤ)) × (R → ZMod d)) :=
  ((ENNReal.ofReal (ZLattice.covolume (latticeSection (standardEuclideanLattice D) W)))⁻¹ •
    (volume.prod (Measure.count : Measure (Fin n → ℤ)))).prod
      (PMF.uniformOfFintype (R → ZMod d)).toMeasure

end Erdos3

end

end OAI
end

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

end VectorPolynomial

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CoefficientFourierTranslation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

variable {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem coefficientTorusCharacter_add (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (y x : CoefficientTorus (K := K) U) :
    coefficientTorusCharacter U frequency (y+x) =
      coefficientTorusCharacter U frequency y * coefficientTorusCharacter U frequency x :=
  quotientLinearCharacter_add _ _ _ _ _

theorem coefficientTorusFourierSum_add
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (y x : CoefficientTorus (K := K) U) :
    coefficientTorusFourierSum U frequency c (y+x) =
      coefficientTorusFourierSum U frequency
        (fun a => c a * coefficientTorusCharacter U (frequency a) y) x := by
  simp only [coefficientTorusFourierSum, coefficientTorusCharacter_add, mul_assoc]

theorem coefficientFourier_translate_norm
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (y : CoefficientTorus (K := K) U) :
    (∑ a, ‖c a * coefficientTorusCharacter U (frequency a) y‖) = ∑ a, ‖c a‖ := by
  simp only [norm_mul, coefficientTorusCharacter_norm, mul_one]

theorem coefficientFourier_translate_approx (D : CoefficientTorus (K := K) U → ℝ)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ) {δ : ℝ}
    (happrox : ∀ x, ‖(D x : ℂ) - coefficientTorusFourierSum U frequency c x‖ ≤ δ)
    (y x : CoefficientTorus (K := K) U) :
    ‖(D (y+x) : ℂ) - coefficientTorusFourierSum U frequency
      (fun a => c a * coefficientTorusCharacter U (frequency a) y) x‖ ≤ δ := by
  rw [← coefficientTorusFourierSum_add]
  exact happrox (y+x)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealOrderedBasisProduct
namespace OAI

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] {d s : ℕ}
  (e : Basis (Fin d) ℝ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

noncomputable def realOrderedBasisTailProduct (i : ℕ) (t : Fin d → ℝ) :
    NilpotentLieBCHGroup L s hnil :=
  (((List.finRange d).drop i).map fun j => (⟨t j • e j⟩ : NilpotentLieBCHGroup L s hnil)).prod

noncomputable def realOrderedBasisProduct (t : Fin d → ℝ) : NilpotentLieBCHGroup L s hnil :=
  realOrderedBasisTailProduct e hnil 0 t

noncomputable def realOrderedBasisPrefixProduct (i : ℕ) (t : Fin d → ℝ) :
    NilpotentLieBCHGroup L s hnil :=
  (((List.finRange d).take i).map fun j => (⟨t j • e j⟩ : NilpotentLieBCHGroup L s hnil)).prod

theorem realOrderedBasisPrefixProduct_congr (i : ℕ) {t u : Fin d → ℝ}
    (h : ∀ j : Fin d, j.val < i → t j = u j) :
    realOrderedBasisPrefixProduct e hnil i t = realOrderedBasisPrefixProduct e hnil i u := by
  apply congrArg List.prod
  apply List.map_congr_left
  intro j hj
  obtain ⟨k, hk, hkj⟩ := List.mem_take_iff_getElem.mp hj
  have hval : k = j.val := by simpa using congrArg Fin.val hkj
  rw [h j (by omega)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AuxiliaryBoxPartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def boxAuxiliaryCellEquiv {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (P i).step k = 1) (hpos : ∀ i k, 0 < (P i).length k)
    (M d : I → ℕ) (hd : ∀ i, 0 < d i) (u r b : I → ℤ)
    (hbase : ∀ i (x : ℤ), x ≡ b i [ZMOD r i] → x ≡ u i [ZMOD (M i : ℤ)])
    (k : AuxiliaryBoxLabels P M d u) (R c : I → ℤ)
    (hcombine : ∀ i (x : ℤ),
      (x ≡ b i [ZMOD r i] ∧ x ≡ ((k i).2.val.val : ℤ) [ZMOD (d i : ℤ)]) ↔ x ≡ c i [ZMOD R i]) :
    ↥(partitionCell (boxAuxiliaryCell a N P M d hd u r b hbase) k) ≃
      IntegerResidueBox (fun i => intervalCellLower (a i) (P i) (k i).1)
        (fun i => intervalCellUpper (a i) (P i) (k i).1) R c := by
  let e₁ : ↥(partitionCell (boxAuxiliaryCell a N P M d hd u r b hbase) k) ≃
      {x : IntegerResidueBox a (fun i => a i + N i) r b //
        ∀ i, intervalAuxiliaryCell (a i) (P i) (M i) (d i) (hd i)
          (u i) (r i) (b i) (hbase i) (x i) = k i} :=
    Equiv.subtypeEquivRight (fun x => by
      simp only [mem_partitionCell, boxAuxiliaryCell, funext_iff])
  exact e₁.trans (Equiv.subtypePiEquivPi.trans (Equiv.piCongrRight (fun i =>
    intervalAuxiliaryCellEquiv (a i) (P i) (hstep i) (hpos i) (M i) (d i) (hd i)
      (u i) (r i) (b i) (hbase i) (k i) (R i) (c i) (hcombine i))))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FixedPrincipalCoefficientSpectrum
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def positiveModerateSpectrumCover (J : Type*) [Fintype J] [DecidableEq J]
    (M n : ℕ) (U V L ζ : ℝ) : Finset (J → Fin M) :=
  lengthAwareSpectrumCover (positiveModerateLengthConstant n U) L (positiveModerateLengthExponent n)
    (polynomialGridCover J M (positiveModerateCoverConstant n (Fintype.card J) U V)
      (positiveModerateCoverExponent n (Fintype.card J))) ζ

end Erdos3

end

section

namespace Erdos3

noncomputable def positiveRetainedFrequencyBound (n d : ℕ) (U V ζ : ℝ) : ℝ :=
  (⌈positiveModerateCoverConstant n d U V / ζ ^ positiveModerateCoverExponent n d⌉₊ : ℝ)

noncomputable def positiveRetainedDenominatorBound (n d t : ℕ) (U V W ζ : ℝ) : ℝ :=
  max ((positiveRetainedFrequencyBound n d U V ζ + 1) ^ d)
    (W * positiveModerateLengthConstant n U ^ t / ζ ^ (positiveModerateLengthExponent n * t))

end Erdos3

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

theorem standardLatticeCoordinates_card {D I J : Type*}
    [Fintype D] [Fintype I] [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
    (bP : Basis J ℝ Wᗮ) (hP : span ℤ (Set.range bP) = projectedIntegerLattice W) :
    Fintype.card (J ⊕ I) = Fintype.card D := by
  simpa only [Module.finrank_fintype_fun_eq_card] using
    (standardLatticeCoordinates W bW bP hP).finrank_eq.symm

end Erdos3

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

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedNestedEndpointDimensionBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem exists_endpointDimension_local_budget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {x pnum : ℝ}, 0 ≤ x → pnum ∈ Set.Icc 0 x →
      ∀ nX M : ℕ, (nX : ℝ) ≤ x → (M : ℝ) ≤ x →
      allocatedComparisonDimension m pnum ≤ (x + C) ^ C ∧
        ((nX + m * M : ℕ) : ℝ) ≤ (x + C) ^ C := by
  let Q : Polynomial ℕ := allocatedComparisonDimension m Polynomial.X +
    Polynomial.C (m + 1) * Polynomial.X
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro x pnum hx hnum nX M hnX hM
  have htotal : allocatedComparisonDimension m x + (m + 1 : ℕ) * x ≤ (x + C) ^ C := by
    simpa [Q, allocatedComparisonDimension, Polynomial.eval₂_pow] using hbound x hx
  have hdim0 : 0 ≤ allocatedComparisonDimension m x := (allocatedComparisonDimension_bounds m hx).1
  have hmul0 : (0 : ℝ) ≤ (m + 1 : ℕ) * x := mul_nonneg (Nat.cast_nonneg _) hx
  have hmod : ((nX + m * M : ℕ) : ℝ) ≤ (m + 1 : ℕ) * x := by
    have hmul := mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    nlinarith only [hnX, hmul]
  exact ⟨(allocatedComparisonDimension_mono m hnum.1 hnum.2).trans
    (by linarith only [htotal, hmul0]), hmod.trans (by linarith only [htotal, hdim0])⟩

theorem exists_endpointDimension_uniform_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ m : ℕ, m ≤ s →
      ∀ {x pnum : ℝ}, 0 ≤ x → pnum ∈ Set.Icc 0 x →
      ∀ nX M : ℕ, (nX : ℝ) ≤ x → (M : ℝ) ≤ x →
      allocatedComparisonDimension m pnum ≤ (x + C) ^ C ∧
        ((nX + m * M : ℕ) : ℝ) ≤ (x + C) ^ C := by
  classical
  choose ex hex hb using fun j : Fin (s + 1) => exists_endpointDimension_local_budget j.val
  let C := 2 + ∑ j, ex j
  refine ⟨C, by dsimp only [C]; omega, ?_⟩
  intro m hm x pnum hx hnum nX M hnX hM
  let j : Fin (s + 1) := ⟨m, by omega⟩
  have hsum : ex j ≤ ∑ i, ex i :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have heC : ex j ≤ C := by dsimp only [C]; omega
  have hCReal : (2 : ℝ) ≤ C := Nat.cast_le.mpr ((hex j).trans heC)
  have hpow : (x + ex j) ^ ex j ≤ (x + C) ^ C :=
    (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl (Nat.cast_le.mpr heC)) _).trans
      (pow_le_pow_right₀ (by linarith only [hx, hCReal]) heC)
  have h := hb j hx hnum nX M hnX hM
  exact ⟨h.1.trans hpow, h.2.trans hpow⟩

noncomputable def preparedNestedEndpointDimensionExponent (s : ℕ) : ℕ :=
  (exists_endpointDimension_uniform_budget s).choose

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.MonomialCharacterMean
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[simp]
theorem monomialCharacterMean_zero (k : ℕ) (α : E) (N : ℕ) :
    monomialCharacterMean k α N 0 = 1 := by
  have hne : (Finset.Icc (-(N : ℤ)) (N : ℤ)).Nonempty := ⟨0, by simp⟩
  have hc : ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℂ) ≠ 0 := by
    exact_mod_cast hne.card_ne_zero
  simp only [monomialCharacterMean, euclideanCharacter, inner_zero_left,
    AddCircle.coe_zero, CircleFourier.character_zero, Finset.sum_const, nsmul_eq_mul,
    mul_one, div_self hc]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GaussianTailRadius
namespace OAI

section

namespace Erdos3

noncomputable def schmidtRadiusFactor (d : ℕ) (A : ℝ) : ℝ :=
  4 * ((d : ℝ) + Real.log A + 1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RegularCylinderDecomposition
namespace OAI

section

namespace Erdos3

variable {Ω ι : Type*} {X : ι → Type*}

noncomputable def removedCylinderWeights (F : Ω → ∀ i, X i) :
    (Ω → ℝ) → List (ProductCylinder X) → List (Ω → ℝ)
  | _, [] => []
  | w, c :: cs => c.cut F w :: removedCylinderWeights F (c.erase F w) cs

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCubeMinorGoodMass
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

variable {B O J α : Type*} [Fintype B] [Fintype O] [Fintype J] [Fintype α]
  [DecidableEq B] [DecidableEq O] [DecidableEq α] {h : ℕ}

noncomputable def affineBooleanCubeGoodWeight
    (c : J → B → ℝ) (sets : O → Finset α) (block : J → O → B)
    (v : Fin h) (sel : J → O → Option α)
    (L : (BlockParameter B (Fin h) α → ℝ) →L[ℝ] (BlockParameter B (Fin h) α → ℝ))
    (b : BlockParameter B (Fin h) α → ℝ)
    (ψ : ℝ → ℝ) (r : B × Fin h → ℝ) (κ : J → ℝ) :
    (BlockParameter B (Fin h) α → ℝ) → ℝ :=
  blockCubeWeight (scalarCubeGoodWeight α ψ r κ
    (fun j => affineBooleanCubeDeterminant (c j) sets (block j) v (sel j) L b))

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
open scoped ContDiff BigOperators

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}
  (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
  (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
  (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) →L[ℝ]
    (BlockParameter (B d) (Fin (h d)) α → ℝ))
  (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
  (ψ : ℝ → ℝ) (r : ∀ d, B d × Fin (h d) → ℝ) (κ : D → ℝ)

noncomputable def jointAffineBooleanGoodWeight : (JointBlockParameter B h α → ℝ) → ℝ :=
  sigmaAxisWeight (fun d => affineBooleanCubeGoodWeight (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.JointAffineBooleanTolerance
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

noncomputable def jointAffineSourceTolerance (h : D → ℕ) (c₀ C : D → ℝ)
    (A T : ℝ≥0) (δ E : ℝ) : ℝ :=
  let r := jointAffineSourceBoundaryRadius (B := B) (α := α) h E
  let κ := jointAffineSourceMinorThreshold (O := O) (α := α) h c₀ δ E
  let K := jointAffineBooleanInverseBudget (O := O) (α := α) h C κ δ
  let Q := jointAffineBooleanErrorBudget (O := O) (α := α) h C κ A T r δ
  polynomialPerturbationScale K 1 Q (E / 3) (Fintype.card (Σ d, O d))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.JointAffinePolynomialSource
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {D α Z : Type*} [Fintype Z] [DecidableEq Z] [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]

noncomputable def jointAffinePolynomialTolerance (h : D → ℕ) (c₀ C : D → ℝ)
    (A T : ℝ≥0) (degree : ℕ) (Cp δ E : ℝ) : ℝ :=
  jointAffineSourceTolerance (B := B) (O := O) (α := α) h c₀ C A T δ E /
    (1 + polynomialC2BoxBudget
      (Fintype.card (PolynomialParameter Z (JointBlockParameter B h α))) degree Cp)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RetainedSlicedCoefficientSource
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {D α Z K₀ : Type*} [Fintype Z] [DecidableEq Z]
  [fintypeD : Fintype D] [decidableEqD : DecidableEq D] [Fintype α]
  [decidableEqAlpha : DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [fintypeO : ∀ d, Fintype (O d)]
  [decidableEqB : ∀ d, DecidableEq (B d)] [decidableEqO : ∀ d, DecidableEq (O d)]
  [nonemptyO : ∀ d, Nonempty (O d)]

noncomputable def jointAffineCoefficientTolerance (h : D → ℕ) (c₀ C : D → ℝ)
    (A T : ℝ≥0) (degree : ℕ) (Csum Wsum δ E : ℝ) : ℝ :=
  jointAffinePolynomialTolerance (Z := Z) (B := B) (O := O) (α := α) h c₀ C A T
    (degree + 2) (booleanJetMassBudget (Fintype.card α) degree Csum +
      booleanJetMassBudget (Fintype.card α) degree Wsum) δ E

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrimeCoordinateCells
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def primeCoordinateCellEquiv {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j))) (I : Finset ι) (u : σ → ℤ) :
    primeCoordinateCell lo N q I (fun i j => (u j : ZMod (q i))) ≃
      IntegerResidueBox lo (fun j => lo j + N j) (fun _ => ((∏ i ∈ I, q i : ℕ) : ℤ)) u where
  toFun z := fun j => ⟨z.val j, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
    ((mem_translatedIntegerBox lo N z.val).mp ((mem_primeCoordinateCell_anchor lo N q hcop I u z.val).mp z.property).1 j),
    ((mem_primeCoordinateCell_anchor lo N q hcop I u z.val).mp z.property).2 j⟩⟩
  invFun z := ⟨fun j => (z j).val, (mem_primeCoordinateCell_anchor lo N q hcop I u _).mpr
    ⟨(mem_translatedIntegerBox lo N _).mpr (fun j => Finset.mem_Ico.mp (Finset.mem_filter.mp (z j).property).1),
      fun j => (Finset.mem_filter.mp (z j).property).2⟩⟩
  left_inv z := by apply Subtype.ext; rfl
  right_inv z := by funext j; apply Subtype.ext; rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CoprimeResiduePhysicalStability
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def residuePrimeCoordinateCellEquiv {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (hM : 0 < M) (hcop : ∀ i, M.Coprime (q i)) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    primeCoordinateCell (fun j => residueIndexLower (lo j) M (a j))
      (fun j => residueIndexLength (lo j) (lo j + N j) M (a j)) q I x ≃
    ResiduePrimeCoordinateCell lo N M a q I
      (fun i => affineResidueCoordinateEquiv M (q i) a (hcop i) (x i)) := by
  refine (primeCoordinateCell_subtypeEquiv _ _ q I x).trans
    ((integerResidueBoxEquiv lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a
      (fun _ => Nat.cast_pos.mpr hM)).subtypeEquiv ?_)
  intro z
  constructor
  · intro hz i hi
    change (fun j => ((a j + (M : ℤ) * z.val j : ℤ) : ZMod (q i))) = _
    rw [← affineResidueCoordinateEquiv_intCast M (q i) a (hcop i)]
    exact congrArg (affineResidueCoordinateEquiv M (q i) a (hcop i)) (hz i hi)
  · intro hz i hi
    apply (affineResidueCoordinateEquiv M (q i) a (hcop i)).injective
    rw [affineResidueCoordinateEquiv_intCast]
    exact hz i hi

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceUpperFailure
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def residuePrimeCoordinateCell_lcmEquiv {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) (u : ResiduePrimeCoordinateCell lo N M a q I x) :
    ResiduePrimeCoordinateCell lo N M a q I x ≃
      IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M.lcm (∏ i ∈ I, q i) : ℤ))
        (fun j => (u.val j).val) := by
  let uv := fun j => (u.val j).val
  have huM : ∀ j, uv j ≡ a j [ZMOD (M : ℤ)] :=
    fun j => (Finset.mem_filter.mp (u.val j).property).2
  have hc := fun z => residuePrimeCoordinate_constraints_lcm M a uv z q hcop I x huM u.property
  exact {
    toFun := fun z j => ⟨(z.val j).val, Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp (z.val j).property).1,
        (hc _).mp ⟨fun k => (Finset.mem_filter.mp (z.val k).property).2, z.property⟩ j⟩⟩
    invFun := fun z => ⟨fun j => ⟨(z j).val, Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp (z j).property).1,
        ((hc _).mpr (fun k => (Finset.mem_filter.mp (z k).property).2)).1 j⟩⟩,
      ((hc _).mpr (fun k => (Finset.mem_filter.mp (z k).property).2)).2⟩
    left_inv := fun z => by apply Subtype.ext; funext j; apply Subtype.ext; rfl
    right_inv := fun z => by funext j; apply Subtype.ext; rfl }

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StableReferenceMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateCell_lcm_nonempty {ι σ : Type*} [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (q : ι → ℕ) (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base) :
    Nonempty (IntegerResidueBox lo (fun j => lo j + N j)
      (fun _ => (M.lcm (∏ i ∈ K, q i) : ℤ)) (fun j => (u.val j).val)) :=
  ⟨residuePrimeCoordinateCell_lcmEquiv lo N M a q hpair K base u u⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedCoefficientIntegerMarginal
namespace OAI

section

namespace Erdos3
open MeasureTheory

namespace VectorPolynomial
open Module Submodule
open scoped BigOperators Classical

def coefficientIntegerScalars {K : Type*} {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
    (a : CoefficientSamplerArrays (K := K) I n) (q : CoefficientIntegerScalarIndex K n) : ℤ :=
  (a q.1).2 q.2.2 q.2.1

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def allocatedCoefficientIntegerPMF :
    PMF (CoefficientIntegerScalarIndex (LayerSamplerVariables G I n B) n → ℤ) :=
  independentProductPMF (fun q => allocatedLayerIntegerPMFs B U b hR hσ S q.1 q.2.2 q.2.1)

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CoefficientDeckResidueMask
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped Matrix

variable {D I : Type*} [Fintype D] [DecidableEq D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))
variable (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
variable (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (q : ℕ) [NeZero q]

noncomputable def normalizedDeckResidueRead (a : D → ZMod q) : Fin n ⊕ I → ZMod q :=
  integerResidueMatrix (Classical.choose (standardLatticeCoordinates_residue W bW b hb q)) q
    *ᵥ (-a)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule

variable {K : Type*} [Fintype K] {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)]
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

noncomputable def coefficientDeckResidueRead (q : ℕ) [NeZero q]
    (a : CoefficientAmbientIndex K J → ZMod q) : CoefficientChartResidues K n E q :=
  fun j e => normalizedDeckResidueRead (euclideanSubspace (U j)) (bW j) (b j) (hb j) q
    (fun i => a ⟨⟨j, e⟩, i⟩)

noncomputable def coefficientDeckResidueMask (q : ℕ) [NeZero q]
    (test : CoefficientChartResidues K n E q → ℝ) :
    (CoefficientAmbientIndex K J → ZMod q) → ℝ :=
  fun a => test (coefficientDeckResidueRead U bW b hb q a)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PartitionedAffineLogEnvelope
namespace OAI

section

namespace Erdos3
open scoped NNReal Classical

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
  {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)]

noncomputable def partitionedAffineSourceRadius (A T : ℝ≥0) (δ E : ℝ) : ℝ :=
  jointAffineSourceRadius (B := fun d : {d // ¬P d} => B d.val) (O := O) (α := α)
    (fun d => h d.val) (fun d => unitProfilePrincipalSize (B := B) d.val)
    (fun d => 2 * unitProfilePrincipalSize (B := B) d.val) A T δ E

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RecoveredLatticeMatrixInvariance
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D I E : Type*} [Fintype D] [Fintype I] [Fintype E] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))
variable (bW : Basis E ℤ (latticeSection (standardEuclideanLattice D) W))
variable (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

noncomputable def recoveredIntegerTransverse : (D → ℤ) →ₗ[ℤ] (Fin n → ℤ) where
  toFun β i := standardLatticeCoordinates W bW b hb β (Sum.inl i)
  map_add' β γ := by ext i; simp only [map_add, Pi.add_apply]
  map_smul' q β := by ext i; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

noncomputable def recoveredIntegerDeck : (D → ℤ) →ₗ[ℤ] (E → ℤ) where
  toFun β i := standardLatticeCoordinates W bW b hb β (Sum.inr i)
  map_add' β γ := by ext i; simp only [map_add, Pi.add_apply]
  map_smul' q β := by ext i; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

variable (o : OrthonormalBasis I ℝ W)

noncomputable def recoveredMixedCoordinates (y : EuclideanSpace ℝ D) (β : D → ℤ) :
    (I → ℝ) × (Fin n → ℤ) :=
  ((mixedRealCoordinates W b o y).1, recoveredIntegerTransverse W bW b hb β)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankMixedUniform
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {K A : Type*} {m : ℕ} {E : Fin m → Type*} {N : ℕ}

def coefficientDeckScalarEquiv :
    CoefficientDeckResidues (K := K) E N ≃ (CoefficientDeckScalarIndex K E → ZMod N) where
  toFun r t := r t.1 t.2.1 t.2.2
  invFun f j e i := f ⟨j, e, i⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ContainedKernelPhysicalDisplacement
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {G : Type*} [Fintype G]

noncomputable def containedKernelCubeMap (S : ℕ) (H step : G → ℕ) (c : G → ℤ)
    (hS : 0 < S)
    (hsubset : ∀ g, integerProgressionSupport (c g) (step g : ℤ) (H g) ⊆
      Finset.Ico (0 : ℤ) (S : ℤ))
    (x : ∀ g, IntegerScalarCubeBox Empty (H g)) : G → IntegerScalarCubeBox Empty S :=
  fun g => containedProgressionCubeMap Empty S (H g) (step g) (c g) hS (hsubset g) (x g)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FixedSpatialKernelSliceDensity
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (lower width : G → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
variable (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
variable (hw : ∀ g, width g ≠ 0)
local notation "frame" => fixedSpatialKernelSliceFrame W L z lower width
local notation "h0slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lower width false h0 hw
local notation "h1slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lower width true h1 hw

noncomputable def fixedSpatialKernelSliceDensity : (X → ℝ) → ℝ :=
  fixedSpatialKernelDensity e W L frame h0slice h1slice

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SmoothPairKernel
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def smoothPairProductDensity {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) (L : ℝ) (hH : ∀ i, 0 < H i) (hL : 0 < L)
    (y : I → Fin 2 → ℝ) : ℝ :=
  ∏ i, affinePairRowDensity t u k hne (H i) L (hH i) hL
    (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2)) (y i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SchmidtShortDualVector
namespace OAI

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

noncomputable def intervalPolynomialPhase (N : ℕ) (P : Polynomial ℝ) (x : ℤ) : ℂ :=
  if x ∈ Finset.Ico (0 : ℤ) (N : ℤ) then character ((P.eval (x : ℝ) : ℝ) : CircleFourier.Circle) else 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoordinatePartition
namespace OAI

section

namespace Erdos3

noncomputable def schmidtStepFactor (C e d : ℕ) (A : ℝ) : ℝ :=
  1 + (C : ℝ) * (8 * A) ^ e * (Real.exp Real.pi * A) *
    (schmidtRadiusFactor d A + (d : ℝ) + 1)

end Erdos3

end

section

namespace Erdos3

noncomputable def schmidtMassMultiplier (d : ℕ) (A : ℝ) : ℝ :=
  Real.exp 10 * ((d : ℝ) + Real.log A + 1) ^ 2

noncomputable def schmidtMassCeiling (d : ℕ) (A : ℝ) : ℝ :=
  A * (schmidtMassMultiplier d A) ^ d

end Erdos3

end

section

namespace Erdos3

noncomputable def schmidtMeanDenominator (C e d : ℕ) (A : ℝ) : ℝ :=
  (schmidtDegreeConstant C e * A ^ (e + 1) *
    (schmidtMassMultiplier d A) ^ (d * (e + 1) + 2)) ^ (d + 1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedSpatialCoefficientReferenceLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical

def coefficientIntegerDeckChartResidues {K : Type*} {m : ℕ}
    {n : Fin m → ℕ} {E : Fin m → Type*} (q : ℕ)
    (a : CoefficientIntegerScalarIndex K n → ℤ)
    (deck : CoefficientDeckResidues (K := K) E q) :
    CoefficientChartResidues K n E q :=
  fun j e => Sum.elim (fun i => (a ⟨j,e,i⟩ : ZMod q)) (deck j e)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CanonicalPairPointLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def shiftedPairLocationKernel {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) (L : ℝ) (hH : ∀ i, 0 < H i) (hL : 0 < L)
    (b : Option J × I → ℤ) (x y : I → ℤ) : ℝ :=
  smoothPairProductDensity t u k hne H L hH hL
    (fun i j => ((affinePairRowsOfLocations (x, y) i j - smoothAffinePairRows t u b i j : ℤ) : ℝ) / H i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.JointMeasureProductiveNarrowSampler
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem narrow_sampler_residue_scale {G J X : Type*} {P W τ ξ : ℝ}
    (hP : 0 ≤ P) (hW : 0 ≤ W) (hWP : W ≤ Real.exp P)
    (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp P)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hξP : ξ⁻¹ ≤ Real.exp P)
    (N q : X → ℕ) (hq : ∀ i, 0 < q i) (hqP : ∀ i, (q i : ℝ) ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hsize : ∀ i, Real.exp (10*P+128) ≤ (N i : ℝ)) :
    ∀ z : Option (G ⊕ J) × X, 8*(probabilityProfileLipschitz : ℝ) ≤
      residueProfileWidth q (narrowTrimmedSpatialWidths W τ ξ N) z := by
  have h2P : 0 ≤ 2*P := by positivity
  have hτξ : 0 < ξ*τ := mul_pos hξ hτ
  have hτξP : (ξ*τ)⁻¹ ≤ Real.exp (2*P) := by
    rw [mul_inv_rev]
    calc
      _ ≤ Real.exp P * Real.exp P := mul_le_mul hτP hξP (inv_nonneg.mpr hξ.le) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hB4 : W ≤ Real.exp (2*(2*P)) := hWP.trans (Real.exp_le_exp.mpr (by linarith))
  have hN (i) : 0 < N i := by exact_mod_cast (Real.exp_pos _).trans_le (hsize i)
  have hsz (i) : 64*(probabilityProfileLipschitz : ℝ)*(q i : ℝ)*(1+W) ≤ (ξ*τ)*(N i : ℝ) := by
    calc
      _ ≤ 64*(probabilityProfileLipschitz : ℝ)*(q i : ℝ)*(1+Real.exp (2*(2*P))) :=
        mul_le_mul_of_nonneg_left (by linarith only [hB4]) (by positivity)
      _ ≤ _ := spatial_scale_of_exp_size h2P hτξ hτξP (Nat.cast_nonneg _)
        ((hqP i).trans (Real.exp_le_exp.mpr (by linarith)))
        (hprofile.trans (Real.exp_le_exp.mpr (by linarith)))
        (by convert hsize i using 1; congr 2; ring)
  intro z
  exact (trimmedSpatialWidths_scale hW q hq N hsz z).trans
    (div_le_div_of_nonneg_right (narrowTrimmedSpatialWidths_lower hW hτ hξ1 N hN z)
      (Nat.cast_nonneg _))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedActualForecastSetup
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem forecastRows_one_le (j : ℕ) :
    1 ≤ (boundedBooleanJetRows (Fin 1) (j + 1)).card := by
  apply Finset.one_le_card.mpr
  exact ⟨∅, by simp only [mem_boundedBooleanJetRows, Finset.card_empty, Nat.zero_le]⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedModularCanonicalDetectorSamplingBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m nX : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {T : Type*} [Fintype T] (stride : Fin nX → ℕ)

structure PreparedModularDetectorSamplingBounds
    (r : PreparedModularCanonicalDetectorResources ℝ) (P target Pphysical Qstride Pk : ℝ) : Prop where
  sample_nonneg : 0 ≤ r.Psample
  mass_nonneg : 0 ≤ r.Pmass
  projection_one : 1 ≤ r.Pproj
  primitive_projection : P ≤ r.Pproj
  gain_projection : P + 32 ≤ r.Pproj
  period_projection : ((m + 1 : ℕ) : ℝ) * Pk ≤ r.Pproj
  profile_projection : (probabilityProfileLipschitz : ℝ) ≤ Real.exp r.Pproj
  projection_mass : r.Pproj ≤ r.Pmass
  mass_sample : r.Pmass ≤ r.Psample
  cover_base : r.coverLog ≤ r.baseAmbient
  cover_sample : r.coverLog ≤ r.Psample
  ambient_sample : r.ambient ≤ r.Psample
  sample_side : r.Psample ≤ r.Pside
  projection_side : r.Pproj ≤ r.Pside
  mass_side : r.Pmass ≤ r.Pside
  primitive_side : P ≤ r.Pside
  physical_side : Pphysical ≤ r.Pside
  target_side : target ≤ r.Pside
  X_sample : (Fintype.card (Fin nX) : ℝ) ≤ r.Psample
  frame_sample : (Fintype.card (Option (Fin 1) × Fin nX) : ℝ) ≤ r.Psample
  ambient_dimension_sample : (Fintype.card (CoefficientAmbientIndex (Fin 1) J) : ℝ) ≤ r.Psample
  jet_sample : ((∑ j : Fin m,
    (Fintype.card (BoundedCoefficientExponent (Fin 1) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp r.Psample
  stride_scale_nonneg : 0 ≤ Real.exp Qstride
  stride_scale_sample : Real.exp Qstride ≤ Real.exp r.Psample
  stride_sample : ∀ i, (stride i : ℝ) ≤ Real.exp r.Psample
  tau_pos : 0 < Real.exp (-Pphysical)
  precision_pos : 0 < Real.exp (-target)
  tau_sample : 1 / Real.exp (-Pphysical) ≤ Real.exp r.Psample
  epsilon_sample : 1 / Real.exp (-target) ≤ Real.exp r.Psample
  eta_sample : (Real.exp (-target))⁻¹ ≤ Real.exp r.Psample
  X_mass : (Fintype.card (Fin nX) : ℝ) ≤ r.Pmass
  frame_mass : (Fintype.card (Option (Fin 1) × Fin nX) : ℝ) ≤ r.Pmass
  ambient_dimension_mass : (Fintype.card (CoefficientAmbientIndex (Fin 1) J) : ℝ) ≤ r.Pmass
  jet_mass : ((∑ j : Fin m,
    (Fintype.card (BoundedCoefficientExponent (Fin 1) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp r.Pmass
  stride_mass : ∀ i, (stride i : ℝ) ≤ Real.exp r.Pmass
  tau_mass : 1 / Real.exp (-Pphysical) ≤ Real.exp r.Pmass
  X_projection : (Fintype.card (Fin nX) : ℝ) ≤ r.Pproj
  variables_projection : (Fintype.card T : ℝ) ≤ r.Pproj
  frame_projection : (Fintype.card (Option T × Fin nX) : ℝ) ≤ r.Pproj
  stride_projection : ∀ i, (stride i : ℝ) ≤ Real.exp r.Pproj
  tau_projection : (Real.exp (-Pphysical))⁻¹ ≤ Real.exp r.Pproj

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedModularGeneralDetectorSamplingBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m dim nX : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {T : Type*} [Fintype T] (stride : Fin nX → ℕ)

structure PreparedModularGeneralDetectorSamplingBounds
    (r : PreparedModularCanonicalDetectorResources ℝ) (P L target Pphysical Qstride Pk : ℝ) : Prop where
  sample_nonneg : 0 ≤ r.Psample
  mass_nonneg : 0 ≤ r.Pmass
  projection_one : 1 ≤ r.Pproj
  primitive_projection : P ≤ r.Pproj
  late_projection : L ≤ r.Pproj
  gain_projection : P + 32 ≤ r.Pproj
  period_projection : ((m + 1 : ℕ) : ℝ) * Pk ≤ r.Pproj
  profile_projection : (probabilityProfileLipschitz : ℝ) ≤ Real.exp r.Pproj
  projection_mass : r.Pproj ≤ r.Pmass
  mass_sample : r.Pmass ≤ r.Psample
  cover_base : r.coverLog ≤ r.baseAmbient
  cover_sample : r.coverLog ≤ r.Psample
  ambient_sample : r.ambient ≤ r.Psample
  sample_side : r.Psample ≤ r.Pside
  projection_side : r.Pproj ≤ r.Pside
  mass_side : r.Pmass ≤ r.Pside
  primitive_side : P ≤ r.Pside
  late_side : L ≤ r.Pside
  physical_side : Pphysical ≤ r.Pside
  target_side : target ≤ r.Pside
  X_sample : (Fintype.card (Fin nX) : ℝ) ≤ r.Psample
  frame_sample : (Fintype.card (Option (Fin dim) × Fin nX) : ℝ) ≤ r.Psample
  ambient_dimension_sample : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ r.Psample
  jet_sample : ((∑ j : Fin m,
    (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp r.Psample
  stride_scale_nonneg : 0 ≤ Real.exp Qstride
  stride_scale_sample : Real.exp Qstride ≤ Real.exp r.Psample
  stride_sample : ∀ i, (stride i : ℝ) ≤ Real.exp r.Psample
  tau_pos : 0 < Real.exp (-Pphysical)
  precision_pos : 0 < Real.exp (-target)
  tau_sample : 1 / Real.exp (-Pphysical) ≤ Real.exp r.Psample
  epsilon_sample : 1 / Real.exp (-target) ≤ Real.exp r.Psample
  eta_sample : (Real.exp (-target))⁻¹ ≤ Real.exp r.Psample
  X_mass : (Fintype.card (Fin nX) : ℝ) ≤ r.Pmass
  frame_mass : (Fintype.card (Option (Fin dim) × Fin nX) : ℝ) ≤ r.Pmass
  ambient_dimension_mass : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ r.Pmass
  jet_mass : ((∑ j : Fin m,
    (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp r.Pmass
  stride_mass : ∀ i, (stride i : ℝ) ≤ Real.exp r.Pmass
  tau_mass : 1 / Real.exp (-Pphysical) ≤ Real.exp r.Pmass
  X_projection : (Fintype.card (Fin nX) : ℝ) ≤ r.Pproj
  variables_projection : (Fintype.card T : ℝ) ≤ r.Pproj
  frame_projection : (Fintype.card (Option T × Fin nX) : ℝ) ≤ r.Pproj
  stride_projection : ∀ i, (stride i : ℝ) ≤ Real.exp r.Pproj
  tau_projection : (Real.exp (-Pphysical))⁻¹ ≤ Real.exp r.Pproj

end Erdos3.VectorPolynomial

end

end OAI
end


