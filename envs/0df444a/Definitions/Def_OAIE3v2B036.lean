-- Prove2me | Definitions.Def_OAIE3v2B036
-- name    : OAIE3v2B036
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:00:02.63673+00:00
-- url     : https://prove2.me/theorems/60771210-6bf8-4381-97da-55a3b14fe5d8
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 37 of 311
-- statement:
--   Definitions bundle 37 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/AllocatedFixedPathAmbientUniformPrecision.lean`, `Dynamics/ConstructLayerResetScales.lean`, `Dynamics/FixedListPowerBudget.lean`, `Dynamics/FixedPathSlicedSourceErrorScalar.lean`, `Estimates/CorrelationDerivative.lean`, `Estimates/CyclicOrdinaryShiftBranches.lean`, `Estimates/DenseCorrelationPairs.lean`, `Estimates/FiniteEqualityPatternCard.lean`, `Estimates/FiniteHypergraphAbstract.lean`, `Estimates/FiniteMixedArrayRefresh.lean`, `Estimates/FiniteMixedPermutation.lean`, `Estimates/FiniteProductImageDecay.lean`, `Estimates/FiniteSectionPermutation.lean`, `Estimates/IntegralHyperplaneCorrection.lean`, `Estimates/JoinedCoefficientProfile.lean`, `Estimates/LocalizedSiftingAlmostPeriods.lean`, `Estimates/MaskedCenteredCounting.lean`, `Estimates/ModularTagGap.lean`, `Estimates/NormalizedCutoffs.lean`, `Estimates/NormalizedJetColumns.lean`, `Estimates/PhysicalL1SourceAccuracy.lean`, `Estimates/PhysicalPairAccuracyLogBounds.lean`, `Estimates/ProductMeanPullback.lean`, `Estimates/ProductTensorGroupedBound.lean`, `Estimates/RationalOutputAxisReindex.lean`, `Estimates/RelativeFiberSlicePatch.lean`, `Estimates/ResidualErrorAllocation.lean`, `Estimates/SimultaneousDirichlet.lean`, `Estimates/SmallWeightedPhysicalReplacement.lean`, `Estimates/SmoothPairErrorLogBounds.lean`, `Estimates/SplitSmoothProductProfile.lean`, `Fourier/CRTConfigurationTorus.lean`, `Fourier/CharacterCoordinateScale.lean`, `Fourier/FrequencyGridIntervals.lean`, `Fourier/PolynomialCharacterRowPhase.lean`, `Fourier/TorusCellBudget.lean`, `Fourier/UniformScaledRetainedCharacters.lean`, `Geometry/EmptyCubeCoordinate.lean`, `Geometry/FixedSpatialEmptyCoordinates.lean`, `Geometry/IndependentProductTransport.lean`, `Geometry/ProgressionCoordinateResampling.lean`, `Geometry/UnitBoxAmplitude.lean`, `Lattices/AffineMeshRetention.lean`, `Lattices/AffineSliceC2Difference.lean`, `Lattices/BoxResiduePartition.lean`, `Lattices/GaussianLatticeDistance.lean`, `Lattices/IntegerBoxCutoffLogBounds.lean`, `Lattices/IntegerCokernelExponent.lean`, `Lattices/IntegerFiberUniformBound.lean`, `Lattices/IntegerImageProbabilityLaw.lean`, `Lattices/IntegerResidueLatticeSum.lean`, `Lattices/LatticeGaussianHyperplane.lean`, `Lattices/LatticeHyperplaneBasis.lean`, `Lattices/LatticeSheetHaar.lean`, `Lattices/MixedSmoothUniformBadPrimeProduct.lean`, `Lattices/PrimeCoordinateCells.lean`, `Lattices/RecoveredLatticeMatrixInvariance.lean`, `Lattices/ResidueRefinedPeriod.lean`, `Lattices/ResidueSliceUpperFailure.lean`, `Lattices/ScalarResidueInteriorCell.lean`, `Lattices/SmoothAffinePairLaw.lean`, `Lattices/UniformBoxResidueMass.lean`, `Linear/ContainedKernelPhysicalDisplacement.lean`, `Linear/FiniteKernelRestriction.lean`, `Linear/FiniteKernelSumBound.lean`, `Polynomial/ForecastComparisonFloorPolynomialBudget.lean`, `Polynomial/PolynomialDifferencePermanentBlocks.lean`, `Polynomial/PolynomialParameterContinuity.lean`, `Polynomial/SingleParameterPolynomial.lean`, `Polynomial/SlicedPrincipalPolynomial.lean`, `Probability/AnisotropicSmoothPairLaw.lean`, `Probability/NormalizedJetDensitySupport.lean`, `Probability/ScaledInputProbability.lean`, `Probability/UniformHomExpectation.lean`, `Sampling/ForecastModularCutoff.lean`, `Sampling/JointGridAccuracy.lean`, `Sampling/PhysicalGridCorrelation.lean`, `Sampling/RationalForecastGridTail.lean`, `Sampling/SmoothPairPhysicalGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorrelationDerivative
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteWeightedTest {Ω T : Type*} [Fintype T]
    (ψ : T → Ω) (w : T → ℂ) : (Ω → ℂ) →ₗ[ℂ] ℂ where
  toFun v := 𝔼 t, w t * v (ψ t)
  map_add' v z := by simp only [Pi.add_apply, mul_add, Finset.expect_add_distrib]
  map_smul' c v := by
    change (𝔼 t, w t * (c * v (ψ t))) = c * (𝔼 t, w t * v (ψ t))
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro t _
    ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseCorrelationPairs
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def partnerAnchorWeight {G : Type*} (U V Q : G → ℂ) (x : G) : ℂ :=
  U x * star (V x) * (Q x * star (Q x))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoxResiduePartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def integerResidueCount (a b r v : ℤ) : ℕ :=
  (Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card

noncomputable def integerRectangleVolume {I : Type*} [Fintype I] (a b : I → ℤ) : ℝ :=
  ∏ i, ((b i - a i : ℤ) : ℝ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FrequencyGridIntervals
namespace OAI

section

namespace Erdos3

noncomputable def frequencyGridInterval (M : ℕ) (center radius : ℝ) : Finset (Fin M) :=
  Finset.univ.filter (fun k => |(k.val : ℝ) - center| ≤ radius)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformScaledRetainedCharacters
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def lengthAwareSpectrumCover {K : Type*} [Fintype K]
    (C L : ℝ) (c : ℕ) (cover : ℝ → Finset K) (ζ : ℝ) : Finset K := by
  classical
  exact if C / ζ ^ c ≤ L then cover ζ else Finset.univ

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

theorem integerMatrixImage_index {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) :
    A.mulVecLin.range.toAddSubgroup.index = A.det.natAbs := by
  let e := LinearEquiv.ofInjective A.mulVecLin (Matrix.mulVec_injective_of_det_ne_zero hA)
  have h := Submodule.natAbs_det_equiv A.mulVecLin.range e
  have he : A.mulVecLin.range.subtype.comp e.toLinearMap = A.mulVecLin := by
    ext x i
    rfl
  change (LinearMap.det (A.mulVecLin.range.subtype.comp e.toLinearMap)).natAbs = _ at h
  rw [he] at h
  rw [← Matrix.toLin'_apply', LinearMap.det_toLin'] at h
  exact h.symm

theorem integerMatrixImage_det_smul {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (y : I → ℤ) : A.det • y ∈ A.mulVecLin.range := by
  refine ⟨A.adjugate *ᵥ y, ?_⟩
  change A *ᵥ (A.adjugate *ᵥ y) = A.det • y
  rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem integerMatrixImage_multiple_smul {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) {m : ℤ} (hm : A.det ∣ m) (y : I → ℤ) :
    m • y ∈ A.mulVecLin.range := by
  obtain ⟨r, rfl⟩ := hm
  simpa only [smul_smul, mul_comm] using
    A.mulVecLin.range.smul_mem r (integerMatrixImage_det_smul A y)

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

def pivotFreeLattice {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) : Submodule ℤ (J → ℤ) :=
  A.mulVecLin.range.comap B.mulVecLin

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerCokernelExponent
namespace OAI

section

namespace Erdos3

noncomputable def integerCokernelExponent {I : Type*} (L : Submodule ℤ (I → ℤ)) : ℕ :=
  AddMonoid.exponent ((I → ℤ) ⧸ L.toAddSubgroup)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CharacterCoordinateScale
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def latticeCharacterCoordinates {I : Type*} [DecidableEq I] (χ : AddChar (I → ℤ) ℂ) (i : I) : ℂ :=
  χ (Pi.single i 1)

theorem integerVector_sum_single {I : Type*} [Fintype I] [DecidableEq I] (v : I → ℤ) :
    v = ∑ i, v i • (Pi.single i 1 : I → ℤ) := by
  ext i
  simp [Pi.single_apply]

theorem latticeCharacter_eval {I : Type*} [Fintype I] [DecidableEq I]
    (χ : AddChar (I → ℤ) ℂ) (v : I → ℤ) :
    χ v = ∏ i, latticeCharacterCoordinates χ i ^ (v i : ℤ) := by
  have hsum (s : Finset I) : χ (∑ i ∈ s, v i • (Pi.single i 1 : I → ℤ)) =
      ∏ i ∈ s, latticeCharacterCoordinates χ i ^ (v i : ℤ) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, χ.map_add_eq_mul, ih]
      rw [χ.map_zsmul_eq_zpow]
      rfl
  rw [integerVector_sum_single v]
  convert hsum Finset.univ using 1
  apply Finset.prod_congr rfl
  intro i _
  simp [Pi.single_apply]

theorem latticeCharacterCoordinates_injective {I : Type*} [Fintype I] [DecidableEq I] :
    Function.Injective (latticeCharacterCoordinates (I := I)) := by
  intro χ ψ h
  ext v
  rw [latticeCharacter_eval, latticeCharacter_eval, h]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnitBoxAmplitude
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def pairedAmplitude (p : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  max (∏ i, p.1 i) (∏ i, p.2 i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativeFiberSlicePatch
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

noncomputable def finiteProductIntegral (w : I → X → ℝ) (f : (I → X) → ℝ) : ℝ :=
  ∑ v, (∏ i, w i (v i)) * f v

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J X : Type*}

def finiteProductCoordinateEquiv (e : I ≃ J) : (I → X) ≃ (J → X) where
  toFun v j := v (e.symm j)
  invFun v i := v (e i)
  left_inv v := by funext i; simp
  right_inv v := by funext j; simp

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

noncomputable def crtConfigurationEquiv {J : Type*} [Fintype J] (N : J → ℕ)
    (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j))) :
    (ZMod (∏ j, N j) × ZMod (∏ j, N j)) ≃+ ((t : J × Bool) → ZMod (N t.1)) where
  toFun z t := if t.2 then ZMod.prodEquivPi N hN z.2 t.1 else ZMod.prodEquivPi N hN z.1 t.1
  invFun w := ((ZMod.prodEquivPi N hN).symm (fun j => w (j, false)),
    (ZMod.prodEquivPi N hN).symm (fun j => w (j, true)))
  left_inv z := by
    apply Prod.ext
    · change (ZMod.prodEquivPi N hN).symm (ZMod.prodEquivPi N hN z.1) = z.1
      exact (ZMod.prodEquivPi N hN).symm_apply_apply z.1
    · change (ZMod.prodEquivPi N hN).symm (ZMod.prodEquivPi N hN z.2) = z.2
      exact (ZMod.prodEquivPi N hN).symm_apply_apply z.2
  right_inv w := by
    funext ⟨j, b⟩
    cases b
    · change ZMod.prodEquivPi N hN ((ZMod.prodEquivPi N hN).symm (fun j => w (j, false))) j = _
      exact congrFun ((ZMod.prodEquivPi N hN).apply_symm_apply _) j
    · change ZMod.prodEquivPi N hN ((ZMod.prodEquivPi N hN).symm (fun j => w (j, true))) j = _
      exact congrFun ((ZMod.prodEquivPi N hN).apply_symm_apply _) j
  map_add' z v := by
    funext ⟨j, b⟩
    cases b
    · change ZMod.prodEquivPi N hN (z.1 + v.1) j = _
      exact congrFun (map_add (ZMod.prodEquivPi N hN) z.1 v.1) j
    · change ZMod.prodEquivPi N hN (z.2 + v.2) j = _
      exact congrFun (map_add (ZMod.prodEquivPi N hN) z.2 v.2) j

noncomputable def crtConfigurationTorus {J : Type*} [Fintype J] (N : J → ℕ)
    [∀ j, NeZero (N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j))) :
    (ZMod (∏ j, N j) × ZMod (∏ j, N j)) →+ ((J × Bool) → UnitAddCircle) where
  toFun z t := ZMod.toAddCircle (crtConfigurationEquiv N hN z t)
  map_zero' := by ext t; simp
  map_add' z v := by ext t; simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SimultaneousDirichlet
namespace OAI

section

namespace Erdos3

noncomputable def fractionalPartBin (Q : ℕ) (hQ : 0 < Q) (x : ℝ) : Fin Q :=
  ⟨⌊(Q : ℝ) * Int.fract x⌋₊, by
    apply (Nat.floor_lt' hQ.ne').mpr
    have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
    simpa using mul_lt_mul_of_pos_left (Int.fract_lt_one x) hQR⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedCutoffs
namespace OAI

section

namespace Erdos3

open scoped NNReal Manifold ContDiff

variable {ι X : Type*} [Fintype ι]

noncomputable def normalizedCutoffs (f : ι → X → ℝ) (i : ι) (x : X) : ℝ :=
  f i x / ∑ j, f j x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.TorusCellBudget
namespace OAI

section

namespace Erdos3

noncomputable def torusGridCenter {d : ℕ} (q : ℕ) (a : Fin d → Fin q) : Fin d → ℝ :=
  fun i => (a i).val / (q : ℝ)

theorem fractionalPartBin_center_error {q : ℕ} (hq : 0 < q) (x : ℝ) :
    |((fractionalPartBin q hq x).val : ℝ) / q - Int.fract x| ≤ 1 / (q : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlo : ((fractionalPartBin q hq x).val : ℝ) ≤ (q : ℝ) * Int.fract x :=
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg q) (Int.fract_nonneg x))
  have hhi : (q : ℝ) * Int.fract x < ((fractionalPartBin q hq x).val : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hle : ((fractionalPartBin q hq x).val : ℝ) / q ≤ Int.fract x :=
    (div_le_iff₀ hqR).mpr (by simpa only [mul_comm] using hlo)
  rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
  apply (le_div_iff₀ hqR).mpr
  rw [sub_mul, div_mul_cancel₀ _ hqR.ne']
  nlinarith

theorem torusGrid_coordinate_cover {d q : ℕ} (hq : 0 < q) (x : Fin d → ℝ) :
    ∃ (a : Fin d → Fin q) (b : Fin d → ℤ),
      ∀ i, |(b i : ℝ) - (x - torusGridCenter q a) i| ≤ 1 / (q : ℝ) := by
  let a := fun i => fractionalPartBin q hq (x i)
  let b := fun i => Int.floor (x i)
  refine ⟨a, b, ?_⟩
  intro i
  have heq : (b i : ℝ) - (x - torusGridCenter q a) i =
      ((fractionalPartBin q hq (x i)).val : ℝ) / q - Int.fract (x i) := by
    simp only [b, a, Pi.sub_apply, torusGridCenter, Int.fract]
    ring
  rw [heq]
  exact fractionalPartBin_center_error hq (x i)

theorem torusGrid_cover {d q : ℕ} (hq : 0 < q) (x : Fin d → ℝ) :
    ∃ (a : Fin d → Fin q) (b : Fin d → ℤ),
      dist (fun i => (b i : ℝ) - (x - torusGridCenter q a) i) 0 ≤ 1 / (q : ℝ) := by
  obtain ⟨a, b, hab⟩ := torusGrid_coordinate_cover hq x
  refine ⟨a, b, (dist_pi_le_iff (by positivity)).mpr ?_⟩
  intro i
  simpa only [Pi.zero_apply, Real.dist_eq, sub_zero] using hab i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.IndependentProductTransport
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

def independentArrayRows {J I X : Type*} (z : J × I → X) : I → J → X :=
  fun i j => z (j, i)

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

noncomputable def scaledIntegerWeight (f : (J → ℝ) × (I → ℝ) → ℝ)
    (S : I → ℝ) (T : J → ℝ) (p : (I → ℤ) × (J → ℤ)) : ℝ :=
  f ((fun j => (p.2 j : ℝ) / T j), (fun i => (p.1 i : ℝ) / S i))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix BigOperators NNReal

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable def scaledIntegerFiberOutputMass (A : Matrix I I ℤ) (B : Matrix I J ℤ)
    (S P : I → ℝ) (T : J → ℝ) (f : (J → ℝ) × (I → ℝ) → ℝ) (v : I → ℤ) : ℝ :=
  ((∏ i, P i) / ((∏ i, S i) * (∏ j, T j))) *
    ∑' p : {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v}, scaledIntegerWeight f S T p.val

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SplitSmoothProductProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def splitInputProfile (f : (J → ℝ) × (I → ℝ) → ℝ) (x : J ⊕ I → ℝ) : ℝ :=
  f ((fun j => x (.inl j)), (fun i => x (.inr i)))

theorem splitCoordinates_norm (x : J ⊕ I → ℝ) :
    ‖((fun j => x (.inl j)), (fun i => x (.inr i)))‖ = ‖x‖ := by
  apply le_antisymm
  · change max ‖fun j => x (.inl j)‖ ‖fun i => x (.inr i)‖ ≤ ‖x‖
    apply max_le
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun j => norm_le_pi_norm x (.inl j)
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun i => norm_le_pi_norm x (.inr i)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro k
    cases k with
    | inl j =>
      exact (norm_le_pi_norm (fun j => x (.inl j)) j).trans
        (norm_fst_le ((fun j => x (.inl j)), (fun i => x (.inr i))))
    | inr i =>
      exact (norm_le_pi_norm (fun i => x (.inr i)) i).trans
        (norm_snd_le ((fun j => x (.inl j)), (fun i => x (.inr i))))

theorem splitInputProfile_zero_outside {f : (J → ℝ) × (I → ℝ) → ℝ} {R : ℝ}
    (hf : ∀ p, R < ‖p‖ → f p = 0) (x : J ⊕ I → ℝ) (hx : R < ‖x‖) :
    splitInputProfile f x = 0 :=
  hf _ (by rwa [splitCoordinates_norm])

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def scaledInputWeightSum (f : (J → ℝ) × (I → ℝ) → ℝ)
    (S : I → ℝ) (T : J → ℝ) : ℝ := ∑' p : (I → ℤ) × (J → ℤ), scaledIntegerWeight f S T p

noncomputable def scaledInputMass (f : (J → ℝ) × (I → ℝ) → ℝ)
    (S : I → ℝ) (T : J → ℝ) : ℝ := scaledInputWeightSum f S T / ((∏ i, S i) * (∏ j, T j))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProgressionCoordinateResampling
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G R : Type*} [DecidableEq R] {X : G → R → Type*}

def resampleGroupCoordinates (label : G → R) (c : ∀ g r, X g r)
    (t : ∀ g, X g (label g)) : ∀ g r, X g r :=
  fun g => Function.update (c g) (label g) (t g)

@[simp] theorem resampleGroupCoordinates_selected (label : G → R)
    (c : ∀ g r, X g r) (t : ∀ g, X g (label g)) (g : G) :
    resampleGroupCoordinates label c t g (label g) = t g := by
  simp only [resampleGroupCoordinates, Function.update_self]

def groupCoordinateResamplingEquiv (label : G → R) :
    ((∀ g r, X g r) × (∀ g, X g (label g))) ≃
      ((∀ g r, X g r) × (∀ g, X g (label g))) where
  toFun p := (resampleGroupCoordinates label p.1 p.2, fun g => p.1 g (label g))
  invFun p := (resampleGroupCoordinates label p.1 p.2, fun g => p.1 g (label g))
  left_inv p := by
    apply Prod.ext
    · funext g r
      by_cases hr : r = label g
      · subst r
        simp only [resampleGroupCoordinates, Function.update_self]
      · simp only [resampleGroupCoordinates, Function.update_of_ne hr]
    · funext g
      exact resampleGroupCoordinates_selected label p.1 p.2 g
  right_inv p := by
    apply Prod.ext
    · funext g r
      by_cases hr : r = label g
      · subst r
        simp only [resampleGroupCoordinates, Function.update_self]
      · simp only [resampleGroupCoordinates, Function.update_of_ne hr]
    · funext g
      exact resampleGroupCoordinates_selected label p.1 p.2 g

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
namespace OAI

section

namespace Erdos3

noncomputable def replacementAccuracy (B epsilon : ℝ) : ℝ := min 1 (epsilon / (1 + B))

theorem replacementAccuracy_spec {B epsilon : ℝ} (hB : 0 ≤ B) (hepsilon : 0 < epsilon) :
    0 < replacementAccuracy B epsilon ∧ replacementAccuracy B epsilon ≤ 1 ∧
      B * replacementAccuracy B epsilon ≤ epsilon := by
  have hden : 0 < 1 + B := by positivity
  refine ⟨lt_min zero_lt_one (div_pos hepsilon hden), min_le_left _ _, ?_⟩
  calc
    _ ≤ B * (epsilon / (1 + B)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hB
    _ ≤ epsilon := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hden).mpr
      nlinarith

theorem replacementAccuracy_cost {B epsilon x : ℝ} (hB : 0 ≤ B) (hepsilon : 0 < epsilon)
    (hx : x ≤ replacementAccuracy B epsilon) : B * x ≤ epsilon :=
  (mul_le_mul_of_nonneg_left hx hB).trans (replacementAccuracy_spec hB hepsilon).2.2

end Erdos3

end

section

namespace Erdos3

noncomputable def replacementScaleThreshold (C delta rho J Q R U : ℝ) : ℝ :=
  1 + 2 * C / delta + 4 * J / rho + 4 / rho + U + R * Q

end Erdos3

end

section

namespace Erdos3

noncomputable def residualPointAccuracy (M S F mesh epsilon : ℝ) : ℝ :=
  min (replacementAccuracy (6 * M * S * F) epsilon) (replacementAccuracy (2 * mesh) 1)

noncomputable def residualGridAccuracy (M S K epsilon : ℝ) : ℝ :=
  replacementAccuracy (6 * M * S * K) epsilon

noncomputable def residualMeanAccuracy (M K V epsilon : ℝ) : ℝ :=
  replacementAccuracy (V ^ 2 * (1 + 3 * M * K)) (min 1 epsilon)

theorem residualPointAccuracy_spec {M S F mesh epsilon : ℝ}
    (hM : 0 ≤ M) (hS : 0 ≤ S) (hF : 0 ≤ F) (hmesh : 0 ≤ mesh) (heps : 0 < epsilon) :
    0 < residualPointAccuracy M S F mesh epsilon ∧ residualPointAccuracy M S F mesh epsilon ≤ 1 ∧
      6 * M * S * F * residualPointAccuracy M S F mesh epsilon ≤ epsilon ∧
      mesh * residualPointAccuracy M S F mesh epsilon ≤ 1 / 2 := by
  have hfirst := replacementAccuracy_spec (by positivity : 0 ≤ 6 * M * S * F) heps
  have hsecond := replacementAccuracy_spec (by positivity : 0 ≤ 2 * mesh) (by norm_num : (0 : ℝ) < 1)
  have hp := replacementAccuracy_cost (by positivity : 0 ≤ 6 * M * S * F) heps (min_le_left _ (replacementAccuracy (2 * mesh) 1))
  have hm := replacementAccuracy_cost (by positivity : 0 ≤ 2 * mesh) (by norm_num : (0 : ℝ) < 1) (min_le_right (replacementAccuracy (6 * M * S * F) epsilon) _)
  exact ⟨lt_min hfirst.1 hsecond.1, (min_le_left _ _).trans hfirst.2.1, hp, by dsimp [residualPointAccuracy]; nlinarith [hm]⟩

theorem residualGridAccuracy_spec {M S K epsilon : ℝ}
    (hM : 0 ≤ M) (hS : 0 ≤ S) (hK : 0 ≤ K) (heps : 0 < epsilon) :
    0 < residualGridAccuracy M S K epsilon ∧ residualGridAccuracy M S K epsilon ≤ 1 ∧
      6 * M * S * K * residualGridAccuracy M S K epsilon ≤ epsilon :=
  replacementAccuracy_spec (by positivity) heps

theorem residualMeanAccuracy_spec {M K V epsilon : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K) (heps : 0 < epsilon) :
    0 < residualMeanAccuracy M K V epsilon ∧ residualMeanAccuracy M K V epsilon ≤ 1 ∧
      residualMeanAccuracy M K V epsilon * V ^ 2 ≤ 1 ∧
      3 * M * K * residualMeanAccuracy M K V epsilon * V ^ 2 ≤ epsilon := by
  have h := replacementAccuracy_spec (by positivity : 0 ≤ V ^ 2 * (1 + 3 * M * K)) (lt_min zero_lt_one heps)
  change 0 < residualMeanAccuracy M K V epsilon ∧ residualMeanAccuracy M K V epsilon ≤ 1 ∧
    V ^ 2 * (1 + 3 * M * K) * residualMeanAccuracy M K V epsilon ≤ min 1 epsilon at h
  have hmin1 : min (1 : ℝ) epsilon ≤ 1 := min_le_left _ _
  have hmine : min (1 : ℝ) epsilon ≤ epsilon := min_le_right _ _
  have heta : 0 ≤ residualMeanAccuracy M K V epsilon := h.1.le
  have hx : 0 ≤ 3 * M * K * residualMeanAccuracy M K V epsilon * V ^ 2 := by positivity
  have hy : 0 ≤ residualMeanAccuracy M K V epsilon * V ^ 2 := by positivity
  refine ⟨h.1, h.2.1, ?_, ?_⟩ <;> nlinarith [h.2.2]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineSliceC2Difference
namespace OAI

section

namespace Erdos3

variable {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

noncomputable def operatorPrecompose (J : E →L[ℝ] X) :
    (X →L[ℝ] Y) →L[ℝ] (E →L[ℝ] Y) :=
  (ContinuousLinearMap.compL ℝ E X Y).flip J

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialParameterContinuity
namespace OAI

section

namespace Erdos3

open scoped ContDiff

variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]

noncomputable def polynomialVectorMap (p : O → MvPolynomial I ℝ) (x : I → ℝ) (o : O) : ℝ :=
  MvPolynomial.eval x (p o)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PolynomialCharacterRowPhase
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {I V R S : Type*} [Fintype I] [CommRing R] [CommRing S]

noncomputable def polynomialCharacterRow (row : I → R) (F : I → MvPolynomial V R) :
    MvPolynomial V R := ∑ i, C (row i) * F i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ModularTagGap
namespace OAI

section

namespace Erdos3

def modularTagWeight (h : ℕ) : ℕ := 2 ^ h * h.factorial

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteProductImageDecay
namespace OAI

section

namespace Erdos3
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]
  {H : J → Type*} [∀ j, AddCommGroup (H j)]

def finiteProductCharacter : (∀ j, AddChar (H j) ℂ) →* AddChar (∀ j, H j) ℂ where
  toFun χ := {
    toFun := fun y => ∏ j, χ j (y j)
    map_zero_eq_one' := by simp
    map_add_eq_mul' := by intro x y; simp only [Pi.add_apply, AddChar.map_add_eq_mul,
      Finset.prod_mul_distrib] }
  map_one' := by ext y; simp
  map_mul' χ ψ := by ext y; simp [Finset.prod_mul_distrib]

def finiteProductCharacterCoordinate (χ : AddChar (∀ j, H j) ℂ) (j : J) :
    AddChar (H j) ℂ where
  toFun x := χ (Pi.single j x)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by rw [Pi.single_add, χ.map_add_eq_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScaledInputProbability
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

theorem scaledInputWeightSum_pos (f : (J → ℝ) × (I → ℝ) → ℝ) (S : I → ℝ) (T : J → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) (hM : 0 < scaledInputMass f S T) :
    0 < scaledInputWeightSum f S T := by
  have hp : 0 < (∏ i, S i) * (∏ j, T j) :=
    mul_pos (Finset.prod_pos fun i _ => hS i) (Finset.prod_pos fun j _ => hT j)
  have h := mul_pos hM hp
  rwa [scaledInputMass, div_mul_cancel₀ _ hp.ne'] at h

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

noncomputable def normalizedIntegerFiberOutputMass {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (S P : I → ℝ) (T : J → ℝ)
    (f : (J → ℝ) × (I → ℝ) → ℝ) (v : I → ℤ) : ℝ :=
  scaledIntegerFiberOutputMass A B S P T f v / scaledInputMass f S T

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedJetColumns
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

noncomputable def normalizedJetMass (α : Type*) [Fintype α] (d : ℕ) : ℝ≥0 :=
  2^Fintype.card α * (Fintype.card α+1)^d

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.NormalizedJetDensitySupport
namespace OAI


namespace Erdos3

open scoped NNReal

noncomputable def normalizedJetOutputRadius {I J : Type*} [Fintype I] [Fintype J]
    (α N : Type*) [Fintype α] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (F : (J → ℝ) →L[ℝ] (I → ℝ))
    (degree : ℕ) (R S : ℝ≥0) : ℝ≥0 :=
  (‖A.toContinuousLinearMap‖₊+‖F‖₊)*R + (Fintype.card N * normalizedJetMass α degree)*S

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothAffinePairLaw
namespace OAI


namespace Erdos3

open scoped Matrix

def pairDifferenceMod (m : ℕ) : (Fin 2 → ℤ) →+ ZMod m where
  toFun v := ((v 1 - v 0 : ℤ) : ZMod m)
  map_zero' := by simp
  map_add' x y := by simp only [Pi.add_apply, Int.cast_sub, Int.cast_add]; ring

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.UniformHomExpectation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def nestedTupleResidueReduction {I : Type*} (n : ℕ)
    {M N : ℕ} (hMN : M ∣ N) :
    (Fin n → I → ZMod N) →+ (Fin n → I → ZMod M) where
  toFun x a i := ZMod.castHom hMN (ZMod M) (x a i)
  map_zero' := by ext a i; simp
  map_add' := by
    intro x y
    ext a i
    exact map_add (ZMod.castHom hMN (ZMod M)) (x a i) (y a i)

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

noncomputable def integerBoxBadPairBudget (d B R r : ℕ) (L : ℝ) : ℝ :=
  2 ^ (d - 1) * (1 / (B : ℝ) ^ (d - 1) + (R : ℝ) / L ^ d) +
    ((2 * (r : ℝ) + 1) / L) ^ d

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

def integerVectorResidue {I : Type*} (m : ℕ) (x : I → ℤ) : I → ZMod m :=
  fun i => (x i : ZMod m)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalForecastGridTail
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]

def integerResidueTuple (N : ℕ) : (J → ℤ) →+ (J → ZMod N) where
  toFun x j := (x j : ZMod N)
  map_zero' := by ext j; simp
  map_add' := by intro x y; ext j; simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastModularCutoff
namespace OAI

section

namespace Erdos3

noncomputable def forecastJointGridCutoff (P E : ℝ) : ℕ :=
  ⌈Real.exp (P + E + 4)⌉₊

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarResidueInteriorCell
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def paddedIntegerPoint {I : Type*} (L P : ℕ) (x : I → Fin P) : I → ℤ :=
  fun i => (x i).val - L

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.EmptyCubeCoordinate
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def emptyCubeCoordinateEquiv (X : Type*) : (Option Empty → X) ≃ X where
  toFun x := x none
  invFun x := fun _ => x
  left_inv x := by
    funext i
    cases i with
    | none => rfl
    | some a => exact a.elim
  right_inv _ := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeHyperplaneBasis
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def latticeHyperplane (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ) : Submodule ℤ f.ker :=
  ZLattice.comap ℝ Λ f.ker.subtype

@[simp]
theorem mem_latticeHyperplane (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ) (x : f.ker) :
    x ∈ latticeHyperplane Λ f ↔ (x : E) ∈ Λ := Iff.rfl

noncomputable def hyperplaneRetraction (f : E →ₗ[ℝ] ℝ) (w : E) (hw : f w = 1) :
    E →ₗ[ℝ] f.ker where
  toFun x := ⟨x - f x • w, by simp only [LinearMap.mem_ker, map_sub, map_smul, hw, smul_eq_mul, mul_one, sub_self]⟩
  map_add' x y := by
    apply Subtype.ext
    change (x + y) - f (x + y) • w = (x - f x • w) + (y - f y • w)
    rw [map_add, add_smul]
    abel
  map_smul' a x := by
    apply Subtype.ext
    change a • x - f (a • x) • w = a • (x - f x • w)
    rw [map_smul, smul_eq_mul, smul_sub, smul_smul]

@[simp]
theorem hyperplaneRetraction_coe (f : E →ₗ[ℝ] ℝ) (w : E) (hw : f w = 1) (x : E) :
    (hyperplaneRetraction f w hw x : E) = x - f x • w := rfl

@[simp]
theorem hyperplaneRetraction_on_kernel (f : E →ₗ[ℝ] ℝ) (w : E) (hw : f w = 1) (x : f.ker) :
    hyperplaneRetraction f w hw (x : E) = x := by
  apply Subtype.ext
  simp only [hyperplaneRetraction_coe, LinearMap.mem_ker.mp x.property, zero_smul, sub_zero]

theorem hyperplaneRetraction_mem (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1) (x : E) (hx : x ∈ Λ) :
    hyperplaneRetraction f w hw x ∈ latticeHyperplane Λ f := by
  change x - f x • w ∈ Λ
  obtain ⟨n, hn⟩ := hint x hx
  rw [hn]
  simpa only [Int.cast_smul_eq_zsmul] using Λ.sub_mem hx (Λ.smul_mem n hwΛ)

instance latticeHyperplane_discrete (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (f : E →ₗ[ℝ] ℝ) : DiscreteTopology (latticeHyperplane Λ f) :=
  ZLattice.comap_discreteTopology ℝ Λ (by fun_prop) Subtype.val_injective

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def integralLatticeValue (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ)) (x : Λ) : ℤ :=
  (hint x x.property).choose

theorem integralLatticeValue_cast (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ)) (x : Λ) :
    (integralLatticeValue Λ f hint x : ℝ) = f (x : E) :=
  (hint x x.property).choose_spec.symm

noncomputable def integralLatticeCoordinate (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ)) : Λ →ₗ[ℤ] ℤ where
  toFun := integralLatticeValue Λ f hint
  map_add' x y := by
    apply Int.cast_injective (α := ℝ)
    simp only [Int.cast_add, integralLatticeValue_cast, Submodule.coe_add, map_add]
  map_smul' a x := by
    apply Int.cast_injective (α := ℝ)
    simp only [integralLatticeValue_cast, Submodule.coe_smul, map_zsmul, RingHom.id_apply,
      smul_eq_mul, Int.cast_mul, zsmul_eq_mul]

theorem integralLatticeCoordinate_cast (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ)) (x : Λ) :
    (integralLatticeCoordinate Λ f hint x : ℝ) = f (x : E) :=
  integralLatticeValue_cast Λ f hint x

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def latticeHyperplaneRetraction (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1) : Λ →ₗ[ℤ] latticeHyperplane Λ f where
  toFun x := ⟨hyperplaneRetraction f w hw x, hyperplaneRetraction_mem Λ f hint w hwΛ hw x x.property⟩
  map_add' x y := by
    apply Subtype.ext
    change hyperplaneRetraction f w hw ((x : E) + y) = _
    exact map_add (hyperplaneRetraction f w hw) (x : E) (y : E)
  map_smul' n x := by
    apply Subtype.ext
    change hyperplaneRetraction f w hw (n • (x : E)) = n • hyperplaneRetraction f w hw x
    exact map_zsmul (hyperplaneRetraction f w hw) n (x : E)

@[simp]
theorem latticeHyperplaneRetraction_coe (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1) (x : Λ) :
    (((latticeHyperplaneRetraction Λ f hint w hwΛ hw x : latticeHyperplane Λ f) : f.ker) : E) =
      (x : E) - f (x : E) • w := rfl

noncomputable def latticeHyperplaneSplit (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1) :
    Λ ≃ₗ[ℤ] (latticeHyperplane Λ f × ℤ) :=
  { (latticeHyperplaneRetraction Λ f hint w hwΛ hw).prod (integralLatticeCoordinate Λ f hint) with
    invFun y := ⟨((y.1 : f.ker) : E) + y.2 • w,
      Λ.add_mem ((mem_latticeHyperplane Λ f (y.1 : f.ker)).mp y.1.property) (Λ.smul_mem y.2 hwΛ)⟩
    left_inv x := by
      apply Subtype.ext
      change (x : E) - f (x : E) • w + integralLatticeCoordinate Λ f hint x • w = (x : E)
      rw [← Int.cast_smul_eq_zsmul ℝ, integralLatticeCoordinate_cast]
      exact sub_add_cancel _ _
    right_inv y := by
      apply Prod.ext
      · apply Subtype.ext
        apply Subtype.ext
        change ((y.1 : f.ker) : E) + y.2 • w -
          f (((y.1 : f.ker) : E) + y.2 • w) • w = ((y.1 : f.ker) : E)
        have hy : f ((y.1 : f.ker) : E) = 0 := (y.1 : f.ker).property
        rw [map_add, map_zsmul, hy, hw, zero_add, zsmul_eq_mul, mul_one,
          Int.cast_smul_eq_zsmul]
        exact add_sub_cancel_right _ _
      · apply Int.cast_injective (α := ℝ)
        change (integralLatticeCoordinate Λ f hint _ : ℝ) = (y.2 : ℝ)
        rw [integralLatticeCoordinate_cast]
        change f (((y.1 : f.ker) : E) + y.2 • w) = (y.2 : ℝ)
        have hy : f ((y.1 : f.ker) : E) = 0 := (y.1 : f.ker).property
        simp only [map_add, map_zsmul, hy, hw, zero_add, zsmul_eq_mul, mul_one] }

end Erdos3

end

section

namespace Erdos3

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def latticeHyperplaneBasis (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1)
    (b : Module.Basis ι ℤ (latticeHyperplane Λ f)) : Module.Basis (ι ⊕ Unit) ℤ Λ :=
  (b.prod (Module.Basis.singleton Unit ℤ)).map
    (latticeHyperplaneSplit Λ f hint w hwΛ hw).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IntegralHyperplaneCorrection
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def normalFunctional (ξ : E) : E →ₗ[ℝ] ℝ := (innerSL ℝ ξ).toLinearMap

@[simp]
theorem normalFunctional_apply (ξ x : E) : normalFunctional ξ x = inner ℝ ξ x := rfl

noncomputable def integralHyperplaneCorrection (ξ x : E) : E :=
  x - ((inner ℝ ξ x - (round (inner ℝ ξ x) : ℝ)) / ‖ξ‖ ^ 2) • ξ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.JointGridAccuracy
namespace OAI

section

namespace Erdos3

open scoped BigOperators

instance oddTorusFactor_neZero (Q : ℕ) : NeZero (2 * Q + 1) := ⟨by omega⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductMeanPullback
namespace OAI

section

namespace Erdos3

variable {I J : Type*} [DecidableEq I] [Fintype J] {X : I → Type*}

noncomputable abbrev productTupleIndexEquiv (a : J → I) (ha : Function.Injective a) :
    J ≃ ↥(Finset.univ.image a) :=
  Equiv.ofBijective (fun j => ⟨a j, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩)
    ⟨fun _ _ h => ha (congrArg Subtype.val h), by
      intro i
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp i.property
      exact ⟨j, Subtype.ext hj⟩⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeGaussianHyperplane
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def latticeHyperplaneInclusion (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ) :
    latticeHyperplane Λ f →ₗ[ℤ] Λ where
  toFun x := ⟨((x : f.ker) : E), (mem_latticeHyperplane Λ f (x : f.ker)).mp x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeSheetHaar
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def latticeGaussianNormalizer (Λ : Submodule ℤ E) (t : ℝ) : ℝ :=
  (Real.sqrt t) ^ Module.finrank ℝ E * ZLattice.covolume Λ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteKernelRestriction
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {G H X : Type*} [AddCommGroup G] [AddCommGroup H]
variable [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
variable (C : G →+ H) [Fintype C.ker]

variable [T2Space G] [MeasurableSpace X] [MeasurableAdd₂ G]

noncomputable def finiteKernelLiftLaw (ρ : Measure X) (s : X → G) : Measure G :=
  (ρ.prod (PMF.uniformOfFintype C.ker).toMeasure).map (fun p => s p.1 + p.2.val)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SlicedPrincipalPolynomial
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff

variable {B F : Type*} [Fintype B] [Fintype F]

noncomputable def principalSlicePolynomial (c : B → ℝ) (lower width : B × F → ℝ) :
    MvPolynomial (B × F) ℝ :=
  ∑ b, MvPolynomial.C (c b) * ∏ i,
    (MvPolynomial.C (lower (b, i)) + MvPolynomial.C (width (b, i)) * MvPolynomial.X (b, i))

section Joint

variable {D : Type*} [Fintype D] {B F : D → Type*}
variable [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
variable [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]

noncomputable def jointSlicedPolynomial (c : ∀ d, B d → ℝ)
    (lower width : ∀ d, B d × F d → ℝ) (o : Σ _d : D, Unit) :
    MvPolynomial (Σ d, B d × F d) ℝ :=
  MvPolynomial.rename (Sigma.mk o.1) (principalSlicePolynomial (c o.1) (lower o.1) (width o.1))

end Joint

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JoinedCoefficientProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def joinedCoefficientProfile {J N : Type*}
    (f : (J → ℝ) → ℝ) (g : (N → ℝ) → ℝ) (x : J ⊕ N → ℝ) : ℝ :=
  f (fun j => x (.inl j)) * g (fun n => x (.inr n))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FixedListPowerBudget
namespace OAI

section

namespace Erdos3

def fixedListWorkingBudget (p b : ℝ) : ℝ := 10 * (p + b + 2)

def fixedListComparisonBudget (B c : ℕ) (p : ℝ) : ℝ :=
  (fixedListWorkingBudget p ((p + 2) ^ B) + 2) ^ c

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalizedSiftingAlmostPeriods
namespace OAI

section

namespace Erdos3

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

noncomputable def goodDifferenceSet (S T : Finset G) (f : G → ℝ) (threshold : ℝ) : Finset G :=
  (S - T).filter (fun x => threshold ≤ f x)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicOrdinaryShiftBranches
namespace OAI

section

namespace Erdos3

def ordinaryShiftBranch {N : ℕ} (h : ZMod N) (b : Fin 2) (x : ZMod N) : ℤ :=
  (if N - h.val ≤ x.val then 1 else 0) - b.val

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MaskedCenteredCounting
namespace OAI

universe u

section

namespace Erdos3

open scoped BigOperators

def maskedNormalized {X : Type*} (mu phi : X → ℝ) (x : X) : ℝ :=
  1 + phi x * (mu x - 1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathAmbientUniformPrecision
namespace OAI

section

namespace Erdos3

def fixedPathComparisonPrecision (E : ℝ) : ℝ := E + 4

noncomputable def fixedPathForecastTolerance (E : ℝ) : ℝ :=
  Real.exp (-(E + 8))

def fixedPathAmbientPrecision (Q E : ℝ) : ℝ := Q + E + 8

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.GaussianLatticeDistance
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

noncomputable def latticeGaussianTail (t R : ℝ) : ℝ :=
  ∑' m : Λ, if R < ‖(m : E)‖ then Real.exp (-Real.pi * t * ‖(m : E)‖ ^ 2) else 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MixedSmoothUniformBadPrimeProduct
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def mixedResidueArrayEquiv (J D R : Type*) : ((J → R) × (D → R)) ≃ ((J ⊕ D) → R) where
  toFun p := Sum.elim p.1 p.2
  invFun f := (fun j => f (.inl j), fun d => f (.inr d))
  left_inv _ := rfl
  right_inv f := by funext t; cases t <;> rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerResidueLatticeSum
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {J : Type*} (q : ℕ) [NeZero q]

def integerResidueLatticePoint (r : J → ZMod q) (k : J → ℤ) : J → ℤ :=
  fun j => (r j).val + q * k j

@[simp] theorem integerResidueLatticePoint_cast
    (r : J → ZMod q) (k : J → ℤ) (j : J) :
    (integerResidueLatticePoint q r k j : ZMod q) = r j := by
  exact (ZMod.intCast_eq_iff q _ _).2 ⟨k j, rfl⟩

theorem integerResidueLatticePoint_bijective :
    Function.Bijective (fun p : (J → ZMod q) × (J → ℤ) =>
      integerResidueLatticePoint q p.1 p.2) := by
  constructor
  · rintro ⟨r, k⟩ ⟨r', k'⟩ h
    have hr : r = r' := by
      funext j
      have hj := congrArg (fun x : J → ℤ => (x j : ZMod q)) h
      simpa only [integerResidueLatticePoint_cast] using hj
    subst r'
    have hk : k = k' := by
      funext j
      have hj := congrFun h j
      change (r j).val + (q : ℤ) * k j = (r j).val + (q : ℤ) * k' j at hj
      exact mul_left_cancel₀ (show (q : ℤ) ≠ 0 by exact_mod_cast NeZero.ne q)
        (add_left_cancel hj)
    exact Prod.ext rfl hk
  · intro x
    refine ⟨(fun j => (x j : ZMod q), fun j => x j / q), ?_⟩
    funext j
    change ((x j : ZMod q).val : ℤ) + q * (x j / q) = x j
    rw [ZMod.val_intCast, Int.emod_add_mul_ediv]

noncomputable def integerResidueLatticeEquiv :
    ((J → ZMod q) × (J → ℤ)) ≃ (J → ℤ) :=
  Equiv.ofBijective _ (integerResidueLatticePoint_bijective q)

@[simp] theorem integerResidueLatticeEquiv_apply
    (r : J → ZMod q) (k : J → ℤ) :
    integerResidueLatticeEquiv q (r, k) = integerResidueLatticePoint q r k := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SingleParameterPolynomial
namespace OAI

section

namespace Erdos3

open scoped BigOperators fwdDiff

noncomputable def integerNewtonPolynomial (s : ℕ) (c : ℕ → ℤ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (s + 1),
    Polynomial.C ((c k : ℝ) / (k.factorial : ℝ)) * descPochhammer ℝ k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ConstructLayerResetScales
namespace OAI

section

namespace Erdos3

def layerResetThreshold (s B T h : ℕ) : ℕ := T ^ ((2 * B) ^ (s + 1 - h))

def layerResetCellScale (s B T h : ℕ) : ℕ := T ^ (2 * (2 * B) ^ (s - h))

@[simp] theorem layerResetThreshold_terminal (s B T : ℕ) :
    layerResetThreshold s B T (s + 1) = T := by simp [layerResetThreshold]

@[simp] theorem layerResetThreshold_initial (s B T : ℕ) :
    layerResetThreshold s B T 1 = T ^ ((2 * B) ^ s) := by simp [layerResetThreshold]

theorem layerResetThreshold_pos {s B T h : ℕ} (hT : 0 < T) :
    0 < layerResetThreshold s B T h := pow_pos hT _

theorem layerResetThreshold_ge {s B T h : ℕ} (hB : 0 < B) (hT : 0 < T) :
    T ≤ layerResetThreshold s B T h := by
  exact (Nat.pow_one T).symm.trans_le
    (Nat.pow_le_pow_right hT (by exact Nat.one_le_iff_ne_zero.mpr (ne_of_gt (pow_pos (by omega) _))))

theorem layerResetCellScale_sq {s B T h : ℕ} :
    layerResetCellScale s B T h = (layerResetThreshold s B T (h + 1)) ^ 2 := by
  have heq : s + 1 - (h + 1) = s - h := by omega
  simp only [layerResetCellScale, layerResetThreshold, heq, ← pow_mul]
  congr 1
  omega

theorem layerResetCellScale_ge {s B T h : ℕ} (hB : 0 < B) (hT : 0 < T) :
    T ≤ layerResetCellScale s B T h := by
  rw [layerResetCellScale_sq]
  exact (layerResetThreshold_ge hB hT).trans
    ((Nat.pow_one _).symm.trans_le (Nat.pow_le_pow_right (layerResetThreshold_pos hT) (by omega)))

theorem layerResetCellScale_power {s B T h : ℕ} (hh : h ≤ s) :
    layerResetCellScale s B T h ^ B = layerResetThreshold s B T h := by
  have heq : s + 1 - h = (s - h) + 1 := by omega
  simp only [layerResetCellScale, layerResetThreshold, heq, ← pow_mul, pow_succ]
  congr 1
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FixedPathSlicedSourceErrorScalar
namespace OAI

section

namespace Erdos3

def fixedPathSlicedSourceError (rP rG C K Kφ ε η ξ : ℝ) : ℝ :=
  rP + (2 * ((2 * C + 2 * K) * rP + K * ε) + 2 * η) +
    (1 + 4 * C + 3 * Kφ) * rG + Kφ * ξ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteEqualityPatternCard
namespace OAI

section

namespace Erdos3

variable {N : ℕ}

noncomputable def finitePatternRepresentative (r : Setoid (Fin N)) (i : Fin N) : Fin N := by
  classical
  exact (Finset.univ.filter (fun j => r i j)).min'
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, r.refl' i⟩⟩

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

noncomputable def finiteSectionIntegral (w : ℕ → X → ℝ) :
    (n : ℕ) → (Fin n → Bool) → ((Fin n → X) → ℝ) → (Fin n → X) → ℝ
  | 0, _, f, _ => f (fun i => Fin.elim0 i)
  | n + 1, s, f, z =>
      if s (Fin.last n) then
        finiteSectionIntegral w n (Fin.init s)
          (fun v => f (Fin.snoc v (z (Fin.last n)))) (Fin.init z)
      else
        finiteSectionIntegral w n (Fin.init s)
          (fun v => ∑ a, w n a * f (Fin.snoc v a)) (Fin.init z)

noncomputable def finiteSectionL2Norm (w : ℕ → X → ℝ) (n : ℕ)
    (s : Fin n → Bool) (f : (Fin n → X) → ℝ) (z : Fin n → X) : ℝ :=
  Real.sqrt (finiteSectionIntegral w n s (fun v => f v ^ 2) z)

def finiteSectionCount {n : ℕ} (s : Fin n → Bool) : ℕ :=
  ∑ i, if s i then 1 else 0

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

noncomputable def finiteWeightedL2Map (w : X → ℝ) : (X → ℝ) →ₗ[ℝ] EuclideanSpace ℝ X where
  toFun f := WithLp.toLp 2 (fun x => Real.sqrt (w x) * f x)
  map_add' f g := by
    ext x
    change Real.sqrt (w x) * (f x + g x) = Real.sqrt (w x) * f x + Real.sqrt (w x) * g x
    ring
  map_smul' c f := by
    ext x
    change Real.sqrt (w x) * (c * f x) = c * (Real.sqrt (w x) * f x)
    ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finiteSectionCount_eq_card (n : ℕ) (s : Fin n → Bool) :
    finiteSectionCount s = Fintype.card {i : Fin n // s i = true} := by
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  rfl

theorem finiteSection_free_card (n : ℕ) (s : Fin n → Bool) :
    Fintype.card {i : Fin n // s i ≠ true} = n - finiteSectionCount s := by
  rw [Fintype.card_subtype_compl, Fintype.card_fin, finiteSectionCount_eq_card]

noncomputable def finiteSectionFreeOrder (n : ℕ) (s : Fin n → Bool) :
    Fin (n - finiteSectionCount s) ≃o {i : Fin n // s i ≠ true} :=
  Fintype.orderIsoFinOfCardEq _ (finiteSection_free_card n s)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

noncomputable def finiteSectionWeight (w : X → ℝ) (b : Bool) (z x : X) : ℝ := by
  classical
  exact if b then (if x = z then 1 else 0) else w x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteMixedPermutation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteMixedLpCore (p E : ℕ → ℝ) : ℕ → ℝ
  | 0 => E 0 ^ (2 / p 0)
  | n + 1 => finiteMixedLpCore p E n * E (n + 1) ^ (2 / p (n + 1) - 2 / p n)

noncomputable def finiteMixedLpBound (p E : ℕ → ℝ) : ℕ → ℝ
  | 0 => E 0
  | n + 1 => finiteMixedLpCore p E n * E (n + 1) ^ (1 - 2 / p n)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteHypergraphAbstract
namespace OAI

section

namespace Erdos3

variable {X : Type*} [Fintype X]

noncomputable def finiteMaskedWeights (w : ℕ → X → ℝ) (s : ℕ → Bool)
    (x₀ : X) (i : ℕ) : X → ℝ :=
  finiteSectionWeight (w i) (!(s i)) x₀

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteMixedArrayRefresh
namespace OAI

section

namespace Erdos3

variable {A B J K C V S T U W : Type*}

def mixedArrayEmbedding (e : A ↪ J) (d : B ↪ K) : A ⊕ B ↪ J ⊕ (K ⊕ C) where
  toFun := Sum.elim (fun a => Sum.inl (e a)) (fun b => Sum.inr (Sum.inl (d b)))
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (e.injective (Sum.inl.inj h))
      | inr b => cases h
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b => exact congrArg Sum.inr (d.injective (Sum.inl.inj (Sum.inr.inj h)))

@[simp] theorem mixedArrayEmbedding_inl (e : A ↪ J) (d : B ↪ K) (a : A) :
    mixedArrayEmbedding (C := C) e d (Sum.inl a) = Sum.inl (e a) := rfl

@[simp] theorem mixedArrayEmbedding_inr (e : A ↪ J) (d : B ↪ K) (b : B) :
    mixedArrayEmbedding (C := C) e d (Sum.inr b) = Sum.inr (Sum.inl (d b)) := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalL1SourceAccuracy
namespace OAI

section

namespace Erdos3

noncomputable def l1SourceAccuracy (target spatialCap spatialVolume : ℝ) : ℝ :=
  Real.exp (-(target + spatialCap + spatialVolume + 8))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AnisotropicSmoothPairLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix NNReal

noncomputable def smoothPairProbabilityCap {J : Type*} [Fintype J] [DecidableEq J]
    (k : J) (Q : ℕ) (C κ : ℝ) : ℝ :=
  1 + (Q : ℝ) * (2 * (4 * C / κ) ^ 2 * 2 ^ Fintype.card {j : J // j ≠ k})

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SmoothPairPhysicalGrid
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def smoothPairKernelBaseCap {J : Type*} [Fintype J] [DecidableEq J]
    (k : J) (C κ : ℝ) : ℝ≥0 :=
  Real.toNNReal (1 + 2 * (4 * C / κ) ^ 2 * 2 ^ Fintype.card {j : J // j ≠ k})

noncomputable def smoothPairKernelCap {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (C κ : ℝ) : ℝ≥0 := (smoothPairKernelBaseCap k C κ) ^ n

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothPairErrorLogBounds
namespace OAI

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem smoothPairScaleRatio_le_exp {C κ P : ℝ}
    (hC0 : 0 ≤ C) (hκ0 : 0 < κ) (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P) :
    4 * C / κ ≤ Real.exp (2 * P + 4) := by
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  rw [div_eq_mul_inv]
  calc
    _ ≤ Real.exp 4 * Real.exp P * Real.exp P := by gcongr
    _ = _ := by simp only [← Real.exp_add]; congr 1; ring

theorem smoothPairQuadraticFactor_le_exp (k : J) {C κ P : ℝ}
    (hC0 : 0 ≤ C) (hκ0 : 0 < κ) (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    2 * (4 * C / κ) ^ 2 * 2 ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp (5 * P + 10) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hU := smoothPairScaleRatio_le_exp hC0 hκ0 hC hκ
  calc
    _ ≤ Real.exp 2 * (Real.exp (2 * P + 4)) ^ 2 * Real.exp P := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul]; simp only [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

noncomputable def smoothPairRowErrorLog (d : ℕ) (P : ℝ) : ℝ :=
  (16 + 4 * d) * P + 16 * d + 48

theorem smoothPairRowErrorLog_nonneg (d : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ smoothPairRowErrorLog d P := by
  unfold smoothPairRowErrorLog
  positivity

noncomputable def smoothPairErrorLog (n d : ℕ) (P : ℝ) : ℝ :=
  P + smoothPairRowErrorLog d P + n * (smoothPairRowErrorLog d P + 6 * P + 12)

theorem smoothPairErrorLog_nonneg (n d : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ smoothPairErrorLog n d P := by
  have hr := smoothPairRowErrorLog_nonneg d hP
  unfold smoothPairErrorLog
  positivity

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

theorem modEq_selected_prod_iff {ι : Type*} [DecidableEq ι]
    (q : ι → ℕ) (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (I : Finset ι) (a b : ℤ) :
    a ≡ b [ZMOD ((∏ i ∈ I, q i : ℕ) : ℤ)] ↔ ∀ i ∈ I, a ≡ b [ZMOD (q i : ℤ)] := by
  induction I using Finset.induction_on with
  | empty => simp [Int.ModEq]
  | @insert i I hi ih =>
    have hc : (q i).Coprime (∏ j ∈ I, q j) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro j hj
      apply hcop
      intro heq
      subst j
      exact hi hj
    have hci : Int.natAbs (q i : ℤ) |>.Coprime (Int.natAbs ((∏ j ∈ I, q j : ℕ) : ℤ)) := by
      simpa only [Int.natAbs_natCast] using hc
    rw [Finset.prod_insert hi, Nat.cast_mul, ← Int.modEq_and_modEq_iff_modEq_mul hci, ih]
    simp only [Finset.mem_insert, forall_eq_or_imp]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteKernelSumBound
namespace OAI

section

namespace Erdos3

variable {S I : Type*}

def kernelFiberEmbeddingEquiv (r : Setoid S) :
    {a : S → I // Setoid.ker a = r} ≃ (Quotient r ↪ I) where
  toFun a := ⟨Quotient.lift a.1 a.2.symm.le,
    (Setoid.lift_injective_iff_ker_eq_of_le a.2.symm.le).mpr a.2⟩
  invFun b := ⟨fun i => b (Quotient.mk'' i), by
    apply Setoid.ext
    intro i j
    change b (Quotient.mk'' i) = b (Quotient.mk'' j) ↔ r i j
    rw [b.injective.eq_iff, Quotient.eq]⟩
  left_inv a := by
    apply Subtype.ext
    rfl
  right_inv b := by
    apply Function.Embedding.ext
    intro i
    induction i using Quotient.inductionOn with
    | h i => rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductTensorGroupedBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {J I : Type*} {X : I → Type*}

def finiteTaggedTupleEquiv : (J → Sigma X) ≃ Σ a : J → I, ∀ j, X (a j) where
  toFun z := ⟨fun j => (z j).1, fun j => (z j).2⟩
  invFun z j := ⟨z.1 j, z.2 j⟩
  left_inv z := by funext j; exact Sigma.eta (z j)
  right_inv z := by cases z; rfl

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

theorem modEq_nat_lcm_iff (m n : ℕ) (a b : ℤ) :
    a ≡ b [ZMOD (m.lcm n : ℤ)] ↔ a ≡ b [ZMOD (m : ℤ)] ∧ a ≡ b [ZMOD (n : ℤ)] := by
  constructor
  · intro h
    exact ⟨h.of_dvd (by exact_mod_cast Nat.dvd_lcm_left m n),
      h.of_dvd (by exact_mod_cast Nat.dvd_lcm_right m n)⟩
  · rintro ⟨hm, hn⟩
    exact Int.modEq_iff_dvd.mpr (Int.coe_lcm_dvd hm.dvd hn.dvd)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PhysicalGridCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem normalizedGridLength_bounds (N : ℕ) (H ρ : ℝ)
    (hlarge : 4 ≤ ρ * H) (hwhole : ρ * H ≤ 2 * (N : ℝ)) :
    0 < ⌊ρ * H / 2⌋₊ ∧ ⌊ρ * H / 2⌋₊ ≤ N ∧
      ρ * H / 4 ≤ (⌊ρ * H / 2⌋₊ : ℝ) ∧ (⌊ρ * H / 2⌋₊ : ℝ) ≤ ρ * H / 2 := by
  have hpos : 0 < ⌊ρ * H / 2⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hN : ⌊ρ * H / 2⌋₊ ≤ N := Nat.floor_le_of_le (by linarith)
  have hup : (⌊ρ * H / 2⌋₊ : ℝ) ≤ ρ * H / 2 := Nat.floor_le (by linarith)
  have hnext := Nat.lt_floor_add_one (ρ * H / 2)
  exact ⟨hpos, hN, by linarith, hup⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalPairAccuracyLogBounds
namespace OAI

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

noncomputable def physicalPairCoefficientLog (n d : ℕ) (P : ℝ) : ℝ :=
  30 + 2 * n * P + 2 * n + smoothPairErrorLog n d P +
    n * (5 * P + 11) + 10 * P + 4 * (2 + d)

theorem physicalPairCoefficientLog_bounds (n d : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ physicalPairCoefficientLog n d P ∧
    P ≤ physicalPairCoefficientLog n d P ∧
    6 + 2 * n * P + 2 * n + smoothPairErrorLog n d P ≤ physicalPairCoefficientLog n d P ∧
    2 + 4 * (2 + d) + P ≤ physicalPairCoefficientLog n d P ∧
    20 + 2 * n * P + 2 * n + n * (5 * P + 11) + 9 * P ≤ physicalPairCoefficientLog n d P := by
  have hF := smoothPairErrorLog_nonneg n d hP
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hnp := mul_nonneg hn hP
  unfold physicalPairCoefficientLog
  constructor
  · positivity
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem physicalPairPowerBounds (n : ℕ) {A P : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ Real.exp P) :
    A ^ (2 * n) ≤ Real.exp (2 * n * P) ∧ (2 : ℝ) ^ n ≤ Real.exp (2 * n) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  constructor
  · apply (pow_le_pow_left₀ hA0 hA (2 * n)).trans_eq
    rw [← Real.exp_nat_mul]
    push_cast
    rfl
  · apply (pow_le_pow_left₀ (by norm_num) h2 n).trans_eq
    rw [← Real.exp_nat_mul]
    congr 1
    ring

noncomputable def physicalPairMeanLog (n degree : ℕ) (P : ℝ) : ℝ :=
  2 * ((degree : ℝ) * (P + 2) + 2) + 4 + 2 * n * P + n * (5 * P + 11) + P

theorem physicalPairMeanLog_bounds (n degree : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ physicalPairMeanLog n degree P ∧ P ≤ physicalPairMeanLog n degree P := by
  unfold physicalPairMeanLog
  constructor
  · positivity
  · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hd : (0 : ℝ) ≤ degree := Nat.cast_nonneg _
    nlinarith [mul_nonneg hn hP, mul_nonneg hd hP]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalOutputAxisReindex
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

def outputAxisReindexAddEquiv {A B : Type*} (e : A ≃ B)
    (H : Type*) [AddCommGroup H] : (A → H) ≃+ (B → H) where
  toFun x b := x (e.symm b)
  invFun y a := y (e a)
  left_inv x := by funext a; simp
  right_inv y := by funext b; simp
  map_add' _ _ := rfl

@[simp] theorem outputAxisReindexAddEquiv_apply {A B H : Type*} [AddCommGroup H]
    (e : A ≃ B) (x : A → H) (b : B) :
    outputAxisReindexAddEquiv e H x b = x (e.symm b) := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBoxCutoffLogBounds
namespace OAI

section

namespace Erdos3

noncomputable def integerBoxGcdCutoff (d : ℕ) (C epsilon : ℝ) : ℕ :=
  ⌈2 * (2 : ℝ) ^ (d - 1) * (1 + C) / epsilon⌉₊ + 1

noncomputable def integerBoxNearRatio (d : ℕ) (epsilon : ℝ) : ℝ :=
  replacementAccuracy (2 * (3 : ℝ) ^ d) epsilon

noncomputable def integerBoxPairScale (d : ℕ) (C epsilon : ℝ) : ℝ :=
  max (integerBoxGcdCutoff d C epsilon : ℝ) (1 / integerBoxNearRatio d epsilon)

noncomputable def integerBoxRetainedGap (d D : ℕ) (c epsilon : ℝ) : ℝ :=
  (D : ℝ) * integerBoxNearRatio d epsilon * c

theorem integerBoxNearRatio_spec (d : ℕ) {epsilon : ℝ} (heps : 0 < epsilon) :
    0 < integerBoxNearRatio d epsilon ∧ integerBoxNearRatio d epsilon ≤ 1 ∧
      (3 : ℝ) ^ d * integerBoxNearRatio d epsilon ≤ epsilon / 2 := by
  have h := replacementAccuracy_spec (by positivity : 0 ≤ 2 * (3 : ℝ) ^ d) heps
  change 0 < integerBoxNearRatio d epsilon ∧ integerBoxNearRatio d epsilon ≤ 1 ∧
    2 * (3 : ℝ) ^ d * integerBoxNearRatio d epsilon ≤ epsilon at h
  exact ⟨h.1, h.2.1, by linarith [h.2.2]⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmallWeightedPhysicalReplacement
namespace OAI

section

namespace Erdos3

theorem replacementSampledEnergy_le_exp (n : ℕ) {A P : ℝ}
    (hA0 : 0 ≤ A) (hA : A ≤ Real.exp P) :
    (2 : ℝ) ^ (n + 1) * A ^ n ≤ Real.exp ((n : ℝ) * P + 2 * (n + 1)) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  calc
    _ ≤ (Real.exp 2) ^ (n + 1) * (Real.exp P) ^ n :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num) h2 _) (pow_le_pow_left₀ hA0 hA _)
        (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; push_cast; congr 1; ring

noncomputable def physicalReplacementInputLog (m n : ℕ) (P : ℝ) : ℝ :=
  (m : ℝ) * (P + 3) + n * P + 2 * (n + 1) + P + 1

theorem physicalReplacementInputLog_nonneg (m n : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ physicalReplacementInputLog m n P := by
  unfold physicalReplacementInputLog
  positivity

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

noncomputable def physicalReplacementThresholdLog (n d degree : ℕ) (P : ℝ) : ℝ :=
  2 * physicalPairCoefficientLog n d P + 2 * physicalPairMeanLog n degree P +
    (2 * degree + 2) * P + 20

theorem physicalReplacementThresholdLog_bounds (n d degree : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ physicalReplacementThresholdLog n d degree P ∧
    P + 8 ≤ physicalReplacementThresholdLog n d degree P ∧
    2 * physicalPairCoefficientLog n d P + 2 ≤ physicalReplacementThresholdLog n d degree P ∧
    2 * physicalPairMeanLog n degree P + 2 + (2 * degree + 1) * P + 1 ≤
      physicalReplacementThresholdLog n d degree P := by
  have hc := (physicalPairCoefficientLog_bounds n d hP).1
  have hm := (physicalPairMeanLog_bounds n degree hP).1
  have hdegree : (0 : ℝ) ≤ degree := Nat.cast_nonneg _
  have hprod := mul_nonneg hdegree hP
  unfold physicalReplacementThresholdLog
  constructor
  · positivity
  constructor
  · nlinarith
  constructor <;> nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FixedSpatialEmptyCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {X : Type*}

def fixedSpatialEmptyIndex : (Σ _ : X, Unit ⊕ Empty) ≃ X where
  toFun a := a.1
  invFun x := ⟨x, .inl ()⟩
  left_inv a := by
    rcases a with ⟨x, u | e⟩
    · cases u
      rfl
    · exact isEmptyElim e
  right_inv _ := rfl

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

variable {m d a : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

def layerIntegerRestriction (e : Fin d ≃ Sigma J) (j : Fin m) :
    (Fin d → ℤ) →ₗ[ℤ] (J j → ℤ) where
  toFun β i := β (e.symm ⟨j, i⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ContainedKernelPhysicalDisplacement
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]

def fixedSpatialKernelBlockCoordinates (e : G ≃ X ⊕ (X ⊕ T))
    (t : G → ℝ) : (T → ℝ) × ((X → ℝ) × (X → ℝ)) :=
  (fun j => t (e.symm (.inr (.inr j))),
    (fun i => t (e.symm (.inl i)), fun i => t (e.symm (.inr (.inl i)))))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDifferencePermanentBlocks
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {R : Type*} [CommSemiring R]

noncomputable def permanentPolynomial (n : ℕ) : MvPolynomial (Fin n × Fin n) R :=
  Matrix.permanent (fun i j => X (i, j))

noncomputable def permanentExponent (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (Fin n × Fin n) →₀ ℕ := ∑ i, Finsupp.single (σ i, i) 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ForecastComparisonFloorPolynomialBudget
namespace OAI

section

namespace Erdos3

def forecastComparisonMeshPolynomial (t grid : ℝ) : ℝ :=
  (2 * t + 1) * (grid + t + 9) + 12 * t + 2 * grid + t + 12

def forecastComparisonFloorPolynomial (t source grid : ℝ) : ℝ :=
  (5 * t + 2 * source + 32) +
    (4 * t + grid + forecastComparisonMeshPolynomial t grid + 12)

end Erdos3

end

end OAI
end


