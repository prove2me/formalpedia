-- Prove2me | Definitions.Def_InfoLossLAR_NativeBundle_01
-- name    : InfoLossLAR_NativeBundle_01
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T10:55:45.93667+00:00
-- url     : https://prove2.me/theorems/dc9454a1-08fe-4b1c-8f00-62e55a8f7b0d
-- title:
--   Gaussian, finite-response, and local-calibration data
-- statement:
--   This package supplies the analytic and finite algebraic objects used by the local affine calibration construction. It includes integer Gaussian weights and their normalized law, finite quantization and convolution routines, physical block tensors, canonical coefficient kernels, and finite inverse and chart interfaces.
--
--   For a positive width $\sigma$, the integer Gaussian uses the convention
--   $$\Pr[Z=z]=\frac{\exp(-\pi z^2/\sigma^2)}{\sum_{u\in\mathbb Z}\exp(-\pi u^2/\sigma^2)}.$$
--   The finite response objects describe public calibration of protected inputs. Their numerical implementations retain exact rational data separately from the ideal real laws.
--
--   These definitions form the common language for later local error and response theorems. Supporting proofs are retained only where needed to construct this data.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0, native lean source modules: lean/AFT/Inverse.lean, lean/AFT/Calibration.lean, lean/AFT/LocalResponse.lean, lean/AFT/FockGaussian.lean, lean/AFT/HistogramTail.lean, lean/AFT/TensorFock.lean, lean/AFT/NonlinearFock.lean, lean/AFT/SelectionBound.lean, lean/AFT/BlockDensity.lean, lean/AFT/LocalTensors.lean, lean/AFT/PhysicalBlockTensors.lean, lean/AFT/ActivatedPair.lean, lean/AFT/Negligible.lean, lean/AFT/GaussianSource.lean, lean/AFT/GaussianTail.lean, lean/AFT/RootSlice.lean, lean/AFT/ClippedSource.lean, lean/AFT/ActivationParameters.lean, lean/AFT/ActualLegCutoffProgram.lean, lean/AFT/MixedActivity.lean, lean/AFT/Anchor.lean, lean/AFT/FinitePrimaryInverse.lean, lean/AFT/Parameters.lean, lean/AFT/TrimmedSlice.lean, lean/AFT/PrimaryCalibration.lean, lean/AFT/Charge.lean, lean/AFT/TrimmedPalette.lean, lean/AFT/SignCalibration.lean, lean/AFT/SignCalibrationParameters.lean, lean/AFT/BetaPrimaryCalibration.lean, lean/AFT/V7PrimaryCalibration.lean, lean/AFT/BackgroundMeanBounds.lean, lean/AFT/RootMarginal.lean, lean/AFT/RootWindow.lean, lean/AFT/GaussianReflection.lean, lean/AFT/ClippedConvolution.lean, lean/AFT/RootErrorParameters.lean, lean/AFT/BodyBlur.lean, lean/AFT/FiniteRetype.lean, lean/AFT/FiniteExpectationAlgebra.lean, lean/AFT/FiniteTicketSampler.lean, lean/AFT/FiniteQuantization.lean, lean/AFT/QuantizedSampling.lean, lean/AFT/FairBitSampling.lean, lean/AFT/RationalFiniteQuantization.lean, lean/AFT/RationalPiProgram.lean, lean/AFT/RationalExpProgram.lean, lean/AFT/RationalGaussianProgram.lean, lean/AFT/FiniteConvolutionProgram.lean, lean/AFT/RootConvolutionProgram.lean, lean/AFT/SignedConditioning.lean, lean/AFT/RationalWindowGaussian.lean, lean/AFT/RationalWindowTickets.lean, lean/AFT/ActualAuxiliaryGaussianProgram.lean, lean/AFT/BodyBlurParameters.lean, lean/AFT/V7ActualMeans.lean, lean/AFT/InverseMixedActivity.lean, lean/AFT/V7PrimaryInverse.lean, lean/AFT/AnchorMean.lean, lean/AFT/V7SafeProjection.lean, lean/AFT/AnchorSeed.lean, lean/AFT/ActualBodyCenter.lean, lean/AFT/TrimmedPair.lean, lean/AFT/SafePairCore.lean, lean/AFT/ActualTriples.lean, lean/AFT/PairWindowTranslation.lean, lean/AFT/MaskedWindowTranslation.lean, lean/AFT/HilbertConcentration.lean, lean/AFT/ProfileHilbert.lean, lean/AFT/TripleMarginals.lean, lean/AFT/BlockProducts.lean, lean/AFT/FiniteBlockNumbering.lean, lean/AFT/V7ReferenceLaws.lean, lean/AFT/V7Blocks.lean, lean/AFT/PublicPlacement.lean, lean/AFT/V7PublicPlacement.lean, lean/AFT/ActualNormalizedMean.lean, lean/AFT/BetaReference.lean, lean/AFT/FiniteConvolution.lean, lean/AFT/SafeFiniteNeumann.lean, lean/AFT/CanonicalConvolution.lean, lean/AFT/CoreProjectionEnergy.lean, lean/AFT/CoreCenteringDifference.lean, lean/AFT/SmoothingDifference.lean, lean/AFT/CanonicalSmoothing.lean, lean/AFT/CoreWindowKernel.lean, lean/AFT/MixedKernel.lean, lean/AFT/MixedCoordinateOperator.lean, lean/AFT/MixedCoordinateIteration.lean, lean/AFT/MixedTensor.lean, lean/AFT/V7RootSmoothing.lean, lean/AFT/PairErrorAssembly.lean, lean/AFT/PairCoreNumerics.lean, lean/AFT/CanonicalMoments.lean, lean/AFT/CollisionCounting.lean, lean/AFT/CollisionOccurrences.lean, lean/AFT/MixedTransfer.lean, lean/AFT/FiniteRefresh.lean, lean/AFT/CollisionGraph.lean, lean/AFT/GraphScopes.lean, lean/AFT/HistogramNormalization.lean, lean/AFT/SymmetricCoefficients.lean, lean/AFT/ReindexedCoefficients.lean, lean/AFT/CanonicalVariance.lean, lean/AFT/PlacedFibers.lean, lean/AFT/PatternContractions.lean, lean/AFT/ReflectionCalibration.lean, lean/AFT/RepresentedPolynomial.lean, lean/AFT/RepresentedTruncation.lean, lean/AFT/RepresentedQueue.lean, lean/AFT/RepresentedRing.lean, lean/AFT/RepresentedOutput.lean, lean/AFT/MeanOutput.lean, lean/AFT/CenteredPolynomial.lean, lean/AFT/FormalLogarithm.lean, lean/AFT/HistogramGenerating.lean, lean/AFT/MixedCoordinateProducts.lean, lean/AFT/JointPairOutput.lean, lean/AFT/RepresentedControlKernel.lean, lean/AFT/ActualBetaReference.lean, lean/AFT/BetaRationalCDF.lean, lean/AFT/BetaGridLaw.lean, lean/AFT/BetaFiniteSampler.lean, lean/AFT/ActualRootGaussianProgram.lean, lean/AFT/ActualRootIntegerProgram.lean, lean/AFT/ActualRootGaussianTickets.lean, lean/AFT/ConditionalRepair.lean, lean/AFT/Rejection.lean, lean/AFT/FiniteConditionProgram.lean, lean/AFT/BetaIntegerCDF.lean, lean/AFT/BetaCountedArithmetic.lean, lean/AFT/BetaCountedSearch.lean, lean/AFT/ParameterProgram.lean, lean/AFT/ActualRootSamplerProgram.lean, lean/AFT/ActualRootTicketConvolution.lean, lean/AFT/ActualRootMarginalProgram.lean, lean/AFT/ActualBodyBlurProgram.lean, lean/AFT/ActualBodyMeanProgram.lean, lean/AFT/ActualSliceMeanProgram.lean. Migrated source units selected by the Lean declaration and syntax oracles; exact source body hashes and original module paths recorded in Integration9_9/provenance/full_project_extraction/native_definition_bundles/manifest.json. Bundle SHA256 87c0b11fcec7fbe5e95ed94fe1a304b87ad40b7235950f3a109207cbc0632db2.

import Definitions.Def_InfoLossLAR_Native_AFT_BlockFock
import Definitions.Def_InfoLossLAR_Native_AFT_FiniteConcentration
import Definitions.Def_InfoLossLAR_Native_AFT_FiniteProbability
import Definitions.Def_InfoLossLAR_Native_AFT_Hoeffding
import Definitions.Def_InfoLossLAR_Native_AFT_TotalVariation
import Definitions.Def_InfoLossLAR_Native_AFT_TransportBound
import Mathlib
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Rat.Floor
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

section


namespace AFT
end AFT
namespace AFT.finiteCorrection
end AFT.finiteCorrection


/-!
# Exact local inverse and boundary-preserving input projection

The rank-one inverse is the actual formula used in V7 Lemma 9.5.  Its
nonzero denominator is proved from an explicit smallness condition below.
The boundary collapse is defined on finite signed profiles and its
projection and preservation identities are proved directly.  These results
do not supply the unformalized model-dependent mixed-fiber estimates.
-/

namespace AFT

open scoped BigOperators

section RankOne

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- The rank-one operator `v ⊗ χ`, acting on signed primary profiles. -/
def profileRankOne (v : V) (χ : V →ₗ[𝕜] 𝕜) : V →ₗ[𝕜] V :=
  χ.smulRight v

@[simp] theorem profileRankOne_apply (v : V) (χ : V →ₗ[𝕜] 𝕜) (x : V) :
    profileRankOne v χ x = χ x • v := rfl

/-- The preconditioner `Id + ρ⁻¹ v ⊗ χ` from the local-response proof. -/
def primaryRankOperator (ρ : 𝕜) (v : V) (χ : V →ₗ[𝕜] 𝕜) : V →ₗ[𝕜] V :=
  LinearMap.id + ρ⁻¹ • profileRankOne v χ

/-- The explicit Sherman--Morrison inverse appearing in V7. -/
def primaryRankInverse (ρ : 𝕜) (v : V) (χ : V →ₗ[𝕜] 𝕜) : V →ₗ[𝕜] V :=
  LinearMap.id - (ρ + χ v)⁻¹ • profileRankOne v χ

@[simp] theorem primaryRankOperator_apply (ρ : 𝕜) (v : V)
    (χ : V →ₗ[𝕜] 𝕜) (x : V) :
    primaryRankOperator ρ v χ x = x + (ρ⁻¹ * χ x) • v := by
  simp [primaryRankOperator, smul_smul]

@[simp] theorem primaryRankInverse_apply (ρ : 𝕜) (v : V)
    (χ : V →ₗ[𝕜] 𝕜) (x : V) :
    primaryRankInverse ρ v χ x = x - ((ρ + χ v)⁻¹ * χ x) • v := by
  simp [primaryRankInverse, smul_smul]

/-- The left inverse is an algebraic identity, with the two necessary
nonvanishing assumptions exposed. -/
theorem primaryRankInverse_left (ρ : 𝕜) (v : V) (χ : V →ₗ[𝕜] 𝕜)
    (hρ : ρ ≠ 0) (hden : ρ + χ v ≠ 0) (x : V) :
    primaryRankInverse ρ v χ (primaryRankOperator ρ v χ x) = x := by
  rw [primaryRankInverse_apply, primaryRankOperator_apply]
  simp only [map_add, map_smul, smul_eq_mul]
  have hc : (ρ + χ v)⁻¹ * (χ x + (ρ⁻¹ * χ x) * χ v) = ρ⁻¹ * χ x := by
    field_simp
  rw [hc]
  abel

/-- The same formula is also a right inverse; no finite-dimensionality is
used in either algebraic direction. -/
theorem primaryRankInverse_right (ρ : 𝕜) (v : V) (χ : V →ₗ[𝕜] 𝕜)
    (hρ : ρ ≠ 0) (hden : ρ + χ v ≠ 0) (x : V) :
    primaryRankOperator ρ v χ (primaryRankInverse ρ v χ x) = x := by
  rw [primaryRankOperator_apply, primaryRankInverse_apply]
  simp only [map_sub, map_smul, smul_eq_mul]
  have hc : ρ⁻¹ * (χ x - ((ρ + χ v)⁻¹ * χ x) * χ v) =
      (ρ + χ v)⁻¹ * χ x := by
    field_simp
    ring
  rw [hc]
  abel

/-- A linear equivalence whose inverse is the displayed rank-one formula. -/
def primaryRankEquiv (ρ : 𝕜) (v : V) (χ : V →ₗ[𝕜] 𝕜)
    (hρ : ρ ≠ 0) (hden : ρ + χ v ≠ 0) : V ≃ₗ[𝕜] V where
  toLinearMap := primaryRankOperator ρ v χ
  invFun := primaryRankInverse ρ v χ
  left_inv := primaryRankInverse_left ρ v χ hρ hden
  right_inv := primaryRankInverse_right ρ v χ hρ hden





end RankOne

/-- The V7 condition `|χ(v)| < ρ` supplies the denominator, rather than
assuming existence of an inverse. -/
theorem primaryRank_denominator_pos (ρ scalar : ℝ) (hsmall : |scalar| < ρ) :
    0 < ρ + scalar := by
  have := (abs_lt.mp hsmall).1
  linarith



section ContinuousLocalInverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





variable [CompleteSpace E]





end ContinuousLocalInverse

section BoundaryCollapse

variable {ι : Type*} [DecidableEq ι]

/-- Collapse the interior mass according to the primary law and keep every
boundary coordinate. `interior` is the complement of the boundary palette. -/
noncomputable def boundaryCollapse (interior : Finset ι) (primary : ι → ℝ) :
    (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun profile color := if color ∈ interior then
    (∑ i ∈ interior, profile i) / (∑ i ∈ interior, primary i) * primary color
    else profile color
  map_add' x y := by
    funext color
    simp only [Pi.add_apply]
    split_ifs <;> simp [Finset.sum_add_distrib, add_div, add_mul]
  map_smul' scalar x := by
    funext color
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp [← Finset.mul_sum, mul_div_assoc, mul_assoc]

@[simp] theorem boundaryCollapse_boundary (interior : Finset ι) (primary profile : ι → ℝ)
    (color : ι) (hcolor : color ∉ interior) :
    boundaryCollapse interior primary profile color = profile color := by
  simp [boundaryCollapse, hcolor]

@[simp] theorem boundaryCollapse_interior (interior : Finset ι) (primary profile : ι → ℝ)
    (color : ι) (hcolor : color ∈ interior) :
    boundaryCollapse interior primary profile color =
      (∑ i ∈ interior, profile i) / (∑ i ∈ interior, primary i) * primary color := by
  simp [boundaryCollapse, hcolor]





/-- The one-coordinate boundary ideal projector from V7. -/
noncomputable def boundaryIdealProjection (interior : Finset ι) (primary : ι → ℝ) :
    (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := LinearMap.id - boundaryCollapse interior primary

@[simp] theorem boundaryIdealProjection_boundary (interior : Finset ι)
    (primary profile : ι → ℝ) (color : ι) (hc : color ∉ interior) :
    boundaryIdealProjection interior primary profile color = 0 := by
  simp [boundaryIdealProjection, hc]







end BoundaryCollapse

section ConjugatedProjection

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- Conjugate the output boundary projection by the constructed primary
inverse. This implements the all-primary legal input projection. -/
def legalInputProjection (A : V ≃ₗ[𝕜] V) (P : V →ₗ[𝕜] V) : V →ₗ[𝕜] V :=
  A.symm.toLinearMap.comp (P.comp A.toLinearMap)

@[simp] theorem legalInputProjection_evaluation (A : V ≃ₗ[𝕜] V)
    (P : V →ₗ[𝕜] V) (input : V) :
    A (legalInputProjection A P input) = P (A input) := by
  simp [legalInputProjection]





end ConjugatedProjection

end AFT

end

section




/-!
# Exact finite calibration identities from reference V7

This module defines V7's base primary profile, beta repair, compensated body
profile, and reference mean. The calibration and normalization identities
are checked without assuming the desired identity. The analytic estimates
for the particular Gaussian, anchor, and trimmed-slice profiles remain
separate obligations; arbitrary profiles are not asserted to be positive.
-/

namespace AFT

open scoped BigOperators

section Calibration

variable {ι : Type*}

/-- Total mass of a finite signed color profile. -/
def signedProfileMass [Fintype ι] : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun profile := ∑ color, profile color
  map_add' x y := Finset.sum_add_distrib
  map_smul' scalar x := by simp [← Finset.mul_sum]

@[simp] theorem signedProfileMass_apply [Fintype ι] (profile : ι → ℝ) :
    signedProfileMass profile = ∑ color, profile color := rfl

/-- The exact numerator in equation (9.5), divided by the total mark mass. -/
noncomputable def basePrimaryProfile (dimension bodies legs activation : ℝ)
    (uniform bodyMean shiftedSlice unshiftedSlice : ι → ℝ) : ι → ℝ :=
  fun color => (dimension * uniform color - (bodies + legs * activation) * bodyMean color
    - 2 * legs * shiftedSlice color + 2 * legs * activation * unshiftedSlice color) /
      (legs * activation)

/-- The beta-dependent boundary mass repair. -/
def calibratedPrimaryProfile (base boundaryUniform interiorUniform : ι → ℝ)
    (boundaryMassChange : ℝ) : ι → ℝ :=
  base + boundaryMassChange • (boundaryUniform - interiorUniform)

/-- The compensated body profile. Positivity requires the explicit estimate
proved separately below. -/
def calibratedBodyProfile (core anchorPrimary : ι → ℝ) (compensation : ℝ) : ι → ℝ :=
  (1 + compensation) • core - compensation • anchorPrimary























end Calibration

end AFT

end

section




/-!
# Finite anchor and paired-lift estimates

These definitions instantiate the local input lift of V7 on finite primary
and safe-center alphabets. The proofs below use the actual anchor matrix
and weighted sums, rather than assuming a bounded lift as a structure field.
-/

namespace AFT

open scoped BigOperators

section FiniteProfiles

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Apply the column-stochastic public anchor law to a signed primary profile. -/
noncomputable def applyAnchor (anchor : ι → κ → ℝ) (profile : ι → ℝ) : κ → ℝ :=
  fun center => ∑ color, anchor color center * profile color

/-- Squared profile norm with respect to a positive reference law. -/
noncomputable def profileSquareNorm (reference profile : ι → ℝ) : ℝ :=
  ∑ color, profile color ^ 2 / reference color

/-- Squared density norm, with the probability weight retained explicitly. -/
noncomputable def densitySquareNorm (reference density : ι → ℝ) : ℝ :=
  ∑ color, reference color * density color ^ 2





theorem profileSquareNorm_nonneg (reference profile : ι → ℝ)
    (hreference : ∀ color, 0 ≤ reference color) :
    0 ≤ profileSquareNorm reference profile := by
  exact Finset.sum_nonneg fun color _ => div_nonneg (sq_nonneg _) (hreference color)

theorem densityScore_square (reference profile : ι → ℝ) :
    densitySquareNorm reference (fun color => profile color / reference color) =
      profileSquareNorm reference profile := by
  apply Finset.sum_congr rfl
  intro color _
  dsimp
  field_simp







omit [Fintype κ] in
/-- Finite weighted Cauchy--Schwarz for a single actual anchor output row. -/
theorem applyAnchor_square_le (primary : ι → ℝ) (anchor : ι → κ → ℝ)
    (profile : ι → ℝ) (hp : ∀ color, 0 < primary color)
    (ha : ∀ color center, 0 ≤ anchor color center) (center : κ) :
    applyAnchor anchor profile center ^ 2 ≤
      applyAnchor anchor primary center *
        ∑ color, anchor color center * (profile color ^ 2 / primary color) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro color _
    exact mul_nonneg (ha color center) (le_of_lt (hp color))
  · intro color _
    exact mul_nonneg (ha color center) (div_nonneg (sq_nonneg _) (le_of_lt (hp color)))
  · intro color _
    have hne := ne_of_gt (hp color)
    field_simp

/-- The anchor lift bound with its genuine finite row comparison.  In V7
`comparison` is `C * q / anchorWidth`, obtained from the safe body lower
bound and the public anchor interval upper bound. -/
theorem applyAnchor_profileSquareNorm_le (primary : ι → ℝ) (body : κ → ℝ)
    (anchor : ι → κ → ℝ) (profile : ι → ℝ) (comparison : ℝ)
    (hp : ∀ color, 0 < primary color) (hs : ∀ center, 0 < body center)
    (ha : ∀ color center, 0 ≤ anchor color center)
    (hamass : ∀ color, ∑ center, anchor color center = 1)
    (hcompare : ∀ center, applyAnchor anchor primary center ≤ comparison * body center) :
    profileSquareNorm body (applyAnchor anchor profile) ≤
      comparison * profileSquareNorm primary profile := by
  calc
    _ ≤ ∑ center, comparison *
        ∑ color, anchor color center * (profile color ^ 2 / primary color) := by
      apply Finset.sum_le_sum
      intro center _
      apply (div_le_iff₀ (hs center)).mpr
      have hnonneg : 0 ≤ ∑ color, anchor color center * (profile color ^ 2 / primary color) :=
        Finset.sum_nonneg fun color _ =>
          mul_nonneg (ha color center) (div_nonneg (sq_nonneg _) (le_of_lt (hp color)))
      have hrow := (applyAnchor_square_le primary anchor profile hp ha center).trans
        (mul_le_mul_of_nonneg_right (hcompare center) hnonneg)
      nlinarith only [hrow]
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hamass, one_mul]
      rfl





















end FiniteProfiles

section SignProfile

variable {ι : Type*} [Fintype ι]

/-- The sign functional on an actual finite signed profile. -/
noncomputable def signFunctional (sign profile : ι → ℝ) : ℝ :=
  ∑ color, sign color * profile color

/-- Linear-map form of the finite sign functional, used in the explicit
primary inverse rather than an uninterpreted functional parameter. -/
noncomputable def profileSignMap (sign : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun := signFunctional sign
  map_add' first second := by
    simp [signFunctional, mul_add, Finset.sum_add_distrib]
  map_smul' scalar profile := by
    simp [signFunctional, ← Finset.mul_sum, mul_left_comm]

/-- V7's sign functional is controlled by the actual L1 mass of its input. -/
theorem signFunctional_abs_le_l1 (sign profile : ι → ℝ)
    (hsign : ∀ color, |sign color| ≤ 1) :
    |signFunctional sign profile| ≤ ∑ color, |profile color| := by
  calc
    _ ≤ ∑ color, |sign color * profile color| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro color _
      rw [abs_mul]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hsign color) (abs_nonneg (profile color))

/-- Construct the finite primary rank inverse from the actual sign-profile
L1 smallness used by V7. No inverse or nonzero denominator is assumed. -/
noncomputable def finitePrimaryRankEquiv (activation : ℝ) (signProfile sign : ι → ℝ)
    (hsign : ∀ color, |sign color| ≤ 1)
    (hsmall : (∑ color, |signProfile color|) < activation) : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
  primaryRankEquiv activation signProfile (profileSignMap sign)
    (ne_of_gt ((Finset.sum_nonneg fun color _ => abs_nonneg (signProfile color)).trans_lt hsmall))
    (ne_of_gt (primaryRank_denominator_pos activation (signFunctional sign signProfile)
      ((signFunctional_abs_le_l1 sign signProfile hsign).trans_lt hsmall)))



/-- The bounded sign function has profile-dual norm at most one. -/
theorem signFunctional_sq_le (primary sign profile : ι → ℝ)
    (hp : ∀ color, 0 < primary color) (hpmass : ∑ color, primary color = 1)
    (hsign : ∀ color, |sign color| ≤ 1) :
    signFunctional sign profile ^ 2 ≤ profileSquareNorm primary profile := by
  have hc : signFunctional sign profile ^ 2 ≤
      (∑ color, primary color * sign color ^ 2) * profileSquareNorm primary profile := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro color _
      exact mul_nonneg (le_of_lt (hp color)) (sq_nonneg _)
    · intro color _
      exact div_nonneg (sq_nonneg _) (le_of_lt (hp color))
    · intro color _
      have hn := ne_of_gt (hp color)
      field_simp
  have hsignsq (color : ι) : sign color ^ 2 ≤ 1 := by
    have h := (abs_le.mp (hsign color))
    nlinarith [sq_nonneg (sign color - 1), sq_nonneg (sign color + 1)]
  have hsum : (∑ color, primary color * sign color ^ 2) ≤ 1 := by
    rw [← hpmass]
    exact Finset.sum_le_sum fun color _ => by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hsignsq color) (le_of_lt (hp color))
  have hfinal := mul_le_mul_of_nonneg_right hsum
    (profileSquareNorm_nonneg primary profile (fun color => le_of_lt (hp color)))
  exact hc.trans (by simpa only [one_mul] using hfinal)

/-- The pointwise calibrated domination and L1 mass bound imply the
weighted L2 sign-profile bound used in the explicit inverse estimate. -/
theorem signProfile_square_bound (primary signProfile : ι → ℝ) (majorant : ℝ)
    (hp : ∀ color, 0 < primary color)
    (hmajorant : ∀ color, |signProfile color| ≤ majorant * primary color) :
    profileSquareNorm primary signProfile ≤ majorant * ∑ color, |signProfile color| := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro color _
  apply (div_le_iff₀ (hp color)).mpr
  have h := mul_le_mul_of_nonneg_right (hmajorant color) (abs_nonneg (signProfile color))
  nlinarith [sq_abs (signProfile color)]

/-- Scalar multiplication is evaluated in the actual weighted profile norm. -/
theorem profileSquareNorm_smul (primary profile : ι → ℝ) (scalar : ℝ) :
    profileSquareNorm primary (scalar • profile) = scalar ^ 2 * profileSquareNorm primary profile := by
  simp only [profileSquareNorm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro color _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The nonidentity part of V7's inverse has the advertised small L2 norm
whenever its displayed L1 and pointwise calibrated bounds hold. The exact
constant squared is `majorant * l1 / denominator^2`. -/
theorem rankCorrection_profileSquareNorm_le (primary signProfile sign profile : ι → ℝ)
    (denominator majorant : ℝ) (hp : ∀ color, 0 < primary color)
    (hpmass : ∑ color, primary color = 1) (hsign : ∀ color, |sign color| ≤ 1)
    (hmajorant : 0 ≤ majorant)
    (hprofile : ∀ color, |signProfile color| ≤ majorant * primary color) :
    profileSquareNorm primary ((signFunctional sign profile / denominator) • signProfile) ≤
      (majorant * (∑ color, |signProfile color|) / denominator ^ 2) *
        profileSquareNorm primary profile := by
  rw [profileSquareNorm_smul]
  have hc := signFunctional_sq_le primary sign profile hp hpmass hsign
  have hv := signProfile_square_bound primary signProfile majorant hp hprofile
  have hl1 : 0 ≤ ∑ color, |signProfile color| := Finset.sum_nonneg fun color _ => abs_nonneg _
  calc
    _ ≤ (signFunctional sign profile / denominator) ^ 2 *
        (majorant * ∑ color, |signProfile color|) :=
      mul_le_mul_of_nonneg_left hv (sq_nonneg _)
    _ = (signFunctional sign profile ^ 2 / denominator ^ 2) *
        (majorant * ∑ color, |signProfile color|) := by rw [div_pow]
    _ ≤ (profileSquareNorm primary profile / denominator ^ 2) *
        (majorant * ∑ color, |signProfile color|) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hc (sq_nonneg denominator)) (mul_nonneg hmajorant hl1)
    _ = _ := by ring



end SignProfile

end AFT

end

section




/-! # Exact circular Gaussian moments for the finite Fock isometry -/

namespace AFT
namespace FockGaussian

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

noncomputable def component : Measure ℝ := gaussianReal 0 (1 / 2)
noncomputable def plane : Measure (ℝ × ℝ) := component.prod component
noncomputable def circular : Measure ℂ :=
  plane.map (fun point => (point.1 : ℂ) + (point.2 : ℂ) * Complex.I)

instance component_probability : IsProbabilityMeasure component :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 (1 / 2)))
instance plane_probability : IsProbabilityMeasure plane :=
  inferInstanceAs (IsProbabilityMeasure (component.prod component))
instance circular_probability : IsProbabilityMeasure circular := by
  unfold circular
  exact Measure.isProbabilityMeasure_map (by fun_prop)





























variable {Coordinate : Type*} [Fintype Coordinate]

noncomputable def field : Measure (Coordinate → ℂ) := Measure.pi (fun _ : Coordinate => circular)

instance field_probability : IsProbabilityMeasure (field (Coordinate := Coordinate)) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Coordinate => circular)))

/-- Actual monomial in finitely many complex coordinates. -/
def monomial (degree : Coordinate → ℕ) (value : Coordinate → ℂ) : ℂ :=
  ∏ coordinate, value coordinate ^ degree coordinate

/-- The monomial's exact Fock weight, a product of coordinate factorials. -/
def monomialWeight (degree : Coordinate → ℕ) : ℕ :=
  ∏ coordinate, (degree coordinate).factorial











/-- Coordinatewise complexification of two independent real Gaussian fields. -/
noncomputable def complexify (point : (Coordinate → ℝ) × (Coordinate → ℝ)) : Coordinate → ℂ :=
  fun index => (point.1 index : ℂ) + (point.2 index : ℂ) * Complex.I









end FockGaussian
end AFT

end

section







/-!
# Finite-population factorial comparison for the complete histogram tail

The estimates here cover every degree up to the actual population size. They
are the numerical comparison in reference V7, Lemma 9.17, and do not assume a
Poisson limit or discard degrees comparable to the population size.

`coefficientEnergy k` denotes the squared Hilbert norm of the homogeneous
coefficient tensor. The analytic Fock bound and the identification of these
coefficients with the physical histogram likelihood are separate obligations.
-/

namespace AFT
namespace HistogramTail

open scoped BigOperators









/-- Complete finite Fock energy, including the constant and highest terms. -/
noncomputable def fockEnergy (population : ℕ) (radius : ℝ)
    (coefficientEnergy : ℕ → ℝ) : ℝ :=
  ∑ degree ∈ Finset.range (population + 1),
    (degree.factorial : ℝ) * radius ^ (2 * degree) * coefficientEnergy degree /
      (population : ℝ) ^ degree







end HistogramTail
end AFT

end

section









/-! # Exact symmetric-tensor and Gaussian Fock norm normalization -/

namespace AFT
namespace TensorFock

open MeasureTheory
open scoped BigOperators Classical

variable {Slot Coordinate : Type*} [Fintype Slot] [Fintype Coordinate]

/-- Multiplicities of coordinate labels in an actual tensor basis word. -/
noncomputable def wordDegree (word : Slot → Coordinate) (coordinate : Coordinate) : ℕ :=
  Fintype.card {slot // word slot = coordinate}

/-- Evaluation of one tensor basis word on a complex vector. -/
noncomputable def wordMonomial (word : Slot → Coordinate) (value : Coordinate → ℂ) : ℂ :=
  ∏ slot, value (word slot)











/-- Actual polynomial evaluation of a finite tensor coordinate array. -/
noncomputable def tensorEvaluation (tensor : BlockFock.Tensor Slot Coordinate)
    (value : Coordinate → ℂ) : ℂ := ∑ word, (tensor word : ℂ) * wordMonomial word value











/-- An actual finite sum of homogeneous tensor evaluations. -/
noncomputable def seriesEvaluation (degrees : Finset ℕ)
    (tensor : (degree : ℕ) → BlockFock.Tensor (Fin degree) Coordinate) (value : Coordinate → ℂ) : ℂ :=
  ∑ degree ∈ degrees, tensorEvaluation (tensor degree) value



/-- Population and radius normalization of each concrete homogeneous tensor. -/
noncomputable def normalizedTensor (population : ℕ) (radius : ℝ)
    (tensor : (degree : ℕ) → BlockFock.Tensor (Fin degree) Coordinate)
    (degree : ℕ) : BlockFock.Tensor (Fin degree) Coordinate :=
  fun word => (radius / Real.sqrt population) ^ degree * tensor degree word















end TensorFock
end AFT

end

section







/-! # Concrete polynomial representation for nonlinear block estimates -/

namespace AFT
namespace NonlinearFock

open MeasureTheory TensorFock
open scoped BigOperators Classical

variable {Slot OtherSlot Coordinate Term : Type*}
variable [Fintype Slot] [Fintype OtherSlot] [Fintype Coordinate]











/-- A finite tensor-polynomial certificate, with all its symmetric coefficients
and exact evaluation identity retained. -/
def IsTensorPolynomial (function : (Coordinate → ℂ) → ℂ) : Prop :=
  ∃ (degrees : Finset ℕ) (tensor : (degree : ℕ) → BlockFock.Tensor (Fin degree) Coordinate),
    (∀ degree ∈ degrees, ∀ word (permutation : Equiv.Perm (Fin degree)),
      tensor degree (word ∘ permutation) = tensor degree word) ∧
    ∀ value, function value = seriesEvaluation degrees tensor value



/-- The coordinate array for the actual product of finitely many homogeneous
polynomials, with one disjoint slot family per factor. -/
noncomputable def familyTensor [Fintype Term] (Slots : Term → Type*)
    (tensor : (term : Term) → BlockFock.Tensor (Slots term) Coordinate) :
    BlockFock.Tensor (Sigma Slots) Coordinate :=
  fun word => ∏ term, tensor term (fun slot => word ⟨term, slot⟩)













omit [Fintype Slot] [Fintype OtherSlot] in
/-- The genuine Gaussian L2 norm of an evaluated polynomial. -/
noncomputable def gaussianNorm (function : (Coordinate → ℂ) → ℂ) : ℝ :=
  lpNorm function 2 FockGaussian.field













/-- A nonlinear choice leaves the linear factor in place, or selects its
quadratic or cubic tensor. -/
abbrev BlockChoice := Option Bool

def selectedSlots : BlockChoice → Type
  | none => Fin 0
  | some false => Fin 2
  | some true => Fin 3

instance selectedSlots_fintype (choice : BlockChoice) : Fintype (selectedSlots choice) := by
  cases choice with
  | none => exact inferInstanceAs (Fintype (Fin 0))
  | some choice =>
    cases choice
    · exact inferInstanceAs (Fintype (Fin 2))
    · exact inferInstanceAs (Fintype (Fin 3))

/-- The actual homogeneous tensor selected from one block. -/
noncomputable def selectedTensor (quadratic : BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : BlockFock.Tensor (Fin 3) Coordinate) :
    (choice : BlockChoice) → BlockFock.Tensor (selectedSlots choice) Coordinate
  | none => fun _ => 1
  | some false => quadratic
  | some true => cubic

/-- Linear coefficients remaining after one nonlinear selection pattern. -/
noncomputable def remainingLinear (coefficient : Term → Coordinate → ℝ)
    (choice : Term → BlockChoice) (term : Term) (coordinate : Coordinate) : ℝ :=
  if choice term = none then coefficient term coordinate else 0

/-- The actual normalized block product whose complete Fock energy is bounded. -/
noncomputable def cubicBlockProduct [Fintype Term] (coefficient : Term → Coordinate → ℝ)
    (quadratic : Term → BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : Term → BlockFock.Tensor (Fin 3) Coordinate) (value : Coordinate → ℂ) : ℂ :=
  ∏ term, ((1 + ∑ coordinate, (coefficient term coordinate : ℂ) * value coordinate) +
    tensorEvaluation (quadratic term) value + tensorEvaluation (cubic term) value)

/-- The coordinate tensor of all homogeneous nonlinear factors selected in a
pattern, on their actual disjoint slot families. -/
noncomputable def selectionTensor [Fintype Term]
    (quadratic : Term → BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : Term → BlockFock.Tensor (Fin 3) Coordinate) (choice : Term → BlockChoice) :
    BlockFock.Tensor (Sigma (fun term => selectedSlots (choice term))) Coordinate :=
  familyTensor (fun term => selectedSlots (choice term))
    (fun term => selectedTensor (quadratic term) (cubic term) (choice term))





/-- An explicit finite selection majorant, obtained from genuine tensor and
Gaussian norms, for the complete degree-three block product. -/
noncomputable def cubicSelectionMajorant [Fintype Term] (coefficient : Term → Coordinate → ℝ)
    (quadratic : Term → BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : Term → BlockFock.Tensor (Fin 3) Coordinate) : ℝ :=
  ∑ choice : Term → BlockChoice,
    Real.sqrt (((Fintype.card (Sigma (fun term => selectedSlots (choice term)))).factorial : ℝ) *
      2 ^ Fintype.card (Sigma (fun term => selectedSlots (choice term))) *
        BlockFock.tensorEnergy (selectionTensor quadratic cubic choice)) *
      (2 * Real.exp (2 * ∑ coordinate, (∑ term, remainingLinear coefficient choice term coordinate) ^ 2))











end NonlinearFock
end AFT

end

section







/-! # Scalar bounds for the complete nonlinear selection sum -/

set_option backward.isDefEq.respectTransparency false

namespace AFT
namespace SelectionBound

open MeasureTheory
open scoped BigOperators Classical







/-- Number of nonlinear blocks in a selection. -/
def choiceActive : NonlinearFock.BlockChoice → ℕ
  | none => 0
  | some _ => 1

noncomputable def choiceWeight (pair triple : ℝ) : NonlinearFock.BlockChoice → ℝ
  | none => 1
  | some false => pair
  | some true => triple

noncomputable def selectionCount {Index : Type*} [Fintype Index]
    (choice : Index → NonlinearFock.BlockChoice) : ℕ := ∑ index, choiceActive (choice index)

noncomputable def selectionWeight {Index : Type*} [Fintype Index]
    (pair triple : Index → ℝ) (choice : Index → NonlinearFock.BlockChoice) : ℝ :=
  ∏ index, choiceWeight (pair index) (triple index) (choice index)









noncomputable def pairSelections {Index : Type*} [Fintype Index]
    (choice : Index → NonlinearFock.BlockChoice) : ℕ :=
  ∑ index, if choice index = some false then 1 else 0

noncomputable def tripleSelections {Index : Type*} [Fintype Index]
    (choice : Index → NonlinearFock.BlockChoice) : ℕ :=
  ∑ index, if choice index = some true then 1 else 0













/-- The number of genuinely nonlinear blocks, detected by their actual local
Hilbert energies, rather than the size of the linear background. -/
noncomputable def nonlinearSupport {Index Coordinate : Type*} [Fintype Index] [Fintype Coordinate]
    (quadratic : Index → BlockFock.Tensor (Fin 2) Coordinate)
    (cubic : Index → BlockFock.Tensor (Fin 3) Coordinate) : Finset Index :=
  Finset.univ.filter (fun index => BlockFock.tensorEnergy (quadratic index) ≠ 0 ∨ BlockFock.tensorEnergy (cubic index) ≠ 0)



/-- Local Hilbert norms used by the original pair and triple activities. -/
noncomputable def localPairNorm {Index Coordinate : Type*} [Fintype Coordinate]
    (quadratic : Index → BlockFock.Tensor (Fin 2) Coordinate) (index : Index) : ℝ :=
  Real.sqrt (BlockFock.tensorEnergy (quadratic index))

noncomputable def localTripleNorm {Index Coordinate : Type*} [Fintype Coordinate]
    (cubic : Index → BlockFock.Tensor (Fin 3) Coordinate) (index : Index) : ℝ :=
  Real.sqrt (BlockFock.tensorEnergy (cubic index))











end SelectionBound
end AFT

end

section











/-! # Concrete endpoint and shared-source attachment L2 estimates -/

namespace AFT
namespace BlockDensity

open scoped BigOperators Classical

variable {First Second Body Source Coordinate Slot : Type*}
variable [Fintype First] [Fintype Second] [Fintype Body] [Fintype Source]

/-- A positive finite mass has L2 energy at most its actual maximum density
ratio times its total mass. -/
theorem profile_energy_le_ratio (reference mass : First → ℝ) (bound : ℝ)
    (href : ∀ point, 0 < reference point) (hmass : ∀ point, 0 ≤ mass point)
    (hratio : ∀ point, mass point ≤ bound * reference point) :
    profileSquareNorm reference mass ≤ bound * ∑ point, mass point := by
  unfold profileSquareNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro point _
  apply (div_le_iff₀ (href point)).mpr
  nlinarith [mul_le_mul_of_nonneg_left (hratio point) (hmass point)]

/-- Squared profile norm of an actual ordered endpoint pair. -/
noncomputable def pairEnergy (firstReference : First → ℝ) (secondReference : Second → ℝ)
    (mass : First → Second → ℝ) : ℝ :=
  ∑ first, ∑ second, mass first second ^ 2 / (firstReference first * secondReference second)

/-- A diffuse endpoint sublaw has its full finite joint norm controlled by
its point mass and the actual target reference lower bounds. -/
theorem diffuse_pair_energy_le (firstReference : First → ℝ) (secondReference : Second → ℝ)
    (mass : First → Second → ℝ) (firstLower secondLower upper : ℝ)
    (hfirst : 0 < firstLower) (hsecond : 0 < secondLower) (hu : 0 ≤ upper)
    (hrefFirst : ∀ first, firstLower ≤ firstReference first)
    (hrefSecond : ∀ second, secondLower ≤ secondReference second)
    (hmass : ∀ first second, 0 ≤ mass first second)
    (hupper : ∀ first second, mass first second ≤ upper)
    (htotal : (∑ first, ∑ second, mass first second) ≤ 1) :
    pairEnergy firstReference secondReference mass ≤ upper / (firstLower * secondLower) := by
  have hpoint (first : First) (second : Second) :
      mass first second ^ 2 / (firstReference first * secondReference second) ≤
        (upper / (firstLower * secondLower)) * mass first second := by
    have href : 0 < firstReference first * secondReference second :=
      mul_pos (hfirst.trans_le (hrefFirst first)) (hsecond.trans_le (hrefSecond second))
    have hden : firstLower * secondLower ≤ firstReference first * secondReference second :=
      mul_le_mul (hrefFirst first) (hrefSecond second) hsecond.le (hfirst.trans_le (hrefFirst first)).le
    calc
      _ ≤ mass first second ^ 2 / (firstLower * secondLower) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hfirst hsecond) hden
      _ ≤ _ := by
        apply (div_le_iff₀ (mul_pos hfirst hsecond)).mpr
        have h := mul_le_mul_of_nonneg_left (hupper first second) (hmass first second)
        field_simp
        nlinarith
  calc
    _ ≤ ∑ first, ∑ second, (upper / (firstLower * secondLower)) * mass first second :=
      Finset.sum_le_sum fun first _ => Finset.sum_le_sum fun second _ => hpoint first second
    _ = (upper / (firstLower * secondLower)) * ∑ first, ∑ second, mass first second := by
      simp only [← Finset.mul_sum]
    _ ≤ _ := by nlinarith [div_nonneg hu (mul_nonneg hfirst.le hsecond.le)]

/-- A conditional finite companion law has counting-square mass bounded by
its actual pointwise height. -/
theorem companion_square_le (companion : FiniteDist Second) (upper : ℝ)
    (hupper : ∀ second, companion.weight second ≤ upper) :
    (∑ second, companion.weight second ^ 2) ≤ upper := by
  calc
    _ ≤ ∑ second, upper * companion.weight second := by
      apply Finset.sum_le_sum
      intro second _
      nlinarith [mul_le_mul_of_nonneg_right (hupper second) (companion.nonneg second)]
    _ = _ := by rw [← Finset.mul_sum, companion.sum_one, mul_one]

/-- The marked endpoint pair is bounded using the actual primary/profile
square sum and conditional companion height. -/
theorem marked_pair_energy_le (firstReference : First → ℝ) (secondReference : Second → ℝ)
    (profile : First → ℝ) (companion : First → FiniteDist Second)
    (activation firstLower secondLower companionUpper : ℝ)
    (hfirst : 0 < firstLower) (hsecond : 0 < secondLower)
    (hrefFirst : ∀ first, firstLower ≤ firstReference first)
    (hrefSecond : ∀ second, secondLower ≤ secondReference second)
    (hcompanion : ∀ first second, (companion first).weight second ≤ companionUpper) :
    pairEnergy firstReference secondReference
      (fun first second => activation * profile first * (companion first).weight second) ≤
      (activation ^ 2 * companionUpper / (firstLower * secondLower)) * ∑ first, profile first ^ 2 := by
  have hden (first : First) (second : Second) : firstLower * secondLower ≤
      firstReference first * secondReference second :=
    mul_le_mul (hrefFirst first) (hrefSecond second) hsecond.le (hfirst.trans_le (hrefFirst first)).le
  calc
    _ ≤ ∑ first, ∑ second,
        (activation * profile first * (companion first).weight second) ^ 2 / (firstLower * secondLower) := by
      exact Finset.sum_le_sum fun first _ => Finset.sum_le_sum fun second _ =>
        div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hfirst hsecond) (hden first second)
    _ = ∑ first, activation ^ 2 * profile first ^ 2 / (firstLower * secondLower) *
        ∑ second, (companion first).weight second ^ 2 := by
      apply Finset.sum_congr rfl
      intro first _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro second _
      ring
    _ ≤ ∑ first, activation ^ 2 * profile first ^ 2 / (firstLower * secondLower) * companionUpper := by
      apply Finset.sum_le_sum
      intro first _
      exact mul_le_mul_of_nonneg_left (companion_square_le _ _ (hcompanion first)) (by positivity)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro first _
      ring





/-- Comparing an actual input profile's counting energy with its weighted
profile norm introduces only the true maximum primary probability. -/
theorem counting_profile_energy_le (primary profile : First → ℝ) (maximum : ℝ)
    (hprimary : ∀ first, 0 < primary first) (hmaximum : ∀ first, primary first ≤ maximum) :
    (∑ first, profile first ^ 2) ≤ maximum * profileSquareNorm primary profile := by
  unfold profileSquareNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro first _
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (hprimary first)).mpr
  nlinarith [mul_le_mul_of_nonneg_left (hmaximum first) (sq_nonneg (profile first))]

/-- The genuine marked endpoint response as a weighted L2 operator; this is
the term carrying the sharper maximum-primary factor in V7. -/
theorem marked_pair_operator_energy_le (firstReference : First → ℝ) (secondReference : Second → ℝ)
    (primary profile : First → ℝ) (companion : First → FiniteDist Second)
    (activation firstLower secondLower companionUpper primaryMaximum : ℝ)
    (hfirst : 0 < firstLower) (hsecond : 0 < secondLower) (hcompanion0 : 0 ≤ companionUpper)
    (hrefFirst : ∀ first, firstLower ≤ firstReference first)
    (hrefSecond : ∀ second, secondLower ≤ secondReference second)
    (hcompanion : ∀ first second, (companion first).weight second ≤ companionUpper)
    (hprimary : ∀ first, 0 < primary first) (hmaximum : ∀ first, primary first ≤ primaryMaximum) :
    pairEnergy firstReference secondReference
      (fun first second => activation * profile first * (companion first).weight second) ≤
      (activation ^ 2 * companionUpper * primaryMaximum / (firstLower * secondLower)) *
        profileSquareNorm primary profile := by
  apply (marked_pair_energy_le firstReference secondReference profile companion activation firstLower
    secondLower companionUpper hfirst hsecond hrefFirst hrefSecond hcompanion).trans
  have h := mul_le_mul_of_nonneg_left (counting_profile_energy_le primary profile primaryMaximum hprimary hmaximum)
    (show 0 ≤ activation ^ 2 * companionUpper / (firstLower * secondLower) by positivity)
  convert h using 1
  ring

/-- Actual endpoint/attachment mass, retaining the shared sample source. -/
noncomputable def attachedMass (source : FiniteDist Source)
    (pair : Source → FiniteDist (First × Second))
    (body : Source → First → Second → FiniteDist Body)
    (first : First) (second : Second) (attached : Body) : ℝ :=
  ∑ sample, source.weight sample * (pair sample).weight (first, second) * (body sample first second).weight attached

/-- Averaging endpoints does not duplicate or independently resample the source. -/
theorem attachedMass_marginal (source : FiniteDist Source)
    (pair : Source → FiniteDist (First × Second))
    (body : Source → First → Second → FiniteDist Body) (first : First) (second : Second) :
    (∑ attached, attachedMass source pair body first second attached) =
      (source.mix pair).weight (first, second) := by
  unfold attachedMass
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, FiniteDist.sum_one, mul_one, FiniteDist.mix_weight]

/-- The complete actual law for one endpoint pair and its fresh attached
body, retaining their common source in its probability mass. -/
noncomputable def attachedLaw (source : FiniteDist Source)
    (pair : Source → FiniteDist (First × Second))
    (body : Source → First → Second → FiniteDist Body) : FiniteDist ((First × Second) × Body) where
  weight point := attachedMass source pair body point.1.1 point.1.2 point.2
  nonneg point := Finset.sum_nonneg fun sample _ => mul_nonneg
    (mul_nonneg (source.nonneg _) ((pair sample).nonneg _))
      ((body sample point.1.1 point.1.2).nonneg _)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [attachedMass_marginal]
    exact (source.mix pair).sum_one

/-- The sampler's exact joint mass is the shared-source mass used in its
energy estimates. -/
theorem attachedLaw_weight (source : FiniteDist Source)
    (pair : Source → FiniteDist (First × Second))
    (body : Source → First → Second → FiniteDist Body) (first : First) (second : Second) (attached : Body) :
    (attachedLaw source pair body).weight ((first, second), attached) =
      attachedMass source pair body first second attached := rfl



/-- Full weighted square norm of an actual endpoint/attached-body triple. -/
noncomputable def tripleEnergy (firstReference : First → ℝ) (secondReference : Second → ℝ)
    (bodyReference : Body → ℝ) (mass : First → Second → Body → ℝ) : ℝ :=
  ∑ first, ∑ second, ∑ attached,
    mass first second attached ^ 2 / (firstReference first * secondReference second * bodyReference attached)







end BlockDensity
end AFT

end

section







/-! # Actual local density coefficients as finite Gaussian tensors -/

namespace AFT
namespace LocalTensors

open scoped BigOperators Classical

variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

/-- Whiten a genuine weighted density kernel into Euclidean tensor coordinates.
The ambient palette coordinates may be redundant; no basis choice is required. -/
noncomputable def whitenedTensor (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) : BlockFock.Tensor Slot Color :=
  fun word => (∏ slot, Real.sqrt ((reference slot).weight (word slot))) * kernel word



set_option backward.isDefEq.respectTransparency false in
/-- Restricting independent inputs to any specified set of slots preserves
the exact product law on those slots. -/
theorem independent_restriction_expectation (reference : Slot → FiniteDist Color)
    (selected : Finset Slot) (function : (selected → Color) → ℝ) :
    (FiniteDist.independent reference).expectation (fun word => function (fun slot => word slot)) =
      (FiniteDist.independent (fun slot : selected => reference slot)).expectation function := by
  let split := Equiv.piEquivPiSubtypeProd (fun slot => slot ∈ selected) (fun _ : Slot => Color)
  unfold FiniteDist.expectation FiniteDist.independent
  rw [← split.symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro chosen _
  have hweight (rest : {slot : Slot // slot ∉ selected} → Color) :
      (∏ slot, (reference slot).weight (split.symm (chosen, rest) slot)) =
        (∏ slot : selected, (reference slot).weight (chosen slot)) *
          ∏ slot : {slot : Slot // slot ∉ selected}, (reference slot).weight (rest slot) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun slot => slot ∈ selected)]
    apply congrArg₂ (· * ·)
    · apply Finset.prod_congr (by ext; simp)
      intro slot _
      change (reference slot).weight (if h : (slot : Slot) ∈ selected then chosen ⟨slot, h⟩ else rest ⟨slot, h⟩) = _
      simp only [dif_pos (show (slot : Slot) ∈ selected from slot.property)]
    · apply Finset.prod_congr (by ext; simp)
      intro slot _
      change (reference slot).weight (if h : (slot : Slot) ∈ selected then chosen ⟨slot, h⟩ else rest ⟨slot, h⟩) = _
      simp only [dif_neg (show (slot : Slot) ∉ selected from slot.property)]
  have hrestriction (rest : {slot : Slot // slot ∉ selected} → Color) :
      (fun slot : selected => split.symm (chosen, rest) slot) = chosen := by
    funext slot
    change (if h : (slot : Slot) ∈ selected then chosen ⟨slot, h⟩ else rest ⟨slot, h⟩) = _
    simp only [dif_pos (show (slot : Slot) ∈ selected from slot.property)]
  simp_rw [hweight, hrestriction]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hmass := (FiniteDist.independent
    (fun slot : {slot : Slot // slot ∉ selected} => reference slot)).sum_one
  change (∑ rest : {slot : Slot // slot ∉ selected} → Color,
    ∏ slot : {slot : Slot // slot ∉ selected}, (reference slot).weight (rest slot)) = 1 at hmass
  rw [hmass, mul_one]

/-- The genuine canonical component, with precisely its selected arguments. -/
noncomputable def restrictedComponent (reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) (word : selected → Color) : ℝ :=
  ∑ input, mass input * ∏ slot : selected,
    Hoeffding.centeredAtom (reference slot) (input slot) (word slot)



/-- A local coefficient's actual Gaussian tensor, before symmetrization. -/
noncomputable def localTensor (reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) : BlockFock.Tensor selected Color :=
  whitenedTensor (fun slot : selected => reference slot) (restrictedComponent reference mass selected)





/-- Actual centered one-color coefficient in the Gaussian coordinate space. -/
noncomputable def atomCoefficient (reference : FiniteDist Color) (input output : Color) : ℝ :=
  Real.sqrt (reference.weight output) * Hoeffding.centeredAtom reference input output

/-- The linear polynomial of one centered color outcome. -/
noncomputable def atomLinear (reference : FiniteDist Color) (input : Color)
    (value : Color → ℂ) : ℂ :=
  ∑ output, (atomCoefficient reference input output : ℂ) * value output

/-- The coefficient tensor is computed directly from the actual signed mass
and the actual one-color centered vectors. -/
theorem localTensor_formula (reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) (word : selected → Color) :
    localTensor reference mass selected word =
      ∑ input, mass input * ∏ slot : selected,
        atomCoefficient (reference slot) (input slot) (word slot) := by
  unfold localTensor whitenedTensor restrictedComponent atomCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro input _
  rw [Finset.prod_mul_distrib]
  ring



/-- The actual generating polynomial of a finite signed output law. -/
noncomputable def localGenerating (reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (value : Color → ℂ) : ℂ :=
  ∑ input, (mass input : ℂ) * ∏ slot, (1 + atomLinear (reference slot) (input slot) value)





/-- The actual selected coefficient reindexed onto its homogeneous degree. -/
noncomputable def degreePiece (reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (degree : ℕ) (selected : Finset Slot) :
    BlockFock.Tensor (Fin degree) Color :=
  if h : Fintype.card selected = degree then
    fun word => localTensor reference mass selected (word ∘ Fintype.equivFinOfCardEq h)
  else fun _ => 0

/-- The actual symmetric homogeneous tensor of a local signed law. -/
noncomputable def degreeTensor (reference : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (degree : ℕ) : BlockFock.Tensor (Fin degree) Color :=
  BlockFock.symmetrize (fun word => ∑ selected : Finset Slot, degreePiece reference mass degree selected word)

























end LocalTensors
end AFT

end

section







/-! # Actual shared-source output laws and all their local homogeneous energies -/

namespace AFT
namespace PhysicalBlockTensors

open scoped BigOperators Classical

variable {Color Source : Type*} [Fintype Color] [Fintype Source]
noncomputable section

local instance _root_.AFT.PhysicalBlockTensors.instDecidableEqFin_aFT (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

/-- Enumerate exactly the two endpoints and their attached body. -/
def tripleEquiv : (Fin 3 → Color) ≃ ((Color × Color) × Color) where
  toFun word := ((word 0, word 1), word 2)
  invFun point := ![point.1.1, point.1.2, point.2]
  left_inv word := by ext index; fin_cases index <;> rfl
  right_inv point := by rcases point with ⟨⟨first, second⟩, third⟩; rfl

/-- Actual joint mass, indexed by its three output positions. -/
noncomputable def tripleMass (mass : Color → Color → Color → ℝ) (word : Fin 3 → Color) : ℝ :=
  mass (word 0) (word 1) (word 2)

omit [Fintype Source] in
set_option backward.isDefEq.respectTransparency false in
/-- The full signed three-output density energy is exactly the concrete
endpoint/attachment weighted square sum. -/
theorem triple_density_energy (reference : FiniteDist Color) (mass : Color → Color → Color → ℝ) :
    (FiniteDist.independent (fun _ : Fin 3 => reference)).l2Sq
      (fun word => tripleMass mass word /
        (FiniteDist.independent (fun _ : Fin 3 => reference)).weight word) =
      BlockDensity.tripleEnergy reference.weight reference.weight reference.weight mass := by
  change densitySquareNorm (FiniteDist.independent (fun _ : Fin 3 => reference)).weight
    (fun word => tripleMass mass word /
      (FiniteDist.independent (fun _ : Fin 3 => reference)).weight word) = _
  rw [densityScore_square]
  unfold profileSquareNorm
  rw [← tripleEquiv.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  unfold BlockDensity.tripleEnergy
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  apply Finset.sum_congr rfl
  intro third _
  simp [FiniteDist.independent, tripleEquiv, tripleMass, Fin.prod_univ_succ]
  ring



/-- The genuine three-output sampler, with no duplicated source variables. -/
noncomputable def sharedSourceTriple (source : FiniteDist Source)
    (pair : Source → FiniteDist (Color × Color))
    (body : Source → Color → Color → FiniteDist Color) : FiniteDist (Fin 3 → Color) :=
  (BlockDensity.attachedLaw source pair body).map tripleEquiv.symm

/-- Exact mass of the concrete shared-source sampler. -/
theorem sharedSourceTriple_weight (source : FiniteDist Source)
    (pair : Source → FiniteDist (Color × Color))
    (body : Source → Color → Color → FiniteDist Color) (word : Fin 3 → Color) :
    (sharedSourceTriple source pair body).weight word =
      tripleMass (BlockDensity.attachedMass source pair body) word := by
  rw [sharedSourceTriple, FiniteDist.map_equiv_weight]
  exact BlockDensity.attachedLaw_weight source pair body (word 0) (word 1) (word 2)



/-- Enumerate the compensator together with the genuine attached triple. -/
def quadrupleEquiv : (Fin 4 → Color) ≃ (Color × ((Color × Color) × Color)) where
  toFun word := (word 0, ((word 1, word 2), word 3))
  invFun point := ![point.1, point.2.1.1, point.2.1.2, point.2.2]
  left_inv word := by ext index; fin_cases index <;> rfl
  right_inv point := by rcases point with ⟨compensator, ⟨⟨first, second⟩, third⟩⟩; rfl

/-- The actual signed four-output mass of a fresh compensator and one triple. -/
def compensatedTripleMass (compensator : Color → ℝ)
    (mass : Color → Color → Color → ℝ) (word : Fin 4 → Color) : ℝ :=
  compensator (word 0) * mass (word 1) (word 2) (word 3)

omit [Fintype Source] in
set_option backward.isDefEq.respectTransparency false in
/-- The full signed compensator-times-triple density energy factors exactly;
the attached triple itself retains its genuine shared source. -/
theorem compensated_triple_density_energy (reference : FiniteDist Color)
    (compensator : Color → ℝ) (mass : Color → Color → Color → ℝ) :
    (FiniteDist.independent (fun _ : Fin 4 => reference)).l2Sq
      (fun word => compensatedTripleMass compensator mass word /
        (FiniteDist.independent (fun _ : Fin 4 => reference)).weight word) =
      profileSquareNorm reference.weight compensator *
        BlockDensity.tripleEnergy reference.weight reference.weight reference.weight mass := by
  change densitySquareNorm (FiniteDist.independent (fun _ : Fin 4 => reference)).weight
    (fun word => compensatedTripleMass compensator mass word /
      (FiniteDist.independent (fun _ : Fin 4 => reference)).weight word) = _
  rw [densityScore_square]
  unfold profileSquareNorm
  rw [← quadrupleEquiv.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  unfold BlockDensity.tripleEnergy
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro color _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro first _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro second _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro attached _
  simp [FiniteDist.independent, quadrupleEquiv, compensatedTripleMass, Fin.prod_univ_succ]
  ring



end
end PhysicalBlockTensors
end AFT

end

section







/-! # Actual marked and unmarked source probabilities retain the same source -/

namespace AFT.BlockDensity

open scoped BigOperators Classical

noncomputable section

local instance _root_.AFT.BlockDensity.instDecidableEqFin_aFT (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

variable {Source Color : Type*} [Fintype Source] [Fintype Color]



















/-- Adding two actual endpoint masses retains their squared amplitudes. -/
theorem pairEnergy_add_le (reference : Color → ℝ) (href : ∀ color, 0 ≤ reference color)
    (first second : Color → Color → ℝ) :
    pairEnergy reference reference (fun a b => first a b + second a b) ≤
      2 * pairEnergy reference reference first + 2 * pairEnergy reference reference second := by
  unfold pairEnergy
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  have h : (first a b + second a b) ^ 2 ≤ 2 * first a b ^ 2 + 2 * second a b ^ 2 := by
    nlinarith [sq_nonneg (first a b - second a b)]
  convert div_le_div_of_nonneg_right h (mul_nonneg (href a) (href b)) using 1
  ring









end

end AFT.BlockDensity

end

section



/-!
# Explicit eventual meaning of negligible error

The security parameter is a natural number. Every inverse-polynomial order
has its own threshold; no claim is made about arbitrary accuracy at a fixed
parameter.
-/

namespace AFT

open Filter
open scoped Topology

/-- The usual eventual inverse-polynomial definition, including absolute
values so the definition also applies to signed error expressions. -/
def Negligible (error : ℕ → ℝ) : Prop :=
  ∀ order : ℕ, ∀ᶠ parameter : ℕ in atTop,
    |error parameter| ≤ 1 / (parameter : ℝ) ^ order















end AFT

end

section



namespace AFT
end AFT
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.minimumMass
end AFT.FiniteDist.minimumMass
namespace AFT.FiniteDist.permutationMixture
end AFT.FiniteDist.permutationMixture


/-!
# A genuine discrete Gaussian source and its full-support residue law

The one-dimensional Gaussian is normalized on the infinite integer lattice.
Its summability is proved by comparison with a geometric exponential series,
not assumed. Independent coordinate products give the source on `ℤ^d`.
Reduction modulo a positive modulus has full support, closing the analytic
source premise in the finite full-support obstruction.
-/

namespace AFT
namespace GaussianSource

open scoped BigOperators Classical ENNReal

/-- The Gaussian convention of the manuscript: `exp(-π z² / width²)`. -/
noncomputable def weight (width : ℝ) (z : ℤ) : ℝ :=
  Real.exp (-(Real.pi / width ^ 2) * (z : ℝ) ^ 2)

theorem weight_pos (width : ℝ) (z : ℤ) : 0 < weight width z :=
  Real.exp_pos _

/-- Polynomial Gaussian decay dominates a geometric exponential on ℕ. -/
theorem summable_weight (width : ℝ) (hwidth : 0 < width) :
    Summable (weight width) := by
  have hcoefficient : -(Real.pi / width ^ 2) < 0 :=
    neg_lt_zero.mpr (div_pos Real.pi_pos (sq_pos_of_pos hwidth))
  have hnat : Summable (fun n : ℕ => Real.exp (-(Real.pi / width ^ 2) * (n : ℝ) ^ 2)) := by
    apply Real.summable_exp_nat_mul_of_ge hcoefficient
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · have hone : (1 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · simpa only [weight, Int.cast_natCast] using hnat
  · simpa only [weight, Int.cast_neg, Int.cast_natCast, neg_sq] using hnat

/-- The unnormalized total Gaussian mass, before any modular reduction. -/
noncomputable def normalizer (width : ℝ) : ℝ≥0∞ :=
  ∑' z : ℤ, ENNReal.ofReal (weight width z)

theorem normalizer_ne_zero (width : ℝ) : normalizer width ≠ 0 := by
  intro hzero
  have h := (ENNReal.tsum_eq_zero.mp hzero) (0 : ℤ)
  simp [weight] at h



theorem normalizer_ne_top (width : ℝ) (hwidth : 0 < width) :
    normalizer width ≠ ∞ :=
  (summable_weight width hwidth).tsum_ofReal_ne_top

/-- The actual probability mass function on the infinite integer lattice. -/
noncomputable def integerGaussian (width : ℝ) (hwidth : 0 < width) : PMF ℤ :=
  PMF.normalize (fun z => ENNReal.ofReal (weight width z))
    (normalizer_ne_zero width) (normalizer_ne_top width hwidth)

































end GaussianSource
end AFT

end

section






/-!
# A quantitative clipping bound for the actual integer Gaussian

All masses are summed on the infinite integer lattice. Polynomial bounds on
the normalizer are proved by a geometric comparison; no Gaussian tail or
normalizing-constant estimate is assumed.
-/

namespace AFT.GaussianSource

open scoped BigOperators Classical

noncomputable def realNormalizer (width : ℝ) : ℝ := ∑' z : ℤ, weight width z

theorem realNormalizer_ge_one (width : ℝ) (hw : 0 < width) :
    1 ≤ realNormalizer width := by
  have h := (summable_weight width hw).le_tsum (0 : ℤ) (fun z _ => (weight_pos width z).le)
  simpa [weight, realNormalizer] using h





theorem weight_even (width : ℝ) : Function.Even (weight width) := by
  intro z
  simp [weight]

set_option backward.isDefEq.respectTransparency false in
/-- The nonzero lattice points are bounded by a genuine geometric series. -/
theorem realNormalizer_le_geometric (width : ℝ) (hw : 0 < width) :
    realNormalizer width ≤
      1 + 2 * (Real.exp (-(Real.pi / width ^ 2)) /
        (1 - Real.exp (-(Real.pi / width ^ 2)))) := by
  let coefficient := Real.pi / width ^ 2
  have hc : 0 < coefficient := div_pos Real.pi_pos (sq_pos_of_pos hw)
  have hr0 : 0 ≤ Real.exp (-coefficient) := (Real.exp_pos _).le
  have hr1 : Real.exp (-coefficient) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hc)
  have hgeom : Summable (fun n : ℕ => Real.exp (-coefficient) ^ n) :=
    summable_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hr0])
  have hgeom' : Summable (fun n : ℕ => Real.exp (-coefficient) ^ (n + 1)) := by
    simpa only [pow_succ] using hgeom.mul_right (Real.exp (-coefficient))
  have hnat : Summable (fun n : ℕ => weight width ((n + 1 : ℕ) : ℤ)) :=
    (summable_weight width hw).comp_injective
      (fun a b h => Nat.succ.inj (Int.ofNat_inj.mp h))
  have hpoint (n : ℕ) : weight width ((n + 1 : ℕ) : ℤ) ≤
      Real.exp (-coefficient) ^ (n + 1) := by
    rw [← Real.exp_nat_mul]
    unfold weight
    push_cast
    apply Real.exp_le_exp.mpr
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    change -coefficient * ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) * -coefficient
    nlinarith [mul_nonneg hc.le (mul_nonneg hn (by linarith : 0 ≤ (n : ℝ) + 1))]
  have hsum := hnat.tsum_le_tsum hpoint hgeom'
  have heq : (∑' n : ℕ, Real.exp (-coefficient) ^ (n + 1)) =
      Real.exp (-coefficient) / (1 - Real.exp (-coefficient)) := by
    simp_rw [pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hr0])]
    ring
  rw [heq] at hsum
  unfold realNormalizer
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat (weight_even width) (summable_weight width hw)]
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => weight width (n : ℤ))]
  simp only [weight, Int.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
    Real.exp_zero, nsmul_eq_mul]
  simpa only [weight, coefficient, Nat.cast_ofNat] using add_le_add (le_refl (1 : ℝ))
    (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2))

theorem exponential_geometric_le_inv (coefficient : ℝ) (hc : 0 < coefficient) :
    Real.exp (-coefficient) / (1 - Real.exp (-coefficient)) ≤ coefficient⁻¹ := by
  have he : 1 < Real.exp coefficient := Real.one_lt_exp_iff.mpr hc
  have he0 : Real.exp coefficient ≠ 0 := (Real.exp_pos _).ne'
  have hd : Real.exp coefficient - 1 ≠ 0 := (sub_pos.mpr he).ne'
  have hident : Real.exp (-coefficient) / (1 - Real.exp (-coefficient)) =
      (Real.exp coefficient - 1)⁻¹ := by
    rw [Real.exp_neg]
    field_simp
  rw [hident]
  exact inv_anti₀ hc (by linarith [Real.add_one_le_exp coefficient])

/-- A deliberately coarse polynomial bound is enough for clipping errors. -/
theorem realNormalizer_le_quadratic (width : ℝ) (hw : 0 < width) :
    realNormalizer width ≤ 1 + 2 * width ^ 2 / Real.pi := by
  have hc : 0 < Real.pi / width ^ 2 := div_pos Real.pi_pos (sq_pos_of_pos hw)
  calc
    _ ≤ 1 + 2 * (Real.exp (-(Real.pi / width ^ 2)) /
        (1 - Real.exp (-(Real.pi / width ^ 2)))) := realNormalizer_le_geometric width hw
    _ ≤ 1 + 2 * (Real.pi / width ^ 2)⁻¹ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (exponential_geometric_le_inv _ hc)
        (by norm_num : (0 : ℝ) ≤ 2))
    _ = _ := by rw [inv_div]; ring

/-- Exact Poisson duality of the lattice normalizing constant. -/
theorem realNormalizer_duality (width : ℝ) (hw : 0 < width) :
    realNormalizer width = width * realNormalizer (1 / width) := by
  have ht := Real.tsum_exp_neg_mul_int_sq (a := 1 / width ^ 2) (by positivity : 0 < 1 / width ^ 2)
  have hroot : (1 / width ^ 2) ^ (1 / 2 : ℝ) = 1 / width := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1),
      Real.sqrt_one, Real.sqrt_sq hw.le]
  rw [hroot, one_div_one_div] at ht
  convert ht using 1
  · unfold realNormalizer
    congr 1
    ext z
    unfold weight
    congr 1
    ring
  · congr 1
    unfold realNormalizer
    congr 1
    ext z
    unfold weight
    congr 1
    field_simp

/-- A linear normalizer bound follows from duality, without comparison to
an unproved Gaussian integral estimate. -/
theorem realNormalizer_le_linear (width : ℝ) (hw : 1 ≤ width) :
    realNormalizer width ≤ (1 + 2 / Real.pi) * width := by
  have hw0 : 0 < width := lt_of_lt_of_le zero_lt_one hw
  rw [realNormalizer_duality width hw0]
  have h := realNormalizer_le_quadratic (1 / width) (by positivity)
  have hi : 0 ≤ 1 / width := by positivity
  have hi1 : 1 / width ≤ 1 := (div_le_one hw0).mpr hw
  have hisq : (1 / width) ^ 2 ≤ 1 := by nlinarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsmall : 1 + 2 * (1 / width) ^ 2 / Real.pi ≤ 1 + 2 / Real.pi := by
    apply add_le_add le_rfl
    exact div_le_div_of_nonneg_right (by nlinarith) hpi.le
  calc
    _ ≤ width * (1 + 2 / Real.pi) := mul_le_mul_of_nonneg_left (h.trans hsmall) hw0.le
    _ = _ := mul_comm _ _

/-- Exact unnormalized mass removed by clipping at the stated absolute
cutoff. The event includes the boundary, as in the manuscript's strict
protected inequalities. -/
noncomputable def clippingMass (width cutoff : ℝ) : ℝ :=
  ∑' z : ℤ, if cutoff ≤ |(z : ℝ)| then weight width z else 0





/-- Actual normalized probability of violating the strict protected cutoff. -/
noncomputable def clippingProbability (width cutoff : ℝ) (hw : 0 < width) : ℝ :=
  ∑' z : ℤ, if cutoff ≤ |(z : ℝ)| then (integerGaussian width hw z).toReal else 0





end AFT.GaussianSource

end

section







/-!
# The actual finite root slice

Conditioning is performed on the integer sum, before taking any marginal.
The reference laws below are those marginals themselves. The first canonical
coefficient consequently vanishes exactly. This file does not assume an
asymptotic Gaussian approximation to the convolution masses.
-/

namespace AFT

open scoped BigOperators Classical

noncomputable section

namespace FiniteDist

variable {α : Type*} [Fintype α]

def eventMass (p : FiniteDist α) (event : α → Prop) : ℝ :=
  ∑ x, if event x then p.weight x else 0

theorem eventMass_nonneg (p : FiniteDist α) (event : α → Prop) : 0 ≤ p.eventMass event :=
  Finset.sum_nonneg fun x _ => by split_ifs; exact p.nonneg x; rfl

def condition (p : FiniteDist α) (event : α → Prop) (h : 0 < p.eventMass event) :
    FiniteDist α where
  weight x := (if event x then p.weight x else 0) / p.eventMass event
  nonneg x := div_nonneg (by split_ifs; exact p.nonneg x; rfl) h.le
  sum_one := by rw [← Finset.sum_div]; exact div_self h.ne'

theorem eventMass_positive_of_atom (p : FiniteDist α) (event : α → Prop)
    (x : α) (hx : event x) (hp : 0 < p.weight x) : 0 < p.eventMass event := by
  apply hp.trans_le
  calc
    p.weight x = (if event x then p.weight x else 0) := by rw [if_pos hx]
    _ ≤ ∑ y, if event y then p.weight y else 0 := Finset.single_le_sum (f := fun y => if event y then p.weight y else 0)
      (fun y _ => by split_ifs; exact p.nonneg y; rfl) (Finset.mem_univ x)

def normalize (weight : α → ℝ) (hweight : ∀ x, 0 ≤ weight x)
    (hmass : 0 < ∑ x, weight x) : FiniteDist α where
  weight x := weight x / ∑ y, weight y
  nonneg x := div_nonneg (hweight x) hmass.le
  sum_one := by rw [← Finset.sum_div]; exact div_self hmass.ne'

end FiniteDist

namespace RootSlice

variable {α ι : Type*} [Fintype α] [Fintype ι]

def integerSum (score : α → ℤ) (x : ι → α) : ℤ := ∑ i, score (x i)

def probability (source : ι → FiniteDist α) (score : α → ℤ) (target : ℤ) : ℝ :=
  (FiniteDist.independent source).eventMass (fun x => integerSum score x = target)

def law (source : ι → FiniteDist α) (score : α → ℤ) (target : ℤ)
    (h : 0 < probability source score target) : FiniteDist (ι → α) :=
  (FiniteDist.independent source).condition (fun x => integerSum score x = target) h



/-- The normalizing event really has positive probability: the all-zero
configuration belongs to it. No conditioning-on-null-event convention occurs. -/
theorem probability_positive (source : ι → FiniteDist α) (score : α → ℤ)
    (zero : α) (hzero : score zero = 0) (hp : ∀ i, 0 < (source i).weight zero) :
    0 < probability source score 0 := by
  apply FiniteDist.eventMass_positive_of_atom _ _ (fun _ => zero)
  · simp [integerSum, hzero]
  · exact Finset.prod_pos fun i _ => hp i













end RootSlice

end

end AFT

end

section







/-!
# The protected scalar sources and their zero atoms

The finite alphabet is an actual symmetric integer window. Its law is the
restriction and normalization of the same Gaussian weights as the infinite
source. In particular its zero atom is bounded using Poisson duality.
-/

namespace AFT.GaussianSource

open scoped BigOperators Classical

noncomputable section

abbrev Window (cutoff : ℕ) := ↥(Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ))

def windowZero (cutoff : ℕ) : Window cutoff :=
  ⟨0, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩

def windowNormalizer (width : ℝ) (cutoff : ℕ) : ℝ :=
  ∑ z : Window cutoff, weight width z

theorem windowNormalizer_ge_one (width : ℝ) (cutoff : ℕ) :
    1 ≤ windowNormalizer width cutoff := by
  have h := Finset.single_le_sum (f := fun z : Window cutoff => weight width z)
    (fun z _ => (weight_pos width z).le) (Finset.mem_univ (windowZero cutoff))
  simpa [windowZero, weight, windowNormalizer] using h

theorem windowNormalizer_le_real (width : ℝ) (cutoff : ℕ) (hw : 0 < width) :
    windowNormalizer width cutoff ≤ realNormalizer width := by
  unfold windowNormalizer realNormalizer
  rw [Finset.sum_coe_sort]
  exact (summable_weight width hw).sum_le_tsum _ (fun z _ => (weight_pos width z).le)

/-- Clipping at `|z| ≤ cutoff`; the manuscript's strict cutoff `B` is
obtained by taking `cutoff = B - 1`. -/
def windowGaussian (width : ℝ) (cutoff : ℕ) : FiniteDist (Window cutoff) :=
  FiniteDist.normalize (fun z => weight width z) (fun z => (weight_pos width z).le)
    (lt_of_lt_of_le zero_lt_one (windowNormalizer_ge_one width cutoff))

theorem windowGaussian_positive (width : ℝ) (cutoff : ℕ) (z : Window cutoff) :
    0 < (windowGaussian width cutoff).weight z :=
  div_pos (weight_pos width z)
    (lt_of_lt_of_le zero_lt_one (windowNormalizer_ge_one width cutoff))

theorem windowGaussian_zero (width : ℝ) (cutoff : ℕ) :
    (windowGaussian width cutoff).weight (windowZero cutoff) =
      1 / windowNormalizer width cutoff := by
  simp [windowGaussian, FiniteDist.normalize, windowZero, weight, windowNormalizer]

/-- The actual clipped zero atom has the required inverse-linear lower
bound, uniformly in the clipping window. -/
theorem windowGaussian_zero_lower (width : ℝ) (cutoff : ℕ) (hw : 1 ≤ width) :
    1 / ((1 + 2 / Real.pi) * width) ≤
      (windowGaussian width cutoff).weight (windowZero cutoff) := by
  rw [windowGaussian_zero]
  apply one_div_le_one_div_of_le
  · exact lt_of_lt_of_le zero_lt_one (windowNormalizer_ge_one width cutoff)
  · exact (windowNormalizer_le_real width cutoff (lt_of_lt_of_le zero_lt_one hw)).trans
      (realNormalizer_le_linear width hw)



/-- The exact activation probability with `100 * featureCount` as the
reciprocal mark weight, including the two actual independent source atoms. -/
def activation (firstWidth secondWidth : ℝ) (cutoff featureCount : ℕ) : ℝ :=
  1 / (100 * (featureCount : ℝ)) *
    ((windowGaussian firstWidth cutoff).prod (windowGaussian secondWidth cutoff)).weight
      (windowZero cutoff, windowZero cutoff)





/-- The protected root event is nonnull for every population, with the
correct integer zero-sum condition. -/
theorem window_root_probability_positive (width : ℝ) (cutoff population : ℕ) :
    0 < RootSlice.probability (fun _ : Fin population => windowGaussian width cutoff)
      (fun z => (z : ℤ)) 0 :=
  RootSlice.probability_positive _ _ (windowZero cutoff) rfl
    (fun _ => windowGaussian_positive width cutoff (windowZero cutoff))

end

end AFT.GaussianSource

end

section





/-!
# The actual activation at the reference V7 cutoff

The mark probability and both clipped Gaussian zero atoms are included in
the definition. The eventual inverse-fifth-power lower bound is proved,
rather than supplied as a parameter hypothesis to the primary inverse.
-/

namespace AFT.GaussianSource

open Filter
open scoped Topology

noncomputable section

def legCutoff (cutoffScale : ℝ) (parameter : ℕ) : ℕ :=
  ⌈cutoffScale * (parameter : ℝ) ^ (9 / 8 : ℝ)⌉₊

def legFeatureCount (cutoffScale : ℝ) (parameter : ℕ) : ℕ :=
  (2 * legCutoff cutoffScale parameter - 1) ^ 2

def v7Activation (cutoffScale : ℝ) (parameter : ℕ) : ℝ :=
  activation (parameter : ℝ) (10 * parameter)
    (legCutoff cutoffScale parameter - 1) (legFeatureCount cutoffScale parameter)









end

end AFT.GaussianSource

end

section





/-! # The actual leg cutoff is computable by finite integer comparisons

For every natural cutoff constant, the program computes exactly the real
ceiling in the V7 source definition. No real-floor or real-power oracle is
used by the executable definition.
-/
namespace AFT.V7Calibration
open GaussianSource

/-- Count the natural numbers strictly below the positive eighth root of
`constant^8 * n^9`, within a proved quadratic search range. -/
def actualLegCutoffProgram (constant n : ℕ) : ℕ :=
  ((Finset.range (constant*n^2+1)).filter (fun index => index^8<constant^8*n^9)).card

noncomputable section









end
end AFT.V7Calibration

end

section




/-!
# Finite mixed-fiber cost of a partial matrix operator

An arbitrary finite alphabet `κ` packages the other integrated coordinates;
its weight may be any nonnegative product weight. Thus the estimates apply
to every mixed fiber after any chosen set of the other coordinates is fixed.
The additional penalty for fixing this output coordinate is derived below.
-/

namespace AFT

open scoped BigOperators

section PartialMatrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]





/-- Integrated norm of the coordinate and any remaining coordinates. -/
noncomputable def integratedFiberNorm (primary : ι → ℝ) (remaining : κ → ℝ)
    (kernel : ι → κ → ℝ) : ℝ :=
  Real.sqrt (∑ rest, remaining rest * ∑ color, primary color * kernel color rest ^ 2)

/-- Largest remaining-coordinate L2 fiber after fixing the distinguished
coordinate. This uses the ordinary finite-function supremum norm. -/
noncomputable def fixedFiberNorm (remaining : κ → ℝ) (kernel : ι → κ → ℝ) : ℝ :=
  ‖fun color => Real.sqrt (∑ rest, remaining rest * kernel color rest ^ 2)‖

/-- The two terms in mixed activity that differ only by fixing this
coordinate. `rate = 1 / sqrt(pool)` is the normalization for this pool. -/
noncomputable def coordinateActivity (rate : ℝ) (primary : ι → ℝ) (remaining : κ → ℝ)
    (kernel : ι → κ → ℝ) : ℝ :=
  rate * integratedFiberNorm primary remaining kernel + rate ^ 2 * fixedFiberNorm remaining kernel











end PartialMatrix

end AFT

end

section




/-!
# Exact translation bounds for the public uniform interval anchors

The anchors are kept on the integer line. Their laws and the full finite
support of their translated difference are explicit; no cyclic-window
replacement or postulated matrix norm is used.
-/

namespace AFT

open scoped BigOperators symmDiff

/-- An integer interval of exactly `width` consecutive possible anchors. -/
noncomputable def anchorInterval (start : ℤ) (width : ℕ) : Finset ℤ :=
  Finset.Ico start (start + width)

@[simp] theorem anchorInterval_card (start : ℤ) (width : ℕ) :
    (anchorInterval start width).card = width := by
  simp [anchorInterval, Int.card_Ico]

/-- The actual counting density of a uniform integer anchor interval. -/
noncomputable def intervalAnchorLaw (start : ℤ) (width : ℕ) (color : ℤ) : ℝ :=
  if color ∈ anchorInterval start width then (width : ℝ)⁻¹ else 0

theorem intervalAnchorLaw_nonneg (start color : ℤ) (width : ℕ) :
    0 ≤ intervalAnchorLaw start width color := by
  unfold intervalAnchorLaw
  split_ifs <;> positivity

theorem intervalAnchorLaw_mass (start : ℤ) (width : ℕ) (hwidth : width ≠ 0) :
    (∑ color ∈ anchorInterval start width, intervalAnchorLaw start width color) = 1 := by
  have hne : (width : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hwidth
  simp [intervalAnchorLaw, hne]

theorem intervalAnchorLaw_bound (start color : ℤ) (width : ℕ) :
    intervalAnchorLaw start width color ≤ (width : ℝ)⁻¹ := by
  unfold intervalAnchorLaw
  split_ifs <;> simp

/-- Translating a whole interval translates its law exactly. -/
theorem intervalAnchorLaw_translate (start shift color : ℤ) (width : ℕ) :
    intervalAnchorLaw (start + shift) width color =
      intervalAnchorLaw start width (color - shift) := by
  unfold intervalAnchorLaw anchorInterval
  have hmem : color ∈ Finset.Ico (start + shift) (start + shift + width) ↔
      color - shift ∈ Finset.Ico start (start + width) := by
    simp only [Finset.mem_Ico]
    omega
  simp only [hmem]

/-- Exact size of the overlap, including shifts longer than the interval. -/
theorem anchorInterval_inter_card (start shift : ℤ) (width : ℕ) :
    (anchorInterval start width ∩ anchorInterval (start + shift) width).card =
      width - min width shift.natAbs := by
  rw [anchorInterval, anchorInterval, Finset.Ico_inter_Ico, Int.card_Ico]
  have habs := Int.natCast_natAbs shift
  by_cases hs : 0 ≤ shift
  · rw [abs_of_nonneg hs] at habs
    omega
  · rw [abs_of_neg (lt_of_not_ge hs)] at habs
    omega

/-- Exactly two edge strips are changed by a translation. -/
theorem anchorInterval_symmDiff_card (start shift : ℤ) (width : ℕ) :
    (anchorInterval start width ∆ anchorInterval (start + shift) width).card =
      2 * min width shift.natAbs := by
  let first := anchorInterval start width
  let second := anchorInterval (start + shift) width
  have hd : Disjoint (first \ second) (second \ first) := by
    apply Finset.disjoint_left.mpr
    intro color hc hd
    exact (Finset.mem_sdiff.mp hc).2 (Finset.mem_sdiff.mp hd).1
  change ((first \ second) ∪ (second \ first)).card = _
  rw [Finset.card_union_of_disjoint hd, Finset.card_sdiff, Finset.card_sdiff,
    Finset.inter_comm second first]
  simp only [first, second, anchorInterval_card, anchorInterval_inter_card]
  omega

/-- Full squared counting norm of the translated anchor difference. Every
nonzero coordinate is included in the displayed finite union. -/
noncomputable def anchorTranslationSquare (start shift : ℤ) (width : ℕ) : ℝ :=
  ∑ color ∈ anchorInterval start width ∪ anchorInterval (start + shift) width,
    (intervalAnchorLaw (start + shift) width color - intervalAnchorLaw start width color) ^ 2

/-- Outside this union the translated difference is exactly zero. -/
theorem anchorTranslation_zero_outside (start shift color : ℤ) (width : ℕ)
    (houtside : color ∉ anchorInterval start width ∪ anchorInterval (start + shift) width) :
    intervalAnchorLaw (start + shift) width color - intervalAnchorLaw start width color = 0 := by
  simp only [Finset.mem_union, not_or] at houtside
  simp [intervalAnchorLaw, houtside.1, houtside.2]

/-- The squared counting norm is exactly `2 min(|shift|,width) / width²`. -/
theorem anchorTranslationSquare_eq (start shift : ℤ) (width : ℕ) :
    anchorTranslationSquare start shift width =
      2 * (min width shift.natAbs : ℝ) / (width : ℝ) ^ 2 := by
  have hrestrict : anchorTranslationSquare start shift width =
      ∑ color ∈ anchorInterval start width ∆ anchorInterval (start + shift) width,
        (intervalAnchorLaw (start + shift) width color - intervalAnchorLaw start width color) ^ 2 := by
    symm
    apply Finset.sum_subset Finset.symmDiff_subset_union
    intro color _ hnot
    simp only [Finset.mem_symmDiff, not_or, not_and] at hnot
    unfold intervalAnchorLaw
    split_ifs <;> simp_all
  rw [hrestrict]
  have hrow (color : ℤ)
      (hc : color ∈ anchorInterval start width ∆ anchorInterval (start + shift) width) :
      (intervalAnchorLaw (start + shift) width color - intervalAnchorLaw start width color) ^ 2 =
        ((width : ℝ)⁻¹) ^ 2 := by
    rcases Finset.mem_symmDiff.mp hc with ⟨hfirst, hsecond⟩ | ⟨hsecond, hfirst⟩ <;>
      simp [intervalAnchorLaw, hfirst, hsecond]
  calc
    _ = ∑ _color ∈ anchorInterval start width ∆ anchorInterval (start + shift) width,
        ((width : ℝ)⁻¹) ^ 2 := Finset.sum_congr rfl hrow
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, anchorInterval_symmDiff_card,
        Nat.cast_mul, Nat.cast_ofNat, Nat.cast_min]
      ring

/-- The Hilbert estimate used in the local primary inverse. -/
theorem anchorTranslationSquare_le (start shift : ℤ) (width : ℕ) :
    anchorTranslationSquare start shift width ≤ 2 * (shift.natAbs : ℝ) / (width : ℝ) ^ 2 := by
  rw [anchorTranslationSquare_eq]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have hm : (min width shift.natAbs : ℝ) ≤ shift.natAbs := by
    exact_mod_cast min_le_right width shift.natAbs
  linarith



/-- The left anchor used below the palette midpoint stays in the safe
integer interval after every allowed source displacement. -/
theorem publicAnchor_left_safe (modulus width color offset shift safeMargin maxShift : ℤ)
    (hmodulus : 6 * width + 1 ≤ modulus) (hcolor : 0 ≤ color)
    (hhalf : 2 * color ≤ modulus - 1) (hoffsetLower : width ≤ offset)
    (hoffsetUpper : offset < 2 * width) (hshift : |shift| ≤ maxShift)
    (hmargin : safeMargin + maxShift ≤ width) :
    safeMargin ≤ modulus - 1 - color - offset + shift ∧
      modulus - 1 - color - offset + shift < modulus - safeMargin := by
  have hs := abs_le.mp hshift
  omega

/-- The right anchor used above the midpoint obeys the same safe bounds. -/
theorem publicAnchor_right_safe (modulus width color offset shift safeMargin maxShift : ℤ)
    (hmodulus : 6 * width + 1 ≤ modulus) (hcolor : color < modulus)
    (hhalf : modulus - 1 ≤ 2 * color) (hoffsetLower : width ≤ offset)
    (hoffsetUpper : offset < 2 * width) (hshift : |shift| ≤ maxShift)
    (hmargin : safeMargin + maxShift ≤ width) :
    safeMargin ≤ modulus - 1 - color + offset + shift ∧
      modulus - 1 - color + offset + shift < modulus - safeMargin := by
  have hs := abs_le.mp hshift
  omega

section ActualAnchorMatrix

variable {ι : Type*} [Fintype ι]

















/-- A finite palette embedded into the integer line cannot increase a
nonnegative finite-support counting sum. -/
theorem finitePalette_sum_le_support (colors : ι → ℤ) (hinj : Function.Injective colors)
    (support : Finset ℤ) (value : ℤ → ℝ) (hn : ∀ output, 0 ≤ value output)
    (hz : ∀ output ∉ support, value output = 0) :
    (∑ color, value (colors color)) ≤ ∑ output ∈ support, value output := by
  classical
  have hsum : (∑ output ∈ support, value output) =
      ∑ output ∈ Finset.univ.image colors ∪ support, value output := by
    exact Finset.sum_subset Finset.subset_union_right (fun output _ hout => hz output hout)
  calc
    _ = ∑ output ∈ Finset.univ.image colors, value output := by
      rw [Finset.sum_image]
      intro first _ second _ heq
      exact hinj heq
    _ ≤ ∑ output ∈ Finset.univ.image colors ∪ support, value output := by
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun output _ _ => hn output)
    _ = _ := hsum.symm









end ActualAnchorMatrix

end AFT

end

section




/-!
# A finite primary inverse in the actual profile activity

The activity below is the one-coordinate mixed activity of signed primary
profiles. A strict contraction gives an inverse by finite-dimensional
injectivity, so no unproved completeness or norm-equivalence assertion is
needed. The eventual concrete operator is obtained from the displayed
rank-one inverse and interval-anchor translation estimates.
-/

namespace AFT

open scoped BigOperators

section ProfileActivity

variable {ι : Type*} [Fintype ι]

/-- The one-primary-coordinate activity, with `rate = 1 / sqrt(pool)`. -/
noncomputable def primaryActivity (rate : ℝ) (primary profile : ι → ℝ) : ℝ :=
  rate * Real.sqrt (profileSquareNorm primary profile) +
    rate ^ 2 * ‖fun color => profile color / primary color‖



@[simp] theorem primaryActivity_neg (rate : ℝ) (primary profile : ι → ℝ) :
    primaryActivity rate primary (-profile) = primaryActivity rate primary profile := by
  have hs : profileSquareNorm primary (-profile) = profileSquareNorm primary profile := by
    simp [profileSquareNorm]
  have hd : (fun color => (-profile) color / primary color) =
      -(fun color => profile color / primary color) := by
    funext color
    simp only [Pi.neg_apply, neg_div]
  simp only [primaryActivity, hs, hd, norm_neg]

/-- Weighted finite Minkowski, with the cross term checked by finite
Cauchy--Schwarz. -/
theorem profileSquareNorm_sqrt_add_le (primary first second : ι → ℝ)
    (hp : ∀ color, 0 < primary color) :
    Real.sqrt (profileSquareNorm primary (first + second)) ≤
      Real.sqrt (profileSquareNorm primary first) + Real.sqrt (profileSquareNorm primary second) := by
  have hnfirst := profileSquareNorm_nonneg primary first (fun color => le_of_lt (hp color))
  have hnsecond := profileSquareNorm_nonneg primary second (fun color => le_of_lt (hp color))
  have hc : (∑ color, first color * second color / primary color) ^ 2 ≤
      profileSquareNorm primary first * profileSquareNorm primary second := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro color _
      exact div_nonneg (sq_nonneg _) (le_of_lt (hp color))
    · intro color _
      exact div_nonneg (sq_nonneg _) (le_of_lt (hp color))
    · intro color _
      ring
  have hcross : (∑ color, first color * second color / primary color) ≤
      Real.sqrt (profileSquareNorm primary first) * Real.sqrt (profileSquareNorm primary second) := by
    simpa only [Real.sqrt_mul hnfirst] using Real.le_sqrt_of_sq_le hc
  have hexpand : profileSquareNorm primary (first + second) =
      profileSquareNorm primary first + profileSquareNorm primary second +
        2 * ∑ color, first color * second color / primary color := by
    simp only [profileSquareNorm, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro color _
    ring
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · rw [hexpand]
    nlinarith [Real.sq_sqrt hnfirst, Real.sq_sqrt hnsecond]





@[simp] theorem primaryActivity_zero (rate : ℝ) (primary : ι → ℝ) :
    primaryActivity rate primary 0 = 0 := by
  simp [primaryActivity, profileSquareNorm]
  exact Or.inr rfl















































end ProfileActivity

end AFT

end

section



/-!
# The fixed parameter powers of reference V7

The modulus is an actual prime selected using Bertrand's theorem. No prime
existence premise is attached to the subsequent population inequalities.
Small security parameters use `max 2 parameter`; this agrees with every
eventual statement of Section 9.
-/

namespace AFT.Parameters

noncomputable section

def security (parameter : ℕ) : ℕ := max 2 parameter

theorem security_ge_two (parameter : ℕ) : 2 ≤ security parameter := le_max_left _ _



 theorem prime_exists (parameter : ℕ) :
    ∃ modulus : ℕ, modulus.Prime ∧ security parameter ^ 40 < modulus ∧
      modulus ≤ 2 * security parameter ^ 40 :=
  Nat.exists_prime_lt_and_le_two_mul _
    (pow_ne_zero _ (show security parameter ≠ 0 by have := security_ge_two parameter; omega))

/-- A prime in the exact power interval specified in Section 9. -/
noncomputable def modulus (parameter : ℕ) : ℕ := Nat.find (prime_exists parameter)

theorem modulus_spec (parameter : ℕ) : (modulus parameter).Prime ∧
    security parameter ^ 40 < modulus parameter ∧
      modulus parameter ≤ 2 * security parameter ^ 40 := Nat.find_spec (prime_exists parameter)

theorem modulus_prime (parameter : ℕ) : (modulus parameter).Prime := (modulus_spec parameter).1

theorem modulus_bounds (parameter : ℕ) :
    security parameter ^ 40 ≤ modulus parameter ∧
      modulus parameter ≤ 2 * security parameter ^ 40 :=
  ⟨(modulus_spec parameter).2.1.le, (modulus_spec parameter).2.2⟩

def meanDensity (parameter : ℕ) : ℕ := security parameter ^ 20
def dimension (parameter : ℕ) : ℕ := modulus parameter * meanDensity parameter
def legs (parameter : ℕ) : ℕ := security parameter ^ 30
def bodies (parameter : ℕ) : ℕ := dimension parameter - 2 * legs parameter
def anchorWidth (parameter : ℕ) : ℕ := security parameter ^ 32
def safeMargin (parameter : ℕ) : ℕ := 20 * security parameter ^ 2
def safeSize (parameter : ℕ) : ℕ := modulus parameter - 2 * safeMargin parameter

theorem dimension_bounds (parameter : ℕ) :
    security parameter ^ 60 ≤ dimension parameter ∧
      dimension parameter ≤ 2 * security parameter ^ 60 := by
  have h := modulus_bounds parameter
  have heq : security parameter ^ 40 * security parameter ^ 20 =
      security parameter ^ 60 := by rw [← pow_add]
  constructor
  · exact heq ▸ Nat.mul_le_mul_right (security parameter ^ 20) h.1
  · have hh := Nat.mul_le_mul_right (security parameter ^ 20) h.2
    simpa only [Nat.mul_assoc, heq, dimension, meanDensity] using hh

theorem four_legs_le_dimension (parameter : ℕ) : 4 * legs parameter ≤ dimension parameter := by
  have hm : 4 ≤ security parameter ^ 30 := by
    have hh := Nat.pow_le_pow_left (security_ge_two parameter) 30
    omega
  have heq : security parameter ^ 60 = legs parameter * legs parameter := by
    unfold legs
    rw [← pow_add]
  have hd := (dimension_bounds parameter).1
  rw [heq] at hd
  exact (Nat.mul_le_mul_right (legs parameter) hm).trans hd

theorem bodies_positive (parameter : ℕ) : 0 < bodies parameter := by
  have hm : 0 < legs parameter := pow_pos (lt_of_lt_of_le (by decide : 0 < 2)
    (security_ge_two parameter)) _
  have hd := four_legs_le_dimension parameter
  unfold bodies
  omega

theorem population_identity (parameter : ℕ) :
    bodies parameter + 2 * legs parameter = dimension parameter := by
  have h := four_legs_le_dimension parameter
  exact Nat.sub_add_cancel (by omega)

theorem legs_le_half_bodies (parameter : ℕ) : 2 * legs parameter ≤ bodies parameter := by
  have h := four_legs_le_dimension parameter
  unfold bodies
  omega

/-- The public anchor intervals fit with the exact six-width clearance. -/
theorem anchor_clearance (parameter : ℕ) : 6 * anchorWidth parameter + 1 ≤ modulus parameter := by
  have hp : 6 ≤ security parameter ^ 8 := by
    have h := Nat.pow_le_pow_left (security_ge_two parameter) 8
    omega
  have hq := (modulus_spec parameter).2.1
  have heq : security parameter ^ 40 = security parameter ^ 8 * anchorWidth parameter := by
    unfold anchorWidth
    rw [← pow_add]
  rw [heq] at hq
  have h := Nat.mul_le_mul_right (anchorWidth parameter) hp
  omega

/-- The actual safe-center palette is nonempty, even at the global fallback
parameter; this uses the specified modulus power rather than an assumption. -/
theorem safeSize_positive (parameter : ℕ) : 0 < safeSize parameter := by
  have hp : 40 ≤ security parameter ^ 38 := by
    have h := Nat.pow_le_pow_left (security_ge_two parameter) 38
    omega
  have hq := (modulus_spec parameter).2.1
  have heq : security parameter ^ 40 = security parameter ^ 38 * security parameter ^ 2 := by
    rw [← pow_add]
  rw [heq] at hq
  have h := Nat.mul_le_mul_right (security parameter ^ 2) hp
  unfold safeSize safeMargin
  omega

end

end AFT.Parameters

end

section




/-!
# Actual trimmed pair slices and averaging over the public interval

The slice is the intersection of the two endpoint safety inequalities.
Its cardinality and its counting probability law are computed exactly.
-/

namespace AFT.TrimmedSlice

open scoped BigOperators symmDiff

/-- Both endpoint colors must avoid the boundary strip. -/
noncomputable def slice (modulus boundary shift : ℤ) : Finset ℤ :=
  Finset.Ico (boundary + max shift 0) (modulus - boundary + min shift 0)

theorem mem_slice (modulus boundary shift color : ℤ) :
    color ∈ slice modulus boundary shift ↔
      boundary ≤ color ∧ color ≤ modulus - 1 - boundary ∧
      boundary ≤ modulus - 1 + shift - color ∧
      modulus - 1 + shift - color ≤ modulus - 1 - boundary := by
  simp only [slice, Finset.mem_Ico]
  omega

/-- The exact cardinality printed in the chart construction. -/
theorem slice_card (modulus boundary shift : ℤ) :
    (slice modulus boundary shift).card = (modulus - 2 * boundary - |shift|).toNat := by
  rw [slice, Int.card_Ico]
  congr 1
  by_cases hs : 0 ≤ shift
  · rw [abs_of_nonneg hs]
    omega
  · rw [abs_of_neg (lt_of_not_ge hs)]
    omega

noncomputable def law (modulus boundary shift color : ℤ) : ℝ :=
  if color ∈ slice modulus boundary shift then ((slice modulus boundary shift).card : ℝ)⁻¹ else 0

theorem law_nonneg (modulus boundary shift color : ℤ) : 0 ≤ law modulus boundary shift color := by
  unfold law
  split_ifs <;> positivity





/-- Every actual trimmed law has the advertised supremum bound. -/
theorem law_le_of_shift_bound (modulus boundary shift shiftBound color : ℤ)
    (hshift : |shift| ≤ shiftBound) (hwidth : 2 * boundary + shiftBound < modulus) :
    law modulus boundary shift color ≤
      1 / ((modulus : ℝ) - 2 * boundary - shiftBound) := by
  have hcard : ((slice modulus boundary shift).card : ℤ) = modulus - 2 * boundary - |shift| := by
    rw [slice_card, Int.toNat_of_nonneg (by omega)]
  have hcardReal : ((slice modulus boundary shift).card : ℝ) =
      (modulus : ℝ) - 2 * boundary - |(shift : ℝ)| := by exact_mod_cast hcard
  have hshiftReal : |(shift : ℝ)| ≤ shiftBound := by exact_mod_cast hshift
  have hwidthReal : 0 < (modulus : ℝ) - 2 * boundary - shiftBound := by exact_mod_cast (show 0 < modulus - 2 * boundary - shiftBound by omega)
  unfold law
  split_ifs
  · rw [hcardReal, ← one_div]
    exact one_div_le_one_div_of_le hwidthReal (by linarith)
  · positivity

/-- Average the slice over the actual finite public uniform offset interval. -/
noncomputable def intervalMixture (start : ℤ) (width : ℕ) (kernel : ℤ → ℝ) : ℝ :=
  ∑ shift ∈ anchorInterval start width, intervalAnchorLaw start width shift * kernel shift









noncomputable def averagedLaw (modulus boundary start source : ℤ) (width : ℕ) (color : ℤ) : ℝ :=
  intervalMixture start width (fun shift => law modulus boundary (shift - source) color)

theorem averagedLaw_nonneg (modulus boundary start source : ℤ) (width : ℕ) (color : ℤ) :
    0 ≤ averagedLaw modulus boundary start source width color := by
  unfold averagedLaw intervalMixture
  exact Finset.sum_nonneg fun shift _ => mul_nonneg (intervalAnchorLaw_nonneg _ _ _) (law_nonneg _ _ _ _)





/-- A finite source and public-blur mixture. A product index includes the
original source and independent public blur without altering either law. -/
noncomputable def mixedLaw {τ : Type*} [Fintype τ] (modulus boundary : ℤ)
    (starts sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ) (color : ℤ) : ℝ :=
  ∑ index, weights index * averagedLaw modulus boundary (starts index) (sources index) width color

theorem mixedLaw_nonneg {τ : Type*} [Fintype τ] (modulus boundary : ℤ)
    (starts sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ) (color : ℤ)
    (hweights : ∀ index, 0 ≤ weights index) :
    0 ≤ mixedLaw modulus boundary starts sources weights width color := by
  exact Finset.sum_nonneg fun index _ => mul_nonneg (hweights index) (averagedLaw_nonneg _ _ _ _ _ _)





end AFT.TrimmedSlice

end

section






/-!
# Pointwise positivity of the mean-calibrated primary law

The estimates retain the actual mean-calibration formula. The first result
isolates its deterministic arithmetic, including the nonnegative body
mean deficit; concrete averaged trimmed slices supply its hypotheses.
-/

namespace AFT

open scoped BigOperators







namespace TrimmedSlice

/-- The actual mean of a safe uniform center after a finite public body blur. -/
noncomputable def blurredSafeLaw {σ : Type*} [Fintype σ]
    (modulus margin : ℤ) (shifts : σ → ℤ) (weights : σ → ℝ) (color : ℤ) : ℝ :=
  ∑ index, weights index * intervalAnchorLaw margin (modulus - 2 * margin).toNat (color - shifts index)







end TrimmedSlice

end AFT

end

section



namespace AFT
end AFT
namespace AFT.finiteCorrection
end AFT.finiteCorrection



/-!
# Exact finite-group charge mixing

This proves a charge estimate directly by convolution of the signed difference
from uniform. It uses the actual `L¹` distance of the center law, rather than
postulating a Fourier mixing estimate. The bound has `q` instead of `q - 1`,
which suffices for the same eventual parameter regime once the concrete
center law's `L¹` estimate is established.
-/

namespace AFT

open scoped BigOperators
open scoped Classical

namespace FiniteDist

variable {G : Type*} [Fintype G] [AddCommGroup G]

























/-- A concrete uniform distribution on a nonempty safe subset. -/
noncomputable def uniformSafe (safe : Finset G) (hsafe : safe.Nonempty) : FiniteDist G where
  weight x := if x ∈ safe then (safe.card : ℝ)⁻¹ else 0
  nonneg x := by split_ifs <;> positivity
  sum_one := by
    have hc : (safe.card : ℝ) ≠ 0 := by exact_mod_cast hsafe.card_ne_zero
    simp [hc]













section Conditioning

variable {Ω : Type*} [Fintype Ω]











end Conditioning

end FiniteDist

end AFT

end

section






/-!
# Trimmed laws on the actual finite output palette
-/

namespace AFT.TrimmedSlice

open scoped BigOperators

/-- The actual slice, represented in the finite palette. -/
noncomputable def paletteSlice (modulus : ℕ) (boundary shift : ℤ) : Finset (Fin modulus) :=
  Finset.univ.filter fun color => (color.val : ℤ) ∈ slice modulus boundary shift

theorem paletteSlice_image (modulus : ℕ) (boundary shift : ℤ) (hboundary : 0 ≤ boundary) :
    (paletteSlice modulus boundary shift).image (fun color => (color.val : ℤ)) =
      slice modulus boundary shift := by
  ext color
  constructor
  · intro hc
    obtain ⟨point, hp, rfl⟩ := Finset.mem_image.mp hc
    exact (Finset.mem_filter.mp hp).2
  · intro hc
    have hb := (mem_slice modulus boundary shift color).mp hc
    have hcolor : 0 ≤ color ∧ color < modulus := by omega
    let point : Fin modulus := ⟨color.toNat, by omega⟩
    have heq : (point.val : ℤ) = color := by dsimp [point]; omega
    refine Finset.mem_image.mpr ⟨point, ?_, heq⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq ▸ hc⟩

theorem paletteSlice_card (modulus : ℕ) (boundary shift : ℤ) (hboundary : 0 ≤ boundary) :
    (paletteSlice modulus boundary shift).card = ((modulus : ℤ) - 2 * boundary - |shift|).toNat := by
  have hinj : Function.Injective (fun color : Fin modulus => (color.val : ℤ)) := by
    intro first second heq
    apply Fin.ext
    dsimp only at heq
    exact_mod_cast heq
  have hh : ((paletteSlice modulus boundary shift).image (fun color => (color.val : ℤ))).card =
      (paletteSlice modulus boundary shift).card :=
    Finset.card_image_iff.mpr (Set.injOn_of_injective hinj)
  rw [paletteSlice_image modulus boundary shift hboundary, slice_card] at hh
  exact hh.symm

theorem paletteSlice_nonempty (modulus : ℕ) (boundary shift : ℤ)
    (hboundary : 0 ≤ boundary) (hwidth : 2 * boundary + |shift| < modulus) :
    (paletteSlice modulus boundary shift).Nonempty := by
  apply Finset.card_pos.mp
  rw [paletteSlice_card modulus boundary shift hboundary]
  omega

/-- The uniform slice is a real finite probability distribution. -/
noncomputable def finiteLaw (modulus : ℕ) (boundary shift : ℤ)
    (hboundary : 0 ≤ boundary) (hwidth : 2 * boundary + |shift| < modulus) : FiniteDist (Fin modulus) :=
  FiniteDist.uniformSafe (paletteSlice modulus boundary shift)
    (paletteSlice_nonempty modulus boundary shift hboundary hwidth)

theorem finiteLaw_weight (modulus : ℕ) (boundary shift : ℤ)
    (hboundary : 0 ≤ boundary) (hwidth : 2 * boundary + |shift| < modulus) (color : Fin modulus) :
    (finiteLaw modulus boundary shift hboundary hwidth).weight color =
      law modulus boundary shift color.val := by
  simp only [finiteLaw, FiniteDist.uniformSafe, paletteSlice, Finset.mem_filter,
    Finset.mem_univ, true_and, law]
  rw [show (Finset.univ.filter fun color : Fin modulus => (color.val : ℤ) ∈ slice modulus boundary shift).card =
      (slice modulus boundary shift).card by
    rw [← paletteSlice, paletteSlice_card modulus boundary shift hboundary, slice_card]]

theorem law_palette_mass (modulus : ℕ) (boundary shift : ℤ)
    (hboundary : 0 ≤ boundary) (hwidth : 2 * boundary + |shift| < modulus) :
    ∑ color : Fin modulus, law modulus boundary shift color.val = 1 := by
  simp_rw [← finiteLaw_weight modulus boundary shift hboundary hwidth]
  exact (finiteLaw modulus boundary shift hboundary hwidth).sum_one

/-- The finite uniform-on-subset L1 identity does not require a group structure. -/
theorem uniformSubset_l1 {ι : Type*} [Fintype ι] (subset : Finset ι) (hsubset : subset.Nonempty) :
    (∑ color, |(FiniteDist.uniformSafe subset hsubset).weight color - (Fintype.card ι : ℝ)⁻¹|) =
      2 * (1 - (subset.card : ℝ) / Fintype.card ι) := by
  classical
  have hs : (0 : ℝ) < subset.card := by exact_mod_cast hsubset.card_pos
  have hle : (subset.card : ℝ) ≤ Fintype.card ι := by exact_mod_cast Finset.card_le_univ subset
  have hcard : (0 : ℝ) < Fintype.card ι := hs.trans_le hle
  have hi : (Fintype.card ι : ℝ)⁻¹ ≤ (subset.card : ℝ)⁻¹ := inv_anti₀ hs hle
  have hpoint (color : ι) :
      |(FiniteDist.uniformSafe subset hsubset).weight color - (Fintype.card ι : ℝ)⁻¹| =
        if color ∈ subset then (subset.card : ℝ)⁻¹ - (Fintype.card ι : ℝ)⁻¹
          else (Fintype.card ι : ℝ)⁻¹ := by
    by_cases hc : color ∈ subset
    · simp only [FiniteDist.uniformSafe, if_pos hc, abs_of_nonneg (sub_nonneg.mpr hi)]
    · simp [FiniteDist.uniformSafe, hc, abs_of_nonneg (inv_nonneg.mpr hcard.le)]
  simp_rw [hpoint]
  rw [Finset.sum_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hcompl : (Finset.univ.filter fun color : ι => color ∉ subset).card = Fintype.card ι - subset.card := by
    simp [← Finset.sdiff_eq_filter, Finset.card_sdiff]
  rw [hcompl, Nat.cast_sub (Finset.card_le_univ subset)]
  field_simp
  ring

/-- Exact L1 deviation of the real trimmed slice from palette uniformity. -/
theorem law_palette_l1 (modulus : ℕ) (boundary shift : ℤ)
    (hboundary : 0 ≤ boundary) (hwidth : 2 * boundary + |shift| < modulus) :
    (∑ color : Fin modulus, |law modulus boundary shift color.val - (modulus : ℝ)⁻¹|) =
      2 * (2 * (boundary : ℝ) + |(shift : ℝ)|) / modulus := by
  have hcard : ((paletteSlice modulus boundary shift).card : ℤ) =
      (modulus : ℤ) - 2 * boundary - |shift| := by
    rw [paletteSlice_card modulus boundary shift hboundary, Int.toNat_of_nonneg (by omega)]
  have hcardReal : ((paletteSlice modulus boundary shift).card : ℝ) =
      (modulus : ℝ) - 2 * boundary - |(shift : ℝ)| := by exact_mod_cast hcard
  have hmodulus : (modulus : ℝ) ≠ 0 := by
    have hnonneg := abs_nonneg shift
    have hh : 0 < modulus := by omega
    exact_mod_cast (ne_of_gt hh)
  simp_rw [← finiteLaw_weight modulus boundary shift hboundary hwidth]
  change (∑ color : Fin modulus, |(FiniteDist.uniformSafe _ _).weight color - _|) = _
  rw [show (modulus : ℝ)⁻¹ = (Fintype.card (Fin modulus) : ℝ)⁻¹ by simp,
    uniformSubset_l1, Fintype.card_fin, hcardReal]
  field_simp
  ring

/-- Actual source displacement and trimming yield a uniform finite-palette
L1 bound for each public interval mixture. -/
theorem averagedLaw_palette_l1_le (modulus : ℕ) (boundary start source shiftBound cutoff : ℤ)
    (width : ℕ) (hwidth : width ≠ 0) (hboundary : 0 ≤ boundary)
    (hbound : ∀ shift ∈ anchorInterval start width, |shift| ≤ shiftBound)
    (hsource : |source| ≤ cutoff) (hclearance : 2 * boundary + shiftBound + cutoff < modulus) :
    (∑ color : Fin modulus, |averagedLaw modulus boundary start source width color.val - (modulus : ℝ)⁻¹|) ≤
      2 * ((shiftBound : ℝ) + cutoff + 2 * boundary) / modulus := by
  have hshift (shift : ℤ) (hs : shift ∈ anchorInterval start width) :
      |shift - source| ≤ shiftBound + cutoff := (abs_sub _ _).trans (add_le_add (hbound shift hs) hsource)
  have hmass := intervalAnchorLaw_mass start width hwidth
  have hrepr (color : Fin modulus) : averagedLaw modulus boundary start source width color.val - (modulus : ℝ)⁻¹ =
      ∑ shift ∈ anchorInterval start width,
        intervalAnchorLaw start width shift * (law modulus boundary (shift - source) color.val - (modulus : ℝ)⁻¹) := by
    simp only [averagedLaw, intervalMixture, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, one_mul]
  calc
    _ ≤ ∑ color : Fin modulus, ∑ shift ∈ anchorInterval start width,
        intervalAnchorLaw start width shift * |law modulus boundary (shift - source) color.val - (modulus : ℝ)⁻¹| := by
      apply Finset.sum_le_sum
      intro color _
      rw [hrepr]
      simpa only [abs_mul, abs_of_nonneg (intervalAnchorLaw_nonneg _ _ _)] using Finset.abs_sum_le_sum_abs
        (fun shift => intervalAnchorLaw start width shift * (law modulus boundary (shift - source) color.val - (modulus : ℝ)⁻¹))
        (anchorInterval start width)
    _ = ∑ shift ∈ anchorInterval start width, intervalAnchorLaw start width shift *
        ∑ color : Fin modulus, |law modulus boundary (shift - source) color.val - (modulus : ℝ)⁻¹| := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ shift ∈ anchorInterval start width, intervalAnchorLaw start width shift *
        (2 * ((shiftBound : ℝ) + cutoff + 2 * boundary) / modulus) := by
      apply Finset.sum_le_sum
      intro shift hs
      apply mul_le_mul_of_nonneg_left _ (intervalAnchorLaw_nonneg _ _ _)
      rw [law_palette_l1 modulus boundary (shift - source) hboundary (by have := hshift shift hs; omega)]
      have hh : |((shift - source : ℤ) : ℝ)| ≤ (shiftBound : ℝ) + cutoff := by exact_mod_cast hshift shift hs
      exact div_le_div_of_nonneg_right (by push_cast at hh ⊢; linarith) (Nat.cast_nonneg modulus)
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]

theorem averagedLaw_palette_mass (modulus : ℕ) (boundary start source shiftBound cutoff : ℤ)
    (width : ℕ) (hwidth : width ≠ 0) (hboundary : 0 ≤ boundary)
    (hbound : ∀ shift ∈ anchorInterval start width, |shift| ≤ shiftBound)
    (hsource : |source| ≤ cutoff) (hclearance : 2 * boundary + shiftBound + cutoff < modulus) :
    ∑ color : Fin modulus, averagedLaw modulus boundary start source width color.val = 1 := by
  unfold averagedLaw intervalMixture
  rw [Finset.sum_comm]
  have heq (shift : ℤ) (hs : shift ∈ anchorInterval start width) :
      (∑ color : Fin modulus, intervalAnchorLaw start width shift * law modulus boundary (shift - source) color.val) =
        intervalAnchorLaw start width shift := by
    rw [← Finset.mul_sum, law_palette_mass modulus boundary (shift - source) hboundary, mul_one]
    have hh := (abs_sub shift source).trans (add_le_add (hbound shift hs) hsource)
    omega
  simpa only [Finset.sum_congr rfl heq] using intervalAnchorLaw_mass start width hwidth

theorem mixedLaw_palette_mass {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary shiftBound cutoff : ℤ) (width : ℕ) (hwidth : width ≠ 0)
    (starts sources : τ → ℤ) (weights : τ → ℝ) (hmass : ∑ index, weights index = 1)
    (hboundary : 0 ≤ boundary)
    (hbound : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclearance : 2 * boundary + shiftBound + cutoff < modulus) :
    ∑ color : Fin modulus, mixedLaw modulus boundary starts sources weights width color.val = 1 := by
  unfold mixedLaw
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, averagedLaw_palette_mass modulus boundary _ _ shiftBound cutoff width hwidth
    hboundary (hbound _) (hsources _) hclearance, mul_one]
  exact hmass

theorem mixedLaw_palette_l1_le {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary shiftBound cutoff : ℤ) (width : ℕ) (hwidth : width ≠ 0)
    (starts sources : τ → ℤ) (weights : τ → ℝ)
    (hweights : ∀ index, 0 ≤ weights index) (hmass : ∑ index, weights index = 1)
    (hboundary : 0 ≤ boundary)
    (hbound : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclearance : 2 * boundary + shiftBound + cutoff < modulus) :
    (∑ color : Fin modulus, |mixedLaw modulus boundary starts sources weights width color.val - (modulus : ℝ)⁻¹|) ≤
      2 * ((shiftBound : ℝ) + cutoff + 2 * boundary) / modulus := by
  have hrepr (color : Fin modulus) : mixedLaw modulus boundary starts sources weights width color.val - (modulus : ℝ)⁻¹ =
      ∑ index, weights index * (averagedLaw modulus boundary (starts index) (sources index) width color.val - (modulus : ℝ)⁻¹) := by
    simp only [mixedLaw, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, one_mul]
  calc
    _ ≤ ∑ color : Fin modulus, ∑ index, weights index *
        |averagedLaw modulus boundary (starts index) (sources index) width color.val - (modulus : ℝ)⁻¹| := by
      apply Finset.sum_le_sum
      intro color _
      rw [hrepr]
      simpa only [abs_mul, abs_of_nonneg (hweights _)] using Finset.abs_sum_le_sum_abs
        (fun index => weights index * (averagedLaw modulus boundary (starts index) (sources index) width color.val - (modulus : ℝ)⁻¹))
        Finset.univ
    _ = ∑ index, weights index * ∑ color : Fin modulus,
        |averagedLaw modulus boundary (starts index) (sources index) width color.val - (modulus : ℝ)⁻¹| := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ index, weights index * (2 * ((shiftBound : ℝ) + cutoff + 2 * boundary) / modulus) :=
      Finset.sum_le_sum fun index _ => mul_le_mul_of_nonneg_left
        (averagedLaw_palette_l1_le modulus boundary (starts index) (sources index) shiftBound cutoff width hwidth
          hboundary (hbound index) (hsources index) hclearance) (hweights index)
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]



/-- The source-averaged mixture retains the trimmed-slice supremum bound. -/
theorem mixedLaw_le {τ : Type*} [Fintype τ] (modulus boundary shiftBound cutoff : ℤ)
    (starts sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ) (hwidth : width ≠ 0)
    (hweights : ∀ index, 0 ≤ weights index) (hmass : ∑ index, weights index = 1)
    (hbound : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclearance : 2 * boundary + shiftBound + cutoff < modulus) (color : ℤ) :
    mixedLaw modulus boundary starts sources weights width color ≤
      1 / ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff) := by
  have hlocal (index : τ) : averagedLaw modulus boundary (starts index) (sources index) width color ≤
      1 / ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff) := by
    unfold averagedLaw intervalMixture
    calc
      _ ≤ ∑ shift ∈ anchorInterval (starts index) width, intervalAnchorLaw (starts index) width shift *
          (1 / ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff)) := by
        apply Finset.sum_le_sum
        intro shift hs
        apply mul_le_mul_of_nonneg_left _ (intervalAnchorLaw_nonneg _ _ _)
        have hh := law_le_of_shift_bound modulus boundary (shift - sources index) (shiftBound + cutoff) color
          ((abs_sub _ _).trans (add_le_add (hbound index shift hs) (hsources index))) (by omega)
        simpa only [Int.cast_add, sub_add_eq_sub_sub] using hh
      _ = _ := by rw [← Finset.sum_mul, intervalAnchorLaw_mass _ _ hwidth, one_mul]
  calc
    _ ≤ ∑ index, weights index * (1 / ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff)) :=
      Finset.sum_le_sum fun index _ => mul_le_mul_of_nonneg_left (hlocal index) (hweights index)
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]

end AFT.TrimmedSlice

end

section






/-!
# The signed diffuse response is controlled by the actual calibration
-/

namespace AFT

open scoped BigOperators









namespace TrimmedSlice

/-- Equal mixture of the two public shift-sign branches. -/
noncomputable def fairMixedLaw {τ : Type*} [Fintype τ] (modulus boundary : ℤ)
    (startsPlus startsMinus sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ) (color : ℤ) : ℝ :=
  (mixedLaw modulus boundary startsPlus sources weights width color +
    mixedLaw modulus boundary startsMinus sources weights width color) / 2



noncomputable def actualFairBasePrimary {σ τ : Type*} [Fintype σ] [Fintype τ]
    (modulus margin boundary : ℤ) (width : ℕ) (bodies legs activation : ℝ)
    (bodyShifts : σ → ℤ) (bodyWeights : σ → ℝ)
    (startsPlus startsMinus sources : τ → ℤ) (weights : τ → ℝ) : ℤ → ℝ :=
  basePrimaryProfile (bodies + 2 * legs) bodies legs activation
    (fun _ => 1 / (modulus : ℝ)) (blurredSafeLaw modulus margin bodyShifts bodyWeights)
    (fairMixedLaw modulus boundary startsPlus startsMinus sources weights width)
    (fairMixedLaw modulus boundary startsPlus startsMinus (fun _ => 0) weights width)











end TrimmedSlice

end AFT

end

section








namespace AFT
end AFT
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.activation
end AFT.GaussianSource.activation
namespace AFT.Parameters
end AFT.Parameters
namespace AFT.Parameters.anchorWidth
end AFT.Parameters.anchorWidth
namespace AFT.Parameters.legs
end AFT.Parameters.legs
namespace AFT.Parameters.safeMargin
end AFT.Parameters.safeMargin
namespace AFT.primaryCalibrationEnvelope
end AFT.primaryCalibrationEnvelope
namespace AFT.primaryRankEnvelope
end AFT.primaryRankEnvelope
namespace AFT.primaryTranslationEnvelope
end AFT.primaryTranslationEnvelope



/-!
# Actual V7 calibrated sign estimates with all asymptotic losses discharged
-/

namespace AFT

open Filter
open scoped BigOperators Topology



namespace V7Calibration

noncomputable def basePrimary {σ τ : Type*} [Fintype σ] [Fintype τ]
    (parameter : ℕ) (cutoffScale : ℝ) (boundary : ℤ)
    (bodyShifts : σ → ℤ) (bodyLaw : FiniteDist σ)
    (startsPlus startsMinus sources : τ → ℤ) (sourceLaw : FiniteDist τ) :
    Fin (Parameters.modulus parameter) → ℝ := fun color =>
  TrimmedSlice.actualFairBasePrimary (Parameters.modulus parameter) (Parameters.safeMargin parameter)
    boundary (Parameters.anchorWidth parameter) (Parameters.bodies parameter) (Parameters.legs parameter)
    (GaussianSource.v7Activation cutoffScale parameter) bodyShifts bodyLaw.weight
    startsPlus startsMinus sources sourceLaw.weight color.val







end V7Calibration
end AFT

end

section









namespace AFT
end AFT
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.activation
end AFT.GaussianSource.activation
namespace AFT.Parameters
end AFT.Parameters
namespace AFT.Parameters.anchorWidth
end AFT.Parameters.anchorWidth
namespace AFT.Parameters.legs
end AFT.Parameters.legs
namespace AFT.Parameters.safeMargin
end AFT.Parameters.safeMargin
namespace AFT.primaryCalibrationEnvelope
end AFT.primaryCalibrationEnvelope
namespace AFT.primaryRankEnvelope
end AFT.primaryRankEnvelope
namespace AFT.primaryTranslationEnvelope
end AFT.primaryTranslationEnvelope




/-!
# The beta boundary-mass repair preserves the actual primary lower bound
-/

namespace AFT

open Filter
open scoped BigOperators Topology

noncomputable def uniformFiniteProfile {ι : Type*} [DecidableEq ι] (support : Finset ι) (color : ι) : ℝ :=
  if color ∈ support then (support.card : ℝ)⁻¹ else 0





/-- The real V7 boundary palette is the complement of the zero-shift trimmed interval. -/
noncomputable def boundaryPalette (modulus : ℕ) (halfWidth : ℤ) : Finset (Fin modulus) :=
  (TrimmedSlice.paletteSlice modulus halfWidth 0)ᶜ



theorem boundaryPalette_card (modulus : ℕ) (halfWidth : ℤ)
    (hh : 0 ≤ halfWidth) (hsmall : 2 * halfWidth ≤ modulus) :
    ((boundaryPalette modulus halfWidth).card : ℤ) = 2 * halfWidth := by
  rw [boundaryPalette, Finset.card_compl, Fintype.card_fin,
    TrimmedSlice.paletteSlice_card modulus halfWidth 0 hh]
  simp only [abs_zero, Int.sub_zero]
  omega



noncomputable def v7BaseBoundaryMass (cutoffScale : ℝ) (parameter : ℕ) (boundaryHalfWidth : ℤ) : ℝ :=
  (Parameters.dimension parameter : ℝ) * (boundaryPalette (Parameters.modulus parameter) boundaryHalfWidth).card /
    ((Parameters.modulus parameter : ℝ) * Parameters.legs parameter * GaussianSource.v7Activation cutoffScale parameter)





namespace TrimmedSlice









end TrimmedSlice

end AFT

end

section





/-!
# The actual beta-calibrated V7 primary probability and sign response
-/

namespace AFT

open Filter
open scoped BigOperators Topology

theorem uniformFiniteProfile_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (support : Finset ι) (hne : support.Nonempty) :
    ∑ color, uniformFiniteProfile support color = 1 := by
  have hh : (support.card : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hne.card_pos
  simp [uniformFiniteProfile, hh]

namespace V7Calibration

noncomputable def repairedBoundaryMass (parameter : ℕ) (cutoffScale beta : ℝ) (boundary : ℤ) : ℝ :=
  ((boundaryPalette (Parameters.modulus parameter) boundary).card / (Parameters.modulus parameter : ℝ)) /
    (GaussianSource.v7Activation cutoffScale parameter * beta)

noncomputable def primary {σ τ : Type*} [Fintype σ] [Fintype τ]
    (parameter : ℕ) (cutoffScale beta : ℝ) (boundary : ℤ)
    (bodyShifts : σ → ℤ) (bodyLaw : FiniteDist σ)
    (startsPlus startsMinus sources : τ → ℤ) (sourceLaw : FiniteDist τ) :
    Fin (Parameters.modulus parameter) → ℝ :=
  calibratedPrimaryProfile (basePrimary parameter cutoffScale boundary bodyShifts bodyLaw
    startsPlus startsMinus sources sourceLaw)
    (uniformFiniteProfile (boundaryPalette (Parameters.modulus parameter) boundary))
    (uniformFiniteProfile (boundaryPalette (Parameters.modulus parameter) boundary)ᶜ)
    (repairedBoundaryMass parameter cutoffScale beta boundary - v7BaseBoundaryMass cutoffScale parameter boundary)



end V7Calibration
end AFT

end

section






namespace AFT
end AFT
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.referenceMean
end AFT.V7Calibration.referenceMean


/-! # Explicit body/reference norm bounds for the actual calibrated model -/

namespace AFT.V7Calibration

open Filter
open scoped BigOperators Classical Topology

noncomputable section



def bodyCompensation (parameter : ℕ) (cutoffScale : ℝ) : ℝ :=
  (Parameters.legs parameter : ℝ) * GaussianSource.v7Activation cutoffScale parameter / Parameters.bodies parameter



end

end AFT.V7Calibration

end

section





/-!
# Exact multi-coordinate marginals of the integer root slice

The selected coordinates are a literal prefix of the full independent
product, and the law is conditioned on the full integer sum. The numerator
below is derived by the append equivalence of those actual finite spaces.
-/

namespace AFT.RootSlice

open scoped BigOperators Classical

noncomputable section

local instance _root_.AFT.RootSlice.instDecidableEqFin_aFT (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {α : Type*} [Fintype α]

def sumProbability (source : FiniteDist α) (score : α → ℤ) (count : ℕ) (target : ℤ) : ℝ :=
  probability (fun _ : Fin count => source) score target

def prefixLaw (source : FiniteDist α) (score : α → ℤ) (selected remaining : ℕ)
    (h : 0 < sumProbability source score (selected + remaining) 0) :
    FiniteDist (Fin selected → α) :=
  (law (fun _ : Fin (selected + remaining) => source) score 0 h).map
    (fun x i => x (Fin.castAdd remaining i))





/-- The actual first-coordinate law of a population root slice. -/
def marginalLaw (source : FiniteDist α) (score : α → ℤ) (population : ℕ)
    (hn : 0 < population) (h : 0 < sumProbability source score population 0) : FiniteDist α :=
  (prefixLaw source score 1 (population - 1)
    (by have heq : 1 + (population - 1) = population := by omega
        simpa only [heq] using h)).map (Equiv.funUnique (Fin 1) α)






end

end AFT.RootSlice

end

section





namespace AFT
end AFT
namespace AFT.GaussianSource
end AFT.GaussianSource



/-!
# Positive marginals and moments on the actual protected root alphabet
-/

set_option backward.isDefEq.respectTransparency false

namespace AFT.GaussianSource

open scoped BigOperators Classical

noncomputable section

local instance _root_.AFT.GaussianSource.instDecidableEqFin_aFT (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def windowNegate (cutoff : ℕ) (a : Window cutoff) : Window cutoff :=
  ⟨-(a : ℤ), by
    obtain ⟨ha, hb⟩ := Finset.mem_Icc.mp a.property
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩



def rootMarginal (width : ℝ) (cutoff population : ℕ) (hn : 0 < population) :
    FiniteDist (Window cutoff) :=
  RootSlice.marginalLaw (windowGaussian width cutoff) (fun z => (z : ℤ)) population hn
    (window_root_probability_positive width cutoff population)









end

end AFT.GaussianSource

end

section





/-!
# Exact sign reversal of the clipped Gaussian and the conditioned root marginal
-/

set_option backward.isDefEq.respectTransparency false

namespace AFT

open scoped BigOperators

namespace RootSlice

noncomputable section

local instance _root_.AFT.RootSlice.instDecidableEqFin_aFT_1 (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _



end

end RootSlice

namespace GaussianSource

noncomputable def windowNegateEquiv (cutoff : ℕ) : Window cutoff ≃ Window cutoff where
  toFun := windowNegate cutoff
  invFun := windowNegate cutoff
  left_inv value := by apply Subtype.ext; simp [windowNegate]
  right_inv value := by apply Subtype.ext; simp [windowNegate]

@[simp] theorem windowNegateEquiv_val (cutoff : ℕ) (value : Window cutoff) :
    ((windowNegateEquiv cutoff value : Window cutoff) : ℤ) = -(value : ℤ) := rfl

theorem windowGaussian_reflection (width : ℝ) (cutoff : ℕ) (value : Window cutoff) :
    (windowGaussian width cutoff).weight (windowNegateEquiv cutoff value) =
      (windowGaussian width cutoff).weight value := by
  simp only [windowGaussian, FiniteDist.normalize, windowNegateEquiv_val, weight, Int.cast_neg, neg_sq]



end GaussianSource
end AFT

end

section





namespace AFT
end AFT
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.gaussianKernel
end AFT.GaussianSource.gaussianKernel
namespace AFT.GaussianSource.harmonicWidth
end AFT.GaussianSource.harmonicWidth
namespace AFT.GaussianSource.kernelPower
end AFT.GaussianSource.kernelPower
namespace AFT.GaussianSource.powerWidth
end AFT.GaussianSource.powerWidth
namespace AFT.GaussianSource.powerWidth.match_1
end AFT.GaussianSource.powerWidth.match_1
namespace AFT.GaussianSource.shiftedWeight
end AFT.GaussianSource.shiftedWeight
namespace AFT.GaussianSource.sumWidth
end AFT.GaussianSource.sumWidth
namespace AFT.GaussianSource.theta
end AFT.GaussianSource.theta
namespace AFT.GaussianSource.thetaFourier
end AFT.GaussianSource.thetaFourier



/-!
# Finite clipped Gaussian sum probabilities

This file relates the actual finite root sum to integer convolutions, with
an explicit clipping defect and the uniform theta error from Poisson summation.
-/

namespace AFT.GaussianSource

open scoped BigOperators Classical



















noncomputable def integerMass (width : ℝ) (z : ℤ) : ℝ := weight width z / realNormalizer width



theorem integerMass_nonneg (width : ℝ) (hw : 0 < width) (z : ℤ) : 0 ≤ integerMass width z :=
  div_nonneg (weight_pos width z).le (le_trans zero_le_one (realNormalizer_ge_one width hw))

theorem summable_integerMass (width : ℝ) (hw : 0 < width) : Summable (integerMass width) :=
  (summable_weight width hw).div_const _

theorem integerMass_sum (width : ℝ) (hw : 0 < width) : (∑' z : ℤ, integerMass width z) = 1 := by
  unfold integerMass
  rw [tsum_div_const]
  exact div_self (lt_of_lt_of_le zero_lt_one (realNormalizer_ge_one width hw)).ne'







noncomputable def restrictWindow (mass : ℤ → ℝ) (cutoff : ℕ) (z : ℤ) : ℝ :=
  if z ∈ Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ) then mass z else 0







noncomputable def retainedFraction (width : ℝ) (cutoff : ℕ) : ℝ :=
  windowNormalizer width cutoff / realNormalizer width













































end AFT.GaussianSource

end

section








namespace AFT
end AFT
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.gaussianKernel
end AFT.GaussianSource.gaussianKernel
namespace AFT.GaussianSource.harmonicWidth
end AFT.GaussianSource.harmonicWidth
namespace AFT.GaussianSource.kernelPower
end AFT.GaussianSource.kernelPower
namespace AFT.GaussianSource.powerWidth
end AFT.GaussianSource.powerWidth
namespace AFT.GaussianSource.powerWidth.match_1
end AFT.GaussianSource.powerWidth.match_1
namespace AFT.GaussianSource.shiftedWeight
end AFT.GaussianSource.shiftedWeight
namespace AFT.GaussianSource.sumWidth
end AFT.GaussianSource.sumWidth
namespace AFT.GaussianSource.theta
end AFT.GaussianSource.theta
namespace AFT.GaussianSource.thetaFourier
end AFT.GaussianSource.thetaFourier
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.quadraticExponent
end AFT.RootSlice.quadraticExponent



/-!
# Explicit polynomial-exponential bounds for the root convolution error
-/

namespace AFT.GaussianSource

open scoped BigOperators Classical









noncomputable def v7RootWidth (parameter : ℕ) : ℝ := Real.sqrt 8 * parameter












open Filter
open scoped Topology





noncomputable def v7RootCutoff (parameter : ℕ) : ℕ := 3 * parameter ^ 2 - 1











end AFT.GaussianSource

end

section






namespace AFT
end AFT
namespace AFT.V7Calibration
end AFT.V7Calibration




/-!
# The actual body blur of referenceV7

The finite sample includes the true root marginal and independent marginal
attachment/queue indicators. It asserts no independence among different
physical body coordinates.
-/

set_option backward.isDefEq.respectTransparency false

namespace AFT

open scoped BigOperators Classical

noncomputable section

namespace FiniteDist

variable {α : Type*} [Fintype α]

def optional (source : FiniteDist α) (rate : ℝ) (h0 : 0 ≤ rate) (h1 : rate ≤ 1) : FiniteDist (Option α) where
  weight value := match value with | none => 1 - rate | some a => rate * source.weight a
  nonneg value := by cases value with
    | none => exact sub_nonneg.mpr h1
    | some a => exact mul_nonneg h0 (source.nonneg a)
  sum_one := by
    rw [Fintype.sum_option]
    simp only [← Finset.mul_sum, source.sum_one, mul_one]
    ring

@[simp] theorem optional_none (source : FiniteDist α) (rate : ℝ) (h0 h1) :
    (optional source rate h0 h1).weight none = 1 - rate := rfl

@[simp] theorem optional_some (source : FiniteDist α) (rate : ℝ) (h0 h1) (a : α) :
    (optional source rate h0 h1).weight (some a) = rate * source.weight a := rfl



end FiniteDist

namespace GaussianSource

def queueCutoff (parameter : ℕ) : ℕ := parameter ^ 2 - 1

def legRate (parameter : ℕ) : ℝ := (Parameters.legs parameter : ℝ) / Parameters.bodies parameter

def queueRate (parameter : ℕ) : ℝ := (Parameters.modulus parameter : ℝ) / Parameters.bodies parameter

theorem body_rates_le_quarter (parameter : ℕ) : legRate parameter ≤ 1 / 4 ∧ queueRate parameter ≤ 1 / 4 := by
  have hx := Parameters.security_ge_two parameter
  have hm8 : 8 ≤ Parameters.legs parameter := by
    have hh := Nat.pow_le_pow_left hx 30
    change 8 ≤ Parameters.security parameter ^ 30
    omega
  have hdim8m : 8 * Parameters.legs parameter ≤ Parameters.dimension parameter := by
    have hh := (Parameters.dimension_bounds parameter).1
    have heq : Parameters.security parameter ^ 60 = Parameters.legs parameter * Parameters.legs parameter := by
      unfold Parameters.legs
      rw [← pow_add]
    rw [heq] at hh
    exact (Nat.mul_le_mul_right _ hm8).trans hh
  have hx20 : 8 ≤ Parameters.security parameter ^ 20 := by
    have hh := Nat.pow_le_pow_left hx 20
    omega
  have hdim8q : 8 * Parameters.modulus parameter ≤ Parameters.dimension parameter := by
    have hh := Nat.mul_le_mul_left (Parameters.modulus parameter) hx20
    simpa only [Parameters.dimension, Parameters.meanDensity, Nat.mul_comm] using hh
  have hpop := Parameters.population_identity parameter
  have hm4 : 4 * Parameters.legs parameter ≤ Parameters.bodies parameter := by omega
  have hq4 : 4 * Parameters.modulus parameter ≤ Parameters.bodies parameter := by omega
  have hN : (0 : ℝ) < Parameters.bodies parameter := by exact_mod_cast Parameters.bodies_positive parameter
  constructor
  · unfold legRate
    apply (div_le_iff₀ hN).mpr
    have hh : 4 * (Parameters.legs parameter : ℝ) ≤ Parameters.bodies parameter := by exact_mod_cast hm4
    linarith
  · unfold queueRate
    apply (div_le_iff₀ hN).mpr
    have hh : 4 * (Parameters.modulus parameter : ℝ) ≤ Parameters.bodies parameter := by exact_mod_cast hq4
    linarith

def optionalShift {cutoff : ℕ} : Option (Window cutoff) → ℤ
  | none => 0
  | some z => z

def extraSample (cutoffScale : ℝ) (parameter : ℕ) :=
  Option (Window (legCutoff cutoffScale parameter - 1)) × Option (Window (queueCutoff parameter))

instance extraSampleFintype (cutoffScale : ℝ) (parameter : ℕ) : Fintype (extraSample cutoffScale parameter) :=
  inferInstanceAs (Fintype (_ × _))

def extraShift (cutoffScale : ℝ) (parameter : ℕ) (sample : extraSample cutoffScale parameter) : ℤ :=
  optionalShift sample.1 + optionalShift sample.2

def extraBlur (cutoffScale : ℝ) (parameter : ℕ) : FiniteDist (extraSample cutoffScale parameter) :=
  (FiniteDist.optional (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1))
    (legRate parameter) (by unfold legRate; positivity) ((body_rates_le_quarter parameter).1.trans (by norm_num))).prod
  (FiniteDist.optional (windowGaussian parameter (queueCutoff parameter))
    (queueRate parameter) (by unfold queueRate; positivity) ((body_rates_le_quarter parameter).2.trans (by norm_num)))

def bodySample (cutoffScale : ℝ) (parameter : ℕ) :=
  Window (v7RootCutoff parameter) × extraSample cutoffScale parameter

instance bodySampleFintype (cutoffScale : ℝ) (parameter : ℕ) : Fintype (bodySample cutoffScale parameter) :=
  inferInstanceAs (Fintype (_ × _))

def bodyShift (cutoffScale : ℝ) (parameter : ℕ) (sample : bodySample cutoffScale parameter) : ℤ :=
  (sample.1 : ℤ) + extraShift cutoffScale parameter sample.2

def bodyBlur (cutoffScale : ℝ) (parameter : ℕ) : FiniteDist (bodySample cutoffScale parameter) :=
  (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
    (Parameters.bodies_positive parameter)).prod (extraBlur cutoffScale parameter)
























def maxBodyShift (cutoffScale : ℝ) (parameter : ℕ) : ℕ :=
  v7RootCutoff parameter + (legCutoff cutoffScale parameter - 1) + queueCutoff parameter







end GaussianSource

end

end AFT

end

section




/-! # Transport a finite probability law across the unique Fintype instance -/

namespace AFT.FiniteDist

open scoped BigOperators

/-- Only the finite enumeration instance changes. All point weights are
literally preserved, and total mass follows by uniqueness of `Fintype`. -/
def retype {α : Type*} {source : Fintype α} [target : Fintype α]
    (law : @FiniteDist α source) : FiniteDist α where
  weight := @FiniteDist.weight α source law
  nonneg := @FiniteDist.nonneg α source law
  sum_one := by
    have h : source = target := Subsingleton.elim _ _
    cases h
    exact law.sum_one

@[simp] theorem retype_weight {α : Type*} {source : Fintype α} [target : Fintype α]
    (law : @FiniteDist α source) (point : α) : (retype law).weight point = @FiniteDist.weight α source law point := rfl

end AFT.FiniteDist

end

section







/-! # Exact finite scalar expectation identities -/

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]

omit [Fintype β] [Fintype ι] in
theorem expectation_const (law : FiniteDist α) (value : ℝ) :
    law.expectation (fun _ => value) = value := by
  simp only [expectation, ← Finset.sum_mul, law.sum_one, one_mul]

omit [Fintype β] [Fintype ι] in
theorem expectation_add (law : FiniteDist α) (f g : α → ℝ) :
    law.expectation (fun x => f x + g x) = law.expectation f + law.expectation g := by
  simp only [expectation, mul_add, Finset.sum_add_distrib]

omit [Fintype β] [Fintype ι] in
theorem expectation_sub (law : FiniteDist α) (f g : α → ℝ) :
    law.expectation (fun x => f x - g x) = law.expectation f - law.expectation g := by
  simp only [expectation, mul_sub, Finset.sum_sub_distrib]

omit [Fintype β] [Fintype ι] in
theorem expectation_const_mul (law : FiniteDist α) (scalar : ℝ) (f : α → ℝ) :
    law.expectation (fun x => scalar * f x) = scalar * law.expectation f := by
  simp only [expectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

omit [Fintype β] [Fintype ι] in
theorem expectation_mul_const (law : FiniteDist α) (f : α → ℝ) (scalar : ℝ) :
    law.expectation (fun x => f x * scalar) = law.expectation f * scalar := by
  simp only [expectation, ← mul_assoc, Finset.sum_mul]



omit [Fintype ι] in
theorem expectation_comm (first : FiniteDist α) (second : FiniteDist β) (f : α → β → ℝ) :
    first.expectation (fun x => second.expectation (f x)) =
      second.expectation (fun y => first.expectation (fun x => f x y)) := by
  simp only [expectation, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

omit [Fintype ι] in
theorem expectation_prod (first : FiniteDist α) (second : FiniteDist β) (f : α × β → ℝ) :
    (first.prod second).expectation f =
      first.expectation (fun x => second.expectation (fun y => f (x,y))) := by
  simp only [expectation, prod_weight, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]





end
end AFT.FiniteDist

end

section





/-! # Executable finite-table sampling from a uniformly selected ticket

The selection function uses comparisons and subtraction only. The theorem
below identifies its complete output law for every integer count table.
-/

namespace AFT.FiniteTicketSampler

open scoped BigOperators Classical

/-- Index of the bucket containing a ticket, in the specified table order. -/
def bucket : List ℕ → ℕ → ℕ
  | [], _ => 0
  | count :: rest, ticket => if ticket < count then 0 else 1 + bucket rest (ticket - count)

theorem bucket_lt_length (counts : List ℕ) (ticket : ℕ) (h : ticket < counts.sum) :
    bucket counts ticket < counts.length := by
  induction counts generalizing ticket with
  | nil => simp at h
  | cons count rest ih =>
    simp only [List.sum_cons] at h
    simp only [bucket, List.length_cons]
    split_ifs with hfirst
    · omega
    · have hh := ih (ticket - count) (by omega)
      omega







end AFT.FiniteTicketSampler

end

section







/-! # Support-preserving finite count tables and their approximation error

The rounding specification uses real weights. The resulting count table is
sampled by `FiniteTicketSampler.draw`; computability of the original real
weights is a separate obligation, not hidden in this statement.
-/

namespace AFT.FiniteQuantization

open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]

def floorCount (law : FiniteDist Color) (tickets : ℕ) (color : Color) : ℕ :=
  ⌊(tickets : ℝ) * law.weight color⌋₊

def floorTotal (law : FiniteDist Color) (tickets : ℕ) : ℕ := ∑ color, floorCount law tickets color

theorem floorTotal_le (law : FiniteDist Color) (tickets : ℕ) : floorTotal law tickets ≤ tickets := by
  have hh := Finset.sum_le_sum fun color (_ : color ∈ Finset.univ) =>
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg tickets) (law.nonneg color))
  rw [← Finset.mul_sum, law.sum_one, mul_one] at hh
  exact_mod_cast hh

def deficit (law : FiniteDist Color) (tickets : ℕ) : ℕ := tickets - floorTotal law tickets



def count (law : FiniteDist Color) (tickets : ℕ) (fallback color : Color) : ℕ :=
  floorCount law tickets color + if color = fallback then deficit law tickets else 0

theorem count_sum (law : FiniteDist Color) (tickets : ℕ) (fallback : Color) :
    (∑ color, count law tickets fallback color) = tickets := by
  have ht := floorTotal_le law tickets
  simp only [count, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change floorTotal law tickets + (tickets - floorTotal law tickets) = tickets
  omega

def roundedLaw (law : FiniteDist Color) (tickets : ℕ) (ht : 0 < tickets) (fallback : Color) : FiniteDist Color where
  weight color := (count law tickets fallback color : ℝ) / tickets
  nonneg _ := by positivity
  sum_one := by
    rw [← Finset.sum_div, ← Nat.cast_sum, count_sum]
    exact div_self (by exact_mod_cast ht.ne')











end
end AFT.FiniteQuantization

end

section





/-! # Exact ticket implementation of the support-preserving rounded law -/

namespace AFT.FiniteTicketSampler

open scoped BigOperators Classical

def drawFin {n : ℕ} (counts : Fin n → ℕ) (ticket : Fin (∑ index, counts index)) : Fin n :=
  ⟨bucket (List.ofFn counts) ticket.val, by
    have hh := bucket_lt_length (List.ofFn counts) ticket.val
      (by simpa only [List.sum_ofFn] using ticket.isLt)
    simpa only [List.length_ofFn] using hh⟩



end FiniteTicketSampler

namespace FiniteQuantization

open scoped BigOperators Classical
noncomputable section







end
end FiniteQuantization
end AFT

end

section





/-! # A fixed number of independent fair bits implements a dyadic table -/

namespace AFT.FiniteTicketSampler

open scoped BigOperators Classical

/-- Little-endian binary evaluation; the underlying equivalence is explicit. -/
def bitTicket (bits : ℕ) : (Fin bits → Fin 2) → Fin (2 ^ bits) := finFunctionFinEquiv

theorem bitTicket_value (bits : ℕ) (word : Fin bits → Fin 2) :
    (bitTicket bits word).val = ∑ index, (word index).val * 2 ^ index.val :=
  finFunctionFinEquiv_apply word





/-- Sampling from a precomputed integer table needs exactly `bits` input
bits. Selection uses only the executable integer ticket and bucket routines. -/
def drawBitTable {n : ℕ} (bits : ℕ) (counts : Fin n → ℕ) (htotal : ∑ index, counts index = 2 ^ bits)
    (word : Fin bits → Fin 2) : Fin n :=
  drawFin counts (Fin.cast htotal.symm (bitTicket bits word))



end FiniteTicketSampler
end AFT

end

section









/-! # Executable dyadic sampling of finite rational distributions

The executable count table rounds rational numbers, and assigns the remaining
tickets to index zero. Its probability law is compared with the corresponding
real distribution only in the proofs below.
-/

namespace AFT.RationalFiniteQuantization

open scoped BigOperators

variable {size : ℕ}

def floorCount (weight : Fin (size + 1) → ℚ) (tickets : ℕ)
    (index : Fin (size + 1)) : ℕ :=
  ⌊(tickets : ℚ) * weight index⌋₊

def floorTotal (weight : Fin (size + 1) → ℚ) (tickets : ℕ) : ℕ :=
  ∑ index, floorCount weight tickets index

def deficit (weight : Fin (size + 1) → ℚ) (tickets : ℕ) : ℕ :=
  tickets - floorTotal weight tickets

def counts (weight : Fin (size + 1) → ℚ) (tickets : ℕ)
    (index : Fin (size + 1)) : ℕ :=
  floorCount weight tickets index + if index = 0 then deficit weight tickets else 0

theorem floorTotal_le (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (tickets : ℕ) : floorTotal weight tickets ≤ tickets := by
  have hh := Finset.sum_le_sum fun index (_ : index ∈ Finset.univ) =>
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg tickets) (hnonneg index))
  rw [← Finset.mul_sum, hsum, mul_one] at hh
  exact_mod_cast hh

theorem counts_total (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (tickets : ℕ) : ∑ index, counts weight tickets index = tickets := by
  have ht := floorTotal_le weight hnonneg hsum tickets
  simp only [counts, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change floorTotal weight tickets + (tickets - floorTotal weight tickets) = tickets
  omega

/-- Exactly `bits` input bits select a ticket in the rationally computed table. -/
def draw (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (bits : ℕ) (word : Fin bits → Fin 2) : Fin (size + 1) :=
  FiniteTicketSampler.drawBitTable bits (counts weight (2 ^ bits))
    (counts_total weight hnonneg hsum (2 ^ bits)) word

noncomputable section

def law (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1) :
    FiniteDist (Fin (size + 1)) where
  weight index := weight index
  nonneg index := by exact_mod_cast hnonneg index
  sum_one := by exact_mod_cast hsum











def roundedLaw (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (tickets : ℕ) (ht : 0 < tickets) : FiniteDist (Fin (size + 1)) where
  weight index := (counts weight tickets index : ℝ) / tickets
  nonneg _ := by positivity
  sum_one := by
    rw [← Finset.sum_div, ← Nat.cast_sum, counts_total weight hnonneg hsum]
    exact div_self (by exact_mod_cast ht.ne')













end
end AFT.RationalFiniteQuantization

end

section



/-! # A finite rational program for pi with an explicit dyadic error

The program uses two convergent arctangent series and the proved identity
arctan(1/2)+arctan(1/3)=pi/4. No real-number oracle occurs in the program.
-/
namespace AFT.RationalNumerics
open scoped BigOperators

/-- A rational finite sum, executable by ordinary exact arithmetic. -/
def arctanSum (value : ℚ) (terms : ℕ) : ℚ :=
  ∑ index∈Finset.range terms,(-1 : ℚ)^index*value^(2*index+1)/(2*index+1 : ℕ)

def piApprox (bits : ℕ) : ℚ :=
  4*(arctanSum (1/2) (bits+3)+arctanSum (1/3) (bits+3))

noncomputable section
open scoped Classical







end
end AFT.RationalNumerics

end

section




/-! # Executable positive rational approximations to a negative exponential -/
namespace AFT.RationalNumerics
open scoped BigOperators

def expSum (value : ℚ) (terms : ℕ) : ℚ :=
  ∑ index∈Finset.range terms,value^index/(index.factorial : ℕ)

/-- Range reduction followed by a positive Taylor polynomial and an integer
power. In particular no exponential or real floor is evaluated by the code. -/
def expNegScaled (argument : ℚ) (scale bits : ℕ) : ℚ :=
  (expSum (argument/(scale : ℚ)) (bits+scale+1))⁻¹^scale

def expScale (argument : ℚ) : ℕ := 2*⌈max argument 0⌉₊+1

def expNegApprox (argument : ℚ) (bits : ℕ) : ℚ :=
  expNegScaled (max argument 0) (expScale argument) bits

noncomputable section
open scoped Classical

theorem expSum_ge_one (value : ℚ) (hv : 0 ≤ value) (terms : ℕ) (ht : 0 < terms) :
    1 ≤ (expSum value terms : ℝ) := by
  have hh := Finset.single_le_sum (f := fun i : ℕ => value^i/(i.factorial : ℕ))
    (fun i _ => by positivity) (Finset.mem_range.mpr ht)
  have hh' : (1 : ℚ) ≤ expSum value terms := by simpa only [pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,expSum] using hh
  exact_mod_cast hh'









theorem expScale_positive (argument : ℚ) : 0 < expScale argument := by
  unfold expScale
  omega



theorem expNegApprox_positive (argument : ℚ) (bits : ℕ) : 0 < expNegApprox argument bits := by
  have hs : (0 : ℚ) < expScale argument := by exact_mod_cast expScale_positive argument
  have hh := expSum_ge_one (max argument 0/(expScale argument : ℚ))
    (div_nonneg (le_max_right _ _) hs.le) (bits+expScale argument+1) (by omega)
  have hh' : (0 : ℚ) < expSum (max argument 0/(expScale argument : ℚ)) (bits+expScale argument+1) := by
    have hh0 : (0 : ℝ) < (expSum (max argument 0/(expScale argument : ℚ)) (bits+expScale argument+1) : ℝ) := by linarith
    exact_mod_cast hh0
  exact pow_pos (inv_pos.mpr hh') _



end
end AFT.RationalNumerics

end

section






/-! # Executable rational Gaussian weights at rational squared widths -/
namespace AFT.RationalNumerics

/-- Squared width avoids an unnecessary square-root computation. -/
def gaussianRatio (squaredWidth : ℚ) (point : ℤ) : ℚ := (point : ℚ)^2/squaredWidth

def gaussianGuard (squaredWidth : ℚ) (point : ℤ) : ℕ := ⌈gaussianRatio squaredWidth point⌉₊

def gaussianApprox (squaredWidth : ℚ) (point : ℤ) (bits : ℕ) : ℚ :=
  expNegApprox (piApprox (bits+gaussianGuard squaredWidth point+1)*gaussianRatio squaredWidth point) (bits+1)

noncomputable section



theorem gaussianApprox_positive (squaredWidth : ℚ) (point : ℤ) (bits : ℕ) :
    0 < gaussianApprox squaredWidth point bits := expNegApprox_positive _ _

/-- This exact special value keeps both the true and approximate Gaussian
normalizers at least one on every symmetric integer window. -/
theorem gaussianApprox_zero (squaredWidth : ℚ) (bits : ℕ) : gaussianApprox squaredWidth 0 bits=1 := by
  have hz (terms : ℕ) (ht : 0 < terms) : expSum 0 terms=1 := by
    unfold expSum
    rw [Finset.sum_eq_single 0]
    · simp
    · intro index hi hn
      simp [hn]
    · simp [Finset.mem_range.mpr ht]
  simp only [gaussianApprox,gaussianRatio,Int.cast_zero,zero_pow (by decide : 2 ≠ 0),zero_div,mul_zero,
    expNegApprox,max_self,expNegScaled,zero_div]
  rw [hz _ (by omega)]
  simp



end
end AFT.RationalNumerics

end

section







/-! # Materialized finite convolution tables

The executable recurrence stores each complete previous row in an array.
It does not enumerate all source words or recursively recompute its cells.
The work counter counts elementary arithmetic, comparisons and array accesses;
bit costs of the coefficient arithmetic remain separate.
-/
namespace AFT.FiniteConvolutionProgram
open scoped BigOperators

structure Result (R : Type*) where
  data : Array R
  work : ℕ

def lookup {R : Type*} [Zero R] (data : Array R) (target : ℕ) : R :=
  data[target]?.getD 0

/-- `alphabet` is the greatest source index. The previous row is evaluated
once and materialized before constructing the next row. -/
def run {R : Type*} [Semiring R] (alphabet : ℕ) (weight : Fin (alphabet+1) → R) : ℕ → Result R
  | 0 => ⟨#[1],1⟩
  | count+1 =>
      let previous := run alphabet weight count
      ⟨Array.ofFn (fun target : Fin (alphabet*(count+1)+1) =>
        ∑ source : Fin (alphabet+1),if source.val ≤ target.val then
          weight source*lookup previous.data (target.val-source.val) else 0),
        previous.work+(alphabet*(count+1)+1)*(5*(alphabet+1)+2)⟩





noncomputable section
open scoped Classical











end
end AFT.FiniteConvolutionProgram

end

section







/-! # The actual integer-window root probabilities are convolution-array entries -/
namespace AFT.FiniteConvolutionProgram
open GaussianSource
open scoped BigOperators

/-- Explicit increasing indexing of the complete protected integer window. -/
def windowIndexEquiv (cutoff : ℕ) : Fin (2*cutoff+1) ≃ Window cutoff where
  toFun index := ⟨(index.val : ℤ)-(cutoff : ℤ),Finset.mem_Icc.mpr (by have hi := index.isLt; constructor <;> omega)⟩
  invFun point := ⟨(point.val+(cutoff : ℤ)).toNat,by
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp point.property
    omega⟩
  left_inv index := by apply Fin.ext; simp
  right_inv point := by
    apply Subtype.ext
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp point.property
    dsimp only
    rw [Int.toNat_of_nonneg (by omega)]
    omega

/-- An integer target is shifted to the nonnegative coefficient index.
An impossible target below the entire support returns zero directly. -/
def integerLookup {R : Type*} [Zero R] (data : Array R) (radius : ℕ) (target : ℤ) : R :=
  if 0 ≤ target+(radius : ℤ) then lookup data (target+(radius : ℤ)).toNat else 0

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local instance rootConvolutionProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _











end
end AFT.FiniteConvolutionProgram

end

section







/-! # Restriction and normalization of an actual signed output law -/

namespace AFT.SignedConditioning

open scoped BigOperators Classical

noncomputable section

variable {Color : Type*} [Fintype Color]

def restricted (mass : Color → ℝ) (event : Color → Prop) (color : Color) : ℝ :=
  if event color then mass color else 0

def conditionalMass (mass : Color → ℝ) (event : Color → Prop) (color : Color) : ℝ :=
  restricted mass event color / ∑ x, restricted mass event x









end

end AFT.SignedConditioning

end

section









/-! # Executable rational normalization of the actual protected Gaussian -/
namespace AFT.RationalNumerics
open GaussianSource FiniteConvolutionProgram
open scoped BigOperators

/-- Guard precision absorbs the number of atoms before normalization. -/
def windowApproxPrecision (cutoff bits : ℕ) : ℕ := bits+(2*cutoff+1)+1

def windowApproxRaw (squaredWidth : ℚ) (cutoff bits : ℕ) (point : Window cutoff) : ℚ :=
  gaussianApprox squaredWidth point (windowApproxPrecision cutoff bits)

def windowApproxNormalizer (squaredWidth : ℚ) (cutoff bits : ℕ) : ℚ :=
  ∑ index : Fin (2*cutoff+1),
    windowApproxRaw squaredWidth cutoff bits (windowIndexEquiv cutoff index)

/-- This normalized table uses rational arithmetic only, including its denominator. -/
def windowApproxWeight (squaredWidth : ℚ) (cutoff bits : ℕ) (point : Window cutoff) : ℚ :=
  windowApproxRaw squaredWidth cutoff bits point/windowApproxNormalizer squaredWidth cutoff bits

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- Explicit finite numbering computes the same normalizer as the integer-window sum. -/
theorem windowApproxNormalizer_eq_sum (squaredWidth : ℚ) (cutoff bits : ℕ) :
    windowApproxNormalizer squaredWidth cutoff bits =
      ∑ point : Window cutoff, windowApproxRaw squaredWidth cutoff bits point :=
  (windowIndexEquiv cutoff).sum_comp _

theorem windowApproxNormalizer_ge_one (squaredWidth : ℚ) (cutoff bits : ℕ) :
    1 ≤ windowApproxNormalizer squaredWidth cutoff bits := by
  have h := Finset.single_le_sum (f:=windowApproxRaw squaredWidth cutoff bits)
    (fun point _ => (gaussianApprox_positive _ _ _).le) (Finset.mem_univ (windowZero cutoff))
  simpa only [windowApproxNormalizer_eq_sum,windowApproxRaw,windowZero,gaussianApprox_zero] using h

theorem windowApproxWeight_positive (squaredWidth : ℚ) (cutoff bits : ℕ) (point : Window cutoff) :
    0 < windowApproxWeight squaredWidth cutoff bits point :=
  div_pos (gaussianApprox_positive _ _ _) (zero_lt_one.trans_le (windowApproxNormalizer_ge_one _ _ _))

theorem windowApproxWeight_sum (squaredWidth : ℚ) (cutoff bits : ℕ) :
    ∑ point : Window cutoff,windowApproxWeight squaredWidth cutoff bits point=1 := by
  simp only [windowApproxWeight,← Finset.sum_div]
  rw [← windowApproxNormalizer_eq_sum]
  exact div_self (ne_of_gt (zero_lt_one.trans_le (windowApproxNormalizer_ge_one _ _ _)))

/-- The law represented by the executable rational table. -/
def windowApproxLaw (squaredWidth : ℚ) (cutoff bits : ℕ) : FiniteDist (Window cutoff) where
  weight point := (windowApproxWeight squaredWidth cutoff bits point : ℝ)
  nonneg point := by exact_mod_cast (windowApproxWeight_positive squaredWidth cutoff bits point).le
  sum_one := by exact_mod_cast windowApproxWeight_sum squaredWidth cutoff bits



end
end AFT.RationalNumerics

end

section








/-! # Executable fair-bit approximations to every finite Gaussian window -/
namespace AFT.RationalNumerics
open GaussianSource FiniteConvolutionProgram
open scoped BigOperators

def windowTicketBits (cutoff bits : ℕ) : ℕ := bits+(2*cutoff+1)+2

def windowGaussianWeights (squaredWidth : ℚ) (cutoff bits : ℕ) (index : Fin (2*cutoff+1)) : ℚ :=
  windowApproxWeight squaredWidth cutoff bits (windowIndexEquiv cutoff index)

theorem windowGaussianWeights_nonneg (squaredWidth : ℚ) (cutoff bits : ℕ) (index : Fin (2*cutoff+1)) :
    0≤windowGaussianWeights squaredWidth cutoff bits index := (windowApproxWeight_positive _ _ _ _).le

theorem windowGaussianWeights_sum (squaredWidth : ℚ) (cutoff bits : ℕ) :
    ∑ index,windowGaussianWeights squaredWidth cutoff bits index=1 := by
  unfold windowGaussianWeights
  rw [(windowIndexEquiv cutoff).sum_comp]
  exact windowApproxWeight_sum _ _ _

def windowTicketCounts (squaredWidth : ℚ) (cutoff bits : ℕ) : Fin (2*cutoff+1) → ℕ :=
  RationalFiniteQuantization.counts (windowGaussianWeights squaredWidth cutoff (bits+1))
    (2^(windowTicketBits cutoff bits))



def windowGaussianDraw (squaredWidth : ℚ) (cutoff bits : ℕ)
    (word : Fin (windowTicketBits cutoff bits) → Fin 2) : Window cutoff :=
  windowIndexEquiv cutoff (RationalFiniteQuantization.draw (windowGaussianWeights squaredWidth cutoff (bits+1))
    (windowGaussianWeights_nonneg _ _ _) (windowGaussianWeights_sum _ _ _) (windowTicketBits cutoff bits) word)

noncomputable section
set_option backward.isDefEq.respectTransparency false

def windowTicketLaw (squaredWidth : ℚ) (cutoff bits : ℕ) : FiniteDist (Window cutoff) :=
  (RationalFiniteQuantization.roundedLaw (windowGaussianWeights squaredWidth cutoff (bits+1))
    (windowGaussianWeights_nonneg _ _ _) (windowGaussianWeights_sum _ _ _)
    (2^(windowTicketBits cutoff bits)) (by positivity)).map (windowIndexEquiv cutoff)









end
end AFT.RationalNumerics

end

section










/-! # Executable actual leg and queue Gaussian sources

The cutoff constant is a natural number. Both leg cutoffs and Gaussian
weights are computed from integers and rationals; the sampler never asks
for a real exponential, real power, or real ceiling.
-/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics
open scoped BigOperators

/-- The source code uses this integer width and its rational square. -/
def actualAuxiliarySquaredWidth (scale n : ℕ) : ℚ := (scale*n : ℚ)^2









noncomputable section
set_option backward.isDefEq.respectTransparency false























end
end AFT.V7Calibration

end

section





/-! # Physical support of the genuine body blur and public pair inputs -/

namespace AFT.GaussianSource

open Filter
open scoped BigOperators Classical Topology

noncomputable section



def boundaryHalf (cutoffScale : ℝ) (parameter : ℕ) : ℤ :=
  (Parameters.safeMargin parameter : ℤ) - maxBodyShift cutoffScale parameter



def pairSample (cutoffScale : ℝ) (parameter : ℕ) :=
  bodySample cutoffScale parameter × Window (legCutoff cutoffScale parameter - 1)

instance pairSampleFintype (cutoffScale : ℝ) (parameter : ℕ) : Fintype (pairSample cutoffScale parameter) :=
  inferInstanceAs (Fintype (_ × _))

def pairSourceLaw (cutoffScale : ℝ) (parameter : ℕ) : FiniteDist (pairSample cutoffScale parameter) :=
  (bodyBlur cutoffScale parameter).prod (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1))

def pairSourceShift (cutoffScale : ℝ) (parameter : ℕ) (sample : pairSample cutoffScale parameter) : ℤ :=
  sample.2

def startsPlus (cutoffScale : ℝ) (parameter : ℕ) (sample : pairSample cutoffScale parameter) : ℤ :=
  (Parameters.anchorWidth parameter : ℤ) + bodyShift cutoffScale parameter sample.1

def startsMinus (cutoffScale : ℝ) (parameter : ℕ) (sample : pairSample cutoffScale parameter) : ℤ :=
  -(2 * (Parameters.anchorWidth parameter : ℤ)) + 1 + bodyShift cutoffScale parameter sample.1



end

end AFT.GaussianSource

end

section





/-! # Calibrated means with every protected source and blur instantiated -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

def actualPrimary (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) :
    Fin (Parameters.modulus parameter) → ℝ :=
  primary parameter cutoffScale beta (boundaryHalf cutoffScale parameter)
    (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter)
    (startsPlus cutoffScale parameter) (startsMinus cutoffScale parameter)
    (pairSourceShift cutoffScale parameter) (pairSourceLaw cutoffScale parameter)












end

end AFT.V7Calibration

end

section






namespace AFT
end AFT
namespace AFT.Parameters
end AFT.Parameters
namespace AFT.Parameters.anchorWidth
end AFT.Parameters.anchorWidth
namespace AFT.Parameters.safeMargin
end AFT.Parameters.safeMargin
namespace AFT.primaryRankEnvelope
end AFT.primaryRankEnvelope
namespace AFT.primaryTranslationEnvelope
end AFT.primaryTranslationEnvelope


/-!
# The actual local inverse on arbitrary finite Hilbert fibers

Scalar profile bounds extend to arbitrary remaining-coordinate weights.
Applying the inverse separately in each remaining fiber and using its exact
operator equation yields the inverse mixed-activity bound without a
palette-dependent norm-equivalence constant.
-/

namespace AFT

open scoped BigOperators

section FiberTriangle

variable {ι κ : Type*} [Fintype ι] [Fintype κ]









@[simp] theorem coordinateActivity_neg (rate : ℝ) (primary : ι → ℝ) (remaining : κ → ℝ)
    (kernel : ι → κ → ℝ) :
    coordinateActivity rate primary remaining (-kernel) = coordinateActivity rate primary remaining kernel := by
  simp [coordinateActivity, integratedFiberNorm, fixedFiberNorm]

end FiberTriangle

section ProfileAmplification

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Apply an actual profile operator to the distinguished density coordinate. -/
noncomputable def partialProfileOperator (operator : Module.End ℝ (ι → ℝ))
    (primary : ι → ℝ) (kernel : ι → κ → ℝ) : ι → κ → ℝ :=
  fun output rest => operator (fun input => primary input * kernel input rest) output / primary output











omit [Fintype ι] [Fintype κ] in
@[simp] theorem partialProfileOperator_id (primary : ι → ℝ) (kernel : ι → κ → ℝ)
    (hp : ∀ color, 0 < primary color) :
    partialProfileOperator LinearMap.id primary kernel = kernel := by
  funext color rest
  exact mul_div_cancel_left₀ _ (ne_of_gt (hp color))















end ProfileAmplification

end AFT

end

section







/-!
# The actual V7 calibrated inverse on finite mixed fibers
-/

namespace AFT

open Filter
open scoped BigOperators Topology

namespace V7Calibration





/-- Uniform width-W anchors reflected about q-1-c, with a fair direction
at the midpoint. The Boolean is irrelevant off the midpoint. -/
def publicAnchorStart (modulus width : ℕ) (color : Fin modulus) (coin : Bool) : ℤ :=
  if 2 * color.val < modulus - 1 then (modulus : ℤ) - color.val - 2 * width
  else if modulus - 1 < 2 * color.val then (modulus : ℤ) - 1 - color.val + width
  else if coin then (modulus : ℤ) - color.val - 2 * width
    else (modulus : ℤ) - 1 - color.val + width

















end V7Calibration
end AFT

end

section






namespace AFT
end AFT
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary



/-! # Exact public anchor means and their calibrated supremum bound -/

namespace AFT

open Filter
open scoped BigOperators Classical Topology

noncomputable section





namespace V7Calibration

/-- The true fair midpoint anchor kernel, with both non-midpoint directions. -/
def publicAnchorKernel (modulus width : ℕ) (color : Fin modulus) (output : ℤ) : ℝ :=
  (intervalAnchorLaw (publicAnchorStart modulus width color true) width output +
    intervalAnchorLaw (publicAnchorStart modulus width color false) width output) / 2

def anchorMean (modulus width : ℕ) (profile : Fin modulus → ℝ) (output : ℤ) : ℝ :=
  ∑ color, profile color * publicAnchorKernel modulus width color output

theorem publicAnchorKernel_nonneg (modulus width : ℕ) (color : Fin modulus) (output : ℤ) :
    0 ≤ publicAnchorKernel modulus width color output := by
  unfold publicAnchorKernel
  exact div_nonneg (add_nonneg (intervalAnchorLaw_nonneg _ _ _) (intervalAnchorLaw_nonneg _ _ _)) (by norm_num)











end V7Calibration
end
end AFT

end

section





/-!
# Actual public anchor support and the calibrated legal-input projection
-/

namespace AFT.V7Calibration

open scoped BigOperators

/-- Every point of the actual reflected public anchor remains safe after
any displacement admitted by the physical margin. -/
theorem publicAnchorStart_safe (modulus width : ℕ) (color : Fin modulus) (coin : Bool)
    (shift margin : ℤ) (hmodulus : 6 * width + 1 ≤ modulus)
    (hmargin : margin + |shift| ≤ width) (output : ℤ)
    (houtput : output ∈ anchorInterval (publicAnchorStart modulus width color coin + shift) width) :
    margin ≤ output ∧ output < (modulus : ℤ) - margin := by
  have hq : 0 < modulus := Nat.zero_lt_of_lt color.isLt
  have hqcast : ((modulus - 1 : ℕ) : ℤ) = (modulus : ℤ) - 1 := by omega
  have hmod : 6 * (width : ℤ) + 1 ≤ modulus := by exact_mod_cast hmodulus
  have hleft (hhalf : 2 * (color.val : ℤ) ≤ (modulus : ℤ) - 1)
      (hc : output ∈ anchorInterval ((modulus : ℤ) - color.val - 2 * width + shift) width) :
      margin ≤ output ∧ output < (modulus : ℤ) - margin := by
    simp only [anchorInterval, Finset.mem_Ico] at hc
    let offset := (modulus : ℤ) - 1 - color.val + shift - output
    have hl : (width : ℤ) ≤ offset := by dsimp [offset]; omega
    have hu : offset < 2 * (width : ℤ) := by dsimp [offset]; omega
    have hh := publicAnchor_left_safe modulus width color.val offset shift margin |shift|
      hmod (by positivity) hhalf hl hu le_rfl hmargin
    dsimp [offset] at hh
    omega
  have hright (hhalf : (modulus : ℤ) - 1 ≤ 2 * (color.val : ℤ))
      (hc : output ∈ anchorInterval ((modulus : ℤ) - 1 - color.val + width + shift) width) :
      margin ≤ output ∧ output < (modulus : ℤ) - margin := by
    simp only [anchorInterval, Finset.mem_Ico] at hc
    let offset := output - ((modulus : ℤ) - 1 - color.val + shift)
    have hl : (width : ℤ) ≤ offset := by dsimp [offset]; omega
    have hu : offset < 2 * (width : ℤ) := by dsimp [offset]; omega
    have hh := publicAnchor_right_safe modulus width color.val offset shift margin |shift|
      hmod (by exact_mod_cast color.isLt) hhalf hl hu le_rfl hmargin
    dsimp [offset] at hh
    omega
  unfold publicAnchorStart at houtput
  split_ifs at houtput with hl hr hc
  · exact hleft (by omega) houtput
  · exact hright (by omega) houtput
  · exact hleft (by omega) houtput
  · exact hright (by omega) houtput





end AFT.V7Calibration

end

section







/-! # Safe public anchor kernels with the actual optional blur -/

namespace AFT

open Filter
open scoped BigOperators Classical Topology

noncomputable section

theorem intervalAnchorLaw_palette_mass (modulus width : ℕ) (start : ℤ) (hw : width ≠ 0)
    (hsupport : ∀ output ∈ anchorInterval start width, 0 ≤ output ∧ output < modulus) :
    (∑ color : Fin modulus, intervalAnchorLaw start width color.val) = 1 := by
  let support : Finset (Fin modulus) := Finset.univ.filter fun c => (c.val : ℤ) ∈ anchorInterval start width
  have hc : support.card = width := by
    have hh := Finset.card_bij (s := support) (t := anchorInterval start width)
      (fun (c : Fin modulus) _ => (c.val : ℤ))
      (by intro c hc; exact (Finset.mem_filter.mp hc).2)
      (by intro a _ b _ h; change (a.val : ℤ) = b.val at h; apply Fin.ext; exact_mod_cast h)
      (by
        intro output hout
        have hb := hsupport output hout
        let point : Fin modulus := ⟨output.toNat, by omega⟩
        have heq : (point.val : ℤ) = output := by dsimp [point]; omega
        exact ⟨point, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [heq] using hout⟩, heq⟩)
    simpa only [anchorInterval_card] using hh
  simp only [intervalAnchorLaw, ← Finset.sum_filter]
  change (∑ _color ∈ support, (width : ℝ)⁻¹) = 1
  simp [hc, Nat.cast_ne_zero.mpr hw]

namespace V7Calibration
open GaussianSource











theorem publicAnchorKernel_translate (modulus width : ℕ) (color : Fin modulus) (output shift : ℤ) :
    publicAnchorKernel modulus width color (output - shift) =
      (intervalAnchorLaw (publicAnchorStart modulus width color true + shift) width output +
        intervalAnchorLaw (publicAnchorStart modulus width color false + shift) width output) / 2 := by
  simp only [publicAnchorKernel, intervalAnchorLaw_translate]

theorem publicAnchorKernel_safe_mass (modulus width : ℕ) (margin shift : ℤ)
    (hw : width ≠ 0) (hmodulus : 6 * width + 1 ≤ modulus) (hm0 : 0 ≤ margin)
    (hmargin : margin + |shift| ≤ width) (color : Fin modulus) :
    (∑ output : Fin modulus, publicAnchorKernel modulus width color ((output.val : ℤ) - shift)) = 1 ∧
    (∀ output : ℤ, output < margin ∨ (modulus : ℤ) - margin ≤ output →
      publicAnchorKernel modulus width color (output - shift) = 0) := by
  have hs (coin : Bool) (output : ℤ)
      (hout : output ∈ anchorInterval (publicAnchorStart modulus width color coin + shift) width) :=
    publicAnchorStart_safe modulus width color coin shift margin hmodulus hmargin output hout
  constructor
  · simp only [publicAnchorKernel_translate, ← Finset.sum_div, Finset.sum_add_distrib]
    rw [intervalAnchorLaw_palette_mass modulus width _ hw (by intro output hout; have hh := hs true output hout; omega),
      intervalAnchorLaw_palette_mass modulus width _ hw (by intro output hout; have hh := hs false output hout; omega)]
    norm_num
  · intro output hout
    have hz (coin : Bool) : intervalAnchorLaw (publicAnchorStart modulus width color coin + shift) width output = 0 := by
      unfold intervalAnchorLaw
      split_ifs with hmem
      · have hh := hs coin output hmem; omega
      · rfl
    rw [publicAnchorKernel_translate, hz true, hz false]
    norm_num









end V7Calibration
end
end AFT

end

section





/-! # The actual positive, calibrated safe-center probability -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

def safePalette (parameter : ℕ) : Finset (Fin (Parameters.modulus parameter)) :=
  TrimmedSlice.paletteSlice (Parameters.modulus parameter) (Parameters.safeMargin parameter) 0

theorem safePalette_nonempty (parameter : ℕ) : (safePalette parameter).Nonempty := by
  apply TrimmedSlice.paletteSlice_nonempty _ _ _ (by positivity)
  have hh := Parameters.safeSize_positive parameter
  unfold Parameters.safeSize at hh
  simp only [abs_zero, add_zero]
  omega

def actualCoreLaw (parameter : ℕ) : FiniteDist (Fin (Parameters.modulus parameter)) :=
  FiniteDist.uniformSafe (safePalette parameter) (safePalette_nonempty parameter)



theorem safeMargin_le_anchor (parameter : ℕ) : Parameters.safeMargin parameter ≤ Parameters.anchorWidth parameter := by
  have hh : 20 ≤ Parameters.security parameter ^ 30 := by
    have hh := Nat.pow_le_pow_left (Parameters.security_ge_two parameter) 30
    omega
  have hh' := Nat.mul_le_mul_right (Parameters.security parameter ^ 2) hh
  simpa only [Parameters.safeMargin, Parameters.anchorWidth, ← pow_add] using hh'

theorem actual_anchor_safe_mass (parameter : ℕ) (color : Fin (Parameters.modulus parameter)) :
    (∑ output : Fin (Parameters.modulus parameter), publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
      color output.val) = 1 ∧
    (∀ output : Fin (Parameters.modulus parameter), output ∉ safePalette parameter →
      publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color output.val = 0) := by
  have hw : Parameters.anchorWidth parameter ≠ 0 := by
    unfold Parameters.anchorWidth
    exact ne_of_gt (pow_pos (lt_of_lt_of_le (by decide : 0 < 2) (Parameters.security_ge_two parameter)) 32)
  have hh := publicAnchorKernel_safe_mass (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
    (Parameters.safeMargin parameter) 0 hw (Parameters.anchor_clearance parameter) (by positivity)
    (by simpa only [abs_zero, add_zero] using (show (Parameters.safeMargin parameter : ℤ) ≤ Parameters.anchorWidth parameter by exact_mod_cast safeMargin_le_anchor parameter)) color
  refine ⟨hh.1, ?_⟩
  intro output hout
  apply hh.2 output.val
  simp only [safePalette, TrimmedSlice.paletteSlice, Finset.mem_filter, Finset.mem_univ, true_and,
    TrimmedSlice.mem_slice] at hout
  omega



/-- The actual compensated center profile, including the calibrated primary. -/
def actualBodyCenter (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) : Fin (Parameters.modulus parameter) → ℝ :=
  calibratedBodyProfile (actualCoreLaw parameter).weight
    (fun center => anchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
      (actualPrimary cutoffScale parameter beta) center.val)
    (bodyCompensation parameter cutoffScale)





end
end AFT.V7Calibration

end

section









/-!
# The actual integer-window endpoint pair and its exact marginals
-/

namespace AFT.TrimmedSlice

open scoped BigOperators

/-- Draw the first endpoint uniformly from its actual trimmed slice, then
set the second endpoint by the required integer pair sum. -/
noncomputable def orderedPairSlice (modulus : ℕ) (boundary shift : ℤ)
    (first second : Fin modulus) : ℝ :=
  law modulus boundary shift first.val *
    if (second.val : ℤ) = (modulus : ℤ) - 1 + shift - first.val then 1 else 0

theorem orderedPairSlice_nonneg (modulus : ℕ) (boundary shift : ℤ) (first second : Fin modulus) :
    0 ≤ orderedPairSlice modulus boundary shift first second := by
  unfold orderedPairSlice
  exact mul_nonneg (law_nonneg _ _ _ _) (by split_ifs <;> norm_num)

theorem orderedPairSlice_marginal (modulus : ℕ) (boundary shift : ℤ)
    (hb : 0 ≤ boundary) (first : Fin modulus) :
    ∑ second, orderedPairSlice modulus boundary shift first second = law modulus boundary shift first.val := by
  classical
  by_cases hc : (first.val : ℤ) ∈ slice modulus boundary shift
  · have hs := (mem_slice modulus boundary shift first.val).mp hc
    let output := (modulus : ℤ) - 1 + shift - first.val
    have houtput : 0 ≤ output ∧ output < modulus := by dsimp [output]; omega
    let second : Fin modulus := ⟨output.toNat, by omega⟩
    have heq : (second.val : ℤ) = output := by dsimp [second]; omega
    have hdelta (color : Fin modulus) : ((color.val : ℤ) = output) ↔ color = second := by
      constructor
      · intro hh
        apply Fin.ext
        have ht : (color.val : ℤ) = second.val := hh.trans heq.symm
        exact_mod_cast ht
      · rintro rfl
        exact heq
    simp only [orderedPairSlice, ← Finset.mul_sum]
    change law modulus boundary shift first.val * (∑ color : Fin modulus, if (color.val : ℤ) = output then 1 else 0) = _
    simp only [hdelta, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one]
  · simp only [orderedPairSlice, law, if_neg hc, zero_mul, Finset.sum_const_zero]

theorem orderedPairSlice_symmetric (modulus : ℕ) (boundary shift : ℤ)
    (first second : Fin modulus) :
    orderedPairSlice modulus boundary shift first second = orderedPairSlice modulus boundary shift second first := by
  have hrel : ((second.val : ℤ) = (modulus : ℤ) - 1 + shift - first.val) ↔
      ((first.val : ℤ) = (modulus : ℤ) - 1 + shift - second.val) := by omega
  unfold orderedPairSlice
  by_cases hr : (second.val : ℤ) = (modulus : ℤ) - 1 + shift - first.val
  · have hc : (first.val : ℤ) ∈ slice modulus boundary shift ↔
        (second.val : ℤ) ∈ slice modulus boundary shift := by
      simp only [mem_slice]
      omega
    simp only [if_pos hr, if_pos (hrel.mp hr), mul_one, law, hc]
  · simp only [if_neg hr, if_neg (fun hh => hr (hrel.mpr hh)), mul_zero]

noncomputable def averagedPair (modulus : ℕ) (boundary start source : ℤ) (width : ℕ)
    (first second : Fin modulus) : ℝ :=
  ∑ offset ∈ anchorInterval start width,
    intervalAnchorLaw start width offset * orderedPairSlice modulus boundary (offset - source) first second

noncomputable def mixedPair {τ : Type*} [Fintype τ] (modulus : ℕ) (boundary : ℤ)
    (starts sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ) (first second : Fin modulus) : ℝ :=
  ∑ index, weights index * averagedPair modulus boundary (starts index) (sources index) width first second

/-- The exact joint mass keeps the integer sum and its nonconstant slice
denominator; no circular-window replacement is used. -/
theorem averagedPair_formula (modulus : ℕ) (boundary start source : ℤ) (width : ℕ)
    (first second : Fin modulus) :
    averagedPair modulus boundary start source width first second =
      intervalAnchorLaw start width ((first.val : ℤ) + second.val - ((modulus : ℤ) - 1) + source) *
      law modulus boundary ((first.val : ℤ) + second.val - ((modulus : ℤ) - 1)) first.val := by
  let offset := (first.val : ℤ) + second.val - ((modulus : ℤ) - 1) + source
  unfold averagedPair
  rw [Finset.sum_eq_single offset]
  · have hs : offset - source = (first.val : ℤ) + second.val - ((modulus : ℤ) - 1) := by dsimp [offset]; ring
    have hd : (second.val : ℤ) = (modulus : ℤ) - 1 + (offset - source) - first.val := by dsimp [offset]; ring
    simp only [orderedPairSlice]
    rw [if_pos hd, mul_one, hs]
  · intro other _ hne
    have hd : ¬ (second.val : ℤ) = (modulus : ℤ) - 1 + (other - source) - first.val := by
      dsimp [offset] at hne
      omega
    simp [orderedPairSlice, hd]
  · intro hout
    simp only [intervalAnchorLaw, if_neg hout, zero_mul]

theorem mixedPair_first_marginal {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary : ℤ) (starts sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ)
    (hb : 0 ≤ boundary) (first : Fin modulus) :
    ∑ second, mixedPair modulus boundary starts sources weights width first second =
      mixedLaw modulus boundary starts sources weights width first.val := by
  unfold mixedPair mixedLaw averagedPair averagedLaw intervalMixture
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro index _
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, orderedPairSlice_marginal modulus boundary _ hb]

theorem mixedPair_symmetric {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary : ℤ) (starts sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ)
    (first second : Fin modulus) :
    mixedPair modulus boundary starts sources weights width first second =
      mixedPair modulus boundary starts sources weights width second first := by
  simp only [mixedPair, averagedPair, orderedPairSlice_symmetric modulus boundary _ first second]

theorem mixedPair_nonneg {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary : ℤ) (starts sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ)
    (hw : ∀ index, 0 ≤ weights index) (first second : Fin modulus) :
    0 ≤ mixedPair modulus boundary starts sources weights width first second := by
  apply Finset.sum_nonneg
  intro index _
  apply mul_nonneg (hw index)
  apply Finset.sum_nonneg
  intro offset _
  exact mul_nonneg (intervalAnchorLaw_nonneg _ _ _) (orderedPairSlice_nonneg _ _ _ _ _)

theorem mixedPair_mass {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary shiftBound cutoff : ℤ) (width : ℕ) (hwidth : width ≠ 0)
    (starts sources : τ → ℤ) (weights : τ → ℝ)
    (hmass : ∑ index, weights index = 1) (hb : 0 ≤ boundary)
    (hstarts : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclear : 2 * boundary + shiftBound + cutoff < modulus) :
    ∑ first, ∑ second, mixedPair modulus boundary starts sources weights width first second = 1 := by
  simp_rw [mixedPair_first_marginal modulus boundary starts sources weights width hb]
  exact mixedLaw_palette_mass modulus boundary shiftBound cutoff width hwidth starts sources weights hmass hb hstarts hsources hclear

/-- The physical joint endpoint mass has the sharp `1/(W*(q-D))` ceiling. -/
theorem mixedPair_le {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary shiftBound cutoff : ℤ) (width : ℕ)
    (starts sources : τ → ℤ) (weights : τ → ℝ)
    (hweights : ∀ index, 0 ≤ weights index) (hmass : ∑ index, weights index = 1)
    (hstarts : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclear : 2 * boundary + shiftBound + cutoff < modulus) (first second : Fin modulus) :
    mixedPair modulus boundary starts sources weights width first second ≤
      1 / ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff)) := by
  have hden : 0 < (modulus : ℝ) - 2 * boundary - shiftBound - cutoff := by
    have hh : (0 : ℤ) < (modulus : ℤ) - 2 * boundary - shiftBound - cutoff := by omega
    exact_mod_cast hh
  have hrow (index : τ) : averagedPair modulus boundary (starts index) (sources index) width first second ≤
      (width : ℝ)⁻¹ * (1 / ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff)) := by
    rw [averagedPair_formula]
    let shift := (first.val : ℤ) + second.val - ((modulus : ℤ) - 1)
    by_cases hin : shift + sources index ∈ anchorInterval (starts index) width
    · have hs : |shift| ≤ shiftBound + cutoff := by
        have hh := (abs_sub (shift + sources index) (sources index)).trans
          (add_le_add (hstarts index _ hin) (hsources index))
        simpa only [add_sub_cancel_right] using hh
      have hslice := law_le_of_shift_bound (modulus : ℤ) boundary shift (shiftBound + cutoff) first.val hs (by omega)
      have hh := mul_le_mul (intervalAnchorLaw_bound (starts index) (shift + sources index) width)
        hslice (law_nonneg _ _ _ _) (inv_nonneg.mpr (Nat.cast_nonneg width))
      simpa only [Int.cast_add, Int.cast_natCast, sub_add_eq_sub_sub] using hh
    · have hz : intervalAnchorLaw (starts index) width (shift + sources index) = 0 := by simp [intervalAnchorLaw, hin]
      change intervalAnchorLaw (starts index) width (shift + sources index) * _ ≤ _
      rw [hz, zero_mul]
      positivity
  calc
    _ ≤ ∑ index, weights index * ((width : ℝ)⁻¹ *
      (1 / ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff))) :=
      Finset.sum_le_sum fun index _ => mul_le_mul_of_nonneg_left (hrow index) (hweights index)
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]; simp only [one_div, mul_inv_rev, mul_comm]

/-- The endpoint construction is an actual finite probability distribution. -/
noncomputable def mixedPairDistribution {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary shiftBound cutoff : ℤ) (width : ℕ) (hwidth : width ≠ 0)
    (starts sources : τ → ℤ) (sourceLaw : FiniteDist τ) (hb : 0 ≤ boundary)
    (hstarts : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclear : 2 * boundary + shiftBound + cutoff < modulus) : FiniteDist (Fin modulus × Fin modulus) where
  weight point := mixedPair modulus boundary starts sources sourceLaw.weight width point.1 point.2
  nonneg point := mixedPair_nonneg _ _ _ _ _ _ sourceLaw.nonneg _ _
  sum_one := by
    rw [Fintype.sum_prod_type]
    exact mixedPair_mass modulus boundary shiftBound cutoff width hwidth starts sources sourceLaw.weight
      sourceLaw.sum_one hb hstarts hsources hclear



/-- Fixing either endpoint leaves counting-square mass at most
`1/(W*(q-D)^2)`, rather than introducing a palette-size factor. -/
theorem mixedPair_fiber_square_le {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary shiftBound cutoff : ℤ) (width : ℕ) (hwidth : width ≠ 0)
    (starts sources : τ → ℤ) (sourceLaw : FiniteDist τ) (hb : 0 ≤ boundary)
    (hstarts : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclear : 2 * boundary + shiftBound + cutoff < modulus) (first : Fin modulus) :
    (∑ second, mixedPair modulus boundary starts sources sourceLaw.weight width first second ^ 2) ≤
      1 / ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff) ^ 2) := by
  have hden : 0 < (modulus : ℝ) - 2 * boundary - shiftBound - cutoff := by
    have hh : (0 : ℤ) < (modulus : ℤ) - 2 * boundary - shiftBound - cutoff := by omega
    exact_mod_cast hh
  have hheight := mixedPair_le modulus boundary shiftBound cutoff width starts sources sourceLaw.weight
    sourceLaw.nonneg sourceLaw.sum_one hstarts hsources hclear
  have hmarginal := mixedLaw_le (modulus : ℤ) boundary shiftBound cutoff starts sources sourceLaw.weight width
    hwidth sourceLaw.nonneg sourceLaw.sum_one hstarts hsources hclear first.val
  calc
    _ ≤ ∑ second, (1 / ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff))) *
        mixedPair modulus boundary starts sources sourceLaw.weight width first second := by
      apply Finset.sum_le_sum
      intro second _
      have hh := mul_le_mul_of_nonneg_right (hheight first second)
        (mixedPair_nonneg modulus boundary starts sources sourceLaw.weight width sourceLaw.nonneg first second)
      nlinarith only [hh]
    _ = (1 / ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff))) *
        mixedLaw modulus boundary starts sources sourceLaw.weight width first.val := by
      rw [← Finset.mul_sum, mixedPair_first_marginal _ _ _ _ _ _ hb]
    _ ≤ (1 / ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff))) *
        (1 / ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff)) :=
      mul_le_mul_of_nonneg_left (by simpa only [Int.cast_natCast] using hmarginal) (by positivity)
    _ = _ := by
      have hwReal : (width : ℝ) ≠ 0 := by exact_mod_cast hwidth
      field_simp

end AFT.TrimmedSlice

end

section










/-!
# Safely supported canonical seeds for the true integer-window pair
-/

namespace AFT.SafePair

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def restrictPair (core : Finset ι) (mass : ι → ι → ℝ) (first second : ι) : ℝ :=
  if first ∈ core ∧ second ∈ core then mass first second else 0

/-- Canonicalize the actual signed pair by subtracting both true marginals
and restoring its total mass once. -/
noncomputable def canonicalPair (reference : ι → ℝ) (mass : ι → ι → ℝ) (first second : ι) : ℝ :=
  mass first second - reference first * (∑ x, mass x second) -
    (∑ y, mass first y) * reference second +
    (∑ x, ∑ y, mass x y) * reference first * reference second

omit [DecidableEq ι] in
theorem canonicalPair_first (reference : ι → ℝ) (mass : ι → ι → ℝ)
    (href : ∑ color, reference color = 1) (first : ι) :
    ∑ second, canonicalPair reference mass first second = 0 := by
  unfold canonicalPair
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, href, mul_one]
  rw [Finset.sum_comm (f := fun y x => mass x y)]
  ring

omit [DecidableEq ι] in
theorem canonicalPair_transpose (reference : ι → ℝ) (mass : ι → ι → ℝ) (first second : ι) :
    canonicalPair reference mass first second =
      canonicalPair reference (fun x y => mass y x) second first := by
  unfold canonicalPair
  rw [Finset.sum_comm (f := fun x y => mass y x)]
  ring

omit [DecidableEq ι] in
theorem canonicalPair_second (reference : ι → ℝ) (mass : ι → ι → ℝ)
    (href : ∑ color, reference color = 1) (second : ι) :
    ∑ first, canonicalPair reference mass first second = 0 := by
  simp_rw [canonicalPair_transpose reference mass]
  exact canonicalPair_first reference (fun x y => mass y x) href second

/-- The actual seed obtained by deleting the edge strips and using uniform
core centering. Its mass and both marginals are exactly zero. -/
noncomputable def coreSeed (core : Finset ι) (mass : ι → ι → ℝ) : ι → ι → ℝ :=
  canonicalPair (uniformFiniteProfile core) (restrictPair core mass)

theorem coreSeed_canonical (core : Finset ι) (mass : ι → ι → ℝ) (hne : core.Nonempty) :
    (∀ first, ∑ second, coreSeed core mass first second = 0) ∧
    (∀ second, ∑ first, coreSeed core mass first second = 0) :=
  ⟨canonicalPair_first _ _ (uniformFiniteProfile_mass core hne),
    canonicalPair_second _ _ (uniformFiniteProfile_mass core hne)⟩

theorem coreSeed_supported (core : Finset ι) (mass : ι → ι → ℝ)
    (first second : ι) (hout : first ∉ core ∨ second ∉ core) :
    coreSeed core mass first second = 0 := by
  rcases hout with hfirst | hsecond
  · simp [coreSeed, canonicalPair, uniformFiniteProfile, restrictPair, hfirst]
  · simp [coreSeed, canonicalPair, uniformFiniteProfile, restrictPair, hsecond]

/-- Deleting either edge strip is charged to its actual fixed-coordinate
square sum. There is no ambient-palette union bound. -/
theorem restriction_square_loss (core : Finset ι) (mass : ι → ι → ℝ) (rowBound : ℝ)
    (hrow : ∀ first, (∑ second, mass first second ^ 2) ≤ rowBound)
    (hcolumn : ∀ second, (∑ first, mass first second ^ 2) ≤ rowBound) :
    (∑ first, ∑ second, (mass first second - restrictPair core mass first second) ^ 2) ≤
      2 * (coreᶜ.card : ℝ) * rowBound := by
  have hfilter : (Finset.univ.filter fun color : ι => color ∉ core) = coreᶜ := by ext; simp
  have hfirst : (∑ first : ι, ∑ second : ι, if first ∉ core then mass first second ^ 2 else 0) ≤
      (coreᶜ.card : ℝ) * rowBound := by
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [Finset.sum_ite, hfilter]
    simp only [Finset.sum_const_zero, add_zero]
    calc
      _ ≤ ∑ _first ∈ coreᶜ, rowBound := Finset.sum_le_sum fun first _ => hrow first
      _ = _ := by simp
  have hsecond : (∑ first : ι, ∑ second : ι, if second ∉ core then mass first second ^ 2 else 0) ≤
      (coreᶜ.card : ℝ) * rowBound := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [Finset.sum_ite, hfilter]
    simp only [Finset.sum_const_zero, add_zero]
    calc
      _ ≤ ∑ _second ∈ coreᶜ, rowBound := Finset.sum_le_sum fun second _ => hcolumn second
      _ = _ := by simp
  calc
    _ ≤ ∑ first, ∑ second, ((if first ∉ core then mass first second ^ 2 else 0) +
        (if second ∉ core then mass first second ^ 2 else 0)) := by
      apply Finset.sum_le_sum
      intro first _
      apply Finset.sum_le_sum
      intro second _
      by_cases hf : first ∈ core <;> by_cases hs : second ∈ core <;>
        simp [restrictPair, hf, hs, sq_nonneg]
    _ = (∑ first, ∑ second, if first ∉ core then mass first second ^ 2 else 0) +
        (∑ first, ∑ second, if second ∉ core then mass first second ^ 2 else 0) := by
      simp only [Finset.sum_add_distrib]
    _ ≤ _ := by linarith

/-- For the actual integer-window pair, the deleted-core square loss is
`4*coreDepth/(W*(q-D)^2)` before uniform-profile scaling by q². -/
theorem actual_core_square_loss {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary shiftBound cutoff coreDepth : ℤ) (width : ℕ) (hwidth : width ≠ 0)
    (starts sources : τ → ℤ) (sourceLaw : FiniteDist τ) (hb : 0 ≤ boundary)
    (hcore : 0 ≤ coreDepth) (hcoreSmall : 2 * coreDepth ≤ modulus)
    (hstarts : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclear : 2 * boundary + shiftBound + cutoff < modulus) :
    let mass := TrimmedSlice.mixedPair modulus boundary starts sources sourceLaw.weight width
    let core := TrimmedSlice.paletteSlice modulus coreDepth 0
    (∑ first, ∑ second, (mass first second - restrictPair core mass first second) ^ 2) ≤
      4 * (coreDepth : ℝ) /
        ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff) ^ 2) := by
  dsimp only
  have hrow := TrimmedSlice.mixedPair_fiber_square_le modulus boundary shiftBound cutoff width hwidth
    starts sources sourceLaw hb hstarts hsources hclear
  have hcolumn (second : Fin modulus) :
      (∑ first, TrimmedSlice.mixedPair modulus boundary starts sources sourceLaw.weight width first second ^ 2) ≤
        1 / ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff) ^ 2) := by
    simpa only [TrimmedSlice.mixedPair_symmetric modulus boundary starts sources sourceLaw.weight width _ second] using hrow second
  have hcard : ((TrimmedSlice.paletteSlice modulus coreDepth 0)ᶜ.card : ℝ) = 2 * (coreDepth : ℝ) := by
    exact_mod_cast boundaryPalette_card modulus coreDepth hcore hcoreSmall
  have hh := restriction_square_loss (TrimmedSlice.paletteSlice modulus coreDepth 0)
    (TrimmedSlice.mixedPair modulus boundary starts sources sourceLaw.weight width)
    (1 / ((width : ℝ) * ((modulus : ℝ) - 2 * boundary - shiftBound - cutoff) ^ 2)) hrow hcolumn
  rw [hcard] at hh
  exact hh.trans_eq (by ring)

end AFT.SafePair

end

section








namespace AFT
end AFT
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap


/-! # The actual inactive source and shared-source local triple identities -/

namespace AFT

open Filter
open scoped BigOperators Classical Topology

noncomputable section

namespace FiniteDist
variable {α : Type*} [Fintype α]

theorem atom_le_one (p : FiniteDist α) (point : α) : p.weight point ≤ 1 := by
  have hh := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => p.nonneg i) (Finset.mem_univ point)
  simpa only [p.sum_one] using hh





end FiniteDist

namespace GaussianSource









end GaussianSource

namespace V7Calibration
open GaussianSource

























end V7Calibration
end
end AFT

end

section







/-! # Translation of the genuine integer pair window and its denominator -/

set_option backward.isDefEq.respectTransparency false

namespace AFT.TrimmedSlice

open scoped BigOperators

/-- A positive extension of the real reciprocal slice length. On every
allowed window it agrees exactly with the physical denominator; the
extension merely permits a global translation estimate. -/
noncomputable def reciprocalSlice (modulus boundary lower : ℝ) (sum : ℤ) : ℝ :=
  (max (modulus - 2 * boundary - |(sum : ℝ)|) lower)⁻¹

theorem reciprocalSlice_nonneg (modulus boundary lower : ℝ) (hlower : 0 < lower) (sum : ℤ) :
    0 ≤ reciprocalSlice modulus boundary lower sum := by
  unfold reciprocalSlice
  exact inv_nonneg.mpr ((le_max_right _ _).trans' hlower.le)

theorem reciprocalSlice_le (modulus boundary lower : ℝ) (hlower : 0 < lower) (sum : ℤ) :
    reciprocalSlice modulus boundary lower sum ≤ lower⁻¹ := by
  exact inv_anti₀ hlower (le_max_right _ _)

/-- The nonconstant denominator has Lipschitz cost 1/lower², derived
from the integer absolute-value slice length. -/
theorem reciprocalSlice_lipschitz (modulus boundary lower : ℝ) (hlower : 0 < lower) (first second : ℤ) :
    |reciprocalSlice modulus boundary lower first - reciprocalSlice modulus boundary lower second| ≤
      |(first : ℝ) - second| / lower ^ 2 := by
  let a := max (modulus - 2 * boundary - |(first : ℝ)|) lower
  let b := max (modulus - 2 * boundary - |(second : ℝ)|) lower
  have ha : lower ≤ a := le_max_right _ _
  have hb : lower ≤ b := le_max_right _ _
  have ha0 : 0 < a := hlower.trans_le ha
  have hb0 : 0 < b := hlower.trans_le hb
  have hdiff : |b - a| ≤ |(first : ℝ) - second| := by
    have hh := abs_max_sub_max_le_abs (modulus - 2 * boundary - |(second : ℝ)|)
      (modulus - 2 * boundary - |(first : ℝ)|) lower
    have heq : modulus - 2 * boundary - |(second : ℝ)| - (modulus - 2 * boundary - |(first : ℝ)|) =
        |(first : ℝ)| - |(second : ℝ)| := by ring
    rw [heq] at hh
    exact hh.trans (abs_abs_sub_abs_le _ _)
  have hprod : lower ^ 2 ≤ a * b := by nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  change |a⁻¹ - b⁻¹| ≤ _
  have heq : |a⁻¹ - b⁻¹| = |b - a| / (a * b) := by
    rw [inv_sub_inv ha0.ne' hb0.ne', abs_div, abs_of_pos (mul_pos ha0 hb0)]
  rw [heq]
  exact (div_le_div_of_nonneg_right hdiff (mul_nonneg ha0.le hb0.le)).trans
    (div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hlower) hprod)

noncomputable def weightedIntegerWindow (modulus boundary lower : ℝ) (start source : ℤ) (width : ℕ) (sum : ℤ) : ℝ :=
  intervalAnchorLaw start width (sum + source) * reciprocalSlice modulus boundary lower sum

/-- The pointwise difference separates the two changed window strips from
the exact reciprocal-denominator variation. -/
theorem weightedIntegerWindow_difference_square (modulus boundary lower : ℝ) (hlower : 0 < lower)
    (start source shift sum : ℤ) (width : ℕ) :
    (weightedIntegerWindow modulus boundary lower start source width (sum - shift) -
      weightedIntegerWindow modulus boundary lower start source width sum) ^ 2 ≤
      (2 / lower ^ 2) * (intervalAnchorLaw (start + shift) width (sum + source) - intervalAnchorLaw start width (sum + source)) ^ 2 +
        (2 * (shift : ℝ) ^ 2 / lower ^ 4) * intervalAnchorLaw start width (sum + source) ^ 2 := by
  let a := intervalAnchorLaw (start + shift) width (sum + source)
  let b := intervalAnchorLaw start width (sum + source)
  let u := reciprocalSlice modulus boundary lower (sum - shift)
  let v := reciprocalSlice modulus boundary lower sum
  have heq : weightedIntegerWindow modulus boundary lower start source width (sum - shift) -
      weightedIntegerWindow modulus boundary lower start source width sum = (a - b) * u + b * (u - v) := by
    unfold weightedIntegerWindow
    dsimp [a, b, u, v]
    rw [intervalAnchorLaw_translate]
    have harg : sum + source - shift = sum - shift + source := by omega
    rw [harg]
    ring
  rw [heq]
  have hu0 := reciprocalSlice_nonneg modulus boundary lower hlower (sum - shift)
  have hu := reciprocalSlice_le modulus boundary lower hlower (sum - shift)
  have hdiff := reciprocalSlice_lipschitz modulus boundary lower hlower (sum - shift) sum
  have harg : |((sum - shift : ℤ) : ℝ) - sum| = |(shift : ℝ)| := by push_cast; ring_nf; rw [abs_neg]
  rw [harg] at hdiff
  have husq : u ^ 2 ≤ 1 / lower ^ 2 := by
    have hh := mul_le_mul hu hu hu0 (inv_nonneg.mpr hlower.le)
    simpa only [← sq, inv_pow, one_div] using hh
  have hdiffsq : (u - v) ^ 2 ≤ (shift : ℝ) ^ 2 / lower ^ 4 := by
    change |u - v| ≤ |(shift : ℝ)| / lower ^ 2 at hdiff
    calc
      _ = |u - v| ^ 2 := (sq_abs _).symm
      _ ≤ (|(shift : ℝ)| / lower ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hdiff 2
      _ = _ := by rw [div_pow, sq_abs]; ring
  have h1 := mul_le_mul_of_nonneg_left husq (sq_nonneg (a - b))
  have h2 := mul_le_mul_of_nonneg_left hdiffsq (sq_nonneg b)
  have hsq := sq_nonneg ((a - b) * u - b * (u - v))
  change _ ≤ 2 / lower ^ 2 * (a - b) ^ 2 + 2 * (shift : ℝ) ^ 2 / lower ^ 4 * b ^ 2
  calc
    _ ≤ 2 * ((a - b) * u) ^ 2 + 2 * (b * (u - v)) ^ 2 := by nlinarith only [hsq]
    _ = 2 * ((a - b) ^ 2 * u ^ 2) + 2 * (b ^ 2 * (u - v) ^ 2) := by ring
    _ ≤ 2 * ((a - b) ^ 2 * (1 / lower ^ 2)) + 2 * (b ^ 2 * ((shift : ℝ) ^ 2 / lower ^ 4)) :=
      add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num)) (mul_le_mul_of_nonneg_left h2 (by norm_num))
    _ = _ := by ring

/-- Finite injective sampling of an integer window costs at most its full
counting energy 1/width. -/
theorem finite_window_square_le {ι : Type*} [Fintype ι] (colors : ι → ℤ)
    (hinj : Function.Injective colors) (start : ℤ) (width : ℕ) :
    (∑ color, intervalAnchorLaw start width (colors color) ^ 2) ≤ 1 / (width : ℝ) := by
  have hh := finitePalette_sum_le_support colors hinj (anchorInterval start width)
    (fun color => intervalAnchorLaw start width color ^ 2) (fun _ => sq_nonneg _)
    (fun color hout => by simp [intervalAnchorLaw, hout])
  exact hh.trans_eq (by
    have hsum : (∑ output ∈ anchorInterval start width, intervalAnchorLaw start width output ^ 2) =
        (width : ℝ) * ((width : ℝ)⁻¹) ^ 2 := by
      calc
        _ = ∑ _output ∈ anchorInterval start width, ((width : ℝ)⁻¹) ^ 2 := by
          apply Finset.sum_congr rfl
          intro output ho
          simp only [intervalAnchorLaw, if_pos ho]
        _ = _ := by simp only [Finset.sum_const, anchorInterval_card, nsmul_eq_mul]
    rw [hsum]
    by_cases hw : (width : ℝ) = 0
    · simp [hw]
    · field_simp)

/-- Full finite row bound for the genuine window-with-denominator kernel.
The first term is the window-edge cost and the second is the exact
reciprocal variation; neither introduces a palette factor. -/
theorem weightedIntegerWindow_translation_square_le {ι : Type*} [Fintype ι]
    (colors : ι → ℤ) (hinj : Function.Injective colors)
    (modulus boundary lower : ℝ) (hlower : 0 < lower) (start source shift : ℤ) (width : ℕ) :
    (∑ color, (weightedIntegerWindow modulus boundary lower start source width (colors color - shift) -
      weightedIntegerWindow modulus boundary lower start source width (colors color)) ^ 2) ≤
      4 * (shift.natAbs : ℝ) / (lower ^ 2 * (width : ℝ) ^ 2) +
        2 * (shift : ℝ) ^ 2 / (lower ^ 4 * width) := by
  have hinj' : Function.Injective (fun color => colors color + source) := by intro a b h; apply hinj; exact add_right_cancel h
  have hwindow := finitePalette_sum_le_support (fun color => colors color + source) hinj'
    (anchorInterval start width ∪ anchorInterval (start + shift) width)
    (fun color => (intervalAnchorLaw (start + shift) width color - intervalAnchorLaw start width color) ^ 2)
    (fun _ => sq_nonneg _) (fun color hout => by rw [anchorTranslation_zero_outside _ _ _ _ hout]; simp)
  have hw := hwindow.trans (anchorTranslationSquare_le start shift width)
  have hbase := finite_window_square_le (fun color => colors color + source) hinj' start width
  calc
    _ ≤ ∑ color, ((2 / lower ^ 2) *
        (intervalAnchorLaw (start + shift) width (colors color + source) - intervalAnchorLaw start width (colors color + source)) ^ 2 +
      (2 * (shift : ℝ) ^ 2 / lower ^ 4) * intervalAnchorLaw start width (colors color + source) ^ 2) :=
      Finset.sum_le_sum fun color _ => weightedIntegerWindow_difference_square modulus boundary lower hlower start source shift (colors color) width
    _ = (2 / lower ^ 2) * (∑ color,
        (intervalAnchorLaw (start + shift) width (colors color + source) - intervalAnchorLaw start width (colors color + source)) ^ 2) +
      (2 * (shift : ℝ) ^ 2 / lower ^ 4) * (∑ color, intervalAnchorLaw start width (colors color + source) ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (2 / lower ^ 2) * (2 * (shift.natAbs : ℝ) / (width : ℝ) ^ 2) +
      (2 * (shift : ℝ) ^ 2 / lower ^ 4) * (1 / (width : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hw (by positivity)) (mul_le_mul_of_nonneg_left hbase (by positivity))
    _ = _ := by ring

/-- On its physical window, the extended kernel is exactly the original
integer-sum endpoint law with the true endpoint mask. -/
theorem averagedPair_eq_weightedIntegerWindow (modulus : ℕ) (boundary start source shiftBound cutoff : ℤ)
    (width : ℕ) (lower : ℝ) (hlower : 0 < lower)
    (hstarts : ∀ shift ∈ anchorInterval start width, |shift| ≤ shiftBound)
    (hsource : |source| ≤ cutoff)
    (hclear : lower ≤ (modulus : ℝ) - 2 * boundary - shiftBound - cutoff)
    (first second : Fin modulus) :
    averagedPair modulus boundary start source width first second =
      if boundary ≤ (first.val : ℤ) ∧ (first.val : ℤ) ≤ (modulus : ℤ) - 1 - boundary ∧
          boundary ≤ (second.val : ℤ) ∧ (second.val : ℤ) ≤ (modulus : ℤ) - 1 - boundary then
        weightedIntegerWindow modulus boundary lower start source width
          ((first.val : ℤ) + second.val - ((modulus : ℤ) - 1)) else 0 := by
  rw [averagedPair_formula]
  let total : ℤ := (first.val : ℤ) + second.val - ((modulus : ℤ) - 1)
  have hmask : (first.val : ℤ) ∈ slice modulus boundary total ↔
      boundary ≤ (first.val : ℤ) ∧ (first.val : ℤ) ≤ (modulus : ℤ) - 1 - boundary ∧
        boundary ≤ (second.val : ℤ) ∧ (second.val : ℤ) ≤ (modulus : ℤ) - 1 - boundary := by
    rw [mem_slice]
    dsimp [total]
    omega
  by_cases hwindow : total + source ∈ anchorInterval start width
  · have hshift : |total| ≤ shiftBound + cutoff := by
      have hh := hstarts (total + source) hwindow
      have htriangle := abs_sub (total + source) source
      simp only [add_sub_cancel_right] at htriangle
      linarith
    have hden : lower ≤ (modulus : ℝ) - 2 * boundary - |(total : ℝ)| := by
      have hshift' : |(total : ℝ)| ≤ (shiftBound : ℝ) + cutoff := by exact_mod_cast hshift
      linarith
    have hdenInt : 0 ≤ (modulus : ℤ) - 2 * boundary - |total| := by
      have hh : (0 : ℝ) < (modulus : ℝ) - 2 * boundary - |(total : ℝ)| := hlower.trans_le hden
      have hh' : (0 : ℤ) < (modulus : ℤ) - 2 * boundary - |total| := by exact_mod_cast hh
      omega
    have hcard : ((slice modulus boundary total).card : ℝ) = (modulus : ℝ) - 2 * boundary - |(total : ℝ)| := by
      rw [slice_card]
      exact_mod_cast Int.toNat_of_nonneg hdenInt
    change intervalAnchorLaw start width (total + source) * law modulus boundary total first.val = _
    unfold law
    simp only [hmask, hcard]
    split_ifs with hm
    · change intervalAnchorLaw start width (total + source) * _ =
        intervalAnchorLaw start width (total + source) * reciprocalSlice modulus boundary lower total
      rw [reciprocalSlice, max_eq_left hden]
    · simp
  · have hz : intervalAnchorLaw start width (total + source) = 0 := by simp only [intervalAnchorLaw, if_neg hwindow]
    change intervalAnchorLaw start width (total + source) * law modulus boundary total first.val = _
    rw [hz, zero_mul]
    split_ifs
    · change 0 = intervalAnchorLaw start width (total + source) * reciprocalSlice modulus boundary lower total
      rw [hz, zero_mul]
    · rfl

end AFT.TrimmedSlice

end

section







/-! # Exact endpoint-mask strip costs for an integer-window pair translation -/

namespace AFT.TrimmedSlice

open scoped BigOperators symmDiff

/-- Masking an integer window to an actual finite interval in each output. -/
noncomputable def maskedIntegerPair (modulus boundary lower : ℝ) (start source : ℤ) (width : ℕ)
    (coreStart : ℤ) (coreWidth : ℕ) (first second : ℤ) : ℝ :=
  if first ∈ anchorInterval coreStart coreWidth ∧ second ∈ anchorInterval coreStart coreWidth then
    weightedIntegerWindow modulus boundary lower start source width (first + second - ⌊modulus - 1⌋) else 0

/-- Restricting an injective finite palette to the two changed strips
counts at most twice the integer displacement. -/
theorem interval_change_count_le {ι : Type*} [Fintype ι] (colors : ι → ℤ)
    (hinj : Function.Injective colors) (start shift : ℤ) (width : ℕ) :
    (∑ color, if colors color ∈ anchorInterval start width ∆ anchorInterval (start + shift) width then (1 : ℝ) else 0) ≤
      2 * (shift.natAbs : ℝ) := by
  have hh := finitePalette_sum_le_support colors hinj
    (anchorInterval start width ∆ anchorInterval (start + shift) width)
    (fun color => if color ∈ anchorInterval start width ∆ anchorInterval (start + shift) width then (1 : ℝ) else 0)
    (fun _ => by split_ifs <;> norm_num) (fun color hout => by simp only [if_neg hout])
  have hcard : (∑ color ∈ anchorInterval start width ∆ anchorInterval (start + shift) width,
      if color ∈ anchorInterval start width ∆ anchorInterval (start + shift) width then (1 : ℝ) else 0) =
      2 * (min width shift.natAbs : ℝ) := by
    simp [anchorInterval_symmDiff_card]
  rw [hcard] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right width shift.natAbs) (by norm_num))

/-- Row energy of the exact denominator extension. -/
theorem weightedIntegerWindow_square_le {ι : Type*} [Fintype ι] (colors : ι → ℤ)
    (hinj : Function.Injective colors) (modulus boundary lower : ℝ) (hlower : 0 < lower)
    (start source : ℤ) (width : ℕ) :
    (∑ color, weightedIntegerWindow modulus boundary lower start source width (colors color) ^ 2) ≤
      1 / (lower ^ 2 * width) := by
  have hpoint (color : ι) : weightedIntegerWindow modulus boundary lower start source width (colors color) ^ 2 ≤
      (1 / lower ^ 2) * intervalAnchorLaw start width (colors color + source) ^ 2 := by
    have hnonneg := reciprocalSlice_nonneg modulus boundary lower hlower (colors color)
    have hu := reciprocalSlice_le modulus boundary lower hlower (colors color)
    have hh := mul_le_mul hu hu hnonneg (inv_nonneg.mpr hlower.le)
    have hh' : reciprocalSlice modulus boundary lower (colors color) ^ 2 ≤ 1 / lower ^ 2 := by
      simpa only [← sq, inv_pow, one_div] using hh
    unfold weightedIntegerWindow
    rw [mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right hh' (sq_nonneg _)
  have hinj' : Function.Injective (fun color => colors color + source) := by
    intro a b heq
    exact hinj (add_right_cancel heq)
  calc
    _ ≤ ∑ color, (1 / lower ^ 2) * intervalAnchorLaw start width (colors color + source) ^ 2 :=
      Finset.sum_le_sum fun color _ => hpoint color
    _ = (1 / lower ^ 2) * ∑ color, intervalAnchorLaw start width (colors color + source) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (1 / lower ^ 2) * (1 / (width : ℝ)) :=
      mul_le_mul_of_nonneg_left (finite_window_square_le _ hinj' start width) (by positivity)
    _ = _ := by ring

 theorem masked_difference_square (a b c d : Prop) [Decidable a] [Decidable b] [Decidable c] [Decidable d]
    (first second : ℝ) :
    ((if a ∧ b then first else 0) - (if c ∧ d then second else 0)) ^ 2 ≤
      2 * (first - second) ^ 2 +
      2 * (if (a ∧ ¬c) ∨ (c ∧ ¬a) then second ^ 2 else 0) +
      2 * (if (b ∧ ¬d) ∨ (d ∧ ¬b) then second ^ 2 else 0) := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> by_cases hd : d <;>
    simp only [ha, hb, hc, hd, not_true_eq_false, not_false_eq_true, and_self, and_true, and_false,
      or_self, or_false, false_or, if_true, if_false, sub_zero, zero_sub, neg_sq,
      mul_zero, add_zero] <;>
    nlinarith [sq_nonneg (first - 2 * second), sq_nonneg (first - second), sq_nonneg second]

/-- A shifted core mask changes only its actual one-dimensional symmetric
difference strips, in addition to the integer-sum window change. -/
theorem maskedIntegerPair_difference_square (modulus boundary lower : ℝ)
    (start source firstShift secondShift first second coreStart : ℤ) (width coreWidth : ℕ) :
    (maskedIntegerPair modulus boundary lower start source width coreStart coreWidth (first - firstShift) (second - secondShift) -
      maskedIntegerPair modulus boundary lower start source width coreStart coreWidth first second) ^ 2 ≤
      2 * (weightedIntegerWindow modulus boundary lower start source width
        ((first + second - ⌊modulus - 1⌋) - (firstShift + secondShift)) -
        weightedIntegerWindow modulus boundary lower start source width (first + second - ⌊modulus - 1⌋)) ^ 2 +
      2 * (if first ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + firstShift) coreWidth then
        weightedIntegerWindow modulus boundary lower start source width (first + second - ⌊modulus - 1⌋) ^ 2 else 0) +
      2 * (if second ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + secondShift) coreWidth then
        weightedIntegerWindow modulus boundary lower start source width (first + second - ⌊modulus - 1⌋) ^ 2 else 0) := by
  have hmem (value shift : ℤ) : value - shift ∈ anchorInterval coreStart coreWidth ↔
      value ∈ anchorInterval (coreStart + shift) coreWidth := by
    simp only [anchorInterval, Finset.mem_Ico]
    omega
  have htotal : first - firstShift + (second - secondShift) - ⌊modulus - 1⌋ =
      first + second - ⌊modulus - 1⌋ - (firstShift + secondShift) := by ring
  unfold maskedIntegerPair
  simp only [hmem, htotal]
  have hh := masked_difference_square
    (first ∈ anchorInterval (coreStart + firstShift) coreWidth) (second ∈ anchorInterval (coreStart + secondShift) coreWidth)
    (first ∈ anchorInterval coreStart coreWidth) (second ∈ anchorInterval coreStart coreWidth)
    (weightedIntegerWindow modulus boundary lower start source width
      (first + second - ⌊modulus - 1⌋ - (firstShift + secondShift)))
    (weightedIntegerWindow modulus boundary lower start source width (first + second - ⌊modulus - 1⌋))
  simpa only [Finset.mem_symmDiff, or_comm] using hh

/-- Both endpoint mask costs use one-fixed row energies. The final bound
contains precisely the physical window-edge, reciprocal-denominator, and
endpoint-strip terms. -/
theorem maskedIntegerPair_translation_square_le {ι : Type*} [Fintype ι]
    (colors : ι → ℤ) (hinj : Function.Injective colors)
    (modulus boundary lower : ℝ) (hlower : 0 < lower) (start source firstShift secondShift coreStart : ℤ)
    (width coreWidth : ℕ) :
    (∑ first, ∑ second,
      (maskedIntegerPair modulus boundary lower start source width coreStart coreWidth
        (colors first - firstShift) (colors second - secondShift) -
      maskedIntegerPair modulus boundary lower start source width coreStart coreWidth (colors first) (colors second)) ^ 2) ≤
      2 * (Fintype.card ι : ℝ) *
        (4 * ((firstShift + secondShift).natAbs : ℝ) / (lower ^ 2 * (width : ℝ) ^ 2) +
          2 * ((firstShift + secondShift : ℤ) : ℝ) ^ 2 / (lower ^ 4 * width)) +
      4 * ((firstShift.natAbs : ℝ) + secondShift.natAbs) / (lower ^ 2 * width) := by
  let window (first second : ι) :=
    weightedIntegerWindow modulus boundary lower start source width (colors first + colors second - ⌊modulus - 1⌋)
  have hinjrow (first : ι) : Function.Injective (fun second => colors first + colors second - ⌊modulus - 1⌋) := by
    intro a b heq
    exact hinj (add_left_cancel (sub_left_inj.mp heq))
  have hinjcol (second : ι) : Function.Injective (fun first => colors first + colors second - ⌊modulus - 1⌋) := by
    intro a b heq
    exact hinj (add_right_cancel (sub_left_inj.mp heq))
  have hrows (first : ι) : (∑ second, window first second ^ 2) ≤ 1 / (lower ^ 2 * width) :=
    weightedIntegerWindow_square_le _ (hinjrow first) modulus boundary lower hlower start source width
  have hcols (second : ι) : (∑ first, window first second ^ 2) ≤ 1 / (lower ^ 2 * width) :=
    weightedIntegerWindow_square_le _ (hinjcol second) modulus boundary lower hlower start source width
  have hfirst : (∑ first, ∑ second, if colors first ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + firstShift) coreWidth
      then window first second ^ 2 else 0) ≤ 2 * (firstShift.natAbs : ℝ) / (lower ^ 2 * width) := by
    calc
      _ ≤ ∑ first, if colors first ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + firstShift) coreWidth
          then 1 / (lower ^ 2 * width) else 0 := by
        apply Finset.sum_le_sum
        intro first _
        split_ifs <;> simp_all only [Finset.sum_const_zero, le_refl]
      _ = (∑ first, if colors first ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + firstShift) coreWidth then (1 : ℝ) else 0) /
          (lower ^ 2 * width) := by simp only [Finset.sum_div, ite_div, zero_div, one_div]
      _ ≤ _ := div_le_div_of_nonneg_right (interval_change_count_le colors hinj coreStart firstShift coreWidth) (by positivity)
  have hsecond : (∑ first, ∑ second, if colors second ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + secondShift) coreWidth
      then window first second ^ 2 else 0) ≤ 2 * (secondShift.natAbs : ℝ) / (lower ^ 2 * width) := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ second, if colors second ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + secondShift) coreWidth
          then 1 / (lower ^ 2 * width) else 0 := by
        apply Finset.sum_le_sum
        intro second _
        split_ifs <;> simp_all only [Finset.sum_const_zero, le_refl]
      _ = (∑ second, if colors second ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + secondShift) coreWidth then (1 : ℝ) else 0) /
          (lower ^ 2 * width) := by simp only [Finset.sum_div, ite_div, zero_div, one_div]
      _ ≤ _ := div_le_div_of_nonneg_right (interval_change_count_le colors hinj coreStart secondShift coreWidth) (by positivity)
  have hwindow : (∑ first, ∑ second,
      (weightedIntegerWindow modulus boundary lower start source width
        ((colors first + colors second - ⌊modulus - 1⌋) - (firstShift + secondShift)) - window first second) ^ 2) ≤
      (Fintype.card ι : ℝ) *
        (4 * ((firstShift + secondShift).natAbs : ℝ) / (lower ^ 2 * (width : ℝ) ^ 2) +
          2 * ((firstShift + secondShift : ℤ) : ℝ) ^ 2 / (lower ^ 4 * width)) := by
    calc
      _ ≤ ∑ _first : ι, (4 * ((firstShift + secondShift).natAbs : ℝ) / (lower ^ 2 * (width : ℝ) ^ 2) +
          2 * ((firstShift + secondShift : ℤ) : ℝ) ^ 2 / (lower ^ 4 * width)) :=
        Finset.sum_le_sum fun first _ => weightedIntegerWindow_translation_square_le _ (hinjrow first)
          modulus boundary lower hlower start source (firstShift + secondShift) width
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    _ ≤ ∑ first, ∑ second,
        (2 * (weightedIntegerWindow modulus boundary lower start source width
          ((colors first + colors second - ⌊modulus - 1⌋) - (firstShift + secondShift)) - window first second) ^ 2 +
        2 * (if colors first ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + firstShift) coreWidth then window first second ^ 2 else 0) +
        2 * (if colors second ∈ anchorInterval coreStart coreWidth ∆ anchorInterval (coreStart + secondShift) coreWidth then window first second ^ 2 else 0)) :=
      Finset.sum_le_sum fun first _ => Finset.sum_le_sum fun second _ =>
        maskedIntegerPair_difference_square modulus boundary lower start source firstShift secondShift (colors first) (colors second) coreStart width coreWidth
    _ ≤ _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      have hh := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hwindow (by norm_num : (0 : ℝ) ≤ 2))
        (mul_le_mul_of_nonneg_left hfirst (by norm_num : (0 : ℝ) ≤ 2)))
        (mul_le_mul_of_nonneg_left hsecond (by norm_num : (0 : ℝ) ≤ 2))
      exact hh.trans_eq (by ring)

end AFT.TrimmedSlice

end

section



namespace AFT
end AFT
namespace AFT.FiniteConcentration
end AFT.FiniteConcentration


/-! # Exponential-square concentration for genuine independent Hilbert sums -/

namespace AFT.FiniteConcentration

open scoped BigOperators Classical

noncomputable section

variable {Color Hilbert : Type*} [Fintype Color]
  [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]

def vectorMean (law : FiniteDist Color) (value : Color → Hilbert) : Hilbert :=
  ∑ color, law.weight color • value color











end

end AFT.FiniteConcentration

end

section









namespace AFT
end AFT
namespace AFT.FiniteConcentration
end AFT.FiniteConcentration
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.condition
end AFT.FiniteDist.condition
namespace AFT.LocalTensors
end AFT.LocalTensors



/-! # Exact Hilbert vectors of physical color profiles -/

namespace AFT

open scoped BigOperators Classical

noncomputable section

namespace FiniteConcentration

variable {Sample Hilbert : Type*} [Fintype Sample]
  [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]

theorem vectorMean_norm_le (law : FiniteDist Sample) (value : Sample → Hilbert)
    (bound : ℝ) (hvalue : ∀ sample, ‖value sample‖ ≤ bound) : ‖vectorMean law value‖ ≤ bound := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ sample, law.weight sample * bound := by
      apply Finset.sum_le_sum
      intro sample _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (law.nonneg sample)]
      exact mul_le_mul_of_nonneg_left (hvalue sample) (law.nonneg sample)
    _ = _ := by rw [← Finset.sum_mul, law.sum_one, one_mul]





end FiniteConcentration

namespace ProfileHilbert

variable {Color Sample : Type*} [Fintype Color] [Fintype Sample]

/-- Whitening is a literal linear map into the finite Euclidean space. -/
def whiten (reference : Color → ℝ) : (Color → ℝ) →ₗ[ℝ] EuclideanSpace ℝ Color where
  toFun profile := WithLp.toLp 2 (fun color => profile color / Real.sqrt (reference color))
  map_add' first second := by ext color; simp [add_div]
  map_smul' scalar profile := by ext color; simp [mul_div_assoc]

omit [Fintype Sample] in
@[simp] theorem whiten_apply (reference profile : Color → ℝ) (color : Color) :
    (whiten reference profile).ofLp color = profile color / Real.sqrt (reference color) := rfl

omit [Fintype Sample] in
/-- Its norm is precisely the weighted profile energy. -/
theorem whiten_norm_sq (reference profile : Color → ℝ) (href : ∀ color, 0 ≤ reference color) :
    ‖whiten reference profile‖ ^ 2 = profileSquareNorm reference profile := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [whiten_apply, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt (href _)]
  rfl

/-- Averaging arbitrary joint-source profile vectors retains their Hilbert
bound without a palette-cardinality factor. -/
theorem whiten_average (reference : Color → ℝ) (law : FiniteDist Sample) (profile : Sample → Color → ℝ) :
    whiten reference (fun color => law.expectation (fun sample => profile sample color)) =
      FiniteConcentration.vectorMean law (fun sample => whiten reference (profile sample)) := by
  have hh : (fun color => law.expectation (fun sample => profile sample color)) =
      ∑ sample, law.weight sample • profile sample := by
    funext color
    simp only [FiniteDist.expectation, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hh, map_sum]
  simp only [map_smul, FiniteConcentration.vectorMean]

/-- Centered mixture profiles are the exact average of the centered
component vectors. -/
theorem whiten_mixture_centered (reference : FiniteDist Color) (law : FiniteDist Sample)
    (component : Sample → FiniteDist Color) :
    whiten reference.weight (fun color => (law.mix component).weight color - reference.weight color) =
      FiniteConcentration.vectorMean law (fun sample => whiten reference.weight
        (fun color => (component sample).weight color - reference.weight color)) := by
  rw [← whiten_average]
  congr 1
  funext color
  simp only [FiniteDist.expectation, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    law.sum_one, one_mul, FiniteDist.mix_weight]

end ProfileHilbert

end

end AFT

end

section










namespace AFT
end AFT
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap




/-! # Exact physical triple marginals and their first coefficient energy -/

namespace AFT.PhysicalBlockTensors

open scoped BigOperators Classical

noncomputable section

local instance _root_.AFT.PhysicalBlockTensors.instDecidableEqFin_aFT_1 (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

variable {Source Color : Type*} [Fintype Source] [Fintype Color]















end

end AFT.PhysicalBlockTensors

end

section







namespace AFT
end AFT
namespace AFT.Fock
end AFT.Fock
namespace AFT.Fock.response
end AFT.Fock.response
namespace AFT.Fock.tensorResponse
end AFT.Fock.tensorResponse
namespace AFT.TaggedFock
end AFT.TaggedFock



/-! # Full coefficient and tail bounds for actual independent finite output blocks -/

namespace AFT
namespace BlockProducts

open scoped BigOperators Classical

variable {Index Color : Type*} [Fintype Index] [Fintype Color]
variable (Slots : Index → Type*) [∀ index, Fintype (Slots index)]

/-- The exact product mass on all physical output positions, with one
independent finite law per block and arbitrary dependence within each block. -/
noncomputable def blockMass (law : (index : Index) → FiniteDist (Slots index → Color))
    (word : Sigma Slots → Color) : ℝ :=
  ∏ index, (law index).weight (fun slot => word ⟨index, slot⟩)

set_option backward.isDefEq.respectTransparency false in
/-- The actual independent block mass sums to one. -/
theorem blockMass_sum (law : (index : Index) → FiniteDist (Slots index → Color)) :
    (∑ word, blockMass Slots law word) = 1 := by
  letI : DecidableEq (Sigma Slots) := Classical.decEq _
  have hequiv := (Equiv.piCurry (fun index (_ : Slots index) => Color)).sum_comp
    (fun word => ∏ index, (law index).weight (word index))
  have hmass : (∑ word : (index : Index) → Slots index → Color,
      ∏ index, (law index).weight (word index)) = 1 := by
    rw [← Fintype.prod_sum]
    simp only [FiniteDist.sum_one, Finset.prod_const_one]
  apply Eq.trans ?_ (hequiv.trans hmass)
  unfold blockMass
  apply Finset.sum_congr (by ext; simp)
  intro word _
  rfl

/-- The complete finite output law of independent physical blocks. -/
noncomputable def blockLaw (law : (index : Index) → FiniteDist (Slots index → Color)) :
    FiniteDist (Sigma Slots → Color) where
  weight := blockMass Slots law
  nonneg _ := Finset.prod_nonneg fun index _ => (law index).nonneg _
  sum_one := blockMass_sum Slots law



/-- The actual homogeneous tensor of one physical block. -/
noncomputable def localCoefficient (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (index : Index) (degree : ℕ) :=
  LocalTensors.degreeTensor (fun _ : Slots index => reference) (law index).weight degree

/-- Actual normalized first coefficient for each block. -/
noncomputable def normalizedLinear (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (scale : ℝ) (index : Index) (color : Color) : ℝ :=
  scale * localCoefficient Slots reference law index 1 (fun _ => color)

/-- Actual normalized second coefficient for each block. -/
noncomputable def normalizedQuadratic (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (scale : ℝ)
    (index : Index) (word : Fin 2 → Color) : ℝ :=
  scale ^ 2 * localCoefficient Slots reference law index 2 word

/-- Actual normalized third coefficient for each block. -/
noncomputable def normalizedCubic (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (scale : ℝ)
    (index : Index) (word : Fin 3 → Color) : ℝ :=
  scale ^ 3 * localCoefficient Slots reference law index 3 word







end BlockProducts
end AFT

end

section





/-! # Explicit numberings of block roots, endpoints and edges

These are arithmetic sum/product encodings; no chosen finite enumeration
is part of the runtime representation.
-/
namespace AFT

 def blockNumbering (legs rest : ℕ) : (Fin legs⊕Fin rest)≃Fin (legs+rest) := finSumFinEquiv

 abbrev blockSlotsProgram (legs rest : ℕ) (index : Fin legs⊕Fin rest) :=
  Fin (Sum.elim (fun _ => 3) (fun _ => 1) index)

 def blockVertexSplit (legs rest : ℕ) :
    (Sigma (blockSlotsProgram legs rest))≃
      ((Fin legs×Fin 3)⊕(Fin rest×Fin 1)) where
  toFun point := match point with
    | ⟨.inl leg,slot⟩ => .inl (leg,slot)
    | ⟨.inr body,slot⟩ => .inr (body,slot)
  invFun point := match point with
    | .inl (leg,slot) => ⟨.inl leg,slot⟩
    | .inr (body,slot) => ⟨.inr body,slot⟩
  left_inv point := by rcases point with ⟨leg|body,slot⟩ <;> rfl
  right_inv point := by rcases point with ⟨leg,slot⟩|⟨body,slot⟩ <;> rfl

 def blockVertexNumbering (legs rest : ℕ) :
    (Sigma (blockSlotsProgram legs rest))≃
      Fin (legs*3+rest) :=
  (blockVertexSplit legs rest).trans
    ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans
      (finSumFinEquiv.trans (finCongr (by omega))))

 

end AFT

end

section




namespace AFT
end AFT
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap


/-! # Actual V7 reference probabilities with legal small-parameter fallbacks -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

/-- A finite probability with specified weights whenever those weights are
nonnegative and normalized. The fallback is used only outside that domain. -/
def probabilityOr {Color : Type*} [Fintype Color] (profile : Color → ℝ)
    (fallback : FiniteDist Color) : FiniteDist Color :=
  if h : (∀ color, 0 ≤ profile color) ∧ (∑ color, profile color) = 1 then
    ⟨profile, h.1, h.2⟩ else fallback



def actualPrimaryLaw (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) :
    FiniteDist (Fin (Parameters.modulus parameter)) :=
  probabilityOr (actualPrimary cutoffScale parameter beta) (actualCoreLaw parameter)

def actualBodyLaw (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) :
    FiniteDist (Fin (Parameters.modulus parameter)) :=
  probabilityOr (actualBodyCenter cutoffScale parameter beta) (actualCoreLaw parameter)





end

end AFT.V7Calibration

end

section


















namespace AFT
end AFT
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture





/-! # The actual V7 independent blocks at a fixed root word and queue -/

namespace AFT

open scoped BigOperators Classical

noncomputable section

local instance _root_.AFT.instDecidableEqFin_aFT (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance _root_.AFT.instDecidableEqSum_aFT {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

namespace LocalTensors



end LocalTensors

namespace V7Calibration

open Filter GaussianSource
open scoped Topology







/-- Each leg owns one attached body and two endpoints; every other body is
its own single-output block. -/
abbrev blockIndex (parameter : ℕ) := Fin (Parameters.legs parameter) ⊕ Fin (Parameters.bodies parameter - Parameters.legs parameter)

instance blockIndexFintype (parameter : ℕ) : Fintype (blockIndex parameter) := inferInstanceAs (Fintype (_ ⊕ _))

abbrev blockSlots (parameter : ℕ) (index : blockIndex parameter) :=
  Fin (match index with | .inl _ => 3 | .inr _ => 1)

instance blockSlotsFintype (parameter : ℕ) (index : blockIndex parameter) : Fintype (blockSlots parameter index) := by
  exact inferInstanceAs (Fintype (Fin _))

theorem blockIndex_card (parameter : ℕ) : Fintype.card (blockIndex parameter) = Parameters.bodies parameter := by
  have hh := Parameters.legs_le_half_bodies parameter
  simp only [blockIndex, Fintype.card_sum, Fintype.card_fin]
  omega

/-- Explicit leg-first arithmetic numbering of the actual body roots. -/
def blockIndexNumbering (parameter : ℕ) : blockIndex parameter ≃ Fin (Parameters.bodies parameter) :=
  (blockNumbering (Parameters.legs parameter) (Parameters.bodies parameter-Parameters.legs parameter)).trans
    (finCongr (by have := Parameters.legs_le_half_bodies parameter;omega))











end V7Calibration
end
end AFT

end

section







/-! # Public permutation placements and a single shared queue

All positions use the same realized queue value. Only the selected public
positions receive it. The one-position marginal is derived from the exact
uniform permutation law; no independence of different positions is asserted.
-/

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {Position Sample : Type*} [Fintype Position] [DecidableEq Position] [Nonempty Position]
  [Fintype Sample]





omit [Fintype Sample] in
/-- A public mask is moved by a single random permutation. -/
def permutationMask (selected : Finset Position) (permutation : Equiv.Perm Position) : Finset Position :=
  selected.map permutation.symm.toEmbedding

omit [Fintype Sample] [Fintype Position] [DecidableEq Position] [Nonempty Position] in
@[simp] theorem permutationMask_mem (selected : Finset Position) (permutation : Equiv.Perm Position)
    (position : Position) : position ∈ permutationMask selected permutation ↔ permutation position ∈ selected := by
  simp [permutationMask]

omit [Fintype Sample] [Fintype Position] [DecidableEq Position] [Nonempty Position] in
@[simp] theorem permutationMask_card (selected : Finset Position) (permutation : Equiv.Perm Position) :
    (permutationMask selected permutation).card = selected.card := Finset.card_map _










end
end AFT.FiniteDist

end

section












/-! # Actual public placement of the shared V7 queue -/

namespace AFT.GaussianSource

open scoped BigOperators Classical
open V7Calibration FiniteDist

noncomputable section

set_option backward.isDefEq.respectTransparency false

theorem modulus_le_bodies (parameter : ℕ) : Parameters.modulus parameter ≤ Parameters.bodies parameter := by
  have hb : (0 : ℝ) < Parameters.bodies parameter := by exact_mod_cast Parameters.bodies_positive parameter
  have hh := (body_rates_le_quarter parameter).2.trans (by norm_num : (1 : ℝ) / 4 ≤ 1)
  unfold queueRate at hh
  exact_mod_cast (div_le_one hb).mp hh

/-- A fixed mask of exactly q body indices, subsequently moved by a uniform
public permutation independently of the single hidden queue draw. -/
def actualQueueSelection (parameter : ℕ) : Finset (blockIndex parameter) :=
  Finset.univ.map ((Fin.castLEEmb (modulus_le_bodies parameter)).trans
    (blockIndexNumbering parameter).symm.toEmbedding)

@[simp] theorem actualQueueSelection_card (parameter : ℕ) :
    (actualQueueSelection parameter).card = Parameters.modulus parameter := by
  simp only [actualQueueSelection, Finset.card_map, Finset.card_univ, Fintype.card_fin]











end
end AFT.GaussianSource

end

section




















namespace AFT
end AFT
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.BlockProducts
end AFT.BlockProducts
namespace AFT.BlockProducts.normalizedLinear
end AFT.BlockProducts.normalizedLinear
namespace AFT.FiniteConcentration
end AFT.FiniteConcentration
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.sharedQueueShift
end AFT.FiniteDist.sharedQueueShift
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBlockBodyLaw
end AFT.V7Calibration.actualBlockBodyLaw
namespace AFT.V7Calibration.actualBlockBodyLaw.match_1
end AFT.V7Calibration.actualBlockBodyLaw.match_1
namespace AFT.V7Calibration.actualBlockBodyVector
end AFT.V7Calibration.actualBlockBodyVector
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualRootValue
end AFT.V7Calibration.actualRootValue
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile





/-! # Exact centering of the physical normalized block mean -/

namespace AFT.V7Calibration

open Filter GaussianSource FiniteConcentration
open scoped BigOperators Classical Topology

noncomputable section

local instance actualNormalizedMeanFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualNormalizedMeanSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

def actualRootWord (parameter : ℕ) := Fin (Parameters.bodies parameter) → Window (v7RootCutoff parameter)

instance actualRootWordFintype (parameter : ℕ) : Fintype (actualRootWord parameter) := inferInstanceAs (Fintype (_ → _))















end

end AFT.V7Calibration

end

section





/-!
# The integer beta identity in the calibrated reference

The beta mixture in V7, Lemma `accuracy-beta-reference`, is a genuine
integral identity, not an assumed closeness property.  The lemmas here prove
its integer-parameter integral from mathlib's Gamma/Beta integral.
-/
namespace AFT
namespace BetaReference

open MeasureTheory

/-- The elementary integer beta integral, with no analytic estimates assumed. -/
theorem integer_beta_integral (m n : ℕ) :
    (∫ x : ℝ in (0 : ℝ)..1, x ^ m * (1 - x) ^ n) =
      (m.factorial : ℝ) * n.factorial / (m + n + 1).factorial := by
  have hc : (∫ x : ℝ in (0 : ℝ)..1,
      (x : ℂ) ^ m * (1 - (x : ℂ)) ^ n) =
      (m.factorial : ℂ) * n.factorial / (m + n + 1).factorial := by
    have h := Complex.betaIntegral_eq_Gamma_mul_div
      ((m : ℂ) + 1) ((n : ℂ) + 1) (by simp; positivity) (by simp; positivity)
    simp only [Complex.betaIntegral, add_sub_cancel_right,
      Complex.cpow_natCast, Complex.Gamma_nat_eq_factorial] at h
    convert h using 1
    congr 2
    rw [show (m : ℂ) + 1 + ((n : ℂ) + 1) = ((m + n + 1 : ℕ) : ℂ) + 1 by push_cast; ring,
      Complex.Gamma_nat_eq_factorial]
  have hr : Complex.ofReal (∫ x : ℝ in (0 : ℝ)..1,
      x ^ m * (1 - x) ^ n) =
      ((m.factorial : ℝ) * n.factorial / (m + n + 1).factorial : ℝ) := by
    rw [← intervalIntegral.integral_ofReal]
    simpa using hc
  exact Complex.ofReal_injective hr



/-- The polynomial density of `Beta(K + 1, n + 1)` on `[0,1]`. -/
noncomputable def density (K n : ℕ) (x : ℝ) : ℝ :=
  ((K + n + 1).factorial : ℝ) / (K.factorial * n.factorial) *
    x ^ K * (1 - x) ^ n







/-- The beta density is normalized on the unit interval. -/
theorem density_integral_one (K n : ℕ) :
    (∫ x : ℝ in (0 : ℝ)..1, density K n x) = 1 := by
  have heq : density K n = fun x : ℝ =>
      (((K + n + 1).factorial : ℝ) / (K.factorial * n.factorial)) *
      (x ^ K * (1 - x) ^ n) := by funext x; unfold density; ring
  rw [heq, intervalIntegral.integral_const_mul _ (fun x : ℝ => x ^ K * (1 - x) ^ n),
    integer_beta_integral]
  have hK : (K.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr K.factorial_ne_zero
  have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hN : ((K + n + 1).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (K + n + 1).factorial_ne_zero
  field_simp































end BetaReference
end AFT

end

section





/-!
# Concrete finite convolution operators and palette-independent Hilbert bounds
-/

namespace AFT.SafeConvolution

open scoped BigOperators

variable {G : Type*} [Fintype G] [AddCommGroup G]

noncomputable def kernelL1 (kernel : G → ℝ) : ℝ := ∑ shift, |kernel shift|
noncomputable def countingL2 (profile : G → ℝ) : ℝ := Real.sqrt (∑ color, profile color ^ 2)

noncomputable def convolution (kernel : G → ℝ) : Module.End ℝ (G → ℝ) where
  toFun profile output := ∑ shift, kernel shift * profile (output - shift)
  map_add' first second := by ext output; simp [mul_add, Finset.sum_add_distrib]
  map_smul' scalar profile := by ext output; simp [← Finset.mul_sum, mul_left_comm]

@[simp] theorem convolution_apply (kernel profile : G → ℝ) (output : G) :
    convolution kernel profile output = ∑ shift, kernel shift * profile (output - shift) := rfl

omit [AddCommGroup G] in
theorem kernelL1_nonneg (kernel : G → ℝ) : 0 ≤ kernelL1 kernel :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

omit [AddCommGroup G] in
theorem countingL2_nonneg (profile : G → ℝ) : 0 ≤ countingL2 profile := Real.sqrt_nonneg _

omit [AddCommGroup G] in
theorem countingL2_add (first second : G → ℝ) :
    countingL2 (first + second) ≤ countingL2 first + countingL2 second := by
  simpa only [countingL2, profileSquareNorm, div_one] using
    profileSquareNorm_sqrt_add_le (fun _ : G => (1 : ℝ)) first second (by intro; norm_num)

omit [AddCommGroup G] in
theorem countingL2_smul (scalar : ℝ) (profile : G → ℝ) :
    countingL2 (scalar • profile) = |scalar| * countingL2 profile := by
  unfold countingL2
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum,
    Real.sqrt_mul (sq_nonneg scalar), Real.sqrt_sq_eq_abs]

omit [AddCommGroup G] in
theorem countingL2_neg (profile : G → ℝ) : countingL2 (-profile) = countingL2 profile := by
  simp only [countingL2, Pi.neg_apply, neg_sq]

theorem translated_sum (profile : G → ℝ) (shift : G) :
    (∑ color, profile (color - shift)) = ∑ color, profile color :=
  Equiv.sum_comp (Equiv.subRight shift) profile



/-- Signed Young inequality proved from the actual finite kernel entries. -/
theorem convolution_square_le (kernel profile : G → ℝ) :
    (∑ color, convolution kernel profile color ^ 2) ≤ kernelL1 kernel ^ 2 * ∑ color, profile color ^ 2 := by
  have hpoint (color : G) : convolution kernel profile color ^ 2 ≤
      kernelL1 kernel * ∑ shift, |kernel shift| * profile (color - shift) ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro shift _
      exact abs_nonneg _
    · intro shift _
      exact mul_nonneg (abs_nonneg _) (sq_nonneg _)
    · intro shift _
      rw [mul_pow]
      nlinarith [sq_abs (kernel shift)]
  calc
    _ ≤ ∑ color, kernelL1 kernel * ∑ shift, |kernel shift| * profile (color - shift) ^ 2 :=
      Finset.sum_le_sum fun color _ => hpoint color
    _ = kernelL1 kernel * ∑ shift, |kernel shift| * ∑ color, profile (color - shift) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      simp_rw [translated_sum (fun color => profile color ^ 2)]
      rw [← Finset.sum_mul]
      dsimp [kernelL1]
      ring

theorem convolution_L2_le (kernel profile : G → ℝ) :
    countingL2 (convolution kernel profile) ≤ kernelL1 kernel * countingL2 profile := by
  exact (Real.sqrt_le_sqrt (convolution_square_le kernel profile)).trans_eq (by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (kernelL1_nonneg kernel)]
    rfl)

theorem probability_convolution_L2_le (source : FiniteDist G) (profile : G → ℝ) :
    countingL2 (convolution source.weight profile) ≤ countingL2 profile := by
  have hmass : kernelL1 source.weight = 1 := by simp only [kernelL1, abs_of_nonneg (source.nonneg _), source.sum_one]
  simpa only [hmass, one_mul] using convolution_L2_le source.weight profile











end AFT.SafeConvolution

end

section






namespace AFT
end AFT
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.intervalDistribution
end AFT.SafeConvolution.intervalDistribution
namespace AFT.SafeConvolution.intervalKernel
end AFT.SafeConvolution.intervalKernel
namespace AFT.SafeConvolution.pushIntegerKernel
end AFT.SafeConvolution.pushIntegerKernel
namespace AFT.finiteCorrection
end AFT.finiteCorrection


/-! # Finite compactly smoothed root inverse with its exact residual -/

namespace AFT.SafeConvolution

open scoped BigOperators

variable {G σ : Type*} [Fintype G] [AddCommGroup G] [Fintype σ]



omit [AddCommGroup G] in
theorem operator_power_L2_le (operator : Module.End ℝ (G → ℝ)) (bound : ℝ) (hbound : 0 ≤ bound)
    (hoperator : ∀ profile, countingL2 (operator profile) ≤ bound * countingL2 profile)
    (order : ℕ) (profile : G → ℝ) :
    countingL2 ((operator ^ order) profile) ≤ bound ^ order * countingL2 profile := by
  induction order with
  | zero => simp
  | succ order ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact (hoperator _).trans ((mul_le_mul_of_nonneg_left ih hbound).trans_eq (by ring))



theorem probability_power_L2_le (source : FiniteDist G) (order : ℕ) (profile : G → ℝ) :
    countingL2 ((convolution source.weight ^ order) profile) ≤ countingL2 profile := by
  simpa only [one_pow, one_mul] using operator_power_L2_le (convolution source.weight) 1 (by norm_num)
    (fun profile => by simpa only [one_mul] using probability_convolution_L2_le source profile) order profile







variable [DecidableEq G]



end AFT.SafeConvolution

end

section





/-! # Exact canonicality under the finite smoothing and Neumann operators -/

namespace AFT.SafeConvolution

open scoped BigOperators

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- Both true signed marginals vanish. -/
def PairCanonical (profile : G × G → ℝ) : Prop :=
  (∀ first, ∑ second, profile (first, second) = 0) ∧
  (∀ second, ∑ first, profile (first, second) = 0)

theorem convolution_pairCanonical (kernel profile : G × G → ℝ) (h : PairCanonical profile) :
    PairCanonical (convolution kernel profile) := by
  constructor
  · intro first
    simp only [convolution_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro shift _
    rw [← Finset.mul_sum]
    change kernel shift * (∑ second, profile (first - shift.1, second - shift.2)) = 0
    rw [translated_sum (fun second => profile (first - shift.1, second)), h.1, mul_zero]
  · intro second
    simp only [convolution_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro shift _
    rw [← Finset.mul_sum]
    change kernel shift * (∑ first, profile (first - shift.1, second - shift.2)) = 0
    rw [translated_sum (fun first => profile (first, second - shift.2)), h.2, mul_zero]

omit [AddCommGroup G] in
theorem PairCanonical.sub {first second : G × G → ℝ} (ha : PairCanonical first) (hb : PairCanonical second) :
    PairCanonical (first - second) := by
  constructor
  · intro color; simp only [Pi.sub_apply, Finset.sum_sub_distrib, ha.1, hb.1, sub_self]
  · intro color; simp only [Pi.sub_apply, Finset.sum_sub_distrib, ha.2, hb.2, sub_self]







end AFT.SafeConvolution

end

section










/-! # Exact Hilbert contraction of the real core-supported canonical seed -/

namespace AFT.SafePair

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def centerOnCore (core : Finset ι) (profile : ι → ℝ) (color : ι) : ℝ :=
  profile color - uniformFiniteProfile core color * ∑ x, profile x



/-- Core centering is the genuine orthogonal projection in counting L2,
including its exact energy decrement. -/
theorem centerOnCore_square (core : Finset ι) (profile : ι → ℝ) (hne : core.Nonempty)
    (hsupport : ∀ color, color ∉ core → profile color = 0) :
    (∑ color, centerOnCore core profile color ^ 2) =
      (∑ color, profile color ^ 2) - (∑ color, profile color) ^ 2 / core.card := by
  have hcross (color : ι) : profile color * uniformFiniteProfile core color = profile color / core.card := by
    by_cases hc : color ∈ core <;> simp [uniformFiniteProfile, hc, hsupport, div_eq_mul_inv]
  have hrefsquare (color : ι) : uniformFiniteProfile core color ^ 2 = uniformFiniteProfile core color / core.card := by
    by_cases hc : color ∈ core <;> simp [uniformFiniteProfile, hc]
    ring
  unfold centerOnCore
  simp only [sub_sq, mul_pow, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hmiddle : (∑ color, 2 * profile color * (uniformFiniteProfile core color * ∑ x, profile x)) =
      2 * (∑ x, profile x) * ((∑ color, profile color) / core.card) := by
    simp_rw [show ∀ color, 2 * profile color * (uniformFiniteProfile core color * ∑ x, profile x) =
      (2 * ∑ x, profile x) * (profile color * uniformFiniteProfile core color) by intro; ring]
    rw [← Finset.mul_sum]
    simp only [hcross, ← Finset.sum_div]
  rw [hmiddle]
  simp only [hrefsquare, ← Finset.sum_mul, ← Finset.sum_div, uniformFiniteProfile_mass core hne]
  ring

theorem centerOnCore_square_le (core : Finset ι) (profile : ι → ℝ) (hne : core.Nonempty)
    (hsupport : ∀ color, color ∉ core → profile color = 0) :
    (∑ color, centerOnCore core profile color ^ 2) ≤ ∑ color, profile color ^ 2 := by
  rw [centerOnCore_square core profile hne hsupport]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))

theorem coreSeed_eq_centers (core : Finset ι) (mass : ι → ι → ℝ) (first second : ι) :
    coreSeed core mass first second =
      centerOnCore core (fun x => centerOnCore core (restrictPair core mass x) second) first := by
  simp only [coreSeed, canonicalPair, centerOnCore, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Finset.sum_comm (f := fun x y => restrictPair core mass x y)]
  ring

/-- Restricting the true pair and canonicalizing on its core loses no
counting-L2 energy. No independent-product approximation is introduced. -/
theorem coreSeed_square_le (core : Finset ι) (mass : ι → ι → ℝ) (hne : core.Nonempty) :
    (∑ first, ∑ second, coreSeed core mass first second ^ 2) ≤ ∑ first, ∑ second, mass first second ^ 2 := by
  have hcolumn (second : ι) :
      (∑ first, coreSeed core mass first second ^ 2) ≤
        ∑ first, centerOnCore core (restrictPair core mass first) second ^ 2 := by
    simp_rw [coreSeed_eq_centers]
    apply centerOnCore_square_le core _ hne
    intro color hout
    simp [centerOnCore, restrictPair, hout]
  calc
    _ = ∑ second, ∑ first, coreSeed core mass first second ^ 2 := Finset.sum_comm
    _ ≤ ∑ second, ∑ first, centerOnCore core (restrictPair core mass first) second ^ 2 :=
      Finset.sum_le_sum fun second _ => hcolumn second
    _ = ∑ first, ∑ second, centerOnCore core (restrictPair core mass first) second ^ 2 := Finset.sum_comm
    _ ≤ ∑ first, ∑ second, restrictPair core mass first second ^ 2 := by
      apply Finset.sum_le_sum
      intro first _
      exact centerOnCore_square_le core _ hne (by intro color hout; simp [restrictPair, hout])
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro first _
      apply Finset.sum_le_sum
      intro second _
      unfold restrictPair
      split_ifs <;> simp [sq_nonneg]

end AFT.SafePair

end

section








/-! # Exact cost of changing the canonical core reference to the full palette -/

namespace AFT.SafePair

open scoped BigOperators
open SafeConvolution

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def pairCountingL2 (mass : ι → ι → ℝ) : ℝ := countingL2 (fun color : ι × ι => mass color.1 color.2)

omit [DecidableEq ι] in
theorem pairCountingL2_add (first second : ι → ι → ℝ) :
    pairCountingL2 (first + second) ≤ pairCountingL2 first + pairCountingL2 second :=
  countingL2_add _ _

omit [DecidableEq ι] in
theorem pairCountingL2_neg (mass : ι → ι → ℝ) : pairCountingL2 (-mass) = pairCountingL2 mass := countingL2_neg _

omit [DecidableEq ι] in
theorem pairCountingL2_tensor (first second : ι → ℝ) :
    pairCountingL2 (fun x y => first x * second y) = countingL2 first * countingL2 second := by
  unfold pairCountingL2 countingL2
  rw [Fintype.sum_prod_type]
  simp only [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [Real.sqrt_mul (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]

theorem uniformFiniteProfile_square (core : Finset ι) (hne : core.Nonempty) :
    (∑ color, uniformFiniteProfile core color ^ 2) = 1 / (core.card : ℝ) := by
  have hp (color : ι) : uniformFiniteProfile core color ^ 2 = uniformFiniteProfile core color / core.card := by
    by_cases hc : color ∈ core <;> simp [uniformFiniteProfile, hc]
    ring
  simp only [hp, ← Finset.sum_div, uniformFiniteProfile_mass core hne]

/-- The full exact distance between the two actual uniform reference laws. -/
theorem uniformCore_difference_square (core : Finset ι) (hne : core.Nonempty) :
    (∑ color, (uniformFiniteProfile core color - 1 / (Fintype.card ι : ℝ)) ^ 2) =
      1 / (core.card : ℝ) - 1 / (Fintype.card ι : ℝ) := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    have hh : 0 < Fintype.card ι := lt_of_lt_of_le (Finset.card_pos.mpr hne) (Finset.card_le_univ core)
    positivity
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [uniformFiniteProfile_square core hne]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, uniformFiniteProfile_mass core hne, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

omit [DecidableEq ι] in
/-- A bounded nonnegative subprobability marginal has counting energy at
most its actual height. -/
theorem nonnegative_countingL2_le (profile : ι → ℝ) (upper : ℝ) (hu : 0 ≤ upper)
    (hp : ∀ color, 0 ≤ profile color) (hb : ∀ color, profile color ≤ upper)
    (hmass : (∑ color, profile color) ≤ 1) : countingL2 profile ≤ Real.sqrt upper := by
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ ∑ color, upper * profile color := Finset.sum_le_sum fun color _ => by
      nlinarith [mul_le_mul_of_nonneg_right (hb color) (hp color)]
    _ = upper * ∑ color, profile color := by rw [Finset.mul_sum]
    _ ≤ upper := by nlinarith

omit [DecidableEq ι] in
/-- Changing the centering law is a sum of two explicit rank-one profiles,
which keeps the reference-change error separate from the pair edge loss. -/
theorem canonicalPair_reference_difference (firstReference secondReference : ι → ℝ)
    (mass : ι → ι → ℝ) (first second : ι) :
    canonicalPair firstReference mass first second - canonicalPair secondReference mass first second =
      -((firstReference first - secondReference first) *
        ((∑ x, mass x second) - (∑ x, ∑ y, mass x y) * firstReference second)) -
      (((∑ y, mass first y) - (∑ x, ∑ y, mass x y) * secondReference first) *
        (firstReference second - secondReference second)) := by
  unfold canonicalPair
  ring

omit [DecidableEq ι] in
/-- The reference change has a palette-independent Hilbert estimate in
terms of actual marginal heights, total mass, and the two reference laws. -/
theorem canonicalPair_reference_L2_le (firstReference secondReference : ι → ℝ)
    (mass : ι → ι → ℝ) (upper : ℝ) (hu : 0 ≤ upper)
    (hmass : ∀ first second, 0 ≤ mass first second)
    (htotal : (∑ first, ∑ second, mass first second) ≤ 1)
    (hrow : ∀ first, (∑ second, mass first second) ≤ upper)
    (hcolumn : ∀ second, (∑ first, mass first second) ≤ upper) :
    pairCountingL2 (canonicalPair firstReference mass - canonicalPair secondReference mass) ≤
      countingL2 (firstReference - secondReference) *
        (2 * Real.sqrt upper + countingL2 firstReference + countingL2 secondReference) := by
  let total := ∑ first, ∑ second, mass first second
  let row := fun first => ∑ second, mass first second
  let column := fun second => ∑ first, mass first second
  have ht0 : 0 ≤ total := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hmass _ _
  have hr := nonnegative_countingL2_le row upper hu
    (fun _ => Finset.sum_nonneg fun _ _ => hmass _ _) hrow htotal
  have hc := nonnegative_countingL2_le column upper hu
    (fun _ => Finset.sum_nonneg fun _ _ => hmass _ _) hcolumn (by dsimp only [column]; rw [Finset.sum_comm]; exact htotal)
  have hcenter (marginal reference : ι → ℝ) (hm : countingL2 marginal ≤ Real.sqrt upper) :
      countingL2 (marginal - total • reference) ≤ Real.sqrt upper + countingL2 reference := by
    change countingL2 (marginal + -(total • reference)) ≤ _
    have hh := countingL2_add marginal (-(total • reference))
    rw [countingL2_neg, countingL2_smul, abs_of_nonneg ht0] at hh
    have hm' := mul_le_mul_of_nonneg_right htotal (countingL2_nonneg reference)
    exact hh.trans (by dsimp only [total] at *; nlinarith)
  have hfirst := hcenter column firstReference hc
  have hsecond := hcenter row secondReference hr
  have heq : canonicalPair firstReference mass - canonicalPair secondReference mass =
      -(fun x y => (firstReference - secondReference) x * (column - total • firstReference) y) +
      -(fun x y => (row - total • secondReference) x * (firstReference - secondReference) y) := by
    funext first second
    exact canonicalPair_reference_difference firstReference secondReference mass first second
  rw [heq]
  calc
    _ ≤ pairCountingL2 (-(fun x y => (firstReference - secondReference) x * (column - total • firstReference) y)) +
      pairCountingL2 (-(fun x y => (row - total • secondReference) x * (firstReference - secondReference) y)) := pairCountingL2_add _ _
    _ = countingL2 (firstReference - secondReference) * countingL2 (column - total • firstReference) +
      countingL2 (row - total • secondReference) * countingL2 (firstReference - secondReference) := by
      rw [pairCountingL2_neg, pairCountingL2_neg, pairCountingL2_tensor, pairCountingL2_tensor]
    _ ≤ countingL2 (firstReference - secondReference) * (Real.sqrt upper + countingL2 firstReference) +
      (Real.sqrt upper + countingL2 secondReference) * countingL2 (firstReference - secondReference) :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst (countingL2_nonneg _))
        (mul_le_mul_of_nonneg_right hsecond (countingL2_nonneg _))
    _ = _ := by ring

end AFT.SafePair

end

section





/-! # Squared Hilbert error of averaging genuine finite translations -/

namespace AFT.SafeConvolution

open scoped BigOperators

variable {G : Type*} [Fintype G] [AddCommGroup G]





omit [AddCommGroup G] in
/-- Full finite mixtures of joint profiles obey the same squared bound;
no rank-one decomposition of their output coordinates is used. -/
theorem probability_profile_mixture_square_le {σ : Type*} [Fintype σ]
    (source : FiniteDist σ) (profiles : σ → G → ℝ) :
    (∑ color, (∑ sample, source.weight sample * profiles sample color) ^ 2) ≤
      ∑ sample, source.weight sample * ∑ color, profiles sample color ^ 2 := by
  have hpoint (color : G) : (∑ sample, source.weight sample * profiles sample color) ^ 2 ≤
      ∑ sample, source.weight sample * profiles sample color ^ 2 := by
    have hh : (∑ sample, source.weight sample * profiles sample color) ^ 2 ≤
        (∑ sample, source.weight sample) * ∑ sample, source.weight sample * profiles sample color ^ 2 := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
      · intro sample _; exact source.nonneg _
      · intro sample _; exact mul_nonneg (source.nonneg _) (sq_nonneg _)
      · intro sample _; ring
    simpa only [source.sum_one, one_mul] using hh
  calc
    _ ≤ ∑ color, ∑ sample, source.weight sample * profiles sample color ^ 2 :=
      Finset.sum_le_sum fun color _ => hpoint color
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]

omit [AddCommGroup G] in
theorem probability_profile_mixture_square_le_uniform {σ : Type*} [Fintype σ]
    (source : FiniteDist σ) (profiles : σ → G → ℝ) (bound : ℝ)
    (hbound : ∀ sample, (∑ color, profiles sample color ^ 2) ≤ bound) :
    (∑ color, (∑ sample, source.weight sample * profiles sample color) ^ 2) ≤ bound := by
  exact (probability_profile_mixture_square_le source profiles).trans (by
    calc
      _ ≤ ∑ sample, source.weight sample * bound :=
        Finset.sum_le_sum fun sample _ => mul_le_mul_of_nonneg_left (hbound sample) (source.nonneg sample)
      _ = _ := by rw [← Finset.sum_mul, source.sum_one, one_mul])



/-- Repeated actual probability smoothing costs only the fixed number of
steps times the proved one-step error. -/
theorem probability_power_error_L2_le (source : FiniteDist G) (profile : G → ℝ) (order : ℕ) :
    countingL2 ((convolution source.weight ^ order) profile - profile) ≤
      order * countingL2 (convolution source.weight profile - profile) := by
  induction order with
  | zero => simp [countingL2]
  | succ order ih =>
    rw [pow_succ', Module.End.mul_apply]
    have heq : convolution source.weight ((convolution source.weight ^ order) profile) - profile =
        convolution source.weight ((convolution source.weight ^ order) profile - profile) +
          (convolution source.weight profile - profile) := by
      rw [map_sub]
      abel
    rw [heq]
    exact (countingL2_add _ _).trans ((add_le_add
      ((probability_convolution_L2_le source _).trans ih) le_rfl).trans_eq (by push_cast; ring))

end AFT.SafeConvolution

end

section










/-! # Uniform canonical projection commutes with actual finite smoothing -/

namespace AFT.SafeConvolution

open scoped BigOperators

variable {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]

noncomputable def uniformCanonical : Module.End ℝ (G × G → ℝ) where
  toFun profile color := SafePair.canonicalPair (fun _ : G => 1 / (Fintype.card G : ℝ))
    (fun x y => profile (x, y)) color.1 color.2
  map_add' first second := by
    funext color
    simp only [SafePair.canonicalPair, Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' scalar profile := by
    funext color
    simp only [SafePair.canonicalPair, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

omit [AddCommGroup G] [DecidableEq G] in
@[simp] theorem uniformCanonical_apply (profile : G × G → ℝ) (color : G × G) :
    uniformCanonical profile color = SafePair.canonicalPair (fun _ : G => 1 / (Fintype.card G : ℝ))
      (fun x y => profile (x, y)) color.1 color.2 := rfl

omit [DecidableEq G] in
theorem uniformCanonical_translation (profile : G × G → ℝ) (shift : G × G) :
    uniformCanonical (fun color => profile (color - shift)) = fun color => uniformCanonical profile (color - shift) := by
  funext color
  simp only [uniformCanonical_apply, SafePair.canonicalPair]
  have hfirst (second : G) : (∑ first, profile (first - shift.1, second - shift.2)) =
      ∑ first, profile (first, second - shift.2) := translated_sum (fun first => profile (first, second - shift.2)) shift.1
  have hsecond (first : G) : (∑ second, profile (first - shift.1, second - shift.2)) =
      ∑ second, profile (first - shift.1, second) := translated_sum (fun second => profile (first - shift.1, second)) shift.2
  have htotal : (∑ first, ∑ second, profile (first - shift.1, second - shift.2)) =
      ∑ first, ∑ second, profile (first, second) := by
    simp_rw [hsecond]
    exact translated_sum (fun first => ∑ second, profile (first, second)) shift.1
  change profile (color.1 - shift.1, color.2 - shift.2) - 1 / (Fintype.card G : ℝ) *
    (∑ x, profile (x - shift.1, color.2 - shift.2)) -
    (∑ x, profile (color.1 - shift.1, x - shift.2)) * (1 / (Fintype.card G : ℝ)) +
    (∑ x, ∑ y, profile (x - shift.1, y - shift.2)) * (1 / (Fintype.card G : ℝ)) * (1 / (Fintype.card G : ℝ)) = _
  rw [hfirst, hsecond, htotal]
  rfl

omit [DecidableEq G] in
theorem uniformCanonical_commute (kernel : G × G → ℝ) : Commute uniformCanonical (convolution kernel) := by
  apply LinearMap.ext
  intro profile
  funext color
  have hrepr : convolution kernel profile = ∑ shift, kernel shift • (fun point => profile (point - shift)) := by
    funext point
    simp only [convolution_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change uniformCanonical (convolution kernel profile) color = convolution kernel (uniformCanonical profile) color
  rw [hrepr, map_sum]
  simp only [map_smul, uniformCanonical_translation, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, convolution_apply]

/-- Uniform canonicalization is the exact counting-Hilbert orthogonal
projection, including for a signed non-product joint profile. -/
theorem uniformCanonical_L2_le (profile : G × G → ℝ) :
    countingL2 (uniformCanonical profile) ≤ countingL2 profile := by
  have hh := SafePair.coreSeed_square_le (Finset.univ : Finset G) (fun x y => profile (x, y)) Finset.univ_nonempty
  simp only [SafePair.coreSeed, SafePair.canonicalPair, SafePair.restrictPair, uniformFiniteProfile, Finset.mem_univ, and_self,
    if_true, Finset.card_univ] at hh
  apply Real.sqrt_le_sqrt
  simpa only [Fintype.sum_prod_type, uniformCanonical_apply, SafePair.canonicalPair, one_div] using hh

/-- The actual smoothed core seed differs from the desired canonical pair
by exactly the core-centering error, the retained smoothing error, and the
deleted edge error. Each is measured before any parameter simplification. -/
theorem smoothed_core_error_L2_le (source : FiniteDist (G × G)) (core : Finset G)
    (mass : G → G → ℝ) (order : ℕ) :
    let original := fun color : G × G => mass color.1 color.2
    let restricted := fun color : G × G => SafePair.restrictPair core mass color.1 color.2
    let seed := fun color : G × G => SafePair.coreSeed core mass color.1 color.2
    countingL2 ((convolution source.weight ^ order) seed - uniformCanonical original) ≤
      countingL2 (seed - uniformCanonical restricted) +
      order * countingL2 (convolution source.weight restricted - restricted) +
      countingL2 (restricted - original) := by
  dsimp only
  let original := fun color : G × G => mass color.1 color.2
  let restricted := fun color : G × G => SafePair.restrictPair core mass color.1 color.2
  let seed := fun color : G × G => SafePair.coreSeed core mass color.1 color.2
  have hc := (uniformCanonical_commute source.weight).pow_right order
  have hcomm : (convolution source.weight ^ order) (uniformCanonical restricted) =
      uniformCanonical ((convolution source.weight ^ order) restricted) := by
    have hh := congrArg (fun operator : Module.End ℝ (G × G → ℝ) => operator restricted) hc.eq
    simpa only [Module.End.mul_apply] using hh.symm
  have heq : (convolution source.weight ^ order) seed - uniformCanonical original =
      (convolution source.weight ^ order) (seed - uniformCanonical restricted) +
      uniformCanonical ((convolution source.weight ^ order) restricted - restricted) +
      uniformCanonical (restricted - original) := by
    simp only [map_sub]
    rw [hcomm]
    abel
  change countingL2 ((convolution source.weight ^ order) seed - uniformCanonical original) ≤ _
  rw [heq]
  exact (countingL2_add _ _).trans ((add_le_add
    ((countingL2_add _ _).trans (add_le_add (probability_power_L2_le source order _)
      ((uniformCanonical_L2_le _).trans (probability_power_error_L2_le source restricted order))))
    (uniformCanonical_L2_le _)))

end AFT.SafeConvolution

end

section










/-! # Identification of the actual restricted pair with its integer core kernel -/

namespace AFT.TrimmedSlice

open scoped BigOperators

/-- The core mask is the original integer palette interval, not a cyclic
window or a replacement endpoint law. -/
theorem core_interval_mem (modulus coreDepth : ℕ) (hcore : 2 * coreDepth ≤ modulus) (color : ℤ) :
    color ∈ anchorInterval coreDepth (modulus - 2 * coreDepth) ↔
      (coreDepth : ℤ) ≤ color ∧ color < (modulus : ℤ) - coreDepth := by
  simp only [anchorInterval, Finset.mem_Ico]
  omega

theorem core_palette_mem (modulus coreDepth : ℕ) (color : Fin modulus) :
    color ∈ paletteSlice modulus coreDepth 0 ↔
      (coreDepth : ℤ) ≤ color.val ∧ (color.val : ℤ) < (modulus : ℤ) - coreDepth := by
  simp only [paletteSlice, Finset.mem_filter, Finset.mem_univ, true_and, slice,
    max_self, min_self, add_zero, Finset.mem_Ico]

/-- Exact equality between the actual core-restricted window pair and the
integer kernel to which the complete translation bound applies. -/
theorem restricted_averagedPair_eq_maskedIntegerPair (modulus coreDepth : ℕ)
    (boundary start source shiftBound cutoff : ℤ) (width : ℕ) (lower : ℝ) (hlower : 0 < lower)
    (hcore : 2 * coreDepth ≤ modulus) (hboundary : boundary ≤ coreDepth)
    (hstarts : ∀ shift ∈ anchorInterval start width, |shift| ≤ shiftBound) (hsource : |source| ≤ cutoff)
    (hclear : lower ≤ (modulus : ℝ) - 2 * boundary - shiftBound - cutoff)
    (first second : Fin modulus) :
    SafePair.restrictPair (paletteSlice modulus coreDepth 0) (averagedPair modulus boundary start source width) first second =
      maskedIntegerPair modulus boundary lower start source width coreDepth (modulus - 2 * coreDepth) first.val second.val := by
  have hfloor : ⌊(modulus : ℝ) - 1⌋ = (modulus : ℤ) - 1 := by
    have heq : (modulus : ℝ) - 1 = ((modulus : ℤ) - 1 : ℤ) := by push_cast; rfl
    rw [heq, Int.floor_intCast]
  unfold SafePair.restrictPair maskedIntegerPair
  simp only [core_palette_mem, core_interval_mem modulus coreDepth hcore, hfloor]
  split_ifs with hc
  · rw [averagedPair_eq_weightedIntegerWindow modulus boundary start source shiftBound cutoff width lower hlower
      hstarts hsource hclear]
    have hmask : boundary ≤ (first.val : ℤ) ∧ (first.val : ℤ) ≤ (modulus : ℤ) - 1 - boundary ∧
        boundary ≤ (second.val : ℤ) ∧ (second.val : ℤ) ≤ (modulus : ℤ) - 1 - boundary := by omega
    rw [if_pos hmask]
  · rfl

end AFT.TrimmedSlice

end

section







/-!
# The full mixed input activity on actual finite kernels

The coordinate rates are `pool⁻¹/²`; allowing a rate for each coordinate
covers both primary and body pools.  Every fixed-coordinate set is included.
The norm is taken on input kernels themselves, without identifying equal
images under an output evaluation map.
-/

namespace AFT.MixedKernel

open scoped BigOperators Classical

noncomputable section

variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

def freeze (fixed : Finset Slot) (values integrated : Slot → Color) : Slot → Color :=
  fun slot => if slot ∈ fixed then values slot else integrated slot

def fiberSq (reference : Slot → FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (fixed : Finset Slot) (values : Slot → Color) : ℝ :=
  (FiniteDist.independent reference).l2Sq fun integrated => kernel (freeze fixed values integrated)

def fiberNorm (reference : Slot → FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (fixed : Finset Slot) : ℝ :=
  ‖fun values => Real.sqrt (fiberSq reference kernel fixed values)‖

def activity (rate : Slot → ℝ) (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) : ℝ :=
  (∏ slot, rate slot) * ∑ fixed : Finset Slot, (∏ slot ∈ fixed, rate slot) *
    fiberNorm reference kernel fixed









@[simp] theorem fiberNorm_zero (reference : Slot → FiniteDist Color) (fixed : Finset Slot) :
    fiberNorm reference (0 : (Slot → Color) → ℝ) fixed = 0 := by
  simp [fiberNorm, fiberSq, FiniteDist.l2Sq, FiniteDist.expectation]
  rfl





@[simp] theorem activity_zero (rate : Slot → ℝ) (reference : Slot → FiniteDist Color) :
    activity rate reference (0 : (Slot → Color) → ℝ) = 0 := by simp [activity]









end

end AFT.MixedKernel

namespace AFT.MixedKernel

open scoped BigOperators Classical

noncomputable section

variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

@[simp] theorem fiberSq_univ (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (values : Slot → Color) :
    fiberSq reference kernel Finset.univ values = kernel values ^ 2 := by
  have hf (integrated : Slot → Color) : freeze Finset.univ values integrated = values := by
    ext slot
    simp [freeze]
  simp only [fiberSq, FiniteDist.l2Sq, FiniteDist.expectation, hf, ← Finset.sum_mul,
    FiniteDist.sum_one, one_mul]

@[simp] theorem fiberNorm_univ (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) :
    fiberNorm reference kernel Finset.univ = ‖kernel‖ := by
  simp only [fiberNorm, fiberSq_univ, Real.sqrt_sq_eq_abs]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg kernel)).mpr
    intro values
    rw [Real.norm_eq_abs, abs_abs]
    exact norm_le_pi_norm kernel values
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro values
    have h := norm_le_pi_norm (fun values => |kernel values|) values
    simpa only [Real.norm_eq_abs, abs_abs] using h





/-- The empty fixed set is the full integrated L2 fiber. -/
@[simp] theorem fiberSq_empty (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (values : Slot → Color) :
    fiberSq reference kernel ∅ values = (FiniteDist.independent reference).l2Sq kernel := by
  have hf (integrated : Slot → Color) : freeze ∅ values integrated = integrated := by
    ext slot
    simp [freeze]
  simp only [fiberSq, hf]

@[simp] theorem fiberNorm_empty (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) :
    fiberNorm reference kernel ∅ = Real.sqrt ((FiniteDist.independent reference).l2Sq kernel) := by
  haveI : Nonempty (Slot → Color) := by
    by_contra hn
    haveI : IsEmpty (Slot → Color) := not_nonempty_iff.mp hn
    have h := (FiniteDist.independent reference).sum_one
    simp at h
  simp only [fiberNorm, fiberSq_empty, pi_norm_const, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]



end

end AFT.MixedKernel

end

section





/-! # A genuine coordinate operator on every mixed input fiber

The operator acts on the literal joint kernel. Grouping fixed-coordinate
sets in pairs gives a dimension-free bound on the full mixed activity.
-/

namespace AFT.MixedKernel

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {Slot Color : Type*} [Fintype Slot] [Fintype Color] [DecidableEq Slot]

/-- Apply a profile operator in one actual input coordinate. -/
def partialInputOperator (slot : Slot) (operator : Module.End ℝ (Color → ℝ))
    (primary : Color → ℝ) (kernel : (Slot → Color) → ℝ) : (Slot → Color) → ℝ :=
  fun word => operator (fun input => primary input * kernel (Function.update word slot input))
    (word slot) / primary (word slot)



























end
end AFT.MixedKernel

end

section





/-! # Literal coordinate composition and finite tensor inverse iteration -/

namespace AFT.MixedKernel

open scoped BigOperators Classical

noncomputable section

variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

/-- The actual coordinate operation is linear on the complete joint kernel. -/
def partialInputLinear (slot : Slot) (operator : Module.End ℝ (Color → ℝ))
    (primary : Color → ℝ) : Module.End ℝ ((Slot → Color) → ℝ) where
  toFun := partialInputOperator slot operator primary
  map_add' first second := by
    funext word
    unfold partialInputOperator
    have heq : (fun input => primary input * (first + second) (Function.update word slot input)) =
        (fun input => primary input * first (Function.update word slot input)) +
        (fun input => primary input * second (Function.update word slot input)) := by funext input; simp [mul_add]
    rw [heq, map_add]
    simp only [Pi.add_apply, add_div]
  map_smul' scalar kernel := by
    funext word
    unfold partialInputOperator
    have heq : (fun input => primary input * (scalar • kernel) (Function.update word slot input)) =
        scalar • (fun input => primary input * kernel (Function.update word slot input)) := by funext input; simp [mul_left_comm]
    rw [heq, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, mul_div_assoc, RingHom.id_apply]

omit [Fintype Slot] [Fintype Color] in
@[simp] theorem partialInputOperator_id (slot : Slot) (primary : Color → ℝ)
    (hprimary : ∀ color, primary color ≠ 0) (kernel : (Slot → Color) → ℝ) :
    partialInputOperator slot LinearMap.id primary kernel = kernel := by
  funext word
  simp only [partialInputOperator, LinearMap.id_apply, Function.update_eq_self]
  exact mul_div_cancel_left₀ _ (hprimary _)





/-- A specified ordered finite list retains all coordinate actions literally. -/
def inputIteration (coordinates : List Slot) (operator : Slot → Module.End ℝ (Color → ℝ))
    (reference : Slot → FiniteDist Color) : Module.End ℝ ((Slot → Color) → ℝ) :=
  coordinates.foldr (fun slot accumulated => (partialInputLinear slot (operator slot) (reference slot).weight).comp accumulated)
    LinearMap.id

omit [Fintype Slot] in
@[simp] theorem inputIteration_nil (operator : Slot → Module.End ℝ (Color → ℝ))
    (reference : Slot → FiniteDist Color) : inputIteration [] operator reference = LinearMap.id := rfl

omit [Fintype Slot] in
@[simp] theorem inputIteration_cons (slot : Slot) (coordinates : List Slot)
    (operator : Slot → Module.End ℝ (Color → ℝ)) (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) :
    inputIteration (slot :: coordinates) operator reference kernel =
      partialInputOperator slot (operator slot) (reference slot).weight
        (inputIteration coordinates operator reference kernel) := rfl



end
end AFT.MixedKernel

end

section





/-! # Tensor multiplication of the full mixed input activity -/

set_option backward.isDefEq.respectTransparency false

namespace AFT.MixedKernel

open scoped BigOperators Classical

noncomputable section

variable {Left Right Color : Type*} [Fintype Left] [Fintype Right] [Fintype Color]
  [DecidableEq Left] [DecidableEq Right]



omit [Fintype Left] [Fintype Right] [Fintype Color] in
@[simp] theorem freeze_disjSum_left (first : Finset Left) (second : Finset Right)
    (values integrated : Left ⊕ Right → Color) :
    freeze (first.disjSum second) values integrated ∘ Sum.inl =
      freeze first (values ∘ Sum.inl) (integrated ∘ Sum.inl) := by
  ext slot
  simp [freeze]

omit [Fintype Left] [Fintype Right] [Fintype Color] in
@[simp] theorem freeze_disjSum_right (first : Finset Left) (second : Finset Right)
    (values integrated : Left ⊕ Right → Color) :
    freeze (first.disjSum second) values integrated ∘ Sum.inr =
      freeze second (values ∘ Sum.inr) (integrated ∘ Sum.inr) := by
  ext slot
  simp [freeze]







end

end AFT.MixedKernel

end

section







/-! # Finite Neumann smoothing instantiated at the actual V7 root parameters -/

namespace AFT.GaussianSource

open scoped BigOperators Classical
open AFT.SafeConvolution

noncomputable section

local instance actualModulusNeZero (parameter : ℕ) : NeZero (Parameters.modulus parameter) :=
  ⟨(Parameters.modulus_prime parameter).ne_zero⟩

 















end
end AFT.GaussianSource

end

section











namespace AFT
end AFT
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox




/-! # Complete error of the actual finite safe pair input -/

namespace AFT.SafePair

open scoped BigOperators
open SafeConvolution

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem coreSeed_reference_error_le (core : Finset ι) (hne : core.Nonempty)
    (mass : ι → ι → ℝ) (upper : ℝ) (hu : 0 ≤ upper)
    (hmass : ∀ first second, 0 ≤ mass first second)
    (htotal : (∑ first, ∑ second, mass first second) ≤ 1)
    (hrow : ∀ first, (∑ second, mass first second) ≤ upper)
    (hcolumn : ∀ second, (∑ first, mass first second) ≤ upper) :
    pairCountingL2 (coreSeed core mass - canonicalPair (fun _ => 1 / (Fintype.card ι : ℝ))
      (restrictPair core mass)) ≤
      Real.sqrt (1 / (core.card : ℝ) - 1 / (Fintype.card ι : ℝ)) *
        (2 * Real.sqrt upper + Real.sqrt (1 / (core.card : ℝ)) +
          Real.sqrt (1 / (Fintype.card ι : ℝ))) := by
  have hnonneg (first second : ι) : 0 ≤ restrictPair core mass first second := by
    unfold restrictPair; split_ifs
    · exact hmass first second
    · exact le_rfl
  have hle (first second : ι) : restrictPair core mass first second ≤ mass first second := by
    unfold restrictPair; split_ifs <;> simp_all
  have hh := canonicalPair_reference_L2_le (uniformFiniteProfile core)
    (fun _ => 1 / (Fintype.card ι : ℝ)) (restrictPair core mass) upper hu hnonneg
    ((Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hle x y).trans htotal)
    (fun x => (Finset.sum_le_sum fun y _ => hle x y).trans (hrow x))
    (fun y => (Finset.sum_le_sum fun x _ => hle x y).trans (hcolumn y))
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    have hp := (Finset.card_pos.mpr hne).trans_le (Finset.card_le_univ core)
    positivity
  have hfull : countingL2 (fun _ : ι => 1 / (Fintype.card ι : ℝ)) =
      Real.sqrt (1 / (Fintype.card ι : ℝ)) := by
    unfold countingL2
    congr 1
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hcore : countingL2 (uniformFiniteProfile core) = Real.sqrt (1 / (core.card : ℝ)) := by
    unfold countingL2
    rw [uniformFiniteProfile_square core hne]
  have hdiff : countingL2 (uniformFiniteProfile core - fun _ : ι => 1 / (Fintype.card ι : ℝ)) =
      Real.sqrt (1 / (core.card : ℝ) - 1 / (Fintype.card ι : ℝ)) := by
    unfold countingL2
    simp only [Pi.sub_apply, uniformCore_difference_square core hne]
  simpa only [coreSeed, hcore, hfull, hdiff] using hh

end AFT.SafePair

namespace AFT.GaussianSource

open scoped BigOperators Classical
open SafeConvolution

attribute [local instance] actualModulusNeZero



end AFT.GaussianSource

end

section








/-! # Numerical cost of the true core reference and deleted edges -/

namespace AFT.SafePair

open scoped BigOperators

/-- The change from the core uniform law to the full uniform law has
squared normalized cost proportional to the deleted fraction. -/
theorem core_reference_scaled_square_le (modulus size depth : ℝ)
    (hq : 0 < modulus) (hd : 0 ≤ depth) (hk : modulus / 2 ≤ size)
    (hsize : size = modulus - 2 * depth) :
    (modulus * (Real.sqrt (1 / size - 1 / modulus) *
      (2 * Real.sqrt (2 / modulus) + Real.sqrt (1 / size) + Real.sqrt (1 / modulus)))) ^ 2 ≤
      128 * depth / modulus := by
  have hk0 : 0 < size := lt_of_lt_of_le (half_pos hq) hk
  have hdiff : 0 ≤ 1 / size - 1 / modulus := by
    apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le hk0 (by linarith)
  have hsmall : 1 / size ≤ 2 / modulus := by
    apply (div_le_div_iff₀ hk0 hq).mpr
    linarith
  have hone : 1 / modulus ≤ 2 / modulus := by gcongr; norm_num
  have hroot := Real.sqrt_le_sqrt hsmall
  have honeRoot := Real.sqrt_le_sqrt hone
  have hs : 0 ≤ 2 * Real.sqrt (2 / modulus) + Real.sqrt (1 / size) + Real.sqrt (1 / modulus) := by positivity
  have hsum : 2 * Real.sqrt (2 / modulus) + Real.sqrt (1 / size) + Real.sqrt (1 / modulus) ≤
      4 * Real.sqrt (2 / modulus) := by linarith
  have hsum2 := (sq_le_sq₀ hs (by positivity : 0 ≤ 4 * Real.sqrt (2 / modulus))).mpr hsum
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 / modulus)] at hsum2
  have hdiffEq : 1 / size - 1 / modulus = 2 * depth / (size * modulus) := by
    field_simp
    nlinarith
  have hdiffBound : 1 / size - 1 / modulus ≤ 4 * depth / modulus ^ 2 := by
    rw [hdiffEq]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ 2 * depth * modulus)]
  rw [mul_pow, mul_pow, Real.sq_sqrt hdiff]
  calc
    _ ≤ modulus ^ 2 * ((4 * depth / modulus ^ 2) * (16 * (2 / modulus))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg modulus)
      exact mul_le_mul hdiffBound (by norm_num at hsum2 ⊢; exact hsum2) (sq_nonneg _) (by positivity)
    _ = _ := by field_simp; ring

end AFT.SafePair

end

section





/-! # Exact finite collision expansion of canonical U-statistic moments -/

namespace AFT
namespace CanonicalMoments

open scoped BigOperators Classical

variable {Slot Pool Color Copy : Type*}
variable [Fintype Slot] [Fintype Pool] [Fintype Color] [Fintype Copy]

/-- Evaluate a genuine joint kernel at distinct sampled pool indices. -/
noncomputable def placedKernel (kernel : (Slot → Color) → ℝ) (placement : Slot ↪ Pool)
    (word : Pool → Color) : ℝ := kernel (word ∘ placement)



/-- The complete product belonging to one labeled moment collision pattern. -/
noncomputable def patternProduct (kernel : (Slot → Color) → ℝ)
    (pattern : Copy → Slot ↪ Pool) (word : Pool → Color) : ℝ :=
  ∏ copy, placedKernel kernel (pattern copy) word







/-- The pool labels actually used by a moment pattern. -/
noncomputable def usedLabels (pattern : Copy → Slot ↪ Pool) : Finset Pool :=
  Finset.univ.image (fun occurrence : Copy × Slot => pattern occurrence.1 occurrence.2)

/-- A surviving pattern has no sample label occurring in only one kernel. -/
def NoSingleton (pattern : Copy → Slot ↪ Pool) : Prop :=
  ∀ copy slot, ∃ otherCopy otherSlot,
    otherCopy ≠ copy ∧ pattern otherCopy otherSlot = pattern copy slot







end CanonicalMoments
end AFT

end

section





/-!
# Counting actual finite collision patterns

A pattern with exactly `used` labels is encoded by an injective enumeration
of those labels and a word on the occurrence positions.  This retains the
falling-factorial pool factor and has no color-alphabet dependence.
-/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

noncomputable section

variable {Slot Pool Copy : Type*} [Fintype Slot] [Fintype Pool] [Fintype Copy]

abbrev PatternsWithLabels (used : ℕ) :=
  {pattern : Copy → Slot ↪ Pool // (usedLabels pattern).card = used}

def labelEnumeration (used : ℕ) (pattern : PatternsWithLabels (Slot := Slot) (Pool := Pool) (Copy := Copy) used) :
    Fin used ≃ usedLabels pattern.val :=
  Fintype.equivOfCardEq (by simpa only [Fintype.card_fin, Fintype.card_coe] using pattern.property.symm)

def collisionCode (used : ℕ) (pattern : PatternsWithLabels (Slot := Slot) (Pool := Pool) (Copy := Copy) used) :
    (Fin used ↪ Pool) × (Copy × Slot → Fin used) :=
  ((labelEnumeration used pattern).toEmbedding.trans (Function.Embedding.subtype _),
    fun occurrence => (labelEnumeration used pattern).symm
      ⟨pattern.val occurrence.1 occurrence.2,
        Finset.mem_image.mpr ⟨occurrence, Finset.mem_univ _, rfl⟩⟩)

















end

end AFT.CanonicalMoments

end

section





/-! # First, last and middle occurrences in actual finite collision graphs -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

noncomputable section

variable {Copy Label : Type*} [Fintype Copy] [LinearOrder Copy] [Fintype Label]

def occurrenceCopies (scope : Copy → Finset Label) (label : Label) : Finset Copy :=
  Finset.univ.filter fun copy => label ∈ scope copy

def middleScopes (scope : Copy → Finset Label) (copy : Copy) : Finset Label :=
  (scope copy).filter fun label =>
    (∃ before, before < copy ∧ label ∈ scope before) ∧
    (∃ after, copy < after ∧ label ∈ scope after)

def scopeUnion (scope : Copy → Finset Label) : Finset Label :=
  Finset.univ.biUnion scope

def NoSingletonScopes (scope : Copy → Finset Label) : Prop :=
  ∀ copy label, label ∈ scope copy → ∃ other, other ≠ copy ∧ label ∈ scope other













end

end AFT.CanonicalMoments

end

section





/-! # Mixed-fiber Hilbert transfers for canonical moment collision graphs -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

variable {Ending New Fixed Keep : Type*}
variable [Fintype Ending] [Fintype New] [Fintype Fixed] [Fintype Keep]

omit [Fintype New] [Fintype Fixed] [Fintype Keep] in
/-- Weighted Cauchy--Schwarz in an actual finite probability space. -/
theorem expectation_mul_sq_le (law : FiniteDist Ending) (first second : Ending → ℝ) :
    law.expectation (fun value => first value * second value) ^ 2 ≤ law.l2Sq first * law.l2Sq second := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro value _
    exact mul_nonneg (law.nonneg value) (sq_nonneg _)
  · intro value _
    exact mul_nonneg (law.nonneg value) (sq_nonneg _)
  · intro value _
    ring









end AFT.CanonicalMoments

end

section





/-! # Exact coordinate refresh operators on finite product probability laws -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

/-- The actual deterministic finite law. -/
noncomputable def pointLaw (value : Color) : FiniteDist Color where
  weight color := if value = color then 1 else 0
  nonneg color := by split_ifs <;> norm_num
  sum_one := by simp

omit [Fintype Slot] in
@[simp] theorem pointLaw_expectation (value : Color) (function : Color → ℝ) :
    (pointLaw value).expectation function = function value := by
  simp [FiniteDist.expectation, pointLaw]

omit [Fintype Slot] in
@[simp] theorem pointLaw_mix (value : Color) (kernel : Color → FiniteDist Color) :
    (pointLaw value).mix kernel = kernel value := by
  ext color
  simp [FiniteDist.mix_weight, pointLaw]

omit [Fintype Slot] in
@[simp] theorem mix_pointLaw (law : FiniteDist Color) : law.mix pointLaw = law := by
  ext color
  simp [FiniteDist.mix_weight, pointLaw]



/-- Resample precisely the indicated coordinates from their product laws. -/
noncomputable def refreshLaw (reference : Slot → FiniteDist Color) (resampled : Finset Slot)
    (word : Slot → Color) : FiniteDist (Slot → Color) :=
  FiniteDist.independent (fun slot => if slot ∈ resampled then reference slot else pointLaw (word slot))

/-- The concrete partial integration operator. -/
noncomputable def refresh (reference : Slot → FiniteDist Color) (resampled : Finset Slot)
    (function : (Slot → Color) → ℝ) (word : Slot → Color) : ℝ :=
  (refreshLaw reference resampled word).expectation function













omit [Fintype Slot] in
@[simp] theorem map_identity (law : FiniteDist Color) : law.map id = law := by
  ext color
  exact FiniteDist.map_equiv_weight law (Equiv.refl Color) color

omit [Fintype Slot] in
@[simp] theorem map_constant (law : FiniteDist Color) (value : Color) :
    law.map (fun _ => value) = pointLaw value := by
  ext color
  by_cases h : value = color
  · simp [FiniteDist.map_weight, pointLaw, h, law.sum_one]
  · simp [FiniteDist.map_weight, pointLaw, h]









end AFT.CanonicalMoments

end

section




namespace AFT
end AFT
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments


/-! # The exact transfer chain of a finite joint-kernel collision graph -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

variable {Label Color : Type*} [Fintype Label] [Fintype Color]

/-- Coordinate sets that remain active after each actual integration step. -/
noncomputable def graphActive (scope ending : ℕ → Finset Label) : ℕ → Finset Label
  | 0 => ∅
  | index + 1 => (scope index ∪ graphActive scope ending index) \ ending index

/-- Actual partially integrated product of the first kernel copies. -/
noncomputable def graphMessage (reference : Label → FiniteDist Color)
    (ending : ℕ → Finset Label) (kernel : ℕ → (Label → Color) → ℝ) : ℕ → (Label → Color) → ℝ
  | 0 => fun _ => 1
  | index + 1 => refresh reference (ending index)
      (fun word => kernel index word * graphMessage reference ending kernel index word)

/-- Middle occurrences are the coordinates fixed by a graph step. -/
noncomputable def graphFixed (scope ending : ℕ → Finset Label) (index : ℕ) : Finset Label :=
  scope index \ ((scope index \ graphActive scope ending index) ∪ ending index)





/-- The exact unprocessed kernel product. -/
noncomputable def graphSuffix (kernel : ℕ → (Label → Color) → ℝ) (length start : ℕ)
    (word : Label → Color) : ℝ := ∏ index ∈ Finset.Ico start length, kernel index word







end AFT.CanonicalMoments

end

section





/-! # The active and fixed coordinates of the actual ordered collision graph -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

variable {Label : Type*} [Fintype Label] {count : ℕ}

/-- Extend a finite copy sequence by empty scopes. -/
noncomputable def scopeAt (scope : Fin count → Finset Label) (index : ℕ) : Finset Label :=
  if h : index < count then scope ⟨index, h⟩ else ∅

/-- Labels appearing strictly before a position. -/
noncomputable def scopePrefix (scope : Fin count → Finset Label) (index : ℕ) : Finset Label :=
  Finset.univ.filter (fun label => ∃ copy : Fin count, copy.val < index ∧ label ∈ scope copy)

/-- Labels appearing at or after a position. -/
noncomputable def scopeSuffix (scope : Fin count → Finset Label) (index : ℕ) : Finset Label :=
  Finset.univ.filter (fun label => ∃ copy : Fin count, index ≤ copy.val ∧ label ∈ scope copy)

/-- Integrate a label exactly at its last occurrence. -/
noncomputable def scopeEnding (scope : Fin count → Finset Label) (index : ℕ) : Finset Label :=
  scopeAt scope index \ scopeSuffix scope (index + 1)











variable {Color : Type*} [Fintype Color]

/-- Extend an actual finite sequence of kernels by zero. -/
noncomputable def kernelAt (kernel : Fin count → (Label → Color) → ℝ) (index : ℕ) : (Label → Color) → ℝ :=
  if h : index < count then kernel ⟨index, h⟩ else fun _ => 0



end AFT.CanonicalMoments

end

section







/-! # Exact finite histogram normalization of actual symmetric coefficients -/

namespace AFT
namespace HistogramNormalization

open scoped BigOperators Classical

variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

/-- Exchangeability of an actual signed output mass. -/
def ExchangeableMass (mass : (Slot → Color) → ℝ) : Prop :=
  ∀ word (permutation : Equiv.Perm Slot), mass (word ∘ permutation) = mass word

/-- Reindex the complete finite word space by a position permutation. -/
def precomposeEquiv (permutation : Equiv.Perm Slot) : (Slot → Color) ≃ (Slot → Color) where
  toFun word := word ∘ permutation
  invFun word := word ∘ permutation.symm
  left_inv word := by ext slot; simp
  right_inv word := by ext slot; simp



















end HistogramNormalization
end AFT

end

section







namespace AFT
end AFT
namespace AFT.TensorFock
end AFT.TensorFock



/-! # Symmetrization preserves the actual complete coefficient sequence -/

namespace AFT
namespace HistogramNormalization

open scoped BigOperators Classical

variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

/-- The actual signed mass after an independently uniform permutation. -/
noncomputable def symmetrizedMass (mass : (Slot → Color) → ℝ) : (Slot → Color) → ℝ :=
  BlockFock.symmetrize mass

















end HistogramNormalization
end AFT

end

section







/-! # Renaming physical output positions preserves all constructed coefficients -/

namespace AFT
namespace HistogramNormalization

open scoped BigOperators Classical

variable {Slot OtherSlot Color : Type*}
variable [Fintype Slot] [Fintype OtherSlot] [Fintype Color]

/-- Rename the actual finite word's physical position type. -/
def renameWord (equiv : Slot ≃ OtherSlot) : (Slot → Color) ≃ (OtherSlot → Color) where
  toFun word := word ∘ equiv.symm
  invFun word := word ∘ equiv
  left_inv word := by ext slot; simp
  right_inv word := by ext slot; simp

/-- The signed mass of a renamed physical law. -/
noncomputable def renamedMass (equiv : Slot ≃ OtherSlot) (mass : (Slot → Color) → ℝ)
    (word : OtherSlot → Color) : ℝ := mass (word ∘ equiv)







end HistogramNormalization
end AFT

end

section










/-! # Exact finite-pool variance for actual canonical subset statistics -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

variable {Slot Pool Color : Type*} [Fintype Slot] [Fintype Pool] [Fintype Color]









set_option backward.isDefEq.respectTransparency false in
/-- Renaming independent, identically distributed coordinates preserves the
actual finite expectation, including its weights. -/
theorem independent_equiv_expectation (equiv : Slot ≃ Pool) (reference : FiniteDist Color)
    (function : (Slot → Color) → ℝ) :
    (FiniteDist.independent (fun _ : Pool => reference)).expectation
      (fun word => function (word ∘ equiv)) =
      (FiniteDist.independent (fun _ : Slot => reference)).expectation function := by
  have h := (HistogramNormalization.renameWord (Color := Color) equiv).symm.sum_comp
    (fun word => (∏ slot, reference.weight (word slot)) * function word)
  unfold FiniteDist.expectation FiniteDist.independent
  apply Eq.trans ?_ h
  apply Finset.sum_congr (by ext; simp)
  intro word _
  change (∏ slot, reference.weight (word slot)) * function (word ∘ equiv) =
    (∏ slot, reference.weight ((word ∘ equiv) slot)) * function (word ∘ equiv)
  congr 1
  exact (equiv.prod_comp (fun slot => reference.weight (word slot))).symm







end AFT.CanonicalMoments

end

section








/-! # Actual mixed fibers of a distinct-index placement -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

variable {Slot Pool Color : Type*} [Fintype Slot] [Fintype Pool] [Fintype Color]

/-- The actual injective placement identifies its slot set with its image. -/
noncomputable def placementEquiv (placement : Slot ↪ Pool) : Slot ≃ (Finset.univ.map placement) :=
  Equiv.ofBijective (fun slot => ⟨placement slot, Finset.mem_map.mpr ⟨slot, Finset.mem_univ _, rfl⟩⟩) (by
    constructor
    · intro first second heq
      exact placement.injective (congrArg Subtype.val heq)
    · intro label
      obtain ⟨slot, _, heq⟩ := Finset.mem_map.mp label.property
      exact ⟨slot, Subtype.ext heq⟩)

/-- Every finite injective subword has exactly the original independent law. -/
theorem independent_embedding_expectation (reference : FiniteDist Color) (placement : Slot ↪ Pool)
    (function : (Slot → Color) → ℝ) :
    (FiniteDist.independent (fun _ : Pool => reference)).expectation (fun word => function (word ∘ placement)) =
      (FiniteDist.independent (fun _ : Slot => reference)).expectation function := by
  have hr := LocalTensors.independent_restriction_expectation
    (fun _ : Pool => reference) (Finset.univ.map placement)
      (fun word => function (word ∘ placementEquiv placement))
  have he := independent_equiv_expectation (placementEquiv placement) reference function
  apply Eq.trans ?_ (hr.trans ?_)
  · rfl
  · apply Eq.trans ?_ he
    unfold FiniteDist.expectation FiniteDist.independent
    apply Finset.sum_congr (by ext; simp)
    intro word _
    rfl

/-- Pull a set of fixed pool labels back to genuine kernel arguments. -/
noncomputable def placementFixed (placement : Slot ↪ Pool) (fixed : Finset Pool) : Finset Slot :=
  Finset.univ.filter (fun slot => placement slot ∈ fixed)





end AFT.CanonicalMoments

end

section












/-! # Actual arbitrary-joint-kernel collision contractions in mixed activity -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

variable {Slot Pool Color : Type*} [Fintype Slot] [Fintype Pool] [Fintype Color] {power : ℕ}

/-- The exact scope of each actual distinct-index copy. -/
noncomputable def patternScopes (pattern : Fin power → Slot ↪ Pool) : Fin power → Finset Pool :=
  fun copy => Finset.univ.map (pattern copy)

/-- The original kernel arguments fixed at the middle occurrences of a pattern. -/
noncomputable def patternFixed (pattern : Fin power → Slot ↪ Pool) (copy : Fin power) : Finset Slot :=
  placementFixed (pattern copy) (middleScopes (patternScopes pattern) copy)















end AFT.CanonicalMoments

end

section





/-!
# Reflection symmetry of the actual calibrated primary law
-/

namespace AFT

open scoped BigOperators

namespace TrimmedSlice

def reflectedStart (start : ℤ) (width : ℕ) : ℤ := -start - width + 1













end TrimmedSlice

namespace V7Calibration













end V7Calibration
end AFT

end

section





namespace AFT
end AFT
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.QueueNormalization
end AFT.QueueNormalization
namespace AFT.QueueNormalization.average
end AFT.QueueNormalization.average
namespace AFT.QueueNormalization.averageUnit
end AFT.QueueNormalization.averageUnit
namespace AFT.QueueNormalization.finiteExp
end AFT.QueueNormalization.finiteExp
namespace AFT.finiteCorrection
end AFT.finiteCorrection



/-!
# Finite polynomials in specified input seeds

Different seed labels remain different formal variables even when their
leading output tensors agree.  The activity is the coefficient L1 sum
weighted by the product of the actual seed activities.  This is an upper
bound for the fully expanded, symmetrized input representation by
`MixedTensor` and `MixedSymmetry`; no quotient by output tensors is used.
-/

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical

noncomputable section

variable {Seed : Type*}

abbrev Table (Seed : Type*) := MvPolynomial Seed ℝ

def monomialWeight (weight : Seed → ℝ) (powers : Seed →₀ ℕ) : ℝ :=
  powers.prod fun seed power => weight seed ^ power

def activity (weight : Seed → ℝ) (table : Table Seed) : ℝ :=
  (AddMonoidAlgebra.coeff table).sum fun powers coefficient => |coefficient| * monomialWeight weight powers



@[simp] theorem monomialWeight_zero (weight : Seed → ℝ) : monomialWeight weight 0 = 1 := by
  simp [monomialWeight]





@[simp] theorem activity_zero (weight : Seed → ℝ) : activity weight (0 : Table Seed) = 0 := by
  simp [activity, MvPolynomial.sum_def]

@[simp] theorem activity_monomial (weight : Seed → ℝ) (powers : Seed →₀ ℕ) (coefficient : ℝ) :
    activity weight (MvPolynomial.monomial powers coefficient) = |coefficient| * monomialWeight weight powers :=
  MvPolynomial.sum_monomial_eq (by simp)

@[simp] theorem activity_one (weight : Seed → ℝ) : activity weight (1 : Table Seed) = 1 := by
  rw [← MvPolynomial.C_1, MvPolynomial.C_apply, activity_monomial, monomialWeight_zero]
  norm_num







/-- A seed's polynomial variable carries precisely its supplied activity. -/
@[simp] theorem activity_X (weight : Seed → ℝ) (seed : Seed) :
    activity weight (MvPolynomial.X seed : Table Seed) = weight seed := by
  simp [MvPolynomial.X, activity_monomial, monomialWeight, Finsupp.prod_single_index]

end

end AFT.RepresentedPolynomial

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical

noncomputable section

variable {Seed Color : Type*} [Fintype Color]

/-- The literal primary/body input table, before output evaluation. -/
structure InputSeed (Color : Type*) where
  primaryOrder : ℕ
  bodyOrder : ℕ
  kernel : (Fin (primaryOrder + bodyOrder) → Color) → ℝ

def inputReference (primary body : FiniteDist Color) (seed : InputSeed Color) :
    Fin (seed.primaryOrder + seed.bodyOrder) → FiniteDist Color :=
  Fin.addCases (fun _ => primary) (fun _ => body)







omit [Fintype Color] in
@[simp] theorem activity_C (weight : Seed → ℝ) (scalar : ℝ) :
    activity weight (MvPolynomial.C scalar : Table Seed) = |scalar| := by
  rw [MvPolynomial.C_apply, activity_monomial, monomialWeight_zero, mul_one]

omit [Fintype Color] in
@[simp] theorem activity_neg (weight : Seed → ℝ) (table : Table Seed) :
    activity weight (-table) = activity weight table := by
  simp only [activity, MvPolynomial.sum_def, MvPolynomial.support_neg,
    MvPolynomial.coeff_neg, abs_neg]











end

end AFT.RepresentedPolynomial

end

section





/-!
# Weighted truncation of literal input seed polynomials

The cutoff acts on the sum of the primary and body input orders.  Formal
seed labels remain distinct.  Finite Neumann inversion is exact after this
cutoff, with its activity controlled before and after truncation.
-/

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical

noncomputable section

variable {Seed : Type*}

def weightedOrder (order : Seed → ℕ) (powers : Seed →₀ ℕ) : ℕ :=
  powers.sum fun seed power => power * order seed

@[simp] theorem weightedOrder_zero (order : Seed → ℕ) : weightedOrder order 0 = 0 := by
  simp [weightedOrder]

theorem weightedOrder_add (order : Seed → ℕ) (first second : Seed →₀ ℕ) :
    weightedOrder order (first + second) = weightedOrder order first + weightedOrder order second :=
  Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

def truncate (order : Seed → ℕ) (cutoff : ℕ) (table : Table Seed) : Table Seed :=
  AddMonoidAlgebra.ofCoeff (Finsupp.filter (fun powers => weightedOrder order powers ≤ cutoff) (AddMonoidAlgebra.coeff table))

@[simp] theorem coeff_truncate (order : Seed → ℕ) (cutoff : ℕ) (table : Table Seed)
    (powers : Seed →₀ ℕ) :
    MvPolynomial.coeff powers (truncate order cutoff table) =
      if weightedOrder order powers ≤ cutoff then MvPolynomial.coeff powers table else 0 := rfl

@[simp] theorem truncate_zero (order : Seed → ℕ) (cutoff : ℕ) :
    truncate order cutoff (0 : Table Seed) = 0 := by
  ext powers
  simp

@[simp] theorem truncate_one (order : Seed → ℕ) (cutoff : ℕ) :
    truncate order cutoff (1 : Table Seed) = 1 := by
  ext powers
  by_cases h : powers = 0
  · subst powers; simp
  · simp [MvPolynomial.coeff_one, Ne.symm h]

theorem truncate_add (order : Seed → ℕ) (cutoff : ℕ) (first second : Table Seed) :
    truncate order cutoff (first + second) = truncate order cutoff first + truncate order cutoff second := by
  ext powers
  simp only [coeff_truncate, MvPolynomial.coeff_add]
  split_ifs <;> simp





@[simp] theorem truncate_idempotent (order : Seed → ℕ) (cutoff : ℕ) (table : Table Seed) :
    truncate order cutoff (truncate order cutoff table) = truncate order cutoff table := by
  ext powers
  simp only [coeff_truncate]
  split_ifs <;> rfl

theorem truncate_mul (order : Seed → ℕ) (cutoff : ℕ) (first second : Table Seed) :
    truncate order cutoff (first * second) =
      truncate order cutoff (truncate order cutoff first * truncate order cutoff second) := by
  ext powers
  simp only [coeff_truncate]
  split_ifs with h
  · simp only [MvPolynomial.coeff_mul]
    apply Finset.sum_congr rfl
    intro pair hpair
    have heq := Finset.HasAntidiagonal.mem_antidiagonal.mp hpair
    have hsum : weightedOrder order pair.1 + weightedOrder order pair.2 ≤ cutoff := by
      rw [← weightedOrder_add, heq]
      exact h
    rw [coeff_truncate, coeff_truncate, if_pos (by omega), if_pos (by omega)]
  · rfl



/-- Every coefficient strictly below the specified weighted order vanishes. -/
def HasOrder (order : Seed → ℕ) (minimum : ℕ) (table : Table Seed) : Prop :=
  ∀ powers, weightedOrder order powers < minimum → MvPolynomial.coeff powers table = 0

theorem hasOrder_zero (order : Seed → ℕ) (table : Table Seed) : HasOrder order 0 table := by
  intro powers h
  omega



theorem hasOrder_mul (order : Seed → ℕ) (firstOrder secondOrder : ℕ)
    (first second : Table Seed) (hfirst : HasOrder order firstOrder first)
    (hsecond : HasOrder order secondOrder second) :
    HasOrder order (firstOrder + secondOrder) (first * second) := by
  intro powers hp
  rw [MvPolynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro pair hpair
  have heq := Finset.HasAntidiagonal.mem_antidiagonal.mp hpair
  have hsum : weightedOrder order pair.1 + weightedOrder order pair.2 < firstOrder + secondOrder := by
    rw [← weightedOrder_add, heq]
    exact hp
  by_cases h : weightedOrder order pair.1 < firstOrder
  · rw [hfirst _ h, zero_mul]
  · rw [hsecond _ (by omega), mul_zero]









end

end AFT.RepresentedPolynomial

end

section





/-!
# Shared-queue normalization in the explicit input polynomial algebra

The average, exponential and finite reciprocal are concrete finite
polynomials.  Exactness is checked coefficient by coefficient through the
specified input-order cutoff; the activity estimates use the actual seed
weights, with no normed-algebra instance supplied as an assumption.
-/

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical

noncomputable section

variable {Seed Queue : Type*} [Fintype Queue]

omit [Fintype Queue] in
theorem hasOrder_sum {Tag : Type*} (order : Seed → ℕ) (minimum : ℕ)
    (tables : Tag → Table Seed) (tags : Finset Tag)
    (h : ∀ tag ∈ tags, HasOrder order minimum (tables tag)) :
    HasOrder order minimum (∑ tag ∈ tags, tables tag) := by
  intro powers hp
  exact (MvPolynomial.coeff_sum tags tables powers).trans
    (Finset.sum_eq_zero fun tag ht => h tag ht powers hp)

omit [Fintype Queue] in
theorem hasOrder_mono (order : Seed → ℕ) (first second : ℕ) (table : Table Seed)
    (h : HasOrder order second table) (hle : first ≤ second) : HasOrder order first table :=
  fun powers hp => h powers (hp.trans_le hle)



def queueAverage (queue : FiniteDist Queue) (tables : Queue → Table Seed) : Table Seed :=
  ∑ value, MvPolynomial.C (queue.weight value) * tables value





@[simp] theorem queueAverage_const (queue : FiniteDist Queue) (table : Table Seed) :
    queueAverage queue (fun _ => table) = table := by
  simp only [queueAverage, ← Finset.sum_mul, ← map_sum, queue.sum_one, map_one, one_mul]



























end

end AFT.RepresentedPolynomial

end

section





/-!
# The actual quotient ring of specified input seed polynomials

Only coefficients above the input-order cutoff are identified.  In
particular, equality of output images is never a quotient relation here.
-/

set_option backward.isDefEq.respectTransparency false

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical

noncomputable section

variable {Seed : Type*}

def cutoffIdeal (order : Seed → ℕ) (cutoff : ℕ) : Ideal (Table Seed) where
  carrier := {table | HasOrder order (cutoff + 1) table}
  zero_mem' := by intro powers _; simp
  add_mem' := by
    intro first second hfirst hsecond powers hp
    simp only [MvPolynomial.coeff_add, hfirst powers hp, hsecond powers hp, add_zero]
  smul_mem' := by
    intro scalar table htable
    change HasOrder order (cutoff + 1) (scalar * table)
    simpa only [zero_add] using
      hasOrder_mul order 0 (cutoff + 1) scalar table (hasOrder_zero order scalar) htable

abbrev CutoffRing (order : Seed → ℕ) (cutoff : ℕ) := (Table Seed) ⧸ cutoffIdeal order cutoff

def quotientMap (order : Seed → ℕ) (cutoff : ℕ) : Table Seed →+* CutoffRing order cutoff :=
  Ideal.Quotient.mk (cutoffIdeal order cutoff)







@[simp] theorem quotient_C (order : Seed → ℕ) (cutoff : ℕ) (scalar : ℝ) :
    quotientMap order cutoff (MvPolynomial.C scalar) = algebraMap ℝ (CutoffRing order cutoff) scalar := rfl






end

end AFT.RepresentedPolynomial

end

section







/-!
# Generating polynomials of literal input seed tables

Every channel is an actual signed finite transition table.  Substitution
into the seed polynomial is an algebra homomorphism; its product is the
joint generating polynomial on disjoint output slots.  Equal output
images do not identify distinct input representations.
-/

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {Color Output Seed : Type*} [Fintype Color] [Fintype Output]

def channelForm (channel : Color → Output → ℝ) (input : Color) : MvPolynomial Output ℝ :=
  ∑ output, MvPolynomial.C (channel input output) * MvPolynomial.X output

def seedChannel (primaryChannel bodyChannel : Color → Output → ℝ) (seed : InputSeed Color) :
    Fin (seed.primaryOrder + seed.bodyOrder) → Color → Output → ℝ :=
  Fin.addCases (fun _ => primaryChannel) (fun _ => bodyChannel)

def seedOutput (primary body : FiniteDist Color) (primaryChannel bodyChannel : Color → Output → ℝ)
    (seed : InputSeed Color) : MvPolynomial Output ℝ :=
  ∑ word : Fin (seed.primaryOrder + seed.bodyOrder) → Color,
    MvPolynomial.C (seed.kernel word * ∏ slot, (inputReference primary body seed slot).weight (word slot)) *
      ∏ slot, channelForm (seedChannel primaryChannel bodyChannel seed slot) (word slot)

/-- The represented input map uses all joint kernel entries, with their
actual product-reference weights. It does not factor a joint kernel. -/
def outputHom (primary body : FiniteDist Color) (primaryChannel bodyChannel : Color → Output → ℝ) :
    Table (InputSeed Color) →ₐ[ℝ] MvPolynomial Output ℝ :=
  MvPolynomial.aeval (seedOutput primary body primaryChannel bodyChannel)

@[simp] theorem outputHom_X (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Output → ℝ) (seed : InputSeed Color) :
    outputHom primary body primaryChannel bodyChannel (MvPolynomial.X seed) =
      seedOutput primary body primaryChannel bodyChannel seed := MvPolynomial.aeval_X _ _

omit [Fintype Color] in
theorem channelForm_homogeneous (channel : Color → Output → ℝ) (input : Color) :
    (channelForm channel input).IsHomogeneous 1 :=
  MvPolynomial.IsHomogeneous.sum _ _ _ (fun _ _ => MvPolynomial.isHomogeneous_C_mul_X _ _)

theorem seedOutput_homogeneous (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Output → ℝ) (seed : InputSeed Color) :
    (seedOutput primary body primaryChannel bodyChannel seed).IsHomogeneous
      (seed.primaryOrder + seed.bodyOrder) := by
  apply MvPolynomial.IsHomogeneous.sum
  intro word _
  apply MvPolynomial.IsHomogeneous.C_mul
  convert MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun slot => channelForm (seedChannel primaryChannel bodyChannel seed slot) (word slot))
    (fun _ => 1) (fun slot _ => channelForm_homogeneous _ _) using 1
  simp







omit [Fintype Color] [Fintype Output] in
theorem homogeneous_hasOrder (degree : ℕ) (table : Table Output)
    (h : table.IsHomogeneous degree) : HasOrder (fun _ => 1) degree table := by
  intro powers hp
  apply h.coeff_eq_zero
  change powers.sum (fun _ power => power) ≠ degree
  simpa only [weightedOrder, mul_one] using ne_of_lt hp

omit [Fintype Color] [Fintype Output] in
theorem aeval_monomial_homogeneous (order : Seed → ℕ)
    (images : Seed → MvPolynomial Output ℝ)
    (himages : ∀ seed, (images seed).IsHomogeneous (order seed))
    (powers : Seed →₀ ℕ) (coefficient : ℝ) :
    (MvPolynomial.aeval images (MvPolynomial.monomial powers coefficient)).IsHomogeneous
      (weightedOrder order powers) := by
  rw [MvPolynomial.aeval_monomial]
  change (MvPolynomial.C coefficient * _).IsHomogeneous _
  apply MvPolynomial.IsHomogeneous.C_mul
  unfold Finsupp.prod weightedOrder Finsupp.sum
  apply MvPolynomial.IsHomogeneous.prod
  intro seed _
  simpa only [mul_comm] using (himages seed).pow (powers seed)

omit [Fintype Color] [Fintype Output] in
theorem aeval_hasOrder (order : Seed → ℕ) (images : Seed → MvPolynomial Output ℝ)
    (himages : ∀ seed, (images seed).IsHomogeneous (order seed))
    (minimum : ℕ) (table : Table Seed) (h : HasOrder order minimum table) :
    HasOrder (fun _ => 1) minimum (MvPolynomial.aeval images table) := by
  conv in MvPolynomial.aeval images table => rw [MvPolynomial.as_sum table]
  rw [map_sum]
  apply hasOrder_sum
  intro powers hp
  have hmin : minimum ≤ weightedOrder order powers := by
    by_contra hlt
    exact (MvPolynomial.mem_support_iff.mp hp) (h powers (by omega))
  exact hasOrder_mono _ _ _ _
    (homogeneous_hasOrder _ _ (aeval_monomial_homogeneous order images himages powers _)) hmin

theorem outputHom_hasOrder (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Output → ℝ)
    (minimum : ℕ) (table : Table (InputSeed Color))
    (h : HasOrder (fun seed => seed.primaryOrder + seed.bodyOrder) minimum table) :
    HasOrder (fun _ => 1) minimum (outputHom primary body primaryChannel bodyChannel table) :=
  aeval_hasOrder _ _ (seedOutput_homogeneous primary body primaryChannel bodyChannel) _ _ h

/-- Degree preservation makes the same map well-defined on the two actual
cutoff rings, while retaining all distinctions in the input ring. -/
def outputQuotient (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Output → ℝ) (cutoff : ℕ) :
    CutoffRing (fun seed : InputSeed Color => seed.primaryOrder + seed.bodyOrder) cutoff →+*
      CutoffRing (fun _ : Output => 1) cutoff :=
  Ideal.Quotient.lift _
    ((quotientMap (fun _ : Output => 1) cutoff).comp
      (outputHom primary body primaryChannel bodyChannel).toRingHom)
    (fun table h => Ideal.Quotient.eq_zero_iff_mem.mpr
      (outputHom_hasOrder primary body primaryChannel bodyChannel (cutoff + 1) table h))

@[simp] theorem outputQuotient_mk (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Output → ℝ) (cutoff : ℕ)
    (table : Table (InputSeed Color)) :
    outputQuotient primary body primaryChannel bodyChannel cutoff
      (quotientMap (fun seed : InputSeed Color => seed.primaryOrder + seed.bodyOrder) cutoff table) =
      quotientMap (fun _ : Output => 1) cutoff
        (outputHom primary body primaryChannel bodyChannel table) := rfl



end

end AFT.RepresentedPolynomial

end

section




































namespace AFT
end AFT
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPairResidualInput
end AFT.GaussianSource.actualPairResidualInput
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.actualRootLaw
end AFT.GaussianSource.actualRootLaw
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.GaussianSource.pairNeumannConstant
end AFT.GaussianSource.pairNeumannConstant
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.partialInputLinear
end AFT.MixedKernel.partialInputLinear
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.RowBound
end AFT.SafeConvolution.RowBound
namespace AFT.SafeConvolution.SupBound
end AFT.SafeConvolution.SupBound
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
namespace AFT.SafePair
end AFT.SafePair
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveBodyPairDensity
end AFT.V7Calibration.actualInactiveBodyPairDensity
namespace AFT.V7Calibration.actualInactiveBodyPairMass
end AFT.V7Calibration.actualInactiveBodyPairMass
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedFringeInput
end AFT.V7Calibration.actualMarkedFringeInput
namespace AFT.V7Calibration.actualMarkedInput
end AFT.V7Calibration.actualMarkedInput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactivePairShift
end AFT.V7Calibration.inactivePairShift
namespace AFT.V7Calibration.inactivePairSources
end AFT.V7Calibration.inactivePairSources
namespace AFT.V7Calibration.inactivePairStarts
end AFT.V7Calibration.inactivePairStarts
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap



/-! # Exact evaluation of the actual body and endpoint mean input tables -/

namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]

def profileForm : (Color → ℝ) →ₗ[ℝ] MvPolynomial Color ℝ where
  toFun profile := ∑ color, MvPolynomial.C (profile color)*MvPolynomial.X color
  map_add' first second := by simp only [Pi.add_apply,map_add,add_mul,Finset.sum_add_distrib]
  map_smul' scalar profile := by
    simp only [Pi.smul_apply,smul_eq_mul,map_mul,Finset.mul_sum,RingHom.id_apply,MvPolynomial.smul_eq_C_mul,mul_assoc]



end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section






end
end AFT.V7Calibration

end

section









/-! # Exact centered generating polynomials of finite physical laws -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]

theorem profileForm_apply (profile : Color → ℝ) :
    profileForm profile = ∑ color,MvPolynomial.C (profile color)*MvPolynomial.X color := rfl

/-- The color factor used by the actual centered histogram generating law. -/
def centeredFactor (reference : Color → ℝ) (color : Color) : MvPolynomial Color ℝ :=
  1+MvPolynomial.X color-profileForm reference

def singleGenerating (reference profile : Color → ℝ) : MvPolynomial Color ℝ :=
  ∑ color,MvPolynomial.C (profile color)*centeredFactor reference color

def pairForm (mass : Color → Color → ℝ) : MvPolynomial Color ℝ :=
  ∑ first,∑ second,MvPolynomial.C (mass first second)*MvPolynomial.X first*MvPolynomial.X second



def pairGenerating (reference : Color → ℝ) (mass : Color → Color → ℝ) : MvPolynomial Color ℝ :=
  ∑ first,∑ second,MvPolynomial.C (mass first second)*centeredFactor reference first*centeredFactor reference second

def tripleGenerating (reference : Color → ℝ) (mass : Color → Color → Color → ℝ) : MvPolynomial Color ℝ :=
  ∑ first,∑ second,∑ third,MvPolynomial.C (mass first second third)*centeredFactor reference first*
    centeredFactor reference second*centeredFactor reference third



























end
end AFT.RepresentedPolynomial

end

section





/-! # The exact rational formal logarithm used by finite log certificates -/

namespace AFT.FormalLogarithm

open scoped BigOperators Classical PowerSeries

noncomputable section

set_option backward.isDefEq.respectTransparency false

def logarithm : PowerSeries ℚ := PowerSeries.mk fun order =>
  match order with
  | 0 => 0
  | index + 1 => (-1 : ℚ) ^ index / (index + 1)

@[simp] theorem logarithm_constant : PowerSeries.constantCoeff logarithm = 0 := rfl











end

end AFT.FormalLogarithm

end

section











/-! # Ordinary generating polynomials determine the entire finite histogram -/
namespace AFT.HistogramGenerating
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color Slot : Type*} [Fintype Color] [Fintype Slot]

/-- Color counts for an arbitrary finite set of physical coordinates. -/
def counts (word : Slot → Color) : Color →₀ ℕ := ∑ slot,Finsupp.single (word slot) 1

omit [Fintype Color] in
theorem counts_apply (word : Slot → Color) (color : Color) :
    counts word color = Fintype.card {slot // word slot=color} := by
  simp only [counts,Finsupp.finset_sum_apply,Finsupp.single_apply]
  simp only [← Finset.card_filter,← Fintype.card_subtype]

def boundedHistogram (N : ℕ) (hcard : Fintype.card Slot≤N) (word : Slot → Color) : Histogram N Color :=
  fun color => ⟨counts word color,by
    rw [counts_apply]
    exact Nat.lt_succ_of_le ((Fintype.card_subtype_le _).trans hcard)⟩

def histogramExponent (N : ℕ) (hist : Histogram N Color) : Color →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun color => (hist color : ℕ)



@[simp] theorem boundedHistogram_exponent (N : ℕ) (hcard : Fintype.card Slot≤N) (word : Slot → Color) :
    histogramExponent N (boundedHistogram N hcard word)=counts word := by ext color; rfl













end
end AFT.HistogramGenerating

end

section





/-! # Exact action of coordinate profile operators on a spanning product family -/

namespace AFT.MixedKernel

open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

def productKernel (functions : Slot → Color → ℝ) (word : Slot → Color) : ℝ :=
  ∏ slot, functions slot (word slot)



















end
end AFT.MixedKernel

end

section



































namespace AFT
end AFT
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPairResidualInput
end AFT.GaussianSource.actualPairResidualInput
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.GaussianSource.pairNeumannConstant
end AFT.GaussianSource.pairNeumannConstant
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.RowBound
end AFT.SafeConvolution.RowBound
namespace AFT.SafeConvolution.SupBound
end AFT.SafeConvolution.SupBound
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
namespace AFT.SafePair
end AFT.SafePair
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualInactiveBodyPairDensity
end AFT.V7Calibration.actualInactiveBodyPairDensity
namespace AFT.V7Calibration.actualInactiveBodyPairMass
end AFT.V7Calibration.actualInactiveBodyPairMass
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedInput
end AFT.V7Calibration.actualMarkedInput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactivePairShift
end AFT.V7Calibration.inactivePairShift
namespace AFT.V7Calibration.inactivePairSources
end AFT.V7Calibration.inactivePairSources
namespace AFT.V7Calibration.inactivePairStarts
end AFT.V7Calibration.inactivePairStarts
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap




/-! # Actual joint root convolution of literal body and mixed pair inputs -/

namespace AFT.FiniteDist

open scoped BigOperators Classical
noncomputable section
variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]



end
end AFT.FiniteDist

namespace AFT.SafeConvolution

open scoped BigOperators Classical
noncomputable section
variable {G : Type*} [Fintype G] [AddCommGroup G]



end
end AFT.SafeConvolution

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color]
local instance jointPairFinDecEq (n : ℕ) : DecidableEq (Fin n) := instDecidableEqFin n


end
end AFT.RepresentedPolynomial

namespace AFT.GaussianSource

noncomputable section



end
end AFT.GaussianSource

namespace AFT.V7Calibration

open GaussianSource SafeConvolution RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] actualModulusNeZero





end
end AFT.V7Calibration

end

section











namespace AFT
end AFT
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput



/-! # Literal finite seed monomials as disjoint joint input kernels -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color]

/-- Every seed occurrence has its own distinct input coordinates. -/
def ControlProductSlot : List (InputSeed Color) → Type
  | [] => PEmpty
  | seed :: rest => Fin (seed.primaryOrder + seed.bodyOrder) ⊕ ControlProductSlot rest

instance controlProductSlotFintype (seeds : List (InputSeed Color)) : Fintype (ControlProductSlot seeds) := by
  induction seeds with
  | nil => exact inferInstanceAs (Fintype PEmpty)
  | cons seed rest ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Fin (seed.primaryOrder + seed.bodyOrder) ⊕ ControlProductSlot rest))

instance controlProductSlotDecEq (seeds : List (InputSeed Color)) : DecidableEq (ControlProductSlot seeds) := by
  induction seeds with
  | nil => exact inferInstanceAs (DecidableEq PEmpty)
  | cons seed rest ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (Fin (seed.primaryOrder + seed.bodyOrder) ⊕ ControlProductSlot rest))































end
end AFT.RepresentedPolynomial

end

section

























































namespace AFT
end AFT
namespace AFT.BetaReference
end AFT.BetaReference
namespace AFT.BetaReference.convexLaw
end AFT.BetaReference.convexLaw
namespace AFT.BetaReference.inverseBinomial
end AFT.BetaReference.inverseBinomial
namespace AFT.BetaReference.referenceHistogram
end AFT.BetaReference.referenceHistogram
namespace AFT.BetaReference.retainedIntegrand
end AFT.BetaReference.retainedIntegrand
namespace AFT.BetaReference.splitLabelLaw
end AFT.BetaReference.splitLabelLaw
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPairResidualInput
end AFT.GaussianSource.actualPairResidualInput
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.actualRootLaw
end AFT.GaussianSource.actualRootLaw
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.extraSample
end AFT.GaussianSource.extraSample
namespace AFT.GaussianSource.optionalShift
end AFT.GaussianSource.optionalShift
namespace AFT.GaussianSource.optionalShift.match_1
end AFT.GaussianSource.optionalShift.match_1
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.GaussianSource.pairNeumannConstant
end AFT.GaussianSource.pairNeumannConstant
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.GaussianSource.rootMarginal
end AFT.GaussianSource.rootMarginal
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.backgroundLogarithm
end AFT.RepresentedPolynomial.backgroundLogarithm
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.boundaryPolynomial
end AFT.RepresentedPolynomial.boundaryPolynomial
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.inversePrimarySeed
end AFT.RepresentedPolynomial.inversePrimarySeed
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.profilePolynomialMap
end AFT.RepresentedPolynomial.profilePolynomialMap
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.reference
end AFT.RootSlice.reference
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.RowBound
end AFT.SafeConvolution.RowBound
namespace AFT.SafeConvolution.SupBound
end AFT.SafeConvolution.SupBound
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
namespace AFT.SafeConvolution.uniformCanonical
end AFT.SafeConvolution.uniformCanonical
namespace AFT.SafePair
end AFT.SafePair
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointDifference
end AFT.V7Calibration.activeEndpointDifference
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualBoundaryProfile
end AFT.V7Calibration.actualBoundaryProfile
namespace AFT.V7Calibration.actualCanonicalPairResidualInput
end AFT.V7Calibration.actualCanonicalPairResidualInput
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualCovarianceTable
end AFT.V7Calibration.actualCovarianceTable
namespace AFT.V7Calibration.actualEndpointHigherTable
end AFT.V7Calibration.actualEndpointHigherTable
namespace AFT.V7Calibration.actualEndpointSeed
end AFT.V7Calibration.actualEndpointSeed
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveBodyPairDensity
end AFT.V7Calibration.actualInactiveBodyPairDensity
namespace AFT.V7Calibration.actualInactiveBodyPairInput
end AFT.V7Calibration.actualInactiveBodyPairInput
namespace AFT.V7Calibration.actualInactiveBodyPairMass
end AFT.V7Calibration.actualInactiveBodyPairMass
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualInteriorProfile
end AFT.V7Calibration.actualInteriorProfile
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedFringeInput
end AFT.V7Calibration.actualMarkedFringeInput
namespace AFT.V7Calibration.actualMarkedInput
end AFT.V7Calibration.actualMarkedInput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualMarkedSafeDensity
end AFT.V7Calibration.actualMarkedSafeDensity
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualPairCompletionInput
end AFT.V7Calibration.actualPairCompletionInput
namespace AFT.V7Calibration.actualPairReferenceInput
end AFT.V7Calibration.actualPairReferenceInput
namespace AFT.V7Calibration.actualPositiveReferenceLaw
end AFT.V7Calibration.actualPositiveReferenceLaw
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualReferenceMarkedProfile
end AFT.V7Calibration.actualReferenceMarkedProfile
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.actual_body_population_expectation
end AFT.V7Calibration.actual_body_population_expectation
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.attachedBodyAtSource
end AFT.V7Calibration.attachedBodyAtSource
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.blockBackgroundError
end AFT.V7Calibration.blockBackgroundError
namespace AFT.V7Calibration.blockBackgroundLinear
end AFT.V7Calibration.blockBackgroundLinear
namespace AFT.V7Calibration.blockBackgroundLinear.match_1
end AFT.V7Calibration.blockBackgroundLinear.match_1
namespace AFT.V7Calibration.blockBodyMeanProfile
end AFT.V7Calibration.blockBodyMeanProfile
namespace AFT.V7Calibration.blockBodyMeanProfile.match_1
end AFT.V7Calibration.blockBodyMeanProfile.match_1
namespace AFT.V7Calibration.blockBodyMeanTable
end AFT.V7Calibration.blockBodyMeanTable
namespace AFT.V7Calibration.blockBodyMeanTable.match_1
end AFT.V7Calibration.blockBodyMeanTable.match_1
namespace AFT.V7Calibration.blockPhysicalPolynomial
end AFT.V7Calibration.blockPhysicalPolynomial
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.endpointCoefficient
end AFT.V7Calibration.endpointCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.V7Calibration.globalLinearProfile
end AFT.V7Calibration.globalLinearProfile
namespace AFT.V7Calibration.globalLinearTable
end AFT.V7Calibration.globalLinearTable
namespace AFT.V7Calibration.globalMeanChangeTable
end AFT.V7Calibration.globalMeanChangeTable
namespace AFT.V7Calibration.globalMeanTable
end AFT.V7Calibration.globalMeanTable
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairDensity
end AFT.V7Calibration.inactiveCanonicalPairDensity
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactiveEndpointMarginalDensity
end AFT.V7Calibration.inactiveEndpointMarginalDensity
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactivePairShift
end AFT.V7Calibration.inactivePairShift
namespace AFT.V7Calibration.inactivePairSources
end AFT.V7Calibration.inactivePairSources
namespace AFT.V7Calibration.inactivePairStarts
end AFT.V7Calibration.inactivePairStarts
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localAttachedMeanInputTable
end AFT.V7Calibration.localAttachedMeanInputTable
namespace AFT.V7Calibration.localBackgroundLinear
end AFT.V7Calibration.localBackgroundLinear
namespace AFT.V7Calibration.localBodyMixture
end AFT.V7Calibration.localBodyMixture
namespace AFT.V7Calibration.localCovarianceInputTable
end AFT.V7Calibration.localCovarianceInputTable
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.localPrimaryMeanInputTable
end AFT.V7Calibration.localPrimaryMeanInputTable
namespace AFT.V7Calibration.primaryPairSeed
end AFT.V7Calibration.primaryPairSeed
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap



/-! # The actual positive V7 reference mixed over its legal beta interval -/
namespace AFT.V7Calibration
open GaussianSource BetaReference HistogramGenerating Filter MeasureTheory
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] actualModulusNeZero















local instance actualBetaReferenceFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def reinstanceFiniteDist {α : Type*} {first : Fintype α} (second : Fintype α)
    (law : @FiniteDist α first) : @FiniteDist α second := by
  cases Subsingleton.elim first second
  exact law

@[simp] theorem reinstanceFiniteDist_weight {α : Type*} {first : Fintype α} (second : Fintype α)
    (law : @FiniteDist α first) : @FiniteDist.weight α second (reinstanceFiniteDist second law)=@FiniteDist.weight α first law := by
  unfold reinstanceFiniteDist
  cases Subsingleton.elim first second
  rfl







end
end AFT.V7Calibration

end

section




/-! # An executable exact rational CDF for the integer beta distribution

Only rational arithmetic and finite sums occur in `rationalCDF`.  The
identity with the genuine beta integral is proved below; no real-number
comparison or integration oracle is part of its evaluation.
-/
namespace AFT.BetaReference
open MeasureTheory
open scoped BigOperators

/-- Exact rational evaluation of the beta CDF at a rational point. -/
def rationalCDF (K n : ℕ) (x : ℚ) : ℚ :=
  ((K+n+1).factorial : ℚ)/(K.factorial*n.factorial)*
    ∑ j∈Finset.range (n+1),(n.choose j : ℚ)*(-1)^j*x^(K+j+1)/(K+j+1 : ℕ)

/-- The finite polynomial expansion being integrated by the evaluator. -/
theorem density_sum (K n : ℕ) (x : ℝ) :
    density K n x=∑ j∈Finset.range (n+1),
      (((K+n+1).factorial : ℝ)/(K.factorial*n.factorial)*(n.choose j : ℝ)*(-1)^j)*x^(K+j) := by
  have hp := add_pow (-x) (1 : ℝ) n
  rw [show -x+1=1-x by ring] at hp
  simp only [one_pow,mul_one] at hp
  unfold density
  rw [hp,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add,neg_pow]
  ring

/-- Exact antiderivative formula, valid at every real endpoint. -/
theorem density_integral_polynomial (K n : ℕ) (x : ℝ) :
    (∫ y : ℝ in (0 : ℝ)..x,density K n y)=
      ((K+n+1).factorial : ℝ)/(K.factorial*n.factorial)*
        ∑ j∈Finset.range (n+1),(n.choose j : ℝ)*(-1)^j*x^(K+j+1)/(K+j+1 : ℕ) := by
  simp_rw [density_sum]
  rw [intervalIntegral.integral_finset_sum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [intervalIntegral.integral_const_mul
      (((K+n+1).factorial : ℝ)/(K.factorial*n.factorial)*(n.choose j : ℝ)*(-1)^j)
      (fun y : ℝ => y^(K+j)),integral_pow]
    simp only [zero_pow (by omega : K+j+1≠0),sub_zero,Nat.cast_add,Nat.cast_one]
    ring
  · intro j _
    exact (by fun_prop : Continuous (fun y : ℝ =>
      (((K+n+1).factorial : ℝ)/(K.factorial*n.factorial)*(n.choose j : ℝ)*(-1)^j)*y^(K+j))).intervalIntegrable _ _

/-- The rational program computes the actual continuous beta CDF exactly. -/
theorem rationalCDF_eq_integral (K n : ℕ) (x : ℚ) :
    (rationalCDF K n x : ℝ)=∫ y : ℝ in (0 : ℝ)..(x : ℝ),density K n y := by
  rw [density_integral_polynomial]
  unfold rationalCDF
  push_cast
  rfl

@[simp] theorem rationalCDF_zero (K n : ℕ) : rationalCDF K n 0=0 := by
  unfold rationalCDF
  have hs : (∑ j∈Finset.range (n+1),(n.choose j : ℚ)*(-1)^j*0^(K+j+1)/(K+j+1 : ℕ))=0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [show (0 : ℚ)^(K+j+1)=0 from zero_pow (by omega)]
    simp
  rw [hs,mul_zero]

@[simp] theorem rationalCDF_one (K n : ℕ) : rationalCDF K n 1=1 := by
  apply Rat.cast_injective (α:=ℝ)
  rw [rationalCDF_eq_integral]
  simpa only [Rat.cast_one] using density_integral_one K n





end AFT.BetaReference

end

section




/-! # The genuine beta law rounded upward to a finite rational grid -/
namespace AFT.BetaReference
open MeasureTheory
open scoped BigOperators

/-- Cumulative mass at the exact rational grid endpoint. -/
def gridCDF (K n M j : ℕ) : ℚ := rationalCDF K n ((j : ℚ)/M)

theorem gridCDF_zero (K n M : ℕ) : gridCDF K n M 0=0 := by simp [gridCDF]
theorem gridCDF_total (K n M : ℕ) (hM : 0<M) : gridCDF K n M M=1 := by
  simp [gridCDF,ne_of_gt hM]



noncomputable section









end
end AFT.BetaReference

end

section





namespace AFT
end AFT
namespace AFT.BinaryCDFSampler
end AFT.BinaryCDFSampler
namespace AFT.BinaryCDFSampler.draw
end AFT.BinaryCDFSampler.draw
namespace AFT.BinaryCDFSampler.locate
end AFT.BinaryCDFSampler.locate
namespace AFT.BinaryCDFSampler.locate.match_1
end AFT.BinaryCDFSampler.locate.match_1
namespace AFT.BinaryCDFSampler.locateQueries
end AFT.BinaryCDFSampler.locateQueries



/-! # Finite fair-bit beta sampling by rational CDF binary search -/
namespace AFT.BetaReference
open scoped BigOperators

/-- Integer cumulative counts computed from the exact rational beta CDF. -/
def finiteCut (K n depth bits j : ℕ) : ℕ :=
  ⌊((2^bits : ℕ) : ℚ)*gridCDF K n (2^depth) j⌋₊







@[simp] theorem finiteCut_zero (K n depth bits : ℕ) : finiteCut K n depth bits 0=0 := by
  simp [finiteCut,gridCDF_zero]

@[simp] theorem finiteCut_total (K n depth bits : ℕ) : finiteCut K n depth bits (2^depth)=2^bits := by
  simp only [finiteCut,gridCDF_total K n (2^depth) (by positivity),mul_one,Nat.floor_natCast]

noncomputable section
open scoped Classical











end
end AFT.BetaReference

end

section





































































namespace AFT
end AFT
namespace AFT.BetaReference
end AFT.BetaReference
namespace AFT.BetaReference.density_succ
end AFT.BetaReference.density_succ
namespace AFT.BetaReference.event_mono
end AFT.BetaReference.event_mono
namespace AFT.BetaReference.gridLaw
end AFT.BetaReference.gridLaw
namespace AFT.BetaReference.gridTailLaw
end AFT.BetaReference.gridTailLaw
namespace AFT.BetaReference.momentCoefficient
end AFT.BetaReference.momentCoefficient
namespace AFT.BetaReference.referenceHistogram
end AFT.BetaReference.referenceHistogram
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.TVBound
end AFT.FiniteDist.TVBound
namespace AFT.FiniteDist.conditionalSource
end AFT.FiniteDist.conditionalSource
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPairResidualInput
end AFT.GaussianSource.actualPairResidualInput
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.actualRootLaw
end AFT.GaussianSource.actualRootLaw
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.extraSample
end AFT.GaussianSource.extraSample
namespace AFT.GaussianSource.gaussianKernel
end AFT.GaussianSource.gaussianKernel
namespace AFT.GaussianSource.harmonicWidth
end AFT.GaussianSource.harmonicWidth
namespace AFT.GaussianSource.kernelPower
end AFT.GaussianSource.kernelPower
namespace AFT.GaussianSource.normalizedRoot
end AFT.GaussianSource.normalizedRoot
namespace AFT.GaussianSource.optionalShift
end AFT.GaussianSource.optionalShift
namespace AFT.GaussianSource.optionalShift.match_1
end AFT.GaussianSource.optionalShift.match_1
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.GaussianSource.pairNeumannConstant
end AFT.GaussianSource.pairNeumannConstant
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.GaussianSource.powerWidth
end AFT.GaussianSource.powerWidth
namespace AFT.GaussianSource.powerWidth.match_1
end AFT.GaussianSource.powerWidth.match_1
namespace AFT.GaussianSource.ratioError
end AFT.GaussianSource.ratioError
namespace AFT.GaussianSource.rootMarginal
end AFT.GaussianSource.rootMarginal
namespace AFT.GaussianSource.rootMomentConstant
end AFT.GaussianSource.rootMomentConstant
namespace AFT.GaussianSource.rootPrefixDensity
end AFT.GaussianSource.rootPrefixDensity
namespace AFT.GaussianSource.shiftedWeight
end AFT.GaussianSource.shiftedWeight
namespace AFT.GaussianSource.sumWidth
end AFT.GaussianSource.sumWidth
namespace AFT.GaussianSource.theta
end AFT.GaussianSource.theta
namespace AFT.GaussianSource.thetaFourier
end AFT.GaussianSource.thetaFourier
namespace AFT.GaussianSource.v7RootKernelSq
end AFT.GaussianSource.v7RootKernelSq
namespace AFT.GaussianSource.v7RootThetaBound
end AFT.GaussianSource.v7RootThetaBound
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.Negligible
end AFT.Negligible
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.backgroundLogarithm
end AFT.RepresentedPolynomial.backgroundLogarithm
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.boundaryPolynomial
end AFT.RepresentedPolynomial.boundaryPolynomial
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.inversePrimarySeed
end AFT.RepresentedPolynomial.inversePrimarySeed
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.profilePolynomialMap
end AFT.RepresentedPolynomial.profilePolynomialMap
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.quadraticExponent
end AFT.RootSlice.quadraticExponent
namespace AFT.RootSlice.reference
end AFT.RootSlice.reference
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.RowBound
end AFT.SafeConvolution.RowBound
namespace AFT.SafeConvolution.SupBound
end AFT.SafeConvolution.SupBound
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
namespace AFT.SafeConvolution.uniformCanonical
end AFT.SafeConvolution.uniformCanonical
namespace AFT.SafePair
end AFT.SafePair
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointDifference
end AFT.V7Calibration.activeEndpointDifference
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualBoundaryProfile
end AFT.V7Calibration.actualBoundaryProfile
namespace AFT.V7Calibration.actualCanonicalPairResidualInput
end AFT.V7Calibration.actualCanonicalPairResidualInput
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualCovarianceTable
end AFT.V7Calibration.actualCovarianceTable
namespace AFT.V7Calibration.actualEndpointHigherTable
end AFT.V7Calibration.actualEndpointHigherTable
namespace AFT.V7Calibration.actualEndpointSeed
end AFT.V7Calibration.actualEndpointSeed
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveBodyPairDensity
end AFT.V7Calibration.actualInactiveBodyPairDensity
namespace AFT.V7Calibration.actualInactiveBodyPairInput
end AFT.V7Calibration.actualInactiveBodyPairInput
namespace AFT.V7Calibration.actualInactiveBodyPairMass
end AFT.V7Calibration.actualInactiveBodyPairMass
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualInteriorProfile
end AFT.V7Calibration.actualInteriorProfile
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedFringeInput
end AFT.V7Calibration.actualMarkedFringeInput
namespace AFT.V7Calibration.actualMarkedInput
end AFT.V7Calibration.actualMarkedInput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualMarkedSafeDensity
end AFT.V7Calibration.actualMarkedSafeDensity
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualPairCompletionInput
end AFT.V7Calibration.actualPairCompletionInput
namespace AFT.V7Calibration.actualPairReferenceInput
end AFT.V7Calibration.actualPairReferenceInput
namespace AFT.V7Calibration.actualPositiveReferenceLaw
end AFT.V7Calibration.actualPositiveReferenceLaw
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualReferenceMarkedProfile
end AFT.V7Calibration.actualReferenceMarkedProfile
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.actual_body_population_expectation
end AFT.V7Calibration.actual_body_population_expectation
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.attachedBodyAtSource
end AFT.V7Calibration.attachedBodyAtSource
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.betaGridMesh
end AFT.V7Calibration.betaGridMesh
namespace AFT.V7Calibration.betaGridStart
end AFT.V7Calibration.betaGridStart
namespace AFT.V7Calibration.blockBackgroundError
end AFT.V7Calibration.blockBackgroundError
namespace AFT.V7Calibration.blockBackgroundLinear
end AFT.V7Calibration.blockBackgroundLinear
namespace AFT.V7Calibration.blockBackgroundLinear.match_1
end AFT.V7Calibration.blockBackgroundLinear.match_1
namespace AFT.V7Calibration.blockBodyMeanProfile
end AFT.V7Calibration.blockBodyMeanProfile
namespace AFT.V7Calibration.blockBodyMeanProfile.match_1
end AFT.V7Calibration.blockBodyMeanProfile.match_1
namespace AFT.V7Calibration.blockBodyMeanTable
end AFT.V7Calibration.blockBodyMeanTable
namespace AFT.V7Calibration.blockBodyMeanTable.match_1
end AFT.V7Calibration.blockBodyMeanTable.match_1
namespace AFT.V7Calibration.blockPhysicalPolynomial
end AFT.V7Calibration.blockPhysicalPolynomial
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.endpointCoefficient
end AFT.V7Calibration.endpointCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.V7Calibration.globalLinearProfile
end AFT.V7Calibration.globalLinearProfile
namespace AFT.V7Calibration.globalLinearTable
end AFT.V7Calibration.globalLinearTable
namespace AFT.V7Calibration.globalMeanChangeTable
end AFT.V7Calibration.globalMeanChangeTable
namespace AFT.V7Calibration.globalMeanTable
end AFT.V7Calibration.globalMeanTable
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairDensity
end AFT.V7Calibration.inactiveCanonicalPairDensity
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactiveEndpointMarginalDensity
end AFT.V7Calibration.inactiveEndpointMarginalDensity
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactivePairShift
end AFT.V7Calibration.inactivePairShift
namespace AFT.V7Calibration.inactivePairSources
end AFT.V7Calibration.inactivePairSources
namespace AFT.V7Calibration.inactivePairStarts
end AFT.V7Calibration.inactivePairStarts
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localAttachedMeanInputTable
end AFT.V7Calibration.localAttachedMeanInputTable
namespace AFT.V7Calibration.localBackgroundLinear
end AFT.V7Calibration.localBackgroundLinear
namespace AFT.V7Calibration.localBodyMixture
end AFT.V7Calibration.localBodyMixture
namespace AFT.V7Calibration.localCovarianceInputTable
end AFT.V7Calibration.localCovarianceInputTable
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.localPrimaryMeanInputTable
end AFT.V7Calibration.localPrimaryMeanInputTable
namespace AFT.V7Calibration.primaryPairSeed
end AFT.V7Calibration.primaryPairSeed
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap



/-! # The root Gaussian is supplied by a proved rational program -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics FiniteConvolutionProgram FiniteDist
open scoped BigOperators

/-- The actual squared root width is rational and requires no square-root oracle. -/
def actualRootSquaredWidth (n : ℕ) : ℚ := 8*(n : ℚ)^2

def actualRootGaussianWeights (n bits : ℕ) (index : Fin (2*(3*n^2-1)+1)) : ℚ :=
  windowApproxWeight (actualRootSquaredWidth n) (3*n^2-1) bits (windowIndexEquiv _ index)



noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
local instance actualRootGaussianProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _













end
end AFT.V7Calibration

end

section





namespace AFT
end AFT
namespace AFT.FiniteConvolutionProgram
end AFT.FiniteConvolutionProgram
namespace AFT.FiniteConvolutionProgram.rowTerm
end AFT.FiniteConvolutionProgram.rowTerm
namespace AFT.V7Calibration
end AFT.V7Calibration



/-! # Actual integer-ticket root convolution with polynomial binary lengths -/
namespace AFT.V7Calibration
open GaussianSource FiniteConvolutionProgram
open scoped BigOperators

/-- No rational reduction is performed within the convolution. The complete
integer numerator is divided by the common ticket denominator at the end. -/
def actualRootIntegerConvolution (n : ℕ) (counts : Fin (2*(3*n^2-1)+1) → ℕ)
    (count : ℕ) : Result ℕ :=
  run (2*(3*n^2-1)) counts count

noncomputable section





end
end AFT.V7Calibration

end

section

















/-! # Actual root Gaussian weights, integer tickets, and fair-bit sampling -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics FiniteConvolutionProgram FiniteDist
open scoped BigOperators

/-- The ticket guard absorbs the support size; the Gaussian program itself
uses one additional precision bit so both errors fit in the requested budget. -/
def actualRootTicketBits (n bits : ℕ) : ℕ := bits+(2*(3*n^2-1)+1)+2





def actualRootTicketCounts (n bits : ℕ) : Fin (2*(3*n^2-1)+1) → ℕ :=
  RationalFiniteQuantization.counts (actualRootGaussianWeights n (bits+1)) (2^(actualRootTicketBits n bits))





noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false











local instance actualRootGaussianTicketsFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _





end
end AFT.V7Calibration

end

section




/-!
# Conditional positive repair as an actual finite probability law

Repair is performed separately within each retained public skeleton.  The
skeleton's entire marginal law is therefore preserved, including rare events.
The error bound averages the centered moment before applying any physical
output channel and has no extra charge-conditioning factor.
-/

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

variable {S A B : Type*} [Fintype S] [Fintype A] [Fintype B]

def joint (skeleton : FiniteDist S) (proposal : S → FiniteDist A) : FiniteDist (S × A) where
  weight pair := skeleton.weight pair.1 * (proposal pair.1).weight pair.2
  nonneg pair := mul_nonneg (skeleton.nonneg _) ((proposal _).nonneg _)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, sum_one, mul_one]
    exact skeleton.sum_one

@[simp] theorem joint_weight (skeleton : FiniteDist S) (proposal : S → FiniteDist A) (s : S) (a : A) :
    (joint skeleton proposal).weight (s, a) = skeleton.weight s * (proposal s).weight a := rfl

@[simp] theorem joint_skeleton (skeleton : FiniteDist S) (proposal : S → FiniteDist A) :
    (joint skeleton proposal).map Prod.fst = skeleton := by
  ext s
  simp only [map_weight, Fintype.sum_prod_type, joint_weight]
  trans ∑ x, if x = s then skeleton.weight x else 0
  · apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x = s
    · simp only [if_pos hx, ← Finset.mul_sum, sum_one, mul_one]
    · simp only [if_neg hx, Finset.sum_const_zero]
  · simp

def weightedMass (proposal : FiniteDist A) (weight : A → ℝ) : A → ℝ :=
  fun a => proposal.weight a * weight a

def positiveRepairLaw (proposal : FiniteDist A) (weight : A → ℝ)
    (hmean : 0 < signedMass (weightedMass proposal weight)) : FiniteDist A where
  weight a := max (weightedMass proposal weight a) 0 / positiveMass (weightedMass proposal weight)
  nonneg := (positive_repair_normalized _ hmean).1
  sum_one := (positive_repair_normalized _ hmean).2

@[simp] theorem positiveRepairLaw_weight (proposal : FiniteDist A) (weight : A → ℝ)
    (hmean : 0 < signedMass (weightedMass proposal weight)) (a : A) :
    (positiveRepairLaw proposal weight hmean).weight a =
      proposal.weight a * max (weight a) 0 / positiveMass (weightedMass proposal weight) := by
  change max (proposal.weight a * weight a) 0 / _ = _
  rw [mul_max_of_nonneg _ _ (proposal.nonneg a), mul_zero]

















end

end AFT.FiniteDist

end

section




/-!
# Finite capped rejection, exact output law and retry error

This module describes the finite-probability semantics of rejection sampling.
It does not assert a bit-machine implementation for real probabilities.
-/

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

variable {A S : Type*} [Fintype A] [Fintype S]

def acceptance (proposal : FiniteDist A) (coin : A → ℝ) : ℝ :=
  ∑ a, proposal.weight a * coin a

theorem acceptance_bounds (proposal : FiniteDist A) (coin : A → ℝ)
    (hcoin : ∀ a, 0 ≤ coin a ∧ coin a ≤ 1) :
    0 ≤ acceptance proposal coin ∧ acceptance proposal coin ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun a _ => mul_nonneg (proposal.nonneg a) (hcoin a).1
  · calc
      _ ≤ ∑ a, proposal.weight a * 1 := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (hcoin a).2 (proposal.nonneg a)
      _ = 1 := by simp only [mul_one, proposal.sum_one]

def acceptedLaw (proposal : FiniteDist A) (coin : A → ℝ)
    (hcoin : ∀ a, 0 ≤ coin a) (haccept : 0 < acceptance proposal coin) : FiniteDist A where
  weight a := proposal.weight a * coin a / acceptance proposal coin
  nonneg a := div_nonneg (mul_nonneg (proposal.nonneg a) (hcoin a)) haccept.le
  sum_one := by rw [← Finset.sum_div]; exact div_self (ne_of_gt haccept)

/-- One fresh proposal is accepted or replaced by the recursively obtained
remaining-attempt law. -/
def rejectionStep (proposal : FiniteDist A) (coin : A → ℝ)
    (hcoin : ∀ a, 0 ≤ coin a ∧ coin a ≤ 1) (remaining : FiniteDist A) : FiniteDist A where
  weight a := proposal.weight a * coin a + (1 - acceptance proposal coin) * remaining.weight a
  nonneg a := add_nonneg (mul_nonneg (proposal.nonneg a) (hcoin a).1)
    (mul_nonneg (sub_nonneg.mpr (acceptance_bounds proposal coin hcoin).2) (remaining.nonneg a))
  sum_one := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, remaining.sum_one, mul_one]
    change acceptance proposal coin + (1 - acceptance proposal coin) = 1
    ring

def cappedRejection (proposal : FiniteDist A) (coin : A → ℝ)
    (hcoin : ∀ a, 0 ≤ coin a ∧ coin a ≤ 1) (fallback : FiniteDist A) : ℕ → FiniteDist A
  | 0 => fallback
  | count + 1 => rejectionStep proposal coin hcoin (cappedRejection proposal coin hcoin fallback count)









end

end AFT.FiniteDist

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

variable {A : Type*} [Fintype A]













end

end AFT.FiniteDist

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

variable {A S : Type*} [Fintype A] [Fintype S]









end

end AFT.FiniteDist

end

section






namespace AFT
end AFT
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.TVBound
end AFT.FiniteDist.TVBound
namespace AFT.FiniteDist.acceptance
end AFT.FiniteDist.acceptance
namespace AFT.FiniteDist.cappedCondition
end AFT.FiniteDist.cappedCondition
namespace AFT.FiniteDist.conditionalSource
end AFT.FiniteDist.conditionalSource
namespace AFT.FiniteDist.eventCoin
end AFT.FiniteDist.eventCoin



/-! # Executable finite rejection for a decidable event

The procedure checks a finite stream in order, returns its first accepted
entry, and returns a fixed fallback if every check fails. It evaluates no
real probabilities. Its law is exactly the capped conditioning law.
-/

namespace AFT.FiniteConditionProgram

open scoped BigOperators

variable {State : Type*}







/-- Explicit row-major regrouping of one finite bit tape into proposal tapes. -/
def groupBits (attempts bits : ℕ) :
    (Fin (attempts * bits) → Fin 2) ≃ (Fin attempts → Fin bits → Fin 2) where
  toFun word attempt bit := word (finProdFinEquiv (attempt, bit))
  invFun words index := words (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2
  left_inv word := by
    funext index
    change word (finProdFinEquiv (finProdFinEquiv.symm index)) = word index
    rw [Equiv.apply_symm_apply]
  right_inv words := by
    funext attempt bit
    change words (finProdFinEquiv.symm (finProdFinEquiv (attempt, bit))).1
      (finProdFinEquiv.symm (finProdFinEquiv (attempt, bit))).2 = words attempt bit
    rw [Equiv.symm_apply_apply]











noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable [Fintype State]





















end
end AFT.FiniteConditionProgram

end

section





/-! # An integer common-denominator evaluator for the exact beta CDF -/
namespace AFT.BetaReference
open scoped BigOperators

/-- A common integer denominator for the exact CDF at a grid point. -/
def integerCDFDenominator (K n M : ℕ) : ℕ := K.factorial*n.factorial*M^(K+n+1)















end AFT.BetaReference

end

section





namespace AFT
end AFT
namespace AFT.BetaReference
end AFT.BetaReference
namespace AFT.BetaReference.integerCDFPrefix
end AFT.BetaReference.integerCDFPrefix
namespace AFT.BetaReference.integerCDFTerm
end AFT.BetaReference.integerCDFTerm
namespace AFT.BetaReference.safeGridValue
end AFT.BetaReference.safeGridValue
namespace AFT.BinaryCDFSampler
end AFT.BinaryCDFSampler


/-! # Checked arithmetic-operation counts for the concrete beta CDF evaluator

The counter records integer additions, multiplications and natural divisions.
It is not a Turing-machine cost model; binary operand bounds are proved
separately in `BetaIntegerArithmetic` and `ActualBetaNumericalBounds`.
-/
namespace AFT.BetaReference

structure CountedInteger where
  value : ℤ
  work : ℕ

namespace CountedInteger

def literal (value : ℤ) : CountedInteger := ⟨value,0⟩

def mul (first second : CountedInteger) : CountedInteger :=
  ⟨first.value*second.value,first.work+second.work+1⟩


def power (value : ℤ) : ℕ → CountedInteger
  | 0 => literal 1
  | exponent+1 => (power value exponent).mul (literal value)

def factorial : ℕ → CountedInteger
  | 0 => literal 1
  | n+1 => (literal (n+1)).mul (factorial n)

@[simp] theorem power_value (value : ℤ) (exponent : ℕ) : (power value exponent).value=value^exponent := by
  induction exponent with
  | zero => simp [power,literal]
  | succ exponent ih => simp only [power,mul,literal,ih,pow_succ]

@[simp] theorem power_work (value : ℤ) (exponent : ℕ) : (power value exponent).work=exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent ih => simp only [power,mul,literal,ih,Nat.add_zero]

@[simp] theorem factorial_value (n : ℕ) : (factorial n).value=n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [factorial,mul,literal,ih,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]

@[simp] theorem factorial_work (n : ℕ) : (factorial n).work=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [factorial,mul,literal,ih,Nat.zero_add]



















def cdfDenominator (K n M : ℕ) : CountedInteger :=
  ((factorial K).mul (factorial n)).mul (power M (K+n+1))

@[simp] theorem cdfDenominator_value (K n M : ℕ) :
    (cdfDenominator K n M).value=integerCDFDenominator K n M := by
  simp only [cdfDenominator,mul,factorial_value,power_value,integerCDFDenominator,Nat.cast_mul,Nat.cast_pow]









end CountedInteger
end AFT.BetaReference

end

section





/-! # The binary beta search with an executable arithmetic counter

The evaluator recomputes the midpoint power at each level and counts the
query's actual arithmetic evaluator, the midpoint addition, and comparison.
-/
namespace AFT.BetaReference

structure CountedNatural where
  value : ℕ
  work : ℕ

namespace CountedNatural



















end CountedNatural
end AFT.BetaReference

end

section







/-! # A bounded executable search for the actual public prime modulus

The program uses trial division and a bounded scan. Its arithmetic counter
is deliberately coarse; no primality oracle is supplied to the executable
program. The result is exactly the prime selected in `Parameters.modulus`.
-/
namespace AFT.ParameterProgram
open BetaReference

structure CountedDecision where
  value : Bool
  work : ℕ

/-- Test divisors `2,...,length+1` by literal natural remainders. -/
def trialDivisors (candidate : ℕ) : ℕ → CountedDecision
  | 0 => ⟨true,0⟩
  | length+1 =>
      let previous := trialDivisors candidate length
      let remainder := candidate%(length+2)
      ⟨previous.value && decide (remainder ≠ 0),previous.work+2⟩

theorem trialDivisors_value (candidate length : ℕ) :
    (trialDivisors candidate length).value=true ↔
      ∀ d,2 ≤ d → d < length+2 → ¬d ∣ candidate := by
  induction length with
  | zero =>
    simp only [trialDivisors]
    constructor
    · intro _ d hlo hhi
      omega
    · intro _
      trivial
  | succ length ih =>
    simp only [trialDivisors,Bool.and_eq_true,decide_eq_true_eq,ih]
    constructor
    · rintro ⟨hprev,hlast⟩ d hlo hhi
      by_cases h : d < length+2
      · exact hprev d hlo h
      · have he : d=length+2 := by omega
        rw [he,Nat.dvd_iff_mod_eq_zero]
        exact hlast
    · intro h
      exact ⟨fun d hlo hhi => h d hlo (by omega),by simpa only [Nat.dvd_iff_mod_eq_zero] using h (length+2) (by omega) (by omega)⟩

@[simp] theorem trialDivisors_work (candidate length : ℕ) :
    (trialDivisors candidate length).work=2*length := by
  induction length with
  | zero => rfl
  | succ length ih => simp only [trialDivisors,ih]; omega

def primeTest (candidate : ℕ) : CountedDecision :=
  if candidate < 2 then ⟨false,1⟩ else
    let result := trialDivisors candidate (candidate-2)
    ⟨result.value,result.work+2⟩

theorem primeTest_value (candidate : ℕ) :
    (primeTest candidate).value=true ↔ candidate.Prime := by
  rw [Nat.prime_def_lt']
  by_cases h : candidate < 2
  · simp only [primeTest,if_pos h,Bool.false_eq_true,false_iff]
    omega
  · simp only [primeTest,if_neg h,trialDivisors_value]
    have he : candidate-2+2=candidate := by omega
    rw [he]
    exact (and_iff_right (by omega : 2 ≤ candidate)).symm



/-- The scan is structurally recursive on the declared finite upper bound.
After finding a witness it retains that same least witness. -/
def boundedLeast (test : ℕ → CountedDecision) : ℕ → CountedNatural
  | 0 => ⟨0,0⟩
  | bound+1 =>
      let previous := boundedLeast test bound
      let checked := test previous.value
      ⟨if checked.value then previous.value else bound+1,previous.work+checked.work+1⟩

theorem boundedLeast_le (test : ℕ → CountedDecision) (bound : ℕ) :
    (boundedLeast test bound).value ≤ bound := by
  induction bound with
  | zero => simp [boundedLeast]
  | succ bound ih => simp only [boundedLeast]; split_ifs <;> omega

theorem boundedLeast_exact (test : ℕ → CountedDecision) (least bound : ℕ)
    (hleast : (test least).value=true)
    (hminimal : ∀ index,index < least → (test index).value=false)
    (hbound : least ≤ bound) : (boundedLeast test bound).value=least := by
  induction bound with
  | zero =>
    have he : least=0 := by omega
    simp only [he,boundedLeast]
  | succ bound ih =>
    by_cases h : least ≤ bound
    · simp only [boundedLeast,ih h,hleast,ite_true]
    · have he : least=bound+1 := by omega
      have hp := boundedLeast_le test bound
      have ht := hminimal (boundedLeast test bound).value (by omega)
      simp only [boundedLeast,ht,Bool.false_eq_true,ite_false,he]

theorem boundedLeast_work_le (test : ℕ → CountedDecision) (bound cost : ℕ)
    (hcost : ∀ index,index ≤ bound → (test index).work ≤ cost) :
    (boundedLeast test bound).work ≤ bound*(cost+1) := by
  induction bound with
  | zero => simp [boundedLeast]
  | succ bound ih =>
    have hp := ih (fun index hi => hcost index (by omega))
    have hq := hcost (boundedLeast test bound).value ((boundedLeast_le test bound).trans (by omega))
    simp only [boundedLeast]
    nlinarith

/-- Every tested property is evaluated from integer operations. -/
def modulusTest (base candidate : ℕ) : CountedDecision :=
  let prime := primeTest candidate
  ⟨prime.value && decide (base < candidate) && decide (candidate ≤ 2*base),prime.work+3⟩

theorem modulusTest_value (base candidate : ℕ) :
    (modulusTest base candidate).value=true ↔
      candidate.Prime ∧ base < candidate ∧ candidate ≤ 2*base := by
  simp only [modulusTest,Bool.and_eq_true,decide_eq_true_eq,primeTest_value,and_assoc]

def modulus (parameter : ℕ) : CountedNatural :=
  let base := CountedInteger.power ((max 2 parameter : ℕ) : ℤ) 40
  let result := boundedLeast (modulusTest base.value.toNat) (2*base.value.toNat)
  ⟨result.value,base.work+result.work+2⟩

 theorem base_value (parameter : ℕ) :
    (CountedInteger.power ((max 2 parameter : ℕ) : ℤ) 40).value.toNat=Parameters.security parameter^40 := by
  rw [CountedInteger.power_value]
  have hh : ((max 2 parameter : ℕ) : ℤ)^40=((max 2 parameter)^40 : ℕ) := by push_cast; rfl
  rw [hh,Int.toNat_natCast]
  rfl

theorem modulus_value (parameter : ℕ) : (modulus parameter).value=Parameters.modulus parameter := by
  simp only [modulus,base_value]
  apply boundedLeast_exact
  · exact (modulusTest_value _ _).mpr (Parameters.modulus_spec parameter)
  · intro index hi
    apply Bool.eq_false_iff.mpr
    intro ht
    have hs := (modulusTest_value _ _).mp ht
    have hmin : Parameters.modulus parameter ≤ index := by
      unfold Parameters.modulus
      exact Nat.find_min' _ hs
    omega
  · exact (Parameters.modulus_bounds parameter).2



end AFT.ParameterProgram

end

section

















namespace AFT
end AFT
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.TVBound
end AFT.FiniteDist.TVBound
namespace AFT.FiniteDist.acceptance
end AFT.FiniteDist.acceptance
namespace AFT.FiniteDist.cappedCondition
end AFT.FiniteDist.cappedCondition
namespace AFT.FiniteDist.conditionalSource
end AFT.FiniteDist.conditionalSource
namespace AFT.FiniteDist.eventCoin
end AFT.FiniteDist.eventCoin
namespace AFT.V7Calibration
end AFT.V7Calibration




/-! # A standalone fair-bit program for the complete actual protected root source -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics FiniteDist FiniteConditionProgram
open scoped BigOperators

/-- The body population is computed by the bounded public prime search. -/
def actualRootPopulationProgram (n : ℕ) : ℕ :=
  (ParameterProgram.modulus n).value*(max 2 n)^20-2*(max 2 n)^30













noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false







end
end AFT.V7Calibration

end

section













/-! # The complete executable integer Gaussian convolution and its actual error -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics FiniteConvolutionProgram FiniteDist
open scoped BigOperators

/-- Every scalar ticket count, including its Gaussian approximation, is
computed from `n`. No real-valued weight is an input to this program. -/
def actualRootTicketConvolution (n count : ℕ) : Result ℕ :=
  actualRootIntegerConvolution n (actualRootTicketCounts n n) count

def actualRootTicketProbability (n count : ℕ) (target : ℤ) : ℚ :=
  (integerLookup (actualRootTicketConvolution n count).data ((3*n^2-1)*count) target : ℕ)/
    (2 : ℚ)^(actualRootTicketBits n n*count)

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local instance actualRootTicketConvolutionFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _







end
end AFT.V7Calibration

end

section




















namespace AFT
end AFT
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.TVBound
end AFT.FiniteDist.TVBound
namespace AFT.FiniteDist.acceptance
end AFT.FiniteDist.acceptance
namespace AFT.FiniteDist.cappedCondition
end AFT.FiniteDist.cappedCondition
namespace AFT.FiniteDist.conditionalSource
end AFT.FiniteDist.conditionalSource
namespace AFT.FiniteDist.eventCoin
end AFT.FiniteDist.eventCoin
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.V7Calibration
end AFT.V7Calibration





/-! # Executable rational queries for the actual one-root marginal -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics FiniteConvolutionProgram FiniteDist
open scoped BigOperators

/-- Both convolution entries and the scalar ticket mass are computed exactly
as rationals. The denominator is one full-root normalizer. -/
def actualRootTicketMarginal (n count : ℕ) (point : Window (3*n^2-1)) : ℚ :=
  (actualRootTicketCounts n n ((windowIndexEquiv _).symm point) : ℚ)/(2 : ℚ)^(actualRootTicketBits n n)*
    actualRootTicketProbability n (count-1) (-(point : ℤ))/actualRootTicketProbability n count 0

/-- The actual population is obtained by the proved bounded prime program. -/
def actualRootMarginalProgram (n : ℕ) (point : Window (3*n^2-1)) : ℚ :=
  actualRootTicketMarginal n (actualRootPopulationProgram n) point

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
local instance actualRootMarginalProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _









end
end AFT.V7Calibration

end

section















/-! # A rational program for the actual root/leg/queue body-blur table -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics FiniteConvolutionProgram Filter
open scoped BigOperators









def windowTicketWeightProgram (squaredWidth : ℚ) (cutoff bits : ℕ) (point : Window cutoff) : ℚ :=
  (windowTicketCounts squaredWidth cutoff bits ((windowIndexEquiv cutoff).symm point) : ℚ)/
    (2 : ℚ)^(windowTicketBits cutoff bits)



noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false
local instance bodyBlurProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

























end
end AFT.V7Calibration

end

section













/-! # Computing the actual safe-body mean from the rational source table -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators



def intervalProbabilityProgram (start : ℤ) (width : ℕ) (point : ℤ) : ℚ :=
  if start ≤ point ∧ point < start+width then (width : ℚ)⁻¹ else 0

def actualSafeMarginProgram (n : ℕ) : ℕ := 20*(max 2 n)^2







noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false





theorem intervalProbabilityProgram_cast (start : ℤ) (width : ℕ) (point : ℤ) :
    (intervalProbabilityProgram start width point : ℝ)=intervalAnchorLaw start width point := by
  unfold intervalProbabilityProgram intervalAnchorLaw
  simp only [anchorInterval,Finset.mem_Ico]
  split_ifs <;> simp only [Rat.cast_inv,Rat.cast_natCast,Rat.cast_zero]











end
end AFT.V7Calibration

end

section













namespace AFT
end AFT
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualPairSourceApproxLaw
end AFT.V7Calibration.actualPairSourceApproxLaw
namespace AFT.V7Calibration.actualPairSourceProgram
end AFT.V7Calibration.actualPairSourceProgram



/-! # Rational computation of the actual shared-source endpoint means -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

def sliceProbabilityProgram (modulus boundary shift color : ℤ) : ℚ :=
  if boundary+max shift 0 ≤ color ∧ color < modulus-boundary+min shift 0 then
    ((modulus-2*boundary-|shift|).toNat : ℚ)⁻¹ else 0

def averagedSliceProgram (modulus boundary start source : ℤ) (width : ℕ) (color : ℤ) : ℚ :=
  ∑ index : Fin width,
    let shift := start+(index.val : ℤ)
    intervalProbabilityProgram start width shift*sliceProbabilityProgram modulus boundary (shift-source) color

def actualBoundaryHalfProgram (constant n : ℕ) : ℤ :=
  (actualSafeMarginProgram n : ℤ)-
    ((3*n^2-1)+(actualLegCutoffProgram constant n-1)+(n^2-1) : ℕ)

def actualAnchorWidthProgram (n : ℕ) : ℕ := (max 2 n)^32













noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
local instance sliceProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- Integer comparisons and the closed slice length compute the original slice law. -/
theorem sliceProbabilityProgram_eq_original (modulus boundary shift color : ℤ) :
    sliceProbabilityProgram modulus boundary shift color =
      if color ∈ TrimmedSlice.slice modulus boundary shift then
        ((TrimmedSlice.slice modulus boundary shift).card : ℚ)⁻¹ else 0 := by
  rw [TrimmedSlice.slice_card]
  simp only [sliceProbabilityProgram,TrimmedSlice.slice,Finset.mem_Ico]

/-- Increasing finite indices enumerate the complete anchor interval exactly once. -/
theorem averagedSliceProgram_eq_sum (modulus boundary start source : ℤ) (width : ℕ) (color : ℤ) :
    averagedSliceProgram modulus boundary start source width color =
      ∑ shift ∈ anchorInterval start width,
        intervalProbabilityProgram start width shift*sliceProbabilityProgram modulus boundary (shift-source) color := by
  unfold averagedSliceProgram
  apply Finset.sum_bij (fun (index : Fin width) _ => start+(index.val : ℤ))
  · intro index _
    simp only [anchorInterval,Finset.mem_Ico]
    have hi := index.isLt
    omega
  · intro first _ second _ h
    apply Fin.ext
    omega
  · intro shift hs
    simp only [anchorInterval,Finset.mem_Ico] at hs
    refine ⟨⟨(shift-start).toNat,by omega⟩,Finset.mem_univ _,?_⟩
    dsimp only
    omega
  · intro index _
    rfl



theorem sliceProbabilityProgram_cast (modulus boundary shift color : ℤ) :
    (sliceProbabilityProgram modulus boundary shift color : ℝ)=TrimmedSlice.law modulus boundary shift color := by
  rw [sliceProbabilityProgram_eq_original]
  unfold TrimmedSlice.law
  split_ifs <;> simp only [Rat.cast_inv,Rat.cast_natCast,Rat.cast_zero]



theorem averagedSliceProgram_cast (modulus boundary start source : ℤ) (width : ℕ) (color : ℤ) :
    (averagedSliceProgram modulus boundary start source width color : ℝ)=
      TrimmedSlice.averagedLaw modulus boundary start source width color := by
  simp only [averagedSliceProgram_eq_sum,Rat.cast_sum,Rat.cast_mul,intervalProbabilityProgram_cast,
    sliceProbabilityProgram_cast,TrimmedSlice.averagedLaw,TrimmedSlice.intervalMixture]





















end
end AFT.V7Calibration

end


