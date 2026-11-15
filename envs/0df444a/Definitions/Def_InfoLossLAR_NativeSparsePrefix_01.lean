-- Prove2me | Definitions.Def_InfoLossLAR_NativeSparsePrefix_01
-- name    : InfoLossLAR_NativeSparsePrefix_01
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T13:18:14.786618+00:00
-- url     : https://prove2.me/theorems/0ce1a552-9785-4185-b5b6-f08a5df012c0
-- title:
--   Local response, Gaussian source, and protected parameter data
-- statement:
--   This package defines finite calibration operators, local tensor and physical block data, Gaussian source weights, activation scales, and protected root and leg parameters for algebraic rounding. The rank-one response associated with a vector $v$, a linear functional $\chi$, and a scalar $\rho$ acts by
--   $$x\longmapsto x+\rho^{-1}\chi(x)v.$$
--   The Gaussian source uses integer weights proportional to $\exp(-\pi z^2/\sigma^2)$, with source width and clipping parameters stored separately. These interfaces provide the common finite data for the subsequent response and transport theorems. Supporting proofs are retained only where needed to construct or interpret these objects.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0; Lean source modules AFT/Inverse.lean, AFT/Calibration.lean, AFT/LocalResponse.lean, AFT/FockGaussian.lean, AFT/HistogramTail.lean, AFT/TensorFock.lean, AFT/NonlinearFock.lean, AFT/SelectionBound.lean, AFT/BlockDensity.lean, AFT/LocalTensors.lean, AFT/PhysicalBlockTensors.lean, AFT/ActivatedPair.lean, AFT/Negligible.lean, AFT/GaussianSource.lean, AFT/GaussianTail.lean, AFT/RootSlice.lean, AFT/ClippedSource.lean, AFT/ActivationParameters.lean, AFT/ActualLegCutoffProgram.lean, AFT/MixedActivity.lean, AFT/Anchor.lean, AFT/FinitePrimaryInverse.lean, AFT/Parameters.lean. Source bodies and declaration spans are recorded in native_sparse_prefix/manifest.json; SHA256 d3c2209b94a7d427ab20574a3af2b73e0c9ddefc853f51cd90e9b1f39a5097f3. Repackaging of identical data declarations, with 4163 public types matched to native source and 7722 origin declarations recursively audited for standard logical axioms only.

import Mathlib
import Definitions.Def_InfoLossLAR_Native_AFT_BlockFock
import Definitions.Def_InfoLossLAR_Native_AFT_Hoeffding

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


