-- Prove2me | Definitions.Def_InfoLossLAR_NativeBundle_05
-- name    : InfoLossLAR_NativeBundle_05
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T11:10:46.438708+00:00
-- url     : https://prove2.me/theorems/9d5616ff-758e-4339-957a-2f6ab2b92198
-- title:
--   Current control families and truncated coefficient algebra
-- statement:
--   For a fixed order $R$, this package defines the current primary and body reference controls, public charge and Fourier objects, physical block data, and the finite algebra of canonical coefficient families.
--
--   The arity index set and corresponding family have the form
--   $$\mathcal A_R=\{(r,s):r,s\in\mathbb N,\ r+s\le R\},\qquad
--   \mathcal F_R=\prod_{(r,s)\in\mathcal A_R}\mathcal K_{r,s},$$
--   where $\mathcal K_{r,s}$ is the appropriate canonical kernel fiber for the chosen primary and body reference laws. The zero-arity fiber stores the scalar coefficient, and multiplication is the actual truncated convolution of disjoint-slot kernel products.
--
--   This finite data representation supports the subsequent stability and calibration theorems without replacing the response algebra by an abstract assumed operation.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0, native lean source modules: lean/CurrentAFT/BackgroundCertificates.lean, lean/CurrentAFT/ProposalSymmetry.lean, lean/CurrentAFT/FirstHistogram.lean, lean/CurrentAFT/GaussianHeights.lean, lean/CurrentAFT/LocalReferenceEnergy.lean, lean/CurrentAFT/ActualPublicLegSeed.lean, lean/CurrentAFT/BoundedClipping.lean, lean/CurrentAFT/Conditioning.lean, lean/CurrentAFT/PublicCharge.lean, lean/CurrentAFT/ZeroSumTarget.lean, lean/CurrentAFT/ChargedEndpoint.lean, lean/CurrentAFT/PublicCore.lean, lean/CurrentAFT/BackgroundTranslations.lean, lean/CurrentAFT/BackgroundRates.lean, lean/CurrentAFT/AmbientFourier.lean, lean/CurrentAFT/ProtectedCycle.lean, lean/CurrentAFT/PathLikelihood.lean, lean/CurrentAFT/ProtectedCycleResponse.lean, lean/CurrentAFT/CycleSelections.lean, lean/CurrentAFT/CycleMatching.lean, lean/CurrentAFT/CycleMeanMGF.lean, lean/CurrentAFT/NormalizedMeanAlgebra.lean, lean/CurrentAFT/UniformBodyProfiles.lean, lean/CurrentAFT/ActualCycleMeanMGF.lean, lean/CurrentAFT/PhysicalSynthesis.lean, lean/CurrentAFT/PairedReferenceEnergy.lean, lean/CurrentAFT/ReferenceMarginals.lean, lean/CurrentAFT/PositiveFirstCoefficient.lean, lean/CurrentAFT/ActualBlockFock.lean, lean/CurrentAFT/ControlProduct.lean, lean/CurrentAFT/ControlCoherence.lean, lean/CurrentAFT/ControlNorm.lean, lean/CurrentAFT/GradedControlAlgebra.lean, lean/CurrentAFT/GradedInverse.lean, lean/CurrentAFT/GradedControlNorm.lean, lean/CurrentAFT/GradedControlStability.lean, lean/CurrentAFT/BackgroundFamilies.lean, lean/CurrentAFT/BackgroundLinear.lean, lean/CurrentAFT/ConditionalPairMean.lean, lean/CurrentAFT/PrimaryPairInverse.lean, lean/CurrentAFT/PrimaryTensorInverse.lean, lean/CurrentAFT/PrimaryMassFamilies.lean, lean/CurrentAFT/ConditionalPairLinear.lean, lean/CurrentAFT/PairSmoothing.lean, lean/CurrentAFT/DiffusePair.lean, lean/CurrentAFT/DiffusePairBounds.lean, lean/CurrentAFT/PairReindex.lean. Migrated source units selected by the Lean declaration and syntax oracles; exact source body hashes and original module paths recorded in Integration9_9/provenance/full_project_extraction/native_definition_bundles/manifest.json. Bundle SHA256 945714cdea8b389b27e45eb8efa5dde6d165ae0f92f3583df1e84769ed32e8e5.

import Definitions.Def_InfoLossLAR_NativeBundle_01
import Definitions.Def_InfoLossLAR_NativeBundle_02
import Definitions.Def_InfoLossLAR_NativeBundle_04
import Definitions.Def_InfoLossLAR_Native_AFT_FiniteProbability
import Definitions.Def_InfoLossLAR_Native_AFT_Hoeffding
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

section






namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.BodyResponse
end CurrentAFT.BodyResponse
namespace CurrentAFT.BodyResponse.jointBodyInputEnergy
end CurrentAFT.BodyResponse.jointBodyInputEnergy
namespace CurrentAFT.BodyResponse.jointBodyProfile
end CurrentAFT.BodyResponse.jointBodyProfile




/-!
# Concrete stable atoms for the current free-body background

The primary fringe certificate and the safe-centered body certificate
are built from the actual current laws. Explicit current parameter bounds
give quantitative decay of their genuine density L2 norms. Their leading
responses sum exactly to the actual root-convolved center-law deviation.
No background smallness or response stability is assumed in this file.
-/

namespace CurrentAFT.BackgroundCertificates

open AFT DiffuseProfiles ProposalPrimary FringeCertificate
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth
  Parameters.bodySize Parameters.legCount Parameters.safeMargin DiffuseProfiles.activation
  DiffuseProfiles.actualSeedLaw primaryProfile safeLaw bodyLaw

abbrev Palette (security : ℕ) := Fin (Parameters.modulus security)

theorem fringeMass_decay (security : ℕ) :
    fringeMass security ≤ 1 / (Parameters.base security : ℝ) ^ 62 := by
  have hb := FirstResponse.base_pos security
  have hq := FirstResponse.modulus_pos security
  have hstrip : 4 * (Parameters.safeMargin security : ℝ) < Parameters.modulus security := by
    exact_mod_cast safe_clearance security
  have hqLower : 65536 * (Parameters.base security : ℝ) ^ 64 ≤ Parameters.modulus security := by
    exact_mod_cast (Parameters.modulus_bounds security).1
  have hmargin : (Parameters.safeMargin security : ℝ) = 3 * (Parameters.base security : ℝ) ^ 2 := by
    simp only [Parameters.safeMargin, Parameters.sourceCutoff, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  calc
    _ ≤ (2 * Parameters.safeMargin security : ℝ) / ((Parameters.modulus security : ℝ) / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    _ = (12 * (Parameters.base security : ℝ) ^ 2) / Parameters.modulus security := by rw [hmargin]; ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ hq (pow_pos hb _)).mpr
      have hsmall : 12 * (Parameters.base security : ℝ) ^ 64 ≤ Parameters.modulus security := by
        nlinarith only [hqLower, pow_nonneg hb.le 64]
      nlinarith only [hsmall]

theorem compensation_decay (security : ℕ) :
    compensation security ≤ 1 / (Parameters.base security : ℝ) ^ 32 := by
  have hb := FirstResponse.base_pos security
  have hq := FirstResponse.modulus_pos security
  have hqLower : 65536 * (Parameters.base security : ℝ) ^ 64 ≤ Parameters.modulus security := by
    exact_mod_cast (Parameters.modulus_bounds security).1
  calc
    _ ≤ (Parameters.legCount security : ℝ) / Parameters.bodySize security := compensation_le_leg_body security
    _ = (Parameters.base security : ℝ) ^ 32 / Parameters.modulus security := by
      simp only [Parameters.legCount_eq, Parameters.bodySize_eq, Nat.cast_pow, Nat.cast_mul]
      field_simp
    _ ≤ _ := by
      apply (div_le_div_iff₀ hq (pow_pos hb _)).mpr
      have hsmall : (Parameters.base security : ℝ) ^ 64 ≤ Parameters.modulus security := by
        nlinarith only [hqLower, pow_nonneg hb.le 64]
      nlinarith only [hsmall]

theorem bodyDeviation_budget_decay (security : ℕ) :
    4 * fringeMass security ^ 2 + 2 * compensation security * fringeMass security ≤
      6 / (Parameters.base security : ℝ) ^ 94 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (show 1 ≤ Parameters.base security by
    have := Parameters.base_ge_two security; omega)
  have hm := fringeMass_decay security
  have hc := compensation_decay security
  have hmsq := pow_le_pow_left₀ (fringeMass_nonneg security) hm 2
  have hproduct := mul_le_mul hc hm (fringeMass_nonneg security) (by positivity)
  have hpower : 1 / (Parameters.base security : ℝ) ^ 124 ≤ 1 / (Parameters.base security : ℝ) ^ 94 :=
    one_div_le_one_div_of_le (pow_pos hb _) (pow_le_pow_right₀ hb1 (by omega))
  have hmsqBound : fringeMass security ^ 2 ≤ 1 / (Parameters.base security : ℝ) ^ 124 :=
    hmsq.trans_eq (by rw [div_pow, one_pow, ← pow_mul])
  have hproductBound : compensation security * fringeMass security ≤
      1 / (Parameters.base security : ℝ) ^ 94 :=
    hproduct.trans_eq (by ring)
  calc
    _ = 4 * fringeMass security ^ 2 + 2 * (compensation security * fringeMass security) := by ring
    _ ≤ 4 * (1 / (Parameters.base security : ℝ) ^ 94) +
        2 * (1 / (Parameters.base security : ℝ) ^ 94) :=
      add_le_add (mul_le_mul_of_nonneg_left (hmsqBound.trans hpower) (by norm_num))
        (mul_le_mul_of_nonneg_left hproductBound (by norm_num))
    _ = _ := by ring

theorem primaryCertificateDensity_square_decay (security : ℕ) :
    (∑ color, (primaryLaw security).weight color * primaryCertificateDensity security color ^ 2) ≤
      384 / (Parameters.base security : ℝ) ^ 92 := by
  have hb := FirstResponse.base_pos security
  have hbudget0 : 0 ≤ 4 * fringeMass security ^ 2 + 2 * compensation security * fringeMass security :=
    add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (mul_nonneg (mul_nonneg (by norm_num) (compensation_nonneg security)) (fringeMass_nonneg security))
  have hinv := FirstResponse.activation_inverse_le security
  have hinvsq := pow_le_pow_left₀ (one_div_pos.mpr (activation_pos security)).le hinv 2
  have hcoefficient : 4 / activation security ^ 2 ≤ 64 * (Parameters.base security : ℝ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hinvsq (show (0 : ℝ) ≤ 4 by norm_num)
    convert h using 1 <;> first | rfl | ring
  calc
    _ ≤ (4 / activation security ^ 2) *
        (4 * fringeMass security ^ 2 + 2 * compensation security * fringeMass security) :=
      primaryCertificateDensity_square_bound security
    _ ≤ (64 * (Parameters.base security : ℝ) ^ 2) * (6 / (Parameters.base security : ℝ) ^ 94) :=
      mul_le_mul hcoefficient (bodyDeviation_budget_decay security) hbudget0 (by positivity)
    _ = _ := by field_simp; ring

/-- Explicit decay is stronger than the coarse `O(base^-31)` budget. -/
theorem primaryCertificateDensity_norm_decay (security : ℕ) :
    Real.sqrt (∑ color, (primaryLaw security).weight color * primaryCertificateDensity security color ^ 2) ≤
      20 / (Parameters.base security : ℝ) ^ 46 := by
  have hb := FirstResponse.base_pos security
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hden : (20 / (Parameters.base security : ℝ) ^ 46) ^ 2 =
      400 / (Parameters.base security : ℝ) ^ 92 := by ring
  rw [hden]
  exact (primaryCertificateDensity_square_decay security).trans
    (div_le_div_of_nonneg_right (by norm_num) (pow_nonneg hb.le _))



def bodyCertificateProfile (security : ℕ) : Palette security → ℝ :=
  fun center => (centerLaw security).weight center - (safeLaw security).weight center

def bodyCertificateDensity (security : ℕ) (center : Palette security) : ℝ :=
  bodyCertificateProfile security center / (centerLaw security).weight center

theorem bodyCertificateProfile_mass (security : ℕ) : ∑ center, bodyCertificateProfile security center = 0 := by
  simp only [bodyCertificateProfile, Finset.sum_sub_distrib, FiniteDist.sum_one, sub_self]



theorem bodyCertificateProfile_zero_of_center_zero (security : ℕ) (center : Palette security)
    (hzero : (centerLaw security).weight center = 0) : bodyCertificateProfile security center = 0 := by
  have hbound := (centerProfile_bounds security center).1
  change (safeLaw security).weight center / 2 ≤ (centerLaw security).weight center at hbound
  rw [hzero] at hbound
  have hsafe : (safeLaw security).weight center = 0 := by
    linarith [(safeLaw security).nonneg center]
  simp only [bodyCertificateProfile, hzero, hsafe, sub_self]

theorem bodyCertificateDensity_profile (security : ℕ) :
    (fun center => (centerLaw security).weight center * bodyCertificateDensity security center) =
      bodyCertificateProfile security := by
  funext center
  by_cases hz : (centerLaw security).weight center = 0
  · simp only [hz, zero_mul, bodyCertificateProfile_zero_of_center_zero security center hz]
  · unfold bodyCertificateDensity
    field_simp

theorem bodyCertificateDensity_centered (security : ℕ) :
    (∑ center, (centerLaw security).weight center * bodyCertificateDensity security center) = 0 := by
  rw [bodyCertificateDensity_profile]
  exact bodyCertificateProfile_mass security



theorem dominated_profile_square_le (security : ℕ) (reference profile : Palette security → ℝ)
    (coefficient : ℝ) (hcoefficient : 0 ≤ coefficient) (href : ∀ color, 0 ≤ reference color)
    (hprofile : ∀ color, 0 ≤ profile color)
    (hdomination : ∀ color, profile color ≤ coefficient * reference color) :
    profileSquareNorm reference profile ≤ coefficient * ∑ color, profile color := by
  unfold profileSquareNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro color _
  by_cases hz : reference color = 0
  · rw [hz, div_zero]
    exact mul_nonneg hcoefficient (hprofile color)
  · have hp : 0 < reference color := lt_of_le_of_ne (href color) (Ne.symm hz)
    apply (div_le_iff₀ hp).mpr
    have h := mul_le_mul_of_nonneg_right (hdomination color) (hprofile color)
    nlinarith only [h]

theorem safeLaw_center_square_le_two (security : ℕ) :
    profileSquareNorm (centerLaw security).weight (safeLaw security).weight ≤ 2 := by
  have hdom (color : Palette security) : (safeLaw security).weight color ≤
      2 * (centerLaw security).weight color := by
    have h := (centerProfile_bounds security color).1
    change (safeLaw security).weight color / 2 ≤ (centerLaw security).weight color at h
    linarith
  simpa only [FiniteDist.sum_one, mul_one] using dominated_profile_square_le security
    (centerLaw security).weight (safeLaw security).weight 2 (by norm_num)
    (centerLaw security).nonneg (safeLaw security).nonneg hdom

theorem anchorPrimaryMean_center_square_le (security : ℕ) :
    profileSquareNorm (centerLaw security).weight (anchorPrimaryMean security) ≤ 256 / activation security := by
  have ha := activation_pos security
  have hdom (color : Palette security) : anchorPrimaryMean security color ≤
      (256 / activation security) * (centerLaw security).weight color := by
    have h := PairedResponse.activated_anchor_center_comparison security color
    have heq : (256 / activation security) * (centerLaw security).weight color =
        (256 * (centerLaw security).weight color) / activation security := by ring
    rw [heq]
    apply (le_div_iff₀ ha).mpr
    nlinarith only [h]
  simpa only [anchorPrimaryMean_mass, mul_one] using dominated_profile_square_le security
    (centerLaw security).weight (anchorPrimaryMean security) (256 / activation security)
    (by positivity) (centerLaw security).nonneg (anchorPrimaryMean_nonneg security) hdom

theorem bodyCertificateProfile_formula (security : ℕ) :
    bodyCertificateProfile security = compensation security •
      ((safeLaw security).weight - anchorPrimaryMean security) := by
  have hanchor (color : Palette security) : (anchorPrimaryLaw security).weight color =
      anchorPrimaryMean security color := by
    simp only [anchorPrimaryLaw, FiniteDist.mix_weight, anchorPrimaryMean]
    apply Finset.sum_congr rfl
    intro primary _
    ring
  funext color
  simp only [bodyCertificateProfile, centerLaw, centerProfile, hanchor, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

theorem center_profile_sub_square_le_two (security : ℕ) (first second : Palette security → ℝ) :
    profileSquareNorm (centerLaw security).weight (first - second) ≤
      2 * profileSquareNorm (centerLaw security).weight first +
        2 * profileSquareNorm (centerLaw security).weight second := by
  have hpoint (color : Palette security) : (first color - second color) ^ 2 / (centerLaw security).weight color ≤
      2 * (first color ^ 2 / (centerLaw security).weight color) +
        2 * (second color ^ 2 / (centerLaw security).weight color) := by
    have hscalar : (first color - second color) ^ 2 ≤ 2 * first color ^ 2 + 2 * second color ^ 2 := by
      nlinarith [sq_nonneg (first color + second color)]
    exact (div_le_div_of_nonneg_right hscalar ((centerLaw security).nonneg color)).trans_eq (by ring)
  simpa only [profileSquareNorm, Pi.sub_apply, Finset.sum_add_distrib, ← Finset.mul_sum] using
    Finset.sum_le_sum (fun color (_ : color ∈ Finset.univ) => hpoint color)

theorem bodyCertificateDensity_square_bound (security : ℕ) :
    (∑ center, (centerLaw security).weight center * bodyCertificateDensity security center ^ 2) ≤
      compensation security ^ 2 * (4 + 512 / activation security) := by
  have hdensity : (∑ center, (centerLaw security).weight center * bodyCertificateDensity security center ^ 2) =
      profileSquareNorm (centerLaw security).weight (bodyCertificateProfile security) := densityScore_square _ _
  rw [hdensity, bodyCertificateProfile_formula, profileSquareNorm_smul]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg (compensation security))
  have h := center_profile_sub_square_le_two security (safeLaw security).weight (anchorPrimaryMean security)
  have hs := safeLaw_center_square_le_two security
  have ha := anchorPrimaryMean_center_square_le security
  calc
    _ ≤ 2 * profileSquareNorm (centerLaw security).weight (safeLaw security).weight +
        2 * profileSquareNorm (centerLaw security).weight (anchorPrimaryMean security) := h
    _ ≤ 2 * 2 + 2 * (256 / activation security) :=
      add_le_add (mul_le_mul_of_nonneg_left hs (by norm_num)) (mul_le_mul_of_nonneg_left ha (by norm_num))
    _ = _ := by ring

theorem bodyCertificateDensity_square_decay (security : ℕ) :
    (∑ center, (centerLaw security).weight center * bodyCertificateDensity security center ^ 2) ≤
      4096 / (Parameters.base security : ℝ) ^ 62 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (show 1 ≤ Parameters.base security by
    have := Parameters.base_ge_two security; omega)
  have hc := pow_le_pow_left₀ (compensation_nonneg security) (compensation_decay security) 2
  have hfactor : 4 + 512 / activation security ≤ 4096 * (Parameters.base security : ℝ) ^ 2 := by
    have hinv := mul_le_mul_of_nonneg_left (FirstResponse.activation_inverse_le security)
      (show (0 : ℝ) ≤ 512 by norm_num)
    calc
      _ = 4 + 512 * (1 / activation security) := by ring
      _ ≤ 4 + 512 * (4 * (Parameters.base security : ℝ)) := add_le_add le_rfl hinv
      _ ≤ _ := by nlinarith only [hb1, sq_nonneg ((Parameters.base security : ℝ) - 1)]
  have hfactor0 : 0 ≤ 4 + 512 / activation security := by have := activation_pos security; positivity
  calc
    _ ≤ compensation security ^ 2 * (4 + 512 / activation security) := bodyCertificateDensity_square_bound security
    _ ≤ (1 / (Parameters.base security : ℝ) ^ 32) ^ 2 * (4096 * (Parameters.base security : ℝ) ^ 2) :=
      mul_le_mul hc hfactor hfactor0 (sq_nonneg _)
    _ = _ := by field_simp

theorem bodyCertificateDensity_norm_decay (security : ℕ) :
    Real.sqrt (∑ center, (centerLaw security).weight center * bodyCertificateDensity security center ^ 2) ≤
      64 / (Parameters.base security : ℝ) ^ 31 := by
  have hb := FirstResponse.base_pos security
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hden : (64 / (Parameters.base security : ℝ) ^ 31) ^ 2 =
      4096 / (Parameters.base security : ℝ) ^ 62 := by ring
  rw [hden]
  exact bodyCertificateDensity_square_decay security

/-- Root-marginal convolution is the actual mixture of cyclic palette
equivalences induced by the independent protected edge difference. -/
def rootConvolutionProfile (security : ℕ) (profile : Palette security → ℝ) : Palette security → ℝ :=
  fun output => ∑ seed, (actualSeedLaw security).weight seed *
    profile ((shiftEquiv security (actualBlur security seed)).symm output)

def convolvedCenterLaw (security : ℕ) : FiniteDist (Palette security) :=
  (actualSeedLaw security).mix (fun seed => (centerLaw security).map
    (shiftEquiv security (actualBlur security seed)))

def bodyLeadingResponse (security : ℕ) (density : Palette security → ℝ) : Palette security → ℝ :=
  rootConvolutionProfile security (fun center => (centerLaw security).weight center * density center)

theorem bodyLaw_false_weight (security : ℕ) (output : Palette security) :
    (bodyLaw security false).weight output = rootConvolutionProfile security (safeLaw security).weight output := by
  simp only [bodyLaw, FiniteDist.mix_weight, FiniteDist.map_equiv_weight,
    Bool.false_eq_true, if_false, add_zero, rootConvolutionProfile]

theorem convolvedCenterLaw_weight (security : ℕ) (output : Palette security) :
    (convolvedCenterLaw security).weight output = rootConvolutionProfile security (centerLaw security).weight output := by
  simp only [convolvedCenterLaw, FiniteDist.mix_weight, FiniteDist.map_equiv_weight, rootConvolutionProfile]







end

end CurrentAFT.BackgroundCertificates

end

section









/-!
# Reflection symmetry and the fair actual inward-anchor sign

The reflection acts simultaneously on the three actual protected Gaussian
scalars. It preserves their joint product weight and reverses both the
public blur and the protected second input. The diffuse profiles and cyclic
body profiles are then reflected before applying the current primary
balancing formula. No frozen-V7 primary law or parameter family is used.

The anchor's direction uses the actual midpoint fair coin. Its exact fair
law is proved from the reflection of the actual constructed primary law,
not supplied as a sign-mixture assumption.
-/

namespace CurrentAFT.ProposalSymmetry

open AFT DiffuseProfiles ProposalPrimary
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth
  Parameters.sourceCutoff Parameters.safeMargin DiffuseProfiles.activation

def seedNegate (security : ℕ) : ActualSeed security ≃ ActualSeed security :=
  ((GaussianSource.windowNegateEquiv (edgeCutoff security)).prodCongr
    (GaussianSource.windowNegateEquiv (edgeCutoff security))).prodCongr
      (GaussianSource.windowNegateEquiv (Parameters.sourceCutoff security - 1))















def shiftColor (modulus : ℕ) [NeZero modulus] (shift : ℤ) : Fin modulus :=
  (ZMod.finEquiv modulus).symm (shift : ZMod modulus)



























def directionLaw (security : ℕ) : FiniteDist Bool :=
  ((primaryLaw security).prod (FiniteDist.uniform Bool)).map
    (fun input => InwardAnchor.positiveDirection security input.1 input.2)







end

end CurrentAFT.ProposalSymmetry

end

section














/-!
# The first histogram of the actual protected leg reference experiment

The reference law below retains the protected second scalar beside the
ordered endpoint pair. The diffuse law is the true integer trimmed slice,
with its varying denominator. The marked companion uses that same second
scalar with a minus sign, together with the independent actual public blur.
Only laws of outputs are constructed here. Implementing them by one public
law of local affine charts is a separate proof obligation.
-/

namespace CurrentAFT.FirstHistogram

open AFT DiffuseProfiles ProposalPrimary PairedResponse
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  actualSeedLaw actualProfile activation primaryLaw centerLaw InwardAnchor.smoothedAnchorLaw

abbrev Palette (security : ℕ) := Fin (Parameters.modulus security)
abbrev Pair (security : ℕ) := Palette security × Palette security
abbrev Scalar (security : ℕ) := InwardAnchor.ScalarSample security
abbrev JointOutput (security : ℕ) := Scalar security × Pair security

 theorem expectation_mix {Input Output : Type*} [Fintype Input] [Fintype Output]
    (law : FiniteDist Input) (kernel : Input → FiniteDist Output) (value : Output → ℝ) :
    (law.mix kernel).expectation value = law.expectation (fun input => (kernel input).expectation value) := by
  simp only [FiniteDist.expectation, FiniteDist.mix_weight, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_assoc]

def atom {Color : Type*} [DecidableEq Color] (first second : Color) : ℝ :=
  if first = second then 1 else 0

 theorem expectation_atom {Color : Type*} [Fintype Color] [DecidableEq Color]
    (law : FiniteDist Color) (color : Color) : law.expectation (fun input => atom input color) = law.weight color := by
  classical
  simp [FiniteDist.expectation, atom, mul_ite]

def endpointHistogram (security : ℕ) (law : FiniteDist (JointOutput security)) (output : Palette security) : ℝ :=
  law.expectation (fun sample => atom sample.2.1 output + atom sample.2.2 output)

 theorem diffuse_clearance (security : ℕ) :
    2 + (2 * (Parameters.anchorWidth security : ℤ) + ((Parameters.sourceCutoff security : ℤ) - 1)) +
        ((Parameters.sourceCutoff security : ℤ) - 1) < Parameters.modulus security := by
  have h := deletion_clearance security
  simp only [deletion] at h
  omega

/-- A fixed protected seed still retains the same second scalar in the
integer pair sum. The uniform offset ranges over the printed signed
anchor interval. -/
def diffuseSeedPair (security : ℕ) (positive : Bool) (seed : ActualSeed security) : FiniteDist (Pair security) :=
  TrimmedSlice.mixedPairDistribution (Parameters.modulus security) 1
    (2 * (Parameters.anchorWidth security : ℤ) + ((Parameters.sourceCutoff security : ℤ) - 1))
    ((Parameters.sourceCutoff security : ℤ) - 1) (Parameters.anchorWidth security)
    (InwardAnchor.anchorWidth_pos security).ne'
    (fun _ : Unit => intervalStart positive (Parameters.anchorWidth security) (actualBlur security seed))
    (fun _ : Unit => actualSecond security seed) (FiniteDist.uniform Unit) (by norm_num)
    (fun _ _ hin => interval_bound positive _ _ _ _ (actualBlur_bound security seed) hin)
    (fun _ => actualSecond_bound security seed) (diffuse_clearance security)

theorem diffuseSeedPair_weight (security : ℕ) (positive : Bool) (seed : ActualSeed security)
    (first second : Palette security) :
    (diffuseSeedPair security positive seed).weight (first, second) =
      TrimmedSlice.averagedPair (Parameters.modulus security) 1
        (intervalStart positive (Parameters.anchorWidth security) (actualBlur security seed))
        (actualSecond security seed) (Parameters.anchorWidth security) first second := by
  simp [diffuseSeedPair, TrimmedSlice.mixedPairDistribution, TrimmedSlice.mixedPair]

theorem diffuseSeedPair_first (security : ℕ) (positive : Bool) (seed : ActualSeed security)
    (output : Palette security) :
    (diffuseSeedPair security positive seed).expectation (fun pair => atom pair.1 output) =
      TrimmedSlice.averagedLaw (Parameters.modulus security) 1
        (intervalStart positive (Parameters.anchorWidth security) (actualBlur security seed))
        (actualSecond security seed) (Parameters.anchorWidth security) output.val := by
  classical
  simp only [FiniteDist.expectation, Fintype.sum_prod_type, diffuseSeedPair_weight]
  rw [Finset.sum_comm]
  simp only [atom, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold TrimmedSlice.averagedPair TrimmedSlice.averagedLaw TrimmedSlice.intervalMixture
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro offset _
  rw [← Finset.mul_sum, TrimmedSlice.orderedPairSlice_marginal _ _ _ (by norm_num)]

theorem diffuseSeedPair_second (security : ℕ) (positive : Bool) (seed : ActualSeed security)
    (output : Palette security) :
    (diffuseSeedPair security positive seed).expectation (fun pair => atom pair.2 output) =
      TrimmedSlice.averagedLaw (Parameters.modulus security) 1
        (intervalStart positive (Parameters.anchorWidth security) (actualBlur security seed))
        (actualSecond security seed) (Parameters.anchorWidth security) output.val := by
  classical
  have hsymm (first second : Palette security) :
      (diffuseSeedPair security positive seed).weight (first, second) =
        (diffuseSeedPair security positive seed).weight (second, first) := by
    rw [diffuseSeedPair_weight, diffuseSeedPair_weight]
    simp only [TrimmedSlice.averagedPair, TrimmedSlice.orderedPairSlice_symmetric]
  rw [← diffuseSeedPair_first security positive seed output]
  simp only [FiniteDist.expectation, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  rw [hsymm]

/-- The actual diffuse reference keeps the source increment beside the
pair. Its direction reads the primary color and the fresh midpoint coin. -/
def diffuseReferenceLaw (security : ℕ) (primary : Palette security) : FiniteDist (JointOutput security) :=
  (FiniteDist.uniform Bool).mix (fun coin =>
    (actualSeedLaw security).mix (fun seed =>
      (diffuseSeedPair security (InwardAnchor.positiveDirection security primary coin) seed).map
        (fun pair => (seed.2, pair))))

def diffuseMarginal (security : ℕ) (primary output : Palette security) : ℝ :=
  (FiniteDist.uniform Bool).expectation (fun coin =>
    actualProfile security (InwardAnchor.positiveDirection security primary coin) output)

theorem diffuseReference_histogram (security : ℕ) (primary output : Palette security) :
    endpointHistogram security (diffuseReferenceLaw security primary) output =
      2 * diffuseMarginal security primary output := by
  unfold endpointHistogram diffuseReferenceLaw
  rw [expectation_mix]
  simp_rw [expectation_mix, FiniteDist.expectation_map, Function.comp_def,
    FiniteDist.expectation_add, diffuseSeedPair_first, diffuseSeedPair_second]
  unfold diffuseMarginal actualProfile profile TrimmedSlice.mixedLaw
  simp only [FiniteDist.expectation]
  ring

theorem diffuse_histogram_decomposition (security : ℕ) (primary output : Palette security) :
    2 * (1 - activation security) * diffuseMarginal security primary output =
      2 * (1 - activation security) * diffuseMean security output +
        signProfile security output * FirstResponse.anchorSign security primary := by
  unfold diffuseMarginal
  simp only [FiniteDist.expectation, FiniteDist.uniform_weight, Fintype.card_bool,
    Nat.cast_ofNat, Fintype.sum_bool]
  by_cases hl : 2 * primary.val < Parameters.modulus security - 1
  · simp only [InwardAnchor.positiveDirection, FirstResponse.anchorSign, hl, if_true]
    unfold diffuseMean signProfile
    ring
  · by_cases hh : Parameters.modulus security - 1 < 2 * primary.val
    · simp only [InwardAnchor.positiveDirection, FirstResponse.anchorSign, hl, hh, if_false, if_true]
      unfold diffuseMean signProfile
      ring
    · simp only [InwardAnchor.positiveDirection, FirstResponse.anchorSign, hl, hh, if_false]
      unfold diffuseMean signProfile
      ring

 theorem negativeSecond_bound (security : ℕ) (seed : ActualSeed security) :
    |-(actualSecond security seed)| ≤ (Parameters.sourceCutoff security : ℤ) - 1 := by
  simpa only [abs_neg] using actualSecond_bound security seed

/-- Activation fixes the marked endpoint and preserves the same second
source, with its negative sign in the companion. Public blur is sampled
independently from the actual edge-difference law. -/
def markedReferenceLaw (security : ℕ) (primary : Palette security) : FiniteDist (JointOutput security) :=
  (actualSeedLaw security).mix (fun seed =>
    (InwardAnchor.shiftedAnchorLaw security primary (-actualSecond security seed)
      (negativeSecond_bound security seed)).map (fun companion =>
        (seed.2, (primary, shiftEquiv security (actualBlur security seed) companion))))

def markedCompanion (security : ℕ) (primary output : Palette security) : ℝ :=
  (actualSeedLaw security).expectation (fun seed =>
    ((InwardAnchor.shiftedAnchorLaw security primary (-actualSecond security seed)
      (negativeSecond_bound security seed)).map
      (shiftEquiv security (actualBlur security seed))).weight output)

theorem markedReference_histogram (security : ℕ) (primary output : Palette security) :
    endpointHistogram security (markedReferenceLaw security primary) output =
      atom primary output + markedCompanion security primary output := by
  unfold endpointHistogram markedReferenceLaw markedCompanion
  rw [expectation_mix]
  simp_rw [FiniteDist.expectation_map, Function.comp_def, FiniteDist.expectation_add,
    FiniteDist.expectation_const]
  simp only [FiniteDist.expectation]
  congr 1
  apply Finset.sum_congr rfl
  intro seed _
  congr 1
  change (InwardAnchor.shiftedAnchorLaw security primary (-actualSecond security seed) _).expectation
      (fun companion => atom (shiftEquiv security (actualBlur security seed) companion) output) = _
  rw [← expectation_atom ((InwardAnchor.shiftedAnchorLaw security primary (-actualSecond security seed)
    (negativeSecond_bound security seed)).map (shiftEquiv security (actualBlur security seed))) output]
  rw [FiniteDist.expectation_map]
  rfl

/-- The protected reference mixture after averaging the activation event.
Both branches retain the same second-source marginal. -/
def referenceLaw (security : ℕ) (primary : Palette security) : FiniteDist (JointOutput security) where
  weight sample := (1 - activation security) * (diffuseReferenceLaw security primary).weight sample +
    activation security * (markedReferenceLaw security primary).weight sample
  nonneg sample := add_nonneg
    (mul_nonneg (by linarith [activation_le_half security]) ((diffuseReferenceLaw security primary).nonneg sample))
    (mul_nonneg (activation_pos security).le ((markedReferenceLaw security primary).nonneg sample))
  sum_one := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, FiniteDist.sum_one, FiniteDist.sum_one]
    ring

theorem reference_histogram (security : ℕ) (primary output : Palette security) :
    endpointHistogram security (referenceLaw security primary) output =
      activation security * atom primary output + activation security * markedCompanion security primary output +
        2 * (1 - activation security) * diffuseMean security output +
          signProfile security output * FirstResponse.anchorSign security primary := by
  have hmix : endpointHistogram security (referenceLaw security primary) output =
      (1 - activation security) * endpointHistogram security (diffuseReferenceLaw security primary) output +
        activation security * endpointHistogram security (markedReferenceLaw security primary) output := by
    simp only [endpointHistogram, FiniteDist.expectation, referenceLaw, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc]
  rw [hmix, diffuseReference_histogram, markedReference_histogram]
  have hdiff := diffuse_histogram_decomposition security primary output
  nlinarith only [hdiff]

/-- Reflection of the second source alone preserves the actual product
law and leaves the two public edge scalars fixed. -/
def secondNegate (security : ℕ) : ActualSeed security ≃ ActualSeed security :=
  (Equiv.refl _).prodCongr
    (GaussianSource.windowNegateEquiv (Parameters.sourceCutoff security - 1))

theorem secondNegate_weight (security : ℕ) (seed : ActualSeed security) :
    (actualSeedLaw security).weight (secondNegate security seed) = (actualSeedLaw security).weight seed := by
  simp only [actualSeedLaw, secondNegate, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
    Equiv.refl_apply, FiniteDist.prod_weight, scalarLaw, GaussianSource.windowGaussian_reflection]

theorem secondNegate_blur (security : ℕ) (seed : ActualSeed security) :
    actualBlur security (secondNegate security seed) = actualBlur security seed := rfl

theorem secondNegate_second (security : ℕ) (seed : ActualSeed security) :
    actualSecond security (secondNegate security seed) = -actualSecond security seed := rfl

theorem markedCompanion_convolution (security : ℕ) (primary output : Palette security) :
    markedCompanion security primary output =
      BackgroundCertificates.rootConvolutionProfile security
        (InwardAnchor.smoothedAnchorLaw security primary).weight output := by
  unfold markedCompanion
  simp only [FiniteDist.expectation, FiniteDist.map_equiv_weight]
  calc
    _ = ∑ seed, (actualSeedLaw security).weight seed *
        (InwardAnchor.shiftedAnchorLaw security primary (actualSecond security seed)
          (actualSecond_bound security seed)).weight
            ((shiftEquiv security (actualBlur security seed)).symm output) := by
      calc
        _ = ∑ seed, (actualSeedLaw security).weight (secondNegate security seed) *
          (InwardAnchor.shiftedAnchorLaw security primary (-actualSecond security (secondNegate security seed))
            (negativeSecond_bound security (secondNegate security seed))).weight
              ((shiftEquiv security (actualBlur security (secondNegate security seed))).symm output) :=
          ((secondNegate security).sum_comp _).symm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro seed _
          simp only [secondNegate_weight, secondNegate_second, secondNegate_blur, neg_neg]
    _ = ((edgeLaw security).prod (edgeLaw security)).expectation (fun edge =>
        (InwardAnchor.smoothedAnchorLaw security primary).weight
          ((shiftEquiv security ((edge.1 : ℤ) - edge.2)).symm output)) := by
      change (actualSeedLaw security).expectation (fun seed =>
        (InwardAnchor.shiftedAnchorLaw security primary (actualSecond security seed)
          (actualSecond_bound security seed)).weight
            ((shiftEquiv security (actualBlur security seed)).symm output)) = _
      rw [actualSeedLaw, FiniteDist.expectation_prod]
      simp only [actualSecond, actualBlur, InwardAnchor.smoothedAnchorLaw, FiniteDist.mix_weight,
        FiniteDist.expectation]
    _ = _ := by
      change _ = (actualSeedLaw security).expectation (fun seed =>
        (InwardAnchor.smoothedAnchorLaw security primary).weight
          ((shiftEquiv security (actualBlur security seed)).symm output))
      conv_rhs => rw [actualSeedLaw, FiniteDist.expectation_prod]
      simp only [actualBlur, FiniteDist.expectation_const]



theorem actualSecond_expectation (security : ℕ) (value : Scalar security → ℝ) :
    (actualSeedLaw security).expectation (fun seed => value seed.2) =
      (scalarLaw security).expectation value := by
  rw [actualSeedLaw, FiniteDist.expectation_prod]
  change ((edgeLaw security).prod (edgeLaw security)).expectation
    (fun _ => (scalarLaw security).expectation value) = _
  rw [FiniteDist.expectation_const]

theorem diffuse_attachment_expectation (security : ℕ) (primary : Palette security)
    (value : Scalar security → ℝ) :
    (diffuseReferenceLaw security primary).expectation (fun sample => value sample.1) =
      (scalarLaw security).expectation value := by
  unfold diffuseReferenceLaw
  rw [expectation_mix]
  simp_rw [expectation_mix, FiniteDist.expectation_map, Function.comp_def, FiniteDist.expectation_const,
    actualSecond_expectation]

theorem marked_attachment_expectation (security : ℕ) (primary : Palette security)
    (value : Scalar security → ℝ) :
    (markedReferenceLaw security primary).expectation (fun sample => value sample.1) =
      (scalarLaw security).expectation value := by
  unfold markedReferenceLaw
  rw [expectation_mix]
  simp_rw [FiniteDist.expectation_map, Function.comp_def, FiniteDist.expectation_const]
  exact actualSecond_expectation security value

theorem reference_expectation (security : ℕ) (primary : Palette security)
    (value : JointOutput security → ℝ) :
    (referenceLaw security primary).expectation value =
      (1 - activation security) * (diffuseReferenceLaw security primary).expectation value +
        activation security * (markedReferenceLaw security primary).expectation value := by
  simp only [FiniteDist.expectation, referenceLaw, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

/-- The protected attachment increment has its genuine scalar law,
independently of the primary color and the activation branch. -/
theorem reference_attachment_expectation (security : ℕ) (primary : Palette security)
    (value : Scalar security → ℝ) :
    (referenceLaw security primary).expectation (fun sample => value sample.1) =
      (scalarLaw security).expectation value := by
  rw [reference_expectation, diffuse_attachment_expectation, marked_attachment_expectation]
  ring

def scoreProfile (security : ℕ) (score : Palette security → ℝ) : Palette security → ℝ :=
  fun primary => (primaryLaw security).weight primary * score primary

 theorem sum_atom (security : ℕ) (profile : Palette security → ℝ) (output : Palette security) :
    (∑ primary, profile primary * atom primary output) = profile output := by
  classical
  simp [atom, mul_ite]

theorem convolution_sum (security : ℕ) (coefficient : Palette security → ℝ)
    (kernel : Palette security → Palette security → ℝ) (output : Palette security) :
    (∑ primary, coefficient primary * BackgroundCertificates.rootConvolutionProfile security (kernel primary) output) =
      BackgroundCertificates.rootConvolutionProfile security
        (fun center => ∑ primary, coefficient primary * kernel primary center) output := by
  unfold BackgroundCertificates.rootConvolutionProfile
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro seed _
  apply Finset.sum_congr rfl
  intro primary _
  ring

theorem markedCompanion_score (security : ℕ) (score : Palette security → ℝ)
    (output : Palette security) :
    (∑ primary, scoreProfile security score primary * markedCompanion security primary output) =
      BackgroundCertificates.rootConvolutionProfile security (anchorWeightedScore security score) output := by
  simp_rw [markedCompanion_convolution]
  rw [convolution_sum]
  congr 1
  funext center
  unfold anchorWeightedScore scoreProfile
  apply Finset.sum_congr rfl
  intro primary _
  ring

def primaryHistogramResponse (security : ℕ) (score : Palette security → ℝ) (output : Palette security) : ℝ :=
  ∑ primary, scoreProfile security score primary * endpointHistogram security (referenceLaw security primary) output

/-- The signed primary response is derived from the concrete joint law.
The independent attachment contributes zero for every centered score. -/
theorem primaryHistogramResponse_formula (security : ℕ) (score : Palette security → ℝ)
    (hcentered : (∑ primary, (primaryLaw security).weight primary * score primary) = 0)
    (output : Palette security) :
    primaryHistogramResponse security score output =
      activation security * scoreProfile security score output +
        activation security * BackgroundCertificates.rootConvolutionProfile security
          (anchorWeightedScore security score) output +
        signProfile security output * signFunctional (FirstResponse.anchorSign security) (scoreProfile security score) := by
  unfold primaryHistogramResponse
  simp_rw [reference_histogram]
  calc
    _ = ∑ primary,
        (activation security * (scoreProfile security score primary * atom primary output) +
          activation security * (scoreProfile security score primary * markedCompanion security primary output) +
          (2 * (1 - activation security) * diffuseMean security output) * scoreProfile security score primary +
          signProfile security output *
            (FirstResponse.anchorSign security primary * scoreProfile security score primary)) := by
      apply Finset.sum_congr rfl
      intro primary _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_atom, markedCompanion_score]
      change _ + _ + _ * (∑ primary, (primaryLaw security).weight primary * score primary) + _ = _
      rw [hcentered, mul_zero, add_zero]
      rfl



/-- A reserved compensator center has the actual ordinary body channel,
using the independent protected edge difference. -/
def compensatorBodyLaw (security : ℕ) (center : Palette security) : FiniteDist (Palette security) :=
  (actualSeedLaw security).map (fun seed => shiftEquiv security (actualBlur security seed) center)

theorem compensatorBodyLaw_weight (security : ℕ) (center output : Palette security) :
    (compensatorBodyLaw security center).weight output =
      BackgroundCertificates.rootConvolutionProfile security (atom center) output := by
  unfold compensatorBodyLaw BackgroundCertificates.rootConvolutionProfile
  rw [FiniteDist.map_weight]
  apply Finset.sum_congr rfl
  intro seed _
  have heq : (shiftEquiv security (actualBlur security seed)) center = output ↔
      center = (shiftEquiv security (actualBlur security seed)).symm output := by
    exact (Equiv.eq_symm_apply _).symm
  simp only [heq, atom]
  split_ifs <;> ring

theorem body_score_convolution (security : ℕ) (coefficient : Palette security → ℝ)
    (output : Palette security) :
    (∑ center, coefficient center * (compensatorBodyLaw security center).weight output) =
      BackgroundCertificates.rootConvolutionProfile security coefficient output := by
  simp_rw [compensatorBodyLaw_weight]
  rw [convolution_sum]
  congr 1
  funext center
  exact sum_atom security coefficient center

theorem center_weight_compensator (security : ℕ) (score : Palette security → ℝ)
    (center : Palette security) :
    (centerLaw security).weight center * compensatorScore security score center =
      activation security * anchorWeightedScore security score center := by
  unfold compensatorScore
  by_cases hzero : (centerLaw security).weight center = 0
  · rw [hzero, centerLaw_zero_implies_anchorScore_zero security score center hzero]
    ring
  · field_simp

theorem compensatorHistogramResponse_formula (security : ℕ) (score : Palette security → ℝ)
    (output : Palette security) :
    (∑ center, (centerLaw security).weight center * compensatorScore security score center *
      (compensatorBodyLaw security center).weight output) =
      activation security * BackgroundCertificates.rootConvolutionProfile security
        (anchorWeightedScore security score) output := by
  simp only [center_weight_compensator, mul_assoc, ← Finset.mul_sum]
  rw [body_score_convolution]

/-- The complete first histogram reads the two actual off-body outputs
and the reserved compensator-body output. Any remaining coordinate has a
profile independent of this public pair and is integrated in `other`.
Their hidden roots may be correlated: only first marginals enter here. -/
def completeHistogramResponse (security : ℕ) (score : Palette security → ℝ)
    (other : Palette security → ℝ) (output : Palette security) : ℝ :=
  ∑ primary, ∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
    pairedScore security score primary center *
      (endpointHistogram security (referenceLaw security primary) output +
        (compensatorBodyLaw security center).weight output + other output)

theorem completeHistogramResponse_decomposition (security : ℕ) (score : Palette security → ℝ)
    (hcentered : (∑ primary, (primaryLaw security).weight primary * score primary) = 0)
    (other : Palette security → ℝ) (output : Palette security) :
    completeHistogramResponse security score other output =
      primaryHistogramResponse security score output -
        ∑ center, (centerLaw security).weight center * compensatorScore security score center *
          (compensatorBodyLaw security center).weight output := by
  have hcompensator : (∑ center, (centerLaw security).weight center * compensatorScore security score center) = 0 := by
    rw [compensatorScore_mass, hcentered, mul_zero]
  have hleg (primary : Palette security) :
      (∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
        pairedScore security score primary center *
          endpointHistogram security (referenceLaw security primary) output) =
        scoreProfile security score primary * endpointHistogram security (referenceLaw security primary) output := by
    unfold pairedScore scoreProfile
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
    calc
      _ = ((primaryLaw security).weight primary * score primary *
            endpointHistogram security (referenceLaw security primary) output) *
              (∑ center, (centerLaw security).weight center) -
          ((primaryLaw security).weight primary * endpointHistogram security (referenceLaw security primary) output) *
            (∑ center, (centerLaw security).weight center * compensatorScore security score center) := by
        simp only [Finset.mul_sum]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro center _ <;> ring
      _ = _ := by rw [FiniteDist.sum_one, hcompensator]; ring
  have hbody : (∑ primary, ∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
        pairedScore security score primary center * (compensatorBodyLaw security center).weight output) =
      -(∑ center, (centerLaw security).weight center * compensatorScore security score center *
        (compensatorBodyLaw security center).weight output) := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ center, (((centerLaw security).weight center * (compensatorBodyLaw security center).weight output) *
          (∑ primary, (primaryLaw security).weight primary * score primary) -
        ((centerLaw security).weight center * compensatorScore security score center *
          (compensatorBodyLaw security center).weight output) * (∑ primary, (primaryLaw security).weight primary)) := by
        apply Finset.sum_congr rfl
        intro center _
        unfold pairedScore
        simp only [Finset.mul_sum]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro primary _
        ring
      _ = _ := by simp only [hcentered, mul_zero, FiniteDist.sum_one, mul_one, zero_sub, Finset.sum_neg_distrib]
  have hother : (∑ primary, ∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
        pairedScore security score primary center * other output) = 0 := by
    simp only [← Finset.sum_mul, pairedScore_mean_zero security score hcentered, zero_mul]
  unfold completeHistogramResponse
  simp only [mul_add, Finset.sum_add_distrib]
  simp_rw [hleg]
  rw [hbody, hother, add_zero]
  rfl

/-- The genuine paired primary and compensator cancel the entire actual
companion term. The remaining physical histogram is exactly activation
times the previously constructed rank-one response. -/
theorem completeHistogramResponse_eq_activation_response (security : ℕ) (score : Palette security → ℝ)
    (hcentered : (∑ primary, (primaryLaw security).weight primary * score primary) = 0)
    (other : Palette security → ℝ) (output : Palette security) :
    completeHistogramResponse security score other output =
      activation security * FirstResponse.response security (scoreProfile security score) output := by
  rw [completeHistogramResponse_decomposition security score hcentered,
    primaryHistogramResponse_formula security score hcentered, compensatorHistogramResponse_formula]
  simp only [FirstResponse.response, primaryRankOperator_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    profileSignMap]
  change _ = activation security * (scoreProfile security score output +
    ((activation security)⁻¹ * signFunctional (FirstResponse.anchorSign security) (scoreProfile security score)) *
      signProfile security output)
  have hactivation := (activation_pos security).ne'
  field_simp
  ring





/-- The unweighted actual leg includes its two off-body outputs and its
attachment output, whose center has the ordinary smoothed body law. -/
def legFirstMean (security : ℕ) (output : Palette security) : ℝ :=
  (∑ primary, (primaryLaw security).weight primary *
      endpointHistogram security (referenceLaw security primary) output) +
    (bodyLaw security true).weight output







end

end CurrentAFT.FirstHistogram

end

section





/-!
# Actual clipped activation and primary heights

A literal subwindow of the same discrete Gaussian lower-bounds its
normalizer. This proves the inverse-width upper bound on the actual
activation, complementing the already proved lower bound. The actual
primary height then follows from its balancing numerator.
-/

namespace CurrentAFT.GaussianHeights

open AFT GaussianSource DiffuseProfiles ProposalPrimary
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

theorem windowNormalizer_lower (width cutoff : ℕ) (hwidth : 0 < width)
    (hcutoff : width - 1 ≤ cutoff) :
    (width : ℝ) * Real.exp (-Real.pi) ≤ windowNormalizer width cutoff := by
  let point : Fin width → Window cutoff := fun index =>
    ⟨(index.val : ℤ), Finset.mem_Icc.mpr ⟨by omega, by have := index.isLt; omega⟩⟩
  have hinjective : Function.Injective point := by
    intro first second hequal
    apply Fin.ext
    have h := congrArg (fun value : Window cutoff => value.val) hequal
    change (first.val : ℤ) = (second.val : ℤ) at h
    exact_mod_cast h
  have hweight (index : Fin width) : Real.exp (-Real.pi) ≤ weight width (point index) := by
    have hw : (0 : ℝ) < width := Nat.cast_pos.mpr hwidth
    have hz : (0 : ℝ) ≤ index.val := Nat.cast_nonneg _
    have hzUpper : (index.val : ℝ) ≤ width := Nat.cast_le.mpr index.isLt.le
    have hsquare : (index.val : ℝ) ^ 2 ≤ (width : ℝ) ^ 2 := by nlinarith
    have hproduct := mul_le_mul_of_nonneg_left hsquare
      (div_nonneg Real.pi_pos.le (sq_nonneg (width : ℝ)))
    have hcancel : Real.pi / (width : ℝ) ^ 2 * (width : ℝ) ^ 2 = Real.pi := by
      field_simp
    rw [hcancel] at hproduct
    unfold weight
    apply Real.exp_le_exp.mpr
    change -Real.pi ≤ -(Real.pi / (width : ℝ) ^ 2) * (index.val : ℝ) ^ 2
    linarith
  have hsubset : Finset.univ.image point ⊆ (Finset.univ : Finset (Window cutoff)) := Finset.subset_univ _
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun value _ _ => (weight_pos (width : ℝ) value).le)
  rw [Finset.sum_image (fun first _ second _ hequal => hinjective hequal)] at hsum
  calc
    _ = ∑ _index : Fin width, Real.exp (-Real.pi) := by simp
    _ ≤ ∑ index : Fin width, weight width (point index) :=
      Finset.sum_le_sum (fun index _ => hweight index)
    _ ≤ _ := hsum

theorem windowGaussian_zero_upper (width cutoff : ℕ) (hwidth : 0 < width)
    (hcutoff : width - 1 ≤ cutoff) :
    (windowGaussian width cutoff).weight (windowZero cutoff) ≤ Real.exp Real.pi / width := by
  have hw : (0 : ℝ) < width := Nat.cast_pos.mpr hwidth
  rw [windowGaussian_zero]
  calc
    _ ≤ 1 / ((width : ℝ) * Real.exp (-Real.pi)) :=
      one_div_le_one_div_of_le (mul_pos hw (Real.exp_pos _))
        (windowNormalizer_lower width cutoff hwidth hcutoff)
    _ = _ := by rw [Real.exp_neg]; field_simp

theorem activation_upper (security : ℕ) :
    DiffuseProfiles.activation security ≤ Real.exp Real.pi / (2 * (Parameters.base security : ℝ)) := by
  have hb : 1 ≤ Parameters.base security := by have := Parameters.base_ge_two security; omega
  have hcutoff : Parameters.base security - 1 ≤ Parameters.sourceCutoff security - 1 := by
    unfold Parameters.sourceCutoff
    have hpower : Parameters.base security ≤ Parameters.base security ^ 2 := by
      simpa only [pow_one] using Nat.pow_le_pow_right hb (by omega : 1 ≤ 2)
    omega
  have h := mul_le_mul_of_nonneg_left
    (windowGaussian_zero_upper (Parameters.base security) (Parameters.sourceCutoff security - 1)
      (Parameters.base_pos security) hcutoff) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  change (1 / 2) * (windowGaussian (Parameters.base security)
    (Parameters.sourceCutoff security - 1)).weight (windowZero _) ≤ _
  exact h.trans_eq (by ring)

theorem primaryProfile_upper (security : ℕ) (color : Fin (Parameters.modulus security)) :
    primaryProfile security color ≤ (Parameters.dimension security : ℝ) /
      (markMass security * Parameters.modulus security) := by
  have hfirst : 0 ≤ (freeMass security + markMass security) * (bodyLaw security false).weight color :=
    mul_nonneg (add_nonneg (freeMass_nonneg security) (markMass_pos security).le)
      ((bodyLaw security false).nonneg color)
  have hsecond : 0 ≤ ((Parameters.legCount security : ℝ) + Parameters.modulus security) *
      (bodyLaw security true).weight color :=
    mul_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ((bodyLaw security true).nonneg color)
  have hthird : 0 ≤ 2 * (Parameters.legCount security : ℝ) * (1 - DiffuseProfiles.activation security) * diffuseMean security color :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (by linarith [activation_le_half security])) (diffuseMean_nonneg security color)
  unfold primaryProfile
  calc
    _ ≤ ((Parameters.dimension security : ℝ) / Parameters.modulus security) / markMass security :=
      div_le_div_of_nonneg_right (by linarith) (markMass_pos security).le
    _ = _ := by ring

theorem primaryLaw_upper (security : ℕ) (color : Fin (Parameters.modulus security)) :
    (primaryLaw security).weight color ≤ (Parameters.dimension security : ℝ) /
      (markMass security * Parameters.modulus security) := by
  simpa only [primaryLaw] using primaryProfile_upper security color

theorem dimension_leg_ratio (security : ℕ) :
    (Parameters.dimension security : ℝ) / Parameters.legCount security ≤
      131074 * (Parameters.base security : ℝ) ^ 32 := by
  have hl : (0 : ℝ) < Parameters.legCount security := by
    rw [Parameters.legCount_eq, Nat.cast_pow]
    exact pow_pos (FirstResponse.base_pos security) _
  apply (div_le_iff₀ hl).mpr
  have hdim : (Parameters.dimension security : ℝ) ≤ 131074 * (Parameters.base security : ℝ) ^ 160 := by
    exact_mod_cast (Parameters.dimension_bounds security).2
  calc
    _ ≤ 131074 * (Parameters.base security : ℝ) ^ 160 := hdim
    _ = _ := by rw [Parameters.legCount_eq, Nat.cast_pow, mul_assoc, ← pow_add]



end

end CurrentAFT.GaussianHeights

end

section














/-!
# Actual fixed-source local pair Hilbert estimates

The protected scalar is fixed before estimating the operator. All public
blur, midpoint, anchor-index, and integer-slice draws are the concrete
current laws. Thus later root/retained inputs can be arbitrary joint
functions, and no inverse root or sign probability is introduced.
-/

namespace CurrentAFT.LocalReferenceEnergy

open AFT DiffuseProfiles ProposalPrimary FirstHistogram
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  primaryLaw centerLaw activation actualSeedLaw

abbrev Palette (security : ℕ) := FirstHistogram.Palette security
abbrev Pair (security : ℕ) := FirstHistogram.Pair security
abbrev Scalar (security : ℕ) := FirstHistogram.Scalar security
abbrev BlurSeed (security : ℕ) :=
  GaussianSource.Window (edgeCutoff security) × GaussianSource.Window (edgeCutoff security)

def publicBlurLaw (security : ℕ) : FiniteDist (BlurSeed security) :=
  (edgeLaw security).prod (edgeLaw security)

def diffusePairAt (security : ℕ) (primary : Palette security) (scalar : Scalar security) : FiniteDist (Pair security) :=
  (FiniteDist.uniform Bool).mix (fun coin =>
    (publicBlurLaw security).mix (fun edge =>
      diffuseSeedPair security (InwardAnchor.positiveDirection security primary coin) (edge, scalar)))

def markedCompanionAt (security : ℕ) (primary : Palette security) (scalar : Scalar security) :
    FiniteDist (Palette security) :=
  (publicBlurLaw security).mix (fun edge =>
    (InwardAnchor.shiftedAnchorLaw security primary (-scalar.val)
      (by simpa only [abs_neg] using InwardAnchor.scalar_bound security scalar)).map
        (shiftEquiv security (edge.1.val - edge.2.val)))

def markedPairAt (security : ℕ) (primary : Palette security) (scalar : Scalar security) : FiniteDist (Pair security) :=
  (markedCompanionAt security primary scalar).map (fun companion => (primary, companion))

def pairAt (security : ℕ) (primary : Palette security) (scalar : Scalar security) : FiniteDist (Pair security) where
  weight pair := (1 - activation security) * (diffusePairAt security primary scalar).weight pair +
    activation security * (markedPairAt security primary scalar).weight pair
  nonneg pair := add_nonneg
    (mul_nonneg (by linarith [activation_le_half security]) ((diffusePairAt security primary scalar).nonneg pair))
    (mul_nonneg (activation_pos security).le ((markedPairAt security primary scalar).nonneg pair))
  sum_one := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, FiniteDist.sum_one, FiniteDist.sum_one]
    ring

 theorem averagedPair_height (modulus width cutoff : ℕ) (start source : ℤ)
    (hwidth : 0 < width) (hdelete : 2 * (2 + 2 * width + 2 * cutoff) ≤ modulus)
    (hstart : ∀ offset ∈ anchorInterval start width,
      |offset| ≤ 2 * (width : ℤ) + ((cutoff : ℤ) - 1))
    (hsource : |source| ≤ (cutoff : ℤ) - 1) (first second : Fin modulus) :
    TrimmedSlice.averagedPair modulus 1 start source width first second ≤
      2 / ((width : ℝ) * modulus) := by
  have hclear : 2 * (1 : ℤ) + (2 * (width : ℤ) + ((cutoff : ℤ) - 1)) +
      ((cutoff : ℤ) - 1) < modulus := by omega
  have h := TrimmedSlice.mixedPair_le modulus 1
    (2 * (width : ℤ) + ((cutoff : ℤ) - 1)) ((cutoff : ℤ) - 1) width
    (fun _ : Unit => start) (fun _ : Unit => source) (FiniteDist.uniform Unit).weight
    (FiniteDist.uniform Unit).nonneg (FiniteDist.uniform Unit).sum_one
    (fun _ => hstart) (fun _ => hsource) hclear first second
  simp only [TrimmedSlice.mixedPair, Fintype.sum_unique, FiniteDist.uniform_weight,
    Fintype.card_unique, Nat.cast_one, inv_one, one_mul] at h
  apply h.trans
  have hq : (0 : ℝ) < modulus := by exact_mod_cast (by omega : 0 < modulus)
  have hw : (0 : ℝ) < width := Nat.cast_pos.mpr hwidth
  have hd := Nat.cast_le (α := ℝ).mpr hdelete
  push_cast at hd
  have hden : 0 < (modulus : ℝ) - 2 - (2 * width + ((cutoff : ℝ) - 1)) - ((cutoff : ℝ) - 1) := by linarith
  push_cast
  norm_num only [mul_one]
  apply (div_le_div_iff₀ (mul_pos hw hden) (mul_pos hw hq)).mpr
  nlinarith only [hd, hw]

theorem diffuseSeedPair_height (security : ℕ) (positive : Bool) (seed : ActualSeed security)
    (first second : Palette security) :
    (diffuseSeedPair security positive seed).weight (first, second) ≤
      2 / ((Parameters.anchorWidth security : ℝ) * Parameters.modulus security) := by
  rw [diffuseSeedPair_weight]
  apply averagedPair_height _ _ _ _ _ (InwardAnchor.anchorWidth_pos security)
  · exact FirstResponse.two_deletion_le_modulus security
  · exact fun offset hin => interval_bound positive _ _ _ _ (actualBlur_bound security seed) hin
  · exact actualSecond_bound security seed

theorem diffusePairAt_height (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (first second : Palette security) :
    (diffusePairAt security primary scalar).weight (first, second) ≤
      2 / ((Parameters.anchorWidth security : ℝ) * Parameters.modulus security) := by
  unfold diffusePairAt
  simp only [FiniteDist.mix_weight]
  calc
    _ ≤ ∑ coin, (FiniteDist.uniform Bool).weight coin *
        ∑ edge, (publicBlurLaw security).weight edge *
          (2 / ((Parameters.anchorWidth security : ℝ) * Parameters.modulus security)) := by
      apply Finset.sum_le_sum
      intro coin _
      apply mul_le_mul_of_nonneg_left _ (FiniteDist.nonneg _ _)
      exact Finset.sum_le_sum (fun edge _ => mul_le_mul_of_nonneg_left
        (diffuseSeedPair_height security _ _ first second) ((publicBlurLaw security).nonneg edge))
    _ = _ := by simp only [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem markedCompanionAt_height (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (output : Palette security) :
    (markedCompanionAt security primary scalar).weight output ≤ 1 / (Parameters.anchorWidth security : ℝ) := by
  unfold markedCompanionAt
  simp only [FiniteDist.mix_weight, FiniteDist.map_equiv_weight]
  calc
    _ ≤ ∑ edge, (publicBlurLaw security).weight edge * (1 / (Parameters.anchorWidth security : ℝ)) :=
      Finset.sum_le_sum (fun edge _ => mul_le_mul_of_nonneg_left
        (InwardAnchor.shiftedAnchorLaw_height security primary _ _ _) ((publicBlurLaw security).nonneg edge))
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

def uniformReference (security : ℕ) : FiniteDist (Palette security) := FiniteDist.uniform _

theorem uniformReference_weight (security : ℕ) (color : Palette security) :
    (uniformReference security).weight color = 1 / (Parameters.modulus security : ℝ) := by
  simp only [uniformReference, FiniteDist.uniform_weight, Fintype.card_fin, one_div]

theorem diffusePairAt_energy (security : ℕ) (primary : Palette security) (scalar : Scalar security) :
    BlockDensity.pairEnergy (uniformReference security).weight (uniformReference security).weight
      (fun first second => (diffusePairAt security primary scalar).weight (first, second)) ≤
        2 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security := by
  have hq := FirstResponse.modulus_pos security
  have hw : (0 : ℝ) < Parameters.anchorWidth security := Nat.cast_pos.mpr (InwardAnchor.anchorWidth_pos security)
  have h := BlockDensity.diffuse_pair_energy_le
    (uniformReference security).weight (uniformReference security).weight
    (fun first second => (diffusePairAt security primary scalar).weight (first, second))
    (1 / (Parameters.modulus security : ℝ)) (1 / (Parameters.modulus security : ℝ))
    (2 / ((Parameters.anchorWidth security : ℝ) * Parameters.modulus security))
    (by positivity) (by positivity) (by positivity)
    (fun color => (uniformReference_weight security color).ge) (fun color => (uniformReference_weight security color).ge)
    (fun first second => (diffusePairAt security primary scalar).nonneg (first, second))
    (diffusePairAt_height security primary scalar)
    (by have hmass := (diffusePairAt security primary scalar).sum_one
        rw [Fintype.sum_prod_type] at hmass; exact hmass.le)
  convert h using 1
  field_simp

/-- Finite weighted Cauchy--Schwarz before summing the full output pair.
The input score can have arbitrary signs. -/
theorem pair_channel_energy_le {Input Color : Type*} [Fintype Input] [Fintype Color]
    (input : FiniteDist Input) (reference : FiniteDist Color)
    (hreference : ∀ color, 0 < reference.weight color)
    (channel : Input → FiniteDist (Color × Color)) (score : Input → ℝ) (bound : ℝ)
    (hbound : ∀ point, BlockDensity.pairEnergy reference.weight reference.weight
      (fun first second => (channel point).weight (first, second)) ≤ bound) :
    BlockDensity.pairEnergy reference.weight reference.weight
      (fun first second => ∑ point, input.weight point * score point * (channel point).weight (first, second)) ≤
        bound * input.expectation (fun point => score point ^ 2) := by
  have hcauchy (first second : Color) :
      (∑ point, input.weight point * score point * (channel point).weight (first, second)) ^ 2 ≤
        input.expectation (fun point => score point ^ 2) *
          ∑ point, input.weight point * (channel point).weight (first, second) ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro point _; exact mul_nonneg (input.nonneg point) (sq_nonneg _)
    · intro point _; exact mul_nonneg (input.nonneg point) (sq_nonneg _)
    · intro point _; ring
  unfold BlockDensity.pairEnergy
  calc
    _ ≤ ∑ first, ∑ second, input.expectation (fun point => score point ^ 2) *
        (∑ point, input.weight point * (channel point).weight (first, second) ^ 2) /
          (reference.weight first * reference.weight second) :=
      Finset.sum_le_sum (fun first _ => Finset.sum_le_sum (fun second _ =>
        div_le_div_of_nonneg_right (hcauchy first second) (mul_pos (hreference first) (hreference second)).le))
    _ = input.expectation (fun point => score point ^ 2) *
        ∑ point, input.weight point * BlockDensity.pairEnergy reference.weight reference.weight
          (fun first second => (channel point).weight (first, second)) := by
      simp only [BlockDensity.pairEnergy, Finset.mul_sum, Finset.sum_div, mul_div_assoc]
      conv_lhs => arg 2; ext first; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ ≤ _ := by
      have haverage : (∑ point, input.weight point * BlockDensity.pairEnergy reference.weight reference.weight
          (fun first second => (channel point).weight (first, second))) ≤ bound := by
        calc
          _ ≤ ∑ point, input.weight point * bound :=
            Finset.sum_le_sum (fun point _ => mul_le_mul_of_nonneg_left (hbound point) (input.nonneg point))
          _ = bound := by rw [← Finset.sum_mul, input.sum_one, one_mul]
      have hnonneg : 0 ≤ input.expectation (fun point => score point ^ 2) :=
        Finset.sum_nonneg (fun point _ => mul_nonneg (input.nonneg point) (sq_nonneg (score point)))
      exact (mul_le_mul_of_nonneg_left haverage hnonneg).trans_eq (by ring)

def signedDiffusePair (security : ℕ) (scalar : Scalar security) (score : Palette security → ℝ)
    (first second : Palette security) : ℝ :=
  ∑ primary, (primaryLaw security).weight primary * score primary *
    (diffusePairAt security primary scalar).weight (first, second)

def signedMarkedPair (security : ℕ) (scalar : Scalar security) (score : Palette security → ℝ)
    (first second : Palette security) : ℝ :=
  activation security * (primaryLaw security).weight first * score first *
    (markedCompanionAt security first scalar).weight second

def signedPairAt (security : ℕ) (scalar : Scalar security) (score : Palette security → ℝ)
    (first second : Palette security) : ℝ :=
  ∑ primary, (primaryLaw security).weight primary * score primary * (pairAt security primary scalar).weight (first, second)

theorem markedPairAt_weight (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (first second : Palette security) :
    (markedPairAt security primary scalar).weight (first, second) =
      if primary = first then (markedCompanionAt security primary scalar).weight second else 0 := by
  classical
  unfold markedPairAt
  rw [FiniteDist.map_weight]
  by_cases hequal : primary = first
  · subst first
    simp only [Prod.mk.injEq, true_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · simp only [Prod.mk.injEq, hequal, false_and, if_false, Finset.sum_const_zero]

theorem signedPairAt_decomposition (security : ℕ) (scalar : Scalar security)
    (score : Palette security → ℝ) (first second : Palette security) :
    signedPairAt security scalar score first second =
      (1 - activation security) * signedDiffusePair security scalar score first second +
        signedMarkedPair security scalar score first second := by
  classical
  unfold signedPairAt signedDiffusePair signedMarkedPair
  simp only [pairAt, markedPairAt_weight, mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro primary _
    ring
  · simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring

theorem signedDiffusePair_energy (security : ℕ) (scalar : Scalar security) (score : Palette security → ℝ) :
    BlockDensity.pairEnergy (uniformReference security).weight (uniformReference security).weight
      (signedDiffusePair security scalar score) ≤
        (2 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security) *
          (primaryLaw security).expectation (fun primary => score primary ^ 2) := by
  apply pair_channel_energy_le
  · intro color
    rw [uniformReference_weight]
    exact one_div_pos.mpr (FirstResponse.modulus_pos security)
  · exact fun primary => diffusePairAt_energy security primary scalar

def primaryMaximum (security : ℕ) : ℝ :=
  (Parameters.dimension security : ℝ) / (markMass security * Parameters.modulus security)

theorem signedMarkedPair_energy (security : ℕ) (scalar : Scalar security) (score : Palette security → ℝ) :
    BlockDensity.pairEnergy (uniformReference security).weight (uniformReference security).weight
      (signedMarkedPair security scalar score) ≤
        (activation security ^ 2 * (Parameters.modulus security : ℝ) ^ 2 * primaryMaximum security /
          Parameters.anchorWidth security) * (primaryLaw security).expectation (fun primary => score primary ^ 2) := by
  have hq := FirstResponse.modulus_pos security
  have hw : (0 : ℝ) < Parameters.anchorWidth security := Nat.cast_pos.mpr (InwardAnchor.anchorWidth_pos security)
  have hp (color : Palette security) : 0 < (primaryLaw security).weight color :=
    (by positivity : (0 : ℝ) < 1 / (2 * (Parameters.modulus security : ℝ))).trans_le
      (by simpa only [primaryLaw] using primaryProfile_atom_lower security color)
  have h := BlockDensity.marked_pair_operator_energy_le (uniformReference security).weight
    (uniformReference security).weight (primaryLaw security).weight
    (fun primary => (primaryLaw security).weight primary * score primary)
    (fun primary => markedCompanionAt security primary scalar)
    (activation security) (1 / (Parameters.modulus security : ℝ)) (1 / (Parameters.modulus security : ℝ))
    (1 / (Parameters.anchorWidth security : ℝ)) (primaryMaximum security)
    (by positivity) (by positivity) (by positivity)
    (fun color => (uniformReference_weight security color).ge) (fun color => (uniformReference_weight security color).ge)
    (fun primary output => markedCompanionAt_height security primary scalar output) hp
    (GaussianHeights.primaryLaw_upper security)
  rw [profileSquareNorm_weight_mul] at h
  change _ ≤ _ * (primaryLaw security).expectation (fun primary => score primary ^ 2) at h
  convert h using 1
  · unfold signedMarkedPair
    congr 1
    funext first second
    ring
  · field_simp

theorem pairEnergy_smul (security : ℕ) (mass : Palette security → Palette security → ℝ) (scalar : ℝ) :
    BlockDensity.pairEnergy (uniformReference security).weight (uniformReference security).weight
      (fun first second => scalar * mass first second) = scalar ^ 2 *
        BlockDensity.pairEnergy (uniformReference security).weight (uniformReference security).weight mass := by
  simp only [BlockDensity.pairEnergy, mul_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring

def pairBudget (security : ℕ) : ℝ :=
  4 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security +
    2 * activation security ^ 2 * (Parameters.modulus security : ℝ) ^ 2 * primaryMaximum security /
      Parameters.anchorWidth security

/-- Actual fixed-source signed pair budget. The diffuse branch is
estimated before any sign conditioning of the score. The marked branch
retains the true primary maximum and the squared activation. -/
theorem signedPairAt_energy (security : ℕ) (scalar : Scalar security) (score : Palette security → ℝ) :
    BlockDensity.pairEnergy (uniformReference security).weight (uniformReference security).weight
      (signedPairAt security scalar score) ≤
        pairBudget security * (primaryLaw security).expectation (fun primary => score primary ^ 2) := by
  have hdiff := signedDiffusePair_energy security scalar score
  have hmark := signedMarkedPair_energy security scalar score
  have hnonnegative : 0 ≤ BlockDensity.pairEnergy (uniformReference security).weight (uniformReference security).weight
      (signedDiffusePair security scalar score) := by
    apply Finset.sum_nonneg
    intro first _
    apply Finset.sum_nonneg
    intro second _
    exact div_nonneg (sq_nonneg _) (mul_nonneg ((uniformReference security).nonneg _) ((uniformReference security).nonneg _))
  have hactivation : (1 - activation security) ^ 2 ≤ 1 := by
    have ha := activation_pos security
    have hb := activation_le_half security
    nlinarith
  have h := BlockDensity.pairEnergy_add_le (uniformReference security).weight
    (uniformReference security).nonneg
    (fun first second => (1 - activation security) * signedDiffusePair security scalar score first second)
    (signedMarkedPair security scalar score)
  simp_rw [← signedPairAt_decomposition] at h
  rw [pairEnergy_smul] at h
  have hscale := mul_le_mul_of_nonneg_right hactivation hnonnegative
  calc
    _ ≤ 2 * BlockDensity.pairEnergy (uniformReference security).weight (uniformReference security).weight
        (signedDiffusePair security scalar score) +
      2 * BlockDensity.pairEnergy (uniformReference security).weight (uniformReference security).weight
        (signedMarkedPair security scalar score) := by linarith only [h, hscale]
    _ ≤ 2 * ((2 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security) *
        (primaryLaw security).expectation (fun primary => score primary ^ 2)) +
      2 * ((activation security ^ 2 * (Parameters.modulus security : ℝ) ^ 2 * primaryMaximum security /
        Parameters.anchorWidth security) * (primaryLaw security).expectation (fun primary => score primary ^ 2)) :=
      add_le_add (mul_le_mul_of_nonneg_left hdiff (by norm_num))
        (mul_le_mul_of_nonneg_left hmark (by norm_num))
    _ = _ := by unfold pairBudget; ring

 theorem expectation_mix {Input Output : Type*} [Fintype Input] [Fintype Output]
    (law : FiniteDist Input) (kernel : Input → FiniteDist Output) (value : Output → ℝ) :
    (law.mix kernel).expectation value = law.expectation (fun input => (kernel input).expectation value) := by
  simp only [FiniteDist.expectation, FiniteDist.mix_weight, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_assoc]

theorem diffuse_scalar_disintegration (security : ℕ) (primary : Palette security)
    (value : JointOutput security → ℝ) :
    (diffuseReferenceLaw security primary).expectation value =
      (scalarLaw security).expectation (fun scalar =>
        (diffusePairAt security primary scalar).expectation (fun pair => value (scalar, pair))) := by
  unfold diffuseReferenceLaw diffusePairAt
  simp_rw [expectation_mix, FiniteDist.expectation_map, Function.comp_def]
  conv_lhs => arg 2; ext coin; rw [actualSeedLaw, FiniteDist.expectation_prod]
  change (FiniteDist.uniform Bool).expectation (fun coin => (publicBlurLaw security).expectation
      (fun edge => (scalarLaw security).expectation (fun scalar =>
        (diffuseSeedPair security (InwardAnchor.positiveDirection security primary coin) (edge, scalar)).expectation
          (fun pair => value (scalar, pair))))) = _
  simp_rw [FiniteDist.expectation_comm (publicBlurLaw security) (scalarLaw security)]
  rw [FiniteDist.expectation_comm]

theorem marked_scalar_disintegration (security : ℕ) (primary : Palette security)
    (value : JointOutput security → ℝ) :
    (markedReferenceLaw security primary).expectation value =
      (scalarLaw security).expectation (fun scalar =>
        (markedPairAt security primary scalar).expectation (fun pair => value (scalar, pair))) := by
  unfold markedReferenceLaw markedPairAt markedCompanionAt
  simp_rw [expectation_mix, FiniteDist.expectation_map, Function.comp_def]
  rw [actualSeedLaw, FiniteDist.expectation_prod]
  change (publicBlurLaw security).expectation (fun edge =>
      (scalarLaw security).expectation (fun scalar =>
        (InwardAnchor.shiftedAnchorLaw security primary (-scalar.val) _).expectation (fun companion =>
          value (scalar, (primary, shiftEquiv security (edge.1.val - edge.2.val) companion))))) = _
  rw [FiniteDist.expectation_comm]
  simp_rw [expectation_mix, FiniteDist.expectation_map, Function.comp_def]

theorem pairAt_expectation (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (value : Pair security → ℝ) :
    (pairAt security primary scalar).expectation value =
      (1 - activation security) * (diffusePairAt security primary scalar).expectation value +
        activation security * (markedPairAt security primary scalar).expectation value := by
  simp only [FiniteDist.expectation, pairAt, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/-- Exact disintegration of the previously constructed actual joint
reference. The scalar occurring in both pair and attachment is sampled
once and retained; it has not been replaced by independent copies. -/
theorem reference_scalar_disintegration (security : ℕ) (primary : Palette security)
    (value : JointOutput security → ℝ) :
    (referenceLaw security primary).expectation value =
      (scalarLaw security).expectation (fun scalar =>
        (pairAt security primary scalar).expectation (fun pair => value (scalar, pair))) := by
  rw [reference_expectation, diffuse_scalar_disintegration, marked_scalar_disintegration]
  simp only [pairAt_expectation, FiniteDist.expectation_add, FiniteDist.expectation_const_mul]

def attachmentAt (security : ℕ) (rootShift : ℤ) (scalar : Scalar security) : FiniteDist (Palette security) :=
  (safeLaw security).map (shiftEquiv security (rootShift + scalar.val))

theorem attachmentAt_height (security : ℕ) (rootShift : ℤ) (scalar : Scalar security)
    (output : Palette security) :
    (attachmentAt security rootShift scalar).weight output ≤ 4 / (Parameters.modulus security : ℝ) := by
  rw [attachmentAt, FiniteDist.map_equiv_weight]
  have hq := FirstResponse.modulus_pos security
  have hclear := Nat.cast_lt (α := ℝ).mpr (safe_clearance security)
  push_cast at hclear
  have hsafe : 0 < (Parameters.modulus security : ℝ) - 2 * Parameters.safeMargin security := by
    linarith [show (0 : ℝ) ≤ Parameters.safeMargin security from Nat.cast_nonneg _]
  have hheight : safeHeight security ≤ 4 / (Parameters.modulus security : ℝ) := by
    unfold safeHeight
    apply (div_le_div_iff₀ hsafe hq).mpr
    linarith [show (0 : ℝ) ≤ Parameters.safeMargin security from Nat.cast_nonneg _]
  exact (safeLaw_upper security _).trans hheight

theorem attachmentAt_energy (security : ℕ) (rootShift : ℤ) (scalar : Scalar security) :
    profileSquareNorm (uniformReference security).weight (attachmentAt security rootShift scalar).weight ≤ 4 := by
  have hq := FirstResponse.modulus_pos security
  have h := BlockDensity.profile_energy_le_ratio (uniformReference security).weight
    (attachmentAt security rootShift scalar).weight 4
    (fun color => by rw [uniformReference_weight]; exact one_div_pos.mpr hq)
    (attachmentAt security rootShift scalar).nonneg (fun color => by
      rw [uniformReference_weight]
      exact (attachmentAt_height security rootShift scalar color).trans_eq (by ring))
  simpa only [FiniteDist.sum_one, mul_one] using h

def tripleMassAt (security : ℕ) (rootShift : ℤ) (scalar : Scalar security)
    (score : Palette security → ℝ) (first second attached : Palette security) : ℝ :=
  signedPairAt security scalar score first second * (attachmentAt security rootShift scalar).weight attached

theorem tripleMassAt_energy (security : ℕ) (rootShift : ℤ) (scalar : Scalar security)
    (score : Palette security → ℝ) :
    BlockDensity.tripleEnergy (uniformReference security).weight (uniformReference security).weight
      (uniformReference security).weight (tripleMassAt security rootShift scalar score) ≤
        (4 * pairBudget security) * (primaryLaw security).expectation (fun primary => score primary ^ 2) := by
  have hfactor : BlockDensity.tripleEnergy (uniformReference security).weight (uniformReference security).weight
      (uniformReference security).weight (tripleMassAt security rootShift scalar score) =
        BlockDensity.pairEnergy (uniformReference security).weight (uniformReference security).weight
          (signedPairAt security scalar score) *
        profileSquareNorm (uniformReference security).weight (attachmentAt security rootShift scalar).weight := by
    unfold BlockDensity.tripleEnergy BlockDensity.pairEnergy profileSquareNorm tripleMassAt
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro first _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro second _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro attached _
    ring
  rw [hfactor]
  have hpairnonneg : 0 ≤ BlockDensity.pairEnergy (uniformReference security).weight (uniformReference security).weight
      (signedPairAt security scalar score) := by
    apply Finset.sum_nonneg
    intro first _
    apply Finset.sum_nonneg
    intro second _
    exact div_nonneg (sq_nonneg _) (mul_nonneg ((uniformReference security).nonneg _) ((uniformReference security).nonneg _))
  calc
    _ ≤ BlockDensity.pairEnergy (uniformReference security).weight (uniformReference security).weight
        (signedPairAt security scalar score) * 4 :=
      mul_le_mul_of_nonneg_left (attachmentAt_energy security rootShift scalar) hpairnonneg
    _ ≤ (pairBudget security * (primaryLaw security).expectation (fun primary => score primary ^ 2)) * 4 :=
      mul_le_mul_of_nonneg_right (signedPairAt_energy security scalar score) (by norm_num)
    _ = _ := by ring



theorem tripleEnergy_average_le {Root Color : Type*} [Fintype Root] [Fintype Color]
    (source : FiniteDist Root) (reference : Color → ℝ) (hreference : ∀ color, 0 ≤ reference color)
    (mass : Root → Color → Color → Color → ℝ) :
    BlockDensity.tripleEnergy reference reference reference
      (fun first second attached => ∑ root, source.weight root * mass root first second attached) ≤
        ∑ root, source.weight root * BlockDensity.tripleEnergy reference reference reference (mass root) := by
  have h := profileSquareNorm_average_le source
    (fun output : (Color × Color) × Color => reference output.1.1 * reference output.1.2 * reference output.2)
    (fun output => mul_nonneg (mul_nonneg (hreference _) (hreference _)) (hreference _))
    (fun root output => mass root output.1.1 output.1.2 output.2)
  simpa only [profileSquareNorm, Fintype.sum_prod_type, BlockDensity.tripleEnergy] using h

def jointTripleMass {Root : Type*} [Fintype Root] (security : ℕ) (source : FiniteDist Root)
    (rootShift : Root → ℤ) (scalar : Root → Scalar security) (score : Root → Palette security → ℝ)
    (first second attached : Palette security) : ℝ :=
  ∑ root, source.weight root * tripleMassAt security (rootShift root) (scalar root) (score root) first second attached





theorem activated_primaryMaximum (security : ℕ) :
    activation security ^ 2 * (Parameters.modulus security : ℝ) * primaryMaximum security ≤
      65537 * Real.exp Real.pi * (Parameters.base security : ℝ) ^ 31 := by
  have hq := FirstResponse.modulus_pos security
  have hb := FirstResponse.base_pos security
  have ha := activation_pos security
  have hl : (0 : ℝ) < Parameters.legCount security := by
    rw [Parameters.legCount_eq, Nat.cast_pow]
    exact pow_pos hb _
  have hcancel : activation security ^ 2 * (Parameters.modulus security : ℝ) * primaryMaximum security =
      activation security * ((Parameters.dimension security : ℝ) / Parameters.legCount security) := by
    unfold primaryMaximum markMass
    field_simp
  rw [hcancel]
  calc
    _ ≤ (Real.exp Real.pi / (2 * (Parameters.base security : ℝ))) *
        (131074 * (Parameters.base security : ℝ) ^ 32) :=
      mul_le_mul (GaussianHeights.activation_upper security) (GaussianHeights.dimension_leg_ratio security)
        (div_nonneg (Nat.cast_nonneg _) hl.le) (by positivity)
    _ = _ := by rw [pow_succ]; field_simp; ring

theorem modulus_anchor_ratio (security : ℕ) :
    (Parameters.modulus security : ℝ) / Parameters.anchorWidth security ≤
      131072 * (Parameters.base security : ℝ) ^ 16 := by
  have hwidth : (0 : ℝ) < Parameters.anchorWidth security := Nat.cast_pos.mpr (InwardAnchor.anchorWidth_pos security)
  apply (div_le_iff₀ hwidth).mpr
  have hq := Nat.cast_le (α := ℝ).mpr (Parameters.modulus_bounds security).2
  push_cast at hq
  convert hq using 1
  rw [anchorWidth_eq, Nat.cast_pow, mul_assoc, ← pow_add]

theorem pairBudget_polynomial (security : ℕ) :
    pairBudget security ≤ (524288 + 17180131328 * Real.exp Real.pi) * (Parameters.base security : ℝ) ^ 47 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (Parameters.base_ge_two security).trans' (by norm_num : 1 ≤ 2)
  have hratio := modulus_anchor_ratio security
  have hmax := activated_primaryMaximum security
  have hnonneg : 0 ≤ activation security ^ 2 * (Parameters.modulus security : ℝ) * primaryMaximum security := by
    apply mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (markMass_pos security).le (Nat.cast_nonneg _))
  have hproduct := mul_le_mul hratio hmax hnonneg (by positivity : (0 : ℝ) ≤ 131072 * (Parameters.base security : ℝ) ^ 16)
  have hpower : (Parameters.base security : ℝ) ^ 16 ≤ (Parameters.base security : ℝ) ^ 47 :=
    pow_le_pow_right₀ hb1 (by omega)
  have hidentity : pairBudget security =
      4 * ((Parameters.modulus security : ℝ) / Parameters.anchorWidth security) +
        2 * (((Parameters.modulus security : ℝ) / Parameters.anchorWidth security) *
          (activation security ^ 2 * (Parameters.modulus security : ℝ) * primaryMaximum security)) := by
    unfold pairBudget
    ring
  rw [hidentity]
  have hpow : (Parameters.base security : ℝ) ^ 16 * (Parameters.base security : ℝ) ^ 31 =
      (Parameters.base security : ℝ) ^ 47 := by rw [← pow_add]
  calc
    _ ≤ 4 * (131072 * (Parameters.base security : ℝ) ^ 16) +
        2 * ((131072 * (Parameters.base security : ℝ) ^ 16) *
          (65537 * Real.exp Real.pi * (Parameters.base security : ℝ) ^ 31)) := by linarith only [hratio, hproduct]
    _ ≤ 4 * (131072 * (Parameters.base security : ℝ) ^ 47) +
        2 * ((131072 * (Parameters.base security : ℝ) ^ 16) *
          (65537 * Real.exp Real.pi * (Parameters.base security : ℝ) ^ 31)) := by linarith only [hpower]
    _ = _ := by
      have hproductIdentity : (131072 * (Parameters.base security : ℝ) ^ 16) *
        (65537 * Real.exp Real.pi * (Parameters.base security : ℝ) ^ 31) =
        (131072 * 65537 * Real.exp Real.pi) * ((Parameters.base security : ℝ) ^ 16 * (Parameters.base security : ℝ) ^ 31) := by ring
      rw [hproductIdentity, hpow]
      ring

end

end CurrentAFT.LocalReferenceEnergy

end

section










/-! # The actual source-independent public seed of one protected leg

The protected scalar is absent from the seed type and its probability law.
The public primary control determines the inward sign after the fair
midpoint coin, while the public anchor index and blur are shared by the
marked and diffuse refinements.
-/
namespace CurrentAFT.ActualPublicLegCharge
open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy InwardAnchor
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance anchorWidthNeZero (security : ℕ) : NeZero (Parameters.anchorWidth security) :=
  ⟨(InwardAnchor.anchorWidth_pos security).ne'⟩
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff activation

structure PublicSeed (security : ℕ) where
  marked : Bool
  coin : Bool
  anchorIndex : InwardAnchor.Index security
  blur : LocalReferenceEnergy.BlurSeed security

abbrev SeedProduct (security : ℕ) :=
  Bool × (Bool × (InwardAnchor.Index security × LocalReferenceEnergy.BlurSeed security))

def seedEquiv (security : ℕ) : PublicSeed security ≃ SeedProduct security where
  toFun seed := (seed.marked, (seed.coin, (seed.anchorIndex, seed.blur)))
  invFun draw := ⟨draw.1, draw.2.1, draw.2.2.1, draw.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance seedFintype (security : ℕ) : Fintype (PublicSeed security) :=
  Fintype.ofEquiv (SeedProduct security) (seedEquiv security).symm

def activationLaw (security : ℕ) : FiniteDist Bool where
  weight marked := if marked then activation security else 1 - activation security
  nonneg marked := by
    cases marked
    · simp only [Bool.false_eq_true, if_false]
      linarith [activation_le_half security]
    · simpa only [if_true] using (activation_pos security).le
  sum_one := by simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true]; ring

def seedLaw (security : ℕ) : FiniteDist (PublicSeed security) :=
  ((activationLaw security).prod ((FiniteDist.uniform Bool).prod
    ((FiniteDist.uniform (InwardAnchor.Index security)).prod (publicBlurLaw security)))).map (seedEquiv security).symm

def signedOffset (security : ℕ) (primary : ActualControls.Palette security) (seed : PublicSeed security) : ℤ :=
  if positiveDirection security primary seed.coin then offset security seed.anchorIndex else -offset security seed.anchorIndex

def publicShift (security : ℕ) (primary : ActualControls.Palette security) (seed : PublicSeed security) : ℤ :=
  signedOffset security primary seed + seed.blur.1.val - seed.blur.2.val







theorem blur_bound (security : ℕ) (seed : PublicSeed security) :
    |seed.blur.1.val - seed.blur.2.val| ≤ (Parameters.sourceCutoff security : ℤ) - 1 := by
  have h1 := Finset.mem_Icc.mp seed.blur.1.property
  have h2 := Finset.mem_Icc.mp seed.blur.2.property
  have hcut := InwardAnchor.sourceCutoff_pos security
  unfold edgeCutoff at *
  apply abs_le.mpr
  constructor <;> omega

theorem signedOffset_bound (security : ℕ) (primary : ActualControls.Palette security) (seed : PublicSeed security) :
    |signedOffset security primary seed| ≤ 2 * (Parameters.anchorWidth security : ℤ) - 1 := by
  have hindex := seed.anchorIndex.isLt
  unfold signedOffset offset
  split_ifs
  · rw [abs_of_nonneg (by positivity)]
    omega
  · rw [abs_neg, abs_of_nonneg (by positivity)]
    omega

theorem publicShift_bound (security : ℕ) (primary : ActualControls.Palette security) (seed : PublicSeed security) :
    |publicShift security primary seed| ≤
      2 * (Parameters.anchorWidth security : ℤ) + ((Parameters.sourceCutoff security : ℤ) - 1) := by
  have h := (abs_add_le (signedOffset security primary seed) (seed.blur.1.val - seed.blur.2.val)).trans
    (add_le_add (signedOffset_bound security primary seed) (blur_bound security seed))
  have hequal : publicShift security primary seed = signedOffset security primary seed + (seed.blur.1.val - seed.blur.2.val) := by
    unfold publicShift
    ring
  rw [hequal]
  exact h.trans (by omega)

end
end CurrentAFT.ActualPublicLegCharge

end

section



/-!
# Bounded clipping for the current affine transport construction

This file formalizes the clipping map used in
`cor:calibration-bounded-clipping` and the finite-reference high-moment
implication used in `lem:df-positive-repair` in the current manuscript.
The high-moment estimate for the actual calibrated public weight is a
separate construction-specific obligation, not a premise hidden in a
definition here.
-/

namespace CurrentAFT

/-- Clip a real public weight to the interval `[0, 2]`. -/
def clip (weight : ℝ) : ℝ := min 2 (max 0 weight)

theorem clip_nonneg (weight : ℝ) : 0 ≤ clip weight := by
  exact le_min (by norm_num) (le_max_left 0 weight)

theorem clip_le_two (weight : ℝ) : clip weight ≤ 2 :=
  min_le_left _ _

















open scoped BigOperators





end CurrentAFT

end

section







/-!
# Bounded clipping followed by public charge conditioning

This module proves the finite-measure part of the current manuscript's
`thm:df-positive-conditioning`. The endpoint kernel may contain correlated
hidden inputs, the protected body cycle, a shared queue, and final relabeling.
Only its normalization is used. The construction-specific ambient error and
the physical weight moments remain separate proof obligations.
-/

namespace CurrentAFT

open scoped BigOperators Classical
open AFT

noncomputable section

variable {Core Endpoint : Type*} [Fintype Core] [Fintype Endpoint]

/-- The signed endpoint image, relative to the uncharged public proposal. -/
def endpointMass (proposal : FiniteDist Core) (weight : Core → ℝ)
    (channel : Core → FiniteDist Endpoint) (output : Endpoint) : ℝ :=
  ∑ core, proposal.weight core * weight core * (channel core).weight output

/-- Clipping loss is measured under the uncharged proposal, at fixed placement. -/
def clippingLoss (proposal : FiniteDist Core) (weight : Core → ℝ) : ℝ :=
  ∑ core, proposal.weight core * |weight core - clip (weight core)|

theorem endpointMass_nonneg (proposal : FiniteDist Core) (weight : Core → ℝ)
    (channel : Core → FiniteDist Endpoint) (hweight : ∀ core, 0 ≤ weight core)
    (output : Endpoint) : 0 ≤ endpointMass proposal weight channel output := by
  exact Finset.sum_nonneg fun core _ =>
    mul_nonneg (mul_nonneg (proposal.nonneg core) (hweight core))
      ((channel core).nonneg output)







/-- The mass of the positive clipped endpoint measure on the charge event. -/
def chargedMass (proposal : FiniteDist Core) (weight : Core → ℝ)
    (channel : Core → FiniteDist Endpoint) (charge : Endpoint → Prop) : ℝ :=
  ∑ output, AFT.SignedConditioning.restricted
    (endpointMass proposal (fun core => clip (weight core)) channel) charge output

/-- The actual probability law obtained by restricting and normalizing the
clipped endpoint measure. The positive-mass proof is required explicitly. -/
def positiveEndpointLaw (proposal : FiniteDist Core) (weight : Core → ℝ)
    (channel : Core → FiniteDist Endpoint) (charge : Endpoint → Prop)
    (hpositive : 0 < chargedMass proposal weight channel charge) : FiniteDist Endpoint :=
  FiniteDist.normalize
    (AFT.SignedConditioning.restricted
      (endpointMass proposal (fun core => clip (weight core)) channel) charge)
    (fun output => by
      unfold AFT.SignedConditioning.restricted
      split_ifs
      · exact endpointMass_nonneg proposal _ channel (fun core => clip_nonneg _) output
      · rfl)
    hpositive





end

end CurrentAFT

end

section



/-!
# The current construction's pointwise public charge identity

This file follows `def:body-injection`, `def:shared-baseline-vector`,
`sec:queue-injection`, and `sec:df-public-charge-verification` in the
current manuscript. It does not import the frozen V7 formalization.

The endpoint assembly keeps the body's closing edge, both off-body leg
colors, the same second input at the companion and attachment, and one
shared queue scalar. The only geometric hypothesis in the modular result
is the queue's prescribed cardinality. No charge identity is assumed.
Safe support and carry cancellation are separate statements: the algebra
below holds for all values of the hidden inputs.
-/

namespace CurrentAFT

open scoped BigOperators

namespace PublicCharge

variable {G : Type*} [AddCommGroup G] {body : ℕ}
variable {Leg : Type*} [Fintype Leg]

/-- Body vertices, primary leg vertices, and companion leg vertices.
An attachment is a body vertex and therefore has no second baseline. -/
abbrev EndpointIndex (body : ℕ) (Leg : Type*) := Fin body ⊕ (Leg ⊕ Leg)

/-- Cyclic differences with the predecessor taken modulo the full body
length. In particular, the first coordinate retains the closing edge. -/
def cycleDifference (latent : Fin body → G) (vertex : Fin body) : G :=
  latent vertex - latent ((finRotate body).symm vertex)





/-- Place each second leg input at its body attachment. The same input
is subtracted from its companion below. -/
def attachmentIncrement (attachment : Leg → Fin body) (second : Leg → G)
    (vertex : Fin body) : G :=
  ∑ leg, if attachment leg = vertex then second leg else 0

theorem sum_attachmentIncrement (attachment : Leg → Fin body) (second : Leg → G) :
    ∑ vertex, attachmentIncrement attachment second vertex = ∑ leg, second leg := by
  unfold attachmentIncrement
  rw [Finset.sum_comm]
  simp

/-- Every queue vertex receives the same scalar. -/
def queueIncrement (queue : Finset (Fin body)) (scalar : G) (vertex : Fin body) : G :=
  if vertex ∈ queue then scalar else 0



/-- The off-body companion retains the shared second input; the
primary may itself depend on both hidden coordinates and the public map. -/
def legCompanion (legConstant : G) (shift second primary : Leg → G) (leg : Leg) : G :=
  legConstant + shift leg - second leg - primary leg



/-- The actual additive endpoint assembly before final relabeling.
The body placement moves the entire closed cycle. -/
def assembledEndpoint (centers : Fin body → G) (shift : Leg → G)
    (legConstant : G) (latent : Fin body → G) (bodyPlacement : Equiv.Perm (Fin body))
    (attachment : Leg → Fin body) (second primary : Leg → G)
    (queue : Finset (Fin body)) (scalar : G) : EndpointIndex body Leg → G
  | .inl vertex => centers vertex + cycleDifference latent (bodyPlacement.symm vertex) +
      attachmentIncrement attachment second vertex + queueIncrement queue scalar vertex
  | .inr (.inl leg) => primary leg
  | .inr (.inr leg) => legCompanion legConstant shift second primary leg





/-- Public charge reads only the sampled centers and leg shifts. It
does not read any hidden input, cycle realization, queue scalar, or map. -/
def PublicChargeTest (modulus : ℕ) (centers : Fin body → ℤ) (shift : Leg → ℤ) : Prop :=
  (((∑ vertex, centers vertex) + (∑ leg, shift leg) : ℤ) : ZMod modulus) =
    (Fintype.card Leg : ZMod modulus)









end PublicCharge

end CurrentAFT

end

section




/-!
# The actual zero-sum endpoint target

For a nonzero modulus and a positive number of endpoint coordinates, uniform
ambient colors have zero total charge with probability exactly `1 / q`.
Conditioning this law gives the uniform zero-sum hyperplane law. These are
finite counting statements; no independence or cardinality estimate for the
calibrated construction is assumed.
-/

namespace CurrentAFT

open AFT
open scoped BigOperators Classical

noncomputable section

/-- The ambient endpoint space has `dimension + 1` coordinates. -/
abbrev EndpointSpace (dimension modulus : ℕ) := Fin (dimension + 1) → ZMod modulus

/-- The zero-sum endpoint hyperplane as a subtype of the ambient space. -/
abbrev ZeroSumSpace (dimension modulus : ℕ) :=
  {endpoint : EndpointSpace dimension modulus // ∑ index, endpoint index = 0}

instance zeroSumSpaceNonempty (dimension modulus : ℕ) :
    Nonempty (ZeroSumSpace dimension modulus) :=
  ⟨⟨fun _ => 0, by simp⟩⟩

/-- Every tail has exactly one zero-charge extension: its first coordinate is
the negative sum of that tail. -/
def zeroSumTailEquiv (dimension modulus : ℕ) :
    ZeroSumSpace dimension modulus ≃ (Fin dimension → ZMod modulus) where
  toFun endpoint index := endpoint.val index.succ
  invFun tail := ⟨Fin.cons (-∑ index, tail index) tail, by simp [Fin.sum_univ_succ]⟩
  left_inv endpoint := by
    apply Subtype.ext
    funext index
    refine Fin.cases ?_ (fun _ => rfl) index
    change -(∑ index : Fin dimension, endpoint.val index.succ) = endpoint.val 0
    have hsum := endpoint.property
    rw [Fin.sum_univ_succ] at hsum
    exact (eq_neg_of_add_eq_zero_left hsum).symm
  right_inv tail := rfl

theorem zeroSumSpace_card (dimension modulus : ℕ) [NeZero modulus] :
    Fintype.card (ZeroSumSpace dimension modulus) = modulus ^ dimension := by
  simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card] using
    Fintype.card_congr (zeroSumTailEquiv dimension modulus)

theorem endpointSpace_card (dimension modulus : ℕ) [NeZero modulus] :
    Fintype.card (EndpointSpace dimension modulus) = modulus ^ (dimension + 1) := by
  simp only [EndpointSpace, Fintype.card_fun, Fintype.card_fin, ZMod.card]

/-- Uniform on the actual hyperplane, viewed as a law in the ambient space. -/
def uniformZeroSum (dimension modulus : ℕ) [NeZero modulus] :
    FiniteDist (EndpointSpace dimension modulus) :=
  (FiniteDist.uniform (ZeroSumSpace dimension modulus)).map Subtype.val



/-- The ambient uniform law assigns the zero-sum event exactly `1 / modulus`.
The proof counts the event using the explicit extension equivalence above. -/
theorem uniform_zeroSum_mass (dimension modulus : ℕ) [NeZero modulus] :
    (∑ endpoint : EndpointSpace dimension modulus,
      if (∑ index, endpoint index) = 0 then
        (FiniteDist.uniform (EndpointSpace dimension modulus)).weight endpoint else 0) =
      1 / (modulus : ℝ) := by
  simp only [FiniteDist.uniform_weight]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcount : (Finset.univ.filter
      (fun endpoint : EndpointSpace dimension modulus => (∑ index, endpoint index) = 0)).card =
      modulus ^ dimension := by
    rw [← Fintype.card_subtype]
    exact zeroSumSpace_card dimension modulus
  rw [hcount, endpointSpace_card]
  have hmodulus : (modulus : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne modulus)
  simp only [Nat.cast_pow, pow_succ]
  field_simp
  push_cast
  rfl



end

end CurrentAFT

end

section









/-!
# Conditioning onto the actual zero-sum target

The reference event mass is proved by finite counting. It is not an
extra analytic premise. At a fixed placement, the channel may average any
remaining finite randomness, including correlated protected inputs.
-/

namespace CurrentAFT

open AFT
open scoped BigOperators Classical

noncomputable section

theorem uniform_eventMass_zeroSum (dimension modulus : ℕ) [NeZero modulus] :
    (FiniteDist.uniform (EndpointSpace dimension modulus)).eventMass
      (fun endpoint => ∑ index, endpoint index = 0) = 1 / (modulus : ℝ) := by
  unfold FiniteDist.eventMass
  rw [← uniform_zeroSum_mass dimension modulus]
  apply Finset.sum_congr rfl
  intro endpoint _
  by_cases h : (∑ index, endpoint index) = 0 <;> simp [h]





/-- Event probabilities under an actual deterministic pushforward. -/
theorem eventMass_map {Seed Output : Type*} [Fintype Seed] [Fintype Output]
    (law : FiniteDist Seed) (output : Seed → Output) (event : Output → Prop) :
    (law.map output).eventMass event =
      ∑ seed, if event (output seed) then law.weight seed else 0 := by
  unfold FiniteDist.eventMass
  simp only [FiniteDist.map_weight]
  trans ∑ endpoint, ∑ seed,
    if output seed = endpoint then (if event endpoint then law.weight seed else 0) else 0
  · apply Finset.sum_congr rfl
    intro endpoint _
    by_cases h : event endpoint <;> simp [h]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro seed _
    simp



end

end CurrentAFT

end

section





/-!
# Public-core conditioning before the hidden endpoint channel

At a fixed placement, the public core law is defined using only the public
proposal, its weight, and its public charge test. If the channel's endpoint
charge agrees almost surely with that public test, conditioning the public
core before applying the channel gives exactly the positive endpoint law.

The channel may retain arbitrary dependence among hidden coordinates. Its
charge consistency is an explicit interface to the construction's pointwise
assembly identity; this generic file does not assume or claim that the
actual assembly has already been connected to the channel.
-/

namespace CurrentAFT

open AFT
open scoped BigOperators Classical

noncomputable section

variable {Core Endpoint : Type*} [Fintype Core] [Fintype Endpoint]







/-- The unnormalized public-core mass depends only on public core data. -/
def clippedPublicCoreWeight (proposal : FiniteDist Core) (weight : Core → ℝ)
    (publicCharge : Core → Prop) (core : Core) : ℝ :=
  if publicCharge core then proposal.weight core * clip (weight core) else 0

theorem clippedPublicCoreWeight_nonneg (proposal : FiniteDist Core) (weight : Core → ℝ)
    (publicCharge : Core → Prop) (core : Core) :
    0 ≤ clippedPublicCoreWeight proposal weight publicCharge core := by
  unfold clippedPublicCoreWeight
  split_ifs
  · exact mul_nonneg (proposal.nonneg core) (clip_nonneg _)
  · rfl

def publicCoreMass (proposal : FiniteDist Core) (weight : Core → ℝ)
    (publicCharge : Core → Prop) : ℝ :=
  ∑ core, clippedPublicCoreWeight proposal weight publicCharge core

/-- The positive public law is specified before any hidden-source channel.
Its arguments contain no hidden source, source sample, or output endpoint. -/
def positivePublicCoreLaw (proposal : FiniteDist Core) (weight : Core → ℝ)
    (publicCharge : Core → Prop) (hpositive : 0 < publicCoreMass proposal weight publicCharge) :
    FiniteDist Core :=
  FiniteDist.normalize (clippedPublicCoreWeight proposal weight publicCharge)
    (clippedPublicCoreWeight_nonneg proposal weight publicCharge) hpositive













end

end CurrentAFT

end

section





/-!
# Actual cyclic translation certificates for the shared queue

A translated safe law is projected back to the safe palette by returning
its unsafe mass according to the original safe law. Both parts are finite
explicit sums. The body certificate records the projected difference;
the remaining root-convolved residual is lifted through the actual first
response inverse. Their leading responses reconstruct the full translated
safe profile minus uniformity exactly.

The bounds here are uniform over every cyclic translation. This weaker
body-seed estimate avoids a shift-size assumption and is sufficient after
the current population and radius weights are applied.
-/

namespace CurrentAFT.BackgroundTranslations

open AFT DiffuseProfiles ProposalPrimary FringeCertificate BackgroundCertificates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.bodySize
  Parameters.legCount Parameters.safeMargin DiffuseProfiles.activation DiffuseProfiles.actualSeedLaw
  primaryProfile safeLaw bodyLaw FirstResponse.responseEquiv

abbrev Palette (security : ℕ) := Fin (Parameters.modulus security)

def shiftedSafeLaw (security : ℕ) (shift : ℤ) : FiniteDist (Palette security) :=
  (safeLaw security).map (shiftEquiv security shift)

theorem shiftedSafeLaw_height (security : ℕ) (shift : ℤ) (color : Palette security) :
    (shiftedSafeLaw security shift).weight color ≤ safeHeight security := by
  rw [shiftedSafeLaw, FiniteDist.map_equiv_weight]
  exact safeLaw_upper security _

def unsafePart (security : ℕ) (shift : ℤ) (color : Palette security) : ℝ :=
  if InwardAnchor.SafeColor security color then 0 else (shiftedSafeLaw security shift).weight color

def unsafeMass (security : ℕ) (shift : ℤ) : ℝ := ∑ color, unsafePart security shift color

theorem unsafePart_nonneg (security : ℕ) (shift : ℤ) (color : Palette security) :
    0 ≤ unsafePart security shift color := by
  unfold unsafePart
  split_ifs
  · rfl
  · exact FiniteDist.nonneg _ _

theorem unsafeMass_nonneg (security : ℕ) (shift : ℤ) : 0 ≤ unsafeMass security shift :=
  Finset.sum_nonneg (fun color _ => unsafePart_nonneg security shift color)

theorem unsafePart_le_shifted (security : ℕ) (shift : ℤ) (color : Palette security) :
    unsafePart security shift color ≤ (shiftedSafeLaw security shift).weight color := by
  unfold unsafePart
  split_ifs
  · exact FiniteDist.nonneg _ _
  · rfl

theorem unsafeMass_le_one (security : ℕ) (shift : ℤ) : unsafeMass security shift ≤ 1 := by
  calc
    _ ≤ ∑ color, (shiftedSafeLaw security shift).weight color :=
      Finset.sum_le_sum (fun color _ => unsafePart_le_shifted security shift color)
    _ = 1 := FiniteDist.sum_one _

theorem unsafePart_le_hole (security : ℕ) (shift : ℤ) (color : Palette security) :
    unsafePart security shift color ≤ safeHeight security - (safeLaw security).weight color := by
  by_cases hsafe : InwardAnchor.SafeColor security color
  · simp only [unsafePart, if_pos hsafe, safeLaw_weight, sub_self, le_refl]
  · simp only [unsafePart, if_neg hsafe, safeLaw_weight, sub_zero]
    exact shiftedSafeLaw_height security shift color

theorem unsafeMass_le_fringeMass (security : ℕ) (shift : ℤ) :
    unsafeMass security shift ≤ fringeMass security := by
  calc
    _ ≤ ∑ color, (safeHeight security - (safeLaw security).weight color) :=
      Finset.sum_le_sum (fun color _ => unsafePart_le_hole security shift color)
    _ = fringeMass security := by
      rw [fringeMass_height]
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, FiniteDist.sum_one]

/-- This is the actual safe projection, including its returned unsafe mass. -/
def projectedShiftProfile (security : ℕ) (shift : ℤ) (color : Palette security) : ℝ :=
  (shiftedSafeLaw security shift).weight color - unsafePart security shift color +
    unsafeMass security shift * (safeLaw security).weight color

theorem projectedShiftProfile_nonneg (security : ℕ) (shift : ℤ) (color : Palette security) :
    0 ≤ projectedShiftProfile security shift color := by
  unfold projectedShiftProfile
  exact add_nonneg (sub_nonneg.mpr (unsafePart_le_shifted security shift color))
    (mul_nonneg (unsafeMass_nonneg security shift) ((safeLaw security).nonneg color))

theorem projectedShiftProfile_mass (security : ℕ) (shift : ℤ) :
    ∑ color, projectedShiftProfile security shift color = 1 := by
  simp only [projectedShiftProfile, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, FiniteDist.sum_one, mul_one, unsafeMass]
  ring



theorem projectedShiftProfile_zero_outside (security : ℕ) (shift : ℤ) (color : Palette security)
    (hunsafe : ¬InwardAnchor.SafeColor security color) : projectedShiftProfile security shift color = 0 := by
  simp only [projectedShiftProfile, unsafePart, if_neg hunsafe, safeLaw_weight,
    sub_self, mul_zero, add_zero]

theorem projectedShiftProfile_majorant (security : ℕ) (shift : ℤ) (color : Palette security) :
    projectedShiftProfile security shift color ≤ 4 * (centerLaw security).weight color := by
  by_cases hsafe : InwardAnchor.SafeColor security color
  · have hheight := shiftedSafeLaw_height security shift color
    have hmass := unsafeMass_le_one security shift
    have hsafeLower := (centerProfile_bounds security color).1
    rw [safeLaw_weight, if_pos hsafe] at hsafeLower
    have hproject : projectedShiftProfile security shift color ≤ 2 * safeHeight security := by
      simp only [projectedShiftProfile, unsafePart, if_pos hsafe, sub_zero, safeLaw_weight]
      nlinarith only [hheight, mul_le_mul_of_nonneg_right hmass (safeHeight_pos security).le]
    change _ ≤ 4 * centerProfile security color
    linarith
  · rw [projectedShiftProfile_zero_outside security shift color hsafe]
    exact mul_nonneg (by norm_num) ((centerLaw security).nonneg color)

def safeSeedProfile (security : ℕ) (shift : ℤ) : Palette security → ℝ :=
  fun color => projectedShiftProfile security shift color - (safeLaw security).weight color

def safeSeedDensity (security : ℕ) (shift : ℤ) (color : Palette security) : ℝ :=
  safeSeedProfile security shift color / (centerLaw security).weight color

theorem safeSeedProfile_mass (security : ℕ) (shift : ℤ) : ∑ color, safeSeedProfile security shift color = 0 := by
  simp only [safeSeedProfile, Finset.sum_sub_distrib, projectedShiftProfile_mass, FiniteDist.sum_one, sub_self]



theorem safeSeedDensity_profile (security : ℕ) (shift : ℤ) :
    (fun color => (centerLaw security).weight color * safeSeedDensity security shift color) =
      safeSeedProfile security shift := by
  funext color
  by_cases hz : (centerLaw security).weight color = 0
  · have hproject : projectedShiftProfile security shift color = 0 := by
      have h := projectedShiftProfile_majorant security shift color
      rw [hz, mul_zero] at h
      exact le_antisymm h (projectedShiftProfile_nonneg security shift color)
    have hsafe : (safeLaw security).weight color = 0 := by
      have h := (centerProfile_bounds security color).1
      change (safeLaw security).weight color / 2 ≤ (centerLaw security).weight color at h
      rw [hz] at h
      linarith [(safeLaw security).nonneg color]
    simp only [hz, zero_mul, safeSeedProfile, hproject, hsafe, sub_self]
  · unfold safeSeedDensity
    field_simp

theorem safeSeedDensity_centered (security : ℕ) (shift : ℤ) :
    (∑ color, (centerLaw security).weight color * safeSeedDensity security shift color) = 0 := by
  rw [safeSeedDensity_profile]
  exact safeSeedProfile_mass security shift



theorem safeSeedDensity_square_le (security : ℕ) (shift : ℤ) :
    (∑ color, (centerLaw security).weight color * safeSeedDensity security shift color ^ 2) ≤ 12 := by
  have hproject : profileSquareNorm (centerLaw security).weight (projectedShiftProfile security shift) ≤ 4 := by
    simpa only [projectedShiftProfile_mass, mul_one] using dominated_profile_square_le security
      (centerLaw security).weight (projectedShiftProfile security shift) 4 (by norm_num)
      (centerLaw security).nonneg (projectedShiftProfile_nonneg security shift)
      (projectedShiftProfile_majorant security shift)
  have hdensity : (∑ color, (centerLaw security).weight color * safeSeedDensity security shift color ^ 2) =
      profileSquareNorm (centerLaw security).weight (safeSeedProfile security shift) := densityScore_square _ _
  rw [hdensity]
  have h := center_profile_sub_square_le_two security (projectedShiftProfile security shift) (safeLaw security).weight
  change profileSquareNorm (centerLaw security).weight (projectedShiftProfile security shift - (safeLaw security).weight) ≤ _
  linarith [safeLaw_center_square_le_two security]

theorem safeSeedDensity_norm_le_four (security : ℕ) (shift : ℤ) :
    Real.sqrt (∑ color, (centerLaw security).weight color * safeSeedDensity security shift color ^ 2) ≤ 4 := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · norm_num
  · linarith [safeSeedDensity_square_le security shift]

theorem rootConvolutionProfile_nonneg (security : ℕ) (profile : Palette security → ℝ)
    (hprofile : ∀ color, 0 ≤ profile color) (output : Palette security) :
    0 ≤ rootConvolutionProfile security profile output :=
  Finset.sum_nonneg (fun seed _ => mul_nonneg ((actualSeedLaw security).nonneg seed) (hprofile _))

theorem rootConvolutionProfile_mono (security : ℕ) (first second : Palette security → ℝ)
    (hle : ∀ color, first color ≤ second color) (output : Palette security) :
    rootConvolutionProfile security first output ≤ rootConvolutionProfile security second output :=
  Finset.sum_le_sum (fun seed _ => mul_le_mul_of_nonneg_left (hle _) ((actualSeedLaw security).nonneg seed))

theorem rootConvolutionProfile_mass (security : ℕ) (profile : Palette security → ℝ) :
    (∑ output, rootConvolutionProfile security profile output) = ∑ color, profile color := by
  unfold rootConvolutionProfile
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, (shiftEquiv security _).symm.sum_comp profile]
  rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem convolved_hole_eq_fringe (security : ℕ) (output : Palette security) :
    rootConvolutionProfile security (fun color => safeHeight security - (safeLaw security).weight color) output =
      fringe security output := by
  simp only [rootConvolutionProfile, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    FiniteDist.sum_one, one_mul, fringe, bodyLaw_false_weight]

theorem convolved_unsafe_le_fringe (security : ℕ) (shift : ℤ) (output : Palette security) :
    rootConvolutionProfile security (unsafePart security shift) output ≤ fringe security output := by
  exact (rootConvolutionProfile_mono security _ _ (unsafePart_le_hole security shift) output).trans_eq
    (convolved_hole_eq_fringe security output)

def translationResidual (security : ℕ) (shift : ℤ) : Palette security → ℝ :=
  fun output => rootConvolutionProfile security (unsafePart security shift) output -
    unsafeMass security shift * (bodyLaw security false).weight output

theorem translationResidual_mass (security : ℕ) (shift : ℤ) : ∑ output, translationResidual security shift output = 0 := by
  simp only [translationResidual, Finset.sum_sub_distrib, rootConvolutionProfile_mass,
    ← Finset.mul_sum, FiniteDist.sum_one, mul_one, unsafeMass, sub_self]

theorem convolvedUnsafe_square_bound (security : ℕ) (shift : ℤ) :
    profileSquareNorm (primaryLaw security).weight (rootConvolutionProfile security (unsafePart security shift)) ≤
      compensation security * unsafeMass security shift := by
  have hq := FirstResponse.modulus_pos security
  have hp (color : Palette security) : 0 < (primaryLaw security).weight color :=
    (by positivity : 0 < 1 / (2 * (Parameters.modulus security : ℝ))).trans_le
      (primaryProfile_atom_lower security color)
  have hnonneg := rootConvolutionProfile_nonneg security _ (unsafePart_nonneg security shift)
  have hdom (color : Palette security) :
      |rootConvolutionProfile security (unsafePart security shift) color| ≤
        compensation security * (primaryLaw security).weight color := by
    rw [abs_of_nonneg (hnonneg color)]
    exact (convolved_unsafe_le_fringe security shift color).trans (fringe_majorant security color)
  have h := signProfile_square_bound _ _ _ hp hdom
  simpa only [abs_of_nonneg (hnonneg _), rootConvolutionProfile_mass, unsafeMass] using h

theorem bodyLaw_false_primary_square_le_four (security : ℕ) :
    profileSquareNorm (primaryLaw security).weight (bodyLaw security false).weight ≤ 4 := by
  have hq := FirstResponse.modulus_pos security
  have hheight : safeHeight security ≤ 2 / (Parameters.modulus security : ℝ) := by
    have hstrip : 4 * (Parameters.safeMargin security : ℝ) < Parameters.modulus security := by
      exact_mod_cast safe_clearance security
    unfold safeHeight
    calc
      _ ≤ 1 / ((Parameters.modulus security : ℝ) / 2) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      _ = _ := by ring
  have hdom (color : Palette security) : (bodyLaw security false).weight color ≤
      4 * (primaryLaw security).weight color := by
    have hp := mul_le_mul_of_nonneg_left (primaryProfile_atom_lower security color)
      (show (0 : ℝ) ≤ 4 by norm_num)
    have heq : 4 * (1 / (2 * (Parameters.modulus security : ℝ))) = 2 / Parameters.modulus security := by ring
    rw [heq] at hp
    exact ((bodyLaw_upper security false color).trans hheight).trans hp
  simpa only [FiniteDist.sum_one, mul_one] using dominated_profile_square_le security
    (primaryLaw security).weight (bodyLaw security false).weight 4 (by norm_num)
    (primaryLaw security).nonneg (bodyLaw security false).nonneg hdom

theorem translationResidual_square_bound (security : ℕ) (shift : ℤ) :
    profileSquareNorm (primaryLaw security).weight (translationResidual security shift) ≤
      2 * compensation security * unsafeMass security shift + 8 * unsafeMass security shift ^ 2 := by
  have h := FringeCertificate.profileSquareNorm_sub_le_two security
    (rootConvolutionProfile security (unsafePart security shift))
    (unsafeMass security shift • (bodyLaw security false).weight)
  rw [profileSquareNorm_smul] at h
  have hunsafe := convolvedUnsafe_square_bound security shift
  have hbody := mul_le_mul_of_nonneg_left (bodyLaw_false_primary_square_le_four security)
    (sq_nonneg (unsafeMass security shift))
  change profileSquareNorm (primaryLaw security).weight
    (rootConvolutionProfile security (unsafePart security shift) - unsafeMass security shift •
      (bodyLaw security false).weight) ≤ _
  nlinarith only [h, hunsafe, hbody]

def residualCertificateProfile (security : ℕ) (shift : ℤ) : Palette security → ℝ :=
  (activation security)⁻¹ • (FirstResponse.responseEquiv security).symm (translationResidual security shift)

def residualCertificateDensity (security : ℕ) (shift : ℤ) (color : Palette security) : ℝ :=
  residualCertificateProfile security shift color / (primaryLaw security).weight color

theorem residualCertificateDensity_profile (security : ℕ) (shift : ℤ) :
    (fun color => (primaryLaw security).weight color * residualCertificateDensity security shift color) =
      residualCertificateProfile security shift := by
  have hq := FirstResponse.modulus_pos security
  funext color
  have hp : (primaryLaw security).weight color ≠ 0 := ne_of_gt
    ((by positivity : 0 < 1 / (2 * (Parameters.modulus security : ℝ))).trans_le
      (primaryProfile_atom_lower security color))
  unfold residualCertificateDensity
  field_simp

theorem residualCertificateDensity_centered (security : ℕ) (shift : ℤ) :
    (∑ color, (primaryLaw security).weight color * residualCertificateDensity security shift color) = 0 := by
  rw [residualCertificateDensity_profile]
  simp only [residualCertificateProfile, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
    FirstResponse.response_inverse_preserves_mass, translationResidual_mass, mul_zero]



theorem translationResidual_square_decay (security : ℕ) (shift : ℤ) :
    profileSquareNorm (primaryLaw security).weight (translationResidual security shift) ≤
      12 / (Parameters.base security : ℝ) ^ 94 := by
  have hmass := unsafeMass_le_fringeMass security shift
  have hmassSq := pow_le_pow_left₀ (unsafeMass_nonneg security shift) hmass 2
  have hproduct := mul_le_mul_of_nonneg_left hmass (compensation_nonneg security)
  have hproduct0 := mul_nonneg (compensation_nonneg security) (fringeMass_nonneg security)
  calc
    _ ≤ 2 * compensation security * unsafeMass security shift + 8 * unsafeMass security shift ^ 2 :=
      translationResidual_square_bound security shift
    _ ≤ 2 * (compensation security * fringeMass security) + 8 * fringeMass security ^ 2 := by
      have h := add_le_add (mul_le_mul_of_nonneg_left hproduct (show (0 : ℝ) ≤ 2 by norm_num))
        (mul_le_mul_of_nonneg_left hmassSq (show (0 : ℝ) ≤ 8 by norm_num))
      exact (by ring_nf at h ⊢; exact h)
    _ ≤ 2 * (4 * fringeMass security ^ 2 + 2 * compensation security * fringeMass security) := by
      nlinarith only [hproduct0]
    _ ≤ 2 * (6 / (Parameters.base security : ℝ) ^ 94) :=
      mul_le_mul_of_nonneg_left (bodyDeviation_budget_decay security) (by norm_num)
    _ = _ := by ring

theorem residualCertificateDensity_square_decay (security : ℕ) (shift : ℤ) :
    (∑ color, (primaryLaw security).weight color * residualCertificateDensity security shift color ^ 2) ≤
      768 / (Parameters.base security : ℝ) ^ 92 := by
  have hb := FirstResponse.base_pos security
  have hpositive (profile : Palette security → ℝ) : 0 ≤ profileSquareNorm (primaryLaw security).weight profile :=
    profileSquareNorm_nonneg _ _ (primaryLaw security).nonneg
  have hinverse := (actual_first_response_stable security (translationResidual security shift)).2
  have hinverseSq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hinverse 2
  rw [mul_pow, Real.sq_sqrt (hpositive _), Real.sq_sqrt (hpositive _)] at hinverseSq
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at hinverseSq
  have hnorm : (∑ color, (primaryLaw security).weight color * residualCertificateDensity security shift color ^ 2) =
      (activation security)⁻¹ ^ 2 * profileSquareNorm (primaryLaw security).weight
        ((FirstResponse.responseEquiv security).symm (translationResidual security shift)) := by
    rw [show (∑ color, (primaryLaw security).weight color * residualCertificateDensity security shift color ^ 2) =
        profileSquareNorm (primaryLaw security).weight (residualCertificateProfile security shift) from densityScore_square _ _]
    rw [residualCertificateProfile, profileSquareNorm_smul]
  rw [hnorm]
  have hinv := FirstResponse.activation_inverse_le security
  have hinvsq := pow_le_pow_left₀ (one_div_pos.mpr (activation_pos security)).le hinv 2
  have hscale : (activation security)⁻¹ ^ 2 ≤ 16 * (Parameters.base security : ℝ) ^ 2 := by
    simpa only [one_div, mul_pow, show (4 : ℝ) ^ 2 = 16 by norm_num] using hinvsq
  calc
    _ ≤ (16 * (Parameters.base security : ℝ) ^ 2) *
        (4 * (12 / (Parameters.base security : ℝ) ^ 94)) :=
      mul_le_mul hscale (hinverseSq.trans (mul_le_mul_of_nonneg_left
        (translationResidual_square_decay security shift) (by norm_num)))
        (hpositive _) (by positivity)
    _ = _ := by field_simp; ring

theorem residualCertificateDensity_norm_decay (security : ℕ) (shift : ℤ) :
    Real.sqrt (∑ color, (primaryLaw security).weight color * residualCertificateDensity security shift color ^ 2) ≤
      32 / (Parameters.base security : ℝ) ^ 46 := by
  have hb := FirstResponse.base_pos security
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hden : (32 / (Parameters.base security : ℝ) ^ 46) ^ 2 =
      1024 / (Parameters.base security : ℝ) ^ 92 := by ring
  rw [hden]
  exact (residualCertificateDensity_square_decay security shift).trans
    (div_le_div_of_nonneg_right (by norm_num) (pow_nonneg hb.le _))



end

end CurrentAFT.BackgroundTranslations

end

section





/-!
# Current graded population bounds for the free and queue atoms

These envelopes are explicit upper bounds on the graded norms of the
actual primary/body density components already constructed. The body
factor uses the actual ordinary-control population and the manuscript's
analysis radius. Population-multiplied linear and quadratic budgets are
proved below; no small-background premise is supplied.
-/

namespace CurrentAFT.BackgroundRates

open AFT DiffuseProfiles ProposalPrimary FringeCertificate BackgroundCertificates BackgroundTranslations
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
  Parameters.safeMargin DiffuseProfiles.activation

def ordinaryPool (security : ℕ) : ℕ :=
  Parameters.bodySize security - Parameters.modulus security - 2 * Parameters.legCount security

def radius (security : ℕ) : ℝ := (Parameters.base security : ℝ) ^ (1 / 4 : ℝ)
def primaryFactor (security : ℕ) : ℝ := (Real.sqrt (Parameters.legCount security : ℝ))⁻¹
def bodyFactor (security : ℕ) : ℝ := radius security * (Real.sqrt (ordinaryPool security : ℝ))⁻¹

theorem ordinaryPool_lower (security : ℕ) : Parameters.base security ^ 160 ≤ ordinaryPool security := by
  have hb : 1 ≤ Parameters.base security := by have := Parameters.base_ge_two security; omega
  have hqLower := (Parameters.modulus_bounds security).1
  have h32 : Parameters.base security ^ 32 ≤ Parameters.base security ^ 64 := Nat.pow_le_pow_right hb (by omega)
  have hqEight : 8 * Parameters.base security ^ 32 ≤ Parameters.modulus security := by omega
  have hlegs : 8 * Parameters.legCount security ≤ Parameters.bodySize security := by
    have h := Nat.mul_le_mul_right (Parameters.base security ^ 96) hqEight
    simpa only [Parameters.legCount_eq, Parameters.bodySize_eq, mul_assoc, ← pow_add] using h
  have h96 : 4 ≤ Parameters.base security ^ 96 := by
    have h := Nat.pow_le_pow_left (Parameters.base_ge_two security) 96
    norm_num at h
    omega
  have hqFour : 4 * Parameters.modulus security ≤ Parameters.bodySize security := by
    have h := Nat.mul_le_mul_left (Parameters.modulus security) h96
    simpa only [Parameters.bodySize_eq, mul_comm _ 4] using h
  have hbody : 65536 * Parameters.base security ^ 160 ≤ Parameters.bodySize security := by
    have h := Nat.mul_le_mul_right (Parameters.base security ^ 96) hqLower
    simpa only [Parameters.bodySize_eq, mul_assoc, ← pow_add] using h
  unfold ordinaryPool
  omega

theorem ordinaryPool_pos (security : ℕ) : 0 < ordinaryPool security :=
  (pow_pos (Parameters.base_pos security) _).trans_le (ordinaryPool_lower security)

theorem primaryFactor_eq (security : ℕ) :
    primaryFactor security = 1 / (Parameters.base security : ℝ) ^ 64 := by
  have hb := FirstResponse.base_pos security
  unfold primaryFactor
  rw [Parameters.legCount_eq, Nat.cast_pow,
    show 128 = 64 * 2 by omega, pow_mul, Real.sqrt_sq (pow_nonneg hb.le _)]
  simp only [one_div]

theorem radius_le_base (security : ℕ) : radius security ≤ Parameters.base security := by
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (show 1 ≤ Parameters.base security by
    have := Parameters.base_ge_two security; omega)
  simpa only [radius, Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hb1 (show (1 / 4 : ℝ) ≤ 1 by norm_num)

theorem bodyFactor_le (security : ℕ) : bodyFactor security ≤ 1 / (Parameters.base security : ℝ) ^ 79 := by
  have hb := FirstResponse.base_pos security
  have hpool : (Parameters.base security : ℝ) ^ 160 ≤ ordinaryPool security := by exact_mod_cast ordinaryPool_lower security
  have hsqrt : (Parameters.base security : ℝ) ^ 80 ≤ Real.sqrt (ordinaryPool security : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hpool]
  have hpoolPos : (0 : ℝ) < ordinaryPool security := Nat.cast_pos.mpr (ordinaryPool_pos security)
  calc
    _ = radius security / Real.sqrt (ordinaryPool security : ℝ) := by rfl
    _ ≤ (Parameters.base security : ℝ) / Real.sqrt (ordinaryPool security : ℝ) :=
      div_le_div_of_nonneg_right (radius_le_base security) (Real.sqrt_nonneg _)
    _ ≤ (Parameters.base security : ℝ) / (Parameters.base security : ℝ) ^ 80 :=
      div_le_div_of_nonneg_left hb.le (pow_pos hb _) hsqrt
    _ = _ := by field_simp

def freeAtomEnvelope (security : ℕ) : ℝ :=
  primaryFactor security * Real.sqrt (∑ color, (primaryLaw security).weight color * primaryCertificateDensity security color ^ 2) +
  bodyFactor security * Real.sqrt (∑ color, (centerLaw security).weight color * bodyCertificateDensity security color ^ 2)

def translationAtomEnvelope (security : ℕ) (shift : ℤ) : ℝ :=
  primaryFactor security *
    (Real.sqrt (∑ color, (primaryLaw security).weight color * primaryCertificateDensity security color ^ 2) +
      Real.sqrt (∑ color, (primaryLaw security).weight color * residualCertificateDensity security shift color ^ 2)) +
  bodyFactor security * Real.sqrt (∑ color, (centerLaw security).weight color * safeSeedDensity security shift color ^ 2)

theorem freeAtomEnvelope_nonneg (security : ℕ) : 0 ≤ freeAtomEnvelope security := by
  unfold freeAtomEnvelope primaryFactor bodyFactor radius
  positivity

theorem translationAtomEnvelope_nonneg (security : ℕ) (shift : ℤ) : 0 ≤ translationAtomEnvelope security shift := by
  unfold translationAtomEnvelope primaryFactor bodyFactor radius
  positivity

theorem freeAtomEnvelope_decay (security : ℕ) :
    freeAtomEnvelope security ≤ 84 / (Parameters.base security : ℝ) ^ 110 := by
  have hb := FirstResponse.base_pos security
  have hfirst := mul_le_mul (le_of_eq (primaryFactor_eq security)) (primaryCertificateDensity_norm_decay security)
    (Real.sqrt_nonneg _) (by positivity : (0 : ℝ) ≤ 1 / (Parameters.base security : ℝ) ^ 64)
  have hsecond := mul_le_mul (bodyFactor_le security) (bodyCertificateDensity_norm_decay security)
    (Real.sqrt_nonneg _) (by positivity : (0 : ℝ) ≤ 1 / (Parameters.base security : ℝ) ^ 79)
  calc
    _ ≤ (1 / (Parameters.base security : ℝ) ^ 64) * (20 / (Parameters.base security : ℝ) ^ 46) +
      (1 / (Parameters.base security : ℝ) ^ 79) * (64 / (Parameters.base security : ℝ) ^ 31) := add_le_add hfirst hsecond
    _ = _ := by ring

theorem translationAtomEnvelope_decay (security : ℕ) (shift : ℤ) :
    translationAtomEnvelope security shift ≤ 56 / (Parameters.base security : ℝ) ^ 79 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (show 1 ≤ Parameters.base security by
    have := Parameters.base_ge_two security; omega)
  have hsum := add_le_add (primaryCertificateDensity_norm_decay security) (residualCertificateDensity_norm_decay security shift)
  have hfirst := mul_le_mul (le_of_eq (primaryFactor_eq security)) hsum
    (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by positivity : (0 : ℝ) ≤ 1 / (Parameters.base security : ℝ) ^ 64)
  have hsecond := mul_le_mul (bodyFactor_le security) (safeSeedDensity_norm_le_four security shift)
    (Real.sqrt_nonneg _) (by positivity : (0 : ℝ) ≤ 1 / (Parameters.base security : ℝ) ^ 79)
  have hpower : 52 / (Parameters.base security : ℝ) ^ 110 ≤ 52 / (Parameters.base security : ℝ) ^ 79 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _) (pow_le_pow_right₀ hb1 (by omega))
  calc
    _ ≤ (1 / (Parameters.base security : ℝ) ^ 64) *
        (20 / (Parameters.base security : ℝ) ^ 46 + 32 / (Parameters.base security : ℝ) ^ 46) +
      (1 / (Parameters.base security : ℝ) ^ 79) * 4 := add_le_add hfirst hsecond
    _ = 52 / (Parameters.base security : ℝ) ^ 110 + 4 / (Parameters.base security : ℝ) ^ 79 := by ring
    _ ≤ 52 / (Parameters.base security : ℝ) ^ 79 + 4 / (Parameters.base security : ℝ) ^ 79 :=
      add_le_add hpower le_rfl
    _ = _ := by ring

theorem free_population_quadratic_budget (security : ℕ) :
    (Parameters.bodySize security : ℝ) * freeAtomEnvelope security ^ 2 ≤
      924844032 / (Parameters.base security : ℝ) ^ 60 := by
  have hb := FirstResponse.base_pos security
  have hbody : (Parameters.bodySize security : ℝ) ≤ 131072 * (Parameters.base security : ℝ) ^ 160 := by
    have h := Nat.mul_le_mul_right (Parameters.base security ^ 96) (Parameters.modulus_bounds security).2
    exact_mod_cast (by simpa only [Parameters.bodySize_eq, mul_assoc, ← pow_add] using h)
  have hsquare := pow_le_pow_left₀ (freeAtomEnvelope_nonneg security) (freeAtomEnvelope_decay security) 2
  calc
    _ ≤ (131072 * (Parameters.base security : ℝ) ^ 160) * (84 / (Parameters.base security : ℝ) ^ 110) ^ 2 :=
      mul_le_mul hbody hsquare (sq_nonneg _) (by positivity)
    _ = _ := by field_simp; ring

theorem queue_population_quadratic_budget (security : ℕ) (shift : ℤ) :
    (Parameters.modulus security : ℝ) * translationAtomEnvelope security shift ^ 2 ≤
      411041792 / (Parameters.base security : ℝ) ^ 94 := by
  have hb := FirstResponse.base_pos security
  have hq : (Parameters.modulus security : ℝ) ≤ 131072 * (Parameters.base security : ℝ) ^ 64 := by
    exact_mod_cast (Parameters.modulus_bounds security).2
  have hsquare := pow_le_pow_left₀ (translationAtomEnvelope_nonneg security shift)
    (translationAtomEnvelope_decay security shift) 2
  calc
    _ ≤ (131072 * (Parameters.base security : ℝ) ^ 64) * (56 / (Parameters.base security : ℝ) ^ 79) ^ 2 :=
      mul_le_mul hq hsquare (sq_nonneg _) (by positivity)
    _ = _ := by field_simp; ring



end

end CurrentAFT.BackgroundRates

end

section



/-!
# Ambient Fourier energy for real signed masses

The frequency space is the actual group of all complex additive characters
of a finite abelian group. Its orthogonality and completeness are proved by
mathlib's finite Pontryagin duality, rather than assumed as a character-table
hypothesis. In particular the results apply to `Fin dimension → ZMod modulus`.
The final section proves the bijection with the manuscript's coordinate-indexed
positive-sign characters and reindexes the complete nonzero spectral sum.
-/

namespace CurrentAFT

open scoped BigOperators ComplexConjugate Classical

noncomputable section

variable {Group : Type*} [Fintype Group] [AddCommGroup Group]

/-- Unnormalized positive-sign Fourier transform of a finite complex mass. -/
def characterFourier (mass : Group → ℂ) (frequency : AddChar Group ℂ) : ℂ :=
  ∑ point, mass point * frequency point









/-- The signed real mass convention of the current manuscript. -/
def signedFourier (mass : Group → ℝ) (frequency : AddChar Group ℂ) : ℂ :=
  characterFourier (fun point => (mass point : ℂ)) frequency

/-- Difference between a real signed mass and ambient uniformity. -/
def uniformDeviation (mass : Group → ℝ) (point : Group) : ℝ :=
  mass point - (Fintype.card Group : ℝ)⁻¹

@[simp] theorem signedFourier_zero (mass : Group → ℝ) :
    signedFourier mass 0 = (∑ point, mass point : ℝ) := by
  simp [signedFourier, characterFourier]













section Coordinates

variable {Index : Type*} [Fintype Index]
    {modulus : ℕ} [NeZero modulus]

/-- The manuscript's positive-sign coordinate character, constructed from
mathlib's characters `exp(2 π i frequency * point / modulus)` on `ZMod`.
The modulus need only be nonzero; primality is unnecessary for Fourier theory. -/
def coordinateCharacter (frequency : Index → ZMod modulus) :
    AddChar (Index → ZMod modulus) ℂ where
  toFun point := ∏ index, AddChar.zmodAddEquiv (frequency index) (point index)
  map_zero_eq_one' := by simp
  map_add_eq_mul' first second := by
    simp [AddChar.map_add_eq_mul, Finset.prod_mul_distrib]

/-- Exact coordinate product formula. -/
theorem coordinateCharacter_apply (frequency point : Index → ZMod modulus) :
    coordinateCharacter frequency point =
      ∏ index, AddChar.zmodAddEquiv (frequency index) (point index) := rfl





@[simp] theorem coordinateCharacter_zero :
    coordinateCharacter (0 : Index → ZMod modulus) = 0 := by
  ext point
  rw [coordinateCharacter_apply]
  simp only [Pi.zero_apply, map_zero, AddChar.zero_apply, Finset.prod_const_one]

variable [DecidableEq Index]

/-- Evaluation on one coordinate identifies the corresponding frequency. -/
@[simp] theorem coordinateCharacter_single (frequency : Index → ZMod modulus)
    (index : Index) (point : ZMod modulus) :
    coordinateCharacter frequency (Pi.single index point) =
      AddChar.zmodAddEquiv (frequency index) point := by
  rw [coordinateCharacter_apply]
  rw [Finset.prod_eq_single index]
  · simp only [Pi.single_apply, ite_true]
  · intro other _ hne
    simp only [Pi.single_apply, if_neg hne, AddChar.map_zero_eq_one]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ index))

/-- All coordinate characters are distinct. -/
theorem coordinateCharacter_injective :
    Function.Injective (coordinateCharacter (Index := Index) (modulus := modulus)) := by
  intro first second hequal
  funext index
  apply AddChar.zmodAddEquiv.injective
  ext point
  have heval := congrArg
    (fun character : AddChar (Index → ZMod modulus) ℂ =>
      character (Pi.single index point)) hequal
  simpa only [coordinateCharacter_single] using heval

/-- Coordinate frequency vectors enumerate the whole dual group, with no
missing or repeated frequencies. Completeness uses finite Pontryagin duality. -/
def coordinateCharacterEquiv : (Index → ZMod modulus) ≃
    AddChar (Index → ZMod modulus) ℂ :=
  Equiv.ofBijective coordinateCharacter
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨coordinateCharacter_injective, AddChar.card_eq.symm⟩)

@[simp] theorem coordinateCharacterEquiv_apply (frequency : Index → ZMod modulus) :
    coordinateCharacterEquiv frequency = coordinateCharacter frequency := rfl







end Coordinates

end

end CurrentAFT

end

section













/-!
# The actual protected latent cycle and its Fourier response

Independent latent edge scalars are sampled first, and every root is their
cyclic difference, including the closing edge. The endpoint law is a
pushforward of this whole product experiment; its roots are not replaced by
independent samples of their one-coordinate marginal.

The identities below are exact finite-distribution identities. Quantitative
centered likelihood bounds for randomly selected paths and the complete
calibration response-norm estimate remain separate obligations.
-/

namespace CurrentAFT.ProtectedCycle

open AFT
open scoped BigOperators Classical

noncomputable section

/-- The entire cyclic difference law of independent finite latent scalars. -/
def cycleLaw {Scalar : Type*} [Fintype Scalar] (body modulus : ℕ) [NeZero modulus]
    (edgeLaw : FiniteDist Scalar) (value : Scalar → ZMod modulus) :
    FiniteDist (Fin body → ZMod modulus) :=
  (FiniteDist.independent (fun _ : Fin body => edgeLaw)).map
    (fun latent => PublicCharge.cycleDifference (fun vertex => value (latent vertex)))









/-- One-coordinate positive-sign transform of the latent scalar law. -/
def scalarFourier {Scalar : Type*} [Fintype Scalar] {modulus : ℕ} [NeZero modulus]
    (edgeLaw : FiniteDist Scalar) (value : Scalar → ZMod modulus)
    (frequency : ZMod modulus) : ℂ :=
  ∑ scalar, (edgeLaw.weight scalar : ℂ) * AddChar.zmodAddEquiv frequency (value scalar)

@[simp] theorem scalarFourier_zero {Scalar : Type*} [Fintype Scalar]
    {modulus : ℕ} [NeZero modulus] (edgeLaw : FiniteDist Scalar)
    (value : Scalar → ZMod modulus) : scalarFourier edgeLaw value 0 = 1 := by
  simp only [scalarFourier, map_zero, AddChar.zero_apply, mul_one,
    ← Complex.ofReal_sum, edgeLaw.sum_one, Complex.ofReal_one]



















/-- Exact coordinate splitting using the same decidability and product
space instances as the latent law. -/
theorem independent_expectation_split {Index Scalar : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Scalar]
    (reference : Index → FiniteDist Scalar) (index : Index) (test : (Index → Scalar) → ℝ) :
    (FiniteDist.independent reference).expectation test =
      ∑ rest : {other : Index // other ≠ index} → Scalar,
        (∏ other : {other : Index // other ≠ index}, (reference other).weight (rest other)) *
          ∑ value, (reference index).weight value *
            test ((Equiv.funSplitAt index Scalar).symm (value, rest)) := by
  unfold FiniteDist.expectation FiniteDist.independent
  rw [← (Equiv.funSplitAt index Scalar).symm.sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro rest _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro value _
  have hproduct :
      (∏ other, (reference other).weight ((Equiv.funSplitAt index Scalar).symm (value, rest) other)) =
      (reference index).weight value *
        ∏ other : {other : Index // other ≠ index}, (reference other).weight (rest other) := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ index]
    apply congrArg₂ (· * ·)
    · simp [Equiv.funSplitAt, Equiv.piSplitAt]
    · apply Finset.prod_congr rfl
      intro other _
      simp [Equiv.funSplitAt, Equiv.piSplitAt, other.property]
  change (∏ other, (reference other).weight
    ((Equiv.funSplitAt index Scalar).symm (value, rest) other)) * _ = _
  rw [hproduct]
  ring

/-- A single latent coordinate has its prescribed independent marginal. -/
theorem independent_single_expectation {Index Scalar : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Scalar]
    (reference : Index → FiniteDist Scalar) (index : Index) (test : Scalar → ℝ) :
    (FiniteDist.independent reference).expectation (fun latent => test (latent index)) =
      (reference index).expectation test := by
  rw [independent_expectation_split reference index]
  simp only [Equiv.funSplitAt, Equiv.piSplitAt, Equiv.coe_fn_symm_mk, dite_true]
  rw [← Finset.sum_mul]
  have hmass := (FiniteDist.independent
    (fun rest : {other : Index // other ≠ index} => reference rest)).sum_one
  change (∑ rest : {other : Index // other ≠ index} → Scalar,
    ∏ other : {other : Index // other ≠ index}, (reference other).weight (rest other)) = 1 at hmass
  rw [hmass, one_mul]
  rfl

/-- Any two different latent coordinates have their actual product law. -/
theorem independent_pair_expectation {Index Scalar : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Scalar]
    (reference : Index → FiniteDist Scalar) (first second : Index) (hdistinct : second ≠ first)
    (test : Scalar → Scalar → ℝ) :
    (FiniteDist.independent reference).expectation
        (fun latent => test (latent first) (latent second)) =
      ∑ firstValue, ∑ secondValue, (reference first).weight firstValue *
        (reference second).weight secondValue * test firstValue secondValue := by
  rw [independent_expectation_split reference first]
  have heval (value : Scalar) (rest : {other : Index // other ≠ first} → Scalar) :
      test ((Equiv.funSplitAt first Scalar).symm (value, rest) first)
        ((Equiv.funSplitAt first Scalar).symm (value, rest) second) =
      test value (rest ⟨second, hdistinct⟩) := by
    simp [Equiv.funSplitAt, Equiv.piSplitAt, hdistinct]
  simp_rw [heval, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro firstValue _
  let restReference := fun other : {other : Index // other ≠ first} => reference other
  have hsingle := independent_single_expectation restReference ⟨second, hdistinct⟩
    (test firstValue)
  have hrewrite :
      (∑ rest : {other : Index // other ≠ first} → Scalar,
        (∏ other : {other : Index // other ≠ first}, (reference other).weight (rest other)) *
          ((reference first).weight firstValue * test firstValue (rest ⟨second, hdistinct⟩))) =
      (reference first).weight firstValue *
        (FiniteDist.independent restReference).expectation
          (fun rest => test firstValue (rest ⟨second, hdistinct⟩)) := by
    unfold FiniteDist.expectation FiniteDist.independent restReference
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro rest _
    ring
  rw [hrewrite, hsingle, FiniteDist.expectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro secondValue _
  ring



/-- Actual one-root difference convolution. -/
def differenceLaw {Scalar : Type*} [Fintype Scalar] {modulus : ℕ} [NeZero modulus]
    (edgeLaw : FiniteDist Scalar) (value : Scalar → ZMod modulus) : FiniteDist (ZMod modulus) :=
  (edgeLaw.prod edgeLaw).map (fun pair => value pair.1 - value pair.2)



/-- In an actual cycle with at least two vertices, the predecessor is different. -/
theorem cycle_predecessor_ne (body : ℕ) (hbody : 2 ≤ body) (vertex : Fin body) :
    (finRotate body).symm vertex ≠ vertex := by
  intro hfixed
  have hnext : finRotate body vertex = vertex := by
    have h := congrArg (finRotate body) hfixed
    simpa only [Equiv.apply_symm_apply] using h.symm
  cases body with
  | zero => omega
  | succ length =>
    have hvalue := congrArg Fin.val hnext
    by_cases hlast : vertex = Fin.last length
    · subst vertex
      simp only [finRotate_last, Fin.val_zero, Fin.val_last] at hvalue
      omega
    · rw [coe_finRotate, if_neg hlast] at hvalue
      omega











end

end CurrentAFT.ProtectedCycle

end

section





/-!
# Finite-support path likelihood from the actual latent sampling law

The path is sampled by an initial latent scalar and one fresh independent
scalar for each edge. The transfer matrix has entries
`sqrt(p u) * sqrt(p v) * 1_{difference u v = color}`. Repeated finite
Cauchy--Schwarz proves the joint point-mass bound; it is not a hypothesis.
-/

namespace CurrentAFT.PathLikelihood

open AFT
open scoped BigOperators Classical

noncomputable section

variable {Scalar Difference : Type*} [Fintype Scalar] [Fintype Difference]

/-- The actual law of one difference of two independent latent scalars. -/
def marginal (source : FiniteDist Scalar) (difference : Scalar → Scalar → Difference) :
    FiniteDist Difference :=
  (source.prod source).map (fun pair => difference pair.1 pair.2)





def boundary (source : FiniteDist Scalar) (scalar : Scalar) : ℝ :=
  Real.sqrt (source.weight scalar)

def transfer (source : FiniteDist Scalar) (difference : Scalar → Scalar → Difference)
    (color : Difference) (first second : Scalar) : ℝ :=
  if difference first second = color then boundary source first * boundary source second else 0

def squareSum (vector : Scalar → ℝ) : ℝ := ∑ scalar, vector scalar ^ 2

@[simp] theorem boundary_sq (source : FiniteDist Scalar) (scalar : Scalar) :
    boundary source scalar ^ 2 = source.weight scalar :=
  Real.sq_sqrt (source.nonneg scalar)

@[simp] theorem boundary_squareSum (source : FiniteDist Scalar) : squareSum (boundary source) = 1 := by
  simp only [squareSum, boundary_sq, source.sum_one]



/-- The actual Frobenius energy equals the one-difference marginal mass. -/
theorem transfer_square_sum (source : FiniteDist Scalar)
    (difference : Scalar → Scalar → Difference) (color : Difference) :
    (∑ first, ∑ second, transfer source difference color first second ^ 2) =
      (marginal source difference).weight color := by
  simp only [marginal, FiniteDist.map_weight, Fintype.sum_prod_type, FiniteDist.prod_weight]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  unfold transfer
  split_ifs
  · rw [mul_pow, boundary_sq, boundary_sq]
  · norm_num





























/-- True integer difference, encoded in its finite safe interval. -/
def windowDifference (cutoff : ℕ) (first second : GaussianSource.Window cutoff) :
    GaussianSource.Window (2 * cutoff) :=
  ⟨(second : ℤ) - (first : ℤ), by
    have hfirst := Finset.mem_Icc.mp first.property
    have hsecond := Finset.mem_Icc.mp second.property
    apply Finset.mem_Icc.mpr
    push_cast
    constructor <;> omega⟩

@[simp] theorem windowDifference_val (cutoff : ℕ)
    (first second : GaussianSource.Window cutoff) :
    (windowDifference cutoff first second : ℤ) = (second : ℤ) - (first : ℤ) := rfl

theorem windowDifference_card (cutoff : ℕ) :
    Fintype.card (GaussianSource.Window (2 * cutoff)) = 4 * cutoff + 1 := by
  simp only [GaussianSource.Window, Fintype.card_coe, Int.card_Icc]
  omega







/-- The explicit head-and-tail bijection for the independent latent word. -/
def latentConsEquiv (length : ℕ) : (Scalar × (Fin length → Scalar)) ≃ (Fin (length + 1) → Scalar) where
  toFun pair := Fin.cons pair.1 pair.2
  invFun word := (word 0, fun index => word index.succ)
  left_inv pair := by cases pair; rfl
  right_inv word := by ext index; refine Fin.cases rfl (fun _ => rfl) index















end

end CurrentAFT.PathLikelihood

end

section





/-!
# Exact protected-cycle response with centers and body relabeling

The body permutation is drawn independently of the latent edges. Its Fourier
response is an average of complete cyclic products, not a product of root
marginal responses. Centers are fixed in the conditional response formula.
These identities define the physical response needed by the calibration
analysis; no response-norm bound is assumed or claimed.
-/

namespace CurrentAFT.ProtectedCycle

open AFT
open scoped BigOperators Classical

noncomputable section



/-- One independently selected body permutation relabels the complete cycle. -/
def relabeledCycleLaw {Scalar : Type*} [Fintype Scalar]
    (body modulus : ℕ) [NeZero modulus] (edgeLaw : FiniteDist Scalar)
    (value : Scalar → ZMod modulus) (permutation : Equiv.Perm (Fin body)) :
    FiniteDist (Fin body → ZMod modulus) :=
  (cycleLaw body modulus edgeLaw value).map
    (fun root vertex => root (permutation.symm vertex))















end

end CurrentAFT.ProtectedCycle

end

section







/-!
# Actual distinct body selections

Selections are finite embeddings and are sampled uniformly before the
latent cycle. Fixed selected coordinates retain their genuine joint law.
This file begins the centered-cycle analysis with the exact singleton
identity and actual two-position adjacency counting. The all-order forest
counting and centered-density norm estimates are separate obligations.
-/

namespace CurrentAFT.CycleSelections

open AFT
open scoped BigOperators Classical

noncomputable section

abbrev Selection (body order : ℕ) := Fin order ↪ Fin body

def initialSelection (body order : ℕ) (horder : order ≤ body) : Selection body order where
  toFun index := ⟨index.val, lt_of_lt_of_le index.isLt horder⟩
  inj' _ _ hequal := Fin.ext (congrArg (fun index : Fin body => index.val) hequal)

def selectionLaw (body order : ℕ) (horder : order ≤ body) : FiniteDist (Selection body order) := by
  letI : Nonempty (Selection body order) := ⟨initialSelection body order horder⟩
  exact FiniteDist.uniform (Selection body order)

theorem selection_card (body order : ℕ) :
    Fintype.card (Selection body order) = body.descFactorial order := by
  simp only [Selection, Fintype.card_embedding_eq, Fintype.card_fin]

/-- The selected roots are a deterministic projection of the whole cycle. -/
def selectedLaw {Scalar : Type*} [Fintype Scalar] (body order modulus : ℕ) [NeZero modulus]
    (source : FiniteDist Scalar) (value : Scalar → ZMod modulus) (sites : Selection body order) :
    FiniteDist (Fin order → ZMod modulus) :=
  (ProtectedCycle.cycleLaw body modulus source value).map (fun root slot => root (sites slot))

/-- Uniform distinct placements are sampled independently of the latent cycle. -/
def averagedSelectedLaw {Scalar : Type*} [Fintype Scalar] (body order modulus : ℕ) [NeZero modulus]
    (horder : order ≤ body) (source : FiniteDist Scalar) (value : Scalar → ZMod modulus) :
    FiniteDist (Fin order → ZMod modulus) :=
  (selectionLaw body order horder).mix (selectedLaw body order modulus source value)















/-- Cycle adjacency in the underlying body, before random placement. -/
def Adjacent (body : ℕ) (first second : Fin body) : Prop :=
  second = finRotate body first ∨ first = finRotate body second

/-- A selected site is isolated among the selected vertices. -/
def Isolated {body order : ℕ} (sites : Selection body order) (slot : Fin order) : Prop :=
  ∀ other, other ≠ slot → ¬Adjacent body (sites slot) (sites other)

/-- The two latent edges used by a body root. -/
def latentSupport {body : ℕ} (vertex : Fin body) : Finset (Fin body) :=
  {vertex, (finRotate body).symm vertex}

/-- Isolated selected roots share no latent scalar with any other selected root. -/
theorem isolated_latentSupport_disjoint {body order : ℕ}
    (sites : Selection body order) (slot other : Fin order) (hne : other ≠ slot)
    (hisolated : Isolated sites slot) :
    Disjoint (latentSupport (sites slot)) (latentSupport (sites other)) := by
  have hsites : sites other ≠ sites slot := fun h => hne (sites.injective h)
  have hnotAdjacent := hisolated other hne
  apply Finset.disjoint_left.mpr
  intro vertex hfirst hsecond
  simp only [latentSupport, Finset.mem_insert, Finset.mem_singleton] at hfirst hsecond
  rcases hfirst with hfirst | hfirst <;> rcases hsecond with hsecond | hsecond
  · exact hsites (hsecond.symm.trans hfirst)
  · apply hnotAdjacent
    left
    have h := congrArg (finRotate body) (hfirst.symm.trans hsecond)
    simpa only [Equiv.apply_symm_apply] using h.symm
  · apply hnotAdjacent
    right
    have h := congrArg (finRotate body) (hsecond.symm.trans hfirst)
    simpa only [Equiv.apply_symm_apply] using h.symm
  · apply hsites
    exact (finRotate body).symm.injective (hsecond.symm.trans hfirst)

/-- Changing the two latent edges of an isolated selected root leaves all
other selected roots unchanged. This preserves their full joint dependence. -/
theorem isolated_other_roots_unchanged {Group : Type*} [AddCommGroup Group]
    {body order : ℕ} (sites : Selection body order) (slot other : Fin order) (hne : other ≠ slot)
    (hisolated : Isolated sites slot) (first second : Fin body → Group)
    (hagree : ∀ vertex ∉ latentSupport (sites slot), first vertex = second vertex) :
    PublicCharge.cycleDifference first (sites other) =
      PublicCharge.cycleDifference second (sites other) := by
  have hdisjoint := isolated_latentSupport_disjoint sites slot other hne hisolated
  have hsite : sites other ∉ latentSupport (sites slot) := by
    intro hmem
    exact Finset.disjoint_left.mp hdisjoint hmem (by simp [latentSupport])
  have hprevious : (finRotate body).symm (sites other) ∉ latentSupport (sites slot) := by
    intro hmem
    exact Finset.disjoint_left.mp hdisjoint hmem (by simp [latentSupport])
  simp only [PublicCharge.cycleDifference, hagree _ hsite, hagree _ hprevious]





















end

end CurrentAFT.CycleSelections

end

section








namespace AFT
end AFT
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments



/-! # Actual independent latent pairs on a cyclic matching -/

namespace CurrentAFT.CycleMatching

open AFT CurrentAFT.CycleSelections
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def IsMatching {body : ℕ} (selected : Finset (Fin body)) : Prop :=
  ∀ first second : selected, first ≠ second → ¬Adjacent body first.val second.val

def pairPosition {body : ℕ} (selected : Finset (Fin body)) (point : selected × Fin 2) : Fin body :=
  if point.2 = 0 then (finRotate body).symm point.1.val else point.1.val

theorem pairPosition_injective (body : ℕ) (hbody : 2 ≤ body)
    (selected : Finset (Fin body)) (hmatching : IsMatching selected) :
    Function.Injective (pairPosition selected) := by
  rintro ⟨first, firstSlot⟩ ⟨second, secondSlot⟩ hequal
  fin_cases firstSlot <;> fin_cases secondSlot
  · have h : (finRotate body).symm first.val = (finRotate body).symm second.val := by simpa [pairPosition] using hequal
    exact Prod.ext (Subtype.ext ((finRotate body).symm.injective h)) rfl
  · have h : (finRotate body).symm first.val = second.val := by simpa [pairPosition] using hequal
    by_cases hsame : first = second
    · subst second
      exact False.elim ((ProtectedCycle.cycle_predecessor_ne body hbody first.val) h)
    · exact False.elim (hmatching first second hsame (Or.inr (by
        have hh := congrArg (finRotate body) h
        simpa only [Equiv.apply_symm_apply] using hh)))
  · have h : first.val = (finRotate body).symm second.val := by simpa [pairPosition] using hequal
    by_cases hsame : first = second
    · subst second
      exact False.elim ((ProtectedCycle.cycle_predecessor_ne body hbody first.val) h.symm)
    · exact False.elim (hmatching first second hsame (Or.inl (by
        have hh := congrArg (finRotate body) h
        simpa only [Equiv.apply_symm_apply] using hh.symm)))
  · have h : first.val = second.val := by simpa [pairPosition] using hequal
    exact Prod.ext (Subtype.ext h) rfl

def pairEmbedding (body : ℕ) (hbody : 2 ≤ body) (selected : Finset (Fin body))
    (hmatching : IsMatching selected) : (selected × Fin 2) ↪ Fin body :=
  ⟨pairPosition selected, pairPosition_injective body hbody selected hmatching⟩

def pairGrouping {Selected Scalar : Type*} : ((Selected × Fin 2) → Scalar) ≃ (Selected → Scalar × Scalar) where
  toFun word := fun selected => (word (selected, 0), word (selected, 1))
  invFun word := fun point => if point.2 = 0 then (word point.1).1 else (word point.1).2
  left_inv word := by funext point; rcases point with ⟨selected, slot⟩; fin_cases slot <;> simp
  right_inv word := by funext selected; simp





/-- One vertex breaks the parity coloring into three genuine matchings,
for odd and even cycle lengths alike. -/
def cycleColor {body : ℕ} (vertex : Fin body) : Fin 3 :=
  if vertex.val = 0 then 2 else if vertex.val % 2 = 0 then 0 else 1



def colorClass (body : ℕ) (color : Fin 3) : Finset (Fin body) :=
  Finset.univ.filter (fun vertex => cycleColor vertex = color)





end

end CurrentAFT.CycleMatching

end

section












/-!
# Dimension-free square-exponential moments of the real dependent cycle

The cyclic sum is decomposed into three matchings. Independence is proved
for the complete latent pairs within each matching; the three matching
sums need not be independent. Convexity of the exponential combines them.
-/

namespace CurrentAFT.CycleMeanMGF

open AFT FiniteConcentration CurrentAFT.CycleMatching
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Hilbert : Type*} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]

















/- Packing the finite product expectation also keeps its dependent `Fintype`
instance fixed when the body is a large public parameter expression. -/
def normalizedCycleMoment {Scalar : Type*} [Fintype Scalar]
    (body population : ℕ) (source : FiniteDist Scalar)
    (response : Fin body → Scalar × Scalar → Hilbert) (parameter : ℝ) : ℝ :=
  (FiniteDist.independent (fun _ : Fin body => source)).expectation
    (fun latent => Real.exp (parameter * ‖(Real.sqrt (population : ℝ))⁻¹ •
      (∑ vertex : Fin body,
        (response vertex (latent ((finRotate body).symm vertex), latent vertex) -
          vectorMean (source.prod source) (response vertex)))‖ ^ 2))





end

end CurrentAFT.CycleMeanMGF

end

section










/-! # Literal normalized finite sums and their centered decomposition -/

namespace CurrentAFT.NormalizedMeanAlgebra

open scoped BigOperators Classical

noncomputable section

def normalizationScale (security : ℕ) : ℝ :=
  (Real.sqrt (Parameters.dimension security : ℝ))⁻¹

variable {Index Hilbert : Type*} [Fintype Index] [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]









section Euclidean

variable {Color : Type*} [Fintype Color]

def euclideanSum (scale : ℝ) (value : Index → EuclideanSpace ℝ Color)
    (offset : EuclideanSpace ℝ Color) : EuclideanSpace ℝ Color :=
  scale • ((∑ index, value index) + offset)







end Euclidean

end

end CurrentAFT.NormalizedMeanAlgebra

end

section












/-! # Actual uniform-reference Hilbert deviations of every pre-root body role -/

namespace CurrentAFT.UniformBodyProfiles

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy BackgroundCertificates FringeCertificate
open scoped BigOperators Classical

noncomputable section

abbrev Palette (security : ℕ) := LocalReferenceEnergy.Palette security

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.safeLaw
  ProposalPrimary.centerLaw LocalReferenceEnergy.uniformReference

def uniformVector (security : ℕ) (profile : Palette security → ℝ) : EuclideanSpace ℝ (Palette security) :=
  ProfileHilbert.whiten (uniformReference security).weight
    (fun color => profile color - (uniformReference security).weight color)

theorem uniformVector_norm_sq (security : ℕ) (profile : Palette security → ℝ) :
    ‖uniformVector security profile‖ ^ 2 =
      (Parameters.modulus security : ℝ) * ∑ color,
        (profile color - (Parameters.modulus security : ℝ)⁻¹) ^ 2 := by
  rw [uniformVector, ProfileHilbert.whiten_norm_sq _ _ (uniformReference security).nonneg]
  unfold profileSquareNorm
  simp only [uniformReference_weight, one_div, div_inv_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro color _
  ring

theorem uniformVector_law_norm_sq (security : ℕ) (law : FiniteDist (Palette security)) :
    ‖uniformVector security law.weight‖ ^ 2 =
      (Parameters.modulus security : ℝ) * ∑ color, law.weight color ^ 2 - 1 := by
  have hq := FirstResponse.modulus_pos security
  rw [uniformVector_norm_sq, Finset.mul_sum]
  have hpoint (color : Palette security) :
      (Parameters.modulus security : ℝ) * (law.weight color - (Parameters.modulus security : ℝ)⁻¹) ^ 2 =
      (Parameters.modulus security : ℝ) * law.weight color ^ 2 - 2 * law.weight color +
        (Parameters.modulus security : ℝ)⁻¹ := by field_simp; ring
  simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [law.sum_one]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- The safe interval's exact chi-square deviation is its actual fringe
mass, rather than an estimate from its largest atom. -/
theorem safe_uniform_energy (security : ℕ) :
    ‖uniformVector security (safeLaw security).weight‖ ^ 2 = fringeMass security := by
  rw [uniformVector_law_norm_sq, fringeMass_height]
  congr 1
  have hsquare (color : Palette security) : (safeLaw security).weight color ^ 2 =
      safeHeight security * (safeLaw security).weight color := by
    rw [safeLaw_weight]
    split_ifs <;> ring
  simp_rw [hsquare, ← Finset.mul_sum, FiniteDist.sum_one, mul_one]

theorem safe_uniform_norm_le (security : ℕ) :
    ‖uniformVector security (safeLaw security).weight‖ ≤ 1 / (Parameters.base security : ℝ) ^ 31 := by
  have hb := FirstResponse.base_pos security
  have hsquare := (safe_uniform_energy security).trans_le (fringeMass_decay security)
  have hpower : (1 / (Parameters.base security : ℝ) ^ 31) ^ 2 =
      1 / (Parameters.base security : ℝ) ^ 62 := by ring
  have hnonneg := norm_nonneg (uniformVector security (safeLaw security).weight)
  have hright : 0 ≤ 1 / (Parameters.base security : ℝ) ^ 31 := by positivity
  nlinarith

theorem bodyCertificate_uniform_energy (security : ℕ) :
    ‖ProfileHilbert.whiten (uniformReference security).weight (bodyCertificateProfile security)‖ ^ 2 ≤
      16384 / (Parameters.base security : ℝ) ^ 62 := by
  rw [ProfileHilbert.whiten_norm_sq _ _ (uniformReference security).nonneg]
  have hpoint (color : Palette security) :
      bodyCertificateProfile security color ^ 2 / (uniformReference security).weight color ≤
        4 * ((centerLaw security).weight color * bodyCertificateDensity security color ^ 2) := by
    have hheight := centerLaw_height security color
    have hq := FirstResponse.modulus_pos security
    have hprofile := congrFun (bodyCertificateDensity_profile security) color
    rw [← hprofile, uniformReference_weight]
    simp only [div_eq_mul_inv, one_mul, inv_inv]
    have hscaled : (Parameters.modulus security : ℝ) * (centerLaw security).weight color ≤ 4 := by
      simpa only [mul_comm] using (le_div_iff₀ hq).mp hheight
    have h := mul_le_mul_of_nonneg_right hscaled
      (mul_nonneg ((centerLaw security).nonneg color) (sq_nonneg (bodyCertificateDensity security color)))
    convert h using 1 <;> first | rfl | ring
  unfold profileSquareNorm
  apply (Finset.sum_le_sum fun color _ => hpoint color).trans
  rw [← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left (bodyCertificateDensity_square_decay security) (by norm_num : (0 : ℝ) ≤ 4)
  exact h.trans_eq (by ring)

theorem bodyCertificate_uniform_norm (security : ℕ) :
    ‖ProfileHilbert.whiten (uniformReference security).weight (bodyCertificateProfile security)‖ ≤
      128 / (Parameters.base security : ℝ) ^ 31 := by
  have h := bodyCertificate_uniform_energy security
  have hright : 0 ≤ 128 / (Parameters.base security : ℝ) ^ 31 := by
    have := FirstResponse.base_pos security; positivity
  have hsquare : (128 / (Parameters.base security : ℝ) ^ 31) ^ 2 =
      16384 / (Parameters.base security : ℝ) ^ 62 := by ring
  nlinarith [norm_nonneg (ProfileHilbert.whiten (uniformReference security).weight (bodyCertificateProfile security))]

/-- The actual compensated center has the same small uniform-reference
deviation scale as the true safe law. -/
theorem center_uniform_norm_le (security : ℕ) :
    ‖uniformVector security (centerLaw security).weight‖ ≤ 129 / (Parameters.base security : ℝ) ^ 31 := by
  have hsplit : uniformVector security (centerLaw security).weight =
      uniformVector security (safeLaw security).weight +
        ProfileHilbert.whiten (uniformReference security).weight (bodyCertificateProfile security) := by
    have hprofile : (fun color => (centerLaw security).weight color - (uniformReference security).weight color) =
        (fun color => (safeLaw security).weight color - (uniformReference security).weight color) +
          bodyCertificateProfile security := by
      funext color
      simp only [Pi.add_apply, bodyCertificateProfile]
      ring
    unfold uniformVector
    rw [hprofile, map_add]
  rw [hsplit]
  exact (norm_add_le _ _).trans ((add_le_add (safe_uniform_norm_le security)
    (bodyCertificate_uniform_norm security)).trans_eq (by ring))

/-- Every deterministic cyclic translation is an exact isometry in the
uniform profile Hilbert space, including atoms crossing the palette end. -/
theorem uniformVector_map_equiv_norm (security : ℕ) (law : FiniteDist (Palette security))
    (permutation : Equiv.Perm (Palette security)) :
    ‖uniformVector security (law.map permutation).weight‖ = ‖uniformVector security law.weight‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [uniformVector_norm_sq, uniformVector_norm_sq]
  simp only [FiniteDist.map_equiv_weight]
  congr 1
  exact permutation.symm.sum_comp (fun color =>
    (law.weight color - (Parameters.modulus security : ℝ)⁻¹) ^ 2)

theorem uniformVector_mix_norm_le {Choice : Type*} [Fintype Choice] (security : ℕ)
    (law : FiniteDist Choice) (channel : Choice → FiniteDist (Palette security))
    (bound : ℝ) (hchannel : ∀ choice, ‖uniformVector security (channel choice).weight‖ ≤ bound) :
    ‖uniformVector security (law.mix channel).weight‖ ≤ bound := by
  rw [uniformVector, ProfileHilbert.whiten_mixture_centered]
  exact FiniteConcentration.vectorMean_norm_le law _ bound hchannel

inductive BodyRole
  | free
  | attachment
  | queue

/-- Actual center law before the cyclic root is added. The attachment
averages its own protected leg scalar, and the common queue is fixed. -/
def preRootLaw (security : ℕ) (role : BodyRole) (queue : ℤ) : FiniteDist (Palette security) :=
  match role with
  | .free => centerLaw security
  | .attachment => (scalarLaw security).mix (fun scalar =>
      (safeLaw security).map (shiftEquiv security scalar.val))
  | .queue => (safeLaw security).map (shiftEquiv security queue)

def deviation (security : ℕ) : ℝ := 129 / (Parameters.base security : ℝ) ^ 31

theorem deviation_nonneg (security : ℕ) : 0 ≤ deviation security := by
  unfold deviation
  have := FirstResponse.base_pos security
  positivity

/-- All three genuine pre-root body roles share the same actual small
uniform-reference deviation, uniformly in the fixed common queue. -/
theorem preRootLaw_norm_le (security : ℕ) (role : BodyRole) (queue : ℤ) :
    ‖uniformVector security (preRootLaw security role queue).weight‖ ≤ deviation security := by
  have hsafe : ‖uniformVector security (safeLaw security).weight‖ ≤ deviation security := by
    apply (safe_uniform_norm_le security).trans
    exact div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 129) (by positivity)
  cases role with
  | free => exact center_uniform_norm_le security
  | attachment =>
    apply uniformVector_mix_norm_le
    intro scalar
    rw [uniformVector_map_equiv_norm]
    exact hsafe
  | queue =>
    rw [preRootLaw, uniformVector_map_equiv_norm]
    exact hsafe

end

end CurrentAFT.UniformBodyProfiles

end

section














/-!
# Actual current-family protected-cycle mean exponential moment

All profile and source inputs below are the actual current center,
safe-interval, protected scalar, and protected edge laws. The fixed role
assignment, independent body permutation, and common queue are arbitrary.
The sufficient security threshold may depend on the fixed exponential
constant, and the resulting bound is uniform in all those fixed data.
-/

namespace CurrentAFT.ActualCycleMeanMGF

open AFT FiniteConcentration DiffuseProfiles ProposalPrimary UniformBodyProfiles
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.scale
  BackgroundRates.radius UniformBodyProfiles.deviation

abbrev Edge (security : ℕ) := GaussianSource.Window (edgeCutoff security)
abbrev BodyIndex (security : ℕ) := Fin (Parameters.bodySize security)
abbrev ProfileSpace (security : ℕ) := EuclideanSpace ℝ (UniformBodyProfiles.Palette security)

/-- Actual translated body-profile deviation at one latent pair. -/
def response (security : ℕ) (roles : BodyIndex security → BodyRole) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (vertex : BodyIndex security)
    (pair : Edge security × Edge security) : ProfileSpace security :=
  uniformVector security ((preRootLaw security (roles (permutation vertex)) queue).map
    (shiftEquiv security (pair.2.val - pair.1.val))).weight



def realizedResponse (security : ℕ) (roles : BodyIndex security → BodyRole) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security) :
    BodyIndex security → ProfileSpace security :=
  fun vertex => response security roles queue permutation vertex
    (latent ((finRotate (Parameters.bodySize security)).symm vertex), latent vertex)





/-- Literal finite Gaussian expectation, with the dependent product-space
enumeration fixed before the current population parameters are inserted. -/
def squareMoment (security : ℕ) (roles : BodyIndex security → BodyRole) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (parameter : ℝ) : ℝ :=
  CycleMeanMGF.normalizedCycleMoment (Parameters.bodySize security) (Parameters.dimension security)
    (edgeLaw security) (response security roles queue permutation) parameter











end

end CurrentAFT.ActualCycleMeanMGF

end

section










/-!
# The complete paired synthesis on joint kernels

The local signed channel is the actual primary/compensator score. Its tensor
power acts on an arbitrary joint density kernel. The tensor Hilbert bound
is obtained from the proved actual local laws, and does not assume that the
kernel is a product of one-coordinate functions.
-/

namespace CurrentAFT.PhysicalSynthesis

open AFT DiffuseProfiles ProposalPrimary PairedResponse
open scoped BigOperators Classical

noncomputable section

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) :=
  Classical.decEq _

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base
  primaryLaw centerLaw InwardAnchor.smoothedAnchorLaw

abbrev Palette (security : ℕ) := Fin (Parameters.modulus security)
abbrev Group (security : ℕ) := Palette security × Palette security





def groupLaw (security : ℕ) : FiniteDist (Group security) :=
  (primaryLaw security).prod (centerLaw security)

/-- The same coefficient function enters the marked primary and its
compensator. The latter is integrated against the actual inward anchor. -/
def pairedChannel (security : ℕ) :
    (Palette security → ℝ) →ₗ[ℝ] (Group security → ℝ) where
  toFun score := fun group => pairedScore security score group.1 group.2
  map_add' first second := by
    funext group
    simp only [pairedScore, compensatorScore, anchorWeightedScore, Pi.add_apply,
      mul_add, Finset.sum_add_distrib, add_div]
    ring
  map_smul' scalar score := by
    funext group
    simp only [pairedScore, compensatorScore, anchorWeightedScore, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    have hsum : (∑ color, (InwardAnchor.smoothedAnchorLaw security color).weight group.2 *
        (primaryLaw security).weight color * (scalar * score color)) =
        scalar * ∑ color, (InwardAnchor.smoothedAnchorLaw security color).weight group.2 *
          (primaryLaw security).weight color * score color := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro color _
      ring
    rw [hsum]
    ring

theorem compensator_square_mean (security : ℕ) (score : Palette security → ℝ) :
    (∑ center, (centerLaw security).weight center * compensatorScore security score center ^ 2) =
      activation security ^ 2 * profileSquareNorm (centerLaw security).weight
        (anchorWeightedScore security score) := by
  calc
    _ = activation security ^ 2 * densitySquareNorm (centerLaw security).weight
        (fun center => anchorWeightedScore security score center / (centerLaw security).weight center) := by
      unfold densitySquareNorm compensatorScore
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro center _
      ring
    _ = _ := by rw [densityScore_square]



theorem pairedChannel_mean (security : ℕ) (score : Palette security → ℝ) :
    (groupLaw security).expectation (pairedChannel security score) =
      (1 - activation security) * (primaryLaw security).expectation score := by
  have hrow (primary : Palette security) :
      (∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
        pairedScore security score primary center) =
        (primaryLaw security).weight primary * score primary -
          (primaryLaw security).weight primary *
            ∑ center, (centerLaw security).weight center * compensatorScore security score center := by
    unfold pairedScore
    simp only [mul_sub, Finset.sum_sub_distrib]
    congr 1
    · rw [show (∑ center, (primaryLaw security).weight primary *
          (centerLaw security).weight center * score primary) =
          (primaryLaw security).weight primary * score primary *
            ∑ center, (centerLaw security).weight center by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro center _; ring]
      rw [FiniteDist.sum_one, mul_one]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro center _
      ring
  change (∑ group, (groupLaw security).weight group * pairedChannel security score group) = _
  simp only [groupLaw, FiniteDist.prod_weight, Fintype.sum_prod_type, pairedChannel,
    LinearMap.coe_mk, AddHom.coe_mk, hrow, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul, compensatorScore_mass]
  unfold FiniteDist.expectation
  ring



/-- The physical lift applies this actual channel in every primary slot,
while retaining the entire body tuple as a parameter. -/
def pairedKernel (security r s : ℕ)
    (kernel : ControlCoordinates.DensityKernel (Primary := Palette security)
      (Body := ActualControls.SafePalette security) r s)
    (groups : Fin r → Group security) (centers : Fin s → ActualControls.SafePalette security) : ℝ :=
  TensorChannel.apply r (fun _ => pairedChannel security) (fun colors => kernel colors centers) groups









/-- Actual paired synthesis at fixed public placement. Both pools are
averaged over distinct groups, with their separate falling factorials. -/
def coefficientWeight (security order primaryPool bodyPool : ℕ)
    (coefficient : ActualControls.Coefficients security order)
    (groups : Fin primaryPool → Group security)
    (centers : Fin bodyPool → ActualControls.SafePalette security) : ℝ :=
  coefficient.1 + ∑ arity : ControlCoordinates.PositiveArity order,
    ControlCoordinates.twoPoolUStatistic primaryPool bodyPool
      (pairedKernel security arity.val.1.val arity.val.2.val (coefficient.2 arity).val) groups centers





end

end CurrentAFT.PhysicalSynthesis

end

section












/-!
# The genuine four-output paired group

The signed mass is obtained by the actual primary score minus its actual
compensator score. The two terms below are exactly the corresponding
finite control sums. The triple retains its same-source scalar; its
attachment center is safe-uniform, while the distinct compensator center
uses the constructed free-center law.
-/

namespace CurrentAFT.PairedReferenceEnergy

open AFT DiffuseProfiles ProposalPrimary PairedResponse FirstHistogram LocalReferenceEnergy
open scoped BigOperators Classical

noncomputable section

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] Parameters.base primaryLaw centerLaw activation

abbrev Palette (security : ℕ) := FirstHistogram.Palette security
abbrev Scalar (security : ℕ) := FirstHistogram.Scalar security

def compensatorAt (security : ℕ) (root : ℤ) : FiniteDist (Palette security) :=
  (centerLaw security).map (shiftEquiv security root)

def signedCompensatorAt (security : ℕ) (root : ℤ) (score : Palette security → ℝ)
    (output : Palette security) : ℝ :=
  (centerLaw security).weight ((shiftEquiv security root).symm output) *
    compensatorScore security score ((shiftEquiv security root).symm output)

theorem signedCompensatorAt_channel (security : ℕ) (root : ℤ) (score : Palette security → ℝ)
    (output : Palette security) :
    signedCompensatorAt security root score output =
      ∑ center, (centerLaw security).weight center * compensatorScore security score center *
        atom (shiftEquiv security root center) output := by
  classical
  have hequal (center : Palette security) : shiftEquiv security root center = output ↔
      center = (shiftEquiv security root).symm output := (Equiv.eq_symm_apply _).symm
  simp only [atom, hequal, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    signedCompensatorAt]

theorem compensatorAt_energy (security : ℕ) (root : ℤ) :
    profileSquareNorm (uniformReference security).weight (compensatorAt security root).weight ≤ 4 := by
  have hq := FirstResponse.modulus_pos security
  have h := BlockDensity.profile_energy_le_ratio (uniformReference security).weight
    (compensatorAt security root).weight 4
    (fun color => by rw [uniformReference_weight]; exact one_div_pos.mpr hq)
    (compensatorAt security root).nonneg (fun color => by
      rw [compensatorAt, FiniteDist.map_equiv_weight, uniformReference_weight]
      exact (centerLaw_height security _).trans_eq (by ring))
  simpa only [FiniteDist.sum_one, mul_one] using h

theorem signedCompensatorAt_energy (security : ℕ) (root : ℤ) (score : Palette security → ℝ) :
    profileSquareNorm (uniformReference security).weight (signedCompensatorAt security root score) ≤
      1024 * activation security * (primaryLaw security).expectation (fun primary => score primary ^ 2) := by
  have hq := FirstResponse.modulus_pos security
  have hfirst : profileSquareNorm (uniformReference security).weight (signedCompensatorAt security root score) ≤
      4 * ∑ center, (centerLaw security).weight center * compensatorScore security score center ^ 2 := by
    unfold profileSquareNorm
    rw [← (shiftEquiv security root).sum_comp]
    simp only [signedCompensatorAt, Equiv.symm_apply_apply, uniformReference_weight]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro center _
    have hheight := centerLaw_height security center
    have hnonneg := (centerLaw security).nonneg center
    have hpoint := mul_le_mul_of_nonneg_right hheight
      (mul_nonneg hnonneg (sq_nonneg (compensatorScore security score center)))
    apply (div_le_iff₀ (one_div_pos.mpr hq)).mpr
    convert hpoint using 1 <;> ring
  rw [PhysicalSynthesis.compensator_square_mean] at hfirst
  have hcomp := compensator_energy_le security score
  change activation security ^ 2 * profileSquareNorm (centerLaw security).weight
    (anchorWeightedScore security score) ≤
      256 * activation security * (primaryLaw security).expectation (fun primary => score primary ^ 2) at hcomp
  calc
    _ ≤ 4 * (activation security ^ 2 * profileSquareNorm (centerLaw security).weight
        (anchorWeightedScore security score)) := hfirst
    _ ≤ 4 * (256 * activation security * (primaryLaw security).expectation (fun primary => score primary ^ 2)) :=
      mul_le_mul_of_nonneg_left hcomp (by norm_num)
    _ = _ := by ring

def pairedMassAt (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (score : Palette security → ℝ) (word : Fin 4 → Palette security) : ℝ :=
  PhysicalBlockTensors.compensatedTripleMass (compensatorAt security compensatorRoot).weight
      (tripleMassAt security attachmentRoot scalar score) word -
    PhysicalBlockTensors.compensatedTripleMass (signedCompensatorAt security compensatorRoot score)
      (tripleMassAt security attachmentRoot scalar (fun _ => 1)) word

theorem pairBudget_nonneg (security : ℕ) : 0 ≤ pairBudget security := by
  unfold pairBudget primaryMaximum
  have hmark := (markMass_pos security).le
  positivity

 theorem profileEnergy_sub_le {Output : Type*} [Fintype Output]
    (reference first second : Output → ℝ) (href : ∀ output, 0 ≤ reference output) :
    profileSquareNorm reference (fun output => first output - second output) ≤
      2 * profileSquareNorm reference first + 2 * profileSquareNorm reference second := by
  simp only [profileSquareNorm, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro output _
  have h : (first output - second output) ^ 2 ≤ 2 * first output ^ 2 + 2 * second output ^ 2 := by
    nlinarith [sq_nonneg (first output + second output)]
  exact (div_le_div_of_nonneg_right h (href output)).trans_eq (by ring)

/-- All four coordinates are present in the same signed mass. The two
terms arise from the actual paired numerator, not separate control laws. -/
theorem pairedMassAt_energy (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (score : Palette security → ℝ) :
    profileSquareNorm (FiniteDist.independent (fun _ : Fin 4 => uniformReference security)).weight
      (pairedMassAt security compensatorRoot attachmentRoot scalar score) ≤
        (4128 * pairBudget security) * (primaryLaw security).expectation (fun primary => score primary ^ 2) := by
  let reference := FiniteDist.independent (fun _ : Fin 4 => uniformReference security)
  have hfirst := PhysicalBlockTensors.compensated_triple_density_energy (uniformReference security)
    (compensatorAt security compensatorRoot).weight (tripleMassAt security attachmentRoot scalar score)
  have hsecond := PhysicalBlockTensors.compensated_triple_density_energy (uniformReference security)
    (signedCompensatorAt security compensatorRoot score) (tripleMassAt security attachmentRoot scalar (fun _ => 1))
  change densitySquareNorm reference.weight (fun word =>
    PhysicalBlockTensors.compensatedTripleMass (compensatorAt security compensatorRoot).weight
      (tripleMassAt security attachmentRoot scalar score) word / reference.weight word) = _ at hfirst
  rw [densityScore_square] at hfirst
  change densitySquareNorm reference.weight (fun word =>
    PhysicalBlockTensors.compensatedTripleMass (signedCompensatorAt security compensatorRoot score)
      (tripleMassAt security attachmentRoot scalar (fun _ => 1)) word / reference.weight word) = _ at hsecond
  rw [densityScore_square] at hsecond
  have hfirst' : profileSquareNorm reference.weight
      (PhysicalBlockTensors.compensatedTripleMass (compensatorAt security compensatorRoot).weight
        (tripleMassAt security attachmentRoot scalar score)) ≤
      16 * pairBudget security * (primaryLaw security).expectation (fun primary => score primary ^ 2) := by
    rw [hfirst]
    have htriple := tripleMassAt_energy security attachmentRoot scalar score
    have hcomp := compensatorAt_energy security compensatorRoot
    have hnonnegative := profileSquareNorm_nonneg (uniformReference security).weight
      (compensatorAt security compensatorRoot).weight (uniformReference security).nonneg
    have hinput := (primaryLaw security).l2Sq_nonneg score
    calc
      _ ≤ profileSquareNorm (uniformReference security).weight (compensatorAt security compensatorRoot).weight *
          ((4 * pairBudget security) * (primaryLaw security).expectation (fun primary => score primary ^ 2)) :=
        mul_le_mul_of_nonneg_left htriple hnonnegative
      _ ≤ 4 * ((4 * pairBudget security) * (primaryLaw security).expectation (fun primary => score primary ^ 2)) :=
        mul_le_mul_of_nonneg_right hcomp (by
          change 0 ≤ (4 * pairBudget security) * (primaryLaw security).l2Sq score
          exact mul_nonneg (mul_nonneg (by norm_num) (pairBudget_nonneg security)) hinput)
      _ = _ := by ring
  have hsecond' : profileSquareNorm reference.weight
      (PhysicalBlockTensors.compensatedTripleMass (signedCompensatorAt security compensatorRoot score)
        (tripleMassAt security attachmentRoot scalar (fun _ => 1))) ≤
      2048 * pairBudget security * (primaryLaw security).expectation (fun primary => score primary ^ 2) := by
    rw [hsecond]
    have htriple := tripleMassAt_energy security attachmentRoot scalar (fun _ => 1)
    simp only [one_pow, FiniteDist.expectation_const, mul_one] at htriple
    have hcomp := signedCompensatorAt_energy security compensatorRoot score
    have hnonnegative := profileSquareNorm_nonneg (uniformReference security).weight
      (signedCompensatorAt security compensatorRoot score) (uniformReference security).nonneg
    have hinput := (primaryLaw security).l2Sq_nonneg score
    have ha := activation_le_half security
    calc
      _ ≤ profileSquareNorm (uniformReference security).weight (signedCompensatorAt security compensatorRoot score) *
          (4 * pairBudget security) := mul_le_mul_of_nonneg_left htriple hnonnegative
      _ ≤ (1024 * activation security * (primaryLaw security).expectation (fun primary => score primary ^ 2)) *
          (4 * pairBudget security) := mul_le_mul_of_nonneg_right hcomp
            (mul_nonneg (by norm_num) (pairBudget_nonneg security))
      _ = activation security * (4096 * pairBudget security *
          (primaryLaw security).expectation (fun primary => score primary ^ 2)) := by ring
      _ ≤ (1 / 2) * (4096 * pairBudget security *
          (primaryLaw security).expectation (fun primary => score primary ^ 2)) :=
        mul_le_mul_of_nonneg_right ha (by
          change 0 ≤ 4096 * pairBudget security * (primaryLaw security).l2Sq score
          exact mul_nonneg (mul_nonneg (by norm_num) (pairBudget_nonneg security)) hinput)
      _ = _ := by ring
  have hsum := profileEnergy_sub_le reference.weight
    (PhysicalBlockTensors.compensatedTripleMass (compensatorAt security compensatorRoot).weight
      (tripleMassAt security attachmentRoot scalar score))
    (PhysicalBlockTensors.compensatedTripleMass (signedCompensatorAt security compensatorRoot score)
      (tripleMassAt security attachmentRoot scalar (fun _ => 1))) reference.nonneg
  change profileSquareNorm reference.weight (pairedMassAt security compensatorRoot attachmentRoot scalar score) ≤ _ at hsum
  change profileSquareNorm reference.weight (pairedMassAt security compensatorRoot attachmentRoot scalar score) ≤ _
  nlinarith only [hsum, hfirst', hsecond']



theorem compensatorAt_channel (security : ℕ) (root : ℤ) (output : Palette security) :
    (compensatorAt security root).weight output =
      ∑ center, (centerLaw security).weight center * atom (shiftEquiv security root center) output := by
  classical
  rw [compensatorAt, FiniteDist.map_weight]
  simp only [atom, mul_ite, mul_one, mul_zero]

theorem pairedMassAt_control_sum (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : Scalar security) (score : Palette security → ℝ) (word : Fin 4 → Palette security) :
    pairedMassAt security compensatorRoot attachmentRoot scalar score word =
      ∑ primary, ∑ center, (primaryLaw security).weight primary * (centerLaw security).weight center *
        pairedScore security score primary center *
        (pairAt security primary scalar).weight (word 1, word 2) *
        (attachmentAt security attachmentRoot scalar).weight (word 3) *
        atom (shiftEquiv security compensatorRoot center) (word 0) := by
  unfold pairedMassAt PhysicalBlockTensors.compensatedTripleMass tripleMassAt
  rw [compensatorAt_channel, signedCompensatorAt_channel]
  unfold signedPairAt
  simp only [mul_one]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  conv_lhs => arg 2; ext center; rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro primary _
  apply Finset.sum_congr rfl
  intro center _
  unfold pairedScore
  ring

/-- The positive local channel conditional on the actual two public
controls and the same protected scalar. -/
def controlMass (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (group : PhysicalSynthesis.Group security) (word : Fin 4 → Palette security) : ℝ :=
  (pairAt security group.1 scalar).weight (word 1, word 2) *
    (attachmentAt security attachmentRoot scalar).weight (word 3) *
    atom (shiftEquiv security compensatorRoot group.2) (word 0)

/-- One actual finite public-control sum, with the true paired channel as
its numerator. Every homogeneous coefficient below is extracted from it. -/
def pairedMassLinear (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security) :
    (Palette security → ℝ) →ₗ[ℝ] ((Fin 4 → Palette security) → ℝ) where
  toFun score word := ∑ group, (PhysicalSynthesis.groupLaw security).weight group *
    PhysicalSynthesis.pairedChannel security score group * controlMass security compensatorRoot attachmentRoot scalar group word
  map_add' first second := by
    funext word
    simp only [map_add, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' coefficient score := by
    funext word
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro group _
    ring

theorem pairedMassLinear_apply (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : Scalar security) (score : Palette security → ℝ) :
    pairedMassLinear security compensatorRoot attachmentRoot scalar score =
      pairedMassAt security compensatorRoot attachmentRoot scalar score := by
  funext word
  rw [pairedMassAt_control_sum]
  simp only [pairedMassLinear, LinearMap.coe_mk, AddHom.coe_mk, PhysicalSynthesis.groupLaw,
    FiniteDist.prod_weight, Fintype.sum_prod_type, PhysicalSynthesis.pairedChannel, controlMass]
  apply Finset.sum_congr rfl
  intro primary _
  apply Finset.sum_congr rfl
  intro center _
  ring

/-- The actual symmetric degree coefficient, as a linear map on an
arbitrary primary input score. Its definition is finite extraction from
the physical four-coordinate mass, not a supplied response matrix. -/
def localDegreeLinear (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (degree : ℕ) : (Palette security → ℝ) →ₗ[ℝ] BlockFock.Tensor (Fin degree) (Palette security) :=
  (LocalTensors.degreeTensorLinear (fun _ : Fin 4 => uniformReference security) degree).comp
    (pairedMassLinear security compensatorRoot attachmentRoot scalar)



def jointPairedMass {Root : Type*} [Fintype Root] (security : ℕ) (source : FiniteDist Root)
    (compensatorRoot attachmentRoot : Root → ℤ) (scalar : Root → Scalar security)
    (score : Root → Palette security → ℝ) (word : Fin 4 → Palette security) : ℝ :=
  ∑ root, source.weight root * pairedMassAt security (compensatorRoot root) (attachmentRoot root) (scalar root) (score root) word





end

end CurrentAFT.PairedReferenceEnergy

end

section








/-! # Actual fixed-scalar pair marginals and the sharp first-degree scale -/

namespace CurrentAFT.ReferenceMarginals

open AFT DiffuseProfiles ProposalPrimary FirstHistogram LocalReferenceEnergy
open scoped BigOperators Classical

noncomputable section

abbrev Palette (security : ℕ) := FirstHistogram.Palette security
abbrev Scalar (security : ℕ) := FirstHistogram.Scalar security

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff primaryLaw

 theorem averagedLaw_height (modulus width cutoff : ℕ) (start source : ℤ)
    (hwidth : 0 < width) (hdelete : 2 * (2 + 2 * width + 2 * cutoff) ≤ modulus)
    (hstart : ∀ offset ∈ anchorInterval start width,
      |offset| ≤ 2 * (width : ℤ) + ((cutoff : ℤ) - 1))
    (hsource : |source| ≤ (cutoff : ℤ) - 1) (color : ℤ) :
    TrimmedSlice.averagedLaw modulus 1 start source width color ≤ 2 / (modulus : ℝ) := by
  have hclear : 2 * (1 : ℤ) + (2 * (width : ℤ) + ((cutoff : ℤ) - 1)) +
      ((cutoff : ℤ) - 1) < modulus := by omega
  have h := TrimmedSlice.mixedLaw_le modulus 1
    (2 * (width : ℤ) + ((cutoff : ℤ) - 1)) ((cutoff : ℤ) - 1)
    (fun _ : Unit => start) (fun _ : Unit => source) (FiniteDist.uniform Unit).weight width hwidth.ne'
    (FiniteDist.uniform Unit).nonneg (FiniteDist.uniform Unit).sum_one
    (fun _ => hstart) (fun _ => hsource) hclear color
  simp only [TrimmedSlice.mixedLaw, Fintype.sum_unique, FiniteDist.uniform_weight,
    Fintype.card_unique, Nat.cast_one, inv_one, one_mul] at h
  apply h.trans
  have hq : (0 : ℝ) < modulus := by exact_mod_cast (by omega : 0 < modulus)
  have hd := Nat.cast_le (α := ℝ).mpr hdelete
  push_cast at hd
  have hden : 0 < (modulus : ℝ) - 2 - (2 * width + ((cutoff : ℝ) - 1)) - ((cutoff : ℝ) - 1) := by linarith
  push_cast
  norm_num only [mul_one]
  apply (div_le_div_iff₀ hden hq).mpr
  linarith

theorem diffuseSeedPair_first_marginal (security : ℕ) (positive : Bool) (seed : ActualSeed security)
    (output : Palette security) :
    (∑ second, (diffuseSeedPair security positive seed).weight (output, second)) =
      TrimmedSlice.averagedLaw (Parameters.modulus security) 1
        (intervalStart positive (Parameters.anchorWidth security) (actualBlur security seed))
        (actualSecond security seed) (Parameters.anchorWidth security) output.val := by
  simp_rw [diffuseSeedPair_weight]
  have h := TrimmedSlice.mixedPair_first_marginal (Parameters.modulus security) 1
    (fun _ : Unit => intervalStart positive (Parameters.anchorWidth security) (actualBlur security seed))
    (fun _ : Unit => actualSecond security seed) (FiniteDist.uniform Unit).weight
    (Parameters.anchorWidth security) (by norm_num) output
  simpa only [TrimmedSlice.mixedPair, TrimmedSlice.mixedLaw, Fintype.sum_unique,
    FiniteDist.uniform_weight, Fintype.card_unique, Nat.cast_one, inv_one, one_mul] using h

theorem diffuseSeedPair_marginal_height (security : ℕ) (positive : Bool) (seed : ActualSeed security)
    (output : Palette security) :
    (∑ second, (diffuseSeedPair security positive seed).weight (output, second)) ≤
      2 / (Parameters.modulus security : ℝ) := by
  rw [diffuseSeedPair_first_marginal]
  apply averagedLaw_height _ _ _ _ _ (InwardAnchor.anchorWidth_pos security)
  · exact FirstResponse.two_deletion_le_modulus security
  · exact fun offset hin => interval_bound positive _ _ _ _ (actualBlur_bound security seed) hin
  · exact actualSecond_bound security seed

theorem diffusePairAt_first_height (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (output : Palette security) :
    (∑ second, (diffusePairAt security primary scalar).weight (output, second)) ≤
      2 / (Parameters.modulus security : ℝ) := by
  unfold diffusePairAt
  simp only [FiniteDist.mix_weight]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ coin, (FiniteDist.uniform Bool).weight coin * (2 / (Parameters.modulus security : ℝ)) := by
      apply Finset.sum_le_sum
      intro coin _
      apply mul_le_mul_of_nonneg_left _ (FiniteDist.nonneg _ _)
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      calc
        _ ≤ ∑ edge, (publicBlurLaw security).weight edge * (2 / (Parameters.modulus security : ℝ)) :=
          Finset.sum_le_sum (fun edge _ => mul_le_mul_of_nonneg_left
            (diffuseSeedPair_marginal_height security _ _ output) ((publicBlurLaw security).nonneg edge))
        _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem diffusePairAt_symmetric (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (first second : Palette security) :
    (diffusePairAt security primary scalar).weight (first, second) =
      (diffusePairAt security primary scalar).weight (second, first) := by
  simp only [diffusePairAt, FiniteDist.mix_weight]
  apply Finset.sum_congr rfl
  intro coin _
  congr 1
  apply Finset.sum_congr rfl
  intro edge _
  rw [diffuseSeedPair_weight, diffuseSeedPair_weight]
  simp only [TrimmedSlice.averagedPair, TrimmedSlice.orderedPairSlice_symmetric]

theorem diffusePairAt_second_height (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (output : Palette security) :
    (∑ first, (diffusePairAt security primary scalar).weight (first, output)) ≤
      2 / (Parameters.modulus security : ℝ) := by
  simp_rw [diffusePairAt_symmetric security primary scalar _ output]
  exact diffusePairAt_first_height security primary scalar output

theorem markedCompanionAt_row_sum (security : ℕ) (scalar : Scalar security) (output : Palette security) :
    (∑ primary, (markedCompanionAt security primary scalar).weight output) ≤ 2 := by
  simp only [markedCompanionAt, FiniteDist.mix_weight, FiniteDist.map_equiv_weight]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ edge, (publicBlurLaw security).weight edge * 2 :=
      Finset.sum_le_sum (fun edge _ => mul_le_mul_of_nonneg_left
        (InwardAnchor.shiftedAnchorLaw_row_sum_le_two security (-scalar.val) _ _)
        ((publicBlurLaw security).nonneg edge))
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem markedCompanionAt_primary_height (security : ℕ) (scalar : Scalar security) (output : Palette security) :
    (∑ primary, (primaryLaw security).weight primary * (markedCompanionAt security primary scalar).weight output) ≤
      2 * primaryMaximum security := by
  have hmaximum : 0 ≤ primaryMaximum security :=
    div_nonneg (Nat.cast_nonneg _) (mul_nonneg (markMass_pos security).le (Nat.cast_nonneg _))
  calc
    _ ≤ ∑ primary, primaryMaximum security * (markedCompanionAt security primary scalar).weight output :=
      Finset.sum_le_sum (fun primary _ => mul_le_mul_of_nonneg_right
        (GaussianHeights.primaryLaw_upper security primary) ((markedCompanionAt security primary scalar).nonneg output))
    _ = primaryMaximum security * ∑ primary, (markedCompanionAt security primary scalar).weight output :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ primaryMaximum security * 2 := mul_le_mul_of_nonneg_left
      (markedCompanionAt_row_sum security scalar output) hmaximum
    _ = _ := by ring

end

end CurrentAFT.ReferenceMarginals

end

section












/-!
# Sharp first coefficients of the actual positive local factors

The first coefficient is estimated from its one-coordinate marginals,
not from the much larger full pair density. The resulting square budget
has exponent 31, retaining the half-power needed by the Fourier tail.
-/

namespace CurrentAFT.PositiveFirstCoefficient

open AFT DiffuseProfiles ProposalPrimary FirstHistogram LocalReferenceEnergy ReferenceMarginals PairedReferenceEnergy
open AFT.PhysicalBlockTensors
open scoped BigOperators Classical

noncomputable section

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

abbrev Palette (security : ℕ) := FirstHistogram.Palette security
abbrev Scalar (security : ℕ) := FirstHistogram.Scalar security

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] Parameters.base primaryLaw activation

def meanPairLaw (security : ℕ) (scalar : Scalar security) : FiniteDist (Palette security × Palette security) :=
  (primaryLaw security).mix (fun primary => pairAt security primary scalar)

def meanDiffuseLaw (security : ℕ) (scalar : Scalar security) : FiniteDist (Palette security × Palette security) :=
  (primaryLaw security).mix (fun primary => diffusePairAt security primary scalar)

def meanMarkedCompanion (security : ℕ) (scalar : Scalar security) : FiniteDist (Palette security) :=
  (primaryLaw security).mix (fun primary => markedCompanionAt security primary scalar)

















def heightBudget (security : ℕ) : ℝ := activation security ^ 2 * (Parameters.modulus security : ℝ) * primaryMaximum security





def positiveTripleLaw (security : ℕ) (attachmentRoot : ℤ) (scalar : Scalar security) :
    FiniteDist (Fin 3 → Palette security) :=
  sharedSourceTriple (primaryLaw security) (fun primary => pairAt security primary scalar)
    (fun _ _ _ => attachmentAt security attachmentRoot scalar)













def positiveFourLaw (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security) :
    FiniteDist (Fin 4 → Palette security) :=
  ((compensatorAt security compensatorRoot).prod (positiveTripleLaw security attachmentRoot scalar)).map
    (fun draw => Fin.cons draw.1 draw.2)















theorem positiveTriple_weight (security : ℕ) (attachmentRoot : ℤ) (scalar : Scalar security)
    (word : Fin 3 → Palette security) :
    (positiveTripleLaw security attachmentRoot scalar).weight word =
      tripleMass (tripleMassAt security attachmentRoot scalar (fun _ => 1)) word := by
  rw [positiveTripleLaw, sharedSourceTriple_weight]
  unfold tripleMass BlockDensity.attachedMass tripleMassAt signedPairAt
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro primary _
  ring

def consEquiv (Color : Type*) : (Color × (Fin 3 → Color)) ≃ (Fin 4 → Color) where
  toFun draw := Fin.cons draw.1 draw.2
  invFun word := (word 0, Fin.tail word)
  left_inv draw := by cases draw; rfl
  right_inv word := by ext index; fin_cases index <;> rfl

theorem positiveFour_weight (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (word : Fin 4 → Palette security) :
    (positiveFourLaw security compensatorRoot attachmentRoot scalar).weight word =
      compensatedTripleMass (compensatorAt security compensatorRoot).weight
        (tripleMassAt security attachmentRoot scalar (fun _ => 1)) word := by
  change (((compensatorAt security compensatorRoot).prod (positiveTripleLaw security attachmentRoot scalar)).map
    (consEquiv (Palette security))).weight word = _
  rw [FiniteDist.map_equiv_weight]
  change (compensatorAt security compensatorRoot).weight (word 0) *
    (positiveTripleLaw security attachmentRoot scalar).weight (Fin.tail word) = _
  rw [positiveTriple_weight]
  rfl





end

end CurrentAFT.PositiveFirstCoefficient

end

section
















/-!
# The actual current conditional independent physical block law

Each leg is a genuine three-output law with its shared protected scalar
averaged inside that block. Every remaining body position is a one-output
center or queue law. The full finite product includes all output positions.
-/

namespace CurrentAFT.ActualBlockFock

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy PositiveFirstCoefficient
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize
  DiffuseProfiles.scalarLaw ProposalPrimary.centerLaw ProposalPrimary.safeLaw

abbrev Palette (security : ℕ) := LocalReferenceEnergy.Palette security



def centerCount (security : ℕ) : ℕ :=
  Parameters.bodySize security - Parameters.legCount security - Parameters.modulus security

abbrev BlockIndex (security : ℕ) :=
  Fin (Parameters.legCount security) ⊕ (Fin (centerCount security) ⊕ Fin (Parameters.modulus security))

def Slots (security : ℕ) : BlockIndex security → Type
  | .inl _ => Fin 3
  | .inr _ => Fin 1

instance slotsFintype (security : ℕ) (index : BlockIndex security) : Fintype (Slots security index) := by
  cases index with
  | inl _ => exact inferInstanceAs (Fintype (Fin 3))
  | inr _ => exact inferInstanceAs (Fintype (Fin 1))

def singletonLaw {Color : Type*} [Fintype Color] (law : FiniteDist Color) : FiniteDist (Fin 1 → Color) :=
  law.map (fun color _ => color)

def primaryLawAt (security : ℕ) (root : ℤ) : FiniteDist (Fin 3 → Palette security) :=
  (scalarLaw security).mix (positiveTripleLaw security root)

def blockLawAt (security : ℕ)
    (attachmentRoot : Fin (Parameters.legCount security) → ℤ)
    (centerRoot : Fin (centerCount security) → ℤ)
    (queueRoot : Fin (Parameters.modulus security) → ℤ) (queue : ℤ) :
    (index : BlockIndex security) → FiniteDist (Slots security index → Palette security)
  | .inl leg => primaryLawAt security (attachmentRoot leg)
  | .inr (.inl center) => singletonLaw ((centerLaw security).map (shiftEquiv security (centerRoot center)))
  | .inr (.inr point) => singletonLaw ((safeLaw security).map (shiftEquiv security (queueRoot point + queue)))



theorem physical_card (security : ℕ) :
    Fintype.card (Sigma (Slots security)) = Parameters.dimension security := by
  have hroom := population_room security
  simp only [Fintype.card_sigma, Fintype.sum_sum_type]
  have hprimary : (∑ index : Fin (Parameters.legCount security),
      Fintype.card (Slots security (.inl index))) = 3 * Parameters.legCount security := by
    simp [Slots, mul_comm]
  have hcenter : (∑ index : Fin (centerCount security),
      Fintype.card (Slots security (.inr (.inl index)))) = centerCount security := by
    simp [Slots]
  have hqueue : (∑ index : Fin (Parameters.modulus security),
      Fintype.card (Slots security (.inr (.inr index)))) = Parameters.modulus security := by
    simp [Slots]
  rw [hprimary, hcenter, hqueue, Parameters.dimension]
  unfold centerCount
  omega











def firstConstant : ℝ := 240 + 6291552 * Real.exp Real.pi
def higherConstant : ℝ := 32 * (524288 + 17180131328 * Real.exp Real.pi) + 1








/-- The whole finite coefficient norm of an actual independent product.
All degrees from zero through the physical population remain in the sum. -/
def productFockEnergy {Index Color : Type*} [Fintype Index] [Fintype Color]
    (slots : Index → Type*) [∀ index, Fintype (slots index)]
    (reference : FiniteDist Color) (law : (index : Index) → FiniteDist (slots index → Color))
    (radius : ℝ) : ℝ :=
  HistogramTail.fockEnergy (Fintype.card (Sigma slots)) radius
    (fun degree => BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Sigma slots => reference)
      (BlockProducts.blockMass slots law) degree))







end

end CurrentAFT.ActualBlockFock

end

section








/-!
# Actual disjoint-slot products of current canonical control kernels

Two kernels are first tensored on disjoint sums of their primary slots and
of their body slots. The combined slots are then separately averaged over
all permutations, including repeated permutations, exactly as in the current
manuscript. This is a finite operation on actual density kernels, not an
assumed abstract algebra. Truncation above the specified total order is zero.

This file is a homogeneous-product foundation. A complete multiplication on
all truncated coefficient families and its associativity remain separate
proof obligations unless explicitly stated below.
-/

namespace CurrentAFT.ControlProduct

open AFT ControlCoordinates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) :=
  Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

/-- Slot labels have independent types for the two public-control pools. -/
abbrev Kernel (PrimarySlots BodySlots : Type*) :=
  (PrimarySlots → Primary) → (BodySlots → Body) → ℝ

section SlotSpaces

variable {PS BS PT BT : Type*} [Fintype PS] [Fintype BS] [Fintype PT] [Fintype BT]

def PrimaryCentered (primary : FiniteDist Primary)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) : Prop :=
  ∀ index colors centers, ∑ color, primary.weight color *
    kernel (Function.update colors index color) centers = 0

def BodyCentered (body : FiniteDist Body)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) : Prop :=
  ∀ index colors centers, ∑ center, body.weight center *
    kernel colors (Function.update centers index center) = 0

/-- Only centering is imposed before symmetrization. The raw tensor need
not be separately symmetric in the combined slots. -/
def centeredKernelSpace (primary : FiniteDist Primary) (body : FiniteDist Body) :
    Submodule ℝ (Kernel (Primary := Primary) (Body := Body) PS BS) where
  carrier := {kernel | PrimaryCentered primary kernel ∧ BodyCentered body kernel}
  zero_mem' := by constructor <;> intro index colors centers <;> simp
  add_mem' := by
    intro first second hfirst hsecond
    constructor
    · intro index colors centers
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib,
        hfirst.1 index colors centers, hsecond.1 index colors centers, add_zero]
    · intro index colors centers
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib,
        hfirst.2 index colors centers, hsecond.2 index colors centers, add_zero]
  smul_mem' := by
    intro scalar kernel hkernel
    constructor
    · intro index colors centers
      change (∑ color, primary.weight color *
        (scalar * kernel (Function.update colors index color) centers)) = 0
      calc
        _ = scalar * ∑ color, primary.weight color *
            kernel (Function.update colors index color) centers := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro color _
          ring
        _ = 0 := by rw [hkernel.1 index colors centers, mul_zero]
    · intro index colors centers
      change (∑ center, body.weight center *
        (scalar * kernel colors (Function.update centers index center))) = 0
      calc
        _ = scalar * ∑ center, body.weight center *
            kernel colors (Function.update centers index center) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro center _
          ring
        _ = 0 := by rw [hkernel.2 index colors centers, mul_zero]

/-- Pull a kernel to equivalent slot labels, without changing its colors. -/
def reindexKernel (primaryEquiv : PS ≃ PT) (bodyEquiv : BS ≃ BT)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    Kernel (Primary := Primary) (Body := Body) PT BT :=
  fun colors centers => kernel (colors ∘ primaryEquiv) (centers ∘ bodyEquiv)

 theorem update_precompose_equiv {Index NewIndex Color : Type*}
    (equiv : Index ≃ NewIndex) (word : NewIndex → Color) (index : NewIndex) (color : Color) :
    Function.update word index color ∘ equiv =
      Function.update (word ∘ equiv) (equiv.symm index) color := by
  simpa only [Equiv.apply_symm_apply] using
    Function.update_comp_eq_of_injective word equiv.injective (equiv.symm index) color

omit [Fintype PS] [Fintype BS] [Fintype PT] [Fintype BT] in
theorem reindexKernel_centered (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryEquiv : PS ≃ PT) (bodyEquiv : BS ≃ BT)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS)
    (hkernel : kernel ∈ centeredKernelSpace primary body) :
    reindexKernel primaryEquiv bodyEquiv kernel ∈ centeredKernelSpace primary body := by
  constructor
  · intro index colors centers
    simp only [reindexKernel, update_precompose_equiv]
    exact hkernel.1 (primaryEquiv.symm index) _ _
  · intro index colors centers
    simp only [reindexKernel, update_precompose_equiv]
    exact hkernel.2 (bodyEquiv.symm index) _ _

/-- The literal tensor uses disjoint slot sets. This has no overlapping
physical indices and therefore differs from multiplying two U-statistics. -/
def disjointTensor (first : Kernel (Primary := Primary) (Body := Body) PS BS)
    (second : Kernel (Primary := Primary) (Body := Body) PT BT) :
    Kernel (Primary := Primary) (Body := Body) (PS ⊕ PT) (BS ⊕ BT) :=
  fun colors centers => first (colors ∘ Sum.inl) (centers ∘ Sum.inl) *
    second (colors ∘ Sum.inr) (centers ∘ Sum.inr)

omit [Fintype PS] [Fintype BS] [Fintype PT] [Fintype BT] in
theorem disjointTensor_centered (primary : FiniteDist Primary) (body : FiniteDist Body)
    (first : Kernel (Primary := Primary) (Body := Body) PS BS)
    (second : Kernel (Primary := Primary) (Body := Body) PT BT)
    (hfirst : first ∈ centeredKernelSpace primary body)
    (hsecond : second ∈ centeredKernelSpace primary body) :
    disjointTensor first second ∈ centeredKernelSpace primary body := by
  constructor
  · intro index colors centers
    cases index with
    | inl index =>
      have hleft color : Function.update colors (Sum.inl index) color ∘ Sum.inl =
          Function.update (colors ∘ Sum.inl) index color :=
        Function.update_comp_eq_of_injective colors Sum.inl_injective index color
      have hright color : Function.update colors (Sum.inl index) color ∘ Sum.inr = colors ∘ Sum.inr :=
        Function.update_comp_eq_of_forall_ne colors color (fun _ => Sum.inr_ne_inl)
      simp only [disjointTensor, hleft, hright, ← mul_assoc, ← Finset.sum_mul,
        hfirst.1 index, zero_mul]
    | inr index =>
      have hleft color : Function.update colors (Sum.inr index) color ∘ Sum.inl = colors ∘ Sum.inl :=
        Function.update_comp_eq_of_forall_ne colors color (fun _ => Sum.inl_ne_inr)
      have hright color : Function.update colors (Sum.inr index) color ∘ Sum.inr =
          Function.update (colors ∘ Sum.inr) index color :=
        Function.update_comp_eq_of_injective colors Sum.inr_injective index color
      simp only [disjointTensor, hleft, hright]
      calc
        _ = first (colors ∘ Sum.inl) (centers ∘ Sum.inl) *
            ∑ color, primary.weight color * second (Function.update (colors ∘ Sum.inr) index color)
              (centers ∘ Sum.inr) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro color _
          ring
        _ = 0 := by rw [hsecond.1 index, mul_zero]
  · intro index colors centers
    cases index with
    | inl index =>
      have hleft center : Function.update centers (Sum.inl index) center ∘ Sum.inl =
          Function.update (centers ∘ Sum.inl) index center :=
        Function.update_comp_eq_of_injective centers Sum.inl_injective index center
      have hright center : Function.update centers (Sum.inl index) center ∘ Sum.inr = centers ∘ Sum.inr :=
        Function.update_comp_eq_of_forall_ne centers center (fun _ => Sum.inr_ne_inl)
      simp only [disjointTensor, hleft, hright, ← mul_assoc, ← Finset.sum_mul,
        hfirst.2 index, zero_mul]
    | inr index =>
      have hleft center : Function.update centers (Sum.inr index) center ∘ Sum.inl = centers ∘ Sum.inl :=
        Function.update_comp_eq_of_forall_ne centers center (fun _ => Sum.inl_ne_inr)
      have hright center : Function.update centers (Sum.inr index) center ∘ Sum.inr =
          Function.update (centers ∘ Sum.inr) index center :=
        Function.update_comp_eq_of_injective centers Sum.inr_injective index center
      simp only [disjointTensor, hleft, hright]
      calc
        _ = first (colors ∘ Sum.inl) (centers ∘ Sum.inl) *
            ∑ center, body.weight center * second (colors ∘ Sum.inr)
              (Function.update (centers ∘ Sum.inr) index center) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro center _
          ring
        _ = 0 := by rw [hsecond.2 index, mul_zero]

/-- Average both slot permutations, including all repeated permutations. -/
def symmetrize (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    Kernel (Primary := Primary) (Body := Body) PS BS :=
  ∑ primaryOrder : Equiv.Perm PS, (FiniteDist.uniform (Equiv.Perm PS)).weight primaryOrder •
    ∑ bodyOrder : Equiv.Perm BS, (FiniteDist.uniform (Equiv.Perm BS)).weight bodyOrder •
      reindexKernel primaryOrder bodyOrder kernel

omit [Fintype Primary] [Fintype Body] in
theorem symmetrize_apply (kernel : Kernel (Primary := Primary) (Body := Body) PS BS)
    (colors : PS → Primary) (centers : BS → Body) :
    symmetrize kernel colors centers =
      (Fintype.card (Equiv.Perm PS) : ℝ)⁻¹ * (Fintype.card (Equiv.Perm BS) : ℝ)⁻¹ *
        ∑ primaryOrder : Equiv.Perm PS, ∑ bodyOrder : Equiv.Perm BS,
          kernel (colors ∘ primaryOrder) (centers ∘ bodyOrder) := by
  simp only [symmetrize, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    FiniteDist.uniform_weight, reindexKernel, ← Finset.mul_sum, mul_assoc]

theorem symmetrize_centered (primary : FiniteDist Primary) (body : FiniteDist Body)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS)
    (hkernel : kernel ∈ centeredKernelSpace primary body) :
    symmetrize kernel ∈ centeredKernelSpace primary body := by
  unfold symmetrize
  apply Submodule.sum_mem
  intro primaryOrder _
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro bodyOrder _
  apply Submodule.smul_mem
  exact reindexKernel_centered primary body primaryOrder bodyOrder kernel hkernel

omit [Fintype Primary] [Fintype Body] in
theorem symmetrize_primary_permutation
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS)
    (colors : PS → Primary) (centers : BS → Body) (permutation : Equiv.Perm PS) :
    symmetrize kernel (colors ∘ permutation) centers = symmetrize kernel colors centers := by
  rw [symmetrize_apply, symmetrize_apply]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft permutation)
    (fun primaryOrder : Equiv.Perm PS => ∑ bodyOrder : Equiv.Perm BS,
      kernel (colors ∘ primaryOrder) (centers ∘ bodyOrder))

omit [Fintype Primary] [Fintype Body] in
theorem symmetrize_body_permutation
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS)
    (colors : PS → Primary) (centers : BS → Body) (permutation : Equiv.Perm BS) :
    symmetrize kernel colors (centers ∘ permutation) = symmetrize kernel colors centers := by
  rw [symmetrize_apply, symmetrize_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro primaryOrder _
  exact Equiv.sum_comp (Equiv.mulLeft permutation)
    (fun bodyOrder : Equiv.Perm BS => kernel (colors ∘ primaryOrder) (centers ∘ bodyOrder))

omit [Fintype Primary] [Fintype Body] in
theorem symmetrize_of_symmetric
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS)
    (hsymmetric : ∀ (primaryOrder : Equiv.Perm PS) (bodyOrder : Equiv.Perm BS) colors centers,
      kernel (colors ∘ primaryOrder) (centers ∘ bodyOrder) = kernel colors centers) :
    symmetrize kernel = kernel := by
  funext colors centers
  rw [symmetrize_apply]
  simp only [hsymmetric, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hprimary : (Fintype.card (Equiv.Perm PS) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hbody : (Fintype.card (Equiv.Perm BS) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

omit [Fintype Primary] [Fintype Body] in
/-- Relabeling the complete slot sets commutes with the actual permutation
average, by a bijection between their full permutation groups. -/
theorem reindexKernel_symmetrize (primaryEquiv : PS ≃ PT) (bodyEquiv : BS ≃ BT)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    reindexKernel primaryEquiv bodyEquiv (symmetrize kernel) =
      symmetrize (reindexKernel primaryEquiv bodyEquiv kernel) := by
  funext colors centers
  change symmetrize kernel (colors ∘ primaryEquiv) (centers ∘ bodyEquiv) = _
  rw [symmetrize_apply, symmetrize_apply]
  have hp : Fintype.card (Equiv.Perm PS) = Fintype.card (Equiv.Perm PT) :=
    Fintype.card_congr primaryEquiv.permCongr
  have hb : Fintype.card (Equiv.Perm BS) = Fintype.card (Equiv.Perm BT) :=
    Fintype.card_congr bodyEquiv.permCongr
  rw [hp, hb]
  congr 1
  symm
  rw [← primaryEquiv.permCongr.sum_comp]
  apply Finset.sum_congr rfl
  intro primaryOrder _
  rw [← bodyEquiv.permCongr.sum_comp]
  apply Finset.sum_congr rfl
  intro bodyOrder _
  unfold reindexKernel
  apply congrArg₂ kernel
  · funext index
    simp only [Function.comp_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  · funext index
    simp only [Function.comp_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply]





/-- The averaging operation is a proved linear map on the actual arrays. -/
def symmetrizeLinear :
    Kernel (Primary := Primary) (Body := Body) PS BS →ₗ[ℝ]
      Kernel (Primary := Primary) (Body := Body) PS BS where
  toFun := symmetrize
  map_add' first second := by
    funext colors centers
    simp only [symmetrize_apply, Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' scalar kernel := by
    funext colors centers
    simp only [symmetrize_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      ← Finset.mul_sum]
    ring

def tensorLeftLinear (second : Kernel (Primary := Primary) (Body := Body) PT BT) :
    Kernel (Primary := Primary) (Body := Body) PS BS →ₗ[ℝ]
      Kernel (Primary := Primary) (Body := Body) (PS ⊕ PT) (BS ⊕ BT) where
  toFun first := disjointTensor first second
  map_add' first other := by
    funext colors centers
    simp only [disjointTensor, Pi.add_apply, add_mul]
  map_smul' scalar first := by
    funext colors centers
    simp only [disjointTensor, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def tensorRightLinear (first : Kernel (Primary := Primary) (Body := Body) PS BS) :
    Kernel (Primary := Primary) (Body := Body) PT BT →ₗ[ℝ]
      Kernel (Primary := Primary) (Body := Body) (PS ⊕ PT) (BS ⊕ BT) where
  toFun second := disjointTensor first second
  map_add' second other := by
    funext colors centers
    simp only [disjointTensor, Pi.add_apply, mul_add]
  map_smul' scalar second := by
    funext colors centers
    simp only [disjointTensor, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

omit [Fintype Primary] [Fintype Body] in
theorem symmetrize_reindex_permutations
    (primaryOrder : Equiv.Perm PS) (bodyOrder : Equiv.Perm BS)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    symmetrize (reindexKernel primaryOrder bodyOrder kernel) = symmetrize kernel := by
  rw [← reindexKernel_symmetrize]
  funext colors centers
  change symmetrize kernel (colors ∘ primaryOrder) (centers ∘ bodyOrder) = _
  rw [symmetrize_primary_permutation, symmetrize_body_permutation]

omit [Fintype Primary] [Fintype Body] [Fintype PS] [Fintype BS] [Fintype PT] [Fintype BT] in
theorem disjointTensor_reindex_first
    (primaryOrder : Equiv.Perm PS) (bodyOrder : Equiv.Perm BS)
    (first : Kernel (Primary := Primary) (Body := Body) PS BS)
    (second : Kernel (Primary := Primary) (Body := Body) PT BT) :
    disjointTensor (reindexKernel primaryOrder bodyOrder first) second =
      reindexKernel (Equiv.sumCongr primaryOrder (Equiv.refl PT))
        (Equiv.sumCongr bodyOrder (Equiv.refl BT)) (disjointTensor first second) := by
  funext colors centers
  simp [disjointTensor, reindexKernel, Function.comp_def]

omit [Fintype Primary] [Fintype Body] [Fintype PS] [Fintype BS] [Fintype PT] [Fintype BT] in
theorem disjointTensor_reindex_second
    (primaryOrder : Equiv.Perm PT) (bodyOrder : Equiv.Perm BT)
    (first : Kernel (Primary := Primary) (Body := Body) PS BS)
    (second : Kernel (Primary := Primary) (Body := Body) PT BT) :
    disjointTensor first (reindexKernel primaryOrder bodyOrder second) =
      reindexKernel (Equiv.sumCongr (Equiv.refl PS) primaryOrder)
        (Equiv.sumCongr (Equiv.refl BS) bodyOrder) (disjointTensor first second) := by
  funext colors centers
  simp [disjointTensor, reindexKernel, Function.comp_def]

omit [Fintype Primary] [Fintype Body] in
/-- A full permutation average absorbs the internal first-block average.
The proof expands both finite averages and reindexes each summand. -/
theorem symmetrizedTensor_first_symmetrize
    (first : Kernel (Primary := Primary) (Body := Body) PS BS)
    (second : Kernel (Primary := Primary) (Body := Body) PT BT) :
    symmetrize (disjointTensor (symmetrize first) second) = symmetrize (disjointTensor first second) := by
  let operation : Kernel (Primary := Primary) (Body := Body) PS BS →ₗ[ℝ]
      Kernel (Primary := Primary) (Body := Body) (PS ⊕ PT) (BS ⊕ BT) :=
    symmetrizeLinear.comp (tensorLeftLinear second)
  change operation (symmetrize first) = operation first
  have hterm (primaryOrder : Equiv.Perm PS) (bodyOrder : Equiv.Perm BS) :
      operation (reindexKernel primaryOrder bodyOrder first) = operation first := by
    change symmetrize (disjointTensor (reindexKernel primaryOrder bodyOrder first) second) = _
    rw [disjointTensor_reindex_first, symmetrize_reindex_permutations]
    rfl
  unfold symmetrize
  rw [map_sum]
  simp_rw [map_smul, map_sum, map_smul, hterm]
  simp only [← Finset.sum_smul, FiniteDist.sum_one, one_smul]

omit [Fintype Primary] [Fintype Body] in
theorem symmetrizedTensor_second_symmetrize
    (first : Kernel (Primary := Primary) (Body := Body) PS BS)
    (second : Kernel (Primary := Primary) (Body := Body) PT BT) :
    symmetrize (disjointTensor first (symmetrize second)) = symmetrize (disjointTensor first second) := by
  let operation : Kernel (Primary := Primary) (Body := Body) PT BT →ₗ[ℝ]
      Kernel (Primary := Primary) (Body := Body) (PS ⊕ PT) (BS ⊕ BT) :=
    symmetrizeLinear.comp (tensorRightLinear first)
  change operation (symmetrize second) = operation second
  have hterm (primaryOrder : Equiv.Perm PT) (bodyOrder : Equiv.Perm BT) :
      operation (reindexKernel primaryOrder bodyOrder second) = operation second := by
    change symmetrize (disjointTensor first (reindexKernel primaryOrder bodyOrder second)) = _
    rw [disjointTensor_reindex_second, symmetrize_reindex_permutations]
    rfl
  unfold symmetrize
  rw [map_sum]
  simp_rw [map_smul, map_sum, map_smul, hterm]
  simp only [← Finset.sum_smul, FiniteDist.sum_one, one_smul]

variable {PU BU : Type*} [Fintype PU] [Fintype BU]

omit [Fintype Primary] [Fintype Body] [Fintype PS] [Fintype BS] [Fintype PT] [Fintype BT]
  [Fintype PU] [Fintype BU] in
theorem disjointTensor_assoc
    (first : Kernel (Primary := Primary) (Body := Body) PS BS)
    (second : Kernel (Primary := Primary) (Body := Body) PT BT)
    (third : Kernel (Primary := Primary) (Body := Body) PU BU) :
    reindexKernel (Equiv.sumAssoc PS PT PU) (Equiv.sumAssoc BS BT BU)
        (disjointTensor (disjointTensor first second) third) =
      disjointTensor first (disjointTensor second third) := by
  funext colors centers
  simp only [reindexKernel, disjointTensor, Function.comp_def,
    Equiv.sumAssoc_apply_inl_inl, Equiv.sumAssoc_apply_inl_inr, Equiv.sumAssoc_apply_inr]
  ring



end SlotSpaces

/-- The actual raw tensor in the manuscript's finite ordered slot labels. -/
def finDisjointTensor {r s r' s' : ℕ}
    (first : DensityKernel (Primary := Primary) (Body := Body) r s)
    (second : DensityKernel (Primary := Primary) (Body := Body) r' s') :
    DensityKernel (Primary := Primary) (Body := Body) (r + r') (s + s') :=
  reindexKernel finSumFinEquiv finSumFinEquiv (disjointTensor first second)

/-- The homogeneous star product has been constructed on actual canonical
density kernels. Centering and separate symmetry are proved properties. -/
def homogeneousProduct (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (first : canonicalKernels primary body r s)
    (second : canonicalKernels primary body r' s') :
    canonicalKernels primary body (r + r') (s + s') := by
  let result := symmetrize (finDisjointTensor first.val second.val)
  have hfirst : first.val ∈ centeredKernelSpace primary body := ⟨first.property.1, first.property.2.1⟩
  have hsecond : second.val ∈ centeredKernelSpace primary body := ⟨second.property.1, second.property.2.1⟩
  have hcenter : result ∈ centeredKernelSpace primary body :=
    symmetrize_centered primary body _
      (reindexKernel_centered primary body finSumFinEquiv finSumFinEquiv _
        (disjointTensor_centered primary body first.val second.val hfirst hsecond))
  refine ⟨result, hcenter.1, hcenter.2, ?_⟩
  intro primaryOrder bodyOrder colors centers
  change symmetrize _ (colors ∘ primaryOrder) (centers ∘ bodyOrder) = symmetrize _ colors centers
  rw [symmetrize_primary_permutation, symmetrize_body_permutation]









/-- Block swapping between the manuscript's ordered total-slot labels. -/
def finBlockSwap (left right : ℕ) : Fin (left + right) ≃ Fin (right + left) :=
  finSumFinEquiv.symm.trans ((Equiv.sumComm (Fin left) (Fin right)).trans finSumFinEquiv)

omit [Fintype Primary] [Fintype Body] in
theorem finDisjointTensor_swap {r s r' s' : ℕ}
    (first : DensityKernel (Primary := Primary) (Body := Body) r s)
    (second : DensityKernel (Primary := Primary) (Body := Body) r' s') :
    reindexKernel (finBlockSwap r r') (finBlockSwap s s') (finDisjointTensor first second) =
      finDisjointTensor second first := by
  funext colors centers
  simp only [finDisjointTensor, reindexKernel, disjointTensor, Function.comp_def,
    finBlockSwap, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.sumComm_apply,
    Sum.swap, Sum.elim_inl, Sum.elim_inr]
  ring

/-- The actual homogeneous product is commutative after its explicit block
swap; this is proved from the permutation averages and raw tensors. -/
theorem homogeneousProduct_comm (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (first : canonicalKernels primary body r s)
    (second : canonicalKernels primary body r' s') :
    reindexKernel (finBlockSwap r r') (finBlockSwap s s')
        (homogeneousProduct primary body first second).val =
      (homogeneousProduct primary body second first).val := by
  change reindexKernel _ _ (symmetrize (finDisjointTensor first.val second.val)) =
    symmetrize (finDisjointTensor second.val first.val)
  rw [reindexKernel_symmetrize, finDisjointTensor_swap]

/-- The degree-zero scalar unit is the actual constant density kernel. -/
def scalarUnit (primary : FiniteDist Primary) (body : FiniteDist Body) :
    canonicalKernels primary body 0 0 := by
  refine ⟨fun _ _ => 1, ?_, ?_, ?_⟩
  · intro index
    exact Fin.elim0 index
  · intro index
    exact Fin.elim0 index
  · unfold SeparatelySymmetric
    intros
    rfl

def finLeftUnit (count : ℕ) : Fin (0 + count) ≃ Fin count :=
  finSumFinEquiv.symm.trans (Equiv.emptySum (Fin 0) (Fin count))



theorem finDisjointTensor_unit_left (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s : ℕ} (kernel : canonicalKernels primary body r s) :
    reindexKernel (finLeftUnit r) (finLeftUnit s)
      (finDisjointTensor (scalarUnit primary body).val kernel.val) = kernel.val := by
  funext colors centers
  simp only [finDisjointTensor, reindexKernel, disjointTensor, scalarUnit,
    finLeftUnit, Function.comp_def, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.emptySum_apply_inr, one_mul]



/-- Left multiplication by the real degree-zero unit fixes every canonical
kernel, after the explicit empty-block identification. -/
theorem homogeneousProduct_unit_left (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s : ℕ} (kernel : canonicalKernels primary body r s) :
    reindexKernel (finLeftUnit r) (finLeftUnit s)
      (homogeneousProduct primary body (scalarUnit primary body) kernel).val = kernel.val := by
  change reindexKernel _ _ (symmetrize (finDisjointTensor _ _)) = _
  rw [reindexKernel_symmetrize, finDisjointTensor_unit_left]
  exact symmetrize_of_symmetric kernel.val kernel.property.2.2







end

end CurrentAFT.ControlProduct

end

section








/-!
# Slot coherence of the actual symmetric coefficient product

Changing finite slot labels commutes with tensoring and with the complete
permutation average. These identities convert the proved sum-slot
associativity into the finite ordered labels used by coefficient arrays.
-/

namespace CurrentAFT.ControlCoherence

open AFT ControlCoordinates ControlProduct
open scoped BigOperators Classical

noncomputable section

variable {Primary Body : Type*}
variable {PS BS PT BT PU BU PV BV : Type*}

theorem reindexKernel_refl
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    reindexKernel (Equiv.refl PS) (Equiv.refl BS) kernel = kernel := rfl

theorem reindexKernel_comp (firstPrimary : PS ≃ PT) (secondPrimary : PT ≃ PU)
    (firstBody : BS ≃ BT) (secondBody : BT ≃ BU)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    reindexKernel secondPrimary secondBody (reindexKernel firstPrimary firstBody kernel) =
      reindexKernel (firstPrimary.trans secondPrimary) (firstBody.trans secondBody) kernel := rfl

theorem tensor_reindex (firstPrimary : PS ≃ PU) (secondPrimary : PT ≃ PV)
    (firstBody : BS ≃ BU) (secondBody : BT ≃ BV)
    (first : Kernel (Primary := Primary) (Body := Body) PS BS)
    (second : Kernel (Primary := Primary) (Body := Body) PT BT) :
    reindexKernel (Equiv.sumCongr firstPrimary secondPrimary)
      (Equiv.sumCongr firstBody secondBody) (disjointTensor first second) =
      disjointTensor (reindexKernel firstPrimary firstBody first)
        (reindexKernel secondPrimary secondBody second) := by
  funext colors centers
  rfl

/-- A separately symmetric kernel is independent of which bijections
identify its complete primary and body slot sets with target labels. -/
theorem symmetric_reindex_unique (firstPrimary secondPrimary : PS ≃ PT)
    (firstBody secondBody : BS ≃ BT)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS)
    (hsymmetric : ∀ (primaryOrder : Equiv.Perm PS) (bodyOrder : Equiv.Perm BS) colors centers,
      kernel (colors ∘ primaryOrder) (centers ∘ bodyOrder) = kernel colors centers) :
    reindexKernel firstPrimary firstBody kernel = reindexKernel secondPrimary secondBody kernel := by
  funext colors centers
  have hp : colors ∘ firstPrimary = (colors ∘ secondPrimary) ∘
      (firstPrimary.trans secondPrimary.symm) := by
    funext index
    simp only [Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
  have hb : centers ∘ firstBody = (centers ∘ secondBody) ∘
      (firstBody.trans secondBody.symm) := by
    funext index
    simp only [Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
  unfold reindexKernel
  rw [hp, hb]
  exact hsymmetric _ _ _ _

section FiniteLabels

def leftFlatten (first second third : ℕ) :
    ((Fin first ⊕ Fin second) ⊕ Fin third) ≃ Fin ((first + second) + third) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin third))).trans finSumFinEquiv

def rightFlatten (first second third : ℕ) :
    (Fin first ⊕ (Fin second ⊕ Fin third)) ≃ Fin (first + (second + third)) :=
  (Equiv.sumCongr (Equiv.refl (Fin first)) finSumFinEquiv).trans finSumFinEquiv

def finAssociator (first second third : ℕ) :
    Fin ((first + second) + third) ≃ Fin (first + (second + third)) :=
  (leftFlatten first second third).symm.trans
    ((Equiv.sumAssoc (Fin first) (Fin second) (Fin third)).trans
      (rightFlatten first second third))

variable {r s r' s' r'' s'' : ℕ}

theorem flatten_left_tensor
    (first : DensityKernel (Primary := Primary) (Body := Body) r s)
    (second : DensityKernel (Primary := Primary) (Body := Body) r' s')
    (third : DensityKernel (Primary := Primary) (Body := Body) r'' s'') :
    reindexKernel (leftFlatten r r' r'') (leftFlatten s s' s'')
      (disjointTensor (disjointTensor first second) third) =
        finDisjointTensor (finDisjointTensor first second) third := by
  rw [leftFlatten, leftFlatten, ← reindexKernel_comp,
    tensor_reindex, reindexKernel_refl]
  rfl

theorem flatten_right_tensor
    (first : DensityKernel (Primary := Primary) (Body := Body) r s)
    (second : DensityKernel (Primary := Primary) (Body := Body) r' s')
    (third : DensityKernel (Primary := Primary) (Body := Body) r'' s'') :
    reindexKernel (rightFlatten r r' r'') (rightFlatten s s' s'')
      (disjointTensor first (disjointTensor second third)) =
        finDisjointTensor first (finDisjointTensor second third) := by
  rw [rightFlatten, rightFlatten, ← reindexKernel_comp,
    tensor_reindex, reindexKernel_refl]
  rfl

theorem finDisjointTensor_assoc
    (first : DensityKernel (Primary := Primary) (Body := Body) r s)
    (second : DensityKernel (Primary := Primary) (Body := Body) r' s')
    (third : DensityKernel (Primary := Primary) (Body := Body) r'' s'') :
    reindexKernel (finAssociator r r' r'') (finAssociator s s' s'')
      (finDisjointTensor (finDisjointTensor first second) third) =
        finDisjointTensor first (finDisjointTensor second third) := by
  rw [← flatten_left_tensor]
  unfold finAssociator
  rw [reindexKernel_comp]
  have hp : (leftFlatten r r' r'').trans
      ((leftFlatten r r' r'').symm.trans
        ((Equiv.sumAssoc (Fin r) (Fin r') (Fin r'')).trans (rightFlatten r r' r''))) =
      (Equiv.sumAssoc (Fin r) (Fin r') (Fin r'')).trans (rightFlatten r r' r'') := by
    ext index
    simp
  have hb : (leftFlatten s s' s'').trans
      ((leftFlatten s s' s'').symm.trans
        ((Equiv.sumAssoc (Fin s) (Fin s') (Fin s'')).trans (rightFlatten s s' s''))) =
      (Equiv.sumAssoc (Fin s) (Fin s') (Fin s'')).trans (rightFlatten s s' s'') := by
    ext index
    simp
  rw [hp, hb, ← reindexKernel_comp, disjointTensor_assoc, flatten_right_tensor]

theorem symmetrized_fin_tensor_first
    (first : DensityKernel (Primary := Primary) (Body := Body) r s)
    (second : DensityKernel (Primary := Primary) (Body := Body) r' s') :
    symmetrize (finDisjointTensor (symmetrize first) second) =
      symmetrize (finDisjointTensor first second) := by
  unfold finDisjointTensor
  rw [← reindexKernel_symmetrize, symmetrizedTensor_first_symmetrize,
    reindexKernel_symmetrize]

theorem symmetrized_fin_tensor_second
    (first : DensityKernel (Primary := Primary) (Body := Body) r s)
    (second : DensityKernel (Primary := Primary) (Body := Body) r' s') :
    symmetrize (finDisjointTensor first (symmetrize second)) =
      symmetrize (finDisjointTensor first second) := by
  unfold finDisjointTensor
  rw [← reindexKernel_symmetrize, symmetrizedTensor_second_symmetrize,
    reindexKernel_symmetrize]

variable [Fintype Primary] [Fintype Body]

theorem homogeneousProduct_assoc_route (primary : FiniteDist Primary) (body : FiniteDist Body)
    (first : canonicalKernels primary body r s) (second : canonicalKernels primary body r' s')
    (third : canonicalKernels primary body r'' s'') :
    reindexKernel (finAssociator r r' r'') (finAssociator s s' s'')
      (homogeneousProduct primary body (homogeneousProduct primary body first second) third).val =
      (homogeneousProduct primary body first (homogeneousProduct primary body second third)).val := by
  change reindexKernel _ _
      (symmetrize (finDisjointTensor (symmetrize (finDisjointTensor first.val second.val)) third.val)) =
    symmetrize (finDisjointTensor first.val (symmetrize (finDisjointTensor second.val third.val)))
  rw [symmetrized_fin_tensor_first, symmetrized_fin_tensor_second,
    reindexKernel_symmetrize, finDisjointTensor_assoc]

/-- Associativity in the exact equality-based finite labels needed by
dependent arity arrays, without assuming a multiplication law. -/
theorem homogeneousProduct_assoc (primary : FiniteDist Primary) (body : FiniteDist Body)
    (first : canonicalKernels primary body r s) (second : canonicalKernels primary body r' s')
    (third : canonicalKernels primary body r'' s'') :
    reindexKernel (finCongr (Nat.add_assoc r r' r'')) (finCongr (Nat.add_assoc s s' s''))
      (homogeneousProduct primary body (homogeneousProduct primary body first second) third).val =
      (homogeneousProduct primary body first (homogeneousProduct primary body second third)).val := by
  apply Eq.trans _ (homogeneousProduct_assoc_route primary body first second third)
  exact symmetric_reindex_unique _ _ _ _ _
    (homogeneousProduct primary body (homogeneousProduct primary body first second) third).property.2.2

theorem homogeneousProduct_comm_cast (primary : FiniteDist Primary) (body : FiniteDist Body)
    (first : canonicalKernels primary body r s) (second : canonicalKernels primary body r' s') :
    reindexKernel (finCongr (Nat.add_comm r r')) (finCongr (Nat.add_comm s s'))
      (homogeneousProduct primary body first second).val =
      (homogeneousProduct primary body second first).val := by
  apply Eq.trans _ (homogeneousProduct_comm primary body first second)
  exact symmetric_reindex_unique _ _ _ _ _
    (homogeneousProduct primary body first second).property.2.2

end FiniteLabels

end

end CurrentAFT.ControlCoherence

end

section








/-!
# Actual Hilbert block energy and graded coefficient size

The block energy is the finite sum of squared density values weighted by
the true primary/body product reference. No pre-existing normed-algebra
structure is assumed. Disjoint tensor multiplication, slot relabeling, and
permutation averaging are verified on these finite sums before any graded
coefficient bound is formed.

The finite coefficient size uses the manuscript's sum of block L2 norms,
with degree-zero absolute value and multiplicative arity weights. This file
does not yet install a normed-algebra instance or assume an unproved product
law for complete truncated coefficient families.
-/

namespace CurrentAFT.ControlNorm

open AFT ControlCoordinates ControlProduct
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) :=
  Classical.decEq _

variable {Primary Body PS BS PT BT : Type*}
  [Fintype Primary] [Fintype Body] [Fintype PS] [Fintype BS] [Fintype PT] [Fintype BT]

/-- The genuine square L2 norm under the two product reference laws. -/
def blockEnergy (primary : FiniteDist Primary) (body : FiniteDist Body)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) : ℝ :=
  ((FiniteDist.independent (fun _ : PS => primary)).prod
    (FiniteDist.independent (fun _ : BS => body))).l2Sq (fun inputs => kernel inputs.1 inputs.2)

theorem blockEnergy_apply (primary : FiniteDist Primary) (body : FiniteDist Body)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    blockEnergy primary body kernel = ∑ colors : PS → Primary, ∑ centers : BS → Body,
      (∏ index, primary.weight (colors index)) * (∏ index, body.weight (centers index)) *
        kernel colors centers ^ 2 := by
  simp only [blockEnergy, FiniteDist.l2Sq, FiniteDist.expectation, FiniteDist.prod_weight,
    FiniteDist.independent, Fintype.sum_prod_type]

theorem blockEnergy_nonneg (primary : FiniteDist Primary) (body : FiniteDist Body)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) : 0 ≤ blockEnergy primary body kernel :=
  FiniteDist.l2Sq_nonneg _ _

def blockL2 (primary : FiniteDist Primary) (body : FiniteDist Body)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) : ℝ :=
  Real.sqrt (blockEnergy primary body kernel)

theorem blockL2_nonneg (primary : FiniteDist Primary) (body : FiniteDist Body)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) : 0 ≤ blockL2 primary body kernel :=
  Real.sqrt_nonneg _

theorem blockL2_sq (primary : FiniteDist Primary) (body : FiniteDist Body)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    blockL2 primary body kernel ^ 2 = blockEnergy primary body kernel :=
  Real.sq_sqrt (blockEnergy_nonneg primary body kernel)

 theorem finite_l2_triangle {State : Type*} [Fintype State]
    (law : FiniteDist State) (first second : State → ℝ) :
    Real.sqrt (law.l2Sq (fun state => first state + second state)) ≤
      Real.sqrt (law.l2Sq first) + Real.sqrt (law.l2Sq second) := by
  have hadd : law.l2Sq (fun state => first state + second state) =
      law.l2Sq first + 2 * law.expectation (fun state => first state * second state) + law.l2Sq second := by
    calc
      _ = ∑ state, (law.weight state * first state ^ 2 +
          2 * (law.weight state * (first state * second state)) + law.weight state * second state ^ 2) := by
        apply Finset.sum_congr rfl
        intro state _
        ring
      _ = _ := by
        simp only [FiniteDist.l2Sq, FiniteDist.expectation,
          Finset.sum_add_distrib, ← Finset.mul_sum]
  have hfirst := Real.sq_sqrt (FiniteDist.l2Sq_nonneg law first)
  have hsecond := Real.sq_sqrt (FiniteDist.l2Sq_nonneg law second)
  have hsum := Real.sq_sqrt (FiniteDist.l2Sq_nonneg law (fun state => first state + second state))
  have hcs := CanonicalMoments.expectation_mul_sq_le law first second
  have hinner : law.expectation (fun state => first state * second state) ≤
      Real.sqrt (law.l2Sq first) * Real.sqrt (law.l2Sq second) := by
    apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    calc
      _ ≤ law.l2Sq first * law.l2Sq second := hcs
      _ = _ := by rw [mul_pow, hfirst, hsecond]
  apply le_of_sq_le_sq _ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  rw [hsum, hadd, add_sq, hfirst, hsecond]
  linarith

/-- The block triangle inequality is proved on the actual weighted finite
sum by Cauchy--Schwarz, rather than obtained from a normed-algebra premise. -/
theorem blockL2_add_le (primary : FiniteDist Primary) (body : FiniteDist Body)
    (first second : Kernel (Primary := Primary) (Body := Body) PS BS) :
    blockL2 primary body (first + second) ≤ blockL2 primary body first + blockL2 primary body second := by
  exact finite_l2_triangle
    ((FiniteDist.independent (fun _ : PS => primary)).prod (FiniteDist.independent (fun _ : BS => body)))
    (fun inputs => first inputs.1 inputs.2) (fun inputs => second inputs.1 inputs.2)

theorem blockEnergy_smul (primary : FiniteDist Primary) (body : FiniteDist Body)
    (scalar : ℝ) (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    blockEnergy primary body (scalar • kernel) = scalar ^ 2 * blockEnergy primary body kernel := by
  rw [blockEnergy_apply, blockEnergy_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro colors _
  apply Finset.sum_congr rfl
  intro centers _
  ring

theorem blockL2_smul (primary : FiniteDist Primary) (body : FiniteDist Body)
    (scalar : ℝ) (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    blockL2 primary body (scalar • kernel) = |scalar| * blockL2 primary body kernel := by
  rw [blockL2, blockEnergy_smul, Real.sqrt_mul (sq_nonneg scalar), Real.sqrt_sq_eq_abs]
  rfl

/-- Positive reference atoms make this genuine L2 norm separate every density
array, including nonsymmetric arrays. -/
theorem blockEnergy_eq_zero_iff (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hprimary : ∀ color, 0 < primary.weight color) (hbody : ∀ center, 0 < body.weight center)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    blockEnergy primary body kernel = 0 ↔ kernel = 0 := by
  constructor
  · intro hzero
    rw [blockEnergy_apply] at hzero
    have hrows := (Finset.sum_eq_zero_iff_of_nonneg (fun colors _ =>
      Finset.sum_nonneg fun centers _ => mul_nonneg
        (mul_nonneg (Finset.prod_nonneg fun index _ => primary.nonneg _)
          (Finset.prod_nonneg fun index _ => body.nonneg _)) (sq_nonneg _))).mp hzero
    funext colors centers
    have hentry := (Finset.sum_eq_zero_iff_of_nonneg (fun centers _ => mul_nonneg
      (mul_nonneg (Finset.prod_nonneg fun index _ => primary.nonneg _)
        (Finset.prod_nonneg fun index _ => body.nonneg _)) (sq_nonneg _))).mp
          (hrows colors (Finset.mem_univ _)) centers (Finset.mem_univ _)
    have hweight : 0 < (∏ index : PS, primary.weight (colors index)) *
        (∏ index : BS, body.weight (centers index)) :=
      mul_pos (Finset.prod_pos fun index _ => hprimary _) (Finset.prod_pos fun index _ => hbody _)
    have hsquare : kernel colors centers ^ 2 = 0 :=
      (mul_eq_zero.mp hentry).resolve_left (ne_of_gt hweight)
    exact sq_eq_zero_iff.mp hsquare
  · intro hzero
    simp only [hzero, blockEnergy_apply, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
      mul_zero, Finset.sum_const_zero]

theorem blockL2_eq_zero_iff (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hprimary : ∀ color, 0 < primary.weight color) (hbody : ∀ center, 0 < body.weight center)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    blockL2 primary body kernel = 0 ↔ kernel = 0 := by
  constructor
  · intro hzero
    apply (blockEnergy_eq_zero_iff primary body hprimary hbody kernel).mp
    have hsquare := blockL2_sq primary body kernel
    rw [hzero, zero_pow (by decide : 2 ≠ 0)] at hsquare
    exact hsquare.symm
  · intro hzero
    rw [blockL2, (blockEnergy_eq_zero_iff primary body hprimary hbody kernel).mpr hzero, Real.sqrt_zero]

/-- The word equivalence used to reindex the full finite product reference. -/
def slotWordEquiv (equiv : PS ≃ PT) : (PS → Primary) ≃ (PT → Primary) where
  toFun colors := colors ∘ equiv.symm
  invFun colors := colors ∘ equiv
  left_inv colors := by funext index; simp
  right_inv colors := by funext index; simp

theorem blockEnergy_reindex (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryEquiv : PS ≃ PT) (bodyEquiv : BS ≃ BT)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    blockEnergy primary body (reindexKernel primaryEquiv bodyEquiv kernel) =
      blockEnergy primary body kernel := by
  rw [blockEnergy_apply, blockEnergy_apply]
  rw [← (slotWordEquiv primaryEquiv).sum_comp]
  apply Finset.sum_congr rfl
  intro colors _
  rw [← (slotWordEquiv (Primary := Body) bodyEquiv).sum_comp]
  apply Finset.sum_congr rfl
  intro centers _
  have hp : (∏ index : PT, primary.weight (colors (primaryEquiv.symm index))) =
      ∏ index : PS, primary.weight (colors index) :=
    primaryEquiv.symm.prod_comp (fun index => primary.weight (colors index))
  have hb : (∏ index : BT, body.weight (centers (bodyEquiv.symm index))) =
      ∏ index : BS, body.weight (centers index) :=
    bodyEquiv.symm.prod_comp (fun index => body.weight (centers index))
  simp only [slotWordEquiv, Equiv.coe_fn_mk, Function.comp_def, reindexKernel,
    Equiv.symm_apply_apply, hp, hb]

theorem blockL2_reindex (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryEquiv : PS ≃ PT) (bodyEquiv : BS ≃ BT)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    blockL2 primary body (reindexKernel primaryEquiv bodyEquiv kernel) =
      blockL2 primary body kernel := by
  simp only [blockL2, blockEnergy_reindex]

/-- Exact tensor factorization for arbitrary joint kernels in each factor.
The two types of product-reference weights are both retained. -/
theorem blockEnergy_disjointTensor (primary : FiniteDist Primary) (body : FiniteDist Body)
    (first : Kernel (Primary := Primary) (Body := Body) PS BS)
    (second : Kernel (Primary := Primary) (Body := Body) PT BT) :
    blockEnergy primary body (disjointTensor first second) =
      blockEnergy primary body first * blockEnergy primary body second := by
  rw [blockEnergy_apply, blockEnergy_apply, blockEnergy_apply]
  rw [← (Equiv.sumArrowEquivProdArrow PS PT Primary).symm.sum_comp, Fintype.sum_prod_type]
  simp_rw [← (Equiv.sumArrowEquivProdArrow BS BT Body).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_symm_mk,
    Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    disjointTensor, Function.comp_def]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro firstColors _
  apply Finset.sum_congr rfl
  intro secondColors _
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro firstCenters _
  apply Finset.sum_congr rfl
  intro secondCenters _
  ring

theorem blockL2_disjointTensor (primary : FiniteDist Primary) (body : FiniteDist Body)
    (first : Kernel (Primary := Primary) (Body := Body) PS BS)
    (second : Kernel (Primary := Primary) (Body := Body) PT BT) :
    blockL2 primary body (disjointTensor first second) =
      blockL2 primary body first * blockL2 primary body second := by
  rw [blockL2, blockEnergy_disjointTensor, Real.sqrt_mul (blockEnergy_nonneg primary body first)]
  rfl

 theorem finite_expectation_square_le {State : Type*} [Fintype State]
    (law : FiniteDist State) (value : State → ℝ) :
    law.expectation value ^ 2 ≤ law.expectation (fun state => value state ^ 2) := by
  let mean := law.expectation value
  have hnonneg : 0 ≤ ∑ state, law.weight state * (value state - mean) ^ 2 :=
    Finset.sum_nonneg fun state _ => mul_nonneg (law.nonneg state) (sq_nonneg _)
  have hterm state : law.weight state * (value state - mean) ^ 2 =
      law.weight state * value state ^ 2 - 2 * mean * (law.weight state * value state) +
        mean ^ 2 * law.weight state := by ring
  simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, law.sum_one, mul_one] at hnonneg
  change 0 ≤ law.expectation (fun state => value state ^ 2) - 2 * mean * mean + mean ^ 2 at hnonneg
  dsimp only [mean] at hnonneg
  nlinarith

 theorem sum_rotate {First Second Third : Type*}
    [Fintype First] [Fintype Second] [Fintype Third] (term : First → Second → Third → ℝ) :
    (∑ first, ∑ second, ∑ third, term first second third) =
      ∑ third, ∑ first, ∑ second, term first second third := by
  calc
    _ = ∑ first, ∑ third, ∑ second, term first second third := by
      apply Finset.sum_congr rfl
      intro first _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Averaging actual density arrays contracts their square L2 energy. This
is finite Jensen, proved above from a nonnegative variance sum. -/
theorem blockEnergy_average_le {Choice : Type*} [Fintype Choice]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (law : FiniteDist Choice)
    (family : Choice → Kernel (Primary := Primary) (Body := Body) PS BS) :
    blockEnergy primary body (fun colors centers => law.expectation (fun choice => family choice colors centers)) ≤
      law.expectation (fun choice => blockEnergy primary body (family choice)) := by
  rw [blockEnergy_apply]
  calc
    _ ≤ ∑ colors : PS → Primary, ∑ centers : BS → Body,
        (∏ index, primary.weight (colors index)) * (∏ index, body.weight (centers index)) *
          law.expectation (fun choice => family choice colors centers ^ 2) := by
      apply Finset.sum_le_sum
      intro colors _
      apply Finset.sum_le_sum
      intro centers _
      exact mul_le_mul_of_nonneg_left (finite_expectation_square_le law _)
        (mul_nonneg (Finset.prod_nonneg fun index _ => primary.nonneg _)
          (Finset.prod_nonneg fun index _ => body.nonneg _))
    _ = _ := by
      simp only [FiniteDist.expectation, Finset.mul_sum, blockEnergy_apply]
      rw [sum_rotate]
      apply Finset.sum_congr rfl
      intro choice _
      apply Finset.sum_congr rfl
      intro colors _
      apply Finset.sum_congr rfl
      intro centers _
      ring

omit [Fintype Primary] [Fintype Body] in
theorem symmetrize_eq_expectation (kernel : Kernel (Primary := Primary) (Body := Body) PS BS)
    (colors : PS → Primary) (centers : BS → Body) :
    symmetrize kernel colors centers =
      ((FiniteDist.uniform (Equiv.Perm PS)).prod (FiniteDist.uniform (Equiv.Perm BS))).expectation
        (fun orders => kernel (colors ∘ orders.1) (centers ∘ orders.2)) := by
  rw [symmetrize_apply]
  simp only [FiniteDist.expectation, FiniteDist.prod_weight, FiniteDist.uniform_weight,
    Fintype.sum_prod_type, ← Finset.mul_sum, mul_assoc]

theorem blockEnergy_symmetrize_le (primary : FiniteDist Primary) (body : FiniteDist Body)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    blockEnergy primary body (symmetrize kernel) ≤ blockEnergy primary body kernel := by
  have hkernel : symmetrize kernel = fun colors centers =>
      ((FiniteDist.uniform (Equiv.Perm PS)).prod (FiniteDist.uniform (Equiv.Perm BS))).expectation
        (fun orders => (reindexKernel orders.1 orders.2 kernel) colors centers) := by
    funext colors centers
    exact symmetrize_eq_expectation kernel colors centers
  rw [hkernel]
  apply (blockEnergy_average_le primary body _
    (fun orders : Equiv.Perm PS × Equiv.Perm BS => reindexKernel orders.1 orders.2 kernel)).trans
  simp only [blockEnergy_reindex, FiniteDist.expectation, ← Finset.sum_mul,
    FiniteDist.sum_one, one_mul]
  exact le_rfl

theorem blockL2_symmetrize_le (primary : FiniteDist Primary) (body : FiniteDist Body)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    blockL2 primary body (symmetrize kernel) ≤ blockL2 primary body kernel :=
  Real.sqrt_le_sqrt (blockEnergy_symmetrize_le primary body kernel)

/-- The manuscript's homogeneous star product is submultiplicative for the
actual Hilbert block norm, with no palette or population loss. -/
theorem homogeneousProduct_blockL2_le (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (first : canonicalKernels primary body r s)
    (second : canonicalKernels primary body r' s') :
    blockL2 primary body (homogeneousProduct primary body first second).val ≤
      blockL2 primary body first.val * blockL2 primary body second.val := by
  change blockL2 primary body (symmetrize (finDisjointTensor first.val second.val)) ≤ _
  calc
    _ ≤ blockL2 primary body (finDisjointTensor first.val second.val) :=
      blockL2_symmetrize_le primary body _
    _ = _ := by
      unfold finDisjointTensor
      rw [blockL2_reindex, blockL2_disjointTensor]

/-- Multiplicative arity weights in factor form, avoiding any rounding of
the half powers of the two population sizes. -/
def gradeWeight (primaryFactor bodyFactor : ℝ) (r s : ℕ) : ℝ :=
  primaryFactor ^ r * bodyFactor ^ s

theorem gradeWeight_nonneg (primaryFactor bodyFactor : ℝ)
    (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor) (r s : ℕ) :
    0 ≤ gradeWeight primaryFactor bodyFactor r s := by
  exact mul_nonneg (pow_nonneg hprimary _) (pow_nonneg hbody _)

theorem gradeWeight_add (primaryFactor bodyFactor : ℝ) (r s r' s' : ℕ) :
    gradeWeight primaryFactor bodyFactor (r + r') (s + s') =
      gradeWeight primaryFactor bodyFactor r s * gradeWeight primaryFactor bodyFactor r' s' := by
  simp only [gradeWeight, pow_add]
  ring





theorem weighted_homogeneousProduct_le (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    {r s r' s' : ℕ} (first : canonicalKernels primary body r s)
    (second : canonicalKernels primary body r' s') :
    gradeWeight primaryFactor bodyFactor (r + r') (s + s') *
        blockL2 primary body (homogeneousProduct primary body first second).val ≤
      (gradeWeight primaryFactor bodyFactor r s * blockL2 primary body first.val) *
        (gradeWeight primaryFactor bodyFactor r' s' * blockL2 primary body second.val) := by
  apply (mul_le_mul_of_nonneg_left (homogeneousProduct_blockL2_le primary body first second)
    (gradeWeight_nonneg primaryFactor bodyFactor hprimary hbody _ _)).trans_eq
  rw [gradeWeight_add]
  ring

/-- The actual graded l1 sum of Hilbert block norms, with the scalar absolute
value in degree zero. This is not a pointwise bound on the public weight. -/
def coefficientNorm (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (primaryFactor bodyFactor : ℝ) (coefficient : CoefficientSpace primary body order) : ℝ :=
  |coefficient.1| + ∑ arity : PositiveArity order,
    gradeWeight primaryFactor bodyFactor arity.val.1.val arity.val.2.val *
      blockL2 primary body (coefficient.2 arity).val



end

end CurrentAFT.ControlNorm

end

section










/-!
# Finite arity families and their actual truncated coefficient convolution

The coefficient space is represented by all canonical kernel fibers at
arities of total degree at most the fixed order, including degree zero.
The explicit linear equivalence below identifies this finite family with
`ControlCoordinates.CoefficientSpace`, whose scalar is stored separately.
Multiplication is an actual finite arity convolution of the already proved
homogeneous disjoint-slot products. No algebra law is included as a field
or used as a hypothesis.
-/

namespace CurrentAFT.GradedControlAlgebra

open AFT ControlCoordinates ControlProduct ControlNorm
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

abbrev TruncatedArity (order : ℕ) :=
  {arity : Fin (order + 1) × Fin (order + 1) // arity.1.val + arity.2.val ≤ order}

def zeroArity (order : ℕ) : TruncatedArity order := ⟨(0, 0), by simp⟩

def positiveArity (order : ℕ) (arity : PositiveArity order) : TruncatedArity order :=
  ⟨arity.val, arity.property.2⟩

abbrev KernelFamily (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :=
  (arity : TruncatedArity order) → canonicalKernels primary body arity.val.1.val arity.val.2.val

instance kernelFamily_finiteDimensional (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) : FiniteDimensional ℝ (KernelFamily primary body order) := by infer_instance

def scalarKernel (primary : FiniteDist Primary) (body : FiniteDist Body) (scalar : ℝ) :
    canonicalKernels primary body 0 0 := by
  refine ⟨fun _ _ => scalar, ?_, ?_, ?_⟩
  · intro index
    exact Fin.elim0 index
  · intro index
    exact Fin.elim0 index
  · unfold SeparatelySymmetric
    intros
    rfl

def scalarAt (primary : FiniteDist Primary) (body : FiniteDist Body)
    (kernel : canonicalKernels primary body 0 0) : ℝ :=
  kernel.val Fin.elim0 Fin.elim0

theorem scalarKernel_scalarAt (primary : FiniteDist Primary) (body : FiniteDist Body)
    (kernel : canonicalKernels primary body 0 0) :
    scalarKernel primary body (scalarAt primary body kernel) = kernel := by
  apply Subtype.ext
  funext colors centers
  have hc : colors = (Fin.elim0 : Fin 0 → Primary) := Subsingleton.elim _ _
  have hb : centers = (Fin.elim0 : Fin 0 → Body) := Subsingleton.elim _ _
  simp only [scalarKernel, scalarAt, hc, hb]

theorem scalarAt_injective (primary : FiniteDist Primary) (body : FiniteDist Body) :
    Function.Injective (scalarAt primary body) := by
  intro first second hequal
  rw [← scalarKernel_scalarAt primary body first, ← scalarKernel_scalarAt primary body second, hequal]

/-- Evaluate the zero fiber and retain every positive canonical kernel. -/
def familyToCoefficients (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    KernelFamily primary body order →ₗ[ℝ] CoefficientSpace primary body order where
  toFun family := (scalarAt primary body (family (zeroArity order)),
    fun arity => family (positiveArity order arity))
  map_add' first second := by
    apply Prod.ext
    · rfl
    · funext arity
      rfl
  map_smul' scalar family := by
    apply Prod.ext
    · rfl
    · funext arity
      rfl

/-- Reconstruct the zero kernel from the scalar; positive fibers are copied
without choosing a tensor basis or adding unconstrained higher arities. -/
def coefficientsToFamily (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (coefficient : CoefficientSpace primary body order) : KernelFamily primary body order := by
  intro arity
  rcases arity with ⟨⟨⟨r, hr⟩, ⟨s, hs⟩⟩, hdegree⟩
  by_cases hzero : r + s = 0
  · have hrzero : r = 0 := by omega
    have hszero : s = 0 := by omega
    subst r
    subst s
    exact scalarKernel primary body coefficient.1
  · exact coefficient.2 ⟨(⟨r, hr⟩, ⟨s, hs⟩), ⟨by change 1 ≤ r + s; omega, hdegree⟩⟩

theorem coefficientsToFamily_zero (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (coefficient : CoefficientSpace primary body order) :
    coefficientsToFamily primary body order coefficient (zeroArity order) =
      scalarKernel primary body coefficient.1 := by
  rfl

theorem coefficientsToFamily_positive (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (coefficient : CoefficientSpace primary body order) (arity : PositiveArity order) :
    coefficientsToFamily primary body order coefficient (positiveArity order arity) = coefficient.2 arity := by
  rcases arity with ⟨⟨⟨r, hr⟩, ⟨s, hs⟩⟩, hdegree⟩
  have hpositive : 1 ≤ r + s := hdegree.1
  have hzero : ¬r + s = 0 := by omega
  simp only [coefficientsToFamily, positiveArity, dif_neg hzero]

theorem familyToCoefficients_injective (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) : Function.Injective (familyToCoefficients primary body order) := by
  intro first second hequal
  funext arity
  by_cases hzero : arity.val.1.val + arity.val.2.val = 0
  · have harity : arity = zeroArity order := by
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext
      · change arity.val.1.val = 0
        omega
      · change arity.val.2.val = 0
        omega
    subst arity
    apply scalarAt_injective primary body
    exact congrArg Prod.fst hequal
  · let positive : PositiveArity order := ⟨arity.val, ⟨by omega, arity.property⟩⟩
    exact congrArg (fun coefficient => coefficient.2 positive) hequal

theorem familyToCoefficients_surjective (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) : Function.Surjective (familyToCoefficients primary body order) := by
  intro coefficient
  refine ⟨coefficientsToFamily primary body order coefficient, ?_⟩
  apply Prod.ext
  · change scalarAt primary body (coefficientsToFamily primary body order coefficient (zeroArity order)) = coefficient.1
    rw [coefficientsToFamily_zero]
    rfl
  · funext arity
    exact coefficientsToFamily_positive primary body order coefficient arity

/-- An actual linear equivalence with the current scalar-plus-positive-kernel
coefficient space, rather than a new abstract algebra representation. -/
def familyCoefficientEquiv (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    KernelFamily primary body order ≃ₗ[ℝ] CoefficientSpace primary body order :=
  LinearEquiv.ofBijective (familyToCoefficients primary body order)
    ⟨familyToCoefficients_injective primary body order, familyToCoefficients_surjective primary body order⟩

/-- Equality transport between fibers is only a relabeling of their finite
ordered slot types; it adds no new kernel values. -/
def transportKernel (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (hr : r = r') (hs : s = s')
    (kernel : canonicalKernels primary body r s) : canonicalKernels primary body r' s' := by
  subst r'
  subst s'
  exact kernel

theorem transportKernel_zero (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (hr : r = r') (hs : s = s') :
    transportKernel primary body hr hs (0 : canonicalKernels primary body r s) = 0 := by
  subst r'
  subst s'
  rfl

theorem transportKernel_add (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (hr : r = r') (hs : s = s') (first second : canonicalKernels primary body r s) :
    transportKernel primary body hr hs (first + second) =
      transportKernel primary body hr hs first + transportKernel primary body hr hs second := by
  subst r'
  subst s'
  rfl

theorem transportKernel_smul (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (hr : r = r') (hs : s = s') (scalar : ℝ) (kernel : canonicalKernels primary body r s) :
    transportKernel primary body hr hs (scalar • kernel) = scalar • transportKernel primary body hr hs kernel := by
  subst r'
  subst s'
  rfl

theorem transportKernel_val (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (hr : r = r') (hs : s = s') (kernel : canonicalKernels primary body r s) :
    (transportKernel primary body hr hs kernel).val = reindexKernel (finCongr hr) (finCongr hs) kernel.val := by
  subst r'
  subst s'
  rfl

theorem transportKernel_comp (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' r'' s'' : ℕ} (hr : r = r') (hs : s = s') (hr' : r' = r'') (hs' : s' = s'')
    (kernel : canonicalKernels primary body r s) :
    transportKernel primary body hr' hs' (transportKernel primary body hr hs kernel) =
      transportKernel primary body (hr.trans hr') (hs.trans hs') kernel := by
  subst r'
  subst s'
  subst r''
  subst s''
  rfl

theorem transport_homogeneousProduct_comm (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' targetR targetS : ℕ}
    (hr : r + r' = targetR) (hs : s + s' = targetS)
    (hr' : r' + r = targetR) (hs' : s' + s = targetS)
    (first : canonicalKernels primary body r s) (second : canonicalKernels primary body r' s') :
    transportKernel primary body hr hs (homogeneousProduct primary body first second) =
      transportKernel primary body hr' hs' (homogeneousProduct primary body second first) := by
  have hcomm : transportKernel primary body (Nat.add_comm r r') (Nat.add_comm s s')
      (homogeneousProduct primary body first second) = homogeneousProduct primary body second first := by
    apply Subtype.ext
    rw [transportKernel_val]
    exact ControlCoherence.homogeneousProduct_comm_cast primary body first second
  calc
    _ = transportKernel primary body hr' hs'
        (transportKernel primary body (Nat.add_comm r r') (Nat.add_comm s s')
          (homogeneousProduct primary body first second)) := by rw [transportKernel_comp]
    _ = _ := by rw [hcomm]

theorem transport_homogeneousProduct_unit_left (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s : ℕ} (kernel : canonicalKernels primary body r s) :
    transportKernel primary body (Nat.zero_add r) (Nat.zero_add s)
      (homogeneousProduct primary body (scalarUnit primary body) kernel) = kernel := by
  apply Subtype.ext
  rw [transportKernel_val]
  apply Eq.trans _ (homogeneousProduct_unit_left primary body kernel)
  exact ControlCoherence.symmetric_reindex_unique _ _ _ _ _
    (homogeneousProduct primary body (scalarUnit primary body) kernel).property.2.2



theorem homogeneousProduct_zero_left (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (second : canonicalKernels primary body r' s') :
    homogeneousProduct primary body (0 : canonicalKernels primary body r s) second = 0 := by
  apply Subtype.ext
  funext colors centers
  simp only [homogeneousProduct, symmetrize_apply, finDisjointTensor, reindexKernel,
    disjointTensor, Submodule.coe_zero, Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero]

theorem homogeneousProduct_zero_right (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (first : canonicalKernels primary body r s) :
    homogeneousProduct primary body first (0 : canonicalKernels primary body r' s') = 0 := by
  apply Subtype.ext
  funext colors centers
  simp only [homogeneousProduct, symmetrize_apply, finDisjointTensor, reindexKernel,
    disjointTensor, Submodule.coe_zero, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

theorem homogeneousProduct_add_left (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (first other : canonicalKernels primary body r s)
    (second : canonicalKernels primary body r' s') :
    homogeneousProduct primary body (first + other) second =
      homogeneousProduct primary body first second + homogeneousProduct primary body other second := by
  apply Subtype.ext
  funext colors centers
  simp only [homogeneousProduct, symmetrize_apply, finDisjointTensor, reindexKernel,
    disjointTensor, Submodule.coe_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

theorem homogeneousProduct_add_right (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (first : canonicalKernels primary body r s)
    (second other : canonicalKernels primary body r' s') :
    homogeneousProduct primary body first (second + other) =
      homogeneousProduct primary body first second + homogeneousProduct primary body first other := by
  apply Subtype.ext
  funext colors centers
  simp only [homogeneousProduct, symmetrize_apply, finDisjointTensor, reindexKernel,
    disjointTensor, Submodule.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The actual arity convolution. All summands use disjoint-slot multiplication,
and only output arities of total degree at most the fixed order exist. -/
def familyProduct (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first second : KernelFamily primary body order) : KernelFamily primary body order :=
  fun output => ∑ left : TruncatedArity order, ∑ right : TruncatedArity order,
    if hmatch : left.val.1.val + right.val.1.val = output.val.1.val ∧
        left.val.2.val + right.val.2.val = output.val.2.val then
      transportKernel primary body hmatch.1 hmatch.2
        (homogeneousProduct primary body (first left) (second right))
    else 0

theorem familyProduct_zero_left (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (second : KernelFamily primary body order) : familyProduct primary body order 0 second = 0 := by
  funext output
  simp only [familyProduct, Pi.zero_apply, homogeneousProduct_zero_left,
    transportKernel_zero, dite_eq_ite, ite_self, Finset.sum_const_zero]

theorem familyProduct_zero_right (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first : KernelFamily primary body order) : familyProduct primary body order first 0 = 0 := by
  funext output
  simp only [familyProduct, Pi.zero_apply, homogeneousProduct_zero_right,
    transportKernel_zero, dite_eq_ite, ite_self, Finset.sum_const_zero]

theorem familyProduct_add_left (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first other second : KernelFamily primary body order) :
    familyProduct primary body order (first + other) second =
      familyProduct primary body order first second + familyProduct primary body order other second := by
  funext output
  simp only [familyProduct, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro left _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro right _
  split_ifs with hmatch
  · rw [homogeneousProduct_add_left, transportKernel_add]
  · exact (add_zero 0).symm

theorem familyProduct_add_right (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first second other : KernelFamily primary body order) :
    familyProduct primary body order first (second + other) =
      familyProduct primary body order first second + familyProduct primary body order first other := by
  funext output
  simp only [familyProduct, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro left _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro right _
  split_ifs with hmatch
  · rw [homogeneousProduct_add_right, transportKernel_add]
  · exact (add_zero 0).symm

theorem familyProduct_comm (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first second : KernelFamily primary body order) :
    familyProduct primary body order first second = familyProduct primary body order second first := by
  funext output
  unfold familyProduct
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro right _
  apply Finset.sum_congr rfl
  intro left _
  split_ifs with hforward hreverse hreverse
  · exact transport_homogeneousProduct_comm primary body hforward.1 hforward.2 hreverse.1 hreverse.2 _ _
  · exfalso
    apply hreverse
    constructor <;> omega
  · exfalso
    apply hforward
    constructor <;> omega
  · rfl

def familyUnit (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    KernelFamily primary body order := Pi.single (zeroArity order) (scalarUnit primary body)

theorem familyProduct_unit_left (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (family : KernelFamily primary body order) :
    familyProduct primary body order (familyUnit primary body order) family = family := by
  funext output
  unfold familyProduct familyUnit
  rw [Finset.sum_eq_single (zeroArity order)]
  · rw [Pi.single_eq_same, Finset.sum_eq_single output]
    · rw [dif_pos (by constructor <;> exact Nat.zero_add _)]
      exact transport_homogeneousProduct_unit_left primary body (family output)
    · intro other _ hother
      rw [dif_neg]
      · intro hmatch
        apply hother
        apply Subtype.ext
        apply Prod.ext <;> apply Fin.ext
        · have := hmatch.1
          simpa only [zeroArity, Fin.val_zero, zero_add] using this
        · have := hmatch.2
          simpa only [zeroArity, Fin.val_zero, zero_add] using this
    · simp
  · intro other _ hother
    rw [Pi.single_eq_of_ne (M := fun arity : TruncatedArity order =>
      canonicalKernels primary body arity.val.1.val arity.val.2.val) hother (scalarUnit primary body)]
    apply Finset.sum_eq_zero
    intro right _
    split_ifs <;> simp only [homogeneousProduct_zero_left, transportKernel_zero]
  · simp

theorem familyProduct_unit_right (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (family : KernelFamily primary body order) :
    familyProduct primary body order family (familyUnit primary body order) = family := by
  rw [familyProduct_comm, familyProduct_unit_left]

theorem familyProduct_single (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (left right output : TruncatedArity order)
    (first : canonicalKernels primary body left.val.1.val left.val.2.val)
    (second : canonicalKernels primary body right.val.1.val right.val.2.val) :
    familyProduct primary body order (Pi.single left first) (Pi.single right second) output =
      if hmatch : left.val.1.val + right.val.1.val = output.val.1.val ∧
          left.val.2.val + right.val.2.val = output.val.2.val then
        transportKernel primary body hmatch.1 hmatch.2 (homogeneousProduct primary body first second)
      else 0 := by
  unfold familyProduct
  rw [Finset.sum_eq_single left]
  · rw [Pi.single_eq_same, Finset.sum_eq_single right]
    · rw [Pi.single_eq_same]
    · intro other _ hother
      rw [Pi.single_eq_of_ne (M := fun arity : TruncatedArity order =>
        canonicalKernels primary body arity.val.1.val arity.val.2.val) hother second]
      split_ifs <;> simp only [homogeneousProduct_zero_right, transportKernel_zero]
    · simp
  · intro other _ hother
    rw [Pi.single_eq_of_ne (M := fun arity : TruncatedArity order =>
      canonicalKernels primary body arity.val.1.val arity.val.2.val) hother first]
    apply Finset.sum_eq_zero
    intro otherRight _
    split_ifs <;> simp only [homogeneousProduct_zero_left, transportKernel_zero]
  · simp

def sumArity (order : ℕ) (left right : TruncatedArity order)
    (hdegree : (left.val.1.val + right.val.1.val) + (left.val.2.val + right.val.2.val) ≤ order) :
    TruncatedArity order :=
  ⟨(⟨left.val.1.val + right.val.1.val, by omega⟩,
    ⟨left.val.2.val + right.val.2.val, by omega⟩), hdegree⟩

theorem familyProduct_single_retained (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (left right : TruncatedArity order)
    (first : canonicalKernels primary body left.val.1.val left.val.2.val)
    (second : canonicalKernels primary body right.val.1.val right.val.2.val)
    (hdegree : (left.val.1.val + right.val.1.val) + (left.val.2.val + right.val.2.val) ≤ order) :
    familyProduct primary body order (Pi.single left first) (Pi.single right second) =
      Pi.single (sumArity order left right hdegree) (homogeneousProduct primary body first second) := by
  funext output
  rw [familyProduct_single]
  by_cases hequal : output = sumArity order left right hdegree
  · subst output
    rw [Pi.single_eq_same, dif_pos ⟨rfl, rfl⟩]
    rfl
  · rw [Pi.single_eq_of_ne (M := fun arity : TruncatedArity order =>
      canonicalKernels primary body arity.val.1.val arity.val.2.val) hequal]
    rw [dif_neg]
    intro hmatch
    apply hequal
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · exact hmatch.1.symm
    · exact hmatch.2.symm

theorem familyProduct_single_dropped (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (left right : TruncatedArity order)
    (first : canonicalKernels primary body left.val.1.val left.val.2.val)
    (second : canonicalKernels primary body right.val.1.val right.val.2.val)
    (hdegree : order < (left.val.1.val + right.val.1.val) + (left.val.2.val + right.val.2.val)) :
    familyProduct primary body order (Pi.single left first) (Pi.single right second) = 0 := by
  funext output
  rw [familyProduct_single]
  rw [dif_neg (by
    intro hmatch
    have houtput := output.property
    omega)]
  rfl

 theorem single_eq_of_transport (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    {left right : TruncatedArity order}
    (hr : left.val.1.val = right.val.1.val) (hs : left.val.2.val = right.val.2.val)
    (first : canonicalKernels primary body left.val.1.val left.val.2.val)
    (second : canonicalKernels primary body right.val.1.val right.val.2.val)
    (hequal : transportKernel primary body hr hs first = second) :
    (Pi.single left first : KernelFamily primary body order) = Pi.single right second := by
  have harity : left = right := by
    apply Subtype.ext
    exact Prod.ext (Fin.ext hr) (Fin.ext hs)
  subst right
  have hkernel : first = second := hequal
  rw [hkernel]

theorem familyProduct_single_assoc (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (left middle right : TruncatedArity order)
    (first : canonicalKernels primary body left.val.1.val left.val.2.val)
    (second : canonicalKernels primary body middle.val.1.val middle.val.2.val)
    (third : canonicalKernels primary body right.val.1.val right.val.2.val) :
    familyProduct primary body order
        (familyProduct primary body order (Pi.single left first) (Pi.single middle second)) (Pi.single right third) =
      familyProduct primary body order (Pi.single left first)
        (familyProduct primary body order (Pi.single middle second) (Pi.single right third)) := by
  by_cases htotal : (left.val.1.val + middle.val.1.val + right.val.1.val) +
      (left.val.2.val + middle.val.2.val + right.val.2.val) ≤ order
  · have hleft : (left.val.1.val + middle.val.1.val) + (left.val.2.val + middle.val.2.val) ≤ order := by omega
    have hright : (middle.val.1.val + right.val.1.val) + (middle.val.2.val + right.val.2.val) ≤ order := by omega
    have hlaterLeft : ((sumArity order left middle hleft).val.1.val + right.val.1.val) +
        ((sumArity order left middle hleft).val.2.val + right.val.2.val) ≤ order := htotal
    have hlaterRight : (left.val.1.val + (sumArity order middle right hright).val.1.val) +
        (left.val.2.val + (sumArity order middle right hright).val.2.val) ≤ order := by
      dsimp only [sumArity]
      omega
    rw [familyProduct_single_retained primary body order left middle first second hleft,
      familyProduct_single_retained primary body order middle right second third hright,
      familyProduct_single_retained primary body order _ right _ third hlaterLeft,
      familyProduct_single_retained primary body order left _ first _ hlaterRight]
    apply single_eq_of_transport primary body order
      (Nat.add_assoc _ _ _) (Nat.add_assoc _ _ _)
    apply Subtype.ext
    rw [transportKernel_val]
    exact ControlCoherence.homogeneousProduct_assoc primary body first second third
  · have hleftZero : familyProduct primary body order
        (familyProduct primary body order (Pi.single left first) (Pi.single middle second)) (Pi.single right third) = 0 := by
      by_cases hleft : (left.val.1.val + middle.val.1.val) + (left.val.2.val + middle.val.2.val) ≤ order
      · rw [familyProduct_single_retained primary body order left middle first second hleft]
        apply familyProduct_single_dropped
        dsimp only [sumArity]
        omega
      · rw [familyProduct_single_dropped primary body order left middle first second (by omega), familyProduct_zero_left]
    have hrightZero : familyProduct primary body order (Pi.single left first)
        (familyProduct primary body order (Pi.single middle second) (Pi.single right third)) = 0 := by
      by_cases hright : (middle.val.1.val + right.val.1.val) + (middle.val.2.val + right.val.2.val) ≤ order
      · rw [familyProduct_single_retained primary body order middle right second third hright]
        apply familyProduct_single_dropped
        dsimp only [sumArity]
        omega
      · rw [familyProduct_single_dropped primary body order middle right second third (by omega), familyProduct_zero_right]
    rw [hleftZero, hrightZero]





def familyLeftAddHom (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (second : KernelFamily primary body order) : KernelFamily primary body order →+ KernelFamily primary body order where
  toFun first := familyProduct primary body order first second
  map_zero' := familyProduct_zero_left primary body order second
  map_add' first other := familyProduct_add_left primary body order first other second

def familyRightAddHom (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first : KernelFamily primary body order) : KernelFamily primary body order →+ KernelFamily primary body order where
  toFun second := familyProduct primary body order first second
  map_zero' := familyProduct_zero_right primary body order first
  map_add' second other := familyProduct_add_right primary body order first second other

 theorem familyAddHom_ext_single (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first second : KernelFamily primary body order →+ KernelFamily primary body order)
    (hsingle : ∀ (arity : TruncatedArity order)
      (kernel : canonicalKernels primary body arity.val.1.val arity.val.2.val),
      first (Pi.single arity kernel) = second (Pi.single arity kernel)) : first = second := by
  apply AddMonoidHom.ext
  intro family
  rw [← Finset.univ_sum_single family, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro arity _
  exact hsingle arity (family arity)

/-- Associativity of the actual finite truncated convolution. Expansion into
single-arity families reduces it to the proved homogeneous associativity;
when total degree is too large, both bracketings vanish. -/
theorem familyProduct_assoc (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first second third : KernelFamily primary body order) :
    familyProduct primary body order (familyProduct primary body order first second) third =
      familyProduct primary body order first (familyProduct primary body order second third) := by
  have hthird (left middle : TruncatedArity order)
      (f : canonicalKernels primary body left.val.1.val left.val.2.val)
      (g : canonicalKernels primary body middle.val.1.val middle.val.2.val)
      (third : KernelFamily primary body order) :
      familyProduct primary body order
        (familyProduct primary body order (Pi.single left f) (Pi.single middle g)) third =
      familyProduct primary body order (Pi.single left f)
        (familyProduct primary body order (Pi.single middle g) third) := by
    let lhs := familyRightAddHom primary body order
      (familyProduct primary body order (Pi.single left f) (Pi.single middle g))
    let rhs := (familyRightAddHom primary body order (Pi.single left f)).comp
      (familyRightAddHom primary body order (Pi.single middle g))
    have hequal : lhs = rhs := familyAddHom_ext_single primary body order lhs rhs
      (fun right h => familyProduct_single_assoc primary body order left middle right f g h)
    exact DFunLike.congr_fun hequal third
  have hsecond (left : TruncatedArity order)
      (f : canonicalKernels primary body left.val.1.val left.val.2.val)
      (second third : KernelFamily primary body order) :
      familyProduct primary body order (familyProduct primary body order (Pi.single left f) second) third =
      familyProduct primary body order (Pi.single left f) (familyProduct primary body order second third) := by
    let lhs := (familyLeftAddHom primary body order third).comp
      (familyRightAddHom primary body order (Pi.single left f))
    let rhs := (familyRightAddHom primary body order (Pi.single left f)).comp
      (familyLeftAddHom primary body order third)
    have hequal : lhs = rhs := familyAddHom_ext_single primary body order lhs rhs
      (fun middle g => hthird left middle f g third)
    exact DFunLike.congr_fun hequal second
  let lhs := (familyLeftAddHom primary body order third).comp (familyLeftAddHom primary body order second)
  let rhs := familyLeftAddHom primary body order (familyProduct primary body order second third)
  have hequal : lhs = rhs := familyAddHom_ext_single primary body order lhs rhs
    (fun left f => hsecond left f second third)
  exact DFunLike.congr_fun hequal first

instance familyOne (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    One (KernelFamily primary body order) := ⟨familyUnit primary body order⟩

instance familyMul (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    Mul (KernelFamily primary body order) := ⟨familyProduct primary body order⟩

instance familyNatCast (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    NatCast (KernelFamily primary body order) := ⟨fun natural => natural • familyUnit primary body order⟩

instance familyIntCast (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    IntCast (KernelFamily primary body order) := ⟨fun integer => integer • familyUnit primary body order⟩

/-- The ring operations are the actual finite kernel convolution proved
above. The existing pointwise additive-group structure is preserved. -/
instance familyCommRing (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    CommRing (KernelFamily primary body order) where
  toAddCommGroup := inferInstanceAs (AddCommGroup (KernelFamily primary body order))
  mul := familyProduct primary body order
  one := familyUnit primary body order
  mul_assoc := familyProduct_assoc primary body order
  mul_comm := familyProduct_comm primary body order
  one_mul := familyProduct_unit_left primary body order
  mul_one := familyProduct_unit_right primary body order
  zero_mul := familyProduct_zero_left primary body order
  mul_zero := familyProduct_zero_right primary body order
  left_distrib := familyProduct_add_right primary body order
  right_distrib := familyProduct_add_left primary body order
  natCast natural := natural • familyUnit primary body order
  natCast_zero := zero_nsmul _
  natCast_succ natural := by
    change (natural + 1) • familyUnit primary body order =
      natural • familyUnit primary body order + familyUnit primary body order
    rw [add_nsmul, one_nsmul]
  intCast integer := integer • familyUnit primary body order
  intCast_ofNat natural := by
    change (natural : ℤ) • familyUnit primary body order = natural • familyUnit primary body order
    simp
  intCast_negSucc natural := by
    change (Int.negSucc natural) • familyUnit primary body order = -((natural + 1) • familyUnit primary body order)
    simp













end

end CurrentAFT.GradedControlAlgebra

end

section








/-!
# Exact finite inverses in the actual truncated control algebra

The augmentation ideal is nilpotent because its products increase total
arity. Consequently every background with scalar coordinate one has an
explicit finite inverse. This algebraic inverse needs no assumed
invertibility and is separate from the quantitative stability estimates.
-/

namespace CurrentAFT.GradedInverse

open AFT ControlCoordinates ControlProduct GradedControlAlgebra
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

def VanishesBelow (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order degree : ℕ) (family : KernelFamily primary body order) : Prop :=
  ∀ arity, arity.val.1.val + arity.val.2.val < degree → family arity = 0

theorem vanishesBelow_zero (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (family : KernelFamily primary body order) :
    VanishesBelow primary body order 0 family := by
  intro arity hdegree
  omega

theorem vanishesBelow_mul (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order firstDegree secondDegree : ℕ) (first second : KernelFamily primary body order)
    (hfirst : VanishesBelow primary body order firstDegree first)
    (hsecond : VanishesBelow primary body order secondDegree second) :
    VanishesBelow primary body order (firstDegree + secondDegree) (first * second) := by
  intro output houtput
  change familyProduct primary body order first second output = 0
  unfold familyProduct
  apply Finset.sum_eq_zero
  intro left _
  apply Finset.sum_eq_zero
  intro right _
  split_ifs with hmatch
  · by_cases hleft : left.val.1.val + left.val.2.val < firstDegree
    · rw [hfirst left hleft, homogeneousProduct_zero_left, transportKernel_zero]
    · have hright : right.val.1.val + right.val.2.val < secondDegree := by omega
      rw [hsecond right hright, homogeneousProduct_zero_right, transportKernel_zero]
  · rfl

theorem vanishesBelow_one_of_zero (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (family : KernelFamily primary body order)
    (hzero : family (zeroArity order) = 0) :
    VanishesBelow primary body order 1 family := by
  intro arity hdegree
  have harity : arity = zeroArity order := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · change arity.val.1.val = 0
      omega
    · change arity.val.2.val = 0
      omega
  rw [harity, hzero]





def backgroundInverse (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (background : KernelFamily primary body order) : KernelFamily primary body order :=
  ∑ power ∈ Finset.range (order + 1), (1 - background) ^ power





end

end CurrentAFT.GradedInverse

end

section








/-!
# Submultiplicativity of the actual finite graded coefficient norm

The proof sums the already verified Hilbert block inequalities over the
actual arity convolution. Each pair of input arities has at most one output
arity. The proof therefore introduces no dimension or palette factor.
The scalar-plus-positive coefficient norm is identified with this finite
family norm by an explicit split of the zero and positive arities.
-/

namespace CurrentAFT.GradedControlNorm

open AFT ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

 theorem blockL2_zero (primary : FiniteDist Primary) (body : FiniteDist Body)
    (r s : ℕ) :
    blockL2 primary body (0 : DensityKernel (Primary := Primary) (Body := Body) r s) = 0 := by
  simp only [blockL2, blockEnergy_apply, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
    mul_zero, Finset.sum_const_zero, Real.sqrt_zero]

 theorem canonical_sum_l2_le {Index : Type*} (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s : ℕ} (terms : Finset Index) (kernels : Index → canonicalKernels primary body r s) :
    blockL2 primary body (∑ index ∈ terms, kernels index).val ≤
      ∑ index ∈ terms, blockL2 primary body (kernels index).val := by
  induction terms using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Submodule.coe_zero, blockL2_zero, le_refl]
  | @insert index terms hnot ih =>
    simp only [Finset.sum_insert hnot, Submodule.coe_add]
    exact (blockL2_add_le primary body _ _).trans (add_le_add le_rfl ih)

theorem transportKernel_blockL2 (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (hr : r = r') (hs : s = s') (kernel : canonicalKernels primary body r s) :
    blockL2 primary body (transportKernel primary body hr hs kernel).val =
      blockL2 primary body kernel.val := by
  subst r'
  subst s'
  rfl

/-- The full finite weighted l1 sum of the genuine Hilbert block norms. -/
def familyNorm (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (family : KernelFamily primary body order) : ℝ :=
  ∑ arity : TruncatedArity order,
    gradeWeight primaryFactor bodyFactor arity.val.1.val arity.val.2.val *
      blockL2 primary body (family arity).val

theorem familyNorm_nonneg (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    (family : KernelFamily primary body order) : 0 ≤ familyNorm primary body order primaryFactor bodyFactor family := by
  apply Finset.sum_nonneg
  intro arity _
  exact mul_nonneg (gradeWeight_nonneg primaryFactor bodyFactor hprimary hbody _ _) (blockL2_nonneg primary body _)

 theorem sum_cycle {First Second Third : Type*}
    [Fintype First] [Fintype Second] [Fintype Third] (term : First → Second → Third → ℝ) :
    (∑ first, ∑ second, ∑ third, term first second third) =
      ∑ second, ∑ third, ∑ first, term first second third := by
  calc
    _ = ∑ second, ∑ first, ∑ third, term first second third := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro second _
      exact Finset.sum_comm

/-- Submultiplicativity for the actual truncated convolution. The sums are
over every legal arity, and pairs whose total degree is too large contribute
nothing rather than producing a multiplicity loss. -/
theorem familyNorm_product_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    (first second : KernelFamily primary body order) :
    familyNorm primary body order primaryFactor bodyFactor (familyProduct primary body order first second) ≤
      familyNorm primary body order primaryFactor bodyFactor first *
        familyNorm primary body order primaryFactor bodyFactor second := by
  let inputBound (left right : TruncatedArity order) : ℝ :=
    (gradeWeight primaryFactor bodyFactor left.val.1.val left.val.2.val * blockL2 primary body (first left).val) *
      (gradeWeight primaryFactor bodyFactor right.val.1.val right.val.2.val * blockL2 primary body (second right).val)
  let term (output left right : TruncatedArity order) :
      canonicalKernels primary body output.val.1.val output.val.2.val :=
    if hmatch : left.val.1.val + right.val.1.val = output.val.1.val ∧
        left.val.2.val + right.val.2.val = output.val.2.val then
      transportKernel primary body hmatch.1 hmatch.2 (homogeneousProduct primary body (first left) (second right))
    else 0
  let bound (output left right : TruncatedArity order) : ℝ :=
    if left.val.1.val + right.val.1.val = output.val.1.val ∧
        left.val.2.val + right.val.2.val = output.val.2.val then inputBound left right else 0
  have hterm (output left right : TruncatedArity order) :
      gradeWeight primaryFactor bodyFactor output.val.1.val output.val.2.val *
        blockL2 primary body (term output left right).val ≤ bound output left right := by
    dsimp only [term, bound]
    split_ifs with hmatch
    · rw [transportKernel_blockL2, ← hmatch.1, ← hmatch.2]
      exact weighted_homogeneousProduct_le primary body primaryFactor bodyFactor hprimary hbody _ _
    · simp only [Submodule.coe_zero, blockL2_zero, mul_zero, le_refl]
  have houtput (output : TruncatedArity order) :
      gradeWeight primaryFactor bodyFactor output.val.1.val output.val.2.val *
        blockL2 primary body ((familyProduct primary body order first second) output).val ≤
      ∑ left, ∑ right, bound output left right := by
    have hweight := gradeWeight_nonneg primaryFactor bodyFactor hprimary hbody output.val.1.val output.val.2.val
    change gradeWeight primaryFactor bodyFactor output.val.1.val output.val.2.val *
      blockL2 primary body (∑ left, ∑ right, term output left right).val ≤ _
    calc
      _ ≤ gradeWeight primaryFactor bodyFactor output.val.1.val output.val.2.val *
          ∑ left, blockL2 primary body (∑ right, term output left right).val :=
        mul_le_mul_of_nonneg_left (canonical_sum_l2_le primary body _ _) hweight
      _ ≤ gradeWeight primaryFactor bodyFactor output.val.1.val output.val.2.val *
          ∑ left, ∑ right, blockL2 primary body (term output left right).val := by
        apply mul_le_mul_of_nonneg_left _ hweight
        apply Finset.sum_le_sum
        intro left _
        exact canonical_sum_l2_le primary body _ _
      _ = ∑ left, ∑ right,
          gradeWeight primaryFactor bodyFactor output.val.1.val output.val.2.val *
            blockL2 primary body (term output left right).val := by simp only [Finset.mul_sum]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro left _
        apply Finset.sum_le_sum
        intro right _
        exact hterm output left right
  have hpair (left right : TruncatedArity order) : (∑ output, bound output left right) ≤ inputBound left right := by
    have hnonneg : 0 ≤ inputBound left right := mul_nonneg
      (mul_nonneg (gradeWeight_nonneg primaryFactor bodyFactor hprimary hbody _ _) (blockL2_nonneg primary body _))
      (mul_nonneg (gradeWeight_nonneg primaryFactor bodyFactor hprimary hbody _ _) (blockL2_nonneg primary body _))
    by_cases hexists : ∃ output : TruncatedArity order,
        left.val.1.val + right.val.1.val = output.val.1.val ∧
          left.val.2.val + right.val.2.val = output.val.2.val
    · obtain ⟨chosen, hchosen⟩ := hexists
      have hequal (output : TruncatedArity order) :
          (left.val.1.val + right.val.1.val = output.val.1.val ∧
            left.val.2.val + right.val.2.val = output.val.2.val) ↔ output = chosen := by
        constructor
        · intro hmatch
          apply Subtype.ext
          apply Prod.ext <;> apply Fin.ext
          · exact hmatch.1.symm.trans hchosen.1
          · exact hmatch.2.symm.trans hchosen.2
        · intro hmatch
          subst output
          exact hchosen
      simp only [bound, hequal, Finset.sum_ite_eq', Finset.mem_univ, if_true, le_refl]
    · have hnone (output : TruncatedArity order) :
          ¬(left.val.1.val + right.val.1.val = output.val.1.val ∧
            left.val.2.val + right.val.2.val = output.val.2.val) := fun h => hexists ⟨output, h⟩
      simpa only [bound, if_neg (hnone _), Finset.sum_const_zero] using hnonneg
  calc
    _ ≤ ∑ output, ∑ left, ∑ right, bound output left right :=
      Finset.sum_le_sum fun output _ => houtput output
    _ = ∑ left, ∑ right, ∑ output, bound output left right := sum_cycle bound
    _ ≤ ∑ left, ∑ right, inputBound left right := by
      apply Finset.sum_le_sum
      intro left _
      apply Finset.sum_le_sum
      intro right _
      exact hpair left right
    _ = _ := by simp only [inputBound, familyNorm, Finset.sum_mul_sum]

 theorem arity_eq_zero_iff (order : ℕ) (arity : TruncatedArity order) :
    arity = zeroArity order ↔ arity.val.1.val + arity.val.2.val = 0 := by
  constructor
  · intro hequal
    subst arity
    rfl
  · intro hzero
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · change arity.val.1.val = 0
      omega
    · change arity.val.2.val = 0
      omega

 theorem positiveArity_ne_zero (order : ℕ) (arity : PositiveArity order) :
    positiveArity order arity ≠ zeroArity order := by
  intro hequal
  have hzero := (arity_eq_zero_iff order (positiveArity order arity)).mp hequal
  change arity.val.1.val + arity.val.2.val = 0 at hzero
  have hpositive := arity.property.1
  omega

/-- A literal finite split into the unique scalar arity and all positive
arities, used to compare the two actual coefficient representations. -/
def aritySplit (order : ℕ) : Unit ⊕ PositiveArity order ≃ TruncatedArity order :=
  Equiv.ofBijective (Sum.elim (fun _ : Unit => zeroArity order) (positiveArity order)) (by
    constructor
    · intro first second hequal
      cases first with
      | inl first =>
        cases second with
        | inl second => cases first; cases second; rfl
        | inr second => exact False.elim ((positiveArity_ne_zero order second) hequal.symm)
      | inr first =>
        cases second with
        | inl second => exact False.elim ((positiveArity_ne_zero order first) hequal)
        | inr second =>
          apply congrArg Sum.inr
          apply Subtype.ext
          exact congrArg (fun arity : TruncatedArity order => arity.val) hequal
    · intro arity
      by_cases hzero : arity.val.1.val + arity.val.2.val = 0
      · exact ⟨Sum.inl (), ((arity_eq_zero_iff order arity).mpr hzero).symm⟩
      · exact ⟨Sum.inr ⟨arity.val, ⟨by omega, arity.property⟩⟩, rfl⟩)

theorem blockL2_scalarKernel (primary : FiniteDist Primary) (body : FiniteDist Body) (scalar : ℝ) :
    blockL2 primary body (scalarKernel primary body scalar).val = |scalar| := by
  simp only [blockL2, blockEnergy, scalarKernel, FiniteDist.l2Sq, FiniteDist.expectation,
    ← Finset.sum_mul, FiniteDist.sum_one, one_mul, Real.sqrt_sq_eq_abs]









end

end CurrentAFT.GradedControlNorm

end

section








/-!
# Stability in the actual finite graded coefficient norm

Triangle, absolute homogeneity, and separation follow from the genuine
weighted finite block sums. The finite-dimensional inverse argument is then
stated for an actual linear map on the coefficient family, using a pointwise
defect estimate in this same norm. This avoids installing an unrelated
ambient norm or assuming a normed algebra.

The construction must still prove the displayed defect estimate for its
complete response. Positive reference atoms and positive population/radius
factors are explicit; the actual safe-control instance discharges them.
-/

namespace CurrentAFT.GradedControlStability

open AFT ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GradedControlNorm
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

theorem familyNorm_zero (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) : familyNorm primary body order primaryFactor bodyFactor 0 = 0 := by
  simp only [familyNorm, Pi.zero_apply, Submodule.coe_zero, blockL2, blockEnergy_apply,
    zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero, Real.sqrt_zero]

theorem familyNorm_add_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    (first second : KernelFamily primary body order) :
    familyNorm primary body order primaryFactor bodyFactor (first + second) ≤
      familyNorm primary body order primaryFactor bodyFactor first +
        familyNorm primary body order primaryFactor bodyFactor second := by
  simp only [familyNorm, Pi.add_apply, Submodule.coe_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro arity _
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (blockL2_add_le primary body _ _)
    (gradeWeight_nonneg primaryFactor bodyFactor hprimary hbody _ _)

theorem familyNorm_smul (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor scalar : ℝ) (family : KernelFamily primary body order) :
    familyNorm primary body order primaryFactor bodyFactor (scalar • family) =
      |scalar| * familyNorm primary body order primaryFactor bodyFactor family := by
  simp only [familyNorm, Pi.smul_apply, Submodule.coe_smul, blockL2_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro arity _
  ring

theorem familyNorm_neg (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (family : KernelFamily primary body order) :
    familyNorm primary body order primaryFactor bodyFactor (-family) =
      familyNorm primary body order primaryFactor bodyFactor family := by
  simpa only [neg_one_smul, abs_neg, abs_one, one_mul] using
    familyNorm_smul primary body order primaryFactor bodyFactor (-1) family

theorem familyNorm_eq_zero_iff (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (hprimaryLaw : ∀ color, 0 < primary.weight color) (hbodyLaw : ∀ center, 0 < body.weight center)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 < primaryFactor) (hbody : 0 < bodyFactor)
    (family : KernelFamily primary body order) :
    familyNorm primary body order primaryFactor bodyFactor family = 0 ↔ family = 0 := by
  constructor
  · intro hzero
    have hterms := (Finset.sum_eq_zero_iff_of_nonneg (fun arity _ => mul_nonneg
      (gradeWeight_nonneg primaryFactor bodyFactor hprimary.le hbody.le _ _) (blockL2_nonneg primary body _))).mp hzero
    funext arity
    have hweight : 0 < gradeWeight primaryFactor bodyFactor arity.val.1.val arity.val.2.val :=
      mul_pos (pow_pos hprimary _) (pow_pos hbody _)
    have hblock : blockL2 primary body (family arity).val = 0 :=
      (mul_eq_zero.mp (hterms arity (Finset.mem_univ _))).resolve_left (ne_of_gt hweight)
    apply Subtype.ext
    exact (blockL2_eq_zero_iff primary body hprimaryLaw hbodyLaw _).mp hblock
  · intro hzero
    rw [hzero, familyNorm_zero]

/-- A pointwise small defect in the actual norm gives the lower norm bound
used for stable inversion. No continuity or topological operator norm is an
input assumption. -/
theorem family_operator_norm_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    (operator : KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order)
    (theta : ℝ) (hgap : theta < 1)
    (hdefect : ∀ family, familyNorm primary body order primaryFactor bodyFactor (family - operator family) ≤
      theta * familyNorm primary body order primaryFactor bodyFactor family)
    (family : KernelFamily primary body order) :
    familyNorm primary body order primaryFactor bodyFactor family ≤
      familyNorm primary body order primaryFactor bodyFactor (operator family) / (1 - theta) := by
  have htriangle := familyNorm_add_le primary body order primaryFactor bodyFactor hprimary hbody
    (operator family) (family - operator family)
  have hequal : operator family + (family - operator family) = family := by abel
  rw [hequal] at htriangle
  apply (le_div_iff₀ (sub_pos.mpr hgap)).mpr
  nlinarith [hdefect family]

theorem family_operator_injective (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (hprimaryLaw : ∀ color, 0 < primary.weight color) (hbodyLaw : ∀ center, 0 < body.weight center)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 < primaryFactor) (hbody : 0 < bodyFactor)
    (operator : KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order)
    (theta : ℝ) (hgap : theta < 1)
    (hdefect : ∀ family, familyNorm primary body order primaryFactor bodyFactor (family - operator family) ≤
      theta * familyNorm primary body order primaryFactor bodyFactor family) :
    Function.Injective operator := by
  intro first second hequal
  have hbound := family_operator_norm_le primary body order primaryFactor bodyFactor hprimary.le hbody.le
    operator theta hgap hdefect (first - second)
  have hoperator : operator (first - second) = 0 := by rw [map_sub, hequal, sub_self]
  rw [hoperator, familyNorm_zero, zero_div] at hbound
  have hnorm : familyNorm primary body order primaryFactor bodyFactor (first - second) = 0 :=
    le_antisymm hbound (familyNorm_nonneg primary body order primaryFactor bodyFactor hprimary.le hbody.le _)
  exact sub_eq_zero.mp ((familyNorm_eq_zero_iff primary body order hprimaryLaw hbodyLaw
    primaryFactor bodyFactor hprimary hbody _).mp hnorm)

/-- Finite-dimensionality supplies surjectivity only after injectivity has
been proved from the actual norm and pointwise defect estimate. -/
theorem family_operator_bijective (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (hprimaryLaw : ∀ color, 0 < primary.weight color) (hbodyLaw : ∀ center, 0 < body.weight center)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 < primaryFactor) (hbody : 0 < bodyFactor)
    (operator : KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order)
    (theta : ℝ) (hgap : theta < 1)
    (hdefect : ∀ family, familyNorm primary body order primaryFactor bodyFactor (family - operator family) ≤
      theta * familyNorm primary body order primaryFactor bodyFactor family) :
    Function.Bijective operator := by
  have hinjective := family_operator_injective primary body order hprimaryLaw hbodyLaw
    primaryFactor bodyFactor hprimary hbody operator theta hgap hdefect
  exact ⟨hinjective, LinearMap.surjective_of_injective hinjective⟩

/-- The finite calibration solve in the actual coefficient space, including
the correction bound relative to any reference coefficient. The full physical
response's defect estimate remains an explicit construction obligation. -/
theorem family_calibration_existsUnique (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (hprimaryLaw : ∀ color, 0 < primary.weight color) (hbodyLaw : ∀ center, 0 < body.weight center)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 < primaryFactor) (hbody : 0 < bodyFactor)
    (operator : KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order)
    (theta : ℝ) (hgap : theta < 1)
    (hdefect : ∀ family, familyNorm primary body order primaryFactor bodyFactor (family - operator family) ≤
      theta * familyNorm primary body order primaryFactor bodyFactor family)
    (target : KernelFamily primary body order) :
    ∃ coefficient, operator coefficient = target ∧
      (∀ other, operator other = target → other = coefficient) ∧
      ∀ reference, familyNorm primary body order primaryFactor bodyFactor (coefficient - reference) ≤
        familyNorm primary body order primaryFactor bodyFactor (target - operator reference) / (1 - theta) := by
  have hbijective := family_operator_bijective primary body order hprimaryLaw hbodyLaw
    primaryFactor bodyFactor hprimary hbody operator theta hgap hdefect
  obtain ⟨coefficient, hcoefficient⟩ := hbijective.2 target
  refine ⟨coefficient, hcoefficient, fun other hother => hbijective.1 (hother.trans hcoefficient.symm), ?_⟩
  intro reference
  simpa only [map_sub, hcoefficient] using family_operator_norm_le primary body order
    primaryFactor bodyFactor hprimary.le hbody.le operator theta hgap hdefect (coefficient - reference)

end

end CurrentAFT.GradedControlStability

end

section












/-!
# Actual free and translated certificates in the finite graded algebra

The density coefficients are the concrete certificates already constructed
from the current proposal. Body coefficients are restricted to the actual
safe alphabet, on which the reference law is strictly positive. Each atom
is inserted into its genuine degree-one fiber of the finite family.
-/

namespace CurrentAFT.BackgroundFamilies

open AFT ControlCoordinates ControlNorm GradedControlAlgebra GradedControlNorm
  GradedControlStability DiffuseProfiles ProposalPrimary FringeCertificate
  BackgroundCertificates BackgroundTranslations BackgroundRates ActualControls
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw
  ProposalPrimary.centerLaw InwardAnchor.smoothedAnchorLaw

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

def primaryKernel (primary : FiniteDist Primary) (body : FiniteDist Body)
    (density : Primary → ℝ) (hcenter : ∑ color, primary.weight color * density color = 0) :
    canonicalKernels primary body 1 0 := by
  refine ⟨fun colors _ => density (colors 0), ?_, ?_, ?_⟩
  · intro index colors centers
    have hi : index = 0 := Subsingleton.elim _ _
    subst index
    simpa only [Function.update_self] using hcenter
  · intro index
    exact Fin.elim0 index
  · intro primaryOrder bodyOrder colors centers
    have hi : primaryOrder 0 = 0 := Subsingleton.elim _ _
    simp only [Function.comp_apply, hi]

def bodyKernel (primary : FiniteDist Primary) (body : FiniteDist Body)
    (density : Body → ℝ) (hcenter : ∑ color, body.weight color * density color = 0) :
    canonicalKernels primary body 0 1 := by
  refine ⟨fun _ centers => density (centers 0), ?_, ?_, ?_⟩
  · intro index
    exact Fin.elim0 index
  · intro index colors centers
    have hi : index = 0 := Subsingleton.elim _ _
    subst index
    simpa only [Function.update_self] using hcenter
  · intro primaryOrder bodyOrder colors centers
    have hi : bodyOrder 0 = 0 := Subsingleton.elim _ _
    simp only [Function.comp_apply, hi]

theorem primaryKernel_blockL2 (primary : FiniteDist Primary) (body : FiniteDist Body)
    (density : Primary → ℝ) (hcenter : ∑ color, primary.weight color * density color = 0) :
    blockL2 primary body (primaryKernel primary body density hcenter).val =
      Real.sqrt (∑ color, primary.weight color * density color ^ 2) := by
  unfold blockL2
  congr 1
  rw [blockEnergy_apply]
  simp only [primaryKernel, Fin.prod_univ_zero, mul_one,
    Finset.univ_unique, Finset.sum_singleton, Finset.prod_singleton]
  change (∑ colors : Fin 1 → Primary, primary.weight (colors 0) * density (colors 0) ^ 2) = _
  exact ((Equiv.funUnique (Fin 1) Primary).symm.sum_comp
    (fun colors => primary.weight (colors 0) * density (colors 0) ^ 2)).symm

theorem bodyKernel_blockL2 (primary : FiniteDist Primary) (body : FiniteDist Body)
    (density : Body → ℝ) (hcenter : ∑ color, body.weight color * density color = 0) :
    blockL2 primary body (bodyKernel primary body density hcenter).val =
      Real.sqrt (∑ color, body.weight color * density color ^ 2) := by
  unfold blockL2
  congr 1
  rw [blockEnergy_apply]
  simp only [bodyKernel, Fin.prod_univ_zero, one_mul,
    Finset.univ_unique, Finset.sum_singleton, Finset.prod_singleton]
  change (∑ colors : Fin 1 → Body, body.weight (colors 0) * density (colors 0) ^ 2) = _
  exact ((Equiv.funUnique (Fin 1) Body).symm.sum_comp
    (fun colors => body.weight (colors 0) * density (colors 0) ^ 2)).symm

def primaryArity (order : ℕ) (horder : 1 ≤ order) : TruncatedArity order :=
  ⟨(⟨1, by omega⟩, 0), by simpa⟩

def bodyArity (order : ℕ) (horder : 1 ≤ order) : TruncatedArity order :=
  ⟨(0, ⟨1, by omega⟩), by simpa⟩

def primaryFamily (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (horder : 1 ≤ order) (density : Primary → ℝ)
    (hcenter : ∑ color, primary.weight color * density color = 0) :
    KernelFamily primary body order :=
  Pi.single (primaryArity order horder) (primaryKernel primary body density hcenter)

def bodyFamily (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (horder : 1 ≤ order) (density : Body → ℝ)
    (hcenter : ∑ color, body.weight color * density color = 0) :
    KernelFamily primary body order :=
  Pi.single (bodyArity order horder) (bodyKernel primary body density hcenter)

theorem familyNorm_single (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (primaryFactor bodyFactor : ℝ) (arity : TruncatedArity order)
    (kernel : canonicalKernels primary body arity.val.1.val arity.val.2.val) :
    familyNorm primary body order primaryFactor bodyFactor (Pi.single arity kernel) =
      gradeWeight primaryFactor bodyFactor arity.val.1.val arity.val.2.val *
        blockL2 primary body kernel.val := by
  unfold familyNorm
  rw [Finset.sum_eq_single arity]
  · rw [Pi.single_eq_same]
  · intro other _ hne
    rw [Pi.single_eq_of_ne hne]
    simp only [Submodule.coe_zero, blockL2, blockEnergy_apply, Pi.zero_apply,
      zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero, Real.sqrt_zero]
  · intro hout
    exact (hout (Finset.mem_univ arity)).elim

theorem primaryFamily_norm (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (horder : 1 ≤ order) (primaryFactor bodyFactor : ℝ) (density : Primary → ℝ)
    (hcenter : ∑ color, primary.weight color * density color = 0) :
    familyNorm primary body order primaryFactor bodyFactor
      (primaryFamily primary body order horder density hcenter) =
        primaryFactor * Real.sqrt (∑ color, primary.weight color * density color ^ 2) := by
  rw [primaryFamily, familyNorm_single, primaryKernel_blockL2]
  simp [primaryArity, gradeWeight]

theorem bodyFamily_norm (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (horder : 1 ≤ order) (primaryFactor bodyFactor : ℝ) (density : Body → ℝ)
    (hcenter : ∑ color, body.weight color * density color = 0) :
    familyNorm primary body order primaryFactor bodyFactor
      (bodyFamily primary body order horder density hcenter) =
        bodyFactor * Real.sqrt (∑ color, body.weight color * density color ^ 2) := by
  rw [bodyFamily, familyNorm_single, bodyKernel_blockL2]
  simp [bodyArity, gradeWeight]

theorem safe_centered (security : ℕ) (density : ActualControls.Palette security → ℝ)
    (hcenter : ∑ color, (centerLaw security).weight color * density color = 0) :
    ∑ color, (bodyReference security).weight color * density color.val = 0 := by
  exact (supportedLaw_expectation (centerLaw security) (InwardAnchor.SafeColor security)
    _ density).trans hcenter

theorem safe_square (security : ℕ) (density : ActualControls.Palette security → ℝ) :
    (∑ color, (bodyReference security).weight color * density color.val ^ 2) =
      ∑ color, (centerLaw security).weight color * density color ^ 2 :=
  supportedLaw_expectation (centerLaw security) (InwardAnchor.SafeColor security) _
    (fun color => density color ^ 2)

abbrev ActualFamily (security order : ℕ) :=
  KernelFamily (primaryLaw security) (bodyReference security) order

def freeCertificate (security order : ℕ) (horder : 1 ≤ order) : ActualFamily security order :=
  primaryFamily (primaryLaw security) (bodyReference security) order horder
      (primaryCertificateDensity security) (primaryCertificateDensity_centered security) +
    bodyFamily (primaryLaw security) (bodyReference security) order horder
      (fun color => bodyCertificateDensity security color.val)
        (safe_centered security _ (bodyCertificateDensity_centered security))

def translationCertificate (security order : ℕ) (horder : 1 ≤ order) (shift : ℤ) :
    ActualFamily security order :=
  primaryFamily (primaryLaw security) (bodyReference security) order horder
      (primaryCertificateDensity security) (primaryCertificateDensity_centered security) +
    primaryFamily (primaryLaw security) (bodyReference security) order horder
      (residualCertificateDensity security shift) (residualCertificateDensity_centered security shift) +
    bodyFamily (primaryLaw security) (bodyReference security) order horder
      (fun color => safeSeedDensity security shift color.val)
        (safe_centered security _ (safeSeedDensity_centered security shift))

attribute [local irreducible] primaryFamily bodyFamily ActualControls.bodyReference
  BackgroundRates.primaryFactor BackgroundRates.bodyFactor BackgroundRates.radius
  primaryCertificateDensity bodyCertificateDensity residualCertificateDensity safeSeedDensity

theorem freeCertificate_norm (security order : ℕ) (horder : 1 ≤ order) :
    familyNorm (primaryLaw security) (bodyReference security) order
      (primaryFactor security) (bodyFactor security) (freeCertificate security order horder) ≤
        freeAtomEnvelope security := by
  have hprimary : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hbody : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  apply (familyNorm_add_le _ _ _ _ _ hprimary hbody _ _).trans_eq
  rw [primaryFamily_norm, bodyFamily_norm, safe_square]
  rfl

theorem translationCertificate_norm (security order : ℕ) (horder : 1 ≤ order) (shift : ℤ) :
    familyNorm (primaryLaw security) (bodyReference security) order
      (primaryFactor security) (bodyFactor security) (translationCertificate security order horder shift) ≤
        translationAtomEnvelope security shift := by
  have hprimary : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hbody : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  have h1 := familyNorm_add_le (primaryLaw security) (bodyReference security) order
    (primaryFactor security) (bodyFactor security) hprimary hbody
    (primaryFamily _ _ order horder (primaryCertificateDensity security) (primaryCertificateDensity_centered security))
    (primaryFamily _ _ order horder (residualCertificateDensity security shift) (residualCertificateDensity_centered security shift))
  have h2 := familyNorm_add_le (primaryLaw security) (bodyReference security) order
    (primaryFactor security) (bodyFactor security) hprimary hbody
    (primaryFamily _ _ order horder (primaryCertificateDensity security) (primaryCertificateDensity_centered security) +
      primaryFamily _ _ order horder (residualCertificateDensity security shift) (residualCertificateDensity_centered security shift))
    (bodyFamily _ _ order horder (fun color => safeSeedDensity security shift color.val)
      (safe_centered security _ (safeSeedDensity_centered security shift)))
  apply h2.trans
  apply (add_le_add h1 le_rfl).trans_eq
  rw [primaryFamily_norm, primaryFamily_norm, bodyFamily_norm, safe_square]
  unfold translationAtomEnvelope
  ring



def primaryCoefficient (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (horder : 1 ≤ order) (family : KernelFamily primary body order) : Primary → ℝ :=
  fun color => (family (primaryArity order horder)).val (fun _ => color) Fin.elim0



















theorem freeCertificate_norm_decay (security order : ℕ) (horder : 1 ≤ order) :
    familyNorm (primaryLaw security) (bodyReference security) order
      (primaryFactor security) (bodyFactor security) (freeCertificate security order horder) ≤
        84 / (Parameters.base security : ℝ) ^ 110 :=
  (freeCertificate_norm security order horder).trans (freeAtomEnvelope_decay security)

theorem translationCertificate_norm_decay (security order : ℕ) (horder : 1 ≤ order) (shift : ℤ) :
    familyNorm (primaryLaw security) (bodyReference security) order
      (primaryFactor security) (bodyFactor security) (translationCertificate security order horder shift) ≤
        56 / (Parameters.base security : ℝ) ^ 79 :=
  (translationCertificate_norm security order horder shift).trans (translationAtomEnvelope_decay security shift)

end

end CurrentAFT.BackgroundFamilies

end

section








/-!
# The actual leg linear certificate and cancellation of the shared queue

The queue scalar is averaged only after the complete fixed-queue linear
coefficient is formed. Its law is the same clipped Gaussian law as the leg
scalar. All coefficients below are elements of the genuine truncated family
algebra with the actual positive safe-control reference.
-/

namespace CurrentAFT.BackgroundLinear

open AFT ControlCoordinates GradedControlAlgebra GradedControlNorm
  GradedControlStability DiffuseProfiles ProposalPrimary ActualControls
  BackgroundCertificates BackgroundRates BackgroundFamilies
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
  ProposalPrimary.primaryLaw ProposalPrimary.centerLaw ActualControls.bodyReference
  BackgroundFamilies.freeCertificate BackgroundFamilies.translationCertificate
  BackgroundRates.primaryFactor BackgroundRates.bodyFactor

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def certificateNorm (security order : ℕ) (family : ActualFamily security order) : ℝ :=
  familyNorm (primaryLaw security) (bodyReference security) order
    (primaryFactor security) (bodyFactor security) family

theorem certificateNorm_nonneg (security order : ℕ) (family : ActualFamily security order) :
    0 ≤ certificateNorm security order family := by
  apply familyNorm_nonneg
  · unfold primaryFactor
    positivity
  · unfold bodyFactor radius
    positivity

theorem certificateNorm_add (security order : ℕ) (first second : ActualFamily security order) :
    certificateNorm security order (first + second) ≤
      certificateNorm security order first + certificateNorm security order second := by
  apply familyNorm_add_le
  · unfold primaryFactor
    positivity
  · unfold bodyFactor radius
    positivity

theorem certificateNorm_smul (security order : ℕ) (scalar : ℝ) (family : ActualFamily security order) :
    certificateNorm security order (scalar • family) = |scalar| * certificateNorm security order family :=
  familyNorm_smul _ _ _ _ _ _ _

theorem certificateNorm_sum_le {Index : Type*} (security order : ℕ)
    (indices : Finset Index) (families : Index → ActualFamily security order) :
    certificateNorm security order (∑ index ∈ indices, families index) ≤
      ∑ index ∈ indices, certificateNorm security order (families index) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, certificateNorm, familyNorm_zero, le_refl]
  | @insert index indices hnot ih =>
    simp only [Finset.sum_insert hnot]
    exact (certificateNorm_add security order _ _).trans (add_le_add le_rfl ih)

theorem certificateNorm_average_le {Index : Type*} [Fintype Index] (security order : ℕ)
    (law : FiniteDist Index) (families : Index → ActualFamily security order) (bound : ℝ)
    (hbound : ∀ index, certificateNorm security order (families index) ≤ bound) :
    certificateNorm security order (∑ index, law.weight index • families index) ≤ bound := by
  calc
    _ ≤ ∑ index, certificateNorm security order (law.weight index • families index) :=
      certificateNorm_sum_le security order _ _
    _ = ∑ index, law.weight index * certificateNorm security order (families index) := by
      apply Finset.sum_congr rfl
      intro index _
      rw [certificateNorm_smul, abs_of_nonneg (law.nonneg index)]
    _ ≤ ∑ index, law.weight index * bound :=
      Finset.sum_le_sum fun index _ => mul_le_mul_of_nonneg_left (hbound index) (law.nonneg index)
    _ = bound := by rw [← Finset.sum_mul, law.sum_one, one_mul]

def meanTranslation (security order : ℕ) (horder : 1 ≤ order) : ActualFamily security order :=
  ∑ scalar, (scalarLaw security).weight scalar •
    translationCertificate security order horder scalar.val

def legLinearCertificate (security order : ℕ) (horder : 1 ≤ order) : ActualFamily security order :=
  -(Parameters.legCount security : ℝ)⁻¹ •
    (freeMass security • freeCertificate security order horder +
      (Parameters.modulus security : ℝ) • meanTranslation security order horder)

def fixedQueueLinear (security order : ℕ) (horder : 1 ≤ order) (queueScalar : ℤ) :
    ActualFamily security order :=
  freeMass security • freeCertificate security order horder +
    (Parameters.modulus security : ℝ) • translationCertificate security order horder queueScalar +
    (Parameters.legCount security : ℝ) • legLinearCertificate security order horder

theorem legCount_pos (security : ℕ) : (0 : ℝ) < Parameters.legCount security := by
  rw [Parameters.legCount_eq, Nat.cast_pow]
  exact pow_pos (FirstResponse.base_pos security) _

theorem fixedQueueLinear_eq (security order : ℕ) (horder : 1 ≤ order) (queueScalar : ℤ) :
    fixedQueueLinear security order horder queueScalar =
      (Parameters.modulus security : ℝ) •
        (translationCertificate security order horder queueScalar - meanTranslation security order horder) := by
  have hl := (legCount_pos security).ne'
  unfold fixedQueueLinear legLinearCertificate
  rw [smul_smul, mul_neg, mul_inv_cancel₀ hl, neg_one_smul]
  rw [smul_sub]
  abel



theorem meanTranslation_norm (security order : ℕ) (horder : 1 ≤ order) :
    certificateNorm security order (meanTranslation security order horder) ≤
      56 / (Parameters.base security : ℝ) ^ 79 :=
  certificateNorm_average_le security order (scalarLaw security) _ _
    (fun scalar => translationCertificate_norm_decay security order horder scalar.val)

theorem legLinearCertificate_norm (security order : ℕ) (horder : 1 ≤ order) :
    certificateNorm security order (legLinearCertificate security order horder) ≤
      (freeMass security * freeAtomEnvelope security +
        (Parameters.modulus security : ℝ) * (56 / (Parameters.base security : ℝ) ^ 79)) /
          Parameters.legCount security := by
  have hl := legCount_pos security
  rw [legLinearCertificate, certificateNorm_smul,
    abs_neg, abs_inv, abs_of_pos hl]
  calc
    _ ≤ (Parameters.legCount security : ℝ)⁻¹ *
        (certificateNorm security order (freeMass security • freeCertificate security order horder) +
          certificateNorm security order ((Parameters.modulus security : ℝ) • meanTranslation security order horder)) :=
      mul_le_mul_of_nonneg_left (certificateNorm_add security order _ _) (inv_nonneg.mpr hl.le)
    _ = (Parameters.legCount security : ℝ)⁻¹ *
        (freeMass security * certificateNorm security order (freeCertificate security order horder) +
          (Parameters.modulus security : ℝ) * certificateNorm security order (meanTranslation security order horder)) := by
      rw [certificateNorm_smul, certificateNorm_smul, abs_of_nonneg (freeMass_nonneg security),
        abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ (Parameters.legCount security : ℝ)⁻¹ *
        (freeMass security * freeAtomEnvelope security +
          (Parameters.modulus security : ℝ) * (56 / (Parameters.base security : ℝ) ^ 79)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hl.le)
      exact add_le_add
        (mul_le_mul_of_nonneg_left (freeCertificate_norm security order horder) (freeMass_nonneg security))
        (mul_le_mul_of_nonneg_left (meanTranslation_norm security order horder) (Nat.cast_nonneg _))
    _ = _ := by ring

theorem bodySize_upper (security : ℕ) :
    (Parameters.bodySize security : ℝ) ≤ 131072 * (Parameters.base security : ℝ) ^ 160 := by
  have h := Nat.mul_le_mul_right (Parameters.base security ^ 96) (Parameters.modulus_bounds security).2
  exact_mod_cast (by simpa only [Parameters.bodySize_eq, mul_assoc, ← pow_add] using h)

theorem legLinearCertificate_norm_decay (security order : ℕ) (horder : 1 ≤ order) :
    certificateNorm security order (legLinearCertificate security order horder) ≤
      18350080 / (Parameters.base security : ℝ) ^ 78 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hfree : freeMass security ≤ 131072 * (Parameters.base security : ℝ) ^ 160 := by
    apply le_trans _ (bodySize_upper security)
    unfold freeMass
    have hl : (0 : ℝ) ≤ Parameters.legCount security := Nat.cast_nonneg _
    have hq : (0 : ℝ) ≤ Parameters.modulus security := Nat.cast_nonneg _
    linarith
  have hq : (Parameters.modulus security : ℝ) ≤ 131072 * (Parameters.base security : ℝ) ^ 64 := by
    exact_mod_cast (Parameters.modulus_bounds security).2
  have hp : (Parameters.base security : ℝ) ^ 78 ≤ (Parameters.base security : ℝ) ^ 143 :=
    pow_le_pow_right₀ hb1 (by omega)
  calc
    _ ≤ (freeMass security * freeAtomEnvelope security +
        (Parameters.modulus security : ℝ) * (56 / (Parameters.base security : ℝ) ^ 79)) /
          Parameters.legCount security := legLinearCertificate_norm security order horder
    _ ≤ ((131072 * (Parameters.base security : ℝ) ^ 160) *
        (84 / (Parameters.base security : ℝ) ^ 110) +
        (131072 * (Parameters.base security : ℝ) ^ 64) *
        (56 / (Parameters.base security : ℝ) ^ 79)) / Parameters.legCount security := by
      apply div_le_div_of_nonneg_right _ (legCount_pos security).le
      exact add_le_add
        (mul_le_mul hfree (freeAtomEnvelope_decay security) (freeAtomEnvelope_nonneg security) (by positivity))
        (mul_le_mul_of_nonneg_right hq (by positivity))
    _ = 11010048 / (Parameters.base security : ℝ) ^ 78 +
        7340032 / (Parameters.base security : ℝ) ^ 143 := by
      rw [Parameters.legCount_eq, Nat.cast_pow]
      field_simp
      ring
    _ ≤ 11010048 / (Parameters.base security : ℝ) ^ 78 +
        7340032 / (Parameters.base security : ℝ) ^ 78 :=
      add_le_add le_rfl (div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _) hp)
    _ = _ := by ring



end

end CurrentAFT.BackgroundLinear

end

section












/-!
# The actual fixed-scalar off-body pair mean

The same protected second scalar is fixed in both marginals. Bounds use
the full primary reference, so the marked primary atom contributes energy
one even when its uniform-reference height is large.
-/

namespace CurrentAFT.ConditionalPairMean

open AFT DiffuseProfiles ProposalPrimary ActualControls FirstResponse
  LocalReferenceEnergy BackgroundCertificates FringeCertificate
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth
  ProposalPrimary.primaryLaw ProposalPrimary.centerLaw

abbrev Palette (security : ℕ) := ActualControls.Palette security
abbrev Scalar (security : ℕ) := LocalReferenceEnergy.Scalar security

def firstMarginal {Color : Type*} [Fintype Color] (law : FiniteDist (Color × Color)) :
    FiniteDist Color where
  weight color := ∑ other, law.weight (color, other)
  nonneg color := Finset.sum_nonneg fun other _ => law.nonneg (color, other)
  sum_one := by simpa only [Fintype.sum_prod_type] using law.sum_one

def secondMarginal {Color : Type*} [Fintype Color] (law : FiniteDist (Color × Color)) :
    FiniteDist Color where
  weight color := ∑ other, law.weight (other, color)
  nonneg color := Finset.sum_nonneg fun other _ => law.nonneg (other, color)
  sum_one := by rw [Finset.sum_comm]; simpa only [Fintype.sum_prod_type] using law.sum_one

def diffuseFirst (security : ℕ) (scalar : Scalar security) : FiniteDist (Palette security) :=
  (primaryLaw security).mix fun primary => firstMarginal (diffusePairAt security primary scalar)

def diffuseSecond (security : ℕ) (scalar : Scalar security) : FiniteDist (Palette security) :=
  (primaryLaw security).mix fun primary => secondMarginal (diffusePairAt security primary scalar)

def markedSecond (security : ℕ) (scalar : Scalar security) : FiniteDist (Palette security) :=
  (primaryLaw security).mix fun primary => markedCompanionAt security primary scalar

def pairMean (security : ℕ) (scalar : Scalar security) (output : Palette security) : ℝ :=
  (1 - activation security) * ((diffuseFirst security scalar).weight output +
      (diffuseSecond security scalar).weight output) +
    activation security * ((primaryLaw security).weight output + (markedSecond security scalar).weight output)

def centeredMean (security : ℕ) (scalar : Scalar security) (output : Palette security) : ℝ :=
  pairMean security scalar output - 2 * uniformProfile security output

theorem pairMean_mass (security : ℕ) (scalar : Scalar security) :
    (∑ output, pairMean security scalar output) = 2 := by
  simp only [pairMean, Finset.sum_add_distrib, ← Finset.mul_sum, FiniteDist.sum_one]
  ring

theorem centeredMean_mass (security : ℕ) (scalar : Scalar security) :
    (∑ output, centeredMean security scalar output) = 0 := by
  have huniform : (∑ output, uniformProfile security output) = 1 := by
    simp only [uniformProfile, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [(modulus_pos security).ne']
  simp only [centeredMean, Finset.sum_sub_distrib, ← Finset.mul_sum, pairMean_mass, huniform]
  norm_num

theorem diffuseFirst_height (security : ℕ) (scalar : Scalar security) (output : Palette security) :
    (diffuseFirst security scalar).weight output ≤ 2 / (Parameters.modulus security : ℝ) := by
  simp only [diffuseFirst, FiniteDist.mix_weight, firstMarginal]
  calc
    _ ≤ ∑ primary, (primaryLaw security).weight primary * (2 / (Parameters.modulus security : ℝ)) :=
      Finset.sum_le_sum fun primary _ => mul_le_mul_of_nonneg_left
        (ReferenceMarginals.diffusePairAt_first_height security primary scalar output)
        ((primaryLaw security).nonneg primary)
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem diffuseSecond_height (security : ℕ) (scalar : Scalar security) (output : Palette security) :
    (diffuseSecond security scalar).weight output ≤ 2 / (Parameters.modulus security : ℝ) := by
  simp only [diffuseSecond, FiniteDist.mix_weight, secondMarginal]
  calc
    _ ≤ ∑ primary, (primaryLaw security).weight primary * (2 / (Parameters.modulus security : ℝ)) :=
      Finset.sum_le_sum fun primary _ => mul_le_mul_of_nonneg_left
        (ReferenceMarginals.diffusePairAt_second_height security primary scalar output)
        ((primaryLaw security).nonneg primary)
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem markedSecond_height (security : ℕ) (scalar : Scalar security) (output : Palette security) :
    (markedSecond security scalar).weight output ≤ 1 / (Parameters.anchorWidth security : ℝ) := by
  simp only [markedSecond, FiniteDist.mix_weight]
  calc
    _ ≤ ∑ primary, (primaryLaw security).weight primary * (1 / (Parameters.anchorWidth security : ℝ)) :=
      Finset.sum_le_sum fun primary _ => mul_le_mul_of_nonneg_left
        (markedCompanionAt_height security primary scalar output)
        ((primaryLaw security).nonneg primary)
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem height_profile_energy (security : ℕ) (law : FiniteDist (Palette security))
    (height : ℝ) (hheight : 0 ≤ height) (hbound : ∀ color, law.weight color ≤ height) :
    profileSquareNorm (primaryLaw security).weight law.weight ≤
      2 * (Parameters.modulus security : ℝ) * height := by
  have hdom (color : Palette security) : law.weight color ≤
      (2 * (Parameters.modulus security : ℝ) * height) * (primaryLaw security).weight color := by
    have hlower : 1 / (2 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight color := by
      simpa only [primaryLaw] using primaryProfile_atom_lower security color
    have hscale := mul_le_mul_of_nonneg_left hlower
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (modulus_pos security).le) hheight)
    have hequal : (2 * (Parameters.modulus security : ℝ) * height) *
        (1 / (2 * (Parameters.modulus security : ℝ))) = height := by
      field_simp [(modulus_pos security).ne']
    rw [hequal] at hscale
    exact (hbound color).trans hscale
  simpa only [FiniteDist.sum_one, mul_one] using dominated_profile_square_le security
    (primaryLaw security).weight law.weight (2 * (Parameters.modulus security : ℝ) * height)
    (by positivity) (primaryLaw security).nonneg law.nonneg hdom

theorem primary_profile_energy (security : ℕ) :
    profileSquareNorm (primaryLaw security).weight (primaryLaw security).weight = 1 := by
  unfold profileSquareNorm
  simp only [sq, mul_div_cancel_right₀ _ (primaryReference_positive security _).ne']
  exact (primaryLaw security).sum_one

 theorem five_profile_square (activation first second primary companion uniform : ℝ)
    (hactivation : 0 ≤ activation) (hactivation' : activation ≤ 1) :
    ((1 - activation) * (first + second) + activation * (primary + companion) - 2 * uniform) ^ 2 ≤
      8 * (first ^ 2 + second ^ 2 + primary ^ 2 + companion ^ 2 + uniform ^ 2) := by
  have hfirst : ((1 - activation) * first) ^ 2 ≤ first ^ 2 := by
    nlinarith [sq_nonneg first, mul_nonneg (sq_nonneg first) (mul_nonneg hactivation (sub_nonneg.mpr hactivation'))]
  have hsecond : ((1 - activation) * second) ^ 2 ≤ second ^ 2 := by
    nlinarith [sq_nonneg second, mul_nonneg (sq_nonneg second) (mul_nonneg hactivation (sub_nonneg.mpr hactivation'))]
  have hprimary : (activation * primary) ^ 2 ≤ primary ^ 2 := by
    nlinarith [sq_nonneg primary, mul_nonneg (sq_nonneg primary) (mul_nonneg hactivation (sub_nonneg.mpr hactivation'))]
  have hcompanion : (activation * companion) ^ 2 ≤ companion ^ 2 := by
    nlinarith [sq_nonneg companion, mul_nonneg (sq_nonneg companion) (mul_nonneg hactivation (sub_nonneg.mpr hactivation'))]
  nlinarith [sq_nonneg ((1 - activation) * (first - second)),
    sq_nonneg (activation * (primary - companion)),
    sq_nonneg ((1 - activation) * (first + second) - activation * (primary + companion)),
    sq_nonneg ((1 - activation) * (first + second) + activation * (primary + companion) + 2 * uniform)]

theorem centeredMean_energy (security : ℕ) (scalar : Scalar security) :
    profileSquareNorm (primaryLaw security).weight (centeredMean security scalar) ≤
      88 + 16 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security := by
  have hfirst := height_profile_energy security (diffuseFirst security scalar)
    (2 / (Parameters.modulus security : ℝ)) (by positivity) (diffuseFirst_height security scalar)
  have hsecond := height_profile_energy security (diffuseSecond security scalar)
    (2 / (Parameters.modulus security : ℝ)) (by positivity) (diffuseSecond_height security scalar)
  have hmarked := height_profile_energy security (markedSecond security scalar)
    (1 / (Parameters.anchorWidth security : ℝ)) (by positivity) (markedSecond_height security scalar)
  have huniform := FringeCertificate.uniformProfile_square_le_two security
  have hpoint (color : Palette security) := div_le_div_of_nonneg_right
    (five_profile_square (activation security) ((diffuseFirst security scalar).weight color)
      ((diffuseSecond security scalar).weight color) ((primaryLaw security).weight color)
      ((markedSecond security scalar).weight color) (uniformProfile security color)
      (activation_pos security).le (by linarith [activation_le_half security]))
    ((primaryLaw security).nonneg color)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun color _ => hpoint color)
  have hexpand : ∀ a b c d e denominator : ℝ,
      8 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) / denominator =
      8 * (a ^ 2 / denominator + b ^ 2 / denominator + c ^ 2 / denominator +
        d ^ 2 / denominator + e ^ 2 / denominator) := by intros; ring
  simp only [hexpand, ← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  change profileSquareNorm (primaryLaw security).weight (centeredMean security scalar) ≤
    8 * (profileSquareNorm (primaryLaw security).weight (diffuseFirst security scalar).weight +
      profileSquareNorm (primaryLaw security).weight (diffuseSecond security scalar).weight +
      profileSquareNorm (primaryLaw security).weight (primaryLaw security).weight +
      profileSquareNorm (primaryLaw security).weight (markedSecond security scalar).weight +
      profileSquareNorm (primaryLaw security).weight (uniformProfile security)) at hsum
  rw [primary_profile_energy] at hsum
  have hq := (modulus_pos security).ne'
  have hcancel : 2 * (Parameters.modulus security : ℝ) * (2 / Parameters.modulus security) = 4 := by
    field_simp
    ring
  rw [hcancel] at hfirst hsecond
  simp only [div_eq_mul_inv] at hmarked ⊢
  nlinarith







end

end CurrentAFT.ConditionalPairMean

end

section












/-!
# The actual first inverse on a joint two-primary profile

Each inverse is applied to complete fibers of the joint profile. The
energy proof integrates the actual scalar bound under the other reference
coordinate and introduces no maximum-atom or inverse-root-atom factor.
-/

namespace CurrentAFT.PrimaryPairInverse

open AFT DiffuseProfiles ProposalPrimary ActualControls FirstResponse
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw FirstResponse.responseEquiv

abbrev Palette (security : ℕ) := ActualControls.Palette security



















theorem inverse_square_le (security : ℕ) (profile : Palette security → ℝ) :
    profileSquareNorm (primaryLaw security).weight ((responseEquiv security).symm profile) ≤
      4 * profileSquareNorm (primaryLaw security).weight profile := by
  have h := response_inverse_norm_le_two security (primaryLaw security).weight
    (by simpa only [primaryLaw] using primaryProfile_atom_lower security) (primaryLaw security).sum_one profile
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  simpa only [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num,
    Real.sq_sqrt (profileSquareNorm_nonneg _ _ (fun color => (primaryLaw security).nonneg color))] using hs





























end

end CurrentAFT.PrimaryPairInverse

end

section












/-!
# Actual normalized primary inverse on arbitrary joint finite tensors

The local channel is the constructed first inverse conjugated by the actual
positive primary reference. Tensorization acts on the full joint array.
-/

namespace CurrentAFT.PrimaryTensorInverse

open AFT DiffuseProfiles ProposalPrimary ActualControls FirstResponse PrimaryPairInverse
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw FirstResponse.responseEquiv

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def diagonal {Color : Type*} (weight : Color → ℝ) : (Color → ℝ) →ₗ[ℝ] (Color → ℝ) where
  toFun kernel := fun color => weight color * kernel color
  map_add' first second := by funext color; simp only [Pi.add_apply]; ring
  map_smul' scalar kernel := by funext color; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def densityInverse (security : ℕ) : (ActualControls.Palette security → ℝ) →ₗ[ℝ] (ActualControls.Palette security → ℝ) :=
  (diagonal (fun color => ((primaryLaw security).weight color)⁻¹)).comp
    (((activation security)⁻¹ • (responseEquiv security).symm.toLinearMap).comp
      (diagonal (primaryLaw security).weight))

def densityResponse (security : ℕ) : (ActualControls.Palette security → ℝ) →ₗ[ℝ] (ActualControls.Palette security → ℝ) :=
  (diagonal (fun color => ((primaryLaw security).weight color)⁻¹)).comp
    ((activation security • response security).comp (diagonal (primaryLaw security).weight))

theorem densityInverse_apply (security : ℕ) (kernel : ActualControls.Palette security → ℝ)
    (output : ActualControls.Palette security) :
    densityInverse security kernel output =
      (activation security)⁻¹ * (responseEquiv security).symm
        (fun input => (primaryLaw security).weight input * kernel input) output /
        (primaryLaw security).weight output := by
  simp only [densityInverse, LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
    diagonal, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul]
  ring

theorem densityResponse_apply (security : ℕ) (kernel : ActualControls.Palette security → ℝ)
    (output : ActualControls.Palette security) :
    densityResponse security kernel output =
      activation security * response security
        (fun input => (primaryLaw security).weight input * kernel input) output /
        (primaryLaw security).weight output := by
  simp only [densityResponse, LinearMap.comp_apply, LinearMap.smul_apply,
    diagonal, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul]
  ring



theorem densityInverse_mean (security : ℕ) (kernel : ActualControls.Palette security → ℝ) :
    (primaryLaw security).expectation (densityInverse security kernel) =
      (activation security)⁻¹ * (primaryLaw security).expectation kernel := by
  have hpoint (color : ActualControls.Palette security) :
      (primaryLaw security).weight color * densityInverse security kernel color =
        (activation security)⁻¹ * (responseEquiv security).symm
          (fun input => (primaryLaw security).weight input * kernel input) color := by
    rw [densityInverse_apply]
    field_simp [(primaryReference_positive security color).ne']
  simp only [FiniteDist.expectation, hpoint, ← Finset.mul_sum, response_inverse_preserves_mass]

theorem densityInverse_energy (security : ℕ) (kernel : ActualControls.Palette security → ℝ) :
    (primaryLaw security).l2Sq (densityInverse security kernel) ≤
      (2 / activation security) ^ 2 * (primaryLaw security).l2Sq kernel := by
  have hpoint (color : ActualControls.Palette security) :
      (primaryLaw security).weight color * densityInverse security kernel color ^ 2 =
        (activation security)⁻¹ ^ 2 *
          ((responseEquiv security).symm (fun input => (primaryLaw security).weight input * kernel input) color ^ 2 /
            (primaryLaw security).weight color) := by
    rw [densityInverse_apply]
    field_simp [(primaryReference_positive security color).ne']
  have hinput : profileSquareNorm (primaryLaw security).weight
      (fun input => (primaryLaw security).weight input * kernel input) = (primaryLaw security).l2Sq kernel := by
    unfold profileSquareNorm FiniteDist.l2Sq FiniteDist.expectation
    apply Finset.sum_congr rfl
    intro color _
    field_simp [(primaryReference_positive security color).ne']
  change (∑ color, (primaryLaw security).weight color * densityInverse security kernel color ^ 2) ≤ _
  simp only [hpoint, ← Finset.mul_sum]
  calc
    _ ≤ (activation security)⁻¹ ^ 2 * (4 * profileSquareNorm (primaryLaw security).weight
        (fun input => (primaryLaw security).weight input * kernel input)) :=
      mul_le_mul_of_nonneg_left (inverse_square_le security _) (sq_nonneg _)
    _ = _ := by rw [hinput]; ring

section Composition

variable {Input Middle Output : Type*} [Fintype Input] [Fintype Middle] [Fintype Output]





end Composition

def tensorInverse (security degree : ℕ) :=
  TensorChannel.applyLinear degree (fun _ => densityInverse security)

def tensorResponse (security degree : ℕ) :=
  TensorChannel.applyLinear degree (fun _ => densityResponse security)



theorem tensor_energy_any {Input Output : Type*} [Fintype Input] [Fintype Output]
    (degree : ℕ) [decision : DecidableEq (Fin degree)]
    (input : Fin degree → FiniteDist Input) (output : Fin degree → FiniteDist Output)
    (channel : Fin degree → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (bound : Fin degree → ℝ)
    (hchannel : ∀ index kernel, (output index).l2Sq (channel index kernel) ≤
      bound index ^ 2 * (input index).l2Sq kernel)
    (kernel : (Fin degree → Input) → ℝ) :
    (FiniteDist.independent output).l2Sq (TensorChannel.apply degree channel kernel) ≤
      (∏ index, bound index ^ 2) * (FiniteDist.independent input).l2Sq kernel := by
  cases Subsingleton.elim decision (instDecidableEqFin degree)
  exact TensorChannel.energy_le degree input output channel bound hchannel kernel

theorem tensorInverse_energy (security degree : ℕ) (kernel : (Fin degree → ActualControls.Palette security) → ℝ) :
    (FiniteDist.independent (fun _ : Fin degree => primaryLaw security)).l2Sq
      (tensorInverse security degree kernel) ≤
      ((2 / activation security) ^ degree) ^ 2 *
        (FiniteDist.independent (fun _ : Fin degree => primaryLaw security)).l2Sq kernel := by
  have h := tensor_energy_any degree (fun _ => primaryLaw security) (fun _ => primaryLaw security)
    (fun _ => densityInverse security) (fun _ => 2 / activation security)
    (fun _ => densityInverse_energy security) kernel
  change (FiniteDist.independent (fun _ : Fin degree => primaryLaw security)).l2Sq
    (TensorChannel.apply degree (fun _ => densityInverse security) kernel) ≤ _
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, Nat.mul_comm] using h

def MassCentered {Color : Type*} [Fintype Color] (degree : ℕ)
    (profile : (Fin degree → Color) → ℝ) : Prop :=
  ∀ index word, ∑ color, profile (Function.update word index color) = 0

def referenceWeight (security degree : ℕ) (word : Fin degree → ActualControls.Palette security) : ℝ :=
  ∏ index, (primaryLaw security).weight (word index)

theorem referenceWeight_pos (security degree : ℕ) (word : Fin degree → ActualControls.Palette security) :
    0 < referenceWeight security degree word :=
  Finset.prod_pos fun index _ => primaryReference_positive security (word index)

def massDensity (security degree : ℕ) (profile : (Fin degree → ActualControls.Palette security) → ℝ) :
    (Fin degree → ActualControls.Palette security) → ℝ :=
  fun word => profile word / referenceWeight security degree word

def massLift (security degree : ℕ) (profile : (Fin degree → ActualControls.Palette security) → ℝ) :
    (Fin degree → ActualControls.Palette security) → ℝ :=
  tensorInverse security degree (massDensity security degree profile)

def massLeading (security degree : ℕ) (density : (Fin degree → ActualControls.Palette security) → ℝ) :
    (Fin degree → ActualControls.Palette security) → ℝ :=
  fun word => referenceWeight security degree word * tensorResponse security degree density word



def massEnergy (security degree : ℕ) (profile : (Fin degree → ActualControls.Palette security) → ℝ) : ℝ :=
  ∑ word, profile word ^ 2 / referenceWeight security degree word

theorem massDensity_energy (security degree : ℕ) (profile : (Fin degree → ActualControls.Palette security) → ℝ) :
    (FiniteDist.independent (fun _ : Fin degree => primaryLaw security)).l2Sq
      (massDensity security degree profile) = massEnergy security degree profile := by
  unfold FiniteDist.l2Sq FiniteDist.expectation
  apply Finset.sum_congr rfl
  intro word _
  change referenceWeight security degree word * (profile word / referenceWeight security degree word) ^ 2 = _
  field_simp [(referenceWeight_pos security degree word).ne']

theorem massLift_energy (security degree : ℕ) (profile : (Fin degree → ActualControls.Palette security) → ℝ) :
    (FiniteDist.independent (fun _ : Fin degree => primaryLaw security)).l2Sq
      (massLift security degree profile) ≤
        ((2 / activation security) ^ degree) ^ 2 * massEnergy security degree profile := by
  exact (tensorInverse_energy security degree (massDensity security degree profile)).trans_eq
    (congrArg (fun value => ((2 / activation security) ^ degree) ^ 2 * value)
      (massDensity_energy security degree profile))

theorem massLift_norm (security degree : ℕ) (profile : (Fin degree → ActualControls.Palette security) → ℝ) :
    Real.sqrt ((FiniteDist.independent (fun _ : Fin degree => primaryLaw security)).l2Sq
      (massLift security degree profile)) ≤
        (2 / activation security) ^ degree * Real.sqrt (massEnergy security degree profile) := by
  have henergy : 0 ≤ massEnergy security degree profile := by
    apply Finset.sum_nonneg
    intro word _
    exact div_nonneg (sq_nonneg _) (referenceWeight_pos security degree word).le
  have ha := activation_pos security
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt henergy]
  exact massLift_energy security degree profile

theorem massDensity_canonical (security degree : ℕ) (profile : (Fin degree → ActualControls.Palette security) → ℝ)
    (hcentered : MassCentered degree profile) :
    Hoeffding.Canonical (fun _ : Fin degree => primaryLaw security) Finset.univ (massDensity security degree profile) := by
  constructor
  · intro first second hequal
    have hword : first = second := funext fun index => hequal index (Finset.mem_univ index)
    rw [hword]
  · intro index _ word
    let remaining := ∏ other ∈ Finset.univ.erase index, (primaryLaw security).weight (word other)
    have hremaining : remaining ≠ 0 := by
      apply ne_of_gt
      exact Finset.prod_pos fun other _ => primaryReference_positive security (word other)
    have hweight (color : ActualControls.Palette security) :
        referenceWeight security degree (Function.update word index color) =
          (primaryLaw security).weight color * remaining := by
      unfold referenceWeight
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ index), Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro other hother
      rw [Function.update_of_ne (Finset.mem_erase.mp hother).1]
    have hpoint (color : ActualControls.Palette security) :
        (primaryLaw security).weight color * massDensity security degree profile (Function.update word index color) =
          profile (Function.update word index color) / remaining := by
      rw [massDensity, hweight]
      field_simp [(primaryReference_positive security color).ne', hremaining]
    change (∑ color, (primaryLaw security).weight color *
      massDensity security degree profile (Function.update word index color)) = 0
    simp only [hpoint, ← Finset.sum_div, hcentered index word, zero_div]

theorem tensorInverse_canonical (security degree : ℕ) (kernel : (Fin degree → ActualControls.Palette security) → ℝ)
    (hcanonical : Hoeffding.Canonical (fun _ : Fin degree => primaryLaw security) Finset.univ kernel) :
    Hoeffding.Canonical (fun _ : Fin degree => primaryLaw security) Finset.univ (tensorInverse security degree kernel) := by
  let matrix : Fin degree → ActualControls.Palette security → ActualControls.Palette security → ℝ :=
    fun _ input output => densityInverse security (Pi.single input 1) output
  have hmean (index : Fin degree) (point : ActualControls.Palette security) :
      (primaryLaw security).expectation (matrix index point) =
        (activation security)⁻¹ * (primaryLaw security).weight point := by
    rw [show matrix index point = densityInverse security (Pi.single point 1) from rfl, densityInverse_mean]
    simp only [FiniteDist.expectation, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h := MixedKernel.matrixApply_canonical (fun _ : Fin degree => primaryLaw security)
    (fun _ : Fin degree => primaryLaw security) matrix (fun _ => (activation security)⁻¹) hmean kernel hcanonical
  have heq : MixedKernel.matrixApply matrix kernel = tensorInverse security degree kernel := by
    funext output
    exact (TensorChannel.apply_formula_instance degree (fun _ => densityInverse security) kernel output).symm
  rw [heq] at h
  exact h

theorem massLift_canonical (security degree : ℕ) (profile : (Fin degree → ActualControls.Palette security) → ℝ)
    (hcentered : MassCentered degree profile) :
    Hoeffding.Canonical (fun _ : Fin degree => primaryLaw security) Finset.univ (massLift security degree profile) :=
  tensorInverse_canonical security degree _ (massDensity_canonical security degree profile hcentered)

section Permutations

variable {Input Output : Type*} [Fintype Input] [Fintype Output]

def wordPermutation (degree : ℕ) (permutation : Equiv.Perm (Fin degree)) :
    (Fin degree → Input) ≃ (Fin degree → Input) where
  toFun word := word ∘ permutation
  invFun word := word ∘ permutation.symm
  left_inv word := by funext index; simp only [Function.comp_apply, Equiv.apply_symm_apply]
  right_inv word := by funext index; simp only [Function.comp_apply, Equiv.symm_apply_apply]

omit [Fintype Output] in
theorem tensor_apply_symmetric (degree : ℕ) (channel : (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (kernel : (Fin degree → Input) → ℝ)
    (hsymmetric : ∀ (permutation : Equiv.Perm (Fin degree)) word, kernel (word ∘ permutation) = kernel word)
    (permutation : Equiv.Perm (Fin degree)) (output : Fin degree → Output) :
    TensorChannel.apply degree (fun _ => channel) kernel (output ∘ permutation) =
      TensorChannel.apply degree (fun _ => channel) kernel output := by
  rw [TensorChannel.apply_formula_instance, TensorChannel.apply_formula_instance]
  rw [← (wordPermutation (Input := Input) degree permutation).sum_comp]
  apply Finset.sum_congr rfl
  intro input _
  change kernel (input ∘ permutation) *
    (∏ index, channel (Pi.single (input (permutation index)) 1) (output (permutation index))) = _
  rw [hsymmetric permutation input]
  congr 1
  exact Equiv.prod_comp permutation (fun index => channel (Pi.single (input index) 1) (output index))

end Permutations

theorem massLift_symmetric (security degree : ℕ) (profile : (Fin degree → ActualControls.Palette security) → ℝ)
    (hsymmetric : ∀ (permutation : Equiv.Perm (Fin degree)) word, profile (word ∘ permutation) = profile word)
    (permutation : Equiv.Perm (Fin degree)) (word : Fin degree → ActualControls.Palette security) :
    massLift security degree profile (word ∘ permutation) = massLift security degree profile word := by
  have hinput : ∀ (order : Equiv.Perm (Fin degree)) word,
      massDensity security degree profile (word ∘ order) = massDensity security degree profile word := by
    intro order word
    rw [massDensity, massDensity, hsymmetric]
    congr 1
    exact Equiv.prod_comp order (fun index => (primaryLaw security).weight (word index))
  exact tensor_apply_symmetric degree (densityInverse security) _ hinput permutation word

end

end CurrentAFT.PrimaryTensorInverse

end

section










/-! Actual canonical family coefficients obtained from the primary tensor inverse. -/

namespace CurrentAFT.PrimaryMassFamilies

open AFT ControlCoordinates ControlNorm GradedControlAlgebra GradedControlNorm
  DiffuseProfiles ProposalPrimary ActualControls PrimaryTensorInverse BackgroundFamilies
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
  PrimaryTensorInverse.massLift

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def oneWordProfile {Color : Type*} (profile : Color → ℝ) (word : Fin 1 → Color) : ℝ := profile (word 0)

theorem oneWordProfile_centered {Color : Type*} [Fintype Color] (profile : Color → ℝ)
    (hzero : ∑ color, profile color = 0) : MassCentered 1 (oneWordProfile profile) := by
  intro index word
  have hi : index = 0 := Subsingleton.elim _ _
  subst index
  simpa only [oneWordProfile, Function.update_self] using hzero

theorem oneWordProfile_symmetric {Color : Type*} (profile : Color → ℝ)
    (permutation : Equiv.Perm (Fin 1)) (word : Fin 1 → Color) :
    oneWordProfile profile (word ∘ permutation) = oneWordProfile profile word := by
  have hi : permutation 0 = 0 := Subsingleton.elim _ _
  simp only [oneWordProfile, Function.comp_apply, hi]

theorem oneWordProfile_energy {Color : Type*} [Fintype Color] (reference : Color → ℝ) (profile : Color → ℝ) :
    (∑ word : Fin 1 → Color, oneWordProfile profile word ^ 2 /
      (∏ index, reference (word index))) = profileSquareNorm reference profile := by
  simp only [oneWordProfile, Fin.prod_univ_one]
  exact ((Equiv.funUnique (Fin 1) Color).symm.sum_comp (fun word : Fin 1 → Color =>
    profile (word 0) ^ 2 / reference (word 0))).symm

def pairWordProfile {Color : Type*} (profile : Color → Color → ℝ) (word : Fin 2 → Color) : ℝ :=
  profile (word 0) (word 1)

theorem pairWordProfile_symmetric {Color : Type*} (profile : Color → Color → ℝ)
    (hsymmetric : ∀ first second, profile first second = profile second first)
    (permutation : Equiv.Perm (Fin 2)) (word : Fin 2 → Color) :
    pairWordProfile profile (word ∘ permutation) = pairWordProfile profile word := by
  have hne : (permutation 0).val ≠ (permutation 1).val := by
    intro hequal
    have h := permutation.injective (Fin.ext hequal)
    have hv := congrArg Fin.val h
    norm_num at hv
  have hzero := (permutation 0).isLt
  have hone := (permutation 1).isLt
  have hcases : ((permutation 0).val = 0 ∧ (permutation 1).val = 1) ∨
      ((permutation 0).val = 1 ∧ (permutation 1).val = 0) := by omega
  rcases hcases with hcases | hcases
  · have h0 : permutation 0 = 0 := Fin.ext hcases.1
    have h1 : permutation 1 = 1 := Fin.ext hcases.2
    simp only [pairWordProfile, Function.comp_apply, h0, h1]
  · have h0 : permutation 0 = 1 := Fin.ext hcases.1
    have h1 : permutation 1 = 0 := Fin.ext hcases.2
    simpa only [pairWordProfile, Function.comp_apply, h0, h1] using hsymmetric (word 1) (word 0)

theorem pairWordProfile_energy {Color : Type*} [Fintype Color] (reference : Color → ℝ)
    (profile : Color → Color → ℝ) :
    (∑ word : Fin 2 → Color, pairWordProfile profile word ^ 2 /
      (∏ index, reference (word index))) = BlockDensity.pairEnergy reference reference profile := by
  rw [← (finTwoArrowEquiv Color).symm.sum_comp]
  simp only [Fintype.sum_prod_type, pairWordProfile, Fin.prod_univ_two, finTwoArrowEquiv,
    Equiv.coe_fn_symm_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    BlockDensity.pairEnergy]

def massLiftKernel (security degree : ℕ)
    (profile : (Fin degree → ActualControls.Palette security) → ℝ)
    (hcentered : MassCentered degree profile)
    (hsymmetric : ∀ (permutation : Equiv.Perm (Fin degree)) word, profile (word ∘ permutation) = profile word) :
    canonicalKernels (primaryLaw security) (bodyReference security) degree 0 := by
  refine ⟨fun colors _ => massLift security degree profile colors, ?_, ?_, ?_⟩
  · intro index colors centers
    exact (massLift_canonical security degree profile hcentered).2 index (Finset.mem_univ index) colors
  · intro index
    exact Fin.elim0 index
  · intro primaryOrder bodyOrder colors centers
    exact massLift_symmetric security degree profile hsymmetric primaryOrder colors

theorem massLiftKernel_blockL2 (security degree : ℕ)
    (profile : (Fin degree → ActualControls.Palette security) → ℝ)
    (hcentered : MassCentered degree profile)
    (hsymmetric : ∀ (permutation : Equiv.Perm (Fin degree)) word, profile (word ∘ permutation) = profile word) :
    blockL2 (primaryLaw security) (bodyReference security) (massLiftKernel security degree profile hcentered hsymmetric).val =
      Real.sqrt ((FiniteDist.independent (fun _ : Fin degree => primaryLaw security)).l2Sq
        (massLift security degree profile)) := by
  unfold blockL2
  congr 1
  rw [blockEnergy_apply]
  simp only [massLiftKernel, Fin.prod_univ_zero, mul_one, Finset.univ_unique, Finset.sum_singleton]
  rfl

def primaryArity (order degree : ℕ) (hdegree : degree ≤ order) : TruncatedArity order :=
  ⟨(⟨degree, by omega⟩, 0), by simpa⟩

def massCertificateFamily (security order degree : ℕ) (hdegree : degree ≤ order)
    (profile : (Fin degree → ActualControls.Palette security) → ℝ)
    (hcentered : MassCentered degree profile)
    (hsymmetric : ∀ (permutation : Equiv.Perm (Fin degree)) word, profile (word ∘ permutation) = profile word) :
    ActualFamily security order :=
  Pi.single (primaryArity order degree hdegree) (massLiftKernel security degree profile hcentered hsymmetric)

theorem massCertificateFamily_norm (security order degree : ℕ) (hdegree : degree ≤ order)
    (primaryFactor bodyFactor : ℝ) (hfactor : 0 ≤ primaryFactor)
    (profile : (Fin degree → ActualControls.Palette security) → ℝ)
    (hcentered : MassCentered degree profile)
    (hsymmetric : ∀ (permutation : Equiv.Perm (Fin degree)) word, profile (word ∘ permutation) = profile word) :
    familyNorm (primaryLaw security) (bodyReference security) order primaryFactor bodyFactor
      (massCertificateFamily security order degree hdegree profile hcentered hsymmetric) ≤
        primaryFactor ^ degree * (2 / activation security) ^ degree * Real.sqrt (massEnergy security degree profile) := by
  rw [massCertificateFamily, familyNorm_single, massLiftKernel_blockL2]
  have hnorm := mul_le_mul_of_nonneg_left (massLift_norm security degree profile) (pow_nonneg hfactor degree)
  simpa only [primaryArity, gradeWeight, Fin.val_zero, pow_zero, mul_one, mul_assoc] using hnorm





end

end CurrentAFT.PrimaryMassFamilies

end

section












/-!
# Actual conditional pair-linear coefficients and their population budget

The coefficient is obtained by the actual primary tensor inverse from the
fixed-scalar mean. The scalar is retained through the later multiplication
with the attachment factor.
-/

namespace CurrentAFT.ConditionalPairLinear

open AFT DiffuseProfiles ProposalPrimary ActualControls FirstResponse
  ConditionalPairMean PrimaryTensorInverse PrimaryMassFamilies BackgroundFamilies BackgroundRates BackgroundLinear
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth ProposalPrimary.primaryLaw
  ProposalPrimary.centerLaw ActualControls.bodyReference

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def wordMean (security : ℕ) (scalar : ConditionalPairMean.Scalar security)
    (word : Fin 1 → ActualControls.Palette security) : ℝ := centeredMean security scalar (word 0)

theorem wordMean_centered (security : ℕ) (scalar : ConditionalPairMean.Scalar security) :
    MassCentered 1 (wordMean security scalar) := by
  intro index word
  have hindex : index = 0 := Subsingleton.elim _ _
  subst index
  simpa only [wordMean, Function.update_self] using centeredMean_mass security scalar

theorem wordMean_symmetric (security : ℕ) (scalar : ConditionalPairMean.Scalar security)
    (permutation : Equiv.Perm (Fin 1)) (word : Fin 1 → ActualControls.Palette security) :
    wordMean security scalar (word ∘ permutation) = wordMean security scalar word := by
  have hindex : permutation 0 = 0 := Subsingleton.elim _ _
  simp only [wordMean, Function.comp_apply, hindex]

def certificate (security order : ℕ) (horder : 1 ≤ order)
    (scalar : ConditionalPairMean.Scalar security) : ActualFamily security order :=
  massCertificateFamily security order 1 horder (wordMean security scalar)
    (wordMean_centered security scalar) (wordMean_symmetric security scalar)

 theorem oneWord_energy {Color : Type*} [Fintype Color]
    (reference profile : Color → ℝ) :
    (∑ word : Fin 1 → Color, profile (word 0) ^ 2 / (∏ index, reference (word index))) =
      profileSquareNorm reference profile := by
  rw [← (Equiv.funUnique (Fin 1) Color).symm.sum_comp]
  simp only [Equiv.funUnique_symm_apply, uniqueElim_const, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, pow_one, profileSquareNorm]

theorem wordMean_energy (security : ℕ) (scalar : ConditionalPairMean.Scalar security) :
    massEnergy security 1 (wordMean security scalar) =
      profileSquareNorm (primaryLaw security).weight (centeredMean security scalar) := by
  exact oneWord_energy (primaryLaw security).weight (centeredMean security scalar)

theorem modulus_anchor_ratio (security : ℕ) :
    (Parameters.modulus security : ℝ) / Parameters.anchorWidth security ≤
      131072 * (Parameters.base security : ℝ) ^ 16 := by
  have hq : (Parameters.modulus security : ℝ) ≤ 131072 * (Parameters.base security : ℝ) ^ 64 := by
    exact_mod_cast (Parameters.modulus_bounds security).2
  have hanchor : (Parameters.anchorWidth security : ℝ) = (Parameters.base security : ℝ) ^ 48 := by
    simp only [Parameters.anchorWidth, Parameters.scale, ← pow_mul, Nat.cast_pow]
  rw [hanchor]
  apply (div_le_iff₀ (pow_pos (base_pos security) _)).mpr
  simpa only [mul_assoc, ← pow_add] using hq

theorem wordMean_norm (security : ℕ) (scalar : ConditionalPairMean.Scalar security) :
    Real.sqrt (massEnergy security 1 (wordMean security scalar)) ≤
      4096 * (Parameters.base security : ℝ) ^ 8 := by
  rw [wordMean_energy]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have h := centeredMean_energy security scalar
  have hratio := modulus_anchor_ratio security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hpower : (1 : ℝ) ≤ (Parameters.base security : ℝ) ^ 16 := one_le_pow₀ hb1
  have hidentity : (4096 * (Parameters.base security : ℝ) ^ 8) ^ 2 =
      16777216 * (Parameters.base security : ℝ) ^ 16 := by ring
  rw [hidentity]
  simp only [div_eq_mul_inv, mul_assoc] at h hratio
  nlinarith

theorem certificate_norm (security order : ℕ) (horder : 1 ≤ order)
    (scalar : ConditionalPairMean.Scalar security) :
    certificateNorm security order (certificate security order horder scalar) ≤
      32768 / (Parameters.base security : ℝ) ^ 55 := by
  have hfactor : 0 ≤ primaryFactor security := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have h := massCertificateFamily_norm security order 1 horder
    (primaryFactor security) (bodyFactor security) hfactor (wordMean security scalar)
    (wordMean_centered security scalar) (wordMean_symmetric security scalar)
  change certificateNorm security order (certificate security order horder scalar) ≤ _ at h
  simp only [pow_one] at h
  have hinverse : 2 / activation security ≤ 8 * (Parameters.base security : ℝ) := by
    have hh := activation_inverse_le security
    simp only [div_eq_mul_inv, one_mul] at hh ⊢
    nlinarith
  calc
    _ ≤ primaryFactor security * (2 / activation security) *
        Real.sqrt (massEnergy security 1 (wordMean security scalar)) := h
    _ ≤ primaryFactor security * (8 * (Parameters.base security : ℝ)) *
        (4096 * (Parameters.base security : ℝ) ^ 8) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hinverse hfactor) (wordMean_norm security scalar)
        (Real.sqrt_nonneg _) (mul_nonneg hfactor (by positivity))
    _ = _ := by
      rw [primaryFactor_eq]
      field_simp [(base_pos security).ne']
      ring





end

end CurrentAFT.ConditionalPairLinear

end

section












/-!
# Full smoothing cost of the true trimmed integer-window pair

The cyclic comparison retains the original varying slice denominator and
both endpoint masks. A no-wrap argument is proved for an arbitrary modulus,
then the complete integer translation estimate is averaged under any actual
finite protected-root law. No old parameter family is used.
-/

namespace CurrentAFT.PairSmoothing

open AFT AFT.TrimmedSlice AFT.SafeConvolution
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem finEquiv_symm_val (modulus : ℕ) [NeZero modulus] (color : ZMod modulus) :
    ((ZMod.finEquiv modulus).symm color).val = color.val := by
  cases modulus with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ modulus => rfl

theorem sub_val_on_core (modulus : ℕ) [NeZero modulus] (core shift : ℤ)
    (color : ZMod modulus) (hshift : |shift| ≤ core)
    (hl : core ≤ ((color - (shift : ZMod modulus)).val : ℤ))
    (hu : ((color - (shift : ZMod modulus)).val : ℤ) < (modulus : ℤ) - core) :
    ((color - (shift : ZMod modulus)).val : ℤ) = color.val - shift := by
  let input := color - (shift : ZMod modulus)
  have hlo : 0 ≤ (input.val : ℤ) + shift := by
    dsimp only [input]
    have hh := abs_le.mp hshift
    omega
  have hhi : (input.val : ℤ) + shift < modulus := by
    dsimp only [input]
    have hh := abs_le.mp hshift
    omega
  have heq : (((input.val : ℤ) + shift : ℤ) : ZMod modulus) = color := by
    rw [Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val]
    dsimp only [input]
    abel
  have hv : (((((input.val : ℤ) + shift : ℤ) : ZMod modulus)).val : ℤ) = input.val + shift := by
    rw [ZMod.val_intCast, Int.emod_eq_of_lt hlo hhi]
  rw [heq] at hv
  dsimp only [input] at hv
  omega

theorem core_profile_translation (modulus : ℕ) [NeZero modulus] (core : ℤ) (hcore : 0 ≤ core)
    (profile : ℤ → ℤ → ℝ)
    (hsupport : ∀ first second, profile first second ≠ 0 →
      (core ≤ first ∧ first < (modulus : ℤ) - core) ∧
      (core ≤ second ∧ second < (modulus : ℤ) - core))
    (firstShift secondShift : ℤ) (hfirst : |firstShift| ≤ core) (hsecond : |secondShift| ≤ core)
    (first second : ZMod modulus) :
    profile ((first - (firstShift : ZMod modulus)).val : ℤ)
        ((second - (secondShift : ZMod modulus)).val : ℤ) =
      profile ((first.val : ℤ) - firstShift) ((second.val : ℤ) - secondShift) := by
  by_cases hn : profile ((first - (firstShift : ZMod modulus)).val : ℤ)
      ((second - (secondShift : ZMod modulus)).val : ℤ) = 0
  · rw [hn]
    symm
    by_contra hneq
    have hh := hsupport _ _ hneq
    have hl1 : 0 ≤ (first.val : ℤ) - firstShift := hcore.trans hh.1.1
    have hu1 : (first.val : ℤ) - firstShift < modulus := by linarith [hh.1.2]
    have hl2 : 0 ≤ (second.val : ℤ) - secondShift := hcore.trans hh.2.1
    have hu2 : (second.val : ℤ) - secondShift < modulus := by linarith [hh.2.2]
    have heq1 : (((first.val : ℤ) - firstShift : ℤ) : ZMod modulus) = first - (firstShift : ZMod modulus) := by
      rw [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
    have heq2 : (((second.val : ℤ) - secondShift : ℤ) : ZMod modulus) = second - (secondShift : ZMod modulus) := by
      rw [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
    have hv1 : ((first - (firstShift : ZMod modulus)).val : ℤ) = first.val - firstShift := by
      rw [← heq1, ZMod.val_intCast, Int.emod_eq_of_lt hl1 hu1]
    have hv2 : ((second - (secondShift : ZMod modulus)).val : ℤ) = second.val - secondShift := by
      rw [← heq2, ZMod.val_intCast, Int.emod_eq_of_lt hl2 hu2]
    rw [hv1, hv2] at hn
    exact hneq hn
  · have hh := hsupport _ _ hn
    rw [sub_val_on_core modulus core firstShift first hfirst hh.1.1 hh.1.2,
      sub_val_on_core modulus core secondShift second hsecond hh.2.1 hh.2.2]

def liftedRestrictedPair (modulus coreDepth : ℕ) [NeZero modulus]
    (boundary start source : ℤ) (width : ℕ) (color : ZMod modulus × ZMod modulus) : ℝ :=
  SafePair.restrictPair (paletteSlice modulus coreDepth 0)
    (averagedPair modulus boundary start source width)
      ((ZMod.finEquiv modulus).symm color.1) ((ZMod.finEquiv modulus).symm color.2)

theorem restrictedPair_translation_square_le (modulus coreDepth radius : ℕ) [NeZero modulus]
    (boundary start source shiftBound cutoff : ℤ) (width : ℕ) (lower : ℝ) (hlower : 0 < lower)
    (hcore : 2 * coreDepth ≤ modulus) (hboundary : boundary ≤ coreDepth)
    (firstShift secondShift : ℤ) (hfirst : |firstShift| ≤ radius) (hsecond : |secondShift| ≤ radius)
    (hradius : radius ≤ coreDepth)
    (hstarts : ∀ shift ∈ anchorInterval start width, |shift| ≤ shiftBound) (hsource : |source| ≤ cutoff)
    (hclear : lower ≤ (modulus : ℝ) - 2 * boundary - shiftBound - cutoff) :
    (∑ color : ZMod modulus × ZMod modulus,
      (liftedRestrictedPair modulus coreDepth boundary start source width
        (color - ((firstShift : ZMod modulus), (secondShift : ZMod modulus))) -
       liftedRestrictedPair modulus coreDepth boundary start source width color) ^ 2) ≤
      16 * (modulus : ℝ) * radius / (lower ^ 2 * (width : ℝ) ^ 2) +
      16 * (modulus : ℝ) * (radius : ℝ) ^ 2 / (lower ^ 4 * width) +
      8 * (radius : ℝ) / (lower ^ 2 * width) := by
  let integerMass := maskedIntegerPair modulus boundary lower start source width coreDepth (modulus - 2 * coreDepth)
  have heq (color : ZMod modulus × ZMod modulus) :
      liftedRestrictedPair modulus coreDepth boundary start source width color =
        integerMass color.1.val color.2.val := by
    rw [liftedRestrictedPair, restricted_averagedPair_eq_maskedIntegerPair modulus coreDepth
      boundary start source shiftBound cutoff width lower hlower hcore hboundary hstarts hsource hclear]
    simp only [finEquiv_symm_val]
    rfl
  have hsupport (first second : ℤ) (hn : integerMass first second ≠ 0) :
      ((coreDepth : ℤ) ≤ first ∧ first < (modulus : ℤ) - coreDepth) ∧
      ((coreDepth : ℤ) ≤ second ∧ second < (modulus : ℤ) - coreDepth) := by
    dsimp only [integerMass, maskedIntegerPair] at hn
    split_ifs at hn with hmask
    · exact ⟨(core_interval_mem _ _ hcore _).mp hmask.1,
        (core_interval_mem _ _ hcore _).mp hmask.2⟩
    · exact (hn rfl).elim
  have htranslation (color : ZMod modulus × ZMod modulus) :
      liftedRestrictedPair modulus coreDepth boundary start source width
          (color - ((firstShift : ZMod modulus), (secondShift : ZMod modulus))) =
        integerMass ((color.1.val : ℤ) - firstShift) ((color.2.val : ℤ) - secondShift) := by
    rw [heq]
    exact core_profile_translation modulus coreDepth (by positivity) integerMass hsupport firstShift secondShift
      (hfirst.trans (by exact_mod_cast hradius)) (hsecond.trans (by exact_mod_cast hradius)) color.1 color.2
  simp only [htranslation, heq, Fintype.sum_prod_type]
  have hinj : Function.Injective (fun color : ZMod modulus => (color.val : ℤ)) := by
    intro a b hequal
    apply ZMod.val_injective modulus
    dsimp only at hequal
    exact_mod_cast hequal
  have hh := maskedIntegerPair_translation_square_le
    (fun color : ZMod modulus => (color.val : ℤ)) hinj modulus boundary lower hlower start source
    firstShift secondShift coreDepth width (modulus - 2 * coreDepth)
  simp only [ZMod.card] at hh
  have habuR : |(firstShift : ℝ)| ≤ radius := by exact_mod_cast hfirst
  have habvR : |(secondShift : ℝ)| ≤ radius := by exact_mod_cast hsecond
  have habsum : |((firstShift + secondShift : ℤ) : ℝ)| ≤ 2 * (radius : ℝ) := by
    push_cast
    linarith [abs_add_le (firstShift : ℝ) secondShift]
  have hsum : ((firstShift + secondShift).natAbs : ℝ) ≤ 2 * radius := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using habsum
  have hsquare : (((firstShift + secondShift : ℤ) : ℝ)) ^ 2 ≤ (2 * (radius : ℝ)) ^ 2 := by
    simpa only [← sq, sq_abs] using mul_self_le_mul_self (abs_nonneg _) habsum
  have hboth : (firstShift.natAbs : ℝ) + secondShift.natAbs ≤ 2 * radius := by
    simpa only [Nat.cast_natAbs, Int.cast_abs, two_mul] using add_le_add habuR habvR
  apply hh.trans
  calc
    _ ≤ 2 * (modulus : ℝ) *
        (4 * (2 * (radius : ℝ)) / (lower ^ 2 * (width : ℝ) ^ 2) +
          2 * (2 * (radius : ℝ)) ^ 2 / (lower ^ 4 * width)) +
        4 * (2 * (radius : ℝ)) / (lower ^ 2 * width) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add
        · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by norm_num)) (by positivity)
        · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsquare (by norm_num)) (by positivity)
      · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hboth (by norm_num)) (by positivity)
    _ = _ := by ring

def smoothProfile {State Seed : Type*} [Fintype Seed] [Sub State]
    (source : FiniteDist Seed) (shifts : Seed → State) (profile : State → ℝ) : State → ℝ :=
  fun color => ∑ seed, source.weight seed * profile (color - shifts seed)

theorem smoothProfile_difference_square_le {State Seed : Type*} [Fintype State] [Fintype Seed] [Sub State]
    (source : FiniteDist Seed) (shifts : Seed → State) (profile : State → ℝ) (bound : ℝ)
    (hbound : ∀ seed, (∑ color, (profile (color - shifts seed) - profile color) ^ 2) ≤ bound) :
    (∑ color, (smoothProfile source shifts profile color - profile color) ^ 2) ≤ bound := by
  have heq (color : State) : smoothProfile source shifts profile color - profile color =
      ∑ seed, source.weight seed * (profile (color - shifts seed) - profile color) := by
    simp only [smoothProfile, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, source.sum_one, one_mul]
  simp only [heq]
  exact probability_profile_mixture_square_le_uniform source _ bound hbound

theorem restrictedPair_smoothing_square_le {Seed : Type*} [Fintype Seed]
    (modulus coreDepth radius : ℕ) [NeZero modulus]
    (boundary start scalar shiftBound cutoff : ℤ) (width : ℕ) (lower : ℝ) (hlower : 0 < lower)
    (hcore : 2 * coreDepth ≤ modulus) (hboundary : boundary ≤ coreDepth) (hradius : radius ≤ coreDepth)
    (source : FiniteDist Seed) (firstShift secondShift : Seed → ℤ)
    (hfirst : ∀ seed, |firstShift seed| ≤ radius) (hsecond : ∀ seed, |secondShift seed| ≤ radius)
    (hstarts : ∀ shift ∈ anchorInterval start width, |shift| ≤ shiftBound) (hscalar : |scalar| ≤ cutoff)
    (hclear : lower ≤ (modulus : ℝ) - 2 * boundary - shiftBound - cutoff) :
    let profile := liftedRestrictedPair modulus coreDepth boundary start scalar width
    (∑ color, (smoothProfile source
      (fun seed => ((firstShift seed : ZMod modulus), (secondShift seed : ZMod modulus))) profile color - profile color) ^ 2) ≤
      16 * (modulus : ℝ) * radius / (lower ^ 2 * (width : ℝ) ^ 2) +
      16 * (modulus : ℝ) * (radius : ℝ) ^ 2 / (lower ^ 4 * width) +
      8 * (radius : ℝ) / (lower ^ 2 * width) := by
  apply smoothProfile_difference_square_le
  intro seed
  exact restrictedPair_translation_square_le modulus coreDepth radius boundary start scalar shiftBound cutoff width lower
    hlower hcore hboundary (firstShift seed) (secondShift seed) (hfirst seed) (hsecond seed)
      hradius hstarts hscalar hclear

theorem smoothProfile_mixture {State Seed Index : Type*}
    [Fintype Seed] [Fintype Index] [Sub State]
    (source : FiniteDist Seed) (shifts : Seed → State) (weights : Index → ℝ)
    (profiles : Index → State → ℝ) (color : State) :
    smoothProfile source shifts (fun point => ∑ index, weights index * profiles index point) color =
      ∑ index, weights index * smoothProfile source shifts (profiles index) color := by
  simp only [smoothProfile, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro index _
  apply Finset.sum_congr rfl
  intro seed _
  ring

def liftedRestrictedMixedPair {Index : Type*} [Fintype Index]
    (modulus coreDepth : ℕ) [NeZero modulus] (boundary : ℤ)
    (starts scalars : Index → ℤ) (law : FiniteDist Index) (width : ℕ)
    (color : ZMod modulus × ZMod modulus) : ℝ :=
  SafePair.restrictPair (paletteSlice modulus coreDepth 0)
    (mixedPair modulus boundary starts scalars law.weight width)
      ((ZMod.finEquiv modulus).symm color.1) ((ZMod.finEquiv modulus).symm color.2)

theorem liftedRestrictedMixedPair_mixture {Index : Type*} [Fintype Index]
    (modulus coreDepth : ℕ) [NeZero modulus] (boundary : ℤ)
    (starts scalars : Index → ℤ) (law : FiniteDist Index) (width : ℕ)
    (color : ZMod modulus × ZMod modulus) :
    liftedRestrictedMixedPair modulus coreDepth boundary starts scalars law width color =
      ∑ index, law.weight index *
        liftedRestrictedPair modulus coreDepth boundary (starts index) (scalars index) width color := by
  by_cases hc : (ZMod.finEquiv modulus).symm color.1 ∈ paletteSlice modulus coreDepth 0 ∧
      (ZMod.finEquiv modulus).symm color.2 ∈ paletteSlice modulus coreDepth 0
  · simp only [liftedRestrictedMixedPair, liftedRestrictedPair, SafePair.restrictPair, hc, and_self, if_true, mixedPair]
  · simp only [liftedRestrictedMixedPair, liftedRestrictedPair, SafePair.restrictPair, hc,
      if_false, mul_zero, Finset.sum_const_zero]

theorem restrictedMixedPair_smoothing_square_le {Seed Index : Type*} [Fintype Seed] [Fintype Index]
    (modulus coreDepth radius : ℕ) [NeZero modulus]
    (boundary shiftBound cutoff : ℤ) (width : ℕ) (lower : ℝ) (hlower : 0 < lower)
    (hcore : 2 * coreDepth ≤ modulus) (hboundary : boundary ≤ coreDepth) (hradius : radius ≤ coreDepth)
    (starts scalars : Index → ℤ) (law : FiniteDist Index)
    (source : FiniteDist Seed) (firstShift secondShift : Seed → ℤ)
    (hfirst : ∀ seed, |firstShift seed| ≤ radius) (hsecond : ∀ seed, |secondShift seed| ≤ radius)
    (hstarts : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hscalar : ∀ index, |scalars index| ≤ cutoff)
    (hclear : lower ≤ (modulus : ℝ) - 2 * boundary - shiftBound - cutoff) :
    let profile := liftedRestrictedMixedPair modulus coreDepth boundary starts scalars law width
    (∑ color, (smoothProfile source
      (fun seed => ((firstShift seed : ZMod modulus), (secondShift seed : ZMod modulus))) profile color - profile color) ^ 2) ≤
      16 * (modulus : ℝ) * radius / (lower ^ 2 * (width : ℝ) ^ 2) +
      16 * (modulus : ℝ) * (radius : ℝ) ^ 2 / (lower ^ 4 * width) +
      8 * (radius : ℝ) / (lower ^ 2 * width) := by
  have hmass : liftedRestrictedMixedPair modulus coreDepth boundary starts scalars law width =
      fun color => ∑ index, law.weight index *
        liftedRestrictedPair modulus coreDepth boundary (starts index) (scalars index) width color := by
    funext color
    exact liftedRestrictedMixedPair_mixture modulus coreDepth boundary starts scalars law width color
  dsimp only
  rw [hmass]
  simp only [smoothProfile_mixture, ← Finset.sum_sub_distrib, ← mul_sub]
  apply probability_profile_mixture_square_le_uniform law
  intro index
  exact restrictedPair_smoothing_square_le modulus coreDepth radius boundary (starts index) (scalars index)
    shiftBound cutoff width lower hlower hcore hboundary hradius source firstShift secondShift
      hfirst hsecond (hstarts index) (hscalar index) hclear

end

end CurrentAFT.PairSmoothing

end

section










namespace AFT
end AFT
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice





/-!
# The actual fixed-scalar diffuse pair and its safe quadratic seed

The anchor sign is the pushforward of the actual primary color and fair
midpoint coin. Public blur uses two actual independent edge Gaussians. The
protected second scalar is fixed throughout each pair; it is not resampled
between the two endpoints or across factors of a shared-scalar product.
-/

namespace CurrentAFT.DiffusePair

open AFT AFT.TrimmedSlice AFT.SafeConvolution DiffuseProfiles ProposalPrimary
  ProposalSymmetry ActualControls FirstResponse PairSmoothing
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  Parameters.safeMargin ProposalPrimary.primaryLaw ProposalPrimary.centerLaw
  DiffuseProfiles.edgeLaw ProposalSymmetry.directionLaw

abbrev PairSeed (security : ℕ) := Bool ×
  (GaussianSource.Window (edgeCutoff security) × GaussianSource.Window (edgeCutoff security))

def pairSeedLaw (security : ℕ) : FiniteDist (PairSeed security) :=
  (directionLaw security).prod ((edgeLaw security).prod (edgeLaw security))

def pairBlur (security : ℕ) (seed : PairSeed security) : ℤ := seed.2.1 - seed.2.2

def pairStart (security : ℕ) (seed : PairSeed security) : ℤ :=
  intervalStart seed.1 (Parameters.anchorWidth security) (pairBlur security seed)

theorem pairBlur_bound (security : ℕ) (seed : PairSeed security) :
    |pairBlur security seed| ≤ Parameters.sourceCutoff security := by
  have h1 := Finset.mem_Icc.mp seed.2.1.property
  have h2 := Finset.mem_Icc.mp seed.2.2.property
  unfold pairBlur edgeCutoff at *
  apply abs_le.mpr
  constructor <;> omega

theorem pairStart_bound (security : ℕ) (seed : PairSeed security) (shift : ℤ)
    (hshift : shift ∈ anchorInterval (pairStart security seed) (Parameters.anchorWidth security)) :
    |shift| ≤ 2 * (Parameters.anchorWidth security : ℤ) + Parameters.sourceCutoff security :=
  interval_bound seed.1 (Parameters.anchorWidth security) _ _ shift (pairBlur_bound security seed) hshift

theorem pair_clearance (security : ℕ) :
    2 * (1 : ℤ) + (2 * (Parameters.anchorWidth security : ℤ) + Parameters.sourceCutoff security) +
      Parameters.sourceCutoff security < Parameters.modulus security := by
  have h := deletion_clearance security
  unfold deletion at h
  omega

def pairProfile (security : ℕ) (scalar : ℤ) :
    ActualControls.Palette security → ActualControls.Palette security → ℝ :=
  mixedPair (Parameters.modulus security) 1 (pairStart security) (fun _ => scalar)
    (pairSeedLaw security).weight (Parameters.anchorWidth security)

theorem pairProfile_nonneg (security : ℕ) (scalar : ℤ) (first second : ActualControls.Palette security) :
    0 ≤ pairProfile security scalar first second :=
  mixedPair_nonneg _ _ _ _ _ _ (pairSeedLaw security).nonneg _ _

theorem pairProfile_mass (security : ℕ) (scalar : ℤ) (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    ∑ first, ∑ second, pairProfile security scalar first second = 1 :=
  mixedPair_mass (Parameters.modulus security) 1
    (2 * (Parameters.anchorWidth security : ℤ) + Parameters.sourceCutoff security)
    (Parameters.sourceCutoff security) (Parameters.anchorWidth security)
    (InwardAnchor.anchorWidth_pos security).ne' _ _ _ (pairSeedLaw security).sum_one (by norm_num)
      (pairStart_bound security) (fun _ => hscalar) (pair_clearance security)



theorem pairProfile_symmetric (security : ℕ) (scalar : ℤ) (first second : ActualControls.Palette security) :
    pairProfile security scalar first second = pairProfile security scalar second first :=
  mixedPair_symmetric _ _ _ _ _ _ _ _

theorem pairProfile_height (security : ℕ) (scalar : ℤ) (hscalar : |scalar| ≤ Parameters.sourceCutoff security)
    (first second : ActualControls.Palette security) :
    pairProfile security scalar first second ≤
      1 / ((Parameters.anchorWidth security : ℝ) *
        ((Parameters.modulus security : ℝ) - deletion security)) := by
  unfold pairProfile
  have h := mixedPair_le (Parameters.modulus security) 1
    (2 * (Parameters.anchorWidth security : ℤ) + Parameters.sourceCutoff security)
    (Parameters.sourceCutoff security) (Parameters.anchorWidth security)
    (pairStart security) (fun _ => scalar) (pairSeedLaw security).weight
    (pairSeedLaw security).nonneg (pairSeedLaw security).sum_one
    (pairStart_bound security) (fun _ => hscalar) (pair_clearance security) first second
  convert h using 1
  simp only [deletion, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.cast_add,
    Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
  congr 2
  ring

def safeCore (security : ℕ) : Finset (ActualControls.Palette security) :=
  paletteSlice (Parameters.modulus security) (Parameters.safeMargin security) 0

theorem safeCore_mem (security : ℕ) (color : ActualControls.Palette security) :
    color ∈ safeCore security ↔ InwardAnchor.SafeColor security color :=
  core_palette_mem _ _ _

theorem safeCore_nonempty (security : ℕ) : (safeCore security).Nonempty := by
  apply paletteSlice_nonempty
  · positivity
  · have h := safe_clearance security
    simp only [abs_zero]
    omega

def safePairProfile (security : ℕ) (scalar : ℤ) :
    ActualControls.Palette security → ActualControls.Palette security → ℝ :=
  SafePair.coreSeed (safeCore security) (pairProfile security scalar)

theorem safePairProfile_canonical (security : ℕ) (scalar : ℤ) :
    (∀ first, ∑ second, safePairProfile security scalar first second = 0) ∧
    (∀ second, ∑ first, safePairProfile security scalar first second = 0) :=
  SafePair.coreSeed_canonical _ _ (safeCore_nonempty security)

theorem safePairProfile_zero_outside (security : ℕ) (scalar : ℤ)
    (first second : ActualControls.Palette security)
    (hout : ¬InwardAnchor.SafeColor security first ∨ ¬InwardAnchor.SafeColor security second) :
    safePairProfile security scalar first second = 0 := by
  apply SafePair.coreSeed_supported
  simpa only [safeCore_mem] using hout

theorem safePairProfile_counting_square (security : ℕ) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    (∑ first, ∑ second, safePairProfile security scalar first second ^ 2) ≤
      1 / ((Parameters.anchorWidth security : ℝ) *
        ((Parameters.modulus security : ℝ) - deletion security)) := by
  calc
    _ ≤ ∑ first, ∑ second, pairProfile security scalar first second ^ 2 :=
      SafePair.coreSeed_square_le _ _ (safeCore_nonempty security)
    _ ≤ ∑ first, ∑ second,
        (1 / ((Parameters.anchorWidth security : ℝ) *
          ((Parameters.modulus security : ℝ) - deletion security))) * pairProfile security scalar first second := by
      apply Finset.sum_le_sum
      intro first _
      apply Finset.sum_le_sum
      intro second _
      have h := mul_le_mul_of_nonneg_right (pairProfile_height security scalar hscalar first second)
        (pairProfile_nonneg security scalar first second)
      nlinarith only [h]
    _ = _ := by simp only [← Finset.mul_sum, pairProfile_mass security scalar hscalar, mul_one]

def liftedPairProfile (security : ℕ) (scalar : ℤ) :
    ZMod (Parameters.modulus security) × ZMod (Parameters.modulus security) → ℝ :=
  liftedRestrictedMixedPair (Parameters.modulus security) (Parameters.safeMargin security) 1
    (pairStart security) (fun _ => scalar) (pairSeedLaw security) (Parameters.anchorWidth security)

def rootPairLaw (security : ℕ) : FiniteDist (DiffuseProfiles.ActualSeed security × DiffuseProfiles.ActualSeed security) :=
  (actualSeedLaw security).prod (actualSeedLaw security)

def rootPairShift (security : ℕ) (seed : DiffuseProfiles.ActualSeed security × DiffuseProfiles.ActualSeed security) :
    ZMod (Parameters.modulus security) × ZMod (Parameters.modulus security) :=
  ((actualBlur security seed.1 : ZMod (Parameters.modulus security)),
    (actualBlur security seed.2 : ZMod (Parameters.modulus security)))

theorem liftedPairProfile_smoothing_square (security : ℕ) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    (∑ color, (smoothProfile (rootPairLaw security) (rootPairShift security) (liftedPairProfile security scalar) color -
      liftedPairProfile security scalar color) ^ 2) ≤
      16 * (Parameters.modulus security : ℝ) * Parameters.sourceCutoff security /
        (((Parameters.modulus security : ℝ) / 2) ^ 2 * (Parameters.anchorWidth security : ℝ) ^ 2) +
      16 * (Parameters.modulus security : ℝ) * (Parameters.sourceCutoff security : ℝ) ^ 2 /
        (((Parameters.modulus security : ℝ) / 2) ^ 4 * Parameters.anchorWidth security) +
      8 * (Parameters.sourceCutoff security : ℝ) /
        (((Parameters.modulus security : ℝ) / 2) ^ 2 * Parameters.anchorWidth security) := by
  have hq := FirstResponse.modulus_pos security
  have hcore : 2 * Parameters.safeMargin security ≤ Parameters.modulus security := by
    have h := safe_clearance security
    omega
  have hmargin : Parameters.sourceCutoff security ≤ Parameters.safeMargin security := by
    simp only [Parameters.safeMargin]
    omega
  have hden : (Parameters.modulus security : ℝ) / 2 ≤
      (Parameters.modulus security : ℝ) - 2 * (1 : ℝ) -
        (2 * (Parameters.anchorWidth security : ℝ) + Parameters.sourceCutoff security) -
        Parameters.sourceCutoff security := by
    have h := Nat.cast_le (α := ℝ).mpr (two_deletion_le_modulus security)
    simp only [deletion, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at h
    linarith
  exact restrictedMixedPair_smoothing_square_le (Parameters.modulus security) (Parameters.safeMargin security)
    (Parameters.sourceCutoff security) 1
    (2 * (Parameters.anchorWidth security : ℤ) + Parameters.sourceCutoff security)
    (Parameters.sourceCutoff security) (Parameters.anchorWidth security) ((Parameters.modulus security : ℝ) / 2)
    (by positivity) hcore (by have h := InwardAnchor.sourceCutoff_pos security; have := hmargin; omega) hmargin
    (pairStart security) (fun _ => scalar) (pairSeedLaw security) (rootPairLaw security)
    (fun seed => actualBlur security seed.1) (fun seed => actualBlur security seed.2)
    (fun seed => (actualBlur_bound security seed.1).trans (by omega))
    (fun seed => (actualBlur_bound security seed.2).trans (by omega))
    (pairStart_bound security) (fun _ => hscalar) (by simpa only [Int.cast_add, Int.cast_mul,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_one] using hden)

end

end CurrentAFT.DiffusePair

end

section










/-!
# Concrete current-parameter quadratic diffuse-pair budgets

The body density is obtained from the actual safe pair seed and the proved
positive safe reference. The smoothing estimate is the complete estimate
for the original integer slice, evaluated at the actual `q,A,B` family.
-/

namespace CurrentAFT.DiffusePairBounds

open AFT AFT.TrimmedSlice AFT.SafeConvolution DiffuseProfiles ProposalPrimary
  ActualControls FirstResponse PairSmoothing DiffusePair BackgroundRates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  Parameters.safeMargin ProposalPrimary.primaryLaw ProposalPrimary.centerLaw ActualControls.bodyReference
  DiffusePair.pairProfile DiffusePair.safePairProfile DiffusePair.liftedPairProfile
  DiffusePair.rootPairLaw DiffusePair.rootPairShift

theorem safe_sum_eq (security : ℕ) (profile : ActualControls.Palette security → ℝ)
    (hzero : ∀ color, ¬InwardAnchor.SafeColor security color → profile color = 0) :
    (∑ color : SafePalette security, profile color.val) = ∑ color, profile color := by
  have hsplit := Fintype.sum_subtype_add_sum_subtype (InwardAnchor.SafeColor security) profile
  have houtside : (∑ color : {color // ¬InwardAnchor.SafeColor security color}, profile color.val) = 0 := by
    apply Finset.sum_eq_zero
    intro color _
    exact hzero color.val color.property
  rw [houtside, add_zero] at hsplit
  exact hsplit

def bodyPairDensity (security : ℕ) (scalar : ℤ) (first second : SafePalette security) : ℝ :=
  safePairProfile security scalar first.val second.val /
    ((bodyReference security).weight first * (bodyReference security).weight second)







theorem bodyPairDensity_centered_second (security : ℕ) (scalar : ℤ) (first : SafePalette security) :
    (∑ second, (bodyReference security).weight second * bodyPairDensity security scalar first second) = 0 := by
  have hpoint (second : SafePalette security) :
      (bodyReference security).weight second * bodyPairDensity security scalar first second =
        safePairProfile security scalar first.val second.val / (bodyReference security).weight first := by
    unfold bodyPairDensity
    field_simp [(bodyReference_positive security first).ne', (bodyReference_positive security second).ne']
  simp only [hpoint, ← Finset.sum_div]
  rw [safe_sum_eq security _ (fun color hunsafe => safePairProfile_zero_outside security scalar first.val color (Or.inr hunsafe)),
    (safePairProfile_canonical security scalar).1, zero_div]

theorem bodyPairDensity_centered_first (security : ℕ) (scalar : ℤ) (second : SafePalette security) :
    (∑ first, (bodyReference security).weight first * bodyPairDensity security scalar first second) = 0 := by
  have hpoint (first : SafePalette security) :
      (bodyReference security).weight first * bodyPairDensity security scalar first second =
        safePairProfile security scalar first.val second.val / (bodyReference security).weight second := by
    unfold bodyPairDensity
    field_simp [(bodyReference_positive security first).ne', (bodyReference_positive security second).ne']
  simp only [hpoint, ← Finset.sum_div]
  rw [safe_sum_eq security _ (fun color hunsafe => safePairProfile_zero_outside security scalar color second.val (Or.inl hunsafe)),
    (safePairProfile_canonical security scalar).2, zero_div]

theorem safePairProfile_safe_square (security : ℕ) (scalar : ℤ) :
    (∑ first : SafePalette security, ∑ second : SafePalette security,
      safePairProfile security scalar first.val second.val ^ 2) =
      ∑ first, ∑ second, safePairProfile security scalar first second ^ 2 := by
  have hrow (first : ActualControls.Palette security) :
      (∑ second : SafePalette security, safePairProfile security scalar first second.val ^ 2) =
        ∑ second, safePairProfile security scalar first second ^ 2 := by
    apply safe_sum_eq security (fun second => safePairProfile security scalar first second ^ 2)
    intro color hunsafe
    rw [safePairProfile_zero_outside security scalar first color (Or.inr hunsafe), zero_pow (by decide : 2 ≠ 0)]
  simp only [hrow]
  apply safe_sum_eq security (fun first => ∑ second, safePairProfile security scalar first second ^ 2)
  intro color hunsafe
  simp only [safePairProfile_zero_outside security scalar color _ (Or.inl hunsafe),
    zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]

theorem bodyPairDensity_square_bound (security : ℕ) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    (∑ first, ∑ second, (bodyReference security).weight first * (bodyReference security).weight second *
      bodyPairDensity security scalar first second ^ 2) ≤
      4 * (Parameters.modulus security : ℝ) ^ 2 /
        ((Parameters.anchorWidth security : ℝ) * ((Parameters.modulus security : ℝ) - deletion security)) := by
  have hq := FirstResponse.modulus_pos security
  have hpoint (first second : SafePalette security) :
      (bodyReference security).weight first * (bodyReference security).weight second *
          bodyPairDensity security scalar first second ^ 2 ≤
        4 * (Parameters.modulus security : ℝ) ^ 2 * safePairProfile security scalar first.val second.val ^ 2 := by
    have hden : 1 / (4 * (Parameters.modulus security : ℝ) ^ 2) ≤
        (bodyReference security).weight first * (bodyReference security).weight second := by
      have h := mul_le_mul (bodyReference_lower security first) (bodyReference_lower security second)
        (by positivity : (0 : ℝ) ≤ 1 / (2 * (Parameters.modulus security : ℝ)))
        (bodyReference_positive security first).le
      convert h using 1 <;> first | rfl | ring
    calc
      _ = safePairProfile security scalar first.val second.val ^ 2 /
          ((bodyReference security).weight first * (bodyReference security).weight second) := by
        unfold bodyPairDensity
        field_simp [(bodyReference_positive security first).ne', (bodyReference_positive security second).ne']
      _ ≤ safePairProfile security scalar first.val second.val ^ 2 /
          (1 / (4 * (Parameters.modulus security : ℝ) ^ 2)) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
      _ = _ := by field_simp [hq.ne']
  calc
    _ ≤ ∑ first, ∑ second,
        4 * (Parameters.modulus security : ℝ) ^ 2 * safePairProfile security scalar first.val second.val ^ 2 :=
      Finset.sum_le_sum fun first _ => Finset.sum_le_sum fun second _ => hpoint first second
    _ = 4 * (Parameters.modulus security : ℝ) ^ 2 *
        ∑ first, ∑ second, safePairProfile security scalar first second ^ 2 := by
      simp only [← Finset.mul_sum]
      rw [safePairProfile_safe_square]
    _ ≤ 4 * (Parameters.modulus security : ℝ) ^ 2 *
        (1 / ((Parameters.anchorWidth security : ℝ) * ((Parameters.modulus security : ℝ) - deletion security))) :=
      mul_le_mul_of_nonneg_left (safePairProfile_counting_square security scalar hscalar) (by positivity)
    _ = _ := by ring

theorem bodyPairDensity_square_growth (security : ℕ) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    (∑ first, ∑ second, (bodyReference security).weight first * (bodyReference security).weight second *
      bodyPairDensity security scalar first second ^ 2) ≤
        1048576 * (Parameters.base security : ℝ) ^ 16 := by
  have hb := FirstResponse.base_pos security
  have hq := FirstResponse.modulus_pos security
  have ha : (0 : ℝ) < Parameters.anchorWidth security := Nat.cast_pos.mpr (InwardAnchor.anchorWidth_pos security)
  have hd : (Parameters.modulus security : ℝ) / 2 ≤ (Parameters.modulus security : ℝ) - deletion security := by
    have h := Nat.cast_le (α := ℝ).mpr (two_deletion_le_modulus security)
    push_cast at h
    linarith
  have hqu : (Parameters.modulus security : ℝ) ≤ 131072 * (Parameters.base security : ℝ) ^ 64 := by
    exact_mod_cast (Parameters.modulus_bounds security).2
  calc
    _ ≤ 4 * (Parameters.modulus security : ℝ) ^ 2 /
        ((Parameters.anchorWidth security : ℝ) * ((Parameters.modulus security : ℝ) - deletion security)) :=
      bodyPairDensity_square_bound security scalar hscalar
    _ ≤ 4 * (Parameters.modulus security : ℝ) ^ 2 /
        ((Parameters.anchorWidth security : ℝ) * ((Parameters.modulus security : ℝ) / 2)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (mul_le_mul_of_nonneg_left hd ha.le)
    _ = 8 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security := by field_simp; ring
    _ ≤ 8 * (131072 * (Parameters.base security : ℝ) ^ 64) / Parameters.anchorWidth security :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hqu (by norm_num)) ha.le
    _ = _ := by rw [anchorWidth_eq, Nat.cast_pow]; field_simp; ring

theorem bodyPairDensity_norm_growth (security : ℕ) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    Real.sqrt (∑ first, ∑ second, (bodyReference security).weight first * (bodyReference security).weight second *
      bodyPairDensity security scalar first second ^ 2) ≤
        1024 * (Parameters.base security : ℝ) ^ 8 := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  convert bodyPairDensity_square_growth security scalar hscalar using 1; ring

def smoothingBudget (security : ℕ) : ℝ :=
  16 * (Parameters.modulus security : ℝ) * Parameters.sourceCutoff security /
    (((Parameters.modulus security : ℝ) / 2) ^ 2 * (Parameters.anchorWidth security : ℝ) ^ 2) +
  16 * (Parameters.modulus security : ℝ) * (Parameters.sourceCutoff security : ℝ) ^ 2 /
    (((Parameters.modulus security : ℝ) / 2) ^ 4 * Parameters.anchorWidth security) +
  8 * (Parameters.sourceCutoff security : ℝ) /
    (((Parameters.modulus security : ℝ) / 2) ^ 2 * Parameters.anchorWidth security)

theorem smoothingBudget_scaled (security : ℕ) :
    (Parameters.modulus security : ℝ) ^ 2 * smoothingBudget security =
      64 * (Parameters.modulus security : ℝ) * Parameters.sourceCutoff security /
        (Parameters.anchorWidth security : ℝ) ^ 2 +
      256 * (Parameters.sourceCutoff security : ℝ) ^ 2 /
        ((Parameters.modulus security : ℝ) * Parameters.anchorWidth security) +
      32 * (Parameters.sourceCutoff security : ℝ) / Parameters.anchorWidth security := by
  have hq := (FirstResponse.modulus_pos security).ne'
  have ha : (Parameters.anchorWidth security : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (InwardAnchor.anchorWidth_pos security).ne'
  unfold smoothingBudget
  field_simp
  ring

theorem smoothingBudget_scaled_decay (security : ℕ) :
    (Parameters.modulus security : ℝ) ^ 2 * smoothingBudget security ≤
      8388896 / (Parameters.base security : ℝ) ^ 30 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hq := FirstResponse.modulus_pos security
  have hqu : (Parameters.modulus security : ℝ) ≤ 131072 * (Parameters.base security : ℝ) ^ 64 := by
    exact_mod_cast (Parameters.modulus_bounds security).2
  have hql : (Parameters.base security : ℝ) ^ 64 ≤ Parameters.modulus security := by
    have h := (Parameters.modulus_bounds security).1
    have hpow : 0 < Parameters.base security ^ 64 := pow_pos (Parameters.base_pos security) _
    exact_mod_cast (show Parameters.base security ^ 64 ≤ Parameters.modulus security by omega)
  rw [smoothingBudget_scaled, Parameters.sourceCutoff, anchorWidth_eq]
  simp only [Nat.cast_pow]
  calc
    _ ≤ 64 * (131072 * (Parameters.base security : ℝ) ^ 64) * (Parameters.base security : ℝ) ^ 2 /
        ((Parameters.base security : ℝ) ^ 48) ^ 2 +
      256 * ((Parameters.base security : ℝ) ^ 2) ^ 2 /
        ((Parameters.base security : ℝ) ^ 64 * (Parameters.base security : ℝ) ^ 48) +
      32 * (Parameters.base security : ℝ) ^ 2 / (Parameters.base security : ℝ) ^ 48 := by
      apply add_le_add _ le_rfl
      apply add_le_add
      · apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqu (by norm_num)) (by positivity)
      · exact div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_right hql (by positivity))
    _ = 8388608 / (Parameters.base security : ℝ) ^ 30 +
        256 / (Parameters.base security : ℝ) ^ 108 +
        32 / (Parameters.base security : ℝ) ^ 46 := by field_simp; ring
    _ ≤ 8388608 / (Parameters.base security : ℝ) ^ 30 +
        256 / (Parameters.base security : ℝ) ^ 30 +
        32 / (Parameters.base security : ℝ) ^ 30 := by
      apply add_le_add
      · exact add_le_add le_rfl (div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _)
          (pow_le_pow_right₀ hb1 (by omega)))
      · exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _)
          (pow_le_pow_right₀ hb1 (by omega))
    _ = _ := by ring

theorem liftedPairProfile_scaled_smoothing_decay (security : ℕ) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    (Parameters.modulus security : ℝ) ^ 2 *
      (∑ color, (smoothProfile (rootPairLaw security) (rootPairShift security) (liftedPairProfile security scalar) color -
        liftedPairProfile security scalar color) ^ 2) ≤
      8388896 / (Parameters.base security : ℝ) ^ 30 :=
  (mul_le_mul_of_nonneg_left (liftedPairProfile_smoothing_square security scalar hscalar)
    (sq_nonneg _)).trans (smoothingBudget_scaled_decay security)

end

end CurrentAFT.DiffusePairBounds

end

section








/-! Exact finite equivalence transport for joint mass profiles and core seeds. -/

namespace CurrentAFT.PairReindex

open AFT AFT.SafePair AFT.SafeConvolution
open scoped BigOperators Classical

noncomputable section

variable {First Second : Type*} [Fintype First] [Fintype Second]

def liftPair (equiv : First ≃ Second) (profile : First → First → ℝ) : Second → Second → ℝ :=
  fun first second => profile (equiv.symm first) (equiv.symm second)

theorem liftPair_first_sum (equiv : First ≃ Second) (profile : First → First → ℝ) (second : Second) :
    (∑ first, liftPair equiv profile first second) = ∑ first, profile first (equiv.symm second) :=
  by
    unfold liftPair
    exact equiv.symm.sum_comp (fun first : First => profile first (equiv.symm second))

theorem liftPair_second_sum (equiv : First ≃ Second) (profile : First → First → ℝ) (first : Second) :
    (∑ second, liftPair equiv profile first second) = ∑ second, profile (equiv.symm first) second :=
  by
    unfold liftPair
    exact equiv.symm.sum_comp (fun second : First => profile (equiv.symm first) second)

theorem liftPair_total (equiv : First ≃ Second) (profile : First → First → ℝ) :
    (∑ first, ∑ second, liftPair equiv profile first second) = ∑ first, ∑ second, profile first second := by
  calc
    _ = ∑ first : Second, ∑ second : First, profile (equiv.symm first) second := by
      apply Finset.sum_congr rfl
      intro first _
      exact liftPair_second_sum equiv profile first
    _ = _ := equiv.symm.sum_comp (fun first : First => ∑ second : First, profile first second)

omit [Fintype First] [Fintype Second] in
theorem liftPair_symmetric (equiv : First ≃ Second) (profile : First → First → ℝ)
    (hsymmetric : ∀ first second, profile first second = profile second first) (first second : Second) :
    liftPair equiv profile first second = liftPair equiv profile second first :=
  hsymmetric (equiv.symm first) (equiv.symm second)

theorem liftPair_countingL2 (equiv : First ≃ Second) (profile : First → First → ℝ) :
    pairCountingL2 (liftPair equiv profile) = pairCountingL2 profile := by
  unfold pairCountingL2 countingL2
  congr 1
  simpa only [Fintype.sum_prod_type, liftPair] using liftPair_total equiv (fun first second => profile first second ^ 2)

variable [DecidableEq First] [DecidableEq Second]

omit [Fintype First] [Fintype Second] [DecidableEq First] [DecidableEq Second] in
theorem mem_map (equiv : First ≃ Second) (core : Finset First) (color : Second) :
    color ∈ core.map equiv.toEmbedding ↔ equiv.symm color ∈ core := by
  constructor
  · intro h
    obtain ⟨first, hfirst, heq⟩ := Finset.mem_map.mp h
    simpa only [← heq, Equiv.coe_toEmbedding, Equiv.symm_apply_apply] using hfirst
  · intro h
    exact Finset.mem_map.mpr ⟨equiv.symm color, h, equiv.apply_symm_apply color⟩

omit [Fintype First] [Fintype Second] in
theorem uniformFiniteProfile_map (equiv : First ≃ Second) (core : Finset First) (color : Second) :
    uniformFiniteProfile (core.map equiv.toEmbedding) color = uniformFiniteProfile core (equiv.symm color) := by
  simp only [uniformFiniteProfile, mem_map, Finset.card_map]

omit [Fintype First] [Fintype Second] in
theorem restrictPair_map (equiv : First ≃ Second) (core : Finset First) (profile : First → First → ℝ) :
    restrictPair (core.map equiv.toEmbedding) (liftPair equiv profile) = liftPair equiv (restrictPair core profile) := by
  funext first second
  simp only [restrictPair, mem_map, liftPair]

omit [DecidableEq First] [DecidableEq Second] in
theorem canonicalPair_lift (equiv : First ≃ Second) (reference : First → ℝ) (profile : First → First → ℝ) :
    canonicalPair (reference ∘ equiv.symm) (liftPair equiv profile) = liftPair equiv (canonicalPair reference profile) := by
  funext first second
  simp only [canonicalPair, Function.comp_apply]
  rw [liftPair_first_sum, liftPair_second_sum, liftPair_total]
  rfl

theorem coreSeed_map (equiv : First ≃ Second) (core : Finset First) (profile : First → First → ℝ) :
    coreSeed (core.map equiv.toEmbedding) (liftPair equiv profile) = liftPair equiv (coreSeed core profile) := by
  unfold coreSeed
  rw [restrictPair_map]
  have href : uniformFiniteProfile (core.map equiv.toEmbedding) = uniformFiniteProfile core ∘ equiv.symm :=
    funext (uniformFiniteProfile_map equiv core)
  rw [href, canonicalPair_lift]

omit [DecidableEq First] [DecidableEq Second] in
theorem canonicalPair_uniform_lift (equiv : First ≃ Second) (profile : First → First → ℝ) :
    canonicalPair (fun _ => 1 / (Fintype.card Second : ℝ)) (liftPair equiv profile) =
      liftPair equiv (canonicalPair (fun _ => 1 / (Fintype.card First : ℝ)) profile) := by
  simpa only [Fintype.card_congr equiv, Function.comp_def] using
    canonicalPair_lift equiv (fun _ : First => 1 / (Fintype.card First : ℝ)) profile

omit [DecidableEq First] [DecidableEq Second] in
theorem liftPair_difference_countingL2 (equiv : First ≃ Second)
    (first second : First → First → ℝ) :
    pairCountingL2 (liftPair equiv first - liftPair equiv second) = pairCountingL2 (first - second) :=
  liftPair_countingL2 equiv (first - second)

omit [DecidableEq First] [DecidableEq Second] in
theorem liftPair_uniform_error_countingL2 (equiv : First ≃ Second)
    (seed mass : First → First → ℝ) :
    pairCountingL2 (liftPair equiv seed -
      canonicalPair (fun _ => 1 / (Fintype.card Second : ℝ)) (liftPair equiv mass)) =
    pairCountingL2 (seed - canonicalPair (fun _ => 1 / (Fintype.card First : ℝ)) mass) := by
  rw [canonicalPair_uniform_lift]
  exact liftPair_difference_countingL2 equiv seed _

end

end CurrentAFT.PairReindex

end


