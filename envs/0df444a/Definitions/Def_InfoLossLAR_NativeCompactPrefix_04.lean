-- Prove2me | Definitions.Def_InfoLossLAR_NativeCompactPrefix_04
-- name    : InfoLossLAR_NativeCompactPrefix_04
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T13:59:08.695791+00:00
-- url     : https://prove2.me/theorems/66f7baf5-03e8-4faf-b6b6-5481b001e5b8
-- title:
--   Physical-output, Fourier, and affine completion data
-- statement:
--   This package defines marked pair and common-queue background families, finite Newton iteration, conditional histogram means and exponential-moment expressions, physical Fock and tagged selection data, Fourier support and energy coordinates, public signed and positive output channels, affine flag and leg laws, completed public outputs, the actual background, truncated polynomial evaluation, family evaluation, and scalar augmentation.
--
--   The interfaces retain the complete finite response and output expressions required by the later global calibration and affine sampler theorems. Ordinary approximation and transport bounds are stated separately. Supporting constructor identities remain part of the data API; native operation counts are kept separate from the platform machine-time certificate.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0; exact source units Definitions.Def_InfoLossLAR_NativeSparsePrefix_25, Definitions.Def_InfoLossLAR_NativeSparsePrefix_26, Definitions.Def_InfoLossLAR_NativeSparsePrefix_27, Definitions.Def_InfoLossLAR_NativeSparsePrefix_28, Definitions.Def_InfoLossLAR_NativeSparsePrefix_29. Original module paths and non-import body hashes are recorded in native_compact_prefix/manifest.json. These previously audited data bodies are copied byte-for-byte with closed section wrappers, and published SparsePrefix01–07 remain unchanged. SHA256 6194ef14f20f1fa74a383981e6e948c5cf07e1005b3be699a1480b3b311b7aa4.

import Definitions.Def_InfoLossLAR_NativeCompactPrefix_03

section

section












/-! Complete actual diffuse quadratic certificate: two safe body slots and a small two-primary residual. -/

namespace CurrentAFT.DiffusePairCertificates

open AFT AFT.SafeConvolution ControlCoordinates GradedControlAlgebra GradedControlNorm
  GradedControlStability DiffuseProfiles ProposalPrimary ActualControls BackgroundRates
  BackgroundFamilies PairCertificateFamilies PrimaryTensorInverse PrimaryMassFamilies
  DiffusePair DiffusePairResidual DiffusePairResidualRates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
  BackgroundRates.primaryFactor BackgroundRates.bodyFactor DiffusePairResidualRates.finiteResidual
  DiffusePairResidual.seedProfile DiffusePairResidual.originalProfile DiffusePairResidual.rootResiduePairLaw
  PrimaryTensorInverse.massLeading

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def residualMass (security : ℕ) (scalar : ℤ) (word : Fin 2 → ActualControls.Palette security) : ℝ :=
  pairWordProfile (finiteResidual security scalar) word

theorem residualMass_centered (security : ℕ) (scalar : ℤ) : MassCentered 2 (residualMass security scalar) := by
  intro index word
  fin_cases index
  · simpa [residualMass, pairWordProfile, Function.update_apply] using (finiteResidual_canonical security scalar).2 (word 1)
  · simpa [residualMass, pairWordProfile, Function.update_apply] using (finiteResidual_canonical security scalar).1 (word 0)

theorem residualMass_symmetric (security : ℕ) (scalar : ℤ)
    (permutation : Equiv.Perm (Fin 2)) (word : Fin 2 → ActualControls.Palette security) :
    residualMass security scalar (word ∘ permutation) = residualMass security scalar word := by
  exact pairWordProfile_symmetric (finiteResidual security scalar)
    (finiteResidual_symmetric security scalar) permutation word

theorem residualMass_energy (security : ℕ) (scalar : ℤ) :
    massEnergy security 2 (residualMass security scalar) =
      BlockDensity.pairEnergy (primaryLaw security).weight (primaryLaw security).weight (finiteResidual security scalar) := by
  exact pairWordProfile_energy (primaryLaw security).weight (finiteResidual security scalar)

def diffusePrimaryCertificate (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ) : ActualFamily security order :=
  massCertificateFamily security order 2 horder (residualMass security scalar)
    (residualMass_centered security scalar) (residualMass_symmetric security scalar)

theorem diffusePrimaryCertificate_norm (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (diffusePrimaryCertificate security order horder scalar) ≤
        387456 / (Parameters.base security : ℝ) ^ 141 := by
  have hb := FirstResponse.base_pos security
  have ha := activation_pos security
  have hfactor : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hinv : 2 / activation security ≤ 8 * (Parameters.base security : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (FirstResponse.activation_inverse_le security) (show (0 : ℝ) ≤ 2 by norm_num)
    convert h using 1 <;> first | rfl | ring
  have hnorm := massCertificateFamily_norm security order 2 horder
    (primaryFactor security) (bodyFactor security) hfactor (residualMass security scalar)
    (residualMass_centered security scalar) (residualMass_symmetric security scalar)
  have hinput : Real.sqrt (massEnergy security 2 (residualMass security scalar)) ≤
      6054 / (Parameters.base security : ℝ) ^ 15 := by
    rw [residualMass_energy]
    exact finiteResidual_primary_norm_decay security scalar hscalar
  calc
    _ ≤ primaryFactor security ^ 2 * (2 / activation security) ^ 2 *
        Real.sqrt (massEnergy security 2 (residualMass security scalar)) := hnorm
    _ ≤ (1 / (Parameters.base security : ℝ) ^ 64) ^ 2 * (8 * (Parameters.base security : ℝ)) ^ 2 *
        (6054 / (Parameters.base security : ℝ) ^ 15) := by
      rw [primaryFactor_eq]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinv 2) (sq_nonneg _))
        hinput (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by field_simp; ring

def diffuseCertificate (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ) : ActualFamily security order :=
  diffuseBodyCertificate security order horder scalar + diffusePrimaryCertificate security order horder scalar

theorem diffuseCertificate_norm (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (diffuseCertificate security order horder scalar) ≤
        388480 / (Parameters.base security : ℝ) ^ 141 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hbdy : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  calc
    _ ≤ familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
          (diffuseBodyCertificate security order horder scalar) +
        familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
          (diffusePrimaryCertificate security order horder scalar) := familyNorm_add_le _ _ _ _ _ hp hbdy _ _
    _ ≤ 1024 / (Parameters.base security : ℝ) ^ 150 + 387456 / (Parameters.base security : ℝ) ^ 141 :=
      add_le_add (diffuseBodyCertificate_norm_decay security order horder scalar hscalar)
        (diffusePrimaryCertificate_norm security order horder scalar hscalar)
    _ ≤ 1024 / (Parameters.base security : ℝ) ^ 141 + 387456 / (Parameters.base security : ℝ) ^ 141 :=
      add_le_add (div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _)
        (pow_le_pow_right₀ hb1 (by omega))) le_rfl
    _ = _ := by ring







end

end CurrentAFT.DiffusePairCertificates

end

section












/-!
# The actual fixed-scalar marked mixed seed

The first coordinate is centered at the full uniform mass profile and the
safe second coordinate at the actual body law. The resulting mixed density
is canonical under the actual positive primary/body product reference.
-/

namespace CurrentAFT.MarkedPairSeed

open AFT DiffuseProfiles ProposalPrimary ActualControls FirstResponse FringeCertificate
  PrimaryTensorInverse
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  ProposalPrimary.primaryLaw ProposalPrimary.centerLaw ActualControls.bodyReference
  InwardAnchor.shiftedAnchorLaw

abbrev Scalar (security : ℕ) := GaussianSource.Window (Parameters.sourceCutoff security - 1)

def fixedAnchor (security : ℕ) (scalar : Scalar security) (primary : ActualControls.Palette security) :
    FiniteDist (SafePalette security) :=
  supportedLaw (InwardAnchor.shiftedAnchorLaw security primary (-scalar.val)
    (by simpa only [abs_neg] using InwardAnchor.scalar_bound security scalar))
      (InwardAnchor.SafeColor security)
      (InwardAnchor.shiftedAnchorLaw_zero_outside security primary _ _)

theorem fixedAnchor_height (security : ℕ) (scalar : Scalar security)
    (primary : ActualControls.Palette security) (center : SafePalette security) :
    (fixedAnchor security scalar primary).weight center ≤ 1 / (Parameters.anchorWidth security : ℝ) :=
  InwardAnchor.shiftedAnchorLaw_height security primary _ _ center.val

def rawDensity (security : ℕ) (scalar : Scalar security) (primary : ActualControls.Palette security)
    (center : SafePalette security) : ℝ :=
  (fixedAnchor security scalar primary).weight center / (bodyReference security).weight center

def secondCentered (security : ℕ) (scalar : Scalar security) (primary : ActualControls.Palette security)
    (center : SafePalette security) : ℝ := rawDensity security scalar primary center - 1

def secondMean (security : ℕ) (scalar : Scalar security) (center : SafePalette security) : ℝ :=
  (primaryLaw security).expectation (fun primary => secondCentered security scalar primary center)

def uniformRelative (security : ℕ) (primary : ActualControls.Palette security) : ℝ :=
  uniformProfile security primary / (primaryLaw security).weight primary

def seedDensity (security : ℕ) (scalar : Scalar security) (primary : ActualControls.Palette security)
    (center : SafePalette security) : ℝ :=
  secondCentered security scalar primary center - uniformRelative security primary * secondMean security scalar center

theorem rawDensity_mean (security : ℕ) (scalar : Scalar security) (primary : ActualControls.Palette security) :
    (bodyReference security).expectation (rawDensity security scalar primary) = 1 := by
  unfold FiniteDist.expectation rawDensity
  simp only [mul_div_cancel₀ _ (bodyReference_positive security _).ne']
  exact (fixedAnchor security scalar primary).sum_one

theorem secondCentered_mean (security : ℕ) (scalar : Scalar security) (primary : ActualControls.Palette security) :
    (bodyReference security).expectation (secondCentered security scalar primary) = 0 := by
  change (bodyReference security).expectation (fun center => rawDensity security scalar primary center - 1) = 0
  rw [FiniteDist.expectation_sub, rawDensity_mean, FiniteDist.expectation_const, sub_self]

theorem uniformRelative_mean (security : ℕ) : (primaryLaw security).expectation (uniformRelative security) = 1 := by
  have hq := (FirstResponse.modulus_pos security).ne'
  unfold FiniteDist.expectation uniformRelative
  simp only [mul_div_cancel₀ _ (primaryReference_positive security _).ne', uniformProfile,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem uniformRelative_energy (security : ℕ) : (primaryLaw security).l2Sq (uniformRelative security) ≤ 2 := by
  have heq : (primaryLaw security).l2Sq (uniformRelative security) =
      profileSquareNorm (primaryLaw security).weight (uniformProfile security) := by
    exact densityScore_square _ _
  rw [heq]
  exact uniformProfile_square_le_two security

theorem seedDensity_centered_primary (security : ℕ) (scalar : Scalar security) (center : SafePalette security) :
    (primaryLaw security).expectation (fun primary => seedDensity security scalar primary center) = 0 := by
  simp only [FiniteDist.expectation, seedDensity, mul_sub, Finset.sum_sub_distrib,
    ← mul_assoc, ← Finset.sum_mul]
  change secondMean security scalar center - (primaryLaw security).expectation (uniformRelative security) *
    secondMean security scalar center = 0
  rw [uniformRelative_mean, one_mul, sub_self]

theorem secondMean_mean (security : ℕ) (scalar : Scalar security) :
    (bodyReference security).expectation (secondMean security scalar) = 0 := by
  change (bodyReference security).expectation (fun center =>
    (primaryLaw security).expectation (fun primary => secondCentered security scalar primary center)) = 0
  rw [FiniteDist.expectation_comm]
  simp only [secondCentered_mean, FiniteDist.expectation_const]

theorem seedDensity_centered_body (security : ℕ) (scalar : Scalar security) (primary : ActualControls.Palette security) :
    (bodyReference security).expectation (seedDensity security scalar primary) = 0 := by
  change (bodyReference security).expectation (fun center => secondCentered security scalar primary center -
    uniformRelative security primary * secondMean security scalar center) = 0
  rw [FiniteDist.expectation_sub, FiniteDist.expectation_const_mul, secondCentered_mean, secondMean_mean, mul_zero, sub_self]

theorem mismatch_center_energy {Color : Type*} [Fintype Color] (law : FiniteDist Color)
    (multiplier kernel : Color → ℝ) (hbound : law.l2Sq multiplier ≤ 2) :
    law.l2Sq (fun color => kernel color - multiplier color * law.expectation kernel) ≤ 6 * law.l2Sq kernel := by
  have hpoint (color : Color) : (kernel color - multiplier color * law.expectation kernel) ^ 2 ≤
      2 * kernel color ^ 2 + 2 * multiplier color ^ 2 * law.expectation kernel ^ 2 := by
    nlinarith [sq_nonneg (kernel color + multiplier color * law.expectation kernel)]
  have hsum : law.l2Sq (fun color => kernel color - multiplier color * law.expectation kernel) ≤
      2 * law.l2Sq kernel + 2 * law.l2Sq multiplier * law.expectation kernel ^ 2 := by
    unfold FiniteDist.l2Sq FiniteDist.expectation
    calc
      _ ≤ ∑ color, law.weight color *
          (2 * kernel color ^ 2 + 2 * multiplier color ^ 2 * (∑ point, law.weight point * kernel point) ^ 2) :=
        Finset.sum_le_sum fun color _ => mul_le_mul_of_nonneg_left (hpoint color) (law.nonneg color)
      _ = _ := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro color _
        ring
  have hmean := HistogramNormalization.expectation_square_le law kernel
  have hprod := mul_le_mul_of_nonneg_right hbound (sq_nonneg (law.expectation kernel))
  nlinarith

theorem rawDensity_energy (security : ℕ) (scalar : Scalar security) (primary : ActualControls.Palette security) :
    (bodyReference security).l2Sq (rawDensity security scalar primary) ≤
      2 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security := by
  have hq := FirstResponse.modulus_pos security
  have ha : (0 : ℝ) < Parameters.anchorWidth security := Nat.cast_pos.mpr (InwardAnchor.anchorWidth_pos security)
  have hratio (center : SafePalette security) : (fixedAnchor security scalar primary).weight center ≤
      (2 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security) * (bodyReference security).weight center := by
    calc
      _ ≤ 1 / (Parameters.anchorWidth security : ℝ) := fixedAnchor_height security scalar primary center
      _ = (2 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security) *
          (1 / (2 * (Parameters.modulus security : ℝ))) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (bodyReference_lower security center) (by positivity)
  have h := BlockDensity.profile_energy_le_ratio (bodyReference security).weight
    (fixedAnchor security scalar primary).weight (2 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security)
    (bodyReference_positive security) (fixedAnchor security scalar primary).nonneg hratio
  rw [FiniteDist.sum_one, mul_one] at h
  exact (densityScore_square _ _).le.trans h

theorem secondCentered_energy (security : ℕ) (scalar : Scalar security) (primary : ActualControls.Palette security) :
    (bodyReference security).l2Sq (secondCentered security scalar primary) ≤
      2 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security := by
  have hcenter : secondCentered security scalar primary =
      TensorChannel.center (bodyReference security) (rawDensity security scalar primary) := by
    funext center
    simp only [secondCentered, TensorChannel.center_apply, rawDensity_mean]
  rw [hcenter]
  exact (TensorChannel.center_energy_le _ _).trans (rawDensity_energy security scalar primary)

theorem seedDensity_energy (security : ℕ) (scalar : Scalar security) :
    (∑ primary, ∑ center, (primaryLaw security).weight primary * (bodyReference security).weight center *
      seedDensity security scalar primary center ^ 2) ≤
        12 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security := by
  have hcolumn (center : SafePalette security) :
      (primaryLaw security).l2Sq (fun primary => seedDensity security scalar primary center) ≤
        6 * (primaryLaw security).l2Sq (fun primary => secondCentered security scalar primary center) :=
    mismatch_center_energy (primaryLaw security) (uniformRelative security) _ (uniformRelative_energy security)
  calc
    _ = ∑ center, (bodyReference security).weight center *
        (primaryLaw security).l2Sq (fun primary => seedDensity security scalar primary center) := by
      rw [Finset.sum_comm]
      simp only [FiniteDist.l2Sq, FiniteDist.expectation, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro center _
      apply Finset.sum_congr rfl
      intro primary _
      ring
    _ ≤ ∑ center, (bodyReference security).weight center *
        (6 * (primaryLaw security).l2Sq (fun primary => secondCentered security scalar primary center)) :=
      Finset.sum_le_sum fun center _ => mul_le_mul_of_nonneg_left (hcolumn center) ((bodyReference security).nonneg center)
    _ = 6 * ∑ primary, (primaryLaw security).weight primary *
        (bodyReference security).l2Sq (secondCentered security scalar primary) := by
      simp only [FiniteDist.l2Sq, FiniteDist.expectation, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro primary _
      apply Finset.sum_congr rfl
      intro center _
      ring
    _ ≤ 6 * ∑ primary, (primaryLaw security).weight primary *
        (2 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun primary _ => mul_le_mul_of_nonneg_left
        (secondCentered_energy security scalar primary) ((primaryLaw security).nonneg primary)
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]; ring

end

end CurrentAFT.MarkedPairSeed

end

section










/-! The actual fixed-scalar marked seed in one primary and one safe-body fiber. -/

namespace CurrentAFT.MarkedPairCertificates

open AFT ControlCoordinates ControlNorm GradedControlAlgebra GradedControlNorm
  DiffuseProfiles ProposalPrimary ActualControls FirstResponse PrimaryTensorInverse
  BackgroundRates BackgroundFamilies MarkedPairSeed
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth ProposalPrimary.primaryLaw ActualControls.bodyReference
  BackgroundRates.primaryFactor BackgroundRates.bodyFactor MarkedPairSeed.seedDensity

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

def mixedEnergy (primary : FiniteDist Primary) (body : FiniteDist Body) (density : Primary → Body → ℝ) : ℝ :=
  ∑ color, ∑ center, primary.weight color * body.weight center * density color center ^ 2

theorem mixedEnergy_fibers (primary : FiniteDist Primary) (body : FiniteDist Body) (density : Primary → Body → ℝ) :
    mixedEnergy primary body density = ∑ center, body.weight center * primary.l2Sq (fun color => density color center) := by
  unfold mixedEnergy FiniteDist.l2Sq FiniteDist.expectation
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro center _
  apply Finset.sum_congr rfl
  intro color _
  ring

def mixedKernel (primary : FiniteDist Primary) (body : FiniteDist Body) (density : Primary → Body → ℝ)
    (hprimary : ∀ center, primary.expectation (fun color => density color center) = 0)
    (hbody : ∀ color, body.expectation (density color) = 0) : canonicalKernels primary body 1 1 := by
  refine ⟨fun colors centers => density (colors 0) (centers 0), ?_, ?_, ?_⟩
  · intro index colors centers
    have hi : index = 0 := Subsingleton.elim _ _
    subst index
    simpa only [Function.update_self, FiniteDist.expectation] using hprimary (centers 0)
  · intro index colors centers
    have hi : index = 0 := Subsingleton.elim _ _
    subst index
    simpa only [Function.update_self, FiniteDist.expectation] using hbody (colors 0)
  · intro primaryOrder bodyOrder colors centers
    have hp : primaryOrder 0 = 0 := Subsingleton.elim _ _
    have hb : bodyOrder 0 = 0 := Subsingleton.elim _ _
    simp only [Function.comp_apply, hp, hb]

theorem mixedKernel_blockL2 (primary : FiniteDist Primary) (body : FiniteDist Body) (density : Primary → Body → ℝ)
    (hprimary : ∀ center, primary.expectation (fun color => density color center) = 0)
    (hbody : ∀ color, body.expectation (density color) = 0) :
    blockL2 primary body (mixedKernel primary body density hprimary hbody).val = Real.sqrt (mixedEnergy primary body density) := by
  unfold blockL2
  congr 1
  rw [blockEnergy_apply]
  simp only [mixedKernel, Fin.prod_univ_one]
  rw [← (Equiv.funUnique (Fin 1) Primary).symm.sum_comp]
  simp only [Equiv.funUnique_symm_apply, uniqueElim_const]
  apply Finset.sum_congr rfl
  intro color _
  exact ((Equiv.funUnique (Fin 1) Body).symm.sum_comp (fun centers : Fin 1 → Body =>
    primary.weight color * body.weight (centers 0) * density color (centers 0) ^ 2)).symm

def inverseDensity (security : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary : ActualControls.Palette security) (center : SafePalette security) : ℝ :=
  densityInverse security (fun color => seedDensity security scalar color center) primary

theorem inverseDensity_centered_primary (security : ℕ) (scalar : MarkedPairSeed.Scalar security) (center : SafePalette security) :
    (primaryLaw security).expectation (fun primary => inverseDensity security scalar primary center) = 0 := by
  rw [show (fun primary => inverseDensity security scalar primary center) =
    densityInverse security (fun color => seedDensity security scalar color center) from rfl,
    densityInverse_mean, seedDensity_centered_primary, mul_zero]

theorem inverseDensity_centered_body (security : ℕ) (scalar : MarkedPairSeed.Scalar security) (primary : ActualControls.Palette security) :
    (bodyReference security).expectation (inverseDensity security scalar primary) = 0 := by
  have hsum : (∑ center, (bodyReference security).weight center •
      (fun color => seedDensity security scalar color center)) = 0 := by
    funext color
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, FiniteDist.expectation] using seedDensity_centered_body security scalar color
  have heq : (bodyReference security).expectation (inverseDensity security scalar primary) =
      densityInverse security (∑ center, (bodyReference security).weight center •
        (fun color => seedDensity security scalar color center)) primary := by
    simp only [FiniteDist.expectation, inverseDensity, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq, hsum, map_zero]
  rfl



theorem inverseDensity_energy (security : ℕ) (scalar : MarkedPairSeed.Scalar security) :
    mixedEnergy (primaryLaw security) (bodyReference security) (inverseDensity security scalar) ≤
      (2 / activation security) ^ 2 * (12 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security) := by
  rw [mixedEnergy_fibers]
  calc
    _ ≤ ∑ center, (bodyReference security).weight center *
        ((2 / activation security) ^ 2 * (primaryLaw security).l2Sq (fun primary => seedDensity security scalar primary center)) :=
      Finset.sum_le_sum fun center _ => mul_le_mul_of_nonneg_left
        (densityInverse_energy security _) ((bodyReference security).nonneg center)
    _ = (2 / activation security) ^ 2 * mixedEnergy (primaryLaw security) (bodyReference security) (seedDensity security scalar) := by
      rw [mixedEnergy_fibers]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro center _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (seedDensity_energy security scalar) (sq_nonneg _)

theorem inverseDensity_norm_growth (security : ℕ) (scalar : MarkedPairSeed.Scalar security) :
    Real.sqrt (mixedEnergy (primaryLaw security) (bodyReference security) (inverseDensity security scalar)) ≤
      16384 * (Parameters.base security : ℝ) ^ 9 := by
  have hb := FirstResponse.base_pos security
  have ha := activation_pos security
  have hA : (0 : ℝ) < Parameters.anchorWidth security := Nat.cast_pos.mpr (InwardAnchor.anchorWidth_pos security)
  have hq : (Parameters.modulus security : ℝ) ≤ 131072 * (Parameters.base security : ℝ) ^ 64 := by
    exact_mod_cast (Parameters.modulus_bounds security).2
  have hinv : 2 / activation security ≤ 8 * (Parameters.base security : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (activation_inverse_le security) (show (0 : ℝ) ≤ 2 by norm_num)
    convert h using 1 <;> first | rfl | ring
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ (2 / activation security) ^ 2 * (12 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security) :=
      inverseDensity_energy security scalar
    _ ≤ (8 * (Parameters.base security : ℝ)) ^ 2 *
        (12 * (131072 * (Parameters.base security : ℝ) ^ 64) / Parameters.anchorWidth security) :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hinv 2)
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hq (by norm_num)) hA.le)
        (by positivity) (by positivity)
    _ = 100663296 * (Parameters.base security : ℝ) ^ 18 := by
      rw [anchorWidth_eq, Nat.cast_pow]
      field_simp
      ring
    _ ≤ _ := by
      have hh : (0 : ℝ) ≤ (Parameters.base security : ℝ) ^ 18 := pow_nonneg hb.le _
      nlinarith

def mixedArity (order : ℕ) (horder : 2 ≤ order) : TruncatedArity order :=
  ⟨(⟨1, by omega⟩, ⟨1, by omega⟩), by simpa⟩

def markedMixedCertificate (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) : ActualFamily security order :=
  Pi.single (mixedArity order horder) (mixedKernel (primaryLaw security) (bodyReference security) (inverseDensity security scalar)
    (inverseDensity_centered_primary security scalar) (inverseDensity_centered_body security scalar))

theorem markedMixedCertificate_norm (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (markedMixedCertificate security order horder scalar) ≤ 16384 / (Parameters.base security : ℝ) ^ 134 := by
  have hb := FirstResponse.base_pos security
  have hpf : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hbf : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  rw [markedMixedCertificate, familyNorm_single, mixedKernel_blockL2]
  simp only [mixedArity, gradeWeight, pow_one]
  calc
    _ ≤ (1 / (Parameters.base security : ℝ) ^ 64) * (1 / (Parameters.base security : ℝ) ^ 79) *
        (16384 * (Parameters.base security : ℝ) ^ 9) :=
      mul_le_mul (mul_le_mul (le_of_eq (primaryFactor_eq security)) (bodyFactor_le security) hbf (by positivity))
        (inverseDensity_norm_growth security scalar) (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by field_simp



end

end CurrentAFT.MarkedPairCertificates

end

section










/-! Exact leading mass of the fixed-scalar marked mixed certificate. -/

namespace CurrentAFT.MarkedPairLeading

open AFT AFT.SafePair DiffuseProfiles ProposalPrimary ActualControls FirstResponse FringeCertificate
  BackgroundCertificates BackgroundTranslations MarkedPairSeed MarkedPairCertificates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ProposalPrimary.centerLaw
  ActualControls.bodyReference InwardAnchor.shiftedAnchorLaw DiffuseProfiles.actualSeedLaw

def paletteAnchor (security : ℕ) (scalar : MarkedPairSeed.Scalar security) (primary : ActualControls.Palette security) :
    FiniteDist (ActualControls.Palette security) :=
  InwardAnchor.shiftedAnchorLaw security primary (-scalar.val)
    (by simpa only [abs_neg] using InwardAnchor.scalar_bound security scalar)

def anchorMean (security : ℕ) (scalar : MarkedPairSeed.Scalar security) : FiniteDist (ActualControls.Palette security) :=
  (primaryLaw security).mix (paletteAnchor security scalar)

def seedProfile (security : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary center : ActualControls.Palette security) : ℝ :=
  (primaryLaw security).weight primary * (paletteAnchor security scalar primary).weight center -
    uniformProfile security primary * (anchorMean security scalar).weight center -
    (primaryLaw security).weight primary * (centerLaw security).weight center +
    uniformProfile security primary * (centerLaw security).weight center







def bodyConvolution (security : ℕ) : Module.End ℝ (ActualControls.Palette security → ℝ) where
  toFun := rootConvolutionProfile security
  map_add' first second := by
    funext output
    simp only [rootConvolutionProfile, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' scalar profile := by
    funext output
    simp only [rootConvolutionProfile, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro seed _
    ring









def mixedSeedProfile {Color : Type*} [Fintype Color]
    (primary body uniform : FiniteDist Color) (anchor : Color → FiniteDist Color) (first second : Color) : ℝ :=
  primary.weight first * (anchor first).weight second - uniform.weight first * (primary.mix anchor).weight second -
    primary.weight first * body.weight second + uniform.weight first * body.weight second





end

end CurrentAFT.MarkedPairLeading

end

section










/-! Concrete first-primary certificate for the actual primary-minus-uniform mass. -/

namespace CurrentAFT.PrimaryDeviationCertificate

open AFT ControlCoordinates GradedControlNorm DiffuseProfiles ProposalPrimary ActualControls FirstResponse
  FringeCertificate BackgroundRates PrimaryTensorInverse PrimaryMassFamilies BackgroundFamilies
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference BackgroundRates.primaryFactor

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def deviation (security : ℕ) : ActualControls.Palette security → ℝ :=
  (primaryLaw security).weight - uniformProfile security

theorem deviation_mass (security : ℕ) : ∑ color, deviation security color = 0 := by
  have hq := (FirstResponse.modulus_pos security).ne'
  simp only [deviation, Pi.sub_apply, uniformProfile, Finset.sum_sub_distrib, FiniteDist.sum_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  norm_num

theorem deviation_energy (security : ℕ) : profileSquareNorm (primaryLaw security).weight (deviation security) ≤ 6 := by
  have hself : profileSquareNorm (primaryLaw security).weight (primaryLaw security).weight = 1 := by
    unfold profileSquareNorm
    have hpoint (color : ActualControls.Palette security) :
        (primaryLaw security).weight color ^ 2 / (primaryLaw security).weight color = (primaryLaw security).weight color := by
      field_simp [(primaryReference_positive security color).ne']
    simp only [hpoint, FiniteDist.sum_one]
  have h := profileSquareNorm_sub_le_two security (primaryLaw security).weight (uniformProfile security)
  rw [hself] at h
  exact h.trans (by linarith [uniformProfile_square_le_two security])

def certificate (security order : ℕ) (horder : 1 ≤ order) : ActualFamily security order :=
  massCertificateFamily security order 1 horder (oneWordProfile (deviation security))
    (oneWordProfile_centered _ (deviation_mass security)) (oneWordProfile_symmetric _)



theorem certificate_norm (security order : ℕ) (horder : 1 ≤ order) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (certificate security order horder) ≤ 24 / (Parameters.base security : ℝ) ^ 63 := by
  have hb := FirstResponse.base_pos security
  have ha := activation_pos security
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hinv : 2 / activation security ≤ 8 * (Parameters.base security : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (activation_inverse_le security) (show (0 : ℝ) ≤ 2 by norm_num)
    convert h using 1 <;> first | rfl | ring
  have henergyEq : massEnergy security 1 (oneWordProfile (deviation security)) =
      profileSquareNorm (primaryLaw security).weight (deviation security) :=
    oneWordProfile_energy (primaryLaw security).weight (deviation security)
  have henergy : massEnergy security 1 (oneWordProfile (deviation security)) ≤ 6 :=
    henergyEq.le.trans (deviation_energy security)
  have hsqrt : Real.sqrt (massEnergy security 1 (oneWordProfile (deviation security))) ≤ 3 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, henergy.trans (by norm_num)⟩
  have h := massCertificateFamily_norm security order 1 horder (primaryFactor security) (bodyFactor security) hp
    (oneWordProfile (deviation security)) (oneWordProfile_centered _ (deviation_mass security)) (oneWordProfile_symmetric _)
  simp only [pow_one] at h
  calc
    _ ≤ primaryFactor security * (2 / activation security) * Real.sqrt (massEnergy security 1 (oneWordProfile (deviation security))) := h
    _ ≤ (1 / (Parameters.base security : ℝ) ^ 64) * (8 * (Parameters.base security : ℝ)) * 3 :=
      mul_le_mul (mul_le_mul (le_of_eq (primaryFactor_eq security)) hinv (by positivity) (by positivity))
        hsqrt (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by field_simp; norm_num

end

end CurrentAFT.PrimaryDeviationCertificate

end

section












/-! Complete fixed-scalar quadratic pair certificates in the actual family algebra. -/

namespace CurrentAFT.PairQuadraticFamilies

open AFT GradedControlAlgebra GradedControlNorm GradedControlStability
  DiffuseProfiles ProposalPrimary ActualControls BackgroundRates BackgroundFamilies
  MarkedPairCertificates PrimaryDeviationCertificate DiffusePairCertificates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
  BackgroundRates.primaryFactor BackgroundRates.bodyFactor

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def markedPairCertificate (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    ActualFamily security order :=
  markedMixedCertificate security order horder scalar +
    familyProduct (primaryLaw security) (bodyReference security) order
      (certificate security order (by omega)) (freeCertificate security order (by omega))

theorem markedPairCertificate_norm (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (markedPairCertificate security order horder scalar) ≤ 18400 / (Parameters.base security : ℝ) ^ 134 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hbdy : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  have hprod := familyNorm_product_le (primaryLaw security) (bodyReference security) order
    (primaryFactor security) (bodyFactor security) hp hbdy
    (certificate security order (by omega)) (freeCertificate security order (by omega))
  have hbound : familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (familyProduct (primaryLaw security) (bodyReference security) order
        (certificate security order (by omega)) (freeCertificate security order (by omega))) ≤
      (24 / (Parameters.base security : ℝ) ^ 63) * (84 / (Parameters.base security : ℝ) ^ 110) := by
    exact hprod.trans (mul_le_mul (certificate_norm security order (by omega))
      (freeCertificate_norm_decay security order (by omega))
      (familyNorm_nonneg _ _ _ _ _ hp hbdy _) (by positivity))
  calc
    _ ≤ familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
          (markedMixedCertificate security order horder scalar) +
        familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
          (familyProduct (primaryLaw security) (bodyReference security) order
            (certificate security order (by omega)) (freeCertificate security order (by omega))) :=
      familyNorm_add_le _ _ _ _ _ hp hbdy _ _
    _ ≤ 16384 / (Parameters.base security : ℝ) ^ 134 +
        (24 / (Parameters.base security : ℝ) ^ 63) * (84 / (Parameters.base security : ℝ) ^ 110) :=
      add_le_add (markedMixedCertificate_norm security order horder scalar) hbound
    _ = 16384 / (Parameters.base security : ℝ) ^ 134 + 2016 / (Parameters.base security : ℝ) ^ 173 := by ring
    _ ≤ 16384 / (Parameters.base security : ℝ) ^ 134 + 2016 / (Parameters.base security : ℝ) ^ 134 :=
      add_le_add le_rfl (div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _)
        (pow_le_pow_right₀ hb1 (by omega)))
    _ = _ := by ring

def pairQuadraticCertificate (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    ActualFamily security order :=
  (1 - activation security) • diffuseCertificate security order horder scalar.val +
    activation security • markedPairCertificate security order horder scalar

theorem pairQuadraticCertificate_norm (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (pairQuadraticCertificate security order horder scalar) ≤ 406880 / (Parameters.base security : ℝ) ^ 134 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hbdy : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  have ha := activation_pos security
  have haHalf := activation_le_half security
  have hdiff : familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (diffuseCertificate security order horder scalar.val) ≤ 388480 / (Parameters.base security : ℝ) ^ 134 := by
    exact (diffuseCertificate_norm security order horder scalar.val
      ((InwardAnchor.scalar_bound security scalar).trans (by omega))).trans
        (div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _) (pow_le_pow_right₀ hb1 (by omega)))
  calc
    _ ≤ familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
          ((1 - activation security) • diffuseCertificate security order horder scalar.val) +
        familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
          (activation security • markedPairCertificate security order horder scalar) :=
      familyNorm_add_le _ _ _ _ _ hp hbdy _ _
    _ = (1 - activation security) * familyNorm (primaryLaw security) (bodyReference security) order
          (primaryFactor security) (bodyFactor security) (diffuseCertificate security order horder scalar.val) +
        activation security * familyNorm (primaryLaw security) (bodyReference security) order
          (primaryFactor security) (bodyFactor security) (markedPairCertificate security order horder scalar) := by
      rw [familyNorm_smul, familyNorm_smul, abs_of_nonneg (by linarith : 0 ≤ 1 - activation security), abs_of_pos ha]
    _ ≤ 388480 / (Parameters.base security : ℝ) ^ 134 + 18400 / (Parameters.base security : ℝ) ^ 134 := by
      apply add_le_add
      · exact (mul_le_mul_of_nonneg_left hdiff (by linarith)).trans (by nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 388480) (pow_nonneg hb.le 134)])
      · exact (mul_le_mul_of_nonneg_left (markedPairCertificate_norm security order horder scalar) ha.le).trans
          (by nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 18400) (pow_nonneg hb.le 134)])
    _ = _ := by ring



end

end CurrentAFT.PairQuadraticFamilies

end

section








namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.ActualPairBridge
end CurrentAFT.ActualPairBridge
namespace CurrentAFT.DiffusePair
end CurrentAFT.DiffusePair
namespace CurrentAFT.DiffusePair.pairBlur
end CurrentAFT.DiffusePair.pairBlur
namespace CurrentAFT.DiffusePair.pairSeedLaw
end CurrentAFT.DiffusePair.pairSeedLaw
namespace CurrentAFT.DiffusePair.pairStart
end CurrentAFT.DiffusePair.pairStart
namespace CurrentAFT.LocalReferenceEnergy
end CurrentAFT.LocalReferenceEnergy
namespace CurrentAFT.LocalReferenceEnergy.diffusePairAt
end CurrentAFT.LocalReferenceEnergy.diffusePairAt
namespace CurrentAFT.LocalReferenceEnergy.publicBlurLaw
end CurrentAFT.LocalReferenceEnergy.publicBlurLaw
namespace CurrentAFT.LocalReferenceEnergy.signedDiffusePair
end CurrentAFT.LocalReferenceEnergy.signedDiffusePair
namespace CurrentAFT.LocalReferenceEnergy.signedMarkedPair
end CurrentAFT.LocalReferenceEnergy.signedMarkedPair
namespace CurrentAFT.ProposalSymmetry
end CurrentAFT.ProposalSymmetry
namespace CurrentAFT.ProposalSymmetry.directionLaw
end CurrentAFT.ProposalSymmetry.directionLaw



/-!
# Complete same-scalar leg background families

The fixed leg scalar is shared by its off-body pair and attachment before
their coefficient products are formed. Only the complete quadratic and
cubic coefficients are averaged. The linear coefficient uses the exact
baseline-balanced recipe, preserving cancellation with the free population.
-/

namespace CurrentAFT.LegBackgroundFamilies

open AFT GradedControlAlgebra GradedControlNorm GradedControlStability
  DiffuseProfiles ProposalPrimary ActualControls BackgroundRates BackgroundFamilies
  BackgroundLinear PairQuadraticFamilies
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount ProposalPrimary.primaryLaw ActualControls.bodyReference
  BackgroundRates.primaryFactor BackgroundRates.bodyFactor BackgroundFamilies.freeCertificate
  BackgroundFamilies.translationCertificate BackgroundLinear.legLinearCertificate
  PairQuadraticFamilies.pairQuadraticCertificate ConditionalPairLinear.certificate

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def conditionalQuadratic (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    ActualFamily security order :=
  pairQuadraticCertificate security order horder scalar +
    ConditionalPairLinear.certificate security order (by omega) scalar *
      translationCertificate security order (by omega) scalar.val

def conditionalCubic (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    ActualFamily security order :=
  pairQuadraticCertificate security order horder scalar * translationCertificate security order (by omega) scalar.val

def legQuadratic (security order : ℕ) (horder : 2 ≤ order) : ActualFamily security order :=
  ∑ scalar, (scalarLaw security).weight scalar • conditionalQuadratic security order horder scalar

def legCubic (security order : ℕ) (horder : 2 ≤ order) : ActualFamily security order :=
  ∑ scalar, (scalarLaw security).weight scalar • conditionalCubic security order horder scalar

def completeLegAtom (security order : ℕ) (horder : 2 ≤ order) : ActualFamily security order :=
  legLinearCertificate security order (by omega) + legQuadratic security order horder + legCubic security order horder

theorem certificateNorm_product (security order : ℕ) (first second : ActualFamily security order) :
    certificateNorm security order (first * second) ≤ certificateNorm security order first * certificateNorm security order second := by
  apply familyNorm_product_le
  · unfold primaryFactor
    positivity
  · unfold bodyFactor radius
    positivity

theorem conditionalQuadratic_norm (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    certificateNorm security order (conditionalQuadratic security order horder scalar) ≤
      2241888 / (Parameters.base security : ℝ) ^ 134 := by
  have hb := FirstResponse.base_pos security
  have hprod := (certificateNorm_product security order
    (ConditionalPairLinear.certificate security order (by omega) scalar)
    (translationCertificate security order (by omega) scalar.val)).trans
      (mul_le_mul (ConditionalPairLinear.certificate_norm security order (by omega) scalar)
        (translationCertificate_norm_decay security order (by omega) scalar.val)
        (certificateNorm_nonneg security order _) (by positivity))
  calc
    _ ≤ certificateNorm security order (pairQuadraticCertificate security order horder scalar) +
        certificateNorm security order (ConditionalPairLinear.certificate security order (by omega) scalar *
          translationCertificate security order (by omega) scalar.val) := certificateNorm_add security order _ _
    _ ≤ 406880 / (Parameters.base security : ℝ) ^ 134 +
        (32768 / (Parameters.base security : ℝ) ^ 55) * (56 / (Parameters.base security : ℝ) ^ 79) :=
      add_le_add (pairQuadraticCertificate_norm security order horder scalar) hprod
    _ = _ := by ring

theorem conditionalCubic_norm (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    certificateNorm security order (conditionalCubic security order horder scalar) ≤
      22785280 / (Parameters.base security : ℝ) ^ 213 := by
  have hb := FirstResponse.base_pos security
  calc
    _ ≤ certificateNorm security order (pairQuadraticCertificate security order horder scalar) *
        certificateNorm security order (translationCertificate security order (by omega) scalar.val) :=
      certificateNorm_product security order _ _
    _ ≤ (406880 / (Parameters.base security : ℝ) ^ 134) * (56 / (Parameters.base security : ℝ) ^ 79) :=
      mul_le_mul (pairQuadraticCertificate_norm security order horder scalar)
        (translationCertificate_norm_decay security order (by omega) scalar.val)
        (certificateNorm_nonneg security order _) (by positivity)
    _ = _ := by ring

theorem legQuadratic_norm (security order : ℕ) (horder : 2 ≤ order) :
    certificateNorm security order (legQuadratic security order horder) ≤
      2241888 / (Parameters.base security : ℝ) ^ 134 :=
  certificateNorm_average_le security order (scalarLaw security) _ _ (conditionalQuadratic_norm security order horder)

theorem legCubic_norm (security order : ℕ) (horder : 2 ≤ order) :
    certificateNorm security order (legCubic security order horder) ≤
      22785280 / (Parameters.base security : ℝ) ^ 213 :=
  certificateNorm_average_le security order (scalarLaw security) _ _ (conditionalCubic_norm security order horder)

theorem legQuadratic_population_bound (security order : ℕ) (horder : 2 ≤ order) :
    (Parameters.legCount security : ℝ) * certificateNorm security order (legQuadratic security order horder) ≤
      2241888 / (Parameters.base security : ℝ) ^ 6 := by
  have hb := FirstResponse.base_pos security
  calc
    _ ≤ (Parameters.legCount security : ℝ) * (2241888 / (Parameters.base security : ℝ) ^ 134) :=
      mul_le_mul_of_nonneg_left (legQuadratic_norm security order horder) (Nat.cast_nonneg _)
    _ = _ := by rw [Parameters.legCount_eq, Nat.cast_pow]; field_simp

theorem legCubic_population_bound (security order : ℕ) (horder : 2 ≤ order) :
    (Parameters.legCount security : ℝ) * certificateNorm security order (legCubic security order horder) ≤
      22785280 / (Parameters.base security : ℝ) ^ 85 := by
  have hb := FirstResponse.base_pos security
  calc
    _ ≤ (Parameters.legCount security : ℝ) * (22785280 / (Parameters.base security : ℝ) ^ 213) :=
      mul_le_mul_of_nonneg_left (legCubic_norm security order horder) (Nat.cast_nonneg _)
    _ = _ := by rw [Parameters.legCount_eq, Nat.cast_pow]; field_simp

theorem completeLegAtom_norm (security order : ℕ) (horder : 2 ≤ order) :
    certificateNorm security order (completeLegAtom security order horder) ≤
      43377248 / (Parameters.base security : ℝ) ^ 78 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  calc
    _ ≤ certificateNorm security order (legLinearCertificate security order (by omega) + legQuadratic security order horder) +
        certificateNorm security order (legCubic security order horder) := certificateNorm_add security order _ _
    _ ≤ certificateNorm security order (legLinearCertificate security order (by omega)) +
        certificateNorm security order (legQuadratic security order horder) +
        certificateNorm security order (legCubic security order horder) :=
      add_le_add (certificateNorm_add security order _ _) le_rfl
    _ ≤ 18350080 / (Parameters.base security : ℝ) ^ 78 + 2241888 / (Parameters.base security : ℝ) ^ 134 +
        22785280 / (Parameters.base security : ℝ) ^ 213 :=
      add_le_add (add_le_add (legLinearCertificate_norm_decay security order (by omega)) (legQuadratic_norm security order horder))
        (legCubic_norm security order horder)
    _ ≤ 18350080 / (Parameters.base security : ℝ) ^ 78 + 2241888 / (Parameters.base security : ℝ) ^ 78 +
        22785280 / (Parameters.base security : ℝ) ^ 78 := by
      exact add_le_add (add_le_add le_rfl (div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _)
        (pow_le_pow_right₀ hb1 (by omega)))) (div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _)
          (pow_le_pow_right₀ hb1 (by omega)))
    _ = _ := by ring

theorem completeLegAtom_square_population (security order : ℕ) (horder : 2 ≤ order) :
    (Parameters.legCount security : ℝ) * certificateNorm security order (completeLegAtom security order horder) ^ 2 ≤
      1881585644053504 / (Parameters.base security : ℝ) ^ 28 := by
  have hb := FirstResponse.base_pos security
  have hs := pow_le_pow_left₀ (certificateNorm_nonneg security order _) (completeLegAtom_norm security order horder) 2
  calc
    _ ≤ (Parameters.legCount security : ℝ) * (43377248 / (Parameters.base security : ℝ) ^ 78) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
    _ = _ := by rw [Parameters.legCount_eq, Nat.cast_pow]; field_simp; ring

end

end CurrentAFT.LegBackgroundFamilies

end

section










/-! The complete concrete background atoms have exactly zero scalar coefficient. -/

namespace CurrentAFT.BackgroundScalarZero

open AFT ControlCoordinates GradedControlAlgebra GradedInverse DiffuseProfiles ProposalPrimary ActualControls
  BackgroundFamilies BackgroundLinear PairCertificateFamilies PrimaryMassFamilies
  DiffusePairCertificates MarkedPairCertificates PairQuadraticFamilies LegBackgroundFamilies
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

theorem positive_single_zero (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (arity : TruncatedArity order) (hpositive : 0 < arity.val.1.val + arity.val.2.val)
    (kernel : canonicalKernels primary body arity.val.1.val arity.val.2.val) :
    (Pi.single arity kernel : KernelFamily primary body order) (zeroArity order) = 0 := by
  apply Pi.single_eq_of_ne
  intro hequal
  have hdegree := congrArg (fun arity : TruncatedArity order => arity.val.1.val + arity.val.2.val) hequal
  have hzero : (zeroArity order).val.1.val + (zeroArity order).val.2.val = 0 := by simp [zeroArity]
  omega

theorem product_zero (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first second : KernelFamily primary body order) (hfirst : first (zeroArity order) = 0) :
    (first * second) (zeroArity order) = 0 := by
  have h := vanishesBelow_mul primary body order 1 0 first second
    (vanishesBelow_one_of_zero primary body order first hfirst) (vanishesBelow_zero primary body order second)
  exact h (zeroArity order) (by simp [zeroArity])

theorem primaryFamily_zero (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) (horder : 1 ≤ order)
    (density : Primary → ℝ) (hcenter : ∑ color, primary.weight color * density color = 0) :
    primaryFamily primary body order horder density hcenter (zeroArity order) = 0 := by
  unfold primaryFamily
  apply positive_single_zero
  simp [BackgroundFamilies.primaryArity]

theorem bodyFamily_zero (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) (horder : 1 ≤ order)
    (density : Body → ℝ) (hcenter : ∑ color, body.weight color * density color = 0) :
    bodyFamily primary body order horder density hcenter (zeroArity order) = 0 := by
  unfold bodyFamily
  apply positive_single_zero
  simp [bodyArity]

theorem freeCertificate_zero (security order : ℕ) (horder : 1 ≤ order) :
    freeCertificate security order horder (zeroArity order) = 0 := by
  simp only [freeCertificate, Pi.add_apply, primaryFamily_zero, bodyFamily_zero, add_zero]

theorem translationCertificate_zero (security order : ℕ) (horder : 1 ≤ order) (shift : ℤ) :
    translationCertificate security order horder shift (zeroArity order) = 0 := by
  simp only [translationCertificate, Pi.add_apply, primaryFamily_zero, bodyFamily_zero, add_zero]

theorem meanTranslation_zero (security order : ℕ) (horder : 1 ≤ order) :
    meanTranslation security order horder (zeroArity order) = 0 := by
  simp only [meanTranslation, Finset.sum_apply, Pi.smul_apply, translationCertificate_zero, smul_zero, Finset.sum_const_zero]

theorem legLinearCertificate_zero (security order : ℕ) (horder : 1 ≤ order) :
    legLinearCertificate security order horder (zeroArity order) = 0 := by
  simp only [legLinearCertificate, Pi.smul_apply, Pi.add_apply, freeCertificate_zero, meanTranslation_zero, smul_zero, add_zero]

theorem massCertificateFamily_zero (security order degree : ℕ) (hdegree : degree ≤ order) (hpositive : 0 < degree)
    (profile : (Fin degree → ActualControls.Palette security) → ℝ)
    (hcentered : PrimaryTensorInverse.MassCentered degree profile)
    (hsymmetric : ∀ (permutation : Equiv.Perm (Fin degree)) word, profile (word ∘ permutation) = profile word) :
    massCertificateFamily security order degree hdegree profile hcentered hsymmetric (zeroArity order) = 0 := by
  unfold massCertificateFamily
  apply positive_single_zero
  simpa [PrimaryMassFamilies.primaryArity] using hpositive

theorem diffuseBodyCertificate_zero (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ) :
    diffuseBodyCertificate security order horder scalar (zeroArity order) = 0 := by
  unfold diffuseBodyCertificate
  apply positive_single_zero
  simp [bodyPairArity]

theorem diffusePrimaryCertificate_zero (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ) :
    diffusePrimaryCertificate security order horder scalar (zeroArity order) = 0 := by
  unfold diffusePrimaryCertificate
  exact massCertificateFamily_zero _ _ _ _ (by omega) _ _ _

theorem diffuseCertificate_zero (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ) :
    diffuseCertificate security order horder scalar (zeroArity order) = 0 := by
  simp only [diffuseCertificate, Pi.add_apply, diffuseBodyCertificate_zero, diffusePrimaryCertificate_zero, add_zero]

theorem markedMixedCertificate_zero (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    markedMixedCertificate security order horder scalar (zeroArity order) = 0 := by
  unfold markedMixedCertificate
  apply positive_single_zero
  simp [mixedArity]

theorem primaryDeviationCertificate_zero (security order : ℕ) (horder : 1 ≤ order) :
    PrimaryDeviationCertificate.certificate security order horder (zeroArity order) = 0 := by
  unfold PrimaryDeviationCertificate.certificate
  exact massCertificateFamily_zero _ _ _ _ (by omega) _ _ _

theorem markedPairCertificate_zero (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    markedPairCertificate security order horder scalar (zeroArity order) = 0 := by
  change markedMixedCertificate security order horder scalar (zeroArity order) +
    (PrimaryDeviationCertificate.certificate security order (by omega) * freeCertificate security order (by omega)) (zeroArity order) = 0
  rw [markedMixedCertificate_zero, product_zero _ _ _ _ _ (primaryDeviationCertificate_zero security order (by omega)), add_zero]

theorem pairQuadraticCertificate_zero (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    pairQuadraticCertificate security order horder scalar (zeroArity order) = 0 := by
  simp only [pairQuadraticCertificate, Pi.add_apply, Pi.smul_apply, diffuseCertificate_zero,
    markedPairCertificate_zero, smul_zero, add_zero]

theorem conditionalPairLinear_zero (security order : ℕ) (horder : 1 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    ConditionalPairLinear.certificate security order horder scalar (zeroArity order) = 0 := by
  unfold ConditionalPairLinear.certificate
  exact massCertificateFamily_zero _ _ _ _ (by omega) _ _ _

theorem conditionalQuadratic_zero (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    conditionalQuadratic security order horder scalar (zeroArity order) = 0 := by
  change pairQuadraticCertificate security order horder scalar (zeroArity order) +
    (ConditionalPairLinear.certificate security order (by omega) scalar *
      translationCertificate security order (by omega) scalar.val) (zeroArity order) = 0
  rw [pairQuadraticCertificate_zero, product_zero _ _ _ _ _ (conditionalPairLinear_zero security order (by omega) scalar), add_zero]

theorem conditionalCubic_zero (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    conditionalCubic security order horder scalar (zeroArity order) = 0 := by
  exact product_zero _ _ _ _ _ (pairQuadraticCertificate_zero security order horder scalar)

theorem legQuadratic_zero (security order : ℕ) (horder : 2 ≤ order) :
    legQuadratic security order horder (zeroArity order) = 0 := by
  simp only [legQuadratic, Finset.sum_apply, Pi.smul_apply, conditionalQuadratic_zero, smul_zero, Finset.sum_const_zero]

theorem legCubic_zero (security order : ℕ) (horder : 2 ≤ order) :
    legCubic security order horder (zeroArity order) = 0 := by
  simp only [legCubic, Finset.sum_apply, Pi.smul_apply, conditionalCubic_zero, smul_zero, Finset.sum_const_zero]

theorem completeLegAtom_zero (security order : ℕ) (horder : 2 ≤ order) :
    completeLegAtom security order horder (zeroArity order) = 0 := by
  simp only [completeLegAtom, Pi.add_apply, legLinearCertificate_zero, legQuadratic_zero, legCubic_zero, add_zero]

end

end CurrentAFT.BackgroundScalarZero

end

section








/-! Actual full-background first-sum and square-population budgets. -/

namespace CurrentAFT.BackgroundPopulationBounds

open AFT GradedControlAlgebra GradedControlNorm GradedControlStability
  DiffuseProfiles ProposalPrimary ActualControls BackgroundRates BackgroundFamilies
  BackgroundLinear LegBackgroundFamilies
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount ProposalPrimary.primaryLaw ActualControls.bodyReference
  BackgroundFamilies.freeCertificate BackgroundFamilies.translationCertificate BackgroundLinear.legLinearCertificate
  LegBackgroundFamilies.completeLegAtom LegBackgroundFamilies.legQuadratic LegBackgroundFamilies.legCubic

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def freeCount (security : ℕ) : ℕ := Parameters.bodySize security - Parameters.legCount security - Parameters.modulus security

theorem freeCount_cast (security : ℕ) : (freeCount security : ℝ) = freeMass security := by
  have hroom := population_room security
  unfold freeCount freeMass
  rw [Nat.cast_sub (by omega : Parameters.modulus security ≤ Parameters.bodySize security - Parameters.legCount security),
    Nat.cast_sub (by omega : Parameters.legCount security ≤ Parameters.bodySize security)]

theorem fixedQueueLinear_norm (security order : ℕ) (horder : 1 ≤ order) (queueShift : ℤ) :
    certificateNorm security order (fixedQueueLinear security order horder queueShift) ≤
      14680064 / (Parameters.base security : ℝ) ^ 15 := by
  have hb := FirstResponse.base_pos security
  have hq : (0 : ℝ) ≤ Parameters.modulus security := Nat.cast_nonneg _
  have hqu : (Parameters.modulus security : ℝ) ≤ 131072 * (Parameters.base security : ℝ) ^ 64 := by
    exact_mod_cast (Parameters.modulus_bounds security).2
  have hsub := certificateNorm_add security order (translationCertificate security order horder queueShift)
    (-meanTranslation security order horder)
  have hneg : certificateNorm security order (-meanTranslation security order horder) =
      certificateNorm security order (meanTranslation security order horder) := familyNorm_neg _ _ _ _ _ _
  rw [hneg] at hsub
  rw [fixedQueueLinear_eq, certificateNorm_smul, abs_of_nonneg hq]
  calc
    _ ≤ (Parameters.modulus security : ℝ) *
        (certificateNorm security order (translationCertificate security order horder queueShift) +
          certificateNorm security order (meanTranslation security order horder)) :=
      mul_le_mul_of_nonneg_left hsub hq
    _ ≤ (131072 * (Parameters.base security : ℝ) ^ 64) *
        (56 / (Parameters.base security : ℝ) ^ 79 + 56 / (Parameters.base security : ℝ) ^ 79) :=
      mul_le_mul hqu (add_le_add (translationCertificate_norm_decay security order horder queueShift)
        (meanTranslation_norm security order horder))
        (add_nonneg (certificateNorm_nonneg security order _) (certificateNorm_nonneg security order _)) (by positivity)
    _ = _ := by field_simp; ring

def combinedFirstSum (security order : ℕ) (horder : 2 ≤ order) (queueShift : ℤ) : ActualFamily security order :=
  freeMass security • freeCertificate security order (by omega) +
    (Parameters.modulus security : ℝ) • translationCertificate security order (by omega) queueShift +
    (Parameters.legCount security : ℝ) • completeLegAtom security order horder

theorem combinedFirstSum_eq (security order : ℕ) (horder : 2 ≤ order) (queueShift : ℤ) :
    combinedFirstSum security order horder queueShift =
      fixedQueueLinear security order (by omega) queueShift +
        (Parameters.legCount security : ℝ) • legQuadratic security order horder +
        (Parameters.legCount security : ℝ) • legCubic security order horder := by
  unfold combinedFirstSum fixedQueueLinear completeLegAtom
  rw [smul_add, smul_add]
  abel

theorem combinedFirstSum_norm (security order : ℕ) (horder : 2 ≤ order) (queueShift : ℤ) :
    certificateNorm security order (combinedFirstSum security order horder queueShift) ≤
      39707232 / (Parameters.base security : ℝ) ^ 6 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  rw [combinedFirstSum_eq]
  calc
    _ ≤ certificateNorm security order
          (fixedQueueLinear security order (by omega) queueShift + (Parameters.legCount security : ℝ) • legQuadratic security order horder) +
        certificateNorm security order ((Parameters.legCount security : ℝ) • legCubic security order horder) := certificateNorm_add security order _ _
    _ ≤ certificateNorm security order (fixedQueueLinear security order (by omega) queueShift) +
        certificateNorm security order ((Parameters.legCount security : ℝ) • legQuadratic security order horder) +
        certificateNorm security order ((Parameters.legCount security : ℝ) • legCubic security order horder) :=
      add_le_add (certificateNorm_add security order _ _) le_rfl
    _ = certificateNorm security order (fixedQueueLinear security order (by omega) queueShift) +
        (Parameters.legCount security : ℝ) * certificateNorm security order (legQuadratic security order horder) +
        (Parameters.legCount security : ℝ) * certificateNorm security order (legCubic security order horder) := by
      rw [certificateNorm_smul, certificateNorm_smul, abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ 14680064 / (Parameters.base security : ℝ) ^ 15 + 2241888 / (Parameters.base security : ℝ) ^ 6 +
        22785280 / (Parameters.base security : ℝ) ^ 85 :=
      add_le_add (add_le_add (fixedQueueLinear_norm security order (by omega) queueShift)
        (legQuadratic_population_bound security order horder)) (legCubic_population_bound security order horder)
    _ ≤ 14680064 / (Parameters.base security : ℝ) ^ 6 + 2241888 / (Parameters.base security : ℝ) ^ 6 +
        22785280 / (Parameters.base security : ℝ) ^ 6 := by
      exact add_le_add (add_le_add (div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _)
        (pow_le_pow_right₀ hb1 (by omega))) le_rfl) (div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _)
          (pow_le_pow_right₀ hb1 (by omega)))
    _ = _ := by ring

theorem free_square_population (security order : ℕ) (horder : 1 ≤ order) :
    (freeCount security : ℝ) * certificateNorm security order (freeCertificate security order horder) ^ 2 ≤
      924844032 / (Parameters.base security : ℝ) ^ 60 := by
  have hcount : (freeCount security : ℝ) ≤ Parameters.bodySize security := by
    rw [freeCount_cast]
    unfold freeMass
    have hl : (0 : ℝ) ≤ Parameters.legCount security := Nat.cast_nonneg _
    have hq : (0 : ℝ) ≤ Parameters.modulus security := Nat.cast_nonneg _
    linarith
  have hsquare := pow_le_pow_left₀ (certificateNorm_nonneg security order _) (freeCertificate_norm security order horder) 2
  calc
    _ ≤ (Parameters.bodySize security : ℝ) * freeAtomEnvelope security ^ 2 :=
      mul_le_mul hcount hsquare (sq_nonneg _) (Nat.cast_nonneg _)
    _ ≤ _ := free_population_quadratic_budget security

theorem queue_square_population (security order : ℕ) (horder : 1 ≤ order) (queueShift : ℤ) :
    (Parameters.modulus security : ℝ) * certificateNorm security order (translationCertificate security order horder queueShift) ^ 2 ≤
      411041792 / (Parameters.base security : ℝ) ^ 94 := by
  have hsquare := pow_le_pow_left₀ (certificateNorm_nonneg security order _) (translationCertificate_norm security order horder queueShift) 2
  exact (mul_le_mul_of_nonneg_left hsquare (Nat.cast_nonneg _)).trans (queue_population_quadratic_budget security queueShift)

theorem square_population (security order : ℕ) (horder : 2 ≤ order) (queueShift : ℤ) :
    (freeCount security : ℝ) * certificateNorm security order (freeCertificate security order (by omega)) ^ 2 +
      (Parameters.modulus security : ℝ) * certificateNorm security order (translationCertificate security order (by omega) queueShift) ^ 2 +
      (Parameters.legCount security : ℝ) * certificateNorm security order (completeLegAtom security order horder) ^ 2 ≤
        1881586979939328 / (Parameters.base security : ℝ) ^ 28 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  calc
    _ ≤ 924844032 / (Parameters.base security : ℝ) ^ 60 + 411041792 / (Parameters.base security : ℝ) ^ 94 +
        1881585644053504 / (Parameters.base security : ℝ) ^ 28 :=
      add_le_add (add_le_add (free_square_population security order (by omega))
        (queue_square_population security order (by omega) queueShift)) (completeLegAtom_square_population security order horder)
    _ ≤ 924844032 / (Parameters.base security : ℝ) ^ 28 + 411041792 / (Parameters.base security : ℝ) ^ 28 +
        1881585644053504 / (Parameters.base security : ℝ) ^ 28 := by
      exact add_le_add (add_le_add (div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _)
        (pow_le_pow_right₀ hb1 (by omega))) (div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _)
          (pow_le_pow_right₀ hb1 (by omega)))) le_rfl
    _ = _ := by ring

end

end CurrentAFT.BackgroundPopulationBounds

end

section










/-! # Actual root-averaged profiles for each body role and each fixed queue -/

namespace CurrentAFT.BodyRootAverages

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy FirstHistogram
  UniformBodyProfiles BackgroundCertificates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ProposalPrimary.centerLaw
  ProposalPrimary.safeLaw











def rootAverage (security : ℕ) (law : FiniteDist (LocalReferenceEnergy.Palette security)) :
    FiniteDist (LocalReferenceEnergy.Palette security) :=
  (publicBlurLaw security).mix fun pair => law.map (shiftEquiv security (pair.2.val - pair.1.val))















end

end CurrentAFT.BodyRootAverages

end

section












/-!
# The actual complete first histogram and its fixed-queue drift

Off-body means use the genuine same-scalar pair reference. The root
average contains every free body, attachment, and queue vertex. Its only
remaining imbalance at a fixed common queue value is the queue profile
minus its true scalar average.
-/

namespace CurrentAFT.HistogramMean

open AFT DiffuseProfiles ProposalPrimary FirstHistogram LocalReferenceEnergy
  ConditionalPairMean BodyRootAverages UniformBodyProfiles BackgroundCertificates
  FringeCertificate BackgroundPopulationBounds FiniteConcentration
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.dimension Parameters.bodySize Parameters.legCount
  ProposalPrimary.primaryLaw ProposalPrimary.centerLaw ProposalPrimary.safeLaw

abbrev Palette (security : ℕ) := LocalReferenceEnergy.Palette security



def offBodyMean (security : ℕ) (output : Palette security) : ℝ :=
  (scalarLaw security).expectation fun scalar => pairMean security scalar output





def queueLaw (security : ℕ) (queue : ℤ) : FiniteDist (Palette security) :=
  (bodyLaw security false).map (shiftEquiv security queue)



def rootAveragedHistogram (security : ℕ) (queue : ℤ) (output : Palette security) : ℝ :=
  freeMass security * (convolvedCenterLaw security).weight output +
    (Parameters.legCount security : ℝ) * (bodyLaw security true).weight output +
    (Parameters.modulus security : ℝ) * (queueLaw security queue).weight output +
    (Parameters.legCount security : ℝ) * offBodyMean security output



def drift (security : ℕ) (queue : ℤ) : EuclideanSpace ℝ (Palette security) :=
  NormalizedMeanAlgebra.normalizationScale security •
    ProfileHilbert.whiten (uniformReference security).weight
      (fun output => rootAveragedHistogram security queue output -
        (Parameters.dimension security : ℝ) * uniformProfile security output)











end

end CurrentAFT.HistogramMean

end

section










/-!
# Quantitative bounds for the actual finite background inverse

The inverse is the finite polynomial in `1 - background` constructed in
`GradedInverse`. Its bounds follow from the proved graded norm triangle and
submultiplicativity, with finite geometric identities. No analytic inverse,
normed-algebra structure, or assumed inverse bound is used.
-/

namespace CurrentAFT.GradedInverseNorm

open AFT ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GradedControlNorm
open GradedControlStability GradedInverse
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

theorem familyNorm_one (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) :
    familyNorm primary body order primaryFactor bodyFactor (1 : KernelFamily primary body order) = 1 := by
  unfold familyNorm
  change (∑ arity : TruncatedArity order,
    gradeWeight primaryFactor bodyFactor arity.val.1.val arity.val.2.val *
      blockL2 primary body ((familyUnit primary body order) arity).val) = 1
  unfold familyUnit
  rw [Finset.sum_eq_single (zeroArity order)]
  · rw [Pi.single_eq_same]
    change gradeWeight primaryFactor bodyFactor 0 0 * blockL2 primary body (scalarUnit primary body).val = 1
    have hscalar : (scalarUnit primary body).val = (scalarKernel primary body 1).val := rfl
    rw [hscalar, blockL2_scalarKernel]
    simp only [gradeWeight, pow_zero, mul_one, abs_one]
  · intro arity _ hnot
    rw [Pi.single_eq_of_ne (M := fun arity : TruncatedArity order =>
      canonicalKernels primary body arity.val.1.val arity.val.2.val) hnot]
    simp only [Submodule.coe_zero, blockL2, blockEnergy_apply, Pi.zero_apply,
      zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero, Real.sqrt_zero]
  · simp

theorem familyNorm_sum_le {Index : Type*} (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    (terms : Finset Index) (family : Index → KernelFamily primary body order) :
    familyNorm primary body order primaryFactor bodyFactor (∑ index ∈ terms, family index) ≤
      ∑ index ∈ terms, familyNorm primary body order primaryFactor bodyFactor (family index) := by
  induction terms using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, familyNorm_zero, le_refl]
  | @insert index terms hnot ih =>
    rw [Finset.sum_insert hnot, Finset.sum_insert hnot]
    exact (familyNorm_add_le primary body order primaryFactor bodyFactor hprimary hbody _ _).trans
      (add_le_add le_rfl ih)

theorem familyNorm_pow_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    (family : KernelFamily primary body order) (power : ℕ) :
    familyNorm primary body order primaryFactor bodyFactor (family ^ power) ≤
      familyNorm primary body order primaryFactor bodyFactor family ^ power := by
  induction power with
  | zero => rw [pow_zero, pow_zero, familyNorm_one]
  | succ power ih =>
    rw [pow_succ, pow_succ]
    exact (familyNorm_product_le primary body order primaryFactor bodyFactor hprimary hbody _ _).trans
      (mul_le_mul_of_nonneg_right ih (familyNorm_nonneg primary body order primaryFactor bodyFactor hprimary hbody _))

 theorem finite_geometric_le (theta : ℝ) (htheta : 0 ≤ theta) (hgap : theta < 1) (terms : ℕ) :
    (∑ power ∈ Finset.range terms, theta ^ power) ≤ 1 / (1 - theta) := by
  apply (le_div_iff₀ (sub_pos.mpr hgap)).mpr
  rw [geom_sum_mul_neg]
  linarith [pow_nonneg htheta terms]

theorem backgroundInverse_norm_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    (background : KernelFamily primary body order) (theta : ℝ) (hgap : theta < 1)
    (hdefect : familyNorm primary body order primaryFactor bodyFactor (1 - background) ≤ theta) :
    familyNorm primary body order primaryFactor bodyFactor (backgroundInverse primary body order background) ≤
      1 / (1 - theta) := by
  have htheta : 0 ≤ theta :=
    (familyNorm_nonneg primary body order primaryFactor bodyFactor hprimary hbody _).trans hdefect
  unfold backgroundInverse
  calc
    _ ≤ ∑ power ∈ Finset.range (order + 1),
        familyNorm primary body order primaryFactor bodyFactor ((1 - background) ^ power) :=
      familyNorm_sum_le primary body order primaryFactor bodyFactor hprimary hbody _ _
    _ ≤ ∑ power ∈ Finset.range (order + 1), theta ^ power := by
      apply Finset.sum_le_sum
      intro power _
      exact (familyNorm_pow_le primary body order primaryFactor bodyFactor hprimary hbody _ power).trans
        (pow_le_pow_left₀ (familyNorm_nonneg primary body order primaryFactor bodyFactor hprimary hbody _) hdefect power)
    _ ≤ _ := finite_geometric_le theta htheta hgap (order + 1)

theorem backgroundInverse_sub_one (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (background : KernelFamily primary body order) :
    backgroundInverse primary body order background - 1 =
      ∑ power ∈ Finset.range order, (1 - background) ^ (power + 1) := by
  unfold backgroundInverse
  rw [Finset.sum_range_succ']
  simp only [pow_zero]
  abel

theorem backgroundInverse_correction_norm_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    (background : KernelFamily primary body order) (theta : ℝ) (hgap : theta < 1)
    (hdefect : familyNorm primary body order primaryFactor bodyFactor (1 - background) ≤ theta) :
    familyNorm primary body order primaryFactor bodyFactor (backgroundInverse primary body order background - 1) ≤
      theta / (1 - theta) := by
  have htheta : 0 ≤ theta :=
    (familyNorm_nonneg primary body order primaryFactor bodyFactor hprimary hbody _).trans hdefect
  rw [backgroundInverse_sub_one]
  calc
    _ ≤ ∑ power ∈ Finset.range order,
        familyNorm primary body order primaryFactor bodyFactor ((1 - background) ^ (power + 1)) :=
      familyNorm_sum_le primary body order primaryFactor bodyFactor hprimary hbody _ _
    _ ≤ ∑ power ∈ Finset.range order, theta ^ (power + 1) := by
      apply Finset.sum_le_sum
      intro power _
      exact (familyNorm_pow_le primary body order primaryFactor bodyFactor hprimary hbody _ (power + 1)).trans
        (pow_le_pow_left₀ (familyNorm_nonneg primary body order primaryFactor bodyFactor hprimary hbody _) hdefect _)
    _ = theta * ∑ power ∈ Finset.range order, theta ^ power := by
      simp only [pow_succ]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro power _
      ring
    _ ≤ theta * (1 / (1 - theta)) := mul_le_mul_of_nonneg_left (finite_geometric_le theta htheta hgap order) htheta
    _ = _ := by ring







end

end CurrentAFT.GradedInverseNorm

end

section








/-!
# Complete shared-queue response assembly in the actual control algebra

Every product inside each average uses the same queue state. The complete
background is averaged first, and its finite inverse is applied afterwards.
The fixed-queue response operators remain explicit arguments: the physical
construction must supply them and their quantitative estimates.
-/

namespace CurrentAFT.CommonQueueAssembly

open AFT ControlCoordinates ControlProduct GradedControlAlgebra GradedInverse
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {Primary Body Queue : Type*} [Fintype Primary] [Fintype Body] [Fintype Queue]

theorem homogeneousProduct_smul_left (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (scalar : ℝ)
    (first : canonicalKernels primary body r s) (second : canonicalKernels primary body r' s') :
    homogeneousProduct primary body (scalar • first) second =
      scalar • homogeneousProduct primary body first second := by
  have hraw : finDisjointTensor (scalar • first.val) second.val =
      scalar • finDisjointTensor first.val second.val := by
    funext colors centers
    simp only [finDisjointTensor, reindexKernel, disjointTensor, Pi.smul_apply, smul_eq_mul]
    ring
  apply Subtype.ext
  change symmetrize (finDisjointTensor (scalar • first.val) second.val) =
    scalar • symmetrize (finDisjointTensor first.val second.val)
  rw [hraw]
  exact map_smul (symmetrizeLinear) scalar _

theorem family_smul_mul (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (scalar : ℝ) (first second : KernelFamily primary body order) :
    (scalar • first) * second = scalar • (first * second) := by
  funext output
  change familyProduct primary body order (scalar • first) second output =
    scalar • familyProduct primary body order first second output
  simp only [familyProduct, Pi.smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  split_ifs with hmatch
  · rw [homogeneousProduct_smul_left, transportKernel_smul]
  · rw [smul_zero]

theorem family_mul_smul (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (scalar : ℝ) (first second : KernelFamily primary body order) :
    first * (scalar • second) = scalar • (first * second) := by
  rw [mul_comm first, family_smul_mul, mul_comm second]























end

end CurrentAFT.CommonQueueAssembly

end

section










/-!
# Finite product cancellation in the actual truncated algebra

Elementary symmetric sums of the actual positive-degree atoms satisfy
Newton's identities. Products of more atoms than the truncation order
vanish by the proved arity filtration. This gives a finite product
representation that retains cancellation of the complete linear sum,
without multiplying norms of individually unbalanced populations.
-/

namespace CurrentAFT.GradedNewton

open AFT ControlCoordinates GradedControlAlgebra GradedInverse CommonQueueAssembly
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {Primary Body Index : Type*} [Fintype Primary] [Fintype Body] [Fintype Index]

 theorem generic_newton {Ring : Type*} [CommRing Ring]
    (atoms : Index → Ring) (degree : ℕ) :
    (degree : Ring) * (∑ selected ∈ Finset.univ.powersetCard degree, ∏ index ∈ selected, atoms index) =
      (-1) ^ (degree + 1) *
        ∑ pair ∈ (Finset.HasAntidiagonal.antidiagonal degree).filter (fun pair => pair.1 < degree),
          (-1) ^ pair.1 * (∑ selected ∈ Finset.univ.powersetCard pair.1, ∏ index ∈ selected, atoms index) *
            (∑ index, atoms index ^ pair.2) := by
  let evaluation := MvPolynomial.eval₂Hom (Int.castRingHom Ring) atoms
  have h := congrArg evaluation (MvPolynomial.mul_esymm_eq_sum Index ℤ degree)
  simpa only [evaluation, map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
    MvPolynomial.esymm, MvPolynomial.psum, map_prod, MvPolynomial.eval₂Hom_X'] using h

def elementary (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (atoms : Index → KernelFamily primary body order) (degree : ℕ) : KernelFamily primary body order :=
  ∑ selected ∈ Finset.univ.powersetCard degree, ∏ index ∈ selected, atoms index

def powerSum (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (atoms : Index → KernelFamily primary body order) (power : ℕ) : KernelFamily primary body order :=
  ∑ index, atoms index ^ power

theorem elementary_zero (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (atoms : Index → KernelFamily primary body order) : elementary primary body order atoms 0 = 1 := by
  simp only [elementary, Finset.powersetCard_zero, Finset.sum_singleton, Finset.prod_empty]



/-- This identity is evaluated from the existing integer polynomial
identity, using the actual finite convolution ring, rather than assumed. -/
theorem newton_identity (primary : FiniteDist Primary) (body : FiniteDist Body) (order degree : ℕ)
    (atoms : Index → KernelFamily primary body order) :
    (degree : KernelFamily primary body order) * elementary primary body order atoms degree =
      (-1) ^ (degree + 1) *
        ∑ pair ∈ (Finset.HasAntidiagonal.antidiagonal degree).filter (fun pair => pair.1 < degree),
          (-1) ^ pair.1 * elementary primary body order atoms pair.1 *
            powerSum primary body order atoms pair.2 := by
  exact generic_newton atoms degree

omit [Fintype Index] in
theorem product_vanishesBelow (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (atoms : Index → KernelFamily primary body order)
    (hzero : ∀ index, atoms index (zeroArity order) = 0) (selected : Finset Index) :
    VanishesBelow primary body order selected.card (∏ index ∈ selected, atoms index) := by
  induction selected using Finset.induction_on with
  | empty => exact vanishesBelow_zero primary body order _
  | @insert index selected hnot ih =>
    rw [Finset.prod_insert hnot, Finset.card_insert_of_notMem hnot]
    have h := vanishesBelow_mul primary body order 1 selected.card _ _
      (vanishesBelow_one_of_zero primary body order (atoms index) (hzero index)) ih
    simpa only [Nat.add_comm 1] using h

theorem elementary_above_order (primary : FiniteDist Primary) (body : FiniteDist Body) (order degree : ℕ)
    (atoms : Index → KernelFamily primary body order)
    (hzero : ∀ index, atoms index (zeroArity order) = 0) (hdegree : order < degree) :
    elementary primary body order atoms degree = 0 := by
  unfold elementary
  apply Finset.sum_eq_zero
  intro selected hselected
  have hcard := (Finset.mem_powersetCard.mp hselected).2
  have h := product_vanishesBelow primary body order atoms hzero selected
  funext arity
  apply h arity
  have := arity.property
  omega

theorem product_one_add_eq_truncated_sum (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (atoms : Index → KernelFamily primary body order)
    (hzero : ∀ index, atoms index (zeroArity order) = 0) (hsize : order ≤ Fintype.card Index) :
    (∏ index, (1 + atoms index)) = ∑ degree ∈ Finset.range (order + 1), elementary primary body order atoms degree := by
  rw [Finset.prod_one_add, Finset.sum_powerset]
  change (∑ degree ∈ Finset.range (Fintype.card Index + 1), elementary primary body order atoms degree) = _
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega : order + 1 ≤ Fintype.card Index + 1))
  intro degree _ hnot
  exact elementary_above_order primary body order degree atoms hzero (by
    simp only [Finset.mem_range] at hnot
    omega)

theorem product_one_add_sub_one (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (atoms : Index → KernelFamily primary body order)
    (hzero : ∀ index, atoms index (zeroArity order) = 0) (hsize : order ≤ Fintype.card Index) :
    (∏ index, (1 + atoms index)) - 1 =
      ∑ degree ∈ Finset.range order, elementary primary body order atoms (degree + 1) := by
  rw [product_one_add_eq_truncated_sum primary body order atoms hzero hsize,
    Finset.sum_range_succ', elementary_zero]
  abel

end

end CurrentAFT.GradedNewton

end

end

section

section









namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.CommonQueueNorm
end CurrentAFT.CommonQueueNorm



/-!
# Norm control of complete finite background products

Newton's identities retain cancellation in the sum of all actual atoms.
Higher power sums are bounded by their total squared norm. The resulting
constant depends only on the fixed truncation order, not on the number of
factors, the palette, or a coordinate basis.
-/

namespace CurrentAFT.GradedNewtonNorm

open AFT ControlCoordinates GradedControlAlgebra GradedControlNorm GradedControlStability
  GradedInverseNorm CommonQueueAssembly GradedNewton
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {Primary Body Index : Type*} [Fintype Primary] [Fintype Body] [Fintype Index]

omit [Fintype Index] in
theorem norm_sign_mul (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (pf bf : ℝ) (power : ℕ) (family : KernelFamily primary body order) :
    familyNorm primary body order pf bf ((-1 : KernelFamily primary body order) ^ power * family) =
      familyNorm primary body order pf bf family := by
  induction power generalizing family with
  | zero => rw [pow_zero, one_mul]
  | succ power ih => rw [pow_succ, mul_assoc, neg_one_mul, ih, familyNorm_neg]

omit [Fintype Index] in
theorem norm_nat_mul (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (pf bf : ℝ) (natural : ℕ) (family : KernelFamily primary body order) :
    familyNorm primary body order pf bf ((natural : KernelFamily primary body order) * family) =
      (natural : ℝ) * familyNorm primary body order pf bf family := by
  have heq : (natural : KernelFamily primary body order) * family = (natural : ℝ) • family := by
    rw [← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
  rw [heq, familyNorm_smul, abs_of_nonneg (Nat.cast_nonneg natural)]

theorem newton_norm_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order degree : ℕ)
    (pf bf : ℝ) (hpf : 0 ≤ pf) (hbf : 0 ≤ bf) (atoms : Index → KernelFamily primary body order) :
    (degree : ℝ) * familyNorm primary body order pf bf (elementary primary body order atoms degree) ≤
      ∑ pair ∈ (Finset.HasAntidiagonal.antidiagonal degree).filter (fun pair => pair.1 < degree),
        familyNorm primary body order pf bf (elementary primary body order atoms pair.1) *
          familyNorm primary body order pf bf (powerSum primary body order atoms pair.2) := by
  rw [← norm_nat_mul, newton_identity, norm_sign_mul]
  calc
    _ ≤ ∑ pair ∈ (Finset.HasAntidiagonal.antidiagonal degree).filter (fun pair => pair.1 < degree),
        familyNorm primary body order pf bf
          ((-1 : KernelFamily primary body order) ^ pair.1 * elementary primary body order atoms pair.1 *
            powerSum primary body order atoms pair.2) :=
      familyNorm_sum_le primary body order pf bf hpf hbf _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro pair _
      have h := familyNorm_product_le primary body order pf bf hpf hbf
        ((-1) ^ pair.1 * elementary primary body order atoms pair.1) (powerSum primary body order atoms pair.2)
      change familyNorm primary body order pf bf
        (((-1) ^ pair.1 * elementary primary body order atoms pair.1) *
          powerSum primary body order atoms pair.2) ≤ _ at h
      simpa only [norm_sign_mul] using h

theorem elementary_norm_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (pf bf : ℝ) (hpf : 0 ≤ pf) (hbf : 0 ≤ bf) (atoms : Index → KernelFamily primary body order)
    (delta : ℝ) (hdelta : 0 ≤ delta) (hsmall : delta ≤ 1)
    (hpowers : ∀ power, 1 ≤ power → power ≤ order →
      familyNorm primary body order pf bf (powerSum primary body order atoms power) ≤ delta) :
    ∀ degree, 1 ≤ degree → degree ≤ order →
      familyNorm primary body order pf bf (elementary primary body order atoms degree) ≤
        delta * ((order + 1 : ℕ) : ℝ) ^ degree := by
  intro degree
  induction degree using Nat.strong_induction_on with
  | h degree ih =>
    intro hpositive hdegree
    let scale : ℝ := ((order + 1 : ℕ) : ℝ)
    have hscale : 1 ≤ scale := by dsimp [scale]; norm_cast; omega
    have hnorm : 0 ≤ familyNorm primary body order pf bf (elementary primary body order atoms degree) :=
      familyNorm_nonneg primary body order pf bf hpf hbf _
    have hterm (pair : ℕ × ℕ)
        (hpair : pair ∈ (Finset.HasAntidiagonal.antidiagonal degree).filter (fun pair => pair.1 < degree)) :
        familyNorm primary body order pf bf (elementary primary body order atoms pair.1) *
            familyNorm primary body order pf bf (powerSum primary body order atoms pair.2) ≤
          scale ^ (degree - 1) * delta := by
      have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_filter.mp hpair).1
      have hlt := (Finset.mem_filter.mp hpair).2
      have hfirst : familyNorm primary body order pf bf (elementary primary body order atoms pair.1) ≤
          scale ^ (degree - 1) := by
        by_cases hz : pair.1 = 0
        · rw [hz, elementary_zero, familyNorm_one]
          exact one_le_pow₀ hscale
        · have h := ih pair.1 hlt (by omega) (by omega)
          have hscaled : delta * scale ^ pair.1 ≤ scale ^ pair.1 := by
            exact (mul_le_mul_of_nonneg_right hsmall (pow_nonneg (by linarith : 0 ≤ scale) _)).trans_eq (one_mul _)
          exact (h.trans hscaled).trans (pow_le_pow_right₀ hscale (by omega))
      exact mul_le_mul hfirst (hpowers pair.2 (by omega) (by omega))
        (familyNorm_nonneg primary body order pf bf hpf hbf _) (pow_nonneg (by linarith : 0 ≤ scale) _)
    have hcard : (((Finset.HasAntidiagonal.antidiagonal degree).filter (fun pair => pair.1 < degree)).card : ℝ) ≤ scale := by
      have h : ((Finset.HasAntidiagonal.antidiagonal degree).filter (fun pair => pair.1 < degree)).card ≤ order + 1 :=
        (Finset.card_filter_le (Finset.HasAntidiagonal.antidiagonal degree) (fun pair => pair.1 < degree)).trans
          (by simpa using (by omega : degree + 1 ≤ order + 1))
      change (((Finset.HasAntidiagonal.antidiagonal degree).filter (fun pair => pair.1 < degree)).card : ℝ) ≤ ((order + 1 : ℕ) : ℝ)
      exact_mod_cast h
    have hnewton := newton_norm_le primary body order degree pf bf hpf hbf atoms
    calc
      _ ≤ (degree : ℝ) * familyNorm primary body order pf bf (elementary primary body order atoms degree) := by
        have hd : (1 : ℝ) ≤ degree := Nat.one_le_cast.mpr hpositive
        nlinarith
      _ ≤ ∑ pair ∈ (Finset.HasAntidiagonal.antidiagonal degree).filter (fun pair => pair.1 < degree),
          familyNorm primary body order pf bf (elementary primary body order atoms pair.1) *
            familyNorm primary body order pf bf (powerSum primary body order atoms pair.2) := hnewton
      _ ≤ ∑ _pair ∈ (Finset.HasAntidiagonal.antidiagonal degree).filter (fun pair => pair.1 < degree), scale ^ (degree - 1) * delta :=
        Finset.sum_le_sum hterm
      _ = (((Finset.HasAntidiagonal.antidiagonal degree).filter (fun pair => pair.1 < degree)).card : ℝ) *
          (scale ^ (degree - 1) * delta) := by simp
      _ ≤ scale * (scale ^ (degree - 1) * delta) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg (pow_nonneg (by linarith : 0 ≤ scale) _) hdelta)
      _ = _ := by
        change _ = delta * scale ^ degree
        conv_rhs => rw [show degree = (degree - 1) + 1 by omega, pow_succ]
        ring

theorem product_norm_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (pf bf : ℝ) (hpf : 0 ≤ pf) (hbf : 0 ≤ bf) (atoms : Index → KernelFamily primary body order)
    (hzero : ∀ index, atoms index (zeroArity order) = 0) (hsize : order ≤ Fintype.card Index)
    (delta : ℝ) (hdelta : 0 ≤ delta) (hsmall : delta ≤ 1)
    (hpowers : ∀ power, 1 ≤ power → power ≤ order →
      familyNorm primary body order pf bf (powerSum primary body order atoms power) ≤ delta) :
    familyNorm primary body order pf bf ((∏ index, (1 + atoms index)) - 1) ≤
      (order : ℝ) * delta * ((order + 1 : ℕ) : ℝ) ^ order := by
  rw [product_one_add_sub_one primary body order atoms hzero hsize]
  calc
    _ ≤ ∑ degree ∈ Finset.range order,
        familyNorm primary body order pf bf (elementary primary body order atoms (degree + 1)) :=
      familyNorm_sum_le primary body order pf bf hpf hbf _ _
    _ ≤ ∑ _degree ∈ Finset.range order, delta * ((order + 1 : ℕ) : ℝ) ^ order := by
      apply Finset.sum_le_sum
      intro degree hdegree
      have hd := Finset.mem_range.mp hdegree
      exact (elementary_norm_le primary body order pf bf hpf hbf atoms delta hdelta hsmall hpowers
        (degree + 1) (by omega) (by omega)).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ order + 1 by omega))
            (by omega : degree + 1 ≤ order)) hdelta)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

theorem powerSum_norm_le_of_square (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (pf bf : ℝ) (hpf : 0 ≤ pf) (hbf : 0 ≤ bf) (atoms : Index → KernelFamily primary body order)
    (delta : ℝ)
    (hfirst : familyNorm primary body order pf bf (∑ index, atoms index) ≤ delta)
    (hsquares : (∑ index, familyNorm primary body order pf bf (atoms index) ^ 2) ≤ delta)
    (hatoms : ∀ index, familyNorm primary body order pf bf (atoms index) ≤ 1)
    (power : ℕ) (hpower : 1 ≤ power) :
    familyNorm primary body order pf bf (powerSum primary body order atoms power) ≤ delta := by
  by_cases hone : power = 1
  · simpa only [powerSum, hone, pow_one] using hfirst
  · have htwo : 2 ≤ power := by omega
    have hpoint (index : Index) : familyNorm primary body order pf bf (atoms index) ^ power ≤
        familyNorm primary body order pf bf (atoms index) ^ 2 := by
      have hnonneg := familyNorm_nonneg primary body order pf bf hpf hbf (atoms index)
      have htail : familyNorm primary body order pf bf (atoms index) ^ (power - 2) ≤ 1 :=
        pow_le_one₀ hnonneg (hatoms index)
      calc
        _ = familyNorm primary body order pf bf (atoms index) ^ 2 *
            familyNorm primary body order pf bf (atoms index) ^ (power - 2) := by
          rw [← pow_add]
          congr 1
          omega
        _ ≤ familyNorm primary body order pf bf (atoms index) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left htail (sq_nonneg _)
        _ = _ := mul_one _
    calc
      _ ≤ ∑ index, familyNorm primary body order pf bf (atoms index ^ power) :=
        familyNorm_sum_le primary body order pf bf hpf hbf _ _
      _ ≤ ∑ index, familyNorm primary body order pf bf (atoms index) ^ 2 := by
        apply Finset.sum_le_sum
        intro index _
        exact (familyNorm_pow_le primary body order pf bf hpf hbf (atoms index) power).trans (hpoint index)
      _ ≤ _ := hsquares

/-- Full product stability needs only its genuinely canceled first sum,
the population-weighted square budget, and small individual atoms. -/
theorem complete_product_norm_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (pf bf : ℝ) (hpf : 0 ≤ pf) (hbf : 0 ≤ bf) (atoms : Index → KernelFamily primary body order)
    (hzero : ∀ index, atoms index (zeroArity order) = 0) (hsize : order ≤ Fintype.card Index)
    (delta : ℝ) (hdelta : 0 ≤ delta) (hsmall : delta ≤ 1)
    (hfirst : familyNorm primary body order pf bf (∑ index, atoms index) ≤ delta)
    (hsquares : (∑ index, familyNorm primary body order pf bf (atoms index) ^ 2) ≤ delta)
    (hatoms : ∀ index, familyNorm primary body order pf bf (atoms index) ≤ 1) :
    familyNorm primary body order pf bf ((∏ index, (1 + atoms index)) - 1) ≤
      (order : ℝ) * delta * ((order + 1 : ℕ) : ℝ) ^ order := by
  exact product_norm_le primary body order pf bf hpf hbf atoms hzero hsize delta hdelta hsmall
    (fun power hpower _ => powerSum_norm_le_of_square primary body order pf bf hpf hbf atoms delta
      hfirst hsquares hatoms power hpower)

end

end CurrentAFT.GradedNewtonNorm

end

section









/-!
# Three actual population roles in a complete fixed-queue product

This is the finite bookkeeping used for free bodies, queue bodies and
complete leg triples. The one queue atom is shared by its entire population.
The estimate retains cancellation of the combined linear coefficient.
-/

namespace CurrentAFT.RoleProduct

open AFT ControlCoordinates GradedControlAlgebra GradedControlNorm GradedNewtonNorm
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

abbrev RoleIndex (freeCount queueCount legCount : ℕ) :=
  Fin freeCount ⊕ (Fin queueCount ⊕ Fin legCount)

def roleAtoms (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (freeCount queueCount legCount : ℕ) (free queue leg : KernelFamily primary body order) :
    RoleIndex freeCount queueCount legCount → KernelFamily primary body order :=
  Sum.elim (fun _ => free) (Sum.elim (fun _ => queue) (fun _ => leg))

theorem roleAtoms_sum (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (freeCount queueCount legCount : ℕ) (free queue leg : KernelFamily primary body order) :
    (∑ index, roleAtoms primary body order freeCount queueCount legCount free queue leg index) =
      freeCount • free + queueCount • queue + legCount • leg := by
  simp only [roleAtoms, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  abel

theorem roleAtoms_product (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (freeCount queueCount legCount : ℕ) (free queue leg : KernelFamily primary body order) :
    (∏ index, (1 + roleAtoms primary body order freeCount queueCount legCount free queue leg index)) =
      (1 + free) ^ freeCount * (1 + queue) ^ queueCount * (1 + leg) ^ legCount := by
  simp only [roleAtoms, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [mul_assoc]

theorem complete_role_product_norm_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (pf bf : ℝ) (hpf : 0 ≤ pf) (hbf : 0 ≤ bf) (freeCount queueCount legCount : ℕ)
    (hsize : order ≤ freeCount + queueCount + legCount) (free queue leg : KernelFamily primary body order)
    (hfreeZero : free (zeroArity order) = 0) (hqueueZero : queue (zeroArity order) = 0)
    (hlegZero : leg (zeroArity order) = 0)
    (delta : ℝ) (hdelta : 0 ≤ delta) (hsmall : delta ≤ 1)
    (hfirst : familyNorm primary body order pf bf
      (freeCount • free + queueCount • queue + legCount • leg) ≤ delta)
    (hsquares : (freeCount : ℝ) * familyNorm primary body order pf bf free ^ 2 +
      (queueCount : ℝ) * familyNorm primary body order pf bf queue ^ 2 +
      (legCount : ℝ) * familyNorm primary body order pf bf leg ^ 2 ≤ delta)
    (hfree : familyNorm primary body order pf bf free ≤ 1)
    (hqueue : familyNorm primary body order pf bf queue ≤ 1)
    (hleg : familyNorm primary body order pf bf leg ≤ 1) :
    familyNorm primary body order pf bf
      ((1 + free) ^ freeCount * (1 + queue) ^ queueCount * (1 + leg) ^ legCount - 1) ≤
        (order : ℝ) * delta * ((order + 1 : ℕ) : ℝ) ^ order := by
  let atoms := roleAtoms primary body order freeCount queueCount legCount free queue leg
  have hzero (index : RoleIndex freeCount queueCount legCount) : atoms index (zeroArity order) = 0 := by
    cases index with
    | inl index => exact hfreeZero
    | inr index => cases index with
      | inl index => exact hqueueZero
      | inr index => exact hlegZero
  have hcard : order ≤ Fintype.card (RoleIndex freeCount queueCount legCount) := by
    simpa only [RoleIndex, Fintype.card_sum, Fintype.card_fin, Nat.add_assoc] using hsize
  have hfirst' : familyNorm primary body order pf bf (∑ index, atoms index) ≤ delta := by
    rw [show (∑ index, atoms index) = freeCount • free + queueCount • queue + legCount • leg from
      roleAtoms_sum primary body order freeCount queueCount legCount free queue leg]
    exact hfirst
  have hsquares' : (∑ index, familyNorm primary body order pf bf (atoms index) ^ 2) ≤ delta := by
    simpa only [atoms, roleAtoms, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, add_assoc] using hsquares
  have hatoms (index : RoleIndex freeCount queueCount legCount) :
      familyNorm primary body order pf bf (atoms index) ≤ 1 := by
    cases index with
    | inl index => exact hfree
    | inr index => cases index with
      | inl index => exact hqueue
      | inr index => exact hleg
  have h := complete_product_norm_le primary body order pf bf hpf hbf atoms hzero hcard delta hdelta hsmall
    hfirst' hsquares' hatoms
  rw [roleAtoms_product primary body order freeCount queueCount legCount free queue leg] at h
  exact h

end

end CurrentAFT.RoleProduct

end

section













/-! # The complete conditional first histogram is cycle fluctuation plus queue drift -/

namespace CurrentAFT.ConditionalHistogramMean

open AFT DiffuseProfiles ProposalPrimary FirstHistogram LocalReferenceEnergy
  UniformBodyProfiles BodyRootAverages BackgroundCertificates FringeCertificate
  BackgroundPopulationBounds HistogramMean FiniteConcentration ActualCycleMeanMGF
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.dimension Parameters.bodySize Parameters.legCount
  ProposalPrimary.primaryLaw ProposalPrimary.centerLaw ProposalPrimary.safeLaw

abbrev RoleIndex (security : ℕ) := RoleProduct.RoleIndex
  (freeCount security) (Parameters.modulus security) (Parameters.legCount security)

def roleOf (security : ℕ) : RoleIndex security → BodyRole :=
  Sum.elim (fun _ => .free) (Sum.elim (fun _ => .queue) (fun _ => .attachment))

def roles (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) :
    BodyIndex security → BodyRole := fun vertex => roleOf security (layout.symm vertex)

def offBodyVector (security : ℕ) : ProfileSpace security :=
  ProfileHilbert.whiten (uniformReference security).weight
    (fun output => offBodyMean security output - 2 * uniformProfile security output)

def conditionalMean (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security) :
    ProfileSpace security :=
  NormalizedMeanAlgebra.euclideanSum (NormalizedMeanAlgebra.normalizationScale security)
    (realizedResponse security (roles security layout) queue permutation latent)
    ((Parameters.legCount security : ℝ) • offBodyVector security)















end

end CurrentAFT.ConditionalHistogramMean

end

section








/-! # The complete normalized cycle mean, retaining a fixed endpoint offset -/

namespace CurrentAFT.WholeCycleMGF

open AFT FiniteConcentration
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq

variable {Scalar Hilbert : Type*} [Fintype Scalar]
  [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]

/-- The literal full finite expectation, with every cyclic difference and
the deterministic off-body endpoint contribution. -/
def normalizedTotalMoment (body population : ℕ) (source : FiniteDist Scalar)
    (response : Fin body → Scalar × Scalar → Hilbert) (offset : Hilbert) (parameter : ℝ) : ℝ :=
  (FiniteDist.independent (fun _ : Fin body => source)).expectation (fun latent =>
    Real.exp (parameter * ‖(Real.sqrt (population : ℝ))⁻¹ •
      ((∑ vertex : Fin body, response vertex
        (latent ((finRotate body).symm vertex), latent vertex)) + offset)‖ ^ 2))

/-- This vector is computed from actual pair-law means, not an assumed
conditional-moment bound. -/
def normalizedMean (body population : ℕ) (source : FiniteDist Scalar)
    (response : Fin body → Scalar × Scalar → Hilbert) (offset : Hilbert) : Hilbert :=
  (Real.sqrt (population : ℝ))⁻¹ •
    ((∑ vertex : Fin body, vectorMean (source.prod source) (response vertex)) + offset)



end

end CurrentAFT.WholeCycleMGF

end

section











namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.DriftMGF
end CurrentAFT.DriftMGF




/-! # The actual complete conditional histogram mean has a uniform MGF -/

namespace CurrentAFT.ConditionalHistogramMGF

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy UniformBodyProfiles
  ActualCycleMeanMGF ConditionalHistogramMean HistogramMean
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  BackgroundRates.radius

/-- Literal finite expectation over the actual closed protected Gaussian
cycle, including every actual off-body endpoint marginal. -/
def moment (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (parameter : ℝ) : ℝ :=
  WholeCycleMGF.normalizedTotalMoment (Parameters.bodySize security) (Parameters.dimension security)
    (edgeLaw security) (response security (roles security layout) queue permutation)
    ((Parameters.legCount security : ℝ) • offBodyVector security) parameter









end

end CurrentAFT.ConditionalHistogramMGF

end

section








/-! # Actual public parameter budgets for the complete physical Fock norm -/

namespace CurrentAFT.PhysicalFockRates

open AFT ProposalPrimary ActualBlockFock BackgroundRates UniformBodyProfiles
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount Parameters.dimension
  BackgroundRates.radius UniformBodyProfiles.deviation

def normalizedScale (security : ℕ) (multiple : ℝ) : ℝ :=
  multiple * radius security / Real.sqrt (Parameters.dimension security : ℝ)



def linearEnvelope (security : ℕ) (multiple : ℝ) : ℝ :=
  normalizedScale security multiple ^ 2 *
    ((Parameters.legCount security : ℝ) * firstConstant * (Parameters.base security : ℝ) ^ 31 +
      2 * (Parameters.bodySize security : ℝ) * deviation security ^ 2)

def nonlinearEnvelope (security : ℕ) (multiple : ℝ) : ℝ :=
  128 * (Parameters.legCount security : ℝ) *
    (normalizedScale security multiple ^ 2 +
      Real.sqrt (Parameters.dimension security : ℝ) * normalizedScale security multiple ^ 3) *
    (higherConstant * (Parameters.base security : ℝ) ^ 24)

theorem dimension_pos (security : ℕ) : (0 : ℝ) < Parameters.dimension security := by
  have h := (Parameters.dimension_bounds security).1
  have hb := Parameters.base_pos security
  exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < 65536 * Parameters.base security ^ 160) h)

































end

end CurrentAFT.PhysicalFockRates

end

section













/-! # The actual independent-block first coefficient is the complete cycle mean -/

namespace CurrentAFT.ActualBlockMean

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy PositiveFirstCoefficient
  ActualBlockFock ConditionalHistogramMean ActualCycleMeanMGF UniformBodyProfiles
  HistogramMean BodyRootAverages PhysicalBlockTensors
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  primaryLaw centerLaw safeLaw scalarLaw

abbrev Palette (security : ℕ) := LocalReferenceEnergy.Palette security









def blockVector (security : ℕ) (index : BlockIndex security)
    (law : FiniteDist (Slots security index → Palette security)) : ProfileSpace security :=
  WithLp.toLp 2 (fun output => LocalTensors.degreeTensor
    (fun _ : Slots security index => uniformReference security) law.weight 1 (fun _ => output))







/-- The same complete cyclic difference is moved by the body permutation.
In particular the first latent vertex still reads its closing predecessor. -/
def rootAt (security : ℕ) (permutation : Equiv.Perm (BodyIndex security))
    (latent : BodyIndex security → Edge security) (position : BodyIndex security) : ℤ :=
  (latent (permutation.symm position)).val -
    (latent ((finRotate (Parameters.bodySize security)).symm (permutation.symm position))).val

def attachmentRoots (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (leg : Fin (Parameters.legCount security)) : ℤ :=
  rootAt security permutation latent (layout (.inr (.inr leg)))

def centerRoots (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (center : Fin (centerCount security)) : ℤ :=
  rootAt security permutation latent (layout (.inl center))

def queueRoots (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (point : Fin (Parameters.modulus security)) : ℤ :=
  rootAt security permutation latent (layout (.inr (.inl point)))

def rootedLaw (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security) :
    (index : BlockIndex security) → FiniteDist (Slots security index → Palette security) :=
  blockLawAt security (attachmentRoots security layout permutation latent)
    (centerRoots security layout permutation latent) (queueRoots security layout permutation latent) queue

def bodyVector (security : ℕ) (role : BodyRole) (queue root : ℤ) : ProfileSpace security :=
  uniformVector security ((preRootLaw security role queue).map (shiftEquiv security root)).weight









end

end CurrentAFT.ActualBlockMean

end

section









/-! # Retaining the full mean cancellation after finitely many block deletions -/

namespace CurrentAFT.OmittedBlockMean

open AFT
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {Index Coordinate : Type*} [Fintype Index] [Fintype Coordinate]

def removed (kept : Finset Index) : Finset Index := Finset.univ.filter (fun index => index ∉ kept)







end

end CurrentAFT.OmittedBlockMean

end

section















/-!
# Complete actual physical Fock energy after averaging the closed cycle

All finite output degrees are retained. The local block conditions and the
whole-mean exponential moment are proved for the current distributions.
-/

namespace CurrentAFT.ActualFockBound

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy ActualBlockFock
  ActualBlockMean ActualCycleMeanMGF ConditionalHistogramMean ConditionalHistogramMGF PhysicalFockRates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  BackgroundRates.radius

/-- The full population-normalized real physical coefficient energy. -/
def energy {Slot Color : Type*} [Fintype Slot] [Fintype Color]
    (reference : FiniteDist Color) (mass : (Slot → Color) → ℝ) (radius : ℝ) : ℝ :=
  HistogramTail.fockEnergy (Fintype.card Slot) radius (fun degree =>
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Slot => reference) mass degree))









def latentLaw (security : ℕ) : FiniteDist (BodyIndex security → Edge security) :=
  FiniteDist.independent (fun _ : BodyIndex security => edgeLaw security)

/-- The actual positive output law with the whole dependent cycle averaged
outside the genuine independent local blocks. -/
def outputLaw (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) : FiniteDist (Sigma (Slots security) → ActualBlockMean.Palette security) :=
  (latentLaw security).mix (fun latent => FiniteDist.retype (BlockProducts.blockLaw (Slots security)
    (rootedLaw security layout queue permutation latent)))









end

end CurrentAFT.ActualFockBound

end

section









/-! # The complete physical Fock energy is a genuine finite Hilbert norm -/

namespace CurrentAFT.PhysicalFockHilbert

open AFT ActualFockBound
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

def channel (reference : FiniteDist Color) (radius : ℝ) :
    ((Slot → Color) → ℝ) →ₗ[ℝ] (LocalTensors.FockCoordinate Slot Color → ℝ) where
  toFun mass coordinate := Real.sqrt (coordinate.1.val.factorial : ℝ) *
    (radius / Real.sqrt (Fintype.card Slot : ℝ)) ^ coordinate.1.val *
      LocalTensors.degreeTensor (fun _ : Slot => reference) mass coordinate.1.val coordinate.2
  map_add' first second := by
    funext coordinate
    rw [← LocalTensors.degreeTensorLinear_apply, map_add]
    simp only [Pi.add_apply, mul_add, LocalTensors.degreeTensorLinear_apply]
  map_smul' scalar mass := by
    funext coordinate
    rw [← LocalTensors.degreeTensorLinear_apply, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, LocalTensors.degreeTensorLinear_apply]
    ring



/-- A literal finite Euclidean vector, with the physical ordered-tensor
factorials and exact full-population normalization in every degree. -/
def vector (reference : FiniteDist Color) (radius : ℝ) :
    ((Slot → Color) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (LocalTensors.FockCoordinate Slot Color) :=
  (ProfileHilbert.whiten (fun _ : LocalTensors.FockCoordinate Slot Color => (1 : ℝ))).comp
    (channel reference radius)





end

end CurrentAFT.PhysicalFockHilbert

end

section









namespace AFT
end AFT
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.CanonicalMoments.refresh
end AFT.CanonicalMoments.refresh
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.MixedKernel
end AFT.MixedKernel




/-!
# Genuine finite-atom fixed moments with unequal public pools

The atom lower bound is applied to every actual mixed fiber. Distinct-index
collision contraction and population counting come from the generic
canonical U-statistic theorems, without any parameter-family substitution.
-/

namespace CurrentAFT.FiniteAtomMoments

open AFT
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]





/-- Explicit norm constant for a single fixed two-pool kernel. -/
def momentFactor (primaryOrder bodyOrder moment : ℕ) (ratio : ℝ) : ℝ :=
  (CanonicalMoments.momentConstant primaryOrder (2 * moment) *
    CanonicalMoments.momentConstant bodyOrder (2 * moment) + 1) *
      (1 + ratio) ^ (primaryOrder + bodyOrder)



variable {PS BS PP BP : Type*} [Fintype PS] [Fintype BS] [Fintype PP] [Fintype BP]

local instance _root_.CurrentAFT.FiniteAtomMoments.instDecidableEqSum_currentAFT : DecidableEq (PS ⊕ BS) := Classical.decEq _
local instance _root_.CurrentAFT.FiniteAtomMoments.instDecidableEqSum_currentAFT_1 : DecidableEq (PP ⊕ BP) := Classical.decEq _



end

end CurrentAFT.FiniteAtomMoments

end

section










/-! # Actual population and atom budgets for fixed public-control moments -/

namespace CurrentAFT.FiniteAtomMoments

open AFT
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount BackgroundRates.ordinaryPool

def currentAtomLower (security : ℕ) : ℝ := 1 / (4 * (Parameters.modulus security : ℝ) ^ 2)















/-- A common explicit threshold supplies both distinct-index moment
normalizers at all arities up to the fixed calibration order. -/
theorem current_pool_room (security maximum : ℕ) (hsecurity : 2 * maximum ≤ security) :
    ∀ primaryOrder bodyOrder, primaryOrder + bodyOrder ≤ maximum →
      2 * primaryOrder ≤ Parameters.legCount security ∧
        2 * bodyOrder ≤ BackgroundRates.ordinaryPool security := by
  intro primaryOrder bodyOrder horders
  have hprimary : Parameters.base security ≤ Parameters.legCount security := by
    rw [Parameters.legCount_eq]
    exact Nat.le_self_pow (by decide) _
  have hbody : Parameters.base security ≤ BackgroundRates.ordinaryPool security :=
    (Nat.le_self_pow (by decide) _).trans (BackgroundRates.ordinaryPool_lower security)
  have hbase : security ≤ Parameters.base security := by simp [Parameters.base]
  omega

end

end CurrentAFT.FiniteAtomMoments

end

section










/-!
# Centering and triangularity of each physical distinct-group summand

The paired channel preserves conditional centering of an arbitrary joint
kernel in every primary slot. Ordinary-body slots remain centered as well.
Each selected group is distinct. A test omitting any one of those groups
therefore integrates to zero, before averaging over selections. This is the
triangularity mechanism, independent of any subsequent response norm bound.
-/

namespace CurrentAFT.PhysicalTriangularity

open AFT DiffuseProfiles ProposalPrimary ControlCoordinates PhysicalSynthesis
open scoped BigOperators Classical

noncomputable section

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def pairedMatrix (security : ℕ) (color : Palette security) (group : Group security) : ℝ :=
  pairedChannel security (Pi.single color 1) group



















end

end CurrentAFT.PhysicalTriangularity

end

section













namespace AFT
end AFT
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.FiniteDist
end AFT.FiniteDist






/-!
# Actual safe control groups for finite-atom moment bounds

The compensator alphabet contains only the safe colors. No positive lower
bound is asserted at forbidden center atoms. Ordinary-body coordinates may
be augmented by an independent unused primary; this gives the same positive
group alphabet in the two independent pools without changing any weight.
-/

namespace CurrentAFT.SafeControlGroups

open AFT DiffuseProfiles ProposalPrimary PhysicalSynthesis
open scoped BigOperators Classical

noncomputable section

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw centerLaw



abbrev SafeGroup (security : ℕ) := Palette security × ActualControls.SafePalette security

def reference (security : ℕ) : FiniteDist (SafeGroup security) :=
  (primaryLaw security).prod (ActualControls.bodyReference security)

def unwrap (security : ℕ) (group : SafeGroup security) : Group security := (group.1, group.2.val)















/-- The common-alphabet kernel used by two-pool moment estimates. The
ordinary-body primary coordinate is independent and unused. -/
def kernel (security r s : ℕ)
    (input : ControlCoordinates.canonicalKernels (primaryLaw security)
      (ActualControls.bodyReference security) r s)
    (word : (Fin r ⊕ Fin s) → SafeGroup security) : ℝ :=
  pairedKernel security r s input.val
    (fun index => unwrap security (word (Sum.inl index)))
    (fun index => (word (Sum.inr index)).2)















end

end CurrentAFT.SafeControlGroups

end

section








/-! # The real diffuse sign profiles before averaging the protected scalar -/

namespace CurrentAFT.FixedDiffuseProfiles

open AFT DiffuseProfiles ProposalPrimary FirstHistogram LocalReferenceEnergy ReferenceMarginals
open scoped BigOperators Classical

noncomputable section

abbrev Palette (security : ℕ) := FirstHistogram.Palette security
abbrev Scalar (security : ℕ) := FirstHistogram.Scalar security

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw activation

def signPairLaw (security : ℕ) (positive : Bool) (scalar : Scalar security) :
    FiniteDist (Palette security × Palette security) :=
  (publicBlurLaw security).mix (fun edge => diffuseSeedPair security positive (edge, scalar))

def fixedProfile (security : ℕ) (positive : Bool) (scalar : Scalar security) (output : Palette security) : ℝ :=
  ∑ second, (signPairLaw security positive scalar).weight (output, second)

theorem fixedProfile_nonneg (security : ℕ) (positive : Bool) (scalar : Scalar security) (output : Palette security) :
    0 ≤ fixedProfile security positive scalar output :=
  Finset.sum_nonneg (fun _ _ => (signPairLaw security positive scalar).nonneg _)

theorem fixedProfile_mass (security : ℕ) (positive : Bool) (scalar : Scalar security) :
    (∑ output, fixedProfile security positive scalar output) = 1 := by
  have h := (signPairLaw security positive scalar).sum_one
  simpa only [Fintype.sum_prod_type, fixedProfile] using h

theorem fixedProfile_height (security : ℕ) (positive : Bool) (scalar : Scalar security) (output : Palette security) :
    fixedProfile security positive scalar output ≤ 2 / (Parameters.modulus security : ℝ) := by
  unfold fixedProfile signPairLaw
  simp only [FiniteDist.mix_weight]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ edge, (publicBlurLaw security).weight edge * (2 / (Parameters.modulus security : ℝ)) :=
      Finset.sum_le_sum (fun edge _ => mul_le_mul_of_nonneg_left
        (diffuseSeedPair_marginal_height security positive (edge, scalar) output) ((publicBlurLaw security).nonneg edge))
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

def directionProfile (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (output : Palette security) : ℝ :=
  (FiniteDist.uniform Bool).expectation (fun coin =>
    fixedProfile security (InwardAnchor.positiveDirection security primary coin) scalar output)

theorem diffusePairAt_first (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (output : Palette security) :
    (∑ second, (diffusePairAt security primary scalar).weight (output, second)) =
      directionProfile security primary scalar output := by
  unfold diffusePairAt directionProfile fixedProfile signPairLaw
  simp only [FiniteDist.mix_weight, FiniteDist.expectation]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro coin _
  rw [← Finset.mul_sum]

theorem diffusePairAt_second (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (output : Palette security) :
    (∑ first, (diffusePairAt security primary scalar).weight (first, output)) =
      directionProfile security primary scalar output := by
  simp_rw [diffusePairAt_symmetric security primary scalar _ output]
  exact diffusePairAt_first security primary scalar output

def fixedMean (security : ℕ) (scalar : Scalar security) (output : Palette security) : ℝ :=
  (fixedProfile security true scalar output + fixedProfile security false scalar output) / 2

def fixedSignProfile (security : ℕ) (scalar : Scalar security) (output : Palette security) : ℝ :=
  (1 - activation security) * (fixedProfile security true scalar output - fixedProfile security false scalar output)

theorem direction_decomposition (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (output : Palette security) :
    2 * (1 - activation security) * directionProfile security primary scalar output =
      2 * (1 - activation security) * fixedMean security scalar output +
        fixedSignProfile security scalar output * FirstResponse.anchorSign security primary := by
  unfold directionProfile
  simp only [FiniteDist.expectation, FiniteDist.uniform_weight, Fintype.card_bool, Nat.cast_ofNat, Fintype.sum_bool]
  by_cases hl : 2 * primary.val < Parameters.modulus security - 1
  · simp only [InwardAnchor.positiveDirection, FirstResponse.anchorSign, hl, if_true]
    unfold fixedMean fixedSignProfile
    ring
  · by_cases hh : Parameters.modulus security - 1 < 2 * primary.val
    · simp only [InwardAnchor.positiveDirection, FirstResponse.anchorSign, hl, hh, if_false, if_true]
      unfold fixedMean fixedSignProfile
      ring
    · simp only [InwardAnchor.positiveDirection, FirstResponse.anchorSign, hl, hh, if_false]
      unfold fixedMean fixedSignProfile
      ring

theorem fixedSignProfile_height (security : ℕ) (scalar : Scalar security) (output : Palette security) :
    |fixedSignProfile security scalar output| ≤ 2 / (Parameters.modulus security : ℝ) := by
  have hfirst := fixedProfile_height security true scalar output
  have hsecond := fixedProfile_height security false scalar output
  have hfirst0 := fixedProfile_nonneg security true scalar output
  have hsecond0 := fixedProfile_nonneg security false scalar output
  have hdiff : |fixedProfile security true scalar output - fixedProfile security false scalar output| ≤
      2 / (Parameters.modulus security : ℝ) := abs_le.mpr (by constructor <;> linarith)
  have ha := activation_pos security
  have ha1 := activation_le_half security
  rw [fixedSignProfile, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - activation security)]
  have hq := FirstResponse.modulus_pos security
  nlinarith only [hdiff, ha, ha1, div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hq.le]

theorem fixedSignProfile_l1 (security : ℕ) (scalar : Scalar security) :
    (∑ output, |fixedSignProfile security scalar output|) ≤ 2 := by
  have ha := activation_pos security
  have ha1 := activation_le_half security
  have hpoint (output : Palette security) :
      |fixedSignProfile security scalar output| ≤ fixedProfile security true scalar output +
        fixedProfile security false scalar output := by
    rw [fixedSignProfile, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - activation security)]
    have hdiff := abs_sub (fixedProfile security true scalar output) (fixedProfile security false scalar output)
    rw [abs_of_nonneg (fixedProfile_nonneg security true scalar output),
      abs_of_nonneg (fixedProfile_nonneg security false scalar output)] at hdiff
    nlinarith only [hdiff, ha, ha1, abs_nonneg
      (fixedProfile security true scalar output - fixedProfile security false scalar output)]
  calc
    _ ≤ ∑ output, (fixedProfile security true scalar output + fixedProfile security false scalar output) :=
      Finset.sum_le_sum (fun output _ => hpoint output)
    _ = 2 := by rw [Finset.sum_add_distrib, fixedProfile_mass, fixedProfile_mass]; norm_num

theorem pairAt_histogram (security : ℕ) (primary : Palette security) (scalar : Scalar security)
    (output : Palette security) :
    (∑ second, (pairAt security primary scalar).weight (output, second)) +
        (∑ first, (pairAt security primary scalar).weight (first, output)) =
      activation security * atom primary output + activation security * (markedCompanionAt security primary scalar).weight output +
        2 * (1 - activation security) * fixedMean security scalar output +
          fixedSignProfile security scalar output * FirstResponse.anchorSign security primary := by
  classical
  have hfirst : (∑ second, (markedPairAt security primary scalar).weight (output, second)) = atom primary output := by
    simp only [markedPairAt_weight, Finset.sum_ite_irrel, Finset.sum_const_zero, FiniteDist.sum_one, atom]
  have hsecond : (∑ first, (markedPairAt security primary scalar).weight (first, output)) =
      (markedCompanionAt security primary scalar).weight output := by
    simp only [markedPairAt_weight, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hdiff := direction_decomposition security primary scalar output
  simp only [pairAt, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [diffusePairAt_first, diffusePairAt_second, hfirst, hsecond]
  nlinarith only [hdiff]

end

end CurrentAFT.FixedDiffuseProfiles

end

section














/-! # Sharp first coefficient of the actual paired group at fixed roots -/

namespace CurrentAFT.FixedPairedFirst

open AFT DiffuseProfiles ProposalPrimary ActualControls FirstHistogram PairedResponse PhysicalSynthesis
open LocalReferenceEnergy PairedReferenceEnergy ReferenceMarginals FixedDiffuseProfiles
open scoped BigOperators Classical

noncomputable section

local instance classicalFourDecidableEq : DecidableEq (Fin 4) := Classical.decEq _
local instance classicalOneDecidableEq : DecidableEq (Fin 1) := Classical.decEq _

abbrev Palette (security : ℕ) := ActualControls.Palette security
abbrev Scalar (security : ℕ) := FirstHistogram.Scalar security

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

 theorem expectation_atom {Color : Type*} [Fintype Color] [DecidableEq Color]
    (law : FiniteDist Color) (color : Color) : law.expectation (fun input => atom input color) = law.weight color := by
  classical
  simp [FiniteDist.expectation, atom, mul_ite]

 theorem indicator_eq_atom {Color : Type*} [DecidableEq Color]
    (first second : Color) (decision : Decidable (first = second)) :
    @ite ℝ (first = second) decision 1 0 = atom first second := by
  by_cases hequal : first = second <;> simp only [atom, hequal, if_true, if_false]

 theorem pair_first_expectation {Color : Type*} [Fintype Color] [DecidableEq Color]
    (law : FiniteDist (Color × Color)) (color : Color) :
    law.expectation (fun pair => atom pair.1 color) = ∑ second, law.weight (color, second) := by
  classical
  simp only [FiniteDist.expectation, Fintype.sum_prod_type, atom]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

 theorem pair_second_expectation {Color : Type*} [Fintype Color] [DecidableEq Color]
    (law : FiniteDist (Color × Color)) (color : Color) :
    law.expectation (fun pair => atom pair.2 color) = ∑ first, law.weight (first, color) := by
  classical
  simp only [FiniteDist.expectation, Fintype.sum_prod_type, atom, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

def pointLaw (security : ℕ) (color : Palette security) : FiniteDist (Palette security) :=
  (FiniteDist.uniform Unit).map (fun _ => color)

theorem pointLaw_weight (security : ℕ) (color output : Palette security) :
    (pointLaw security color).weight output = atom color output := by
  classical
  simp only [pointLaw, FiniteDist.map_weight, Fintype.sum_unique, FiniteDist.uniform_weight,
    Fintype.card_unique, Nat.cast_one, inv_one, atom]

def fixedControlLaw (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (group : Group security) : FiniteDist (Fin 4 → Palette security) :=
  ((pointLaw security (shiftEquiv security compensatorRoot group.2)).prod
    ((pairAt security group.1 scalar).prod (attachmentAt security attachmentRoot scalar))).map
      PhysicalBlockTensors.quadrupleEquiv.symm

theorem fixedControlLaw_weight (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (group : Group security) (word : Fin 4 → Palette security) :
    (fixedControlLaw security compensatorRoot attachmentRoot scalar group).weight word =
      controlMass security compensatorRoot attachmentRoot scalar group word := by
  rw [fixedControlLaw, FiniteDist.map_equiv_weight]
  change (pointLaw security (shiftEquiv security compensatorRoot group.2)).weight (word 0) *
    ((pairAt security group.1 scalar).weight (word 1, word 2) *
      (attachmentAt security attachmentRoot scalar).weight (word 3)) = _
  rw [pointLaw_weight]
  unfold controlMass
  by_cases hequal : shiftEquiv security compensatorRoot group.2 = word 0 <;>
    simp only [atom, hequal, if_true, if_false] <;> ring

theorem fixedControlLaw_histogram (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (group : Group security) (output : Palette security) :
    (fixedControlLaw security compensatorRoot attachmentRoot scalar group).expectation
        (fun word => ∑ index, atom (word index) output) =
      ((∑ second, (pairAt security group.1 scalar).weight (output, second)) +
        (∑ first, (pairAt security group.1 scalar).weight (first, output))) +
      atom (shiftEquiv security compensatorRoot group.2) output +
        (attachmentAt security attachmentRoot scalar).weight output := by
  unfold fixedControlLaw
  rw [FiniteDist.expectation_map]
  have hcount (draw : Palette security × ((Palette security × Palette security) × Palette security)) :
      (∑ index : Fin 4, atom (PhysicalBlockTensors.quadrupleEquiv.symm draw index) output) =
        atom draw.1 output + (atom draw.2.1.1 output + atom draw.2.1.2 output) + atom draw.2.2 output := by
    rw [Fin.sum_univ_four]
    simp only [PhysicalBlockTensors.quadrupleEquiv, Equiv.coe_fn_symm_mk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    ring
  simp only [Function.comp_def]
  simp_rw [hcount, FiniteDist.expectation_prod, FiniteDist.expectation_add, FiniteDist.expectation_const,
    expectation_atom, pointLaw_weight, pair_first_expectation, pair_second_expectation]
  ring

theorem fixedMass_expectation (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (score : Palette security → ℝ) (value : (Fin 4 → Palette security) → ℝ) :
    (∑ word, pairedMassAt security compensatorRoot attachmentRoot scalar score word * value word) =
      (groupLaw security).expectation (fun group => pairedChannel security score group *
        (fixedControlLaw security compensatorRoot attachmentRoot scalar group).expectation value) := by
  rw [← pairedMassLinear_apply]
  simp only [pairedMassLinear, LinearMap.coe_mk, AddHom.coe_mk, FiniteDist.expectation,
    fixedControlLaw_weight, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro group _
  apply Finset.sum_congr rfl
  intro word _
  ring

theorem fixedMass_sum (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (score : Palette security → ℝ) :
    (∑ word, pairedMassAt security compensatorRoot attachmentRoot scalar score word) =
      (1 - activation security) * (primaryLaw security).expectation score := by
  have h := fixedMass_expectation security compensatorRoot attachmentRoot scalar score (fun _ => 1)
  simp only [mul_one, FiniteDist.expectation_const] at h
  rw [h, pairedChannel_mean]

 theorem paired_histogram_decomposition {Primary Center : Type*} [Fintype Primary] [Fintype Center]
    (primary : FiniteDist Primary) (center : FiniteDist Center) (score : Primary → ℝ) (compensator : Center → ℝ)
    (hscore : primary.expectation score = 0) (hcompensator : center.expectation compensator = 0)
    (leg : Primary → ℝ) (body : Center → ℝ) (other : ℝ) :
    (primary.prod center).expectation (fun group =>
      (score group.1 - compensator group.2) * (leg group.1 + body group.2 + other)) =
      primary.expectation (fun color => score color * leg color) -
        center.expectation (fun color => compensator color * body color) := by
  rw [FiniteDist.expectation_prod]
  have hexpand (first : Primary) (second : Center) :
      (score first - compensator second) * (leg first + body second + other) =
        score first * leg first + score first * body second + score first * other -
          compensator second * leg first - compensator second * body second - compensator second * other := by ring
  simp only [hexpand, FiniteDist.expectation_add, FiniteDist.expectation_sub,
    FiniteDist.expectation_const_mul, FiniteDist.expectation_mul_const, FiniteDist.expectation_const,
    hscore, hcompensator]
  ring

theorem fixedMass_histogram_decomposition (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (score : Palette security → ℝ) (hcentered : (primaryLaw security).expectation score = 0) (output : Palette security) :
    LocalTensors.signedColorCount (pairedMassAt security compensatorRoot attachmentRoot scalar score) output =
      (primaryLaw security).expectation (fun primary => score primary *
        ((∑ second, (pairAt security primary scalar).weight (output, second)) +
          (∑ first, (pairAt security primary scalar).weight (first, output)))) -
        signedCompensatorAt security compensatorRoot score output := by
  unfold LocalTensors.signedColorCount
  simp_rw [indicator_eq_atom]
  rw [fixedMass_expectation]
  simp_rw [fixedControlLaw_histogram]
  change ((primaryLaw security).prod (centerLaw security)).expectation (fun group =>
    (score group.1 - compensatorScore security score group.2) * _) = _
  have hcomp : (centerLaw security).expectation (compensatorScore security score) = 0 := by
    change (∑ center, (centerLaw security).weight center * compensatorScore security score center) = 0
    rw [compensatorScore_mass]
    change activation security * (primaryLaw security).expectation score = 0
    rw [hcentered, mul_zero]
  rw [paired_histogram_decomposition (primaryLaw security) (centerLaw security) score
    (compensatorScore security score) hcentered hcomp
    (fun primary => (∑ second, (pairAt security primary scalar).weight (output, second)) +
      (∑ first, (pairAt security primary scalar).weight (first, output)))
    (fun center => atom (shiftEquiv security compensatorRoot center) output)
    ((attachmentAt security attachmentRoot scalar).weight output)]
  rw [signedCompensatorAt_channel]
  congr 1
  unfold FiniteDist.expectation
  apply Finset.sum_congr rfl
  intro center _
  by_cases hequal : shiftEquiv security compensatorRoot center = output <;>
    simp only [atom, hequal, if_true, if_false] <;> ring

def compensatorAnchorAt (security : ℕ) (root : ℤ) (primary : Palette security) : FiniteDist (Palette security) :=
  (InwardAnchor.smoothedAnchorLaw security primary).map (shiftEquiv security root)

theorem compensatorAnchorAt_primary_height (security : ℕ) (root : ℤ) (output : Palette security) :
    (∑ primary, (primaryLaw security).weight primary * (compensatorAnchorAt security root primary).weight output) ≤
      2 * primaryMaximum security := by
  have hmaximum : 0 ≤ primaryMaximum security :=
    div_nonneg (Nat.cast_nonneg _) (mul_nonneg (markMass_pos security).le (Nat.cast_nonneg _))
  simp only [compensatorAnchorAt, FiniteDist.map_equiv_weight]
  calc
    _ ≤ primaryMaximum security * ∑ primary,
        (InwardAnchor.smoothedAnchorLaw security primary).weight ((shiftEquiv security root).symm output) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro primary _
      exact mul_le_mul_of_nonneg_right (GaussianHeights.primaryLaw_upper security primary)
        ((InwardAnchor.smoothedAnchorLaw security primary).nonneg _)
    _ ≤ primaryMaximum security * 2 := mul_le_mul_of_nonneg_left
      (InwardAnchor.smoothedAnchorLaw_row_sum_le_two security _) hmaximum
    _ = _ := by ring

theorem signedCompensatorAt_anchor (security : ℕ) (root : ℤ) (score : Palette security → ℝ)
    (output : Palette security) :
    signedCompensatorAt security root score output = activation security *
      applyAnchor (fun primary center => (compensatorAnchorAt security root primary).weight center)
        (scoreProfile security score) output := by
  unfold signedCompensatorAt
  rw [center_weight_compensator]
  simp only [anchorWeightedScore, compensatorAnchorAt, FiniteDist.map_equiv_weight,
    applyAnchor, scoreProfile, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro primary _
  ring

theorem fixedMass_first_formula (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (score : Palette security → ℝ) (hcentered : (primaryLaw security).expectation score = 0) :
    LocalTensors.signedColorCount (pairedMassAt security compensatorRoot attachmentRoot scalar score) =
      activation security • scoreProfile security score +
        signFunctional (FirstResponse.anchorSign security) (scoreProfile security score) • fixedSignProfile security scalar +
        activation security • applyAnchor (fun primary output => (markedCompanionAt security primary scalar).weight output)
          (scoreProfile security score) -
        activation security • applyAnchor (fun primary output => (compensatorAnchorAt security compensatorRoot primary).weight output)
          (scoreProfile security score) := by
  funext output
  rw [fixedMass_histogram_decomposition security compensatorRoot attachmentRoot scalar score hcentered,
    signedCompensatorAt_anchor]
  simp_rw [pairAt_histogram]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  unfold FiniteDist.expectation
  simp only [← mul_assoc]
  change (∑ primary, scoreProfile security score primary * _) = _
  calc
    _ = activation security * (∑ primary, scoreProfile security score primary * atom primary output) +
        activation security * (∑ primary, (markedCompanionAt security primary scalar).weight output * scoreProfile security score primary) +
        (2 * (1 - activation security) * fixedMean security scalar output) * (∑ primary, scoreProfile security score primary) +
        fixedSignProfile security scalar output *
          (∑ primary, FirstResponse.anchorSign security primary * scoreProfile security score primary) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro primary _
      ring
    _ = _ := by
      have hzero : (∑ primary, scoreProfile security score primary) = 0 := hcentered
      have hatom : (∑ primary, scoreProfile security score primary * atom primary output) = scoreProfile security score output := by
        simp only [atom, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hatom, hzero, mul_zero, add_zero]
      unfold applyAnchor signFunctional
      ring

/-- The complete signed histogram has zero total mass and the exact
four-channel response at every fixed attachment and compensator root. -/
theorem fixedPaired_first_energy (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (score : Palette security → ℝ) (hcentered : (primaryLaw security).expectation score = 0) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
      (pairedMassAt security compensatorRoot attachmentRoot scalar score) 1) ≤
        (20 * activation security ^ 2 * (Parameters.modulus security : ℝ) * primaryMaximum security + 16) *
          (primaryLaw security).expectation (fun primary => score primary ^ 2) := by
  have hmass : (∑ word, pairedMassAt security compensatorRoot attachmentRoot scalar score word) = 0 := by
    rw [fixedMass_sum, hcentered, mul_zero]
  have hq := FirstResponse.modulus_pos security
  have hu (color : Palette security) : 0 < (uniformReference security).weight color := by
    rw [uniformReference_weight]; exact one_div_pos.mpr hq
  have hfirstAnchor (output : Palette security) :
      applyAnchor (fun primary color => (markedCompanionAt security primary scalar).weight color)
        (primaryLaw security).weight output ≤ 2 * primaryMaximum security := by
    unfold applyAnchor
    simpa only [mul_comm] using markedCompanionAt_primary_height security scalar output
  have hsecondAnchor (output : Palette security) :
      applyAnchor (fun primary color => (compensatorAnchorAt security compensatorRoot primary).weight color)
        (primaryLaw security).weight output ≤ 2 * primaryMaximum security := by
    unfold applyAnchor
    simpa only [mul_comm] using compensatorAnchorAt_primary_height security compensatorRoot output
  rw [LocalTensors.degreeTensor_one_energy_zero_mass (uniformReference security) hu _ hmass,
    fixedMass_first_formula security compensatorRoot attachmentRoot scalar score hcentered]
  have h := four_channel_response_energy (primaryLaw security).weight (uniformReference security).weight
    (FirstResponse.anchorSign security) (fixedSignProfile security scalar)
    (fun primary output => (markedCompanionAt security primary scalar).weight output)
    (fun primary output => (compensatorAnchorAt security compensatorRoot primary).weight output)
    (activation security) ((Parameters.modulus security : ℝ) * primaryMaximum security) 2 2
    (2 * (Parameters.modulus security : ℝ) * primaryMaximum security)
    (primaryReference_positive security) (primaryLaw security).sum_one hu
    (fun color => by
      rw [uniformReference_weight]
      exact (GaussianHeights.primaryLaw_upper security color).trans_eq (by unfold primaryMaximum; field_simp))
    (FirstResponse.anchorSign_abs_le_one security) (by norm_num)
    (fun color => by rw [uniformReference_weight, mul_one_div]; exact fixedSignProfile_height security scalar color)
    (fixedSignProfile_l1 security scalar)
    (fun primary output => (markedCompanionAt security primary scalar).nonneg output)
    (fun primary output => (compensatorAnchorAt security compensatorRoot primary).nonneg output)
    (fun primary => (markedCompanionAt security primary scalar).sum_one)
    (fun primary => (compensatorAnchorAt security compensatorRoot primary).sum_one)
    (fun output => by
      rw [uniformReference_weight]
      exact (hfirstAnchor output).trans_eq (by field_simp))
    (fun output => by
      rw [uniformReference_weight]
      exact (hsecondAnchor output).trans_eq (by field_simp))
    (scoreProfile security score)
  change _ ≤ _ * profileSquareNorm (primaryLaw security).weight
    (fun primary => (primaryLaw security).weight primary * score primary) at h
  rw [profileSquareNorm_weight_mul] at h
  exact h.trans_eq (by change _ = _ * (primaryLaw security).l2Sq score; ring)

theorem fixedPaired_first_polynomial (security : ℕ) (compensatorRoot attachmentRoot : ℤ) (scalar : Scalar security)
    (score : Palette security → ℝ) (hcentered : (primaryLaw security).expectation score = 0) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
      (pairedMassAt security compensatorRoot attachmentRoot scalar score) 1) ≤
        ((16 + 1310740 * Real.exp Real.pi) * (Parameters.base security : ℝ) ^ 31) *
          (primaryLaw security).expectation (fun primary => score primary ^ 2) := by
  have h := fixedPaired_first_energy security compensatorRoot attachmentRoot scalar score hcentered
  have hmax := activated_primaryMaximum security
  have hb : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (Parameters.base_ge_two security).trans' (by norm_num : 1 ≤ 2)
  have hpower : (1 : ℝ) ≤ (Parameters.base security : ℝ) ^ 31 := one_le_pow₀ hb
  have hbudget : 20 * activation security ^ 2 * (Parameters.modulus security : ℝ) * primaryMaximum security + 16 ≤
      (16 + 1310740 * Real.exp Real.pi) * (Parameters.base security : ℝ) ^ 31 := by nlinarith only [hmax, hpower]
  exact h.trans (mul_le_mul_of_nonneg_right hbudget ((primaryLaw security).l2Sq_nonneg score))

theorem jointPaired_first_polynomial {Root : Type*} [Fintype Root]
    (security : ℕ) (source : FiniteDist Root) (compensatorRoot attachmentRoot : Root → ℤ)
    (scalar : Root → Scalar security) (score : Root → Palette security → ℝ)
    (hcentered : ∀ root, (primaryLaw security).expectation (score root) = 0) :
    BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
      (jointPairedMass security source compensatorRoot attachmentRoot scalar score) 1) ≤
        ((16 + 1310740 * Real.exp Real.pi) * (Parameters.base security : ℝ) ^ 31) *
          source.expectation (fun root => (primaryLaw security).expectation (fun primary => score root primary ^ 2)) := by
  have hmass : jointPairedMass security source compensatorRoot attachmentRoot scalar score =
      ∑ root, source.weight root • pairedMassAt security (compensatorRoot root) (attachmentRoot root) (scalar root) (score root) := by
    funext word
    simp only [jointPairedMass, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hlinear : LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
      (jointPairedMass security source compensatorRoot attachmentRoot scalar score) 1 =
      ∑ root, source.weight root • LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
        (pairedMassAt security (compensatorRoot root) (attachmentRoot root) (scalar root) (score root)) 1 := by
    rw [← LocalTensors.degreeTensorLinear_apply, hmass, map_sum]
    simp only [map_smul, LocalTensors.degreeTensorLinear_apply]
  rw [hlinear]
  have havg := profileSquareNorm_average_le source (fun _ : Fin 1 → Palette security => (1 : ℝ))
    (fun _ => by norm_num) (fun root => LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
      (pairedMassAt security (compensatorRoot root) (attachmentRoot root) (scalar root) (score root)) 1)
  simp only [profileSquareNorm, div_one] at havg
  simp only [BlockFock.tensorEnergy, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply havg.trans
  calc
    _ ≤ ∑ root, source.weight root * (((16 + 1310740 * Real.exp Real.pi) * (Parameters.base security : ℝ) ^ 31) *
        (primaryLaw security).expectation (fun primary => score root primary ^ 2)) :=
      Finset.sum_le_sum (fun root _ => mul_le_mul_of_nonneg_left
        (fixedPaired_first_polynomial security (compensatorRoot root) (attachmentRoot root) (scalar root) (score root) (hcentered root))
        (source.nonneg root))
    _ = _ := by
      change (∑ root, source.weight root * (((16 + 1310740 * Real.exp Real.pi) * (Parameters.base security : ℝ) ^ 31) *
        (primaryLaw security).expectation (fun primary => score root primary ^ 2))) =
        ((16 + 1310740 * Real.exp Real.pi) * (Parameters.base security : ℝ) ^ 31) *
          ∑ root, source.weight root * (primaryLaw security).expectation (fun primary => score root primary ^ 2)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro root _
      ring



end

end CurrentAFT.FixedPairedFirst

end

section
















/-!
# Complete current paired local Fock response

The sharp first coefficient and all higher coefficients are extracted from
the same actual four-output signed mass. The normalization always uses the
full current output population, including its square-root denominator.
-/

namespace CurrentAFT.TaggedPhysicalFock

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy PairedReferenceEnergy FixedPairedFirst
  PhysicalFockRates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.dimension Parameters.legCount BackgroundRates.radius
  ProposalPrimary.primaryLaw



def firstConstant : ℝ := 16 + 1310740 * Real.exp Real.pi
def higherConstant : ℝ := 66048 * (524288 + 17180131328 * Real.exp Real.pi)






def pairedConstant (multiple : ℝ) : ℝ :=
  10 * firstConstant * multiple ^ 2 + 2200 * higherConstant * multiple ^ 4







/-- The protected second scalar is averaged inside the same four-output
channel, so its pair and attachment are never independently resampled. -/
def averagedPairedChannel (security : ℕ) (compensatorRoot attachmentRoot : ℤ) :
    (FirstHistogram.Palette security → ℝ) →ₗ[ℝ] ((Fin 4 → FirstHistogram.Palette security) → ℝ) :=
  ∑ scalar, (scalarLaw security).weight scalar •
    pairedMassLinear security compensatorRoot attachmentRoot scalar





end

end CurrentAFT.TaggedPhysicalFock

end

section












/-! # Actual ordinary-body response in the complete physical Fock space -/

namespace CurrentAFT.OrdinaryPhysicalFock

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy PhysicalFockRates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.dimension ProposalPrimary.centerLaw
  BackgroundRates.ordinaryPool BackgroundRates.radius

abbrev Palette (security : ℕ) := LocalReferenceEnergy.Palette security
abbrev SafePalette (security : ℕ) := ActualControls.SafePalette security

/-- Extend a genuine safe control density by zero at forbidden atoms. -/
def extendDensity (security : ℕ) : (SafePalette security → ℝ) →ₗ[ℝ] (Palette security → ℝ) where
  toFun score color := if h : InwardAnchor.SafeColor security color then score ⟨color, h⟩ else 0
  map_add' first second := by
    funext color
    by_cases h : InwardAnchor.SafeColor security color <;> simp [h]
  map_smul' scalar score := by
    funext color
    by_cases h : InwardAnchor.SafeColor security color <;> simp [h]







def profile (security : ℕ) (score : SafePalette security → ℝ) (color : Palette security) : ℝ :=
  (centerLaw security).weight color * extendDensity security score color

def translatedProfile (security : ℕ) (root : ℤ) (score : SafePalette security → ℝ) (color : Palette security) : ℝ :=
  profile security score ((shiftEquiv security root).symm color)









/-- The actual root-translated signed center output, as one finite linear
channel. Its positive reference is the actual safe center law. -/
def bodyChannel (security : ℕ) (root : ℤ) :
    (SafePalette security → ℝ) →ₗ[ℝ] ((Fin 1 → Palette security) → ℝ) where
  toFun score word := translatedProfile security root score (word 0)
  map_add' first second := by
    funext word
    simp only [translatedProfile, profile, map_add, Pi.add_apply, mul_add]
  map_smul' scalar score := by
    funext word
    simp only [translatedProfile, profile, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring



end

end CurrentAFT.OrdinaryPhysicalFock

end

section














namespace AFT
end AFT
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.CoordinateTransport
end AFT.MixedKernel.CoordinateTransport




/-!
# Unpaired common-alphabet kernels and actual mixed physical channels

The original coefficient kernel is enlarged only by independent unused
coordinates. The paired four-output channel is then applied exactly once.
-/

namespace CurrentAFT.JointTaggedPhysicalFock

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy PhysicalFockRates
  TaggedPhysicalFock OrdinaryPhysicalFock ControlCoordinates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.dimension Parameters.legCount ProposalPrimary.primaryLaw

section Generic

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]





def unpairedKernel {r s : ℕ} (kernel : DensityKernel (Primary := Primary) (Body := Body) r s)
    (word : (Fin r ⊕ Fin s) → Primary × Body) : ℝ :=
  kernel (fun index => (word (.inl index)).1) (fun index => (word (.inr index)).2)







def finiteKernel {r s : ℕ} (kernel : DensityKernel (Primary := Primary) (Body := Body) r s)
    (word : Fin (r + s) → Primary × Body) : ℝ :=
  unpairedKernel kernel (word ∘ finSumFinEquiv)





def reducePrimary (body : FiniteDist Body) : ((Primary × Body) → ℝ) →ₗ[ℝ] (Primary → ℝ) where
  toFun score first := body.expectation (fun second => score (first, second))
  map_add' first second := by funext point; exact FiniteDist.expectation_add _ _ _
  map_smul' scalar score := by
    funext point
    simp only [Pi.smul_apply, smul_eq_mul, FiniteDist.expectation_const_mul, RingHom.id_apply]

def reduceBody (primary : FiniteDist Primary) : ((Primary × Body) → ℝ) →ₗ[ℝ] (Body → ℝ) where
  toFun score second := primary.expectation (fun first => score (first, second))
  map_add' first second := by funext point; exact FiniteDist.expectation_add _ _ _
  map_smul' scalar score := by
    funext point
    simp only [Pi.smul_apply, smul_eq_mul, FiniteDist.expectation_const_mul, RingHom.id_apply]









end Generic

abbrev Group (security : ℕ) := SafeControlGroups.SafeGroup security

def primaryChannel (security : ℕ) (compensatorRoot attachmentRoot : ℤ) :
    (Group security → ℝ) →ₗ[ℝ] ((Fin 4 → FirstHistogram.Palette security) → ℝ) :=
  (averagedPairedChannel security compensatorRoot attachmentRoot).comp
    (reducePrimary (ActualControls.bodyReference security))

def ordinaryChannel (security : ℕ) (root : ℤ) :
    (Group security → ℝ) →ₗ[ℝ] ((Fin 1 → FirstHistogram.Palette security) → ℝ) :=
  (bodyChannel security root).comp (reduceBody (primaryLaw security))





def roleSlots (r s : ℕ) : (Fin r ⊕ Fin s) → Type
  | .inl _ => Fin 4
  | .inr _ => Fin 1

instance roleSlotsFintype (r s : ℕ) (index : Fin r ⊕ Fin s) : Fintype (roleSlots r s index) := by
  cases index with
  | inl _ => exact inferInstanceAs (Fintype (Fin 4))
  | inr _ => exact inferInstanceAs (Fintype (Fin 1))

def roleChannel (security r s : ℕ) (compensatorRoot attachmentRoot : Fin r → ℤ) (bodyRoot : Fin s → ℤ) :
    (index : Fin r ⊕ Fin s) → (Group security → ℝ) →ₗ[ℝ] ((roleSlots r s index → FirstHistogram.Palette security) → ℝ)
  | .inl index => primaryChannel security (compensatorRoot index) (attachmentRoot index)
  | .inr index => ordinaryChannel security (bodyRoot index)

def roleBound (security r s : ℕ) (multiple : ℝ) : Fin r ⊕ Fin s → ℝ
  | .inl _ => Real.sqrt (pairedConstant multiple / (Parameters.legCount security : ℝ))
  | .inr _ => Real.sqrt (32 * normalizedScale security multiple ^ 2)



def physicalSlots (r s : ℕ) (index : Fin (r + s)) : Type :=
  roleSlots r s (finSumFinEquiv.symm index)

instance physicalSlotsFintype (r s : ℕ) (index : Fin (r + s)) : Fintype (physicalSlots r s index) :=
  roleSlotsFintype r s (finSumFinEquiv.symm index)

def physicalChannel (security r s : ℕ) (compensatorRoot attachmentRoot : Fin r → ℤ) (bodyRoot : Fin s → ℤ)
    (index : Fin (r + s)) :
    (Group security → ℝ) →ₗ[ℝ] ((physicalSlots r s index → FirstHistogram.Palette security) → ℝ) :=
  roleChannel security r s compensatorRoot attachmentRoot bodyRoot (finSumFinEquiv.symm index)

/-- The actual mixed output of an arbitrary original canonical kernel.
The added independent coordinates are unused before applying the paired
physical response once, and every input remains in one joint finite sum. -/
def jointMass (security r s : ℕ) (compensatorRoot attachmentRoot : Fin r → ℤ) (bodyRoot : Fin s → ℤ)
    (kernel : DensityKernel (Primary := FirstHistogram.Palette security)
      (Body := ActualControls.SafePalette security) r s) :
    (Sigma (physicalSlots r s) → FirstHistogram.Palette security) → ℝ :=
  JointPhysicalChannel.mass (physicalSlots r s)
    (physicalChannel security r s compensatorRoot attachmentRoot bodyRoot) (finiteKernel kernel)



theorem physicalSlots_card (r s : ℕ) : Fintype.card (Sigma (physicalSlots r s)) = 4 * r + s := by
  rw [Fintype.card_sigma]
  change (∑ index : Fin (r + s), Fintype.card (roleSlots r s (finSumFinEquiv.symm index))) = _
  rw [finSumFinEquiv.symm.sum_comp (fun index : Fin r ⊕ Fin s => Fintype.card (roleSlots r s index))]
  simp [roleSlots, Fintype.sum_sum_type, mul_comm]







def jointConstant (r s : ℕ) (multiple : ℝ) : ℝ :=
  ((4 * r + s + 1 : ℕ) * ((5 : ℕ) ^ (r + s) : ℕ) * ((4 * (r + s)).factorial : ℝ)) *
    (pairedConstant multiple ^ r * (32 * multiple ^ 2) ^ s)





end

end CurrentAFT.JointTaggedPhysicalFock

end

section















/-! # Actual distinct primary/compensator/body selections and physical complements -/

namespace CurrentAFT.TaggedSelection

open AFT ActualBlockFock
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Actual distinct public control positions. A selected primary uses one
triple and one separate compensator center. Ordinary selections are
disjoint from those compensators. -/
structure Selection (security r s : ℕ) where
  primary : Fin r ↪ Fin (Parameters.legCount security)
  compensator : Fin r ↪ Fin (centerCount security)
  body : Fin s ↪ Fin (centerCount security)
  separated : ∀ first second, compensator first ≠ body second

abbrev RemovedLabel (r s : ℕ) := Fin r ⊕ (Fin r ⊕ Fin s)

def Selection.removedEmbedding {security r s : ℕ} (selection : Selection security r s) :
    RemovedLabel r s ↪ BlockIndex security where
  toFun
    | .inl index => .inl (selection.primary index)
    | .inr (.inl index) => .inr (.inl (selection.compensator index))
    | .inr (.inr index) => .inr (.inl (selection.body index))
  inj' := by
    intro first second hequal
    rcases first with first | first
    · rcases second with second | second
      · exact congrArg Sum.inl (selection.primary.injective (Sum.inl.inj hequal))
      · cases second <;> cases hequal
    · rcases first with first | first
      · rcases second with second | second
        · cases hequal
        · rcases second with second | second
          · exact congrArg (Sum.inr ∘ Sum.inl) (selection.compensator.injective (Sum.inl.inj (Sum.inr.inj hequal)))
          · exact False.elim (selection.separated first second (Sum.inl.inj (Sum.inr.inj hequal)))
      · rcases second with second | second
        · cases hequal
        · rcases second with second | second
          · exact False.elim (selection.separated second first (Sum.inl.inj (Sum.inr.inj hequal)).symm)
          · exact congrArg (Sum.inr ∘ Sum.inr) (selection.body.injective (Sum.inl.inj (Sum.inr.inj hequal)))

def Selection.removed {security r s : ℕ} (selection : Selection security r s) : Finset (BlockIndex security) :=
  Finset.univ.map selection.removedEmbedding

def Selection.kept {security r s : ℕ} (selection : Selection security r s) : Finset (BlockIndex security) :=
  Finset.univ \ selection.removed

theorem Selection.removed_card {security r s : ℕ} (selection : Selection security r s) :
    selection.removed.card = 2 * r + s := by
  simp only [Selection.removed, Finset.card_map, Finset.card_univ, RemovedLabel,
    Fintype.card_sum, Fintype.card_fin]
  omega

theorem Selection.removed_complement {security r s : ℕ} (selection : Selection security r s) :
    OmittedBlockMean.removed selection.kept = selection.removed := by
  ext index
  simp [OmittedBlockMean.removed, Selection.kept]

theorem Selection.removed_outputs {security r s : ℕ} (selection : Selection security r s) :
    (∑ index ∈ selection.removed, Fintype.card (Slots security index)) = 4 * r + s := by
  simp only [Selection.removed, Finset.sum_map]
  change (∑ label : RemovedLabel r s, Fintype.card (Slots security (selection.removedEmbedding label))) = _
  simp [RemovedLabel, Fintype.sum_sum_type, Selection.removedEmbedding, Slots]
  omega

theorem Selection.kept_outputs {security r s : ℕ} (selection : Selection security r s) :
    Fintype.card (Sigma (fun index : selection.kept => Slots security index.val)) + (4 * r + s) =
      Parameters.dimension security := by
  have hkept : Fintype.card (Sigma (fun index : selection.kept => Slots security index.val)) =
      ∑ index ∈ selection.kept, Fintype.card (Slots security index) := by
    rw [Fintype.card_sigma, Finset.sum_subtype selection.kept (fun _ => Iff.rfl)]
  have hfull : (∑ index : BlockIndex security, Fintype.card (Slots security index)) =
      Parameters.dimension security := by rw [← Fintype.card_sigma]; exact physical_card security
  have hsplit := Finset.sum_sdiff (f := fun index : BlockIndex security => Fintype.card (Slots security index))
    (Finset.subset_univ selection.removed)
  rw [← Selection.kept, selection.removed_outputs, hfull] at hsplit
  rw [hkept]
  exact hsplit

/-- Replacing each selected triple plus compensator by its real four-output
channel, and each selected ordinary center by a singleton, keeps exactly
the original full output dimension. -/
theorem Selection.full_output_card {security r s : ℕ} (selection : Selection security r s) :
    Fintype.card ((Sigma (JointTaggedPhysicalFock.physicalSlots r s)) ⊕
      Sigma (fun index : selection.kept => Slots security index.val)) = Parameters.dimension security := by
  rw [Fintype.card_sum, JointTaggedPhysicalFock.physicalSlots_card]
  have h := selection.kept_outputs
  omega

end

end CurrentAFT.TaggedSelection

end

section













/-! # Actual complement mean MGF after distinct public control selections -/

namespace CurrentAFT.ComplementMeanMGF

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy ActualBlockFock
  ActualBlockMean ActualCycleMeanMGF ConditionalHistogramMean ConditionalHistogramMGF
  PhysicalFockRates ActualFockBound TaggedSelection
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  BackgroundRates.radius

def linear (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (multiple : ℝ)
    (latent : BodyIndex security → Edge security) (index : BlockIndex security)
    (color : ActualBlockMean.Palette security) : ℝ :=
  BlockProducts.normalizedLinear (Slots security) (uniformReference security)
    (rootedLaw security layout queue permutation latent)
    (normalizedScale security (Real.sqrt 2 * multiple)) index color

def keptEnergy (security r s : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (multiple : ℝ)
    (selection : Selection security r s) (latent : BodyIndex security → Edge security) : ℝ :=
  ∑ color, (∑ index ∈ selection.kept, linear security layout queue permutation multiple latent index color) ^ 2





end

end CurrentAFT.ComplementMeanMGF

end

section











/-!
# Complete signed physical output for an actual selected joint coefficient

The selected paired four-output channels and singleton body channels are
multiplied by every unselected physical block, then averaged over the same
closed protected cycle. All output degrees, including full support, remain.
-/

namespace CurrentAFT.TaggedOutputFock

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy ActualBlockFock ActualBlockMean
  ActualCycleMeanMGF ConditionalHistogramMean PhysicalFockRates ActualFockBound TaggedSelection
  JointTaggedPhysicalFock ComplementMeanMGF ControlCoordinates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  BackgroundRates.radius

abbrev OutputIndex {security r s : ℕ} (selection : Selection security r s) :=
  Sigma (physicalSlots r s) ⊕ Sigma (fun index : selection.kept => Slots security index.val)

def taggedMass (security r s : ℕ) (selection : Selection security r s)
    (layout : RoleIndex security ≃ BodyIndex security) (permutation : Equiv.Perm (BodyIndex security))
    (latent : BodyIndex security → Edge security)
    (kernel : DensityKernel (Primary := ActualBlockMean.Palette security) (Body := ActualControls.SafePalette security) r s) :
    (Sigma (physicalSlots r s) → ActualBlockMean.Palette security) → ℝ :=
  jointMass security r s
    (fun index => centerRoots security layout permutation latent (selection.compensator index))
    (fun index => attachmentRoots security layout permutation latent (selection.primary index))
    (fun index => centerRoots security layout permutation latent (selection.body index)) kernel

def conditionalMass (security r s : ℕ) (selection : Selection security r s)
    (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (kernel : DensityKernel (Primary := ActualBlockMean.Palette security) (Body := ActualControls.SafePalette security) r s) :
    (OutputIndex selection → ActualBlockMean.Palette security) → ℝ :=
  BlockProducts.taggedBlockMass (fun index : selection.kept => Slots security index.val)
    (taggedMass security r s selection layout permutation latent kernel)
    (fun index : selection.kept => rootedLaw security layout queue permutation latent index.val)

def outputMass (security r s : ℕ) (selection : Selection security r s)
    (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security))
    (kernel : DensityKernel (Primary := ActualBlockMean.Palette security) (Body := ActualControls.SafePalette security) r s)
    (word : OutputIndex selection → ActualBlockMean.Palette security) : ℝ :=
  (latentLaw security).expectation (fun latent =>
    conditionalMass security r s selection layout queue permutation latent kernel word)

def inputSize (security r s : ℕ)
    (kernel : DensityKernel (Primary := ActualBlockMean.Palette security) (Body := ActualControls.SafePalette security) r s) : ℝ :=
  ControlNorm.gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) r s *
    ControlNorm.blockL2 (primaryLaw security) (ActualControls.bodyReference security) kernel



def outputConstant (r s : ℕ) (multiple : ℝ) : ℝ :=
  32 * Real.exp (2 * ((2 * r + s : ℕ) : ℝ) + 2) * jointConstant r s multiple





end

end CurrentAFT.TaggedOutputFock

end

end

section

section













/-! # Actual independent uniform distinct-index averages of complete physical outputs -/

namespace CurrentAFT.UniformTaggedOutput

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy ActualBlockFock ActualBlockMean
  ActualCycleMeanMGF ConditionalHistogramMean PhysicalFockRates ActualFockBound TaggedSelection
  JointTaggedPhysicalFock TaggedOutputFock ControlCoordinates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  BackgroundRates.radius BackgroundRates.ordinaryPool

theorem centerCount_split (security : ℕ) :
    Parameters.legCount security + BackgroundRates.ordinaryPool security = centerCount security := by
  have := population_room security
  unfold centerCount BackgroundRates.ordinaryPool
  omega

/-- A fixed public division of center positions into compensators and
ordinary controls. Arbitrary body layouts subsequently place this division. -/
def centerSplit (security : ℕ) :
    (Fin (Parameters.legCount security) ⊕ Fin (BackgroundRates.ordinaryPool security)) ≃ Fin (centerCount security) :=
  finSumFinEquiv.trans (finCongr (centerCount_split security))

def compensatorPosition (security : ℕ) : Fin (Parameters.legCount security) ↪ Fin (centerCount security) where
  toFun index := centerSplit security (.inl index)
  inj' _first _second hequal := Sum.inl.inj ((centerSplit security).injective hequal)

def ordinaryPosition (security : ℕ) : Fin (BackgroundRates.ordinaryPool security) ↪ Fin (centerCount security) where
  toFun index := centerSplit security (.inr index)
  inj' _first _second hequal := Sum.inr.inj ((centerSplit security).injective hequal)

abbrev Choice (security r s : ℕ) :=
  (Fin r ↪ Fin (Parameters.legCount security)) × (Fin s ↪ Fin (BackgroundRates.ordinaryPool security))

def selection (security r s : ℕ) (choice : Choice security r s) : Selection security r s where
  primary := choice.1
  compensator := choice.1.trans (compensatorPosition security)
  body := choice.2.trans (ordinaryPosition security)
  separated first second hequal := by
    have h := (centerSplit security).injective hequal
    cases h

def choiceLaw (security r s : ℕ) (hprimary : r ≤ Parameters.legCount security)
    (hbody : s ≤ BackgroundRates.ordinaryPool security) : FiniteDist (Choice security r s) := by
  letI : Nonempty (Fin r ↪ Fin (Parameters.legCount security)) := ⟨Fin.castLEEmb hprimary⟩
  letI : Nonempty (Fin s ↪ Fin (BackgroundRates.ordinaryPool security)) := ⟨Fin.castLEEmb hbody⟩
  exact (FiniteDist.uniform (Fin r ↪ Fin (Parameters.legCount security))).prod
    (FiniteDist.uniform (Fin s ↪ Fin (BackgroundRates.ordinaryPool security)))



def outputEquiv {security r s : ℕ} (chosen : Selection security r s) :
    OutputIndex chosen ≃ Fin (Parameters.dimension security) :=
  Fintype.equivFinOfCardEq chosen.full_output_card

def flatMass (security r s : ℕ) (chosen : Selection security r s)
    (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security))
    (kernel : DensityKernel (Primary := ActualBlockMean.Palette security) (Body := ActualControls.SafePalette security) r s) :
    (Fin (Parameters.dimension security) → ActualBlockMean.Palette security) → ℝ :=
  HistogramNormalization.renamedMass (outputEquiv chosen)
    (outputMass security r s chosen layout queue permutation kernel)

/-- The actual independent uniform distinct-index physical output, with
one fixed compensator placement and one common queue scalar. -/
def uMass (security r s : ℕ) (hprimary : r ≤ Parameters.legCount security)
    (hbody : s ≤ BackgroundRates.ordinaryPool security)
    (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security))
    (kernel : DensityKernel (Primary := ActualBlockMean.Palette security) (Body := ActualControls.SafePalette security) r s)
    (word : Fin (Parameters.dimension security) → ActualBlockMean.Palette security) : ℝ :=
  (choiceLaw security r s hprimary hbody).expectation (fun choice =>
    flatMass security r s (selection security r s choice) layout queue permutation kernel word)



end

end CurrentAFT.UniformTaggedOutput

end

section













/-!
# Whole finite coefficient families satisfy the actual full physical Fock bound

The scalar baseline and every original canonical joint coefficient use
their actual independent uniform selections. The same closed cycle and
queue are retained throughout. The Hilbert triangle bound combines all
arities without a palette-size factor.
-/

namespace CurrentAFT.CoefficientOutputFock

open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy ActualBlockFock ActualBlockMean
  ActualCycleMeanMGF ConditionalHistogramMean PhysicalFockRates ActualFockBound
  TaggedOutputFock UniformTaggedOutput ControlCoordinates ControlNorm
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  BackgroundRates.radius BackgroundRates.ordinaryPool

theorem primary_room (security order : ℕ) (hsecurity : 2 * order ≤ security) (arity : PositiveArity order) :
    arity.val.1.val ≤ Parameters.legCount security := by
  have h := FiniteAtomMoments.current_pool_room security order hsecurity arity.val.1.val arity.val.2.val arity.property.2
  omega

theorem body_room (security order : ℕ) (hsecurity : 2 * order ≤ security) (arity : PositiveArity order) :
    arity.val.2.val ≤ BackgroundRates.ordinaryPool security := by
  have h := FiniteAtomMoments.current_pool_room security order hsecurity arity.val.1.val arity.val.2.val arity.property.2
  omega

def baselineMass (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) :
    (Fin (Parameters.dimension security) → ActualBlockMean.Palette security) → ℝ :=
  HistogramNormalization.renamedMass (Fintype.equivFinOfCardEq (physical_card security))
    (outputLaw security layout queue permutation).weight

def familyMass (security order : ℕ) (hsecurity : 2 * order ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security))
    (coefficient : CoefficientSpace (primaryLaw security) (ActualControls.bodyReference security) order)
    (word : Fin (Parameters.dimension security) → ActualBlockMean.Palette security) : ℝ :=
  coefficient.1 * baselineMass security layout queue permutation word +
    ∑ arity : PositiveArity order, uMass security arity.val.1.val arity.val.2.val
      (primary_room security order hsecurity arity) (body_room security order hsecurity arity)
      layout queue permutation (coefficient.2 arity).val word

def normConstant (order : ℕ) (multiple : ℝ) : ℝ :=
  Real.sqrt (32 * Real.exp 2) + ∑ arity : PositiveArity order,
    Real.sqrt (outputConstant arity.val.1.val arity.val.2.val multiple)













end

end CurrentAFT.CoefficientOutputFock

end

section









/-!
# Actual finite color coordinates and the positive-sign character basis

The palette may be the implementation's `Fin q`. A fixed equivalence with
`ZMod q` supplies the actual additive characters. Parseval and the
centered-atom identities are proved on these finite sums, with no assumed
unitary table or replacement of the physical coefficient arrays.
-/

namespace CurrentAFT.FourierCoordinates

open AFT
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {Color Index : Type*} [Fintype Color] [Nonempty Color] [Fintype Index] [DecidableEq Index]
  {modulus : ℕ} [NeZero modulus]

def scalarCharacter (palette : Color ≃ ZMod modulus) (frequency : ZMod modulus) (color : Color) : ℂ :=
  AddChar.zmodAddEquiv frequency (palette color)

def fourier (palette : Color ≃ ZMod modulus) (mass : (Index → Color) → ℂ)
    (frequency : Index → ZMod modulus) : ℂ :=
  ∑ point, mass point * ∏ index, scalarCharacter palette (frequency index) (point index)

def uniformReference : FiniteDist Color := FiniteDist.uniform Color











end

end CurrentAFT.FourierCoordinates

end

section



/-! # Exact enumeration of all coordinate frequencies by their actual support -/

namespace CurrentAFT.FrequencySupport

open scoped BigOperators Classical

noncomputable section

variable {Index : Type*} [Fintype Index] {modulus : ℕ}

abbrev NonzeroFrequency (modulus : ℕ) := {frequency : ZMod modulus // frequency ≠ 0}

def support (frequency : Index → ZMod modulus) : Finset Index :=
  Finset.univ.filter (fun index => frequency index ≠ 0)

def extend (selected : Finset Index) (frequency : selected → ZMod modulus) : Index → ZMod modulus :=
  fun index => if h : index ∈ selected then frequency ⟨index, h⟩ else 0

def packed (selected : Finset Index) (frequency : selected → NonzeroFrequency modulus) : Index → ZMod modulus :=
  extend selected (fun index => (frequency index).val)

omit [Fintype Index] in
theorem packed_apply (selected : Finset Index) (frequency : selected → NonzeroFrequency modulus)
    (index : selected) : packed selected frequency index = (frequency index).val := by
  unfold packed extend
  split_ifs with h
  · rfl
  · exact False.elim (h index.property)

theorem support_packed (selected : Finset Index) (frequency : selected → NonzeroFrequency modulus) :
    support (packed selected frequency) = selected := by
  ext index
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hindex : index ∈ selected
  · simp only [packed, extend, dif_pos hindex]
    exact iff_of_true (frequency ⟨index, hindex⟩).property hindex
  · simp only [packed, extend, dif_neg hindex, ne_eq, not_true_eq_false]
    exact iff_of_false id hindex

theorem packed_injective : Function.Injective
    (fun point : Sigma (fun selected : Finset Index => selected → NonzeroFrequency modulus) => packed point.1 point.2) := by
  rintro ⟨first, firstWord⟩ ⟨second, secondWord⟩ hequal
  have hselected : first = second := by
    have h := congrArg support hequal
    simpa only [support_packed] using h
  subst second
  congr 1
  funext index
  apply Subtype.ext
  have h := congrFun hequal index.val
  simpa only [packed_apply] using h

theorem packed_surjective : Function.Surjective
    (fun point : Sigma (fun selected : Finset Index => selected → NonzeroFrequency modulus) => packed point.1 point.2) := by
  intro frequency
  let word : support frequency → NonzeroFrequency modulus :=
    fun index => ⟨frequency index.val, (Finset.mem_filter.mp index.property).2⟩
  refine ⟨⟨support frequency, word⟩, ?_⟩
  funext index
  by_cases hzero : frequency index = 0
  · have hnot : index ∉ support frequency := by simp [support, hzero]
    simp only [packed, extend, dif_neg hnot, hzero]
  · have hmem : index ∈ support frequency := by simp [support, hzero]
    simp only [packed, extend, dif_pos hmem, word]

/-- Every full frequency has one support and one nonzero word on that
support. No frequency of high or full support is discarded. -/
def encodingEquiv :
    Sigma (fun selected : Finset Index => selected → NonzeroFrequency modulus) ≃ (Index → ZMod modulus) :=
  Equiv.ofBijective (fun point => packed point.1 point.2) ⟨packed_injective, packed_surjective⟩

variable [NeZero modulus]





end

end CurrentAFT.FrequencySupport

end

section



/-!
# Complete finite-frequency support tails

This module formalizes the tail extraction in the proof of
`prop:df-corrected-weight-bounds` in the current manuscript. It sums every
remaining frequency, including those of full support. The input weighted
energy bound and low-support cancellation must still be established for the
actual protected endpoint law; this module does not assert either physical
estimate or the constructive AFT theorem.
-/

namespace CurrentAFT

open scoped BigOperators

noncomputable section

/-- The complete weighted energy on a specified finite frequency set. -/
def weightedSupportEnergy {Frequency : Type*} (frequencies : Finset Frequency)
    (supportDegree : Frequency → ℕ) (energy : Frequency → ℝ) (radius : ℝ) : ℝ :=
  ∑ frequency ∈ frequencies, radius ^ (2 * supportDegree frequency) * energy frequency









end

end CurrentAFT

end

section













/-!
# Exact support energy of the actual ordered homogeneous coefficient tensors

The coordinate characters diagonalize the actual finite Hoeffding
components. Complete Parseval on each selected coordinate space therefore
identifies every support-energy layer with the real color-frame tensor
energy already used by the physical local response bounds.
-/

namespace CurrentAFT.FourierSupportIsometry

open AFT FourierCoordinates FrequencySupport
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {Color Index : Type*} [Fintype Color] [Nonempty Color] [Fintype Index]
  {modulus : ℕ} [NeZero modulus]

/-- Actual Fourier transform of a selected canonical density component. -/
def componentFourier (palette : Color ≃ ZMod modulus) (mass : (Index → Color) → ℝ)
    (selected : Finset Index) (frequency : selected → ZMod modulus) : ℂ :=
  fourier palette (fun output =>
    (((FiniteDist.independent (fun _ : selected => uniformReference (Color := Color))).weight output *
      LocalTensors.restrictedComponent (fun _ : Index => uniformReference (Color := Color)) mass selected output : ℝ) : ℂ)) frequency











/-- Complete actual ordered-color-tensor Fock energy. Its coefficients
are extracted from the physical signed-law polynomial by `degreeTensor`. -/
def colorFockEnergy (mass : (Index → Color) → ℝ) (radius : ℝ) : ℝ :=
  HistogramTail.fockEnergy (Fintype.card Index) radius
    (fun degree => BlockFock.tensorEnergy
      (LocalTensors.degreeTensor (fun _ : Index => uniformReference (Color := Color)) mass degree))





end

end CurrentAFT.FourierSupportIsometry

end

section













/-!
# Complete weighted Fourier bound of the actual finite physical coefficient family

The common protected queue scalar and the independent whole-body permutation
are averaged after the complete physical response. The final independent
uniform endpoint permutation is literal finite symmetrization. Every
frequency, including zero and full support, occurs in the resulting bound.
-/

namespace CurrentAFT.ActualWeightedFourier

open AFT DiffuseProfiles ProposalPrimary ActualBlockMean ActualCycleMeanMGF
  ConditionalHistogramMean PhysicalFockRates ActualFockBound ControlCoordinates ControlNorm
  CoefficientOutputFock
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  BackgroundRates.radius

def randomizationLaw (security : ℕ) :
    FiniteDist (FirstHistogram.Scalar security × Equiv.Perm (BodyIndex security)) :=
  (scalarLaw security).prod (FiniteDist.uniform (Equiv.Perm (BodyIndex security)))

def mixedMass (security order : ℕ) (hroom : 2 * order ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security)
    (coefficient : CoefficientSpace (primaryLaw security) (ActualControls.bodyReference security) order)
    (word : Fin (Parameters.dimension security) → ActualBlockMean.Palette security) : ℝ :=
  (randomizationLaw security).expectation (fun sample =>
    familyMass security order hroom layout sample.1.val sample.2 coefficient word)

/-- The full signed endpoint law after the independent final permutation. -/
def signedOutputMass (security order : ℕ) (hroom : 2 * order ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security)
    (coefficient : CoefficientSpace (primaryLaw security) (ActualControls.bodyReference security) order) :
    (Fin (Parameters.dimension security) → ActualBlockMean.Palette security) → ℝ :=
  HistogramNormalization.symmetrizedMass (mixedMass security order hroom layout coefficient)





end

end CurrentAFT.ActualWeightedFourier

end

section













/-!
# Full physical Fourier tail with the weighted-energy premise discharged

The remaining cancellation premise is the explicit finite collection of
linear Fourier constraints to be solved by calibration. The complete
physical weighted norm is supplied by the actual-law proof.
-/

namespace CurrentAFT.ActualPhysicalTail

open AFT DiffuseProfiles ProposalPrimary ActualBlockMean ActualCycleMeanMGF
  ConditionalHistogramMean PhysicalFockRates ControlCoordinates ControlNorm
  CoefficientOutputFock ActualWeightedFourier
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.dimension BackgroundRates.radius

def analysisRadius (security : ℕ) : ℝ := BackgroundRates.radius security / Real.sqrt (Real.exp 1)

def coefficient (security order : ℕ) (hroom : 2 * order ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security)
    (input : CoefficientSpace (primaryLaw security) (ActualControls.bodyReference security) order)
    (frequency : Fin (Parameters.dimension security) → ZMod (Parameters.modulus security)) : ℂ :=
  FourierCoordinates.fourier (ZMod.finEquiv (Parameters.modulus security)).toEquiv
    (fun word => (signedOutputMass security order hroom layout input word : ℂ)) frequency





end

end CurrentAFT.ActualPhysicalTail

end

section












/-! Explicit physical endpoint numbering for the current construction.
Primary leg slots come first, in (leg,slot) order, followed by all singleton
centers and then queue slots. No chosen finite enumeration is executed. -/
namespace CurrentAFT.CurrentPhysicalNumbering
open AFT ActualBlockFock
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
attribute [local irreducible] Parameters.bodySize Parameters.legCount Parameters.dimension


def split (security : ℕ) : Sigma (Slots security) ≃
    ((Fin (Parameters.legCount security) × Fin 3) ⊕
      (Fin (centerCount security) ⊕ Fin (Parameters.modulus security))) where
  toFun
    | ⟨.inl leg, slot⟩ => .inl (leg, slot)
    | ⟨.inr (.inl center), _⟩ => .inr (.inl center)
    | ⟨.inr (.inr queue), _⟩ => .inr (.inr queue)
  invFun
    | .inl (leg, slot) => ⟨.inl leg, slot⟩
    | .inr (.inl center) => ⟨.inr (.inl center), (0 : Fin 1)⟩
    | .inr (.inr queue) => ⟨.inr (.inr queue), (0 : Fin 1)⟩
  left_inv := by
    rintro ⟨leg | (center | queue), slot⟩
    · rfl
    · change Fin 1 at slot
      have he : slot = 0 := Subsingleton.elim _ _
      subst slot
      rfl
    · change Fin 1 at slot
      have he : slot = 0 := Subsingleton.elim _ _
      subst slot
      rfl
  right_inv := by
    intro point
    rcases point with pair | rest
    · rcases pair with ⟨leg, slot⟩; rfl
    · rcases rest with center | queue <;> rfl

 theorem dimension_eq (security : ℕ) :
    Parameters.legCount security * 3 + (centerCount security + Parameters.modulus security) = Parameters.dimension security := by
  have h := ProposalPrimary.population_room security
  unfold centerCount Parameters.dimension
  omega


def numbering (security : ℕ) : Sigma (Slots security) ≃ Fin (Parameters.dimension security) :=
  (split security).trans (((Equiv.sumCongr finProdFinEquiv finSumFinEquiv).trans finSumFinEquiv).trans
    (finCongr (dimension_eq security)))

 

 

 



 

end CurrentAFT.CurrentPhysicalNumbering

end

section











/-! # Actual endpoint placement of selected paired groups and their complement -/
namespace CurrentAFT.PairedOutputPlacement
open AFT ActualBlockFock TaggedSelection TaggedOutputFock JointTaggedPhysicalFock
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def blockEquiv {security r s : ℕ} (selection : Selection security r s) :
    RemovedLabel r s ⊕ selection.kept ≃ BlockIndex security :=
  Equiv.ofBijective (Sum.elim selection.removedEmbedding Subtype.val) (by
    constructor
    · intro first second hequal
      rcases first with first | first <;> rcases second with second | second
      · exact congrArg Sum.inl (selection.removedEmbedding.injective hequal)
      · have hnot := (Finset.mem_sdiff.mp second.property).2
        dsimp only [Sum.elim_inl, Sum.elim_inr] at hequal
        apply False.elim
        apply hnot
        rw [← hequal]
        exact Finset.mem_map.mpr ⟨first, Finset.mem_univ _, rfl⟩
      · have hnot := (Finset.mem_sdiff.mp first.property).2
        dsimp only [Sum.elim_inl, Sum.elim_inr] at hequal
        apply False.elim
        apply hnot
        rw [hequal]
        exact Finset.mem_map.mpr ⟨second, Finset.mem_univ _, rfl⟩
      · exact congrArg Sum.inr (Subtype.ext hequal)
    · intro index
      by_cases hremoved : index ∈ selection.removed
      · obtain ⟨label, _, hequal⟩ := Finset.mem_map.mp hremoved
        exact ⟨Sum.inl label, hequal⟩
      · exact ⟨Sum.inr ⟨index, by simp [Selection.kept, hremoved]⟩, rfl⟩)

@[simp] theorem blockEquiv_removed {security r s : ℕ} (selection : Selection security r s)
    (index : RemovedLabel r s) : blockEquiv selection (.inl index) = selection.removedEmbedding index := rfl

@[simp] theorem blockEquiv_kept {security r s : ℕ} (selection : Selection security r s)
    (index : selection.kept) : blockEquiv selection (.inr index) = index.val := rfl

/-- The compensator is output zero; the three leg outputs follow it. -/
def roleRemovedEquiv {security r s : ℕ} (selection : Selection security r s) :
    Sigma (roleSlots r s) ≃ Sigma (fun index : RemovedLabel r s => Slots security (selection.removedEmbedding index)) where
  toFun
    | ⟨.inl index, slot⟩ => Fin.cases ⟨.inr (.inl index), (0 : Fin 1)⟩ (fun slot => ⟨.inl index, slot⟩) slot
    | ⟨.inr index, slot⟩ => ⟨.inr (.inr index), slot⟩
  invFun
    | ⟨.inl index, slot⟩ => ⟨.inl index, slot.succ⟩
    | ⟨.inr (.inl index), _⟩ => ⟨.inl index, (0 : Fin 4)⟩
    | ⟨.inr (.inr index), slot⟩ => ⟨.inr index, slot⟩
  left_inv := by
    rintro ⟨index | index, slot⟩
    · change Fin 4 at slot
      fin_cases slot <;> rfl
    · rfl
  right_inv := by
    rintro ⟨index | (index | index), slot⟩
    · rfl
    · have hequal : slot = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst slot
      rfl
    · rfl

def taggedRemovedEquiv {security r s : ℕ} (selection : Selection security r s) :
    Sigma (physicalSlots r s) ≃ Sigma (fun index : RemovedLabel r s => Slots security (selection.removedEmbedding index)) :=
  (Equiv.sigmaCongrLeft (β := roleSlots r s) finSumFinEquiv.symm).trans (roleRemovedEquiv selection)

def gather {security r s : ℕ} (selection : Selection security r s) :
    OutputIndex selection ≃ Sigma (Slots security) :=
  (Equiv.sumCongr (taggedRemovedEquiv selection) (Equiv.refl _)).trans
    ((Equiv.sumSigmaDistrib (fun index : RemovedLabel r s ⊕ selection.kept =>
      Slots security (blockEquiv selection index))).symm.trans
        (Equiv.sigmaCongrLeft (β := Slots security) (blockEquiv selection)))

@[simp] theorem gather_kept {security r s : ℕ} (selection : Selection security r s)
    (index : selection.kept) (slot : Slots security index.val) :
    gather selection (.inr ⟨index, slot⟩) = ⟨index.val, slot⟩ := rfl

def physicalRoleIndex (r s : ℕ) (index : Sigma (roleSlots r s)) : Sigma (physicalSlots r s) :=
  (Equiv.sigmaCongrLeft (β := roleSlots r s) finSumFinEquiv.symm).symm index

def primaryIndex {r s : ℕ} (index : Fin r) (slot : Fin 4) : Sigma (physicalSlots r s) :=
  physicalRoleIndex r s ⟨.inl index, slot⟩

def ordinaryIndex {r s : ℕ} (index : Fin s) (slot : Fin 1) : Sigma (physicalSlots r s) :=
  physicalRoleIndex r s ⟨.inr index, slot⟩

@[simp] theorem primaryIndex_fst {r s : ℕ} (index : Fin r) (slot : Fin 4) :
    (primaryIndex (s := s) index slot).fst = finSumFinEquiv (.inl index) := rfl

@[simp] theorem ordinaryIndex_fst {r s : ℕ} (index : Fin s) (slot : Fin 1) :
    (ordinaryIndex (r := r) index slot).fst = finSumFinEquiv (.inr index) := rfl

theorem gather_role {security r s : ℕ} (selection : Selection security r s)
    (index : Sigma (roleSlots r s)) :
    gather selection (.inl (physicalRoleIndex r s index)) =
      ⟨selection.removedEmbedding ((roleRemovedEquiv selection index).fst),
        (roleRemovedEquiv selection index).snd⟩ := by
  have hequal : taggedRemovedEquiv selection (physicalRoleIndex r s index) =
      roleRemovedEquiv selection index :=
    congrArg (roleRemovedEquiv selection)
      ((Equiv.sigmaCongrLeft (β := roleSlots r s) finSumFinEquiv.symm).apply_symm_apply index)
  exact congrArg (fun point : Sigma (fun label : RemovedLabel r s =>
      Slots security (selection.removedEmbedding label)) =>
        (⟨selection.removedEmbedding point.fst, point.snd⟩ : Sigma (Slots security))) hequal

@[simp] theorem gather_compensator {security r s : ℕ} (selection : Selection security r s) (index : Fin r) :
    gather selection (.inl (primaryIndex index 0)) =
      ⟨.inr (.inl (selection.compensator index)), (0 : Fin 1)⟩ := by
  rw [primaryIndex, gather_role]
  rfl

@[simp] theorem gather_primary {security r s : ℕ} (selection : Selection security r s)
    (index : Fin r) (slot : Fin 3) :
    gather selection (.inl (primaryIndex index slot.succ)) =
      ⟨.inl (selection.primary index), slot⟩ := by
  rw [primaryIndex, gather_role]
  rfl

@[simp] theorem gather_ordinary {security r s : ℕ} (selection : Selection security r s)
    (index : Fin s) (slot : Fin 1) :
    gather selection (.inl (ordinaryIndex index slot)) =
      ⟨.inr (.inl (selection.body index)), slot⟩ := by
  rw [ordinaryIndex, gather_role]
  rfl

end
end CurrentAFT.PairedOutputPlacement

end

section












/-! # Literal positive public channels before coefficient weighting -/
namespace CurrentAFT.PositivePublicChannels
open AFT FirstHistogram DiffuseProfiles ProposalPrimary LocalReferenceEnergy FixedPairedFirst
  PairedReferenceEnergy TaggedPhysicalFock PhysicalSynthesis OrdinaryPhysicalFock
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.dimension Parameters.legCount
  ProposalPrimary.primaryLaw ProposalPrimary.centerLaw

abbrev Palette (security : ℕ) := FirstHistogram.Palette security

/-- The actual positive leg conditioned on its public primary color. -/
def tripleGiven (security : ℕ) (root : ℤ) (primary : Palette security) : FiniteDist (Fin 3 → Palette security) :=
  (scalarLaw security).mix (fun scalar =>
    ((pairAt security primary scalar).prod (attachmentAt security root scalar)).map
      PhysicalBlockTensors.tripleEquiv.symm)





/-- A single protected scalar supplies both the pair and its attachment.
The compensator is the prescribed public center, translated by its root. -/
def quadGiven (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (group : PhysicalSynthesis.Group security) : FiniteDist (Fin 4 → Palette security) :=
  (scalarLaw security).mix (fun scalar => fixedControlLaw security compensatorRoot attachmentRoot scalar group)







/-- The ordinary channel is the actual public center followed by its
deterministic cyclic-root translation. -/
def bodyGiven (security : ℕ) (root : ℤ) (center : ActualControls.SafePalette security) :
    FiniteDist (Fin 1 → Palette security) :=
  (pointLaw security (shiftEquiv security root center.val)).map (fun color _ => color)









section FiniteTensor
variable {Index Input Control : Type*} [Fintype Index] [Fintype Input] [Fintype Control]
  [DecidableEq Index]



end FiniteTensor
end
end CurrentAFT.PositivePublicChannels

end

section










/-! # Exact removal of unused coordinates in the common control alphabet -/
namespace CurrentAFT.TensorPublicProjection
open AFT JointTaggedPhysicalFock
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance finDecEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _





section Generic
variable {Index Primary Body : Type*} [Fintype Index] [Fintype Primary] [Fintype Body]
  [DecidableEq Index]













end Generic



section TwoPools
variable {Primary Body Public : Type*} [Fintype Primary] [Fintype Body] [Fintype Public]



end TwoPools
end
end CurrentAFT.TensorPublicProjection

end

section










/-! # The actual selected controls controls before the signed physical response -/
namespace CurrentAFT.SelectedPublicChannels
open AFT DiffuseProfiles ProposalPrimary PositivePublicChannels JointTaggedPhysicalFock
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance finDecEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance groupDecEq (security : ℕ) : DecidableEq (Group security) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.dimension Parameters.legCount
  primaryLaw centerLaw

def primaryScore (security : ℕ) : (Group security → ℝ) →ₗ[ℝ] (Group security → ℝ) where
  toFun score controls := PhysicalSynthesis.pairedChannel security
    (reducePrimary (ActualControls.bodyReference security) score) (SafeControlGroups.unwrap security controls)
  map_add' first second := by funext controls; simp only [map_add, Pi.add_apply]
  map_smul' scalar score := by funext controls; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

def ordinaryScore (security : ℕ) : (Group security → ℝ) →ₗ[ℝ] (Group security → ℝ) where
  toFun score controls := reduceBody (primaryLaw security) score controls.2
  map_add' first second := by funext controls; simp only [map_add, Pi.add_apply]
  map_smul' scalar score := by funext controls; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

def roleScore (security r s : ℕ) : (Fin r ⊕ Fin s) →
    (Group security → ℝ) →ₗ[ℝ] (Group security → ℝ)
  | .inl _ => primaryScore security
  | .inr _ => ordinaryScore security

def roleLaw (security r s : ℕ) (compensatorRoot attachmentRoot : Fin r → ℤ) (bodyRoot : Fin s → ℤ) :
    (index : Fin r ⊕ Fin s) → Group security → FiniteDist (roleSlots r s index → FirstHistogram.Palette security)
  | .inl index, controls => quadGiven security (compensatorRoot index) (attachmentRoot index)
      (SafeControlGroups.unwrap security controls)
  | .inr index, controls => bodyGiven security (bodyRoot index) controls.2



def scoreChannel (security r s : ℕ) (index : Fin (r + s)) :
    (Group security → ℝ) →ₗ[ℝ] (Group security → ℝ) :=
  roleScore security r s (finSumFinEquiv.symm index)

def publicLaw (security r s : ℕ) (compensatorRoot attachmentRoot : Fin r → ℤ) (bodyRoot : Fin s → ℤ)
    (index : Fin (r + s)) (controls : Group security) :
    FiniteDist (physicalSlots r s index → FirstHistogram.Palette security) :=
  roleLaw security r s compensatorRoot attachmentRoot bodyRoot (finSumFinEquiv.symm index) controls

def selectedScore (security r s : ℕ)
    (kernel : ControlCoordinates.DensityKernel (Primary := FirstHistogram.Palette security)
      (Body := ActualControls.SafePalette security) r s) (controls : Fin (r + s) → Group security) : ℝ :=
  ∑ input, finiteKernel kernel input * ∏ index,
    scoreChannel security r s index (Pi.single (input index) 1) (controls index)





end
end CurrentAFT.SelectedPublicChannels

end

section












namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.PairedOutputProduct
end CurrentAFT.PairedOutputProduct
namespace CurrentAFT.PairedOutputProduct.remaining
end CurrentAFT.PairedOutputProduct.remaining
namespace CurrentAFT.PairedOutputProduct.selectedBodies
end CurrentAFT.PairedOutputProduct.selectedBodies
namespace CurrentAFT.PairedOutputProduct.selectedPairs
end CurrentAFT.PairedOutputProduct.selectedPairs




/-! # The actual positive public experiment weighted by coefficientWeight -/
namespace CurrentAFT.PublicOutputExperiment
open AFT DiffuseProfiles ProposalPrimary ActualBlockFock ActualBlockMean ActualCycleMeanMGF
  ConditionalHistogramMean UniformTaggedOutput TaggedSelection PairedOutputPlacement
  PositivePublicChannels SelectedPublicChannels ControlCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.dimension Parameters.legCount Parameters.bodySize
  BackgroundRates.ordinaryPool primaryLaw centerLaw

abbrev PublicIndex (security : ℕ) :=
  Fin (Parameters.legCount security) ⊕ Fin (BackgroundRates.ordinaryPool security)
abbrev PublicWord (security : ℕ) := PublicIndex security → SafeControlGroups.SafeGroup security

/-- All public controls are drawn before the protected sources. Ordinary
controls carry an independent unused primary coordinate. -/
def reference (security : ℕ) : FiniteDist (PublicWord security) :=
  FiniteDist.independent (fun _ => SafeControlGroups.reference security)

def actualWeight (security order : ℕ) (coefficient : ActualControls.Coefficients security order)
    (controls : PublicWord security) : ℝ :=
  PhysicalSynthesis.coefficientWeight security order (Parameters.legCount security)
    (BackgroundRates.ordinaryPool security) coefficient
    (fun index => SafeControlGroups.unwrap security (controls (.inl index)))
    (fun index => (controls (.inr index)).2)

def conditionalBlocks (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (controls : PublicWord security) : (index : BlockIndex security) → FiniteDist (Slots security index → ActualBlockMean.Palette security)
  | .inl leg => tripleGiven security (attachmentRoots security layout permutation latent leg) (controls (.inl leg)).1
  | .inr (.inl center) => bodyGiven security (centerRoots security layout permutation latent center)
      (controls ((centerSplit security).symm center)).2
  | .inr (.inr point) => rootedLaw security layout queue permutation latent (.inr (.inr point))

def conditionalLaw (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (controls : PublicWord security) : FiniteDist (Sigma (Slots security) → ActualBlockMean.Palette security) :=
  FiniteDist.retype (BlockProducts.blockLaw (Slots security) (conditionalBlocks security layout queue permutation latent controls))

/-- The signed weight depends only on public controls, outside every
protected-source average. No hidden observation enters its normalization. -/
def weightedConditionalMass (security order : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (coefficient : ActualControls.Coefficients security order)
    (word : Sigma (Slots security) → ActualBlockMean.Palette security) : ℝ :=
  (reference security).expectation (fun controls => actualWeight security order coefficient controls *
    (conditionalLaw security layout queue permutation latent controls).weight word)







def pairedWord (security : ℕ) (word : Sigma (Slots security) → ActualBlockMean.Palette security)
    (index : Fin (Parameters.legCount security)) : Fin 4 → ActualBlockMean.Palette security :=
  Fin.cons (word ⟨.inr (.inl (compensatorPosition security index)), (0 : Fin 1)⟩)
    (fun slot => word ⟨.inl index, slot⟩)

def ordinaryWord (security : ℕ) (word : Sigma (Slots security) → ActualBlockMean.Palette security)
    (index : Fin (BackgroundRates.ordinaryPool security)) : Fin 1 → ActualBlockMean.Palette security :=
  fun slot => word ⟨.inr (.inl (ordinaryPosition security index)), slot⟩

def physicalFactor (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (word : Sigma (Slots security) → ActualBlockMean.Palette security) :
    PublicIndex security → SafeControlGroups.SafeGroup security → ℝ
  | .inl index, control =>
    (FiniteDist.retype (quadGiven security (centerRoots security layout permutation latent (compensatorPosition security index))
      (attachmentRoots security layout permutation latent index) (SafeControlGroups.unwrap security control))).weight
      (pairedWord security word index)
  | .inr index, control =>
    (FiniteDist.retype (bodyGiven security (centerRoots security layout permutation latent (ordinaryPosition security index)) control.2)).weight
      (ordinaryWord security word index)

def queueFactor (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (word : Sigma (Slots security) → ActualBlockMean.Palette security) : ℝ :=
  ∏ point : Fin (Parameters.modulus security),
    (rootedLaw security layout queue permutation latent (.inr (.inr point))).weight
      (fun slot => word ⟨.inr (.inr point), slot⟩)

def placedEmbedding {security r s : ℕ} (choice : Choice security r s) : Fin (r + s) ↪ PublicIndex security :=
  finSumFinEquiv.symm.toEmbedding.trans (choice.1.sumMap choice.2)









end
end CurrentAFT.PublicOutputExperiment

end

section











namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.PairedKeptProduct
end CurrentAFT.PairedKeptProduct
namespace CurrentAFT.TaggedSelection
end CurrentAFT.TaggedSelection
namespace CurrentAFT.TaggedSelection.Selection
end CurrentAFT.TaggedSelection.Selection
namespace CurrentAFT.TaggedSelection.Selection.mk
end CurrentAFT.TaggedSelection.Selection.mk
namespace CurrentAFT.TaggedSelection.Selection.removedEmbedding
end CurrentAFT.TaggedSelection.Selection.removedEmbedding
namespace CurrentAFT.TaggedSelection.Selection.removedEmbedding.match_1
end CurrentAFT.TaggedSelection.Selection.removedEmbedding.match_1
namespace CurrentAFT.UniformTaggedOutput
end CurrentAFT.UniformTaggedOutput
namespace CurrentAFT.UniformTaggedOutput.selection
end CurrentAFT.UniformTaggedOutput.selection



/-! # Exact selected and unselected public output identities -/
namespace CurrentAFT.PublicOutputBridge
open AFT DiffuseProfiles ProposalPrimary ActualBlockFock ActualBlockMean ActualCycleMeanMGF
  ConditionalHistogramMean UniformTaggedOutput TaggedSelection PairedOutputPlacement
  PositivePublicChannels SelectedPublicChannels PublicOutputExperiment ControlCoordinates
  JointTaggedPhysicalFock
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.dimension Parameters.legCount Parameters.bodySize
  BackgroundRates.ordinaryPool primaryLaw centerLaw

def backgroundFactor (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security)
    (word : Sigma (Slots security) → ActualBlockMean.Palette security) (block : BlockIndex security) : ℝ :=
  (rootedLaw security layout queue permutation latent block).weight (fun slot => word ⟨block, slot⟩)





























end
end CurrentAFT.PublicOutputBridge

end

section












namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.SymmetrizedOutputRename
end CurrentAFT.SymmetrizedOutputRename




/-! # The literal public coefficient weight produces the constructed mass -/
namespace CurrentAFT.PublicCoefficientOutput
open AFT DiffuseProfiles ProposalPrimary ActualBlockFock ActualBlockMean ActualCycleMeanMGF
  ConditionalHistogramMean UniformTaggedOutput TaggedSelection PairedOutputPlacement
  PositivePublicChannels SelectedPublicChannels PublicOutputExperiment PublicOutputBridge
  ControlCoordinates CoefficientOutputFock ActualFockBound
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.dimension Parameters.legCount Parameters.bodySize
  BackgroundRates.ordinaryPool primaryLaw centerLaw

def conditionalFamilyMass (security order : ℕ) (hroom : 2 * order ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security))
    (latent : BodyIndex security → Edge security) (coefficient : ActualControls.Coefficients security order)
    (word : Sigma (Slots security) → ActualBlockMean.Palette security) : ℝ :=
  coefficient.1 * BlockProducts.blockMass (Slots security) (rootedLaw security layout queue permutation latent) word +
    ∑ arity : PositiveArity order,
      (choiceLaw security arity.val.1.val arity.val.2.val (primary_room security order hroom arity)
        (body_room security order hroom arity)).expectation (fun choice =>
          TaggedOutputFock.conditionalMass security arity.val.1.val arity.val.2.val
            (selection security arity.val.1.val arity.val.2.val choice) layout queue permutation latent
            (coefficient.2 arity).val (word ∘ gather (selection security arity.val.1.val arity.val.2.val choice)))



def outputLawGiven (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) (controls : PublicWord security) :
    FiniteDist (Sigma (Slots security) → ActualBlockMean.Palette security) :=
  (FiniteDist.retype (latentLaw security)).mix (fun latent => conditionalLaw security layout queue permutation latent controls)

def physicalFamilyMass (security order : ℕ) (hroom : 2 * order ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security) (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security))
    (coefficient : ActualControls.Coefficients security order) (word : Sigma (Slots security) → ActualBlockMean.Palette security) : ℝ :=
  (FiniteDist.retype (latentLaw security)).expectation (fun latent => conditionalFamilyMass security order hroom layout queue permutation latent coefficient word)

/-- This is the actual positive protected-source experiment, with its
public coefficient weight outside the entire closed-cycle source average. -/
def weightedPhysicalMass (security order : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (BodyIndex security)) (coefficient : ActualControls.Coefficients security order)
    (word : Sigma (Slots security) → ActualBlockMean.Palette security) : ℝ :=
  (reference security).expectation (fun controls => actualWeight security order coefficient controls *
    (outputLawGiven security layout queue permutation controls).weight word)





/-- The arithmetic endpoint numbering is executable. Uniform endpoint
permutations make the resulting distribution invariant under this choice. -/
def flatten (security : ℕ) : Sigma (Slots security) ≃ Fin (Parameters.dimension security) :=
  CurrentPhysicalNumbering.numbering security



end
end CurrentAFT.PublicCoefficientOutput

end

section












namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.ActualWeightedFourier
end CurrentAFT.ActualWeightedFourier




/-! # The actual public weight and the final signed endpoint experiment -/
namespace CurrentAFT.PublicSignedOutput
open AFT DiffuseProfiles ProposalPrimary ActualBlockFock ActualBlockMean ActualCycleMeanMGF
  ConditionalHistogramMean PublicOutputExperiment PublicCoefficientOutput HistogramNormalization
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.dimension Parameters.legCount Parameters.bodySize
  BackgroundRates.ordinaryPool primaryLaw centerLaw

/-- One common queue scalar and one independent uniform whole-body
permutation are used for all local factors of this positive public kernel. -/
def rawLawGiven (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (controls : PublicWord security) : FiniteDist (Fin (Parameters.dimension security) → ActualBlockMean.Palette security) :=
  (FiniteDist.retype (ActualWeightedFourier.randomizationLaw security)).mix (fun sample =>
    (outputLawGiven security layout sample.1.val sample.2 controls).map (renameWord (flatten security)))

/-- The final independent endpoint permutation is a genuine finite positive
sampler. The public controls remain unchanged. -/
def lawGiven (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (controls : PublicWord security) : FiniteDist (Fin (Parameters.dimension security) → ActualBlockMean.Palette security) :=
  AFT.symmetrize (rawLawGiven security layout controls)

/-- The original coefficientWeight is evaluated on public controls before
the entire protected source and the two permutation draws. -/
def signedMass (security order : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (coefficient : ActualControls.Coefficients security order)
    (word : Fin (Parameters.dimension security) → ActualBlockMean.Palette security) : ℝ :=
  (reference security).expectation (fun controls => actualWeight security order coefficient controls *
    (lawGiven security layout controls).weight word)









section Rates
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq





def coefficient (security order : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (input : ActualControls.Coefficients security order)
    (frequency : Fin (Parameters.dimension security) → ZMod (Parameters.modulus security)) : ℂ :=
  FourierCoordinates.fourier (ZMod.finEquiv (Parameters.modulus security)).toEquiv
    (fun word => (signedMass security order layout input word : ℂ)) frequency





end Rates

end
end CurrentAFT.PublicSignedOutput

end

section













namespace CurrentAFT
end CurrentAFT




/-! # The source-independent public data needed for the actual charge test

The Fourier experiment conditions only on the score controls. Its positive
kernel has already averaged public anchor, blur, and baseline draws. Those
draws are made explicit here before any protected scalar or cycle is read.
-/
namespace CurrentAFT.ActualPublicCharge
open AFT DiffuseProfiles ProposalPrimary FirstHistogram LocalReferenceEnergy ActualBlockFock
  ActualBlockMean ActualCycleMeanMGF ConditionalHistogramMean PublicOutputExperiment
  PublicCoefficientOutput PublicSignedOutput
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  primaryLaw centerLaw safeLaw

abbrev Palette (security : ℕ) := FirstHistogram.Palette security



abbrev LegCore (security : ℕ) := ActualPublicLegCharge.PublicSeed security × Palette security

/-- The public leg shift seed and its independent attachment baseline are
sampled without reading any protected scalar or closed-cycle latent. -/
def legCoreLaw (security : ℕ) : FiniteDist (LegCore security) :=
  (ActualPublicLegCharge.seedLaw security).prod (safeLaw security)

structure Core (security : ℕ) where
  controls : PublicWord security
  legs : Fin (Parameters.legCount security) → LegCore security
  queueBaselines : Fin (Parameters.modulus security) → Palette security
  bodyPermutation : Equiv.Perm (BodyIndex security)
  endpointPermutation : Equiv.Perm (Fin (Parameters.dimension security))

instance coreFintype (security : ℕ) : Fintype (Core security) := by
  classical
  let source := (((PublicWord security × (Fin (Parameters.legCount security) → LegCore security)) ×
    (Fin (Parameters.modulus security) → Palette security)) × Equiv.Perm (BodyIndex security)) ×
      Equiv.Perm (Fin (Parameters.dimension security))
  exact Fintype.ofEquiv source
    { toFun := fun draw => ⟨draw.1.1.1.1, draw.1.1.1.2, draw.1.1.2, draw.1.2, draw.2⟩
      invFun := fun core => ((((core.controls, core.legs), core.queueBaselines), core.bodyPermutation), core.endpointPermutation)
      left_inv := by rintro ⟨⟨⟨⟨controls, legs⟩, baselines⟩, body⟩, endpoints⟩; rfl
      right_inv := by intro core; cases core; rfl }

def proposal (security : ℕ) : FiniteDist (Core security) :=
  (((PublicOutputExperiment.reference security).prod
      (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legCoreLaw security))).prod
      (FiniteDist.independent (fun _ : Fin (Parameters.modulus security) => safeLaw security)) |>.prod
      (FiniteDist.uniform (Equiv.Perm (BodyIndex security))) |>.prod
      (FiniteDist.uniform (Equiv.Perm (Fin (Parameters.dimension security))))).map
    (fun draw => ⟨draw.1.1.1.1, draw.1.1.1.2, draw.1.1.2, draw.1.2, draw.2⟩)

def pulledWeight (security order : ℕ) (coefficient : ActualControls.Coefficients security order)
    (core : Core security) : ℝ := actualWeight security order coefficient core.controls

/-- The fresh public coordinates conditional on the original score
controls; this law still contains no protected source sample. -/
def localSeedsLaw (security : ℕ) :
    FiniteDist ((Fin (Parameters.legCount security) → LegCore security) ×
      (Fin (Parameters.modulus security) → Palette security)) :=
  (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legCoreLaw security)).prod
    (FiniteDist.independent (fun _ : Fin (Parameters.modulus security) => safeLaw security))

def bodyPermutationLaw (security : ℕ) : FiniteDist (Equiv.Perm (BodyIndex security)) :=
  FiniteDist.uniform _

def endpointPermutationLaw (security : ℕ) : FiniteDist (Equiv.Perm (Fin (Parameters.dimension security))) :=
  FiniteDist.uniform _

def auxiliaryLaw (security : ℕ) (controls : PublicWord security) : FiniteDist (Core security) :=
  (((localSeedsLaw security).prod (bodyPermutationLaw security)).prod
      (endpointPermutationLaw security)).map
    (fun draw => ⟨controls, draw.1.1.1, draw.1.1.2, draw.1.2, draw.2⟩)















def legShift (security : ℕ) (core : Core security) (leg : Fin (Parameters.legCount security)) : ℤ :=
  ActualPublicLegCharge.publicShift security (core.controls (.inl leg)).1 (core.legs leg).1

/-- The complete public numerator includes all body baselines and leg
shifts. It contains no protected source input. -/
def chargeValue (security : ℕ) (core : Core security) : ZMod (Parameters.modulus security) :=
  (∑ leg, ((core.controls (.inl leg)).2.val.val : ℤ)) +
    (∑ center, ((core.controls (.inr center)).2.val.val : ℤ)) +
    (∑ leg, ((core.legs leg).2.val : ℤ)) +
    (∑ point, ((core.queueBaselines point).val : ℤ)) +
    (∑ leg, legShift security core leg) - (Parameters.legCount security : ℤ)

def publicCharge (security : ℕ) (core : Core security) : Prop := chargeValue security core = 0

def attachmentPosition (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) :
    Fin (Parameters.legCount security) ↪ BodyIndex security where
  toFun leg := layout (.inr (.inr leg))
  inj' _first _second hequal := Sum.inr.inj (Sum.inr.inj (layout.injective hequal))

def queuePosition (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) :
    Fin (Parameters.modulus security) ↪ BodyIndex security where
  toFun point := layout (.inr (.inl point))
  inj' _first _second hequal := Sum.inl.inj (Sum.inr.inj (layout.injective hequal))

def queueSet (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) : Finset (BodyIndex security) :=
  Finset.univ.map (queuePosition security layout)



def centerAt (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (vertex : BodyIndex security) : ℤ :=
  match layout.symm vertex with
  | .inl center => (core.controls ((UniformTaggedOutput.centerSplit security).symm center)).2.val.val
  | .inr (.inl point) => (core.queueBaselines point).val
  | .inr (.inr leg) => (core.legs leg).2.val

theorem sum_centerAt (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security) :
    (∑ vertex, centerAt security layout core vertex) =
      (∑ leg, ((core.controls (.inl leg)).2.val.val : ℤ)) +
      (∑ center, ((core.controls (.inr center)).2.val.val : ℤ)) +
      (∑ leg, ((core.legs leg).2.val : ℤ)) +
      (∑ point, ((core.queueBaselines point).val : ℤ)) := by
  unfold centerAt
  let value : RoleIndex security → ℤ := fun role => match role with
    | .inl center => ((core.controls ((UniformTaggedOutput.centerSplit security).symm center)).2.val.val : ℤ)
    | .inr (.inl point) => ((core.queueBaselines point).val : ℤ)
    | .inr (.inr leg) => ((core.legs leg).2.val : ℤ)
  change (∑ vertex, value (layout.symm vertex)) = _
  rw [Equiv.sum_comp layout.symm value]
  dsimp only [value]
  simp only [Fintype.sum_sum_type]
  have hcontrol : (∑ center, ((core.controls ((UniformTaggedOutput.centerSplit security).symm center)).2.val.val : ℤ)) =
      ∑ index : PublicIndex security, ((core.controls index).2.val.val : ℤ) := by
    convert Equiv.sum_comp (UniformTaggedOutput.centerSplit security).symm
      (fun index => ((core.controls index).2.val.val : ℤ)) using 1
  calc
    _ = (∑ index : PublicIndex security, ((core.controls index).2.val.val : ℤ)) +
        ((∑ point, ((core.queueBaselines point).val : ℤ)) +
          ∑ leg, ((core.legs leg).2.val : ℤ)) := by
      apply congrArg₂ (· + ·)
      · exact hcontrol
      · rfl
    _ = _ := by simp only [Fintype.sum_sum_type]; abel

theorem publicCharge_iff (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security) :
    PublicCharge.PublicChargeTest (Parameters.modulus security) (centerAt security layout core)
      (legShift security core) ↔ publicCharge security core := by
  unfold PublicCharge.PublicChargeTest publicCharge chargeValue
  rw [sum_centerAt]
  simp only [Fintype.card_fin, Int.cast_add, Int.cast_natCast, Int.cast_sum, sub_eq_zero]





end
end CurrentAFT.ActualPublicCharge

end

section










/-! # The real public leg seed fixes the protected pair's integer charge

The seed is sampled before the protected scalar. Its marked branch is the
actual inward anchor point and its diffuse branch is the actual ordered
trimmed pair slice. Both branches have the same exact integer pair sum.
-/
namespace CurrentAFT.ActualPublicLegCharge
open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy FirstHistogram InwardAnchor
open scoped BigOperators Classical Fin.NatCast
noncomputable section
local instance chargeFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance chargeModulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
abbrev Palette (security : ℕ) := ActualControls.Palette security

theorem finEquiv_natCast (modulus : ℕ) [NeZero modulus] (color : Fin modulus) :
    (ZMod.finEquiv modulus) color = (color.val : ZMod modulus) := by
  cases modulus with
  | zero => exact Fin.elim0 color
  | succ modulus =>
      change color = (color.val : Fin (modulus + 1))
      exact (Fin.cast_val_eq_self color).symm



def markedPoint (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security)
    (seed : PublicSeed security) : Palette security :=
  shiftEquiv security (seed.blur.1.val - seed.blur.2.val)
    (point security primary seed.coin seed.anchorIndex (-scalar.val)
      (by simpa only [abs_neg] using InwardAnchor.scalar_bound security scalar))



def markedLaw (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security)
    (seed : PublicSeed security) : FiniteDist (Palette security × Palette security) :=
  (FiniteDist.uniform Unit).map (fun _ => (primary, markedPoint security primary scalar seed))



theorem diffuse_shift_clearance (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security)
    (seed : PublicSeed security) :
    2 * (1 : ℤ) + |publicShift security primary seed - scalar.val| < Parameters.modulus security := by
  have habs := (abs_sub (publicShift security primary seed) scalar.val).trans
    (add_le_add (publicShift_bound security primary seed) (InwardAnchor.scalar_bound security scalar))
  have hclear := DiffuseProfiles.deletion_clearance security
  simp only [DiffuseProfiles.deletion] at hclear
  omega

def diffuseLaw (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security)
    (seed : PublicSeed security) : FiniteDist (Palette security × Palette security) where
  weight pair := TrimmedSlice.orderedPairSlice (Parameters.modulus security) 1
    (publicShift security primary seed - scalar.val) pair.1 pair.2
  nonneg pair := TrimmedSlice.orderedPairSlice_nonneg _ _ _ _ _
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [TrimmedSlice.orderedPairSlice_marginal (Parameters.modulus security) 1
      (publicShift security primary seed - scalar.val) (by norm_num)]
    exact TrimmedSlice.law_palette_mass _ _ _ (by norm_num) (diffuse_shift_clearance security primary scalar seed)

def refinedPair (security : ℕ) (primary : Palette security) (scalar : FirstHistogram.Scalar security)
    (seed : PublicSeed security) : FiniteDist (Palette security × Palette security) :=
  if seed.marked then markedLaw security primary scalar seed else diffuseLaw security primary scalar seed










end
end CurrentAFT.ActualPublicLegCharge

end

section




/-!
# The current simultaneous flag and affine-map calibration

The marked branch is allowed on an entire set of protected inputs.  In
particular this is not the older one-feature, small-atom chart theorem.
The deletion operator below is the actual masked feature projection.  Its
inverse is controlled by the manuscript's one-sided marked-defect budget.
-/

namespace CurrentAFT.AffineFlagCalibration

open AFT AFT.BoundaryCalibration
open scoped BigOperators Classical

noncomputable section

variable {Ω C I : Type*} [Fintype Ω] [Fintype C] [Fintype I]

/-- The exact geometric bound, with a variable contraction budget. -/
theorem solve_sub_norm_le (D : (Ω → ℝ) →L[ℝ] (Ω → ℝ))
    (hD : ‖D‖ < 1) (b : ℝ) (hb : b < 1) (hDb : ‖D‖ ≤ b)
    (f : Ω → ℝ) :
    ‖neumannSolve D hD f - f‖ ≤ b / (1 - b) * ‖f‖ := by
  let h := neumannSolve D hD f
  have heq : h - f = D h := by
    have hs := neumannSolve_equation D hD f
    change h - D h = f at hs
    rw [← hs]
    abel
  have htri : ‖h‖ ≤ ‖h - f‖ + ‖f‖ := by
    simpa only [sub_add_cancel] using norm_add_le (h - f) f
  have hop : ‖h - f‖ ≤ b * ‖h‖ := by
    rw [heq]
    exact (D.le_opNorm h).trans
      (mul_le_mul_of_nonneg_right hDb (norm_nonneg _))
  have hb0 : 0 ≤ b := (norm_nonneg D).trans hDb
  have hh : (1 - b) * ‖h - f‖ ≤ b * ‖f‖ := by
    nlinarith [mul_le_mul_of_nonneg_left htri hb0]
  change ‖h - f‖ ≤ _
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith : 0 < 1 - b)]
  nlinarith

/-- A one-sided defect estimate survives the actual inverse. -/
theorem solve_pointwise_upper (D : (Ω → ℝ) →L[ℝ] (Ω → ℝ))
    (hD : ‖D‖ < 1) (b : ℝ) (hb : b < 1) (hDb : ‖D‖ ≤ b)
    (f : Ω → ℝ) (upper magnitude : ℝ)
    (hf : ∀ x, f x ≤ upper) (hnorm : ‖f‖ ≤ magnitude) (x : Ω) :
    neumannSolve D hD f x ≤ upper + b / (1 - b) * magnitude := by
  have hb0 : 0 ≤ b := (norm_nonneg D).trans hDb
  have hpoint := (norm_le_pi_norm (neumannSolve D hD f - f) x).trans
    (solve_sub_norm_le D hD b hb hDb f)
  change |neumannSolve D hD f x - f x| ≤ _ at hpoint
  have hm := mul_le_mul_of_nonneg_left hnorm
    (div_nonneg hb0 (by linarith : 0 ≤ 1 - b))
  linarith [(abs_le.mp hpoint).2, hf x]

/-- The density correction deliberately leaves every marked-line component
unchanged, rather than only one distinguished input. -/
def offLineDefect (p : FiniteDist Ω) (features : I → Ω → C)
    (allowed : I → Finset C) (line : I → Prop) (spike : Ω → ℝ) : Ω → ℝ :=
  ∑ i, if line i then 0 else featureProjection p (features i) (allowed i) spike

theorem offLineDefect_mean [Nonempty C] (p : FiniteDist Ω)
    (features : I → Ω → C) (allowed : I → Finset C) (line : I → Prop)
    (spike : Ω → ℝ)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C) :
    expectation p (offLineDefect p features allowed line spike) = 0 := by
  rw [offLineDefect, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  split_ifs
  · exact map_zero _
  · exact featureProjection_mean p _ (hfeature i) _ spike

theorem offLineDefect_projected [Nonempty C] (p : FiniteDist Ω)
    (features : I → Ω → C) (allowed : I → Finset C) (line : I → Prop)
    (spike : Ω → ℝ)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C)
    (hpair : ∀ i j, i ≠ j → p.map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C)) :
    combinedProjection p features allowed (offLineDefect p features allowed line spike) =
      offLineDefect p features allowed line spike := by
  rw [offLineDefect, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · exact map_zero _
  · exact combinedProjection_feature p features allowed hfeature hpair i spike

theorem offLineDefect_component [Nonempty C] (p : FiniteDist Ω)
    (features : I → Ω → C) (allowed : I → Finset C) (line : I → Prop)
    (spike : Ω → ℝ)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C)
    (hpair : ∀ i j, i ≠ j → p.map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C)) (i : I) :
    featureProjection p (features i) (allowed i)
      (offLineDefect p features allowed line spike) =
      if line i then 0 else featureProjection p (features i) (allowed i) spike := by
  rw [offLineDefect, map_sum, Finset.sum_eq_single i]
  · split_ifs
    · exact map_zero _
    · exact congrArg (fun L : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) => L spike)
        (featureProjection_idempotent p (features i) (hfeature i) (allowed i))
  · intro j _ hji
    split_ifs
    · exact map_zero _
    · exact congrArg (fun L : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) => L spike)
        (featureProjection_orthogonal p (features i) (features j) (hpair i j hji.symm)
          (allowed i) (allowed j))
  · simp

/-- A normalized supported color density has average at least one on its
allowed palette.  This is the extra one-sided gain needed at atom `1/2`. -/
theorem centered_palette_bounds [Nonempty C] (allowed : Finset C)
    (g : C → ℝ) (M : ℝ) (hM : 1 ≤ M)
    (hg0 : ∀ c, 0 ≤ g c) (hgM : ∀ c, g c ≤ M)
    (hzero : ∀ c ∉ allowed, g c = 0)
    (hsum : ∑ c, g c = Fintype.card C) (c : C) :
    |centerAllowed allowed g c| ≤ M ∧ centerAllowed allowed g c ≤ M - 1 := by
  have hsumA : ∑ a ∈ allowed, g a = (Fintype.card C : ℝ) := by
    rw [← hsum]
    exact Finset.sum_subset (Finset.subset_univ _) (fun a _ ha => hzero a ha)
  have hcard : 0 < allowed.card := by
    by_contra hn
    have he : allowed = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [he] at hsumA
    simp only [Finset.sum_empty] at hsumA
    exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hsumA.symm
  have hcR : (0 : ℝ) < allowed.card := Nat.cast_pos.mpr hcard
  have havg1 : 1 ≤ (∑ a ∈ allowed, g a) / allowed.card := by
    rw [hsumA, le_div_iff₀ hcR, one_mul]
    exact_mod_cast (Finset.card_le_card (Finset.subset_univ allowed))
  have havgM : (∑ a ∈ allowed, g a) / allowed.card ≤ M := by
    apply (div_le_iff₀ hcR).mpr
    calc
      _ ≤ ∑ _a ∈ allowed, M := Finset.sum_le_sum (fun a _ => hgM a)
      _ = _ := by simp; ring
  rw [centerAllowed_apply]
  split_ifs with hc
  · constructor
    · apply abs_le.mpr
      constructor <;> linarith [hg0 c, hgM c]
    · linarith [hgM c]
  · exact ⟨by simpa using (le_trans (by norm_num : (0 : ℝ) ≤ 1) hM), by linarith⟩

/-- The manuscript's two separate bounds: the upper defect is smaller by the
deleted fraction, while its absolute norm may be of order the input count. -/
theorem offLineDefect_bounds [Nonempty Ω] [Nonempty C] (p : FiniteDist Ω)
    (features : I → Ω → C) (allowed : I → Finset C) (line : I → Prop)
    (spike : Ω → ℝ) (hmean : expectation p spike = 1)
    (hspike : ∀ x, 0 ≤ spike x)
    (hallowed : ∀ i, ¬ line i → ∀ x, features i x ∉ allowed i → spike x = 0)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hbound : ∀ i, ¬ line i → ∀ c, conditional p (features i) spike c ≤ 1 / (1 - δ)) :
    ‖offLineDefect p features allowed line spike‖ ≤ Fintype.card I / (1 - δ) ∧
      ∀ x, offLineDefect p features allowed line spike x ≤
        Fintype.card I * δ / (1 - δ) := by
  have hM : 1 ≤ 1 / (1 - δ) := by
    apply (le_div_iff₀ (by linarith : 0 < 1 - δ)).mpr
    linarith
  have hcomp (i : I) (hi : ¬ line i) (x : Ω) :
      |featureProjection p (features i) (allowed i) spike x| ≤ 1 / (1 - δ) ∧
      featureProjection p (features i) (allowed i) spike x ≤ 1 / (1 - δ) - 1 := by
    apply centered_palette_bounds (allowed i) (conditional p (features i) spike) _ hM
    · intro c
      rw [conditional_apply, expectation_apply]
      apply mul_nonneg (Nat.cast_nonneg _)
      apply Finset.sum_nonneg
      intro a _
      exact mul_nonneg (p.nonneg a) (by split_ifs; exacts [hspike a, le_rfl])
    · exact hbound i hi
    · intro c hc
      exact conditional_outside_zero p (features i) (allowed i)
        (fun x => features i x ∈ allowed i) spike
        (fun x hx => hallowed i hi x hx) (fun _ hx => hx) c hc
    · rw [conditional_sum, hmean, mul_one]
  have habs (x : Ω) : |offLineDefect p features allowed line spike x| ≤
      (Fintype.card I : ℝ) * (1 / (1 - δ)) := by
    rw [offLineDefect, Finset.sum_apply]
    calc
      _ ≤ ∑ i : I, |(if line i then 0 else
          featureProjection p (features i) (allowed i) spike) x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : I, (1 / (1 - δ) : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : line i
        · simp only [if_pos hi, Pi.zero_apply, abs_zero]; positivity
        · simpa only [if_neg hi] using (hcomp i hi x).1
      _ = _ := by simp
  constructor
  · rw [← mul_one_div]
    exact (pi_norm_le_iff_of_nonneg (by positivity)).mpr habs
  · intro x
    rw [offLineDefect, Finset.sum_apply]
    calc
      _ ≤ ∑ _i : I, (1 / (1 - δ) - 1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : line i
        · simp only [if_pos hi, Pi.zero_apply]; linarith
        · simpa only [if_neg hi] using (hcomp i hi x).2
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp [show 1 - δ ≠ 0 by linarith]
        ring

/- The current positive regular branch, simultaneously calibrated at every
protected input.  Only concrete deletion probabilities and marked color
counts are premises; invertibility and positivity are conclusions. -/
/-- The exact regular-branch witness. Its formula is public and contains
no hidden protected input. The proof argument only certifies the already
computed finite deletion response. -/
def regularDensity (p : FiniteDist Ω) (features : I → Ω → C)
    (allowed : I → Finset C) (line : I → Prop) (safe : Ω → Prop) [DecidablePred safe]
    (atom : ℝ) (spike : Ω → ℝ)
    (hD : ‖deletion (chartProjection p features allowed) safe‖ < 1) : Ω → ℝ :=
  safeMask safe (neumannSolve (deletion (chartProjection p features allowed) safe) hD
    (1 - (atom / (1 - atom)) • offLineDefect p features allowed line spike))

theorem regularDensity_properties [Nonempty Ω] [Nonempty C] (p : FiniteDist Ω)
    (features : I → Ω → C) (allowed : I → Finset C) (line : I → Prop)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C)
    (hpair : ∀ i j, i ≠ j → p.map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C))
    (safe : Ω → Prop) [DecidablePred safe]
    (hallowed : ∀ i x, safe x → features i x ∈ allowed i)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hglobal : expectation p (badIndicator safe) ≤ δ)
    (hconditional : ∀ i c, c ∈ allowed i →
      conditional p (features i) (badIndicator safe) c ≤ δ)
    (hsmall : (2 * Fintype.card I + 1) * δ ≤ 1 / 4)
    (hpositivity : (Fintype.card I : ℝ) / (1 - δ) *
      (δ + ((2 * Fintype.card I + 1) * δ) /
        (1 - (2 * Fintype.card I + 1) * δ)) ≤ 1 / 3)
    (atom : ℝ) (ha0 : 0 ≤ atom) (haHalf : atom ≤ 1 / 2)
    (spike : Ω → ℝ) (hsmean : expectation p spike = 1)
    (hsnonneg : ∀ x, 0 ≤ spike x)
    (hsallowed : ∀ i, ¬ line i → ∀ x, features i x ∉ allowed i → spike x = 0)
    (hsbound : ∀ i, ¬ line i → ∀ c,
      conditional p (features i) spike c ≤ 1 / (1 - δ))
    (hD' : ‖deletion (chartProjection p features allowed) safe‖ < 1) :
    let regular := regularDensity p features allowed line safe atom spike hD';
      expectation p regular = 1 ∧ (∀ x, 0 ≤ regular x) ∧
      (∀ x, ¬ safe x → regular x = 0) ∧
      (∀ x, safe x → 1 / 3 ≤ regular x) ∧
      (∀ i, line i → ∀ c, conditional p (features i) regular c =
        if c ∈ allowed i then (Fintype.card C : ℝ) / (allowed i).card else 0) ∧
      (∀ i, ¬ line i → ∀ c,
        conditional p (features i) ((1 - atom) • regular + atom • spike) c =
          if c ∈ allowed i then (Fintype.card C : ℝ) / (allowed i).card else 0) := by
  let P := chartProjection p features allowed
  let D := deletion P safe
  let b : ℝ := (2 * Fintype.card I + 1) * δ
  let η : ℝ := (Fintype.card I : ℝ) / (1 - δ) * (δ + b / (1 - b))
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hbQuarter : b ≤ 1 / 4 := hsmall
  have hb1 : b < 1 := by linarith
  have hDb : ‖D‖ ≤ b := chartDeletion_norm p features allowed safe δ hδ0 hglobal hconditional
  have hD : ‖D‖ < 1 := hDb.trans_lt hb1
  let defect := offLineDefect p features allowed line spike
  have hdef := offLineDefect_bounds p features allowed line spike hsmean hsnonneg hsallowed
    δ hδ0 hδ1 hsbound
  have hη : η ≤ 1 / 3 := hpositivity
  have hη0 : 0 ≤ η := by
    dsimp only [η]
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by linarith))
      (add_nonneg hδ0 (div_nonneg hb0 (by linarith)))
  let odds := atom / (1 - atom)
  have hden : 0 < 1 - atom := by linarith
  have hodds0 : 0 ≤ odds := div_nonneg ha0 hden.le
  have hodds1 : odds ≤ 1 := by
    dsimp [odds]
    rw [div_le_iff₀ hden, one_mul]
    linarith
  let target : Ω → ℝ := 1 - odds • defect
  let raw := neumannSolve D hD target
  let regular := safeMask safe raw
  have htarget : P target = target := by
    change combinedProjection p features allowed (1 - odds • defect) = _
    rw [map_sub, map_smul, combinedProjection_one p features allowed hfeature,
      offLineDefect_projected p features allowed line spike hfeature hpair]
  have hproject : P regular = target :=
    safe_neumann_projection P safe
      (chartProjection_idempotent p features allowed hfeature hpair) hD target htarget
  have hmean : expectation p regular = 1 := by
    have hm := combinedProjection_mean p features allowed hfeature regular
    change expectation p (P regular) = expectation p regular at hm
    rw [hproject] at hm
    dsimp only [target] at hm
    have hone : expectation p (1 : Ω → ℝ) = 1 := expectation_const p 1
    rw [map_sub, map_smul, hone,
      offLineDefect_mean p features allowed line spike hfeature, smul_zero, sub_zero] at hm
    exact hm.symm
  have hzero (x : Ω) (hx : ¬ safe x) : regular x = 0 := by
    simp [regular, hx]
  have hlower (x : Ω) (hx : safe x) : 1 / 3 ≤ regular x := by
    have hbase := solve_sub_norm_le D hD b hb1 hDb (1 : Ω → ℝ)
    rw [norm_one] at hbase
    have hbasepoint := (norm_le_pi_norm (neumannSolve D hD 1 - 1) x).trans hbase
    change |neumannSolve D hD 1 x - 1| ≤ b / (1 - b) * 1 at hbasepoint
    have hrepair := solve_pointwise_upper D hD b hb1 hDb defect
      ((Fintype.card I : ℝ) * δ / (1 - δ))
      ((Fintype.card I : ℝ) / (1 - δ)) hdef.2 hdef.1 x
    have hηformula : (Fintype.card I : ℝ) * δ / (1 - δ) +
        b / (1 - b) * (Fintype.card I / (1 - δ)) = η := by dsimp [η]; ring
    rw [hηformula] at hrepair
    have hratio : b / (1 - b) ≤ 1 / 3 := by
      rw [div_le_iff₀ (by linarith : 0 < 1 - b)]
      linarith
    have hscaled : odds * neumannSolve D hD defect x ≤ 1 / 3 := by
      calc
        _ ≤ odds * η := mul_le_mul_of_nonneg_left hrepair hodds0
        _ ≤ η := (mul_le_mul_of_nonneg_right hodds1 hη0).trans_eq (one_mul η)
        _ ≤ _ := hη
    have hlinear : raw = neumannSolve D hD 1 - odds • neumannSolve D hD defect := by
      dsimp [raw, target, neumannSolve]
      rw [map_sub, map_smul]
    rw [show regular x = raw x by simp [regular, hx], hlinear]
    change 1 / 3 ≤ neumannSolve D hD 1 x - odds * neumannSolve D hD defect x
    linarith [(abs_le.mp hbasepoint).1]
  have hnonneg (x : Ω) : 0 ≤ regular x := by
    by_cases hx : safe x
    · linarith [hlower x hx]
    · rw [hzero x hx]
  have hcomponent (i : I) : featureProjection p (features i) (allowed i) regular =
      -odds • (if line i then 0 else featureProjection p (features i) (allowed i) spike) := by
    rw [← featureProjection_combined p features allowed hfeature hpair i regular]
    change featureProjection p (features i) (allowed i) (P regular) = _
    rw [hproject]
    dsimp only [target]
    have hone : featureProjection p (features i) (allowed i) (1 : Ω → ℝ) = 0 :=
      featureProjection_const p (features i) (hfeature i) (allowed i) 1
    rw [map_sub, map_smul, hone,
      offLineDefect_component p features allowed line spike hfeature hpair]
    split_ifs <;> simp
  dsimp only
  rw [show regularDensity p features allowed line safe atom spike hD' = regular from rfl]
  refine ⟨hmean, hnonneg, hzero, hlower, ?_, ?_⟩
  · intro i hi c
    have hc : featureProjection p (features i) (allowed i) regular = 0 := by
      rw [hcomponent i, if_pos hi, smul_zero]
    have hs := conditional_outside_zero p (features i) (allowed i) safe regular hzero (hallowed i)
    rw [component_zero_marginal p (features i) (hfeature i) (allowed i) regular hc hs c,
      hmean, mul_one]
  · intro i hi c
    let final := (1 - atom) • regular + atom • spike
    have hfmean : expectation p final = 1 := by
      change expectation p ((1 - atom) • regular + atom • spike) = 1
      rw [map_add, map_smul, map_smul, hmean, hsmean]
      simp
    have hfcomp : featureProjection p (features i) (allowed i) final = 0 := by
      dsimp [final]
      rw [map_add, map_smul, map_smul, hcomponent i, if_neg hi, smul_smul,
        ← add_smul]
      have hc : (1 - atom) * -odds + atom = 0 := by
        dsimp [odds]
        field_simp
        ring
      rw [hc, zero_smul]
    have hfzero (x : Ω) (hx : features i x ∉ allowed i) : final x = 0 := by
      have hn : ¬ safe x := fun h => hx (hallowed i x h)
      simp [final, hzero x hn, hsallowed i hi x hx]
    have hs := conditional_outside_zero p (features i) (allowed i)
      (fun x => features i x ∈ allowed i) final hfzero (fun _ h => h)
    rw [component_zero_marginal p (features i) (hfeature i) (allowed i) final hfcomp hs c,
      hfmean, mul_one]

theorem regular_branch [Nonempty Ω] [Nonempty C] (p : FiniteDist Ω)
    (features : I → Ω → C) (allowed : I → Finset C) (line : I → Prop)
    (hfeature : ∀ i, p.map (features i) = FiniteDist.uniform C)
    (hpair : ∀ i j, i ≠ j → p.map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C))
    (safe : Ω → Prop) [DecidablePred safe]
    (hallowed : ∀ i x, safe x → features i x ∈ allowed i)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hglobal : expectation p (badIndicator safe) ≤ δ)
    (hconditional : ∀ i c, c ∈ allowed i →
      conditional p (features i) (badIndicator safe) c ≤ δ)
    (hsmall : (2 * Fintype.card I + 1) * δ ≤ 1 / 4)
    (hpositivity : (Fintype.card I : ℝ) / (1 - δ) *
      (δ + ((2 * Fintype.card I + 1) * δ) /
        (1 - (2 * Fintype.card I + 1) * δ)) ≤ 1 / 3)
    (atom : ℝ) (ha0 : 0 ≤ atom) (haHalf : atom ≤ 1 / 2)
    (spike : Ω → ℝ) (hsmean : expectation p spike = 1)
    (hsnonneg : ∀ x, 0 ≤ spike x)
    (hsallowed : ∀ i, ¬ line i → ∀ x, features i x ∉ allowed i → spike x = 0)
    (hsbound : ∀ i, ¬ line i → ∀ c,
      conditional p (features i) spike c ≤ 1 / (1 - δ)) :
    ∃ regular : Ω → ℝ,
      expectation p regular = 1 ∧ (∀ x, 0 ≤ regular x) ∧
      (∀ x, ¬ safe x → regular x = 0) ∧
      (∀ x, safe x → 1 / 3 ≤ regular x) ∧
      (∀ i, line i → ∀ c, conditional p (features i) regular c =
        if c ∈ allowed i then (Fintype.card C : ℝ) / (allowed i).card else 0) ∧
      (∀ i, ¬ line i → ∀ c,
        conditional p (features i) ((1 - atom) • regular + atom • spike) c =
          if c ∈ allowed i then (Fintype.card C : ℝ) / (allowed i).card else 0) := by
  have hquarter : ‖deletion (chartProjection p features allowed) safe‖ ≤ 1 / 4 :=
    (chartDeletion_norm p features allowed safe δ hδ0 hglobal hconditional).trans hsmall
  have hD : ‖deletion (chartProjection p features allowed) safe‖ < 1 :=
    hquarter.trans_lt (by norm_num)
  exact ⟨regularDensity p features allowed line safe atom spike hD,
    regularDensity_properties p features allowed line hfeature hpair safe hallowed δ hδ0 hδ1
      hglobal hconditional hsmall hpositivity atom ha0 haHalf spike hsmean hsnonneg hsallowed hsbound hD⟩

/-- The complete public flag and map distribution.  Neither its inputs nor
its support depend on the protected hidden source. -/
def flagLaw (atom : ℝ) (ha0 : 0 ≤ atom) (ha1 : atom ≤ 1)
    (regular marked : FiniteDist Ω) : FiniteDist (Bool × Ω) where
  weight point := if point.1 then atom * marked.weight point.2 else
    (1 - atom) * regular.weight point.2
  nonneg point := by
    split_ifs
    · exact mul_nonneg ha0 (marked.nonneg _)
    · exact mul_nonneg (by linarith) (regular.nonneg _)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true,
      ← Finset.mul_sum, regular.sum_one, marked.sum_one, mul_one]
    ring

theorem flagLaw_flag (atom : ℝ) (ha0 : 0 ≤ atom) (ha1 : atom ≤ 1)
    (regular marked : FiniteDist Ω) (flag : Bool) :
    ((flagLaw atom ha0 ha1 regular marked).map Prod.fst).weight flag =
      if flag then atom else 1 - atom := by
  rw [FiniteDist.map_weight, Fintype.sum_prod_type]
  cases flag <;>
    simp [flagLaw, ← Finset.mul_sum, regular.sum_one, marked.sum_one]

theorem flagLaw_feature (atom : ℝ) (ha0 : 0 ≤ atom) (ha1 : atom ≤ 1)
    (regular marked : FiniteDist Ω) (feature : Ω → C) (c : C) :
    ((flagLaw atom ha0 ha1 regular marked).map (fun point => feature point.2)).weight c =
      (1 - atom) * (regular.map feature).weight c + atom * (marked.map feature).weight c := by
  simp only [FiniteDist.map_weight, Fintype.sum_prod_type, flagLaw,
    Fintype.sum_bool, Bool.false_eq_true, if_false, if_true]
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  exact add_comm _ _

end
end CurrentAFT.AffineFlagCalibration

end

end

section

section




/-!
# The actual one-dimensional marked affine fiber

Marked charts have intercept `mark`, shear zero, and a uniformly sampled
surviving nonzero scale.  The survival and marginal bounds below are proved
from finite affine bijections and the palette deletion budget.
-/

namespace CurrentAFT.AffineFlagCalibration

open AFT AFT.BoundaryCalibration
open scoped BigOperators Classical

noncomputable section

variable {F I : Type*} [Field F] [Fintype F] [Fintype I]

def markedEvaluationEquiv (mark first : F) (hfirst : first ≠ 0) : F ≃ F where
  toFun scale := mark + scale * first
  invFun color := (color - mark) / first
  left_inv scale := by field_simp; ring
  right_inv color := by field_simp; ring

def markedScaleSafe (inputs : I → F × F) (allowed : I → Finset F)
    (mark scale : F) : Prop :=
  scale ≠ 0 ∧ ∀ i, (inputs i).1 ≠ 0 → mark + scale * (inputs i).1 ∈ allowed i

def markedSurvival (inputs : I → F × F) (allowed : I → Finset F) (mark : F) : ℝ :=
  eventMass (FiniteDist.uniform F) (markedScaleSafe inputs allowed mark)

theorem marked_scale_deletion (inputs : I → F × F) (allowed : I → Finset F) (mark : F) :
    expectation (FiniteDist.uniform F) (badIndicator (markedScaleSafe inputs allowed mark)) ≤
      affineDeletionBudget allowed := by
  let Off := {i : I // (inputs i).1 ≠ 0}
  let features : Off → F → F := fun i scale => mark + scale * (inputs i.val).1
  let palettes : Off → Finset F := fun i => allowed i.val
  let auxAllowed : Finset F := Finset.univ.erase 0
  have hfeatures (i : Off) : (FiniteDist.uniform F).map (features i) = FiniteDist.uniform F :=
    FiniteDist.uniform_map_equiv (markedEvaluationEquiv mark (inputs i.val).1 i.property)
  have hsafe : markedScaleSafe inputs allowed mark = legalChart id auxAllowed features palettes := by
    funext scale
    apply propext
    simp only [markedScaleSafe, legalChart, auxAllowed, Finset.mem_erase,
      Finset.mem_univ, and_true, id_eq]
    constructor
    · rintro ⟨hn, hh⟩
      exact ⟨hn, fun i => hh i.val i.property⟩
    · rintro ⟨hn, hh⟩
      exact ⟨hn, fun i hi => hh ⟨i, hi⟩⟩
  have hb := legalChart_global_budget (FiniteDist.uniform F) id auxAllowed features palettes
    (FiniteDist.uniform_map_equiv (Equiv.refl F)) hfeatures
  rw [← hsafe] at hb
  apply hb.trans
  rw [show expectation (FiniteDist.uniform F) (paletteFailure auxAllowed) =
      (Fintype.card F : ℝ)⁻¹ from nonzero_palette_failure]
  unfold affineDeletionBudget
  apply add_le_add le_rfl
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun i : I => (inputs i).1 ≠ 0)
    (fun i => expectation (FiniteDist.uniform F) (paletteFailure (allowed i)))
  have hnonneg : 0 ≤ ∑ i : {i : I // ¬ (inputs i).1 ≠ 0},
      expectation (FiniteDist.uniform F) (paletteFailure (allowed i.val)) := by
    apply Finset.sum_nonneg
    intro i _
    rw [expectation_apply]
    apply Finset.sum_nonneg
    intro c _
    exact mul_nonneg (FiniteDist.uniform F |>.nonneg c)
      (by unfold paletteFailure; split_ifs <;> norm_num)
  simp only [uniform_palette_failure] at hsplit ⊢
  simp only [uniform_palette_failure, palettes] at *
  linarith

theorem markedSurvival_lower (inputs : I → F × F) (allowed : I → Finset F) (mark : F) :
    1 - affineDeletionBudget allowed ≤ markedSurvival inputs allowed mark := by
  have h := marked_scale_deletion inputs allowed mark
  have he : eventIndicator (markedScaleSafe inputs allowed mark) =
      (1 : F → ℝ) - badIndicator (markedScaleSafe inputs allowed mark) := by
    funext scale
    simp only [eventIndicator, badIndicator, Pi.sub_apply, Pi.one_apply]
    split_ifs <;> norm_num
  change _ ≤ expectation (FiniteDist.uniform F) (eventIndicator _)
  rw [he, map_sub, show expectation (FiniteDist.uniform F) (1 : F → ℝ) = 1 from
    expectation_const _ 1]
  linarith

def markedScaleLaw (inputs : I → F × F) (allowed : I → Finset F) (mark : F)
    (hpos : 0 < markedSurvival inputs allowed mark) : FiniteDist F :=
  densityLaw (FiniteDist.uniform F)
    (restrictedDensity (FiniteDist.uniform F) (markedScaleSafe inputs allowed mark))
    (restrictedDensity_nonneg _ _) (restrictedDensity_mean _ _ hpos)

def markedChartLaw (inputs : I → F × F) (allowed : I → Finset F) (mark : F)
    (hpos : 0 < markedSurvival inputs allowed mark) : FiniteDist (Chart F) :=
  (markedScaleLaw inputs allowed mark hpos).map (fun scale => (mark, scale, 0))

omit [Fintype I] in
theorem markedChartLaw_support (inputs : I → F × F) (allowed : I → Finset F) (mark : F)
    (hpos : 0 < markedSurvival inputs allowed mark) (chart : Chart F)
    (hchart : ¬ (chart.1 = mark ∧ chart.2.2 = 0 ∧ chart.2.1 ≠ 0 ∧
      ∀ i, (inputs i).1 ≠ 0 → feature (inputs i).1 (inputs i).2 chart ∈ allowed i)) :
    (markedChartLaw inputs allowed mark hpos).weight chart = 0 := by
  rw [markedChartLaw, FiniteDist.map_weight]
  apply Finset.sum_eq_zero
  intro scale _
  by_cases he : (mark, scale, (0 : F)) = chart
  · subst chart
    have hn : ¬ markedScaleSafe inputs allowed mark scale := by
      intro hs
      apply hchart
      refine ⟨rfl, rfl, hs.1, ?_⟩
      intro i hi
      simpa only [feature, zero_mul, add_zero] using hs.2 i hi
    simp [markedScaleLaw, densityLaw, restrictedDensity, eventIndicator, hn]
  · simp only [if_neg he]

omit [Fintype I] in
theorem markedChartLaw_line (inputs : I → F × F) (allowed : I → Finset F) (mark : F)
    (hpos : 0 < markedSurvival inputs allowed mark) (i : I) (hi : (inputs i).1 = 0) (c : F) :
    ((markedChartLaw inputs allowed mark hpos).map (feature (inputs i).1 (inputs i).2)).weight c =
      if c = mark then 1 else 0 := by
  rw [markedChartLaw, FiniteDist.map_map, FiniteDist.map_weight]
  simp only [feature, hi, mul_zero, zero_mul, add_zero]
  by_cases hc : c = mark
  · subst c
    simpa using (markedScaleLaw inputs allowed mark hpos).sum_one
  · simp [Ne.symm hc, hc]

omit [Fintype I] in
theorem markedChartLaw_offLine_bound (inputs : I → F × F) (allowed : I → Finset F) (mark : F)
    (hpos : 0 < markedSurvival inputs allowed mark) (i : I) (hi : (inputs i).1 ≠ 0) (c : F) :
    ((markedChartLaw inputs allowed mark hpos).map (feature (inputs i).1 (inputs i).2)).weight c ≤
      (Fintype.card F : ℝ)⁻¹ / markedSurvival inputs allowed mark := by
  rw [markedChartLaw, FiniteDist.map_map]
  have hf : (fun a : F => feature (inputs i).1 (inputs i).2 (mark, a, 0)) =
      markedEvaluationEquiv mark (inputs i).1 hi := by
    funext a
    simp only [feature, zero_mul, add_zero, markedEvaluationEquiv, Equiv.coe_fn_mk]
  rw [hf]
  rw [FiniteDist.map_equiv_weight]
  change (Fintype.card F : ℝ)⁻¹ *
    (eventIndicator (markedScaleSafe inputs allowed mark) _ / markedSurvival inputs allowed mark) ≤ _
  unfold eventIndicator
  split_ifs
  · simp only [div_eq_mul_inv, one_mul, le_refl]
  · simp only [zero_div, mul_zero]
    positivity

section Density
variable {Ω C : Type*} [Fintype Ω] [Nonempty Ω] [Fintype C]

/-- Convert a literal probability law into its density against the full
uniform coefficient table. -/
def uniformDensity (law : FiniteDist Ω) : Ω → ℝ :=
  fun x => (Fintype.card Ω : ℝ) * law.weight x

omit [Nonempty Ω] in
theorem uniformDensity_nonneg (law : FiniteDist Ω) (x : Ω) : 0 ≤ uniformDensity law x :=
  mul_nonneg (Nat.cast_nonneg _) (law.nonneg x)

theorem uniformDensity_mean (law : FiniteDist Ω) :
    expectation (FiniteDist.uniform Ω) (uniformDensity law) = 1 := by
  have hq : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [expectation_apply, FiniteDist.uniform_weight, uniformDensity,
    ← mul_assoc, inv_mul_cancel₀ hq, one_mul]
  exact law.sum_one

theorem uniformDensity_conditional (law : FiniteDist Ω) (f : Ω → C) (c : C) :
    conditional (FiniteDist.uniform Ω) f (uniformDensity law) c =
      (Fintype.card C : ℝ) * (law.map f).weight c := by
  have hq : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [conditional_apply, expectation_apply, FiniteDist.uniform_weight,
    uniformDensity, FiniteDist.map_weight, mul_ite, mul_zero,
    ← mul_assoc, inv_mul_cancel₀ hq, one_mul]

end Density

theorem markedDensity_bound (inputs : I → F × F) (allowed : I → Finset F) (mark : F)
    (δ : ℝ) (hδ : δ < 1) (hbudget : affineDeletionBudget allowed ≤ δ)
    (hpos : 0 < markedSurvival inputs allowed mark) (i : I) (hi : (inputs i).1 ≠ 0) (c : F) :
    conditional (FiniteDist.uniform (Chart F)) (feature (inputs i).1 (inputs i).2)
      (uniformDensity (markedChartLaw inputs allowed mark hpos)) c ≤ 1 / (1 - δ) := by
  rw [uniformDensity_conditional]
  have hq : (0 : ℝ) < Fintype.card F := Nat.cast_pos.mpr Fintype.card_pos
  have hm := mul_le_mul_of_nonneg_left
    (markedChartLaw_offLine_bound inputs allowed mark hpos i hi c) hq.le
  have hl : 1 - δ ≤ markedSurvival inputs allowed mark :=
    (by linarith : 1 - δ ≤ 1 - affineDeletionBudget allowed).trans
      (markedSurvival_lower inputs allowed mark)
  calc
    _ ≤ (Fintype.card F : ℝ) * ((Fintype.card F : ℝ)⁻¹ / markedSurvival inputs allowed mark) := hm
    _ = 1 / markedSurvival inputs allowed mark := by rw [← mul_div_assoc, mul_inv_cancel₀ hq.ne']
    _ ≤ _ := one_div_le_one_div_of_le (by linarith) hl

end
end CurrentAFT.AffineFlagCalibration

end

section




/-!
# One positive public affine-map law for all protected inputs

This is the current marked-line theorem.  The public law is a distribution
on complete `(flag, intercept, scale, shear)` tuples, constructed before any
protected input is supplied.  The hypotheses are the manuscript's finite
palette budgets; no response inverse or positive map law is assumed.
-/

namespace CurrentAFT.AffineFlagCalibration

open AFT AFT.BoundaryCalibration
open scoped BigOperators Classical

noncomputable section

variable {F I : Type*} [Field F] [Fintype F] [Fintype I]

theorem affine_flag_law (inputs : I → F × F) (hinj : Function.Injective inputs)
    (allowed : I → Finset F) (mark : F)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hbudget : affineDeletionBudget allowed ≤ δ)
    (hsmall : (2 * Fintype.card I + 1) * δ ≤ 1 / 4)
    (hpositivity : (Fintype.card I : ℝ) / (1 - δ) *
      (δ + ((2 * Fintype.card I + 1) * δ) /
        (1 - (2 * Fintype.card I + 1) * δ)) ≤ 1 / 3)
    (atom : ℝ) (ha0 : 0 ≤ atom) (haHalf : atom ≤ 1 / 2) :
    ∃ regular marked : FiniteDist (Chart F),
      ∃ law : FiniteDist (Bool × Chart F),
      law = flagLaw atom ha0 (by linarith) regular marked ∧
      (∀ chart, ¬ (chart.2.1 ≠ 0 ∧
        ∀ i, feature (inputs i).1 (inputs i).2 chart ∈ allowed i) → regular.weight chart = 0) ∧
      (∀ chart, chart.2.1 ≠ 0 →
        (∀ i, feature (inputs i).1 (inputs i).2 chart ∈ allowed i) →
          (Fintype.card (Chart F) : ℝ)⁻¹ / 3 ≤ regular.weight chart) ∧
      (∀ chart, ¬ (chart.1 = mark ∧ chart.2.2 = 0 ∧ chart.2.1 ≠ 0 ∧
        ∀ i, (inputs i).1 ≠ 0 → feature (inputs i).1 (inputs i).2 chart ∈ allowed i) →
          marked.weight chart = 0) ∧
      (∀ flag, (law.map Prod.fst).weight flag = if flag then atom else 1 - atom) ∧
      (∀ i, (inputs i).1 = 0 → ∀ c,
        (law.map (fun point => feature (inputs i).1 (inputs i).2 point.2)).weight c =
          (1 - atom) * (if c ∈ allowed i then ((allowed i).card : ℝ)⁻¹ else 0) +
            atom * (if c = mark then 1 else 0)) ∧
      (∀ i, (inputs i).1 ≠ 0 → ∀ c,
        (law.map (fun point => feature (inputs i).1 (inputs i).2 point.2)).weight c =
          if c ∈ allowed i then ((allowed i).card : ℝ)⁻¹ else 0) := by
  let p := FiniteDist.uniform (Chart F)
  let features := fun i => feature (inputs i).1 (inputs i).2
  let auxiliary := fun chart : Chart F => chart.2.1
  let auxAllowed : Finset F := Finset.univ.erase 0
  let safe := legalChart auxiliary auxAllowed features allowed
  have hfeature (i : I) : p.map (features i) = FiniteDist.uniform F := feature_uniform _ _
  have hpair (i j : I) (hij : i ≠ j) : p.map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform F).prod (FiniteDist.uniform F) :=
    feature_pair_uniform (inputs i) (inputs j) (fun h => hij (hinj h))
  have hauxpair (i : I) : p.map (fun x => (features i x, auxiliary x)) =
      (FiniteDist.uniform F).prod (FiniteDist.uniform F) := feature_scale_uniform _ _
  have hbudgetFormula : expectation (FiniteDist.uniform F) (paletteFailure auxAllowed) +
      ∑ i, expectation (FiniteDist.uniform F) (paletteFailure (allowed i)) =
        affineDeletionBudget allowed := by
    rw [show expectation (FiniteDist.uniform F) (paletteFailure auxAllowed) =
        (Fintype.card F : ℝ)⁻¹ from nonzero_palette_failure]
    simp only [uniform_palette_failure, affineDeletionBudget]
  have hglobal : expectation p (badIndicator safe) ≤ δ := by
    apply le_trans _ hbudget
    rw [← hbudgetFormula]
    exact legalChart_global_budget p auxiliary auxAllowed features allowed scale_uniform hfeature
  have hconditional : ∀ i c, c ∈ allowed i → conditional p (features i) (badIndicator safe) c ≤ δ := by
    intro i c hc
    apply le_trans _ hbudget
    rw [← hbudgetFormula]
    exact legalChart_conditional_budget p auxiliary auxAllowed features allowed
      hfeature hpair hauxpair i c hc
  have hsurvival : 0 < markedSurvival inputs allowed mark := by
    have hl := markedSurvival_lower inputs allowed mark
    linarith
  let marked := markedChartLaw inputs allowed mark hsurvival
  let spike := uniformDensity marked
  have hsmean : expectation p spike = 1 := uniformDensity_mean marked
  have hsnonneg (chart : Chart F) : 0 ≤ spike chart := uniformDensity_nonneg marked chart
  have hsallowed (i : I) (hi : ¬ (inputs i).1 = 0) (chart : Chart F)
      (hc : features i chart ∉ allowed i) : spike chart = 0 := by
    have hz : marked.weight chart = 0 := markedChartLaw_support inputs allowed mark hsurvival chart
      (by rintro ⟨_, _, _, hh⟩; exact hc (hh i hi))
    simp only [spike, uniformDensity, hz, mul_zero]
  have hsbound (i : I) (hi : ¬ (inputs i).1 = 0) (c : F) :
      conditional p (features i) spike c ≤ 1 / (1 - δ) :=
    markedDensity_bound inputs allowed mark δ hδ1 hbudget hsurvival i hi c
  obtain ⟨density, hdmean, hdnonneg, hdzero, hdlower, hdline, hdoff⟩ :=
    regular_branch p features allowed (fun i => (inputs i).1 = 0) hfeature hpair safe
      (fun i chart hc => hc.2 i) δ hδ0 hδ1 hglobal hconditional hsmall hpositivity
      atom ha0 haHalf spike hsmean hsnonneg hsallowed hsbound
  let regular := densityLaw p density hdnonneg hdmean
  let law := flagLaw atom ha0 (by linarith : atom ≤ 1) regular marked
  have hregular (i : I) (hi : (inputs i).1 = 0) (c : F) :
      (regular.map (features i)).weight c =
        if c ∈ allowed i then ((allowed i).card : ℝ)⁻¹ else 0 := by
    rw [densityLaw_marginal, hdline i hi]
    split_ifs
    · have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      field_simp
    · simp
  refine ⟨regular, marked, law, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro chart hc
    have hn : ¬ safe chart := by
      simpa only [safe, legalChart, auxiliary, auxAllowed, features, Finset.mem_erase,
        Finset.mem_univ, and_true] using hc
    simp only [regular, densityLaw, hdzero chart hn, mul_zero]
  · intro chart hn hc
    have hs : safe chart := by
      simpa only [safe, legalChart, auxiliary, auxAllowed, features, Finset.mem_erase,
        Finset.mem_univ, and_true] using And.intro hn hc
    change (Fintype.card (Chart F) : ℝ)⁻¹ / 3 ≤
      (Fintype.card (Chart F) : ℝ)⁻¹ * density chart
    have hh := mul_le_mul_of_nonneg_left (hdlower chart hs)
      (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card (Chart F)) : (0 : ℝ) ≤ _))
    simpa only [div_eq_mul_inv, one_mul] using hh
  · exact markedChartLaw_support inputs allowed mark hsurvival
  · exact flagLaw_flag atom ha0 (by linarith) regular marked
  · intro i hi c
    rw [flagLaw_feature, hregular i hi c,
      markedChartLaw_line inputs allowed mark hsurvival i hi c]
  · intro i hi c
    rw [flagLaw_feature, densityLaw_marginal]
    have hm := uniformDensity_conditional marked (features i) c
    have hf := hdoff i hi c
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hf
    change (1 - atom) * (conditional p (features i) density c / Fintype.card F) +
      atom * (marked.map (features i)).weight c = _
    change conditional p (features i) spike c = _ at hm
    rw [hm] at hf
    have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    split_ifs at hf ⊢ <;> field_simp <;> nlinarith [hf]

end
end CurrentAFT.AffineFlagCalibration

end

section




/-! # The simultaneous public flag and affine-map specification -/
namespace CurrentAFT.AffineFlagCalibration
open AFT AFT.BoundaryCalibration
open scoped BigOperators Classical
noncomputable section

structure SimultaneousLaw {F I : Type*} [Field F] [Fintype F] [Fintype I]
    (inputs : I → F × F) (allowed : I → Finset F) (mark : F) (atom : ℝ) where
  regular : FiniteDist (Chart F)
  marked : FiniteDist (Chart F)
  joint : FiniteDist (Bool × Chart F)
  decomposition : ∀ point, joint.weight point = if point.1 then atom * marked.weight point.2
    else (1 - atom) * regular.weight point.2
  regular_support : ∀ chart, ¬ (chart.2.1 ≠ 0 ∧
    ∀ i, feature (inputs i).1 (inputs i).2 chart ∈ allowed i) → regular.weight chart = 0
  regular_lower : ∀ chart, chart.2.1 ≠ 0 →
    (∀ i, feature (inputs i).1 (inputs i).2 chart ∈ allowed i) →
    (Fintype.card (Chart F) : ℝ)⁻¹ / 3 ≤ regular.weight chart
  marked_support : ∀ chart, ¬ (chart.1 = mark ∧ chart.2.2 = 0 ∧ chart.2.1 ≠ 0 ∧
    ∀ i, (inputs i).1 ≠ 0 → feature (inputs i).1 (inputs i).2 chart ∈ allowed i) →
    marked.weight chart = 0
  flag_marginal : ∀ flag, (joint.map Prod.fst).weight flag = if flag then atom else 1 - atom
  on_line : ∀ i, (inputs i).1 = 0 → ∀ c,
    (joint.map (fun point => feature (inputs i).1 (inputs i).2 point.2)).weight c =
      (1 - atom) * (if c ∈ allowed i then ((allowed i).card : ℝ)⁻¹ else 0) +
        atom * (if c = mark then 1 else 0)
  off_line : ∀ i, (inputs i).1 ≠ 0 → ∀ c,
    (joint.map (fun point => feature (inputs i).1 (inputs i).2 point.2)).weight c =
      if c ∈ allowed i then ((allowed i).card : ℝ)⁻¹ else 0

end
end CurrentAFT.AffineFlagCalibration

end

section









/-!
# Feasibility at the current polynomial parameters

Only the generic finite palette-count lemmas are reused from the old library.
All sizes and all numerical estimates in this file use `CurrentAFT.Parameters`.
-/

namespace CurrentAFT.AffineFlagCalibration

open AFT AFT.BoundaryCalibration
open scoped BigOperators Classical

noncomputable section

 theorem small_budget (x S : ℝ) (hx : 1 ≤ x) (hS0 : 0 ≤ S) (hS : S ≤ 4 * x ^ 4) :
    let δ := 1 / (1024 * x ^ 12)
    δ < 1 ∧ (2 * S + 1) * δ ≤ 1 / 4 ∧
      S / (1 - δ) * (δ + ((2 * S + 1) * δ) / (1 - (2 * S + 1) * δ)) ≤ 1 / 3 := by
  dsimp only
  let δ := 1 / (1024 * x ^ 12)
  let b := (2 * S + 1) * δ
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hx4 : 1 ≤ x ^ 4 := one_le_pow₀ hx
  have hx12 : 1 ≤ x ^ 12 := one_le_pow₀ hx
  have h412 : x ^ 4 ≤ x ^ 12 := pow_le_pow_right₀ hx (by omega)
  have h812 : x ^ 8 ≤ x ^ 12 := pow_le_pow_right₀ hx (by omega)
  have hδ0 : 0 ≤ δ := by dsimp [δ]; positivity
  have hδ : δ ≤ 1 / 1024 := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity : 0 < 1024 * x ^ 12)).mpr
    nlinarith
  have htwo : 2 * S + 1 ≤ 9 * x ^ 4 := by linarith
  have hb0 : 0 ≤ b := mul_nonneg (by linarith) hδ0
  have hb : b ≤ 9 / 1024 := by
    dsimp [b, δ]
    rw [mul_one_div, div_le_iff₀ (by positivity : 0 < 1024 * x ^ 12)]
    nlinarith
  have hSδ : S * δ ≤ 1 / 256 := by
    dsimp [δ]
    rw [mul_one_div, div_le_iff₀ (by positivity : 0 < 1024 * x ^ 12)]
    nlinarith
  have hSb : S * b ≤ 9 / 256 := by
    have hm := mul_le_mul hS htwo (by linarith : 0 ≤ 2 * S + 1) (by positivity : 0 ≤ 4 * x ^ 4)
    have hpow : (4 * x ^ 4) * (9 * x ^ 4) = 36 * x ^ 8 := by ring
    rw [hpow] at hm
    dsimp [b, δ]
    rw [← mul_assoc, mul_one_div, div_le_iff₀ (by positivity : 0 < 1024 * x ^ 12)]
    nlinarith
  have hd1 : 0 < 1 - δ := by linarith
  have hb1 : 0 < 1 - b := by linarith
  have hden : (1 : ℝ) / 4 ≤ (1 - δ) * (1 - b) := by
    have hm := mul_le_mul (by linarith : (1 : ℝ) / 2 ≤ 1 - δ)
      (by linarith : (1 : ℝ) / 2 ≤ 1 - b) (by norm_num : (0 : ℝ) ≤ 1 / 2) hd1.le
    norm_num at hm
    exact hm
  refine ⟨by linarith, by change b ≤ _; linarith, ?_⟩
  change S / (1 - δ) * (δ + b / (1 - b)) ≤ _
  rw [show S / (1 - δ) * (δ + b / (1 - b)) =
      (S * δ * (1 - b) + S * b) / ((1 - δ) * (1 - b)) by
        field_simp]
  rw [div_le_iff₀ (mul_pos hd1 hb1)]
  have hm : S * δ * (1 - b) ≤ S * δ := by nlinarith [mul_nonneg (mul_nonneg hS0 hδ0) hb0]
  nlinarith

def legDeletionUpper (security : ℕ) : ℝ :=
  1 / (1024 * (Parameters.base security : ℝ) ^ 12)

abbrev ProtectedInput (security : ℕ) :=
  GaussianSource.Window (Parameters.sourceCutoff security - 1) ×
    GaussianSource.Window (Parameters.sourceCutoff security - 1)

def legOffsetBound (security : ℕ) : ℤ :=
  2 * (Parameters.anchorWidth security : ℤ) + Parameters.sourceCutoff security - 1

theorem leg_trimmed_room (security : ℕ) :
    2 + legOffsetBound security + (Parameters.sourceCutoff security - 1 : ℕ) <
      (Parameters.modulus security : ℤ) := by
  have hb : 1 ≤ Parameters.base security := (Parameters.base_ge_two security).trans' (by omega)
  have hp : 0 < Parameters.base security ^ 64 := pow_pos (Parameters.base_pos security) _
  have hA : Parameters.anchorWidth security ≤ Parameters.base security ^ 64 := by
    simpa only [Parameters.anchorWidth, Parameters.scale, ← pow_mul] using
      Nat.pow_le_pow_right hb (show 48 ≤ 64 by omega)
  have hB : Parameters.sourceCutoff security ≤ Parameters.base security ^ 64 :=
    Nat.pow_le_pow_right hb (show 2 ≤ 64 by omega)
  have hBpos : 0 < Parameters.sourceCutoff security := pow_pos (Parameters.base_pos security) _
  have hq := (Parameters.modulus_bounds security).1
  have hclear : 2 * Parameters.anchorWidth security + 2 * Parameters.sourceCutoff security <
      Parameters.modulus security := by omega
  dsimp only [legOffsetBound]
  omega

theorem leg_input_separation (security : ℕ) :
    2 * (Parameters.sourceCutoff security - 1) < Parameters.modulus security := by
  have h := leg_trimmed_room security
  have hA : (0 : ℤ) ≤ Parameters.anchorWidth security := Int.natCast_nonneg _
  dsimp only [legOffsetBound] at h
  omega

theorem protectedInput_count_le (security : ℕ) :
    (Fintype.card (ProtectedInput security) : ℝ) ≤ 4 * (Parameters.base security : ℝ) ^ 4 := by
  rw [protectedInputs_card]
  have hB : 0 < Parameters.sourceCutoff security := pow_pos (Parameters.base_pos security) _
  have hcount : 2 * (Parameters.sourceCutoff security - 1) + 1 ≤ 2 * Parameters.sourceCutoff security := by omega
  have hsquare := Nat.pow_le_pow_left hcount 2
  have hh : ((2 * Parameters.sourceCutoff security) ^ 2 : ℕ) = 4 * Parameters.base security ^ 4 := by
    simp only [Parameters.sourceCutoff]
    ring
  rw [hh] at hsquare
  exact_mod_cast hsquare

theorem leg_budget_conditions (security : ℕ) :
    0 ≤ legDeletionUpper security ∧ legDeletionUpper security < 1 ∧
      (2 * Fintype.card (ProtectedInput security) + 1) * legDeletionUpper security ≤ 1 / 4 ∧
      (Fintype.card (ProtectedInput security) : ℝ) / (1 - legDeletionUpper security) *
        (legDeletionUpper security +
          ((2 * Fintype.card (ProtectedInput security) + 1) * legDeletionUpper security) /
            (1 - (2 * Fintype.card (ProtectedInput security) + 1) * legDeletionUpper security)) ≤ 1 / 3 := by
  have h := small_budget (Parameters.base security : ℝ) (Fintype.card (ProtectedInput security))
    (by exact_mod_cast (show 1 ≤ Parameters.base security from by have := Parameters.base_ge_two security; omega))
    (Nat.cast_nonneg _) (protectedInput_count_le security)
  exact ⟨by unfold legDeletionUpper; positivity, h⟩

local instance currentModulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

theorem protectedPalette_current_budget (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ legOffsetBound security) :
    affineDeletionBudget (protectedPalettes (Parameters.sourceCutoff security - 1)
      (Parameters.modulus security) 1 baseline) ≤ legDeletionUpper security := by
  have hbudget := protectedPalette_budget (Parameters.sourceCutoff security - 1)
    (Parameters.modulus security) 1 baseline (legOffsetBound security) (by norm_num)
    hbaseline (by simpa using leg_trimmed_room security)
  apply hbudget.trans
  let x : ℝ := Parameters.base security
  let S : ℝ := ((2 * (Parameters.sourceCutoff security - 1) + 1 : ℕ) : ℝ) ^ 2
  let d : ℝ := 2 + (legOffsetBound security : ℝ) + (Parameters.sourceCutoff security - 1 : ℕ)
  have hx : 1 ≤ x := by
    dsimp [x]
    exact_mod_cast (show 1 ≤ Parameters.base security from by have := Parameters.base_ge_two security; omega)
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hBpos : 0 < Parameters.sourceCutoff security := pow_pos (Parameters.base_pos security) _
  have hS : S ≤ 4 * x ^ 4 := by
    simpa only [S, x, protectedInputs_card, Nat.cast_pow] using protectedInput_count_le security
  have hB : (Parameters.sourceCutoff security : ℝ) ≤ x ^ 48 := by
    simpa only [Parameters.sourceCutoff, Nat.cast_pow, x] using
      pow_le_pow_right₀ hx (show 2 ≤ 48 by omega)
  have hd : d ≤ 4 * x ^ 48 := by
    have heq : d = 2 * x ^ 48 + 2 * (Parameters.sourceCutoff security : ℝ) := by
      dsimp only [d, legOffsetBound, x]
      push_cast
      rw [Nat.cast_sub (by omega : 1 ≤ Parameters.sourceCutoff security)]
      simp only [Parameters.anchorWidth, Parameters.scale, Nat.cast_pow, ← pow_mul]
      ring
    rw [heq]
    linarith
  have hd0 : 0 ≤ d := by
    have hT : 0 ≤ legOffsetBound security := by
      dsimp only [legOffsetBound]
      omega
    dsimp only [d]
    have hTR : (0 : ℝ) ≤ (legOffsetBound security : ℝ) := by exact_mod_cast hT
    exact add_nonneg (add_nonneg (by norm_num) hTR) (Nat.cast_nonneg _)
  have hq : (65536 : ℝ) * x ^ 64 ≤ Parameters.modulus security := by
    dsimp [x]
    exact_mod_cast (Parameters.modulus_bounds security).1
  have hq0 : (0 : ℝ) < Parameters.modulus security :=
    lt_of_lt_of_le (by positivity) hq
  have hnum : 1 + S * d ≤ 17 * x ^ 52 := by
    have hm := mul_le_mul hS hd hd0 (by positivity : 0 ≤ 4 * x ^ 4)
    have heq : (4 * x ^ 4) * (4 * x ^ 48) = 16 * x ^ 52 := by ring
    rw [heq] at hm
    nlinarith [one_le_pow₀ hx (n := 52)]
  simp only [Int.cast_one, mul_one]
  change (1 + S * d) / Parameters.modulus security ≤ 1 / (1024 * x ^ 12)
  apply (div_le_iff₀ hq0).mpr
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0 < 1024 * x ^ 12)]
  have hm := mul_le_mul_of_nonneg_right hnum (by positivity : 0 ≤ 1024 * x ^ 12)
  have heq : (17 * x ^ 52) * (1024 * x ^ 12) = 17408 * x ^ 64 := by ring
  rw [heq] at hm
  nlinarith [pow_nonneg hx0.le 64]

end
end CurrentAFT.AffineFlagCalibration

end

section







/-!
# Exact rational finite response for the current flag calibration

The matrix is the literal `Id - P(1_safeᶜ ·)` on the complete finite chart
table.  Its entries are rational.  The real deletion bound proves this
rational matrix invertible; no inverse or positive table is supplied as a
premise.  Bit-operation accounting for solving the table is separate.
-/

namespace CurrentAFT.CurrentRationalFlagLaw

open AFT AFT.BoundaryCalibration AffineFlagCalibration
open scoped BigOperators Classical

noncomputable section

variable {Ω C I : Type*} [Fintype Ω] [Fintype C] [Fintype I]

def realVector (f : Ω → ℚ) : Ω → ℝ := fun x => f x

def expectationQ : (Ω → ℚ) →ₗ[ℚ] ℚ where
  toFun f := (Fintype.card Ω : ℚ)⁻¹ * ∑ x, f x
  map_add' f g := by simp only [Pi.add_apply, Finset.sum_add_distrib, mul_add]
  map_smul' r f := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]; ring

def conditionalQ (feature : Ω → C) : (Ω → ℚ) →ₗ[ℚ] (C → ℚ) where
  toFun f c := (Fintype.card C : ℚ) * expectationQ (fun x => if feature x = c then f x else 0)
  map_add' f g := by
    funext c
    simp only [expectationQ, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    simp_rw [ite_add_zero]
    rw [Finset.sum_add_distrib]
    ring
  map_smul' r f := by
    funext c
    have he : (fun x => if feature x = c then r * f x else 0) =
        r • (fun x => if feature x = c then f x else 0) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      split_ifs <;> simp
    change (Fintype.card C : ℚ) * expectationQ (fun x => if feature x = c then r * f x else 0) =
      r * ((Fintype.card C : ℚ) * expectationQ (fun x => if feature x = c then f x else 0))
    rw [he, map_smul]
    simp only [smul_eq_mul]
    ring

def centerAllowedQ (allowed : Finset C) : (C → ℚ) →ₗ[ℚ] (C → ℚ) where
  toFun f c := if c ∈ allowed then f c - (∑ a ∈ allowed, f a) / allowed.card else 0
  map_add' f g := by
    funext c
    simp only [Pi.add_apply]
    split_ifs <;> simp [Finset.sum_add_distrib, add_div]
    ring
  map_smul' r f := by
    funext c
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp [← Finset.mul_sum, mul_sub, mul_div_assoc]

def featureProjectionQ (feature : Ω → C) (allowed : Finset C) :
    (Ω → ℚ) →ₗ[ℚ] (Ω → ℚ) :=
  (LinearMap.funLeft ℚ ℚ feature).comp ((centerAllowedQ allowed).comp (conditionalQ feature))

def projectionQ (features : I → Ω → C) (allowed : I → Finset C) :
    (Ω → ℚ) →ₗ[ℚ] (Ω → ℚ) where
  toFun f x := expectationQ f + ∑ i, featureProjectionQ (features i) (allowed i) f x
  map_add' f g := by
    funext x
    simp only [map_add, Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' r f := by
    funext x
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← Finset.mul_sum]
    ring

def badMaskQ (safe : Ω → Prop) : (Ω → ℚ) →ₗ[ℚ] (Ω → ℚ) where
  toFun f x := if safe x then 0 else f x
  map_add' f g := by funext x; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' r f := by funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

def responseQ (features : I → Ω → C) (allowed : I → Finset C) (safe : Ω → Prop) :
    (Ω → ℚ) →ₗ[ℚ] (Ω → ℚ) :=
  LinearMap.id - (projectionQ features allowed).comp (badMaskQ safe)

theorem expectationQ_cast [Nonempty Ω] (f : Ω → ℚ) :
    (expectationQ f : ℝ) = expectation (FiniteDist.uniform Ω) (realVector f) := by
  simp only [expectationQ, LinearMap.coe_mk, AddHom.coe_mk, Rat.cast_mul, Rat.cast_inv,
    Rat.cast_natCast, Rat.cast_sum, expectation_apply, FiniteDist.uniform_weight, realVector,
    Finset.mul_sum]

theorem conditionalQ_cast [Nonempty Ω] (feature : Ω → C) (f : Ω → ℚ) (c : C) :
    (conditionalQ feature f c : ℝ) = conditional (FiniteDist.uniform Ω) feature (realVector f) c := by
  simp only [conditionalQ, LinearMap.coe_mk, AddHom.coe_mk, Rat.cast_mul,
    Rat.cast_natCast, expectationQ_cast, conditional_apply]
  congr 2
  funext x
  simp only [realVector]
  split_ifs <;> simp

omit [Fintype C] in
theorem centerAllowedQ_cast (allowed : Finset C) (f : C → ℚ) (c : C) :
    (centerAllowedQ allowed f c : ℝ) = centerAllowed allowed (realVector f) c := by
  simp only [centerAllowedQ, LinearMap.coe_mk, AddHom.coe_mk, centerAllowed_apply, realVector]
  split_ifs <;> simp only [Rat.cast_sub, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast, Rat.cast_zero]

theorem featureProjectionQ_cast [Nonempty Ω] (feature : Ω → C) (allowed : Finset C)
    (f : Ω → ℚ) (x : Ω) :
    (featureProjectionQ feature allowed f x : ℝ) =
      featureProjection (FiniteDist.uniform Ω) feature allowed (realVector f) x := by
  change (centerAllowedQ allowed (conditionalQ feature f) (feature x) : ℝ) = _
  rw [centerAllowedQ_cast]
  have hc : realVector (conditionalQ feature f) = conditional (FiniteDist.uniform Ω) feature (realVector f) :=
    funext (conditionalQ_cast feature f)
  rw [hc]
  rfl

theorem projectionQ_cast [Nonempty Ω] (features : I → Ω → C) (allowed : I → Finset C)
    (f : Ω → ℚ) (x : Ω) :
    (projectionQ features allowed f x : ℝ) =
      chartProjection (FiniteDist.uniform Ω) features allowed (realVector f) x := by
  simp only [projectionQ, LinearMap.coe_mk, AddHom.coe_mk, Rat.cast_add, Rat.cast_sum,
    expectationQ_cast, featureProjectionQ_cast, chartProjection_apply]
  rfl

theorem responseQ_cast [Nonempty Ω] (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop) (f : Ω → ℚ) :
    realVector (responseQ features allowed safe f) = realVector f -
      deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe (realVector f) := by
  funext x
  change ((f x - projectionQ features allowed (badMaskQ safe f) x : ℚ) : ℝ) = _
  rw [Rat.cast_sub, projectionQ_cast]
  have hb : realVector (badMaskQ safe f) = realVector f - safeMask safe (realVector f) := by
    funext y
    simp only [badMaskQ, realVector, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, safeMask_apply]
    split_ifs <;> simp
  rw [hb]
  rfl

theorem contraction_response_injective (D : (Ω → ℝ) →L[ℝ] (Ω → ℝ)) (hD : ‖D‖ < 1) :
    Function.Injective (fun f : Ω → ℝ => f - D f) := by
  intro f g heq
  have hd : f - g = D (f - g) := by rw [map_sub]; linear_combination heq
  have hn : ‖f - g‖ ≤ ‖D‖ * ‖f - g‖ := by
    conv_lhs => rw [hd]
    exact D.le_opNorm _
  have hz : ‖f - g‖ = 0 := by nlinarith [norm_nonneg (f - g)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

variable [DecidableEq Ω]

def responseMatrix (features : I → Ω → C) (allowed : I → Finset C) (safe : Ω → Prop) :
    Matrix Ω Ω ℚ := LinearMap.toMatrix' (responseQ features allowed safe)

def solve (features : I → Ω → C) (allowed : I → Finset C) (safe : Ω → Prop)
    (target : Ω → ℚ) : Ω → ℚ := (responseMatrix features allowed safe)⁻¹.mulVec target

theorem responseMatrix_isUnit [Nonempty Ω] (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop)
    (hD : ‖deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe‖ < 1) :
    IsUnit (responseMatrix features allowed safe) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro f g hfg
  have hq : responseQ features allowed safe f = responseQ features allowed safe g := by
    simpa only [responseMatrix, LinearMap.toMatrix'_mulVec] using hfg
  have hr := congrArg realVector hq
  rw [responseQ_cast, responseQ_cast] at hr
  have hi := contraction_response_injective _ hD hr
  funext x
  exact Rat.cast_injective (congrFun hi x)

theorem solve_equation [Nonempty Ω] (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop)
    (hD : ‖deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe‖ < 1)
    (target : Ω → ℚ) : responseQ features allowed safe (solve features allowed safe target) = target := by
  have hu := responseMatrix_isUnit features allowed safe hD
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hu
  rw [← LinearMap.toMatrix'_mulVec (responseQ features allowed safe)]
  change (responseMatrix features allowed safe).mulVec
    ((responseMatrix features allowed safe)⁻¹.mulVec target) = _
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]

theorem solve_cast [Nonempty Ω] (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop)
    (hD : ‖deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe‖ < 1)
    (target : Ω → ℚ) :
    realVector (solve features allowed safe target) =
      neumannSolve (deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe) hD (realVector target) := by
  apply contraction_response_injective _ hD
  exact ((responseQ_cast features allowed safe (solve features allowed safe target)).symm.trans
    (congrArg realVector (solve_equation features allowed safe hD target))).trans
      (neumannSolve_equation _ hD (realVector target)).symm

def offLineDefectQ (features : I → Ω → C) (allowed : I → Finset C)
    (line : I → Prop) (spike : Ω → ℚ) : Ω → ℚ :=
  ∑ i, if line i then 0 else featureProjectionQ (features i) (allowed i) spike

def regularDensityQ (features : I → Ω → C) (allowed : I → Finset C)
    (line : I → Prop) (safe : Ω → Prop) (atom : ℚ) (spike : Ω → ℚ) : Ω → ℚ :=
  fun x => if safe x then solve features allowed safe
    (1 - (atom / (1 - atom)) • offLineDefectQ features allowed line spike) x else 0

omit [DecidableEq Ω] in
theorem offLineDefectQ_cast [Nonempty Ω] (features : I → Ω → C) (allowed : I → Finset C)
    (line : I → Prop) (spike : Ω → ℚ) :
    realVector (offLineDefectQ features allowed line spike) =
      offLineDefect (FiniteDist.uniform Ω) features allowed line (realVector spike) := by
  funext x
  simp only [realVector, offLineDefectQ, offLineDefect, Finset.sum_apply, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : line i
  · simp only [if_pos hi, Pi.zero_apply, Rat.cast_zero]
  · simp only [if_neg hi, featureProjectionQ_cast]

theorem regularDensityQ_cast [Nonempty Ω] (features : I → Ω → C) (allowed : I → Finset C)
    (line : I → Prop) (safe : Ω → Prop) (atom : ℚ) (spike : Ω → ℚ)
    (hD : ‖deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe‖ < 1) :
    realVector (regularDensityQ features allowed line safe atom spike) =
      regularDensity (FiniteDist.uniform Ω) features allowed line safe atom (realVector spike) hD := by
  let target : Ω → ℚ := 1 - (atom / (1 - atom)) • offLineDefectQ features allowed line spike
  have htarget : realVector target = (1 : Ω → ℝ) -
      ((atom : ℝ) / (1 - (atom : ℝ))) • offLineDefect (FiniteDist.uniform Ω) features allowed line (realVector spike) := by
    funext x
    have hd := congrFun (offLineDefectQ_cast features allowed line spike) x
    change ((1 - atom / (1 - atom) * offLineDefectQ features allowed line spike x : ℚ) : ℝ) = _
    simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Pi.sub_apply,
      Pi.one_apply, Pi.smul_apply, smul_eq_mul]
    rw [show (offLineDefectQ features allowed line spike x : ℝ) = _ from hd]
  have hraw := solve_cast features allowed safe hD target
  rw [htarget] at hraw
  funext x
  change ((if safe x then solve features allowed safe target x else 0 : ℚ) : ℝ) = _
  rw [regularDensity, safeMask_apply]
  by_cases hx : safe x
  · simp only [if_pos hx]
    exact congrFun hraw x
  · simp only [if_neg hx, Rat.cast_zero]

structure RegularCertificate [Nonempty Ω] (features : I → Ω → C) (allowed : I → Finset C)
    (line : I → Prop) (safe : Ω → Prop) (atom : ℚ) (spike density : Ω → ℚ) where
  mass : expectation (FiniteDist.uniform Ω) (realVector density) = 1
  nonneg : ∀ x, 0 ≤ (density x : ℝ)
  support : ∀ x, ¬ safe x → density x = 0
  lower : ∀ x, safe x → (1 / 3 : ℝ) ≤ density x
  on_line : ∀ i, line i → ∀ c,
    conditional (FiniteDist.uniform Ω) (features i) (realVector density) c =
      if c ∈ allowed i then (Fintype.card C : ℝ) / (allowed i).card else 0
  off_line : ∀ i, ¬ line i → ∀ c,
    conditional (FiniteDist.uniform Ω) (features i)
      ((1 - (atom : ℝ)) • realVector density + (atom : ℝ) • realVector spike) c =
        if c ∈ allowed i then (Fintype.card C : ℝ) / (allowed i).card else 0

theorem regularDensityQ_certificate [Nonempty Ω] [Nonempty C]
    (features : I → Ω → C) (allowed : I → Finset C) (line : I → Prop)
    (hfeature : ∀ i, (FiniteDist.uniform Ω).map (features i) = FiniteDist.uniform C)
    (hpair : ∀ i j, i ≠ j → (FiniteDist.uniform Ω).map (fun x => (features i x, features j x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C))
    (safe : Ω → Prop) (hallowed : ∀ i x, safe x → features i x ∈ allowed i)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hglobal : expectation (FiniteDist.uniform Ω) (badIndicator safe) ≤ δ)
    (hconditional : ∀ i c, c ∈ allowed i →
      conditional (FiniteDist.uniform Ω) (features i) (badIndicator safe) c ≤ δ)
    (hsmall : (2 * Fintype.card I + 1) * δ ≤ 1 / 4)
    (hpositivity : (Fintype.card I : ℝ) / (1 - δ) *
      (δ + ((2 * Fintype.card I + 1) * δ) /
        (1 - (2 * Fintype.card I + 1) * δ)) ≤ 1 / 3)
    (atom : ℚ) (ha0 : 0 ≤ (atom : ℝ)) (haHalf : (atom : ℝ) ≤ 1 / 2)
    (spike : Ω → ℚ) (hsmean : expectation (FiniteDist.uniform Ω) (realVector spike) = 1)
    (hsnonneg : ∀ x, 0 ≤ (spike x : ℝ))
    (hsallowed : ∀ i, ¬ line i → ∀ x, features i x ∉ allowed i → spike x = 0)
    (hsbound : ∀ i, ¬ line i → ∀ c,
      conditional (FiniteDist.uniform Ω) (features i) (realVector spike) c ≤ 1 / (1 - δ)) :
    RegularCertificate features allowed line safe atom spike
      (regularDensityQ features allowed line safe atom spike) := by
  have hquarter : ‖deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe‖ ≤ 1 / 4 :=
    (chartDeletion_norm _ features allowed safe δ hδ0 hglobal hconditional).trans hsmall
  have hD : ‖deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe‖ < 1 :=
    hquarter.trans_lt (by norm_num)
  have h := regularDensity_properties (FiniteDist.uniform Ω) features allowed line hfeature hpair
    safe hallowed δ hδ0 hδ1 hglobal hconditional hsmall hpositivity (atom : ℝ) ha0 haHalf
    (realVector spike) hsmean hsnonneg
    (by intro i hi x hx; change (spike x : ℝ) = 0; rw [hsallowed i hi x hx]; norm_num)
    hsbound hD
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at h
  rw [← regularDensityQ_cast features allowed line safe atom spike hD] at h
  refine ⟨h.1, h.2.1, ?_, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  intro x hx
  exact Rat.cast_injective (by simpa only [realVector, Rat.cast_zero] using h.2.2.1 x hx)

section MarkedFiber

variable {F : Type*} [Field F] [Fintype F]

def markedScaleSet (inputs : I → F × F) (allowed : I → Finset F) (mark : F) : Finset F :=
  Finset.univ.filter (markedScaleSafe inputs allowed mark)

def markedSurvivalQ (inputs : I → F × F) (allowed : I → Finset F) (mark : F) : ℚ :=
  (markedScaleSet inputs allowed mark).card / (Fintype.card F : ℚ)

omit [Fintype I] in
theorem markedSurvivalQ_cast (inputs : I → F × F) (allowed : I → Finset F) (mark : F) :
    (markedSurvivalQ inputs allowed mark : ℝ) = markedSurvival inputs allowed mark := by
  simp only [markedSurvivalQ, Rat.cast_div, Rat.cast_natCast, markedSurvival,
    eventMass, expectation_apply, FiniteDist.uniform_weight, eventIndicator,
    mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp only [markedScaleSet, Finset.sum_const, nsmul_eq_mul]
  ring

/-- The actual normalized marked branch, as a finite rational table. -/
def markedDensityQ (inputs : I → F × F) (allowed : I → Finset F) (mark : F) : Chart F → ℚ :=
  fun chart => (Fintype.card F : ℚ) ^ 2 / markedSurvivalQ inputs allowed mark *
    if chart.1 = mark ∧ chart.2.2 = 0 ∧ markedScaleSafe inputs allowed mark chart.2.1 then 1 else 0

omit [Fintype I] in
theorem markedChartLaw_weight (inputs : I → F × F) (allowed : I → Finset F) (mark : F)
    (hpos : 0 < markedSurvival inputs allowed mark) (chart : Chart F) :
    (markedChartLaw inputs allowed mark hpos).weight chart =
      if chart.1 = mark ∧ chart.2.2 = 0 then
        (markedScaleLaw inputs allowed mark hpos).weight chart.2.1 else 0 := by
  rcases chart with ⟨base, scale, shear⟩
  by_cases hb : base = mark
  · subst base
    by_cases hs : shear = 0
    · subst shear
      simp only [markedChartLaw, FiniteDist.map_weight, Prod.mk.injEq, true_and, and_true,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · simp [markedChartLaw, FiniteDist.map_weight, hs, Ne.symm hs]
  · simp [markedChartLaw, FiniteDist.map_weight, hb, Ne.symm hb]

omit [Fintype I] in
theorem markedDensityQ_cast (inputs : I → F × F) (allowed : I → Finset F) (mark : F)
    (hpos : 0 < markedSurvival inputs allowed mark) :
    realVector (markedDensityQ inputs allowed mark) =
      uniformDensity (markedChartLaw inputs allowed mark hpos) := by
  funext chart
  have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [realVector, markedDensityQ, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_natCast, markedSurvivalQ_cast, uniformDensity, markedChartLaw_weight,
    markedScaleLaw, densityLaw, FiniteDist.uniform_weight, restrictedDensity]
  rw [show eventMass (FiniteDist.uniform F) (markedScaleSafe inputs allowed mark) =
    markedSurvival inputs allowed mark from rfl]
  by_cases hb : chart.1 = mark ∧ chart.2.2 = 0
  · by_cases hs : markedScaleSafe inputs allowed mark chart.2.1
    · simp only [hb.1, hb.2, hs, and_self, if_true, Rat.cast_one, eventIndicator]
      simp only [Chart, Fintype.card_prod, Nat.cast_mul]
      field_simp [hq, hpos.ne']
    · simp only [hb.1, hb.2, hs, and_false, and_self, if_false, if_true, Rat.cast_zero, mul_zero,
        eventIndicator, zero_div]
  · have hn : ¬ (chart.1 = mark ∧ chart.2.2 = 0 ∧ markedScaleSafe inputs allowed mark chart.2.1) :=
      fun h => hb ⟨h.1, h.2.1⟩
    simp only [if_neg hn, if_neg hb, Rat.cast_zero, mul_zero]

def affineFeatures (inputs : I → F × F) : I → Chart F → F :=
  fun i => feature (inputs i).1 (inputs i).2

def affineSafe (inputs : I → F × F) (allowed : I → Finset F) : Chart F → Prop :=
  legalChart (fun chart => chart.2.1) (Finset.univ.erase 0) (affineFeatures inputs) allowed

theorem affine_regular_certificate (inputs : I → F × F) (hinj : Function.Injective inputs)
    (allowed : I → Finset F) (mark : F)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hbudget : affineDeletionBudget allowed ≤ δ)
    (hsmall : (2 * Fintype.card I + 1) * δ ≤ 1 / 4)
    (hpositivity : (Fintype.card I : ℝ) / (1 - δ) *
      (δ + ((2 * Fintype.card I + 1) * δ) /
        (1 - (2 * Fintype.card I + 1) * δ)) ≤ 1 / 3)
    (atom : ℚ) (ha0 : 0 ≤ (atom : ℝ)) (haHalf : (atom : ℝ) ≤ 1 / 2) :
    RegularCertificate (affineFeatures inputs) allowed (fun i => (inputs i).1 = 0)
      (affineSafe inputs allowed) atom (markedDensityQ inputs allowed mark)
      (regularDensityQ (affineFeatures inputs) allowed (fun i => (inputs i).1 = 0)
        (affineSafe inputs allowed) atom (markedDensityQ inputs allowed mark)) := by
  let p := FiniteDist.uniform (Chart F)
  have hfeature (i : I) : p.map (affineFeatures inputs i) = FiniteDist.uniform F := feature_uniform _ _
  have hpair (i j : I) (hij : i ≠ j) :
      p.map (fun x => (affineFeatures inputs i x, affineFeatures inputs j x)) =
        (FiniteDist.uniform F).prod (FiniteDist.uniform F) :=
    feature_pair_uniform (inputs i) (inputs j) (fun h => hij (hinj h))
  have hauxpair (i : I) : p.map (fun x => (affineFeatures inputs i x, x.2.1)) =
      (FiniteDist.uniform F).prod (FiniteDist.uniform F) := feature_scale_uniform _ _
  have hbudgetFormula : expectation (FiniteDist.uniform F) (paletteFailure (Finset.univ.erase 0)) +
      ∑ i, expectation (FiniteDist.uniform F) (paletteFailure (allowed i)) = affineDeletionBudget allowed := by
    rw [nonzero_palette_failure]
    simp only [uniform_palette_failure, affineDeletionBudget]
  have hglobal : expectation p (badIndicator (affineSafe inputs allowed)) ≤ δ := by
    apply le_trans _ hbudget
    rw [← hbudgetFormula]
    exact legalChart_global_budget p (fun chart => chart.2.1) (Finset.univ.erase 0)
      (affineFeatures inputs) allowed scale_uniform hfeature
  have hconditional : ∀ i c, c ∈ allowed i →
      conditional p (affineFeatures inputs i) (badIndicator (affineSafe inputs allowed)) c ≤ δ := by
    intro i c hc
    apply le_trans _ hbudget
    rw [← hbudgetFormula]
    exact legalChart_conditional_budget p _ _ (affineFeatures inputs) allowed hfeature hpair hauxpair i c hc
  have hsurvival : 0 < markedSurvival inputs allowed mark := by
    have hl := markedSurvival_lower inputs allowed mark
    linarith
  have hspike := markedDensityQ_cast inputs allowed mark hsurvival
  apply regularDensityQ_certificate (affineFeatures inputs) allowed (fun i => (inputs i).1 = 0)
    hfeature hpair (affineSafe inputs allowed) (fun i x hx => hx.2 i)
    δ hδ0 hδ1 hglobal hconditional hsmall hpositivity atom ha0 haHalf
    (markedDensityQ inputs allowed mark)
  · rw [hspike]
    exact uniformDensity_mean _
  · intro x
    change realVector (markedDensityQ inputs allowed mark) x ≥ 0
    rw [hspike]
    exact uniformDensity_nonneg _ _
  · intro i hi chart hc
    have hzR : (markedDensityQ inputs allowed mark chart : ℝ) = 0 := by
      change realVector (markedDensityQ inputs allowed mark) chart = (0 : ℝ)
      rw [hspike]
      have hz := markedChartLaw_support inputs allowed mark hsurvival chart
        (by rintro ⟨_, _, _, hh⟩; exact hc (hh i hi))
      simp only [uniformDensity, hz, mul_zero]
    exact_mod_cast hzR
  · intro i hi c
    rw [hspike]
    exact markedDensity_bound inputs allowed mark δ hδ1 hbudget hsurvival i hi c

end MarkedFiber

end
end CurrentAFT.CurrentRationalFlagLaw

end

section







/-!
# A canonical exact rational flag and chart table

The ideal table is built from the literal finite rational response matrix.
It has the same simultaneous marginal and safe-support specification as
the real construction, with no arbitrary selection of a positive law.
The binary finite-iteration implementation is developed separately from
this exact table semantics.
-/

namespace CurrentAFT.CurrentFlagProgram

open AFT AFT.BoundaryCalibration AffineFlagCalibration CurrentRationalFlagLaw
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentRationalFlagLaw.solve CurrentRationalFlagLaw.responseMatrix

variable {F I : Type*} [Field F] [Fintype F] [Fintype I]

structure RationalModel (inputs : I → F × F) (allowed : I → Finset F) (mark : F) (atom : ℚ) where
  model : SimultaneousLaw inputs allowed mark (atom : ℝ)
  table : Bool × Chart F → ℚ
  table_cast : ∀ point, (table point : ℝ) = model.joint.weight point





def regularDensity (inputs : I → F × F) (allowed : I → Finset F) (mark : F) (atom : ℚ) : Chart F → ℚ :=
  regularDensityQ (affineFeatures inputs) allowed (fun i => (inputs i).1 = 0)
    (affineSafe inputs allowed) atom (markedDensityQ inputs allowed mark)

def table (inputs : I → F × F) (allowed : I → Finset F) (mark : F) (atom : ℚ) : Bool × Chart F → ℚ :=
  fun point => if point.1 then atom * ((Fintype.card (Chart F) : ℚ)⁻¹ * markedDensityQ inputs allowed mark point.2)
    else (1 - atom) * ((Fintype.card (Chart F) : ℚ)⁻¹ * regularDensity inputs allowed mark atom point.2)

def make (inputs : I → F × F) (hinj : Function.Injective inputs)
    (allowed : I → Finset F) (mark : F)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hbudget : affineDeletionBudget allowed ≤ δ)
    (hsmall : (2 * Fintype.card I + 1) * δ ≤ 1 / 4)
    (hpositivity : (Fintype.card I : ℝ) / (1 - δ) *
      (δ + ((2 * Fintype.card I + 1) * δ) /
        (1 - (2 * Fintype.card I + 1) * δ)) ≤ 1 / 3)
    (atom : ℚ) (ha0 : 0 ≤ (atom : ℝ)) (haHalf : (atom : ℝ) ≤ 1 / 2) :
    RationalModel inputs allowed mark atom := by
  let densityQ := regularDensity inputs allowed mark atom
  let cert : RegularCertificate (affineFeatures inputs) allowed (fun i => (inputs i).1 = 0)
      (affineSafe inputs allowed) atom (markedDensityQ inputs allowed mark) densityQ :=
    affine_regular_certificate inputs hinj allowed mark δ hδ0 hδ1 hbudget hsmall hpositivity atom ha0 haHalf
  let p := FiniteDist.uniform (Chart F)
  let regular := densityLaw p (realVector densityQ) cert.nonneg cert.mass
  have hsurvival : 0 < markedSurvival inputs allowed mark := by
    have hl := markedSurvival_lower inputs allowed mark
    linarith
  let marked := markedChartLaw inputs allowed mark hsurvival
  let joint := flagLaw (atom : ℝ) ha0 (by linarith : (atom : ℝ) ≤ 1) regular marked
  have hspike : realVector (markedDensityQ inputs allowed mark) = uniformDensity marked :=
    markedDensityQ_cast inputs allowed mark hsurvival
  have hregular (i : I) (hi : (inputs i).1 = 0) (c : F) :
      (regular.map (feature (inputs i).1 (inputs i).2)).weight c =
        if c ∈ allowed i then ((allowed i).card : ℝ)⁻¹ else 0 := by
    rw [densityLaw_marginal]
    have hc := cert.on_line i hi c
    change conditional p (feature (inputs i).1 (inputs i).2) (realVector densityQ) c = _ at hc
    rw [hc]
    split_ifs
    · have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      field_simp
    · simp
  have hon (i : I) (hi : (inputs i).1 = 0) (c : F) :
      (joint.map (fun point => feature (inputs i).1 (inputs i).2 point.2)).weight c =
        (1 - (atom : ℝ)) * (if c ∈ allowed i then ((allowed i).card : ℝ)⁻¹ else 0) +
          (atom : ℝ) * (if c = mark then 1 else 0) := by
    rw [flagLaw_feature, hregular i hi c, markedChartLaw_line inputs allowed mark hsurvival i hi c]
  have hoff (i : I) (hi : (inputs i).1 ≠ 0) (c : F) :
      (joint.map (fun point => feature (inputs i).1 (inputs i).2 point.2)).weight c =
        if c ∈ allowed i then ((allowed i).card : ℝ)⁻¹ else 0 := by
    rw [flagLaw_feature, densityLaw_marginal]
    have hf := cert.off_line i hi c
    change conditional p (affineFeatures inputs i)
      ((1 - (atom : ℝ)) • realVector densityQ + (atom : ℝ) • realVector (markedDensityQ inputs allowed mark)) c = _ at hf
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hf
    rw [hspike, uniformDensity_conditional] at hf
    change (1 - (atom : ℝ)) * (conditional p (affineFeatures inputs i) (realVector densityQ) c /
      Fintype.card F) + (atom : ℝ) * (marked.map (affineFeatures inputs i)).weight c = _
    have hq : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    split_ifs at hf ⊢ <;> field_simp <;> nlinarith [hf]
  let model : SimultaneousLaw inputs allowed mark (atom : ℝ) :=
    { regular := regular
      marked := marked
      joint := joint
      decomposition := by intro point; rfl
      regular_support := by
        intro chart hn
        have hsafe : ¬ affineSafe inputs allowed chart := by
          simpa only [affineSafe, legalChart, affineFeatures, Finset.mem_erase,
            Finset.mem_univ, and_true] using hn
        change p.weight chart * (densityQ chart : ℝ) = 0
        rw [cert.support chart hsafe, Rat.cast_zero, mul_zero]
      regular_lower := by
        intro chart hn hc
        have hsafe : affineSafe inputs allowed chart := by
          simpa only [affineSafe, legalChart, affineFeatures, Finset.mem_erase,
            Finset.mem_univ, and_true] using And.intro hn hc
        change (Fintype.card (Chart F) : ℝ)⁻¹ / 3 ≤
          (Fintype.card (Chart F) : ℝ)⁻¹ * (densityQ chart : ℝ)
        have hh := mul_le_mul_of_nonneg_left (cert.lower chart hsafe)
          (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card (Chart F)) : (0 : ℝ) ≤ _))
        simpa only [div_eq_mul_inv, one_mul] using hh
      marked_support := markedChartLaw_support inputs allowed mark hsurvival
      flag_marginal := flagLaw_flag (atom : ℝ) ha0 (by linarith) regular marked
      on_line := hon
      off_line := hoff }
  refine ⟨model, table inputs allowed mark atom, ?_⟩
  intro point
  have hm : (Fintype.card (Chart F) : ℝ)⁻¹ *
      (markedDensityQ inputs allowed mark point.2 : ℝ) = marked.weight point.2 := by
    have h := congrFun hspike point.2
    change (markedDensityQ inputs allowed mark point.2 : ℝ) =
      (Fintype.card (Chart F) : ℝ) * marked.weight point.2 at h
    rw [h, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]
  change ((if point.1 then atom * ((Fintype.card (Chart F) : ℚ)⁻¹ * markedDensityQ inputs allowed mark point.2)
    else (1 - atom) * ((Fintype.card (Chart F) : ℚ)⁻¹ * densityQ point.2) : ℚ) : ℝ) = _
  rw [model.decomposition]
  cases point.1 <;> simp only [Bool.false_eq_true, if_false, if_true, Rat.cast_mul, Rat.cast_inv,
    Rat.cast_natCast, Rat.cast_sub, Rat.cast_one, hm]
  all_goals rfl

local instance currentFlagModulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩
local instance currentFlagModulusPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩

/-- Exact rational ideal at the current public sizes, for every protected
input simultaneously.  Only public data occur among the arguments. -/
def current (security : ℕ) (baseline : ℤ) (hbaseline : |baseline| ≤ legOffsetBound security)
    (mark : ZMod (Parameters.modulus security)) (atom : ℚ)
    (ha0 : 0 ≤ (atom : ℝ)) (haHalf : (atom : ℝ) ≤ 1 / 2) :
    RationalModel (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
      (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
      mark atom := by
  have hb := leg_budget_conditions security
  exact make (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
    (protectedInputs_injective _ _ (leg_input_separation security))
    (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
    mark (legDeletionUpper security) hb.1 hb.2.1 (protectedPalette_current_budget security baseline hbaseline)
    hb.2.2.1 hb.2.2.2 atom ha0 haHalf

attribute [irreducible] make current

end
end CurrentAFT.CurrentFlagProgram

end

section









/-!
# The current source-independent positive flag and chart law

`currentLaw` is selected once from public offset, prescribed color, and
branch weight.  The protected input is an argument only to its correctness
theorems, never to the sampled distribution.
-/

namespace CurrentAFT.AffineFlagCalibration

open AFT AFT.BoundaryCalibration
open scoped BigOperators Classical

noncomputable section

theorem exists_simultaneousLaw {F I : Type*} [Field F] [Fintype F] [Fintype I]
    (inputs : I → F × F) (hinj : Function.Injective inputs)
    (allowed : I → Finset F) (mark : F)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hbudget : affineDeletionBudget allowed ≤ δ)
    (hsmall : (2 * Fintype.card I + 1) * δ ≤ 1 / 4)
    (hpositivity : (Fintype.card I : ℝ) / (1 - δ) *
      (δ + ((2 * Fintype.card I + 1) * δ) /
        (1 - (2 * Fintype.card I + 1) * δ)) ≤ 1 / 3)
    (atom : ℝ) (ha0 : 0 ≤ atom) (haHalf : atom ≤ 1 / 2) :
    Nonempty (SimultaneousLaw inputs allowed mark atom) := by
  obtain ⟨regular, marked, joint, hjoint, hs, hl, hm, hf, hon, hoff⟩ :=
    affine_flag_law inputs hinj allowed mark δ hδ0 hδ1 hbudget hsmall hpositivity atom ha0 haHalf
  exact ⟨⟨regular, marked, joint, by intro point; rw [hjoint]; rfl,
    hs, hl, hm, hf, hon, hoff⟩⟩

local instance legLawModulusNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

local instance currentModulusPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩

/-- The complete current public law.  All feasibility obligations are
discharged at the current polynomial sizes, for every security parameter. -/
def currentLaw (security : ℕ) (baseline : ℤ) (hbaseline : |baseline| ≤ legOffsetBound security)
    (mark : ZMod (Parameters.modulus security)) (atom : ℝ)
    (ha0 : 0 ≤ atom) (haHalf : atom ≤ 1 / 2) :
    SimultaneousLaw (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
      (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
      mark atom := by
  by_cases hrational : ∃ value : ℚ, (value : ℝ) = atom
  · let value := Classical.choose hrational
    have hvalue : (value : ℝ) = atom := Classical.choose_spec hrational
    have hnonneg : 0 ≤ (value : ℝ) := by rw [hvalue]; exact ha0
    have hhalf : (value : ℝ) ≤ 1 / 2 := by rw [hvalue]; exact haHalf
    exact hvalue ▸ (CurrentFlagProgram.current security baseline hbaseline mark value hnonneg hhalf).model
  · have hb := leg_budget_conditions security
    exact Classical.choice (exists_simultaneousLaw
      (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
      (protectedInputs_injective _ _ (leg_input_separation security))
      (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
      mark (legDeletionUpper security) hb.1 hb.2.1
      (protectedPalette_current_budget security baseline hbaseline) hb.2.2.1 hb.2.2.2 atom ha0 haHalf)









end
end CurrentAFT.AffineFlagCalibration

end

section










/-!
# Evaluating the same public affine law at protected leg inputs

The companion is the canonical modular complement of the evaluated primary.
On the supported charts it has the prescribed safe integer lift.  The
reference second scalar is fixed throughout each identity in this file.
-/

namespace CurrentAFT.AffineFlagCalibration

open AFT AFT.BoundaryCalibration ActualPublicLegCharge
open scoped BigOperators Classical

noncomputable section

local instance pairGraphDecidableEq {A B : Type*} : DecidableEq (A × B) := Classical.decEq _

local instance pairModulusPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩

abbrev Palette (security : ℕ) := ActualControls.Palette security
abbrev Scalar (security : ℕ) := FirstHistogram.Scalar security

def companion (security : ℕ) (shift : ℤ) (primary : Palette security) : Palette security :=
  (ZMod.finEquiv (Parameters.modulus security)).toEquiv.symm
    (-1 + (shift : ZMod (Parameters.modulus security)) -
      (ZMod.finEquiv (Parameters.modulus security)) primary)

def pairProjection (security : ℕ) (shift : ℤ) (primary : Palette security) :
    Palette security × Palette security := (primary, companion security shift primary)









def evaluatedPrimary (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ legOffsetBound security) (mark : Palette security)
    (first second : Scalar security) : FiniteDist (Palette security) :=
  (currentLaw security baseline hbaseline ((ZMod.finEquiv (Parameters.modulus security)) mark)
    (1 / 2) (by norm_num) (by norm_num)).joint.map (fun point =>
      (ZMod.finEquiv (Parameters.modulus security)).toEquiv.symm
        (feature ((first.val : ℤ) : ZMod (Parameters.modulus security))
          ((second.val : ℤ) : ZMod (Parameters.modulus security)) point.2))

def evaluatedPair (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ legOffsetBound security) (mark : Palette security)
    (first second : Scalar security) : FiniteDist (Palette security × Palette security) :=
  (evaluatedPrimary security baseline hbaseline mark first second).map
    (pairProjection security (baseline - second.val))



end
end CurrentAFT.AffineFlagCalibration

end

section








/-!
# Fixed-public-core comparison with the protected reference pair

The real public flag has probability one half.  The auxiliary `marked` bit
in the reference seed has probability `activation`, which also includes the
independent protected first scalar's zero atom.  They are never identified.
The equalities hold with coin, anchor index, blur and the second scalar fixed.
-/

namespace CurrentAFT.AffineFlagCalibration

open AFT AFT.BoundaryCalibration ActualPublicLegCharge DiffuseProfiles
open scoped BigOperators Classical

noncomputable section







def setMarked (security : ℕ) (seed : PublicSeed security) (flag : Bool) : PublicSeed security :=
  { seed with marked := flag }













end
end CurrentAFT.AffineFlagCalibration

end

section













/-!
# Removing the auxiliary activation bits before positive public sampling

The reference activation bit is not the real public chart flag.  Both the
clipped coefficient weight and public charge predicate ignore every such
bit.  Thus their public sampling law can first forget these bits, then use
the genuine half-flag chart completion of `AffineLegReference`.
-/

namespace CurrentAFT.AffineFlagCalibration

open AFT ActualPublicCharge
open scoped BigOperators Classical

noncomputable section

def setActivationBits (security : ℕ) (core : Core security)
    (bits : Fin (Parameters.legCount security) → Bool) : Core security :=
  { core with legs := fun leg =>
      (setMarked security (core.legs leg).1 (bits leg), (core.legs leg).2) }









/-- The actual bounded nonnegative multiplier, including charge selection. -/
def positiveMultiplier (security order : ℕ)
    (coefficient : ActualControls.Coefficients security order) (core : Core security) : ℝ :=
  clip (pulledWeight security order coefficient core) * if publicCharge security core then 1 else 0









end
end CurrentAFT.AffineFlagCalibration

end

section

















namespace AFT
end AFT
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.TVBound
end AFT.FiniteDist.TVBound
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.RootTensor
end AFT.RootTensor
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
namespace AFT.V7Calibration.centeredRootBodyProfile
end AFT.V7Calibration.centeredRootBodyProfile
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile



/-! # Finite Fubini for exposing independent public seeds -/
namespace CurrentAFT.PublicAuxiliaryFubini
open AFT
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

def enumeration {State : Type*} {source : Fintype State} (_law : @FiniteDist State source) : Fintype State := source





















end
end CurrentAFT.PublicAuxiliaryFubini

end

section










namespace AFT
end AFT
namespace AFT.BlockProducts
end AFT.BlockProducts
namespace AFT.FiniteDist
end AFT.FiniteDist



/-! # Exact values on the support of genuine finite kernels -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
variable {State Source Value : Type*} [Fintype State] [Fintype Source]

def HasValue (law : FiniteDist State) (read : State → Value) (value : Value) : Prop :=
  ∀ state, law.weight state ≠ 0 → read state = value







end
end AFT.FiniteDist

namespace AFT.BlockProducts
open scoped BigOperators Classical
noncomputable section
variable {Index Color Group : Type*} [Fintype Index] [Fintype Color] [AddCommMonoid Group]
  (Slots : Index → Type*) [∀ index, Fintype (Slots index)]



end
end AFT.BlockProducts

end

section















/-! # The actual positive channel at its complete public core -/
namespace CurrentAFT.RefinedPublicOutput
open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy ActualBlockFock ActualBlockMean
  ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge PositivePublicChannels
  PublicCoefficientOutput
open HistogramNormalization PhysicalSynthesis
open scoped BigOperators Classical
noncomputable section
local instance refinedFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

abbrev Palette (security : ℕ) := FirstHistogram.Palette security
abbrev Residue (security : ℕ) := ZMod (Parameters.modulus security)

def embed (security : ℕ) (color : Palette security) : Residue security :=
  (ZMod.finEquiv (Parameters.modulus security)) color

theorem embed_shift (security : ℕ) (shift : ℤ) (color : Palette security) :
    embed security (shiftEquiv security shift color) = embed security color + (shift : Residue security) := by
  unfold embed shiftEquiv
  change (ZMod.finEquiv (Parameters.modulus security))
    ((ZMod.finEquiv (Parameters.modulus security)).symm
      ((ZMod.finEquiv (Parameters.modulus security)) color + (shift : Residue security))) = _
  exact RingEquiv.apply_symm_apply _ _

theorem embed_value (security : ℕ) (color : Palette security) :
    embed security color = (color.val : Residue security) :=
  ActualPublicLegCharge.finEquiv_natCast _ _

/-- The same protected scalar enters the actual pair and its attachment.
Only the anchor/blur seed and attachment baseline have become public. -/
def triple (security : ℕ) (root : ℤ) (primary : Palette security)
    (seed : LegCore security) : FiniteDist (Fin 3 → Palette security) :=
  (scalarLaw security).mix (fun scalar =>
    (ActualPublicLegCharge.refinedPair security primary scalar seed.1).map
      (fun pair => PhysicalBlockTensors.tripleEquiv.symm
        (pair, shiftEquiv security (root + scalar.val) seed.2)))



def singleton (security : ℕ) (root : ℤ) (center : Palette security) :
    FiniteDist (Fin 1 → Palette security) :=
  (FixedPairedFirst.pointLaw security (shiftEquiv security root center)).map (fun color _ => color)



def blocks (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (queue : ℤ) (latent : BodyIndex security → Edge security) :
    (index : BlockIndex security) → FiniteDist (Slots security index → Palette security)
  | .inl leg => triple security (attachmentRoots security layout core.bodyPermutation latent leg)
      (core.controls (.inl leg)).1 (core.legs leg)
  | .inr (.inl center) => singleton security (centerRoots security layout core.bodyPermutation latent center)
      (core.controls ((UniformTaggedOutput.centerSplit security).symm center)).2.val
  | .inr (.inr point) => singleton security
      (queueRoots security layout core.bodyPermutation latent point + queue) (core.queueBaselines point)

def blockCharge (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (queue : ℤ) (latent : BodyIndex security → Edge security) :
    BlockIndex security → Residue security
  | .inl leg => -1 + (legShift security core leg : Residue security) + embed security (core.legs leg).2 +
      (attachmentRoots security layout core.bodyPermutation latent leg : Residue security)
  | .inr (.inl center) => embed security
      (core.controls ((UniformTaggedOutput.centerSplit security).symm center)).2.val +
      (centerRoots security layout core.bodyPermutation latent center : Residue security)
  | .inr (.inr point) => embed security (core.queueBaselines point) +
      (queueRoots security layout core.bodyPermutation latent point : Residue security) + (queue : Residue security)







def conditionalLaw (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (queue : ℤ) (latent : BodyIndex security → Edge security) :
    FiniteDist (Sigma (Slots security) → Palette security) :=
  FiniteDist.retype (BlockProducts.blockLaw (Slots security) (blocks security layout core queue latent))



/-- The hidden scalar and complete latent cycle are sampled after the
full public core. Both public permutations were drawn in that core. -/
def lawGiven (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security) :
    FiniteDist (Fin (Parameters.dimension security) → Palette security) :=
  (scalarLaw security).mix (fun queue => (FiniteDist.retype (ActualFockBound.latentLaw security)).mix
    (fun latent => (conditionalLaw security layout core queue.val latent).map
      (fun word => AFT.relabel (renameWord (flatten security) word) core.endpointPermutation)))

def outputEquiv (security : ℕ) (permutation : Equiv.Perm (Fin (Parameters.dimension security))) :
    (Sigma (Slots security) → Palette security) ≃ (Fin (Parameters.dimension security) → Palette security) :=
  (renameWord (flatten security)).trans (AFT.relabelEquiv permutation)





def mappedChannel (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security) :
    FiniteDist (Fin (Parameters.dimension security) → Residue security) :=
  (lawGiven security layout core).map (fun word index => embed security (word index))



end
end CurrentAFT.RefinedPublicOutput

end

section















/-!
# Real public chart completion of a fixed leg core

The complete chart is sampled before, and independently of, both protected
source coordinates.  The retained second coordinate is reused in the
attachment.  The auxiliary activation bit of the old reference core is
ignored by this sampler.
-/

namespace CurrentAFT.AffineFlagCalibration

open AFT AFT.BoundaryCalibration ActualPublicLegCharge ActualPublicCharge DiffuseProfiles ProposalPrimary
open scoped BigOperators Classical

noncomputable section

local instance completionFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

local instance completionPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩



def completionLaw (security : ℕ) (primary : Palette security) (seed : PublicSeed security) :
    FiniteDist (Bool × Chart (ZMod (Parameters.modulus security))) :=
  (currentLaw security (publicShift security primary seed)
    (by simpa only [legOffsetBound, add_sub_assoc] using publicShift_bound security primary seed)
    ((ZMod.finEquiv (Parameters.modulus security)) primary) (1 / 2) (by norm_num) (by norm_num)).joint

def evaluatePrimary (security : ℕ) (chart : Bool × Chart (ZMod (Parameters.modulus security)))
    (first second : Scalar security) : Palette security :=
  (ZMod.finEquiv (Parameters.modulus security)).toEquiv.symm
    (feature ((first.val : ℤ) : ZMod (Parameters.modulus security))
      ((second.val : ℤ) : ZMod (Parameters.modulus security)) chart.2)

def evaluateTriple (security : ℕ) (root : ℤ) (primary : Palette security) (seed : LegCore security)
    (chart : Bool × Chart (ZMod (Parameters.modulus security))) (first second : Scalar security) :
    Fin 3 → Palette security :=
  PhysicalBlockTensors.tripleEquiv.symm
    (pairProjection security (publicShift security primary seed.1 - second.val)
      (evaluatePrimary security chart first second),
      shiftEquiv security (root + second.val) seed.2)

/-- The positive complete chart law is sampled independently of the entire
protected first/second pair.  Both coordinates are subsequently drawn from
their original clipped Gaussian law. -/
def completedTriple (security : ℕ) (root : ℤ) (primary : Palette security) (seed : LegCore security) :
    FiniteDist (Fin 3 → Palette security) :=
  (completionLaw security primary seed.1).mix (fun chart =>
    (scalarLaw security).mix (fun first =>
      (scalarLaw security).map (evaluateTriple security root primary seed chart first)))











end
end CurrentAFT.AffineFlagCalibration

end

section











/-!
# Complete protected output after public affine-chart completion

All roots, queue scalars and permutations are the actual ones.  Each
protected leg uses the complete source-independent public chart law; the
ordinary and queue channels are unchanged.  Averaging auxiliary activation
bits is exactly this completed output, even with the entire remaining core
fixed.
-/

namespace CurrentAFT.ActualAffineCompletedOutput

open AFT AffineFlagCalibration ActualPublicCharge DiffuseProfiles ProposalPrimary
  ActualBlockFock ActualBlockMean ActualCycleMeanMGF ConditionalHistogramMean
  PublicOutputExperiment PublicCoefficientOutput PublicAuxiliaryFubini
open HistogramNormalization PhysicalSynthesis
open scoped BigOperators Classical

noncomputable section

local instance completedOutputFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def activationBitsLaw (security : ℕ) : FiniteDist (Fin (Parameters.legCount security) → Bool) :=
  FiniteDist.independent (fun _ => ActualPublicLegCharge.activationLaw security)

def blocks (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (queue : ℤ) (latent : BodyIndex security → Edge security) :
    (index : BlockIndex security) → FiniteDist (Slots security index → RefinedPublicOutput.Palette security)
  | .inl leg => completedTriple security (attachmentRoots security layout core.bodyPermutation latent leg)
      (core.controls (.inl leg)).1 (core.legs leg)
  | .inr (.inl center) => RefinedPublicOutput.singleton security
      (centerRoots security layout core.bodyPermutation latent center)
      (core.controls ((UniformTaggedOutput.centerSplit security).symm center)).2.val
  | .inr (.inr point) => RefinedPublicOutput.singleton security
      (queueRoots security layout core.bodyPermutation latent point + queue) (core.queueBaselines point)

def conditionalLaw (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (queue : ℤ) (latent : BodyIndex security → Edge security) :
    FiniteDist (Sigma (Slots security) → RefinedPublicOutput.Palette security) :=
  FiniteDist.retype (BlockProducts.blockLaw (Slots security) (blocks security layout core queue latent))



def lawGiven (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security) :
    FiniteDist (Fin (Parameters.dimension security) → RefinedPublicOutput.Palette security) :=
  (scalarLaw security).mix (fun queue => (FiniteDist.retype (ActualFockBound.latentLaw security)).mix
    (fun latent => (conditionalLaw security layout core queue.val latent).map
      (fun word => AFT.relabel (renameWord (flatten security) word) core.endpointPermutation)))



def mappedChannel (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security) :
    FiniteDist (Fin (Parameters.dimension security) → RefinedPublicOutput.Residue security) :=
  (lawGiven security layout core).map (fun word index => RefinedPublicOutput.embed security (word index))



end
end CurrentAFT.ActualAffineCompletedOutput

end

end

section

section











/-!
# Closed stability bound for the actual complete same-queue background

All three role atoms and their populations are the concrete current
families. The only large-parameter condition below is an explicit numerical
threshold. No small-background or response-size hypothesis is supplied.
-/

namespace CurrentAFT.ActualBackground

open AFT GradedControlAlgebra GradedControlNorm GradedControlStability RoleProduct
  DiffuseProfiles ProposalPrimary ActualControls BackgroundRates BackgroundFamilies
  BackgroundLinear LegBackgroundFamilies BackgroundScalarZero BackgroundPopulationBounds
open Filter
open scoped BigOperators Classical Topology

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount ProposalPrimary.primaryLaw ActualControls.bodyReference
  BackgroundFamilies.freeCertificate BackgroundFamilies.translationCertificate LegBackgroundFamilies.completeLegAtom

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def numericalThreshold : ℕ := 10000000000000000

def budget (security : ℕ) : ℝ := (numericalThreshold : ℝ) / (Parameters.base security : ℝ) ^ 6

theorem budget_nonneg (security : ℕ) : 0 ≤ budget security := by unfold budget; positivity

theorem rate_le_budget (security : ℕ) (numerator : ℝ) (exponent : ℕ)
    (hnum : 0 ≤ numerator) (hupper : numerator ≤ numericalThreshold) (hexponent : 6 ≤ exponent) :
    numerator / (Parameters.base security : ℝ) ^ exponent ≤ budget security := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  exact (div_le_div_of_nonneg_left hnum (pow_pos hb _) (pow_le_pow_right₀ hb1 hexponent)).trans
    (div_le_div_of_nonneg_right hupper (pow_nonneg hb.le _))

theorem budget_le_one (security : ℕ) (hsecurity : numericalThreshold ≤ security) : budget security ≤ 1 := by
  have hb := FirstResponse.base_pos security
  have hbase : (numericalThreshold : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show numericalThreshold ≤ Parameters.base security by unfold Parameters.base; omega)
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hpower : (numericalThreshold : ℝ) ≤ (Parameters.base security : ℝ) ^ 6 :=
    hbase.trans (by simpa only [pow_one] using pow_le_pow_right₀ hb1 (show 1 ≤ 6 by omega))
  exact (div_le_one (pow_pos hb _)).mpr hpower

theorem role_count_lower (security order : ℕ) (horder : order ≤ security) :
    order ≤ freeCount security + Parameters.modulus security + Parameters.legCount security := by
  have hbase : order ≤ Parameters.base security := by unfold Parameters.base; omega
  have hleg : Parameters.base security ≤ Parameters.legCount security := by
    rw [Parameters.legCount_eq]
    exact Nat.le_self_pow (by omega : 128 ≠ 0) _
  omega

def fixedQueueBackground (security order : ℕ) (horder : 2 ≤ order) (queueShift : ℤ) : ActualFamily security order :=
  (1 + freeCertificate security order (by omega)) ^ freeCount security *
    (1 + translationCertificate security order (by omega) queueShift) ^ Parameters.modulus security *
    (1 + completeLegAtom security order horder) ^ Parameters.legCount security

def background (security order : ℕ) (horder : 2 ≤ order) : ActualFamily security order :=
  ∑ scalar, (scalarLaw security).weight scalar • fixedQueueBackground security order horder scalar.val

theorem nat_role_sum_eq (security order : ℕ) (horder : 2 ≤ order) (queueShift : ℤ) :
    freeCount security • freeCertificate security order (by omega) +
      Parameters.modulus security • translationCertificate security order (by omega) queueShift +
      Parameters.legCount security • completeLegAtom security order horder = combinedFirstSum security order horder queueShift := by
  unfold combinedFirstSum
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, freeCount_cast]

theorem fixedQueueBackground_norm (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : max order numericalThreshold ≤ security) (queueShift : ℤ) :
    certificateNorm security order (fixedQueueBackground security order horder queueShift - 1) ≤
      (order : ℝ) * budget security * ((order + 1 : ℕ) : ℝ) ^ order := by
  have hb := FirstResponse.base_pos security
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hbdy : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  have hsmall := budget_le_one security ((le_max_right order numericalThreshold).trans hsecurity)
  have hfree : certificateNorm security order (freeCertificate security order (by omega)) ≤ budget security :=
    (freeCertificate_norm_decay security order (by omega)).trans
      (rate_le_budget security 84 110 (by norm_num) (by norm_num [numericalThreshold]) (by omega))
  have hqueue : certificateNorm security order (translationCertificate security order (by omega) queueShift) ≤ budget security :=
    (translationCertificate_norm_decay security order (by omega) queueShift).trans
      (rate_le_budget security 56 79 (by norm_num) (by norm_num [numericalThreshold]) (by omega))
  have hleg : certificateNorm security order (completeLegAtom security order horder) ≤ budget security :=
    (completeLegAtom_norm security order horder).trans
      (rate_le_budget security 43377248 78 (by norm_num) (by norm_num [numericalThreshold]) (by omega))
  have hfirst : certificateNorm security order
      (freeCount security • freeCertificate security order (by omega) +
        Parameters.modulus security • translationCertificate security order (by omega) queueShift +
        Parameters.legCount security • completeLegAtom security order horder) ≤ budget security := by
    rw [nat_role_sum_eq]
    exact (combinedFirstSum_norm security order horder queueShift).trans
      (rate_le_budget security 39707232 6 (by norm_num) (by norm_num [numericalThreshold]) (by omega))
  have hsquares : (freeCount security : ℝ) * certificateNorm security order (freeCertificate security order (by omega)) ^ 2 +
      (Parameters.modulus security : ℝ) * certificateNorm security order (translationCertificate security order (by omega) queueShift) ^ 2 +
      (Parameters.legCount security : ℝ) * certificateNorm security order (completeLegAtom security order horder) ^ 2 ≤ budget security :=
    (square_population security order horder queueShift).trans
      (rate_le_budget security 1881586979939328 28 (by norm_num) (by norm_num [numericalThreshold]) (by omega))
  exact complete_role_product_norm_le (primaryLaw security) (bodyReference security) order
    (primaryFactor security) (bodyFactor security) hp hbdy (freeCount security) (Parameters.modulus security) (Parameters.legCount security)
    (role_count_lower security order ((le_max_left order numericalThreshold).trans hsecurity))
    (freeCertificate security order (by omega)) (translationCertificate security order (by omega) queueShift) (completeLegAtom security order horder)
    (freeCertificate_zero security order (by omega)) (translationCertificate_zero security order (by omega) queueShift)
    (completeLegAtom_zero security order horder) (budget security) (budget_nonneg security) hsmall hfirst hsquares
    (hfree.trans hsmall) (hqueue.trans hsmall) (hleg.trans hsmall)

theorem background_sub_one (security order : ℕ) (horder : 2 ≤ order) :
    background security order horder - 1 =
      ∑ scalar, (scalarLaw security).weight scalar • (fixedQueueBackground security order horder scalar.val - 1) := by
  simp only [background, smul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_smul, FiniteDist.sum_one, one_smul]

theorem background_norm (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : max order numericalThreshold ≤ security) :
    certificateNorm security order (background security order horder - 1) ≤
      (order : ℝ) * budget security * ((order + 1 : ℕ) : ℝ) ^ order := by
  rw [background_sub_one]
  exact certificateNorm_average_le security order (scalarLaw security) _ _
    (fun scalar => fixedQueueBackground_norm security order horder hsecurity scalar.val)

def stabilityConstant (order : ℕ) : ℝ :=
  (order : ℝ) * ((order + 1 : ℕ) : ℝ) ^ order * numericalThreshold

theorem background_norm_decay (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : max order numericalThreshold ≤ security) :
    certificateNorm security order (background security order horder - 1) ≤
      stabilityConstant order / (Parameters.base security : ℝ) ^ 6 := by
  apply (background_norm security order horder hsecurity).trans_eq
  unfold budget stabilityConstant
  ring

theorem background_norm_decay_eventually (order : ℕ) (horder : 2 ≤ order) :
    ∀ᶠ security : ℕ in atTop, certificateNorm security order (background security order horder - 1) ≤
      stabilityConstant order / (Parameters.base security : ℝ) ^ 6 := by
  filter_upwards [eventually_ge_atTop (max order numericalThreshold)] with security hsecurity
  exact background_norm_decay security order horder hsecurity

end

end CurrentAFT.ActualBackground

end

section





/-!
# The literal truncated endpoint polynomial algebra

Elements are actual real multivariate polynomials fixed by the total-degree
cutoff. Multiplication is their actual polynomial product followed by that
cutoff. The ring and real-algebra laws follow from the proved coefficient
truncation identities; they are not abstract response assumptions.
-/

namespace CurrentAFT.TruncatedOutput

open AFT.RepresentedPolynomial
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {Variable : Type*}

def cut (order : ℕ) (polynomial : MvPolynomial Variable ℝ) : MvPolynomial Variable ℝ :=
  truncate (fun _ => 1) order polynomial

theorem cut_smul (order : ℕ) (scalar : ℝ) (polynomial : MvPolynomial Variable ℝ) :
    cut order (scalar • polynomial) = scalar • cut order polynomial := by
  ext powers
  simp only [cut, coeff_truncate, MvPolynomial.coeff_smul, smul_eq_mul]
  split_ifs <;> simp

theorem cut_constant (order : ℕ) (scalar : ℝ) : cut order (MvPolynomial.C scalar : MvPolynomial Variable ℝ) =
    MvPolynomial.C scalar := by
  ext powers
  by_cases hzero : powers = 0
  · subst powers
    simp only [cut, coeff_truncate, weightedOrder_zero, Nat.zero_le, if_true]
  · simp only [cut, coeff_truncate, MvPolynomial.coeff_C, Ne.symm hzero, if_false, ite_self]

def space (Variable : Type*) (order : ℕ) : Submodule ℝ (MvPolynomial Variable ℝ) where
  carrier := {polynomial | cut order polynomial = polynomial}
  zero_mem' := truncate_zero _ _
  add_mem' := by
    intro first second hfirst hsecond
    change cut order (first + second) = first + second
    rw [cut, truncate_add, ← cut, ← cut, hfirst, hsecond]
  smul_mem' := by
    intro scalar polynomial hpolynomial
    change cut order (scalar • polynomial) = scalar • polynomial
    change cut order polynomial = polynomial at hpolynomial
    rw [cut_smul, hpolynomial]

abbrev Polynomial (Variable : Type*) (order : ℕ) := space Variable order

def project (order : ℕ) (polynomial : MvPolynomial Variable ℝ) : Polynomial Variable order :=
  ⟨cut order polynomial, truncate_idempotent _ _ _⟩

instance polynomialOne (order : ℕ) : One (Polynomial Variable order) :=
  ⟨⟨1, truncate_one _ _⟩⟩

instance polynomialMul (order : ℕ) : Mul (Polynomial Variable order) :=
  ⟨fun first second => project order (first.val * second.val)⟩

instance polynomialNatCast (order : ℕ) : NatCast (Polynomial Variable order) :=
  ⟨fun natural => natural • (1 : Polynomial Variable order)⟩

instance polynomialIntCast (order : ℕ) : IntCast (Polynomial Variable order) :=
  ⟨fun integer => integer • (1 : Polynomial Variable order)⟩

theorem polynomial_mul_assoc (order : ℕ) (first second third : Polynomial Variable order) :
    first * second * third = first * (second * third) := by
  apply Subtype.ext
  change cut order (cut order (first.val * second.val) * third.val) =
    cut order (first.val * cut order (second.val * third.val))
  have hleft := truncate_mul (fun _ : Variable => 1) order (first.val * second.val) third.val
  have hright := truncate_mul (fun _ : Variable => 1) order first.val (second.val * third.val)
  change cut order (first.val * second.val * third.val) =
    cut order (cut order (first.val * second.val) * cut order third.val) at hleft
  change cut order (first.val * (second.val * third.val)) =
    cut order (cut order first.val * cut order (second.val * third.val)) at hright
  rw [third.property] at hleft
  rw [first.property] at hright
  exact hleft.symm.trans ((congrArg (cut order) (mul_assoc first.val second.val third.val)).trans hright)

instance polynomialCommRing (order : ℕ) : CommRing (Polynomial Variable order) where
  toAddCommGroup := inferInstanceAs (AddCommGroup (Polynomial Variable order))
  mul first second := project order (first.val * second.val)
  one := ⟨1, truncate_one _ _⟩
  mul_assoc := polynomial_mul_assoc order
  mul_comm first second := by apply Subtype.ext; exact congrArg (cut order) (mul_comm first.val second.val)
  one_mul polynomial := by apply Subtype.ext; change cut order (1 * polynomial.val) = _; rw [one_mul, polynomial.property]
  mul_one polynomial := by apply Subtype.ext; change cut order (polynomial.val * 1) = _; rw [mul_one, polynomial.property]
  zero_mul polynomial := by apply Subtype.ext; change cut order (0 * polynomial.val) = _; simp only [zero_mul, cut, truncate_zero, Submodule.coe_zero]
  mul_zero polynomial := by apply Subtype.ext; change cut order (polynomial.val * 0) = _; simp only [mul_zero, cut, truncate_zero, Submodule.coe_zero]
  left_distrib first second third := by
    apply Subtype.ext
    change cut order (first.val * (second.val + third.val)) = cut order (first.val * second.val) + cut order (first.val * third.val)
    simp only [mul_add, cut, truncate_add]
  right_distrib first second third := by
    apply Subtype.ext
    change cut order ((first.val + second.val) * third.val) = cut order (first.val * third.val) + cut order (second.val * third.val)
    simp only [add_mul, cut, truncate_add]
  natCast natural := natural • (1 : Polynomial Variable order)
  natCast_zero := zero_nsmul _
  natCast_succ natural := by rw [add_nsmul, one_nsmul]
  intCast integer := integer • (1 : Polynomial Variable order)
  intCast_ofNat natural := by
    change (natural : ℤ) • (1 : Polynomial Variable order) = natural • (1 : Polynomial Variable order)
    simp
  intCast_negSucc natural := by
    change (Int.negSucc natural) • (1 : Polynomial Variable order) = -((natural + 1) • (1 : Polynomial Variable order))
    simp

theorem polynomial_smul_mul (order : ℕ) (scalar : ℝ) (first second : Polynomial Variable order) :
    (scalar • first) * second = scalar • (first * second) := by
  apply Subtype.ext
  change cut order ((scalar • first.val) * second.val) = scalar • cut order (first.val * second.val)
  rw [smul_mul_assoc, cut_smul]

theorem polynomial_mul_smul (order : ℕ) (scalar : ℝ) (first second : Polynomial Variable order) :
    first * (scalar • second) = scalar • (first * second) := by
  rw [mul_comm first, polynomial_smul_mul, mul_comm second]

instance polynomialAlgebra (order : ℕ) : Algebra ℝ (Polynomial Variable order) :=
  Algebra.ofModule (polynomial_smul_mul order) (polynomial_mul_smul order)

def quotientMap (order : ℕ) : MvPolynomial Variable ℝ →ₐ[ℝ] Polynomial Variable order where
  toFun := project order
  map_zero' := by apply Subtype.ext; exact truncate_zero _ _
  map_one' := by apply Subtype.ext; exact truncate_one _ _
  map_add' first second := by apply Subtype.ext; exact truncate_add _ _ first second
  map_mul' first second := by apply Subtype.ext; exact truncate_mul _ _ first second
  commutes' scalar := by
    apply Subtype.ext
    change cut order (MvPolynomial.C scalar) = scalar • (1 : MvPolynomial Variable ℝ)
    rw [cut_constant, Algebra.smul_def, mul_one]
    rfl

end

end CurrentAFT.TruncatedOutput

end

section














/-!
# Literal endpoint evaluation of two-pool control kernels

The primary and body alphabets may differ. Every coefficient below is the
finite reference expectation of the actual joint kernel. Slot relabeling,
permutation averaging and disjoint-slot multiplication are proved identities
of these polynomials.
-/

namespace CurrentAFT.LeadingEvaluation

open AFT ControlCoordinates ControlProduct GradedControlAlgebra
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) :=
  Classical.decEq _

variable {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]

def kernelPolynomial {PS BS : Type*} [Fintype PS] [Fintype BS]
    (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) : MvPolynomial Variable ℝ :=
  ∑ colors : PS → Primary, ∑ centers : BS → Body,
    MvPolynomial.C ((∏ index, primary.weight (colors index)) *
      (∏ index, body.weight (centers index)) * kernel colors centers) *
      ((∏ index, primaryForm (colors index)) * ∏ index, bodyForm (centers index))

def kernelLinear {PS BS : Type*} [Fintype PS] [Fintype BS]
    (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ) :
    Kernel (Primary := Primary) (Body := Body) PS BS →ₗ[ℝ] MvPolynomial Variable ℝ where
  toFun := kernelPolynomial primary body primaryForm bodyForm
  map_add' first second := by
    simp only [kernelPolynomial, Pi.add_apply, mul_add, map_add, add_mul,
      Finset.sum_add_distrib]
  map_smul' scalar kernel := by
    simp only [kernelPolynomial, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Algebra.smul_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro colors _
    apply Finset.sum_congr rfl
    intro centers _
    simp only [map_mul, MvPolynomial.algebraMap_eq]
    ring

theorem kernelPolynomial_reindex {PS BS PT BT : Type*}
    [Fintype PS] [Fintype BS] [Fintype PT] [Fintype BT]
    (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ)
    (primaryEquiv : PS ≃ PT) (bodyEquiv : BS ≃ BT)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    kernelPolynomial primary body primaryForm bodyForm
      (reindexKernel primaryEquiv bodyEquiv kernel) =
      kernelPolynomial primary body primaryForm bodyForm kernel := by
  unfold kernelPolynomial
  rw [← (HistogramNormalization.renameWord (Color := Primary) primaryEquiv).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro colors _
  rw [← (HistogramNormalization.renameWord (Color := Body) bodyEquiv).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro centers _
  have hp := primaryEquiv.prod_comp (fun index => primary.weight (colors index))
  have hb := bodyEquiv.prod_comp (fun index => body.weight (centers index))
  have hpf := primaryEquiv.prod_comp (fun index => primaryForm (colors index))
  have hbf := bodyEquiv.prod_comp (fun index => bodyForm (centers index))
  simp only [HistogramNormalization.renameWord, Equiv.coe_fn_symm_mk, reindexKernel,
    Function.comp_def] at *
  rw [hp, hb, hpf, hbf]

theorem kernelPolynomial_symmetrize {PS BS : Type*} [Fintype PS] [Fintype BS]
    (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    kernelPolynomial primary body primaryForm bodyForm (symmetrize kernel) =
      kernelPolynomial primary body primaryForm bodyForm kernel := by
  change kernelLinear primary body primaryForm bodyForm (symmetrize kernel) = _
  simp only [ControlProduct.symmetrize, map_sum, map_smul]
  change (∑ primaryOrder : Equiv.Perm PS, (FiniteDist.uniform _).weight primaryOrder •
    ∑ bodyOrder : Equiv.Perm BS, (FiniteDist.uniform _).weight bodyOrder •
      kernelPolynomial primary body primaryForm bodyForm
        (reindexKernel primaryOrder bodyOrder kernel)) = _
  simp only [kernelPolynomial_reindex, ← Finset.sum_smul,
    (FiniteDist.uniform (Equiv.Perm BS)).sum_one,
    (FiniteDist.uniform (Equiv.Perm PS)).sum_one, one_smul]

theorem kernelPolynomial_disjointTensor {PS BS PT BT : Type*}
    [Fintype PS] [Fintype BS] [Fintype PT] [Fintype BT]
    (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ)
    (first : Kernel (Primary := Primary) (Body := Body) PS BS)
    (second : Kernel (Primary := Primary) (Body := Body) PT BT) :
    kernelPolynomial primary body primaryForm bodyForm (disjointTensor first second) =
      kernelPolynomial primary body primaryForm bodyForm first *
        kernelPolynomial primary body primaryForm bodyForm second := by
  unfold kernelPolynomial
  rw [← (Equiv.sumArrowEquivProdArrow PS PT Primary).symm.sum_comp,
    Fintype.sum_prod_type]
  conv_rhs =>
    rw [Finset.sum_mul]
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro leftColors _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro rightColors _
  rw [← (Equiv.sumArrowEquivProdArrow BS BT Body).symm.sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro leftCenters _
  apply Finset.sum_congr rfl
  intro rightCenters _
  simp only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_symm_mk, Fintype.prod_sum_type,
    Sum.elim_inl, Sum.elim_inr, disjointTensor, Function.comp_def, map_mul]
  ring

theorem kernelPolynomial_homogeneousProduct
    (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ)
    {r s r' s' : ℕ} (first : canonicalKernels primary body r s)
    (second : canonicalKernels primary body r' s') :
    kernelPolynomial primary body primaryForm bodyForm
      (homogeneousProduct primary body first second).val =
      kernelPolynomial primary body primaryForm bodyForm first.val *
        kernelPolynomial primary body primaryForm bodyForm second.val := by
  change kernelPolynomial primary body primaryForm bodyForm
    (symmetrize (finDisjointTensor first.val second.val)) = _
  rw [kernelPolynomial_symmetrize]
  unfold finDisjointTensor
  rw [kernelPolynomial_reindex, kernelPolynomial_disjointTensor]

theorem kernelPolynomial_homogeneous {PS BS : Type*} [Fintype PS] [Fintype BS]
    (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ)
    (hprimary : ∀ color, (primaryForm color).IsHomogeneous 1)
    (hbody : ∀ color, (bodyForm color).IsHomogeneous 1)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    (kernelPolynomial primary body primaryForm bodyForm kernel).IsHomogeneous
      (Fintype.card PS + Fintype.card BS) := by
  apply MvPolynomial.IsHomogeneous.sum
  intro colors _
  apply MvPolynomial.IsHomogeneous.sum
  intro centers _
  apply MvPolynomial.IsHomogeneous.C_mul
  convert (MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun index : PS => primaryForm (colors index)) (fun _ => 1)
    (fun index _ => hprimary (colors index))).mul
    (MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun index : BS => bodyForm (centers index)) (fun _ => 1)
      (fun index _ => hbody (centers index))) using 1
  simp

end

end CurrentAFT.LeadingEvaluation

end

section









/-! # The actual truncated endpoint evaluation of canonical kernel families -/

namespace CurrentAFT.LeadingEvaluation

open AFT ControlCoordinates ControlProduct GradedControlAlgebra
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

local instance familyFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]

def homogeneousLinear (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ) (order r s : ℕ) :
    canonicalKernels primary body r s →ₗ[ℝ] TruncatedOutput.Polynomial Variable order :=
  (TruncatedOutput.quotientMap order).toLinearMap.comp
    ((kernelLinear primary body primaryForm bodyForm).comp
      (Submodule.subtype (canonicalKernels primary body r s)))

def familyLinear (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ) (order : ℕ) :
    KernelFamily primary body order →ₗ[ℝ] TruncatedOutput.Polynomial Variable order :=
  ∑ arity : TruncatedArity order,
    (homogeneousLinear primary body primaryForm bodyForm order arity.val.1.val arity.val.2.val).comp
      (LinearMap.proj arity)



theorem familyLinear_single (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ) (order : ℕ)
    (arity : TruncatedArity order)
    (kernel : canonicalKernels primary body arity.val.1.val arity.val.2.val) :
    familyLinear primary body primaryForm bodyForm order (Pi.single arity kernel) =
      homogeneousLinear primary body primaryForm bodyForm order _ _ kernel := by
  simp only [familyLinear, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  change (∑ other : TruncatedArity order,
    homogeneousLinear primary body primaryForm bodyForm order other.val.1.val other.val.2.val
      ((Pi.single arity kernel : KernelFamily primary body order) other)) = _
  rw [Finset.sum_eq_single arity]
  · rw [Pi.single_eq_same]
  · intro other _ hother
    rw [Pi.single_eq_of_ne (M := fun index : TruncatedArity order =>
      canonicalKernels primary body index.val.1.val index.val.2.val) hother, map_zero]
  · simp

theorem kernelPolynomial_scalar (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ) (scalar : ℝ) :
    kernelPolynomial primary body primaryForm bodyForm (scalarKernel primary body scalar).val =
      MvPolynomial.C scalar := by
  simp [kernelPolynomial, scalarKernel]

theorem familyLinear_one (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ) (order : ℕ) :
    familyLinear primary body primaryForm bodyForm order 1 = 1 := by
  have hunit : scalarUnit primary body = scalarKernel primary body 1 := by
    apply Subtype.ext
    rfl
  change familyLinear primary body primaryForm bodyForm order
    (Pi.single (zeroArity order) (scalarUnit primary body)) = _
  rw [hunit]
  rw [familyLinear_single]
  change TruncatedOutput.quotientMap order
    (kernelPolynomial primary body primaryForm bodyForm (scalarKernel primary body 1).val) = _
  rw [kernelPolynomial_scalar, map_one, map_one]

theorem homogeneousLinear_product (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ) (order : ℕ)
    {r s r' s' : ℕ} (first : canonicalKernels primary body r s)
    (second : canonicalKernels primary body r' s') :
    homogeneousLinear primary body primaryForm bodyForm order (r + r') (s + s')
      (homogeneousProduct primary body first second) =
      homogeneousLinear primary body primaryForm bodyForm order r s first *
        homogeneousLinear primary body primaryForm bodyForm order r' s' second := by
  change TruncatedOutput.quotientMap order
    (kernelPolynomial primary body primaryForm bodyForm (homogeneousProduct primary body first second).val) = _
  rw [kernelPolynomial_homogeneousProduct, map_mul]
  rfl

theorem homogeneousLinear_above (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ)
    (hprimary : ∀ color, (primaryForm color).IsHomogeneous 1)
    (hbody : ∀ color, (bodyForm color).IsHomogeneous 1)
    (order r s : ℕ) (habove : order < r + s)
    (kernel : canonicalKernels primary body r s) :
    homogeneousLinear primary body primaryForm bodyForm order r s kernel = 0 := by
  apply Subtype.ext
  change AFT.RepresentedPolynomial.truncate (fun _ : Variable => 1) order
    (kernelPolynomial primary body primaryForm bodyForm kernel.val) = 0
  have hhomogeneous := kernelPolynomial_homogeneous primary body primaryForm bodyForm
    hprimary hbody kernel.val
  simp only [Fintype.card_fin] at hhomogeneous
  ext powers
  rw [AFT.RepresentedPolynomial.coeff_truncate, MvPolynomial.coeff_zero]
  split_ifs with hdegree
  · apply hhomogeneous.coeff_eq_zero
    have hne : AFT.RepresentedPolynomial.weightedOrder (fun _ : Variable => 1) powers ≠ r + s := by omega
    simpa only [AFT.RepresentedPolynomial.weightedOrder, mul_one, Finsupp.sum, Finsupp.degree_apply] using hne
  · rfl

theorem familyLinear_single_product (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ)
    (hprimary : ∀ color, (primaryForm color).IsHomogeneous 1)
    (hbody : ∀ color, (bodyForm color).IsHomogeneous 1) (order : ℕ)
    (left right : TruncatedArity order)
    (first : canonicalKernels primary body left.val.1.val left.val.2.val)
    (second : canonicalKernels primary body right.val.1.val right.val.2.val) :
    familyLinear primary body primaryForm bodyForm order
      ((Pi.single left first : KernelFamily primary body order) * Pi.single right second) =
      familyLinear primary body primaryForm bodyForm order (Pi.single left first) *
        familyLinear primary body primaryForm bodyForm order (Pi.single right second) := by
  rw [familyLinear_single, familyLinear_single]
  change familyLinear primary body primaryForm bodyForm order
    (familyProduct primary body order (Pi.single left first) (Pi.single right second)) = _
  by_cases hdegree : (left.val.1.val + right.val.1.val) +
      (left.val.2.val + right.val.2.val) ≤ order
  · rw [familyProduct_single_retained primary body order left right first second hdegree,
      familyLinear_single]
    exact homogeneousLinear_product primary body primaryForm bodyForm order first second
  · rw [familyProduct_single_dropped primary body order left right first second (by omega), map_zero]
    rw [← homogeneousLinear_product]
    exact (homogeneousLinear_above primary body primaryForm bodyForm hprimary hbody order _ _
      (by omega) (homogeneousProduct primary body first second)).symm

theorem familyLinear_product (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ)
    (hprimary : ∀ color, (primaryForm color).IsHomogeneous 1)
    (hbody : ∀ color, (bodyForm color).IsHomogeneous 1) (order : ℕ)
    (first second : KernelFamily primary body order) :
    familyLinear primary body primaryForm bodyForm order (first * second) =
      familyLinear primary body primaryForm bodyForm order first *
        familyLinear primary body primaryForm bodyForm order second := by
  let evaluation := familyLinear primary body primaryForm bodyForm order
  have hfirst : first = ∑ arity, Pi.single arity (first arity) :=
    (Finset.univ_sum_single first).symm
  have hsecond : second = ∑ arity, Pi.single arity (second arity) :=
    (Finset.univ_sum_single second).symm
  change evaluation (first * second) = evaluation first * evaluation second
  conv_lhs => rw [hfirst, hsecond]
  conv_rhs => rw [hfirst, hsecond]
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  exact familyLinear_single_product primary body primaryForm bodyForm hprimary hbody order
    right left (first right) (second left)

instance familyRealAlgebra (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    Algebra ℝ (KernelFamily primary body order) :=
  Algebra.ofModule (CommonQueueAssembly.family_smul_mul primary body order)
    (CommonQueueAssembly.family_mul_smul primary body order)

/-- Evaluation is an algebra homomorphism because it evaluates the actual
disjoint tensors and kills precisely the terms beyond the stated cutoff. -/
def familyHom (primary : FiniteDist Primary) (body : FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ)
    (hprimary : ∀ color, (primaryForm color).IsHomogeneous 1)
    (hbody : ∀ color, (bodyForm color).IsHomogeneous 1) (order : ℕ) :
    KernelFamily primary body order →ₐ[ℝ] TruncatedOutput.Polynomial Variable order where
  toFun := familyLinear primary body primaryForm bodyForm order
  map_zero' := map_zero _
  map_one' := familyLinear_one primary body primaryForm bodyForm order
  map_add' := map_add _
  map_mul' := familyLinear_product primary body primaryForm bodyForm hprimary hbody order
  commutes' scalar := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, familyLinear_one,
      Algebra.algebraMap_eq_smul_one]

end

end CurrentAFT.LeadingEvaluation

end

section









/-! # The actual scalar-coordinate algebra homomorphism -/

namespace CurrentAFT.Augmentation

open AFT ControlCoordinates ControlProduct GradedControlAlgebra
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

theorem arity_eq_zero (order : ℕ) (arity : TruncatedArity order)
    (hprimary : arity.val.1.val = 0) (hbody : arity.val.2.val = 0) :
    arity = zeroArity order := by
  apply Subtype.ext
  exact Prod.ext (Fin.ext hprimary) (Fin.ext hbody)

theorem product_zero_fiber (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first second : KernelFamily primary body order) :
    (first * second) (zeroArity order) =
      homogeneousProduct primary body (first (zeroArity order)) (second (zeroArity order)) := by
  change familyProduct primary body order first second (zeroArity order) = _
  unfold familyProduct
  rw [Finset.sum_eq_single (zeroArity order)]
  · rw [Finset.sum_eq_single (zeroArity order)]
    · rw [dif_pos ⟨rfl, rfl⟩]
      rfl
    · intro right _ hright
      rw [dif_neg]
      intro hmatch
      apply hright
      apply arity_eq_zero order right <;> simp only [zeroArity, Fin.val_zero, zero_add] at hmatch
      · exact hmatch.1
      · exact hmatch.2
    · simp
  · intro left _ hleft
    apply Finset.sum_eq_zero
    intro right _
    rw [dif_neg]
    intro hmatch
    apply hleft
    apply arity_eq_zero order left <;> simp only [zeroArity, Fin.val_zero] at hmatch
    · omega
    · omega
  · simp

theorem scalarAt_product (primary : FiniteDist Primary) (body : FiniteDist Body)
    (first second : canonicalKernels primary body 0 0) :
    scalarAt primary body (homogeneousProduct primary body first second) =
      scalarAt primary body first * scalarAt primary body second := by
  have hconst (kernel : canonicalKernels primary body 0 0) :
      kernel = (scalarAt primary body kernel) • scalarUnit primary body := by
    rw [← scalarKernel_scalarAt primary body kernel]
    apply Subtype.ext
    funext colors centers
    simp only [scalarKernel, scalarUnit, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_one]
    rfl
  rw [hconst first, CommonQueueAssembly.homogeneousProduct_smul_left]
  have hunit : homogeneousProduct primary body (scalarUnit primary body) second = second := by
    apply Subtype.ext
    have h := homogeneousProduct_unit_left primary body second
    have hequiv : finLeftUnit 0 = Equiv.refl (Fin 0) := Subsingleton.elim _ _
    rw [hequiv] at h
    exact h
  rw [hunit]
  simp only [scalarAt, scalarUnit, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_one]

def scalar (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (family : KernelFamily primary body order) : ℝ := scalarAt primary body (family (zeroArity order))

def scalarHom (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    KernelFamily primary body order →ₐ[ℝ] ℝ where
  toFun := scalar primary body order
  map_zero' := rfl
  map_one' := by
    change scalarAt primary body ((familyUnit primary body order) (zeroArity order)) = 1
    rw [familyUnit, Pi.single_eq_same]
    rfl
  map_add' first second := rfl
  map_mul' first second := by
    change scalarAt primary body ((first * second) (zeroArity order)) = _
    rw [product_zero_fiber, scalarAt_product]
    rfl
  commutes' value := by
    rw [Algebra.algebraMap_eq_smul_one]
    change value * scalar primary body order 1 = value
    have hone : scalar primary body order (1 : KernelFamily primary body order) = 1 := by
      change scalarAt primary body ((familyUnit primary body order) (zeroArity order)) = 1
      rw [familyUnit, Pi.single_eq_same]
      rfl
    rw [hone, mul_one]





end

end CurrentAFT.Augmentation

end

end


