-- Prove2me | Definitions.Def_InfoLossLAR_NativeBundle_08
-- name    : InfoLossLAR_NativeBundle_08
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T16:31:20.85709+00:00
-- url     : https://prove2.me/theorems/b2e534dd-a5c3-4c0c-a4be-a448a873bf17
-- title:
--   Calibrated weights, physical polynomial, and affine geometry data
-- statement:
--   This package defines the complete root-family and raising-pattern data, the chosen stable calibration solution, its physical public weight, clipping and Fourier error objects, and the affine geometry used to realize the public output.
--
--   For fixed parameters, order, admissible threshold evidence, and layout, the chosen calibration coefficient $c$ is specified through the concrete finite response operator $\mathcal R$ by
--   $$\mathcal R(c)=1.$$
--   The resulting public weight depends on the public control pools and layout. It does not take a protected hidden source value as an argument.
--
--   The package contains the supporting proofs needed to select this finite calibration data. Separate theorems establish its physical interpretation, positivity after the prescribed processing, asymptotic errors, and final transport accuracy.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0, native lean source modules: lean/CurrentAFT/RootOrdinaryGroupedChannel.lean, lean/CurrentAFT/RootSelectedZeroTag.lean, lean/CurrentAFT/RootTaggedSelectedCancellation.lean, lean/CurrentAFT/RootPrimaryGroupedChannel.lean, lean/CurrentAFT/RootTaggedLocal.lean, lean/CurrentAFT/RootTaggedFamilies.lean, lean/CurrentAFT/RootTaggedLegFirst.lean, lean/CurrentAFT/RootTaggedLegHigher.lean, lean/CurrentAFT/RootLegCoefficientFamily.lean, lean/CurrentAFT/RootLegCoefficientNorm.lean, lean/CurrentAFT/RootLegCoefficientLinear.lean, lean/CurrentAFT/RootLegCoefficientEvaluation.lean, lean/CurrentAFT/RootLegCoefficientBounds.lean, lean/CurrentAFT/RootMeanPrimary.lean, lean/CurrentAFT/PrimaryOnlyFamily.lean, lean/CurrentAFT/RootLegNormalized.lean, lean/CurrentAFT/RootLegReciprocal.lean, lean/CurrentAFT/RootUnselectedChannels.lean, lean/CurrentAFT/RootLegFirstCoefficient.lean, lean/CurrentAFT/RootUnselectedBlockChannel.lean, lean/CurrentAFT/RootUnselectedGrouped.lean, lean/CurrentAFT/ActualRootGroupedChannel.lean, lean/CurrentAFT/GroupedFamilyTensor.lean, lean/CurrentAFT/GroupedKernelLinear.lean, lean/CurrentAFT/GroupedFamilyIdentity.lean, lean/CurrentAFT/GroupedFamilyComposition.lean, lean/CurrentAFT/ActualRootResponse.lean, lean/CurrentAFT/ActualRootDefect.lean, lean/CurrentAFT/WeightedSubsetSum.lean, lean/CurrentAFT/RootActivityBudget.lean, lean/CurrentAFT/RootGroupCostBudget.lean, lean/CurrentAFT/RootSubsetNormSum.lean, lean/CurrentAFT/ActualRootDefectNorm.lean, lean/CurrentAFT/ActualRootFamily.lean, lean/CurrentAFT/CompleteRaisingPatternIdentity.lean, lean/CurrentAFT/RaisingPatternNorm.lean, lean/CurrentAFT/CompleteRaisingStability.lean, lean/CurrentAFT/ActualCompleteStability.lean, lean/CurrentAFT/ActualCalibrationSolution.lean, lean/CurrentAFT/PhysicalMoments.lean, lean/CurrentAFT/ActualCalibrationMoments.lean, lean/CurrentAFT/FixedOrderAccuracy.lean, lean/CurrentAFT/ActualCalibrationClipping.lean, lean/CurrentAFT/ActualLayouts.lean, lean/CurrentAFT/CenteredPolynomialDegree.lean, lean/CurrentAFT/PublicLowDegree.lean, lean/CurrentAFT/ActualCalibrationFourier.lean, lean/CurrentAFT/ActualCalibrationRates.lean, lean/CurrentAFT/PublicEndpointFourier.lean, lean/CurrentAFT/ActualPublicLegDisintegration.lean, lean/CurrentAFT/RefinedPublicTripleAverage.lean, lean/CurrentAFT/RefinedPublicDisintegration.lean, lean/CurrentAFT/ActualPublicExperiment.lean, lean/CurrentAFT/FiniteZeroSum.lean, lean/CurrentAFT/ActualCalibratedPublic.lean, lean/CurrentAFT/PhysicalPolynomialAverages.lean, lean/CurrentAFT/FinitePolynomialTensor.lean, lean/CurrentAFT/RootSelectedControlCenter.lean, lean/CurrentAFT/RootLocalDenominators.lean, lean/CurrentAFT/RootSelectedPhysicalColumns.lean, lean/CurrentAFT/RootSelectedPhysicalLinear.lean, lean/CurrentAFT/TypedTaggedPhysical.lean, lean/CurrentAFT/TypedRolePolynomial.lean, lean/CurrentAFT/RootUnselectedPhysicalLinear.lean, lean/CurrentAFT/ActualRootPhysicalResponse.lean, lean/CurrentAFT/RootBlockReindex.lean, lean/CurrentAFT/RootBackgroundDenominatorProduct.lean, lean/CurrentAFT/RootInactivePlacement.lean, lean/CurrentAFT/RootPolynomialTensor.lean, lean/CurrentAFT/RootPhysicalAverages.lean, lean/CurrentAFT/RootPolynomialPlacement.lean, lean/CurrentAFT/RootTaggedPhysicalFactorization.lean, lean/CurrentAFT/RootConditionalComponent.lean, lean/CurrentAFT/ActualRootDefectPhysical.lean, lean/CurrentAFT/RootConditionalResidues.lean, lean/CurrentAFT/RootActualOutputPolynomial.lean, lean/CurrentAFT/PointPolynomial.lean, lean/CurrentAFT/CompleteRaisingEvaluation.lean, lean/CurrentAFT/RootIndependentSelectedPhysical.lean, lean/CurrentAFT/ActualCompletePhysical.lean, lean/CurrentAFT/ActualFamilyPolynomial.lean, lean/CurrentAFT/RootScalarOutputPolynomial.lean, lean/CurrentAFT/ActualCompletePGF.lean, lean/CurrentAFT/ActualCalibrationExact.lean, lean/CurrentAFT/AffineActivationFubini.lean, lean/CurrentAFT/LobsterIncidence.lean, lean/CurrentAFT/LobsterCoordinates.lean, lean/CurrentAFT/LobsterMixerMatrix.lean, lean/CurrentAFT/AffineBaseline.lean, lean/CurrentAFT/AffineRealization.lean, lean/CurrentAFT/PublicEndpointPlacement.lean, lean/CurrentAFT/CurrentAffineGeometry.lean, lean/CurrentAFT/CurrentAffineLegCarry.lean, lean/CurrentAFT/CurrentAffineData.lean, lean/CurrentAFT/CurrentAffineLoad.lean, lean/CurrentAFT/GaussianWindowProtection.lean, lean/CurrentAFT/GaussianProductProtection.lean, lean/CurrentAFT/CurrentSourceProtection.lean, lean/CurrentAFT/CurrentSourceTail.lean, lean/CurrentAFT/CurrentSourceLayout.lean, lean/CurrentAFT/LobsterAffineLoad.lean, lean/CurrentAFT/CurrentAffineEndpoint.lean, lean/CurrentAFT/CurrentPublicSupport.lean, lean/CurrentAFT/CurrentAffineProtectedCarry.lean, lean/CurrentAFT/CurrentAffinePhysicalEndpoint.lean. Migrated source units selected by the Lean declaration and syntax oracles; exact source body hashes and original module paths recorded in Integration9_9/provenance/full_project_extraction/native_definition_bundles/manifest.json. Bundle SHA256 f992e35959b518fbeceae1f6cdfd8f77c9519b4c1be820ac42c36c93de210cc6. Header-only transitive import reduction verified by Lean module-data and parser oracles; imported module closure and all non-import source bytes are unchanged. Alternate sparse native dependencies preserve the original non-import body bytes and all public types; this header-only packaging is recorded in sparse_live/manifest.json. Current source SHA256 f992e35959b518fbeceae1f6cdfd8f77c9519b4c1be820ac42c36c93de210cc6. Header-only omission of an empty compatibility facade: directimport of the already published Native07Part3 replaces Native07. Lean syntax andkernel oracles confirm the omitted facade has0declarations/instances/attributes/options and0ownedkernelconstants; all non-import source bytes remain exact. Full9429native+2099runtime type comparison andstandard-three-axiom audits pass, withactualimportclosures explicitlyexcluding the empty facade. Current sourceSHA256 6df0ef4e50b318ecedc40c975c521f958f831bc2d4d0f30aa6d5d218b5cea430.

import Definitions.Def_InfoLossLAR_NativeBundle_07_Part_3















section















/-! # Typed one-root selected ordinary channels

The untagged root is averaged and the tagged root is centered before the
local channel is applied. This gives a degree bound for every input score,
including point masses used in joint tensor assembly.
-/
namespace CurrentAFT.RootOrdinaryGroupedChannel
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
  ControlCoordinates ControlProduct GradedControlAlgebra GradedControlNorm GradedControlStability
  GradedInverse LocalCoefficientFamily LocalRaisingLinear LocalRaisingBounds CoefficientHilbert
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance safeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference
abbrev Input (security : ℕ) := (Fin 1 → Root security) × SafePalette security

def reference (security : ℕ) : FiniteDist (Input security) :=
  RootCoordinateProjection.reference (rootReference security) (bodyReference security)

def toRaw (security : ℕ) : (Input security → ℝ) →ₗ[ℝ] (SelectedOrdinaryRoot.Input security → ℝ) where
  toFun score sample := score ((fun _ => sample.1), sample.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem oneRoot_expectation (security : ℕ) (value : (Fin 1 → Root security) → ℝ) :
    (FiniteDist.independent (fun _ : Fin 1 => rootReference security)).expectation value =
      (rootReference security).expectation (fun root => value (fun _ => root)) := by
  unfold FiniteDist.expectation
  change (∑ roots : Fin 1 → Root security, (∏ index, (rootReference security).weight (roots index)) * value roots) = _
  rw [← (Equiv.funUnique (Fin 1) (Root security)).symm.sum_comp]
  simp only [Equiv.funUnique_symm_apply, Fin.prod_univ_one]
  rfl

theorem toRaw_energy (security : ℕ) (score : Input security → ℝ) :
    (SelectedOrdinaryRoot.inputLaw security).l2Sq (toRaw security score) = (reference security).l2Sq score := by
  unfold reference RootCoordinateProjection.reference SelectedOrdinaryRoot.inputLaw FiniteDist.l2Sq
  rw [FiniteDist.expectation_prod, FiniteDist.expectation_prod, oneRoot_expectation]
  rfl

def projector (security : ℕ) (tagged : Bool) : (Input security → ℝ) →ₗ[ℝ] (Input security → ℝ) :=
  RootCoordinateProjection.coordinate (rootReference security) (0 : Fin 1) tagged



theorem average_toRaw (security : ℕ) (score : Input security → ℝ) :
    toRaw security (projector security false score) =
      SelectedOrdinaryMean.constantRoot security (SelectedOrdinaryMean.rootMean security (toRaw security score)) := by
  funext sample
  change (rootReference security).expectation (fun root =>
    score (Function.update (fun _ : Fin 1 => sample.1) 0 root, sample.2)) = _
  simp only [Function.update_eq_const_of_subsingleton]
  rfl

theorem center_toRaw (security : ℕ) (score : Input security → ℝ) :
    toRaw security (projector security true score) = SelectedOrdinaryMean.rootCenter security (toRaw security score) := by
  change toRaw security (score - RootCoordinateProjection.average (rootReference security) (0 : Fin 1) score) = _
  rw [map_sub]
  rw [show toRaw security (RootCoordinateProjection.average (rootReference security) (0 : Fin 1) score) =
    SelectedOrdinaryMean.constantRoot security (SelectedOrdinaryMean.rootMean security (toRaw security score)) from average_toRaw security score]
  rfl

def channel (security order : ℕ) (horder : 1 ≤ order) (tagged : Bool) :
    (Input security → ℝ) →ₗ[ℝ] Family security order :=
  (SelectedOrdinaryHybrid.channel security order horder).comp ((toRaw security).comp (projector security tagged))

theorem channel_false (security order : ℕ) (horder : 1 ≤ order) (score : Input security → ℝ) :
    channel security order horder false score =
      SelectedOrdinaryHybrid.independentChannel security order horder
        (SelectedOrdinaryMean.rootMean security (toRaw security score)) := by
  change SelectedOrdinaryHybrid.channel security order horder (toRaw security (projector security false score)) = _
  rw [average_toRaw, SelectedOrdinaryHybrid.channel_constant]

theorem channel_true (security order : ℕ) (horder : 1 ≤ order) (score : Input security → ℝ) :
    channel security order horder true score =
      SelectedOrdinaryRoot.channel security order horder
        (SelectedOrdinaryMean.rootCenter security (toRaw security score)) := by
  change SelectedOrdinaryHybrid.channel security order horder (toRaw security (projector security true score)) = _
  rw [center_toRaw]
  exact SelectedOrdinaryHybrid.channel_on_centered security order horder _ (SelectedOrdinaryMean.rootCenter_centered security _)

def cost (security : ℕ) (tagged : Bool) : ℝ :=
  if tagged then 48 / (Parameters.base security : ℝ)^63 else 2 * BackgroundRates.bodyFactor security

theorem channel_norm (security order : ℕ) (horder : 1 ≤ order) (tagged : Bool) (score : Input security → ℝ) :
    coefficientNorm security order (channel security order horder tagged score) ≤
      cost security tagged * Real.sqrt ((reference security).l2Sq score) := by
  cases tagged
  · rw [channel_false]
    apply (SelectedOrdinaryHybrid.independentChannel_norm security order horder _).trans
    have h := SelectedOrdinaryMean.rootMean_energy_le security (toRaw security score)
    rw [toRaw_energy] at h
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h)
      (mul_nonneg (by norm_num) (RaisingPatternBudget.bodyFactor_pos security).le)
  · rw [channel_true]
    apply (SelectedOrdinaryRootProperties.channel_norm security order horder _).trans
    have h := SelectedOrdinaryMean.rootCenter_energy_le security (toRaw security score)
    rw [toRaw_energy] at h
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) (by positivity)

theorem channel_vanishesBelow_one (security order : ℕ) (horder : 1 ≤ order) (tagged : Bool) (score : Input security → ℝ) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 1 (channel security order horder tagged score) :=
  SelectedOrdinaryHybrid.channel_vanishesBelow_one security order horder _







end
end CurrentAFT.RootOrdinaryGroupedChannel

end

section

















/-! # The zero-tag selected primary channel is its independent-root response

Both actual modular roots are averaged before applying the same finite
normalization. This is an equality of coefficient families, not merely an
equality after polynomial evaluation.
-/
namespace CurrentAFT.RootSelectedZeroTag
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion FirstHistogram
  LocalReferenceEnergy PairedReferenceEnergy FixedPairedFirst IndependentPairedReference
  RootTaggedSelected RootTaggedSelectedChannel RootReferenceExpectation
  ControlCoordinates ControlProduct GradedControlAlgebra GradedControlNorm GradedControlStability
  LocalCoefficientFamily LocalRaisingLinear LocalRaisingFirst LocalRaisingBounds CoefficientHilbert
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference
abbrev Palette (security : ℕ) := ActualControls.Palette security

theorem pairedMassAt_periodic (security : ℕ) (firstComp secondComp firstAttach secondAttach : ℤ)
    (hcomp : (firstComp : Root security) = (secondComp : Root security))
    (hattach : (firstAttach : Root security) = (secondAttach : Root security))
    (scalar : FirstHistogram.Scalar security) (score : Palette security → ℝ) :
    pairedMassAt security firstComp firstAttach scalar score =
      pairedMassAt security secondComp secondAttach scalar score := by
  have hc := RootBackgroundPolynomial.shiftEquiv_eq_of_cast security firstComp secondComp hcomp
  have ha : attachmentAt security firstAttach scalar = attachmentAt security secondAttach scalar := by
    unfold attachmentAt
    rw [RootBackgroundPolynomial.shiftEquiv_eq_of_cast security (firstAttach + scalar.val) (secondAttach + scalar.val)
      (by simp only [Int.cast_add, hattach])]
  funext word
  simp only [pairedMassAt_control_sum, hc, ha]

theorem mass_zeroTag (security : ℕ) (score : Palette security → ℝ) :
    mass security (liftZero security score) = independentSignedMass security score := by
  funext word
  rw [IndependentReferenceEnergy.independentSigned_mixture]
  rw [mass_eq_joint]
  change (sourceLaw security).expectation (fun sample => pairedMassAt security
    (sample.1.1.val : ℤ) (sample.1.2.val : ℤ) sample.2 score word) = _
  unfold sourceLaw rootsLaw IndependentReferenceEnergy.rootLaw
  rw [FiniteDist.expectation_prod, FiniteDist.expectation_comm]
  rw [FiniteDist.expectation_prod]
  apply congrArg (scalarLaw security).expectation
  funext scalar
  rw [FiniteDist.expectation_prod]
  calc
    _ = (actualSeedLaw security).expectation (fun comp =>
        (rootReference security).expectation (fun attach => pairedMassAt security
          (actualBlur security comp) (attach.val : ℤ) scalar score word)) := by
      apply rootReference_seed_expectation security (fun comp : ℤ =>
        (rootReference security).expectation (fun attach => pairedMassAt security comp (attach.val : ℤ) scalar score word))
      intro first second hequal
      apply congrArg (rootReference security).expectation
      funext attach
      exact congrFun (pairedMassAt_periodic security first second (attach.val : ℤ) (attach.val : ℤ)
        hequal rfl scalar score) word
    _ = _ := by
      rw [FiniteDist.expectation_prod]
      apply congrArg (actualSeedLaw security).expectation
      funext comp
      apply rootReference_seed_expectation security (fun attach : ℤ => pairedMassAt security (actualBlur security comp) attach scalar score word)
      intro first second hequal
      exact congrFun (pairedMassAt_periodic security (actualBlur security comp) (actualBlur security comp)
        first second rfl hequal scalar score) word

theorem normalizedResponse_zeroTag (security order : ℕ) (score : Palette security → ℝ) :
    normalizedResponse security order (liftZero security score) =
      NormalizedLocalPolynomial.independentNormalized security order score := by
  unfold normalizedResponse NormalizedLocalPolynomial.independentNormalized
  rw [mass_zeroTag]

theorem zeroChannel_eq (security order : ℕ) (score : Palette security → ℝ) :
    zeroChannel security order score = NormalizedLocalPolynomial.independentNormalized security order
      (centerLinear (primaryLaw security) score) := by
  change normalizedResponse security order
    (RootTaggedSelectedChannel.controlCenterLinear security
      (RootTaggedSelectedChannel.curryLinear security (zeroLiftLinear security score))) = _
  exact normalizedResponse_zeroTag security order (centerLinear (primaryLaw security) score)

theorem zeroChannel_eq_leading_add_raised (security order : ℕ) (horder : 1 ≤ order)
    (score : Palette security → ℝ) :
    zeroChannel security order score = RaisingChannels.primaryLeading security order horder score +
      RaisingChannels.primaryRaised security order horder score := by
  rw [zeroChannel_eq]
  change _ = _ + (NormalizedLocalPolynomial.independentNormalized security order
    (centerLinear (primaryLaw security) score) - _)
  unfold RaisingChannels.primaryLeading
  simp only [LinearMap.comp_apply]
  abel

 theorem primaryFactor_nonneg (security : ℕ) : 0 ≤ BackgroundRates.primaryFactor security :=
  (RaisingPatternBudget.primaryFactor_pos security).le

 theorem bodyFactor_nonneg (security : ℕ) : 0 ≤ BackgroundRates.bodyFactor security :=
  (RaisingPatternBudget.bodyFactor_pos security).le

theorem zeroChannel_norm_sharp (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ))
    (hsmall : raisingConstant ≤ (Parameters.base security : ℝ)^38)
    (score : Palette security → ℝ) :
    coefficientNorm security order (zeroChannel security order score) ≤
      (2 * BackgroundRates.primaryFactor security) * Real.sqrt ((primaryLaw security).l2Sq score) := by
  rw [zeroChannel_eq_leading_add_raised security order horder]
  apply (familyNorm_add_le _ _ order _ _ (primaryFactor_nonneg security) (bodyFactor_nonneg security) _ _).trans
  have hcost : raisingConstant / (Parameters.base security : ℝ)^102 ≤ BackgroundRates.primaryFactor security := by
    rw [BackgroundRates.primaryFactor_eq]
    apply (div_le_iff₀ (pow_pos (FirstResponse.base_pos security) _)).mpr
    convert hsmall using 1 <;> first | rfl | field_simp [(FirstResponse.base_pos security).ne']
  calc
    _ ≤ BackgroundRates.primaryFactor security * Real.sqrt ((primaryLaw security).l2Sq score) +
        (raisingConstant / (Parameters.base security : ℝ)^102) * Real.sqrt ((primaryLaw security).l2Sq score) :=
      add_le_add (RaisingChannels.primaryLeading_norm security order horder score)
        (RaisingChannels.primaryRaised_norm security order horder hlarge score)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hcost (Real.sqrt_nonneg ((primaryLaw security).l2Sq score))]

end
end CurrentAFT.RootSelectedZeroTag

end

section













/-! # A tagged attachment forces a second selected-group output -/
namespace CurrentAFT.RootTaggedSelectedCancellation

open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
  ControlCoordinates ControlProduct GradedControlAlgebra GradedInverse
  LocalCoefficientFamily LocalRaisingFirst NormalizedLocalPolynomial LocalReferenceEnergy
  PairedReferenceEnergy FixedPairedFirst CompleteFirstCoefficient RootTaggedSelected
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference
abbrev Palette (security : ℕ) := ActualControls.Palette security

theorem fixed_first_attachment_irrelevant (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (scalar : FirstHistogram.Scalar security) (score : Palette security → ℝ)
    (hcentered : (primaryLaw security).expectation score = 0) :
    LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
      (pairedMassAt security compensatorRoot attachmentRoot scalar score) 1 =
    LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
      (pairedMassAt security compensatorRoot 0 scalar score) 1 := by
  have hmass (root : ℤ) : (∑ word, pairedMassAt security compensatorRoot root scalar score word) = 0 := by
    rw [fixedMass_sum, hcentered, mul_zero]
  funext word
  have hword : word = (fun _ => word 0) := by
    funext index
    have hi := Fin.eq_zero index
    subst index
    rfl
  rw [hword, LocalTensors.degreeTensor_one_zero_mass (uniformReference security)
      (fun color => by rw [uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security))
      _ (hmass attachmentRoot),
    LocalTensors.degreeTensor_one_zero_mass (uniformReference security)
      (fun color => by rw [uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security))
      _ (hmass 0)]
  rw [fixedMass_first_formula security compensatorRoot attachmentRoot scalar score hcentered,
    fixedMass_first_formula security compensatorRoot 0 scalar score hcentered]

theorem mass_first_tensor_zero_of_attachment_centered (security : ℕ)
    (score : RootPair security → Palette security → ℝ)
    (hcontrol : ∀ roots, (primaryLaw security).expectation (score roots) = 0)
    (hattachment : ∀ comp primary, (rootReference security).expectation
      (fun attach => score (comp, attach) primary) = 0) :
    LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security) (mass security score) 1 = 0 := by
  have hmass : mass security score = ∑ sample : Sample security, (sourceLaw security).weight sample •
      pairedMassAt security (sample.1.1.val : ℤ) (sample.1.2.val : ℤ) sample.2 (score sample.1) := by
    rw [mass_eq_joint]
    funext word
    simp only [jointPairedMass, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← LocalTensors.degreeTensorLinear_apply, hmass, map_sum]
  simp only [map_smul, LocalTensors.degreeTensorLinear_apply]
  simp_rw [fixed_first_attachment_irrelevant security _ _ _ _ (hcontrol _)]
  simp only [sourceLaw, rootsLaw, FiniteDist.prod_weight, Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro comp _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro scalar _
  let channel := localDegreeLinear security (comp.val : ℤ) 0 scalar 1
  have hscore : (∑ attach : Root security, (rootReference security).weight attach • score (comp, attach)) = 0 := by
    funext primary
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, FiniteDist.expectation] using hattachment comp primary
  have hsum : (∑ attach : Root security, (rootReference security).weight attach • channel (score (comp, attach))) = 0 := by
    have h := congrArg channel hscore
    simpa only [map_sum, map_smul, map_zero] using h
  have hchannel (input : Palette security → ℝ) : LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security)
      (pairedMassAt security (comp.val : ℤ) 0 scalar input) 1 = channel input := by
    simp only [channel, localDegreeLinear, LinearMap.comp_apply, LocalTensors.degreeTensorLinear_apply,
      pairedMassLinear_apply]
  simp_rw [hchannel]
  calc
    _ = ((rootReference security).weight comp * (scalarLaw security).weight scalar) •
        ∑ attach : Root security, (rootReference security).weight attach • channel (score (comp, attach)) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro attach _
      rw [smul_smul]
      congr 1
      ring
    _ = 0 := by rw [hsum, smul_zero]

theorem mass_count_zero_of_attachment_centered (security : ℕ)
    (score : RootPair security → Palette security → ℝ)
    (hcontrol : ∀ roots, (primaryLaw security).expectation (score roots) = 0)
    (hattachment : ∀ comp primary, (rootReference security).expectation
      (fun attach => score (comp, attach) primary) = 0) :
    LocalTensors.signedColorCount (mass security score) = 0 := by
  funext color
  have h := congrFun (mass_first_tensor_zero_of_attachment_centered security score hcontrol hattachment) (fun _ => color)
  rw [LocalTensors.degreeTensor_one_zero_mass (uniformReference security)
    (fun output => by rw [uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security))
    _ (mass_zero security score hcontrol)] at h
  change LocalTensors.signedColorCount (mass security score) color / Real.sqrt ((uniformReference security).weight color) = 0 at h
  have hsqrt : Real.sqrt ((uniformReference security).weight color) ≠ 0 := by
    apply (Real.sqrt_pos.mpr _).ne'
    rw [uniformReference_weight]
    exact one_div_pos.mpr (FirstResponse.modulus_pos security)
  field_simp [hsqrt] at h
  simpa only [Pi.zero_apply, mul_zero] using h

theorem firstFamily_zero_of_attachment_centered (security order : ℕ) (horder : 1 ≤ order)
    (score : RootPair security → Palette security → ℝ)
    (hcontrol : ∀ roots, (primaryLaw security).expectation (score roots) = 0)
    (hattachment : ∀ comp primary, (rootReference security).expectation
      (fun attach => score (comp, attach) primary) = 0) :
    CompleteFirstCoefficient.firstFamily security order horder (mass security score) = 0 := by
  have hcount := mass_count_zero_of_attachment_centered security score hcontrol hattachment
  have hscore : CompleteFirstCoefficient.firstScore security order horder (mass security score) = 0 := by
    rw [CompleteFirstCoefficient.firstScore, completeFamily_primary_centered security order horder _
      (mass_zero security score hcontrol), hcount]
    simp only [Pi.zero_apply, zero_div]
    change PrimaryTensorInverse.densityInverse security (0 : Palette security → ℝ) = 0
    exact map_zero _
  unfold CompleteFirstCoefficient.firstFamily BackgroundFamilies.primaryFamily
  have hkernel : BackgroundFamilies.primaryKernel (primaryLaw security) (bodyReference security)
      (CompleteFirstCoefficient.firstScore security order horder (mass security score))
      (firstScore_centered security order horder (mass security score)) = 0 := by
    apply Subtype.ext
    funext colors centers
    change CompleteFirstCoefficient.firstScore security order horder (mass security score) (colors 0) = 0
    rw [hscore]
    rfl
  rw [hkernel, Pi.single_zero]

/-- In particular a group with both of its roots tagged has no scalar or
first-degree response. It still consumes its one original control score. -/
theorem normalizedResponse_vanishesBelow_two (security order : ℕ) (horder : 1 ≤ order)
    (score : RootPair security → Palette security → ℝ)
    (hcontrol : ∀ roots, (primaryLaw security).expectation (score roots) = 0)
    (hattachment : ∀ comp primary, (rootReference security).expectation
      (fun attach => score (comp, attach) primary) = 0) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 2 (normalizedResponse security order score) := by
  unfold normalizedResponse NormalizedLocalPolynomial.normalizedFamily
  rw [complete_eq_first_add_higher security order horder _ (mass_zero security score hcontrol),
    firstFamily_zero_of_attachment_centered security order horder score hcontrol hattachment, zero_add]
  exact vanishesBelow_mul _ _ order 2 0 _ _ (higherFamily_vanishesBelow security order _) (vanishesBelow_zero _ _ order _)

end
end CurrentAFT.RootTaggedSelectedCancellation

end

section

















/-! # The actual selected primary channel on two typed root coordinates

Coordinate zero is the compensator root and coordinate one is the attachment
root. Both roots act on one joint primary-control score. A false mask entry
averages its root; a true entry centers it.
-/
namespace CurrentAFT.RootPrimaryGroupedChannel
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
  ControlCoordinates ControlProduct GradedControlAlgebra GradedControlNorm
  LocalCoefficientFamily LocalReferenceEnergy NormalizedLocalPolynomial
  LocalRaisingBounds RootTaggedSelected RootTaggedSelectedNorm
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference

abbrev Palette (security : ℕ) := ActualControls.Palette security
abbrev Input (security : ℕ) := (Fin 2 → Root security) × Palette security

def inputLaw (security : ℕ) : FiniteDist (Input security) :=
  RootCoordinateProjection.reference (rootReference security) (primaryLaw security)

/-- The numbering is fixed: compensator first, attachment second. -/
def pairEquiv (security : ℕ) : (Fin 2 → Root security) ≃ RootPair security :=
  finTwoArrowEquiv (Root security)

def pairLinear (security : ℕ) : (Input security → ℝ) →ₗ[ℝ]
    (RootTaggedSelectedChannel.Input security → ℝ) where
  toFun score sample := score ((pairEquiv security).symm sample.1, sample.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem expectation_finTwo {Color : Type*} [Fintype Color]
    (law : FiniteDist Color) (value : (Fin 2 → Color) → ℝ) :
    (FiniteDist.independent (fun _ : Fin 2 => law)).expectation value =
      (law.prod law).expectation (fun pair => value ((finTwoArrowEquiv Color).symm pair)) := by
  unfold FiniteDist.expectation
  conv_rhs => rw [← (finTwoArrowEquiv Color).sum_comp]
  apply Finset.sum_congr rfl
  intro word _
  change (∏ index : Fin 2, law.weight (word index)) * value word =
    law.weight (word 0) * law.weight (word 1) *
      value ((finTwoArrowEquiv Color).symm ((finTwoArrowEquiv Color) word))
  rw [Fin.prod_univ_two, Equiv.symm_apply_apply]

theorem pairLinear_energy (security : ℕ) (score : Input security → ℝ) :
    (RootTaggedSelectedChannel.inputLaw security).l2Sq (pairLinear security score) =
      (inputLaw security).l2Sq score := by
  unfold RootTaggedSelectedChannel.inputLaw inputLaw RootCoordinateProjection.reference FiniteDist.l2Sq
  rw [FiniteDist.expectation_prod, FiniteDist.expectation_prod]
  exact (expectation_finTwo (rootReference security)
    (fun roots => (primaryLaw security).expectation (fun primary => score (roots, primary) ^ 2))).symm

def mask (tagged : Fin 2 → Bool) : List (Fin 2 × Bool) :=
  (Finset.univ : Finset (Fin 2)).toList.map (fun index => (index, tagged index))

def projector (security : ℕ) (tagged : Fin 2 → Bool) :
    (Input security → ℝ) →ₗ[ℝ] (Input security → ℝ) :=
  RootCoordinateProjection.sequence (rootReference security) (mask tagged)

 theorem sequence_perm {Color Control : Type*} [Fintype Color] [Fintype Control]
    (law : FiniteDist Color) (tagged : Fin 2 → Bool) {first second : List (Fin 2)}
    (hperm : first.Perm second)
    (score : ((Fin 2 → Color) × Control) → ℝ) :
    RootCoordinateProjection.sequence law (first.map (fun index => (index, tagged index))) score =
      RootCoordinateProjection.sequence law (second.map (fun index => (index, tagged index))) score := by
  induction hperm with
  | nil => rfl
  | cons index hperm ih =>
      simp only [List.map_cons, RootCoordinateProjection.sequence, LinearMap.comp_apply, ih]
  | swap first second rest =>
      simp only [List.map_cons, RootCoordinateProjection.sequence, LinearMap.comp_apply]
      by_cases hequal : first = second
      · subst second; rfl
      · exact RootCoordinateProjection.coordinate_commute law second first (Ne.symm hequal)
          (tagged second) (tagged first) _
  | trans first second ihfirst ihsecond => exact ihfirst.trans ihsecond

theorem projector_eq_two (security : ℕ) (tagged : Fin 2 → Bool) (score : Input security → ℝ) :
    projector security tagged score =
      RootCoordinateProjection.coordinate (rootReference security) 0 (tagged 0)
        (RootCoordinateProjection.coordinate (rootReference security) 1 (tagged 1) score) := by
  have huniv : ([0, 1] : List (Fin 2)).toFinset = Finset.univ := by
    ext index
    fin_cases index <;> simp
  have hperm : (Finset.univ : Finset (Fin 2)).toList.Perm [0, 1] := by
    rw [← huniv]
    exact List.toFinset_toList (by simp)
  exact sequence_perm (rootReference security) tagged hperm score

theorem projector_energy_le (security : ℕ) (tagged : Fin 2 → Bool) (score : Input security → ℝ) :
    (inputLaw security).l2Sq (projector security tagged score) ≤ (inputLaw security).l2Sq score :=
  RootCoordinateProjection.sequence_energy_le (rootReference security) (primaryLaw security) (mask tagged) score

def projectedScore (security : ℕ) (tagged : Fin 2 → Bool) (score : Input security → ℝ) :
    RootPair security → Palette security → ℝ :=
  RootTaggedSelectedChannel.curryLinear security (pairLinear security (projector security tagged score))

def centeredScore (security : ℕ) (tagged : Fin 2 → Bool) (score : Input security → ℝ) :
    RootPair security → Palette security → ℝ :=
  RootTaggedSelectedChannel.controlCenterLinear security (projectedScore security tagged score)

/-- This is the actual selected paired channel after the explicit two-root mask. -/
def channel (security order : ℕ) (tagged : Fin 2 → Bool) :
    (Input security → ℝ) →ₗ[ℝ] Family security order :=
  (RootTaggedSelectedChannel.channel security order).comp
    ((pairLinear security).comp (projector security tagged))

/-- Equality of coefficient data, before any polynomial evaluation. -/
theorem channel_eq_normalizedResponse (security order : ℕ) (tagged : Fin 2 → Bool)
    (score : Input security → ℝ) :
    channel security order tagged score =
      normalizedResponse security order (centeredScore security tagged score) := rfl

theorem centeredScore_control_mean (security : ℕ) (tagged : Fin 2 → Bool)
    (score : Input security → ℝ) (roots : RootPair security) :
    (primaryLaw security).expectation (centeredScore security tagged score roots) = 0 :=
  CoefficientHilbert.center_mean _ _

theorem channel_norm (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ))
    (tagged : Fin 2 → Bool) (score : Input security → ℝ) :
    coefficientNorm security order (channel security order tagged score) ≤
      (selectedConstant / (Parameters.base security : ℝ)^47) *
        Real.sqrt ((inputLaw security).l2Sq score) := by
  have h := RootTaggedSelectedChannel.channel_norm security order horder hlarge
    (pairLinear security (projector security tagged score))
  rw [pairLinear_energy] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (projector_energy_le security tagged score))
    (div_nonneg selectedConstant_nonneg (pow_nonneg (FirstResponse.base_pos security).le _)))

theorem channel_vanishesBelow_one (security order : ℕ) (tagged : Fin 2 → Bool)
    (score : Input security → ℝ) :
    GradedInverse.VanishesBelow (primaryLaw security) (bodyReference security) order 1
      (channel security order tagged score) :=
  RootTaggedSelectedChannel.channel_vanishesBelow_one security order _





theorem projector_attachment_average_zero (security : ℕ) (tagged : Fin 2 → Bool)
    (htag : tagged 1 = true) (score : Input security → ℝ) :
    RootCoordinateProjection.average (rootReference security) 1
      (projector security tagged score) = 0 := by
  rw [projector_eq_two, htag]
  change RootCoordinateProjection.coordinate (rootReference security) 1 false
    (RootCoordinateProjection.coordinate (rootReference security) 0 (tagged 0)
      (RootCoordinateProjection.center (rootReference security) 1 score)) = 0
  rw [RootCoordinateProjection.coordinate_commute (rootReference security) 1 0
    (by intro hequal; exact Nat.one_ne_zero (congrArg Fin.val hequal))]
  change RootCoordinateProjection.coordinate (rootReference security) 0 (tagged 0)
    (RootCoordinateProjection.average (rootReference security) 1
      (RootCoordinateProjection.center (rootReference security) 1 score)) = 0
  rw [RootCoordinateProjection.center_mean_zero, map_zero]

 theorem update_attachment {Color : Type*} (first second value : Color) :
    Function.update (![first, second] : Fin 2 → Color) 1 value = ![first, value] := by
  funext index
  fin_cases index <;> simp

theorem projectedScore_attachment_mean (security : ℕ) (tagged : Fin 2 → Bool)
    (htag : tagged 1 = true) (score : Input security → ℝ)
    (compensator : Root security) (primary : Palette security) :
    (rootReference security).expectation (fun attachment =>
      projectedScore security tagged score (compensator, attachment) primary) = 0 := by
  have h := congrFun (projector_attachment_average_zero security tagged htag score)
    (![compensator, compensator], primary)
  simpa only [RootCoordinateProjection.average_apply, update_attachment, Pi.zero_apply,
    projectedScore, RootTaggedSelectedChannel.curryLinear, pairLinear, pairEquiv,
    finTwoArrowEquiv, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, LinearMap.coe_mk, AddHom.coe_mk] using h

/-- Primary-control centering commutes with the actual attachment-root mean.
The two roots still share their original one primary score. -/
theorem centeredScore_attachment_mean (security : ℕ) (tagged : Fin 2 → Bool)
    (htag : tagged 1 = true) (score : Input security → ℝ)
    (compensator : Root security) (primary : Palette security) :
    (rootReference security).expectation (fun attachment =>
      centeredScore security tagged score (compensator, attachment) primary) = 0 := by
  change (rootReference security).expectation (fun attachment =>
    projectedScore security tagged score (compensator, attachment) primary -
      (primaryLaw security).expectation (projectedScore security tagged score (compensator, attachment))) = 0
  rw [FiniteDist.expectation_sub, projectedScore_attachment_mean security tagged htag score,
    FiniteDist.expectation_comm]
  simp only [projectedScore_attachment_mean security tagged htag score, FiniteDist.expectation_const, sub_self]

theorem channel_vanishesBelow_two (security order : ℕ) (horder : 1 ≤ order)
    (tagged : Fin 2 → Bool) (htag : tagged 1 = true) (score : Input security → ℝ) :
    GradedInverse.VanishesBelow (primaryLaw security) (bodyReference security) order 2
      (channel security order tagged score) := by
  rw [channel_eq_normalizedResponse]
  exact RootTaggedSelectedCancellation.normalizedResponse_vanishesBelow_two security order horder _
    (centeredScore_control_mean security tagged score)
    (centeredScore_attachment_mean security tagged htag score)

def rootMean (security : ℕ) : (Input security → ℝ) →ₗ[ℝ] (Palette security → ℝ) where
  toFun score primary := (FiniteDist.independent (fun _ : Fin 2 => rootReference security)).expectation
    (fun roots => score (roots, primary))
  map_add' first second := by funext primary; exact FiniteDist.expectation_add _ _ _
  map_smul' scalar score := by funext primary; exact FiniteDist.expectation_const_mul _ _ _

 theorem update_both {Color : Type*} (word : Fin 2 → Color) (first second : Color) :
    Function.update (Function.update word 0 first) 1 second = ![first, second] := by
  funext index
  fin_cases index <;> simp

theorem projector_zero (security : ℕ) (score : Input security → ℝ) :
    projector security (fun _ => false) score = fun sample => rootMean security score sample.2 := by
  funext sample
  rw [projector_eq_two]
  simp only [RootCoordinateProjection.coordinate, Bool.false_eq_true, if_false,
    RootCoordinateProjection.average_apply, update_both]
  change _ = (FiniteDist.independent (fun _ : Fin 2 => rootReference security)).expectation
    (fun roots => score (roots, sample.2))
  rw [expectation_finTwo, FiniteDist.expectation_prod]
  rfl

theorem rootMean_energy_le (security : ℕ) (score : Input security → ℝ) :
    (primaryLaw security).l2Sq (rootMean security score) ≤ (inputLaw security).l2Sq score := by
  unfold inputLaw RootCoordinateProjection.reference FiniteDist.l2Sq
  rw [FiniteDist.expectation_prod, FiniteDist.expectation_comm]
  apply Finset.sum_le_sum
  intro primary _
  exact mul_le_mul_of_nonneg_left
    (BlockFock.mean_square_le (FiniteDist.independent (fun _ : Fin 2 => rootReference security))
      (fun roots => score (roots, primary))) ((primaryLaw security).nonneg primary)

theorem channel_zero (security order : ℕ) (score : Input security → ℝ) :
    channel security order (fun _ => false) score =
      RootTaggedSelectedChannel.zeroChannel security order (rootMean security score) := by
  change RootTaggedSelectedChannel.channel security order
    (pairLinear security (projector security (fun _ => false) score)) =
      RootTaggedSelectedChannel.channel security order
        (RootTaggedSelectedChannel.zeroLiftLinear security (rootMean security score))
  congr 1
  rw [projector_zero]
  rfl

theorem channel_zero_norm_sharp (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ))
    (hsmall : raisingConstant ≤ (Parameters.base security : ℝ)^38)
    (score : Input security → ℝ) :
    coefficientNorm security order (channel security order (fun _ => false) score) ≤
      (2 * BackgroundRates.primaryFactor security) * Real.sqrt ((inputLaw security).l2Sq score) := by
  rw [channel_zero]
  exact (RootSelectedZeroTag.zeroChannel_norm_sharp security order horder hlarge hsmall _).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (rootMean_energy_le security score))
      (mul_nonneg (by norm_num) (RaisingPatternBudget.primaryFactor_pos security).le))







/-- The root-free selected channel retains its sharp independent-response
cost. Every tagged channel uses the full joint root/control estimate. -/
def cost (security : ℕ) (tagged : Fin 2 → Bool) : ℝ :=
  if tagged 0 || tagged 1 then selectedConstant / (Parameters.base security : ℝ)^47
  else 2 * BackgroundRates.primaryFactor security

theorem cost_nonneg (security : ℕ) (tagged : Fin 2 → Bool) : 0 ≤ cost security tagged := by
  unfold cost
  split
  · exact div_nonneg selectedConstant_nonneg (pow_nonneg (FirstResponse.base_pos security).le _)
  · exact mul_nonneg (by norm_num) (RaisingPatternBudget.primaryFactor_pos security).le

theorem channel_norm_cost (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ))
    (hsmall : raisingConstant ≤ (Parameters.base security : ℝ)^38)
    (tagged : Fin 2 → Bool) (score : Input security → ℝ) :
    coefficientNorm security order (channel security order tagged score) ≤
      cost security tagged * Real.sqrt ((inputLaw security).l2Sq score) := by
  by_cases hzero : tagged = fun _ => false
  · subst tagged
    simpa only [cost, Bool.or_self, Bool.false_eq_true, if_false] using
      channel_zero_norm_sharp security order horder hlarge hsmall score
  · have hsome : (tagged 0 || tagged 1) = true := by
      cases hfirst : tagged 0 <;> cases hsecond : tagged 1
      · exfalso
        apply hzero
        funext index
        fin_cases index <;> assumption
      · rfl
      · rfl
      · rfl
    simpa only [cost, hsome, if_true] using channel_norm security order horder hlarge tagged score

end
end CurrentAFT.RootPrimaryGroupedChannel

end

section















/-!
# Actual unselected singleton root-tag channels

The root coordinate is centered before the actual primary mass inverse is
applied. The source law may have zero atoms; no root atom is ever divided by.
-/

namespace CurrentAFT.RootTaggedLocal

open AFT DiffuseProfiles ProposalPrimary ActualControls LocalReferenceEnergy
  UniformBodyProfiles CycleRootExpansion RootBackgroundPolynomial PrimaryTensorInverse
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize ProposalPrimary.primaryLaw
  CycleRootExpansion.rootReference

def shiftedLaw (security : ℕ) (role : BodyRole) (queue : ℤ) (root : Root security) :
    FiniteDist (ActualControls.Palette security) :=
  (preRootLaw security role queue).map (shiftEquiv security root.val)

def meanLaw (security : ℕ) (role : BodyRole) (queue : ℤ) : FiniteDist (ActualControls.Palette security) :=
  (rootReference security).mix (shiftedLaw security role queue)

def deviationProfile (security : ℕ) (role : BodyRole) (queue : ℤ) (root : Root security) :
    ActualControls.Palette security → ℝ :=
  (shiftedLaw security role queue root).weight - (meanLaw security role queue).weight

theorem deviationProfile_mass (security : ℕ) (role : BodyRole) (queue : ℤ) (root : Root security) :
    (∑ color, deviationProfile security role queue root color) = 0 := by
  simp only [deviationProfile, Pi.sub_apply, Finset.sum_sub_distrib, FiniteDist.sum_one, sub_self]



theorem shiftedLaw_uniform_norm (security : ℕ) (role : BodyRole) (queue : ℤ) (root : Root security) :
    ‖uniformVector security (shiftedLaw security role queue root).weight‖ ≤ deviation security := by
  rw [shiftedLaw, uniformVector_map_equiv_norm]
  exact preRootLaw_norm_le security role queue

theorem meanLaw_uniform_norm (security : ℕ) (role : BodyRole) (queue : ℤ) :
    ‖uniformVector security (meanLaw security role queue).weight‖ ≤ deviation security :=
  uniformVector_mix_norm_le security _ _ _ (shiftedLaw_uniform_norm security role queue)

theorem deviationProfile_uniform_norm (security : ℕ) (role : BodyRole) (queue : ℤ) (root : Root security) :
    ‖ProfileHilbert.whiten (uniformReference security).weight (deviationProfile security role queue root)‖ ≤
      2 * deviation security := by
  have hsplit : ProfileHilbert.whiten (uniformReference security).weight (deviationProfile security role queue root) =
      uniformVector security (shiftedLaw security role queue root).weight - uniformVector security (meanLaw security role queue).weight := by
    unfold uniformVector
    rw [← map_sub]
    congr 1
    funext color
    simp only [deviationProfile, Pi.sub_apply]
    ring
  rw [hsplit]
  exact (norm_sub_le _ _).trans ((add_le_add (shiftedLaw_uniform_norm security role queue root)
    (meanLaw_uniform_norm security role queue)).trans_eq (by ring))

theorem uniform_to_primary_energy (security : ℕ) (profile : ActualControls.Palette security → ℝ) :
    profileSquareNorm (primaryLaw security).weight profile ≤
      2 * profileSquareNorm (uniformReference security).weight profile := by
  have hq := FirstResponse.modulus_pos security
  have hprimary (color : ActualControls.Palette security) :
      1 / (2 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight color := by
    simpa only [primaryLaw] using primaryProfile_atom_lower security color
  unfold profileSquareNorm
  calc
    _ ≤ ∑ color, profile color ^ 2 / (1 / (2 * (Parameters.modulus security : ℝ))) := by
      apply Finset.sum_le_sum
      intro color _
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (hprimary color)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro color _
      rw [uniformReference_weight]
      field_simp

theorem deviationProfile_primary_energy (security : ℕ) (role : BodyRole) (queue : ℤ) (root : Root security) :
    profileSquareNorm (primaryLaw security).weight (deviationProfile security role queue root) ≤
      8 * deviation security ^ 2 := by
  have hn := deviationProfile_uniform_norm security role queue root
  have hn2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [ProfileHilbert.whiten_norm_sq _ _ (uniformReference security).nonneg] at hn2
  exact (uniform_to_primary_energy security _).trans
    ((mul_le_mul_of_nonneg_left hn2 (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

def rootMass (security : ℕ) (role : BodyRole) (queue : ℤ) :
    (Root security → ℝ) →ₗ[ℝ] (ActualControls.Palette security → ℝ) where
  toFun input := fun color => ∑ root, (rootReference security).weight root * input root * deviationProfile security role queue root color
  map_add' first second := by
    funext color
    simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' scalar input := by
    funext color
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro root _
    ring

theorem rootMass_mass (security : ℕ) (role : BodyRole) (queue : ℤ) (input : Root security → ℝ) :
    (∑ color, rootMass security role queue input color) = 0 := by
  unfold rootMass
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, deviationProfile_mass, mul_zero, Finset.sum_const_zero]





theorem weighted_pair_cauchy {Index : Type*} [Fintype Index] (law : FiniteDist Index)
    (first second : Index → ℝ) :
    (∑ index, law.weight index * first index * second index) ^ 2 ≤
      (∑ index, law.weight index * first index ^ 2) * ∑ index, law.weight index * second index ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro index _
    exact mul_nonneg (law.nonneg index) (sq_nonneg _)
  · intro index _
    exact mul_nonneg (law.nonneg index) (sq_nonneg _)
  · intro index _
    ring

theorem rootMass_energy (security : ℕ) (role : BodyRole) (queue : ℤ) (input : Root security → ℝ) :
    profileSquareNorm (primaryLaw security).weight (rootMass security role queue input) ≤
      8 * deviation security ^ 2 * (rootReference security).l2Sq input := by
  have he (color : ActualControls.Palette security) := weighted_pair_cauchy (rootReference security) input
    (fun root => deviationProfile security role queue root color)
  unfold profileSquareNorm
  calc
    _ ≤ ∑ color, ((rootReference security).l2Sq input *
        ∑ root, (rootReference security).weight root * deviationProfile security role queue root color ^ 2) /
          (primaryLaw security).weight color := by
      apply Finset.sum_le_sum
      intro color _
      exact div_le_div_of_nonneg_right (he color) (primaryReference_positive security color).le
    _ = (rootReference security).l2Sq input * ∑ root, (rootReference security).weight root *
        profileSquareNorm (primaryLaw security).weight (deviationProfile security role queue root) := by
      simp only [profileSquareNorm, mul_div_assoc, Finset.sum_div, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ (rootReference security).l2Sq input * ∑ root, (rootReference security).weight root * (8 * deviation security ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ ((rootReference security).l2Sq_nonneg input)
      exact Finset.sum_le_sum fun root _ => mul_le_mul_of_nonneg_left
        (deviationProfile_primary_energy security role queue root) ((rootReference security).nonneg root)
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one]; ring



def profileDensity (security : ℕ) :
    (ActualControls.Palette security → ℝ) →ₗ[ℝ] (ActualControls.Palette security → ℝ) :=
  diagonal (fun color => ((primaryLaw security).weight color)⁻¹)

theorem profileDensity_apply (security : ℕ) (profile : ActualControls.Palette security → ℝ) (color : ActualControls.Palette security) :
    profileDensity security profile color = profile color / (primaryLaw security).weight color := by
  change ((primaryLaw security).weight color)⁻¹ * profile color = _
  ring

theorem profileDensity_mean (security : ℕ) (profile : ActualControls.Palette security → ℝ) :
    (primaryLaw security).expectation (profileDensity security profile) = ∑ color, profile color := by
  unfold FiniteDist.expectation
  apply Finset.sum_congr rfl
  intro color _
  rw [profileDensity_apply]
  field_simp [(primaryReference_positive security color).ne']

theorem profileDensity_energy (security : ℕ) (profile : ActualControls.Palette security → ℝ) :
    (primaryLaw security).l2Sq (profileDensity security profile) = profileSquareNorm (primaryLaw security).weight profile := by
  unfold FiniteDist.l2Sq FiniteDist.expectation profileSquareNorm
  apply Finset.sum_congr rfl
  intro color _
  change (primaryLaw security).weight color * (profileDensity security profile color) ^ 2 = _
  rw [profileDensity_apply]
  field_simp [(primaryReference_positive security color).ne']

/-- The actual calibrated first-response inverse, as one genuine local
linear map on the whole root Hilbert space. -/
def rootLift (security : ℕ) (role : BodyRole) (queue : ℤ) :
    (Root security → ℝ) →ₗ[ℝ] (ActualControls.Palette security → ℝ) :=
  (densityInverse security).comp ((profileDensity security).comp (rootMass security role queue))

theorem rootLift_apply (security : ℕ) (role : BodyRole) (queue : ℤ) (input : Root security → ℝ) :
    rootLift security role queue input = densityInverse security (profileDensity security (rootMass security role queue input)) := rfl

theorem rootLift_mean (security : ℕ) (role : BodyRole) (queue : ℤ) (input : Root security → ℝ) :
    (primaryLaw security).expectation (rootLift security role queue input) = 0 := by
  rw [rootLift_apply, densityInverse_mean, profileDensity_mean, rootMass_mass, mul_zero]





theorem rootLift_energy (security : ℕ) (role : BodyRole) (queue : ℤ) (input : Root security → ℝ) :
    (primaryLaw security).l2Sq (rootLift security role queue input) ≤
      32 * deviation security ^ 2 / activation security ^ 2 * (rootReference security).l2Sq input := by
  rw [rootLift_apply]
  calc
    _ ≤ (2 / activation security) ^ 2 * (primaryLaw security).l2Sq
        (profileDensity security (rootMass security role queue input)) := densityInverse_energy security _
    _ = (2 / activation security) ^ 2 * profileSquareNorm (primaryLaw security).weight (rootMass security role queue input) := by
      rw [profileDensity_energy]
    _ ≤ (2 / activation security) ^ 2 * (8 * deviation security ^ 2 * (rootReference security).l2Sq input) :=
      mul_le_mul_of_nonneg_left (rootMass_energy security role queue input) (sq_nonneg _)
    _ = _ := by ring

def rootCost (security : ℕ) : ℝ := 4 * Real.sqrt 2 * deviation security / activation security

theorem rootCost_nonneg (security : ℕ) : 0 ≤ rootCost security := by
  unfold rootCost
  have := deviation_nonneg security
  have := activation_pos security
  positivity

theorem rootCost_square (security : ℕ) :
    rootCost security ^ 2 = 32 * deviation security ^ 2 / activation security ^ 2 := by
  rw [rootCost, div_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem rootLift_energy_le_cost (security : ℕ) (role : BodyRole) (queue : ℤ) (input : Root security → ℝ) :
    (primaryLaw security).l2Sq (rootLift security role queue input) ≤
      rootCost security ^ 2 * (rootReference security).l2Sq input := by
  rw [rootCost_square]
  exact rootLift_energy security role queue input



theorem rootLift_norm (security : ℕ) (role : BodyRole) (queue : ℤ) (input : Root security → ℝ) :
    Real.sqrt ((primaryLaw security).l2Sq (rootLift security role queue input)) ≤
      rootCost security * Real.sqrt ((rootReference security).l2Sq input) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (rootCost_nonneg security) (Real.sqrt_nonneg _), ?_⟩
  rw [mul_pow, Real.sq_sqrt ((rootReference security).l2Sq_nonneg input)]
  exact rootLift_energy_le_cost security role queue input

theorem rootCost_decay (security : ℕ) : rootCost security ≤ 4128 / (Parameters.base security : ℝ) ^ 30 := by
  have hb := FirstResponse.base_pos security
  have hd := deviation_nonneg security
  have ha := activation_pos security
  have hinv : 1 / activation security ≤ 4 * (Parameters.base security : ℝ) := by
    have h := one_div_le_one_div_of_le (by positivity : 0 < 1 / (4 * (Parameters.base security : ℝ)))
      (FirstResponse.activation_lower_simple security)
    simpa only [one_div_one_div] using h
  have hsqrt : Real.sqrt 2 ≤ (2 : ℝ) := by
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  calc
    _ = 4 * Real.sqrt 2 * deviation security * (1 / activation security) := by unfold rootCost; ring
    _ ≤ 4 * 2 * deviation security * (4 * (Parameters.base security : ℝ)) := by gcongr
    _ = _ := by unfold deviation; field_simp; ring







end

end CurrentAFT.RootTaggedLocal

end

section













/-! The actual singleton root channel in the genuine canonical coefficient family. -/

namespace CurrentAFT.RootTaggedFamilies

open AFT ControlCoordinates GradedControlAlgebra GradedControlNorm DiffuseProfiles
  ProposalPrimary ActualControls UniformBodyProfiles CycleRootExpansion RootTaggedLocal
  BackgroundFamilies BackgroundRates BackgroundEvaluation BackgroundFirstEvaluation
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize ProposalPrimary.primaryLaw
  ActualControls.bodyReference CycleRootExpansion.rootReference

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def rootKernelLinear (security : ℕ) (role : BodyRole) (queue : ℤ) :
    (Root security → ℝ) →ₗ[ℝ] canonicalKernels (primaryLaw security) (bodyReference security) 1 0 where
  toFun input := primaryKernel (primaryLaw security) (bodyReference security)
    (rootLift security role queue input) (rootLift_mean security role queue input)
  map_add' first second := by
    apply Subtype.ext
    funext colors centers
    exact congrFun (map_add (rootLift security role queue) first second) (colors 0)
  map_smul' scalar input := by
    apply Subtype.ext
    funext colors centers
    exact congrFun (map_smul (rootLift security role queue) scalar input) (colors 0)

def rootFamilyLinear (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ) :
    (Root security → ℝ) →ₗ[ℝ] ActualFamily security order :=
  (LinearMap.single ℝ (fun arity : TruncatedArity order =>
    canonicalKernels (primaryLaw security) (bodyReference security) arity.val.1.val arity.val.2.val)
      (BackgroundFamilies.primaryArity order horder)).comp (rootKernelLinear security role queue)

theorem rootFamilyLinear_apply (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (input : Root security → ℝ) :
    rootFamilyLinear security order horder role queue input =
      primaryFamily (primaryLaw security) (bodyReference security) order horder
        (rootLift security role queue input) (rootLift_mean security role queue input) := by
  funext arity
  by_cases hequal : arity = BackgroundFamilies.primaryArity order horder
  · subst arity
    simp only [rootFamilyLinear, LinearMap.comp_apply, LinearMap.single_apply,
      primaryFamily, Pi.single_eq_same, rootKernelLinear]
    rfl
  · simp only [rootFamilyLinear, LinearMap.comp_apply, LinearMap.single_apply,
      primaryFamily, Pi.single_eq_of_ne hequal]

theorem rootFamily_norm (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (input : Root security → ℝ) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
        (rootFamilyLinear security order horder role queue input) ≤
      primaryFactor security * rootCost security * Real.sqrt ((rootReference security).l2Sq input) := by
  rw [rootFamilyLinear_apply, primaryFamily_norm]
  have h := rootLift_norm security role queue input
  exact (mul_le_mul_of_nonneg_left h (by unfold primaryFactor; positivity)).trans_eq (by ring)







end

end CurrentAFT.RootTaggedFamilies

end

section













/-! The root-tagged first coefficient of the full actual unselected leg. -/

namespace CurrentAFT.RootTaggedLegFirst

open AFT DiffuseProfiles ProposalPrimary ActualControls LocalReferenceEnergy
  ActualBlockFock ActualBlockMean ActualCycleMeanMGF UniformBodyProfiles HistogramMean
  CycleRootExpansion RootTaggedLocal RootTaggedFamilies BackgroundEvaluation
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize ProposalPrimary.primaryLaw
  CycleRootExpansion.rootReference

local instance finThreeDecidableEq : DecidableEq (Fin 3) := Classical.decEq _

def legHistogram (security : ℕ) (root : Root security) (color : ActualControls.Palette security) : ℝ :=
  ∑ coordinate : Fin 3, ((primaryLawAt security root.val).map (fun word => word coordinate)).weight color

def meanLegHistogram (security : ℕ) (color : ActualControls.Palette security) : ℝ :=
  (rootReference security).expectation (fun root => legHistogram security root color)







def legFirstMass (security : ℕ) : (Root security → ℝ) →ₗ[ℝ] (ActualControls.Palette security → ℝ) where
  toFun input := fun color => ∑ root, (rootReference security).weight root * input root *
    (legHistogram security root color - meanLegHistogram security color)
  map_add' first second := by
    funext color
    simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' scalar input := by
    funext color
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro root _
    ring









end

end CurrentAFT.RootTaggedLegFirst

end

section















/-! Actual root-tagged full same-scalar unselected leg mass and higher channels. -/

namespace CurrentAFT.RootTaggedLegHigher

open AFT DiffuseProfiles ProposalPrimary ActualControls LocalReferenceEnergy
  ActualBlockFock PositiveFirstCoefficient CycleRootExpansion RootTaggedLocal
  PrimaryTensorInverse PhysicalBlockTensors BlockFock
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize ProposalPrimary.primaryLaw
  CycleRootExpansion.rootReference

local instance finThreeDecidableEq : DecidableEq (Fin 3) := Classical.decEq _

def rawMassLinear (security : ℕ) :
    (Root security → ℝ) →ₗ[ℝ] ((Fin 3 → ActualControls.Palette security) → ℝ) where
  toFun input := fun word => ∑ root, (rootReference security).weight root * input root *
    (primaryLawAt security root.val).weight word
  map_add' first second := by
    funext word
    simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' scalar input := by
    funext word
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro root _
    ring

def massLinear (security : ℕ) :
    (Root security → ℝ) →ₗ[ℝ] ((Fin 3 → ActualControls.Palette security) → ℝ) :=
  (rawMassLinear security).comp (TensorChannel.center (rootReference security))

def sourceLaw (security : ℕ) := (rootReference security).prod (scalarLaw security)

theorem tripleMassAt_const_score (security : ℕ) (root : ℤ) (scalar : LocalReferenceEnergy.Scalar security) (score : ℝ)
    (first second third : ActualControls.Palette security) :
    tripleMassAt security root scalar (fun _ => score) first second third =
      score * tripleMassAt security root scalar (fun _ => 1) first second third := by
  unfold tripleMassAt signedPairAt
  simp only [mul_one, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro primary _
  ring

theorem rawMass_joint_source (security : ℕ) (input : Root security → ℝ) :
    rawMassLinear security input = tripleMass (jointTripleMass security (sourceLaw security)
      (fun source => (source.1.val : ℤ)) Prod.snd (fun source _ => input source.1)) := by
  funext word
  simp only [rawMassLinear, LinearMap.coe_mk, AddHom.coe_mk, primaryLawAt, FiniteDist.mix_weight,
    tripleMass, jointTripleMass, sourceLaw, Fintype.sum_prod_type, FiniteDist.prod_weight]
  simp_rw [positiveTriple_weight, tripleMass]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro root _
  apply Finset.sum_congr rfl
  intro scalar _
  rw [tripleMassAt_const_score security root.val scalar (input root)]
  ring













theorem rawMass_uniform_energy (security : ℕ) (input : Root security → ℝ) :
    profileSquareNorm (FiniteDist.independent (fun _ : Fin 3 => uniformReference security)).weight
      (rawMassLinear security input) ≤ (4 * pairBudget security) * (rootReference security).l2Sq input := by
  rw [rawMass_joint_source]
  have hidentity := triple_density_energy (uniformReference security)
    (jointTripleMass security (sourceLaw security) (fun source => (source.1.val : ℤ)) Prod.snd (fun source _ => input source.1))
  change densitySquareNorm _ _ = _ at hidentity
  rw [densityScore_square] at hidentity
  rw [hidentity]
  have havg := tripleEnergy_average_le (sourceLaw security) (uniformReference security).weight
    (uniformReference security).nonneg (fun source => tripleMassAt security source.1.val source.2 (fun _ => input source.1))
  apply havg.trans
  calc
    _ ≤ ∑ source, (sourceLaw security).weight source *
        ((4 * pairBudget security) * (primaryLaw security).expectation (fun _ => input source.1 ^ 2)) :=
      Finset.sum_le_sum fun source _ => mul_le_mul_of_nonneg_left
        (tripleMassAt_energy security source.1.val source.2 (fun _ => input source.1)) ((sourceLaw security).nonneg source)
    _ = _ := by
      simp only [FiniteDist.expectation_const, sourceLaw, Fintype.sum_prod_type, FiniteDist.prod_weight]
      simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, FiniteDist.sum_one, one_mul]
      unfold FiniteDist.l2Sq FiniteDist.expectation
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro root _
      ring

theorem massLinear_uniform_energy (security : ℕ) (input : Root security → ℝ) :
    profileSquareNorm (FiniteDist.independent (fun _ : Fin 3 => uniformReference security)).weight
      (massLinear security input) ≤ (4 * pairBudget security) * (rootReference security).l2Sq input := by
  change profileSquareNorm _ (rawMassLinear security (TensorChannel.center (rootReference security) input)) ≤ _
  apply (rawMass_uniform_energy security _).trans
  apply mul_le_mul_of_nonneg_left (TensorChannel.center_energy_le _ _)
  have hmark := markMass_pos security
  unfold pairBudget primaryMaximum
  positivity

end

end CurrentAFT.RootTaggedLegHigher

end

section





















/-! Exact canonical primary coefficients of the actual unselected three-output leg. -/

namespace CurrentAFT.RootLegCoefficientFamily

open AFT DiffuseProfiles ProposalPrimary ActualControls
open ControlCoordinates ControlProduct GradedControlAlgebra GradedInverse
  LocalCoefficientFamily
open scoped BigOperators Classical

noncomputable section

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected :=
  Classical.decEq _

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

abbrev Palette (security : ℕ) := ActualControls.Palette security
abbrev Family (security order : ℕ) := KernelFamily (primaryLaw security) (bodyReference security) order

def selectedDensity (security degree : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) (hdegree : Fintype.card selected = degree)
    (word : Fin degree → Palette security) : ℝ :=
  LocalTensors.referenceRestrictedComponent (fun _ : Fin 3 => primaryLaw security)
    (fun _ : Fin 3 => LocalReferenceEnergy.uniformReference security) mass selected
      (word ∘ Fintype.equivFinOfCardEq hdegree)

 theorem selectedDensity_generic_canonical {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]
    (primary reference : FiniteDist Color) (hpositive : ∀ color, 0 < primary.weight color)
    (degree : ℕ) (mass : (Slot → Color) → ℝ) (selected : Finset Slot)
    (hdegree : Fintype.card selected = degree) :
    Hoeffding.Canonical (fun _ : Fin degree => primary) Finset.univ
      (fun word => LocalTensors.referenceRestrictedComponent (fun _ : Slot => primary)
        (fun _ : Slot => reference) mass selected (word ∘ Fintype.equivFinOfCardEq hdegree)) := by
  have hraw := LocalTensors.referenceRestrictedComponent_canonical
    (fun _ : Slot => primary) (fun _ : Slot => reference) (fun _ => hpositive) mass selected
  let raw : Kernel (Primary := Color) (Body := Unit) selected (Fin 0) :=
    fun colors _ => LocalTensors.referenceRestrictedComponent (fun _ : Slot => primary)
      (fun _ : Slot => reference) mass selected colors
  have hcentered : raw ∈ centeredKernelSpace primary (FiniteDist.uniform Unit) := by
    constructor
    · intro index colors _
      exact hraw.2 index (Finset.mem_univ index) colors
    · intro index
      exact Fin.elim0 index
  have htransport := reindexKernel_centered primary (FiniteDist.uniform Unit)
    (Fintype.equivFinOfCardEq hdegree) (Equiv.refl (Fin 0)) raw hcentered
  constructor
  · intro first second hequal
    have heq : first = second := funext (fun index => hequal index (Finset.mem_univ index))
    rw [heq]
  · intro index _ word
    exact htransport.1 index word Fin.elim0

theorem selectedDensity_canonical (security degree : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) (hdegree : Fintype.card selected = degree) :
    Hoeffding.Canonical (fun _ : Fin degree => primaryLaw security) Finset.univ
      (selectedDensity security degree mass selected hdegree) :=
  selectedDensity_generic_canonical (primaryLaw security) (LocalReferenceEnergy.uniformReference security)
    (primaryReference_positive security) degree mass selected hdegree

def normalizedSelectedDensity (security degree : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) (hdegree : Fintype.card selected = degree) :
    (Fin degree → Palette security) → ℝ :=
  PrimaryTensorInverse.tensorInverse security degree (selectedDensity security degree mass selected hdegree)



theorem normalizedSelectedDensity_canonical (security degree : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) (hdegree : Fintype.card selected = degree) :
    Hoeffding.Canonical (fun _ : Fin degree => primaryLaw security) Finset.univ
      (normalizedSelectedDensity security degree mass selected hdegree) :=
  PrimaryTensorInverse.tensorInverse_canonical security degree _
    (selectedDensity_canonical security degree mass selected hdegree)

def selectedKernel (security degree : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) (hdegree : Fintype.card selected = degree) :
    canonicalKernels (primaryLaw security) (bodyReference security) degree 0 := by
  let raw : DensityKernel (Primary := Palette security) (Body := SafePalette security) degree 0 :=
    fun colors _ => normalizedSelectedDensity security degree mass selected hdegree colors
  have hcanonical := normalizedSelectedDensity_canonical security degree mass selected hdegree
  have hcentered : raw ∈ centeredKernelSpace (primaryLaw security) (bodyReference security) := by
    constructor
    · intro index colors _
      exact hcanonical.2 index (Finset.mem_univ index) colors
    · intro index
      exact Fin.elim0 index
  have hs := symmetrize_centered (primaryLaw security) (bodyReference security) raw hcentered
  refine ⟨symmetrize raw, hs.1, hs.2, ?_⟩
  intro primaryOrder bodyOrder colors centers
  rw [symmetrize_primary_permutation, symmetrize_body_permutation]

def selectedArity (order : ℕ) (selected : Finset (Fin 3)) (hdegree : selected.card ≤ order) : TruncatedArity order :=
  ⟨(⟨selected.card, by omega⟩, 0), by simpa using hdegree⟩

def selectedFamily (security order : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) : Family security order :=
  if hdegree : selected.card ≤ order then
    Pi.single (selectedArity order selected hdegree)
      (selectedKernel security selected.card mass selected (by simp))
  else 0

def higherFamily (security order : ℕ) (mass : (Fin 3 → Palette security) → ℝ) : Family security order :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).filter (fun selected => 2 ≤ selected.card),
    selectedFamily security order mass selected

theorem higherFamily_vanishesBelow (security order : ℕ) (mass : (Fin 3 → Palette security) → ℝ) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 2 (higherFamily security order mass) := by
  intro arity hsmall
  unfold higherFamily
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro selected hselected
  have hcard := (Finset.mem_filter.mp hselected).2
  unfold selectedFamily
  split_ifs with hdegree
  · rw [Pi.single_eq_of_ne]
    intro hequal
    have hsmall' := hsmall
    rw [hequal] at hsmall'
    change selected.card + 0 < 2 at hsmall'
    omega
  · rfl

/-- The higher family of the actual root-centered full unselected leg. -/
def rootHigherFamily (security order : ℕ) (input : CycleRootExpansion.Root security → ℝ) : Family security order :=
  higherFamily security order (RootTaggedLegHigher.massLinear security input)

theorem rootHigherFamily_vanishesBelow (security order : ℕ) (input : CycleRootExpansion.Root security → ℝ) :
    VanishesBelow (primaryLaw security) (bodyReference security) order 2 (rootHigherFamily security order input) :=
  higherFamily_vanishesBelow security order _







end

end CurrentAFT.RootLegCoefficientFamily

end

section

















/-! # Genuine local coefficient norm budgets after the actual primary inverse -/

namespace CurrentAFT.RootLegCoefficientNorm

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct ControlNorm
open RootLegCoefficientFamily LocalReferenceEnergy RootTaggedLegHigher
open scoped BigOperators Classical

noncomputable section

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _

abbrev Palette (security : ℕ) := ActualControls.Palette security

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

 theorem blockEnergy_no_body {Primary Body Index : Type*}
    [Fintype Primary] [Fintype Body] [Fintype Index]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (kernel : (Index → Primary) → ℝ) :
    blockEnergy primary body (fun colors (_ : Fin 0 → Body) => kernel colors) =
      (FiniteDist.independent (fun _ : Index => primary)).l2Sq kernel := by
  unfold blockEnergy FiniteDist.l2Sq
  rw [FiniteDist.expectation_prod]
  simp only [FiniteDist.expectation_const]

def primaryMassEnergy (security : ℕ) (mass : (Fin 3 → Palette security) → ℝ) : ℝ :=
  profileSquareNorm (FiniteDist.independent (fun _ : Fin 3 => primaryLaw security)).weight mass

theorem selectedDensity_energy (security degree : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) (hdegree : Fintype.card selected = degree) :
    (FiniteDist.independent (fun _ : Fin degree => primaryLaw security)).l2Sq
      (selectedDensity security degree mass selected hdegree) ≤
        ((4 : ℝ) ^ selected.card) ^ 2 * primaryMassEnergy security mass := by
  let raw : Kernel (Primary := Palette security) (Body := Unit) selected (Fin 0) :=
    fun colors _ => LocalTensors.referenceRestrictedComponent (fun _ : Fin 3 => primaryLaw security)
      (fun _ : Fin 3 => uniformReference security) mass selected colors
  rw [← blockEnergy_no_body (primaryLaw security) (FiniteDist.uniform Unit)]
  change blockEnergy (primaryLaw security) (FiniteDist.uniform Unit)
    (reindexKernel (Fintype.equivFinOfCardEq hdegree) (Equiv.refl (Fin 0)) raw) ≤ _
  rw [blockEnergy_reindex, blockEnergy_no_body]
  have h := LocalTensors.referenceRestrictedComponent_l2Sq_le (fun _ : Fin 3 => primaryLaw security)
    (fun _ : Fin 3 => uniformReference security) (fun _ => primaryReference_positive security) mass selected 2 (by norm_num)
    (fun _ color => by
      rw [uniformReference_weight]
      have hlower : 1 / (2 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight color := by
        simpa only [primaryLaw] using primaryProfile_atom_lower security color
      have hq := FirstResponse.modulus_pos security
      have hidentity : (1 / (Parameters.modulus security : ℝ)) = 2 * (1 / (2 * (Parameters.modulus security : ℝ))) := by ring
      rw [hidentity]
      exact mul_le_mul_of_nonneg_left hlower (by norm_num))
  change _ ≤ ((2 * (2 : ℝ)) ^ selected.card) ^ 2 * densitySquareNorm
    (FiniteDist.independent (fun _ : Fin 3 => primaryLaw security)).weight
    (fun word => mass word / (FiniteDist.independent (fun _ : Fin 3 => primaryLaw security)).weight word) at h
  rw [densityScore_square] at h
  simpa only [show (2 : ℝ) * 2 = 4 by norm_num, primaryMassEnergy] using h

theorem normalizedSelectedDensity_energy (security degree : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) (hdegree : Fintype.card selected = degree) :
    (FiniteDist.independent (fun _ : Fin degree => primaryLaw security)).l2Sq
      (normalizedSelectedDensity security degree mass selected hdegree) ≤
        ((2 / activation security) ^ degree) ^ 2 * ((4 : ℝ) ^ selected.card) ^ 2 * primaryMassEnergy security mass := by
  have h := PrimaryTensorInverse.tensorInverse_energy security degree (selectedDensity security degree mass selected hdegree)
  exact h.trans ((mul_le_mul_of_nonneg_left (selectedDensity_energy security degree mass selected hdegree)
    (sq_nonneg _)).trans_eq (by ring))

theorem selectedKernel_energy (security degree : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) (hdegree : Fintype.card selected = degree) :
    blockEnergy (primaryLaw security) (bodyReference security) (selectedKernel security degree mass selected hdegree).val ≤
      ((2 / activation security) ^ degree) ^ 2 * ((4 : ℝ) ^ selected.card) ^ 2 * primaryMassEnergy security mass := by
  change blockEnergy (primaryLaw security) (bodyReference security)
    (symmetrize (fun colors (_ : Fin 0 → SafePalette security) =>
      normalizedSelectedDensity security degree mass selected hdegree colors)) ≤ _
  apply (blockEnergy_symmetrize_le _ _ _).trans
  rw [blockEnergy_no_body]
  exact normalizedSelectedDensity_energy security degree mass selected hdegree

theorem primaryMassEnergy_uniform_le (security : ℕ) (mass : (Fin 3 → Palette security) → ℝ) :
    primaryMassEnergy security mass ≤
      8 * profileSquareNorm (FiniteDist.independent (fun _ : Fin 3 => uniformReference security)).weight mass := by
  let primary := FiniteDist.independent (fun _ : Fin 3 => primaryLaw security)
  let uniform := FiniteDist.independent (fun _ : Fin 3 => uniformReference security)
  have hu (word : Fin 3 → Palette security) : 0 < uniform.weight word := by
    change 0 < ∏ index : Fin 3, (uniformReference security).weight (word index)
    exact Finset.prod_pos (fun _ _ => by rw [uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security))
  have hcompare (word : Fin 3 → Palette security) : uniform.weight word ≤ 8 * primary.weight word := by
    have h := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin 3)))
      (fun index _ => (uniformReference security).nonneg (word index))
      (fun index _ => show (uniformReference security).weight (word index) ≤ 2 * (primaryLaw security).weight (word index) by
        rw [uniformReference_weight]
        have hlower : 1 / (2 * (Parameters.modulus security : ℝ)) ≤ (primaryLaw security).weight (word index) := by
          simpa only [primaryLaw] using primaryProfile_atom_lower security (word index)
        have hidentity : 1 / (Parameters.modulus security : ℝ) = 2 * (1 / (2 * (Parameters.modulus security : ℝ))) := by ring
        rw [hidentity]
        exact mul_le_mul_of_nonneg_left hlower (by norm_num))
    change (∏ index : Fin 3, (uniformReference security).weight (word index)) ≤
      8 * ∏ index : Fin 3, (primaryLaw security).weight (word index)
    simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      show (2 : ℝ) ^ 3 = 8 by norm_num] using h
  unfold primaryMassEnergy profileSquareNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro word _
  have hlower : uniform.weight word / 8 ≤ primary.weight word := (div_le_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr (by
    simpa only [mul_comm] using hcompare word)
  exact (div_le_div_of_nonneg_left (sq_nonneg (mass word)) (div_pos (hu word) (by norm_num)) hlower).trans_eq (by ring)

theorem selectedKernel_norm (security degree : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) (hdegree : Fintype.card selected = degree) :
    blockL2 (primaryLaw security) (bodyReference security) (selectedKernel security degree mass selected hdegree).val ≤
      (2 / activation security) ^ degree * (4 : ℝ) ^ selected.card * Real.sqrt (primaryMassEnergy security mass) := by
  let coefficient := (2 / activation security) ^ degree * (4 : ℝ) ^ selected.card
  have hcoefficient : 0 ≤ coefficient := by
    dsimp only [coefficient]
    exact mul_nonneg (pow_nonneg (div_nonneg (by norm_num) (activation_pos security).le) _) (by positivity)
  have h := Real.sqrt_le_sqrt (selectedKernel_energy security degree mass selected hdegree)
  change blockL2 (primaryLaw security) (bodyReference security) (selectedKernel security degree mass selected hdegree).val ≤ _ at h
  have hrewrite : ((2 / activation security) ^ degree) ^ 2 * ((4 : ℝ) ^ selected.card) ^ 2 * primaryMassEnergy security mass =
      coefficient ^ 2 * primaryMassEnergy security mass := by dsimp only [coefficient]; ring
  rw [hrewrite, Real.sqrt_mul (sq_nonneg coefficient), Real.sqrt_sq_eq_abs, abs_of_nonneg hcoefficient] at h
  exact h

theorem selectedFamily_norm (security order : ℕ) (mass : (Fin 3 → Palette security) → ℝ)
    (selected : Finset (Fin 3)) (primaryFactor bodyFactor : ℝ) (hprimaryFactor : 0 ≤ primaryFactor) :
    GradedControlNorm.familyNorm (primaryLaw security) (bodyReference security) order primaryFactor bodyFactor
      (selectedFamily security order mass selected) ≤
        primaryFactor ^ selected.card * ((2 / activation security) ^ selected.card * (4 : ℝ) ^ selected.card *
          Real.sqrt (primaryMassEnergy security mass)) := by
  unfold selectedFamily
  split_ifs with hdegree
  · rw [BackgroundFamilies.familyNorm_single]
    change gradeWeight primaryFactor bodyFactor selected.card 0 *
      blockL2 (primaryLaw security) (bodyReference security)
        (selectedKernel security selected.card mass selected (by simp)).val ≤ _
    simp only [gradeWeight, pow_zero, mul_one]
    exact mul_le_mul_of_nonneg_left (selectedKernel_norm security selected.card mass selected (by simp))
      (pow_nonneg hprimaryFactor _)
  · rw [GradedControlStability.familyNorm_zero]
    apply mul_nonneg (pow_nonneg hprimaryFactor _)
    apply mul_nonneg
    · apply mul_nonneg
      · exact pow_nonneg (div_nonneg (by norm_num) (activation_pos security).le) _
      · positivity
    · exact Real.sqrt_nonneg _

end

end CurrentAFT.RootLegCoefficientNorm

end

section













/-! # Actual local responses are linear in the common public score -/
namespace CurrentAFT.RootLegCoefficientLinear

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
open GradedControlAlgebra GradedInverse RootLegCoefficientFamily
open scoped BigOperators Classical

noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

abbrev Palette (security : ℕ) := ActualControls.Palette security

def selectedDensityLinear (security degree : ℕ) (selected : Finset (Fin 3))
    (hdegree : Fintype.card selected = degree) :
    ((Fin 3 → Palette security) → ℝ) →ₗ[ℝ] ((Fin degree → Palette security) → ℝ) where
  toFun := fun mass => selectedDensity security degree mass selected hdegree
  map_add' first second := by
    funext word
    simp only [selectedDensity, LocalTensors.referenceRestrictedComponent, Pi.add_apply,
      add_mul, Finset.sum_add_distrib]
  map_smul' scalar mass := by
    funext word
    simp only [selectedDensity, LocalTensors.referenceRestrictedComponent, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum]

def normalizedSelectedLinear (security degree : ℕ) (selected : Finset (Fin 3))
    (hdegree : Fintype.card selected = degree) :=
  (PrimaryTensorInverse.tensorInverse security degree).comp (selectedDensityLinear security degree selected hdegree)

def selectedKernelLinear (security degree : ℕ) (selected : Finset (Fin 3))
    (hdegree : Fintype.card selected = degree) :
    ((Fin 3 → Palette security) → ℝ) →ₗ[ℝ]
      canonicalKernels (primaryLaw security) (bodyReference security) degree 0 where
  toFun := fun mass => selectedKernel security degree mass selected hdegree
  map_add' first second := by
    apply Subtype.ext
    have hraw : (fun colors (_ : Fin 0 → SafePalette security) =>
        normalizedSelectedDensity security degree (first + second) selected hdegree colors) =
        (fun colors (_ : Fin 0 → SafePalette security) => normalizedSelectedDensity security degree first selected hdegree colors) +
        (fun colors (_ : Fin 0 → SafePalette security) => normalizedSelectedDensity security degree second selected hdegree colors) := by
      funext colors _
      exact congrFun ((normalizedSelectedLinear security degree selected hdegree).map_add first second) colors
    change ControlProduct.symmetrize _ = ControlProduct.symmetrize _ + ControlProduct.symmetrize _
    rw [hraw]
    exact (symmetrizeLinear (PS := Fin degree) (BS := Fin 0)).map_add _ _
  map_smul' scalar mass := by
    apply Subtype.ext
    have hraw : (fun colors (_ : Fin 0 → SafePalette security) =>
        normalizedSelectedDensity security degree (scalar • mass) selected hdegree colors) =
        scalar • (fun colors (_ : Fin 0 → SafePalette security) =>
          normalizedSelectedDensity security degree mass selected hdegree colors) := by
      funext colors _
      exact congrFun ((normalizedSelectedLinear security degree selected hdegree).map_smul scalar mass) colors
    change ControlProduct.symmetrize _ = scalar • ControlProduct.symmetrize _
    rw [hraw]
    exact (symmetrizeLinear (PS := Fin degree) (BS := Fin 0)).map_smul scalar _

def selectedFamilyLinear (security order : ℕ) (selected : Finset (Fin 3)) :
    ((Fin 3 → Palette security) → ℝ) →ₗ[ℝ] Family security order where
  toFun := fun mass => selectedFamily security order mass selected
  map_add' first second := by
    unfold selectedFamily
    split_ifs with hdegree
    · have hkernel := (selectedKernelLinear security selected.card selected (by simp)).map_add first second
      funext arity
      by_cases hequal : arity = selectedArity order selected hdegree
      · subst arity
        simp only [Pi.add_apply, Pi.single_eq_same]
        exact hkernel
      · simp only [Pi.add_apply, Pi.single_eq_of_ne hequal, add_zero]
    · exact (add_zero _).symm
  map_smul' scalar mass := by
    unfold selectedFamily
    split_ifs with hdegree
    · have hkernel := (selectedKernelLinear security selected.card selected (by simp)).map_smul scalar mass
      funext arity
      by_cases hequal : arity = selectedArity order selected hdegree
      · subst arity
        simp only [Pi.smul_apply, Pi.single_eq_same]
        exact hkernel
      · simp only [Pi.smul_apply, Pi.single_eq_of_ne hequal, smul_zero]
    · exact (smul_zero _).symm


def higherFamilyLinear (security order : ℕ) :
    ((Fin 3 → Palette security) → ℝ) →ₗ[ℝ] Family security order :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).filter (fun selected => 2 ≤ selected.card),
    selectedFamilyLinear security order selected

theorem higherFamilyLinear_apply (security order : ℕ) (mass : (Fin 3 → Palette security) → ℝ) :
    higherFamilyLinear security order mass = higherFamily security order mass := by
  simp only [higherFamilyLinear, LinearMap.sum_apply, higherFamily, selectedFamilyLinear,
    LinearMap.coe_mk, AddHom.coe_mk]

def rootHigherLinear (security order : ℕ) :
    (CycleRootExpansion.Root security → ℝ) →ₗ[ℝ] Family security order :=
  (higherFamilyLinear security order).comp (RootTaggedLegHigher.massLinear security)

theorem rootHigherLinear_apply (security order : ℕ) (input : CycleRootExpansion.Root security → ℝ) :
    rootHigherLinear security order input = rootHigherFamily security order input := by
  rw [rootHigherLinear, LinearMap.comp_apply, higherFamilyLinear_apply]
  rfl

end

end CurrentAFT.RootLegCoefficientLinear

end

section















/-! Exact physical polynomial images of the actual unselected leg coefficients. -/
namespace CurrentAFT.RootLegCoefficientEvaluation
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
  LocalCoefficientEvaluation RootLegCoefficientFamily LeadingEvaluation
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
abbrev Palette (security : ℕ) := ActualControls.Palette security





end
end CurrentAFT.RootLegCoefficientEvaluation

end

section















/-! Actual higher unselected-leg coefficient cost from the real same-scalar law. -/

namespace CurrentAFT.RootLegCoefficientBounds

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates GradedControlAlgebra
  GradedControlNorm GradedControlStability GradedInverseNorm RootLegCoefficientFamily RootLegCoefficientNorm
  RootLegCoefficientLinear RootTaggedLegHigher CycleRootExpansion BackgroundRates BackgroundLinear
  LocalReferenceEnergy
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw ActualControls.bodyReference rootReference

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

theorem pairBudget_nonneg (security : ℕ) : 0 ≤ pairBudget security := by
  have hmark := markMass_pos security
  unfold pairBudget primaryMaximum
  positivity

theorem rootMass_primary_energy (security : ℕ) (input : Root security → ℝ) :
    primaryMassEnergy security (massLinear security input) ≤
      (32 * pairBudget security) * (rootReference security).l2Sq input := by
  apply (primaryMassEnergy_uniform_le security _).trans
  exact (mul_le_mul_of_nonneg_left (massLinear_uniform_energy security input) (by norm_num : (0 : ℝ) ≤ 8)).trans_eq (by ring)

def normalizedFactor (security : ℕ) : ℝ := primaryFactor security * (8 / activation security)

theorem normalizedFactor_nonneg (security : ℕ) : 0 ≤ normalizedFactor security := by
  unfold normalizedFactor primaryFactor
  have := activation_pos security
  positivity

theorem normalizedFactor_decay (security : ℕ) : normalizedFactor security ≤ 32 / (Parameters.base security : ℝ) ^ 63 := by
  have hb := FirstResponse.base_pos security
  have ha := activation_pos security
  have hinv : 1 / activation security ≤ 4 * (Parameters.base security : ℝ) := by
    have h := one_div_le_one_div_of_le (by positivity : 0 < 1 / (4 * (Parameters.base security : ℝ)))
      (FirstResponse.activation_lower_simple security)
    simpa only [one_div_one_div] using h
  rw [normalizedFactor, primaryFactor_eq]
  calc
    _ = (1 / (Parameters.base security : ℝ) ^ 64) * 8 * (1 / activation security) := by ring
    _ ≤ (1 / (Parameters.base security : ℝ) ^ 64) * 8 * (4 * (Parameters.base security : ℝ)) := by gcongr
    _ = _ := by field_simp; norm_num

theorem normalizedFactor_le_one (security : ℕ) : normalizedFactor security ≤ 1 := by
  apply (normalizedFactor_decay security).trans
  have hb := FirstResponse.base_pos security
  have hpower : (32 : ℝ) ≤ (Parameters.base security : ℝ) ^ 63 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
      (show (2 : ℝ) ≤ (Parameters.base security : ℝ) by exact_mod_cast Parameters.base_ge_two security) 63
    exact (by norm_num : (32 : ℝ) ≤ 2 ^ 63).trans h
  exact (div_le_one (pow_pos hb _)).mpr hpower

theorem selected_rootFamily_norm (security order : ℕ) (input : Root security → ℝ) (selected : Finset (Fin 3)) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (selectedFamily security order (massLinear security input) selected) ≤
        normalizedFactor security ^ selected.card * Real.sqrt (32 * pairBudget security) *
          Real.sqrt ((rootReference security).l2Sq input) := by
  have hpositive : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have h := selectedFamily_norm security order (massLinear security input) selected
    (primaryFactor security) (bodyFactor security) hpositive
  have henergy := Real.sqrt_le_sqrt (rootMass_primary_energy security input)
  rw [Real.sqrt_mul (mul_nonneg (by norm_num) (pairBudget_nonneg security))] at henergy
  apply h.trans
  calc
    _ = normalizedFactor security ^ selected.card *
        Real.sqrt (primaryMassEnergy security (massLinear security input)) := by
      unfold normalizedFactor
      rw [show (8 : ℝ) = 2 * 4 by norm_num]
      simp only [mul_pow, div_pow]
      ring
    _ ≤ normalizedFactor security ^ selected.card *
        (Real.sqrt (32 * pairBudget security) * Real.sqrt ((rootReference security).l2Sq input)) :=
      mul_le_mul_of_nonneg_left henergy (pow_nonneg (normalizedFactor_nonneg security) selected.card)
    _ = _ := by ring

def higherCost (security : ℕ) : ℝ :=
  8 * normalizedFactor security ^ 2 * Real.sqrt (32 * pairBudget security)

theorem rootHigher_norm (security order : ℕ) (input : Root security → ℝ) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (rootHigherLinear security order input) ≤ higherCost security * Real.sqrt ((rootReference security).l2Sq input) := by
  rw [rootHigherLinear_apply]
  unfold rootHigherFamily higherFamily
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hb : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  apply (familyNorm_sum_le _ _ _ _ _ hp hb _ _).trans
  have hpoint (selected : Finset (Fin 3)) (hselected : selected ∈
      (Finset.univ : Finset (Finset (Fin 3))).filter (fun selected => 2 ≤ selected.card)) :
      familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
        (selectedFamily security order (massLinear security input) selected) ≤
          normalizedFactor security ^ 2 * Real.sqrt (32 * pairBudget security) * Real.sqrt ((rootReference security).l2Sq input) := by
    apply (selected_rootFamily_norm security order input selected).trans
    have hpower := pow_le_pow_of_le_one (normalizedFactor_nonneg security) (normalizedFactor_le_one security)
      (Finset.mem_filter.mp hselected).2
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpower (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  apply (Finset.sum_le_sum hpoint).trans
  have hcard : (((Finset.univ : Finset (Finset (Fin 3))).filter (fun selected => 2 ≤ selected.card)).card : ℝ) ≤ 8 := by
    have h := Finset.card_filter_le (Finset.univ : Finset (Finset (Fin 3))) (fun selected => 2 ≤ selected.card)
    exact_mod_cast (by simpa using h : _ ≤ 8)
  rw [Finset.sum_const, nsmul_eq_mul]
  calc
    _ ≤ 8 * (normalizedFactor security ^ 2 * Real.sqrt (32 * pairBudget security) * Real.sqrt ((rootReference security).l2Sq input)) := by gcongr
    _ = _ := by unfold higherCost; ring

theorem sqrtBudget_polynomial (security : ℕ) :
    Real.sqrt (32 * pairBudget security) ≤ 6 * Real.sqrt LocalRaisingBounds.pairConstant * (Parameters.base security : ℝ) ^ 24 := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 32)]
  have hroot : Real.sqrt 32 ≤ (6 : ℝ) := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  exact (mul_le_mul hroot (LocalRaisingBounds.pairBudget_sqrt_polynomial security)
    (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)).trans_eq (by ring)

def higherConstant : ℝ := 49152 * Real.sqrt LocalRaisingBounds.pairConstant

theorem higherCost_decay (security : ℕ) : higherCost security ≤ higherConstant / (Parameters.base security : ℝ) ^ 102 := by
  have hb := FirstResponse.base_pos security
  unfold higherCost
  calc
    _ ≤ 8 * (32 / (Parameters.base security : ℝ) ^ 63) ^ 2 *
        (6 * Real.sqrt LocalRaisingBounds.pairConstant * (Parameters.base security : ℝ) ^ 24) := by
      gcongr
      · exact normalizedFactor_nonneg security
      · exact normalizedFactor_decay security
      · exact sqrtBudget_polynomial security
    _ = _ := by unfold higherConstant; field_simp; ring

end

end CurrentAFT.RootLegCoefficientBounds

end

section













/-! Pure-primary positive denominators for the actual singleton root means. -/

namespace CurrentAFT.RootMeanPrimary

open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls LocalReferenceEnergy
  UniformBodyProfiles CycleRootExpansion RootTaggedLocal PrimaryTensorInverse PrimaryMassFamilies
  ControlCoordinates GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverse GradedInverseNorm
  BackgroundFamilies BackgroundRates BackgroundEvaluation BackgroundFirstEvaluation
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw bodyReference rootReference
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def meanProfile (security : ℕ) (role : BodyRole) (queue : ℤ) : ActualControls.Palette security → ℝ :=
  (meanLaw security role queue).weight - (uniformReference security).weight

theorem meanProfile_mass (security : ℕ) (role : BodyRole) (queue : ℤ) :
    (∑ color, meanProfile security role queue color) = 0 := by
  simp only [meanProfile, Pi.sub_apply, Finset.sum_sub_distrib, FiniteDist.sum_one, sub_self]

theorem meanProfile_energy (security : ℕ) (role : BodyRole) (queue : ℤ) :
    profileSquareNorm (primaryLaw security).weight (meanProfile security role queue) ≤ 2 * deviation security ^ 2 := by
  have hnorm := pow_le_pow_left₀ (norm_nonneg _) (meanLaw_uniform_norm security role queue) 2
  change ‖ProfileHilbert.whiten (uniformReference security).weight (meanProfile security role queue)‖ ^ 2 ≤ _ at hnorm
  rw [ProfileHilbert.whiten_norm_sq _ _ (uniformReference security).nonneg] at hnorm
  exact (uniform_to_primary_energy security _).trans (mul_le_mul_of_nonneg_left hnorm (by norm_num))

def positiveAtom (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ) : ActualFamily security order :=
  massCertificateFamily security order 1 horder (oneWordProfile (meanProfile security role queue))
    (oneWordProfile_centered _ (meanProfile_mass security role queue)) (oneWordProfile_symmetric _)



theorem positiveAtom_norm (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (positiveAtom security order horder role queue) ≤ 2064 / (Parameters.base security : ℝ) ^ 94 := by
  have hb := FirstResponse.base_pos security
  have ha := activation_pos security
  have hd := deviation_nonneg security
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have henergy : massEnergy security 1 (oneWordProfile (meanProfile security role queue)) ≤ 2 * deviation security ^ 2 := by
    rw [show massEnergy security 1 (oneWordProfile (meanProfile security role queue)) =
      profileSquareNorm (primaryLaw security).weight (meanProfile security role queue) from
        oneWordProfile_energy _ _]
    exact meanProfile_energy security role queue
  have hsqrt : Real.sqrt (massEnergy security 1 (oneWordProfile (meanProfile security role queue))) ≤ 2 * deviation security := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    exact henergy.trans (by nlinarith [sq_nonneg (deviation security)])
  have hinv : 2 / activation security ≤ 8 * (Parameters.base security : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (FirstResponse.activation_inverse_le security) (by norm_num : (0 : ℝ) ≤ 2)
    convert h using 1 <;> first | rfl | ring
  have h := massCertificateFamily_norm security order 1 horder (primaryFactor security) (bodyFactor security) hp
    (oneWordProfile (meanProfile security role queue))
    (oneWordProfile_centered _ (meanProfile_mass security role queue)) (oneWordProfile_symmetric _)
  simp only [pow_one] at h
  apply h.trans
  calc
    _ ≤ (1 / (Parameters.base security : ℝ) ^ 64) * (8 * (Parameters.base security : ℝ)) * (2 * deviation security) :=
      mul_le_mul (mul_le_mul (le_of_eq (primaryFactor_eq security)) hinv (by positivity) (by positivity))
        hsqrt (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by unfold deviation; field_simp; norm_num

def positiveFamily (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ) : ActualFamily security order :=
  1 + positiveAtom security order horder role queue

def positiveInverse (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ) : ActualFamily security order :=
  backgroundInverse (primaryLaw security) (bodyReference security) order (positiveFamily security order horder role queue)







theorem positiveInverse_norm (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (positiveInverse security order horder role queue) ≤ 2 := by
  have hb := FirstResponse.base_pos security
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hbdy : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  have htwo : (2 : ℝ) ≤ (Parameters.base security : ℝ) := by exact_mod_cast Parameters.base_ge_two security
  have hpower : (4128 : ℝ) ≤ (Parameters.base security : ℝ) ^ 94 := by
    exact (by norm_num : (4128 : ℝ) ≤ 2 ^ 94).trans (pow_le_pow_left₀ (by norm_num) htwo 94)
  have hhalf : 2064 / (Parameters.base security : ℝ) ^ 94 ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (pow_pos hb _)).mpr
    linarith
  have hdefect : familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (1 - positiveFamily security order horder role queue) ≤ (1 / 2 : ℝ) := by
    have heq : 1 - positiveFamily security order horder role queue = - positiveAtom security order horder role queue := by
      unfold positiveFamily
      abel
    rw [heq, familyNorm_neg]
    exact (positiveAtom_norm security order horder role queue).trans hhalf
  exact (backgroundInverse_norm_le _ _ _ _ _ hp hbdy _ (1 / 2) (by norm_num) hdefect).trans_eq (by norm_num)

end
end CurrentAFT.RootMeanPrimary

end

section













/-! Pure-primary support is preserved by actual convolution and finite inversion. -/

namespace CurrentAFT.PrimaryOnlyFamily

open AFT ControlCoordinates ControlProduct GradedControlAlgebra GradedInverse
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

def PrimaryOnly (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (family : KernelFamily primary body order) : Prop :=
  ∀ arity, 0 < arity.val.2.val → family arity = 0

























end
end CurrentAFT.PrimaryOnlyFamily

end

section















/-! Pure-primary finite normalization of the actual complete unselected leg. -/
namespace CurrentAFT.RootLegNormalized

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
open GradedControlAlgebra GradedInverse RootLegCoefficientFamily RootLegCoefficientEvaluation LocalCoefficientEvaluation
open scoped BigOperators Classical

noncomputable section

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

abbrev Palette (security : ℕ) := ActualControls.Palette security

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

def completeFamily (security order : ℕ) (mass : (Fin 3 → Palette security) → ℝ) : Family security order :=
  (∑ word, mass word) • (1 : Family security order) +
    ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).erase ∅,
      selectedFamily security order mass selected





def positiveFamily (security order : ℕ) (law : FiniteDist (Fin 3 → Palette security)) : Family security order :=
  completeFamily security order law.weight










end
end CurrentAFT.RootLegNormalized

end

section













/-! Pure-primary finite reciprocal for the complete actual unselected leg. -/

namespace CurrentAFT.RootLegReciprocal

open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls
  LocalReferenceEnergy ActualBlockFock RootIndependentBackground RootBackgroundPolynomial
  CycleRootExpansion RootTaggedLegHigher RootLegCoefficientFamily RootLegCoefficientNorm
  RootLegCoefficientLinear RootLegCoefficientBounds RootLegNormalized PrimaryOnlyFamily
  ControlCoordinates GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverse GradedInverseNorm
  BackgroundFamilies BackgroundRates BackgroundEvaluation
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw bodyReference rootReference
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def meanPositiveLaw (security : ℕ) : FiniteDist (Fin 3 → ActualControls.Palette security) :=
  (rootReference security).mix (fun root => primaryLawAt security root.val)

theorem meanPositiveLaw_weight (security : ℕ) :
    (meanPositiveLaw security).weight = rawMassLinear security (fun _ => 1) := by
  funext word
  simp only [meanPositiveLaw, FiniteDist.mix_weight, rawMassLinear,
    LinearMap.coe_mk, AddHom.coe_mk, mul_one]

theorem meanPositiveLaw_energy (security : ℕ) :
    primaryMassEnergy security (meanPositiveLaw security).weight ≤ 32 * pairBudget security := by
  rw [meanPositiveLaw_weight]
  apply (primaryMassEnergy_uniform_le security _).trans
  have h := rawMass_uniform_energy security (fun _ => 1)
  simp only [FiniteDist.l2Sq, one_pow, FiniteDist.expectation_const, mul_one] at h
  exact (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 8)).trans_eq (by ring)



def positive (security order : ℕ) : ActualFamily security order :=
  RootLegNormalized.positiveFamily security order (meanPositiveLaw security)

def reciprocal (security order : ℕ) : ActualFamily security order :=
  backgroundInverse (primaryLaw security) (bodyReference security) order (positive security order)

















def positiveCost (security : ℕ) : ℝ := 8 * normalizedFactor security * Real.sqrt (32 * pairBudget security)

theorem positive_defect_norm (security order : ℕ) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (positive security order - 1) ≤ positiveCost security := by
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hb : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  have hequal : positive security order - 1 = ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).erase ∅,
      selectedFamily security order (meanPositiveLaw security).weight selected := by
    unfold positive RootLegNormalized.positiveFamily RootLegNormalized.completeFamily
    rw [(meanPositiveLaw security).sum_one, one_smul]
    abel
  rw [hequal]
  apply (familyNorm_sum_le _ _ _ _ _ hp hb _ _).trans
  have hpoint (selected : Finset (Fin 3)) (hselected : selected ∈ (Finset.univ : Finset (Finset (Fin 3))).erase ∅) :
      familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
        (selectedFamily security order (meanPositiveLaw security).weight selected) ≤
          normalizedFactor security * Real.sqrt (32 * pairBudget security) := by
    have h := selectedFamily_norm security order (meanPositiveLaw security).weight selected
      (primaryFactor security) (bodyFactor security) hp
    have henergy := Real.sqrt_le_sqrt (meanPositiveLaw_energy security)
    have hpower : normalizedFactor security ^ selected.card ≤ normalizedFactor security := by
      have hnonempty := Finset.mem_erase.mp hselected |>.1
      have hcard : 1 ≤ selected.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hnonempty)
      simpa only [pow_one] using pow_le_pow_of_le_one (normalizedFactor_nonneg security) (normalizedFactor_le_one security) hcard
    apply h.trans
    calc
      _ = normalizedFactor security ^ selected.card * Real.sqrt (primaryMassEnergy security (meanPositiveLaw security).weight) := by
        unfold normalizedFactor
        rw [show (8 : ℝ) = 2 * 4 by norm_num]
        simp only [mul_pow, div_pow]
        ring
      _ ≤ _ := mul_le_mul hpower henergy (Real.sqrt_nonneg _) (normalizedFactor_nonneg security)
  apply (Finset.sum_le_sum hpoint).trans
  have hcard : (((Finset.univ : Finset (Finset (Fin 3))).erase ∅).card : ℝ) ≤ 8 := by
    exact_mod_cast (show ((Finset.univ : Finset (Finset (Fin 3))).erase ∅).card ≤ 8 by simp)
  rw [Finset.sum_const, nsmul_eq_mul]
  exact (mul_le_mul_of_nonneg_right hcard (mul_nonneg (normalizedFactor_nonneg security) (Real.sqrt_nonneg _))).trans_eq (by unfold positiveCost; ring)

def positiveConstant : ℝ := 1536 * Real.sqrt LocalRaisingBounds.pairConstant

theorem positiveCost_decay (security : ℕ) : positiveCost security ≤ positiveConstant / (Parameters.base security : ℝ) ^ 39 := by
  have hb := FirstResponse.base_pos security
  unfold positiveCost
  calc
    _ ≤ 8 * (32 / (Parameters.base security : ℝ) ^ 63) *
        (6 * Real.sqrt LocalRaisingBounds.pairConstant * (Parameters.base security : ℝ) ^ 24) := by
      gcongr
      · exact normalizedFactor_decay security
      · exact sqrtBudget_polynomial security
    _ = _ := by unfold positiveConstant; field_simp; ring

theorem reciprocal_norm_eventually (order : ℕ) :
    ∀ᶠ security : ℕ in atTop,
      familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
        (reciprocal security order) ≤ 2 := by
  obtain ⟨threshold, hthreshold⟩ := exists_nat_ge (2 * positiveConstant)
  filter_upwards [eventually_ge_atTop threshold] with security hsecurity
  have hb := FirstResponse.base_pos security
  have hbase : 2 * positiveConstant ≤ (Parameters.base security : ℝ) :=
    hthreshold.trans (Nat.cast_le.mpr (show threshold ≤ Parameters.base security by unfold Parameters.base; omega))
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (Parameters.base_ge_two security).trans' (by omega)
  have hpower : (Parameters.base security : ℝ) ≤ (Parameters.base security : ℝ) ^ 39 := by
    simpa only [pow_one] using pow_le_pow_right₀ hb1 (show 1 ≤ 39 by omega)
  have hhalf : positiveConstant / (Parameters.base security : ℝ) ^ 39 ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (pow_pos hb _)).mpr
    linarith
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hbdy : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  have hdefect : familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (1 - positive security order) ≤ (1 / 2 : ℝ) := by
    rw [show 1 - positive security order = -(positive security order - 1) by abel, familyNorm_neg]
    exact (positive_defect_norm security order).trans ((positiveCost_decay security).trans hhalf)
  exact (backgroundInverse_norm_le _ _ _ _ _ hp hbdy _ (1 / 2) (by norm_num) hdefect).trans_eq (by norm_num)

end
end CurrentAFT.RootLegReciprocal

end

section













/-! Actual normalized unselected root channels, with pure-primary reciprocals. -/

namespace CurrentAFT.RootUnselectedChannels

open AFT DiffuseProfiles ProposalPrimary ActualControls UniformBodyProfiles CycleRootExpansion
  RootTaggedLocal RootTaggedFamilies RootLegCoefficientFamily RootLegCoefficientLinear RootLegCoefficientBounds
  RootLegReciprocal PrimaryOnlyFamily ControlCoordinates GradedControlAlgebra
  GradedControlNorm GradedControlStability BackgroundFamilies BackgroundRates BackgroundEvaluation
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw bodyReference rootReference
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _





def singletonChannel (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ) :
    (Root security → ℝ) →ₗ[ℝ] ActualFamily security order where
  toFun input := rootFamilyLinear security order horder role queue input * RootMeanPrimary.positiveInverse security order horder role queue
  map_add' first second := by rw [map_add, add_mul]
  map_smul' scalar input := by simp only [map_smul, smul_mul_assoc, RingHom.id_apply]





theorem singletonChannel_norm (security order : ℕ) (horder : 1 ≤ order) (role : BodyRole) (queue : ℤ)
    (input : Root security → ℝ) : familyNorm (primaryLaw security) (bodyReference security) order
      (primaryFactor security) (bodyFactor security) (singletonChannel security order horder role queue input) ≤
        (2 * primaryFactor security * rootCost security) * Real.sqrt ((rootReference security).l2Sq input) := by
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hb : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  apply (familyNorm_product_le _ _ _ _ _ hp hb _ _).trans
  exact (mul_le_mul (rootFamily_norm security order horder role queue input)
    (RootMeanPrimary.positiveInverse_norm security order horder role queue)
    (familyNorm_nonneg _ _ _ _ _ hp hb _) (by positivity [rootCost_nonneg security])).trans_eq (by ring)



def legNumeratorLinear (security order : ℕ) (horder : 1 ≤ order) :
    (Root security → ℝ) →ₗ[ℝ] ActualFamily security order :=
  rootFamilyLinear security order horder .attachment 0 + rootHigherLinear security order

def legChannel (security order : ℕ) (horder : 1 ≤ order) :
    (Root security → ℝ) →ₗ[ℝ] ActualFamily security order where
  toFun input := legNumeratorLinear security order horder input * reciprocal security order
  map_add' first second := by rw [map_add, add_mul]
  map_smul' scalar input := by simp only [map_smul, smul_mul_assoc, RingHom.id_apply]





theorem legNumerator_norm (security order : ℕ) (horder : 1 ≤ order) (input : Root security → ℝ) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (legNumeratorLinear security order horder input) ≤
        (primaryFactor security * rootCost security + higherCost security) * Real.sqrt ((rootReference security).l2Sq input) := by
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hb : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  change familyNorm _ _ _ _ _ (_ + _) ≤ _
  exact (familyNorm_add_le _ _ _ _ _ hp hb _ _).trans
    ((add_le_add (rootFamily_norm security order horder .attachment 0 input)
      (rootHigher_norm security order input)).trans_eq (by ring))

theorem legChannel_norm_eventually (order : ℕ) (horder : 1 ≤ order) :
    ∀ᶠ security : ℕ in atTop, ∀ input : Root security → ℝ,
      familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
        (legChannel security order horder input) ≤
          2 * (primaryFactor security * rootCost security + higherCost security) * Real.sqrt ((rootReference security).l2Sq input) := by
  filter_upwards [reciprocal_norm_eventually order] with security hinverse input
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hb : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  apply (familyNorm_product_le _ _ _ _ _ hp hb _ _).trans
  have hcost : 0 ≤ higherCost security := by unfold higherCost; positivity
  exact (mul_le_mul (legNumerator_norm security order horder input) hinverse
    (familyNorm_nonneg _ _ _ _ _ hp hb _) (by positivity [rootCost_nonneg security])).trans_eq (by ring)

end
end CurrentAFT.RootUnselectedChannels

end

section















/-! Exact first/higher coefficient split of the actual root-centered unselected leg. -/
namespace CurrentAFT.RootLegFirstCoefficient
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct ControlNorm
  GradedControlAlgebra GradedControlNorm GradedControlStability RootLegCoefficientFamily RootLegCoefficientNorm
  RootLegNormalized RootLegReciprocal LocalRaisingFirst BackgroundFamilies LocalReferenceEnergy
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
abbrev Palette (security : ℕ) := ActualControls.Palette security

















def firstScore (security order : ℕ) (horder : 1 ≤ order) (mass : (Fin 3 → Palette security) → ℝ) : Palette security → ℝ :=
  primaryCoefficient (primaryLaw security) (bodyReference security) order horder (completeFamily security order mass)

theorem firstScore_centered (security order : ℕ) (horder : 1 ≤ order) (mass : (Fin 3 → Palette security) → ℝ) :
    (primaryLaw security).expectation (firstScore security order horder mass) = 0 := by
  let color : Palette security := ⟨0, (Parameters.modulus_spec security).2.pos⟩
  let kernel : canonicalKernels (primaryLaw security) (bodyReference security) 1 0 :=
    completeFamily security order mass (primaryArity order horder)
  have h := kernel.property.1 (0 : Fin 1) (fun _ => color) Fin.elim0
  have hupdate (input : Palette security) : Function.update (fun _ : Fin 1 => color) 0 input = (fun _ => input) := by
    funext index
    have hi := Fin.eq_zero index
    subst index
    exact Function.update_self _ _ _
  simp only [hupdate] at h
  exact h

def firstFamily (security order : ℕ) (horder : 1 ≤ order) (mass : (Fin 3 → Palette security) → ℝ) : Family security order :=
  primaryFamily (primaryLaw security) (bodyReference security) order horder (firstScore security order horder mass)
    (firstScore_centered security order horder mass)




















end
end CurrentAFT.RootLegFirstCoefficient

end

section













/-! One actual pure-primary normalized channel for every unselected physical block. -/

namespace CurrentAFT.RootUnselectedBlockChannel

open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls LocalReferenceEnergy
  ActualBlockFock UniformBodyProfiles CycleSelections CycleRootExpansion RootTaggedLocal
  RootTaggedFamilies RootUnselectedChannels RootLegCoefficientBounds RootLegCoefficientLinear
  RootLegFirstCoefficient PrimaryOnlyFamily BackgroundFamilies BackgroundRates BackgroundEvaluation
  ControlCoordinates GradedControlAlgebra GradedControlNorm
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize primaryLaw bodyReference rootReference
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def channel (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ) :
    BlockIndex security → ((Root security → ℝ) →ₗ[ℝ] ActualFamily security order)
  | .inl _ => legChannel security order horder
  | .inr (.inl _) => singletonChannel security order horder .free 0
  | .inr (.inr _) => singletonChannel security order horder .queue queue

def positivePolynomial (security : ℕ) (queue : ℤ) : BlockIndex security → MvPolynomial (ActualControls.Palette security) ℝ
  | .inl _ => LegPolynomialEvaluation.legGenerating security
  | .inr (.inl _) => singleGenerating (uniformReference security).weight (meanLaw security .free 0).weight
  | .inr (.inr _) => singleGenerating (uniformReference security).weight (meanLaw security .queue queue).weight

def numeratorPolynomial (security : ℕ) (queue : ℤ) (input : Root security → ℝ) :
    BlockIndex security → MvPolynomial (ActualControls.Palette security) ℝ
  | .inl _ => centeredGeneratingLinear (uniformReference security).weight (RootTaggedLegHigher.massLinear security input)
  | .inr (.inl _) => profileForm (rootMass security .free 0 input)
  | .inr (.inr _) => profileForm (rootMass security .queue queue input)





def channelConstant : ℝ := 8256 + 2 * RootLegCoefficientBounds.higherConstant

theorem channelConstant_nonneg : 0 ≤ channelConstant := by
  unfold channelConstant RootLegCoefficientBounds.higherConstant
  positivity

theorem raw_first_cost_decay (security : ℕ) :
    primaryFactor security * rootCost security ≤ 4128 / (Parameters.base security : ℝ) ^ 94 := by
  have hb := FirstResponse.base_pos security
  rw [primaryFactor_eq]
  exact (mul_le_mul_of_nonneg_left (rootCost_decay security) (by positivity)).trans_eq (by field_simp)

theorem combined_cost_decay (security : ℕ) :
    2 * (primaryFactor security * rootCost security + higherCost security) ≤
      channelConstant / (Parameters.base security : ℝ) ^ 94 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (Parameters.base_ge_two security).trans' (by omega)
  have hconstant : 0 ≤ RootLegCoefficientBounds.higherConstant := by
    unfold RootLegCoefficientBounds.higherConstant
    positivity
  have hhigher : higherCost security ≤ RootLegCoefficientBounds.higherConstant / (Parameters.base security : ℝ) ^ 94 :=
    (higherCost_decay security).trans (div_le_div_of_nonneg_left hconstant (pow_pos hb _) (pow_le_pow_right₀ hb1 (by omega)))
  exact (mul_le_mul_of_nonneg_left (add_le_add (raw_first_cost_decay security) hhigher) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by unfold channelConstant; ring)

theorem channel_norm_eventually (order : ℕ) (horder : 1 ≤ order) :
    ∀ᶠ security : ℕ in atTop, ∀ queue : ℤ, ∀ block : BlockIndex security, ∀ input : Root security → ℝ,
      familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
        (channel security order horder queue block input) ≤
          channelConstant / (Parameters.base security : ℝ) ^ 94 * Real.sqrt ((rootReference security).l2Sq input) := by
  filter_upwards [legChannel_norm_eventually order horder] with security hleg queue block input
  rcases block with leg | singleton
  · exact (hleg input).trans (mul_le_mul_of_nonneg_right (combined_cost_decay security) (Real.sqrt_nonneg _))
  · have hsingle : 2 * primaryFactor security * rootCost security ≤ channelConstant / (Parameters.base security : ℝ) ^ 94 := by
      have hh : 0 ≤ higherCost security := by unfold higherCost; positivity
      exact (by nlinarith : 2 * primaryFactor security * rootCost security ≤
        2 * (primaryFactor security * rootCost security + higherCost security)).trans (combined_cost_decay security)
    rcases singleton with center | point
    · exact (singletonChannel_norm security order horder .free 0 input).trans
        (mul_le_mul_of_nonneg_right hsingle (Real.sqrt_nonneg _))
    · exact (singletonChannel_norm security order horder .queue queue input).trans
        (mul_le_mul_of_nonneg_right hsingle (Real.sqrt_nonneg _))



end
end CurrentAFT.RootUnselectedBlockChannel

end

section















/-! # The real unselected channel in one-root, no-control grouped coordinates -/
namespace CurrentAFT.RootUnselectedGrouped
open AFT ActualBlockFock CycleRootExpansion RootTaggedFamilies RootUnselectedChannels
  RootLegCoefficientFamily RootLegCoefficientLinear GradedInverse LocalRaisingFirst
  ControlCoordinates GradedControlAlgebra BackgroundFamilies
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

abbrev Input (security : ℕ) := (Fin 1 → Root security) × Unit

def inputEquiv (security : ℕ) : Input security ≃ Root security where
  toFun sample := sample.1 0
  invFun root := (fun _ => root, ())
  left_inv := by
    rintro ⟨roots, control⟩
    apply Prod.ext
    · funext index
      rw [Fin.eq_zero index]
    · exact Subsingleton.elim _ _
  right_inv _ := rfl

def reference (security : ℕ) : FiniteDist (Input security) :=
  (FiniteDist.independent (fun _ : Fin 1 => rootReference security)).prod (FiniteDist.uniform Unit)

def extractLinear (security : ℕ) : (Input security → ℝ) →ₗ[ℝ] (Root security → ℝ) where
  toFun score root := score ((inputEquiv security).symm root)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem extract_energy (security : ℕ) (score : Input security → ℝ) :
    (rootReference security).l2Sq (extractLinear security score) = (reference security).l2Sq score := by
  unfold reference FiniteDist.l2Sq FiniteDist.expectation
  rw [← (inputEquiv security).symm.sum_comp]
  simp only [inputEquiv, Equiv.coe_fn_symm_mk, FiniteDist.prod_weight, FiniteDist.independent,
    Fin.prod_univ_one, FiniteDist.uniform_weight, Fintype.card_unit, Nat.cast_one, inv_one, mul_one,
    extractLinear, LinearMap.coe_mk, AddHom.coe_mk]

def channel (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ) (block : BlockIndex security) :
    (Input security → ℝ) →ₗ[ℝ] ActualFamily security order :=
  (RootUnselectedBlockChannel.channel security order horder queue block).comp (extractLinear security)

theorem channel_norm_eventually (order : ℕ) (horder : 1 ≤ order) :
    ∀ᶠ security : ℕ in atTop, ∀ queue : ℤ, ∀ block : BlockIndex security, ∀ score : Input security → ℝ,
      LocalRaisingBounds.coefficientNorm security order (channel security order horder queue block score) ≤
        RootUnselectedBlockChannel.channelConstant / (Parameters.base security : ℝ) ^ 94 *
          Real.sqrt ((reference security).l2Sq score) := by
  filter_upwards [RootUnselectedBlockChannel.channel_norm_eventually order horder] with security h queue block score
  have hh := h queue block (extractLinear security score)
  rw [extract_energy] at hh
  exact hh

theorem rootFamily_degree (security order : ℕ) (horder : 1 ≤ order)
    (role : UniformBodyProfiles.BodyRole) (queue : ℤ) (input : Root security → ℝ) :
    VanishesBelow (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) order 1
      (rootFamilyLinear security order horder role queue input) := by
  intro arity hsmall
  rw [rootFamilyLinear_apply]
  unfold primaryFamily
  rw [Pi.single_eq_of_ne]
  intro hequal
  have h := congrArg (fun item : TruncatedArity order => item.val.1.val + item.val.2.val) hequal
  change arity.val.1.val + arity.val.2.val = 1 + 0 at h
  omega

theorem raw_channel_degree (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (block : BlockIndex security) (input : Root security → ℝ) :
    VanishesBelow (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) order 1
      (RootUnselectedBlockChannel.channel security order horder queue block input) := by
  have hsingle (role : UniformBodyProfiles.BodyRole) (shift : ℤ) :
      VanishesBelow (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) order 1
        (singletonChannel security order horder role shift input) :=
    vanishesBelow_mul _ _ order 1 0 _ _ (rootFamily_degree security order horder role shift input)
      (vanishesBelow_zero _ _ _ _)
  rcases block with leg | singleton
  · change VanishesBelow _ _ _ _ (legNumeratorLinear security order horder input * _)
    apply vanishesBelow_mul _ _ order 1 0
    · apply vanishesBelow_add
      · exact rootFamily_degree security order horder .attachment 0 input
      · rw [rootHigherLinear_apply]
        intro arity hsmall
        exact rootHigherFamily_vanishesBelow security order input arity (by omega)
    · exact vanishesBelow_zero _ _ _ _
  · rcases singleton with center | point
    · exact hsingle .free 0
    · exact hsingle .queue queue

theorem channel_degree (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (block : BlockIndex security) (score : Input security → ℝ) :
    VanishesBelow (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) order 1
      (channel security order horder queue block score) :=
  raw_channel_degree security order horder queue block (extractLinear security score)





end
end CurrentAFT.RootUnselectedGrouped

end

section





















/-! # All actual normalized root/control channels at a fixed placement -/
namespace CurrentAFT.ActualRootGroupedChannel
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  GradedControlAlgebra ControlCoordinates LocalCoefficientFamily GradedInverse
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

abbrev Input {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged) :=
  (groupRootSlots selection tagged group → CycleRootExpansion.Root security) × ControlInput selection tagged group

def primaryFlags {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin r) (slot : Fin 2) : Bool :=
  decide (rootEmbedding selection tagged ⟨.inl (.inl index), slot⟩ ∈ tagged)

def ordinaryFlag {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin s) : Bool :=
  decide (rootEmbedding selection tagged ⟨.inl (.inr index), (0 : Fin 1)⟩ ∈ tagged)

def channel {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :
    (group : ActiveGroup selection tagged) → (Input selection tagged group → ℝ) →ₗ[ℝ] Family security order
  | .inl (.inl index) => RootPrimaryGroupedChannel.channel security order (primaryFlags selection tagged index)
  | .inl (.inr index) => RootOrdinaryGroupedChannel.channel security order horder (ordinaryFlag selection tagged index)
  | .inr index => RootUnselectedGrouped.channel security order horder queue index.val.val

def cost {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : ActiveGroup selection tagged → ℝ
  | .inl (.inl index) => RootPrimaryGroupedChannel.cost security (primaryFlags selection tagged index)
  | .inl (.inr index) => RootOrdinaryGroupedChannel.cost security (ordinaryFlag selection tagged index)
  | .inr _ => RootUnselectedBlockChannel.channelConstant / (Parameters.base security : ℝ) ^ 94

theorem cost_nonneg {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged) :
    0 ≤ cost selection tagged group := by
  rcases group with (primary | ordinary) | unselected
  · exact RootPrimaryGroupedChannel.cost_nonneg security _
  · change 0 ≤ RootOrdinaryGroupedChannel.cost security (ordinaryFlag selection tagged ordinary)
    unfold RootOrdinaryGroupedChannel.cost
    split_ifs
    · positivity
    · exact mul_nonneg (by norm_num) (RaisingPatternBudget.bodyFactor_pos security).le
  · exact div_nonneg RootUnselectedBlockChannel.channelConstant_nonneg (by positivity)

theorem channel_norm_eventually (order : ℕ) (horder : 1 ≤ order) :
    ∀ᶠ security : ℕ in atTop,
      2 * LocalRaisingBounds.positiveConstant ≤ (Parameters.base security : ℝ) →
      LocalRaisingBounds.raisingConstant ≤ (Parameters.base security : ℝ)^38 →
      ∀ r s, ∀ selection : Selection security r s, ∀ tagged : Finset (BlockIndex security),
      ∀ queue : ℤ, ∀ group : ActiveGroup selection tagged, ∀ score : Input selection tagged group → ℝ,
      LocalRaisingBounds.coefficientNorm security order (channel order horder queue selection tagged group score) ≤
        cost selection tagged group * Real.sqrt
          ((GroupedSourceNorm.groupReference (groupRootSlots selection tagged) (ControlInput selection tagged)
            (CycleRootExpansion.rootReference security) (controlReference selection tagged) group).l2Sq score) := by
  filter_upwards [RootUnselectedGrouped.channel_norm_eventually order horder] with security hunselected
  intro hlarge hsmall r s selection tagged queue group score
  rcases group with (primary | ordinary) | unselected
  · exact RootPrimaryGroupedChannel.channel_norm_cost security order horder hlarge hsmall _ score
  · exact RootOrdinaryGroupedChannel.channel_norm security order horder _ score
  · exact hunselected queue unselected.val.val score

theorem channel_degree {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (group : ActiveGroup selection tagged) (score : Input selection tagged group → ℝ) :
    VanishesBelow (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) order
      (PairedRootDegrees.minimumDegree selection tagged group) (channel order horder queue selection tagged group score) := by
  rcases group with (primary | ordinary) | unselected
  · have hbound := PairedRootDegrees.primary_minimumDegree_le_two selection tagged primary
    have hpositive : 1 ≤ PairedRootDegrees.minimumDegree selection tagged (.inl (.inl primary)) := le_max_left _ _
    by_cases hone : PairedRootDegrees.minimumDegree selection tagged (.inl (.inl primary)) = 1
    · rw [hone]
      exact RootPrimaryGroupedChannel.channel_vanishesBelow_one security order _ score
    · have htwo : PairedRootDegrees.minimumDegree selection tagged (.inl (.inl primary)) = 2 := by omega
      rw [htwo]
      apply RootPrimaryGroupedChannel.channel_vanishesBelow_two security order horder _ _ score
      apply decide_eq_true
      exact PairedRootDegrees.primary_minimumDegree_two_requires_attachment selection tagged primary htwo
  · rw [PairedRootDegrees.ordinary_minimumDegree]
    exact RootOrdinaryGroupedChannel.channel_vanishesBelow_one security order horder _ score
  · rw [PairedRootDegrees.kept_minimumDegree]
    exact RootUnselectedGrouped.channel_degree security order horder queue unselected.val.val score

end
end CurrentAFT.ActualRootGroupedChannel

end

section

















/-! # Finite-degree joint tensor synthesis of family-valued local channels -/
namespace CurrentAFT.GroupedFamilyTensor
open AFT ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GradedControlNorm
  GradedControlStability GradedInverseNorm BackgroundFamilies RaisingChannels GroupedKernelNorm GroupedKernelProduct
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _

variable {Primary Body Group : Type*} [Fintype Primary] [Fintype Body] [Fintype Group]
  (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
  {Input : Group → Type*} [∀ group, Fintype (Input group)]

def totalPrimary (pattern : Group → TruncatedArity order) : ℕ := ∑ group, (pattern group).val.1.val
def totalBody (pattern : Group → TruncatedArity order) : ℕ := ∑ group, (pattern group).val.2.val
abbrev PS (pattern : Group → TruncatedArity order) (group : Group) := Fin (pattern group).val.1.val
abbrev BS (pattern : Group → TruncatedArity order) (group : Group) := Fin (pattern group).val.2.val

def componentChannel
    (channels : ∀ group, (Input group → ℝ) →ₗ[ℝ] KernelFamily primary body order)
    (pattern : Group → TruncatedArity order) (group : Group) :=
  (fiberLinear primary body order (pattern group)).comp (channels group)

def patternKernel
    (channels : ∀ group, (Input group → ℝ) →ₗ[ℝ] KernelFamily primary body order)
    (pattern : Group → TruncatedArity order) (input : ((group : Group) → Input group) → ℝ) :
    canonicalKernels primary body (totalPrimary order pattern) (totalBody order pattern) :=
  canonicalTensor (PS order pattern) (BS order pattern) primary body
    (finiteSlotsEquiv (fun group => (pattern group).val.1.val))
    (finiteSlotsEquiv (fun group => (pattern group).val.2.val))
    (componentChannel primary body order channels pattern)
    (fun group score => (channels group score (pattern group)).property.1)
    (fun group score => (channels group score (pattern group)).property.2.1) input

def patternFamily
    (channels : ∀ group, (Input group → ℝ) →ₗ[ℝ] KernelFamily primary body order)
    (pattern : Group → TruncatedArity order) (input : ((group : Group) → Input group) → ℝ) : KernelFamily primary body order :=
  if hdegree : totalPrimary order pattern + totalBody order pattern ≤ order then
    embed primary body order hdegree (patternKernel primary body order channels pattern input)
  else 0

def response
    (channels : ∀ group, (Input group → ℝ) →ₗ[ℝ] KernelFamily primary body order)
    (input : ((group : Group) → Input group) → ℝ) : KernelFamily primary body order :=
  ∑ pattern, patternFamily primary body order channels pattern input

theorem patternKernel_norm (pf bf : ℝ) (hpf : 0 < pf) (hbf : 0 < bf)
    (reference : ∀ group, FiniteDist (Input group))
    (channels : ∀ group, (Input group → ℝ) →ₗ[ℝ] KernelFamily primary body order)
    (cost : Group → ℝ) (hcost : ∀ group, 0 ≤ cost group)
    (hchannels : ∀ group score, familyNorm primary body order pf bf (channels group score) ≤
      cost group * Real.sqrt ((reference group).l2Sq score))
    (pattern : Group → TruncatedArity order) (input : ((group : Group) → Input group) → ℝ) :
    gradeWeight pf bf (totalPrimary order pattern) (totalBody order pattern) *
      blockL2 primary body (patternKernel primary body order channels pattern input).val ≤
        (∏ group, cost group) * Real.sqrt ((FiniteDist.dependentIndependent reference).l2Sq input) := by
  let weight := fun group => gradeWeight pf bf (pattern group).val.1.val (pattern group).val.2.val
  have hw (group : Group) : 0 < weight group := by unfold weight gradeWeight; positivity
  let bounds := fun group => cost group / weight group
  have hchannel (group : Group) (score : Input group → ℝ) :
      (localReference (PS order pattern) (BS order pattern) primary body group).l2Sq
        (componentChannel primary body order channels pattern group score) ≤
          bounds group ^ 2 * (reference group).l2Sq score :=
    fiber_energy_le primary body order pf bf hpf hbf (reference group) (channels group) (cost group)
      (hchannels group) (pattern group) score
  have henergy := canonicalize_tensor_energy_le (PS order pattern) (BS order pattern) primary body
    (finiteSlotsEquiv (fun group => (pattern group).val.1.val))
    (finiteSlotsEquiv (fun group => (pattern group).val.2.val)) reference
    (componentChannel primary body order channels pattern) bounds hchannel input
  change blockEnergy primary body (patternKernel primary body order channels pattern input).val ≤ _ at henergy
  have hbounds : 0 ≤ ∏ group, bounds group := Finset.prod_nonneg (fun group _ => div_nonneg (hcost group) (hw group).le)
  have hsqrt := Real.sqrt_le_sqrt henergy
  rw [Finset.prod_pow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hbounds] at hsqrt
  apply (mul_le_mul_of_nonneg_left hsqrt
    (gradeWeight_nonneg pf bf hpf.le hbf.le _ _)).trans_eq
  have hweight : gradeWeight pf bf (totalPrimary order pattern) (totalBody order pattern) = ∏ group, weight group := by
    simp only [weight, gradeWeight, totalPrimary, totalBody, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hweight, ← mul_assoc]
  have hcancel : (∏ group, weight group) * (∏ group, bounds group) = ∏ group, cost group := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro group _
    dsimp only [bounds]
    field_simp [(hw group).ne']
  rw [hcancel]

theorem patternFamily_norm (pf bf : ℝ) (hpf : 0 < pf) (hbf : 0 < bf)
    (reference : ∀ group, FiniteDist (Input group))
    (channels : ∀ group, (Input group → ℝ) →ₗ[ℝ] KernelFamily primary body order)
    (cost : Group → ℝ) (hcost : ∀ group, 0 ≤ cost group)
    (hchannels : ∀ group score, familyNorm primary body order pf bf (channels group score) ≤
      cost group * Real.sqrt ((reference group).l2Sq score))
    (pattern : Group → TruncatedArity order) (input : ((group : Group) → Input group) → ℝ) :
    familyNorm primary body order pf bf (patternFamily primary body order channels pattern input) ≤
      (∏ group, cost group) * Real.sqrt ((FiniteDist.dependentIndependent reference).l2Sq input) := by
  unfold patternFamily
  split_ifs
  · rw [embed, familyNorm_single]
    exact patternKernel_norm primary body order pf bf hpf hbf reference channels cost hcost hchannels pattern input
  · rw [familyNorm_zero]
    exact mul_nonneg (Finset.prod_nonneg (fun group _ => hcost group)) (Real.sqrt_nonneg _)

/-- Only the finite output-degree patterns are summed by the triangle
inequality. The color, root, and control source spaces are tensorized as
one joint Hilbert input, so their cardinalities do not enter this bound. -/
theorem response_norm (pf bf : ℝ) (hpf : 0 < pf) (hbf : 0 < bf)
    (reference : ∀ group, FiniteDist (Input group))
    (channels : ∀ group, (Input group → ℝ) →ₗ[ℝ] KernelFamily primary body order)
    (cost : Group → ℝ) (hcost : ∀ group, 0 ≤ cost group)
    (hchannels : ∀ group score, familyNorm primary body order pf bf (channels group score) ≤
      cost group * Real.sqrt ((reference group).l2Sq score))
    (input : ((group : Group) → Input group) → ℝ) :
    familyNorm primary body order pf bf (response primary body order channels input) ≤
      (Fintype.card (TruncatedArity order) : ℝ) ^ Fintype.card Group *
        ((∏ group, cost group) * Real.sqrt ((FiniteDist.dependentIndependent reference).l2Sq input)) := by
  unfold response
  apply (familyNorm_sum_le primary body order pf bf hpf.le hbf.le Finset.univ _).trans
  calc
    _ ≤ ∑ _ : Group → TruncatedArity order,
        (∏ group, cost group) * Real.sqrt ((FiniteDist.dependentIndependent reference).l2Sq input) :=
      Finset.sum_le_sum (fun pattern _ => patternFamily_norm primary body order pf bf hpf hbf
        reference channels cost hcost hchannels pattern input)
    _ = _ := by simp [nsmul_eq_mul, Nat.cast_pow]

end
end CurrentAFT.GroupedFamilyTensor

end

section








/-! # Exact linear finite-sum formula for the mixed grouped tensor bundle -/
namespace CurrentAFT.GroupedKernelNorm
open AFT ControlCoordinates ControlProduct ControlNorm
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
local instance linearSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _

variable {Group Primary Body : Type*} [Fintype Group] [Fintype Primary] [Fintype Body]
  (PrimarySlots BodySlots : Group → Type*)
  [∀ group, Fintype (PrimarySlots group)] [∀ group, Fintype (BodySlots group)]
  {PrimaryTarget BodyTarget : Type*} [Fintype PrimaryTarget] [Fintype BodyTarget]

def canonicalizeLinear (primaryEquiv : Sigma PrimarySlots ≃ PrimaryTarget)
    (bodyEquiv : Sigma BodySlots ≃ BodyTarget) :
    (GroupWord (Primary := Primary) (Body := Body) PrimarySlots BodySlots → ℝ) →ₗ[ℝ]
      Kernel (Primary := Primary) (Body := Body) PrimaryTarget BodyTarget where
  toFun := canonicalize PrimarySlots BodySlots primaryEquiv bodyEquiv
  map_add' first second := by
    change symmetrizeLinear _ = symmetrizeLinear _ + symmetrizeLinear _
    rw [← map_add]
    rfl
  map_smul' scalar kernel := by
    change symmetrizeLinear _ = scalar • symmetrizeLinear _
    rw [← map_smul]
    rfl

variable {Input : Group → Type*} [∀ group, Fintype (Input group)]

omit [Fintype Primary] [Fintype Body] [∀ group, Fintype (PrimarySlots group)]
  [∀ group, Fintype (BodySlots group)] in
/-- Exact source-matrix expansion of the same joint tensor used for the
Hilbert estimate. No norm triangle is taken over these source coordinates. -/
theorem canonicalize_tensor_formula
    (primaryEquiv : Sigma PrimarySlots ≃ PrimaryTarget) (bodyEquiv : Sigma BodySlots ≃ BodyTarget)
    (channel : ∀ group, (Input group → ℝ) →ₗ[ℝ]
      (((PrimarySlots group → Primary) × (BodySlots group → Body)) → ℝ))
    (kernel : ((group : Group) → Input group) → ℝ) :
    canonicalize PrimarySlots BodySlots primaryEquiv bodyEquiv
        (DependentTensorChannel.apply channel kernel) =
      ∑ input, kernel input • canonicalize PrimarySlots BodySlots primaryEquiv bodyEquiv
        (fun word => ∏ group, channel group (Pi.single (input group) 1) (word group)) := by
  have hequal : DependentTensorChannel.apply channel kernel =
      ∑ input, kernel input • (fun word => ∏ group, channel group (Pi.single (input group) 1) (word group)) := by
    funext word
    simp only [DependentTensorChannel.apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change canonicalizeLinear PrimarySlots BodySlots primaryEquiv bodyEquiv _ = _
  rw [hequal, map_sum]
  simp only [map_smul]
  rfl

end
end CurrentAFT.GroupedKernelNorm

end

section

















/-! # Exact source formula and filtration of joint family tensor synthesis -/
namespace CurrentAFT.GroupedFamilyIdentity
open AFT ControlCoordinates ControlProduct GradedControlAlgebra GradedInverse
  GroupedKernelNorm GroupedKernelProduct GroupedFamilyTensor
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _

variable {Primary Body Group : Type*} [Fintype Primary] [Fintype Body] [Fintype Group]
  (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
  {Input : Group → Type*} [∀ group, Fintype (Input group)]
  (channels : ∀ group, (Input group → ℝ) →ₗ[ℝ] KernelFamily primary body order)

def columnKernel (pattern : Group → TruncatedArity order) (source : (group : Group) → Input group) :
    canonicalKernels primary body (totalPrimary order pattern) (totalBody order pattern) :=
  finiteProduct primary body (fun group => (pattern group).val.1.val) (fun group => (pattern group).val.2.val)
    (fun group => channels group (Pi.single (source group) 1) (pattern group))

theorem kernel_column_formula (pattern : Group → TruncatedArity order)
    (input : ((group : Group) → Input group) → ℝ) :
    patternKernel primary body order channels pattern input =
      ∑ source, input source • columnKernel primary body order channels pattern source := by
  apply Subtype.ext
  change canonicalize _ _ _ _
    (DependentTensorChannel.apply (componentChannel primary body order channels pattern) input) = _
  rw [canonicalize_tensor_formula]
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  apply Finset.sum_congr rfl
  intro source _
  congr 1
  rw [columnKernel, finiteProduct_val]
  rfl

omit [∀ group, Fintype (Input group)] in
theorem column_retained (pattern : Group → TruncatedArity order) (source : (group : Group) → Input group)
    (hdegree : totalPrimary order pattern + totalBody order pattern ≤ order) :
    (∏ group, (Pi.single (pattern group) (channels group (Pi.single (source group) 1) (pattern group)) :
      KernelFamily primary body order)) =
      embed primary body order hdegree (columnKernel primary body order channels pattern source) :=
  finite_product_embed primary body order (fun group => (pattern group).val.1.val)
    (fun group => (pattern group).val.2.val)
    (fun group => channels group (Pi.single (source group) 1) (pattern group)) hdegree
    (fun group => (pattern group).property)

omit [∀ group, Fintype (Input group)] in
theorem column_dropped (pattern : Group → TruncatedArity order) (source : (group : Group) → Input group)
    (hdegree : order < totalPrimary order pattern + totalBody order pattern) :
    (∏ group, (Pi.single (pattern group) (channels group (Pi.single (source group) 1) (pattern group)) :
      KernelFamily primary body order)) = 0 := by
  have h := GlobalRaising.vanishesBelow_prod primary body order (Finset.univ : Finset Group)
    (fun group => (pattern group).val.1.val + (pattern group).val.2.val)
    (fun group => Pi.single (pattern group) (channels group (Pi.single (source group) 1) (pattern group))) (by
      intro group _ output hsmall
      rw [Pi.single_eq_of_ne]
      intro hequal
      subst output
      omega)
  rw [Finset.sum_add_distrib] at h
  funext output
  exact h output (by have := output.property; unfold totalPrimary totalBody at hdegree; omega)

theorem family_column_formula (pattern : Group → TruncatedArity order)
    (input : ((group : Group) → Input group) → ℝ) :
    patternFamily primary body order channels pattern input =
      ∑ source, input source •
        ∏ group, (Pi.single (pattern group) (channels group (Pi.single (source group) 1) (pattern group)) :
          KernelFamily primary body order) := by
  unfold patternFamily
  split_ifs with hdegree
  · simp_rw [column_retained primary body order channels pattern _ hdegree]
    rw [kernel_column_formula]
    unfold embed
    funext output
    by_cases hequal : output = embedArity order (totalPrimary order pattern) (totalBody order pattern) hdegree
    · subst output; simp
    · simp [Pi.single_eq_of_ne hequal]
  · simp_rw [column_dropped primary body order channels pattern _ (Nat.lt_of_not_ge hdegree),
      smul_zero, Finset.sum_const_zero]

/-- The norm-controlled assembly is the original finite joint source sum
of local response products, as an equality of canonical coefficient data. -/
theorem response_eq (input : ((group : Group) → Input group) → ℝ) :
    response primary body order channels input =
      ∑ source, input source • ∏ group, channels group (Pi.single (source group) 1) := by
  unfold response
  simp_rw [family_column_formula]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  rw [← Finset.smul_sum, ← product_family_arity_expansion]

theorem response_vanishes (degree : Group → ℕ)
    (hchannel : ∀ group score, VanishesBelow primary body order (degree group) (channels group score))
    (input : ((group : Group) → Input group) → ℝ) :
    VanishesBelow primary body order (∑ group, degree group) (response primary body order channels input) := by
  rw [response_eq]
  apply LocalRaisingFirst.vanishesBelow_sum
  intro source _
  apply GlobalRaising.vanishesBelow_smul
  exact GlobalRaising.vanishesBelow_prod primary body order Finset.univ degree
    (fun group => channels group (Pi.single (source group) 1)) (fun group _ => hchannel group _)



end
end CurrentAFT.GroupedFamilyIdentity

end

section













namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.DependentTensorComposition
end CurrentAFT.DependentTensorComposition



/-! # Exact preprocessing of joint family-valued tensor inputs -/
namespace CurrentAFT.GroupedFamilyComposition
open AFT ControlCoordinates ControlProduct GradedControlAlgebra GroupedFamilyTensor
  GroupedKernelNorm
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _

variable {Primary Body Group : Type*} [Fintype Primary] [Fintype Body] [Fintype Group]
  (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
  {Input Middle : Group → Type*}
  [∀ group, Fintype (Input group)] [∀ group, Fintype (Middle group)]
  (preprocess : ∀ group, (Input group → ℝ) →ₗ[ℝ] (Middle group → ℝ))
  (channels : ∀ group, (Middle group → ℝ) →ₗ[ℝ] KernelFamily primary body order)







/-- The actual tensor response is linear in the entire joint input. -/
def responseLinear : (((group : Group) → Middle group) → ℝ) →ₗ[ℝ] KernelFamily primary body order where
  toFun := response primary body order channels
  map_add' first second := by
    simp only [GroupedFamilyIdentity.response_eq, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' scalar input := by
    simp only [GroupedFamilyIdentity.response_eq, Pi.smul_apply, smul_eq_mul, mul_smul,
      Finset.smul_sum, RingHom.id_apply]

end
end CurrentAFT.GroupedFamilyComposition

end

section















/-! # Actual finite root-subset response on canonical control data

The source is the real selected coefficient of the permuted closed cycle.
The local factors are the actual normalized primary, ordinary, and omitted
block channels. Large root subsets vanish as canonical coefficient data.
-/
namespace CurrentAFT.ActualRootResponse
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  GradedControlAlgebra ControlCoordinates LocalCoefficientFamily GradedInverse ControlNorm
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

def response {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s →ₗ[ℝ]
      Family security order :=
  (GroupedFamilyComposition.responseLinear (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security)
    order (ActualRootGroupedChannel.channel order horder queue selection tagged)).comp
      (jointInputLinear selection tagged layout)



theorem response_degree {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    VanishesBelow (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) order
      (∑ group, PairedRootDegrees.minimumDegree selection tagged group)
      (response order horder queue selection tagged layout kernel) :=
  GroupedFamilyIdentity.response_vanishes _ _ order
    (ActualRootGroupedChannel.channel order horder queue selection tagged) _
    (ActualRootGroupedChannel.channel_degree order horder queue selection tagged) _

theorem response_zero_of_order_lt_card {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) (hlarge : order < tagged.card) :
    response order horder queue selection tagged layout = 0 := by
  apply LinearMap.ext
  intro kernel
  funext arity
  have hcount := PairedRootDegrees.tags_le_degree selection tagged
  have harity := arity.property
  exact response_degree order horder queue selection tagged layout kernel arity (by omega)

/-- The true local Hilbert bounds are tensored against the true joint
root/control density; only finite degree-pattern counting appears. -/
theorem response_norm_eventually (order : ℕ) (horder : 1 ≤ order) :
    ∀ᶠ security : ℕ in atTop,
      2 * LocalRaisingBounds.positiveConstant ≤ (Parameters.base security : ℝ) →
      LocalRaisingBounds.raisingConstant ≤ (Parameters.base security : ℝ)^38 →
      ∀ r s, ∀ selection : Selection security r s, ∀ tagged : Finset (BlockIndex security),
      ∀ layout : BlockIndex security ≃ CycleRootExpansion.Vertex security, ∀ queue : ℤ,
      ∀ kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s,
      1 ≤ tagged.card → 2 * tagged.card ≤ Parameters.bodySize security →
      LocalRaisingBounds.coefficientNorm security order (response order horder queue selection tagged layout kernel) ≤
        (Fintype.card (TruncatedArity order) : ℝ) ^ Fintype.card (ActiveGroup selection tagged) *
          ((∏ group, ActualRootGroupedChannel.cost selection tagged group) *
            ((((2 * (tagged.card + 1) : ℕ) : ℝ)^tagged.card) *
              CycleSelections.currentRootTag security ^ tagged.card *
              blockL2 (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) kernel.val)) := by
  filter_upwards [ActualRootGroupedChannel.channel_norm_eventually order horder] with security hchannels
  intro hlarge hsmall r s selection tagged layout queue kernel hpositive hbody
  have h := GroupedFamilyTensor.response_norm (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security)
    order (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
    (RaisingPatternBudget.primaryFactor_pos security) (RaisingPatternBudget.bodyFactor_pos security)
    (GroupedSourceNorm.groupReference (groupRootSlots selection tagged) (ControlInput selection tagged)
      (CycleRootExpansion.rootReference security) (controlReference selection tagged))
    (ActualRootGroupedChannel.channel order horder queue selection tagged)
    (ActualRootGroupedChannel.cost selection tagged) (ActualRootGroupedChannel.cost_nonneg selection tagged)
    (hchannels hlarge hsmall r s selection tagged queue) (jointInput selection tagged layout kernel)
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun group _ => ActualRootGroupedChannel.cost_nonneg selection tagged group)
  exact jointInput_norm selection tagged layout kernel hpositive hbody

end
end CurrentAFT.ActualRootResponse

end

section













/-! # The complete finite root defect at one actual control selection -/
namespace CurrentAFT.ActualRootDefect
open AFT ActualBlockFock TaggedSelection PairedRootPlacement ControlCoordinates
  GradedControlAlgebra LocalCoefficientFamily GradedInverse
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

def selectedDefect {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s)
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s →ₗ[ℝ]
      Family security order :=
  ∑ tagged ∈ (Finset.univ : Finset (Finset (BlockIndex security))).filter (fun tagged => 2 ≤ tagged.card),
    ActualRootResponse.response order horder queue selection tagged layout

theorem selectedDefect_eq_small {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s)
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    selectedDefect order horder queue selection layout =
      ∑ tagged ∈ (Finset.univ : Finset (Finset (BlockIndex security))).filter
          (fun tagged => 2 ≤ tagged.card ∧ tagged.card ≤ order),
        ActualRootResponse.response order horder queue selection tagged layout := by
  unfold selectedDefect
  symm
  apply Finset.sum_subset
  · intro tagged htagged
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp htagged).2.1⟩
  · intro tagged htagged hnot
    have hlower := (Finset.mem_filter.mp htagged).2
    have hlarge : order < tagged.card := by
      have hn : ¬ (2 ≤ tagged.card ∧ tagged.card ≤ order) := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hnot
      omega
    exact ActualRootResponse.response_zero_of_order_lt_card order horder queue selection tagged layout hlarge





end
end CurrentAFT.ActualRootDefect

end

section



/-! # Nonnegative weighted subset sums without a population factor -/
namespace CurrentAFT.WeightedSubsetSum
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {Index : Type*} [DecidableEq Index]

theorem insert_recursion (pool : Finset Index) (point : Index) (hpoint : point ∉ pool)
    (activity : Index → ℝ) (degree : ℕ) :
    (∑ selected ∈ (insert point pool).powersetCard (degree + 1), ∏ index ∈ selected, activity index) =
      (∑ selected ∈ pool.powersetCard (degree + 1), ∏ index ∈ selected, activity index) +
        activity point * (∑ selected ∈ pool.powersetCard degree, ∏ index ∈ selected, activity index) := by
  have hnot (selected : Finset Index) (hselected : selected ⊆ pool) : point ∉ selected :=
    fun hmember => hpoint (hselected hmember)
  have hdisjoint : Disjoint (pool.powersetCard (degree + 1)) ((pool.powersetCard degree).image (insert point)) := by
    apply Finset.disjoint_left.mpr
    intro selected hselected himage
    obtain ⟨other, _, hequal⟩ := Finset.mem_image.mp himage
    apply hnot selected (Finset.mem_powersetCard.mp hselected).1
    rw [← hequal]
    exact Finset.mem_insert_self _ _
  rw [Finset.powersetCard_succ_insert hpoint, Finset.sum_union hdisjoint]
  congr 1
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro selected hselected
    exact Finset.prod_insert (hnot selected (Finset.mem_powersetCard.mp hselected).1)
  · intro first hfirst second hsecond hequal
    have h := congrArg (fun selected => selected.erase point) hequal
    simpa only [Finset.erase_insert (hnot first (Finset.mem_powersetCard.mp hfirst).1),
      Finset.erase_insert (hnot second (Finset.mem_powersetCard.mp hsecond).1)] using h

/-- Every unordered distinct subset is bounded by the complete ordered
power expansion. No number of vertices or choice of enumeration is lost. -/
theorem sum_le_power (pool : Finset Index) (activity : Index → ℝ)
    (hnonneg : ∀ index ∈ pool, 0 ≤ activity index) (degree : ℕ) :
    (∑ selected ∈ pool.powersetCard degree, ∏ index ∈ selected, activity index) ≤
      (∑ index ∈ pool, activity index) ^ degree := by
  induction pool using Finset.induction_on generalizing degree with
  | empty =>
    cases degree with
    | zero => simp
    | succ degree =>
      rw [Finset.powersetCard_eq_empty.mpr (by simp)]
      simp
  | @insert point pool hpoint ih =>
    have hp : 0 ≤ activity point := hnonneg point (Finset.mem_insert_self _ _)
    have hpool : ∀ index ∈ pool, 0 ≤ activity index :=
      fun index hindex => hnonneg index (Finset.mem_insert_of_mem hindex)
    have hsum : 0 ≤ ∑ index ∈ pool, activity index := Finset.sum_nonneg (fun index hindex => hpool index hindex)
    cases degree with
    | zero => simp
    | succ degree =>
      rw [insert_recursion pool point hpoint activity degree, Finset.sum_insert hpoint]
      calc
        _ ≤ (∑ index ∈ pool, activity index) ^ (degree + 1) +
            activity point * (∑ index ∈ pool, activity index) ^ degree :=
          add_le_add (ih hpool _) (mul_le_mul_of_nonneg_left (ih hpool _) hp)
        _ = (activity point + ∑ index ∈ pool, activity index) *
            (∑ index ∈ pool, activity index) ^ degree := by rw [pow_succ]; ring
        _ ≤ (activity point + ∑ index ∈ pool, activity index) *
            (activity point + ∑ index ∈ pool, activity index) ^ degree :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hsum (le_add_of_nonneg_left hp) degree) (add_nonneg hp hsum)
        _ = _ := by rw [pow_succ]; ring





/-- Grouping every retained subset by its exact cardinality gives the
fixed-order bound used by the complete root defect. -/
theorem sum_card_range_le (pool : Finset Index) (activity : Index → ℝ)
    (hnonneg : ∀ index ∈ pool, 0 ≤ activity index) (bound : ℕ → ℝ)
    (hbound : ∀ degree, 0 ≤ bound degree) (maximum : ℕ) :
    (∑ selected ∈ pool.powerset.filter (fun selected => 2 ≤ selected.card ∧ selected.card ≤ maximum),
      bound selected.card * ∏ index ∈ selected, activity index) ≤
      ∑ degree ∈ Finset.range (maximum + 1),
        if 2 ≤ degree then bound degree * (∑ index ∈ pool, activity index) ^ degree else 0 := by
  have hfiber (degree : ℕ) :
      (∑ selected ∈ pool.powersetCard degree,
        if 2 ≤ selected.card ∧ selected.card ≤ maximum then bound selected.card *
          (∏ index ∈ selected, activity index) else 0) =
      if 2 ≤ degree ∧ degree ≤ maximum then bound degree *
        (∑ selected ∈ pool.powersetCard degree, ∏ index ∈ selected, activity index) else 0 := by
    calc
      _ = ∑ selected ∈ pool.powersetCard degree,
          if 2 ≤ degree ∧ degree ≤ maximum then bound degree * (∏ index ∈ selected, activity index) else 0 := by
        apply Finset.sum_congr rfl
        intro selected hselected
        rw [(Finset.mem_powersetCard.mp hselected).2]
      _ = _ := by
        by_cases hcondition : 2 ≤ degree ∧ degree ≤ maximum
        · simp only [if_pos hcondition, Finset.mul_sum]
        · simp only [if_neg hcondition, Finset.sum_const_zero]
  rw [Finset.sum_filter, Finset.sum_powerset]
  simp_rw [hfiber]
  calc
    _ ≤ ∑ degree ∈ Finset.range (pool.card + 1),
        if 2 ≤ degree ∧ degree ≤ maximum then bound degree *
          (∑ index ∈ pool, activity index) ^ degree else 0 := by
      apply Finset.sum_le_sum
      intro degree _
      split_ifs
      · exact mul_le_mul_of_nonneg_left (sum_le_power pool activity hnonneg degree) (hbound degree)
      · exact le_rfl
    _ = ∑ degree ∈ (Finset.range (pool.card + 1)).filter (fun degree => degree ≤ maximum),
        if 2 ≤ degree then bound degree * (∑ index ∈ pool, activity index) ^ degree else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro degree _
      split_ifs <;> simp_all
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (by
      intro degree hdegree
      have h := (Finset.mem_filter.mp hdegree).2
      exact Finset.mem_range.mpr (by omega)) (fun degree _ _ => by
        split_ifs
        · exact mul_nonneg (hbound degree) (pow_nonneg (Finset.sum_nonneg hnonneg) _)
        · exact le_rfl)

end
end CurrentAFT.WeightedSubsetSum

end

section















/-! # Actual selected and unselected root activity at the current parameters -/
namespace CurrentAFT.RootActivityBudget
open AFT ActualBlockFock TaggedSelection BackgroundRates CycleSelections
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance finDecEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  ordinaryPool

def commonConstant : ℝ := max 1 (max RootTaggedSelectedNorm.selectedConstant
  (max (48 * Real.sqrt 131074) RootUnselectedBlockChannel.channelConstant))

theorem commonConstant_one : 1 ≤ commonConstant := le_max_left _ _
theorem commonConstant_primary : RootTaggedSelectedNorm.selectedConstant ≤ commonConstant :=
  (le_max_left _ _).trans (le_max_right _ _)
theorem commonConstant_ordinary : 48 * Real.sqrt 131074 ≤ commonConstant :=
  (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
theorem commonConstant_background : RootUnselectedBlockChannel.channelConstant ≤ commonConstant :=
  (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

def selectedActivity (security : ℕ) (constant : ℝ) : ℝ := constant * (Parameters.base security : ℝ) ^ 17
def backgroundActivity (security : ℕ) (constant : ℝ) : ℝ := constant / (Parameters.base security : ℝ) ^ 94
def activity {security r s : ℕ} (selection : Selection security r s) (constant : ℝ)
    (vertex : BlockIndex security) : ℝ :=
  if vertex ∈ selection.removed then selectedActivity security constant else backgroundActivity security constant

theorem selectedActivity_one (security : ℕ) (constant : ℝ) (hone : 1 ≤ constant) :
    1 ≤ selectedActivity security constant := by
  have hb : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (Parameters.base_ge_two security).trans' (by norm_num)
  exact (one_le_mul_of_one_le_of_one_le hone (one_le_pow₀ hb))

theorem bodyFactor_lower (security : ℕ) :
    1 / (Real.sqrt 131074 * (Parameters.base security : ℝ) ^ 80) ≤ bodyFactor security := by
  have hb : (0 : ℝ) < Parameters.base security := by exact_mod_cast Parameters.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (Parameters.base_ge_two security).trans' (by norm_num)
  have hpool : (ordinaryPool security : ℝ) ≤ 131074 * (Parameters.base security : ℝ) ^ 160 := by
    have hnat : ordinaryPool security ≤ Parameters.dimension security := by
      unfold ordinaryPool Parameters.dimension
      omega
    exact_mod_cast hnat.trans (Parameters.dimension_bounds security).2
  have hpoolPos : (0 : ℝ) < ordinaryPool security := by exact_mod_cast ordinaryPool_pos security
  have hsqrt : Real.sqrt (ordinaryPool security : ℝ) ≤ Real.sqrt 131074 * (Parameters.base security : ℝ) ^ 80 := by
    apply (Real.sqrt_le_sqrt hpool).trans_eq
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 131074),
      show (Parameters.base security : ℝ) ^ 160 = ((Parameters.base security : ℝ) ^ 80) ^ 2 by rw [← pow_mul],
      Real.sqrt_sq (pow_nonneg hb.le _)]
  have hradius : 1 ≤ radius security := Real.one_le_rpow hb1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
  calc
    _ ≤ 1 / Real.sqrt (ordinaryPool security : ℝ) := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hpoolPos) hsqrt
    _ ≤ radius security / Real.sqrt (ordinaryPool security : ℝ) :=
      div_le_div_of_nonneg_right hradius (Real.sqrt_nonneg _)
    _ = _ := rfl

theorem primary_tag_cost_relative (security : ℕ) (constant : ℝ)
    (hconstant : RootTaggedSelectedNorm.selectedConstant ≤ constant) :
    RootTaggedSelectedNorm.selectedConstant / (Parameters.base security : ℝ) ^ 47 ≤
      primaryFactor security * selectedActivity security constant := by
  have hb : (0 : ℝ) < Parameters.base security := by exact_mod_cast Parameters.base_pos security
  rw [primaryFactor_eq, selectedActivity]
  calc
    _ ≤ constant / (Parameters.base security : ℝ) ^ 47 := div_le_div_of_nonneg_right hconstant (pow_nonneg hb.le _)
    _ = _ := by field_simp

theorem ordinary_tag_cost_relative (security : ℕ) (constant : ℝ)
    (hconstant : 48 * Real.sqrt 131074 ≤ constant) :
    48 / (Parameters.base security : ℝ) ^ 63 ≤ bodyFactor security * selectedActivity security constant := by
  have hb : (0 : ℝ) < Parameters.base security := by exact_mod_cast Parameters.base_pos security
  have hsqrt : (0 : ℝ) < Real.sqrt 131074 := Real.sqrt_pos.mpr (by norm_num)
  calc
    _ = (1 / (Real.sqrt 131074 * (Parameters.base security : ℝ) ^ 80)) *
        ((48 * Real.sqrt 131074) * (Parameters.base security : ℝ) ^ 17) := by field_simp
    _ ≤ bodyFactor security * ((48 * Real.sqrt 131074) * (Parameters.base security : ℝ) ^ 17) :=
      mul_le_mul_of_nonneg_right (bodyFactor_lower security) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hconstant (pow_nonneg hb.le _))
      (RaisingPatternBudget.bodyFactor_pos security).le

theorem activity_nonneg {security r s : ℕ} (selection : Selection security r s) (constant : ℝ)
    (hconstant : 0 ≤ constant) (vertex : BlockIndex security) : 0 ≤ activity selection constant vertex := by
  unfold activity selectedActivity backgroundActivity
  split_ifs <;> positivity

theorem block_card (security : ℕ) : Fintype.card (BlockIndex security) = Parameters.bodySize security := by
  have hroom := ProposalPrimary.population_room security
  simp only [BlockIndex, Fintype.card_sum, Fintype.card_fin]
  unfold centerCount
  omega

theorem sum_activity_le {security r s : ℕ} (selection : Selection security r s) (constant : ℝ)
    (hconstant : 0 ≤ constant) :
    (∑ vertex, activity selection constant vertex) ≤
      ((2 * r + s : ℕ) : ℝ) * selectedActivity security constant +
        (Parameters.bodySize security : ℝ) * backgroundActivity security constant := by
  have hb : 0 ≤ backgroundActivity security constant := by unfold backgroundActivity; positivity
  have hpoint (vertex : BlockIndex security) : activity selection constant vertex ≤
      (if vertex ∈ selection.removed then selectedActivity security constant else 0) + backgroundActivity security constant := by
    unfold activity
    split_ifs <;> linarith
  have h := Finset.sum_le_sum (fun vertex (_ : vertex ∈ (Finset.univ : Finset (BlockIndex security))) => hpoint vertex)
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const_zero,
    add_zero, Finset.sum_const, Finset.card_univ, block_card, Selection.removed_card, nsmul_eq_mul] using h

theorem sum_activity_tag_le {security r s : ℕ} (selection : Selection security r s) (constant : ℝ)
    (hconstant : 0 ≤ constant) :
    (∑ vertex, activity selection constant vertex) * currentRootTag security ≤
      constant * (((2 * r + s : ℕ) : ℝ) + 131074) / (Parameters.base security : ℝ) ^ 13 := by
  have hb : (0 : ℝ) < Parameters.base security := by exact_mod_cast Parameters.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (Parameters.base_ge_two security).trans' (by norm_num)
  have hbody : (Parameters.bodySize security : ℝ) ≤ 131074 * (Parameters.base security : ℝ) ^ 160 := by
    have hnat : Parameters.bodySize security ≤ Parameters.dimension security := by unfold Parameters.dimension; omega
    exact_mod_cast hnat.trans (Parameters.dimension_bounds security).2
  have hpower : (Parameters.base security : ℝ) ^ 17 ≤ (Parameters.base security : ℝ) ^ 66 :=
    pow_le_pow_right₀ hb1 (by omega)
  have hbackground : (131074 * (Parameters.base security : ℝ) ^ 160) *
      (constant / (Parameters.base security : ℝ) ^ 94) =
      131074 * constant * (Parameters.base security : ℝ) ^ 66 := by field_simp
  have hsum : (∑ vertex, activity selection constant vertex) ≤
      constant * (((2 * r + s : ℕ) : ℝ) + 131074) * (Parameters.base security : ℝ) ^ 66 := by
    calc
      _ ≤ (((2 * r + s : ℕ) : ℝ) * (constant * (Parameters.base security : ℝ) ^ 17)) +
          (Parameters.bodySize security : ℝ) * (constant / (Parameters.base security : ℝ) ^ 94) :=
        sum_activity_le selection constant hconstant
      _ ≤ (((2 * r + s : ℕ) : ℝ) * (constant * (Parameters.base security : ℝ) ^ 66)) +
          (131074 * (Parameters.base security : ℝ) ^ 160) * (constant / (Parameters.base security : ℝ) ^ 94) :=
        add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpower hconstant) (Nat.cast_nonneg _))
          (mul_le_mul_of_nonneg_right hbody (div_nonneg hconstant (pow_nonneg hb.le _)))
      _ = _ := by rw [hbackground]; ring
  have htag : 0 ≤ currentRootTag security := by rw [currentRootTag_eq]; positivity
  calc
    _ ≤ (constant * (((2 * r + s : ℕ) : ℝ) + 131074) * (Parameters.base security : ℝ) ^ 66) * currentRootTag security :=
      mul_le_mul_of_nonneg_right hsum htag
    _ = _ := by rw [currentRootTag_eq]; field_simp







end
end CurrentAFT.RootActivityBudget

end

section













/-! # The actual grouped channel cost is a product of vertex activities -/
namespace CurrentAFT.RootGroupCostBudget
open AFT ActualBlockFock TaggedSelection PairedRootPlacement RootActivityBudget BackgroundRates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance finDecEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance sumDecEq {First Second : Type*} : DecidableEq (First ⊕ Second) := Classical.decEq _
local instance sigmaDecEq {Index : Type*} {Fiber : Index → Type*} : DecidableEq (Sigma Fiber) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def taggedActivity {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (constant : ℝ) (vertex : BlockIndex security) : ℝ :=
  if vertex ∈ tagged then activity selection constant vertex else 1

def leadingCost {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : ActiveGroup selection tagged → ℝ
  | .inl (.inl _) => 2 * primaryFactor security
  | .inl (.inr _) => 2 * bodyFactor security
  | .inr _ => 1

theorem primary_cost_activity (security : ℕ) (constant : ℝ) (hconstant : commonConstant ≤ constant)
    (flags : Fin 2 → Bool) :
    RootPrimaryGroupedChannel.cost security flags ≤ (2 * primaryFactor security) *
      ∏ slot : Fin 2, if flags slot then selectedActivity security constant else 1 := by
  have hone := selectedActivity_one security constant (commonConstant_one.trans hconstant)
  have hprimary := (RaisingPatternBudget.primaryFactor_pos security).le
  have hrelative := primary_tag_cost_relative security constant (commonConstant_primary.trans hconstant)
  have hnonneg : 0 ≤ selectedActivity security constant := by linarith
  have hscaled : primaryFactor security * selectedActivity security constant ≤
      primaryFactor security * (selectedActivity security constant * selectedActivity security constant) :=
    mul_le_mul_of_nonneg_left (by nlinarith : selectedActivity security constant ≤
      selectedActivity security constant * selectedActivity security constant) hprimary
  rw [Fin.prod_univ_two]
  cases hfirst : flags 0 <;> cases hsecond : flags 1 <;>
    simp only [RootPrimaryGroupedChannel.cost, hfirst, hsecond, Bool.or_false,
      Bool.or_true, Bool.false_eq_true, if_false, if_true, mul_one, one_mul]
  all_goals nlinarith [mul_nonneg hprimary hnonneg,
    mul_nonneg hprimary (mul_nonneg hnonneg hnonneg)]

theorem ordinary_cost_activity (security : ℕ) (constant : ℝ) (hconstant : commonConstant ≤ constant)
    (flag : Bool) :
    RootOrdinaryGroupedChannel.cost security flag ≤ (2 * bodyFactor security) *
      (if flag then selectedActivity security constant else 1) := by
  have hrelative := ordinary_tag_cost_relative security constant (commonConstant_ordinary.trans hconstant)
  have hone := selectedActivity_one security constant (commonConstant_one.trans hconstant)
  have hbody := (RaisingPatternBudget.bodyFactor_pos security).le
  cases flag <;> simp only [RootOrdinaryGroupedChannel.cost, Bool.false_eq_true, if_false, if_true, mul_one]
  all_goals nlinarith [mul_nonneg hbody (by linarith : 0 ≤ selectedActivity security constant)]

theorem selected_root_removed {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (role : Fin r ⊕ Fin s) (slot : selectedRootSlots r s role) :
    rootEmbedding selection tagged ⟨.inl role, slot⟩ ∈ selection.removed := by
  have hequal : rootEmbedding selection tagged ⟨.inl role, slot⟩ =
      selection.removedEmbedding (selectedRootEquiv r s ⟨role, slot⟩) := rfl
  rw [hequal]
  exact Finset.mem_map.mpr ⟨_, Finset.mem_univ _, rfl⟩

theorem group_cost_le {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (constant : ℝ) (hconstant : commonConstant ≤ constant)
    (group : ActiveGroup selection tagged) :
    ActualRootGroupedChannel.cost selection tagged group ≤ leadingCost selection tagged group *
      ∏ slot : groupRootSlots selection tagged group,
        taggedActivity selection tagged constant (rootEmbedding selection tagged ⟨group, slot⟩) := by
  rcases group with (primary | ordinary) | kept
  · have hfactor (slot : Fin 2) : taggedActivity selection tagged constant
        (rootEmbedding selection tagged ⟨.inl (.inl primary), slot⟩) =
        if ActualRootGroupedChannel.primaryFlags selection tagged primary slot then selectedActivity security constant else 1 := by
      unfold taggedActivity
      rw [activity, if_pos (selected_root_removed selection tagged (.inl primary) slot)]
      simp only [ActualRootGroupedChannel.primaryFlags, decide_eq_true_eq]
    change RootPrimaryGroupedChannel.cost security (ActualRootGroupedChannel.primaryFlags selection tagged primary) ≤
      (2 * primaryFactor security) * ∏ slot : Fin 2, _
    simp_rw [hfactor]
    exact primary_cost_activity security constant hconstant _
  · have hfactor : taggedActivity selection tagged constant
        (rootEmbedding selection tagged ⟨.inl (.inr ordinary), (0 : Fin 1)⟩) =
        if ActualRootGroupedChannel.ordinaryFlag selection tagged ordinary then selectedActivity security constant else 1 := by
      unfold taggedActivity
      rw [activity, if_pos (selected_root_removed selection tagged (.inr ordinary) (0 : Fin 1))]
      simp only [ActualRootGroupedChannel.ordinaryFlag, decide_eq_true_eq]
    change RootOrdinaryGroupedChannel.cost security (ActualRootGroupedChannel.ordinaryFlag selection tagged ordinary) ≤
      (2 * bodyFactor security) * ∏ slot : Fin 1, _
    rw [Fin.prod_univ_one, hfactor]
    exact ordinary_cost_activity security constant hconstant _
  · change RootUnselectedBlockChannel.channelConstant / (Parameters.base security : ℝ) ^ 94 ≤
      1 * ∏ slot : Fin 1, _
    rw [Fin.prod_univ_one, one_mul]
    change RootUnselectedBlockChannel.channelConstant / (Parameters.base security : ℝ) ^ 94 ≤
      taggedActivity selection tagged constant kept.val.val
    have hnot : kept.val.val ∉ selection.removed := by
      rw [← selection.removed_complement]
      simp only [OmittedBlockMean.removed, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      exact kept.val.property
    unfold taggedActivity activity
    rw [if_pos kept.property, if_neg hnot]
    exact div_le_div_of_nonneg_right (commonConstant_background.trans hconstant) (by positivity)

theorem tagged_root_product {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (constant : ℝ) :
    (∏ group : ActiveGroup selection tagged, ∏ slot : groupRootSlots selection tagged group,
      taggedActivity selection tagged constant (rootEmbedding selection tagged ⟨group, slot⟩)) =
      ∏ vertex ∈ tagged, activity selection constant vertex := by
  have hsigma := Fintype.prod_sigma (fun point : Sigma (groupRootSlots selection tagged) =>
    taggedActivity selection tagged constant (rootEmbedding selection tagged point))
  apply Eq.trans hsigma.symm
  unfold taggedActivity
  rw [← Finset.prod_filter]
  apply Finset.prod_bij (fun source _ => rootEmbedding selection tagged source)
  · intro source hsource
    exact (Finset.mem_filter.mp hsource).2
  · intro first _ second _ hequal
    exact (rootEmbedding selection tagged).injective hequal
  · intro vertex hvertex
    refine ⟨tagEmbedding selection tagged ⟨vertex, hvertex⟩, ?_, tag_image selection tagged ⟨vertex, hvertex⟩⟩
    simp only [Finset.mem_filter, Finset.mem_univ, tag_image, true_and]
    exact hvertex
  · intro source _
    rfl

theorem leading_cost_product {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    (∏ group : ActiveGroup selection tagged, leadingCost selection tagged group) =
      (2 : ℝ) ^ (r + s) * ControlNorm.gradeWeight (primaryFactor security) (bodyFactor security) r s := by
  simp only [Fintype.prod_sum_type, leadingCost, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    mul_pow, pow_add, ControlNorm.gradeWeight]
  ring

/-- Every actual grouped channel contributes its sharp leading pool factor
and at most one activity for each tagged physical root vertex. -/
theorem product_cost_le {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (constant : ℝ) (hconstant : commonConstant ≤ constant) :
    (∏ group : ActiveGroup selection tagged, ActualRootGroupedChannel.cost selection tagged group) ≤
      (2 : ℝ) ^ (r + s) * ControlNorm.gradeWeight (primaryFactor security) (bodyFactor security) r s *
        ∏ vertex ∈ tagged, activity selection constant vertex := by
  apply (Finset.prod_le_prod (fun group _ => ActualRootGroupedChannel.cost_nonneg selection tagged group)
    (fun group _ => group_cost_le selection tagged constant hconstant group)).trans_eq
  rw [Finset.prod_mul_distrib, leading_cost_product, tagged_root_product]

end
end CurrentAFT.RootGroupCostBudget

end

section




/-! # Fixed-order summation of all genuine root subsets -/
namespace CurrentAFT.RootSubsetNormSum
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000

theorem power_decay (base constant : ℝ) (hbase : 1 ≤ base) (hconstant : 1 ≤ constant)
    (order degree : ℕ) (hlower : 2 ≤ degree) (hupper : degree ≤ order) :
    (constant / base ^ 13) ^ degree ≤ constant ^ order / base ^ 26 := by
  have hb : 0 < base := lt_of_lt_of_le zero_lt_one hbase
  rw [div_pow, ← pow_mul]
  apply (div_le_div_of_nonneg_left (pow_nonneg (zero_le_one.trans hconstant) _)
    (pow_pos hb _) (pow_le_pow_right₀ hbase (by omega : 26 ≤ 13 * degree))).trans
  exact div_le_div_of_nonneg_right (pow_le_pow_right₀ hconstant hupper) (pow_nonneg hb.le _)

theorem subset_sum_decay {Index : Type*} [DecidableEq Index]
    (pool : Finset Index) (activity : Index → ℝ) (hnonneg : ∀ index ∈ pool, 0 ≤ activity index)
    (base constant : ℝ) (hbase : 1 ≤ base) (hconstant : 1 ≤ constant)
    (hsum : (∑ index ∈ pool, activity index) ≤ constant / base ^ 13) (order : ℕ) :
    (∑ selected ∈ pool.powerset.filter (fun selected => 2 ≤ selected.card ∧ selected.card ≤ order),
      ∏ index ∈ selected, activity index) ≤ ((order + 1 : ℕ) : ℝ) * constant ^ order / base ^ 26 := by
  have h := WeightedSubsetSum.sum_card_range_le pool activity hnonneg (fun _ => 1)
    (fun _ => zero_le_one) order
  simp only [one_mul] at h
  apply h.trans
  calc
    _ ≤ ∑ _degree ∈ Finset.range (order + 1), constant ^ order / base ^ 26 := by
      apply Finset.sum_le_sum
      intro degree hdegree
      split_ifs with hlower
      · exact (pow_le_pow_left₀ (Finset.sum_nonneg hnonneg) hsum degree).trans
          (power_decay base constant hbase hconstant order degree hlower
            (by have := Finset.mem_range.mp hdegree; omega))
      · exact div_nonneg (pow_nonneg (zero_le_one.trans hconstant) _) (pow_nonneg (zero_le_one.trans hbase) _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end
end CurrentAFT.RootSubsetNormSum

end

section

















/-! # Stability of the complete root defect under actual control selection -/
namespace CurrentAFT.ActualRootDefectNorm
open AFT ActualBlockFock TaggedSelection PairedRootPlacement ControlCoordinates
  ControlNorm GradedControlAlgebra LocalCoefficientFamily LocalRaisingBounds
  RootActivityBudget GradedInverseNorm
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
local instance finDecEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance sumDecEq {First Second : Type*} : DecidableEq (First ⊕ Second) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

def degreeConstant (order : ℕ) : ℝ :=
  (Fintype.card (TruncatedArity order) : ℝ) ^ (2 * order) *
    (((2 * (order + 1) : ℕ) : ℝ) ^ order) * 2 ^ order

def activityConstant (order : ℕ) : ℝ := commonConstant * (((2 * order : ℕ) : ℝ) + 131074)

def stabilityConstant (order : ℕ) : ℝ :=
  degreeConstant order * ((order + 1 : ℕ) : ℝ) * activityConstant order ^ order

theorem degreeConstant_nonneg (order : ℕ) : 0 ≤ degreeConstant order := by
  unfold degreeConstant
  positivity

theorem activityConstant_one (order : ℕ) : 1 ≤ activityConstant order :=
  one_le_mul_of_one_le_of_one_le commonConstant_one (by have := Nat.cast_nonneg (α := ℝ) (2 * order); linarith)

theorem stabilityConstant_nonneg (order : ℕ) : 0 ≤ stabilityConstant order := by
  exact mul_nonneg (mul_nonneg (degreeConstant_nonneg order) (Nat.cast_nonneg _))
    (pow_nonneg (zero_le_one.trans (activityConstant_one order)) _)

theorem response_norm_activity_eventually (order : ℕ) (horder : 1 ≤ order) :
    ∀ᶠ security : ℕ in atTop,
      2 * positiveConstant ≤ (Parameters.base security : ℝ) →
      raisingConstant ≤ (Parameters.base security : ℝ)^38 →
      ∀ r s, r + s ≤ order → ∀ selection : Selection security r s,
      ∀ tagged : Finset (BlockIndex security), 1 ≤ tagged.card → tagged.card ≤ order →
      2 * tagged.card ≤ Parameters.bodySize security →
      ∀ layout : BlockIndex security ≃ CycleRootExpansion.Vertex security, ∀ queue : ℤ,
      ∀ kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s,
      coefficientNorm security order (ActualRootResponse.response order horder queue selection tagged layout kernel) ≤
        degreeConstant order *
          (gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) r s *
            blockL2 (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) kernel.val) *
          ∏ vertex ∈ tagged, activity selection commonConstant vertex * CycleSelections.currentRootTag security := by
  filter_upwards [ActualRootResponse.response_norm_eventually order horder] with security hresponse
  intro hlarge hsmall r s hdegree selection tagged hpositive hcard hbody layout queue kernel
  have hp := (RaisingPatternBudget.primaryFactor_pos security).le
  have hb := (RaisingPatternBudget.bodyFactor_pos security).le
  have ha := activity_nonneg selection commonConstant (zero_le_one.trans commonConstant_one)
  have ht : 0 ≤ CycleSelections.currentRootTag security := by rw [CycleSelections.currentRootTag_eq]; positivity
  have hc : 1 ≤ (Fintype.card (TruncatedArity order) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (show Nonempty (TruncatedArity order) from ⟨zeroArity order⟩)
  have hg : Fintype.card (ActiveGroup selection tagged) ≤ 2 * order := by
    have hgroup : Fintype.card (ActiveGroup selection tagged) ≤ r + s + tagged.card := by
      convert activeGroup_card_le selection tagged using 1
      congr 3
      exact Subsingleton.elim _ _
    omega
  have hpattern := pow_le_pow_right₀ hc hg
  have hroot : (((2 * (tagged.card + 1) : ℕ) : ℝ) ^ tagged.card) ≤
      (((2 * (order + 1) : ℕ) : ℝ) ^ order) := by
    have hbase : (((2 * (tagged.card + 1) : ℕ) : ℝ)) ≤ (((2 * (order + 1) : ℕ) : ℝ)) := by
      exact_mod_cast (show 2 * (tagged.card + 1) ≤ 2 * (order + 1) by omega)
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hbase tagged.card).trans
    exact pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ 2 * (order + 1) by omega)) hcard
  have htwo := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hdegree
  have hcost := RootGroupCostBudget.product_cost_le selection tagged commonConstant le_rfl
  have hweight := gradeWeight_nonneg _ _ hp hb r s
  have hl2 := blockL2_nonneg (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) kernel.val
  have hprod : 0 ≤ ∏ vertex ∈ tagged, activity selection commonConstant vertex :=
    Finset.prod_nonneg (fun vertex _ => ha vertex)
  have hcost0 : 0 ≤ ∏ group, ActualRootGroupedChannel.cost selection tagged group :=
    Finset.prod_nonneg (fun group _ => ActualRootGroupedChannel.cost_nonneg selection tagged group)
  apply (hresponse hlarge hsmall r s selection tagged layout queue kernel hpositive hbody).trans
  calc
    _ ≤ (Fintype.card (TruncatedArity order) : ℝ) ^ (2 * order) *
        (((2 : ℝ) ^ order * gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) r s *
          ∏ vertex ∈ tagged, activity selection commonConstant vertex) *
        ((((2 * (order + 1) : ℕ) : ℝ) ^ order) * CycleSelections.currentRootTag security ^ tagged.card *
          blockL2 (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) kernel.val)) := by
      apply mul_le_mul hpattern _ (by positivity) (by positivity)
      apply mul_le_mul _ (by gcongr) (by positivity) (by positivity)
      exact hcost.trans (by gcongr)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      unfold degreeConstant
      ring

theorem selectedDefect_norm_eventually (order : ℕ) (horder : 1 ≤ order) :
    ∀ᶠ security : ℕ in atTop,
      2 * positiveConstant ≤ (Parameters.base security : ℝ) →
      raisingConstant ≤ (Parameters.base security : ℝ)^38 →
      2 * order ≤ Parameters.bodySize security →
      ∀ r s, r + s ≤ order → ∀ selection : Selection security r s,
      ∀ layout : BlockIndex security ≃ CycleRootExpansion.Vertex security, ∀ queue : ℤ,
      ∀ kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s,
      coefficientNorm security order (ActualRootDefect.selectedDefect order horder queue selection layout kernel) ≤
        (stabilityConstant order / (Parameters.base security : ℝ)^26) *
          (gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) r s *
            blockL2 (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) kernel.val) := by
  filter_upwards [response_norm_activity_eventually order horder] with security hresponse
  intro hlarge hsmall hbody r s hdegree selection layout queue kernel
  let inputNorm := gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) r s *
    blockL2 (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) kernel.val
  let vertexActivity := fun vertex => activity selection commonConstant vertex * CycleSelections.currentRootTag security
  have hinput : 0 ≤ inputNorm := mul_nonneg
    (gradeWeight_nonneg _ _ (RaisingPatternBudget.primaryFactor_pos security).le
      (RaisingPatternBudget.bodyFactor_pos security).le r s) (blockL2_nonneg _ _ _)
  have ht : 0 ≤ CycleSelections.currentRootTag security := by rw [CycleSelections.currentRootTag_eq]; positivity
  have ha : ∀ vertex, 0 ≤ vertexActivity vertex := fun vertex =>
    mul_nonneg (activity_nonneg selection commonConstant (zero_le_one.trans commonConstant_one) vertex) ht
  have hbase : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security from (by have := Parameters.base_ge_two security; omega))
  have hsum : (∑ vertex, vertexActivity vertex) ≤ activityConstant order / (Parameters.base security : ℝ)^13 := by
    dsimp only [vertexActivity]
    rw [← Finset.sum_mul]
    apply (sum_activity_tag_le selection commonConstant (zero_le_one.trans commonConstant_one)).trans
    unfold activityConstant
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans commonConstant_one)
    gcongr
    exact_mod_cast (show 2 * r + s ≤ 2 * order by omega)
  have hsubsets := RootSubsetNormSum.subset_sum_decay Finset.univ vertexActivity (fun vertex _ => ha vertex)
    (Parameters.base security : ℝ) (activityConstant order) hbase (activityConstant_one order) hsum order
  have hpowerset : (Finset.univ : Finset (BlockIndex security)).powerset = Finset.univ := by ext; simp
  rw [hpowerset] at hsubsets
  rw [ActualRootDefect.selectedDefect_eq_small]
  simp only [LinearMap.sum_apply]
  apply (familyNorm_sum_le _ _ order _ _ (RaisingPatternBudget.primaryFactor_pos security).le
    (RaisingPatternBudget.bodyFactor_pos security).le _ _).trans
  calc
    _ ≤ ∑ tagged ∈ (Finset.univ : Finset (Finset (BlockIndex security))).filter
        (fun tagged => 2 ≤ tagged.card ∧ tagged.card ≤ order),
        degreeConstant order * inputNorm * ∏ vertex ∈ tagged, vertexActivity vertex := by
      apply Finset.sum_le_sum
      intro tagged htagged
      have hh := (Finset.mem_filter.mp htagged).2
      exact hresponse hlarge hsmall r s hdegree selection tagged (by omega) hh.2 (by omega) layout queue kernel
    _ = degreeConstant order * inputNorm *
        ∑ tagged ∈ (Finset.univ : Finset (Finset (BlockIndex security))).filter
          (fun tagged => 2 ≤ tagged.card ∧ tagged.card ≤ order), ∏ vertex ∈ tagged, vertexActivity vertex :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ degreeConstant order * inputNorm *
        (((order + 1 : ℕ) : ℝ) * activityConstant order ^ order / (Parameters.base security : ℝ)^26) :=
      mul_le_mul_of_nonneg_left hsubsets (mul_nonneg (degreeConstant_nonneg order) hinput)
    _ = _ := by unfold stabilityConstant; ring

end
end CurrentAFT.ActualRootDefectNorm

end

section

















/-! # The complete averaged actual root operator on coefficient families -/
namespace CurrentAFT.ActualRootFamily
open AFT ActualBlockFock TaggedSelection UniformTaggedOutput ControlCoordinates ControlNorm
  GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverseNorm
  LocalCoefficientFamily BackgroundRates
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance finDecEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance sumDecEq {First Second : Type*} : DecidableEq (First ⊕ Second) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  ordinaryPool ProposalPrimary.primaryLaw ActualControls.bodyReference

theorem primary_room (security order : ℕ) (hroom : 2 * order ≤ security) (arity : TruncatedArity order) :
    arity.val.1.val ≤ Parameters.legCount security := by
  have h := FiniteAtomMoments.current_pool_room security order hroom arity.val.1.val arity.val.2.val arity.property
  omega

theorem body_room (security order : ℕ) (hroom : 2 * order ≤ security) (arity : TruncatedArity order) :
    arity.val.2.val ≤ ordinaryPool security := by
  have h := FiniteAtomMoments.current_pool_room security order hroom arity.val.1.val arity.val.2.val arity.property
  omega

/-- Every arity uses the actual independent uniform distinct selections,
including the scalar arity. The queue and public placement stay fixed. -/
def selectedAverage (security order : ℕ) (horder : 1 ≤ order) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) (arity : TruncatedArity order) :
    canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security)
      arity.val.1.val arity.val.2.val →ₗ[ℝ] Family security order where
  toFun kernel := ∑ choice : Choice security arity.val.1.val arity.val.2.val,
    ((choiceLaw security arity.val.1.val arity.val.2.val (primary_room security order hroom arity)
      (body_room security order hroom arity)).weight choice •
        ActualRootDefect.selectedDefect order horder queue
          (selection security arity.val.1.val arity.val.2.val choice) layout kernel : Family security order)
  map_add' first second := by simp only [map_add, smul_add, Finset.sum_add_distrib]
  map_smul' scalar kernel := by
    simp only [map_smul, Finset.smul_sum, smul_smul, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro choice _
    rw [mul_comm]

theorem selectedAverage_apply (security order : ℕ) (horder : 1 ≤ order) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) (arity : TruncatedArity order)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security)
      arity.val.1.val arity.val.2.val) :
    selectedAverage security order horder hroom queue layout arity kernel =
      ∑ choice : Choice security arity.val.1.val arity.val.2.val,
        (choiceLaw security arity.val.1.val arity.val.2.val (primary_room security order hroom arity)
          (body_room security order hroom arity)).weight choice •
          ActualRootDefect.selectedDefect order horder queue
            (selection security arity.val.1.val arity.val.2.val choice) layout kernel := rfl

def rootLinear (security order : ℕ) (horder : 1 ≤ order) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    Family security order →ₗ[ℝ] Family security order :=
  ∑ arity : TruncatedArity order,
    (selectedAverage security order horder hroom queue layout arity).comp (LinearMap.proj arity)

theorem rootLinear_apply (security order : ℕ) (horder : 1 ≤ order) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) (family : Family security order) :
    rootLinear security order horder hroom queue layout family =
      ∑ arity : TruncatedArity order, selectedAverage security order horder hroom queue layout arity (family arity) := by
  simp only [rootLinear, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]

 theorem average_norm_le {Choice : Type*} [Fintype Choice] (security order : ℕ)
    (law : FiniteDist Choice) (terms : Choice → Family security order) (bound : ℝ)
    (hbound : ∀ choice, LocalRaisingBounds.coefficientNorm security order (terms choice) ≤ bound) :
    LocalRaisingBounds.coefficientNorm security order (∑ choice, law.weight choice • terms choice) ≤ bound := by
  apply (familyNorm_sum_le _ _ order _ _ (RaisingPatternBudget.primaryFactor_pos security).le
    (RaisingPatternBudget.bodyFactor_pos security).le Finset.univ (fun choice => law.weight choice • terms choice)).trans
  calc
    _ ≤ ∑ choice, law.weight choice * bound := by
      apply Finset.sum_le_sum
      intro choice _
      rw [familyNorm_smul, abs_of_nonneg (law.nonneg choice)]
      exact mul_le_mul_of_nonneg_left (hbound choice) (law.nonneg choice)
    _ = bound := by rw [← Finset.sum_mul, law.sum_one, one_mul]

/-- The full actual root map is uniformly small after a fixed-order
threshold. Local positivity and current population thresholds are proved
from the public parameter family, rather than supplied as assumptions. -/
theorem rootLinear_norm_eventually (order : ℕ) (horder : 1 ≤ order) :
    ∀ᶠ security : ℕ in atTop, ∀ hroom : 2 * order ≤ security, ∀ queue : ℤ,
      ∀ layout : BlockIndex security ≃ CycleRootExpansion.Vertex security, ∀ family : Family security order,
      LocalRaisingBounds.coefficientNorm security order (rootLinear security order horder hroom queue layout family) ≤
        (ActualRootDefectNorm.stabilityConstant order / (Parameters.base security : ℝ) ^ 26) *
          LocalRaisingBounds.coefficientNorm security order family := by
  obtain ⟨threshold, hthreshold⟩ := exists_nat_ge
    (max (2 * LocalRaisingBounds.positiveConstant) LocalRaisingBounds.raisingConstant)
  filter_upwards [ActualRootDefectNorm.selectedDefect_norm_eventually order horder,
    eventually_ge_atTop threshold] with security hselected hsecurity
  intro hroom queue layout family
  have hbase : max (2 * LocalRaisingBounds.positiveConstant) LocalRaisingBounds.raisingConstant ≤
      (Parameters.base security : ℝ) := hthreshold.trans (Nat.cast_le.mpr (by unfold Parameters.base; omega))
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (Parameters.base_ge_two security).trans' (by norm_num)
  have hlarge := (le_max_left _ _).trans hbase
  have hsmall : LocalRaisingBounds.raisingConstant ≤ (Parameters.base security : ℝ) ^ 38 := by
    apply ((le_max_right _ _).trans hbase).trans
    simpa only [pow_one] using pow_le_pow_right₀ hb1 (show 1 ≤ 38 by omega)
  have hbody := CycleSelections.current_body_fixed_orders order security hroom order le_rfl
  have haverage (arity : TruncatedArity order) :
      LocalRaisingBounds.coefficientNorm security order
        (selectedAverage security order horder hroom queue layout arity (family arity)) ≤
      (ActualRootDefectNorm.stabilityConstant order / (Parameters.base security : ℝ) ^ 26) *
        (gradeWeight (primaryFactor security) (bodyFactor security) arity.val.1.val arity.val.2.val *
          blockL2 (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) (family arity).val) := by
    rw [selectedAverage_apply]
    apply average_norm_le
    intro choice
    exact hselected hlarge hsmall hbody arity.val.1.val arity.val.2.val arity.property
      (selection security arity.val.1.val arity.val.2.val choice) layout queue (family arity)
  rw [rootLinear_apply]
  apply (familyNorm_sum_le _ _ order _ _ (RaisingPatternBudget.primaryFactor_pos security).le
    (RaisingPatternBudget.bodyFactor_pos security).le Finset.univ _).trans
  calc
    _ ≤ ∑ arity : TruncatedArity order,
        (ActualRootDefectNorm.stabilityConstant order / (Parameters.base security : ℝ) ^ 26) *
          (gradeWeight (primaryFactor security) (bodyFactor security) arity.val.1.val arity.val.2.val *
            blockL2 (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) (family arity).val) :=
      Finset.sum_le_sum (fun arity _ => haverage arity)
    _ = _ := by rw [← Finset.mul_sum]; rfl



end
end CurrentAFT.ActualRootFamily

end

section















/-! # Exact arity decomposition of the actual mixed-role raising response -/
namespace CurrentAFT.CompleteRaisingPatternIdentity
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
  GradedControlAlgebra GradedInverse LocalCoefficientFamily CompleteRaising
  RaisingPatternBudget RaisingPatternKernel GroupedKernelNorm GroupedKernelProduct
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw bodyReference

def columnKernel (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s)) (pattern : Role r s → TruncatedArity order)
    (input : (role : Role r s) → RoleInput security r s role) :
    canonicalKernels (primaryLaw security) (bodyReference security) (totalPrimary pattern) (totalBody pattern) :=
  finiteProduct (primaryLaw security) (bodyReference security)
    (fun role => (pattern role).val.1.val) (fun role => (pattern role).val.2.val)
    (fun role => roleChannel security order horder selected role (Pi.single (input role) 1) (pattern role))

theorem patternKernel_column_formula (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s)) (pattern : Role r s → TruncatedArity order)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    patternKernel security order horder selected pattern kernel =
      ∑ input, inputJoint security kernel input • columnKernel security order horder selected pattern input := by
  apply Subtype.ext
  change canonicalize (primarySlots pattern) (bodySlots pattern) (primaryEquiv pattern) (bodyEquiv pattern)
    (DependentTensorChannel.apply (componentChannel security order horder selected pattern)
      (inputJoint security kernel)) = _
  rw [canonicalize_tensor_formula]
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  apply Finset.sum_congr rfl
  intro input _
  congr 1
  rw [columnKernel, finiteProduct_val]
  rfl

theorem column_product_retained (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s)) (pattern : Role r s → TruncatedArity order)
    (input : (role : Role r s) → RoleInput security r s role)
    (hdegree : totalPrimary pattern + totalBody pattern ≤ order) :
    (∏ role : Role r s, Pi.single (pattern role)
      (roleChannel security order horder selected role (Pi.single (input role) 1) (pattern role))) =
      embed (primaryLaw security) (bodyReference security) order hdegree
        (columnKernel security order horder selected pattern input) := by
  exact finite_product_embed (primaryLaw security) (bodyReference security) order
    (fun role => (pattern role).val.1.val) (fun role => (pattern role).val.2.val)
    (fun role => roleChannel security order horder selected role (Pi.single (input role) 1) (pattern role))
    hdegree (fun role => (pattern role).property)

theorem column_product_dropped (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s)) (pattern : Role r s → TruncatedArity order)
    (input : (role : Role r s) → RoleInput security r s role)
    (hdegree : order < totalPrimary pattern + totalBody pattern) :
    (∏ role : Role r s, Pi.single (pattern role)
      (roleChannel security order horder selected role (Pi.single (input role) 1) (pattern role))) =
      (0 : Family security order) := by
  have h := GlobalRaising.vanishesBelow_prod (primaryLaw security) (bodyReference security) order
    (Finset.univ : Finset (Role r s)) (fun role => (pattern role).val.1.val + (pattern role).val.2.val)
    (fun role => Pi.single (pattern role)
      (roleChannel security order horder selected role (Pi.single (input role) 1) (pattern role))) (by
        intro role _ output hsmall
        rw [Pi.single_eq_of_ne]
        intro hequal
        subst output
        omega)
  rw [Finset.sum_add_distrib] at h
  funext output
  exact h output (by have := output.property; unfold totalPrimary totalBody at hdegree; omega)

theorem patternFamily_column_formula (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s)) (pattern : Role r s → TruncatedArity order)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    patternFamily security order horder selected pattern kernel =
      ∑ input, inputJoint security kernel input •
        (∏ role : Role r s, (Pi.single (pattern role)
          (roleChannel security order horder selected role (Pi.single (input role) 1) (pattern role)) :
            Family security order)) := by
  unfold patternFamily
  split_ifs with hdegree
  · simp_rw [column_product_retained security order horder selected pattern _ hdegree]
    rw [patternKernel_column_formula]
    unfold embed
    funext output
    by_cases hequal : output = embedArity order (totalPrimary pattern) (totalBody pattern) hdegree
    · subst output
      simp
    · simp [Pi.single_eq_of_ne hequal]
  · simp_rw [column_product_dropped security order horder selected pattern _ (Nat.lt_of_not_ge hdegree),
      smul_zero, Finset.sum_const_zero]

/-- Summing finite arity patterns reconstructs the original tensor of
local family-valued channels exactly, before any norm inequality. -/
theorem sum_patternFamily (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s))
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    (∑ pattern, patternFamily security order horder selected pattern kernel) =
      ∑ input, inputJoint security kernel input •
        ∏ role : Role r s, roleChannel security order horder selected role (Pi.single (input role) 1) := by
  simp_rw [patternFamily_column_formula]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  rw [← Finset.smul_sum, ← product_family_arity_expansion]

/-- The Hilbert-friendly arity bundles are exactly the originally defined
actual correction, including both reference weights and both control roles. -/
theorem selectedCorrection_eq_sum_patterns (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s))
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    CompleteRaising.selectedCorrection security order horder selected kernel =
      ∑ pattern, patternFamily security order horder selected pattern kernel := by
  rw [sum_patternFamily]
  simp_rw [roleChannel_single, Finset.prod_smul, smul_smul]
  rw [← (Equiv.prodPiEquivSumPi (fun _ : Fin r => ActualControls.Palette security)
    (fun _ : Fin s => SafePalette security)).sum_comp, Fintype.sum_prod_type]
  unfold CompleteRaising.selectedCorrection
  apply Finset.sum_congr rfl
  intro colors _
  apply Finset.sum_congr rfl
  intro centers _
  have hweights : (∏ role : Role r s, (roleReference security r s role).weight
      ((Equiv.prodPiEquivSumPi (fun _ : Fin r => ActualControls.Palette security)
        (fun _ : Fin s => SafePalette security)) (colors, centers) role)) =
      (∏ index, (primaryLaw security).weight (colors index)) *
        ∏ index, (bodyReference security).weight (centers index) := by
    simp only [Fintype.prod_sum_type, roleReference, Equiv.prodPiEquivSumPi,
      Equiv.sumPiEquivProdPi, Equiv.coe_fn_symm_mk, Sum.elim_inl, Sum.elim_inr, RoleInput]
  rw [hweights]
  have hproduct : (∏ role : Role r s, rolePoint security order horder selected role
      ((Equiv.prodPiEquivSumPi (fun _ : Fin r => ActualControls.Palette security)
        (fun _ : Fin s => SafePalette security)) (colors, centers) role)) =
      CompleteRaising.selectedPointProduct security order horder selected colors centers := by
    apply Finset.prod_congr rfl
    intro role _
    cases role <;>
      simp only [rolePoint, CompleteRaising.slotRaised, CompleteRaising.slotLeading,
        Equiv.prodPiEquivSumPi, Equiv.sumPiEquivProdPi, Equiv.coe_fn_symm_mk,
        Sum.elim_inl, Sum.elim_inr]
  rw [hproduct]
  congr 1
  change _ = kernel.val colors centers * _
  ring

end
end CurrentAFT.CompleteRaisingPatternIdentity

end

section













/-! # Finite-degree counting for the actual mixed-role Hilbert patterns -/
namespace CurrentAFT.RaisingPatternNorm

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct ControlNorm
  GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverseNorm
  LocalCoefficientFamily LocalRaisingBounds RaisingPatternBudget RaisingPatternKernel
open Filter
open scoped BigOperators Classical Topology
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

 theorem norm_sum_le {Index : Type*} (security order : ℕ) (terms : Finset Index)
    (families : Index → Family security order) :
    LocalRaisingBounds.coefficientNorm security order (∑ index ∈ terms, families index) ≤
      ∑ index ∈ terms, LocalRaisingBounds.coefficientNorm security order (families index) :=
  familyNorm_sum_le _ _ order _ _ (primaryFactor_pos security).le (bodyFactor_pos security).le terms families

def patternCorrection (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s))
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) : Family security order :=
  ∑ pattern : Role r s → TruncatedArity order, patternFamily security order horder selected pattern kernel

theorem patternCorrection_norm (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ)) {r s : ℕ}
    (selected : Finset (Role r s))
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    LocalRaisingBounds.coefficientNorm security order (patternCorrection security order horder selected kernel) ≤
      (Fintype.card (TruncatedArity order) : ℝ) ^ (r + s) *
        ((∏ role, roleCost security selected role) * blockL2 (primaryLaw security) (bodyReference security) kernel.val) := by
  unfold patternCorrection
  apply (norm_sum_le security order Finset.univ _).trans
  calc
    _ ≤ ∑ _ : Role r s → TruncatedArity order,
        ((∏ role, roleCost security selected role) * blockL2 (primaryLaw security) (bodyReference security) kernel.val) :=
      Finset.sum_le_sum (fun pattern _ => patternFamily_norm security order horder hlarge selected pattern kernel)
    _ = _ := by simp [Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]

def homogeneousCorrection (security order : ℕ) (horder : 1 ≤ order) (r s : ℕ)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) : Family security order :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Role r s))).erase ∅,
    patternCorrection security order horder selected kernel

theorem homogeneousCorrection_norm (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ))
    (hsmall : relativeBudget security ≤ 1) (r s : ℕ)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    LocalRaisingBounds.coefficientNorm security order (homogeneousCorrection security order horder r s kernel) ≤
      (2 * (Fintype.card (TruncatedArity order) : ℝ)) ^ (r + s) * relativeBudget security *
        (gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) r s *
          blockL2 (primaryLaw security) (bodyReference security) kernel.val) := by
  let count := (Fintype.card (TruncatedArity order) : ℝ) ^ (r + s)
  let inputNorm := gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) r s *
    blockL2 (primaryLaw security) (bodyReference security) kernel.val
  have hcount : 0 ≤ count := by unfold count; positivity
  have hinput : 0 ≤ inputNorm := mul_nonneg
    (gradeWeight_nonneg _ _ (primaryFactor_pos security).le (bodyFactor_pos security).le _ _) (blockL2_nonneg _ _ _)
  have hselection (selected : Finset (Role r s)) (hselected : selected ∈ (Finset.univ : Finset (Finset (Role r s))).erase ∅) :
      LocalRaisingBounds.coefficientNorm security order (patternCorrection security order horder selected kernel) ≤
        count * (relativeBudget security * inputNorm) := by
    apply (patternCorrection_norm security order horder hlarge selected kernel).trans
    apply mul_le_mul_of_nonneg_left _ hcount
    apply (mul_le_mul_of_nonneg_right (nonempty_roleCost_product security selected
      (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1) hsmall) (blockL2_nonneg _ _ _)).trans_eq
    unfold inputNorm
    ring
  unfold homogeneousCorrection
  apply (norm_sum_le security order _ _).trans
  calc
    _ ≤ ∑ _ ∈ (Finset.univ : Finset (Finset (Role r s))).erase ∅,
        count * (relativeBudget security * inputNorm) := Finset.sum_le_sum (fun selected hselected => hselection selected hselected)
    _ = (((Finset.univ : Finset (Finset (Role r s))).erase ∅).card : ℝ) *
        (count * (relativeBudget security * inputNorm)) := by simp [nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ (r + s) * (count * (relativeBudget security * inputNorm)) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hcount (mul_nonneg (relativeBudget_nonneg security) hinput))
      exact_mod_cast (show ((Finset.univ : Finset (Finset (Role r s))).erase ∅).card ≤ 2 ^ (r + s) by
        calc
          _ ≤ Fintype.card (Finset (Role r s)) := Finset.card_le_univ _
          _ = _ := by simp [Fintype.card_sum])
    _ = _ := by unfold count inputNorm; rw [mul_pow]; ring

def degreeConstant (order : ℕ) : ℝ := (2 * (Fintype.card (TruncatedArity order) : ℝ)) ^ order

theorem degreeConstant_nonneg (order : ℕ) : 0 ≤ degreeConstant order := by unfold degreeConstant; positivity

theorem homogeneousCorrection_norm_order (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ))
    (hsmall : relativeBudget security ≤ 1) (r s : ℕ) (hdegree : r + s ≤ order)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    LocalRaisingBounds.coefficientNorm security order (homogeneousCorrection security order horder r s kernel) ≤
      degreeConstant order * relativeBudget security *
        (gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) r s *
          blockL2 (primaryLaw security) (bodyReference security) kernel.val) := by
  have hcard : 0 < Fintype.card (TruncatedArity order) := Fintype.card_pos_iff.mpr ⟨zeroArity order⟩
  have hbase : (1 : ℝ) ≤ 2 * (Fintype.card (TruncatedArity order) : ℝ) := by exact_mod_cast (show 1 ≤ 2 * Fintype.card (TruncatedArity order) by omega)
  have hbound := pow_le_pow_right₀ hbase hdegree
  have hweight := gradeWeight_nonneg _ _ (primaryFactor_pos security).le (bodyFactor_pos security).le r s
  exact (homogeneousCorrection_norm security order horder hlarge hsmall r s kernel).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbound (relativeBudget_nonneg security))
      (mul_nonneg hweight (blockL2_nonneg _ _ _)))

def assembledRaising (security order : ℕ) (horder : 1 ≤ order) (family : Family security order) : Family security order :=
  ∑ arity : TruncatedArity order,
    homogeneousCorrection security order horder arity.val.1.val arity.val.2.val (family arity)

theorem assembledRaising_norm (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ))
    (hsmall : relativeBudget security ≤ 1) (family : Family security order) :
    LocalRaisingBounds.coefficientNorm security order (assembledRaising security order horder family) ≤
      degreeConstant order * relativeBudget security * LocalRaisingBounds.coefficientNorm security order family := by
  unfold assembledRaising
  apply (norm_sum_le security order Finset.univ _).trans
  unfold LocalRaisingBounds.coefficientNorm familyNorm
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun arity _ => homogeneousCorrection_norm_order security order horder hlarge hsmall
    arity.val.1.val arity.val.2.val arity.property (family arity))

def stabilityConstant (order : ℕ) : ℝ := degreeConstant order * (raisingConstant + 80)

theorem assembledRaising_norm_eventually (order : ℕ) (horder : 1 ≤ order) :
    ∀ᶠ security : ℕ in atTop, ∀ family : Family security order,
      LocalRaisingBounds.coefficientNorm security order (assembledRaising security order horder family) ≤
        (stabilityConstant order / (Parameters.base security : ℝ) ^ 38) *
          LocalRaisingBounds.coefficientNorm security order family := by
  obtain ⟨threshold, hthreshold⟩ := exists_nat_ge (2 * positiveConstant)
  filter_upwards [eventually_ge_atTop threshold, relativeBudget_small_eventually] with security hsecurity hsmall family
  have hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ) :=
    hthreshold.trans (Nat.cast_le.mpr (show threshold ≤ Parameters.base security by unfold Parameters.base; omega))
  exact (assembledRaising_norm security order horder hlarge hsmall family).trans_eq (by unfold stabilityConstant relativeBudget; ring)

end
end CurrentAFT.RaisingPatternNorm

end

section















namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.CompleteRaising
end CurrentAFT.CompleteRaising
namespace CurrentAFT.CompleteRaising.raisingLinear
end CurrentAFT.CompleteRaising.raisingLinear
namespace CurrentAFT.CompleteRaisingInverse
end CurrentAFT.CompleteRaisingInverse
namespace CurrentAFT.CompleteRaisingInverse.inverse
end CurrentAFT.CompleteRaisingInverse.inverse
namespace CurrentAFT.CompleteRaisingInverse.response
end CurrentAFT.CompleteRaisingInverse.response
namespace CurrentAFT.RaisingInverseGeometry
end CurrentAFT.RaisingInverseGeometry




/-!
# Stability of the actual complete independent-root raising response

The exact finite-source product identity identifies the original two-role
raising map with its Hilbert arity-pattern assembly. All local operator
bounds, tensor contractions, and pattern counts have already been proved
for the current public parameters. The resulting bound is uniform over
every joint canonical input. Its explicit finite inverse preserves the
constant fiber and is bounded after one fixed-order threshold.
-/
namespace CurrentAFT.CompleteRaisingStability

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
  GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverse
  LocalCoefficientFamily LocalRaisingBounds RaisingPatternBudget RaisingPatternNorm
open Filter
open scoped BigOperators Classical Topology
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw

theorem homogeneous_eq_patterns (security order : ℕ) (horder : 1 ≤ order) (r s : ℕ)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    CompleteRaising.homogeneousCorrectionLinear security order horder r s kernel =
      RaisingPatternNorm.homogeneousCorrection security order horder r s kernel := by
  simp only [CompleteRaising.homogeneousCorrectionLinear, LinearMap.sum_apply]
  unfold RaisingPatternNorm.homogeneousCorrection RaisingPatternNorm.patternCorrection
  apply Finset.sum_congr rfl
  intro selected _
  exact CompleteRaisingPatternIdentity.selectedCorrection_eq_sum_patterns security order horder selected kernel

theorem raising_eq_patterns (security order : ℕ) (horder : 1 ≤ order) (family : Family security order) :
    CompleteRaising.raisingLinear security order horder family = assembledRaising security order horder family := by
  change (∑ arity : TruncatedArity order,
    CompleteRaising.homogeneousCorrectionLinear security order horder arity.val.1.val arity.val.2.val (family arity)) = _
  unfold assembledRaising
  exact Finset.sum_congr rfl (fun arity _ => homogeneous_eq_patterns security order horder _ _ (family arity))

/-- The actual complete raising map satisfies a current-parameter bound;
no stability estimate or factorization of the input kernel is a premise. -/
theorem raising_norm_eventually (order : ℕ) (horder : 1 ≤ order) :
    ∀ᶠ security : ℕ in atTop, ∀ family : Family security order,
      LocalRaisingBounds.coefficientNorm security order (CompleteRaising.raisingLinear security order horder family) ≤
        (stabilityConstant order / (Parameters.base security : ℝ) ^ 38) *
          LocalRaisingBounds.coefficientNorm security order family := by
  filter_upwards [assembledRaising_norm_eventually order horder] with security hbound family
  rw [raising_eq_patterns]
  exact hbound family

theorem stabilityConstant_nonneg (order : ℕ) : 0 ≤ stabilityConstant order :=
  mul_nonneg (degreeConstant_nonneg order) (add_nonneg raisingConstant_nonneg (by norm_num))







end
end CurrentAFT.CompleteRaisingStability

end

section



















/-! # Stability of the actual background and normalized response

Queue factors are multiplied before their true common-queue average. The
independent-root part below uses the constructed complete two-role raising
map and the actual averaged background. Root corrections are added only
through their actual finite-source operator.
-/
namespace CurrentAFT.ActualCompleteStability
open AFT DiffuseProfiles ProposalPrimary ActualControls LocalCoefficientFamily
  GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverseNorm
  BackgroundRates BackgroundLinear ActualBackground
open Filter
open scoped BigOperators Classical Topology
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount primaryLaw bodyReference BackgroundRates.ordinaryPool

 theorem hp (security : ℕ) : 0 ≤ primaryFactor security := (RaisingPatternBudget.primaryFactor_pos security).le
 theorem hb (security : ℕ) : 0 ≤ bodyFactor security := (RaisingPatternBudget.bodyFactor_pos security).le

 theorem norm_nonneg (security order : ℕ) (family : Family security order) :
    0 ≤ LocalRaisingBounds.coefficientNorm security order family :=
  familyNorm_nonneg _ _ order _ _ (hp security) (hb security) family

 theorem norm_add (security order : ℕ) (first second : Family security order) :
    LocalRaisingBounds.coefficientNorm security order (first + second) ≤
      LocalRaisingBounds.coefficientNorm security order first + LocalRaisingBounds.coefficientNorm security order second :=
  familyNorm_add_le _ _ order _ _ (hp security) (hb security) first second

 theorem norm_mul (security order : ℕ) (first second : Family security order) :
    LocalRaisingBounds.coefficientNorm security order (first * second) ≤
      LocalRaisingBounds.coefficientNorm security order first * LocalRaisingBounds.coefficientNorm security order second :=
  familyNorm_product_le _ _ order _ _ (hp security) (hb security) first second

theorem fixedQueueBackground_norm_decay (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : max order numericalThreshold ≤ security) (queue : ℤ) :
    LocalRaisingBounds.coefficientNorm security order (fixedQueueBackground security order horder queue - 1) ≤
      ActualBackground.stabilityConstant order / (Parameters.base security : ℝ)^6 := by
  apply (ActualBackground.fixedQueueBackground_norm security order horder hsecurity queue).trans_eq
  unfold budget ActualBackground.stabilityConstant
  ring

theorem fixedQueueBackground_norm_le_two (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : ActualBackgroundInverse.inverseThreshold order ≤ security) (queue : ℤ) :
    LocalRaisingBounds.coefficientNorm security order (fixedQueueBackground security order horder queue) ≤ 2 := by
  have hsmall := ActualBackgroundInverse.theta_le_half security order hsecurity
  have hlarge : max order numericalThreshold ≤ security :=
    (le_max_left _ _).trans hsecurity
  have hdefect := fixedQueueBackground_norm_decay security order horder hlarge queue
  have hsplit : fixedQueueBackground security order horder queue =
      (fixedQueueBackground security order horder queue - 1) + 1 := by abel
  calc
    _ = LocalRaisingBounds.coefficientNorm security order ((fixedQueueBackground security order horder queue - 1) + 1) := congrArg _ hsplit
    _ ≤ LocalRaisingBounds.coefficientNorm security order (fixedQueueBackground security order horder queue - 1) + 1 := by
      simpa only [LocalRaisingBounds.coefficientNorm, familyNorm_one] using norm_add security order (fixedQueueBackground security order horder queue - 1) 1
    _ ≤ 2 := by linarith

theorem fixedQueueBackground_norm_eventually (order : ℕ) (horder : 2 ≤ order) :
    ∀ᶠ security : ℕ in atTop, ∀ queue : ℤ,
      LocalRaisingBounds.coefficientNorm security order (fixedQueueBackground security order horder queue) ≤ 2 := by
  filter_upwards [eventually_ge_atTop (ActualBackgroundInverse.inverseThreshold order)] with security hsecurity queue
  exact fixedQueueBackground_norm_le_two security order horder hsecurity queue

theorem background_norm_le_two_eventually (order : ℕ) (horder : 2 ≤ order) :
    ∀ᶠ security : ℕ in atTop,
      LocalRaisingBounds.coefficientNorm security order (background security order horder) ≤ 2 := by
  filter_upwards [fixedQueueBackground_norm_eventually order horder] with security hbound
  exact certificateNorm_average_le security order (scalarLaw security) _ 2 (fun scalar => hbound scalar.val)

def independentResponse (security order : ℕ) (horder : 2 ≤ order) : Module.End ℝ (Family security order) where
  toFun family := background security order horder * (family + CompleteRaising.raisingLinear security order (by omega) family)
  map_add' first second := by rw [map_add]; simp only [mul_add]; abel
  map_smul' scalar family := by rw [map_smul]; simp only [← smul_add, mul_smul_comm, RingHom.id_apply]

def independentConstant (order : ℕ) : ℝ :=
  ActualBackground.stabilityConstant order + 2 * RaisingPatternNorm.stabilityConstant order



theorem independentResponse_defect_eventually (order : ℕ) (horder : 2 ≤ order) :
    ∀ᶠ security : ℕ in atTop, ∀ family : Family security order,
      LocalRaisingBounds.coefficientNorm security order (family - independentResponse security order horder family) ≤
        (independentConstant order / (Parameters.base security : ℝ)^6) * LocalRaisingBounds.coefficientNorm security order family := by
  filter_upwards [background_norm_decay_eventually order horder, background_norm_le_two_eventually order horder,
    CompleteRaisingStability.raising_norm_eventually order (by omega)] with security hbackground hbound hraising family
  have hbase : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (Parameters.base_ge_two security).trans' (by omega)
  have hcost : RaisingPatternNorm.stabilityConstant order / (Parameters.base security : ℝ)^38 ≤
      RaisingPatternNorm.stabilityConstant order / (Parameters.base security : ℝ)^6 :=
    div_le_div_of_nonneg_left (CompleteRaisingStability.stabilityConstant_nonneg order)
      (pow_pos (FirstResponse.base_pos security) _) (pow_le_pow_right₀ hbase (by omega))
  have hsplit : family - independentResponse security order horder family =
      -((background security order horder - 1) * family + background security order horder * CompleteRaising.raisingLinear security order (by omega) family) := by
    change family - background security order horder * (family + _) = _
    rw [sub_mul, one_mul, mul_add]
    abel
  rw [hsplit]
  change familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security) (-_) ≤ _
  rw [familyNorm_neg]
  apply (norm_add security order _ _).trans
  apply (add_le_add (norm_mul security order _ _) (norm_mul security order _ _)).trans
  calc
    _ ≤ (ActualBackground.stabilityConstant order / (Parameters.base security : ℝ)^6) * LocalRaisingBounds.coefficientNorm security order family +
        2 * ((RaisingPatternNorm.stabilityConstant order / (Parameters.base security : ℝ)^38) * LocalRaisingBounds.coefficientNorm security order family) := by
      exact add_le_add (mul_le_mul_of_nonneg_right hbackground (norm_nonneg security order family))
        (mul_le_mul hbound (hraising family) (norm_nonneg security order _) (by norm_num))
    _ ≤ _ := by
      unfold independentConstant
      have h := mul_le_mul_of_nonneg_right hcost (norm_nonneg security order family)
      calc
        _ ≤ (ActualBackground.stabilityConstant order / (Parameters.base security : ℝ)^6) * LocalRaisingBounds.coefficientNorm security order family +
          2 * ((RaisingPatternNorm.stabilityConstant order / (Parameters.base security : ℝ)^6) * LocalRaisingBounds.coefficientNorm security order family) := by linarith
        _ = _ := by ring




/-- The common public queue is sampled once. Its actual background factor
is multiplied by its actual root defect before averaging. -/
def rootCorrection (security order : ℕ) (horder : 2 ≤ order) (hroom : 2 * order ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) : Module.End ℝ (Family security order) where
  toFun family := ∑ scalar : FirstHistogram.Scalar security, (scalarLaw security).weight scalar •
    (fixedQueueBackground security order horder scalar.val *
      ActualRootFamily.rootLinear security order (by omega) hroom scalar.val layout family)
  map_add' first second := by simp only [map_add, mul_add, smul_add, Finset.sum_add_distrib]
  map_smul' coefficient family := by
    simp only [map_smul, mul_smul_comm, Finset.smul_sum, smul_smul, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro scalar _
    congr 1
    ring

def fullResponse (security order : ℕ) (horder : 2 ≤ order) (hroom : 2 * order ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) : Module.End ℝ (Family security order) :=
  independentResponse security order horder + rootCorrection security order horder hroom layout

def stabilityConstant (order : ℕ) : ℝ :=
  independentConstant order + 2 * ActualRootDefectNorm.stabilityConstant order



theorem rootCorrection_norm_eventually (order : ℕ) (horder : 2 ≤ order) :
    ∀ᶠ security : ℕ in atTop, ∀ hroom : 2 * order ≤ security,
      ∀ layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security, ∀ family : Family security order,
      LocalRaisingBounds.coefficientNorm security order (rootCorrection security order horder hroom layout family) ≤
        (2 * ActualRootDefectNorm.stabilityConstant order / (Parameters.base security : ℝ)^26) *
          LocalRaisingBounds.coefficientNorm security order family := by
  filter_upwards [fixedQueueBackground_norm_eventually order horder,
    ActualRootFamily.rootLinear_norm_eventually order (by omega)] with security hbackground hroot hroom layout family
  simp only [rootCorrection, LinearMap.coe_mk, AddHom.coe_mk]
  apply certificateNorm_average_le security order (scalarLaw security)
  intro scalar
  apply (norm_mul security order _ _).trans
  exact (mul_le_mul (hbackground scalar.val) (hroot hroom scalar.val layout family) (norm_nonneg security order _) (by norm_num)).trans_eq (by ring)

theorem fullResponse_defect_eventually (order : ℕ) (horder : 2 ≤ order) :
    ∀ᶠ security : ℕ in atTop, ∀ hroom : 2 * order ≤ security,
      ∀ layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security, ∀ family : Family security order,
      LocalRaisingBounds.coefficientNorm security order (family - fullResponse security order horder hroom layout family) ≤
        (stabilityConstant order / (Parameters.base security : ℝ)^6) * LocalRaisingBounds.coefficientNorm security order family := by
  filter_upwards [independentResponse_defect_eventually order horder, rootCorrection_norm_eventually order horder]
    with security hindependent hroot hroom layout family
  have hbase : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (Parameters.base_ge_two security).trans' (by omega)
  have hcost : 2 * ActualRootDefectNorm.stabilityConstant order / (Parameters.base security : ℝ)^26 ≤
      2 * ActualRootDefectNorm.stabilityConstant order / (Parameters.base security : ℝ)^6 :=
    div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (ActualRootDefectNorm.stabilityConstant_nonneg order))
      (pow_pos (FirstResponse.base_pos security) _) (pow_le_pow_right₀ hbase (by omega))
  have hsplit : family - fullResponse security order horder hroom layout family =
      (family - independentResponse security order horder family) + -(rootCorrection security order horder hroom layout family) := by
    change family - (independentResponse security order horder family + rootCorrection security order horder hroom layout family) = _
    abel
  rw [hsplit]
  apply (norm_add security order _ _).trans
  change _ + familyNorm _ _ order _ _ (-_) ≤ _
  rw [familyNorm_neg]
  apply (add_le_add (hindependent family) (hroot hroom layout family)).trans
  have h := mul_le_mul_of_nonneg_right hcost (norm_nonneg security order family)
  unfold stabilityConstant
  calc
    _ ≤ (independentConstant order / (Parameters.base security : ℝ)^6) * LocalRaisingBounds.coefficientNorm security order family +
      (2 * ActualRootDefectNorm.stabilityConstant order / (Parameters.base security : ℝ)^6) * LocalRaisingBounds.coefficientNorm security order family := by linarith
    _ = _ := by ring

end
end CurrentAFT.ActualCompleteStability

end

section













/-! # The actual stable signed calibration solution

The operator is the concrete common-queue response assembled in
`ActualCompleteStability`. The threshold below is chosen from its proved
current-parameter bound. No inverse, response norm, or construction
existence is an assumption of this calibration result. Its physical
polynomial identification is a separate theorem under construction.
-/
namespace CurrentAFT.ActualCompleteStability
open AFT DiffuseProfiles ProposalPrimary ActualControls LocalCoefficientFamily ControlCoordinates
  GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverseNorm Augmentation
  BackgroundRates BackgroundLinear ActualBackground
open Filter
open scoped BigOperators Classical Topology
noncomputable section
local instance solutionFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount primaryLaw bodyReference BackgroundRates.ordinaryPool












theorem stable_eventually (order : ℕ) (horder : 2 ≤ order) :
    ∀ᶠ security : ℕ in atTop, ∀ hroom : 2 * order ≤ security,
      ∀ layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security,
      stabilityConstant order / (Parameters.base security : ℝ)^6 ≤ 1 / 2 ∧
      ∀ family : Family security order,
      LocalRaisingBounds.coefficientNorm security order (family - fullResponse security order horder hroom layout family) ≤
        (stabilityConstant order / (Parameters.base security : ℝ)^6) * LocalRaisingBounds.coefficientNorm security order family := by
  obtain ⟨threshold, hthreshold⟩ := exists_nat_ge (2 * stabilityConstant order)
  filter_upwards [fullResponse_defect_eventually order horder, eventually_ge_atTop threshold]
    with security hdefect hsecurity hroom layout
  refine ⟨?_, hdefect hroom layout⟩
  have hbase : 2 * stabilityConstant order ≤ (Parameters.base security : ℝ) :=
    hthreshold.trans (Nat.cast_le.mpr (by unfold Parameters.base; omega))
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (Parameters.base_ge_two security).trans' (by omega)
  have hpower : (Parameters.base security : ℝ) ≤ (Parameters.base security : ℝ)^6 := by
    simpa only [pow_one] using pow_le_pow_right₀ hb1 (show 1 ≤ 6 by omega)
  apply (div_le_iff₀ (pow_pos (FirstResponse.base_pos security) _)).mpr
  linarith

 theorem exists_stable_threshold (order : ℕ) (horder : 2 ≤ order) :
    ∃ threshold : ℕ, ∀ security, threshold ≤ security → ∀ hroom : 2 * order ≤ security,
      ∀ layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security,
      stabilityConstant order / (Parameters.base security : ℝ)^6 ≤ 1 / 2 ∧
      ∀ family : Family security order,
      LocalRaisingBounds.coefficientNorm security order (family - fullResponse security order horder hroom layout family) ≤
        (stabilityConstant order / (Parameters.base security : ℝ)^6) * LocalRaisingBounds.coefficientNorm security order family :=
  Filter.eventually_atTop.mp (stable_eventually order horder)

/-- A public fixed-order threshold obtained from the proved actual bound. -/
def threshold (order : ℕ) (horder : 2 ≤ order) : ℕ :=
  max (2 * order) (Classical.choose (exists_stable_threshold order horder))

def room (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security) : 2 * order ≤ security :=
  (le_max_left _ _).trans hsecurity

theorem stable (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    stabilityConstant order / (Parameters.base security : ℝ)^6 ≤ 1 / 2 ∧
      ∀ family : Family security order,
      LocalRaisingBounds.coefficientNorm security order
        (family - fullResponse security order horder (room security order horder hsecurity) layout family) ≤
        (stabilityConstant order / (Parameters.base security : ℝ)^6) * LocalRaisingBounds.coefficientNorm security order family :=
  Classical.choose_spec (exists_stable_threshold order horder) security
    ((le_max_right _ _).trans hsecurity) _ layout

theorem calibration_existsUnique (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) (target : Family security order) :
    ∃ coefficient, fullResponse security order horder (room security order horder hsecurity) layout coefficient = target ∧
      (∀ other, fullResponse security order horder (room security order horder hsecurity) layout other = target → other = coefficient) ∧
      ∀ reference, LocalRaisingBounds.coefficientNorm security order (coefficient - reference) ≤
        LocalRaisingBounds.coefficientNorm security order
          (target - fullResponse security order horder (room security order horder hsecurity) layout reference) /
            (1 - stabilityConstant order / (Parameters.base security : ℝ)^6) := by
  have hs := stable security order horder hsecurity layout
  exact family_calibration_existsUnique (primaryLaw security) (bodyReference security) order
    (primaryReference_positive security) (bodyReference_positive security)
    (primaryFactor security) (bodyFactor security) (RaisingPatternBudget.primaryFactor_pos security)
    (RaisingPatternBudget.bodyFactor_pos security) _ _ (by linarith [hs.1]) hs.2 target

def solution (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) : Family security order :=
  Classical.choose (calibration_existsUnique security order horder hsecurity layout 1)











def coefficients (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) : ActualControls.Coefficients security order :=
  familyCoefficientEquiv (primaryLaw security) (bodyReference security) order (solution security order horder hsecurity layout)











/-- A public weight on the actual independent control pools at the fixed
placement. Its arguments contain no protected source or hidden input. -/
def publicWeight (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) :=
  PhysicalSynthesis.coefficientWeight security order (Parameters.legCount security) (ordinaryPool security)
    (coefficients security order horder hsecurity layout)



end
end CurrentAFT.ActualCompleteStability

end

section










/-!
# Fixed high moments of the actual signed public coefficient weight

The true paired kernel is centered before its distinct-index average.
Its common safe-group alphabet has a proved atom lower bound, and each
pool keeps its own collision normalizer. The complete coefficient family
is then summed by finite Minkowski in the genuine public reference law.
-/

namespace CurrentAFT.PhysicalMoments

open AFT DiffuseProfiles ProposalPrimary PhysicalSynthesis ControlCoordinates ControlNorm
  BackgroundRates FiniteAtomMoments
open scoped BigOperators Classical

noncomputable section

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize
  BackgroundRates.ordinaryPool ProposalPrimary.primaryLaw ProposalPrimary.centerLaw
  ActualControls.bodyReference SafeControlGroups.reference SafeControlGroups.kernel

/-- A fixed kernel's moment constant includes the proved tensor energy
cost `258^r≤17^(2r)`. It has no public-parameter dependence. -/
def blockFactor (primaryOrder bodyOrder moment : ℕ) : ℝ :=
  momentFactor primaryOrder bodyOrder moment 262144 * 17 ^ primaryOrder



/-- An order-only common constant for the finite family of all arities. -/
def coefficientFactor (order moment : ℕ) : ℝ :=
  1 + ∑ arity : PositiveArity order, blockFactor arity.val.1.val arity.val.2.val moment















end

end CurrentAFT.PhysicalMoments

end

section















namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.PublicWeightMoments
end CurrentAFT.PublicWeightMoments



/-! # Actual calibrated public weight: all fixed moments and bounded clipping

The coefficient family is the concrete solution of the assembled response.
The moment order changes the estimate, not the sampled public weight.
-/
namespace CurrentAFT.ActualCalibrationMoments
open AFT ActualCompleteStability PublicOutputExperiment BackgroundRates ControlNorm
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  ordinaryPool ProposalPrimary.primaryLaw ActualControls.bodyReference

def momentConstant (order moment : ℕ) : ℝ :=
  2 * PhysicalMoments.coefficientFactor order moment * ActualCompleteStability.stabilityConstant order











end
end CurrentAFT.ActualCalibrationMoments

end

section




/-!
# The final fixed-order error arithmetic

The public family is fixed before choosing the accuracy order. Its actual
modulus bound and calibration order leave three spare inverse powers in the
Fourier term. For each fixed constant, these powers absorb that constant;
a negligible remainder and the prescribed decreasing numerical budget then
give the requested eventual accuracy.

This file proves only this arithmetic and its quantifiers. It does not prove
the actual calibrated weight's negligible remainder, produce a sampler, or
verify the implementation of the numerical budget. Increasing the exponent
used to bound the remainder does not change that remainder function.
-/

namespace CurrentAFT

open Filter
open scoped Topology

/-- Inverse powers use the current public base `security + 2`. -/
noncomputable def inversePower (security order : ℕ) : ℝ :=
  1 / (Parameters.base security : ℝ) ^ order













end CurrentAFT

end

section















/-! # Negligible charge-amplified clipping for the same actual weight

The requested decay exponent changes only the moment used to estimate the
loss. The calibration order and the public coefficient family stay fixed.
-/
namespace CurrentAFT.ActualCalibrationClipping
open AFT ActualCompleteStability ActualCalibrationMoments PublicOutputExperiment
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def loss (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) : ℝ :=
  (reference security).expectation (fun controls =>
    |actualWeight security order (coefficients security order horder hsecurity layout) controls -
      clip (actualWeight security order (coefficients security order horder hsecurity layout) controls)|)





end
end CurrentAFT.ActualCalibrationClipping

end

section













/-! # The exact rotation between physical block and body-role indices -/
namespace CurrentAFT.ActualLayouts
open ActualBlockFock ConditionalHistogramMean
noncomputable section

def blockRoleEquiv (security : ℕ) : BlockIndex security ≃ RoleIndex security :=
  (Equiv.sumComm _ _).trans (Equiv.sumAssoc _ _ _)

@[simp] theorem blockRole_primary (security : ℕ) (index : Fin (Parameters.legCount security)) :
    blockRoleEquiv security (.inl index) = .inr (.inr index) := rfl

@[simp] theorem blockRole_center (security : ℕ) (index : Fin (centerCount security)) :
    blockRoleEquiv security (.inr (.inl index)) = .inl index := rfl

@[simp] theorem blockRole_queue (security : ℕ) (index : Fin (Parameters.modulus security)) :
    blockRoleEquiv security (.inr (.inr index)) = .inr (.inl index) := rfl

def blockLayout {security : ℕ} (layout : RoleIndex security ≃ ActualCycleMeanMGF.BodyIndex security) :
    BlockIndex security ≃ CycleRootExpansion.Vertex security := (blockRoleEquiv security).trans layout

@[simp] theorem blockLayout_primary {security : ℕ}
    (layout : RoleIndex security ≃ ActualCycleMeanMGF.BodyIndex security) (index : Fin (Parameters.legCount security)) :
    blockLayout layout (.inl index) = layout (.inr (.inr index)) := rfl

@[simp] theorem blockLayout_center {security : ℕ}
    (layout : RoleIndex security ≃ ActualCycleMeanMGF.BodyIndex security) (index : Fin (centerCount security)) :
    blockLayout layout (.inr (.inl index)) = layout (.inl index) := rfl

@[simp] theorem blockLayout_queue {security : ℕ}
    (layout : RoleIndex security ≃ ActualCycleMeanMGF.BodyIndex security) (index : Fin (Parameters.modulus security)) :
    blockLayout layout (.inr (.inr index)) = layout (.inr (.inl index)) := rfl

end
end CurrentAFT.ActualLayouts

end

section











namespace AFT
end AFT
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.LocalTensors.atomLinear
end AFT.LocalTensors.atomLinear
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial



/-! # Actual homogeneous output coefficients of a truncated centered PGF -/
namespace CurrentAFT.CenteredPolynomialDegree
open AFT RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

def selectedPolynomial (reference : FiniteDist Color) (mass : (Slot → Color) → ℝ)
    (selected : Finset Slot) : MvPolynomial Color ℝ :=
  ∑ word, mass word • ∏ slot ∈ selected, (centeredFactor reference.weight (word slot) - 1)

















end
end CurrentAFT.CenteredPolynomialDegree

end

section















namespace AFT
end AFT
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.LocalTensors.atomLinear
end AFT.LocalTensors.atomLinear
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.CenteredPolynomialSymmetry
end CurrentAFT.CenteredPolynomialSymmetry
namespace CurrentAFT.LowDegreeCancellation
end CurrentAFT.LowDegreeCancellation




/-! # Exact cancellation and the full tail for the literal public experiment -/
namespace CurrentAFT.PublicLowDegree
open AFT RepresentedPolynomial ActualBlockMean ActualCycleMeanMGF ConditionalHistogramMean
  FourierCoordinates FrequencySupport
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount







end
end CurrentAFT.PublicLowDegree

end

section

















/-! # Complete Fourier energy for the actual stable calibration solution -/
namespace CurrentAFT.ActualCalibrationFourier
open AFT ActualCompleteStability ActualLayouts ConditionalHistogramMean ActualCycleMeanMGF
  BackgroundRates ControlNorm
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def calibratedCoefficients (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security) (layout : RoleIndex security ≃ BodyIndex security) :
    ActualControls.Coefficients security order :=
  coefficients security order horder hsecurity (blockLayout layout)

def energyBudget (order : ℕ) : ℝ := (2 * CoefficientOutputFock.normConstant order 1)^2











end
end CurrentAFT.ActualCalibrationFourier

end

section















/-! # The actual Fourier budget has the manuscript's fixed-order decay -/
namespace CurrentAFT.ActualCalibrationRates
open ActualCalibrationFourier ActualCalibrationClipping
open Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def fourierError (security order : ℕ) : ℝ :=
  Real.sqrt (energyBudget order / ActualPhysicalTail.analysisRadius security^(2 * (order + 1)))

def fourierConstant (order : ℕ) : ℝ :=
  2 * CoefficientOutputFock.normConstant order 1 * Real.sqrt (Real.exp 1)^(order + 1)













end
end CurrentAFT.ActualCalibrationRates

end

section










/-! # Exact Fourier transport from the implementation palette to residues -/
namespace CurrentAFT.PublicEndpointFourier
open AFT FourierCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {Core Index Color : Type*} [Fintype Core] [Fintype Index] [Fintype Color]
  [DecidableEq Index] {modulus : ℕ} [NeZero modulus]

def wordEquiv (palette : Color ≃ ZMod modulus) : (Index → Color) ≃ (Index → ZMod modulus) :=
  Equiv.piCongrRight (fun _ => palette)







end
end CurrentAFT.PublicEndpointFourier

end

section










/-! # Exact public-seed disintegration of the actual protected pair law -/
namespace CurrentAFT.ActualPublicLegCharge
open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy FirstHistogram InwardAnchor
open scoped BigOperators Classical
noncomputable section
local instance disintegrationFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance disintegrationAnchorWidthNeZero (security : ℕ) : NeZero (Parameters.anchorWidth security) :=
  ⟨(InwardAnchor.anchorWidth_pos security).ne'⟩
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff


















end
end CurrentAFT.ActualPublicLegCharge

end

section













/-! # Exact coarse marginals of the public leg and baseline refinement -/
namespace CurrentAFT.RefinedPublicTripleAverage
open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy FirstHistogram FixedPairedFirst
  ActualBlockFock ActualPublicCharge RefinedPublicOutput PositivePublicChannels
open scoped BigOperators Classical
noncomputable section
local instance averageFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw centerLaw
abbrev Palette (security : ℕ) := ActualControls.Palette security







end
end CurrentAFT.RefinedPublicTripleAverage

end

section















/-! # Averaging only the newly exposed public coordinates -/
namespace CurrentAFT.RefinedPublicDisintegration
open AFT DiffuseProfiles ProposalPrimary ActualBlockFock ActualBlockMean ActualCycleMeanMGF
  ConditionalHistogramMean ActualPublicCharge PublicOutputExperiment PublicCoefficientOutput
  PositivePublicChannels RefinedPublicOutput PublicAuxiliaryFubini
open scoped BigOperators Classical
noncomputable section
section Local
local instance disintegrationFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount





end Local
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount







end
end CurrentAFT.RefinedPublicDisintegration

end

section













/-! # One source-independent public proposal for charge and Fourier calibration -/
namespace CurrentAFT.ActualPublicExperiment
open AFT ActualBlockFock ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  PublicOutputExperiment PublicEndpointFourier RefinedPublicDisintegration FourierCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

abbrev Palette (security : ℕ) := FirstHistogram.Palette security
abbrev Residue (security : ℕ) := ZMod (Parameters.modulus security)



def paletteChannel (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) : FiniteDist (Fin (Parameters.dimension security) → Palette security) :=
  FiniteDist.retype (RefinedPublicOutput.lawGiven security layout core)

def channel (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) : FiniteDist (Fin (Parameters.dimension security) → Residue security) :=
  (paletteChannel security layout core).map
    (wordEquiv (ZMod.finEquiv (Parameters.modulus security)).toEquiv)













end
end CurrentAFT.ActualPublicExperiment

end

section







/-! # Public conditioning on a nonempty finite endpoint index set -/
namespace CurrentAFT.FiniteZeroSum
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {Index : Type*} [Fintype Index] [DecidableEq Index] [Nonempty Index] (modulus : ℕ) [NeZero modulus]

def indexEquiv : Index ≃ Fin (Fintype.card Index - 1 + 1) :=
  (Fintype.equivFin Index).trans (finCongr (by have := Fintype.card_pos (α := Index); omega))

def wordEquiv : (Index → ZMod modulus) ≃ EndpointSpace (Fintype.card Index - 1) modulus :=
  Equiv.arrowCongr (indexEquiv (Index := Index)) (Equiv.refl _)

omit [NeZero modulus] [DecidableEq Index] in
theorem wordEquiv_sum (word : Index → ZMod modulus) :
    ∑ index, wordEquiv modulus word index = ∑ index, word index :=
  Equiv.sum_comp (indexEquiv (Index := Index)).symm word

theorem uniform_charge_mass :
    (FiniteDist.uniform (Index → ZMod modulus)).eventMass (fun word => ∑ index, word index = 0) =
      1 / (modulus : ℝ) := by
  have h := uniform_eventMass_zeroSum (Fintype.card Index - 1) modulus
  rw [← FiniteDist.uniform_map_equiv (wordEquiv (Index := Index) modulus), eventMass_map] at h
  refine Eq.trans ?_ h
  unfold FiniteDist.eventMass
  apply Finset.sum_congr rfl
  intro word _
  rw [wordEquiv_sum]

/-- Ambient uniformity conditioned on exactly the zero-sum event. -/
def uniformLaw : FiniteDist (Index → ZMod modulus) :=
  (FiniteDist.uniform (Index → ZMod modulus)).condition (fun word => ∑ index, word index = 0)
    (by rw [uniform_charge_mass]; exact one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne modulus))))





end
end CurrentAFT.FiniteZeroSum

end

section

















/-! # Positive publicly charged sampling with the actual calibrated weight -/
namespace CurrentAFT.ActualCalibratedPublic
open AFT ActualBlockFock ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge ActualPublicExperiment
  ActualCalibrationFourier ActualCalibrationRates ActualCalibrationClipping ActualCompleteStability
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

local instance endpointNonempty (security : ℕ) : Nonempty (Fin (Parameters.dimension security)) :=
  ⟨⟨0, by exact_mod_cast PhysicalFockRates.dimension_pos security⟩⟩

def weight (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security) : Core security → ℝ :=
  pulledWeight security order (calibratedCoefficients security order horder hsecurity layout)

def mass (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security) :
    (Fin (Parameters.dimension security) → ZMod (Parameters.modulus security)) → ℝ :=
  endpointMass (proposal security) (weight security order horder hsecurity layout) (channel security layout)

/-- The sole algebraic premise left to the complete physical PGF identity. -/
def Calibrated (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security) : Prop :=
  TruncatedOutput.quotientMap order
    (RepresentedPolynomial.centeredGeneratingLinear (LocalReferenceEnergy.uniformReference security).weight
      (ActualWeightedFourier.mixedMass security order (room security order horder hsecurity) layout
        (calibratedCoefficients security order horder hsecurity layout))) = 1















end
end CurrentAFT.ActualCalibratedPublic

end

section














namespace AFT
end AFT
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.LocalTensors.atomLinear
end AFT.LocalTensors.atomLinear
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial





/-! # Exact finite averages and relabelings of the physical output PGF -/
namespace CurrentAFT.PhysicalPolynomialAverages
open AFT AFT.RepresentedPolynomial HistogramNormalization GradedControlAlgebra
  ControlCoordinates CycleRootExpansion
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false













def arityOptionMap (order : ℕ) : Option (PositiveArity order) → TruncatedArity order
  | none => zeroArity order
  | some arity => positiveArity order arity





end
end CurrentAFT.PhysicalPolynomialAverages

end

section




namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.DependentTensorComposition
end CurrentAFT.DependentTensorComposition


/-! # Exact algebra-valued contraction of arbitrary joint finite inputs

This is a literal source sum of products of local linear columns. It is
not a product assumption on the input kernel. Coordinate projections may
be moved to the complete joint input before physical polynomial evaluation.
-/
namespace CurrentAFT.FinitePolynomialTensor
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

variable {Index : Type*} [Fintype Index] [DecidableEq Index]
  {Input Middle : Index → Type*} [∀ index, Fintype (Input index)] [∀ index, Fintype (Middle index)]
  {Value : Type*} [CommRing Value] [Algebra ℝ Value]



def synthesis (channels : ∀ index, (Input index → ℝ) →ₗ[ℝ] Value)
    (input : ((index : Index) → Input index) → ℝ) : Value :=
  ∑ source, input source • ∏ index, channels index (Pi.single (source index) 1)

def synthesisLinear (channels : ∀ index, (Input index → ℝ) →ₗ[ℝ] Value) :
    ((((index : Index) → Input index) → ℝ) →ₗ[ℝ] Value) where
  toFun := synthesis channels
  map_add' first second := by simp only [synthesis, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' scalar input := by
    simp only [synthesis, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]







variable {Output : Type*} [CommRing Output] [Algebra ℝ Output]



end
end CurrentAFT.FinitePolynomialTensor

end

section













namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.DependentTensorComposition
end CurrentAFT.DependentTensorComposition
namespace CurrentAFT.DependentTensorFixedInput
end CurrentAFT.DependentTensorFixedInput




/-! # Control centering fixes the actual full joint source

Only selected public controls are centered. Root words remain joint, and
unselected blocks have an identity control map. Canonicality of the
original coefficient kernel supplies these exact fixed-point identities.
-/
namespace CurrentAFT.RootSelectedControlCenter
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  ControlCoordinates GradedControlAlgebra CoefficientHilbert
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

section Generic
variable {RootData Control : Type*} [Fintype Control]

def centerControl (law : FiniteDist Control) :
    ((RootData × Control) → ℝ) →ₗ[ℝ] ((RootData × Control) → ℝ) where
  toFun score sample := score sample - law.expectation (fun control => score (sample.1, control))
  map_add' first second := by
    funext sample
    simp only [Pi.add_apply]
    rw [FiniteDist.expectation_add]
    ring
  map_smul' scalar score := by
    funext sample
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [FiniteDist.expectation_const_mul]
    ring





end Generic

abbrev Input {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged) :=
  (groupRootSlots selection tagged group → CycleRootExpansion.Root security) × ControlInput selection tagged group

def projector {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    (group : ActiveGroup selection tagged) → (Input selection tagged group → ℝ) →ₗ[ℝ] (Input selection tagged group → ℝ)
  | .inl role => centerControl (RaisingPatternBudget.roleReference security r s role)
  | .inr _ => LinearMap.id







end
end CurrentAFT.RootSelectedControlCenter

end

section

















/-! # Literal physical denominators of the selected local channels

The primary factor contains an independent compensator and the complete
same-scalar leg. The ordinary factor is the actual root-averaged center
singleton. These equalities identify the physical factors canceled by
the finite reciprocals; no polynomial image is assumed injective.
-/
namespace CurrentAFT.RootLocalDenominators
open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls FirstHistogram
  LocalReferenceEnergy PairedReferenceEnergy FixedPairedFirst IndependentPairedReference
  PositiveFirstCoefficient ActualBlockFock RootTaggedSelected RootReferenceExpectation
  RootBackgroundPolynomial RootIndependentBackground BodyRootAverages BackgroundPolynomialEvaluation
  BackgroundEndpointLaw CycleRootExpansion ControlCoordinates GradedControlAlgebra GradedControlNorm
  LocalCoefficientFamily LocalRaisingBounds NormalizedLocalPolynomial
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw rootReference
abbrev Palette (security : ℕ) := ActualControls.Palette security

theorem uniformReference_eq (security : ℕ) :
    (uniformReference security).weight = FringeCertificate.uniformProfile security := by
  funext color
  rw [uniformReference_weight]
  simp only [FringeCertificate.uniformProfile, one_div]

theorem generating_eq_block {Slot : Type*} [Fintype Slot] (security : ℕ)
    (law : FiniteDist (Slot → Palette security)) :
    centeredGeneratingLinear (uniformReference security).weight law.weight = blockGenerating security law := by
  simp only [centeredGeneratingLinear, blockGenerating, finiteGenerating, LinearMap.coe_mk, AddHom.coe_mk,
    MvPolynomial.smul_eq_C_mul, uniformReference_eq]











def ordinaryPolynomial (security : ℕ) : MvPolynomial (Palette security) ℝ :=
  singleGenerating (FringeCertificate.uniformProfile security) (BackgroundCertificates.convolvedCenterLaw security).weight

def primaryPolynomial (security : ℕ) : MvPolynomial (Palette security) ℝ :=
  ordinaryPolynomial security * LegPolynomialEvaluation.legGenerating security















end
end CurrentAFT.RootLocalDenominators

end

section

















/-! # Literal physical columns of the selected normalized channels

Every numerator below is a finite weighted generating function of the
actual local law. The selected primary score is used once in the paired
channel, and its compensator and attachment retain the same leg scalar.
-/
namespace CurrentAFT.RootSelectedPhysicalColumns
open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls FirstHistogram
  LocalReferenceEnergy PairedReferenceEnergy FixedPairedFirst PhysicalSynthesis
  RootTaggedSelected RootBackgroundPolynomial BackgroundPolynomialEvaluation
  CycleRootExpansion LocalCoefficientFamily RootLocalDenominators
  ControlCoordinates GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance safeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw rootReference
abbrev Palette (security : ℕ) := ActualControls.Palette security

def primaryNumerator (security : ℕ) (score : RootPair security → Palette security → ℝ) : MvPolynomial (Palette security) ℝ :=
  ∑ sample : RootTaggedSelected.Sample security, (sourceLaw security).weight sample •
    ∑ group : PhysicalSynthesis.Group security, ((groupLaw security).weight group * pairedChannel security (score sample.1) group) •
      blockGenerating security (fixedControlLaw security (sample.1.1.val : ℤ) (sample.1.2.val : ℤ) sample.2 group)

theorem pairedMass_generating (security : ℕ) (comp attach : ℤ) (scalar : FirstHistogram.Scalar security)
    (score : Palette security → ℝ) :
    centeredGeneratingLinear (uniformReference security).weight (pairedMassAt security comp attach scalar score) =
      ∑ group : PhysicalSynthesis.Group security, ((groupLaw security).weight group * pairedChannel security score group) •
        blockGenerating security (fixedControlLaw security comp attach scalar group) := by
  have hmass : pairedMassAt security comp attach scalar score =
      ∑ group : PhysicalSynthesis.Group security, ((groupLaw security).weight group * pairedChannel security score group) •
        (fixedControlLaw security comp attach scalar group).weight := by
    rw [← pairedMassLinear_apply]
    funext word
    simp only [pairedMassLinear, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      fixedControlLaw_weight]
  rw [hmass, map_sum]
  simp only [map_smul, generating_eq_block]

theorem primaryNumerator_eq (security : ℕ) (score : RootPair security → Palette security → ℝ) :
    centeredGeneratingLinear (uniformReference security).weight (mass security score) = primaryNumerator security score := by
  have hmass : mass security score =
      ∑ sample : RootTaggedSelected.Sample security, (sourceLaw security).weight sample •
        pairedMassAt security (sample.1.1.val : ℤ) (sample.1.2.val : ℤ) sample.2 (score sample.1) := by
    funext word
    simp only [mass_eq_joint, jointPairedMass, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hmass, map_sum]
  simp only [map_smul, pairedMass_generating]
  rfl







def ordinaryNumerator (security : ℕ) (score : SelectedOrdinaryRoot.Input security → ℝ) : MvPolynomial (Palette security) ℝ :=
  ∑ root : Root security, (rootReference security).weight root •
    ∑ center : SafePalette security, ((bodyReference security).weight center * score (root, center)) •
      centeredFactor (uniformReference security).weight (SelectedOrdinaryRoot.rootEmbedding security root center)











end
end CurrentAFT.RootSelectedPhysicalColumns

end

section















/-! # Explicit projected linear columns of the true local physical numerator

Both selected roles have the form physicalLinear ∘ controlCenter ∘ rootMask.
The control projector is exactly the one proved to fix the original full
joint coefficient source. No factorization of that source is required.
-/
namespace CurrentAFT.RootSelectedPhysicalLinear
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
  LocalCoefficientFamily RootTaggedSelected RootSelectedPhysicalColumns RootLocalDenominators
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance safeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw rootReference
abbrev Palette (security : ℕ) := ActualControls.Palette security

def primaryNumeratorLinear (security : ℕ) :
    (RootPair security → Palette security → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ where
  toFun := primaryNumerator security
  map_add' first second := by
    simp only [← primaryNumerator_eq]
    exact congrArg (AFT.RepresentedPolynomial.centeredGeneratingLinear (LocalReferenceEnergy.uniformReference security).weight)
      ((massLinear security).map_add first second) |>.trans
        ((AFT.RepresentedPolynomial.centeredGeneratingLinear (LocalReferenceEnergy.uniformReference security).weight).map_add _ _)
  map_smul' scalar score := by
    simp only [← primaryNumerator_eq]
    exact congrArg (AFT.RepresentedPolynomial.centeredGeneratingLinear (LocalReferenceEnergy.uniformReference security).weight)
      ((massLinear security).map_smul scalar score) |>.trans
        ((AFT.RepresentedPolynomial.centeredGeneratingLinear (LocalReferenceEnergy.uniformReference security).weight).map_smul scalar _)

def ordinaryNumeratorLinear (security : ℕ) :
    (SelectedOrdinaryRoot.Input security → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ where
  toFun := ordinaryNumerator security
  map_add' first second := by
    simp only [ordinaryNumerator, Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib, smul_add]
  map_smul' scalar score := by
    simp only [ordinaryNumerator, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro root _
    apply Finset.sum_congr rfl
    intro center _
    congr 1
    ring

def primaryRaw (security : ℕ) :
    (RootPrimaryGroupedChannel.Input security → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ :=
  (primaryNumeratorLinear security).comp
    ((RootTaggedSelectedChannel.curryLinear security).comp (RootPrimaryGroupedChannel.pairLinear security))

def ordinaryRaw (security : ℕ) :
    (RootOrdinaryGroupedChannel.Input security → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ :=
  (ordinaryNumeratorLinear security).comp (RootOrdinaryGroupedChannel.toRaw security)

def primaryProjected (security : ℕ) (tagged : Fin 2 → Bool) :
    (RootPrimaryGroupedChannel.Input security → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ :=
  (primaryRaw security).comp ((RootSelectedControlCenter.centerControl (primaryLaw security)).comp
    (RootPrimaryGroupedChannel.projector security tagged))

def ordinaryProjected (security : ℕ) (tagged : Bool) :
    (RootOrdinaryGroupedChannel.Input security → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ :=
  (ordinaryRaw security).comp ((RootSelectedControlCenter.centerControl (bodyReference security)).comp
    (RootOrdinaryGroupedChannel.projector security tagged))













end
end CurrentAFT.RootSelectedPhysicalLinear

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
namespace CurrentAFT.PairedRootInput
end CurrentAFT.PairedRootInput
namespace CurrentAFT.PairedRootInput.controlReference
end CurrentAFT.PairedRootInput.controlReference
namespace CurrentAFT.PairedRootInput.controlReference.match_1
end CurrentAFT.PairedRootInput.controlReference.match_1
namespace CurrentAFT.PairedRootInput.reference
end CurrentAFT.PairedRootInput.reference
namespace CurrentAFT.RootGroupedSourceFormula
end CurrentAFT.RootGroupedSourceFormula
namespace CurrentAFT.RootGroupedSourceFormula.completedTest
end CurrentAFT.RootGroupedSourceFormula.completedTest
namespace CurrentAFT.RootGroupedSourceFormula.controlWeightedTest
end CurrentAFT.RootGroupedSourceFormula.controlWeightedTest




/-! # Literal complete conditional tagged output polynomials

All remaining blocks stay in the product. The selected common-alphabet
score is the original kernel with only its independent unused controls added.
-/
namespace CurrentAFT.TypedTaggedPhysical
open AFT AFT.RepresentedPolynomial ActualBlockFock TaggedSelection TaggedOutputFock
  JointTaggedPhysicalFock PairedOutputPlacement LocalReferenceEnergy
  RootBackgroundPolynomial BackgroundPolynomialEvaluation RootLocalDenominators
  CycleRootExpansion ControlCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _
local instance actualGroupDecidableEq (security : ℕ) :
    DecidableEq (JointTaggedPhysicalFock.Group security) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

section Generic
variable {Index Color : Type*} [Fintype Index] [Fintype Color]





end Generic

abbrev Palette (security : ℕ) := ActualControls.Palette security

def blockLaw (security : ℕ) (queue : ℤ) (roots : BlockIndex security → ℤ) :=
  blockLawAt security (fun leg => roots (.inl leg)) (fun center => roots (.inr (.inl center)))
    (fun point => roots (.inr (.inr point))) queue

def selectedMass {security r s : ℕ} (selection : Selection security r s)
    (roots : BlockIndex security → ℤ)
    (kernel : DensityKernel (Primary := Palette security) (Body := ActualControls.SafePalette security) r s) :=
  jointMass security r s
    (fun index => roots (.inr (.inl (selection.compensator index))))
    (fun index => roots (.inl (selection.primary index)))
    (fun index => roots (.inr (.inl (selection.body index)))) kernel

def conditionalMass {security r s : ℕ} (selection : Selection security r s) (queue : ℤ)
    (roots : BlockIndex security → ℤ)
    (kernel : DensityKernel (Primary := Palette security) (Body := ActualControls.SafePalette security) r s) :
    (OutputIndex selection → Palette security) → ℝ :=
  BlockProducts.taggedBlockMass (fun index : selection.kept => Slots security index.val)
    (selectedMass selection roots kernel) (fun index => blockLaw security queue roots index.val)

def conditionalPolynomial {security r s : ℕ} (selection : Selection security r s) (queue : ℤ)
    (roots : BlockIndex security → ℤ)
    (kernel : DensityKernel (Primary := Palette security) (Body := ActualControls.SafePalette security) r s) :
    MvPolynomial (Palette security) ℝ :=
  centeredGeneratingLinear (uniformReference security).weight (conditionalMass selection queue roots kernel)









end
end CurrentAFT.TypedTaggedPhysical

end

section














namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.DependentTensorComposition
end CurrentAFT.DependentTensorComposition




/-! # Exact removal of unused coordinates in the actual physical PGF

The common safe-control alphabet used for the Fock bounds and the two typed
control alphabets used for calibration define the same joint signed output.
-/
namespace CurrentAFT.TypedRolePolynomial
open AFT AFT.RepresentedPolynomial ActualBlockFock JointTaggedPhysicalFock
  LocalReferenceEnergy ControlCoordinates RaisingPatternBudget TaggedPhysicalFock
  OrdinaryPhysicalFock
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance actualGroupDecidableEq (security : ℕ) :
    DecidableEq (JointTaggedPhysicalFock.Group security) := Classical.decEq _
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw

section Generic
variable {Index : Type*} [Fintype Index] [DecidableEq Index]
  {Input Output : Index → Type*} [∀ index, Fintype (Input index)]

def pullbackLinear {First Second : Type*} (projection : Second → First) :
    (First → ℝ) →ₗ[ℝ] (Second → ℝ) where
  toFun score output := score (projection output)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl



end Generic

abbrev Palette (security : ℕ) := ActualControls.Palette security

def roleProjection (security r s : ℕ) :
    (role : Role r s) → JointTaggedPhysicalFock.Group security → RoleInput security r s role
  | .inl _, group => group.1
  | .inr _, group => group.2

def lift (security r s : ℕ) (role : Role r s) :
    (RoleInput security r s role → ℝ) →ₗ[ℝ] (JointTaggedPhysicalFock.Group security → ℝ) :=
  pullbackLinear (roleProjection security r s role)

def reduce (security r s : ℕ) :
    (role : Role r s) → (JointTaggedPhysicalFock.Group security → ℝ) →ₗ[ℝ] (RoleInput security r s role → ℝ)
  | .inl _ => reducePrimary (ActualControls.bodyReference security)
  | .inr _ => reduceBody (ProposalPrimary.primaryLaw security)



def typedKernel (security : ℕ) {r s : ℕ}
    (kernel : DensityKernel (Primary := Palette security) (Body := ActualControls.SafePalette security) r s)
    (word : (role : Role r s) → RoleInput security r s role) : ℝ :=
  kernel (fun index => word (.inl index)) (fun index => word (.inr index))







def raw (security r s : ℕ) (compensator attachment : Fin r → ℤ) (body : Fin s → ℤ) :
    (role : Role r s) → (RoleInput security r s role → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ
  | .inl index => (centeredGeneratingLinear (uniformReference security).weight).comp
      (averagedPairedChannel security (compensator index) (attachment index))
  | .inr index => (centeredGeneratingLinear (uniformReference security).weight).comp
      (bodyChannel security (body index))

def common (security r s : ℕ) (compensator attachment : Fin r → ℤ) (body : Fin s → ℤ)
    (role : Role r s) : (JointTaggedPhysicalFock.Group security → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ :=
  (raw security r s compensator attachment body role).comp (reduce security r s role)







end
end CurrentAFT.TypedRolePolynomial

end

section















/-! # Complete unselected physical numerators as root-centered linear maps -/
namespace CurrentAFT.RootUnselectedPhysicalLinear
open AFT AFT.RepresentedPolynomial ActualBlockFock CycleRootExpansion DiffuseProfiles
  ProposalPrimary ActualControls LocalReferenceEnergy RootTaggedLocal UniformBodyProfiles
  RootUnselectedGrouped RootUnselectedBlockChannel RootIndependentBackground
  RootLocalDenominators BodyRootAverages
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw rootReference

abbrev Palette (security : ℕ) := ActualControls.Palette security

def positiveAt (security : ℕ) (queue : ℤ) : BlockIndex security → Root security → MvPolynomial (Palette security) ℝ
  | .inl _, root => RootBackgroundPolynomial.blockGenerating security (primaryLawAt security root.val)
  | .inr (.inl _), root => singleGenerating (uniformReference security).weight (shiftedLaw security .free 0 root).weight
  | .inr (.inr _), root => singleGenerating (uniformReference security).weight (shiftedLaw security .queue queue root).weight



def rawRoot (security : ℕ) (queue : ℤ) (block : BlockIndex security) :
    (Root security → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ where
  toFun input := ∑ root, ((rootReference security).weight root * input root) • positiveAt security queue block root
  map_add' first second := by
    simp only [Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' scalar input := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro root _
    congr 1
    ring















def raw (security : ℕ) (queue : ℤ) (block : BlockIndex security) :
    (RootUnselectedGrouped.Input security → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ :=
  (rawRoot security queue block).comp (extractLinear security)

def projected (security : ℕ) (queue : ℤ) (block : BlockIndex security) :
    (RootUnselectedGrouped.Input security → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ :=
  (raw security queue block).comp (RootCoordinateProjection.center (rootReference security) (0 : Fin 1))







end
end CurrentAFT.RootUnselectedPhysicalLinear

end

section



















/-! # Exact physical image of the actual joint root-subset response -/
namespace CurrentAFT.ActualRootPhysicalResponse
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  CycleRootExpansion ControlCoordinates GradedControlAlgebra LocalCoefficientFamily
  RootLocalDenominators FinitePolynomialTensor
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalProdDecidableEq {Left Right : Type*} : DecidableEq (Left × Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount









def localDenominator {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : ActiveGroup selection tagged →
      MvPolynomial (ActualControls.Palette security) ℝ
  | .inl (.inl _) => primaryPolynomial security
  | .inl (.inr _) => ordinaryPolynomial security
  | .inr index => RootUnselectedBlockChannel.positivePolynomial security queue index.val.val

def rawPhysical {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : (group : ActiveGroup selection tagged) →
      (ActualRootGroupedChannel.Input selection tagged group → ℝ) →ₗ[ℝ] MvPolynomial (ActualControls.Palette security) ℝ
  | .inl (.inl _) => RootSelectedPhysicalLinear.primaryRaw security
  | .inl (.inr _) => RootSelectedPhysicalLinear.ordinaryRaw security
  | .inr index => RootUnselectedPhysicalLinear.raw security queue index.val.val

def projectedPhysical {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged) :
    (ActualRootGroupedChannel.Input selection tagged group → ℝ) →ₗ[ℝ] MvPolynomial (ActualControls.Palette security) ℝ :=
  (rawPhysical queue selection tagged group).comp
    ((RootSelectedControlCenter.projector selection tagged group).comp
      (PairedRootProjection.projector selection tagged group))







end
end CurrentAFT.ActualRootPhysicalResponse

end

section













/-! # Actual cycle components in physical block coordinates -/
namespace CurrentAFT.RootBlockReindex
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  PairedRootCentering CycleRootExpansion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount



end
end CurrentAFT.RootBlockReindex

end

section















/-! # All actual local denominators reconstruct the same-queue background -/
namespace CurrentAFT.RootBackgroundDenominatorProduct
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedOutputPlacement
  RootLocalDenominators RootUnselectedBlockChannel BackgroundPolynomialEvaluation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

abbrev InactiveKept {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :=
  {index : selection.kept // index.val ∉ tagged}

def denominator {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : ActiveGroup selection tagged → MvPolynomial (ActualControls.Palette security) ℝ
  | .inl (.inl _) => primaryPolynomial security
  | .inl (.inr _) => ordinaryPolynomial security
  | .inr index => positivePolynomial security queue index.val.val









end
end CurrentAFT.RootBackgroundDenominatorProduct

end

section













/-! # Roots outside the active tensor are exactly the untagged kept blocks -/
namespace CurrentAFT.RootInactivePlacement
open AFT ActualBlockFock TaggedSelection PairedRootPlacement
  RootBackgroundDenominatorProduct
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

theorem active_range_iff {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (block : BlockIndex security) :
    block ∈ Set.range (activeRootEmbedding selection tagged) ↔
      block ∈ selection.removed ∨ block ∈ tagged := by
  constructor
  · rintro ⟨index | index, hindex⟩
    · left
      change selection.removedEmbedding (selectedRootEquiv r s index) = block at hindex
      exact Finset.mem_map.mpr ⟨selectedRootEquiv r s index, Finset.mem_univ _, hindex⟩
    · right
      change index.val.val = block at hindex
      exact hindex ▸ index.property
  · rintro (hremoved | htagged)
    · obtain ⟨index, _, hindex⟩ := Finset.mem_map.mp hremoved
      refine ⟨.inl ((selectedRootEquiv r s).symm index), ?_⟩
      change selection.removedEmbedding ((selectedRootEquiv r s) ((selectedRootEquiv r s).symm index)) = block
      simpa only [Equiv.apply_symm_apply] using hindex
    · exact tagged_in_active_range selection tagged block htagged

theorem root_range_iff {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (block : BlockIndex security) :
    block ∈ Set.range (rootEmbedding selection tagged) ↔
      block ∈ selection.removed ∨ block ∈ tagged := by
  rw [← active_range_iff]
  constructor
  · rintro ⟨index, hindex⟩
    exact ⟨activeSlotsEquiv selection tagged index, hindex⟩
  · rintro ⟨index, hindex⟩
    refine ⟨(activeSlotsEquiv selection tagged).symm index, ?_⟩
    change activeRootEmbedding selection tagged
      ((activeSlotsEquiv selection tagged) ((activeSlotsEquiv selection tagged).symm index)) = block
    simpa only [Equiv.apply_symm_apply] using hindex

theorem root_mem_map_iff {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (block : BlockIndex security) :
    block ∈ Finset.univ.map (rootEmbedding selection tagged) ↔
      block ∈ selection.removed ∨ block ∈ tagged := by
  rw [← root_range_iff]
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Set.mem_range]

abbrev InactiveRoot {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :=
  {block : BlockIndex security // block ∉ Finset.univ.map (rootEmbedding selection tagged)}

def inactiveEquiv {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : InactiveRoot selection tagged ≃ InactiveKept selection tagged where
  toFun block :=
    ⟨⟨block.val, by
      have h := block.property
      rw [root_mem_map_iff] at h
      simp only [Selection.kept, Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact fun hremoved => h (.inl hremoved)⟩, by
        have h := block.property
        rw [root_mem_map_iff] at h
        exact fun htagged => h (.inr htagged)⟩
  invFun index := ⟨index.val.val, by
    rw [root_mem_map_iff]
    rintro (hremoved | htagged)
    · exact (Finset.mem_sdiff.mp index.val.property).2 hremoved
    · exact index.property htagged⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem inactiveEquiv_val {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (block : InactiveRoot selection tagged) :
    (inactiveEquiv selection tagged block).val.val = block.val := rfl

@[simp] theorem inactiveEquiv_symm_val {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : InactiveKept selection tagged) :
    ((inactiveEquiv selection tagged).symm index).val = index.val.val := rfl

end
end CurrentAFT.RootInactivePlacement

end

section





/-! # Exact root Fubini for joint physical polynomial channels -/
namespace CurrentAFT.RootPolynomialTensor
open AFT FinitePolynomialTensor
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
local instance classicalProdDecidableEq {First Second : Type*} : DecidableEq (First × Second) := Classical.decEq _

variable {Index : Type*} [Fintype Index] [DecidableEq Index]
  {RootData Control : Index → Type*} [∀ index, Fintype (RootData index)] [∀ index, Fintype (Control index)]
  {Value : Type*} [CommRing Value] [Algebra ℝ Value]

def sliceLinear (index : Index) (root : RootData index) :
    ((RootData index × Control index) → ℝ) →ₗ[ℝ] (Control index → ℝ) where
  toFun score control := score (root, control)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def averagedChannel (reference : ∀ index, FiniteDist (RootData index))
    (physical : ∀ index, RootData index → (Control index → ℝ) →ₗ[ℝ] Value) (index : Index) :
    ((RootData index × Control index) → ℝ) →ₗ[ℝ] Value :=
  ∑ root, (reference index).weight root • ((physical index root).comp (sliceLinear index root))



def sourceEquiv : ((index : Index) → RootData index × Control index) ≃
    (((index : Index) → RootData index) × ((index : Index) → Control index)) where
  toFun word := (fun index => (word index).1, fun index => (word index).2)
  invFun word index := (word.1 index, word.2 index)
  left_inv _ := rfl
  right_inv _ := rfl



end
end CurrentAFT.RootPolynomialTensor

end

section

















/-! # The actual selected physical numerators are genuine root averages -/
namespace CurrentAFT.RootPhysicalAverages
open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls FirstHistogram
  LocalReferenceEnergy PairedReferenceEnergy FixedPairedFirst PhysicalSynthesis
  RootTaggedSelected RootSelectedPhysicalLinear RootSelectedPhysicalColumns
  CycleRootExpansion TaggedPhysicalFock OrdinaryPhysicalFock
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance safeDecidableEq (security : ℕ) : DecidableEq (ActualControls.SafePalette security) := Classical.decEq _
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw rootReference
abbrev Palette (security : ℕ) := ActualControls.Palette security

def primaryAt (security : ℕ) (roots : Fin 2 → Root security) :
    (Palette security → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ :=
  (centeredGeneratingLinear (uniformReference security).weight).comp
    (averagedPairedChannel security ((roots 0).val : ℤ) ((roots 1).val : ℤ))

def ordinaryAt (security : ℕ) (roots : Fin 1 → Root security) :
    (ActualControls.SafePalette security → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ :=
  (centeredGeneratingLinear (uniformReference security).weight).comp
    (bodyChannel security ((roots 0).val : ℤ))











end
end CurrentAFT.RootPhysicalAverages

end

section













namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.PairedRootInput
end CurrentAFT.PairedRootInput
namespace CurrentAFT.PairedRootInput.controlReference
end CurrentAFT.PairedRootInput.controlReference
namespace CurrentAFT.PairedRootInput.controlReference.match_1
end CurrentAFT.PairedRootInput.controlReference.match_1
namespace CurrentAFT.PairedRootInput.reference
end CurrentAFT.PairedRootInput.reference
namespace CurrentAFT.RootGroupedSourceFormula
end CurrentAFT.RootGroupedSourceFormula
namespace CurrentAFT.RootGroupedSourceFormula.completedTest
end CurrentAFT.RootGroupedSourceFormula.completedTest
namespace CurrentAFT.RootGroupedSourceFormula.controlWeightedTest
end CurrentAFT.RootGroupedSourceFormula.controlWeightedTest


/-! # Integrating all inactive root polynomials without root-atom inverses -/
namespace CurrentAFT.RootPolynomialPlacement
open AFT CycleRootExpansion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} {predicate : Index → Prop} :
    DecidableEq (Subtype predicate) := Classical.decEq _

variable {Selected Pool Color Value : Type*} [Fintype Selected] [Fintype Pool] [Fintype Color]
  [CommRing Value] [Algebra ℝ Value]





end
end CurrentAFT.RootPolynomialPlacement

end

section





















/-! # Full joint root/control Fubini for the actual physical block product -/
namespace CurrentAFT.RootTaggedPhysicalFactorization
open AFT AFT.RepresentedPolynomial ActualBlockFock TaggedSelection PairedRootPlacement
  PairedRootInput PairedRootCentering CycleRootExpansion ControlCoordinates
  RaisingPatternBudget FinitePolynomialTensor ActualRootPhysicalResponse
  LocalReferenceEnergy
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalProdDecidableEq {Left Right : Type*} : DecidableEq (Left × Right) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} {predicate : Index → Prop} :
    DecidableEq (Subtype predicate) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount ProposalPrimary.primaryLaw

abbrev Palette (security : ℕ) := ActualControls.Palette security

def unitPolynomial {Variable : Type*} (value : MvPolynomial Variable ℝ) :
    (Unit → ℝ) →ₗ[ℝ] MvPolynomial Variable ℝ where
  toFun score := score () • value
  map_add' first second := add_smul _ _ _
  map_smul' scalar score := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_smul]

def fixedPhysical {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : (group : ActiveGroup selection tagged) →
    (groupRootSlots selection tagged group → Root security) →
    (ControlInput selection tagged group → ℝ) →ₗ[ℝ] MvPolynomial (Palette security) ℝ
  | .inl (.inl _), roots => RootPhysicalAverages.primaryAt security roots
  | .inl (.inr _), roots => RootPhysicalAverages.ordinaryAt security roots
  | .inr index, roots => unitPolynomial (RootUnselectedPhysicalLinear.positiveAt security queue index.val.val (roots (0 : Fin 1)))

def rootReferenceByGroup {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged) :
    FiniteDist (groupRootSlots selection tagged group → Root security) :=
  FiniteDist.independent (fun _ => rootReference security)



def selectedPolynomial {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security))
    (roots : Sigma (groupRootSlots selection tagged) → Root security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    MvPolynomial (Palette security) ℝ :=
  synthesis (fun role => fixedPhysical queue selection tagged (.inl role)
    (fun slot => roots ⟨.inl role, slot⟩)) (RaisingPatternKernel.inputJoint security kernel)

def hitPolynomial {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security))
    (roots : Sigma (groupRootSlots selection tagged) → Root security) : MvPolynomial (Palette security) ℝ :=
  ∏ index : HitKept selection tagged,
    RootUnselectedPhysicalLinear.positiveAt security queue index.val.val (roots ⟨.inr index, (0 : Fin 1)⟩)





end
end CurrentAFT.RootTaggedPhysicalFactorization

end

section













/-! # The actual cycle component of the complete conditional output PGF -/
namespace CurrentAFT.RootConditionalComponent
open AFT AFT.RepresentedPolynomial ActualBlockFock TaggedSelection PairedRootPlacement
  PairedRootInput PairedRootCentering CycleRootExpansion ControlCoordinates
  RootTaggedPhysicalFactorization RootUnselectedPhysicalLinear RootBackgroundDenominatorProduct
  RootLocalDenominators RootIndependentBackground LocalReferenceEnergy FinitePolynomialTensor
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalProdDecidableEq {Left Right : Type*} : DecidableEq (Left × Right) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} {predicate : Index → Prop} :
    DecidableEq (Subtype predicate) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount ProposalPrimary.primaryLaw









def keptFactor {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (block : BlockIndex security) (root : Root security) : MvPolynomial (ActualControls.Palette security) ℝ :=
  if block ∈ selection.kept then positiveAt security queue block root else 1











end
end CurrentAFT.RootConditionalComponent

end

section















/-! # Physical PGF of the complete actual root defect -/
namespace CurrentAFT.ActualRootDefectPhysical
open AFT ActualBlockFock TaggedSelection CycleRootExpansion ControlCoordinates
  LocalCoefficientFamily ActualRootDefect RootConditionalComponent
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance vertexDecidableEq (security : ℕ) : DecidableEq (Vertex security) :=
  instDecidableEqFin (Parameters.bodySize security)
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

def rootTest {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (layout : BlockIndex security ≃ Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    (Vertex security → Root security) → MvPolynomial (ActualControls.Palette security) ℝ :=
  fun roots => TypedTaggedPhysical.conditionalPolynomial selection queue
    (fun block => (roots (layout block)).val) kernel.val





end
end CurrentAFT.ActualRootDefectPhysical

end

section

















/-! # Integer roots and residue roots give the identical full conditional PGF -/
namespace CurrentAFT.RootConditionalResidues
open AFT ActualBlockFock TaggedSelection JointTaggedPhysicalFock TaggedPhysicalFock
  OrdinaryPhysicalFock TypedTaggedPhysical RootBackgroundPolynomial ActualLayouts
  ActualBlockMean ActualCycleMeanMGF ConditionalHistogramMean CycleRootExpansion ControlCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount





















end
end CurrentAFT.RootConditionalResidues

end

section















/-! # The cycle-root PGF is the literal actual averaged signed output PGF -/
namespace CurrentAFT.RootActualOutputPolynomial
open AFT AFT.RepresentedPolynomial ActualBlockFock ActualBlockMean ActualFockBound
  TaggedSelection TaggedOutputFock CycleRootExpansion ActualLayouts ActualRootDefectPhysical
  LocalReferenceEnergy RootBackgroundPolynomial ActualCycleMeanMGF
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance vertexDecidableEq (security : ℕ) : DecidableEq (Vertex security) :=
  instDecidableEqFin (Parameters.bodySize security)
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

section Generic
variable {Source Target Value : Type*} [Fintype Source] [Fintype Target]
  [AddCommGroup Value] [Module ℝ Value]







end Generic





end
end CurrentAFT.RootActualOutputPolynomial

end

section














/-! # Literal polynomial factors of the actual centered-point tensors -/

namespace CurrentAFT.PointPolynomial

open AFT ControlCoordinates ControlProduct GradedControlAlgebra
  CanonicalReconstruction LeadingEvaluation
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]

def atomForm {Color : Type*} [Fintype Color] (law : FiniteDist Color)
    (forms : Color → MvPolynomial Variable ℝ) (source : Color) : MvPolynomial Variable ℝ :=
  ∑ output, MvPolynomial.C (law.weight output * Hoeffding.centeredAtom law source output) * forms output







end

end CurrentAFT.PointPolynomial

end

section

















/-! # Physical image of the complete independent-root normalized response

The leading term is reconstructed from the original joint kernel. The
remaining terms are exactly the two-role raising operator. No injectivity
of physical polynomial evaluation is assumed.
-/
namespace CurrentAFT.CompleteRaisingEvaluation
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
  GradedControlAlgebra GradedInverse LocalCoefficientFamily LocalRaisingFirst LocalRaisingLinear
  BackgroundFamilies GlobalRaising CompleteRaising LeadingEvaluation PointPolynomial
  LocalCoefficientEvaluation BackgroundEvaluation PrimaryMassFamilies
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw bodyReference











def normalizedSlot (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (colors : Fin r → ActualControls.Palette security) (centers : Fin s → SafePalette security) :
    Fin r ⊕ Fin s → Family security order :=
  Sum.elim (fun index => NormalizedLocalPolynomial.independentNormalized security order
    (primaryAtom security (colors index)).val)
    (fun index => OrdinaryRaising.normalizedFamily security order horder
      (bodyAtom security (centers index)).val (bodyAtom security (centers index)).property)





def normalizedJoint (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) : Family security order :=
  ∑ colors, ∑ centers,
    ((∏ index, (primaryLaw security).weight (colors index)) *
      (∏ index, (bodyReference security).weight (centers index)) * kernel.val colors centers) •
        ∏ slot, normalizedSlot security order horder colors centers slot





def normalizedResponse (security order : ℕ) (horder : 1 ≤ order) (family : Family security order) :
    Family security order :=
  ∑ arity : TruncatedArity order, normalizedJoint security order horder (family arity)



end
end CurrentAFT.CompleteRaisingEvaluation

end

section















/-! # The true independent-root conditional PGF is the normalized baseline

This identifies the empty root component of the actual selected experiment
with the previously constructed joint normalized coefficient response.
All original control references and the full joint canonical kernel remain
inside the finite source sum.
-/
namespace CurrentAFT.RootIndependentSelectedPhysical
open AFT AFT.RepresentedPolynomial ActualBlockFock TaggedSelection PairedRootPlacement
  PairedRootInput CycleRootExpansion ControlCoordinates ControlProduct GradedControlAlgebra
  LocalCoefficientFamily RaisingPatternBudget FinitePolynomialTensor
  DiffuseProfiles ProposalPrimary ActualControls CompleteRaisingEvaluation
  RootConditionalComponent
open scoped BigOperators Classical
noncomputable section
local instance baselineFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance baselineVertexDecidableEq (security : ℕ) : DecidableEq (Vertex security) :=
  instDecidableEqFin (Parameters.bodySize security)
local instance baselineSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance baselineProdDecidableEq {Left Right : Type*} : DecidableEq (Left × Right) := Classical.decEq _
local instance baselineSubtypeDecidableEq {Index : Type*} {predicate : Index → Prop} : DecidableEq (Subtype predicate) := Classical.decEq _
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount primaryLaw bodyReference

abbrev Palette (security : ℕ) := ActualControls.Palette security

def normalizedRole (security order : ℕ) (horder : 1 ≤ order) (r s : ℕ) :
    (role : Role r s) → (RoleInput security r s role → ℝ) →ₗ[ℝ] Family security order
  | .inl _ => RaisingChannels.primaryLeading security order horder + RaisingChannels.primaryRaised security order horder
  | .inr _ => RaisingChannels.bodyLeading security order horder + RaisingChannels.bodyRaised security order horder

def normalizedPoint (security order : ℕ) (horder : 1 ≤ order) (r s : ℕ) :
    (role : Role r s) → RoleInput security r s role → Family security order
  | .inl _, source => NormalizedLocalPolynomial.independentNormalized security order
      (GlobalRaising.primaryAtom security source).val
  | .inr _, source => OrdinaryRaising.normalizedFamily security order horder
      (CompleteRaising.bodyAtom security source).val (CompleteRaising.bodyAtom security source).property














 instance emptyHitKeptIsEmpty {security r s : ℕ} (selection : Selection security r s) :
    IsEmpty (HitKept selection ∅) := ⟨fun index => Finset.notMem_empty index.val.val index.property⟩











end
end CurrentAFT.RootIndependentSelectedPhysical

end

section



















/-! # The complete physical response, with all actual finite averages -/
namespace CurrentAFT.ActualCompletePhysical
open AFT AFT.RepresentedPolynomial ActualBlockFock TaggedSelection ControlCoordinates
  LocalCoefficientFamily GradedControlAlgebra CycleRootExpansion ActualLayouts
  ActualRootDefectPhysical RootActualOutputPolynomial RootIndependentSelectedPhysical
  PhysicalPolynomialAverages LocalReferenceEnergy ActualFockBound ActualRootFamily
  ConditionalHistogramMean UniformTaggedOutput CompleteRaisingEvaluation ActualCycleMeanMGF
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance finDecEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance sumDecEq {First Second : Type*} : DecidableEq (First ⊕ Second) := Classical.decEq _
local instance vertexDecEq (security : ℕ) : DecidableEq (Vertex security) :=
  instDecidableEqFin (Parameters.bodySize security)
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount



def selectedGenerating (security order : ℕ) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : RoleIndex security ≃ BodyIndex security) (arity : TruncatedArity order)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security)
      arity.val.1.val arity.val.2.val) : MvPolynomial (ActualControls.Palette security) ℝ :=
  ∑ choice : Choice security arity.val.1.val arity.val.2.val,
    (choiceLaw security arity.val.1.val arity.val.2.val
      (ActualRootFamily.primary_room security order hroom arity)
      (ActualRootFamily.body_room security order hroom arity)).weight choice •
        expectationLinear (FiniteDist.uniform (Equiv.Perm (BodyIndex security)))
          (fun permutation => centeredGeneratingLinear (uniformReference security).weight
            (TaggedOutputFock.outputMass security arity.val.1.val arity.val.2.val
              (selection security arity.val.1.val arity.val.2.val choice) layout queue permutation kernel.val))



def familyGenerating (security order : ℕ) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : RoleIndex security ≃ BodyIndex security) (family : Family security order) :
    MvPolynomial (ActualControls.Palette security) ℝ :=
  ∑ arity : TruncatedArity order, selectedGenerating security order hroom queue layout arity (family arity)





end
end CurrentAFT.ActualCompletePhysical

end

section












/-! # The literal coefficient-family output PGF -/
namespace CurrentAFT.ActualFamilyPolynomial
open AFT AFT.RepresentedPolynomial PhysicalPolynomialAverages CoefficientOutputFock
  UniformTaggedOutput ActualFockBound ConditionalHistogramMean ActualCycleMeanMGF
  LocalReferenceEnergy CycleRootExpansion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance finDecEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount







end
end CurrentAFT.ActualFamilyPolynomial

end

section













/-! # The scalar arity is the literal unselected positive output law -/
namespace CurrentAFT.RootScalarOutputPolynomial
open AFT AFT.RepresentedPolynomial ActualBlockFock ActualBlockMean ActualFockBound
  ActualCycleMeanMGF TaggedSelection TaggedOutputFock CycleRootExpansion ActualLayouts
  LocalReferenceEnergy ControlCoordinates GradedControlAlgebra RootActualOutputPolynomial
  RootBackgroundPolynomial RootLocalDenominators
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount



def blockPolynomial (security : ℕ) (queue : ℤ) (roots : BlockIndex security → ℤ) :
    MvPolynomial (ActualControls.Palette security) ℝ :=
  centeredGeneratingLinear (uniformReference security).weight
    (BlockProducts.blockMass (Slots security) (TypedTaggedPhysical.blockLaw security queue roots))











end
end CurrentAFT.RootScalarOutputPolynomial

end

section















namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.PhysicalPolynomialAverages
end CurrentAFT.PhysicalPolynomialAverages





/-! # Actual complete output PGF and its coefficient response -/
namespace CurrentAFT.ActualCompletePhysical
open AFT AFT.RepresentedPolynomial ActualBlockFock TaggedSelection ControlCoordinates
  LocalCoefficientFamily GradedControlAlgebra CycleRootExpansion ActualLayouts
  ActualRootDefectPhysical RootActualOutputPolynomial RootIndependentSelectedPhysical
  PhysicalPolynomialAverages LocalReferenceEnergy ActualFockBound ActualRootFamily
  ConditionalHistogramMean UniformTaggedOutput CompleteRaisingEvaluation ActualCycleMeanMGF
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance pgfFinDecEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount









end
end CurrentAFT.ActualCompletePhysical

end

section















/-! # Exact physical calibration and the actual positive protected law

All response, Fourier, moment and charge estimates are proved for the
constructed weight. No physical-calibration premise remains in this file.
The finite positive law is not a finite-bit sampler or an unprotected
Gaussian affine-transport theorem.
-/
namespace CurrentAFT.ActualCalibrationExact
open AFT ActualCompleteStability ActualCalibrationFourier ActualCalibrationRates
  ActualCompletePhysical ActualLayouts ConditionalHistogramMean ActualCycleMeanMGF
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance exactFinDecEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount











end
end CurrentAFT.ActualCalibrationExact

end

section















/-!
# Auxiliary activation refresh in the clipped and charged public law

This is a full-core identity.  It does not condition the Gaussian source on
activation.  The positive multiplier ignores activation bits, and their
fresh reference law can be integrated before applying the real public chart
completion.
-/

namespace CurrentAFT.AffineActivationFubini

open AFT AffineFlagCalibration ActualPublicCharge ActualPublicLegCharge
  ActualAffineCompletedOutput DiffuseProfiles ProposalPrimary LocalReferenceEnergy
  PublicOutputExperiment PublicAuxiliaryFubini ActualCycleMeanMGF ConditionalHistogramMean
open scoped BigOperators Classical

noncomputable section

local instance activationFubiniFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance activationFubiniProdDecidableEq {A B : Type*} : DecidableEq (A × B) := Classical.decEq _
local instance activationPublicIndexDecidableEq (security : ℕ) : DecidableEq (PublicIndex security) :=
  @instDecidableEqSum _ _ (instDecidableEqFin _) (instDecidableEqFin _)
local instance activationBodyIndexDecidableEq (security : ℕ) : DecidableEq (BodyIndex security) :=
  instDecidableEqFin _
local instance activationEndpointIndexDecidableEq (security : ℕ) :
    DecidableEq (Fin (Parameters.dimension security)) := instDecidableEqFin _
local instance activationQueueIndexDecidableEq (security : ℕ) :
    DecidableEq (Fin (Parameters.modulus security)) := instDecidableEqFin _
local instance activationAnchorNonempty (security : ℕ) : Nonempty (InwardAnchor.Index security) :=
  ⟨⟨0, InwardAnchor.anchorWidth_pos security⟩⟩
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount



abbrev LegAux (security : ℕ) :=
  (Bool × (InwardAnchor.Index security × LocalReferenceEnergy.BlurSeed security)) ×
    AffineFlagCalibration.Palette security

def legAuxLaw (security : ℕ) : FiniteDist (LegAux security) :=
  ((FiniteDist.uniform Bool).prod
    ((FiniteDist.uniform (InwardAnchor.Index security)).prod (publicBlurLaw security))).prod (safeLaw security)

def joinLeg (security : ℕ) (flag : Bool) (aux : LegAux security) : LegCore security :=
  (⟨flag, aux.1.1, aux.1.2.1, aux.1.2.2⟩, aux.2)





def legRefresh (security : ℕ) (seed : LegCore security) : FiniteDist (LegCore security) :=
  (activationLaw security).map (fun flag => (setMarked security seed.1 flag, seed.2))



def updateLegs (security : ℕ) (legs : Fin (Parameters.legCount security) → LegCore security)
    (bits : Fin (Parameters.legCount security) → Bool) :
    Fin (Parameters.legCount security) → LegCore security :=
  fun leg => (setMarked security (legs leg).1 (bits leg), (legs leg).2)











local instance activationOutputEndpointDecidableEq (security : ℕ) :
    DecidableEq (Fin (Parameters.dimension security)) := Classical.decEq _





end
end CurrentAFT.AffineActivationFubini

end

section






/-! # Integral basis of the actual placed body path and two-edge legs

The load is written in the manuscript's body, primary, companion order.
Its inverse reads both leg edges and then solves the remaining body path.
Only the generic integral path basis is reused from the frozen directory.
-/
namespace CurrentAFT.LobsterIncidence
open AFT PublicCharge
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {Leg : Type*} [Fintype Leg] {bodyEdges : ℕ}

abbrev Edges (bodyEdges : ℕ) (Leg : Type*) :=
  (Fin bodyEdges → ℤ) × ((Leg → ℤ) × (Leg → ℤ))

def zeroSum (Index : Type*) [Fintype Index] : Submodule ℤ (Index → ℤ) where
  carrier := {word | ∑ index, word index = 0}
  zero_mem' := by simp
  add_mem' := by intro first second hf hs; simp_all [Finset.sum_add_distrib]
  smul_mem' := by
    intro scalar word hw
    change ∑ index, scalar * word index = 0
    rw [← Finset.mul_sum, hw, mul_zero]

def load (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Leg → Fin (bodyEdges + 1))
    (edges : Edges bodyEdges Leg) : EndpointIndex (bodyEdges + 1) Leg → ℤ
  | .inl vertex => pathLoad bodyEdges edges.1 (placement.symm vertex) +
      attachmentIncrement attachment edges.2.2 vertex
  | .inr (.inl leg) => edges.2.1 leg
  | .inr (.inr leg) => -edges.2.1 leg - edges.2.2 leg

theorem sum_load (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Leg → Fin (bodyEdges + 1)) (edges : Edges bodyEdges Leg) :
    ∑ index, load placement attachment edges index = 0 := by
  simp only [Fintype.sum_sum_type, load, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [placement.symm.sum_comp, sum_attachmentIncrement]
  have h := totalCharge_pathLoad bodyEdges edges.1
  unfold totalCharge at h
  rw [h]
  ring

def firstEdge (word : EndpointIndex (bodyEdges + 1) Leg → ℤ) (leg : Leg) : ℤ := word (.inr (.inl leg))
def secondEdge (word : EndpointIndex (bodyEdges + 1) Leg → ℤ) (leg : Leg) : ℤ :=
  -word (.inr (.inl leg)) - word (.inr (.inr leg))

@[simp] theorem firstEdge_load (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Leg → Fin (bodyEdges + 1)) (edges : Edges bodyEdges Leg) :
    firstEdge (load placement attachment edges) = edges.2.1 := rfl

@[simp] theorem secondEdge_load (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Leg → Fin (bodyEdges + 1)) (edges : Edges bodyEdges Leg) :
    secondEdge (load placement attachment edges) = edges.2.2 := by
  funext leg
  simp only [secondEdge, load]
  ring

def bodyResidual (attachment : Leg → Fin (bodyEdges + 1))
    (word : EndpointIndex (bodyEdges + 1) Leg → ℤ) (vertex : Fin (bodyEdges + 1)) : ℤ :=
  word (.inl vertex) - attachmentIncrement attachment (secondEdge word) vertex

theorem bodyResidual_charge (attachment : Leg → Fin (bodyEdges + 1))
    (word : EndpointIndex (bodyEdges + 1) Leg → ℤ) (hword : ∑ index, word index = 0) :
    ∑ vertex, bodyResidual attachment word vertex = 0 := by
  simp only [bodyResidual, Finset.sum_sub_distrib, sum_attachmentIncrement,
    secondEdge, Finset.sum_neg_distrib]
  simp only [Fintype.sum_sum_type] at hword
  linarith

theorem load_injective (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Leg → Fin (bodyEdges + 1)) : Function.Injective (load placement attachment) := by
  intro first second hequal
  have hfirst := congrArg firstEdge hequal
  have hsecond := congrArg secondEdge hequal
  simp only [firstEdge_load, secondEdge_load] at hfirst hsecond
  have hbody : pathLoad bodyEdges first.1 = pathLoad bodyEdges second.1 := by
    funext vertex
    have h := congrFun hequal (.inl (placement vertex))
    simp only [load, Equiv.symm_apply_apply, hsecond] at h
    exact add_right_cancel h
  exact Prod.ext (pathLoad_injective bodyEdges hbody) (Prod.ext hfirst hsecond)

theorem exists_load (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Leg → Fin (bodyEdges + 1)) (word : EndpointIndex (bodyEdges + 1) Leg → ℤ)
    (hword : ∑ index, word index = 0) : ∃ edges, load placement attachment edges = word := by
  have hroot : totalCharge (fun vertex => bodyResidual attachment word (placement vertex)) = 0 := by
    unfold totalCharge
    rw [Equiv.sum_comp placement]
    exact bodyResidual_charge attachment word hword
  obtain ⟨path, hpath⟩ := AFT.exists_pathLoad bodyEdges _ hroot
  refine ⟨(path, firstEdge word, secondEdge word), ?_⟩
  funext index
  rcases index with vertex | (leg | leg)
  · simp only [load, hpath, Equiv.apply_symm_apply, bodyResidual]
    ring
  · rfl
  · simp only [load, firstEdge, secondEdge]
    ring

def incidenceLinear (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Leg → Fin (bodyEdges + 1)) :
    Edges bodyEdges Leg →ₗ[ℤ] (EndpointIndex (bodyEdges + 1) Leg → ℤ) where
  toFun := load placement attachment
  map_add' first second := by
    funext index
    rcases index with vertex | (leg | leg)
    · have hsplit (leg : Leg) : (if attachment leg = vertex then first.2.2 leg + second.2.2 leg else 0) =
          (if attachment leg = vertex then first.2.2 leg else 0) +
          (if attachment leg = vertex then second.2.2 leg else 0) := by split_ifs <;> simp
      simp only [load, Prod.fst_add, Prod.snd_add, pathLoad_add, Pi.add_apply,
        attachmentIncrement, hsplit, Finset.sum_add_distrib]
      ring
    · rfl
    · simp only [load, Prod.fst_add, Prod.snd_add, Pi.add_apply]
      ring
  map_smul' scalar edges := by
    funext index
    rcases index with vertex | (leg | leg)
    · have hsplit (leg : Leg) : (if attachment leg = vertex then scalar * edges.2.2 leg else 0) =
          scalar * (if attachment leg = vertex then edges.2.2 leg else 0) := by split_ifs <;> simp
      simp only [load, Prod.smul_fst, Prod.smul_snd, pathLoad_smul, Pi.smul_apply, smul_eq_mul,
        attachmentIncrement, hsplit, ← Finset.mul_sum, RingHom.id_apply]
      ring
    · rfl
    · simp only [load, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring

/-- The actual placed incidence is an integral basis, for every attachment
map and every body permutation; no graph or rank hypothesis is assumed. -/
def basis (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Leg → Fin (bodyEdges + 1)) :
    Edges bodyEdges Leg ≃ₗ[ℤ] zeroSum (EndpointIndex (bodyEdges + 1) Leg) :=
  LinearEquiv.ofBijective
    ((incidenceLinear placement attachment).codRestrict _ (sum_load placement attachment)) (by
      constructor
      · intro first second hequal
        exact load_injective placement attachment (congrArg Subtype.val hequal)
      · rintro ⟨word, hword⟩
        obtain ⟨edges, hequal⟩ := exists_load placement attachment word hword
        exact ⟨edges, Subtype.ext hequal⟩)

@[simp] theorem basis_apply (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Leg → Fin (bodyEdges + 1)) (edges : Edges bodyEdges Leg) :
    (basis placement attachment edges).val = load placement attachment edges := rfl

end
end CurrentAFT.LobsterIncidence

end

section






/-! # Physical vertex and source numbering for the current incidence basis -/
namespace CurrentAFT.LobsterCoordinates
open AFT PublicCharge LobsterIncidence
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def edgeIndex (bodyEdges legs : ℕ) :
    (Fin bodyEdges ⊕ (Fin legs ⊕ Fin legs)) ≃ Fin (bodyEdges + (legs + legs)) :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv

def vertexIndex (bodyEdges legs : ℕ) :
    EndpointIndex (bodyEdges + 1) (Fin legs) ≃ Fin (bodyEdges + (legs + legs) + 1) :=
  ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv).trans
    (finCongr (by omega))

def edgeCoordinates (Scalar : Type*) [CommRing Scalar] (bodyEdges legs : ℕ) :
    (Fin (bodyEdges + (legs + legs)) → Scalar) ≃ₗ[Scalar]
      ((Fin bodyEdges → Scalar) × ((Fin legs → Scalar) × (Fin legs → Scalar))) :=
  (LinearEquiv.funCongrLeft Scalar Scalar (edgeIndex bodyEdges legs)).trans
    ((LinearEquiv.sumArrowLequivProdArrow (Fin bodyEdges) (Fin legs ⊕ Fin legs) Scalar Scalar).trans
      (LinearEquiv.prodCongr (LinearEquiv.refl _ _)
        (LinearEquiv.sumArrowLequivProdArrow (Fin legs) (Fin legs) Scalar Scalar)))

def zeroSumCoordinates {Index : Type*} [Fintype Index] (count : ℕ) (numbering : Index ≃ Fin (count + 1)) :
    zeroSum Index ≃ₗ[ℤ] zeroSumLattice count where
  toFun word := ⟨fun index => word.val (numbering.symm index), by
    change ∑ index, word.val (numbering.symm index) = 0
    rw [Equiv.sum_comp numbering.symm]
    exact word.property⟩
  invFun word := ⟨fun index => word.val (numbering index), by
    change ∑ index, word.val (numbering index) = 0
    rw [Equiv.sum_comp numbering]
    exact word.property⟩
  left_inv word := by apply Subtype.ext; funext index; simp
  right_inv word := by apply Subtype.ext; funext index; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def incidenceBasis (bodyEdges legs : ℕ) (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Fin legs → Fin (bodyEdges + 1)) :
    (Fin (bodyEdges + (legs + legs)) → ℤ) ≃ₗ[ℤ] zeroSumLattice (bodyEdges + (legs + legs)) :=
  (edgeCoordinates ℤ bodyEdges legs).trans
    ((LobsterIncidence.basis placement attachment).trans
      (zeroSumCoordinates _ (vertexIndex bodyEdges legs)))



def relabeledBasis (bodyEdges legs : ℕ) (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) :
    (Fin (bodyEdges + (legs + legs)) → ℤ) ≃ₗ[ℤ] zeroSumLattice (bodyEdges + (legs + legs)) :=
  (incidenceBasis bodyEdges legs placement attachment).trans (zeroSumCoordinates _ relabeling)



theorem current_body_positive (security : ℕ) : 0 < Parameters.bodySize security := by
  unfold Parameters.bodySize Parameters.scale
  exact Nat.mul_pos (Parameters.modulus_spec security).2.pos (Nat.pow_pos (Nat.pow_pos (Parameters.base_pos security)))

theorem current_edge_count (security : ℕ) :
    (Parameters.bodySize security - 1) + (Parameters.legCount security + Parameters.legCount security) =
      Parameters.dimension security - 1 := by
  have hbody := current_body_positive security
  unfold Parameters.dimension
  omega

theorem current_vertex_count (security : ℕ) :
    (Parameters.bodySize security - 1) + (Parameters.legCount security + Parameters.legCount security) + 1 =
      Parameters.dimension security := by
  have hbody := current_body_positive security
  unfold Parameters.dimension
  omega

end
end CurrentAFT.LobsterCoordinates

end

section



namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.LegMixer
end CurrentAFT.LegMixer
namespace CurrentAFT.LegMixer.blockCoordinateMixer
end CurrentAFT.LegMixer.blockCoordinateMixer
namespace CurrentAFT.LegMixer.coordinateMixer
end CurrentAFT.LegMixer.coordinateMixer
namespace CurrentAFT.LegMixer.inverseMixer
end CurrentAFT.LegMixer.inverseMixer
namespace CurrentAFT.LegMixer.legIncidence
end CurrentAFT.LegMixer.legIncidence



/-! # The complete integer source mixer and its actual modular determinant -/
namespace CurrentAFT.LobsterMixerMatrix
open AFT LobsterCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {Scalar : Type*} [CommRing Scalar]

def blockMatrix (bodyEdges legs : ℕ) (scale shear : Fin legs → Scalar) :
    Matrix (Fin bodyEdges ⊕ (Fin legs ⊕ Fin legs)) (Fin bodyEdges ⊕ (Fin legs ⊕ Fin legs)) Scalar :=
  Matrix.fromBlocks 1 0 0 (Matrix.fromBlocks (Matrix.diagonal scale) (Matrix.diagonal shear) 0 1)

def numberedMatrix (bodyEdges legs : ℕ) (scale shear : Fin legs → Scalar) :
    Matrix (Fin (bodyEdges + (legs + legs))) (Fin (bodyEdges + (legs + legs))) Scalar :=
  Matrix.reindex (edgeIndex bodyEdges legs) (edgeIndex bodyEdges legs) (blockMatrix bodyEdges legs scale shear)

theorem blockMatrix_det (bodyEdges legs : ℕ) (scale shear : Fin legs → Scalar) :
    (blockMatrix bodyEdges legs scale shear).det = ∏ leg, scale leg := by
  simp [blockMatrix]

theorem numberedMatrix_det (bodyEdges legs : ℕ) (scale shear : Fin legs → Scalar) :
    (numberedMatrix bodyEdges legs scale shear).det = ∏ leg, scale leg := by
  rw [numberedMatrix, Matrix.det_reindex_self, blockMatrix_det]





/-- The exact integer mixer used by the incidence construction reduces to
an invertible matrix whenever each public scale is nonzero modulo q. -/
theorem numberedMatrix_mod_det_nonzero (bodyEdges legs modulus : ℕ) [Fact modulus.Prime]
    (scale shear : Fin legs → ℤ) (hscale : ∀ leg, (scale leg : ZMod modulus) ≠ 0) :
    ((numberedMatrix bodyEdges legs scale shear).det : ZMod modulus) ≠ 0 := by
  rw [numberedMatrix_det, Int.cast_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun leg _ => hscale leg)





theorem relabeled_transport_modular_invertible (bodyEdges legs modulus : ℕ) [Fact modulus.Prime]
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (scale shear : Fin legs → ℤ) (hscale : ∀ leg, (scale leg : ZMod modulus) ≠ 0)
    (correction : Fin (bodyEdges + (legs + legs)) → ℤ) :
    IsUnit ((transportBlockMatrix (bodyEdges + (legs + legs))
      (edgeBasisChangeMatrix _ (relabeledBasis bodyEdges legs placement attachment relabeling))
      (numberedMatrix bodyEdges legs scale shear) correction).map (Int.castRingHom (ZMod modulus))) :=
  tree_transport_modular_invertible _ modulus
    (relabeledBasis bodyEdges legs placement attachment relabeling) _ correction
    (numberedMatrix_mod_det_nonzero bodyEdges legs modulus scale shear hscale)

end
end CurrentAFT.LobsterMixerMatrix

end

section




/-! # Shared baseline, public closure, and integral affine offsets -/
namespace CurrentAFT.AffineBaseline
open AFT PublicCharge LobsterCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {Leg : Type*} [Fintype Leg] {bodyEdges : ℕ}

def baseline (modulus : ℕ) (centers : Fin (bodyEdges + 1) → ℤ) (shift intercept : Leg → ℤ) :
    EndpointIndex (bodyEdges + 1) Leg → ℤ
  | .inl vertex => centers vertex
  | .inr (.inl leg) => intercept leg
  | .inr (.inr leg) => (modulus : ℤ) - 1 + shift leg - intercept leg

theorem sum_baseline (modulus : ℕ) (centers : Fin (bodyEdges + 1) → ℤ) (shift intercept : Leg → ℤ) :
    ∑ index, baseline modulus centers shift intercept index =
      (∑ vertex, centers vertex) + (∑ leg, shift leg) + (Fintype.card Leg : ℤ) * ((modulus : ℤ) - 1) := by
  simp only [Fintype.sum_sum_type, baseline, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

def closure (bodyEdges : ℕ) (scalar : ℤ) (vertex : Fin (bodyEdges + 1)) : ℤ :=
  (if vertex = Fin.last bodyEdges then scalar else 0) - (if vertex = 0 then scalar else 0)

theorem sum_closure (bodyEdges : ℕ) (scalar : ℤ) : ∑ vertex, closure bodyEdges scalar vertex = 0 := by
  simp [closure, Finset.sum_sub_distrib]

def offset (modulus : ℕ) (centers : Fin (bodyEdges + 1) → ℤ) (shift intercept : Leg → ℤ)
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (closureScalar : ℤ) :
    EndpointIndex (bodyEdges + 1) Leg → ℤ :=
  baseline modulus centers shift intercept + Sum.elim
    (fun vertex => closure bodyEdges closureScalar (placement.symm vertex)) (fun _ => 0)

theorem sum_offset (modulus : ℕ) (centers : Fin (bodyEdges + 1) → ℤ) (shift intercept : Leg → ℤ)
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (closureScalar : ℤ) :
    ∑ index, offset modulus centers shift intercept placement closureScalar index =
      (∑ vertex, centers vertex) + (∑ leg, shift leg) + (Fintype.card Leg : ℤ) * ((modulus : ℤ) - 1) := by
  simp only [offset, Pi.add_apply, Finset.sum_add_distrib]
  rw [sum_baseline]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero, add_zero]
  rw [Equiv.sum_comp placement.symm, sum_closure, add_zero]

theorem offset_charge_iff (modulus : ℕ) (centers : Fin (bodyEdges + 1) → ℤ) (shift intercept : Leg → ℤ)
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (closureScalar : ℤ) :
    (modulus : ℤ) ∣ ∑ index, offset modulus centers shift intercept placement closureScalar index ↔
      PublicChargeTest modulus centers shift := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, sum_offset]
  unfold PublicChargeTest
  push_cast
  simp only [ZMod.natCast_self, zero_sub, mul_neg, mul_one]
  constructor <;> intro h <;> linear_combination h

def numberedOffset (bodyEdges legs modulus : ℕ) (centers : Fin (bodyEdges + 1) → ℤ)
    (shift intercept : Fin legs → ℤ) (placement : Equiv.Perm (Fin (bodyEdges + 1))) (closureScalar : ℤ)
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) :
    Fin (bodyEdges + (legs + legs) + 1) → ℤ :=
  fun index => offset modulus centers shift intercept placement closureScalar
    ((vertexIndex bodyEdges legs).symm (relabeling.symm index))

theorem numberedOffset_charge (bodyEdges legs modulus : ℕ) (centers : Fin (bodyEdges + 1) → ℤ)
    (shift intercept : Fin legs → ℤ) (placement : Equiv.Perm (Fin (bodyEdges + 1))) (closureScalar : ℤ)
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (hcharge : PublicChargeTest modulus centers shift) :
    (modulus : ℤ) ∣ totalCharge (numberedOffset bodyEdges legs modulus centers shift intercept placement closureScalar relabeling) := by
  unfold totalCharge numberedOffset
  rw [Equiv.sum_comp relabeling.symm (fun index =>
    offset modulus centers shift intercept placement closureScalar ((vertexIndex bodyEdges legs).symm index)),
    Equiv.sum_comp (vertexIndex bodyEdges legs).symm]
  exact (offset_charge_iff modulus centers shift intercept placement closureScalar).mpr hcharge

/-- The actual baseline and closure offset have a unique integral pullback
through the fixed rounding matrix, after every final endpoint relabeling. -/
theorem offset_integral_preimage (bodyEdges legs modulus : ℕ) (hmodulus : modulus ≠ 0)
    (roundingColumn : Fin (bodyEdges + (legs + legs) + 1) → ℤ)
    (hcolumn : totalCharge roundingColumn = (modulus : ℤ))
    (centers : Fin (bodyEdges + 1) → ℤ) (shift intercept : Fin legs → ℤ)
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (closureScalar : ℤ)
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (hcharge : PublicChargeTest modulus centers shift) :
    ∃! preimage, roundingLoad (bodyEdges + (legs + legs)) roundingColumn preimage =
      numberedOffset bodyEdges legs modulus centers shift intercept placement closureScalar relabeling :=
  unique_integral_preimage _ modulus (by exact_mod_cast hmodulus) roundingColumn hcolumn _
    (numberedOffset_charge bodyEdges legs modulus centers shift intercept placement closureScalar relabeling hcharge)

end
end CurrentAFT.AffineBaseline

end

section




/-! # Actual queue columns and integral affine realization of the lobster load -/
namespace CurrentAFT.AffineRealization
open AFT LobsterCoordinates LobsterMixerMatrix AffineBaseline
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def queueEmbedding (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) :
    Fin modulus ↪ Fin (bodyEdges + (legs + legs) + 1) :=
  queues.trans ((Function.Embedding.inl : Fin (bodyEdges + 1) ↪
    (Fin (bodyEdges + 1) ⊕ (Fin legs ⊕ Fin legs))).trans
      ((vertexIndex bodyEdges legs).toEmbedding.trans relabeling.toEmbedding))

def queueColumn (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) :
    Fin (bodyEdges + (legs + legs) + 1) → ℤ :=
  fun index => if index ∈ Finset.univ.map (queueEmbedding bodyEdges legs modulus queues relabeling) then 1 else 0

theorem queueColumn_charge (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) :
    totalCharge (queueColumn bodyEdges legs modulus queues relabeling) = (modulus : ℤ) := by
  simp [totalCharge, queueColumn]
  exact (Finset.card_image_of_injective _ (queueEmbedding bodyEdges legs modulus queues relabeling).injective).trans
    (by simp)

theorem queue_modulus_le (bodyEdges legs modulus : ℕ) (queues : Fin modulus ↪ Fin (bodyEdges + 1)) :
    modulus ≤ bodyEdges + (legs + legs) + 1 := by
  have h := Fintype.card_le_of_injective queues queues.injective
  simp only [Fintype.card_fin] at h
  omega

def extensionCorrection (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) :
    Fin (bodyEdges + (legs + legs)) → ℤ :=
  Classical.choose (exists_extension_correction _
    (injectionColumn _ modulus) (queueColumn bodyEdges legs modulus queues relabeling)
    ((queueColumn_charge bodyEdges legs modulus queues relabeling).trans
      (totalCharge_injectionColumn _ modulus (queue_modulus_le bodyEdges legs modulus queues)).symm))



def linearPart (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (scale shear : Fin legs → ℤ) :
    ((Fin (bodyEdges + (legs + legs)) → ℤ) × ℤ) →ₗ[ℤ]
      ((Fin (bodyEdges + (legs + legs)) → ℤ) × ℤ) :=
  blockTransport _ (edgeBasisChange _ (relabeledBasis bodyEdges legs placement attachment relabeling))
    (numberedMatrix bodyEdges legs scale shear).mulVecLin
    (extensionCorrection bodyEdges legs modulus queues relabeling)



def offsetCoordinates (bodyEdges legs modulus : ℕ) [NeZero modulus]
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (centers : Fin (bodyEdges + 1) → ℤ) (shift intercept : Fin legs → ℤ)
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (closureScalar : ℤ)
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (hcharge : PublicCharge.PublicChargeTest modulus centers shift) :
    (Fin (bodyEdges + (legs + legs)) → ℤ) × ℤ :=
  Classical.choose (offset_integral_preimage bodyEdges legs modulus (NeZero.ne modulus)
    (injectionColumn _ modulus) (totalCharge_injectionColumn _ modulus (queue_modulus_le bodyEdges legs modulus queues))
    centers shift intercept placement closureScalar relabeling hcharge)





def matrix (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) (scale shear : Fin legs → ℤ) :
    Matrix (Fin (bodyEdges + (legs + legs)) ⊕ Unit) (Fin (bodyEdges + (legs + legs)) ⊕ Unit) ℤ :=
  transportBlockMatrix _ (edgeBasisChangeMatrix _ (relabeledBasis bodyEdges legs placement attachment relabeling))
    (numberedMatrix bodyEdges legs scale shear) (extensionCorrection bodyEdges legs modulus queues relabeling)





theorem matrix_modular_invertible (bodyEdges legs modulus : ℕ) [Fact modulus.Prime]
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (scale shear : Fin legs → ℤ) (hscale : ∀ leg, (scale leg : ZMod modulus) ≠ 0) :
    IsUnit ((matrix bodyEdges legs modulus queues placement attachment relabeling scale shear).map
      (Int.castRingHom (ZMod modulus))) :=
  relabeled_transport_modular_invertible bodyEdges legs modulus placement attachment relabeling scale shear hscale _

end
end CurrentAFT.AffineRealization

end

section













/-! # The natural body and two-leg endpoints are the actual physical slots -/
namespace CurrentAFT.PublicEndpointPlacement
open AFT ActualBlockFock ActualBlockMean ActualCycleMeanMGF ConditionalHistogramMean PublicCoefficientOutput
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

abbrev AssemblyIndex (security : ℕ) :=
  PublicCharge.EndpointIndex (Parameters.bodySize security) (Fin (Parameters.legCount security))

def toPhysical (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) :
    AssemblyIndex security → Sigma (Slots security)
  | .inl vertex => match layout.symm vertex with
    | .inl center => ⟨.inr (.inl center), (0 : Fin 1)⟩
    | .inr (.inl point) => ⟨.inr (.inr point), (0 : Fin 1)⟩
    | .inr (.inr leg) => ⟨.inl leg, (2 : Fin 3)⟩
  | .inr (.inl leg) => ⟨.inl leg, (0 : Fin 3)⟩
  | .inr (.inr leg) => ⟨.inl leg, (1 : Fin 3)⟩

def toAssembly (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) :
    Sigma (Slots security) → AssemblyIndex security
  | ⟨.inl leg, slot⟩ => Fin.cases (.inr (.inl leg))
      (fun slot => Fin.cases (.inr (.inr leg)) (fun _ => .inl (layout (.inr (.inr leg)))) slot) slot
  | ⟨.inr (.inl center), _⟩ => .inl (layout (.inl center))
  | ⟨.inr (.inr point), _⟩ => .inl (layout (.inr (.inl point)))

theorem toAssembly_toPhysical (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (index : AssemblyIndex security) : toAssembly security layout (toPhysical security layout index) = index := by
  rcases index with vertex | (leg | leg)
  · change toAssembly security layout (match layout.symm vertex with
      | .inl center => ⟨.inr (.inl center), (0 : Fin 1)⟩
      | .inr (.inl point) => ⟨.inr (.inr point), (0 : Fin 1)⟩
      | .inr (.inr leg) => ⟨.inl leg, (2 : Fin 3)⟩) = .inl vertex
    generalize hrole : layout.symm vertex = role
    have hvertex : layout role = vertex := by rw [← hrole, Equiv.apply_symm_apply]
    rcases role with center | (point | attached)
    · exact congrArg Sum.inl hvertex
    · exact congrArg Sum.inl hvertex
    · exact congrArg Sum.inl hvertex
  · rfl
  · rfl

theorem toPhysical_toAssembly (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (index : Sigma (Slots security)) : toPhysical security layout (toAssembly security layout index) = index := by
  rcases index with ⟨leg | (center | point), slot⟩
  · change Fin 3 at slot
    fin_cases slot
    · rfl
    · rfl
    · change ((match layout.symm (layout (.inr (.inr leg))) with
        | .inl center => ⟨.inr (.inl center), (0 : Fin 1)⟩
        | .inr (.inl point) => ⟨.inr (.inr point), (0 : Fin 1)⟩
        | .inr (.inr leg) => ⟨.inl leg, (2 : Fin 3)⟩) : Sigma (Slots security)) = _
      rw [Equiv.symm_apply_apply]
      rfl
  · change Fin 1 at slot
    have hslot : slot = (0 : Fin 1) := Subsingleton.elim _ _
    subst slot
    simp only [toAssembly, toPhysical, Equiv.symm_apply_apply]
  · change Fin 1 at slot
    have hslot : slot = (0 : Fin 1) := Subsingleton.elim _ _
    subst slot
    simp only [toAssembly, toPhysical, Equiv.symm_apply_apply]

def endpointEquiv (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) :
    AssemblyIndex security ≃ Sigma (Slots security) where
  toFun := toPhysical security layout
  invFun := toAssembly security layout
  left_inv := toAssembly_toPhysical security layout
  right_inv := toPhysical_toAssembly security layout

def endpointFlatten (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) :
    AssemblyIndex security ≃ Fin (Parameters.dimension security) :=
  (endpointEquiv security layout).trans (flatten security)



end
end CurrentAFT.PublicEndpointPlacement

end

section














namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.CyclePathClosure
end CurrentAFT.CyclePathClosure





/-! # Current public-core geometry and actual integral affine data -/
namespace CurrentAFT.CurrentAffineGeometry
open AFT ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  LobsterCoordinates AffineRealization PublicEndpointPlacement
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

abbrev bodyEdges (security : ℕ) := Parameters.bodySize security - 1
abbrev edgeCount (security : ℕ) := bodyEdges security + (Parameters.legCount security + Parameters.legCount security)

def bodyEquiv (security : ℕ) : BodyIndex security ≃ Fin (bodyEdges security + 1) :=
  finCongr (by have := current_body_positive security; dsimp only [bodyEdges]; omega)

def dimensionEquiv (security : ℕ) : Fin (edgeCount security + 1) ≃ Fin (Parameters.dimension security) :=
  finCongr (current_vertex_count security)

def naturalNumbering (security : ℕ) : AssemblyIndex security ≃ Fin (edgeCount security + 1) :=
  (Equiv.sumCongr (bodyEquiv security) (Equiv.refl _)).trans
    (vertexIndex (bodyEdges security) (Parameters.legCount security))

/-- The final relabeling includes the actual physical-slot flattening. -/
def relabeling (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security) :
    Equiv.Perm (Fin (edgeCount security + 1)) :=
  (naturalNumbering security).symm.trans ((endpointFlatten security layout).trans
    (core.endpointPermutation.symm.trans (dimensionEquiv security).symm))



def placement (security : ℕ) (core : Core security) : Equiv.Perm (Fin (bodyEdges security + 1)) :=
  (bodyEquiv security).symm.trans (core.bodyPermutation.trans (bodyEquiv security))

def queues (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) :
    Fin (Parameters.modulus security) ↪ Fin (bodyEdges security + 1) :=
  (queuePosition security layout).trans (bodyEquiv security).toEmbedding

def attachments (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) :
    Fin (Parameters.legCount security) → Fin (bodyEdges security + 1) :=
  fun leg => bodyEquiv security (attachmentPosition security layout leg)

def centers (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security) :
    Fin (bodyEdges security + 1) → ℤ :=
  fun vertex => centerAt security layout core ((bodyEquiv security).symm vertex)

theorem centers_charge (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (hcharge : publicCharge security core) :
    PublicCharge.PublicChargeTest (Parameters.modulus security) (centers security layout core)
      (legShift security core) := by
  have h := (publicCharge_iff security layout core).mpr hcharge
  unfold PublicCharge.PublicChargeTest centers at *
  rw [Equiv.sum_comp (bodyEquiv security).symm]
  exact h

def unitToFinOne : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv input := by cases input; rfl
  right_inv input := (Fin.eq_zero input).symm

/-- Edge coordinates precede the one queue coordinate, as in the fixed
rounding matrix `[pathIncidence | injectionColumn]`. -/
def coordinateNumbering (security : ℕ) : (Fin (edgeCount security) ⊕ Unit) ≃ Fin (Parameters.dimension security) :=
  ((Equiv.sumCongr (Equiv.refl _) unitToFinOne).trans finSumFinEquiv).trans (dimensionEquiv security)

def matrix (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scale shear : Fin (Parameters.legCount security) → ℤ) :
    Matrix (Fin (Parameters.dimension security)) (Fin (Parameters.dimension security)) ℤ :=
  Matrix.reindex (coordinateNumbering security) (coordinateNumbering security)
    (AffineRealization.matrix (bodyEdges security) (Parameters.legCount security) (Parameters.modulus security)
      (queues security layout) (placement security core) (attachments security layout)
      (relabeling security layout core) scale shear)

theorem matrix_invertible (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scale shear : Fin (Parameters.legCount security) → ℤ)
    (hscale : ∀ leg, (scale leg : ZMod (Parameters.modulus security)) ≠ 0) :
    IsUnit ((matrix security layout core scale shear).map (Int.castRingHom (ZMod (Parameters.modulus security)))) := by
  letI : Fact (Parameters.modulus security).Prime := ⟨(Parameters.modulus_spec security).2⟩
  have h := AffineRealization.matrix_modular_invertible (bodyEdges security) (Parameters.legCount security)
    (Parameters.modulus security) (queues security layout) (placement security core) (attachments security layout)
    (relabeling security layout core) scale shear hscale
  exact h.map (Matrix.reindexAlgEquiv (ZMod (Parameters.modulus security))
    (ZMod (Parameters.modulus security)) (coordinateNumbering security)).toMonoidHom

def offset (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (intercept : Fin (Parameters.legCount security) → ℤ) (closureScalar : ℤ)
    (hcharge : publicCharge security core) : Fin (Parameters.dimension security) → ℤ := by
  letI : NeZero (Parameters.modulus security) := ⟨(Parameters.modulus_spec security).2.ne_zero⟩
  let value := AffineRealization.offsetCoordinates (bodyEdges security) (Parameters.legCount security)
    (Parameters.modulus security) (queues security layout) (centers security layout core)
    (legShift security core) intercept (placement security core) closureScalar (relabeling security layout core)
    (centers_charge security layout core hcharge)
  exact fun index => Sum.elim value.1 (fun _ : Unit => value.2) ((coordinateNumbering security).symm index)

end
end CurrentAFT.CurrentAffineGeometry

end

section











namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.AffineFlagCalibration
end CurrentAFT.AffineFlagCalibration
namespace CurrentAFT.AffineFlagCalibration.SimultaneousLaw
end CurrentAFT.AffineFlagCalibration.SimultaneousLaw



/-! # Exact paired integer carries of the actual public chart law -/
namespace CurrentAFT.CurrentAffineLegCarry
open AFT AFT.BoundaryCalibration AffineFlagCalibration ActualPublicLegCharge
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

local instance modulusPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩

abbrev PublicChart (security : ℕ) := Bool × Chart (ZMod (Parameters.modulus security))

def integerPrimary (security : ℕ) (chart : PublicChart security) (first second : ℤ) : ℤ :=
  (chart.2.1.val : ℤ) + (chart.2.2.1.val : ℤ) * first + (chart.2.2.2.val : ℤ) * second

def integerCompanion (security : ℕ) (shift : ℤ) (chart : PublicChart security)
    (first second : ℤ) : ℤ :=
  (Parameters.modulus security : ℤ) - 1 + shift - second - integerPrimary security chart first second















end
end CurrentAFT.CurrentAffineLegCarry

end

section












namespace CurrentAFT
end CurrentAFT




/-! # Actual integral public affine data, including an always-legal fallback -/
namespace CurrentAFT.CurrentAffineData
open AFT CurrentAffineGeometry CurrentAffineLegCarry ActualPublicCharge
  ActualCycleMeanMGF ConditionalHistogramMean AffineFlagCalibration
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

local instance modulusPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩

structure Data (security : ℕ) where
  matrix : Matrix (Fin (Parameters.dimension security)) (Fin (Parameters.dimension security)) ℤ
  offset : Fin (Parameters.dimension security) → ℤ
  invertible : IsUnit (matrix.map (Int.castRingHom (ZMod (Parameters.modulus security))))

def Data.eval {security : ℕ} (data : Data security) (input : Fin (Parameters.dimension security) → ℤ) :=
  data.matrix.mulVec input + data.offset





def fallback (security : ℕ) : Data security where
  matrix := 1
  offset := 0
  invertible := by simp

abbrev Charts (security : ℕ) := Fin (Parameters.legCount security) → PublicChart security

def scales (security : ℕ) (charts : Charts security) : Fin (Parameters.legCount security) → ℤ :=
  fun leg => (charts leg).2.2.1.val

def shears (security : ℕ) (charts : Charts security) : Fin (Parameters.legCount security) → ℤ :=
  fun leg => (charts leg).2.2.2.val

def intercepts (security : ℕ) (charts : Charts security) : Fin (Parameters.legCount security) → ℤ :=
  fun leg => (charts leg).2.1.val

def Valid (security : ℕ) (core : Core security) (charts : Charts security) : Prop :=
  publicCharge security core ∧ ∀ leg, (charts leg).2.2.1 ≠ 0

def assembled (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (charts : Charts security) (closure : ℤ) (hvalid : Valid security core charts) : Data security where
  matrix := CurrentAffineGeometry.matrix security layout core (scales security charts) (shears security charts)
  offset := CurrentAffineGeometry.offset security layout core (intercepts security charts) closure hvalid.1
  invertible := CurrentAffineGeometry.matrix_invertible security layout core _ _ (by
    intro leg
    simpa [scales] using hvalid.2 leg)

/-- This constructor takes only public data. Every branch returns integral
affine data whose reduction is invertible. -/
def assemble (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (charts : Charts security) (closure : ℤ) : Data security :=
  if hvalid : Valid security core charts then assembled security layout core charts closure hvalid
  else fallback security







end
end CurrentAFT.CurrentAffineData

end

section











/-! # The actual dimension-indexed matrix has the exact integral vertex load -/
namespace CurrentAFT.CurrentAffineLoad
open AFT ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  CurrentAffineGeometry LobsterCoordinates LobsterMixerMatrix AffineBaseline
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def splitSource (security : ℕ) (input : Fin (Parameters.dimension security) → ℤ) :
    (Fin (edgeCount security) → ℤ) × ℤ :=
  (fun edge => input (coordinateNumbering security (.inl edge)),
    input (coordinateNumbering security (.inr ())))

def packSource (security : ℕ) (input : (Fin (edgeCount security) → ℤ) × ℤ) :
    Fin (Parameters.dimension security) → ℤ :=
  fun index => Sum.elim input.1 (fun _ : Unit => input.2) ((coordinateNumbering security).symm index)













/-- The fixed rounding map, with the path columns first and the charge
injection column last. It is independent of all sampled public data. -/
def rounding (security : ℕ) (input : Fin (Parameters.dimension security) → ℤ) :
    Fin (Parameters.dimension security) → ℤ :=
  fun vertex => roundingLoad (edgeCount security) (injectionColumn _ (Parameters.modulus security))
    (splitSource security input) ((dimensionEquiv security).symm vertex)

def load (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scale shear intercept : Fin (Parameters.legCount security) → ℤ) (closureScalar : ℤ)
    (input : Fin (Parameters.dimension security) → ℤ) : Fin (Parameters.dimension security) → ℤ :=
  fun vertex =>
    ((relabeledBasis (bodyEdges security) (Parameters.legCount security)
        (placement security core) (attachments security layout) (relabeling security layout core)
        ((numberedMatrix (bodyEdges security) (Parameters.legCount security) scale shear).mulVec
          (splitSource security input).1)).val +
      (splitSource security input).2 • AffineRealization.queueColumn (bodyEdges security) (Parameters.legCount security)
        (Parameters.modulus security) (queues security layout) (relabeling security layout core) +
      numberedOffset (bodyEdges security) (Parameters.legCount security) (Parameters.modulus security)
        (centers security layout core) (legShift security core) intercept (placement security core) closureScalar
        (relabeling security layout core)) ((dimensionEquiv security).symm vertex)



end
end CurrentAFT.CurrentAffineLoad

end

section











namespace AFT
end AFT




/-! # Actual infinite Gaussian to actual protected-window comparison

The protected real mass is identified with the finite `windowGaussian`
law. Its full countable total variation is controlled by the actual deleted
Gaussian probability, before any source-independent public channel is used.
-/
namespace CurrentAFT.GaussianWindowProtection
open AFT GaussianSource
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def protectedMass (width : ℝ) (cutoff : ℕ) (point : ℤ) : ℝ :=
  restrictWindow (integerMass width) cutoff point / retainedFraction width cutoff























end
end CurrentAFT.GaussianWindowProtection

end

section












/-! # One joint comparison for all actual protected Gaussian scalars -/
namespace CurrentAFT.GaussianProductProtection
open AFT GaussianSource GaussianWindowProtection
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def fullMass (width : ℝ) (count : ℕ) (word : Fin count → ℤ) : ℝ :=
  ∏ index, integerMass width (word index)

def protectedMass (width : ℝ) {count : ℕ} (cutoff : Fin count → ℕ) (word : Fin count → ℤ) : ℝ :=
  ∏ index, GaussianWindowProtection.protectedMass width (cutoff index) (word index)

theorem fullMass_nonneg (width : ℝ) (hwidth : 0 < width) (count : ℕ) (word : Fin count → ℤ) :
    0 ≤ fullMass width count word := Finset.prod_nonneg (fun _ _ => integerMass_nonneg width hwidth _)



theorem fullMass_summable (width : ℝ) (hwidth : 0 < width) (count : ℕ) :
    Summable (fullMass width count) :=
  (countableFiniteProduct_summable_sum count (fun _ => integerMass width)
    (fun _ => integerMass_nonneg width hwidth) (fun _ => summable_integerMass width hwidth)).1



theorem fullMass_sum (width : ℝ) (hwidth : 0 < width) (count : ℕ) :
    (∑' word, fullMass width count word) = 1 := by
  unfold fullMass
  rw [(countableFiniteProduct_summable_sum count (fun _ => integerMass width)
    (fun _ => integerMass_nonneg width hwidth) (fun _ => summable_integerMass width hwidth)).2]
  simp only [integerMass_sum width hwidth, Finset.prod_const_one]





abbrev ProtectedWord {count : ℕ} (cutoff : Fin count → ℕ) := (index : Fin count) → Window (cutoff index)

def sourceEmbedding {count : ℕ} (cutoff : Fin count → ℕ) : ProtectedWord cutoff ↪ (Fin count → ℤ) where
  toFun word index := (word index).val
  inj' := by
    intro first second hequal
    funext index
    exact Subtype.ext (congrFun hequal index)

def protectedLaw (width : ℝ) {count : ℕ} (cutoff : Fin count → ℕ) : FiniteDist (ProtectedWord cutoff) :=
  FiniteDist.dependentIndependent (fun index => windowGaussian width (cutoff index))









end
end CurrentAFT.GaussianProductProtection

end

section














/-! # The current complete Gaussian source and its one protection budget

The body block includes its public closure edge. Every leg contributes two
inputs and the shared queue contributes one input, independently of `q`.
-/
namespace CurrentAFT.CurrentSourceProtection
open AFT GaussianSource GaussianWindowProtection GaussianProductProtection
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.bodySize Parameters.legCount

def sourceCount (security : ℕ) : ℕ := Parameters.bodySize security + (Parameters.legCount security * 2 + 1)
def width (security : ℕ) : ℝ := Parameters.sourceWidth security

theorem width_pos (security : ℕ) : 0 < width security := by
  unfold width Parameters.sourceWidth
  exact_mod_cast Parameters.base_pos security

def cutoff (security : ℕ) (index : Fin (sourceCount security)) : ℕ :=
  if index.val < Parameters.bodySize security then DiffuseProfiles.edgeCutoff security
  else Parameters.sourceCutoff security - 1

def bodyPosition (security : ℕ) (index : Fin (Parameters.bodySize security)) : Fin (sourceCount security) :=
  index.castAdd (Parameters.legCount security * 2 + 1)

def auxPosition (security : ℕ) (index : Fin (Parameters.legCount security * 2 + 1)) : Fin (sourceCount security) :=
  Fin.natAdd (Parameters.bodySize security) index

theorem cutoff_body (security : ℕ) (index : Fin (Parameters.bodySize security)) :
    cutoff security (bodyPosition security index) = DiffuseProfiles.edgeCutoff security := by
  exact if_pos index.isLt

theorem cutoff_aux (security : ℕ) (index : Fin (Parameters.legCount security * 2 + 1)) :
    cutoff security (auxPosition security index) = Parameters.sourceCutoff security - 1 := by
  exact if_neg (Nat.not_lt.mpr (Nat.le_add_right _ _))

def budget (security : ℕ) : ℝ :=
  (Parameters.bodySize security : ℝ) *
      clippingProbability (width security) (DiffuseProfiles.edgeCutoff security + 1 : ℕ) (width_pos security) +
    (Parameters.legCount security * 2 + 1 : ℕ) *
      clippingProbability (width security) (Parameters.sourceCutoff security - 1 + 1 : ℕ) (width_pos security)





def protectedSourceLaw (security : ℕ) : FiniteDist (GaussianProductProtection.ProtectedWord (cutoff security)) :=
  GaussianProductProtection.protectedLaw (width security) (cutoff security)







def protectedBody (security : ℕ) (word : GaussianProductProtection.ProtectedWord (cutoff security))
    (index : Fin (Parameters.bodySize security)) : Window (DiffuseProfiles.edgeCutoff security) :=
  ⟨(word (bodyPosition security index)).val, by
    have h := (word (bodyPosition security index)).property
    simpa only [cutoff_body] using h⟩

def protectedAux (security : ℕ) (word : GaussianProductProtection.ProtectedWord (cutoff security))
    (index : Fin (Parameters.legCount security * 2 + 1)) : Window (Parameters.sourceCutoff security - 1) :=
  ⟨(word (auxPosition security index)).val, by
    have h := (word (auxPosition security index)).property
    simpa only [cutoff_aux] using h⟩











end
end CurrentAFT.CurrentSourceProtection

end

section












/-! # Negligibility of the actual complete-source protection error

The body includes the independent public closure edge, and the queue has
only one Gaussian input. The estimate concerns the whole product source
before any public Markov channel is applied.
-/
namespace CurrentAFT.CurrentSourceTail

open AFT GaussianSource CurrentSourceProtection
open Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1200000

def envelope (security : ℕ) : ℝ :=
  (1 + 4 * (Parameters.base security : ℝ) ^ 2 / Real.pi) *
    Real.exp (-(Real.pi / 8) * (Parameters.base security : ℝ) ^ 2)



















end
end CurrentAFT.CurrentSourceTail

end

section














namespace AFT
end AFT
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.TVBound
end AFT.FiniteDist.TVBound
namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.CurrentSourcePublicTransport
end CurrentAFT.CurrentSourcePublicTransport



/-! # Actual hidden-source coordinates and the independent public closure

The complete comparison source has `dimension + 1` entries. Exactly one
entry is the public closing edge. The other `dimension` entries follow
the fixed rounding-matrix order: body path, first leg inputs, second leg
inputs, and finally the unique queue input.
-/
namespace CurrentAFT.CurrentSourceLayout

open AFT CurrentSourceProtection GaussianProductProtection CurrentAffineGeometry
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.bodySize Parameters.legCount Parameters.dimension

 def moveClosure (Path Legs Queue Closure : Type*) :
    ((Path ⊕ Legs) ⊕ Queue) ⊕ Closure ≃ (Path ⊕ Closure) ⊕ (Legs ⊕ Queue) where
  toFun
    | .inl (.inl (.inl path)) => .inl (.inl path)
    | .inl (.inl (.inr legs)) => .inr (.inl legs)
    | .inl (.inr queue) => .inr (.inr queue)
    | .inr closure => .inl (.inr closure)
  invFun
    | .inl (.inl path) => .inl (.inl (.inl path))
    | .inl (.inr closure) => .inr closure
    | .inr (.inl legs) => .inl (.inl (.inr legs))
    | .inr (.inr queue) => .inl (.inr queue)
  left_inv := by rintro (((path | legs) | queue) | closure) <;> rfl
  right_inv := by rintro ((path | closure) | (legs | queue)) <;> rfl

def bodyNumbering (security : ℕ) :
    (Fin (bodyEdges security) ⊕ Unit) ≃ Fin (Parameters.bodySize security) :=
  ((Equiv.sumCongr (Equiv.refl _) unitToFinOne).trans finSumFinEquiv).trans
    (bodyEquiv security).symm

def auxNumbering (security : ℕ) :
    ((Fin (Parameters.legCount security) ⊕ Fin (Parameters.legCount security)) ⊕ Unit) ≃
      Fin (Parameters.legCount security * 2 + 1) :=
  ((Equiv.sumCongr finSumFinEquiv unitToFinOne).trans finSumFinEquiv).trans
    (finCongr (by omega))

def sourceNumbering (security : ℕ) :
    (Fin (Parameters.dimension security) ⊕ Unit) ≃ Fin (sourceCount security) :=
  (Equiv.sumCongr (coordinateNumbering security).symm (Equiv.refl Unit)).trans
    ((Equiv.sumCongr (Equiv.sumCongr
      (LobsterCoordinates.edgeIndex (bodyEdges security) (Parameters.legCount security)).symm
      (Equiv.refl Unit)) (Equiv.refl Unit)).trans
    ((moveClosure _ _ _ _).trans
    ((Equiv.sumCongr (bodyNumbering security) (auxNumbering security)).trans finSumFinEquiv)))









theorem numbering_closure (security : ℕ) :
    sourceNumbering security (.inr ()) =
      bodyPosition security ((bodyEquiv security).symm (Fin.last (bodyEdges security))) := by
  apply Fin.ext
  simp [sourceNumbering, moveClosure, bodyNumbering, bodyPosition, unitToFinOne]
  rfl

def hiddenWord (security : ℕ) (word : Fin (sourceCount security) → ℤ) :
    Fin (Parameters.dimension security) → ℤ := fun index => word (sourceNumbering security (.inl index))

def closureScalar (security : ℕ) (word : Fin (sourceCount security) → ℤ) : ℤ :=
  word (sourceNumbering security (.inr ()))

def hiddenCoordinates (security : ℕ) (word : Fin (sourceCount security) → ℤ) :
    (Fin (edgeCount security) → ℤ) × ℤ :=
  ((fun edge => hiddenWord security word (coordinateNumbering security (.inl edge))),
    hiddenWord security word (coordinateNumbering security (.inr ())))

def bodyLatent (security : ℕ) (word : Fin (sourceCount security) → ℤ) :
    Fin (Parameters.bodySize security) → ℤ := fun index => word (bodyPosition security index)

def firstInput (security : ℕ) (word : Fin (sourceCount security) → ℤ) :
    Fin (Parameters.legCount security) → ℤ :=
  fun leg => word (auxPosition security (auxNumbering security (.inl (.inl leg))))

def secondInput (security : ℕ) (word : Fin (sourceCount security) → ℤ) :
    Fin (Parameters.legCount security) → ℤ :=
  fun leg => word (auxPosition security (auxNumbering security (.inl (.inr leg))))

def queueInput (security : ℕ) (word : Fin (sourceCount security) → ℤ) : ℤ :=
  word (auxPosition security (Fin.last (Parameters.legCount security * 2)))











/-- This is a genuine coordinate equivalence, including the public closure;
no source coordinate is dropped or duplicated. -/
def splitWord (security : ℕ) : (Fin (sourceCount security) → ℤ) ≃
    (Fin (Parameters.dimension security) → ℤ) × ℤ where
  toFun word := (hiddenWord security word, closureScalar security word)
  invFun pair index := Sum.elim pair.1 (fun _ => pair.2) ((sourceNumbering security).symm index)
  left_inv word := by
    funext index
    change Sum.elim (fun position => word (sourceNumbering security (.inl position)))
      (fun _ : Unit => word (sourceNumbering security (.inr ())))
        ((sourceNumbering security).symm index) = word index
    have h : (fun position => word (sourceNumbering security position)) =
        Sum.elim (fun position => word (sourceNumbering security (.inl position)))
          (fun _ : Unit => word (sourceNumbering security (.inr ()))) := by
      funext position
      rcases position with position | position
      · rfl
      · cases position; rfl
    rw [← h]
    exact congrArg word ((sourceNumbering security).apply_symm_apply index)
  right_inv pair := by
    apply Prod.ext
    · funext index
      simp [hiddenWord]
    · simp [closureScalar]



theorem cutoff_closure (security : ℕ) :
    cutoff security (sourceNumbering security (.inr ())) = DiffuseProfiles.edgeCutoff security := by
  rw [numbering_closure, cutoff_body]

def hiddenCutoff (security : ℕ) (index : Fin (Parameters.dimension security)) : ℕ :=
  cutoff security (sourceNumbering security (.inl index))



def hiddenProtectedWord (security : ℕ) (word : ProtectedWord (cutoff security)) :
    ProtectedWord (hiddenCutoff security) :=
  fun index => word (sourceNumbering security (.inl index))

def protectedClosure (security : ℕ) (word : ProtectedWord (cutoff security)) :
    GaussianSource.Window (DiffuseProfiles.edgeCutoff security) :=
  ⟨(word (sourceNumbering security (.inr ()))).val, by
    simpa only [cutoff_closure] using (word (sourceNumbering security (.inr ()))).property⟩





end
end CurrentAFT.CurrentSourceLayout

end

section










namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.CyclePathClosure
end CurrentAFT.CyclePathClosure



/-! # The actual affine load is the complete endpoint assembly -/
namespace CurrentAFT.LobsterAffineLoad
open AFT PublicCharge LobsterCoordinates LobsterMixerMatrix AffineBaseline AffineRealization
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false







def primary (bodyEdges legs : ℕ) (scale shear intercept : Fin legs → ℤ)
    (input : Fin (bodyEdges + (legs + legs)) → ℤ) : Fin legs → ℤ :=
  fun leg => intercept leg + scale leg * (edgeCoordinates ℤ bodyEdges legs input).2.1 leg +
    shear leg * (edgeCoordinates ℤ bodyEdges legs input).2.2 leg



end
end CurrentAFT.LobsterAffineLoad

end

section

















/-! # The actual dimension-indexed affine map has the natural endpoint load

This pointwise integer identity uses the same two inputs at each leg,
the same closing edge at the body wraparound, and the single shared queue.
The final index is precisely the physical-slot flattening followed by
the core's endpoint permutation.
-/
namespace CurrentAFT.CurrentAffineEndpoint

open AFT ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  CurrentAffineGeometry CurrentAffineLoad CurrentSourceProtection CurrentSourceLayout
  PublicEndpointPlacement PublicCharge LobsterCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount



def primaryOutput (security : ℕ) (scale shear intercept : Fin (Parameters.legCount security) → ℤ)
    (word : Fin (sourceCount security) → ℤ) : Fin (Parameters.legCount security) → ℤ :=
  fun leg => intercept leg + scale leg * firstInput security word leg +
    shear leg * secondInput security word leg

/-- The current natural assembly, before its already specified physical
flattening and final endpoint relabeling. -/
def naturalAssembly (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (scale shear intercept : Fin (Parameters.legCount security) → ℤ)
    (word : Fin (sourceCount security) → ℤ) : AssemblyIndex security → ℤ :=
  assembledEndpoint (centerAt security layout core) (legShift security core)
    ((Parameters.modulus security : ℤ) - 1) (bodyLatent security word) core.bodyPermutation
    (attachmentPosition security layout) (secondInput security word)
    (primaryOutput security scale shear intercept word) (queueSet security layout) (queueInput security word)





end
end CurrentAFT.CurrentAffineEndpoint

end

section



















/-! # Safe baselines and public charge on the actual positive core support -/
namespace CurrentAFT.CurrentPublicSupport
open AFT ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean ProposalPrimary
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount





def SafeCore (security : ℕ) (core : Core security) : Prop :=
  (∀ leg, InwardAnchor.SafeColor security (core.legs leg).2) ∧
    ∀ point, InwardAnchor.SafeColor security (core.queueBaselines point)











end
end CurrentAFT.CurrentPublicSupport

end

section



















/-! # Total carry cancellation for the actual protected affine inputs

Every body coordinate has zero integer carry. Each leg's two off-body
coordinates have cancelling carries for every supported public chart.
The final physical flattening and endpoint permutation preserve their sum.
-/
namespace CurrentAFT.CurrentAffineProtectedCarry

open AFT ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge PublicCharge
  CurrentSourceProtection CurrentSourceLayout CurrentAffineEndpoint CurrentAffineGeometry
  CurrentAffineData CurrentAffineLegCarry CurrentPublicSupport GaussianProductProtection
  PublicEndpointPlacement
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def protectedFirst (security : ℕ) (word : ProtectedWord (cutoff security))
    (leg : Fin (Parameters.legCount security)) : AffineFlagCalibration.Scalar security :=
  protectedAux security word (auxNumbering security (.inl (.inl leg)))

def protectedSecond (security : ℕ) (word : ProtectedWord (cutoff security))
    (leg : Fin (Parameters.legCount security)) : AffineFlagCalibration.Scalar security :=
  protectedAux security word (auxNumbering security (.inl (.inr leg)))



def bodyExtra (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (word : Fin (sourceCount security) → ℤ) (vertex : BodyIndex security) : ℤ :=
  attachmentIncrement (attachmentPosition security layout) (secondInput security word) vertex +
    queueIncrement (queueSet security layout) (queueInput security word) vertex





















end
end CurrentAFT.CurrentAffineProtectedCarry

end

section

















/-! # Actual protected affine endpoints are the completed physical output

The physical word below is evaluated from the real completed public charts
and the same protected first/second sources. Its block coordinates are the
ones of `ActualAffineCompletedOutput`, before the existing flattening and
endpoint permutation.
-/
namespace CurrentAFT.CurrentAffinePhysicalEndpoint

open AFT ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge ActualBlockFock
  ActualBlockMean CurrentSourceProtection CurrentSourceLayout CurrentAffineEndpoint
  CurrentAffineGeometry CurrentAffineData CurrentAffineLegCarry CurrentAffineProtectedCarry
  GaussianProductProtection PublicEndpointPlacement AffineFlagCalibration ProposalPrimary
  PublicCoefficientOutput
open HistogramNormalization
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def blockWord (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (charts : Charts security) (word : ProtectedWord (cutoff security)) :
    Sigma (Slots security) → RefinedPublicOutput.Palette security
  | ⟨.inl leg, slot⟩ => evaluateTriple security
      (attachmentRoots security layout core.bodyPermutation (protectedBody security word) leg)
      (core.controls (.inl leg)).1 (core.legs leg) (charts leg)
      (protectedFirst security word leg) (protectedSecond security word leg) slot
  | ⟨.inr (.inl center), _⟩ => shiftEquiv security
      (centerRoots security layout core.bodyPermutation (protectedBody security word) center)
      (core.controls ((UniformTaggedOutput.centerSplit security).symm center)).2.val
  | ⟨.inr (.inr point), _⟩ => shiftEquiv security
      (queueRoots security layout core.bodyPermutation (protectedBody security word) point +
        queueInput security (sourceEmbedding (cutoff security) word)) (core.queueBaselines point)

def outputWord (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (charts : Charts security) (word : ProtectedWord (cutoff security)) :
    Fin (Parameters.dimension security) → RefinedPublicOutput.Palette security :=
  AFT.relabel (renameWord (flatten security) (blockWord security layout core charts word)) core.endpointPermutation















end
end CurrentAFT.CurrentAffinePhysicalEndpoint

end


