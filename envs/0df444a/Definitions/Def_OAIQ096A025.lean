-- Prove2me | Definitions.Def_OAIQ096A025
-- name    : OAIQ096A025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T04:07:41.603736+00:00
-- url     : https://prove2.me/theorems/3d0ba943-53d3-4d65-9b0f-1240f473aab7
-- title:
--   Definitions bundle OAIQ096A025 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 57 declarations of OpenAI's Lean: 13 definitions and 44 theorems. The definitions and types are `OAI.CubicFirstMoment.cubicThetaBorelInversion`, `OAI.CubicFirstMoment.cubicThetaBorelInversionLinear`, `OAI.CubicFirstMoment.cubicThetaInvertedFiniteExtension`, `OAI.CubicFirstMoment.cubicThetaInvertedFiniteRestriction`, `OAI.CubicFirstMoment.cubicThetaMassRegular`, `OAI.CubicFirstMoment.cubicThetaRamifiedShortContinuation`, `OAI.CubicFirstMoment.cubicThetaRegularizedPrimaryTwist`, `OAI.CubicFirstMoment.cubicThetaRegularizedShiftedFrequency`, `OAI.CubicFirstMoment.cubicThetaShiftedModelSeries`, `OAI.CubicFirstMoment.cubicThetaShiftedModelTerm`, `OAI.CubicFirstMoment.cubicThetaShiftedModelTorus`, `OAI.CubicFirstMoment.cubicThetaShiftedNormalizedCoefficient`, `OAI.CubicFirstMoment.cubicThetaShiftedResidueFactor`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `CubicMoment_Theta_CubicThetaBorelInversion`, `CubicMoment_Theta_CubicThetaBorelRestriction`, `CubicMoment_Theta_CubicThetaFullEisensteinFourier`, `CubicMoment_Theta_CubicThetaInversionEnergyInvolution`, `CubicMoment_Theta_CubicThetaInversionL2Bounds`, `CubicMoment_Theta_CubicThetaInversionPairing`, `CubicMoment_Theta_CubicThetaInversionRestriction`, `CubicMoment_Theta_CubicThetaInvertedCoefficients`, `CubicMoment_Theta_CubicThetaInvertedDirichlet`, `CubicMoment_Theta_CubicThetaInvertedFourier`, `CubicMoment_Theta_CubicThetaInvertedFourierObservable`, `CubicMoment_Theta_CubicThetaInvertedGaussian`, `CubicMoment_Theta_CubicThetaInvertedIncoming`, `CubicMoment_Theta_CubicThetaInvertedRowFourier`, `CubicMoment_Theta_CubicThetaInvertedTorus`, `CubicMoment_Theta_CubicThetaInvertedWindow`, `CubicMoment_Theta_CubicThetaMassResidue`, `CubicMoment_Theta_CubicThetaPositiveCuspRestriction`, `CubicMoment_Theta_CubicThetaPositiveFourierMass`, `CubicMoment_Theta_CubicThetaPositiveFourierObservable`, `CubicMoment_Theta_CubicThetaPositiveRadialNormalization`, `CubicMoment_Theta_CubicThetaPositiveStripPairing`, `CubicMoment_Theta_CubicThetaPositiveZeroWindow`, `CubicMoment_Theta_CubicThetaRamifiedResidueSystem`, `CubicMoment_Theta_CubicThetaRamifiedThreeTwists`, `CubicMoment_Theta_CubicThetaResidueKernelPairing`, `CubicMoment_Theta_CubicThetaResidueNormalization`, `CubicMoment_Theta_CubicThetaShiftedCoefficientNormalization`, `CubicMoment_Theta_CubicThetaShiftedFrequencyContinuation`, `CubicMoment_Theta_CubicThetaShiftedModelSeries`, `CubicMoment_Theta_CubicThetaShiftedResiduePairing`.
--
--   **Imports.** It imports the published bundle `Def_PattersonFirstMoment`; the bundles `OAIQ096A021`, `OAIQ096A022` and `OAIQ096A023` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ096A026`, `OAIQ096A029`, `OAIQ096A030` and `OAIQ096A031`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A021
import Definitions.Def_OAIQ096A022
import Definitions.Def_OAIQ096A023

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaResidueNormalization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Match the actual residue's constant term and frequency lattice with
the normalization of Patterson's theta expansion. This does not identify
the nonzero arithmetic coefficients. -/
noncomputable section
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaResidueScale_constant :
    cubicThetaResidueScale*((3*Real.pi:ℂ)*cubicThetaScatteringResidue)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(cubicThetaConstant:ℂ) := by
  have hr : (Real.sqrt 3:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hz : principalIdealZeta 2≠0 := cubicTheta_principalZeta_two_ne_zero
  have hπ : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hJ : ((9*Real.sqrt 3/2:ℝ):ℂ)*(2*Real.pi/(3*Real.sqrt 3):ℂ)=(3*Real.pi:ℂ) := by
    push_cast
    field_simp
    norm_num
  calc
    _ = cubicThetaResidueScale*(((9*Real.sqrt 3/2:ℝ):ℂ)*
        ((2*Real.pi/(3*Real.sqrt 3):ℂ)*cubicThetaScatteringResidue)) := by rw [← hJ]; ring
    _ = cubicThetaResidueScale*(((9*Real.sqrt 3/2:ℝ):ℂ)*
        ((Real.pi:ℂ)^2/(54*principalIdealZeta 2))) := by
      rw [cubicThetaScatteringResidue,cubicTheta_constant_residue_coefficient]
    _ = _ := by unfold cubicThetaResidueScale; field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveCuspRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual bounded restriction to any positive-height period strip.
Injectivity is replaced by the proved finite multiplicity below height two. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.positiveCuspRestriction_finiteEnergyAdd
lemma cubicThetaPositiveCuspRestriction_finiteEnergy {ε : ℝ} (hε : 0<ε)
    (F : cubicThetaFiniteEnergySections) :
    cubicThetaPositiveCuspRestriction hε (cubicThetaFiniteEnergyEmbedding F)=
      cubicThetaFinitePositiveCuspRestriction hε F :=
  LinearMap.extendOfNorm_eq (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (f:=cubicThetaFinitePositiveCuspRestriction hε) (e:=cubicThetaFiniteEnergyEmbedding)
    cubicThetaFiniteEnergyEmbedding_dense (cubicThetaFinitePositiveCuspRestriction_bound hε) F

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionEnergyInvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inversion is an involutive isometry of the actual energy space and
preserves its mass form. It therefore preserves every spectral kernel. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaInversionEnergy_involutive (u : cubicThetaGlobalEnergySpace) :
    cubicThetaInversionEnergy (cubicThetaInversionEnergy u)=u := by
  refine cubicThetaGlobalEnergyTestLinear_dense.induction_on u
    (isClosed_eq (cubicThetaInversionEnergy.continuous.comp
      cubicThetaInversionEnergy.continuous) continuous_id) ?_
  intro F
  change cubicThetaInversionEnergy (cubicThetaInversionEnergy
    (cubicThetaGlobalEnergyTest F))=cubicThetaGlobalEnergyTest F
  rw [cubicThetaInversionEnergy_test,cubicThetaInversionEnergy_test,
    cubicThetaInversionSmooth_involutive]

lemma cubicThetaInversionEnergy_mass_norm (u : cubicThetaGlobalEnergySpace) :
    ‖cubicThetaGlobalInclusion (cubicThetaInversionEnergy u)‖=
      ‖cubicThetaGlobalInclusion u‖ := by
  refine cubicThetaGlobalEnergyTestLinear_dense.induction_on u
    (isClosed_eq (cubicThetaGlobalInclusion.continuous.comp
      cubicThetaInversionEnergy.continuous).norm cubicThetaGlobalInclusion.continuous.norm) ?_
  intro F
  change ‖cubicThetaGlobalInclusion (cubicThetaInversionEnergy
    (cubicThetaGlobalEnergyTest F))‖=‖cubicThetaGlobalInclusion (cubicThetaGlobalEnergyTest F)‖
  rw [cubicThetaInversionEnergy_test]
  exact (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
    (cubicThetaInversion_test_mass_norm F)

lemma cubicThetaInversionEnergy_mass_inner (u v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaGlobalInclusion (cubicThetaInversionEnergy u))
      (cubicThetaGlobalInclusion (cubicThetaInversionEnergy v))=
        inner ℂ (cubicThetaGlobalInclusion u) (cubicThetaGlobalInclusion v) := by
  exact cubicThetaLinear_inner_of_norm_eq
    (cubicThetaGlobalInclusion.toLinearMap.comp cubicThetaInversionEnergy.toLinearMap)
    cubicThetaGlobalInclusion.toLinearMap cubicThetaInversionEnergy_mass_norm u v

lemma cubicThetaInversionEnergy_pencil_inner (z : ℂ) (u v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaInversionEnergy u)
      (cubicThetaEnergyPencil z (cubicThetaInversionEnergy v))=
        inner ℂ u (cubicThetaEnergyPencil z v) := by
  have hf (a b : cubicThetaGlobalEnergySpace) :
      inner ℂ a (cubicThetaEnergyPencil z b)=inner ℂ a b-
        z*inner ℂ (cubicThetaGlobalInclusion a) (cubicThetaGlobalInclusion b) := by
    change inner ℂ a (b-z • cubicThetaGlobalInclusion.adjoint (cubicThetaGlobalInclusion b))=_
    rw [inner_sub_right,inner_smul_right (𝕜:=ℂ) (E:=cubicThetaGlobalEnergySpace)]
    exact congrArg (fun t : ℂ => inner ℂ a b-z*t)
      (cubicThetaGlobalInclusion.adjoint_inner_right a (cubicThetaGlobalInclusion b))
  rw [hf,hf,cubicThetaInversionEnergy.inner_map_map,cubicThetaInversionEnergy_mass_inner]

theorem cubicThetaInversionEnergy_kernel (z : ℂ) (u : cubicThetaGlobalEnergySpace)
    (hu : cubicThetaEnergyPencil z u=0) :
    cubicThetaEnergyPencil z (cubicThetaInversionEnergy u)=0 := by
  apply ext_inner_left ℂ
  intro v
  have h := cubicThetaInversionEnergy_pencil_inner z (cubicThetaInversionEnergy v) u
  rw [cubicThetaInversionEnergy_involutive,hu,inner_zero_right] at h
  exact h.trans (inner_zero_right v).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport of actual section pairings under inversion. Only the
test section is inverted in the energy-space application. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaInversion_pairing_integral (F G : CubicThetaSection) :
    (∫ q, cubicThetaSectionPairing (cubicThetaInversionSection F) G q
      ∂cubicThetaQuotientMeasure)=
    ∫ q, cubicThetaSectionPairing F (cubicThetaInversionSection G) q
      ∂cubicThetaQuotientMeasure := by
  simp_rw [cubicThetaInversion_pairing]
  exact (cubicThetaIntegralQuotient_measurePreserving cubicThetaFullInversion).integral_comp
    (cubicThetaIntegralQuotientHomeomorph cubicThetaFullInversion).measurableEmbedding
    (cubicThetaSectionPairing F (cubicThetaInversionSection G))

lemma cubicThetaInversionEnergy_mass_flip (u v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaGlobalInclusion (cubicThetaInversionEnergy u))
      (cubicThetaGlobalInclusion v)=
    inner ℂ (cubicThetaGlobalInclusion u)
      (cubicThetaGlobalInclusion (cubicThetaInversionEnergy v)) := by
  have h := cubicThetaInversionEnergy_mass_inner u (cubicThetaInversionEnergy v)
  rw [cubicThetaInversionEnergy_involutive] at h
  exact h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedIncoming
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The incoming cutoff vanishes at the inverted high cusp. The actual
inverted Eisenstein series is consequently square integrable on that strip. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaInvertedEisenstein_strip_memLp {s : ℂ} (hs : 3 < s.re) :
    MemLp (fun p : CubicThetaPoint => cubicThetaEisenstein
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val) s) 2
      (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)) := by
  have h := cubicThetaSection_strip_memLp
    (cubicThetaInversionSection (cubicThetaArithmeticSection s (by linarith)))
    (cubicThetaInversionSection_memLp _ (cubicThetaArithmeticSection_memLp hs))
  apply h.ae_eq
  filter_upwards [ae_restrict_mem (cubicThetaCuspStrip_measurable 2)] with p hp
  change cubicThetaArithmeticRemainder
    (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val) s=_
  exact cubicThetaArithmeticRemainder_inverted (by have h:=hp.1; change 2<p.val.2 at h; linarith) s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionL2Bounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! L2 bounds for the literal inverted restriction of finite-energy
sections. Only the value norm is needed for this transport. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaInversionSection_L2_norm (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    ‖(cubicThetaInversionSection_memLp F hF).toLp
        (cubicThetaSectionRepresentative (cubicThetaInversionSection F))‖=
      ‖hF.toLp (cubicThetaSectionRepresentative F)‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  rw [cubicThetaSectionL2_norm_sq,cubicThetaSectionL2_norm_sq]
  calc
    _ = ∫ q, cubicThetaSectionNorm F
        (cubicThetaIntegralQuotientMap cubicThetaFullInversion q)^2 ∂cubicThetaQuotientMeasure := by
      apply integral_congr_ae
      filter_upwards with q
      rw [cubicThetaInversionSection_norm]
    _ = _ := (cubicThetaIntegralQuotient_measurePreserving cubicThetaFullInversion).integral_comp
      (cubicThetaIntegralQuotientHomeomorph cubicThetaFullInversion).measurableEmbedding
      (fun q => cubicThetaSectionNorm F q^2)

def cubicThetaInvertedFiniteRestriction : cubicThetaFiniteEnergySections →ₗ[ℂ] CubicThetaStripL2 where
  toFun F := (cubicThetaSection_strip_memLp (cubicThetaInversionSection F)
    (cubicThetaInversionSection_memLp F F.property.2.1)).toLp _
  map_add' _F _G := MemLp.toLp_add _ _
  map_smul' c _F := MemLp.toLp_const_smul c _

lemma cubicThetaInvertedFiniteRestriction_bound (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaInvertedFiniteRestriction F‖≤‖cubicThetaFiniteEnergyValue F‖ := by
  exact (cubicThetaSectionStrip_norm_le (cubicThetaInversionSection F)
    (cubicThetaInversionSection_memLp F F.property.2.1)).trans_eq
      (cubicThetaInversionSection_L2_norm F F.property.2.1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveFourierMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All positive-cutoff Fourier profiles lie in the actual mass closure.
Their pairings are the full positive-height Fourier integrals. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment

lemma cubicThetaPositiveFourierMass_pairing_finite (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ))
    (F : cubicThetaFiniteEnergySections) :
    inner ℂ (cubicThetaPositiveFourierMass h W hε hW hsm) (cubicThetaFiniteMassClosure F)=
      ∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*cubicThetaSectionFourierFunction F h v := by
  change inner ℂ (cubicThetaPositiveFourierProfileL2 h W hε hW) (F.property.2.1.toLp _)=_
  rw [cubicThetaPositiveFourierProfileL2,cubicThetaSectionPairing_L2,
    cubicThetaPositiveFourierProfile_pairing_radial h W hε hW F,
    cubicThetaPositiveRadialIntegral_zero_extension W hε.le hW]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveFourierObservable
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The genuine meromorphic Fourier observable at any positive cutoff.
Its incoming correction is entire and its residue is the actual global mass pairing. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPositiveFourierObservable_meromorphic (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) {s : ℂ} (hs : 1 < s.re) :
    MeromorphicAt (cubicThetaPositiveFourierObservable h W hε hW) s :=
  (cubicThetaArithmeticDistribution_meromorphic _ _ hs).add
    (((cubicThetaIncomingCompactIntegral_differentiable h W hε hW).analyticAt s).meromorphicAt)

lemma cubicThetaPositiveFourierObservable_right (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) {s : ℂ} (hs : 3 < s.re) :
    cubicThetaPositiveFourierObservable h W hε hW s=
      ∫ p,star (cubicThetaFourierStripSeed h W p)*cubicThetaEisenstein p.val s
        ∂cubicThetaPointMeasure := by
  rw [cubicThetaPositiveFourierObservable,cubicThetaArithmeticDistribution_right _ _ hs,
    cubicThetaPositiveFourierProfile_pairing_integral h W hε hW]
  have hR := cubicThetaFourierStripSeed_pair_integrable h W hε hW
    (cubicThetaArithmeticSection s (by linarith))
  have hI := cubicThetaFourierStripSeed_mul_integrable h W hε hW _
    (cubicThetaIncoming_point_continuous s)
  rw [←integral_add hR hI]
  apply integral_congr_ae
  filter_upwards with p
  change star (cubicThetaFourierStripSeed h W p)*cubicThetaArithmeticRemainder p.val s+
    star (cubicThetaFourierStripSeed h W p)*cubicThetaIncomingEisenstein p.val s=_
  rw [cubicThetaArithmeticRemainder]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFullEisensteinFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual initial Eisenstein Fourier coefficient on every positive
horosphere, including below the injective cusp. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaFullTorus_real {v : ℝ} (hv : 0<v) {s : ℂ} (hs : 2 < s.re)
    (x : Fin 2 → ℝ) :
    cubicThetaEisenstein (cubicThetaPeriodCell x,v) s=
      cubicThetaFullTorus v s (fun i => (x i:UnitAddCircle)) := by
  rw [cubicThetaEisenstein_torus hv hs]
  simp only [cubicThetaFullTorus,cubicThetaArithmeticTorus,ContinuousMap.add_apply,
    ContinuousMap.smul_apply,cubicThetaTorusFourier_zero,ContinuousMap.one_apply,
    smul_eq_mul,mul_one]
  ring

attribute [local instance] OAI.CubicFirstMoment.cubicThetaFullEisensteinFourierMeasureSpace
attribute [local instance] OAI.CubicFirstMoment.cubicThetaFullEisensteinFourierProbability
lemma cubicThetaEisenstein_horizontal_coefficient {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2 < s.re) {h : Eisenstein} (hh : h≠0) :
    (∫ z in cubicThetaHorizontalCell,
      star (cubicThetaHorizontalCharacter h z)*cubicThetaEisenstein (z,v) s)=
      (9*Real.sqrt 3/2:ℝ) •
        (((2*Real.pi/(9*Real.sqrt 3):ℂ)*(v:ℂ)^s/Complex.Gamma s)*
          cubicThetaNonzeroFrequencyTerm (0,v) s h) := by
  unfold cubicThetaHorizontalCharacter
  rw [cubicThetaHorizontalCoefficient (fun z => cubicThetaEisenstein (z,v) s)
    (cubicThetaFullTorus v s) h (cubicThetaFullTorus_real hv hs),
    cubicThetaFullTorus_coefficient hv hs hh]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveRadialNormalization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Initial normalization of the full positive-height Fourier observable. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPositiveFourierObservable_iterated (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) {s : ℂ} (hs : 3 < s.re) :
    cubicThetaPositiveFourierObservable h W hε hW s=
      ∫ v in Ioi ε,star (W v)/(v:ℂ)^3*
        ∫ z in cubicThetaHorizontalCell,star (cubicThetaHorizontalCharacter h z)*
          cubicThetaEisenstein (z,v) s := by
  rw [cubicThetaPositiveFourierObservable_right h W hε hW hs]
  have he := cubicThetaFourierStripSeed_pair_on_strip h W hε hW
    (cubicThetaEisensteinSection s (by linarith))
  change (∫ p,star (cubicThetaFourierStripSeed h W p)*cubicThetaEisenstein p.val s
    ∂cubicThetaPointMeasure)=_ at he
  rw [he]
  have hi := cubicThetaPositiveFourierPairing_integrable h W hε hW
    (cubicThetaEisensteinSection s (by linarith))
  have hf := cubicThetaPositiveCuspStrip_fubini hε.le
    (fun y => star (W y.2*cubicThetaHorizontalCharacter h y.1)*cubicThetaEisenstein y s) hi
  change (∫ p in cubicThetaCuspStrip ε,
    star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*cubicThetaEisenstein p.val s
      ∂cubicThetaPointMeasure)=_ at hf
  change (∫ p in cubicThetaCuspStrip ε,star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*
    cubicThetaEisenstein p.val s ∂cubicThetaPointMeasure)=_
  rw [hf]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  dsimp only
  rw [←integral_const_mul]
  apply setIntegral_congr_fun cubicThetaHorizontalCell_measurable
  intro z _
  dsimp only
  rw [star_mul]
  ring

theorem cubicThetaPositiveFourierObservable_normalized {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0)
    {s : ℂ} (hs : 3 < s.re) :
    cubicThetaPositiveFourierObservable h W hε hW s=
      ((Real.pi:ℂ)/Complex.Gamma s)*cubicThetaFrequencyDirichlet h s*
        cubicThetaPositiveRadialTest h W ε s := by
  rw [cubicThetaPositiveFourierObservable_iterated h W hε hW hs,
    cubicThetaPositiveRadialTest,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  rw [cubicThetaEisenstein_horizontal_coefficient (hε.trans hv) (by linarith) hh]
  have hphase : (Real.fourierChar (tracePair 0 (cubicThetaRowFrequency h)):ℂ)=1 := by
    simp [tracePair]
  simp only [cubicThetaNonzeroFrequencyTerm,ite_eq_right hh,hphase,mul_one,Complex.real_smul]
  calc
    _ = (((9*Real.sqrt 3/2:ℝ):ℂ)*(2*Real.pi/(9*Real.sqrt 3):ℂ))*
        (star (W v)*(v:ℂ)^s*
          (∫ t in Ioi (0:ℝ),cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t)/(v:ℂ)^3)/
            Complex.Gamma s*cubicThetaFrequencyDirichlet h s := by ring
    _ = _ := by rw [cubicThetaPeriod_fourier_constant]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaResidueKernelPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual residue pairs with any vector in the theta eigenspace
through the incoming forcing. Its compact-window equation reduces that
pairing to the constant cusp observation. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaKernel_window_balance (v : cubicThetaGlobalEnergySpace)
    (hv : cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (4/3:ℂ)) v=0) :
    inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaForcingL2 (4/3))=
      inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaHighWindowL2 (4/3)) := by
  have hR := cubicThetaEnergyPencil_inner (cubicThetaGlobalSpectralParameter (4/3:ℂ))
    (cubicThetaGlobalEnergyTest (cubicThetaIncomingWindowTest (4/3))) v
  rw [hv,inner_zero_right,cubicThetaGlobalInclusion_test,cubicThetaGlobalEnergyGradient_test] at hR
  have hR' := congrArg (starRingEnd ℂ) hR
  simp only [map_add,map_mul,map_sub,map_zero,map_one,map_ofNat,inner_conj_symm,
    cubicThetaGlobalSpectralParameter] at hR'
  norm_num [starRingEnd_apply] at hR'
  have hW := cubicThetaWindow_global_weak (4/3) v
  have hz : inner ℂ (cubicThetaGlobalEnergyGradient v)
      (cubicThetaGlobalGradient (cubicThetaIncomingWindowTest (4/3)))+
      (4/3:ℂ)*((4/3:ℂ)-2)*inner ℂ (cubicThetaGlobalInclusion v)
        (cubicThetaGlobalMass (cubicThetaIncomingWindowTest (4/3)))=0 := by
    norm_num at hR' ⊢
    linear_combination -hR'
  rw [hz,inner_sub_right] at hW
  exact (sub_eq_zero.mp hW.symm).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal inverted cusp restriction extends continuously from
finite-energy sections and agrees with inversion on the energy completion. -/
noncomputable section
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.instAddCommGroupSubtypeContinuousMapCubicThetaPointComplexMemSubmoduleCubicThetaSectionCubicThetaFiniteEnergySections
lemma cubicThetaInvertedFiniteRestriction_energy_bound :
    ∃ C, ∀ F : cubicThetaFiniteEnergySections,
      ‖cubicThetaInvertedFiniteRestriction F‖≤C*‖cubicThetaFiniteEnergyEmbedding F‖ := by
  refine ⟨1,fun F => ?_⟩
  simpa only [one_mul] using (cubicThetaInvertedFiniteRestriction_bound F).trans
    (cubicThetaGlobalInclusion_bound (cubicThetaFiniteEnergyEmbedding F))

def cubicThetaInvertedFiniteExtension : cubicThetaGlobalEnergySpace →L[ℂ] CubicThetaStripL2 :=
  LinearMap.extendOfNorm (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (E:=cubicThetaFiniteEnergySections) (Eₗ:=cubicThetaGlobalEnergySpace) (F:=CubicThetaStripL2)
    cubicThetaInvertedFiniteRestriction cubicThetaFiniteEnergyEmbedding

lemma cubicThetaInvertedFiniteExtension_finite (F : cubicThetaFiniteEnergySections) :
    cubicThetaInvertedFiniteExtension (cubicThetaFiniteEnergyEmbedding F)=
      cubicThetaInvertedFiniteRestriction F :=
  LinearMap.extendOfNorm_eq (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (f:=cubicThetaInvertedFiniteRestriction) (e:=cubicThetaFiniteEnergyEmbedding)
    cubicThetaFiniteEnergyEmbedding_dense cubicThetaInvertedFiniteRestriction_energy_bound F

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedDirichlet
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact ideal reindexing and Euler factor of the inverted-cusp
constant coefficient, derived from its actual finite character sums. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaInvertedConstantContinuation_right {s : ℂ} (hs : 4/3 < s.re) :
    cubicThetaInvertedConstantDirichlet s=cubicThetaInvertedConstantContinuation s := by
  have ht : 1<(3*s-3).re := by
    simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
    linarith
  rw [cubicThetaInvertedConstantDirichlet_difference hs,
    cubicThetaTotientSeries_zeta_quotient ht,cubicThetaRamifiedDensitySeries_eq ht]
  rw [show -(3*s-3)=3-3*s by ring,show (3*s-3)+1=3*s-2 by ring,
    show -(3*s-2)=2-3*s by ring]
  have he : (3:ℂ)^(2-3*s)=(3:ℂ)^(3-3*s)/3 := by
    rw [show 2-3*s=(3-3*s)+(-1:ℂ) by ring,
      Complex.cpow_add _ _ (by norm_num : (3:ℂ)≠0),Complex.cpow_neg_one]
    ring
  have hn := cubicTheta_ramified_denominator_ne_zero ht
  rw [show (3*s-3)+1=3*s-2 by ring,show -(3*s-2)=2-3*s by ring] at hn
  unfold cubicThetaInvertedConstantContinuation
  rw [he] at hn ⊢
  have hscalar : (1:ℂ)-(2/3)*(3:ℂ)^(3-3*s)/(1-(3:ℂ)^(3-3*s)/3)=
      (1-(3:ℂ)^(3-3*s))/(1-(3:ℂ)^(3-3*s)/3) := by
    apply (eq_div_iff hn).mpr
    rw [sub_mul,one_mul,div_mul_cancel₀ _ hn]
    ring
  calc
    _ = (1-(2/3)*(3:ℂ)^(3-3*s)/(1-(3:ℂ)^(3-3*s)/3))*
        (principalIdealZeta (3*s-3)/principalIdealZeta (3*s-2)) := by ring
    _ = _ := by rw [hscalar]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedGaussian
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Poisson summation for the actual inverted rows d=3a, with their
finite cubic character and the unchanged frequency lattice. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaInvertedGaussianRow_poisson {c : Eisenstein} (hc : primary c)
    (z : ℂ) {t : ℝ} (ht : 0<t) :
    cubicThetaInvertedGaussianRow c z t=
      (2/(9*Real.sqrt 3):ℂ)*∑' h : Eisenstein,
        cubicThetaInvertedGaussCoefficient c h*
          (Real.fourierChar (tracePair z ((h:ℂ)/(3*traceLambda))):ℂ)*
            ((Real.pi/t:ℝ)*(Real.exp
              (-4*Real.pi^2/t*Complex.normSq ((h:ℂ)/(3*traceLambda))):ℝ)) := by
  have hc0 := primary_ne_zero hc
  have hcC : (c:ℂ)≠0 := fun h => hc0 (Subtype.ext h)
  have hc3 : (c:ℂ)/3≠0 := div_ne_zero hcC (by norm_num)
  have hp := poisson_eisenstein_periodic c hc0
    (fun x => cubicSymbol c (3*residueRepresentative c x))
    (cubicThetaShiftedGaussian ((c:ℂ)/3) z hc3 t ht)
  have hleft : (∑' a : Eisenstein,
      cubicSymbol c (3*residueRepresentative c (Ideal.Quotient.mk (modulus c) a))*
        cubicThetaShiftedGaussian ((c:ℂ)/3) z hc3 t ht (a:ℂ))=
      cubicThetaInvertedGaussianRow c z t := by
    apply tsum_congr
    intro a
    rw [cubicThetaInvertedResidueWeight_mk hc,cubicThetaShiftedGaussian_apply]
    congr 4
    field_simp
  rw [hleft] at hp
  have hfreq (h : Eisenstein) : ((h:ℂ)/((c:ℂ)*traceLambda))*((c:ℂ)/3)=
      (h:ℂ)/(3*traceLambda) := by field_simp
  simp_rw [cubicThetaShiftedGaussian_fourier,hfreq] at hp
  change cubicThetaInvertedGaussianRow c z t=
    (2/(Real.sqrt 3*norm c):ℝ) •
      ∑' h : Eisenstein, cubicThetaInvertedGaussCoefficient c h*
        ((Complex.normSq ((c:ℂ)/3):ℂ)*
          (Real.fourierChar (tracePair z ((h:ℂ)/(3*traceLambda))):ℂ)*
            ((Real.pi/t:ℝ)*(Real.exp
              (-4*Real.pi^2/t*Complex.normSq ((h:ℂ)/(3*traceLambda))):ℝ))) at hp
  rw [hp]
  change ((2/(Real.sqrt 3*norm c):ℝ):ℂ)*_=_
  have hf : (∑' h : Eisenstein, cubicThetaInvertedGaussCoefficient c h*
        ((Complex.normSq ((c:ℂ)/3):ℂ)*
          (Real.fourierChar (tracePair z ((h:ℂ)/(3*traceLambda))):ℂ)*
            ((Real.pi/t:ℝ)*(Real.exp
              (-4*Real.pi^2/t*Complex.normSq ((h:ℂ)/(3*traceLambda))):ℝ))))=
      (Complex.normSq ((c:ℂ)/3):ℂ)*∑' h : Eisenstein,
        cubicThetaInvertedGaussCoefficient c h*
          (Real.fourierChar (tracePair z ((h:ℂ)/(3*traceLambda))):ℂ)*
            ((Real.pi/t:ℝ)*(Real.exp
              (-4*Real.pi^2/t*Complex.normSq ((h:ℂ)/(3*traceLambda))):ℝ)) := by
    rw [←tsum_mul_left]
    apply tsum_congr
    intro h
    ring
  rw [hf,←mul_assoc]
  congr 1
  have hN : norm c≠0 := (norm_pos_of_ne_zero hc0).ne'
  rw [Complex.normSq_div]
  norm_num [Complex.normSq_ofReal]
  change (2/(((Real.sqrt 3:ℝ):ℂ)*(norm c:ℂ)))*((norm c:ℂ)/9)=_
  have hNC : (norm c:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hN
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedRowFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual inverted row Fourier expansion, with absolute integrated
summability proved before interchanging its heat integral and lattice sum. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaInvertedRow_heat_poisson {c : Eisenstein} (hc : primary c)
    (z : ℂ) (v : ℝ) (s : ℂ) {t : ℝ} (ht : 0<t) :
    (t:ℂ)^(s-1)*(Real.exp (-v^2*t):ℂ)*cubicThetaInvertedGaussianRow c z t=
      (2*Real.pi/(9*Real.sqrt 3):ℂ)*∑' h : Eisenstein,
        cubicThetaInvertedRowFourierCoefficient c z h*
          cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t := by
  rw [cubicThetaInvertedGaussianRow_poisson hc z ht]
  simp only [←tsum_mul_left]
  apply tsum_congr
  intro h
  have he := cubicThetaRowHeat_factor ht v s h
  change (t:ℂ)^(s-1)*(Real.exp (-v^2*t):ℂ)*
    ((2/(9*Real.sqrt 3):ℂ)*(cubicThetaInvertedGaussCoefficient c h*
      (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*
        ((Real.pi/t:ℝ)*(Real.exp
          (-4*Real.pi^2/t*Complex.normSq (cubicThetaRowFrequency h)):ℝ))))=_
  calc
    _ = (2/(9*Real.sqrt 3):ℂ)*cubicThetaInvertedRowFourierCoefficient c z h*
        ((t:ℂ)^(s-1)*(Real.exp (-v^2*t):ℂ)*
          ((Real.pi/t:ℝ)*(Real.exp
            (-4*Real.pi^2/t*Complex.normSq (cubicThetaRowFrequency h)):ℝ))) := by
      unfold cubicThetaInvertedRowFourierCoefficient
      ring
    _ = _ := by rw [he]; ring

theorem cubicThetaInvertedRow_fourier {c : Eisenstein} (hc : primary c)
    {p : ℂ × ℝ} (hp : 0<p.2) {s : ℂ} (hs : 2 < s.re) :
    Complex.Gamma s*cubicThetaInvertedRowSeries c p s=
      ((p.2/norm c:ℝ):ℂ)^s*(2*Real.pi/(9*Real.sqrt 3):ℂ)*
        ∑' h : Eisenstein, cubicThetaInvertedRowFourierCoefficient c p.1 h*
          (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t) := by
  let : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
  have hs1 : 1 < s.re := by linarith
  have hFi (h : Eisenstein) : IntegrableOn (fun t =>
      cubicThetaInvertedRowFourierCoefficient c p.1 h*
        cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t) (Ioi 0) := by
    apply (cubicThetaDualHeat_integrable hp hs1 _).const_mul
    by_cases hh : h=0
    · simp [hh]
    · exact (cubicThetaRowHeatScale_pos hh).le
  have hi := integral_tsum_of_summable_integral_norm hFi
    (cubicThetaInvertedWeightedHeat_summable hp hs1 hc p.1)
  rw [cubicThetaInvertedRow_mellin hc hp hs]
  calc
    _ = ((p.2/norm c:ℝ):ℂ)^s*((2*Real.pi/(9*Real.sqrt 3):ℂ)*
        ∫ t in Ioi (0:ℝ), ∑' h : Eisenstein,
          cubicThetaInvertedRowFourierCoefficient c p.1 h*
            cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t) := by
      congr 1
      rw [←integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi
        (fun t ht => cubicThetaInvertedRow_heat_poisson hc p.1 p.2 s ht)
    _ = _ := by
      rw [←hi]
      simp only [integral_const_mul,mul_assoc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full actual inverted Eisenstein series and its zero-frequency
row term. The scalar continuation retains the exact archimedean factor. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaEisenstein_inverted_fourier_rows {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2 < s.re) :
    Complex.Gamma s*cubicThetaEisenstein
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p) s=
      ∑' c : Eisenstein, if primary c then
        ((p.2/norm c:ℝ):ℂ)^s*(2*Real.pi/(9*Real.sqrt 3):ℂ)*
          ∑' h : Eisenstein, cubicThetaInvertedRowFourierCoefficient c p.1 h*
            (∫ t in Set.Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t)
        else 0 := by
  rw [cubicThetaEisenstein_inverted_rows hp hs,←tsum_mul_left]
  apply tsum_congr
  intro c
  by_cases hc : primary c
  · simpa only [ite_eq_left hc] using cubicThetaInvertedRow_fourier hc hp hs
  · simp only [ite_eq_right hc,mul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Collect the inverted Fourier coefficients by an absolutely
convergent interchange of the two actual lattice sums. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaEisenstein_inverted_fourier_coefficients {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2 < s.re) :
    Complex.Gamma s*cubicThetaEisenstein
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p) s=
      (2*Real.pi/(9*Real.sqrt 3):ℂ)*(p.2:ℂ)^s*
        ∑' h : Eisenstein, cubicThetaInvertedFrequencyDirichlet h s*
          (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency h)):ℂ)*
          (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t) := by
  let F (c h : Eisenstein) := cubicThetaInvertedFrequencyTerm s h c*
    (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency h)):ℂ)*
    (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t)
  have hF : Summable (fun ch : Eisenstein × Eisenstein => F ch.1 ch.2) :=
    (cubicThetaInvertedFrequency_heat_norm_summable hp hs).of_norm
  have hswap : (∑' c,∑' h,F c h)=(∑' h,∑' c,F c h) := hF.tsum_comm.symm
  rw [cubicThetaEisenstein_inverted_fourier_rows hp hs]
  calc
    _ = ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(p.2:ℂ)^s)*(∑' c,∑' h,F c h) := by
      rw [←tsum_mul_left]
      apply tsum_congr
      intro c
      by_cases hc : primary c
      · rw [ite_eq_left hc,cubicTheta_row_power hp (primary_ne_zero hc),
          ←tsum_mul_left,←tsum_mul_left]
        apply tsum_congr
        intro h
        simp only [F,cubicThetaInvertedFrequencyTerm,ite_eq_left hc,
          cubicThetaInvertedRowFourierCoefficient]
        ring
      · simp [F,cubicThetaInvertedFrequencyTerm,hc]
    _ = ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(p.2:ℂ)^s)*(∑' h,∑' c,F c h) := by rw [hswap]
    _ = _ := by
      congr 1
      apply tsum_congr
      intro h
      dsimp only [F]
      rw [tsum_mul_right,tsum_mul_right,cubicThetaInvertedFrequencyDirichlet_tsum]

theorem cubicThetaEisenstein_inverted_fourier_normalized {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2 < s.re) :
    cubicThetaEisenstein
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p) s=
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(p.2:ℂ)^s/Complex.Gamma s)*
        ∑' h : Eisenstein, cubicThetaInvertedFrequencyDirichlet h s*
          (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency h)):ℂ)*
          (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale h) t) := by
  have hG := Complex.Gamma_ne_zero_of_re_pos (show 0 < s.re by linarith)
  apply mul_left_cancel₀ hG
  rw [cubicThetaEisenstein_inverted_fourier_coefficients hp hs]
  field_simp

theorem cubicThetaEisenstein_inverted_nonzero {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2 < s.re) :
    cubicThetaEisenstein
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p) s=
      cubicThetaInvertedConstantMode p.2 s+
      ((2*Real.pi/(9*Real.sqrt 3):ℂ)*(p.2:ℂ)^s/Complex.Gamma s)*
        ∑' h : Eisenstein, cubicThetaInvertedNonzeroTerm p s h := by
  rw [cubicThetaEisenstein_inverted_fourier_normalized hp hs,
    (cubicThetaInvertedFourierCoefficients_summable hp hs).tsum_eq_add_tsum_ite 0,
    cubicThetaInvertedFrequencyDirichlet_zero,cubicThetaRowHeatScale_zero]
  have hphase : (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency 0)):ℂ)=1 := by
    simp [cubicThetaRowFrequency,tracePair]
  rw [hphase,mul_one,mul_add,cubicTheta_zero_mode_archimedean hp (show 1 < s.re by linarith),
    cubicThetaInvertedConstantMode_eq hp (show 1 < s.re by linarith)]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedTorus
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continuous inverted-cusp Fourier series and its physical mean.
The constant term is obtained by an actual torus projection. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaInvertedTorus_real {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2 < s.re) (x : Fin 2 → ℝ) :
    cubicThetaInvertedTorus v s (fun i => (x i:UnitAddCircle))=
      cubicThetaEisenstein (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion)
        (cubicThetaPeriodCell x,v)) s := by
  rw [cubicThetaEisenstein_inverted_nonzero hv hs]
  simp only [cubicThetaInvertedTorus,ContinuousMap.add_apply,ContinuousMap.smul_apply,
    cubicThetaTorusFourier_zero,ContinuousMap.one_apply,smul_eq_mul,mul_one,
    cubicThetaInvertedTorusRemainder_real hv hs]

attribute [local instance] OAI.CubicFirstMoment.cubicThetaInvertedTorusMeasureSpace
attribute [local instance] OAI.CubicFirstMoment.cubicThetaInvertedTorusProbability
theorem cubicThetaInverted_horizontal_mean {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2 < s.re) :
    (∫ z in cubicThetaHorizontalCell, cubicThetaEisenstein
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) (z,v)) s)=
      (9*Real.sqrt 3/2:ℝ) • cubicThetaInvertedConstantMode v s := by
  have he := cubicThetaHorizontalCoefficient
    (fun z => cubicThetaEisenstein
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) (z,v)) s)
    (cubicThetaInvertedTorus v s) 0 (fun x => (cubicThetaInvertedTorus_real hv hs x).symm)
  rw [cubicThetaInvertedTorus_mean hv hs] at he
  simpa [cubicThetaRowFrequency,tracePair] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded global observation of the inverted Eisenstein series.
The literal strip integral is evaluated by the previously proved physical mean. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaInvertedWindowObservable_right {s : ℂ} (hs : 3 < s.re) :
    cubicThetaInvertedWindowObservable s=
      ∫ p in cubicThetaCuspStrip 2,
        star (cubicThetaHighWindowForcing (4/3) p.val.2)*cubicThetaEisenstein
          (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val) s
        ∂cubicThetaPointMeasure := by
  let F := cubicThetaArithmeticSection s (show 2 < s.re by linarith)
  have hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure :=
    cubicThetaArithmeticSection_memLp hs
  have hI := cubicThetaInversionSection_memLp F hF
  rw [cubicThetaInvertedWindowObservable,cubicThetaArithmeticDistribution_right _ _ hs]
  change (∫ q, cubicThetaSectionPairing
    (cubicThetaInversionSection (cubicThetaHighWindowSection (4/3))) F q
      ∂cubicThetaQuotientMeasure)=_
  rw [cubicThetaInversion_pairing_integral]
  have hp := cubicThetaSectionPairing_L2 (cubicThetaHighWindowSection (4/3))
    (cubicThetaInversionSection F)
    (cubicThetaCompactSection_memLp _ (cubicThetaHighWindowSection_compact (4/3))) hI
  rw [←hp]
  change inner ℂ (cubicThetaHighWindowL2 (4/3)) (hI.toLp _)=_
  rw [cubicThetaHighWindowPairing_section (4/3) _ hI]
  apply setIntegral_congr_fun (cubicThetaCuspStrip_measurable 2)
  intro p hp
  have hheight : 1<p.val.2 := by have h:=hp.1; change 2<p.val.2 at h; linarith
  change inner ℂ (cubicThetaHighWindowForcing (4/3) p.val.2)
    (cubicThetaArithmeticRemainder
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val) s)=_
  rw [cubicThetaArithmeticRemainder_inverted hheight]
  simp only [RCLike.inner_apply,starRingEnd_apply]
  ring

lemma cubicThetaInvertedWindow_integrable {s : ℂ} (hs : 3 < s.re) :
    IntegrableOn (fun p : CubicThetaPoint =>
      star (cubicThetaHighWindowForcing (4/3) p.val.2)*cubicThetaEisenstein
        (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val) s)
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
  have hW := cubicThetaCuspFourierWeight_memLp 0 (cubicThetaHighWindowWeight (4/3))
  have hE := cubicThetaInvertedEisenstein_strip_memLp hs
  have hw : MemLp (fun p : CubicThetaPoint => cubicThetaHighWindowForcing (4/3) p.val.2) 2
      (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)) := by
    change MemLp (fun p : CubicThetaPoint => cubicThetaHighWindowForcing (4/3) p.val.2*
      (Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency 0)):ℂ)) 2
      (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)) at hW
    simpa [cubicThetaRowFrequency,tracePair] using hW
  exact hw.star.integrable_mul hE

lemma cubicThetaInvertedWindowObservable_normalized {s : ℂ} (hs : 3 < s.re) :
    cubicThetaInvertedWindowObservable s=
      ((Real.pi:ℂ)/(s-1))*cubicThetaInvertedConstantContinuation s*
        cubicThetaZeroRadialTest (cubicThetaHighWindowWeight (4/3)) s := by
  rw [cubicThetaInvertedWindowObservable_right hs]
  have hf := cubicThetaCuspStrip_fubini
    (fun y => star (cubicThetaHighWindowForcing (4/3) y.2)*cubicThetaEisenstein
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) y) s)
    (cubicThetaInvertedWindow_integrable hs)
  change (∫ p in cubicThetaCuspStrip 2,
    star (cubicThetaHighWindowForcing (4/3) p.val.2)*cubicThetaEisenstein
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val) s
    ∂cubicThetaPointMeasure)=_ at hf
  rw [hf]
  rw [cubicThetaZeroRadialTest,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  change 2<v at hv
  dsimp only
  have he : (∫ z in cubicThetaHorizontalCell,
      star (cubicThetaHighWindowForcing (4/3) v)*cubicThetaEisenstein
        (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) (z,v)) s/(v:ℂ)^3)=
      (star (cubicThetaHighWindowForcing (4/3) v)/(v:ℂ)^3)*
        ∫ z in cubicThetaHorizontalCell, cubicThetaEisenstein
          (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) (z,v)) s := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    ring
  rw [he,cubicThetaInverted_horizontal_mean (by linarith) (by linarith),
    cubicThetaInvertedConstantMode_eq (by linarith) (by linarith),
    cubicThetaInvertedConstantContinuation_right (by linarith),Complex.real_smul]
  calc
    _ = (((9*Real.sqrt 3/2:ℝ):ℂ)*(2*Real.pi/(9*Real.sqrt 3):ℂ))/(s-1)*
        cubicThetaInvertedConstantContinuation s*
        (star (cubicThetaHighWindowForcing (4/3) v)*(v:ℂ)^(2-s)/(v:ℂ)^3) := by ring
    _ = _ := by rw [cubicThetaPeriod_fourier_constant]; rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedFourierObservable
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonzero Fourier observations at the inverted cusp retain the exact
primary Dirichlet coefficient and the original radial normalization. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.instMeasureSpaceUnitAddCircle_solutions_5
attribute [local instance] OAI.CubicFirstMoment.instIsProbabilityMeasureUnitAddCircleVolume_solutions_1
lemma cubicThetaInverted_horizontal_coefficient {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2 < s.re) {h : Eisenstein} (hh : h≠0) :
    (∫ z in cubicThetaHorizontalCell,
      star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*
        cubicThetaEisenstein (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) (z,v)) s)=
      (9*Real.sqrt 3/2:ℝ) •
        (((2*Real.pi/(9*Real.sqrt 3):ℂ)*(v:ℂ)^s/Complex.Gamma s)*
          cubicThetaInvertedNonzeroTerm (0,v) s h) := by
  rw [cubicThetaHorizontalCoefficient
    (fun z => cubicThetaEisenstein
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) (z,v)) s)
    (cubicThetaInvertedTorus v s) h (fun x => (cubicThetaInvertedTorus_real hv hs x).symm),
    cubicThetaInvertedTorus_coefficient hv hs hh]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedThreeTwists
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All three primary lambda twists inherit actual holomorphic
pole-cleared continuations by cycling the nonzero frequency. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaRegularizedPrimaryTwist (j : Fin 3) (h : Eisenstein) (s : ℂ) : ℂ :=
  cubicThetaRegularizedPrimaryOne (lambdaE^(((j:ℕ)+2)%3)*h) s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedResidueSystem
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal three-row ramified expansion at the actual theta pole.
All unit twists are retained as frequencies of the same arithmetic residue. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaRamifiedShortContinuation (h : Eisenstein) (s : ℂ) : ℂ :=
  ∑' e : Eisensteinˣ, ∑ j : Fin 3, cubicThetaRamifiedFactor e j s h*
    cubicThetaRegularizedPrimaryTwist j (h*(e:Eisenstein)) s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveZeroWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero Fourier mode at every positive cutoff. The incoming Mellin
term is entire and therefore contributes no residue. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.cubicThetaPositiveZeroWindowMeasureSpace
attribute [local instance] OAI.CubicFirstMoment.cubicThetaPositiveZeroWindowProbability
lemma cubicThetaEisenstein_horizontal_zero {v : ℝ} (hv : 0<v)
    {s : ℂ} (hs : 2 < s.re) :
    (∫ z in cubicThetaHorizontalCell,star (cubicThetaHorizontalCharacter 0 z)*
      cubicThetaEisenstein (z,v) s)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicThetaEisensteinConstantMode v s := by
  unfold cubicThetaHorizontalCharacter
  rw [cubicThetaHorizontalCoefficient (fun z => cubicThetaEisenstein (z,v) s)
    (cubicThetaFullTorus v s) 0 (cubicThetaFullTorus_real hv hs),
    cubicThetaFullTorus_zero hv hs]
  rfl

lemma cubicThetaPositiveZeroObservable_normalized (W : C_c(ℝ,ℂ)) {ε : ℝ}
    (hε : 0<ε) (hW : ∀ v≤ε,W v=0) {s : ℂ} (hs : 3 < s.re) :
    cubicThetaPositiveFourierObservable 0 W hε hW s=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*mellin (star W) (s-2)+
      ((Real.pi:ℂ)/(s-1))*cubicThetaConstantContinuation s*mellin (star W) (-s) := by
  rw [cubicThetaPositiveFourierObservable_iterated 0 W hε hW hs]
  calc
    _ = ∫ v in Ioi ε,
        ((9*Real.sqrt 3/2:ℝ):ℂ)*(star (W v)*(v:ℂ)^s/(v:ℂ)^3)+
        ((Real.pi:ℂ)/(s-1))*cubicThetaConstantContinuation s*
          (star (W v)*(v:ℂ)^(2-s)/(v:ℂ)^3) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only
      rw [cubicThetaEisenstein_horizontal_zero (hε.trans hv) (by linarith),
        cubicThetaEisensteinConstantMode_eq (hε.trans hv) (by linarith),
        cubicThetaConstantContinuation_right (by linarith)]
      have he := cubicThetaPeriod_fourier_constant
      linear_combination (star (W v)/(v:ℂ)^3/(s-1)*
        cubicThetaConstantContinuation s*(v:ℂ)^(2-s))*he
    _ = ((9*Real.sqrt 3/2:ℝ):ℂ)*mellin (star W) (s-2)+
        ((Real.pi:ℂ)/(s-1))*cubicThetaConstantContinuation s*mellin (star W) (-s) := by
      rw [integral_add
        ((cubicThetaPositiveWindow_power_integrable W hε hW s).const_mul _)
        ((cubicThetaPositiveWindow_power_integrable W hε hW (2-s)).const_mul _),
        integral_const_mul,integral_const_mul,
        cubicThetaPositiveWindow_power W hε hW s,
        cubicThetaPositiveWindow_power W hε hW (2-s)]
      congr 3
      ring

theorem cubicThetaPositiveZeroObservable_continued (W : C_c(ℝ,ℂ)) {ε : ℝ}
    (hε : 0<ε) (hW : ∀ v≤ε,W v=0) {s : ℂ} (hs : 1 < s.re) :
    cubicThetaPositiveFourierObservable 0 W hε hW =ᶠ[𝓝[≠] s]
      (fun z => ((9*Real.sqrt 3/2:ℝ):ℂ)*mellin (star W) (z-2)+
        ((Real.pi:ℂ)/(z-1))*cubicThetaConstantContinuation z*mellin (star W) (-z)) := by
  have hm := cubicThetaPositiveWindow_entire W hε hW
  have ho : MeromorphicOn (cubicThetaPositiveFourierObservable 0 W hε hW)
      {z : ℂ | 1<z.re} :=
    fun z hz => cubicThetaPositiveFourierObservable_meromorphic 0 W hε hW hz
  have hr : MeromorphicOn (fun z => ((9*Real.sqrt 3/2:ℝ):ℂ)*mellin (star W) (z-2)+
      ((Real.pi:ℂ)/(z-1))*cubicThetaConstantContinuation z*mellin (star W) (-z))
      {z : ℂ | 1<z.re} := by
    intro z _
    exact (((hm.comp (differentiable_id.sub_const 2)).const_mul _).analyticAt z).meromorphicAt.add
      ((((MeromorphicAt.const (Real.pi:ℂ) z).div
        (analyticAt_id.sub analyticAt_const).meromorphicAt).mul
          (cubicThetaConstantContinuation_meromorphic z)).mul
            ((hm.comp differentiable_id.neg).analyticAt z).meromorphicAt)
  apply cubicThetaMeromorphic_identity ho hr (convex_halfSpace_re_gt 1).isPreconnected
    (z₀:=(4:ℂ)) (by norm_num) hs
  have hn : ∀ᶠ z in 𝓝 (4:ℂ),3<z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hn] with z hz
  exact cubicThetaPositiveZeroObservable_normalized W hε hW hz

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveStripPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted Fourier pairing on the actual positive strip, and its
compatibility with the global energy restriction. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment

lemma cubicThetaPositiveRestriction_finite_pairing {ε : ℝ} (hε : 0<ε)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) (hW : ∀ v≤ε,W v=0)
    (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) (F : cubicThetaFiniteEnergySections) :
    inner ℂ (cubicThetaPositiveFourierProfileL2 h W hε hW) (cubicThetaFiniteEnergyValue F)=
      inner ℂ (cubicThetaPositiveStripFourierTest hε h W)
        (cubicThetaFinitePositiveCuspRestriction hε F) := by
  have hf : MemLp (fun p : CubicThetaPoint => cubicThetaSectionFunction F p.val) 2
      (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip ε)) := by
    simpa only [cubicThetaSectionFunction_coordinates] using
      cubicThetaFiniteEnergy_positiveStrip_memLp hε F
  have he := cubicThetaPositiveFourierMass_pairing_finite h W hε hW hsm F
  change inner ℂ (cubicThetaPositiveFourierProfileL2 h W hε hW)
    (cubicThetaFiniteEnergyValue F)=_ at he
  rw [he,←cubicThetaPositiveRadialIntegral_zero_extension W hε.le hW]
  have hto : hf.toLp _=cubicThetaFinitePositiveCuspRestriction hε F := by
    apply Lp.ext
    filter_upwards [hf.coeFn_toLp,
      (cubicThetaFiniteEnergy_positiveStrip_memLp hε F).coeFn_toLp] with p hp hF
    change (hf.toLp _) p=((cubicThetaFiniteEnergy_positiveStrip_memLp hε F).toLp _) p
    rw [hp,hF,cubicThetaSectionFunction_coordinates]
  rw [←hto,cubicThetaPositiveStrip_inner_formula hε]
  rfl

theorem cubicThetaPositiveRestriction_pairing {ε : ℝ} (hε : 0<ε)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) (hW : ∀ v≤ε,W v=0)
    (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) (u : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaPositiveFourierProfileL2 h W hε hW) (cubicThetaGlobalInclusion u)=
      inner ℂ (cubicThetaPositiveStripFourierTest hε h W) (cubicThetaPositiveCuspRestriction hε u) := by
  refine cubicThetaFiniteEnergyEmbedding_dense.induction_on u
    (isClosed_eq (continuous_const.inner cubicThetaGlobalInclusion.continuous)
      (continuous_const.inner (cubicThetaPositiveCuspRestriction hε).continuous)) ?_
  intro F
  rw [cubicThetaFiniteEnergyEmbedding_value,cubicThetaPositiveCuspRestriction_finiteEnergy]
  exact cubicThetaPositiveRestriction_finite_pairing hε h W hW hsm F

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBorelRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The completed positive-strip restriction is the actual measurable
lift from the quotient, including its cubic automorphy factor. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

theorem cubicThetaPositiveCuspRestriction_borel {ε : ℝ} (hε : 0<ε)
    (u : cubicThetaGlobalEnergySpace) :
    cubicThetaPositiveCuspRestriction hε u=
      cubicThetaBorelRestriction hε (cubicThetaGlobalInclusion u) := by
  refine cubicThetaFiniteEnergyEmbedding_dense.induction_on u
    (isClosed_eq (cubicThetaPositiveCuspRestriction hε).continuous
      ((cubicThetaBorelRestriction hε).continuous.comp cubicThetaGlobalInclusion.continuous)) ?_
  intro F
  rw [cubicThetaPositiveCuspRestriction_finiteEnergy,cubicThetaFiniteEnergyEmbedding_value,
    cubicThetaBorelRestriction_finite]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBorelInversion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual inversion operator on quotient representatives, including
the cubic phase of the chosen Borel section. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaBorelInversionFunction_memLp (f : CubicThetaGlobalL2) :
    MemLp (cubicThetaBorelInversionFunction f) 2 cubicThetaQuotientMeasure := by
  have hf := (Lp.memLp f).comp_measurePreserving
    (cubicThetaIntegralQuotient_measurePreserving cubicThetaFullInversion)
  apply (memLp_norm_iff (cubicThetaBorelInversionFunction_measurable
    (Lp.stronglyMeasurable f).measurable).aestronglyMeasurable).mp
  simpa only [cubicThetaBorelInversionFunction_norm,Function.comp_def] using hf.norm

def cubicThetaBorelInversionLinear : CubicThetaGlobalL2 →ₗ[ℂ] CubicThetaGlobalL2 where
  toFun f := (cubicThetaBorelInversionFunction_memLp f).toLp _
  map_add' f g := by
    apply Lp.ext
    have hsum := (cubicThetaIntegralQuotient_measurePreserving
      cubicThetaFullInversion).quasiMeasurePreserving.ae (Lp.coeFn_add f g)
    filter_upwards [(cubicThetaBorelInversionFunction_memLp (f+g)).coeFn_toLp,
      (cubicThetaBorelInversionFunction_memLp f).coeFn_toLp,
      (cubicThetaBorelInversionFunction_memLp g).coeFn_toLp,
      Lp.coeFn_add ((cubicThetaBorelInversionFunction_memLp f).toLp _)
        ((cubicThetaBorelInversionFunction_memLp g).toLp _),hsum] with q hfg hf hg hadd hq
    change ((cubicThetaBorelInversionFunction_memLp (f+g)).toLp _) q=_
    rw [hfg,hadd]
    simp only [Pi.add_apply]
    rw [hf,hg]
    simp only [Pi.add_apply] at hq
    simp only [cubicThetaBorelInversionFunction,cubicThetaBorelLift,
      ←cubicThetaIntegralQuotientMap_apply,cubicThetaBorelSection_rightInverse q]
    rw [hq,mul_add]
  map_smul' c f := by
    apply Lp.ext
    have hsum := (cubicThetaIntegralQuotient_measurePreserving
      cubicThetaFullInversion).quasiMeasurePreserving.ae (Lp.coeFn_smul c f)
    filter_upwards [(cubicThetaBorelInversionFunction_memLp (c • f)).coeFn_toLp,
      (cubicThetaBorelInversionFunction_memLp f).coeFn_toLp,
      Lp.coeFn_smul c ((cubicThetaBorelInversionFunction_memLp f).toLp _),hsum]
      with q hcf hf hsm hq
    change ((cubicThetaBorelInversionFunction_memLp (c • f)).toLp _) q=_
    simp only [RingHom.id_apply]
    rw [hcf,hsm]
    simp only [Pi.smul_apply]
    rw [hf]
    simp only [Pi.smul_apply,smul_eq_mul] at hq ⊢
    simp only [cubicThetaBorelInversionFunction,cubicThetaBorelLift,
      ←cubicThetaIntegralQuotientMap_apply,cubicThetaBorelSection_rightInverse q]
    rw [hq]
    ring

lemma cubicThetaBorelInversionLinear_norm (f : CubicThetaGlobalL2) :
    ‖cubicThetaBorelInversionLinear f‖=‖f‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  rw [cubicTheta_l2_norm_sq_measure,cubicTheta_l2_norm_sq_measure]
  calc
    _ = ∫ q,‖f (cubicThetaIntegralQuotientMap cubicThetaFullInversion q)‖^2
        ∂cubicThetaQuotientMeasure := by
      apply integral_congr_ae
      filter_upwards [(cubicThetaBorelInversionFunction_memLp f).coeFn_toLp] with q hq
      change ‖((cubicThetaBorelInversionFunction_memLp f).toLp _) q‖^2=_
      rw [hq,cubicThetaBorelInversionFunction_norm]
    _ = _ := (cubicThetaIntegralQuotient_measurePreserving cubicThetaFullInversion).integral_comp
      (cubicThetaIntegralQuotientHomeomorph cubicThetaFullInversion).measurableEmbedding
      (fun q => ‖f q‖^2)

def cubicThetaBorelInversion : CubicThetaGlobalL2 →ₗᵢ[ℂ] CubicThetaGlobalL2 :=
  ⟨cubicThetaBorelInversionLinear,cubicThetaBorelInversionLinear_norm⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedFrequencyContinuation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continue the actual translated-cusp Dirichlet coefficients through
the already proved primary family. No cusp transform is postulated. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaRegularizedShiftedFrequency (b : ℤ) (h : Eisenstein) (s : ℂ) : ℂ :=
  if (3:Eisenstein) ∣ h-lambdaE*(b:Eisenstein) then
    9*cubicThetaRegularizedPrimaryOne (lambdaE*h) s else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedResiduePairing
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted height identities for the actual translated theta coefficients. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaShiftedResidueFactor (n : ℤ) (h : Eisenstein) : ℂ :=
  cubicThetaResidueScale*((Real.pi:ℂ)/Complex.Gamma (4/3))*
    cubicThetaRegularizedShiftedFrequency n h (4/3)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedCoefficientNormalization
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The other-cusp Whittaker coefficients have the explicit arithmetic
normalization, with the same actual scalar as the original cusp. -/
noncomputable section
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaShiftedNormalizedCoefficient (n : ℤ) (h : Eisenstein) : ℂ :=
  (cubicThetaShiftedResidueFactor n h*
    ((2*(cubicThetaShiftedRowHeatScale h)^(1/6:ℝ)/‖cubicThetaShiftedRowFrequency h‖:ℝ):ℂ))/
    ((81*Real.sqrt 3/2:ℝ):ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedModelSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The absolutely convergent arithmetic series determined by the proved
other-cusp coefficients. Its constant coefficient is explicitly zero. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaShiftedModelTerm (n : ℤ) (v : ℝ) (h : Eisenstein) : ℂ :=
  if h=0 then 0 else cubicThetaShiftedNormalizedCoefficient n h*
    cubicThetaWhittaker (‖cubicThetaShiftedRowFrequency h‖*v)

def cubicThetaShiftedModelTorus (n : ℤ) (v : ℝ) : C(UnitAddTorus (Fin 2),ℂ) :=
  ∑' h : Eisenstein,cubicThetaShiftedModelTerm n v h • cubicThetaTorusFourier h

def cubicThetaShiftedModelSeries (n : ℤ) (z : ℂ) (v : ℝ) : ℂ :=
  ∑' h : Eisenstein,cubicThetaShiftedModelTerm n v h*
    (Real.fourierChar (tracePair z (cubicThetaShiftedRowFrequency h)):ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMassResidue
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact residue of the arithmetic coefficient-energy Dirichlet series.
This is an arithmetic calculation, before comparison with the global norm. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

def cubicThetaMassRegular (s : ℂ) : ℂ :=
  cubicThetaMassEulerPrefactor s * principalZetaRegularFactor (1+s) *
    principalIdealZeta (2+3*s) / principalIdealZeta (2+2*s)

end CubicFirstMoment

end

end OAI
end


