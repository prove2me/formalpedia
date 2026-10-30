-- Prove2me | Definitions.Def_OAIQ096A023
-- name    : OAIQ096A023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T03:58:14.865194+00:00
-- url     : https://prove2.me/theorems/6cee3a68-dc2c-4d32-89a9-34f5c7525172
-- title:
--   Definitions bundle OAIQ096A023 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 99 declarations of OpenAI's Lean: 42 definitions and 57 theorems. The definitions and types are `OAI.CubicFirstMoment.cubicThetaBorelRestriction`, `OAI.CubicFirstMoment.cubicThetaBorelRestrictionLinear`, `OAI.CubicFirstMoment.cubicThetaCompactBorelRestriction`, `OAI.CubicFirstMoment.cubicThetaCompactBorelRestrictionLinear`, `OAI.CubicFirstMoment.cubicThetaCompactIntegralRestriction`, `OAI.CubicFirstMoment.cubicThetaCompactShiftedFamily`, `OAI.CubicFirstMoment.cubicThetaCompactShiftedObservation`, `OAI.CubicFirstMoment.cubicThetaCuspExpansion`, `OAI.CubicFirstMoment.cubicThetaFinitePositiveCuspRestriction`, `OAI.CubicFirstMoment.cubicThetaInvertedConstantContinuation`, `OAI.CubicFirstMoment.cubicThetaNormalizedArithmeticResidue`, `OAI.CubicFirstMoment.cubicThetaObservedBaseFactor`, `OAI.CubicFirstMoment.cubicThetaPositiveCuspRestriction`, `OAI.CubicFirstMoment.cubicThetaPositiveFourierMass`, `OAI.CubicFirstMoment.cubicThetaPositiveFourierObservable`, `OAI.CubicFirstMoment.cubicThetaPositiveModelStrip`, `OAI.CubicFirstMoment.cubicThetaPrimaryCubeEquiv`, `OAI.CubicFirstMoment.cubicThetaPrimaryCubeMap`, `OAI.CubicFirstMoment.cubicThetaPrimeResidueVector`, `OAI.CubicFirstMoment.cubicThetaProjectedPlane`, `OAI.CubicFirstMoment.cubicThetaProjectedRadialCompleted`, `OAI.CubicFirstMoment.cubicThetaProjectedRadialDirichlet`, `OAI.CubicFirstMoment.cubicThetaRadialHeightRemainder`, `OAI.CubicFirstMoment.cubicThetaRamifiedPhaseCandidate`, `OAI.CubicFirstMoment.cubicThetaRankinRadialEnergy`, `OAI.CubicFirstMoment.cubicThetaResidueConstant`, `OAI.CubicFirstMoment.cubicThetaSelectedRadialCompleted`, `OAI.CubicFirstMoment.cubicThetaSelectedRadialDirichlet`, `OAI.CubicFirstMoment.cubicThetaSelectedRadialHolomorphicPart`, `OAI.CubicFirstMoment.cubicThetaShiftedFullObservation`, `OAI.CubicFirstMoment.cubicThetaShiftedModelHorizontal`, `OAI.CubicFirstMoment.cubicThetaShiftedWindowObservation`, `OAI.CubicFirstMoment.cubicThetaShiftedWindowTest`, `OAI.CubicFirstMoment.cubicThetaWeightedFourierResidue`, `OAI.CubicFirstMoment.structuredAngularFrequencyCoefficient`, `OAI.CubicFirstMoment.structuredAngularPrimeMoment`, `OAI.CubicFirstMoment.structuredAngularPrimeMomentAt`, `OAI.CubicFirstMoment.structuredAngularPrimeSum`, `OAI.CubicFirstMoment.structuredPrimeMoment`, `OAI.CubicFirstMoment.structuredPrimeMomentAt` and 2 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `CubicMoment_Angular_AngularPrimeMomentCoefficient`, `CubicMoment_Angular_AngularStructuredFrequencyPolynomial`, `CubicMoment_Angular_AngularStructuredPartition`, `CubicMoment_Estimates_PrimeMomentCoefficient`, `CubicMoment_Estimates_StructuredCutoffConsistency`, `CubicMoment_Estimates_StructuredPartition`, `CubicMoment_Estimates_TailPrimeRegroup`, `CubicMoment_Theta_CubicThetaArithmeticModelL2`, `CubicMoment_Theta_CubicThetaArithmeticModelObservation`, `CubicMoment_Theta_CubicThetaBorelRestriction`, `CubicMoment_Theta_CubicThetaBorelTransport`, `CubicMoment_Theta_CubicThetaCellFourierSeparation`, `CubicMoment_Theta_CubicThetaCompactBorelRestriction`, `CubicMoment_Theta_CubicThetaCompactIntegralRestriction`, `CubicMoment_Theta_CubicThetaCompactShiftedFamily`, `CubicMoment_Theta_CubicThetaCompactShiftedObservation`, `CubicMoment_Theta_CubicThetaCuspTypes`, `CubicMoment_Theta_CubicThetaFourierStripSeed`, `CubicMoment_Theta_CubicThetaFourierStripSupport`, `CubicMoment_Theta_CubicThetaFourierStripUnfold`, `CubicMoment_Theta_CubicThetaIncomingCompactIntegral`, `CubicMoment_Theta_CubicThetaInversionL2Bounds`, `CubicMoment_Theta_CubicThetaInversionPairing`, `CubicMoment_Theta_CubicThetaInvertedDirichlet`, `CubicMoment_Theta_CubicThetaPositiveCuspRestriction`, `CubicMoment_Theta_CubicThetaPositiveFourierMass`, `CubicMoment_Theta_CubicThetaPositiveFourierObservable`, `CubicMoment_Theta_CubicThetaPositiveModelL2`, `CubicMoment_Theta_CubicThetaPositiveStripBound`, `CubicMoment_Theta_CubicThetaPositiveStripFourierSeparation`, `CubicMoment_Theta_CubicThetaPositiveStripFubini`, `CubicMoment_Theta_CubicThetaPositiveStripHorizontalDensity`, `CubicMoment_Theta_CubicThetaPositiveStripPairing`, `CubicMoment_Theta_CubicThetaPositiveStripRepresentative`, `CubicMoment_Theta_CubicThetaPrimaryCubes`, `CubicMoment_Theta_CubicThetaPrimaryObservedCoefficient`, `CubicMoment_Theta_CubicThetaPrimeResidueImage`, `CubicMoment_Theta_CubicThetaProjectedConstant`, `CubicMoment_Theta_CubicThetaProjectedPlane`, `CubicMoment_Theta_CubicThetaProjectedRadial`, `CubicMoment_Theta_CubicThetaRadialDirichlet`, `CubicMoment_Theta_CubicThetaRadialHeight`, `CubicMoment_Theta_CubicThetaRadialRegularization`, `CubicMoment_Theta_CubicThetaRamifiedResidueFormula`, `CubicMoment_Theta_CubicThetaResidueConstant`, `CubicMoment_Theta_CubicThetaResidueNormalization`, `CubicMoment_Theta_CubicThetaScalarRankinRadial`, `CubicMoment_Theta_CubicThetaShiftedFullObservation`, `CubicMoment_Theta_CubicThetaShiftedHorizontalContinuity`, `CubicMoment_Theta_CubicThetaShiftedPeriodMeasure`, `CubicMoment_Theta_CubicThetaShiftedWindow`, `CubicMoment_Theta_CubicThetaShiftedWindowTest`, `CubicMoment_Theta_CubicThetaTorusCellTransport`, `CubicMoment_Theta_CubicThetaWeightedResidue`.
--
--   **Imports.** It imports the published bundle `Def_PattersonFirstMoment`; the bundles `OAIQ096A016`, `OAIQ096A017`, `OAIQ096A018` and `OAIQ096A019` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ096A024`, `OAIQ096A025`, `OAIQ096A028`, `OAIQ096A029`, `OAIQ096A030` and `OAIQ096A031`; the statements `OAI.CubicFirstMoment.UniformLogWeights.cubicTheta_radial_remainder_negative_long_mean`, `OAI.CubicFirstMoment.cubicTheta_radial_remainder_negative_tail_mean`, `OAI.CubicFirstMoment.cubicTheta_radial_remainder_tail_mean` and `OAI.CubicFirstMoment.first_unweighted_structured_moment`; the proofs of `OAI.CubicFirstMoment.UniformLogWeights.cubicTheta_radial_remainder_negative_long_mean`, `OAI.CubicFirstMoment.angular_exceptional_residual_moment`, `OAI.CubicFirstMoment.angular_height_signed_mellin_saving`, `OAI.CubicFirstMoment.angular_large_core_mellin_integral_saving`, `OAI.CubicFirstMoment.angular_tailHighUpperArity_isLittleO_uniform`, `OAI.CubicFirstMoment.cubicThetaScalarRankinKernel_integral_limit`, `OAI.CubicFirstMoment.first_unweighted_structured_moment`, `OAI.CubicFirstMoment.primeProductGaussTail_angular_isLittleO_proved`, `OAI.CubicFirstMoment.tailHighOrdinaryArity_isLittleO`, `OAI.CubicFirstMoment.tailHighUpperArity_isLittleO_uniform` and `OAI.CubicFirstMoment.uniform_core_block_polynomial_height`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A016
import Definitions.Def_OAIQ096A017
import Definitions.Def_OAIQ096A018
import Definitions.Def_OAIQ096A019

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeMomentCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of the structured moment with the original
squarefree ordered-prime coefficient, including numerator and exclusion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def structuredPrimeMoment (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ z ∈ (orderedConvolutionSupport (coordinatePrimeSupport W X Y)).filter
      (fun z => IsCoprime z e),
    primeMomentCoefficient W X Y z*mellinPhase u (norm z)*
      cubicSymbol z (v*a*b^2)*V (norm z/Y)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimeMomentCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (ℓ : ℤ)

def structuredAngularPrimeMoment (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ z ∈ (orderedConvolutionSupport (coordinatePrimeSupport W X Y)).filter
      (fun z => IsCoprime z e),
    primeMomentCoefficient W X Y z*theta ℓ z*mellinPhase u (norm z)*
      cubicSymbol z (v*a*b^2)*V (norm z/Y)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredCutoffConsistency
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The factor cutoff may be moved to the current output dyad. It does
not impose a new condition on a product whose norm is already in that dyad. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def structuredPrimeMomentAt (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ z ∈ (orderedConvolutionSupport (coordinatePrimeSupport W X Z)).filter
      (fun z => IsCoprime z e),
    primeMomentCoefficient W X Z z*mellinPhase u (norm z)*
      cubicSymbol z (v*a*b^2)*V (norm z/Y)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredPartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite smooth decomposition of the original structured sum. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def structuredPrimeSum (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ) : ℂ :=
  ∑ z ∈ (orderedConvolutionSupport (coordinatePrimeSupport W X Z)).filter
      (fun z => IsCoprime z e),
    primeMomentCoefficient W X Z z*mellinPhase u (norm z)*cubicSymbol z (v*a*b^2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStructuredPartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal angular sum and its finite smooth output partition, with
coefficient cutoffs kept consistent at every output dyad. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (ℓ : ℤ)

def structuredAngularPrimeMomentAt (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ z ∈ (orderedConvolutionSupport (coordinatePrimeSupport W X Z)).filter
      (fun z => IsCoprime z e),
    primeMomentCoefficient W X Z z*theta ℓ z*mellinPhase u (norm z)*
      cubicSymbol z (v*a*b^2)*V (norm z/Y)


def structuredAngularPrimeSum (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ) : ℂ :=
  ∑ z ∈ (orderedConvolutionSupport (coordinatePrimeSupport W X Z)).filter
      (fun z => IsCoprime z e),
    primeMomentCoefficient W X Z z*theta ℓ z*mellinPhase u (norm z)*cubicSymbol z (v*a*b^2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStructuredFrequencyPolynomial
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact angular frequency coefficients; their energy is unchanged. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def structuredAngularFrequencyCoefficient (ℓ : ℤ) (v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (Z : ℝ) (z : Eisenstein) : ℂ :=
  theta ℓ z*structuredFrequencyCoefficient v e u W X Z z

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TailPrimeRegroup
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact prime-tuple regrouping for the Gauss height tail. The original
product envelope and finite weights survive both support changes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment


def tailPrimeTupleRegrouped (i j : ℕ) (ℓ : ℤ) (ξ H U X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (s : Finset (Fin i ⊕ Fin j)) : ℂ :=
  ∑ b ∈ largeTupleSelectedSupport ξ X k s,
    ∑ a ∈ largeTupleOtherSupport ξ X k s,
      largeTupleSelectedCoefficient ξ X k s b*largeTupleOtherCoefficient ξ X k s a*
        productGaussHeightWindowKernel ℓ primeProductEnvelope H U X X (b*a)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaResidueConstant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical normalization of the computed principal constant-mode residue. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicTheta_constant_residue_coefficient :
    (2*Real.pi/(3*Real.sqrt 3):ℂ)*
      ((principalThetaConstant/(residueHeckeScale 1:ℂ))/(4*principalIdealZeta 2))=
        (Real.pi:ℂ)^2/(54*principalIdealZeta 2) := by
  rw [cubicTheta_principalZeta_residue_value]
  have hroot : (Real.sqrt 3:ℂ)^2=3 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hn : (Real.sqrt 3:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  field_simp
  ring_nf
  rw [hroot]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaResidueNormalization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
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

def cubicThetaNormalizedArithmeticResidue : cubicThetaGlobalEnergySpace :=
  cubicThetaResidueScale • cubicThetaArithmeticResidueEnergy (4/3)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticModelL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit arithmetic model is an actual L2 function on the
high cusp, including its nonzero constant term. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaStrip_height_rpow_integrable {r : ℝ} (hr : r<2) :
    IntegrableOn (fun p : CubicThetaPoint => p.val.2^r)
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
  have hh : IntegrableOn (fun _ : ℂ => (1:ℝ)) cubicThetaHorizontalCell :=
    integrableOn_const cubicThetaHorizontalCell_measure_ne_top
  have hv : IntegrableOn (fun v : ℝ => v^(r-3)) (Ioi (2:ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hm := hh.mul_prod hv
  rw [Measure.prod_restrict] at hm
  apply (cubicThetaPointIntegrable_density (cubicThetaCuspStrip_measurable 2)
    (fun y => y.2^r)).mpr
  rw [cubicThetaCuspStrip_coordinates (by norm_num : (0:ℝ)≤2)]
  apply hm.congr
  filter_upwards [ae_restrict_mem
    (cubicThetaHorizontalCell_measurable.prod measurableSet_Ioi)] with y hy
  rw [one_mul,Real.rpow_sub (by have hp : (2:ℝ)<y.2 := hy.2; linarith)]
  simpa only [Nat.cast_ofNat] using
    congrArg (fun t : ℝ => y.2^r/t) (Real.rpow_natCast y.2 3)

lemma cubicThetaArithmeticModel_constant_memLp :
    MemLp (fun p : CubicThetaPoint => ((cubicThetaConstant*p.val.2^(2/3:ℝ):ℝ):ℂ))
      2 (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)) := by
  have hc : Continuous (fun p : CubicThetaPoint =>
      ((cubicThetaConstant*p.val.2^(2/3:ℝ):ℝ):ℂ)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact Complex.continuous_ofReal.continuousAt.comp
      (((continuousAt_snd.comp continuous_subtype_val.continuousAt).rpow_const
        (Or.inl p.property.ne')).const_mul cubicThetaConstant)
  rw [memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable]
  apply ((cubicThetaStrip_height_rpow_integrable (r:=(4/3:ℝ)) (by norm_num)).const_mul
    (cubicThetaConstant^2)).congr
  filter_upwards [ae_restrict_mem (cubicThetaCuspStrip_measurable 2)] with p hp
  have hv : 0<p.val.2 := p.property
  rw [Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow,
    ←Real.rpow_mul_natCast hv.le]
  norm_num

lemma cubicThetaArithmeticModel_memLp (A : ℂ) :
    MemLp (fun p : CubicThetaPoint => cubicThetaArithmeticModel A p.val)
      2 (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)) :=
  cubicThetaArithmeticModel_constant_memLp.add
    (cubicThetaArithmeticModel_remainder_memLp.const_mul A)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeResidueImage
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact passage between the three actual prime-free residues and the
actual Fourier residues. It preserves the critical local image condition;
this does not assert that either family is in that image. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeResidueVector (p h : Eisenstein) : Fin 3 → ℂ :=
  ![cubicThetaArithmeticFourierResidue h (4/3),
    cubicThetaPrimeCriticalScale p*cubicThetaArithmeticFourierResidue (p*h) (4/3),
    (cubicThetaPrimeCriticalScale p)^2*cubicThetaArithmeticFourierResidue (p^2*h) (4/3)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma cubicThetaInversion_pairing (F G : CubicThetaSection) (q : CubicThetaQuotient) :
    cubicThetaSectionPairing (cubicThetaInversionSection F) G q=
      cubicThetaSectionPairing F (cubicThetaInversionSection G)
        (cubicThetaIntegralQuotientMap cubicThetaFullInversion q) := by
  obtain ⟨p,rfl⟩ := cubicThetaQuotientMap_surjective q
  rw [cubicThetaIntegralQuotientMap_apply,cubicThetaSectionPairing_apply,
    cubicThetaSectionPairing_apply]
  change inner ℂ (F.val (cubicThetaFullInversion • p)) (G.val p)=
    inner ℂ (F.val (cubicThetaFullInversion • p))
      (G.val (cubicThetaFullInversion • (cubicThetaFullInversion • p)))
  rw [cubicThetaFullInversion_involutive]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionL2Bounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.instMeasurableSpace
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

lemma cubicThetaSectionStrip_norm_le (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    ‖(cubicThetaSection_strip_memLp F hF).toLp (fun p : CubicThetaPoint => F.val p)‖≤
      ‖hF.toLp (cubicThetaSectionRepresentative F)‖ := by
  have hn : Integrable (fun q => cubicThetaSectionNorm F q^2) cubicThetaQuotientMeasure := by
    simpa only [cubicThetaSectionRepresentative_norm] using hF.integrable_norm_pow (by norm_num)
  have hi := cubicThetaInjective_integral_le (cubicThetaCuspStrip_measurable 2)
    (cubicThetaCuspStrip_injective (by norm_num)) hn (fun q => sq_nonneg (cubicThetaSectionNorm F q))
  simp only [cubicThetaSectionNorm_apply] at hi
  have hs : ‖(cubicThetaSection_strip_memLp F hF).toLp (fun p : CubicThetaPoint => F.val p)‖^2=
      ∫ p in cubicThetaCuspStrip 2, ‖F.val p‖^2 ∂cubicThetaPointMeasure := by
    rw [cubicTheta_l2_norm_sq_measure]
    apply integral_congr_ae
    filter_upwards [(cubicThetaSection_strip_memLp F hF).coeFn_toLp] with p hp
    rw [hp]
  rw [←hs,←cubicThetaSectionL2_norm_sq F hF] at hi
  exact _root_.le_of_sq_le_sq hi (_root_.norm_nonneg _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFourierStripSeed
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single half-open strip seed for the full Fourier Poincare sum.
Its translations have exactly one contributing term at every point. -/
noncomputable section
open Set
open scoped CompactlySupported
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaHorizontalCell_unique_eisenstein (z : ℂ) :
    ∃! w : Eisenstein,z+3*(w:ℂ)∈cubicThetaHorizontalCell := by
  obtain ⟨g,hg,huniq⟩ := cubicThetaHorizontalCell_unique z
  refine ⟨Multiplicative.toAdd g,hg,?_⟩
  intro w hw
  have he := huniq (Multiplicative.ofAdd w) hw
  exact congrArg Multiplicative.toAdd he

lemma cubicThetaFourierStripSeed_translation_sum (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (p : CubicThetaPoint) :
    (∑' w : Eisenstein,cubicThetaFourierStripSeed h W (cubicThetaPrincipalTranslation w • p))=
      W p.val.2*cubicThetaHorizontalCharacter h p.val.1 := by
  classical
  obtain ⟨w,hw,huniq⟩ := cubicThetaHorizontalCell_unique_eisenstein p.val.1
  rw [tsum_eq_single w]
  · rw [cubicThetaFourierStripSeed_translate,ite_eq_left hw]
  · intro v hv
    rw [cubicThetaFourierStripSeed_translate]
    apply ite_eq_right
    intro hm
    exact hv (huniq v hm)

lemma cubicThetaFourierStripSeed_pair_translation_sum (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (F : CubicThetaSection) (p : CubicThetaPoint) :
    (∑' w : Eisenstein,star (cubicThetaFourierStripSeed h W (cubicThetaPrincipalTranslation w • p))*
      F.val (cubicThetaPrincipalTranslation w • p))=
      star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*F.val p := by
  have he (w : Eisenstein) : F.val (cubicThetaPrincipalTranslation w • p)=F.val p := by
    have hh := F.property (cubicThetaPrincipalTranslation w) p
    change F.val (cubicThetaPrincipalTranslation w • p)=
      cubicThetaKubotaValue (cubicThetaPrincipalTranslation w)*F.val p at hh
    simpa only [cubicThetaPrincipalTranslation_value,one_mul] using hh
  simp_rw [he]
  rw [tsum_mul_right,←tsum_star,cubicThetaFourierStripSeed_translation_sum]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFourierStripSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact support and absolute integrability of the half-open Fourier seed
at every positive height cutoff. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaFourierStripSeed_mul_integrable (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (g : CubicThetaPoint → ℂ) (hg : Continuous g) :
    Integrable (fun p => star (cubicThetaFourierStripSeed h W p)*g p)
      cubicThetaPointMeasure := by
  obtain ⟨K,hK,hsub⟩ := cubicThetaFourierStripSeed_compact h W hε hW
  let f : CubicThetaPoint → ℂ := fun p =>
    star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*g p
  have hf : Continuous f := by
    exact ((W.continuous.comp (continuous_snd.comp continuous_subtype_val)).mul
      ((cubicThetaHorizontalCharacter_continuous h).comp
        (continuous_fst.comp continuous_subtype_val))).star.mul hg
  let A : Set CubicThetaPoint := {p | p.val.1∈cubicThetaHorizontalCell}
  have hA : MeasurableSet A := cubicThetaHorizontalCell_measurable.preimage
    (measurable_fst.comp cubicThetaPointInclusion_measurableEmbedding.measurable)
  have he : (fun p => star (cubicThetaFourierStripSeed h W p)*g p)=
      A.indicator (K.indicator f) := by
    funext p
    by_cases ha : p.val.1∈cubicThetaHorizontalCell
    · by_cases hk : p∈K
      · simp [A,ha,hk,cubicThetaFourierStripSeed,f]
      · have hz : cubicThetaFourierStripSeed h W p=0 :=
          not_not.mp (fun hn => hk (hsub hn))
        simp [A,ha,hk,hz]
    · have hz : cubicThetaFourierStripSeed h W p=0 := ite_eq_right ha
      simp [A,ha,hz]

  rw [he]
  exact ((hf.continuousOn.integrableOn_compact hK).integrable_indicator hK.measurableSet).indicator hA

lemma cubicThetaFourierStripSeed_pair_integrable (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (F : CubicThetaSection) :
    Integrable (fun p => star (cubicThetaFourierStripSeed h W p)*F.val p)
      cubicThetaPointMeasure :=
  cubicThetaFourierStripSeed_mul_integrable h W hε hW F.val F.val.continuous

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFourierStripUnfold
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full arithmetic unfolding of the compact Fourier profile. The positive
cutoff can lie below the injective cusp, since the group sum is unfolded first. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaFourierStripSeed_group_sum (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (F : CubicThetaSection)
    (p : CubicThetaPoint) :
    (∑' g : cubicThetaPrincipalGroup,
      star (cubicThetaFourierStripSeed h W (g • p))*F.val (g • p))=
      star (cubicThetaFourierProfileSeries h p.val W)*F.val p := by
  let f : cubicThetaPrincipalGroup → ℂ := fun g =>
    star (cubicThetaFourierStripSeed h W (g • p))*F.val (g • p)
  let e : (CubicThetaBottomRow × Eisenstein) ≃ cubicThetaPrincipalGroup :=
    (Equiv.prodComm _ _).trans cubicThetaRowTranslationEquiv
  have hs : Summable (fun rw => f (e rw)) :=
    e.summable_iff.mpr (cubicThetaFourierStripSeed_pair_summable h W hε hW F p)
  calc
    _ = ∑' rw : CubicThetaBottomRow × Eisenstein,f (e rw) := (e.tsum_eq f).symm
    _ = ∑' r : CubicThetaBottomRow,∑' w : Eisenstein,f (e (r,w)) := hs.tsum_prod
    _ = ∑' r : CubicThetaBottomRow,star (cubicThetaFourierProfileTerm h r p.val W)*F.val p := by
      apply tsum_congr
      intro r
      change (∑' w : Eisenstein,star (cubicThetaFourierStripSeed h W
        ((cubicThetaPrincipalTranslation w*r.completion) • p))*
          F.val ((cubicThetaPrincipalTranslation w*r.completion) • p))=_
      simp_rw [mul_smul]
      rw [cubicThetaFourierStripSeed_pair_translation_sum]
      have hh : (r.completion • p).val.2=r.height p.val := by
        change (cubicThetaBottomRow r.completion).height p.val=_
        rw [r.completion_row]
      have hf := F.property r.completion p
      change F.val (r.completion • p)=cubicThetaKubotaValue r.completion*F.val p at hf
      rw [hh,hf]
      simp only [cubicThetaFourierProfileTerm,cubicThetaRadialProfileTerm,star_mul,star_star]
      rw [cubicThetaKubotaValue_bottomRow,r.completion_row]
      change star (cubicThetaHorizontalCharacter h
        (cubicThetaMobius (cubicThetaPrincipalComplex r.completion) p.val).1)*
          star (W (r.height p.val))*(r.phase*F.val p)=_
      ring
    _ = _ := by rw [tsum_mul_right,←tsum_star]; rfl

theorem cubicThetaPositiveFourierProfile_pairing_integral (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (F : CubicThetaSection) :
    (∫ q,cubicThetaSectionPairing (cubicThetaPositiveFourierProfileSection h W hε hW) F q
      ∂cubicThetaQuotientMeasure)=
      ∫ p,star (cubicThetaFourierStripSeed h W p)*F.val p ∂cubicThetaPointMeasure := by
  rw [cubicThetaQuotientMeasure,
    integral_map_of_stronglyMeasurable cubicThetaQuotientMap_open.continuous.measurable
      (cubicThetaSectionPairing_continuous _ _).stronglyMeasurable]
  have he (p : CubicThetaPoint) :
      cubicThetaSectionPairing (cubicThetaPositiveFourierProfileSection h W hε hW) F
        (cubicThetaQuotientMap p)=
      ∑' g : cubicThetaPrincipalGroup,
        star (cubicThetaFourierStripSeed h W (g • p))*F.val (g • p) := by
    rw [cubicThetaFourierStripSeed_group_sum h W hε hW F p,cubicThetaSectionPairing_apply]
    change inner ℂ (cubicThetaFourierProfileSeries h p.val W) (F.val p)=_
    simp only [RCLike.inner_apply',starRingEnd_apply]
  simp_rw [he]
  exact cubicThetaFundamental_integral_tsum (cubicThetaFourierStripSeed_pair_integrable h W hε hW F)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveStripFubini
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fubini and radial Fourier pairing at any positive cutoff. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPositiveFourierPairing_integrable (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (F : CubicThetaSection) :
    IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*F.val p)
      (cubicThetaCuspStrip ε) cubicThetaPointMeasure := by
  apply (cubicThetaFourierStripSeed_pair_integrable h W hε hW F).integrableOn.congr
  filter_upwards [ae_restrict_mem (cubicThetaCuspStrip_measurable ε)] with p hp
  change ε<p.val.2 ∧ p.val.1∈cubicThetaHorizontalCell at hp
  simp only [cubicThetaFourierStripSeed,ite_eq_left hp.2]

theorem cubicThetaPositiveFourierProfile_pairing_radial (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (F : CubicThetaSection) :
    (∫ q,cubicThetaSectionPairing (cubicThetaPositiveFourierProfileSection h W hε hW) F q
      ∂cubicThetaQuotientMeasure)=
      ∫ v in Ioi ε,star (W v)/(v:ℂ)^3*cubicThetaSectionFourierFunction F h v := by
  have hi := cubicThetaPositiveFourierPairing_integrable h W hε hW F
  have hi' : IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*cubicThetaSectionFunction F p.val)
      (cubicThetaCuspStrip ε) cubicThetaPointMeasure := by
    apply hi.congr
    filter_upwards with p
    rw [cubicThetaSectionFunction_coordinates]
  rw [cubicThetaPositiveFourierProfile_pairing_integral h W hε hW F,
    cubicThetaFourierStripSeed_pair_on_strip h W hε hW F]
  have he := cubicThetaPositiveCuspStrip_fubini hε.le
    (fun y => star (W y.2*cubicThetaHorizontalCharacter h y.1)*cubicThetaSectionFunction F y) hi'
  change (∫ p in cubicThetaCuspStrip ε,
    star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*cubicThetaSectionFunction F p.val
      ∂cubicThetaPointMeasure)=_ at he
  simp_rw [cubicThetaSectionFunction_coordinates] at he
  rw [he]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  dsimp only [cubicThetaSectionFourierFunction,cubicThetaHorizontalFourierCoefficient]
  rw [←integral_const_mul]
  apply setIntegral_congr_fun cubicThetaHorizontalCell_measurable
  intro z _
  simp only [star_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveFourierMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

def cubicThetaPositiveFourierMass (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) :
    cubicThetaAutomorphicL2 :=
  cubicThetaGlobalMassClosure (cubicThetaPositiveFourierProfileTest h W hε hW hsm)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaIncomingCompactIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact strip contribution of the incoming arithmetic series is
entire in the spectral parameter. It contributes no pole to Fourier tests. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaIncomingCompactIntegral_differentiable (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    Differentiable ℂ (fun s : ℂ => ∫ p,
      star (cubicThetaFourierStripSeed h W p)*cubicThetaIncomingEisenstein p.val s
        ∂cubicThetaPointMeasure) := by
  obtain ⟨K,hK,hsub⟩ := cubicThetaFourierStripSeed_compact h W hε hW
  have hKC : IsCompact (cubicThetaPointCoordinates '' K) :=
    hK.image cubicThetaPointCoordinates_continuous
  obtain ⟨S,hS⟩ := cubicThetaIncomingEisenstein_compact_sum hKC
    (by rintro _ ⟨p,_,rfl⟩; exact p.property)
  have he (s : ℂ) : (∫ p,star (cubicThetaFourierStripSeed h W p)*
      cubicThetaIncomingEisenstein p.val s ∂cubicThetaPointMeasure)=
      ∑ r∈S,∫ p in K,star (cubicThetaFourierStripSeed h W p)*
        cubicThetaIncomingTerm r p.val s ∂cubicThetaPointMeasure := by
    rw [←setIntegral_eq_integral_of_forall_compl_eq_zero (s:=K) (by
      intro p hp
      have hz : cubicThetaFourierStripSeed h W p=0 := not_not.mp (fun hn => hp (hsub hn))
      rw [hz,star_zero,zero_mul])]
    calc
      _ = ∫ p in K,∑ r∈S,star (cubicThetaFourierStripSeed h W p)*
          cubicThetaIncomingTerm r p.val s ∂cubicThetaPointMeasure := by
        apply setIntegral_congr_fun hK.measurableSet
        intro p hp
        dsimp only
        rw [hS p.val ⟨p,hp,rfl⟩ s,Finset.mul_sum]
      _ = _ := integral_finsetSum S (fun r _ =>
        (cubicThetaFourierStripSeed_mul_integrable h W hε hW _
          (cubicThetaIncomingTerm_point_continuous r s)).integrableOn)
  have hterm (r : CubicThetaBottomRow) : Differentiable ℂ (fun s : ℂ => ∫ p in K,
      star (cubicThetaFourierStripSeed h W p)*cubicThetaIncomingTerm r p.val s
        ∂cubicThetaPointMeasure) := by
    have hd := cubicThetaCompactExponential_differentiable hK
      (fun p => star (cubicThetaFourierStripSeed h W p)*cubicThetaIncomingTerm r p.val 0)
      (cubicThetaFourierStripSeed_mul_integrable h W hε hW _
        (cubicThetaIncomingTerm_point_continuous r 0)).integrableOn
      (fun p => Real.log (r.height p.val)) (cubicThetaRowLogHeight_point_continuous r).continuousOn
    convert hd using 1
    all_goals try with_reducible_and_instances rfl
    funext s
    apply setIntegral_congr_fun hK.measurableSet
    intro p _
    dsimp only
    rw [cubicThetaIncomingTerm_exponential]
    ring
  have hf : (fun s : ℂ => ∫ p,star (cubicThetaFourierStripSeed h W p)*
      cubicThetaIncomingEisenstein p.val s ∂cubicThetaPointMeasure)=
      (fun s => ∑ r∈S,∫ p in K,star (cubicThetaFourierStripSeed h W p)*
        cubicThetaIncomingTerm r p.val s ∂cubicThetaPointMeasure) := funext he
  rw [hf]
  exact Differentiable.fun_sum (fun r _ => hterm r)

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

def cubicThetaPositiveFourierObservable (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (s : ℂ) : ℂ :=
  cubicThetaArithmeticDistribution (cubicThetaPositiveFourierProfileSection h W hε hW)
    (cubicThetaPositiveFourierProfileSection_compact h W hε hW) s+
  ∫ p,star (cubicThetaFourierStripSeed h W p)*cubicThetaIncomingEisenstein p.val s
    ∂cubicThetaPointMeasure

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaWeightedResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unramified coefficient laws for the actual arithmetic residue in
the Whittaker normalization. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaWeightedFourierResidue (h : Eisenstein) : ℂ :=
  (norm h:ℂ)^(-(1/3:ℂ))*cubicThetaArithmeticFourierResidue h (4/3)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryObservedCoefficient
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized Whittaker coefficients agree with the explicit
primary theta family up to its single base coefficient. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaObservedBaseFactor : ℂ :=
  cubicThetaResidueScale*((Real.pi:ℂ)/Complex.Gamma (4/3))*
    ((2*(cubicThetaRowHeatScale 1)^(1/6:ℝ)/‖cubicThetaRowFrequency 1‖:ℝ):ℂ)/
      ((9*Real.sqrt 3/2:ℝ):ℂ)

lemma cubicThetaNormalizedObservedCoefficient_weighted {h : Eisenstein} (hh : h≠0) :
    cubicThetaNormalizedObservedCoefficient h=
      cubicThetaObservedBaseFactor*cubicThetaWeightedFourierResidue h := by
  have hw := cubicThetaPoleWeight_mul hh (one_ne_zero : (1:Eisenstein)≠0)
  rw [mul_one] at hw
  have hc : (((norm h)^(-(1/3:ℝ)):ℝ):ℂ)=((norm h:ℂ)^(-(1/3:ℂ))) := by
    simpa only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using
      (Complex.ofReal_cpow (norm_nonneg h) (-(1/3:ℝ)))
  unfold cubicThetaNormalizedObservedCoefficient cubicThetaObservedWhittakerCoefficient
    cubicThetaObservedBaseFactor cubicThetaWeightedFourierResidue
  rw [hw,Complex.ofReal_mul,hc]
  ring

lemma cubicThetaNormalizedObservedCoefficient_one :
    cubicThetaNormalizedObservedCoefficient 1=
      cubicThetaObservedBaseFactor*cubicThetaWeightedFourierResidue 1 :=
  cubicThetaNormalizedObservedCoefficient_weighted one_ne_zero

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryCubes
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The primary cubes at the inverted cusp are in exact bijection with
ideals prime to lambda. No choice of a cube root contributes multiplicity. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimaryGenerator_primary (ν : CubicThetaUnramifiedIdeal) :
    primary (idealPrimaryGenerator ν.val) := by
  have hn : ¬lambdaE∣idealExponentGenerator ν.val := by
    rw [cubicThetaRamifiedPrime_dvd_iff,ν.property]
    exact Nat.not_lt_zero _
  have hc : IsCoprime (idealExponentGenerator ν.val) lambdaE :=
    (lambdaE_prime.coprime_iff_not_dvd.mpr hn).symm
  have hc3 : IsCoprime (idealExponentGenerator ν.val) 3 := by
    have ht := hc.pow_right (n:=2)
    rw [lambdaE_sq] at ht
    simpa using ht.neg_right
  exact primaryNormalize_primary (residue_isUnit_of_isCoprime hc3.symm)

lemma cubicThetaPrimaryGenerator_cube_primary (ν : CubicThetaUnramifiedIdeal) :
    primary ((idealPrimaryGenerator ν.val)^3) := by
  have hp := cubicThetaPrimaryGenerator_primary ν
  simpa only [pow_succ,pow_zero,one_mul] using primary_mul (primary_mul hp hp) hp

def cubicThetaPrimaryCubeMap (ν : CubicThetaUnramifiedIdeal) : CubicThetaPrimaryCube :=
  ⟨(idealPrimaryGenerator ν.val)^3,cubicThetaPrimaryGenerator_cube_primary ν,
    idealPrimaryGenerator ν.val,rfl⟩

lemma cubicThetaPrimaryCubeMap_exponent (ν : CubicThetaUnramifiedIdeal) :
    idealExponentOf (cubicThetaPrimaryCubeMap ν).val=3•ν.val := by
  rw [cubicThetaPrimaryCubeMap,idealExponentOf_pow
    (primary_ne_zero (cubicThetaPrimaryGenerator_primary ν)),idealExponentOf_primaryGenerator]

lemma cubicThetaPrimaryCubeMap_bijective : Function.Bijective cubicThetaPrimaryCubeMap := by
  constructor
  · intro ν κ he
    apply Subtype.ext
    have ht := congrArg (fun c : CubicThetaPrimaryCube => idealExponentOf c.val) he
    rw [cubicThetaPrimaryCubeMap_exponent,cubicThetaPrimaryCubeMap_exponent] at ht
    ext p
    have hp := congrArg (fun f : EisensteinIdealExponent => f p) ht
    simp only [Finsupp.smul_apply,smul_eq_mul] at hp
    omega
  · intro c
    obtain ⟨j,hj⟩ := c.property.2
    have hj0 : j≠0 := by
      intro h
      subst j
      have hc0 := primary_ne_zero c.property.1
      simp only [zero_pow (by norm_num : (3:ℕ)≠0)] at hj
      exact hc0 hj.symm
    let ν := idealExponentOf j
    have hν : ν cubicThetaRamifiedPrime=0 := by
      apply Nat.eq_zero_of_not_pos
      intro hpos
      have hd : lambdaE∣j :=
        ((cubicThetaRamifiedPrime_dvd_iff ν).mpr hpos).trans (idealExponentOf_associated hj0).dvd
      have hd' : lambdaE∣c.val := hj ▸ hd.trans (dvd_pow_self j (by norm_num : (3:ℕ)≠0))
      exact lambdaE_prime.not_isUnit ((primary_coprime_lambda c.property.1).isRelPrime hd' dvd_rfl)
    refine ⟨⟨ν,hν⟩,Subtype.ext ?_⟩
    change (idealPrimaryGenerator ν)^3=c.val
    apply primary_associated_eq (cubicThetaPrimaryGenerator_cube_primary ⟨ν,hν⟩) c.property.1
    rw [←hj]
    exact ((primaryNormalize_associated (idealExponentGenerator ν)).symm.trans
      (idealExponentOf_associated hj0)).pow_pow

def cubicThetaPrimaryCubeEquiv : CubicThetaUnramifiedIdeal ≃ CubicThetaPrimaryCube :=
  Equiv.ofBijective _ cubicThetaPrimaryCubeMap_bijective

lemma cubicThetaPrimaryCube_norm (ν : CubicThetaUnramifiedIdeal) :
    norm (cubicThetaPrimaryCubeMap ν).val=idealExponentNorm ν.val^3 := by
  change norm ((idealPrimaryGenerator ν.val)^3)=_
  rw [←normNat_cast,show normNat ((idealPrimaryGenerator ν.val)^3)=
    normNat (idealPrimaryGenerator ν.val)^3 from map_pow normNatHom _ _,
    Nat.cast_pow,normNat_cast,idealPrimaryGenerator_norm]

lemma cubicThetaPrimaryCube_units (ν : CubicThetaUnramifiedIdeal) :
    (Nat.card (Residues (cubicThetaPrimaryCubeMap ν).val)ˣ:ℂ)=
      (idealExponentNorm ν.val:ℂ)^2*(cubicThetaIdealTotient ν.val:ℂ) := by
  have hp0 := primary_ne_zero (cubicThetaPrimaryGenerator_primary ν)
  change (Nat.card (Residues ((idealPrimaryGenerator ν.val)^3))ˣ:ℂ)=_
  rw [show (3:ℕ)=2+1 from rfl,cubicTheta_power_units_card hp0 2,Nat.cast_mul,Nat.cast_pow]
  have hnorm : (normNat (idealPrimaryGenerator ν.val):ℂ)=(idealExponentNorm ν.val:ℂ) := by
    rw [←Complex.ofReal_natCast,normNat_cast,idealPrimaryGenerator_norm]
  have ht : Nat.card (Residues (idealPrimaryGenerator ν.val))ˣ=cubicThetaIdealTotient ν.val :=
    cubicTheta_residue_units_associated (primaryNormalize_associated (idealExponentGenerator ν.val)).symm
  rw [hnorm,ht]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInvertedDirichlet
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma cubicThetaInvertedConstantWeight_cube (s : ℂ) (ν : CubicThetaUnramifiedIdeal) :
    cubicThetaInvertedConstantWeight s (cubicThetaPrimaryCubeMap ν).val=
      cubicThetaIdealDensity ν.val*(idealExponentNorm ν.val:ℂ)^(-(3*s-3)) := by
  have hp := (cubicThetaPrimaryCubeMap ν).property
  rw [cubicThetaInvertedConstantWeight,ite_eq_left hp.1,
    cubicThetaInvertedConstantGauss_eq hp.1,ite_eq_left hp.2,
    cubicThetaPrimaryCube_units,cubicThetaPrimaryCube_norm,cubicThetaIdealDensity,
    Complex.ofReal_pow]
  have hN := Complex.ofReal_ne_zero.mpr (idealExponentNorm_pos ν.val).ne'
  have he : ((idealExponentNorm ν.val:ℂ)^3)^(-s)=
      (idealExponentNorm ν.val:ℂ)^(-3*s) := by
    rw [←Complex.cpow_nat_mul' (n:=3)
      (by rw [Complex.arg_ofReal_of_nonneg (idealExponentNorm_pos ν.val).le]; nlinarith [Real.pi_pos])
      (by rw [Complex.arg_ofReal_of_nonneg (idealExponentNorm_pos ν.val).le]; nlinarith [Real.pi_pos])]
    congr 1
    ring
  rw [he,show -(3*s-3)=(3:ℂ)+(-3*s) by ring,Complex.cpow_add _ _ hN,
    show (idealExponentNorm ν.val:ℂ)^(3:ℂ)=(idealExponentNorm ν.val:ℂ)^3 from
      Complex.cpow_natCast _ 3]
  field_simp

lemma cubicThetaInvertedConstantDirichlet_ideal (s : ℂ) :
    cubicThetaInvertedConstantDirichlet s=
      ∑' ν : CubicThetaUnramifiedIdeal,
        cubicThetaIdealDensity ν.val*(idealExponentNorm ν.val:ℂ)^(-(3*s-3)) := by
  calc
    _ = ∑' c : CubicThetaPrimaryCube, cubicThetaInvertedConstantWeight s c.val :=
      (tsum_subtype_eq_of_support_subset (cubicThetaInvertedConstantWeight_support s)).symm
    _ = ∑' ν : CubicThetaUnramifiedIdeal,
        cubicThetaInvertedConstantWeight s (cubicThetaPrimaryCubeMap ν).val :=
      (cubicThetaPrimaryCubeEquiv.tsum_eq _).symm
    _ = _ := tsum_congr (cubicThetaInvertedConstantWeight_cube s)

lemma cubicThetaInvertedConstantDirichlet_difference {s : ℂ} (hs : 4/3 < s.re) :
    cubicThetaInvertedConstantDirichlet s=
      normDirichletSeries cubicThetaIdealDensity idealExponentNorm (3*s-3)-
        cubicThetaRamifiedDensitySeries (3*s-3) := by
  have ht : 1<(3*s-3).re := by
    simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
    linarith
  let f (ν : EisensteinIdealExponent) :=
    cubicThetaIdealDensity ν*(idealExponentNorm ν:ℂ)^(-(3*s-3))
  let g (ν : EisensteinIdealExponent) :=
    cubicThetaPrimeDensity cubicThetaRamifiedPrime ν*(idealExponentNorm ν:ℂ)^(-(3*s-3))
  have hf : Summable f := (idealDirichlet_norm_summable _ cubicThetaIdealDensity_norm ht).of_norm
  have hg : Summable g :=
    (idealDirichlet_norm_summable _ (cubicThetaPrimeDensity_norm cubicThetaRamifiedPrime) ht).of_norm
  rw [cubicThetaInvertedConstantDirichlet_ideal]
  change (∑' ν : CubicThetaUnramifiedIdeal, f ν.val)=(∑' ν, f ν)-(∑' ν, g ν)
  rw [←hf.tsum_sub hg]
  have hsup : Function.support (fun ν => f ν-g ν) ⊆
      {ν | ν cubicThetaRamifiedPrime=0} := by
    intro ν hν
    by_contra hn
    exact hν (by simp [f,g,cubicThetaPrimeDensity,Nat.pos_of_ne_zero hn])
  calc
    _ = ∑' ν : CubicThetaUnramifiedIdeal, (f ν.val-g ν.val) := by
      apply tsum_congr
      intro ν
      simp [g,cubicThetaPrimeDensity,ν.property]
    _ = _ := tsum_subtype_eq_of_support_subset hsup

def cubicThetaInvertedConstantContinuation (s : ℂ) : ℂ :=
  ((1-(3:ℂ)^(3-3*s))/(1-(3:ℂ)^(2-3*s)))*
    principalIdealZeta (3*s-3)/principalIdealZeta (3*s-2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedResidueFormula
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit solution of the actual ramified residue system. The phase
is obtained from the finite rows and uniqueness from their strict contraction. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaRamifiedPhaseCandidate (h : Eisenstein) (d : Eisensteinˣ) : ℂ :=
  (3:ℂ)^(-(1/3:ℂ))*(cubicThetaNinePhase ((d:Eisenstein)^2*h)*
    cubicThetaArithmeticFourierResidue h (4/3))

lemma cubicThetaRamifiedPhaseCandidate_neg (h : Eisenstein) (d : Eisensteinˣ) :
    cubicThetaRamifiedPhaseCandidate h (-d)=cubicThetaRamifiedPhaseCandidate h d := by
  unfold cubicThetaRamifiedPhaseCandidate
  rw [Units.val_neg,neg_sq]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticModelObservation
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted Fourier observations identify the arithmetic residue with
the explicit coefficient model, retaining its one actual base scalar. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaArithmeticModel_horizontal (A : ℂ) {v : ℝ} (hv : 0<v)
    (h : Eisenstein) :
    (∫ z in cubicThetaHorizontalCell,
      star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*
        cubicThetaArithmeticModel A (z,v))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*
        (if h=0 then ((cubicThetaConstant*v^(2/3:ℝ):ℝ):ℂ)
        else A*cubicThetaArithmeticCoefficient (-lambdaE*h)*
          cubicThetaWhittaker (‖cubicThetaRowFrequency h‖*v)) := by
  rw [cubicThetaHorizontalCoefficient (fun z => cubicThetaArithmeticModel A (z,v))
    (cubicThetaArithmeticModelTorus A v) h
    (fun x => (cubicThetaArithmeticModelTorus_real A hv x).symm),
    cubicThetaArithmeticModelTorus_coefficient A hv]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveStripBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded multiplicity of a positive-height period strip over the
actual arithmetic quotient. Only a finite compact chart cover is used. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

lemma cubicThetaCompact_pullback_bound {K : Set CubicThetaPoint} (hK : IsCompact K) :
    ∃ N : ℕ,(cubicThetaPointMeasure.restrict K).map cubicThetaQuotientMap≤
      (N:ℝ≥0∞) • cubicThetaQuotientMeasure := by
  classical
  obtain ⟨T,hT⟩ := hK.elim_finite_subcover
    (fun p => (cubicThetaCoveringChart p).source)
    (fun p => (cubicThetaCoveringChart p).open_source) (by
      intro p _
      exact mem_iUnion.mpr ⟨p,cubicThetaCoveringChart_source p⟩)
  refine ⟨T.card,Measure.le_iff.mpr (fun B hB => ?_)⟩
  rw [Measure.map_apply cubicThetaQuotientMap_open.continuous.measurable hB,
    Measure.restrict_apply (hB.preimage cubicThetaQuotientMap_open.continuous.measurable),
    Measure.smul_apply,smul_eq_mul]
  calc
    cubicThetaPointMeasure (cubicThetaQuotientMap ⁻¹' B ∩ K)≤
        cubicThetaPointMeasure (⋃ p∈T,
          cubicThetaQuotientMap ⁻¹' B ∩ (cubicThetaCoveringChart p).source) := by
      apply measure_mono
      rintro p ⟨hB,hK⟩
      obtain ⟨q,hq,hp⟩ := mem_iUnion₂.mp (hT hK)
      exact mem_iUnion₂.mpr ⟨q,hq,hB,hp⟩
    _ ≤ ∑ p∈T,cubicThetaPointMeasure
        (cubicThetaQuotientMap ⁻¹' B ∩ (cubicThetaCoveringChart p).source) :=
      measure_biUnion_finset_le T _
    _ ≤ ∑ _p∈T,cubicThetaQuotientMeasure B := by
      apply Finset.sum_le_sum
      intro p _
      have hm := cubicThetaChart_measure_le (cubicThetaCoveringChart p)
        (cubicThetaCoveringChart_coe p) (cubicThetaCoveringChart p).open_source.measurableSet
        (Subset.rfl)
      have hb := hm B
      simpa only [Measure.map_apply cubicThetaQuotientMap_open.continuous.measurable hB,
        Measure.restrict_apply (hB.preimage cubicThetaQuotientMap_open.continuous.measurable)] using hb
    _ = _ := by simp [nsmul_eq_mul]

theorem cubicThetaPositiveStrip_pullback_bound {ε : ℝ} (hε : 0<ε) :
    ∃ N : ℕ,0<N ∧
      (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip ε)).map cubicThetaQuotientMap≤
        (N:ℝ≥0∞) • cubicThetaQuotientMeasure := by
  obtain ⟨K,hK,hcover⟩ := cubicThetaPositiveStrip_compact_cover hε
  obtain ⟨N,hN⟩ := cubicThetaCompact_pullback_bound hK
  refine ⟨N+1,by omega,Measure.le_iff.mpr (fun B hB => ?_)⟩
  have hq := cubicThetaQuotientMap_open.continuous.measurable
  have hpre := hB.preimage hq
  have hN' := hN B
  rw [Measure.map_apply hq hB,Measure.restrict_apply hpre,
    Measure.smul_apply,smul_eq_mul] at hN' ⊢
  have hhigh := (Measure.restrict_le_self (μ:=cubicThetaQuotientMeasure)
    (s:=cubicThetaQuotientMap '' cubicThetaCuspStrip 2)) B
  rw [←cubicThetaInjective_map_restrict (cubicThetaCuspStrip_measurable 2)
    (cubicThetaCuspStrip_injective (by norm_num)),Measure.map_apply hq hB,
    Measure.restrict_apply hpre] at hhigh
  calc
    cubicThetaPointMeasure (cubicThetaQuotientMap ⁻¹' B ∩ cubicThetaCuspStrip ε)≤
        cubicThetaPointMeasure ((cubicThetaQuotientMap ⁻¹' B ∩ K) ∪
          (cubicThetaQuotientMap ⁻¹' B ∩ cubicThetaCuspStrip 2)) := by
      apply measure_mono
      rintro p ⟨hb,hp⟩
      rcases hcover hp with hk|hh
      · exact Or.inl ⟨hb,hk⟩
      · exact Or.inr ⟨hb,hh⟩
    _ ≤ _ := measure_union_le _ _
    _ ≤ (N:ℝ≥0∞)*cubicThetaQuotientMeasure B+cubicThetaQuotientMeasure B :=
      add_le_add hN' hhigh
    _ = _ := by rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBorelTransport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable transport of the quotient's chosen representatives back
upstairs, with the actual cubic character. No smooth representative is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

lemma cubicThetaBorelLift_positive_memLp {ε : ℝ} (hε : 0<ε)
    {f : CubicThetaQuotient → ℂ} (hm : Measurable f) (hf : MemLp f 2 cubicThetaQuotientMeasure) :
    MemLp (cubicThetaBorelLift f) 2
      (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip ε)) := by
  obtain ⟨N,_,hN⟩ := cubicThetaPositiveStrip_pullback_bound hε
  have hi := (hf.integrable_norm_pow (by norm_num)).smul_measure
    (c:=(N:ℝ≥0∞)) (by simp)
  have hc := (hi.mono_measure hN).comp_measurable cubicThetaQuotientMap_open.continuous.measurable
  apply (memLp_two_iff_integrable_sq_norm
    (cubicThetaBorelLift_measurable hm).aestronglyMeasurable).mpr
  simpa only [Function.comp_def,cubicThetaBorelLift_norm] using hc

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTorusCellTransport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact measurable transport between the arithmetic period cell and
the torus. This also applies to measurable L2 representatives. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.cubicThetaTorusCellTransportMeasureSpace
theorem cubicThetaTorusCellPoint_map :
    Measure.map cubicThetaTorusCellPoint volume=
      ENNReal.ofReal (2/(9*Real.sqrt 3)) •
        (volume : Measure ℂ).restrict cubicThetaHorizontalCell := by
  let e := UnitAddTorus.measurableEquivPiIoc (0 : Fin 2 → ℝ)
  let r := fun u : UnitAddTorus (Fin 2) => (e u).val
  have hr : Measurable r := measurable_subtype_coe.comp e.measurable
  have hS : MeasurableSet {x : Fin 2 → ℝ | ∀ i,
      x i∈Ioc ((0 : Fin 2 → ℝ) i) ((0 : Fin 2 → ℝ) i+1)} :=
    MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)
  have hm : Measure.map r volume=
      (volume : Measure (Fin 2 → ℝ)).restrict {x | ∀ i,x i∈Ioc (0:ℝ) 1} := by
    change Measure.map (Subtype.val ∘ e) volume=_
    rw [←Measure.map_map measurable_subtype_coe e.measurable,
      (UnitAddTorus.measurePreserving_equivPiIoc (0 : Fin 2 → ℝ)).map_eq]
    convert! map_comap_subtype_coe hS (volume : Measure (Fin 2 → ℝ)) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext x
    simp
  change Measure.map (cubicThetaPeriodEquiv ∘ r) volume=_
  rw [←Measure.map_map cubicThetaPeriodEquiv.continuous.measurable hr,hm,
    ←cubicThetaCube_halfOpen_measure,←cubicThetaPeriodEquiv_preimage_cell,
    ←Measure.restrict_map cubicThetaPeriodEquiv.continuous.measurable
      cubicThetaHorizontalCell_measurable,cubicThetaPeriodEquiv_map_volume,
    Measure.restrict_smul]

lemma cubicThetaTorusCellPoint_memLp {f : ℂ → ℂ}
    (hf : MemLp f 2 ((volume : Measure ℂ).restrict cubicThetaHorizontalCell)) :
    MemLp (f ∘ cubicThetaTorusCellPoint) 2 volume := by
  have hs := hf.smul_measure (c:=ENNReal.ofReal (2/(9*Real.sqrt 3))) ENNReal.ofReal_ne_top
  rw [←cubicThetaTorusCellPoint_map] at hs
  exact hs.comp_of_map cubicThetaTorusCellPoint_embedding.measurable.aemeasurable

lemma cubicThetaTorusCellPoint_integral (f : ℂ → ℂ) :
    (∫ u : UnitAddTorus (Fin 2),f (cubicThetaTorusCellPoint u))=
      (2/(9*Real.sqrt 3):ℝ) • ∫ z in cubicThetaHorizontalCell,f z := by
  rw [←cubicThetaTorusCellPoint_embedding.integral_map,cubicThetaTorusCellPoint_map,
    integral_smul_measure,ENNReal.toReal_ofReal (by positivity : (0:ℝ)≤2/(9*Real.sqrt 3))]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCellFourierSeparation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual horizontal characters separate square-integrable functions
on the half-open arithmetic cell. No periodic representative is assumed. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.cubicThetaCellFourierSeparationMeasureSpace
lemma cubicThetaCellFourier_coefficient {f : ℂ → ℂ}
    (hf : MemLp f 2 ((volume : Measure ℂ).restrict cubicThetaHorizontalCell))
    (h : Eisenstein) :
    cubicThetaTorusCoefficient ((cubicThetaTorusCellPoint_memLp hf).toLp _) h=
      (2/(9*Real.sqrt 3):ℝ) •
        ∫ z in cubicThetaHorizontalCell,
          star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*f z := by
  unfold cubicThetaTorusCoefficient UnitAddTorus.mFourierCoeff
  simp only [UnitAddTorus.mFourier_neg,starRingEnd_apply,smul_eq_mul]
  calc
    _ = ∫ u : UnitAddTorus (Fin 2),star (cubicThetaTorusFourier h u)*
        f (cubicThetaTorusCellPoint u) := by
      apply integral_congr_ae
      filter_upwards [(cubicThetaTorusCellPoint_memLp hf).coeFn_toLp] with u hu
      rw [hu]
      rfl
    _ = _ := by
      simp_rw [cubicThetaTorusCellPoint_character]
      exact cubicThetaTorusCellPoint_integral (fun z =>
        star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*f z)

theorem cubicThetaCellFourier_separates {f : ℂ → ℂ}
    (hf : MemLp f 2 ((volume : Measure ℂ).restrict cubicThetaHorizontalCell))
    (hzero : ∀ h : Eisenstein,
      (∫ z in cubicThetaHorizontalCell,
        star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*f z)=0) :
    f =ᵐ[(volume : Measure ℂ).restrict cubicThetaHorizontalCell] 0 := by
  let F : CubicThetaTorusL2 := (cubicThetaTorusCellPoint_memLp hf).toLp _
  have hc (h : Eisenstein) : cubicThetaTorusCoefficient F h=0 := by
    rw [cubicThetaCellFourier_coefficient hf,hzero h,smul_zero]
  have hn : ‖F‖^2=0 := by
    rw [←cubicThetaTorus_parseval]
    simp only [hc,norm_zero,zero_pow (by decide : 2≠0),tsum_zero]
  have hF : F=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  have hφ : (f ∘ cubicThetaTorusCellPoint) =ᵐ[volume] 0 :=
    (cubicThetaTorusCellPoint_memLp hf).coeFn_toLp.symm.trans
      (Lp.eq_zero_iff_ae_eq_zero.mp hF)
  have hm : f =ᵐ[Measure.map cubicThetaTorusCellPoint volume] 0 :=
    cubicThetaTorusCellPoint_embedding.ae_map_iff.mpr hφ
  rw [cubicThetaTorusCellPoint_map] at hm
  exact (Measure.ae_ennreal_smul_measure_iff (by positivity :
    ENNReal.ofReal (2/(9*Real.sqrt 3))≠0)).mp hm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveCuspRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma cubicThetaFiniteEnergy_positiveStrip_memLp {ε : ℝ} (hε : 0<ε)
    (F : cubicThetaFiniteEnergySections) :
    MemLp (fun p : CubicThetaPoint => F.val.val p) 2
      (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip ε)) := by
  obtain ⟨N,_,hN⟩ := cubicThetaPositiveStrip_pullback_bound hε
  have h := ((cubicThetaFiniteEnergy_norm_integrable F).smul_measure
    (c:=(N:ℝ≥0∞)) (by simp)).mono_measure hN
  have hi := h.comp_measurable cubicThetaQuotientMap_open.continuous.measurable
  apply (memLp_two_iff_integrable_sq_norm F.val.val.continuous.aestronglyMeasurable).mpr
  simpa only [Function.comp_def,cubicThetaSectionNorm_apply] using hi

def cubicThetaFinitePositiveCuspRestriction {ε : ℝ} (hε : 0<ε) :
    cubicThetaFiniteEnergySections →ₗ[ℂ] CubicThetaPositiveStripL2 ε where
  toFun F := (cubicThetaFiniteEnergy_positiveStrip_memLp hε F).toLp _
  map_add' F G := MemLp.toLp_add
    (cubicThetaFiniteEnergy_positiveStrip_memLp hε F)
    (cubicThetaFiniteEnergy_positiveStrip_memLp hε G)
  map_smul' c F := MemLp.toLp_const_smul c
    (cubicThetaFiniteEnergy_positiveStrip_memLp hε F)

lemma cubicThetaFinitePositiveCuspRestriction_norm_sq {ε : ℝ} (hε : 0<ε)
    (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaFinitePositiveCuspRestriction hε F‖^2=
      ∫ p in cubicThetaCuspStrip ε,‖F.val.val p‖^2 ∂cubicThetaPointMeasure := by
  rw [cubicTheta_l2_norm_sq_measure]
  apply integral_congr_ae
  filter_upwards [(cubicThetaFiniteEnergy_positiveStrip_memLp hε F).coeFn_toLp] with p hp
  change ‖((cubicThetaFiniteEnergy_positiveStrip_memLp hε F).toLp _) p‖^2=_
  rw [hp]

lemma cubicThetaFinitePositiveCuspRestriction_bound {ε : ℝ} (hε : 0<ε) :
    ∃ C,∀ F : cubicThetaFiniteEnergySections,
      ‖cubicThetaFinitePositiveCuspRestriction hε F‖≤
        C*‖cubicThetaFiniteEnergyEmbedding F‖ := by
  obtain ⟨N,_,hN⟩ := cubicThetaPositiveStrip_pullback_bound hε
  refine ⟨Real.sqrt N,fun F => ?_⟩
  have hf := (cubicThetaFiniteEnergy_norm_integrable F).smul_measure
    (c:=(N:ℝ≥0∞)) (by simp)
  have hi := integral_mono_measure hN
    (ae_of_all _ (fun q => sq_nonneg (cubicThetaSectionNorm F q))) hf
  rw [integral_map cubicThetaQuotientMap_open.continuous.measurable.aemeasurable
    (hf.aestronglyMeasurable.mono_measure hN),integral_smul_measure] at hi
  simp only [cubicThetaSectionNorm_apply,ENNReal.toReal_natCast,
    smul_eq_mul] at hi
  rw [←cubicThetaFinitePositiveCuspRestriction_norm_sq hε,
    ←cubicThetaFiniteEnergyValue_norm_sq] at hi
  have hs : (Real.sqrt N*‖cubicThetaFiniteEnergyValue F‖)^2=
      N*‖cubicThetaFiniteEnergyValue F‖^2 := by
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
  have hb : ‖cubicThetaFinitePositiveCuspRestriction hε F‖≤
      Real.sqrt N*‖cubicThetaFiniteEnergyValue F‖ :=
    _root_.le_of_sq_le_sq (hi.trans_eq hs.symm)
      (mul_nonneg (Real.sqrt_nonneg N) (_root_.norm_nonneg _))
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg N)
  exact cubicThetaGlobalInclusion_bound (cubicThetaFiniteEnergyEmbedding F)

attribute [local instance] OAI.CubicFirstMoment.positiveCuspRestriction_finiteEnergyAdd
def cubicThetaPositiveCuspRestriction {ε : ℝ} (hε : 0<ε) :
    cubicThetaGlobalEnergySpace →L[ℂ] CubicThetaPositiveStripL2 ε :=
  LinearMap.extendOfNorm (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (E:=cubicThetaFiniteEnergySections) (Eₗ:=cubicThetaGlobalEnergySpace)
    (F:=CubicThetaPositiveStripL2 ε)
    (cubicThetaFinitePositiveCuspRestriction hε) cubicThetaFiniteEnergyEmbedding

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveModelL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal arithmetic series in the L2 space of every positive
height strip, with its scalar still retained. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaArithmeticModel_positive_memLp (A : ℂ) {ε : ℝ} (hε : 0<ε) :
    MemLp (fun p : CubicThetaPoint => cubicThetaArithmeticModel A p.val) 2
      (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip ε)) := by
  obtain ⟨K,hK,hcover⟩ := cubicThetaPositiveStrip_compact_cover hε
  have hc := cubicThetaArithmeticModel_point_continuous A
  have hlow : IntegrableOn (fun p : CubicThetaPoint =>
      ‖cubicThetaArithmeticModel A p.val‖^2) K cubicThetaPointMeasure :=
    (hc.norm.pow 2).continuousOn.integrableOn_compact hK
  have hhigh := (cubicThetaArithmeticModel_memLp A).integrable_norm_pow (by norm_num)
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  exact (hlow.union hhigh).mono_set hcover

def cubicThetaPositiveModelStrip (A : ℂ) {ε : ℝ} (hε : 0<ε) :
    CubicThetaPositiveStripL2 ε :=
  (cubicThetaArithmeticModel_positive_memLp A hε).toLp _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveStripRepresentative
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable coordinate representative of every positive-strip L2
vector, with its first and second moment densities on the literal cell. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace CubicFirstMoment
variable {ε : ℝ}

theorem cubicThetaPositiveStripRepresentative_pairing (hε : 0<ε) (F : CubicThetaPositiveStripL2 ε)
    (h : Eisenstein) (W : CompactlySupportedContinuousMap ℝ ℂ) :
    inner ℂ (cubicThetaPositiveStripFourierTest hε h W) F=
      ∫ v in Ioi ε,star (W v)/(v:ℂ)^3*
        ∫ z in cubicThetaHorizontalCell,
          star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*
            cubicThetaPositiveStripRepresentative F (z,v) := by
  have hi : IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*
        cubicThetaPositiveStripRepresentative F (cubicThetaPointCoordinates p))
      (cubicThetaCuspStrip ε) cubicThetaPointMeasure := by
    simpa only [cubicThetaPositiveStripRepresentative_coordinates] using
      cubicThetaPositiveStripRepresentative_pair_integrable hε F h W
  have he := cubicThetaPositiveCuspStrip_fubini hε.le
    (fun y => star (W y.2*(Real.fourierChar (tracePair y.1 (cubicThetaRowFrequency h)):ℂ))*
      cubicThetaPositiveStripRepresentative F y) hi
  change (∫ p in cubicThetaCuspStrip ε,
    star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*
      cubicThetaPositiveStripRepresentative F (cubicThetaPointCoordinates p) ∂cubicThetaPointMeasure)=_ at he
  rw [L2.inner_def]
  calc
    _ = ∫ p in cubicThetaCuspStrip ε,
        star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*
          cubicThetaPositiveStripRepresentative F (cubicThetaPointCoordinates p) ∂cubicThetaPointMeasure := by
      apply integral_congr_ae
      filter_upwards [(cubicThetaPositiveFourierWeight_memLp hε h W).coeFn_toLp] with p hp
      change inner ℂ (((cubicThetaPositiveFourierWeight_memLp hε h W).toLp _) p) (F p)=_
      rw [hp,cubicThetaPositiveStripRepresentative_coordinates,RCLike.inner_apply]
      simp only [starRingEnd_apply,cubicThetaCuspFourierWeight]
      ring
    _ = _ := by
      rw [he]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v _
      dsimp only
      rw [←integral_const_mul]
      apply setIntegral_congr_fun cubicThetaHorizontalCell_measurable
      intro z _
      simp only [star_mul]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveStripHorizontalDensity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact radial tests recover the horizontal Fourier coefficient
of an arbitrary cusp L2 vector at almost every height. -/
noncomputable section
open MeasureTheory Set
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment
variable {ε : ℝ}

lemma cubicThetaPositiveStripHorizontalDensity_pairing (hε : 0<ε) (F : CubicThetaPositiveStripL2 ε) (h : Eisenstein)
    (W : C_c(ℝ,ℂ)) :
    inner ℂ (cubicThetaPositiveStripFourierTest hε h W) F=
      ∫ v in Ioi ε,star (W v)*cubicThetaPositiveStripHorizontalDensity F h v := by
  rw [cubicThetaPositiveStripRepresentative_pairing hε]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  dsimp only
  unfold cubicThetaPositiveStripHorizontalDensity
  rw [integral_div]
  ring

theorem cubicThetaPositiveStripHorizontalDensity_zero (hε : 0<ε) (F : CubicThetaPositiveStripL2 ε) (h : Eisenstein)
    (hzero : ∀ W : C_c(ℝ,ℂ), (∀ v≤ε,W v=0) →
      ContDiff ℝ ∞ (W : ℝ → ℂ) →
      inner ℂ (cubicThetaPositiveStripFourierTest hε h W) F=0) :
    ∀ᵐ v ∂volume, v∈Ioi ε → cubicThetaPositiveStripHorizontalDensity F h v=0 := by
  apply isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (cubicThetaPositiveStripHorizontalDensity_integrable hε F h).locallyIntegrableOn
  intro g hg hgs hs
  let W : C_c(ℝ,ℂ) :=
    ⟨⟨fun v => (g v:ℂ),Complex.continuous_ofReal.comp hg.continuous⟩,
      hgs.comp_left Complex.ofReal_zero⟩
  have hW (v : ℝ) (hv : v≤ε) : W v=0 := by
    have hz : g v=0 := image_eq_zero_of_notMem_tsupport
      (fun hv' => (not_lt_of_ge hv) (hs hv'))
    change (g v:ℂ)=0
    rw [hz,Complex.ofReal_zero]
  have hsm : ContDiff ℝ ∞ (W : ℝ → ℂ) := by
    change ContDiff ℝ ∞ (fun v => (g v:ℂ))
    exact Complex.ofRealCLM.contDiff.comp hg
  have he := hzero W hW hsm
  rw [cubicThetaPositiveStripHorizontalDensity_pairing hε] at he
  have hf : (∫ v in Ioi ε, g v • cubicThetaPositiveStripHorizontalDensity F h v)=0 := by
    simpa only [W,CompactlySupportedContinuousMap.coe_mk,ContinuousMap.coe_mk,
      Complex.star_def,Complex.conj_ofReal,Complex.real_smul] using he
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero (s:=Ioi ε)]
  · exact hf
  · intro v hv
    have hz : g v=0 := image_eq_zero_of_notMem_tsupport (fun hv' => hv (hs hv'))
    rw [hz,zero_smul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveStripFourierSeparation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact radial weights and the actual horizontal characters jointly
separate the literal cusp L2 space. -/
noncomputable section
open MeasureTheory Set
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment
variable {ε : ℝ}

attribute [local instance] OAI.CubicFirstMoment.cubicThetaPositiveStripFourierSeparationCountable
theorem cubicThetaPositiveStripFourier_separates (hε : 0<ε) (F : CubicThetaPositiveStripL2 ε)
    (hzero : ∀ (h : Eisenstein) (W : C_c(ℝ,ℂ)), (∀ v≤ε,W v=0) →
      ContDiff ℝ ∞ (W : ℝ → ℂ) →
      inner ℂ (cubicThetaPositiveStripFourierTest hε h W) F=0) : F=0 := by
  have hD : ∀ᵐ v ∂(volume : Measure ℝ),∀ h : Eisenstein,
      v∈Ioi ε → cubicThetaPositiveStripHorizontalDensity F h v=0 :=
    ae_all_iff.mpr (fun h => cubicThetaPositiveStripHorizontalDensity_zero hε F h (hzero h))
  have hfiber : ∀ᵐ v ∂(volume : Measure ℝ).restrict (Ioi ε),
      (fun z : ℂ => cubicThetaPositiveStripRepresentative F (z,v))
        =ᵐ[(volume : Measure ℂ).restrict cubicThetaHorizontalCell] 0 := by
    filter_upwards [cubicThetaPositiveStripRepresentative_fiber_memLp hε F,
      ae_restrict_of_ae hD,ae_restrict_mem measurableSet_Ioi] with v hv hD hv2
    apply cubicThetaCellFourier_separates hv
    intro h
    have he := hD h hv2
    rw [cubicThetaPositiveStripHorizontalDensity,integral_div] at he
    have hv0 : (v:ℂ)^3≠0 := pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr
      ((hε.trans hv2).ne'))
    simpa only [zero_mul] using (div_eq_iff hv0).mp he
  have hm : MeasurableSet {y : ℂ × ℝ | cubicThetaPositiveStripRepresentative F y=0} :=
    measurableSet_eq_fun (cubicThetaPositiveStripRepresentative_measurable F).measurable measurable_const
  have hj : ∀ᵐ y ∂((volume : Measure ℂ).restrict cubicThetaHorizontalCell).prod
      ((volume : Measure ℝ).restrict (Ioi ε)), cubicThetaPositiveStripRepresentative F y=0 :=
    (Measure.ae_prod_iff_ae_ae hm).mpr ((Measure.ae_ae_comm hm).mpr hfiber)
  rw [Measure.prod_restrict] at hj
  have hn : ‖F‖^2=0 := by
    calc
      _ = ∫ p in cubicThetaCuspStrip ε, ‖F p‖^2 ∂cubicThetaPointMeasure :=
        cubicTheta_l2_norm_sq_measure F
      _ = ∫ p in cubicThetaCuspStrip ε,
          ‖cubicThetaPositiveStripRepresentative F (cubicThetaPointCoordinates p)‖^2
            ∂cubicThetaPointMeasure := by
        apply integral_congr_ae
        filter_upwards with p
        rw [cubicThetaPositiveStripRepresentative_coordinates]
      _ = ∫ y in cubicThetaHorizontalCell ×ˢ Ioi ε,
          ‖cubicThetaPositiveStripRepresentative F y‖^2/y.2^3 := by
        have he := cubicThetaPointIntegral_density (cubicThetaCuspStrip_measurable ε)
          (fun y => ‖cubicThetaPositiveStripRepresentative F y‖^2)
        rw [cubicThetaCuspStrip_coordinates hε.le] at he
        exact he
      _ = 0 := integral_eq_zero_of_ae (hj.mono (fun y hy => by simp only [hy,norm_zero,zero_pow (by decide : 2≠0),zero_div,Pi.zero_apply]))
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveStripPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaPositiveStrip_inner_formula {ε : ℝ} (hε : 0<ε)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) (f : ℂ × ℝ → ℂ)
    (hf : MemLp (fun p : CubicThetaPoint => f p.val) 2
      (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip ε))) :
    inner ℂ (cubicThetaPositiveStripFourierTest hε h W) (hf.toLp _)=
      ∫ v in Ioi ε,star (W v)/(v:ℂ)^3*
        ∫ z in cubicThetaHorizontalCell,
          star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*f (z,v) := by
  have hi := L2.integrable_inner (𝕜:=ℂ)
    (cubicThetaPositiveStripFourierTest hε h W) (hf.toLp _)
  have hp : IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*f p.val)
      (cubicThetaCuspStrip ε) cubicThetaPointMeasure := by
    apply hi.congr
    filter_upwards [(cubicThetaPositiveFourierWeight_memLp hε h W).coeFn_toLp,
      hf.coeFn_toLp] with p hW hf
    change inner ℂ (((cubicThetaPositiveFourierWeight_memLp hε h W).toLp _) p) _=_
    rw [hW,hf,RCLike.inner_apply]
    simp only [starRingEnd_apply,cubicThetaCuspFourierWeight]
    ring
  have he := cubicThetaPositiveCuspStrip_fubini hε.le
    (fun y => star (W y.2*(Real.fourierChar (tracePair y.1 (cubicThetaRowFrequency h)):ℂ))*f y) hp
  change (∫ p in cubicThetaCuspStrip ε,
    star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*f p.val
      ∂cubicThetaPointMeasure)=_ at he
  rw [L2.inner_def]
  calc
    _ = ∫ p in cubicThetaCuspStrip ε,
        star (W p.val.2*(Real.fourierChar (tracePair p.val.1 (cubicThetaRowFrequency h)):ℂ))*f p.val
          ∂cubicThetaPointMeasure := by
      apply integral_congr_ae
      filter_upwards [(cubicThetaPositiveFourierWeight_memLp hε h W).coeFn_toLp,
        hf.coeFn_toLp] with p hW hf
      change inner ℂ (((cubicThetaPositiveFourierWeight_memLp hε h W).toLp _) p) _=_
      rw [hW,hf,RCLike.inner_apply]
      simp only [starRingEnd_apply,cubicThetaCuspFourierWeight]
      ring
    _ = _ := by
      rw [he]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v _
      dsimp only
      rw [←integral_const_mul]
      apply setIntegral_congr_fun cubicThetaHorizontalCell_measurable
      intro z _
      simp only [star_mul]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBorelRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaPositiveStrip_pull_ae {ε : ℝ} (hε : 0<ε)
    {P : CubicThetaQuotient → Prop} (hP : ∀ᵐ q ∂cubicThetaQuotientMeasure,P q) :
    ∀ᵐ p ∂cubicThetaPointMeasure.restrict (cubicThetaCuspStrip ε),P (cubicThetaQuotientMap p) := by
  obtain ⟨N,hNpos,hN⟩ := cubicThetaPositiveStrip_pullback_bound hε
  have hNne : (N:ℝ≥0∞)≠0 := by exact_mod_cast hNpos.ne'
  have hs : ∀ᵐ q ∂(N:ℝ≥0∞) • cubicThetaQuotientMeasure,P q :=
    (Measure.ae_ennreal_smul_measure_iff hNne).mpr hP
  exact ae_of_ae_map cubicThetaQuotientMap_open.continuous.measurable.aemeasurable
    (ae_mono hN hs)

def cubicThetaBorelRestrictionLinear {ε : ℝ} (hε : 0<ε) :
    CubicThetaGlobalL2 →ₗ[ℂ] CubicThetaPositiveStripL2 ε where
  toFun F := (cubicThetaBorelLift_positive_memLp hε (Lp.stronglyMeasurable F).measurable
    (Lp.memLp F)).toLp _
  map_add' F G := by
    apply Lp.ext
    filter_upwards [
      (cubicThetaBorelLift_positive_memLp hε (Lp.stronglyMeasurable (F+G)).measurable
        (Lp.memLp (F+G))).coeFn_toLp,
      (cubicThetaBorelLift_positive_memLp hε (Lp.stronglyMeasurable F).measurable
        (Lp.memLp F)).coeFn_toLp,
      (cubicThetaBorelLift_positive_memLp hε (Lp.stronglyMeasurable G).measurable
        (Lp.memLp G)).coeFn_toLp,
      Lp.coeFn_add
        ((cubicThetaBorelLift_positive_memLp hε (Lp.stronglyMeasurable F).measurable
          (Lp.memLp F)).toLp _)
        ((cubicThetaBorelLift_positive_memLp hε (Lp.stronglyMeasurable G).measurable
          (Lp.memLp G)).toLp _),
      cubicThetaPositiveStrip_pull_ae hε (Lp.coeFn_add F G)] with p hFG hF hG hadd hq
    change ((cubicThetaBorelLift_positive_memLp hε
      (Lp.stronglyMeasurable (F+G)).measurable (Lp.memLp (F+G))).toLp _) p=_
    rw [hFG,hadd]
    simp only [Pi.add_apply]
    rw [hF,hG]
    simp only [cubicThetaBorelLift,Pi.add_apply] at hq ⊢
    rw [hq,mul_add]
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [
      (cubicThetaBorelLift_positive_memLp hε (Lp.stronglyMeasurable (c • F)).measurable
        (Lp.memLp (c • F))).coeFn_toLp,
      (cubicThetaBorelLift_positive_memLp hε (Lp.stronglyMeasurable F).measurable
        (Lp.memLp F)).coeFn_toLp,
      Lp.coeFn_smul c ((cubicThetaBorelLift_positive_memLp hε
        (Lp.stronglyMeasurable F).measurable (Lp.memLp F)).toLp _),
      cubicThetaPositiveStrip_pull_ae hε (Lp.coeFn_smul c F)] with p hCF hF hsm hq
    change ((cubicThetaBorelLift_positive_memLp hε
      (Lp.stronglyMeasurable (c • F)).measurable (Lp.memLp (c • F))).toLp _) p=_
    simp only [RingHom.id_apply]
    rw [hCF,hsm]
    simp only [Pi.smul_apply]
    rw [hF]
    simp only [cubicThetaBorelLift,Pi.smul_apply,smul_eq_mul] at hq ⊢
    rw [hq]
    ring

lemma cubicThetaBorelRestrictionLinear_bound {ε : ℝ} (hε : 0<ε) :
    ∃ C,∀ F : CubicThetaGlobalL2,‖cubicThetaBorelRestrictionLinear hε F‖≤C*‖F‖ := by
  obtain ⟨N,_,hN⟩ := cubicThetaPositiveStrip_pullback_bound hε
  refine ⟨Real.sqrt N,fun F => ?_⟩
  have hf := ((Lp.memLp F).integrable_norm_pow (by norm_num)).smul_measure
    (c:=(N:ℝ≥0∞)) (by simp)
  have hi := integral_mono_measure hN (ae_of_all _ (fun q => sq_nonneg ‖F q‖)) hf
  rw [integral_map cubicThetaQuotientMap_open.continuous.measurable.aemeasurable
    (hf.aestronglyMeasurable.mono_measure hN),integral_smul_measure] at hi
  simp only [ENNReal.toReal_natCast,smul_eq_mul] at hi
  rw [←cubicTheta_l2_norm_sq_measure F] at hi
  have he : ‖cubicThetaBorelRestrictionLinear hε F‖^2=
      ∫ p in cubicThetaCuspStrip ε,‖F (cubicThetaQuotientMap p)‖^2 ∂cubicThetaPointMeasure := by
    rw [cubicTheta_l2_norm_sq_measure]
    apply integral_congr_ae
    filter_upwards [(cubicThetaBorelLift_positive_memLp hε
      (Lp.stronglyMeasurable F).measurable (Lp.memLp F)).coeFn_toLp] with p hp
    change ‖((cubicThetaBorelLift_positive_memLp hε
      (Lp.stronglyMeasurable F).measurable (Lp.memLp F)).toLp _) p‖^2=_
    rw [hp,cubicThetaBorelLift_norm]
  rw [←he] at hi
  have hs : (Real.sqrt N*‖F‖)^2=N*‖F‖^2 := by
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
  exact _root_.le_of_sq_le_sq (hi.trans_eq hs.symm)
    (mul_nonneg (Real.sqrt_nonneg N) (_root_.norm_nonneg F))

def cubicThetaBorelRestriction {ε : ℝ} (hε : 0<ε) :
    CubicThetaGlobalL2 →L[ℂ] CubicThetaPositiveStripL2 ε :=
  (cubicThetaBorelRestrictionLinear hε).mkContinuousOfExistsBound
    (cubicThetaBorelRestrictionLinear_bound hε)

lemma cubicThetaBorelRestriction_coe {ε : ℝ} (hε : 0<ε) (F : CubicThetaGlobalL2) :
    cubicThetaBorelRestriction hε F =ᵐ[cubicThetaPointMeasure.restrict (cubicThetaCuspStrip ε)]
      cubicThetaBorelLift (F : CubicThetaQuotient → ℂ) :=
  (cubicThetaBorelLift_positive_memLp hε
    (Lp.stronglyMeasurable F).measurable (Lp.memLp F)).coeFn_toLp

lemma cubicThetaBorelRestriction_finite {ε : ℝ} (hε : 0<ε)
    (F : cubicThetaFiniteEnergySections) :
    cubicThetaBorelRestriction hε (cubicThetaFiniteEnergyValue F)=
      cubicThetaFinitePositiveCuspRestriction hε F := by
  apply Lp.ext
  filter_upwards [cubicThetaBorelRestriction_coe hε (cubicThetaFiniteEnergyValue F),
    (cubicThetaFiniteEnergy_positiveStrip_memLp hε F).coeFn_toLp,
    cubicThetaPositiveStrip_pull_ae hε F.property.2.1.coeFn_toLp] with p hB hF hq
  change (cubicThetaFiniteEnergyValue F) (cubicThetaQuotientMap p)=
    cubicThetaSectionRepresentative F (cubicThetaQuotientMap p) at hq
  change _=((cubicThetaFiniteEnergy_positiveStrip_memLp hε F).toLp _) p
  rw [hB,hF,cubicThetaBorelLift,hq]
  exact cubicThetaBorelLift_section F p

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactBorelRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded compact restriction of the actual global L2 lift. This
permits cusp Fourier windows after arbitrary integral coordinate changes. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

lemma cubicThetaCompact_pull_ae {K : Set CubicThetaPoint} (hK : IsCompact K)
    {P : CubicThetaQuotient → Prop} (hP : ∀ᵐ q ∂cubicThetaQuotientMeasure,P q) :
    ∀ᵐ p ∂cubicThetaPointMeasure.restrict K,P (cubicThetaQuotientMap p) := by
  obtain ⟨N,hN⟩ := cubicThetaCompact_pullback_bound hK
  have hs : ∀ᵐ q ∂(N:ℝ≥0∞) • cubicThetaQuotientMeasure,P q :=
    Measure.ae_smul_measure hP _
  exact ae_of_ae_map cubicThetaQuotientMap_open.continuous.measurable.aemeasurable
    (ae_mono hN hs)

lemma cubicThetaBorelLift_compact_memLp {K : Set CubicThetaPoint} (hK : IsCompact K)
    {f : CubicThetaQuotient → ℂ} (hm : Measurable f) (hf : MemLp f 2 cubicThetaQuotientMeasure) :
    MemLp (cubicThetaBorelLift f) 2 (cubicThetaPointMeasure.restrict K) := by
  obtain ⟨N,hN⟩ := cubicThetaCompact_pullback_bound hK
  have hi := (hf.integrable_norm_pow (by norm_num)).smul_measure
    (c:=(N:ℝ≥0∞)) (by simp)
  have hc := (hi.mono_measure hN).comp_measurable cubicThetaQuotientMap_open.continuous.measurable
  apply (memLp_two_iff_integrable_sq_norm
    (cubicThetaBorelLift_measurable hm).aestronglyMeasurable).mpr
  simpa only [Function.comp_def,cubicThetaBorelLift_norm] using hc

def cubicThetaCompactBorelRestrictionLinear {K : Set CubicThetaPoint} (hK : IsCompact K) :
    CubicThetaGlobalL2 →ₗ[ℂ] Lp ℂ 2 (cubicThetaPointMeasure.restrict K) where
  toFun F := (cubicThetaBorelLift_compact_memLp hK (Lp.stronglyMeasurable F).measurable
    (Lp.memLp F)).toLp _
  map_add' F G := by
    apply Lp.ext
    filter_upwards [
      (cubicThetaBorelLift_compact_memLp hK (Lp.stronglyMeasurable (F+G)).measurable
        (Lp.memLp (F+G))).coeFn_toLp,
      (cubicThetaBorelLift_compact_memLp hK (Lp.stronglyMeasurable F).measurable
        (Lp.memLp F)).coeFn_toLp,
      (cubicThetaBorelLift_compact_memLp hK (Lp.stronglyMeasurable G).measurable
        (Lp.memLp G)).coeFn_toLp,
      Lp.coeFn_add
        ((cubicThetaBorelLift_compact_memLp hK (Lp.stronglyMeasurable F).measurable
          (Lp.memLp F)).toLp _)
        ((cubicThetaBorelLift_compact_memLp hK (Lp.stronglyMeasurable G).measurable
          (Lp.memLp G)).toLp _),
      cubicThetaCompact_pull_ae hK (Lp.coeFn_add F G)] with p hFG hF hG hadd hq
    change ((cubicThetaBorelLift_compact_memLp hK
      (Lp.stronglyMeasurable (F+G)).measurable (Lp.memLp (F+G))).toLp _) p=_
    rw [hFG,hadd]
    simp only [Pi.add_apply]
    rw [hF,hG]
    simp only [cubicThetaBorelLift,Pi.add_apply] at hq ⊢
    rw [hq,mul_add]
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [
      (cubicThetaBorelLift_compact_memLp hK (Lp.stronglyMeasurable (c • F)).measurable
        (Lp.memLp (c • F))).coeFn_toLp,
      (cubicThetaBorelLift_compact_memLp hK (Lp.stronglyMeasurable F).measurable
        (Lp.memLp F)).coeFn_toLp,
      Lp.coeFn_smul c ((cubicThetaBorelLift_compact_memLp hK
        (Lp.stronglyMeasurable F).measurable (Lp.memLp F)).toLp _),
      cubicThetaCompact_pull_ae hK (Lp.coeFn_smul c F)] with p hCF hF hsm hq
    change ((cubicThetaBorelLift_compact_memLp hK
      (Lp.stronglyMeasurable (c • F)).measurable (Lp.memLp (c • F))).toLp _) p=_
    simp only [RingHom.id_apply]
    rw [hCF,hsm]
    simp only [Pi.smul_apply]
    rw [hF]
    simp only [cubicThetaBorelLift,Pi.smul_apply,smul_eq_mul] at hq ⊢
    rw [hq]
    ring

lemma cubicThetaCompactBorelRestrictionLinear_bound {K : Set CubicThetaPoint} (hK : IsCompact K) :
    ∃ C,∀ F : CubicThetaGlobalL2,‖cubicThetaCompactBorelRestrictionLinear hK F‖≤C*‖F‖ := by
  obtain ⟨N,hN⟩ := cubicThetaCompact_pullback_bound hK
  refine ⟨Real.sqrt N,fun F => ?_⟩
  have hf := ((Lp.memLp F).integrable_norm_pow (by norm_num)).smul_measure
    (c:=(N:ℝ≥0∞)) (by simp)
  have hi := integral_mono_measure hN (ae_of_all _ (fun q => sq_nonneg ‖F q‖)) hf
  rw [integral_map cubicThetaQuotientMap_open.continuous.measurable.aemeasurable
    (hf.aestronglyMeasurable.mono_measure hN),integral_smul_measure] at hi
  simp only [ENNReal.toReal_natCast,smul_eq_mul] at hi
  rw [←cubicTheta_l2_norm_sq_measure F] at hi
  have he : ‖cubicThetaCompactBorelRestrictionLinear hK F‖^2=
      ∫ p in K,‖F (cubicThetaQuotientMap p)‖^2 ∂cubicThetaPointMeasure := by
    rw [cubicTheta_l2_norm_sq_measure]
    apply integral_congr_ae
    filter_upwards [(cubicThetaBorelLift_compact_memLp hK
      (Lp.stronglyMeasurable F).measurable (Lp.memLp F)).coeFn_toLp] with p hp
    change ‖((cubicThetaBorelLift_compact_memLp hK
      (Lp.stronglyMeasurable F).measurable (Lp.memLp F)).toLp _) p‖^2=_
    rw [hp,cubicThetaBorelLift_norm]
  rw [←he] at hi
  have hs : (Real.sqrt N*‖F‖)^2=N*‖F‖^2 := by
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
  exact _root_.le_of_sq_le_sq (hi.trans_eq hs.symm)
    (mul_nonneg (Real.sqrt_nonneg N) (_root_.norm_nonneg F))

def cubicThetaCompactBorelRestriction {K : Set CubicThetaPoint} (hK : IsCompact K) :
    CubicThetaGlobalL2 →L[ℂ] Lp ℂ 2 (cubicThetaPointMeasure.restrict K) :=
  (cubicThetaCompactBorelRestrictionLinear hK).mkContinuousOfExistsBound
    (cubicThetaCompactBorelRestrictionLinear_bound hK)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactIntegralRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact sampling after a literal integral Mobius transformation.
The map acts on actual global L2 vectors and retains the cubic Borel phase. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCompactIntegral_measure (δ : SL(2,Eisenstein))
    {K : Set CubicThetaPoint} (hK : IsCompact K) :
    MeasurePreserving (fun p : CubicThetaPoint => δ • p)
      (cubicThetaPointMeasure.restrict K)
      (cubicThetaPointMeasure.restrict ((fun p : CubicThetaPoint => δ • p) '' K)) :=
  ⟨measurable_const_smul δ,cubicThetaSmul_map_restrict δ hK.measurableSet⟩

def cubicThetaCompactIntegralRestriction (δ : SL(2,Eisenstein))
    {K : Set CubicThetaPoint} (hK : IsCompact K) :
    CubicThetaGlobalL2 →L[ℂ] Lp ℂ 2 (cubicThetaPointMeasure.restrict K) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun p : CubicThetaPoint => δ • p)
    (cubicThetaCompactIntegral_measure δ hK)).toContinuousLinearMap.comp
      (cubicThetaCompactBorelRestriction (hK.image (continuous_const_smul δ)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactShiftedFamily
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded observations of the actual translated-cusp Eisenstein family.
Their residues are the already constructed arithmetic theta model, sampled
at the same Mobius transform. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace CubicFirstMoment

def cubicThetaCompactShiftedFamily (b : Eisenstein) {K : Set CubicThetaPoint}
    (hK : IsCompact K) (s : ℂ) : Lp ℂ 2 (cubicThetaPointMeasure.restrict K) :=
  cubicThetaCompactIntegralRestriction (cubicThetaShiftedInversion b) hK
    (cubicThetaResidueScale • cubicThetaForcedResolvent s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactShiftedObservation
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded scalar observations of the translated family and its actual residue. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace CubicFirstMoment

def cubicThetaCompactShiftedObservation (b : Eisenstein) {K : Set CubicThetaPoint}
    (hK : IsCompact K) (T : Lp ℂ 2 (cubicThetaPointMeasure.restrict K)) (s : ℂ) : ℂ :=
  inner ℂ T (cubicThetaCompactShiftedFamily b hK s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedPeriodMeasure
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual period-nine cell and its exact volume normalization. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaShiftedHorizontalCell_measurable : MeasurableSet cubicThetaShiftedHorizontalCell :=
  (complexMulEquiv 3 (by norm_num)).toHomeomorph.measurableEmbedding.measurableSet_image'
    cubicThetaHorizontalCell_measurable

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedWindow
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact height windows in the actual period-nine cusp cell. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaShiftedWindow_measurable (a d : ℝ) :
    MeasurableSet (cubicThetaShiftedWindow a d) := by
  have hf : Continuous (fun p : CubicThetaPoint => p.val.1) := by fun_prop
  have hg : Continuous (fun p : CubicThetaPoint => p.val.2) := by fun_prop
  exact (cubicThetaShiftedHorizontalCell_measurable.preimage hf.measurable).inter
    (measurableSet_Icc.preimage hg.measurable)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedWindowTest
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual bounded Fourier tests on finite translated-cusp windows. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaShiftedWindowWeight_memLp (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (a d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K) :
    MemLp ((cubicThetaShiftedWindow a d).indicator (cubicThetaShiftedFourierWeight h W))
      2 (cubicThetaPointMeasure.restrict K) := by
  classical
  let : IsFiniteMeasure (cubicThetaPointMeasure.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_ne_top
  obtain ⟨C,hC⟩ := W.hasCompactSupport.exists_bound_of_continuousOn W.continuous.continuousOn
  apply MemLp.of_bound
    ((cubicThetaShiftedFourierWeight_continuous h W).aestronglyMeasurable.indicator
      (cubicThetaShiftedWindow_measurable a d)) (max C 0)
  apply Filter.Eventually.of_forall
  intro p
  by_cases hp : p∈cubicThetaShiftedWindow a d
  · rw [indicator_of_mem hp,cubicThetaShiftedFourierWeight,norm_mul,Circle.norm_coe,mul_one]
    by_cases hv : p.val.2∈tsupport W
    · exact (hC _ hv).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hv,norm_zero]
      exact le_max_right _ _
  · rw [indicator_of_notMem hp,norm_zero]
    exact le_max_right _ _

def cubicThetaShiftedWindowTest (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (a d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K) :
    Lp ℂ 2 (cubicThetaPointMeasure.restrict K) :=
  (cubicThetaShiftedWindowWeight_memLp h W a d hK).toLp _

def cubicThetaShiftedWindowObservation (b h : Eisenstein) (W : C_c(ℝ,ℂ))
    (a d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K) (s : ℂ) : ℂ :=
  cubicThetaCompactShiftedObservation b hK (cubicThetaShiftedWindowTest h W a d hK) s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedHorizontalContinuity
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity of the actual translated theta coefficient and its radial kernel. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace CubicFirstMoment

def cubicThetaShiftedModelHorizontal (b h : Eisenstein) (v : ℝ) : ℂ :=
  ∫ z in cubicThetaShiftedHorizontalCell,
    star (Real.fourierChar (tracePair z (cubicThetaShiftedRowFrequency h)):ℂ)*
      cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
        (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) (z,v))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedFullObservation
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full translated-cusp observation, including the entire incoming
correction at low height. Its residue is unchanged. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaShiftedFullObservation (b h : Eisenstein) (W : C_c(ℝ,ℂ))
    (a d : ℝ) {K : Set CubicThetaPoint} (hK : IsCompact K) (s : ℂ) : ℂ :=
  cubicThetaShiftedWindowObservation b h W a d hK s+
    cubicThetaResidueScale*cubicThetaShiftedIncomingWindow b h W a d s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspTypes
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three translated inversion types needed for primary bottom rows.
The actual constant is retained at the trivial type. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaCuspExpansion (n : ℤ) (p : ℂ×ℝ) : ℂ :=
  if (3:ℤ) ∣ n then
    cubicThetaSeriesConstant*((p.2^(2/3:ℝ):ℝ):ℂ)+
      cubicThetaNonconstant cubicThetaArithmeticCoefficient p
  else cubicThetaNonconstant (cubicThetaShiftedLatticeCoefficient n) p

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProjectedPlane
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual projected cusp expansion supports the same angular
extraction as the original theta series, with its own literal coefficients. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology MatrixGroups
namespace CubicFirstMoment

def cubicThetaProjectedPlane (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (p : ℂ×ℝ) : ℂ :=
  cubicThetaProjectedConstant g hc*((p.2^(2/3:ℝ):ℝ):ℂ)+
    cubicThetaNonconstant (cubicThetaProjectedCoefficient g hc) p

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProjectedConstant
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual radial constant in the adapted primary cusp. The arithmetic
base scalar is retained, including after finite character averaging. -/
noncomputable section
open scoped BigOperators MatrixGroups
namespace CubicFirstMoment

def cubicThetaResidueConstant (r : Eisenstein) (hr : primary r) [Fintype (Residues r)] : ℂ :=
  ∑ u : Residues r,cubicSymbol r (residueRepresentative r u)*
    cubicThetaProjectedConstant (cubicThetaResidueCuspMatrix r hr (residueRepresentative r u))
      (cubicThetaResidueCuspPrimary r hr (residueRepresentative r u))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProjectedRadial
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero angular mode of the actual primary projection, with its
constant-to-Fourier ratio retained in the pole coefficient. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaSelectedRadialCompleted (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (s : ℂ) : ℂ :=
  mellin (thetaUpper (cubicThetaSelectedRadialAxis g)) s+
    mellin (thetaUpper (cubicThetaProjectedRadialAxis g hc)) (-s)+
      cubicThetaProjectedRadialConstant g hc/(s-2/3)

def cubicThetaProjectedRadialCompleted (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (s : ℂ) : ℂ :=
  mellin (thetaUpper (cubicThetaProjectedRadialAxis g hc)) s+
    mellin (thetaUpper (cubicThetaSelectedRadialAxis g)) (-s)-
      cubicThetaProjectedRadialConstant g hc/(s+2/3)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialDirichlet
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual radial Dirichlet continuation and its functional equation.
The selected pole coefficient is computed from the actual cusp constant. -/
noncomputable section
open Filter
open scoped MatrixGroups Topology
namespace CubicFirstMoment

def cubicThetaSelectedRadialDirichlet (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (s : ℂ) : ℂ :=
  cubicThetaAngularUncompletion (g 1 0) 0 s*cubicThetaSelectedRadialCompleted g hc (2*s-1)

def cubicThetaProjectedRadialDirichlet (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (s : ℂ) : ℂ :=
  cubicThetaAngularUncompletion (g 1 0) 0 s*cubicThetaProjectedRadialCompleted g hc (2*s-1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialRegularization
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit removal of the actual radial pole. The residue is retained
as the computed cusp constant; no normalization of that constant is assumed. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaSelectedRadialHolomorphicPart (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (s : ℂ) : ℂ :=
  cubicThetaAngularUncompletion (g 1 0) 0 s*cubicThetaSelectedRadialTail g hc s+
    (cubicThetaProjectedRadialConstant g hc/2)*
      dslope (cubicThetaAngularUncompletion (g 1 0) 0) (5/6) s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialHeight
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact norm twists and finite dual-tail reduction for the actual radial
remainder. Its main term is the computed one, not an assumed normalization. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def cubicThetaRadialHeightRemainder (r : Eisenstein) (W : ℝ→ℂ) (X t : ℝ) : ℂ :=
  metaplecticHeightCompleted r 0 W X t-mellinPhase t X*
    cubicThetaActualCompletedRadialMain r (fun x => W x*mellinPhase t x) X

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarRankinRadial
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact radial integral of the positive scalar Rankin seed. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaRankinRadialEnergy (σ v : ℝ) : ℂ :=
  ((v^(2*σ-1):ℝ):ℂ)*(((cubicThetaConstant*v^(2/3:ℝ))^2:ℝ)+
    ‖cubicThetaArithmeticBaseScalar‖^2*cubicThetaArithmeticFourierEnergy v)

end CubicFirstMoment

end

end OAI
end


