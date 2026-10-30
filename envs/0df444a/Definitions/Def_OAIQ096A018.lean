-- Prove2me | Definitions.Def_OAIQ096A018
-- name    : OAIQ096A018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T03:49:50.58205+00:00
-- url     : https://prove2.me/theorems/b32ae0f6-a1f6-4c9a-aeb6-56909cfedb28
-- title:
--   Definitions bundle OAIQ096A018 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 197 declarations of OpenAI's Lean: 29 definitions, 2 instances and 166 theorems. The definitions and types are `OAI.CubicFirstMoment.cubicThetaBaseCover`, `OAI.CubicFirstMoment.cubicThetaCubeCoordinates`, `OAI.CubicFirstMoment.cubicThetaDoubleRootCover`, `OAI.CubicFirstMoment.cubicThetaFirstRootCover`, `OAI.CubicFirstMoment.cubicThetaHorizontalCover`, `OAI.CubicFirstMoment.cubicThetaHorizontalFourierCoefficient`, `OAI.CubicFirstMoment.cubicThetaHorizontalScaledCell`, `OAI.CubicFirstMoment.cubicThetaLongWindowTest`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeNormalizerPermutation`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeNormalizerStep`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeOpposite`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeOppositeMatrix`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootWeylConjugate`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootWeylElement`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootWeylSection`, `OAI.CubicFirstMoment.cubicThetaPrimeDoubleRootDomain`, `OAI.CubicFirstMoment.cubicThetaPrimeDoubleRootWeylSection`, `OAI.CubicFirstMoment.cubicThetaPrimeRootCoverWeylHomeomorph`, `OAI.CubicFirstMoment.cubicThetaPrimeRootFiniteResidue`, `OAI.CubicFirstMoment.cubicThetaPrimeRootFiniteWeyl`, `OAI.CubicFirstMoment.cubicThetaPrimeRootResidueL2`, `OAI.CubicFirstMoment.cubicThetaPrimeRootWeylL2`, `OAI.CubicFirstMoment.cubicThetaPrimeRootWeylSection`, `OAI.CubicFirstMoment.cubicThetaRadialProfileL2`, `OAI.CubicFirstMoment.cubicThetaRadialProfileTest`, `OAI.CubicFirstMoment.cubicThetaSectionFourier`, `OAI.CubicFirstMoment.cubicThetaSectionFourierFunction`, `OAI.CubicFirstMoment.cubicThetaSectionMean`, `OAI.CubicFirstMoment.cubicThetaSmoothWeakDefect`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `CubicMoment_Estimates_IdealDirichletInverse`, `CubicMoment_Estimates_IdealMellinSeries`, `CubicMoment_Estimates_IdealThetaMellin`, `CubicMoment_Estimates_PrincipalZetaPole`, `CubicMoment_Theta_CubicThetaConstantDirichlet`, `CubicMoment_Theta_CubicThetaConstantSupport`, `CubicMoment_Theta_CubicThetaCubeCoordinates`, `CubicMoment_Theta_CubicThetaCubeRowWeight`, `CubicMoment_Theta_CubicThetaCuspStripFubini`, `CubicMoment_Theta_CubicThetaCuspStripMeasure`, `CubicMoment_Theta_CubicThetaDensityLocal`, `CubicMoment_Theta_CubicThetaFiniteCover`, `CubicMoment_Theta_CubicThetaFiniteCoverIntegral`, `CubicMoment_Theta_CubicThetaFiniteCuspRestriction`, `CubicMoment_Theta_CubicThetaFrequencyHolomorphic`, `CubicMoment_Theta_CubicThetaHeightBandCore`, `CubicMoment_Theta_CubicThetaHighWindowPairing`, `CubicMoment_Theta_CubicThetaHorizontalAffine`, `CubicMoment_Theta_CubicThetaHorizontalCoefficient`, `CubicMoment_Theta_CubicThetaHorizontalCover`, `CubicMoment_Theta_CubicThetaHorizontalDomain`, `CubicMoment_Theta_CubicThetaHorizontalFourierAlgebra`, `CubicMoment_Theta_CubicThetaHorizontalFourierIntegrability`, `CubicMoment_Theta_CubicThetaHorizontalFourierTranslation`, `CubicMoment_Theta_CubicThetaHorizontalLattice`, `CubicMoment_Theta_CubicThetaHorizontalPeriodization`, `CubicMoment_Theta_CubicThetaHorizontalSection`, `CubicMoment_Theta_CubicThetaLongWindowKernel`, `CubicMoment_Theta_CubicThetaPeriodMeasure`, `CubicMoment_Theta_CubicThetaPointC1Hecke`, `CubicMoment_Theta_CubicThetaPointC1Inversion`, `CubicMoment_Theta_CubicThetaPrimeAtkinConjugation`, `CubicMoment_Theta_CubicThetaPrimeCubeBranchFourier`, `CubicMoment_Theta_CubicThetaPrimeCubeComplexIntegration`, `CubicMoment_Theta_CubicThetaPrimeCubeFirstPeriodMean`, `CubicMoment_Theta_CubicThetaPrimeCubeFourierOperator`, `CubicMoment_Theta_CubicThetaPrimeCubeHeckeFormula`, `CubicMoment_Theta_CubicThetaPrimeCubeHeckePairing`, `CubicMoment_Theta_CubicThetaPrimeCubeHorizontalContinuity`, `CubicMoment_Theta_CubicThetaPrimeCubeLowerValue`, `CubicMoment_Theta_CubicThetaPrimeCubeNormalizerCosets`, `CubicMoment_Theta_CubicThetaPrimeCubeOppositeBranch`, `CubicMoment_Theta_CubicThetaPrimeCubeOppositeConjugation`, `CubicMoment_Theta_CubicThetaPrimeCubeReciprocalGeometry`, `CubicMoment_Theta_CubicThetaPrimeCubeRootBruhat`, `CubicMoment_Theta_CubicThetaPrimeCubeRootBruhatL2`, `CubicMoment_Theta_CubicThetaPrimeCubeRootBruhatPhase`, `CubicMoment_Theta_CubicThetaPrimeCubeRootFirstIntegral`, `CubicMoment_Theta_CubicThetaPrimeCubeRootObservationProjection`, `CubicMoment_Theta_CubicThetaPrimeCubeRootResidueOverlap`, `CubicMoment_Theta_CubicThetaPrimeCubeRootSecondIntegral`, `CubicMoment_Theta_CubicThetaPrimeCubeRootStripBound`, `CubicMoment_Theta_CubicThetaPrimeCubeRootTraceNormalized`, `CubicMoment_Theta_CubicThetaPrimeCubeRootWeight`, `CubicMoment_Theta_CubicThetaPrimeCubeRootWeyl`, `CubicMoment_Theta_CubicThetaPrimeCubeRootWeylGlobal`, `CubicMoment_Theta_CubicThetaPrimeCubeRootWeylSections`, `CubicMoment_Theta_CubicThetaPrimeCubeSelfAdjointSection`, `CubicMoment_Theta_CubicThetaPrimeCubeTraceExpansion`, `CubicMoment_Theta_CubicThetaPrimeCubeTracePairing`, `CubicMoment_Theta_CubicThetaPrimeCubeValuationSum`, `CubicMoment_Theta_CubicThetaPrimeDoubleRootBruhat`, `CubicMoment_Theta_CubicThetaPrimeDoubleRootDomain`, `CubicMoment_Theta_CubicThetaPrimeDoubleRootGlobal`, `CubicMoment_Theta_CubicThetaPrimeDoubleRootOrthogonal`, `CubicMoment_Theta_CubicThetaPrimeDoubleRootPairing`, `CubicMoment_Theta_CubicThetaPrimeDoubleRootTranslationIntegral`, `CubicMoment_Theta_CubicThetaPrimeDoubleRootWeyl`, `CubicMoment_Theta_CubicThetaPrimeDoubleRootWeylSections`, `CubicMoment_Theta_CubicThetaPrimeRootAutomorphicL2`, `CubicMoment_Theta_CubicThetaPrimeRootBruhat`, `CubicMoment_Theta_CubicThetaPrimeRootBruhatOperators`, `CubicMoment_Theta_CubicThetaPrimeRootBruhatResidues`, `CubicMoment_Theta_CubicThetaPrimeRootCoverDegree`, `CubicMoment_Theta_CubicThetaPrimeRootCoverDomain`, `CubicMoment_Theta_CubicThetaPrimeRootCoverMeasure`, `CubicMoment_Theta_CubicThetaPrimeRootCoverTransport`, `CubicMoment_Theta_CubicThetaPrimeRootHorizontal`, `CubicMoment_Theta_CubicThetaPrimeRootIwahoriDomain`, `CubicMoment_Theta_CubicThetaPrimeRootL2`, `CubicMoment_Theta_CubicThetaPrimeRootRestrictionBound`, `CubicMoment_Theta_CubicThetaPrimeRootSectionNorm`, `CubicMoment_Theta_CubicThetaPrimeRootSquareOrthogonal`, `CubicMoment_Theta_CubicThetaPrimeRootTranslationL2`, `CubicMoment_Theta_CubicThetaPrimeRootWeyl`, `CubicMoment_Theta_CubicThetaPrimeRootWeylCover`, `CubicMoment_Theta_CubicThetaPrimeRootWeylFixed`, `CubicMoment_Theta_CubicThetaPrimeRootWeylInvolution`, `CubicMoment_Theta_CubicThetaPrimeRootWeylMeasure`, `CubicMoment_Theta_CubicThetaPrimeRootWeylSections`, `CubicMoment_Theta_CubicThetaRadialProfileEquation`, `CubicMoment_Theta_CubicThetaRadialProfilePairing`, `CubicMoment_Theta_CubicThetaRadialProfileSeries`, `CubicMoment_Theta_CubicThetaRadialProfileSmooth`, `CubicMoment_Theta_CubicThetaRamifiedIdeal`, `CubicMoment_Theta_CubicThetaResidueKernelPairing`, `CubicMoment_Theta_CubicThetaSectionFourierPairing`, `CubicMoment_Theta_CubicThetaSectionMean`, `CubicMoment_Theta_CubicThetaSectionMeanPairing`, `CubicMoment_Theta_CubicThetaSmoothLocalWeak`, `CubicMoment_Theta_CubicThetaSmoothWeakDefect`, `CubicMoment_Theta_CubicThetaTotientConvolution`, `CubicMoment_Theta_CubicThetaTotientEuler`, `CubicMoment_Theta_CubicThetaTotientSeries`.
--
--   **Imports.** It imports the published bundle `Def_PattersonFirstMoment`; the bundles `OAIQ096A011`, `OAIQ096A012`, `OAIQ096A013` and `OAIQ096A014` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ096A022` and `OAIQ096A023`; the proofs of `OAI.CubicFirstMoment.full_smooth_angular_twisted_primitive_cubic_bound` and `OAI.CubicFirstMoment.full_smooth_twisted_primitive_cubic_bound`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A011
import Definitions.Def_OAIQ096A012
import Definitions.Def_OAIQ096A013
import Definitions.Def_OAIQ096A014

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMellinSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute convergence and Mellin inversion for the complete ideal
series. Prime-exponent vectors include all nonzero ideals, including
the ramified prime; no Euler factor is silently removed. -/

noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

instance idealExponentCountable : Countable EisensteinIdealExponent := by
  have : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
  exact idealExponentGenerator_injective.countable

theorem summable_ideal_norm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun ν : EisensteinIdealExponent => idealExponentNorm ν^(-σ)) := by
  have h := (summable_eisenstein_norm_rpow hσ).comp_injective idealExponentGenerator_injective
  simpa only [Function.comp_def,idealExponentNorm,normNat_cast] using h

theorem summable_ideal_character_weight {σ : ℝ} (hσ : 1 < σ)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) :
    Summable (fun ν => ‖χ ν‖*idealExponentNorm ν^(-σ)) := by
  apply (summable_ideal_norm_rpow hσ).of_norm_bounded
  intro ν
  have hn := idealExponentNorm_pos ν
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_left (by positivity) (hχ ν)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealDirichletInverse
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An absolutely convergent Möbius inverse of the complete ideal Hecke
series. In particular the actual series has no zeros to the right of one. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealDirichlet_norm_summable (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun ν => ‖χ ν*(idealExponentNorm ν:ℂ)^(-s)‖) := by
  simpa only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (idealExponentNorm_pos _),
    Complex.neg_re] using summable_ideal_character_weight hs χ hχ

/-- The literal complete ideal series has its absolutely convergent
Möbius-twisted inverse on `Re(s)>1`. -/
theorem idealDirichlet_moebius_mul (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {s : ℂ} (hs : 1 < s.re) :
    normDirichletSeries (fun ν => ((MvPowerSeries.coeff ν idealMoebiusSeries:ℝ):ℂ)*χ ν)
      idealExponentNorm s * normDirichletSeries χ idealExponentNorm s = 1 := by
  have h0 : χ 0*(idealExponentNorm 0:ℂ)^(-s)=1 := by
    simp [hχ0,idealExponentNorm,idealExponentGenerator]
  have h := idealMoebius_tsum_mul (fun ν => χ ν*(idealExponentNorm ν:ℂ)^(-s))
    (idealDirichlet_norm_summable χ hχ hs) h0 (idealDirichlet_weight_add χ hχadd s)
  simpa only [normDirichletSeries,mul_assoc] using h

theorem idealDirichlet_ne_zero (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {s : ℂ} (hs : 1 < s.re) :
    normDirichletSeries χ idealExponentNorm s ≠ 0 := by
  intro hzero
  have h := idealDirichlet_moebius_mul χ hχ hχ0 hχadd hs
  rw [hzero,mul_zero] at h
  exact zero_ne_one h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealThetaMellin
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Mellin transform of the complete ideal theta series. -/
noncomputable section
namespace CubicFirstMoment

lemma idealTheta_one_mellin (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    mellin (idealTheta 1 χ) s =
      Complex.Gamma s * normDirichletSeries χ idealExponentNorm s := by
  have hsum : Summable (fun ν => ‖χ ν‖ / idealExponentNorm ν^s.re) := by
    simpa only [Real.rpow_neg (idealExponentNorm_pos _).le,div_eq_mul_inv] using
      summable_ideal_character_weight hs χ hχ
  have h := hasSum_mellin (fun ν => Or.inr (idealExponentNorm_pos ν))
    (show 0 < s.re by linarith) (F := idealTheta 1 χ) (fun t ht => by
      simpa only [idealTheta,div_one] using (idealTheta_summable zero_lt_one ht χ hχ).hasSum) hsum
  rw [← h.tsum_eq]
  simp only [normDirichletSeries,Complex.cpow_neg,div_eq_mul_inv,mul_assoc]
  exact tsum_mul_left

lemma idealTheta_mellin {A : ℝ} (hA : 0 < A)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    mellin (idealTheta A χ) s =
      (A:ℂ)^s * Complex.Gamma s * normDirichletSeries χ idealExponentNorm s := by
  rw [idealTheta_scale A χ,mellin_comp_mul_right _ _ (one_div_pos.mpr hA),
    idealTheta_one_mellin χ hχ hs]
  have hp : ((1/A:ℝ):ℂ)^(-s) = (A:ℂ)^s := by
    simpa using mellin_scale_cpow zero_lt_one hA s
  rw [hp,smul_eq_mul,mul_assoc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrincipalZetaPole
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An analytic, nonzero numerator for the simple pole at one of the
actual principal ideal zeta function. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

lemma principalZetaPrefactor_differentiable : Differentiable ℂ principalZetaPrefactor := by
  let _ : NeZero (residueHeckeScale 1:ℂ) := ⟨Complex.ofReal_ne_zero.mpr
    (residueHeckeScale_pos (q := 1) one_ne_zero).ne'⟩
  exact ((differentiable_const_cpow_of_neZero (residueHeckeScale 1:ℂ)).comp
    differentiable_neg).mul Complex.differentiable_one_div_Gamma

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaConstantSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact cube support of the constant coefficient of the cubic
Eisenstein series, including the ramified factor. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaEisenstein_constant_noncube {c : Eisenstein}
    (hc : (3:Eisenstein) ∣ c) (hc0 : c ≠ 0) (hcb : ¬∃ j : Eisenstein, j^3=c) :
    cubicThetaEisensteinGaussCoefficient c 0 = 0 := by
  obtain ⟨u,hu,hcu,hchi⟩ :=
    (cubicNumeratorChar_ne_one_iff cubicSupplementaryPeriodicity_proved c hc0).mp
      (cubicNumeratorChar_noncube cubicSupplementaryPeriodicity_proved hc0 hcb)
  exact cubicThetaEisenstein_constant_vanish hc hc0 hu hcu.of_mul_left_right hchi

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCubeCoordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every nonzero cubic Eisenstein integer has exactly one ideal exponent
vector and one of two signs. This removes the cube-root multiplicity. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaSignedCube_exponent (ε : Bool) (ν : EisensteinIdealExponent) :
    idealExponentOf (cubicThetaSignedCube ε ν)=3•ν := by
  cases ε <;> simp only [cubicThetaSignedCube,Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
  · rw [idealExponentOf_pow (idealExponentGenerator_ne_zero ν),idealExponentOf_generator]
  · rw [cubicTheta_idealExponentOf_neg (pow_ne_zero _ (idealExponentGenerator_ne_zero ν)),
      idealExponentOf_pow (idealExponentGenerator_ne_zero ν),idealExponentOf_generator]

lemma cubicThetaCubeCoordinates_bijective : Function.Bijective cubicThetaCubeCoordinatesMap := by
  constructor
  · rintro ⟨ε,ν⟩ ⟨δ,κ⟩ he
    have hv := congrArg (fun x : CubicThetaNonzeroCube => idealExponentOf x.val) he
    change idealExponentOf (cubicThetaSignedCube ε ν)=
      idealExponentOf (cubicThetaSignedCube δ κ) at hv
    rw [cubicThetaSignedCube_exponent,cubicThetaSignedCube_exponent] at hv
    have hν : ν=κ := by
      ext p
      have hp := congrArg (fun f : EisensteinIdealExponent => f p) hv
      simp only [Finsupp.smul_apply,smul_eq_mul] at hp
      omega
    subst κ
    have he' := congrArg Subtype.val he
    change cubicThetaSignedCube ε ν=cubicThetaSignedCube δ ν at he'
    have hn := pow_ne_zero 3 (idealExponentGenerator_ne_zero ν)
    have htwo : (2:Eisenstein)≠0 := by norm_num
    have hcontra : ¬ -(idealExponentGenerator ν)^3=(idealExponentGenerator ν)^3 := by
      intro h
      have hz : (2:Eisenstein)*(idealExponentGenerator ν)^3=0 := by linear_combination -h
      exact (mul_ne_zero htwo hn) hz
    cases ε <;> cases δ
    · rfl
    · exact False.elim (hcontra (by simpa only [cubicThetaSignedCube,ite_true, if_true,ite_false, if_false,
        Bool.false_eq_true] using he'.symm))
    · exact False.elim (hcontra (by simpa only [cubicThetaSignedCube,ite_true, if_true,ite_false, if_false,
        Bool.false_eq_true] using he'))
    · rfl
  · intro c
    obtain ⟨j,hj⟩ := c.property.2
    have hj0 : j≠0 := by intro h; subst j; simp at hj; exact c.property.1 hj.symm
    let ν := idealExponentOf j
    obtain ⟨u,hu⟩ := idealExponentOf_associated hj0
    rcases eisenstein_unit_cube_sign u with hs | hs
    · refine ⟨(false,ν),Subtype.ext ?_⟩
      change (idealExponentGenerator ν)^3=c.val
      rw [←hj,←hu,mul_pow,hs,mul_one]
    · refine ⟨(true,ν),Subtype.ext ?_⟩
      change -(idealExponentGenerator ν)^3=c.val
      rw [←hj,←hu,mul_pow,hs,mul_neg_one]

def cubicThetaCubeCoordinates : (Bool × EisensteinIdealExponent) ≃ CubicThetaNonzeroCube :=
  Equiv.ofBijective _ cubicThetaCubeCoordinates_bijective

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTotientEuler
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Euler factors for the actual residue-unit counts in the cubic
Eisenstein constant term. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaIdealTotient_add {ν κ : EisensteinIdealExponent}
    (h : ∀ p, ν p=0 ∨ κ p=0) :
    cubicThetaIdealTotient (ν+κ)=cubicThetaIdealTotient ν*cubicThetaIdealTotient κ := by
  unfold cubicThetaIdealTotient
  rw [idealExponentGenerator_add]
  apply cubicTheta_coprime_units_card
  rw [isCoprime_iff_idealExponent_disjoint (idealExponentGenerator_ne_zero ν)
    (idealExponentGenerator_ne_zero κ),idealExponentOf_generator,idealExponentOf_generator]
  exact h

lemma cubicThetaIdealTotient_euler (ν : EisensteinIdealExponent) :
    (cubicThetaIdealTotient ν:ℝ)=idealExponentNorm ν*
      ∏ p ∈ ν.support, (1-1/(normNat (idealPrimeRepresentative p):ℝ)) := by
  induction ν using Finsupp.induction with
  | zero => simp [cubicThetaIdealTotient_zero,idealExponentNorm,idealExponentGenerator]
  | @single_add p n ν hp hn ih =>
    have hν : ν p=0 := Finsupp.notMem_support_iff.mp hp
    have hs : (Finsupp.single p n+ν).support=insert p ν.support := by
      ext q
      by_cases hqp : q=p
      · subst q
        simp [Finsupp.mem_support_iff,hν,hn]
      · simp [Finsupp.mem_support_iff,hqp]
    have hcop : ∀ q, (Finsupp.single p n) q=0 ∨ ν q=0 := by
      intro q
      by_cases hqp : q=p
      · subst q; exact Or.inr hν
      · left; simp [hqp]
    rw [cubicThetaIdealTotient_add hcop,Nat.cast_mul,cubicThetaIdealTotient_single_real p hn,
      ih,idealExponentNorm_add,hs,Finset.prod_insert hp]
    ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTotientConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized finite-ring totient as the actual ideal Möbius
convolution. This identifies its scattering Dirichlet series. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaTotient_moebius (ν : EisensteinIdealExponent) :
    (cubicThetaIdealTotient ν:ℝ)/idealExponentNorm ν=
      MvPowerSeries.coeff ν (idealZeta*cubicThetaNormInverse idealMoebiusSeries) := by
  have hf : MvPowerSeries.coeff ν (idealZeta*cubicThetaNormInverse idealMoebiusSeries)=
      MvPowerSeries.coeff ν (idealZeta*cubicThetaNormInverse (finiteIdealMoebius ν.support)) := by
    rw [MvPowerSeries.coeff_mul,MvPowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [cubicThetaNormInverse_coeff,cubicThetaNormInverse_coeff]
    congr 2
    apply coeff_idealMoebiusSeries_eq_finite
    have hle : p.2≤ν := by
      rw [←Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
      exact le_add_of_nonneg_left zero_le
    intro q hq
    apply Finsupp.mem_support_iff.mpr
    intro hzero
    have he := hle q
    rw [hzero] at he
    exact (Finsupp.mem_support_iff.mp hq) (Nat.eq_zero_of_le_zero he)
  rw [hf,totient_finite_product,cubicThetaIdealTotient_euler]
  have hN := (idealExponentNorm_pos ν).ne'
  rw [mul_div_cancel_left₀ _ hN]
  apply Finset.prod_congr rfl
  intro p hp
  simp [Finsupp.mem_support_iff.mp hp,one_div]

lemma cubicThetaTotient_divisor_sum (ν : EisensteinIdealExponent) :
    (cubicThetaIdealTotient ν:ℝ)/idealExponentNorm ν=
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
        MvPowerSeries.coeff p.1 idealMoebiusSeries/idealExponentNorm p.1 := by
  rw [cubicThetaTotient_moebius,mul_comm,MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [cubicThetaNormInverse_coeff]
  simp [idealZeta,MvPowerSeries.coeff_apply]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTotientSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact quotient of principal ideal zeta functions supplied by the
normalized residue-unit counts. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaIdealDensity_coeff (ν : EisensteinIdealExponent) :
    cubicThetaIdealDensity ν=
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
        ((MvPowerSeries.coeff p.1 idealMoebiusSeries:ℝ):ℂ)/(idealExponentNorm p.1:ℂ) := by
  have he := congrArg Complex.ofReal (cubicThetaTotient_divisor_sum ν)
  simpa only [cubicThetaIdealDensity,Complex.ofReal_div,Complex.ofReal_natCast,
    Complex.ofReal_sum] using he

lemma cubicThetaTotientSeries_product {s : ℂ} (hs : 1 < s.re) :
    normDirichletSeries cubicThetaIdealDensity idealExponentNorm s=
      normDirichletSeries (fun ν => ((MvPowerSeries.coeff ν idealMoebiusSeries:ℝ):ℂ))
        idealExponentNorm (s+1)*normDirichletSeries (fun _ => 1) idealExponentNorm s := by
  have hsp : 1<(s+1).re := by simp only [Complex.add_re,Complex.one_re]; linarith
  have hmu (ν : EisensteinIdealExponent) : ‖((MvPowerSeries.coeff ν idealMoebiusSeries:ℝ):ℂ)‖≤1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using idealMoebiusSeries_abs_le_one ν
  let f := fun ν : EisensteinIdealExponent =>
    ((MvPowerSeries.coeff ν idealMoebiusSeries:ℝ):ℂ)*(idealExponentNorm ν:ℂ)^(-(s+1))
  let g := fun ν : EisensteinIdealExponent => (1:ℂ)*(idealExponentNorm ν:ℂ)^(-s)
  have hf := idealDirichlet_norm_summable _ hmu hsp
  have hg := idealDirichlet_norm_summable (fun _ => (1:ℂ)) (by simp) hs
  change (∑' ν, cubicThetaIdealDensity ν*(idealExponentNorm ν:ℂ)^(-s))=
    (∑' ν, f ν)*(∑' ν, g ν)
  rw [ideal_cauchy_product f g hf hg]
  apply tsum_congr
  intro ν
  rw [cubicThetaIdealDensity_coeff,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  dsimp only [f,g]
  rw [cubicTheta_norm_cpow_shift]
  have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [←he,idealExponentNorm_add,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (idealExponentNorm_pos p.1).le (idealExponentNorm_pos p.2).le]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaDensityLocal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local prime factor of the actual normalized residue-unit density. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaIdealDensity_product (ν : EisensteinIdealExponent) :
    cubicThetaIdealDensity ν=
      ∏ p ∈ ν.support, (1-(normNat (idealPrimeRepresentative p):ℂ)⁻¹) := by
  have he : (cubicThetaIdealTotient ν:ℝ)/idealExponentNorm ν=
      ∏ p ∈ ν.support, (1-1/(normNat (idealPrimeRepresentative p):ℝ)) := by
    rw [cubicThetaIdealTotient_euler,mul_div_cancel_left₀ _ (idealExponentNorm_pos ν).ne']
  simpa only [cubicThetaIdealDensity,Complex.ofReal_div,Complex.ofReal_natCast,
    Complex.ofReal_prod,Complex.ofReal_sub,Complex.ofReal_one,one_div,
    Complex.ofReal_inv] using congrArg Complex.ofReal he

lemma cubicThetaIdealDensity_prime_step (p : EisensteinIdealPrime) (ν : EisensteinIdealExponent) :
    cubicThetaIdealDensity (Finsupp.single p 1+ν)=
      if ν p=0 then (1-(normNat (idealPrimeRepresentative p):ℂ)⁻¹)*cubicThetaIdealDensity ν
      else cubicThetaIdealDensity ν := by
  have hs : (Finsupp.single p 1+ν).support=insert p ν.support := by
    ext q
    by_cases hq : q=p
    · subst q
      simp [Finsupp.mem_support_iff]
    · simp [Finsupp.mem_support_iff,hq]
  rw [cubicThetaIdealDensity_product,hs]
  by_cases hp : ν p=0
  · rw [ite_eq_left hp,Finset.prod_insert (Finsupp.notMem_support_iff.mpr hp),
      cubicThetaIdealDensity_product]
  · rw [ite_eq_right hp,Finset.insert_eq_of_mem (Finsupp.mem_support_iff.mpr hp),
      cubicThetaIdealDensity_product]

lemma cubicThetaPrimeDensity_series_equation (p : EisensteinIdealPrime)
    {s : ℂ} (hs : 1 < s.re) :
    normDirichletSeries (cubicThetaPrimeDensity p) idealExponentNorm s =
      (normNat (idealPrimeRepresentative p):ℂ)^(-s)*
        ((1-(normNat (idealPrimeRepresentative p):ℂ)⁻¹)*
          normDirichletSeries cubicThetaIdealDensity idealExponentNorm s+
          (normNat (idealPrimeRepresentative p):ℂ)⁻¹*
            normDirichletSeries (cubicThetaPrimeDensity p) idealExponentNorm s) := by
  let δ : EisensteinIdealExponent := Finsupp.single p 1
  let f (ν : EisensteinIdealExponent) := cubicThetaIdealDensity ν*(idealExponentNorm ν:ℂ)^(-s)
  let g (ν : EisensteinIdealExponent) := cubicThetaPrimeDensity p ν*(idealExponentNorm ν:ℂ)^(-s)
  have hf : Summable f := (idealDirichlet_norm_summable _ cubicThetaIdealDensity_norm hs).of_norm
  have hg : Summable g := (idealDirichlet_norm_summable _ (cubicThetaPrimeDensity_norm p) hs).of_norm
  have hi : Function.Injective (fun ν : EisensteinIdealExponent => δ+ν) :=
    fun _ _ h => add_left_cancel h
  have hsup : Function.support g ⊆ Set.range (fun ν => δ+ν) := by
    intro ν hν
    have hp : 0<ν p := by
      by_contra h
      exact hν (by simp [g,cubicThetaPrimeDensity,h])
    exact ⟨ν-δ,add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.succ_le_iff.mpr hp))⟩
  have hpoint (ν : EisensteinIdealExponent) :
      g (δ+ν)=(normNat (idealPrimeRepresentative p):ℂ)^(-s)*
        ((1-(normNat (idealPrimeRepresentative p):ℂ)⁻¹)*f ν+
          (normNat (idealPrimeRepresentative p):ℂ)⁻¹*g ν) := by
    have hpos : 0<(δ+ν) p := by simp [δ]
    dsimp only [g,f]
    rw [cubicThetaPrimeDensity,ite_eq_left hpos,idealExponentNorm_add,
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (idealExponentNorm_pos δ).le
        (idealExponentNorm_pos ν).le]
    have hδ : idealExponentNorm δ=(normNat (idealPrimeRepresentative p):ℝ) := by
      simp [δ,idealExponentNorm_single]
    rw [hδ,cubicThetaIdealDensity_prime_step]
    by_cases hp : ν p=0
    · simp only [hp,ite_true, if_true,cubicThetaPrimeDensity,lt_self_iff_false,ite_false, if_false]
      push_cast
      ring
    · rw [ite_eq_right hp,cubicThetaPrimeDensity,ite_eq_left (Nat.pos_of_ne_zero hp)]
      push_cast
      ring
  change (∑' ν, g ν)=_
  rw [←hi.tsum_eq hsup]
  simp_rw [hpoint]
  rw [tsum_mul_left, (hf.mul_left _).tsum_add (hg.mul_left _),tsum_mul_left,tsum_mul_left]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedIdeal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The single ramified ideal in the cube part of the constant term. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaRamifiedPrime_dvd_iff (ν : EisensteinIdealExponent) :
    lambdaE∣idealExponentGenerator ν ↔ 0<ν cubicThetaRamifiedPrime := by
  rw [←cubicThetaRamifiedPrime_associated.dvd_iff_dvd_left,
    idealPrime_dvd_iff (idealExponentGenerator_ne_zero ν),idealExponentOf_generator]

lemma cubicThetaSignedCube_ramified (ε : Bool) (ν : EisensteinIdealExponent) :
    (3:Eisenstein)∣cubicThetaSignedCube ε ν ↔ 0<ν cubicThetaRamifiedPrime := by
  cases ε <;> simp only [cubicThetaSignedCube,Bool.false_eq_true,ite_true, if_true,ite_false, if_false]
  · rw [cubicTheta_cube_row_three_iff,cubicThetaRamifiedPrime_dvd_iff]
  · rw [dvd_neg,cubicTheta_cube_row_three_iff,cubicThetaRamifiedPrime_dvd_iff]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCubeRowWeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The value of either signed cube row in canonical ideal coordinates. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaSignedCube_constant (ε : Bool) (ν : EisensteinIdealExponent)
    (hν : 0<ν cubicThetaRamifiedPrime) :
    cubicThetaEisensteinGaussCoefficient (cubicThetaSignedCube ε ν) 0=
      (3/2:ℂ)*(idealExponentNorm ν:ℂ)^2*(cubicThetaIdealTotient ν:ℂ) := by
  have h3 : (3:Eisenstein)∣(idealExponentGenerator ν)^3 :=
    cubicTheta_cube_row_three_iff.mpr ((cubicThetaRamifiedPrime_dvd_iff ν).mpr hν)
  cases ε
  · simpa only [cubicThetaSignedCube,Bool.false_eq_true,ite_false, if_false,
      idealExponentNorm,Complex.ofReal_natCast,cubicThetaIdealTotient] using
      cubicThetaEisenstein_constant_cube_totient (idealExponentGenerator_ne_zero ν) h3
  · have hneg : (-idealExponentGenerator ν)^3= -(idealExponentGenerator ν)^3 := by ring
    have he := cubicThetaEisenstein_constant_cube_totient
      (neg_ne_zero.mpr (idealExponentGenerator_ne_zero ν))
      (show (3:Eisenstein)∣(-idealExponentGenerator ν)^3 by rw [hneg]; exact dvd_neg.mpr h3)
    rw [hneg,cubicTheta_normNat_neg,cubicTheta_residue_units_associated
      (Associated.refl (idealExponentGenerator ν)).neg_left] at he
    simpa only [cubicThetaSignedCube,ite_true, if_true,idealExponentNorm,
      Complex.ofReal_natCast,cubicThetaIdealTotient] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaConstantDirichlet
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reindexing of the Eisenstein constant coefficient Dirichlet
series by the two signed cubes of each nonzero ideal. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaConstantTermWeight_support (s : ℂ) :
    Function.support (cubicThetaConstantTermWeight s) ⊆
      {c : Eisenstein | c≠0 ∧ ∃ j : Eisenstein, j^3=c} := by
  intro c hc
  by_cases h : (3:Eisenstein)∣c ∧ c≠0
  · refine ⟨h.2,?_⟩
    by_contra hcb
    exact hc (by simp [cubicThetaConstantTermWeight,h,
      cubicThetaEisenstein_constant_noncube h.1 h.2 hcb])
  · exact False.elim (hc (by simp [cubicThetaConstantTermWeight,h]))

lemma cubicThetaConstantTermWeight_cube (s : ℂ) (ε : Bool) (ν : EisensteinIdealExponent) :
    cubicThetaConstantTermWeight s (cubicThetaSignedCube ε ν)=
      (3/2:ℂ)*cubicThetaPrimeDensity cubicThetaRamifiedPrime ν*
        (idealExponentNorm ν:ℂ)^(-(3*s-3)) := by
  by_cases hν : 0<ν cubicThetaRamifiedPrime
  · have h3 := (cubicThetaSignedCube_ramified ε ν).mpr hν
    rw [cubicThetaConstantTermWeight,ite_eq_left ⟨h3,cubicThetaSignedCube_ne_zero ε ν⟩,
      cubicThetaSignedCube_constant ε ν hν,cubicThetaSignedCube_norm,cubicThetaPrimeDensity,
      ite_eq_left hν,cubicThetaIdealDensity,Complex.ofReal_pow]
    have hN := Complex.ofReal_ne_zero.mpr (idealExponentNorm_pos ν).ne'
    have hp : ((idealExponentNorm ν:ℂ)^3)^(-s)=
        (idealExponentNorm ν:ℂ)^(-3*s) := by
      rw [←Complex.cpow_nat_mul' (n:=3)
        (by rw [Complex.arg_ofReal_of_nonneg (idealExponentNorm_pos ν).le]; nlinarith [Real.pi_pos])
        (by rw [Complex.arg_ofReal_of_nonneg (idealExponentNorm_pos ν).le]; nlinarith [Real.pi_pos])]
      congr 1
      ring
    rw [hp,show -(3*s-3)=(3:ℂ)+(-3*s) by ring,Complex.cpow_add _ _ hN]
    rw [show (idealExponentNorm ν:ℂ)^(3:ℂ)=(idealExponentNorm ν:ℂ)^3 from
      Complex.cpow_natCast _ 3]
    field_simp
  · have h3 : ¬(3:Eisenstein)∣cubicThetaSignedCube ε ν :=
      fun h => hν ((cubicThetaSignedCube_ramified ε ν).mp h)
    simp [cubicThetaConstantTermWeight,h3,cubicThetaPrimeDensity,hν]

lemma cubicThetaConstantDirichlet_cube_sum (s : ℂ) :
    cubicThetaConstantDirichlet s=∑' x : Bool × EisensteinIdealExponent,
      cubicThetaConstantTermWeight s (cubicThetaSignedCube x.1 x.2) := by
  calc
    cubicThetaConstantDirichlet s=∑' c : CubicThetaNonzeroCube, cubicThetaConstantTermWeight s c.val :=
      (tsum_subtype_eq_of_support_subset (cubicThetaConstantTermWeight_support s)).symm
    _ = ∑' x : Bool × EisensteinIdealExponent,
        cubicThetaConstantTermWeight s (cubicThetaCubeCoordinates x).val :=
      (cubicThetaCubeCoordinates.tsum_eq _).symm
    _ = _ := rfl

theorem cubicThetaConstantDirichlet_eq_ramified {s : ℂ} (hs : 4/3 < s.re) :
    cubicThetaConstantDirichlet s=3*cubicThetaRamifiedDensitySeries (3*s-3) := by
  have ht : 1<(3*s-3).re := by
    simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
    linarith
  let g (ν : EisensteinIdealExponent) := cubicThetaPrimeDensity cubicThetaRamifiedPrime ν*
    (idealExponentNorm ν:ℂ)^(-(3*s-3))
  have hg : Summable (fun ν => ‖g ν‖) :=
    idealDirichlet_norm_summable _ (cubicThetaPrimeDensity_norm cubicThetaRamifiedPrime) ht
  calc
    cubicThetaConstantDirichlet s=∑' x : Bool × EisensteinIdealExponent,
        cubicThetaConstantTermWeight s (cubicThetaSignedCube x.1 x.2) :=
      cubicThetaConstantDirichlet_cube_sum s
    _ = ∑' x : Bool × EisensteinIdealExponent, (3/2:ℂ)*g x.2 := by
      apply tsum_congr
      intro x
      simpa only [g,mul_assoc] using cubicThetaConstantTermWeight_cube s x.1 x.2
    _ = 3*cubicThetaRamifiedDensitySeries (3*s-3) := cubicTheta_signed_sum g hg

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspStripMeasure
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact quotient integration on the half-open arithmetic cusp strip.
This identifies the cusp mass and energy with their global restrictions,
including the boundary convention of the horizontal period cell. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaInjective_integral_le {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) (hi : InjOn cubicThetaQuotientMap S)
    {f : CubicThetaQuotient → ℝ} (hf : Integrable f cubicThetaQuotientMeasure)
    (hn : ∀ q, 0≤f q) :
    (∫ p in S, f (cubicThetaQuotientMap p) ∂cubicThetaPointMeasure)≤
      ∫ q, f q ∂cubicThetaQuotientMeasure := by
  have hm : (cubicThetaPointMeasure.restrict S).map cubicThetaQuotientMap≤
      cubicThetaQuotientMeasure := by
    rw [cubicThetaInjective_map_restrict hS hi]
    exact Measure.restrict_le_self
  rw [← integral_map cubicThetaQuotientMap_open.continuous.measurable.aemeasurable
    (hf.aestronglyMeasurable.mono_measure hm)]
  exact integral_mono_measure hm (ae_of_all _ hn) hf

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspStripFubini
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fubini on the literal half-open cusp cell, with the v^-3 density. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaCuspStrip_fubini (f : ℂ × ℝ → ℂ)
    (hf : IntegrableOn (fun p => f (cubicThetaPointCoordinates p))
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure) :
    (∫ p in cubicThetaCuspStrip 2, f (cubicThetaPointCoordinates p) ∂cubicThetaPointMeasure)=
      ∫ v in Ioi (2:ℝ), ∫ z in cubicThetaHorizontalCell, f (z,v)/(v:ℂ)^3 := by
  have hi := (cubicThetaPointIntegrable_complex_density (cubicThetaCuspStrip_measurable 2) f).mp hf
  rw [cubicThetaPointIntegral_complex_density (cubicThetaCuspStrip_measurable 2),
    cubicThetaCuspStrip_coordinates (by norm_num : (0:ℝ)≤2)]
  rw [cubicThetaCuspStrip_coordinates (by norm_num : (0:ℝ)≤2)] at hi
  change Integrable (fun y : ℂ × ℝ => f y/(y.2:ℂ)^3)
    (((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict _) at hi
  rw [← Measure.prod_restrict] at hi
  change (∫ y : ℂ × ℝ, f y/(y.2:ℂ)^3 ∂
    ((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict
      (cubicThetaHorizontalCell ×ˢ Ioi (2:ℝ)))=_
  rw [← Measure.prod_restrict]
  exact integral_prod_symm _ hi

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteCover
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite-cover domains in the fixed arithmetic action.  This is
used to compare the three root levels without postulating equality of
integrals on different covers. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaBaseCover : CubicThetaArithmeticCover where
  group := ⊤
  domain := cubicThetaFundamentalDomain
  measurable := cubicThetaFundamentalDomain_measurable
  unique x := by
    obtain ⟨g,hg,hu⟩ := cubicThetaFundamentalDomain_unique x
    refine ⟨⟨g,Subgroup.mem_top g⟩,hg,?_⟩
    intro k hk
    exact Subtype.ext (hu k.val hk)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteCoverIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-index integral transport in the fixed arithmetic action,
including the nonintegrable case of the Bochner integral convention. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

variable (D : CubicThetaArithmeticCover) (K : Subgroup cubicThetaPrincipalGroup)
  (hle : K≤D.group) [K.FiniteIndex]

section Integral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma cubicThetaRelativeDomain_integral {f : CubicThetaPoint → E}
    (hi : ∀ (g : D.group) x, f (g • x)=f x) :
    (∫ x in cubicThetaRelativeDomain D K, f x ∂cubicThetaPointMeasure)=
      ((cubicThetaRelativeSubgroup D K).index:ℝ) •
        ∫ x in D.domain, f x ∂cubicThetaPointMeasure := by
  classical
  let : Fintype (cubicThetaRelativeTransversal D K) := Fintype.ofFinite _
  have hmeas (t : cubicThetaRelativeTransversal D K) :
      MeasurableSet ((fun x : CubicThetaPoint => t.val • x) '' D.domain) :=
    (measurableEmbedding_const_smul t.val).measurableSet_image' D.measurable
  by_cases hf : IntegrableOn f D.domain cubicThetaPointMeasure
  · have hint (t : cubicThetaRelativeTransversal D K) :
        IntegrableOn f ((fun x : CubicThetaPoint => t.val • x) '' D.domain)
          cubicThetaPointMeasure := by
      apply ((measurePreserving_smul t.val cubicThetaPointMeasure).integrableOn_image
        (measurableEmbedding_const_smul t.val)).mpr
      simpa only [Function.comp_def,hi] using hf
    change (∫ x in ⋃ t : cubicThetaRelativeTransversal D K,
      (fun y : CubicThetaPoint => t.val • y) '' D.domain, f x
        ∂cubicThetaPointMeasure)=_
    rw [integral_iUnion_fintype hmeas (cubicThetaRelativeDomain_disjoint D K) hint]
    have ht (t : cubicThetaRelativeTransversal D K) :
        (∫ x in (fun y : CubicThetaPoint => t.val • y) '' D.domain,
          f x ∂cubicThetaPointMeasure)=∫ x in D.domain, f x ∂cubicThetaPointMeasure := by
      rw [(measurePreserving_smul t.val cubicThetaPointMeasure).setIntegral_image_emb
        (measurableEmbedding_const_smul t.val) f D.domain]
      simp only [hi]
    simp only [ht,Finset.sum_const,Finset.card_univ]
    rw [←Nat.card_eq_fintype_card,(cubicThetaRelativeTransversal_complement D K).card_right,
      Nat.cast_smul_eq_nsmul ℝ]
  · have hnot : ¬IntegrableOn f (cubicThetaRelativeDomain D K) cubicThetaPointMeasure := by
      intro hrel
      obtain ⟨⟨h,t⟩,_⟩ := (cubicThetaRelativeTransversal_complement D K).existsUnique (1:D.group)
      have hsub : ((fun x : CubicThetaPoint => t.val • x) '' D.domain)⊆
          cubicThetaRelativeDomain D K := by
        exact subset_iUnion (fun u : cubicThetaRelativeTransversal D K =>
          (fun x : CubicThetaPoint => u.val • x) '' D.domain) t
      have hint := hrel.mono_set hsub
      have hint' := ((measurePreserving_smul t.val cubicThetaPointMeasure).integrableOn_image
        (measurableEmbedding_const_smul t.val)).mp hint
      apply hf
      simpa only [Function.comp_def,hi] using hint'
    rw [integral_undef hnot,integral_undef hf,smul_zero]

include hle in
theorem cubicThetaFiniteCover_integral (S : Set CubicThetaPoint)
    (hS : IsFundamentalDomain K S cubicThetaPointMeasure) {f : CubicThetaPoint → E}
    (hi : ∀ (g : D.group) x, f (g • x)=f x) :
    (∫ x in S, f x ∂cubicThetaPointMeasure)=
      ((cubicThetaRelativeSubgroup D K).index:ℝ) •
        ∫ x in D.domain, f x ∂cubicThetaPointMeasure := by
  have hk (g : K) (x : CubicThetaPoint) : f (g • x)=f x := hi ⟨g.val,hle g.property⟩ x
  rw [hS.setIntegral_eq ((cubicThetaRelativeCover D K hle).fundamental cubicThetaPointMeasure) hk]
  exact cubicThetaRelativeDomain_integral D K hi

end Integral
end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteCuspRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restriction of actual finite-energy sections to the injective
height-two cusp strip is bounded in L2 by the global value norm. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaFiniteCuspRestriction_norm_sq (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaFiniteCuspRestriction F‖^2=
      ∫ p in cubicThetaCuspStrip 2, ‖F.val.val p‖^2 ∂cubicThetaPointMeasure := by
  rw [cubicTheta_l2_norm_sq_measure]
  apply integral_congr_ae
  filter_upwards [(cubicThetaFiniteEnergy_strip_memLp F).coeFn_toLp] with p hp
  change ‖((cubicThetaFiniteEnergy_strip_memLp F).toLp _) p‖^2=_
  rw [hp]

lemma cubicThetaFiniteEnergyValue_norm_sq (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaFiniteEnergyValue F‖^2=
      ∫ q, cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure := by
  rw [cubicTheta_l2_norm_sq_measure]
  apply integral_congr_ae
  filter_upwards [F.property.2.1.coeFn_toLp] with q hq
  change ‖(F.property.2.1.toLp _) q‖^2=_
  rw [hq,cubicThetaSectionRepresentative_norm]

lemma cubicThetaFiniteCuspRestriction_bound (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaFiniteCuspRestriction F‖≤‖cubicThetaFiniteEnergyValue F‖ := by
  have hi := cubicThetaInjective_integral_le (cubicThetaCuspStrip_measurable 2)
    (cubicThetaCuspStrip_injective (by norm_num)) (cubicThetaFiniteEnergy_norm_integrable F)
    (fun q => sq_nonneg (cubicThetaSectionNorm F q))
  simp only [cubicThetaSectionNorm_apply] at hi
  rw [← cubicThetaFiniteCuspRestriction_norm_sq,← cubicThetaFiniteEnergyValue_norm_sq] at hi
  nlinarith [_root_.norm_nonneg (cubicThetaFiniteCuspRestriction F),
    _root_.norm_nonneg (cubicThetaFiniteEnergyValue F)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFrequencyHolomorphic
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Holomorphy of the actual arithmetic Fourier coefficients on their
initial half-plane, with a common bound independent of the frequency. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFrequencyTerm_strip_bound {a : ℝ} (ha : 2<a)
    {s : ℂ} (hs : a < s.re) (h c : Eisenstein) :
    ‖cubicThetaFrequencyTerm s h c‖ ≤ 9*(norm c)^(-(a-1)) := by
  by_cases hc : c=0
  · simp only [hc,cubicThetaFrequencyTerm,ne_eq,not_true_eq_false,and_false,ite_false, if_false,norm_zero]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (norm_nonneg _) _)
  · exact (cubicThetaFrequencyTerm_bound (ha.trans hs) h c).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (one_le_norm hc) (by linarith)) (by norm_num))

lemma cubicThetaFrequencyDirichlet_differentiableOn {a : ℝ} (ha : 2<a)
    (h : Eisenstein) :
    DifferentiableOn ℂ (cubicThetaFrequencyDirichlet h) {s : ℂ | a < s.re} := by
  apply Complex.differentiableOn_tsum_of_summable_norm
    ((summable_eisenstein_norm_rpow (show 1<a-1 by linarith)).mul_left 9)
  · intro c
    exact (cubicThetaFrequencyTerm_entire h c).differentiableOn
  · exact isOpen_lt continuous_const Complex.continuous_re
  · intro c s hs
    exact cubicThetaFrequencyTerm_strip_bound ha hs h c

theorem cubicThetaFrequencyDirichlet_differentiableAt (h : Eisenstein)
    {s : ℂ} (hs : 2 < s.re) :
    DifferentiableAt ℂ (cubicThetaFrequencyDirichlet h) s := by
  have ha : 2<(2+s.re)/2 := by linarith
  have hU : IsOpen {z : ℂ | (2+s.re)/2<z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hsU : s ∈ {z : ℂ | (2+s.re)/2<z.re} := by
    change (2+s.re)/2 < s.re
    linarith
  exact (cubicThetaFrequencyDirichlet_differentiableOn ha h).differentiableAt
    (hU.mem_nhds hsU)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHeightBandCore
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every bounded height band in an integral cusp lies in a compact core. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaHeightBand_core {H : ℝ} (hH : 1≤H) :
    ∃ S : Finset SL(2,Eisenstein), ∀ (δ : SL(2,Eisenstein)) (p : CubicThetaPoint),
      1 ≤ cubicThetaPointHeight p → cubicThetaPointHeight p≤H →
        cubicThetaQuotientMap (δ • p)∈cubicThetaQuotientCore S H := by
  obtain ⟨S,hS⟩ := cubicThetaFiniteSiegelCover
  refine ⟨S,?_⟩
  intro δ p hp₁ hp₂
  let q := δ • p
  obtain ⟨σ,hσ,k,hk⟩ := hS q.val q.property
  let y := (σ*k.val) • q
  have hy : y.val∈cubicThetaSiegelSet := hk
  have hb : cubicThetaPointHeight y≤H := by
    have he : y=(σ*k.val*δ) • p := by rw [mul_smul]
    rw [he]
    apply (cubicThetaPointHeight_full_smul_le _ p).trans
    apply max_le hp₂
    apply (div_le_iff₀ (cubicThetaPointHeight_pos p)).mpr
    nlinarith
  have hyc : y.val∈cubicThetaSiegelCore H := cubicThetaSiegelSet_mem_core hy hb
  have hpoint : σ⁻¹ • y=k • q := by
    dsimp [y]
    rw [mul_smul,inv_smul_smul]
    rfl
  refine ⟨k • q,?_,cubicThetaQuotient_covering.map_smul k⟩
  change (k • q).val∈cubicThetaCompactCore S H
  refine mem_iUnion.mpr ⟨σ,mem_iUnion.mpr ⟨hσ,y.val,hyc,?_⟩⟩
  exact congrArg cubicThetaPointCoordinates hpoint

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPeriodMeasure
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact Jacobian of the level-three period cell. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPeriodEquiv_map_volume :
    Measure.map cubicThetaPeriodEquiv volume=
      ENNReal.ofReal (2/(9*Real.sqrt 3)) • (volume : Measure ℂ) := by
  have he : (cubicThetaPeriodEquiv : (Fin 2 → ℝ) → ℂ)=
      (fun z : ℂ => 3*z) ∘ eisensteinRealCoords := rfl
  rw [he,← Measure.map_map (by fun_prop) eisensteinRealCoords.continuous.measurable,
    eisensteinRealCoords_map_volume,
    Measure.map_smul,complexMul_map_volume 3 (by norm_num),smul_smul]
  congr 1
  norm_num only [Complex.normSq_ofNat,ENNReal.ofReal_ofNat]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

lemma cubicThetaPeriodEquiv_preimage_cell :
    cubicThetaPeriodEquiv ⁻¹' cubicThetaHorizontalCell=
      {x : Fin 2 → ℝ | ∀ i, x i∈Ico (0:ℝ) 1} := by
  ext x
  simp only [mem_preimage,cubicThetaHorizontalCell,mem_ofPred_eq,cubicThetaPeriodEquiv_apply,
    cubicThetaPeriodCoordinates_cell]

lemma cubicThetaHorizontalCell_integral (f : ℂ → ℂ) :
    (∫ z in cubicThetaHorizontalCell, f z)=
      (9*Real.sqrt 3/2:ℝ) •
        ∫ x in {x : Fin 2 → ℝ | ∀ i, x i∈Ico (0:ℝ) 1}, f (cubicThetaPeriodCell x) := by
  have hi := setIntegral_map_equiv (μ:=volume) cubicThetaPeriodEquiv.toHomeomorph.toMeasurableEquiv f
    cubicThetaHorizontalCell
  change (∫ z in cubicThetaHorizontalCell, f z ∂Measure.map cubicThetaPeriodEquiv volume)=
    ∫ x in cubicThetaPeriodEquiv ⁻¹' cubicThetaHorizontalCell, f (cubicThetaPeriodEquiv x) at hi
  rw [cubicThetaPeriodEquiv_map_volume,Measure.restrict_smul,integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : (0:ℝ)≤2/(9*Real.sqrt 3)),
    cubicThetaPeriodEquiv_preimage_cell] at hi
  have he : (9*Real.sqrt 3/2:ℝ)*(2/(9*Real.sqrt 3))=1 := by
    field_simp
  calc
    _ = (9*Real.sqrt 3/2:ℝ) • ((2/(9*Real.sqrt 3):ℝ) •
        ∫ z in cubicThetaHorizontalCell, f z) := by rw [smul_smul,he,one_smul]
    _ = _ := congrArg (fun w : ℂ => (9*Real.sqrt 3/2:ℝ) • w) hi

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact Fourier coefficient normalization for the physical cusp cell. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.cubicThetaHorizontalCoefficientMeasureSpace
attribute [local instance] OAI.CubicFirstMoment.cubicThetaHorizontalCoefficientProbability
lemma cubicThetaHorizontalCoefficient (f : ℂ → ℂ)
    (F : C(UnitAddTorus (Fin 2),ℂ)) (h : Eisenstein)
    (hf : ∀ x, f (cubicThetaPeriodCell x)=F (fun i => (x i:UnitAddCircle))) :
    (∫ z in cubicThetaHorizontalCell,
      star (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)*f z)=
      (9*Real.sqrt 3/2:ℝ) • cubicThetaTorusCoefficient (ContinuousMap.toLp 2 volume ℂ F) h := by
  rw [cubicThetaHorizontalCell_integral,cubicThetaTorusCoefficient_integral,
    cubicThetaTorus_integral_cell]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  rw [hf,cubicThetaTorusFourier_actual]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHighWindowPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global pairing with the high forcing is exactly the constant
cusp observation, first on actual sections and then on the energy closure. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaInjective_complex_integral {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) (hi : InjOn cubicThetaQuotientMap S)
    (f : CubicThetaQuotient → ℂ) (hf : StronglyMeasurable f) :
    (∫ q in cubicThetaQuotientMap '' S, f q ∂cubicThetaQuotientMeasure)=
      ∫ p in S, f (cubicThetaQuotientMap p) ∂cubicThetaPointMeasure := by
  rw [← cubicThetaInjective_map_restrict hS hi]
  exact integral_map_of_stronglyMeasurable cubicThetaQuotientMap_open.continuous.measurable hf

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalDomain
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal half-open level-three cell is a fundamental domain for
horizontal translations. This is the measure bridge for Hecke constant modes. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaHorizontalCell_unique (z : ℂ) :
    ∃! g : CubicThetaPeriodGroup,g • z∈cubicThetaHorizontalCell := by
  let x := cubicThetaPeriodCoordinates z
  let n : Fin 2 → ℤ := fun i => -Int.floor (x i)
  let w := coordinatesEquiv n
  refine ⟨Multiplicative.ofAdd w,?_,?_⟩
  · intro i
    change cubicThetaPeriodCoordinates (z+3*(w:ℂ)) i∈Ico (0:ℝ) 1
    rw [cubicThetaPeriodCoordinates_translate]
    have he : (cubicThetaPeriodCoordinates z+fun j => ((coordinatesEquiv.symm w) j:ℝ)) i=
        Int.fract (x i) := by
      simp only [w,LinearEquiv.symm_apply_apply,Pi.add_apply,n,Int.cast_neg]
      rfl
    rw [he]
    exact ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
  · intro g hg
    change Multiplicative.toAdd g=w
    apply coordinatesEquiv.symm.injective
    funext i
    have hi := hg i
    change cubicThetaPeriodCoordinates (z+3*((Multiplicative.toAdd g:Eisenstein):ℂ)) i∈Ico (0:ℝ) 1 at hi
    rw [cubicThetaPeriodCoordinates_translate] at hi
    have hz : Int.floor ((cubicThetaPeriodCoordinates z) i+
        ((coordinatesEquiv.symm (Multiplicative.toAdd g)) i:ℝ))=0 :=
      Int.floor_eq_zero_iff.mpr hi
    rw [Int.floor_add_intCast] at hz
    change (coordinatesEquiv.symm (Multiplicative.toAdd g)) i=(coordinatesEquiv.symm (coordinatesEquiv n)) i
    rw [LinearEquiv.symm_apply_apply]
    dsimp [n,x]
    omega

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSmoothLocalWeak
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaGlobalEnergySpace_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate Green identity applied to a genuine smooth section
with its actual differential equation. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaSectionFunction_continuousOn (F : CubicThetaSection) :
    ContinuousOn (cubicThetaSectionFunction F) {p : ℂ × ℝ | 0<p.2} := by
  apply F.val.continuous.comp_continuousOn
  apply cubicThetaPointInclusion.symm.continuousOn.mono
  intro p hp
  rwa [OpenPartialHomeomorph.symm_source,cubicThetaPointInclusion_target]

lemma cubicThetaSmooth_axis_regular (G : cubicThetaSmoothTests) (k : CubicThetaAxis)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContDiffAt ℝ 2 (fun t => cubicThetaSectionFunction G
      (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t))
      (cubicThetaCoordinateCenter k p.1.re p.1.im p.2) := by
  have hc := G.property.1.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)
  have hl : ContDiff ℝ ∞ (cubicThetaCoordinateLine k p.1.re p.1.im p.2) := by
    cases k with
    | x => exact (Complex.ofRealCLM.contDiff.add contDiff_const).prodMk contDiff_const
    | y => exact (contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)).prodMk contDiff_const
    | height => exact contDiff_const.prodMk contDiff_id
  have he : cubicThetaCoordinateLine k p.1.re p.1.im p.2
      (cubicThetaCoordinateCenter k p.1.re p.1.im p.2)=p :=
    (cubicThetaCoordinateLine_center _ _ _ _).trans (cubicThetaCartesianPoint_self p)
  have hcp : ContDiffAt ℝ ∞ (cubicThetaSectionFunction G)
      (cubicThetaCoordinateLine k p.1.re p.1.im p.2
        (cubicThetaCoordinateCenter k p.1.re p.1.im p.2)) := by
    rw [he]
    exact hc
  exact (hcp.comp _ hl.contDiffAt).of_le (by norm_num)

theorem cubicThetaSmooth_local_weak (G : cubicThetaSmoothTests) (J : CubicThetaSection)
    (lam : ℂ) (hEq : ∀ p : ℂ × ℝ, 0<p.2 →
      cubicThetaCoordinateLaplacian (cubicThetaSectionFunction G) p=
        lam*cubicThetaSectionFunction G p-cubicThetaSectionFunction J p)
    (φ : ℂ × ℝ → ℂ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ⊆{p : ℂ × ℝ | 0<p.2}) :
    (∫ p, cubicThetaHeightInverse p*cubicThetaCoordinatePairing φ
      (cubicThetaSectionFunction G) p)+
      lam*(∫ p, star (φ p)*cubicThetaSectionFunction G p/(p.2:ℂ)^3)=
    ∫ p, star (φ p)*cubicThetaSectionFunction J p/(p.2:ℂ)^3 := by
  have hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {p : ℂ × ℝ | 0<p.2} :=
    G.property.1.of_le (show (1:ℕ∞ω)≤∞ by norm_num)
  have hg := cubicThetaLocalGreen_identity φ (cubicThetaSectionFunction G) hφ hc hp hG
    (fun k => cubicThetaAxisSecond_continuousOn k _
      (isOpen_lt continuous_const continuous_snd) (G.property.1.of_le (by norm_num)))
    (fun k p hp => cubicThetaSmooth_axis_regular G k hp)
  have hd : ContinuousOn (fun p : ℂ × ℝ => (p.2:ℂ)^3) {p : ℂ × ℝ | 0<p.2} :=
    (Complex.continuous_ofReal.comp continuous_snd).continuousOn.pow 3
  have hn : ∀ p∈{p : ℂ × ℝ | 0<p.2}, (p.2:ℂ)^3≠0 :=
    fun p hp => pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hp.ne')
  have hM : Integrable (fun p => star (φ p)*cubicThetaSectionFunction G p/(p.2:ℂ)^3) := by
    simpa only [mul_div_assoc,Pi.div_apply] using cubicThetaPositiveStarProduct_integrable
      hφ.continuous hc hp (hG.continuousOn.div hd hn)
  have hJ : Integrable (fun p => star (φ p)*cubicThetaSectionFunction J p/(p.2:ℂ)^3) := by
    simpa only [mul_div_assoc,Pi.div_apply] using cubicThetaPositiveStarProduct_integrable
      hφ.continuous hc hp ((cubicThetaSectionFunction_continuousOn J).div hd hn)
  have he (p : ℂ × ℝ) :
      star (φ p)*cubicThetaCoordinateLaplacian (cubicThetaSectionFunction G) p/(p.2:ℂ)^3=
        lam*(star (φ p)*cubicThetaSectionFunction G p/(p.2:ℂ)^3)-
          star (φ p)*cubicThetaSectionFunction J p/(p.2:ℂ)^3 := by
    by_cases hpos : 0<p.2
    · rw [hEq p hpos]
      ring
    · have hz : φ p=0 := image_eq_zero_of_notMem_tsupport (fun h => hpos (hp h))
      simp only [hz,star_zero,zero_mul,zero_div,mul_zero,sub_self]
  have hi : (∫ p, star (φ p)*cubicThetaCoordinateLaplacian
      (cubicThetaSectionFunction G) p/(p.2:ℂ)^3)=
      lam*(∫ p, star (φ p)*cubicThetaSectionFunction G p/(p.2:ℂ)^3)-
        ∫ p, star (φ p)*cubicThetaSectionFunction J p/(p.2:ℂ)^3 := by
    simp_rw [he]
    rw [integral_sub (hM.const_mul _) hJ,integral_const_mul]
  rw [hi] at hg
  linear_combination hg

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSmoothWeakDefect
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous weak defect for an actual smooth section and its
compact forcing. This will pass the coordinate equation to the energy closure. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaSmoothWeakDefect (G : cubicThetaSmoothTests) (J : CubicThetaSection)
    (hJ : HasCompactSupport (cubicThetaSectionNorm J)) (lam : ℂ) :
    CubicThetaGlobalEnergyAmbient →+ ℂ where
  toFun u :=
    inner ℂ (WithLp.sndL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2 u) (cubicThetaGlobalGradient G)+
    lam*inner ℂ (WithLp.fstL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2 u) (cubicThetaGlobalMass G)-
    inner ℂ (WithLp.fstL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2 u)
      ((cubicThetaCompactSection_memLp J hJ).toLp _)
  map_zero' := by simp
  map_add' u v := by
    simp only [map_add,inner_add_left]
    ring

lemma cubicThetaSmoothWeakDefect_continuous (G : cubicThetaSmoothTests) (J : CubicThetaSection)
    (hJ : HasCompactSupport (cubicThetaSectionNorm J)) (lam : ℂ) :
    Continuous (cubicThetaSmoothWeakDefect G J hJ lam) := by
  change Continuous (fun u : CubicThetaGlobalEnergyAmbient =>
    inner ℂ (WithLp.sndL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2 u) (cubicThetaGlobalGradient G)+
    lam*inner ℂ (WithLp.fstL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2 u) (cubicThetaGlobalMass G)-
    inner ℂ (WithLp.fstL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2 u)
      ((cubicThetaCompactSection_memLp J hJ).toLp _))
  fun_prop

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeTraceExpansion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubed-prime trace as two explicit finite sums. Both the actual
integral representatives and their Kubota phases are retained. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeTraceSection_expansion {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p) (x : CubicThetaPoint) :
    (cubicThetaPrimeCubeTraceSection hp F).val x=
      (∑' r : Residues (p^3),
        F.val (cubicThetaPrincipalLower (residueRepresentative (p^3) r) • x))+
      (∑' r : cubicThetaPrimeCubeUpperParameter p,
        star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
          F.val (cubicThetaPrimeCubeUpperRepresentative hp r • x)) := by
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Finite (cubicThetaPrimeCubeUpperParameter p) := by
    unfold cubicThetaPrimeCubeUpperParameter
    infer_instance
  change (∑' t : cubicThetaPrimeCubeTransversal p,cubicThetaPrimeCubeTraceTerm p F t.val x)=_
  rw [←(cubicThetaPrimeCubeChartEquiv hp).tsum_eq,
    Summable.tsum_sum Summable.of_finite Summable.of_finite]
  congr 1
  · apply tsum_congr
    intro r
    change cubicThetaPrimeCubeTraceTerm p F
      (cubicThetaPrimeCubeCoset p (cubicThetaPrincipalLower (residueRepresentative (p^3) r))).val x=_
    rw [cubicThetaPrimeCubeTraceTerm_coset]
    simp only [cubicThetaPrimeCubeTraceTerm,cubicThetaPrincipalLower_value,star_one,one_mul]
  · apply tsum_congr
    intro r
    change cubicThetaPrimeCubeTraceTerm p F
      (cubicThetaPrimeCubeCoset p (cubicThetaPrimeCubeUpperRepresentative hp r)).val x=_
    rw [cubicThetaPrimeCubeTraceTerm_coset]
    simp only [cubicThetaPrimeCubeTraceTerm,cubicThetaPrimeCubeUpperRepresentative,
      cubicThetaKubotaValue_mul,cubicThetaPrincipalTranslation_value,mul_one]

theorem cubicThetaPrimeCubeHecke_expansion {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    (cubicThetaPrimeCubeHecke hp F).val x=
      (∑' r : Residues (p^3), F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
        (cubicThetaPrincipalLower (residueRepresentative (p^3) r) • x)))+
      (∑' r : cubicThetaPrimeCubeUpperParameter p,
        star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
          F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
            (cubicThetaPrimeCubeUpperRepresentative hp r • x))) :=
  cubicThetaPrimeCubeTraceSection_expansion hp (cubicThetaPrimeCubeDilationSection hp F) x

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalSection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous periodic horizontal slices of the actual automorphic
sections, with their genuine finite cell integrals. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaSectionHorizontal_integrable (F : CubicThetaSection) (v : ℝ) (hv : 0<v) :
    IntegrableOn (cubicThetaSectionHorizontal F v hv) cubicThetaHorizontalCell := by
  obtain ⟨K,hK,hsub⟩ := cubicThetaHorizontalCell_compact_container
  exact ((cubicThetaSectionHorizontal F v hv).continuous.continuousOn.integrableOn_compact hK).mono_set hsub

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalAffine
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Affine translates have the same cell integral after an integral
nonzero Eisenstein dilation. This is used for the character branches. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaHorizontal_affine_integrable (f : C(ℂ,ℂ)) (a b : ℂ) :
    IntegrableOn (fun z => f (a*z+b)) cubicThetaHorizontalCell := by
  obtain ⟨K,hK,hsub⟩ := cubicThetaHorizontalCell_compact_container
  have hc : Continuous (fun z : ℂ => f (a*z+b)) := by fun_prop
  exact (hc.continuousOn.integrableOn_compact hK).mono_set hsub

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite residue coordinates for the sublattice used by a horizontal
Hecke dilation. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaHorizontalScaledCell (a : Eisenstein) : Set ℂ :=
  (fun z : ℂ => (a:ℂ)*z) '' cubicThetaHorizontalCell

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalCover
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A disjoint finite union of period cells for the scaled horizontal lattice. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaHorizontalCover (a : Eisenstein) : Set ℂ :=
  ⋃ r : Residues a, (fun z : ℂ => z-3*(residueRepresentative a r:ℂ)) '' cubicThetaHorizontalCell

lemma cubicThetaHorizontalCover_unique {a : Eisenstein} (ha : a≠0) (z : ℂ) :
    ∃! g : CubicThetaScaledPeriodGroup a,g • z∈cubicThetaHorizontalCover a := by
  obtain ⟨w,hw,hwu⟩ := cubicThetaHorizontalCell_unique z
  let mr := (cubicThetaHorizontalLatticeEquiv ha).symm (Multiplicative.toAdd w)
  have he : a*mr.1+residueRepresentative a mr.2=Multiplicative.toAdd w :=
    (cubicThetaHorizontalLatticeEquiv ha).apply_symm_apply _
  refine ⟨Multiplicative.ofAdd mr.1,?_,?_⟩
  · refine mem_iUnion.mpr ⟨mr.2, z+3*((Multiplicative.toAdd w:Eisenstein):ℂ), hw, ?_⟩
    change z+3*((Multiplicative.toAdd w:Eisenstein):ℂ)-3*(residueRepresentative a mr.2:ℂ)=
      z+3*(a:ℂ)*(mr.1:ℂ)
    rw [←he]
    push_cast
    ring
  · intro g hg
    obtain ⟨r,y,hy,hyg⟩ := mem_iUnion.mp hg
    have hwy : Multiplicative.ofAdd (a*Multiplicative.toAdd g+residueRepresentative a r)=w := by
      apply hwu
      convert hy using 1
      all_goals try with_reducible_and_instances rfl
      change z+3*((a*Multiplicative.toAdd g+residueRepresentative a r:Eisenstein):ℂ)=y
      change y-3*(residueRepresentative a r:ℂ)=z+3*(a:ℂ)*((Multiplicative.toAdd g:Eisenstein):ℂ) at hyg
      push_cast
      linear_combination -hyg
    have hpair : (Multiplicative.toAdd g,r)=mr := by
      apply (cubicThetaHorizontalLatticeEquiv ha).injective
      exact (congrArg (fun v : CubicThetaPeriodGroup => (Multiplicative.toAdd v:Eisenstein)) hwy).trans he.symm
    exact congrArg (fun v : Eisenstein × Residues a => Multiplicative.ofAdd v.1) hpair

lemma cubicThetaHorizontalCover_disjoint (a : Eisenstein) :
    Pairwise (fun r s : Residues a =>
      Disjoint ((fun z : ℂ => z-3*(residueRepresentative a r:ℂ)) '' cubicThetaHorizontalCell)
        ((fun z : ℂ => z-3*(residueRepresentative a s:ℂ)) '' cubicThetaHorizontalCell)) := by
  intro r s hrs
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
  have hw : (Multiplicative.ofAdd (residueRepresentative a s) : CubicThetaPeriodGroup)=
      Multiplicative.ofAdd (residueRepresentative a r) := by
    apply (cubicThetaHorizontalCell_unique z).unique
    · change z+3*(residueRepresentative a s:ℂ)∈cubicThetaHorizontalCell
      have h : z+3*(residueRepresentative a s:ℂ)=y := by linear_combination -hyz
      rwa [h]
    · change z+3*(residueRepresentative a r:ℂ)∈cubicThetaHorizontalCell
      have h : z+3*(residueRepresentative a r:ℂ)=x := by linear_combination -hxz
      rwa [h]
  have he : residueRepresentative a s=residueRepresentative a r :=
    congrArg (fun v : CubicThetaPeriodGroup => (Multiplicative.toAdd v:Eisenstein)) hw
  apply hrs
  simpa only [residueRepresentative_spec] using
    (congrArg (Ideal.Quotient.mk (modulus a)) he).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalFourierTranslation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourier observations on the literal half-open cell, under translation
and integral dilation. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaHorizontalFourierCoefficient (h : Eisenstein) (f : ℂ → ℂ) : ℂ :=
  ∫ z in cubicThetaHorizontalCell,star (cubicThetaHorizontalCharacter h z)*f z

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalFourierIntegrability
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute integrability of the actual weighted cell coefficients. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaHorizontalFourier_integrable (h : Eisenstein) (f : ℂ → ℂ)
    (hf : Continuous f) :
    IntegrableOn (fun z => star (cubicThetaHorizontalCharacter h z)*f z)
      cubicThetaHorizontalCell := by
  obtain ⟨K,hK,hsub⟩ := cubicThetaHorizontalCell_compact_container
  exact (((cubicThetaHorizontalCharacter_continuous h).star.mul hf).continuousOn.integrableOn_compact hK).mono_set hsub

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalFourierAlgebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linearity of the literal horizontal Fourier observation. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaHorizontalFourier_const_mul (h : Eisenstein) (c : ℂ) (f : ℂ → ℂ) :
    cubicThetaHorizontalFourierCoefficient h (fun z => c*f z)=
      c*cubicThetaHorizontalFourierCoefficient h f := by
  unfold cubicThetaHorizontalFourierCoefficient
  rw [←integral_const_mul]
  congr 1
  funext z
  ring

lemma cubicThetaHorizontalFourier_sum {ι : Type*} (s : Finset ι)
    (h : Eisenstein) (f : ι → ℂ → ℂ) (hf : ∀ i ∈ s,Continuous (f i)) :
    cubicThetaHorizontalFourierCoefficient h (fun z => ∑ i ∈ s,f i z)=
      ∑ i ∈ s,cubicThetaHorizontalFourierCoefficient h (f i) := by
  unfold cubicThetaHorizontalFourierCoefficient
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum s (fun i hi => cubicThetaHorizontalFourier_integrable h _ (hf i hi))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalPeriodization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The horizontal periodization appearing in the bottom Hecke branch. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaHorizontalPeriodization_integrable {a : Eisenstein} (ha : a≠0)
    (f : C(ℂ,ℂ)) : IntegrableOn (cubicThetaHorizontalPeriodization a f) cubicThetaHorizontalCell := by
  obtain ⟨K,hK,hsub⟩ := cubicThetaHorizontalCell_compact_container
  exact ((cubicThetaHorizontalPeriodization_continuous ha f).continuousOn.integrableOn_compact hK).mono_set hsub

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialProfileSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact radial profiles give actual automorphic sections by a locally finite
Poincaré sum. No spectral input is used. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups CompactlySupported
namespace CubicFirstMoment


theorem cubicThetaRadialProfileSeries_core (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ), W v=0) :
    ∃ (H : ℝ) (S : Finset SL(2,Eisenstein)),
      ∀ p : CubicThetaPoint, cubicThetaQuotientMap p∉cubicThetaQuotientCore S H →
        cubicThetaRadialProfileSeries p.val W=0 := by
  obtain ⟨B,hB⟩ := W.hasCompactSupport.isCompact.bddAbove_image continuous_id.continuousOn
  let H := max 1 B
  obtain ⟨S,hS⟩ := cubicThetaHeightBand_core (le_max_left 1 B)
  refine ⟨H,S,fun p hp => ?_⟩
  suffices hz : ∀ r, cubicThetaRadialProfileTerm r p.val W=0 by
    simp only [cubicThetaRadialProfileSeries,hz,tsum_zero]
  intro r
  by_cases hlo : r.height p.val≤1
  · exact mul_eq_zero_of_right _ (hW _ hlo)
  by_cases hz : W (r.height p.val)=0
  · exact mul_eq_zero_of_right _ hz
  have hhi : r.height p.val≤H :=
    (hB (mem_image_of_mem id (subset_closure hz))).trans (le_max_right 1 B)
  have he : cubicThetaPointHeight (r.completion • p)=r.height p.val := by
    change (cubicThetaBottomRow r.completion).height p.val=_
    rw [r.completion_row]
  have hq := hS 1 (r.completion • p) (by rw [he]; linarith) (by rw [he]; exact hhi)
  rw [one_smul,cubicThetaQuotient_covering.map_smul] at hq
  exact False.elim (hp hq)

lemma cubicThetaRadialProfileSection_compact (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ), W v=0) :
    HasCompactSupport (cubicThetaSectionNorm (cubicThetaRadialProfileSection W hW)) := by
  obtain ⟨H,S,hS⟩ := cubicThetaRadialProfileSeries_core W hW
  apply HasCompactSupport.of_support_subset_isCompact (cubicThetaQuotientCore_compact S H)
  intro q hq
  by_contra h
  have hz := hS (cubicThetaQuotientLift q) (by rwa [cubicThetaQuotientLift_map])
  apply hq
  change ‖cubicThetaRadialProfileSeries (cubicThetaQuotientLift q).val W‖=0
  rw [hz,norm_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialProfileSmooth
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth compact radial profiles produce genuine compact smooth sections. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff CompactlySupported
namespace CubicFirstMoment

def cubicThetaRadialProfileTest (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ), W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) : cubicThetaSmoothTests :=
  ⟨cubicThetaRadialProfileSection W hW,by
    refine ⟨?_,cubicThetaRadialProfileSection_compact W hW⟩
    apply (cubicThetaRadialProfileSeries_contDiffOn W hW hsm).congr
    intro y hy
    change cubicThetaRadialProfileSeries (cubicThetaPointInclusion.symm y).val W=
      cubicThetaRadialProfileSeries y W
    have he := cubicThetaPointInclusion.right_inv (show y∈cubicThetaPointInclusion.target by
      rwa [cubicThetaPointInclusion_target])
    change (cubicThetaPointInclusion.symm y).val=y at he
    exact congrArg (fun p => cubicThetaRadialProfileSeries p W) he⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialProfileEquation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pointwise Euler equation of a compact radial profile is preserved
by the actual locally finite arithmetic sum. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaRadialProfile_coordinate_equation (W J : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ), W v=0) (hJ : ∀ v≤(1:ℝ), J v=0)
    (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) (lam : ℂ)
    (hEq : ∀ v, 0<v → cubicThetaRadialEuler W v=lam*W v-J v)
    (p : ℂ × ℝ) (hp : 0<p.2) :
    cubicThetaCoordinateLaplacian (cubicThetaSectionFunction (cubicThetaRadialProfileTest W hW hsm)) p=
      lam*cubicThetaSectionFunction (cubicThetaRadialProfileTest W hW hsm) p-
        cubicThetaSectionFunction (cubicThetaRadialProfileSection J hJ) p := by
  have he : ∀ x y v, 0<v →
      cubicThetaSectionFunction (cubicThetaRadialProfileTest W hW hsm) (cubicThetaCartesianPoint x y v)=
        cubicThetaRadialProfileSeries (cubicThetaCartesianPoint x y v) W := by
    intro x y v hv
    rw [cubicThetaSectionFunction_apply _ hv]
    rfl
  rw [cubicThetaCoordinateLaplacian_hyperbolic,cubicThetaHyperbolicOperator_congr he p.1.re p.1.im hp,
    cubicThetaRadialProfileSeries_equation W J hW hJ hsm lam hEq p.1.re p.1.im hp,
    cubicThetaCartesianPoint_self,cubicThetaSectionFunction_apply _ hp,cubicThetaSectionFunction_apply _ hp]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeAtkinConjugation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prime Atkin involution on the actual arithmetic subgroup. Its
cubic twist disappears on the kernel of the diagonal character. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeAtkinKernel_kubota {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCharacterKernel hp) :
    cubicThetaKubotaValue (cubicThetaPrimeAtkinKernel hp g).val.val=
      cubicThetaKubotaValue g.val.val := by
  change cubicThetaKubotaValue (cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹
    (cubicThetaPrimeConjugate hp.1 g.val))=cubicThetaKubotaValue g.val.val
  rw [cubicThetaInversionConjugate_character]
  have he := cubicThetaPrimeConjugate_kubota hp g.val
  have hg : cubicThetaPrimeIwahoriCharacter p hp g.val=1 := g.property
  rw [hg,one_mul] at he
  exact he.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeOppositeConjugation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complementary chart becomes the inverse dilation. The actual
integral conjugating matrix has exactly the Weyl representative's multiplier. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeWeyl_division {p : Eisenstein} (hp : primaryPrime p) :
    p^3*(cubicThetaPrimeCubeWeylDenominator hp/p^3)=cubicThetaPrimeCubeWeylDenominator hp :=
  EuclideanDomain.mul_div_cancel' (pow_ne_zero 3 hp.2.ne_zero)
    (cubicThetaPrimeCubeWeylDenominator_dvd hp)

def cubicThetaPrimeCubeOppositeMatrix {p : Eisenstein} (hp : primaryPrime p) : SL(2,Eisenstein) where
  val := !![p^3*(cubicThetaPrimeCubeWeyl hp).val 0 0,(cubicThetaPrimeCubeWeyl hp).val 0 1;
    3,cubicThetaPrimeCubeWeylDenominator hp/p^3]
  property := by
    have he := cubicThetaPrincipalGroup_det (cubicThetaPrimeCubeWeyl hp)
    rw [cubicThetaPrimeCubeWeyl_c,cubicThetaPrimeCubeWeyl_d] at he
    rw [Matrix.det_fin_two_of]
    linear_combination he+(cubicThetaPrimeCubeWeyl hp).val 0 0*
      (cubicThetaPrimeCubeWeyl_division hp)

lemma cubicThetaPrimeCubeOppositeMatrix_mem {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeOppositeMatrix hp∈cubicThetaPrincipalGroup := by
  have ha := (cubicThetaPrincipalGroup_diagonal_primary (cubicThetaPrimeCubeWeyl hp)).1
  have hb := (cubicThetaPrincipalGroup_offDiagonal (cubicThetaPrimeCubeWeyl hp)).1
  have hd : primary (cubicThetaPrimeCubeWeylDenominator hp/p^3) :=
    primary_of_mul (cubicThetaPrimeCube_primary hp) (by
      rw [cubicThetaPrimeCubeWeyl_division]
      exact cubicThetaPrimeCubeWeylDenominator_primary hp)
  exact (cubicThetaPrincipalGroup_mem_iff _).mpr
    ⟨primary_mul (cubicThetaPrimeCube_primary hp) ha,hb,dvd_refl _,hd⟩

def cubicThetaPrimeCubeOpposite {p : Eisenstein} (hp : primaryPrime p) : cubicThetaPrincipalGroup :=
  ⟨cubicThetaPrimeCubeOppositeMatrix hp,cubicThetaPrimeCubeOppositeMatrix_mem hp⟩

lemma cubicThetaPrimeCubeOpposite_kubota {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaKubotaValue (cubicThetaPrimeCubeOpposite hp)=
      cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp) := by
  have ha := (cubicThetaPrincipalGroup_diagonal_primary (cubicThetaPrimeCubeWeyl hp)).1
  rw [cubicThetaKubotaValue_eq_symbol,cubicThetaKubotaValue_eq_symbol,cubicThetaPrimeCubeWeyl_c]
  change cubicSymbol (p^3*(cubicThetaPrimeCubeWeyl hp).val 0 0) 3=_
  rw [cubicSymbol_mul_lower (pow_ne_zero 3 hp.2.ne_zero) (primary_ne_zero ha),
    cubicThetaSymbol_prime_pow hp,cubicSymbol_cube_of_isCoprime hp.1 3
      (primary_coprime_three hp.1),one_mul]

theorem cubicThetaPrimeCubeOpposite_intertwines {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)*
      cubicThetaPrincipalComplex (cubicThetaPrimeCubeWeyl hp)=
    cubicThetaPrincipalComplex (cubicThetaPrimeCubeOpposite hp)*
      (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))⁻¹ := by
  let q := cubicThetaPrimeSquareRoot (p^3)
  have hq : q≠0 := cubicThetaPrimeSquareRoot_ne_zero (pow_ne_zero 3 hp.2.ne_zero)
  have hs : q^2=(p:ℂ)^3 := (cubicThetaPrimeSquareRoot_sq (p^3)).trans
    (map_pow (eisensteinRing.subtype : Eisenstein →+* ℂ) p 3)
  have hd : (p:ℂ)^3*((cubicThetaPrimeCubeWeylDenominator hp/p^3:Eisenstein):ℂ)=
      (cubicThetaPrimeCubeWeylDenominator hp:Eisenstein) := by
    have h := congrArg (fun z : Eisenstein => (z:ℂ)) (cubicThetaPrimeCubeWeyl_division hp)
    push_cast at h
    exact h
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply,Fin.sum_univ_two,cubicThetaPrimeDilation,
      cubicThetaPrincipalComplex_apply,
      cubicThetaPrimeCubeOpposite,cubicThetaPrimeCubeOppositeMatrix]
    change q*((cubicThetaPrimeCubeWeyl hp).val 0 0:Eisenstein)=_
    change q*((cubicThetaPrimeCubeWeyl hp).val 0 0:Eisenstein)=
      ((p:ℂ)^3*((cubicThetaPrimeCubeWeyl hp).val 0 0:Eisenstein))*q⁻¹
    field_simp
    linear_combination ((cubicThetaPrimeCubeWeyl hp).val 0 0:Eisenstein)*hs
  · simp [Matrix.mul_apply,Fin.sum_univ_two,cubicThetaPrimeDilation,
      cubicThetaPrincipalComplex_apply,
      cubicThetaPrimeCubeOpposite,cubicThetaPrimeCubeOppositeMatrix,mul_comm]
  · simp [Matrix.mul_apply,Fin.sum_univ_two,cubicThetaPrimeDilation,
      cubicThetaPrincipalComplex_apply,
      cubicThetaPrimeCubeOpposite,cubicThetaPrimeCubeOppositeMatrix,cubicThetaPrimeCubeWeyl_c,mul_comm]
  · simp [Matrix.mul_apply,Fin.sum_univ_two,cubicThetaPrimeDilation,
      cubicThetaPrincipalComplex_apply,
      cubicThetaPrimeCubeOpposite,cubicThetaPrimeCubeOppositeMatrix,cubicThetaPrimeCubeWeyl_d]
    change q⁻¹*(cubicThetaPrimeCubeWeylDenominator hp:Eisenstein)=_
    field_simp
    linear_combination -hd-((cubicThetaPrimeCubeWeylDenominator hp/p^3:Eisenstein):ℂ)*hs

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeOppositeBranch
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complementary chart contributes the missing nonunit translations
in the lowest branch, with complete cancellation of its two multipliers. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeOpposite_section {p : Eisenstein} (hp : primaryPrime p)
    (m : Eisenstein) (F : CubicThetaSection) (x : CubicThetaPoint) :
    star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
      F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
        ((cubicThetaPrimeCubeWeyl hp*cubicThetaPrincipalTranslation m) • x))=
      F.val ((cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))⁻¹ •
        (cubicThetaPrincipalTranslation m • x)) := by
  have hu : star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
      cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp)=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
    norm_num
  rw [mul_smul]
  change star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
    F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
      (cubicThetaPrincipalComplex (cubicThetaPrimeCubeWeyl hp) •
        (cubicThetaPrincipalTranslation m • x)))=_
  rw [←mul_smul,cubicThetaPrimeCubeOpposite_intertwines,mul_smul]
  change star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
    F.val (cubicThetaPrimeCubeOpposite hp •
      ((cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))⁻¹ •
        (cubicThetaPrincipalTranslation m • x)))=_
  rw [F.property,cubicThetaPrimeCubeOpposite_kubota,←mul_assoc,hu,one_mul]

theorem cubicThetaPrimeCubeUpperBranch {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) (r : cubicThetaPrimeCubeUpperParameter p) :
    star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
      F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
        (cubicThetaPrimeCubeUpperRepresentative hp r • x))=
      F.val (cubicThetaPrimeCubeBranchPoint hp 0 (residueRepresentative (p^3) r.val) x) := by
  rw [cubicThetaPrimeCubeUpperRepresentative,cubicThetaPrimeCubeOpposite_section,
    cubicThetaPrimeCubeInverse_branchPoint]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeLowerValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The lower-chart value is a genuine function modulo p^3. Its scaled
versions descend to the smaller residue rings used in the valuation split. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeLowerValue_congr {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) (m n : Eisenstein) (h : p^3∣m-n) :
    cubicThetaPrimeCubeLowerValue hp F x m=cubicThetaPrimeCubeLowerValue hp F x n := by
  let g : cubicThetaPrimeIwahori (p^3) :=
    ⟨cubicThetaPrincipalLower (m-n),dvd_mul_of_dvd_right h 3⟩
  have he := (cubicThetaPrimeCubeDilationSection hp F).property g (cubicThetaPrincipalLower n • x)
  change (cubicThetaPrimeCubeDilationSection hp F).val
    (cubicThetaPrincipalLower (m-n) • (cubicThetaPrincipalLower n • x))=
      cubicThetaKubotaValue (cubicThetaPrincipalLower (m-n))*
        (cubicThetaPrimeCubeDilationSection hp F).val (cubicThetaPrincipalLower n • x) at he
  rw [←mul_smul,←cubicThetaPrincipalLower_add,sub_add_cancel,cubicThetaPrincipalLower_value,one_mul] at he
  exact he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeValuationSum
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal lower-chart sum split into its three exact prime
valuations and its zero class. All reductions preserve the sharp modulus. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeLowerValue_sum {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    (∑' r : Residues (p^3), cubicThetaPrimeCubeLowerValue hp F x (residueRepresentative (p^3) r))=
      cubicThetaPrimeCubeLowerValue hp F x 0+
      (∑' u : (Residues (p^3))ˣ, cubicThetaPrimeCubeLowerValue hp F x
        (residueRepresentative (p^3) (u : Residues (p^3))))+
      (∑' u : (Residues (p^2))ˣ, cubicThetaPrimeCubeLowerValue hp F x
        (p*residueRepresentative (p^2) (u : Residues (p^2))))+
      (∑' u : (Residues p)ˣ, cubicThetaPrimeCubeLowerValue hp F x
        (p^2*residueRepresentative p (u : Residues p))) :=
  cubicThetaPrimeCubePeriodic_sum hp _ (cubicThetaPrimeCubeLowerValue_congr hp F x)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeHeckeFormula
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal four-branch cubed-prime Hecke formula for actual cubic
automorphic sections, with the two intermediate cubic-character sums. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeLowerValue_branches {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    (∑' r : Residues (p^3),cubicThetaPrimeCubeLowerValue hp F x (residueRepresentative (p^3) r))=
      F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x)+
        cubicThetaPrimeCubeBranchSum hp 0 F x+cubicThetaPrimeCubeBranchSum hp 1 F x+
          cubicThetaPrimeCubeBranchSum hp (⟨2,by decide⟩ : Fin 3) F x := by
  rw [cubicThetaPrimeCubeLowerValue_sum,cubicThetaPrimeCubeLowerValue_zero,
    cubicThetaPrimeCubeBranchSum_zero,cubicThetaPrimeCubeBranchSum_one,
    cubicThetaPrimeCubeBranchSum_two]

theorem cubicThetaPrimeCubeHecke_fourBranches {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    (cubicThetaPrimeCubeHecke hp F).val x=
      F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x)+
        cubicThetaPrimeCubeFullBottomSum hp F x+
        cubicThetaPrimeCubeBranchSum hp 1 F x+cubicThetaPrimeCubeBranchSum hp (⟨2,by decide⟩ : Fin 3) F x := by
  have hu : (∑' r : cubicThetaPrimeCubeUpperParameter p,
      star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
        F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
          (cubicThetaPrimeCubeUpperRepresentative hp r • x)))=
      ∑' r : cubicThetaPrimeCubeUpperParameter p,
        F.val (cubicThetaPrimeCubeBranchPoint hp 0 (residueRepresentative (p^3) r.val) x) :=
    tsum_congr (cubicThetaPrimeCubeUpperBranch hp F x)
  rw [cubicThetaPrimeCubeHecke_expansion,hu,cubicThetaPrimeCubeBottomValue_split]
  change (∑' r : Residues (p^3),cubicThetaPrimeCubeLowerValue hp F x
    (residueRepresentative (p^3) r))+_= _
  rw [cubicThetaPrimeCubeLowerValue_branches]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeFourierOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit cubed-prime operator and its exact action on a single
horizontal mode. The formula keeps all frequency and height dilations. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeHecke_functionOperator {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    (cubicThetaPrimeCubeHecke hp F).val x=cubicThetaPrimeCubeFunctionOperator hp F.val x :=
  cubicThetaPrimeCubeHecke_fourBranches hp F x

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeFirstPeriodMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first character branch has zero horizontal mean. Integer dilation
turns each summand into a translate of the original slice. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeFirstPeriodization_integrable {p : Eisenstein} (hp : primaryPrime p)
    (f : C(ℂ,ℂ)) : IntegrableOn (cubicThetaPrimeCubeFirstPeriodization p f) cubicThetaHorizontalCell := by
  obtain ⟨K,hK,hsub⟩ := cubicThetaHorizontalCell_compact_container
  exact ((cubicThetaPrimeCubeFirstPeriodization_continuous hp f).continuousOn.integrableOn_compact hK).mono_set hsub

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeHorizontalContinuity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Horizontal slices of the literal Hecke summands are integrable on the
actual finite cell. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaContinuous_cell_integrable (f : ℂ → ℂ) (hf : Continuous f) :
    IntegrableOn f cubicThetaHorizontalCell := by
  obtain ⟨K,hK,hsub⟩ := cubicThetaHorizontalCell_compact_container
  exact (hf.continuousOn.integrableOn_compact hK).mono_set hsub

lemma cubicThetaPrimeCubeUnit_horizontal_integrable {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (F : CubicThetaSection) (v : ℝ) (hv : 0<v) :
    IntegrableOn (fun z => cubicThetaPrimeCubeUnitFunctionSum hp k F.val
      (cubicThetaHorizontalPoint v hv z)) cubicThetaHorizontalCell := by
  let : Finite (Residues (p^(3-k.val))) := finite_residues (pow_ne_zero _ hp.2.ne_zero)
  let : Fintype (Residues (p^(3-k.val)))ˣ := Fintype.ofFinite _
  apply cubicThetaContinuous_cell_integrable
  unfold cubicThetaPrimeCubeUnitFunctionSum
  simp_rw [tsum_fintype]
  apply continuous_finsetSum
  intro u _
  exact continuous_const.mul (F.val.continuous.comp
    (cubicThetaPrimeCubeBranch_horizontal_continuous hp k _ v hv))

lemma cubicThetaPrimeCubeBottom_horizontal_integrable {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) :
    IntegrableOn (fun z => cubicThetaPrimeCubeBottomFunctionSum hp F.val
      (cubicThetaHorizontalPoint v hv z)) cubicThetaHorizontalCell := by
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero _ hp.2.ne_zero)
  let : Fintype (Residues (p^3)) := Fintype.ofFinite _
  apply cubicThetaContinuous_cell_integrable
  unfold cubicThetaPrimeCubeBottomFunctionSum
  simp_rw [tsum_fintype]
  apply continuous_finsetSum
  intro u _
  exact F.val.continuous.comp (cubicThetaPrimeCubeBranch_horizontal_continuous hp 0 _ v hv)

lemma cubicThetaPrimeCubeDilation_horizontal_integrable {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (v : ℝ) (hv : 0<v) :
    IntegrableOn (fun z => F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
      cubicThetaHorizontalPoint v hv z)) cubicThetaHorizontalCell := by
  apply cubicThetaContinuous_cell_integrable
  exact F.val.continuous.comp ((continuous_const_smul _).comp (cubicThetaHorizontalPoint_continuous v hv))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSectionMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A proof-independent scalar horizontal mean for actual sections. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaSectionFunction_coordinates (F : CubicThetaSection) (p : CubicThetaPoint) :
    cubicThetaSectionFunction F p.val=F.val p := by
  change F.val (cubicThetaPointInclusion.symm (cubicThetaPointCoordinates p))=F.val p
  have h : cubicThetaPointInclusion.symm (cubicThetaPointCoordinates p)=p :=
    cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)
  exact congrArg F.val h

def cubicThetaSectionMean (F : CubicThetaSection) (v : ℝ) : ℂ :=
  ∫ z in cubicThetaHorizontalCell,cubicThetaSectionFunction F (z,v)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSectionMeanPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Genuine compact radial observations of finite-energy sections, expressed
through their scalar horizontal means. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaSectionMeanPairing_integrable (F : cubicThetaFiniteEnergySections)
    (W : C_c(ℝ,ℂ)) :
    IntegrableOn (fun p : CubicThetaPoint => star (W p.val.2)*F.val.val p)
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
  have hi := L2.integrable_inner (𝕜:=ℂ) (cubicThetaCuspFourierTest 0 W)
    (cubicThetaFiniteCuspRestriction F)
  apply hi.congr
  filter_upwards [(cubicThetaCuspFourierWeight_memLp 0 W).coeFn_toLp,
    (cubicThetaFiniteEnergy_strip_memLp F).coeFn_toLp] with p hW hF
  change inner ℂ (((cubicThetaCuspFourierWeight_memLp 0 W).toLp _) p)
    (((cubicThetaFiniteEnergy_strip_memLp F).toLp _) p)=_
  rw [hW,hF]
  rw [show cubicThetaCuspFourierWeight 0 W p=W p.val.2 from by
    simp [cubicThetaCuspFourierWeight,cubicThetaRowFrequency,tracePair]]
  simpa only [starRingEnd_apply] using (RCLike.inner_apply' (W p.val.2) (F.val.val p))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialProfilePairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact radial Poincaré profile supported above two pairs with the
actual constant cusp observation, including on the completed energy space. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaRadialProfileSeries_off_cusp (W : C_c(ℝ,ℂ)) (hW : ∀ v≤(2:ℝ), W v=0) (p : CubicThetaPoint)
    (hp : cubicThetaQuotientMap p∉cubicThetaQuotientMap '' cubicThetaCuspStrip 2) :
    cubicThetaRadialProfileSeries p.val W=0 := by
  suffices hz : ∀ r, cubicThetaRadialProfileTerm r p.val W=0 by
    simp only [cubicThetaRadialProfileSeries,hz,tsum_zero]
  intro r
  by_cases hh : r.height p.val≤2
  · exact mul_eq_zero_of_right _ (hW _ hh)
  have he : cubicThetaPointHeight (r.completion • p)=r.height p.val := by
    change (cubicThetaBottomRow r.completion).height p.val=_
    rw [r.completion_row]
  obtain ⟨w,hw⟩ := cubicThetaCuspStrip_reduction (H:=2) (r.completion • p) (by rw [he]; linarith)
  have hq : cubicThetaQuotientMap (cubicThetaPrincipalTranslation w • (r.completion • p))=
      cubicThetaQuotientMap p :=
    (cubicThetaQuotient_covering.map_smul (cubicThetaPrincipalTranslation w)).trans
      (cubicThetaQuotient_covering.map_smul r.completion)
  exact False.elim (hp ⟨_,hw,hq⟩)

def cubicThetaRadialProfileL2 (W : C_c(ℝ,ℂ)) (hW : ∀ v≤(2:ℝ), W v=0) : CubicThetaGlobalL2 :=
  (cubicThetaCompactSection_memLp (cubicThetaRadialProfileSection W (fun v hv => hW v (by linarith)))
    (cubicThetaRadialProfileSection_compact W (fun v hv => hW v (by linarith)))).toLp _


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaResidueKernelPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
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

lemma cubicThetaResidue_kernel_pairing (v : cubicThetaGlobalEnergySpace)
    (hv : cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (4/3:ℂ)) v=0) :
    inner ℂ v (cubicThetaArithmeticResidueEnergy (4/3))=
      (cubicThetaGlobalSpectralParameter (4/3:ℂ)/((2*(4/3:ℝ)-2:ℝ):ℂ))*
        inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaForcingL2 (4/3)) := by
  let K := (cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (4/3:ℂ))).ker
  have hPv : K.starProjection v=v := K.starProjection_eq_self_iff.mpr hv
  have hR : cubicThetaArithmeticResidueEnergy (4/3)=
      (17/6:ℂ) • K.starProjection (cubicThetaGlobalInclusion.adjoint (cubicThetaForcingL2 (4/3))) := by
    unfold cubicThetaArithmeticResidueEnergy K cubicThetaExceptionalProjection
    norm_num [cubicThetaGlobalSpectralParameter]
  have hc : cubicThetaGlobalSpectralParameter (4/3:ℂ)/((2*(4/3:ℝ)-2:ℝ):ℂ)=(17/6:ℂ) := by
    norm_num [cubicThetaGlobalSpectralParameter]
  rw [hR,inner_smul_right (𝕜:=ℂ) (E:=cubicThetaGlobalEnergySpace),hc]
  congr 1
  let f := cubicThetaGlobalInclusion.adjoint (cubicThetaForcingL2 (4/3))
  have he : inner ℂ (K.starProjection v) f = inner ℂ v f :=
    congrArg (fun w : cubicThetaGlobalEnergySpace => inner ℂ w f) hPv
  exact (K.inner_starProjection_left_eq_right v f).symm.trans
    (he.trans (cubicThetaGlobalInclusion.adjoint_inner_right v (cubicThetaForcingL2 (4/3))))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLongWindowKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual theta kernel can be paired with the incoming forcing in an
arbitrarily high compact annulus. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaLongWindowTest (H : ℝ) (hH : 2≤H) (s : ℂ) : cubicThetaSmoothTests :=
  cubicThetaRadialProfileTest (cubicThetaLongWindowWeight H (by linarith) s)
    (fun _ hv => cubicThetaLongWindowHeight_low (by linarith) s hv)
    (cubicThetaLongWindowHeight_smooth H s)

lemma cubicThetaLongWindowDefectSection_compact (H : ℝ) (hH : 2≤H) (s : ℂ) :
    HasCompactSupport (cubicThetaSectionNorm (cubicThetaLongWindowDefectSection H hH s)) :=
  cubicThetaRadialProfileSection_compact _ _

lemma cubicThetaLongWindowDefectSection_eq (H : ℝ) (hH : 2≤H) (s : ℂ) :
    cubicThetaLongWindowDefectSection H hH s=
      cubicThetaRadialProfileSection (cubicThetaLongForcingWeight H (by linarith) s)
        (cubicThetaLongForcingWeight_low_one hH s)-cubicThetaForcingSection s := by
  exact cubicThetaRadialProfileSection_sub _ _ (cubicThetaLongForcingWeight_low_one hH s)
    (cubicThetaIncomingForcingWeight_low s)

lemma cubicThetaLongWindowDefectL2 (H : ℝ) (hH : 2≤H) (s : ℂ) :
    (cubicThetaCompactSection_memLp (cubicThetaLongWindowDefectSection H hH s)
      (cubicThetaLongWindowDefectSection_compact H hH s)).toLp _=
      cubicThetaRadialProfileL2 (cubicThetaLongForcingWeight H (by linarith) s)
        (cubicThetaLongForcingWeight_low_two hH s)-cubicThetaForcingL2 s := by
  let A := cubicThetaRadialProfileSection (cubicThetaLongForcingWeight H (by linarith) s)
    (cubicThetaLongForcingWeight_low_one hH s)
  have hmA := cubicThetaCompactSection_memLp A (cubicThetaRadialProfileSection_compact _ _)
  have hmF := cubicThetaSectionRepresentative_memLp (cubicThetaForcingTest s)
  calc
    _ = (hmA.sub hmF).toLp _ := by
      apply MemLp.toLp_congr
      filter_upwards with q
      exact congrArg (fun F : CubicThetaSection => cubicThetaSectionRepresentative F q)
        (cubicThetaLongWindowDefectSection_eq H hH s)
    _ = _ := MemLp.toLp_sub hmA hmF

lemma cubicThetaLongWindow_coordinate_equation (H : ℝ) (hH : 2≤H) (s : ℂ)
    (p : ℂ × ℝ) (hp : 0<p.2) :
    cubicThetaCoordinateLaplacian (cubicThetaSectionFunction (cubicThetaLongWindowTest H hH s)) p=
      s*(s-2)*cubicThetaSectionFunction (cubicThetaLongWindowTest H hH s) p-
        cubicThetaSectionFunction (cubicThetaLongWindowDefectSection H hH s) p := by
  apply cubicThetaRadialProfile_coordinate_equation (p:=p) (hp:=hp)
  intro v hv
  have he := cubicThetaLongWindowHeight_equation (show 1≤H by linarith) s hv
  change cubicThetaRadialEuler (cubicThetaLongWindowHeight H s) v=
    s*(s-2)*cubicThetaLongWindowHeight H s v-
      (cubicThetaLongForcingWeight H _ s v-cubicThetaIncomingForcing s v)
  linear_combination he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeComplexIntegration
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complex integration on the actual cubed-prime cover and the
integrability of Hermitian products of square-integrable sections. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeComplexSheet_integrable {p : Eisenstein} (_hp : primaryPrime p)
    {f : CubicThetaPoint → ℂ}
    (hf : IntegrableOn f (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure)
    (t : cubicThetaPrimeCubeTransversal p) :
    IntegrableOn (fun x => f (t.val • x)) cubicThetaFundamentalDomain cubicThetaPointMeasure := by
  have hs := hf.mono_set (subset_iUnion (fun u : cubicThetaPrimeCubeTransversal p =>
    (fun x : CubicThetaPoint => u.val • x) '' cubicThetaFundamentalDomain) t)
  exact ((measurePreserving_smul t.val cubicThetaPointMeasure).integrableOn_image
    (measurableEmbedding_const_smul t.val)).mp hs

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeTracePairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal cubed-prime trace is adjoint to restriction for actual
square-integrable sections, with the exact unnormalized cover measure. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeTrace_pair_point {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p) (G : CubicThetaSection) (x : CubicThetaPoint) :
    star (G.val x)*(cubicThetaPrimeCubeTraceSection hp F).val x=
      ∑' t : cubicThetaPrimeCubeTransversal p,star (G.val (t.val • x))*F.val (t.val • x) := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  change star (G.val x)*(∑' t : cubicThetaPrimeCubeTransversal p,
    cubicThetaPrimeCubeTraceTerm p F t.val x)=_
  rw [tsum_fintype,tsum_fintype,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [G.property,star_mul,cubicThetaPrimeCubeTraceTerm]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeHeckePairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mass adjoint of the literal cubed-prime correspondence. All
integrals use the constructed arithmetic domains. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeAtkin_restrict_eq {p : Eisenstein} (hp : primaryPrime p)
    (G : CubicThetaSection) :
    cubicThetaPrimeCubeAtkinSection hp (cubicThetaPrimeCubeSectionRestrict G)=
      cubicThetaPrimeCubeDilationSection hp (cubicThetaInversionSection G) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change G.val (cubicThetaPrimeCubeAtkinMatrix hp • x)=
    G.val (cubicThetaFullInversion • (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x))
  exact congrArg G.val (mul_smul (β:=CubicThetaPoint) _ _ x)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPointC1Inversion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global inversion for the actual gradient pairing. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPointC1Inversion_covariance (F : cubicThetaPointC1)
    (hF : ∀ (g : cubicThetaPrincipalGroup) x,F.val (g • x)=cubicThetaKubotaValue g*F.val x)
    (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
    (cubicThetaPointC1Pullback (cubicThetaFullComplex cubicThetaFullInversion) F).val (g • x)=
      cubicThetaKubotaValue g*
        (cubicThetaPointC1Pullback (cubicThetaFullComplex cubicThetaFullInversion) F).val x := by
  change F.val (cubicThetaFullInversion • (g • x))=
    cubicThetaKubotaValue g*F.val (cubicThetaFullInversion • x)
  rw [cubicThetaInversion_intertwine,hF,cubicThetaInversionConjugate_character]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPointC1Hecke
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The C1 trace is the literal cubed-prime Hecke operator, and its
three geometric pullbacks have the required finite gradient integrals. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPointC1_atkin_dilation {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPointC1) :
    cubicThetaPointC1Pullback (cubicThetaPrimeCubeAtkinMatrix hp) F=
      cubicThetaPointC1Pullback (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))
        (cubicThetaPointC1Pullback (cubicThetaFullComplex cubicThetaFullInversion) F) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  exact congrArg F.val (mul_smul (β:=CubicThetaPoint) _ _ x)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeBranchFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonzero horizontal observations of the actual four Hecke branches. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaSectionFourier (F : CubicThetaSection) (v : ℝ) (hv : 0<v)
    (h : Eisenstein) : ℂ :=
  cubicThetaHorizontalFourierCoefficient h (cubicThetaSectionHorizontal F v hv)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeNormalizerCosets
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integral normalizers permute the actual finite cosets of the
cubed-prime trace. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrimeCubeNormalizerStep (p : Eisenstein) (δ : SL(2,Eisenstein))
    (t : cubicThetaPrimeCubeTransversal p) : cubicThetaPrimeCubeTransversal p :=
  ((cubicThetaPrimeCubeTransversal_complement p).equiv (cubicThetaPrincipalConjugate δ t.val)).snd

lemma cubicThetaPrimeCubeNormalizerStep_cancel (p : Eisenstein) (δ : SL(2,Eisenstein))
    (hδ : p^3∣δ.val 1 0) (t : cubicThetaPrimeCubeTransversal p) :
    cubicThetaPrimeCubeNormalizerStep p δ⁻¹ (cubicThetaPrimeCubeNormalizerStep p δ t)=t := by
  let C := cubicThetaPrimeCubeTransversal_complement p
  let a := C.equiv (cubicThetaPrincipalConjugate δ t.val)
  have he : a.fst.val*a.snd.val=cubicThetaPrincipalConjugate δ t.val := C.equiv_fst_mul_equiv_snd _
  have hi : p^3∣(δ⁻¹).val 1 0 := by
    simpa [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two] using dvd_neg.mpr hδ
  let h : cubicThetaPrimeIwahori (p^3) :=
    ⟨cubicThetaPrincipalConjugate δ⁻¹ a.fst.val,
      cubicThetaPrimeIwahori_integral_conjugate (p^3) δ⁻¹ hi a.fst⟩
  have hm : h.val*cubicThetaPrincipalConjugate δ⁻¹ a.snd.val=t.val := by
    apply Subtype.ext
    have he' := congrArg (fun g : cubicThetaPrincipalGroup => g.val) he
    change ((δ⁻¹)⁻¹*a.fst.val.val*δ⁻¹)*((δ⁻¹)⁻¹*a.snd.val.val*δ⁻¹)=t.val.val
    rw [inv_inv]
    change a.fst.val.val*a.snd.val.val=δ⁻¹*t.val.val*δ at he'
    calc
      _ = δ*(a.fst.val.val*a.snd.val.val)*δ⁻¹ := by group
      _ = _ := by rw [he']; group
  have hx : cubicThetaPrincipalConjugate δ⁻¹ a.snd.val=h.val⁻¹*t.val :=
    (eq_inv_mul_iff_mul_eq).mpr hm
  change (C.equiv (cubicThetaPrincipalConjugate δ⁻¹ a.snd.val)).snd=t
  rw [hx]
  change (C.equiv ((h⁻¹).val*t.val)).snd=t
  rw [C.equiv_mul_left]
  exact C.equiv_snd_eq_self_of_mem_of_one_mem (cubicThetaPrimeIwahori (p^3)).one_mem t.property

def cubicThetaPrimeCubeNormalizerPermutation (p : Eisenstein) (δ : SL(2,Eisenstein))
    (hδ : p^3∣δ.val 1 0) : cubicThetaPrimeCubeTransversal p ≃ cubicThetaPrimeCubeTransversal p where
  toFun := cubicThetaPrimeCubeNormalizerStep p δ
  invFun := cubicThetaPrimeCubeNormalizerStep p δ⁻¹
  left_inv := cubicThetaPrimeCubeNormalizerStep_cancel p δ hδ
  right_inv t := by
    have hi : p^3∣(δ⁻¹).val 1 0 := by
      simpa [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two] using dvd_neg.mpr hδ
    simpa only [inv_inv] using cubicThetaPrimeCubeNormalizerStep_cancel p δ⁻¹ hi t

lemma cubicThetaPrimeCubeTrace_normalizer {p : Eisenstein} (hp : primaryPrime p)
    (δ : SL(2,Eisenstein)) (hδ : p^3∣δ.val 1 0)
    (F : cubicThetaPrimeCubeSections p) (x : CubicThetaPoint) :
    (∑' t : cubicThetaPrimeCubeTransversal p,
      cubicThetaPrimeCubeTraceTerm p F (cubicThetaPrincipalConjugate δ t.val) x)=
      (cubicThetaPrimeCubeTraceSection hp F).val x := by
  have ht (t : cubicThetaPrimeCubeTransversal p) :
      cubicThetaPrimeCubeTraceTerm p F (cubicThetaPrincipalConjugate δ t.val) x=
      cubicThetaPrimeCubeTraceTerm p F (cubicThetaPrimeCubeNormalizerPermutation p δ hδ t).val x := by
    rw [←(cubicThetaPrimeCubeTransversal_complement p).equiv_fst_mul_equiv_snd
      (cubicThetaPrincipalConjugate δ t.val),cubicThetaPrimeCubeTraceTerm_left]
    rfl
  simp_rw [ht]
  exact (cubicThetaPrimeCubeNormalizerPermutation p δ hδ).tsum_eq
    (fun t => cubicThetaPrimeCubeTraceTerm p F t.val x)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeReciprocalGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reciprocal geometry and multiplier identities for the literal
cubed-prime correspondence. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeCube_inversion_dilation {p : Eisenstein} (hp : primaryPrime p)
    (x : CubicThetaPoint) :
    cubicThetaFullInversion • (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x)=
      (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))⁻¹ • (cubicThetaFullInversion • x) := by
  have he : cubicThetaFullComplex cubicThetaFullInversion*
      cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)=
      (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))⁻¹*
        cubicThetaFullComplex cubicThetaFullInversion := by
    rw [cubicThetaFullInversion_complex]
    apply Subtype.ext
    change (cubicThetaInversionMatrix 1 one_ne_zero : Matrix (Fin 2) (Fin 2) ℂ)*
      (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) : Matrix (Fin 2) (Fin 2) ℂ)=
      Matrix.adjugate (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) : Matrix (Fin 2) (Fin 2) ℂ)*
        (cubicThetaInversionMatrix 1 one_ne_zero : Matrix (Fin 2) (Fin 2) ℂ)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cubicThetaInversionMatrix,cubicThetaPrimeDilation,Matrix.adjugate_fin_two,
        Matrix.mul_apply,Fin.sum_univ_two]

  change cubicThetaFullComplex cubicThetaFullInversion •
    (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x)=_
  rw [←mul_smul,he,mul_smul]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootWeyl
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual opposite-root involution at modulus p cubed. Both
integral conjugations preserve the original cubic automorphy factor. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootWeylRaw_matrix {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) :
    ((cubicThetaPrimeCubeAtkinConjugate hp (cubicThetaPrimeCubeRootDilationIwahori hp g)).val.val :
      Matrix (Fin 2) (Fin 2) Eisenstein)=
      !![g.val.val 1 1,-(g.val.val 1 0/(p^3)^2);-(p^3)^2*g.val.val 0 1,g.val.val 0 0] := by
  have he := cubicThetaPrimeCubeAtkinConjugate_matrix hp (cubicThetaPrimeCubeRootDilationIwahori hp g)
  rw [cubicThetaPrimeCubeRootDilationIwahori_entry00,
    cubicThetaPrimeCubeRootDilationIwahori_entry01,
    cubicThetaPrimeCubeRootDilationIwahori_entry10,
    cubicThetaPrimeCubeRootDilationIwahori_entry11] at he
  rw [he,cubicThetaPrimeCubeRoot_lower_single_division hp g,
    mul_div_cancel_left₀ _ (pow_ne_zero 3 hp.2.ne_zero)]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [pow_two,mul_assoc]

def cubicThetaPrimeCubeRootWeylConjugate {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) : cubicThetaPrimeCubeRootSubgroup p :=
  ⟨(cubicThetaPrimeCubeAtkinConjugate hp (cubicThetaPrimeCubeRootDilationIwahori hp g)).val,by
    change (p^3)^2∣(cubicThetaPrimeCubeAtkinConjugate hp
      (cubicThetaPrimeCubeRootDilationIwahori hp g)).val.val 1 0 ∧
      p^3∣(cubicThetaPrimeCubeAtkinConjugate hp
      (cubicThetaPrimeCubeRootDilationIwahori hp g)).val.val 0 0-
      (cubicThetaPrimeCubeAtkinConjugate hp (cubicThetaPrimeCubeRootDilationIwahori hp g)).val.val 1 1
    rw [cubicThetaPrimeCubeRootWeylRaw_matrix]
    constructor
    · exact ⟨-g.val.val 0 1,by simp⟩
    · simpa only [Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,neg_sub]
        using dvd_neg.mpr g.property.2⟩

lemma cubicThetaPrimeCubeRootWeylConjugate_matrix {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) :
    ((cubicThetaPrimeCubeRootWeylConjugate hp g).val.val : Matrix (Fin 2) (Fin 2) Eisenstein)=
      !![g.val.val 1 1,-(g.val.val 1 0/(p^3)^2);-(p^3)^2*g.val.val 0 1,g.val.val 0 0] :=
  cubicThetaPrimeCubeRootWeylRaw_matrix hp g

lemma cubicThetaPrimeCubeRootWeyl_kubota {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) :
    cubicThetaKubotaValue (cubicThetaPrimeCubeRootWeylConjugate hp g).val=cubicThetaKubotaValue g.val := by
  exact (cubicThetaPrimeCubeAtkinConjugate_kubota hp _).trans
    (cubicThetaPrimeCubeConjugate_kubota hp (cubicThetaPrimeCubeRootIwahori g)).symm

def cubicThetaPrimeCubeRootWeylElement {p : Eisenstein} (hp : primaryPrime p) : SL(2,ℂ) :=
  cubicThetaPrimeCubeAtkinMatrix hp*cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)

theorem cubicThetaPrimeCubeRootWeyl_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) :
    cubicThetaPrimeCubeRootWeylElement hp*cubicThetaPrincipalComplex g.val=
      cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootWeylConjugate hp g).val*
        cubicThetaPrimeCubeRootWeylElement hp := by
  have hD : cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)*cubicThetaPrincipalComplex g.val=
      cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootDilationIwahori hp g).val*
        cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) :=
    cubicThetaPrimeDilation_intertwines (cubicThetaPrimeCube_primary hp) (cubicThetaPrimeCubeRootIwahori g)
  have hW : cubicThetaPrimeCubeAtkinMatrix hp*
      cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootDilationIwahori hp g).val=
      cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootWeylConjugate hp g).val*cubicThetaPrimeCubeAtkinMatrix hp :=
    cubicThetaPrimeCubeAtkinMatrix_intertwines hp (cubicThetaPrimeCubeRootDilationIwahori hp g)
  unfold cubicThetaPrimeCubeRootWeylElement
  rw [mul_assoc,hD,←mul_assoc,hW,mul_assoc]

lemma cubicThetaPrimeCubeRootWeylElement_inversion {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeRootWeylElement hp=cubicThetaInversionMatrix ((p^3:Eisenstein):ℂ)
      (fun he => (pow_ne_zero 3 hp.2.ne_zero) (Subtype.ext he)) := by
  rw [cubicThetaPrimeCubeRootWeylElement,cubicThetaPrimeCubeAtkinMatrix,cubicThetaFullInversion_complex]
  apply Subtype.ext
  change ((cubicThetaInversionMatrix 1 one_ne_zero:Matrix (Fin 2) (Fin 2) ℂ)*
    (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero):Matrix (Fin 2) (Fin 2) ℂ))*
      (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero):Matrix (Fin 2) (Fin 2) ℂ)=_
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicThetaInversionMatrix,cubicThetaPrimeDilation,Matrix.mul_apply,Fin.sum_univ_two,
      ←pow_two,cubicThetaPrimeSquareRoot_sq]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootBruhat
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal integral Bruhat identity for unit translations modulo p cubed. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment


theorem cubicThetaPrimeCubeRootBruhat_identity {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) :
    cubicThetaPrimeCubeRootElement hp y*cubicThetaPrimeCubeRootWeylElement hp*cubicThetaPrimeCubeRootElement hp x=
      cubicThetaFullComplex cubicThetaFullInversion*
        cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootBruhat hp x y hxy) := by
  have hpC : ((p^3:Eisenstein):ℂ)≠0 := fun he => (pow_ne_zero 3 hp.2.ne_zero) (Subtype.ext he)
  have hp1C : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  have hthree : ((3:Eisenstein):ℂ)=3 := rfl
  have hd : (((1-9*x*y)/p^3:Eisenstein):ℂ)=(1-9*(x:ℂ)*(y:ℂ))/((p^3:Eisenstein):ℂ) := by
    apply (eq_div_iff hpC).mpr
    calc
      _ = ((p^3:Eisenstein):ℂ)*(((1-9*x*y)/p^3:Eisenstein):ℂ) := mul_comm _ _
      _ = ((1-9*x*y:Eisenstein):ℂ) := congrArg Subtype.val (cubicThetaPrimeCubeRootBruhat_division hp x y hxy)
      _ = _ := by push_cast; rfl
  rw [cubicThetaPrimeCubeRootElement_translation,cubicThetaPrimeCubeRootElement_translation,
    cubicThetaPrimeCubeRootWeylElement_inversion,cubicThetaFullInversion_complex]
  apply Subtype.ext
  change ((cubicThetaTranslationMatrix (((3*y:Eisenstein):ℂ)/((p^3:Eisenstein):ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*
    (cubicThetaInversionMatrix ((p^3:Eisenstein):ℂ) hpC:Matrix (Fin 2) (Fin 2) ℂ))*
      (cubicThetaTranslationMatrix (((3*x:Eisenstein):ℂ)/((p^3:Eisenstein):ℂ)):Matrix (Fin 2) (Fin 2) ℂ)=
        (cubicThetaInversionMatrix 1 one_ne_zero:Matrix (Fin 2) (Fin 2) ℂ)*
          (cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootBruhat hp x y hxy):Matrix (Fin 2) (Fin 2) ℂ)
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicThetaTranslationMatrix,cubicThetaInversionMatrix,cubicThetaPrincipalComplex_apply,
      cubicThetaPrimeCubeRootBruhat,cubicThetaPrimeCubeRootBruhatMatrix,Matrix.mul_apply,Fin.sum_univ_two,hd]
  all_goals field_simp [hp1C]
  all_goals try rw [hthree]
  all_goals ring

theorem cubicThetaPrimeCubeRootBruhat_section {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) (F : CubicThetaSection) (z : CubicThetaPoint) :
    F.val (cubicThetaPrimeCubeRootElement hp y •
      (cubicThetaPrimeCubeRootWeylElement hp • (cubicThetaPrimeCubeRootElement hp x • z)))=
      cubicSymbol (p^3) (3*y)*(cubicThetaInversionSection F).val z := by
  rw [←mul_smul,←mul_smul,cubicThetaPrimeCubeRootBruhat_identity hp x y hxy,mul_smul]
  change (cubicThetaInversionSection F).val
    (cubicThetaPrimeCubeRootBruhat hp x y hxy • z)=_
  rw [(cubicThetaInversionSection F).property,cubicThetaPrimeCubeRootBruhat_kubota]


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootCoverDomain
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable fundamental domain for the fractional-root cover, obtained from
finitely many translates of the original proved fundamental domain. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeRootCoverDomain_measurable {p : Eisenstein} (hp : primaryPrime p) :
    MeasurableSet (cubicThetaPrimeRootCoverDomain hp) := by
  apply MeasurableSet.iUnion
  intro t
  exact (Homeomorph.smul t.val).measurableEmbedding.measurableSet_image'
    cubicThetaFundamentalDomain_measurable

theorem cubicThetaPrimeRootCoverDomain_unique {p : Eisenstein} (hp : primaryPrime p)
    (x : CubicThetaPoint) :
    ∃! g : cubicThetaPrimeRootCoverGroup hp, g • x∈cubicThetaPrimeRootCoverDomain hp := by
  obtain ⟨a,ha,hua⟩ := cubicThetaFundamentalDomain_unique x
  obtain ⟨⟨h,t⟩,he,hunique⟩ := (cubicThetaPrimeRootTransversal_complement hp).existsUnique a⁻¹
  have hmove : (h.val)⁻¹=t.val*a := by
    calc
      _ = h.val⁻¹*(a⁻¹*a) := by simp
      _ = h.val⁻¹*((h.val*t.val)*a) := by rw [he]
      _ = _ := by group
  refine ⟨h⁻¹,?_,?_⟩
  · apply mem_iUnion.mpr
    refine ⟨t,a • x,ha,?_⟩
    change t.val • (a • x)=h.val⁻¹ • x
    rw [←mul_smul,hmove]
  · intro k hk
    obtain ⟨u,hu⟩ := mem_iUnion.mp hk
    obtain ⟨y,hy,hky⟩ := hu
    have hya : u.val⁻¹*k.val=a := by
      apply hua
      rw [mul_smul]
      change u.val⁻¹ • (k • x)∈cubicThetaFundamentalDomain
      rw [←hky,inv_smul_smul]
      exact hy
    have hpair : ((k⁻¹,u) : cubicThetaPrimeRootCoverGroup hp × cubicThetaPrimeRootTransversal hp)=(h,t) := by
      apply hunique
      change k.val⁻¹*u.val=a⁻¹
      rw [←hya]
      group
    have hh : k⁻¹=h := congrArg Prod.fst hpair
    simpa only [inv_inv] using congrArg Inv.inv hh

theorem cubicThetaPrimeRootCoverDomain_isFundamentalDomain {p : Eisenstein}
    (hp : primaryPrime p) (μ : Measure CubicThetaPoint) :
    IsFundamentalDomain (cubicThetaPrimeRootCoverGroup hp) (cubicThetaPrimeRootCoverDomain hp) μ :=
  IsFundamentalDomain.mk' (cubicThetaPrimeRootCoverDomain_measurable hp).nullMeasurableSet
    (cubicThetaPrimeRootCoverDomain_unique hp)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootCoverMeasure
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independence of the fractional-root cover measure from the finite translated
fundamental domain used in its construction. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

instance cubicThetaPrimeRootCoverPointMeasure_invariant {p : Eisenstein} (hp : primaryPrime p) :
    SMulInvariantMeasure (cubicThetaPrimeRootCoverGroup hp) CubicThetaPoint cubicThetaPointMeasure where
  measure_preimage_smul g _S hS :=
    SMulInvariantMeasure.measure_preimage_smul (g.val : cubicThetaPrincipalGroup) hS

theorem cubicThetaPrimeRootCoverMeasure_independent {p : Eisenstein} (hp : primaryPrime p)
    {D : Set CubicThetaPoint}
    (hD : IsFundamentalDomain (cubicThetaPrimeRootCoverGroup hp) D cubicThetaPointMeasure) :
    cubicThetaPrimeRootCoverMeasure hp=
      (cubicThetaPointMeasure.restrict D).map (cubicThetaPrimeRootCoverMap hp) := by
  ext S hS
  rw [cubicThetaPrimeRootCoverMeasure_apply hp hS,Measure.map_apply
    (cubicThetaPrimeRootCoverMap_open hp).continuous.measurable hS,
    Measure.restrict_apply (hS.preimage (cubicThetaPrimeRootCoverMap_open hp).continuous.measurable)]
  apply (cubicThetaPrimeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).measure_set_eq hD
    (hS.preimage (cubicThetaPrimeRootCoverMap_open hp).continuous.measurable)
  intro g
  ext x
  simp only [mem_preimage,(cubicThetaPrimeRootCover_covering hp).map_smul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootCoverTransport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual fractional roots preserve hyperbolic measure on their
finite arithmetic cover, by transport of the proved fundamental domain. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeRootImage_fundamental {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) :
    IsFundamentalDomain (cubicThetaPrimeRootCoverGroup hp)
      ((fun y : CubicThetaPoint => cubicThetaPrimeRootElement hp x • y) ''
        cubicThetaPrimeRootCoverDomain hp) cubicThetaPointMeasure := by
  apply (cubicThetaPrimeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).image_of_equiv
    (Homeomorph.smul (cubicThetaPrimeRootElement hp x)).toEquiv
    (measurePreserving_smul (cubicThetaPrimeRootElement hp x)⁻¹
      cubicThetaPointMeasure).quasiMeasurePreserving
    (cubicThetaPrimeRootAutomorphism hp (-x)).toEquiv
  intro g y
  change cubicThetaPrimeRootElement hp x • ((cubicThetaPrimeRootConjugate hp (-x) g).val • y)=
    g.val • (cubicThetaPrimeRootElement hp x • y)
  rw [cubicThetaPrimeRootPoint_intertwines,←cubicThetaPrimeRootConjugate_add,
    add_neg_cancel,cubicThetaPrimeRootConjugate_zero]

theorem cubicThetaPrimeRootCoverTranslate_measurePreserving {p : Eisenstein} (hp : primaryPrime p) (x : Eisenstein) :
    MeasurePreserving (cubicThetaPrimeRootCoverTranslate hp x)
      (cubicThetaPrimeRootCoverMeasure hp) (cubicThetaPrimeRootCoverMeasure hp) := by
  have hcont : Continuous (cubicThetaPrimeRootCoverTranslate hp x) :=
    (cubicThetaPrimeRootCoverHomeomorph hp x).continuous
  refine ⟨hcont.measurable,?_⟩
  calc
    _ = ((cubicThetaPointMeasure.restrict (cubicThetaPrimeRootCoverDomain hp)).map
        (fun y : CubicThetaPoint => cubicThetaPrimeRootElement hp x • y)).map
          (cubicThetaPrimeRootCoverMap hp) := by
      rw [cubicThetaPrimeRootCoverMeasure,
        Measure.map_map hcont.measurable
          (cubicThetaPrimeRootCoverMap_open hp).continuous.measurable,
        Measure.map_map (cubicThetaPrimeRootCoverMap_open hp).continuous.measurable
          (measurable_const_smul (cubicThetaPrimeRootElement hp x))]
      rfl
    _ = (cubicThetaPointMeasure.restrict
        ((fun y : CubicThetaPoint => cubicThetaPrimeRootElement hp x • y) ''
          cubicThetaPrimeRootCoverDomain hp)).map (cubicThetaPrimeRootCoverMap hp) := by
      rw [cubicThetaPrimeRoot_map_restrict hp x (cubicThetaPrimeRootCoverDomain_measurable hp)]
    _ = cubicThetaPrimeRootCoverMeasure hp :=
      (cubicThetaPrimeRootCoverMeasure_independent hp (cubicThetaPrimeRootImage_fundamental hp x)).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootSectionNorm
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The norm of a section on the finite root cover is a genuine
continuous quotient function. The fractional-root pullback preserves its exact mass. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaPrimeRootSectionTranslate_mass {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaPrimeRootSections p) :
    (∫ q, (cubicThetaPrimeRootSectionNorm hp (cubicThetaPrimeRootSectionTranslate hp x F) q)^2
      ∂cubicThetaPrimeRootCoverMeasure hp)=
    ∫ q, (cubicThetaPrimeRootSectionNorm hp F q)^2 ∂cubicThetaPrimeRootCoverMeasure hp := by
  simp_rw [cubicThetaPrimeRootSectionTranslate_norm]
  exact (cubicThetaPrimeRootCoverTranslate_measurePreserving hp x).integral_comp
    (cubicThetaPrimeRootCoverHomeomorph hp x).measurableEmbedding
    (fun q => (cubicThetaPrimeRootSectionNorm hp F q)^2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootHorizontal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual root average selects exactly the Fourier frequencies
divisible by the prime, on every positive-height horizontal slice. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaPrimeRootHorizontal_periodic {p : Eisenstein}
    (F : cubicThetaPrimeRootSections p) (v : ℝ) (hv : 0<v) (w : Eisenstein) (z : ℂ) :
    cubicThetaPrimeRootHorizontal F v hv (z+3*(w:ℂ))=cubicThetaPrimeRootHorizontal F v hv z := by
  have he : cubicThetaHorizontalPoint v hv (z+3*(w:ℂ))=
      cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation w) • cubicThetaHorizontalPoint v hv z := by
    apply Subtype.ext
    change (z+3*(w:ℂ),v)=cubicThetaMobius
      (cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation w)) (z,v)
    rw [cubicThetaPrincipalTranslation_complex,cubicThetaMobius_translation]
    push_cast
    rfl
  change F.val (cubicThetaHorizontalPoint v hv (z+3*(w:ℂ)))=_
  rw [he,cubicThetaPrimeRootSection_integral]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootWeyl
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The second root direction is supplied by the actual conjugated
inversion. Its integral conjugation preserves the same cubic multiplier. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

theorem cubicThetaPrimeRootWeyl_kubota {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeRootSubgroup p) :
    cubicThetaKubotaValue (cubicThetaPrimeRootWeylConjugate hp g).val=cubicThetaKubotaValue g.val := by
  let k : cubicThetaPrimeCharacterKernel hp :=
    ⟨cubicThetaPrimeRootDilationIwahori hp g,by
      change cubicSymbol p (g.val.val 0 0)=1
      exact cubicThetaPrimeRoot_diagonal_character hp g⟩
  change cubicThetaKubotaValue (cubicThetaPrimeAtkinKernel hp k).val.val=_
  exact (cubicThetaPrimeAtkinKernel_kubota hp k).trans (cubicThetaPrimeRootDilation_kubota hp g)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootWeylInvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Involutivity of the actual conjugated inversion, on both the
arithmetic root subgroup and positive-height points. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeRootWeylElement_inversion {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeRootWeylElement hp=cubicThetaInversionMatrix (p:ℂ)
      (fun he => hp.2.ne_zero (Subtype.ext he)) := by
  rw [cubicThetaPrimeRootWeylElement,cubicThetaPrimeAtkinMatrix,cubicThetaFullInversion_complex]
  apply Subtype.ext
  change ((cubicThetaInversionMatrix 1 one_ne_zero:Matrix (Fin 2) (Fin 2) ℂ)*
    (cubicThetaPrimeDilation hp.2.ne_zero:Matrix (Fin 2) (Fin 2) ℂ))*
      (cubicThetaPrimeDilation hp.2.ne_zero:Matrix (Fin 2) (Fin 2) ℂ)=_
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicThetaInversionMatrix,cubicThetaPrimeDilation,Matrix.mul_apply,Fin.sum_univ_two,
      ←pow_two,cubicThetaPrimeSquareRoot_sq]

lemma cubicThetaPrimeRootWeylPoint_involutive {p : Eisenstein} (hp : primaryPrime p)
    (y : CubicThetaPoint) :
    cubicThetaPrimeRootWeylElement hp • (cubicThetaPrimeRootWeylElement hp • y)=y := by
  apply Subtype.ext
  change cubicThetaMobius (cubicThetaPrimeRootWeylElement hp)
    (cubicThetaMobius (cubicThetaPrimeRootWeylElement hp) y.val)=y.val
  rw [cubicThetaPrimeRootWeylElement_inversion,
    cubicThetaMobius_inversion _ (cubicThetaMobius_height_pos _ y.property),
    cubicThetaMobius_inversion _ y.property]
  exact cubicThetaInversion_involutive (fun he => hp.2.ne_zero (Subtype.ext he)) y.property

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootWeylSections
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conjugated inversion is an involutive linear action on the
actual root-cover sections. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeRootWeylSection {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p) : cubicThetaPrimeRootSections p :=
  ⟨⟨fun y => F.val (cubicThetaPrimeRootWeylElement hp • y),
    F.val.continuous.comp (continuous_const_smul _)⟩,by
    intro g y
    change F.val (cubicThetaPrimeRootWeylElement hp • (g.val • y))=
      cubicThetaKubotaValue g.val*F.val (cubicThetaPrimeRootWeylElement hp • y)
    rw [cubicThetaPrimeRootWeylPoint_intertwines,F.property,cubicThetaPrimeRootWeyl_kubota]⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootWeylCover
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same conjugated inversion is a homeomorphism of the actual
finite arithmetic cover. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeRootCoverWeylHomeomorph {p : Eisenstein} (hp : primaryPrime p) :
    CubicThetaPrimeRootCover hp ≃ₜ CubicThetaPrimeRootCover hp where
  toFun := cubicThetaPrimeRootCoverWeyl hp
  invFun := cubicThetaPrimeRootCoverWeyl hp
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h y =>
      change cubicThetaPrimeRootCoverMap hp
        (cubicThetaPrimeRootWeylElement hp • (cubicThetaPrimeRootWeylElement hp • y))=
          cubicThetaPrimeRootCoverMap hp y
      rw [cubicThetaPrimeRootWeylPoint_involutive]
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h y =>
      change cubicThetaPrimeRootCoverMap hp
        (cubicThetaPrimeRootWeylElement hp • (cubicThetaPrimeRootWeylElement hp • y))=
          cubicThetaPrimeRootCoverMap hp y
      rw [cubicThetaPrimeRootWeylPoint_involutive]
  continuous_toFun := by
    apply (cubicThetaPrimeRootCoverMap_open hp).isQuotientMap.continuous_iff.mpr
    exact (cubicThetaPrimeRootCoverMap_open hp).continuous.comp
      (continuous_const_smul (cubicThetaPrimeRootWeylElement hp))
  continuous_invFun := by
    apply (cubicThetaPrimeRootCoverMap_open hp).isQuotientMap.continuous_iff.mpr
    exact (cubicThetaPrimeRootCoverMap_open hp).continuous.comp
      (continuous_const_smul (cubicThetaPrimeRootWeylElement hp))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootWeylMeasure
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual conjugated inversion preserves the root-cover measure
and the square norm of its sections. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeRootWeylImage_fundamental {p : Eisenstein} (hp : primaryPrime p) :
    IsFundamentalDomain (cubicThetaPrimeRootCoverGroup hp)
      ((fun y : CubicThetaPoint => cubicThetaPrimeRootWeylElement hp • y) ''
        cubicThetaPrimeRootCoverDomain hp) cubicThetaPointMeasure := by
  apply (cubicThetaPrimeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).image_of_equiv
    (Homeomorph.smul (cubicThetaPrimeRootWeylElement hp)).toEquiv
    (measurePreserving_smul (cubicThetaPrimeRootWeylElement hp)⁻¹
      cubicThetaPointMeasure).quasiMeasurePreserving
    (cubicThetaPrimeRootWeylConjugate_involutive hp).toPerm
  intro g y
  change cubicThetaPrimeRootWeylElement hp • ((cubicThetaPrimeRootWeylConjugate hp g).val • y)=
    g.val • (cubicThetaPrimeRootWeylElement hp • y)
  rw [cubicThetaPrimeRootWeylPoint_intertwines,cubicThetaPrimeRootWeylConjugate_involutive]

theorem cubicThetaPrimeRootCoverWeyl_measurePreserving {p : Eisenstein} (hp : primaryPrime p) :
    MeasurePreserving (cubicThetaPrimeRootCoverWeyl hp)
      (cubicThetaPrimeRootCoverMeasure hp) (cubicThetaPrimeRootCoverMeasure hp) := by
  have hcont : Continuous (cubicThetaPrimeRootCoverWeyl hp) :=
    (cubicThetaPrimeRootCoverWeylHomeomorph hp).continuous
  refine ⟨hcont.measurable,?_⟩
  calc
    _ = ((cubicThetaPointMeasure.restrict (cubicThetaPrimeRootCoverDomain hp)).map
        (fun y : CubicThetaPoint => cubicThetaPrimeRootWeylElement hp • y)).map
          (cubicThetaPrimeRootCoverMap hp) := by
      rw [cubicThetaPrimeRootCoverMeasure,
        Measure.map_map hcont.measurable (cubicThetaPrimeRootCoverMap_open hp).continuous.measurable,
        Measure.map_map (cubicThetaPrimeRootCoverMap_open hp).continuous.measurable
          (measurable_const_smul (cubicThetaPrimeRootWeylElement hp))]
      rfl
    _ = (cubicThetaPointMeasure.restrict
        ((fun y : CubicThetaPoint => cubicThetaPrimeRootWeylElement hp • y) ''
          cubicThetaPrimeRootCoverDomain hp)).map (cubicThetaPrimeRootCoverMap hp) := by
      rw [cubicThetaPrimeRootWeyl_map_restrict hp (cubicThetaPrimeRootCoverDomain_measurable hp)]
    _ = cubicThetaPrimeRootCoverMeasure hp :=
      (cubicThetaPrimeRootCoverMeasure_independent hp (cubicThetaPrimeRootWeylImage_fundamental hp)).symm

lemma cubicThetaPrimeRootWeylSection_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p) (q : CubicThetaPrimeRootCover hp) :
    cubicThetaPrimeRootSectionNorm hp (cubicThetaPrimeRootWeylSection hp F) q=
      cubicThetaPrimeRootSectionNorm hp F (cubicThetaPrimeRootCoverWeyl hp q) := by
  induction q using Quotient.inductionOn with
  | h y => rfl

theorem cubicThetaPrimeRootWeylSection_mass {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p) :
    (∫ q, (cubicThetaPrimeRootSectionNorm hp (cubicThetaPrimeRootWeylSection hp F) q)^2
      ∂cubicThetaPrimeRootCoverMeasure hp)=
      ∫ q, (cubicThetaPrimeRootSectionNorm hp F q)^2 ∂cubicThetaPrimeRootCoverMeasure hp := by
  simp_rw [cubicThetaPrimeRootWeylSection_norm]
  exact (cubicThetaPrimeRootCoverWeyl_measurePreserving hp).integral_comp
    (cubicThetaPrimeRootCoverWeylHomeomorph hp).measurableEmbedding
    (fun q => (cubicThetaPrimeRootSectionNorm hp F q)^2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootBruhat
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal finite-root Bruhat relation, in the original complex
hyperbolic action and with its cubic automorphy factor. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

theorem cubicThetaPrimeRootBruhat_identity {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p∣9*x*y-1) :
    cubicThetaPrimeRootElement hp y*cubicThetaPrimeRootWeylElement hp*cubicThetaPrimeRootElement hp x=
      cubicThetaFullComplex cubicThetaFullInversion*
        cubicThetaPrincipalComplex (cubicThetaPrimeRootBruhat hp x y hxy) := by
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  have hthree : ((3:Eisenstein):ℂ)=3 := rfl
  have hd : (((1-9*x*y)/p:Eisenstein):ℂ)=(1-9*(x:ℂ)*(y:ℂ))/(p:ℂ) := by
    apply (eq_div_iff hpC).mpr
    calc
      _ = (p:ℂ)*(((1-9*x*y)/p:Eisenstein):ℂ) := mul_comm _ _
      _ = ((1-9*x*y:Eisenstein):ℂ) := congrArg Subtype.val (cubicThetaPrimeRootBruhat_division hp x y hxy)
      _ = _ := by push_cast; rfl
  rw [cubicThetaPrimeRootElement_translation,cubicThetaPrimeRootElement_translation,
    cubicThetaPrimeRootWeylElement_inversion,cubicThetaFullInversion_complex]
  apply Subtype.ext
  change ((cubicThetaTranslationMatrix (((3*y:Eisenstein):ℂ)/(p:ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*
    (cubicThetaInversionMatrix (p:ℂ) hpC:Matrix (Fin 2) (Fin 2) ℂ))*
      (cubicThetaTranslationMatrix (((3*x:Eisenstein):ℂ)/(p:ℂ)):Matrix (Fin 2) (Fin 2) ℂ)=
        (cubicThetaInversionMatrix 1 one_ne_zero:Matrix (Fin 2) (Fin 2) ℂ)*
          (cubicThetaPrincipalComplex (cubicThetaPrimeRootBruhat hp x y hxy):Matrix (Fin 2) (Fin 2) ℂ)
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicThetaTranslationMatrix,cubicThetaInversionMatrix,cubicThetaPrincipalComplex_apply,
      cubicThetaPrimeRootBruhat,cubicThetaPrimeRootBruhatMatrix,Matrix.mul_apply,Fin.sum_univ_two,hd]
  all_goals field_simp
  all_goals simp only [hthree]
  all_goals ring

theorem cubicThetaPrimeRootBruhat_section {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p∣9*x*y-1) (F : CubicThetaSection) (z : CubicThetaPoint) :
    F.val (cubicThetaPrimeRootElement hp y •
      (cubicThetaPrimeRootWeylElement hp • (cubicThetaPrimeRootElement hp x • z)))=
      cubicSymbol p (3*y)*(cubicThetaInversionSection F).val z := by
  rw [←mul_smul,←mul_smul,cubicThetaPrimeRootBruhat_identity hp x y hxy,mul_smul]
  change (cubicThetaInversionSection F).val
    (cubicThetaPrimeRootBruhat hp x y hxy • z)=_
  rw [(cubicThetaInversionSection F).property,cubicThetaPrimeRootBruhat_kubota]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootBruhatOperators
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonzero Bruhat branches act on actual global sections by the
reciprocal root parameter and its cubic symbol. The zero branch retains
the literal squared-prime dilation. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeRootWeyl_translated_global {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p∣9*x*y-1) (F : CubicThetaSection) :
    cubicThetaPrimeRootWeylSection hp
      (cubicThetaPrimeRootSectionTranslate hp y (cubicThetaPrimeRootSectionRestrict F))=
      cubicSymbol p (3*y) • cubicThetaPrimeRootSectionTranslate hp (-x)
        (cubicThetaPrimeRootSectionRestrict (cubicThetaInversionSection F)) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  change F.val (cubicThetaPrimeRootElement hp y • (cubicThetaPrimeRootWeylElement hp • z))=
    cubicSymbol p (3*y)*(cubicThetaInversionSection F).val (cubicThetaPrimeRootElement hp (-x) • z)
  have he := cubicThetaPrimeRootBruhat_section hp x y hxy F (cubicThetaPrimeRootElement hp (-x) • z)
  have hx : cubicThetaPrimeRootElement hp x • (cubicThetaPrimeRootElement hp (-x) • z)=z := by
    rw [←mul_smul,←cubicThetaPrimeRootElement_add,add_neg_cancel,cubicThetaPrimeRootElement_zero,one_smul]
  rw [hx] at he
  exact he

theorem cubicThetaPrimeRootWeyl_global_zero {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (z : CubicThetaPoint) :
    (cubicThetaPrimeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F)).val z=
      (cubicThetaInversionSection F).val
        (cubicThetaPrimeDilation hp.2.ne_zero • (cubicThetaPrimeDilation hp.2.ne_zero • z)) := by
  change F.val (cubicThetaPrimeRootWeylElement hp • z)=_
  rw [cubicThetaPrimeRootWeylElement,cubicThetaPrimeAtkinMatrix,mul_smul,mul_smul]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootBruhatResidues
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choice-independent nonzero Bruhat branches, indexed by the actual
prime residue units. The cubic multiplier is the original residue character. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeRootWeyl_residue_branch {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) (hr : IsUnit r) (F : CubicThetaSection) :
    cubicThetaPrimeRootWeylSection hp
      (cubicThetaPrimeRootResidueOperator hp r (cubicThetaPrimeRootSectionRestrict F))=
      (cubicSymbol p 3*cubicResidueChar p hp r) •
        cubicThetaPrimeRootResidueOperator hp (-cubicThetaPrimeRootReciprocal p r)
          (cubicThetaPrimeRootSectionRestrict (cubicThetaInversionSection F)) := by
  let x := residueRepresentative p (cubicThetaPrimeRootReciprocal p r)
  have hx : Ideal.Quotient.mk (modulus p) (-x)= -cubicThetaPrimeRootReciprocal p r := by
    rw [map_neg]
    exact congrArg Neg.neg (residueRepresentative_spec p _)
  rw [←hx,cubicThetaPrimeRootResidueOperator_mk]
  change cubicThetaPrimeRootWeylSection hp
    (cubicThetaPrimeRootSectionTranslate hp (residueRepresentative p r) (cubicThetaPrimeRootSectionRestrict F))=
      (cubicSymbol p 3*cubicResidueChar p hp r) • cubicThetaPrimeRootSectionTranslate hp (-x)
        (cubicThetaPrimeRootSectionRestrict (cubicThetaInversionSection F))
  rw [←cubicThetaPrimeRootBruhat_residue_character hp r]
  exact cubicThetaPrimeRootWeyl_translated_global hp x (residueRepresentative p r)
    (cubicThetaPrimeRootReciprocal_pair hp r hr) F

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootBruhatPhase
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubic-scale unit branch has trivial multiplier. This is a
consequence of the elementary cubic character, not a residue hypothesis. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeRootBruhat_section_one {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) (F : CubicThetaSection) (z : CubicThetaPoint) :
    F.val (cubicThetaPrimeCubeRootElement hp y •
      (cubicThetaPrimeCubeRootWeylElement hp • (cubicThetaPrimeCubeRootElement hp x • z)))=
      (cubicThetaInversionSection F).val z := by
  rw [cubicThetaPrimeCubeRootBruhat_section hp x y hxy F z,
    cubicThetaPrimeCubeRootBruhat_phase hp x y hxy,one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootWeylSections
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Involutive action of the opposite cubic root on actual sections. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeRootWeylConjugate_involutive {p : Eisenstein} (hp : primaryPrime p) :
    Function.Involutive (cubicThetaPrimeCubeRootWeylConjugate hp) := by
  intro g
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [cubicThetaPrimeCubeRootWeylConjugate_matrix]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 1 1)
      (cubicThetaPrimeCubeRootWeylConjugate_matrix hp g)
  · have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 1 0)
      (cubicThetaPrimeCubeRootWeylConjugate_matrix hp g)
    simp at he ⊢
    rw [he,show -((p^3)^2*g.val.val 0 1)=(p^3)^2*(-g.val.val 0 1) by ring,
      mul_div_cancel_left₀ _ (pow_ne_zero 2 (pow_ne_zero 3 hp.2.ne_zero)),neg_neg]
  · have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 0 1)
      (cubicThetaPrimeCubeRootWeylConjugate_matrix hp g)
    simp at he ⊢
    rw [he]
    linear_combination cubicThetaPrimeCubeRoot_lower_division hp g
  · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 0 0)
      (cubicThetaPrimeCubeRootWeylConjugate_matrix hp g)

lemma cubicThetaPrimeCubeRootWeylPoint_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeCubeRootSubgroup p) (y : CubicThetaPoint) :
    cubicThetaPrimeCubeRootWeylElement hp • (g.val • y)=
      (cubicThetaPrimeCubeRootWeylConjugate hp g).val • (cubicThetaPrimeCubeRootWeylElement hp • y) := by
  change cubicThetaPrimeCubeRootWeylElement hp • (cubicThetaPrincipalComplex g.val • y)=
    cubicThetaPrincipalComplex (cubicThetaPrimeCubeRootWeylConjugate hp g).val •
      (cubicThetaPrimeCubeRootWeylElement hp • y)
  rw [←mul_smul,←mul_smul,cubicThetaPrimeCubeRootWeyl_intertwines]


def cubicThetaPrimeCubeRootWeylSection {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootSections p) : cubicThetaPrimeCubeRootSections p :=
  ⟨⟨fun y => F.val (cubicThetaPrimeCubeRootWeylElement hp • y),
    F.val.continuous.comp (continuous_const_smul _)⟩,by
    intro g y
    change F.val (cubicThetaPrimeCubeRootWeylElement hp • (g.val • y))=
      cubicThetaKubotaValue g.val*F.val (cubicThetaPrimeCubeRootWeylElement hp • y)
    rw [cubicThetaPrimeCubeRootWeylPoint_intertwines,F.property,cubicThetaPrimeCubeRootWeyl_kubota]⟩


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootWeylGlobal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual twice-cubically-dilated global branch and its invariance
under all cubic-scale translations. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeRootWeyl_global_zero {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (z : CubicThetaPoint) :
    (cubicThetaPrimeCubeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F)).val z=
      (cubicThetaInversionSection F).val
        (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • z)) := by
  change F.val (cubicThetaPrimeCubeRootWeylElement hp • z)=_
  rw [cubicThetaPrimeCubeRootWeylElement,cubicThetaPrimeCubeAtkinMatrix,mul_smul,mul_smul]
  rfl

lemma cubicThetaPrimeCubeRootWeyl_global_translate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : CubicThetaSection) :
    cubicThetaPrimeCubeRootSectionTranslate hp x
      (cubicThetaPrimeCubeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F))=
        cubicThetaPrimeCubeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F) := by
  let D := cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)
  let t := cubicThetaPrincipalTranslation x
  let g : cubicThetaPrimeIwahori (p^3) := ⟨t,by change p^3∣0; exact dvd_zero (p^3)⟩
  have h1 : D*cubicThetaPrimeCubeRootElement hp x=cubicThetaPrincipalComplex t*D := by
    dsimp only [D,t,cubicThetaPrimeCubeRootElement]
    group
  have h2 : D*cubicThetaPrincipalComplex t=
      cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g)*D :=
    cubicThetaPrimeDilation_intertwines (cubicThetaPrimeCube_primary hp) g
  have h3 : D*(D*cubicThetaPrimeCubeRootElement hp x)=
      cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g)*(D*D) := by
    rw [h1,←mul_assoc,h2,mul_assoc]
  have hk : cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g)=1 := by
    rw [cubicThetaKubotaValue_eq_symbol]
    simp [g,t,cubicThetaPrimeConjugate,cubicThetaPrimeConjugatedMatrix,
      cubicThetaPrincipalTranslation,cubicSymbol_one_lower]
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  change (cubicThetaPrimeCubeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F)).val
    (cubicThetaPrimeCubeRootElement hp x • y)=_
  rw [cubicThetaPrimeCubeRootWeyl_global_zero,cubicThetaPrimeCubeRootWeyl_global_zero]
  change (cubicThetaInversionSection F).val (D • (D • (cubicThetaPrimeCubeRootElement hp x • y)))=
    (cubicThetaInversionSection F).val (D • (D • y))
  rw [←mul_smul,←mul_smul,mul_assoc,h3,mul_smul,mul_smul]
  change (cubicThetaInversionSection F).val
    (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g • (D • (D • y)))=_
  rw [(cubicThetaInversionSection F).property,hk,one_mul]


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootBruhatL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact unit-branch transport on the cubic-scale Hilbert completion.
There is no arithmetic-residue or Hecke-eigenvector hypothesis here. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootWeyl_translated_global {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) (F : CubicThetaSection) :
    cubicThetaPrimeCubeRootWeylSection hp
      (cubicThetaPrimeCubeRootSectionTranslate hp y (cubicThetaPrimeRootSectionRestrict F))=
      cubicThetaPrimeCubeRootSectionTranslate hp (-x)
        (cubicThetaPrimeRootSectionRestrict (cubicThetaInversionSection F)) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  change F.val (cubicThetaPrimeCubeRootElement hp y • (cubicThetaPrimeCubeRootWeylElement hp • z))=
    (cubicThetaInversionSection F).val (cubicThetaPrimeCubeRootElement hp (-x) • z)
  have he := cubicThetaPrimeCubeRootBruhat_section_one hp x y hxy F
    (cubicThetaPrimeCubeRootElement hp (-x) • z)
  have hx : cubicThetaPrimeCubeRootElement hp x • (cubicThetaPrimeCubeRootElement hp (-x) • z)=z := by
    rw [←mul_smul,←cubicThetaPrimeCubeRootElement_add,add_neg_cancel,
      cubicThetaPrimeCubeRootElement_zero,one_smul]
  rw [hx] at he
  exact he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSectionFourierPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual weighted observations at every horizontal frequency, obtained
by Fubini on the geometric cusp strip. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaSectionFourierFunction (F : CubicThetaSection) (h : Eisenstein) (v : ℝ) : ℂ :=
  cubicThetaHorizontalFourierCoefficient h (fun z => cubicThetaSectionFunction F (z,v))

lemma cubicThetaSectionFourierFunction_eq (F : CubicThetaSection) (h : Eisenstein)
    (v : ℝ) (hv : 0<v) :
    cubicThetaSectionFourierFunction F h v=cubicThetaSectionFourier F v hv h := by
  unfold cubicThetaSectionFourierFunction cubicThetaSectionFourier
  congr 1
  funext z
  exact cubicThetaSectionFunction_apply F hv

lemma cubicThetaSectionFourierPairing_integrable (F : cubicThetaFiniteEnergySections)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) :
    IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*F.val.val p)
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
  have hi := L2.integrable_inner (𝕜:=ℂ) (cubicThetaCuspFourierTest h W)
    (cubicThetaFiniteCuspRestriction F)
  apply hi.congr
  filter_upwards [(cubicThetaCuspFourierWeight_memLp h W).coeFn_toLp,
    (cubicThetaFiniteEnergy_strip_memLp F).coeFn_toLp] with p hW hF
  change inner ℂ (((cubicThetaCuspFourierWeight_memLp h W).toLp _) p)
    (((cubicThetaFiniteEnergy_strip_memLp F).toLp _) p)=_
  rw [hW,hF]
  simpa only [starRingEnd_apply,cubicThetaCuspFourierWeight,cubicThetaHorizontalCharacter] using
    (RCLike.inner_apply' (cubicThetaCuspFourierWeight h W p) (F.val.val p))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeSelfAdjointSection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reciprocal coset permutation identifies the actual adjoint
correspondence with the original cubed-prime operator. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCube_inverse_section {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (y : CubicThetaPoint) :
    F.val ((cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))⁻¹ • y)=
      star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
        F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
          (cubicThetaPrimeCubeWeyl hp • y)) := by
  have hu : star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
      cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp)=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
    norm_num
  symm
  change star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
    F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
      (cubicThetaPrincipalComplex (cubicThetaPrimeCubeWeyl hp) • y))=_
  rw [←mul_smul,cubicThetaPrimeCubeOpposite_intertwines,mul_smul]
  change star (cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp))*
    F.val (cubicThetaPrimeCubeOpposite hp •
      ((cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))⁻¹ • y))=_
  rw [F.property,cubicThetaPrimeCubeOpposite_kubota,←mul_assoc,hu,one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootIwahoriDomain
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The integral Iwahori normalizer sends the actual root-cover
fundamental domain to another fundamental domain of the same subgroup. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaPrimeRootIwahoriImage_fundamental {p : Eisenstein}
    (hp : primaryPrime p) (g : cubicThetaPrimeIwahori p) :
    IsFundamentalDomain (cubicThetaPrimeRootCoverGroup hp)
      ((fun x : CubicThetaPoint => g.val • x) '' cubicThetaPrimeRootCoverDomain hp)
        cubicThetaPointMeasure := by
  apply (cubicThetaPrimeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).image_of_equiv
    (Homeomorph.smul g.val).toEquiv
    (measurePreserving_smul g.val⁻¹ cubicThetaPointMeasure).quasiMeasurePreserving
    (cubicThetaPrimeRootIwahoriEquiv g⁻¹)
  intro h x
  change g.val • ((g.val⁻¹*h.val*(g.val⁻¹)⁻¹) • x)=h.val • (g.val • x)
  simp only [←mul_smul,inv_inv,mul_inv_cancel_left,mul_assoc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootCoverDegree
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The root cover has its exact finite subgroup index as measure degree. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

lemma cubicThetaPrimeRootCoverProjection_continuous {p : Eisenstein} (hp : primaryPrime p) :
    Continuous (cubicThetaPrimeRootCoverProjection hp) := by
  apply (cubicThetaPrimeRootCoverMap_open hp).isQuotientMap.continuous_iff.mpr
  exact cubicThetaQuotientMap_open.continuous

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual L2 representatives of sections on the finite root cover.
The Weyl action preserves square integrability and the exact L2 norm. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeRootWeylSection_memLp {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p)
    (hF : MemLp (cubicThetaPrimeRootSectionRepresentative hp F) 2 (cubicThetaPrimeRootCoverMeasure hp)) :
    MemLp (cubicThetaPrimeRootSectionRepresentative hp (cubicThetaPrimeRootWeylSection hp F))
      2 (cubicThetaPrimeRootCoverMeasure hp) := by
  apply (memLp_norm_iff
    (cubicThetaPrimeRootSectionRepresentative_measurable hp _).aestronglyMeasurable).mp
  have hn := hF.norm
  simp only [cubicThetaPrimeRootSectionRepresentative_norm] at hn
  have hc := hn.comp_measurePreserving (cubicThetaPrimeRootCoverWeyl_measurePreserving hp)
  simpa only [Function.comp_def,cubicThetaPrimeRootSectionRepresentative_norm,
    cubicThetaPrimeRootWeylSection_norm] using hc

lemma cubicThetaPrimeRootWeylSection_L2_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p)
    (hF : MemLp (cubicThetaPrimeRootSectionRepresentative hp F) 2 (cubicThetaPrimeRootCoverMeasure hp)) :
    ‖(cubicThetaPrimeRootWeylSection_memLp hp F hF).toLp
      (cubicThetaPrimeRootSectionRepresentative hp (cubicThetaPrimeRootWeylSection hp F))‖=
      ‖hF.toLp (cubicThetaPrimeRootSectionRepresentative hp F)‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  rw [cubicThetaPrimeRootSectionL2_norm_sq,cubicThetaPrimeRootSectionL2_norm_sq]
  exact cubicThetaPrimeRootWeylSection_mass hp F

def cubicThetaPrimeRootFiniteWeyl {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeRootFiniteSections hp →ₗ[ℂ] cubicThetaPrimeRootFiniteSections hp where
  toFun F := ⟨cubicThetaPrimeRootWeylSection hp F.val,cubicThetaPrimeRootWeylSection_memLp hp F.val F.property⟩
  map_add' _F _G := rfl
  map_smul' _c _F := rfl

lemma cubicThetaPrimeRootFiniteWeyl_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootFiniteSections hp) :
    ‖cubicThetaPrimeRootFiniteValue hp (cubicThetaPrimeRootFiniteWeyl hp F)‖=
      ‖cubicThetaPrimeRootFiniteValue hp F‖ :=
  cubicThetaPrimeRootWeylSection_L2_norm hp F.val F.property

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootAutomorphicL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Completion of the actual finite-mass sections on the root cover.
The geometric Weyl pullback extends to a linear isometry of this space. -/
noncomputable section
open Topology
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.rootFiniteSections_addCommGroup
def cubicThetaPrimeRootWeylL2 {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeRootAutomorphicL2 hp →ₗᵢ[ℂ] cubicThetaPrimeRootAutomorphicL2 hp :=
  ((cubicThetaPrimeRootFiniteEmbedding hp).comp (cubicThetaPrimeRootFiniteWeyl hp)).extendOfIsometry
    (cubicThetaPrimeRootFiniteEmbedding_dense hp) (cubicThetaPrimeRootFiniteWeyl_norm hp)

lemma cubicThetaPrimeRootWeylL2_finite {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootFiniteSections hp) :
    cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootFiniteEmbedding hp F)=
      cubicThetaPrimeRootFiniteEmbedding hp (cubicThetaPrimeRootFiniteWeyl hp F) :=
  LinearMap.extendOfIsometry_eq _ _ _ F

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootTranslationL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fractional translations extend isometrically to the actual completed
space of root-cover sections. -/
noncomputable section
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.rootTranslation_finiteGroup
lemma cubicThetaPrimeRootResidueSection_memLp {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) (F : cubicThetaPrimeRootSections p)
    (hF : MeasureTheory.MemLp (cubicThetaPrimeRootSectionRepresentative hp F) 2
      (cubicThetaPrimeRootCoverMeasure hp)) :
    MeasureTheory.MemLp (cubicThetaPrimeRootSectionRepresentative hp
      (cubicThetaPrimeRootResidueOperator hp r F)) 2 (cubicThetaPrimeRootCoverMeasure hp) := by
  change MeasureTheory.MemLp (cubicThetaPrimeRootSectionRepresentative hp
    (cubicThetaPrimeRootSectionTranslate hp (residueRepresentative p r) F)) 2 _
  apply (MeasureTheory.memLp_norm_iff
    (cubicThetaPrimeRootSectionRepresentative_measurable hp _).aestronglyMeasurable).mp
  have hn := hF.norm
  simp only [cubicThetaPrimeRootSectionRepresentative_norm] at hn
  have hc := hn.comp_measurePreserving
    (cubicThetaPrimeRootCoverTranslate_measurePreserving hp (residueRepresentative p r))
  simpa only [Function.comp_def,cubicThetaPrimeRootSectionRepresentative_norm,
    cubicThetaPrimeRootSectionTranslate_norm] using hc

def cubicThetaPrimeRootFiniteResidue {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) : cubicThetaPrimeRootFiniteSections hp →ₗ[ℂ]
      cubicThetaPrimeRootFiniteSections hp where
  toFun F := ⟨cubicThetaPrimeRootResidueOperator hp r F.val,
    cubicThetaPrimeRootResidueSection_memLp hp r F.val F.property⟩
  map_add' _F _G := rfl
  map_smul' _c _F := rfl

lemma cubicThetaPrimeRootFiniteResidue_norm {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) (F : cubicThetaPrimeRootFiniteSections hp) :
    ‖cubicThetaPrimeRootFiniteEmbedding hp (cubicThetaPrimeRootFiniteResidue hp r F)‖=
      ‖cubicThetaPrimeRootFiniteEmbedding hp F‖ := by
  change ‖cubicThetaPrimeRootFiniteValue hp (cubicThetaPrimeRootFiniteResidue hp r F)‖=
    ‖cubicThetaPrimeRootFiniteValue hp F‖
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  have hf : MeasureTheory.MemLp (cubicThetaPrimeRootSectionRepresentative hp F.val) 2
      (cubicThetaPrimeRootCoverMeasure hp) := F.property
  change ‖(cubicThetaPrimeRootResidueSection_memLp hp r F.val hf).toLp _‖^2=‖hf.toLp _‖^2
  calc
    _ = ∫ q, (cubicThetaPrimeRootSectionNorm hp
        (cubicThetaPrimeRootResidueOperator hp r F.val) q)^2
        ∂cubicThetaPrimeRootCoverMeasure hp :=
      cubicThetaPrimeRootSectionL2_norm_sq hp _ (cubicThetaPrimeRootResidueSection_memLp hp r F.val hf)
    _ = ∫ q, (cubicThetaPrimeRootSectionNorm hp F.val q)^2
        ∂cubicThetaPrimeRootCoverMeasure hp :=
      cubicThetaPrimeRootSectionTranslate_mass hp (residueRepresentative p r) F.val
    _ = _ := (cubicThetaPrimeRootSectionL2_norm_sq hp F.val hf).symm

def cubicThetaPrimeRootResidueL2 {p : Eisenstein} (hp : primaryPrime p) (r : Residues p) :
    cubicThetaPrimeRootAutomorphicL2 hp →ₗᵢ[ℂ] cubicThetaPrimeRootAutomorphicL2 hp :=
  ((cubicThetaPrimeRootFiniteEmbedding hp).comp (cubicThetaPrimeRootFiniteResidue hp r)).extendOfIsometry
    (cubicThetaPrimeRootFiniteEmbedding_dense hp) (cubicThetaPrimeRootFiniteResidue_norm hp r)

lemma cubicThetaPrimeRootResidueL2_finite {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) (F : cubicThetaPrimeRootFiniteSections hp) :
    cubicThetaPrimeRootResidueL2 hp r (cubicThetaPrimeRootFiniteEmbedding hp F)=
      cubicThetaPrimeRootFiniteEmbedding hp (cubicThetaPrimeRootFiniteResidue hp r F) :=
  LinearMap.extendOfIsometry_eq _ _ _ F

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootRestrictionBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the root-average contraction to actual global sections. The
finite-cover degree supplies the exact normalization of their square norm. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

lemma cubicThetaPrimeRootSectionRestrict_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (q : CubicThetaPrimeRootCover hp) :
    cubicThetaPrimeRootSectionNorm hp (cubicThetaPrimeRootSectionRestrict F) q=
      cubicThetaSectionNorm F (cubicThetaPrimeRootCoverProjection hp q) := by
  induction q using Quotient.inductionOn with
  | h y => exact (cubicThetaSectionNorm_apply F y).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootSquareOrthogonal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original and twice-dilated sections have distinct cubic
characters on an actual arithmetic subgroup, so their integral pairing vanishes. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeRootWeyl_global_square {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^2)) (F : CubicThetaSection) (x : CubicThetaPoint) :
    (cubicThetaPrimeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F)).val (g.val • x)=
      cubicThetaPrimeIwahoriCharacter p hp (cubicThetaPrimeSquareIwahori g)*
        cubicThetaKubotaValue g.val*
          (cubicThetaPrimeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F)).val x := by
  let D := cubicThetaPrimeDilation hp.2.ne_zero
  have h1 := cubicThetaPrimeDilation_intertwines hp.1 (cubicThetaPrimeSquareIwahori g)
  have h2 := cubicThetaPrimeDilation_intertwines hp.1 (cubicThetaPrimeSquareConjugate hp g)
  change D*cubicThetaPrincipalComplex g.val=
    cubicThetaPrincipalComplex (cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeSquareIwahori g))*D at h1
  change D*cubicThetaPrincipalComplex (cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeSquareIwahori g))=
    cubicThetaPrincipalComplex (cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeSquareConjugate hp g))*D at h2
  have he : D*(D*cubicThetaPrincipalComplex g.val)=
      cubicThetaPrincipalComplex (cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeSquareConjugate hp g))*(D*D) := by
    rw [h1,←mul_assoc,h2,mul_assoc]
  rw [cubicThetaPrimeRootWeyl_global_zero,cubicThetaPrimeRootWeyl_global_zero]
  change (cubicThetaInversionSection F).val (D • (D • (cubicThetaPrincipalComplex g.val • x)))=_
  rw [←mul_smul,←mul_smul,mul_assoc,he,mul_smul,mul_smul]
  change (cubicThetaInversionSection F).val
    (cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeSquareConjugate hp g) • (D • (D • x)))=_
  rw [(cubicThetaInversionSection F).property,cubicThetaPrimeSquareConjugate_kubota]

theorem cubicThetaPrimeRootSquare_pair_integral_zero {p : Eisenstein} (hp : primaryPrime p)
    (F G : CubicThetaSection) :
    (∫ x in cubicThetaPrimeRootCoverDomain hp,star (F.val x)*
      (cubicThetaPrimeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict G)).val x
        ∂cubicThetaPointMeasure)=0 := by
  let H := cubicThetaPrimeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict G)
  let f : CubicThetaPoint → ℂ := fun x => star (F.val x)*H.val x
  obtain ⟨g,hg⟩ := cubicThetaPrimeSquareCharacter_nontrivial hp
  let c := cubicThetaPrimeIwahoriCharacter p hp (cubicThetaPrimeSquareIwahori g)
  have hinv (h : cubicThetaPrimeRootCoverGroup hp) (x : CubicThetaPoint) : f (h • x)=f x := by
    change star (F.val (h.val • x))*H.val (h.val • x)=_
    have hH : H.val (h.val • x)=cubicThetaKubotaValue h.val*H.val x := H.property h x
    rw [F.property,hH,star_mul]
    have hk : star (cubicThetaKubotaValue h.val)*cubicThetaKubotaValue h.val=1 := by
      rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
      norm_num
    calc
      _ = (star (cubicThetaKubotaValue h.val)*cubicThetaKubotaValue h.val)*f x := by dsimp [f]; ring
      _ = f x := by rw [hk,one_mul]
  have hi := (cubicThetaPrimeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).setIntegral_eq
    (cubicThetaPrimeRootIwahoriImage_fundamental hp (cubicThetaPrimeSquareIwahori g)) hinv
  have hc := (measurePreserving_smul g.val cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul g.val) f (cubicThetaPrimeRootCoverDomain hp)
  have he : (∫ x in cubicThetaPrimeRootCoverDomain hp,f x ∂cubicThetaPointMeasure)=
      ∫ x in cubicThetaPrimeRootCoverDomain hp,f (g.val • x) ∂cubicThetaPointMeasure := hi.trans hc
  have hfun : (fun x => f (g.val • x))=fun x => c*f x := by
    funext x
    dsimp only [f,H,c]
    rw [F.property,cubicThetaPrimeRootWeyl_global_square,star_mul]
    have hk : star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val=1 := by
      rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
      norm_num
    calc
      _ = (star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val)*
        (cubicThetaPrimeIwahoriCharacter p hp (cubicThetaPrimeSquareIwahori g)*
          (star (F.val x)*(cubicThetaPrimeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict G)).val x)) := by ring
      _ = _ := by rw [hk,one_mul]
  rw [hfun,integral_const_mul] at he
  exact eq_zero_of_mul_eq_self_left hg he.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootWeylFixed
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained twice-dilated branch is fixed by the root group. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeRootWeyl_global_translate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : CubicThetaSection) :
    cubicThetaPrimeRootSectionTranslate hp x
      (cubicThetaPrimeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F))=
        cubicThetaPrimeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F) := by
  let D := cubicThetaPrimeDilation hp.2.ne_zero
  let t := cubicThetaPrincipalTranslation x
  let g : cubicThetaPrimeIwahori p := ⟨t,by change p∣0; exact dvd_zero p⟩
  have h1 : D*cubicThetaPrimeRootElement hp x=cubicThetaPrincipalComplex t*D := by
    dsimp only [D,t,cubicThetaPrimeRootElement]
    group
  have h2 : D*cubicThetaPrincipalComplex t=
      cubicThetaPrincipalComplex (cubicThetaPrimeConjugate hp.1 g)*D :=
    cubicThetaPrimeDilation_intertwines hp.1 g
  have h3 : D*(D*cubicThetaPrimeRootElement hp x)=
      cubicThetaPrincipalComplex (cubicThetaPrimeConjugate hp.1 g)*(D*D) := by
    rw [h1,←mul_assoc,h2,mul_assoc]
  have hk : cubicThetaKubotaValue (cubicThetaPrimeConjugate hp.1 g)=1 := by
    rw [cubicThetaKubotaValue_eq_symbol]
    simp [g,t,cubicThetaPrimeConjugate,cubicThetaPrimeConjugatedMatrix,
      cubicThetaPrincipalTranslation,cubicSymbol_one_lower]
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  change (cubicThetaPrimeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F)).val
    (cubicThetaPrimeRootElement hp x • y)=_
  rw [cubicThetaPrimeRootWeyl_global_zero,cubicThetaPrimeRootWeyl_global_zero]
  change (cubicThetaInversionSection F).val (D • (D • (cubicThetaPrimeRootElement hp x • y)))=
    (cubicThetaInversionSection F).val (D • (D • y))
  rw [←mul_smul,←mul_smul,mul_assoc,h3,mul_smul,mul_smul]
  change (cubicThetaInversionSection F).val
    (cubicThetaPrimeConjugate hp.1 g • (D • (D • y)))=_
  rw [(cubicThetaInversionSection F).property,hk,one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootFirstIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer of the first root level to the actual cube-root domain.
In particular the nonzero p-squared residue branches have zero pairing. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaFirstRootCover {p : Eisenstein} (hp : primaryPrime p) : CubicThetaArithmeticCover where
  group := cubicThetaPrimeRootCoverGroup hp
  domain := cubicThetaPrimeRootCoverDomain hp
  measurable := cubicThetaPrimeRootCoverDomain_measurable hp
  unique := cubicThetaPrimeRootCoverDomain_unique hp

lemma cubicThetaPrimeRoot_translate_pair_invariant {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F G : CubicThetaSection)
    (g : cubicThetaPrimeRootCoverGroup hp) (z : CubicThetaPoint) :
    star (F.val (g • z))*G.val (cubicThetaPrimeRootElement hp x • (g • z))=
      star (F.val z)*G.val (cubicThetaPrimeRootElement hp x • z) := by
  have hG := cubicThetaPrimeRootSection_property hp
    (cubicThetaPrimeRootSectionTranslate hp x (cubicThetaPrimeRootSectionRestrict G)) g z
  change G.val (cubicThetaPrimeRootElement hp x • (g.val • z))=
    cubicThetaKubotaValue g.val*G.val (cubicThetaPrimeRootElement hp x • z) at hG
  change star (F.val (g.val • z))*G.val (cubicThetaPrimeRootElement hp x • (g.val • z))=_
  rw [F.property,hG,star_mul]
  have hk : star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
    norm_num
  calc
    _ = (star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val)*
      (star (F.val z)*G.val (cubicThetaPrimeRootElement hp x • z)) := by ring
    _ = _ := by rw [hk,one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootStripBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal cusp strip has at most one representative in each orbit of
any subgroup of the principal group. Its mass is bounded by fundamental-domain
mass, also for the cubic-root cover. -/
noncomputable section
open Set MeasureTheory
open scoped Pointwise ENNReal
namespace CubicFirstMoment

lemma cubicThetaInjective_subgroup_lintegral_le (K : Subgroup cubicThetaPrincipalGroup)
    {D S : Set CubicThetaPoint} (hD : IsFundamentalDomain K D cubicThetaPointMeasure)
    (hDm : MeasurableSet D) (hSm : MeasurableSet S) (hS : InjOn cubicThetaQuotientMap S)
    (f : CubicThetaPoint → ℝ≥0∞) (hi : ∀ (g : K) x, f (g • x)=f x) :
    (∫⁻ x in S,f x ∂cubicThetaPointMeasure)≤∫⁻ x in D,f x ∂cubicThetaPointMeasure := by
  have hm (g : K) : MeasurableSet (g • S ∩ D) :=
    ((measurableEmbedding_const_smul g).measurableSet_image' hSm).inter hDm
  have hd : Pairwise (fun g h : K => Disjoint (g • S ∩ D) (h • S ∩ D)) := by
    intro g h hgh
    exact (cubicThetaInjective_subgroup_disjoint K hS hgh).mono inter_subset_left inter_subset_left
  rw [hD.setLIntegral_eq_tsum' f S]
  simp_rw [hi]
  rw [←lintegral_iUnion hm hd]
  apply lintegral_mono_set
  exact iUnion_subset fun _ => inter_subset_right

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootObservationProjection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Fourier support rule survives completion and all bounded
cusp observations. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootFunction_fourier {p : Eisenstein}
    (F : cubicThetaPrimeCubeRootSections p) (h : Eisenstein) (v : ℝ) (hv : 0<v) :
    cubicThetaHorizontalFourierCoefficient h (fun z => cubicThetaPrimeCubeRootFunction F (z,v))=
      cubicThetaHorizontalFourierCoefficient h (cubicThetaPrimeRootHorizontal F v hv) := by
  congr 1
  funext z
  exact cubicThetaPrimeCubeRootFunction_apply F hv

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootTraceNormalized
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact normalized trace pairing. No Hecke eigenvalue or local
coefficient relation is postulated in constructing this identity. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootTrace_scalar {p : Eisenstein} (hp : primaryPrime p) :
    star (((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ)):ℂ)⁻¹)*
      (((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ)):ℂ)⁻¹)*
        ((cubicThetaPrimeCubeRootHeckeSubgroup hp).index:ℂ)=
      ((cubicThetaPrimeIwahori (p^3)).index:ℂ)⁻¹ := by
  let k : ℝ := (cubicThetaPrimeCubeRootCoverGroup hp).index
  let r : ℝ := (cubicThetaPrimeCubeRootHeckeSubgroup hp).index
  let d : ℝ := (cubicThetaPrimeIwahori (p^3)).index
  have hk : 0<k := cubicThetaPrimeCubeRootCoverDegree_pos hp
  have hd : d≠0 := by
    exact Nat.cast_ne_zero.mpr (cubicThetaPrimeCubeIwahori_finiteIndex hp).index_ne_zero
  have hrd : (r:ℂ)*(d:ℂ)=(k:ℂ) := by
    change ((cubicThetaPrimeCubeRootHeckeSubgroup hp).index:ℂ)*
      ((cubicThetaPrimeIwahori (p^3)).index:ℂ)=((cubicThetaPrimeCubeRootCoverGroup hp).index:ℂ)
    rw [←Nat.cast_mul,cubicThetaPrimeCubeRootHecke_index hp]
  have hs : star ((Real.sqrt k:ℂ)⁻¹)*(Real.sqrt k:ℂ)⁻¹=(k:ℂ)⁻¹ := by
    rw [star_inv₀,Complex.star_def,Complex.conj_ofReal,←mul_inv_rev,←pow_two,
      ←Complex.ofReal_pow,Real.sq_sqrt hk.le]
  change star ((Real.sqrt k:ℂ)⁻¹)*(Real.sqrt k:ℂ)⁻¹*(r:ℂ)=(d:ℂ)⁻¹
  rw [hs]
  apply mul_left_cancel₀ (show (d:ℂ)≠0 from Complex.ofReal_ne_zero.mpr hd)
  rw [mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hd)]
  calc
    _ = (k:ℂ)⁻¹*((r:ℂ)*(d:ℂ)) := by ring
    _ = 1 := by rw [hrd,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hk.ne')]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootResidueOverlap
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The once-cubic overlap of the actual arithmetic residue follows
from the proved Hecke eigenvalue and exact trace normalization. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootHecke_ratio {p : Eisenstein} (hp : primaryPrime p) :
    ((cubicThetaPrimeIwahori (p^3)).index:ℂ)⁻¹*((norm p:ℂ)^2+norm p)=(norm p:ℂ)⁻¹ := by
  have hN : (normNat p:ℂ)=(norm p:ℂ) := by
    simpa only [Complex.ofReal_natCast] using congrArg Complex.ofReal (normNat_cast p)
  rw [cubicThetaPrimeCubeIwahori_index hp,Nat.cast_add,Nat.cast_pow,Nat.cast_pow,hN]
  have hq : (norm p:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hp.2.ne_zero).ne'
  have hq1 : (norm p:ℂ)+1≠0 := by
    have h : (norm p+1:ℝ)≠0 := (add_pos_of_nonneg_of_pos (norm_nonneg p) zero_lt_one).ne'
    simpa only [Complex.ofReal_add,Complex.ofReal_one] using Complex.ofReal_ne_zero.mpr h
  have hd : (norm p:ℂ)^3+(norm p:ℂ)^2≠0 := by
    rw [show (norm p:ℂ)^3+(norm p:ℂ)^2=(norm p:ℂ)^2*((norm p:ℂ)+1) by ring]
    exact mul_ne_zero (pow_ne_zero 2 hq) hq1
  field_simp [hd,hq]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDoubleRootWeyl
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual opposite-root involution at modulus p cubed. Both
integral conjugations preserve the original cubic automorphy factor. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeDoubleRootWeyl_kubota {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeDoubleRootSubgroup p) :
    cubicThetaKubotaValue (cubicThetaPrimeDoubleRootWeylConjugate hp g).val=cubicThetaKubotaValue g.val := by
  change cubicThetaKubotaValue (cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹
    (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
      (cubicThetaPrimeDoubleRootDilationIwahori hp g)))=cubicThetaKubotaValue g.val
  rw [cubicThetaInversionConjugate_character]
  have he := cubicThetaPrimePowerConjugate_kubota_star hp 2
    (cubicThetaPrimeDoubleRootDilationIwahori hp g)
  change cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
    (cubicThetaPrimeDoubleRootDilationIwahori hp g))=
    star ((cubicSymbol p (g.val.val 0 0))^2)*
      cubicThetaKubotaValue (cubicThetaPrimeDoubleRootDilationIwahori hp g).val at he
  rw [cubicThetaPrimeDoubleRoot_diagonal_character hp g,one_pow,star_one,one_mul] at he
  exact he.trans (cubicThetaPrimeDoubleRootDilation_kubota hp g)


lemma cubicThetaPrimeDoubleRootWeylElement_inversion {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeDoubleRootWeylElement hp=cubicThetaInversionMatrix ((p^2:Eisenstein):ℂ)
      (fun he => (pow_ne_zero 2 hp.2.ne_zero) (Subtype.ext he)) := by
  rw [cubicThetaPrimeDoubleRootWeylElement,cubicThetaPrimeDoubleAtkinMatrix,cubicThetaFullInversion_complex]
  apply Subtype.ext
  change ((cubicThetaInversionMatrix 1 one_ne_zero:Matrix (Fin 2) (Fin 2) ℂ)*
    (cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero):Matrix (Fin 2) (Fin 2) ℂ))*
      (cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero):Matrix (Fin 2) (Fin 2) ℂ)=_
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicThetaInversionMatrix,cubicThetaPrimeDilation,Matrix.mul_apply,Fin.sum_univ_two,
      ←pow_two,cubicThetaPrimeSquareRoot_sq]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDoubleRootBruhat
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal integral Bruhat identity for unit translations modulo p cubed. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment


theorem cubicThetaPrimeDoubleRootBruhat_identity {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^2∣9*x*y-1) :
    cubicThetaPrimeDoubleRootElement hp y*cubicThetaPrimeDoubleRootWeylElement hp*cubicThetaPrimeDoubleRootElement hp x=
      cubicThetaFullComplex cubicThetaFullInversion*
        cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootBruhat hp x y hxy) := by
  have hpC : ((p^2:Eisenstein):ℂ)≠0 := fun he => (pow_ne_zero 2 hp.2.ne_zero) (Subtype.ext he)
  have hp1C : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  have hthree : ((3:Eisenstein):ℂ)=3 := rfl
  have hd : (((1-9*x*y)/p^2:Eisenstein):ℂ)=(1-9*(x:ℂ)*(y:ℂ))/((p^2:Eisenstein):ℂ) := by
    apply (eq_div_iff hpC).mpr
    calc
      _ = ((p^2:Eisenstein):ℂ)*(((1-9*x*y)/p^2:Eisenstein):ℂ) := mul_comm _ _
      _ = ((1-9*x*y:Eisenstein):ℂ) := congrArg Subtype.val (cubicThetaPrimeDoubleRootBruhat_division hp x y hxy)
      _ = _ := by push_cast; rfl
  rw [cubicThetaPrimeDoubleRootElement_translation,cubicThetaPrimeDoubleRootElement_translation,
    cubicThetaPrimeDoubleRootWeylElement_inversion,cubicThetaFullInversion_complex]
  apply Subtype.ext
  change ((cubicThetaTranslationMatrix (((3*y:Eisenstein):ℂ)/((p^2:Eisenstein):ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*
    (cubicThetaInversionMatrix ((p^2:Eisenstein):ℂ) hpC:Matrix (Fin 2) (Fin 2) ℂ))*
      (cubicThetaTranslationMatrix (((3*x:Eisenstein):ℂ)/((p^2:Eisenstein):ℂ)):Matrix (Fin 2) (Fin 2) ℂ)=
        (cubicThetaInversionMatrix 1 one_ne_zero:Matrix (Fin 2) (Fin 2) ℂ)*
          (cubicThetaPrincipalComplex (cubicThetaPrimeDoubleRootBruhat hp x y hxy):Matrix (Fin 2) (Fin 2) ℂ)
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicThetaTranslationMatrix,cubicThetaInversionMatrix,cubicThetaPrincipalComplex_apply,
      cubicThetaPrimeDoubleRootBruhat,cubicThetaPrimeDoubleRootBruhatMatrix,Matrix.mul_apply,Fin.sum_univ_two,hd]
  all_goals field_simp [hp1C]
  all_goals try rw [hthree]
  all_goals ring

theorem cubicThetaPrimeDoubleRootBruhat_section {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^2∣9*x*y-1) (F : CubicThetaSection) (z : CubicThetaPoint) :
    F.val (cubicThetaPrimeDoubleRootElement hp y •
      (cubicThetaPrimeDoubleRootWeylElement hp • (cubicThetaPrimeDoubleRootElement hp x • z)))=
      cubicSymbol (p^2) (3*y)*(cubicThetaInversionSection F).val z := by
  rw [←mul_smul,←mul_smul,cubicThetaPrimeDoubleRootBruhat_identity hp x y hxy,mul_smul]
  change (cubicThetaInversionSection F).val
    (cubicThetaPrimeDoubleRootBruhat hp x y hxy • z)=_
  rw [(cubicThetaInversionSection F).property,cubicThetaPrimeDoubleRootBruhat_kubota]


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDoubleRootWeylSections
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Involutive action of the opposite square root on actual sections. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment


def cubicThetaPrimeDoubleRootWeylSection {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeDoubleRootSections p) : cubicThetaPrimeDoubleRootSections p :=
  ⟨⟨fun y => F.val (cubicThetaPrimeDoubleRootWeylElement hp • y),
    F.val.continuous.comp (continuous_const_smul _)⟩,by
    intro g y
    change F.val (cubicThetaPrimeDoubleRootWeylElement hp • (g.val • y))=
      cubicThetaKubotaValue g.val*F.val (cubicThetaPrimeDoubleRootWeylElement hp • y)
    rw [cubicThetaPrimeDoubleRootWeylPoint_intertwines,F.property,cubicThetaPrimeDoubleRootWeyl_kubota]⟩


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDoubleRootGlobal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The twice-dilated global branch is fixed by intermediate root translations. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeDoubleRootWeyl_global_zero {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (z : CubicThetaPoint) :
    (cubicThetaPrimeDoubleRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F)).val z=
      (cubicThetaInversionSection F).val
        (cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero) • (cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero) • z)) := by
  change F.val (cubicThetaPrimeDoubleRootWeylElement hp • z)=_
  rw [cubicThetaPrimeDoubleRootWeylElement,cubicThetaPrimeDoubleAtkinMatrix,mul_smul,mul_smul]
  rfl

lemma cubicThetaPrimeDoubleRootWeyl_global_translate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : CubicThetaSection) :
    cubicThetaPrimeDoubleRootSectionTranslate hp x
      (cubicThetaPrimeDoubleRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F))=
        cubicThetaPrimeDoubleRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F) := by
  let D := cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero)
  let t := cubicThetaPrincipalTranslation x
  let g : cubicThetaPrimeIwahori (p^2) := ⟨t,by change p^2∣0; exact dvd_zero (p^2)⟩
  have h1 : D*cubicThetaPrimeDoubleRootElement hp x=cubicThetaPrincipalComplex t*D := by
    dsimp only [D,t,cubicThetaPrimeDoubleRootElement]
    group
  have h2 : D*cubicThetaPrincipalComplex t=
      cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp) g)*D :=
    cubicThetaPrimeDilation_intertwines (cubicThetaPrimeDouble_primary hp) g
  have h3 : D*(D*cubicThetaPrimeDoubleRootElement hp x)=
      cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp) g)*(D*D) := by
    rw [h1,←mul_assoc,h2,mul_assoc]
  have hk : cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp) g)=1 := by
    rw [cubicThetaKubotaValue_eq_symbol]
    simp [g,t,cubicThetaPrimeConjugate,cubicThetaPrimeConjugatedMatrix,
      cubicThetaPrincipalTranslation,cubicSymbol_one_lower]
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  change (cubicThetaPrimeDoubleRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F)).val
    (cubicThetaPrimeDoubleRootElement hp x • y)=_
  rw [cubicThetaPrimeDoubleRootWeyl_global_zero,cubicThetaPrimeDoubleRootWeyl_global_zero]
  change (cubicThetaInversionSection F).val (D • (D • (cubicThetaPrimeDoubleRootElement hp x • y)))=
    (cubicThetaInversionSection F).val (D • (D • y))
  rw [←mul_smul,←mul_smul,mul_assoc,h3,mul_smul,mul_smul]
  change (cubicThetaInversionSection F).val
    (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp) g • (D • (D • y)))=_
  rw [(cubicThetaInversionSection F).property,hk,one_mul]


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDoubleRootDomain
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact intermediate root cover and its two measure-preserving
root operations. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaDoubleRootCover {p : Eisenstein} (hp : primaryPrime p) : CubicThetaArithmeticCover := by
  letI := cubicThetaPrimeDoubleRootSubgroup_finiteIndex hp
  exact cubicThetaRelativeCover cubicThetaBaseCover (cubicThetaPrimeDoubleRootSubgroup p) (le_top)

def cubicThetaPrimeDoubleRootDomain {p : Eisenstein} (hp : primaryPrime p) : Set CubicThetaPoint :=
  (cubicThetaDoubleRootCover hp).domain

lemma cubicThetaPrimeDoubleRootDomain_fundamental {p : Eisenstein} (hp : primaryPrime p) :
    IsFundamentalDomain (cubicThetaPrimeDoubleRootSubgroup p)
      (cubicThetaPrimeDoubleRootDomain hp) cubicThetaPointMeasure :=
  (cubicThetaDoubleRootCover hp).fundamental cubicThetaPointMeasure

lemma cubicThetaPrimeDoubleRootImage_fundamental {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) :
    IsFundamentalDomain (cubicThetaPrimeDoubleRootSubgroup p)
      ((fun z : CubicThetaPoint => cubicThetaPrimeDoubleRootElement hp x • z) ''
        cubicThetaPrimeDoubleRootDomain hp) cubicThetaPointMeasure := by
  apply (cubicThetaPrimeDoubleRootDomain_fundamental hp).image_of_equiv
    (Homeomorph.smul (cubicThetaPrimeDoubleRootElement hp x)).toEquiv
    (measurePreserving_smul (cubicThetaPrimeDoubleRootElement hp x)⁻¹
      cubicThetaPointMeasure).quasiMeasurePreserving
    (cubicThetaPrimeDoubleRootAutomorphism hp (-x)).toEquiv
  intro g y
  change cubicThetaPrimeDoubleRootElement hp x • ((cubicThetaPrimeDoubleRootConjugate hp (-x) g).val • y)=
    g.val • (cubicThetaPrimeDoubleRootElement hp x • y)
  rw [cubicThetaPrimeDoubleRootPoint_intertwines,←cubicThetaPrimeDoubleRootConjugate_add,
    add_neg_cancel,cubicThetaPrimeDoubleRootConjugate_zero]

lemma cubicThetaPrimeDoubleRootWeylImage_fundamental {p : Eisenstein} (hp : primaryPrime p) :
    IsFundamentalDomain (cubicThetaPrimeDoubleRootSubgroup p)
      ((fun z : CubicThetaPoint => cubicThetaPrimeDoubleRootWeylElement hp • z) ''
        cubicThetaPrimeDoubleRootDomain hp) cubicThetaPointMeasure := by
  apply (cubicThetaPrimeDoubleRootDomain_fundamental hp).image_of_equiv
    (Homeomorph.smul (cubicThetaPrimeDoubleRootWeylElement hp)).toEquiv
    (measurePreserving_smul (cubicThetaPrimeDoubleRootWeylElement hp)⁻¹
      cubicThetaPointMeasure).quasiMeasurePreserving
    (cubicThetaPrimeDoubleRootWeylConjugate_involutive hp).toPerm
  intro g y
  change cubicThetaPrimeDoubleRootWeylElement hp • ((cubicThetaPrimeDoubleRootWeylConjugate hp g).val • y)=
    g.val • (cubicThetaPrimeDoubleRootWeylElement hp • y)
  rw [cubicThetaPrimeDoubleRootWeylPoint_intertwines,cubicThetaPrimeDoubleRootWeylConjugate_involutive]

lemma cubicThetaPrimeDoubleRootIwahoriImage_fundamental {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^2)) :
    IsFundamentalDomain (cubicThetaPrimeDoubleRootSubgroup p)
      ((fun z : CubicThetaPoint => g.val • z) '' cubicThetaPrimeDoubleRootDomain hp)
        cubicThetaPointMeasure := by
  apply (cubicThetaPrimeDoubleRootDomain_fundamental hp).image_of_equiv
    (Homeomorph.smul g.val).toEquiv
    (measurePreserving_smul g.val⁻¹ cubicThetaPointMeasure).quasiMeasurePreserving
    (cubicThetaPrimeRootIwahoriEquiv g⁻¹)
  intro h x
  change g.val • ((g.val⁻¹*h.val*(g.val⁻¹)⁻¹) • x)=h.val • (g.val • x)
  simp only [←mul_smul,inv_inv,mul_inv_cancel_left,mul_assoc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDoubleRootPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal Hermitian integral transport on the intermediate root cover. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeDoubleRoot_pair_translation {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F G : cubicThetaPrimeDoubleRootSections p) :
    (∫ z in cubicThetaPrimeDoubleRootDomain hp,
      star (F.val (cubicThetaPrimeDoubleRootElement hp x • z))*
        G.val (cubicThetaPrimeDoubleRootElement hp x • z) ∂cubicThetaPointMeasure)=
      ∫ z in cubicThetaPrimeDoubleRootDomain hp,star (F.val z)*G.val z ∂cubicThetaPointMeasure := by
  have he := (cubicThetaPrimeDoubleRootDomain_fundamental hp).setIntegral_eq
    (f:=fun z => star (F.val z)*G.val z) (cubicThetaPrimeDoubleRootImage_fundamental hp x)
    (cubicThetaPrimeDoubleRoot_pair_invariant hp F G)
  have hm := (measurePreserving_smul (cubicThetaPrimeDoubleRootElement hp x)
    cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul (cubicThetaPrimeDoubleRootElement hp x))
    (fun z => star (F.val z)*G.val z) (cubicThetaPrimeDoubleRootDomain hp)
  exact (he.trans hm).symm

lemma cubicThetaPrimeDoubleRoot_pair_weyl {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPrimeDoubleRootSections p) :
    (∫ z in cubicThetaPrimeDoubleRootDomain hp,
      star (F.val (cubicThetaPrimeDoubleRootWeylElement hp • z))*
        G.val (cubicThetaPrimeDoubleRootWeylElement hp • z) ∂cubicThetaPointMeasure)=
      ∫ z in cubicThetaPrimeDoubleRootDomain hp,star (F.val z)*G.val z ∂cubicThetaPointMeasure := by
  have he := (cubicThetaPrimeDoubleRootDomain_fundamental hp).setIntegral_eq
    (f:=fun z => star (F.val z)*G.val z) (cubicThetaPrimeDoubleRootWeylImage_fundamental hp)
    (cubicThetaPrimeDoubleRoot_pair_invariant hp F G)
  have hm := (measurePreserving_smul (cubicThetaPrimeDoubleRootWeylElement hp)
    cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul (cubicThetaPrimeDoubleRootWeylElement hp))
    (fun z => star (F.val z)*G.val z) (cubicThetaPrimeDoubleRootDomain hp)
  exact (he.trans hm).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDoubleRootOrthogonal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The twice-squared dilation has a nontrivial diagonal character.
Its actual integral pairing with global sections vanishes. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeDoubleRootWeyl_global_transform {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori ((p^2)^2)) (F : CubicThetaSection) (x : CubicThetaPoint) :
    (cubicThetaPrimeDoubleRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F)).val (g.val • x)=
      star ((cubicSymbol p (g.val.val 0 0))^4)*cubicThetaKubotaValue g.val*
        (cubicThetaPrimeDoubleRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F)).val x := by
  let D := cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero)
  have h1 := cubicThetaPrimeDilation_intertwines (cubicThetaPrimeDouble_primary hp)
    (cubicThetaPrimeSquareIwahori g)
  have h2 := cubicThetaPrimeDilation_intertwines (cubicThetaPrimeDouble_primary hp)
    (cubicThetaPrimeDoubleSquareConjugate hp g)
  change D*cubicThetaPrincipalComplex g.val=
    cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
      (cubicThetaPrimeSquareIwahori g))*D at h1
  change D*cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
    (cubicThetaPrimeSquareIwahori g))=
    cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
      (cubicThetaPrimeDoubleSquareConjugate hp g))*D at h2
  have he : D*(D*cubicThetaPrincipalComplex g.val)=
      cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
        (cubicThetaPrimeDoubleSquareConjugate hp g))*(D*D) := by
    rw [h1,←mul_assoc,h2,mul_assoc]
  rw [cubicThetaPrimeDoubleRootWeyl_global_zero,cubicThetaPrimeDoubleRootWeyl_global_zero]
  change (cubicThetaInversionSection F).val (D • (D • (cubicThetaPrincipalComplex g.val • x)))=_
  rw [←mul_smul,←mul_smul,mul_assoc,he,mul_smul,mul_smul]
  change (cubicThetaInversionSection F).val
    (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
      (cubicThetaPrimeDoubleSquareConjugate hp g) • (D • (D • x)))=_
  rw [(cubicThetaInversionSection F).property,cubicThetaPrimeDoubleSquareConjugate_kubota]

lemma cubicThetaPrimeDoubleRootWeyl_pair_zero {p : Eisenstein} (hp : primaryPrime p)
    (F G : CubicThetaSection) :
    (∫ x in cubicThetaPrimeDoubleRootDomain hp,star (F.val x)*
      (cubicThetaPrimeDoubleRootWeylSection hp (cubicThetaPrimeRootSectionRestrict G)).val x
        ∂cubicThetaPointMeasure)=0 := by
  let H := cubicThetaPrimeDoubleRootWeylSection hp (cubicThetaPrimeRootSectionRestrict G)
  let f : CubicThetaPoint → ℂ := fun x => star (F.val x)*H.val x
  obtain ⟨g,hg⟩ := cubicThetaPrimeSixthCharacter_nontrivial hp
  let j : cubicThetaPrimeIwahori ((p^2)^2) := ⟨g.val,by
    change (p^2)^2∣g.val.val 1 0
    have hd : p^4∣g.val.val 1 0 := (pow_dvd_pow p (by decide : 4≤6)).trans g.property
    simpa only [←pow_mul] using hd⟩
  let c : ℂ := star ((cubicSymbol p (g.val.val 0 0))^4)
  have hc : c≠1 := by
    have h3 : (cubicSymbol p (g.val.val 0 0))^3=1 :=
      cubicThetaPrimeIwahoriCharacter_cube hp (cubicThetaPrimeSixthIwahori g)
    intro he
    have he' : (cubicSymbol p (g.val.val 0 0))^4=1 := by
      simpa only [c,star_star,star_one] using congrArg star he
    rw [show (cubicSymbol p (g.val.val 0 0))^4=(cubicSymbol p (g.val.val 0 0))^3*
      cubicSymbol p (g.val.val 0 0) by ring,h3,one_mul] at he'
    exact hg he'
  have hi := (cubicThetaPrimeDoubleRootDomain_fundamental hp).setIntegral_eq (f:=f)
    (cubicThetaPrimeDoubleRootIwahoriImage_fundamental hp (cubicThetaPrimeSixthPowerIwahori 2 (by decide) g))
    (cubicThetaPrimeDoubleRoot_pair_invariant hp (cubicThetaPrimeRootSectionRestrict F) H)
  have hm := (measurePreserving_smul g.val cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul g.val) f (cubicThetaPrimeDoubleRootDomain hp)
  have he : (∫ x in cubicThetaPrimeDoubleRootDomain hp,f x ∂cubicThetaPointMeasure)=
      ∫ x in cubicThetaPrimeDoubleRootDomain hp,f (g.val • x) ∂cubicThetaPointMeasure := hi.trans hm
  have hfun : (fun x => f (g.val • x))=fun x => c*f x := by
    funext x
    have hG := cubicThetaPrimeDoubleRootWeyl_global_transform hp j G x
    change H.val (g.val • x)=c*cubicThetaKubotaValue g.val*H.val x at hG
    dsimp only [f]
    rw [F.property,hG,star_mul]
    have hk : star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val=1 := by
      rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
      norm_num
    calc
      _ = (star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val)*
        (c*(star (F.val x)*H.val x)) := by ring
      _ = _ := by rw [hk,one_mul]
  rw [hfun,integral_const_mul] at he
  exact eq_zero_of_mul_eq_self_left hc he.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeDoubleRootTranslationIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nontrivial translations at the intermediate denominator have zero
integral correlation, by the proved Bruhat identity and character cancellation. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaPrimeDoubleRootWeyl_translated_global {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^2∣9*x*y-1) (F : CubicThetaSection) :
    cubicThetaPrimeDoubleRootWeylSection hp
      (cubicThetaPrimeDoubleRootSectionTranslate hp y (cubicThetaPrimeRootSectionRestrict F))=
      cubicSymbol (p^2) (3*y) • cubicThetaPrimeDoubleRootSectionTranslate hp (-x)
        (cubicThetaPrimeRootSectionRestrict (cubicThetaInversionSection F)) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  change F.val (cubicThetaPrimeDoubleRootElement hp y • (cubicThetaPrimeDoubleRootWeylElement hp • z))=
    cubicSymbol (p^2) (3*y)*(cubicThetaInversionSection F).val (cubicThetaPrimeDoubleRootElement hp (-x) • z)
  have he := cubicThetaPrimeDoubleRootBruhat_section hp x y hxy F (cubicThetaPrimeDoubleRootElement hp (-x) • z)
  have hx : cubicThetaPrimeDoubleRootElement hp x • (cubicThetaPrimeDoubleRootElement hp (-x) • z)=z := by
    rw [←mul_smul,←cubicThetaPrimeDoubleRootElement_add,add_neg_cancel,cubicThetaPrimeDoubleRootElement_zero,one_smul]
  rw [hx] at he
  exact he

theorem cubicThetaPrimeDoubleRoot_translation_integral_zero {p : Eisenstein}
    (hp : primaryPrime p) (x : Eisenstein) (hx : ¬p∣x) (F G : CubicThetaSection) :
    (∫ z in cubicThetaPrimeDoubleRootDomain hp,star (F.val z)*
      G.val (cubicThetaPrimeDoubleRootElement hp x • z) ∂cubicThetaPointMeasure)=0 := by
  have hpx : IsCoprime p x := hp.2.coprime_iff_not_dvd.mpr hx
  have hp9 : IsCoprime p (9:Eisenstein) := by
    simpa only [show (3:Eisenstein)^2=9 by norm_num] using (primary_coprime_three hp.1).pow_right (n:=2)
  have hcop : IsCoprime (p^2) (9*x) := (hp9.mul_right hpx).pow_left
  obtain ⟨a,y,hxy⟩ := hcop
  have hd : p^2∣9*y*x-1 := ⟨-a,by linear_combination hxy⟩
  let A := cubicThetaPrimeRootSectionRestrict (p:=p^2) F
  let B := cubicThetaPrimeDoubleRootSectionTranslate hp x (cubicThetaPrimeRootSectionRestrict G)
  let H := cubicThetaPrimeDoubleRootWeylSection hp A
  let J := cubicThetaPrimeRootSectionRestrict (p:=p^2) (cubicThetaInversionSection G)
  let K := cubicThetaPrimeDoubleRootSectionTranslate hp (-y) J
  let c := cubicSymbol (p^2) (3*x)
  have hBruhat : cubicThetaPrimeDoubleRootWeylSection hp B=c • K :=
    cubicThetaPrimeDoubleRootWeyl_translated_global hp y x hd G
  have hH (z : CubicThetaPoint) : H.val (cubicThetaPrimeDoubleRootElement hp (-y) • z)=H.val z :=
    congrArg (fun T : cubicThetaPrimeDoubleRootSections p => T.val z)
      (cubicThetaPrimeDoubleRootWeyl_global_translate hp (-y) F)
  have hpair : (∫ z in cubicThetaPrimeDoubleRootDomain hp,star (H.val z)*K.val z ∂cubicThetaPointMeasure)=
      ∫ z in cubicThetaPrimeDoubleRootDomain hp,star (H.val z)*J.val z ∂cubicThetaPointMeasure := by
    change (∫ z in cubicThetaPrimeDoubleRootDomain hp,star (H.val z)*
      J.val (cubicThetaPrimeDoubleRootElement hp (-y) • z) ∂cubicThetaPointMeasure)=_
    have he := cubicThetaPrimeDoubleRoot_pair_translation hp (-y) H J
    simpa only [hH] using he
  have hzero : (∫ z in cubicThetaPrimeDoubleRootDomain hp,star (H.val z)*J.val z
      ∂cubicThetaPointMeasure)=0 := by
    have he := congrArg star (cubicThetaPrimeDoubleRootWeyl_pair_zero hp (cubicThetaInversionSection G) F)
    rw [cubicThetaComplexPair_flip,star_zero] at he
    exact he
  calc
    _ = ∫ z in cubicThetaPrimeDoubleRootDomain hp,
        star ((cubicThetaPrimeDoubleRootWeylSection hp A).val z)*
          (cubicThetaPrimeDoubleRootWeylSection hp B).val z ∂cubicThetaPointMeasure :=
      (cubicThetaPrimeDoubleRoot_pair_weyl hp A B).symm
    _ = ∫ z in cubicThetaPrimeDoubleRootDomain hp,
        c*(star (H.val z)*K.val z) ∂cubicThetaPointMeasure := by
      rw [hBruhat]
      apply integral_congr_ae
      filter_upwards with z
      change star (H.val z)*(c*K.val z)=c*(star (H.val z)*K.val z)
      ring
    _ = c*(∫ z in cubicThetaPrimeDoubleRootDomain hp,star (H.val z)*K.val z
        ∂cubicThetaPointMeasure) := integral_const_mul c _
    _ = 0 := by rw [hpair,hzero,mul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootSecondIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport of intermediate root orthogonality to the cubic root cover. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeDoubleRoot_translate_pair_invariant {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F G : CubicThetaSection)
    (g : cubicThetaPrimeDoubleRootSubgroup p) (z : CubicThetaPoint) :
    star (F.val (g • z))*G.val (cubicThetaPrimeDoubleRootElement hp x • (g • z))=
      star (F.val z)*G.val (cubicThetaPrimeDoubleRootElement hp x • z) :=
  cubicThetaPrimeDoubleRoot_pair_invariant hp (cubicThetaPrimeRootSectionRestrict F)
    (cubicThetaPrimeDoubleRootSectionTranslate hp x (cubicThetaPrimeRootSectionRestrict G)) g z

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootWeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubic character at the cube modulus is the literal unit detector. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRoot_gauss_zero {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 3 0=
      (norm p:ℂ)^3-(norm p:ℂ)^2 := by
  have he := cubicThetaLocalPrimePowerGauss_reduction hp 2 0
  change cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 3 (p^2*0)=
    (norm (p^2):ℂ)*cubicThetaPrimeFourier p hp 3 0 at he
  rw [mul_zero,cubicThetaPrimeFourier_three hp 0,ite_eq_left (dvd_zero p),
    eisenstein_norm_pow,Complex.ofReal_pow] at he
  rw [he]
  ring

end CubicFirstMoment

end

end OAI
end


