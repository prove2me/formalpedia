-- Prove2me | Definitions.Def_OAIQ096A021
-- name    : OAIQ096A021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T03:55:52.343223+00:00
-- url     : https://prove2.me/theorems/c351db70-48a8-4e52-b73a-a5dfd3398721
-- title:
--   Definitions bundle OAIQ096A021 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 120 declarations of OpenAI's Lean: 18 definitions and 102 theorems. The definitions and types are `OAI.CubicFirstMoment.cubicThetaArithmeticEnergy`, `OAI.CubicFirstMoment.cubicThetaArithmeticFiniteEnergy`, `OAI.CubicFirstMoment.cubicThetaArithmeticGradientL2`, `OAI.CubicFirstMoment.cubicThetaArithmeticL2`, `OAI.CubicFirstMoment.cubicThetaArithmeticWeakDefect`, `OAI.CubicFirstMoment.cubicThetaCuspLogSection`, `OAI.CubicFirstMoment.cubicThetaEnergyRegularizer`, `OAI.CubicFirstMoment.cubicThetaInversionEnergy`, `OAI.CubicFirstMoment.cubicThetaInversionFinite`, `OAI.CubicFirstMoment.cubicThetaInversionFiniteExtension`, `OAI.CubicFirstMoment.cubicThetaInversionFiniteLinear`, `OAI.CubicFirstMoment.cubicThetaInversionRawEnergy`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeAdjointFinite`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeHeckeAdjoint`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeHeckeEnergy`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeHeckeRawEnergy`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootLiftL2`, `OAI.CubicFirstMoment.principalZetaRegularFactor`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `CubicMoment_Estimates_PrincipalZetaPole`, `CubicMoment_Theta_CubicThetaArithmeticChartWeak`, `CubicMoment_Theta_CubicThetaArithmeticCuspMass`, `CubicMoment_Theta_CubicThetaArithmeticDistribution`, `CubicMoment_Theta_CubicThetaArithmeticEnergy`, `CubicMoment_Theta_CubicThetaArithmeticEnergyGraph`, `CubicMoment_Theta_CubicThetaArithmeticGlobalWeak`, `CubicMoment_Theta_CubicThetaArithmeticGradientL2`, `CubicMoment_Theta_CubicThetaArithmeticL2`, `CubicMoment_Theta_CubicThetaArithmeticResolvent`, `CubicMoment_Theta_CubicThetaArithmeticWeakDefect`, `CubicMoment_Theta_CubicThetaCompactEnergyCorrection`, `CubicMoment_Theta_CubicThetaContinuedWeakEquation`, `CubicMoment_Theta_CubicThetaCuspCoreEnergy`, `CubicMoment_Theta_CubicThetaCuspCutoffEnergy`, `CubicMoment_Theta_CubicThetaCuspDerivativeIntegral`, `CubicMoment_Theta_CubicThetaCuspExteriorMass`, `CubicMoment_Theta_CubicThetaCuspIntegratedHardy`, `CubicMoment_Theta_CubicThetaCuspLogSection`, `CubicMoment_Theta_CubicThetaCuspMassIntegral`, `CubicMoment_Theta_CubicThetaCuspRestriction`, `CubicMoment_Theta_CubicThetaCuspScalarIntegrals`, `CubicMoment_Theta_CubicThetaCuspSectionHardy`, `CubicMoment_Theta_CubicThetaCuspStripReduction`, `CubicMoment_Theta_CubicThetaCuspVerticalEnergy`, `CubicMoment_Theta_CubicThetaEnergyIntegralIdentities`, `CubicMoment_Theta_CubicThetaEnergyInverseContinuation`, `CubicMoment_Theta_CubicThetaEnergyPencilKernel`, `CubicMoment_Theta_CubicThetaEnergyRegularDomain`, `CubicMoment_Theta_CubicThetaEnergyRegularizer`, `CubicMoment_Theta_CubicThetaEnergyResolventTransport`, `CubicMoment_Theta_CubicThetaExceptionalProjection`, `CubicMoment_Theta_CubicThetaExteriorEnergy`, `CubicMoment_Theta_CubicThetaExteriorIntegral`, `CubicMoment_Theta_CubicThetaFiniteCuspEnergy`, `CubicMoment_Theta_CubicThetaFiniteEnergySections`, `CubicMoment_Theta_CubicThetaForcedCusp`, `CubicMoment_Theta_CubicThetaForcedResolvent`, `CubicMoment_Theta_CubicThetaGlobalMeromorphic`, `CubicMoment_Theta_CubicThetaGlobalResolventWeak`, `CubicMoment_Theta_CubicThetaIntegralQuotient`, `CubicMoment_Theta_CubicThetaInversionEnergy`, `CubicMoment_Theta_CubicThetaInversionFiniteCompletion`, `CubicMoment_Theta_CubicThetaInversionFiniteEnergy`, `CubicMoment_Theta_CubicThetaInversionPairing`, `CubicMoment_Theta_CubicThetaLocalEnergyResolvent`, `CubicMoment_Theta_CubicThetaPointC1Hecke`, `CubicMoment_Theta_CubicThetaPointC1Trace`, `CubicMoment_Theta_CubicThetaPrimeCubeCompletedAdjoint`, `CubicMoment_Theta_CubicThetaPrimeCubeFiniteAdjoint`, `CubicMoment_Theta_CubicThetaPrimeCubeHeckeEnergyOperator`, `CubicMoment_Theta_CubicThetaPrimeCubeRootDilationFixed`, `CubicMoment_Theta_CubicThetaPrimeCubeRootLiftL2`, `CubicMoment_Theta_CubicThetaTranslatedCuspStrip`, `CubicMoment_Theta_CubicThetaWeakUniqueness`.
--
--   **Imports.** It imports the published bundle `Def_PattersonFirstMoment`; the bundles `OAIQ096A016` and `OAIQ096A017` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ096A024` and `OAIQ096A025`; the statements `OAI_CubicFirstMoment_ProfileControl_low_coprime_mellin_height_log_saving`, `OAI_CubicFirstMoment_UniformLogWeights_cubeModelTerm_mass_error`, `OAI_CubicFirstMoment_UniformLogWeights_metaplectic_twisted_tail_arbitrary_power`, `OAI_CubicFirstMoment_angular_distinguishedHighScaleRows_isLittleO_actual`, `OAI_CubicFirstMoment_angular_distinguishedLowScaleRows_two_stage`, `OAI_CubicFirstMoment_angular_divisor_full_model_asymptotic`, `OAI_CubicFirstMoment_angular_divisor_noncube_annulus_saving`, `OAI_CubicFirstMoment_angular_height_coprime_mellin_saving`, `OAI_CubicFirstMoment_angular_height_poisson_total_saving`, `OAI_CubicFirstMoment_angular_noncube_poisson_dyadic_saving`, `OAI_CubicFirstMoment_angular_primeProductGaussTail_scale_decomposition`, `OAI_CubicFirstMoment_angular_semiprime_smoothed_log_saving_actual`, `OAI_CubicFirstMoment_angular_sieved_squarefree_model_asymptotic`, `OAI_CubicFirstMoment_angular_stopped_divisor_full_model_log_saving`, `OAI_CubicFirstMoment_angular_stopped_divisor_noncube_dyadic`, `OAI_CubicFirstMoment_angular_stopped_mixed_model_log_saving`, `OAI_CubicFirstMoment_angular_stopped_squarefree_model_log_saving`, `OAI_CubicFirstMoment_angular_upperStoppedTail_bound_uniform`, `OAI_CubicFirstMoment_bounded_rough_divisor_variance_remainder`, `OAI_CubicFirstMoment_cubicThetaFullDual_radial_voronoi`, `OAI_CubicFirstMoment_cubicTheta_completed_voronoi`, `OAI_CubicFirstMoment_cubicTheta_height_voronoi`, `OAI_CubicFirstMoment_cubicTheta_radial_upperLowTail_isLittleO_uniform`, `OAI_CubicFirstMoment_distinguishedHighScaleRows_isLittleO_actual`, `OAI_CubicFirstMoment_distinguishedLowScaleRows_two_stage`, `OAI_CubicFirstMoment_distinguishedStoppedDyad_early_bound_actual`, `OAI_CubicFirstMoment_distinguishedStoppedLate_bound`, `OAI_CubicFirstMoment_divisor_coprime_gram_asymptotic`, `OAI_CubicFirstMoment_divisor_high_poisson_log_saving`, `OAI_CubicFirstMoment_height_coprime_mellin_saving`, `OAI_CubicFirstMoment_height_poisson_total_saving`, `OAI_CubicFirstMoment_large_tuple_restricted_smoothed_actual`, `OAI_CubicFirstMoment_large_tuple_triple_transition_smoothed`, `OAI_CubicFirstMoment_low_shrinking_variance_remainder`, `OAI_CubicFirstMoment_metaplectic_actual_retained_mean`, `OAI_CubicFirstMoment_prime_variance_transition_bound`, `OAI_CubicFirstMoment_scaleFirstLow_sub_stopped_isLittleO_actual`, `OAI_CubicFirstMoment_scaleFirstMiddleSum_isLittleO_actual`, `OAI_CubicFirstMoment_scaleFirstOrdinaryStoppedTail_isLittleO`, `OAI_CubicFirstMoment_semiprimeGaussTail_angular_piece_log_saving`, `OAI_CubicFirstMoment_semiprimeGaussTail_hecke_window`, `OAI_CubicFirstMoment_semiprimeGaussTail_isLittleO`, `OAI_CubicFirstMoment_semiprimeGaussTail_middle_window`, `OAI_CubicFirstMoment_semiprime_piece_log_saving_actual`, `OAI_CubicFirstMoment_sharp_prime_product_log_height_remainder`, `OAI_CubicFirstMoment_sieved_squarefree_model_asymptotic`, `OAI_CubicFirstMoment_stopped_divisor_coprime_model_log_saving`, `OAI_CubicFirstMoment_stopped_divisor_noncube_dyadic`, `OAI_CubicFirstMoment_stopped_squarefree_model_log_saving`, `OAI_CubicFirstMoment_tailPrime_hecke_window`, `OAI_CubicFirstMoment_tailPrime_ordinary_tuple_bound`, `OAI_CubicFirstMoment_typeI_product_low_integral_actual` and `OAI_CubicFirstMoment_upperStoppedTail_bound_uniform`; the proofs of `OAI_CubicFirstMoment_ProfileControl_low_coprime_height_real`, `OAI_CubicFirstMoment_ProfileControl_low_coprime_mellin_height_log_saving`, `OAI_CubicFirstMoment_ProfileControl_smallB_nonzero_variance_height_power`, `OAI_CubicFirstMoment_ProfileControl_smallB_radial_form_height_power`, `OAI_CubicFirstMoment_ShortFactorFamily_first_rows_contradiction`, `OAI_CubicFirstMoment_UniformLogWeights_cubeModelTerm_mass_error`, `OAI_CubicFirstMoment_UniformLogWeights_cubicTheta_completed_dilated_long_mean`, `OAI_CubicFirstMoment_UniformLogWeights_cubicTheta_completed_dilated_negative_long_mean`, `OAI_CubicFirstMoment_UniformLogWeights_cubicTheta_radial_remainder_dilated_long_mean`, `OAI_CubicFirstMoment_UniformLogWeights_metaplectic_twisted_tail_arbitrary_power`, `OAI_CubicFirstMoment_angular_corrected_dispersion_asymptotic_actual`, `OAI_CubicFirstMoment_angular_distinguishedHighScaleRows_isLittleO_actual`, `OAI_CubicFirstMoment_angular_distinguishedLowScaleRows_two_stage`, `OAI_CubicFirstMoment_angular_distinguishedStoppedDyad_early_bound_actual`, `OAI_CubicFirstMoment_angular_distinguishedStoppedLate_bound`, `OAI_CubicFirstMoment_angular_divisor_full_model_asymptotic`, `OAI_CubicFirstMoment_angular_divisor_noncube_annulus_saving`, `OAI_CubicFirstMoment_angular_full_exceptional_structured_moment`, `OAI_CubicFirstMoment_angular_full_prime_product_height_bilinear`, `OAI_CubicFirstMoment_angular_height_coprime_mellin_saving`, `OAI_CubicFirstMoment_angular_height_poisson_total_saving`, `OAI_CubicFirstMoment_angular_largePrimeTupleOrdinaryHighSum_isLittleO_actual`, `OAI_CubicFirstMoment_angular_largePrimeTuplePiece_flat_high_bound`, `OAI_CubicFirstMoment_angular_largePrimeTuplePiece_nonflat_high_bound_actual`, `OAI_CubicFirstMoment_angular_noncube_poisson_dyadic_saving`, `OAI_CubicFirstMoment_angular_primeProductGaussTail_scale_decomposition`, `OAI_CubicFirstMoment_angular_scaleFirstMiddleSum_isLittleO_actual`, `OAI_CubicFirstMoment_angular_scaleFirstOrdinaryStoppedTail_isLittleO`, `OAI_CubicFirstMoment_angular_semiprime_smoothed_log_saving_actual`, `OAI_CubicFirstMoment_angular_sieved_squarefree_model_asymptotic`, `OAI_CubicFirstMoment_angular_stopped_divisor_full_model_log_saving`, `OAI_CubicFirstMoment_angular_stopped_divisor_noncube_dyadic`, `OAI_CubicFirstMoment_angular_stopped_mixed_model_log_saving`, `OAI_CubicFirstMoment_angular_stopped_norm_mellin_integral`, `OAI_CubicFirstMoment_angular_stopped_squarefree_model_log_saving`, `OAI_CubicFirstMoment_angular_tailPrime_ordinary_tuple_bound`, `OAI_CubicFirstMoment_angular_two_prime_transition_height`, `OAI_CubicFirstMoment_angular_upperLowTail_isLittleO_uniform_proved`, `OAI_CubicFirstMoment_angular_upperStoppedTail_bound_uniform`, `OAI_CubicFirstMoment_bounded_rough_divisor_variance_remainder`, `OAI_CubicFirstMoment_cubicThetaArithmeticBaseScalar_sign`, `OAI_CubicFirstMoment_cubicThetaArithmeticRankinMass_residue`, `OAI_CubicFirstMoment_cubicThetaFullDual_radial_voronoi`, `OAI_CubicFirstMoment_cubicTheta_completed_voronoi`, `OAI_CubicFirstMoment_cubicTheta_height_voronoi`, `OAI_CubicFirstMoment_cubicTheta_radial_upperLowTail_isLittleO_uniform`, `OAI_CubicFirstMoment_cubic_gram_large_value_count`, `OAI_CubicFirstMoment_distinguishedHighScaleRows_isLittleO_actual`, `OAI_CubicFirstMoment_distinguishedLowScaleRows_two_stage`, `OAI_CubicFirstMoment_distinguishedStoppedDyad_early_bound_actual`, `OAI_CubicFirstMoment_distinguishedStoppedLate_bound`, `OAI_CubicFirstMoment_divisor_coprime_gram_asymptotic`, `OAI_CubicFirstMoment_divisor_high_poisson_log_saving`, `OAI_CubicFirstMoment_full_exceptional_structured_moment`, `OAI_CubicFirstMoment_height_coprime_mellin_saving`, `OAI_CubicFirstMoment_height_poisson_total_saving`, `OAI_CubicFirstMoment_largePrimeTuplePiece_flat_high_bound`, `OAI_CubicFirstMoment_largePrimeTuplePiece_nonflat_high_bound_actual`, `OAI_CubicFirstMoment_large_tuple_restricted_smoothed_actual`, `OAI_CubicFirstMoment_large_tuple_triple_transition_smoothed`, `OAI_CubicFirstMoment_logCell_bilinear_height_square`, `OAI_CubicFirstMoment_low_logCell_bilinear_height_square`, `OAI_CubicFirstMoment_low_shrinking_variance_remainder`, `OAI_CubicFirstMoment_metaplectic_actual_retained_mean`, `OAI_CubicFirstMoment_normalized_angular_twisted_primitive_ideal_cubic_moment`, `OAI_CubicFirstMoment_normalized_twisted_primitive_ideal_cubic_moment`, `OAI_CubicFirstMoment_primeGroupTail_common_row_height_power`, `OAI_CubicFirstMoment_primeGroupTail_wide_bilinear_log_saving`, `OAI_CubicFirstMoment_prime_variance_transition_bound`, `OAI_CubicFirstMoment_rough_prime_corrected_bilinear_actual`, `OAI_CubicFirstMoment_scaleFirstLow_sub_stopped_isLittleO_actual`, `OAI_CubicFirstMoment_scaleFirstMiddleSum_isLittleO_actual`, `OAI_CubicFirstMoment_scaleFirstOrdinaryStoppedTail_isLittleO`, `OAI_CubicFirstMoment_semiprimeGaussTail_angular_piece_log_saving`, `OAI_CubicFirstMoment_semiprimeGaussTail_hecke_window`, `OAI_CubicFirstMoment_semiprimeGaussTail_isLittleO`, `OAI_CubicFirstMoment_semiprimeGaussTail_middle_window`, `OAI_CubicFirstMoment_semiprime_piece_log_saving_actual`, `OAI_CubicFirstMoment_sharp_prime_product_log_height_remainder`, `OAI_CubicFirstMoment_sieved_squarefree_model_asymptotic`, `OAI_CubicFirstMoment_stopped_corrected_dispersion_log_saving_actual`, `OAI_CubicFirstMoment_stopped_divisor_coprime_model_log_saving`, `OAI_CubicFirstMoment_stopped_divisor_noncube_dyadic`, `OAI_CubicFirstMoment_stopped_norm_mellin_integral`, `OAI_CubicFirstMoment_stopped_squarefree_model_log_saving`, `OAI_CubicFirstMoment_tailPrime_hecke_group`, `OAI_CubicFirstMoment_tailPrime_hecke_window`, `OAI_CubicFirstMoment_tailPrime_ordinary_tuple_bound`, `OAI_CubicFirstMoment_typeI_product_low_integral_actual`, `OAI_CubicFirstMoment_uniform_cubicTheta_centered_subpower`, `OAI_CubicFirstMoment_uniform_cubicTheta_radial_remainder_low` and `OAI_CubicFirstMoment_upperStoppedTail_bound_uniform`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A016
import Definitions.Def_OAIQ096A017

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrincipalZetaPole
attribute [-instance] _root_.instMeasurableSpace
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

def principalZetaRegularFactor (s : ℂ) : ℂ :=
  principalZetaPrefactor s*((s-1)*(principalIdealFEPair.Λ₀ s-principalThetaConstant/s)+
    principalThetaConstant)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaGlobalEnergySpace_complete _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual arithmetic remainder has a continuous invariant
Dirichlet energy density. No energy membership is assumed here. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaArithmeticEnergy_invariant {s : ℂ} (hs : 2 < s.re)
    (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    cubicThetaSectionEnergy (cubicThetaArithmeticSection s hs) (g • p)=
      cubicThetaSectionEnergy (cubicThetaArithmeticSection s hs) p := by
  have he := congrArg cubicThetaTangentEnergy (cubicThetaArithmeticDifferential_automorphy hs g p)
  rw [cubicThetaTangentEnergy_derivative _ _ p.property,
    cubicThetaTangentEnergy_complex_smul,cubicThetaKubotaValue_norm,one_pow,one_mul] at he
  change (cubicThetaMobius (cubicThetaPrincipalComplex g) p.val).2^2*
    cubicThetaTangentEnergy (cubicThetaSectionDifferential (cubicThetaArithmeticSection s hs) (g • p))=
    p.val.2^2*cubicThetaTangentEnergy (cubicThetaSectionDifferential (cubicThetaArithmeticSection s hs) p)
  calc
    _ = p.val.2^2*(((cubicThetaMobius (cubicThetaPrincipalComplex g) p.val).2/p.val.2)^2*
        cubicThetaTangentEnergy (cubicThetaSectionDifferential (cubicThetaArithmeticSection s hs) (g • p))) := by
      field_simp [p.property.ne']
    _ = _ := by rw [he]

lemma cubicThetaArithmeticQuotientEnergy_apply (s : ℂ) (hs : 2 < s.re) (p : CubicThetaPoint) :
    cubicThetaArithmeticQuotientEnergy s hs (cubicThetaQuotientMap p)=
      cubicThetaSectionEnergy (cubicThetaArithmeticSection s hs) p := by
  have he := cubicThetaQuotientLift_map (cubicThetaQuotientMap p)
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  unfold cubicThetaArithmeticQuotientEnergy
  rw [← hg,cubicThetaArithmeticEnergy_invariant]

lemma cubicThetaArithmeticQuotientEnergy_continuous (s : ℂ) (hs : 2 < s.re) :
    Continuous (cubicThetaArithmeticQuotientEnergy s hs) := by
  apply cubicThetaQuotientMap_open.isQuotientMap.continuous_iff.mpr
  have he : cubicThetaArithmeticQuotientEnergy s hs ∘ cubicThetaQuotientMap=
      cubicThetaSectionEnergy (cubicThetaArithmeticSection s hs) :=
    funext (cubicThetaArithmeticQuotientEnergy_apply s hs)
  rw [he]
  exact cubicThetaArithmeticEnergy_continuous hs

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTranslatedCuspStrip
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every arithmetic cusp strip remains injective after an integral
Mobius transformation. Normality of the actual level-three group and
invariance of hyperbolic measure give the exact transported integrals. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaTranslatedCuspStrip_integral (δ : SL(2,Eisenstein)) {H : ℝ} (hH : 1≤H)
    (f : CubicThetaQuotient → ℝ) (hf : StronglyMeasurable f) :
    (∫ q in cubicThetaQuotientMap '' cubicThetaTranslatedCuspStrip δ H,
      f q ∂cubicThetaQuotientMeasure)=
      ∫ p in cubicThetaCuspStrip H, f (cubicThetaQuotientMap (δ • p)) ∂cubicThetaPointMeasure := by
  rw [cubicThetaInjective_integral (cubicThetaTranslatedCuspStrip_measurable δ H)
    (cubicThetaTranslatedCuspStrip_injective δ hH) f hf]
  change (∫ p, f (cubicThetaQuotientMap p) ∂cubicThetaPointMeasure.restrict
    ((fun p : CubicThetaPoint => δ • p) '' cubicThetaCuspStrip H))=_
  rw [← cubicThetaSmul_map_restrict δ (cubicThetaCuspStrip_measurable H)]
  exact integral_map_of_stronglyMeasurable (measurable_const_smul δ)
    (hf.comp_measurable cubicThetaQuotientMap_open.continuous.measurable)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspStripReduction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Horizontal reduction into the exact half-open cusp strip uses the
actual principal translations. It is compatible with every arithmetic
cusp through the proved conjugation in the level-three group. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCuspNeighborhood_measurable (δ : SL(2,Eisenstein)) {H : ℝ} (hH : 1≤H) :
    MeasurableSet (cubicThetaCuspNeighborhood δ H) :=
  cubicThetaQuotient_injective_image_measurable (cubicThetaTranslatedCuspStrip_measurable δ H)
    (cubicThetaTranslatedCuspStrip_injective δ hH)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticChartWeak
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate weak equation descends, with its exact measure, to
compactly supported periodized tests in every injective sheet. -/
noncomputable section
open Set Filter Topology MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaArithmeticSectionFunction_axisFirst {s : ℂ} (hs : 2 < s.re)
    (k : CubicThetaAxis) {p : ℂ × ℝ} (hp : 0<p.2) :
    cubicThetaAxisFirst k (cubicThetaSectionFunction (cubicThetaArithmeticSection s hs)) p=
      cubicThetaAxisFirst k (fun y => cubicThetaArithmeticRemainder y s) p := by
  have he : cubicThetaSectionFunction (cubicThetaArithmeticSection s hs)=ᶠ[𝓝 p]
      (fun y => cubicThetaArithmeticRemainder y s) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hp] with y hy
    rw [cubicThetaSectionFunction_apply _ hy]
    rfl
  have hf := ((cubicThetaArithmeticSectionFunction_contDiffOn_one hs).contDiffAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)).differentiableAt (by norm_num)
  have hg := ((cubicThetaArithmeticRemainder_contDiffOn_one hs).contDiffAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)).differentiableAt (by norm_num)
  rw [cubicThetaAxisFirst_eq_fderiv _ _ hf,cubicThetaAxisFirst_eq_fderiv _ _ hg,he.fderiv_eq]

lemma cubicThetaArithmetic_chart_weak {s : ℂ} (hs : 2 < s.re)
    {g : ℂ × ℝ → ℂ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {K : Set (ℂ × ℝ)} (hK : IsCompact K) (hp : K⊆{y : ℂ × ℝ | 0<y.2})
    (hgs : tsupport g⊆K)
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hKe : cubicThetaPointInclusion.symm '' K⊆e.source) :
    let P := cubicThetaPoincareSection (cubicThetaCoordinateSeed g hg.continuous hc (hgs.trans hp))
    (∫ q, cubicThetaC1Pairing P (cubicThetaArithmeticSection s hs) q ∂cubicThetaQuotientMeasure)+
      s*(s-2)*(∫ q, cubicThetaSectionPairing P (cubicThetaArithmeticSection s hs) q
        ∂cubicThetaQuotientMeasure)=
      ∫ q, cubicThetaSectionPairing P (cubicThetaForcingSection s) q ∂cubicThetaQuotientMeasure := by
  intro P
  rw [cubicThetaCoordinateSection_gradient_pairing hg hc hK hp hgs e he hKe _
    (cubicThetaArithmeticSectionFunction_contDiffOn_one hs),
    cubicThetaCoordinateSection_mass_pairing hg hc hK hp hgs e he hKe,
    cubicThetaCoordinateSection_mass_pairing hg hc hK hp hgs e he hKe]
  have hG : (∫ y in K, cubicThetaHeightInverse y*cubicThetaCoordinatePairing g
      (cubicThetaSectionFunction (cubicThetaArithmeticSection s hs)) y)=
      ∫ y, cubicThetaHeightInverse y*cubicThetaCoordinatePairing g
        (fun z => cubicThetaArithmeticRemainder z s) y := by
    calc
      _ = ∫ y in K, cubicThetaHeightInverse y*cubicThetaCoordinatePairing g
          (fun z => cubicThetaArithmeticRemainder z s) y := by
        apply setIntegral_congr_fun hK.measurableSet
        intro y hy
        simp only [cubicThetaCoordinatePairing,cubicThetaArithmeticSectionFunction_axisFirst hs _ (hp hy)]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
        rw [cubicThetaCoordinatePairing_zero_left (fun h => hy (hgs h)),mul_zero])
  have hM : (∫ y in K, star (g y)*cubicThetaSectionFunction (cubicThetaArithmeticSection s hs) y/(y.2:ℂ)^3)=
      ∫ y, star (g y)*cubicThetaArithmeticRemainder y s/(y.2:ℂ)^3 := by
    calc
      _ = ∫ y in K, star (g y)*cubicThetaArithmeticRemainder y s/(y.2:ℂ)^3 := by
        apply setIntegral_congr_fun hK.measurableSet
        intro y hy
        dsimp only
        rw [cubicThetaSectionFunction_apply _ (hp hy)]
        rfl
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hgs h)),star_zero,zero_mul,zero_div])
  have hF : (∫ y in K, star (g y)*cubicThetaSectionFunction (cubicThetaForcingSection s) y/(y.2:ℂ)^3)=
      ∫ y, star (g y)*cubicThetaForcingSeries y s/(y.2:ℂ)^3 := by
    calc
      _ = ∫ y in K, star (g y)*cubicThetaForcingSeries y s/(y.2:ℂ)^3 := by
        apply setIntegral_congr_fun hK.measurableSet
        intro y hy
        dsimp only
        rw [cubicThetaSectionFunction_apply _ (hp hy)]
        rfl
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hgs h)),star_zero,zero_mul,zero_div])
  rw [hG,hM,hF]
  exact cubicThetaArithmetic_local_weak hs g hg hc (hgs.trans hp)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspLogSection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaGlobalEnergySpace_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual compact smooth sections, pulled into a cusp and conjugated
by logarithmic height, are genuine compact radial test functions. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff
namespace CubicFirstMoment

def cubicThetaCuspLogSection (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) (t : ℝ) : ℂ :=
  (Real.exp (-t):ℂ)*cubicThetaCuspCutoffSection δ F z (Real.exp t)

lemma cubicThetaCuspLogSection_contDiff (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) : ContDiff ℝ ∞ (cubicThetaCuspLogSection δ F z) := by
  have hM : ContDiff ℝ ∞ (fun t : ℝ => cubicThetaMobius (cubicThetaFullComplex δ) (z,Real.exp t)) := by
    rw [contDiff_iff_contDiffAt]
    intro t
    exact (cubicThetaMobius_contDiffAt _ (Real.exp_pos t)).comp t
      (contDiffAt_const.prodMk Real.contDiff_exp.contDiffAt)
  have hF : ContDiff ℝ ∞ (fun t : ℝ => cubicThetaSectionFunction F
      (cubicThetaMobius (cubicThetaFullComplex δ) (z,Real.exp t))) := by
    rw [contDiff_iff_contDiffAt]
    intro t
    have hpos := cubicThetaMobius_height_pos (cubicThetaFullComplex δ)
      (p:=(z,Real.exp t)) (Real.exp_pos t)
    have hFpoint : ContDiffAt ℝ ∞ (cubicThetaSectionFunction F)
        (cubicThetaMobius (cubicThetaFullComplex δ) (z,Real.exp t)) :=
      F.property.1.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hpos)
    exact ContDiffAt.comp (g:=cubicThetaSectionFunction F)
      (f:=fun t : ℝ => cubicThetaMobius (cubicThetaFullComplex δ) (z,Real.exp t))
      t hFpoint hM.contDiffAt
  have he : ContDiff ℝ ∞ (fun t : ℝ => (Real.exp (-t):ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp contDiff_id.neg)
  exact he.mul ((cubicThetaCuspCutoff_smooth.comp Real.contDiff_exp).mul hF)

lemma cubicThetaCuspLogSection_compact (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) : HasCompactSupport (cubicThetaCuspLogSection δ F z) := by
  obtain ⟨C,_,hC⟩ := cubicThetaSmoothTests_cusp_function_support F
  let D := max C 2
  have hD : 0<D := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (le_max_right _ _)
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=0) (b:=Real.log D))
  intro t ht
  by_contra hout
  have hout' : t<0 ∨ Real.log D<t := by simpa only [mem_Icc,not_and_or,not_le] using hout
  apply ht
  rcases hout' with ht | ht
  · have hv : Real.exp t≤1 := Real.exp_le_one_iff.mpr ht.le
    simp only [cubicThetaCuspLogSection,cubicThetaCuspCutoffSection,
      cubicThetaCuspCutoff_zero hv,zero_mul,mul_zero]
  · have hv : D<Real.exp t := (Real.log_lt_iff_lt_exp hD).mp ht
    have hz := hC δ z (Real.exp t) (Real.exp_pos t) (lt_of_le_of_lt (le_max_left _ _) hv)
    simp only [cubicThetaCuspLogSection,cubicThetaCuspCutoffSection,hz,mul_zero]

lemma cubicThetaCuspLogSection_lift (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) {v : ℝ} (hv : 0<v) :
    cubicThetaLogLift (cubicThetaCuspLogSection δ F z) v=cubicThetaCuspCutoffSection δ F z v := by
  unfold cubicThetaLogLift cubicThetaCuspLogSection
  rw [Real.exp_log hv,Real.exp_neg,Real.exp_log hv]
  have hv' : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  push_cast
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspVerticalEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaGlobalEnergySpace_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial derivative in a cusp is controlled by the actual
hyperbolic Dirichlet energy of the pulled-back cubic section. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaCuspSection_vertical_energy (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) {v : ℝ} (hv : 0<v) :
    v^2*‖deriv (fun t : ℝ => cubicThetaSectionFunction F
      (cubicThetaMobius (cubicThetaFullComplex δ) (z,t))) v‖^2≤
      cubicThetaSectionEnergy F (δ • cubicThetaVerticalPoint z v hv) := by
  rw [cubicThetaCuspSection_deriv δ F z hv]
  have h := cubicThetaTangentEnergy_apply
    ((cubicThetaSectionDifferential F (δ • cubicThetaVerticalPoint z v hv)).comp
      (cubicThetaTangentDerivative (cubicThetaFullComplex δ) (z,v))) cubicThetaVerticalTangent
  rw [cubicThetaVerticalTangent_norm,one_pow,mul_one,
    cubicThetaTangentEnergy_derivative _ _ hv] at h
  have hb := mul_le_mul_of_nonneg_left h (sq_nonneg v)
  apply hb.trans_eq
  change v^2*(((cubicThetaMobius (cubicThetaFullComplex δ) (z,v)).2/v)^2*
    cubicThetaTangentEnergy (cubicThetaSectionDifferential F (δ • cubicThetaVerticalPoint z v hv)))=
    (cubicThetaMobius (cubicThetaFullComplex δ) (z,v)).2^2*
      cubicThetaTangentEnergy (cubicThetaSectionDifferential F (δ • cubicThetaVerticalPoint z v hv))
  field_simp [hv.ne']

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspCutoffEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! With any prescribed loss above the sharp coefficient one, cutting
off a cusp costs only mass in its fixed compact transition annulus. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaCuspCutoff_energy {ε : ℝ} (hε : 0<ε) :
    ∃ B≥0, ∀ (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests) (z : ℂ) (v : ℝ) (hv : 0<v),
      v^2*‖deriv (cubicThetaCuspCutoffSection δ F z) v‖^2≤
        (1+ε)*cubicThetaSectionEnergy F (δ • cubicThetaVerticalPoint z v hv)+
          B*(Icc (1:ℝ) 2).indicator (fun t => ‖cubicThetaSectionFunction F
            (cubicThetaMobius (cubicThetaFullComplex δ) (z,t))‖^2) v := by
  classical
  obtain ⟨B₀,hB₀,hB⟩ := cubicThetaCuspCutoff_deriv_bound
  have he : 0≤1+ε⁻¹ := by positivity
  refine ⟨(1+ε⁻¹)*B₀,mul_nonneg he hB₀,?_⟩
  intro δ F z v hv
  let f : ℝ → ℂ := fun t => cubicThetaSectionFunction F
    (cubicThetaMobius (cubicThetaFullComplex δ) (z,t))
  have hf : DifferentiableAt ℝ f v := cubicThetaCuspRaw_differentiableAt δ F z hv
  have ha := (cubicThetaCuspCutoff_smooth.differentiable (by simp)) v
  have hd : deriv (cubicThetaCuspCutoffSection δ F z) v=
      deriv cubicThetaCuspCutoff v*f v+cubicThetaCuspCutoff v*deriv f v :=
    deriv_mul ha hf
  rw [hd]
  have hy := cubicThetaComplex_norm_add_young
    (deriv cubicThetaCuspCutoff v*f v) (cubicThetaCuspCutoff v*deriv f v) hε
  have hy' := mul_le_mul_of_nonneg_left hy (sq_nonneg v)
  simp only [norm_mul,mul_pow] at hy'
  have hunit : ‖cubicThetaCuspCutoff v‖^2≤1 := by
    nlinarith [cubicThetaCuspCutoff_norm v,_root_.norm_nonneg (cubicThetaCuspCutoff v)]
  have hmain : v^2*(‖cubicThetaCuspCutoff v‖^2*‖deriv f v‖^2)≤
      cubicThetaSectionEnergy F (δ • cubicThetaVerticalPoint z v hv) := by
    calc
      _ = ‖cubicThetaCuspCutoff v‖^2*(v^2*‖deriv f v‖^2) := by ring
      _ ≤ 1*(v^2*‖deriv f v‖^2) := mul_le_mul_of_nonneg_right hunit
        (mul_nonneg (sq_nonneg v) (sq_nonneg _))
      _ ≤ _ := by simpa only [one_mul] using cubicThetaCuspSection_vertical_energy δ F z hv
  have herr : v^2*(‖deriv cubicThetaCuspCutoff v‖^2*‖f v‖^2)≤
      (Icc (1:ℝ) 2).indicator (fun _ => B₀) v*‖f v‖^2 := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hB v) (sq_nonneg ‖f v‖)
  calc
    _ ≤ (1+ε)*(v^2*(‖cubicThetaCuspCutoff v‖^2*‖deriv f v‖^2))+
        (1+ε⁻¹)*(v^2*(‖deriv cubicThetaCuspCutoff v‖^2*‖f v‖^2)) := by
      convert hy' using 1
      all_goals try with_reducible_and_instances rfl
      ring
    _ ≤ (1+ε)*cubicThetaSectionEnergy F (δ • cubicThetaVerticalPoint z v hv)+
        (1+ε⁻¹)*((Icc (1:ℝ) 2).indicator (fun _ => B₀) v*‖f v‖^2) :=
      add_le_add (mul_le_mul_of_nonneg_left hmain (by positivity))
        (mul_le_mul_of_nonneg_left herr he)
    _ = _ := by
      by_cases h : v∈Icc (1:ℝ) 2
      · simp only [indicator_of_mem h]
        dsimp [f]
        ring
      · simp only [indicator_of_notMem h,zero_mul,mul_zero,add_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspDerivativeIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual cutoff radial derivative is integrable on each exact
cusp cell. The majorant is the already proved global mass plus energy. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCuspCutoff_derivative_majorant :
    ∃ C≥0, ∀ (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests) (z : ℂ) (v : ℝ), 0<v →
      ‖deriv (cubicThetaCuspCutoffSection δ F z) v‖^2/v≤
        C*cubicThetaCuspCoordinateEnergy δ F (z,v)/v^3 := by
  classical
  obtain ⟨B,hB,h⟩ := cubicThetaCuspCutoff_energy (by norm_num : (0:ℝ)<1)
  refine ⟨2+B,by positivity,?_⟩
  intro δ F z v hv
  have ht := h δ F z v hv
  norm_num only at ht
  let M := ‖cubicThetaSectionFunction F (cubicThetaMobius (cubicThetaFullComplex δ) (z,v))‖^2
  let E := cubicThetaSectionEnergy F (δ • cubicThetaVerticalPoint z v hv)
  have hM : 0≤M := sq_nonneg _
  have hE : 0≤E := cubicThetaSectionEnergy_nonneg F _
  have hi : (Icc (1:ℝ) 2).indicator (fun t => ‖cubicThetaSectionFunction F
      (cubicThetaMobius (cubicThetaFullComplex δ) (z,t))‖^2) v≤M := by
    by_cases hv' : v∈Icc (1:ℝ) 2
    · rw [indicator_of_mem hv']
    · rw [indicator_of_notMem hv']
      exact hM
  have hmul := mul_le_mul_of_nonneg_left hi hB
  have ht' : v^2*‖deriv (cubicThetaCuspCutoffSection δ F z) v‖^2≤(2+B)*(M+E) := by
    change _≤2*E+B*_ at ht
    nlinarith [mul_nonneg hB hE]
  rw [cubicThetaCuspCoordinateEnergy_norm δ F z hv]
  have hd := div_le_div_of_nonneg_right ht' (pow_nonneg hv.le 3)
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  field_simp [hv.ne']

lemma cubicThetaCuspCutoff_derivative_integrable_high (δ : SL(2,Eisenstein))
    (F : cubicThetaSmoothTests) :
    IntegrableOn (fun y : ℂ × ℝ => ‖deriv (cubicThetaCuspCutoffSection δ F y.1) y.2‖^2/y.2)
      (cubicThetaHorizontalCell ×ˢ Ioi (1:ℝ)) := by
  obtain ⟨C,_,hC⟩ := cubicThetaCuspCutoff_derivative_majorant
  have he := (cubicThetaCuspCoordinateEnergy_integrable δ F (le_refl 1)).const_mul C
  have hm : IntegrableOn (fun y : ℂ × ℝ => C*cubicThetaCuspCoordinateEnergy δ F y/y.2^3)
      (cubicThetaHorizontalCell ×ˢ Ioi (1:ℝ)) := by
    simpa only [IntegrableOn,mul_div_assoc] using he
  apply hm.mono'
  · exact (((cubicThetaCuspCutoff_deriv_measurable δ F).norm.pow_const 2).div
      measurable_snd).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (cubicThetaHorizontalCell_measurable.prod measurableSet_Ioi)] with y hy
    have hv : 0<y.2 := lt_trans zero_lt_one hy.2
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) hv.le)]
    exact hC δ F y.1 y.2 hv

lemma cubicThetaCuspCutoffSection_deriv_zero (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) {v : ℝ} (hv : v≤1) : deriv (cubicThetaCuspCutoffSection δ F z) v=0 := by
  apply HasDerivWithinAt.deriv_eq_zero _ (uniqueDiffWithinAt_Iic v)
  apply (hasDerivWithinAt_const v (Iic v) (0:ℂ)).congr_of_mem _ (by simp)
  intro w hw
  change cubicThetaCuspCutoff w*_=0
  rw [cubicThetaCuspCutoff_zero (hw.trans hv),zero_mul]

lemma cubicThetaCuspCell_integrable_extend {f : ℂ × ℝ → ℝ}
    (hf : IntegrableOn f (cubicThetaHorizontalCell ×ˢ Ioi (1:ℝ)))
    (hz : ∀ z v, v≤1 → f (z,v)=0) :
    IntegrableOn f (cubicThetaHorizontalCell ×ˢ Ioi (0:ℝ)) := by
  classical
  have hi := (integrable_indicator_iff (cubicThetaHorizontalCell_measurable.prod measurableSet_Ioi)).mpr hf
  have h := hi.integrableOn (s:=cubicThetaHorizontalCell ×ˢ Ioi (0:ℝ))
  apply h.congr
  filter_upwards [ae_restrict_mem (cubicThetaHorizontalCell_measurable.prod measurableSet_Ioi)] with y hy
  change (cubicThetaHorizontalCell ×ˢ Ioi (1:ℝ)).indicator f y=f y
  by_cases hv : 1<y.2
  · exact indicator_of_mem (s:=cubicThetaHorizontalCell ×ˢ Ioi (1:ℝ)) ⟨hy.1,hv⟩ f
  · rw [indicator_of_notMem (by rintro ⟨_,h⟩; exact hv h)]
    exact (hz y.1 y.2 (le_of_not_gt hv)).symm

theorem cubicThetaCuspCutoff_derivative_integrable (δ : SL(2,Eisenstein))
    (F : cubicThetaSmoothTests) :
    IntegrableOn (fun y : ℂ × ℝ => ‖deriv (cubicThetaCuspCutoffSection δ F y.1) y.2‖^2/y.2)
      (cubicThetaHorizontalCell ×ˢ Ioi (0:ℝ)) := by
  apply cubicThetaCuspCell_integrable_extend (cubicThetaCuspCutoff_derivative_integrable_high δ F)
  intro z v hv
  rw [cubicThetaCuspCutoffSection_deriv_zero δ F z hv,norm_zero,
    zero_pow (by norm_num : (2:ℕ)≠0),zero_div]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspMassIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability of the actual cutoff cusp mass, with the exact v^-3
density, including the zero extension below height one. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCuspCutoff_mass_bound (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) {v : ℝ} (hv : 0<v) :
    ‖cubicThetaCuspCutoffSection δ F z v‖^2/v^3 ≤ cubicThetaCuspCoordinateEnergy δ F (z,v)/v^3 := by
  apply div_le_div_of_nonneg_right _ (pow_nonneg hv.le 3)
  rw [cubicThetaCuspCoordinateEnergy_norm δ F z hv,cubicThetaCuspCutoffSection,norm_mul,mul_pow]
  have hunit : ‖cubicThetaCuspCutoff v‖^2≤1 := by
    nlinarith [cubicThetaCuspCutoff_norm v,_root_.norm_nonneg (cubicThetaCuspCutoff v)]
  calc
    _ ≤ 1*‖cubicThetaSectionFunction F (cubicThetaMobius (cubicThetaFullComplex δ) (z,v))‖^2 :=
      mul_le_mul_of_nonneg_right hunit (sq_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      exact le_add_of_nonneg_right (cubicThetaSectionEnergy_nonneg F _)

lemma cubicThetaCuspCutoff_mass_integrable_high (δ : SL(2,Eisenstein))
    (F : cubicThetaSmoothTests) :
    IntegrableOn (fun y : ℂ × ℝ => ‖cubicThetaCuspCutoffSection δ F y.1 y.2‖^2/y.2^3)
      (cubicThetaHorizontalCell ×ˢ Ioi (1:ℝ)) := by
  apply (cubicThetaCuspCoordinateEnergy_integrable δ F (le_refl 1)).mono'
  · exact (((cubicThetaCuspCutoffSection_continuous δ F).measurable.norm.pow_const 2).div
      (measurable_snd.pow_const 3)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (cubicThetaHorizontalCell_measurable.prod measurableSet_Ioi)] with y hy
    have hv : 0<y.2 := lt_trans zero_lt_one hy.2
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) (pow_nonneg hv.le 3))]
    exact cubicThetaCuspCutoff_mass_bound δ F y.1 hv

theorem cubicThetaCuspCutoff_mass_integrable (δ : SL(2,Eisenstein))
    (F : cubicThetaSmoothTests) :
    IntegrableOn (fun y : ℂ × ℝ => ‖cubicThetaCuspCutoffSection δ F y.1 y.2‖^2/y.2^3)
      (cubicThetaHorizontalCell ×ˢ Ioi (0:ℝ)) := by
  apply cubicThetaCuspCell_integrable_extend (cubicThetaCuspCutoff_mass_integrable_high δ F)
  intro z v hv
  simp only [cubicThetaCuspCutoffSection,cubicThetaCuspCutoff_zero hv,zero_mul,
    norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),zero_div]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspSectionHardy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sharp radial Hardy inequality for the actual cutoff of any
compact smooth cubic section in each arithmetic cusp. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCuspLogSection_lift_deriv (δ : SL(2,Eisenstein))
    (F : cubicThetaSmoothTests) (z : ℂ) {v : ℝ} (hv : 0<v) :
    deriv (cubicThetaLogLift (cubicThetaCuspLogSection δ F z)) v=
      deriv (cubicThetaCuspCutoffSection δ F z) v := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioi.mem_nhds hv] with w hw
  exact cubicThetaCuspLogSection_lift δ F z hw

theorem cubicThetaCuspSection_hardy (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) :
    (∫ v in Ioi (0:ℝ), ‖cubicThetaCuspCutoffSection δ F z v‖^2/v^3)≤
      ∫ v in Ioi (0:ℝ), ‖deriv (cubicThetaCuspCutoffSection δ F z) v‖^2/v := by
  have h := cubicTheta_radial_hardy
    ((cubicThetaCuspLogSection_contDiff δ F z).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (cubicThetaCuspLogSection_compact δ F z)
  calc
    _ = ∫ v in Ioi (0:ℝ), ‖cubicThetaLogLift (cubicThetaCuspLogSection δ F z) v‖^2/v^3 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only
      rw [cubicThetaCuspLogSection_lift δ F z hv]
    _ ≤ ∫ v in Ioi (0:ℝ), ‖deriv (cubicThetaLogLift (cubicThetaCuspLogSection δ F z)) v‖^2/v := h
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only
      rw [cubicThetaCuspLogSection_lift_deriv δ F z hv]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspIntegratedHardy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sharp radial inequality is integrated over the actual horizontal
period cell. Both sides are justified by the proved scalar integrability. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaCusp_integrated_hardy (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests) :
    (∫ y in cubicThetaHorizontalCell ×ˢ Ioi (0:ℝ),
      ‖cubicThetaCuspCutoffSection δ F y.1 y.2‖^2/y.2^3)≤
    ∫ y in cubicThetaHorizontalCell ×ˢ Ioi (0:ℝ),
      ‖deriv (cubicThetaCuspCutoffSection δ F y.1) y.2‖^2/y.2 := by
  have hm := cubicThetaCuspCutoff_mass_integrable δ F
  have hd := cubicThetaCuspCutoff_derivative_integrable δ F
  have hm' : Integrable (fun y : ℂ × ℝ => ‖cubicThetaCuspCutoffSection δ F y.1 y.2‖^2/y.2^3)
      ((volume.restrict cubicThetaHorizontalCell).prod (volume.restrict (Ioi (0:ℝ)))) := by
    rw [Measure.prod_restrict]
    exact hm
  have hd' : Integrable (fun y : ℂ × ℝ => ‖deriv (cubicThetaCuspCutoffSection δ F y.1) y.2‖^2/y.2)
      ((volume.restrict cubicThetaHorizontalCell).prod (volume.restrict (Ioi (0:ℝ)))) := by
    rw [Measure.prod_restrict]
    exact hd
  change (∫ y, ‖cubicThetaCuspCutoffSection δ F y.1 y.2‖^2/y.2^3
    ∂((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict
      (cubicThetaHorizontalCell ×ˢ Ioi (0:ℝ)))≤
    (∫ y, ‖deriv (cubicThetaCuspCutoffSection δ F y.1) y.2‖^2/y.2
      ∂((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict
        (cubicThetaHorizontalCell ×ˢ Ioi (0:ℝ)))
  rw [← Measure.prod_restrict,integral_prod _ hm',integral_prod _ hd']
  exact integral_mono hm'.integral_prod_left hd'.integral_prod_left
    (fun z => cubicThetaCuspSection_hardy δ F z)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticCuspMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal arithmetic remainder is square integrable in every
integral cusp in its initial half-plane. The bound keeps the exact
hyperbolic density rather than replacing the cusp by a finite region. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaArithmeticRemainder_cusp_mass_integrable
    (δ : SL(2,Eisenstein)) {s : ℂ} (hs : 3 < s.re) :
    IntegrableOn (fun y : ℂ × ℝ =>
      ‖cubicThetaArithmeticRemainder (cubicThetaMobius (cubicThetaFullComplex δ) y) s‖^2/y.2^3)
      (cubicThetaHorizontalCell ×ˢ Ioi (2:ℝ)) := by
  obtain ⟨R,_,hR⟩ := cubicThetaHorizontalCell_normSq_bound
  have hh : IntegrableOn (fun _ : ℂ => (cubicThetaCuspRemainderConstant s R)^2)
      cubicThetaHorizontalCell := integrableOn_const cubicThetaHorizontalCell_measure_ne_top
  have hv : IntegrableOn (fun v : ℝ => v^(5-2*s.re)) (Ioi (2:ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hm := hh.mul_prod hv
  rw [Measure.prod_restrict] at hm
  apply hm.mono'
  · exact (cubicThetaArithmeticRemainder_cusp_mass_continuousOn δ (by linarith)).aestronglyMeasurable
      (cubicThetaHorizontalCell_measurable.prod measurableSet_Ioi)
  · filter_upwards [ae_restrict_mem (cubicThetaHorizontalCell_measurable.prod measurableSet_Ioi)] with y hy
    have hy0 : 0<y.2 := lt_trans (by norm_num : (0:ℝ)<2) hy.2
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) (pow_nonneg hy0.le 3))]
    exact cubicThetaArithmeticRemainder_cusp_mass_bound δ y.1 hy.2.le (hR y.1 hy.1) hs

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cusp estimates and finite arithmetic core cover put the literal
Eisenstein remainder in the actual global L2 space. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCuspNeighborhood_integrable_iff
    (δ : SL(2,Eisenstein)) {H : ℝ} (hH : 1≤H)
    {f : CubicThetaQuotient → ℝ} (hf : Continuous f) :
    IntegrableOn f (cubicThetaCuspNeighborhood δ H) cubicThetaQuotientMeasure ↔
      IntegrableOn (fun p => f (cubicThetaQuotientMap (δ • p)))
        (cubicThetaCuspStrip H) cubicThetaPointMeasure := by
  unfold cubicThetaCuspNeighborhood IntegrableOn
  rw [← cubicThetaInjective_map_restrict (cubicThetaTranslatedCuspStrip_measurable δ H)
    (cubicThetaTranslatedCuspStrip_injective δ hH)]
  rw [integrable_map_measure hf.aestronglyMeasurable
    cubicThetaQuotientMap_open.continuous.measurable.aemeasurable]
  change Integrable (fun p => f (cubicThetaQuotientMap p))
    (cubicThetaPointMeasure.restrict ((fun p : CubicThetaPoint => δ • p) '' cubicThetaCuspStrip H)) ↔ _
  rw [← cubicThetaSmul_map_restrict δ (cubicThetaCuspStrip_measurable H)]
  exact integrable_map_measure
    (hf.comp cubicThetaQuotientMap_open.continuous).aestronglyMeasurable
    (measurable_const_smul δ).aemeasurable

lemma cubicThetaArithmeticSection_cusp_mass_integrable
    (δ : SL(2,Eisenstein)) {s : ℂ} (hs : 3 < s.re) :
    IntegrableOn (fun q => cubicThetaSectionNorm (cubicThetaArithmeticSection s (by linarith)) q^2)
      (cubicThetaCuspNeighborhood δ 2) cubicThetaQuotientMeasure := by
  have hf : Continuous (fun q =>
      cubicThetaSectionNorm (cubicThetaArithmeticSection s (by linarith)) q^2) :=
    (cubicThetaSectionNorm_continuous _).pow 2
  apply (cubicThetaCuspNeighborhood_integrable_iff δ (by norm_num) hf).mpr
  have h := cubicThetaArithmeticRemainder_cusp_mass_integrable δ hs
  rw [← cubicThetaCuspStrip_coordinates (by norm_num : (0:ℝ)≤2),
    ← cubicThetaPointIntegrable_density (cubicThetaCuspStrip_measurable 2)] at h
  simpa only [cubicThetaArithmeticSection_norm,cubicThetaFullPointAction_apply,cubicThetaPointCoordinates] using h

theorem cubicThetaArithmeticSection_mass_integrable {s : ℂ} (hs : 3 < s.re) :
    Integrable (fun q => cubicThetaSectionNorm (cubicThetaArithmeticSection s (by linarith)) q^2)
      cubicThetaQuotientMeasure := by
  obtain ⟨S,hS⟩ := cubicThetaCuspNeighborhood_cover
  have hf : Continuous (fun q =>
      cubicThetaSectionNorm (cubicThetaArithmeticSection s (by linarith)) q^2) :=
    (cubicThetaSectionNorm_continuous _).pow 2
  have hc := hf.continuousOn.integrableOn_compact (μ:=cubicThetaQuotientMeasure) (cubicThetaQuotientCore_compact S 2)
  have hu : IntegrableOn
      (fun q => cubicThetaSectionNorm (cubicThetaArithmeticSection s (by linarith)) q^2)
      (⋃ δ∈S,cubicThetaCuspNeighborhood δ⁻¹ 2) cubicThetaQuotientMeasure :=
    integrableOn_finset_iUnion.mpr (fun δ _ => cubicThetaArithmeticSection_cusp_mass_integrable δ⁻¹ hs)
  have h := hc.union hu
  rwa [hS 2,integrableOn_univ] at h

lemma cubicThetaArithmeticSection_memLp {s : ℂ} (hs : 3 < s.re) :
    MemLp (cubicThetaSectionRepresentative (cubicThetaArithmeticSection s (by linarith)))
      2 cubicThetaQuotientMeasure := by
  apply (memLp_two_iff_integrable_sq_norm
    (cubicThetaSectionRepresentative_measurable _).aestronglyMeasurable).mpr
  simpa only [cubicThetaSectionRepresentative_norm] using cubicThetaArithmeticSection_mass_integrable hs

def cubicThetaArithmeticL2 (s : ℂ) (hs : 3 < s.re) : CubicThetaGlobalL2 :=
  (cubicThetaArithmeticSection_memLp hs).toLp _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticGradientL2
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual arithmetic differential is globally square integrable.
The result uses the finite arithmetic cusp/core cover and the literal
hyperbolic energy density, without assuming energy-graph membership. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaArithmeticQuotientEnergy_cusp_integrable (δ : SL(2,Eisenstein))
    {s : ℂ} (hs : 3 < s.re) :
    IntegrableOn (cubicThetaArithmeticQuotientEnergy s (by linarith))
      (cubicThetaCuspNeighborhood δ 2) cubicThetaQuotientMeasure := by
  apply (cubicThetaCuspNeighborhood_integrable_iff δ (by norm_num)
    (cubicThetaArithmeticQuotientEnergy_continuous s (by linarith))).mpr
  have h := cubicThetaArithmeticCoordinateEnergy_integrable δ hs
  rw [← cubicThetaCuspStrip_coordinates (by norm_num : (0:ℝ)≤2),
    ← cubicThetaPointIntegrable_density (cubicThetaCuspStrip_measurable 2)] at h
  simpa only [cubicThetaArithmeticQuotientEnergy_apply,cubicThetaArithmeticCoordinateEnergy_apply] using h

theorem cubicThetaArithmeticQuotientEnergy_integrable {s : ℂ} (hs : 3 < s.re) :
    Integrable (cubicThetaArithmeticQuotientEnergy s (by linarith)) cubicThetaQuotientMeasure := by
  obtain ⟨S,hS⟩ := cubicThetaCuspNeighborhood_cover
  have hf := cubicThetaArithmeticQuotientEnergy_continuous s (show 2 < s.re by linarith)
  have hc := hf.continuousOn.integrableOn_compact (μ:=cubicThetaQuotientMeasure)
    (cubicThetaQuotientCore_compact S 2)
  have hu : IntegrableOn (cubicThetaArithmeticQuotientEnergy s (by linarith))
      (⋃ δ∈S,cubicThetaCuspNeighborhood δ⁻¹ 2) cubicThetaQuotientMeasure :=
    integrableOn_finset_iUnion.mpr (fun δ _ => cubicThetaArithmeticQuotientEnergy_cusp_integrable δ⁻¹ hs)
  have h := hc.union hu
  rwa [hS 2,integrableOn_univ] at h

lemma cubicThetaArithmeticGradient_continuous {s : ℂ} (hs : 2 < s.re) :
    Continuous (cubicThetaSectionGradient (cubicThetaArithmeticSection s hs)) := by
  have hd : Continuous (fun p : CubicThetaPoint =>
      fderiv ℝ (cubicThetaSectionFunction (cubicThetaArithmeticSection s hs)) p.val) :=
    ((cubicThetaArithmeticSectionFunction_contDiffOn_one hs).continuousOn_fderiv_of_isOpen
      (isOpen_lt continuous_const continuous_snd) (by norm_num)).comp_continuous
      continuous_subtype_val (fun p => p.property)
  apply (PiLp.continuous_toLp _ _).comp
  apply continuous_pi
  intro i
  exact (continuous_snd.comp continuous_subtype_val).smul (hd.clm_apply continuous_const)

lemma cubicThetaArithmeticGradientRepresentative_measurable {s : ℂ} (hs : 2 < s.re) :
    Measurable (cubicThetaGradientRepresentative (cubicThetaArithmeticSection s hs)) :=
  (cubicThetaArithmeticGradient_continuous hs).measurable.comp cubicThetaBorelSection_measurable

lemma cubicThetaArithmeticGradientRepresentative_norm_sq {s : ℂ} (hs : 2 < s.re)
    (q : CubicThetaQuotient) :
    ‖cubicThetaGradientRepresentative (cubicThetaArithmeticSection s hs) q‖^2=
      cubicThetaArithmeticQuotientEnergy s hs q := by
  unfold cubicThetaGradientRepresentative
  rw [cubicThetaSectionGradient_norm_sq,← cubicThetaArithmeticQuotientEnergy_apply,
    cubicThetaBorelSection_rightInverse]

lemma cubicThetaArithmeticGradientRepresentative_memLp {s : ℂ} (hs : 3 < s.re) :
    MemLp (cubicThetaGradientRepresentative (cubicThetaArithmeticSection s (by linarith)))
      2 cubicThetaQuotientMeasure := by
  apply (memLp_two_iff_integrable_sq_norm
    (cubicThetaArithmeticGradientRepresentative_measurable (by linarith)).aestronglyMeasurable).mpr
  simpa only [cubicThetaArithmeticGradientRepresentative_norm_sq] using
    cubicThetaArithmeticQuotientEnergy_integrable hs

def cubicThetaArithmeticGradientL2 (s : ℂ) (hs : 3 < s.re) : CubicThetaGradientL2 :=
  (cubicThetaArithmeticGradientRepresentative_memLp hs).toLp _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticEnergyGraph
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal arithmetic Eisenstein remainder belongs to the completed
energy graph, with its actual value and differentiated coordinates. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaArithmeticEnergy (s : ℂ) (hs : 3 < s.re) : cubicThetaGlobalEnergySpace :=
  ⟨WithLp.toLp 2 (cubicThetaArithmeticL2 s hs,cubicThetaArithmeticGradientL2 s hs),
    cubicThetaFiniteEnergy_mem_graph (cubicThetaArithmeticSection s (by linarith))
      (cubicThetaArithmeticSectionFunction_contDiffOn_one (by linarith))
      (cubicThetaArithmeticSection_memLp hs) (cubicThetaArithmeticGradientRepresentative_memLp hs)⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticWeakDefect
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous additive defect for the literal arithmetic weak
PDE. Its vanishing can be glued and passed to the energy completion. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaArithmeticWeakDefect (s : ℂ) (hs : 3 < s.re) :
    CubicThetaGlobalEnergyAmbient →+ ℂ where
  toFun u :=
    inner ℂ (WithLp.sndL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2 u)
      (cubicThetaArithmeticGradientL2 s hs)+
    s*(s-2)*inner ℂ (WithLp.fstL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2 u)
      (cubicThetaArithmeticL2 s hs)-
    inner ℂ (WithLp.fstL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2 u)
      (cubicThetaForcingL2 s)
  map_zero' := by simp
  map_add' u v := by
    simp only [map_add,inner_add_left]
    ring

lemma cubicThetaArithmeticWeakDefect_continuous (s : ℂ) (hs : 3 < s.re) :
    Continuous (cubicThetaArithmeticWeakDefect s hs) := by
  change Continuous (fun u : CubicThetaGlobalEnergyAmbient =>
    inner ℂ (WithLp.sndL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2 u)
      (cubicThetaArithmeticGradientL2 s hs)+
    s*(s-2)*inner ℂ (WithLp.fstL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2 u)
      (cubicThetaArithmeticL2 s hs)-
    inner ℂ (WithLp.fstL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2 u)
      (cubicThetaForcingL2 s))
  fun_prop

lemma cubicThetaArithmeticWeakDefect_C1 (s : ℂ) (hs : 3 < s.re)
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) :
    cubicThetaArithmeticWeakDefect s hs (cubicThetaC1EnergyData F hF hc)=
      (∫ q, cubicThetaC1Pairing F (cubicThetaArithmeticSection s (by linarith)) q
        ∂cubicThetaQuotientMeasure)+
      s*(s-2)*(∫ q, cubicThetaSectionPairing F (cubicThetaArithmeticSection s (by linarith)) q
        ∂cubicThetaQuotientMeasure)-
      ∫ q, cubicThetaSectionPairing F (cubicThetaForcingSection s) q ∂cubicThetaQuotientMeasure := by
  change inner ℂ ((cubicThetaC1Gradient_memLp F hF hc).toLp _)
      ((cubicThetaArithmeticGradientRepresentative_memLp hs).toLp _)+
    s*(s-2)*inner ℂ ((cubicThetaCompactSection_memLp F hc).toLp _)
      ((cubicThetaArithmeticSection_memLp hs).toLp _)-
    inner ℂ ((cubicThetaCompactSection_memLp F hc).toLp _)
      ((cubicThetaSectionRepresentative_memLp (cubicThetaForcingTest s)).toLp _)=_
  rw [cubicThetaC1Pairing_L2 F _ hF (cubicThetaArithmeticSectionFunction_contDiffOn_one (by linarith)),
    cubicThetaSectionPairing_L2,cubicThetaSectionPairing_L2]
  rfl

lemma cubicThetaArithmeticWeakDefect_coordinate {s : ℂ} (hs : 3 < s.re)
    {g : ℂ × ℝ → ℂ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {K : Set (ℂ × ℝ)} (hK : IsCompact K) (hp : K⊆{y : ℂ × ℝ | 0<y.2})
    (hgs : tsupport g⊆K)
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hKe : cubicThetaPointInclusion.symm '' K⊆e.source) :
    cubicThetaArithmeticWeakDefect s hs (cubicThetaCoordinateData hg hc (hgs.trans hp))=0 := by
  rw [cubicThetaCoordinateData,cubicThetaArithmeticWeakDefect_C1]
  exact sub_eq_zero.mpr (cubicThetaArithmetic_chart_weak (by linarith) hg hc hK hp hgs e he hKe)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticGlobalWeak
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite arithmetic chart reconstruction and continuity extend the
literal remainder's weak equation to every global energy test. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaArithmeticWeakDefect_compact {s : ℂ} (hs : 3 < s.re)
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) :
    cubicThetaArithmeticWeakDefect s hs (cubicThetaC1EnergyData F hF hc)=0 := by
  obtain ⟨S,V,hSV⟩ := cubicThetaCompact_subset_core hc
  obtain ⟨A,hA⟩ := cubicThetaCoreDenominator_covers S V
  have hn : ∀ q∈tsupport (cubicThetaSectionNorm F), cubicThetaCoreDenominator A q≠0 := by
    intro q hq
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (hA q (hSV hq)))
  let D := cubicThetaCoreDenominator A
  let H := cubicThetaSectionDivide F D (cubicThetaCoreDenominator_continuous A) hn
  have hH : ContDiffOn ℝ 1 (cubicThetaSectionFunction H) {y : ℂ × ℝ | 0<y.2} :=
    cubicThetaSectionDivide_regular F hF D (cubicThetaCoreDenominator_continuous A) hn
      (cubicThetaCoreDenominator_pullback A)
  let P := fun c : CubicThetaQuotient => cubicThetaPoincareSection
    (cubicThetaCoordinateSeed (cubicThetaC1CoreFunction c H)
      (cubicThetaC1CoreFunction_regular c H hH).continuous
      (cubicThetaC1CoreFunction_compact c H)
      ((cubicThetaC1CoreFunction_support c H).trans (cubicThetaCoreProfile_support_positive c)))
  have hP (c : CubicThetaQuotient) :
      ContDiffOn ℝ 1 (cubicThetaSectionFunction (P c)) {y : ℂ × ℝ | 0<y.2} :=
    cubicThetaCoordinateSection_regular (cubicThetaC1CoreFunction_regular c H hH)
      (cubicThetaC1CoreFunction_compact c H)
      ((cubicThetaC1CoreFunction_support c H).trans (cubicThetaCoreProfile_support_positive c))
  have hcP (c : CubicThetaQuotient) : HasCompactSupport (cubicThetaSectionNorm (P c)) :=
    cubicThetaPoincareSection_compact _
  have hzP (c : CubicThetaQuotient) :
      cubicThetaArithmeticWeakDefect s hs (cubicThetaC1EnergyData (P c) (hP c) (hcP c))=0 := by
    apply cubicThetaArithmeticWeakDefect_coordinate hs
      (cubicThetaC1CoreFunction_regular c H hH) (cubicThetaC1CoreFunction_compact c H)
      (cubicThetaCoreProfile_compact c) (cubicThetaCoreProfile_support_positive c)
      (cubicThetaC1CoreFunction_support c H)
      (cubicThetaCoveringChart (cubicThetaQuotientLift c)) (cubicThetaCoveringChart_coe _)
    rintro p ⟨y,hy,rfl⟩
    exact (cubicThetaCoreProfile_support_target c hy).2
  have hsum : (∑ c∈A, P c)=F := by
    calc
      _ = ∑ c∈A, cubicThetaSectionCutoff (cubicThetaCoreSquare c) H := by
        apply Finset.sum_congr rfl
        intro c hcA
        exact cubicThetaC1CoreFunction_periodization c H hH
      _ = F := cubicThetaCoreDivision_reconstruction A F hn
  have he : cubicThetaC1EnergyData F hF hc=
      ∑ c∈A, cubicThetaC1EnergyData (P c) (hP c) (hcP c) := by
    rw [← cubicThetaC1EnergyData_sum A P hP hcP]
    congr 1
    exact hsum.symm
  rw [he,map_sum]
  exact Finset.sum_eq_zero (fun c _ => hzP c)

lemma cubicThetaArithmeticWeakDefect_energy {s : ℂ} (hs : 3 < s.re)
    (v : cubicThetaGlobalEnergySpace) :
    cubicThetaArithmeticWeakDefect s hs (v:CubicThetaGlobalEnergyAmbient)=0 := by
  have hc : IsClosed {u : CubicThetaGlobalEnergyAmbient | cubicThetaArithmeticWeakDefect s hs u=0} :=
    isClosed_eq (cubicThetaArithmeticWeakDefect_continuous s hs) continuous_const
  have hr : (cubicThetaGlobalEnergyGraph.range : Set CubicThetaGlobalEnergyAmbient)⊆
      {u | cubicThetaArithmeticWeakDefect s hs u=0} := by
    rintro u ⟨F,rfl⟩
    rw [← cubicThetaC1EnergyData_smooth F]
    exact cubicThetaArithmeticWeakDefect_compact hs F (F.property.1.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) F.property.2
  have hv : (v:CubicThetaGlobalEnergyAmbient)∈
      closure (cubicThetaGlobalEnergyGraph.range : Set CubicThetaGlobalEnergyAmbient) := v.property
  exact closure_minimal hr hc hv

theorem cubicThetaArithmetic_global_weak {s : ℂ} (hs : 3 < s.re)
    (v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaGlobalEnergyGradient v)
      (cubicThetaGlobalEnergyGradient (cubicThetaArithmeticEnergy s hs))+
    s*(s-2)*inner ℂ (cubicThetaGlobalInclusion v)
      (cubicThetaGlobalInclusion (cubicThetaArithmeticEnergy s hs))=
    inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaForcingL2 s) := by
  exact sub_eq_zero.mp (cubicThetaArithmeticWeakDefect_energy hs v)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspScalarIntegrals
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scalar transport from the quotient to each arithmetic cusp cell.
These formulas separate mass and derivative energy, so the sharp Hardy
coefficient is preserved when the cusp estimates are summed. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCuspPullback_integrable (δ : SL(2,Eisenstein))
    {f : CubicThetaQuotient → ℝ} (hf : Integrable f cubicThetaQuotientMeasure)
    {H : ℝ} (hH : 1≤H) :
    IntegrableOn (fun y => cubicThetaCuspPullback δ f y/y.2^3)
      (cubicThetaHorizontalCell ×ˢ Ioi H) := by
  rw [← cubicThetaCuspStrip_coordinates (zero_le_one.trans hH),
    ← cubicThetaPointIntegrable_density (cubicThetaCuspStrip_measurable H)]
  simpa only [cubicThetaCuspPullback_apply] using
    cubicThetaTranslatedCuspStrip_integrable δ hH hf

lemma cubicThetaCuspPullback_integral (δ : SL(2,Eisenstein))
    (f : CubicThetaQuotient → ℝ) (hf : StronglyMeasurable f) {H : ℝ} (hH : 1≤H) :
    (∫ y in cubicThetaHorizontalCell ×ˢ Ioi H, cubicThetaCuspPullback δ f y/y.2^3)=
      ∫ q in cubicThetaCuspNeighborhood δ H, f q ∂cubicThetaQuotientMeasure := by
  unfold cubicThetaCuspNeighborhood
  rw [cubicThetaTranslatedCuspStrip_integral δ hH f hf]
  rw [← cubicThetaCuspStrip_coordinates (zero_le_one.trans hH),
    ← cubicThetaPointIntegral_density (cubicThetaCuspStrip_measurable H)]
  apply setIntegral_congr_fun (cubicThetaCuspStrip_measurable H)
  intro p hp
  exact cubicThetaCuspPullback_apply δ f p

lemma cubicThetaCuspPullback_mass (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) {v : ℝ} (hv : 0<v) :
    cubicThetaCuspPullback δ (fun q => cubicThetaSectionNorm F q^2) (z,v)=
      ‖cubicThetaSectionFunction F (cubicThetaMobius (cubicThetaFullComplex δ) (z,v))‖^2 := by
  have h := cubicThetaCuspPullback_apply δ (fun q => cubicThetaSectionNorm F q^2)
    (cubicThetaVerticalPoint z v hv)
  change cubicThetaCuspPullback δ (fun q => cubicThetaSectionNorm F q^2) (z,v)=_ at h
  rw [h,cubicThetaCusp_raw_norm δ F z hv]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEnergyIntegralIdentities
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The completed energy coordinates and compact restrictions retain
the literal mass and differential integrals on smooth sections. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaGlobalInclusion_test_norm_sq (F : cubicThetaSmoothTests) :
    ‖cubicThetaGlobalInclusion (cubicThetaGlobalEnergyTest F)‖^2=
      ∫ q, cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure := by
  rw [cubicThetaGlobalInclusion_test,cubicTheta_l2_norm_sq_measure]
  apply integral_congr_ae
  filter_upwards [(cubicThetaSectionRepresentative_memLp F).coeFn_toLp] with q hq
  change ‖((cubicThetaSectionRepresentative_memLp F).toLp _) q‖^2=_
  rw [hq,cubicThetaSectionRepresentative_norm]

lemma cubicThetaGlobalGradient_test_norm_sq (F : cubicThetaSmoothTests) :
    ‖cubicThetaGlobalEnergyGradient (cubicThetaGlobalEnergyTest F)‖^2=
      ∫ q, cubicThetaQuotientEnergy F q ∂cubicThetaQuotientMeasure := by
  rw [cubicThetaGlobalEnergyGradient_test,cubicTheta_l2_norm_sq_measure]
  apply integral_congr_ae
  filter_upwards [(cubicThetaGradientRepresentative_memLp F).coeFn_toLp] with q hq
  change ‖((cubicThetaGradientRepresentative_memLp F).toLp _) q‖^2=_
  rw [hq]
  change ‖cubicThetaSectionGradient F (cubicThetaBorelSection q)‖^2=_
  rw [cubicThetaSectionGradient_norm_sq,← cubicThetaQuotientEnergy_apply,
    cubicThetaBorelSection_rightInverse]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspCoreEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cutoff error is supported in the genuine compact arithmetic core.
The coefficient of the full cusp gradient can be any number above one. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCusp_derivative_integral_high (δ : SL(2,Eisenstein))
    (F : cubicThetaSmoothTests) :
    (∫ y in cubicThetaHorizontalCell ×ˢ Ioi (0:ℝ),
      ‖deriv (cubicThetaCuspCutoffSection δ F y.1) y.2‖^2/y.2)=
    ∫ y in cubicThetaHorizontalCell ×ˢ Ioi (1:ℝ),
      ‖deriv (cubicThetaCuspCutoffSection δ F y.1) y.2‖^2/y.2 := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (cubicThetaHorizontalCell_measurable.prod measurableSet_Ioi)
    (fun y hy => ⟨hy.1,lt_trans zero_lt_one hy.2⟩)
  intro y hy
  have hv : y.2≤1 := le_of_not_gt (fun h => hy.2 ⟨hy.1.1,h⟩)
  rw [cubicThetaCuspCutoffSection_deriv_zero δ F y.1 hv,norm_zero,
    zero_pow (by norm_num : (2:ℕ)≠0),zero_div]

lemma cubicThetaCusp_transition_bound {K : Set CubicThetaQuotient}
    (hK : ∀ (δ : SL(2,Eisenstein)) (p : CubicThetaPoint),
      1 ≤ cubicThetaPointHeight p → cubicThetaPointHeight p≤2 →
        cubicThetaQuotientMap (δ • p)∈K)
    (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests) (z : ℂ)
    {v : ℝ} (hv : 0<v) :
    (Icc (1:ℝ) 2).indicator (fun t => ‖cubicThetaSectionFunction F
      (cubicThetaMobius (cubicThetaFullComplex δ) (z,t))‖^2) v≤
    cubicThetaCuspPullback δ (K.indicator (fun q => cubicThetaSectionNorm F q^2)) (z,v) := by
  classical
  have hp := cubicThetaCuspPullback_apply δ
    (K.indicator (fun q => cubicThetaSectionNorm F q^2)) (cubicThetaVerticalPoint z v hv)
  change cubicThetaCuspPullback δ (K.indicator (fun q => cubicThetaSectionNorm F q^2))
    (z,v)=_ at hp
  by_cases ht : v∈Icc (1:ℝ) 2
  · rw [indicator_of_mem ht,hp,
      indicator_of_mem (hK δ (cubicThetaVerticalPoint z v hv) ht.1 ht.2),
      cubicThetaCusp_raw_norm δ F z hv]
  · rw [indicator_of_notMem ht]
    exact indicator_nonneg (fun q hq => sq_nonneg _) _

lemma cubicThetaCusp_core_energy {ε : ℝ} (hε : 0<ε) :
    ∃ B≥0, ∀ (K : Set CubicThetaQuotient), MeasurableSet K →
      (∀ (δ : SL(2,Eisenstein)) (p : CubicThetaPoint),
        1 ≤ cubicThetaPointHeight p → cubicThetaPointHeight p≤2 →
          cubicThetaQuotientMap (δ • p)∈K) →
      ∀ (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests),
    (∫ y in cubicThetaHorizontalCell ×ˢ Ioi (0:ℝ),
      ‖deriv (cubicThetaCuspCutoffSection δ F y.1) y.2‖^2/y.2)≤
      (1+ε)*(∫ q in cubicThetaCuspNeighborhood δ 1,
        cubicThetaQuotientEnergy F q ∂cubicThetaQuotientMeasure)+
      B*(∫ q in K, cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure) := by
  obtain ⟨B,hB,hpoint⟩ := cubicThetaCuspCutoff_energy hε
  refine ⟨B,hB,?_⟩
  intro K hKm hK δ F
  let m : CubicThetaQuotient → ℝ := K.indicator (fun q => cubicThetaSectionNorm F q^2)
  have hm : Integrable m cubicThetaQuotientMeasure := (cubicThetaMass_integrable F).indicator hKm
  have hms : StronglyMeasurable m :=
    ((cubicThetaSectionNorm_continuous F).pow 2).stronglyMeasurable.indicator hKm
  have he := cubicThetaCuspPullback_integrable δ (cubicThetaGradientEnergy_integrable F) (le_refl 1)
  have hc := cubicThetaCuspPullback_integrable δ hm (le_refl 1)
  have hbound : (∫ y in cubicThetaHorizontalCell ×ˢ Ioi (1:ℝ),
      ‖deriv (cubicThetaCuspCutoffSection δ F y.1) y.2‖^2/y.2)≤
      ∫ y in cubicThetaHorizontalCell ×ˢ Ioi (1:ℝ),
        (1+ε)*(cubicThetaCuspPullback δ (cubicThetaQuotientEnergy F) y/y.2^3)+
        B*(cubicThetaCuspPullback δ m y/y.2^3) := by
    apply setIntegral_mono_on (cubicThetaCuspCutoff_derivative_integrable_high δ F)
      ((he.const_mul (1+ε)).add (hc.const_mul B))
      (cubicThetaHorizontalCell_measurable.prod measurableSet_Ioi)
    intro y hy
    have hv : 0<y.2 := lt_trans zero_lt_one hy.2
    have h := (hpoint δ F y.1 y.2 hv).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (cubicThetaCusp_transition_bound hK δ F y.1 hv) hB))
    rw [← cubicThetaCuspPullback_energy δ F y.1 hv] at h
    have hd := div_le_div_of_nonneg_right h (pow_nonneg hv.le 3)
    convert hd using 1
    · field_simp [hv.ne']
    · dsimp [m]
      ring
  rw [cubicThetaCusp_derivative_integral_high δ F]
  apply hbound.trans
  rw [integral_add (he.const_mul _) (hc.const_mul _),integral_const_mul,integral_const_mul,
    cubicThetaCuspPullback_integral δ _ (cubicThetaQuotientEnergy_continuous F).stronglyMeasurable (le_refl 1),
    cubicThetaCuspPullback_integral δ m hms (le_refl 1)]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ hB
  calc
    (∫ q in cubicThetaCuspNeighborhood δ 1, m q ∂cubicThetaQuotientMeasure)≤
        ∫ q, m q ∂cubicThetaQuotientMeasure :=
      setIntegral_le_integral hm (Filter.Eventually.of_forall (fun q => indicator_nonneg (fun _ _ => sq_nonneg _) q))
    _ = _ := integral_indicator hKm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspExteriorMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mass above height two is bounded by the full energy above height one
and a mass error in the compact transition core. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCusp_high_mass (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests) :
    (∫ q in cubicThetaCuspNeighborhood δ 2, cubicThetaSectionNorm F q^2
      ∂cubicThetaQuotientMeasure)≤
    ∫ y in cubicThetaHorizontalCell ×ˢ Ioi (0:ℝ),
      ‖cubicThetaCuspCutoffSection δ F y.1 y.2‖^2/y.2^3 := by
  have hf : StronglyMeasurable (fun q => cubicThetaSectionNorm F q^2) :=
    ((cubicThetaSectionNorm_continuous F).pow 2).stronglyMeasurable
  rw [← cubicThetaCuspPullback_integral δ (fun q => cubicThetaSectionNorm F q^2)
    hf (by norm_num : (1:ℝ)≤2)]
  calc
    _ = ∫ y in cubicThetaHorizontalCell ×ˢ Ioi (2:ℝ),
        ‖cubicThetaCuspCutoffSection δ F y.1 y.2‖^2/y.2^3 := by
      apply setIntegral_congr_fun (cubicThetaHorizontalCell_measurable.prod measurableSet_Ioi)
      rintro ⟨z,v⟩ hy
      dsimp only at hy ⊢
      have hv : 0<v := lt_trans (by norm_num : (0:ℝ)<2) hy.2
      rw [cubicThetaCuspPullback_mass δ F z hv,cubicThetaCuspCutoffSection,
        cubicThetaCuspCutoff_one hy.2.le,one_mul]
    _ ≤ _ := by
      apply setIntegral_mono_set (cubicThetaCuspCutoff_mass_integrable δ F)
      · filter_upwards [ae_restrict_mem (cubicThetaHorizontalCell_measurable.prod measurableSet_Ioi)] with y hy
        exact div_nonneg (sq_nonneg _) (pow_nonneg hy.2.le 3)
      · exact Filter.Eventually.of_forall (fun y hy => ⟨hy.1,lt_trans (by norm_num : (0:ℝ)<2) hy.2⟩)

theorem cubicThetaCusp_exterior_mass {ε : ℝ} (hε : 0<ε) :
    ∃ (S : Finset SL(2,Eisenstein)) (B : ℝ), 0≤B ∧
      ∀ (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests),
    (∫ q in cubicThetaCuspNeighborhood δ 2, cubicThetaSectionNorm F q^2
      ∂cubicThetaQuotientMeasure)≤
    (1+ε)*(∫ q in cubicThetaCuspNeighborhood δ 1, cubicThetaQuotientEnergy F q
      ∂cubicThetaQuotientMeasure)+
    B*(∫ q in cubicThetaQuotientCore S 2, cubicThetaSectionNorm F q^2
      ∂cubicThetaQuotientMeasure) := by
  obtain ⟨S,hS⟩ := cubicThetaCuspTransition_core
  obtain ⟨B,hB,h⟩ := cubicThetaCusp_core_energy hε
  refine ⟨S,B,hB,fun δ F => ?_⟩
  exact (cubicThetaCusp_high_mass δ F).trans ((cubicThetaCusp_integrated_hardy δ F).trans
    (h _ (cubicThetaQuotientCore_compact S 2).measurableSet hS δ F))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteCuspEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact summation of the sharp cusp estimates. Distinct cusp classes
are disjoint already at height one, so no covering multiplicity is lost
in the gradient coefficient. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaFiniteCusps_energy_le (T : Finset SL(2,Eisenstein))
    (hT : (T : Set SL(2,Eisenstein)).PairwiseDisjoint
      (fun δ => cubicThetaCuspNeighborhood δ 1)) (F : cubicThetaSmoothTests) :
    (∑ δ∈T, ∫ q in cubicThetaCuspNeighborhood δ 1,
      cubicThetaQuotientEnergy F q ∂cubicThetaQuotientMeasure)≤
    ∫ q, cubicThetaQuotientEnergy F q ∂cubicThetaQuotientMeasure := by
  rw [← integral_biUnion_finset T (fun δ hδ => cubicThetaCuspNeighborhood_measurable δ (le_refl 1))
    hT (fun δ hδ => (cubicThetaGradientEnergy_integrable F).integrableOn)]
  exact setIntegral_le_integral (cubicThetaGradientEnergy_integrable F)
    (Filter.Eventually.of_forall (cubicThetaQuotientEnergy_nonneg F))

lemma cubicThetaFiniteCusps_mass_le (S T : Finset SL(2,Eisenstein))
    (hcover : cubicThetaQuotientCore S 2∪(⋃ δ∈T,cubicThetaCuspNeighborhood δ 2)=univ)
    (hT : (T : Set SL(2,Eisenstein)).PairwiseDisjoint
      (fun δ => cubicThetaCuspNeighborhood δ 2)) (F : cubicThetaSmoothTests) :
    (∫ q, cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure)≤
    (∫ q in cubicThetaQuotientCore S 2, cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure)+
    ∑ δ∈T, ∫ q in cubicThetaCuspNeighborhood δ 2,
      cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure := by
  have hU : MeasurableSet (⋃ δ∈T,cubicThetaCuspNeighborhood δ 2) :=
    T.measurableSet_biUnion (fun δ hδ => cubicThetaCuspNeighborhood_measurable δ (by norm_num))
  have h := cubicThetaIntegral_cover_le (cubicThetaQuotientCore_compact S 2).measurableSet
    hU hcover (cubicThetaMass_integrable F) (fun q => sq_nonneg _)
  rwa [integral_biUnion_finset T (fun δ hδ => cubicThetaCuspNeighborhood_measurable δ (by norm_num))
    hT (fun δ hδ => (cubicThetaMass_integrable F).integrableOn)] at h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaExteriorIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global exterior inequality for actual compact smooth cubic
sections. The only remainder is mass on two explicit arithmetic compact
cores; no analytic estimate is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaFiniteCusps_cover :
    ∃ S T : Finset SL(2,Eisenstein),
      (∀ H : ℝ, cubicThetaQuotientCore S H∪(⋃ δ∈T,cubicThetaCuspNeighborhood δ H)=univ) ∧
      ∀ H : ℝ, 1≤H → (T : Set SL(2,Eisenstein)).PairwiseDisjoint
        (fun δ => cubicThetaCuspNeighborhood δ H) := by
  classical
  obtain ⟨S,hS⟩ := cubicThetaCuspNeighborhood_cover
  obtain ⟨T,_,hT,hdis⟩ := cubicThetaFiniteCusps_disjoint (S.image (fun δ => δ⁻¹))
  refine ⟨S,T,?_,hdis⟩
  intro H
  rw [← hT H]
  have he : (⋃ δ∈S,cubicThetaCuspNeighborhood δ⁻¹ H)=
      ⋃ δ∈S.image (fun δ => δ⁻¹),cubicThetaCuspNeighborhood δ H := by
    ext q
    constructor
    · intro hq
      obtain ⟨δ,hδ,hqδ⟩ := mem_iUnion₂.mp hq
      exact mem_iUnion₂.mpr ⟨δ⁻¹,Finset.mem_image.mpr ⟨δ,hδ,rfl⟩,hqδ⟩
    · intro hq
      obtain ⟨δ,hδ,hqδ⟩ := mem_iUnion₂.mp hq
      obtain ⟨σ,hσ,rfl⟩ := Finset.mem_image.mp hδ
      exact mem_iUnion₂.mpr ⟨σ,hσ,hqδ⟩
  rw [← he]
  exact hS H

theorem cubicThetaExterior_integral {ε : ℝ} (hε : 0<ε) :
    ∃ (S R : Finset SL(2,Eisenstein)) (B : ℝ), 0≤B ∧
      ∀ F : cubicThetaSmoothTests,
    (∫ q, cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure)≤
      (1+ε)*(∫ q, cubicThetaQuotientEnergy F q ∂cubicThetaQuotientMeasure)+
      (∫ q in cubicThetaQuotientCore S 2, cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure)+
      B*(∫ q in cubicThetaQuotientCore R 2, cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure) := by
  classical
  obtain ⟨S,T,hcover,hdis⟩ := cubicThetaFiniteCusps_cover
  obtain ⟨R,B,hB,hcusp⟩ := cubicThetaCusp_exterior_mass hε
  refine ⟨S,R,T.card*B,mul_nonneg (Nat.cast_nonneg _) hB,?_⟩
  intro F
  have hm := cubicThetaFiniteCusps_mass_le S T (hcover 2) (hdis 2 (by norm_num)) F
  have he := cubicThetaFiniteCusps_energy_le T (hdis 1 (le_refl 1)) F
  have hs := Finset.sum_le_sum (s:=T) (fun δ hδ => hcusp δ F)
  rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul] at hs
  have hg := mul_le_mul_of_nonneg_left he (by positivity : 0≤1+ε)
  calc
    _ ≤ (∫ q in cubicThetaQuotientCore S 2, cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure)+
        ((1+ε)*(∑ δ∈T,∫ q in cubicThetaCuspNeighborhood δ 1,
          cubicThetaQuotientEnergy F q ∂cubicThetaQuotientMeasure)+
        T.card*(B*(∫ q in cubicThetaQuotientCore R 2,
          cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure))) :=
      hm.trans (add_le_add le_rfl hs)
    _ ≤ (∫ q in cubicThetaQuotientCore S 2, cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure)+
        ((1+ε)*(∫ q, cubicThetaQuotientEnergy F q ∂cubicThetaQuotientMeasure)+
        T.card*(B*(∫ q in cubicThetaQuotientCore R 2,
          cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure))) :=
      add_le_add le_rfl (add_le_add hg le_rfl)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaExteriorEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sharp exterior estimate extends by density to the actual closed
automorphic energy space. Its remainders are compact operators already
constructed from local Rellich compactness. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaExterior_energy {ε : ℝ} (hε : 0<ε) :
    ∃ (S R : Finset SL(2,Eisenstein)) (B : ℝ), 0≤B ∧
      ∀ u : cubicThetaGlobalEnergySpace,
    ‖cubicThetaGlobalInclusion u‖^2≤
      (1+ε)*‖cubicThetaGlobalEnergyGradient u‖^2+
      ‖cubicThetaCoreRestriction S 2 u‖^2+B*‖cubicThetaCoreRestriction R 2 u‖^2 := by
  obtain ⟨S,R,B,hB,h⟩ := cubicThetaExterior_integral hε
  refine ⟨S,R,B,hB,?_⟩
  let K : Set cubicThetaGlobalEnergySpace := {u | ‖cubicThetaGlobalInclusion u‖^2≤
    (1+ε)*‖cubicThetaGlobalEnergyGradient u‖^2+
      ‖cubicThetaCoreRestriction S 2 u‖^2+B*‖cubicThetaCoreRestriction R 2 u‖^2}
  have hK : IsClosed K := isClosed_le (by fun_prop) (by fun_prop)
  have ht : Set.range cubicThetaGlobalEnergyTestLinear⊆K := by
    rintro u ⟨F,rfl⟩
    change ‖cubicThetaGlobalInclusion (cubicThetaGlobalEnergyTest F)‖^2≤
      (1+ε)*‖cubicThetaGlobalEnergyGradient (cubicThetaGlobalEnergyTest F)‖^2+
      ‖cubicThetaCoreRestriction S 2 (cubicThetaGlobalEnergyTest F)‖^2+
      B*‖cubicThetaCoreRestriction R 2 (cubicThetaGlobalEnergyTest F)‖^2
    rw [cubicThetaGlobalInclusion_test_norm_sq,cubicThetaGlobalGradient_test_norm_sq,
      cubicThetaCoreRestriction_test_norm_sq,cubicThetaCoreRestriction_test_norm_sq]
    exact h F
  intro u
  exact closure_minimal ht hK (cubicThetaGlobalEnergyTestLinear_dense u)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactEnergyCorrection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact corrections of the actual energy inclusion. The exterior
inequality gives a numerical-range bound with arbitrary coefficient
strictly larger than one half. -/
noncomputable section
open scoped MatrixGroups InnerProduct
namespace CubicFirstMoment

lemma cubicThetaCompactEnergyCorrection_inner (S R : Finset SL(2,Eisenstein)) (B : ℝ)
    (u : cubicThetaGlobalEnergySpace) :
    (inner ℂ (cubicThetaCompactEnergyCorrection S R B u) u).re=
      ‖cubicThetaCoreRestriction S 2 u‖^2+B*‖cubicThetaCoreRestriction R 2 u‖^2 := by
  let P := cubicThetaCoreRestriction S 2
  let Q := cubicThetaCoreRestriction R 2
  have hs : inner ℂ ((B:ℂ) • (Q.adjoint (Q u))) u=
      star (B:ℂ)*inner ℂ (Q.adjoint (Q u)) u :=
    inner_smul_left (𝕜:=ℂ) (E:=cubicThetaGlobalEnergySpace) (Q.adjoint (Q u)) u (B:ℂ)
  change (inner ℂ (P.adjoint (P u)+(B:ℂ) • (Q.adjoint (Q u))) u).re=_
  have hP := P.adjoint_inner_left u (P u)
  have hQ := Q.adjoint_inner_left u (Q u)
  have ha := inner_add_left (𝕜:=ℂ) (E:=cubicThetaGlobalEnergySpace)
    (P.adjoint (P u)) ((B:ℂ) • (Q.adjoint (Q u))) u
  have hb : inner ℂ ((B:ℂ) • (Q.adjoint (Q u))) u=(B:ℂ)*inner ℂ (Q u) (Q u) := by
    calc
      _ = star (B:ℂ)*inner ℂ (Q.adjoint (Q u)) u := hs
      _ = _ := by rw [hQ,RCLike.star_def,Complex.conj_ofReal]
  have hh := congrArg Complex.re (ha.trans (congrArg₂ (fun x y : ℂ => x+y) hP hb))
  have hPn : (inner ℂ (P u) (P u)).re=‖P u‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) (P u)
  have hQn : (inner ℂ (Q u) (Q u)).re=‖Q u‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) (Q u)
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,hPn,hQn] at hh
  exact hh

lemma cubicThetaEnergyMass_upper_mod_compact {ε : ℝ} (hε : 0<ε) :
    ∃ (S R : Finset SL(2,Eisenstein)) (B : ℝ), 0≤B ∧
      ∀ u : cubicThetaGlobalEnergySpace,
    (2+ε)*(inner ℂ (cubicThetaEnergyMass u) u).re≤
      (1+ε)*‖u‖^2+(inner ℂ (cubicThetaCompactEnergyCorrection S R B u) u).re := by
  obtain ⟨S,R,B,hB,h⟩ := cubicThetaExterior_energy hε
  refine ⟨S,R,B,hB,fun u => ?_⟩
  rw [cubicThetaEnergyMass_inner,cubicThetaCompactEnergyCorrection_inner,
    cubicThetaGlobalEnergy_norm_sq]
  nlinarith [h u]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEnergyRegularizer
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At every real spectral parameter below two the energy pencil admits
an explicit compact correction which is invertible. This is the local
Fredholm reduction used for continuation across the real axis. -/
noncomputable section
open scoped MatrixGroups InnerProduct NNReal
namespace CubicFirstMoment

def cubicThetaEnergyRegularizer (S R : Finset SL(2,Eisenstein)) (B ε z : ℝ) :
    cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace :=
  1-(z:ℂ) • cubicThetaEnergyMass+
    ((z/(2+ε):ℝ):ℂ) • cubicThetaCompactEnergyCorrection S R B

lemma cubicThetaEnergyRegularizer_inner (S R : Finset SL(2,Eisenstein)) (B ε z : ℝ)
    (u : cubicThetaGlobalEnergySpace) :
    (inner ℂ (cubicThetaEnergyRegularizer S R B ε z u) u).re=
      ‖u‖^2-z*(inner ℂ (cubicThetaEnergyMass u) u).re+
        (z/(2+ε))*(inner ℂ (cubicThetaCompactEnergyCorrection S R B u) u).re := by
  let v := cubicThetaEnergyMass u
  let w := cubicThetaCompactEnergyCorrection S R B u
  have ha := inner_add_left (𝕜:=ℂ) (E:=cubicThetaGlobalEnergySpace)
    (u-(z:ℂ) • v) (((z/(2+ε):ℝ):ℂ) • w) u
  have hs := inner_sub_left (𝕜:=ℂ) (E:=cubicThetaGlobalEnergySpace) u ((z:ℂ) • v) u
  have hh := congrArg Complex.re (ha.trans (congrArg₂ (fun x y : ℂ => x+y) hs rfl))
  have hnorm : (inner ℂ u u).re=‖u‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) u
  rw [Complex.add_re,Complex.sub_re,hnorm,cubicThetaEnergy_real_smul_inner,
    cubicThetaEnergy_real_smul_inner] at hh
  exact hh

lemma cubicThetaEnergyRegularizer_unit {ε z : ℝ} (hε : 0<ε) (hz : 0≤z)
    (hgap : z*(1+ε)<2+ε)
    (S R : Finset SL(2,Eisenstein)) (B : ℝ)
    (hupper : ∀ u : cubicThetaGlobalEnergySpace,
      (2+ε)*(inner ℂ (cubicThetaEnergyMass u) u).re≤
        (1+ε)*‖u‖^2+(inner ℂ (cubicThetaCompactEnergyCorrection S R B u) u).re) :
    IsUnit (cubicThetaEnergyRegularizer S R B ε z) := by
  have hd : 0<2+ε := by linarith
  let c : ℝ := 1-z*(1+ε)/(2+ε)
  have hc : 0 < c := sub_pos.mpr ((div_lt_one hd).mpr hgap)
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map _ (c:=⟨c,hc.le⟩) hc
  intro u
  have hs := mul_le_mul_of_nonneg_left (hupper u) (div_nonneg hz hd.le)
  have hcancel : z/(2+ε)*((2+ε)*(inner ℂ (cubicThetaEnergyMass u) u).re)=
      z*(inner ℂ (cubicThetaEnergyMass u) u).re := by field_simp
  rw [hcancel] at hs
  calc
    ‖u‖^2*(⟨c,hc.le⟩:ℝ≥0)≤(inner ℂ (cubicThetaEnergyRegularizer S R B ε z u) u).re := by
      rw [cubicThetaEnergyRegularizer_inner]
      change ‖u‖^2*c≤_
      dsimp [c]
      rw [mul_add] at hs
      have he : z/(2+ε)*(1+ε)=z*(1+ε)/(2+ε) := by ring
      rw [← mul_assoc,he] at hs
      have hlin (N M Q r t : ℝ) (h : z*M ≤ r*N+t*Q) :
          N*(1-r)≤N-z*M+t*Q := by nlinarith only [h]
      exact hlin _ _ _ _ _ hs
    _ ≤ _ := Complex.re_le_norm _

theorem cubicThetaEnergyPencil_compact_regularizer {z : ℝ} (hz : 0≤z) (hz2 : z<2) :
    ∃ K : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace,
      IsCompactOperator K ∧ IsUnit (1-(z:ℂ) • cubicThetaEnergyMass+K) := by
  let ε : ℝ := (2-z)/(2*(z+1))
  have hε : 0<ε := div_pos (sub_pos.mpr hz2) (by positivity)
  have hgap : z*(1+ε)<2+ε := by
    have he : ε*(2*(z+1))=2-z := by dsimp [ε]; field_simp
    nlinarith [mul_pos hε (by linarith : 0<z+2)]
  obtain ⟨S,R,B,_,h⟩ := cubicThetaEnergyMass_upper_mod_compact hε
  refine ⟨((z/(2+ε):ℝ):ℂ) • cubicThetaCompactEnergyCorrection S R B,
    (cubicThetaCompactEnergyCorrection_compact S R B).smul (((z/(2+ε):ℝ):ℂ)),?_⟩
  exact cubicThetaEnergyRegularizer_unit hε hz hgap S R B h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEnergyPencilKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact correction makes every real exceptional energy space
below the threshold finite dimensional. The proof uses the actual
compact core operators, not a spectral finiteness assumption. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaEnergyPencil_finite_ker {z : ℝ} (hz : 0≤z) (hz2 : z<2) :
    FiniteDimensional ℂ (cubicThetaEnergyPencil (z:ℂ)).ker := by
  obtain ⟨K,hK,hunit⟩ := cubicThetaEnergyPencil_compact_regularizer hz hz2
  let T := cubicThetaEnergyPencil (z:ℂ)
  let U : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace := T+K
  have hU : IsUnit U := hunit
  have hleft (u : cubicThetaGlobalEnergySpace) : Ring.inverse U (U u)=u := by
    change (Ring.inverse U*U) u=u
    rw [Ring.inverse_mul_cancel _ hU]
    rfl
  have hid : T.ker.subtypeL=(Ring.inverse U).comp (K.comp T.ker.subtypeL) := by
    apply ContinuousLinearMap.ext
    intro u
    have he : U u.val=K u.val := by
      change T u.val+K u.val=K u.val
      have hz : T (u : cubicThetaGlobalEnergySpace)=0 := u.property
      rw [hz,zero_add]
    change u.val=Ring.inverse U (K u.val)
    rw [← he,hleft]
  have hi : IsCompactOperator T.ker.subtypeL := by
    rw [hid]
    exact (hK.comp_clm T.ker.subtypeL).clm_comp (Ring.inverse U)
  have hc := hi.codRestrict (V:=T.ker) (fun u => u.property) T.isClosed_ker
  apply FiniteDimensional.of_isCompactOperator_id (𝕜:=ℂ)
  exact hc

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaExceptionalProjection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite exceptional eigenspace has an actual orthogonal
projection. Adding it to the self-adjoint real pencil removes its kernel. -/
noncomputable section
open scoped InnerProduct
namespace CubicFirstMoment

lemma cubicThetaExceptionalProjection_compact {z : ℝ} (hz : 0≤z) (hz2 : z<2) :
    IsCompactOperator (cubicThetaExceptionalProjection (z:ℂ)) := by
  have := cubicThetaEnergyPencil_finite_ker hz hz2
  exact (isCompactOperator_of_locallyCompactSpace_rng (cubicThetaEnergyPencil (z:ℂ)).ker.subtypeL).comp_clm
    (cubicThetaEnergyPencil (z:ℂ)).ker.orthogonalProjectionOnto

theorem cubicThetaProjectedPencil_unit {z : ℝ} (hz : 0≤z) (hz2 : z<2) :
    IsUnit (cubicThetaEnergyPencil (z:ℂ)+cubicThetaExceptionalProjection (z:ℂ)) := by
  obtain ⟨K,hK,hu⟩ := cubicThetaEnergyPencil_compact_regularizer hz hz2
  let P := cubicThetaExceptionalProjection (z:ℂ)
  apply cubicThetaCompactPerturbation_unit _ (K-P)
  · exact hK.sub (cubicThetaExceptionalProjection_compact hz hz2)
  · have he : (cubicThetaEnergyPencil (z:ℂ)+P)+(K-P)=cubicThetaEnergyPencil (z:ℂ)+K := by abel
    rw [he]
    exact hu
  · exact cubicThetaProjectedPencil_injective z

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalEnergyResolvent
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local candidate inverse at an exceptional real parameter is an
analytic inverse on the complementary subspace plus an explicit simple
pole on the finite exceptional space. Algebraic agreement with the
original inverse is proved separately. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaLocalEnergyResolvent_meromorphic {z : ℝ} (hz : 0≤z) (hz2 : z<2) :
    MeromorphicAt (cubicThetaLocalEnergyResolvent (z:ℂ)) (z:ℂ) := by
  have hu := cubicThetaProjectedPencil_unit hz hz2
  have hi : AnalyticAt ℂ Ring.inverse
      (cubicThetaEnergyPencil (z:ℂ)+cubicThetaExceptionalProjection (z:ℂ)) := by
    convert analyticAt_inverse (𝕜:=ℂ) (A:=cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) hu.unit using 1
    all_goals try with_reducible_and_instances rfl
    exact hu.unit_spec
  have hp : AnalyticAt ℂ
      (fun w => cubicThetaEnergyPencil w+cubicThetaExceptionalProjection (z:ℂ)) (z:ℂ) :=
    (cubicThetaEnergyPencil_analytic (z:ℂ)).add analyticAt_const
  have hcomp : AnalyticAt ℂ (fun w : ℂ => Ring.inverse
      (cubicThetaEnergyPencil w+cubicThetaExceptionalProjection (z:ℂ))) (z:ℂ) :=
    hi.comp (f:=fun w : ℂ => cubicThetaEnergyPencil w+cubicThetaExceptionalProjection (z:ℂ)) (x:=(z:ℂ)) hp
  have hmain : AnalyticAt ℂ (fun w : ℂ => Ring.inverse
      (cubicThetaEnergyPencil w+cubicThetaExceptionalProjection (z:ℂ))*
        (1-cubicThetaExceptionalProjection (z:ℂ))) (z:ℂ) := AnalyticAt.mul (𝕜:=ℂ)
    (A:=cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) hcomp
    (show AnalyticAt ℂ (fun _ : ℂ => 1-cubicThetaExceptionalProjection (z:ℂ)) (z:ℂ)
      from analyticAt_const)
  have hscalar : MeromorphicAt (fun w : ℂ => (z:ℂ)/((z:ℂ)-w)) (z:ℂ) :=
    (MeromorphicAt.const _ _).div ((MeromorphicAt.const _ _).sub (MeromorphicAt.id _))
  exact hmain.meromorphicAt.add (cubicThetaMeromorphic_clm
    ((ContinuousLinearMap.id ℂ ℂ).smulRight (cubicThetaExceptionalProjection (z:ℂ))) hscalar)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEnergyInverseContinuation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local meromorphic formula agrees with the actual inverse on a
punctured neighborhood of each positive real parameter below two. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

lemma cubicThetaEnergyPencil_unit_near_real {z : ℝ} (hz : 0<z) (hz2 : z<2) :
    ∀ᶠ w : ℂ in 𝓝[≠] (z:ℂ), IsUnit (cubicThetaEnergyPencil w) := by
  have hu := cubicThetaProjectedPencil_unit hz.le hz2
  have ha := (cubicThetaEnergyPencil_analytic (z:ℂ)).add
    (show AnalyticAt ℂ (fun _ : ℂ => cubicThetaExceptionalProjection (z:ℂ)) (z:ℂ)
      from analyticAt_const)
  have hunit : ∀ᶠ w : ℂ in 𝓝 (z:ℂ),
      IsUnit (cubicThetaEnergyPencil w+cubicThetaExceptionalProjection (z:ℂ)) :=
    by
      have hn : {A : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace | IsUnit A} ∈
          𝓝 (cubicThetaEnergyPencil (z:ℂ)+cubicThetaExceptionalProjection (z:ℂ)) :=
        (Units.isOpen (R:=cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace)).mem_nhds hu
      exact ha.continuousAt.eventually hn
  filter_upwards [nhdsWithin_le_nhds hunit,self_mem_nhdsWithin] with w hwu hw
  have hcz : (z:ℂ)≠0 := by exact_mod_cast hz.ne'
  have hc : 1-w/(z:ℂ)≠0 := by
    apply sub_ne_zero.mpr
    intro he
    exact hw ((div_eq_one_iff_eq hcz).mp he.symm)
  have hTP := cubicThetaEnergyPencil_mul_projection hz.ne' w
  exact (cubicThetaProjection_inverse_data _ _ _
    (cubicThetaExceptionalProjection_idempotent _) hTP
    ((cubicThetaEnergyPencil_commute_projection hz.ne' w).eq.symm.trans hTP) hwu hc).1

theorem cubicThetaEnergyInverse_meromorphic_real {z : ℝ} (hz : 0<z) (hz2 : z<2) :
    MeromorphicAt (fun w : ℂ => Ring.inverse (cubicThetaEnergyPencil w)) (z:ℂ) := by
  have hu := cubicThetaProjectedPencil_unit hz.le hz2
  have ha := (cubicThetaEnergyPencil_analytic (z:ℂ)).add
    (show AnalyticAt ℂ (fun _ : ℂ => cubicThetaExceptionalProjection (z:ℂ)) (z:ℂ)
      from analyticAt_const)
  have hunit : ∀ᶠ w : ℂ in 𝓝 (z:ℂ),
      IsUnit (cubicThetaEnergyPencil w+cubicThetaExceptionalProjection (z:ℂ)) :=
    by
      have hn : {A : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace | IsUnit A} ∈
          𝓝 (cubicThetaEnergyPencil (z:ℂ)+cubicThetaExceptionalProjection (z:ℂ)) :=
        (Units.isOpen (R:=cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace)).mem_nhds hu
      exact ha.continuousAt.eventually hn
  apply (cubicThetaLocalEnergyResolvent_meromorphic hz.le hz2).congr
  filter_upwards [nhdsWithin_le_nhds hunit,self_mem_nhdsWithin] with w hwu hw
  exact cubicThetaLocalEnergyResolvent_eq_inverse hz.ne' (by simpa using hw) hwu

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEnergyRegularDomain
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The energy inverse is analytic off the positive real spectral ray,
and meromorphic across its part strictly below the cusp threshold two. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

theorem cubicThetaEnergyInverse_meromorphic {z : ℂ} (hz : z.im≠0 ∨ z.re<2) :
    MeromorphicAt (fun w => Ring.inverse (cubicThetaEnergyPencil w)) z := by
  by_cases hr : z.im≠0 ∨ z.re<1
  · exact (cubicThetaEnergyInverse_analytic hr).meromorphicAt
  · have him : z.im=0 := not_not.mp (not_or.mp hr).1
    have hre : 1≤z.re := le_of_not_gt (not_or.mp hr).2
    have hlt : z.re<2 := hz.resolve_left (fun h => h him)
    have he : (z.re:ℂ)=z := Complex.ext rfl (by simpa only [Complex.ofReal_im] using him.symm)
    rw [← he]
    exact cubicThetaEnergyInverse_meromorphic_real (by linarith) hlt

lemma cubicThetaEnergyPencil_eventually_unit {z : ℂ} (hz : z.im≠0 ∨ z.re<2) :
    ∀ᶠ w : ℂ in 𝓝[≠] z, IsUnit (cubicThetaEnergyPencil w) := by
  by_cases hr : z.im≠0 ∨ z.re<1
  · have hn : {A : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace | IsUnit A} ∈
        𝓝 (cubicThetaEnergyPencil z) :=
      (Units.isOpen (R:=cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace)).mem_nhds
        (cubicThetaEnergyPencil_unit hr)
    exact nhdsWithin_le_nhds ((cubicThetaEnergyPencil_analytic z).continuousAt.eventually hn)
  · have him : z.im=0 := not_not.mp (not_or.mp hr).1
    have hre : 1≤z.re := le_of_not_gt (not_or.mp hr).2
    have hlt : z.re<2 := hz.resolve_left (fun h => h him)
    have he : (z.re:ℂ)=z := Complex.ext rfl (by simpa only [Complex.ofReal_im] using him.symm)
    rw [← he]
    exact cubicThetaEnergyPencil_unit_near_real (by linarith) hlt

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEnergyResolventTransport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport from the actual energy space to the actual quotient L2
space. Both inverse identities are retained, including at real regular
parameters outside the initial positive-contraction domain. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaEnergyValueResolvent_left {z : ℂ}
    (hu : IsUnit (cubicThetaEnergyPencil z)) :
    (1-z • cubicThetaGlobalGreen)*cubicThetaEnergyValueResolvent z=cubicThetaGlobalGreen := by
  apply ContinuousLinearMap.ext
  intro F
  have h := congrArg
    (fun A : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace =>
      cubicThetaGlobalInclusion (A (cubicThetaGlobalInclusion.adjoint F)))
    (Ring.mul_inverse_cancel (cubicThetaEnergyPencil z) hu)
  change cubicThetaGlobalInclusion
    (Ring.inverse (cubicThetaEnergyPencil z) (cubicThetaGlobalInclusion.adjoint F)-
      z • cubicThetaGlobalInclusion.adjoint (cubicThetaGlobalInclusion
        (Ring.inverse (cubicThetaEnergyPencil z) (cubicThetaGlobalInclusion.adjoint F))))=
      cubicThetaGlobalInclusion (cubicThetaGlobalInclusion.adjoint F) at h
  change cubicThetaGlobalInclusion
    (Ring.inverse (cubicThetaEnergyPencil z) (cubicThetaGlobalInclusion.adjoint F))-
      z • cubicThetaGlobalInclusion (cubicThetaGlobalInclusion.adjoint (cubicThetaGlobalInclusion
        (Ring.inverse (cubicThetaEnergyPencil z) (cubicThetaGlobalInclusion.adjoint F))))=
    cubicThetaGlobalInclusion (cubicThetaGlobalInclusion.adjoint F)
  simpa only [map_sub,map_smul] using h

lemma cubicThetaEnergyValueResolvent_right {z : ℂ}
    (hu : IsUnit (cubicThetaEnergyPencil z)) :
    cubicThetaEnergyValueResolvent z*(1-z • cubicThetaGlobalGreen)=cubicThetaGlobalGreen := by
  apply ContinuousLinearMap.ext
  intro F
  have h := congrArg
    (fun A : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace =>
      cubicThetaGlobalInclusion (A (cubicThetaGlobalInclusion.adjoint F)))
    (Ring.inverse_mul_cancel (cubicThetaEnergyPencil z) hu)
  change cubicThetaGlobalInclusion (Ring.inverse (cubicThetaEnergyPencil z)
    (cubicThetaGlobalInclusion.adjoint F-z • cubicThetaGlobalInclusion.adjoint
      (cubicThetaGlobalInclusion (cubicThetaGlobalInclusion.adjoint F))))=
    cubicThetaGlobalInclusion (cubicThetaGlobalInclusion.adjoint F) at h
  change cubicThetaGlobalInclusion (Ring.inverse (cubicThetaEnergyPencil z)
    (cubicThetaGlobalInclusion.adjoint
      (F-z • cubicThetaGlobalInclusion (cubicThetaGlobalInclusion.adjoint F))))=
    cubicThetaGlobalInclusion (cubicThetaGlobalInclusion.adjoint F)
  simpa only [map_sub,map_smul] using h

lemma cubicThetaGlobalGreen_unit_of_energy {z : ℂ}
    (hu : IsUnit (cubicThetaEnergyPencil z)) : IsUnit (1-z • cubicThetaGlobalGreen) := by
  let Q := 1-z • cubicThetaGlobalGreen
  let C := 1+z • cubicThetaEnergyValueResolvent z
  have hQC : Q*C=1 := by
    dsimp only [C]
    rw [mul_add,mul_one,mul_smul_comm,cubicThetaEnergyValueResolvent_left hu]
    dsimp only [Q]
    abel
  have hCQ : C*Q=1 := by
    dsimp only [C]
    rw [add_mul,one_mul,smul_mul_assoc,cubicThetaEnergyValueResolvent_right hu]
    dsimp only [Q]
    abel
  exact ⟨⟨Q,C,hQC,hCQ⟩,rfl⟩

lemma cubicThetaEnergyValueResolvent_eq {z : ℂ}
    (hu : IsUnit (cubicThetaEnergyPencil z)) :
    cubicThetaEnergyValueResolvent z=cubicThetaGlobalResolvent z := by
  have h := cubicThetaEnergyValueResolvent_left hu
  have hQ := cubicThetaGlobalGreen_unit_of_energy hu
  unfold cubicThetaGlobalResolvent
  calc
    _ = Ring.inverse (1-z • cubicThetaGlobalGreen)*
        ((1-z • cubicThetaGlobalGreen)*cubicThetaEnergyValueResolvent z) := by
      rw [← mul_assoc,Ring.inverse_mul_cancel _ hQ,one_mul]
    _ = _ := congrArg (fun A => Ring.inverse (1-z • cubicThetaGlobalGreen)*A) h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGlobalResolventWeak
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global resolvent has a genuine energy lift solving the weak
mass-plus-gradient equation. This does not assume elliptic regularity. -/
noncomputable section
open scoped InnerProduct
namespace CubicFirstMoment

lemma cubicThetaGlobalEnergy_inner (u v : cubicThetaGlobalEnergySpace) :
    inner ℂ u v=inner ℂ (cubicThetaGlobalInclusion u) (cubicThetaGlobalInclusion v)+
      inner ℂ (cubicThetaGlobalEnergyGradient u) (cubicThetaGlobalEnergyGradient v) :=
  WithLp.prod_inner_apply (u:CubicThetaGlobalEnergyAmbient) (v:CubicThetaGlobalEnergyAmbient)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGlobalMeromorphic
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Meromorphic continuation of the actual global weak resolvent past
the finite exceptional spectrum, throughout the Eisenstein half-plane. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

theorem cubicThetaGlobalResolvent_meromorphic {z : ℂ} (hz : z.im≠0 ∨ z.re<2) :
    MeromorphicAt cubicThetaGlobalResolvent z := by
  have h0 := cubicThetaMeromorphic_clm
      (E:=cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace)
      (F:=CubicThetaGlobalL2 →L[ℂ] CubicThetaGlobalL2)
      (f:=fun w : ℂ => Ring.inverse (cubicThetaEnergyPencil w)) (z:=z)
      cubicThetaEnergyResolventTransport (cubicThetaEnergyInverse_meromorphic hz)
  have h : MeromorphicAt cubicThetaEnergyValueResolvent z := h0
  apply h.congr
  filter_upwards [cubicThetaEnergyPencil_eventually_unit hz] with w hw
  exact cubicThetaEnergyValueResolvent_eq hw

theorem cubicThetaGlobalSpectralResolvent_meromorphic {s : ℂ} (hs : 1 < s.re) :
    MeromorphicAt cubicThetaGlobalSpectralResolvent s := by
  have h := cubicThetaGlobalResolvent_meromorphic
    (cubicThetaGlobalSpectralParameter_below_threshold hs)
  have hp : AnalyticAt ℂ cubicThetaGlobalSpectralParameter s :=
    analyticAt_const.sub (analyticAt_id.mul (analyticAt_id.sub analyticAt_const))
  exact h.comp_analyticAt hp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaContinuedWeakEquation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At every regular parameter the continued inverse solves the actual
global variational equation. The equation uses the completed gradient
graph and is not an abstract substitute for the geometric Laplacian. -/
noncomputable section
open scoped InnerProduct
namespace CubicFirstMoment

lemma cubicThetaContinuedEnergyLift_value {z : ℂ} (hu : IsUnit (cubicThetaEnergyPencil z))
    (F : CubicThetaGlobalL2) :
    cubicThetaGlobalInclusion (cubicThetaContinuedEnergyLift z F)=cubicThetaGlobalResolvent z F := by
  have h := congrArg (fun A : CubicThetaGlobalL2 →L[ℂ] CubicThetaGlobalL2 => A F)
    (cubicThetaEnergyValueResolvent_eq hu)
  exact h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaForcedResolvent
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global resolvent applied to the literal incoming arithmetic
forcing. Identification with the Eisenstein remainder is a separate step. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaForcedResolvent_meromorphic {s : ℂ} (hs : 1 < s.re) :
    MeromorphicAt cubicThetaForcedResolvent s :=
  cubicThetaMeromorphic_apply (cubicThetaGlobalSpectralResolvent_meromorphic hs)
    (cubicThetaForcingL2_analytic s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaWeakUniqueness
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniqueness for the actual completed energy equation at regular
parameters, used to identify the arithmetic Eisenstein remainder. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaEnergyPencil_inner (z : ℂ) (v u : cubicThetaGlobalEnergySpace) :
    inner ℂ v (cubicThetaEnergyPencil z u)=
      inner ℂ (cubicThetaGlobalEnergyGradient v) (cubicThetaGlobalEnergyGradient u)+
        (1-z)*inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaGlobalInclusion u) := by
  have hsub := inner_sub_right (𝕜:=ℂ) (E:=cubicThetaGlobalEnergySpace) v u
    (z • cubicThetaGlobalInclusion.adjoint (cubicThetaGlobalInclusion u))
  have hsmul := inner_smul_right (𝕜:=ℂ) (E:=cubicThetaGlobalEnergySpace) v
    (cubicThetaGlobalInclusion.adjoint (cubicThetaGlobalInclusion u)) z
  have ha := cubicThetaGlobalInclusion.adjoint_inner_right v (cubicThetaGlobalInclusion u)
  change inner ℂ v (cubicThetaGlobalInclusion.adjoint (cubicThetaGlobalInclusion u))=
    inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaGlobalInclusion u) at ha
  have he := cubicThetaGlobalEnergy_inner v u
  change inner ℂ v (u-z • cubicThetaGlobalInclusion.adjoint (cubicThetaGlobalInclusion u))=_
  rw [hsub,hsmul,ha,he]
  ring

theorem cubicThetaContinuedEnergyLift_unique {z : ℂ}
    (hz : IsUnit (cubicThetaEnergyPencil z)) (F : CubicThetaGlobalL2)
    (u : cubicThetaGlobalEnergySpace)
    (hu : ∀ v : cubicThetaGlobalEnergySpace,
      inner ℂ (cubicThetaGlobalEnergyGradient v) (cubicThetaGlobalEnergyGradient u)+
        (1-z)*inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaGlobalInclusion u)=
          inner ℂ (cubicThetaGlobalInclusion v) F) :
    u=cubicThetaContinuedEnergyLift z F := by
  have he : cubicThetaEnergyPencil z u=cubicThetaGlobalInclusion.adjoint F := by
    apply ext_inner_left ℂ
    intro v
    have hf := cubicThetaEnergyPencil_inner z v u
    have ha := cubicThetaGlobalInclusion.adjoint_inner_right v F
    change inner ℂ v (cubicThetaGlobalInclusion.adjoint F)=
      inner ℂ (cubicThetaGlobalInclusion v) F at ha
    exact hf.trans ((hu v).trans ha.symm)
  have h := congrArg (fun w => Ring.inverse (cubicThetaEnergyPencil z) w) he
  have hi := congrArg (fun A : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace => A u)
    (Ring.inverse_mul_cancel (cubicThetaEnergyPencil z) hz)
  exact hi.symm.trans h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticResolvent
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continued global resolvent is the literal arithmetic Eisenstein
remainder on its initial half-plane of absolute convergence. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaArithmeticEnergy_eq_continued {s : ℂ} (hs : 3 < s.re) :
    cubicThetaArithmeticEnergy s hs=cubicThetaContinuedEnergyLift
      (cubicThetaGlobalSpectralParameter s) (cubicThetaForcingL2 s) := by
  apply cubicThetaContinuedEnergyLift_unique
    (cubicThetaEnergyPencil_unit (cubicThetaGlobalSpectralParameter_regular
      (by linarith) (Or.inr (by linarith))))
  intro v
  have h := cubicThetaArithmetic_global_weak hs v
  have he : 1-cubicThetaGlobalSpectralParameter s=s*(s-2) := by
    unfold cubicThetaGlobalSpectralParameter
    ring
  rwa [he]

theorem cubicThetaArithmeticL2_eq_forcedResolvent {s : ℂ} (hs : 3 < s.re) :
    cubicThetaArithmeticL2 s hs=cubicThetaForcedResolvent s := by
  have hu := cubicThetaEnergyPencil_unit (cubicThetaGlobalSpectralParameter_regular
    (show 1 < s.re by linarith) (Or.inr (by linarith)))
  calc
    _ = cubicThetaGlobalInclusion (cubicThetaArithmeticEnergy s hs) := rfl
    _ = cubicThetaGlobalInclusion (cubicThetaContinuedEnergyLift
        (cubicThetaGlobalSpectralParameter s) (cubicThetaForcingL2 s)) :=
      congrArg cubicThetaGlobalInclusion (cubicThetaArithmeticEnergy_eq_continued hs)
    _ = cubicThetaForcedResolvent s := cubicThetaContinuedEnergyLift_value hu _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticDistribution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continued family tested against actual compact automorphic
sections. On the initial half-plane these are the literal quotient
integrals of the arithmetic Eisenstein remainder. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaArithmeticDistribution_meromorphic (F : CubicThetaSection)
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) {s : ℂ} (hs : 1 < s.re) :
    MeromorphicAt (cubicThetaArithmeticDistribution F hc) s :=
  cubicThetaMeromorphic_clm (innerSL ℂ ((cubicThetaCompactSection_memLp F hc).toLp _))
    (cubicThetaForcedResolvent_meromorphic hs)

lemma cubicThetaArithmeticDistribution_right (F : CubicThetaSection)
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) {s : ℂ} (hs : 3 < s.re) :
    cubicThetaArithmeticDistribution F hc s=
      ∫ q, cubicThetaSectionPairing F (cubicThetaArithmeticSection s (by linarith)) q
        ∂cubicThetaQuotientMeasure := by
  unfold cubicThetaArithmeticDistribution
  rw [← cubicThetaArithmeticL2_eq_forcedResolvent hs]
  exact cubicThetaSectionPairing_L2 F _ (cubicThetaCompactSection_memLp F hc)
    (cubicThetaArithmeticSection_memLp hs)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteEnergySections
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual C1 sections of finite value and gradient energy form a
complex vector space. This retains their literal pointwise functions. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaFiniteEnergyEmbedding_smooth (F : cubicThetaSmoothTests) :
    cubicThetaFiniteEnergyEmbedding (cubicThetaSmoothToFiniteEnergy F)=cubicThetaGlobalEnergyTest F := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded restriction from the completed global energy space to the
literal high cusp strip, extending all actual C1 finite-energy sections. -/
noncomputable section
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.finiteEnergy_addCommGroup
lemma cubicThetaFiniteEnergyEmbedding_dense : DenseRange cubicThetaFiniteEnergyEmbedding := by
  have h : DenseRange (fun F : cubicThetaSmoothTests =>
      cubicThetaFiniteEnergyEmbedding (cubicThetaSmoothToFiniteEnergy F)) := by
    have he : (fun F : cubicThetaSmoothTests =>
        cubicThetaFiniteEnergyEmbedding (cubicThetaSmoothToFiniteEnergy F))=
        (fun F => cubicThetaGlobalEnergyTestLinear F) := by
      funext F
      exact cubicThetaFiniteEnergyEmbedding_smooth F
    rw [he]
    exact cubicThetaGlobalEnergyTestLinear_dense
  exact h.of_comp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaForcedCusp
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual arithmetic continuation restricted to the high cusp.
Both its meromorphic dependence and its initial pointwise representative
are retained in the L2 strip space. -/
noncomputable section
open Filter Topology MeasureTheory
namespace CubicFirstMoment

def cubicThetaArithmeticFiniteEnergy (s : ℂ) (hs : 3 < s.re) : cubicThetaFiniteEnergySections :=
  ⟨cubicThetaArithmeticSection s (by linarith),
    cubicThetaArithmeticSectionFunction_contDiffOn_one (by linarith),
    cubicThetaArithmeticSection_memLp hs,cubicThetaArithmeticGradientRepresentative_memLp hs⟩

lemma cubicThetaArithmeticFiniteEnergy_embedding (s : ℂ) (hs : 3 < s.re) :
    cubicThetaFiniteEnergyEmbedding (cubicThetaArithmeticFiniteEnergy s hs)=
      cubicThetaArithmeticEnergy s hs := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaIntegralQuotient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integral Mobius changes of cusp descend to the actual principal
quotient and preserve its constructed hyperbolic measure. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaIntegralQuotient_measurePreserving (δ : SL(2,Eisenstein)) :
    MeasurePreserving (cubicThetaIntegralQuotientMap δ) cubicThetaQuotientMeasure
      cubicThetaQuotientMeasure := by
  refine ⟨(cubicThetaIntegralQuotientMap_continuous δ).measurable,?_⟩
  calc
    _ = ((cubicThetaPointMeasure.restrict cubicThetaFundamentalDomain).map
        (fun p : CubicThetaPoint => δ • p)).map cubicThetaQuotientMap := by
      rw [cubicThetaQuotientMeasure,
        Measure.map_map (cubicThetaIntegralQuotientMap_continuous δ).measurable
          cubicThetaQuotientMap_open.continuous.measurable,
        Measure.map_map cubicThetaQuotientMap_open.continuous.measurable
          (measurable_const_smul δ)]
      rfl
    _ = (cubicThetaPointMeasure.restrict
        ((fun p : CubicThetaPoint => δ • p) '' cubicThetaFundamentalDomain)).map
        cubicThetaQuotientMap := by
      rw [cubicThetaSmul_map_restrict δ cubicThetaFundamentalDomain_measurable]
    _ = cubicThetaQuotientMeasure :=
      (cubicThetaQuotientMeasure_independent (cubicThetaIntegralImage_fundamental δ)).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric inversion extends isometrically to the actual
completed automorphic energy space. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.instAddCommGroupSubtypeContinuousMapCubicThetaPointComplexMemSubmoduleCubicThetaSectionCubicThetaSmoothTests
lemma cubicThetaInversion_test_mass_norm (F : cubicThetaSmoothTests) :
    ‖cubicThetaGlobalInclusion (cubicThetaGlobalEnergyTest (cubicThetaInversionSmooth F))‖^2=
      ‖cubicThetaGlobalInclusion (cubicThetaGlobalEnergyTest F)‖^2 := by
  rw [cubicThetaGlobalInclusion_test_norm_sq,cubicThetaGlobalInclusion_test_norm_sq]
  calc
    _ = ∫ q, cubicThetaSectionNorm F
        (cubicThetaIntegralQuotientMap cubicThetaFullInversion q)^2 ∂cubicThetaQuotientMeasure := by
      apply integral_congr_ae
      filter_upwards with q
      exact congrArg (fun x : ℝ => x^2) (cubicThetaInversionSection_norm F q)
    _ = _ := (cubicThetaIntegralQuotient_measurePreserving cubicThetaFullInversion).integral_comp
      (cubicThetaIntegralQuotientHomeomorph cubicThetaFullInversion).measurableEmbedding
      (fun q => cubicThetaSectionNorm F q^2)

lemma cubicThetaInversion_test_gradient_norm (F : cubicThetaSmoothTests) :
    ‖cubicThetaGlobalEnergyGradient (cubicThetaGlobalEnergyTest (cubicThetaInversionSmooth F))‖^2=
      ‖cubicThetaGlobalEnergyGradient (cubicThetaGlobalEnergyTest F)‖^2 := by
  rw [cubicThetaGlobalGradient_test_norm_sq,cubicThetaGlobalGradient_test_norm_sq]
  calc
    _ = ∫ q, cubicThetaQuotientEnergy F
        (cubicThetaIntegralQuotientMap cubicThetaFullInversion q) ∂cubicThetaQuotientMeasure := by
      apply integral_congr_ae
      filter_upwards with q
      exact cubicThetaInversion_quotient_energy F q
    _ = _ := (cubicThetaIntegralQuotient_measurePreserving cubicThetaFullInversion).integral_comp
      (cubicThetaIntegralQuotientHomeomorph cubicThetaFullInversion).measurableEmbedding
      (cubicThetaQuotientEnergy F)

lemma cubicThetaInversion_test_norm (F : cubicThetaSmoothTests) :
    ‖cubicThetaGlobalEnergyTest (cubicThetaInversionSmooth F)‖=‖cubicThetaGlobalEnergyTest F‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  rw [cubicThetaGlobalEnergy_norm_sq,cubicThetaGlobalEnergy_norm_sq,
    cubicThetaInversion_test_mass_norm,cubicThetaInversion_test_gradient_norm]

def cubicThetaInversionEnergy : cubicThetaGlobalEnergySpace →ₗᵢ[ℂ] cubicThetaGlobalEnergySpace :=
  (cubicThetaGlobalEnergyTestLinear.comp cubicThetaInversionSmoothLinear).extendOfIsometry
    cubicThetaGlobalEnergyTestLinear_dense cubicThetaInversion_test_norm

lemma cubicThetaInversionEnergy_test (F : cubicThetaSmoothTests) :
    cubicThetaInversionEnergy (cubicThetaGlobalEnergyTest F)=
      cubicThetaGlobalEnergyTest (cubicThetaInversionSmooth F) :=
  LinearMap.extendOfIsometry_eq _ _ _ F

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.instMeasurableSpace
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

lemma cubicThetaInversionSection_memLp (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    MemLp (cubicThetaSectionRepresentative (cubicThetaInversionSection F)) 2
      cubicThetaQuotientMeasure := by
  have hn : MemLp (cubicThetaSectionNorm F) 2 cubicThetaQuotientMeasure := by
    simpa only [cubicThetaSectionRepresentative_norm] using hF.norm
  have hi := hn.comp_measurePreserving
    (cubicThetaIntegralQuotient_measurePreserving cubicThetaFullInversion)
  apply (memLp_norm_iff
    (cubicThetaSectionRepresentative_measurable (cubicThetaInversionSection F)).aestronglyMeasurable).mp
  simpa only [Function.comp_def,cubicThetaSectionRepresentative_norm,
    cubicThetaInversionSection_norm] using hi

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeHeckeEnergyOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual cubed-prime Hecke correspondence on the completed global
energy space. The extension is determined by its literal action
on the dense finite-energy sections. -/
noncomputable section
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.cubicThetaCubeFinite_addGroup
def cubicThetaPrimeCubeHeckeRawEnergy {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaFiniteEnergySections →ₗ[ℂ] cubicThetaGlobalEnergySpace :=
  cubicThetaFiniteEnergyEmbedding.comp (cubicThetaPrimeCubeHeckeFiniteLinear hp)

def cubicThetaPrimeCubeHeckeEnergy {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace :=
  LinearMap.extendOfNorm (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (cubicThetaPrimeCubeHeckeRawEnergy hp) cubicThetaFiniteEnergyEmbedding

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionFiniteEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global inversion on actual finite-energy C1 sections. This bridges
the completed inversion to the literal functions occurring in the Hecke trace. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaInversionFinite (F : cubicThetaFiniteEnergySections) : cubicThetaFiniteEnergySections :=
  ⟨cubicThetaInversionSection F.val,cubicThetaInversionSection_c1 F.val F.property.1,
    cubicThetaInversionSection_memLp F.val F.property.2.1,
    cubicThetaPrimeCubeGradient_memLp_of_domain _ (cubicThetaInversionSection_c1 F.val F.property.1) (by
      have hi := cubicThetaScalarInversion_integrable (cubicThetaPrimeCubeFinite_energy_domain F)
        (cubicThetaC1Energy_invariant F.val F.property.1)
      change IntegrableOn (fun x => cubicThetaSectionEnergy (cubicThetaInversionSection F.val) x)
        cubicThetaFundamentalDomain cubicThetaPointMeasure
      simpa only [cubicThetaInversionSection_C1energy F.val F.property.1] using hi)⟩

def cubicThetaInversionFiniteLinear : cubicThetaFiniteEnergySections →ₗ[ℂ] cubicThetaFiniteEnergySections where
  toFun := cubicThetaInversionFinite
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma cubicThetaInversionFinite_value_norm (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaFiniteEnergyValue (cubicThetaInversionFinite F)‖^2=
      ‖cubicThetaFiniteEnergyValue F‖^2 := by
  rw [cubicThetaFiniteEnergyValue_domain_norm_sq,cubicThetaFiniteEnergyValue_domain_norm_sq]
  exact cubicThetaInversion_domain_integral F.val

lemma cubicThetaInversionFinite_gradient_norm (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaFiniteEnergyGradient (cubicThetaInversionFinite F)‖^2=
      ‖cubicThetaFiniteEnergyGradient F‖^2 := by
  rw [cubicThetaFiniteEnergyGradient_domain_norm_sq,cubicThetaFiniteEnergyGradient_domain_norm_sq]
  change (∫ x in cubicThetaFundamentalDomain,
    cubicThetaSectionEnergy (cubicThetaInversionSection F.val) x ∂cubicThetaPointMeasure)=_
  simp_rw [cubicThetaInversionSection_C1energy F.val F.property.1]
  exact cubicThetaScalarInversion_integral (cubicThetaC1Energy_invariant F.val F.property.1)

lemma cubicThetaInversionFinite_embedding_norm (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaFiniteEnergyEmbedding (cubicThetaInversionFinite F)‖=
      ‖cubicThetaFiniteEnergyEmbedding F‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  rw [cubicThetaGlobalEnergy_norm_sq,cubicThetaGlobalEnergy_norm_sq]
  exact congrArg₂ (·+·) (cubicThetaInversionFinite_value_norm F)
    (cubicThetaInversionFinite_gradient_norm F)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionFiniteCompletion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric inversion on finite-energy sections agrees with the
already constructed involution on the completed global energy space. -/
noncomputable section
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.inversionFinite_addGroup
def cubicThetaInversionRawEnergy : cubicThetaFiniteEnergySections →ₗ[ℂ] cubicThetaGlobalEnergySpace :=
  cubicThetaFiniteEnergyEmbedding.comp cubicThetaInversionFiniteLinear

def cubicThetaInversionFiniteExtension :
    cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace :=
  LinearMap.extendOfNorm (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    cubicThetaInversionRawEnergy cubicThetaFiniteEnergyEmbedding

lemma cubicThetaInversionRawEnergy_bound (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaInversionRawEnergy F‖≤1*‖cubicThetaFiniteEnergyEmbedding F‖ := by
  change ‖cubicThetaFiniteEnergyEmbedding (cubicThetaInversionFinite F)‖≤_
  rw [cubicThetaInversionFinite_embedding_norm,one_mul]

lemma cubicThetaInversionFiniteExtension_finite (F : cubicThetaFiniteEnergySections) :
    cubicThetaInversionFiniteExtension (cubicThetaFiniteEnergyEmbedding F)=
      cubicThetaInversionRawEnergy F :=
  LinearMap.extendOfNorm_eq (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (f:=cubicThetaInversionRawEnergy) (e:=cubicThetaFiniteEnergyEmbedding)
    cubicThetaFiniteEnergyEmbedding_dense ⟨1,cubicThetaInversionRawEnergy_bound⟩ F

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPointC1Trace
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The gradient trace identity before integration. Its finite sum uses
the same literal representatives and cubic phases as the Hecke trace. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPointC1Trace_apply {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPointC1) (x : CubicThetaPoint) :
    (cubicThetaPointC1Trace hp F).val x=
      ∑' t : cubicThetaPrimeCubeTransversal p,star (cubicThetaKubotaValue t.val)*F.val (t.val • x) := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  simp only [cubicThetaPointC1Trace,tsum_fintype]
  simp
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPointC1Hecke
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaPointC1_dilation_atkin {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPointC1) :
    cubicThetaPointC1Pullback (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)) F=
      cubicThetaPointC1Pullback (cubicThetaPrimeCubeAtkinMatrix hp)
        (cubicThetaPointC1Pullback (cubicThetaFullComplex cubicThetaFullInversion) F) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  exact congrArg F.val (cubicThetaPrimeCubeDilation_inversion_atkin hp x).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeFiniteAdjoint
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same literal inversion conjugate is the adjoint for the mass
and gradient forms on finite-energy sections. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeAdjointFinite {p : Eisenstein} (hp : primaryPrime p)
    (G : cubicThetaFiniteEnergySections) : cubicThetaFiniteEnergySections :=
  cubicThetaInversionFinite (cubicThetaPrimeCubeHeckeFinite hp (cubicThetaInversionFinite G))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeCompletedAdjoint
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both finite pairings extend to the completed global energy
space. The adjoint is the actual inversion-conjugated correspondence. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeHeckeAdjoint {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace :=
  cubicThetaInversionEnergy.toContinuousLinearMap.comp
    ((cubicThetaPrimeCubeHeckeEnergy hp).comp cubicThetaInversionEnergy.toContinuousLinearMap)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootLiftL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized isometric lifting from the original automorphic Hilbert
space to the actual root cover. -/
noncomputable section
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.cubeRootLift_smoothGroup
lemma cubicThetaPrimeCubeRootSmoothRestriction_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    ‖cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootSmoothRestriction hp F)‖^2=
      ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ)*‖cubicThetaGlobalMassClosure F‖^2 :=
  by
    change ‖cubicThetaPrimeCubeRootFiniteValue hp (cubicThetaPrimeCubeRootSmoothRestriction hp F)‖^2=_
    rw [cubicThetaPrimeCubeRootSectionL2_norm_sq]
    change (∫ x in cubicThetaPrimeCubeRootCoverDomain hp,‖F.val.val x‖^2 ∂cubicThetaPointMeasure)=_
    rw [cubicThetaPrimeCubeRootDomain_global_mass]
    change ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ)*
      (∫ q, (cubicThetaSectionNorm F.val q)^2 ∂cubicThetaQuotientMeasure)=
      ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ)*
        ‖cubicThetaGlobalInclusion (cubicThetaGlobalEnergyTest F)‖^2
    rw [cubicThetaGlobalInclusion_test_norm_sq]

lemma cubicThetaPrimeCubeRootNormalizedRestriction_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    ‖cubicThetaPrimeCubeRootNormalizedRestriction hp F‖=‖cubicThetaGlobalMassClosure F‖ := by
  let d : ℝ := (cubicThetaPrimeCubeRootCoverGroup hp).index
  have hd : 0<d := cubicThetaPrimeCubeRootCoverDegree_pos hp
  have hc : ‖((Real.sqrt d)⁻¹:ℂ)‖^2*d=1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,inv_pow,sq_abs,Real.sq_sqrt hd.le,
      inv_mul_cancel₀ hd.ne']
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  change ‖((Real.sqrt d)⁻¹:ℂ) •
    cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootSmoothRestriction hp F)‖^2=_
  rw [norm_smul,mul_pow,cubicThetaPrimeCubeRootSmoothRestriction_norm_sq]
  change ‖((Real.sqrt d)⁻¹:ℂ)‖^2*(d*‖cubicThetaGlobalMassClosure F‖^2)=_
  rw [←mul_assoc,hc,one_mul]

def cubicThetaPrimeCubeRootLiftL2 {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaAutomorphicL2 →ₗᵢ[ℂ] cubicThetaPrimeCubeRootAutomorphicL2 hp :=
  (cubicThetaPrimeCubeRootNormalizedRestriction hp).extendOfIsometry
    cubicThetaGlobalMassClosure_dense (cubicThetaPrimeCubeRootNormalizedRestriction_norm hp)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootDilationFixed
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The once-cubic dilation is fixed by the cubic root translations.
The zero Fourier projection preserves its pairings exactly. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeRootDilationL2_average_pairing {p : Eisenstein} (hp : primaryPrime p)
    (u v : cubicThetaAutomorphicL2) :
    inner ℂ (cubicThetaPrimeCubeRootFourierL2 hp 0 (cubicThetaPrimeCubeRootLiftL2 hp u))
      (cubicThetaPrimeCubeRootDilationL2 hp v)=
    inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp u) (cubicThetaPrimeCubeRootDilationL2 hp v) := by
  have he := cubicThetaPrimeCubeRootFourierL2_pair_projection hp 0
    (cubicThetaPrimeCubeRootLiftL2 hp u) (cubicThetaPrimeCubeRootDilationL2 hp v)
  rwa [cubicThetaPrimeCubeRootDilationL2_fourier_zero] at he

end CubicFirstMoment

end

end OAI
end


