-- Prove2me | Definitions.Def_OAIQ096A017
-- name    : OAIQ096A017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T03:46:25.417195+00:00
-- url     : https://prove2.me/theorems/e07cfe95-2aa6-4252-ba92-44271f8416ab
-- title:
--   Definitions bundle OAIQ096A017 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 171 declarations of OpenAI's Lean: 33 definitions, 2 instances and 136 theorems. The definitions and types are `OAI.CubicFirstMoment.cubicThetaArithmeticQuotientEnergy`, `OAI.CubicFirstMoment.cubicThetaArithmeticResidueL2`, `OAI.CubicFirstMoment.cubicThetaAutomorphicL2`, `OAI.CubicFirstMoment.cubicThetaC1Pairing`, `OAI.CubicFirstMoment.cubicThetaContinuedEnergyLift`, `OAI.CubicFirstMoment.cubicThetaCubeFinite_addGroup`, `OAI.CubicFirstMoment.cubicThetaEnergyResolventTransport`, `OAI.CubicFirstMoment.cubicThetaEnergyValueResolvent`, `OAI.CubicFirstMoment.cubicThetaGlobalMassClosure`, `OAI.CubicFirstMoment.cubicThetaIntegralQuotientHomeomorph`, `OAI.CubicFirstMoment.cubicThetaInversionSmooth`, `OAI.CubicFirstMoment.cubicThetaInversionSmoothLinear`, `OAI.CubicFirstMoment.cubicThetaPointC1Hecke`, `OAI.CubicFirstMoment.cubicThetaPointC1Trace`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeHeckeCoordinate`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeHeckeFinite`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeHeckeFiniteLinear`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeReciprocalNormalizer`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootDilationL2`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootFiniteEmbedding`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootFiniteTranslate`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootFiniteValue`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootFourierL2`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootNormalizedDilation`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootNormalizedRestriction`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootResidueL2`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootSmoothDilation`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootSmoothRestriction`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTranslateL2`, `OAI.CubicFirstMoment.cubicThetaSectionPointC1`, `OAI.CubicFirstMoment.cubicThetaSmoothToFiniteEnergy`, `OAI.CubicFirstMoment.inversionFinite_addGroup`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `CubicMoment_Theta_CubicThetaArithmeticCuspMass`, `CubicMoment_Theta_CubicThetaArithmeticEnergy`, `CubicMoment_Theta_CubicThetaArithmeticSection`, `CubicMoment_Theta_CubicThetaC1Pairing`, `CubicMoment_Theta_CubicThetaC1PairingIntegral`, `CubicMoment_Theta_CubicThetaCompactCuspSupport`, `CubicMoment_Theta_CubicThetaContinuedWeakEquation`, `CubicMoment_Theta_CubicThetaCoordinateChartIntegral`, `CubicMoment_Theta_CubicThetaCoordinatePairing`, `CubicMoment_Theta_CubicThetaCoordinateSectionPairing`, `CubicMoment_Theta_CubicThetaCuspCoordinateEnergy`, `CubicMoment_Theta_CubicThetaCuspScalarIntegrals`, `CubicMoment_Theta_CubicThetaCuspStripMeasure`, `CubicMoment_Theta_CubicThetaEnergyRegularizer`, `CubicMoment_Theta_CubicThetaEnergyResolventTransport`, `CubicMoment_Theta_CubicThetaExceptionalProjection`, `CubicMoment_Theta_CubicThetaFiniteEnergyPairing`, `CubicMoment_Theta_CubicThetaFiniteEnergySections`, `CubicMoment_Theta_CubicThetaForcedResidue`, `CubicMoment_Theta_CubicThetaGlobalAutomorphicRange`, `CubicMoment_Theta_CubicThetaGlobalL2`, `CubicMoment_Theta_CubicThetaIntegralQuotient`, `CubicMoment_Theta_CubicThetaInversionEnergy`, `CubicMoment_Theta_CubicThetaInversionEnergyInvolution`, `CubicMoment_Theta_CubicThetaInversionFiniteCompletion`, `CubicMoment_Theta_CubicThetaInversionFiniteEnergy`, `CubicMoment_Theta_CubicThetaInversionL2Bounds`, `CubicMoment_Theta_CubicThetaInversionSmooth`, `CubicMoment_Theta_CubicThetaPointC1Hecke`, `CubicMoment_Theta_CubicThetaPointC1Pairing`, `CubicMoment_Theta_CubicThetaPointC1Section`, `CubicMoment_Theta_CubicThetaPointC1Trace`, `CubicMoment_Theta_CubicThetaPrimeArithmeticResidue`, `CubicMoment_Theta_CubicThetaPrimeCoverDegree`, `CubicMoment_Theta_CubicThetaPrimeCubeAtkinIntegral`, `CubicMoment_Theta_CubicThetaPrimeCubeAtkinPairing`, `CubicMoment_Theta_CubicThetaPrimeCubeCoverDomain`, `CubicMoment_Theta_CubicThetaPrimeCubeDilationNorm`, `CubicMoment_Theta_CubicThetaPrimeCubeEnergyIntegral`, `CubicMoment_Theta_CubicThetaPrimeCubeFiniteEnergy`, `CubicMoment_Theta_CubicThetaPrimeCubeHeckeEnergy`, `CubicMoment_Theta_CubicThetaPrimeCubeHeckeEnergyOperator`, `CubicMoment_Theta_CubicThetaPrimeCubeHeckeLinear`, `CubicMoment_Theta_CubicThetaPrimeCubeHeckeRegularity`, `CubicMoment_Theta_CubicThetaPrimeCubeInvariantDilation`, `CubicMoment_Theta_CubicThetaPrimeCubeReciprocalNormalizer`, `CubicMoment_Theta_CubicThetaPrimeCubeRootAutomorphicL2`, `CubicMoment_Theta_CubicThetaPrimeCubeRootCoverDomain`, `CubicMoment_Theta_CubicThetaPrimeCubeRootDilation`, `CubicMoment_Theta_CubicThetaPrimeCubeRootDilationFixed`, `CubicMoment_Theta_CubicThetaPrimeCubeRootDilationL2`, `CubicMoment_Theta_CubicThetaPrimeCubeRootDomainMass`, `CubicMoment_Theta_CubicThetaPrimeCubeRootFourier`, `CubicMoment_Theta_CubicThetaPrimeCubeRootFourierNorm`, `CubicMoment_Theta_CubicThetaPrimeCubeRootFourierProducts`, `CubicMoment_Theta_CubicThetaPrimeCubeRootHeckeCover`, `CubicMoment_Theta_CubicThetaPrimeCubeRootHeckeIntegral`, `CubicMoment_Theta_CubicThetaPrimeCubeRootL2`, `CubicMoment_Theta_CubicThetaPrimeCubeRootL2Algebra`, `CubicMoment_Theta_CubicThetaPrimeCubeRootLiftL2`, `CubicMoment_Theta_CubicThetaPrimeCubeRootMassTransport`, `CubicMoment_Theta_CubicThetaPrimeCubeSectionAtkin`, `CubicMoment_Theta_CubicThetaPrimeCubeSheetIntegral`, `CubicMoment_Theta_CubicThetaPrimeCubeTraceNorm`, `CubicMoment_Theta_CubicThetaPrimeEnergyDomainNorm`, `CubicMoment_Theta_CubicThetaPrimeLiftL2`, `CubicMoment_Theta_CubicThetaPrimeWeakLift`, `CubicMoment_Theta_CubicThetaSectionPairing`.
--
--   **Imports.** It imports the published bundle `Def_PattersonFirstMoment`; the bundles `OAIQ096A011`, `OAIQ096A012` and `OAIQ096A013` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ096A021`, `OAIQ096A022` and `OAIQ096A023`; the proofs of `OAI_CubicFirstMoment_angular_balanced_truncated_neighborhood_moment`, `OAI_CubicFirstMoment_angular_balanced_twisted_vonMangoldt_neighborhood`, `OAI_CubicFirstMoment_angular_first_weighted_tuple_neighborhood`, `OAI_CubicFirstMoment_angular_typeI_selected_height_ranges_proved`, `OAI_CubicFirstMoment_balanced_truncated_neighborhood_moment` and `OAI_CubicFirstMoment_balanced_twisted_vonMangoldt_neighborhood`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A011
import Definitions.Def_OAIQ096A012
import Definitions.Def_OAIQ096A013

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticSection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The arithmetic Eisenstein-minus-incoming difference is a genuine
continuous automorphic section in the initial convergence half-plane. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaArithmeticSection_norm (s : ℂ) (hs : 2 < s.re) (p : CubicThetaPoint) :
    cubicThetaSectionNorm (cubicThetaArithmeticSection s hs) (cubicThetaQuotientMap p)=
      ‖cubicThetaArithmeticRemainder p.val s‖ :=
  cubicThetaSectionNorm_apply _ p

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactCuspSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaGlobalEnergySpace_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact smooth automorphic section vanishes uniformly high in
every arithmetic cusp. This is derived from its actual quotient support,
not imposed as a separate cusp-decay hypothesis. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaSmoothTests_cusp_support (F : cubicThetaSmoothTests) :
    ∃ C≥0, ∀ δ : SL(2,Eisenstein), ∀ p : CubicThetaPoint,
      C < cubicThetaPointHeight p → F.val.val (δ • p)=0 := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaCompact_all_cusp_height_bound F.property.2
  refine ⟨C,hC,fun δ p hp => ?_⟩
  by_contra hn
  have hs : cubicThetaQuotientMap (δ • p)∈tsupport (cubicThetaSectionNorm F) := by
    apply subset_tsupport
    change cubicThetaSectionNorm F (cubicThetaQuotientMap (δ • p))≠0
    rw [cubicThetaSectionNorm_apply]
    exact norm_ne_zero_iff.mpr hn
  have h := hbound (δ • p) hs δ⁻¹
  rw [inv_smul_smul] at h
  exact (not_lt_of_ge h) hp

lemma cubicThetaSmoothTests_cusp_function_support (F : cubicThetaSmoothTests) :
    ∃ C≥0, ∀ δ : SL(2,Eisenstein), ∀ z : ℂ, ∀ v : ℝ, 0<v → C<v →
      cubicThetaSectionFunction F (cubicThetaMobius (cubicThetaFullComplex δ) (z,v))=0 := by
  obtain ⟨C,hC,h⟩ := cubicThetaSmoothTests_cusp_support F
  refine ⟨C,hC,fun δ z v hv hCv => ?_⟩
  rw [cubicThetaSectionFunction_apply F (cubicThetaMobius_height_pos _ hv)]
  exact h δ ⟨(z,v),hv⟩ hCv

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGlobalL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaGlobalEnergySpace_complete _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual automorphic sections as global L2 vectors. A Borel section
chooses representatives, while the norm is the continuous intrinsic norm
on the quotient, so compact smooth sections are square integrable. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

def cubicThetaAutomorphicL2 : Submodule ℂ CubicThetaGlobalL2 :=
  cubicThetaGlobalMass.range.topologicalClosure

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspStripMeasure
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaInjective_integral {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) (hi : InjOn cubicThetaQuotientMap S)
    (f : CubicThetaQuotient → ℝ) (hf : StronglyMeasurable f) :
    (∫ q in cubicThetaQuotientMap '' S, f q ∂cubicThetaQuotientMeasure)=
      ∫ p in S, f (cubicThetaQuotientMap p) ∂cubicThetaPointMeasure := by
  rw [← cubicThetaInjective_map_restrict hS hi]
  exact integral_map_of_stronglyMeasurable cubicThetaQuotientMap_open.continuous.measurable hf

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspCoordinateEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The true scalar mass and energy in each cusp, in the Euclidean
coordinates used for the radial integration. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaSectionEnergy_nonneg (F : cubicThetaSmoothTests) (p : CubicThetaPoint) :
    0 ≤ cubicThetaSectionEnergy F p :=
  mul_nonneg (sq_nonneg _) (cubicThetaTangentEnergy_nonneg _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticCuspMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaArithmeticRemainder_cusp_mass_continuousOn
    (δ : SL(2,Eisenstein)) {s : ℂ} (hs : 2 < s.re) :
    ContinuousOn (fun y : ℂ × ℝ =>
      ‖cubicThetaArithmeticRemainder (cubicThetaMobius (cubicThetaFullComplex δ) y) s‖^2/y.2^3)
      (cubicThetaHorizontalCell ×ˢ Ioi (2:ℝ)) := by
  intro y hy
  have hv : 0<y.2 := lt_trans (by norm_num : (0:ℝ)<2) hy.2
  have hR := (cubicThetaArithmeticRemainder_continuousAt hs
    (cubicThetaMobius_height_pos (cubicThetaFullComplex δ) hv)).comp
    (cubicThetaMobius_contDiffAt (cubicThetaFullComplex δ) hv).continuousAt
  exact ((hR.norm.pow 2).div (continuousAt_snd.pow 3) (pow_ne_zero 3 hv.ne')).continuousWithinAt

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaGlobalEnergySpace_complete _root_.instMeasurableSpace
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

def cubicThetaArithmeticQuotientEnergy (s : ℂ) (hs : 2 < s.re) (q : CubicThetaQuotient) : ℝ :=
  cubicThetaSectionEnergy (cubicThetaArithmeticSection s hs) (cubicThetaQuotientLift q)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaC1Pairing
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sesquilinear differential pairing descends to the arithmetic
quotient; its value is independent of the measurable frame choice. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaC1Gradient_norm_invariant (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    ‖cubicThetaSectionGradient F (g • p)‖=‖cubicThetaSectionGradient F p‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  rw [cubicThetaSectionGradient_norm_sq,cubicThetaSectionGradient_norm_sq]
  exact cubicThetaC1Energy_invariant F hF g p

lemma cubicThetaC1Gradient_inner_invariant (F G : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2})
    (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    inner ℂ (cubicThetaSectionGradient F (g • p)) (cubicThetaSectionGradient G (g • p))=
      inner ℂ (cubicThetaSectionGradient F p) (cubicThetaSectionGradient G p) := by
  have hsum := cubicThetaC1Gradient_norm_invariant (F+G) (hF.add hG) g p
  have hsub := cubicThetaC1Gradient_norm_invariant (F-G) (hF.sub hG) g p
  have hsumI := cubicThetaC1Gradient_norm_invariant (F+Complex.I • G) (hF.add (hG.const_smul Complex.I)) g p
  have hsubI := cubicThetaC1Gradient_norm_invariant (F-Complex.I • G) (hF.sub (hG.const_smul Complex.I)) g p
  simp only [cubicThetaC1Gradient_add _ _ hF hG] at hsum
  simp only [cubicThetaC1Gradient_sub _ _ hF hG] at hsub
  simp only [cubicThetaC1Gradient_add F (Complex.I • G) hF (hG.const_smul Complex.I),
    cubicThetaC1Gradient_smul Complex.I G hG] at hsumI
  simp only [cubicThetaC1Gradient_sub F (Complex.I • G) hF (hG.const_smul Complex.I),
    cubicThetaC1Gradient_smul Complex.I G hG] at hsubI
  rw [inner_eq_sum_norm_sq_div_four,inner_eq_sum_norm_sq_div_four]
  change ((‖cubicThetaSectionGradient F (g • p)+cubicThetaSectionGradient G (g • p)‖:ℂ)^2-
    (‖cubicThetaSectionGradient F (g • p)-cubicThetaSectionGradient G (g • p)‖:ℂ)^2+
    ((‖cubicThetaSectionGradient F (g • p)-Complex.I • cubicThetaSectionGradient G (g • p)‖:ℂ)^2-
    (‖cubicThetaSectionGradient F (g • p)+Complex.I • cubicThetaSectionGradient G (g • p)‖:ℂ)^2)*Complex.I)/4=_
  rw [hsum,hsub,hsubI,hsumI]
  rfl

def cubicThetaC1Pairing (F G : CubicThetaSection) (q : CubicThetaQuotient) : ℂ :=
  inner ℂ (cubicThetaSectionGradient F (cubicThetaQuotientLift q))
    (cubicThetaSectionGradient G (cubicThetaQuotientLift q))

lemma cubicThetaC1Pairing_apply (F G : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2})
    (p : CubicThetaPoint) :
    cubicThetaC1Pairing F G (cubicThetaQuotientMap p)=
      inner ℂ (cubicThetaSectionGradient F p) (cubicThetaSectionGradient G p) := by
  have he := cubicThetaQuotientLift_map (cubicThetaQuotientMap p)
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  unfold cubicThetaC1Pairing
  rw [← hg,cubicThetaC1Gradient_inner_invariant F G hF hG]

lemma cubicThetaC1Pairing_continuous (F G : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2}) :
    Continuous (cubicThetaC1Pairing F G) := by
  apply cubicThetaQuotientMap_open.isQuotientMap.continuous_iff.mpr
  have he : cubicThetaC1Pairing F G ∘ cubicThetaQuotientMap=
      fun p => inner ℂ (cubicThetaSectionGradient F p) (cubicThetaSectionGradient G p) :=
    funext (cubicThetaC1Pairing_apply F G hF hG)
  rw [he]
  exact (cubicThetaC1Gradient_continuous F hF).inner (cubicThetaC1Gradient_continuous G hG)

lemma cubicThetaC1Pairing_representative (F G : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2})
    (q : CubicThetaQuotient) :
    cubicThetaC1Pairing F G q=inner ℂ (cubicThetaGradientRepresentative F q)
      (cubicThetaGradientRepresentative G q) := by
  have h := cubicThetaC1Pairing_apply F G hF hG (cubicThetaBorelSection q)
  rwa [cubicThetaBorelSection_rightInverse] at h

lemma cubicThetaChart_complex_integral
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    {S : Set CubicThetaPoint} (hS : MeasurableSet S) (hSe : S⊆e.source)
    (f : CubicThetaQuotient → ℂ) (hf : StronglyMeasurable f) :
    (∫ q in cubicThetaQuotientMap '' S, f q ∂cubicThetaQuotientMeasure)=
      ∫ p in S, f (cubicThetaQuotientMap p) ∂cubicThetaPointMeasure := by
  rw [← cubicThetaChart_map_restrict e he hS hSe]
  exact integral_map_of_stronglyMeasurable cubicThetaQuotientMap_open.continuous.measurable hf

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaC1PairingIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quotient integration of the actual differential pairing agrees
with the Hilbert L2 inner product. Compact tests give compact support. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaC1Pairing_L2 (F G : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2})
    (hmF : MemLp (cubicThetaGradientRepresentative F) 2 cubicThetaQuotientMeasure)
    (hmG : MemLp (cubicThetaGradientRepresentative G) 2 cubicThetaQuotientMeasure) :
    inner ℂ (hmF.toLp _) (hmG.toLp _)=∫ q, cubicThetaC1Pairing F G q ∂cubicThetaQuotientMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hmF.coeFn_toLp,hmG.coeFn_toLp] with q hqF hqG
  rw [hqF,hqG,cubicThetaC1Pairing_representative F G hF hG]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspScalarIntegrals
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaMass_integrable (F : cubicThetaSmoothTests) :
    Integrable (fun q => cubicThetaSectionNorm F q^2) cubicThetaQuotientMeasure := by
  have h := (cubicThetaSectionRepresentative_memLp F).integrable_norm_pow (by norm_num)
  simpa only [cubicThetaSectionRepresentative_norm] using h

lemma cubicThetaGradientEnergy_integrable (F : cubicThetaSmoothTests) :
    Integrable (cubicThetaQuotientEnergy F) cubicThetaQuotientMeasure :=
  (cubicThetaQuotientEnergy_continuous F).integrable_of_hasCompactSupport
    (cubicThetaQuotientEnergy_compact F)

lemma cubicThetaCuspPullback_energy (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) {v : ℝ} (hv : 0<v) :
    cubicThetaCuspPullback δ (cubicThetaQuotientEnergy F) (z,v)=
      cubicThetaSectionEnergy F (δ • cubicThetaVerticalPoint z v hv) := by
  have h := cubicThetaCuspPullback_apply δ (cubicThetaQuotientEnergy F)
    (cubicThetaVerticalPoint z v hv)
  change cubicThetaCuspPullback δ (cubicThetaQuotientEnergy F) (z,v)=_ at h
  rw [h,cubicThetaQuotientEnergy_apply]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEnergyRegularizer
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
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

lemma cubicThetaEnergy_real_smul_inner (u v : cubicThetaGlobalEnergySpace) (r : ℝ) :
    (inner ℂ ((r:ℂ) • u) v).re=r*(inner ℂ u v).re := by
  have h : inner ℂ ((r:ℂ) • u) v=star (r:ℂ)*inner ℂ u v :=
    inner_smul_left (𝕜:=ℂ) (E:=cubicThetaGlobalEnergySpace) u v (r:ℂ)
  rw [RCLike.star_def,Complex.conj_ofReal] at h
  have hh := congrArg Complex.re h
  simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaExceptionalProjection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
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

lemma cubicThetaEnergyPencil_selfAdjoint (z : ℝ) :
    IsSelfAdjoint (cubicThetaEnergyPencil (z:ℂ)) := by
  have hA : IsSelfAdjoint cubicThetaEnergyMass :=
    (ContinuousLinearMap.isPositive_adjoint_comp_self cubicThetaGlobalInclusion).isSelfAdjoint
  have hz : IsSelfAdjoint (z:ℂ) := by
    change star (z:ℂ)=(z:ℂ)
    rw [RCLike.star_def,Complex.conj_ofReal]
  have h1 : IsSelfAdjoint (1 : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) := by
    change ContinuousLinearMap.adjoint (1 : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace)=1
    exact ContinuousLinearMap.adjoint_one
  have hs : IsSelfAdjoint ((z:ℂ) • cubicThetaEnergyMass) :=
    IsSelfAdjoint.smul (R:=ℂ) (A:=cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) hz hA
  exact IsSelfAdjoint.sub (R:=cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) h1 hs

lemma cubicThetaProjectedPencil_injective (z : ℝ) :
    Function.Injective (cubicThetaEnergyPencil (z:ℂ)+cubicThetaExceptionalProjection (z:ℂ)) := by
  let T := cubicThetaEnergyPencil (z:ℂ)
  let P := cubicThetaExceptionalProjection (z:ℂ)
  have hT : T.toLinearMap.IsSymmetric := (cubicThetaEnergyPencil_selfAdjoint z).isSymmetric
  have hzero (u : cubicThetaGlobalEnergySpace) (hu : (T+P) u=0) : u=0 := by
    have hp : T (P u)=0 := (T.ker.starProjection_apply_mem u)
    have ho : inner ℂ (T u) (P u)=0 := by
      have hs := hT u (P u)
      change inner ℂ (T u) (P u)=inner ℂ u (T (P u)) at hs
      rw [hp,inner_zero_right] at hs
      exact hs
    have hu' : T u+P u=0 := by simpa only [add_apply] using hu
    have he := congrArg (fun v => inner ℂ v (P u)) hu'
    rw [inner_zero_left] at he
    rw [inner_add_left,ho,zero_add] at he
    have hpu : P u=0 := inner_self_eq_zero.mp he
    have htu : T u=0 := by
      rwa [hpu,add_zero] at hu'
    have hself : P u=u := T.ker.starProjection_eq_self_iff.mpr htu
    exact hself.symm.trans hpu
  intro u v huv
  have hsub : (T+P) (u-v)=0 := by rw [map_sub,huv,sub_self]
  exact sub_eq_zero.mp (hzero _ hsub)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEnergyResolventTransport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
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

def cubicThetaEnergyResolventTransport :
    (cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) →L[ℂ]
      (CubicThetaGlobalL2 →L[ℂ] CubicThetaGlobalL2) where
  toFun A := cubicThetaGlobalInclusion.comp (A.comp cubicThetaGlobalInclusion.adjoint)
  map_add' A B := by
    apply ContinuousLinearMap.ext
    intro F
    change cubicThetaGlobalInclusion (A (cubicThetaGlobalInclusion.adjoint F)+
      B (cubicThetaGlobalInclusion.adjoint F))=_
    exact cubicThetaGlobalInclusion.map_add _ _
  map_smul' c A := by
    apply ContinuousLinearMap.ext
    intro F
    change cubicThetaGlobalInclusion (c • A (cubicThetaGlobalInclusion.adjoint F))=
      c • cubicThetaGlobalInclusion (A (cubicThetaGlobalInclusion.adjoint F))
    exact cubicThetaGlobalInclusion.map_smul c _
  cont := (continuous_id.clm_comp_const cubicThetaGlobalInclusion.adjoint).const_clm_comp
    cubicThetaGlobalInclusion

def cubicThetaEnergyValueResolvent (z : ℂ) : CubicThetaGlobalL2 →L[ℂ] CubicThetaGlobalL2 :=
  cubicThetaEnergyResolventTransport (Ring.inverse (cubicThetaEnergyPencil z))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaContinuedWeakEquation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
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

def cubicThetaContinuedEnergyLift (z : ℂ) (F : CubicThetaGlobalL2) :
    cubicThetaGlobalEnergySpace :=
  Ring.inverse (cubicThetaEnergyPencil z) (cubicThetaGlobalInclusion.adjoint F)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateChartIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact complex integration of a quotient function supported in one
injective coordinate sheet. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaCoordinateChart_integral
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    {K : Set (ℂ × ℝ)} (hK : IsCompact K) (hp : K⊆{y : ℂ × ℝ | 0<y.2})
    (hKe : cubicThetaPointInclusion.symm '' K⊆e.source)
    (F : CubicThetaQuotient → ℂ) (hF : StronglyMeasurable F)
    (hs : Function.support F⊆cubicThetaQuotientMap '' (cubicThetaPointInclusion.symm '' K))
    (f : ℂ × ℝ → ℂ)
    (hf : ∀ p∈cubicThetaPointInclusion.symm '' K, F (cubicThetaQuotientMap p)=f p.val) :
    (∫ q, F q ∂cubicThetaQuotientMeasure)=∫ y in K, f y/(y.2:ℂ)^3 := by
  let S := cubicThetaPointInclusion.symm '' K
  have hi : ContinuousOn cubicThetaPointInclusion.symm {y : ℂ × ℝ | 0<y.2} := by
    simpa only [OpenPartialHomeomorph.symm_source,cubicThetaPointInclusion_target] using
      cubicThetaPointInclusion.symm.continuousOn
  have hS : IsCompact S := hK.image_of_continuousOn (hi.mono hp)
  have hcoords : cubicThetaPointCoordinates '' S=K := by
    ext y
    constructor
    · rintro ⟨p,⟨z,hz,rfl⟩,rfl⟩
      have heq := cubicThetaPointInclusion.right_inv
        (show z∈cubicThetaPointInclusion.target by rw [cubicThetaPointInclusion_target]; exact hp hz)
      change cubicThetaPointCoordinates (cubicThetaPointInclusion.symm z)∈K
      change cubicThetaPointCoordinates (cubicThetaPointInclusion.symm z)=z at heq
      rw [heq]
      exact hz
    · intro hy
      exact ⟨cubicThetaPointInclusion.symm y,⟨y,hy,rfl⟩,
        cubicThetaPointInclusion.right_inv (by rw [cubicThetaPointInclusion_target]; exact hp hy)⟩
  have hz : ∀ q, q∉cubicThetaQuotientMap '' S → F q=0 := by
    intro q hq
    by_contra hn
    exact hq (hs hn)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    cubicThetaChart_complex_integral e he hS.measurableSet hKe F hF]
  rw [setIntegral_congr_fun hS.measurableSet hf]
  change (∫ p in S, f (cubicThetaPointCoordinates p) ∂cubicThetaPointMeasure)=_
  simpa only [hcoords] using cubicThetaPointIntegral_complex_density hS.measurableSet f

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinatePairing
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The intrinsic tangent inner product is the literal three-coordinate
sesquilinear sum. This fixes the local normalization of the weak form. -/
noncomputable section
open scoped Matrix
namespace CubicFirstMoment

lemma cubicThetaSectionGradient_pair_coordinates (F G : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2})
    (p : CubicThetaPoint) :
    inner ℂ (cubicThetaSectionGradient F p) (cubicThetaSectionGradient G p)=
      (p.val.2:ℂ)^2*cubicThetaCoordinatePairing (cubicThetaSectionFunction F)
        (cubicThetaSectionFunction G) p.val := by
  have hp : {y : ℂ × ℝ | 0<y.2}∈nhds p.val :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds p.property
  have hf := (hF.contDiffAt hp).differentiableAt (by norm_num)
  have hg := (hG.contDiffAt hp).differentiableAt (by norm_num)
  have heF : cubicThetaSectionGradient F p=(p.val.2:ℂ) •
      cubicThetaTangentValues (fderiv ℝ (cubicThetaSectionFunction F) p.val) := by
    ext i
    simp only [cubicThetaSectionGradient,cubicThetaSectionDifferential,cubicThetaTangentValues,
      ContinuousLinearMap.comp_apply]
    rfl
  have heG : cubicThetaSectionGradient G p=(p.val.2:ℂ) •
      cubicThetaTangentValues (fderiv ℝ (cubicThetaSectionFunction G) p.val) := by
    ext i
    simp only [cubicThetaSectionGradient,cubicThetaSectionDifferential,cubicThetaTangentValues,
      ContinuousLinearMap.comp_apply]
    rfl
  rw [heF,heG,inner_smul_left,inner_smul_right,cubicThetaTangentValues_inner]
  unfold cubicThetaCoordinatePairing
  simp only [cubicThetaAxisFirst_eq_fderiv _ _ hf,cubicThetaAxisFirst_eq_fderiv _ _ hg,
    cubicThetaAxisVector]
  have hs : (starRingEnd ℂ) (p.val.2:ℂ)=(p.val.2:ℂ) := by simp
  rw [hs]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSectionPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar Hermitian pairing of two actual automorphic sections
descends to the quotient and agrees with the L2 inner product. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaSectionPairing_continuous (F G : CubicThetaSection) :
    Continuous (cubicThetaSectionPairing F G) := by
  apply cubicThetaQuotientMap_open.isQuotientMap.continuous_iff.mpr
  have he : cubicThetaSectionPairing F G ∘ cubicThetaQuotientMap=
      fun p => inner ℂ (F.val p) (G.val p) := funext (cubicThetaSectionPairing_apply F G)
  rw [he]
  exact F.val.continuous.inner G.val.continuous

lemma cubicThetaSectionPairing_L2 (F G : CubicThetaSection)
    (hmF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure)
    (hmG : MemLp (cubicThetaSectionRepresentative G) 2 cubicThetaQuotientMeasure) :
    inner ℂ (hmF.toLp _) (hmG.toLp _)=∫ q, cubicThetaSectionPairing F G q ∂cubicThetaQuotientMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hmF.coeFn_toLp,hmG.coeFn_toLp] with q hqF hqG
  rw [hqF,hqG]
  have h := cubicThetaSectionPairing_apply F G (cubicThetaBorelSection q)
  rw [cubicThetaBorelSection_rightInverse] at h
  exact h.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateSectionPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pairing a section with one compact periodized chart function is
exactly its coordinate mass and gradient pairing. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaC1Pairing_support (F G : CubicThetaSection) :
    tsupport (cubicThetaC1Pairing F G)⊆tsupport (cubicThetaSectionNorm F) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro q hq
  by_contra hout
  have hp : cubicThetaQuotientMap (cubicThetaQuotientLift q)∉tsupport (cubicThetaSectionNorm F) := by
    rwa [cubicThetaQuotientLift_map]
  have hd := cubicThetaSectionDifferential_eq_zero F (cubicThetaQuotientLift q) hp
  have hg : cubicThetaSectionGradient F (cubicThetaQuotientLift q)=0 := by
    ext i
    simp [cubicThetaSectionGradient,hd]
  exact hq (by simp only [cubicThetaC1Pairing,hg,inner_zero_left])

lemma cubicThetaCoordinateSection_mass_pairing {g : ℂ × ℝ → ℂ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {K : Set (ℂ × ℝ)} (hK : IsCompact K) (hp : K⊆{y : ℂ × ℝ | 0<y.2})
    (hgs : tsupport g⊆K)
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hKe : cubicThetaPointInclusion.symm '' K⊆e.source) (G : CubicThetaSection) :
    let P := cubicThetaPoincareSection (cubicThetaCoordinateSeed g hg.continuous hc (hgs.trans hp))
    (∫ q, cubicThetaSectionPairing P G q ∂cubicThetaQuotientMeasure)=
      ∫ y in K, star (g y)*cubicThetaSectionFunction G y/(y.2:ℂ)^3 := by
  intro P
  have hs : tsupport (cubicThetaCoordinateSeed g hg.continuous hc (hgs.trans hp))⊆
      cubicThetaPointInclusion.symm '' K :=
    (cubicThetaCoordinateSeed_support _ _ _ _).trans (image_mono hgs)
  apply cubicThetaCoordinateChart_integral e he hK hp hKe _
    (cubicThetaSectionPairing_continuous P G).stronglyMeasurable
  · exact (subset_tsupport _).trans ((cubicThetaSectionPairing_support P G).trans
      ((cubicThetaPoincareSection_norm_support _).trans (image_mono hs)))
  · intro p hps
    rw [cubicThetaSectionPairing_apply]
    have hv := cubicThetaPoincareSection_on_sheet
      (cubicThetaCoordinateSeed g hg.continuous hc (hgs.trans hp)) e he
      ((subset_tsupport _).trans (hs.trans hKe)) (hKe hps)
    change P.val p=g p.val at hv
    rw [hv]
    rw [cubicThetaSectionFunction_apply G p.property]
    simp only [RCLike.inner_apply,starRingEnd_apply]
    change G.val p*star (g p.val)=star (g p.val)*G.val p
    ring

lemma cubicThetaCoordinateSection_gradient_pairing {g : ℂ × ℝ → ℂ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {K : Set (ℂ × ℝ)} (hK : IsCompact K) (hp : K⊆{y : ℂ × ℝ | 0<y.2})
    (hgs : tsupport g⊆K)
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hKe : cubicThetaPointInclusion.symm '' K⊆e.source) (G : CubicThetaSection)
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2}) :
    let P := cubicThetaPoincareSection (cubicThetaCoordinateSeed g hg.continuous hc (hgs.trans hp))
    (∫ q, cubicThetaC1Pairing P G q ∂cubicThetaQuotientMeasure)=
      ∫ y in K, cubicThetaHeightInverse y*cubicThetaCoordinatePairing g (cubicThetaSectionFunction G) y := by
  intro P
  have hP := cubicThetaCoordinateSection_regular hg hc (hgs.trans hp)
  have hs : tsupport (cubicThetaCoordinateSeed g hg.continuous hc (hgs.trans hp))⊆
      cubicThetaPointInclusion.symm '' K :=
    (cubicThetaCoordinateSeed_support _ _ _ _).trans (image_mono hgs)
  have ht := (subset_tsupport _).trans (hs.trans hKe)
  have hchart : (∫ q, cubicThetaC1Pairing P G q ∂cubicThetaQuotientMeasure)=
      ∫ y in K, ((y.2:ℂ)^2*cubicThetaCoordinatePairing g (cubicThetaSectionFunction G) y)/(y.2:ℂ)^3 := by
    apply cubicThetaCoordinateChart_integral e he hK hp hKe _
      (cubicThetaC1Pairing_continuous P G hP hG).stronglyMeasurable
    · exact (subset_tsupport _).trans ((cubicThetaC1Pairing_support P G).trans
        ((cubicThetaPoincareSection_norm_support _).trans (image_mono hs)))
    · intro p hps
      rw [cubicThetaC1Pairing_apply P G hP hG,cubicThetaSectionGradient_pair_coordinates P G hP hG]
      have hleft : cubicThetaPointInclusion.symm p.val=p :=
        cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)
      have hd := cubicThetaCoordinateSection_fderiv_on_sheet g hg.continuous hc (hgs.trans hp)
        e he ht p.property (by rw [hleft]; exact hKe hps)
      rw [cubicThetaCoordinatePairing_fderiv_congr
        ((hP.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds p.property)).differentiableAt (by norm_num))
        (hg.differentiable one_ne_zero p.val) hd]
  rw [hchart]
  apply setIntegral_congr_fun hK.measurableSet
  intro y hy
  have hv : (y.2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hp hy).ne'
  simp only [cubicThetaHeightInverse,Complex.ofReal_inv]
  field_simp [hv]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteEnergySections
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaSmoothTests_finiteEnergy : cubicThetaSmoothTests ≤ cubicThetaFiniteEnergySections := by
  intro F hF
  let G : cubicThetaSmoothTests := ⟨F,hF⟩
  exact ⟨hF.1.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),cubicThetaSectionRepresentative_memLp G,cubicThetaGradientRepresentative_memLp G⟩

def cubicThetaSmoothToFiniteEnergy : cubicThetaSmoothTests →ₗ[ℂ] cubicThetaFiniteEnergySections :=
  Submodule.inclusion cubicThetaSmoothTests_finiteEnergy

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaIntegralQuotient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaIntegralQuotientMap_continuous (δ : SL(2,Eisenstein)) :
    Continuous (cubicThetaIntegralQuotientMap δ) := by
  apply cubicThetaQuotientMap_open.isQuotientMap.continuous_iff.mpr
  exact cubicThetaQuotientMap_open.continuous.comp (continuous_const_smul δ)

def cubicThetaIntegralQuotientHomeomorph (δ : SL(2,Eisenstein)) :
    CubicThetaQuotient ≃ₜ CubicThetaQuotient where
  toFun := cubicThetaIntegralQuotientMap δ
  invFun := cubicThetaIntegralQuotientMap δ⁻¹
  left_inv q := by rw [cubicThetaIntegralQuotientMap_comp,inv_mul_cancel,cubicThetaIntegralQuotientMap_one]
  right_inv q := by rw [cubicThetaIntegralQuotientMap_comp,mul_inv_cancel,cubicThetaIntegralQuotientMap_one]
  continuous_toFun := cubicThetaIntegralQuotientMap_continuous δ
  continuous_invFun := cubicThetaIntegralQuotientMap_continuous δ⁻¹

lemma cubicThetaIntegralImage_fundamental (δ : SL(2,Eisenstein)) :
    IsFundamentalDomain cubicThetaPrincipalGroup
      ((fun p : CubicThetaPoint => δ • p) '' cubicThetaFundamentalDomain) cubicThetaPointMeasure := by
  apply (cubicThetaFundamentalDomain_isFundamentalDomain cubicThetaPointMeasure).image_of_equiv
    (Homeomorph.smul δ).toEquiv
    (measurePreserving_smul δ⁻¹ cubicThetaPointMeasure).quasiMeasurePreserving
    (cubicThetaPrincipalConjugateEquiv δ)
  intro g p
  change δ • ((δ⁻¹*g.val*δ) • p)=g.val • (δ • p)
  simp only [←mul_smul,mul_assoc,mul_inv_cancel_left]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionSmooth
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inversion acts on the actual compact smooth sections. Both their
pointwise differential and quotient norm are transported geometrically. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaInversionSection_norm (F : CubicThetaSection) (q : CubicThetaQuotient) :
    cubicThetaSectionNorm (cubicThetaInversionSection F) q=
      cubicThetaSectionNorm F (cubicThetaIntegralQuotientMap cubicThetaFullInversion q) := by
  obtain ⟨p,rfl⟩ := cubicThetaQuotientMap_surjective q
  rw [cubicThetaSectionNorm_apply,cubicThetaIntegralQuotientMap_apply,cubicThetaSectionNorm_apply]
  rfl

lemma cubicThetaInversionSection_function (F : CubicThetaSection)
    {y : ℂ × ℝ} (hy : 0<y.2) :
    cubicThetaSectionFunction (cubicThetaInversionSection F) y=
      cubicThetaSectionFunction F (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) y) := by
  rw [cubicThetaSectionFunction_apply _ hy,cubicThetaSectionFunction_apply _
    (cubicThetaMobius_height_pos _ hy)]
  rfl

lemma cubicThetaInversionSection_smooth (F : cubicThetaSmoothTests) :
    ContDiffOn ℝ ∞ (cubicThetaSectionFunction (cubicThetaInversionSection F)) {y | 0<y.2} := by
  have hM : ContDiffOn ℝ ∞ (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion))
      {y : ℂ × ℝ | 0<y.2} := fun _ hy => (cubicThetaMobius_contDiffAt _ hy).contDiffWithinAt
  have hcomp := F.property.1.comp hM (fun _ hy => cubicThetaMobius_height_pos _ hy)
  exact hcomp.congr (fun _ hy => cubicThetaInversionSection_function F hy)

def cubicThetaInversionSmooth (F : cubicThetaSmoothTests) : cubicThetaSmoothTests :=
  ⟨cubicThetaInversionSection F,cubicThetaInversionSection_smooth F,by
    have h := F.property.2.comp_homeomorph
      (cubicThetaIntegralQuotientHomeomorph cubicThetaFullInversion)
    change HasCompactSupport (fun q => cubicThetaSectionNorm F
      (cubicThetaIntegralQuotientMap cubicThetaFullInversion q)) at h
    simpa only [←cubicThetaInversionSection_norm] using h⟩

lemma cubicThetaInversionSection_differential (F : cubicThetaSmoothTests) (p : CubicThetaPoint) :
    cubicThetaSectionDifferential (cubicThetaInversionSection F) p=
      (cubicThetaSectionDifferential F (cubicThetaFullInversion • p)).comp
        (cubicThetaTangentDerivative (cubicThetaFullComplex cubicThetaFullInversion) p.val) := by
  have hM := (cubicThetaMobius_contDiffAt
    (cubicThetaFullComplex cubicThetaFullInversion) p.property).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hF := cubicThetaSectionFunction_differentiable F
    (cubicThetaMobius_height_pos (cubicThetaFullComplex cubicThetaFullInversion) p.property)
  have hI := cubicThetaSectionFunction_differentiable (cubicThetaInversionSmooth F) p.property
  change DifferentiableAt ℝ (cubicThetaSectionFunction (cubicThetaInversionSection F)) p.val at hI
  have he : (fun y => cubicThetaSectionFunction F
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) y))=ᶠ[𝓝 p.val]
      cubicThetaSectionFunction (cubicThetaInversionSection F) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds p.property] with y hy
    exact (cubicThetaInversionSection_function F hy).symm
  have hd := ((hF.hasFDerivAt.comp p.val hM.hasFDerivAt).congr_of_eventuallyEq he.symm).unique
    hI.hasFDerivAt
  ext u
  have hv := congrArg (fun L : (ℂ × ℝ) →L[ℝ] ℂ => L (cubicThetaTangentCoordinates u)) hd
  have hgp : (cubicThetaFullInversion • p).val=
      cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val := rfl
  simpa only [cubicThetaSectionDifferential,cubicThetaTangentDerivative,
    ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply,hgp] using hv.symm

lemma cubicThetaInversionSection_energy (F : cubicThetaSmoothTests) (p : CubicThetaPoint) :
    cubicThetaSectionEnergy (cubicThetaInversionSection F) p=
      cubicThetaSectionEnergy F (cubicThetaFullInversion • p) := by
  rw [cubicThetaSectionEnergy,cubicThetaInversionSection_differential,
    cubicThetaTangentEnergy_derivative _ _ p.property]
  unfold cubicThetaSectionEnergy
  have hgp : (cubicThetaFullInversion • p).val=
      cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val := rfl
  rw [hgp]
  field_simp [p.property.ne']

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
def cubicThetaInversionSmoothLinear : cubicThetaSmoothTests →ₗ[ℂ] cubicThetaSmoothTests where
  toFun := cubicThetaInversionSmooth
  map_add' _F _G := rfl
  map_smul' _c _F := rfl

lemma cubicThetaInversion_quotient_energy (F : cubicThetaSmoothTests) (q : CubicThetaQuotient) :
    cubicThetaQuotientEnergy (cubicThetaInversionSmooth F) q=
      cubicThetaQuotientEnergy F (cubicThetaIntegralQuotientMap cubicThetaFullInversion q) := by
  obtain ⟨p,rfl⟩ := cubicThetaQuotientMap_surjective q
  rw [cubicThetaQuotientEnergy_apply,cubicThetaIntegralQuotientMap_apply,cubicThetaQuotientEnergy_apply]
  exact cubicThetaInversionSection_energy F p

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGlobalAutomorphicRange
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.supported_complete _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaEnergyPencil_ker_complete _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Values of completed energy vectors, and consequently the constructed
Green operator, remain in the closure of genuine automorphic sections. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaGlobalInclusion_mem (u : cubicThetaGlobalEnergySpace) :
    cubicThetaGlobalInclusion u∈cubicThetaAutomorphicL2 := by
  let P := WithLp.fstL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2
  have hr : cubicThetaGlobalEnergyGraph.range ≤ cubicThetaAutomorphicL2.comap P.toLinearMap := by
    rintro x ⟨F,rfl⟩
    change cubicThetaGlobalMass F∈cubicThetaAutomorphicL2
    exact Submodule.le_topologicalClosure _ ⟨F,rfl⟩
  have hc : IsClosed (cubicThetaAutomorphicL2.comap P.toLinearMap : Set CubicThetaGlobalEnergyAmbient) :=
    (Submodule.isClosed_topologicalClosure cubicThetaGlobalMass.range).preimage P.continuous
  exact cubicThetaGlobalEnergyGraph.range.topologicalClosure_minimal hr hc u.property

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionEnergyInvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inversion is an involutive isometry of the actual energy space and
preserves its mass form. It therefore preserves every spectral kernel. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFullInversion_involutive (p : CubicThetaPoint) :
    cubicThetaFullInversion • (cubicThetaFullInversion • p)=p := by
  apply Subtype.ext
  change cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion)
    (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val)=p.val
  rw [cubicThetaFullInversion_complex,
    cubicThetaMobius_inversion one_ne_zero (cubicThetaMobius_height_pos _ p.property),
    cubicThetaMobius_inversion one_ne_zero p.property]
  exact cubicThetaInversion_involutive one_ne_zero p.property

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaForcedResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The residue of the actual arithmetic continuation is an explicit
finite-dimensional spectral projection of its incoming forcing. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

lemma cubicThetaArithmeticResidueEnergy_kernel (σ : ℝ) :
    cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (σ:ℂ))
      (cubicThetaArithmeticResidueEnergy σ)=0 := by
  unfold cubicThetaArithmeticResidueEnergy
  rw [map_smul]
  have h := (cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (σ:ℂ))).ker.starProjection_apply_mem
    (cubicThetaGlobalInclusion.adjoint (cubicThetaForcingL2 (σ:ℂ)))
  change cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (σ:ℂ))
    (cubicThetaExceptionalProjection (cubicThetaGlobalSpectralParameter (σ:ℂ))
      (cubicThetaGlobalInclusion.adjoint (cubicThetaForcingL2 (σ:ℂ))))=0 at h
  rw [h,smul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCoverDegree
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite arithmetic covering has exactly its subgroup index as
measure degree. This gives the normalization for lifting actual L2 vectors. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

lemma cubicThetaFundamentalDomain_translates_disjoint
    {g h : cubicThetaPrincipalGroup} (hne : g≠h) :
    Disjoint ((fun x : CubicThetaPoint => g • x) '' cubicThetaFundamentalDomain)
      ((fun x : CubicThetaPoint => h • x) '' cubicThetaFundamentalDomain) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨a,ha,hga⟩ ⟨b,hb,hgb⟩
  dsimp only at hga hgb
  have hm : (h⁻¹*g) • a=b := by
    rw [mul_smul,hga,←hgb,inv_smul_smul]
  have he : h⁻¹*g=(1:cubicThetaPrincipalGroup) :=
    (cubicThetaFundamentalDomain_unique a).unique (by rwa [hm]) (by simpa using ha)
  exact hne (inv_mul_eq_one.mp he).symm

lemma cubicThetaFundamentalDomain_translate_map (g : cubicThetaPrincipalGroup) :
    (cubicThetaPointMeasure.restrict
      ((fun x : CubicThetaPoint => g • x) '' cubicThetaFundamentalDomain)).map
        cubicThetaQuotientMap=cubicThetaQuotientMeasure :=
  (cubicThetaQuotientMeasure_independent (cubicThetaIntegralImage_fundamental g.val)).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeCoverDomain
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Iwahori(p^3) fundamental domain underlying the cubed-prime
trace. It consists of precisely the finite cosets enumerated above. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeCoverDomain_measurable {p : Eisenstein} (hp : primaryPrime p) :
    MeasurableSet (cubicThetaPrimeCubeCoverDomain p) := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  apply MeasurableSet.iUnion
  intro t
  exact (Homeomorph.smul t.val).measurableEmbedding.measurableSet_image'
    cubicThetaFundamentalDomain_measurable

theorem cubicThetaPrimeCubeCoverDomain_unique (p : Eisenstein) (x : CubicThetaPoint) :
    ∃! g : cubicThetaPrimeIwahori (p^3),g • x∈cubicThetaPrimeCubeCoverDomain p := by
  obtain ⟨a,ha,hua⟩ := cubicThetaFundamentalDomain_unique x
  obtain ⟨⟨h,t⟩,he,hunique⟩ := (cubicThetaPrimeCubeTransversal_complement p).existsUnique a⁻¹
  have hmove : h.val⁻¹=t.val*a := by
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
    have hpair : ((k⁻¹,u) : cubicThetaPrimeIwahori (p^3) × cubicThetaPrimeCubeTransversal p)=(h,t) := by
      apply hunique
      change k.val⁻¹*u.val=a⁻¹
      rw [←hya]
      group
    have hh : k⁻¹=h := congrArg Prod.fst hpair
    simpa only [inv_inv] using congrArg Inv.inv hh

theorem cubicThetaPrimeCubeCoverDomain_isFundamentalDomain {p : Eisenstein}
    (hp : primaryPrime p) (μ : Measure CubicThetaPoint) :
    IsFundamentalDomain (cubicThetaPrimeIwahori (p^3)) (cubicThetaPrimeCubeCoverDomain p) μ :=
  IsFundamentalDomain.mk' (cubicThetaPrimeCubeCoverDomain_measurable hp).nullMeasurableSet
    (cubicThetaPrimeCubeCoverDomain_unique p)

lemma cubicThetaPrimeCubeCoverDomain_disjoint (p : Eisenstein) :
    Pairwise (fun t u : cubicThetaPrimeCubeTransversal p =>
      Disjoint ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain)
        ((fun x : CubicThetaPoint => u.val • x) '' cubicThetaFundamentalDomain)) := by
  intro t u htu
  exact cubicThetaFundamentalDomain_translates_disjoint (fun he => htu (Subtype.ext he))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeAtkinIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubed-prime Atkin involution preserves the actual integral norm
on its finite arithmetic covering, before passing to a completion. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

instance cubicThetaPrimeCubePointMeasure_invariant (p : Eisenstein) :
    SMulInvariantMeasure (cubicThetaPrimeIwahori (p^3)) CubicThetaPoint cubicThetaPointMeasure where
  measure_preimage_smul g _S hS :=
    SMulInvariantMeasure.measure_preimage_smul (g.val : cubicThetaPrincipalGroup) hS

lemma cubicThetaPrimeCubeAtkinImage_fundamental {p : Eisenstein} (hp : primaryPrime p) :
    IsFundamentalDomain (cubicThetaPrimeIwahori (p^3))
      ((fun x : CubicThetaPoint => cubicThetaPrimeCubeAtkinMatrix hp • x) ''
        cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure := by
  apply (cubicThetaPrimeCubeCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).image_of_equiv
    (Homeomorph.smul (cubicThetaPrimeCubeAtkinMatrix hp)).toEquiv
    (measurePreserving_smul (cubicThetaPrimeCubeAtkinMatrix hp)⁻¹
      cubicThetaPointMeasure).quasiMeasurePreserving
    (cubicThetaPrimeCubeAtkinEquiv hp)
  intro g x
  change cubicThetaPrimeCubeAtkinMatrix hp • (cubicThetaPrimeCubeAtkinEquiv hp g • x)=
    g • (cubicThetaPrimeCubeAtkinMatrix hp • x)
  rw [cubicThetaPrimeCubeAtkinPoint_intertwines]
  exact congrArg (fun h : cubicThetaPrimeIwahori (p^3) =>
    h • (cubicThetaPrimeCubeAtkinMatrix hp • x))
      (cubicThetaPrimeCubeAtkinConjugate_involutive hp g)

theorem cubicThetaPrimeCubeAtkin_integral_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p) :
    (∫ x in cubicThetaPrimeCubeCoverDomain p,
      ‖F.val (cubicThetaPrimeCubeAtkinMatrix hp • x)‖^2 ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaPrimeCubeCoverDomain p,‖F.val x‖^2 ∂cubicThetaPointMeasure := by
  let f : CubicThetaPoint → ℝ := fun x => ‖F.val x‖^2
  have hinv (g : cubicThetaPrimeIwahori (p^3)) (x : CubicThetaPoint) : f (g • x)=f x :=
    cubicThetaPrimeCubeSection_norm_invariant p F g x
  have he := (cubicThetaPrimeCubeCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).setIntegral_eq
    (cubicThetaPrimeCubeAtkinImage_fundamental hp) hinv
  have hc := (measurePreserving_smul (cubicThetaPrimeCubeAtkinMatrix hp) cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul (cubicThetaPrimeCubeAtkinMatrix hp)) f (cubicThetaPrimeCubeCoverDomain p)
  exact (he.trans hc).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeSectionAtkin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restriction and Atkin pullback of actual cubed-prime sections. The
original dilation is exactly Atkin pullback after the global inversion. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeDilation_eq_atkin {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) :
    cubicThetaPrimeCubeDilationSection hp F=
      cubicThetaPrimeCubeAtkinSection hp (cubicThetaPrimeCubeSectionRestrict (cubicThetaInversionSection F)) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x)=
    F.val (cubicThetaFullInversion • (cubicThetaPrimeCubeAtkinMatrix hp • x))
  rw [cubicThetaPrimeCubeAtkinMatrix,mul_smul]
  change F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x)=
    F.val (cubicThetaFullInversion • (cubicThetaFullInversion •
      (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x)))
  rw [cubicThetaFullInversion_involutive]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeSheetIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact integrals on the finite cubed-prime covering. Original invariant
functions gain exactly the computed index, with integrability preserved. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeSheetIntegral {p : Eisenstein} (hp : primaryPrime p)
    {f : CubicThetaPoint → ℝ}
    (hf : IntegrableOn f (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure) :
    (∫ x in cubicThetaPrimeCubeCoverDomain p,f x ∂cubicThetaPointMeasure)=
      ∑' t : cubicThetaPrimeCubeTransversal p,
        ∫ x in cubicThetaFundamentalDomain,f (t.val • x) ∂cubicThetaPointMeasure := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  rw [tsum_fintype]
  have hmeas (t : cubicThetaPrimeCubeTransversal p) :
      MeasurableSet ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain) :=
    (measurableEmbedding_const_smul t.val).measurableSet_image' cubicThetaFundamentalDomain_measurable
  have hint (t : cubicThetaPrimeCubeTransversal p) :
      IntegrableOn f ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain)
        cubicThetaPointMeasure :=
    hf.mono_set (subset_iUnion (fun u : cubicThetaPrimeCubeTransversal p =>
      (fun x : CubicThetaPoint => u.val • x) '' cubicThetaFundamentalDomain) t)
  change (∫ x in ⋃ t : cubicThetaPrimeCubeTransversal p,
    (fun y : CubicThetaPoint => t.val • y) '' cubicThetaFundamentalDomain,f x
      ∂cubicThetaPointMeasure)=_
  rw [integral_iUnion_fintype hmeas (cubicThetaPrimeCubeCoverDomain_disjoint p) hint]
  apply Finset.sum_congr rfl
  intro t _
  exact (measurePreserving_smul t.val cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul t.val) f cubicThetaFundamentalDomain

lemma cubicThetaPrimeCubeInvariant_integrable {p : Eisenstein} (hp : primaryPrime p)
    {f : CubicThetaPoint → ℝ} (hf : IntegrableOn f cubicThetaFundamentalDomain cubicThetaPointMeasure)
    (hi : ∀ (g : cubicThetaPrincipalGroup) x,f (g • x)=f x) :
    IntegrableOn f (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  apply integrableOn_iUnion_of_summable_integral_norm
  · intro t
    exact ((cubicThetaFundamentalDomain_isFundamentalDomain cubicThetaPointMeasure).integrableOn_iff
      (cubicThetaIntegralImage_fundamental t.val.val) hi).mp hf
  · exact Summable.of_finite

theorem cubicThetaPrimeCubeInvariant_integral {p : Eisenstein} (hp : primaryPrime p)
    {f : CubicThetaPoint → ℝ} (hf : IntegrableOn f cubicThetaFundamentalDomain cubicThetaPointMeasure)
    (hi : ∀ (g : cubicThetaPrincipalGroup) x,f (g • x)=f x) :
    (∫ x in cubicThetaPrimeCubeCoverDomain p,f x ∂cubicThetaPointMeasure)=
      ((normNat p)^3+(normNat p)^2:ℝ)*
        ∫ x in cubicThetaFundamentalDomain,f x ∂cubicThetaPointMeasure := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  rw [cubicThetaPrimeCubeSheetIntegral hp (cubicThetaPrimeCubeInvariant_integrable hp hf hi)]
  simp_rw [hi]
  rw [tsum_fintype,Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,
    (cubicThetaPrimeCubeTransversal_complement p).card_right,cubicThetaPrimeCubeIwahori_index hp]
  simp only [nsmul_eq_mul,Nat.cast_add,Nat.cast_pow]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeTraceNorm
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite trace has its Cauchy--Schwarz mass bound with the
exact covering index. The integrability assertion is proved from this
bound, so it will pass to the completed operator. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeSection_sheet_integrable {p : Eisenstein} (_hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure)
    (t : cubicThetaPrimeCubeTransversal p) :
    IntegrableOn (fun x => ‖F.val (t.val • x)‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure := by
  have hs : IntegrableOn (fun x => ‖F.val x‖^2)
      ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain) cubicThetaPointMeasure :=
    hF.mono_set (subset_iUnion (fun u : cubicThetaPrimeCubeTransversal p =>
      (fun x : CubicThetaPoint => u.val • x) '' cubicThetaFundamentalDomain) t)
  exact ((measurePreserving_smul t.val cubicThetaPointMeasure).integrableOn_image
    (measurableEmbedding_const_smul t.val)).mp hs

lemma cubicThetaPrimeCubeTrace_majorant_integrable {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure) :
    IntegrableOn (fun x => ((cubicThetaPrimeIwahori (p^3)).index:ℝ)*
      ∑' t : cubicThetaPrimeCubeTransversal p,‖F.val (t.val • x)‖^2)
      cubicThetaFundamentalDomain cubicThetaPointMeasure := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  simp_rw [tsum_fintype]
  exact (integrable_finsetSum Finset.univ (fun t _ =>
    cubicThetaPrimeCubeSection_sheet_integrable hp F hF t)).const_mul _

lemma cubicThetaPrimeCubeTrace_integrable {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure) :
    IntegrableOn (fun x => ‖(cubicThetaPrimeCubeTraceSection hp F).val x‖^2)
      cubicThetaFundamentalDomain cubicThetaPointMeasure := by
  apply (cubicThetaPrimeCubeTrace_majorant_integrable hp F hF).mono'
    (((cubicThetaPrimeCubeTraceSection hp F).val.continuous.norm.pow 2).aestronglyMeasurable)
  filter_upwards with x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact cubicThetaPrimeCubeTrace_norm_sq_le hp F x

theorem cubicThetaPrimeCubeTrace_mass_integral_le {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure) :
    (∫ x in cubicThetaFundamentalDomain,‖(cubicThetaPrimeCubeTraceSection hp F).val x‖^2
      ∂cubicThetaPointMeasure)≤((cubicThetaPrimeIwahori (p^3)).index:ℝ)*
        ∫ x in cubicThetaPrimeCubeCoverDomain p,‖F.val x‖^2 ∂cubicThetaPointMeasure := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  calc
    _ ≤ ∫ x in cubicThetaFundamentalDomain,((cubicThetaPrimeIwahori (p^3)).index:ℝ)*
        ∑' t : cubicThetaPrimeCubeTransversal p,‖F.val (t.val • x)‖^2 ∂cubicThetaPointMeasure :=
      integral_mono (cubicThetaPrimeCubeTrace_integrable hp F hF)
        (cubicThetaPrimeCubeTrace_majorant_integrable hp F hF) (cubicThetaPrimeCubeTrace_norm_sq_le hp F)
    _ = _ := by
      simp_rw [tsum_fintype]
      rw [integral_const_mul,integral_finsetSum Finset.univ
        (fun t _ => cubicThetaPrimeCubeSection_sheet_integrable hp F hF t),
        cubicThetaPrimeCubeSheetIntegral hp hF,tsum_fintype]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeDilationNorm
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubed-prime dilation has exactly the finite-cover mass factor.
Consequently the literal Hecke operator is bounded on the original L2
sections, with no analytic assumption. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeAtkin_integrable {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure) :
    IntegrableOn (fun x => ‖(cubicThetaPrimeCubeAtkinSection hp F).val x‖^2)
      (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure := by
  have hi := (cubicThetaPrimeCubeCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).integrableOn_iff
    (cubicThetaPrimeCubeAtkinImage_fundamental hp) (f:=fun x : CubicThetaPoint => ‖F.val x‖^2)
      (cubicThetaPrimeCubeSection_norm_invariant p F)
  have hImage := hi.mp hF
  exact ((measurePreserving_smul (cubicThetaPrimeCubeAtkinMatrix hp) cubicThetaPointMeasure).integrableOn_image
    (measurableEmbedding_const_smul (cubicThetaPrimeCubeAtkinMatrix hp))).mp hImage

lemma cubicThetaInversion_domain_integrable (F : CubicThetaSection)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    IntegrableOn (fun x => ‖(cubicThetaInversionSection F).val x‖^2)
      cubicThetaFundamentalDomain cubicThetaPointMeasure := by
  have hImage := ((cubicThetaFundamentalDomain_isFundamentalDomain cubicThetaPointMeasure).integrableOn_iff
    (cubicThetaIntegralImage_fundamental cubicThetaFullInversion) (cubicThetaOriginal_norm_invariant F)).mp hF
  exact ((measurePreserving_smul cubicThetaFullInversion cubicThetaPointMeasure).integrableOn_image
    (measurableEmbedding_const_smul cubicThetaFullInversion)).mp hImage

lemma cubicThetaInversion_domain_integral (F : CubicThetaSection) :
    (∫ x in cubicThetaFundamentalDomain,‖(cubicThetaInversionSection F).val x‖^2 ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaFundamentalDomain,‖F.val x‖^2 ∂cubicThetaPointMeasure := by
  have he := (cubicThetaFundamentalDomain_isFundamentalDomain cubicThetaPointMeasure).setIntegral_eq
    (cubicThetaIntegralImage_fundamental cubicThetaFullInversion) (f:=fun x : CubicThetaPoint => ‖F.val x‖^2)
      (cubicThetaOriginal_norm_invariant F)
  have hc := (measurePreserving_smul cubicThetaFullInversion cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul cubicThetaFullInversion) (fun x => ‖F.val x‖^2) cubicThetaFundamentalDomain
  exact (he.trans hc).symm

lemma cubicThetaPrimeCubeDilation_integrable {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    IntegrableOn (fun x => ‖(cubicThetaPrimeCubeDilationSection hp F).val x‖^2)
      (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure := by
  rw [cubicThetaPrimeCubeDilation_eq_atkin]
  apply cubicThetaPrimeCubeAtkin_integrable hp
  exact cubicThetaPrimeCubeInvariant_integrable hp (cubicThetaInversion_domain_integrable F hF)
    (cubicThetaOriginal_norm_invariant (cubicThetaInversionSection F))

theorem cubicThetaPrimeCubeDilation_integral_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    (∫ x in cubicThetaPrimeCubeCoverDomain p,‖(cubicThetaPrimeCubeDilationSection hp F).val x‖^2
      ∂cubicThetaPointMeasure)=((cubicThetaPrimeIwahori (p^3)).index:ℝ)*
        ∫ x in cubicThetaFundamentalDomain,‖F.val x‖^2 ∂cubicThetaPointMeasure := by
  rw [cubicThetaPrimeCubeDilation_eq_atkin]
  change (∫ x in cubicThetaPrimeCubeCoverDomain p,
    ‖(cubicThetaPrimeCubeSectionRestrict (p:=p) (cubicThetaInversionSection F)).val
      (cubicThetaPrimeCubeAtkinMatrix hp • x)‖^2 ∂cubicThetaPointMeasure)=_
  rw [cubicThetaPrimeCubeAtkin_integral_norm hp]
  change (∫ x in cubicThetaPrimeCubeCoverDomain p,‖(cubicThetaInversionSection F).val x‖^2
    ∂cubicThetaPointMeasure)=_
  rw [cubicThetaPrimeCubeInvariant_integral hp (cubicThetaInversion_domain_integrable F hF)
    (cubicThetaOriginal_norm_invariant (cubicThetaInversionSection F)),
    cubicThetaInversion_domain_integral,cubicThetaPrimeCubeIwahori_index hp]
  norm_cast

theorem cubicThetaPrimeCubeHecke_integral_bound {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    (∫ x in cubicThetaFundamentalDomain,‖(cubicThetaPrimeCubeHecke hp F).val x‖^2
      ∂cubicThetaPointMeasure)≤((cubicThetaPrimeIwahori (p^3)).index:ℝ)^2*
        ∫ x in cubicThetaFundamentalDomain,‖F.val x‖^2 ∂cubicThetaPointMeasure := by
  have he := cubicThetaPrimeCubeTrace_mass_integral_le hp (cubicThetaPrimeCubeDilationSection hp F)
    (cubicThetaPrimeCubeDilation_integrable hp F hF)
  rw [cubicThetaPrimeCubeDilation_integral_norm hp F hF] at he
  simpa only [cubicThetaPrimeCubeHecke,pow_two,mul_assoc] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeHeckeRegularity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First differentiability of the literal cubed-prime Hecke trace.
Every summand is the actual Mobius pullback, including its cubic phase. -/
noncomputable section
open Set
namespace CubicFirstMoment

def cubicThetaPrimeCubeHeckeCoordinate {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (t : cubicThetaPrimeCubeTransversal p) (y : ℂ × ℝ) : ℂ :=
  star (cubicThetaKubotaValue t.val)*
    cubicThetaSectionFunction F (cubicThetaMobius (cubicThetaPrimeCubeHeckeMatrix hp t) y)

lemma cubicThetaPrimeCubeHecke_function {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) {y : ℂ × ℝ} (hy : 0<y.2) :
    cubicThetaSectionFunction (cubicThetaPrimeCubeHecke hp F) y=
      ∑' t : cubicThetaPrimeCubeTransversal p,cubicThetaPrimeCubeHeckeCoordinate hp F t y := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  rw [cubicThetaSectionFunction_apply _ hy]
  rw [cubicThetaPrimeCubeHecke_apply hp F (⟨y,hy⟩ : CubicThetaPoint)]
  apply tsum_congr
  intro t
  unfold cubicThetaPrimeCubeHeckeCoordinate
  rw [cubicThetaSectionFunction_apply _ (cubicThetaMobius_height_pos _ hy)]
  exact congrArg (fun x : CubicThetaPoint => star (cubicThetaKubotaValue t.val)*F.val x)
    (mul_smul (β:=CubicThetaPoint) (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))
      (cubicThetaPrincipalComplex t.val) (⟨y,hy⟩ : CubicThetaPoint)).symm

lemma cubicThetaPrimeCubeHeckeCoordinate_c1 {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (t : cubicThetaPrimeCubeTransversal p) :
    ContDiffOn ℝ 1 (cubicThetaPrimeCubeHeckeCoordinate hp F t) {y : ℂ × ℝ | 0<y.2} := by
  have hm : ContDiffOn ℝ 1 (cubicThetaMobius (cubicThetaPrimeCubeHeckeMatrix hp t))
      {y : ℂ × ℝ | 0<y.2} := fun _ hy =>
    ((cubicThetaMobius_contDiffAt _ hy).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffWithinAt
  exact contDiffOn_const.mul (hF.comp hm (fun _ hy => cubicThetaMobius_height_pos _ hy))

theorem cubicThetaPrimeCubeHecke_c1 {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) :
    ContDiffOn ℝ 1 (cubicThetaSectionFunction (cubicThetaPrimeCubeHecke hp F))
      {y : ℂ × ℝ | 0<y.2} := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  have hs := ContDiffOn.sum (s:=Finset.univ)
    (fun t _ => cubicThetaPrimeCubeHeckeCoordinate_c1 hp F hF t)
  apply hs.congr
  intro y hy
  simpa only [tsum_fintype] using cubicThetaPrimeCubeHecke_function hp F hy

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeHeckeEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pointwise gradient bound for the actual cubed-prime trace. Its
summands use the hyperbolic isometry identity, not a coordinate estimate. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeHeckeCoordinate_energy {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (t : cubicThetaPrimeCubeTransversal p) (x : CubicThetaPoint) :
    x.val.2^2*cubicThetaFunctionEnergy (cubicThetaPrimeCubeHeckeCoordinate hp F t) x.val=
      cubicThetaSectionEnergy F (cubicThetaPrimeCubeHeckeMatrix hp t • x) := by
  let f := fun y => cubicThetaSectionFunction F (cubicThetaMobius (cubicThetaPrimeCubeHeckeMatrix hp t) y)
  have hf := (hF.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds
    (cubicThetaMobius_height_pos (cubicThetaPrimeCubeHeckeMatrix hp t) x.property))).differentiableAt
      (by norm_num)
  have hd : DifferentiableAt ℝ f x.val :=
    hf.comp x.val ((cubicThetaMobius_contDiffAt _ x.property).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have he : fderiv ℝ (cubicThetaPrimeCubeHeckeCoordinate hp F t) x.val=
      star (cubicThetaKubotaValue t.val) • fderiv ℝ f x.val :=
    (hd.hasFDerivAt.const_smul (star (cubicThetaKubotaValue t.val))).fderiv
  have hc : cubicThetaFunctionEnergy (cubicThetaPrimeCubeHeckeCoordinate hp F t) x.val=
      cubicThetaFunctionEnergy f x.val := by
    unfold cubicThetaFunctionEnergy
    rw [he,ContinuousLinearMap.smul_comp,cubicThetaTangentEnergy_complex_smul,
      norm_star,cubicThetaKubotaValue_norm,one_pow,one_mul]
  rw [hc]
  exact cubicThetaFunctionEnergy_mobius (cubicThetaSectionFunction F)
    (cubicThetaPrimeCubeHeckeMatrix hp t) x.property hf

theorem cubicThetaPrimeCubeHecke_energy_le {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (x : CubicThetaPoint) :
    cubicThetaSectionEnergy (cubicThetaPrimeCubeHecke hp F) x≤
      ((cubicThetaPrimeIwahori (p^3)).index:ℝ)*
        ∑' t : cubicThetaPrimeCubeTransversal p,
          cubicThetaSectionEnergy F (cubicThetaPrimeCubeHeckeMatrix hp t • x) := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  have he : cubicThetaSectionFunction (cubicThetaPrimeCubeHecke hp F)=ᶠ[𝓝 x.val]
      (fun y => ∑ t : cubicThetaPrimeCubeTransversal p,cubicThetaPrimeCubeHeckeCoordinate hp F t y) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds x.property] with y hy
    simpa only [tsum_fintype] using cubicThetaPrimeCubeHecke_function hp F hy
  have hd (t : cubicThetaPrimeCubeTransversal p) :
      DifferentiableAt ℝ (cubicThetaPrimeCubeHeckeCoordinate hp F t) x.val :=
    ((cubicThetaPrimeCubeHeckeCoordinate_c1 hp F hF t).contDiffAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds x.property)).differentiableAt (by norm_num)
  have hs := mul_le_mul_of_nonneg_left
    (cubicThetaFunctionEnergy_sum_le Finset.univ (cubicThetaPrimeCubeHeckeCoordinate hp F) x.val
      (fun t _ => hd t)) (sq_nonneg x.val.2)
  change x.val.2^2*cubicThetaFunctionEnergy (cubicThetaSectionFunction (cubicThetaPrimeCubeHecke hp F)) x.val≤_
  have hfun : cubicThetaFunctionEnergy (cubicThetaSectionFunction (cubicThetaPrimeCubeHecke hp F)) x.val=
      cubicThetaFunctionEnergy (fun y => ∑ t : cubicThetaPrimeCubeTransversal p,
        cubicThetaPrimeCubeHeckeCoordinate hp F t y) x.val := by
    unfold cubicThetaFunctionEnergy
    rw [he.fderiv_eq]
  rw [hfun,tsum_fintype]
  calc
    _ ≤ x.val.2^2*((Finset.univ.card:ℝ)*∑ t : cubicThetaPrimeCubeTransversal p,
        cubicThetaFunctionEnergy (cubicThetaPrimeCubeHeckeCoordinate hp F t) x.val) := hs
    _ = _ := by
      rw [mul_left_comm,Finset.mul_sum]
      simp_rw [cubicThetaPrimeCubeHeckeCoordinate_energy hp F hF]
      rw [Finset.card_univ,←Nat.card_eq_fintype_card,
        (cubicThetaPrimeCubeTransversal_complement p).card_right]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeInvariantDilation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar integration for the actual dilation. This is used for the
invariant derivative energy as well as the mass density. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeDilation_inversion_atkin {p : Eisenstein} (hp : primaryPrime p)
    (x : CubicThetaPoint) :
    cubicThetaFullInversion • (cubicThetaPrimeCubeAtkinMatrix hp • x)=
      cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x := by
  rw [cubicThetaPrimeCubeAtkinMatrix,mul_smul]
  change cubicThetaFullInversion • (cubicThetaFullInversion •
    (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x))=_
  rw [cubicThetaFullInversion_involutive]

lemma cubicThetaPrimeCubeScalarAtkin_integrable {p : Eisenstein} (hp : primaryPrime p)
    {f : CubicThetaPoint → ℝ}
    (hf : IntegrableOn f (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure)
    (hi : ∀ (g : cubicThetaPrimeIwahori (p^3)) x,f (g • x)=f x) :
    IntegrableOn (fun x => f (cubicThetaPrimeCubeAtkinMatrix hp • x))
      (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure := by
  have hImage := ((cubicThetaPrimeCubeCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).integrableOn_iff
    (cubicThetaPrimeCubeAtkinImage_fundamental hp) hi).mp hf
  exact ((measurePreserving_smul (cubicThetaPrimeCubeAtkinMatrix hp) cubicThetaPointMeasure).integrableOn_image
    (measurableEmbedding_const_smul (cubicThetaPrimeCubeAtkinMatrix hp))).mp hImage

lemma cubicThetaPrimeCubeScalarAtkin_integral {p : Eisenstein} (hp : primaryPrime p)
    {f : CubicThetaPoint → ℝ}
    (hi : ∀ (g : cubicThetaPrimeIwahori (p^3)) x,f (g • x)=f x) :
    (∫ x in cubicThetaPrimeCubeCoverDomain p,f (cubicThetaPrimeCubeAtkinMatrix hp • x)
      ∂cubicThetaPointMeasure)=∫ x in cubicThetaPrimeCubeCoverDomain p,f x ∂cubicThetaPointMeasure := by
  have he := (cubicThetaPrimeCubeCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).setIntegral_eq
    (cubicThetaPrimeCubeAtkinImage_fundamental hp) hi
  have hc := (measurePreserving_smul (cubicThetaPrimeCubeAtkinMatrix hp) cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul (cubicThetaPrimeCubeAtkinMatrix hp)) f (cubicThetaPrimeCubeCoverDomain p)
  exact (he.trans hc).symm

lemma cubicThetaScalarInversion_integrable {f : CubicThetaPoint → ℝ}
    (hf : IntegrableOn f cubicThetaFundamentalDomain cubicThetaPointMeasure)
    (hi : ∀ (g : cubicThetaPrincipalGroup) x,f (g • x)=f x) :
    IntegrableOn (fun x => f (cubicThetaFullInversion • x)) cubicThetaFundamentalDomain cubicThetaPointMeasure := by
  have hImage := ((cubicThetaFundamentalDomain_isFundamentalDomain cubicThetaPointMeasure).integrableOn_iff
    (cubicThetaIntegralImage_fundamental cubicThetaFullInversion) hi).mp hf
  exact ((measurePreserving_smul cubicThetaFullInversion cubicThetaPointMeasure).integrableOn_image
    (measurableEmbedding_const_smul cubicThetaFullInversion)).mp hImage

lemma cubicThetaScalarInversion_integral {f : CubicThetaPoint → ℝ}
    (hi : ∀ (g : cubicThetaPrincipalGroup) x,f (g • x)=f x) :
    (∫ x in cubicThetaFundamentalDomain,f (cubicThetaFullInversion • x) ∂cubicThetaPointMeasure)=
      ∫ x in cubicThetaFundamentalDomain,f x ∂cubicThetaPointMeasure := by
  have he := (cubicThetaFundamentalDomain_isFundamentalDomain cubicThetaPointMeasure).setIntegral_eq
    (cubicThetaIntegralImage_fundamental cubicThetaFullInversion) hi
  have hc := (measurePreserving_smul cubicThetaFullInversion cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul cubicThetaFullInversion) f cubicThetaFundamentalDomain
  exact (he.trans hc).symm

theorem cubicThetaPrimeCubeScalarDilation_integrable {p : Eisenstein} (hp : primaryPrime p)
    {f : CubicThetaPoint → ℝ}
    (hf : IntegrableOn f cubicThetaFundamentalDomain cubicThetaPointMeasure)
    (hi : ∀ (g : cubicThetaPrincipalGroup) x,f (g • x)=f x) :
    IntegrableOn (fun x => f (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x))
      (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure := by
  have hI := cubicThetaPrimeCubeInvariant_integrable hp (cubicThetaScalarInversion_integrable hf hi)
    (cubicThetaScalarInversion_invariant hi)
  have hA := cubicThetaPrimeCubeScalarAtkin_integrable hp hI
    (fun g x => cubicThetaScalarInversion_invariant hi g.val x)
  simpa only [cubicThetaPrimeCubeDilation_inversion_atkin] using hA

theorem cubicThetaPrimeCubeScalarDilation_integral {p : Eisenstein} (hp : primaryPrime p)
    {f : CubicThetaPoint → ℝ}
    (hf : IntegrableOn f cubicThetaFundamentalDomain cubicThetaPointMeasure)
    (hi : ∀ (g : cubicThetaPrincipalGroup) x,f (g • x)=f x) :
    (∫ x in cubicThetaPrimeCubeCoverDomain p,f (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x)
      ∂cubicThetaPointMeasure)=((cubicThetaPrimeIwahori (p^3)).index:ℝ)*
        ∫ x in cubicThetaFundamentalDomain,f x ∂cubicThetaPointMeasure := by
  have hA := cubicThetaPrimeCubeScalarAtkin_integral hp
    (f:=fun x => f (cubicThetaFullInversion • x))
    (fun g x => cubicThetaScalarInversion_invariant hi g.val x)
  simp only [cubicThetaPrimeCubeDilation_inversion_atkin] at hA
  rw [hA,cubicThetaPrimeCubeInvariant_integral hp (cubicThetaScalarInversion_integrable hf hi)
    (cubicThetaScalarInversion_invariant hi),cubicThetaScalarInversion_integral hi,
    cubicThetaPrimeCubeIwahori_index hp]
  norm_cast

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeEnergyIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal Hecke trace preserves integrable derivative energy,
with the same degree-squared bound as its mass. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeSheet_integrable {p : Eisenstein}
    {f : CubicThetaPoint → ℝ}
    (hf : IntegrableOn f (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure)
    (t : cubicThetaPrimeCubeTransversal p) :
    IntegrableOn (fun x => f (t.val • x)) cubicThetaFundamentalDomain cubicThetaPointMeasure := by
  have hs : IntegrableOn f ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain)
      cubicThetaPointMeasure :=
    hf.mono_set (subset_iUnion (fun u : cubicThetaPrimeCubeTransversal p =>
      (fun x : CubicThetaPoint => u.val • x) '' cubicThetaFundamentalDomain) t)
  exact ((measurePreserving_smul t.val cubicThetaPointMeasure).integrableOn_image
    (measurableEmbedding_const_smul t.val)).mp hs

lemma cubicThetaPrimeCubeHecke_energy_majorant {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hE : IntegrableOn (cubicThetaSectionEnergy F) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    IntegrableOn (fun x => ((cubicThetaPrimeIwahori (p^3)).index:ℝ)*
      ∑' t : cubicThetaPrimeCubeTransversal p,
        cubicThetaSectionEnergy F (cubicThetaPrimeCubeHeckeMatrix hp t • x))
      cubicThetaFundamentalDomain cubicThetaPointMeasure := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  have hd := cubicThetaPrimeCubeScalarDilation_integrable hp hE (cubicThetaC1Energy_invariant F hF)
  simp_rw [tsum_fintype,cubicThetaPrimeCubeHeckeMatrix_action]
  exact (integrable_finsetSum Finset.univ (fun t _ => cubicThetaPrimeCubeSheet_integrable hd t)).const_mul _

lemma cubicThetaPrimeCubeHecke_energy_integrable {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hE : IntegrableOn (cubicThetaSectionEnergy F) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    IntegrableOn (cubicThetaSectionEnergy (cubicThetaPrimeCubeHecke hp F))
      cubicThetaFundamentalDomain cubicThetaPointMeasure := by
  apply (cubicThetaPrimeCubeHecke_energy_majorant hp F hF hE).mono'
    (cubicThetaC1Energy_continuous _ (cubicThetaPrimeCubeHecke_c1 hp F hF)).aestronglyMeasurable
  filter_upwards with x
  have hn : 0 ≤ cubicThetaSectionEnergy (cubicThetaPrimeCubeHecke hp F) x :=
    mul_nonneg (sq_nonneg _) (cubicThetaTangentEnergy_nonneg _)
  rw [Real.norm_eq_abs,abs_of_nonneg hn]
  exact cubicThetaPrimeCubeHecke_energy_le hp F hF x

theorem cubicThetaPrimeCubeHecke_energy_integral_le {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hE : IntegrableOn (cubicThetaSectionEnergy F) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    (∫ x in cubicThetaFundamentalDomain,cubicThetaSectionEnergy (cubicThetaPrimeCubeHecke hp F) x
      ∂cubicThetaPointMeasure)≤((cubicThetaPrimeIwahori (p^3)).index:ℝ)^2*
        ∫ x in cubicThetaFundamentalDomain,cubicThetaSectionEnergy F x ∂cubicThetaPointMeasure := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  have hd := cubicThetaPrimeCubeScalarDilation_integrable hp hE (cubicThetaC1Energy_invariant F hF)
  calc
    _ ≤ ∫ x in cubicThetaFundamentalDomain,((cubicThetaPrimeIwahori (p^3)).index:ℝ)*
        ∑' t : cubicThetaPrimeCubeTransversal p,
          cubicThetaSectionEnergy F (cubicThetaPrimeCubeHeckeMatrix hp t • x) ∂cubicThetaPointMeasure :=
      integral_mono (cubicThetaPrimeCubeHecke_energy_integrable hp F hF hE)
        (cubicThetaPrimeCubeHecke_energy_majorant hp F hF hE) (cubicThetaPrimeCubeHecke_energy_le hp F hF)
    _ = ((cubicThetaPrimeIwahori (p^3)).index:ℝ)*
        ∫ x in cubicThetaPrimeCubeCoverDomain p,
          cubicThetaSectionEnergy F (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x)
            ∂cubicThetaPointMeasure := by
      simp_rw [cubicThetaPrimeCubeHeckeMatrix_action,tsum_fintype]
      rw [integral_const_mul,integral_finsetSum Finset.univ
        (fun t _ => cubicThetaPrimeCubeSheet_integrable hd t),cubicThetaPrimeCubeSheetIntegral hp hd,tsum_fintype]
    _ = _ := by
      rw [cubicThetaPrimeCubeScalarDilation_integral hp hE (cubicThetaC1Energy_invariant F hF)]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionL2Bounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaStrip_finiteMeasure _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.W21.instNorm _root_.instMeasurableSpace
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

lemma cubicThetaSectionL2_norm_sq (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    ‖hF.toLp (cubicThetaSectionRepresentative F)‖^2=
      ∫ q, cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure := by
  rw [cubicTheta_l2_norm_sq_measure]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp] with q hq
  rw [hq,cubicThetaSectionRepresentative_norm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeLiftL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized lifting from the original automorphic L2 closure to the
actual finite prime cover. The normalization is the square root of its degree. -/
noncomputable section
open Topology
namespace CubicFirstMoment

local instance primeLift_smoothGroup_r47b728_1 : AddCommGroup cubicThetaSmoothTests :=
  Module.addCommMonoidToAddCommGroup ℂ
def cubicThetaGlobalMassClosure : cubicThetaSmoothTests →ₗ[ℂ] cubicThetaAutomorphicL2 :=
  cubicThetaGlobalMass.codRestrict cubicThetaAutomorphicL2
    (fun F => Submodule.le_topologicalClosure _ ⟨F,rfl⟩)

lemma cubicThetaGlobalMassClosure_dense : DenseRange cubicThetaGlobalMassClosure := by
  intro u
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have he : Subtype.val '' Set.range cubicThetaGlobalMassClosure=Set.range cubicThetaGlobalMass := by
    ext y
    constructor
    · rintro ⟨v,⟨F,rfl⟩,rfl⟩
      exact ⟨F,rfl⟩
    · rintro ⟨F,rfl⟩
      exact ⟨cubicThetaGlobalMassClosure F,⟨F,rfl⟩,rfl⟩
  rw [he]
  exact u.property

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeArithmeticResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonzero arithmetic spectral residue is lifted to the actual
prime cover. Its Atkin translate has equal norm and is orthogonal to it. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaArithmeticResidueL2 : cubicThetaAutomorphicL2 :=
  ⟨cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3)),
    cubicThetaGlobalInclusion_mem _⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeEnergyDomainNorm
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal fundamental-domain formulas for the two coordinates of
the original and prime-cover energy graphs. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaFiniteEnergyValue_domain_norm_sq (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaFiniteEnergyValue F‖^2=
      ∫ x in cubicThetaFundamentalDomain, ‖F.val.val x‖^2 ∂cubicThetaPointMeasure := by
  change ‖F.property.2.1.toLp (cubicThetaSectionRepresentative F.val)‖^2=_
  rw [cubicThetaSectionL2_norm_sq,cubicThetaQuotientMeasure]
  have hi := integral_map_of_stronglyMeasurable
    (μ:=cubicThetaPointMeasure.restrict cubicThetaFundamentalDomain)
    cubicThetaQuotientMap_open.continuous.measurable
    ((cubicThetaSectionNorm_continuous F.val).pow 2).stronglyMeasurable
  simpa only [Pi.pow_apply,cubicThetaSectionNorm_apply] using hi

lemma cubicThetaFiniteEnergyGradient_domain_norm_sq (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaFiniteEnergyGradient F‖^2=
      ∫ x in cubicThetaFundamentalDomain, cubicThetaSectionEnergy F.val x
        ∂cubicThetaPointMeasure := by
  have he : ‖cubicThetaFiniteEnergyGradient F‖^2=
      ∫ q, cubicThetaC1QuotientEnergy F.val q ∂cubicThetaQuotientMeasure := by
    rw [cubicTheta_l2_norm_sq_measure]
    apply integral_congr_ae
    filter_upwards [F.property.2.2.coeFn_toLp] with q hq
    change ‖(F.property.2.2.toLp _) q‖^2=_
    rw [hq,cubicThetaC1Gradient_norm_sq F.val F.property.1]
  rw [he,cubicThetaQuotientMeasure]
  have hi := integral_map_of_stronglyMeasurable
    (μ:=cubicThetaPointMeasure.restrict cubicThetaFundamentalDomain)
    cubicThetaQuotientMap_open.continuous.measurable
    (cubicThetaC1QuotientEnergy_continuous F.val F.property.1).stronglyMeasurable
  simpa only [cubicThetaC1QuotientEnergy_apply F.val F.property.1] using hi

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeFiniteEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal cubed-prime Hecke operator preserves actual finite-energy
C1 sections. Both its value and gradient bounds are inherited from the
proved domain integral identities. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeFinite_mass_domain (F : cubicThetaFiniteEnergySections) :
    IntegrableOn (fun x => ‖F.val.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure := by
  have hn : Integrable (fun q => (cubicThetaSectionNorm F.val q)^2) cubicThetaQuotientMeasure := by
    simpa only [cubicThetaSectionRepresentative_norm] using
      F.property.2.1.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hc := hn.comp_measurable cubicThetaQuotientMap_open.continuous.measurable
  simpa only [IntegrableOn,Function.comp_def,cubicThetaSectionNorm_apply] using hc

lemma cubicThetaPrimeCubeFinite_energy_domain (F : cubicThetaFiniteEnergySections) :
    IntegrableOn (cubicThetaSectionEnergy F.val) cubicThetaFundamentalDomain cubicThetaPointMeasure := by
  have hn : Integrable (cubicThetaC1QuotientEnergy F.val) cubicThetaQuotientMeasure := by
    simpa only [cubicThetaC1Gradient_norm_sq F.val F.property.1] using
      F.property.2.2.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hc := hn.comp_measurable cubicThetaQuotientMap_open.continuous.measurable
  simpa only [IntegrableOn,Function.comp_def,cubicThetaC1QuotientEnergy_apply F.val F.property.1] using hc

lemma cubicThetaPrimeCubeSection_memLp_of_domain (F : CubicThetaSection)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure := by
  apply (memLp_two_iff_integrable_sq_norm (cubicThetaSectionRepresentative_measurable F).aestronglyMeasurable).mpr
  simp only [cubicThetaSectionRepresentative_norm]
  apply (integrable_map_measure ((cubicThetaSectionNorm_continuous F).pow 2).aestronglyMeasurable
    cubicThetaQuotientMap_open.continuous.measurable.aemeasurable).mpr
  simpa only [IntegrableOn,Function.comp_def,Pi.pow_apply,cubicThetaSectionNorm_apply] using hF

lemma cubicThetaPrimeCubeGradient_memLp_of_domain (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hE : IntegrableOn (cubicThetaSectionEnergy F) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    MemLp (cubicThetaGradientRepresentative F) 2 cubicThetaQuotientMeasure := by
  have hm : Measurable (cubicThetaGradientRepresentative F) :=
    (cubicThetaC1Gradient_continuous F hF).measurable.comp cubicThetaBorelSection_measurable
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  simp only [cubicThetaC1Gradient_norm_sq F hF]
  apply (integrable_map_measure (cubicThetaC1QuotientEnergy_continuous F hF).aestronglyMeasurable
    cubicThetaQuotientMap_open.continuous.measurable.aemeasurable).mpr
  simpa only [IntegrableOn,Function.comp_def,cubicThetaC1QuotientEnergy_apply F hF] using hE

def cubicThetaPrimeCubeHeckeFinite {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) : cubicThetaFiniteEnergySections :=
  ⟨cubicThetaPrimeCubeHecke hp F.val,cubicThetaPrimeCubeHecke_c1 hp F.val F.property.1,
    cubicThetaPrimeCubeSection_memLp_of_domain _
      (cubicThetaPrimeCubeTrace_integrable hp (cubicThetaPrimeCubeDilationSection hp F.val)
        (cubicThetaPrimeCubeDilation_integrable hp F.val (cubicThetaPrimeCubeFinite_mass_domain F))),
    cubicThetaPrimeCubeGradient_memLp_of_domain _ (cubicThetaPrimeCubeHecke_c1 hp F.val F.property.1)
      (cubicThetaPrimeCubeHecke_energy_integrable hp F.val F.property.1
        (cubicThetaPrimeCubeFinite_energy_domain F))⟩

theorem cubicThetaPrimeCubeHeckeFinite_value_bound {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaFiniteEnergyValue (cubicThetaPrimeCubeHeckeFinite hp F)‖^2≤
      ((cubicThetaPrimeIwahori (p^3)).index:ℝ)^2*‖cubicThetaFiniteEnergyValue F‖^2 := by
  rw [cubicThetaFiniteEnergyValue_domain_norm_sq,cubicThetaFiniteEnergyValue_domain_norm_sq]
  exact cubicThetaPrimeCubeHecke_integral_bound hp F.val (cubicThetaPrimeCubeFinite_mass_domain F)

theorem cubicThetaPrimeCubeHeckeFinite_gradient_bound {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaFiniteEnergyGradient (cubicThetaPrimeCubeHeckeFinite hp F)‖^2≤
      ((cubicThetaPrimeIwahori (p^3)).index:ℝ)^2*‖cubicThetaFiniteEnergyGradient F‖^2 := by
  rw [cubicThetaFiniteEnergyGradient_domain_norm_sq,cubicThetaFiniteEnergyGradient_domain_norm_sq]
  exact cubicThetaPrimeCubeHecke_energy_integral_le hp F.val F.property.1
    (cubicThetaPrimeCubeFinite_energy_domain F)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeHeckeLinear
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linearity of the literal cubed-prime Hecke correspondence, including
its action on actual finite-energy sections. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeHecke_smul {p : Eisenstein} (hp : primaryPrime p)
    (c : ℂ) (F : CubicThetaSection) :
    cubicThetaPrimeCubeHecke hp (c • F)=c • cubicThetaPrimeCubeHecke hp F := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change (∑' t : cubicThetaPrimeCubeTransversal p,star (cubicThetaKubotaValue t.val)*
    (c*F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • (t.val • x))))=
      c*∑' t : cubicThetaPrimeCubeTransversal p,star (cubicThetaKubotaValue t.val)*
        F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • (t.val • x))
  simp only [tsum_fintype,mul_left_comm,Finset.mul_sum]

def cubicThetaPrimeCubeHeckeFiniteLinear {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaFiniteEnergySections →ₗ[ℂ] cubicThetaFiniteEnergySections where
  toFun := cubicThetaPrimeCubeHeckeFinite hp
  map_add' F G := by
    apply Subtype.ext
    exact cubicThetaPrimeCubeHecke_add hp F.val G.val
  map_smul' c F := by
    apply Subtype.ext
    exact cubicThetaPrimeCubeHecke_smul hp c F.val

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeHeckeEnergyOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.instMeasurableSpace
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

local instance cubicThetaCubeFinite_addGroup : AddCommGroup cubicThetaFiniteEnergySections :=
  Module.addCommMonoidToAddCommGroup ℂ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPointC1Section
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The auxiliary C1 coordinates retain the literal automorphic section
and its previously constructed gradient. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaSectionPointC1 (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) :
    cubicThetaPointC1 := ⟨F.val,hF⟩

lemma cubicThetaSectionPointC1_gradient (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (x : CubicThetaPoint) :
    cubicThetaPointC1Gradient x (cubicThetaSectionPointC1 F hF)=cubicThetaSectionGradient F x := by
  ext i
  simp only [cubicThetaPointC1Gradient,cubicThetaSectionPointC1,cubicThetaTangentValues,
    cubicThetaSectionGradient,cubicThetaSectionDifferential,ContinuousLinearMap.comp_apply]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionFiniteEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaInversionSection_c1 (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) :
    ContDiffOn ℝ 1 (cubicThetaSectionFunction (cubicThetaInversionSection F)) {y : ℂ × ℝ | 0<y.2} := by
  exact (cubicThetaPointC1Pullback (cubicThetaFullComplex cubicThetaFullInversion)
    (cubicThetaSectionPointC1 F hF)).property

lemma cubicThetaInversionPointC1 (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) :
    cubicThetaSectionPointC1 (cubicThetaInversionSection F) (cubicThetaInversionSection_c1 F hF)=
      cubicThetaPointC1Pullback (cubicThetaFullComplex cubicThetaFullInversion)
        (cubicThetaSectionPointC1 F hF) := rfl

lemma cubicThetaInversionSection_C1energy (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (x : CubicThetaPoint) :
    cubicThetaSectionEnergy (cubicThetaInversionSection F) x=
      cubicThetaSectionEnergy F (cubicThetaFullInversion • x) := by
  rw [←cubicThetaSectionGradient_norm_sq,←cubicThetaSectionGradient_norm_sq,
    ←cubicThetaSectionPointC1_gradient _ (cubicThetaInversionSection_c1 F hF),
    ←cubicThetaSectionPointC1_gradient _ hF,cubicThetaInversionPointC1,
    cubicThetaPointC1Pullback_gradient_norm]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionFiniteCompletion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric inversion on finite-energy sections agrees with the
already constructed involution on the completed global energy space. -/
noncomputable section
namespace CubicFirstMoment

local instance inversionFinite_addGroup : AddCommGroup cubicThetaFiniteEnergySections :=
  Module.addCommMonoidToAddCommGroup ℂ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteEnergyPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal domain formulas for both Hermitian pairings on actual
finite-energy sections. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaFiniteEnergyGradient_pairing (F G : cubicThetaFiniteEnergySections) :
    inner ℂ (cubicThetaFiniteEnergyGradient F) (cubicThetaFiniteEnergyGradient G)=
      ∫ x in cubicThetaFundamentalDomain,
        inner ℂ (cubicThetaSectionGradient F.val x) (cubicThetaSectionGradient G.val x)
          ∂cubicThetaPointMeasure := by
  change inner ℂ (F.property.2.2.toLp _) (G.property.2.2.toLp _)=_
  rw [cubicThetaC1Pairing_L2 F.val G.val F.property.1 G.property.1 F.property.2.2 G.property.2.2,
    cubicThetaQuotientMeasure]
  have he := integral_map_of_stronglyMeasurable
    (μ:=cubicThetaPointMeasure.restrict cubicThetaFundamentalDomain)
    cubicThetaQuotientMap_open.continuous.measurable
    (cubicThetaC1Pairing_continuous F.val G.val F.property.1 G.property.1).stronglyMeasurable
  simpa only [cubicThetaC1Pairing_apply F.val G.val F.property.1 G.property.1] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPointC1Trace
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaPointC1Trace {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPointC1) : cubicThetaPointC1 := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  exact ∑ t : cubicThetaPrimeCubeTransversal p,
    star (cubicThetaKubotaValue t.val) • cubicThetaPointC1Pullback (cubicThetaPrincipalComplex t.val) F

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeAtkinPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubed-prime Atkin involution is self-adjoint for the actual
cover integral. No spectral or residue identity is assumed. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeAtkinMatrix_eq {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeAtkinMatrix hp=
      cubicThetaInversionMatrix (cubicThetaPrimeSquareRoot (p^3))
        (cubicThetaPrimeSquareRoot_ne_zero (pow_ne_zero 3 hp.2.ne_zero)) := by
  rw [cubicThetaPrimeCubeAtkinMatrix,cubicThetaFullInversion_complex]
  apply Subtype.ext
  change (cubicThetaInversionMatrix 1 one_ne_zero : Matrix (Fin 2) (Fin 2) ℂ)*
      (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) : Matrix (Fin 2) (Fin 2) ℂ)=_
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicThetaInversionMatrix,cubicThetaPrimeDilation,Matrix.mul_apply,Fin.sum_univ_two]

lemma cubicThetaPrimeCubeAtkinPoint_involutive {p : Eisenstein} (hp : primaryPrime p)
    (x : CubicThetaPoint) :
    cubicThetaPrimeCubeAtkinMatrix hp • (cubicThetaPrimeCubeAtkinMatrix hp • x)=x := by
  apply Subtype.ext
  change cubicThetaMobius (cubicThetaPrimeCubeAtkinMatrix hp)
    (cubicThetaMobius (cubicThetaPrimeCubeAtkinMatrix hp) x.val)=x.val
  rw [cubicThetaPrimeCubeAtkinMatrix_eq,
    cubicThetaMobius_inversion _ (cubicThetaMobius_height_pos _ x.property),
    cubicThetaMobius_inversion _ x.property]
  exact cubicThetaInversion_involutive (cubicThetaPrimeSquareRoot_ne_zero (pow_ne_zero 3 hp.2.ne_zero)) x.property

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPointC1Pairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariance of actual gradient pairings and the Atkin adjoint identity
on the finite cubed-prime cover. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPointC1Atkin_covariance {p : Eisenstein} (hp : primaryPrime p)
    (G : cubicThetaPointC1)
    (hG : ∀ (g : cubicThetaPrimeIwahori (p^3)) x,
      G.val (g.val • x)=cubicThetaKubotaValue g.val*G.val x)
    (g : cubicThetaPrimeIwahori (p^3)) (x : CubicThetaPoint) :
    (cubicThetaPointC1Pullback (cubicThetaPrimeCubeAtkinMatrix hp) G).val (g.val • x)=
      cubicThetaKubotaValue g.val*(cubicThetaPointC1Pullback
        (cubicThetaPrimeCubeAtkinMatrix hp) G).val x := by
  change G.val (cubicThetaPrimeCubeAtkinMatrix hp • (g • x))=
    cubicThetaKubotaValue g.val*G.val (cubicThetaPrimeCubeAtkinMatrix hp • x)
  rw [cubicThetaPrimeCubeAtkinPoint_intertwines]
  change G.val ((cubicThetaPrimeCubeAtkinConjugate hp g).val •
    (cubicThetaPrimeCubeAtkinMatrix hp • x))=_
  rw [hG,cubicThetaPrimeCubeAtkinConjugate_kubota]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPointC1Hecke
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaPointC1Hecke {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPointC1) : cubicThetaPointC1 :=
  cubicThetaPointC1Trace hp (cubicThetaPointC1Pullback
    (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)) F)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeReciprocalNormalizer
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The integral normalizer used to compare the cubed-prime correspondence
with its reciprocal. Its lower-left entry vanishes modulo p cubed. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaPrimeCubeReciprocalNormalizer {p : Eisenstein} (hp : primaryPrime p) : SL(2,Eisenstein) :=
  ((cubicThetaPrimeCubeWeyl hp).val*cubicThetaFullInversion)⁻¹

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootCoverDomain
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable fundamental domain for the cubic-scale fractional-root cover, obtained from
finitely many translates of the original proved fundamental domain. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootCoverDomain_measurable {p : Eisenstein} (hp : primaryPrime p) :
    MeasurableSet (cubicThetaPrimeCubeRootCoverDomain hp) := by
  apply MeasurableSet.iUnion
  intro t
  exact (Homeomorph.smul t.val).measurableEmbedding.measurableSet_image'
    cubicThetaFundamentalDomain_measurable

theorem cubicThetaPrimeCubeRootCoverDomain_unique {p : Eisenstein} (hp : primaryPrime p)
    (x : CubicThetaPoint) :
    ∃! g : cubicThetaPrimeCubeRootCoverGroup hp, g • x∈cubicThetaPrimeCubeRootCoverDomain hp := by
  obtain ⟨a,ha,hua⟩ := cubicThetaFundamentalDomain_unique x
  obtain ⟨⟨h,t⟩,he,hunique⟩ := (cubicThetaPrimeCubeRootTransversal_complement hp).existsUnique a⁻¹
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
    have hpair : ((k⁻¹,u) : cubicThetaPrimeCubeRootCoverGroup hp × cubicThetaPrimeCubeRootTransversal hp)=(h,t) := by
      apply hunique
      change k.val⁻¹*u.val=a⁻¹
      rw [←hya]
      group
    have hh : k⁻¹=h := congrArg Prod.fst hpair
    simpa only [inv_inv] using congrArg Inv.inv hh

theorem cubicThetaPrimeCubeRootCoverDomain_isFundamentalDomain {p : Eisenstein}
    (hp : primaryPrime p) (μ : Measure CubicThetaPoint) :
    IsFundamentalDomain (cubicThetaPrimeCubeRootCoverGroup hp) (cubicThetaPrimeCubeRootCoverDomain hp) μ :=
  IsFundamentalDomain.mk' (cubicThetaPrimeCubeRootCoverDomain_measurable hp).nullMeasurableSet
    (cubicThetaPrimeCubeRootCoverDomain_unique hp)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootDomainMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact global mass on the cubic root domain, without introducing
another quotient representative or any analytic input. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeRootDomain_global_map {p : Eisenstein} (hp : primaryPrime p) :
    (cubicThetaPointMeasure.restrict (cubicThetaPrimeCubeRootCoverDomain hp)).map
      cubicThetaQuotientMap=
        ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ≥0∞) • cubicThetaQuotientMeasure := by
  let : Fintype (cubicThetaPrimeCubeRootTransversal hp) := Fintype.ofFinite _
  have hdis : Pairwise (fun t u : cubicThetaPrimeCubeRootTransversal hp =>
      Disjoint ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain)
        ((fun x : CubicThetaPoint => u.val • x) '' cubicThetaFundamentalDomain)) := by
    intro t u htu
    exact cubicThetaFundamentalDomain_translates_disjoint (fun he => htu (Subtype.ext he))
  have hmeas (t : cubicThetaPrimeCubeRootTransversal hp) :
      MeasurableSet ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain) :=
    (Homeomorph.smul t.val).measurableEmbedding.measurableSet_image' cubicThetaFundamentalDomain_measurable
  change (cubicThetaPointMeasure.restrict (⋃ t : cubicThetaPrimeCubeRootTransversal hp,
    (fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain)).map cubicThetaQuotientMap=_
  rw [Measure.restrict_iUnion hdis hmeas,
    Measure.map_sum cubicThetaQuotientMap_open.continuous.measurable.aemeasurable]
  simp_rw [cubicThetaFundamentalDomain_translate_map]
  ext S hS
  rw [Measure.sum_apply _ hS,Measure.smul_apply,tsum_fintype,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul]
  rw [←Nat.card_eq_fintype_card,(cubicThetaPrimeCubeRootTransversal_complement hp).card_right]
  rfl

theorem cubicThetaPrimeCubeRootDomain_global_memLp {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    MemLp F.val 2 (cubicThetaPointMeasure.restrict (cubicThetaPrimeCubeRootCoverDomain hp)) := by
  apply (memLp_norm_iff F.val.continuous.aestronglyMeasurable).mp
  have hn := hF.norm
  simp only [cubicThetaSectionRepresentative_norm] at hn
  have hs := hn.smul_measure
    (by simp : ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ≥0∞)≠∞)
  rw [←cubicThetaPrimeCubeRootDomain_global_map hp] at hs
  have hc := hs.comp_of_map cubicThetaQuotientMap_open.continuous.measurable.aemeasurable
  simpa only [Function.comp_def,cubicThetaSectionNorm_apply] using hc

theorem cubicThetaPrimeCubeRootDomain_global_mass {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) :
    (∫ x in cubicThetaPrimeCubeRootCoverDomain hp,‖F.val x‖^2 ∂cubicThetaPointMeasure)=
      ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ)*
        ∫ q, (cubicThetaSectionNorm F q)^2 ∂cubicThetaQuotientMeasure := by
  have hi := integral_map_of_stronglyMeasurable
    (μ:=cubicThetaPointMeasure.restrict (cubicThetaPrimeCubeRootCoverDomain hp))
    cubicThetaQuotientMap_open.continuous.measurable
    ((cubicThetaSectionNorm_continuous F).pow 2).stronglyMeasurable
  simp only [Pi.pow_apply,cubicThetaSectionNorm_apply] at hi
  rw [cubicThetaPrimeCubeRootDomain_global_map hp,integral_smul_measure] at hi
  simpa only [ENNReal.toReal_natCast,smul_eq_mul] using hi.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootMassTransport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fractional translations preserve the literal finite-domain mass
and square integrability of cubic-scale automorphic sections. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootImage_fundamental {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) :
    IsFundamentalDomain (cubicThetaPrimeCubeRootCoverGroup hp)
      ((fun y : CubicThetaPoint => cubicThetaPrimeCubeRootElement hp x • y) ''
        cubicThetaPrimeCubeRootCoverDomain hp) cubicThetaPointMeasure := by
  apply (cubicThetaPrimeCubeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).image_of_equiv
    (Homeomorph.smul (cubicThetaPrimeCubeRootElement hp x)).toEquiv
    (measurePreserving_smul (cubicThetaPrimeCubeRootElement hp x)⁻¹
      cubicThetaPointMeasure).quasiMeasurePreserving
    (cubicThetaPrimeCubeRootAutomorphism hp (-x)).toEquiv
  intro g y
  change cubicThetaPrimeCubeRootElement hp x • ((cubicThetaPrimeCubeRootConjugate hp (-x) g).val • y)=
    g.val • (cubicThetaPrimeCubeRootElement hp x • y)
  rw [cubicThetaPrimeCubeRootPoint_intertwines,←cubicThetaPrimeCubeRootConjugate_add,
    add_neg_cancel,cubicThetaPrimeCubeRootConjugate_zero]

theorem cubicThetaPrimeCubeRootSectionTranslate_mass {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaPrimeCubeRootSections p) :
    (∫ y in cubicThetaPrimeCubeRootCoverDomain hp,
      ‖(cubicThetaPrimeCubeRootSectionTranslate hp x F).val y‖^2 ∂cubicThetaPointMeasure)=
        ∫ y in cubicThetaPrimeCubeRootCoverDomain hp,‖F.val y‖^2 ∂cubicThetaPointMeasure := by
  have hi := (cubicThetaPrimeCubeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).setIntegral_eq
    (f:=fun y : CubicThetaPoint => ‖F.val y‖^2)
    (cubicThetaPrimeCubeRootImage_fundamental hp x) (cubicThetaPrimeCubeRootSection_norm_invariant hp F)
  have hc := (measurePreserving_smul (cubicThetaPrimeCubeRootElement hp x) cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul (cubicThetaPrimeCubeRootElement hp x))
      (fun y => ‖F.val y‖^2) (cubicThetaPrimeCubeRootCoverDomain hp)
  exact (hi.trans hc).symm

theorem cubicThetaPrimeCubeRootSectionTranslate_memLp {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaPrimeCubeRootSections p)
    (hF : MemLp F.val 2 (cubicThetaPointMeasure.restrict (cubicThetaPrimeCubeRootCoverDomain hp))) :
    MemLp (cubicThetaPrimeCubeRootSectionTranslate hp x F).val 2
      (cubicThetaPointMeasure.restrict (cubicThetaPrimeCubeRootCoverDomain hp)) := by
  have hf := (memLp_two_iff_integrable_sq_norm F.val.continuous.aestronglyMeasurable).mp hF
  have hi := (cubicThetaPrimeCubeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).integrableOn_iff
    (f:=fun y : CubicThetaPoint => ‖F.val y‖^2)
    (cubicThetaPrimeCubeRootImage_fundamental hp x) (cubicThetaPrimeCubeRootSection_norm_invariant hp F)
  have hImage := hi.mp hf
  apply (memLp_two_iff_integrable_sq_norm
    (cubicThetaPrimeCubeRootSectionTranslate hp x F).val.continuous.aestronglyMeasurable).mpr
  exact ((measurePreserving_smul (cubicThetaPrimeCubeRootElement hp x) cubicThetaPointMeasure).integrableOn_image
    (measurableEmbedding_const_smul (cubicThetaPrimeCubeRootElement hp x))).mp hImage

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square-integrable cubic-root sections on the actual finite domain.
The finite translation action has exactly the original L2 norm. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

def cubicThetaPrimeCubeRootFiniteValue {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeRootFiniteSections hp →ₗ[ℂ] CubicThetaPrimeCubeRootL2 hp where
  toFun F := F.property.toLp _
  map_add' F G := MemLp.toLp_add F.property G.property
  map_smul' c F := MemLp.toLp_const_smul c F.property

lemma cubicThetaPrimeCubeRootSectionL2_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    ‖cubicThetaPrimeCubeRootFiniteValue hp F‖^2=
      ∫ x in cubicThetaPrimeCubeRootCoverDomain hp,‖F.val.val x‖^2 ∂cubicThetaPointMeasure := by
  change ‖F.property.toLp F.val.val‖^2=_
  rw [cubicTheta_l2_norm_sq_measure]
  apply integral_congr_ae
  filter_upwards [F.property.coeFn_toLp] with x hx
  rw [hx]

def cubicThetaPrimeCubeRootFiniteTranslate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) : cubicThetaPrimeCubeRootFiniteSections hp →ₗ[ℂ]
      cubicThetaPrimeCubeRootFiniteSections hp where
  toFun F := ⟨cubicThetaPrimeCubeRootSectionTranslate hp x F.val,
    cubicThetaPrimeCubeRootSectionTranslate_memLp hp x F.val F.property⟩
  map_add' _F _G := rfl
  map_smul' _c _F := rfl

lemma cubicThetaPrimeCubeRootFiniteTranslate_norm {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    ‖cubicThetaPrimeCubeRootFiniteValue hp (cubicThetaPrimeCubeRootFiniteTranslate hp x F)‖=
      ‖cubicThetaPrimeCubeRootFiniteValue hp F‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  rw [cubicThetaPrimeCubeRootSectionL2_norm_sq,cubicThetaPrimeCubeRootSectionL2_norm_sq]
  exact cubicThetaPrimeCubeRootSectionTranslate_mass hp x F.val

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootAutomorphicL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Completion of the actual finite-mass sections on the root cover.
Its fractional translations extend isometrically to this space. -/
noncomputable section
open Topology
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.cubeRootFiniteSections_addCommGroup
def cubicThetaPrimeCubeRootAutomorphicL2 {p : Eisenstein} (hp : primaryPrime p) :
    Submodule ℂ (CubicThetaPrimeCubeRootL2 hp) := (cubicThetaPrimeCubeRootFiniteValue hp).range.topologicalClosure

instance cubicThetaPrimeCubeRootAutomorphicL2_complete {p : Eisenstein} (hp : primaryPrime p) :
    CompleteSpace (cubicThetaPrimeCubeRootAutomorphicL2 hp) :=
  (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

def cubicThetaPrimeCubeRootFiniteEmbedding {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeRootFiniteSections hp →ₗ[ℂ] cubicThetaPrimeCubeRootAutomorphicL2 hp :=
  (cubicThetaPrimeCubeRootFiniteValue hp).codRestrict (cubicThetaPrimeCubeRootAutomorphicL2 hp)
    (fun F => Submodule.le_topologicalClosure _ ⟨F,rfl⟩)

lemma cubicThetaPrimeCubeRootFiniteEmbedding_dense {p : Eisenstein} (hp : primaryPrime p) :
    DenseRange (cubicThetaPrimeCubeRootFiniteEmbedding hp) := by
  intro u
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have he : Subtype.val '' Set.range (cubicThetaPrimeCubeRootFiniteEmbedding hp)=
      Set.range (cubicThetaPrimeCubeRootFiniteValue hp) := by
    ext y
    constructor
    · rintro ⟨v,⟨F,rfl⟩,rfl⟩
      exact ⟨F,rfl⟩
    · rintro ⟨F,rfl⟩
      exact ⟨cubicThetaPrimeCubeRootFiniteEmbedding hp F,⟨F,rfl⟩,rfl⟩
  rw [he]
  exact u.property

def cubicThetaPrimeCubeRootTranslateL2 {p : Eisenstein} (hp : primaryPrime p) (x : Eisenstein) :
    cubicThetaPrimeCubeRootAutomorphicL2 hp →ₗᵢ[ℂ] cubicThetaPrimeCubeRootAutomorphicL2 hp :=
  ((cubicThetaPrimeCubeRootFiniteEmbedding hp).comp (cubicThetaPrimeCubeRootFiniteTranslate hp x)).extendOfIsometry
    (cubicThetaPrimeCubeRootFiniteEmbedding_dense hp) (cubicThetaPrimeCubeRootFiniteTranslate_norm hp x)

lemma cubicThetaPrimeCubeRootTranslateL2_finite {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    cubicThetaPrimeCubeRootTranslateL2 hp x (cubicThetaPrimeCubeRootFiniteEmbedding hp F)=
      cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootFiniteTranslate hp x F) :=
  LinearMap.extendOfIsometry_eq _ _ _ F

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootHeckeCover
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual intermediate cover from the cubic root subgroup to
Iwahori(p cubed), needed to transport the cubed-prime trace pairing. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootHeckeDomain_measurable {p : Eisenstein} (hp : primaryPrime p) :
    MeasurableSet (cubicThetaPrimeCubeRootHeckeDomain hp) := by
  apply MeasurableSet.iUnion
  intro t
  exact (Homeomorph.smul t.val).measurableEmbedding.measurableSet_image'
    (cubicThetaPrimeCubeCoverDomain_measurable hp)

theorem cubicThetaPrimeCubeRootHeckeDomain_unique {p : Eisenstein} (hp : primaryPrime p)
    (x : CubicThetaPoint) :
    ∃! g : cubicThetaPrimeCubeRootHeckeSubgroup hp, g • x∈cubicThetaPrimeCubeRootHeckeDomain hp := by
  obtain ⟨a,ha,hua⟩ := cubicThetaPrimeCubeCoverDomain_unique p x
  obtain ⟨⟨h,t⟩,he,hunique⟩ := (cubicThetaPrimeCubeRootHeckeTransversal_complement hp).existsUnique a⁻¹
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
      change u.val⁻¹ • (k • x)∈(cubicThetaPrimeCubeCoverDomain p)
      rw [←hky,inv_smul_smul]
      exact hy
    have hpair : ((k⁻¹,u) : cubicThetaPrimeCubeRootHeckeSubgroup hp × cubicThetaPrimeCubeRootHeckeTransversal hp)=(h,t) := by
      apply hunique
      change k.val⁻¹*u.val=a⁻¹
      rw [←hya]
      group
    have hh : k⁻¹=h := congrArg Prod.fst hpair
    simpa only [inv_inv] using congrArg Inv.inv hh

theorem cubicThetaPrimeCubeRootHeckeDomain_root_fundamental {p : Eisenstein}
    (hp : primaryPrime p) (μ : Measure CubicThetaPoint) :
    IsFundamentalDomain (cubicThetaPrimeCubeRootCoverGroup hp)
      (cubicThetaPrimeCubeRootHeckeDomain hp) μ := by
  apply IsFundamentalDomain.mk' (cubicThetaPrimeCubeRootHeckeDomain_measurable hp).nullMeasurableSet
  intro x
  obtain ⟨k,hk,huniq⟩ := cubicThetaPrimeCubeRootHeckeDomain_unique hp x
  refine ⟨cubicThetaPrimeCubeRootHeckeSubgroupEquiv hp k,hk,?_⟩
  intro g hg
  have he := huniq ((cubicThetaPrimeCubeRootHeckeSubgroupEquiv hp).symm g) hg
  have hf := congrArg (cubicThetaPrimeCubeRootHeckeSubgroupEquiv hp) he
  simpa only [MulEquiv.apply_symm_apply] using hf


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootHeckeIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite-index integral transport to the actual cubic root domain.
The statement is used for real masses and complex pairings alike. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootHecke_disjoint {p : Eisenstein} (hp : primaryPrime p) :
    Pairwise (fun t u : cubicThetaPrimeCubeRootHeckeTransversal hp =>
      Disjoint ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaPrimeCubeCoverDomain p)
        ((fun x : CubicThetaPoint => u.val • x) '' cubicThetaPrimeCubeCoverDomain p)) := by
  intro t u htu
  apply Set.disjoint_left.mpr
  rintro x ⟨a,ha,hga⟩ ⟨b,hb,hgb⟩
  dsimp only at hga hgb
  have hm : (u.val⁻¹*t.val) • a=b := by rw [mul_smul,hga,←hgb,inv_smul_smul]
  have he : u.val⁻¹*t.val=1 := (cubicThetaPrimeCubeCoverDomain_unique p a).unique
    (by rwa [hm]) (by simpa using ha)
  exact htu (Subtype.ext (inv_mul_eq_one.mp he).symm)

section Integral
variable {E : Type*} [NormedAddCommGroup E]

lemma cubicThetaPrimeCubeRootHecke_relative_integrable {p : Eisenstein} (hp : primaryPrime p)
    {f : CubicThetaPoint → E}
    (hf : IntegrableOn f (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure)
    (hi : ∀ (g : cubicThetaPrimeIwahori (p^3)) x,f (g • x)=f x) :
    IntegrableOn f (cubicThetaPrimeCubeRootHeckeDomain hp) cubicThetaPointMeasure := by
  apply integrableOn_iUnion_of_summable_integral_norm
  · intro t
    apply ((measurePreserving_smul t.val cubicThetaPointMeasure).integrableOn_image
      (measurableEmbedding_const_smul t.val)).mpr
    simpa only [Function.comp_def,hi] using hf
  · exact Summable.of_finite

lemma cubicThetaPrimeCubeRootHecke_integrable {p : Eisenstein} (hp : primaryPrime p)
    {f : CubicThetaPoint → E}
    (hf : IntegrableOn f (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure)
    (hi : ∀ (g : cubicThetaPrimeIwahori (p^3)) x,f (g • x)=f x) :
    IntegrableOn f (cubicThetaPrimeCubeRootCoverDomain hp) cubicThetaPointMeasure := by
  have hk (g : cubicThetaPrimeCubeRootCoverGroup hp) (x : CubicThetaPoint) : f (g • x)=f x :=
    hi ⟨g.val,cubicThetaPrimeCubeRoot_le_hecke hp g.property⟩ x
  exact ((cubicThetaPrimeCubeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).integrableOn_iff
    (cubicThetaPrimeCubeRootHeckeDomain_root_fundamental hp cubicThetaPointMeasure) hk).mpr
    (cubicThetaPrimeCubeRootHecke_relative_integrable hp hf hi)

theorem cubicThetaPrimeCubeRootHecke_integral {p : Eisenstein} (hp : primaryPrime p)
    [NormedSpace ℝ E]
    {f : CubicThetaPoint → E}
    (hf : IntegrableOn f (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure)
    (hi : ∀ (g : cubicThetaPrimeIwahori (p^3)) x,f (g • x)=f x) :
    (∫ x in cubicThetaPrimeCubeRootCoverDomain hp,f x ∂cubicThetaPointMeasure)=
      ((cubicThetaPrimeCubeRootHeckeSubgroup hp).index:ℝ) •
        ∫ x in cubicThetaPrimeCubeCoverDomain p,f x ∂cubicThetaPointMeasure := by
  let : Fintype (cubicThetaPrimeCubeRootHeckeTransversal hp) := Fintype.ofFinite _
  have hk (g : cubicThetaPrimeCubeRootCoverGroup hp) (x : CubicThetaPoint) : f (g • x)=f x :=
    hi ⟨g.val,cubicThetaPrimeCubeRoot_le_hecke hp g.property⟩ x
  rw [(cubicThetaPrimeCubeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).setIntegral_eq
    (cubicThetaPrimeCubeRootHeckeDomain_root_fundamental hp cubicThetaPointMeasure) hk]
  have hmeas (t : cubicThetaPrimeCubeRootHeckeTransversal hp) :
      MeasurableSet ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaPrimeCubeCoverDomain p) :=
    (measurableEmbedding_const_smul t.val).measurableSet_image'
      (cubicThetaPrimeCubeCoverDomain_measurable hp)
  have hint (t : cubicThetaPrimeCubeRootHeckeTransversal hp) :
      IntegrableOn f ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaPrimeCubeCoverDomain p)
        cubicThetaPointMeasure := by
    apply ((measurePreserving_smul t.val cubicThetaPointMeasure).integrableOn_image
      (measurableEmbedding_const_smul t.val)).mpr
    simpa only [Function.comp_def,hi] using hf
  change (∫ x in ⋃ t : cubicThetaPrimeCubeRootHeckeTransversal hp,
    (fun y : CubicThetaPoint => t.val • y) '' cubicThetaPrimeCubeCoverDomain p,f x
      ∂cubicThetaPointMeasure)=_
  rw [integral_iUnion_fintype hmeas (cubicThetaPrimeCubeRootHecke_disjoint hp) hint]
  have ht (t : cubicThetaPrimeCubeRootHeckeTransversal hp) :
      (∫ x in (fun y : CubicThetaPoint => t.val • y) '' cubicThetaPrimeCubeCoverDomain p,
        f x ∂cubicThetaPointMeasure)=∫ x in cubicThetaPrimeCubeCoverDomain p,f x ∂cubicThetaPointMeasure := by
    rw [(measurePreserving_smul t.val cubicThetaPointMeasure).setIntegral_image_emb
      (measurableEmbedding_const_smul t.val) f (cubicThetaPrimeCubeCoverDomain p)]
    simp only [hi]
  simp only [ht,Finset.sum_const,Finset.card_univ]
  rw [←Nat.card_eq_fintype_card,(cubicThetaPrimeCubeRootHeckeTransversal_complement hp).card_right,
    Nat.cast_smul_eq_nsmul ℝ]

end Integral
end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootLiftL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
def cubicThetaPrimeCubeRootSmoothRestriction {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaSmoothTests →ₗ[ℂ] cubicThetaPrimeCubeRootFiniteSections hp where
  toFun F := ⟨cubicThetaPrimeRootSectionRestrict F.val,
    cubicThetaPrimeCubeRootDomain_global_memLp hp F.val (cubicThetaSectionRepresentative_memLp F)⟩
  map_add' _F _G := rfl
  map_smul' _c _F := rfl

def cubicThetaPrimeCubeRootNormalizedRestriction {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaSmoothTests →ₗ[ℂ] cubicThetaPrimeCubeRootAutomorphicL2 hp :=
  ((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ))⁻¹:ℂ) •
    ((cubicThetaPrimeCubeRootFiniteEmbedding hp).comp (cubicThetaPrimeCubeRootSmoothRestriction hp))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootDilation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The once-cubic dilation is an actual square-integrable section on
K3. Its finite-domain norm has the original global covering degree. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootDilation_integrable {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    IntegrableOn (fun x => ‖(cubicThetaPrimeCubeDilationSection hp F).val x‖^2)
      (cubicThetaPrimeCubeRootCoverDomain hp) cubicThetaPointMeasure :=
  cubicThetaPrimeCubeRootHecke_integrable hp (cubicThetaPrimeCubeDilation_integrable hp F hF)
    (cubicThetaPrimeCubeSection_norm_invariant p (cubicThetaPrimeCubeDilationSection hp F))

theorem cubicThetaPrimeCubeRootDilation_mass {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    (∫ x in cubicThetaPrimeCubeRootCoverDomain hp,
      ‖(cubicThetaPrimeCubeDilationSection hp F).val x‖^2 ∂cubicThetaPointMeasure)=
      ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ)*
        ∫ x in cubicThetaFundamentalDomain,‖F.val x‖^2 ∂cubicThetaPointMeasure := by
  rw [cubicThetaPrimeCubeRootHecke_integral hp
    (cubicThetaPrimeCubeDilation_integrable hp F hF)
    (cubicThetaPrimeCubeSection_norm_invariant p (cubicThetaPrimeCubeDilationSection hp F)),
    smul_eq_mul,cubicThetaPrimeCubeDilation_integral_norm hp F hF,←mul_assoc,←Nat.cast_mul,
    cubicThetaPrimeCubeRootHecke_index hp]

def cubicThetaPrimeCubeRootSmoothDilation {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaSmoothTests →ₗ[ℂ] cubicThetaPrimeCubeRootFiniteSections hp where
  toFun F := ⟨cubicThetaPrimeCubeRootHeckeRestriction hp (cubicThetaPrimeCubeDilationSection hp F.val),by
    apply (memLp_two_iff_integrable_sq_norm
      (cubicThetaPrimeCubeRootHeckeRestriction hp
        (cubicThetaPrimeCubeDilationSection hp F.val)).val.continuous.aestronglyMeasurable).mpr
    exact cubicThetaPrimeCubeRootDilation_integrable hp F.val
      (cubicThetaPrimeCubeFinite_mass_domain (cubicThetaSmoothToFiniteEnergy F))⟩
  map_add' _F _G := rfl
  map_smul' _c _F := rfl

lemma cubicThetaPrimeCubeRootSmoothDilation_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    ‖cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootSmoothDilation hp F)‖^2=
      ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ)*‖cubicThetaGlobalMassClosure F‖^2 := by
  change ‖cubicThetaPrimeCubeRootFiniteValue hp (cubicThetaPrimeCubeRootSmoothDilation hp F)‖^2=_
  rw [cubicThetaPrimeCubeRootSectionL2_norm_sq]
  change (∫ x in cubicThetaPrimeCubeRootCoverDomain hp,
    ‖(cubicThetaPrimeCubeDilationSection hp F.val).val x‖^2 ∂cubicThetaPointMeasure)=_
  rw [cubicThetaPrimeCubeRootDilation_mass hp F.val
    (cubicThetaPrimeCubeFinite_mass_domain (cubicThetaSmoothToFiniteEnergy F))]
  congr 1
  exact (cubicThetaFiniteEnergyValue_domain_norm_sq (cubicThetaSmoothToFiniteEnergy F)).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootL2Algebra
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal cubic-scale translations form the finite residue-group
action on the actual completed domain space. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootTranslateL2_add {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (u : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    cubicThetaPrimeCubeRootTranslateL2 hp (x+y) u=
      cubicThetaPrimeCubeRootTranslateL2 hp x (cubicThetaPrimeCubeRootTranslateL2 hp y u) := by
  refine (cubicThetaPrimeCubeRootFiniteEmbedding_dense hp).induction_on u
    (isClosed_eq (cubicThetaPrimeCubeRootTranslateL2 hp (x+y)).continuous
      ((cubicThetaPrimeCubeRootTranslateL2 hp x).continuous.comp
        (cubicThetaPrimeCubeRootTranslateL2 hp y).continuous)) ?_
  intro F
  rw [cubicThetaPrimeCubeRootTranslateL2_finite,cubicThetaPrimeCubeRootTranslateL2_finite,
    cubicThetaPrimeCubeRootTranslateL2_finite]
  apply congrArg (cubicThetaPrimeCubeRootFiniteEmbedding hp)
  apply Subtype.ext
  exact cubicThetaPrimeCubeRootSectionTranslate_add hp x y F.val

lemma cubicThetaPrimeCubeRootTranslateL2_zero {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaPrimeCubeRootAutomorphicL2 hp) : cubicThetaPrimeCubeRootTranslateL2 hp 0 u=u := by
  refine (cubicThetaPrimeCubeRootFiniteEmbedding_dense hp).induction_on u
    (isClosed_eq (cubicThetaPrimeCubeRootTranslateL2 hp 0).continuous continuous_id) ?_
  intro F
  rw [cubicThetaPrimeCubeRootTranslateL2_finite]
  apply congrArg (cubicThetaPrimeCubeRootFiniteEmbedding hp)
  apply Subtype.ext
  exact cubicThetaPrimeCubeRootSectionTranslate_zero hp F.val

lemma cubicThetaPrimeCubeRootTranslateL2_congr {p : Eisenstein} (hp : primaryPrime p)
    {x y : Eisenstein} (hxy : p^3∣x-y) (u : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    cubicThetaPrimeCubeRootTranslateL2 hp x u=cubicThetaPrimeCubeRootTranslateL2 hp y u := by
  refine (cubicThetaPrimeCubeRootFiniteEmbedding_dense hp).induction_on u
    (isClosed_eq (cubicThetaPrimeCubeRootTranslateL2 hp x).continuous
      (cubicThetaPrimeCubeRootTranslateL2 hp y).continuous) ?_
  intro F
  rw [cubicThetaPrimeCubeRootTranslateL2_finite,cubicThetaPrimeCubeRootTranslateL2_finite]
  apply congrArg (cubicThetaPrimeCubeRootFiniteEmbedding hp)
  apply Subtype.ext
  exact congrArg (fun T : cubicThetaPrimeCubeRootSections p ≃ₗ[ℂ] cubicThetaPrimeCubeRootSections p => T F.val)
    (cubicThetaPrimeCubeRootOperator_congr hp hxy)

def cubicThetaPrimeCubeRootResidueL2 {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues (p^3)) : cubicThetaPrimeCubeRootAutomorphicL2 hp →ₗᵢ[ℂ]
      cubicThetaPrimeCubeRootAutomorphicL2 hp :=
  cubicThetaPrimeCubeRootTranslateL2 hp (residueRepresentative (p^3) r)

lemma cubicThetaPrimeCubeRootResidueL2_mk {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (u : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    cubicThetaPrimeCubeRootResidueL2 hp (Ideal.Quotient.mk (modulus (p^3)) x) u=
      cubicThetaPrimeCubeRootTranslateL2 hp x u := by
  apply cubicThetaPrimeCubeRootTranslateL2_congr hp
  exact Ideal.mem_span_singleton.mp
    (Ideal.Quotient.eq.mp (residueRepresentative_spec (p^3) (Ideal.Quotient.mk (modulus (p^3)) x)))

lemma cubicThetaPrimeCubeRootResidueL2_add {p : Eisenstein} (hp : primaryPrime p)
    (r s : Residues (p^3)) (u : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    cubicThetaPrimeCubeRootResidueL2 hp (r+s) u=
      cubicThetaPrimeCubeRootResidueL2 hp r (cubicThetaPrimeCubeRootResidueL2 hp s u) := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [←map_add,cubicThetaPrimeCubeRootResidueL2_mk,cubicThetaPrimeCubeRootResidueL2_mk,
    cubicThetaPrimeCubeRootResidueL2_mk,cubicThetaPrimeCubeRootTranslateL2_add]

lemma cubicThetaPrimeCubeRootResidueL2_zero {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaPrimeCubeRootAutomorphicL2 hp) : cubicThetaPrimeCubeRootResidueL2 hp 0 u=u := by
  rw [←map_zero (Ideal.Quotient.mk (modulus (p^3))),cubicThetaPrimeCubeRootResidueL2_mk,
    cubicThetaPrimeCubeRootTranslateL2_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite Fourier averages at the cube modulus, on sections
and on their completed domain space. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaPrimeCubeRootFourierL2 {p : Eisenstein} (hp : primaryPrime p)
    (k : Residues (p^3)) : cubicThetaPrimeCubeRootAutomorphicL2 hp →L[ℂ]
      cubicThetaPrimeCubeRootAutomorphicL2 hp := by
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Fintype (Residues (p^3)) := Fintype.ofFinite _
  exact (norm (p^3):ℂ)⁻¹ • ∑ r : Residues (p^3),
    star (residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero) (k*r)) •
      (cubicThetaPrimeCubeRootResidueL2 hp r).toContinuousLinearMap

lemma cubicThetaPrimeCubeRootFourierL2_apply {p : Eisenstein} (hp : primaryPrime p)
    [Fintype (Residues (p^3))] (k : Residues (p^3))
    (u : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    cubicThetaPrimeCubeRootFourierL2 hp k u=(norm (p^3):ℂ)⁻¹ • ∑ r : Residues (p^3),
      star (residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero) (k*r)) •
        cubicThetaPrimeCubeRootResidueL2 hp r u := by
  classical
  simp only [cubicThetaPrimeCubeRootFourierL2,smul_apply,sum_apply,
    LinearIsometry.coe_toContinuousLinearMap]
  congr 1
  apply Finset.sum_congr
  · ext r
    simp
  · intro r _
    rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootFourierProducts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonal projection algebra for the actual cubic-scale finite action. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootFourierL2_translate {p : Eisenstein} (hp : primaryPrime p)
    (k s : Residues (p^3)) (F : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    cubicThetaPrimeCubeRootFourierL2 hp k (cubicThetaPrimeCubeRootResidueL2 hp s F)=
      residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero) (k*s) • cubicThetaPrimeCubeRootFourierL2 hp k F := by
  classical
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Fintype (Residues (p^3)) := Fintype.ofFinite _
  let ψ := residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero)
  have hc (r : Residues (p^3)) : star (ψ (k*r))=ψ (k*s)*star (ψ (k*(r+s))) := by
    simp only [ψ,cubicThetaResidueFourier_star]
    rw [←AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [cubicThetaPrimeCubeRootFourierL2_apply]
  simp_rw [←cubicThetaPrimeCubeRootResidueL2_add]
  calc
    _ = (norm (p^3):ℂ)⁻¹ • ∑ r : Residues (p^3),ψ (k*s) •
        (star (ψ (k*(r+s))) • cubicThetaPrimeCubeRootResidueL2 hp (r+s) F) := by
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      rw [smul_smul,←hc r]
    _ = ψ (k*s) • ((norm (p^3):ℂ)⁻¹ • ∑ r : Residues (p^3),
        star (ψ (k*(r+s))) • cubicThetaPrimeCubeRootResidueL2 hp (r+s) F) := by
      rw [←Finset.smul_sum,smul_comm]
    _ = _ := by
      have he := Equiv.sum_comp (Equiv.addRight s)
        (fun r => star (ψ (k*r)) • cubicThetaPrimeCubeRootResidueL2 hp r F)
      change (∑ r : Residues (p^3),star (ψ (k*(r+s))) • cubicThetaPrimeCubeRootResidueL2 hp (r+s) F)=
        ∑ r : Residues (p^3),star (ψ (k*r)) • cubicThetaPrimeCubeRootResidueL2 hp r F at he
      rw [he,cubicThetaPrimeCubeRootFourierL2_apply]

lemma cubicThetaPrimeCubeRootFourierL2_commute {p : Eisenstein} (hp : primaryPrime p)
    (k s : Residues (p^3)) (F : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    cubicThetaPrimeCubeRootResidueL2 hp s (cubicThetaPrimeCubeRootFourierL2 hp k F)=
      cubicThetaPrimeCubeRootFourierL2 hp k (cubicThetaPrimeCubeRootResidueL2 hp s F) := by
  classical
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Fintype (Residues (p^3)) := Fintype.ofFinite _
  have hc (r : Residues (p^3)) :
      cubicThetaPrimeCubeRootResidueL2 hp s (cubicThetaPrimeCubeRootResidueL2 hp r F)=
        cubicThetaPrimeCubeRootResidueL2 hp r (cubicThetaPrimeCubeRootResidueL2 hp s F) := by
    rw [←cubicThetaPrimeCubeRootResidueL2_add,add_comm s r,cubicThetaPrimeCubeRootResidueL2_add]
  simp only [cubicThetaPrimeCubeRootFourierL2_apply,map_smul,map_sum,hc]

lemma cubicThetaPrimeCubeRootFourierL2_eigen {p : Eisenstein} (hp : primaryPrime p)
    (k s : Residues (p^3)) (F : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    cubicThetaPrimeCubeRootResidueL2 hp s (cubicThetaPrimeCubeRootFourierL2 hp k F)=
      residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero) (k*s) • cubicThetaPrimeCubeRootFourierL2 hp k F := by
  rw [cubicThetaPrimeCubeRootFourierL2_commute,cubicThetaPrimeCubeRootFourierL2_translate]


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootFourierNorm
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The norm of the actual cubic-scale Fourier projection is the
Fourier transform of its translation correlations. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootResidueL2_adjoint {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues (p^3)) (u v : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    inner ℂ (cubicThetaPrimeCubeRootResidueL2 hp r u) v=
      inner ℂ u (cubicThetaPrimeCubeRootResidueL2 hp (-r) v) := by
  have he := (cubicThetaPrimeCubeRootResidueL2 hp r).inner_map_map u
    (cubicThetaPrimeCubeRootResidueL2 hp (-r) v)
  rw [←cubicThetaPrimeCubeRootResidueL2_add,add_neg_cancel,
    cubicThetaPrimeCubeRootResidueL2_zero] at he
  exact he

lemma cubicThetaPrimeCubeRootFourierL2_pair_projection {p : Eisenstein} (hp : primaryPrime p)
    (k : Residues (p^3)) (u v : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    inner ℂ (cubicThetaPrimeCubeRootFourierL2 hp k u)
      (cubicThetaPrimeCubeRootFourierL2 hp k v)=
    inner ℂ u (cubicThetaPrimeCubeRootFourierL2 hp k v) := by
  classical
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Fintype (Residues (p^3)) := Fintype.ofFinite _
  let ψ := residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero)
  let w := cubicThetaPrimeCubeRootFourierL2 hp k v
  have hterm (r : Residues (p^3)) :
      inner ℂ (star (ψ (k*r)) • cubicThetaPrimeCubeRootResidueL2 hp r u) w=
        inner ℂ u w := by
    rw [inner_smul_left (𝕜:=ℂ) (E:=cubicThetaPrimeCubeRootAutomorphicL2 hp),starRingEnd_apply,star_star,
      cubicThetaPrimeCubeRootResidueL2_adjoint]
    change ψ (k*r)*inner ℂ u (cubicThetaPrimeCubeRootResidueL2 hp (-r)
      (cubicThetaPrimeCubeRootFourierL2 hp k v))=inner ℂ u w
    rw [cubicThetaPrimeCubeRootFourierL2_eigen,
      inner_smul_right (𝕜:=ℂ) (E:=cubicThetaPrimeCubeRootAutomorphicL2 hp),←mul_assoc]
    have hc : ψ (k*r)*ψ (k*(-r))=1 := by
      rw [←AddChar.map_add_eq_mul,←mul_add,add_neg_cancel,mul_zero,AddChar.map_zero_eq_one]
    rw [hc,one_mul]
  have hcard : (Fintype.card (Residues (p^3)):ℂ)=(norm (p^3):ℂ) := by
    rw [←Nat.card_eq_fintype_card,residues_card (pow_ne_zero 3 hp.2.ne_zero)]
    simpa only [Complex.ofReal_natCast] using congrArg Complex.ofReal (normNat_cast (p^3))
  change inner ℂ (cubicThetaPrimeCubeRootFourierL2 hp k u) w=inner ℂ u w
  rw [cubicThetaPrimeCubeRootFourierL2_apply,
    inner_smul_left (𝕜:=ℂ) (E:=cubicThetaPrimeCubeRootAutomorphicL2 hp),sum_inner]
  change star ((norm (p^3):ℂ)⁻¹)*(∑ r : Residues (p^3),
    inner ℂ (star (ψ (k*r)) • cubicThetaPrimeCubeRootResidueL2 hp r u) w)=_
  have hs : star ((norm (p^3):ℂ)⁻¹)=(norm (p^3):ℂ)⁻¹ := by
    have hn : star (norm (p^3):ℂ)=(norm (p^3):ℂ) :=
      (congrArg (fun z : ℂ => star z) hcard).symm.trans ((star_natCast _).trans hcard)
    exact (star_inv₀ (norm (p^3):ℂ)).trans (congrArg (fun z : ℂ => z⁻¹) hn)
  rw [hs]
  simp only [hterm,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hcard]
  rw [inv_mul_cancel_left₀
    (Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero (pow_ne_zero 3 hp.2.ne_zero)).ne')]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootDilationL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized isometric cubic dilation of the actual global mass space
into the common arithmetic root cover. -/
noncomputable section
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.cubeRootDilation_smoothGroup
def cubicThetaPrimeCubeRootNormalizedDilation {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaSmoothTests →ₗ[ℂ] cubicThetaPrimeCubeRootAutomorphicL2 hp :=
  ((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ))⁻¹:ℂ) •
    ((cubicThetaPrimeCubeRootFiniteEmbedding hp).comp (cubicThetaPrimeCubeRootSmoothDilation hp))

lemma cubicThetaPrimeCubeRootNormalizedDilation_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    ‖cubicThetaPrimeCubeRootNormalizedDilation hp F‖=‖cubicThetaGlobalMassClosure F‖ := by
  let d : ℝ := (cubicThetaPrimeCubeRootCoverGroup hp).index
  have hd : 0<d := cubicThetaPrimeCubeRootCoverDegree_pos hp
  have hc : ‖((Real.sqrt d)⁻¹:ℂ)‖^2*d=1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,inv_pow,sq_abs,Real.sq_sqrt hd.le,
      inv_mul_cancel₀ hd.ne']
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  change ‖((Real.sqrt d)⁻¹:ℂ) •
    cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootSmoothDilation hp F)‖^2=_
  rw [norm_smul,mul_pow,cubicThetaPrimeCubeRootSmoothDilation_norm_sq]
  change ‖((Real.sqrt d)⁻¹:ℂ)‖^2*(d*‖cubicThetaGlobalMassClosure F‖^2)=_
  rw [←mul_assoc,hc,one_mul]

def cubicThetaPrimeCubeRootDilationL2 {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaAutomorphicL2 →ₗᵢ[ℂ] cubicThetaPrimeCubeRootAutomorphicL2 hp :=
  (cubicThetaPrimeCubeRootNormalizedDilation hp).extendOfIsometry
    cubicThetaGlobalMassClosure_dense (cubicThetaPrimeCubeRootNormalizedDilation_norm hp)

lemma cubicThetaPrimeCubeRootDilationL2_smooth {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaSmoothTests) :
    cubicThetaPrimeCubeRootDilationL2 hp (cubicThetaGlobalMassClosure F)=
      cubicThetaPrimeCubeRootNormalizedDilation hp F :=
  LinearMap.extendOfIsometry_eq _ _ _ F


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootDilationFixed
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaPrimeCubeRootFiniteDilation_translate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaSmoothTests) :
    cubicThetaPrimeCubeRootFiniteTranslate hp x (cubicThetaPrimeCubeRootSmoothDilation hp F)=
      cubicThetaPrimeCubeRootSmoothDilation hp F := by
  apply Subtype.ext
  exact cubicThetaPrimeCubeRootDilation_translate hp x F.val

theorem cubicThetaPrimeCubeRootDilationL2_translate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (u : cubicThetaAutomorphicL2) :
    cubicThetaPrimeCubeRootTranslateL2 hp x (cubicThetaPrimeCubeRootDilationL2 hp u)=
      cubicThetaPrimeCubeRootDilationL2 hp u := by
  refine cubicThetaGlobalMassClosure_dense.induction_on u
    (isClosed_eq ((cubicThetaPrimeCubeRootTranslateL2 hp x).continuous.comp
      (cubicThetaPrimeCubeRootDilationL2 hp).continuous) (cubicThetaPrimeCubeRootDilationL2 hp).continuous) ?_
  intro F
  simp only [cubicThetaPrimeCubeRootDilationL2_smooth,cubicThetaPrimeCubeRootNormalizedDilation,
    LinearMap.smul_apply,LinearMap.comp_apply,map_smul,cubicThetaPrimeCubeRootTranslateL2_finite,
    cubicThetaPrimeCubeRootFiniteDilation_translate]

theorem cubicThetaPrimeCubeRootDilationL2_fourier_zero {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaAutomorphicL2) :
    cubicThetaPrimeCubeRootFourierL2 hp 0 (cubicThetaPrimeCubeRootDilationL2 hp u)=
      cubicThetaPrimeCubeRootDilationL2 hp u := by
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Fintype (Residues (p^3)) := Fintype.ofFinite _
  have hcard : (Fintype.card (Residues (p^3)):ℂ)=(norm (p^3):ℂ) := by
    rw [←Nat.card_eq_fintype_card,residues_card (pow_ne_zero 3 hp.2.ne_zero)]
    simpa only [Complex.ofReal_natCast] using congrArg Complex.ofReal (normNat_cast (p^3))
  rw [cubicThetaPrimeCubeRootFourierL2_apply]
  simp only [zero_mul,AddChar.map_zero_eq_one,star_one,one_smul,
    cubicThetaPrimeCubeRootResidueL2,cubicThetaPrimeCubeRootDilationL2_translate,
    Finset.sum_const,Finset.card_univ]
  rw [←Nat.cast_smul_eq_nsmul ℂ,hcard,smul_smul,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero (pow_ne_zero 3 hp.2.ne_zero)).ne'),one_smul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeWeakLift
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite-cover trace transports the complete weak energy
equation to the prime cover, with all finite-cover test vectors allowed. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaGlobalEnergyPencil_pairing (z : ℂ) (u v : cubicThetaGlobalEnergySpace) :
    inner ℂ u (cubicThetaEnergyPencil z v)=inner ℂ u v-
      z*inner ℂ (cubicThetaGlobalInclusion u) (cubicThetaGlobalInclusion v) := by
  change inner ℂ u (v-z • cubicThetaGlobalInclusion.adjoint (cubicThetaGlobalInclusion v))=_
  rw [inner_sub_right,inner_smul_right (𝕜:=ℂ) (E:=cubicThetaGlobalEnergySpace),
    cubicThetaGlobalInclusion.adjoint_inner_right]

end CubicFirstMoment

end

end OAI
end


