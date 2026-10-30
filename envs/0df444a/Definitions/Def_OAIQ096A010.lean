-- Prove2me | Definitions.Def_OAIQ096A010
-- name    : OAIQ096A010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T03:35:46.696654+00:00
-- url     : https://prove2.me/theorems/602bdc93-cffa-49f1-b8ab-98dfe1c3d02a
-- title:
--   Definitions bundle OAIQ096A010 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 203 declarations of OpenAI's Lean: 169 definitions, 2 instances and 32 theorems. The definitions and types are `OAI.CubicFirstMoment.cubicThetaCuspCharacter`, `OAI.CubicFirstMoment.cubicThetaCuspStep`, `OAI.CubicFirstMoment.cubicThetaCuspStepMatrix`, `OAI.CubicFirstMoment.cubicThetaCuspStepValue`, `OAI.CubicFirstMoment.cubicThetaCuspTranslation`, `OAI.CubicFirstMoment.cubicThetaCuspTranslationMatrix`, `OAI.CubicFirstMoment.cubicThetaGaussianLinearConstant`, `OAI.CubicFirstMoment.cubicThetaGaussianPowerConstant`, `OAI.CubicFirstMoment.cubicThetaIntegerEmbedding`, `OAI.CubicFirstMoment.cubicThetaKubotaConjugate`, `OAI.CubicFirstMoment.cubicThetaLatticeGaussianTail`, `OAI.CubicFirstMoment.cubicThetaModularS`, `OAI.CubicFirstMoment.cubicThetaModularT`, `OAI.CubicFirstMoment.cubicThetaNonzeroFirstHeat`, `OAI.CubicFirstMoment.cubicThetaPrimaryNumerator`, `OAI.CubicFirstMoment.cubicThetaPrimeAdditiveGauss`, `OAI.CubicFirstMoment.cubicThetaRamanujan`, `OAI.CubicFirstMoment.cubicThetaResidueChar`, `OAI.CubicFirstMoment.cubicThetaRootProjector`, `OAI.CubicFirstMoment.cubicThetaScalarEisenstein`, `OAI.CubicFirstMoment.cubicThetaScalarGaussian`, `OAI.CubicFirstMoment.cubicThetaScalarGaussianReal`, `OAI.CubicFirstMoment.cubicThetaShiftedCuspGaussianRow`, `OAI.CubicFirstMoment.cubicThetaShiftedFrequencyTerm`, `OAI.CubicFirstMoment.cubicThetaShiftedGaussCoefficient`, `OAI.CubicFirstMoment.cubicThetaShiftedInvertedRowEquiv`, `OAI.CubicFirstMoment.cubicThetaShiftedResidueWeight`, `OAI.CubicFirstMoment.cubicThetaShiftedRowFourierCoefficient`, `OAI.CubicFirstMoment.cubicThetaShiftedRowFrequency`, `OAI.CubicFirstMoment.cubicThetaShiftedRowHeatScale`, `OAI.CubicFirstMoment.cubicThetaShiftedRowPhase`, `OAI.CubicFirstMoment.cubicThetaShiftedRowSeries`, `OAI.CubicFirstMoment.cubicThetaShiftedRowStep`, `OAI.CubicFirstMoment.cubicThetaShiftedRowTranslate`, `OAI.CubicFirstMoment.cubicThetaShiftedRowWeight`, `OAI.CubicFirstMoment.dispersionAbsoluteModel`, `OAI.CubicFirstMoment.distinguishedSmoothWeights`, `OAI.CubicFirstMoment.divisorCharacterMass`, `OAI.CubicFirstMoment.divisorDispersionVariance`, `OAI.CubicFirstMoment.eisensteinNormPolynomial` and 129 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `CubicGram_CubicOperator`, `CubicGram_InnerExtension`, `CubicGram_NormRecurrence`, `CubicGram_Reciprocity`, `CubicGram_SquarefreeGauss`, `CubicMoment_Angular_AngularCoprimeLattice`, `CubicMoment_Angular_AngularDyadicMoment`, `CubicMoment_Angular_AngularPrimaryLattice`, `CubicMoment_Angular_AngularPrimeCoordinateCollection`, `CubicMoment_Angular_AngularSquarefreeIdentity`, `CubicMoment_Angular_AngularSquarefreeLattice`, `CubicMoment_Estimates_BalancedFullRows`, `CubicMoment_Estimates_BilinearKernelIdentity`, `CubicMoment_Estimates_ComplexWeightedConvolution`, `CubicMoment_Estimates_ConductorNeighborhoods`, `CubicMoment_Estimates_CoordinateWeightedTuple`, `CubicMoment_Estimates_DispersionAbsoluteModel`, `CubicMoment_Estimates_DispersionPoisson`, `CubicMoment_Estimates_DivisorCharacterMass`, `CubicMoment_Estimates_DivisorDispersion`, `CubicMoment_Estimates_ExcludedPrimeInput`, `CubicMoment_Estimates_FarLogNormCells`, `CubicMoment_Estimates_FiniteCharacterMass`, `CubicMoment_Estimates_FullPrimeFactorization`, `CubicMoment_Estimates_FullSmoothFactor`, `CubicMoment_Estimates_HeckeDiskGrowth`, `CubicMoment_Estimates_HeckeNormalizedDisk`, `CubicMoment_Estimates_HeckeUniformGrowth`, `CubicMoment_Estimates_HeightBilinearValue`, `CubicMoment_Estimates_HeightCubeMass`, `CubicMoment_Estimates_HuxleyGaussianRows`, `CubicMoment_Estimates_HuxleyPhase`, `CubicMoment_Estimates_HuxleyResiduePoints`, `CubicMoment_Estimates_IdealDirichletBounds`, `CubicMoment_Estimates_IdealEulerSeries`, `CubicMoment_Estimates_IdealHeatTheta`, `CubicMoment_Estimates_IdealLogDerivativeTwist`, `CubicMoment_Estimates_LargeTupleCoordinateWeights`, `CubicMoment_Estimates_LargeTupleRestrictedWeights`, `CubicMoment_Estimates_LargeTupleWeightLengths`, `CubicMoment_Estimates_LargeTupleWeights`, `CubicMoment_Estimates_LateStopDivisor`, `CubicMoment_Estimates_LogNormCells`, `CubicMoment_Estimates_LogSmallTwist`, `CubicMoment_Estimates_LowCoreSupport`, `CubicMoment_Estimates_ModelPartialSummation`, `CubicMoment_Estimates_NearLogNormCells`, `CubicMoment_Estimates_NormCoprimeMellin`, `CubicMoment_Estimates_OrdinaryMixedSieve`, `CubicMoment_Estimates_PolynomialMeanValue`, `CubicMoment_Estimates_PrimaryHeckeCharacter`, `CubicMoment_Estimates_PrimeCoordinateDifference`, `CubicMoment_Estimates_PrimeDyadicReconstruction`, `CubicMoment_Estimates_PrimeIdealEulerExclusion`, `CubicMoment_Estimates_PrimeMellinTransfer`, `CubicMoment_Estimates_PrimeTailProductMellin`, `CubicMoment_Estimates_PrimeToThreeIdeals`, `CubicMoment_Estimates_PrimeTupleDecomposition`, `CubicMoment_Estimates_PrimeTupleFiber`, `CubicMoment_Estimates_PrimitiveResidueFourier`, `CubicMoment_Estimates_ResidueGaussianPoisson`, `CubicMoment_Estimates_ResidueHarmonicPoisson`, `CubicMoment_Estimates_ResidueThetaLattice`, `CubicMoment_Estimates_RoughRemainderArity`, `CubicMoment_Estimates_SemiprimeGaussTailAngularWeights`, `CubicMoment_Estimates_SemiprimeGaussTailWeights`, `CubicMoment_Estimates_SemiprimeSmoothWeights`, `CubicMoment_Estimates_ShortConvolutionExpansion`, `CubicMoment_Estimates_ShortConvolutionMoments`, `CubicMoment_Estimates_ShortFactorGram`, `CubicMoment_Estimates_ShortFactorUniform`, `CubicMoment_Estimates_ShortMoebius`, `CubicMoment_Estimates_ShortMoebiusProducts`, `CubicMoment_Estimates_ShortTupleMellin`, `CubicMoment_Estimates_ShortTuplePartition`, `CubicMoment_Estimates_SieveResidue`, `CubicMoment_Estimates_SievedDispersion`, `CubicMoment_Estimates_SievedModelAssembly`, `CubicMoment_Estimates_SmallPairParts`, `CubicMoment_Estimates_SmallPrimeParts`, `CubicMoment_Estimates_SmallTwistSmoothMoment`, `CubicMoment_Estimates_SparseFourthMoment`, `CubicMoment_Estimates_SparseLateSupport`, `CubicMoment_Estimates_SquarefreeMajorant`, `CubicMoment_Estimates_SquarefreeModelMass`, `CubicMoment_Estimates_StructuredConvolution`, `CubicMoment_Estimates_StructuredMeanValue`, `CubicMoment_Estimates_StructuredMomentTwists`, `CubicMoment_Estimates_SupportedIdealParts`, `CubicMoment_Estimates_WideLogDenominator`, `CubicMoment_Theta_CubicThetaArithmeticRowSeries`, `CubicMoment_Theta_CubicThetaCuspCharacter`, `CubicMoment_Theta_CubicThetaCuspHeatBound`, `CubicMoment_Theta_CubicThetaCuspStep`, `CubicMoment_Theta_CubicThetaGaussianLinearTail`, `CubicMoment_Theta_CubicThetaGaussianPowerBound`, `CubicMoment_Theta_CubicThetaGaussianTail`, `CubicMoment_Theta_CubicThetaKubotaConjugation`, `CubicMoment_Theta_CubicThetaKubotaInteger`, `CubicMoment_Theta_CubicThetaPointMeasureLocallyFinite`, `CubicMoment_Theta_CubicThetaPointMeasurePositive`, `CubicMoment_Theta_CubicThetaPositiveHeightBand`, `CubicMoment_Theta_CubicThetaPrimaryIndex`, `CubicMoment_Theta_CubicThetaPrimaryUnitResidue`, `CubicMoment_Theta_CubicThetaPrimeAdditiveGauss`, `CubicMoment_Theta_CubicThetaPrimeCubeRows`, `CubicMoment_Theta_CubicThetaPrimeHeckeContinuation`, `CubicMoment_Theta_CubicThetaPrimePoleFactors`, `CubicMoment_Theta_CubicThetaPrimeValuation`, `CubicMoment_Theta_CubicThetaRamanujan`, `CubicMoment_Theta_CubicThetaRamifiedMiddleSupport`, `CubicMoment_Theta_CubicThetaRamifiedPrimarySupport`, `CubicMoment_Theta_CubicThetaRamifiedTopPhase`, `CubicMoment_Theta_CubicThetaScalarEisenstein`, `CubicMoment_Theta_CubicThetaScalarGaussian`, `CubicMoment_Theta_CubicThetaScalarGaussianReal`, `CubicMoment_Theta_CubicThetaShiftedCuspGaussian`, `CubicMoment_Theta_CubicThetaShiftedCuspPeriodicity`, `CubicMoment_Theta_CubicThetaShiftedFrequencyBounds`, `CubicMoment_Theta_CubicThetaShiftedHeatSummability`, `CubicMoment_Theta_CubicThetaShiftedInvertedRows`, `CubicMoment_Theta_CubicThetaShiftedRowFourier`, `CubicMoment_Theta_CubicThetaShiftedRowMellin`, `CubicMoment_Theta_CubicThetaShiftedRowWeight`, `CubicMoment_Theta_CubicThetaSieveSupport`, `CubicMoment_Theta_CubicThetaTwistFourier`, `CubicMoment_Transform_MetaplecticConjugateMean`, `CubicMoment_Transform_MetaplecticCubeEnergy`, `CubicMoment_Transform_MetaplecticNormDyads`, `CubicMoment_Transform_MetaplecticPrimalFinite`, `CubicMoment_Transform_MetaplecticPrimaryCompletion`, `CubicMoment_Transform_MetaplecticRadialCentered`, `CubicMoment_Transform_MetaplecticRadialEulerTail`, `CubicMoment_Transform_MetaplecticRetainedSupport`, `CubicMoment_Transform_MetaplecticSquarefreeRadial`, `CubicMoment_Transform_MetaplecticVoronoi`.
--
--   **Imports.** It imports the published bundle `Def_PattersonFirstMoment`; the bundles `OAIQ096A004`, `OAIQ096A005` and `OAIQ096A006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ096A014` and `OAIQ096A015`; the statements `OAI.CubicFirstMoment.UniformLogWeights.cubicTheta_completed_signed_angular_mean`, `OAI.CubicFirstMoment.UniformLogWeights.cubicTheta_completed_signed_radial_mean`, `OAI.CubicFirstMoment.all_short_smooth_cubic_neighborhood`, `OAI.CubicFirstMoment.angular_sieved_full_model_asymptotic`, `OAI.CubicFirstMoment.angular_stopped_noncube_radial_form`, `OAI.CubicFirstMoment.angular_stopped_sieved_model_log_saving`, `OAI.CubicFirstMoment.cubicThetaActualCompletedRadialMain_eq`, `OAI.CubicFirstMoment.dominant_balanced_full_factor_neighborhood`, `OAI.CubicFirstMoment.first_common_prime_exponents`, `OAI.CubicFirstMoment.first_weighted_tuple_neighborhood`, `OAI.CubicFirstMoment.height_radial_form_saving`, `OAI.CubicFirstMoment.localized_integral_power_saving`, `OAI.CubicFirstMoment.sieved_full_model_asymptotic`, `OAI.CubicFirstMoment.stopped_noncube_radial_form` and `OAI.CubicFirstMoment.stopped_sieved_model_log_saving`; the proofs of `OAI_CubicFirstMoment_LogarithmicWeightFamily_metaplectic_long_large_power`, `OAI_CubicFirstMoment_LogarithmicWeightFamily_metaplectic_long_small_power`, `OAI_CubicFirstMoment_angular_low_noncube_mass`, `OAI.CubicFirstMoment.bounded_cubic_moment`, `OAI.CubicFirstMoment.bounded_large_common_nonzero`, `OAI.CubicFirstMoment.dilated_noncube_three_sieve_bounds`, `OAI.CubicFirstMoment.first_angular_squarefreeCoordinateError_moment`, `OAI_CubicFirstMoment_low_noncube_mass`, `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.smallB_core_hybrid_sieve` and `OAI.CubicFirstMoment.small_conductor_frequency_sieve`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A004
import Definitions.Def_OAIQ096A005
import Definitions.Def_OAIQ096A006

section
-- module Solutions.OAIQ096_CM.CubicGram_SquarefreeGauss
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Composite residue characters, Chinese remainders and squarefree Gauss norms. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid

theorem gauss_eq_zero_of_not_squarefree {b : Eisenstein} (hb : primary b)
    (hs : ¬Squarefree b) : gauss b = 0 := by
  obtain ⟨p,hp,d,hd⟩ := exists_primary_prime_square_dvd hb hs
  have hd0 : d ≠ 0 := by
    intro h
    apply primary_ne_zero hb
    simp [hd, h]
  subst b
  let b : Eisenstein := p*p*d
  have hb0 : b ≠ 0 := mul_ne_zero (mul_ne_zero hp.2.ne_zero hp.2.ne_zero) hd0
  let : Finite (Residues b) := finite_residues hb0
  let : Fintype (Residues b) := Fintype.ofFinite _
  obtain ⟨w,hw⟩ := exists_nontrivial_additivePhase hp
  let h : Residues b := Ideal.Quotient.mk (modulus b) (p*d*w)
  let f : Residues b → ℂ := fun v =>
    cubicSymbol b (residueRepresentative b v) * additivePhase b (residueRepresentative b v)
  have hf (v : Residues b) : f (v+h) = f v * additivePhase p w := by
    have heq : Ideal.Quotient.mk (modulus b) (residueRepresentative b (v+h)) =
        Ideal.Quotient.mk (modulus b) (residueRepresentative b v + p*d*w) := by
      rw [residueRepresentative_spec, map_add, residueRepresentative_spec]
    dsimp only [f]
    rw [cubicSymbol_congr heq, additivePhase_congr hb0 heq,
      cubicSymbol_add_last_lift, additivePhase_add, additivePhase_last_lift hp.2.ne_zero hd0]
    ring
  have hsum := Equiv.sum_comp (Equiv.addRight h) f
  change (∑ v : Residues b, f (v+h)) = ∑ v : Residues b, f v at hsum
  simp_rw [hf] at hsum
  rw [← Finset.sum_mul] at hsum
  have hz : (∑ v : Residues b, f v) = 0 := by
    rcases mul_eq_zero.mp (show (∑ v : Residues b, f v) * (additivePhase p w - 1) = 0 by
      linear_combination hsum) with hz | hz
    · exact hz
    · exact (hw (sub_eq_zero.mp hz)).elim
  change gauss b = 0
  rw [gauss_eq_finite_sum, show (∑ v : Residues b,
    cubicSymbol b (residueRepresentative b v) * additivePhase b (residueRepresentative b v)) = 0 from hz,
    mul_zero]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_Reciprocity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full cubic reciprocity and twisted multiplicativity of Gauss sums. -/

section

noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem gauss_twisted_mul {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hab : IsCoprime a b) : gauss (a*b) = gauss a * gauss b * cubicSymbol b a ^ 2 := by
  rw [gauss_mul_of_isCoprime ha hb hab, cubic_reciprocity ha hb, pow_two]

theorem gauss_mul {a b : Eisenstein} (ha : primary a) (hb : primary b) :
    gauss (a*b) = gauss a * gauss b * star (cubicSymbol b a) := by
  by_cases hab : IsCoprime a b
  · rw [gauss_twisted_mul ha hb hab, cubicSymbol_sq_eq_star hb]
  · have hs : ¬Squarefree (a*b) := fun hs =>
      hab (isRelPrime_iff_isCoprime.mp (IsRelPrime.of_squarefree_mul hs))
    rw [gauss_eq_zero_of_not_squarefree (primary_mul ha hb) hs,
      cubicSymbol_eq_zero_of_not_isCoprime hb (fun h => hab h.symm), star_zero, mul_zero]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubicOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite cubic sieve operators, bilinear norms and coprime completion. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable

open UniqueFactorizationMonoid
namespace CubicFirstMoment

lemma primaryPrime_mem_factors {n p : Eisenstein} (hn : primary n)
    (hp : primaryPrime p) (hd : p ∣ n) : p ∈ primaryPrimeFactors n := by
  obtain ⟨q,hq,hpq⟩ := exists_mem_normalizedFactors_of_dvd
    (primary_ne_zero hn) hp.2.irreducible hd
  apply Finset.mem_image.mpr
  refine ⟨q, Multiset.mem_toFinset.mpr hq, ?_⟩
  apply primary_associated_eq
    (primaryNormalize_primary (unit_residue_of_dvd_primary hn (dvd_of_mem_normalizedFactors hq))) hp.1
  exact (primaryNormalize_associated q).symm.trans hpq.symm

lemma primaryPrime_mem_factors_iff {n p : Eisenstein} (hn : primary n) :
    p ∈ primaryPrimeFactors n ↔ primaryPrime p ∧ p ∣ n :=
  ⟨primaryPrimeFactor_spec hn, fun h => primaryPrime_mem_factors hn h.1 h.2⟩

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_NormRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Divisor-completed energies and the coprime Poisson norm recurrence. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def sievePrimeSet (S : Finset Eisenstein) : Finset Eisenstein :=
  S.biUnion primaryPrimeFactors

end CubicFirstMoment

namespace CubicFirstMoment

def gaussRowCoefficient (u : Eisenstein → ℂ) (a : Eisenstein) : ℂ :=
  u a * gauss a / (Real.sqrt (norm a) : ℂ)

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_InnerExtension
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full inner cube covers and sharp coefficient extension bounds. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def innerCubeIndices (j : ℕ) : Finset InnerCubeIndex :=
  (cubeDyadTriples j).sigma (fun z => (nonzeroNormBall 729).product
    ((squarefreePrimaryDyad z.1).product
      ((squarefreePrimaryDyad z.2.1).product (frequencyDyad z.2.2))))

def innerCubeValue (q : InnerCubeIndex) : Eisenstein :=
  q.2.1*(q.2.2.1*q.2.2.2.1^2*q.2.2.2.2^3)

def innerCubeCoefficient (j : ℕ) (v : Eisenstein → ℂ) : InnerCubeIndex → ℂ :=
  finiteCoverCoefficient (innerCubeIndices j) innerCubeValue (frequencyDyad j) v

def innerCubeBlockSum (j : ℕ) (v : Eisenstein → ℂ) (a : Eisenstein)
    (z : ℕ×ℕ×ℕ) (r : Eisenstein) : ℂ :=
  ∑ t ∈ squarefreePrimaryDyad z.2.1, ∑ c ∈ frequencyDyad z.2.2,
    ∑ s ∈ squarefreePrimaryDyad z.1,
      innerCubeCoefficient j v ⟨z,r,s,t,c⟩*cubicSymbol a (r*(s*t^2*c^3))

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimaryLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cancellation on the actual primary congruence class. The annulus
has zero area, and scaled coset Poisson summation controls every length. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff SchwartzMap
namespace CubicFirstMoment

def primaryAngularLattice (ℓ : ℤ) (W : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑' u : PrimaryArgument, theta ℓ u*W (norm u/Y)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularCoprimeLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coprimality removal for the angular lattice model. The
primary congruence class and all divisor phases remain literal. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primaryCoprimeAngularLattice (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑' u : Eisenstein, if primary u ∧ IsCoprime r u then theta ℓ u*W (norm u/Y) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebius
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The short Möbius identity on Eisenstein ideals

Nonzero Eisenstein ideals are represented by their finite prime-ideal
exponent vectors. Their arithmetic functions form the multivariate power
series ring: its multiplication is exactly finite Dirichlet convolution.
The norm below is the norm of the product of prime representatives, so
the support statements retain the actual multiplicative ideal norm.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

def shortMoebiusResidual (F : ℝ) : EisensteinArithmeticFunction :=
  1 - shortIdealMoebius F * idealZeta

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite ordered prime convolutions used in the exceptional moments.
The weights are independent on the prime factors; the squarefree cutoff
is exposed exactly as the repeated-prime discrepancy. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A product of primary primes is squarefree exactly when the tuple has
no repeated prime. The normalization to primary elements makes equality,
rather than association, the correct repetition test. -/
theorem squarefree_prime_tuple_iff (f : ι → Eisenstein) (hf : ∀ i, primaryPrime (f i)) :
    Squarefree (∏ i, f i) ↔ Function.Injective f := by
  constructor
  · intro hs i j hij
    by_contra hne
    have hdiv : f i*f j ∣ ∏ k, f k := by
      have h := Finset.prod_dvd_prod_of_subset ({i,j}:Finset ι) Finset.univ f
        (Finset.subset_univ _)
      simpa [hne] using h
    have hs' := hs.squarefree_of_dvd hdiv
    rw [hij] at hs'
    have hu := hs' (f j) (by simp)
    exact (hf j).2.not_isUnit hu
  · intro hi
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i _ j _ hij
      exact (primaryPrimes_isCoprime (hf i) (hf j) (fun h => hij (hi h))).isRelPrime
    · intro i _
      exact (hf i).2.squarefree

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_OrdinaryMixedSieve
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary mixed cubic character sieve, derived from Huxley's additive
large sieve. The only extra loss is the proved arbitrarily small divisor power. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def pairConductor (p : Eisenstein × Eisenstein) : Eisenstein := p.1*p.2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PolynomialMeanValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ordinary mean values after collecting Eisenstein norms

The input `MontgomeryVaughanBound` is the ordinary Dirichlet-polynomial
mean-square theorem of Montgomery--Vaughan, *Hilbert's inequality*,
J. London Math. Soc. (2) 8 (1974), Corollary 3, p. 75, equation (1.11),
in the form explicitly recorded
in the manuscript as `eq:ordinary-mean-value`.

The deductions below collect the actual Eisenstein norms, record their
multiplicity cost, and preserve an arbitrary fixed angular weight and
an arbitrary translated height. These are the ordinary mean-value steps
in `eq:dispersion-height-small` and `eq:angular-completed-height`.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace CubicFirstMoment

/-- Collection by rational norm, with no change to the coefficients. -/
def normCollectedCoeff (s : Finset Eisenstein) (v : Eisenstein → ℂ) (n : ℕ) : ℂ :=
  ∑ b ∈ s with normNat b = n, v b

/-- Finite polynomial before collecting the equal rational norms. -/
def eisensteinNormPolynomial (s : Finset Eisenstein) (v : Eisenstein → ℂ) (t : ℝ) : ℂ :=
  ∑ b ∈ s, v b * mellinPhase t (norm b)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredMeanValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mean values of the squarefree prime-convolution discrepancy

The ordinary Montgomery--Vaughan input is specialized to the actual
coefficients obtained from independent prime factors.  The full polynomial
factors exactly; removing repeated primes costs the energy already proved
in `RepeatedPrimeSupport`.  The maximum multiplicity of an integer norm is
kept explicit, so no divisor estimate is hidden in this deduction.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The product before imposing squarefreeness. The prime supports and
weights are independent, exactly as required by the structured coefficients. -/
def fullPrimeProductPolynomial (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (ℓ : ℤ) (u t : ℝ) : ℂ :=
  ∏ i, ∑ p ∈ S i, w i p * theta ℓ p * mellinPhase (t + u) (norm p)

/-- The actual largest multiplicity when distinct Eisenstein integers have
the same positive rational norm. -/
def normFiberMultiplicity (B : Finset Eisenstein) (Z : ℕ) : ℕ :=
  (Finset.Icc 1 Z).sup (fun n => (B.filter (fun b => normNat b = n)).card)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SparseFourthMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The square of a structured error polynomial has controlled coefficient
energy. This supplies the fourth-moment estimate in the balanced range. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def productSupport (B : Finset Eisenstein) : Finset Eisenstein :=
  (B.product B).image (fun z => z.1*z.2)

def squareConvolution (B : Finset Eisenstein) (v : Eisenstein → ℂ) (n : Eisenstein) : ℂ :=
  ∑ z ∈ B.product B with z.1*z.2 = n, v z.1*v z.2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeToThreeIdeals
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual ramified Euler restriction in primary-element polynomials.
Prime-to-three ideals are identified arithmetically, then the complete
ideal-sum exclusion formula restores their missing local factors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- All prime ideals dividing the rational integer three. -/
def ramifiedIdealPrimes : Finset EisensteinIdealPrime :=
  (idealExponentOf (3 : Eisenstein)).support

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryHeckeCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite character attached to the primary mixed cubic
symbol. Including the modulus 3 makes primary normalization periodic
and removes its dependence on the choice of a unit associate. -/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- The actual ideal coefficient, with ramified factors explicitly zero. -/
def primaryMixedIdealChar (a b : Eisenstein) (ν : EisensteinIdealExponent) : ℂ :=
  primaryMixedLift a b (idealExponentGenerator ν)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularDyadicMoment
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite dyadic splitting of the retained dual integral and the
resulting character-average bound. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def finiteAngularDualIntegral {ν : Type*} (W : ℝ → ℂ) (S : Finset ν) (χ : ν → ℂ)
    (N : ν → ℝ) (ε : ℂ) (A k Z t : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ,
    mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*(Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
      angularFiniteHeckeDual S χ N ε A k ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortFactorGram
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Repeated short factors in the final Gram estimate. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def shortRepeatedSupport (m : ℕ) (X : ℝ) : Finset Eisenstein :=
  orderedConvolutionSupport (fun _ : Fin m => primaryElementBall X)

def shortRepeatedCoefficient (m : ℕ) (X : ℝ) (A : EisensteinArithmeticFunction)
    (u : Eisenstein → ℂ) : Eisenstein → ℂ :=
  orderedConvolution (fun _ : Fin m => primaryElementBall X)
    (fun _ n => ((MvPowerSeries.coeff (idealExponentOf n) A:ℝ):ℂ)*u n)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortFactorUniform
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform power saving from the proved actual-sequence contradictions. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mixedInstanceMoment (x : ShortMomentInstance ι (Eisenstein × Eisenstein)) : ℝ :=
  ∑ p ∈ x.rows, ‖∏ i, x.family.mixedValue 0 i p‖^2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallPrimeParts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual small-prime partition of squarefree cubic moduli. Its
parts divide the small modulus, so their number has a proved subpower bound. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def supportedIdealPart (v : Eisenstein) (ν : EisensteinIdealExponent) : EisensteinIdealExponent :=
  ν.filter (fun p => p ∈ (idealExponentOf v).support)

def outsideIdealPart (v : Eisenstein) (ν : EisensteinIdealExponent) : EisensteinIdealExponent :=
  ν.filter (fun p => p ∉ (idealExponentOf v).support)

lemma supported_add_outside (v : Eisenstein) (ν : EisensteinIdealExponent) :
    supportedIdealPart v ν+outsideIdealPart v ν = ν := Finsupp.filter_add_filter_not _ _

lemma supportedIdealPart_le (v : Eisenstein) (ν : EisensteinIdealExponent) :
    supportedIdealPart v ν ≤ ν := by
  intro p
  simp only [supportedIdealPart,Finsupp.filter_apply]
  split <;> simp

lemma outsideIdealPart_le (v : Eisenstein) (ν : EisensteinIdealExponent) :
    outsideIdealPart v ν ≤ ν := by
  intro p
  simp only [outsideIdealPart,Finsupp.filter_apply]
  split <;> simp

def primarySmallPart (v a : Eisenstein) : Eisenstein :=
  idealPrimaryGenerator (supportedIdealPart v (idealExponentOf a))

def primaryOutsidePart (v a : Eisenstein) : Eisenstein :=
  idealPrimaryGenerator (outsideIdealPart v (idealExponentOf a))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SupportedIdealParts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact separation of the primes of an arbitrary nonzero modulus. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def supportedParts (v : Eisenstein) (S : Finset EisensteinIdealExponent) : Finset EisensteinIdealExponent :=
  S.image (supportedIdealPart v)

def outsideFiber (v : Eisenstein) (S : Finset EisensteinIdealExponent) (ρ : EisensteinIdealExponent) :
    Finset EisensteinIdealExponent :=
  (S.filter (fun ν => supportedIdealPart v ν = ρ)).image (outsideIdealPart v)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallTwistSmoothMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original primary mixed smooth sum has the cubic second moment.
Its primitive characters, conductors, and Euler corrections are constructed. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primarySmallTwistSmoothSum (a b q : Eisenstein) (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ) (Z t : ℝ) : ℂ :=
  ∑' x : Eisenstein, if primary x then
    mixedCubic a b x*η (Ideal.Quotient.mk (modulus q) x)*mellinPhase t (norm x)*W (norm x/Z) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogSmallTwist
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dominant logarithmic full factor retains a positive power saving. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primarySmallTwistLogSmoothSum (a b q : Eisenstein) (η : MulChar (Residues q) ℂ)
    (W : ℝ → ℂ) (Z t : ℝ) : ℂ :=
  ∑' x : Eisenstein, if primary x then
    (Real.log (norm x):ℂ)*(mixedCubic a b x*η (Ideal.Quotient.mk (modulus q) x)*
      mellinPhase t (norm x))*W (norm x/Z) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullSmoothFactor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact classification of the full smooth factors from the short inverse.
The short Möbius alternative vanishes once the dyad lies above its support. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primaryShortSmoothSum (A : EisensteinArithmeticFunction) (a b q : Eisenstein)
    (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ) (Z t : ℝ) : ℂ :=
  ∑' x : Eisenstein, if primary x then
    ((MvPowerSeries.coeff (idealExponentOf x) A:ℝ):ℂ)*
      (mixedCubic a b x*η (Ideal.Quotient.mk (modulus q) x)*mellinPhase t (norm x))*W (norm x/Z)
    else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BalancedFullRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Collection over the second conductor variable, with literal row fibers. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def pairFirstFiber (S : Finset (Eisenstein × Eisenstein)) (b : Eisenstein) : Finset Eisenstein :=
  (S.filter (fun p => p.2 = b)).image Prod.fst

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallPairParts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact two-variable conductor partitions and their arithmetic size. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def pairSmallParts (v : Eisenstein) (p : Eisenstein × Eisenstein) : Eisenstein × Eisenstein :=
  (primarySmallPart v p.1,primarySmallPart v p.2)

def pairOutsideParts (v : Eisenstein) (p : Eisenstein × Eisenstein) : Eisenstein × Eisenstein :=
  (primaryOutsidePart v p.1,primaryOutsidePart v p.2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortTupleMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mellin separation for the actual smooth short-inverse factors. The
integrand is a product of the original primary sums, with a common shift. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primaryShortTupleSum (X : ι → ℝ) (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (W : ι → ℝ → ℂ) (t : ι → ℝ) (V : ℝ → ℂ) (Z : ℝ) : ℂ :=
  ∑ n : (i : ι) → primaryElementBall (X i),
    (∏ i, ((MvPowerSeries.coeff (idealExponentOf (n i)) (A i):ℝ):ℂ)*
      (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
        mellinPhase (t i) (norm (n i)))*W i (norm (n i)/(X i/2)))*
      V ((∏ i, norm (n i))/Z)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortTuplePartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reconstruction of the original finite convolution from smooth
norm pieces. The common ball is forced by the global product cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primaryTupleCore (A : ι → EisensteinArithmeticFunction) (a b : Eisenstein)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (t : ι → ℝ) (V : ℝ → ℂ) (Z : ℝ) (n : ι → Eisenstein) : ℂ :=
  (∏ i, ((MvPowerSeries.coeff (idealExponentOf (n i)) (A i):ℝ):ℂ)*
    (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
      mellinPhase (t i) (norm (n i))))*V ((∏ i, norm (n i))/Z)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortConvolutionMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exceptional moments of the actual unsplit short convolutions, obtained
by inserting and then summing the constructed smooth norm partition. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primaryUnsplitTuple (A : ι → EisensteinArithmeticFunction) (a b : Eisenstein)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (t : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
    primaryTupleCore A a b q η t V Y n

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebiusProducts
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short Möbius identity remains valid inside any fixed product of
prime-weight factors. This is the algebraic replacement before smoothing. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def shortVonMangoldt (F : ℝ) : EisensteinArithmeticFunction :=
  (2*shortIdealMoebius F-shortIdealMoebius F*shortIdealMoebius F*idealZeta)*idealLogNorm

def shortTwoFactor (F : ℝ) : EisensteinArithmeticFunction := shortIdealMoebius F*idealLogNorm

def shortFourFactor (F : ℝ) : EisensteinArithmeticFunction :=
  shortIdealMoebius F*shortIdealMoebius F*idealZeta*idealLogNorm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ComplexWeightedConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complex coefficient collection retains the distinct norm and residue
twists of each original prime factor during short inversion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primaryComplexProductPolynomial (A : ι → MvPowerSeries EisensteinIdealPrime ℂ)
    (χ : Eisenstein → ℂ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ b ∈ primaryElementBall (2*Y),
    MvPowerSeries.coeff (idealExponentOf b) (∏ i, A i)*χ b*V (norm b/Y)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoordinateWeightedTuple
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent smooth weights on the original arithmetic factors, with the
exact Mellin representation by the unweighted convolutions. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primaryCoordinateWeightedTuple (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
    primaryTupleCore A a b q η t V Y n * ∏ i, W i (norm (n i)/X i)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeCoordinateDifference
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact difference between normalized von Mangoldt tuples and
original prime-indicator tuples on the global smooth cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primaryPrimeIndicatorTuple (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
    (∏ i, (primeIndicator (n i):ℂ)*W i (norm (n i)/X i)*
      (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
        mellinPhase (t i) (norm (n i))))*V ((∏ i, norm (n i))/Y)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimeCoordinateCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact collection of angular coordinate tuples. The same fixed theta
factor occurs on each original coordinate and hence on their product. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primaryAngularCoefficientTuple (ℓ : ℤ) (A : Eisenstein → ℂ)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
    (∏ i, A (n i)*W i (norm (n i)/X i)*
      (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
        theta ℓ (n i)*mellinPhase (t i) (norm (n i))))*V ((∏ i, norm (n i))/Y)

def primaryAngularPrimeIndicatorTuple (ℓ : ℤ) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  primaryAngularCoefficientTuple ℓ (fun n => (primeIndicator n:ℂ)) a b q η t W X V Y

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The exact arithmetic identity for dispersion

The existing lattice Poisson theorem is applied to the actual Gauss-sum
rows. Conjugation reverses the mixed-character pair; the two normalized
Gauss factors then cancel. The resulting identity retains the dispersion remainder explicitly.
-/

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

def smoothedDispersionVariance (B : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑' a : Eisenstein, if primary a then
    W (norm a / A) * ((‖dispersionPolynomial B β u a‖^2 : ℝ) : ℂ) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeMajorant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The squarefree majorant in corrected dispersion

Only the positive variance term is majorized. The mixed and model terms
retain their actual Möbius-square weights.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def truncatedSquareDivisorSum (C : Finset Eisenstein) (a : Eisenstein) : ℝ :=
  ∑ c ∈ C, if c^2 ∣ a then (idealMoebius c : ℝ) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSquarefreeIdentity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact square-divisor Möbius identity on primary elements.
This is the arithmetic inversion used by the low-height angular model. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primarySquarePrimeFactors (a : Eisenstein) : Finset Eisenstein :=
  (primaryPrimeFactors a).filter (fun p => p^2 ∣ a)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSquarefreeLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Low-height angular cancellation for the literal squarefree,
coprime primary lattice sum. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def squarefreeCoprimeAngularLattice (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑' u : Eisenstein, if primary u ∧ IsCoprime r u then
    (idealMoebius u:ℂ)^2*theta ℓ u*W (norm u/Y) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticVoronoi
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal level/angular Voronoi input of Dunn--Radziwill,
arXiv:2109.07463v3, Proposition 5.3, equations (5.79)--(5.82), pp.33--34.
The raw formula is kept separate from its proved Gauss/phase normalization.
The index `n` below denotes the actual frequency `n / lambda`; zero is excluded.
No estimate for a completed sum is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticCommonNorm (r : Eisenstein) (n : MetaplecticDualArgument) : ℝ :=
  ∏ p ∈ (primaryPrimeFactors r).filter (fun p => p ∣ n.val), norm p

def metaplecticRawCompleted (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' du : PrimaryArgument × PrimaryArgument,
    if IsCoprime (du.1:Eisenstein) r then
      (Real.sqrt (norm du.1):ℂ)*gauss du.2*theta ℓ (du.2*du.1^3)*
        star (cubicSymbol r du.2)*W (norm (du.2*du.1^3)/X)
    else 0

def metaplecticCompleted (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' du : PrimaryArgument × PrimaryArgument,
    if IsCoprime (du.1:Eisenstein) r then
      (Real.sqrt (norm du.1):ℂ)*gauss (r*du.2)*theta ℓ (r*(du.2*du.1^3))*
        W (norm (du.2*du.1^3)/X)
    else 0

def metaplecticMain (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  if ℓ = 0 then
    ((metaplecticA0*X^(5/6:ℝ)*metaplecticTotient r*norm r^(-7/6:ℝ):ℝ):ℂ)*
      mellin W (5/6)
  else 0

def metaplecticRawPrefactor (r : Eisenstein) (ℓ : ℤ) : ℂ :=
  star ((Real.sqrt (norm r):ℂ)*gauss r)/
    ((3^(7/2:ℝ)*(2*Real.pi)^2:ℝ):ℂ)*((star (r:ℂ)/(r:ℂ))^(-ℓ))

def metaplecticPrefactor (r : Eisenstein) (ℓ : ℤ) : ℂ :=
  ((Real.sqrt (norm r)/(3^(7/2:ℝ)*(2*Real.pi)^2):ℝ):ℂ)*theta (3*ℓ) r

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorDispersion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dispersion after a square-divisor restriction

The squarefree majorant introduces `d² ∣ a`. Expanding the actual
variance and changing variables produces a Gram kernel at scale
`A / N(d)²`, with the precise cubic-character factor retained.
-/

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def divisorDispersionVariance (d : Eisenstein) (B : Finset Eisenstein)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑' a : Eisenstein, if primary a ∧ d^2 ∣ a then
    W (norm a/A)*((‖dispersionPolynomial B β u a‖^2 : ℝ) : ℂ) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SievedDispersion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact assembly of the sieved dispersion variance

The positive majorant is the finite sum of the square-divisor variances.
This makes the collected coefficients and the restricted Poisson formula
apply to the original arithmetic polynomial.
-/

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def sievedDispersionVariance (C B : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑' a : Eisenstein, if primary a then
    (((truncatedSquareDivisorSum C a)^2 : ℝ) : ℂ)*
      W (norm a/A)*((‖dispersionPolynomial B β u a‖^2 : ℝ) : ℂ) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRadialCentered
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform centered radial lattice sums, including the short empty range.
The coprimality correction is a literal finite Möbius expansion. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primaryCoprimeRadialMain (r : Eisenstein) (W : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ s ∈ (primaryPrimeFactors r).powerset,
    (idealMoebius (∏ p ∈ s,p):ℂ)*primaryRadialMain W (Y/norm (∏ p ∈ s,p))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRadialEulerTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite Möbius density has a uniform quantitative tail.
A convergent Eisenstein norm series supplies the only estimate. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticRadialEulerPartial (r : Eisenstein) (C : ℝ) : ℂ :=
  ∑ c ∈ primaryElementBall C, if IsCoprime r c then
    (idealMoebius c:ℂ)*((norm c^(-2:ℝ):ℝ):ℂ) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticSquarefreeRadial
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The squarefree radial model after actual square-divisor inversion.
Its finite main term remains explicit for comparison with the inverse
completion residue. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def squarefreeCoprimeRadialMain (r : Eisenstein) (W : ℝ → ℂ) (Y B : ℝ) : ℂ :=
  ∑ c ∈ squarefreeDivisorTruncation (Real.sqrt (B*Y)),
    (idealMoebius c:ℂ)*(if IsCoprime r (c^2) then
      primaryCoprimeRadialMain r W (Y/norm (c^2)) else 0)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeModelMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal squarefree mass occurring in the corrected model,
written in the radial lattice normalization. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def squarefreeModelMass (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑' a : Eisenstein, if primary a then (idealMoebius a:ℂ)^2*
    W (norm a/A)*((norm a^(-1/3:ℝ):ℝ):ℂ) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BilinearKernelIdentity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The factored correction and the original squarefree product kernel
are related by the explicit shared-prime contribution. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def modelOverlap (P B : Finset Eisenstein) (α β : Eisenstein → ℂ) (u : ℝ) : ℂ :=
  ∑ a ∈ P, ∑ b ∈ B, if IsCoprime a b then 0 else
    (cStar:ℂ)*α a*β b*normTwist u a*normTwist u b*(idealMoebius a:ℂ)^2*
      ((norm a^(-1/6:ℝ):ℝ):ℂ)*((norm b^(-1/6:ℝ):ℝ):ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ConductorNeighborhoods
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform exceptional moments hold throughout a fixed open neighborhood
of each exceptional conductor exponent. The neighborhoods are constructed by
contradiction from actual short-factor sequences, not assumed as analytic inputs. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def neighborhoodFamily {ι κ : Type*} (x : ℕ → ConductorMomentInstance ι κ) :
    ShortFactorFamily ι where
  cutoff := fun j => (x j).family.cutoff 0
  length := fun j => (x j).family.length 0
  coefficient := fun j => (x j).family.coefficient 0
  twist := fun j => (x j).family.twist 0
  factor_spec := fun j => (x j).family.factor_spec 0
  length_ge_one := fun j => (x j).family.length_ge_one 0
  twist_bound := fun j => (x j).family.twist_bound 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormCoprimeMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite Mellin separation of the Poisson form including its
square-root norm denominator. The character rows retain their original weights. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def normCoprimeRadialForm (S H : Finset Eisenstein) (v w phase : Eisenstein → ℂ)
    (x y : Eisenstein → ℝ) (W : ℝ → ℂ) (ρ : ℝ) : ℂ :=
  ∑ h ∈ H, phase h * ∑ a ∈ S, ∑ b ∈ S,
    if IsCoprime a b then
      (v a*star (cubicSymbol a h))*star (w b*star (cubicSymbol b h))*
        (radialDualProfile W (ρ*x h/(y a*y b))/(Real.sqrt (y a*y b):ℂ)) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionAbsoluteModel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute model mass controls both the model and the coprimality error
in its Type-I replacement. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def dispersionAbsoluteModel (S : Finset Eisenstein) (β : Eisenstein → ℂ) : ℝ :=
  ∑ b ∈ S, ‖β b‖*norm b^(-1/6:ℝ)


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ExcludedPrimeInput
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The numerator-independent coprimality exclusion in the actual smooth
prime sum, with the error supplied by the proved divisor bound. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def excludedSmoothPrimeCharacterSum (R Y : ℝ) (w : ℝ → ℂ)
    (χ : Eisenstein → ℂ) (e : Eisenstein) (u : ℝ) : ℂ :=
  ∑ p ∈ primeCutoff (R*Y) with IsCoprime p e,
    w (norm p/Y)*mellinPhase u (norm p)*χ p

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeFactorization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact independent-prime factorization, keeping the squarefree error
and the coprimality exclusion of the actual structured sum. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primeExclusionCharacter (e : Eisenstein) : Eisenstein →* ℂ :=
  (1 : MulChar (Residues e) ℂ).toMonoidHom.comp
    (Ideal.Quotient.mk (modulus e)).toMonoidHom

def excludedPrimeWeight (e : Eisenstein) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (i : ι) (p : Eisenstein) : ℂ := W i (norm p/X i)*primeExclusionCharacter e p

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowCoreSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete finite low-conductor frequency support: a small
nonzero core times a bounded cube, with precisely the cubes removed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def lowNoncubeSupport (V J : ℝ) : Finset Eisenstein :=
  (((nonzeroNormBall V).product (nonzeroNormBall J)).image
    (fun z => z.1*z.2^3)).filter (fun h => ¬∃ j : Eisenstein, j^3 = h)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightCubeMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cube frequencies in a height average use the ordinary polynomial
mean, rather than the low-height cube lattice asymptotic. -/
noncomputable section
open scoped BigOperators
open Filter MeasureTheory
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

def nonzeroCubeNormBall (B : ℝ) : Finset Eisenstein :=
  (nonzeroNormBall (B^(1/3:ℝ))).image (fun z => z^3)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCubeEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Energy of the actual cube-completed primal polynomial. Cube-divisor
fibers cost an arbitrary small power; the remaining weighted pair count
is linear in the norm cutoff, because the d-variable has exponent -2. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticCubeProduct (du : Eisenstein × Eisenstein) : Eisenstein := du.2*du.1^3

def metaplecticCubeCoefficient (S : Finset (Eisenstein × Eisenstein))
    (w : Eisenstein × Eisenstein → ℂ) (b : Eisenstein) : ℂ :=
  ∑ du ∈ S with metaplecticCubeProduct du = b, w du

/-- The literal primal summand before its norm-phase, as in the
published completed sum. -/
def metaplecticPrimalCoefficient (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    (X : ℝ) (du : Eisenstein × Eisenstein) : ℂ :=
  if IsCoprime du.1 r then
    (Real.sqrt (norm du.1):ℂ)*gauss (r*du.2)*
      theta ℓ (r*metaplecticCubeProduct du)*W (norm (metaplecticCubeProduct du)/X)
  else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticPrimalFinite
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact support turns the literal completed sum, at every translated
height, into the finite primary cube polynomial used by Montgomery--Vaughan. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticPrimaryPair (du : PrimaryArgument × PrimaryArgument) : Eisenstein × Eisenstein :=
  (du.1.val,du.2.val)

def metaplecticPrimalSupport (V : ℝ) : Finset (PrimaryArgument × PrimaryArgument) :=
  (((primaryElementBall V).subtype primary).product ((primaryElementBall V).subtype primary)).filter
    (fun du => norm (metaplecticCubeProduct (metaplecticPrimaryPair du)) ≤ V)

def metaplecticPrimalElementSupport (V : ℝ) : Finset (Eisenstein × Eisenstein) :=
  (metaplecticPrimalSupport V).image metaplecticPrimaryPair

def metaplecticHeightCompleted (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    (X t : ℝ) : ℂ :=
  ∑' du : PrimaryArgument × PrimaryArgument,
    metaplecticPrimalCoefficient r ℓ W X (metaplecticPrimaryPair du)*
      mellinPhase t (norm (metaplecticCubeProduct (metaplecticPrimaryPair du)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRetainedSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose the literal published support representation once for each
nonzero retained coefficient. The resulting finite code set decodes
injectively to the original frequency set. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticDivisorPrimary (r : Eisenstein) (h : metaplecticPrimaryDivisors r) : PrimaryArgument :=
  ⟨h.val,(mem_primaryElementBall.mp (Finset.mem_filter.mp h.property).1).1⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticNormDyads
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical finite norm-dyad partition of the retained Voronoi pairs.
The integral frequency d³n has norm exactly three times N(d³ν). -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticIntegralFrequency (nd : MetaplecticDualArgument × PrimaryArgument) : Eisenstein :=
  nd.2.val^3*nd.1.val

def metaplecticNormDyadIndex (nd : MetaplecticDualArgument × PrimaryArgument) : ℕ :=
  Nat.log 2 (normNat (metaplecticIntegralFrequency nd))

def metaplecticNormDyad (S : Finset (MetaplecticDualArgument × PrimaryArgument)) (j : ℕ) :
    Finset (MetaplecticDualArgument × PrimaryArgument) :=
  S.filter (fun nd => metaplecticNormDyadIndex nd = j)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FiniteCharacterMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrary finite cubic-character rows and their exact Mellin twists. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def finiteCharacterMass (S H : Finset Eisenstein) (β : Eisenstein → ℂ) (u : ℝ) : ℝ :=
  ∑ h ∈ H, ‖∑ a ∈ S, β a*cubicSymbol a h*mellinPhase u (norm a)‖^2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorCharacterMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact divisor mass behind the genuine coprimality kernel, with
arbitrary squarefree coefficients and both Fourier signs. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def divisorCharacterMass (S H U : Finset Eisenstein) (β : Eisenstein → ℂ) (u : ℝ) : ℝ :=
  ∑ d ∈ U.powerset, finiteCharacterMass (S.filter (fun a => (∏ p ∈ d, p) ∣ a)) H β u

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogNormCells
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual disjoint log-norm partition used in the integrated bilinear
estimate. Its finite fibers preserve both the sum and coefficient energy. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def logNormCellSupport (S : Finset Eisenstein) (J A : ℝ) (i : ℤ) : Finset Eisenstein :=
  S.filter (fun a => logNormCell J A a = i)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NearLogNormCells
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual log-norm cells meeting the product boundary have degree at
most five. The near-cell diagonal therefore retains the inverse cell width. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def nearLogNormCells (P S : Finset Eisenstein) (J A B X₀ : ℝ) : Finset (ℤ × ℤ) := by
  classical
  exact ((P.image (logNormCell J A)).product (S.image (logNormCell J B))).filter
    (fun e => ∃ a ∈ P, ∃ b ∈ S, logNormCell J A a = e.1 ∧
      logNormCell J B b = e.2 ∧ |J*Real.log (norm (a*b)/X₀)| ≤ 1)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FarLogNormCells
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Far cells are the exact complement of the actual near-cell graph.
Every product in such a cell has the lower frequency bound needed for IBP. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def farLogNormCells (P S : Finset Eisenstein) (J A B X₀ : ℝ) : Finset (ℤ × ℤ) :=
  allLogNormCells P S J A B \ nearLogNormCells P S J A B X₀

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealDirichletBounds
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform normalization of the complete ideal series on Re(s) ≥ 2.
The lower bound follows from its actual Möbius inverse. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def idealZetaTwo : ℝ :=
  ∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeUniformGrowth
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A conductor-explicit polynomial bound in the fixed strip needed by
the local zero-free argument. The finite-order constant disappears under
Phragmen--Lindelof; only the actual functional-equation factors remain. -/
noncomputable section
open Set
namespace CubicFirstMoment

def heckeZeroFreeMajorant (A k : ℝ) (ε : ℂ) : ℝ :=
  (idealZetaTwo+‖ε‖*A^4*(k+7)^4*idealZetaTwo)*16*(9/2:ℝ)^4

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealLogDerivativeTwist
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical translation and the zero-free positivity inequality for the
literal complete ideal series. -/
noncomputable section
open scoped Topology
namespace CubicFirstMoment

def idealNormTwist (χ : EisensteinIdealExponent → ℂ) (t : ℝ)
    (ν : EisensteinIdealExponent) : ℂ := χ ν*mellinPhase t (idealExponentNorm ν)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeNormalizedDisk
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize a complete Hecke function at 2+it on a disk of radius 3.
The resulting bound is explicit in the finite and archimedean conductor. -/
noncomputable section
open scoped Topology
namespace CubicFirstMoment

def normalizedHeckeDiskBound (A k : ℝ) (ε : ℂ) (t : ℝ) : ℝ :=
  2+idealZetaTwo*heckeZeroFreeMajorant A k ε*(4+|t|)^4

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyGaussianRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Periodized Gaussian rows over the actual finite set of residue fractions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def huxleyPeriodizedGaussian (t : ℝ) (x : ℂ) : ℝ :=
  ∑' z : Eisenstein, Real.exp (-t*‖(z:ℂ)-x‖^2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueThetaLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete Eisenstein theta sum, including its zero term, equals the
ideal theta sum with its exact unit multiplicity. -/
noncomputable section
namespace CubicFirstMoment

def residueLatticeTheta (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (A t : ℝ) : ℂ :=
  ∑' a : Eisenstein, χ (Ideal.Quotient.mk (modulus q) a)*(Real.exp (-norm a*t/A):ℝ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueGaussianPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian specialization of periodic lattice Poisson, retaining the exact
finite Fourier coefficient. Primitivity is only needed when this coefficient
is later evaluated as a Gauss eigenvalue. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def residueFiniteFourier (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (h : Eisenstein) : ℂ :=
  ∑' v : Residues q, χ v *
    (Real.fourierChar (tracePair (residueRepresentative q v : ℂ)
      ((h : ℂ)/((q:ℂ)*traceLambda))) : ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeDiskGrowth
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial and logarithmic conductor-height bounds for the actual
normalized Hecke disks. The constants depend only on the fixed ideal lattice. -/
noncomputable section
namespace CubicFirstMoment

def heckeDiskPolynomialConstant : ℝ := 2+32*(9/2:ℝ)^4*idealZetaTwo^2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightBilinearValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal normalized height-integrated Gauss bilinear form. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

def heightBilinearValue (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (h : ℝ → ℂ) (X₀ T : ℝ) : ℂ :=
  (T:ℂ)⁻¹*(∑ a ∈ P, ∑ b ∈ S, (α a*β b*gauss (a*b))*
    heightFourierIntegral h (Real.log (norm (a*b))-Real.log X₀))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyPhase
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The additive sieve phase as the standard Fourier character of the trace lattice. -/
noncomputable section
namespace CubicFirstMoment

def huxleyFrequencyPhase (x : ℂ) (n : Eisenstein) : ℂ :=
  Real.fourierChar (tracePair (n:ℂ) (x/traceLambda))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyResiduePoints
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal residue sums as a finite set of reduced fractions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

abbrev huxleyResidueFintype {Q : ℝ} (q : {q : Eisenstein // q ∈ nonzeroNormBall Q}) :
    Fintype (Residues q.val) :=
  @Fintype.ofFinite _ (finite_residues (mem_nonzeroNormBall.mp q.property).2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeMellinTransfer
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The prime comparison through a common-height integral

The angular Gauss-minus-model coefficients are uniformly bounded. The
actual sharp dyadic prime sum differs negligibly from the same finite
polynomial integrated against the constructed Mellin cutoff.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

def primeComparisonCoefficient (ℓ : ℤ) (p : Eisenstein) : ℂ :=
  theta ℓ p * (gaussAtPrime p - ((cStar*norm p^(-1/6 : ℝ) : ℝ) : ℂ))

def sharpDyadicPrimeComparison (ℓ : ℤ) (X : ℝ) : ℂ :=
  ∑ p ∈ primeCutoff (4*X), primeComparisonCoefficient ℓ p*(intervalStep X (2*X) (norm p) : ℝ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIdealEulerExclusion
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact deletion of finitely many Euler factors in prime-ideal sums.
Its logarithmic cost is bounded by the norm of the original modulus. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primeIdealRestriction (S : Finset EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (ν : EisensteinIdealExponent) : ℂ :=
  if ∀ p ∈ S, ν p=0 then χ ν else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealEulerSeries
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite Euler factors for the complete ideal Dirichlet series.
These retain the ramified factors lost in primitive reduction. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def idealEulerFactor (S : Finset EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (s : ℂ) : ℂ :=
  ∏ p ∈ S, (1-χ (Finsupp.single p 1)*(idealExponentNorm (Finsupp.single p 1):ℂ)^(-s))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealHeatTheta
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized theta series whose Mellin transform has the angular
Gamma shift. Its defining sum runs over all nonzero ideals. -/
noncomputable section
open Filter Asymptotics
namespace CubicFirstMoment

def idealHeatTheta (A κ : ℝ) (χ : EisensteinIdealExponent → ℂ) (t : ℝ) : ℂ :=
  ∑' ν, χ ν*((idealExponentNorm ν*t/A)^κ*Real.exp (-idealExponentNorm ν*t/A):ℝ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTupleDecomposition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual primary factor tuples in the distinguished-prime expansion.
Ordering a subset contributes its factorial; the remaining primary factor
is the literal complementary product, not an abstract coefficient. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primaryFactorRemainder (n : Eisenstein) (s : Finset Eisenstein) : Eisenstein :=
  ∏ p ∈ primaryPrimeFactors n \ s, p

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTupleFiber
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal independent prime-tuple fibre over a squarefree primary
product is exactly its set of orderings. This connects the subset detector
to the fixed-arity coefficients used in the analytic estimates. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def squarefreePrimeTupleEquiv {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    (f : ι → Eisenstein) (hf : ∀ i, primaryPrime (f i)) (hprod : (∏ i, f i) = n) :
    ι ≃ primaryPrimeFactors n :=
  Equiv.ofBijective (fun i => ⟨f i,(primaryPrime_mem_factors_iff hn).mpr
    ⟨hf i,hprod ▸ Finset.dvd_prod_of_mem f (Finset.mem_univ i)⟩⟩) (by
      constructor
      · intro i j hij
        have hinj := (squarefree_prime_tuple_iff f hf).mp (hprod.symm ▸ hs)
        exact hinj (congrArg Subtype.val hij)
      · intro p
        have hp := primaryPrimeFactor_spec hn p.property
        have hd : (p:Eisenstein) ∣ ∏ i, f i := hprod.symm ▸ hp.2
        obtain ⟨i,_,hi⟩ := (hp.1.2.dvd_finsetProd_iff f).mp hd
        have he : (p:Eisenstein) = f i := primary_associated_eq hp.1.1 (hf i).1
          ((hp.1.2.dvd_prime_iff_associated (hf i).2).mp hi)
        exact ⟨i,Subtype.ext he.symm⟩)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ModelPartialSummation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The elementary prime model from the ordinary prime ideal theorem

The only number-theoretic hypothesis used here is the ordinary asymptotic
for the number of primary prime elements.  The power-weighted consequence
is derived by Abel summation.
-/

noncomputable section

open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology

namespace CubicFirstMoment

/-- The number of primary primes having a specified integer norm. -/
def primaryPrimeMultiplicity (n : ℕ) : ℝ :=
  ((primeCutoff (n : ℝ)).filter (fun p => normNat p = n)).card

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticPrimaryCompletion
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The expanded ideal kernel is exactly a primary cube-divisor sum.
This reindexing retains the finite norm cutoff and arbitrary complex
coefficients; no analytic summability assumption enters the inversion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def weightedCubeSeries (B : ComplexIdealSeries) (x : EisensteinIdealPrime → ℂ) :
    ComplexIdealSeries := MvPowerSeries.expand 3 (by norm_num) (MvPowerSeries.rescale x B)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticConjugateMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficient conjugation supplies the opposite height orientation.
The literal published coefficient support is preserved under conjugation. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticConjugateCoefficients
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein)
    (n : MetaplecticDualArgument) : ℂ := star (a r n)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortConvolutionExpansion
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each term of the short Möbius product expansion is an actual finite
family of the three permitted arithmetic factors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def shortBranchFactor (F : ℝ) (S : Finset ι) : shortBranchIndex S → EisensteinArithmeticFunction
  | Sum.inl (_,j) => ![shortIdealMoebius F,shortIdealMoebius F,idealZeta,idealLogNorm] j
  | Sum.inr (_,j) => ![shortIdealMoebius F,idealLogNorm] j

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WideLogDenominator
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quadratic coordinate range accommodates the fixed dilations in
an output norm partition. The denominator identities need no upper range. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment

 def uniformWideLogDenominatorWeights {γ : Type*} {c : ℝ} (hc : 0 < c)
    {W : γ → ℝ → ℂ} (hW : UniformLogWeights W) :
    UniformLogWeights (fun z : γ × wideLogWeightParameters c => logDenominatorWeight c (W z.1) z.2) := by
  let F : (ℝ × ℝ) → ℝ → ℂ :=
    fun p x => (smoothReciprocal c (p.1+p.2*smoothLog x):ℂ)
  have hF : ContDiff ℝ ∞ (Function.uncurry F) := by
    have hD : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ =>
        z.1.1+z.1.2*smoothLog z.2) := by
      have hL := smoothLog_smooth.comp
        (contDiff_snd : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => z.2))
      fun_prop
    exact Complex.ofRealCLM.contDiff.comp ((smoothReciprocal_smooth hc).comp hD)
  exact hW.compactMultiplier (wideLogWeightParameters c) (wideLogWeightParameters_compact c) F hF

 def uniformCoordinateWideLogDenominatorWeights {γ ι : Type*} [Fintype ι]
    {c : ℝ} (hc : 0 < c) {W : γ → ι → ℝ → ℂ}
    (hW : UniformLogWeights (fun z : γ × ι => W z.1 z.2)) :
    UniformLogWeights (fun z : (γ × (ι → wideLogWeightParameters c)) × ι =>
      logDenominatorWeight c (W z.1.1 z.2) (z.1.2 z.2)) := by
  exact (uniformWideLogDenominatorWeights hc hW).reindex
    (fun z : (γ × (ι → wideLogWeightParameters c)) × ι => ((z.1.1,z.2),z.1.2 z.2))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredMomentTwists
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact modulus and unit condition for the numerator/exclusion twist. -/
noncomputable section
namespace CubicFirstMoment

def structuredTwistModulus (v e : Eisenstein) : Eisenstein := 1*((9*v)*e)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RoughRemainderArity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual rough remainder is a finite sum of independent prime
convolutions. The factorial weight, literal product and roughness cutoff
are retained. This is the second arity expansion needed for the large rows. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def roughTupleCoefficient (k : ℕ) (B : ℝ) (ψ : ℝ → ℝ) (w : ℝ)
    (n : Eisenstein) : ℂ :=
  (k.factorial:ℂ)⁻¹ * orderedConvolution (fun _ : Fin k => primeCutoff B)
    (fun _ p => 1-(ψ (norm p/w):ℂ)) n

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimeSmoothWeights
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The roughness transition in each actual semiprime norm piece belongs
to a single uniform smooth family. Capping its scale ratio at two is an
identity on the fixed norm support, so all logarithmic derivatives are
uniform even when the original ratio is unbounded. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def semiprimeSmoothWeights :
    UniformLogWeights (fun r : Ici (0:ℝ) => semiprimeSmoothWeight r) := by
  have hcont : ContDiff ℝ ∞ (Function.uncurry semiprimeSmoothWeight) := by
    exact (normPartitionWeight_smooth.comp contDiff_snd).mul
      (contDiff_const.sub (Complex.ofRealCLM.contDiff.comp
        (primeDetectorCutoff_smooth.comp (contDiff_fst.mul contDiff_snd))))
  let h := uniformLogWeights_compactParameter (Icc (0:ℝ) 2) isCompact_Icc
    semiprimeSmoothWeight normPartitionWeight normPartitionWeight_compact
    normPartitionWeight_positive_support normPartitionWeight_smooth hcont
    (fun r _ _ hx => (mul_ne_zero_iff.mp hx).1)
  let c : Ici (0:ℝ) → Icc (0:ℝ) 2 := fun r =>
    ⟨min (r:ℝ) 2,le_min r.property (by norm_num),min_le_right _ _⟩
  have he : (fun r : Ici (0:ℝ) => semiprimeSmoothWeight (c r)) =
      (fun r : Ici (0:ℝ) => semiprimeSmoothWeight r) := by
    funext r x
    exact semiprimeSmoothWeight_capped r x
  rw [← he]
  refine ⟨fun r => h.compact (c r),fun r => h.positive (c r),fun r => h.smooth (c r),
    h.radius,h.radius_nonneg,fun r => h.support_bound (c r),?_⟩
  intro n
  obtain ⟨B,hB,hbound⟩ := h.derivative_bound n
  exact ⟨B,hB,fun r => hbound (c r)⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleWeights
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single uniform smooth family for the actual distinguished-prime
weights in each large-row norm piece. Both scale ratios are capped only
after proving that the cap leaves the weight unchanged. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

def distinguishedSmoothWeights :
    UniformLogWeights (fun r : Ici (0:ℝ) × Ici (0:ℝ) =>
      distinguishedSmoothWeight ((r.1:ℝ),(r.2:ℝ))) := by
  let c : Ici (0:ℝ) × Ici (0:ℝ) → (Icc (0:ℝ) 2) ×ˢ (Icc (0:ℝ) 2) := fun r =>
    ⟨(min (r.1:ℝ) 2,min (r.2:ℝ) 2),
      ⟨⟨le_min r.1.property (by norm_num),min_le_right _ _⟩,
        ⟨le_min r.2.property (by norm_num),min_le_right _ _⟩⟩⟩
  have he : (fun r : Ici (0:ℝ) × Ici (0:ℝ) => distinguishedSmoothWeight (c r)) =
      (fun r => distinguishedSmoothWeight ((r.1:ℝ),(r.2:ℝ))) := by
    funext r x
    change distinguishedSmoothWeight (min (r.1:ℝ) 2,min (r.2:ℝ) 2) x =
      distinguishedSmoothWeight ((r.1:ℝ),(r.2:ℝ)) x
    exact distinguishedSmoothWeight_capped ((r.1:ℝ),(r.2:ℝ)) x
  rw [←he]
  exact compactDistinguishedSmoothWeights.reindex c

def largePrimeSmoothWeights : UniformLogWeights
    (fun z : (Ici (0:ℝ) × Ici (0:ℝ)) × Bool => largePrimeSmoothWeight z.1 z.2) := by
  apply UniformLogWeights.finiteCoordinates
  intro b
  cases b
  · exact semiprimeSmoothWeights.reindex (fun r : Ici (0:ℝ) × Ici (0:ℝ) => r.1)
  · exact distinguishedSmoothWeights

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleCoordinateWeights
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual independently smoothed prime coordinates of a large row
belong to one uniform family, for every norm partition and roughness scale. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment

def largeTupleCoordinateWeights (i j : ℕ) (ξ : ℝ) : UniformLogWeights
    (fun z : ({X : ℝ // 0 < X} × ((Fin i ⊕ Fin j) → ℕ)) × (Fin i ⊕ Fin j) =>
      largeTupleCoordinateWeight ξ z.1.1 z.1.2 z.2) := by
  let f : (({X : ℝ // 0 < X} × ((Fin i ⊕ Fin j) → ℕ)) × (Fin i ⊕ Fin j)) →
      (Ici (0:ℝ) × Ici (0:ℝ)) × Bool := fun z =>
    ((⟨largeTupleNormScale z.1.2 z.2/((z.1.1:ℝ)^ξ),
        div_nonneg (largeTupleNormScale_pos _ _).le (Real.rpow_nonneg z.1.1.property.le _)⟩,
      ⟨largeTupleNormScale z.1.2 z.2/((z.1.1:ℝ)^(2/5:ℝ)),
        div_nonneg (largeTupleNormScale_pos _ _).le (Real.rpow_nonneg z.1.1.property.le _)⟩),
      match z.2 with | .inl _ => true | .inr _ => false)
  have he : (fun z => largePrimeSmoothWeight (f z).1 (f z).2) =
      (fun z : ({X : ℝ // 0 < X} × ((Fin i ⊕ Fin j) → ℕ)) × (Fin i ⊕ Fin j) =>
        largeTupleCoordinateWeight ξ z.1.1 z.1.2 z.2) := by
    funext z x
    rcases z with ⟨r,a | b⟩ <;> rfl
  rw [←he]
  exact largePrimeSmoothWeights.reindex f

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleWeightLengths
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same actual coordinate weights are logarithmic families when
the length is the product of any fixed group of their scales. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def largeTupleGroupWeights {i j : ℕ} (ξ : ℝ) (s : Finset (Fin i ⊕ Fin j)) :
    UniformLogWeights (fun z : largeTupleBoxIndex i j × s => largeTupleGroupWeight ξ s z.1 z.2) :=
  (largeTupleCoordinateWeights i j ξ).reindex (fun z : largeTupleBoxIndex i j × s => (z.1.1,z.2.val))

def largeTupleGroupLogWeights {i j : ℕ} (ξ : ℝ) (s : Finset (Fin i ⊕ Fin j)) :
    LogarithmicWeightFamily
      (fun z : largeTupleBoxIndex i j × s => largeTupleGroupLength s z.1)
      (fun z => largeTupleGroupWeight ξ s z.1 z.2) := by
  let hW := largeTupleGroupWeights ξ s
  refine ⟨fun z => largeTupleGroupLength_one s z.1,hW.compact,hW.positive,hW.smooth,
    hW.radius,hW.radius_nonneg,hW.support_bound,?_⟩
  intro n
  obtain ⟨C,hC,hbound⟩ := hW.derivative_bound n
  exact ⟨C,0,hC,fun z u => by simpa only [pow_zero,mul_one] using hbound z u⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleRestrictedWeights
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual coordinate weights restricted to either predicate in a fixed
partition of the tuple indices. This preserves the predicate-subtype
indexing in the exact finite convolution identity. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {i j : ℕ} (P : (Fin i ⊕ Fin j) → Prop) [DecidablePred P]

def largeTupleRestrictedLogWeights (ξ : ℝ) :
    LogarithmicWeightFamily
      (fun z : largeTupleBoxIndex i j × {a : Fin i ⊕ Fin j // P a} =>
        largeTupleRestrictedLength P z.1)
      (fun z => largeTupleRestrictedWeight P ξ z.1 z.2) := by
  let hW := (largeTupleCoordinateWeights i j ξ).reindex
    (fun z : largeTupleBoxIndex i j × {a : Fin i ⊕ Fin j // P a} => (z.1.1,z.2.val))
  refine ⟨fun z => largeTupleRestrictedLength_one P z.1,
    hW.compact,hW.positive,hW.smooth,hW.radius,hW.radius_nonneg,hW.support_bound,?_⟩
  intro n
  obtain ⟨C,hC,hbound⟩ := hW.derivative_bound n
  exact ⟨C,0,hC,fun z u => by simpa only [pow_zero,mul_one,largeTupleRestrictedWeight] using hbound z u⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LateStopDivisor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A late ordinary stop contains the required large smooth divisor.
The divisor is the actual product of selected prime factors at or below
the roughness boundary, not an auxiliary existence hypothesis. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def lateStopDivisor (bin : Eisenstein → ℕ) (h : ℕ) (d : Eisenstein) : Eisenstein :=
  ∏ p ∈ (primaryPrimeFactors d).filter (fun p => h ≤ bin p), p

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeDyadicReconstruction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual prime sums satisfy the small-argument and local-growth
conditions of dyadic reconstruction; closed interval endpoints cost O(1). -/
noncomputable section
open Filter Asymptotics
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primeDyadicSum (c : Eisenstein → ℂ) (X : ℝ) : ℂ :=
  ∑ p ∈ primeCutoff (4*X), c p*(intervalStep X (2*X) (norm p):ℝ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTailProductMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact full-line Mellin separation for the original Gauss polynomial. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def productGaussPolynomial (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (ℓ : ℤ) (u : ℝ) : ℂ :=
  ∑ a ∈ A, ∑ b ∈ B, α a*β b*theta ℓ (a*b)*gauss (a*b)*normTwist u (a*b)

def productGaussSmoothed (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (ℓ : ℤ) (W : ℝ → ℂ) (X u : ℝ) : ℂ :=
  ∑ a ∈ A, ∑ b ∈ B,
    α a*β b*theta ℓ (a*b)*gauss (a*b)*normTwist u (a*b)*W (norm (a*b)/X)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimitiveResidueFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The perfect codifferent pairing on every Eisenstein residue ring.
Unlike the trace pairing without the different, this includes ramified moduli. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

/-- The finite Fourier transform of the actual residue multiplicative character. -/
def residueCharacterFourier (q : Eisenstein) (hq : q ≠ 0)
    [Fintype (Residues q)] (χ : MulChar (Residues q) ℂ) (a : Residues q) : ℂ :=
  gaussSum χ ((residueFourierChar q hq).mulShift a)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueHarmonicPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Periodic Poisson for the actual positive and negative angular
polynomial Gaussians. The finite Fourier coefficient is retained exactly. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def residueHarmonicTheta (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (A : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  ∑' z : Eisenstein, χ (Ideal.Quotient.mk (modulus q) z)*
    ((z:ℂ)^n*(Real.exp (-norm z*t/A):ℝ))

def residueAntiHarmonicTheta (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (A : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  ∑' z : Eisenstein, χ (Ideal.Quotient.mk (modulus q) z)*
    ((star (z:ℂ))^n*(Real.exp (-norm z*t/A):ℝ))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SieveResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The residue sum after squarefree majorization

The actual collected coefficients agree with Möbius below the truncation.
Their uniformly convergent norm series therefore differs from the true
Möbius residue by `O(D⁻¹ᐟ²)`.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def squarefreeSieveResidueTerm (D : ℝ) (e : Eisenstein) : ℝ :=
  if primary e then
    collectedSquarefreeSieveCoefficient (squarefreeDivisorTruncation D) e / (norm e)^2
  else 0

def moebiusResidueTerm (e : Eisenstein) : ℝ :=
  if primary e then (idealMoebius e : ℝ)/(norm e)^2 else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SievedModelAssembly
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite sieve assembly and its error norm. These identities
retain the actual joined square divisors and their Möbius weights. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def finiteSieveDensity (C : Finset Eisenstein) : ℝ :=
  ∑ c ∈ C, ∑ d ∈ C, (idealMoebius c:ℝ)*(idealMoebius d:ℝ)/
    (norm (primarySquarefreeJoin c d))^2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimeGaussTailAngularWeights
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual semiprime coordinates as a uniform smooth prime-weight family.
The angular factor remains separate from the radial weight throughout. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

def semiprimeAngularLeftLogWeights :
    LogarithmicWeightFamily
      (fun z : SemiprimeAngularWeightParameters × Unit => semiprimeAngularLeftLength z.1)
      (fun z => semiprimeAngularLeftWeight z.1 z.2) :=
  uniformLogWeights_prime_coordinates semiprimeAngularLeftLength
    (fun z => semiprimeSmoothWeight z.1.1) (fun z => z.1.2.property)
    (semiprimeSmoothWeights.reindex (fun z : SemiprimeAngularWeightParameters => z.1.1))

def semiprimeAngularRightLogWeights :
    LogarithmicWeightFamily
      (fun z : SemiprimeAngularWeightParameters × Unit => semiprimeAngularRightLength z.1)
      (fun z => semiprimeAngularRightWeight z.1 z.2) :=
  uniformLogWeights_prime_coordinates semiprimeAngularRightLength
    (fun z => semiprimeSmoothWeight z.2.1) (fun z => z.2.2.property)
    (semiprimeSmoothWeights.reindex (fun z : SemiprimeAngularWeightParameters => z.2.1))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimeGaussTailWeights
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both analytic height ranges on the original smooth rough-prime weights.
The parameter families retain their actual transition ratios. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def semiTailLeftFamily :
    LogarithmicWeightFamily (fun z : SemiprimeTailParameters × Unit => semiTailLeft z.1)
      (fun z => semiTailLeftWeight z.1 z.2) :=
  uniformLogWeights_prime_coordinates semiTailLeft
    (fun z => semiprimeSmoothWeight z.1.1) (fun z => z.1.2.property)
    (semiprimeSmoothWeights.reindex (fun z : SemiprimeTailParameters => z.1.1))

def semiTailRightFamily :
    LogarithmicWeightFamily (fun z : SemiprimeTailParameters × Unit => semiTailRight z.1)
      (fun z => semiTailRightWeight z.1 z.2) :=
  uniformLogWeights_prime_coordinates semiTailRight
    (fun z => semiprimeSmoothWeight z.2.1) (fun z => z.2.2.property)
    (semiprimeSmoothWeights.reindex (fun z : SemiprimeTailParameters => z.2.1))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SparseLateSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal sparse-support count: primary numbers containing a large
squarefree divisor made from small primes occupy a power-saving fraction
of a norm ball. The multiple count is the proved Eisenstein lattice bound. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def sparseLateSupport (X C η B : ℝ) : Finset Eisenstein :=
  (primaryElementBall B).filter (fun b => ∃ d : Eisenstein,
    primary d ∧ Squarefree d ∧ d ∣ b ∧ X^η ≤ norm d ∧
      ∀ p ∈ primaryPrimeFactors d, norm p ≤ (Real.log X)^C)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPointMeasureLocallyFinite
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hyperbolic measure is finite on each compact positive-height set;
the singularity at height zero stays outside every such compact set. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

instance cubicThetaPointMeasure_finiteOnCompacts : IsFiniteMeasureOnCompacts cubicThetaPointMeasure :=
  ⟨fun _K hK => cubicThetaPointMeasure_compact hK⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticRowSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reindex the literal theta expansion on the actual three-Eisenstein
period lattice. Coefficients off this lattice vanish by their ramified
support, so this change of variables introduces no multiplicity. -/
noncomputable section
open Set
namespace CubicFirstMoment

lemma cubicThetaRowIndex_injective :
    Function.Injective (fun h : Eisenstein => -lambdaE*h) := by
  intro h k he
  exact mul_left_cancel₀ (neg_ne_zero.mpr lambdaE_prime.ne_zero) he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedInvertedRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primitive rows at the translated inverted cusps used by the primary
coefficient projector. The phase is kept as the actual cubic symbol; its
ramified evaluation is a subsequent arithmetic step. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicTheta_primary_add_three_mul {c d : Eisenstein} (hc : primary c)
    (hd : (3:Eisenstein)∣d) (b : Eisenstein) : primary (c+b*d) := by
  obtain ⟨t,ht⟩ := hc
  obtain ⟨u,hu⟩ := hd
  refine ⟨t+b*u,?_⟩
  linear_combination ht+b*hu

def cubicThetaShiftedInvertedRowEquiv (b : Eisenstein) :
    CubicThetaBottomRow ≃ CubicThetaInvertedRow where
  toFun r := {
    c := r.d+b*r.c
    d := -r.c
    c_primary := cubicTheta_primary_add_three_mul r.d_primary r.c_three b
    d_three := dvd_neg.mpr r.c_three
    coprime := by
      obtain ⟨u,v,h⟩ := r.coprime
      refine ⟨v,v*b-u,?_⟩
      linear_combination h }
  invFun r := {
    c := -r.d
    d := r.c+b*r.d
    c_three := dvd_neg.mpr r.d_three
    d_primary := cubicTheta_primary_add_three_mul r.c_primary r.d_three b
    coprime := by
      obtain ⟨u,v,h⟩ := r.coprime
      refine ⟨u*b-v,u,?_⟩
      linear_combination h }
  left_inv r := by ext <;> dsimp <;> ring
  right_inv r := by ext <;> dsimp <;> ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedCuspPeriodicity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Periodicity of the actual translated-cusp row phase. Conjugating a
translation by the cusp matrix gives a principal level-nine matrix with
trivial Kubota value, proved from the supplementary laws. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaCuspTranslationMatrix (b m : Eisenstein) : SL(2,Eisenstein) :=
  ⟨!![1-9*b*m,9*b^2*m;-9*m,1+9*b*m],by
    rw [Matrix.det_fin_two_of]
    ring⟩

lemma cubicThetaCuspTranslationMatrix_mem (b m : Eisenstein) :
    cubicThetaCuspTranslationMatrix b m ∈ cubicThetaPrincipalGroup := by
  apply (cubicThetaPrincipalGroup_mem_iff _).mpr
  change primary (1-9*b*m) ∧ (3:Eisenstein)∣9*b^2*m ∧
    (3:Eisenstein)∣-9*m ∧ primary (1+9*b*m)
  exact ⟨⟨-3*b*m,by ring⟩,⟨3*b^2*m,by ring⟩,⟨-3*m,by ring⟩,⟨3*b*m,by ring⟩⟩

def cubicThetaCuspTranslation (b m : Eisenstein) : cubicThetaPrincipalGroup :=
  ⟨cubicThetaCuspTranslationMatrix b m,cubicThetaCuspTranslationMatrix_mem b m⟩

lemma cubicThetaCuspTranslation_value (b m : Eisenstein) :
    cubicThetaKubotaValue (cubicThetaCuspTranslation b m)=1 := by
  unfold cubicThetaKubotaValue
  split_ifs
  · rfl
  · change cubicSymbol (1-9*b*m) (-9*m)=1
    apply cubicThetaKubota_symbol_one
    · exact ⟨-3*b*m,by ring⟩
    · exact ⟨-b*m,by ring⟩
    · exact ⟨b,by ring⟩

def cubicThetaShiftedRowTranslate (r : CubicThetaInvertedRow) (m : Eisenstein) :
    CubicThetaInvertedRow where
  c := r.c
  d := r.d+9*m*r.c
  c_primary := r.c_primary
  d_three := dvd_add r.d_three ⟨3*m*r.c,by ring⟩
  coprime := by
    obtain ⟨u,v,h⟩ := r.coprime
    refine ⟨u-9*m*v,v,?_⟩
    linear_combination h

def cubicThetaShiftedRowPhase (b : Eisenstein) (r : CubicThetaInvertedRow) : ℂ :=
  cubicSymbol (r.c+b*r.d) r.d

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedRowWeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Zero-extended periodic weights of the translated inverted rows.
The finite residue modulus is `3*c` in the variable `d=3*u`. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicTheta_coprime_add_left (c d b : Eisenstein) :
    IsCoprime (c+b*d) d ↔ IsCoprime c d := by
  constructor
  · rintro ⟨u,v,h⟩
    refine ⟨u,u*b+v,?_⟩
    linear_combination h
  · rintro ⟨u,v,h⟩
    refine ⟨u,v-u*b,?_⟩
    linear_combination h

lemma cubicTheta_coprime_add_right (c d b : Eisenstein) :
    IsCoprime c (d+b*c) ↔ IsCoprime c d := by
  rw [isCoprime_comm,cubicTheta_coprime_add_left,isCoprime_comm]

def cubicThetaShiftedRowWeight (b c u : Eisenstein) : ℂ :=
  cubicSymbol (c+b*(3*u)) (3*u)

def cubicThetaShiftedResidueWeight (b c : Eisenstein) (x : Residues (3*c)) : ℂ :=
  cubicThetaShiftedRowWeight b c (residueRepresentative (3*c) x)

def cubicThetaShiftedGaussCoefficient (b c h : Eisenstein) : ℂ :=
  ∑' x : Residues (3*c), cubicThetaShiftedResidueWeight b c x*
    (Real.fourierChar (tracePair (residueRepresentative (3*c) x:ℂ)
      ((h:ℂ)/(((3*c:Eisenstein):ℂ)*traceLambda))):ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspStep
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three-step translation character of a shifted cusp. It supplies
the ramified finite Fourier factor before the unramified Gauss sum. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaCuspStepMatrix (b m : Eisenstein) : SL(2,Eisenstein) :=
  ⟨!![1-3*b*m,3*b^2*m;-3*m,1+3*b*m],by rw [Matrix.det_fin_two_of]; ring⟩

lemma cubicThetaCuspStepMatrix_mem (b m : Eisenstein) :
    cubicThetaCuspStepMatrix b m∈cubicThetaPrincipalGroup := by
  apply (cubicThetaPrincipalGroup_mem_iff _).mpr
  change primary (1-3*b*m) ∧ (3:Eisenstein)∣3*b^2*m ∧
    (3:Eisenstein)∣-3*m ∧ primary (1+3*b*m)
  exact ⟨⟨-b*m,by ring⟩,⟨b^2*m,by ring⟩,⟨-m,by ring⟩,⟨b*m,by ring⟩⟩

def cubicThetaCuspStep (b m : Eisenstein) : cubicThetaPrincipalGroup :=
  ⟨cubicThetaCuspStepMatrix b m,cubicThetaCuspStepMatrix_mem b m⟩

lemma cubicThetaCuspStep_add (b m n : Eisenstein) :
    cubicThetaCuspStep b (m+n)=cubicThetaCuspStep b m*cubicThetaCuspStep b n := by
  apply Subtype.ext
  apply Subtype.ext
  change (!![1-3*b*(m+n),3*b^2*(m+n);-3*(m+n),1+3*b*(m+n)] : Matrix (Fin 2) (Fin 2) Eisenstein)=
    !![1-3*b*m,3*b^2*m;-3*m,1+3*b*m]*!![1-3*b*n,3*b^2*n;-3*n,1+3*b*n]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two] <;> ring

lemma cubicThetaCuspStep_triple (b m : Eisenstein) :
    cubicThetaCuspStep b (3*m)=cubicThetaCuspTranslation b m := by
  apply Subtype.ext
  apply Subtype.ext
  change (!![1-3*b*(3*m),3*b^2*(3*m);-3*(3*m),1+3*b*(3*m)] : Matrix (Fin 2) (Fin 2) Eisenstein)=
    !![1-9*b*m,9*b^2*m;-9*m,1+9*b*m]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num <;> ring

def cubicThetaCuspStepValue (b m : Eisenstein) : ℂ :=
  cubicThetaKubotaValue (cubicThetaCuspStep b m)

lemma cubicThetaCuspStepValue_add (b m n : Eisenstein) :
    cubicThetaCuspStepValue b (m+n)=cubicThetaCuspStepValue b m*cubicThetaCuspStepValue b n := by
  unfold cubicThetaCuspStepValue
  rw [cubicThetaCuspStep_add,cubicThetaKubotaValue_mul]

lemma cubicThetaCuspStepValue_triple (b m : Eisenstein) : cubicThetaCuspStepValue b (3*m)=1 := by
  rw [cubicThetaCuspStepValue,cubicThetaCuspStep_triple,cubicThetaCuspTranslation_value]

def cubicThetaShiftedRowStep (r : CubicThetaInvertedRow) (m : Eisenstein) :
    CubicThetaInvertedRow where
  c := r.c
  d := r.d+3*m*r.c
  c_primary := r.c_primary
  d_three := dvd_add r.d_three ⟨m*r.c,by ring⟩
  coprime := (cubicTheta_coprime_add_right r.c r.d (3*m)).mpr r.coprime

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeValuation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unique separation of an unramified prime power in an actual admissible
Eisenstein denominator. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaPrimePower_unique {p c d : Eisenstein} (hp : p≠0)
    (hc : ¬p ∣ c) (hd : ¬p ∣ d) {n m : ℕ} (he : p^n*c=p^m*d) : n=m ∧ c=d := by
  have hle {n m : ℕ} {c d : Eisenstein} (hc : ¬p ∣ c)
      (he : p^n*c=p^m*d) (hnm : n ≤ m) : n=m ∧ c=d := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hnm
    have hcd : c=p^k*d := by
      apply mul_left_cancel₀ (pow_ne_zero n hp)
      rw [← mul_assoc,← pow_add]
      exact he
    have hk : k=0 := by
      by_contra hk
      apply hc
      rw [hcd]
      exact dvd_mul_of_dvd_left (dvd_pow_self p hk) d
    subst k
    exact ⟨by omega,by simpa using hcd⟩
  rcases le_total n m with hnm | hmn
  · exact hle hc he hnm
  · obtain ⟨hn,hcd⟩ := hle hd he.symm hmn
    exact ⟨hn.symm,hcd.symm⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The five possible local rows at a cubically multiplied frequency. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaNormPower_cpow (p d : Eisenstein) (n : ℕ) (s : ℂ) :
    (norm (p^n*d):ℂ)^(-s)=((norm p:ℂ)^(-s))^n*(norm d:ℂ)^(-s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',mul_assoc,norm_mul_eq,Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (norm_nonneg p) (norm_nonneg (p^n*d)),ih,pow_succ']
    ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeHeckeContinuation
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local three-frequency identity holds for the actual meromorphic
continuation, hence for its holomorphic pole-cleared representative. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

lemma cubicThetaPrimeNormPower_analytic {p : Eisenstein} (hp : primaryPrime p) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => (norm p:ℂ)^(-z)) s := by
  let _ : NeZero (norm p:ℂ) := ⟨Complex.ofReal_ne_zero.mpr
    (norm_pos_of_ne_zero hp.2.ne_zero).ne'⟩
  exact ((differentiable_const_cpow_of_neZero (norm p:ℂ)).analyticAt _).comp
    (f:=fun z : ℂ => -z) (x:=s) analyticAt_id.neg

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimePoleFactors
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact normalization of the unramified three-frequency relation at
the theta pole. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeFactor_pole {p : Eisenstein} (hp : primaryPrime p) :
    (norm p:ℂ)^3*((norm p:ℂ)^(-(4/3:ℂ)))^3=(norm p:ℂ)⁻¹ := by
  have hq : (norm p:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_pos_of_ne_zero hp.2.ne_zero).ne'
  rw [← Complex.cpow_mul_nat]
  norm_num only [show (-(4/3:ℂ))*(3:ℕ)=-(4:ℂ) by norm_num]
  rw [Complex.cpow_neg,show (4:ℂ)=((4:ℕ):ℂ) by rfl,Complex.cpow_natCast]
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit additive character at an integral translated cusp. Its
frequency is determined by the omega coordinate of the translation. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaCuspCharacter (b : Eisenstein) : AddChar Eisenstein ℂ where
  toFun := cubicThetaCuspStepValue b
  map_zero_eq_one' := by
    simpa only [mul_zero] using cubicThetaCuspStepValue_triple b 0
  map_add_eq_mul' := cubicThetaCuspStepValue_add b

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGaussianTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonzero unweighted lattice Gaussian, with its exact ideal multiplicity
and exponential decay. -/
noncomputable section
open scoped Topology
open Filter Asymptotics
namespace CubicFirstMoment

def cubicThetaLatticeGaussianTail (t : ℝ) : ℝ :=
  ∑' a : {a : Eisenstein // a≠0}, Real.exp (-t*norm a.val)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGaussianPowerBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A global quadratic decay bound for the nonzero Gaussian lattice tail. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaGaussianPowerConstant : ℝ :=
  2*∑' a : {a : Eisenstein // a≠0},(norm a.val)^(-2:ℝ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarGaussian
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unweighted Gaussian on the affine level-three lattice. This is the
scalar Poisson kernel used to compute the height-series residue. -/
noncomputable section
open scoped SchwartzMap
namespace CubicFirstMoment

def cubicThetaScalarGaussian (z : ℂ) (t : ℝ) : ℂ :=
  ∑' a : Eisenstein,(Real.exp (-t*Complex.normSq (z+3*(a:ℂ))):ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarGaussianReal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real positive form of the scalar lattice Gaussian and its uniform bound. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaScalarGaussianReal (z : ℂ) (t : ℝ) : ℝ :=
  ∑' a : Eisenstein,Real.exp (-t*Complex.normSq (z+3*(a:ℂ)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGaussianLinearTail
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform inverse-linear bound for the nonzero lattice heat sum.
It controls the nonzero first coordinate in the reduced cusp. -/
noncomputable section
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaGaussianLinearConstant : ℝ :=
  cubicThetaGaussianPowerConstant+(2*Real.pi/Real.sqrt 3)*
    (1+cubicThetaGaussianPowerConstant/(4*Real.pi^2/3)^2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspHeatBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform Gaussian control of rows with nonzero first coordinate in a
fixed-height cusp. This estimate precedes the scalar Rankin domination. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaNonzeroFirstHeat (p : ℂ × ℝ) (t : ℝ) : ℝ :=
  ∑' c : {c : Eisenstein // c≠0},Real.exp (-(t*p.2)*norm c.val)*
    cubicThetaScalarGaussianReal (3*(c.val:ℂ)*p.1) (t/(9*p.2))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaKubotaConjugation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Invariance of the cubic multiplier under the two integral modular
generators, as needed to extend it to the group of DR v3 Section 5.1. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaKubotaConjugate (u : SL(2,Eisenstein)) (g : cubicThetaPrincipalGroup) :
    cubicThetaPrincipalGroup :=
  ⟨u*g.val*u⁻¹,by
    have hg : Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (modulus (3:Eisenstein))) g.val = 1 :=
      g.property
    change Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (modulus (3:Eisenstein)))
      (u*g.val*u⁻¹) = 1
    rw [map_mul,map_mul,map_inv,hg,mul_one,mul_inv_cancel]⟩

def cubicThetaModularS : SL(2,Eisenstein) :=
  ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩

def cubicThetaModularT : SL(2,Eisenstein) :=
  ⟨!![1,1;0,1],by simp [Matrix.det_fin_two]⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaKubotaInteger
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Invariance under the whole integer modular group, derived from its
proved S,T generation and the two explicit reciprocity calculations. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaIntegerEmbedding : SL(2,ℤ) →* SL(2,Eisenstein) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom Eisenstein)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPointMeasurePositive
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual hyperbolic measure is positive on every nonempty open
subset of the positive-height space. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

instance cubicThetaPointMeasure_openPositive :
    Measure.IsOpenPosMeasure cubicThetaPointMeasure where
  open_pos U hU hne := by
    have hopen : IsOpen (cubicThetaPointCoordinates '' U) :=
      (isOpen_lt continuous_const continuous_snd).isOpenEmbedding_subtypeVal.isOpenMap U hU
    have he : {y : ℂ × ℝ | cubicThetaHyperbolicDensity y≠0} ∩
        (cubicThetaPointCoordinates '' U)=cubicThetaPointCoordinates '' U := by
      apply inter_eq_right.mpr
      rintro y ⟨p,hp,rfl⟩
      change ENNReal.ofReal ((p.val.2^3)⁻¹)≠0
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos p.property 3)))
    rw [cubicThetaPointMeasure_apply hU.measurableSet,cubicThetaHyperbolicMeasure]
    intro hz
    have hh := (withDensity_apply_eq_zero (μ:=(volume : Measure (ℂ × ℝ)))
      (s:=cubicThetaPointCoordinates '' U) cubicThetaHyperbolicDensity_measurable).mp hz
    rw [he] at hh
    exact hopen.measure_ne_zero volume (hne.image _) hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveHeightBand
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive lower height cutoffs, needed when Hecke dilations move a
compact Poincare profile below the unit cusp height. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaRows_compact_below {ε : ℝ} (hε : 0<ε)
    {K : Set (ℂ × ℝ)} (hK : IsCompact K) (hpos : ∀ p∈K,0<p.2) :
    ∃ S : Finset CubicThetaBottomRow,∀ p∈K,∀ r∉S,r.height p<ε := by
  classical
  have hc : ContinuousOn (fun p : ℂ × ℝ => p.2*cubicThetaHeightConstant p/ε) K := by
    intro p hp
    unfold cubicThetaHeightConstant
    fun_prop (disch := first | exact hε.ne' | exact pow_ne_zero _ (hpos p hp).ne')
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hc
  have hi : Function.Injective (fun r : CubicThetaBottomRow => (r.c,r.d)) := by
    intro r t h
    exact CubicThetaBottomRow.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hfin : {r : CubicThetaBottomRow | norm r.c≤B ∧ norm r.d≤B}.Finite :=
    ((finite_norm_le B).prod (finite_norm_le B)).preimage hi.injOn
  refine ⟨hfin.toFinset,?_⟩
  intro p hp r hr
  apply lt_of_not_ge
  intro hhigh
  have hn : 0<1+norm r.c+norm r.d := by linarith [norm_nonneg r.c,norm_nonneg r.d]
  have hrow : 1+norm r.c+norm r.d≤p.2*cubicThetaHeightConstant p/ε := by
    apply (le_div_iff₀ hε).mpr
    nlinarith [(le_div_iff₀ hn).mp (hhigh.trans (r.height_le (hpos p hp)))]
  have hb : p.2*cubicThetaHeightConstant p/ε≤B := (le_abs_self _).trans (hB p hp)
  apply hr
  apply hfin.mem_toFinset.mpr
  constructor <;> linarith [norm_nonneg r.c,norm_nonneg r.d]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSieveSupport
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact primary coefficient selector of DR v3 (5.17)--(5.18). -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaRootProjector (z : ℂ) : ℂ := (1+omega*z+omega^2*z^2)/3

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryIndex
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unique indexing of the primary theta frequencies by the original
squarefree and cube variables. There is no multiplicity factor. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaPrimaryNumerator (cd : CubicThetaPrimaryPair) : Eisenstein :=
  lambdaE*cd.val.1*cd.val.2^3

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedMiddleSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exactly two unit classes can contribute to the middle ramified row
above a frequency congruent to one modulo lambda. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaLambda_dvd_omega_pow_sub_one (k : ℕ) : lambdaE∣omegaE^k-1 := by
  have h1 : lambdaE∣omegaE-1 := by
    refine ⟨1+omegaE,?_⟩
    dsimp only [lambdaE]
    linear_combination -2*omegaE_quadratic
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ,show omegaE^k*omegaE-1=omegaE^k*(omegaE-1)+(omegaE^k-1) by ring]
    exact dvd_add (dvd_mul_of_dvd_right h1 _) ih

lemma cubicThetaThree_dvd_lambda_mul (h : Eisenstein) :
    (3:Eisenstein)∣lambdaE*h ↔ lambdaE∣h := by
  rw [show (3:Eisenstein)=-(lambdaE*lambdaE) by rw [←pow_two,lambdaE_sq]; ring,
    neg_dvd,mul_dvd_mul_iff_left lambdaE_prime.ne_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedPrimarySupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Away from lambda, the literal frequency series is supported on the
two signed primary classes. This is a finite ramified selection rule. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

lemma unit_ramified_primary_congruence (r : Fin 3) :
    (3:Eisenstein) ∣ omegaE^(r:ℕ)*(4+lambdaE*(r:ℕ))-1 := by
  fin_cases r
  · exact ⟨1,by norm_num⟩
  · refine ⟨omegaE-1,?_⟩
    norm_num only [Fin.val_one,pow_one,Nat.cast_one,mul_one]
    dsimp only [lambdaE]
    linear_combination 2*omegaE_quadratic
  · refine ⟨-1-2*omegaE,?_⟩
    norm_num only [Fin.val_ofNat,Nat.cast_ofNat]
    dsimp only [lambdaE]
    linear_combination (4*omegaE+2)*omegaE_quadratic

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryUnitResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The base residue on the six-unit orbit of a primary frequency is
supported precisely on the two signed primary representatives. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaPrimary_mul_unit_iff {h : Eisenstein} (hh : primary h)
    (e : Eisensteinˣ) : primary (h*(e:Eisenstein)) ↔ e=1 := by
  constructor
  · intro hp
    have h3 : (3:Eisenstein)∣(e:Eisenstein)-1 := by
      convert dvd_sub hp (dvd_mul_of_dvd_left hh (e:Eisenstein)) using 1
      all_goals try with_reducible_and_instances rfl
      ring
    exact Units.ext (primary_unit_eq_one e.isUnit h3)
  · rintro rfl
    simpa using hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeAdditiveGauss
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite cubic Gauss factors with the additive character of the original
arithmetic normalization. These are the off-diagonal finite factors needed
in the unramified critical intertwining calculation. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaPrimeAdditiveGauss (p : Eisenstein) (hp : primaryPrime p)
    (n : ℕ) (h : Eisenstein) : ℂ :=
  ∑' y : Residues p, (cubicResidueChar p hp y)^n*
    residueAddChar p hp.2.ne_zero (Ideal.Quotient.mk (modulus p) h*y)

lemma cubicThetaPrimeAdditiveGauss_one {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : IsCoprime p h) :
    cubicThetaPrimeAdditiveGauss p hp 1 h=
      star (cubicSymbol p h)*(Real.sqrt (norm p):ℂ)*gauss p := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  obtain ⟨u,hu⟩ := residue_isUnit_of_isCoprime hh
  have he : Ideal.Quotient.mk (modulus p) h=(u:Residues p) := hu.symm
  have hg : cubicThetaPrimeAdditiveGauss p hp 1 h=
      gaussSum (cubicResidueChar p hp)
        ((residueAddChar p hp.2.ne_zero).mulShift (Ideal.Quotient.mk (modulus p) h)) := by
    simp only [cubicThetaPrimeAdditiveGauss,tsum_fintype,gaussSum,pow_one,AddChar.mulShift_apply]
  rw [hg,he,gaussSum_mulShift_eq,←MulChar.star_apply',hu,cubicResidueChar_mk,←cubicSymbol_prime hp]
  have hn : gaussSum (cubicResidueChar p hp) (residueAddChar p hp.2.ne_zero)=
      (Real.sqrt (norm p):ℂ)*gauss p := by
    rw [gauss_prime hp,gaussAtPrime_eq_gaussSum hp]
    have hq : (Real.sqrt (norm p):ℂ)≠0 := Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.sqrt_pos.mpr (norm_pos_of_ne_zero hp.2.ne_zero)))
    rw [mul_inv_cancel_left₀ hq]
  rw [hn]
  ring

lemma cubicThetaPrimeAdditiveGauss_norm {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : IsCoprime p h) :
    ‖cubicThetaPrimeAdditiveGauss p hp 1 h‖=Real.sqrt (norm p) := by
  rw [cubicThetaPrimeAdditiveGauss_one hp h hh,norm_mul,norm_mul,norm_star,
    norm_cubicSymbol_of_isCoprime hp.1 hh,gauss_prime hp,norm_gaussAtPrime hp,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),one_mul,mul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTwistFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Fourier inversion for the periodic numerator twists in the
cubic theta formula. The trace pairing is perfect for primary moduli. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

/-- The source trace character, without the inverse-different factor.
For primary q the removed factor is a unit modulo q. -/
def cubicThetaResidueChar (q : Eisenstein) (hq : q ≠ 0) : AddChar (Residues q) ℂ :=
  (residueFourierChar q hq).mulShift (Ideal.Quotient.mk (modulus q) lambdaE)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamanujan
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Ramanujan sum in the trace normalization of the actual
cubic theta series. Its weight is the cube of the cubic residue character. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaRamanujan (r h : Eisenstein) : ℂ :=
  ∑' x : Residues r,cubicSymbol r (residueRepresentative r x)^3*
    additivePhase r (h*residueRepresentative r x)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedTopPhase
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected top-row contribution has the same explicit phase as
the middle-row eigenvector. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment


lemma cubicThetaTopUnit_congruence (j : Fin 3) :
    (3:Eisenstein)∣(omegaE^(j:ℕ))^2+2+lambdaE*(cubicThetaInverseUnitIndex j:ℕ) := by
  fin_cases j
  · refine ⟨1,?_⟩
    norm_num [cubicThetaInverseUnitIndex]
  · refine ⟨1+omegaE,?_⟩
    norm_num [cubicThetaInverseUnitIndex]
    dsimp only [lambdaE]
    linear_combination omegaE_quadratic
  · refine ⟨1+omegaE,?_⟩
    norm_num [cubicThetaInverseUnitIndex]
    dsimp only [lambdaE]
    linear_combination (omegaE^2-omegaE)*omegaE_quadratic

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarEisenstein
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar Eisenstein series for the same principal arithmetic group.
It supplies the positive height kernel for the energy unfolding. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaScalarEisenstein (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  ∑' r : CubicThetaBottomRow,(r.height p:ℂ)^s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedCuspGaussian
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Poisson summation at each translated inverted cusp. The true period
is 3c in the row variable and the dual frequency is h/(9 lambda). -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaShiftedCuspGaussianRow (b c : Eisenstein) (z : ℂ) (t : ℝ) : ℂ :=
  ∑' a : Eisenstein, cubicThetaShiftedRowWeight b c a*
    (Real.exp (-t*‖z+3*(a:ℂ)/(c:ℂ)‖^2):ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedHeatSummability
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The frequency and summable heat majorant at the translated cusps. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaShiftedRowFrequency (h : Eisenstein) : ℂ := (h:ℂ)/(9*traceLambda)

def cubicThetaShiftedRowHeatScale (h : Eisenstein) : ℝ :=
  4*Real.pi^2*Complex.normSq (cubicThetaShiftedRowFrequency h)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedRowMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian Mellin representation of the actual rows at a translated
inverted cusp, retaining their finite ramified character. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaShiftedRowSeries (b c : Eisenstein) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  ∑' a : Eisenstein, cubicThetaShiftedRowWeight b c a*
    ((p.2/(Complex.normSq ((c:ℂ)*p.1+(3*a:Eisenstein))+norm c*p.2^2):ℝ):ℂ)^s

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedRowFourier
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaShiftedRowFourierCoefficient (b c : Eisenstein) (z : ℂ) (h : Eisenstein) : ℂ :=
  cubicThetaShiftedGaussCoefficient b c h*
    (Real.fourierChar (tracePair z (cubicThetaShiftedRowFrequency h)):ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedFrequencyBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute arithmetic and heat majorants for collecting the actual
inverted Fourier coefficients on their half-plane of convergence. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaShiftedFrequencyTerm (b : Eisenstein) (s : ℂ) (h c : Eisenstein) : ℂ :=
  if primary c then cubicThetaShiftedGaussCoefficient b c h*(norm c:ℂ)^(-s) else 0

end CubicFirstMoment

end

end OAI
end


