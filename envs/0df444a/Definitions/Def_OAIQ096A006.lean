-- Prove2me | Definitions.Def_OAIQ096A006
-- name    : OAIQ096A006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T03:32:38.121489+00:00
-- url     : https://prove2.me/theorems/eb9d3384-59d0-46f1-af38-20442c807cb6
-- title:
--   Definitions bundle OAIQ096A006 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 247 declarations of OpenAI's Lean: 100 definitions, 1 inductive type or structure, 8 instances and 138 theorems. The definitions and types are `OAI.CubicFirstMoment.cubicThetaAxisSecond`, `OAI.CubicFirstMoment.cubicThetaCutoffHeight`, `OAI.CubicFirstMoment.cubicThetaExpConstant`, `OAI.CubicFirstMoment.cubicThetaHighWindowFluxDensity`, `OAI.CubicFirstMoment.cubicThetaHighWindowForcing`, `OAI.CubicFirstMoment.cubicThetaHighWindowWeight`, `OAI.CubicFirstMoment.cubicThetaIncomingWindowCutoff`, `OAI.CubicFirstMoment.cubicThetaIntegerBox`, `OAI.CubicFirstMoment.cubicThetaIntegerQuadratic`, `OAI.CubicFirstMoment.cubicThetaIntegerRadius`, `OAI.CubicFirstMoment.cubicThetaInversion`, `OAI.CubicFirstMoment.cubicThetaLongWindowDefect`, `OAI.CubicFirstMoment.cubicThetaLongWindowHeight`, `OAI.CubicFirstMoment.cubicThetaLongWindowWeight`, `OAI.CubicFirstMoment.cubicThetaPointC1`, `OAI.CubicFirstMoment.cubicThetaPointC1Gradient`, `OAI.CubicFirstMoment.cubicThetaPointFunction`, `OAI.CubicFirstMoment.cubicThetaPrimaryBoxWeight`, `OAI.CubicFirstMoment.cubicThetaPrimaryDerivativeWeight`, `OAI.CubicFirstMoment.cubicThetaPrimaryQuadratic`, `OAI.CubicFirstMoment.cubicThetaPrimaryTailMass`, `OAI.CubicFirstMoment.cubicThetaRamifiedBoxWeight`, `OAI.CubicFirstMoment.cubicThetaRamifiedDerivativeWeight`, `OAI.CubicFirstMoment.cubicThetaRamifiedTailMass`, `OAI.CubicFirstMoment.cubicThetaTangentValues`, `OAI.CubicFirstMoment.cubicThetaWindowDefect`, `OAI.CubicFirstMoment.cubicThetaWindowFlux`, `OAI.CubicFirstMoment.cubicThetaWindowHeight`, `OAI.CubicFirstMoment.cubicWhittakerDerivativePowerConstant`, `OAI.CubicFirstMoment.cubicWhittakerEnergyMass`, `OAI.CubicFirstMoment.cubicWhittakerNormMass`, `OAI.CubicFirstMoment.distinguishedStoppingWeights`, `OAI.CubicFirstMoment.divisorCharacterGram`, `OAI.CubicFirstMoment.dyadicFourierMultiplier`, `OAI.CubicFirstMoment.endpointProfile`, `OAI.CubicFirstMoment.farFourierKernel`, `OAI.CubicFirstMoment.farInverseSquare`, `OAI.CubicFirstMoment.farInverseSquareReal`, `OAI.CubicFirstMoment.farMellinKernel`, `OAI.CubicFirstMoment.finiteCoverCoefficient` and 61 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `CubicGram_CommonFactors`, `CubicGram_Coordinates`, `CubicGram_CubeEstimates`, `CubicGram_CubicOperator`, `CubicGram_GramPoisson`, `CubicGram_InnerExtension`, `CubicGram_MellinDecay`, `CubicGram_PeriodicPoisson`, `CubicGram_SquarefreeGauss`, `CubicMoment_Decomposition_DistinguishedStoppingWeights`, `CubicMoment_Decomposition_StoppedBinDecomposition`, `CubicMoment_Decomposition_StoppedProductMellinPhase`, `CubicMoment_Decomposition_StoppedProductProfile`, `CubicMoment_Estimates_CubicDyadicCoverage`, `CubicMoment_Estimates_CubicWhittakerBounds`, `CubicMoment_Estimates_CubicWhittakerDerivative`, `CubicMoment_Estimates_CubicWhittakerEnergy`, `CubicMoment_Estimates_CubicWhittakerExponential`, `CubicMoment_Estimates_DivisorDispersion`, `CubicMoment_Estimates_FarFourierSeparation`, `CubicMoment_Estimates_FarInverseSquare`, `CubicMoment_Estimates_FarMellinKernel`, `CubicMoment_Estimates_FourierCutoff`, `CubicMoment_Estimates_HeckeDualContour`, `CubicMoment_Estimates_HeckeDualMoment`, `CubicMoment_Estimates_HeckeDyadicMoment`, `CubicMoment_Estimates_HeckeSymmetry`, `CubicMoment_Estimates_HeightEndpointProfile`, `CubicMoment_Estimates_HeightEndpointRegularity`, `CubicMoment_Estimates_HuxleyFiniteDual`, `CubicMoment_Estimates_HuxleyGaussianCoordinates`, `CubicMoment_Estimates_IdealDirichletInverse`, `CubicMoment_Estimates_IndependentMellin`, `CubicMoment_Estimates_IndependentMellinTail`, `CubicMoment_Estimates_IntervalSmoothing`, `CubicMoment_Estimates_LargeSquareSupport`, `CubicMoment_Estimates_LargeTupleCoordinateWeights`, `CubicMoment_Estimates_LargeTupleRestrictedWeights`, `CubicMoment_Estimates_LargeTupleScaleGeometry`, `CubicMoment_Estimates_LargeTupleWeightLengths`, `CubicMoment_Estimates_LargeTupleWeights`, `CubicMoment_Estimates_LogSchwartzWeight`, `CubicMoment_Estimates_MellinSmooth`, `CubicMoment_Estimates_NormPartitionVariation`, `CubicMoment_Estimates_PrimeConvolutionMoments`, `CubicMoment_Estimates_PrimeDetectorCutoff`, `CubicMoment_Estimates_PrimePowerSupport`, `CubicMoment_Estimates_ScaledPrimeInput`, `CubicMoment_Estimates_SemiprimeGaussTailAngularWeights`, `CubicMoment_Estimates_SemiprimeGaussTailWeights`, `CubicMoment_Estimates_SemiprimeSmoothWeights`, `CubicMoment_Estimates_SharpCutoff`, `CubicMoment_Estimates_SharpHeightMultiplier`, `CubicMoment_Estimates_SharpHeightPartition`, `CubicMoment_Estimates_ShortOuterLow`, `CubicMoment_Estimates_SieveMobius`, `CubicMoment_Estimates_SinglePrimeHeight`, `CubicMoment_Estimates_SquarefreeMajorant`, `CubicMoment_Estimates_ThetaHeatKernelBound`, `CubicMoment_Estimates_ThetaUpperVerticalBound`, `CubicMoment_Estimates_TraceDuality`, `CubicMoment_Estimates_TruncatedMellin`, `CubicMoment_Estimates_WeightedPrimeInput`, `CubicMoment_Estimates_WideGramDecay`, `CubicMoment_Theta_CubicThetaArithmeticAxisRegularity`, `CubicMoment_Theta_CubicThetaArithmeticEquation`, `CubicMoment_Theta_CubicThetaAveragedHeat`, `CubicMoment_Theta_CubicThetaAxisDifferentials`, `CubicMoment_Theta_CubicThetaCompactExponential`, `CubicMoment_Theta_CubicThetaComplexHeight`, `CubicMoment_Theta_CubicThetaComplexPointMeasure`, `CubicMoment_Theta_CubicThetaCoordinateAxis`, `CubicMoment_Theta_CubicThetaCoordinateNormBounds`, `CubicMoment_Theta_CubicThetaCoordinatePairing`, `CubicMoment_Theta_CubicThetaCoordinateProfile`, `CubicMoment_Theta_CubicThetaEisensteinTorus`, `CubicMoment_Theta_CubicThetaExponential`, `CubicMoment_Theta_CubicThetaFiniteCoordinateBox`, `CubicMoment_Theta_CubicThetaFourierBessel`, `CubicMoment_Theta_CubicThetaHeatMoments`, `CubicMoment_Theta_CubicThetaHeatScaling`, `CubicMoment_Theta_CubicThetaHeatSmallNonzero`, `CubicMoment_Theta_CubicThetaHighHeatNonzero`, `CubicMoment_Theta_CubicThetaHighWindowSmooth`, `CubicMoment_Theta_CubicThetaIncomingWindow`, `CubicMoment_Theta_CubicThetaIntegerBox`, `CubicMoment_Theta_CubicThetaInversionGeometry`, `CubicMoment_Theta_CubicThetaInversionInvolutive`, `CubicMoment_Theta_CubicThetaLaplaceSum`, `CubicMoment_Theta_CubicThetaLocalBudget`, `CubicMoment_Theta_CubicThetaLocalOperator`, `CubicMoment_Theta_CubicThetaLongWindow`, `CubicMoment_Theta_CubicThetaLongWindowKernel`, `CubicMoment_Theta_CubicThetaMellinWeights`, `CubicMoment_Theta_CubicThetaMobiusGenerators`, `CubicMoment_Theta_CubicThetaNonzeroHeat`, `CubicMoment_Theta_CubicThetaPointC1`, `CubicMoment_Theta_CubicThetaPointC1Section`, `CubicMoment_Theta_CubicThetaPointC1Trace`, `CubicMoment_Theta_CubicThetaPointC1TraceIntegral`, `CubicMoment_Theta_CubicThetaPositiveAveragedHeat`, `CubicMoment_Theta_CubicThetaPositiveRadialMellin`, `CubicMoment_Theta_CubicThetaPositiveRadialWindow`, `CubicMoment_Theta_CubicThetaPrimeCubeComplexIntegration`, `CubicMoment_Theta_CubicThetaPrimeCubeHeckePairing`, `CubicMoment_Theta_CubicThetaPrimeCubeRootDilationObservation`, `CubicMoment_Theta_CubicThetaPrimeResidueTestWeight`, `CubicMoment_Theta_CubicThetaRadialEulerScaling`, `CubicMoment_Theta_CubicThetaRadialMellinIntegrability`, `CubicMoment_Theta_CubicThetaRadialNonzero`, `CubicMoment_Theta_CubicThetaRadialTent`, `CubicMoment_Theta_CubicThetaRemainderWeights`, `CubicMoment_Theta_CubicThetaTorusCellIntegral`, `CubicMoment_Theta_CubicThetaWindowFlux`, `CubicMoment_Theta_CubicThetaWindowFluxIntegral`, `CubicMoment_Theta_CubicThetaWindowProfile`, `CubicMoment_Theta_CubicThetaZeroWindow`, `CubicMoment_Transform_MetaplecticCriticalKernel`, `CubicMoment_Transform_MetaplecticHeight`, `Fourier`, `Sobolev`, `Wiener`.
--
--   **Imports.** It imports the published bundle `Def_PattersonFirstMoment`; the bundles `OAIQ096A000`, `OAIQ096A001`, `OAIQ096A002` and `OAIQ096A003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ096A008`, `OAIQ096A009` and `OAIQ096A010`; the statements `OAI_CubicFirstMoment_ProfileControl_low_coprime_height_real`, `OAI_CubicFirstMoment_all_frequency_cubic_operator_bound`, `OAI_CubicFirstMoment_angularKummerPrimeExplicitEstimate_of_primitive`, `OAI_CubicFirstMoment_angular_balanced_twisted_vonMangoldt_neighborhood`, `OAI_CubicFirstMoment_angular_first_twisted_vonMangoldt_neighborhood`, `OAI_CubicFirstMoment_angular_full_prime_product_height_bilinear`, `OAI_CubicFirstMoment_angular_stopped_distinguished_full_saving`, `OAI_CubicFirstMoment_angular_stopped_noncube_core_blocks`, `OAI_CubicFirstMoment_angular_stopped_selected_prime_row_saving`, `OAI_CubicFirstMoment_balanced_truncated_neighborhood_moment`, `OAI_CubicFirstMoment_dominant_first_full_factor_neighborhood`, `OAI_CubicFirstMoment_first_common_coordinate_exponents`, `OAI_CubicFirstMoment_huxleyAdditiveLargeSieve_proved`, `OAI_CubicFirstMoment_kummer_unweighted_from_primitive`, `OAI_CubicFirstMoment_normalized_angular_twisted_primitive_ideal_cubic_moment`, `OAI_CubicFirstMoment_normalized_twisted_primitive_ideal_cubic_moment`, `OAI_CubicFirstMoment_primeGroupTail_wide_bilinear_log_saving`, `OAI_CubicFirstMoment_primitiveResidueHeckeInput_proved` and `OAI_CubicFirstMoment_stopped_distinguished_full_saving`; the proofs of `OAI_CubicFirstMoment_all_frequency_cubic_operator_bound` and `OAI_CubicFirstMoment_stopped_distinguished_full_saving`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A000
import Definitions.Def_OAIQ096A001
import Definitions.Def_OAIQ096A002
import Definitions.Def_OAIQ096A003

section
-- module Solutions.OAIQ096_CM.CubicGram_Coordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integral coordinates and finite norm cutoffs in the Eisenstein subring. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma ofCoords_injective : Function.Injective (fun p : ℤ × ℤ => ofCoords p.1 p.2) := by
  intro ⟨a,b⟩ ⟨c,d⟩ h
  have hh := coordinates_unique (congrArg (fun z : Eisenstein => (z : ℂ)) h)
  exact Prod.ext hh.1 hh.2

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_SquarefreeGauss
attribute [-instance] _root_.instMeasurableSpace
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

lemma exists_primary_prime_square_dvd {b : Eisenstein} (hb : primary b)
    (hs : ¬Squarefree b) : ∃ p, primaryPrime p ∧ p*p ∣ b := by
  rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero (primary_ne_zero hb)] at hs
  push Not at hs
  obtain ⟨q,hq,hd⟩ := hs
  have hqb : q ∣ b := dvd_trans (dvd_mul_right q q) hd
  refine ⟨primaryNormalize q, ⟨primaryNormalize_primary
    (unit_residue_of_dvd_primary hb hqb), prime_primaryNormalize hq.prime⟩, ?_⟩
  have hh := (primaryNormalize_associated q).pow_pow (n := 2)
  rw [pow_two, pow_two] at hh
  exact hh.dvd_iff_dvd_left.mp hd

lemma exists_nontrivial_additivePhase {p : Eisenstein} (hp : primaryPrime p) :
    ∃ w : Eisenstein, additivePhase p w ≠ 1 := by
  by_contra! h
  apply residueAddChar_ne_one hp
  ext x
  exact h _

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_PeriodicPoisson
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Periodic lattice Poisson summation and exact trace frequencies. -/

section
noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

def residueCosetMap (c : Eisenstein) (x : Residues c × Eisenstein) : Eisenstein :=
  residueRepresentative c x.1 + c * x.2

lemma residueCosetMap_mk (c : Eisenstein) (x : Residues c × Eisenstein) :
    Ideal.Quotient.mk (modulus c) (residueCosetMap c x) = x.1 := by
  simp only [residueCosetMap, map_add, map_mul, residueRepresentative_spec]
  have h : Ideal.Quotient.mk (modulus c) c = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton c)
  simp [h]

lemma residueCosetMap_bijective {c : Eisenstein} (hc : c ≠ 0) :
    Function.Bijective (residueCosetMap c) := by
  constructor
  · intro x y h
    have hxy : x.1 = y.1 := by
      simpa only [residueCosetMap_mk] using congrArg (Ideal.Quotient.mk (modulus c)) h
    apply Prod.ext hxy
    have : c * x.2 = c * y.2 := by
      simpa only [residueCosetMap, hxy, add_right_inj] using h
    exact mul_left_cancel₀ hc this
  · intro a
    let v := Ideal.Quotient.mk (modulus c) a
    have hd : c ∣ a - residueRepresentative c v := by
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
      change Ideal.Quotient.mk (modulus c) (a - residueRepresentative c v) = 0
      rw [map_sub, residueRepresentative_spec]
      exact sub_self _
    obtain ⟨b, hb⟩ := hd
    exact ⟨(v, b), by dsimp [residueCosetMap]; linear_combination -hb⟩

end CubicFirstMoment

end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_GramPoisson
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal character Gram kernel and normalized radial Poisson expansion. -/

section

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable

noncomputable section
open Filter
open scoped ContDiff

namespace CubicFirstMoment

def primaryCosetMap (c : Eisenstein) (hc : primary c) (s : Eisenstein) :
    {n : Eisenstein // primary n} :=
  ⟨c+3*s, by
    obtain ⟨t, ht⟩ := hc
    use t+s
    rw [sub_eq_iff_eq_add] at ht
    rw [ht]
    ring⟩

end CubicFirstMoment

end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CommonFactors
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moebius removal of common factors and coprime Gram decomposition. -/

section

noncomputable section
open scoped BigOperators SchwartzMap ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

def multiplesMap (m : Eisenstein) (x : Eisenstein) : {n : Eisenstein // m ∣ n} :=
  ⟨m*x, dvd_mul_right m x⟩

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubicOperator
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
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
namespace CubicFirstMoment

def primarySmoothedSieveMass (S : Finset Eisenstein) (u : Eisenstein → ℂ)
    (W : ℝ → ℂ) (M : ℝ) : ℂ :=
  ∑' x : Eisenstein, if primary x then
    W (norm x / M) * (‖∑ n ∈ S, u n * cubicSymbol n x‖^2 : ℝ) else 0

end CubicFirstMoment

open UniqueFactorizationMonoid
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_MellinDecay
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separated radial Mellin kernels with uniform rapid decay. -/

section

noncomputable section
open scoped BigOperators SchwartzMap ContDiff FourierTransform
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def gramBumpSchwartz : 𝓢(ℝ, ℝ) :=
  gramLogBump.hasCompactSupport.toSchwartzMap gramLogBump.contDiff

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubeEstimates
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric decay, cube frequency dyads and numerical block inequalities. -/

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma eisenstein_norm_pow (a : Eisenstein) (k : ℕ) : norm (a^k) = norm a ^ k := by
  induction k with
  | zero => simp
  | succ k ih => simp only [pow_succ,norm_mul_eq,ih]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_InnerExtension
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.instMeasurableSpace
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

def finiteCoverCoefficient {ι : Type*} (I : Finset ι) (f : ι → Eisenstein)
    (H : Finset Eisenstein) (v : Eisenstein → ℂ) (x : ι) : ℂ :=
  if f x ∈ H then v (f x) / ((I.filter (fun y => f y = f x)).card : ℂ) else 0

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinSmooth
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analytic properties of the actual compactly supported smooth norm
weights. Passing to logarithmic coordinates realizes every vertical
Mellin line as a Schwartz Fourier transform. -/

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology SchwartzMap ContDiff FourierTransform

namespace CubicFirstMoment

def mellinVerticalSchwartz (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.compCLM ℂ (by
    simp only [div_eq_mul_inv]
    fun_prop : (fun t : ℝ => t/(2*Real.pi)).HasTemperateGrowth)
    mellin_frequency_growth (𝓕 (mellinLogSchwartz W hW hpos hsm σ))

theorem smooth_mellin_entire (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hc : Continuous W) : Differentiable ℂ (mellin W) := by
  intro s
  obtain ⟨ht,hb⟩ := smooth_mellin_power_bounds W hW hpos (s.re+1) (s.re-1)
  exact mellin_differentiableAt_of_isBigO_rpow (hc.locallyIntegrable.locallyIntegrableOn _)
    ht (by linarith) hb (by linarith)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WeightedPrimeInput
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Applying the published prime input to smooth prime weights

Prime elements of equal norm are collected without identifying conjugate
prime ideals. Complex Abel summation then derives the smooth-weighted
estimate from `CubicPrimeSiegelWalfisz`. The weighted estimate follows by partial summation.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace CubicFirstMoment

/-- Coefficients collected by integer norm, on a finite ambient prime set. -/
def primeNormCoefficient (R : ℝ) (χ : Eisenstein → ℂ) (n : ℕ) : ℂ :=
  ∑ p ∈ primeCutoff R, if n = normNat p then χ p else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeSquareSupport
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse support from a large square divisor, used to remove repeated
large primes in the exceptional character moments. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def largeSquareSupport (Y D : ℝ) : Finset Eisenstein :=
  (nonzeroNormBall Y).filter (fun b => ∃ d : Eisenstein, D < norm d ∧ d^2 ∣ b)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeConvolutionMoments
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Energy and actual character moments of fixed-length independent prime products. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primeConvolutionEnergy (S : ι → Finset Eisenstein) (w : ι → Eisenstein → ℂ) : ℝ :=
  ∏ i, ∑ p ∈ S i, ‖w i p‖^2

def primeCubicProductPolynomial (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (a : Eisenstein) : ℂ :=
  ∏ i, ∑ p ∈ S i, w i p*cubicSymbol a p

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimePowerSupport
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Higher prime powers in the von Mangoldt replacement have sparse support,
even when the underlying prime is small. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def largePrimePowerSupport (Y c : ℝ) : Finset Eisenstein :=
  (nonzeroNormBall Y).filter (fun b => ∃ p : Eisenstein, ∃ j : ℕ,
    primaryPrime p ∧ 2 ≤ j ∧ Y^c < norm (p^j) ∧ p^j ∣ b)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeSymmetry
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar factors on the symmetry line in the primitive Hecke
functional equation. These identities apply also to fixed infinity type.
They keep conductor-dependent phases outside the dual polynomial. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

/-- `D` includes the fixed field factor in the completed L-function. -/
def heckeSymmetryFactor (ε : ℂ) (D Z k t τ : ℝ) : ℂ :=
  ε * mellinPhase (t-τ) D * mellinPhase τ Z * heckeGammaRatio k (τ-t)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeDualContour
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moving finite dual polynomials back to the symmetry line. The only
new conditional analytic input is the bounded-strip polynomial estimate
for the classical Gamma quotient, a specialization of NIST DLMF 5.11.9
(uniformly for bounded real parts). The half-integer-line estimate needed
for the discarded tail was proved directly in GammaLeftLine. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def finiteHeckeDual {ι : Type*} (S : Finset ι) (a : ι → ℂ) (N : ι → ℝ)
    (ε : ℂ) (A : ℝ) (s : ℂ) : ℂ :=
  ε*(A:ℂ)^(1-2*s)*gammaFEQuotient s*finiteNormDirichlet S a N (1-s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeDualMoment
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer of a common bound for normalized dual polynomials to the
retained Hecke integrals. Root numbers and conductors only enter through
unit-modulus row factors. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def normalizedDualPolynomial {ν : Type*} (S : Finset ν) (χ : ν → ℂ)
    (N : ν → ℝ) (J u : ℝ) : ℂ :=
  ∑ v ∈ S, (χ v*((J/N v)^(1/2:ℝ):ℝ))*mellinPhase u (N v)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeDyadicMoment
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

def finiteDualIntegral {ν : Type*} (W : ℝ → ℂ) (S : Finset ν) (χ : ν → ℂ)
    (N : ν → ℝ) (ε : ℂ) (A Z t : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ,
    mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*(Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
      finiteHeckeDual S χ N ε A ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeMajorant
attribute [-instance] _root_.instMeasurableSpace
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

/-- The concrete norm truncation used by corrected dispersion. -/
def squareDivisorTruncation (D : ℝ) : Finset Eisenstein :=
  (nonzeroNormBall D).filter primary

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SieveMobius
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The Möbius coefficient below the sieve truncation

The union convolution of the squarefree Möbius weights is the same
Möbius weight. This proves the exact low-divisor coefficient identity,
which is stronger than a divisor bound and is needed in the residue.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Terms at nonsquarefree divisors have zero Möbius weight, so this
finite truncation gives exactly the original truncated divisor sum. -/
def squarefreeDivisorTruncation (D : ℝ) : Finset Eisenstein :=
  (squareDivisorTruncation D).filter Squarefree

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticHeight
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero-angular metaplectic inputs, stated for the literal Gauss series.

Sources: Heath-Brown, *Kummer's conjecture for cubic Gauss sums* (2000),
§3 Lemma 3 (author manuscript p.9), with angular index zero; Dunn–Radziwiłł,
*Bias in cubic Gauss sums* (2024), arXiv:2109.07463v3, Proposition 5.2,
pp.29–30. No Type-I estimate or Mellin contour identity is an input here. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticTotient (r : Eisenstein) : ℝ := (Nat.card (Residues r)ˣ : ℝ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeDetectorCutoff
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit smooth cutoff for the exact prime detector. -/
noncomputable section
open Filter
open scoped ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primeDetectorCutoff_zero {x : ℝ} (hx : 2 ≤ x) : primeDetectorCutoff x = 0 := by
  rw [primeDetectorCutoff,Real.smoothTransition.one_of_one_le (by linarith),sub_self]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ScaledPrimeInput
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rescaled, Mellin-twisted prime estimate derived from the precise
published unweighted Siegel–Walfisz input. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def smoothPrimeCharacterSum (R Y : ℝ) (w : ℝ → ℂ) (χ : Eisenstein → ℂ) (u : ℝ) : ℂ :=
  ∑ p ∈ primeCutoff (R*Y), w (norm p/Y)*mellinPhase u (norm p)*χ p

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedBinDecomposition
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact long-bin decomposition of a stopped coefficient. The
complementary short-bin part is supported on genuinely smooth integers. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def stoppedLongBins (B ρ y : ℝ) : Finset ℕ :=
  (Finset.range (geometricBinCount ρ B)).filter (fun j => y/2 ≤ geometricBinLower ρ B j)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IndependentMellin
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Mellin separation of independent coordinate weights on a finite
arithmetic sum. The joint weight has explicitly factored L1 mass. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def independentMellinWeight (W : ι → ℝ → ℂ) (X : ι → ℝ) (τ : ι → ℝ) : ℂ :=
  ∏ i, zeroLineMellinWeight (W i) (X i) (τ i)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WideGramDecay
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform Fourier decay for the fixed wider log-norm cutoff used by the
actual prime convolution. -/
noncomputable section
open scoped BigOperators SchwartzMap ContDiff FourierTransform
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment


def wideGramBumpSchwartz (M : ℝ) (hM : 0 < M) : 𝓢(ℝ, ℝ) :=
  (wideGramLogBump M hM).hasCompactSupport.toSchwartzMap (wideGramLogBump M hM).contDiff

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealDirichletInverse
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.instMeasurableSpace
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

lemma ideal_cauchy_product (f g : EisensteinIdealExponent → ℂ)
    (hf : Summable (fun ν => ‖f ν‖)) (hg : Summable (fun ν => ‖g ν‖)) :
    (∑' ν, f ν)*(∑' ν, g ν)=
      ∑' ν, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν, f p.1*g p.2 := by
  have hpair : Summable (fun p : EisensteinIdealExponent × EisensteinIdealExponent =>
      f p.1*g p.2) := summable_mul_of_summable_norm hf hg
  exact Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal
    (A := EisensteinIdealExponent) (f := f) (g := g) hf.of_norm hg.of_norm hpair

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IntervalSmoothing
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The endpoint error of a smoothed interval

A normalized integrable kernel approximates an interval indicator with
error controlled by its two tails. The proof retains exact endpoints.
This is the physical-space step of the Fourier truncation argument.
-/

noncomputable section
open MeasureTheory

namespace CubicFirstMoment

def intervalSmoothing (k : ℝ → ℂ) (a b s : ℝ) : ℂ :=
  ∫ y, (intervalStep a b (s - y) : ℂ) * k y

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FourierCutoff
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A concrete Fourier cutoff kernel

The fixed cutoff is a smooth bump, one near zero and supported in [-1,1].
Its inverse Fourier transform is a normalized Schwartz kernel. Mathlib
uses exp(2π i x ξ); this frequency variable differs by 2π from the
height variable in the manuscript.
-/

noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform

namespace CubicFirstMoment

def truncationKernel : SchwartzMap ℝ ℂ := 𝓕⁻ frequencyCutoff

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SharpCutoff
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The sharp-cutoff error at integer norms

The smoothing constructed from the fixed Fourier kernel has a summable
endpoint error.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace CubicFirstMoment

def smoothLogInterval (T v : ℝ) : ℂ :=
  intervalSmoothing (scaledKernel truncationKernel T) 0 (Real.log 2) (Real.log v)

def sharpIntervalError (X T n : ℝ) : ℂ :=
  (intervalStep X (2*X) n : ℂ) - smoothLogInterval T (n/X)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TruncatedMellin
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual truncated Mellin integral

The Fourier approximation to the dyadic indicator is inserted into a
finite arithmetic polynomial. The height is `2πξ`, in accordance with
Mathlib's Fourier convention. The multiplier vanishes for `|ξ| ≥ T`.
-/

noncomputable section
open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

def dyadicFourierMultiplier (ξ : ℝ) : ℂ :=
  𝓕 (fun x => (intervalStep 0 (Real.log 2) x : ℂ)) ξ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LogSchwartzWeight
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact logarithmic Schwartz profile gives an actual smooth norm
weight supported away from zero, with no loss in its logarithmic seminorms. -/
noncomputable section
open Set Filter
open scoped ContDiff SchwartzMap Topology
namespace CubicFirstMoment

lemma logSchwartzWeight_zero_small (H : 𝓢(ℝ,ℂ)) {R : ℝ}
    (hR : ∀ u ∈ tsupport (H : ℝ → ℂ), |u| ≤ R)
    {x : ℝ} (hx : x < Real.exp (-R)) : logSchwartzWeight H x=0 := by
  by_cases hxp : 0 < x
  · rw [logSchwartzWeight,ite_eq_left hxp]
    by_contra hn
    have hh := hR (-Real.log x) (subset_tsupport _ hn)
    have hl := (Real.log_lt_iff_lt_exp hxp).mpr hx
    linarith [le_abs_self (-Real.log x)]
  · simp only [logSchwartzWeight,ite_eq_right hxp]

lemma logSchwartzWeight_zero_large (H : 𝓢(ℝ,ℂ)) {R : ℝ}
    (hR : ∀ u ∈ tsupport (H : ℝ → ℂ), |u| ≤ R)
    {x : ℝ} (hx : Real.exp R < x) : logSchwartzWeight H x=0 := by
  have hxp : 0 < x := (Real.exp_pos R).trans hx
  rw [logSchwartzWeight,ite_eq_left hxp]
  by_contra hn
  have hh := hR (-Real.log x) (subset_tsupport _ hn)
  have hl := (Real.lt_log_iff_exp_lt hxp).mpr hx
  linarith [neg_abs_le (-Real.log x)]

lemma logSchwartzWeight_support (H : 𝓢(ℝ,ℂ)) {R : ℝ}
    (hR : ∀ u ∈ tsupport (H : ℝ → ℂ), |u| ≤ R) :
    Function.support (logSchwartzWeight H) ⊆ Icc (Real.exp (-R)) (Real.exp R) := by
  intro x hx
  constructor
  · by_contra h
    exact hx (logSchwartzWeight_zero_small H hR (lt_of_not_ge h))
  · by_contra h
    exact hx (logSchwartzWeight_zero_large H hR (lt_of_not_ge h))

lemma logSchwartzWeight_compact (H : 𝓢(ℝ,ℂ)) {R : ℝ}
    (hR : ∀ u ∈ tsupport (H : ℝ → ℂ), |u| ≤ R) :
    HasCompactSupport (logSchwartzWeight H) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (logSchwartzWeight_support H hR)

lemma logSchwartzWeight_positive_support (H : 𝓢(ℝ,ℂ)) {R : ℝ}
    (hR : ∀ u ∈ tsupport (H : ℝ → ℂ), |u| ≤ R) :
    tsupport (logSchwartzWeight H) ⊆ Ioi 0 := by
  have hc := closure_minimal (logSchwartzWeight_support H hR) isClosed_Icc
  intro x hx
  exact (Real.exp_pos (-R)).trans_le (hc hx).1

lemma logSchwartzWeight_smooth (H : 𝓢(ℝ,ℂ)) {R : ℝ}
    (hR : ∀ u ∈ tsupport (H : ℝ → ℂ), |u| ≤ R) :
    ContDiff ℝ ∞ (logSchwartzWeight H) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : 0 < x
  · have he : logSchwartzWeight H =ᶠ[𝓝 x] fun y => H (-Real.log y) := by
      filter_upwards [(isOpen_lt continuous_const continuous_id).mem_nhds hx] with y hy
      exact ite_eq_left hy
    have hl : ContDiffAt ℝ ∞ (fun y : ℝ => -Real.log y) x :=
      (contDiffAt_id.log hx.ne').neg
    exact ((H.smooth ⊤).contDiffAt.comp x hl).congr_of_eventuallyEq he
  · have hxe : x < Real.exp (-R) := (le_of_not_gt hx).trans_lt (Real.exp_pos _)
    have he : logSchwartzWeight H =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_id continuous_const).mem_nhds hxe] with y hy
      exact logSchwartzWeight_zero_small H hR hy
    exact contDiffAt_const.congr_of_eventuallyEq he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticCriticalKernel
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At the critical line the angular Gamma quotient has modulus one.
Thus the actual translated Mellin kernel has one common integrable
weight, independent of height and of the retained frequency polynomial. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

def metaplecticCriticalKernel (ℓ : ℤ) (W : ℝ → ℂ) (c : ℝ)
    (P : ℝ → ℂ) (τ t : ℝ) : ℂ :=
  mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*
    metaplecticGammaQuotient ℓ ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)*
    mellinPhase (τ-t) c*P (τ-t)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorDispersion
attribute [-instance] _root_.instMeasurableSpace
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

def divisorCharacterGram (d p q : Eisenstein) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑' a : Eisenstein, if primary a ∧ d^2 ∣ a then
    W (norm a/A)*cubicSymbol p a*star (cubicSymbol q a) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SharpHeightPartition
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth height windows with ratio 3/2. Their support lies in [T,2T]
in absolute value, exactly the range of the proved bilinear estimates.
The finite telescoping identity keeps the actual truncation multiplier. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma heightPartitionBump_one {t : ℝ} (ht : |t| ≤ 1) :
    heightPartitionBump t = 1 := by
  apply heightPartitionBump.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, heightPartitionBump] using ht

lemma heightPartitionBump_zero {t : ℝ} (ht : 4/3 ≤ |t|) :
    heightPartitionBump t = 0 := by
  apply heightPartitionBump.zero_of_le_dist
  simpa only [Real.dist_eq, sub_zero, heightPartitionBump] using ht

lemma heightWindow_smooth (T : ℝ) : ContDiff ℝ ∞ (heightWindow T) := by
  exact Complex.ofRealCLM.contDiff.comp
    ((heightPartitionBump.contDiff.comp (contDiff_id.div_const _)).sub
      (heightPartitionBump.contDiff.comp (contDiff_id.div_const _)))

lemma heightWindow_zero {T t : ℝ} (hT : 0 < T)
    (ht : t ∉ dyadicHeightSupport T) : heightWindow T t = 0 := by
  have hnot : ¬(T ≤ |t| ∧ |t| ≤ 2*T) := by
    rintro ⟨hl,hu⟩
    apply ht
    rcases le_total 0 t with hpos | hneg
    · left
      simpa only [Set.mem_Icc, abs_of_nonneg hpos] using And.intro hl hu
    · right
      rw [abs_of_nonpos hneg] at hl hu
      exact ⟨by linarith, by linarith⟩
  rcases lt_or_ge |t| T with hl | hl
  · have hsmall : |t/T| ≤ 1 := by rw [abs_div, abs_of_pos hT]; exact (div_le_one hT).mpr hl.le
    have hsmall' : |t/((3/2)*T)| ≤ 1 := by
      rw [abs_div, abs_of_pos (by positivity : 0 < (3/2:ℝ)*T)]
      apply (div_le_one (by positivity)).mpr
      linarith
    simp only [heightWindow, heightPartitionBump_one hsmall,
      heightPartitionBump_one hsmall', sub_self, Complex.ofReal_zero]
  · have hu : 2*T < |t| := lt_of_not_ge (fun hu => hnot ⟨hl,hu⟩)
    have hlarge : 4/3 ≤ |t/T| := by
      rw [abs_div, abs_of_pos hT]
      apply (le_div_iff₀ hT).mpr
      linarith
    have hlarge' : 4/3 ≤ |t/((3/2)*T)| := by
      rw [abs_div, abs_of_pos (by positivity : 0 < (3/2:ℝ)*T)]
      apply (le_div_iff₀ (by positivity)).mpr
      linarith
    simp only [heightWindow, heightPartitionBump_zero hlarge,
      heightPartitionBump_zero hlarge', sub_self, Complex.ofReal_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SharpHeightMultiplier
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two endpoint phases of the actual cutoff. On each smooth height
window the normalized reciprocal factor is uniformly bounded. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

def localizedEndpointWeight (S T t : ℝ) : ℂ :=
  (T:ℂ)*frequencyCutoff ((t/(2*Real.pi))/S)/((t:ℂ)*Complex.I)*heightWindow T t

lemma localizedEndpointWeight_zero {T : ℝ} (S : ℝ) (hT : 0 < T) (t : ℝ)
    (ht : t ∉ dyadicHeightSupport T) : localizedEndpointWeight S T t = 0 := by
  simp only [localizedEndpointWeight, heightWindow_zero hT ht, mul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightEndpointRegularity
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness at the removable reciprocal singularity, compact support,
and the exact two-endpoint formula for a localized cutoff. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff Topology
namespace CubicFirstMoment

lemma localizedEndpointWeight_smooth (S : ℝ) {T : ℝ} (hT : 0 < T) :
    ContDiff ℝ ∞ (localizedEndpointWeight S T) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    have hn : ∀ᶠ t : ℝ in 𝓝 0, |t| < T :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds (by simpa using hT)
    filter_upwards [hn] with t ht
    exact localizedEndpointWeight_zero S hT t (abs_lt_not_mem_dyadic ht)
  · unfold localizedEndpointWeight
    apply ContDiffAt.mul _ (heightWindow_smooth T).contDiffAt
    simp only [div_eq_mul_inv]
    apply ContDiffAt.mul
    · exact (contDiff_const.mul (frequencyCutoff.smooth'.comp
        ((contDiff_id.div_const (2*Real.pi)).div_const S))).contDiffAt
    · exact (Complex.ofRealCLM.contDiff.mul contDiff_const).contDiffAt.inv
        (mul_ne_zero (by change (x:ℂ) ≠ 0; exact_mod_cast hx) Complex.I_ne_zero)

lemma localizedEndpointWeight_tsupport (S : ℝ) {T : ℝ} (hT : 0 < T) :
    tsupport (localizedEndpointWeight S T) ⊆ dyadicHeightSupport T := by
  apply closure_minimal _ (isClosed_Icc.union isClosed_Icc)
  intro t ht
  by_contra hh
  exact ht (localizedEndpointWeight_zero S hT t hh)

lemma localizedEndpointWeight_compact (S : ℝ) {T : ℝ} (hT : 0 < T) :
    HasCompactSupport (localizedEndpointWeight S T) := by
  apply (isCompact_Icc.union isCompact_Icc).of_isClosed_subset isClosed_closure
  exact localizedEndpointWeight_tsupport S hT

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TraceDuality
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integral self-duality for the symmetric Eisenstein trace pairing. -/

noncomputable section
open MeasureTheory
namespace CubicFirstMoment

def traceBilinear : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] ℝ where
  toFun z :=
    { toFun := fun w => tracePair z w
      map_add' := by intro a b; simp [tracePair,mul_add]
      map_smul' := by intro r w; simp [tracePair,Complex.real_smul]; ring }
  map_add' := by
    intro a b
    ext w
    simp [tracePair,add_mul]
    ring
  map_smul' := by
    intro r z
    ext w
    simp [tracePair,Complex.real_smul]
    ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicDyadicCoverage
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite cover of all noncube frequencies outside the small-core set
by the actual coprime ramified/squarefree blocks used in the moment bounds. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def largeCoreDyadicIndices (V B : ℝ) : Finset (ℕ × ℕ) :=
  ((Finset.range (Nat.log 2 ⌊B⌋₊+1)).product
    (Finset.range (Nat.log 2 ⌊B⌋₊+1))).filter
    (fun z => V/5832 < coreDyadicConductor z.1 z.2 ∧ coreDyadicConductor z.1 z.2 ≤ B)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IndependentMellinTail
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The high-coordinate tail of the genuine product Mellin weight is bounded
by its explicit finite sum of coordinate moments. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def independentMellinMoment (W : ι → ℝ → ℂ) (A : ℕ) : ℝ :=
  ∫ τ : ι → ℝ, mellinHeightPower A τ*‖independentMellinWeight W (fun _ => 1) τ‖

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortOuterLow
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum all short outer norm dyads in the central corrected kernel.
The dyad count costs one logarithm, and all weights and support are actual. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def shortOuterCount (Y : ℝ) : ℕ := geometricBinCount 2 (2*Y)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SemiprimeSmoothWeights
attribute [-instance] _root_.instMeasurableSpace
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

lemma semiprimeSmoothWeight_low (r : ℝ) {x : ℝ} (hx : x < 1) :
    semiprimeSmoothWeight r x = 0 := by
  rw [semiprimeSmoothWeight,normPartitionWeight_low hx,zero_mul]

lemma semiprimeSmoothWeight_capped (r x : ℝ) :
    semiprimeSmoothWeight (min r 2) x = semiprimeSmoothWeight r x := by
  by_cases hr : r ≤ 2
  · rw [min_eq_left hr]
  · rw [min_eq_right (le_of_not_ge hr)]
    by_cases hx : x < 1
    · rw [semiprimeSmoothWeight_low _ hx,semiprimeSmoothWeight_low _ hx]
    · have hx1 : 1 ≤ x := le_of_not_gt hx
      have hr2 : 2 ≤ r := le_of_not_ge hr
      rw [semiprimeSmoothWeight,semiprimeSmoothWeight,
        primeDetectorCutoff_zero (by nlinarith : 2 ≤ 2*x),
        primeDetectorCutoff_zero (by nlinarith : 2 ≤ r*x)]

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

lemma distinguishedSmoothWeight_capped (r : ℝ × ℝ) (x : ℝ) :
    distinguishedSmoothWeight (min r.1 2,min r.2 2) x =
      distinguishedSmoothWeight r x := by
  simp only [distinguishedSmoothWeight,semiprimeSmoothWeight_capped]

def largePrimeSmoothWeight (r : Ici (0:ℝ) × Ici (0:ℝ)) (distinguished : Bool) : ℝ → ℂ :=
  if distinguished then distinguishedSmoothWeight ((r.1:ℝ),(r.2:ℝ))
  else semiprimeSmoothWeight r.1

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

lemma largeTupleNormScale_pos {i j : ℕ} (k : (Fin i ⊕ Fin j) → ℕ)
    (a : Fin i ⊕ Fin j) : 0 < largeTupleNormScale k a := by
  unfold largeTupleNormScale
  positivity

def largeTupleCoordinateWeight {i j : ℕ} (ξ X : ℝ) (k : (Fin i ⊕ Fin j) → ℕ)
    (a : Fin i ⊕ Fin j) : ℝ → ℂ :=
  match a with
  | .inl _ => distinguishedSmoothWeight
      (largeTupleNormScale k a/(X^ξ),largeTupleNormScale k a/(X^(2/5:ℝ)))
  | .inr _ => semiprimeSmoothWeight (largeTupleNormScale k a/(X^ξ))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleScaleGeometry
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nonzero smooth box fixes independent coordinate lengths. The
same lengths work for every tuple in the box, so a grouping chosen at
one surviving tuple does not introduce a new coupled coefficient. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def largeTupleSubsetScale {i j : ℕ} (k : (Fin i ⊕ Fin j) → ℕ)
    (s : Finset (Fin i ⊕ Fin j)) : ℝ := ∏ a ∈ s, largeTupleNormScale k a

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormPartitionVariation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform scaled derivative bounds for the actual distinguished norm
partition. Rescaling the prime norm introduces no growing variation cost. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

def scaledNormPartitionWeight (c x : ℝ) : ℂ := normPartitionWeight (c*x)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedStoppingWeights
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinguished scale coefficients use a single bounded-variation
family at every partition scale, exactly as the stopped estimate requires. -/
noncomputable section
open Filter
open scoped ContDiff
namespace CubicFirstMoment

def distinguishedStoppingWeights {i N : ℕ} (k : Fin i → Fin N)
    (j : Fin i) (x : ℝ) : ℂ := scaledNormPartitionWeight (2/(4/3:ℝ)^(k j).val) x

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightEndpointProfile
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed compact profile removes the reciprocal singularity. Dilating
this profile gives the normalized endpoint weights used in localization. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def endpointProfile : SchwartzMap ℝ ℂ :=
  (localizedEndpointWeight_compact (2/Real.pi) (by norm_num : (0:ℝ) < 1)).toSchwartzMap
    (localizedEndpointWeight_smooth (2/Real.pi) (by norm_num : (0:ℝ) < 1))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedProductProfile
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed Schwartz function localized in a genuine dyadic height window.
The normalized profile and its scaled second derivative decay like 1/T. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff Topology
namespace CubicFirstMoment

lemma heightWindow_compact {T : ℝ} (hT : 0 < T) :
    HasCompactSupport (heightWindow T) := by
  have hs : tsupport (heightWindow T) ⊆ dyadicHeightSupport T := by
    apply closure_minimal _ (isClosed_Icc.union isClosed_Icc)
    intro t ht
    by_contra hh
    exact ht (heightWindow_zero hT hh)
  exact (isCompact_Icc.union isCompact_Icc).of_isClosed_subset isClosed_closure hs

def heightWindowSchwartz : SchwartzMap ℝ ℂ :=
  (heightWindow_compact (by norm_num : (0:ℝ) < 1)).toSchwartzMap (heightWindow_smooth 1)

def schwartzHeightWindow (f : SchwartzMap ℝ ℂ) (T t : ℝ) : ℂ :=
  (T:ℂ)*f t*heightWindow T t

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FarInverseSquare
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed smooth inverse-square extension, with all Fourier hypotheses proved. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff FourierTransform Topology
namespace CubicFirstMoment

def farInverseSquareReal (x : ℝ) : ℝ := (1-frequencyBump x)*x^(-2:ℤ)

def farInverseSquare (x : ℝ) : ℂ := (farInverseSquareReal x : ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FarFourierSeparation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Fourier separation of the far product cutoff. The kernel has
uniform L1 norm, and its shifts act on the actual norm twists. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators FourierTransform
namespace CubicFirstMoment

def farFourierKernel (J u : ℝ) : ℂ :=
  𝓕 (fun x : ℝ => farInverseSquare (J*x)) u

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FarMellinKernel
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular-frequency normalization of the far-cutoff Fourier kernel.
It has exactly the same L1 mass for every positive cell scale. -/
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform
namespace CubicFirstMoment

def farMellinKernel (J v : ℝ) : ℂ :=
  ((2*Real.pi:ℝ):ℂ)⁻¹*farFourierKernel J (v/(2*Real.pi))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedProductMellinPhase
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact phases in the product Mellin integral. The scale oscillation is
kept outside the fixed Schwartz profile, so its derivative cost is uniform. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def reflectedZeroMellinProfile (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hpos : tsupport V ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ V) : SchwartzMap ℝ ℂ :=
  (1/(2*Real.pi):ℝ) •
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv)
      (mellinVerticalSchwartz V hV hpos hsm 0)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicWhittakerBounds
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local regularity and explicit majorants of the cubic theta Fourier kernel. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicThetaWhittaker_norm {v : ℝ} (hv : 0 < v) :
    ‖cubicThetaWhittaker v‖ = v/2*cubicBesselKernel ((2*Real.pi*v)^2) := by
  simp only [cubicThetaWhittaker,norm_mul,norm_div,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos hv]
  rw [abs_of_nonneg (cubicBesselKernel_nonneg (sq_nonneg _))]
  norm_num

lemma cubicThetaWhittaker_continuousAt {v : ℝ} (hv : 0 < v) :
    ContinuousAt cubicThetaWhittaker v := by
  have hx : 0 < (2*Real.pi*v)^2 := by positivity
  have hk : ContinuousAt cubicBesselKernel ((2*Real.pi*v)^2) :=
    cubicBesselKernel_continuousOn.continuousAt (isOpen_Ioi.mem_nhds hx)
  have hc : ContinuousAt (fun w : ℝ => (2*Real.pi*w)^2) v := by fun_prop
  have hi : ContinuousAt (fun w : ℝ => (cubicBesselKernel ((2*Real.pi*w)^2):ℂ)) v :=
    Complex.continuous_ofReal.continuousAt.comp (hk.comp (f := fun w : ℝ => (2*Real.pi*w)^2) hc)
  exact (Complex.continuous_ofReal.continuousAt.div_const 2).mul hi

/-- Every fixed power majorant is available on the full positive axis. -/
theorem cubicThetaWhittaker_power_bound (k : ℕ) (hk : 1 ≤ k) {v : ℝ} (hv : 0 < v) :
    ‖cubicThetaWhittaker v‖ ≤ cubicWhittakerPowerConstant k*v^(4/3-2*(k:ℝ)) := by
  rw [cubicThetaWhittaker_norm hv]
  apply (mul_le_mul_of_nonneg_left
    (cubicBesselKernel_power_bound k hk (show 0 < (2*Real.pi*v)^2 by positivity))
    (by positivity : 0 ≤ v/2)).trans_eq
  have hp : ((2*Real.pi*v)^2)^(1/6-(k:ℝ)) =
      (2*Real.pi)^(1/3-2*(k:ℝ))*v^(1/3-2*(k:ℝ)) := by
    rw [←Real.rpow_natCast_mul (by positivity : 0 ≤ 2*Real.pi*v)]
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ)*(1/6-(k:ℝ))=1/3-2*(k:ℝ) by ring,
      Real.mul_rpow (by positivity : 0 ≤ 2*Real.pi) hv.le]
  rw [hp]
  have hvp : v*v^(1/3-2*(k:ℝ)) = v^(4/3-2*(k:ℝ)) := by
    calc
      _ = v^(1:ℝ)*v^(1/3-2*(k:ℝ)) := by rw [Real.rpow_one]
      _ = v^(1+(1/3-2*(k:ℝ))) := (Real.rpow_add hv _ _).symm
      _ = _ := by congr 1; ring
  unfold cubicWhittakerPowerConstant
  calc
    _ = (((k.factorial:ℝ)*Real.Gamma ((k:ℝ)-1/3)/2)*(2*Real.pi)^(1/3-2*(k:ℝ)))*
        (v*v^(1/3-2*(k:ℝ))) := by ring
    _ = _ := by rw [hvp]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicWhittakerDerivative
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First vertical derivative of the actual cubic Whittaker kernel,
with arbitrary fixed power decay. -/
noncomputable section
namespace CubicFirstMoment

def cubicWhittakerDerivativePowerConstant (k : ℕ) : ℝ :=
  (((k.factorial:ℝ)*Real.Gamma ((k:ℝ)-1/3))/2+cubicBesselDerivativePowerConstant k)*
    (2*Real.pi)^(1/3-2*(k:ℝ))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicWhittakerExponential
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential decay retaining an arbitrarily summable polynomial factor. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicWhittakerExpConstant_pos : 0 < cubicWhittakerExpConstant := by
  have hg := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 1/3)
  unfold cubicWhittakerExpConstant
  positivity

lemma cubicThetaWhittaker_exponential_bound {v : ℝ} (hv : 0 < v) :
    ‖cubicThetaWhittaker v‖ ≤
      cubicWhittakerExpConstant*v^(2/3:ℝ)*Real.exp (-(2*Real.pi*v)) := by
  rw [cubicThetaWhittaker_norm hv]
  apply (mul_le_mul_of_nonneg_left
    (cubicBesselKernel_exp_power_bound (show 0 < (2*Real.pi*v)^2 by positivity))
    (by positivity : 0 ≤ v/2)).trans_eq
  have hbase : 0 < 2*Real.pi*v := by positivity
  rw [Real.sqrt_sq_eq_abs,abs_of_pos hbase]
  have hp : ((2*Real.pi*v)^2)^(-1/6:ℝ) = (2*Real.pi)^(-1/3:ℝ)*v^(-1/3:ℝ) := by
    rw [←Real.rpow_natCast_mul hbase.le]
    norm_num only [Nat.cast_ofNat]
    rw [Real.mul_rpow (by positivity : 0 ≤ 2*Real.pi) hv.le]
  rw [hp]
  have hvp : v*v^(-1/3:ℝ) = v^(2/3:ℝ) := by
    calc
      _ = v^(1:ℝ)*v^(-1/3:ℝ) := by rw [Real.rpow_one]
      _ = v^(1+(-1/3:ℝ)) := (Real.rpow_add hv _ _).symm
      _ = _ := by congr 1; ring
  unfold cubicWhittakerExpConstant
  calc
    _ = ((Real.Gamma (1/3)*2^(1/3:ℝ)/2)*(2*Real.pi)^(-1/3:ℝ))*
      (v*v^(-1/3:ℝ))*Real.exp (-(2*Real.pi*v)) := by ring
    _ = _ := by rw [hvp]

lemma cubicWhittakerMixedConstant_pos : 0 < cubicWhittakerMixedConstant := by
  unfold cubicWhittakerMixedConstant
  exact div_pos (mul_pos cubicWhittakerExpConstant_pos (by norm_num)) (pow_pos Real.pi_pos 6)

/-- Half the exponential is retained, while the other half supplies six
powers of decay for the two-dimensional frequency sum. -/
theorem cubicThetaWhittaker_mixed_bound {v : ℝ} (hv : 0 < v) :
    ‖cubicThetaWhittaker v‖ ≤
      cubicWhittakerMixedConstant*v^(-16/3:ℝ)*Real.exp (-Real.pi*v) := by
  have he : Real.exp (-Real.pi*v) ≤ (720:ℝ)/(Real.pi*v)^6 := by
    have h := exp_neg_div_le_power 6 (mul_pos Real.pi_pos hv) (show (0:ℝ) < 1 by norm_num)
    norm_num at h
    simpa only [neg_mul] using h
  have hA := cubicWhittakerExpConstant_pos.le
  have hsplit : Real.exp (-(2*Real.pi*v)) = Real.exp (-Real.pi*v)*Real.exp (-Real.pi*v) := by
    rw [←Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ cubicWhittakerExpConstant*v^(2/3:ℝ)*Real.exp (-(2*Real.pi*v)) :=
      cubicThetaWhittaker_exponential_bound hv
    _ = (cubicWhittakerExpConstant*v^(2/3:ℝ)*Real.exp (-Real.pi*v))*Real.exp (-Real.pi*v) := by
      rw [hsplit]; ring
    _ ≤ (cubicWhittakerExpConstant*v^(2/3:ℝ)*(720/(Real.pi*v)^6))*Real.exp (-Real.pi*v) := by
      gcongr
    _ = _ := by
      have hvp : v^(2/3:ℝ)/v^6 = v^(-16/3:ℝ) := by
        rw [←Real.rpow_natCast v 6,←Real.rpow_sub hv]
        congr 1
        norm_num
      unfold cubicWhittakerMixedConstant
      rw [mul_pow]
      calc
        _ = (cubicWhittakerExpConstant*720/Real.pi^6)*(v^(2/3:ℝ)/v^6)*Real.exp (-Real.pi*v) := by ring
        _ = _ := by rw [hvp]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicWhittakerEnergy
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute squared Mellin masses for the fixed cubic Whittaker kernel. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicWhittakerEnergyMass (σ : ℝ) : ℝ :=
  ∫ v in Ioi (0:ℝ), v^(2*σ-1)*‖cubicThetaWhittaker v‖^2


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyGaussianCoordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute convergence and the two-coordinate theta identity. -/
noncomputable section
namespace CubicFirstMoment

def huxleyCoordinateEquiv : (ℤ × ℤ) ≃ Eisenstein :=
  Equiv.ofBijective (fun p => ofCoords p.1 p.2)
    ⟨ofCoords_injective,ofCoords_surjective⟩

def huxleyDualCoordinateEquiv : (ℤ × ℤ) ≃ Eisenstein :=
  Equiv.ofBijective (fun p => ofCoords (p.1+p.2) p.1) (by
    constructor
    · intro p q hpq
      have h : (p.1+p.2,p.1) = (q.1+q.2,q.1) := ofCoords_injective hpq
      have h1 : p.1+p.2 = q.1+q.2 := congrArg Prod.fst h
      have h2 : p.1 = q.1 := congrArg Prod.snd h
      apply Prod.ext h2
      omega
    · intro z
      obtain ⟨⟨a,b⟩,h⟩ := ofCoords_surjective z
      exact ⟨(b,a-b),by simpa using h⟩)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyFiniteDual
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the Gaussian weight on the finite norm ball and applying duality. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def huxleyAdditiveConstant : ℝ :=
  Real.exp 1*huxleyGaussianConstant*(2*Real.pi+3/(2*Real.pi))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleWeightLengths
attribute [-instance] _root_.instMeasurableSpace
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

def largeTupleBoxIndex (i j : ℕ) :=
  {z : {X : ℝ // 0 < X} × ((Fin i ⊕ Fin j) → ℕ) //
    ∀ a, 1 ≤ largeTupleNormScale z.2 a}

def largeTupleGroupLength {i j : ℕ} (s : Finset (Fin i ⊕ Fin j))
    (z : largeTupleBoxIndex i j) : ℝ := ∏ a ∈ s, largeTupleNormScale z.1.2 a

lemma largeTupleGroupLength_one {i j : ℕ} (s : Finset (Fin i ⊕ Fin j))
    (z : largeTupleBoxIndex i j) : 1 ≤ largeTupleGroupLength s z :=
  Finset.one_le_prod (fun a _ => z.property a)

def largeTupleGroupWeight {i j : ℕ} (ξ : ℝ) (s : Finset (Fin i ⊕ Fin j))
    (z : largeTupleBoxIndex i j) (a : s) : ℝ → ℂ :=
  largeTupleCoordinateWeight ξ z.1.1 z.1.2 a

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeTupleRestrictedWeights
attribute [-instance] _root_.instMeasurableSpace
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

def largeTupleRestrictedLength (z : largeTupleBoxIndex i j) : ℝ :=
  ∏ a : {a : Fin i ⊕ Fin j // P a}, largeTupleNormScale z.1.2 a

lemma largeTupleRestrictedLength_one (z : largeTupleBoxIndex i j) :
    1 ≤ largeTupleRestrictedLength P z :=
  Finset.one_le_prod (fun a _ => z.property a)

def largeTupleRestrictedWeight (ξ : ℝ) (z : largeTupleBoxIndex i j)
    (a : {a : Fin i ⊕ Fin j // P a}) : ℝ → ℂ :=
  largeTupleCoordinateWeight ξ z.1.1 z.1.2 a

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SinglePrimeHeight
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The published-input height mean for a single genuine prime coordinate.
This is used for the complementary Mellin frequencies of the semiprime branch. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def uniformLogWeights_prime_coordinates {γ : Type*} (L : γ → ℝ)
    (W : γ → ℝ → ℂ) (hL : ∀ r, 1 ≤ L r) (hW : UniformLogWeights W) :
    LogarithmicWeightFamily (fun z : γ × Unit => L z.1) (fun z => W z.1) := by
  refine ⟨fun z => hL z.1,fun z => hW.compact z.1,fun z => hW.positive z.1,
    fun z => hW.smooth z.1,hW.radius,hW.radius_nonneg,
    fun z => hW.support_bound z.1,?_⟩
  intro n
  obtain ⟨B,hB,hb⟩ := hW.derivative_bound n
  exact ⟨B,0,hB,by simpa only [pow_zero,mul_one] using fun z : γ × Unit => hb z.1⟩

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

def semiprimeAngularLeftLength (z : SemiprimeAngularWeightParameters) : ℝ := z.1.2

def semiprimeAngularRightLength (z : SemiprimeAngularWeightParameters) : ℝ := z.2.2

def semiprimeAngularLeftWeight (z : SemiprimeAngularWeightParameters) (_ : Unit) : ℝ → ℂ :=
  semiprimeSmoothWeight z.1.1

def semiprimeAngularRightWeight (z : SemiprimeAngularWeightParameters) (_ : Unit) : ℝ → ℂ :=
  semiprimeSmoothWeight z.2.1

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

def semiTailLeftWeight (z : SemiprimeTailParameters) (_ : Unit) : ℝ → ℂ :=
  semiprimeSmoothWeight z.1.1
def semiTailRightWeight (z : SemiprimeTailParameters) (_ : Unit) : ℝ → ℂ :=
  semiprimeSmoothWeight z.2.1

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ThetaHeatKernelBound
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential bounds for the normalized angular heat kernel. -/
noncomputable section
namespace CubicFirstMoment

lemma rpow_exp_half_bound {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : ℝ, 0 ≤ x →
      x^κ*Real.exp (-x) ≤ C*Real.exp (-x/2) := by
  let n : ℕ := ⌈κ⌉₊
  let C : ℝ := 1+(n.factorial:ℝ)/(1/2:ℝ)^n
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (by positivity)
  refine ⟨C,hC,?_⟩
  intro x hx
  have hbound : x^κ*Real.exp (-(1/2)*x) ≤ C := by
    by_cases hx1 : x ≤ 1
    · have hr := Real.rpow_le_one hx hx1 hκ
      have he : Real.exp (-(1/2)*x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      exact (show x^κ*Real.exp (-(1/2)*x) ≤ 1 by
        simpa only [one_mul] using mul_le_mul hr he (Real.exp_pos _).le zero_le_one).trans hC
    · have hr : x^κ ≤ x^n := by
        simpa only [Real.rpow_natCast] using
          Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx1) (Nat.le_ceil κ)
      exact (mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le).trans
        ((power_exp_bound (by norm_num : (0:ℝ) < 1/2) n x hx).trans (by dsimp [C]; linarith))
  calc
    x^κ*Real.exp (-x) = (x^κ*Real.exp (-(1/2)*x))*Real.exp (-x/2) := by
      rw [mul_assoc,←Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbound (Real.exp_pos _).le

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ThetaUpperVerticalBound
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform vertical bounds for upper Mellin integrals from one real moment. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def thetaUpperNormMass (f : ℝ→ℂ) (b : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0, ‖(t:ℂ)^((b:ℂ)-1) • thetaUpper f t‖

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaExponential
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform exponential decay of the nonconstant cubic cusp expansion. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaExpConstant (C : ℝ) : ℝ :=
  (C*cubicWhittakerMixedConstant*81^(8/3:ℝ))*(∑' n : Eisenstein, norm n^(-5/3:ℝ))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionGeometry
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric inversion in the cubic theta transformation, restricted
only by positive height and nonzero level. No automorphy law is assumed. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaInversion (q : ℂ) (p : ℂ × ℝ) : ℂ × ℝ :=
  (-star p.1/(q^2*(cubicThetaRadius p:ℂ)),
    p.2/(Complex.normSq q*cubicThetaRadius p))

lemma cubicThetaRadius_pos {p : ℂ × ℝ} (hp : 0 < p.2) : 0 < cubicThetaRadius p := by
  unfold cubicThetaRadius
  exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (sq_pos_of_pos hp)

lemma cubicThetaInversion_radius {q : ℂ} (hq : q ≠ 0) {p : ℂ × ℝ} (hp : 0 < p.2) :
    cubicThetaRadius (cubicThetaInversion q p) =
      (Complex.normSq q^2*cubicThetaRadius p)⁻¹ := by
  have hρ := cubicThetaRadius_pos hp
  have hN := Complex.normSq_pos.mpr hq
  unfold cubicThetaRadius cubicThetaInversion
  simp only [Complex.normSq_div,Complex.normSq_neg,Complex.star_def,Complex.normSq_conj,
    Complex.normSq_mul,map_pow,Complex.normSq_ofReal,div_pow]
  dsimp only [cubicThetaRadius] at hρ ⊢
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionInvolutive
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The level-scaled hyperbolic inversion is an involution. This fixes
its conjugations and powers before using it in a transformation formula. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaInversion_involutive {q : ℂ} (hq : q ≠ 0)
    {p : ℂ × ℝ} (hp : 0 < p.2) :
    cubicThetaInversion q (cubicThetaInversion q p) = p := by
  have hρ := cubicThetaRadius_pos hp
  have hN := Complex.normSq_pos.mpr hq
  have hρC : (cubicThetaRadius p:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hρ
  have hNC : (Complex.normSq q:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  have hqstar : star q ≠ 0 := star_ne_zero.mpr hq
  have hprod : (Complex.normSq q:ℂ) = q*star q := by
    exact (Complex.mul_conj q).symm
  have hrad := cubicThetaInversion_radius hq hp
  apply Prod.ext
  · change -star (-star p.1/(q^2*(cubicThetaRadius p:ℂ)))/
        (q^2*(cubicThetaRadius (cubicThetaInversion q p):ℂ)) = p.1
    rw [hrad]
    simp only [Complex.ofReal_inv,Complex.ofReal_mul,Complex.ofReal_pow,
      Complex.star_def,map_neg,map_div₀,map_mul,map_pow,Complex.conj_conj,Complex.conj_ofReal,
      neg_div,neg_neg]
    change p.1/((star q)^2*(cubicThetaRadius p:ℂ))/
      (q^2*((Complex.normSq q:ℂ)^2*(cubicThetaRadius p:ℂ))⁻¹) = p.1
    rw [hprod]
    field_simp
  · change (p.2/(Complex.normSq q*cubicThetaRadius p))/
        (Complex.normSq q*cubicThetaRadius (cubicThetaInversion q p)) = p.2
    rw [hrad]
    field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMobiusGenerators
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translation and level inversion matrices in the exact coordinates
used by the cubic theta Fourier and Mellin expansions. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaInversionMatrix_denominator {q : ℂ} (hq : q ≠ 0) (p : ℂ × ℝ) :
    cubicThetaMobiusDenominator (cubicThetaInversionMatrix q hq) p =
      Complex.normSq q*cubicThetaRadius p := by
  simp [cubicThetaMobiusDenominator,cubicThetaInversionMatrix,cubicThetaRadius,
    Complex.normSq_mul,mul_add]

theorem cubicThetaMobius_inversion {q : ℂ} (hq : q ≠ 0)
    {p : ℂ × ℝ} (hp : 0 < p.2) :
    cubicThetaMobius (cubicThetaInversionMatrix q hq) p = cubicThetaInversion q p := by
  have hstar : star q ≠ 0 := star_ne_zero.mpr hq
  have hρ : (cubicThetaRadius p:ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (cubicThetaRadius_pos hp)
  have hN : (Complex.normSq q:ℂ) = q*star q := (Complex.mul_conj q).symm
  apply Prod.ext
  · change cubicThetaMobiusNumerator (cubicThetaInversionMatrix q hq) p/
      (cubicThetaMobiusDenominator (cubicThetaInversionMatrix q hq) p:ℂ) = _
    rw [cubicThetaInversionMatrix_denominator]
    simp only [cubicThetaMobiusNumerator,cubicThetaInversionMatrix,Matrix.of_apply,
      Matrix.cons_val_zero,Matrix.cons_val_one,zero_mul,zero_add,
      add_zero,star_mul,Complex.ofReal_mul,hN,cubicThetaInversion]
    change (-q⁻¹*(star p.1*star q))/(q*star q*(cubicThetaRadius p:ℂ)) =
      -star p.1/(q^2*(cubicThetaRadius p:ℂ))
    field_simp
  · change p.2/cubicThetaMobiusDenominator (cubicThetaInversionMatrix q hq) p =
      p.2/(Complex.normSq q*cubicThetaRadius p)
    rw [cubicThetaInversionMatrix_denominator]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLaplaceSum
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute Laplace interchange for the Eisenstein lattice row. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

theorem cubicTheta_laplace_tsum (a : Eisenstein → ℂ) (R : Eisenstein → ℝ)
    (hR : ∀ d, 0 < R d) {s : ℂ} (hs : 0 < s.re)
    (hsum : Summable (fun d => ‖a d‖*(R d)^(-s.re))) :
    Complex.Gamma s*(∑' d : Eisenstein, a d*(R d:ℂ)^(-s)) =
      ∫ t in Ioi (0:ℝ), (t:ℂ)^(s-1)*
        ∑' d : Eisenstein, a d*(Real.exp (-R d*t):ℂ) := by
  let : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
  have hm : Summable (fun d => ∫ t in Ioi (0:ℝ), ‖cubicThetaLaplaceTerm (a d) (R d) s t‖) := by
    simp_rw [cubicThetaLaplaceTerm_mass _ (hR _) hs]
    exact hsum.mul_left _
  have hi := integral_tsum_of_summable_integral_norm
    (fun d => cubicThetaLaplaceTerm_integrable (a d) (hR d) hs) hm
  calc
    _ = ∑' d : Eisenstein, ∫ t in Ioi (0:ℝ), cubicThetaLaplaceTerm (a d) (R d) s t := by
      simp_rw [cubicThetaLaplaceTerm_integral _ (hR _) hs]
      rw [tsum_mul_left]
    _ = ∫ t in Ioi (0:ℝ), ∑' d : Eisenstein, cubicThetaLaplaceTerm (a d) (R d) s t := hi
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp only
      rw [← tsum_mul_left]
      apply tsum_congr
      intro d
      unfold cubicThetaLaplaceTerm
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaNonzeroHeat
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonzero Fourier heat integral is entire in the Eisenstein
parameter: its positive and reciprocal exponential factors control both
ends of the Mellin integral. -/
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaDoubleHeat_top (v : ℝ) {A : ℝ} (hA : 0<A) :
    cubicThetaDoubleHeat v A =O[atTop] (fun t : ℝ => Real.exp (-v^2*t)) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  rw [cubicThetaDoubleHeat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
    Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),one_mul]
  apply Real.exp_le_exp.mpr
  exact sub_le_self _ (div_pos hA ht).le

lemma cubicThetaDoubleHeat_bottom (v : ℝ) {A : ℝ} (hA : 0<A) (b : ℝ) :
    cubicThetaDoubleHeat v A =O[𝓝[>] 0] (fun t : ℝ => t^(-b)) := by
  have h := (isLittleO_exp_neg_mul_rpow_atTop hA b).isBigO.comp_tendsto
    (tendsto_inv_nhdsGT_zero : Tendsto (fun t : ℝ => t⁻¹) (𝓝[>] 0) atTop)
  change (fun t : ℝ => Real.exp (-A*t⁻¹)) =O[𝓝[>] 0] (fun t : ℝ => t⁻¹^b) at h
  have h' : (fun t : ℝ => Real.exp (-A/t)) =O[𝓝[>] 0] (fun t : ℝ => t^(-b)) := by
    simpa only [Function.comp_apply,div_eq_mul_inv,Real.rpow_neg_eq_inv_rpow] using h
  apply IsBigO.trans ?_ h'
  apply IsBigO.of_bound 1
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [cubicThetaDoubleHeat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
    Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),one_mul]
  apply Real.exp_le_exp.mpr
  have hpos : 0≤v^2*t := mul_nonneg (sq_nonneg _) (le_of_lt ht)
  rw [neg_div]
  nlinarith only [hpos]

lemma cubicThetaDoubleHeat_mellinConvergent {v A : ℝ} (hv : 0<v) (hA : 0<A)
    (s : ℂ) : MellinConvergent (cubicThetaDoubleHeat v A) s := by
  exact mellinConvergent_of_isBigO_rpow_exp (sq_pos_of_pos hv)
    ((cubicThetaDoubleHeat_continuous v A).locallyIntegrableOn measurableSet_Ioi)
    (cubicThetaDoubleHeat_top v hA) (cubicThetaDoubleHeat_bottom v hA (s.re-1))
    (by linarith)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHeatMoments
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrary inverse-frequency decay of the nonzero heat modes.
The order is chosen after the spectral parameter, without restricting
the latter to its initial half-plane. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicTheta_inverse_heat_power_bound {A t : ℝ} (hA : 0<A) (ht : 0<t) (k : ℕ) :
    Real.exp (-A/t)≤((k.factorial:ℝ)/A^k)*t^k := by
  have h := power_exp_bound (by norm_num : (0:ℝ)<1) k (A/t) (div_pos hA ht).le
  simp only [one_pow,div_one,neg_one_mul] at h
  rw [div_pow,div_mul_eq_mul_div] at h
  have hh := (div_le_iff₀ (pow_pos ht k)).mp h
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (pow_pos hA k)).mpr
  simpa only [mul_comm,neg_div] using hh

lemma cubicThetaNonzeroHeat_integrable {v A : ℝ} (hv : 0<v) (hA : 0<A) (s : ℂ) :
    IntegrableOn (cubicThetaDualHeat v s A) (Ioi 0) := by
  have h := cubicThetaDoubleHeat_mellinConvergent hv hA (s-1)
  change IntegrableOn (fun t : ℝ => (t:ℂ)^(s-2)*(Real.exp (-v^2*t-A/t):ℂ)) (Ioi 0)
  simpa only [MellinConvergent,smul_eq_mul,cubicThetaDoubleHeat,
    show s-1-1=s-2 by ring] using h

lemma cubicThetaNonzeroHeat_norm_mass_power {v A : ℝ} (hv : 0<v) (hA : 0<A)
    (s : ℂ) (k : ℕ) (hk : 0 < s.re+(k:ℝ)-1) :
    (∫ t in Ioi (0:ℝ), ‖cubicThetaDualHeat v s A t‖)≤
      ((k.factorial:ℝ)/A^k)*
        (Real.Gamma (s.re+(k:ℝ)-1)*(v^2)^(-(s.re+(k:ℝ)-1))) := by
  have hi := (integrable_laplace_rpow hk (sq_pos_of_pos hv)).const_mul
    ((k.factorial:ℝ)/A^k)
  calc
    _ ≤ ∫ t in Ioi (0:ℝ), ((k.factorial:ℝ)/A^k)*
        (t^((s.re+(k:ℝ)-1)-1)*Real.exp (-v^2*t)) := by
      apply integral_mono_ae (cubicThetaNonzeroHeat_integrable hv hA s).norm hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [cubicThetaDualHeat_norm v s A ht]
      calc
        _ ≤ t^(s.re-2)*Real.exp (-v^2*t)*(((k.factorial:ℝ)/A^k)*t^k) :=
          mul_le_mul_of_nonneg_left (cubicTheta_inverse_heat_power_bound hA ht k)
            (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _))
        _ = _ := by
          have he : t^(s.re-2)*t^k=t^((s.re+(k:ℝ)-1)-1) := by
            rw [←Real.rpow_natCast,←Real.rpow_add ht]
            congr 1
            ring
          calc
            _ = ((k.factorial:ℝ)/A^k)*(t^(s.re-2)*t^k)*Real.exp (-v^2*t) := by ring
            _ = _ := by rw [he]; ring
    _ = _ := by rw [integral_const_mul,laplace_rpow hk (sq_pos_of_pos hv)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateAxis
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate lines used for the spatial derivatives of the series. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaCoordinateLine_center (k : CubicThetaAxis) (x y v : ℝ) :
    cubicThetaCoordinateLine k x y v (cubicThetaCoordinateCenter k x y v)=
      cubicThetaCartesianPoint x y v := by
  cases k <;> rfl

lemma cubicThetaCoordinateLine_continuous (k : CubicThetaAxis) (x y v : ℝ) :
    Continuous (cubicThetaCoordinateLine k x y v) := by
  cases k <;> unfold cubicThetaCoordinateLine cubicThetaCartesianPoint <;> fun_prop

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalBudget
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each coordinate line has a neighborhood with uniformly positive
height and a bounded Eisenstein majorant constant. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaHeightBudget_continuousAt {p : ℝ → ℂ × ℝ} {t : ℝ}
    (hp : ContinuousAt p t) (ht : 0<(p t).2) :
    ContinuousAt (fun w => (p w).2*cubicThetaHeightConstant (p w)) t := by
  unfold cubicThetaHeightConstant
  have hn : (p t).2^2≠0 := pow_ne_zero _ ht.ne'
  fun_prop

lemma cubicThetaCoordinate_local_budget (k : CubicThetaAxis) (x y : ℝ)
    {v : ℝ} (hv : 0<v) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Set.Ioo
      (cubicThetaCoordinateCenter k x y v-r) (cubicThetaCoordinateCenter k x y v+r),
      v/2 < (cubicThetaCoordinateLine k x y v t).2 ∧
      (cubicThetaCoordinateLine k x y v t).2*
        cubicThetaHeightConstant (cubicThetaCoordinateLine k x y v t) <
          v*cubicThetaHeightConstant (cubicThetaCartesianPoint x y v)+1 := by
  let w := cubicThetaCoordinateCenter k x y v
  let p := cubicThetaCoordinateLine k x y v
  have hp : ContinuousAt p w := (cubicThetaCoordinateLine_continuous k x y v).continuousAt
  have hp0 : (p w).2=v := congrArg Prod.snd (cubicThetaCoordinateLine_center k x y v)
  have he1 : ∀ᶠ t in 𝓝 w, v/2<(p t).2 := hp.snd.eventually_const_lt (by change v/2<(p w).2; rw [hp0]; linarith)
  have he2 : ∀ᶠ t in 𝓝 w, (p t).2*cubicThetaHeightConstant (p t)<
      v*cubicThetaHeightConstant (cubicThetaCartesianPoint x y v)+1 := by
    apply (cubicThetaHeightBudget_continuousAt hp (by rw [hp0]; exact hv)).eventually_lt_const
    dsimp [p,w]
    rw [cubicThetaCoordinateLine_center]
    change v*cubicThetaHeightConstant (cubicThetaCartesianPoint x y v)<
      v*cubicThetaHeightConstant (cubicThetaCartesianPoint x y v)+1
    linarith
  obtain ⟨r,hr,hbound⟩ := Metric.eventually_nhds_iff.mp (he1.and he2)
  refine ⟨r,hr,?_⟩
  intro t ht
  apply hbound
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalOperator
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Locality and finite additivity of the actual hyperbolic operator
for twice continuously differentiable functions. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace CubicFirstMoment

lemma cubicThetaHyperbolicOperator_germ {F G : ℂ × ℝ → ℂ} (x y v : ℝ)
    (h : F =ᶠ[𝓝 (cubicThetaCartesianPoint x y v)] G) :
    cubicThetaHyperbolicOperator (fun a b t => F (cubicThetaCartesianPoint a b t)) x y v=
      cubicThetaHyperbolicOperator (fun a b t => G (cubicThetaCartesianPoint a b t)) x y v := by
  have hx : Continuous (fun t : ℝ => cubicThetaCartesianPoint t y v) :=
    (Complex.continuous_ofReal.add continuous_const).prodMk continuous_const
  have hy : Continuous (fun t : ℝ => cubicThetaCartesianPoint x t v) :=
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).prodMk continuous_const
  have ht : Continuous (fun t : ℝ => cubicThetaCartesianPoint x y t) :=
    continuous_const.prodMk continuous_id
  have ex := h.comp_tendsto (hx.tendsto x)
  have ey := h.comp_tendsto (hy.tendsto y)
  have et := h.comp_tendsto (ht.tendsto v)
  dsimp only [Function.comp_def] at ex ey et
  unfold cubicThetaHyperbolicOperator
  rw [ex.deriv.deriv_eq,ey.deriv.deriv_eq,et.deriv.deriv_eq,et.deriv_eq]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticEquation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual arithmetic remainder satisfies the same forced spectral
operator as the continued global weak response. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace CubicFirstMoment

lemma cubicThetaHyperbolicOperator_sub {F G : ℝ → ℝ → ℝ → ℂ} (x y v : ℝ)
    (hF : ∀ k, ContDiffAt ℝ 2 (cubicThetaAxisFunction F k x y v) (cubicThetaCoordinateCenter k x y v))
    (hG : ∀ k, ContDiffAt ℝ 2 (cubicThetaAxisFunction G k x y v) (cubicThetaCoordinateCenter k x y v)) :
    cubicThetaHyperbolicOperator (fun a b t => F a b t-G a b t) x y v=
      cubicThetaHyperbolicOperator F x y v-cubicThetaHyperbolicOperator G x y v := by
  have hx := second_sub (hF .x) (hG .x)
  have hy := second_sub (hF .y) (hG .y)
  have ht := second_sub (hF .height) (hG .height)
  have h₁ := deriv_sub ((hF .height).differentiableAt (by norm_num))
    ((hG .height).differentiableAt (by norm_num))
  dsimp only [cubicThetaAxisFunction,cubicThetaCoordinateCenter] at hx hy ht h₁
  change deriv (fun t => F x y t-G x y t) v=
    deriv (fun t => F x y t) v-deriv (fun t => G x y t) v at h₁
  unfold cubicThetaHyperbolicOperator
  rw [hx,hy,ht,h₁]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAxisDifferentials
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate derivatives are actual directional derivatives on
complex-horizontal and real-height space. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

def cubicThetaAxisSecond (k : CubicThetaAxis) (f : ℂ × ℝ → ℂ) (p : ℂ × ℝ) : ℂ :=
  deriv (deriv (fun t => f (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t)))
    (cubicThetaCoordinateCenter k p.1.re p.1.im p.2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticAxisRegularity
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal arithmetic remainder has continuous pure second
coordinate derivatives and the corresponding actual line derivatives. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaAxisSecond_sub (k : CubicThetaAxis) (f g : ℂ × ℝ → ℂ) (p : ℂ × ℝ)
    (hf : ContDiffAt ℝ 2 (fun t => f (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t))
      (cubicThetaCoordinateCenter k p.1.re p.1.im p.2))
    (hg : ContDiffAt ℝ 2 (fun t => g (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t))
      (cubicThetaCoordinateCenter k p.1.re p.1.im p.2)) :
    cubicThetaAxisSecond k (f-g) p=cubicThetaAxisSecond k f p-cubicThetaAxisSecond k g p := by
  let c := cubicThetaCoordinateCenter k p.1.re p.1.im p.2
  let F := fun t => f (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t)
  let G := fun t => g (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t)
  have he : deriv (F-G)=ᶠ[𝓝 c] (fun t => deriv F t-deriv G t) := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with t ht hu
    exact deriv_sub (ht.differentiableAt (by norm_num)) (hu.differentiableAt (by norm_num))
  change deriv (deriv (F-G)) c=deriv (deriv F) c-deriv (deriv G) c
  rw [he.deriv_eq]
  exact deriv_sub ((hf.derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEisensteinTorus
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual nonconstant Eisenstein Fourier series is a continuous
function on its period torus. Its coefficients retain the arithmetic
Dirichlet series and heat integral, including the zero-mode exclusion. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.instMeasureSpaceUnitAddCircle_solutions_4
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
attribute [local instance] Classical.propDecidable

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaTorusCellIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Haar integration on the cusp torus agrees with the actual half-open
level-three cell, including its boundary convention and Jacobian. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.cubicThetaTorusCellMeasureSpace
lemma cubicThetaTorus_integral_cell (f : UnitAddTorus (Fin 2) → ℂ) :
    (∫ t, f t)=∫ x in {x : Fin 2 → ℝ | ∀ i, x i∈Ico (0:ℝ) 1},
      f (fun i => (x i:UnitAddCircle)) := by
  rw [cubicThetaCube_halfOpen_measure]
  simpa only [Pi.zero_apply,zero_add] using UnitAddTorus.integral_preimage f (0 : Fin 2 → ℝ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinatePairing
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
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

def cubicThetaTangentValues : ((ℂ × ℝ) →L[ℝ] ℂ) →ₗ[ℂ] CubicThetaGradient where
  toFun L := WithLp.toLp 2 (fun i => L (cubicThetaTangentCoordinates (cubicThetaTangentBasis i)))
  map_add' L M := by ext i; rfl
  map_smul' c L := by ext i; rfl

lemma cubicThetaTangentValues_norm (L : (ℂ × ℝ) →L[ℝ] ℂ) :
    ‖cubicThetaTangentValues L‖=‖cubicThetaCoordinateValues L‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  change cubicThetaTangentEnergy (L.comp cubicThetaTangentCoordinates.toContinuousLinearMap)=_
  rw [cubicThetaTangentEnergy_coordinates]
  simp [cubicThetaCoordinateValues,Fin.sum_univ_succ,add_assoc]

lemma cubicThetaTangentValues_inner (L M : (ℂ × ℝ) →L[ℝ] ℂ) :
    inner ℂ (cubicThetaTangentValues L) (cubicThetaTangentValues M)=
      star (L (1,0))*M (1,0)+star (L (Complex.I,0))*M (Complex.I,0)+
        star (L (0,1))*M (0,1) := by
  rw [cubicThetaLinear_inner_of_norm_eq cubicThetaTangentValues cubicThetaCoordinateValues
    cubicThetaTangentValues_norm]
  simp [cubicThetaCoordinateValues,PiLp.inner_apply,Fin.sum_univ_succ,RCLike.inner_apply,mul_comm,add_assoc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHeatScaling
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A height dilation turns the weighted heat coefficient into one
Mellin kernel, independent of the spectral parameter. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaLinearHeat_scale {v t : ℝ} (hv : 0<v) (ht : 0<t)
    (A : ℝ) (s : ℂ) :
    (v:ℂ)^s*cubicThetaDualHeat v s A t=
      (v:ℂ)^2*((v*t:ℝ):ℂ)^(s-2)*cubicThetaLinearHeat v A (v*t) := by
  have he : -v*(v*t)-A*v/(v*t) = -v^2*t-A/t := by field_simp
  have hp : (v:ℂ)^2*(v:ℂ)^(s-2)=(v:ℂ)^s := by
    rw [← Complex.cpow_natCast,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hv.ne')]
    congr 1
    ring
  unfold cubicThetaDualHeat cubicThetaLinearHeat
  rw [he,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hv.le ht.le]
  rw [← mul_assoc ((v:ℂ)^2) ((v:ℂ)^(s-2)),hp]
  ring

lemma cubicThetaHeat_height_dilation {v : ℝ} (hv : 0<v) (A : ℝ) (s : ℂ) :
    (v:ℂ)^s*(∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s A t)=
      (v:ℂ)*(∫ u in Ioi (0:ℝ), (u:ℂ)^(s-2)*cubicThetaLinearHeat v A u) := by
  let g := fun u : ℝ => (u:ℂ)^(s-2)*cubicThetaLinearHeat v A u
  have hi := integral_comp_mul_left_Ioi g 0 hv
  rw [mul_zero] at hi
  calc
    _ = (v:ℂ)^2*(∫ t in Ioi (0:ℝ), g (v*t)) := by
      rw [← integral_const_mul,← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only [g]
      simpa only [mul_assoc] using cubicThetaLinearHeat_scale hv ht A s
    _ = _ := by
      rw [hi,Complex.real_smul,Complex.ofReal_inv]
      dsimp only [g]
      field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAveragedHeat
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging the dilated heat kernel against a fixed radial test preserves
exponential decay at both endpoints of its Mellin variable. -/
noncomputable section
open Set MeasureTheory Filter Asymptotics
open scoped CompactlySupported Topology
namespace CubicFirstMoment

lemma cubicThetaLinearHeat_average_bound (W : C_c(ℝ,ℂ)) {A u v : ℝ}
    (hA : 0<A) (hu : 0<u) (hv : 2<v) :
    ‖star (W v)/(v:ℂ)^2*cubicThetaLinearHeat v A u‖≤
      (‖W v‖/v^2)*‖cubicThetaDoubleHeat 1 A u‖ := by
  have he : -v*u-A*v/u≤-(1:ℝ)^2*u-A/u := by
    have h₁ := mul_le_mul_of_nonneg_right (show (1:ℝ)≤v by linarith) hu.le
    have h₂ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (show (1:ℝ)≤v by linarith) hA.le) hu.le
    norm_num only [one_pow,neg_one_mul,one_mul,mul_one] at h₁ h₂ ⊢
    linarith
  simp only [norm_mul,norm_div,norm_star,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,sq_abs,cubicThetaLinearHeat,cubicThetaDoubleHeat,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
    (div_nonneg (_root_.norm_nonneg _) (sq_nonneg _))

lemma cubicThetaDoubleHeat_norm_le_one {A u : ℝ} (hA : 0<A) (hu : 0<u) :
    ‖cubicThetaDoubleHeat 1 A u‖≤1 := by
  rw [cubicThetaDoubleHeat,Complex.norm_real,Real.norm_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_le_one_iff.mpr
  have hp : 0<A/u := div_pos hA hu
  nlinarith

lemma cubicThetaAveragedHeat_integrable (W : C_c(ℝ,ℂ)) {A u : ℝ}
    (hA : 0<A) (hu : 0<u) :
    IntegrableOn (fun v : ℝ => star (W v)/(v:ℂ)^2*cubicThetaLinearHeat v A u)
      (Ioi (2:ℝ)) := by
  apply (cubicThetaRadialWeight_integrable W).mono' (by
    apply Measurable.aestronglyMeasurable
    unfold cubicThetaLinearHeat
    fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact (cubicThetaLinearHeat_average_bound W hA hu hv).trans
    ((mul_le_mul_of_nonneg_left (cubicThetaDoubleHeat_norm_le_one hA hu)
      (div_nonneg (_root_.norm_nonneg _) (sq_nonneg _))).trans_eq (mul_one _))

lemma cubicThetaAveragedHeat_bound (W : C_c(ℝ,ℂ)) {A u : ℝ}
    (hA : 0<A) (hu : 0<u) :
    ‖cubicThetaAveragedHeat W A u‖≤
      cubicThetaRadialWeightMass W*‖cubicThetaDoubleHeat 1 A u‖ := by
  apply (norm_integral_le_integral_norm _).trans
  rw [cubicThetaRadialWeightMass,← integral_mul_const]
  apply integral_mono_ae (cubicThetaAveragedHeat_integrable W hA hu).norm
    ((cubicThetaRadialWeight_integrable W).mul_const _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact cubicThetaLinearHeat_average_bound W hA hu hv

lemma cubicThetaAveragedHeat_continuous (W : C_c(ℝ,ℂ)) {A : ℝ} (hA : 0<A) :
    ContinuousOn (cubicThetaAveragedHeat W A) (Ioi (0:ℝ)) := by
  apply continuousOn_of_dominated
    (bound:=fun v : ℝ => ‖W v‖/v^2)
  · intro u hu
    apply Measurable.aestronglyMeasurable
    unfold cubicThetaLinearHeat
    fun_prop
  · intro u hu
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact (cubicThetaLinearHeat_average_bound W hA hu hv).trans
      ((mul_le_mul_of_nonneg_left (cubicThetaDoubleHeat_norm_le_one hA hu)
        (div_nonneg (_root_.norm_nonneg _) (sq_nonneg _))).trans_eq (mul_one _))
  · exact cubicThetaRadialWeight_integrable W
  · filter_upwards with v
    have hc : ContinuousOn (fun u : ℝ => -v*u-A*v/u) (Ioi 0) :=
      (continuousOn_const.mul continuousOn_id).sub
        (continuousOn_const.div continuousOn_id (fun u hu => ne_of_gt hu))
    exact continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn (Real.continuous_exp.comp_continuousOn hc))

lemma cubicThetaAveragedHeat_top (W : C_c(ℝ,ℂ)) {A : ℝ} (hA : 0<A) :
    cubicThetaAveragedHeat W A =O[atTop] (fun u : ℝ => Real.exp (-(1:ℝ)*u)) := by
  have ht : cubicThetaDoubleHeat 1 A =O[atTop] (fun u : ℝ => Real.exp (-(1:ℝ)*u)) := by
    simpa only [one_pow] using cubicThetaDoubleHeat_top 1 hA
  apply IsBigO.trans ?_ ht
  apply IsBigO.of_bound (cubicThetaRadialWeightMass W)
  filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
  exact cubicThetaAveragedHeat_bound W hA hu

lemma cubicThetaAveragedHeat_bottom (W : C_c(ℝ,ℂ)) {A : ℝ} (hA : 0<A) (b : ℝ) :
    cubicThetaAveragedHeat W A =O[𝓝[>] 0] (fun u : ℝ => u^(-b)) := by
  apply IsBigO.trans ?_ (cubicThetaDoubleHeat_bottom 1 hA b)
  apply IsBigO.of_bound (cubicThetaRadialWeightMass W)
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact cubicThetaAveragedHeat_bound W hA hu

lemma cubicThetaAveragedHeat_mellinConvergent (W : C_c(ℝ,ℂ)) {A : ℝ} (hA : 0<A)
    (s : ℂ) : MellinConvergent (cubicThetaAveragedHeat W A) s := by
  exact mellinConvergent_of_isBigO_rpow_exp (by norm_num : (0:ℝ)<1)
    ((cubicThetaAveragedHeat_continuous W hA).locallyIntegrableOn measurableSet_Ioi)
    (cubicThetaAveragedHeat_top W hA) (cubicThetaAveragedHeat_bottom W hA (s.re-1))
    (by linarith)

theorem cubicThetaAveragedHeat_mellin_entire (W : C_c(ℝ,ℂ)) {A : ℝ} (hA : 0<A) :
    Differentiable ℂ (mellin (cubicThetaAveragedHeat W A)) := by
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow_exp (by norm_num : (0:ℝ)<1)
    ((cubicThetaAveragedHeat_continuous W hA).locallyIntegrableOn measurableSet_Ioi)
    (cubicThetaAveragedHeat_top W hA) (cubicThetaAveragedHeat_bottom W hA (s.re-1))
    (by linarith)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCompactExponential
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entire dependence of the compact incoming correction. Only an
integrable amplitude and a bounded continuous real exponent are needed. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace CubicFirstMoment

lemma cubicThetaCompactExponential_differentiable {K : Set CubicThetaPoint}
    (hK : IsCompact K) (a : CubicThetaPoint → ℂ)
    (ha : IntegrableOn a K cubicThetaPointMeasure)
    (b : CubicThetaPoint → ℝ) (hb : ContinuousOn b K) :
    Differentiable ℂ (fun s : ℂ =>
      ∫ p in K,a p*Complex.exp (s*(b p:ℂ)) ∂cubicThetaPointMeasure) := by
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hb
  let M := max C 0
  have hM : 0≤M := le_max_right _ _
  have hbM (p : CubicThetaPoint) (hp : p∈K) : |b p|≤M :=
    (hC p hp).trans (le_max_left _ _)
  intro s
  let H := Real.exp ((‖s‖+1)*M)
  have hH : 0<H := Real.exp_pos _
  let F : ℂ → CubicThetaPoint → ℂ := fun z p => a p*Complex.exp (z*(b p:ℂ))
  let F' : ℂ → CubicThetaPoint → ℂ := fun z p => a p*(Complex.exp (z*(b p:ℂ))*(b p:ℂ))
  have hm (z : ℂ) : AEStronglyMeasurable (F z) (cubicThetaPointMeasure.restrict K) := by
    apply ha.aestronglyMeasurable.mul
    exact (Complex.continuous_exp.comp_continuousOn
      (continuous_const.continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn hb))).aestronglyMeasurable hK.measurableSet
  have hm' : AEStronglyMeasurable (F' s) (cubicThetaPointMeasure.restrict K) := by
    apply ha.aestronglyMeasurable.mul
    apply ContinuousOn.aestronglyMeasurable _ hK.measurableSet
    exact (Complex.continuous_exp.comp_continuousOn
      (continuous_const.continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn hb))).mul
        (Complex.continuous_ofReal.comp_continuousOn hb)
  have he (z : ℂ) (hz : ‖z‖≤‖s‖+1) (p : CubicThetaPoint) (hp : p∈K) :
      ‖Complex.exp (z*(b p:ℂ))‖≤H := by
    apply (Complex.norm_exp_le_exp_norm _).trans
    apply Real.exp_le_exp.mpr
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul hz (hbM p hp) (abs_nonneg _) (by positivity)
  have hi : Integrable (F s) (cubicThetaPointMeasure.restrict K) := by
    apply (ha.norm.mul_const H).mono' (hm s)
    filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (he s (by linarith) p hp) (_root_.norm_nonneg _)
  have hd : ∀ᵐ p ∂cubicThetaPointMeasure.restrict K,∀ z∈Metric.ball s 1,
      HasDerivAt (fun w => F w p) (F' z p) z := by
    filter_upwards with p z _
    simpa only [F,F',id_eq,one_mul] using
      (((hasDerivAt_id z).mul_const (b p:ℂ)).cexp.const_mul (a p))
  have hbound : ∀ᵐ p ∂cubicThetaPointMeasure.restrict K,∀ z∈Metric.ball s 1,
      ‖F' z p‖≤‖a p‖*(H*M) := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with p hp z hz
    have hz' : ‖z‖≤‖s‖+1 := by
      have ht := norm_le_norm_add_norm_sub s z
      rw [Metric.mem_ball,dist_eq_norm] at hz
      rw [norm_sub_rev s z] at ht
      linarith
    dsimp only [F']
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
    exact mul_le_mul (he z hz' p hp) (hbM p hp) (abs_nonneg _) hH.le
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s zero_lt_one) (Eventually.of_forall hm) hi hm' hbound
    (ha.norm.mul_const (H*M)) hd).2.differentiableAt

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaComplexHeight
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Holomorphic dependence of the Fourier heat integral on a complex
height with positive real part. All majorants are actual heat integrals. -/
noncomputable section
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

lemma cubicThetaHeightMajorant_eq (s : ℂ) (A : ℝ) {d : ℝ} (hd : 0<d)
    {t : ℝ} (ht : 0<t) :
    cubicThetaHeightMajorant s A d t=‖cubicThetaDualHeat (Real.sqrt d) s (A*d) t‖ := by
  rw [cubicThetaDualHeat_norm _ _ _ ht,Real.sq_sqrt hd.le]
  unfold cubicThetaHeightMajorant
  rw [mul_assoc,← Real.exp_add]
  congr 2
  ring

lemma cubicThetaHeightMajorant_integrable (s : ℂ) {A d : ℝ} (hA : 0<A) (hd : 0<d) :
    IntegrableOn (cubicThetaHeightMajorant s A d) (Ioi 0) := by
  apply (cubicThetaNonzeroHeat_integrable (Real.sqrt_pos.mpr hd) (mul_pos hA hd) s).norm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (cubicThetaHeightMajorant_eq s A hd ht).symm

lemma cubicThetaHeightDerivative_integrable (s : ℂ) {A d : ℝ} (hA : 0<A) (hd : 0<d) :
    IntegrableOn (fun t => (t+A/t)*cubicThetaHeightMajorant s A d t) (Ioi 0) := by
  have hp := cubicThetaHeightMajorant_integrable (s+1) hA hd
  have hm := (cubicThetaHeightMajorant_integrable (s-1) hA hd).const_mul A
  apply (hp.add hm).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : t*t^(s.re-2)=t^((s+1).re-2) := by
    calc
      _ = t^(1:ℝ)*t^(s.re-2) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add ht]
        congr 1
        simp only [Complex.add_re,Complex.one_re]
        ring
  have ht2 : t^(s.re-2)/t=t^((s-1).re-2) := by
    calc
      _ = t^(s.re-2)/t^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_sub ht]
        congr 1
        simp only [Complex.sub_re,Complex.one_re]
        ring
  simp only [Pi.add_apply,cubicThetaHeightMajorant]
  rw [← ht1,← ht2]
  ring

lemma cubicThetaComplexHeightIntegral_differentiableAt (s : ℂ) {A : ℝ} (hA : 0<A)
    {z : ℂ} (hz : 0<z.re) :
    DifferentiableAt ℂ (cubicThetaComplexHeightIntegral s A) z := by
  let d := z.re/2
  have hd : 0<d := half_pos hz
  let U : Set ℂ := {w | d<w.re}
  have hU : U∈𝓝 z := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show d<z.re by dsimp [d]; linarith)
  let F' (w : ℂ) (t : ℝ) := -((t+A/t:ℝ):ℂ)*cubicThetaComplexHeightHeat s A w t
  have hmeas (w : ℂ) : AEStronglyMeasurable (cubicThetaComplexHeightHeat s A w)
      (volume.restrict (Ioi 0)) := by
    apply Measurable.aestronglyMeasurable
    unfold cubicThetaComplexHeightHeat
    fun_prop
  have hint : IntegrableOn (cubicThetaComplexHeightHeat s A z) (Ioi 0) := by
    apply (cubicThetaHeightMajorant_integrable s hA hd).mono' (hmeas z)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cubicThetaComplexHeightHeat_bound s hA hd (by dsimp [d]; linarith) ht
  have hderivmeas : AEStronglyMeasurable (F' z) (volume.restrict (Ioi 0)) := by
    apply Measurable.aestronglyMeasurable
    dsimp [F',cubicThetaComplexHeightHeat]
    fun_prop
  have hb : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), ∀ w∈U,
      ‖F' w t‖≤(t+A/t)*cubicThetaHeightMajorant s A d t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0<t at ht
    intro w hw
    change d<w.re at hw
    dsimp only [F']
    rw [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0<t+A/t)]
    exact mul_le_mul_of_nonneg_left (cubicThetaComplexHeightHeat_bound s hA hd hw.le ht)
      (by positivity)
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), ∀ w∈U,
      HasDerivAt (fun w => cubicThetaComplexHeightHeat s A w t) (F' w t) w :=
    Filter.Eventually.of_forall (fun t w _ => cubicThetaComplexHeightHeat_deriv s w A t)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hU
    (Filter.Eventually.of_forall hmeas) hint hderivmeas hb
    (cubicThetaHeightDerivative_integrable s hA hd) hdiff).2.differentiableAt

theorem cubicThetaComplexHeightIntegral_analytic (s : ℂ) {A : ℝ} (hA : 0<A)
    {z : ℂ} (hz : 0<z.re) : AnalyticAt ℂ (cubicThetaComplexHeightIntegral s A) z := by
  have hd : DifferentiableOn ℂ (cubicThetaComplexHeightIntegral s A) {w : ℂ | 0<w.re} :=
    fun w hw => (cubicThetaComplexHeightIntegral_differentiableAt s hA hw).differentiableWithinAt
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaComplexPointMeasure
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The already computed hyperbolic Jacobian also applies to the
nonintegral prime normalizer on the same positive-height space. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

instance cubicThetaComplexPointAction_continuous : ContinuousConstSMul SL(2,ℂ) CubicThetaPoint where
  continuous_const_smul g := by
    change Continuous (fun x : CubicThetaPoint =>
      (⟨cubicThetaMobius g x.val,cubicThetaMobius_height_pos _ x.property⟩ : CubicThetaPoint))
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (cubicThetaMobius_continuousAt g x.property).comp
      (x:=x) (f:=fun y : CubicThetaPoint => y.val) continuous_subtype_val.continuousAt

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaIntegerBox
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coordinate boxes for the quantitative arithmetic theta tail. -/
noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace CubicFirstMoment

def cubicThetaIntegerRadius (p : CubicThetaIntegerPoint) : ℕ :=
  max p.1.natAbs p.2.natAbs

def cubicThetaIntegerBox (k : ℕ) : Finset CubicThetaIntegerPoint :=
  (Finset.Icc (-(k:ℤ)) k).product (Finset.Icc (-(k:ℤ)) k)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateNormBounds
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square-root norm bounds outside finite coordinate boxes. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaIntegerQuadratic (p : CubicThetaIntegerPoint) : ℝ :=
  (p.1:ℝ)^2-(p.1:ℝ)*(p.2:ℝ)+(p.2:ℝ)^2

def cubicThetaPrimaryQuadratic (p : CubicThetaIntegerPoint) : ℝ :=
  (1+3*(p.1:ℝ))^2-(1+3*(p.1:ℝ))*(3*(p.2:ℝ))+(3*(p.2:ℝ))^2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateProfile
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise geometric majorants beyond the finite coordinate boxes. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicThetaPrimaryTailMass (p : CubicThetaIntegerPoint) : ℝ :=
  cubicThetaPrimaryQuadratic p*Real.exp (-(241/100:ℝ)*Real.sqrt (cubicThetaPrimaryQuadratic p))

def cubicThetaRamifiedTailMass (p : CubicThetaIntegerPoint) : ℝ :=
  cubicThetaIntegerQuadratic p*Real.exp (-(29/4:ℝ)*Real.sqrt (cubicThetaIntegerQuadratic p))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteCoordinateBox
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal finite coordinate boxes are bounded by rational certificates. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaPrimaryBoxWeight (p : CubicThetaIntegerPoint) : ℝ :=
  if p=(0,0) then 0 else
    let n : ℕ := ((1+3*p.1)^2-(1+3*p.1)*(3*p.2)+(3*p.2)^2).toNat
    (n:ℝ)*cubicThetaPrimaryBoxBound n

def cubicThetaRamifiedBoxWeight (p : CubicThetaIntegerPoint) : ℝ :=
  if p=(0,0) then 0 else
    let n : ℕ := (p.1^2-p.1*p.2+p.2^2).toNat
    (n:ℝ)*cubicThetaRamifiedBoxBound n

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFourierBessel
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Fourier heat kernel at the cubic Eisenstein pole s=4/3.
The resulting Bessel function is the literal kernel already used in theta. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicTheta_cubicPole_heat {A v : ℝ} (hA : 0 < A) (hv : 0 < v) :
    (∫ t in Ioi (0:ℝ), ((t^(-2/3:ℝ):ℝ):ℂ)*
      (Real.exp (-v^2*t-A/t):ℂ)) =
      ((A^(1/3:ℝ)/(A*v^2)^(1/6:ℝ):ℝ):ℂ)*
        (cubicBesselKernel (A*v^2):ℂ) := by
  let H : ℝ → ℂ := fun u => (Real.exp (-u)*Real.exp (-(A*v^2)/u):ℝ)
  have hc := inverse_mellin_change H (4/3) hA
  have hleft : (∫ t in Ioi (0:ℝ), ((t^(-2/3:ℝ):ℝ):ℂ)*
      (Real.exp (-v^2*t-A/t):ℂ)) =
      ∫ t in Ioi (0:ℝ), ((t^((4/3:ℝ)-2):ℝ):ℂ)*H (A/t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have he : -(A*v^2)/(A/t) = -v^2*t := by field_simp
    dsimp only [H]
    rw [he, ← Real.exp_add]
    rw [show (4/3:ℝ)-2 = -2/3 by norm_num]
    congr 2
    ring_nf
  rw [hleft, hc]
  have hright : (∫ u in Ioi (0:ℝ), ((u^(-(4/3:ℝ)):ℝ):ℂ)*H u) =
      ((∫ u in Ioi (0:ℝ), cubicBesselHeat (A*v^2) u):ℝ) := by
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp only [H, cubicBesselHeat]
    push_cast
    norm_num only [neg_div]
    ring
  rw [hright]
  have hx : (A*v^2)^(1/6:ℝ) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (mul_pos hA (sq_pos_of_pos hv)) _)
  unfold cubicBesselKernel
  norm_num only
  push_cast
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHeatSmallNonzero
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small-height Gamma limit applies to the actual Fourier heat
kernel, and proves that it cannot vanish identically in height. -/
noncomputable section
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

lemma cubicThetaNormalizedHeat_scale (s : ℂ) (A : ℝ) {v : ℝ} (hv : 0<v) :
    (∫ t in Ioi (0:ℝ), cubicThetaNormalizedHeat s A v t)=
      ((v^2:ℝ):ℂ)^(s-1)*(∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s A t) := by
  let a : ℝ := v^2
  have ha : 0<a := sq_pos_of_pos hv
  have hac : (a:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hi := integral_comp_mul_left_Ioi (cubicThetaNormalizedHeat s A v) 0 ha
  rw [mul_zero,Complex.real_smul,Complex.ofReal_inv] at hi
  have he : (∫ t in Ioi (0:ℝ), cubicThetaNormalizedHeat s A v (a*t))=
      (a:ℂ)^(s-2)*(∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s A t) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change 0<t at ht
    dsimp only [cubicThetaNormalizedHeat,cubicThetaDualHeat]
    rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg ha.le ht.le]
    have hfrac : -A*v^2/(a*t)=-A/t := by dsimp [a]; field_simp
    rw [hfrac]
    change (Real.exp (-(a*t)):ℂ)*((a:ℂ)^(s-2)*(t:ℂ)^(s-2))*(Real.exp (-A/t):ℂ)=_
    rw [show -v^2*t-A/t=-(a*t)+(-A/t) by dsimp [a]; ring,Real.exp_add,
      Complex.ofReal_mul]
    ring
  have hp : (a:ℂ)*(a:ℂ)^(s-2)=(a:ℂ)^(s-1) := by
    calc
      _ = (a:ℂ)^(1:ℂ)*(a:ℂ)^(s-2) := by rw [Complex.cpow_one]
      _ = _ := by rw [← Complex.cpow_add _ _ hac]; congr 1; ring
  calc
    _ = (a:ℂ)*(∫ t in Ioi (0:ℝ), cubicThetaNormalizedHeat s A v (a*t)) := by
      rw [hi]
      field_simp
    _ = (a:ℂ)^ (s-1)*(∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s A t) := by
      rw [he,← mul_assoc,hp]

theorem cubicThetaDualHeat_eventually_nonzero {s : ℂ} (hs : 1 < s.re)
    {A : ℝ} (hA : 0≤A) :
    ∀ᶠ v in 𝓝[>] (0:ℝ), (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s A t)≠0 := by
  have hG : Complex.Gamma (s-1)≠0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hn := (cubicThetaNormalizedHeat_gamma_limit hs hA).eventually
    (eventually_ne_nhds hG)
  filter_upwards [nhdsWithin_le_nhds hn,self_mem_nhdsWithin] with v hv hpos
  intro hz
  rw [cubicThetaNormalizedHeat_scale s A hpos,hz,mul_zero] at hv
  exact hv rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHighHeatNonzero
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! For each parameter in Re(s)>1, the genuine Fourier heat kernel is
nonzero at some height above two. This removes the possible common-zero
obstruction for compact radial tests. -/
noncomputable section
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

lemma cubicThetaComplexHeightIntegral_real_zero_iff (s : ℂ) (A : ℝ)
    {v : ℝ} (hv : 0<v) :
    cubicThetaComplexHeightIntegral s A (v:ℂ)=0 ↔
      (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s A t)=0 := by
  have he := cubicThetaHeat_height_dilation hv A s
  rw [← cubicThetaComplexHeightIntegral_real] at he
  have hvc : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  constructor
  · intro hz
    rw [hz,mul_zero] at he
    exact (mul_eq_zero.mp he).resolve_left (Complex.cpow_ne_zero_iff.mpr (Or.inl hvc))
  · intro hz
    rw [hz,mul_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hvc

theorem cubicThetaHighHeat_nonzero {s : ℂ} (hs : 1 < s.re) {A : ℝ} (hA : 0<A) :
    ∃ v : ℝ, 2<v ∧ (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s A t)≠0 := by
  by_contra hn
  push Not at hn
  have hzero (v : ℝ) (hv : 2<v) : cubicThetaComplexHeightIntegral s A (v:ℂ)=0 :=
    (cubicThetaComplexHeightIntegral_real_zero_iff s A (by linarith)).mpr (hn v hv)
  have hmap : Tendsto (fun v : ℝ => (v:ℂ)) (𝓝[≠] (3:ℝ)) (𝓝[≠] (3:ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with v hv
      change (v:ℂ)≠3
      exact_mod_cast hv
  have hnear : ∀ᶠ v : ℝ in 𝓝[≠] 3, cubicThetaComplexHeightIntegral s A (v:ℂ)=0 := by
    have he : ∀ᶠ v : ℝ in 𝓝 3, 2<v := (isOpen_Ioi.mem_nhds (by norm_num : (3:ℝ)∈Ioi 2))
    filter_upwards [nhdsWithin_le_nhds he] with v hv
    exact hzero v hv
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] 3, cubicThetaComplexHeightIntegral s A z=0 := by
    by_contra hneg
    have hf := hmap.eventually (not_frequently.mp hneg)
    have hc := hf.and hnear
    exact (hc.exists).elim (fun _ h => h.1 h.2)
  have ha : AnalyticOnNhd ℂ (cubicThetaComplexHeightIntegral s A) {z : ℂ | 0<z.re} :=
    fun z hz => cubicThetaComplexHeightIntegral_analytic s hA hz
  have hglobal := ha.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_halfSpace_re_gt 0).isPreconnected
      (z₀:=(3:ℂ)) (by norm_num) hfreq
  have hnonzero := cubicThetaDualHeat_eventually_nonzero hs hA.le
  have hc : ∀ᶠ v : ℝ in 𝓝[>] 0, False := by
    filter_upwards [hnonzero,self_mem_nhdsWithin] with v hv hpos
    exact hv ((cubicThetaComplexHeightIntegral_real_zero_iff s A hpos).mp (hglobal (by simpa using hpos)))
  exact (hc.exists).elim (fun _ h => h)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaIncomingWindow
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The difference of incoming cutoffs at heights one and two is a
literal compact smooth automorphic section. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff MatrixGroups
namespace CubicFirstMoment

def cubicThetaIncomingWindowCutoff (v : ℝ) : ℂ :=
  cubicThetaCuspCutoff v-cubicThetaCuspCutoff (v/2)

lemma cubicThetaIncomingWindowCutoff_smooth :
    ContDiff ℝ ∞ cubicThetaIncomingWindowCutoff :=
  cubicThetaCuspCutoff_smooth.sub
    (cubicThetaCuspCutoff_smooth.comp (contDiff_id.div_const 2))

lemma cubicThetaIncomingWindowCutoff_low {v : ℝ} (hv : v≤1) :
    cubicThetaIncomingWindowCutoff v=0 := by
  rw [cubicThetaIncomingWindowCutoff,cubicThetaCuspCutoff_zero hv,
    cubicThetaCuspCutoff_zero (by linarith : v/2≤1),sub_self]

lemma cubicThetaIncomingWindowCutoff_high {v : ℝ} (hv : 4≤v) :
    cubicThetaIncomingWindowCutoff v=0 := by
  rw [cubicThetaIncomingWindowCutoff,cubicThetaCuspCutoff_one (by linarith : 2≤v),
    cubicThetaCuspCutoff_one (by linarith : 2≤v/2),sub_self]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaWindowProfile
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact radial defect of the compact incoming window. Its difference
from the original forcing is a continuous weight supported in [2,4]. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff CompactlySupported
namespace CubicFirstMoment

def cubicThetaWindowHeight (s : ℂ) (v : ℝ) : ℂ :=
  cubicThetaIncomingWindowCutoff v*(v:ℂ)^s

lemma cubicThetaWindowHeight_smooth (s : ℂ) : ContDiff ℝ ∞ (cubicThetaWindowHeight s) := by
  apply contDiff_iff_contDiffAt.mpr
  intro v
  by_cases hv : 0<v
  · exact cubicThetaIncomingWindowCutoff_smooth.contDiffAt.mul
      (cubicThetaHeightPower_analytic s hv).contDiffAt
  · have he : cubicThetaWindowHeight s =ᶠ[𝓝 v] (fun _ => 0) := by
      filter_upwards [eventually_lt_nhds (show v<1 by linarith)] with t ht
      simp only [cubicThetaWindowHeight,cubicThetaIncomingWindowCutoff_low ht.le,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

lemma cubicThetaWindowHeight_zero {v : ℝ} (s : ℂ) (hv : v≤1 ∨ 4≤v) :
    cubicThetaWindowHeight s v=0 := by
  rcases hv with hv | hv
  · simp only [cubicThetaWindowHeight,cubicThetaIncomingWindowCutoff_low hv,zero_mul]
  · simp only [cubicThetaWindowHeight,cubicThetaIncomingWindowCutoff_high hv,zero_mul]

def cubicThetaWindowDefect (s : ℂ) (v : ℝ) : ℂ :=
  (v:ℂ)^2*deriv (deriv (cubicThetaWindowHeight s)) v-
    (v:ℂ)*deriv (cubicThetaWindowHeight s) v-s*(s-2)*cubicThetaWindowHeight s v

lemma cubicThetaWindowDefect_continuous (s : ℂ) : Continuous (cubicThetaWindowDefect s) := by
  have hd := (contDiff_infty_iff_deriv.mp (cubicThetaWindowHeight_smooth s)).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  exact ((Complex.continuous_ofReal.pow 2).mul hdd.continuous).sub
    (Complex.continuous_ofReal.mul hd.continuous) |>.sub
      (continuous_const.mul (cubicThetaWindowHeight_smooth s).continuous)

lemma cubicThetaWindowDefect_zero_open (s : ℂ) {v : ℝ} (hv : v<1 ∨ 4<v) :
    cubicThetaWindowDefect s v=0 := by
  have he : cubicThetaWindowHeight s =ᶠ[𝓝 v] (fun _ => 0) := by
    rcases hv with hv | hv
    · filter_upwards [eventually_lt_nhds hv] with t ht
      exact cubicThetaWindowHeight_zero s (Or.inl ht.le)
    · filter_upwards [eventually_gt_nhds hv] with t ht
      exact cubicThetaWindowHeight_zero s (Or.inr ht.le)
  have h₀ := he.eq_of_nhds
  have h₁ := he.deriv_eq
  have h₂ := he.deriv.deriv_eq
  simp only [deriv_const',deriv_const] at h₁ h₂
  simp only [cubicThetaWindowDefect,h₀,h₁,h₂,mul_zero,sub_zero]

lemma cubicThetaWindowDefect_low (s : ℂ) {v : ℝ} (hv : v<2) :
    cubicThetaWindowDefect s v=cubicThetaIncomingForcing s v := by
  by_cases hlow : v<1
  · rw [cubicThetaWindowDefect_zero_open s (Or.inl hlow),
      cubicThetaIncomingForcing_zero s (Or.inl hlow)]
  have he : cubicThetaWindowHeight s =ᶠ[𝓝 v]
      (fun t => cubicThetaCuspCutoff t*(t:ℂ)^s) := by
    filter_upwards [eventually_lt_nhds hv] with t ht
    simp only [cubicThetaWindowHeight,cubicThetaIncomingWindowCutoff,
      cubicThetaCuspCutoff_zero (by linarith : t/2≤1),sub_zero]
  have h₀ := he.eq_of_nhds
  have h₁ := he.deriv_eq
  have h₂ := he.deriv.deriv_eq
  have h := cubicThetaCutoffIncoming_equation s 0 0 (show 0<v by linarith)
  simp only [cubicThetaHyperbolicOperator,deriv_const',deriv_const,zero_add] at h
  unfold cubicThetaWindowDefect
  rw [h₀,h₁,h₂,h]
  ring

def cubicThetaHighWindowForcing (s : ℂ) (v : ℝ) : ℂ :=
  cubicThetaIncomingForcing s v-cubicThetaWindowDefect s v

lemma cubicThetaHighWindowForcing_continuous (s : ℂ) :
    Continuous (cubicThetaHighWindowForcing s) :=
  (cubicThetaIncomingForcing_continuous s).sub (cubicThetaWindowDefect_continuous s)

lemma cubicThetaHighWindowForcing_low (s : ℂ) {v : ℝ} (hv : v≤2) :
    cubicThetaHighWindowForcing s v=0 := by
  have hz : EqOn (cubicThetaHighWindowForcing s) (fun _ => 0) (Iio (2:ℝ)) := by
    intro t ht
    rw [cubicThetaHighWindowForcing,cubicThetaWindowDefect_low s ht,sub_self]
  exact hz.closure (cubicThetaHighWindowForcing_continuous s) continuous_const
    (by simpa only [closure_Iio,mem_Iic] using hv)

lemma cubicThetaHighWindowForcing_high (s : ℂ) {v : ℝ} (hv : 4≤v) :
    cubicThetaHighWindowForcing s v=0 := by
  have hz : EqOn (cubicThetaHighWindowForcing s) (fun _ => 0) (Ioi (4:ℝ)) := by
    intro t ht
    change 4<t at ht
    rw [cubicThetaHighWindowForcing,cubicThetaWindowDefect_zero_open s (Or.inr ht),
      cubicThetaIncomingForcing_zero s (Or.inr (by linarith : 2<t)),sub_zero]
  exact hz.closure (cubicThetaHighWindowForcing_continuous s) continuous_const
    (by simpa only [closure_Ioi,mem_Ici] using hv)

def cubicThetaHighWindowWeight (s : ℂ) : C_c(ℝ,ℂ) where
  toFun := cubicThetaHighWindowForcing s
  continuous_toFun := cubicThetaHighWindowForcing_continuous s
  hasCompactSupport' := by
    apply HasCompactSupport.of_support_subset_isCompact (K:=Icc (2:ℝ) 4) isCompact_Icc
    intro v hv
    constructor
    · by_contra hn
      exact hv (cubicThetaHighWindowForcing_low s (le_of_not_ge hn))
    · by_contra hn
      exact hv (cubicThetaHighWindowForcing_high s (le_of_not_ge hn))

lemma cubicThetaWindowHeight_equation (s : ℂ) (x y v : ℝ) :
    cubicThetaHyperbolicOperator (fun _ _ t => cubicThetaWindowHeight s t) x y v=
      s*(s-2)*cubicThetaWindowHeight s v+cubicThetaIncomingForcing s v-
        cubicThetaHighWindowForcing s v := by
  simp only [cubicThetaHyperbolicOperator,deriv_const',deriv_const,zero_add,
    cubicThetaHighWindowForcing,cubicThetaWindowDefect]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHighWindowSmooth
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact high-cusp forcing is a genuine smooth test section. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaIncomingForcing_smooth (s : ℂ) :
    ContDiff ℝ ∞ (cubicThetaIncomingForcing s) := by
  apply contDiff_iff_contDiffAt.mpr
  intro v
  by_cases hv : 0<v
  · exact cubicThetaIncomingForcing_contDiffAt s hv
  · have he : cubicThetaIncomingForcing s =ᶠ[𝓝 v] (fun _ => 0) := by
      filter_upwards [eventually_lt_nhds (show v<1 by linarith)] with t ht
      exact cubicThetaIncomingForcing_zero s (Or.inl ht)
    exact contDiffAt_const.congr_of_eventuallyEq he

lemma cubicThetaWindowDefect_smooth (s : ℂ) :
    ContDiff ℝ ∞ (cubicThetaWindowDefect s) := by
  have hd := (contDiff_infty_iff_deriv.mp (cubicThetaWindowHeight_smooth s)).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  exact ((Complex.ofRealCLM.contDiff.pow 2).mul hdd).sub
    (Complex.ofRealCLM.contDiff.mul hd) |>.sub
      (contDiff_const.mul (cubicThetaWindowHeight_smooth s))

lemma cubicThetaHighWindowForcing_smooth (s : ℂ) :
    ContDiff ℝ ∞ (cubicThetaHighWindowForcing s) :=
  (cubicThetaIncomingForcing_smooth s).sub (cubicThetaWindowDefect_smooth s)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialEulerScaling
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial Euler operator commutes with positive changes of height. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaRadialEuler_scale {f : ℝ → ℂ} {r v : ℝ} (hr : 0 < r)
    (hf : ContDiffAt ℝ 2 f (v/r)) :
    cubicThetaRadialEuler (fun t => f (t/r)) v=cubicThetaRadialEuler f (v/r) := by
  have hg : ContDiffAt ℝ 2 (fun t : ℝ => t/r) v :=
    (contDiff_id.div_const r).contDiffAt
  have hd := (hf.differentiableAt (by norm_num)).hasDerivAt.scomp v
    ((hasDerivAt_id v).div_const r)
  have hdd := cubicThetaSecondChain (h:=fun t : ℝ => t/r) (x:=v) hf hg
  have hdlin : deriv (fun t : ℝ => t/r)=(fun _ => 1/r) := by
    funext t
    simp only [deriv_div_const,deriv_id'']
  simp only [Function.comp_def,hdlin,deriv_const,zero_smul,add_zero,
    Complex.real_smul,Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_one] at hdd
  have hd' : deriv (fun t => f (t/r)) v=(1/r:ℝ) • deriv f (v/r) := hd.deriv
  unfold cubicThetaRadialEuler
  rw [hd',hdd]
  simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_one]
  have hr0 : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialMellinIntegrability
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute convergence for the radial-test Mellin interchange. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaRadialMellin_integrable (W : C_c(ℝ,ℂ)) {A : ℝ} (hA : 0<A)
    (s : ℂ) :
    Integrable (cubicThetaRadialMellinIntegrand W A s)
      ((volume.restrict (Ioi (2:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  have hh := (cubicThetaDoubleHeat_mellinConvergent (by norm_num : (0:ℝ)<1) hA (s-1)).norm
  change IntegrableOn (fun u : ℝ => ‖(u:ℂ)^(s-1-1)*cubicThetaDoubleHeat 1 A u‖) (Ioi 0) at hh
  rw [show s-1-1=s-2 by ring] at hh
  have hm := (cubicThetaRadialWeight_integrable W).mul_prod hh
  rw [Measure.prod_restrict] at hm ⊢
  apply hm.mono' (by
    apply Measurable.aestronglyMeasurable
    unfold cubicThetaRadialMellinIntegrand cubicThetaLinearHeat
    fun_prop)
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
  have hb := mul_le_mul_of_nonneg_left
    (cubicThetaLinearHeat_average_bound W hA hp.2 hp.1) (_root_.norm_nonneg ((p.2:ℂ)^(s-2)))
  simpa only [cubicThetaRadialMellinIntegrand,norm_mul,mul_comm,mul_left_comm,mul_assoc] using hb

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialTent
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete nonnegative radial test supported in [2,4]. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaRadialTent_nonneg (v : ℝ) : 0 ≤ cubicThetaRadialTent v :=
  le_max_left _ _

lemma cubicThetaRadialTestWeight_apply (v : ℝ) :
    cubicThetaRadialTestWeight v=(cubicThetaRadialTent v:ℂ) := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialNonzero
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed radial test is nontrivial: its value at s=2 is strictly
positive. This supplies a genuine analytic denominator for continuation. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaRadialTest_kernel_real (A u v : ℝ) :
    star (cubicThetaRadialTestWeight v)/(v:ℂ)^2*cubicThetaLinearHeat v A u=
      ((cubicThetaRadialTent v/v^2*Real.exp (-v*u-A*v/u):ℝ):ℂ) := by
  rw [cubicThetaRadialTestWeight_apply,cubicThetaLinearHeat]
  push_cast
  simp

lemma cubicThetaAveragedHeat_test_re_pos {A u : ℝ} (hA : 0<A) (hu : 0<u) :
    0<(cubicThetaAveragedHeat cubicThetaRadialTestWeight A u).re := by
  let f := fun v : ℝ => cubicThetaRadialTent v/v^2*Real.exp (-v*u-A*v/u)
  have hi : IntegrableOn f (Ioi (2:ℝ)) := by
    have hr := (cubicThetaAveragedHeat_integrable cubicThetaRadialTestWeight hA hu).re
    change IntegrableOn (fun v : ℝ =>
      (star (cubicThetaRadialTestWeight v)/(v:ℂ)^2*cubicThetaLinearHeat v A u).re) (Ioi 2) at hr
    simpa only [cubicThetaRadialTest_kernel_real,Complex.ofReal_re] using hr
  have hc : ContinuousOn f (Ioi (2:ℝ)) := by
    apply ContinuousOn.mul
    · exact cubicThetaRadialTent_continuous.continuousOn.div (continuousOn_id.pow 2)
        (fun v hv => pow_ne_zero _ (ne_of_gt (lt_trans (by norm_num) hv)))
    · exact (Real.continuous_exp.comp (by fun_prop)).continuousOn
  have hp : 0<∫ v in Ioi (2:ℝ), f v :=
    cubicThetaPositive_setIntegral hc hi
      (fun v _ => mul_nonneg (div_nonneg (cubicThetaRadialTent_nonneg v) (sq_nonneg v))
        (Real.exp_nonneg _)) (x:=3) (by norm_num)
      (by dsimp [f,cubicThetaRadialTent]; positivity)
  have hr := integral_re (cubicThetaAveragedHeat_integrable cubicThetaRadialTestWeight hA hu)
  change (∫ v in Ioi (2:ℝ),
    (star (cubicThetaRadialTestWeight v)/(v:ℂ)^2*cubicThetaLinearHeat v A u).re)=
      (cubicThetaAveragedHeat cubicThetaRadialTestWeight A u).re at hr
  rw [← hr]
  simpa only [cubicThetaRadialTest_kernel_real,Complex.ofReal_re] using hp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaZeroWindow
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact radial windows supported above height two retain the exact
constant-mode continuation. They will test the high annular forcing. -/
noncomputable section
open Set Filter MeasureTheory Topology
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaZeroRadialWindow_entire (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ), W v=0) :
    Differentiable ℂ (cubicThetaZeroRadialTest W) := by
  have hpos : tsupport (star W)⊆Ioi (0:ℝ) := by
    have hs : tsupport (star W)⊆Ici (2:ℝ) := by
      apply closure_minimal ?_ isClosed_Ici
      intro v hv
      by_contra hn
      apply hv
      change star (W v)=0
      rw [hW v (le_of_not_ge hn),star_zero]
    intro v hv
    exact lt_of_lt_of_le (show (0:ℝ)<2 by norm_num) (hs hv)
  have hm := smooth_mellin_entire (star W) (star W).hasCompactSupport
    hpos (star W).continuous
  have he : cubicThetaZeroRadialTest W=(fun s : ℂ => mellin (star W) (-s)) :=
    funext (cubicThetaZeroRadialWindow_mellin W hW)
  rw [he]
  exact hm.comp differentiable_id.neg

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLongWindow
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact incoming window between heights one and H. Its defect is
exactly the difference of the original and dilated annular forcing. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff CompactlySupported
namespace CubicFirstMoment

def cubicThetaCutoffHeight (s : ℂ) (v : ℝ) : ℂ :=
  cubicThetaCuspCutoff v*(v:ℂ)^s

lemma cubicThetaCutoffHeight_smooth (s : ℂ) :
    ContDiff ℝ ∞ (cubicThetaCutoffHeight s) := by
  apply contDiff_iff_contDiffAt.mpr
  intro v
  by_cases hv : 0<v
  · exact cubicThetaCuspCutoff_smooth.contDiffAt.mul
      (cubicThetaHeightPower_analytic s hv).contDiffAt
  · have he : cubicThetaCutoffHeight s =ᶠ[𝓝 v] (fun _ => 0) := by
      filter_upwards [eventually_lt_nhds (show v<1 by linarith)] with t ht
      simp only [cubicThetaCutoffHeight,cubicThetaCuspCutoff_zero ht.le,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

lemma cubicThetaCutoffHeight_equation (s : ℂ) {v : ℝ} (hv : 0<v) :
    cubicThetaRadialEuler (cubicThetaCutoffHeight s) v=
      s*(s-2)*cubicThetaCutoffHeight s v+cubicThetaIncomingForcing s v := by
  have h := cubicThetaCutoffIncoming_equation s 0 0 hv
  change (v:ℂ)^2*deriv (deriv (fun t => cubicThetaCuspCutoff t*(t:ℂ)^s)) v-
    (v:ℂ)*deriv (fun t => cubicThetaCuspCutoff t*(t:ℂ)^s) v=_
  dsimp only [cubicThetaCutoffHeight]
  simpa only [cubicThetaHyperbolicOperator,deriv_const',deriv_const,zero_add] using h

def cubicThetaLongWindowHeight (H : ℝ) (s : ℂ) (v : ℝ) : ℂ :=
  cubicThetaCutoffHeight s v-(H:ℂ)^s*cubicThetaCutoffHeight s (v/H)

lemma cubicThetaLongWindowHeight_smooth (H : ℝ) (s : ℂ) :
    ContDiff ℝ ∞ (cubicThetaLongWindowHeight H s) :=
  (cubicThetaCutoffHeight_smooth s).sub (contDiff_const.mul
    ((cubicThetaCutoffHeight_smooth s).comp (contDiff_id.div_const H)))

lemma cubicThetaLongWindowHeight_low {H : ℝ} (hH : 1≤H) (s : ℂ)
    {v : ℝ} (hv : v≤1) : cubicThetaLongWindowHeight H s v=0 := by
  have hvH : v/H≤1 := (div_le_iff₀ (by linarith : 0<H)).mpr (by linarith)
  simp only [cubicThetaLongWindowHeight,cubicThetaCutoffHeight,
    cubicThetaCuspCutoff_zero hv,cubicThetaCuspCutoff_zero hvH,zero_mul,mul_zero,sub_self]

lemma cubicThetaLongWindowHeight_high {H : ℝ} (hH : 1≤H) (s : ℂ)
    {v : ℝ} (hv : 2*H≤v) : cubicThetaLongWindowHeight H s v=0 := by
  have hH0 : 0<H := by linarith
  have hv2 : 2≤v := by linarith
  have hvH : 2≤v/H := (le_div_iff₀ hH0).mpr hv
  have he : (H:ℂ)^s*((v/H:ℝ):ℂ)^s=(v:ℂ)^s := by
    rw [←Complex.mul_cpow_ofReal_nonneg hH0.le (div_nonneg (by linarith) hH0.le),
      ←Complex.ofReal_mul]
    congr 1
    field_simp
  simp only [cubicThetaLongWindowHeight,cubicThetaCutoffHeight,
    cubicThetaCuspCutoff_one hv2,cubicThetaCuspCutoff_one hvH,one_mul,he,sub_self]

def cubicThetaLongWindowWeight (H : ℝ) (hH : 1≤H) (s : ℂ) : C_c(ℝ,ℂ) where
  toFun := cubicThetaLongWindowHeight H s
  continuous_toFun := (cubicThetaLongWindowHeight_smooth H s).continuous
  hasCompactSupport' := by
    apply HasCompactSupport.of_support_subset_isCompact (K:=Icc (1:ℝ) (2*H)) isCompact_Icc
    intro v hv
    constructor
    · by_contra hn
      exact hv (cubicThetaLongWindowHeight_low hH s (le_of_not_ge hn))
    · by_contra hn
      exact hv (cubicThetaLongWindowHeight_high hH s (le_of_not_ge hn))

lemma cubicThetaLongWindowHeight_equation {H : ℝ} (hH : 1≤H) (s : ℂ) {v : ℝ} (hv : 0<v) :
    cubicThetaRadialEuler (cubicThetaLongWindowHeight H s) v=
      s*(s-2)*cubicThetaLongWindowHeight H s v+cubicThetaIncomingForcing s v-
        cubicThetaLongForcingWeight H (by linarith) s v := by
  have hH0 : 0<H := by linarith
  change cubicThetaRadialEuler
    (fun t => cubicThetaCutoffHeight s t-(H:ℂ)^s*cubicThetaCutoffHeight s (t/H)) v=_
  have hd : ContDiff ℝ ∞ (fun t => (H:ℂ)^s*cubicThetaCutoffHeight s (t/H)) :=
    contDiff_const.mul ((cubicThetaCutoffHeight_smooth s).comp (contDiff_id.div_const H))
  rw [cubicThetaRadialEuler_sub (cubicThetaCutoffHeight_smooth s) hd,
    cubicThetaRadialEuler_const_mul,cubicThetaRadialEuler_scale hH0
      ((cubicThetaCutoffHeight_smooth s).contDiffAt.of_le (by norm_num)),
    cubicThetaCutoffHeight_equation s hv,cubicThetaCutoffHeight_equation s (div_pos hv hH0),
    cubicThetaLongForcingWeight_apply]
  dsimp only [cubicThetaLongWindowHeight]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLongWindowKernel
attribute [-instance] _root_.instMeasurableSpace
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

lemma cubicThetaIncomingForcingWeight_low (s : ℂ) (v : ℝ) (hv : v≤1) :
    cubicThetaIncomingForcingWeight s v=0 :=
  cubicThetaIncomingForcing_zero_closed s (Or.inl hv)

lemma cubicThetaLongForcingWeight_low_one {H : ℝ} (hH : 2≤H) (s : ℂ) (v : ℝ) (hv : v≤1) :
    cubicThetaLongForcingWeight H (by linarith) s v=0 :=
  cubicThetaLongForcingWeight_low (by linarith) s (by linarith)

lemma cubicThetaLongForcingWeight_low_two {H : ℝ} (hH : 2≤H) (s : ℂ) (v : ℝ) (hv : v≤2) :
    cubicThetaLongForcingWeight H (by linarith) s v=0 :=
  cubicThetaLongForcingWeight_low (by linarith) s (by linarith)

def cubicThetaLongWindowDefect (H : ℝ) (hH : 2≤H) (s : ℂ) : C_c(ℝ,ℂ) :=
  cubicThetaLongForcingWeight H (by linarith) s-cubicThetaIncomingForcingWeight s

lemma cubicThetaLongWindowDefect_low (H : ℝ) (hH : 2≤H) (s : ℂ) (v : ℝ) (hv : v≤1) :
    cubicThetaLongWindowDefect H hH s v=0 := by
  change cubicThetaLongForcingWeight H _ s v-cubicThetaIncomingForcingWeight s v=0
  rw [cubicThetaLongForcingWeight_low_one hH s v hv,cubicThetaIncomingForcingWeight_low s v hv,sub_self]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMellinWeights
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute lattice and kernel masses for exchanging the theta sum with
its Mellin integral on the initial right half-plane. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicWhittakerNormMass (σ : ℝ) : ℝ :=
  ∫ v in Ioi (0:ℝ), v^(σ-1)*‖cubicThetaWhittaker v‖

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPointC1
attribute [-instance] _root_.OAI.CubicFirstMoment.LocalSobolev.tangentBorelVolume_finiteOnCompacts _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! C1 functions on the hyperbolic upper half-space, used only to
transport the actual gradients through the finite Hecke correspondence. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPointFunction (F : C(CubicThetaPoint,ℂ)) (y : ℂ × ℝ) : ℂ :=
  F (cubicThetaPointInclusion.symm y)

def cubicThetaPointC1 : Submodule ℂ C(CubicThetaPoint,ℂ) where
  carrier := {F | ContDiffOn ℝ 1 (cubicThetaPointFunction F) {y : ℂ × ℝ | 0<y.2}}
  zero_mem' := contDiffOn_const
  add_mem' := fun hF hG => hF.add hG
  smul_mem' := fun c _ hF => hF.const_smul c

lemma cubicThetaPointC1_differentiable (F : cubicThetaPointC1)
    {y : ℂ × ℝ} (hy : 0<y.2) : DifferentiableAt ℝ (cubicThetaPointFunction F.val) y :=
  (F.property.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hy)).differentiableAt
    (by norm_num)

def cubicThetaPointC1Gradient (x : CubicThetaPoint) : cubicThetaPointC1 →ₗ[ℂ] CubicThetaGradient where
  toFun F := (x.val.2:ℂ) • cubicThetaTangentValues (fderiv ℝ (cubicThetaPointFunction F.val) x.val)
  map_add' F G := by
    change (x.val.2:ℂ) • cubicThetaTangentValues
      (fderiv ℝ (cubicThetaPointFunction F.val+cubicThetaPointFunction G.val) x.val)=_
    rw [fderiv_add (cubicThetaPointC1_differentiable F x.property)
      (cubicThetaPointC1_differentiable G x.property),map_add,smul_add]
  map_smul' c F := by
    change (x.val.2:ℂ) • cubicThetaTangentValues
      (fderiv ℝ (c • cubicThetaPointFunction F.val) x.val)=_
    rw [fderiv_const_smul (cubicThetaPointC1_differentiable F x.property),map_smul]
    exact smul_comm _ _ _

lemma cubicThetaPointC1Gradient_norm_sq (F : cubicThetaPointC1) (x : CubicThetaPoint) :
    ‖cubicThetaPointC1Gradient x F‖^2=
      x.val.2^2*cubicThetaFunctionEnergy (cubicThetaPointFunction F.val) x.val := by
  change ‖(x.val.2:ℂ) • cubicThetaTangentValues
    (fderiv ℝ (cubicThetaPointFunction F.val) x.val)‖^2=_
  rw [norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  congr 1
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPointC1Section
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The auxiliary C1 coordinates retain the literal automorphic section
and its previously constructed gradient. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPointC1Gradient_continuous (F : cubicThetaPointC1) :
    Continuous (fun x => cubicThetaPointC1Gradient x F) := by
  have hd : Continuous (fun x : CubicThetaPoint =>
      fderiv ℝ (cubicThetaPointFunction F.val) x.val) :=
    (F.property.continuousOn_fderiv_of_isOpen (isOpen_lt continuous_const continuous_snd)
      (by norm_num)).comp_continuous continuous_subtype_val (fun x => x.property)
  change Continuous (fun x : CubicThetaPoint => (x.val.2:ℂ) •
    cubicThetaTangentValues (fderiv ℝ (cubicThetaPointFunction F.val) x.val))
  apply Continuous.smul (Complex.continuous_ofReal.comp (continuous_snd.comp continuous_subtype_val))
  apply (PiLp.continuous_toLp _ _).comp
  apply continuous_pi
  intro i
  exact hd.clm_apply continuous_const

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeComplexIntegration
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
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

lemma cubicThetaSquareIntegrablePair {S : Set CubicThetaPoint}
    (F G : CubicThetaPoint → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hFs : IntegrableOn (fun x => ‖F x‖^2) S cubicThetaPointMeasure)
    (hGs : IntegrableOn (fun x => ‖G x‖^2) S cubicThetaPointMeasure) :
    IntegrableOn (fun x => star (F x)*G x) S cubicThetaPointMeasure := by
  apply ((hFs.add hGs).div_const 2).mono'
    ((hF.star.mul hG).aestronglyMeasurable)
  filter_upwards with x
  change ‖star (F x)*G x‖ ≤ (‖F x‖^2+‖G x‖^2)/2
  rw [norm_mul,norm_star]
  nlinarith [sq_nonneg (‖F x‖-‖G x‖)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPointC1Trace
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
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

lemma cubicThetaPointC1Pair_integrable (F G : cubicThetaPointC1) {S : Set CubicThetaPoint}
    (hF : IntegrableOn (fun x => ‖cubicThetaPointC1Gradient x F‖^2) S cubicThetaPointMeasure)
    (hG : IntegrableOn (fun x => ‖cubicThetaPointC1Gradient x G‖^2) S cubicThetaPointMeasure) :
    IntegrableOn (fun x => inner ℂ (cubicThetaPointC1Gradient x G)
      (cubicThetaPointC1Gradient x F)) S cubicThetaPointMeasure := by
  apply ((hG.add hF).div_const 2).mono'
    (((cubicThetaPointC1Gradient_continuous G).inner
      (cubicThetaPointC1Gradient_continuous F)).aestronglyMeasurable)
  filter_upwards with x
  change ‖inner ℂ (cubicThetaPointC1Gradient x G) (cubicThetaPointC1Gradient x F)‖≤
    (‖cubicThetaPointC1Gradient x G‖^2+‖cubicThetaPointC1Gradient x F‖^2)/2
  apply (norm_inner_le_norm _ _).trans
  have hs := sq_nonneg (‖cubicThetaPointC1Gradient x G‖-‖cubicThetaPointC1Gradient x F‖)
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPointC1TraceIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The gradient trace adjoint on the actual finite cover, obtained
from the pointwise isometry identity and justified finite integration. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPointC1Pair_flip (F G : cubicThetaPointC1) (S : Set CubicThetaPoint) :
    star (∫ x in S,inner ℂ (cubicThetaPointC1Gradient x G)
      (cubicThetaPointC1Gradient x F) ∂cubicThetaPointMeasure)=
    ∫ x in S,inner ℂ (cubicThetaPointC1Gradient x F)
      (cubicThetaPointC1Gradient x G) ∂cubicThetaPointMeasure := by
  have he := (integral_conj (f:=fun x => inner ℂ (cubicThetaPointC1Gradient x G)
    (cubicThetaPointC1Gradient x F)) (μ:=cubicThetaPointMeasure.restrict S)).symm
  change star (∫ x in S,inner ℂ (cubicThetaPointC1Gradient x G)
    (cubicThetaPointC1Gradient x F) ∂cubicThetaPointMeasure)=
    ∫ x in S,(starRingEnd ℂ) (inner ℂ (cubicThetaPointC1Gradient x G)
      (cubicThetaPointC1Gradient x F)) ∂cubicThetaPointMeasure at he
  simpa only [inner_conj_symm] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeHeckePairing
attribute [-instance] _root_.instMeasurableSpace
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

lemma cubicThetaComplexPair_flip (f g : CubicThetaPoint → ℂ) (S : Set CubicThetaPoint) :
    star (∫ x in S,star (f x)*g x ∂cubicThetaPointMeasure)=
      ∫ x in S,star (g x)*f x ∂cubicThetaPointMeasure := by
  have he := (integral_conj (f:=fun x => star (f x)*g x)
    (μ:=cubicThetaPointMeasure.restrict S)).symm
  change star (∫ x in S,star (f x)*g x ∂cubicThetaPointMeasure)=
    ∫ x in S,star (star (f x)*g x) ∂cubicThetaPointMeasure at he
  rw [he]
  apply integral_congr_ae
  filter_upwards with x
  rw [star_mul,star_star,mul_comm]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveAveragedHeat
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial Mellin kernel at an arbitrary positive cutoff. Its
endpoint decay follows from the same double heat kernel, with rescaled parameters. -/
noncomputable section
open Set MeasureTheory Filter Asymptotics Topology
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPositiveLinearHeat_bound (W : C_c(ℝ,ℂ)) {ε A u v : ℝ}
    (hε : 0<ε) (hA : 0<A) (hu : 0<u) (hv : ε<v) :
    ‖star (W v)/(v:ℂ)^2*cubicThetaLinearHeat v A u‖≤
      (‖W v‖/v^2)*‖cubicThetaDoubleHeat (Real.sqrt ε) (A*ε) u‖ := by
  have he : -v*u-A*v/u≤-(Real.sqrt ε)^2*u-(A*ε)/u := by
    rw [Real.sq_sqrt hε.le]
    have h₁ := mul_le_mul_of_nonneg_right hv.le hu.le
    have h₂ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv.le hA.le) hu.le
    linarith
  simp only [norm_mul,norm_div,norm_star,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    cubicThetaLinearHeat,cubicThetaDoubleHeat,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
    (div_nonneg (_root_.norm_nonneg _) (sq_nonneg _))

lemma cubicThetaPositiveDoubleHeat_norm_le_one {ε A u : ℝ}
    (hε : 0<ε) (hA : 0<A) (hu : 0<u) :
    ‖cubicThetaDoubleHeat (Real.sqrt ε) (A*ε) u‖≤1 := by
  rw [cubicThetaDoubleHeat,Complex.norm_real,Real.norm_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_le_one_iff.mpr
  have h₁ := mul_pos hε hu
  have h₂ := div_pos (mul_pos hA hε) hu
  rw [Real.sq_sqrt hε.le]
  linarith

lemma cubicThetaPositiveAveragedHeat_integrable (W : C_c(ℝ,ℂ)) {ε A u : ℝ}
    (hε : 0<ε) (hA : 0<A) (hu : 0<u) :
    IntegrableOn (fun v : ℝ => star (W v)/(v:ℂ)^2*cubicThetaLinearHeat v A u)
      (Ioi ε) := by
  apply (cubicThetaPositiveRadialWeight_integrable W hε).mono' (by
    apply Measurable.aestronglyMeasurable
    unfold cubicThetaLinearHeat
    fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact (cubicThetaPositiveLinearHeat_bound W hε hA hu hv).trans
    ((mul_le_mul_of_nonneg_left (cubicThetaPositiveDoubleHeat_norm_le_one hε hA hu)
      (div_nonneg (_root_.norm_nonneg _) (sq_nonneg _))).trans_eq (mul_one _))

lemma cubicThetaPositiveAveragedHeat_bound (W : C_c(ℝ,ℂ)) {ε A u : ℝ}
    (hε : 0<ε) (hA : 0<A) (hu : 0<u) :
    ‖cubicThetaPositiveAveragedHeat W ε A u‖≤
      cubicThetaPositiveRadialWeightMass W ε*‖cubicThetaDoubleHeat (Real.sqrt ε) (A*ε) u‖ := by
  apply (norm_integral_le_integral_norm _).trans
  rw [cubicThetaPositiveRadialWeightMass,←integral_mul_const]
  apply integral_mono_ae (cubicThetaPositiveAveragedHeat_integrable W hε hA hu).norm
    ((cubicThetaPositiveRadialWeight_integrable W hε).mul_const _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact cubicThetaPositiveLinearHeat_bound W hε hA hu hv

lemma cubicThetaPositiveAveragedHeat_continuous (W : C_c(ℝ,ℂ)) {ε A : ℝ}
    (hε : 0<ε) (hA : 0<A) :
    ContinuousOn (cubicThetaPositiveAveragedHeat W ε A) (Ioi (0:ℝ)) := by
  apply continuousOn_of_dominated (bound:=fun v : ℝ => ‖W v‖/v^2)
  · intro u hu
    apply Measurable.aestronglyMeasurable
    unfold cubicThetaLinearHeat
    fun_prop
  · intro u hu
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact (cubicThetaPositiveLinearHeat_bound W hε hA hu hv).trans
      ((mul_le_mul_of_nonneg_left (cubicThetaPositiveDoubleHeat_norm_le_one hε hA hu)
        (div_nonneg (_root_.norm_nonneg _) (sq_nonneg _))).trans_eq (mul_one _))
  · exact cubicThetaPositiveRadialWeight_integrable W hε
  · filter_upwards with v
    have hc : ContinuousOn (fun u : ℝ => -v*u-A*v/u) (Ioi 0) :=
      (continuousOn_const.mul continuousOn_id).sub
        (continuousOn_const.div continuousOn_id (fun u hu => ne_of_gt hu))
    exact continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn (Real.continuous_exp.comp_continuousOn hc))

lemma cubicThetaPositiveAveragedHeat_top (W : C_c(ℝ,ℂ)) {ε A : ℝ}
    (hε : 0<ε) (hA : 0<A) :
    cubicThetaPositiveAveragedHeat W ε A =O[atTop] (fun u : ℝ => Real.exp (-ε*u)) := by
  have ht : cubicThetaDoubleHeat (Real.sqrt ε) (A*ε) =O[atTop]
      (fun u : ℝ => Real.exp (-ε*u)) := by
    simpa only [Real.sq_sqrt hε.le] using cubicThetaDoubleHeat_top (Real.sqrt ε) (mul_pos hA hε)
  apply IsBigO.trans ?_ ht
  apply IsBigO.of_bound (cubicThetaPositiveRadialWeightMass W ε)
  filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
  exact cubicThetaPositiveAveragedHeat_bound W hε hA hu

lemma cubicThetaPositiveAveragedHeat_bottom (W : C_c(ℝ,ℂ)) {ε A : ℝ}
    (hε : 0<ε) (hA : 0<A) (b : ℝ) :
    cubicThetaPositiveAveragedHeat W ε A =O[𝓝[>] 0] (fun u : ℝ => u^(-b)) := by
  apply IsBigO.trans ?_ (cubicThetaDoubleHeat_bottom (Real.sqrt ε) (mul_pos hA hε) b)
  apply IsBigO.of_bound (cubicThetaPositiveRadialWeightMass W ε)
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact cubicThetaPositiveAveragedHeat_bound W hε hA hu

theorem cubicThetaPositiveAveragedHeat_mellin_entire (W : C_c(ℝ,ℂ)) {ε A : ℝ}
    (hε : 0<ε) (hA : 0<A) :
    Differentiable ℂ (mellin (cubicThetaPositiveAveragedHeat W ε A)) := by
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow_exp hε
    ((cubicThetaPositiveAveragedHeat_continuous W hε hA).locallyIntegrableOn measurableSet_Ioi)
    (cubicThetaPositiveAveragedHeat_top W hε hA)
    (cubicThetaPositiveAveragedHeat_bottom W hε hA (s.re-1)) (by linarith)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveRadialMellin
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full positive-height radial Fourier factor is entire. All
integral interchanges retain the positive cutoff rather than discarding it. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPositiveRadialMellin_integrable (W : C_c(ℝ,ℂ)) {ε A : ℝ}
    (hε : 0<ε) (hA : 0<A) (s : ℂ) :
    Integrable (cubicThetaRadialMellinIntegrand W A s)
      ((volume.restrict (Ioi ε)).prod (volume.restrict (Ioi (0:ℝ)))) := by
  have hh := (cubicThetaDoubleHeat_mellinConvergent (Real.sqrt_pos.mpr hε)
    (mul_pos hA hε) (s-1)).norm
  change IntegrableOn (fun u : ℝ => ‖(u:ℂ)^(s-1-1)*
    cubicThetaDoubleHeat (Real.sqrt ε) (A*ε) u‖) (Ioi 0) at hh
  rw [show s-1-1=s-2 by ring] at hh
  have hm := (cubicThetaPositiveRadialWeight_integrable W hε).mul_prod hh
  rw [Measure.prod_restrict] at hm ⊢
  apply hm.mono' (by
    apply Measurable.aestronglyMeasurable
    unfold cubicThetaRadialMellinIntegrand cubicThetaLinearHeat
    fun_prop)
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
  have hb := mul_le_mul_of_nonneg_left
    (cubicThetaPositiveLinearHeat_bound W hε hA hp.2 hp.1) (_root_.norm_nonneg ((p.2:ℂ)^(s-2)))
  simpa only [cubicThetaRadialMellinIntegrand,norm_mul,mul_comm,mul_left_comm,mul_assoc] using hb

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPositiveRadialWindow
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mellin windows at an arbitrary strictly positive height cutoff. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPositiveWindow_entire (W : C_c(ℝ,ℂ)) {ε : ℝ}
    (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    Differentiable ℂ (mellin (star W)) :=
  smooth_mellin_entire (star W) (star W).hasCompactSupport
    (cubicThetaPositiveWindow_support W hε hW) (star W).continuous

lemma cubicThetaPositiveWindow_power_integrable (W : C_c(ℝ,ℂ)) {ε : ℝ}
    (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (a : ℂ) :
    IntegrableOn (fun v => star (W v)*(v:ℂ)^a/(v:ℂ)^3) (Ioi ε) := by
  have hm := smooth_mellin_convergent (star W) (star W).hasCompactSupport
    (cubicThetaPositiveWindow_support W hε hW) (star W).continuous (a-2)
  apply (hm.mono_set (Ioi_subset_Ioi hε.le)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hε.trans hv).ne'
  change (v:ℂ)^(a-2-1)*star (W v)=star (W v)*(v:ℂ)^a/(v:ℂ)^3
  rw [mul_div_assoc,←Complex.cpow_natCast,←Complex.cpow_sub _ _ hv0]
  rw [show a-2-1=a-(3:ℕ) by norm_num; ring]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootDilationObservation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact observation scaling under the once-cubic dilation. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaRadialIntegral_scaled_weight (r : ℝ) (hr : 1 ≤ r)
    (W : C_c(ℝ,ℂ)) (hW : ∀ v≤2*r,W v=0) (f : ℝ → ℂ) :
    (∫ v in Ioi (2:ℝ),star (cubicThetaRadialWeightScale r (lt_of_lt_of_le zero_lt_one hr) W v)/
      (v:ℂ)^3*f (r*v))=(r:ℂ)^2*∫ v in Ioi (2:ℝ),star (W v)/(v:ℂ)^3*f v := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  let V := cubicThetaRadialWeightScale r hr0 W
  have hV : ∀ v≤(2:ℝ),V v=0 := by
    intro v hv
    change W (r*v)=0
    exact hW _ (by nlinarith)
  have hW2 : ∀ v≤(2:ℝ),W v=0 := fun v hv => hW v (by linarith)
  rw [cubicThetaRadialIntegral_zero_extension V hV,
    cubicThetaRadialIntegral_zero_extension W hW2,cubicThetaRadialIntegral_dilate r hr0 V f]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  change star (W (r*(v/r)))/(v:ℂ)^3*f v=star (W v)/(v:ℂ)^3*f v
  rw [mul_div_cancel₀ v hr0.ne']

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeResidueTestWeight
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete high-cusp test with a nonzero common radial factor for
the three unramified residue coordinates. -/
noncomputable section
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaRadialTestWeight_low {v : ℝ} (hv : v≤2) :
    cubicThetaRadialTestWeight v=0 := by
  change ((max 0 (1-|v-3|):ℝ):ℂ)=0
  rw [abs_of_nonpos (by linarith),max_eq_left (by linarith),Complex.ofReal_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRemainderWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A summable majorant on the actual Fourier lattice, with its full mass bounded. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaPrimaryDerivativeWeight (p : CubicThetaIntegerPoint) : ℝ :=
  ((9/2:ℝ)*Real.pi)*(if p=(0,0) then 0 else cubicThetaPrimaryTailMass p)

def cubicThetaRamifiedDerivativeWeight (p : CubicThetaIntegerPoint) : ℝ :=
  (27*Real.pi)*(if p=(0,0) then 0 else cubicThetaRamifiedTailMass p)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaWindowFlux
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial Green flux of the actual compact incoming window. -/
noncomputable section
open Set Filter
open scoped Topology
namespace CubicFirstMoment

def cubicThetaWindowFlux (v : ℝ) : ℂ :=
  (v:ℂ)^(-1/3:ℂ)*deriv (cubicThetaWindowHeight (4/3)) v -
    (2/3:ℂ)*(v:ℂ)^(-4/3:ℂ)*cubicThetaWindowHeight (4/3) v

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaWindowFluxIntegral
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact boundary evaluation of the constant theta-window observation. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaHighWindowFluxDensity (v : ℝ) : ℂ :=
  (v:ℂ)^(-7/3:ℂ)*cubicThetaHighWindowForcing (4/3) v

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.Sobolev
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

structure trunc extends (CS 2 ℝ) where
  h3 : (Set.Icc (-1) (1)).indicator 1 ≤ toFun
  h4 : toFun ≤ Set.indicator (Set.Ioo (-2) (2)) 1

namespace trunc

instance instCoeFunForallReal : CoeFun trunc (fun _ => ℝ → ℝ) where coe f := f.toFun

instance instCoeCSOfNatNatReal : Coe trunc (CS 2 ℝ) where coe := trunc.toCS

end trunc

namespace W1

lemma iteratedDeriv_sub {f g : ℝ → E} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    iteratedDeriv n (f - g) = iteratedDeriv n f - iteratedDeriv n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    have hf' : ContDiff ℝ n (_root_.deriv f) := hf.iterate_deriv' n 1
    have hg' : ContDiff ℝ n (_root_.deriv g) := hg.iterate_deriv' n 1
    have hfg : _root_.deriv (f - g) = _root_.deriv f - _root_.deriv g := by
      ext x ; apply deriv_sub
      · exact (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt
      · exact (hg.differentiable (by simp)).differentiableAt
    simp_rw [iteratedDeriv_succ', ← ih hf' hg', hfg]

noncomputable def deriv (f : W1 (n + 1) E) : W1 n E where
  toFun := _root_.deriv f
  smooth := contDiff_succ_iff_deriv.mp f.smooth |>.2.2
  integrable k hk := by
    simpa [iteratedDeriv_succ'] using f.integrable (Nat.succ_le_succ hk)

def sub (f g : W1 n E) : W1 n E where
  toFun := f - g
  smooth := f.smooth.sub g.smooth
  integrable k hk := by
    have hf : ContDiff ℝ k f := f.smooth.of_le (by simp [hk])
    have hg : ContDiff ℝ k g := g.smooth.of_le (by simp [hk])
    simpa [iteratedDeriv_sub hf hg] using (f.integrable hk).sub (g.integrable hk)

instance instSub : Sub (W1 n E) where sub := sub

lemma integrable_iteratedDeriv_Schwarz {f : 𝓢(ℝ, ℂ)} : Integrable (iteratedDeriv n f) := by
  induction n generalizing f with
  | zero => exact f.integrable
  | succ n ih => simpa [iteratedDeriv_succ'] using! ih (f := SchwartzMap.derivCLM ℝ ℂ f)

noncomputable def of_Schwartz (f : 𝓢(ℝ, ℂ)) : W1 n ℂ where
  toFun := f
  smooth := f.smooth n
  integrable _ _ := integrable_iteratedDeriv_Schwarz

end W1

namespace W21

variable {f : W21}

noncomputable instance instCoeSchwartzMapRealComplex : Coe 𝓢(ℝ, ℂ) W21 where coe := W1.of_Schwartz

def ofCS2 (f : CS 2 ℂ) : W21 := by
  refine ⟨f, f.h1, fun k hk => ?_⟩ ; match k with
  | 0 => exact f.h1.continuous.integrable_of_hasCompactSupport f.h2
  | 1 => simpa using (f.h1.continuous_deriv one_le_two).integrable_of_hasCompactSupport f.h2.deriv
  | 2 => simpa [iteratedDeriv_succ] using
    (f.h1.iterate_deriv' 0 2).continuous.integrable_of_hasCompactSupport f.h2.deriv.deriv

instance instCoeCSOfNatNatComplex : Coe (CS 2 ℂ) W21 where coe := ofCS2

instance instHMulCSOfNatNatComplex : HMul (CS 2 ℂ) W21 (CS 2 ℂ) where
  hMul g f := ⟨g * f, g.h1.mul f.smooth, g.h2.mul_right⟩

instance instHMulCSOfNatNatRealComplex : HMul (CS 2 ℝ) W21 (CS 2 ℂ) where hMul g f := (g : CS 2 ℂ) * f

end W21
end

section
-- module Solutions.OAIQ096_CM.Fourier
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv
end

section
-- module Solutions.OAIQ096_CM.Wiener
private local instance wienerCoeRealComplex {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option linter.style.header false

-- note: the opening of ArithmeticFunction introduces a notation σ that seems
-- impossible to hide, and hence parameters that are traditionally called σ will
-- have to be called σ' instead in this file.

open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate

variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]


-- TODO - add to mathlib
attribute [fun_prop] Real.continuous_fourierChar

attribute [fun_prop] measurable_coe_nnreal_ennreal



noncomputable def exists_trunc : trunc := by
  choose ψ h1 h2 h3 h4 using smooth_urysohn (-2) (-1) (1) (2) (by linarith) (by linarith)
  exact ⟨⟨ψ, h1.of_le (by norm_cast), h2⟩, h3, h4⟩
end


