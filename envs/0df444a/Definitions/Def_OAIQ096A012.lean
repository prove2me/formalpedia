-- Prove2me | Definitions.Def_OAIQ096A012
-- name    : OAIQ096A012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T03:43:22.087565+00:00
-- url     : https://prove2.me/theorems/469d2940-873f-4e30-987a-dbb3d761e990
-- title:
--   Definitions bundle OAIQ096A012 of the split of OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 224 declarations of OpenAI's Lean: 69 definitions, 6 instances and 149 theorems. The definitions and types are `OAI.CubicFirstMoment.cubicThetaActualCuspCoefficient`, `OAI.CubicFirstMoment.cubicThetaAnnularRepresentative`, `OAI.CubicFirstMoment.cubicThetaArithmeticAxis`, `OAI.CubicFirstMoment.cubicThetaArithmeticAxisDerivative`, `OAI.CubicFirstMoment.cubicThetaArithmeticCoefficient`, `OAI.CubicFirstMoment.cubicThetaArithmeticFourierEnergy`, `OAI.CubicFirstMoment.cubicThetaArithmeticRowTerm`, `OAI.CubicFirstMoment.cubicThetaArithmeticSection`, `OAI.CubicFirstMoment.cubicThetaCoefficientTwist`, `OAI.CubicFirstMoment.cubicThetaConjugateCoefficient`, `OAI.CubicFirstMoment.cubicThetaCuspIndex`, `OAI.CubicFirstMoment.cubicThetaCuspLatticeWeight`, `OAI.CubicFirstMoment.cubicThetaCuspPullback`, `OAI.CubicFirstMoment.cubicThetaCuspRow`, `OAI.CubicFirstMoment.cubicThetaGlobalMultiplier`, `OAI.CubicFirstMoment.cubicThetaGlobalMultiplierLinear`, `OAI.CubicFirstMoment.cubicThetaGlobalRestriction`, `OAI.CubicFirstMoment.cubicThetaHighCuspRow`, `OAI.CubicFirstMoment.cubicThetaInversionSection`, `OAI.CubicFirstMoment.cubicThetaLocalEnergyTestLinear`, `OAI.CubicFirstMoment.cubicThetaLocalValue`, `OAI.CubicFirstMoment.cubicThetaPrimaryBottomDefect`, `OAI.CubicFirstMoment.cubicThetaPrimaryBottomPrincipal`, `OAI.CubicFirstMoment.cubicThetaPrimaryBottomSeed`, `OAI.CubicFirstMoment.cubicThetaPrimaryCuspCenter`, `OAI.CubicFirstMoment.cubicThetaPrimaryDualCenter`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeAtkinConjugate`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeAtkinEquiv`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeAtkinMatrix`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeAtkinSection`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeChart`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeChartEquiv`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeCoset`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeCosetPermutation`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeCosetStep`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeCoverDomain`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeDilationSection`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeHecke`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeHeckeMatrix`, `OAI.CubicFirstMoment.cubicThetaPrimeCubeLowerChart` and 29 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `CubicMoment_Estimates_HuxleyGaussianPacking`, `CubicMoment_Estimates_HuxleyGaussianRows`, `CubicMoment_Estimates_HuxleyGridPacking`, `CubicMoment_Estimates_HuxleyLiftedPacking`, `CubicMoment_Estimates_IdealMellinSeries`, `CubicMoment_Estimates_IdealThetaDecay`, `CubicMoment_Estimates_IdealThetaLattice`, `CubicMoment_Estimates_PrincipalIdealTheta`, `CubicMoment_Estimates_PrincipalLatticeTheta`, `CubicMoment_Estimates_PublishedPrimitiveHecke`, `CubicMoment_Estimates_ResidueGaussianScale`, `CubicMoment_Theta_CubicThetaActualCuspCoefficients`, `CubicMoment_Theta_CubicThetaActualProjection`, `CubicMoment_Theta_CubicThetaAnnularL2`, `CubicMoment_Theta_CubicThetaArithmetic`, `CubicMoment_Theta_CubicThetaArithmeticChartWeak`, `CubicMoment_Theta_CubicThetaArithmeticCuspMass`, `CubicMoment_Theta_CubicThetaArithmeticLocalWeak`, `CubicMoment_Theta_CubicThetaArithmeticModelEnergy`, `CubicMoment_Theta_CubicThetaArithmeticRemainder`, `CubicMoment_Theta_CubicThetaArithmeticRowSeries`, `CubicMoment_Theta_CubicThetaArithmeticSection`, `CubicMoment_Theta_CubicThetaAxisDerivativeBalance`, `CubicMoment_Theta_CubicThetaCoefficientMellin`, `CubicMoment_Theta_CubicThetaComplexLocalization`, `CubicMoment_Theta_CubicThetaCoordinateIntegrationByParts`, `CubicMoment_Theta_CubicThetaCoordinateSectionPairing`, `CubicMoment_Theta_CubicThetaCoreMassCompact`, `CubicMoment_Theta_CubicThetaCoreRestriction`, `CubicMoment_Theta_CubicThetaCuspLatticeWeight`, `CubicMoment_Theta_CubicThetaCuspRemainderBound`, `CubicMoment_Theta_CubicThetaCuspRowTransport`, `CubicMoment_Theta_CubicThetaCuspScalarIntegrals`, `CubicMoment_Theta_CubicThetaEven`, `CubicMoment_Theta_CubicThetaFiniteCuspEnergy`, `CubicMoment_Theta_CubicThetaFullRows`, `CubicMoment_Theta_CubicThetaGlobalLocalRellich`, `CubicMoment_Theta_CubicThetaGlobalMultiplier`, `CubicMoment_Theta_CubicThetaGreenAlgebra`, `CubicMoment_Theta_CubicThetaHighCuspDerivativeBound`, `CubicMoment_Theta_CubicThetaHighCuspDifferentiation`, `CubicMoment_Theta_CubicThetaHighCuspRows`, `CubicMoment_Theta_CubicThetaIntegralQuotient`, `CubicMoment_Theta_CubicThetaInversionCharacter`, `CubicMoment_Theta_CubicThetaInversionEnergy`, `CubicMoment_Theta_CubicThetaLocalEnergyGraph`, `CubicMoment_Theta_CubicThetaLocalGreen`, `CubicMoment_Theta_CubicThetaMellinReciprocity`, `CubicMoment_Theta_CubicThetaPrimaryBottom`, `CubicMoment_Theta_CubicThetaPrimaryCoefficients`, `CubicMoment_Theta_CubicThetaPrimaryPeriodicity`, `CubicMoment_Theta_CubicThetaPrimaryPowerCoordinates`, `CubicMoment_Theta_CubicThetaPrimeCubeAtkin`, `CubicMoment_Theta_CubicThetaPrimeCubeAtkinIntegral`, `CubicMoment_Theta_CubicThetaPrimeCubeChartCover`, `CubicMoment_Theta_CubicThetaPrimeCubeChartEquiv`, `CubicMoment_Theta_CubicThetaPrimeCubeCosets`, `CubicMoment_Theta_CubicThetaPrimeCubeCoverDomain`, `CubicMoment_Theta_CubicThetaPrimeCubeDegree`, `CubicMoment_Theta_CubicThetaPrimeCubeDilationNorm`, `CubicMoment_Theta_CubicThetaPrimeCubeEnergyIntegral`, `CubicMoment_Theta_CubicThetaPrimeCubeHeckeLinear`, `CubicMoment_Theta_CubicThetaPrimeCubeHeckeRegularity`, `CubicMoment_Theta_CubicThetaPrimeCubeInvariantDilation`, `CubicMoment_Theta_CubicThetaPrimeCubeLowerChart`, `CubicMoment_Theta_CubicThetaPrimeCubeRootCoverDomain`, `CubicMoment_Theta_CubicThetaPrimeCubeRootDilation`, `CubicMoment_Theta_CubicThetaPrimeCubeRootDilationFixed`, `CubicMoment_Theta_CubicThetaPrimeCubeRootHeckeCover`, `CubicMoment_Theta_CubicThetaPrimeCubeRootLiftL2`, `CubicMoment_Theta_CubicThetaPrimeCubeRootMassTransport`, `CubicMoment_Theta_CubicThetaPrimeCubeRootSections`, `CubicMoment_Theta_CubicThetaPrimeCubeSectionAtkin`, `CubicMoment_Theta_CubicThetaPrimeCubeSections`, `CubicMoment_Theta_CubicThetaPrimeCubeTrace`, `CubicMoment_Theta_CubicThetaPrimeCubeTraceNorm`, `CubicMoment_Theta_CubicThetaPrimeCubeTransversal`, `CubicMoment_Theta_CubicThetaPrimeCubeUpperChart`, `CubicMoment_Theta_CubicThetaPrimeRootSections`, `CubicMoment_Theta_CubicThetaPrimitivePower`, `CubicMoment_Theta_CubicThetaProjectedCoefficient`, `CubicMoment_Theta_CubicThetaProjectedPlane`, `CubicMoment_Theta_CubicThetaRamifiedCoefficientSupport`, `CubicMoment_Theta_CubicThetaRamifiedMissingCoefficient`, `CubicMoment_Theta_CubicThetaRamifiedModel`, `CubicMoment_Theta_CubicThetaRamifiedPrimaryResidue`, `CubicMoment_Theta_CubicThetaSectionPairing`, `CubicMoment_Theta_CubicThetaShiftedLattice`, `CubicMoment_Theta_CubicThetaSieveProjection`, `CubicMoment_Theta_CubicThetaUnitPhaseSymbol`.
--
--   **Imports.** It imports the published bundle `Def_PattersonFirstMoment`; the bundles `OAIQ096A007`, `OAIQ096A008` and `OAIQ096A009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ096A016`, `OAIQ096A017`, `OAIQ096A018` and `OAIQ096A019`; the statement `OAI.CubicFirstMoment.cubicThetaArithmeticAxisDerivative_re_neg`; the proofs of `OAI.CubicFirstMoment.LogarithmicWeightFamily.metaplectic_long_sieve`, `OAI_CubicFirstMoment_LogarithmicWeightFamily_radial_model_low_power`, `OAI_CubicFirstMoment_UniformLogWeights_cubeModelTerm_mass_error`, `OAI_CubicFirstMoment_angular_cube_poisson_log_saving`, `OAI_CubicFirstMoment_angular_stopped_cube_uniform_error`, `OAI_CubicFirstMoment_cube_poisson_log_saving`, `OAI.CubicFirstMoment.first_angular_primeCoordinateError_moment`, `OAI.CubicFirstMoment.primeGroupTail_coprime_mellin_height_power` and `OAI_CubicFirstMoment_stopped_cube_uniform_error`.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A007
import Definitions.Def_OAIQ096A008
import Definitions.Def_OAIQ096A009

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMellinSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma idealExponentOf_generator (ν : EisensteinIdealExponent) :
    idealExponentOf (idealExponentGenerator ν) = ν := by
  induction ν using Finsupp.induction_linear with
  | zero => simpa [idealExponentGenerator] using idealExponentOf_one_aux
  | add ν κ hν hκ =>
      rw [idealExponentGenerator_add,idealExponentOf_mul
        (idealExponentGenerator_ne_zero ν) (idealExponentGenerator_ne_zero κ),hν,hκ]
  | single p k =>
      simp only [idealExponentGenerator,Finsupp.prod_single_index,pow_zero]
      rw [idealExponentOf_pow (idealPrimeRepresentative_irreducible p).ne_zero,
        idealExponentOf_primeRepresentative]
      simp

lemma idealExponentGenerator_injective : Function.Injective idealExponentGenerator :=
  Function.LeftInverse.injective idealExponentOf_generator

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyLiftedPacking
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local multiplicity of the reduced fractions and all their lattice translates. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma huxleyLift_eq_of_frequency_of_denominator {Q : ℝ} {i j : HuxleyLift}
    (hi : i.reduced Q) (hj : j.reduced Q)
    (hq : i.denominator = j.denominator) (hf : i.frequency = j.frequency) : i = j := by
  rcases i with ⟨q,a,u⟩
  rcases j with ⟨r,b,v⟩
  dsimp at hq
  subst r
  have hq0 : q ≠ 0 := hi.1
  have hqc : (q:ℂ) ≠ 0 := fun h => hq0 (Subtype.ext h)
  have he : a-b-(v-u)*q = 0 := by
    apply Subtype.ext
    change (a:ℂ)-(b:ℂ)-((v:ℂ)-(u:ℂ))*(q:ℂ) = 0
    dsimp [HuxleyLift.frequency] at hf
    field_simp at hf
    linear_combination hf
  have heq := congrArg (Ideal.Quotient.mk (modulus q)) he
  have hqz : Ideal.Quotient.mk (modulus q) q = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_refl q))
  simp only [map_sub,map_mul,map_zero,hqz,mul_zero,sub_zero,sub_eq_zero] at heq
  have hab : a = b := hi.2.2.2.symm.trans ((congrArg (residueRepresentative q) heq).trans hj.2.2.2)
  subst b
  have huv : u = v := by
    apply Subtype.ext
    dsimp [HuxleyLift.frequency] at hf
    exact add_left_cancel hf
  subst v
  rfl

lemma huxleyLift_eq_frequency_of_close {Q : ℝ} {i j : HuxleyLift}
    (hi : i.reduced Q) (hj : j.reduced Q)
    (hclose : ‖i.frequency-j.frequency‖^2 < 1/Q^2) :
    i.frequency = j.frequency :=
  translated_fraction_eq_of_close hi.1 hj.1 hi.2.1 hj.2.1
    i.numerator j.numerator i.shift j.shift hclose

lemma huxleyLift_associated_of_close {Q : ℝ} {i j : HuxleyLift}
    (hi : i.reduced Q) (hj : j.reduced Q)
    (hclose : ‖i.frequency-j.frequency‖^2 < 1/Q^2) :
    Associated i.denominator j.denominator := by
  apply reduced_fraction_associated_denominators hi.2.2.1 hj.2.2.1
  by_contra hne
  have hsep := eisenstein_fraction_separation hi.1 hj.1 hi.2.1 hj.2.1
    i.numerator j.numerator (j.shift-i.shift) hne
  have he : (i.numerator:ℂ)/(i.denominator:ℂ)-(j.numerator:ℂ)/(j.denominator:ℂ)-
      ((j.shift-i.shift:Eisenstein):ℂ) = i.frequency-j.frequency := by
    dsimp [HuxleyLift.frequency]
    ring
  rw [he] at hsep
  exact (not_le_of_gt hclose) hsep

/-- A small disk contains at most eighteen lifted reduced fractions, counting
all associate denominators and all lattice translations. -/
lemma huxleyLift_local_count (Q : ℝ) (hQ : 0 < Q) (z : ℂ) (S : Finset HuxleyLift)
    (hred : ∀ i ∈ S, i.reduced Q)
    (hclose : ∀ i ∈ S, ‖i.frequency-z‖ < 1/(3*Q)) :
    (S.card:ℝ) ≤ 18 := by
  classical
  by_cases hs : S.Nonempty
  · obtain ⟨i0,hi0⟩ := hs
    have hpair (i : HuxleyLift) (hi : i ∈ S) :
        ‖i.frequency-i0.frequency‖^2 < 1/Q^2 := by
      have ht := dist_triangle i.frequency z i0.frequency
      simp only [dist_eq_norm] at ht
      rw [norm_sub_rev z i0.frequency] at ht
      have hh : ‖i.frequency-i0.frequency‖ < 1/Q := by
        have hi' := hclose i hi
        have h0' := hclose i0 hi0
        have hdiv : 1/(3*Q)+1/(3*Q) < 1/Q := by
          field_simp
          linarith
        linarith
      have hd : 0 ≤ 1/Q := (one_div_pos.mpr hQ).le
      have hsq := (sq_lt_sq₀ (_root_.norm_nonneg _) hd).mpr hh
      simpa only [one_div_pow,one_pow] using hsq
    have hinj : Set.InjOn HuxleyLift.denominator (↑S : Set HuxleyLift) := by
      intro i hi j hj hij
      apply huxleyLift_eq_of_frequency_of_denominator (hred i hi) (hred j hj) hij
      exact (huxleyLift_eq_frequency_of_close (hred i hi) (hred i0 hi0) (hpair i hi)).trans
        (huxleyLift_eq_frequency_of_close (hred j hj) (hred i0 hi0) (hpair j hj)).symm
    have hsub : S.image HuxleyLift.denominator ⊆
        (S.image HuxleyLift.denominator).filter (fun q => Associated i0.denominator q) := by
      intro q hq
      refine Finset.mem_filter.mpr ⟨hq,?_⟩
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
      exact (huxleyLift_associated_of_close (hred i hi) (hred i0 hi0) (hpair i hi)).symm
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_iff.mpr hinj] at hc
    exact (show (S.card:ℝ) ≤
      (((S.image HuxleyLift.denominator).filter (fun q => Associated i0.denominator q)).card:ℝ)
      by exact_mod_cast hc).trans (associated_denominator_count _ _)
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyGridPacking
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square-grid packing of the actual lifted reduced fractions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma huxleyGrid_fiber_count (Q : ℝ) (hQ : 0 < Q) (z : ℂ) (S : Finset HuxleyLift)
    (hred : ∀ i ∈ S, i.reduced Q) (k : ℤ × ℤ) :
    ((S.filter (fun i => huxleyGrid Q z i.frequency = k)).card:ℝ) ≤ 18 := by
  let T := S.filter (fun i => huxleyGrid Q z i.frequency = k)
  by_cases hT : T.Nonempty
  · obtain ⟨i0,hi0⟩ := hT
    apply huxleyLift_local_count Q hQ i0.frequency T
    · intro i hi
      exact hred i (Finset.mem_filter.mp hi).1
    · intro i hi
      apply huxleyGrid_close hQ
      exact (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hi0).2.symm
  · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    change (T.card:ℝ) ≤ _
    simp [he]

lemma huxleyLift_count_of_grid_mem (Q : ℝ) (hQ : 0 < Q) (z : ℂ)
    (S : Finset HuxleyLift) (T : Finset (ℤ × ℤ))
    (hred : ∀ i ∈ S, i.reduced Q)
    (hT : ∀ i ∈ S, huxleyGrid Q z i.frequency ∈ T) :
    (S.card:ℝ) ≤ 18*T.card := by
  have he := Finset.card_eq_sum_card_fiberwise hT
  have he' : (S.card:ℝ) = ∑ k ∈ T,
      ((S.filter (fun i => huxleyGrid Q z i.frequency = k)).card:ℝ) := by
    exact_mod_cast he
  rw [he']
  calc
    _ ≤ ∑ k ∈ T, (18:ℝ) := Finset.sum_le_sum (fun k hk => huxleyGrid_fiber_count Q hQ z S hred k)
    _ = _ := by simp [mul_comm]


/-- Uniform disk count for all reduced residue fractions and their translates. -/
lemma huxleyLift_disk_count (Q : ℝ) (hQ : 0 < Q) (z : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (S : Finset HuxleyLift) (hred : ∀ i ∈ S, i.reduced Q)
    (hball : ∀ i ∈ S, ‖i.frequency-z‖ ≤ R) :
    (S.card:ℝ) ≤ 6000*(1+Q^2*R^2) := by
  let B : ℤ := ⌈6*Q*R⌉+1
  let T := (Finset.Icc (-B) B).product (Finset.Icc (-B) B)
  have hlow : -B = -⌈(6*Q)*R⌉-1 := by dsimp [B]; ring
  have hmem : ∀ i ∈ S, huxleyGrid Q z i.frequency ∈ T := by
    intro i hi
    apply Finset.mem_product.mpr
    constructor
    · change ⌊6*Q*(i.frequency-z).re⌋ ∈ Finset.Icc (-B) B
      rw [hlow]
      exact floor_scaled_in_box (by positivity)
        ((Complex.abs_re_le_norm _).trans (hball i hi))
    · change ⌊6*Q*(i.frequency-z).im⌋ ∈ Finset.Icc (-B) B
      rw [hlow]
      exact floor_scaled_in_box (by positivity)
        ((Complex.abs_im_le_norm _).trans (hball i hi))
  have hc := huxleyLift_count_of_grid_mem Q hQ z S T hred hmem
  have hB0 : 0 ≤ B := by
    dsimp [B]
    have hc0 : (0:ℤ) ≤ ⌈6*Q*R⌉ := Int.ceil_nonneg (by positivity)
    omega
  have hcard : ((Finset.Icc (-B) B).card:ℝ) = 2*(B:ℝ)+1 := by
    rw [Int.card_Icc]
    rw [← Int.cast_natCast,Int.toNat_of_nonneg (by omega)]
    push_cast
    ring
  have hT : (T.card:ℝ) = (2*(B:ℝ)+1)^2 := by
    dsimp [T]
    rw [Finset.card_product,Nat.cast_mul,hcard]
    ring
  rw [hT] at hc
  have hB : (B:ℝ) ≤ 6*Q*R+2 := by
    have hh := Int.ceil_lt_add_one (6*Q*R)
    dsimp [B]
    push_cast
    linarith
  have hsz : 0 ≤ 2*(B:ℝ)+1 := by exact_mod_cast (show (0:ℤ) ≤ 2*B+1 by omega)
  have hsquare : (2*(B:ℝ)+1)^2 ≤ (12*(Q*R)+5)^2 := by
    apply (sq_le_sq₀ hsz (by positivity)).mpr
    linarith
  have hpoly : 18*(12*(Q*R)+5)^2 ≤ 6000*(1+Q^2*R^2) := by
    nlinarith [sq_nonneg (12*(Q*R)-5),sq_nonneg (Q*R)]
  exact hc.trans ((mul_le_mul_of_nonneg_left hsquare (by norm_num)).trans hpoly)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyGaussianPacking
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian mass of the separated lifted fractions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma huxleyLift_gaussian_bin_bound (Q : ℝ) (hQ : 0 < Q) (z : ℂ)
    {t : ℝ} (ht : 0 < t) (S : Finset HuxleyLift)
    (hred : ∀ i ∈ S, i.reduced Q) (k : ℕ) :
    (∑ i ∈ S with ⌊t*‖i.frequency-z‖^2⌋₊ = k,
      Real.exp (-t*‖i.frequency-z‖^2)) ≤
      6000*(1+Q^2*((k:ℝ)+1)/t)*Real.exp (-(k:ℝ)) := by
  let U := S.filter (fun i => ⌊t*‖i.frequency-z‖^2⌋₊ = k)
  let R := Real.sqrt (((k:ℝ)+1)/t)
  have hnum : 0 ≤ ((k:ℝ)+1)/t := by positivity
  have hR : R^2 = ((k:ℝ)+1)/t := Real.sq_sqrt hnum
  have hball : ∀ i ∈ U, ‖i.frequency-z‖ ≤ R := by
    intro i hi
    have hk := (Finset.mem_filter.mp hi).2
    have hlt := Nat.lt_floor_add_one (t*‖i.frequency-z‖^2)
    rw [hk] at hlt
    apply (Real.le_sqrt (_root_.norm_nonneg _) hnum).mpr
    exact (le_div_iff₀ ht).mpr (by nlinarith)
  have hcard := huxleyLift_disk_count Q hQ z R (Real.sqrt_nonneg _) U
    (fun i hi => hred i (Finset.mem_filter.mp hi).1) hball
  have hpoint : ∀ i ∈ U, Real.exp (-t*‖i.frequency-z‖^2) ≤ Real.exp (-(k:ℝ)) := by
    intro i hi
    have hk := (Finset.mem_filter.mp hi).2
    have hlo := Nat.floor_le (show 0 ≤ t*‖i.frequency-z‖^2 by positivity)
    rw [hk] at hlo
    exact Real.exp_le_exp.mpr (by nlinarith)
  change (∑ i ∈ U, Real.exp (-t*‖i.frequency-z‖^2)) ≤ _
  calc
    _ ≤ ∑ i ∈ U, Real.exp (-(k:ℝ)) := Finset.sum_le_sum hpoint
    _ = (U.card:ℝ)*Real.exp (-(k:ℝ)) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      rw [hR] at hcard
      simpa only [mul_div_assoc] using hcard

/-- The Gaussian row bound has exactly the required two-dimensional scale. -/
lemma huxleyLift_gaussian_sum_bound (Q : ℝ) (hQ : 0 < Q) (z : ℂ)
    {t : ℝ} (ht : 0 < t) (S : Finset HuxleyLift)
    (hred : ∀ i ∈ S, i.reduced Q) :
    (∑ i ∈ S, Real.exp (-t*‖i.frequency-z‖^2)) ≤
      huxleyGaussianConstant*(1+Q^2/t) := by
  let bin := fun i : HuxleyLift => ⌊t*‖i.frequency-z‖^2⌋₊
  let K := S.image bin
  have he : (∑ i ∈ S, Real.exp (-t*‖i.frequency-z‖^2)) =
      ∑ k ∈ K, ∑ i ∈ S with bin i = k, Real.exp (-t*‖i.frequency-z‖^2) := by
    exact (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image.mpr ⟨i,hi,rfl⟩) _).symm
  have hα : 0 ≤ Q^2/t := by positivity
  calc
    _ = _ := he
    _ ≤ ∑ k ∈ K, 6000*(1+Q^2*((k:ℝ)+1)/t)*Real.exp (-(k:ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact huxleyLift_gaussian_bin_bound Q hQ z ht S hred k
    _ ≤ ∑ k ∈ K, (6000*(1+Q^2/t))*(((k:ℝ)+2)*Real.exp (-(k:ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      have hpoly : 1+Q^2*((k:ℝ)+1)/t ≤ (1+Q^2/t)*((k:ℝ)+2) := by
        have hkn : (0:ℝ) ≤ k := Nat.cast_nonneg k
        rw [show Q^2*((k:ℝ)+1)/t = (Q^2/t)*((k:ℝ)+1) by ring]
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hpoly (Real.exp_pos (-(k:ℝ))).le]
    _ = (6000*(1+Q^2/t))*∑ k ∈ K, ((k:ℝ)+2)*Real.exp (-(k:ℝ)) := by rw [Finset.mul_sum]
    _ ≤ (6000*(1+Q^2/t))*∑' k : ℕ, ((k:ℝ)+2)*Real.exp (-(k:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact huxley_gaussian_weight_summable.sum_le_tsum K (fun k hk => by positivity)
    _ = _ := by unfold huxleyGaussianConstant; ring

def huxleyLiftGaussian (Q t : ℝ) (z : ℂ) (i : HuxleyLift) : ℝ :=
  if i.reduced Q then Real.exp (-t*‖i.frequency-z‖^2) else 0

lemma huxleyLiftGaussian_finite_bound (Q : ℝ) (hQ : 0 < Q) (z : ℂ)
    {t : ℝ} (ht : 0 < t) (S : Finset HuxleyLift) :
    (∑ i ∈ S, huxleyLiftGaussian Q t z i) ≤ huxleyGaussianConstant*(1+Q^2/t) := by
  simp only [huxleyLiftGaussian,← Finset.sum_filter]
  exact huxleyLift_gaussian_sum_bound Q hQ z ht (S.filter (fun i => i.reduced Q))
    (fun i hi => (Finset.mem_filter.mp hi).2)

lemma huxleyLiftGaussian_summable (Q : ℝ) (hQ : 0 < Q) (z : ℂ)
    {t : ℝ} (ht : 0 < t) : Summable (huxleyLiftGaussian Q t z) := by
  apply summable_of_sum_le (c := huxleyGaussianConstant*(1+Q^2/t))
  · intro i
    unfold huxleyLiftGaussian
    split_ifs <;> positivity
  · exact huxleyLiftGaussian_finite_bound Q hQ z ht

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HuxleyGaussianRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma huxleyPeriodizedGaussian_summable {t : ℝ} (ht : 0 < t) (x : ℂ) :
    Summable (fun z : Eisenstein => Real.exp (-t*‖(z:ℂ)-x‖^2)) := by
  let a : Eisenstein := residueRepresentative 1 0
  let lift : Eisenstein → HuxleyLift := fun z => ⟨1,a,z-a⟩
  have hi : Function.Injective lift := by
    intro z w h
    have he := congrArg HuxleyLift.shift h
    simpa only [lift,sub_left_inj] using he
  have hr (z : Eisenstein) : (lift z).reduced 1 := by
    dsimp only [HuxleyLift.reduced,lift]
    refine ⟨one_ne_zero,?_,isCoprime_one_left,?_⟩
    · simp [norm]
    · change residueRepresentative 1 (Ideal.Quotient.mk (modulus 1) a) = a
      dsimp only [a]
      rw [residueRepresentative_spec]
  have hs := (huxleyLiftGaussian_summable 1 zero_lt_one x ht).comp_injective hi
  change Summable (fun z => huxleyLiftGaussian 1 t x (lift z)) at hs
  apply hs.congr
  intro z
  rw [huxleyLiftGaussian,ite_eq_left (hr z)]
  have he : (lift z).frequency = (z:ℂ) := by simp [lift,HuxleyLift.frequency]
  rw [he]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealThetaDecay
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convergence and exponential decay of the actual ideal theta series. -/
noncomputable section
open scoped Topology
open Filter Asymptotics
namespace CubicFirstMoment

lemma summable_ideal_exponential {c : ℝ} (hc : 0 < c) :
    Summable (fun ν : EisensteinIdealExponent => Real.exp (-c*idealExponentNorm ν)) := by
  have hs := (huxleyPeriodizedGaussian_summable hc 0).comp_injective idealExponentGenerator_injective
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  ext ν
  simp only [Function.comp_apply,sub_zero,idealExponentNorm,normNat_cast,norm,
    Complex.normSq_eq_norm_sq]

lemma idealTheta_summable {A t : ℝ} (hA : 0 < A) (ht : 0 < t)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) :
    Summable (fun ν => χ ν*(Real.exp (-idealExponentNorm ν*t/A):ℝ)) := by
  apply (summable_ideal_exponential (div_pos ht hA)).of_norm_bounded
  intro ν
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have he : -idealExponentNorm ν*t/A = -(t/A)*idealExponentNorm ν := by ring
  rw [he]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (hχ ν)

lemma idealTheta_norm_bound {A : ℝ} (hA : 0 < A)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    {t : ℝ} (ht : 1 ≤ t) :
    ‖idealTheta A χ t‖ ≤
      (∑' ν : EisensteinIdealExponent, Real.exp (-idealExponentNorm ν/(2*A)))*
        Real.exp (-t/(2*A)) := by
  have ht0 : 0 < t := by linarith
  have hs := idealTheta_summable hA ht0 χ hχ
  have he := summable_ideal_exponential (show 0 < 1/(2*A) by positivity)
  have hg : Summable (fun ν : EisensteinIdealExponent =>
      Real.exp (-idealExponentNorm ν/(2*A))*Real.exp (-t/(2*A))) := by
    convert he.mul_right (Real.exp (-t/(2*A))) using 1
    all_goals try with_reducible_and_instances rfl
    ext ν
    congr 2
    ring
  unfold idealTheta
  calc
    _ ≤ ∑' ν, ‖χ ν*(Real.exp (-idealExponentNorm ν*t/A):ℝ)‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' ν : EisensteinIdealExponent,
        Real.exp (-idealExponentNorm ν/(2*A))*Real.exp (-t/(2*A)) := by
      apply hs.norm.tsum_le_tsum _ hg
      intro ν
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      apply (mul_le_of_le_one_left (Real.exp_pos _).le (hχ ν)).trans
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hn := idealExponentNorm_ge_one ν
      have hprod := mul_nonneg (sub_nonneg.mpr hn) (sub_nonneg.mpr ht)
      have hh : -2*(idealExponentNorm ν*t) ≤ -idealExponentNorm ν-t := by nlinarith
      have hh' := div_le_div_of_nonneg_right hh (show 0 ≤ 2*A by positivity)
      convert hh' using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)
      all_goals ring
    _ = _ := tsum_mul_right

lemma idealTheta_continuousOn_ray {A δ : ℝ} (hA : 0 < A) (hδ : 0 < δ)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) :
    ContinuousOn (idealTheta A χ) (Set.Ici δ) := by
  apply continuousOn_tsum (fun ν => by fun_prop)
    (summable_ideal_exponential (div_pos hδ hA))
  intro ν t ht
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply (mul_le_of_le_one_left (Real.exp_pos _).le (hχ ν)).trans
  apply Real.exp_le_exp.mpr
  have hn := idealExponentNorm_pos ν
  have hd := div_pos hn hA
  have hm := mul_le_mul_of_nonneg_left ht hd.le
  have hh := neg_le_neg hm
  first | (convert hh using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))

lemma idealTheta_continuousOn {A : ℝ} (hA : 0 < A)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) :
    ContinuousOn (idealTheta A χ) (Set.Ioi 0) := by
  intro t ht
  change 0 < t at ht
  have hr := idealTheta_continuousOn_ray hA (show 0 < t/2 by linarith) χ hχ
  exact (hr.continuousAt (Ici_mem_nhds (show t/2 < t by linarith))).continuousWithinAt

lemma idealTheta_isBigO_exp {A : ℝ} (hA : 0 < A)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) :
    idealTheta A χ =O[atTop] (fun t : ℝ => Real.exp (-(1/(2*A))*t)) := by
  apply Asymptotics.IsBigO.of_bound
    (∑' ν : EisensteinIdealExponent, Real.exp (-idealExponentNorm ν/(2*A)))
  filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
  have he : -(1/(2*A))*t = -t/(2*A) := by ring
  simpa only [he,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
    idealTheta_norm_bound hA χ hχ ht

lemma idealTheta_isBigO_rpow {A : ℝ} (hA : 0 < A)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (r : ℝ) :
    idealTheta A χ =O[atTop] (fun t : ℝ => t^r) :=
  (idealTheta_isBigO_exp hA χ hχ).trans
    (isLittleO_exp_neg_mul_rpow_atTop (show 0 < 1/(2*A) by positivity) r).isBigO

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealThetaLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact ideal-to-element reindexing for a unit-invariant residue theta series. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma idealExponentOf_unit_mul (ν : EisensteinIdealExponent) (u : Eisensteinˣ) :
    idealExponentOf ((u:Eisenstein)*idealExponentGenerator ν) = ν := by
  have ha : Associated (idealExponentGenerator ν) ((u:Eisenstein)*idealExponentGenerator ν) :=
    ⟨u,mul_comm _ _⟩
  exact (idealExponentOf_eq_of_associated
    (mul_ne_zero u.ne_zero (idealExponentGenerator_ne_zero ν))
    (idealExponentGenerator_ne_zero ν) ha.symm).trans (idealExponentOf_generator ν)

lemma idealElementCoordinates_bijective : Function.Bijective
    (fun x : EisensteinIdealExponent × Eisensteinˣ =>
      (⟨(x.2:Eisenstein)*idealExponentGenerator x.1,
        mul_ne_zero x.2.ne_zero (idealExponentGenerator_ne_zero x.1)⟩ :
        {a : Eisenstein // a ≠ 0})) := by
  constructor
  · intro x y h
    have he := congrArg Subtype.val h
    have hv : x.1 = y.1 := by
      simpa only [idealExponentOf_unit_mul] using congrArg idealExponentOf he
    rcases x with ⟨ν,u⟩
    rcases y with ⟨κ,v⟩
    dsimp only at hv he
    subst κ
    exact congrArg (fun w : Eisensteinˣ => (ν,w))
      (Units.ext (mul_right_cancel₀ (idealExponentGenerator_ne_zero ν) he))
  · intro a
    obtain ⟨u,hu⟩ := idealExponentOf_associated a.property
    refine ⟨(idealExponentOf a.val,u),Subtype.ext ?_⟩
    simpa only [mul_comm] using hu

def idealElementCoordinates : (EisensteinIdealExponent × Eisensteinˣ) ≃
    {a : Eisenstein // a ≠ 0} := Equiv.ofBijective _ idealElementCoordinates_bijective

lemma idealElementCoordinates_norm (x : EisensteinIdealExponent × Eisensteinˣ) :
    norm (idealElementCoordinates x).val = idealExponentNorm x.1 := by
  change norm ((x.2:Eisenstein)*idealExponentGenerator x.1) = _
  rw [← normNat_cast,normNat_mul,normNat_of_isUnit x.2.isUnit]
  simp only [Nat.one_mul]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PublishedPrimitiveHecke
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The classical primitive Hecke input on the actual finite residue
characters constructed here. Completion/functional equation: Watkins
(2011), §3.6, p.123; entire order-one completion: Thorner–Zaman (2019),
§2C, p.1049, Eq.(2-15). This is a conditional input, not an axiom.
No character sum estimate or new-paper conclusion is included. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma residueHeckeScale_pos {q : Eisenstein} (hq : q ≠ 0) : 0 < residueHeckeScale q := by
  unfold residueHeckeScale
  positivity [norm_pos_of_ne_zero hq,Real.pi_pos]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueGaussianScale
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact self-dual normalization of the finite-character Gaussian. -/
noncomputable section
namespace CubicFirstMoment

lemma residueHeckeScale_squared (q : Eisenstein) :
    4*Real.pi^2*(residueHeckeScale q)^2 = 3*norm q := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold residueHeckeScale
  rw [div_pow,Real.sq_sqrt (mul_nonneg (by norm_num) (norm_nonneg q))]
  field_simp
  ring

lemma residueGaussian_prefactor {q : Eisenstein} (hq : q ≠ 0)
    {t : ℝ} (ht : 0 < t) :
    (2/(Real.sqrt 3*norm q))*(Real.pi/(t/residueHeckeScale q)) =
      1/(Real.sqrt (norm q)*t) := by
  have hN := norm_pos_of_ne_zero hq
  have hsN : Real.sqrt (norm q) ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
  have hs3 : Real.sqrt (3:ℝ) ≠ 0 := by positivity
  unfold residueHeckeScale
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
  field_simp [ht.ne',hsN,hs3,Real.pi_ne_zero]
  nlinarith [Real.sq_sqrt hN.le]

lemma residueGaussian_exponent {q : Eisenstein} (hq : q ≠ 0)
    {t : ℝ} (ht : 0 < t) (h : Eisenstein) :
    -4*Real.pi^2/(t/residueHeckeScale q)*Complex.normSq ((h:ℂ)/((q:ℂ)*traceLambda)) =
      -norm h/(residueHeckeScale q*t) := by
  have hN := (norm_pos_of_ne_zero hq).ne'
  have hA := (residueHeckeScale_pos hq).ne'
  have hs := residueHeckeScale_squared q
  rw [Complex.normSq_div,Complex.normSq_mul,traceLambda_normSq]
  change -4*Real.pi^2/(t/residueHeckeScale q)*(norm h/(norm q*3)) = _
  field_simp
  nlinarith [congrArg (fun x : ℝ => x*norm h) hs]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrincipalLatticeTheta
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Poisson inversion of the principal lattice Gaussian, with its zero
term retained. This supplies the pole term of the principal ideal zeta
function rather than treating it as a nonprincipal Hecke function. -/
noncomputable section
namespace CubicFirstMoment

def principalLatticeTheta (t : ℝ) : ℂ :=
  ∑' a : Eisenstein, (Real.exp (-norm a*t/residueHeckeScale 1):ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrincipalIdealTheta
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The principal theta function includes the zero vector. Its exact
unit multiplicity gives the inhomogeneous transformation of the ideal
theta sum and therefore the principal zeta pole. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma principalIdealTheta_nonzero {A t : ℝ} (hA : 0 < A) (ht : 0 < t) :
    (∑' a : {a : Eisenstein // a ≠ 0}, (Real.exp (-norm a.val*t/A):ℂ))=
      (Nat.card (Eisensteinˣ):ℂ)*idealTheta A (fun _ => 1) t := by
  let : Finite (Eisensteinˣ) := idealTheta_units_finite
  let : Fintype (Eisensteinˣ) := Fintype.ofFinite _
  let f : EisensteinIdealExponent → ℂ := fun ν => (Real.exp (-idealExponentNorm ν*t/A):ℂ)
  have hf : Summable f := by
    simpa only [one_mul] using idealTheta_summable hA ht (fun _ => 1) (by simp)
  have hp : Summable (fun x : EisensteinIdealExponent × Eisensteinˣ => f x.1) := by
    simpa only [mul_one] using summable_mul_of_summable_norm
      (g := fun _ : Eisensteinˣ => (1:ℂ)) hf.norm (hasSum_fintype _).summable
  rw [←idealElementCoordinates.tsum_eq]
  simp_rw [idealElementCoordinates_norm]
  change (∑' x : EisensteinIdealExponent × Eisensteinˣ, f x.1)=_
  rw [hp.tsum_prod' (fun _ => (hasSum_fintype _).summable)]
  simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [tsum_mul_left]
  simp only [Nat.card_eq_fintype_card,idealTheta,one_mul]
  rfl

lemma principalLatticeTheta_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun a : Eisenstein => (Real.exp (-norm a*t/residueHeckeScale 1):ℂ)) := by
  have hA := residueHeckeScale_pos (q := 1) one_ne_zero
  have h := schwartz_summable_eisenstein
    (radialGaussianSchwartz (t/residueHeckeScale 1) (div_pos ht hA))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext a
  rw [radialGaussianSchwartz_apply]
  change (Real.exp (-Complex.normSq (a:ℂ)*t/residueHeckeScale 1):ℂ)=
    (Real.exp (-(t/residueHeckeScale 1)*‖(a:ℂ)‖^2):ℂ)
  rw [Complex.normSq_eq_norm_sq]
  congr 2
  ring

lemma principalLatticeTheta_eq_ideal {t : ℝ} (ht : 0 < t) :
    principalLatticeTheta t=1+(Nat.card (Eisensteinˣ):ℂ)*
      idealTheta (residueHeckeScale 1) (fun _ => 1) t := by
  classical
  have h := (principalLatticeTheta_summable ht).tsum_eq_add_tsum_ite 0
  have hzero : (Real.exp (-norm (0:Eisenstein)*t/residueHeckeScale 1):ℂ)=1 := by
    norm_num [norm]
  rw [hzero] at h
  rw [principalLatticeTheta,h,←principalIdealTheta_nonzero
    (residueHeckeScale_pos (q := 1) one_ne_zero) ht]
  congr 1
  calc
    _ = ∑' a : Eisenstein, Set.indicator {a : Eisenstein | a ≠ 0}
        (fun a => (Real.exp (-norm a*t/residueHeckeScale 1):ℂ)) a := by
      apply tsum_congr
      intro a
      by_cases ha : a=0 <;> simp [ha,Set.indicator]
    _ = _ := (tsum_subtype {a : Eisenstein | a ≠ 0}
      (fun a => (Real.exp (-norm a*t/residueHeckeScale 1):ℂ))).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmetic
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized arithmetic coefficient of DR v3 (5.7), indexed on the
common cusp lattice lambda^-4 Z[omega]. The coefficient used in the
Whittaker series is tau(mu)/|mu|. No modular transformation is asserted. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaArithmeticCoefficient (n : Eisenstein) : ℂ :=
  if h : Nonempty (CubicThetaCoordinates n) then (Classical.choice h).coefficient else 0

/-- Uniqueness makes the explicit formula independent of the chosen
coordinate witness. -/
lemma cubicThetaArithmeticCoefficient_formula {n : Eisenstein} (R : CubicThetaCoordinates n) :
    cubicThetaArithmeticCoefficient n = R.coefficient := by
  unfold cubicThetaArithmeticCoefficient
  rw [dite_eq_left (show Nonempty (CubicThetaCoordinates n) from ⟨R⟩),(Classical.choice (show Nonempty (CubicThetaCoordinates n) from ⟨R⟩)).unique R]

lemma cubicThetaArithmeticCoefficient_norm_le (n : Eisenstein) :
    ‖cubicThetaArithmeticCoefficient n‖ ≤ 81 := by
  unfold cubicThetaArithmeticCoefficient
  split_ifs with h
  · exact (Classical.choice h).coefficient_norm_le
  · norm_num

lemma cubicThetaArithmeticCoefficient_bound (n : Eisenstein) (hn : n ≠ 0) :
    ‖cubicThetaArithmeticCoefficient n‖ ≤ 81*norm n :=
  (cubicThetaArithmeticCoefficient_norm_le n).trans
    (le_mul_of_one_le_right (by norm_num) (one_le_norm hn))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEven
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The evenness of the cubic theta coefficients, derived directly from
all cases of the arithmetic formula, and the resulting horizontal symmetry. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaArithmeticCoefficient_even (n : Eisenstein) :
    cubicThetaArithmeticCoefficient (-n) = cubicThetaArithmeticCoefficient n := by
  by_cases hn : Nonempty (CubicThetaCoordinates n)
  · let R := Classical.choice hn
    rw [cubicThetaArithmeticCoefficient_formula R.neg,cubicThetaArithmeticCoefficient_formula R,
      R.neg_coefficient]
  · have hneg : ¬Nonempty (CubicThetaCoordinates (-n)) := by
      rintro ⟨R⟩
      apply hn
      simpa only [neg_neg] using (show Nonempty (CubicThetaCoordinates (-(-n))) from ⟨R.neg⟩)
    simp only [cubicThetaArithmeticCoefficient,dite_eq_right hn,dite_eq_right hneg]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact primary cube coefficients isolated in DR v3 (5.17).
This connects the constructed theta expansion to the completed Gauss sum. -/
noncomputable section
namespace CubicFirstMoment

/-- The primary frequency lambda^-3*c*d^3 has no unit phase and has the
normalized conjugate Gauss coefficient of the original cubic sum. -/
lemma cubicThetaArithmeticCoefficient_primary {c d : Eisenstein}
    (hc : primary c) (hd : primary d) (hs : Squarefree c) :
    cubicThetaArithmeticCoefficient (lambdaE*c*d^3) =
      ((81/(Real.sqrt (norm c)*norm d):ℝ):ℂ)*star (gauss c) := by
  let R : CubicThetaCoordinates (lambdaE*c*d^3) := {
    unit := 1
    order := 1
    squarefreePart := c
    cubePart := d
    squarefree_primary := hc
    cube_primary := hd
    squarefree := hs
    numerator_eq := by simp [mul_assoc] }
  rw [cubicThetaArithmeticCoefficient_formula R]
  norm_num [R,CubicThetaCoordinates.coefficient,CubicThetaCoordinates.amplitude]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSieveProjection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The primary cubic Gauss coefficients are the exact finite additive
projection of the conjugate cubic theta expansion. No transformation under
inversion is used in this arithmetic sieving step. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaConjugateCoefficient (n : Eisenstein) : ℂ := star (cubicThetaArithmeticCoefficient n)

def cubicThetaSelectedCoefficient (n : Eisenstein) : ℂ :=
  if cubicThetaPrimarySupport n then cubicThetaConjugateCoefficient n else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFullRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primitive rows of the full Eisenstein modular group. Their proper
height function gives the full-group reduction needed for a finite cusp
cover of the principal level-three quotient. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaPrimitiveRow_height (g : SL(2,Eisenstein)) (p : ℂ × ℝ) :
    (cubicThetaPrimitiveRow g).height p=(cubicThetaMobius (cubicThetaFullComplex g) p).2 := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryPeriodicity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The base theta series has the smaller period lattice 3 Z[omega].
This follows from its actual ramified support, and supplies the upper
unipotent stabilizer for the principal level-three group. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaArithmeticCoefficient_lambda_dvd {n : Eisenstein}
    (hn : cubicThetaArithmeticCoefficient n ≠ 0) : lambdaE ∣ n := by
  unfold cubicThetaArithmeticCoefficient at hn
  split_ifs at hn with h
  · let R := Classical.choice h
    have hR : R.coefficient ≠ 0 := hn
    have ho : 0 < R.order := by
      unfold CubicThetaCoordinates.coefficient at hR
      split_ifs at hR with h0 h1
      · omega
      · have hm := h1.1
        omega
      · exact False.elim (hR rfl)
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ho)
    refine ⟨(R.unit:Eisenstein)*lambdaE^k*(R.squarefreePart*R.cubePart^3),?_⟩
    calc
      n = (R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*R.cubePart^3) := R.numerator_eq
      _ = _ := by rw [hk,pow_succ]; ring
  · exact False.elim (hn rfl)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspRowTransport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual primitive bottom rows transported into an arbitrary integral
cusp. The row map remains injective and preserves the literal height. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaCuspRow (δ : SL(2,Eisenstein)) (r : CubicThetaBottomRow) : CubicThetaPrimitiveRow :=
  cubicThetaPrimitiveRow (r.completion.val*δ)

lemma cubicThetaCuspRow_coordinates (δ : SL(2,Eisenstein)) (r : CubicThetaBottomRow) :
    (cubicThetaCuspRow δ r).c=r.c*δ 0 0+r.d*δ 1 0 ∧
    (cubicThetaCuspRow δ r).d=r.c*δ 0 1+r.d*δ 1 1 := by
  have hc := congrArg CubicThetaBottomRow.c r.completion_row
  have hd := congrArg CubicThetaBottomRow.d r.completion_row
  change r.completion.val 1 0=r.c at hc
  change r.completion.val 1 1=r.d at hd
  simp only [cubicThetaCuspRow,cubicThetaPrimitiveRow,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply,Fin.sum_univ_two,hc,hd]
  exact ⟨trivial,trivial⟩

lemma cubicThetaCuspRow_injective (δ : SL(2,Eisenstein)) :
    Function.Injective (cubicThetaCuspRow δ) := by
  intro r t h
  have hu : IsUnit (δ.val) := (Group.isUnit δ).map Matrix.SpecialLinearGroup.coeMonoidHom
  have hv : ![r.c,r.d] ᵥ* δ.val=![t.c,t.d] ᵥ* δ.val := by
    apply funext
    intro j
    fin_cases j
    · simpa [Matrix.vecMul,dotProduct,Fin.sum_univ_two,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.head_cons,Matrix.head_fin_const] using
        ((cubicThetaCuspRow_coordinates δ r).1.symm.trans
          ((congrArg CubicThetaPrimitiveRow.c h).trans (cubicThetaCuspRow_coordinates δ t).1))
    · simpa [Matrix.vecMul,dotProduct,Fin.sum_univ_two,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.head_cons,Matrix.head_fin_const] using
        ((cubicThetaCuspRow_coordinates δ r).2.symm.trans
          ((congrArg CubicThetaPrimitiveRow.d h).trans (cubicThetaCuspRow_coordinates δ t).2))
  have he := Matrix.vecMul_injective_of_isUnit hu hv
  exact CubicThetaBottomRow.ext (congrFun he 0) (congrFun he 1)

lemma cubicThetaCuspRow_height (δ : SL(2,Eisenstein)) (r : CubicThetaBottomRow)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    (cubicThetaCuspRow δ r).height p=
      r.height (cubicThetaMobius (cubicThetaFullComplex δ) p) := by
  rw [cubicThetaCuspRow,cubicThetaPrimitiveRow_height,map_mul,← cubicThetaMobius_comp _ _ hp]
  have he : cubicThetaFullComplex r.completion.val=cubicThetaPrincipalComplex r.completion := rfl
  rw [he,← cubicThetaBottomRow_height,r.completion_row]

lemma cubicThetaCuspRow_height_zero_c {r : CubicThetaPrimitiveRow} (hc : r.c=0)
    (p : ℂ × ℝ) : r.height p=p.2 := by
  have hu : IsUnit r.d := isCoprime_zero_left.mp (hc ▸ r.coprime)
  simp only [CubicThetaPrimitiveRow.height,CubicThetaPrimitiveRow.denominator,hc,
    ZeroMemClass.coe_zero,zero_mul,zero_add,norm,Complex.normSq_zero]
  rw [show Complex.normSq (r.d:ℂ)=1 from norm_of_isUnit hu,add_zero,div_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticRemainder
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal arithmetic difference between Eisenstein and incoming
series, with its absolutely convergent row expansion and all-cusp bound. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaRemainderRow_cusp_zero (δ : Matrix.SpecialLinearGroup (Fin 2) Eisenstein)
    (r : CubicThetaBottomRow) {p : ℂ × ℝ} (hp : 0<p.2) (hv : 2≤p.2)
    (s : ℂ) (hc : (cubicThetaCuspRow δ r).c=0) :
    cubicThetaRemainderRow r (cubicThetaMobius (cubicThetaFullComplex δ) p) s=0 := by
  have hh := cubicThetaCuspRow_height δ r hp
  rw [cubicThetaCuspRow_height_zero_c hc] at hh
  unfold cubicThetaRemainderRow
  rw [← hh,cubicThetaCuspCutoff_one hv,sub_self,zero_mul]

lemma cubicThetaRemainderRow_cusp_bound (δ : Matrix.SpecialLinearGroup (Fin 2) Eisenstein)
    (r : CubicThetaBottomRow) (z : ℂ) {v R : ℝ} (hv : 2≤v)
    (hz : Complex.normSq z≤R) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖cubicThetaRemainderRow r (cubicThetaMobius (cubicThetaFullComplex δ) (z,v)) s‖≤
      (2*(3+2*R)^2*v^(4-s.re))*
        (norm (cubicThetaCuspRow δ r).c)^(-(s.re-2))*
          (1+norm (cubicThetaCuspRow δ r).d)^(-2:ℝ) := by
  have hv0 : 0<v := by linarith
  have hnc := norm_nonneg (cubicThetaCuspRow δ r).c
  have hnd := norm_nonneg (cubicThetaCuspRow δ r).d
  by_cases hc : (cubicThetaCuspRow δ r).c=0
  · rw [cubicThetaRemainderRow_cusp_zero δ r (p:=(z,v)) hv0 hv s hc,norm_zero]
    positivity
  · have hb := cubicThetaRemainderRow_norm r
      (cubicThetaMobius_height_pos (cubicThetaFullComplex δ) (p:=(z,v)) hv0) s
    rw [← cubicThetaCuspRow_height δ r (p:=(z,v)) hv0] at hb
    have h := cubicThetaCuspRowHeight_power hc (cubicThetaCuspRow δ r).d z
      (by linarith : 1≤v) hz hs
    exact hb.trans ((mul_le_mul_of_nonneg_left h (by norm_num)).trans_eq (by ring))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticSection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The arithmetic Eisenstein-minus-incoming difference is a genuine
continuous automorphic section in the initial convergence half-plane. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaArithmeticSection (s : ℂ) (hs : 2 < s.re) : CubicThetaSection :=
  ⟨⟨fun p => cubicThetaArithmeticRemainder p.val s,by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (cubicThetaArithmeticRemainder_continuousAt hs p.property).comp
      continuous_subtype_val.continuousAt⟩,by
    intro g p
    exact cubicThetaArithmeticRemainder_automorphy g p.property s⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspRemainderBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute lattice summation gives a uniform bound for the literal
Eisenstein-minus-incoming remainder in every integral cusp. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaArithmeticRemainder_cusp_bound
    (δ : Matrix.SpecialLinearGroup (Fin 2) Eisenstein) (z : ℂ)
    {v R : ℝ} (hv : 2≤v) (hz : Complex.normSq z≤R) {s : ℂ} (hs : 3 < s.re) :
    ‖cubicThetaArithmeticRemainder (cubicThetaMobius (cubicThetaFullComplex δ) (z,v)) s‖≤
      cubicThetaCuspRemainderConstant s R*v^(4-s.re) := by
  have hv0 : 0<v := by linarith
  let F : Eisenstein × Eisenstein → ℝ := fun cd =>
    (norm cd.1)^(-(s.re-2))*(1+norm cd.2)^(-2:ℝ)
  have hc := summable_eisenstein_norm_rpow (show 1 < s.re-2 by linarith)
  have hd := summable_eisenstein_one_add_norm (by norm_num : (1:ℝ)<2)
  have hF : Summable F := summable_mul_of_summable_norm hc.norm hd.norm
  have hF0 (cd : Eisenstein × Eisenstein) : 0≤F cd :=
    mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg (by linarith [norm_nonneg cd.2]) _)
  let j : CubicThetaBottomRow → Eisenstein × Eisenstein :=
    fun r => ((cubicThetaCuspRow δ r).c,(cubicThetaCuspRow δ r).d)
  have hj : Function.Injective j := by
    intro r t h
    exact cubicThetaCuspRow_injective δ
      (CubicThetaPrimitiveRow.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  let K : ℝ := 2*(3+2*R)^2*v^(4-s.re)
  have hK : 0≤K := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (Real.rpow_nonneg hv0.le _)
  have hM : Summable (fun cd => K*F cd) := hF.mul_left K
  have hmr : Summable (fun r => K*F (j r)) := hM.comp_injective hj
  have hb (r : CubicThetaBottomRow) :
      ‖cubicThetaRemainderRow r (cubicThetaMobius (cubicThetaFullComplex δ) (z,v)) s‖≤K*F (j r) := by
    simpa only [K,F,j,mul_assoc] using cubicThetaRemainderRow_cusp_bound δ r z hv hz
      (show 2 ≤ s.re by linarith)
  have hsum := cubicThetaRemainderRow_summable (cubicThetaMobius_height_pos (p := (z,v)) (cubicThetaFullComplex δ) hv0)
    (show 2 < s.re by linarith)
  rw [cubicThetaArithmeticRemainder_eq_sum (cubicThetaMobius_height_pos (p := (z,v)) (cubicThetaFullComplex δ) hv0)
    (show 2 < s.re by linarith)]
  calc
    _ ≤ ∑' r, ‖cubicThetaRemainderRow r (cubicThetaMobius (cubicThetaFullComplex δ) (z,v)) s‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' r, K*F (j r) := Summable.tsum_le_tsum hb hsum.norm hmr
    _ ≤ ∑' cd, K*F cd := tsum_comp_le_tsum_of_inj hM (fun cd => mul_nonneg hK (hF0 cd)) hj
    _ = K*((∑' c : Eisenstein, (norm c)^(-(s.re-2)))*
        (∑' d : Eisenstein, (1+norm d)^(-2:ℝ))) := by
      rw [tsum_mul_left,← hc.tsum_mul_tsum hd hF]
    _ = _ := by unfold K cubicThetaCuspRemainderConstant; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspLatticeWeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The summable lattice weight controlling both values and first
spatial derivatives of the arithmetic remainder in each cusp. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaCuspLatticeWeight (δ : SL(2,Eisenstein)) (s : ℂ) (r : CubicThetaBottomRow) : ℝ :=
  norm (cubicThetaCuspRow δ r).c^(-(s.re-2))*(1+norm (cubicThetaCuspRow δ r).d)^(-2:ℝ)

lemma cubicThetaCuspLatticeWeight_nonneg (δ : SL(2,Eisenstein)) (s : ℂ) (r : CubicThetaBottomRow) :
    0 ≤ cubicThetaCuspLatticeWeight δ s r :=
  mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
    (Real.rpow_nonneg (by linarith [norm_nonneg (cubicThetaCuspRow δ r).d]) _)

def rowIndex (δ : SL(2,Eisenstein)) (r : CubicThetaBottomRow) : Eisenstein × Eisenstein :=
  ((cubicThetaCuspRow δ r).c,(cubicThetaCuspRow δ r).d)

lemma rowIndex_injective (δ : SL(2,Eisenstein)) : Function.Injective (rowIndex δ) := by
  intro r t he
  exact cubicThetaCuspRow_injective δ
    (CubicThetaPrimitiveRow.ext (congrArg Prod.fst he) (congrArg Prod.snd he))

lemma cubicThetaCuspLatticeWeight_summable (δ : SL(2,Eisenstein)) {s : ℂ} (hs : 3 < s.re) :
    Summable (cubicThetaCuspLatticeWeight δ s) := by
  change Summable (fun r => pairWeight s (rowIndex δ r))
  exact (pairWeight_summable hs).comp_injective (rowIndex_injective δ)

lemma cubicThetaCuspLatticeWeight_tsum_le (δ : SL(2,Eisenstein)) {s : ℂ} (hs : 3 < s.re) :
    (∑' r, cubicThetaCuspLatticeWeight δ s r) ≤ cubicThetaCuspLatticeMass s := by
  have hc := summable_eisenstein_norm_rpow (show 1 < s.re-2 by linarith)
  have hd := summable_eisenstein_one_add_norm (by norm_num : (1:ℝ)<2)
  have h := pairWeight_summable hs
  have hn (cd : Eisenstein × Eisenstein) : 0≤pairWeight s cd :=
    mul_nonneg (Real.rpow_nonneg (norm_nonneg cd.1) _)
      (Real.rpow_nonneg (by linarith [norm_nonneg cd.2]) _)
  have hb := tsum_comp_le_tsum_of_inj h hn (rowIndex_injective δ)
  have hm : (∑' cd, pairWeight s cd)=cubicThetaCuspLatticeMass s :=
    (hc.tsum_mul_tsum hd h).symm
  exact hb.trans_eq hm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimitivePower
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primitive row powers in every cusp obey the same coordinate and
joint derivative bounds as the original Eisenstein rows. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

def cubicThetaPrimitivePower (r : CubicThetaPrimitiveRow) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  (r.height p:ℂ)^s

lemma cubicThetaPrimitivePower_contDiffAt (r : CubicThetaPrimitiveRow) (s : ℂ)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContDiffAt ℝ ∞ (fun q => cubicThetaPrimitivePower r q s) p := by
  obtain ⟨g,rfl⟩ := cubicThetaPrimitiveRow_surjective r
  have hh : ContDiffAt ℝ ∞ (fun q => (cubicThetaPrimitiveRow g).height q) p := by
    simp only [cubicThetaPrimitiveRow_height]
    exact contDiffAt_snd.comp p (cubicThetaMobius_contDiffAt _ hp)
  exact (cubicThetaHeightPower_analytic s ((cubicThetaPrimitiveRow g).height_pos hp)).contDiffAt.comp p hh

lemma cubicThetaPrimitivePower_cartesian (r : CubicThetaPrimitiveRow) (hc : r.c≠0)
    (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaPrimitivePower r (cubicThetaCartesianPoint x y v) s=
      (norm r.c:ℂ)^(-s)*cubicThetaCartesianKernel s
        (x+((r.d:ℂ)/(r.c:ℂ)).re) (y+((r.d:ℂ)/(r.c:ℂ)).im) v := by
  unfold cubicThetaPrimitivePower CubicThetaPrimitiveRow.height CubicThetaPrimitiveRow.denominator
  rw [cubicThetaRowRadius_complex_power hc (p:=cubicThetaCartesianPoint x y v) hv,
    cubicThetaRowRadius_cartesian]
  rw [show (cubicThetaCartesianPoint x y v).2=v from rfl,cubicTheta_row_power hv hc]
  unfold cubicThetaCartesianKernel
  ring

lemma cubicThetaPrimitivePower_jetBound (r : CubicThetaPrimitiveRow) (s : ℂ)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    CubicThetaCoordinateJetBound
      (fun a b t => cubicThetaPrimitivePower r (cubicThetaCartesianPoint a b t) s) s x y v := by
  by_cases hc : r.c=0
  · have he : (fun a b t => cubicThetaPrimitivePower r (cubicThetaCartesianPoint a b t) s)=
        (fun (_ _ t : ℝ) => (t:ℂ)^s) := by
      funext a b t
      simp only [cubicThetaPrimitivePower,cubicThetaCuspRow_height_zero_c hc,cubicThetaCartesianPoint]
    rw [he]
    exact cubicThetaHeightPower_jetBound s x y hv
  · exact cubicThetaCoordinateJetBound_congr
      (fun a b t ht => cubicThetaPrimitivePower_cartesian r hc s a b ht) hv
      (cubicThetaCoordinateJetBound_translate ((norm r.c:ℂ)^(-s))
        ((r.d:ℂ)/(r.c:ℂ)).re ((r.d:ℂ)/(r.c:ℂ)).im x y v
        (cubicThetaCartesian_jetBound s _ _ hv))

lemma cubicThetaPrimitivePower_fderiv_bound (r : CubicThetaPrimitiveRow) (s : ℂ)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ‖fderiv ℝ (fun q => cubicThetaPrimitivePower r q s) p‖≤
      3*(‖cubicThetaPrimitivePower r p s‖*(cubicThetaFirstJetConstant s/p.2)) := by
  have he : cubicThetaCartesianPoint p.1.re p.1.im p.2=p := by
    apply Prod.ext
    · exact Complex.re_add_im p.1
    · rfl
  have hd := (cubicThetaPrimitivePower_contDiffAt r s hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hc := cubicThetaFDeriv_coordinates p.1.re p.1.im p.2 (he ▸ hd)
  rw [he] at hc
  have hj := cubicThetaPrimitivePower_jetBound r s p.1.re p.1.im hp
  apply cubicThetaComplexProduct_opNorm_le _
    (mul_nonneg (_root_.norm_nonneg _) (div_nonneg (cubicThetaJetConstants_nonneg s).1 hp.le))
  · rw [hc.1]
    simpa only [he,cubicThetaAxisFunction,cubicThetaCoordinateCenter] using (hj .x).1
  · rw [hc.2.1]
    simpa only [he,cubicThetaAxisFunction,cubicThetaCoordinateCenter] using (hj .y).1
  · rw [hc.2.2]
    simpa only [he,cubicThetaAxisFunction,cubicThetaCoordinateCenter] using (hj .height).1

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHighCuspRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! In a high cusp, the incoming term cancels precisely the constant
rows. The remaining literal terms are smooth primitive height powers. -/
noncomputable section
open scoped MatrixGroups ContDiff
namespace CubicFirstMoment

def cubicThetaHighCuspRow (δ : SL(2,Eisenstein)) (r : CubicThetaBottomRow)
    (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  if (cubicThetaCuspRow δ r).c=0 then 0
  else star r.phase*cubicThetaPrimitivePower (cubicThetaCuspRow δ r) p s

lemma cubicThetaHighCuspRow_eq (δ : SL(2,Eisenstein)) (r : CubicThetaBottomRow)
    {p : ℂ × ℝ} (hp : 2≤p.2) (s : ℂ) :
    cubicThetaHighCuspRow δ r p s=
      cubicThetaRemainderRow r (cubicThetaMobius (cubicThetaFullComplex δ) p) s := by
  have hp0 : 0<p.2 := by linarith
  classical
  by_cases hc : (cubicThetaCuspRow δ r).c=0
  · rw [cubicThetaHighCuspRow,ite_eq_left hc,cubicThetaRemainderRow_cusp_zero δ r hp0 hp s hc]
  · have hh : (cubicThetaCuspRow δ r).height p≤1 := by
      apply le_of_not_gt
      intro h
      apply hc
      exact cubicThetaMobius_high_overlap (r.completion.val*δ) (by linarith)
        (by rwa [← cubicThetaPrimitiveRow_height])
    rw [cubicThetaHighCuspRow,ite_eq_right hc,cubicThetaRemainderRow,
      ← cubicThetaCuspRow_height δ r hp0,cubicThetaCuspCutoff_zero hh,sub_zero,one_mul]
    change star r.phase*((cubicThetaCuspRow δ r).height p:ℂ)^s=
      star r.phase*(r.height (cubicThetaMobius (cubicThetaFullComplex δ) p):ℂ)^s
    rw [cubicThetaCuspRow_height δ r hp0]

lemma cubicThetaHighCuspRow_contDiffAt (δ : SL(2,Eisenstein)) (r : CubicThetaBottomRow)
    (s : ℂ) {p : ℂ × ℝ} (hp : 0<p.2) :
    ContDiffAt ℝ ∞ (fun q => cubicThetaHighCuspRow δ r q s) p := by
  classical
  unfold cubicThetaHighCuspRow
  split_ifs
  · exact contDiffAt_const
  · exact contDiffAt_const.mul (cubicThetaPrimitivePower_contDiffAt _ s hp)

lemma cubicThetaHighCuspRow_fderiv_bound (δ : SL(2,Eisenstein)) (r : CubicThetaBottomRow)
    (s : ℂ) {p : ℂ × ℝ} (hp : 0<p.2) :
    ‖fderiv ℝ (fun q => cubicThetaHighCuspRow δ r q s) p‖≤
      3*(‖cubicThetaHighCuspRow δ r p s‖*(cubicThetaFirstJetConstant s/p.2)) := by
  classical
  by_cases hc : (cubicThetaCuspRow δ r).c=0
  · simp only [cubicThetaHighCuspRow,ite_eq_left hc,fderiv_const_apply,norm_zero,zero_mul,mul_zero,le_refl]
  · have hdP := (cubicThetaPrimitivePower_contDiffAt (cubicThetaCuspRow δ r) s hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    have hd := hdP.hasFDerivAt.const_mul (star r.phase)
    simp only [cubicThetaHighCuspRow,ite_eq_right hc]
    rw [hd.fderiv,norm_smul,norm_star,r.phase_norm,one_mul,norm_mul,norm_star,r.phase_norm,one_mul]
    exact cubicThetaPrimitivePower_fderiv_bound _ s hp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHighCuspDerivativeBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual high-cusp row derivatives have a summable lattice
majorant, with one inverse height gained by differentiation. -/
noncomputable section
open Set Filter
open scoped MatrixGroups Topology
namespace CubicFirstMoment

lemma cubicThetaHighCuspRow_fderiv_lattice_bound
    (δ : SL(2,Eisenstein)) (r : CubicThetaBottomRow) {p : ℂ × ℝ} {R : ℝ}
    (hp : 2≤p.2) (hR : Complex.normSq p.1≤R) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖fderiv ℝ (fun q => cubicThetaHighCuspRow δ r q s) p‖≤
      (6*(3+2*R)^2*cubicThetaFirstJetConstant s*p.2^(3-s.re))*cubicThetaCuspLatticeWeight δ s r := by
  have hp0 : 0<p.2 := by linarith
  have hd := cubicThetaHighCuspRow_fderiv_bound δ r s hp0
  rw [cubicThetaHighCuspRow_eq δ r hp s] at hd
  have hb := cubicThetaRemainderRow_cusp_bound δ r p.1 hp hR hs
  have hJ : 0 ≤ cubicThetaFirstJetConstant s/p.2 := div_nonneg (cubicThetaJetConstants_nonneg s).1 hp0.le
  have he : p.2^(4-s.re)/p.2=p.2^(3-s.re) := by
    rw [← Real.rpow_sub_one hp0.ne']
    congr 1
    ring
  calc
    _ ≤ 3*(‖cubicThetaRemainderRow r (cubicThetaMobius (cubicThetaFullComplex δ) p) s‖*
        (cubicThetaFirstJetConstant s/p.2)) := hd
    _ ≤ 3*(((2*(3+2*R)^2*p.2^(4-s.re))*
        norm (cubicThetaCuspRow δ r).c^(-(s.re-2))*(1+norm (cubicThetaCuspRow δ r).d)^(-2:ℝ))*
        (cubicThetaFirstJetConstant s/p.2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb hJ) (by norm_num)
    _ = (6*(3+2*R)^2*cubicThetaFirstJetConstant s*cubicThetaCuspLatticeWeight δ s r)*
        (p.2^(4-s.re)/p.2) := by unfold cubicThetaCuspLatticeWeight; ring
    _ = _ := by rw [he]; ring

lemma cubicThetaHighCuspRow_local_fderiv_bound
    (δ : SL(2,Eisenstein)) {s : ℂ} (hs : 3 < s.re) {p : ℂ × ℝ} (hp : 2<p.2) :
    ∃ r : ℝ, 0 < r ∧ ∃ u : CubicThetaBottomRow → ℝ, Summable u ∧
      ∀ b q, q∈Metric.ball p r → 2<q.2 ∧
        ‖fderiv ℝ (fun z => cubicThetaHighCuspRow δ b z s) q‖≤u b := by
  let R := Complex.normSq p.1+1
  let H := p.2^(3-s.re)+1
  have hp0 : 0<p.2 := by linarith
  have hN : ContinuousAt (fun q : ℂ × ℝ => Complex.normSq q.1) p :=
    Complex.continuous_normSq.continuousAt.comp continuousAt_fst
  have hV : ContinuousAt (fun q : ℂ × ℝ => q.2^(3-s.re)) p :=
    continuousAt_snd.rpow_const (Or.inl hp0.ne')
  have hU : {q : ℂ × ℝ | 2<q.2 ∧ Complex.normSq q.1<R ∧ q.2^(3-s.re)<H}∈𝓝 p :=
    (continuous_snd.continuousAt.eventually_const_lt hp).and
      ((hN.eventually_lt_const (by dsimp [R]; linarith)).and
        (hV.eventually_lt_const (by dsimp [H]; linarith)))
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hU
  let C := 6*(3+2*R)^2*cubicThetaFirstJetConstant s
  have hC : 0≤C := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (cubicThetaJetConstants_nonneg s).1
  let u := fun b => (C*H)*cubicThetaCuspLatticeWeight δ s b
  refine ⟨r,hr,u,(cubicThetaCuspLatticeWeight_summable δ hs).mul_left _,?_⟩
  intro b q hq
  obtain ⟨hqv,hqR,hqH⟩ := hsub hq
  refine ⟨hqv,?_⟩
  have hd := cubicThetaHighCuspRow_fderiv_lattice_bound δ b hqv.le hqR.le (by linarith : 2 ≤ s.re)
  exact hd.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqH.le hC)
    (cubicThetaCuspLatticeWeight_nonneg δ s b))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHighCuspDifferentiation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaBottomRow_countable _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiate the exact high-cusp expansion of the arithmetic
remainder. The derivative bound is obtained from a summable majorant. -/
noncomputable section
open Set Filter
open scoped MatrixGroups Topology
namespace CubicFirstMoment

lemma cubicThetaHighCuspRow_sum (δ : SL(2,Eisenstein)) {p : ℂ × ℝ}
    (hp : 2≤p.2) {s : ℂ} (hs : 2 < s.re) :
    cubicThetaArithmeticRemainder (cubicThetaMobius (cubicThetaFullComplex δ) p) s=
      ∑' r, cubicThetaHighCuspRow δ r p s := by
  rw [cubicThetaArithmeticRemainder_eq_sum
    (cubicThetaMobius_height_pos (cubicThetaFullComplex δ) (by linarith : 0<p.2)) hs]
  exact tsum_congr (fun r => (cubicThetaHighCuspRow_eq δ r hp s).symm)

lemma cubicThetaHighCuspRow_sum_summable (δ : SL(2,Eisenstein)) {p : ℂ × ℝ}
    (hp : 2≤p.2) {s : ℂ} (hs : 2 < s.re) :
    Summable (fun r => cubicThetaHighCuspRow δ r p s) :=
  (cubicThetaRemainderRow_summable
    (cubicThetaMobius_height_pos (cubicThetaFullComplex δ) (by linarith : 0<p.2)) hs).congr
    (fun r => (cubicThetaHighCuspRow_eq δ r hp s).symm)

lemma cubicThetaHighCusp_fderiv_eq (δ : SL(2,Eisenstein)) {s : ℂ} (hs : 3 < s.re)
    {p : ℂ × ℝ} (hp : 2<p.2) :
    Summable (fun r => fderiv ℝ (fun q => cubicThetaHighCuspRow δ r q s) p) ∧
      fderiv ℝ (fun q => cubicThetaArithmeticRemainder
        (cubicThetaMobius (cubicThetaFullComplex δ) q) s) p=
        ∑' r, fderiv ℝ (fun q => cubicThetaHighCuspRow δ r q s) p := by
  obtain ⟨ρ,hρ,u,hu,hb⟩ := cubicThetaHighCuspRow_local_fderiv_bound δ hs hp
  have hpB : p∈Metric.ball p ρ := Metric.mem_ball_self hρ
  have hD : ∀ r q, q∈Metric.ball p ρ →
      HasFDerivAt (fun y => cubicThetaHighCuspRow δ r y s)
        (fderiv ℝ (fun y => cubicThetaHighCuspRow δ r y s) q) q := by
    intro r q hq
    exact ((cubicThetaHighCuspRow_contDiffAt δ r s
      (lt_trans (by norm_num : (0:ℝ)<2) (hb r q hq).1)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have hdf := hasFDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball (convex_ball p ρ).isPreconnected
    hD (fun r q hq => (hb r q hq).2) hpB
    (cubicThetaHighCuspRow_sum_summable δ hp.le (by linarith)) hpB
  have he : (fun q => cubicThetaArithmeticRemainder (cubicThetaMobius (cubicThetaFullComplex δ) q) s)=ᶠ[𝓝 p]
      (fun q => ∑' r, cubicThetaHighCuspRow δ r q s) := by
    filter_upwards [Metric.ball_mem_nhds p hρ] with q hq
    exact cubicThetaHighCuspRow_sum δ (hb cubicThetaZeroRow q hq).1.le (by linarith)
  exact ⟨hu.of_norm_bounded (fun r => (hb r p hpB).2),(hdf.congr_of_eventuallyEq he).fderiv⟩

theorem cubicThetaArithmeticCusp_fderiv_bound (δ : SL(2,Eisenstein)) {s : ℂ} (hs : 3 < s.re)
    {p : ℂ × ℝ} (hp : 2<p.2) {R : ℝ} (hR : Complex.normSq p.1≤R) :
    ‖fderiv ℝ (fun q => cubicThetaArithmeticRemainder
        (cubicThetaMobius (cubicThetaFullComplex δ) q) s) p‖≤
      (6*(3+2*R)^2*cubicThetaFirstJetConstant s*p.2^(3-s.re))*cubicThetaCuspLatticeMass s := by
  obtain ⟨hds,he⟩ := cubicThetaHighCusp_fderiv_eq δ hs hp
  rw [he]
  let K := 6*(3+2*R)^2*cubicThetaFirstJetConstant s*p.2^(3-s.re)
  have hK : 0≤K := by
    apply mul_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (cubicThetaJetConstants_nonneg s).1
    · exact Real.rpow_nonneg (by linarith) _
  have hW := cubicThetaCuspLatticeWeight_summable δ hs
  calc
    _ ≤ ∑' r, ‖fderiv ℝ (fun q => cubicThetaHighCuspRow δ r q s) p‖ := norm_tsum_le_tsum_norm hds.norm
    _ ≤ ∑' r, K*cubicThetaCuspLatticeWeight δ s r :=
      Summable.tsum_le_tsum (fun r => cubicThetaHighCuspRow_fderiv_lattice_bound δ r hp.le hR (by linarith))
        hds.norm (hW.mul_left K)
    _ = K*(∑' r, cubicThetaCuspLatticeWeight δ s r) := tsum_mul_left
    _ ≤ K*cubicThetaCuspLatticeMass s :=
      mul_le_mul_of_nonneg_left (cubicThetaCuspLatticeWeight_tsum_le δ hs) hK

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalEnergyGraph
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPoint_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local graph of genuine compact smooth sections and its closed
Hilbert energy space. The value and derivative entries remain tied to the
same localized section throughout the construction. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

instance cubicThetaLocalEnergySpace_complete {φ : ℂ × ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ ⊆ {y : ℂ × ℝ | 0<y.2}) :
    CompleteSpace (cubicThetaLocalEnergySpace hφ hc hp) :=
  (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGlobalLocalRellich
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact localization of the completed global automorphic energy
space in an actual injective compact chart. -/
noncomputable section
open Set MeasureTheory Topology
open scoped ContDiff
namespace CubicFirstMoment

local instance globalLocalRellich_smoothGroup : AddCommGroup cubicThetaSmoothTests :=
  Module.addCommMonoidToAddCommGroup ℂ

variable {φ : ℂ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
  (hc : HasCompactSupport φ) (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})
  (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
  (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
  {S : Set CubicThetaPoint} (hS : IsCompact S) (hSe : S⊆e.source)
  (hsupp : tsupport φ⊆cubicThetaPointCoordinates '' S)

def cubicThetaLocalEnergyTestLinear : cubicThetaSmoothTests →ₗ[ℂ]
    cubicThetaLocalEnergySpace hφ hc hp :=
  (cubicThetaLocalEnergyGraph hφ hc hp).codRestrict (cubicThetaLocalEnergySpace hφ hc hp)
    (fun F => Submodule.le_topologicalClosure (cubicThetaLocalEnergyGraph hφ hc hp).range ⟨F,rfl⟩)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateIntegrationByParts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integration by parts for the pure coordinate derivatives, with
compact positive-height tests and no assumption on mixed derivatives. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.instIsAddHaarMeasureProdComplexRealVolume_solutions
lemma cubicThetaCoordinate_integrationByParts (k : CubicThetaAxis) (f φ : ℂ × ℝ → ℂ)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ⊆{p : ℂ × ℝ | 0<p.2})
    (hf : ContDiffOn ℝ 1 f {p : ℂ × ℝ | 0<p.2})
    (hf₂ : ContinuousOn (cubicThetaAxisSecond k f) {p : ℂ × ℝ | 0<p.2})
    (haxis : ∀ p : ℂ × ℝ, 0<p.2 → ContDiffAt ℝ 2
      (fun t => f (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t))
      (cubicThetaCoordinateCenter k p.1.re p.1.im p.2)) :
    (∫ p, φ p*cubicThetaAxisSecond k f p)=
      -(∫ p, cubicThetaAxisFirst k φ p*cubicThetaAxisFirst k f p) := by
  have hdf := cubicThetaAxisFirst_continuousOn k hf
  have hdφ := cubicThetaAxisFirst_continuous k hφ
  have hdφs := cubicThetaAxisFirst_support k φ
  have hdφc : HasCompactSupport (cubicThetaAxisFirst k φ) := hc.of_isClosed_subset isClosed_closure hdφs
  have hi₁ := cubicThetaPositiveProduct_integrable hdφ hdφc (hdφs.trans hp) hdf
  have hi₂ := cubicThetaPositiveProduct_integrable hφ.continuous hc hp hf₂
  have hi₀ := cubicThetaPositiveProduct_integrable hφ.continuous hc hp hdf
  exact integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B:=ContinuousLinearMap.mul ℝ ℂ) hi₁ hi₂ hi₀
    (fun p _ => by
      rw [cubicThetaAxisFirst_eq_fderiv k φ (hφ.differentiable one_ne_zero p)]
      exact (hφ.differentiable one_ne_zero p).hasFDerivAt.hasLineDerivAt (cubicThetaAxisVector k))
    (fun p h => cubicThetaAxisFirst_hasLineDerivAt k f p (haxis p (hp h)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGreenAlgebra
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact algebraic divergence identity for the hyperbolic density
v^-3 and the three real coordinate directions. -/
noncomputable section
open Set
namespace CubicFirstMoment

lemma cubicThetaGreen_identity (φ f : ℂ × ℝ → ℂ) (hφ : ContDiff ℝ 1 φ)
    (hs : tsupport φ⊆{p : ℂ × ℝ | 0<p.2}) (p : ℂ × ℝ) :
    star (φ p)*cubicThetaCoordinateLaplacian f p/(p.2:ℂ)^3+
      cubicThetaHeightInverse p*cubicThetaCoordinatePairing φ f p=
    cubicThetaCoordinateDivergence .x φ f p+cubicThetaCoordinateDivergence .y φ f p+
      cubicThetaCoordinateDivergence .height φ f p := by
  by_cases hp : 0<p.2
  · simp only [cubicThetaCoordinateDivergence,cubicThetaWeightedTest_axis _ hφ hp,
      cubicThetaHeightInverse_axis _ hp,cubicThetaCoordinatePairing,cubicThetaCoordinateLaplacian,
      cubicThetaWeightedTest,cubicThetaHeightInverse,mul_zero,add_zero]
    have hv : (p.2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hp.ne'
    push_cast
    field_simp [hv]
    ring
  · have hout : p∉tsupport φ := fun h => hp (hs h)
    have hz : φ p=0 := image_eq_zero_of_notMem_tsupport hout
    have hd (k : CubicThetaAxis) : cubicThetaAxisFirst k φ p=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hout (cubicThetaAxisFirst_support k φ h))
    have hw : cubicThetaWeightedTest φ p=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hout (cubicThetaWeightedTest_support φ h))
    have hdw (k : CubicThetaAxis) : cubicThetaAxisFirst k (cubicThetaWeightedTest φ) p=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hout
        (cubicThetaWeightedTest_support φ (cubicThetaAxisFirst_support k (cubicThetaWeightedTest φ) h)))
    simp only [hz,hd,hw,hdw,cubicThetaCoordinateDivergence,cubicThetaCoordinatePairing,
      star_zero,zero_mul,zero_div,mul_zero,add_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLocalGreen
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local hyperbolic Green identity for compact C1 tests. Its
only second derivatives are the three pure coordinate derivatives. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaCoordinateDivergence_integrable (k : CubicThetaAxis) (φ f : ℂ × ℝ → ℂ)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ⊆{p : ℂ × ℝ | 0<p.2})
    (hf : ContDiffOn ℝ 1 f {p : ℂ × ℝ | 0<p.2})
    (h₂ : ContinuousOn (cubicThetaAxisSecond k f) {p : ℂ × ℝ | 0<p.2}) :
    Integrable (cubicThetaCoordinateDivergence k φ f) := by
  have hw := cubicThetaWeightedTest_regular hφ hp
  have hwc := cubicThetaWeightedTest_compact hc
  have hws := (cubicThetaWeightedTest_support φ).trans hp
  have hds := cubicThetaAxisFirst_support k (cubicThetaWeightedTest φ)
  exact (cubicThetaPositiveProduct_integrable hw.continuous hwc hws h₂).add
    (cubicThetaPositiveProduct_integrable (cubicThetaAxisFirst_continuous k hw)
      (hwc.of_isClosed_subset isClosed_closure hds) (hds.trans hws)
      (cubicThetaAxisFirst_continuousOn k hf))

lemma cubicThetaCoordinateDivergence_integral (k : CubicThetaAxis) (φ f : ℂ × ℝ → ℂ)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ⊆{p : ℂ × ℝ | 0<p.2})
    (hf : ContDiffOn ℝ 1 f {p : ℂ × ℝ | 0<p.2})
    (h₂ : ContinuousOn (cubicThetaAxisSecond k f) {p : ℂ × ℝ | 0<p.2})
    (haxis : ∀ p : ℂ × ℝ, 0<p.2 → ContDiffAt ℝ 2
      (fun t => f (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t))
      (cubicThetaCoordinateCenter k p.1.re p.1.im p.2)) :
    (∫ p, cubicThetaCoordinateDivergence k φ f p)=0 := by
  have hw := cubicThetaWeightedTest_regular hφ hp
  have hwc := cubicThetaWeightedTest_compact hc
  have hws := (cubicThetaWeightedTest_support φ).trans hp
  have hds := cubicThetaAxisFirst_support k (cubicThetaWeightedTest φ)
  have hA := cubicThetaPositiveProduct_integrable hw.continuous hwc hws h₂
  have hB := cubicThetaPositiveProduct_integrable (cubicThetaAxisFirst_continuous k hw)
    (hwc.of_isClosed_subset isClosed_closure hds) (hds.trans hws)
    (cubicThetaAxisFirst_continuousOn k hf)
  simp only [cubicThetaCoordinateDivergence]
  rw [integral_add (f:=fun p => cubicThetaWeightedTest φ p*cubicThetaAxisSecond k f p)
      (g:=fun p => cubicThetaAxisFirst k (cubicThetaWeightedTest φ) p*cubicThetaAxisFirst k f p) hA hB,
    cubicThetaCoordinate_integrationByParts k f _ hw hwc hws hf h₂ haxis,neg_add_cancel]

lemma cubicThetaCoordinateLaplacian_continuous (f : ℂ × ℝ → ℂ)
    (hf : ContDiffOn ℝ 1 f {p : ℂ × ℝ | 0<p.2})
    (h₂ : ∀ k, ContinuousOn (cubicThetaAxisSecond k f) {p : ℂ × ℝ | 0<p.2}) :
    ContinuousOn (cubicThetaCoordinateLaplacian f) {p : ℂ × ℝ | 0<p.2} :=
  (((Complex.continuous_ofReal.comp continuous_snd).continuousOn.pow 2).mul
    (((h₂ .x).add (h₂ .y)).add (h₂ .height))).sub
      ((Complex.continuous_ofReal.comp continuous_snd).continuousOn.mul
        (cubicThetaAxisFirst_continuousOn .height hf))

lemma cubicThetaLocalGreen_identity (φ f : ℂ × ℝ → ℂ)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ⊆{p : ℂ × ℝ | 0<p.2})
    (hf : ContDiffOn ℝ 1 f {p : ℂ × ℝ | 0<p.2})
    (h₂ : ∀ k, ContinuousOn (cubicThetaAxisSecond k f) {p : ℂ × ℝ | 0<p.2})
    (haxis : ∀ k (p : ℂ × ℝ), 0<p.2 → ContDiffAt ℝ 2
      (fun t => f (cubicThetaCoordinateLine k p.1.re p.1.im p.2 t))
      (cubicThetaCoordinateCenter k p.1.re p.1.im p.2)) :
    (∫ p, cubicThetaHeightInverse p*cubicThetaCoordinatePairing φ f p)=
      -(∫ p, star (φ p)*cubicThetaCoordinateLaplacian f p/(p.2:ℂ)^3) := by
  have hL : Integrable (fun p => star (φ p)*cubicThetaCoordinateLaplacian f p/(p.2:ℂ)^3) := by
    have hdiv : ContinuousOn (fun p => cubicThetaCoordinateLaplacian f p/(p.2:ℂ)^3)
        {p : ℂ × ℝ | 0<p.2} :=
      (cubicThetaCoordinateLaplacian_continuous f hf h₂).div
        ((Complex.continuous_ofReal.comp continuous_snd).continuousOn.pow 3)
        (fun p hp => pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hp.ne'))
    simpa only [mul_div_assoc] using cubicThetaPositiveStarProduct_integrable hφ.continuous hc hp hdiv
  have hterm (k : CubicThetaAxis) : Integrable (fun p => star (cubicThetaAxisFirst k φ p)*
      (cubicThetaHeightInverse p*cubicThetaAxisFirst k f p)) := by
    have hs := cubicThetaAxisFirst_support k φ
    exact cubicThetaPositiveStarProduct_integrable (cubicThetaAxisFirst_continuous k hφ)
      (hc.of_isClosed_subset isClosed_closure hs) (hs.trans hp)
      (cubicThetaHeightInverse_regular.continuousOn.mul (cubicThetaAxisFirst_continuousOn k hf))
  have hP : Integrable (fun p => cubicThetaHeightInverse p*cubicThetaCoordinatePairing φ f p) := by
    convert ((hterm .x).add (hterm .y)).add (hterm .height) using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    unfold cubicThetaCoordinatePairing
    simp only [Pi.add_apply]
    ring
  have hD (k : CubicThetaAxis) := cubicThetaCoordinateDivergence_integrable k φ f hφ hc hp hf (h₂ k)
  have hi : (∫ p, star (φ p)*cubicThetaCoordinateLaplacian f p/(p.2:ℂ)^3)+
      (∫ p, cubicThetaHeightInverse p*cubicThetaCoordinatePairing φ f p)=0 := by
    rw [← integral_add hL hP]
    have he : (fun p => star (φ p)*cubicThetaCoordinateLaplacian f p/(p.2:ℂ)^3+
        cubicThetaHeightInverse p*cubicThetaCoordinatePairing φ f p)=
      (fun p => cubicThetaCoordinateDivergence .x φ f p+cubicThetaCoordinateDivergence .y φ f p+
        cubicThetaCoordinateDivergence .height φ f p) := funext (cubicThetaGreen_identity φ f hφ hp)
    rw [he,integral_add
      (f:=fun p => cubicThetaCoordinateDivergence .x φ f p+cubicThetaCoordinateDivergence .y φ f p)
      (g:=fun p => cubicThetaCoordinateDivergence .height φ f p)
      ((hD .x).add (hD .y)) (hD .height),
      integral_add (f:=fun p => cubicThetaCoordinateDivergence .x φ f p)
        (g:=fun p => cubicThetaCoordinateDivergence .y φ f p) (hD .x) (hD .y)]
    simp only [cubicThetaCoordinateDivergence_integral _ φ f hφ hc hp hf (h₂ _) (haxis _),add_zero]
  exact eq_neg_of_add_eq_zero_right hi

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticLocalWeak
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Eisenstein remainder satisfies the forced weak equation
against every compact C1 coordinate test at positive height. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaArithmetic_local_weak {s : ℂ} (hs : 2 < s.re)
    (φ : ℂ × ℝ → ℂ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ⊆{p : ℂ × ℝ | 0<p.2}) :
    (∫ p, cubicThetaHeightInverse p*cubicThetaCoordinatePairing φ
      (fun q => cubicThetaArithmeticRemainder q s) p)+
      s*(s-2)*(∫ p, star (φ p)*cubicThetaArithmeticRemainder p s/(p.2:ℂ)^3)=
    ∫ p, star (φ p)*cubicThetaForcingSeries p s/(p.2:ℂ)^3 := by
  have hg := cubicThetaLocalGreen_identity φ (fun q => cubicThetaArithmeticRemainder q s)
    hφ hc hp (cubicThetaArithmeticRemainder_contDiffOn_one hs)
    (fun k => cubicThetaArithmetic_axisSecond_continuous k hs)
    (fun k p hp => cubicThetaArithmetic_axis_contDiffAt k hs hp)
  have hd : ContinuousOn (fun p : ℂ × ℝ => (p.2:ℂ)^3) {p : ℂ × ℝ | 0<p.2} :=
    (Complex.continuous_ofReal.comp continuous_snd).continuousOn.pow 3
  have hn : ∀ p∈{p : ℂ × ℝ | 0<p.2}, (p.2:ℂ)^3≠0 :=
    fun p hp => pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hp.ne')
  have hM : Integrable (fun p => star (φ p)*cubicThetaArithmeticRemainder p s/(p.2:ℂ)^3) := by
    simpa only [mul_div_assoc,Pi.div_apply] using cubicThetaPositiveStarProduct_integrable hφ.continuous hc hp
      ((cubicThetaArithmeticRemainder_contDiffOn_one hs).continuousOn.div hd hn)
  have hF : Integrable (fun p => star (φ p)*cubicThetaForcingSeries p s/(p.2:ℂ)^3) := by
    simpa only [mul_div_assoc,Pi.div_apply] using cubicThetaPositiveStarProduct_integrable hφ.continuous hc hp
      ((cubicThetaForcingSeries_contDiffOn s).continuousOn.div hd hn)
  have he (p : ℂ × ℝ) :
      star (φ p)*cubicThetaCoordinateLaplacian (fun q => cubicThetaArithmeticRemainder q s) p/(p.2:ℂ)^3=
        s*(s-2)*(star (φ p)*cubicThetaArithmeticRemainder p s/(p.2:ℂ)^3)-
          star (φ p)*cubicThetaForcingSeries p s/(p.2:ℂ)^3 := by
    by_cases hpos : 0<p.2
    · have h := cubicThetaArithmeticRemainder_equation hs p.1.re p.1.im hpos
      rw [← cubicThetaCoordinateLaplacian_hyperbolic (fun q => cubicThetaArithmeticRemainder q s) p,
        cubicThetaCartesianPoint_self] at h
      have hl : cubicThetaCoordinateLaplacian (fun q => cubicThetaArithmeticRemainder q s) p=
          s*(s-2)*cubicThetaArithmeticRemainder p s-cubicThetaForcingSeries p s := by
        linear_combination h
      rw [hl]
      ring
    · have hz : φ p=0 := image_eq_zero_of_notMem_tsupport (fun h => hpos (hp h))
      simp only [hz,star_zero,zero_mul,zero_div,mul_zero,sub_self]
  have hi : (∫ p, star (φ p)*cubicThetaCoordinateLaplacian
      (fun q => cubicThetaArithmeticRemainder q s) p/(p.2:ℂ)^3)=
      s*(s-2)*(∫ p, star (φ p)*cubicThetaArithmeticRemainder p s/(p.2:ℂ)^3)-
        ∫ p, star (φ p)*cubicThetaForcingSeries p s/(p.2:ℂ)^3 := by
    simp_rw [he]
    rw [integral_sub (hM.const_mul _) hF,integral_const_mul]
  rw [hi] at hg
  linear_combination hg

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSectionPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaSectionPairing (F G : CubicThetaSection) (q : CubicThetaQuotient) : ℂ :=
  inner ℂ (F.val (cubicThetaQuotientLift q)) (G.val (cubicThetaQuotientLift q))

lemma cubicThetaSectionPairing_invariant (F G : CubicThetaSection)
    (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    inner ℂ (F.val (g • p)) (G.val (g • p))=inner ℂ (F.val p) (G.val p) := by
  rw [F.property,G.property]
  change inner ℂ (cubicThetaKubotaValue g • F.val p) (cubicThetaKubotaValue g • G.val p)=_
  rw [inner_smul_left,inner_smul_right,← mul_assoc,
    ← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,cubicThetaKubotaValue_norm]
  simp

lemma cubicThetaSectionPairing_apply (F G : CubicThetaSection) (p : CubicThetaPoint) :
    cubicThetaSectionPairing F G (cubicThetaQuotientMap p)=inner ℂ (F.val p) (G.val p) := by
  have he := cubicThetaQuotientLift_map (cubicThetaQuotientMap p)
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  unfold cubicThetaSectionPairing
  rw [← hg,cubicThetaSectionPairing_invariant]

lemma cubicThetaSectionPairing_support (F G : CubicThetaSection) :
    tsupport (cubicThetaSectionPairing F G)⊆tsupport (cubicThetaSectionNorm F) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro q hq
  apply subset_tsupport
  intro h
  have hz : F.val (cubicThetaQuotientLift q)=0 := norm_eq_zero.mp h
  exact hq (by simp only [cubicThetaSectionPairing,hz,inner_zero_left])

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoordinateSectionPairing
attribute [-instance] _root_.instMeasurableSpace
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

lemma cubicThetaCoordinatePairing_fderiv_congr {f g h : ℂ × ℝ → ℂ} {p : ℂ × ℝ}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p)
    (he : fderiv ℝ f p=fderiv ℝ g p) :
    cubicThetaCoordinatePairing f h p=cubicThetaCoordinatePairing g h p := by
  unfold cubicThetaCoordinatePairing
  simp only [cubicThetaAxisFirst_eq_fderiv _ _ hf,cubicThetaAxisFirst_eq_fderiv _ _ hg,he]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticChartWeak
attribute [-instance] _root_.instMeasurableSpace
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

lemma cubicThetaCoordinatePairing_zero_left {g f : ℂ × ℝ → ℂ} {p : ℂ × ℝ}
    (hp : p∉tsupport g) : cubicThetaCoordinatePairing g f p=0 := by
  have hz (k : CubicThetaAxis) : cubicThetaAxisFirst k g p=0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hp (cubicThetaAxisFirst_support k g h))
  simp only [cubicThetaCoordinatePairing,hz,star_zero,zero_mul,add_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticCuspMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaArithmeticRemainder_cusp_mass_bound
    (δ : SL(2,Eisenstein)) (z : ℂ) {v R : ℝ} (hv : 2≤v)
    (hz : Complex.normSq z≤R) {s : ℂ} (hs : 3 < s.re) :
    ‖cubicThetaArithmeticRemainder (cubicThetaMobius (cubicThetaFullComplex δ) (z,v)) s‖^2/v^3≤
      (cubicThetaCuspRemainderConstant s R)^2*v^(5-2*s.re) := by
  have hv0 : 0<v := by linarith
  have hb := cubicThetaArithmeticRemainder_cusp_bound δ z hv hz hs
  have hsq := mul_self_le_mul_self (_root_.norm_nonneg _) hb
  have he : (v^(4-s.re))^2/v^3=v^(5-2*s.re) := by
    rw [← Real.rpow_mul_natCast hv0.le,← Real.rpow_sub_natCast hv0.ne']
    congr 1
    norm_num
    ring
  calc
    _ ≤ (cubicThetaCuspRemainderConstant s R*v^(4-s.re))^2/v^3 :=
      div_le_div_of_nonneg_right (by simpa only [pow_two] using hsq) (pow_nonneg hv0.le 3)
    _ = _ := by rw [mul_pow,mul_div_assoc,he]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAnnularL2
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial annulus transport is a bounded linear map to the actual
global L2 space, with its norm bounded by the mass of a compact core. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaAnnularRepresentative (f : C(CubicThetaForcingBand,ℂ))
    (q : CubicThetaQuotient) : ℂ := cubicThetaAnnularSeries f (cubicThetaBorelSection q)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaComplexLocalization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact chart inclusion also respects the complex scalar action.
The extension is identified on the dense genuine smooth sections. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

variable {φ : ℂ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
  (hc : HasCompactSupport φ) (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})

local instance complexLocalization_borel_r02da95_1 : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
local instance complexLocalization_borelSpace_r02da95_1 : BorelSpace CubicThetaTangent := ⟨rfl⟩
local instance complexLocalization_smoothGroup_r02da95_1 : AddCommGroup cubicThetaSmoothTests :=
  Module.addCommMonoidToAddCommGroup ℂ
include hφ hc hp in
theorem valueMemLp (F : cubicThetaSmoothTests) :
    MemLp (cubicThetaTestLocalization φ F ∘ cubicThetaTangentCoordinates) 2
      LocalSobolev.tangentBorelVolume :=
  LocalSobolev.tangentFunction_memLp (cubicThetaTestLocalization φ F)
    ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (cubicThetaTestLocalization_compact hc F)

def cubicThetaLocalValue : cubicThetaSmoothTests →ₗ[ℂ] LocalSobolev.TangentComplexL2 where
  toFun F := (valueMemLp hφ hc hp F).toLp _
  map_add' F G := by
    apply Lp.ext
    filter_upwards [(valueMemLp hφ hc hp (F+G)).coeFn_toLp,
      (valueMemLp hφ hc hp F).coeFn_toLp,(valueMemLp hφ hc hp G).coeFn_toLp,
      Lp.coeFn_add ((valueMemLp hφ hc hp F).toLp _) ((valueMemLp hφ hc hp G).toLp _)]
      with u hFG hF hG ha
    simp only [Pi.add_apply] at ha
    rw [hFG,ha,hF,hG]
    change cubicThetaTestLocalization φ ((F+G : cubicThetaSmoothTests) : CubicThetaSection) _=_
    rw [cubicThetaTestLocalization_add]
    rfl
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [(valueMemLp hφ hc hp (c • F)).coeFn_toLp,
      (valueMemLp hφ hc hp F).coeFn_toLp,
      Lp.coeFn_smul c ((valueMemLp hφ hc hp F).toLp _)] with u hCF hF hs
    simp only [Pi.smul_apply,RingHom.id_apply] at hs ⊢
    rw [hCF,hs,hF]
    change cubicThetaTestLocalization φ ((c • F : cubicThetaSmoothTests) : CubicThetaSection) _=_
    rw [cubicThetaTestLocalization_smul]
    rfl

lemma cubicThetaLocalValue_apply (F : cubicThetaSmoothTests) :
    cubicThetaLocalValue hφ hc hp F=
      LocalSobolev.tangentFunctionL2 (cubicThetaTestLocalization φ F)
        ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
        (cubicThetaTestLocalization_compact hc F) := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGlobalMultiplier
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded multiplication on the actual quotient L2 space. This is used
to reconstruct core cutoffs from the compact coordinate inclusions. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

variable {φ : CubicThetaQuotient → ℂ} (hφ : AEStronglyMeasurable φ cubicThetaQuotientMeasure)
  {C : ℝ} (hbound : ∀ q, ‖φ q‖≤C)

include hφ hbound in
lemma multiplier_memLp (u : CubicThetaGlobalL2) :
    MemLp (fun q => φ q*u q) 2 cubicThetaQuotientMeasure := by
  apply (Lp.memLp u).of_le_mul (c:=C) (hφ.mul (Lp.aestronglyMeasurable u))
  filter_upwards with q
  change ‖φ q*u q‖≤C*‖u q‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hbound q) (_root_.norm_nonneg _)

def cubicThetaGlobalMultiplierLinear : CubicThetaGlobalL2 →ₗ[ℂ] CubicThetaGlobalL2 where
  toFun u := (multiplier_memLp hφ hbound u).toLp _
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(multiplier_memLp hφ hbound (u+v)).coeFn_toLp,
      (multiplier_memLp hφ hbound u).coeFn_toLp,(multiplier_memLp hφ hbound v).coeFn_toLp,
      Lp.coeFn_add u v,
      Lp.coeFn_add ((multiplier_memLp hφ hbound u).toLp _)
        ((multiplier_memLp hφ hbound v).toLp _)] with q hsum hu hv huv hadd
    simp only [Pi.add_apply] at huv hadd
    rw [hsum,hadd,hu,hv,huv]
    ring
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [(multiplier_memLp hφ hbound (c • u)).coeFn_toLp,
      (multiplier_memLp hφ hbound u).coeFn_toLp,Lp.coeFn_smul c u,
      Lp.coeFn_smul c ((multiplier_memLp hφ hbound u).toLp _)] with q hmul hu hcu hadd
    simp only [Pi.smul_apply,RingHom.id_apply] at hcu hadd ⊢
    rw [hmul,hadd,hu,hcu]
    simp only [smul_eq_mul]
    ring

lemma cubicThetaGlobalMultiplierLinear_bound (u : CubicThetaGlobalL2) :
    ‖cubicThetaGlobalMultiplierLinear hφ hbound u‖≤C*‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(multiplier_memLp hφ hbound u).coeFn_toLp] with q hq
  change ‖((multiplier_memLp hφ hbound u).toLp _) q‖≤C*‖u q‖
  rw [hq,norm_mul]
  exact mul_le_mul_of_nonneg_right (hbound q) (_root_.norm_nonneg _)

def cubicThetaGlobalMultiplier : CubicThetaGlobalL2 →L[ℂ] CubicThetaGlobalL2 :=
  (cubicThetaGlobalMultiplierLinear hφ hbound).mkContinuous C
    (cubicThetaGlobalMultiplierLinear_bound hφ hbound)

lemma cubicThetaGlobalMultiplier_ae (u : CubicThetaGlobalL2) :
    (cubicThetaGlobalMultiplier hφ hbound u : CubicThetaQuotient → ℂ)=ᵐ[cubicThetaQuotientMeasure]
      fun q => φ q*u q := (multiplier_memLp hφ hbound u).coeFn_toLp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoreMassCompact
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPoint_polish _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactness of the genuine global core bump multipliers. The
weighted quotient norm is controlled by the proved compact local map. -/
noncomputable section
open Set MeasureTheory Topology
open scoped ContDiff
namespace CubicFirstMoment

local instance coreMassCompact_borel_r02da95_1 : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent
local instance coreMassCompact_borelSpace_r02da95_1 : BorelSpace CubicThetaTangent := ⟨rfl⟩
lemma cubicThetaLocalValue_norm_sq {φ : ℂ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})
    (F : cubicThetaSmoothTests) :
    ‖cubicThetaLocalValue hφ hc hp F‖^2=
      ∫ y, ‖cubicThetaTestLocalization φ F y‖^2 := by
  rw [cubicThetaLocalValue_apply,cubicTheta_l2_norm_sq_measure]
  calc
    _ = ∫ u, ‖cubicThetaTestLocalization φ F (cubicThetaTangentCoordinates u)‖^2
        ∂LocalSobolev.tangentBorelVolume := by
      apply integral_congr_ae
      filter_upwards [(LocalSobolev.tangentFunction_memLp (cubicThetaTestLocalization φ F)
        ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
        (cubicThetaTestLocalization_compact hc F)).coeFn_toLp] with u hu
      change ‖((LocalSobolev.tangentFunction_memLp (cubicThetaTestLocalization φ F)
        ((cubicThetaTestLocalization_smooth hφ hp F).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
        (cubicThetaTestLocalization_compact hc F)).toLp _) u‖^2=_
      rw [hu]
      rfl
    _ = _ := LocalSobolev.tangentBorelVolume_integral
      (fun y => ‖cubicThetaTestLocalization φ F y‖^2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoreRestriction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual global restriction to the arithmetic compact core is
compact from the energy space to L2. The finite bump inequality gives
norm domination by the already compact family of localizations. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators MatrixGroups
namespace CubicFirstMoment

lemma indicatorOne_bound {K : Set CubicThetaQuotient} (q : CubicThetaQuotient) :
    ‖K.indicator (fun _ => (1:ℂ)) q‖≤1 := by
  by_cases h : q∈K <;> simp [h]

def cubicThetaGlobalRestriction {K : Set CubicThetaQuotient} (hK : MeasurableSet K) :
    CubicThetaGlobalL2 →L[ℂ] CubicThetaGlobalL2 :=
  cubicThetaGlobalMultiplier (stronglyMeasurable_const.indicator hK).aestronglyMeasurable
    indicatorOne_bound

lemma cubicThetaGlobalRestriction_ae {K : Set CubicThetaQuotient} (hK : MeasurableSet K)
    (u : CubicThetaGlobalL2) :
    (cubicThetaGlobalRestriction hK u : CubicThetaQuotient → ℂ)=ᵐ[cubicThetaQuotientMeasure]
      K.indicator (fun q => u q) := by
  filter_upwards [cubicThetaGlobalMultiplier_ae
    (stronglyMeasurable_const.indicator hK).aestronglyMeasurable indicatorOne_bound u] with q hq
  change cubicThetaGlobalRestriction hK u q=K.indicator (fun _ => (1:ℂ)) q*u q at hq
  rw [hq]
  by_cases h : q∈K <;> simp [h]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCuspScalarIntegrals
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaCuspPullback (δ : SL(2,Eisenstein)) (f : CubicThetaQuotient → ℝ)
    (y : ℂ × ℝ) : ℝ :=
  f (cubicThetaQuotientMap (δ • cubicThetaPointInclusion.symm y))

lemma cubicThetaCuspPullback_apply (δ : SL(2,Eisenstein)) (f : CubicThetaQuotient → ℝ)
    (p : CubicThetaPoint) :
    cubicThetaCuspPullback δ f (cubicThetaPointCoordinates p)=f (cubicThetaQuotientMap (δ • p)) := by
  have h : cubicThetaPointInclusion.symm (cubicThetaPointCoordinates p)=p :=
    cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)
  simp only [cubicThetaCuspPullback,h]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFiniteCuspEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.instMeasurableSpace
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

lemma cubicThetaIntegral_cover_le {K U : Set CubicThetaQuotient}
    (hK : MeasurableSet K) (hU : MeasurableSet U) (hcover : K∪U=univ)
    {f : CubicThetaQuotient → ℝ} (hf : Integrable f cubicThetaQuotientMeasure)
    (hn : ∀ q, 0≤f q) :
    (∫ q, f q ∂cubicThetaQuotientMeasure)≤
      (∫ q in K, f q ∂cubicThetaQuotientMeasure)+
      ∫ q in U, f q ∂cubicThetaQuotientMeasure := by
  rw [← integral_indicator hK,← integral_indicator hU,
    ← integral_add (hf.indicator hK) (hf.indicator hU)]
  apply integral_mono hf ((hf.indicator hK).add (hf.indicator hU))
  intro q
  dsimp only [Pi.add_apply]
  have hq : q∈K∪U := by rw [hcover]; trivial
  rcases hq with hq | hq
  · rw [indicator_of_mem hq]
    exact le_add_of_nonneg_right (indicator_nonneg (fun x hx => hn x) q)
  · rw [indicator_of_mem hq]
    exact le_add_of_nonneg_left (indicator_nonneg (fun x hx => hn x) q)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticRowSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaArithmeticRowTerm (z : ℂ) (v : ℝ) (h : Eisenstein) : ℂ :=
  if h=0 then 0 else cubicThetaArithmeticCoefficient (-lambdaE*h)*
    cubicThetaWhittaker (‖cubicThetaRowFrequency h‖*v)*
      (Real.fourierChar (tracePair z (cubicThetaRowFrequency h)):ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeSections
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dilation by a cubed prime pulls an original section to a genuine
section on the integral cubed-prime subgroup, with the same multiplier. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeDilationSection {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) : cubicThetaPrimeCubeSections p :=
  ⟨⟨fun x => F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x),
    F.val.continuous.comp (continuous_const_smul _)⟩,by
    intro g x
    have he : cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • (g.val • x)=
        cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g •
          (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x) := by
      change cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
        (cubicThetaPrincipalComplex g.val • x)=
        cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g) •
          (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x)
      rw [←mul_smul,←mul_smul,cubicThetaPrimeDilation_intertwines (cubicThetaPrimeCube_primary hp)]
    change F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • (g.val • x))=_
    rw [he,F.property,←cubicThetaPrimeCubeConjugate_kubota hp g]
    rfl⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeTransversal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite right cosets used by the cubed-prime Hecke trace. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeTransversal_complement (p : Eisenstein) :
    Subgroup.IsComplement (cubicThetaPrimeIwahori (p^3)) (cubicThetaPrimeCubeTransversal p) :=
  (Classical.choose_spec ((cubicThetaPrimeIwahori (p^3)).exists_isComplement_right 1)).1

lemma cubicThetaPrimeCubeTransversal_finite {p : Eisenstein} (hp : primaryPrime p) :
    Finite (cubicThetaPrimeCubeTransversal p) := by
  let := cubicThetaPrimeCubeIwahori_finiteIndex hp
  apply Nat.finite_of_card_ne_zero
  rw [(cubicThetaPrimeCubeTransversal_complement p).card_right]
  exact Subgroup.FiniteIndex.index_ne_zero

def cubicThetaPrimeCubeCosetStep (p : Eisenstein) (g : cubicThetaPrincipalGroup)
    (t : cubicThetaPrimeCubeTransversal p) : cubicThetaPrimeCubeTransversal p :=
  ((cubicThetaPrimeCubeTransversal_complement p).equiv (t.val*g)).snd

lemma cubicThetaPrimeCubeCosetStep_cancel (p : Eisenstein) (g : cubicThetaPrincipalGroup)
    (t : cubicThetaPrimeCubeTransversal p) :
    cubicThetaPrimeCubeCosetStep p g⁻¹ (cubicThetaPrimeCubeCosetStep p g t)=t := by
  let C := cubicThetaPrimeCubeTransversal_complement p
  let a := C.equiv (t.val*g)
  have he : a.fst.val*a.snd.val=t.val*g := C.equiv_fst_mul_equiv_snd _
  have hm : a.snd.val*g⁻¹=a.fst.val⁻¹*t.val := by
    calc
      _ = a.fst.val⁻¹*((a.fst.val*a.snd.val)*g⁻¹) := by group
      _ = _ := by rw [he]; group
  change (C.equiv (a.snd.val*g⁻¹)).snd=t
  rw [hm]
  change (C.equiv ((a.fst⁻¹).val*t.val)).snd=t
  rw [C.equiv_mul_left]
  exact C.equiv_snd_eq_self_of_mem_of_one_mem (cubicThetaPrimeIwahori (p^3)).one_mem t.property

def cubicThetaPrimeCubeCosetPermutation (p : Eisenstein) (g : cubicThetaPrincipalGroup) :
    cubicThetaPrimeCubeTransversal p ≃ cubicThetaPrimeCubeTransversal p where
  toFun := cubicThetaPrimeCubeCosetStep p g
  invFun := cubicThetaPrimeCubeCosetStep p g⁻¹
  left_inv := cubicThetaPrimeCubeCosetStep_cancel p g
  right_inv t := by simpa only [inv_inv] using cubicThetaPrimeCubeCosetStep_cancel p g⁻¹ t

lemma cubicThetaPrimeCubeCosetPermutation_factor (p : Eisenstein) (g : cubicThetaPrincipalGroup)
    (t : cubicThetaPrimeCubeTransversal p) :
    (((cubicThetaPrimeCubeTransversal_complement p).equiv (t.val*g)).fst.val)*
      (cubicThetaPrimeCubeCosetPermutation p g t).val=t.val*g :=
  (cubicThetaPrimeCubeTransversal_complement p).equiv_fst_mul_equiv_snd _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeTrace
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal finite cubed-prime trace, with its cubic multipliers.
Composing it with dilation gives the actual cubed-prime Hecke operator. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeTraceTerm_permute (p : Eisenstein) (F : cubicThetaPrimeCubeSections p)
    (g : cubicThetaPrincipalGroup) (t : cubicThetaPrimeCubeTransversal p) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeTraceTerm p F (t.val*g) x=
      cubicThetaPrimeCubeTraceTerm p F (cubicThetaPrimeCubeCosetPermutation p g t).val x := by
  rw [←cubicThetaPrimeCubeCosetPermutation_factor p g t,cubicThetaPrimeCubeTraceTerm_left]

def cubicThetaPrimeCubeTraceSection {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p) : CubicThetaSection := by
  letI : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  letI := Fintype.ofFinite (cubicThetaPrimeCubeTransversal p)
  refine ⟨⟨fun x => ∑' t : cubicThetaPrimeCubeTransversal p,
    cubicThetaPrimeCubeTraceTerm p F t.val x,?_⟩,?_⟩
  · simp only [tsum_fintype]
    apply continuous_finsetSum
    intro t _
    exact continuous_const.mul (F.val.continuous.comp (continuous_const_smul t.val))
  · intro g x
    change (∑' t : cubicThetaPrimeCubeTransversal p, cubicThetaPrimeCubeTraceTerm p F t.val (g • x))=
      cubicThetaKubotaValue g*(∑' t : cubicThetaPrimeCubeTransversal p,
        cubicThetaPrimeCubeTraceTerm p F t.val x)
    simp only [tsum_fintype]
    simp_rw [cubicThetaPrimeCubeTraceTerm_translate,cubicThetaPrimeCubeTraceTerm_permute]
    rw [←Finset.mul_sum]
    exact congrArg (fun a : ℂ => cubicThetaKubotaValue g*a)
      (Equiv.sum_comp (cubicThetaPrimeCubeCosetPermutation p g)
        (fun t => cubicThetaPrimeCubeTraceTerm p F t.val x))

def cubicThetaPrimeCubeHecke {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) : CubicThetaSection :=
  cubicThetaPrimeCubeTraceSection hp (cubicThetaPrimeCubeDilationSection hp F)

lemma cubicThetaPrimeCubeHecke_apply {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    (cubicThetaPrimeCubeHecke hp F).val x=
      ∑' t : cubicThetaPrimeCubeTransversal p, star (cubicThetaKubotaValue t.val)*
        F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • (t.val • x)) := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeCosets
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete bottom-row coordinates for the cubed-prime correspondence.
The first chart is represented by integral lower unipotents in level three. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaPrimeCubeCoset (p : Eisenstein) (g : cubicThetaPrincipalGroup) :
    cubicThetaPrimeCubeTransversal p :=
  ((cubicThetaPrimeCubeTransversal_complement p).equiv g).snd

lemma cubicThetaPrimeCubeCoset_eq_iff (p : Eisenstein)
    (g h : cubicThetaPrincipalGroup) :
    cubicThetaPrimeCubeCoset p g=cubicThetaPrimeCubeCoset p h ↔
      p^3 ∣ h.val 1 0*g.val 1 1-h.val 1 1*g.val 1 0 := by
  rw [cubicThetaPrimeCubeCoset,cubicThetaPrimeCubeCoset,
    (cubicThetaPrimeCubeTransversal_complement p).equiv_snd_eq_iff_rightCosetEquivalence]
  rw [RightCosetEquivalence,rightCoset_eq_iff]
  change p^3 ∣ (h.val*g.val⁻¹) 1 0 ↔ _
  simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.mul_apply,Fin.sum_univ_two,Matrix.adjugate_fin_two,sub_eq_add_neg]

lemma cubicThetaPrimeCubeCoset_lower_eq_iff {p : Eisenstein} (hp : primaryPrime p)
    (m n : Eisenstein) :
    cubicThetaPrimeCubeCoset p (cubicThetaPrincipalLower m)=
      cubicThetaPrimeCubeCoset p (cubicThetaPrincipalLower n) ↔ p^3 ∣ n-m := by
  rw [cubicThetaPrimeCubeCoset_eq_iff]
  change p^3 ∣ 3*n*1-1*(3*m) ↔ p^3 ∣ n-m
  rw [mul_one,one_mul,←mul_sub]
  constructor
  · exact (primary_coprime_three (cubicThetaPrimeCube_primary hp)).dvd_of_dvd_mul_left
  · exact fun h => dvd_mul_of_dvd_right h 3

def cubicThetaPrimeCubeLowerChart (p : Eisenstein) (r : Residues (p^3)) :
    cubicThetaPrimeCubeTransversal p :=
  cubicThetaPrimeCubeCoset p (cubicThetaPrincipalLower (residueRepresentative (p^3) r))

theorem cubicThetaPrimeCubeLowerChart_injective {p : Eisenstein} (hp : primaryPrime p) :
    Function.Injective (cubicThetaPrimeCubeLowerChart p) := by
  intro r s h
  have hd := (cubicThetaPrimeCubeCoset_lower_eq_iff hp _ _).mp h
  have he := residue_eq_of_dvd_sub hd
  simpa only [residueRepresentative_spec] using he.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeLowerChart
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The lower-unipotent chart covers precisely the cosets whose bottom
right entry is a unit at the chosen prime. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeLowerChart_covers {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrincipalGroup) (hd : ¬p ∣ g.val 1 1) :
    ∃ r : Residues (p^3), cubicThetaPrimeCubeLowerChart p r=cubicThetaPrimeCubeCoset p g := by
  let q := Ideal.Quotient.mk (modulus (p^3))
  have hpd : IsCoprime (p^3) (g.val 1 1) :=
    (hp.2.coprime_iff_not_dvd.mpr hd).pow_left
  let d : (Residues (p^3))ˣ := (residue_isUnit_of_isCoprime hpd).unit
  let t : (Residues (p^3))ˣ :=
    (residue_isUnit_of_isCoprime (primary_coprime_three (cubicThetaPrimeCube_primary hp))).unit
  let r : Residues (p^3) := ((d*t)⁻¹ : (Residues (p^3))ˣ)*q (g.val 1 0)
  refine ⟨r,(cubicThetaPrimeCubeCoset_eq_iff p _ _).mpr ?_⟩
  change p^3 ∣ g.val 1 0*1-g.val 1 1*(3*residueRepresentative (p^3) r)
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (g.val 1 0*1-g.val 1 1*(3*residueRepresentative (p^3) r))=0
  have hdv : (d : Residues (p^3))=q (g.val 1 1) := IsUnit.unit_spec _
  have htv : (t : Residues (p^3))=q 3 := IsUnit.unit_spec _
  have hr : q (residueRepresentative (p^3) r)=r := residueRepresentative_spec _ _
  simp only [map_sub,map_mul,mul_one]
  rw [hr,←hdv,←htv]
  change q (g.val 1 0)-(d : Residues (p^3))*
    ((t : Residues (p^3))*(((d*t)⁻¹ : (Residues (p^3))ˣ)*q (g.val 1 0)))=0
  rw [←mul_assoc,←Units.val_mul,←mul_assoc,←Units.val_mul,mul_inv_cancel,
    Units.val_one,one_mul,sub_self]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeUpperChart
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complementary chart of the cubed-prime correspondence. Its
parameters are the residue classes divisible by the prime. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeWeylDenominator {p : Eisenstein} (hp : primaryPrime p) : Eisenstein :=
  Classical.choose (residue_crt_one (primary_coprime_three (cubicThetaPrimeCube_primary hp)) 0)

lemma cubicThetaPrimeCubeWeylDenominator_dvd {p : Eisenstein} (hp : primaryPrime p) :
    p^3 ∣ cubicThetaPrimeCubeWeylDenominator hp := by
  change p^3 ∣ Classical.choose (residue_crt_one
    (primary_coprime_three (cubicThetaPrimeCube_primary hp)) 0)
  simpa only [sub_zero] using
    (Classical.choose_spec (residue_crt_one
      (primary_coprime_three (cubicThetaPrimeCube_primary hp)) 0)).1

lemma cubicThetaPrimeCubeWeylDenominator_primary {p : Eisenstein} (hp : primaryPrime p) :
    primary (cubicThetaPrimeCubeWeylDenominator hp) :=
  (Classical.choose_spec (residue_crt_one
    (primary_coprime_three (cubicThetaPrimeCube_primary hp)) 0)).2

def cubicThetaPrimeCubeWeylRow {p : Eisenstein} (hp : primaryPrime p) : CubicThetaBottomRow :=
  ⟨3,cubicThetaPrimeCubeWeylDenominator hp,dvd_refl _,
    cubicThetaPrimeCubeWeylDenominator_primary hp,
    (primary_coprime_three (cubicThetaPrimeCubeWeylDenominator_primary hp)).symm⟩

def cubicThetaPrimeCubeWeyl {p : Eisenstein} (hp : primaryPrime p) : cubicThetaPrincipalGroup :=
  (cubicThetaPrimeCubeWeylRow hp).completion

lemma cubicThetaPrimeCubeWeyl_c {p : Eisenstein} (hp : primaryPrime p) :
    (cubicThetaPrimeCubeWeyl hp).val 1 0=3 :=
  congrArg CubicThetaBottomRow.c (cubicThetaPrimeCubeWeylRow hp).completion_row

lemma cubicThetaPrimeCubeWeyl_d {p : Eisenstein} (hp : primaryPrime p) :
    (cubicThetaPrimeCubeWeyl hp).val 1 1=cubicThetaPrimeCubeWeylDenominator hp :=
  congrArg CubicThetaBottomRow.d (cubicThetaPrimeCubeWeylRow hp).completion_row

def cubicThetaPrimeCubeUpperRepresentative {p : Eisenstein} (hp : primaryPrime p)
    (r : cubicThetaPrimeCubeUpperParameter p) : cubicThetaPrincipalGroup :=
  cubicThetaPrimeCubeWeyl hp*cubicThetaPrincipalTranslation (residueRepresentative (p^3) r.val)

lemma cubicThetaPrimeCubeUpperRepresentative_c {p : Eisenstein} (hp : primaryPrime p)
    (r : cubicThetaPrimeCubeUpperParameter p) :
    (cubicThetaPrimeCubeUpperRepresentative hp r).val 1 0=3 := by
  change (((cubicThetaPrimeCubeWeyl hp).val : Matrix (Fin 2) (Fin 2) Eisenstein)*
    !![1,3*residueRepresentative (p^3) r.val;0,1]) 1 0=3
  simp [Matrix.mul_apply,Fin.sum_univ_two,cubicThetaPrimeCubeWeyl_c]

lemma cubicThetaPrimeCubeUpperRepresentative_d {p : Eisenstein} (hp : primaryPrime p)
    (r : cubicThetaPrimeCubeUpperParameter p) :
    (cubicThetaPrimeCubeUpperRepresentative hp r).val 1 1=
      cubicThetaPrimeCubeWeylDenominator hp+9*residueRepresentative (p^3) r.val := by
  change (((cubicThetaPrimeCubeWeyl hp).val : Matrix (Fin 2) (Fin 2) Eisenstein)*
    !![1,3*residueRepresentative (p^3) r.val;0,1]) 1 1=_
  simp only [Matrix.mul_apply,Fin.sum_univ_two]
  change (cubicThetaPrimeCubeWeyl hp).val 1 0*(3*residueRepresentative (p^3) r.val)+
    (cubicThetaPrimeCubeWeyl hp).val 1 1*1=_
  rw [cubicThetaPrimeCubeWeyl_c,cubicThetaPrimeCubeWeyl_d]
  ring

def cubicThetaPrimeCubeUpperChart {p : Eisenstein} (hp : primaryPrime p)
    (r : cubicThetaPrimeCubeUpperParameter p) : cubicThetaPrimeCubeTransversal p :=
  cubicThetaPrimeCubeCoset p (cubicThetaPrimeCubeUpperRepresentative hp r)

theorem cubicThetaPrimeCubeUpperChart_injective {p : Eisenstein} (hp : primaryPrime p) :
    Function.Injective (cubicThetaPrimeCubeUpperChart hp) := by
  intro r s h
  have hd := (cubicThetaPrimeCubeCoset_eq_iff p _ _).mp h
  rw [cubicThetaPrimeCubeUpperRepresentative_c,cubicThetaPrimeCubeUpperRepresentative_c,
    cubicThetaPrimeCubeUpperRepresentative_d,cubicThetaPrimeCubeUpperRepresentative_d] at hd
  have he : p^3 ∣ 27*(residueRepresentative (p^3) r.val-residueRepresentative (p^3) s.val) := by
    convert hd using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hc : IsCoprime (p^3) (27:Eisenstein) := by
    convert (primary_coprime_three (cubicThetaPrimeCube_primary hp)).pow_right (n := 3) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  apply Subtype.ext
  simpa only [residueRepresentative_spec] using
    residue_eq_of_dvd_sub (hc.dvd_of_dvd_mul_left he)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeChartCover
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two integral charts are disjoint and cover the actual right
cosets. The proof uses the primitive bottom row and units modulo p^3. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeLower_ne_upper {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues (p^3)) (s : cubicThetaPrimeCubeUpperParameter p) :
    cubicThetaPrimeCubeLowerChart p r≠cubicThetaPrimeCubeUpperChart hp s := by
  intro he
  have hdet := (cubicThetaPrimeCubeCoset_eq_iff p _ _).mp he
  rw [cubicThetaPrimeCubeUpperRepresentative_c,cubicThetaPrimeCubeUpperRepresentative_d] at hdet
  change p^3 ∣ 3*1-(cubicThetaPrimeCubeWeylDenominator hp+
    9*residueRepresentative (p^3) s.val)*(3*residueRepresentative (p^3) r) at hdet
  have hpow : p ∣ p^3 := dvd_pow_self p (by norm_num)
  have hd : p ∣ cubicThetaPrimeCubeWeylDenominator hp+
      9*residueRepresentative (p^3) s.val :=
    dvd_add (hpow.trans (cubicThetaPrimeCubeWeylDenominator_dvd hp))
      (dvd_mul_of_dvd_right s.property 9)
  have ht := dvd_add (hpow.trans hdet)
    (dvd_mul_of_dvd_left hd (3*residueRepresentative (p^3) r))
  have hthree : p ∣ (3:Eisenstein) := by simpa only [mul_one,sub_add_cancel] using ht
  exact hp.2.not_isUnit ((primary_coprime_three hp.1).isRelPrime (dvd_refl p) hthree)

theorem cubicThetaPrimeCubeUpperChart_covers {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrincipalGroup) (hd : p∣g.val 1 1) :
    ∃ r : cubicThetaPrimeCubeUpperParameter p,
      cubicThetaPrimeCubeUpperChart hp r=cubicThetaPrimeCubeCoset p g := by
  let q := Ideal.Quotient.mk (modulus (p^3))
  have hc : ¬p∣g.val 1 0 := fun hc => hp.2.not_isUnit
    ((cubicThetaBottomRow g).coprime.isRelPrime hc hd)
  have hpc : IsCoprime (p^3) (g.val 1 0) :=
    (hp.2.coprime_iff_not_dvd.mpr hc).pow_left
  have hunit : IsCoprime (p^3) (g.val 1 0*3) :=
    hpc.mul_right (primary_coprime_three (cubicThetaPrimeCube_primary hp))
  let u : (Residues (p^3))ˣ := (residue_isUnit_of_isCoprime hunit).unit
  let x := residueRepresentative (p^3) (u⁻¹ : (Residues (p^3))ˣ)
  let m := g.val 1 1*x
  let r : cubicThetaPrimeCubeUpperParameter p :=
    ⟨q m,cubicThetaPrimeCubeRepresentative_dvd (dvd_mul_of_dvd_left hd x)⟩
  refine ⟨r,(cubicThetaPrimeCubeCoset_eq_iff p _ _).mpr ?_⟩
  rw [cubicThetaPrimeCubeUpperRepresentative_c,cubicThetaPrimeCubeUpperRepresentative_d]
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (g.val 1 0*(cubicThetaPrimeCubeWeylDenominator hp+
    9*residueRepresentative (p^3) r.val)-g.val 1 1*3)=0
  have hqW : q (cubicThetaPrimeCubeWeylDenominator hp)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr (cubicThetaPrimeCubeWeylDenominator_dvd hp))
  have hu : (u : Residues (p^3))=q (g.val 1 0*3) := IsUnit.unit_spec _
  have hx : q x=(u⁻¹ : (Residues (p^3))ˣ) := residueRepresentative_spec _ _
  have hi : q (g.val 1 0)*q 3*q x=1 := by
    rw [←map_mul,←hu,hx,←Units.val_mul,mul_inv_cancel,Units.val_one]
  have hr : q (residueRepresentative (p^3) r.val)=q m := residueRepresentative_spec _ _
  simp only [map_sub,map_add,map_mul,hqW,zero_add]
  rw [hr]
  change q (g.val 1 0)*(q 9*(q (g.val 1 1)*q x))-q (g.val 1 1)*q 3=0
  norm_num only [map_ofNat] at hi ⊢
  linear_combination (3*q (g.val 1 1))*hi

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeChartEquiv
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite parametrization of the right cosets for the cubed-prime
trace by the two integral affine charts. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeChart {p : Eisenstein} (hp : primaryPrime p) :
    Residues (p^3) ⊕ cubicThetaPrimeCubeUpperParameter p → cubicThetaPrimeCubeTransversal p :=
  Sum.elim (cubicThetaPrimeCubeLowerChart p) (cubicThetaPrimeCubeUpperChart hp)

lemma cubicThetaPrimeCubeChart_injective {p : Eisenstein} (hp : primaryPrime p) :
    Function.Injective (cubicThetaPrimeCubeChart hp) := by
  intro r s h
  cases r with
  | inl r =>
    cases s with
    | inl s => exact congrArg Sum.inl (cubicThetaPrimeCubeLowerChart_injective hp h)
    | inr s => exact False.elim (cubicThetaPrimeCubeLower_ne_upper hp r s h)
  | inr r =>
    cases s with
    | inl s => exact False.elim (cubicThetaPrimeCubeLower_ne_upper hp s r h.symm)
    | inr s => exact congrArg Sum.inr (cubicThetaPrimeCubeUpperChart_injective hp h)

lemma cubicThetaPrimeCubeCoset_self (p : Eisenstein) (t : cubicThetaPrimeCubeTransversal p) :
    cubicThetaPrimeCubeCoset p t.val=t :=
  (cubicThetaPrimeCubeTransversal_complement p).equiv_snd_eq_self_of_mem_of_one_mem
    (cubicThetaPrimeIwahori (p^3)).one_mem t.property

lemma cubicThetaPrimeCubeChart_surjective {p : Eisenstein} (hp : primaryPrime p) :
    Function.Surjective (cubicThetaPrimeCubeChart hp) := by
  intro t
  by_cases hd : p∣t.val.val 1 1
  · obtain ⟨r,hr⟩ := cubicThetaPrimeCubeUpperChart_covers hp t.val hd
    exact ⟨Sum.inr r,hr.trans (cubicThetaPrimeCubeCoset_self p t)⟩
  · obtain ⟨r,hr⟩ := cubicThetaPrimeCubeLowerChart_covers hp t.val hd
    exact ⟨Sum.inl r,hr.trans (cubicThetaPrimeCubeCoset_self p t)⟩

def cubicThetaPrimeCubeChartEquiv {p : Eisenstein} (hp : primaryPrime p) :
    (Residues (p^3) ⊕ cubicThetaPrimeCubeUpperParameter p) ≃ cubicThetaPrimeCubeTransversal p :=
  Equiv.ofBijective (cubicThetaPrimeCubeChart hp)
    ⟨cubicThetaPrimeCubeChart_injective hp,cubicThetaPrimeCubeChart_surjective hp⟩

lemma cubicThetaPrimeCubeTraceTerm_coset (p : Eisenstein) (F : cubicThetaPrimeCubeSections p)
    (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeTraceTerm p F (cubicThetaPrimeCubeCoset p g).val x=
      cubicThetaPrimeCubeTraceTerm p F g x := by
  let C := cubicThetaPrimeCubeTransversal_complement p
  have he := C.equiv_fst_mul_equiv_snd g
  calc
    _ = cubicThetaPrimeCubeTraceTerm p F
        ((C.equiv g).fst.val*(C.equiv g).snd.val) x :=
      (cubicThetaPrimeCubeTraceTerm_left p F (C.equiv g).fst (C.equiv g).snd.val x).symm
    _ = _ := by rw [he]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaIntegralQuotient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaPrincipalConjugateEquiv (δ : SL(2,Eisenstein)) :
    cubicThetaPrincipalGroup ≃ cubicThetaPrincipalGroup where
  toFun := cubicThetaPrincipalConjugate δ
  invFun := cubicThetaPrincipalConjugate δ⁻¹
  left_inv g := by
    apply Subtype.ext
    simp [cubicThetaPrincipalConjugate,mul_assoc]
  right_inv g := by
    apply Subtype.ext
    simp [cubicThetaPrincipalConjugate,mul_assoc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inversion preserves the actual cubic multiplier. Consequently its
pullback acts on genuine automorphic sections, with no new multiplier input. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaInversionConjugate_character (g : cubicThetaPrincipalGroup) :
    cubicThetaKubotaValue (cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹ g)=
      cubicThetaKubotaValue g := by
  obtain ⟨h00,h10⟩ := cubicThetaInversionConjugate_entries g
  rw [cubicThetaKubotaValue_eq_symbol,h00,h10,
    cubicSymbol_neg (cubicThetaPrincipalGroup_diagonal_primary g).2,
    ←cubicThetaKubota_column_switch g,←cubicThetaKubotaValue_eq_symbol]

lemma cubicThetaInversion_intertwine (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    cubicThetaFullInversion • (g • p)=
      cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹ g •
        (cubicThetaFullInversion • p) := by
  change cubicThetaFullInversion • (g.val • p)=
    ((cubicThetaFullInversion⁻¹)⁻¹*g.val*cubicThetaFullInversion⁻¹) • (cubicThetaFullInversion • p)
  rw [inv_inv]
  simp only [←mul_smul,mul_assoc,inv_mul_cancel,mul_one]

def cubicThetaInversionSection (F : CubicThetaSection) : CubicThetaSection :=
  ⟨⟨fun p => F.val (cubicThetaFullInversion • p),
    F.val.continuous.comp (continuous_const_smul cubicThetaFullInversion)⟩,by
      intro g p
      change F.val (cubicThetaFullInversion • (g • p))=
        cubicThetaKubotaValue g*F.val (cubicThetaFullInversion • p)
      rw [cubicThetaInversion_intertwine,F.property,cubicThetaInversionConjugate_character]⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.instMeasurableSpace
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
local instance instAddCommGroupSubtypeContinuousMapCubicThetaPointComplexMemSubmoduleCubicThetaSectionCubicThetaSmoothTests : AddCommGroup cubicThetaSmoothTests := Module.addCommMonoidToAddCommGroup ℂ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeAtkin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubed-prime Atkin involution preserves the original multiplier
on the full Iwahori subgroup; no auxiliary character kernel is needed. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrimeCubeAtkinConjugate {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^3)) : cubicThetaPrimeIwahori (p^3) :=
  ⟨cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹
      (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g),by
    have he := (cubicThetaInversionConjugate_entries
      (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g)).2
    change p^3∣(cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹
      (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g)).val 1 0
    rw [he]
    change p^3∣-(p^3*g.val.val 0 1)
    exact dvd_neg.mpr (dvd_mul_right _ _)⟩

lemma cubicThetaPrimeCubeAtkinConjugate_kubota {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^3)) :
    cubicThetaKubotaValue (cubicThetaPrimeCubeAtkinConjugate hp g).val=
      cubicThetaKubotaValue g.val := by
  change cubicThetaKubotaValue (cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹
    (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g))=_
  rw [cubicThetaInversionConjugate_character]
  exact (cubicThetaPrimeCubeConjugate_kubota hp g).symm

lemma cubicThetaPrimeCubeAtkinConjugate_matrix {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^3)) :
    ((cubicThetaPrimeCubeAtkinConjugate hp g).val.val : Matrix (Fin 2) (Fin 2) Eisenstein)=
      !![g.val.val 1 1,-(g.val.val 1 0/p^3);-p^3*g.val.val 0 1,g.val.val 0 0] := by
  change (((cubicThetaFullInversion⁻¹)⁻¹*
    cubicThetaPrimeConjugatedMatrix (primary_ne_zero (cubicThetaPrimeCube_primary hp)) g*
      cubicThetaFullInversion⁻¹ : SL(2,Eisenstein)) : Matrix (Fin 2) (Fin 2) Eisenstein)=_
  rw [inv_inv,Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]
  simp [cubicThetaFullInversion,cubicThetaPrimeConjugatedMatrix,Matrix.adjugate_fin_two]

theorem cubicThetaPrimeCubeAtkinConjugate_involutive {p : Eisenstein}
    (hp : primaryPrime p) : Function.Involutive (cubicThetaPrimeCubeAtkinConjugate hp) := by
  intro g
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [cubicThetaPrimeCubeAtkinConjugate_matrix]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 1 1)
      (cubicThetaPrimeCubeAtkinConjugate_matrix hp g)
  · have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 1 0)
      (cubicThetaPrimeCubeAtkinConjugate_matrix hp g)
    simp at he ⊢
    rw [he,show -(p^3*g.val.val 0 1)=p^3*(-g.val.val 0 1) by ring,
      mul_div_cancel_left₀ _ (pow_ne_zero 3 hp.2.ne_zero),neg_neg]
  · have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 0 1)
      (cubicThetaPrimeCubeAtkinConjugate_matrix hp g)
    simp at he ⊢
    rw [he]
    linear_combination cubicThetaPrimeIwahori_division (pow_ne_zero 3 hp.2.ne_zero) g
  · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) Eisenstein => M 0 0)
      (cubicThetaPrimeCubeAtkinConjugate_matrix hp g)

def cubicThetaPrimeCubeAtkinMatrix {p : Eisenstein} (hp : primaryPrime p) : SL(2,ℂ) :=
  cubicThetaFullComplex cubicThetaFullInversion*cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)

theorem cubicThetaPrimeCubeAtkinMatrix_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^3)) :
    cubicThetaPrimeCubeAtkinMatrix hp*cubicThetaPrincipalComplex g.val=
      cubicThetaPrincipalComplex (cubicThetaPrimeCubeAtkinConjugate hp g).val*
        cubicThetaPrimeCubeAtkinMatrix hp := by
  have he : cubicThetaPrincipalComplex (cubicThetaPrimeCubeAtkinConjugate hp g).val=
      cubicThetaFullComplex cubicThetaFullInversion*
        cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g)*
          (cubicThetaFullComplex cubicThetaFullInversion)⁻¹ := by
    change cubicThetaFullComplex ((cubicThetaFullInversion⁻¹)⁻¹*
      (cubicThetaPrimeConjugate (cubicThetaPrimeCube_primary hp) g).val*cubicThetaFullInversion⁻¹)=_
    rw [inv_inv,map_mul,map_mul,map_inv]
    rfl
  rw [cubicThetaPrimeCubeAtkinMatrix,mul_assoc,
    cubicThetaPrimeDilation_intertwines (cubicThetaPrimeCube_primary hp) g,he]
  group

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeCoverDomain
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaPrimeCubeCoverDomain (p : Eisenstein) : Set CubicThetaPoint :=
  ⋃ t : cubicThetaPrimeCubeTransversal p,
    (fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeAtkinIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaPrimeCubeAtkinEquiv {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeIwahori (p^3) ≃ cubicThetaPrimeIwahori (p^3) :=
  (cubicThetaPrimeCubeAtkinConjugate_involutive hp).toPerm

lemma cubicThetaPrimeCubeAtkinPoint_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^3)) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeAtkinMatrix hp • (g • x)=
      cubicThetaPrimeCubeAtkinEquiv hp g • (cubicThetaPrimeCubeAtkinMatrix hp • x) := by
  change cubicThetaPrimeCubeAtkinMatrix hp • (cubicThetaPrincipalComplex g.val • x)=
    cubicThetaPrincipalComplex (cubicThetaPrimeCubeAtkinConjugate hp g).val •
      (cubicThetaPrimeCubeAtkinMatrix hp • x)
  rw [←mul_smul,←mul_smul,cubicThetaPrimeCubeAtkinMatrix_intertwines]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeSectionAtkin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restriction and Atkin pullback of actual cubed-prime sections. The
original dilation is exactly Atkin pullback after the global inversion. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeSectionRestrict {p : Eisenstein} (F : CubicThetaSection) :
    cubicThetaPrimeCubeSections p :=
  ⟨F.val,fun g x => F.property g.val x⟩

def cubicThetaPrimeCubeAtkinSection {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p) : cubicThetaPrimeCubeSections p :=
  ⟨⟨fun x => F.val (cubicThetaPrimeCubeAtkinMatrix hp • x),
    F.val.continuous.comp (continuous_const_smul _)⟩,by
    intro g x
    change F.val (cubicThetaPrimeCubeAtkinMatrix hp • (g.val • x))=
      cubicThetaKubotaValue g.val*F.val (cubicThetaPrimeCubeAtkinMatrix hp • x)
    have ht := cubicThetaPrimeCubeAtkinPoint_intertwines hp g x
    change cubicThetaPrimeCubeAtkinMatrix hp • (g.val • x)=
      (cubicThetaPrimeCubeAtkinConjugate hp g).val • (cubicThetaPrimeCubeAtkinMatrix hp • x) at ht
    rw [ht,F.property,cubicThetaPrimeCubeAtkinConjugate_kubota]⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeDegree
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact degree of the cubed-prime correspondence. The second chart
is explicitly identified with the residue ring modulo p^2. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeIwahori_index {p : Eisenstein} (hp : primaryPrime p) :
    (cubicThetaPrimeIwahori (p^3)).index=(normNat p)^3+(normNat p)^2 := by
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Finite (cubicThetaPrimeCubeUpperParameter p) := by
    unfold cubicThetaPrimeCubeUpperParameter
    infer_instance
  rw [←(cubicThetaPrimeCubeTransversal_complement p).card_right,
    ←Nat.card_congr (cubicThetaPrimeCubeChartEquiv hp),Nat.card_sum,
    ←Nat.card_congr (cubicThetaPrimeCubeUpperParameterEquiv hp.2.ne_zero),
    residues_card (pow_ne_zero 3 hp.2.ne_zero),residues_card (pow_ne_zero 2 hp.2.ne_zero)]
  simp [pow_succ,normNat_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeTraceNorm
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaPrimeCubeTrace_norm_sq_le {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p) (x : CubicThetaPoint) :
    ‖(cubicThetaPrimeCubeTraceSection hp F).val x‖^2≤
      ((cubicThetaPrimeIwahori (p^3)).index:ℝ)*
        ∑' t : cubicThetaPrimeCubeTransversal p,‖F.val (t.val • x)‖^2 := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  have he : (cubicThetaPrimeCubeTraceSection hp F).val x=
      ∑' t : cubicThetaPrimeCubeTransversal p,cubicThetaPrimeCubeTraceTerm p F t.val x := rfl
  rw [he,tsum_fintype,tsum_fintype]
  have hn := norm_sum_le Finset.univ (fun t : cubicThetaPrimeCubeTransversal p =>
    cubicThetaPrimeCubeTraceTerm p F t.val x)
  have ht (t : cubicThetaPrimeCubeTransversal p) :
      ‖cubicThetaPrimeCubeTraceTerm p F t.val x‖=‖F.val (t.val • x)‖ := by
    rw [cubicThetaPrimeCubeTraceTerm,norm_mul,norm_star,cubicThetaKubotaValue_norm,one_mul]
  simp_rw [ht] at hn
  have hs := mul_self_le_mul_self (_root_.norm_nonneg _) hn
  rw [←pow_two,←pow_two] at hs
  apply hs.trans
  have hc := sq_sum_le_card_mul_sum_sq (s:=Finset.univ)
    (f:=fun t : cubicThetaPrimeCubeTransversal p => ‖F.val (t.val • x)‖)
  rwa [Finset.card_univ,←Nat.card_eq_fintype_card,
    (cubicThetaPrimeCubeTransversal_complement p).card_right] at hc

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeDilationNorm
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaOriginal_norm_invariant (F : CubicThetaSection)
    (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
    ‖F.val (g • x)‖^2=‖F.val x‖^2 := by
  rw [F.property,norm_mul,cubicThetaKubotaValue_norm,one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeHeckeRegularity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaPrimeCubeHeckeMatrix {p : Eisenstein} (hp : primaryPrime p)
    (t : cubicThetaPrimeCubeTransversal p) :=
  cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)*cubicThetaPrincipalComplex t.val

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeInvariantDilation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaScalarInversion_invariant {f : CubicThetaPoint → ℝ}
    (hi : ∀ (g : cubicThetaPrincipalGroup) x,f (g • x)=f x)
    (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
    f (cubicThetaFullInversion • (g • x))=f (cubicThetaFullInversion • x) := by
  rw [cubicThetaInversion_intertwine,hi]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeEnergyIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaPrimeCubeHeckeMatrix_action {p : Eisenstein} (hp : primaryPrime p)
    (t : cubicThetaPrimeCubeTransversal p) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeHeckeMatrix hp t • x=
      cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • (t.val • x) := by
  rw [cubicThetaPrimeCubeHeckeMatrix,mul_smul]
  rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeHeckeLinear
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linearity of the literal cubed-prime Hecke correspondence, including
its action on actual finite-energy sections. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeHecke_add {p : Eisenstein} (hp : primaryPrime p)
    (F G : CubicThetaSection) :
    cubicThetaPrimeCubeHecke hp (F+G)=cubicThetaPrimeCubeHecke hp F+cubicThetaPrimeCubeHecke hp G := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change (∑' t : cubicThetaPrimeCubeTransversal p,star (cubicThetaKubotaValue t.val)*
    (F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • (t.val • x))+
      G.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • (t.val • x))))=_
  change _ = (cubicThetaPrimeCubeHecke hp F).val x +
    (cubicThetaPrimeCubeHecke hp G).val x
  rw [cubicThetaPrimeCubeHecke_apply, cubicThetaPrimeCubeHecke_apply]
  simp only [tsum_fintype,mul_add,Finset.sum_add_distrib]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootCoverDomain
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

instance cubicThetaPrimeCubeRootCoverGroup_finiteIndex {p : Eisenstein} (hp : primaryPrime p) :
    (cubicThetaPrimeCubeRootCoverGroup hp).FiniteIndex :=
  cubicThetaPrimeCubeRootSubgroup_finiteIndex hp

lemma cubicThetaPrimeCubeRootTransversal_complement {p : Eisenstein} (hp : primaryPrime p) :
    Subgroup.IsComplement (cubicThetaPrimeCubeRootCoverGroup hp) (cubicThetaPrimeCubeRootTransversal hp) :=
  (Classical.choose_spec ((cubicThetaPrimeCubeRootCoverGroup hp).exists_isComplement_right 1)).1

instance cubicThetaPrimeCubeRootTransversal_finite {p : Eisenstein} (hp : primaryPrime p) :
    Finite (cubicThetaPrimeCubeRootTransversal hp) := by
  apply Nat.finite_of_card_ne_zero
  rw [(cubicThetaPrimeCubeRootTransversal_complement hp).card_right]
  exact Subgroup.FiniteIndex.index_ne_zero

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeRootSections
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite-cover section space and its fractional root action. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPrimeRootSectionRestrict {p : Eisenstein} (F : CubicThetaSection) :
    cubicThetaPrimeRootSections p := ⟨F.val,fun g y => F.property g.val y⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootSections
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual sections and their fractional translations at the cube modulus. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootSectionTranslate_add {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (F : cubicThetaPrimeCubeRootSections p) :
    cubicThetaPrimeCubeRootSectionTranslate hp (x+y) F=
      cubicThetaPrimeCubeRootSectionTranslate hp x (cubicThetaPrimeCubeRootSectionTranslate hp y F) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  change F.val (cubicThetaPrimeCubeRootElement hp (x+y) • z)=
    F.val (cubicThetaPrimeCubeRootElement hp y • (cubicThetaPrimeCubeRootElement hp x • z))
  rw [←mul_smul,←cubicThetaPrimeCubeRootElement_add,add_comm]

lemma cubicThetaPrimeCubeRootSectionTranslate_integral {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : cubicThetaPrimeCubeRootSections p) :
    cubicThetaPrimeCubeRootSectionTranslate hp (p^3*x) F=F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  change F.val (cubicThetaPrimeCubeRootElement hp (p^3*x) • y)=F.val y
  rw [cubicThetaPrimeCubeRootElement_integral,cubicThetaPrimeRootSection_integral]

def cubicThetaPrimeCubeRootOperator {p : Eisenstein} (hp : primaryPrime p) (x : Eisenstein) :
    cubicThetaPrimeCubeRootSections p ≃ₗ[ℂ] cubicThetaPrimeCubeRootSections p where
  toFun := cubicThetaPrimeCubeRootSectionTranslate hp x
  invFun := cubicThetaPrimeCubeRootSectionTranslate hp (-x)
  left_inv F := by
    rw [←cubicThetaPrimeCubeRootSectionTranslate_add,neg_add_cancel,
      cubicThetaPrimeCubeRootSectionTranslate_zero]
  right_inv F := by
    rw [←cubicThetaPrimeCubeRootSectionTranslate_add,add_neg_cancel,
      cubicThetaPrimeCubeRootSectionTranslate_zero]
  map_add' _F _G := rfl
  map_smul' _a _F := rfl

theorem cubicThetaPrimeCubeRootOperator_congr {p : Eisenstein} (hp : primaryPrime p)
    {x y : Eisenstein} (hxy : p^3∣x-y) :
    cubicThetaPrimeCubeRootOperator hp x=cubicThetaPrimeCubeRootOperator hp y := by
  obtain ⟨z,hz⟩ := hxy
  have hx : x=y+p^3*z := by linear_combination hz
  apply LinearEquiv.ext
  intro F
  change cubicThetaPrimeCubeRootSectionTranslate hp x F=
    cubicThetaPrimeCubeRootSectionTranslate hp y F
  rw [hx,cubicThetaPrimeCubeRootSectionTranslate_add,cubicThetaPrimeCubeRootSectionTranslate_integral]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootMassTransport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaPrimeCubeRootSection_norm_invariant {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeRootSections p) (g : cubicThetaPrimeCubeRootCoverGroup hp)
    (x : CubicThetaPoint) : ‖F.val (g • x)‖^2=‖F.val x‖^2 := by
  change ‖F.val (g.val • x)‖^2=‖F.val x‖^2
  have hf : F.val (g.val • x)=cubicThetaKubotaValue g.val*F.val x :=
    F.property (⟨g.val,g.property⟩ : cubicThetaPrimeRootSubgroup (p^3)) x
  rw [hf,norm_mul,cubicThetaKubotaValue_norm,one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootLiftL2
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized isometric lifting from the original automorphic Hilbert
space to the actual root cover. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootCoverDegree_pos {p : Eisenstein} (hp : primaryPrime p) :
    0<((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ) :=
  Nat.cast_pos.mpr (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootHeckeCover
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

instance cubicThetaPrimeCubeIwahori_continuous {p : Eisenstein} :
    ContinuousConstSMul (cubicThetaPrimeIwahori (p^3)) CubicThetaPoint where
  continuous_const_smul g := continuous_const_smul g.val

lemma cubicThetaPrimeCubeRoot_le_hecke {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeRootCoverGroup hp ≤ cubicThetaPrimeIwahori (p^3) := by
  intro g hg
  exact (cubicThetaPrimeCubeRootIwahori (⟨g,hg⟩ : cubicThetaPrimeCubeRootSubgroup p)).property

def cubicThetaPrimeCubeRootHeckeSubgroup {p : Eisenstein} (hp : primaryPrime p) :
    Subgroup (cubicThetaPrimeIwahori (p^3)) :=
  (cubicThetaPrimeCubeRootCoverGroup hp).comap (cubicThetaPrimeIwahori (p^3)).subtype

instance cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex {p : Eisenstein} (hp : primaryPrime p) :
    (cubicThetaPrimeCubeRootHeckeSubgroup hp).FiniteIndex := by
  unfold cubicThetaPrimeCubeRootHeckeSubgroup
  exact Subgroup.instFiniteIndex_subgroupOf (cubicThetaPrimeCubeRootCoverGroup hp) (cubicThetaPrimeIwahori (p^3))

def cubicThetaPrimeCubeRootHeckeSubgroupEquiv {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeRootHeckeSubgroup hp ≃* cubicThetaPrimeCubeRootCoverGroup hp where
  toFun h := ⟨h.val.val,h.property⟩
  invFun h := ⟨⟨h.val,cubicThetaPrimeCubeRoot_le_hecke hp h.property⟩,h.property⟩
  left_inv _h := rfl
  right_inv _h := rfl
  map_mul' _h _k := rfl

theorem cubicThetaPrimeCubeRootHecke_index {p : Eisenstein} (hp : primaryPrime p) :
    (cubicThetaPrimeCubeRootHeckeSubgroup hp).index*(cubicThetaPrimeIwahori (p^3)).index=
      (cubicThetaPrimeCubeRootCoverGroup hp).index :=
  Subgroup.relIndex_mul_index (cubicThetaPrimeCubeRoot_le_hecke hp)


def cubicThetaPrimeCubeRootHeckeTransversal {p : Eisenstein} (hp : primaryPrime p) :
    Set (cubicThetaPrimeIwahori (p^3)) :=
  Classical.choose ((cubicThetaPrimeCubeRootHeckeSubgroup hp).exists_isComplement_right 1)

lemma cubicThetaPrimeCubeRootHeckeTransversal_complement {p : Eisenstein} (hp : primaryPrime p) :
    Subgroup.IsComplement (cubicThetaPrimeCubeRootHeckeSubgroup hp) (cubicThetaPrimeCubeRootHeckeTransversal hp) :=
  (Classical.choose_spec ((cubicThetaPrimeCubeRootHeckeSubgroup hp).exists_isComplement_right 1)).1

instance cubicThetaPrimeCubeRootHeckeTransversal_finite {p : Eisenstein} (hp : primaryPrime p) :
    Finite (cubicThetaPrimeCubeRootHeckeTransversal hp) := by
  apply Nat.finite_of_card_ne_zero
  rw [(cubicThetaPrimeCubeRootHeckeTransversal_complement hp).card_right]
  exact Subgroup.FiniteIndex.index_ne_zero

def cubicThetaPrimeCubeRootHeckeDomain {p : Eisenstein} (hp : primaryPrime p) : Set CubicThetaPoint :=
  ⋃ t : cubicThetaPrimeCubeRootHeckeTransversal hp,
    (fun x : CubicThetaPoint => t.val • x) '' (cubicThetaPrimeCubeCoverDomain p)


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootDilation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

def cubicThetaPrimeCubeRootHeckeRestriction {p : Eisenstein} (_hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p) : cubicThetaPrimeCubeRootSections p :=
  ⟨F.val,by
    intro g x
    exact F.property (cubicThetaPrimeCubeRootIwahori g) x⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimeCubeRootDilationFixed
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

lemma cubicThetaPrimeCubeRootDilation_translate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : CubicThetaSection) :
    cubicThetaPrimeCubeRootSectionTranslate hp x
      (cubicThetaPrimeCubeRootHeckeRestriction hp (cubicThetaPrimeCubeDilationSection hp F))=
    cubicThetaPrimeCubeRootHeckeRestriction hp (cubicThetaPrimeCubeDilationSection hp F) := by
  let D := cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)
  have hm : D*cubicThetaPrimeCubeRootElement hp x=
      cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x)*D := by
    dsimp only [D,cubicThetaPrimeCubeRootElement]
    group
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  change F.val (D • (cubicThetaPrimeCubeRootElement hp x • y))=F.val (D • y)
  rw [←mul_smul,hm,mul_smul]
  change F.val (cubicThetaPrincipalTranslation x • (D • y))=_
  rw [F.property,cubicThetaPrincipalTranslation_value,one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryPowerCoordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact support coordinates at each unit and ramified power of a primary
frequency. Changing that unit or exponent preserves the squarefree/cube support. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaCoordinates_primary_power_iff {h : Eisenstein}
    (hh : primary h) (e : Eisensteinˣ) (k : ℕ) :
    Nonempty (CubicThetaCoordinates ((e:Eisenstein)*lambdaE^k*h)) ↔
      ∃ c d : Eisenstein, primary c ∧ primary d ∧ Squarefree c ∧ h=c*d^3 := by
  constructor
  · rintro ⟨R⟩
    exact ⟨R.squarefreePart,R.cubePart,R.squarefree_primary,R.cube_primary,
      R.squarefree,(R.primary_power hh e k).2.2.symm⟩
  · rintro ⟨c,d,hc,hd,hs,he⟩
    exact ⟨{
      unit := e
      order := k
      squarefreePart := c
      cubePart := d
      squarefree_primary := hc
      cube_primary := hd
      squarefree := hs
      numerator_eq := by rw [he] }⟩

theorem cubicThetaCoordinates_primary_support_iff {h : Eisenstein} (hh : primary h)
    (e f : Eisensteinˣ) (k j : ℕ) :
    Nonempty (CubicThetaCoordinates ((e:Eisenstein)*lambdaE^k*h)) ↔
      Nonempty (CubicThetaCoordinates ((f:Eisenstein)*lambdaE^j*h)) := by
  rw [cubicThetaCoordinates_primary_power_iff hh,cubicThetaCoordinates_primary_power_iff hh]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedMissingCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Agreement of the actual and prescribed coefficients in the first
absent ramified class. The frequency index is exactly -lambda*h. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaArithmeticCoefficient_ramified_two {h : Eisenstein}
    (hh : ¬lambdaE ∣ h) : cubicThetaArithmeticCoefficient (lambdaE^2*h)=0 := by
  by_cases hc : Nonempty (CubicThetaCoordinates (lambdaE^2*h))
  · let R := Classical.choice hc
    have hp : primary (R.cubePart^3) := by
      simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using
        primary_mul R.cube_primary (primary_mul R.cube_primary R.cube_primary)
    have he := congrArg (emultiplicity lambdaE) R.numerator_eq
    simp only [emultiplicity_mul lambdaE_prime,
      emultiplicity_pow_self_of_prime lambdaE_prime,emultiplicity_eq_zero.mpr hh,
      unit_lambda_emultiplicity,primary_lambda_emultiplicity R.squarefree_primary,
      primary_lambda_emultiplicity hp,zero_add,add_zero] at he
    have hR : R.order=2 := by exact_mod_cast he.symm
    rw [cubicThetaArithmeticCoefficient_formula R]
    simp only [CubicThetaCoordinates.coefficient,hR]
    norm_num
  · simp only [cubicThetaArithmeticCoefficient,dite_eq_right hc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedPrimaryResidue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The signed-primary selection rule holds for the actual residue and
matches the prescribed coefficient on the same arithmetic frequency. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

theorem cubicThetaArithmeticCoefficient_signed_primary_support
    {h : Eisenstein} (hh : ¬lambdaE ∣ h) (hpos : ¬primary h) (hneg : ¬primary (-h)) :
    cubicThetaArithmeticCoefficient (-lambdaE*h)=0 := by
  by_cases hc : Nonempty (CubicThetaCoordinates (-lambdaE*h))
  · let R := Classical.choice hc
    have hp : primary (R.cubePart^3) := by
      simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using
        primary_mul R.cube_primary (primary_mul R.cube_primary R.cube_primary)
    have hcprim := primary_mul R.squarefree_primary hp
    have hn : ¬lambdaE ∣ -h := fun hd => hh (dvd_neg.mp hd)
    have hi : -lambdaE*h=lambdaE*(-h) := by ring
    have he := (congrArg (emultiplicity lambdaE) hi).symm.trans
      (congrArg (emultiplicity lambdaE) R.numerator_eq)
    have hl : emultiplicity lambdaE lambdaE=1 := by
      simpa only [pow_one,Nat.cast_one] using emultiplicity_pow_self_of_prime lambdaE_prime 1
    simp only [emultiplicity_mul lambdaE_prime,hl,
      emultiplicity_pow_self_of_prime lambdaE_prime,emultiplicity_eq_zero.mpr hn,
      unit_lambda_emultiplicity,primary_lambda_emultiplicity R.squarefree_primary,
      primary_lambda_emultiplicity hp,zero_add,add_zero] at he
    have hR : R.order=1 := by exact_mod_cast he.symm
    have hunit : ¬((R.unit:Eisenstein)=1 ∨ (R.unit:Eisenstein)=-1) := by
      intro hu
      have heq : -h=(R.unit:Eisenstein)*(R.squarefreePart*R.cubePart^3) := by
        apply mul_left_cancel₀ lambdaE_prime.ne_zero
        calc
          _ = -lambdaE*h := by ring
          _ = (R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*R.cubePart^3) :=
            R.numerator_eq
          _ = _ := by rw [hR,pow_one]; ring
      rcases hu with hu | hu
      · apply hneg
        rw [hu,one_mul] at heq
        rw [heq]
        exact hcprim
      · apply hpos
        rw [hu,neg_one_mul] at heq
        rw [neg_inj.mp heq]
        exact hcprim
    rw [cubicThetaArithmeticCoefficient_formula R]
    simp only [CubicThetaCoordinates.coefficient,hR]
    norm_num only [Nat.reduceMod,one_ne_zero,false_and,ite_false]
    simp only [true_and,ite_eq_right hunit]
  · simp only [cubicThetaArithmeticCoefficient,dite_eq_right hc]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaUnitPhaseSymbol
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact matching of the unit phase and supplementary symbol in the
ramified arithmetic theta coefficient. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaUnitPhase_neg (e : Eisensteinˣ) :
    cubicThetaUnitPhase (-e)=cubicThetaUnitPhase e := by
  have hneg : (-(e:Eisenstein))^4=(e:Eisenstein)^4 := by ring
  simp only [cubicThetaUnitPhase,Units.val_neg,hneg]

lemma cubicThetaUnitPhase_omega_power (j : Fin 3) :
    cubicThetaUnitPhase (cubicThetaOmegaUnit^(j:ℕ))=
      cubicThetaNinePhase ((omegaE^(j:ℕ))^2) := by
  have h1 := omegaE_primitive.ne_one (by norm_num : 1<3)
  have h2 := omegaE_primitive.pow_ne_one_of_pos_of_lt (by norm_num : (2:ℕ)≠0)
    (by norm_num : (2:ℕ)<3)
  have h4 : omegaE^4=omegaE := by rw [show 4=3+1 by omega,pow_add,omegaE_cube]; simp
  have h8 : omegaE^8=omegaE^2 := by rw [show 8=3*2+2 by omega,pow_add,pow_mul,omegaE_cube]; simp
  have h21 : omegaE^2≠omegaE := by
    intro he
    have hz : omegaE*(omegaE-1)=0 := by linear_combination he
    rcases mul_eq_zero.mp hz with hz|hz
    · exact (omegaE_primitive.ne_zero (by norm_num)) hz
    · exact h1 (sub_eq_zero.mp hz)
  fin_cases j
  · simp [cubicThetaUnitPhase,cubicThetaOmegaUnit,cubicThetaNinePhase_one]
  · simp only [pow_one,cubicThetaUnitPhase,cubicThetaOmegaUnit,
      Units.val_mkOfMulEqOne,h4,h1,ite_false, if_false,ite_true, if_true]
    exact cubicThetaNinePhase_omega_square.symm
  · simp only [Units.val_pow_eq_pow_val,cubicThetaUnitPhase,
      cubicThetaOmegaUnit,Units.val_mkOfMulEqOne,←pow_mul]
    norm_num only [Nat.reduceMul]
    rw [h8,h4,ite_eq_right h2,ite_eq_right h21]
    exact cubicThetaNinePhase_omega.symm

theorem cubicThetaUnitPhase_eq (e : Eisensteinˣ) :
    cubicThetaUnitPhase e=cubicThetaNinePhase ((e:Eisenstein)^2) := by
  obtain ⟨j,hj|hj⟩ := cubicThetaUnit_signed_power e
  · have he : e=cubicThetaOmegaUnit^(j:ℕ) := Units.ext (by
      simpa only [Units.val_pow_eq_pow_val,cubicThetaOmegaUnit,Units.val_mkOfMulEqOne] using hj)
    simpa only [he,Units.val_pow_eq_pow_val,cubicThetaOmegaUnit,Units.val_mkOfMulEqOne] using
      cubicThetaUnitPhase_omega_power j
  · have he : e=-(cubicThetaOmegaUnit^(j:ℕ)) := Units.ext (by
      simpa only [Units.val_neg,Units.val_pow_eq_pow_val,cubicThetaOmegaUnit,
        Units.val_mkOfMulEqOne] using hj)
    rw [he,cubicThetaUnitPhase_neg]
    simpa only [Units.val_neg,Units.val_pow_eq_pow_val,cubicThetaOmegaUnit,
      Units.val_mkOfMulEqOne,neg_sq] using cubicThetaUnitPhase_omega_power j

theorem cubicThetaNinePhase_unit_primary {h : Eisenstein} (hh : primary h)
    (e : Eisensteinˣ) :
    cubicThetaNinePhase ((e:Eisenstein)^2*h)=
      cubicThetaUnitPhase e*cubicSymbol h ((e:Eisenstein)^4*lambdaE^2) := by
  have hsub : cubicThetaNinePhase (h-1)=cubicThetaNinePhase h := by
    calc
      _ = cubicThetaNinePhase (h-1)*cubicThetaNinePhase 1 := by rw [cubicThetaNinePhase_one,mul_one]
      _ = _ := by rw [←cubicThetaNinePhase_add]; congr 1; ring
  have H (j : Fin 3) : cubicThetaNinePhase ((omegaE^(j:ℕ))^2*h)=
      cubicThetaNinePhase ((omegaE^(j:ℕ))^2)*
        cubicSymbol h ((omegaE^(j:ℕ))^4*lambdaE^2) := by
    rw [cubicSymbol_mul_upper hh,←cubicThetaNinePhase_primary hh,←hsub,
      show (omegaE^(j:ℕ))^4=omegaE^(4*(j:ℕ)) by rw [←pow_mul]; congr 1; omega,
      cubicSymbol_pow_upper hh,cubicThetaUnitCharacter_power hh]
    norm_num only [Nat.cast_mul,Nat.cast_ofNat]
    change cubicThetaNinePhase ((omegaE^(j:ℕ))^2*h)=
      cubicThetaNinePhase ((omegaE^(j:ℕ))^2)*
        (cubicThetaNinePhase (lambdaE*(4*(j:ℕ))*(h-1))*cubicThetaNinePhase (h-1))
    rw [←cubicThetaNinePhase_add,←cubicThetaNinePhase_add]
    apply cubicThetaNinePhase_congr
    obtain ⟨t,ht⟩ := hh
    obtain ⟨b,hb⟩ := cubicThetaUnit_square_congruence j
    refine ⟨b*t,?_⟩
    calc
      _ = ((omegaE^(j:ℕ))^2-1-lambdaE*(4*(j:ℕ)))*(h-1) := by ring
      _ = _ := by rw [hb,ht]; ring
  rw [cubicThetaUnitPhase_eq]
  obtain ⟨j,hj|hj⟩ := cubicThetaUnit_signed_power e
  · rw [hj]; exact H j
  · have hneg : (-(omegaE^(j:ℕ)))^4=(omegaE^(j:ℕ))^4 := by ring
    simpa only [hj,neg_sq,hneg] using H j

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedModel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal arithmetic theta coefficients obey the same exact
ramified phase relation as the actual normalized residue. Zero support is retained. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaArithmeticCoefficient_ramified_parts {c d : Eisenstein}
    (hc : primary c) (hd : primary d) (hs : Squarefree c) (e : Eisensteinˣ) :
    cubicThetaArithmeticCoefficient ((e:Eisenstein)*lambdaE^3*(c*d^3))=
      (1/3:ℂ)*cubicThetaNinePhase ((e:Eisenstein)^2*(c*d^3))*
        cubicThetaArithmeticCoefficient (lambdaE*(c*d^3)) := by
  let R : CubicThetaCoordinates ((e:Eisenstein)*lambdaE^3*(c*d^3)) := {
    unit := e
    order := 3
    squarefreePart := c
    cubePart := d
    squarefree_primary := hc
    cube_primary := hd
    squarefree := hs
    numerator_eq := rfl }
  have hp : primary (c*d^3) := primary_mul hc (by
    simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using
      primary_mul hd (primary_mul hd hd))
  rw [cubicThetaArithmeticCoefficient_formula R,
    cubicThetaNinePhase_unit_primary hp,cubicThetaSymbol_primary_cube_part hc hd,
    show lambdaE*(c*d^3)=lambdaE*c*d^3 by ring,
    cubicThetaArithmeticCoefficient_primary hc hd hs]
  norm_num [R,CubicThetaCoordinates.coefficient,CubicThetaCoordinates.amplitude,
    cubicThetaTwistedGauss,star_mul]
  ring

theorem cubicThetaArithmeticCoefficient_ramified_primary {h : Eisenstein}
    (hh : primary h) (e : Eisensteinˣ) :
    cubicThetaArithmeticCoefficient ((e:Eisenstein)*lambdaE^3*h)=
      (1/3:ℂ)*cubicThetaNinePhase ((e:Eisenstein)^2*h)*
        cubicThetaArithmeticCoefficient (lambdaE*h) := by
  classical
  by_cases hR : Nonempty (CubicThetaCoordinates ((1:Eisenstein)*lambdaE^1*h))
  · obtain ⟨c,d,hc,hd,hs,he⟩ := (cubicThetaCoordinates_primary_power_iff hh 1 1).mp hR
    rw [he]
    exact cubicThetaArithmeticCoefficient_ramified_parts hc hd hs e
  · have hL : ¬Nonempty (CubicThetaCoordinates ((e:Eisenstein)*lambdaE^3*h)) :=
      mt (cubicThetaCoordinates_primary_support_iff hh e 1 3 1).mp hR
    have hB : ¬Nonempty (CubicThetaCoordinates (lambdaE*h)) := by
      simpa only [one_mul,pow_one] using hR
    simp only [cubicThetaArithmeticCoefficient,dite_eq_right hL,dite_eq_right hB,mul_zero]

theorem cubicThetaArithmeticCoefficient_ramified_signed {h : Eisenstein}
    (hh : primary h) (e : Eisensteinˣ) :
    cubicThetaArithmeticCoefficient (-lambdaE*(lambdaE^2*(h*(e:Eisenstein))))=
      (1/3:ℂ)*cubicThetaNinePhase ((e:Eisenstein)^2*h)*
        cubicThetaArithmeticCoefficient (-lambdaE*h) := by
  rw [show -lambdaE*(lambdaE^2*(h*(e:Eisenstein)))=
    -((e:Eisenstein)*lambdaE^3*h) by ring,
    cubicThetaArithmeticCoefficient_even,cubicThetaArithmeticCoefficient_ramified_primary hh,
    neg_mul,cubicThetaArithmeticCoefficient_even]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedCoefficientSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removal of a ramified cube preserves arithmetic support. This
extends the coordinate scaling to the literal zero-extended coefficient. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaCoordinates_lambdaCube_iff (n : Eisenstein) :
    Nonempty (CubicThetaCoordinates (lambdaE^3*n)) ↔ Nonempty (CubicThetaCoordinates n) := by
  constructor
  · rintro ⟨R⟩
    exact ⟨R.removeLambdaCube⟩
  · rintro ⟨R⟩
    exact ⟨R.mulLambdaCube⟩

theorem cubicThetaArithmeticCoefficient_lambdaCube {n : Eisenstein} (hn : lambdaE∣n) :
    cubicThetaArithmeticCoefficient (lambdaE^3*n)=(1/3:ℂ)*cubicThetaArithmeticCoefficient n := by
  classical
  by_cases hR : Nonempty (CubicThetaCoordinates n)
  · let R := Classical.choice hR
    rw [cubicThetaArithmeticCoefficient_formula R.mulLambdaCube,
      cubicThetaArithmeticCoefficient_formula R,R.coefficient_mulLambdaCube (R.order_pos hn)]
  · have hC := mt (cubicThetaCoordinates_lambdaCube_iff n).mp hR
    simp only [cubicThetaArithmeticCoefficient,dite_eq_right hR,dite_eq_right hC,mul_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaShiftedLattice
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Put the translated-cusp coefficients on the common lambda^-4 lattice.
The congruence restriction forces the apparent larger lattice to collapse. -/
noncomputable section
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

/-- The actual translated-cusp coefficient, with the single global residue
scalar removed. This is derived, not postulated as a new theta family. -/
def cubicThetaShiftedLatticeCoefficient (n : ℤ) (k : Eisenstein) : ℂ :=
  if lambdaE ∣ k-(n:Eisenstein) then 3*cubicThetaArithmeticCoefficient (3*(lambdaE*k)) else 0

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryBottom
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A full integral matrix with primary lower-left entry reduces to an
actual translated inversion through a principal-level matrix. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaPrimaryBottomSeed (g : SL(2,Eisenstein)) : SL(2,Eisenstein) :=
  cubicThetaShiftedInversion (g 0 0)*cubicThetaFullTranslation (g 1 1)

def cubicThetaPrimaryBottomDefect (g : SL(2,Eisenstein)) : SL(2,Eisenstein) :=
  g*(cubicThetaPrimaryBottomSeed g)⁻¹

lemma cubicThetaPrimaryBottomSeed_matrix (g : SL(2,Eisenstein)) :
    (cubicThetaPrimaryBottomSeed g).val=!![g 0 0,g 0 0*g 1 1-1;1,g 1 1] := by
  change (!![g 0 0,-1;1,0] : Matrix (Fin 2) (Fin 2) Eisenstein)*!![1,g 1 1;0,1]=_
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two,sub_eq_add_neg]

lemma cubicThetaPrimaryBottomDefect_matrix (g : SL(2,Eisenstein)) :
    (cubicThetaPrimaryBottomDefect g).val=
      !![1+g 0 1*(g 1 0-1),-g 0 0*g 0 1*(g 1 0-1);
        g 1 1*(g 1 0-1),1+(1-g 0 0*g 1 1)*(g 1 0-1)] := by
  have hg : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.property
  rw [cubicThetaPrimaryBottomDefect,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv,cubicThetaPrimaryBottomSeed_matrix]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  all_goals simp only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.adjugate_fin_two]
  all_goals dsimp
  · change g 0 0*g 1 1+g 0 1*(-1)=1+g 0 1*(g 1 0-1)
    linear_combination hg
  · change g 0 0*(-(g 0 0*g 1 1-1))+g 0 1*g 0 0= -g 0 0*g 0 1*(g 1 0-1)
    linear_combination -g 0 0*hg
  · change g 1 0*g 1 1+g 1 1*(-1)=g 1 1*(g 1 0-1)
    ring
  · change g 1 0*(-(g 0 0*g 1 1-1))+g 1 1*g 0 0=1+(1-g 0 0*g 1 1)*(g 1 0-1)
    ring

lemma cubicThetaPrimaryBottomDefect_mem (g : SL(2,Eisenstein)) (hc : primary (g 1 0)) :
    cubicThetaPrimaryBottomDefect g∈cubicThetaPrincipalGroup := by
  apply (cubicThetaPrincipalGroup_mem_iff _).mpr
  have he := cubicThetaPrimaryBottomDefect_matrix g
  change primary ((cubicThetaPrimaryBottomDefect g).val 0 0) ∧
    (3:Eisenstein)∣(cubicThetaPrimaryBottomDefect g).val 0 1 ∧
    (3:Eisenstein)∣(cubicThetaPrimaryBottomDefect g).val 1 0 ∧
    primary ((cubicThetaPrimaryBottomDefect g).val 1 1)
  rw [he]
  change (3:Eisenstein)∣(1+g 0 1*(g 1 0-1))-1 ∧
    (3:Eisenstein)∣-g 0 0*g 0 1*(g 1 0-1) ∧
    (3:Eisenstein)∣g 1 1*(g 1 0-1) ∧
    (3:Eisenstein)∣(1+(1-g 0 0*g 1 1)*(g 1 0-1))-1
  obtain ⟨t,ht⟩ := hc
  refine ⟨⟨g 0 1*t,?_⟩,⟨-g 0 0*g 0 1*t,?_⟩,⟨g 1 1*t,?_⟩,
    ⟨(1-g 0 0*g 1 1)*t,?_⟩⟩ <;> rw [ht] <;> ring

def cubicThetaPrimaryBottomPrincipal (g : SL(2,Eisenstein)) (hc : primary (g 1 0)) :
    cubicThetaPrincipalGroup := ⟨cubicThetaPrimaryBottomDefect g,cubicThetaPrimaryBottomDefect_mem g hc⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaActualCuspCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal constant and nonconstant coefficients of the three actual
cusp types, and their conjugates on the common frequency lattice. -/
noncomputable section
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaActualCuspCoefficient (n : ℤ) : Eisenstein → ℂ :=
  if (3:ℤ) ∣ n then cubicThetaArithmeticCoefficient else cubicThetaShiftedLatticeCoefficient n

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaActualProjection
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual primary projector and its finite transformed cusp family. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaCuspIndex (b : Eisenstein) : ℤ := coordinatesEquiv.symm b 1

lemma cubicThetaFullTranslation_mul_bottom (b : Eisenstein) (g : SL(2,Eisenstein)) :
    (cubicThetaFullTranslation b*g) 1 0=g 1 0 ∧
      (cubicThetaFullTranslation b*g) 1 1=g 1 1 := by
  change ((!![1,b;0,1] : Matrix (Fin 2) (Fin 2) Eisenstein)*g.val) 1 0=g 1 0 ∧
    ((!![1,b;0,1] : Matrix (Fin 2) (Fin 2) Eisenstein)*g.val) 1 1=g 1 1
  constructor <;> simp [Matrix.mul_apply,Fin.sum_univ_two]

def cubicThetaProjectedCuspMatrix (g : SL(2,Eisenstein)) (j : Fin 3) : SL(2,Eisenstein) :=
  cubicThetaFullTranslation ((j.val:Eisenstein)*omegaE)*g

lemma cubicThetaProjectedCuspMatrix_primary (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (j : Fin 3) : primary (cubicThetaProjectedCuspMatrix g j 1 0) := by
  rw [cubicThetaProjectedCuspMatrix,(cubicThetaFullTranslation_mul_bottom _ g).1]
  exact hc

def cubicThetaProjectedCuspMultiplier (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (j : Fin 3) : ℂ :=
  cubicThetaKubotaValue (cubicThetaPrimaryBottomPrincipal (cubicThetaProjectedCuspMatrix g j)
    (cubicThetaProjectedCuspMatrix_primary g hc j))

def cubicThetaProjectedCuspType (g : SL(2,Eisenstein)) (j : Fin 3) : ℤ :=
  cubicThetaCuspIndex (cubicThetaProjectedCuspMatrix g j 0 0)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticModelEnergy
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact horizontal energy of the arithmetic residue model.
This retains the common scalar for its remaining normalization. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

def cubicThetaArithmeticFourierEnergy (v : ℝ) : ℝ :=
  ∑' h : Eisenstein,‖cubicThetaArithmeticRowTerm 0 v h‖^2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaProjectedCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite primary projector gives an explicit dual coefficient
family, with absolute convergence and its actual constant term. -/
noncomputable section
open scoped BigOperators MatrixGroups
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaProjectedCoefficient (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (k : Eisenstein) : ℂ :=
  (∑ j : Fin 3, omega^j.val*star (cubicThetaProjectedCuspMultiplier g hc j)*
    star (cubicThetaActualCuspCoefficient (cubicThetaProjectedCuspType g j) (-k)))/3

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMellinReciprocity
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mellin continuation of the actual arithmetic theta expansion.
The undetermined constant-to-Fourier ratio remains visible in both residues. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaArithmeticAxis (v : ℝ) : ℂ :=
  cubicThetaNonconstant cubicThetaArithmeticCoefficient (0,v)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoefficientMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Initial Mellin identity for the actual selected and projected
coefficient families, with their horizontal phases retained. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaCoefficientTwist (a : Eisenstein→ℂ) (z : ℂ) (n : Eisenstein) : ℂ :=
  a n*(Real.fourierChar (tracePair (cubicThetaFrequency n) z):ℂ)

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

def cubicThetaPrimaryCuspCenter (g : SL(2,Eisenstein)) : ℂ := (g 0 0:ℂ)/(g 1 0:ℂ)

def cubicThetaPrimaryDualCenter (g : SL(2,Eisenstein)) : ℂ :=
  (g 1 1:ℂ)-(g 1 1:ℂ)/(g 1 0:ℂ)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAxisDerivativeBalance
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inversion fixes the axis derivative at height one. A negative real
arithmetic derivative determines the remaining sign of the base scalar. -/
noncomputable section
open Filter Set
open scoped Topology
namespace CubicFirstMoment

def cubicThetaArithmeticAxisDerivative (v : ℝ) : ℂ :=
  ∑' n : Eisenstein,cubicThetaSeriesTermVertical cubicThetaArithmeticCoefficient 0 v n

end CubicFirstMoment

end

end OAI
end


