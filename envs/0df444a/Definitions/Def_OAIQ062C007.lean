-- Prove2me | Definitions.Def_OAIQ062C007
-- name    : OAIQ062C007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T00:06:24.615992+00:00
-- url     : https://prove2.me/theorems/3e239f41-0333-42dd-89e9-194e00d7c7f1
-- title:
--   Definitions bundle OAIQ062C007 of the split of OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NeutralAtom.generalized_outer_radii`, carved from OpenAI's openai/math development (OpenAI, *Generalized outer-electron radii of neutral Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 167 declarations of OpenAI's Lean: 40 definitions, 4 inductive types or structures, 1 instance and 122 theorems. The definitions and types are `OAI.Coulomb.atomicCross`, `OAI.Coulomb.atomicInnerField`, `OAI.Coulomb.atomicKineticFormula`, `OAI.Coulomb.atomicRefinedError`, `OAI.Coulomb.atomicRefinedFormula`, `OAI.Coulomb.bindingCut`, `OAI.Coulomb.bindingLocalized`, `OAI.Coulomb.configurationBox`, `OAI.Coulomb.deletionShell`, `OAI.Coulomb.deletionShellWeight`, `OAI.Coulomb.exteriorCut`, `OAI.Coulomb.flatOneBodyDensity`, `OAI.Coulomb.imsShell`, `OAI.Coulomb.innerLocalCap`, `OAI.Coulomb.innerMeshCap`, `OAI.Coulomb.nearPotential`, `OAI.Coulomb.nearWeight`, `OAI.Coulomb.oneBodyDensity`, `OAI.Coulomb.outerDeletionField`, `OAI.Coulomb.particleInnerExterior`, `OAI.Coulomb.radialTailPotential`, `OAI.Coulomb.rawRMS`, `OAI.Coulomb.reciprocalCoefficient`, `OAI.Coulomb.regularizedUCoefficient`, `OAI.Coulomb.rootReciprocalCoefficient`, `OAI.Coulomb.tfPotentialEvaluation`, `OAI.Coulomb.weightedInnerField`, `OAI.NeutralAtom.InitialPropagationData`, `OAI.NeutralAtom.NuclearRandomDatum`, `OAI.NeutralAtom.PropagationDatum`, `OAI.NeutralAtom.PropagationDatum.posteriorStep`, `OAI.NeutralAtom.PropagationInvariant`, `OAI.NeutralAtom.asH1`, `OAI.NeutralAtom.fromH1Gradient`, `OAI.NeutralAtom.fromH1Wave`, `OAI.NeutralAtom.initialPropagationDatum`, `OAI.NeutralAtom.observationArrayPositions`, `OAI.NeutralAtom.observationCoordinateData`, `OAI.NeutralAtom.observationSingleScale`, `OAI.NeutralAtom.physical_family_of_data` and 4 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CoulombRadii_FieldAnalysis_AtomicGapScale`, `CoulombRadii_FieldAnalysis_AtomicWeighted`, `CoulombRadii_FieldAnalysis_BodyCoefficient`, `CoulombRadii_FieldAnalysis_CoulombTest`, `CoulombRadii_FieldAnalysis_FermionicNear`, `CoulombRadii_FieldAnalysis_FlatBodyDensity`, `CoulombRadii_FieldAnalysis_GridIndex`, `CoulombRadii_FieldAnalysis_GroupFermionicCoefficients`, `CoulombRadii_FieldAnalysis_OuterJoinConfiguration`, `CoulombRadii_FieldAnalysis_RawRMS`, `CoulombRadii_FieldAnalysis_RotatedDensityPower`, `CoulombRadii_FieldAnalysis_SliceExpectation`, `CoulombRadii_FieldAnalysis_TailClosure`, `CoulombRadii_FieldAnalysis_WeightedInner`, `CoulombRadii_FormDomain_AtomicPhysicalKinetic`, `CoulombRadii_FormDomain_PatchErrors`, `CoulombRadii_FormDomain_RegularizedKinetic`, `CoulombRadii_Localization_DeletionEnvelope`, `CoulombRadii_Localization_ExteriorCut`, `CoulombRadii_Localization_ShellIMS`, `CoulombRadii_Localization_TotalDeletion`, `CoulombRadii_Packets_InnerMeshCap`, `CoulombRadii_Packets_TailMoment`, `CoulombRadii_Propagation_InitialDatum`, `CoulombRadii_Propagation_InitialInvariant`, `CoulombRadii_Propagation_NearActiveMaximum`, `CoulombRadii_Propagation_PosteriorPropagationData`, `CoulombRadii_Propagation_PropagationAverageAE`, `CoulombRadii_Propagation_PropagationBarrierBounds`, `CoulombRadii_Propagation_PropagationBarrierOffset`, `CoulombRadii_Propagation_PropagationDatumRegularity`, `CoulombRadii_Propagation_PropagationMaximum`, `CoulombRadii_Propagation_PropagationPosteriorStep`, `CoulombRadii_Propagation_PropagationRegularity`, `CoulombRadii_Propagation_PropagationStepWeak`, `CoulombRadii_Propagation_RetainedGoodEvent`, `CoulombRadii_RandomFields_ObservationAnnulusTail`, `CoulombRadii_RandomFields_ObservationMatching`, `CoulombRadii_RandomFields_PhysicalLikelihoodBridge`, `CoulombRadii_RandomFields_PhysicalRetainedLikelihood`, `CoulombRadii_RandomFields_PosteriorDataMeasurable`, `CoulombRadii_RandomFields_PosteriorDensityContinuity`, `CoulombRadii_RandomFields_QuantumRetainedFamily`, `CoulombRadii_Screening_CountScalar`, `CoulombRadii_Screening_CountUnits`, `CoulombRadii_Screening_FineCountTest`, `CoulombRadii_Screening_InnerCap`, `CoulombRadii_Screening_ScaledTest`, `CoulombRadii_Screening_SharpThinScreening`, `CoulombRadii_SpectralTheory_BindingCut`, `CoulombRadii_ThomasFermi_AtomicRefinedGap`, `CoulombRadii_ThomasFermi_PhysicalCount`, `CoulombRadii_ThomasFermi_QuantumProfileDatum`, `CoulombRadii_ThomasFermi_TFCountTest`, `CoulombRadii_ThomasFermi_TFPotentialParameter`, `CoulombRadii_ThomasFermi_TFResponseMargins`, `CoulombRadii_ThomasFermi_TfExtendNonneg`, `CoulombRadii_Variational_PhysicalBridge`.
--
--   **Imports.** It imports the published bundle `Def_CoulombRadii`; the bundles `OAIQ062C003`, `OAIQ062C004` and `OAIQ062C005` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ062C008`; the statement `OAI.NeutralAtom.atomic_global_master_potential`; the proofs of `OAI.Coulomb.atom_strict_binding_attained`, `OAI.Coulomb.strictly_bound_sequence_tight`, `OAI.NeutralAtom.atomic_global_master_potential` and `OAI.NeutralAtom.physical_initial_event`.
-- source:
--   OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C003
import Definitions.Def_OAIQ062C004
import Definitions.Def_OAIQ062C005

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_GroupFermionicCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Coulomb

open scoped Classical

open scoped Classical

open Filter
open scoped Convolution
open ContinuousLinearMap

lemma groupNeumannLower_uniform {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (g : Fin n → ι) (b : ℝ) :
    (b⁻¹)^2 * thomasFermiCoefficient * groupLeadingCount g -
      (b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n : ℝ)^(4/3 : ℝ) ≤
      groupNeumannLower g b := by
  unfold groupNeumannLower groupLeadingCount
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, mul_assoc]
  have H := sum_fiber_power_le g (p := (4/3 : ℝ)) (by norm_num)
  have hC : 0 ≤ ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary)) := by
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (by positivity) neumannBoundary_nonneg)
  nlinarith [mul_le_mul_of_nonneg_left H hC]

lemma grid_hasSum_mass {n : ℕ} (ψ : H1Vector n) {b : ℝ} (hb : 0 < b) :
    HasSum (fun k : GridAssignment n => cubeMass (ψ.translate (gridShift b k)) b)
      (mass ψ) := by
  unfold cubeMass mass
  exact hasSum_sum (fun s _ => gridShift_hasSum_integral hb
    ((ψ.value_L2 s).integrable_norm_pow (p := 2) (by decide)))

lemma grid_hasSum_kinetic {n : ℕ} (ψ : H1Vector n) {b : ℝ} (hb : 0 < b) :
    HasSum (fun k : GridAssignment n => cubeKinetic (ψ.translate (gridShift b k)) b)
      (kinetic ψ) := by
  unfold cubeKinetic kinetic
  exact (hasSum_sum (fun s _ => hasSum_sum (fun i _ => gridShift_hasSum_integral hb
    ((ψ.partial_L2 s i).integrable_norm_pow (p := 2) (by decide))))).mul_left (1/2 : ℝ)

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_GridIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Coulomb
open scoped Classical
open scoped Classical
open Filter
open scoped Convolution
open ContinuousLinearMap

lemma cubeMass_nonneg {n : ℕ} (ψ : H1Vector n) (b : ℝ) : 0 ≤ cubeMass ψ b :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))

lemma grid_leading_summable {n : ℕ} (ψ : H1Vector n) {b : ℝ} (hb : 0 < b) :
    Summable (fun k : GridAssignment n =>
      gridLeadingCount k * cubeMass (ψ.translate (gridShift b k)) b) := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (groupLeadingCount_nonneg _) (cubeMass_nonneg _ _))
    (fun k => mul_le_mul_of_nonneg_right (groupLeadingCount_le _) (cubeMass_nonneg _ _))
    ((grid_hasSum_mass ψ hb).summable.mul_left ((n : ℝ)^(5/3 : ℝ)))

lemma grid_leading_expectation {n : ℕ} (ψ : H1Vector n) {b : ℝ} (hb : 0 < b) :
    (∑' k : GridAssignment n,
      gridLeadingCount k * cubeMass (ψ.translate (gridShift b k)) b) =
    ∑ s, ∫ x : (Fin n × Fin 3) → ℝ,
      gridLeadingCount (gridIndex b x) * ‖ψ.value s (WithLp.toLp 2 x)‖^2 := by
  have Hs (s : Spins n) := gridBox_hasSum_weighted hb
    (gridLeadingCount (n := n))
    (fun k => by
      change ‖groupLeadingCount _‖ ≤ (n : ℝ)^(5/3 : ℝ)
      rw [Real.norm_of_nonneg (groupLeadingCount_nonneg _)]
      exact groupLeadingCount_le _)
    (((ψ.value_L2 s).comp_measurePreserving
      (PiLp.volume_preserving_toLp (Fin n × Fin 3))).integrable_norm_pow (p := 2) (by decide))
  simp only [gridBox_integral_eq_cube, Function.comp_apply, WithLp.toLp_add] at Hs
  have H := hasSum_sum (fun s (_ : s ∈ (Finset.univ : Finset (Spins n))) => Hs s)
  convert H.tsum_eq using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext k
  unfold cubeMass H1Vector.translate gridShift
  rw [Finset.mul_sum]

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_RotatedDensityPower
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.instIsHaarMeasureSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure_1 _root_.OAI.Coulomb.instIsMulLeftInvariantSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure_1 _root_.OAI.Coulomb.instIsMulRightInvariantSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure_1 _root_.OAI.Coulomb.instIsProbabilityMeasureSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
namespace Coulomb

lemma rotation_configuration_continuous {n : ℕ} :
    Continuous (fun p : Rotation × Configuration n => commonIsometry (rotationIsometry p.1) p.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro ij
  have hs : Continuous (fun p : Rotation × Configuration n => (p.1, position p.2 ij.1)) :=
    continuous_fst.prodMk ((continuous_position ij.1).comp continuous_snd)
  have hc := rotation_action_continuous.comp hs
  have H := (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) ij.2).comp hc
  exact H

end Coulomb

open MeasureTheory Set
open scoped BigOperators Matrix ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_OuterJoinConfiguration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma mass_outerSlice_ae {m k : ℕ} (ψ : H1Vector (k+m)) (s : Spins m) :
    (fun x => mass (ψ.outerSlice s x)) =ᵐ[volume]
      fun x => ∑ t : Spins k, ∫ y, ‖ψ.value (outerAppend s t) (outerJoinConfiguration m k (x,y))‖^2 := by
  filter_upwards [ψ.outerSliceRegular_ae s] with x hx
  simp only [mass, ψ.outerSlice_value s hx]

lemma mass_outerSlice_integrable {m k : ℕ} (ψ : H1Vector (k+m)) (s : Spins m) :
    Integrable (fun x => mass (ψ.outerSlice s x)) := by
  apply Integrable.congr _ (mass_outerSlice_ae ψ s).symm
  apply integrable_finsetSum
  intro t _
  have h := ((ψ.value_L2 (outerAppend s t)).comp_measurePreserving
    (outerJoinConfiguration_measurePreserving m k)).integrable_norm_pow (p := 2) (by decide)
  exact h.integral_prod_left

lemma integral_mass_outerSlice {m k : ℕ} (ψ : H1Vector (k+m)) :
    (∑ s : Spins m, ∫ x, mass (ψ.outerSlice s x)) = mass ψ := by
  calc
    _ = ∑ s : Spins m, ∑ t : Spins k, ∫ z, ‖ψ.value (outerAppend s t) z‖^2 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [integral_congr_ae (mass_outerSlice_ae ψ s), integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro t _
        have h := ((ψ.value_L2 (outerAppend s t)).comp_measurePreserving
          (outerJoinConfiguration_measurePreserving m k)).integrable_norm_pow (p := 2) (by decide)
        change Integrable (fun z : Configuration m × Configuration k =>
          ‖ψ.value (outerAppend s t) (outerJoinConfiguration m k z)‖^2) (volume.prod volume) at h
        rw [← integral_prod _ h]
        exact (outerJoinConfiguration_measurePreserving m k).integral_comp'
          (fun z => ‖ψ.value (outerAppend s t) z‖^2)
      · intro t _
        exact (((ψ.value_L2 (outerAppend s t)).comp_measurePreserving
          (outerJoinConfiguration_measurePreserving m k)).integrable_norm_pow
            (p := 2) (by decide)).integral_prod_left
    _ = mass ψ := by
      rw [← Fintype.sum_prod_type (f := fun st : Spins m × Spins k =>
        ∫ z, ‖ψ.value (outerAppend st.1 st.2) z‖^2)]
      exact Fintype.sum_equiv (outerAppendEquiv m k) _ _ (fun _ => rfl)

lemma kinetic_outerSlice_ae {m k : ℕ} (ψ : H1Vector (k+m)) (s : Spins m) :
    (fun x => kinetic (ψ.outerSlice s x)) =ᵐ[volume]
      fun x => (1/2 : ℝ) * ∑ t : Spins k, ∑ a : Fin k × Fin 3,
        ∫ y, ‖ψ.gradient (outerAppend s t) (Fin.castAdd m a.1,a.2)
          (outerJoinConfiguration m k (x,y))‖^2 := by
  filter_upwards [ψ.outerSliceRegular_ae s] with x hx
  simp only [kinetic, ψ.outerSlice_gradient s hx]

lemma kinetic_outerSlice_integrable {m k : ℕ} (ψ : H1Vector (k+m)) (s : Spins m) :
    Integrable (fun x => kinetic (ψ.outerSlice s x)) := by
  apply Integrable.congr _ (kinetic_outerSlice_ae ψ s).symm
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro t _
  apply integrable_finsetSum
  intro a _
  exact (((ψ.partial_L2 (outerAppend s t) (Fin.castAdd m a.1,a.2)).comp_measurePreserving
    (outerJoinConfiguration_measurePreserving m k)).integrable_norm_pow (p := 2) (by decide)).integral_prod_left

lemma integral_kinetic_outerSlice {m k : ℕ} (ψ : H1Vector (k+m)) :
    (∑ s : Spins m, ∫ x, kinetic (ψ.outerSlice s x)) =
      (1/2 : ℝ) * ∑ st : Spins (k+m), ∑ a : Fin k × Fin 3,
        ∫ z, ‖ψ.gradient st (Fin.castAdd m a.1,a.2) z‖^2 := by
  have hs (s : Spins m) : (∫ x, kinetic (ψ.outerSlice s x)) =
      (1/2 : ℝ) * ∑ t : Spins k, ∑ a : Fin k × Fin 3,
        ∫ z, ‖ψ.gradient (outerAppend s t) (Fin.castAdd m a.1,a.2) z‖^2 := by
    rw [integral_congr_ae (kinetic_outerSlice_ae ψ s), integral_const_mul]
    congr 1
    have hi (t : Spins k) (a : Fin k × Fin 3) :
        Integrable (fun z : Configuration m × Configuration k =>
          ‖ψ.gradient (outerAppend s t) (Fin.castAdd m a.1,a.2) (outerJoinConfiguration m k z)‖^2)
          (volume.prod volume) :=
      ((ψ.partial_L2 (outerAppend s t) (Fin.castAdd m a.1,a.2)).comp_measurePreserving
        (outerJoinConfiguration_measurePreserving m k)).integrable_norm_pow (p := 2) (by decide)
    rw [integral_finsetSum _ (fun t _ => integrable_finsetSum _ (fun a _ => (hi t a).integral_prod_left))]
    apply Finset.sum_congr rfl
    intro t _
    rw [integral_finsetSum _ (fun a _ => (hi t a).integral_prod_left)]
    apply Finset.sum_congr rfl
    intro a _
    rw [← integral_prod _ (hi t a)]
    exact (outerJoinConfiguration_measurePreserving m k).integral_comp'
      (fun z => ‖ψ.gradient (outerAppend s t) (Fin.castAdd m a.1,a.2) z‖^2)
  simp_rw [hs]
  rw [← Finset.mul_sum, ← Fintype.sum_prod_type (f := fun st : Spins m × Spins k =>
    ∑ a : Fin k × Fin 3, ∫ z, ‖ψ.gradient (outerAppend st.1 st.2) (Fin.castAdd m a.1,a.2) z‖^2)]
  congr 1
  exact Fintype.sum_equiv (outerAppendEquiv m k) _ _ (fun _ => rfl)

lemma potentialForm_outerSlice_ae {m k : ℕ} (ψ : H1Vector (k+m)) (s : Spins m)
    (V : Configuration k → ℝ) :
    (fun x => potentialForm V (ψ.outerSlice s x)) =ᵐ[volume]
      fun x => ∑ t : Spins k, ∫ y, V y * ‖ψ.value (outerAppend s t) (outerJoinConfiguration m k (x,y))‖^2 := by
  filter_upwards [ψ.outerSliceRegular_ae s] with x hx
  simp only [potentialForm, ψ.outerSlice_value s hx]

lemma potentialForm_outerSlice_integrable {m k : ℕ} (ψ : H1Vector (k+m)) (s : Spins m)
    (V : Configuration k → ℝ)
    (hV : ∀ t : Spins k, Integrable (fun z => V ((outerJoinConfiguration m k).symm z).2 *
      ‖ψ.value (outerAppend s t) z‖^2)) :
    Integrable (fun x => potentialForm V (ψ.outerSlice s x)) := by
  apply Integrable.congr _ (potentialForm_outerSlice_ae ψ s V).symm
  apply integrable_finsetSum
  intro t _
  have H := ((outerJoinConfiguration_measurePreserving m k).integrable_comp_emb
    (outerJoinConfiguration m k).toHomeomorph.toMeasurableEquiv.measurableEmbedding).mpr (hV t)
  have H' : Integrable (fun z : Configuration m × Configuration k =>
      V z.2 * ‖ψ.value (outerAppend s t) (outerJoinConfiguration m k z)‖^2) (volume.prod volume) := by
    change Integrable (fun z : Configuration m × Configuration k =>
      V ((outerJoinConfiguration m k).symm (outerJoinConfiguration m k z)).2 *
        ‖ψ.value (outerAppend s t) (outerJoinConfiguration m k z)‖^2) (volume.prod volume) at H
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using H
  exact H'.integral_prod_left

lemma integral_potentialForm_outerSlice {m k : ℕ} (ψ : H1Vector (k+m))
    (V : Configuration k → ℝ)
    (hV : ∀ st : Spins (k+m), Integrable (fun z => V ((outerJoinConfiguration m k).symm z).2 *
      ‖ψ.value st z‖^2)) :
    (∑ s : Spins m, ∫ x, potentialForm V (ψ.outerSlice s x)) =
      ∑ st : Spins (k+m), ∫ z, V ((outerJoinConfiguration m k).symm z).2 * ‖ψ.value st z‖^2 := by
  have hs (s : Spins m) : (∫ x, potentialForm V (ψ.outerSlice s x)) =
      ∑ t : Spins k, ∫ z, V ((outerJoinConfiguration m k).symm z).2 * ‖ψ.value (outerAppend s t) z‖^2 := by
    rw [integral_congr_ae (potentialForm_outerSlice_ae ψ s V)]
    have hi (t : Spins k) : Integrable (fun z : Configuration m × Configuration k =>
        V z.2 * ‖ψ.value (outerAppend s t) (outerJoinConfiguration m k z)‖^2) (volume.prod volume) := by
      have H := ((outerJoinConfiguration_measurePreserving m k).integrable_comp_emb
        (outerJoinConfiguration m k).toHomeomorph.toMeasurableEquiv.measurableEmbedding).mpr
        (hV (outerAppend s t))
      change Integrable (fun z : Configuration m × Configuration k =>
        V ((outerJoinConfiguration m k).symm (outerJoinConfiguration m k z)).2 *
          ‖ψ.value (outerAppend s t) (outerJoinConfiguration m k z)‖^2) (volume.prod volume) at H
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using H
    rw [integral_finsetSum _ (fun t _ => (hi t).integral_prod_left)]
    apply Finset.sum_congr rfl
    intro t _
    rw [← integral_prod _ (hi t)]
    have H := (outerJoinConfiguration_measurePreserving m k).integral_comp'
        (fun z => V ((outerJoinConfiguration m k).symm z).2 * ‖ψ.value (outerAppend s t) z‖^2)
    change (∫ z : Configuration m × Configuration k,
        V ((outerJoinConfiguration m k).symm (outerJoinConfiguration m k z)).2 *
          ‖ψ.value (outerAppend s t) (outerJoinConfiguration m k z)‖^2 ∂volume.prod volume) = _ at H
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using H
  simp_rw [hs]
  rw [← Fintype.sum_prod_type (f := fun st : Spins m × Spins k =>
    ∫ z, V ((outerJoinConfiguration m k).symm z).2 * ‖ψ.value (outerAppend st.1 st.2) z‖^2)]
  exact Fintype.sum_equiv (outerAppendEquiv m k) _ _ (fun _ => rfl)

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SliceExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma sliceExpectation_const {m k : ℕ} (ψ : H1Vector (m+k))
    (f : Configuration m → ℝ)
    (hf : ∀ st, Integrable (fun z => f ((joinConfiguration m k).symm z).1*‖ψ.value st z‖^2)) :
    sliceExpectation ψ (fun _ x => f x) = potentialForm (fun z => f ((joinConfiguration m k).symm z).1) ψ := by
  unfold sliceExpectation
  simp_rw [mul_comm (mass _) (f _), ←potentialForm_const]
  exact integral_potentialForm_coreSlice_parameter ψ (fun x _ => f x) hf

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TfExtendNonneg
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical BigOperators Topology SchwartzMap Pointwise
namespace Coulomb

lemma tfDensity_measurable {Ω : Set Space} (hΩ : MeasurableSet Ω) (f : TFLp (volume.restrict Ω)) :
    Measurable (tfDensity Ω f) := (tfExtend_measurable hΩ f).max measurable_const
lemma tfDensity_eq_zero {Ω : Set Space} (f : TFLp (volume.restrict Ω)) {x : Space} (hx : x ∉ Ω) :
    tfDensity Ω f x = 0 := by simp [tfDensity,tfExtend,hx]
lemma tfDensity_memLp {Ω : Set Space} (hΩ : MeasurableSet Ω)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    MemLp (tfDensity Ω f) TFExponent volume :=
  (memLp_congr_ae (tfDensity_ae_tfExtend hΩ hf)).mpr (tfExtend_memLp hΩ f)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical BigOperators Topology SchwartzMap Pointwise
namespace Coulomb

lemma tfExtend_sub_ae {Ω : Set Space} (hΩ : MeasurableSet Ω)
    (f g : TFLp (volume.restrict Ω)) :
    tfExtend Ω (g-f) =ᵐ[volume] fun x => tfExtend Ω g x-tfExtend Ω f x := by
  filter_upwards [(ae_restrict_iff' hΩ).mp (Lp.coeFn_sub g f)] with x hx
  by_cases h : x ∈ Ω
  · simpa only [tfExtend,Set.indicator_of_mem h,Pi.sub_apply] using hx h
  · simp [tfExtend,h]

lemma coulombBilinear_tfDensity_sub {Ω : Set Space} (hΩ : MeasurableSet Ω)
    {f g : TFLp (volume.restrict Ω)} (hf : TFNonneg f) (hg : TFNonneg g) :
    coulombBilinear (fun x => tfDensity Ω g x-tfDensity Ω f x)
      (fun x => tfDensity Ω g x-tfDensity Ω f x) = tfCoulomb Ω (g-f) (g-f) := by
  have h : (fun x => tfDensity Ω g x-tfDensity Ω f x) =ᵐ[volume] tfExtend Ω (g-f) := by
    filter_upwards [tfDensity_ae_tfExtend hΩ hf,tfDensity_ae_tfExtend hΩ hg,tfExtend_sub_ae hΩ f g]
      with x hx hy hz
    rw [hx,hy,hz]
  exact coulombBilinear_congr_ae h h

lemma rawTFBregman_tfDensity {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)]
    {f g : TFLp (volume.restrict Ω)} (hf : TFNonneg f) (hg : TFNonneg g) :
    rawTFBregman (tfDensity Ω f) (tfDensity Ω g) = thomasFermiKineticConstant*tfBregman f g := by
  rw [rawTFBregman_congr_ae (tfDensity_ae_tfExtend hΩ hf) (tfDensity_ae_tfExtend hΩ hg),
    rawTFBregman, tfBregman_formula hf hg, ← integral_indicator hΩ]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Ω <;> simp [tfExtend,hx]

lemma tfDensity_rawToTFLp {Ω : Set Space} (hΩ : MeasurableSet Ω) {σ : Space → ℝ}
    (hσ : MemLp σ TFExponent (volume.restrict Ω))
    (hp : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ σ x) (hs : ∀ x ∉ Ω, σ x = 0) :
    tfDensity Ω (rawToTFLp σ hσ) =ᵐ[volume] σ := by
  refine (tfDensity_ae_tfExtend hΩ (rawToTFLp_nonneg hσ hp)).trans ?_
  filter_upwards [(ae_restrict_iff' hΩ).mp hσ.coeFn_toLp] with x hx
  by_cases hy : x ∈ Ω
  · simpa only [tfExtend,rawToTFLp,Set.indicator_of_mem hy] using hx hy
  · simp [tfExtend,hy,hs x hy]

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CoulombTest
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.NeutralAtom.observationLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology ContDiff
noncomputable section
namespace Coulomb

variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]

include hΩ in
lemma tfCoulomb_cauchy (f g : TFLp (volume.restrict Ω)) :
    (tfCoulomb Ω f g)^2 ≤ tfCoulomb Ω f f*tfCoulomb Ω g g := by
  have H (t : ℝ) : 0 ≤ tfCoulomb Ω g g*(t*t)+(2*tfCoulomb Ω f g)*t+tfCoulomb Ω f f := by
    have hh := tfCoulomb_self_nonneg hΩ (f+t • g)
    change 0 ≤ (tfCoulombContinuous hΩ) (f+t • g) (f+t • g) at hh
    simp only [map_add,map_smul,_root_.add_apply,_root_.smul_apply,smul_eq_mul] at hh
    change 0 ≤ tfCoulomb Ω f f+t*tfCoulomb Ω g f+t*(tfCoulomb Ω f g+t*tfCoulomb Ω g g) at hh
    rw [tfCoulomb_symm g f] at hh
    nlinarith only [hh]
  have hh := discrim_le_zero H
  dsimp [discrim] at hh
  nlinarith only [hh]

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in
lemma tfExtend_toLp {q : Space → ℝ} (hΩ : MeasurableSet Ω)
    (hq : MemLp q TFExponent (volume.restrict Ω)) (hs : ∀ x∉Ω, q x=0) :
    tfExtend Ω (hq.toLp q) =ᵐ[volume] q := by
  filter_upwards [(ae_restrict_iff' hΩ).mp hq.coeFn_toLp] with x hx
  by_cases hy : x∈Ω
  · simpa only [tfExtend,indicator_of_mem hy] using hx hy
  · simp only [tfExtend,indicator_of_notMem hy,hs x hy]

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in
lemma testCharge_continuous {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    Continuous (testCharge χ) :=
  (NeutralAtom.continuous_coordinateLaplacian (hχ.of_le (by exact WithTop.coe_le_coe.mpr le_top))).neg.div_const _

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in
lemma testCharge_compact {χ : Space → ℝ} (hc : HasCompactSupport χ) :
    HasCompactSupport (testCharge χ) := by
  apply hc.mono'
  intro x hx
  by_contra hn
  exact hx (by simp only [testCharge,NeutralAtom.coordinateLaplacian_eq_zero_of_notMem_tsupport hn,neg_zero,zero_div])

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in
lemma testCharge_zero {χ : Space → ℝ} {x : Space} (hx : x∉tsupport χ) :
    testCharge χ x=0 := by
  simp only [testCharge,NeutralAtom.coordinateLaplacian_eq_zero_of_notMem_tsupport hx,neg_zero,zero_div]

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in
lemma testCharge_potential {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (y : Space) :
    (∫ x, coulombKernel (y-x)*testCharge χ x)=χ y := by
  have H := NeutralAtom.integral_translated_coulombKernel_laplacian hχ hc y
  have he : (fun x => coulombKernel (y-x)*testCharge χ x)=
      (fun x => -(NeutralAtom.coulombKernel (x-y)*NeutralAtom.coordinateLaplacian χ x)/(4*Real.pi)) := by
    funext x
    simp only [testCharge,coulombKernel,NeutralAtom.coulombKernel,norm_sub_rev]
    ring
  rw [he,integral_div,integral_neg,H]
  field_simp

include hΩ in
lemma tfCoulomb_testCharge {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ⊆Ω) (f : TFLp (volume.restrict Ω)) :
    tfCoulomb Ω f (((testCharge_continuous hχ).memLp_of_hasCompactSupport (testCharge_compact hc)).restrict (s := Ω) |>.toLp (testCharge χ))=
      ∫ x, tfExtend Ω f x*χ x := by
  let hm : MemLp (testCharge χ) TFExponent (volume.restrict Ω) :=
    ((testCharge_continuous hχ).memLp_of_hasCompactSupport (testCharge_compact hc)).restrict (s := Ω)
  have he := tfExtend_toLp hΩ hm (fun x hx => testCharge_zero (fun h => hx (hs h)))
  have hep := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure Space)) (ν := (volume : Measure Space))).ae_eq_comp he
  change _ =ᵐ[(volume : Measure Space).prod volume] _ at hep
  unfold tfCoulomb
  rw [Measure.volume_eq_prod]
  have hi := tfCoulomb_integrable hΩ f (hm.toLp (testCharge χ))
  rw [Measure.volume_eq_prod] at hi
  have hpair : (fun p : Space × Space => tfExtend Ω f p.1 * tfExtend Ω (hm.toLp (testCharge χ)) p.2 * coulombKernel (p.1 - p.2)) =ᵐ[(volume : Measure Space).prod volume]
      (fun p => tfExtend Ω f p.1 * testCharge χ p.2 * coulombKernel (p.1 - p.2)) := by
    filter_upwards [hep] with p hp
    change tfExtend Ω (hm.toLp (testCharge χ)) p.2 = testCharge χ p.2 at hp
    rw [hp]
  rw [integral_congr_ae hpair,integral_prod _ (hi.congr hpair)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [show (fun y => tfExtend Ω f x*testCharge χ y*coulombKernel (x-y))=
      (fun y => tfExtend Ω f x*(coulombKernel (x-y)*testCharge χ y)) by funext y; ring,
    integral_const_mul,testCharge_potential hχ hc]

include hΩ in

lemma coulomb_smooth_test {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ⊆Ω) (f : TFLp (volume.restrict Ω)) :
    (∫ x, tfExtend Ω f x*χ x)^2 ≤ tfCoulomb Ω f f*(∫ x, testCharge χ x*χ x) := by
  let hm : MemLp (testCharge χ) TFExponent (volume.restrict Ω) :=
    ((testCharge_continuous hχ).memLp_of_hasCompactSupport (testCharge_compact hc)).restrict (s := Ω)
  let g : TFLp (volume.restrict Ω) := hm.toLp (testCharge χ)
  have hg : tfExtend Ω g =ᵐ[volume] testCharge χ :=
    tfExtend_toLp hΩ hm (fun x hx => testCharge_zero (fun h => hx (hs h)))
  have He := tfCoulomb_testCharge hΩ hχ hc hs f
  have Hgg := tfCoulomb_testCharge hΩ hχ hc hs g
  change tfCoulomb Ω g g = _ at Hgg
  have Hg : (∫ x, tfExtend Ω g x*χ x) = ∫ x, testCharge χ x*χ x :=
    integral_congr_ae (hg.mono (fun x hx => congrArg (·*χ x) hx))
  rw [Hg] at Hgg
  have H := tfCoulomb_cauchy hΩ f g
  rwa [He,Hgg] at H

include hΩ in
lemma raw_coulomb_smooth_test {χ σ : Space → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ⊆Ω)
    (hσ : MemLp σ TFExponent (volume.restrict Ω)) (hσs : ∀ x∉Ω, σ x=0) :
    (∫ x, σ x*χ x)^2 ≤ coulombBilinear σ σ*(∫ x, testCharge χ x*χ x) := by
  let f := hσ.toLp σ
  have he : tfExtend Ω f =ᵐ[volume] σ := tfExtend_toLp hΩ hσ hσs
  have H := coulomb_smooth_test hΩ hχ hc hs f
  have Hc : tfCoulomb Ω f f = coulombBilinear σ σ := by
    exact coulombBilinear_congr_ae he he
  rw [Hc] at H
  rwa [integral_congr_ae (he.mono (fun x hx => congrArg (·*χ x) hx))] at H

end Coulomb

end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_ScaledTest
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.NeutralAtom.observationLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology ContDiff
noncomputable section
namespace Coulomb
open NeutralAtom (dirPartial coordinateLaplacian axis)

lemma testCharge_countTest (y : Space) (a : ℝ) (x : Space) :
    testCharge (countTest y a) x=a⁻¹^2*testCharge cutSeed (a⁻¹ • (x-y)) := by
  unfold testCharge countTest
  rw [coordinateLaplacian_scaled (cutSeed_smooth.of_le (by exact WithTop.coe_le_coe.mpr le_top))]
  ring

lemma countTest_energy (y : Space) {a : ℝ} (ha : 0<a) :
    (∫ x, testCharge (countTest y a) x*countTest y a x)=a*countTestEnergy := by
  simp only [testCharge_countTest,countTest,mul_assoc,integral_const_mul]
  rw [←integral_add_right_eq_self (fun x : Space => (testCharge cutSeed (a⁻¹ • (x-y))*cutSeed (a⁻¹ • (x-y)))) y]
  simp only [add_sub_cancel_right]
  rw [Measure.integral_comp_inv_smul (volume : Measure Space) (fun x => testCharge cutSeed x*cutSeed x) a]
  simp only [show Module.finrank ℝ Space=3 from by simp [Space],smul_eq_mul,abs_of_pos (pow_pos ha _)]
  dsimp only [countTestEnergy]
  field_simp

end Coulomb

end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TFCountTest
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology ContDiff
noncomputable section
namespace Coulomb

variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]

include hΩ in
lemma raw_coulomb_nonneg {σ : Space → ℝ}
    (hσ : MemLp σ TFExponent (volume.restrict Ω)) (hs : ∀ x∉Ω, σ x=0) :
    0 ≤ coulombBilinear σ σ := by
  have he := tfExtend_toLp hΩ hσ hs
  have H := tfCoulomb_self_nonneg hΩ (hσ.toLp σ)
  rwa [show tfCoulomb Ω (hσ.toLp σ) (hσ.toLp σ)=coulombBilinear σ σ from
    coulombBilinear_congr_ae he he] at H

include hΩ in
lemma tfDensity_test_bound {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (y : Space) {a B : ℝ} (ha : 0<a) (hB : 0≤B)
    (hbound : ∀ᵐ x ∂volume.restrict (Metric.closedBall y (2*a)), tfDensity Ω f x≤B) :
    (∫ x, tfDensity Ω f x*countTest y a x)≤B*((2*a)^3*(Real.pi*4/3)) := by
  have hi := integrable_mul_countTest ((tfExtend_integrable hΩ f).congr
    (tfDensity_ae_tfExtend hΩ hf).symm) y a
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall y (2*a))) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall y (2*a)).measure_lt_top.ne
  have hj : Integrable (Metric.closedBall y (2*a) |>.indicator (fun _ => B)) := by
    apply integrable_indicator_iff measurableSet_closedBall |>.mpr
    exact integrable_const B
  have H : (∫ x, tfDensity Ω f x*countTest y a x)≤
      ∫ x in Metric.closedBall y (2*a), B := by
    rw [←integral_indicator measurableSet_closedBall]
    apply integral_mono_ae hi hj
    filter_upwards [(ae_restrict_iff' measurableSet_closedBall).mp hbound] with x hx
    by_cases h : x∈Metric.closedBall y (2*a)
    · rw [indicator_of_mem h]
      calc
        _≤B*countTest y a x := mul_le_mul_of_nonneg_right (hx h) (countTest_nonneg y a x)
        _≤B := mul_le_of_le_one_right hB (countTest_le_one y a x)
    · rw [indicator_of_notMem h,countTest_zero y ha (le_of_lt (by simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using h)),mul_zero]
  apply H.trans_eq
  simp only [integral_const,Measure.real,Measure.restrict_apply_univ,EuclideanSpace.volume_closedBall_fin_three,
    ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal (by positivity : 0≤2*a),
    ENNReal.toReal_ofReal (by positivity : 0≤Real.pi*4/3),smul_eq_mul]
  ring

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_FineCountTest
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

lemma deletedLabels_patchRetained {n : ℕ} (y : Space) (t b : ℝ) (x : Configuration n) :
    ((deletedLabels (patchRetained y t b) x).card:ℝ)=localCount {z | t-7*b≤‖z-y‖} x := by
  have he : deletedLabels (patchRetained y t b) x=Finset.univ.filter (fun i => t-7*b≤‖position x i-y‖) := by
    ext i
    simp [deletedLabels,patchRetained,not_lt]
  rw [he]
  simp only [Finset.card_eq_sum_ones,Nat.cast_sum,Finset.sum_filter,localCount,Set.indicator_apply,Set.mem_ofPred_eq]
  simp

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_PatchErrors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Classical
noncomputable section
namespace Coulomb

lemma slice_ensemble_mean_le_sqrt {P : Type*} [Fintype P] (m k : P → ℕ)
    (u : (p : P) → H1Vector (m p+k p))
    (F : (p : P) → Spins (m p) → Configuration (m p) → ℝ)
    (hFm : ∀ p s, AEStronglyMeasurable (F p s) volume)
    (hF0 : ∀ p s, ∀ᵐ x, 0≤F p s x)
    (hFi : ∀ p s, Integrable (fun x => mass ((u p).coreSlice s x)*(F p s x)^2))
    (hm : (∑ p, mass (u p))=1) :
    (∑ p, sliceExpectation (u p) (F p))≤Real.sqrt
      (∑ p, sliceExpectation (u p) (fun s x => (F p s x)^2)) := by
  have H := slice_ensemble_mul_le_sqrt m k u F (fun _ _ _ => 1) hFi
    (fun p s => by simpa only [one_pow,mul_one] using mass_coreSlice_integrable (u p) s)
    (fun p s => by
      simpa only [mul_one] using (weighted_cap_integrable (mass_coreSlice_integrable (u p) s)
        (Eventually.of_forall (fun _ => mass_nonneg _)) (hFm p s) (hF0 p s) (hFi p s)))
  simpa only [mul_one,one_pow,sliceExpectation_number,one_mul,hm] using H

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_CountUnits
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma screenCountParameter_le_of {n : ℕ} (ψ : H1Vector n) (δ : ℝ) {P : ℝ} (hP : 1 ≤ P)
    (hc : ∀ y : Space, y≠0 → localCountSecondMoment ψ (Metric.closedBall y (atomicCellScale y)) ≤
      P*(screenMass δ (atomicCellScale y))^2) : screenCountParameter ψ δ ≤ P := by
  apply max_le hP
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨y,rfl⟩
  unfold screenCountRatio
  split_ifs with hy
  · linarith
  · exact (div_le_iff₀ (sq_pos_of_pos (screenMass_pos δ _))).mpr (hc y hy)

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_PhysicalCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace Coulomb

lemma sliceExpectation_le_affine {m k : ℕ} (ψ : H1Vector (m+k))
    (H G : Spins m → Configuration m → ℝ) (A B : ℝ)
    (hH : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*H s x))
    (hG : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*G s x))
    (hbound : ∀ s, ∀ᵐ x, H s x≤A+B*G s x) :
    sliceExpectation ψ H≤A*mass ψ+B*sliceExpectation ψ G := by
  rw [←sliceExpectation_number ψ A]
  unfold sliceExpectation
  rw [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s hs
  rw [←integral_const_mul,←integral_add ((mass_coreSlice_integrable ψ s).mul_const A) ((hG s).const_mul B)]
  apply integral_mono_ae (hH s) (((mass_coreSlice_integrable ψ s).mul_const A).add ((hG s).const_mul B))
  filter_upwards [hbound s] with x hx
  convert mul_le_mul_of_nonneg_left hx (mass_nonneg (ψ.coreSlice s x)) using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [Pi.add_apply]
  ring

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_SharpThinScreening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
namespace Coulomb

lemma thinIMS_sharp_budget {n : ℕ} (ψ : H1Vector n) (hm : mass ψ=1)
    {δ P : ℝ} (hδ : 0≤δ) (hP : 0≤P)
    (hc : ∀ z : Space, z≠0 → localCountSecondMoment ψ (Metric.closedBall z (atomicCellScale z))≤
      P*(screenMass δ (atomicCellScale z))^2)
    {y : Space} (hy : y≠0) {t b : ℝ} (hb : 0<b) (hwidth : t+b≤80*atomicCellScale y) :
    thinIMS ψ y t b≤thinReserveFactor*(Real.sqrt P*screenMass δ (atomicCellScale y)/b^2) := by
  have H := (expectedPopulation_mono ψ measurableSet_closedBall measurableSet_closedBall
    (Metric.closedBall_subset_closedBall hwidth)).trans (atomicPatch_population ψ hm hδ hP hc hy)
  have Hims := mul_le_mul_of_nonneg_left H (show 0≤3*(thinCutCoefficient/b)^2 by positivity)
  apply Hims.trans
  calc
    _=(3*thinCutCoefficient^2*(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*8)*
        (Real.sqrt P*screenMass δ (atomicCellScale y)/b^2) := by rw [div_pow]; ring
    _≤_ := mul_le_mul_of_nonneg_right (le_max_right _ _)
      (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (screenMass_pos _ _).le) (sq_pos_of_pos hb).le)

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_CountScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
namespace Coulomb

lemma countBootstrap_coefficients_nonneg : 0 ≤ countBootstrapA ∧ 0 ≤ countBootstrapB ∧
    0 ≤ countBootstrapC ∧ 0 ≤ countBootstrapD ∧ 0 ≤ countBootstrapE := by
  have hM : 0 ≤ max countTestEnergy 0 := le_max_right _ _
  have hK := unitWindowKinetic_nonneg
  have hR := thinReserveFactor_nonneg
  have hN := neumannBoundary_nonneg
  have hD := atomicPatchCountFactor_nonneg
  unfold countBootstrapA countBootstrapB countBootstrapC countBootstrapD countBootstrapE
  exact ⟨by positivity,by positivity,by positivity,by positivity [Real.pi_pos],by positivity⟩

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma countBootstrap_small_parameter : ∃ β : ℝ, 0 < β ∧ 18*β ≤ 1 ∧ countBootstrapB*Real.sqrt β < 1/4 := by
  have hB := countBootstrap_coefficients_nonneg.2.1
  let u : ℝ := 1/(100*(countBootstrapB+1))
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 1/100 := by
    dsimp [u]
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    nlinarith
  refine ⟨u^2,by positivity,by nlinarith,?_⟩
  rw [Real.sqrt_sq hu.le]
  have H : countBootstrapB*u < 1/100 := by
    dsimp [u]
    rw [←mul_div_assoc,mul_one]
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  linarith

lemma countBootstrap_ratio_limit (β : ℝ) :
    Tendsto (fun P : ℝ => countBootstrapA*P^(-(1:ℝ))+countBootstrapB*Real.sqrt β+
      (countBootstrapC/β^2+countBootstrapD/β)*P^(-(1/2:ℝ))+
      countBootstrapE/β^2*P^(-(1/3:ℝ))) atTop (𝓝 (countBootstrapB*Real.sqrt β)) := by
  have h1 := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)).const_mul countBootstrapA
  have h2 := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).const_mul (countBootstrapC/β^2+countBootstrapD/β)
  have h3 := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/3)).const_mul (countBootstrapE/β^2)
  simpa only [mul_zero,zero_add,add_zero] using ((h1.add tendsto_const_nhds).add h2).add h3

lemma countBootstrap_ratio_identity {β P : ℝ} (hP : 0 < P) :
    countBootstrapMajorant β P=
    (countBootstrapA*P^(-(1:ℝ))+countBootstrapB*Real.sqrt β+
      (countBootstrapC/β^2+countBootstrapD/β)*P^(-(1/2:ℝ))+
      countBootstrapE/β^2*P^(-(1/3:ℝ)))*P := by
  have h (r : ℝ) : P^r*P=P^(r+1) := by
    nth_rw 2 [←Real.rpow_one P]
    rw [←Real.rpow_add hP]
  have h1 := h (-(1:ℝ))
  have h2 := h (-(1/2:ℝ))
  have h3 := h (-(1/3:ℝ))
  norm_num at h1 h2 h3
  calc
    _ = countBootstrapA*(P^(-(1:ℝ))*P)+countBootstrapB*Real.sqrt β*P+
        (countBootstrapC/β^2+countBootstrapD/β)*(P^(-(1/2:ℝ))*P)+
        countBootstrapE/β^2*(P^(-(1/3:ℝ))*P) := by
      rw [h1,h2,h3]
      simp only [countBootstrapMajorant,Real.sqrt_eq_rpow,mul_one]
    _ = _ := by ring

theorem countBootstrap_threshold : ∃ β P₀ : ℝ, 0 < β ∧ 18*β ≤ 1 ∧ 2 ≤ P₀ ∧
    ∀ P ≥ P₀, 1 ≤ β^2*Real.sqrt P ∧ countBootstrapMajorant β P ≤ P/2 := by
  obtain ⟨β,hβ,hβsmall,hβB⟩ := countBootstrap_small_parameter
  obtain ⟨q,hq⟩ := eventually_atTop.mp ((countBootstrap_ratio_limit β).eventually_lt_const
    (show countBootstrapB*Real.sqrt β < 1/2 by linarith))
  let P₀ := max 2 (max q ((β^2)⁻¹^2))
  refine ⟨β,P₀,hβ,hβsmall,le_max_left _ _,?_⟩
  intro P hP
  have hP2 : 2 ≤ P := (le_max_left _ _).trans hP
  have hP0 : 0 < P := by linarith
  have hPq : q ≤ P := (le_max_left _ _).trans ((le_max_right _ _).trans hP)
  have hPt : (β^2)⁻¹^2 ≤ P := (le_max_right _ _).trans ((le_max_right _ _).trans hP)
  constructor
  · have H := Real.sqrt_le_sqrt hPt
    rw [Real.sqrt_sq (by positivity)] at H
    have H' := mul_le_mul_of_nonneg_left H (sq_nonneg β)
    simpa only [mul_inv_cancel₀ (ne_of_gt (sq_pos_of_pos hβ))] using H'
  · rw [countBootstrap_ratio_identity hP0]
    have H := mul_le_mul_of_nonneg_right (hq P hPq).le hP0.le
    simpa only [one_div,mul_comm (2:ℝ)⁻¹ P,←div_eq_mul_inv] using H

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_AtomicRefinedGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace Coulomb

def atomicRefinedError (δ P a b : ℝ) : ℝ :=
(δ+thinReserveFactor*(Real.sqrt P*screenMass δ a/b^2))+
      12*a*unitWindowKinetic/b^2*Real.sqrt (atomicPhysicalCapConstant*P*(screenMass δ a)^2/a^2)+
      Real.sqrt ((atomicPhysicalCapConstant*P*(screenMass δ a)^2/a^2)*
        (18*atomicPatchCountFactor*(b/a)*P*(screenMass δ a)^2))+
      (b⁻¹)^2*((Real.pi^2/2)*neumannBoundary)*(atomicPatchCountFactor*P*(screenMass δ a)^2)^(2/3:ℝ)+
      ((2*Real.pi+1)/(2*b))*Real.sqrt (atomicPatchCountFactor*P*(screenMass δ a)^2)

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_AtomicGapScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

def atomicRefinedFormula (δ P m a b : ℝ) : ℝ :=
  (δ+thinReserveFactor*(Real.sqrt P*m/b^2))+
    12*a*unitWindowKinetic/b^2*Real.sqrt (atomicPhysicalCapConstant*P*m^2/a^2)+
    Real.sqrt ((atomicPhysicalCapConstant*P*m^2/a^2)*
      (18*atomicPatchCountFactor*(b/a)*P*m^2))+
    (b⁻¹)^2*((Real.pi^2/2)*neumannBoundary)*(atomicPatchCountFactor*P*m^2)^(2/3:ℝ)+
    ((2*Real.pi+1)/(2*b))*Real.sqrt (atomicPatchCountFactor*P*m^2)

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FlatBodyDensity
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

noncomputable def flatOneBodyDensity {n : ℕ} (ψ : H1Vector (n+1)) (x : Fin 3 → ℝ) : ℝ :=
  ∑ s : Fin 2, firstParticleDensity (μ := spinSpaceMeasure) (cubeState ψ) (s,x)

noncomputable def oneBodyDensity {n : ℕ} (ψ : H1Vector (n+1)) (x : Space) : ℝ :=
  flatOneBodyDensity ψ (WithLp.ofLp x)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_PhysicalBridge
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
noncomputable section
namespace NeutralAtom

lemma flattenConfiguration_symm_measurePreserving (n : ℕ) :
    MeasurePreserving (flattenConfiguration n).symm.toHomeomorph.toMeasurableEquiv :=
  Coulomb.configurationMeasurableEquiv_measurePreserving n

lemma flattenConfiguration_coordinateDirection {n : ℕ} (i : Fin n) (a : Fin 3) :
    flattenConfiguration n (coordinateDirection i a) = EuclideanSpace.single (i,a) 1 := by
  ext ⟨j,b⟩
  simp [flattenConfiguration_apply,coordinateDirection,Pi.single_apply,PiLp.single_apply]
  split_ifs <;> simp_all

def asH1 {n : ℕ} (ψ : Wavefunction n) (g : Gradient n)
    (hw : HasWeakGradient ψ g) (hψ : ∀ σ, MemLp (ψ σ) 2 volume)
    (hg : ∀ σ i a, MemLp (g σ i a) 2 volume) : Coulomb.H1Vector n where
  value := fun s x => ψ s ((flattenConfiguration n).symm x)
  gradient := fun s ia x => g s ia.1 ia.2 ((flattenConfiguration n).symm x)
  value_L2 := fun s => (hψ s).comp_measurePreserving (flattenConfiguration_symm_measurePreserving n)
  partial_L2 := fun s ia => (hg s ia.1 ia.2).comp_measurePreserving
    (flattenConfiguration_symm_measurePreserving n)
  weak_partial := by
    intro s ia φ hφ hc
    apply weakDirectional_pullback (flattenConfiguration n).symm
      (flattenConfiguration_symm_measurePreserving n)
      (fun φ hφ hc => by simpa only [mul_comm] using hw s ia.1 ia.2 φ hφ hc)
      (w := EuclideanSpace.single ia 1) _ φ hφ hc
    rw [ContinuousLinearEquiv.symm_apply_eq]
    exact (flattenConfiguration_coordinateDirection ia.1 ia.2).symm

def fromH1Wave {n : ℕ} (ψ : Coulomb.H1Vector n) : Wavefunction n :=
  fun s x => ψ.value s (flattenConfiguration n x)
def fromH1Gradient {n : ℕ} (ψ : Coulomb.H1Vector n) : Gradient n :=
  fun s i a x => ψ.gradient s (i,a) (flattenConfiguration n x)

end NeutralAtom

end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FermionicNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
namespace Coulomb

def nearWeight (y : Space) (R : ℝ) : Space → ℝ :=
  (Metric.ball y R).indicator (fun z => coulombKernel (y-z))
def nearPotential {n : ℕ} (y : Space) (R : ℝ) (x : Configuration n) : ℝ :=
  ∑ i,nearWeight y R (position x i)
end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TFPotentialParameter
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb
variable {Ω : Set Space} (hΩ : MeasurableSet Ω)
include hΩ

lemma tfPotential_eq_restrict [IsFiniteMeasure (volume.restrict Ω)]
    (f : TFLp (volume.restrict Ω)) (y : Space) :
    tfPotential f y=∫ z in Ω, coulombKernel (y-z)*f z := by
  rw [←integral_indicator hΩ]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z∈Ω <;> simp [tfExtend,hz]

variable [IsFiniteMeasure (volume.restrict Ω)]

lemma tfPotential_add (f g : TFLp (volume.restrict Ω)) (y : Space) :
    tfPotential (f+g) y=tfPotential f y+tfPotential g y := by
  have he : tfPotential (f+g) y=∫ z, coulombKernel (y-z)*tfExtend Ω f z+
      coulombKernel (y-z)*tfExtend Ω g z := by
    rw [tfPotential_eq_restrict hΩ,←integral_indicator hΩ]
    apply integral_congr_ae
    have H := ae_restrict_iff' hΩ |>.mp (Lp.coeFn_add f g)
    filter_upwards [H] with z hz
    by_cases hzi : z∈Ω
    · simp only [Set.indicator_of_mem hzi,tfExtend,hz hzi,Pi.add_apply,mul_add]
    · simp [hzi,tfExtend]
  rw [he,integral_add (tfPotential_integrand hΩ f y) (tfPotential_integrand hΩ g y)]
  rfl

lemma tfPotential_smul (c : ℝ) (f : TFLp (volume.restrict Ω)) (y : Space) :
    tfPotential (c • f) y=c*tfPotential f y := by
  rw [tfPotential_eq_restrict hΩ,tfPotential_eq_restrict hΩ,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c f] with z hz
  rw [hz]
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

def tfPotentialEvaluation (y : Space) : TFLp (volume.restrict Ω) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => tfPotential f y
      map_add' := fun f g => tfPotential_add hΩ f g y
      map_smul' := fun c f => tfPotential_smul hΩ c f y }
    ((8*Real.pi)^(2/5:ℝ)+(volume.real Ω)^(2/5:ℝ))
    (fun f => tfPotential_bound hΩ f y)

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_BodyCoefficient
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical ContDiff
noncomputable section
namespace Coulomb

def reciprocalCoefficient (l e:ℝ) (hl:l≠0) (he:0<e):SmoothBoundedCoefficient where
  value x := (regularizedU l e x)⁻¹
  smooth := (regularizedU_smooth hl e).inv (fun x => (regularizedU_pos he x).ne')
  bound := e⁻¹
  derivBound := ((l^2)^(-1/2:ℝ)+(l^2)^(-3/2:ℝ))/e^2
  bound_nonneg := le_of_lt (inv_pos.mpr he)
  derivBound_nonneg := by positivity
  value_le x := by
    rw [abs_of_pos (inv_pos.mpr (regularizedU_pos he x))]
    exact inv_anti₀ he (regularizedU_ge x)
  deriv_le a x := by
    have H:=((hasDerivAt_inv (regularizedU_pos he x).ne').comp_hasFDerivAt x
      (((regularizedU_smooth hl e).differentiable (by simp) x).hasFDerivAt)).fderiv
    change fderiv ℝ (fun y => (regularizedU l e y)⁻¹) x=_ at H
    rw [H]
    simp only [smul_apply,smul_eq_mul,abs_mul,abs_neg,
      abs_inv,abs_of_nonneg (sq_nonneg (regularizedU l e x))]
    rw [regularizedU_partial hl]
    have hd:=NeutralAtom.regularizedPartial_uniform_bound hl x a
    have hu:(e^2)≤(regularizedU l e x)^2:=sq_le_sq₀ he.le (regularizedU_pos he x).le |>.mpr (regularizedU_ge x)
    have hh:=mul_le_mul (inv_anti₀ (sq_pos_of_pos he) hu) hd (abs_nonneg _) (by positivity)
    simpa only [div_eq_mul_inv,mul_comm] using hh

def rootReciprocalCoefficient (l e:ℝ) (hl:l≠0) (he:0<e):SmoothBoundedCoefficient where
  value x := (regularizedU l e x)^(-1/2:ℝ)
  smooth := (regularizedU_smooth hl e).rpow_const_of_ne (fun x => (regularizedU_pos he x).ne')
  bound := e^(-1/2:ℝ)
  derivBound := (1/2:ℝ)*e^(-3/2:ℝ)*((l^2)^(-1/2:ℝ)+(l^2)^(-3/2:ℝ))
  bound_nonneg := Real.rpow_nonneg he.le _
  derivBound_nonneg := by positivity
  value_le x := by
    rw [abs_of_nonneg (Real.rpow_nonneg (regularizedU_pos he x).le _)]
    exact Real.rpow_le_rpow_of_nonpos he (regularizedU_ge x) (by norm_num)
  deriv_le a x := by
    have H:=((((regularizedU_smooth hl e).differentiable (by simp) x).hasFDerivAt).rpow_const
      (p:=(-1/2:ℝ)) (Or.inl (regularizedU_pos he x).ne')).fderiv
    rw [H]
    simp only [smul_apply,smul_eq_mul,abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (regularizedU_pos he x).le _),regularizedU_partial hl]
    rw [show (-1/2:ℝ)-1=(-3/2:ℝ) by norm_num,show |(-1/2:ℝ)|=(1/2:ℝ) by norm_num]
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos he (regularizedU_ge x) (by norm_num)) (by norm_num)
    · exact NeutralAtom.regularizedPartial_uniform_bound hl x a
    · exact abs_nonneg _
    · positivity

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_RegularizedKinetic
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical ContDiff
noncomputable section
namespace Coulomb

def regularizedUCoefficient (l e:ℝ) (hl:l≠0):SmoothBoundedCoefficient where
  value:=regularizedU l e
  smooth:=regularizedU_smooth hl e
  bound:=(l^2)^(-1/2:ℝ)+|e|
  derivBound:=(l^2)^(-1/2:ℝ)+(l^2)^(-3/2:ℝ)
  bound_nonneg:=by positivity
  derivBound_nonneg:=by positivity
  value_le x:= (abs_add_le _ _).trans (add_le_add (NeutralAtom.regularizedKernel_uniform_bound hl x) le_rfl)
  deriv_le a x:=by rw [regularizedU_partial hl]; exact NeutralAtom.regularizedPartial_uniform_bound hl x a

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_AtomicWeighted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical ContDiff
noncomputable section
namespace Coulomb
def atomicCross {k:ℕ} (x:Configuration (1+k)):ℝ:=
  ∑ j:Fin k,coulombKernel (position x 0-position x (Fin.natAdd 1 j))
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_ShellIMS
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical ContDiff Topology
noncomputable section
namespace Coulomb

def imsShell (y : Space) (r : ℝ) : Set Space :=
  {x | r ≤ ‖x-y‖ ∧ ‖x-y‖ ≤ 2*r}

end Coulomb

end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_RawRMS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

def rawRMS {n : ℕ} (ψ : H1Vector n) (f : Configuration n → ℝ) : ℝ :=
  Real.sqrt (potentialForm (fun x => (f x)^2) ψ)

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_TailMoment
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

def radialTailPotential {n : ℕ} (ψ : H1Vector n) (r : ℝ) : ℝ :=
  restrictedCorePotential ψ {x | r ≤ ‖x‖} 0

lemma radialTailPotential_eq {n : ℕ} (ψ : H1Vector n) (r : ℝ) :
    radialTailPotential ψ r=∑ s, ∑ i : Fin n, ∫ x, radialTailKernel r (position x i)*‖ψ.value s x‖^2 := by
  unfold radialTailPotential restrictedCorePotential radialTailKernel coulombKernel
  simp only [sub_zero,Set.mem_ofPred_eq,ite_mul,zero_mul]

lemma radialTailKernel_nonneg (r : ℝ) (x : Space) : 0 ≤ radialTailKernel r x := by
  unfold radialTailKernel
  split_ifs <;> positivity

lemma radialTailKernel_le {r : ℝ} (hr : 0 < r) (x : Space) : radialTailKernel r x ≤ r⁻¹ := by
  unfold radialTailKernel
  split_ifs with hx
  · exact (inv_le_inv₀ (hr.trans_le hx) hr).mpr hx
  · positivity

lemma radialTailKernel_integrable {n : ℕ} (ψ : H1Vector n) (r : ℝ) (s : Spins n) (i : Fin n) :
    Integrable (fun x => radialTailKernel r (position x i)*‖ψ.value s x‖^2) := by
  simpa only [radialTailKernel,coulombKernel,sub_zero,Set.mem_ofPred_eq,ite_mul,zero_mul] using
    restrictedCore_integrable ψ (isClosed_le continuous_const continuous_norm).measurableSet s i 0

lemma radialTailPotential_cap {n : ℕ} (ψ : H1Vector n) {r : ℝ} (hr : 0 < r) :
    radialTailPotential ψ r ≤ (n:ℝ)/r*mass ψ := by
  rw [radialTailPotential_eq]
  calc
    _ ≤ ∑ s : Spins n, ∑ i : Fin n, ∫ x, r⁻¹*‖ψ.value s x‖^2 := by
      apply Finset.sum_le_sum; intro s hs
      apply Finset.sum_le_sum; intro i hi
      exact integral_mono (radialTailKernel_integrable ψ r s i)
        (((ψ.value_L2 s).integrable_norm_pow (p:=2) (by norm_num)).const_mul _)
        (fun x => mul_le_mul_of_nonneg_right (radialTailKernel_le hr _) (sq_nonneg _))
    _ = _ := by simp only [integral_const_mul,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mass,div_eq_mul_inv,←Finset.mul_sum,mul_assoc]

lemma radialTailKernel_step {r : ℝ} (hr : 0 < r) (x : Space) :
    radialTailKernel r x ≤ r⁻¹*({z : Space | (1/2:ℝ)*r < ‖z‖ ∧ ‖z‖ < 4*r}.indicator (fun _ => (1:ℝ)) x)+
      radialTailKernel (2*r) x := by
  by_cases h0 : r ≤ ‖x‖
  · by_cases h1 : 2*r ≤ ‖x‖
    · simp only [radialTailKernel,ite_eq_left h0,ite_eq_left h1]
      have H : 0 ≤ ({z : Space | (1/2:ℝ)*r < ‖z‖ ∧ ‖z‖ < 4*r}.indicator (fun _ => (1:ℝ)) x) := Set.indicator_nonneg (fun _ _ => zero_le_one) _
      nlinarith [mul_nonneg (inv_nonneg.mpr hr.le) H]
    · have hA : x∈{z : Space | (1/2:ℝ)*r < ‖z‖ ∧ ‖z‖ < 4*r} := by constructor <;> linarith
      simp only [indicator_of_mem hA,mul_one,radialTailKernel,ite_eq_left h0,ite_eq_right h1,add_zero]
      exact (inv_le_inv₀ (hr.trans_le h0) hr).mpr h0
  · rw [radialTailKernel,ite_eq_right h0]
    exact add_nonneg (mul_nonneg (inv_nonneg.mpr hr.le) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)) (radialTailKernel_nonneg _ _)

lemma radialTailPotential_step {n : ℕ} (ψ : H1Vector n) {r : ℝ} (hr : 0 < r) :
    radialTailPotential ψ r ≤ expectedPopulation ψ {z : Space | (1/2:ℝ)*r < ‖z‖ ∧ ‖z‖ < 4*r}/r+
      radialTailPotential ψ (2*r) := by
  let A : Set Space := {z : Space | (1/2:ℝ)*r < ‖z‖ ∧ ‖z‖ < 4*r}
  have hA : MeasurableSet A := (isOpen_lt continuous_const continuous_norm).measurableSet.inter
    (isOpen_lt continuous_norm continuous_const).measurableSet
  rw [radialTailPotential_eq,radialTailPotential_eq]
  calc
    _ ≤ ∑ s : Spins n, ∑ i : Fin n, ∫ x, (r⁻¹*A.indicator (fun _ => (1:ℝ)) (position x i)+radialTailKernel (2*r) (position x i))*‖ψ.value s x‖^2 := by
      apply Finset.sum_le_sum; intro s hs
      apply Finset.sum_le_sum; intro i hi
      apply integral_mono (radialTailKernel_integrable ψ r s i) _
        (fun x => mul_le_mul_of_nonneg_right (radialTailKernel_step hr _) (sq_nonneg _))
      convert ((population_integrable ψ A hA s i).const_mul r⁻¹).add
        (radialTailKernel_integrable ψ (2*r) s i) using 1
      all_goals try with_reducible_and_instances rfl
      first | rfl | (ext x; simp only [Pi.add_apply]; ring)
    _ = _ := by
      simp_rw [add_mul,mul_assoc]
      simp_rw [integral_add ((population_integrable ψ A hA _ _).const_mul _) (radialTailKernel_integrable ψ (2*r) _ _),integral_const_mul]
      simp only [Finset.sum_add_distrib,←Finset.mul_sum,expectedPopulation,A,div_eq_mul_inv]
      ring

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_TailClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

def atomicInnerField {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n) (h : ℝ) (y : Space) : ℝ :=
  attraction S y-restrictedCorePotential ψ (Metric.ball 0 h) y

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_WeightedInner
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

def weightedInnerField {J n : ℕ} (S : Nuclei J) (h : ℝ) (w : Space → ℝ)
    (x : Configuration n) : ℝ :=
  ∑ i, w (position x i)*rawSignedField (attraction S (position x i)) (Metric.ball 0 h) (position x i) x

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_AtomicPhysicalKinetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

def atomicKineticFormula (δ P m a b : ℝ) : ℝ :=
  δ+thinReserveFactor*(Real.sqrt P*m/b^2)+
    (atomicPhysicalCapConstant+atomicPatchCountFactor)*P*m^2/(2*a)

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservationMatching
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
namespace NeutralAtom

def observationArrayPositions {H : Type*} {n : ℕ} (h : H)
    (y : (H × (Fin n × Fin 3)) → ℝ) : Configuration n :=
  fun i => WithLp.toLp 2 (fun a => y (h,i,a))

end NeutralAtom

end
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_InnerCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

def innerLocalCap {J m k : ℕ} (S : Nuclei J) (v : H1Vector k)
    (x : Configuration m) (h : ℝ) (z : Space) (a : ℝ) : ℝ :=
  Real.sqrt (8*(∫ w, (max (recordedFarField S v x (Metric.ball 0 h) w) 0)^2*
    ballCloud z (2*a) 1 w))
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_InnerMeshCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

def innerMeshCap {J m k M : ℕ} (S : Nuclei J) (v : H1Vector k)
    (x : Configuration m) (h : ℝ) (z : Fin M → Space) : ℝ :=
  Real.sqrt (∑ i, (innerLocalCap S v x h (z i) (atomicCellScale (z i)))^2)
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_DeletionEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

def deletionShell (t : ℝ) (j : ℕ) : Set Space :=
  {x | (2:ℝ)^j*t ≤ ‖x‖ ∧ ‖x‖ < (2:ℝ)^(j+1)*t}

def deletionShellWeight (t : ℝ) (w : Space → ℝ) (j : ℕ) : Space → ℝ :=
  (deletionShell t j).indicator w

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_ExteriorCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology ContDiff
noncomputable section
namespace Coulomb

def exteriorCut (t : ℝ) (l : Fin 2) : Space → ℝ :=
  if l=0 then radialCut 0 t 1 else radialCut 0 t 0

lemma exteriorCut_smooth (t : ℝ) (l : Fin 2) : ContDiff ℝ ∞ (exteriorCut t l) := by
  unfold exteriorCut
  split_ifs <;> exact radialCut_smooth 0 t _

lemma exteriorCut_partition (t : ℝ) (x : Space) : ∑ l : Fin 2, exteriorCut t l x^2=1 := by
  simpa only [Fin.sum_univ_two,exteriorCut,ite_true,show (1:Fin 2)≠0 by decide,ite_false,add_comm]
    using radialCut_partition 0 t x

lemma exteriorCut_derivative_bound {t : ℝ} (ht : 0<t) (l : Fin 2) (b : Fin 3) (x : Space) :
    |fderiv ℝ (exteriorCut t l) x (EuclideanSpace.single b 1)| ≤ radialCutCoefficient/t := by
  unfold exteriorCut
  split_ifs <;> exact radialCut_derivative_bound 0 ht _ b x

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_TotalDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

def particleInnerExterior {J n : ℕ} (S : Nuclei J) (h t : ℝ)
    (i : Fin n) (x : Configuration n) : ℝ :=
  if t ≤ ‖position x i‖ then
    rawSignedField (attraction S (position x i)) (Metric.ball 0 h) (position x i) x else 0

def outerDeletionField {J m k : ℕ} (S : Nuclei J) (h t : ℝ) (v : Configuration (m+k)) : ℝ :=
  ∑ i : Fin m, particleInnerExterior S h t (Fin.castAdd k i) v

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TFResponseMargins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

lemma tfScalarDensity_scale (v : ℝ) {a : ℝ} (ha : 0<a) :
    tfScalarDensity (v/a^4)=tfScalarDensity v/a^6 := by
  unfold tfScalarDensity
  have hmax : max (v/a^4) 0=max v 0/a^4 := by
    simpa only [zero_div] using max_div_div_right (pow_nonneg ha.le 4) v 0
  rw [hmax]
  have heq : max v 0/a^4/(thomasFermiKineticConstant*(5/3:ℝ)) =
      (max v 0/(thomasFermiKineticConstant*(5/3:ℝ)))/a^4 := by ring
  rw [heq,Real.div_rpow (div_nonneg (le_max_right _ _) (mul_nonneg thomasFermiKineticConstant_pos.le (by norm_num))) (pow_nonneg ha.le 4)]
  have hp : (a^4)^(3/2:ℝ)=a^6 := by
    rw [←Real.rpow_natCast a 4,←Real.rpow_mul ha.le]
    norm_num
  rw [hp]

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_NearActiveMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

lemma tfReaction_normalized {d : ℝ} (hd : 0<d) (v : ℝ) :
    d^6*tfReaction v=4*Real.pi*Coulomb.tfScalarDensity (d^4*v) := by
  have H := Coulomb.tfScalarDensity_scale (d^4*v) hd
  have he : d^4*v/d^4=v := by field_simp
  rw [he] at H
  rw [tfReaction_eq_scalar,H]
  field_simp

lemma normalized_density_le_reaction_iff {d μ v : ℝ} (hd : 0<d) :
    d^6*μ≤Coulomb.tfScalarDensity (d^4*v) ↔ 4*Real.pi*μ≤tfReaction v := by
  have H := tfReaction_normalized hd v
  have hp : 0<4*Real.pi := by positivity
  constructor
  · intro h
    have HH := mul_le_mul_of_nonneg_left h hp.le
    have h' : d^6*(4*Real.pi*μ)≤d^6*tfReaction v := by nlinarith only [HH,H]
    exact (mul_le_mul_iff_right₀ (pow_pos hd 6)).mp h'
  · intro h
    have HH := mul_le_mul_of_nonneg_left h (pow_pos hd 6).le
    have h' : (4*Real.pi)*(d^6*μ)≤(4*Real.pi)*Coulomb.tfScalarDensity (d^4*v) := by nlinarith only [HH,H]
    exact (mul_le_mul_iff_right₀ hp).mp h'

lemma normalized_reaction_le_density_iff {d μ v : ℝ} (hd : 0<d) :
    Coulomb.tfScalarDensity (d^4*v)≤d^6*μ ↔ tfReaction v≤4*Real.pi*μ := by
  have H := tfReaction_normalized hd v
  have hp : 0<4*Real.pi := by positivity
  constructor
  · intro h
    have HH := mul_le_mul_of_nonneg_left h hp.le
    have h' : d^6*tfReaction v≤d^6*(4*Real.pi*μ) := by nlinarith only [HH,H]
    exact (mul_le_mul_iff_right₀ (pow_pos hd 6)).mp h'
  · intro h
    have HH := mul_le_mul_of_nonneg_left h (pow_pos hd 6).le
    have h' : (4*Real.pi)*Coulomb.tfScalarDensity (d^4*v)≤(4*Real.pi)*(d^6*μ) := by nlinarith only [HH,H]
    exact (mul_le_mul_iff_right₀ hp).mp h'

lemma propagation_gain_density {d R u H μ l1 l2 e ξ hl hh : ℝ}
    (hd : 0<d) (hR : 0<R) (hdR : R/2≤d) (hξ : 0≤ξ)
    (hgap : 16*ξ+2*e<l1-l2)
    (hu : hl≤d^4*u ∧ d^4*u≤hh)
    (hinv : ∀ h∈Icc hl hh,Coulomb.tfScalarDensity h≤d^6*μ → h-ξ≤d^4*H)
    (hnear : H≤u-(l1-l2-2*e)/R^4) : 4*Real.pi*μ≤tfReaction u := by
  by_contra hh'
  have hm : Coulomb.tfScalarDensity (d^4*u)≤d^6*μ :=
    (normalized_reaction_le_density_iff hd).mpr (le_of_not_ge hh')
  have hI := hinv _ hu hm
  have hp : R^4≤16*d^4 := by
    have := pow_le_pow_left₀ (by positivity : 0≤R/2) hdR 4
    nlinarith only [this]
  have hgap' : 16*ξ<l1-l2-2*e := by linarith only [hgap]
  have hd4 : 0<d^4 := pow_pos hd 4
  have hR4 : 0<R^4 := pow_pos hR 4
  have hnear' : H*R^4≤u*R^4-(l1-l2-2*e) := by
    have h := mul_le_mul_of_nonneg_right hnear hR4.le
    field_simp at h
    linarith only [h]
  have hgg : ξ*R^4<(l1-l2-2*e)*d^4 := by
    calc
      _≤ξ*(16*d^4) := mul_le_mul_of_nonneg_left hp hξ
      _<(l1-l2-2*e)*d^4 := by nlinarith only [mul_lt_mul_of_pos_right hgap' hd4]
  have h1 := mul_le_mul_of_nonneg_right hI hR4.le
  have h2 := mul_le_mul_of_nonneg_right hnear' hd4.le
  nlinarith only [h1,h2,hgg]

lemma propagation_outer_reaction {d R H μ l2 ξ hl hh : ℝ}
    (hR : 0<R) (hRd : R≤d) (hξ : 0≤ξ) (hξl : ξ<l2)
    (hv : hl≤d^4*(H-l2/R^4) ∧ d^4*(H-l2/R^4)≤hh)
    (hinv : ∀ h∈Icc hl hh,d^6*μ≤Coulomb.tfScalarDensity h → d^4*H≤h+ξ) :
    tfReaction (H-l2/R^4)≤4*Real.pi*μ := by
  have hd : 0<d := hR.trans_le hRd
  by_contra hh'
  have hm : d^6*μ≤Coulomb.tfScalarDensity (d^4*(H-l2/R^4)) :=
    (normalized_density_le_reaction_iff hd).mpr (le_of_not_ge hh')
  have hI := hinv _ hv hm
  have hp := pow_le_pow_left₀ hR.le hRd 4
  have hR4 := pow_pos hR 4
  have h1 := mul_le_mul_of_nonneg_right hI hR4.le
  have he : (d^4*(H-l2/R^4)+ξ)*R^4=d^4*H*R^4-l2*d^4+ξ*R^4 := by field_simp
  rw [he] at h1
  have h2 := mul_le_mul_of_nonneg_left hp hξ
  have h3 := mul_lt_mul_of_pos_right hξl (pow_pos hd 4)
  nlinarith only [h1,h2,h3]
end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationBarrierBounds
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

lemma tfReaction_div_fourth (v : ℝ) {d : ℝ} (hd : 0<d) :
    tfReaction (v/d^4)=tfReaction v/d^6 := by
  rw [tfReaction_eq_scalar,tfReaction_eq_scalar,Coulomb.tfScalarDensity_scale v hd]
  ring

lemma propagationBarrier_reaction_bound {B r : ℝ} (hB : 0<B) (hr : 0 < r)
    {x : Position} (hx : r≤‖x‖) :
    tfReaction (propagationBarrier B r x)≤(4*Real.pi*kTF*Real.sqrt B)*B/‖x‖^6 := by
  have hd := hr.trans_le hx
  have H := tfReaction_monotone (propagationBarrier_two_sided hB.le hr hx).2
  rw [tfReaction_div_fourth B hd] at H
  have hb : B^(3/2:ℝ)=B*Real.sqrt B := by
    rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add hB,Real.rpow_one,Real.sqrt_eq_rpow]
  have he : tfReaction B=(4*Real.pi*kTF*Real.sqrt B)*B := by
    unfold tfReaction
    rw [max_eq_left hB.le,hb]
    ring
  rw [he] at H
  exact H

theorem propagationBarrier_laplacian_ge_reaction {B r : ℝ} (hB : 0<B) (hr : 0 < r)
    (hsmall : 4*Real.pi*kTF*Real.sqrt B≤19/2) {x : Position} (hx : r≤‖x‖) :
    tfReaction (propagationBarrier B r x) ≤ coordinateLaplacian (propagationBarrier B r) x := by
  have hd := hr.trans_le hx
  have hx0 : x≠0 := norm_pos_iff.mp hd
  have hfrac : 5*r/(2*‖x‖)≤5/2 := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hx])
  rw [laplacian_propagationBarrier hx0]
  calc
    _≤(4*Real.pi*kTF*Real.sqrt B)*B/‖x‖^6 := propagationBarrier_reaction_bound hB hr hx
    _≤(19/2:ℝ)*B/‖x‖^6 := by gcongr
    _≤B/‖x‖^6*(12-5*r/(2*‖x‖)) := by
      have H := mul_le_mul_of_nonneg_left (show (19/2:ℝ)≤12-5*r/(2*‖x‖) by linarith only [hfrac])
        (by positivity : 0≤B/‖x‖^6)
      calc
        _=(B/‖x‖^6)*(19/2:ℝ) := by ring
        _≤_ := H
end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationBarrierOffset
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

lemma propagationBarrier_weak {B R Z : ℝ} (hB : 0<B) (hR : 0<R)
    (hsmall : 4*Real.pi*kTF*Real.sqrt B≤19/2) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+propagationBarrierOffset B R Z x) Z
      {x | R<‖x‖} (fun x => tfReaction (propagationBarrier B R x)) := by
  have hU : IsOpen {x : Position | R<‖x‖} := isOpen_lt continuous_const continuous_norm
  have hsub : {x : Position | R<‖x‖} ⊆ punctured := by
    intro x hx
    exact norm_pos_iff.mp (hR.trans hx)
  have hp : ContDiffOn ℝ 2 (propagationBarrier B R) {x | R<‖x‖} :=
    (contDiffOn_propagationBarrier B R 2).mono hsub
  have hf : ∀ x ∈ {x : Position | R<‖x‖},ContDiffAt ℝ 2 (propagationBarrier B R) x :=
    fun x hx => hp.contDiffAt (hU.mem_nhds hx)
  have hq : LocallyIntegrableOn (fun x => tfReaction (propagationBarrier B R x)) {x | R<‖x‖} :=
    (tfReaction_continuous.comp_continuousOn hp.continuousOn).locallyIntegrableOn hU.measurableSet
  have H := WeakLaplacianGE.of_classical hf hq
    (fun x hx => propagationBarrier_laplacian_ge_reaction hB hR hsmall hx.le)
  apply (H.to_nuclear_away (by simp [not_lt_of_ge hR.le]) Z).congr_on
  · intro x hx
    exact (propagationBarrierOffset_eq hx.le).symm
  · intro x hx
    rfl

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

lemma propagation_near_old_gain {B C r R u H μ M l1 l2 e ξ hl hh : ℝ}
    (hB : 0≤B) (hr : 0 < r) (hR : R=2*r) {x : Position}
    (hx : r≤‖x‖) (hhl : hl≤(7/8:ℝ)*B) (hhh : C≤hh)
    (hu : propagationBarrier B r x≤u ∧ u≤C/‖x‖^4)
    (hξ : 0≤ξ) (hgap : 16*ξ+2*e<l1-l2)
    (hinv : ∀ h∈Icc hl hh,Coulomb.tfScalarDensity h≤‖x‖^6*μ → h-ξ≤‖x‖^4*H)
    (hcandidate : H-l2/R^4≤M) (hnear : M-(u-l1/R^4)<2*e/R^4) :
    4*Real.pi*μ≤tfReaction u := by
  have hd := hr.trans_le hx
  have hRp : 0<R := by rw [hR]; positivity
  apply propagation_gain_density hd hRp (by rw [hR]; linarith only [hx]) hξ hgap
  · exact ⟨hhl.trans (normalized_barrier_lower hB hr hx hu.1),
      (normalized_cap hd hu.2).trans hhh⟩
  · exact hinv
  · exact near_active_old_field hRp hcandidate hnear

lemma propagation_near_physical_reaction {B C R L H μ M l2 e ξ hl hh : ℝ}
    (hB : 0≤B) (hR : 0<R) (hL : 0≤L) (he : 0≤e) {x : Position}
    (hx : R≤‖x‖) (hx' : ‖x‖≤2*L*R)
    (hhl : hl≤(7/8:ℝ)*B-2*e*(2*L)^4) (hhh : C≤hh)
    (hcap : H≤C/‖x‖^4) (hξ : 0≤ξ) (hl2 : 0≤l2) (hξl : ξ<l2)
    (hlower : propagationBarrier B R x≤M) (hnear : M-(H-l2/R^4)<2*e/R^4)
    (hinv : ∀ h∈Icc hl hh,‖x‖^6*μ≤Coulomb.tfScalarDensity h → ‖x‖^4*H≤h+ξ) :
    tfReaction (H-l2/R^4)≤4*Real.pi*μ := by
  have hd := hR.trans_le hx
  apply propagation_outer_reaction hR hx hξ hξl
  · constructor
    · exact hhl.trans (normalized_near_barrier_lower hB hR hL he hx hx'
        (near_active_physical_lower hlower hnear))
    · apply (normalized_cap hd ?_).trans hhh
      exact (sub_le_self _ (div_nonneg hl2 (pow_pos hR 4).le)).trans hcap
  · exact hinv

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationMaximum
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

theorem propagation_finite_max_step {bad : Prop} {B C r R Z L l1 l2 e ξ hl hh : ℝ}
    {u H μ p : Position → ℝ} {U : Set Position} (s : Finset (Fin 3)) (h0 : 0∈s)
    (h1 : 1∈s ↔ ¬bad) (h2 : 2∈s → ∀ x∈U,R<‖x‖)
    (hB : 0<B) (hr : 0 < r) (hR : R=2*r) (hL : 0≤L)
    (hl2 : 0≤l2) (hl21 : l2≤l1) (he : 0<e) (hξ : 0≤ξ)
    (hξl : ξ<l2) (hgap : 16*ξ+2*e<l1-l2)
    (hhl : hl≤(7/8:ℝ)*B-2*e*(2*L)^4) (hhh : C≤hh)
    (hU : IsOpen U) (hUb : ∀ x∈U,‖x‖≤2*L*R)
    (huc : Continuous u) (hHc : Continuous H)
    (hμ : ∀ x,0≤μ x) (hp : ∀ x,0≤p x)
    (hqi : ∀ i∈s,LocallyIntegrable
      (propagationCandidateSources r R Z u μ p (propagationBarrierOffset B R Z) i) volume)
    (hb : Measurable (fun x => propagationCoreSource R ‖x‖ (μ x)
      (propagationStepError bad r R ‖x‖ (μ x) (p x))))
    (hbb : ∀ D : ℝ, ∃ K : ℝ, ∀ x∈Metric.closedBall 0 D,
      |propagationCoreSource R ‖x‖ (μ x) (propagationStepError bad r R ‖x‖ (μ x) (p x))|≤K)
    (hwu : WeakNuclearSubsolution (fun x => Z*coulombKernel x+u x) Z U
      (fun x => propagationRHS r ‖x‖ (μ x) (p x) (Z*coulombKernel x+u x)))
    (hwH : WeakNuclearSubsolution (fun x => Z*coulombKernel x+H x) Z U (fun x => 4*Real.pi*μ x))
    (hsmall : 4*Real.pi*kTF*Real.sqrt B≤19/2)
    (hu : ∀ x,r≤‖x‖ → propagationBarrier B r x≤Z*coulombKernel x+u x ∧
      Z*coulombKernel x+u x≤C/‖x‖^4)
    (hH : ¬bad → ∀ x,r≤‖x‖ → ‖x‖≤2*L*R → Z*coulombKernel x+H x≤C/‖x‖^4)
    (hinv : ¬bad → ∀ x,r≤‖x‖ → ‖x‖≤2*L*R → ∀ h∈Icc hl hh,
      (‖x‖^6*μ x≤Coulomb.tfScalarDensity h → ‖x‖^4*(Z*coulombKernel x+H x)≤h+ξ) ∧
      (Coulomb.tfScalarDensity h≤‖x‖^6*μ x → h-ξ≤‖x‖^4*(Z*coulombKernel x+H x)))
    (hlo : ∀ x∈U,R≤‖x‖ → propagationBarrier B R x≤Z*coulombKernel x+
      s.sup' ⟨0,h0⟩ (fun i => propagationCandidates B R Z l1 l2 u H i x)) :
    WeakNuclearSubsolution
      (fun x => Z*coulombKernel x+s.sup' ⟨0,h0⟩ (fun i => propagationCandidates B R Z l1 l2 u H i x)) Z U
      (fun x => propagationRHS R ‖x‖ (μ x) (propagationStepError bad r R ‖x‖ (μ x) (p x))
        (Z*coulombKernel x+s.sup' ⟨0,h0⟩ (fun i => propagationCandidates B R Z l1 l2 u H i x))) := by
  have hRp : 0<R := by rw [hR]; positivity
  have hrR : r≤R := by rw [hR]; linarith only [hr]
  have hη : 0<e/R^4 := div_pos he (pow_pos hRp 4)
  have hf : ∀ i∈s,Continuous (propagationCandidates B R Z l1 l2 u H i) := by
    intro i hi
    fin_cases i
    · exact huc.sub continuous_const
    · exact hHc.sub continuous_const
    · exact propagationBarrierOffset_continuous B Z hRp
  have hw : ∀ i∈s,WeakNuclearSubsolution
      (fun x => Z*coulombKernel x+propagationCandidates B R Z l1 l2 u H i x) Z U
      (propagationCandidateSources r R Z u μ p (propagationBarrierOffset B R Z) i) := by
    intro i hi
    fin_cases i
    · exact hwu.sub_offset_const huc (l1/R^4)
    · exact hwH.sub_offset_const hHc (l2/R^4)
    · apply ((propagationBarrier_weak (Z:=Z) hB hRp hsmall).mono_domain (h2 hi)).congr_on (fun x hx => rfl)
      intro x hx
      simp [propagationCandidateSources,cutoffReaction,le_of_lt (h2 hi x hx),propagationBarrierOffset_eq]
  have Hmax := WeakNuclearSubsolution.near_active_cutoffTF s ⟨0,h0⟩
    (propagationCandidates B R Z l1 l2 u H)
    (propagationCandidateSources r R Z u μ p (propagationBarrierOffset B R Z))
    hRp hη hU hf hqi hb hbb hw
  apply (Hmax ?_).congr_on (fun x hx => rfl)
  · intro x hx
    simp [propagationRHS,cutoffReaction,Set.indicator]
  · intro i hi x hx hnear
    change propagationRHS R ‖x‖ (μ x) (propagationStepError bad r R ‖x‖ (μ x) (p x))
      (Z*coulombKernel x+propagationCandidates B R Z l1 l2 u H i x) ≤ _
    fin_cases i
    · change propagationRHS R ‖x‖ (μ x) (propagationStepError bad r R ‖x‖ (μ x) (p x))
        (Z*coulombKernel x+(u x-l1/R^4)) ≤ propagationRHS r ‖x‖ (μ x) (p x) (Z*coulombKernel x+u x)
      rw [←add_sub_assoc]
      apply propagation_old_source hrR hRp (hl2.trans hl21)
      intro hbad hrx hRx
      have hcand := Finset.le_sup' (f:=fun j => propagationCandidates B R Z l1 l2 u H j x) ((h1).2 hbad)
      have hn : (Z*coulombKernel x+s.sup' ⟨0,h0⟩ (fun j => propagationCandidates B R Z l1 l2 u H j x))-
          (Z*coulombKernel x+u x-l1/R^4)<2*e/R^4 := by
        change (s.sup' ⟨0,h0⟩ (fun j => propagationCandidates B R Z l1 l2 u H j x))-(u x-l1/R^4)<2*(e/R^4) at hnear
        rw [←mul_div_assoc] at hnear
        linarith only [hnear]
      have hc : Z*coulombKernel x+H x-l2/R^4≤
          Z*coulombKernel x+s.sup' ⟨0,h0⟩ (fun j => propagationCandidates B R Z l1 l2 u H j x) := by
        change H x-l2/R^4 ≤ s.sup' ⟨0,h0⟩ (fun j => propagationCandidates B R Z l1 l2 u H j x) at hcand
        linarith only [hcand]
      have hhlo : hl≤(7/8:ℝ)*B := by
        have ht : 0≤2*e*(2*L)^4 := by positivity
        linarith only [hhl,ht]
      exact propagation_near_old_gain (hl:=hl) (hh:=hh) hB.le hr hR hrx hhlo
        hhh (hu x hrx) hξ hgap (fun a ha => (hinv hbad x hrx (hUb x hx) a ha).2) hc hn
    · have hbad := h1.mp hi
      change propagationRHS R ‖x‖ (μ x) (propagationStepError bad r R ‖x‖ (μ x) (p x))
        (Z*coulombKernel x+(H x-l2/R^4)) ≤ 4*Real.pi*μ x
      rw [←add_sub_assoc]
      apply @propagation_physical_source _ _ _ _ _ _ _ ξ _ (hμ x) (hp x)
      intro hRx
      have hrx := hrR.trans hRx
      apply propagation_near_physical_reaction hB.le hRp hL he.le hRx (hUb x hx) hhl hhh
        (hH hbad x hrx (hUb x hx)) hξ hl2 hξl (hlo x hx hRx)
      · change (s.sup' ⟨0,h0⟩ (fun j => propagationCandidates B R Z l1 l2 u H j x))-(H x-l2/R^4)<2*(e/R^4) at hnear
        rw [←mul_div_assoc] at hnear
        linarith only [hnear]
      · exact fun a ha => (hinv hbad x hrx (hUb x hx) a ha).1
    · have hRx := (h2 hi x hx).le
      simpa [propagationCandidates,propagationCandidateSources,cutoffReaction,hRx] using
        (propagation_barrier_source (bad:=bad) (r:=r) (v:=Z*coulombKernel x+propagationBarrierOffset B R Z x)
          hRx (hμ x) (hp x))

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationRegularity
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

namespace PropagationStepHypotheses
variable {bad : Prop} {B C r R Z L l1 l2 e ξ hl hh : ℝ} {u H μ p : Position → ℝ}
variable (d : PropagationStepHypotheses bad B C r R Z L l1 l2 e ξ hl hh u H μ p)
include d

lemma finite_step {U : Set Position} (s : Finset (Fin 3)) (h0 : 0∈s)
    (h1 : 1∈s ↔ ¬bad) (h2 : 2∈s → ∀ x∈U,R<‖x‖)
    (hU : IsOpen U) (hUb : ∀ x∈U,‖x‖≤2*L*R)
    (hlo : ∀ x∈U,R≤‖x‖ → propagationBarrier B R x≤Z*coulombKernel x+
      s.sup' ⟨0,h0⟩ (fun i => propagationCandidates B R Z l1 l2 u H i x)) :
    WeakNuclearSubsolution
      (fun x => Z*coulombKernel x+s.sup' ⟨0,h0⟩ (fun i => propagationCandidates B R Z l1 l2 u H i x)) Z U
      (fun x => propagationRHS R ‖x‖ (μ x) (propagationStepError bad r R ‖x‖ (μ x) (p x))
        (Z*coulombKernel x+s.sup' ⟨0,h0⟩ (fun i => propagationCandidates B R Z l1 l2 u H i x))) := by
  have hqi : ∀ i∈s,LocallyIntegrable
      (propagationCandidateSources r R Z u μ p (propagationBarrierOffset B R Z) i) volume := by
    intro i hi
    fin_cases i
    · exact propagationRHS_locallyIntegrable d.r_pos d.u_cont d.mu_measurable d.p_measurable d.mu_bounds d.p_bounds
    · exact (locallyIntegrable_of_ball_bounds d.mu_measurable d.mu_bounds).smul (4*Real.pi)
    · exact cutoffReaction_offset_locallyIntegrable d.R_pos (propagationBarrierOffset_continuous B Z d.R_pos)
  exact propagation_finite_max_step s h0 h1 h2 d.B_pos d.r_pos d.R_eq d.L_pos.le
    d.l2_nonneg d.l2_le_l1 d.e_pos d.xi_nonneg d.xi_lt_l2 d.gain_gap d.height_lower d.height_upper
    hU hUb d.u_cont d.H_cont d.mu_nonneg d.p_nonneg hqi
    (propagationCoreSource_measurable d.mu_measurable d.step_error_measurable)
    (propagationCoreSource_ball_bounds d.mu_bounds d.step_error_bounds)
    (d.u_weak.mono_domain (subset_univ _)) (d.H_weak.mono_domain (subset_univ _))
    d.barrier_small d.old_caps d.physical_cap d.inverse hlo

end PropagationStepHypotheses
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationStepWeak
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
namespace PropagationStepHypotheses
variable {bad : Prop} {B C r R Z L l1 l2 e ξ hl hh : ℝ} {u H μ p : Position → ℝ}
variable (d : PropagationStepHypotheses bad B C r R Z L l1 l2 e ξ hl hh u H μ p)
include d

lemma inner_weak : WeakNuclearSubsolution
    (fun x => Z*coulombKernel x+propagationPairOffset bad R l1 l2 u H x) Z {x | ‖x‖<(27/25)*R}
    (fun x => propagationRHS R ‖x‖ (μ x) (propagationStepError bad r R ‖x‖ (μ x) (p x))
      (Z*coulombKernel x+propagationPairOffset bad R l1 l2 u H x)) := by
  have hh : (27/25)*R≤2*L*R := by nlinarith only [mul_pos (show 0<2*L-27/25 by linarith only [d.L_large]) d.R_pos]
  have Hmax := d.finite_step (U:={x | ‖x‖<(27/25)*R}) (propagationInnerIndices bad)
    (zero_mem_propagationInnerIndices bad) (one_mem_propagationInnerIndices bad)
    (fun hi => False.elim (two_not_mem_propagationInnerIndices bad hi))
    (isOpen_lt continuous_norm continuous_const) (fun x hx => hx.le.trans hh)
    (fun x hx hxR => by
      rw [propagationInner_sup]
      exact d.lower_pair hxR (by
        change ‖x‖ < (27/25)*R at hx
        linarith only [hx,d.R_pos]))
  simpa only [propagationInner_sup] using Hmax

lemma middle_weak : WeakNuclearSubsolution
    (fun x => Z*coulombKernel x+max (propagationPairOffset bad R l1 l2 u H x) (propagationBarrierOffset B R Z x)) Z
    {x | (26/25)*R<‖x‖ ∧ ‖x‖<2*L*R}
    (fun x => propagationRHS R ‖x‖ (μ x) (propagationStepError bad r R ‖x‖ (μ x) (p x))
      (Z*coulombKernel x+max (propagationPairOffset bad R l1 l2 u H x) (propagationBarrierOffset B R Z x))) := by
  have Hmax := d.finite_step (U:={x | (26/25)*R<‖x‖ ∧ ‖x‖<2*L*R}) (propagationMiddleIndices bad)
    (zero_mem_propagationMiddleIndices bad) (one_mem_propagationMiddleIndices bad)
    (fun hi x hx => by linarith only [hx.1,d.R_pos])
    ((isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const))
    (fun x hx => hx.2.le) (fun x hx hxR => by
      rw [propagationMiddle_sup]
      have H := le_max_right (propagationPairOffset bad R l1 l2 u H x) (propagationBarrierOffset B R Z x)
      have he := propagationBarrierOffset_eq (B:=B) (Z:=Z) hxR
      linarith only [H,he])
  simpa only [propagationMiddle_sup] using Hmax

lemma outer_weak : WeakNuclearSubsolution
    (fun x => Z*coulombKernel x+propagationBarrierOffset B R Z x) Z {x | L*R<‖x‖}
    (fun x => propagationRHS R ‖x‖ (μ x) (propagationStepError bad r R ‖x‖ (μ x) (p x))
      (Z*coulombKernel x+propagationBarrierOffset B R Z x)) := by
  have hsub : {x : Position | L*R<‖x‖}⊆{x | R<‖x‖} := by
    intro x hx
    have hh : R<L*R := by nlinarith only [mul_pos (show 0<L-1 by linarith only [d.L_large]) d.R_pos]
    exact hh.trans hx
  have hbc := propagationBarrierOffset_continuous B Z d.R_pos
  have Hbar : WeakNuclearSubsolution
      (fun x => Z*coulombKernel x+propagationBarrierOffset B R Z x) Z {x | L*R<‖x‖}
      (cutoffReaction R (fun x => Z*coulombKernel x+propagationBarrierOffset B R Z x)) := by
    apply ((propagationBarrier_weak (Z:=Z) d.B_pos d.R_pos d.barrier_small).mono_domain hsub).congr_on (fun x hx => rfl)
    intro x hx
    have hRx : R ≤ ‖x‖ := le_of_lt (hsub hx)
    simp [cutoffReaction,hRx,propagationBarrierOffset_eq hRx]
  apply (weakNuclearSubsolution_offset_iff hbc).2
  apply ((weakNuclearSubsolution_offset_iff hbc).1 Hbar).mono_source_on
    (cutoffReaction_offset_locallyIntegrable d.R_pos hbc)
    (propagationRHS_locallyIntegrable d.R_pos hbc d.mu_measurable d.step_error_measurable d.mu_bounds d.step_error_bounds)
  exact Eventually.of_forall (fun x hx => by
    have hRx : R ≤ ‖x‖ := le_of_lt (hsub hx)
    simpa [cutoffReaction,hRx] using
      (propagation_barrier_source (bad:=bad) (r:=r) (v:=Z*coulombKernel x+propagationBarrierOffset B R Z x)
        hRx (d.mu_nonneg x) (d.p_nonneg x)))

theorem next_weak : WeakNuclearSubsolution
    (fun x => Z*coulombKernel x+propagationNextOffset bad B R Z L l1 l2 u H x) Z univ
    (fun x => propagationRHS R ‖x‖ (μ x) (propagationStepError bad r R ‖x‖ (μ x) (p x))
      (Z*coulombKernel x+propagationNextOffset bad B R Z L l1 l2 u H x)) := by
  obtain ⟨hlo,hup⟩ := propagation_splice_overlaps d.B_pos d.r_pos d.R_eq d.L_large d.l2_nonneg
    d.l2_le_l1 d.l1_le_gamma d.upper_overlap d.old_caps d.physical_cap
  apply WeakNuclearSubsolution.radialMaxSplice
    (a:=(27/25)*R) (b:=(26/25)*R) (e:=L*R) (c:=2*L*R)
    (q:=fun x v => propagationRHS R ‖x‖ (μ x) (propagationStepError bad r R ‖x‖ (μ x) (p x)) (Z*coulombKernel x+v))
  · linarith only [d.R_pos]
  · linarith only [d.R_pos]
  · nlinarith only [mul_pos (show 0<L-27/25 by linarith only [d.L_large]) d.R_pos]
  · nlinarith only [mul_pos d.L_pos d.R_pos]
  · nlinarith only [mul_pos d.L_pos d.R_pos]
  · exact propagationPairOffset_continuous bad R l1 l2 d.u_cont d.H_cont
  · exact propagationBarrierOffset_continuous B Z d.R_pos
  · exact hlo
  · exact hup
  · exact propagationRHS_locallyIntegrable d.R_pos d.next_continuous d.mu_measurable d.step_error_measurable d.mu_bounds d.step_error_bounds
  · exact d.inner_weak
  · exact d.middle_weak
  · exact d.outer_weak

end PropagationStepHypotheses
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PhysicalLikelihoodBridge
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
namespace NeutralAtom

def observationCoordinateData {n J : ℕ} (ℓ : Fin J → ℝ)
    (z : ObservationSample n J) : (Fin J × (Fin n × Fin 3)) → ℝ :=
  fun ia => z.1 ia.2.1 ia.2.2+ℓ ia.1*z.2 ia.1 ia.2.1 ia.2.2

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PhysicalRetainedLikelihood
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace NeutralAtom

def retainedObservationData {n J : ℕ} (j : ℕ) (ℓ : RetainedScales J j → ℝ)
    (z : ObservationSample n J) : (RetainedScales J j × (Fin n × Fin 3)) → ℝ :=
  fun ia => z.1 ia.2.1 ia.2.2+ℓ ia.1*z.2 ia.1.val ia.2.1 ia.2.2

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace NeutralAtom

def retainedTailObservation {n J : ℕ} (j : ℕ)
    (z : (RetainedScales J j × (Fin n × Fin 3)) → ℝ) : Fin J → UnorderedArray n :=
  fun k => if hk : j≤k.val then forgetOrder (observationArrayPositions ⟨k,hk⟩ z) else forgetOrder 0

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PosteriorDataMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
namespace NeutralAtom

@[simp] lemma unorderedSum_retainedTailObservation {n J : ℕ} {j : ℕ}
    (k : RetainedScales J j) (f : Position → ℝ)
    (z : (RetainedScales J j × (Fin n × Fin 3)) → ℝ) :
    unorderedSum f (retainedTailObservation j z k.val)=
      ∑ i,f (observationArrayPositions k z i) := by
  simp only [retainedTailObservation,dite_eq_left k.property,unorderedSum_forgetOrder]

@[simp] lemma unorderedSum_tailObservation {n J : ℕ} (r : Fin J → ℝ) {j : ℕ}
    (k : Fin J) (hk : j ≤ k.val) (f : Position → ℝ) (z : ObservationSample n J) :
    unorderedSum f (tailObservation r j z k)=∑ i,f (observedOrdered r k z i) := by
  simp only [tailObservation,ite_eq_left hk,observedArray,unorderedSum_forgetOrder]

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationDatumRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma continuous_ball_bounds {f : Position → ℝ} (hf : Continuous f) :
    ∀ D : ℝ,∃ C : ℝ,∀ x∈Metric.closedBall 0 D,|f x|≤C := by
  intro D
  simpa only [Real.norm_eq_abs] using
    (isCompact_closedBall (0:Position) D).exists_bound_of_continuousOn hf.continuousOn

section Datum
variable {Ω : Type*} [MeasurableSpace Ω] {bad : Ω → Prop}
variable {u H μ p : Ω → Position → ℝ} {B r R Z L l1 l2 : ℝ}

lemma propagationPairOffset_joint_measurable (hb : MeasurableSet {o | bad o})
    (hu : Measurable (Function.uncurry u)) (hH : Measurable (Function.uncurry H)) :
    Measurable (fun z : Ω×Position => propagationPairOffset (bad z.1) R l1 l2 (u z.1) (H z.1) z.2) := by
  exact (hu.sub measurable_const).ite (hb.preimage measurable_fst)
    ((hu.sub measurable_const).max (hH.sub measurable_const))

omit [MeasurableSpace Ω] in
lemma propagationPairOffset_uniform_bounds
    (hu : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |u o x|≤C)
    (hH : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |H o x|≤C) :
    ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D →
      |propagationPairOffset (bad o) R l1 l2 (u o) (H o) x|≤C := by
  intro D
  obtain ⟨C,hC⟩ := hu D
  obtain ⟨A,hA⟩ := hH D
  refine ⟨max (C+|l1/R^4|) (A+|l2/R^4|),?_⟩
  intro o x hx
  have h1 := (abs_sub (u o x) (l1/R^4)).trans (add_le_add (hC o x hx) le_rfl)
  have h2 := (abs_sub (H o x) (l2/R^4)).trans (add_le_add (hA o x hx) le_rfl)
  unfold propagationPairOffset
  split_ifs
  · exact h1.trans (le_max_left _ _)
  · exact abs_max_le_max_abs_abs.trans (max_le_max h1 h2)

lemma propagationNextOffset_joint_measurable (hR : 0<R) (hb : MeasurableSet {o | bad o})
    (hu : Measurable (Function.uncurry u)) (hH : Measurable (Function.uncurry H)) :
    Measurable (fun z : Ω×Position => propagationNextOffset (bad z.1) B R Z L l1 l2 (u z.1) (H z.1) z.2) :=
  radialMaxSplice_joint_measurable (f:=fun o => propagationPairOffset (bad o) R l1 l2 (u o) (H o))
    (g:=fun _ => propagationBarrierOffset B R Z) ((53/50)*R) ((3/2)*L*R) (propagationPairOffset_joint_measurable hb hu hH)
    ((propagationBarrierOffset_continuous B Z hR).measurable.comp measurable_snd)

omit [MeasurableSpace Ω] in
lemma propagationNextOffset_uniform_bounds (hR : 0<R)
    (hu : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |u o x|≤C)
    (hH : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |H o x|≤C) :
    ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D →
      |propagationNextOffset (bad o) B R Z L l1 l2 (u o) (H o) x|≤C := by
  intro D
  obtain ⟨C,hC⟩ := propagationPairOffset_uniform_bounds (bad:=bad) (R:=R) (l1:=l1) (l2:=l2) hu hH D
  obtain ⟨A,hA⟩ := continuous_ball_bounds (propagationBarrierOffset_continuous B Z hR) D
  exact ⟨max C A,fun o x hx => radialMaxSplice_abs_bound (hC o x hx) (hA x hx)⟩

lemma propagationStepError_joint_measurable (hb : MeasurableSet {o | bad o})
    (hμ : Measurable (Function.uncurry μ)) (hp : Measurable (Function.uncurry p)) :
    Measurable (fun z : Ω×Position => propagationStepError (bad z.1) r R ‖z.2‖ (μ z.1 z.2) (p z.1 z.2)) := by
  apply hp.add
  exact hμ.ite ((hb.preimage measurable_fst).inter
    ((measurableSet_le measurable_const (continuous_norm.measurable.comp measurable_snd)).inter
      (measurableSet_lt (continuous_norm.measurable.comp measurable_snd) measurable_const))) measurable_const

omit [MeasurableSpace Ω] in
lemma propagationStepError_uniform_bounds
    (hμ : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μ o x|≤C)
    (hp : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |p o x|≤C) :
    ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D →
      |propagationStepError (bad o) r R ‖x‖ (μ o x) (p o x)|≤C := by
  intro D
  obtain ⟨C,hC⟩ := hμ D
  obtain ⟨A,hA⟩ := hp D
  refine ⟨A+max C 0,?_⟩
  intro o x hx
  apply (abs_add_le _ _).trans
  apply add_le_add (hA o x hx)
  split_ifs
  · exact (hC o x hx).trans (le_max_left _ _)
  · simp
end Datum
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

structure PropagationInvariant (B C r Z L : ℝ) (u μ p : Position → ℝ) : Prop where
  continuous_offset : Continuous u
  nonnegative_error : ∀ x,0≤p x
  error_support : ∀ x,r≤‖x‖ → p x=0
  weak : WeakNuclearSubsolution (fun x => Z*coulombKernel x+u x) Z univ
    (fun x => propagationRHS r ‖x‖ (μ x) (p x) (Z*coulombKernel x+u x))
  caps : ∀ x,r≤‖x‖ → propagationBarrier B r x≤Z*coulombKernel x+u x ∧
    Z*coulombKernel x+u x≤C/‖x‖^4
  outer : ∀ x,L*r<‖x‖ → Z*coulombKernel x+u x=propagationBarrier B r x

lemma PropagationStepHypotheses.next_invariant
    {bad : Prop} {B C r R Z L l1 l2 e ξ hl hh : ℝ} {u H μ p : Position → ℝ}
    (d : PropagationStepHypotheses bad B C r R Z L l1 l2 e ξ hl hh u H μ p)
    (hs : ∀ x,r≤‖x‖ → p x=0) :
    PropagationInvariant B C R Z L (propagationNextOffset bad B R Z L l1 l2 u H) μ
      (fun x => propagationStepError bad r R ‖x‖ (μ x) (p x)) :=
  ⟨d.next_continuous,d.next_error_nonneg,d.next_error_support hs,d.next_weak,
    fun _ => d.next_caps,fun _ => d.next_outer⟩

section Average
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {u μ p : Ω → Position → ℝ} {B C r Z L : ℝ}

lemma propagationCoreSource_joint_measurable
    (hμ : Measurable (Function.uncurry μ)) (hp : Measurable (Function.uncurry p)) :
    Measurable (fun z : Ω×Position => propagationCoreSource r ‖z.2‖ (μ z.1 z.2) (p z.1 z.2)) :=
  measurable_const.mul ((hμ.ite (measurableSet_lt
    (continuous_norm.measurable.comp measurable_snd) measurable_const) measurable_const).sub hp)

omit [MeasurableSpace Ω] in
lemma propagationCoreSource_uniform_bounds
    (hμ : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μ o x|≤C)
    (hp : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |p o x|≤C) :
    ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D →
      |propagationCoreSource r ‖x‖ (μ o x) (p o x)|≤C := by
  intro D
  obtain ⟨A,hA⟩ := hμ D
  obtain ⟨K,hK⟩ := hp D
  exact ⟨4*Real.pi*(A+K),fun o x hx => propagationCoreSource_abs_bound (hA o x hx) (hK o x hx)⟩

lemma propagationCoreSource_average (hμ : Measurable (Function.uncurry μ))
    (hp : Measurable (Function.uncurry p))
    (hbμ : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μ o x|≤C)
    (hbp : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |p o x|≤C) (x : Position) :
    (∫ o,propagationCoreSource r ‖x‖ (μ o x) (p o x) ∂P)=
      propagationCoreSource r ‖x‖ (∫ o,μ o x ∂P) (∫ o,p o x ∂P) := by
  obtain h1 := integrable_section_of_ball_bounds (μ:=P) hμ hbμ x
  obtain h2 := integrable_section_of_ball_bounds (μ:=P) hp hbp x
  unfold propagationCoreSource
  split_ifs
  · rw [integral_const_mul,integral_sub h1 h2]
  · simp only [zero_sub,integral_const_mul,integral_neg]

end Average
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_InitialInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma propagationRHS_ball_bounds {r Z : ℝ} {u μ p : Position → ℝ} (hr : 0 < r)
    (hu : Continuous u)
    (hbμ : ∀ D : ℝ,∃ M : ℝ,∀ x∈Metric.closedBall 0 D,|μ x| ≤ M)
    (hbp : ∀ D : ℝ,∃ P : ℝ,∀ x∈Metric.closedBall 0 D,|p x| ≤ P) :
    ∀ D : ℝ,∃ K : ℝ,∀ x∈Metric.closedBall 0 D,
      |propagationRHS r ‖x‖ (μ x) (p x) (Z*coulombKernel x+u x)| ≤ K := by
  intro D
  obtain ⟨A,hA⟩ := propagationCoreSource_ball_bounds (r:=r) hbμ hbp D
  obtain ⟨K,hK⟩ := cutoffReaction_offset_ball_bound (Z:=Z) hr hu D
  refine ⟨A+K,fun x hx => ?_⟩
  rw [propagationRHS_eq]
  exact (abs_add_le _ _).trans (add_le_add (hA x hx) (hK x hx))

structure InitialPropagationData (bad : Prop) (B C Z r a L : ℝ) (H μ : Position → ℝ) : Prop where
  B_pos : 0<B
  Z_nonneg : 0 ≤ Z
  r_pos : 0 < r
  a_nonneg : 0 ≤ a
  L_large : 2 ≤ L
  BZ : B ≤ (1/10:ℝ)*Z*r^3
  C_B : B ≤ C
  C_Z : 32*Z*r^3 ≤ C
  quadratic : 4*a*r^2 ≤ (1/20:ℝ)*Z/r
  reaction : tfReaction (2*Z/r) ≤ 6*a
  barrier_small : 4*Real.pi*kTF*Real.sqrt B ≤ 19/2
  H_cont : Continuous H
  H_nonpos : ∀ x,H x ≤ 0
  H_lower : ¬bad → ∀ x,r ≤ ‖x‖ → ‖x‖ ≤ 2*r → -(1/10:ℝ)*Z/r ≤ H x
  mu_measurable : Measurable μ
  mu_nonneg : ∀ x,0 ≤ μ x
  mu_bounds : ∀ D : ℝ,∃ M : ℝ,∀ x∈Metric.closedBall 0 D,|μ x| ≤ M
  nuclear : WeakNuclearSubsolution (fun x => Z*coulombKernel x+H x) Z univ (fun x => 4*Real.pi*μ x)

namespace InitialPropagationData
variable {bad : Prop} {B C Z r a L : ℝ} {H μ : Position → ℝ}
variable (d : InitialPropagationData bad B C Z r a L H μ)
include d

lemma next_continuous : Continuous (initialNextOffset bad B Z r a H) :=
  initialNextOffset_continuous d.B_pos d.Z_nonneg d.r_pos d.a_nonneg d.BZ d.quadratic d.H_cont d.H_nonpos d.H_lower

lemma branch_weak : WeakNuclearSubsolution
    (fun x => Z*coulombKernel x+initialPropagationOffset bad Z r a H x) Z {x | ‖x‖<2*r}
    (fun x => propagationRHS r ‖x‖ (μ x) (initialPropagationError bad r μ x)
      (Z*coulombKernel x+initialPropagationOffset bad Z r a H x)) :=
  initialPropagationOffset_weak d.Z_nonneg d.r_pos d.a_nonneg d.quadratic d.reaction d.H_cont d.H_nonpos
    d.mu_measurable d.mu_nonneg d.mu_bounds d.nuclear

lemma barrier_weak : WeakNuclearSubsolution
    (fun x => Z*coulombKernel x+propagationBarrierOffset B r Z x) Z {x | r<‖x‖}
    (fun x => propagationRHS r ‖x‖ (μ x) (initialPropagationError bad r μ x)
      (Z*coulombKernel x+propagationBarrierOffset B r Z x)) := by
  apply (propagationBarrier_weak (Z:=Z) d.B_pos d.r_pos d.barrier_small).congr_on
  · intro x hx; rfl
  · intro x hx
    have hrx : r ≤ ‖x‖ := le_of_lt hx
    simp [propagationRHS,propagationCoreSource,initialPropagationError,not_lt_of_ge hrx,hrx,
      propagationBarrierOffset_eq hrx]

lemma middle_weak : WeakNuclearSubsolution
    (fun x => Z*coulombKernel x+max (initialPropagationOffset bad Z r a H x) (propagationBarrierOffset B r Z x))
    Z {x | r<‖x‖ ∧ ‖x‖<2*r}
    (fun x => propagationRHS r ‖x‖ (μ x) (initialPropagationError bad r μ x)
      (Z*coulombKernel x+max (initialPropagationOffset bad Z r a H x) (propagationBarrierOffset B r Z x))) := by
  have hc := initialPropagationOffset_continuous bad Z r a d.H_cont
  have hb := propagationBarrierOffset_continuous B Z d.r_pos
  have he := initialPropagationError_measurable bad r d.mu_measurable
  have heK := initialPropagationError_ball_bounds (bad:=bad) (r:=r) d.mu_bounds
  have Hmax := WeakNuclearSubsolution.max_reaction
    (Z:=Z) (b:=fun _ => 0) (F:=fun x v => propagationRHS r ‖x‖ (μ x) (initialPropagationError bad r μ x) v)
    (U:={x | r<‖x‖ ∧ ‖x‖<2*r})
    ((isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const))
    hc hb
    (by simpa only [zero_add] using propagationRHS_locallyIntegrable (Z:=Z) d.r_pos hc d.mu_measurable he d.mu_bounds heK)
    (by simpa only [zero_add] using propagationRHS_locallyIntegrable (Z:=Z) d.r_pos hb d.mu_measurable he d.mu_bounds heK)
    (by simpa only [zero_add] using propagationRHS_ball_bounds (Z:=Z) d.r_pos hc d.mu_bounds heK)
    (by simpa only [zero_add] using propagationRHS_ball_bounds (Z:=Z) d.r_pos hb d.mu_bounds heK)
    (by simpa only [zero_add] using d.branch_weak.mono_domain (fun x hx => hx.2))
    (by simpa only [zero_add] using d.barrier_weak.mono_domain (fun x hx => hx.1))
  simpa only [zero_add] using Hmax

lemma next_weak : WeakNuclearSubsolution
    (fun x => Z*coulombKernel x+initialNextOffset bad B Z r a H x) Z univ
    (fun x => propagationRHS r ‖x‖ (μ x) (initialPropagationError bad r μ x)
      (Z*coulombKernel x+initialNextOffset bad B Z r a H x)) := by
  apply WeakNuclearSubsolution.radialMaxSplice (a:=(53/50)*r) (b:=r) (e:=(19/10)*r) (c:=2*r)
    (q:=fun x v => propagationRHS r ‖x‖ (μ x) (initialPropagationError bad r μ x) (Z*coulombKernel x+v))
  · linarith only [d.r_pos]
  · linarith only [d.r_pos]
  · linarith only [d.r_pos]
  · linarith only [d.r_pos]
  · linarith only [d.r_pos]
  · exact initialPropagationOffset_continuous bad Z r a d.H_cont
  · exact propagationBarrierOffset_continuous B Z d.r_pos
  · exact fun x hx hx' => initialPropagationOffset_low_overlap d.B_pos d.Z_nonneg d.r_pos d.a_nonneg d.BZ d.H_lower hx hx'
  · exact fun x hx hx' => initialPropagationOffset_high_overlap d.B_pos d.Z_nonneg d.r_pos d.a_nonneg d.quadratic d.H_nonpos hx hx'
  · exact propagationRHS_locallyIntegrable d.r_pos d.next_continuous d.mu_measurable
      (initialPropagationError_measurable bad r d.mu_measurable) d.mu_bounds (initialPropagationError_ball_bounds d.mu_bounds)
  · exact d.branch_weak.mono_domain (fun x hx => by
      change ‖x‖<(53/50)*r at hx
      change ‖x‖<2*r
      linarith only [hx,d.r_pos])
  · exact d.middle_weak
  · exact d.barrier_weak.mono_domain (fun x hx => by
      change (19/10)*r<‖x‖ at hx
      change r<‖x‖
      linarith only [hx,d.r_pos])

end InitialPropagationData
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
namespace InitialPropagationData
variable {bad : Prop} {B C Z r a L : ℝ} {H μ : Position → ℝ}
variable (d : InitialPropagationData bad B C Z r a L H μ)
include d

lemma branch_cap {x : Position} (hx : r ≤ ‖x‖) (hx' : ‖x‖ ≤ 2*r) :
    Z*coulombKernel x+initialPropagationOffset bad Z r a H x ≤ C/‖x‖^4 := by
  have hd := d.r_pos.trans_le hx
  have H := initialPropagationOffset_upper (bad:=bad) d.Z_nonneg d.r_pos d.a_nonneg d.quadratic d.H_nonpos hx hx'
  have hp := pow_le_pow_left₀ (norm_nonneg x) hx' 4
  have hpre : (2*Z/r)*‖x‖^4 ≤ C := by
    have hmul := mul_le_mul_of_nonneg_left hp (div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) d.Z_nonneg) d.r_pos.le)
    calc
      _ ≤ (2*Z/r)*(2*r)^4 := hmul
      _ = 32*Z*r^3 := by field_simp; ring
      _ ≤ C := d.C_Z
  exact H.trans ((le_div_iff₀ (pow_pos hd 4)).mpr hpre)

lemma next_caps {x : Position} (hx : r ≤ ‖x‖) :
    propagationBarrier B r x ≤ Z*coulombKernel x+initialNextOffset bad B Z r a H x ∧
    Z*coulombKernel x+initialNextOffset bad B Z r a H x ≤ C/‖x‖^4 := by
  have hd := d.r_pos.trans_le hx
  have hbar := (propagationBarrier_two_sided d.B_pos.le d.r_pos hx).2.trans
    (div_le_div_of_nonneg_right d.C_B (pow_pos hd 4).le)
  have he := propagationBarrierOffset_eq (B:=B) (Z:=Z) hx
  unfold initialNextOffset radialMaxSplice
  split_ifs with hα hβ
  · have hlow := initialPropagationOffset_low_overlap d.B_pos d.Z_nonneg d.r_pos d.a_nonneg d.BZ d.H_lower hx
      (show ‖x‖ ≤ (53/50)*r by linarith only [hα,d.r_pos])
    refine ⟨?_,d.branch_cap hx (by linarith only [hα,d.r_pos])⟩
    linarith only [hlow,he]
  · have hlow := le_max_right (initialPropagationOffset bad Z r a H x) (propagationBarrierOffset B r Z x)
    refine ⟨by linarith only [hlow,he],?_⟩
    rw [add_max]
    exact max_le (d.branch_cap hx (by linarith only [hβ,d.r_pos])) (by simpa only [he] using hbar)
  · simpa only [he] using And.intro le_rfl hbar

lemma next_outer {x : Position} (hx : L*r<‖x‖) :
    Z*coulombKernel x+initialNextOffset bad B Z r a H x=propagationBarrier B r x := by
  have h2 : 2*r ≤ L*r := mul_le_mul_of_nonneg_right d.L_large d.r_pos.le
  have h1 : r ≤ ‖x‖ := by linarith only [hx,h2,d.r_pos]
  have hα : ¬‖x‖<(103/100)*r := by linarith only [hx,h2,d.r_pos]
  have hβ : ¬‖x‖<(39/20)*r := by linarith only [hx,h2,d.r_pos]
  simpa only [initialNextOffset,radialMaxSplice,ite_eq_right hα,ite_eq_right hβ] using
    (propagationBarrierOffset_eq (B:=B) (Z:=Z) h1)

theorem invariant : PropagationInvariant B C r Z L (initialNextOffset bad B Z r a H) μ
    (initialPropagationError bad r μ) :=
  ⟨d.next_continuous,initialPropagationError_nonneg d.mu_nonneg,
    fun _ hx => initialPropagationError_support bad r μ hx,d.next_weak,
    fun _ hx => d.next_caps hx,fun _ hx => d.next_outer hx⟩

end InitialPropagationData
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationAverageAE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
noncomputable section
namespace NeutralAtom
section Average
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem continuous_average_ae_of_ball_bounds {f : Ω → Position → ℝ}
    (hf : ∀ᵐ o ∂μ, Continuous (f o)) (hm : Measurable (Function.uncurry f))
    (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |f o x| ≤ C) :
    Continuous (fun x => ∫ o, f o x ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨C,hC⟩ := hb (‖x₀‖+1)
  apply continuousAt_of_dominated
    (Eventually.of_forall (fun x => (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable))
    (bound := fun _ => C) ?_ (integrable_const C)
    (hf.mono (fun o ho => ho.continuousAt))
  filter_upwards [Metric.ball_mem_nhds x₀ (by norm_num : (0:ℝ)<1)] with x hx
  filter_upwards [] with o
  have hdist : ‖x-x₀‖<1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
  have hn : ‖x‖≤‖x₀‖+1 := by
    have h := norm_add_le (x-x₀) x₀
    rw [sub_add_cancel] at h
    linarith
  change ‖f o x‖ ≤ C
  simpa only [Real.norm_eq_abs] using hC o x (by simpa using hn)

theorem WeakNuclearSubsolution.average_ae {f q : Ω → Position → ℝ} {Z : ℝ} {U : Set Position}
    (hf : ∀ᵐ o ∂μ, Continuous (f o))
    (hcf : Continuous (fun x => ∫ o, f o x ∂μ))
    (hmf : Measurable (Function.uncurry f)) (hmq : Measurable (Function.uncurry q))
    (hbf : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |f o x| ≤ C)
    (hbq : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |q o x| ≤ C)
    (hw : ∀ᵐ o ∂μ, WeakNuclearSubsolution (fun x => Z*coulombKernel x+f o x) Z U (q o)) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+∫ o, f o x ∂μ) Z U
      (fun x => ∫ o, q o x ∂μ) := by
  apply (weakNuclearSubsolution_offset_iff hcf).2
  apply WeakLaplacianGE.average hmf hmq hbf hbq
  filter_upwards [hw,hf] with o ho hf
  exact (weakNuclearSubsolution_offset_iff hf).1 ho

theorem WeakNuclearSubsolution.average_cutoffTF_ae {a Z : ℝ} {U : Set Position}
    {f b : Ω → Position → ℝ} (ha : 0<a)
    (hf : ∀ᵐ o ∂μ, Continuous (f o))
    (hmf : Measurable (Function.uncurry f)) (hmb : Measurable (Function.uncurry b))
    (hbf : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |f o x| ≤ C)
    (hbb : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |b o x| ≤ C)
    (hw : ∀ᵐ o ∂μ, WeakNuclearSubsolution (fun x => Z*coulombKernel x+f o x) Z U
      (fun x => b o x+cutoffReaction a (fun y => Z*coulombKernel y+f o y) x)) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+∫ o, f o x ∂μ) Z U
      (fun x => (∫ o, b o x ∂μ)+cutoffReaction a (fun y => Z*coulombKernel y+∫ o, f o y ∂μ) x) := by
  let q : Ω → Position → ℝ := fun o x => b o x+cutoffReaction a (fun y => Z*coulombKernel y+f o y) x
  have hmq : Measurable (Function.uncurry q) := hmb.add (cutoffReaction_offset_joint_measurable hmf)
  have hbc := cutoffReaction_offset_uniform_bound (Z:=Z) ha hbf
  have hbq : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |q o x| ≤ C := by
    intro R
    obtain ⟨C,hC⟩ := hbb R
    obtain ⟨D,hD⟩ := hbc R
    exact ⟨C+D,fun o x hx => (abs_add_le _ _).trans (add_le_add (hC o x hx) (hD o x hx))⟩
  have hc := continuous_average_ae_of_ball_bounds (μ:=μ) hf hmf hbf
  have H := WeakNuclearSubsolution.average_ae hf hc hmf hmq hbf hbq hw
  apply (weakNuclearSubsolution_offset_iff hc).2
  apply ((weakNuclearSubsolution_offset_iff hc).1 H).mono_source_on
  · exact locallyIntegrable_of_ball_bounds hmq.stronglyMeasurable.integral_prod_left.measurable
      (average_ball_bounds (μ:=μ) hbq)
  · exact (locallyIntegrable_of_ball_bounds hmb.stronglyMeasurable.integral_prod_left.measurable
      (average_ball_bounds (μ:=μ) hbb)).add (cutoffReaction_offset_locallyIntegrable ha hc)
  · filter_upwards [] with x hx
    have hib := integrable_section_of_ball_bounds (μ:=μ) hmb hbb x
    have hic := integrable_section_of_ball_bounds (μ:=μ)
      (f:=fun o x => cutoffReaction a (fun y => Z*coulombKernel y+f o y) x)
      (cutoffReaction_offset_joint_measurable hmf) hbc x
    change (∫ o, b o x ∂μ)+cutoffReaction a (fun y => Z*coulombKernel y+∫ o, f o y ∂μ) x ≤
      ∫ o, b o x+cutoffReaction a (fun y => Z*coulombKernel y+f o y) x ∂μ
    rw [integral_add hib hic]
    have h := cutoffReaction_average_le (μ:=μ) (a:=a) (Z:=Z) hmf hbf x
    linarith

end Average
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
section Average
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {u μ p : Ω → Position → ℝ} {B C r Z L : ℝ}
theorem PropagationInvariant.average_ae (hr : 0 < r)
    (hi : ∀ᵐ o ∂P,PropagationInvariant B C r Z L (u o) (μ o) (p o))
    (hu : Measurable (Function.uncurry u)) (hμ : Measurable (Function.uncurry μ))
    (hp : Measurable (Function.uncurry p))
    (hbu : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |u o x|≤C)
    (hbμ : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μ o x|≤C)
    (hbp : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |p o x|≤C) :
    PropagationInvariant B C r Z L (fun x => ∫ o,u o x ∂P)
      (fun x => ∫ o,μ o x ∂P) (fun x => ∫ o,p o x ∂P) := by
  constructor
  · exact continuous_average_ae_of_ball_bounds (hi.mono (fun o ho => ho.continuous_offset)) hu hbu
  · intro x
    exact integral_nonneg_of_ae (hi.mono (fun o ho => ho.nonnegative_error x))
  · intro x hx
    exact integral_eq_zero_of_ae (hi.mono (fun o ho => ho.error_support x hx))
  · have H := WeakNuclearSubsolution.average_cutoffTF_ae (μ:=P) (Z:=Z)
      (b:=fun o x => propagationCoreSource r ‖x‖ (μ o x) (p o x)) hr
      (hi.mono (fun o ho => ho.continuous_offset)) hu (propagationCoreSource_joint_measurable (r:=r) hμ hp)
      hbu (propagationCoreSource_uniform_bounds (r:=r) hbμ hbp)
      (hi.mono (fun o ho => by simpa only [propagationRHS_eq] using ho.weak))
    simp only [propagationCoreSource_average hμ hp hbμ hbp] at H
    simpa only [propagationRHS,cutoffReaction,Set.indicator,Set.mem_ofPred_eq] using H
  · intro x hx
    have hiu := integrable_section_of_ball_bounds (μ:=P) hu hbu x
    have hii := (integrable_const (Z*coulombKernel x)).add hiu
    have he : (∫ o,Z*coulombKernel x+u o x ∂P)=Z*coulombKernel x+∫ o,u o x ∂P := by
      rw [integral_add (integrable_const _) hiu]; simp
    constructor
    · have H := integral_mono_ae (integrable_const (propagationBarrier B r x)) hii
        (hi.mono (fun o ho => (ho.caps x hx).1))
      change (∫ _ : Ω,propagationBarrier B r x ∂P) ≤ (∫ o,Z*coulombKernel x+u o x ∂P) at H
      simpa only [integral_const,probReal_univ,one_smul,he] using H
    · have H := integral_mono_ae hii (integrable_const (C/‖x‖^4))
        (hi.mono (fun o ho => (ho.caps x hx).2))
      change (∫ o,Z*coulombKernel x+u o x ∂P) ≤ (∫ _ : Ω,C/‖x‖^4 ∂P) at H
      simpa only [integral_const,probReal_univ,one_smul,he] using H
  · intro x hx
    have hiu := integrable_section_of_ball_bounds (μ:=P) hu hbu x
    have he : (∫ o,Z*coulombKernel x+u o x ∂P)=Z*coulombKernel x+∫ o,u o x ∂P := by
      rw [integral_add (integrable_const _) hiu]; simp
    rw [←he]
    calc
      _ = ∫ _ : Ω,propagationBarrier B r x ∂P := integral_congr_ae (hi.mono (fun o ho => ho.outer x hx))
      _ = _ := by simp
end Average
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PosteriorDensityContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter ProbabilityTheory
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
section Posterior
variable {Ω A : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace A]
variable (P : Measure Ω) [IsProbabilityMeasure P] (obs : Ω → A)

def posteriorAverage (f : Ω → Position → ℝ) (a : A) (x : Position) : ℝ :=
  ∫ o,f o x ∂ProbabilityTheory.condDistrib id obs P a
lemma posteriorAverage_joint_measurable {f : Ω → Position → ℝ}
    (hf : Measurable (Function.uncurry f)) : Measurable (Function.uncurry (posteriorAverage P obs f)) := by
  let κ : ProbabilityTheory.Kernel (A×Position) Ω := (ProbabilityTheory.condDistrib id obs P).comap (Prod.fst : A×Position → A) measurable_fst
  have H : StronglyMeasurable (fun z : (A×Position)×Ω => f z.2 z.1.2) :=
    hf.stronglyMeasurable.comp_measurable (measurable_snd.prodMk measurable_fst.snd)
  exact (H.integral_kernel_prod_right' (κ:=κ)).measurable
lemma posteriorAverage_uniform_bounds {f : Ω → Position → ℝ}
    (hb : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |f o x|≤C) :
    ∀ D : ℝ,∃ C : ℝ,∀ a x,x∈Metric.closedBall 0 D → |posteriorAverage P obs f a x|≤C := by
  intro D
  obtain ⟨C,hC⟩ := hb D
  refine ⟨C,fun a x hx => ?_⟩
  calc
    |posteriorAverage P obs f a x| ≤ ∫ o, |f o x| ∂ProbabilityTheory.condDistrib id obs P a := abs_integral_le_integral_abs
    _ ≤ ∫ _ : Ω, C ∂ProbabilityTheory.condDistrib id obs P a := integral_mono_of_nonneg
      (Eventually.of_forall (fun o => abs_nonneg (f o x))) (integrable_const C)
      (Eventually.of_forall (fun o => hC o x hx))
    _ = C := by simp
lemma posteriorAverage_invariant {B C r Z L : ℝ} (hr : 0 < r) (ho : Measurable obs)
    {u μ p : Ω → Position → ℝ}
    (hi : ∀ᵐ o ∂P,PropagationInvariant B C r Z L (u o) (μ o) (p o))
    (hu : Measurable (Function.uncurry u)) (hμ : Measurable (Function.uncurry μ))
    (hp : Measurable (Function.uncurry p))
    (hbu : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |u o x|≤C)
    (hbμ : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μ o x|≤C)
    (hbp : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |p o x|≤C) :
    ∀ᵐ o ∂P,PropagationInvariant B C r Z L (posteriorAverage P obs u (obs o))
      (posteriorAverage P obs μ (obs o)) (posteriorAverage P obs p (obs o)) := by
  filter_upwards [posterior_ae P obs ho hi] with o h
  exact PropagationInvariant.average_ae hr h hu hμ hp hbu hbμ hbp
end Posterior
end NeutralAtom
end

end
section
open MeasureTheory
noncomputable section
namespace NeutralAtom
instance observationSample_standardBorel (n J : ℕ) : StandardBorelSpace (ObservationSample n J) :=
  StandardBorelSpace.prod
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationPosteriorStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

structure PropagationDatum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B C r Z L : ℝ) (μ : Ω → Position → ℝ) where
  offset : Ω → Position → ℝ
  error : Ω → Position → ℝ
  offset_measurable : Measurable (Function.uncurry offset)
  error_measurable : Measurable (Function.uncurry error)
  offset_bounds : ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D → |offset o x|≤A
  error_bounds : ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D → |error o x|≤A
  invariant : ∀ᵐ o ∂P,PropagationInvariant B C r Z L (offset o) (μ o) (error o)

section Step
variable {Ω A : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace A]
variable {P : Measure Ω} [IsProbabilityMeasure P] {B C r R Z L l1 l2 e ξ hl hh : ℝ}
variable {μ μ' H : Ω → Position → ℝ} {bad : Ω → Prop}

def PropagationDatum.posteriorStep (d : PropagationDatum P B C r Z L μ)
    (obs : Ω → A) (ho : Measurable obs) (hR : 0<R)
    (hb : MeasurableSet {o | bad o})
    (hH : Measurable (Function.uncurry H)) (hμ : Measurable (Function.uncurry μ))
    (hbH : ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D → |H o x|≤A)
    (hbμ : ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μ o x|≤A)
    (hstep : ∀ᵐ o ∂P,PropagationStepHypotheses (bad o) B C r R Z L l1 l2 e ξ hl hh
      (d.offset o) (H o) (μ o) (d.error o))
    (htower : ∀ᵐ o ∂P,posteriorAverage P obs μ (obs o)=μ' o) :
    PropagationDatum P B C R Z L μ' := by
  let v := fun o => propagationNextOffset (bad o) B R Z L l1 l2 (d.offset o) (H o)
  let q := fun o x => propagationStepError (bad o) r R ‖x‖ (μ o x) (d.error o x)
  have hv := propagationNextOffset_joint_measurable (B:=B) (Z:=Z) (L:=L) (l1:=l1) (l2:=l2)
    hR hb d.offset_measurable hH
  have hq := propagationStepError_joint_measurable (r:=r) (R:=R) hb hμ d.error_measurable
  have hvb := propagationNextOffset_uniform_bounds (bad:=bad) (B:=B) (Z:=Z) (L:=L) (l1:=l1) (l2:=l2)
    hR d.offset_bounds hbH
  have hqb := propagationStepError_uniform_bounds (bad:=bad) (r:=r) (R:=R) hbμ d.error_bounds
  refine ⟨fun o => posteriorAverage P obs v (obs o),fun o => posteriorAverage P obs q (obs o),
    (posteriorAverage_joint_measurable P obs (f:=v) hv).comp (ho.prodMap measurable_id),
    (posteriorAverage_joint_measurable P obs (f:=q) hq).comp (ho.prodMap measurable_id),?_,?_,?_⟩
  · intro D
    obtain ⟨K,hK⟩ := posteriorAverage_uniform_bounds P obs hvb D
    exact ⟨K,fun o => hK (obs o)⟩
  · intro D
    obtain ⟨K,hK⟩ := posteriorAverage_uniform_bounds P obs hqb D
    exact ⟨K,fun o => hK (obs o)⟩
  · have hi : ∀ᵐ o ∂P,PropagationInvariant B C R Z L (v o) (μ o) (q o) := by
      filter_upwards [d.invariant,hstep] with o hoi hos
      exact hos.next_invariant hoi.error_support
    have Havg := posteriorAverage_invariant P obs hR ho hi hv hμ hq hvb hbμ hqb
    filter_upwards [Havg,htower] with o hi ht
    simpa only [ht] using hi
end Step
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_InitialDatum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
section Init
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {bad : Ω → Prop} {H μ : Ω → Position → ℝ} {B C Z r a L : ℝ}
lemma initialPropagationOffset_joint_measurable (hb : MeasurableSet {o | bad o})
    (hH : Measurable (Function.uncurry H)) :
    Measurable (fun z : Ω×Position => initialPropagationOffset (bad z.1) Z r a (H z.1) z.2) := by
  exact ((measurable_const.ite (hb.preimage measurable_fst) hH).sub measurable_const).add
    (measurable_const.mul ((continuous_norm.measurable.comp measurable_snd).pow_const 2))

omit [MeasurableSpace Ω] in
lemma initialPropagationOffset_uniform_bounds
    (hbH : ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D → |H o x|≤A) :
    ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D →
      |initialPropagationOffset (bad o) Z r a (H o) x|≤A := by
  intro D
  obtain ⟨K,hK⟩ := hbH D
  refine ⟨max 0 K+|(7/10:ℝ)*Z/r|+|a| * D^2,fun o x hx => ?_⟩
  have hn : ‖x‖≤D := by simpa using hx
  have h2 : ‖x‖^2≤D^2 := pow_le_pow_left₀ (norm_nonneg x) hn 2
  have hi : |if bad o then (0:ℝ) else H o x| ≤ max 0 K := by
    split_ifs
    · simpa only [abs_zero] using le_max_left 0 K
    · exact (hK o x hx).trans (le_max_right 0 K)
  exact (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add hi le_rfl))
    (by rw [abs_mul,abs_of_nonneg (sq_nonneg ‖x‖)]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg a)))

lemma initialNextOffset_joint_measurable (hr : 0 < r) (hb : MeasurableSet {o | bad o})
    (hH : Measurable (Function.uncurry H)) :
    Measurable (fun z : Ω×Position => initialNextOffset (bad z.1) B Z r a (H z.1) z.2) :=
  radialMaxSplice_joint_measurable (f:=fun o => initialPropagationOffset (bad o) Z r a (H o))
    (g:=fun _ => propagationBarrierOffset B r Z) ((103/100)*r) ((39/20)*r)
    (initialPropagationOffset_joint_measurable hb hH)
    ((propagationBarrierOffset_continuous B Z hr).measurable.comp measurable_snd)

omit [MeasurableSpace Ω] in
lemma initialNextOffset_uniform_bounds (hr : 0 < r)
    (hbH : ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D → |H o x|≤A) :
    ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D →
      |initialNextOffset (bad o) B Z r a (H o) x|≤A := by
  intro D
  obtain ⟨K,hK⟩ := initialPropagationOffset_uniform_bounds (bad:=bad) (Z:=Z) (r:=r) (a:=a) hbH D
  obtain ⟨A,hA⟩ := continuous_ball_bounds (propagationBarrierOffset_continuous B Z hr) D
  exact ⟨max K A,fun o x hx => radialMaxSplice_abs_bound (hK o x hx) (hA x hx)⟩

lemma initialPropagationError_joint_measurable (hb : MeasurableSet {o | bad o})
    (hμ : Measurable (Function.uncurry μ)) :
    Measurable (fun z : Ω×Position => initialPropagationError (bad z.1) r (μ z.1) z.2) :=
  hμ.ite ((hb.preimage measurable_fst).inter (measurableSet_lt
    (continuous_norm.measurable.comp measurable_snd) measurable_const)) measurable_const

omit [MeasurableSpace Ω] in
lemma initialPropagationError_uniform_bounds
    (hbμ : ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μ o x|≤A) :
    ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D →
      |initialPropagationError (bad o) r (μ o) x|≤A := by
  intro D
  obtain ⟨K,hK⟩ := hbμ D
  refine ⟨max K 0,fun o x hx => ?_⟩
  unfold initialPropagationError
  split_ifs
  · exact (hK o x hx).trans (le_max_left K 0)
  · simpa only [abs_zero] using le_max_right K 0

def initialPropagationDatum (hr : 0 < r) (hb : MeasurableSet {o | bad o})
    (hH : Measurable (Function.uncurry H)) (hμ : Measurable (Function.uncurry μ))
    (hbH : ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D → |H o x|≤A)
    (hbμ : ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μ o x|≤A)
    (hd : ∀ᵐ o ∂P,InitialPropagationData (bad o) B C Z r a L (H o) (μ o)) :
    PropagationDatum P B C r Z L μ :=
  ⟨fun o => initialNextOffset (bad o) B Z r a (H o),fun o => initialPropagationError (bad o) r (μ o),
    initialNextOffset_joint_measurable hr hb hH,initialPropagationError_joint_measurable hb hμ,
    initialNextOffset_uniform_bounds hr hbH,initialPropagationError_uniform_bounds hbμ,
    hd.mono (fun _ h => h.invariant)⟩
end Init
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservationAnnulusTail
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom

def observationSingleScale {n J : ℕ} (k : Fin J)
    (sample : ObservationSample n J) : ObservationSample n 1 :=
  (sample.1, fun _ => sample.2 k)

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PosteriorPropagationData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

structure NuclearRandomDatum {Ω : Type*} [MeasurableSpace Ω] (Z : ℝ)
    (μ H : Ω → Position → ℝ) : Prop where
  mu_measurable : Measurable (Function.uncurry μ)
  H_measurable : Measurable (Function.uncurry H)
  mu_bounds : ∀ D : ℝ,∃ M : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μ o x|≤M
  H_bounds : ∀ D : ℝ,∃ M : ℝ,∀ o x,x∈Metric.closedBall 0 D → |H o x|≤M
  continuous_H : ∀ o,Continuous (H o)
  nonpositive_H : ∀ o x,H o x≤0
  nonnegative_mu : ∀ o x,0≤μ o x
  integrable_mu : ∀ o,Integrable (μ o)
  nuclear : ∀ o,WeakNuclearSubsolution (fun x => Z*coulombKernel x+H o x) Z univ
    (fun x => 4*Real.pi*μ o x)

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_RetainedGoodEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace NeutralAtom
lemma barrierSource_eq_propagationRHS (r : ℝ) (u μ p : Position → ℝ) (x : Position) :
    barrierSource r u μ p x = propagationRHS r ‖x‖ (μ x) (p x) (u x) := by
  unfold barrierSource cutoffReaction propagationRHS propagationCoreSource
  simp only [Set.indicator_apply,Set.mem_ofPred_eq]
  ring

lemma PropagationDatum.error_global_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B C r Z L : ℝ} {μ : Ω → Position → ℝ}
    (d : PropagationDatum P B C r Z L μ) :
    ∃ A : ℝ,∀ o,PropagationInvariant B C r Z L (d.offset o) (μ o) (d.error o) →
      ∀ x,d.error o x ≤ A := by
  obtain ⟨A,hA⟩ := d.error_bounds r
  refine ⟨max A 0,?_⟩
  intro o ho x
  by_cases hx : ‖x‖ ≤ r
  · exact (le_abs_self _).trans ((hA o x (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)).trans (le_max_left _ _))
  · rw [ho.error_support x (le_of_not_ge hx)]
    exact le_max_right _ _
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_QuantumRetainedFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace NeutralAtom

def physical_family_of_data {Ω : ℕ → Type*} [∀ n,MeasurableSpace (Ω n)]
    (P : ∀ n,Measure (Ω n)) (μ : ∀ n,Ω n → Position → ℝ)
    (Z q : ℕ → ℕ) (s r : ℕ → ℝ) (B C L Ccap : ℝ)
    (hB : 0 < B) (hcap : 0 ≤ Ccap) (hs : ∀ n,0 < s n) (hr : ∀ n,0 < r n)
    (hslim : Tendsto s atTop (𝓝 0)) (hqlim : Tendsto q atTop atTop)
    (hlo : ∀ n,1/(2*(q n:ℝ)) ≤ r n/s n) (hhi : ∀ n,r n/s n ≤ (q n:ℝ)⁻¹)
    (hμi : ∀ n o,Integrable (μ n o)) (hμp : ∀ n o x,0 ≤ μ n o x)
    (Aμ : ℕ → ℝ) (hμb : ∀ n o x,μ n o x ≤ Aμ n)
    (hμmass : ∀ n o,(∫ x,μ n o x)=(Z n:ℝ))
    (d : ∀ n,PropagationDatum (P n) B C (r n) (Z n:ℝ) L (μ n))
    (G : ∀ n,Set (Ω n))
    (hvalid : ∀ n o,o∈G n → PropagationInvariant B C (r n) (Z n:ℝ) L
      ((d n).offset o) (μ n o) ((d n).error o) ∧ Integrable ((d n).error o) ∧
      (∫ x,(d n).error o x) ≤ 1)
    (hband : ∀ n o,o∈G n → ∀ x,r n ≤ ‖x‖ → ‖x‖ ≤ (q n:ℝ)*s n →
      screenedField (Z n:ℝ) (μ n o) x ≤ Ccap/‖x‖^4 ∧
      |μ n o x-tfDensityScalar (screenedField (Z n:ℝ) (μ n o) x)| ≤ ((q n:ℝ)^8)⁻¹/‖x‖^6) :
    PhysicalRetainedFamily (fun n => G n) where
  μ := fun n o => μ n o
  u := fun n o x => (Z n:ℝ)*coulombKernel x+(d n).offset o x
  p := fun n o => (d n).error o
  Z := Z
  s := s
  r := r
  q := q
  Aμ := fun n _ => Aμ n
  Ap := fun n _ => ((d n).error_global_bound).choose
  B := B
  Ccap := Ccap
  Cinv := C
  Bpos := hB
  Cpos := hcap
  sp := hs
  rp := hr
  slim := hslim
  qlim := hqlim
  rlo := hlo
  rhi := hhi
  μi := fun n o => hμi n o
  μp := fun n o => hμp n o
  μb := fun n o => hμb n o
  μmass := fun n o => hμmass n o
  pi := fun n o => (hvalid n o o.property).2.1
  pp := fun n o => (hvalid n o o.property).1.nonnegative_error
  pb := fun n o => ((d n).error_global_bound).choose_spec o (hvalid n o o.property).1
  ps := fun n o x hx => (hvalid n o o.property).1.error_support x hx.le
  pm := fun n o => (hvalid n o o.property).2.2
  ucont := fun n o => by simpa only [add_sub_cancel_left] using (hvalid n o o.property).1.continuous_offset
  ubounds := fun n o x hx => by
    simpa only [propagationBarrier_eq] using (hvalid n o o.property).1.caps x hx
  uweak := fun n o => by
    rw [show barrierSource (r n) (fun x => (Z n:ℝ)*coulombKernel x+(d n).offset o x)
      (μ n o) ((d n).error o) = (fun x => propagationRHS (r n) ‖x‖ (μ n o x)
        ((d n).error o x) ((Z n:ℝ)*coulombKernel x+(d n).offset o x)) from
      funext (barrierSource_eq_propagationRHS _ _ _ _)]
    exact (hvalid n o o.property).1.weak
  band := fun n o => hband n o o.property
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_SpectralTheory_BindingCut
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical ContDiff
noncomputable section
namespace Coulomb
def bindingCut (r:ℝ) (l:Fin 2) : Space → ℝ := radialCut 0 r (Equiv.swap 0 1 l)
lemma bindingCut_smooth (r:ℝ) (l:Fin 2) : ContDiff ℝ ∞ (bindingCut r l) := radialCut_smooth ..
lemma bindingCut_partition (r:ℝ) (z:Space) : ∑ l,bindingCut r l z^2=1 := by
  rw [show (∑ l,bindingCut r l z^2)=∑ l,radialCut 0 r l z^2 from Equiv.sum_comp (Equiv.swap (0:Fin 2) 1) (fun l => radialCut 0 r l z^2)]
  exact radialCut_partition 0 r z
lemma bindingCut_derivative {r:ℝ} (hr:0 < r) (l:Fin 2) (b:Fin 3) (z:Space) :
    |fderiv ℝ (bindingCut r l) z (EuclideanSpace.single b 1)| ≤ radialCutCoefficient/r :=
  radialCut_derivative_bound 0 hr _ b z

def bindingLocalized {n:ℕ} (u:H1Vector n) {r:ℝ} (hr:0 < r) (p:Fin n → Fin 2) : H1Vector n :=
  u.labelCut (bindingCut r) (bindingCut_smooth r) (bindingCut_partition r) (radialCutCoefficient/r)
    (div_nonneg radialCutCoefficient_pos.le hr.le) (bindingCut_derivative hr) p

def configurationBox (n:ℕ) (r:ℝ) : Set (Configuration n) := {x | ∀ i,‖position x i‖ ≤ 2*r}
lemma configurationBox_measurable (n:ℕ) (r:ℝ) : MeasurableSet (configurationBox n r) := by
  simpa only [configurationBox,ofPred_forall,positionCLM_apply] using
    MeasurableSet.iInter (fun i:Fin n => (isClosed_le (positionCLM i).continuous.norm (continuous_const (y:=2*r))).measurableSet)
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_QuantumProfileDatum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom

def profileDensity {N : ℕ} (ψ : Wavefunction (N+1)) [IsProbabilityMeasure (rawLaw ψ)]
    (ε s : ℝ) (j : ℕ) : ObservationSample (N+1) (j+1) → Position → ℝ :=
  let P := observationLaw (j+1) (rawLaw ψ)
  let rs := fun k : Fin (j+1) => profileRadius ε N k.val
  fun o => conditionalPacketDensity P Prod.fst (tailObservation rs j) Coulomb.unitWindow 1
    (initialAtomicRadius ε ((N+1:ℕ):ℝ)) s (tailObservation rs j o)

end NeutralAtom
end

end

end OAI
end


