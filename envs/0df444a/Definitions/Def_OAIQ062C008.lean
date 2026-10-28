-- Prove2me | Definitions.Def_OAIQ062C008
-- name    : OAIQ062C008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T00:10:23.066344+00:00
-- url     : https://prove2.me/theorems/5c328cd9-013d-4fc3-8156-3db6336e2a3e
-- title:
--   Definitions bundle OAIQ062C008 of the split of OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NeutralAtom.generalized_outer_radii`, carved from OpenAI's openai/math development (OpenAI, *Generalized outer-electron radii of neutral Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 86 declarations of OpenAI's Lean: 19 definitions, 1 inductive type or structure and 66 theorems. The definitions and types are `OAI.Coulomb.atomicCountConstant`, `OAI.Coulomb.atomicFraction`, `OAI.Coulomb.atomicInnerFieldConstant`, `OAI.Coulomb.atomicKineticConstant`, `OAI.Coulomb.atomicNearConstant`, `OAI.Coulomb.atomicPatchMeanField`, `OAI.Coulomb.atomicPatchTFGap`, `OAI.Coulomb.atomicTailConstant`, `OAI.Coulomb.atomicTransferConstant`, `OAI.Coulomb.patchFieldTransferError`, `OAI.Coulomb.patchSliceTFGap`, `OAI.Coulomb.patchTFScreenedField`, `OAI.Coulomb.patchTransferRemainder`, `OAI.Coulomb.rotatedDensityPower`, `OAI.NeutralAtom.QuantumProfileDatum`, `OAI.NeutralAtom.fixedCoreMomentBound`, `OAI.NeutralAtom.observedDeficitCoefficient`, `OAI.NeutralAtom.physicalFieldCapBase`, `OAI.NeutralAtom.physicalFieldCapUnit`, `OAI.NeutralAtom.physicalSpatialCap`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CoulombRadii_FieldAnalysis_AtomicNear`, `CoulombRadii_FieldAnalysis_AtomicWeightGeometry`, `CoulombRadii_FieldAnalysis_CorePointMeasurable`, `CoulombRadii_FieldAnalysis_FlatDensityPower`, `CoulombRadii_FieldAnalysis_FreshTransferScale`, `CoulombRadii_FieldAnalysis_GridIndex`, `CoulombRadii_FieldAnalysis_GroupFermionicCoefficients`, `CoulombRadii_FieldAnalysis_OuterJoinConfiguration`, `CoulombRadii_FieldAnalysis_RawThomasFermiEnergy`, `CoulombRadii_FieldAnalysis_RetainedFineDensity`, `CoulombRadii_FieldAnalysis_RetainedFinePower`, `CoulombRadii_FieldAnalysis_RotatedDensityPower`, `CoulombRadii_FieldAnalysis_Rotation`, `CoulombRadii_FieldAnalysis_TailClosure`, `CoulombRadii_FormDomain_AtomicPhysicalKinetic`, `CoulombRadii_FormDomain_PhysicalEnsemble`, `CoulombRadii_FormDomain_TfGradientField`, `CoulombRadii_Localization_DeletedLabels`, `CoulombRadii_RandomFields_PhysicalDeficitTail`, `CoulombRadii_RandomFields_PosteriorSpatialCap`, `CoulombRadii_Screening_CoreMoment`, `CoulombRadii_Screening_CountScalar`, `CoulombRadii_Screening_FineCountTest`, `CoulombRadii_Screening_PatchComparison`, `CoulombRadii_Screening_PhysicalCapMoment`, `CoulombRadii_Screening_ScaledFieldCap`, `CoulombRadii_Screening_SharpThinScreening`, `CoulombRadii_Screening_UniformCountConsequences`, `CoulombRadii_Screening_UpperDeficit`, `CoulombRadii_ThomasFermi_AtomicRefinedGap`, `CoulombRadii_ThomasFermi_PatchGeometry`, `CoulombRadii_ThomasFermi_PatchNegativeCost`, `CoulombRadii_ThomasFermi_PhysicalCount`, `CoulombRadii_ThomasFermi_QuantumProfileDatum`, `CoulombRadii_ThomasFermi_TFCountTest`, `CoulombRadii_ThomasFermi_TFInterior`, `CoulombRadii_ThomasFermi_TFOscillation`, `CoulombRadii_ThomasFermi_TfExtendNonneg`, `CoulombRadii_ThomasFermi_TfFunctionalUniformBound`.
--
--   **Imports.** It imports the published bundle `Def_CoulombRadii`; the bundles `OAIQ062C006` and `OAIQ062C007` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.Coulomb.atomic_predecessor_from_physical_mean`, `OAI.Coulomb.exists_atomic_near_scale`, `OAI.NeutralAtom.arrayEvent_fresh_field_means`, `OAI.NeutralAtom.physical_propagation_good_events`, `OAI.NeutralAtom.physical_retained_master_fresh_transfer`, `OAI.NeutralAtom.physical_retained_spatial_cap`, `OAI.NeutralAtom.physical_tf_band` and `OAI.NeutralAtom.quantum_profile_packet_limit`; the proofs of `OAI.Coulomb.RecordedEnsemble.atomic_zero_offset_core_deletion`, `OAI.Coulomb.atom_global_sector_minimum`, `OAI.Coulomb.atomic_predecessor_from_physical_mean`, `OAI.Coulomb.exists_atomic_near_scale`, `OAI.NeutralAtom.arrayEvent_fresh_field_means`, `OAI.NeutralAtom.generalized_outer_radii`, `OAI.NeutralAtom.physical_neutral_energy_offset`, `OAI.NeutralAtom.physical_normalized_inverse_point`, `OAI.NeutralAtom.physical_observed_small_annular_count_tail`, `OAI.NeutralAtom.physical_propagation_good_events`, `OAI.NeutralAtom.physical_retained_master_fresh_transfer`, `OAI.NeutralAtom.physical_retained_spatial_cap`, `OAI.NeutralAtom.physical_tf_band` and `OAI.NeutralAtom.quantum_profile_packet_limit`.
-- source:
--   OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C006
import Definitions.Def_OAIQ062C007

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_GroupFermionicCoefficients
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
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

lemma grid_cube_kinetic_lower {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) {b : ℝ} (hb : 0 < b) (k : GridAssignment n) :
    ((b⁻¹)^2 * thomasFermiCoefficient * gridLeadingCount k -
      (b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n : ℝ)^(4/3 : ℝ)) *
      cubeMass (ψ.translate (gridShift b k)) b ≤
      cubeKinetic (ψ.translate (gridShift b k)) b := by
  let g := Set.rangeFactorization (gridCell k)
  let center : Set.range (gridCell k) → Space := fun u =>
    WithLp.toLp 2 (fun j => b*(u.val j : ℝ))
  have hm : 0 ≤ cubeMass (ψ.translate (gridShift b k)) b :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  exact (mul_le_mul_of_nonneg_right (groupNeumannLower_uniform g b) hm).trans
    (assigned_cube_kinetic_lower hn ψ hψ g center hb)

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

lemma grid_kinetic_lower {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) {b : ℝ} (hb : 0 < b) :
    (b⁻¹)^2 * thomasFermiCoefficient *
        (∑' k : GridAssignment n,
          gridLeadingCount k * cubeMass (ψ.translate (gridShift b k)) b) -
      ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n : ℝ)^(4/3 : ℝ)) * mass ψ ≤
      kinetic ψ := by
  have HM := grid_hasSum_mass ψ hb
  have HK := grid_hasSum_kinetic ψ hb
  have HL := (grid_leading_summable ψ hb).hasSum
  have HS := (HL.mul_left ((b⁻¹)^2 * thomasFermiCoefficient)).sub
    (HM.mul_left ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n : ℝ)^(4/3 : ℝ)))
  apply hasSum_le _ HS HK
  intro k
  have H := grid_cube_kinetic_lower hn ψ hψ hb k
  nlinarith

lemma grid_count_expectation_kinetic_lower {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) {b : ℝ} (hb : 0 < b) :
    (b⁻¹)^2 * thomasFermiCoefficient *
      (∑ s, ∫ x : (Fin n × Fin 3) → ℝ,
        gridLeadingCount (gridIndex b x) * ‖ψ.value s (WithLp.toLp 2 x)‖^2) -
      ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n : ℝ)^(4/3 : ℝ)) * mass ψ ≤
      kinetic ψ := by
  rw [← grid_leading_expectation ψ hb]
  exact grid_kinetic_lower hn ψ hψ hb

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FlatDensityPower
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

lemma shifted_grid_count_kinetic_lower {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) {b : ℝ} (hb : 0 < b) (t : Fin 3 → ℝ) :
    (b⁻¹)^2 * thomasFermiCoefficient *
      (∑ s, ∫ x : (Fin n × Fin 3) → ℝ,
        gridLeadingCount (gridIndex b (fun ij => x ij+t ij.2)) *
          ‖ψ.value s (WithLp.toLp 2 x)‖^2) -
      ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n : ℝ)^(4/3 : ℝ)) * mass ψ ≤
      kinetic ψ := by
  have H := grid_count_expectation_kinetic_lower hn
    (ψ.translate (commonShift (-t))) (hψ.translate_common (-t)) hb
  rw [mass_translate, kinetic_translate] at H
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  congr 1
  funext s
  have he := integral_add_right_eq_self (μ := volume) (fun x => gridLeadingCount (gridIndex b x) *
      ‖(ψ.translate (commonShift (-t))).value s (WithLp.toLp 2 x)‖^2)
    (fun ij => t ij.2)
  have hf (x : (Fin n × Fin 3) → ℝ) :
      (ψ.translate (commonShift (-t))).value s (WithLp.toLp 2 (x+(fun ij => t ij.2))) =
        ψ.value s (WithLp.toLp 2 x) := by
    change ψ.value s (_ + _) = _
    congr 1
    ext ij
    simp [commonShift]
  simp only [hf] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl

theorem flat_fine_density_kinetic_lower {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) {b : ℝ} (hb : 0 < b) :
    thomasFermiCoefficient *
      (∑ s, ∫ x : (Fin n × Fin 3) → ℝ,
        flatDensityPower b x * ‖ψ.value s (WithLp.toLp 2 x)‖^2) -
      ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n : ℝ)^(4/3 : ℝ)) * mass ψ ≤
      kinetic ψ := by
  let w (s : Spins n) (x : (Fin n × Fin 3) → ℝ) := ‖ψ.value s (WithLp.toLp 2 x)‖^2
  have hw (s : Spins n) : Integrable (w s) :=
    (((ψ.value_L2 s).comp_measurePreserving
      (PiLp.volume_preserving_toLp (Fin n × Fin 3))).integrable_norm_pow (p := 2) (by decide))
  have hw0 (s : Spins n) (x) : 0 ≤ w s x := sq_nonneg _
  let B (t : Fin 3 → ℝ) := ∑ s, ∫ x,
    gridLeadingCount (gridIndex b (fun ij => x ij+t ij.2)) * w s x
  have hBs (s : Spins n) : Integrable (fun t : Fin 3 → ℝ =>
      ∫ x, gridLeadingCount (gridIndex b (fun ij => x ij+t ij.2)) * w s x)
        (finiteCubeMeasure b (Fin 3)) :=
    (translated_count_integrable hb (hw s) (hw0 s)).integral_prod_left
  have hB : Integrable B (finiteCubeMeasure b (Fin 3)) :=
    integrable_finsetSum _ (fun s _ => hBs s)
  have hL : (∑ s, ∫ x, flatDensityPower b x * w s x) ≤
      (b⁻¹)^5 * ∫ t, B t ∂finiteCubeMeasure b (Fin 3) := by
    calc
      _ ≤ ∑ s, (b⁻¹)^5 * ∫ t, (∫ x,
          gridLeadingCount (gridIndex b (fun ij => x ij+t ij.2)) * w s x)
            ∂finiteCubeMeasure b (Fin 3) :=
        Finset.sum_le_sum (fun s _ => weighted_flatDensityPower_le hb (hw s) (hw0 s))
      _ = _ := by
        rw [← Finset.mul_sum]
        congr 1
        exact (integral_finsetSum _ (fun s _ => hBs s)).symm
  let e := ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n : ℝ)^(4/3 : ℝ)) * mass ψ
  have Hp (t : Fin 3 → ℝ) : (b⁻¹)^2 * thomasFermiCoefficient * B t - e ≤ kinetic ψ :=
    shifted_grid_count_kinetic_lower hn ψ hψ hb t
  have H := integral_mono ((hB.const_mul _).sub (integrable_const e))
    (integrable_const (kinetic ψ)) Hp
  change (∫ t, (b⁻¹)^2 * thomasFermiCoefficient * B t - e ∂finiteCubeMeasure b (Fin 3)) ≤
    ∫ t, kinetic ψ ∂finiteCubeMeasure b (Fin 3) at H
  rw [integral_sub (hB.const_mul _) (integrable_const e), integral_const_mul,
    integral_const, integral_const, finiteCubeMeasure_real_univ hb, Fintype.card_fin,
    smul_eq_mul] at H
  simp only [smul_eq_mul] at H
  have HS := mul_le_mul_of_nonneg_left H (show 0 ≤ (b⁻¹)^3 by positivity)
  have Hscaled : thomasFermiCoefficient * ((b⁻¹)^5 * ∫ t, B t ∂finiteCubeMeasure b (Fin 3)) - e ≤
      kinetic ψ := by
    have hs3 : (b⁻¹)^3 * b^3 = 1 := by field_simp [hb.ne']
    have hleft : (b⁻¹)^3 * ((b⁻¹)^2 * thomasFermiCoefficient *
        (∫ t, B t ∂finiteCubeMeasure b (Fin 3)) - b^3 * e) =
        thomasFermiCoefficient * ((b⁻¹)^5 * ∫ t, B t ∂finiteCubeMeasure b (Fin 3)) - e := by
      rw [mul_sub, ← mul_assoc _ (b^3) e, hs3, one_mul]
      congr 1
      ring
    rw [hleft, ← mul_assoc ((b⁻¹)^3) (b^3) (kinetic ψ), hs3, one_mul] at HS
    exact HS
  exact (sub_le_sub_right (mul_le_mul_of_nonneg_left hL thomasFermiCoefficient_pos.le) e).trans Hscaled

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_Rotation
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.instIsHaarMeasureSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure_1 _root_.OAI.Coulomb.instIsMulLeftInvariantSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure_1 _root_.OAI.Coulomb.instIsMulRightInvariantSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure_1 _root_.OAI.Coulomb.instIsProbabilityMeasureSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure_1 _root_.OAI.Coulomb.packetIndexCountable
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

lemma rotatedFlatDensityPower_eq {n : ℕ} (b : ℝ) (Q : Rotation) (x : Configuration n) :
    (∫ y, rotatedFlatDensity b Q (position x) y ^ (5/3:ℝ)) =
      flatDensityPower b (commonIsometry (rotationIsometry Q) x).ofLp := by
  let f : Space → ℝ := fun y => (∑ i : Fin n, flatFineKernel b
    (y.ofLp - (rotationIsometry Q (position x i)).ofLp)) ^ (5/3:ℝ)
  have hrot := (show MeasurePreserving (rotationIsometry Q).toHomeomorph.toMeasurableEquiv volume volume from
    (rotationIsometry Q).measurePreserving).integral_comp' f
  have hpi := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).integral_comp'
    (fun y : Fin 3 → ℝ => (∑ i : Fin n, flatFineKernel b
      (y - (rotationIsometry Q (position x i)).ofLp)) ^ (5/3:ℝ))
  calc
    _ = ∫ y, f (rotationIsometry Q y) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by
        dsimp only [f, rotatedFlatDensity]
        simp only [map_sub]
        rfl)
    _ = ∫ y, f y := hrot
    _ = _ := by
      convert hpi using 1 <;> rfl

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_RotatedDensityPower
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.instIsHaarMeasureSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure_1 _root_.OAI.Coulomb.instIsMulLeftInvariantSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure_1 _root_.OAI.Coulomb.instIsMulRightInvariantSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure_1 _root_.OAI.Coulomb.instIsProbabilityMeasureSubtypeMatrixFinOfNatNatRealMemSubmonoidRotationRotationMeasure_1 _root_.OAI.Coulomb.packetIndexCountable
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

lemma flat_fine_density_kinetic_lower_euclidean {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) {b : ℝ} (hb : 0 < b) :
    thomasFermiCoefficient *
      (∑ s, ∫ x : Configuration n, flatDensityPower b x.ofLp * ‖ψ.value s x‖^2) -
      ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n : ℝ)^(4/3 : ℝ)) * mass ψ ≤
      kinetic ψ := by
  have H := flat_fine_density_kinetic_lower hn ψ hψ hb
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  apply Finset.sum_congr rfl
  intro s _
  exact (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n × Fin 3)).integral_comp'
    (fun x => flatDensityPower b x * ‖ψ.value s (WithLp.toLp 2 x)‖^2)

lemma fixed_rotation_fine_density_kinetic_lower {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) {b : ℝ} (hb : 0 < b) (Q : Rotation) :
    thomasFermiCoefficient *
      (∑ s, ∫ x : Configuration n,
        (∫ y : Space, rotatedFlatDensity b Q (position x) y^(5/3:ℝ)) * ‖ψ.value s x‖^2) -
      ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n : ℝ)^(4/3 : ℝ)) * mass ψ ≤
      kinetic ψ := by
  let L := commonIsometry (n:=n) (rotationIsometry Q)
  have has : Antisymmetric (ψ.pullback L.symm) := by
    rw [show L.symm = commonIsometry (rotationIsometry Q).symm from commonIsometry_symm _]
    exact hψ.pullback_common _
  have H := flat_fine_density_kinetic_lower_euclidean hn (ψ.pullback L.symm) has hb
  rw [mass_pullback, kinetic_pullback] at H
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  apply Finset.sum_congr rfl
  intro s _
  have hp := (show MeasurePreserving L.toHomeomorph.toMeasurableEquiv volume volume from
    L.measurePreserving).integral_comp'
      (fun x : Configuration n => flatDensityPower b x.ofLp * ‖ψ.value s (L.symm x)‖^2)
  change (∫ x : Configuration n, flatDensityPower b (L x).ofLp * ‖ψ.value s (L.symm (L x))‖^2) = _ at hp
  simpa only [H1Vector.pullback, rotatedFlatDensityPower_eq, LinearIsometryEquiv.symm_apply_apply] using hp

noncomputable def rotatedDensityPower {n : ℕ} (b : ℝ) (Q : Rotation) (x : Configuration n) : ℝ :=
  ∫ y : Space, rotatedFlatDensity b Q (position x) y^(5/3:ℝ)

lemma rotatedDensityPower_nonneg {n : ℕ} (b : ℝ) (Q : Rotation) (x : Configuration n) :
    0 ≤ rotatedDensityPower b Q x :=
  integral_nonneg (fun _ => Real.rpow_nonneg (rotatedFlatDensity_nonneg ..) _)
lemma rotatedDensityPower_le {n : ℕ} {b : ℝ} (hb : 0 < b) (Q : Rotation) (x : Configuration n) :
    rotatedDensityPower b Q x ≤ ((n:ℝ)*(b⁻¹)^3)^(2/3:ℝ)*n :=
  rotatedFlatDensity_power_integral_le hb ..

lemma rotatedDensityPower_measurable {n : ℕ} (b : ℝ) :
    Measurable (fun p : Rotation × Configuration n => rotatedDensityPower b p.1 p.2) := by
  simp_rw [rotatedDensityPower, rotatedFlatDensityPower_eq]
  exact (flatDensityPower_measurable b).comp
    ((PiLp.continuous_ofLp 2 _).measurable.comp rotation_configuration_continuous.measurable)

lemma fineDensityPower_configuration_measurable {n : ℕ} (b : ℝ) :
    Measurable (fun x : Configuration n => fineDensityPower b (position x)) := by
  have hm : Measurable (fun p : Configuration n × Space =>
      fineDensity b (position p.1) p.2^(5/3:ℝ)) := by
    apply Measurable.pow_const
    apply Finset.measurable_sum
    intro i _
    exact (fineKernel_measurable b).comp
      (measurable_snd.sub ((continuous_position i).measurable.comp measurable_fst))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma fineDensityPower_nonneg {n : ℕ} (b : ℝ) (x : Fin n → Space) :
    0 ≤ fineDensityPower b x :=
  integral_nonneg (fun _ => Real.rpow_nonneg (fineDensity_nonneg ..) _)

lemma weighted_rotatedDensityPower_integrable_prod {n : ℕ} {b : ℝ} (hb : 0 < b)
    {w : Configuration n → ℝ} (hw : Integrable w) (hw0 : ∀ x, 0 ≤ w x) :
    Integrable (fun p : Rotation × Configuration n => rotatedDensityPower b p.1 p.2 * w p.2)
      (rotationMeasure.prod volume) := by
  apply ((hw.const_mul (((n:ℝ)*(b⁻¹)^3)^(2/3:ℝ)*n)).comp_snd rotationMeasure).mono'
    ((rotatedDensityPower_measurable b).aestronglyMeasurable.mul (hw.comp_snd rotationMeasure).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun p => by
    change ‖rotatedDensityPower b p.1 p.2 * w p.2‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (rotatedDensityPower_nonneg ..) (hw0 _))]
    exact mul_le_mul_of_nonneg_right (rotatedDensityPower_le hb ..) (hw0 _))

lemma weighted_fineDensityPower_integrable {n : ℕ} {b : ℝ} (hb : 0 < b)
    {w : Configuration n → ℝ} (hw : Integrable w) (hw0 : ∀ x, 0 ≤ w x) :
    Integrable (fun x => fineDensityPower b (position x) * w x) := by
  apply (hw.const_mul (((n:ℝ)*(b⁻¹)^3)^(2/3:ℝ)*n)).mono'
    ((fineDensityPower_configuration_measurable b).aestronglyMeasurable.mul hw.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun x => by
    change ‖fineDensityPower b (position x) * w x‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (fineDensityPower_nonneg ..) (hw0 _))]
    exact mul_le_mul_of_nonneg_right (fineDensityPower_bound hb ..) (hw0 _))

lemma weighted_fineDensityPower_le_angular {n : ℕ} {b : ℝ} (hb : 0 < b)
    {w : Configuration n → ℝ} (hw : Integrable w) (hw0 : ∀ x, 0 ≤ w x) :
    (∫ x, fineDensityPower b (position x) * w x) ≤
      ∫ Q, (∫ x, rotatedDensityPower b Q x * w x) ∂rotationMeasure := by
  have hi := weighted_rotatedDensityPower_integrable_prod hb hw hw0
  calc
    _ ≤ ∫ x, (∫ Q, rotatedDensityPower b Q x * w x ∂rotationMeasure) := by
      apply integral_mono (weighted_fineDensityPower_integrable hb hw hw0) hi.integral_prod_right
      intro x
      change fineDensityPower b (position x) * w x ≤ ∫ Q, rotatedDensityPower b Q x * w x ∂rotationMeasure
      rw [integral_mul_const]
      exact mul_le_mul_of_nonneg_right (fineDensityPower_le_angularAverage hb (position x)) (hw0 _)
    _ = _ := (integral_integral_swap hi).symm

theorem fine_density_kinetic_lower {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) {b : ℝ} (hb : 0 < b) :
    thomasFermiCoefficient *
      (∑ s, ∫ x : Configuration n, fineDensityPower b (position x) * ‖ψ.value s x‖^2) -
      ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n : ℝ)^(4/3 : ℝ)) * mass ψ ≤
      kinetic ψ := by
  let w (s : Spins n) (x : Configuration n) := ‖ψ.value s x‖^2
  have hw (s : Spins n) : Integrable (w s) :=
    (ψ.value_L2 s).integrable_norm_pow (p:=2) (by decide)
  have hw0 (s : Spins n) (x) : 0 ≤ w s x := sq_nonneg _
  let A (Q : Rotation) := ∑ s, ∫ x, rotatedDensityPower b Q x * w s x
  have hAs (s : Spins n) : Integrable (fun Q => ∫ x, rotatedDensityPower b Q x * w s x) rotationMeasure :=
    (weighted_rotatedDensityPower_integrable_prod hb (hw s) (hw0 s)).integral_prod_left
  have hA : Integrable A rotationMeasure := integrable_finsetSum _ (fun s _ => hAs s)
  have hJ : (∑ s, ∫ x, fineDensityPower b (position x) * w s x) ≤ ∫ Q, A Q ∂rotationMeasure := by
    rw [show (∫ Q, A Q ∂rotationMeasure) = ∑ s, ∫ Q, (∫ x, rotatedDensityPower b Q x * w s x) ∂rotationMeasure from
      integral_finsetSum _ (fun s _ => hAs s)]
    exact Finset.sum_le_sum (fun s _ => weighted_fineDensityPower_le_angular hb (hw s) (hw0 s))
  have hpoint (Q : Rotation) : thomasFermiCoefficient * A Q ≤ kinetic ψ +
      ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n : ℝ)^(4/3 : ℝ)) * mass ψ := by
    have H := fixed_rotation_fine_density_kinetic_lower hn ψ hψ hb Q
    exact sub_le_iff_le_add.mp H
  have hI := integral_mono (hA.const_mul thomasFermiCoefficient)
    (integrable_const (kinetic ψ + ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n : ℝ)^(4/3 : ℝ)) * mass ψ)) hpoint
  rw [integral_const_mul] at hI
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hI
  have hc : 0 ≤ thomasFermiCoefficient := by
    unfold thomasFermiCoefficient
    positivity
  exact sub_le_iff_le_add.mpr ((mul_le_mul_of_nonneg_left hJ hc).trans hI)

end Coulomb

open MeasureTheory Set
open scoped BigOperators Matrix ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_RetainedFineDensity
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
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
namespace Coulomb

lemma retainedFineDensity_power_weight_integrable {n : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Configuration n → Finset (Fin n)) (hr : ∀ i, MeasurableSet {x | i ∈ r x})
    {w : Configuration n → ℝ} (hw : Integrable w) (hw0 : ∀ x, 0 ≤ w x) :
    Integrable (fun x => (∫ y, retainedFineDensity b (r x) (position x) y^(5/3:ℝ))*w x) := by
  apply (weighted_fineDensityPower_integrable hb hw hw0).mono'
  · exact (retainedFineDensity_power_configuration_measurable b r hr).aestronglyMeasurable.mul
      hw.aestronglyMeasurable
  · exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (mul_nonneg (integral_nonneg (fun y =>
        Real.rpow_nonneg (retainedFineDensity_nonneg ..) _)) (hw0 x))]
      exact mul_le_mul_of_nonneg_right (retainedFineDensity_power_le hb (r x) (position x)) (hw0 x)

theorem retained_fine_kinetic_lower {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) {b : ℝ} (hb : 0 < b)
    (r : Configuration n → Finset (Fin n)) (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    thomasFermiCoefficient * (∑ s, ∫ x : Configuration n,
      (∫ y, retainedFineDensity b (r x) (position x) y^(5/3:ℝ))*‖ψ.value s x‖^2) -
      ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n:ℝ)^(4/3:ℝ)) * mass ψ ≤ kinetic ψ := by
  apply le_trans _ (fine_density_kinetic_lower hn ψ hψ hb)
  apply sub_le_sub_right
  apply mul_le_mul_of_nonneg_left _ (by unfold thomasFermiCoefficient; positivity)
  apply Finset.sum_le_sum
  intro s hs
  have hw : Integrable (fun x => ‖ψ.value s x‖^2) :=
    (ψ.value_L2 s).integrable_norm_pow (p:=2) (by decide)
  exact integral_mono (retainedFineDensity_power_weight_integrable hb r hr hw (fun _ => sq_nonneg _))
    (weighted_fineDensityPower_integrable hb hw (fun _ => sq_nonneg _))
    (fun x => mul_le_mul_of_nonneg_right (retainedFineDensity_power_le hb _ _) (sq_nonneg _))
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_RetainedFinePower
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
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
namespace Coulomb

lemma retained_fine_kinetic_lower_all {n : ℕ} (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) {b : ℝ} (hb : 0 < b)
    (r : Configuration n → Finset (Fin n)) (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    thomasFermiCoefficient * potentialForm (retainedFinePower b r) ψ -
      ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n:ℝ)^(4/3:ℝ)) * mass ψ ≤ kinetic ψ := by
  by_cases hn : 0 < n
  · exact retained_fine_kinetic_lower hn ψ hψ hb r hr
  · have hn : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have hr0 (x : Configuration 0) : r x = ∅ := Finset.eq_empty_of_forall_notMem (fun i => Fin.elim0 i)
    simpa [potentialForm, retainedFinePower, retainedFineDensity, hr0,
      Real.zero_rpow (by norm_num : (5/3:ℝ) ≠ 0), Real.zero_rpow (by norm_num : (4/3:ℝ) ≠ 0)]
      using (show 0 ≤ kinetic ψ from by unfold kinetic; positivity)

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

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

theorem outer_block_retained_fine_kinetic_lower {m k : ℕ} (ψ : H1Vector (k+m))
    (hψ : ∀ (s : Spins m) (p : Equiv.Perm (Fin k)) (t : Spins k),
      ∀ᵐ z ∂volume, ψ.value (outerAppend s t ∘ outerPerm m p) (permute (outerPerm m p) z) =
        (((outerPerm m p).sign : ℤ) : ℂ) * ψ.value (outerAppend s t) z)
    {b : ℝ} (hb : 0 < b) (r : Configuration k → Finset (Fin k))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    thomasFermiCoefficient * potentialForm
      (fun z => retainedFinePower b r ((outerJoinConfiguration m k).symm z).2) ψ -
      ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (k:ℝ)^(4/3:ℝ)) * mass ψ ≤ outerKinetic (m:=k) (k:=m) ψ := by
  let C := (b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (k:ℝ)^(4/3:ℝ)
  have hs (s : Spins m) :
      thomasFermiCoefficient * (∫ x, potentialForm (retainedFinePower b r) (ψ.outerSlice s x)) -
        C * (∫ x, mass (ψ.outerSlice s x)) ≤ ∫ x, kinetic (ψ.outerSlice s x) := by
    rw [←integral_const_mul, ←integral_const_mul,
      ←integral_sub ((potentialForm_outerSlice_integrable ψ s _ (fun t => outer_finePower_integrable hb r hr ψ (outerAppend s t))).const_mul _)
        ((mass_outerSlice_integrable ψ s).const_mul C)]
    apply integral_mono_ae
      (((potentialForm_outerSlice_integrable ψ s _ (fun t => outer_finePower_integrable hb r hr ψ (outerAppend s t))).const_mul _).sub
        ((mass_outerSlice_integrable ψ s).const_mul C)) (kinetic_outerSlice_integrable ψ s)
    exact (ψ.outerSlice_antisymmetric s (hψ s)).mono fun x hx =>
      retained_fine_kinetic_lower_all (ψ.outerSlice s x) hx hb r hr
  have H := Finset.sum_le_sum (s:=Finset.univ) (fun s _ => hs s)
  simp only [Finset.sum_sub_distrib, ←Finset.mul_sum] at H
  rw [integral_potentialForm_outerSlice ψ _ (outer_finePower_integrable hb r hr ψ),
    integral_mass_outerSlice, integral_kinetic_outerSlice] at H
  exact H

theorem outer_block_retained_fine_pair_lower {m k : ℕ} (ψ : H1Vector (k+m))
    {b : ℝ} (hb : 0 < b) (r : Configuration k → Finset (Fin k))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    potentialForm (fun z => retainedFineCoulomb b r ((outerJoinConfiguration m k).symm z).2) ψ -
      (((2*Real.pi+1)/(2*b))*k)*mass ψ ≤
    potentialForm (fun z => pairPotential ((outerJoinConfiguration m k).symm z).2) ψ :=
  sub_le_iff_le_add.mpr (potentialForm_le_add_const ψ (outer_fineCoulomb_integrable hb r hr ψ)
    ψ.outer_pair_integrable (ae_outer_fine_pair_bound hb r))

theorem outer_block_retained_fine_energy_lower {m k : ℕ} (ψ : H1Vector (k+m))
    (hψ : ∀ (s : Spins m) (p : Equiv.Perm (Fin k)) (t : Spins k),
      ∀ᵐ z ∂volume, ψ.value (outerAppend s t ∘ outerPerm m p) (permute (outerPerm m p) z) =
        (((outerPerm m p).sign : ℤ) : ℂ) * ψ.value (outerAppend s t) z)
    {b : ℝ} (hb : 0 < b) (r : Configuration k → Finset (Fin k))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    thomasFermiCoefficient * potentialForm
      (fun z => retainedFinePower b r ((outerJoinConfiguration m k).symm z).2) ψ +
    potentialForm (fun z => retainedFineCoulomb b r ((outerJoinConfiguration m k).symm z).2) ψ -
      (((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (k:ℝ)^(4/3:ℝ)) +
        ((2*Real.pi+1)/(2*b))*k)*mass ψ ≤
      outerKinetic (m:=k) (k:=m) ψ + potentialForm (fun z => pairPotential ((outerJoinConfiguration m k).symm z).2) ψ := by
  have h1 := outer_block_retained_fine_kinetic_lower ψ hψ hb r hr
  have h2 := outer_block_retained_fine_pair_lower ψ hb r hr
  linarith
end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_DeletedLabels
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
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma outerPair_weight_integrable {m k : ℕ} (ψ : H1Vector (m+k)) (s : Spins m) :
    Integrable (fun x => mass (ψ.coreSlice s x)*pairPotential x) :=
  slice_weight_integrable_const ψ pairPotential ψ.outer_pair_integrable s

lemma fine_energy_expectation_lower {m k : ℕ} (ψ : H1Vector (m+k))
    (hψ : ∀ (s : Spins k) (p : Equiv.Perm (Fin m)) (t : Spins m),
      ∀ᵐ z, ψ.value (outerAppend s t ∘ outerPerm k p) (permute (outerPerm k p) z) =
        (((outerPerm k p).sign : ℤ) : ℂ)*ψ.value (outerAppend s t) z)
    {b : ℝ} (hb : 0 < b) (r : Configuration m → Finset (Fin m))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x}) :
    sliceExpectation ψ (fun _ x => thomasFermiCoefficient*retainedFinePower b r x + retainedFineCoulomb b r x) -
      fineLocalizationError m b*mass ψ ≤ outerKinetic ψ + sliceExpectation ψ (fun _ x => pairPotential x) := by
  rw [sliceExpectation_add ψ _ _
      (fun s => by simpa only [mul_left_comm (mass _) thomasFermiCoefficient] using
        (retainedFinePower_weight_integrable ψ hb r hr s).const_mul thomasFermiCoefficient)
      (retainedFineCoulomb_weight_integrable ψ hb r hr), sliceExpectation_const_mul]
  rw [sliceExpectation_const ψ _ (by simpa only [outerJoinConfiguration_symm_snd] using outer_finePower_integrable hb r hr ψ),
    sliceExpectation_const ψ _ (by simpa only [outerJoinConfiguration_symm_snd] using outer_fineCoulomb_integrable hb r hr ψ),
    sliceExpectation_const ψ _ ψ.outer_pair_integrable]
  simpa only [outerJoinConfiguration_symm_snd, fineLocalizationError] using
    outer_block_retained_fine_energy_lower ψ hψ hb r hr

theorem conditional_fine_lower {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k))
    (hψ : ∀ (s : Spins k) (p : Equiv.Perm (Fin m)) (t : Spins m),
      ∀ᵐ z, ψ.value (outerAppend s t ∘ outerPerm k p) (permute (outerPerm k p) z) =
        (((outerPerm k p).sign : ℤ) : ℂ)*ψ.value (outerAppend s t) z)
    {b : ℝ} (hb : 0 < b) (r : Configuration m → Finset (Fin m))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x})
    (F : Spins m → Configuration m → ℝ)
    (hFi : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*(F s x*(deletedLabels r x).card)))
    (hcap : ∀ s, ∀ᵐ x, ∀ i ∈ deletedLabels r x,
      coreScreenedField S (ψ.coreSlice s x).normalized (position x i) ≤ F s x) :
    sliceExpectation ψ (fun s x => form S (ψ.coreSlice s x).normalized + discreteFineTF S ψ b r s x) -
      sliceExpectation ψ (fun s x => F s x*(deletedLabels r x).card) - fineLocalizationError m b*mass ψ ≤ form S ψ := by
  let P := fun s x => ∑ i ∈ r x, coreScreenedField S (ψ.coreSlice s x).normalized (position x i)
  let D := fun s x => ∑ i ∈ deletedLabels r x, coreScreenedField S (ψ.coreSlice s x).normalized (position x i)
  let A := fun (_ : Spins m) x => thomasFermiCoefficient*retainedFinePower b r x + retainedFineCoulomb b r x
  let e := fun s x => form S (ψ.coreSlice s x).normalized
  have hPi := retained_field_weight_integrable S ψ r hr
  have hDi := retained_field_weight_integrable S ψ (deletedLabels r) (deletedLabels_measurable r hr)
  have hAi (s : Spins m) : Integrable (fun x => mass (ψ.coreSlice s x)*A s x) := by
    dsimp only [A]; simp only [mul_add, mul_left_comm (mass _) thomasFermiCoefficient]
    exact ((retainedFinePower_weight_integrable ψ hb r hr s).const_mul _).add
      (retainedFineCoulomb_weight_integrable ψ hb r hr s)
  have hei := normalized_coreForm_weight_integrable S ψ
  have heq (s : Spins m) (x : Configuration m) : conditionalEnergy S ψ s x =
      (e s x-P s x)+pairPotential x-D s x := by
    rw [conditionalEnergy_eq_screened, ←retained_deleted_sum r x]
    dsimp only [e, P, D]; ring
  have hE : form S ψ = outerKinetic ψ +
      (sliceExpectation ψ e-sliceExpectation ψ P)+sliceExpectation ψ (fun _ x => pairPotential x)-sliceExpectation ψ D := by
    rw [conditional_energy_identity]
    change outerKinetic ψ + sliceExpectation ψ (conditionalEnergy S ψ) = _
    conv_lhs => rw [show conditionalEnergy S ψ = (fun s x => (e s x-P s x)+pairPotential x-D s x) by funext s x; exact heq s x]
    rw [sliceExpectation_sub ψ _ _
        (fun s => by
          apply ((hei s |>.sub (hPi s)).add (outerPair_weight_integrable ψ s)).congr
          exact Eventually.of_forall (fun x => by dsimp [e,P]; ring)) hDi,
      sliceExpectation_add ψ _ _ (fun s => by
        apply ((hei s).sub (hPi s)).congr
        exact Eventually.of_forall (fun x => by dsimp [e,P]; ring))
        (outerPair_weight_integrable ψ), sliceExpectation_sub ψ e P hei hPi]
    ring
  have hD : sliceExpectation ψ D ≤ sliceExpectation ψ (fun s x => F s x*(deletedLabels r x).card) := by
    apply sliceExpectation_mono_ae ψ _ _ hDi hFi
    intro s
    filter_upwards [hcap s] with x hx
    calc D s x ≤ ∑ i ∈ deletedLabels r x, F s x := Finset.sum_le_sum hx
      _ = F s x*(deletedLabels r x).card := by simp; ring
  have hL := fine_energy_expectation_lower ψ hψ hb r hr
  have hT : sliceExpectation ψ (fun s x => form S (ψ.coreSlice s x).normalized + discreteFineTF S ψ b r s x) =
      sliceExpectation ψ e + (sliceExpectation ψ A-sliceExpectation ψ P) := by
    change sliceExpectation ψ (fun s x => e s x+(A s x-P s x)) = _
    rw [sliceExpectation_add ψ e _ hei (fun s => by
        apply ((hAi s).sub (hPi s)).congr
        exact Eventually.of_forall (fun x => by dsimp [A,P]; ring)),
      sliceExpectation_sub ψ A P hAi hPi]
  rw [hT, hE]
  change sliceExpectation ψ A -fineLocalizationError m b*mass ψ ≤ _ at hL
  linarith
end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_RawThomasFermiEnergy
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
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
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

theorem conditional_source_free_lower {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k))
    (hψ : ∀ (s : Spins k) (p : Equiv.Perm (Fin m)) (t : Spins m),
      ∀ᵐ z, ψ.value (outerAppend s t ∘ outerPerm k p) (permute (outerPerm k p) z) =
        (((outerPerm k p).sign : ℤ) : ℂ)*ψ.value (outerAppend s t) z)
    {b : ℝ} (hb : 0 < b) (r : Configuration m → Finset (Fin m))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x})
    (F : Spins m → Configuration m → ℝ)
    (hFi : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*(F s x*(deletedLabels r x).card)))
    (hcap : ∀ s, ∀ᵐ x, ∀ i ∈ deletedLabels r x,
      coreScreenedField S (ψ.coreSlice s x).normalized (position x i) ≤ F s x)
    (A : Spins m → Configuration m → Set Space)
    (hsupport : ∀ s, ∀ᵐ x, SpatiallySupported (ψ.coreSlice s x).normalized (A s x))
    (hnuc : ∀ s : Spins m, ∀ᵐ x, ∀ j i, i ∈ r x → Real.sqrt 3*b ≤ ‖S.position j-position x i‖)
    (hcore : ∀ s, ∀ᵐ x, ∀ z ∈ A s x, ∀ i ∈ r x, Real.sqrt 3*b ≤ ‖z-position x i‖) :
    sliceExpectation ψ (fun s x => form S (ψ.coreSlice s x).normalized +
      rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized)
        (retainedFineDensity b (r x) (position x))) -
      sliceExpectation ψ (fun s x => F s x*(deletedLabels r x).card) - fineLocalizationError m b*mass ψ ≤ form S ψ := by
  have he : sliceExpectation ψ (fun s x => form S (ψ.coreSlice s x).normalized + discreteFineTF S ψ b r s x) =
      sliceExpectation ψ (fun s x => form S (ψ.coreSlice s x).normalized +
        rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized)
          (retainedFineDensity b (r x) (position x))) := by
    apply sliceExpectation_congr_ae
    intro s
    filter_upwards [hsupport s, hnuc s, hcore s] with x hs hn hc
    rw [discreteFineTF_eq_raw S ψ hb r s x hs hn hc]
  rw [←he]
  exact conditional_fine_lower S ψ hψ hb r hr F hFi hcap

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

lemma source_free_trial_from_density {M k : ℕ} (S : Nuclei M) (u : H1Vector k)
    (hu : Antisymmetric u) (hmu : mass u = 1)
    (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hgc : HasCompactSupport (g : Space → ℝ))
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖))
    {R : ℝ} (hR : 0 < R) (hgs : ∀ y, R < ‖y‖ → g y = 0)
    (ρ : Space → ℝ) (K A : Set Space) (hρ : SourceFreeHoleDensity S u g R ρ K A) :
    unrestrictedFormBottom S ≤ ((form S u+rawThomasFermiEnergy (coreScreenedField S u) ρ+
      packetKineticError g ρ : ℝ) : EReal) := by
  rcases hρ with ⟨hp,hm,ht,hK,hA,hs,hsu,hsep,hcore,hnuc⟩
  exact source_free_trial_raw S u hu hmu g hg hgc hrad hR hgs ρ hp hm ht K A hK hA hs hsu hsep hcore hnuc

theorem conditional_source_free_upper {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k))
    (hcoreAnti : ∀ s, ∀ᵐ x, Antisymmetric (ψ.coreSlice s x))
    (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hgc : HasCompactSupport (g : Space → ℝ))
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖))
    {R : ℝ} (hR : 0 < R) (hgs : ∀ y, R < ‖y‖ → g y = 0)
    (ρ : Spins m → Configuration m → Space → ℝ)
    (K A : Spins m → Configuration m → Set Space)
    (hρ : ∀ s, ∀ᵐ x, SourceFreeHoleDensity S (ψ.coreSlice s x).normalized g R (ρ s x) (K s x) (A s x))
    (hTi : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*
      rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized) (ρ s x)))
    (hKi : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*packetKineticError g (ρ s x)))
    {E : ℝ} (hE : (E : EReal) ≤ unrestrictedFormBottom S) :
    E*mass ψ ≤ sliceExpectation ψ (fun s x => form S (ψ.coreSlice s x).normalized+
      rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized) (ρ s x)) +
      sliceExpectation ψ (fun s x => packetKineticError g (ρ s x)) := by
  have hCi := normalized_coreForm_weight_integrable S ψ
  have hCT (s : Spins m) : Integrable (fun x => mass (ψ.coreSlice s x)*(form S (ψ.coreSlice s x).normalized+
      rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized) (ρ s x))) := by
    apply ((hCi s).add (hTi s)).congr
    exact Eventually.of_forall (fun x => (mul_add ..).symm)
  rw [←sliceExpectation_add ψ _ _ hCT hKi]
  rw [←sliceExpectation_number ψ E]
  apply Finset.sum_le_sum
  intro s _
  apply integral_mono_ae
    (by simpa only [mul_comm (mass _) E] using (mass_coreSlice_integrable ψ s).const_mul E)
    (by
      apply ((hCT s).add (hKi s)).congr
      exact Eventually.of_forall (fun x => (mul_add ..).symm))
  filter_upwards [hcoreAnti s, hρ s] with x hx hρx
  by_cases hz : mass (ψ.coreSlice s x)=0
  · simp [hz]
  · have hp : 0 < mass (ψ.coreSlice s x) := lt_of_le_of_ne (mass_nonneg _) (Ne.symm hz)
    have H := source_free_trial_from_density S (ψ.coreSlice s x).normalized hx.normalized
      (mass_normalized _ hp) g hg hgc hrad hR hgs (ρ s x) (K s x) (A s x) hρx
    have HE : E ≤ form S (ψ.coreSlice s x).normalized +
        rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized) (ρ s x)+packetKineticError g (ρ s x) :=
      EReal.coe_le_coe_iff.mp (hE.trans H)
    exact mul_le_mul_of_nonneg_left HE hp.le

theorem source_free_patch_comparison {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k))
    (houterAnti : ∀ (s : Spins k) (p : Equiv.Perm (Fin m)) (t : Spins m),
      ∀ᵐ z, ψ.value (outerAppend s t ∘ outerPerm k p) (permute (outerPerm k p) z) =
        (((outerPerm k p).sign : ℤ) : ℂ)*ψ.value (outerAppend s t) z)
    (hcoreAnti : ∀ s, ∀ᵐ x, Antisymmetric (ψ.coreSlice s x))
    {b : ℝ} (hb : 0 < b) (r : Configuration m → Finset (Fin m))
    (hr : ∀ i, MeasurableSet {x | i ∈ r x})
    (F : Spins m → Configuration m → ℝ)
    (hFi : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*(F s x*(deletedLabels r x).card)))
    (hcap : ∀ s, ∀ᵐ x, ∀ i ∈ deletedLabels r x,
      coreScreenedField S (ψ.coreSlice s x).normalized (position x i) ≤ F s x)
    (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hgc : HasCompactSupport (g : Space → ℝ))
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖))
    {R : ℝ} (hR : 0 < R) (hgs : ∀ y, R < ‖y‖ → g y = 0)
    (ρ : Spins m → Configuration m → Space → ℝ)
    (K A : Spins m → Configuration m → Set Space)
    (hρ : ∀ s, ∀ᵐ x, SourceFreeHoleDensity S (ψ.coreSlice s x).normalized g R (ρ s x) (K s x) (A s x))
    (hnuc : ∀ s : Spins m, ∀ᵐ x, ∀ j i, i ∈ r x → Real.sqrt 3*b ≤ ‖S.position j-position x i‖)
    (hcore : ∀ s, ∀ᵐ x, ∀ z ∈ A s x, ∀ i ∈ r x, Real.sqrt 3*b ≤ ‖z-position x i‖)
    (hTi : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*
      rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized) (ρ s x)))
    (hKi : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*packetKineticError g (ρ s x)))
    {E : ℝ} (hE : (E : EReal) ≤ unrestrictedFormBottom S) :
    sliceExpectation ψ (fun s x =>
      rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized) (retainedFineDensity b (r x) (position x)) -
      rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized) (ρ s x)) ≤
      form S ψ-E*mass ψ + sliceExpectation ψ (fun s x => packetKineticError g (ρ s x)) +
      sliceExpectation ψ (fun s x => F s x*(deletedLabels r x).card) +fineLocalizationError m b*mass ψ := by
  have hs : ∀ s, ∀ᵐ x, SpatiallySupported (ψ.coreSlice s x).normalized (A s x) := by
    intro s; exact (hρ s).mono fun x h => h.2.2.2.2.2.2.1
  have hσeq (s : Spins m) : discreteFineTF S ψ b r s =ᵐ[volume]
      (fun x => rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized)
        (retainedFineDensity b (r x) (position x))) := by
    filter_upwards [hs s, hnuc s, hcore s] with x hx hy hz
    exact discreteFineTF_eq_raw S ψ hb r s x hx hy hz
  have hσi (s : Spins m) : Integrable (fun x => mass (ψ.coreSlice s x)*
      rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized) (retainedFineDensity b (r x) (position x))) := by
    apply (discreteFineTF_weight_integrable S ψ hb r hr s).congr
    exact (hσeq s).mono fun x hx => congrArg (mass (ψ.coreSlice s x)*·) hx
  have HL := conditional_source_free_lower S ψ houterAnti hb r hr F hFi hcap A hs hnuc hcore
  have HU := conditional_source_free_upper S ψ hcoreAnti g hg hgc hrad hR hgs ρ K A hρ hTi hKi hE
  rw [sliceExpectation_add ψ _ _ (normalized_coreForm_weight_integrable S ψ) hσi] at HL
  rw [sliceExpectation_add ψ _ _ (normalized_coreForm_weight_integrable S ψ) hTi] at HU
  rw [sliceExpectation_sub ψ _ _ hσi hTi]
  linarith
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_TfGradientField
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
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
namespace Coulomb
variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]
lemma tfGradientField_coe (c : ℝ) (W : TFLq (volume.restrict Ω))
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    tfGradientField hΩ c W f =ᵐ[volume.restrict Ω]
      (fun x => c*(5/3:ℝ)*(f x)^(2/3:ℝ)-W x+tfPotential f x) := by
  filter_upwards [Lp.coeFn_add ((c*(5/3:ℝ)) • tfKineticField f-W) (tfPotentialField hΩ f),
    Lp.coeFn_sub ((c*(5/3:ℝ)) • tfKineticField f) W,
    Lp.coeFn_smul (c*(5/3:ℝ)) (tfKineticField f),tfKineticField_coe f,
    tfPotentialField_coe hΩ f,hf] with x ha hs hm hk hp hx
  simp only [tfGradientField,ha,Pi.add_apply,hs,Pi.sub_apply,hm,Pi.smul_apply,
    smul_eq_mul,hk,Real.norm_of_nonneg hx,hp]
lemma tfGradientField_pair (c : ℝ) (W : TFLq (volume.restrict Ω))
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) (h : TFLp (volume.restrict Ω)) :
    tfFieldContinuous (tfGradientField hΩ c W f) h =
      c*(5/3:ℝ)*(∫ x in Ω, (f x)^(2/3:ℝ)*h x) - tfFieldContinuous W h+tfCoulomb Ω h f := by
  unfold tfGradientField
  simp only [map_add,map_sub,map_smul,_root_.add_apply,_root_.sub_apply,_root_.smul_apply,smul_eq_mul]
  rw [tfKineticField_pair hf,tfCoulomb_eq_field hΩ h f]
lemma tfGradientField_nonneg (c : ℝ) (W : TFLq (volume.restrict Ω))
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (hm : ∀ g, TFNonneg g → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W g) :
    ∀ᵐ x ∂volume.restrict Ω, 0 ≤ tfGradientField hΩ c W f x := by
  apply tfDual_nonneg
  intro h hh hb
  rw [tfGradientField_pair hΩ c W hf]
  have H := tfFunctional_tangent_nonneg c (tfFieldContinuous W) (tfCoulombContinuous hΩ) hf hm hh hb
  change 0 ≤ c*(5/3:ℝ)*(∫ x in Ω, (f x)^(2/3:ℝ)*h x) - tfFieldContinuous W h +
    (tfCoulomb Ω f h+tfCoulomb Ω h f)/2 at H
  rw [tfCoulomb_symm f h] at H
  linarith
lemma tfGradientField_self (c : ℝ) (W : TFLq (volume.restrict Ω))
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (hm : ∀ g, TFNonneg g → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W g) :
    tfFieldContinuous (tfGradientField hΩ c W f) f = 0 := by
  rw [tfGradientField_pair hΩ c W hf,←tfKineticField_pair hf f,tfKineticField_self hf]
  exact tfFunctional_scaling_stationary c (tfFieldContinuous W) (tfCoulombContinuous hΩ) hf hm
lemma tfGradientField_complementarity (c : ℝ) (W : TFLq (volume.restrict Ω))
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (hm : ∀ g, TFNonneg g → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W g) :
    ∀ᵐ x ∂volume.restrict Ω, tfGradientField hΩ c W f x*f x = 0 := by
  have hn : 0 ≤ᵐ[volume.restrict Ω] (fun x => tfGradientField hΩ c W f x*f x) := by
    filter_upwards [tfGradientField_nonneg hΩ c W hf hm,hf] with x hx hy
    exact mul_nonneg hx hy
  apply (integral_eq_zero_iff_of_nonneg_ae hn (tfFieldPairing_integrable _ _)).mp
  exact tfGradientField_self hΩ c W hf hm
lemma tfEuler_complementarity (c : ℝ) (W : TFLq (volume.restrict Ω))
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (hm : ∀ g, TFNonneg g → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W g) :
    ∀ᵐ x ∂volume.restrict Ω,
      0 ≤ c*(5/3:ℝ)*(f x)^(2/3:ℝ)-W x+tfPotential f x ∧
      (c*(5/3:ℝ)*(f x)^(2/3:ℝ)-W x+tfPotential f x)*f x = 0 := by
  filter_upwards [tfGradientField_coe hΩ c W hf,tfGradientField_nonneg hΩ c W hf hm,
    tfGradientField_complementarity hΩ c W hf hm] with x he hn hz
  simpa only [he] using And.intro hn hz
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TfFunctionalUniformBound
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
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
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]
lemma tfEuler_equation {c : ℝ} (hc : 0 < c) (W : TFLq (volume.restrict Ω))
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (hm : ∀ g, TFNonneg g → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W g) :
    ∀ᵐ x ∂volume.restrict Ω,
      f x = (max (W x-tfPotential f x) 0/(c*(5/3:ℝ)))^(3/2:ℝ) ∧
      tfGradientField hΩ c W f x = max (tfPotential f x-W x) 0 := by
  filter_upwards [hf,tfEuler_complementarity hΩ c W hf hm,tfGradientField_coe hΩ c W hf] with x hx hh he
  have H := tf_complementarity_solve (show 0 < c*(5/3:ℝ) by positivity) hx
    (show 0 ≤ c*(5/3:ℝ)*(f x)^(2/3:ℝ)-(W x-tfPotential f x) by linarith [hh.1])
    (by convert hh.2 using 1; ring)
  refine ⟨H.1,?_⟩
  calc
    _ = c*(5/3:ℝ)*(f x)^(2/3:ℝ)-(W x-tfPotential f x) := by rw [he]; ring
    _ = max (-(W x-tfPotential f x)) 0 := H.2
    _ = _ := by rw [neg_sub]
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]
lemma tfEnergy_expansion (c : ℝ) (W : TFLq (volume.restrict Ω))
    {f g : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    tfEnergy hΩ c W g-tfEnergy hΩ c W f =
      tfCoulomb Ω (g-f) (g-f)/2+c*tfBregman f g+
        tfFieldContinuous (tfGradientField hΩ c W f) (g-f) := by
  rw [tfGradientField_pair hΩ c W hf,←tfKineticField_pair hf]
  change tfFunctional c (tfFieldContinuous W) (tfCoulombContinuous hΩ) g-
    tfFunctional c (tfFieldContinuous W) (tfCoulombContinuous hΩ) f = _
  have he : tfCoulomb Ω (g-f) (g-f) = tfCoulomb Ω g g-tfCoulomb Ω g f-
      tfCoulomb Ω f g+tfCoulomb Ω f f := by
    change (tfCoulombContinuous hΩ) (g-f) (g-f) = _
    simp only [map_sub,_root_.sub_apply]
    change tfCoulomb Ω g g-tfCoulomb Ω f g-(tfCoulomb Ω g f-tfCoulomb Ω f f) = _
    ring
  have he' : tfCoulomb Ω (g-f) f = tfCoulomb Ω g f-tfCoulomb Ω f f := by
    change (tfCoulombContinuous hΩ) (g-f) f = _
    simp only [map_sub,_root_.sub_apply]
    rfl
  rw [he,he',tfCoulomb_symm f g]
  simp only [tfFunctional,tfBregman,map_sub]
  change c*‖g‖^(5/3:ℝ)-tfFieldContinuous W g+tfCoulomb Ω g g/2 -
    (c*‖f‖^(5/3:ℝ)-tfFieldContinuous W f+tfCoulomb Ω f f/2) = _
  ring
lemma tfEnergy_gap_controls (c : ℝ) (W : TFLq (volume.restrict Ω))
    {f g : TFLp (volume.restrict Ω)} (hf : TFNonneg f) (hg : TFNonneg g)
    (hm : ∀ h, TFNonneg h → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W h) :
    tfCoulomb Ω (g-f) (g-f)/2+c*tfBregman f g ≤ tfEnergy hΩ c W g-tfEnergy hΩ c W f := by
  rw [tfEnergy_expansion hΩ c W hf,map_sub,tfGradientField_self hΩ c W hf hm,sub_zero]
  apply le_add_of_nonneg_right
  rw [tfFieldContinuous_apply]
  apply integral_nonneg_of_ae
  filter_upwards [tfGradientField_nonneg hΩ c W hf hm,hg] with x hx hy
  exact mul_nonneg hx hy
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
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

lemma tfDensity_power_integrable {Ω : Set Space} (hΩ : MeasurableSet Ω)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    Integrable (fun x => (tfDensity Ω f x)^(5/3:ℝ)) :=
  integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3)
    (tfDensity_memLp hΩ hf) (Eventually.of_forall (tfDensity_nonneg f))

lemma localTFDensity_hole {M k : ℕ} {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (W : TFLq (volume.restrict Ω))
    (S : Nuclei M) (u : H1Vector k) (g : 𝓢(Space,ℝ)) (R : ℝ)
    (K A : Set Space) (hK : IsCompact K) (hA : IsClosed A) (hΩK : Ω ⊆ K)
    (hu : SpatiallySupported u A) (hsep : Disjoint A (K+tsupport (g : Space → ℝ)))
    (hcore : ∀ a ∈ A, ∀ y ∈ Ω, R ≤ ‖a-y‖)
    (hnuc : ∀ j y, y ∈ Ω → R ≤ ‖S.position j-y‖) :
    SourceFreeHoleDensity S u g R (localTFDensity hΩ W) K A := by
  have hs (y : Space) (hy : localTFDensity hΩ W y ≠ 0) : y ∈ Ω := by
    by_contra hn
    exact hy (tfDensity_eq_zero _ hn)
  refine ⟨tfDensity_nonneg _,tfDensity_measurable hΩ _,
    tfDensity_power_integrable hΩ (localTFMinimizer_nonneg hΩ W),hK,hA,?_,hu,hsep,?_,?_⟩
  · intro y hy
    exact tfDensity_eq_zero _ (fun h => hy (hΩK h))
  · intro a ha y hy
    exact hcore a ha y (hs y hy)
  · intro j y hy
    exact hnuc j y (hs y hy)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical BigOperators Topology SchwartzMap Pointwise
namespace Coulomb

lemma raw_localTF_gap {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    coulombBilinear (fun x => tfDensity Ω f x-localTFDensity hΩ W x)
      (fun x => tfDensity Ω f x-localTFDensity hΩ W x)/2+
      rawTFBregman (localTFDensity hΩ W) (tfDensity Ω f) ≤
    rawThomasFermiEnergy Φ (tfDensity Ω f)-rawThomasFermiEnergy Φ (localTFDensity hΩ W) := by
  unfold localTFDensity
  rw [coulombBilinear_tfDensity_sub hΩ (localTFMinimizer_nonneg hΩ W) hf,
    rawTFBregman_tfDensity hΩ (localTFMinimizer_nonneg hΩ W) hf,
    rawThomasFermiEnergy_tfDensity hΩ Φ W hW hf,
    rawThomasFermiEnergy_tfDensity hΩ Φ W hW (localTFMinimizer_nonneg hΩ W)]
  exact tfEnergy_gap_controls hΩ _ W (localTFMinimizer_nonneg hΩ W) hf
    (fun _ hf => localTFMinimizer_minimizes hΩ W hf)

lemma raw_localTF_gap_density {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {σ : Space → ℝ} (hσ : MemLp σ TFExponent (volume.restrict Ω))
    (hp : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ σ x) (hs : ∀ x ∉ Ω, σ x = 0) :
    coulombBilinear (fun x => σ x-localTFDensity hΩ W x)
      (fun x => σ x-localTFDensity hΩ W x)/2+
      rawTFBregman (localTFDensity hΩ W) σ ≤
    rawThomasFermiEnergy Φ σ-rawThomasFermiEnergy Φ (localTFDensity hΩ W) := by
  have he := tfDensity_rawToTFLp hΩ hσ hp hs
  have hd : (fun x => tfDensity Ω (rawToTFLp σ hσ) x-localTFDensity hΩ W x) =ᵐ[volume]
      (fun x => σ x-localTFDensity hΩ W x) := he.sub EventuallyEq.rfl
  have H := raw_localTF_gap hΩ Φ W hW (rawToTFLp_nonneg hσ hp)
  rwa [coulombBilinear_congr_ae hd hd,rawTFBregman_congr_ae EventuallyEq.rfl he,
    rawThomasFermiEnergy_congr_ae Φ he] at H

end Coulomb

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

lemma rawTF_gap_coulomb (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {σ : Space → ℝ} (hσ : MemLp σ TFExponent (volume.restrict Ω))
    (hp : ∀ᵐ x, 0≤σ x) (hs : ∀ x∉Ω, σ x=0) :
    coulombBilinear (fun x => σ x-localTFDensity hΩ W x)
      (fun x => σ x-localTFDensity hΩ W x) ≤
      2*(rawThomasFermiEnergy Φ σ-rawThomasFermiEnergy Φ (localTFDensity hΩ W)) := by
  have H := raw_localTF_gap_density hΩ Φ W hW hσ (ae_restrict_of_ae hp) hs
  have HB := rawTFBregman_nonneg (ρ := localTFDensity hΩ W) (Eventually.of_forall (tfDensity_nonneg (localTFMinimizer hΩ W))) hp
  linarith

lemma rawTF_count_test (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {σ : Space → ℝ} (hσ : MemLp σ TFExponent (volume.restrict Ω))
    (hp : ∀ᵐ x, 0≤σ x) (hs : ∀ x∉Ω, σ x=0)
    (y : Space) {a : ℝ} (ha : 0<a) (hb : Metric.closedBall y (2*a)⊆Ω) :
    (∫ x, σ x*countTest y a x)^2 ≤
      2*(∫ x, localTFDensity hΩ W x*countTest y a x)^2+
      4*a*(max countTestEnergy 0)*(rawThomasFermiEnergy Φ σ-
        rawThomasFermiEnergy Φ (localTFDensity hΩ W)) := by
  let ρ := localTFDensity hΩ W
  have hρ : MemLp ρ TFExponent volume := tfDensity_memLp hΩ (localTFMinimizer_nonneg hΩ W)
  have hρs (x : Space) (hx : x∉Ω) : ρ x=0 := tfDensity_eq_zero _ hx
  have hd := hσ.sub (hρ.restrict (s := Ω))
  have hds : ∀ x∉Ω, σ x-ρ x=0 := fun x hx => by rw [hs x hx,hρs x hx,sub_self]
  have H := raw_coulomb_smooth_test hΩ (countTest_smooth y a) (countTest_compact y ha)
    ((countTest_support y ha).trans hb) hd hds
  rw [countTest_energy y ha] at H
  have hQ := raw_coulomb_nonneg hΩ hd hds
  have Hgap := rawTF_gap_coulomb hΩ Φ W hW hσ hp hs
  have He := mul_le_mul_of_nonneg_left (le_max_left countTestEnergy 0) (mul_nonneg ha.le hQ)
  have Hg := mul_le_mul_of_nonneg_right Hgap (mul_nonneg ha.le (le_max_right countTestEnergy 0))
  have hiσ : Integrable σ := (tfExtend_integrable hΩ (hσ.toLp σ)).congr (tfExtend_toLp hΩ hσ hs)
  have hiρ : Integrable ρ := (tfExtend_integrable hΩ (localTFMinimizer hΩ W)).congr
    (tfDensity_ae_tfExtend hΩ (localTFMinimizer_nonneg hΩ W)).symm
  have hiσχ := integrable_mul_countTest hiσ y a
  have hiρχ := integrable_mul_countTest hiρ y a
  have he : (∫ x, (σ x-ρ x)*countTest y a x)=(∫ x, σ x*countTest y a x)-
      (∫ x, ρ x*countTest y a x) := by
    simp_rw [sub_mul]; exact integral_sub hiσχ hiρχ
  simp only [Pi.sub_apply,Pi.sub_def] at H hQ He
  rw [he] at H
  dsimp only [ρ] at H hQ He hiρχ
  nlinarith only [H,He,Hg,sq_nonneg ((∫ x, σ x*countTest y a x)-2*(∫ x, localTFDensity hΩ W x*countTest y a x))]

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

lemma retainedFineDensity_memLp {n : ℕ} {b : ℝ} (hb : 0<b)
    (r : Finset (Fin n)) (x : Fin n → Space) {Ω : Set Space}
    [IsFiniteMeasure (volume.restrict Ω)] :
    MemLp (retainedFineDensity b r x) TFExponent (volume.restrict Ω) := by
  apply MemLp.of_bound ((retainedFineDensity_measurable b r x).aestronglyMeasurable) ((n:ℝ)*(b⁻¹)^3)
  filter_upwards [] with z
  rw [Real.norm_of_nonneg (retainedFineDensity_nonneg ..)]
  apply (retainedFineDensity_le ..).trans
  unfold fineDensity
  calc
    _≤∑ _i : Fin n, (b⁻¹)^3 := Finset.sum_le_sum (fun _ _ => fineKernel_le hb _)
    _=_ := by simp

lemma retainedFineDensity_patch_support {n : ℕ} {b : ℝ} (hb : 0<b)
    (y : Space) (t : ℝ) (x : Configuration n) (z : Space)
    (hz : z∉Metric.ball y (t-4*b)) :
    retainedFineDensity b (patchRetained y t b x) (position x) z=0 := by
  apply Finset.sum_eq_zero
  intro i hi
  apply fineKernel_eq_zero_of_two_mul_lt hb
  have hc := (patchRetained_mem y t b x i).mp hi
  have hn : t-4*b≤‖z-y‖ := by simpa only [Metric.mem_ball,dist_eq_norm,not_lt] using hz
  have htri := norm_sub_le_norm_sub_add_norm_sub z (position x i) y
  linarith

lemma localCount_le_fine_test {n : ℕ} {a b t : ℝ} (ha : 0<a) (hb : 0<b)
    (hsmall : 4*b≤a) (ht : a<t-7*b) (y : Space) (x : Configuration n) :
    localCount (Metric.closedBall y a) x≤
      ∫ z, retainedFineDensity b (patchRetained y t b x) (position x) z*countTest y (3*a/2) z := by
  simp only [retainedFineDensity,Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => integrable_mul_countTest (fineKernel_shift_integrable hb _) y (3*a/2))]
  have hr : localCount (Metric.closedBall y a) x=
      ∑ i∈patchRetained y t b x, (Metric.closedBall y a).indicator (fun _ => (1:ℝ)) (position x i) := by
    unfold localCount
    apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro i hi hn
    apply indicator_of_notMem
    intro hm
    apply hn
    apply (patchRetained_mem ..).mpr
    have hh : ‖position x i-y‖≤a := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hm
    exact hh.trans_lt ht
  rw [hr]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hm : position x i∈Metric.closedBall y a
  · rw [indicator_of_mem hm,fineKernel_countTest_one ha hb hsmall y (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hm)]
  · rw [indicator_of_notMem hm]
    exact integral_nonneg (fun z => mul_nonneg (fineKernel_nonneg ..) (countTest_nonneg ..))

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TFInterior
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Classical BigOperators Topology ContDiff
noncomputable section
namespace Coulomb

variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]

include hΩ

lemma tfDensity_bound_of_minimizes {c F : ℝ} (hc : 0 < c) (hF : 0≤F)
    (W : TFLq (volume.restrict Ω)) (hW : ∀ᵐ x ∂volume.restrict Ω, W x≤F)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (hm : ∀ g, TFNonneg g → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W g) :
    ∀ᵐ x ∂volume, tfDensity Ω f x ≤ (F/(c*(5/3:ℝ)))^(3/2:ℝ) := by
  have ha : 0 < c*(5/3:ℝ) := by positivity
  have hlocal : ∀ᵐ x ∂volume.restrict Ω, f x≤(F/(c*(5/3:ℝ)))^(3/2:ℝ) := by
    filter_upwards [tfEuler_equation hΩ hc W hf hm,hW] with x hx hw
    rw [hx.1]
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    apply div_le_div_of_nonneg_right _ ha.le
    exact max_le (by linarith [tfPotential_nonneg_of_nonneg hΩ hf x]) hF
  filter_upwards [(ae_restrict_iff' hΩ).mp hlocal,tfDensity_ae_tfExtend hΩ hf] with x hx he
  rw [he]
  by_cases hs : x∈Ω
  · simpa only [tfExtend,indicator_of_mem hs] using hx hs
  · simp only [tfExtend,indicator_of_notMem hs]
    exact Real.rpow_nonneg (div_nonneg hF ha.le) _

lemma tfPotential_continuous_of_minimizes {c F : ℝ} (hc : 0 < c) (hF : 0≤F)
    (W : TFLq (volume.restrict Ω)) (hW : ∀ᵐ x ∂volume.restrict Ω, W x≤F)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (hm : ∀ g, TFNonneg g → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W g) :
    Continuous (tfPotential f) := by
  let L := (F/(c*(5/3:ℝ)))^(3/2:ℝ)
  let ρ : Space → ℝ := fun x => min (tfDensity Ω f x) L
  have hL : 0≤L := Real.rpow_nonneg (by positivity) _
  have hρ : ρ =ᵐ[volume] tfExtend Ω f := by
    filter_upwards [tfDensity_bound_of_minimizes hΩ hc hF W hW hf hm,
      tfDensity_ae_tfExtend hΩ hf] with x hx he
    exact (min_eq_left hx).trans he
  have hi : Integrable ρ := (tfExtend_integrable hΩ f).congr hρ.symm
  have hp (x) : 0≤ρ x := le_min (tfDensity_nonneg _ _) hL
  have hb (x) : ρ x≤L := min_le_right _ _
  have he : tfPotential f = NeutralAtom.potentialOf ρ := by
    funext x
    apply integral_congr_ae
    filter_upwards [hρ] with y hy
    change coulombKernel (x-y)*tfExtend Ω f y=coulombKernel (x-y)*ρ y
    rw [hy]
  rw [he]
  exact NeutralAtom.potentialOf_continuous hi hp hb

lemma tfScreened_weak_equation {c F : ℝ} (hc : 0 < c) (hF : 0≤F)
    (W : TFLq (volume.restrict Ω)) (hW : ∀ᵐ x ∂volume.restrict Ω, W x≤F)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (hm : ∀ g, TFNonneg g → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W g)
    {Φ : Space → ℝ} (hΦ : ContinuousOn Φ Ω) (ho : IsOpen Ω)
    (he : W =ᵐ[volume.restrict Ω] Φ)
    (hh : NeutralAtom.HasWeakLaplacian Φ Ω (fun _ => 0)) :
    NeutralAtom.HasWeakLaplacian (fun x => Φ x-tfPotential f x) Ω
      (fun x => (4*Real.pi)/(c*(5/3:ℝ))^(3/2:ℝ)*(max (Φ x-tfPotential f x) 0)^(3/2:ℝ)) := by
  intro φ hφ hφc ht
  have hL := NeutralAtom.continuous_coordinateLaplacian
    (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top))
  have hLc := NeutralAtom.hasCompactSupport_coordinateLaplacian hφc
  have hts : tsupport (NeutralAtom.coordinateLaplacian φ) ⊆ tsupport φ := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    by_contra hn
    exact hx (NeutralAtom.coordinateLaplacian_eq_zero_of_notMem_tsupport hn)
  have hiΦ : Integrable (fun x => Φ x*NeutralAtom.coordinateLaplacian φ x) :=
    NeutralAtom.integrable_mul_compact_of_continuousAt
      (fun x hx => hΦ.continuousAt (ho.mem_nhds (ht (hts hx)))) hL hLc
  have hiP : Integrable (fun x => tfPotential f x*NeutralAtom.coordinateLaplacian φ x) :=
    NeutralAtom.integrable_mul_compact_of_continuousAt
      (fun x _ => (tfPotential_continuous_of_minimizes hΩ hc hF W hW hf hm).continuousAt) hL hLc
  have hP := NeutralAtom.potentialOf_weakLaplacian (tfExtend_integrable hΩ f) φ hφ hφc (subset_univ _)
  change (∫ x, tfPotential f x*NeutralAtom.coordinateLaplacian φ x) = _ at hP
  simp_rw [sub_mul]
  rw [integral_sub hiΦ hiP,hh φ hφ hφc ht,hP]
  simp only [zero_mul,integral_zero,zero_sub,←integral_neg,neg_mul,neg_neg]
  apply integral_congr_ae
  have hE := (ae_restrict_iff' hΩ).mp (tfEuler_equation hΩ hc W hf hm)
  have hWe := (ae_restrict_iff' hΩ).mp he
  filter_upwards [hE,hWe] with x hx hw
  by_cases hs : x∈Ω
  · simp only [tfExtend,indicator_of_mem hs]
    rw [(hx hs).1,hw hs,Real.div_rpow (le_max_right _ _) (by positivity)]
    ring
  · have hpz : φ x=0 := image_eq_zero_of_notMem_tsupport (fun h => hs (ht h))
    simp only [hpz,mul_zero]

theorem tfScreened_interior_upper {c F : ℝ} (hc : 0 < c) (hF : 0≤F)
    (W : TFLq (volume.restrict Ω)) (hW : ∀ᵐ x ∂volume.restrict Ω, W x≤F)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (hm : ∀ g, TFNonneg g → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W g)
    {Φ : Space → ℝ} (hΦ : ContinuousOn Φ Ω) (ho : IsOpen Ω)
    (he : W =ᵐ[volume.restrict Ω] Φ)
    (hh : NeutralAtom.HasWeakLaplacian Φ Ω (fun _ => 0))
    {y : Space} {s : ℝ} (hs : 0 < s) (hball : Metric.closedBall y s⊆Ω)
    {z : Space} (hz : z∈Metric.ball y s) :
    Φ z-tfPotential f z ≤
      (80/((4*Real.pi)/(c*(5/3:ℝ))^(3/2:ℝ)))^2*s^4/(s^2-‖z-y‖^2)^4 := by
  have hcc : 0<(4*Real.pi)/(c*(5/3:ℝ))^(3/2:ℝ) := by positivity
  apply NeutralAtom.weak_power_interior_upper hs hcc
    ((hΦ.mono hball).sub ((tfPotential_continuous_of_minimizes hΩ hc hF W hW hf hm).continuousOn))
    ((tfScreened_weak_equation hΩ hc hF W hW hf hm hΦ ho he hh).mono
      (Metric.ball_subset_closedBall.trans hball)) hz

lemma tfScreened_three_quarters {c F : ℝ} (hc : 0 < c) (hF : 0≤F)
    (W : TFLq (volume.restrict Ω)) (hW : ∀ᵐ x ∂volume.restrict Ω, W x≤F)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (hm : ∀ g, TFNonneg g → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W g)
    {Φ : Space → ℝ} (hΦ : ContinuousOn Φ Ω) (ho : IsOpen Ω)
    (he : W =ᵐ[volume.restrict Ω] Φ)
    (hh : NeutralAtom.HasWeakLaplacian Φ Ω (fun _ => 0))
    {y : Space} {a : ℝ} (ha : 0<a) (hball : Metric.closedBall y (4*a)⊆Ω)
    {z : Space} (hz : z∈Metric.closedBall y (3*a)) :
    Φ z-tfPotential f z ≤ tfInteriorConstant c/a^4 := by
  have hz' : ‖z-y‖≤3*a := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
  have hz4 : z∈Metric.ball y (4*a) := by
    simp only [Metric.mem_ball,dist_eq_norm]; linarith
  have H := tfScreened_interior_upper hΩ hc hF W hW hf hm hΦ ho he hh
    (by positivity : 0<4*a) hball hz4
  have hD : a^2 ≤ (4*a)^2-‖z-y‖^2 := by
    nlinarith [sq_le_sq₀ (norm_nonneg (z-y)) (by positivity : 0≤3*a) |>.mpr hz']
  have hD0 : 0<(4*a)^2-‖z-y‖^2 := (sq_pos_of_pos ha).trans_le hD
  apply H.trans
  have hd4 : a^8 ≤ ((4*a)^2-‖z-y‖^2)^4 := by
    simpa only [←pow_mul,show 2*4=8 by norm_num] using pow_le_pow_left₀ (sq_nonneg a) hD 4
  apply (div_le_div_iff₀ (pow_pos hD0 4) (pow_pos ha 4)).mpr
  have hc0 := tfInteriorConstant_nonneg c
  have Hm := mul_le_mul_of_nonneg_left hd4 hc0
  calc
    _ = tfInteriorConstant c*a^8 := by dsimp [tfInteriorConstant]; ring
    _ ≤ _ := Hm

lemma tfDensity_interior_bound {c F : ℝ} (hc : 0 < c) (hF : 0≤F)
    (W : TFLq (volume.restrict Ω)) (hW : ∀ᵐ x ∂volume.restrict Ω, W x≤F)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (hm : ∀ g, TFNonneg g → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W g)
    {Φ : Space → ℝ} (hΦ : ContinuousOn Φ Ω) (ho : IsOpen Ω)
    (he : W =ᵐ[volume.restrict Ω] Φ)
    (hh : NeutralAtom.HasWeakLaplacian Φ Ω (fun _ => 0))
    {y : Space} {a : ℝ} (ha : 0<a) (hball : Metric.closedBall y (4*a)⊆Ω) :
    ∀ᵐ z ∂volume.restrict (Metric.closedBall y (3*a)), tfDensity Ω f z ≤
      (tfInteriorConstant c/(c*(5/3:ℝ)))^(3/2:ℝ)/a^6 := by
  have hsub : Metric.closedBall y (3*a)⊆Ω :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hball
  have he' := (ae_restrict_iff' hΩ).mp he
  have hE := (ae_restrict_iff' hΩ).mp (tfEuler_equation hΩ hc W hf hm)
  apply (ae_restrict_iff' measurableSet_closedBall).mpr
  filter_upwards [he',hE,tfDensity_ae_tfExtend hΩ hf] with z hze hzE hden
  intro hz
  have hzΩ := hsub hz
  rw [hden,tfExtend,indicator_of_mem hzΩ,(hzE hzΩ).1,hze hzΩ]
  have H := tfScreened_three_quarters hΩ hc hF W hW hf hm hΦ ho he hh ha hball hz
  have Hb : max (Φ z-tfPotential f z) 0 ≤ tfInteriorConstant c/a^4 :=
    max_le H (div_nonneg (tfInteriorConstant_nonneg c) (by positivity))
  have HH := Real.rpow_le_rpow (by positivity : 0 ≤ max (Φ z-tfPotential f z) 0/(c*(5/3:ℝ)))
    (div_le_div_of_nonneg_right Hb (by positivity : 0 ≤ c*(5/3:ℝ))) (by norm_num : (0:ℝ)≤3/2)
  apply HH.trans_eq
  rw [show tfInteriorConstant c/a^4/(c*(5/3:ℝ))=(tfInteriorConstant c/(c*(5/3:ℝ)))/a^4 by ring,
    Real.div_rpow (div_nonneg (tfInteriorConstant_nonneg c) (by positivity)) (by positivity),←Real.rpow_natCast,←Real.rpow_mul ha.le]
  norm_num

end Coulomb

end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_PatchGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology ContDiff SchwartzMap Pointwise
noncomputable section
namespace Coulomb

lemma patch_hole_density {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a) (ht : t≤6*a) (y : Space)
    (hu : SpatiallySupported u {z | t≤‖z-y‖}) (hn : ∀ j, 20*a≤‖S.position j-y‖)
    (W : TFLq (volume.restrict (Metric.ball y (t-4*b)))) :
    SourceFreeHoleDensity S u (scaledWindow unitWindow b hb.ne') b
      (localTFDensity measurableSet_ball W) (Metric.closedBall y (t-4*b)) {z | t≤‖z-y‖} := by
  apply localTFDensity_hole measurableSet_ball W S u _ b _ _
    (isCompact_closedBall ..) (isClosed_le continuous_const (by fun_prop)) Metric.ball_subset_closedBall hu
  · apply Set.disjoint_left.mpr
    rintro z hz ⟨v,hv,w,hw,rfl⟩
    have hv' : ‖v-y‖≤t-4*b := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hv
    have hw' : ‖w‖≤b := by
      apply le_of_not_gt
      intro hw'
      have hn' : w∉tsupport (scaledWindow unitWindow b hb.ne' : Space → ℝ) := by
        have hs : tsupport (scaledWindow unitWindow b hb.ne' : Space → ℝ)⊆Metric.closedBall 0 b := by
          apply closure_minimal _ Metric.isClosed_closedBall
          intro x hx
          simp only [Metric.mem_closedBall,dist_zero_right]
          exact le_of_not_gt (fun h => hx (scaledWindow_support unitWindow unitWindow_support hb x h))
        intro hm
        have hle : ‖w‖≤b := by simpa only [Metric.mem_closedBall,dist_zero_right] using hs hm
        linarith
      exact hn' hw
    have htri : ‖v+w-y‖≤‖v-y‖+‖w‖ := by
      simpa only [show v+w-y=(v-y)+w by abel] using norm_add_le (v-y) w
    change t≤‖v+w-y‖ at hz
    linarith
  · intro z hz x hx
    have hh : ‖x-y‖<t-4*b := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
    have H := norm_sub_le_norm_sub_add_norm_sub z x y
    change t≤‖z-y‖ at hz
    linarith
  · intro j x hx
    have H := patch_nucleus_separation S ha hb ht y hn j x hx
    rw [norm_sub_rev]
    linarith

lemma patch_TF_test_bound {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a b t F : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hu : SpatiallySupported u {z | t≤‖z-y‖}) (hn : ∀ j, 20*a≤‖S.position j-y‖)
    (hF : 0≤F) (hcap : ∀ x∈Metric.ball y (t-4*b), coreScreenedField S u x≤F) :
    (∫ x, localTFDensity measurableSet_ball
      (coreTFField S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn)) x*
      countTest y (3*a/2) x) ≤ tfInteriorCountConstant/a^3 := by
  let W := coreTFField S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn)
  have hW : ∀ᵐ x ∂volume.restrict (Metric.ball y (t-4*b)), W x≤F := by
    filter_upwards [coreTFField_coe S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn),ae_restrict_mem measurableSet_ball] with x hx hy
    exact hx ▸ hcap x hy
  have H := tfDensity_interior_bound measurableSet_ball thomasFermiKineticConstant_pos hF W hW
    (localTFMinimizer_nonneg measurableSet_ball W) (fun g hg => localTFMinimizer_minimizes measurableSet_ball W hg)
    (patch_continuous_field S u ha hb ht.2 y hu hn) Metric.isOpen_ball
    (coreTFField_coe S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn))
    (patch_harmonic_field S u ha hb ht.2 y hu hn) ha (patch_inner_ball ha hb hsmall ht.1 y)
  have H' := tfDensity_test_bound measurableSet_ball (localTFMinimizer_nonneg measurableSet_ball W) y
    (by positivity : 0<3*a/2) (by positivity [tfInteriorConstant_nonneg thomasFermiKineticConstant,thomasFermiKineticConstant_pos] : 0≤(tfInteriorConstant thomasFermiKineticConstant/(thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)/a^6)
    (by simpa only [show 2*(3*a/2)=3*a by ring] using H)
  apply H'.trans_eq
  unfold tfInteriorCountConstant
  field_simp
  ring

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_PatchComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap
noncomputable section
namespace Coulomb

theorem physical_patch_comparison {J m k : ℕ} (S : Nuclei J) (ψ : H1Vector (m+k))
    (ho : ∀ (s : Spins k) (p : Equiv.Perm (Fin m)) (t : Spins m),
      ∀ᵐ z, ψ.value (outerAppend s t ∘ outerPerm k p) (permute (outerPerm k p) z) =
        (((outerPerm k p).sign : ℤ):ℂ)*ψ.value (outerAppend s t) z)
    (hc : ∀ s, ∀ᵐ x, Antisymmetric (ψ.coreSlice s x))
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a) (ht : t∈Set.Icc (5*a) (6*a))
    (y : Space) (hn : ∀ j, 20*a≤‖S.position j-y‖)
    (hcs : ∀ s, ∀ᵐ x, SpatiallySupported (ψ.coreSlice s x).normalized {z | t≤‖z-y‖})
    (hos : ∀ s, ∀ᵐ x, mass (ψ.coreSlice s x)≠0 → ∀ i, position x i∈Metric.closedBall y (t+b))
    (F : Spins m → Configuration m → ℝ)
    (hFm : ∀ s, AEStronglyMeasurable (F s) volume)
    (hF0 : ∀ s, ∀ᵐ x, 0≤F s x)
    (hFi : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*(F s x)^2))
    (hcap : ∀ s, ∀ᵐ x, ∀ w∈Metric.closedBall y (t+b), coreScreenedField S (ψ.coreSlice s x).normalized w≤F s x)
    {E : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S) :
    let ρ := fun s x => localTFDensity measurableSet_ball
      (coreTFField S (ψ.coreSlice s x).normalized measurableSet_ball ha
        (patch_nucleus_separation S ha hb ht.2 y hn))
    sliceExpectation ψ (fun s x => rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized)
      (retainedFineDensity b (patchRetained y t b x) (position x))-
      rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized) (ρ s x)) ≤
      form S ψ-E*mass ψ+
      sliceExpectation ψ (fun s x => packetKineticError (scaledWindow unitWindow b hb.ne') (ρ s x))+
      sliceExpectation ψ (fun s x => F s x*localCount {z | t-7*b≤‖z-y‖} x)+fineLocalizationError m b*mass ψ := by
  dsimp only
  let ρ := fun s x => localTFDensity measurableSet_ball
    (coreTFField S (ψ.coreSlice s x).normalized measurableSet_ball ha
      (patch_nucleus_separation S ha hb ht.2 y hn))
  have hcap' (s : Spins m) : ∀ᵐ x, ∀ w∈Metric.ball y (t-4*b), coreScreenedField S (ψ.coreSlice s x).normalized w≤F s x := by
    filter_upwards [hcap s] with x hx
    intro w hw
    apply hx w
    exact Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith)) hw
  have hTF (s : Spins m) := coreTF_conditional_integrable measurableSet_ball S ψ s ha
    (patch_nucleus_separation S ha hb ht.2 y hn) (show 0<12*a by positivity)
    (patch_diameter ha hb ht.2 y) (F s) (hF0 s) (hFi s) (hcap' s)
  have hFC (s : Spins m) : Integrable (fun x => mass (ψ.coreSlice s x)*(F s x*(deletedLabels (patchRetained y t b) x).card)) := by
    simp_rw [deletedLabels_patchRetained]
    exact weighted_cap_count_integrable (mass_coreSlice_integrable ψ s)
      (Eventually.of_forall (fun _ => mass_nonneg _)) (hFm s) (hF0 s) (hFi s)
      (localCount_measurable (isClosed_le continuous_const (by fun_prop)).measurableSet).aestronglyMeasurable
      (Nat.cast_nonneg m) (Eventually.of_forall (fun x => ⟨localCount_nonneg _ x,localCount_le _ x⟩))
  have hKC (s : Spins m) : Integrable (fun x => mass (ψ.coreSlice s x)*packetKineticError (scaledWindow unitWindow b hb.ne') (ρ s x)) := by
    unfold packetKineticError
    convert (hTF s).1.mul_const ((1/2:ℝ)*(∑ j : Fin 3, ∫ z : Space,
      (fderiv ℝ (scaledWindow unitWindow b hb.ne') z (EuclideanSpace.single j 1))^2)) using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    ring
  let F' := fun s x => if mass (ψ.coreSlice s x)=0 then
    ∑ i : Fin m, max (coreScreenedField S (ψ.coreSlice s x).normalized (position x i)) 0 else F s x
  have hFC' (s : Spins m) : Integrable (fun x => mass (ψ.coreSlice s x)*(F' s x*(deletedLabels (patchRetained y t b) x).card)) := by
    apply (hFC s).congr
    filter_upwards [] with x
    dsimp only [F']
    split_ifs with hm <;> simp_all
  have hFE : sliceExpectation ψ (fun s x => F' s x*(deletedLabels (patchRetained y t b) x).card)=
      sliceExpectation ψ (fun s x => F s x*localCount {z | t-7*b≤‖z-y‖} x) := by
    apply Finset.sum_congr rfl
    intro s hs
    apply integral_congr_ae
    filter_upwards [] with x
    rw [deletedLabels_patchRetained]
    dsimp only [F']
    split_ifs with hm <;> simp_all
  have HH := source_free_patch_comparison S ψ ho hc hb (patchRetained y t b) (patchRetained_measurable y t b)
    F' hFC' (show ∀ s, ∀ᵐ x, ∀ i∈deletedLabels (patchRetained y t b) x,
      coreScreenedField S (ψ.coreSlice s x).normalized (position x i)≤F' s x from ?_)
    (scaledWindow unitWindow b hb.ne') (by rw [scaledWindow_mass _ hb,unitWindow_mass])
    (scaledWindow_compactSupport unitWindow unitWindow_support hb)
    (scaledWindow_radial unitWindow unitWindow_radial hb) hb
    (scaledWindow_support unitWindow unitWindow_support hb) ρ
    (fun _ _ => Metric.closedBall y (t-4*b)) (fun _ _ => {z | t≤‖z-y‖})
    (show ∀ s, ∀ᵐ x, SourceFreeHoleDensity S (ψ.coreSlice s x).normalized _ b (ρ s x) _ _ from ?_)
    (show ∀ s : Spins m, ∀ᵐ x, ∀ j i, i∈patchRetained y t b x → Real.sqrt 3*b≤‖S.position j-position x i‖ from ?_)
    (fun _ => Eventually.of_forall (fun x => patch_retained_separated ha hb y x))
    (fun s => (hTF s).2) hKC hE
  · rwa [hFE] at HH
  · intro s
    filter_upwards [hcap s,hos s] with x hx ho
    intro i hi
    dsimp only [F']
    split_ifs with hm
    · exact (le_max_left _ 0).trans (Finset.single_le_sum (fun j _ => le_max_right (coreScreenedField S (ψ.coreSlice s x).normalized (position x j)) 0) (Finset.mem_univ i))
    · exact hx _ (ho hm i)
  · intro s
    filter_upwards [hcs s] with x hx
    exact patch_hole_density S _ ha hb hsmall ht.2 y hx hn _
  · intro s
    filter_upwards [] with x
    intro j i hi
    have hret := (patchRetained_mem ..).mp hi
    have H := norm_sub_le_norm_sub_add_norm_sub (S.position j) (position x i) y
    have hs : Real.sqrt 3≤2 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
    nlinarith [hn j,ht.2]

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

lemma physical_patch_count_gap {J n k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a b t F : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hn : ∀ j, 20*a≤‖S.position j-y‖)
    (hu : SpatiallySupported u {z | t≤‖z-y‖})
    (hF : 0≤F) (hcap : ∀ w∈Metric.ball y (t-4*b), coreScreenedField S u w≤F)
    (x : Configuration n) :
    let ρ := localTFDensity measurableSet_ball
      (coreTFField S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn))
    (localCount (Metric.closedBall y a) x)^2 ≤
      2*(tfInteriorCountConstant/a^3)^2+6*a*(max countTestEnergy 0)*
      (rawThomasFermiEnergy (coreScreenedField S u) (retainedFineDensity b (patchRetained y t b x) (position x))-
        rawThomasFermiEnergy (coreScreenedField S u) ρ) := by
  dsimp only
  have Hcount := localCount_le_fine_test (t := t) ha hb (by linarith) (by linarith [ht.1]) y x
  have Hgap := rawTF_count_test measurableSet_ball (coreScreenedField S u)
    (coreTFField S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn))
    (coreTFField_coe S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn))
    (retainedFineDensity_memLp hb (patchRetained y t b x) (position x))
    (Eventually.of_forall (retainedFineDensity_nonneg b (patchRetained y t b x) (position x)))
    (retainedFineDensity_patch_support hb y t x) y (show 0<3*a/2 by positivity)
    (show Metric.closedBall y (2*(3*a/2))⊆Metric.ball y (t-4*b) from
      (Metric.closedBall_subset_closedBall (by linarith)).trans (patch_inner_ball ha hb hsmall ht.1 y))
  have HT := patch_TF_test_bound S u ha hb hsmall ht y hu hn hF hcap
  have hp : 0≤∫ z, localTFDensity measurableSet_ball
      (coreTFField S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn)) z*countTest y (3*a/2) z :=
    integral_nonneg (fun z => mul_nonneg (tfDensity_nonneg _ z) (countTest_nonneg ..))
  have Ht2 := pow_le_pow_left₀ hp HT 2
  have Hc2 := pow_le_pow_left₀ (localCount_nonneg _ _) Hcount 2
  nlinarith only [Hgap,Ht2,Hc2]

section Averaged
variable {J m k : ℕ} (S : Nuclei J) (ψ : H1Vector (m+k))
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a) (ht : t∈Set.Icc (5*a) (6*a))
    (y : Space) (hn : ∀ j, 20*a≤‖S.position j-y‖)
    (hcs : ∀ s, ∀ᵐ x, SpatiallySupported (ψ.coreSlice s x).normalized {z | t≤‖z-y‖})
    (F : Spins m → Configuration m → ℝ)
    (hF0 : ∀ s, ∀ᵐ x, 0≤F s x)
    (hFi : ∀ s, Integrable (fun x => mass (ψ.coreSlice s x)*(F s x)^2))
    (hcap : ∀ s, ∀ᵐ x, ∀ w∈Metric.closedBall y (t+b), coreScreenedField S (ψ.coreSlice s x).normalized w≤F s x)

include hsmall hcs F hF0 hFi hcap in
lemma physical_patch_averaged_count :
    let ρ := fun s x => localTFDensity measurableSet_ball
      (coreTFField S (ψ.coreSlice s x).normalized measurableSet_ball ha
        (patch_nucleus_separation S ha hb ht.2 y hn))
    sliceExpectation ψ (fun _ x => (localCount (Metric.closedBall y a) x)^2)≤
      2*(tfInteriorCountConstant/a^3)^2*mass ψ+6*a*(max countTestEnergy 0)*
      sliceExpectation ψ (fun s x =>
        rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized)
          (retainedFineDensity b (patchRetained y t b x) (position x))-
        rawThomasFermiEnergy (coreScreenedField S (ψ.coreSlice s x).normalized) (ρ s x)) := by
  dsimp only
  have hcap' (s : Spins m) : ∀ᵐ x, ∀ w∈Metric.ball y (t-4*b), coreScreenedField S (ψ.coreSlice s x).normalized w≤F s x := by
    filter_upwards [hcap s] with x hx
    exact fun w hw => hx w (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith)) hw)
  apply sliceExpectation_le_affine
  · exact fun s => sliceCount_weight_integrable ψ measurableSet_closedBall s 2
  · intro s
    have hTF := coreTF_conditional_integrable measurableSet_ball S ψ s ha
      (patch_nucleus_separation S ha hb ht.2 y hn) (show 0<12*a by positivity)
      (patch_diameter ha hb ht.2 y) (F s) (hF0 s) (hFi s) (hcap' s)
    apply ((patchFineTF_weight_integrable S ψ ha hb hsmall ht.2 y hn s (hcs s)).sub hTF.2).congr
    exact Eventually.of_forall (fun x => (mul_sub ..).symm)
  · intro s
    filter_upwards [hcs s,hF0 s,hcap' s] with x hc hf hcap
    exact physical_patch_count_gap S _ ha hb hsmall ht y hn hc hf hcap x

end Averaged

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_PhysicalEnsemble
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

theorem physical_ensemble_count {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n)
    (T : RecordedEnsemble n) (hC : T.Conserves ψ) (hc : T.CoreFermionic) (ho : T.OutFermionic)
    (hm : T.totalMass=1) {E B : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S)
    (henergy : T.totalForm S≤E+B)
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a) (ht : t∈Set.Icc (5*a) (6*a))
    (y : Space) (hn : ∀ j, 20*a≤‖S.position j-y‖)
    (hcs : T.CoreSupported {z | t≤‖z-y‖}) (hos : T.OutSupported (Metric.closedBall y (t+b)))
    (F : (p : T.index) → Spins (T.out p) → Configuration (T.out p) → ℝ)
    (hFm : ∀ p s, AEStronglyMeasurable (F p s) volume)
    (hF0 : ∀ p s, ∀ᵐ x, 0≤F p s x)
    (hFi : ∀ p s, Integrable (fun x => mass ((T.vector p).coreSlice s x)*(F p s x)^2))
    (hcap : ∀ p s, ∀ᵐ x, ∀ w∈Metric.closedBall y (t+b), coreScreenedField S ((T.vector p).coreSlice s x).normalized w≤F p s x) :
    let Q := ∑ p, sliceExpectation (T.vector p) (fun s x => (F p s x)^2)
    let N := ∑ p, (T.out p:ℝ)^2*mass (T.vector p)
    localCountSecondMoment ψ (Metric.closedBall y a)≤2*(tfInteriorCountConstant/a^3)^2+
      6*a*(max countTestEnergy 0)*(B+12*a*unitWindowKinetic/b^2*Real.sqrt Q+
        Real.sqrt (Q*T.deletedSquare y t b)+
        (b⁻¹)^2*((Real.pi^2/2)*neumannBoundary)*N^(2/3:ℝ)+
        ((2*Real.pi+1)/(2*b))*Real.sqrt N) := by
  dsimp only
  let ρ := fun p s x => localTFDensity measurableSet_ball
    (coreTFField S ((T.vector p).coreSlice s x).normalized measurableSet_ball ha
      (patch_nucleus_separation S ha hb ht.2 y hn))
  let G := fun p s x => rawThomasFermiEnergy (coreScreenedField S ((T.vector p).coreSlice s x).normalized)
    (retainedFineDensity b (patchRetained y t b x) (position x))-
    rawThomasFermiEnergy (coreScreenedField S ((T.vector p).coreSlice s x).normalized) (ρ p s x)
  have hcs' (p : T.index) (s) : ∀ᵐ x, SpatiallySupported ((T.vector p).coreSlice s x).normalized {z | t≤‖z-y‖} := by
    filter_upwards [(hcs p).coreSlice s] with x hx
    exact hx.normalized
  have hcap' (p : T.index) (s) : ∀ᵐ x, ∀ w∈Metric.ball y (t-4*b), coreScreenedField S ((T.vector p).coreSlice s x).normalized w≤F p s x := by
    filter_upwards [hcap p s] with x hx
    exact fun w hw => hx w (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith)) hw)
  have hgap (p : T.index) := physical_patch_comparison S (T.vector p) (ho p).outer_symmetry
    (fun s => (hc p).coreSlice s) ha hb hsmall ht y hn (hcs' p) (fun s => (hos p).recorded_positions s)
    (F p) (hFm p) (hF0 p) (hFi p) (hcap p) hE
  have hpacket (p : T.index) := patch_packet_expected_bound S (T.vector p) ha hb ht.2 y hn
    (F p) (hFm p) (hF0 p) (hFi p) (hcap' p)
  have hmean := slice_ensemble_mean_le_sqrt T.out T.core T.vector F hFm hF0 hFi hm
  have hdel := slice_ensemble_mul_le_sqrt T.out T.core T.vector F
    (fun _ _ x => localCount {z | t-7*b≤‖z-y‖} x) hFi
    (fun p s => sliceCount_weight_integrable (T.vector p) (isClosed_le continuous_const (by fun_prop)).measurableSet s 2)
    (fun p s => weighted_cap_count_integrable (mass_coreSlice_integrable (T.vector p) s)
      (Eventually.of_forall (fun _ => mass_nonneg _)) (hFm p s) (hF0 p s) (hFi p s)
      (localCount_measurable (isClosed_le continuous_const (by fun_prop)).measurableSet).aestronglyMeasurable
      (Nat.cast_nonneg (T.out p)) (Eventually.of_forall (fun x => ⟨localCount_nonneg _ x,localCount_le _ x⟩)))
  have hfine := ensemble_fineLocalizationError T.out (fun p => mass (T.vector p)) (fun p => mass_nonneg _) hm hb
  have hsumgap := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => hgap p)
  have hsumpacket := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => hpacket p)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum] at hsumgap hsumpacket
  change (∑ p, sliceExpectation (T.vector p) (G p))≤_ at hsumgap
  have hGapBound : (∑ p, sliceExpectation (T.vector p) (G p))≤B+
      12*a*unitWindowKinetic/b^2*Real.sqrt (∑ p, sliceExpectation (T.vector p) (fun s x => (F p s x)^2))+
      Real.sqrt ((∑ p, sliceExpectation (T.vector p) (fun s x => (F p s x)^2))*T.deletedSquare y t b)+
      (b⁻¹)^2*((Real.pi^2/2)*neumannBoundary)*(∑ p, (T.out p:ℝ)^2*mass (T.vector p))^(2/3:ℝ)+
      ((2*Real.pi+1)/(2*b))*Real.sqrt (∑ p, (T.out p:ℝ)^2*mass (T.vector p)) := by
    have hp := mul_le_mul_of_nonneg_left hmean (show 0≤12*a*unitWindowKinetic/b^2 by exact div_nonneg (mul_nonneg (by positivity) unitWindowKinetic_nonneg) (sq_nonneg _))
    change (∑ p, mass (T.vector p))=1 at hm
    rw [hm,mul_one] at hsumgap
    change (∑ p, form S (T.vector p))≤E+B at henergy
    unfold RecordedEnsemble.deletedSquare
    linarith
  have hAB : Disjoint {z : Space | t≤‖z-y‖} (Metric.closedBall y a) := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    have hh : ‖z-y‖≤a := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz'
    have hz : t≤‖z-y‖ := hz
    linarith [ht.1]
  rw [←hC.recorded_secondMoment_eq measurableSet_closedBall hAB hcs]
  have hcounts := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => physical_patch_averaged_count S (T.vector p)
    ha hb hsmall ht y hn (hcs' p) (F p) (hF0 p) (hFi p) (hcap p))
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hcounts
  change (∑ p, mass (T.vector p))=1 at hm
  rw [hm,mul_one] at hcounts
  have hcoef : 0≤6*a*max countTestEnergy 0 := mul_nonneg (mul_nonneg (by norm_num) ha.le) (le_max_right _ _)
  exact hcounts.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hGapBound hcoef))

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

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
namespace Coulomb

theorem atomic_physical_count_comparison {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hm : mass ψ=1)
    {E δ : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S) (hstate : form S ψ≤E+δ)
    (hδ : 0≤δ) {y : Space} (hy : y≠0) {b : ℝ} (hb : 0<b)
    (hsmall : 18*b≤atomicCellScale y)
    (hcond : atomicCellScale y≤b^2*Real.sqrt (screenCountParameter ψ δ)*screenMass δ (atomicCellScale y)) :
    localCountSecondMoment ψ (Metric.closedBall y (atomicCellScale y))≤
      atomicComparisonExpression δ (screenCountParameter ψ δ) (atomicCellScale y) b := by
  let a := atomicCellScale y
  let P := screenCountParameter ψ δ
  let m := screenMass δ a
  have ha : 0<a := atomicCellScale_pos hy
  have hP1 : 1≤P := screenCountParameter_ge_one ψ δ
  have hP : 0≤P := le_trans zero_le_one hP1
  have hm0 : 0 < m := screenMass_pos δ a
  have hc := fun z hz => screenCountParameter_controls ψ hm δ (y:=z) hz
  obtain ⟨t,ht,T,hEt,ho,hcs,hos,hD,hN,hraw⟩ :=
    exists_atomic_thin_screened_sharp S hatom ψ hψ hm hE hstate hδ hy hb hsmall hcond
  let F := fun p s x => atomicPatchCap S ((T.ensemble.vector p).coreSlice s x).normalized x y
  let Q := ∑ p, sliceExpectation (T.ensemble.vector p) (fun s x => (F p s x)^2)
  let N := ∑ p, (T.ensemble.out p:ℝ)^2*mass (T.ensemble.vector p)
  have hN0 : 0≤N := Finset.sum_nonneg (fun p _ => mul_nonneg (sq_nonneg _) (mass_nonneg _))
  have hD0 : 0≤T.ensemble.deletedSquare y t b := Finset.sum_nonneg (fun p _ =>
    Finset.sum_nonneg (fun s _ => integral_nonneg (fun x => mul_nonneg (mass_nonneg _) (sq_nonneg _))))
  have hwidth : t+b≤80*a := by dsimp only [a] at *; linarith [ht.2]
  have hgap : T.ensemble.totalForm S≤E+(δ+thinIMS ψ y t b) := by linarith
  have hQ : Q≤atomicPhysicalCapConstant*P*m^2/a^2 := by
    have HQ := atomicPatchCap_ensemble_square S hatom T.ensemble hy
      (H := (2*atomicBudgetRecursionC^3*Real.sqrt thinReserveFactor*screenFieldUnit δ P a)^2)
      (fun v hv => (Real.sqrt_le_iff.mp (hraw v hv)).2)
    change Q≤_ at HQ
    calc
      Q≤16*(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*
        (2*atomicBudgetRecursionC^3*Real.sqrt thinReserveFactor*screenFieldUnit δ P a)^2+8*N/(9*a^2) := HQ
      _≤16*(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*
        (2*atomicBudgetRecursionC^3*Real.sqrt thinReserveFactor*screenFieldUnit δ P a)^2+
        8*(atomicPatchCountFactor*P*m^2)/(9*a^2) := add_le_add le_rfl
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hN (by norm_num)) (by positivity))
      _=atomicPhysicalCapConstant*P*m^2/a^2 := by
        dsimp only [atomicPhysicalCapConstant,screenFieldUnit,m]
        simp only [mul_pow,div_pow,Real.sq_sqrt hP]
        ring
  have hQ0 : 0≤atomicPhysicalCapConstant*P*m^2/a^2 := by positivity [atomicPhysicalCapConstant_nonneg]
  have hn (j) : 20*a≤‖S.position j-y‖ := by
    rw [hatom j,zero_sub,norm_neg]
    dsimp only [a,atomicCellScale]
    nlinarith [norm_nonneg y]
  have hH := physical_ensemble_count S ψ T.ensemble T.law T.fermionic ho
    (T.mass_eq.trans hm) hE hgap ha hb hsmall ht y hn hcs hos F
    (fun p s => atomicPatchCap_slice_aestronglyMeasurable S (T.ensemble.vector p) s y)
    (fun p s => Eventually.of_forall (fun x => atomicPatchCap_nonneg S _ x hy))
    (fun p s => atomicPatchCap_weight_integrable S hatom (T.ensemble.vector p) s hy)
    (fun p s => Eventually.of_forall (fun x w hw => coreField_le_atomicPatchCap S hatom _ x hy
      ((show ‖w-y‖≤t+b from by simpa only [Metric.mem_closedBall,dist_eq_norm] using hw).trans hwidth)))
  change localCountSecondMoment ψ (Metric.closedBall y a)≤_ at hH
  apply hH.trans
  unfold atomicComparisonExpression
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg (by norm_num) ha.le) (le_max_right _ _))
  have hB := thinIMS_sharp_budget ψ hm hδ hP hc hy hb hwidth
  have hp := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hQ)
    (show 0≤12*a*unitWindowKinetic/b^2 from div_nonneg (mul_nonneg (by positivity) unitWindowKinetic_nonneg) (sq_nonneg _))
  have hd := Real.sqrt_le_sqrt (mul_le_mul hQ hD hD0 hQ0)
  have hf := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hN0 hN (by norm_num : (0:ℝ)≤2/3))
    (show 0≤(b⁻¹)^2*((Real.pi^2/2)*neumannBoundary) by positivity [neumannBoundary_nonneg])
  have hn' := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hN)
    (show 0≤(2*Real.pi+1)/(2*b) by positivity [Real.pi_pos])
  dsimp only [Q,N,m,a,P] at hp hd hf hn' hB ⊢
  linarith

end Coulomb

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

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

theorem atomic_screenCountParameter_uniform : ∃ P₀ : ℝ, 2 ≤ P₀ ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ i, S.position i=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E δ : ℝ}, (E:EReal) ≤ unrestrictedFormBottom S → form S ψ ≤ E+δ → 0 ≤ δ →
      screenCountParameter ψ δ ≤ P₀ := by
  obtain ⟨β,P₀,hβ,hβsmall,hP₀,hthreshold⟩ := countBootstrap_threshold
  refine ⟨P₀,hP₀,?_⟩
  intro J n S hatom ψ hψ hm E δ hE hstate hδ
  by_contra hbound
  have hPbig : P₀ < screenCountParameter ψ δ := lt_of_not_ge hbound
  let P := screenCountParameter ψ δ
  have hP2 : 2 ≤ P := hP₀.trans hPbig.le
  have hP := screenCountParameter_ge_one ψ δ
  obtain ⟨hcondP,himp⟩ := hthreshold P hPbig.le
  have hbetter : screenCountParameter ψ δ ≤ P/2 := by
    apply screenCountParameter_le_of ψ δ (by dsimp [P] at *; linarith)
    intro y hy
    let a := atomicCellScale y
    have ha : 0 < a := atomicCellScale_pos hy
    have hb : 0 < β*a := mul_pos hβ ha
    have hs : 18*(β*a) ≤ a := by nlinarith [mul_le_mul_of_nonneg_right hβsmall ha.le]
    have hcond : a ≤ (β*a)^2*Real.sqrt P*screenMass δ a := by
      have H := mul_le_mul hcondP (screenMass_scale δ ha) (by norm_num : (0:ℝ)≤1)
        (mul_nonneg (sq_nonneg β) (Real.sqrt_nonneg P))
      have H' := mul_le_mul_of_nonneg_left H ha.le
      nlinarith
    have H := atomic_physical_count_comparison S hatom ψ hψ hm hE hstate hδ hy hb hs hcond
    exact H.trans ((atomicComparisonExpression_le_majorant hδ (by linarith) ha hβ).trans
      (mul_le_mul_of_nonneg_right himp (sq_nonneg _)))
  dsimp [P] at hbetter hP2
  linarith

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_UniformCountConsequences
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

def atomicCountConstant : ℝ := Classical.choose atomic_screenCountParameter_uniform
lemma atomicCountConstant_ge_two : 2 ≤ atomicCountConstant :=
  (Classical.choose_spec atomic_screenCountParameter_uniform).1

theorem screenCountParameter_le_atomicCountConstant {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hm : mass ψ=1)
    {E δ : ℝ} (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ)
    (hδ : 0 ≤ δ) : screenCountParameter ψ δ ≤ atomicCountConstant :=
  (Classical.choose_spec atomic_screenCountParameter_uniform).2 S hatom ψ hψ hm hE hstate hδ

theorem atomic_annular_second_moment {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {J n : ℕ} (S : Nuclei J), (∀ i, S.position i=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E δ : ℝ}, (E:EReal) ≤ unrestrictedFormBottom S → form S ψ ≤ E+δ → 0 ≤ δ →
    ∀ {u : ℝ}, 0 < u →
      localCountSecondMoment ψ {x : Space | α*u < ‖x‖ ∧ ‖x‖ < β*u} ≤ C*(screenMass δ u)^2 := by
  obtain ⟨t,ht,hcover⟩ := exists_atomic_annular_mesh (β:=β) hα
  let q : ℝ := max 1 (max (100000/α) (β/100000))
  have hq : 1 ≤ q := le_max_left _ _
  have hqα : 100000/α ≤ q := (le_max_left _ _).trans (le_max_right _ _)
  have hqβ : β/100000 ≤ q := (le_max_right _ _).trans (le_max_right _ _)
  have hq0 : 0 < q := (div_pos (hα.trans hαβ) (by norm_num)).trans_le hqβ
  let C : ℝ := (Fintype.card {z : Space // z∈t}:ℝ)^2*atomicCountConstant*q^6
  have hC0 : 0 ≤ atomicCountConstant := by linarith [atomicCountConstant_ge_two]
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro J n S hatom ψ hψ hm E δ hE hstate hδ u hu
  let A := fun z : {z : Space // z∈t} => Metric.closedBall (u • z.val) (atomicCellScale (u • z.val))
  have hz0 (z : {z : Space // z∈t}) : z.val≠0 := by
    intro he; have H:=(ht z.val z.property).1; simpa [he] using hα.trans_le H
  have hmz (z : {z : Space // z∈t}) : screenMass δ (atomicCellScale (u • z.val)) ≤ q^3*screenMass δ u := by
    apply screenMass_comparable hδ hu hq
    · rw [atomicCellScale_smul hu.le]
      apply (div_le_iff₀ hq0).mpr
      have H := (div_le_iff₀ hα).mp hqα
      have Hz := mul_le_mul_of_nonneg_left (ht z.val z.property).1 hq0.le
      dsimp only [atomicCellScale]
      nlinarith
    · rw [atomicCellScale_smul hu.le]
      apply mul_le_mul_of_nonneg_left _ hu.le
      exact (div_le_div_of_nonneg_right (ht z.val z.property).2 (by norm_num)).trans hqβ
  have hA : {x : Space | α*u < ‖x‖ ∧ ‖x‖ < β*u} ⊆ ⋃ z, A z := by
    intro x hx
    have hn : ‖u⁻¹ • x‖=‖x‖/u := by simp [norm_smul,abs_of_pos hu,div_eq_mul_inv,mul_comm]
    have hlow : α ≤ ‖u⁻¹ • x‖ := by rw [hn]; exact (le_div_iff₀ hu).mpr hx.1.le
    have hhigh : ‖u⁻¹ • x‖ ≤ β := by rw [hn]; exact (div_le_iff₀ hu).mpr hx.2.le
    obtain ⟨z,hz,hxz⟩ := hcover (u⁻¹ • x) hlow hhigh
    refine Set.mem_iUnion.mpr ⟨⟨z,hz⟩,?_⟩
    change ‖x-u • z‖ ≤ atomicCellScale (u • z)
    rw [atomicCellScale_smul hu.le]
    have hid : x-u • z=u • (u⁻¹ • x-z) := by simp [smul_sub,smul_smul,hu.ne']
    rw [hid,norm_smul,Real.norm_eq_abs,abs_of_pos hu]
    exact mul_le_mul_of_nonneg_left hxz.le hu.le
  have H := localCountSecondMoment_cover ψ A (fun _ => measurableSet_closedBall) hA
  have Hc (z : {z : Space // z∈t}) : localCountSecondMoment ψ (A z) ≤
      atomicCountConstant*(q^3*screenMass δ u)^2 := by
    have H0 := (screenCountParameter_controls ψ hm δ (smul_ne_zero hu.ne' (hz0 z))).trans
      (mul_le_mul_of_nonneg_right (screenCountParameter_le_atomicCountConstant S hatom ψ hψ hm hE hstate hδ) (sq_nonneg _))
    exact H0.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (screenMass_pos δ _).le (hmz z) 2) hC0)
  apply H.trans
  have HH := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun z (_ : z∈Finset.univ) => Hc z))
    (show 0 ≤ (Fintype.card {z : Space // z∈t}:ℝ) by positivity)
  apply HH.trans_eq
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,C]
  ring

end Coulomb
end

end
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

def atomicPatchTFGap {J n : ℕ} (S : Nuclei J) (hatom : ∀ i, S.position i=0)
    (T : RecordedEnsemble n) (y : Space) (hy : y≠0) (b : ℝ) (hb : 0<b)
    (t : ℝ) (ht : t≤6*atomicCellScale y) : ℝ :=
  ∑ p, sliceExpectation (T.vector p) (fun s x =>
    let Φ := coreScreenedField S ((T.vector p).coreSlice s x).normalized
    let ρ := localTFDensity measurableSet_ball
      (coreTFField S ((T.vector p).coreSlice s x).normalized measurableSet_ball
        (atomicCellScale_pos hy)
        (patch_nucleus_separation S (atomicCellScale_pos hy) hb ht y
          (atomic_patch_nucleus_distance S hatom y)))
    rawThomasFermiEnergy Φ (retainedFineDensity b (patchRetained y t b x) (position x))-
    rawThomasFermiEnergy Φ ρ)

end Coulomb
end

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

def atomicKineticConstant : ℝ := 1+2*thinReserveFactor*Real.sqrt atomicCountConstant+
  2*(atomicPhysicalCapConstant+atomicPatchCountFactor)*atomicCountConstant

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_AtomicNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

def atomicNearConstant : ℝ := fermionicNearConstant*(atomicKineticConstant+1)
end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TFOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology ContDiff
namespace Coulomb

def patchTFScreenedField {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : t ≤ 6*a) (y : Space)
    (hn : ∀ j, 20*a ≤ ‖S.position j-y‖) (z : Space) : ℝ :=
  coreScreenedField S u z-tfPotential (localTFMinimizer measurableSet_ball
    (coreTFField S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht y hn))) z

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_PatchNegativeCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

def patchSliceTFGap {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
    (hn : ∀ j, 20*a≤‖S.position j-y‖) (s : Spins m) (x : Configuration m) : ℝ :=
  rawThomasFermiEnergy (coreScreenedField S (u.coreSlice s x).normalized)
    (retainedFineDensity b (patchRetained y t b x) (position x))-
  rawThomasFermiEnergy (coreScreenedField S (u.coreSlice s x).normalized)
    (localTFDensity measurableSet_ball (coreTFField S (u.coreSlice s x).normalized
      measurableSet_ball ha (patch_nucleus_separation S ha hb ht y hn)))

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CorePointMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

def patchFieldTransferError {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
    (hn : ∀ j,20*a≤‖S.position j-y‖) (s : Spins m) (x : Configuration m) : ℝ :=
  (coreScreenedField S (u.coreSlice s x).normalized y-nuclearPotential (unitNucleus y) x)-
    patchTFScreenedField S (u.coreSlice s x).normalized ha hb ht y hn y

def patchTransferRemainder {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
    (hn : ∀ j,20*a≤‖S.position j-y‖) (r ε : ℝ) (s : Spins m) (x : Configuration m) : ℝ :=
  ε+(5/(4*r*ε))*patchSliceTFGap S u ha hb ht y hn s x+
    nearPotential y (r+2*b) x+nearPotential y (2*b) x+
    localCount {z | t-7*b≤‖z-y‖} x/a+
    ((tfInteriorConstant thomasFermiKineticConstant/
      (thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)/a^6)*(2*Real.pi*r^2)

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_AtomicWeightGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical
noncomputable section
namespace Coulomb
def atomicFraction (e:ℝ) (x:Space):ℝ:=coulombKernel x*atomicWeight e x
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FreshTransferScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

def atomicPatchMeanField {J n : ℕ} (S : Nuclei J) (hatom : ∀ i,S.position i=0)
    (T : RecordedEnsemble n) (y : Space) (hy : y≠0) (b : ℝ) (hb : 0<b)
    (t : ℝ) (ht : t≤6*atomicCellScale y) : ℝ :=
  ∑ p,sliceExpectation (T.vector p) (fun s x =>
    patchTFScreenedField S ((T.vector p).coreSlice s x).normalized
      (atomicCellScale_pos hy) hb ht y (atomic_patch_nucleus_distance S hatom y) y)

def atomicTransferConstant : ℝ := 7/2+2*atomicNearConstant*3^(1/5:ℝ)+
  Real.sqrt (72*atomicPatchCountFactor*atomicCountConstant)+
  2*Real.pi*(tfInteriorConstant thomasFermiKineticConstant/
    (thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)

end Coulomb

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

theorem atomic_radial_tail_uniform : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ i, S.position i=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E δ : ℝ}, (E:EReal) ≤ unrestrictedFormBottom S → form S ψ ≤ E+δ → 0 ≤ δ →
    ∀ {h : ℝ}, 0 < h → radialTailPotential ψ h ≤ C*screenMass δ h/h := by
  obtain ⟨C,hC,H⟩ := atomic_annular_second_moment (α:=(1/2:ℝ)) (β:=4) (by norm_num) (by norm_num)
  refine ⟨4*Real.sqrt C,by positivity,?_⟩
  intro J n S hatom ψ hψ hm E δ hE hstate hδ h hh
  have hmean {r : ℝ} (hr : 0 < r) :
      expectedPopulation ψ {z : Space | (1/2:ℝ)*r < ‖z‖ ∧ ‖z‖ < 4*r} ≤ Real.sqrt C*screenMass δ r := by
    have hA : MeasurableSet {z : Space | (1/2:ℝ)*r < ‖z‖ ∧ ‖z‖ < 4*r} :=
      (isOpen_lt continuous_const continuous_norm).measurableSet.inter (isOpen_lt continuous_norm continuous_const).measurableSet
    have hs := (expectedPopulation_sq_le ψ hA hm).trans (H S hatom ψ hψ hm hE hstate hδ hr)
    rw [←Real.sq_sqrt hC,←mul_pow] at hs
    exact (sq_le_sq₀ (expectedPopulation_nonneg _ _) (mul_nonneg (Real.sqrt_nonneg _) (screenMass_pos _ _).le)).mp hs
  let K : ℝ := Real.sqrt C*screenMass δ h/h
  have hK : 0 ≤ K := by exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (screenMass_pos _ _).le) hh.le
  have hstep (j : ℕ) : radialTailPotential ψ ((2:ℝ)^j*h) ≤ K*(3/4:ℝ)^j+
      radialTailPotential ψ ((2:ℝ)^(j+1)*h) := by
    have hr : 0 < (2:ℝ)^j*h := by positivity
    have H1 := div_le_div_of_nonneg_right (hmean hr) hr.le
    have H2 := mul_le_mul_of_nonneg_left (screenMass_dyadic_bound hδ hh j) (Real.sqrt_nonneg C)
    have H3 : expectedPopulation ψ {z : Space | (1/2:ℝ)*((2:ℝ)^j*h) < ‖z‖ ∧ ‖z‖ < 4*((2:ℝ)^j*h)}/((2:ℝ)^j*h) ≤ K*(3/4:ℝ)^j := by
      calc
        _ ≤ Real.sqrt C*screenMass δ ((2:ℝ)^j*h)/((2:ℝ)^j*h) := H1
        _ ≤ K*(3/4:ℝ)^j := by simpa only [K,mul_div_assoc,mul_assoc] using H2
    have He : 2*((2:ℝ)^j*h)=(2:ℝ)^(j+1)*h := by rw [pow_succ]; ring
    exact (radialTailPotential_step ψ hr).trans (by rw [He]; exact add_le_add H3 le_rfl)
  have hfinite (N : ℕ) : radialTailPotential ψ h ≤
      K*(∑ j∈Finset.range N, (3/4:ℝ)^j)+radialTailPotential ψ ((2:ℝ)^N*h) := by
    induction N with
    | zero => simp
    | succ N ih =>
      have HS := add_le_add (le_refl (K*∑ j∈Finset.range N, (3/4:ℝ)^j)) (hstep N)
      refine ih.trans (HS.trans_eq ?_)
      rw [Finset.sum_range_succ]
      ring
  have hbound (N : ℕ) : radialTailPotential ψ h ≤ 4*K+((n:ℝ)/h)*(1/2:ℝ)^N := by
    have hs : (∑ j∈Finset.range N, (3/4:ℝ)^j) ≤ 4 := by
      have HH := geom_sum_mul_neg (3/4:ℝ) N
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 3/4) N]
    have ht := radialTailPotential_cap ψ (show 0 < (2:ℝ)^N*h by positivity)
    rw [hm,mul_one] at ht
    have he : (n:ℝ)/((2:ℝ)^N*h)=((n:ℝ)/h)*(1/2:ℝ)^N := by
      rw [div_pow,one_pow]
      field_simp
    exact (hfinite N).trans (by rw [←he]; nlinarith [mul_le_mul_of_nonneg_left hs hK])
  have hlim : Tendsto (fun N : ℕ => 4*K+(n:ℝ)/h*(1/2:ℝ)^N) atTop (𝓝 (4*K)) := by
    convert tendsto_const_nhds.add (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1))) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have Hfinal := ge_of_tendsto' hlim hbound
  dsimp [K] at Hfinal
  exact Hfinal.trans_eq (by ring)

def atomicTailConstant : ℝ := Classical.choose atomic_radial_tail_uniform

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_UpperDeficit
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

def atomicInnerFieldConstant : ℝ :=
  2*atomicBudgetRecursionC^2*Real.sqrt atomicCountConstant*(100000:ℝ)^4+2501*atomicTailConstant

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PhysicalDeficitTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators Classical
noncomputable section
namespace NeutralAtom

def observedDeficitCoefficient {J : ℕ} (ℓ : Fin J → ℝ) (D r : ℝ) : ℝ :=
  2*Coulomb.atomicInnerFieldConstant*(Coulomb.screenBaseMass r+
    Real.sqrt ((D+observationEventEnergyConstant*observationWidthSquareSum ℓ)*r))+1

end NeutralAtom

end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_ScaledFieldCap
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

def physicalFieldCapUnit : ℝ :=
  2*Coulomb.atomicBudgetRecursionC^2*Real.sqrt Coulomb.atomicCountConstant*100000^4
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_PhysicalCapMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

def physicalFieldCapBase : ℝ := max 1 (2*physicalFieldCapUnit)
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PosteriorSpatialCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

def physicalSpatialCap : ℝ := 32*physicalFieldCapBase+1
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_CoreMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom

def fixedCoreMomentBound (t : ℝ) : ℝ :=
  1+(observedDeficitCoefficient (fun _ : Fin 1 => t/16) 0 (t/4))^2+
    ∑' k : ℕ, (observedDeficitCoefficient (fun _ : Fin 1 => t/16) 0 (t/4)*
      (1+((k+1:ℕ):ℝ))^3)^2*Real.exp (-(k:ℝ))

end NeutralAtom
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

structure QuantumProfileDatum {N : ℕ} (ψ : Wavefunction (N+1)) [IsProbabilityMeasure (rawLaw ψ)]
    (ε B C L M s q Cq : ℝ) where
  j : ℕ
  low : s/(2*q) ≤ profileRadius ε N j
  high : profileRadius ε N j ≤ s/q
  datum : PropagationDatum (observationLaw (j+1) (rawLaw ψ)) B C (profileRadius ε N j)
    ((N+1:ℕ):ℝ) L (profileDensity ψ ε s j)
  G : Set (ObservationSample (N+1) (j+1))
  measurable : MeasurableSet G
  failure : (observationLaw (j+1) (rawLaw ψ)).real Gᶜ ≤ M*s^9+Cq*s^25
  valid : ∀ o∈G,PropagationInvariant B C (profileRadius ε N j) ((N+1:ℕ):ℝ) L
    (datum.offset o) (profileDensity ψ ε s j o) (datum.error o) ∧
    Integrable (datum.error o) ∧ (∫ x,datum.error o x) ≤ 1
  band : ∀ o∈G,∀ x,profileRadius ε N j ≤ ‖x‖ → ‖x‖ ≤ q*s →
    screenedField ((N+1:ℕ):ℝ) (profileDensity ψ ε s j o) x ≤ physicalSpatialCap/‖x‖^4 ∧
    |profileDensity ψ ε s j o x-tfDensityScalar (screenedField ((N+1:ℕ):ℝ)
      (profileDensity ψ ε s j o) x)| ≤ (q^8)⁻¹/‖x‖^6

end NeutralAtom
end

end

end OAI
end


