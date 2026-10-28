-- Prove2me | Definitions.Def_OAIQ071C008
-- name    : OAIQ071C008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T05:16:35.694543+00:00
-- url     : https://prove2.me/theorems/f7ae59e3-d65f-42ed-b4b8-f89f63faaaaf
-- title:
--   Definitions bundle OAIQ071C008 of the split of OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 274 declarations of OpenAI's Lean: 43 definitions, 1 inductive type or structure and 230 theorems. The definitions and types are `OAI.CoulombAtom.CoreObservationEnsemble.fullAverage`, `OAI.CoulombAtom.CoreObservationEnsemble.innerCapAverage`, `OAI.CoulombAtom.CoreObservationEnsemble.outMoment`, `OAI.CoulombAtom.CoreObservationEnsemble.weightedMoment`, `OAI.CoulombAtom.CoreObservationGraph.fullAverage`, `OAI.CoulombAtom.CoreObservationGraph.innerCapAverage`, `OAI.CoulombAtom.CoreObservationGraph.outMoment`, `OAI.CoulombAtom.CoreObservationGraph.weightedMoment`, `OAI.CoulombAtom.FullStatistic`, `OAI.CoulombAtom.SmoothMultiplier.oneBody`, `OAI.CoulombAtom.actualInnerBoundaryCap`, `OAI.CoulombAtom.actualInnerSource`, `OAI.CoulombAtom.actualParticleSource`, `OAI.CoulombAtom.bindingMultiplier`, `OAI.CoulombAtom.bindingRoot`, `OAI.CoulombAtom.bindingTotalMultiplier`, `OAI.CoulombAtom.closedRawInnerField`, `OAI.CoulombAtom.closedShellField`, `OAI.CoulombAtom.conditionalBlockMaximum`, `OAI.CoulombAtom.conditionalOutMaximum`, `OAI.CoulombAtom.coulombTailWeight`, `OAI.CoulombAtom.cutExteriorPrice`, `OAI.CoulombAtom.freshOutMaximumSecondMoment`, `OAI.CoulombAtom.fullSlicePair`, `OAI.CoulombAtom.innerCapStatistic`, `OAI.CoulombAtom.innerFieldVolume`, `OAI.CoulombAtom.innerParticleWeight`, `OAI.CoulombAtom.localFieldEnvelope`, `OAI.CoulombAtom.localFieldUniversalConstant`, `OAI.CoulombAtom.localHistoryFieldValues`, `OAI.CoulombAtom.oneBodyGradientError`, `OAI.CoulombAtom.oneBodySquareTotal`, `OAI.CoulombAtom.radialCutExcessConstant`, `OAI.CoulombAtom.radialOutLinearConstant`, `OAI.CoulombAtom.radialPatchGapMean`, `OAI.CoulombAtom.rawOneParticleLaw`, `OAI.CoulombAtom.rawWeightedCount`, `OAI.CoulombAtom.rawWeightedMoment`, `OAI.CoulombAtom.shellMeanField`, `OAI.CoulombAtom.shellMeanStatistic` and 4 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CoulombIonization_Fermionic_CorePotentialTower`, `CoulombIonization_Fermionic_CutCountDomination`, `CoulombIonization_Fermionic_Sum`, `CoulombIonization_Fermionic_WeightedCoreStatistics`, `CoulombIonization_FieldAnalysis_ConditionalFieldIdentity`, `CoulombIonization_FieldAnalysis_ConditionalShellField`, `CoulombIonization_FieldAnalysis_CoreHistoryFieldBarrier`, `CoulombIonization_FieldAnalysis_CoreSubmeanSquareBarrier`, `CoulombIonization_FieldAnalysis_DeletedFieldBudget`, `CoulombIonization_FieldAnalysis_FreshFieldTower`, `CoulombIonization_FieldAnalysis_InnerCapStatistic`, `CoulombIonization_FieldAnalysis_InnerFieldCap`, `CoulombIonization_FieldAnalysis_LocalFieldBootstrapBarrier`, `CoulombIonization_FieldAnalysis_LocalFieldEnvelopeBarrier`, `CoulombIonization_FieldAnalysis_LocalFieldScalarBoundBarrier`, `CoulombIonization_FieldAnalysis_OutMaximumSubmeanBarrier`, `CoulombIonization_FieldAnalysis_OuterFieldMaximum`, `CoulombIonization_FieldAnalysis_PatchMassSubmeanBarrier`, `CoulombIonization_FieldAnalysis_QuantumFieldExcessBarrier`, `CoulombIonization_FieldAnalysis_ShellMeanStatistic`, `CoulombIonization_FieldAnalysis_ThinFieldFeedbackBarrier`, `CoulombIonization_FormDomain_BlockEnergetics`, `CoulombIonization_FormDomain_CoreKinetic`, `CoulombIonization_FormDomain_FormRawPotential`, `CoulombIonization_FormDomain_Forms`, `CoulombIonization_FormDomain_InnerLinearCap`, `CoulombIonization_FormDomain_Restriction`, `CoulombIonization_FormDomain_ShiftedCoulombIntegrable`, `CoulombIonization_Ionization_CoreHistoryFieldFubiniBarrier`, `CoulombIonization_Ionization_SharpJointComparisonBarrier`, `CoulombIonization_Localization_ConditionalRetainedGap`, `CoulombIonization_Localization_CoreHistoryAverageBarrier`, `CoulombIonization_Localization_CoreHistoryMassBarrier`, `CoulombIonization_Localization_CoreHistoryOutMaximumBarrier`, `CoulombIonization_Localization_CoreObservationEnsembleBarrier`, `CoulombIonization_Localization_FiniteCellObservation`, `CoulombIonization_Localization_FormRawLaw`, `CoulombIonization_Localization_ObservedInnerCap`, `CoulombIonization_Localization_OrdinaryDensity`, `CoulombIonization_Localization_PacketComparison`, `CoulombIonization_RadialBounds_ArbitraryCutExcess`, `CoulombIonization_RadialBounds_BallAverageKernelBarrier`, `CoulombIonization_RadialBounds_CoreHistoryCountsBarrier`, `CoulombIonization_RadialBounds_CoreSubmeanBarrier`, `CoulombIonization_RadialBounds_CoulombTailNumerics`, `CoulombIonization_RadialBounds_CoulombTailStatistic`, `CoulombIonization_RadialBounds_CoupledCoreExcessBarrier`, `CoulombIonization_RadialBounds_LocalHistoryWeightsBarrier`, `CoulombIonization_RadialBounds_RadialCountSelection`, `CoulombIonization_RadialBounds_RadialPatchGeometry`, `CoulombIonization_RadialBounds_RadialSelectedCounts`, `CoulombIonization_RadialBounds_RootMomentCauchyBarrier`, `CoulombIonization_RadialBounds_SelectionNumerics`, `CoulombIonization_RadialBounds_dShellForm`, `CoulombIonization_Variational_ClosedInnerStatistic`, `CoulombIonization_Variational_CutCoreExcess`, `CoulombIonization_Variational_CutCoreNumber`, `CoulombIonization_Variational_CutExpectedOut`, `CoulombIonization_Variational_FullSliceStatistics`, `CoulombIonization_Variational_Inner`, `CoulombIonization_Variational_IntegrableCutTower`, `CoulombIonization_Variational_Spatial`, `CoulombIonization_Variational_SpatialErrorWeight`, `CoulombIonization_Variational_Weighted`.
--
--   **Imports.** It imports the published bundle `Def_CoulombIonization`; the bundles `OAIQ071C006` and `OAIQ071C007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ071C010` and `OAIQ071C012`; the proof of `OAI.CoulombAtom.actual_priced_particle_bound_three`.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C006
import Definitions.Def_OAIQ071C007

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_ShiftedCoulombIntegrable
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

namespace CoulombAtom

lemma coreSlice_mass_shifted_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (i : Fin M) (y : Space) :
    Integrable (fun u : Configuration M => formMass (coreSlice ψ s u)/‖u i-y‖) := by
  have he (u : Configuration M) : formMass (coreSlice ψ s u)/‖u i-y‖ =
      ∑ t : Spins N, ∫ v : Configuration N,
        ‖ψ.value (joinLists t s) (joinLists v u)‖^2/‖u i-y‖ := by
    simp only [formMass,Finset.sum_div,integral_div,coreSlice]
  simp_rw [he]
  apply integrable_finsetSum
  intro t _
  have hh := (integrable_join (N := N) (M := M)
    (hψ.shifted_nuclear_integrable (joinLists t s) (finSumFinEquiv (Sum.inr i)) y)).integral_prod_right
  simpa only [joinLists_right] using hh

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_FormRawLaw
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace CoulombAtom
open CoulombRadialAveraging

lemma formRawLaw_univ {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ) :
    formRawLaw ψ univ = ENNReal.ofReal (formMass ψ) := by
  rw [formRawLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal (formRawDensity_integrable hψ)
    (ae_of_all _ (formRawDensity_nonneg ψ))).symm.trans
      (congrArg ENNReal.ofReal (formRawDensity_integral hψ))

lemma formRawLaw_finite {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ) :
    IsFiniteMeasure (formRawLaw ψ) := by
  constructor
  rw [formRawLaw_univ hψ]
  exact ENNReal.ofReal_lt_top

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_Forms
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
section
variable {N : ℕ} {J : Type*} [Fintype J]
variable (p : J → SmoothMultiplier (sectorDirections N))
variable (hp : ∀ x, ∑ j, (p j).value x ^ 2 = 1)
include hp

lemma finite_partition_kinetic {ψ : FormVector N} (hψ : SobolevVector ψ)
    (s : Spins N) (i : Fin N) (a : Fin 3) :
    (∑ j, ∫ x, ‖(multiplyForm (p j) ψ).gradient s i a x‖ ^ 2) =
      (∫ x, ‖ψ.gradient s i a x‖ ^ 2) +
        ∑ j, ∫ x, lineDeriv ℝ (p j).value x (direction i a) ^ 2 *
          ‖ψ.value s x‖ ^ 2 := by
  rw [← integral_finsetSum _ (fun j _ =>
    ((hψ.multiply (p j)).2.1 s i a).norm.integrable_sq)]
  have he : (fun x => ∑ j, ‖(multiplyForm (p j) ψ).gradient s i a x‖ ^ 2) =
      fun x => ‖ψ.gradient s i a x‖ ^ 2 +
        ∑ j, lineDeriv ℝ (p j).value x (direction i a) ^ 2 * ‖ψ.value s x‖ ^ 2 := by
    funext x
    rw [finite_partition_gradient p hp, Finset.sum_mul]
  rw [he, integral_add (hψ.2.1 s i a).norm.integrable_sq
      (integrable_finsetSum _ (fun j _ => smoothMultiplier_gradient_integrable p j hψ s i a)),
    integral_finsetSum _ (fun j _ => smoothMultiplier_gradient_integrable p j hψ s i a)]

lemma finite_partition_div_integral (ψ : FormVector N) (s : Spins N)
    (w : Configuration N → ℝ)
    (hi : ∀ j, Integrable (fun x => ‖(multiplyForm (p j) ψ).value s x‖ ^ 2 / w x)) :
    (∑ j, ∫ x, ‖(multiplyForm (p j) ψ).value s x‖ ^ 2 / w x) =
      ∫ x, ‖ψ.value s x‖ ^ 2 / w x := by
  rw [← integral_finsetSum _ (fun j _ => hi j)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  dsimp only
  rw [← Finset.sum_div, finite_partition_value p hp]

lemma finite_partition_nuclear {ψ : FormVector N} (hψ : SobolevVector ψ)
    (s : Spins N) (i : Fin N) :
    (∑ j, ∫ x, ‖(multiplyForm (p j) ψ).value s x‖ ^ 2 / ‖x i‖) =
      ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i‖ :=
  finite_partition_div_integral p hp ψ s _
    (fun j => (hψ.multiply (p j)).nuclear_integrable s i)

lemma finite_partition_pair {ψ : FormVector N} (hψ : SobolevVector ψ)
    (s : Spins N) (i k : Fin N) (hik : i ≠ k) :
    (∑ j, ∫ x, ‖(multiplyForm (p j) ψ).value s x‖ ^ 2 / ‖x i - x k‖) =
      ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i - x k‖ :=
  finite_partition_div_integral p hp ψ s _
    (fun j => (hψ.multiply (p j)).pair_integrable s i k hik)

theorem finite_partition_energy {ψ : FormVector N} (hψ : SobolevVector ψ) (Z : ℝ) :
    (∑ j, formEnergy Z (multiplyForm (p j) ψ)) =
      formEnergy Z ψ + ∑ j, formMultiplierError (p j) ψ := by
  have hk : (∑ j, ∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
      ∫ x, ‖(multiplyForm (p j) ψ).gradient s i a x‖ ^ 2) =
      (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3, ∫ x, ‖ψ.gradient s i a x‖ ^ 2) +
      ∑ j, ∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        ∫ x, lineDeriv ℝ (p j).value x (direction i a) ^ 2 * ‖ψ.value s x‖ ^ 2 := by
    calc
      _ = ∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
          ∑ j, ∫ x, ‖(multiplyForm (p j) ψ).gradient s i a x‖ ^ 2 := by
        rw [Finset.sum_comm]
        congr 1; funext s
        rw [Finset.sum_comm]
        congr 1; funext i
        rw [Finset.sum_comm]
      _ = _ := by
        simp_rw [finite_partition_kinetic p hp hψ, Finset.sum_add_distrib]
        congr 1
        symm
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro s _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.sum_comm]
  have hn : (∑ j, ∑ s : Spins N, ∑ i : Fin N,
      ∫ x, ‖(multiplyForm (p j) ψ).value s x‖ ^ 2 / ‖x i‖) =
      ∑ s : Spins N, ∑ i : Fin N, ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i‖ := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro s _
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => finite_partition_nuclear p hp hψ s i)
  have hv : (∑ j, ∑ s : Spins N, ∑ i : Fin N, ∑ k : Fin N,
      if i < k then ∫ x, ‖(multiplyForm (p j) ψ).value s x‖ ^ 2 / ‖x i - x k‖ else 0) =
      ∑ s : Spins N, ∑ i : Fin N, ∑ k : Fin N,
        if i < k then ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i - x k‖ else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro s _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    split_ifs with hik
    · exact finite_partition_pair p hp hψ s i k (ne_of_lt hik)
    · simp
  simp only [formEnergy, formMultiplierError, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hk, hn, hv]
  ring

end

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_Spatial
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
section
variable {N : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)

variable (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)
include hp

theorem spatial_cut_energy {ψ : FormVector N} (hψ : SobolevVector ψ) (Z : ℝ) :
    (∑ b : Fin N → Fin 2, formEnergy Z (multiplyForm (spatialProduct p hp b) ψ)) =
      formEnergy Z ψ + ∑ b : Fin N → Fin 2, formMultiplierError (spatialProduct p hp b) ψ :=
  finite_partition_energy (spatialProduct p hp) (spatial_square_partition p hp) hψ Z

end

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CoreKinetic
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
namespace CoulombAtom

lemma integral_core_nuclear {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) :
    (∑ t : Spins M, ∫ y, formNuclear (coreSlice ψ t y)) = coreNuclear ψ := by
  have hi (s : Spins N) (t : Spins M) (i : Fin N) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖(coreSlice ψ t y).value s x‖^2 / ‖x i‖) := by
    have hh := (integrable_join (N := N) (M := M)
      (nuclear_integrable (finSumFinEquiv (Sum.inl i)) (hψ.1 (joinLists s t))
        (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))).integral_prod_right
    simpa only [coreSlice, joinLists_left] using hh
  unfold formNuclear coreNuclear
  simp_rw [integral_finsetSum _ (fun s _ => integrable_finsetSum _ (fun i _ => hi s _ i)),
    integral_finsetSum _ (fun i _ => hi _ _ i)]
  have he (s : Spins N) (t : Spins M) (i : Fin N) :
      (∫ y : Configuration M, ∫ x : Configuration N,
        ‖(coreSlice ψ t y).value s x‖^2 / ‖x i‖) =
      ∫ z, ‖ψ.value (joinLists s t) z‖^2 / ‖z (finSumFinEquiv (Sum.inl i))‖ := by
    simpa only [coreSlice, joinLists_left] using
      integral_join (N := N) (M := M)
        (nuclear_integrable (finSumFinEquiv (Sum.inl i)) (hψ.1 (joinLists s t))
          (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))
  simp_rw [he]
  exact sum_spin_join (N := N) (M := M) (fun u => ∑ i : Fin N,
    ∫ z, ‖ψ.value u z‖^2 / ‖z (finSumFinEquiv (Sum.inl i))‖)

lemma integrated_core_parts {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z : ℝ) :
    (∑ t : Spins M, ∫ y, formEnergy Z (coreSlice ψ t y)) =
      coreKinetic ψ - Z * coreNuclear ψ + coreRepulsion ψ := by
  have he (t : Spins M) : (∫ y, formEnergy Z (coreSlice ψ t y)) =
      (∫ y, formKinetic (coreSlice ψ t y)) - Z * (∫ y, formNuclear (coreSlice ψ t y)) +
      (∫ y, formRepulsion (coreSlice ψ t y)) := by
    simp only [formEnergy_parts]
    rw [integral_add (f := fun y => formKinetic (coreSlice ψ t y) - Z * formNuclear (coreSlice ψ t y))
      (g := fun y => formRepulsion (coreSlice ψ t y)) ((coreSlice_parts_integrable hψ t).1.sub
      ((coreSlice_parts_integrable hψ t).2.1.const_mul Z))
      (coreSlice_parts_integrable hψ t).2.2,
      integral_sub (f := fun y => formKinetic (coreSlice ψ t y))
        (g := fun y => Z * formNuclear (coreSlice ψ t y)) (coreSlice_parts_integrable hψ t).1
        ((coreSlice_parts_integrable hψ t).2.1.const_mul Z), integral_const_mul]
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    integral_core_kinetic hψ, integral_core_nuclear hψ, integral_core_repulsion hψ]

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SpatialErrorWeight
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace CoulombAtom
variable {N : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)

theorem spatial_cut_ims {ψ : FormVector N} (hψ : SobolevVector ψ) (Z : ℝ) :
    (∑ b : Fin N → Fin 2, formEnergy Z (multiplyForm (spatialProduct p hp b) ψ)) =
      formEnergy Z ψ + (1 / 2 : ℝ) * ∑ s : Spins N, ∑ i : Fin N,
        ∫ x, spatialErrorWeight p (x i) * ‖ψ.value s x‖ ^ 2 := by
  rw [spatial_cut_energy p hp hψ, spatial_cut_error p hp hψ]

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CutCoreNumber
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace CoulombAtom

lemma orderedCutForm_energy {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)
    (ψ : FormVector L) (b : Fin L → Fin 2) (Z : ℝ) :
    formEnergy Z (orderedCutForm p hp ψ b) = formEnergy Z (multiplyForm (spatialProduct (N := L) p hp b) ψ) :=
  formEnergy_reindex _ _ _

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CutExpectedOut
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
namespace CoulombAtom

lemma orderedCutForm_zero_of_factor {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)
    (ψ : FormVector L) (b : Fin L → Fin 2)
    (s : Spins (cutCoreNumber b + cutOutNumber b))
    (x : Configuration (cutCoreNumber b + cutOutNumber b)) (i : Fin (cutOutNumber b))
    (hzero : (p 1).value (x (finSumFinEquiv (Sum.inr i))) = 0) :
    (orderedCutForm p hp ψ b).value s x = 0 := by
  classical
  rw [orderedCutForm_value]
  change (spatialProductValue p (coreCutLabels (cutCoreNumber b) (cutOutNumber b)) x : ℂ) * _ = 0
  have hh : spatialProductValue p (coreCutLabels (cutCoreNumber b) (cutOutNumber b)) x = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ (finSumFinEquiv (Sum.inr i)))
    simpa only [coreCutLabels,joinLists_right] using hzero
  rw [hh,Complex.ofReal_zero,zero_mul]

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_BlockEnergetics
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom

theorem formEnergy_core_out_cross {N M : ℕ} (Z : ℝ) (ψ : FormVector (N+M)) :
    formEnergy Z ψ = (coreKinetic ψ-Z*coreNuclear ψ+coreRepulsion ψ)+
      outKinetic ψ-Z*outNuclear ψ+outRepulsion ψ+crossRepulsion ψ := by
  rw [formEnergy_parts,formKinetic_core_out,formNuclear_core_out,formRepulsion_core_out_cross]
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_ConditionalFieldIdentity
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom

lemma normalizedCoreField_mul_mass {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (Z lam : ℝ) (y : Space) :
    normalizedCoreField Z lam ψ y*formMass ψ =
      Z*formMass ψ/‖y‖-coreCoulombAt ψ y-lam*formMass ψ := by
  by_cases hm : formMass ψ = 0
  · simp only [hm,mul_zero,zero_div,coreCoulombAt_mass_zero hψ hm,sub_zero]
  · unfold normalizedCoreField
    rw [sub_mul,div_mul_cancel₀ _ hm]

lemma coreSlice_mass_div_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (j : Fin M) :
    Integrable (fun y : Configuration M => formMass (coreSlice ψ t y)/‖y j‖) := by
  simp_rw [coreSlice_mass_div]
  apply integrable_finsetSum
  intro s _
  have hh := (integrable_join (N := N) (M := M) (nuclear_integrable
    (finSumFinEquiv (Sum.inr j)) (hψ.1 (joinLists s t))
    (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))).integral_prod_right
  simpa only [joinLists_right] using hh

lemma coreSlice_cross_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (j : Fin M) :
    Integrable (fun y : Configuration M => coreCoulombAt (coreSlice ψ t y) (y j)) := by
  unfold coreCoulombAt
  apply integrable_finsetSum
  intro s _
  apply integrable_finsetSum
  intro i _
  have hne : (finSumFinEquiv (Sum.inl i) : Fin (N+M)) ≠ finSumFinEquiv (Sum.inr j) := by
      intro h
      have hh := finSumFinEquiv.injective h
      cases hh
  have hh := (integrable_join (N := N) (M := M) (pair_integrable _ _ hne
    (hψ.1 (joinLists s t)) (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))).integral_prod_right
  simpa only [coreSlice,joinLists_left,joinLists_right] using hh

lemma integral_coreSlice_mass_div {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) :
    (∑ t : Spins M, ∫ y : Configuration M, ∑ j : Fin M, formMass (coreSlice ψ t y)/‖y j‖) =
      outNuclear ψ := by
  have hi (s : Spins N) (t : Spins M) (j : Fin M) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖ψ.value (joinLists s t) (joinLists x y)‖^2/‖y j‖) := by
    simpa only [joinLists_right] using (integrable_join (N := N) (M := M)
      (nuclear_integrable (finSumFinEquiv (Sum.inr j)) (hψ.1 (joinLists s t))
        (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))).integral_prod_right
  simp_rw [integral_finsetSum _ (fun j _ => coreSlice_mass_div_integrable hψ _ j),
    coreSlice_mass_div,integral_finsetSum _ (fun s _ => hi s _ _)]
  have he (s : Spins N) (t : Spins M) (j : Fin M) :
      (∫ y : Configuration M, ∫ x : Configuration N,
        ‖ψ.value (joinLists s t) (joinLists x y)‖^2/‖y j‖) =
      ∫ z, ‖ψ.value (joinLists s t) z‖^2/‖z (finSumFinEquiv (Sum.inr j))‖ := by
    simpa only [joinLists_right] using integral_join (N := N) (M := M)
      (nuclear_integrable (finSumFinEquiv (Sum.inr j)) (hψ.1 (joinLists s t))
        (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))
  simp_rw [he]
  conv_lhs => arg 2; ext t; rw [Finset.sum_comm]
  exact sum_spin_join (fun s => ∑ j : Fin M, ∫ z,
    ‖ψ.value s z‖^2/‖z (finSumFinEquiv (Sum.inr j))‖)

lemma integral_coreSlice_cross {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) :
    (∑ t : Spins M, ∫ y : Configuration M, ∑ j : Fin M, coreCoulombAt (coreSlice ψ t y) (y j)) =
      crossRepulsion ψ := by
  have hi (s : Spins N) (t : Spins M) (i : Fin N) (j : Fin M) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖ψ.value (joinLists s t) (joinLists x y)‖^2/‖x i-y j‖) := by
    have hne : (finSumFinEquiv (Sum.inl i) : Fin (N+M)) ≠ finSumFinEquiv (Sum.inr j) := by
      intro h
      have hh := finSumFinEquiv.injective h
      cases hh
    simpa only [joinLists_right,joinLists_left] using (integrable_join (N := N) (M := M)
      (pair_integrable _ _ hne (hψ.1 (joinLists s t))
        (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))).integral_prod_right
  simp_rw [integral_finsetSum _ (fun j _ => coreSlice_cross_integrable hψ _ j),coreCoulombAt,coreSlice]
  simp_rw [integral_finsetSum _ (fun s _ => integrable_finsetSum _ (fun i _ => hi s _ i _)),
    integral_finsetSum _ (fun i _ => hi _ _ i _)]
  have he (s : Spins N) (t : Spins M) (i : Fin N) (j : Fin M) :
      (∫ y : Configuration M, ∫ x : Configuration N,
        ‖ψ.value (joinLists s t) (joinLists x y)‖^2/‖x i-y j‖) =
      ∫ z, ‖ψ.value (joinLists s t) z‖^2/
        ‖z (finSumFinEquiv (Sum.inl i))-z (finSumFinEquiv (Sum.inr j))‖ := by
    have hne : (finSumFinEquiv (Sum.inl i) : Fin (N+M)) ≠ finSumFinEquiv (Sum.inr j) := by
      intro h
      have hh := finSumFinEquiv.injective h
      cases hh
    simpa only [joinLists_right,joinLists_left] using integral_join (N := N) (M := M)
      (pair_integrable _ _ hne (hψ.1 (joinLists s t))
        (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))
  simp_rw [he]
  conv_lhs => arg 2; ext t; rw [Finset.sum_comm]; arg 2; ext s; rw [Finset.sum_comm]
  exact sum_spin_join (fun s => ∑ i : Fin N, ∑ j : Fin M, ∫ z,
    ‖ψ.value s z‖^2/‖z (finSumFinEquiv (Sum.inl i))-z (finSumFinEquiv (Sum.inr j))‖)

lemma conditionalFieldSum_ae {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z lam : ℝ) (t : Spins M) :
    conditionalFieldSum Z lam ψ t =ᵐ[volume]
      fun y => Z*(∑ j : Fin M, formMass (coreSlice ψ t y)/‖y j‖)-
        (∑ j : Fin M, coreCoulombAt (coreSlice ψ t y) (y j))-
        lam*M*formMass (coreSlice ψ t y) := by
  apply (hψ.ae_coreSlice t).mono
  intro y hy
  unfold conditionalFieldSum
  rw [Finset.mul_sum]
  simp_rw [mul_comm (formMass _),normalizedCoreField_mul_mass hy,mul_div_assoc]
  simp only [Finset.sum_sub_distrib,←Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

lemma conditionalFieldSum_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z lam : ℝ) (t : Spins M) :
    Integrable (conditionalFieldSum Z lam ψ t) := by
  have hi := ((integrable_finsetSum Finset.univ (fun j _ => coreSlice_mass_div_integrable hψ t j)).const_mul Z).sub
    (integrable_finsetSum Finset.univ (fun j _ => coreSlice_cross_integrable hψ t j))
  exact (hi.sub ((hψ.coreSlice_mass_integrable t).const_mul (lam*M))).congr
    (conditionalFieldSum_ae hψ Z lam t).symm

lemma integral_conditionalFieldSum {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z lam : ℝ) :
    (∑ t : Spins M, ∫ y, conditionalFieldSum Z lam ψ t y) =
      Z*outNuclear ψ-crossRepulsion ψ-lam*M*formMass ψ := by
  have ht (t : Spins M) : (∫ y, conditionalFieldSum Z lam ψ t y) =
      Z*(∫ y, ∑ j : Fin M, formMass (coreSlice ψ t y)/‖y j‖)-
      (∫ y, ∑ j : Fin M, coreCoulombAt (coreSlice ψ t y) (y j))-
      lam*M*(∫ y, formMass (coreSlice ψ t y)) := by
    rw [integral_congr_ae (conditionalFieldSum_ae hψ Z lam t)]
    have hi := (integrable_finsetSum Finset.univ (fun j _ => coreSlice_mass_div_integrable hψ t j)).const_mul Z
    have hj := integrable_finsetSum Finset.univ (fun j _ => coreSlice_cross_integrable hψ t j)
    rw [integral_sub (f := fun y => Z*(∑ j : Fin M, formMass (coreSlice ψ t y)/‖y j‖)-
      (∑ j : Fin M, coreCoulombAt (coreSlice ψ t y) (y j)))
      (g := fun y => lam*M*formMass (coreSlice ψ t y))
      (hi.sub hj) ((hψ.coreSlice_mass_integrable t).const_mul (lam*M)),
      integral_sub hi hj,integral_const_mul,integral_const_mul]
  simp_rw [ht]
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum,
    integral_coreSlice_mass_div hψ,integral_coreSlice_cross hψ,hψ.integral_coreSlice_mass]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ConditionalRetainedGap
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis CoulombNeumann

def weightedPatchGap {N M : ℕ} (ψ : FormVector (N+M)) (t : Spins M)
    (Z lam : ℝ) (y : Space) (R : ℝ) {b : ℝ} (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (u : Configuration M) : ℝ :=
  formMass (coreSlice ψ t u)*tfPatchGap R tfKinetic tfKinetic_pos
    (conditionalPatchField ψ t Z lam y R u) (retainedPatchLp hb (S u) u y R)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RadialPatchGeometry
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis CoulombNeumann

lemma coreFirstRadialCut_error (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) :
    spatialErrorWeight (coreFirstRadialCut y ht hb) = spatialErrorWeight (radialCut y ht hb) := by
  funext x
  unfold spatialErrorWeight
  apply Finset.sum_congr rfl
  intro a _
  simp only [Fin.sum_univ_two,coreFirstRadialCut,radialCut,Matrix.cons_val_zero,
    Matrix.cons_val_one]
  exact add_comm _ _

lemma coreFirstRadialCut_core_deriv_zero (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (x : Space) (hx : x ∉ radialPatchCore y t) (a : Fin 3) :
    lineDeriv ℝ (coreFirstRadialCut y ht hb 0).value x (spaceDirections a) = 0 := by
  have hx' : ‖x-y‖ < t := lt_of_not_ge hx
  change lineDeriv ℝ (fun z => Real.sin (radialPhase y t b z)) x _ = 0
  rw [radial_sin_derivative,radialPhase_derivative_zero_off_collar ht hb
    (fun h => (not_le.mpr hx') h.1),mul_zero]

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis CoulombNeumann

lemma weightedParticleCount_const_mul {L : ℕ} (ψ : FormVector L) (c : ℝ) (w : Space → ℝ) :
    weightedParticleCount ψ (fun x => c*w x) = c*weightedParticleCount ψ w := by
  simp only [weightedParticleCount,mul_assoc,integral_const_mul,Finset.mul_sum]

lemma radial_fresh_ims_bound {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) :
    (1/2:ℝ)*weightedParticleCount ψ (spatialErrorWeight (coreFirstRadialCut y ht hb)) ≤
      (3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2*
        weightedParticleCount ψ (fun x => if t ≤ ‖x-y‖ ∧ ‖x-y‖ ≤ t+b then 1 else 0) := by
  classical
  rw [coreFirstRadialCut_error]
  have hm : Measurable (fun x : Space => if t ≤ ‖x-y‖ ∧ ‖x-y‖ ≤ t+b then (1:ℝ) else 0) :=
    measurable_const.ite
      ((isClosed_le continuous_const ((continuous_id.sub continuous_const).norm)).inter
        (isClosed_le ((continuous_id.sub continuous_const).norm) continuous_const)).measurableSet
      measurable_const
  have hi (s : Spins L) (i : Fin L) : Integrable (fun x : Configuration L =>
      (3*(Real.pi*smoothTransitionBound/b)^2)*
        (if t ≤ ‖x i-y‖ ∧ ‖x i-y‖ ≤ t+b then (1:ℝ) else 0)*‖ψ.value s x‖^2) := by
    have hi := weightedParticleCount_integrable hψ hm (B := 1)
      (fun x => by split_ifs <;> norm_num) s i
    convert hi.const_mul (3*(Real.pi*smoothTransitionBound/b)^2) using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    ring
  have hh := weightedParticleCount_mono
    (fun s i => spatial_error_weight_integrable (radialCut y ht hb) hψ s i)
    hi (radialCut_error_bound y ht hb)
  rw [weightedParticleCount_const_mul] at hh
  nlinarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_CutCountDomination
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombAtom
open CoulombRadialAveraging

lemma spatialCutExpectation_outMoment {N : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector N)
    (q : ℕ → ℝ) :
    (∑ c : Fin N → Fin 2, q (cutOutNumber c)*formMass (orderedCutForm p hp ψ c)) =
      spatialCutExpectation p hp ψ (fun c _ => q (cutOutNumber c)) := by
  simp_rw [orderedCutForm_mass]
  simp only [spatialCutExpectation,formMass,Finset.mul_sum,integral_const_mul]

lemma radialCut_out_distance {N : ℕ} (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (c : Fin N → Fin 2) (x : Configuration N)
    (hx : (spatialProduct (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) c).value x ≠ 0)
    (i : Fin N) (hi : c i ≠ 0) : ‖x i-y‖ < t+b := by
  classical
  have hc : c i = 1 := by omega
  change (∏ j, (coreFirstRadialCut y ht hb (c j)).value (x j)) ≠ 0 at hx
  have hf : (coreFirstRadialCut y ht hb (c i)).value (x i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i)
  by_contra hh
  have hz := (radialCut_outer ht hb (le_of_not_gt hh)).1
  apply hf
  simpa only [hc,coreFirstRadialCut,radialCut,Matrix.cons_val_one,Matrix.cons_val_zero] using hz

lemma radialCut_outNumber_le_rawBall {N : ℕ} (y : Space) {t b R : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (hR : t+b ≤ R)
    (c : Fin N → Fin 2) (x : Configuration N)
    (hx : (spatialProduct (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) c).value x ≠ 0) :
    (cutOutNumber c:ℝ) ≤ rawBallCount y R x := by
  classical
  rw [cutOutNumber_eq_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : c i ≠ 0
  · have hd := lt_of_lt_of_le (radialCut_out_distance y ht hb c x hx i hi) hR
    simp [hi,hd]
  · simp only [hi,ite_false]
    split_ifs <;> norm_num

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RadialCountSelection
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombAtom
open CoulombRadialAveraging

lemma radialCut_out_second_moment {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) {t b R : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hR : t+b ≤ R) :
    (∑ c : Fin N → Fin 2, (cutOutNumber c:ℝ)^2*formMass
      (orderedCutForm (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) ψ c)) ≤
      ∫ x, rawBallCount y R x^2 ∂formRawLaw ψ := by
  rw [spatialCutExpectation_outMoment _ _ _ (fun n => (n:ℝ)^2)]
  apply spatialCutExpectation_le_raw _ _ hψ
    (fun _ => measurable_const) (A := (N:ℝ)^2)
    (fun c _ => norm_sq_le_of_nonneg (Nat.cast_nonneg _) (by exact_mod_cast cutOutNumber_le_total c))
    ((rawBallCount_measurable y R).pow_const 2) (B := (N:ℝ)^2)
    (fun x => norm_sq_le_of_nonneg (rawBallCount_nonneg _ _ _) (rawBallCount_le _ _ _))
  intro c x hx
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (radialCut_outNumber_le_rawBall y ht hb hR c x hx) 2

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_IntegrableCutTower
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_IntegrableCutTower_scope

open MeasureTheory Set Filter
open scoped BigOperators

lemma weighted_coreSlice_eq_full_integrable {N M : ℕ}
    (ψ : FormVector (N+M)) (g : Configuration M → ℝ)
    (hi : ∀ s : Spins (N+M), Integrable (fun x => g (outProjection x)*‖ψ.value s x‖^2)) :
    (∑ s : Spins M, ∫ u, g u*formMass (coreSlice ψ s u)) =
      ∑ s : Spins (N+M), ∫ x, g (outProjection x)*‖ψ.value s x‖^2 := by
  have hj (s : Spins N) (t : Spins M) : Integrable (fun p : Configuration N × Configuration M =>
      g p.2*‖ψ.value (joinLists s t) (joinLists p.1 p.2)‖^2) := by
    simpa only [outProjection_join] using integrable_join (N := N) (M := M) (hi (joinLists s t))
  have hk (s : Spins N) (t : Spins M) : Integrable (fun u : Configuration M =>
      g u*(∫ v : Configuration N, ‖ψ.value (joinLists s t) (joinLists v u)‖^2)) := by
    simpa only [integral_const_mul] using (hj s t).integral_prod_right
  simp only [formMass,Finset.mul_sum,coreSlice]
  simp_rw [integral_finsetSum _ (fun s _ => hk s _),←integral_const_mul]
  have he (s : Spins N) (t : Spins M) :
      (∫ u : Configuration M, ∫ v : Configuration N,
        g u*‖ψ.value (joinLists s t) (joinLists v u)‖^2) =
      ∫ x, g (outProjection x)*‖ψ.value (joinLists s t) x‖^2 := by
    simpa only [outProjection_join] using integral_join (N := N) (M := M) (hi (joinLists s t))
  simp_rw [he]
  exact sum_spin_join (fun s : Spins (N+M) =>
    ∫ x, g (outProjection x)*‖ψ.value s x‖^2)

end Work_IntegrableCutTower_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_FormRawPotential
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombAtom

lemma rawPotential_nonneg {N : ℕ} (y : Space) (x : Configuration N) : 0 ≤ rawPotential y x :=
  Finset.sum_nonneg (fun _ _ => by positivity)

lemma formRawLaw_integrable_iff {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {f : Configuration N → ℝ} :
    Integrable f (formRawLaw ψ) ↔ Integrable (fun x => formRawDensity ψ x*f x) := by
  rw [formRawLaw,integrable_withDensity_iff_integrable_smul₀'
    (formRawDensity_integrable hψ).aemeasurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (formRawDensity_nonneg ψ _),smul_eq_mul]

lemma rawPotential_form_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ) (y : Space) :
    Integrable (rawPotential y) (formRawLaw ψ) := by
  rw [formRawLaw_integrable_iff hψ]
  simp only [formRawDensity,rawPotential,Finset.sum_mul,Finset.mul_sum]
  apply integrable_finsetSum
  intro s _
  apply integrable_finsetSum
  intro i _
  simpa only [mul_one_div] using hψ.shifted_nuclear_integrable i s y

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_CorePotentialTower
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators

namespace CoulombAtom

lemma rawPotential_coreSlice_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (y : Space) :
    Integrable (fun u : Configuration M => rawPotential y u*formMass (coreSlice ψ t u)) := by
  simp only [rawPotential,Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  simpa only [one_div,mul_comm,←div_eq_mul_inv] using coreSlice_mass_shifted_integrable hψ t i y

lemma integral_coreSlice_coreCoulombAt {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (y : Space) :
    (∑ t : Spins M, ∫ u : Configuration M, coreCoulombAt (coreSlice ψ t u) y) =
      ∑ s : Spins (N+M), ∑ i : Fin N, ∫ x, ‖ψ.value s x‖^2/‖x (finSumFinEquiv (Sum.inl i))-y‖ := by
  have hi (s : Spins N) (t : Spins M) (i : Fin N) : Integrable (fun u : Configuration M =>
      ∫ v : Configuration N, ‖ψ.value (joinLists s t) (joinLists v u)‖^2/‖v i-y‖) := by
    simpa only [joinLists_left] using (integrable_join (N := N) (M := M)
      (hψ.shifted_nuclear_integrable (joinLists s t) (finSumFinEquiv (Sum.inl i)) y)).integral_prod_right
  simp only [coreCoulombAt,coreSlice]
  simp_rw [integral_finsetSum _ (fun s _ => integrable_finsetSum _ (fun i _ => hi s _ i)),
    integral_finsetSum _ (fun i _ => hi _ _ i)]
  have he (s : Spins N) (t : Spins M) (i : Fin N) :
      (∫ u : Configuration M, ∫ v : Configuration N,
        ‖ψ.value (joinLists s t) (joinLists v u)‖^2/‖v i-y‖) =
      ∫ x, ‖ψ.value (joinLists s t) x‖^2/‖x (finSumFinEquiv (Sum.inl i))-y‖ := by
    simpa only [joinLists_left] using integral_join (N := N) (M := M)
      (hψ.shifted_nuclear_integrable (joinLists s t) (finSumFinEquiv (Sum.inl i)) y)
  simp_rw [he]
  exact sum_spin_join (fun s : Spins (N+M) => ∑ i : Fin N,
    ∫ x, ‖ψ.value s x‖^2/‖x (finSumFinEquiv (Sum.inl i))-y‖)

lemma integral_rawPotential_coreSlice {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (y : Space) :
    (∑ t : Spins M, ∫ u : Configuration M, rawPotential y u*formMass (coreSlice ψ t u)) =
      ∑ s : Spins (N+M), ∑ i : Fin M, ∫ x, ‖ψ.value s x‖^2/‖x (finSumFinEquiv (Sum.inr i))-y‖ := by
  have hi (s : Spins (N+M)) : Integrable (fun x =>
      rawPotential y (outProjection x)*‖ψ.value s x‖^2) := by
    simp only [rawPotential,Finset.sum_mul,outProjection]
    apply integrable_finsetSum
    intro i _
    simpa only [one_div,mul_comm,←div_eq_mul_inv] using
      hψ.shifted_nuclear_integrable s (finSumFinEquiv (Sum.inr i)) y
  rw [weighted_coreSlice_eq_full_integrable _ _ hi]
  apply Finset.sum_congr rfl
  intro s _
  simp only [rawPotential,outProjection]
  simp only [Finset.sum_mul,div_mul_eq_mul_div,one_mul]
  exact integral_finsetSum _ (fun i _ => hψ.shifted_nuclear_integrable s (finSumFinEquiv (Sum.inr i)) y)

lemma fresh_core_outer_potential_tower {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (y : Space) :
    (∑ t : Spins M, ∫ u : Configuration M,
      coreCoulombAt (coreSlice ψ t u) y+rawPotential y u*formMass (coreSlice ψ t u)) =
      coreCoulombAt ψ y := by
  simp_rw [integral_add (coreSlice_coreCoulombAt_integrable hψ _ y)
    (rawPotential_coreSlice_integrable hψ _ y)]
  rw [Finset.sum_add_distrib,integral_coreSlice_coreCoulombAt hψ y,
    integral_rawPotential_coreSlice hψ y,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  change (∑ i : Fin N, ∫ x, ‖ψ.value s x‖^2/‖x (finSumFinEquiv (Sum.inl i))-y‖) +
    (∑ i : Fin M, ∫ x, ‖ψ.value s x‖^2/‖x (finSumFinEquiv (Sum.inr i))-y‖) =
    ∑ i : Fin (N+M), ∫ x, ‖ψ.value s x‖^2/‖x i-y‖
  simpa only [Fintype.sum_sum_type] using
    (Equiv.sum_comp finSumFinEquiv (fun i : Fin (N+M) => ∫ x, ‖ψ.value s x‖^2/‖x i-y‖))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_FreshFieldTower
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_FreshFieldTower_scope

open MeasureTheory Filter Set
open scoped BigOperators

namespace CoulombAtom

lemma normalizedCoreField_weighted_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (Z lam : ℝ) (y : Space) :
    Integrable (fun u => normalizedCoreField Z lam (coreSlice ψ t u) y*formMass (coreSlice ψ t u)) := by
  have hi := ((hψ.coreSlice_mass_integrable t).const_mul (Z/‖y‖-lam)).sub
    (coreSlice_coreCoulombAt_integrable hψ t y)
  apply hi.congr
  filter_upwards [hψ.ae_coreSlice t] with u hu
  rw [normalizedCoreField_mul_mass hu]
  simp only [Pi.sub_apply]
  ring

lemma normalized_core_outer_field_tower {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z lam : ℝ) (y : Space) :
    (∑ t : Spins M, ∫ u : Configuration M,
      (normalizedCoreField Z lam (coreSlice ψ t u) y-rawPotential y u)*formMass (coreSlice ψ t u)) =
      (Z/‖y‖-lam)*formMass ψ-coreCoulombAt ψ y := by
  have he (t : Spins M) :
      (fun u => (normalizedCoreField Z lam (coreSlice ψ t u) y-rawPotential y u)*formMass (coreSlice ψ t u)) =ᵐ[volume]
      fun u => (Z/‖y‖-lam)*formMass (coreSlice ψ t u)-
        (coreCoulombAt (coreSlice ψ t u) y+rawPotential y u*formMass (coreSlice ψ t u)) := by
    filter_upwards [hψ.ae_coreSlice t] with u hu
    rw [sub_mul,normalizedCoreField_mul_mass hu]
    ring
  have hint (t : Spins M) :
      (∫ u : Configuration M, (normalizedCoreField Z lam (coreSlice ψ t u) y-rawPotential y u)*
        formMass (coreSlice ψ t u)) =
      (Z/‖y‖-lam)*(∫ u, formMass (coreSlice ψ t u))-
        ∫ u, coreCoulombAt (coreSlice ψ t u) y+rawPotential y u*formMass (coreSlice ψ t u) := by
    rw [integral_congr_ae (he t)]
    have hh := integral_sub
      ((hψ.coreSlice_mass_integrable t).const_mul (Z/‖y‖-lam))
      ((coreSlice_coreCoulombAt_integrable hψ t y).add (rawPotential_coreSlice_integrable hψ t y))
    simp only [Pi.add_apply] at hh
    rw [hh,integral_const_mul]
  simp_rw [hint]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,hψ.integral_coreSlice_mass,
    fresh_core_outer_potential_tower hψ y]

theorem fresh_cut_field_tower {N : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    {ψ : FormVector N} (hψ : SobolevVector ψ) (Z lam : ℝ) (y : Space) :
    (∑ c : Fin N → Fin 2, ∑ t : Spins (cutOutNumber c), ∫ u,
      (normalizedCoreField Z lam (coreSlice (orderedCutForm p hp ψ c) t u) y-rawPotential y u)*
        formMass (coreSlice (orderedCutForm p hp ψ c) t u)) =
      (Z/‖y‖-lam)*formMass ψ-(∫ x, rawPotential y x ∂formRawLaw ψ) := by
  simp_rw [normalized_core_outer_field_tower (orderedCutForm_sobolev p hp hψ _) Z lam y]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,orderedCutForm_mass_sum p hp hψ,
    fresh_cut_coreCoulombAt_sum p hp hψ y,integral_rawPotential_formRawLaw hψ y]

end CoulombAtom

end Work_FreshFieldTower_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_Weighted
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

def bindingRoot (R ε : ℝ) (x : Space) : ℝ := Real.sqrt (bindingWeight R ε x)

lemma bindingWeight_pos {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (x : Space) :
    0 < bindingWeight R ε x := by
  unfold bindingWeight
  have ht := regularizedRadius_pos hε x
  positivity

lemma bindingWeight_le {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (x : Space) :
    bindingWeight R ε x ≤ R := by
  have ht := regularizedRadius_pos hε x
  unfold bindingWeight
  apply (div_le_iff₀ (by positivity : 0 < R + regularizedRadius ε x)).mpr
  nlinarith [sq_nonneg R]

lemma bindingRoot_sq {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (x : Space) :
    bindingRoot R ε x ^ 2 = bindingWeight R ε x :=
  Real.sq_sqrt (bindingWeight_pos hR hε x).le

lemma bindingRoot_pos {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (x : Space) :
    0 < bindingRoot R ε x := Real.sqrt_pos.mpr (bindingWeight_pos hR hε x)

lemma bindingRoot_bound {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (x : Space) :
    |bindingRoot R ε x| ≤ Real.sqrt R := by
  rw [abs_of_pos (bindingRoot_pos hR hε x)]
  exact Real.sqrt_le_sqrt (bindingWeight_le hR hε x)

lemma bindingRoot_smooth {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ContDiff ℝ ∞ (bindingRoot R ε) := by
  apply ContDiff.sqrt
  · apply ContDiff.div
    · exact contDiff_const.mul (regularizedRadius_smooth hε)
    · exact contDiff_const.add (regularizedRadius_smooth hε)
    · intro x; have ht := regularizedRadius_pos hε x; positivity
  · intro x; exact (bindingWeight_pos hR hε x).ne'

lemma bindingRoot_derivative {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (a : Fin 3) (x : Space) :
    fderiv ℝ (bindingRoot R ε) x (EuclideanSpace.single a 1) =
      bindingRoot R ε x * R * x a /
        (2 * (regularizedRadius ε x) ^ 2 * (R + regularizedRadius ε x)) := by
  let t := regularizedRadius ε x
  have ht : 0 < t := regularizedRadius_pos hε x
  have hD := ((hasFDerivAt_id (𝕜 := ℝ) x).norm_sq).add_const (ε ^ 2)
  have htD := (Real.hasDerivAt_sqrt (by positivity : ‖x‖ ^ 2 + ε ^ 2 ≠ 0)).comp_hasFDerivAt x hD
  have hw := ((hasDerivAt_id t).const_mul R).div
    ((hasDerivAt_id t).const_add R) (by positivity : R + t ≠ 0)
  have hs := (Real.hasDerivAt_sqrt (by positivity : R * t / (R+t) ≠ 0)).comp t hw
  have hh := hs.comp_hasFDerivAt x htD
  change HasFDerivAt (bindingRoot R ε) _ x at hh
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
    innerSL_apply_apply, EuclideanSpace.inner_single_right, conj_trivial, one_mul]
  have hp := bindingRoot_pos hR hε x
  have he := bindingRoot_sq hR hε x
  change bindingRoot R ε x ^ 2 = R*t/(R+t) at he
  simp only [smul_eq_mul, nsmul_eq_mul, id_eq, mul_one]
  change (1 / (2 * bindingRoot R ε x)) *
    ((R * (R+t) - R*t) / (R+t)^2) *
    ((1 / (2 * t)) * (2 * x a)) =
      bindingRoot R ε x * R * x a / (2 * t^2 * (R+t))
  have he' : bindingRoot R ε x ^ 2 * (R+t) = R*t := (eq_div_iff (by positivity)).mp he
  field_simp
  rw [he']
  ring

lemma bindingRoot_gradient_bound {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (a : Fin 3) (x : Space) :
    |fderiv ℝ (bindingRoot R ε) x (EuclideanSpace.single a 1)| ≤
      Real.sqrt R / (2 * ε) := by
  let t := regularizedRadius ε x
  have ht : 0 < t := regularizedRadius_pos hε x
  have hp := bindingRoot_pos hR hε x
  have hx : |x a| ≤ t := by
    have hc := radialField_norm_le hε a x
    change ‖x a / t‖ ≤ 1 at hc
    rw [norm_div, Real.norm_eq_abs, Real.norm_of_nonneg ht.le, div_le_one ht] at hc
    exact hc
  rw [bindingRoot_derivative hR hε, abs_div, abs_mul, abs_mul,
    abs_of_pos hp, abs_of_pos hR, abs_of_pos (by positivity : 0 < 2 * t^2 * (R+t))]
  change bindingRoot R ε x * R * |x a| / (2*t^2*(R+t)) ≤ _
  calc
    _ ≤ Real.sqrt R * R * t / (2*t^2*(R+t)) := by
      gcongr
      exact (abs_of_pos hp ▸ bindingRoot_bound hR hε x)
    _ ≤ Real.sqrt R / (2*t) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_nonneg (Real.sqrt_nonneg R) (pow_nonneg ht.le 3)]
    _ ≤ _ := div_le_div_of_nonneg_left (Real.sqrt_nonneg R) (by positivity)
      (by gcongr; exact le_regularizedRadius hε.le x)


open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_Restriction
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
namespace CoulombAtom

lemma lineDeriv_binding_coordinate {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (i j : Fin N) (a : Fin 3) (x : Configuration N) :
    lineDeriv ℝ (fun y : Configuration N => bindingRoot R ε (y i)) x (direction j a) =
      if j = i then fderiv ℝ (bindingRoot R ε) (x i) (EuclideanSpace.single a 1) else 0 := by
  classical
  have h := ((bindingRoot_smooth hR hε).differentiable (by simp) (x i)).hasFDerivAt.comp
    x (electronProjection i).hasFDerivAt
  change HasFDerivAt (fun y : Configuration N => bindingRoot R ε (y i)) _ x at h
  rw [h.differentiableAt.lineDeriv_eq_fderiv, h.fderiv]
  change fderiv ℝ (bindingRoot R ε) (x i) (direction j a i) = _
  by_cases hij : j = i
  · subst j
    simp [direction]
  · simp [direction, hij, Ne.symm hij]

def bindingMultiplier {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (i : Fin N) :
    SmoothMultiplier (sectorDirections N) where
  value := fun x => bindingRoot R ε (x i)
  regular := (bindingRoot_smooth hR hε).comp (electronProjection i).contDiff
  bound := ⟨Real.sqrt R, fun x => bindingRoot_bound hR hε (x i)⟩
  gradient_bound := fun j => ⟨Real.sqrt R / (2*ε), fun x => by
    rw [lineDeriv_binding_coordinate hR hε i j.1 j.2 x]
    split_ifs
    · exact bindingRoot_gradient_bound hR hε j.2 (x i)
    · simp only [abs_zero]; positivity⟩

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_Sum
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace

def bindingTotalMultiplier {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    FermionMultiplier N where
  toSmoothMultiplier := SmoothMultiplier.sumSquares (bindingMultiplier hR hε)
  symmetric := by
    intro π x
    change (∑ i, bindingRoot R ε ((x ∘ π) i) ^ 2) = ∑ i, bindingRoot R ε (x i) ^ 2
    exact Equiv.sum_comp π (fun i => bindingRoot R ε (x i) ^ 2)


open MeasureTheory Filter
open scoped Topology BigOperators


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_OuterFieldMaximum
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombAtom

def conditionalOutMaximum {N M : ℕ} (Z lam : ℝ) (ψ : FormVector (N+M))
    (s : Spins M) (u : Configuration M) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun o : Option (Fin M) =>
    o.elim 0 (fun i => normalizedCoreField Z lam (coreSlice ψ s u) (u i)))

lemma conditionalOutMaximum_nonneg {N M : ℕ} (Z lam : ℝ) (ψ : FormVector (N+M))
    (s : Spins M) (u : Configuration M) : 0 ≤ conditionalOutMaximum Z lam ψ s u := by
  exact Finset.le_sup' (fun o : Option (Fin M) =>
    o.elim 0 (fun i => normalizedCoreField Z lam (coreSlice ψ s u) (u i))) (Finset.mem_univ none)

lemma conditionalField_le_outMaximum {N M : ℕ} (Z lam : ℝ) (ψ : FormVector (N+M))
    (s : Spins M) (u : Configuration M) (i : Fin M) :
    normalizedCoreField Z lam (coreSlice ψ s u) (u i) ≤ conditionalOutMaximum Z lam ψ s u := by
  exact Finset.le_sup' (fun o : Option (Fin M) =>
    o.elim 0 (fun i => normalizedCoreField Z lam (coreSlice ψ s u) (u i))) (Finset.mem_univ (some i))

lemma conditionalOutMaximum_le {N M : ℕ} (Z lam : ℝ) (ψ : FormVector (N+M))
    (s : Spins M) (u : Configuration M) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ i, normalizedCoreField Z lam (coreSlice ψ s u) (u i) ≤ B) :
    conditionalOutMaximum Z lam ψ s u ≤ B := by
  apply Finset.sup'_le
  intro o _
  cases o with
  | none => exact hB
  | some i => exact hf i

lemma conditionalOutMaximum_aemeasurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (Z lam : ℝ) :
    AEMeasurable (conditionalOutMaximum Z lam ψ s) := by
  obtain ⟨F,hF,he⟩ := coreSlice_field_measurable_rep hψ s Z lam
  let f : Option (Fin M) → Configuration M → ℝ := fun o u => o.elim 0 (fun i => F (u,u i))
  have hf (o : Option (Fin M)) : Measurable (f o) := by
    cases o with
    | none => exact measurable_const
    | some i => exact hF.comp (measurable_id.prodMk (measurable_pi_apply i))
  have hh := Finset.measurable_sup' Finset.univ_nonempty (fun i (_ : i ∈ Finset.univ) => hf i)
  apply hh.aemeasurable.congr
  filter_upwards [he] with u hu
  simp only [Finset.sup'_apply]
  unfold conditionalOutMaximum
  congr 1
  funext o
  cases o with
  | none => rfl
  | some i => exact hu (u i)

lemma orderedCutForm_slice_mass_zero {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector L) (c : Fin L → Fin 2)
    (s : Spins (cutOutNumber c)) (u : Configuration (cutOutNumber c))
    (i : Fin (cutOutNumber c)) (hi : (p 1).value (u i) = 0) :
    formMass (coreSlice (orderedCutForm p hp ψ c) s u) = 0 := by
  apply Finset.sum_eq_zero
  intro t _
  have hz (x : Configuration (cutCoreNumber c)) :
      (coreSlice (orderedCutForm p hp ψ c) s u).value t x = 0 := by
    apply orderedCutForm_zero_of_factor p hp ψ c _ _ i
    simpa only [joinLists_right] using hi
  simp only [hz,norm_zero,zero_pow (by decide : 2 ≠ 0),integral_zero]

lemma radial_out_position_nuclear {L : ℕ} (ψ : FormVector L) (y : Space)
    {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hy : t+2*b ≤ ‖y‖)
    (c : Fin L → Fin 2) (s : Spins (cutOutNumber c)) (u : Configuration (cutOutNumber c))
    (hm : formMass (coreSlice (orderedCutForm (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ c) s u) ≠ 0) (i : Fin (cutOutNumber c)) :
    b ≤ ‖u i‖ := by
  have hi : ‖u i-y‖ < t+b := by
    by_contra! h
    apply hm
    exact orderedCutForm_slice_mass_zero _ _ ψ c s u i (coreFirstRadialCut_out_zero y ht hb _ h)
  have hn := norm_le_norm_sub_add y (u i)
  rw [norm_sub_rev y (u i)] at hn
  linarith

lemma radial_conditionalOutMaximum_bound {L : ℕ} (ψ : FormVector L) (y : Space)
    {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hy : t+2*b ≤ ‖y‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (c : Fin L → Fin 2)
    (s : Spins (cutOutNumber c)) (u : Configuration (cutOutNumber c)) :
    conditionalOutMaximum Z lam (orderedCutForm (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ c) s u ≤ Z/b := by
  apply conditionalOutMaximum_le _ _ _ _ _ (by positivity)
  intro i
  by_cases hm : formMass (coreSlice (orderedCutForm (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ c) s u) = 0
  · simp only [normalizedCoreField,hm,mul_zero,div_zero,zero_sub]
    exact (neg_nonpos.mpr hlam).trans (by positivity)
  · exact (normalizedCoreField_le_nuclear _ hZ hlam _).trans
      (div_le_div_of_nonneg_left hZ hb (radial_out_position_nuclear ψ y ht hb hy c s u hm i))

lemma radial_outMaximum_square_integrable {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hy : t+2*b ≤ ‖y‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (c : Fin L → Fin 2)
    (s : Spins (cutOutNumber c)) :
    let χ := orderedCutForm (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) ψ c
    Integrable (fun u => conditionalOutMaximum Z lam χ s u^2*formMass (coreSlice χ s u)) := by
  dsimp only
  have hχ := orderedCutForm_sobolev (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) hψ c
  exact (hχ.coreSlice_mass_integrable s).bdd_mul
    ((conditionalOutMaximum_aemeasurable hχ s Z lam).pow_const 2).aestronglyMeasurable
    (ae_of_all _ (fun u => norm_sq_le_of_nonneg (conditionalOutMaximum_nonneg _ _ _ _ _)
      (radial_conditionalOutMaximum_bound ψ y ht hb hy hZ hlam c s u)))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CoreSubmeanBarrier
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombAtom
open CoulombAnalysis

lemma radial_translatedDensity_core_le {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) {η : Space → ℝ} (hm : Measurable η)
    {R B : ℝ} (hR : 0 ≤ R) (hn : ∀ x, 0 ≤ η x)
    (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : ∀ x, |η x| ≤ B)
    (hr : IsRadial η) (h1 : ∫ x : Space, η x = 1) (y : Space) :
    coreDensityInteraction ψ (translatedDensity η y) ≤ coreCoulombAt ψ y := by
  have hsupport : Function.support η ⊆ closedBall 0 R :=
    fun x hx => by simpa only [mem_closedBall,dist_zero_right] using hs x hx
  have hi := bounded_compact_integrable hm (isCompact_closedBall _ _) hsupport hb
  have hp := bounded_compact_memLp hm (isCompact_closedBall _ _) hsupport hb (5/3 : ENNReal)
  have htm := translatedDensity_measurable hm y
  have hts := translatedDensity_support hs y
  have hti := bounded_compact_integrable htm (isCompact_closedBall _ _) hts (fun z => hb (z-y))
  have htp := bounded_compact_memLp htm (isCompact_closedBall _ _) hts (fun z => hb (z-y)) (5/3 : ENNReal)
  obtain ⟨C,hC⟩ := compact_support_potential_bounded hti htp (isCompact_closedBall y R) hts
  apply Finset.sum_le_sum
  intro s _
  apply Finset.sum_le_sum
  intro i _
  apply integral_mono_ae
    (core_bounded_potential_integrable hψ (tfPotential_continuous hti htp) hC s i)
    (hψ.shifted_nuclear_integrable s i y)
  filter_upwards [Measure.ae_eval_ne (fun _ : Fin N => (volume : Measure Space)) i y] with x hx
  rw [potential_translatedDensity]
  have he := radial_potential_le_point hi hp hn hr hR hs (sub_ne_zero.mpr hx)
  rw [h1] at he
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left he (sq_nonneg ‖ψ.value s x‖)

theorem normalizedCoreField_radial_submean {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) {η : Space → ℝ} (hm : Measurable η)
    {R B : ℝ} (hR : 0 < R) (hn : ∀ x, 0 ≤ η x)
    (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : ∀ x, |η x| ≤ B)
    (hr : IsRadial η) (h1 : ∫ x : Space, η x = 1)
    (y : Space) (hnuc : R ≤ ‖y‖) (Z lam : ℝ) :
    normalizedCoreField Z lam ψ y ≤
      ∫ z, normalizedCoreField Z lam ψ z*η (z-y) := by
  change _ ≤ ∫ z, normalizedCoreField Z lam ψ z*translatedDensity η y z
  rw [normalizedCoreField_pairing hψ (translatedDensity_measurable hm y)
    (isCompact_closedBall y R) (translatedDensity_support hs y) (fun z => hb (z-y)),
    radial_translatedDensity_potential hm hR hs hb hr h1 y 0
      (by simpa only [zero_sub,norm_neg] using hnuc),
    translatedDensity_mass,h1,zero_sub,norm_neg,mul_one]
  apply sub_le_sub_right
  apply div_le_div_of_nonneg_right _ (formMass_nonneg ψ)
  rw [mul_one_div]
  exact sub_le_sub_left (radial_translatedDensity_core_le hψ hm hR.le hn hs hb hr h1 y) _

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_CoreSubmeanSquareBarrier
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators

namespace CoulombAtom
open CoulombAnalysis

lemma positive_core_pair_integrable {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) {η : Space → ℝ} (hη : Integrable η)
    (hm : Measurable η) (hn : ∀ z, 0 ≤ η z)
    {Z lam d : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hd : 0 < d)
    (hs : ∀ z, η z ≠ 0 → d ≤ ‖z‖) (k : ℕ) :
    Integrable (fun z => (max (normalizedCoreField Z lam ψ z) 0)^k*η z) := by
  apply (hη.const_mul ((Z/d)^k)).mono'
    (((normalizedCoreField_measurable hψ Z lam).max measurable_const).pow_const k |>.mul hm).aestronglyMeasurable
  apply ae_of_all; intro z
  change ‖(max (normalizedCoreField Z lam ψ z) 0)^k*η z‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (le_max_right _ _) _) (hn z))]
  by_cases he : η z = 0
  · simp only [he,mul_zero,le_refl]
  · exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (le_max_right _ _) (normalizedCoreField_pos_le ψ hZ hlam hd (hs z he)) k) (hn z)

theorem normalizedCoreField_radial_submean_sq {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) {η : Space → ℝ} (hm : Measurable η)
    {R B : ℝ} (hR : 0 < R) (hn : ∀ x, 0 ≤ η x)
    (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : ∀ x, |η x| ≤ B)
    (hr : IsRadial η) (h1 : ∫ x : Space, η x = 1)
    (y : Space) (hnuc : 2*R ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    (max (normalizedCoreField Z lam ψ y) 0)^2 ≤
      ∫ z, (max (normalizedCoreField Z lam ψ z) 0)^2*η (z-y) := by
  let k := translatedDensity η y
  have hkm : Measurable k := translatedDensity_measurable hm y
  have hks : Function.support k ⊆ closedBall y R := translatedDensity_support hs y
  have hkb : ∀ z, |k z| ≤ B := fun z => hb (z-y)
  have hki : Integrable k := bounded_compact_integrable hkm (isCompact_closedBall _ _) hks hkb
  have hkn (z : Space) : 0 ≤ k z := hn (z-y)
  have hk1 : ∫ z, k z = 1 := (translatedDensity_mass η y).trans h1
  have hsep : ∀ z, k z ≠ 0 → R ≤ ‖z‖ := by
    intro z hz
    have hz0 := hs (z-y) hz
    have htri : ‖y‖ ≤ ‖z-y‖+‖z‖ := by
      calc
        ‖y‖ = ‖z-(z-y)‖ := by congr 1; abel
        _ ≤ ‖z‖+‖z-y‖ := norm_sub_le _ _
        _ = ‖z-y‖+‖z‖ := add_comm _ _
    linarith
  have hf1 : Integrable (fun z => max (normalizedCoreField Z lam ψ z) 0*k z) := by
    simpa only [pow_one] using positive_core_pair_integrable hψ hki hkm hkn hZ hlam hR hsep 1
  have hf2 := positive_core_pair_integrable hψ hki hkm hkn hZ hlam hR hsep 2
  have hh := normalizedCoreField_radial_submean hψ hm hR hn hs hb hr h1 y (by linarith) Z lam
  have hp : max (normalizedCoreField Z lam ψ y) 0 ≤
      ∫ z, max (normalizedCoreField Z lam ψ z) 0*k z := by
    apply max_le
    · apply hh.trans
      exact integral_mono (normalizedCoreField_pair_integrable hψ hkm (isCompact_closedBall _ _) hks hkb Z lam)
        hf1 (fun z => mul_le_mul_of_nonneg_right (le_max_left _ _) (hkn z))
    · exact integral_nonneg (fun z => mul_nonneg (le_max_right _ _) (hkn z))
  have hc := weighted_sum_integral_cauchy (ι := Unit) (X := fun _ => Space)
    (fun _ => volume) (fun _ => k) (fun _ z => max (normalizedCoreField Z lam ψ z) 0)
    (fun _ _ => 1) (fun _ => hkn) (fun _ => hf2)
    (fun _ => by simpa only [one_pow,one_mul] using hki)
    (fun _ => by simpa only [mul_one] using hf1)
  simp only [Finset.univ_unique,Finset.sum_singleton,one_pow,one_mul,mul_one,hk1,Real.sqrt_one] at hc
  have hi : 0 ≤ ∫ z, (max (normalizedCoreField Z lam ψ z) 0)^2*k z :=
    integral_nonneg (fun z => mul_nonneg (sq_nonneg _) (hkn z))
  have hb0 := (sq_le_sq₀ (le_max_right _ _) (Real.sqrt_nonneg _)).mpr (hp.trans hc)
  rwa [Real.sq_sqrt hi] at hb0

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_OutMaximumSubmeanBarrier
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators

namespace CoulombAtom
open CoulombAnalysis

lemma core_field_square_ball_integrable {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (y : Space) {A d : ℝ}
    (hd : 0 < d) (hsep : A+d ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    IntegrableOn (fun z => (max (normalizedCoreField Z lam ψ z) 0)^2) (closedBall y A) := by
  let w : Space → ℝ := (closedBall y A).indicator (fun _ => 1)
  have hwm : Measurable w := measurable_const.indicator isClosed_closedBall.measurableSet
  have hwn (z : Space) : 0 ≤ w z := by
    by_cases hz : z ∈ closedBall y A <;> simp [w,hz]
  have hwi : Integrable w := bounded_compact_integrable hwm (isCompact_closedBall y A)
    (by intro z hz; by_contra hz0; exact hz (by simp [w,hz0]))
    (B := 1) (fun z => by by_cases hz : z ∈ closedBall y A <;> simp [w,hz])
  have hwsep : ∀ z, w z ≠ 0 → d ≤ ‖z‖ := by
    intro z hz
    have hzd : ‖z-y‖ ≤ A := by
      by_contra hh
      have hn : z ∉ closedBall y A := by simpa only [mem_closedBall,dist_eq_norm] using hh
      exact hz (by simp [w,hn])
    have htri := norm_le_norm_sub_add y z
    rw [norm_sub_rev y z] at htri
    linarith
  have hi := positive_core_pair_integrable hψ hwi hwm hwn hZ hlam hd hwsep 2
  rw [←integrable_indicator_iff isClosed_closedBall.measurableSet]
  have heq : (closedBall y A).indicator (fun z => (max (normalizedCoreField Z lam ψ z) 0)^2) =
      (fun z => w z * (max (normalizedCoreField Z lam ψ z) 0)^2) := by
    funext z
    by_cases hz : z ∈ closedBall y A <;> simp [w,hz]
  rw [heq]
  simpa only [mul_comm] using hi

theorem conditional_out_maximum_sq_le_ball_average {N M : ℕ} (ψ : FormVector (N+M))
    (s : Spins M) (u : Configuration M) (hψ : SobolevVector (coreSlice ψ s u))
    (y : Space) {a R B Z lam : ℝ} (_ha : 0 ≤ a) (hR : 0 < R)
    (hsep : a+2*R ≤ ‖y‖) (hu : ∀ i, ‖u i-y‖ ≤ a)
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) {η : Space → ℝ}
    (hm : Measurable η) (hn : ∀ z, 0 ≤ η z)
    (hs : ∀ z, η z ≠ 0 → ‖z‖ ≤ R) (hb : ∀ z, |η z| ≤ B)
    (hr : IsRadial η) (h1 : ∫ z, η z = 1) :
    conditionalOutMaximum Z lam ψ s u^2 ≤
      B*∫ z in closedBall y (a+R), (max (normalizedCoreField Z lam (coreSlice ψ s u) z) 0)^2 := by
  let F : Space → ℝ := fun z => (max (normalizedCoreField Z lam (coreSlice ψ s u) z) 0)^2
  have hB : 0 ≤ B := (abs_nonneg (η 0)).trans (hb 0)
  have hFi : IntegrableOn F (closedBall y (a+R)) :=
    core_field_square_ball_integrable hψ y hR (by linarith) hZ hlam
  have hQ : 0 ≤ B*∫ z in closedBall y (a+R), F z :=
    mul_nonneg hB (integral_nonneg (fun z => sq_nonneg _))
  have hF (i : Fin M) : F (u i) ≤ B*∫ z in closedBall y (a+R), F z := by
    have hnuc : 2*R ≤ ‖u i‖ := by
      have htri := norm_le_norm_sub_add y (u i)
      rw [norm_sub_rev y (u i)] at htri
      linarith [hu i]
    have hi := normalizedCoreField_radial_submean_sq hψ hm hR hn hs hb hr h1 (u i) hnuc hZ hlam
    apply hi.trans
    let k := translatedDensity η (u i)
    have hkm : Measurable k := translatedDensity_measurable hm _
    have hkn (z : Space) : 0 ≤ k z := hn (z-u i)
    have hki : Integrable k := bounded_compact_integrable hkm (isCompact_closedBall _ _)
      (translatedDensity_support hs _) (fun z => hb (z-u i))
    have hks : ∀ z, k z ≠ 0 → R ≤ ‖z‖ := by
      intro z hz
      have htri := norm_le_norm_sub_add (u i) z
      rw [norm_sub_rev (u i) z] at htri
      linarith [hs (z-u i) hz]
    have hleft := positive_core_pair_integrable hψ hki hkm hkn hZ hlam hR hks 2
    rw [←integral_const_mul,←integral_indicator isClosed_closedBall.measurableSet]
    apply integral_mono hleft ((integrable_indicator_iff isClosed_closedBall.measurableSet).2 (hFi.const_mul B))
    intro z
    by_cases hz : z ∈ closedBall y (a+R)
    · rw [indicator_of_mem hz]
      simpa only [k,translatedDensity,F,mul_comm] using
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hb (z-u i)))
          (sq_nonneg (max (normalizedCoreField Z lam (coreSlice ψ s u) z) 0))
    · rw [indicator_of_notMem hz]
      have hk0 : η (z-u i) = 0 := by
        by_contra hk
        have hnz := norm_sub_le_norm_sub_add_norm_sub z (u i) y
        have hh := hs (z-u i) hk
        exact hz (by rw [mem_closedBall,dist_eq_norm]; linarith [hu i])
      simp only [k,translatedDensity,hk0,mul_zero,le_refl]
  have hh : conditionalOutMaximum Z lam ψ s u ≤
      Real.sqrt (B*∫ z in closedBall y (a+R), F z) := by
    apply conditionalOutMaximum_le _ _ _ _ _ (Real.sqrt_nonneg _)
    intro i
    apply (le_max_left _ _).trans
    apply (sq_le_sq₀ (le_max_right _ _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hQ]
    exact hF i
  have hh2 := (sq_le_sq₀ (conditionalOutMaximum_nonneg _ _ _ _ _) (Real.sqrt_nonneg _)).mpr hh
  rwa [Real.sq_sqrt hQ] at hh2

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CutCoreExcess
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
namespace CoulombAtom

def cutExteriorPrice {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (Z lam : ℝ)
    (ψ : FormVector L) (b : Fin L → Fin 2) : ℝ :=
  formEnergy Z (orderedCutForm p hp ψ b)-cutCoreEnergy p hp Z ψ b+
    lam*cutOutNumber b*formMass (orderedCutForm p hp ψ b)

theorem fock_cut_excess_identity {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevVector ψ) (Z lam : ℝ) :
    (∑ b : Fin L → Fin 2, cutCoreExcess p hp Z lam ψ b)+
      (∑ b : Fin L → Fin 2, cutExteriorPrice p hp Z lam ψ b) =
        corePriceExcess Z lam ψ+(1/2:ℝ)*weightedParticleCount ψ (spatialErrorWeight p) := by
  rw [← Finset.sum_add_distrib]
  have hb (b : Fin L → Fin 2) :
      cutCoreExcess p hp Z lam ψ b+cutExteriorPrice p hp Z lam ψ b =
      formEnergy Z (orderedCutForm p hp ψ b)+
        (lam*L-priceEnergy (energy Z) lam)*formMass (orderedCutForm p hp ψ b) := by
    have hcard : (cutCoreNumber b : ℝ)+cutOutNumber b = L := by
      exact_mod_cast cutNumbers_sum b
    unfold cutCoreExcess cutExteriorPrice
    rw [← hcard]
    ring
  simp_rw [hb,orderedCutForm_energy,orderedCutForm_mass]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,spatial_cut_mass p hp hψ,
    spatial_cut_ims p hp hψ Z]
  unfold corePriceExcess weightedParticleCount
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_QuantumFieldExcessBarrier
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators

open MeasureTheory Filter Set Metric
open scoped BigOperators

lemma normalizedCoreField_mass_le_cut_envelope {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (y : Space) {B : ℝ}
    (hB : 0 < B) (hnuc : 2*B ≤ ‖y‖)
    (hv : ∀ x ∈ ball y (2*B), (p 0).value x = 0)
    (hd : ∀ x ∈ ball y (2*B), ∀ a, lineDeriv ℝ (p 0).value x (spaceDirections a) = 0)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    normalizedCoreField Z lam ψ y*formMass ψ ≤
      ∑ c : Fin L → Fin 2, ∑ t : Spins (cutOutNumber c), ∫ u,
        coreCapEnvelope Z lam B (coreSlice (orderedCutForm p hp ψ c) t u)*
          formMass (coreSlice (orderedCutForm p hp ψ c) t u) := by
  have ht := fresh_cut_field_tower p hp hψ.sobolevVector Z lam y
  rw [integral_rawPotential_formRawLaw hψ.sobolevVector] at ht
  have he : (Z/‖y‖-lam)*formMass ψ-coreCoulombAt ψ y = normalizedCoreField Z lam ψ y*formMass ψ := by
    rw [normalizedCoreField_mul_mass hψ.sobolevVector]
    ring
  rw [he] at ht
  rw [←ht]
  apply Finset.sum_le_sum; intro c _
  apply Finset.sum_le_sum; intro t _
  have hχ := orderedCutForm_sobolev p hp hψ.sobolevVector c
  have hleft : Integrable (fun u =>
      (normalizedCoreField Z lam (coreSlice (orderedCutForm p hp ψ c) t u) y-rawPotential y u)*
        formMass (coreSlice (orderedCutForm p hp ψ c) t u)) := by
    have hi := (normalizedCoreField_weighted_integrable hχ t Z lam y).sub
      (rawPotential_coreSlice_integrable hχ t y)
    convert hi using 1
    all_goals try with_reducible_and_instances rfl
    ext u
    simp only [Pi.sub_apply]
    ring
  apply integral_mono_ae hleft
    (coreSlice_envelope_first_integrable (orderedCutForm_core_antisymmetric p hp hψ c) hχ hZ hlam hB t)
  apply (fresh_cut_field_envelope p hp hψ c y hB hnuc hv hd hZ hlam t).mono
  intro u hu
  apply mul_le_mul_of_nonneg_right _ (formMass_nonneg _)
  exact (sub_le_self _ (rawPotential_nonneg y u)).trans
    (hu y (mem_closedBall_self hB.le))

theorem parent_field_sq_mass_le_fresh_core_excess {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (y : Space) {B : ℝ}
    (hB : 0 < B) (hnuc : 2*B ≤ ‖y‖)
    (hv : ∀ x ∈ ball y (2*B), (p 0).value x = 0)
    (hd : ∀ x ∈ ball y (2*B), ∀ a, lineDeriv ℝ (p 0).value x (spaceDirections a) = 0)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    (max (normalizedCoreField Z lam ψ y) 0)^2*formMass ψ ≤
      2*packetFieldConstant^2*((1/B^4+1/B)^2*formMass ψ+
        (∑ c : Fin L → Fin 2, cutCoreExcess p hp Z lam ψ c)/B) := by
  let Q := ∑ c : Fin L → Fin 2, ∑ t : Spins (cutOutNumber c), ∫ u,
    formMass (coreSlice (orderedCutForm p hp ψ c) t u)*
      (coreCapEnvelope Z lam B (coreSlice (orderedCutForm p hp ψ c) t u))^2
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun c _ => Finset.sum_nonneg
    (fun t _ => integral_nonneg (fun u => mul_nonneg (formMass_nonneg _) (sq_nonneg _))))
  have hsq : (max (normalizedCoreField Z lam ψ y) 0)^2*formMass ψ ≤ Q := by
    by_cases hm : formMass ψ = 0
    · simpa only [hm,mul_zero] using hQ
    have hmass : 0 < formMass ψ := lt_of_le_of_ne (formMass_nonneg _) (Ne.symm hm)
    have hh : max (normalizedCoreField Z lam ψ y) 0*formMass ψ ≤
        Real.sqrt Q*Real.sqrt (formMass ψ) := by
      rw [max_mul_of_nonneg _ _ hmass.le,zero_mul]
      exact max_le
        ((normalizedCoreField_mass_le_cut_envelope p hp hψ y hB hnuc hv hd hZ hlam).trans
          (fock_cut_envelope_first_le_sqrt_mass p hp hψ hZ hlam hB))
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have hh2 := (sq_le_sq₀
      (mul_nonneg (le_max_right _ _) hmass.le)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hh
    rw [mul_pow, mul_pow, Real.sq_sqrt hQ, Real.sq_sqrt hmass.le] at hh2
    exact (mul_le_mul_iff_left₀ hmass).mp (by nlinarith only [hh2])
  exact hsq.trans (fock_cut_envelope_square p hp hψ hZ hlam hB)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_CoreHistoryAverageBarrier
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators

lemma coreLawAverage_next_excess {N M : ℕ} {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2) (Z lam : ℝ) :
    coreLawAverage (nextCoreObservation p hp ψ c) (corePriceExcess Z lam) =
      ∑ t : Spins M, ∫ v, cutCoreExcess p hp Z lam (coreSlice ψ t v) c :=
by
  rw [coreLawAverage_next ψ p hp c (corePriceExcess Z lam)
    (fun s => (nextCoreObservation_sobolev hψ p hp c).coreSlice_excess_integrable Z lam s)]
  apply Finset.sum_congr rfl
  intro t _
  apply integral_congr_ae
  filter_upwards [hψ.ae_coreSlice t] with v hv
  exact coreLawAverage_ordered_excess hv p hp c Z lam

open MeasureTheory Filter
open scoped BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_CoreHistoryMassBarrier
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators

namespace CoulombAtom

lemma sum_nextCoreObservation_excess {N M : ℕ} {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (Z lam : ℝ) :
    (∑ c : Fin N → Fin 2,
      coreLawAverage (nextCoreObservation p hp ψ c) (corePriceExcess Z lam)) =
      ∑ t : Spins M, ∫ v, ∑ c : Fin N → Fin 2, cutCoreExcess p hp Z lam (coreSlice ψ t v) c := by
  simp_rw [coreLawAverage_next_excess hψ p hp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  exact (integral_finsetSum _ (fun c _ =>
    nextCoreObservation_excess_statistic_integrable hψ p hp c t Z lam)).symm

namespace CoreObservationGraph

lemma mass_nonneg (G : CoreObservationGraph) : 0 ≤ G.mass := formMass_nonneg _

end CoreObservationGraph
end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_CoreHistoryFieldBarrier
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators

namespace CoulombAtom

lemma sum_nextCoreObservation_fieldSquare {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (y : Space) :
    (∑ c : Fin N → Fin 2,
      coreLawAverage (nextCoreObservation p hp ψ c) (coreFieldSquare Z lam y)) =
      ∑ t : Spins M, ∫ v, ∑ c : Fin N → Fin 2,
        coreLawAverage (orderedCutForm p hp (coreSlice ψ t v) c) (coreFieldSquare Z lam y) := by
  have hi (c : Fin N → Fin 2) (s : Spins (cutOutNumber c+M)) :=
    coreFieldSquare_coreSlice_integrable (nextCoreObservation_sobolev hψ p hp c) s hZ hlam y
  have ht (c : Fin N → Fin 2) := coreLawAverage_next ψ p hp c
    (coreFieldSquare Z lam y) (hi c)
  simp_rw [ht]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  exact (integral_finsetSum _ (fun c _ =>
    nextCoreObservation_statistic_integrable ψ p hp c _ (hi c) t)).symm

namespace CoreObservationGraph

theorem fieldMoment_le_observe_excess (G : CoreObservationGraph)
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (y : Space) {B : ℝ}
    (hB : 0 < B) (hnuc : 2*B ≤ ‖y‖)
    (hv : ∀ x ∈ ball y (2*B), (p 0).value x = 0)
    (hd : ∀ x ∈ ball y (2*B), ∀ a, lineDeriv ℝ (p 0).value x (spaceDirections a) = 0)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    G.fieldMoment Z lam y ≤ 2*packetFieldConstant^2*((1/B^4+1/B)^2*G.mass+
      (∑ c : Fin G.coreSize → Fin 2, (G.observe p hp c).excess Z lam)/B) := by
  have hi (t : Spins G.outSize) := integrable_finsetSum Finset.univ (fun c _ =>
    nextCoreObservation_excess_statistic_integrable G.sobolev p hp c t Z lam)
  have hbound (t : Spins G.outSize) :
      (∫ v, coreFieldSquare Z lam y (coreSlice G.vector t v)) ≤
        ∫ v, 2*packetFieldConstant^2*((1/B^4+1/B)^2*formMass (coreSlice G.vector t v)+
          (∑ c : Fin G.coreSize → Fin 2, cutCoreExcess p hp Z lam (coreSlice G.vector t v) c)/B) := by
    apply integral_mono_ae (coreFieldSquare_coreSlice_integrable G.sobolev t hZ hlam.le y)
      (((G.sobolev.coreSlice_mass_integrable t).const_mul _ |>.add ((hi t).div_const B)).const_mul _)
    filter_upwards [G.antisymmetric.ae_coreSlice G.sobolev t] with v hvs
    exact parent_field_sq_mass_le_fresh_core_excess p hp hvs y hB hnuc hv hd hZ hlam
  have he (t : Spins G.outSize) :
      (∫ v, 2*packetFieldConstant^2*((1/B^4+1/B)^2*formMass (coreSlice G.vector t v)+
        (∑ c : Fin G.coreSize → Fin 2, cutCoreExcess p hp Z lam (coreSlice G.vector t v) c)/B)) =
      2*packetFieldConstant^2*((1/B^4+1/B)^2*(∫ v, formMass (coreSlice G.vector t v))+
        (∫ v, ∑ c : Fin G.coreSize → Fin 2, cutCoreExcess p hp Z lam (coreSlice G.vector t v) c)/B) := by
    rw [integral_const_mul,integral_add ((G.sobolev.coreSlice_mass_integrable t).const_mul _)
      ((hi t).div_const B),integral_const_mul,integral_div]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun t _ => hbound t)
  simp_rw [he] at hh
  simp only [←Finset.mul_sum,Finset.sum_add_distrib,←Finset.sum_div] at hh
  rw [G.sobolev.integral_coreSlice_mass] at hh
  change G.fieldMoment Z lam y ≤ _ at hh
  change G.fieldMoment Z lam y ≤ 2*packetFieldConstant^2*((1/B^4+1/B)^2*formMass G.vector+
    (∑ c : Fin G.coreSize → Fin 2,
      coreLawAverage (nextCoreObservation p hp G.vector c) (corePriceExcess Z lam))/B)
  rw [sum_nextCoreObservation_excess G.sobolev p hp Z lam]
  exact hh

end CoreObservationGraph
end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_CoreHistoryFieldFubiniBarrier
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators

namespace CoulombAtom

lemma coreFieldSquare_weighted_fubini {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z lam : ℝ) {d : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hd : 0 < d) {w : Space → ℝ}
    (hw : Integrable w) (hn : ∀ z, 0 ≤ w z) (hs : ∀ z, w z ≠ 0 → d ≤ ‖z‖) :
    coreLawAverage ψ (fun φ => ∫ z, coreFieldSquare Z lam z φ*w z) =
      ∫ z, coreLawAverage ψ (coreFieldSquare Z lam z)*w z := by
  unfold coreLawAverage
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro t _
    rw [integral_integral_swap (coreFieldSquare_weighted_prod_integrable hψ t hZ hlam hd hw hn hs)]
    apply integral_congr_ae
    exact ae_of_all _ (fun z => integral_mul_const (w z) _)
  · intro t _
    have hi := (coreFieldSquare_weighted_prod_integrable hψ t hZ hlam hd hw hn hs).integral_prod_right
    simpa only [integral_mul_const] using hi

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_CoreHistoryOutMaximumBarrier
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators

def conditionalBlockMaximum {N K M : ℕ} (Z lam : ℝ) (ψ : FormVector (N+(K+M)))
    (s : Spins (K+M)) (u : Configuration (K+M)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun o : Option (Fin K) =>
    o.elim 0 (fun i => normalizedCoreField Z lam (coreSlice ψ s u) (leftList u i)))

lemma conditionalBlockMaximum_nonneg {N K M : ℕ} (Z lam : ℝ)
    (ψ : FormVector (N+(K+M))) (s : Spins (K+M)) (u : Configuration (K+M)) :
    0 ≤ conditionalBlockMaximum (K := K) Z lam ψ s u :=
  Finset.le_sup' (fun o : Option (Fin K) =>
    o.elim 0 (fun i => normalizedCoreField Z lam (coreSlice ψ s u) (leftList u i)))
    (Finset.mem_univ none)

lemma conditionalBlockMaximum_aemeasurable {N K M : ℕ} {ψ : FormVector (N+(K+M))}
    (hψ : SobolevVector ψ) (s : Spins (K+M)) (Z lam : ℝ) :
    AEMeasurable (conditionalBlockMaximum (K := K) Z lam ψ s) := by
  obtain ⟨F,hF,he⟩ := coreSlice_field_measurable_rep hψ s Z lam
  let f : Option (Fin K) → Configuration (K+M) → ℝ :=
    fun o u => o.elim 0 (fun i => F (u,leftList u i))
  have hf (o : Option (Fin K)) : Measurable (f o) := by
    cases o with
    | none => exact measurable_const
    | some i => exact hF.comp (measurable_id.prodMk (measurable_pi_apply _))
  have hh := Finset.measurable_sup' Finset.univ_nonempty (fun i (_ : i ∈ Finset.univ) => hf i)
  apply hh.aemeasurable.congr
  filter_upwards [he] with u hu
  simp only [Finset.sup'_apply]
  unfold conditionalBlockMaximum
  congr 1
  funext o
  cases o with
  | none => rfl
  | some i => exact hu _

lemma conditionalBlockMaximum_next_join {N M : ℕ} (ψ : FormVector (N+M))
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2)
    (s : Spins (cutOutNumber c)) (t : Spins M)
    (u : Configuration (cutOutNumber c)) (v : Configuration M) (Z lam : ℝ) :
    conditionalBlockMaximum (K := cutOutNumber c) Z lam (nextCoreObservation p hp ψ c)
      (joinLists s t) (joinLists u v) =
      conditionalOutMaximum Z lam (orderedCutForm p hp (coreSlice ψ t v) c) s u := by
  simp only [conditionalBlockMaximum,conditionalOutMaximum,nextCoreObservation_slice,leftList_join]

lemma radial_nextBlockMaximum_bound {N M : ℕ} (ψ : FormVector (N+M))
    (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hy : t+2*b ≤ ‖y‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (c : Fin N → Fin 2)
    (s : Spins (cutOutNumber c+M)) (u : Configuration (cutOutNumber c+M)) :
    conditionalBlockMaximum (K := cutOutNumber c) Z lam
      (nextCoreObservation (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) ψ c) s u ≤ Z/b := by
  conv_lhs => rw [←join_list_parts s,←join_list_parts u]
  rw [conditionalBlockMaximum_next_join]
  exact radial_conditionalOutMaximum_bound _ y ht hb hy hZ hlam c _ _

lemma radial_nextBlockMaximum_square_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (hy : t+2*b ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam)
    (c : Fin N → Fin 2) (s : Spins (cutOutNumber c+M)) :
    let χ := nextCoreObservation (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) ψ c
    Integrable (fun u => conditionalBlockMaximum (K := cutOutNumber c) Z lam χ s u^2*
      formMass (coreSlice χ s u)) := by
  dsimp only
  have hχ := nextCoreObservation_sobolev hψ (coreFirstRadialCut y ht hb)
    (coreFirstRadialCut_partition y ht hb) c
  exact (hχ.coreSlice_mass_integrable s).bdd_mul
    ((conditionalBlockMaximum_aemeasurable hχ s Z lam).pow_const 2).aestronglyMeasurable
    (ae_of_all _ (fun u => norm_sq_le_of_nonneg (conditionalBlockMaximum_nonneg _ _ _ _ _)
      (radial_nextBlockMaximum_bound ψ y ht hb hy hZ hlam c s u)))

lemma nextBlockMaximum_square_fubini {N M : ℕ} (ψ : FormVector (N+M))
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2) (Z lam : ℝ)
    (hi : ∀ s, Integrable (fun u => conditionalBlockMaximum (K := cutOutNumber c) Z lam
      (nextCoreObservation p hp ψ c) s u^2*formMass (coreSlice (nextCoreObservation p hp ψ c) s u))) :
    (∑ s : Spins (cutOutNumber c+M), ∫ u,
      conditionalBlockMaximum (K := cutOutNumber c) Z lam (nextCoreObservation p hp ψ c) s u^2*
        formMass (coreSlice (nextCoreObservation p hp ψ c) s u)) =
      ∑ t : Spins M, ∫ v, ∑ s : Spins (cutOutNumber c), ∫ u,
        conditionalOutMaximum Z lam (orderedCutForm p hp (coreSlice ψ t v) c) s u^2*
          formMass (coreSlice (orderedCutForm p hp (coreSlice ψ t v) c) s u) := by
  rw [←sum_spin_join]
  apply Finset.sum_congr rfl
  intro t _
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro s _
    rw [←integral_join (hi (joinLists s t))]
    simp only [conditionalBlockMaximum_next_join,nextCoreObservation_slice]
  · intro s _
    have hh := (integrable_join (hi (joinLists s t))).integral_prod_right
    simpa only [conditionalBlockMaximum_next_join,nextCoreObservation_slice] using hh

lemma nextBlockMaximum_square_statistic_integrable {N M : ℕ} (ψ : FormVector (N+M))
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2) (Z lam : ℝ)
    (hi : ∀ s, Integrable (fun u => conditionalBlockMaximum (K := cutOutNumber c) Z lam
      (nextCoreObservation p hp ψ c) s u^2*formMass (coreSlice (nextCoreObservation p hp ψ c) s u)))
    (t : Spins M) : Integrable (fun v => ∑ s : Spins (cutOutNumber c), ∫ u,
        conditionalOutMaximum Z lam (orderedCutForm p hp (coreSlice ψ t v) c) s u^2*
          formMass (coreSlice (orderedCutForm p hp (coreSlice ψ t v) c) s u)) := by
  apply integrable_finsetSum
  intro s _
  have hh := (integrable_join (hi (joinLists s t))).integral_prod_right
  simpa only [conditionalBlockMaximum_next_join,nextCoreObservation_slice] using hh

open MeasureTheory Filter Set Metric
open scoped BigOperators

open CoulombAnalysis

lemma fieldSquare_ball_weight_eq {N : ℕ} (ψ : FormVector N) (Z lam : ℝ)
    (y : Space) (A : ℝ) :
    (∫ z, coreFieldSquare Z lam z ψ*(closedBall y A).indicator (fun _ => (1:ℝ)) z) =
      ∫ z in closedBall y A, coreFieldSquare Z lam z ψ := by
  rw [←integral_indicator isClosed_closedBall.measurableSet]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  by_cases hz : z ∈ closedBall y A <;> simp [hz]

lemma coreFieldSquare_ball_statistic_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (y : Space) {A d Z lam : ℝ}
    (hd : 0 < d) (hsep : A+d ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    Integrable (fun u => ∫ z in closedBall y A, coreFieldSquare Z lam z (coreSlice ψ t u)) := by
  have hi := (coreFieldSquare_weighted_prod_integrable hψ t hZ hlam hd
    (ball_one_integrable y A)
    (fun z => indicator_nonneg (fun _ _ => zero_le_one) z)
    (ball_indicator_nuclear_separation y hsep)).integral_prod_left
  simpa only [fieldSquare_ball_weight_eq] using hi

lemma coreFieldSquare_ball_fubini {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (y : Space) {A d Z lam : ℝ}
    (hd : 0 < d) (hsep : A+d ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    coreLawAverage ψ (fun φ => ∫ z in closedBall y A, coreFieldSquare Z lam z φ) =
      ∫ z in closedBall y A, coreLawAverage ψ (coreFieldSquare Z lam z) := by
  have hh := coreFieldSquare_weighted_fubini hψ Z lam hZ hlam hd (ball_one_integrable y A)
    (fun z => indicator_nonneg (fun _ _ => zero_le_one) z)
    (ball_indicator_nuclear_separation y hsep)
  simp only [fieldSquare_ball_weight_eq] at hh
  rw [hh,←integral_indicator isClosed_closedBall.measurableSet]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  by_cases hz : z ∈ closedBall y A <;> simp [hz]

lemma radial_out_position_distance {L : ℕ} (ψ : FormVector L) (y : Space)
    {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (c : Fin L → Fin 2)
    (s : Spins (cutOutNumber c)) (u : Configuration (cutOutNumber c))
    (hm : formMass (coreSlice (orderedCutForm (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ c) s u) ≠ 0) (i : Fin (cutOutNumber c)) :
    ‖u i-y‖ < t+b := by
  by_contra! h
  exact hm (orderedCutForm_slice_mass_zero _ _ ψ c s u i (coreFirstRadialCut_out_zero y ht hb _ h))

theorem radial_nextBlockMaximum_sq_spatial {N M : ℕ} (ψ : FormVector (N+M))
    (y : Space) {t b R B Z lam : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hR : 0 < R)
    (hsep : t+b+2*R ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam)
    (c : Fin N → Fin 2) (s : Spins (cutOutNumber c+M)) (u : Configuration (cutOutNumber c+M))
    (hcore : SobolevVector (coreSlice (nextCoreObservation (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ c) s u)) {η : Space → ℝ}
    (hm : Measurable η) (hn : ∀ z, 0 ≤ η z) (hs : ∀ z, η z ≠ 0 → ‖z‖ ≤ R)
    (hbound : ∀ z, |η z| ≤ B) (hr : IsRadial η) (h1 : ∫ z, η z = 1) :
    let χ := nextCoreObservation (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) ψ c
    conditionalBlockMaximum (K := cutOutNumber c) Z lam χ s u^2*formMass (coreSlice χ s u) ≤
      B*∫ z in closedBall y (t+b+R), coreFieldSquare Z lam z (coreSlice χ s u) := by
  dsimp only
  have hc0 : coreSlice (nextCoreObservation (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ c) s u =
      coreSlice (orderedCutForm (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb)
        (coreSlice ψ (rightList s) (rightList u)) c) (leftList s) (leftList u) := by
    conv_lhs => rw [←join_list_parts s,←join_list_parts u]
    exact nextCoreObservation_slice _ _ _ _ _ _ _ _
  have hb0 : 0 ≤ B := (abs_nonneg (η 0)).trans (hbound 0)
  by_cases hmass : formMass (coreSlice (nextCoreObservation (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ c) s u) = 0
  · simp only [hmass,mul_zero,coreFieldSquare,integral_zero,le_refl]
  have hpos := radial_out_position_distance (coreSlice ψ (rightList s) (rightList u)) y ht hb c
    (leftList s) (leftList u) (by rwa [←hc0])
  have hh := conditional_out_maximum_sq_le_ball_average
    (orderedCutForm (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb)
      (coreSlice ψ (rightList s) (rightList u)) c) (leftList s) (leftList u)
      (by rwa [←hc0]) y (by positivity : 0 ≤ t+b) hR hsep
      (fun i => (hpos i).le) hZ hlam hm hn hs hbound hr h1
  have hend := mul_le_mul_of_nonneg_right hh
    (formMass_nonneg (coreSlice (nextCoreObservation (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ c) s u))
  rw [←hc0] at hend
  have hemax : conditionalBlockMaximum (K := cutOutNumber c) Z lam
      (nextCoreObservation (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) ψ c) s u =
      conditionalOutMaximum Z lam (orderedCutForm (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) (coreSlice ψ (rightList s) (rightList u)) c)
        (leftList s) (leftList u) := by
    conv_lhs => rw [←join_list_parts s,←join_list_parts u]
    exact conditionalBlockMaximum_next_join _ _ _ _ _ _ _ _ _ _
  rw [hemax]
  simpa only [coreFieldSquare,integral_mul_const,mul_assoc] using hend

theorem radial_nextBlockMaximum_moment_spatial {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (y : Space) {t b R B Z lam : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (hR : 0 < R) (hsep : t+b+2*R ≤ ‖y‖)
    (hnear : t+2*b ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam)
    (c : Fin N → Fin 2) {η : Space → ℝ}
    (hm : Measurable η) (hn : ∀ z, 0 ≤ η z) (hs : ∀ z, η z ≠ 0 → ‖z‖ ≤ R)
    (hbound : ∀ z, |η z| ≤ B) (hr : IsRadial η) (h1 : ∫ z, η z = 1) :
    let χ := nextCoreObservation (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) ψ c
    (∑ s : Spins (cutOutNumber c+M), ∫ u,
      conditionalBlockMaximum (K := cutOutNumber c) Z lam χ s u^2*formMass (coreSlice χ s u)) ≤
      B*∫ z in closedBall y (t+b+R), coreLawAverage χ (coreFieldSquare Z lam z) := by
  let χ := nextCoreObservation (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) ψ c
  have hχ := nextCoreObservation_sobolev hψ (coreFirstRadialCut y ht hb)
    (coreFirstRadialCut_partition y ht hb) c
  change _ ≤ B*∫ z in closedBall y (t+b+R), coreLawAverage χ (coreFieldSquare Z lam z)
  rw [←coreFieldSquare_ball_fubini hχ y hR (by linarith : t+b+R+R ≤ ‖y‖) hZ hlam]
  unfold coreLawAverage
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  rw [←integral_const_mul]
  apply integral_mono_ae
    (radial_nextBlockMaximum_square_integrable hψ y ht hb hnear hZ hlam c s)
    ((coreFieldSquare_ball_statistic_integrable hχ s y hR (by linarith) hZ hlam).const_mul B)
  filter_upwards [hχ.ae_coreSlice s] with u hu
  exact radial_nextBlockMaximum_sq_spatial ψ y ht hb hR hsep hZ hlam c s u hu hm hn hs hbound hr h1

namespace CoreObservationGraph

def outMoment (G : CoreObservationGraph) (y : Space) {t b : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (Z lam : ℝ) : ℝ :=
  ∑ c : Fin G.coreSize → Fin 2, ∑ s : Spins (cutOutNumber c+G.outSize), ∫ u,
    conditionalBlockMaximum (K := cutOutNumber c) Z lam
      (G.observe (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) c).vector s u^2*
      formMass (coreSlice
        (G.observe (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) c).vector s u)

lemma outMoment_nonneg (G : CoreObservationGraph) (y : Space) {t b : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (Z lam : ℝ) : 0 ≤ G.outMoment y ht hb Z lam :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ =>
    mul_nonneg (sq_nonneg _) (formMass_nonneg _))))

lemma outMoment_spatial (G : CoreObservationGraph) (y : Space) {t b R B Z lam : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (hR : 0 < R) (hsep : t+b+2*R ≤ ‖y‖)
    (hnear : t+2*b ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) {η : Space → ℝ}
    (hm : Measurable η) (hn : ∀ z, 0 ≤ η z) (hs : ∀ z, η z ≠ 0 → ‖z‖ ≤ R)
    (hbound : ∀ z, |η z| ≤ B) (hr : IsRadial η) (h1 : ∫ z, η z = 1) :
    G.outMoment y ht hb Z lam ≤ B*∫ z in closedBall y (t+b+R),
      ∑ c : Fin G.coreSize → Fin 2,
        (G.observe (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) c).fieldMoment Z lam z := by
  unfold outMoment
  rw [integral_finsetSum,Finset.mul_sum]
  · apply Finset.sum_le_sum
    intro c _
    exact radial_nextBlockMaximum_moment_spatial G.sobolev y ht hb hR hsep hnear hZ hlam c
      hm hn hs hbound hr h1
  · intro c _
    exact coreLawAverage_fieldSquare_ball_integrable
      (G.observe (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) c).sobolev y
      hR (by linarith) hZ hlam

end CoreObservationGraph

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_DeletedFieldBudget
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombAtom

def freshOutMaximumSecondMoment {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector L) (Z lam : ℝ) : ℝ :=
  ∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
    conditionalOutMaximum Z lam (orderedCutForm p hp ψ c) s u^2*
      formMass (coreSlice (orderedCutForm p hp ψ c) s u)

lemma freshOutMaximumSecondMoment_nonneg {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector L) (Z lam : ℝ) :
    0 ≤ freshOutMaximumSecondMoment p hp ψ Z lam := by
  apply Finset.sum_nonneg; intro c _
  apply Finset.sum_nonneg; intro s _
  exact integral_nonneg (fun u => mul_nonneg (sq_nonneg _) (formMass_nonneg _))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CoreHistoryCountsBarrier
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators

lemma rawCountMoment_eq_integral {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) (R : ℝ) : rawCountMoment ψ y R = ∫ x, rawBallCount y R x^2 ∂formRawLaw ψ :=
  rawFormPair_eq_integral hψ ((rawBallCount_measurable y R).pow_const 2)
    (fun x => norm_sq_le_of_nonneg (rawBallCount_nonneg y R x) (rawBallCount_le y R x))

open MeasureTheory Filter
open scoped BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RadialSelectedCounts
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombAtom

lemma weightedParticleCount_eq_rawLaw {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {w : Space → ℝ} (hw : Measurable w) {B : ℝ} (hB : ∀ x, ‖w x‖ ≤ B) :
    weightedParticleCount ψ w = ∫ x, (∑ i, w (x i)) ∂formRawLaw ψ := by
  have hm : Measurable (fun x : Configuration N => ∑ i, w (x i)) :=
    Finset.measurable_sum _ (fun i _ => hw.comp (measurable_pi_apply i))
  have hbnd (x : Configuration N) : ‖∑ i, w (x i)‖ ≤ N*B := by
    calc
      _ ≤ ∑ i, ‖w (x i)‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Fin N, B := Finset.sum_le_sum (fun i _ => hB (x i))
      _ = N*B := by simp
  rw [formRawLaw_integral_eq_spin_sum hψ hm hbnd]
  apply Finset.sum_congr rfl; intro s _
  simp only [Finset.sum_mul]
  exact (integral_finsetSum _ (fun i _ => weightedParticleCount_integrable hψ hw hB s i)).symm

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RootMomentCauchyBarrier
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

section Work_CoreHistoryIMS_barrier_scope

open MeasureTheory Filter Set
open scoped BigOperators

lemma rawFormPair_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {g : Configuration N → ℝ} (hg : Measurable g) {B : ℝ}
    (hB : ∀ x, ‖g x‖ ≤ B) (s : Spins N) : Integrable (fun x => g x*‖ψ.value s x‖^2) :=
  ((hψ.1 s).norm.integrable_sq).bdd_mul hg.aestronglyMeasurable (ae_of_all _ hB)

lemma rawBallFirst_le_sqrt_count {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) (R : ℝ) :
    rawFormPair ψ (rawBallCount y R) ≤ Real.sqrt (rawCountMoment ψ y R)*Real.sqrt (formMass ψ) := by
  have hc := weighted_sum_integral_cauchy (fun _ : Spins N => volume)
    (fun s x => ‖ψ.value s x‖^2) (fun _ => rawBallCount y R) (fun _ _ => 1)
    (fun _ _ => sq_nonneg _)
    (fun s => rawFormPair_integrable hψ ((rawBallCount_measurable y R).pow_const 2)
      (fun x => norm_sq_le_of_nonneg (rawBallCount_nonneg _ _ _) (rawBallCount_le _ _ _)) s)
    (fun s => by simpa only [one_pow,one_mul] using (hψ.1 s).norm.integrable_sq)
    (fun s => by
      simpa only [mul_one] using (rawFormPair_integrable hψ (rawBallCount_measurable y R)
        (fun x => by rw [Real.norm_of_nonneg (rawBallCount_nonneg _ _ _)]; exact rawBallCount_le _ _ _) s))
  simpa only [mul_one,one_pow,one_mul,rawFormPair,rawCountMoment,formMass] using hc

lemma collar_count_le_rawBallFirst {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) {t b R : ℝ} (hR : t+b < R) :
    weightedParticleCount ψ (fun z => if t ≤ ‖z-y‖ ∧ ‖z-y‖ ≤ t+b then 1 else 0) ≤
      rawFormPair ψ (rawBallCount y R) := by
  let w : Space → ℝ := fun z => if t ≤ ‖z-y‖ ∧ ‖z-y‖ ≤ t+b then 1 else 0
  have hw : Measurable w := measurable_const.ite
    (((isClosed_le continuous_const ((continuous_id.sub continuous_const).norm)).inter
      (isClosed_le ((continuous_id.sub continuous_const).norm) continuous_const)).measurableSet) measurable_const
  have hB : ∀ z, ‖w z‖ ≤ 1 := by intro z; unfold w; split_ifs <;> norm_num
  have hg : Measurable (fun x : Configuration N => ∑ i, w (x i)) :=
    Finset.measurable_sum _ (fun i _ => hw.comp (measurable_pi_apply i))
  have hgB (x : Configuration N) : ‖∑ i, w (x i)‖ ≤ (N:ℝ) := by
    calc
      _ ≤ ∑ i, ‖w (x i)‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Fin N, (1:ℝ) := Finset.sum_le_sum (fun i _ => hB (x i))
      _ = _ := by simp
  change weightedParticleCount ψ w ≤ _
  rw [weightedParticleCount_eq_rawLaw hψ hw hB,←rawFormPair_eq_integral hψ hg hgB]
  unfold rawFormPair
  apply Finset.sum_le_sum
  intro s _
  apply integral_mono (rawFormPair_integrable hψ hg hgB s)
    (rawFormPair_integrable hψ (rawBallCount_measurable y R)
      (fun x => by rw [Real.norm_of_nonneg (rawBallCount_nonneg _ _ _)]; exact rawBallCount_le _ _ _) s)
  intro x
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  unfold rawBallCount
  apply Finset.sum_le_sum
  intro i _
  dsimp only [w]
  split_ifs with h h' h'
  · norm_num
  · exfalso; exact h' (lt_of_le_of_lt h.2 hR)
  · norm_num
  · norm_num

lemma radial_ims_le_sqrt_count {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) {t b R : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hR : t+b < R) :
    (1/2:ℝ)*weightedParticleCount ψ (spatialErrorWeight (coreFirstRadialCut y ht hb)) ≤
      ((3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2)*
        (Real.sqrt (rawCountMoment ψ y R)*Real.sqrt (formMass ψ)) := by
  exact (radial_fresh_ims_bound hψ y ht hb).trans (mul_le_mul_of_nonneg_left
    ((collar_count_le_rawBallFirst hψ y hR).trans (rawBallFirst_le_sqrt_count hψ y R)) (by positivity))

end Work_CoreHistoryIMS_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CoupledCoreExcessBarrier
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CoupledCoreExcess_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators

lemma outKinetic_nonneg {N M : ℕ} (ψ : FormVector (N+M)) : 0 ≤ outKinetic ψ := by
  unfold outKinetic
  positivity

lemma outRepulsion_nonneg {N M : ℕ} (ψ : FormVector (N+M)) : 0 ≤ outRepulsion ψ := by
  apply Finset.sum_nonneg; intro s _
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  split_ifs
  · exact integral_nonneg (fun _ => by positivity)
  · exact le_rfl

lemma cutExteriorPrice_eq_field_work {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevVector ψ) (Z lam : ℝ) (c : Fin L → Fin 2) :
    cutExteriorPrice p hp Z lam ψ c =
      outKinetic (orderedCutForm p hp ψ c)-
        (∑ s : Spins (cutOutNumber c), ∫ u,
          conditionalFieldSum Z lam (orderedCutForm p hp ψ c) s u)+
        outRepulsion (orderedCutForm p hp ψ c) := by
  have hχ := orderedCutForm_sobolev p hp hψ c
  rw [integral_conditionalFieldSum hχ Z lam]
  unfold cutExteriorPrice cutCoreEnergy
  rw [integrated_core_parts hχ Z,formEnergy_core_out_cross]
  ring

lemma cutCoreExcess_le_field_work {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevVector ψ) (Z lam : ℝ) :
    (∑ c : Fin L → Fin 2, cutCoreExcess p hp Z lam ψ c) ≤
      corePriceExcess Z lam ψ+(1/2:ℝ)*weightedParticleCount ψ (spatialErrorWeight p)+
        (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          conditionalFieldSum Z lam (orderedCutForm p hp ψ c) s u) := by
  have hid := fock_cut_excess_identity p hp hψ Z lam
  simp_rw [cutExteriorPrice_eq_field_work p hp hψ Z lam] at hid
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib] at hid
  have hk : 0 ≤ ∑ c : Fin L → Fin 2, outKinetic (orderedCutForm p hp ψ c) :=
    Finset.sum_nonneg (fun c _ => outKinetic_nonneg _)
  have hr : 0 ≤ ∑ c : Fin L → Fin 2, outRepulsion (orderedCutForm p hp ψ c) :=
    Finset.sum_nonneg (fun c _ => outRepulsion_nonneg _)
  linarith

lemma conditionalFieldSum_le_max {N M : ℕ} (ψ : FormVector (N+M))
    (s : Spins M) (u : Configuration M) (Z lam : ℝ) :
    conditionalFieldSum Z lam ψ s u ≤
      conditionalOutMaximum Z lam ψ s u*M*formMass (coreSlice ψ s u) := by
  have hh := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => conditionalField_le_outMaximum Z lam ψ s u i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  unfold conditionalFieldSum
  nlinarith [mul_le_mul_of_nonneg_left hh (formMass_nonneg (coreSlice ψ s u))]

lemma radial_max_out_product_integrable {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevVector ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t)
    (hb : 0 < b) (hy : t+2*b ≤ ‖y‖) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (c : Fin L → Fin 2)
    (s : Spins (cutOutNumber c)) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    Integrable (fun u => conditionalOutMaximum Z lam (orderedCutForm p hp ψ c) s u*
      (cutOutNumber c:ℝ)*formMass (coreSlice (orderedCutForm p hp ψ c) s u)) := by
  dsimp only
  have hχ := orderedCutForm_sobolev (coreFirstRadialCut y ht hb)
    (coreFirstRadialCut_partition y ht hb) hψ c
  have hh : Integrable (fun u => conditionalOutMaximum Z lam
      (orderedCutForm (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) ψ c) s u*
        formMass (coreSlice (orderedCutForm (coreFirstRadialCut y ht hb)
          (coreFirstRadialCut_partition y ht hb) ψ c) s u)) := by
    apply (hχ.coreSlice_mass_integrable s).bdd_mul
      (conditionalOutMaximum_aemeasurable hχ s Z lam).aestronglyMeasurable
    apply ae_of_all; intro u
    rw [Real.norm_of_nonneg (conditionalOutMaximum_nonneg _ _ _ _ _)]
    exact radial_conditionalOutMaximum_bound ψ y ht hb hy hZ hlam c s u
  simpa only [mul_right_comm] using hh.mul_const (cutOutNumber c:ℝ)

theorem radial_full_field_work_budget {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevVector ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t)
    (hb : 0 < b) (hy : t+2*b ≤ ‖y‖) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      conditionalFieldSum Z lam (orderedCutForm p hp ψ c) s u) ≤
      Real.sqrt (freshOutMaximumSecondMoment p hp ψ Z lam)*
        Real.sqrt (∑ c : Fin L → Fin 2, (cutOutNumber c:ℝ)^2*
          formMass (orderedCutForm p hp ψ c)) := by
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  dsimp only
  have hc := weighted_sum_integral_cauchy
    (ι := Σ c : Fin L → Fin 2, Spins (cutOutNumber c))
    (X := fun cs => Configuration (cutOutNumber cs.1)) (fun _ => volume)
    (fun cs u => formMass (coreSlice (orderedCutForm p hp ψ cs.1) cs.2 u))
    (fun cs u => conditionalOutMaximum Z lam (orderedCutForm p hp ψ cs.1) cs.2 u)
    (fun cs _ => (cutOutNumber cs.1:ℝ)) (fun _ _ => formMass_nonneg _)
    (fun cs => radial_outMaximum_square_integrable hψ y ht hb hy hZ hlam cs.1 cs.2)
    (fun cs => ((orderedCutForm_sobolev p hp hψ cs.1).coreSlice_mass_integrable cs.2).const_mul _)
    (fun cs => radial_max_out_product_integrable hψ y ht hb hy hZ hlam cs.1 cs.2)
  simp only [Fintype.sum_sigma,integral_const_mul,←Finset.mul_sum,
    SobolevVector.integral_coreSlice_mass (orderedCutForm_sobolev p hp hψ _)] at hc
  apply le_trans _ hc
  apply Finset.sum_le_sum; intro c _
  apply Finset.sum_le_sum; intro s _
  apply integral_mono
    (conditionalFieldSum_integrable (orderedCutForm_sobolev p hp hψ c) Z lam s)
    (radial_max_out_product_integrable hψ y ht hb hy hZ hlam c s)
  intro u
  exact conditionalFieldSum_le_max _ s u Z lam

theorem radial_core_excess_coupling {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevVector ψ) (y : Space) {t b R : ℝ} (ht : 0 ≤ t)
    (hb : 0 < b) (hy : t+2*b ≤ ‖y‖) (hR : t+b ≤ R) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    (∑ c : Fin L → Fin 2, cutCoreExcess p hp Z lam ψ c) ≤
      corePriceExcess Z lam ψ+(1/2:ℝ)*weightedParticleCount ψ (spatialErrorWeight p)+
        Real.sqrt (freshOutMaximumSecondMoment p hp ψ Z lam)*
          Real.sqrt (∫ x, rawBallCount y R x^2 ∂formRawLaw ψ) := by
  dsimp only
  refine (cutCoreExcess_le_field_work _ _ hψ Z lam).trans (add_le_add le_rfl
    ((radial_full_field_work_budget hψ y ht hb hy hZ hlam).trans ?_))
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (radialCut_out_second_moment hψ y ht hb hR))
    (Real.sqrt_nonneg _)

end Work_CoupledCoreExcess_barrier_scope

open MeasureTheory Filter
open scoped BigOperators

lemma radial_freshMaximum_statistic_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (y : Space) {r b : ℝ} (hr : 0 ≤ r) (hb : 0 < b)
    (hy : r+2*b ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (s : Spins M) :
    Integrable (fun v => freshOutMaximumSecondMoment (coreFirstRadialCut y hr hb)
      (coreFirstRadialCut_partition y hr hb) (coreSlice ψ s v) Z lam) := by
  apply integrable_finsetSum
  intro c _
  exact nextBlockMaximum_square_statistic_integrable ψ _ _ c Z lam
    (fun t => radial_nextBlockMaximum_square_integrable hψ y hr hb hy hZ hlam c t) s

namespace CoreObservationGraph

lemma outMoment_eq_average (G : CoreObservationGraph) (y : Space) {r b : ℝ}
    (hr : 0 ≤ r) (hb : 0 < b) (hy : r+2*b ≤ ‖y‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    G.outMoment y hr hb Z lam = coreLawAverage G.vector (fun φ =>
      freshOutMaximumSecondMoment (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb) φ Z lam) := by
  unfold outMoment
  change (∑ c : Fin G.coreSize → Fin 2, ∑ s : Spins (cutOutNumber c+G.outSize), ∫ u,
    conditionalBlockMaximum (K := cutOutNumber c) Z lam
      (nextCoreObservation (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb) G.vector c) s u^2*
      formMass (coreSlice
        (nextCoreObservation (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb) G.vector c) s u)) = _
  have he (c : Fin G.coreSize → Fin 2) := nextBlockMaximum_square_fubini G.vector
    (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb) c Z lam
    (fun s => radial_nextBlockMaximum_square_integrable G.sobolev y hr hb hy hZ hlam c s)
  simp_rw [he]
  rw [Finset.sum_comm]
  unfold coreLawAverage freshOutMaximumSecondMoment
  apply Finset.sum_congr rfl
  intro s _
  apply (integral_finsetSum _ _).symm
  intro c _
  exact nextBlockMaximum_square_statistic_integrable G.vector _ _ c Z lam
    (fun t => radial_nextBlockMaximum_square_integrable G.sobolev y hr hb hy hZ hlam c t) s

theorem observe_excess_budget (G : CoreObservationGraph) (y : Space) {r b R : ℝ}
    (hr : 0 ≤ r) (hb : 0 < b) (hy : r+2*b ≤ ‖y‖) (hR : r+b < R)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    (∑ c : Fin G.coreSize → Fin 2,
      (G.observe (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb) c).excess Z lam) ≤
      G.excess Z lam+((3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2)*
        (Real.sqrt (G.countMoment y R)*Real.sqrt G.mass)+
        Real.sqrt (G.outMoment y hr hb Z lam)*Real.sqrt (G.countMoment y R) := by
  let p := coreFirstRadialCut y hr hb
  let hp := coreFirstRadialCut_partition y hr hb
  let K := (3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2
  let C (s : Spins G.outSize) (v : Configuration G.outSize) := rawCountMoment (coreSlice G.vector s v) y R
  let F (s : Spins G.outSize) (v : Configuration G.outSize) :=
    freshOutMaximumSecondMoment p hp (coreSlice G.vector s v) Z lam
  let W (s : Spins G.outSize) (v : Configuration G.outSize) := formMass (coreSlice G.vector s v)
  have hC (s : Spins G.outSize) : Integrable (C s) := rawCountMoment_coreSlice_integrable G.sobolev y R s
  have hF (s : Spins G.outSize) : Integrable (F s) := radial_freshMaximum_statistic_integrable G.sobolev y hr hb hy hZ hlam s
  have hW (s : Spins G.outSize) : Integrable (W s) := G.sobolev.coreSlice_mass_integrable s
  have hCn (s : Spins G.outSize) (v : Configuration G.outSize) : 0 ≤ C s v := rawCountMoment_nonneg _ _ _
  have hFn (s : Spins G.outSize) (v : Configuration G.outSize) : 0 ≤ F s v := freshOutMaximumSecondMoment_nonneg _ _ _ _ _
  have hWn (s : Spins G.outSize) (v : Configuration G.outSize) : 0 ≤ W s v := formMass_nonneg _
  have hCW (s : Spins G.outSize) := integrable_sqrt_mul_sqrt (hC s) (hW s) (hCn s) (hWn s)
  have hFC (s : Spins G.outSize) := integrable_sqrt_mul_sqrt (hF s) (hC s) (hFn s) (hCn s)
  have hcW := sum_integral_sqrt_mul_sqrt_le (fun _ : Spins G.outSize => volume) C W hC hW hCn hWn
  have hcF := sum_integral_sqrt_mul_sqrt_le (fun _ : Spins G.outSize => volume) F C hF hC hFn hCn
  have hstep (s : Spins G.outSize) :
      (∫ v, ∑ c : Fin G.coreSize → Fin 2, cutCoreExcess p hp Z lam (coreSlice G.vector s v) c) ≤
        ∫ v, corePriceExcess Z lam (coreSlice G.vector s v)+
          K*(Real.sqrt (C s v)*Real.sqrt (W s v))+Real.sqrt (F s v)*Real.sqrt (C s v) := by
    apply integral_mono_ae
      (integrable_finsetSum _ (fun c _ => nextCoreObservation_excess_statistic_integrable G.sobolev p hp c s Z lam))
      (((G.sobolev.coreSlice_excess_integrable Z lam s).add ((hCW s).const_mul K)).add (hFC s))
    filter_upwards [G.sobolev.ae_coreSlice s] with v hv
    have hh := radial_core_excess_coupling hv y hr hb hy hR.le hZ hlam
    dsimp only at hh
    rw [←rawCountMoment_eq_integral hv y R] at hh
    have hi := radial_ims_le_sqrt_count hv y hr hb hR
    exact hh.trans (add_le_add (add_le_add le_rfl hi) le_rfl)
  have he (s : Spins G.outSize) :
      (∫ v, corePriceExcess Z lam (coreSlice G.vector s v)+
          K*(Real.sqrt (C s v)*Real.sqrt (W s v))+Real.sqrt (F s v)*Real.sqrt (C s v)) =
      (∫ v, corePriceExcess Z lam (coreSlice G.vector s v))+
        K*(∫ v, Real.sqrt (C s v)*Real.sqrt (W s v))+
        (∫ v, Real.sqrt (F s v)*Real.sqrt (C s v)) := by
    have hA : Integrable (fun v => corePriceExcess Z lam (coreSlice G.vector s v)+
        K*(Real.sqrt (C s v)*Real.sqrt (W s v))) :=
      (G.sobolev.coreSlice_excess_integrable Z lam s).add ((hCW s).const_mul K)
    rw [integral_add hA (hFC s),
      integral_add (G.sobolev.coreSlice_excess_integrable Z lam s) ((hCW s).const_mul K),integral_const_mul]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hstep s)
  simp_rw [he] at hh
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hh
  have hend := hh.trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hcW (by positivity : 0 ≤ K))) hcF)
  change (∑ c : Fin G.coreSize → Fin 2, coreLawAverage (nextCoreObservation p hp G.vector c) (corePriceExcess Z lam)) ≤ _
  rw [sum_nextCoreObservation_excess G.sobolev p hp Z lam]
  have hwe : (∑ s : Spins G.outSize, ∫ v, W s v) = G.mass := G.sobolev.integral_coreSlice_mass
  have hfe : (∑ s : Spins G.outSize, ∫ v, F s v) = G.outMoment y hr hb Z lam :=
    (G.outMoment_eq_average y hr hb hy hZ hlam).symm
  rw [hwe,hfe] at hend
  exact hend

end CoreObservationGraph

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_CoreObservationEnsembleBarrier
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators

namespace CoulombAtom

attribute [instance] CoreObservationEnsemble.finite

namespace CoreObservationEnsemble

def outMoment (E : CoreObservationEnsemble) (y : Space) {r b : ℝ} (hr : 0 ≤ r) (hb : 0 < b)
    (Z lam : ℝ) : ℝ := ∑ i, (E.graph i).outMoment y hr hb Z lam

lemma fieldMoment_nonneg (E : CoreObservationEnsemble) (Z lam : ℝ) (y : Space) : 0 ≤ E.fieldMoment Z lam y :=
  Finset.sum_nonneg (fun i _ => (E.graph i).fieldMoment_nonneg Z lam y)
lemma outMoment_nonneg (E : CoreObservationEnsemble) (y : Space) {r b : ℝ} (hr : 0 ≤ r) (hb : 0 < b)
    (Z lam : ℝ) : 0 ≤ E.outMoment y hr hb Z lam :=
  Finset.sum_nonneg (fun i _ => (E.graph i).outMoment_nonneg y hr hb Z lam)

lemma observe_excess_budget (E : CoreObservationEnsemble) (y : Space) {r b R : ℝ}
    (hr : 0 ≤ r) (hb : 0 < b) (hy : r+2*b ≤ ‖y‖) (hR : r+b < R)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    (E.observe (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb)).excess Z lam ≤
      E.excess Z lam+((3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2)*
        (Real.sqrt (E.countMoment y R)*Real.sqrt E.mass)+
        Real.sqrt (E.outMoment y hr hb Z lam)*Real.sqrt (E.countMoment y R) := by
  let K := (3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2
  have h1 := Real.sum_sqrt_mul_sqrt_le Finset.univ
    (fun i : E.Branch => (E.graph i).countMoment_nonneg y R) (fun i => (E.graph i).mass_nonneg)
  have h2 := Real.sum_sqrt_mul_sqrt_le Finset.univ
    (fun i : E.Branch => (E.graph i).outMoment_nonneg y hr hb Z lam)
    (fun i => (E.graph i).countMoment_nonneg y R)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i (_ : i ∈ Finset.univ) =>
    (E.graph i).observe_excess_budget y hr hb hy hR hZ hlam)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hh
  have hend := hh.trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ K))) h2)
  change (∑ ic : Σ i : E.Branch, Fin (E.graph i).coreSize → Fin 2,
    ((E.graph ic.1).observe (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb) ic.2).excess Z lam) ≤ _
  rw [Fintype.sum_sigma]
  exact hend

lemma fieldMoment_le_observe_excess (E : CoreObservationEnsemble)
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    (y : Space) {B : ℝ} (hB : 0 < B) (hnuc : 2*B ≤ ‖y‖)
    (hv : ∀ x ∈ ball y (2*B), (p 0).value x = 0)
    (hd : ∀ x ∈ ball y (2*B), ∀ a, lineDeriv ℝ (p 0).value x (spaceDirections a) = 0)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    E.fieldMoment Z lam y ≤ 2*packetFieldConstant^2*((1/B^4+1/B)^2*E.mass+
      (E.observe p hp).excess Z lam/B) := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i (_ : i ∈ Finset.univ) =>
    (E.graph i).fieldMoment_le_observe_excess p hp y hB hnuc hv hd hZ hlam)
  simp only [←Finset.mul_sum,Finset.sum_add_distrib,←Finset.sum_div] at hh
  change E.fieldMoment Z lam y ≤ 2*packetFieldConstant^2*((1/B^4+1/B)^2*E.mass+
    (∑ ic : Σ i : E.Branch, Fin (E.graph i).coreSize → Fin 2,
      ((E.graph ic.1).observe p hp ic.2).excess Z lam)/B)
  rw [Fintype.sum_sigma]
  exact hh

lemma outMoment_spatial (E : CoreObservationEnsemble) (y : Space) {r b R B Z lam : ℝ}
    (hr : 0 ≤ r) (hb : 0 < b) (hR : 0 < R) (hsep : r+b+2*R ≤ ‖y‖)
    (hnear : r+2*b ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) {η : Space → ℝ}
    (hm : Measurable η) (hn : ∀ z, 0 ≤ η z) (hs : ∀ z, η z ≠ 0 → ‖z‖ ≤ R)
    (hbound : ∀ z, |η z| ≤ B) (hηr : CoulombAnalysis.IsRadial η) (h1 : ∫ z, η z = 1) :
    E.outMoment y hr hb Z lam ≤ B*∫ z in closedBall y (r+b+R),
      (E.observe (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb)).fieldMoment Z lam z := by
  let p := coreFirstRadialCut y hr hb
  let hp := coreFirstRadialCut_partition y hr hb
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i (_ : i ∈ Finset.univ) =>
    (E.graph i).outMoment_spatial y hr hb hR hsep hnear hZ hlam hm hn hs hbound hηr h1)
  rw [←Finset.mul_sum] at hh
  change _ ≤ B*∫ z in closedBall y (r+b+R),
    ∑ ic : Σ i : E.Branch, Fin (E.graph i).coreSize → Fin 2,
      ((E.graph ic.1).observe p hp ic.2).fieldMoment Z lam z
  simp_rw [Fintype.sum_sigma]
  rw [integral_finsetSum]
  · exact hh
  · intro i _
    exact integrable_finsetSum _ (fun c _ => coreLawAverage_fieldSquare_ball_integrable
      ((E.graph i).observe p hp c).sobolev y hR (by linarith) hZ hlam)

end CoreObservationEnsemble
end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BallAverageKernelBarrier
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped BigOperators

lemma coreSlice_empty {N : ℕ} (ψ : FormVector N) (s : Spins 0) (v : Configuration 0) :
    coreSlice (M := 0) ψ s v = ψ := by
  cases ψ
  simp only [coreSlice,joinLists_empty,finSumFinEquiv_apply_left,Fin.castAdd_zero]
  rfl

lemma coreLawAverage_empty {N : ℕ} (ψ : FormVector N) (F : FormVector N → ℝ) :
    coreLawAverage (M := 0) ψ F = F ψ := by
  unfold coreLawAverage
  simp [coreSlice_empty,Spins,Configuration,Measure.real,volume_pi]

namespace CoreObservationEnsemble

lemma initial_mass {N : ℕ} (ψ : FormVector N) (hψ : SobolevFermion ψ) :
    (initial ψ hψ).mass = formMass ψ := by
  change (∑ _i : Unit, formMass ψ) = formMass ψ
  simp
lemma initial_countMoment {N : ℕ} (ψ : FormVector N) (hψ : SobolevFermion ψ) (y : Space) (R : ℝ) :
    (initial ψ hψ).countMoment y R = rawCountMoment ψ y R := by
  change (∑ _i : Unit, coreLawAverage (M := 0) ψ (fun f => rawCountMoment f y R)) = _
  simp [coreLawAverage_empty]
lemma initial_excess {N : ℕ} (ψ : FormVector N) (hψ : SobolevFermion ψ) (Z lam : ℝ) :
    (initial ψ hψ).excess Z lam = corePriceExcess Z lam ψ := by
  change (∑ _i : Unit, coreLawAverage (M := 0) ψ (corePriceExcess Z lam)) = _
  simp [coreLawAverage_empty]

lemma outMoment_le_ball_field (E : CoreObservationEnsemble) (y : Space) {a Z lam Q : ℝ}
    (ha : 0 < a) (hsep : 5*a ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam)
    (hQ : ∀ z ∈ closedBall y (4*a),
      (E.observe (coreFirstRadialCut y (by positivity : 0 ≤ 2*a) ha)
        (coreFirstRadialCut_partition y (by positivity : 0 ≤ 2*a) ha)).fieldMoment Z lam z ≤ Q) :
    E.outMoment y (by positivity : 0 ≤ 2*a) ha Z lam ≤ 64*Q := by
  have hh := E.outMoment_spatial y (by positivity : 0 ≤ 2*a) ha ha
    (by linarith : 2*a+a+2*a ≤ ‖y‖) (by linarith : 2*a+2*a ≤ ‖y‖) hZ hlam
    (ballAverageKernel_measurable a) (ballAverageKernel_nonneg ha)
    (ballAverageKernel_support a) (ballAverageKernel_bound ha)
    (ballAverageKernel_radial a) (ballAverageKernel_mass ha)
  have he : 2*a+a+a = 4*a := by ring
  rw [he] at hh
  let E' := E.observe (coreFirstRadialCut y (by positivity : 0 ≤ 2*a) ha)
    (coreFirstRadialCut_partition y (by positivity : 0 ≤ 2*a) ha)
  have hi := E'.fieldMoment_ball_integrable y ha (by linarith : 4*a+a ≤ ‖y‖) hZ hlam
  have hc : IntegrableOn (fun _ : Space => Q) (closedBall y (4*a)) :=
    integrableOn_const (isCompact_closedBall y (4*a)).measure_lt_top.ne
  have hm := setIntegral_mono_on hi hc isClosed_closedBall.measurableSet hQ
  have hb : 0 ≤ 1/(a^3*(Real.pi*4/3)) := by positivity
  have hout := hh.trans (mul_le_mul_of_nonneg_left hm hb)
  rw [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,
    ←Measure.real,space_closedBall_real y (by positivity)] at hout
  have hv : 1/(a^3*(Real.pi*4/3))*((4*a)^3*(Real.pi*4/3)*Q) = 64*Q := by
    field_simp [ha.ne',Real.pi_ne_zero]
    ring
  rwa [hv] at hout

end CoreObservationEnsemble

open MeasureTheory Set Metric
open scoped BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_LocalFieldEnvelopeBarrier
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric

namespace CoulombAtom

def localHistoryFieldValues (E₀ : CoreObservationEnsemble) (y₀ : Space) (a : ℝ)
    (ha : 0 < a) (Z lam : ℝ) : Set ℝ :=
  {t | ∃ n E, CoreLocalHistory E₀ y₀ a ha n E ∧ ∃ y ∈ closedBall y₀ (localHistoryReach a n),
    t = Real.sqrt (E.fieldMoment Z lam y)/((n:ℝ)+2)^8}

def localFieldEnvelope (E₀ : CoreObservationEnsemble) (y₀ : Space) (a : ℝ)
    (ha : 0 < a) (Z lam : ℝ) : ℝ := sSup (localHistoryFieldValues E₀ y₀ a ha Z lam)

lemma localHistoryFieldValues_nonempty (E₀ : CoreObservationEnsemble) (y₀ : Space) {a : ℝ}
    (ha : 0 < a) (Z lam : ℝ) : (localHistoryFieldValues E₀ y₀ a ha Z lam).Nonempty := by
  refine ⟨_,0,E₀,CoreLocalHistory.initial,y₀,?_,rfl⟩
  simp [localHistoryReach]

lemma localHistoryFieldValues_bdd (E₀ : CoreObservationEnsemble) (y₀ : Space) {a Z lam : ℝ}
    (ha : 0 < a) (hsep : 12*a ≤ ‖y₀‖) (hm : E₀.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    BddAbove (localHistoryFieldValues E₀ y₀ a ha Z lam) := by
  refine ⟨Z/(8*a),?_⟩
  rintro t ⟨n,E,hE,y,hy,rfl⟩
  have hs := CoreLocalHistory.center_nuclear_separation (ha := ha) hsep y hy
  have hField := E.fieldMoment_le_nuclear hZ hlam y
  rw [hE.mass,hm,mul_one] at hField
  have hdiv : Z/‖y‖ ≤ Z/(8*a) := div_le_div_of_nonneg_left hZ (by positivity) hs
  have hsq := pow_le_pow_left₀ (div_nonneg hZ (norm_nonneg _)) hdiv 2
  have hroot : Real.sqrt (E.fieldMoment Z lam y) ≤ Z/(8*a) :=
    (Real.sqrt_le_iff).2 ⟨by positivity,hField.trans hsq⟩
  apply (div_le_iff₀ (by positivity : 0 < ((n:ℝ)+2)^8)).2
  have hw : 1 ≤ ((n:ℝ)+2)^8 := one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  exact hroot.trans (le_mul_of_one_le_right (by positivity) hw)

lemma localFieldEnvelope_nonneg (E₀ : CoreObservationEnsemble) (y₀ : Space) {a Z lam : ℝ}
    (ha : 0 < a) (hsep : 12*a ≤ ‖y₀‖) (hm : E₀.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    0 ≤ localFieldEnvelope E₀ y₀ a ha Z lam := by
  obtain ⟨t,ht⟩ := localHistoryFieldValues_nonempty E₀ y₀ ha Z lam
  have ht0 : 0 ≤ t := by
    obtain ⟨n,E,_,y,_,rfl⟩ := ht
    positivity
  exact ht0.trans (le_csSup (localHistoryFieldValues_bdd E₀ y₀ ha hsep hm hZ hlam) ht)

lemma localFieldEnvelope_bound {E₀ E : CoreObservationEnsemble} {y₀ : Space} {a Z lam : ℝ}
    {ha : 0 < a} (hsep : 12*a ≤ ‖y₀‖) (hm : E₀.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam)
    {n : ℕ} (hE : CoreLocalHistory E₀ y₀ a ha n E) (y : Space)
    (hy : y ∈ closedBall y₀ (localHistoryReach a n)) :
    Real.sqrt (E.fieldMoment Z lam y) ≤ localFieldEnvelope E₀ y₀ a ha Z lam*((n:ℝ)+2)^8 := by
  have hh : Real.sqrt (E.fieldMoment Z lam y)/((n:ℝ)+2)^8 ≤ localFieldEnvelope E₀ y₀ a ha Z lam :=
    le_csSup (localHistoryFieldValues_bdd E₀ y₀ ha hsep hm hZ hlam) ⟨n,E,hE,y,hy,rfl⟩
  exact (div_le_iff₀ (by positivity)).1 hh

lemma localFieldEnvelope_outMoment {E₀ E : CoreObservationEnsemble} {y₀ : Space} {a Z lam : ℝ}
    {ha : 0 < a} (hsep : 12*a ≤ ‖y₀‖) (hm : E₀.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam)
    {n : ℕ} (hE : CoreLocalHistory E₀ y₀ a ha n E) (y : Space)
    (hy : y ∈ closedBall y₀ (localHistoryReach a n)) :
    Real.sqrt (E.outMoment y (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (localHistoryRadius_pos ha n).le)
      (localHistoryRadius_pos ha n) Z lam) ≤ 8*localFieldEnvelope E₀ y₀ a ha Z lam*((n:ℝ)+3)^8 := by
  let u := localHistoryRadius a n
  have hu : 0 < u := localHistoryRadius_pos ha n
  have hn := CoreLocalHistory.center_nuclear_separation (ha := ha) hsep y hy
  have hn' : 5*u ≤ ‖y‖ := by have := localHistoryRadius_le ha n; dsimp [u]; linarith
  let H := localFieldEnvelope E₀ y₀ a ha Z lam
  have hH : 0 ≤ H := localFieldEnvelope_nonneg E₀ y₀ ha hsep hm hZ hlam
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity,?_⟩
  have hh := E.outMoment_le_ball_field y hu hn' hZ hlam (Q := (H*((n:ℝ)+3)^8)^2) ?_
  · calc E.outMoment y _ _ Z lam ≤ 64*(H*((n:ℝ)+3)^8)^2 := hh
         _ = (8*H*((n:ℝ)+3)^8)^2 := by ring
  · intro z hz
    have he := CoreLocalHistory.observe hE y hy
    have hz' := CoreLocalHistory.next_center y z hy hz
    have hh := localFieldEnvelope_bound hsep hm hZ hlam he z hz'
    have hcast : ((n+1:ℕ):ℝ)+2 = (n:ℝ)+3 := by push_cast; ring
    rw [hcast] at hh
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hh 2
    rwa [Real.sq_sqrt (CoreObservationEnsemble.fieldMoment_nonneg ..)] at hsq

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_LocalHistoryWeightsBarrier
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open scoped BigOperators

open Set Metric

lemma localHistory_excess_step {E₀ E : CoreObservationEnsemble} {y₀ : Space} {a Z lam : ℝ}
    {ha : 0 < a} (hsep : 12*a ≤ ‖y₀‖) (hm : E₀.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam)
    {n : ℕ} (hE : CoreLocalHistory E₀ y₀ a ha n E) (y : Space)
    (hy : y ∈ closedBall y₀ (localHistoryReach a n)) :
    (E.observe (coreFirstRadialCut y (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (localHistoryRadius_pos ha n).le)
      (localHistoryRadius_pos ha n))
      (coreFirstRadialCut_partition y (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (localHistoryRadius_pos ha n).le)
        (localHistoryRadius_pos ha n))).excess Z lam ≤ E.excess Z lam+
        localHistoryCostScale a (E₀.countMoment y₀ (8*a)) (localFieldEnvelope E₀ y₀ a ha Z lam)*((n:ℝ)+3)^8 := by
  have hH := localFieldEnvelope_nonneg E₀ y₀ ha hsep hm hZ hlam
  have hu := localHistoryRadius_pos ha n
  have hn := CoreLocalHistory.center_nuclear_separation (ha := ha) hsep y hy
  have hu' := localHistoryRadius_le ha n
  have hh := E.observe_excess_budget y (by positivity : 0 ≤ 2*localHistoryRadius a n) hu
    (by linarith : 2*localHistoryRadius a n+2*localHistoryRadius a n ≤ ‖y‖)
    (by linarith : 2*localHistoryRadius a n+localHistoryRadius a n < 4*localHistoryRadius a n) hZ hlam
  rw [hE.mass,hm,Real.sqrt_one,mul_one] at hh
  have hc := Real.sqrt_le_sqrt (hE.countMoment_local y hy)
  have hi := mul_le_mul (localHistoryRadius_ims ha n) hc (Real.sqrt_nonneg _)
    (mul_nonneg (div_nonneg localizationIMSConstant_nonneg (sq_nonneg a)) (by positivity))
  have ho := mul_le_mul (localFieldEnvelope_outMoment hsep hm hZ hlam hE y hy) hc
    (Real.sqrt_nonneg _) (by positivity)
  calc _ ≤ E.excess Z lam+((3/2:ℝ)*(Real.pi*smoothTransitionBound/localHistoryRadius a n)^2)*
      Real.sqrt (E.countMoment y (4*localHistoryRadius a n))+
      Real.sqrt (E.outMoment y _ _ Z lam)*Real.sqrt (E.countMoment y (4*localHistoryRadius a n)) := hh
    _ ≤ E.excess Z lam+(localizationIMSConstant/a^2)*((n:ℝ)+3)^8*Real.sqrt (E₀.countMoment y₀ (8*a))+
      (8*localFieldEnvelope E₀ y₀ a ha Z lam*((n:ℝ)+3)^8)*Real.sqrt (E₀.countMoment y₀ (8*a)) :=
      add_le_add (add_le_add le_rfl hi) ho
    _ = _ := by unfold localHistoryCostScale; ring

lemma localHistory_excess_bound {E₀ E : CoreObservationEnsemble} {y₀ : Space} {a Z lam : ℝ}
    {ha : 0 < a} (hsep : 12*a ≤ ‖y₀‖) (hm : E₀.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam)
    {n : ℕ} (hE : CoreLocalHistory E₀ y₀ a ha n E) :
    E.excess Z lam ≤ E₀.excess Z lam+
      localHistoryCostScale a (E₀.countMoment y₀ (8*a)) (localFieldEnvelope E₀ y₀ a ha Z lam)*
        (n:ℝ)*((n:ℝ)+2)^8 := by
  have hC := localHistoryCostScale_nonneg a (E₀.countMoment y₀ (8*a))
    (localFieldEnvelope_nonneg E₀ y₀ ha hsep hm hZ hlam)
  induction hE with
  | initial => simp
  | @observe n E hE y hy ih =>
    have hh := localHistory_excess_step hsep hm hZ hlam hE y hy
    have hp : ((n:ℝ)+2)^8 ≤ ((n:ℝ)+3)^8 := pow_le_pow_left₀ (by positivity) (by linarith) 8
    have hmul := mul_le_mul_of_nonneg_left hp (mul_nonneg hC (Nat.cast_nonneg n))
    push_cast
    calc
      _ ≤ E.excess Z lam+localHistoryCostScale a (E₀.countMoment y₀ (8*a))
        (localFieldEnvelope E₀ y₀ a ha Z lam)*((n:ℝ)+3)^8 := hh
      _ ≤ (E₀.excess Z lam+localHistoryCostScale a (E₀.countMoment y₀ (8*a))
        (localFieldEnvelope E₀ y₀ a ha Z lam)*(n:ℝ)*((n:ℝ)+2)^8)+
        localHistoryCostScale a (E₀.countMoment y₀ (8*a)) (localFieldEnvelope E₀ y₀ a ha Z lam)*((n:ℝ)+3)^8 :=
        add_le_add ih le_rfl
      _ ≤ (E₀.excess Z lam+localHistoryCostScale a (E₀.countMoment y₀ (8*a))
        (localFieldEnvelope E₀ y₀ a ha Z lam)*(n:ℝ)*((n:ℝ)+3)^8)+
        localHistoryCostScale a (E₀.countMoment y₀ (8*a)) (localFieldEnvelope E₀ y₀ a ha Z lam)*((n:ℝ)+3)^8 := by linarith
      _ = _ := by ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_LocalFieldBootstrapBarrier
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_LocalFieldBootstrap_barrier_scope

open Set Metric

lemma localHistory_field_bound {E₀ E : CoreObservationEnsemble} {y₀ : Space} {a Z lam : ℝ}
    {ha : 0 < a} (hsep : 12*a ≤ ‖y₀‖) (hm : E₀.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {n : ℕ} (hE : CoreLocalHistory E₀ y₀ a ha n E) (y : Space)
    (hy : y ∈ closedBall y₀ (localHistoryReach a n)) :
    E.fieldMoment Z lam y ≤ 2*packetFieldConstant^2*((1/a^4+1/a)^2+max (E₀.excess Z lam) 0/a+
      256*localHistoryCostScale a (E₀.countMoment y₀ (8*a)) (localFieldEnvelope E₀ y₀ a ha Z lam)/a)*
        ((n:ℝ)+2)^16 := by
  let u := localHistoryRadius a n
  have hu := localHistoryRadius_pos ha n
  let hr : 0 ≤ 2*u := by dsimp [u]; positivity
  let p := coreFirstRadialCut y hr hu
  let hp := coreFirstRadialCut_partition y hr hu
  have hn := CoreLocalHistory.center_nuclear_separation (ha := ha) hsep y hy
  have hu' := localHistoryRadius_le ha n
  have hv (x : Space) (hx : x ∈ ball y (2*u)) : (p 0).value x = 0 :=
    coreFirstRadialCut_core_zero y hr hu x (by simpa only [radialPatchCore,mem_ofPred_eq,not_le,mem_ball,dist_eq_norm] using hx)
  have hd (x : Space) (hx : x ∈ ball y (2*u)) (d : Fin 3) : lineDeriv ℝ (p 0).value x (spaceDirections d) = 0 :=
    coreFirstRadialCut_core_deriv_zero y hr hu x (by simpa only [radialPatchCore,mem_ofPred_eq,not_le,mem_ball,dist_eq_norm] using hx) d
  have hf := E.fieldMoment_le_observe_excess p hp y hu (by linarith) hv hd hZ hlam
  rw [hE.mass,hm,mul_one] at hf
  have he := localHistory_excess_bound hsep hm hZ hlam.le (CoreLocalHistory.observe hE y hy)
  have hc := localHistoryCostScale_nonneg a (E₀.countMoment y₀ (8*a))
    (localFieldEnvelope_nonneg E₀ y₀ ha hsep hm hZ hlam.le)
  have he' : (E.observe p hp).excess Z lam ≤ max (E₀.excess Z lam) 0+
      localHistoryCostScale a (E₀.countMoment y₀ (8*a)) (localFieldEnvelope E₀ y₀ a ha Z lam)*
        ((n:ℝ)+1)*((n:ℝ)+3)^8 := by
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,show (1:ℝ)+2 = 3 by norm_num] using
      he.trans (add_le_add (le_max_left (E₀.excess Z lam) 0) le_rfl)
  have hediv := (div_le_div_of_nonneg_right he' hu.le).trans
    (localHistoryRadius_energy ha (le_max_right _ _) hc n)
  have hall := mul_le_mul_of_nonneg_left (add_le_add (localHistoryRadius_packet ha n) hediv)
    (by positivity : 0 ≤ 2*packetFieldConstant^2)
  apply hf.trans
  convert hall using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma localFieldEnvelope_quadratic (E₀ : CoreObservationEnsemble) (y₀ : Space) {a Z lam : ℝ}
    (ha : 0 < a) (hsep : 12*a ≤ ‖y₀‖) (hm : E₀.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    (localFieldEnvelope E₀ y₀ a ha Z lam)^2 ≤
      2*packetFieldConstant^2*((1/a^4+1/a)^2+max (E₀.excess Z lam) 0/a+
        256*localizationIMSConstant*Real.sqrt (E₀.countMoment y₀ (8*a))/a^3)+
      (4096*packetFieldConstant^2*Real.sqrt (E₀.countMoment y₀ (8*a))/a)*
        localFieldEnvelope E₀ y₀ a ha Z lam := by
  let H := localFieldEnvelope E₀ y₀ a ha Z lam
  let C := localHistoryCostScale a (E₀.countMoment y₀ (8*a)) H
  let G := 2*packetFieldConstant^2*((1/a^4+1/a)^2+max (E₀.excess Z lam) 0/a+256*C/a)
  have hH : 0 ≤ H := localFieldEnvelope_nonneg E₀ y₀ ha hsep hm hZ hlam.le
  have hC : 0 ≤ C := localHistoryCostScale_nonneg _ _ hH
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hb (t : ℝ) (ht : t ∈ localHistoryFieldValues E₀ y₀ a ha Z lam) : t ≤ Real.sqrt G := by
    obtain ⟨n,E,hE,y,hy,rfl⟩ := ht
    have hh := localHistory_field_bound hsep hm hZ hlam hE y hy
    have hsq : (Real.sqrt (E.fieldMoment Z lam y)/((n:ℝ)+2)^8)^2 ≤ G := by
      rw [div_pow,Real.sq_sqrt (E.fieldMoment_nonneg Z lam y),←pow_mul]
      apply (div_le_iff₀ (by positivity)).2
      exact hh
    exact (Real.le_sqrt (by positivity) hG).2 hsq
  have hu : H ≤ Real.sqrt G := csSup_le (localHistoryFieldValues_nonempty E₀ y₀ ha Z lam) hb
  have hs := pow_le_pow_left₀ hH hu 2
  rw [Real.sq_sqrt hG] at hs
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [G,C,H,localHistoryCostScale]
  field_simp [ha.ne']
  ring

theorem ensemble_local_field_estimate (E₀ : CoreObservationEnsemble) (y₀ : Space) {a Z lam : ℝ}
    (ha : 0 < a) (hsep : 12*a ≤ ‖y₀‖) (hm : E₀.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    E₀.fieldMoment Z lam y₀ ≤ 65536*(
      4*packetFieldConstant^2*((1/a^4+1/a)^2+max (E₀.excess Z lam) 0/a+
        256*localizationIMSConstant*Real.sqrt (E₀.countMoment y₀ (8*a))/a^3)+
      (4096*packetFieldConstant^2*Real.sqrt (E₀.countMoment y₀ (8*a))/a)^2) := by
  let H := localFieldEnvelope E₀ y₀ a ha Z lam
  let A := 2*packetFieldConstant^2*((1/a^4+1/a)^2+max (E₀.excess Z lam) 0/a+
        256*localizationIMSConstant*Real.sqrt (E₀.countMoment y₀ (8*a))/a^3)
  let D := 4096*packetFieldConstant^2*Real.sqrt (E₀.countMoment y₀ (8*a))/a
  have hs : H^2 ≤ A+D*H := localFieldEnvelope_quadratic E₀ y₀ ha hsep hm hZ hlam
  have hs' : H^2 ≤ 2*A+D^2 := by nlinarith [sq_nonneg (H-D)]
  have hh := localFieldEnvelope_bound hsep hm hZ hlam.le (CoreLocalHistory.initial (E₀ := E₀) (y₀ := y₀) (a := a) (ha := ha)) y₀
    (by simp [localHistoryReach])
  norm_num at hh
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hh 2
  rw [Real.sq_sqrt (E₀.fieldMoment_nonneg Z lam y₀)] at hsq
  have hfinal := hsq.trans (show (localFieldEnvelope E₀ y₀ a ha Z lam*256)^2 ≤ 65536*(2*A+D^2) by nlinarith [hs'])
  convert hfinal using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [A,D]
  ring

end Work_LocalFieldBootstrap_barrier_scope

def localFieldUniversalConstant : ℝ := 65536*(4*packetFieldConstant^2+
  512*packetFieldConstant^2*localizationIMSConstant+(4096*packetFieldConstant^2)^2)

lemma localFieldUniversalConstant_pos : 0 < localFieldUniversalConstant := by
  have := packetFieldConstant_pos
  have := localizationIMSConstant_nonneg
  unfold localFieldUniversalConstant
  positivity

lemma field_explicit_bound_le_scale {a D B : ℝ} (ha : 0 < a) (hD : 0 ≤ D) (hB : 0 ≤ B) :
    65536*(4*packetFieldConstant^2*((1/a^4+1/a)^2+D/a+
        256*localizationIMSConstant*Real.sqrt B/a^3)+
      (4096*packetFieldConstant^2*Real.sqrt B/a)^2) ≤
        localFieldUniversalConstant*localFieldScale a D B := by
  let S := localFieldScale a D B
  have hP : 0 ≤ 1/a^4 := by positivity
  have hB' : 0 ≤ B/a^2 := by positivity
  have hD' : 0 ≤ D/a := by positivity
  have hX : 0 ≤ (1/a^4+1/a)^2 := sq_nonneg _
  have hS1 : (1/a^4+1/a)^2+D/a ≤ S := by dsimp [S,localFieldScale]; linarith
  have hS2 : 1/a^4+B/a^2 ≤ S := by dsimp [S,localFieldScale]; linarith
  have hS3 : B/a^2 ≤ S := by dsimp [S,localFieldScale]; linarith
  have hK := localizationIMSConstant_nonneg
  have hy := mul_le_mul_of_nonneg_left (sqrt_count_reciprocal_young ha hB)
    (show 0 ≤ 512*packetFieldConstant^2*localizationIMSConstant by positivity)
  have hterm : (4096*packetFieldConstant^2*Real.sqrt B/a)^2 =
      (4096*packetFieldConstant^2)^2*(B/a^2) := by
    rw [div_pow,mul_pow,Real.sq_sqrt hB]
    ring
  rw [hterm]
  have h1 := mul_le_mul_of_nonneg_left hS1 (show 0 ≤ 4*packetFieldConstant^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hS2 (show 0 ≤ 512*packetFieldConstant^2*localizationIMSConstant by positivity)
  have h3 := mul_le_mul_of_nonneg_left hS3 (sq_nonneg (4096*packetFieldConstant^2))
  change _ ≤ 65536*(4*packetFieldConstant^2+
    512*packetFieldConstant^2*localizationIMSConstant+(4096*packetFieldConstant^2)^2)*S
  calc
    _ = 65536*(4*packetFieldConstant^2*((1/a^4+1/a)^2+D/a)+
      512*packetFieldConstant^2*localizationIMSConstant*(2*Real.sqrt B/a^3)+
      (4096*packetFieldConstant^2)^2*(B/a^2)) := by ring
    _ ≤ 65536*(4*packetFieldConstant^2*S+
      512*packetFieldConstant^2*localizationIMSConstant*S+(4096*packetFieldConstant^2)^2*S) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 (hy.trans h2)) h3) (by norm_num)
    _ = _ := by ring

theorem ensemble_local_field_scale (E : CoreObservationEnsemble) (y : Space) {a Z lam : ℝ}
    (ha : 0 < a) (hsep : 12*a ≤ ‖y‖) (hm : E.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    E.fieldMoment Z lam y ≤ localFieldUniversalConstant*
      localFieldScale a (max (E.excess Z lam) 0) (E.countMoment y (8*a)) :=
  (ensemble_local_field_estimate E y ha hsep hm hZ hlam).trans
    (field_explicit_bound_le_scale ha (le_max_right _ _) (E.countMoment_nonneg y (8*a)))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_ThinFieldFeedbackBarrier
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric

 def thinOutMajorant (a b D B : ℝ) : ℝ :=
    1024*localFieldUniversalConstant*thinFieldBase a b D B+
      (512*localFieldUniversalConstant)^2*B/a^2
 def thinFieldMajorant (a b D B : ℝ) : ℝ := localFieldUniversalConstant*
    (thinFieldBase a b D B+(thinOutMajorant a b D B+B/a^2)/2)

namespace CoreObservationEnsemble

lemma thin_observe_field (E : CoreObservationEnsemble) (y z : Space) {a r b Z lam : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) (hra : r ≤ 6*a) (hb : 0 < b) (hba : b ≤ a)
    (hsep : 20*a ≤ ‖y‖) (hz : z ∈ closedBall y (8*a))
    (hm : E.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    (E.observe (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb)).fieldMoment Z lam z ≤
      localFieldUniversalConstant*(thinFieldBase a b (max (E.excess Z lam) 0) (E.countMoment y (16*a))+
        Real.sqrt (E.outMoment y hr hb Z lam)*Real.sqrt (E.countMoment y (16*a))/a) := by
  let E' := E.observe (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb)
  let B := E.countMoment y (16*a)
  have hzn : ‖z-y‖ ≤ 8*a := mem_closedBall_iff_norm.mp hz
  have hzy : ‖y‖ ≤ ‖z‖+‖z-y‖ := by
    calc ‖y‖ = ‖z-(z-y)‖ := by congr 1; abel
         _ ≤ _ := norm_sub_le _ _
  have hs : 12*a ≤ ‖z‖ := by linarith
  have hf := ensemble_local_field_scale E' z ha hs (by simpa [E',hm] using E.observe_mass (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb)) hZ hlam
  have hcount : E'.countMoment z (8*a) ≤ B :=
    (E.observe_countMoment _ _ z (8*a)).trans (E.countMoment_le_of_radius z y (by linarith))
  have he := E.observe_excess_budget y hr hb (by linarith) (R := 16*a) (by linarith) hZ hlam.le
  rw [hm,Real.sqrt_one,mul_one] at he
  have hK : (3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2 = localizationIMSConstant/b^2 := by
    unfold localizationIMSConstant
    ring
  rw [hK] at he
  have he' : max (E'.excess Z lam) 0 ≤ max (E.excess Z lam) 0+
      localizationIMSConstant/b^2*Real.sqrt B+
      Real.sqrt (E.outMoment y hr hb Z lam)*Real.sqrt B := by
    apply max_le
    · exact he.trans (add_le_add (add_le_add (le_max_left _ _) le_rfl) le_rfl)
    · have := localizationIMSConstant_nonneg
      positivity
  have ht := (localFieldScale_mono ha he' hcount)
  have hh := hf.trans (mul_le_mul_of_nonneg_left ht localFieldUniversalConstant_pos.le)
  apply hh.trans_eq
  unfold thinFieldBase localFieldScale
  ring

lemma thin_out_feedback (E : CoreObservationEnsemble) (y : Space) {a r b Z lam : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) (hra : r ≤ 6*a) (hb : 0 < b) (hba : b ≤ a)
    (hsep : 20*a ≤ ‖y‖) (hm : E.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    E.outMoment y hr hb Z lam ≤
      512*localFieldUniversalConstant*(thinFieldBase a b (max (E.excess Z lam) 0) (E.countMoment y (16*a))+
        Real.sqrt (E.outMoment y hr hb Z lam)*Real.sqrt (E.countMoment y (16*a))/a) := by
  let E' := E.observe (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb)
  let Q := localFieldUniversalConstant*(thinFieldBase a b (max (E.excess Z lam) 0) (E.countMoment y (16*a))+
        Real.sqrt (E.outMoment y hr hb Z lam)*Real.sqrt (E.countMoment y (16*a))/a)
  have hh := E.outMoment_spatial y hr hb ha (by linarith : r+b+2*a ≤ ‖y‖)
    (by linarith) hZ hlam.le (ballAverageKernel_measurable a) (ballAverageKernel_nonneg ha)
    (ballAverageKernel_support a) (ballAverageKernel_bound ha)
    (ballAverageKernel_radial a) (ballAverageKernel_mass ha)
  have hi8 := E'.fieldMoment_ball_integrable y ha (by linarith : 8*a+a ≤ ‖y‖) hZ hlam.le
  have hsub : closedBall y (r+b+a) ⊆ closedBall y (8*a) := closedBall_subset_closedBall (by linarith)
  have hinc := setIntegral_mono_set hi8 (ae_of_all _ (fun z => E'.fieldMoment_nonneg Z lam z))
    (ae_of_all _ hsub)
  have hc : IntegrableOn (fun _ : Space => Q) (closedBall y (8*a)) :=
    integrableOn_const (isCompact_closedBall y (8*a)).measure_lt_top.ne
  have hmQ := setIntegral_mono_on hi8 hc isClosed_closedBall.measurableSet
    (fun z hz => E.thin_observe_field y z ha hr hra hb hba hsep hz hm hZ hlam)
  have hp : 0 ≤ 1/(a^3*(Real.pi*4/3)) := by positivity
  have hout := hh.trans (mul_le_mul_of_nonneg_left (hinc.trans hmQ) hp)
  rw [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,
    ←Measure.real,space_closedBall_real y (by positivity)] at hout
  have he : 1/(a^3*(Real.pi*4/3))*((8*a)^3*(Real.pi*4/3)*Q) = 512*Q := by
    field_simp [ha.ne',Real.pi_ne_zero]
    ring
  rw [he] at hout
  simpa only [Q,mul_assoc] using hout

theorem thin_out_bound (E : CoreObservationEnsemble) (y : Space) {a r b Z lam : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) (hra : r ≤ 6*a) (hb : 0 < b) (hba : b ≤ a)
    (hsep : 20*a ≤ ‖y‖) (hm : E.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    E.outMoment y hr hb Z lam ≤
      thinOutMajorant a b (max (E.excess Z lam) 0) (E.countMoment y (16*a)) := by
  let X := Real.sqrt (E.outMoment y hr hb Z lam)
  let B := E.countMoment y (16*a)
  let D := 512*localFieldUniversalConstant*Real.sqrt B/a
  let A := 512*localFieldUniversalConstant*thinFieldBase a b (max (E.excess Z lam) 0) B
  have hX : X^2 = E.outMoment y hr hb Z lam := Real.sq_sqrt (E.outMoment_nonneg _ _ _ _ _)
  have hD : D^2 = (512*localFieldUniversalConstant)^2*B/a^2 := by
    dsimp [D]; rw [div_pow,mul_pow,Real.sq_sqrt (E.countMoment_nonneg _ _)]
  have hh := E.thin_out_feedback y ha hr hra hb hba hsep hm hZ hlam
  have hquad : X^2 ≤ A+D*X := by
    rw [hX]
    convert hh using 1; dsimp [A,D,X]; ring
  have hbnd : X^2 ≤ 2*A+D^2 := by nlinarith [sq_nonneg (X-D)]
  rw [hX,hD] at hbnd
  convert hbnd using 1
  all_goals try with_reducible_and_instances rfl
  unfold thinOutMajorant A B
  ring

end CoreObservationEnsemble

open MeasureTheory Set Metric

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_PatchMassSubmeanBarrier
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators

namespace CoreObservationEnsemble

lemma initial_observe_fieldMoment {N : ℕ} (ψ : FormVector N) (hψ : SobolevFermion ψ)
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (z : Space) :
    ((initial ψ hψ).observe p hp).fieldMoment Z lam z =
      ∑ c : Fin N → Fin 2, coreLawAverage (orderedCutForm p hp ψ c) (coreFieldSquare Z lam z) := by
  change (∑ ic : Σ _ : Unit, Fin N → Fin 2,
    coreLawAverage (nextCoreObservation (M := 0) p hp ψ ic.2) (coreFieldSquare Z lam z)) = _
  rw [Fintype.sum_sigma]
  simp only [Finset.univ_unique,Finset.sum_singleton]
  have hh := sum_nextCoreObservation_fieldSquare (M := 0) hψ.sobolevVector p hp hZ hlam z
  change _ = coreLawAverage (M := 0) ψ (fun φ =>
    ∑ c : Fin N → Fin 2, coreLawAverage (orderedCutForm p hp φ c) (coreFieldSquare Z lam z)) at hh
  rwa [coreLawAverage_empty] at hh

lemma initial_outMoment {N : ℕ} (ψ : FormVector N) (hψ : SobolevFermion ψ)
    (y : Space) {r b : ℝ} (hr : 0 ≤ r) (hb : 0 < b) (hy : r+2*b ≤ ‖y‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    (initial ψ hψ).outMoment y hr hb Z lam =
      freshOutMaximumSecondMoment (coreFirstRadialCut y hr hb)
        (coreFirstRadialCut_partition y hr hb) ψ Z lam := by
  change (∑ _i : Unit, (CoreObservationGraph.initial ψ hψ).outMoment y hr hb Z lam) = _
  simp only [Finset.univ_unique,Finset.sum_singleton]
  rw [CoreObservationGraph.outMoment_eq_average _ y hr hb hy hZ hlam]
  exact coreLawAverage_empty _ _

end CoreObservationEnsemble

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_LocalFieldScalarBoundBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom

 def radialOutLinearConstant (C : ℝ) : ℝ :=
    1+1024*localFieldUniversalConstant*(6+C+localizationIMSConstant*C)+
      (512*localFieldUniversalConstant)^2*C
lemma radialOutLinearConstant_one_le {C : ℝ} (hC : 1 ≤ C) : 1 ≤ radialOutLinearConstant C := by
  have := localizationIMSConstant_nonneg
  have := localFieldUniversalConstant_pos
  unfold radialOutLinearConstant
  have hC0 := le_trans zero_le_one hC
  have h1 : 0 ≤ 1024*localFieldUniversalConstant*(6+C+localizationIMSConstant*C) := by positivity
  have h2 : 0 ≤ (512*localFieldUniversalConstant)^2*C := by positivity
  linarith only [h1,h2]

lemma thinOutMajorant_linear_bound {a m D B C : ℝ}
    (ha : 0 < a) (hm : 1 ≤ m) (h3 : 1/a^3 ≤ m) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hC : 1 ≤ C) (hBC : B ≤ C*m^2) :
    thinOutMajorant a a D B ≤ radialOutLinearConstant C*(D/a+(m/a)^2) := by
  let S := (m/a)^2
  let Q := 5+C+localizationIMSConstant*C
  let H := D/a+S
  have hS : 0 ≤ S := sq_nonneg _
  have hD' : 0 ≤ D/a := by positivity
  have hH : 0 ≤ H := add_nonneg hD' hS
  have hI := localizationIMSConstant_nonneg
  have hF := localFieldUniversalConstant_pos.le
  have hC0 := le_trans zero_le_one hC
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hh := thinFieldBase_linear_bound ha hm h3 hB hC hBC (D := D)
  have hf : thinFieldBase a a D B ≤ (1+Q)*H := by
    have hc := mul_nonneg hQ hD'
    dsimp [H]
    nlinarith only [hh,hS,hc]
  have hb : B/a^2 ≤ C*H := by
    have ht := div_le_div_of_nonneg_right hBC (sq_nonneg a)
    have hc := mul_nonneg hC0 hD'
    have hid : (C*m^2)/a^2 = C*S := by dsimp [S]; ring
    rw [hid] at ht
    dsimp [H]
    nlinarith only [ht,hc]
  have h1 := mul_le_mul_of_nonneg_left hf (show 0 ≤ 1024*localFieldUniversalConstant by positivity)
  have h2 := mul_le_mul_of_nonneg_left hb (sq_nonneg (512*localFieldUniversalConstant))
  have ht : thinOutMajorant a a D B ≤ (radialOutLinearConstant C-1)*H := by
    calc _ = 1024*localFieldUniversalConstant*thinFieldBase a a D B+
          (512*localFieldUniversalConstant)^2*(B/a^2) := by unfold thinOutMajorant; ring
         _ ≤ 1024*localFieldUniversalConstant*((1+Q)*H)+
          (512*localFieldUniversalConstant)^2*(C*H) := add_le_add h1 h2
         _ = _ := by unfold radialOutLinearConstant Q; ring
  nlinarith only [ht,hH]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ArbitraryCutExcess
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Metric
noncomputable section
namespace CoulombAtom

 def radialCutExcessConstant (C : ℝ) : ℝ :=
    1+localizationIMSConstant*C+radialOutLinearConstant C+C

 lemma radialCutExcessConstant_one_le {C : ℝ} (hC : 1 ≤ C) :
    1 ≤ radialCutExcessConstant C := by
  have hI := localizationIMSConstant_nonneg
  have hL := radialOutLinearConstant_one_le hC
  unfold radialCutExcessConstant
  have : 0 ≤ localizationIMSConstant*C := mul_nonneg hI (zero_le_one.trans hC)
  linarith

namespace CoreObservationEnsemble

 theorem observe_excess_linear (E : CoreObservationEnsemble) (y : Space)
    {a r Z lam m C : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (hra : r ≤ 6*a)
    (hsep : 20*a ≤ ‖y‖) (hmass : E.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 < lam)
    (hm : 1 ≤ m) (h3 : 1/a^3 ≤ m) (hC : 1 ≤ C)
    (hBC : E.countMoment y (16*a) ≤ C*m^2) :
    max ((E.observe (coreFirstRadialCut y hr ha)
      (coreFirstRadialCut_partition y hr ha)).excess Z lam) 0 ≤
      radialCutExcessConstant C*(max (E.excess Z lam) 0+m^2/a) := by
  let D := max (E.excess Z lam) 0
  let B := E.countMoment y (16*a)
  let O := E.outMoment y hr ha Z lam
  let L := radialOutLinearConstant C
  let T := m^2/a
  have hD : 0 ≤ D := le_max_right _ _
  have hB : 0 ≤ B := E.countMoment_nonneg _ _
  have hO : 0 ≤ O := E.outMoment_nonneg ..
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hL : 1 ≤ L := radialOutLinearConstant_one_le hC
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hroot : Real.sqrt B ≤ C*m := by
    simpa using sqrt_count_scale hB hC (by norm_num : (0:ℝ) ≤ 1)
      (zero_le_one.trans hm) (by simpa using hBC)
  have hout : O ≤ L*(D/a+(m/a)^2) :=
    (E.thin_out_bound y ha hr hra ha le_rfl hsep hmass hZ hlam).trans
      (thinOutMajorant_linear_bound ha hm h3 hD hB hC hBC)
  have hyoung := sqrt_product_weighted_young ha hO hB
  have hmul := mul_le_mul_of_nonneg_left hout ha.le
  have hmul' : a*O ≤ L*(D+T) := by
    calc a*O ≤ a*(L*(D/a+(m/a)^2)) := hmul
         _ = L*(D+T) := by dsimp [T]; field_simp
  have hbdiv : B/a ≤ C*T := by
    calc B/a ≤ (C*m^2)/a := div_le_div_of_nonneg_right hBC ha.le
         _ = C*T := by dsimp [T]; ring
  have hma : m/a^2 ≤ T := by
    have hh := mul_le_mul_of_nonneg_left (cell_reciprocal_bounds ha hm h3).1
      (show 0 ≤ m/a by positivity)
    calc m/a^2 = (m/a)*(1/a) := by ring
         _ ≤ (m/a)*m := hh
         _ = T := by dsimp [T]; ring
  have hI := localizationIMSConstant_nonneg
  have hims : (localizationIMSConstant/a^2)*Real.sqrt B ≤
      localizationIMSConstant*C*T := by
    calc _ ≤ (localizationIMSConstant/a^2)*(C*m) :=
                mul_le_mul_of_nonneg_left hroot (by positivity)
         _ = localizationIMSConstant*C*(m/a^2) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hma (by positivity)
  have hbudget := E.observe_excess_budget y hr ha (by linarith)
    (R := 16*a) (by linarith) hZ hlam.le
  rw [hmass,Real.sqrt_one,mul_one] at hbudget
  have heq : (3/2:ℝ)*(Real.pi*smoothTransitionBound/a)^2 =
      localizationIMSConstant/a^2 := by unfold localizationIMSConstant; ring
  rw [heq] at hbudget
  have hcost : Real.sqrt O*Real.sqrt B ≤ L*(D+T)+C*T := by
    have hp : 0 ≤ L*(D+T)+C*T := by positivity
    linarith only [hyoung,hmul',hbdiv,hp]
  have hpos : 0 ≤ radialCutExcessConstant C*(D+T) :=
    mul_nonneg (zero_le_one.trans (radialCutExcessConstant_one_le hC)) (by positivity)
  apply max_le _ hpos
  have hiD : 0 ≤ localizationIMSConstant*C*D := by positivity
  have hcD : 0 ≤ C*D := by positivity
  have heD : E.excess Z lam ≤ D := le_max_left _ _
  change _ ≤ radialCutExcessConstant C*(D+T)
  unfold radialCutExcessConstant
  dsimp only [L] at hcost
  have hbudget' : (E.observe (coreFirstRadialCut y hr ha)
      (coreFirstRadialCut_partition y hr ha)).excess Z lam ≤
      E.excess Z lam+(localizationIMSConstant/a^2)*Real.sqrt B+
        Real.sqrt O*Real.sqrt B := hbudget
  nlinarith only [hbudget',hims,hcost,heD,hiD,hcD,hT]

end CoreObservationEnsemble
end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_FiniteCellObservation
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Metric
noncomputable section
namespace CoulombAtom
namespace CoreObservationEnsemble

 lemma observeCell_mass (E : CoreObservationEnsemble) (y : Space) :
    (E.observeCell y).mass = E.mass := by
  classical
  unfold observeCell
  split_ifs <;> simp only [observe_mass]

 lemma observeCell_countMoment (E : CoreObservationEnsemble) (y z : Space) (R : ℝ) :
    (E.observeCell y).countMoment z R ≤ E.countMoment z R := by
  classical
  unfold observeCell
  split_ifs
  · exact le_rfl
  · exact observe_countMoment ..

 lemma observeCells_countMoment (E : CoreObservationEnsemble) (ys : List Space)
    (z : Space) (R : ℝ) :
    (E.observeCells ys).countMoment z R ≤ E.countMoment z R := by
  induction ys generalizing E with
  | nil => exact le_rfl
  | cons y ys ih => exact (ih _).trans (observeCell_countMoment ..)

 theorem observeCells_excess (E : CoreObservationEnsemble) (ys : List Space)
    {Z lam C H : ℝ} (hmass : E.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 < lam)
    (hC : 1 ≤ C) (hH : 0 ≤ H)
    (hb : ∀ y ∈ ys, y ≠ 0 ∧ ∃ m : ℝ, 1 ≤ m ∧ 1/(localCellRadius y)^3 ≤ m ∧
      E.countMoment y (16*localCellRadius y) ≤ C*m^2 ∧ m^2/localCellRadius y ≤ H) :
    max ((E.observeCells ys).excess Z lam) 0+H ≤
      (radialCutExcessConstant C+1)^ys.length*(max (E.excess Z lam) 0+H) := by
  classical
  induction ys generalizing E with
  | nil => simpa only [observeCells,List.length_nil,pow_zero,one_mul] using (le_refl (max (E.excess Z lam) 0+H))
  | cons y ys ih =>
    obtain ⟨hy,m,hm,h3,hB,hmH⟩ := hb y (List.mem_cons_self ..)
    have ha := localCellRadius_pos hy
    have hf := E.observe_excess_linear y ha ha.le (by linarith)
      (by unfold localCellRadius; nlinarith [norm_nonneg y]) hmass hZ hlam hm h3 hC hB
    have hp : max ((E.observeCell y).excess Z lam) 0 ≤
        radialCutExcessConstant C*(max (E.excess Z lam) 0+H) := by
      rw [observeCell, dite_eq_right hy]
      apply max_le
      · exact (le_max_left _ _).trans (hf.trans
          (mul_le_mul_of_nonneg_left (add_le_add le_rfl hmH)
            (zero_le_one.trans (radialCutExcessConstant_one_le hC))))
      · exact mul_nonneg (zero_le_one.trans (radialCutExcessConstant_one_le hC))
          (add_nonneg (le_max_right _ _) hH)
    have hb' : ∀ z ∈ ys, z ≠ 0 ∧ ∃ m : ℝ, 1 ≤ m ∧ 1/(localCellRadius z)^3 ≤ m ∧
        (E.observeCell y).countMoment z (16*localCellRadius z) ≤ C*m^2 ∧
          m^2/localCellRadius z ≤ H := by
      intro z hz
      obtain ⟨hz0,m,hm,h3,hB,hH⟩ := hb z (List.mem_cons_of_mem y hz)
      exact ⟨hz0,m,hm,h3,(observeCell_countMoment ..).trans hB,hH⟩
    have h0 : 0 ≤ max (E.excess Z lam) 0 := le_max_right _ _
    have hK : 0 ≤ radialCutExcessConstant C+1 := by
      have := radialCutExcessConstant_one_le hC; linarith
    have hh : max ((E.observeCell y).excess Z lam) 0+H ≤
        (radialCutExcessConstant C+1)*(max (E.excess Z lam) 0+H) := by
      nlinarith only [hp,h0]
    calc
      _ ≤ (radialCutExcessConstant C+1)^ys.length*
            (max ((E.observeCell y).excess Z lam) 0+H) :=
          ih _ ((observeCell_mass E y).trans hmass) hb'
      _ ≤ (radialCutExcessConstant C+1)^ys.length*
            ((radialCutExcessConstant C+1)*(max (E.excess Z lam) 0+H)) :=
          mul_le_mul_of_nonneg_left hh (pow_nonneg hK _)
      _ = _ := by simp only [List.length_cons,pow_succ]; ring

end CoreObservationEnsemble
end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_WeightedCoreStatistics
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set
open scoped BigOperators
noncomputable section
namespace CoulombAtom

def rawWeightedCount {N : ℕ} (f : Space → ℝ) (x : Configuration N) : ℝ := ∑ i, f (x i)
lemma rawWeightedCount_nonneg {N : ℕ} {f : Space → ℝ} (hf : ∀ z, 0 ≤ f z)
    (x : Configuration N) : 0 ≤ rawWeightedCount f x := Finset.sum_nonneg (fun i _ => hf (x i))
lemma rawWeightedCount_le {N : ℕ} {f : Space → ℝ} {A : ℝ} (hf : ∀ z, f z ≤ A)
    (x : Configuration N) : rawWeightedCount f x ≤ N*A := by
  calc _ ≤ ∑ _i : Fin N, A := Finset.sum_le_sum (fun i _ => hf (x i))
       _ = _ := by simp
lemma rawWeightedCount_measurable {N : ℕ} {f : Space → ℝ} (hf : Measurable f) :
    Measurable (rawWeightedCount (N := N) f) :=
  Finset.measurable_sum _ (fun i _ => hf.comp (measurable_pi_apply i))

def rawWeightedMoment {N : ℕ} (psi : FormVector N) (f : Space → ℝ) : ℝ :=
  rawFormPair psi (fun x => rawWeightedCount f x^2)
lemma rawWeightedMoment_nonneg {N : ℕ} (psi : FormVector N) (f : Space → ℝ) :
    0 ≤ rawWeightedMoment psi f :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
lemma rawWeightedMoment_coreSlice_integrable {N M : ℕ} {psi : FormVector (N+M)}
    (hpsi : SobolevVector psi) {f : Space → ℝ} (hm : Measurable f) (hn : ∀ z, 0 ≤ f z)
    {A : ℝ} (hb : ∀ z, f z ≤ A) (t : Spins M) :
    Integrable (fun v => rawWeightedMoment (coreSlice psi t v) f) :=
  rawFormPair_coreSlice_integrable hpsi ((rawWeightedCount_measurable hm).pow_const 2)
    (fun x => norm_sq_le_of_nonneg (rawWeightedCount_nonneg hn x) (rawWeightedCount_le hb x)) t

namespace CoreObservationGraph
 def weightedMoment (G : CoreObservationGraph) (f : Space → ℝ) : ℝ :=
    coreLawAverage G.vector (fun phi => rawWeightedMoment phi f)
end CoreObservationGraph
namespace CoreObservationEnsemble
 def weightedMoment (E : CoreObservationEnsemble) (f : Space → ℝ) : ℝ :=
   ∑ i, (E.graph i).weightedMoment f
 lemma initial_weightedMoment {N : ℕ} (psi : FormVector N) (hpsi : SobolevFermion psi) (f : Space → ℝ) :
   (initial psi hpsi).weightedMoment f = rawWeightedMoment psi f := by
   change (∑ _i : Unit, coreLawAverage (M := 0) psi (fun phi => rawWeightedMoment phi f)) = _
   simp [coreLawAverage_empty]
end CoreObservationEnsemble
end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PacketComparison
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set Metric Laplacian
noncomputable section
namespace CoulombAtom
open CoulombAnalysis

 lemma packetPotentialConstant_one_le : 1 ≤ packetPotentialConstant := by
   unfold packetPotentialConstant
   nlinarith only [mul_nonneg packetDensityConstant_pos.le unitCoulombIntegral_nonneg]

 lemma packet_potential_uniform (y a : Space) {r : ℝ} (hr : 0 < r) :
     tfPotential (packetDensity y r) a ≤ packetPotentialConstant/r := by
   by_cases ha : 2*r ≤ ‖a-y‖
   · change (∫ z, packetDensity y r z/‖a-z‖) ≤ _
     rw [packetDensity_potential y hr (by linarith)]
     exact (div_le_div_of_nonneg_left (by norm_num) hr (by linarith)).trans
       (div_le_div_of_nonneg_right packetPotentialConstant_one_le hr.le)
   · have ha' : ‖a-y‖ < 2*r := lt_of_not_ge ha
     have hk : Integrable (fun z : Space => truncatedCoulomb (3*r) (a-z)) :=
       (integrable_comp_sub_left _ a).mpr (truncatedCoulomb_integrable _)
     calc
       _ ≤ ∫ z : Space, (packetDensityConstant/r^3)*truncatedCoulomb (3*r) (a-z) := by
         apply integral_mono (tfPotential_integrable (packetDensity_integrable y hr)
           (packetDensity_memLp y hr) a) (hk.const_mul _)
         intro z
         change packetDensity y r z / ‖a-z‖ ≤ (packetDensityConstant/r^3)*truncatedCoulomb (3*r) (a-z)
         by_cases hz : packetDensity y r z = 0
         · simp only [hz,zero_div]
           exact mul_nonneg (by positivity [packetDensityConstant_pos]) (truncatedCoulomb_nonneg _ _)
         · have hs := packetDensity_support y hr hz
           have hd : ‖a-z‖ < 3*r := by
             have ht := norm_sub_le a y
             have ht' := norm_sub_le (a-y) (z-y)
             have he : (a-y)-(z-y) = a-z := by abel
             rw [he] at ht'
             linarith only [ht',hs,ha']
           rw [truncatedCoulomb,indicator_of_mem (mem_ball_zero_iff.mpr hd),mul_one_div]
           exact div_le_div_of_nonneg_right (packetDensity_bound y z hr) (norm_nonneg _)
       _ = 9*packetDensityConstant*unitCoulombIntegral/r := by
         rw [integral_const_mul,integral_sub_left_eq_self,truncatedCoulomb_integral (by positivity)]
         field_simp
         ring
       _ ≤ _ := by
         apply div_le_div_of_nonneg_right _ hr.le
         unfold packetPotentialConstant
         linarith

 lemma packet_source_pair_integrable (mu : Measure Space) [IsFiniteMeasure mu]
     (y : Space) {r : ℝ} (hr : 0 < r) :
     Integrable (fun p : Space × Space => packetDensity y r p.2/‖p.1-p.2‖)
       (mu.prod volume) := by
   have hm : Measurable (fun p : Space × Space => packetDensity y r p.2/‖p.1-p.2‖) :=
     ((packetDensity_continuous y r).measurable.comp measurable_snd).div
       (measurable_fst.sub measurable_snd).norm
   apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
   refine ⟨ae_of_all _ (fun a => tfPotential_integrable (packetDensity_integrable y hr)
     (packetDensity_memLp y hr) a),?_⟩
   have hnorm (a : Space) : (∫ z, ‖packetDensity y r z/‖a-z‖‖) =
       tfPotential (packetDensity y r) a := by
     simp only [Real.norm_of_nonneg (div_nonneg (packetDensity_nonneg y r _) (norm_nonneg _)),tfPotential]
   simp only [hnorm]
   apply (integrable_const (packetPotentialConstant/r)).mono'
     (hm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable)
   apply ae_of_all
   intro a
   change ‖(∫ z, packetDensity y r z/‖a-z‖)‖ ≤ _
   rw [Real.norm_of_nonneg (integral_nonneg (fun z => div_nonneg (packetDensity_nonneg y r z) (norm_nonneg _)))]
   exact packet_potential_uniform y a hr

 lemma packet_source_pairing (mu : Measure Space) [IsFiniteMeasure mu]
     (y : Space) {r : ℝ} (hr : 0 < r) :
     (∫ z, packetDensity y r z*sourcePotential mu z) =
       ∫ a, tfPotential (packetDensity y r) a ∂mu := by
   have hi := packet_source_pair_integrable mu y hr
   simp only [sourcePotential,← integral_const_mul,tfPotential]
   calc
     (∫ z, ∫ a, packetDensity y r z*‖z-a‖⁻¹ ∂mu) =
         ∫ z, ∫ a, packetDensity y r z/‖a-z‖ ∂mu := by
       simp only [div_eq_mul_inv,norm_sub_rev]
     _ = _ := (integral_integral_swap hi).symm

 lemma packet_source_integrable (mu : Measure Space) [IsFiniteMeasure mu]
     (y : Space) {r : ℝ} (hr : 0 < r) :
     Integrable (fun z => packetDensity y r z*sourcePotential mu z) := by
   have hi := (packet_source_pair_integrable mu y hr).integral_prod_right
   simpa only [sourcePotential,← integral_const_mul,div_eq_mul_inv,norm_sub_rev] using hi

 lemma packet_outer_potential (y a : Space) {h : ℝ} (hh : 0 < h)
     (hy : ‖y‖ ≤ 2*h) (ha : h < ‖a‖) :
     tfPotential (packetDensity y (h/4)) a ≤ 16*packetPotentialConstant/‖a‖ := by
   have hap : 0 < ‖a‖ := hh.trans ha
   by_cases hfar : 4*h ≤ ‖a‖
   · have hd : ‖a‖/2 ≤ ‖a-y‖ := by
       have ht := norm_le_norm_sub_add a y
       linarith
     change (∫ z, packetDensity y (h/4) z/‖a-z‖) ≤ _
     rw [packetDensity_potential y (by positivity) (by linarith)]
     calc
       _ ≤ 1/(‖a‖/2) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hd
       _ = 2/‖a‖ := by ring
       _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith [packetPotentialConstant_one_le]) hap.le
   · have hnear : ‖a‖ < 4*h := lt_of_not_ge hfar
     calc
       _ ≤ packetPotentialConstant/(h/4) := packet_potential_uniform y a (by positivity)
       _ ≤ 16*packetPotentialConstant/‖a‖ := by
         apply (div_le_div_iff₀ (by positivity : 0 < h/4) hap).mpr
         have hc := packetPotentialConstant_one_le
         nlinarith only [mul_le_mul_of_nonneg_left hnear.le (zero_le_one.trans hc)]

 theorem packet_outer_source_bound (mu : Measure Space) [IsFiniteMeasure mu]
     {h : ℝ} (hh : 0 < h) (hs : ∀ᵐ a ∂mu, h < ‖a‖)
     {y : Space} (hy : ‖y‖ ≤ 2*h) :
     (∫ z, packetDensity y (h/4) z*sourcePotential mu z) ≤
       16*packetPotentialConstant*(∫ a, ‖a‖⁻¹ ∂mu) := by
   have hi : Integrable (fun a : Space => ‖a‖⁻¹) mu := by
     apply (integrable_const (h⁻¹)).mono' (by fun_prop)
     filter_upwards [hs] with a ha
     rw [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
     exact inv_anti₀ hh ha.le
   rw [packet_source_pairing mu y (by positivity),←integral_const_mul]
   apply integral_mono_ae (packet_source_pair_integrable mu y (by positivity)).integral_prod_left
     (hi.const_mul _)
   filter_upwards [hs] with a ha
   simpa only [tfPotential,div_eq_mul_inv] using packet_outer_potential y a hh hy ha

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_OrdinaryDensity
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombAtom

def rawOneParticleLaw {N : ℕ} (μ : Measure (Configuration N)) : Measure Space :=
  Measure.sum (fun i : Fin N => μ.map (fun x => x i))

lemma rawOneParticleLaw_finite {N : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] : IsFiniteMeasure (rawOneParticleLaw μ) := by
  rw [rawOneParticleLaw,Measure.sum_fintype]
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma rawOneParticleLaw_pairing {N : ℕ} (μ : Measure (Configuration N))
    {f : Space → ℝ} (hf : Measurable f) (hi : ∀ i : Fin N, Integrable (fun x => f (x i)) μ) :
    (∫ z, f z ∂rawOneParticleLaw μ) = ∫ x, ∑ i, f (x i) ∂μ := by
  have him (i : Fin N) : Integrable f (μ.map (fun x => x i)) :=
    (integrable_map_measure hf.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).mpr (hi i)
  rw [rawOneParticleLaw,Measure.sum_fintype,integral_finsetSum_measure (fun i _ => him i),
    integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_Inner
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set Metric Laplacian
noncomputable section
namespace CoulombAtom

 def actualParticleSource {N : ℕ} (psi : FormVector N) : Measure Space :=
   ENNReal.ofReal ((formMass psi)⁻¹) • rawOneParticleLaw (formRawLaw psi)

 def actualInnerSource {N : ℕ} (psi : FormVector N) (h : ℝ) : Measure Space :=
   (actualParticleSource psi).restrict {a | ‖a‖ ≤ h}

 lemma actualParticleSource_finite {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) : IsFiniteMeasure (actualParticleSource psi) := by
   let : IsFiniteMeasure (formRawLaw psi) := formRawLaw_finite hpsi
   let : IsFiniteMeasure (rawOneParticleLaw (formRawLaw psi)) := rawOneParticleLaw_finite _
   refine ⟨?_⟩
   change (ENNReal.ofReal ((formMass psi)⁻¹) • rawOneParticleLaw (formRawLaw psi)) Set.univ < ⊤
   rw [Measure.smul_apply]
   exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

 lemma actualInnerSource_finite {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) (h : ℝ) : IsFiniteMeasure (actualInnerSource psi h) := by
   let : IsFiniteMeasure (actualParticleSource psi) := actualParticleSource_finite hpsi
   unfold actualInnerSource
   first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

 lemma actualInnerSource_support {N : ℕ} (psi : FormVector N) (h : ℝ) :
     ∀ᵐ a ∂actualInnerSource psi h, ‖a‖ ≤ h :=
   ae_restrict_mem (measurableSet_le continuous_norm.measurable measurable_const)

 lemma rawOneParticleLaw_potential_integrable {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) (y : Space) :
     Integrable (fun a => ‖y-a‖⁻¹) (rawOneParticleLaw (formRawLaw psi)) := by
   have hm : Measurable (fun a : Space => ‖y-a‖⁻¹) :=
     ((continuous_const.sub continuous_id).norm.measurable).inv
   rw [rawOneParticleLaw,Measure.sum_fintype,integrable_finsetSum_measure]
   intro i _
   apply (integrable_map_measure hm.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).mpr
   apply (rawPotential_form_integrable hpsi y).mono'
     ((hm.comp (measurable_pi_apply i)).aestronglyMeasurable)
   apply ae_of_all
   intro x
   simp only [Function.comp_apply,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
   rw [norm_sub_rev]
   simpa only [one_div,rawPotential] using Finset.single_le_sum (f := fun j : Fin N => 1/‖x j-y‖)
     (fun _ _ => by positivity) (Finset.mem_univ i)

 lemma sourcePotential_rawOneParticleLaw {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) (y : Space) :
     sourcePotential (rawOneParticleLaw (formRawLaw psi)) y = coreCoulombAt psi y := by
   have hm : Measurable (fun a : Space => ‖y-a‖⁻¹) :=
     ((continuous_const.sub continuous_id).norm.measurable).inv
   have hi := rawOneParticleLaw_potential_integrable hpsi y
   rw [rawOneParticleLaw,Measure.sum_fintype,integrable_finsetSum_measure] at hi
   have hp := rawOneParticleLaw_pairing (formRawLaw psi) hm (fun i =>
     (integrable_map_measure hm.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).mp
       (hi i (Finset.mem_univ i)))
   unfold sourcePotential
   rw [hp]
   convert integral_rawPotential_formRawLaw hpsi y using 1
   all_goals try with_reducible_and_instances rfl
   apply integral_congr_ae
   apply ae_of_all
   intro x
   apply Finset.sum_congr rfl
   intro i _
   simp only [one_div,norm_sub_rev]

 lemma actualParticleSource_potential_integrable {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) (y : Space) :
     Integrable (fun a => ‖y-a‖⁻¹) (actualParticleSource psi) :=
   (rawOneParticleLaw_potential_integrable hpsi y).smul_measure ENNReal.ofReal_ne_top

 lemma sourcePotential_actualParticleSource {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) (y : Space) :
     sourcePotential (actualParticleSource psi) y = coreCoulombAt psi y/formMass psi := by
   simp only [sourcePotential,actualParticleSource,integral_smul_measure,
     ENNReal.toReal_ofReal (inv_nonneg.mpr (formMass_nonneg psi)),smul_eq_mul]
   change (formMass psi)⁻¹*sourcePotential (rawOneParticleLaw (formRawLaw psi)) y = _
   rw [sourcePotential_rawOneParticleLaw hpsi]
   ring

 lemma sourceField_actualParticleSource {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) (hm : formMass psi ≠ 0) (Z lam : ℝ) (y : Space) :
     sourceField Z (actualParticleSource psi) y = normalizedCoreField Z lam psi y+lam := by
   rw [sourceField,sourcePotential_actualParticleSource hpsi]
   unfold normalizedCoreField
   field_simp [hm]
   ring

 lemma sourcePotential_inner_add_outer {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) (h : ℝ) (y : Space) :
     sourcePotential (actualInnerSource psi h) y+
         sourcePotential ((actualParticleSource psi).restrict {a | h < ‖a‖}) y =
       sourcePotential (actualParticleSource psi) y := by
   have hc : {a : Space | h < ‖a‖} = {a : Space | ‖a‖ ≤ h}ᶜ := by
     ext a; simp only [mem_ofPred_eq,mem_compl_iff,not_le]
   rw [hc]
   exact integral_add_compl (measurableSet_le continuous_norm.measurable measurable_const)
     (actualParticleSource_potential_integrable hpsi y)

 lemma sourceField_inner_eq {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) (hm : formMass psi ≠ 0) (Z lam h : ℝ) (y : Space) :
     sourceField Z (actualInnerSource psi h) y = normalizedCoreField Z lam psi y+lam+
         sourcePotential ((actualParticleSource psi).restrict {a | h < ‖a‖}) y := by
   have hp := sourcePotential_inner_add_outer hpsi h y
   have hf := sourceField_actualParticleSource hpsi hm Z lam y
   unfold sourceField at hf ⊢
   linarith only [hp,hf]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_InnerFieldCap
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set Metric Laplacian
noncomputable section
namespace CoulombAtom
open CoulombAnalysis

 lemma positiveCoreField_annular_integrable {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) {Z lam h : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) :
     IntegrableOn (fun z => max (normalizedCoreField Z lam psi z) 0) (innerFieldTestAnnulus h) := by
   let : IsFiniteMeasure (volume.restrict (innerFieldTestAnnulus h)) :=
     ⟨by rw [Measure.restrict_apply_univ]; exact innerFieldTestAnnulus_finite h⟩
   apply (integrable_const (Z/h)).mono'
     ((normalizedCoreField_measurable hpsi Z lam).max measurable_const).aestronglyMeasurable
   filter_upwards [ae_restrict_mem (innerFieldTestAnnulus_measurable h)] with z hz
   rw [Real.norm_of_nonneg (le_max_right _ _)]
   exact max_le ((normalizedCoreField_le_nuclear psi hZ hlam z).trans
     (div_le_div_of_nonneg_left hZ hh hz.1)) (div_nonneg hZ hh.le)

 lemma packet_on_inner_annulus {h : ℝ} (hh : 0 < h) {y z : Space}
     (hy : ‖y‖ = 2*h) (hz : packetDensity y (h/4) z ≠ 0) :
     z ∈ innerFieldTestAnnulus h := by
   have hd := packetDensity_support y (show 0 < h/4 by positivity) hz
   have h1 := norm_le_norm_sub_add y z
   have h2 := norm_le_norm_sub_add z y
   rw [norm_sub_rev y z] at h1
   constructor <;> linarith only [hd,h1,h2,hy,hh]

 lemma positiveCoreField_packet_le {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) {Z lam h : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h)
     {y : Space} (hy : ‖y‖ = 2*h) :
     Integrable (fun z => packetDensity y (h/4) z*max (normalizedCoreField Z lam psi z) 0) ∧
     (∫ z, packetDensity y (h/4) z*max (normalizedCoreField Z lam psi z) 0) ≤
       packetDensityConstant/(h/4)^3*
         (∫ z in innerFieldTestAnnulus h, max (normalizedCoreField Z lam psi z) 0) := by
   let A := innerFieldTestAnnulus h
   let F := fun z => max (normalizedCoreField Z lam psi z) 0
   have hi := (positiveCoreField_annular_integrable hpsi hZ hlam hh).integrable_indicator
     (innerFieldTestAnnulus_measurable h)
   have hC : 0 ≤ packetDensityConstant/(h/4)^3 := by positivity [packetDensityConstant_pos]
   have hb (z : Space) : packetDensity y (h/4) z*F z ≤
       packetDensityConstant/(h/4)^3*A.indicator F z := by
     by_cases hz : packetDensity y (h/4) z = 0
     · rw [hz,zero_mul]
       exact mul_nonneg hC (indicator_nonneg (fun z _ => le_max_right _ _) z)
     · rw [indicator_of_mem (packet_on_inner_annulus hh hy hz)]
       exact mul_le_mul_of_nonneg_right (packetDensity_bound y z (by positivity)) (le_max_right _ _)
   have hp : Integrable (fun z => packetDensity y (h/4) z*F z) := by
     apply (hi.const_mul (packetDensityConstant/(h/4)^3)).mono'
       (((packetDensity_continuous y _).measurable.mul
         ((normalizedCoreField_measurable hpsi Z lam).max measurable_const)).aestronglyMeasurable)
     exact ae_of_all _ (fun z => by
       change ‖packetDensity y (h/4) z*F z‖ ≤ _
       rw [Real.norm_of_nonneg (mul_nonneg (packetDensity_nonneg _ _ _) (le_max_right _ _))]
       exact hb z)
   refine ⟨hp,?_⟩
   calc
     _ ≤ ∫ z, packetDensityConstant/(h/4)^3*A.indicator F z := integral_mono hp (hi.const_mul _) hb
     _ = _ := by rw [integral_const_mul,integral_indicator (innerFieldTestAnnulus_measurable h)]

 def actualInnerBoundaryCap {N : ℕ} (psi : FormVector N) (Z lam h : ℝ) : ℝ :=
   packetDensityConstant/(h/4)^3*
     (∫ z in innerFieldTestAnnulus h, max (normalizedCoreField Z lam psi z) 0)+lam+
       16*packetPotentialConstant*(∫ a, ‖a‖⁻¹ ∂(actualParticleSource psi).restrict {a | h < ‖a‖})

 lemma actualInnerBoundaryCap_nonneg {N : ℕ} (psi : FormVector N) (Z : ℝ) {lam h : ℝ}
     (hlam : 0 ≤ lam) (hh : 0 < h) : 0 ≤ actualInnerBoundaryCap psi Z lam h := by
   unfold actualInnerBoundaryCap
   have hp := packetDensityConstant_pos
   have hc := packetPotentialConstant_one_le
   positivity

 theorem actual_inner_boundary_cap {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) (hm : formMass psi ≠ 0) {Z lam h : ℝ}
     (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h)
     {y : Space} (hy : ‖y‖ = 2*h) :
     sourceField Z (actualInnerSource psi h) y ≤ actualInnerBoundaryCap psi Z lam h := by
   let mu := actualInnerSource psi h
   let nu := (actualParticleSource psi).restrict {a | h < ‖a‖}
   let : IsFiniteMeasure (actualParticleSource psi) := actualParticleSource_finite hpsi
   let : IsFiniteMeasure mu := actualInnerSource_finite hpsi h
   have hs : ∀ᵐ a ∂mu, ‖a‖ ≤ h := actualInnerSource_support psi h
   have hnu : ∀ᵐ a ∂nu, h < ‖a‖ :=
     ae_restrict_mem (measurableSet_lt measurable_const continuous_norm.measurable)
   have hball : closedBall y (h/2) ⊆ {z | h < ‖z‖} := by
     intro z hz
     have hd : ‖z-y‖ ≤ h/2 := mem_closedBall.mp hz
     have ht := norm_le_norm_sub_add y z
     rw [norm_sub_rev y z] at ht
     change h < ‖z‖
     linarith only [hy,ht,hd,hh]
   have hu := (sourceField_continuousOn Z mu hh.le hs).mono hball
   have hmean : (∫ z, packetDensity y (h/4) z*sourceField Z mu z) = sourceField Z mu y :=
     weak_harmonic_packet_mean_local hu (by positivity) (by linarith)
       (fun g hg hcg hsg => sourceField_weak_harmonic Z mu hh.le hs hg hcg
         (hsg.trans (ball_subset_closedBall.trans hball)))
   have hleft : Integrable (fun z => packetDensity y (h/4) z*sourceField Z mu z) := by
     apply Integrable.congr (continuousOn_mul_integrable_support (isCompact_closedBall y (h/2)) hu
       (packetDensity_continuous y (h/4)) (fun z hz => ?_))
     · exact ae_of_all _ (fun z => mul_comm _ _)
     · rw [mem_closedBall]
       have hd := packetDensity_support y (show 0 < h/4 by positivity) hz
       rw [dist_eq_norm]
       linarith
   obtain ⟨hpos,hposB⟩ := positiveCoreField_packet_le hpsi hZ hlam hh hy
   have hout := packet_source_integrable nu y (show 0 < h/4 by positivity)
   have houtB := packet_outer_source_bound nu hh hnu hy.le
   have hconst := (packetDensity_integrable y (show 0 < h/4 by positivity)).mul_const lam
   have hb (z : Space) : packetDensity y (h/4) z*sourceField Z mu z ≤
       packetDensity y (h/4) z*max (normalizedCoreField Z lam psi z) 0+
         packetDensity y (h/4) z*lam+packetDensity y (h/4) z*sourcePotential nu z := by
     have he := sourceField_inner_eq hpsi hm Z lam h z
     change sourceField Z mu z = normalizedCoreField Z lam psi z+lam+sourcePotential nu z at he
     rw [he,mul_add,mul_add]
     have hh := mul_le_mul_of_nonneg_left
       (le_max_left (normalizedCoreField Z lam psi z) 0) (packetDensity_nonneg y (h/4) z)
     linarith only [hh]
   have hb' := integral_mono hleft ((hpos.add hconst).add hout) hb
   simp only [Pi.add_apply] at hb'
   have hab := integral_add (hpos.add hconst) hout
   have hac := integral_add hpos hconst
   simp only [Pi.add_apply] at hab hac
   rw [hmean,hab,hac,integral_mul_const,
     packetDensity_mass y (show 0 < h/4 by positivity),one_mul] at hb'
   unfold actualInnerBoundaryCap
   change sourceField Z mu y ≤ _
   linarith only [hb',hposB,houtB]

 theorem actual_inner_exterior_cap {N : ℕ} {psi : FormVector N}
     (hpsi : SobolevVector psi) (hm : formMass psi ≠ 0) {Z lam h : ℝ}
     (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) {y : Space} (hy : 2*h ≤ ‖y‖) :
     sourceField Z (actualInnerSource psi h) y ≤ actualInnerBoundaryCap psi Z lam h*(2*h)/‖y‖ := by
   let : IsFiniteMeasure (actualInnerSource psi h) := actualInnerSource_finite hpsi h
   exact sourceField_exterior_comparison Z _ hh.le (by linarith)
     (actualInnerBoundaryCap_nonneg psi Z hlam hh) (actualInnerSource_support psi h)
     (fun z hz => actual_inner_boundary_cap hpsi hm hZ hlam hh hz) hy

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CoulombTailStatistic
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set
open scoped BigOperators
noncomputable section
namespace CoulombAtom

def coulombTailWeight (h : ℝ) (a : Space) : ℝ := if h < ‖a‖ then ‖a‖⁻¹ else 0
lemma coulombTailWeight_measurable (h : ℝ) : Measurable (coulombTailWeight h) :=
  continuous_norm.measurable.inv.ite (measurableSet_lt measurable_const continuous_norm.measurable) measurable_const
lemma coulombTailWeight_nonneg (h : ℝ) (a : Space) : 0 ≤ coulombTailWeight h a := by
  unfold coulombTailWeight; split_ifs <;> positivity
lemma coulombTailWeight_le {h : ℝ} (hh : 0 < h) (a : Space) : coulombTailWeight h a ≤ 1/h := by
  unfold coulombTailWeight
  split_ifs with ha
  · simpa only [one_div] using inv_anti₀ hh ha.le
  · positivity

lemma rawWeightedFirst_le_sqrt {N : ℕ} {psi : FormVector N} (hpsi : SobolevVector psi)
    {f : Space → ℝ} (hm : Measurable f) (hn : ∀ z, 0 ≤ f z) {A : ℝ} (hb : ∀ z, f z ≤ A) :
    rawFormPair psi (rawWeightedCount f) ≤ Real.sqrt (rawWeightedMoment psi f)*Real.sqrt (formMass psi) := by
  have hc := weighted_sum_integral_cauchy (fun _ : Spins N => volume)
    (fun s x => ‖psi.value s x‖^2) (fun _ => rawWeightedCount f) (fun _ _ => 1)
    (fun _ _ => sq_nonneg _)
    (fun s => rawFormPair_integrable hpsi ((rawWeightedCount_measurable hm).pow_const 2)
      (fun x => norm_sq_le_of_nonneg (rawWeightedCount_nonneg hn x) (rawWeightedCount_le hb x)) s)
    (fun s => by simpa only [one_pow,one_mul] using (hpsi.1 s).norm.integrable_sq)
    (fun s => by
      simpa only [mul_one] using (rawFormPair_integrable hpsi (rawWeightedCount_measurable hm)
        (fun x => by rw [Real.norm_of_nonneg (rawWeightedCount_nonneg hn x)]; exact rawWeightedCount_le hb x) s))
  simpa only [mul_one,one_pow,one_mul,rawFormPair,rawWeightedMoment,formMass] using hc

lemma actual_tail_eq_raw {N : ℕ} {psi : FormVector N} (hpsi : SobolevVector psi)
    {h : ℝ} (hh : 0 < h) :
    (∫ a, ‖a‖⁻¹ ∂(actualParticleSource psi).restrict {a | h < ‖a‖}) =
      rawFormPair psi (rawWeightedCount (coulombTailWeight h))/formMass psi := by
  let f := coulombTailWeight h
  have hm : Measurable f := coulombTailWeight_measurable h
  have hn : ∀ z, 0 ≤ f z := coulombTailWeight_nonneg h
  have hb : ∀ z, f z ≤ 1/h := coulombTailWeight_le hh
  let : IsFiniteMeasure (formRawLaw psi) := formRawLaw_finite hpsi
  have hi (i : Fin N) : Integrable (fun x : Configuration N => f (x i)) (formRawLaw psi) := by
    apply (integrable_const (1/h)).mono' (hm.comp (measurable_pi_apply i)).aestronglyMeasurable
    exact ae_of_all _ (fun x => by change ‖f (x i)‖ ≤ _; rw [Real.norm_of_nonneg (hn _)]; exact hb _)
  have hp := rawOneParticleLaw_pairing (formRawLaw psi) hm hi
  have hr := rawFormPair_eq_integral hpsi (rawWeightedCount_measurable hm)
    (fun x => by rw [Real.norm_of_nonneg (rawWeightedCount_nonneg hn x)]; exact rawWeightedCount_le hb x)
  have hind : (fun a : Space => ({a | h < ‖a‖} : Set Space).indicator (fun a => ‖a‖⁻¹) a) = f := rfl
  rw [←integral_indicator (measurableSet_lt measurable_const continuous_norm.measurable),hind]
  simp only [actualParticleSource,integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (formMass_nonneg psi)),smul_eq_mul]
  rw [hp]
  change (formMass psi)⁻¹*(∫ x, rawWeightedCount f x ∂formRawLaw psi) = _
  rw [←hr]
  ring

theorem actual_tail_square_le {N : ℕ} {psi : FormVector N} (hpsi : SobolevVector psi)
    {h : ℝ} (hh : 0 < h) :
    (∫ a, ‖a‖⁻¹ ∂(actualParticleSource psi).restrict {a | h < ‖a‖})^2*formMass psi ≤
      rawWeightedMoment psi (coulombTailWeight h) := by
  rw [actual_tail_eq_raw hpsi hh]
  by_cases hm : formMass psi = 0
  · simp only [hm,mul_zero]; exact rawWeightedMoment_nonneg _ _
  have hm' : 0 < formMass psi := lt_of_le_of_ne (formMass_nonneg psi) (Ne.symm hm)
  have hn : 0 ≤ rawFormPair psi (rawWeightedCount (coulombTailWeight h)) :=
    Finset.sum_nonneg (fun s _ => integral_nonneg (fun x =>
      mul_nonneg (rawWeightedCount_nonneg (coulombTailWeight_nonneg h) x) (sq_nonneg _)))
  have hc := pow_le_pow_left₀ hn
    (rawWeightedFirst_le_sqrt hpsi (coulombTailWeight_measurable h)
      (coulombTailWeight_nonneg h) (coulombTailWeight_le hh)) 2
  rw [mul_pow,Real.sq_sqrt (rawWeightedMoment_nonneg _ _),Real.sq_sqrt hm'.le] at hc
  have he : (rawFormPair psi (rawWeightedCount (coulombTailWeight h))/formMass psi)^2*formMass psi =
      (rawFormPair psi (rawWeightedCount (coulombTailWeight h)))^2/formMass psi := by field_simp
  rw [he]
  exact (div_le_iff₀ hm').2 hc

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_InnerCapStatistic
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

section
open MeasureTheory Filter Set
open scoped BigOperators

def innerFieldVolume (h : ℝ) : ℝ := volume.real (innerFieldTestAnnulus h)
lemma innerFieldVolume_nonneg (h : ℝ) : 0 ≤ innerFieldVolume h := measureReal_nonneg

lemma positiveCoreField_annular_sq_integrable {N : ℕ} {psi : FormVector N}
    (hpsi : SobolevVector psi) {Z lam h : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) :
    IntegrableOn (fun z => (max (normalizedCoreField Z lam psi z) 0)^2) (innerFieldTestAnnulus h) := by
  let : IsFiniteMeasure (volume.restrict (innerFieldTestAnnulus h)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact innerFieldTestAnnulus_finite h⟩
  apply (integrable_const ((Z/h)^2)).mono'
    (((normalizedCoreField_measurable hpsi Z lam).max measurable_const).pow_const 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (innerFieldTestAnnulus_measurable h)] with z hz
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (le_max_right _ _) (normalizedCoreField_pos_le psi hZ hlam hh hz.1) 2

lemma positiveCoreField_annular_cauchy {N : ℕ} {psi : FormVector N}
    (hpsi : SobolevVector psi) {Z lam h : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) :
    (∫ z in innerFieldTestAnnulus h, max (normalizedCoreField Z lam psi z) 0)^2 ≤
      innerFieldVolume h*(∫ z in innerFieldTestAnnulus h, (max (normalizedCoreField Z lam psi z) 0)^2) := by
  let mu := volume.restrict (innerFieldTestAnnulus h)
  let : IsFiniteMeasure mu := ⟨by rw [Measure.restrict_apply_univ]; exact innerFieldTestAnnulus_finite h⟩
  let f := fun z => max (normalizedCoreField Z lam psi z) 0
  have h1 : Integrable f mu := positiveCoreField_annular_integrable hpsi hZ hlam hh
  have h2 : Integrable (fun z => f z^2) mu := positiveCoreField_annular_sq_integrable hpsi hZ hlam hh
  have hc := weighted_sum_integral_cauchy (fun _ : Unit => mu)
    (fun _ _ => (1:ℝ)) (fun _ z => f z) (fun _ _ => (1:ℝ))
    (fun _ _ => zero_le_one)
    (fun _ => by simpa only [mul_one] using h2)
    (fun _ => by simpa only [one_pow,one_mul] using (integrable_const (1:ℝ) : Integrable (fun _ : Space => (1:ℝ)) mu))
    (fun _ => by simpa only [mul_one] using h1)
  simp only [Finset.univ_unique,Finset.sum_singleton,mul_one,one_pow,integral_const,
    smul_eq_mul,Measure.real] at hc
  have hsq := pow_le_pow_left₀ (integral_nonneg (fun z => le_max_right _ _)) hc 2
  rw [mul_pow,Real.sq_sqrt (integral_nonneg (fun z => sq_nonneg _)),
    Real.sq_sqrt (by dsimp [mu]; positivity)] at hsq
  simpa only [f,mu,innerFieldVolume,Measure.real,Measure.restrict_apply_univ,mul_comm] using hsq

def innerCapStatistic {N : ℕ} (psi : FormVector N) (Z lam h : ℝ) : ℝ :=
  3*(packetDensityConstant/(h/4)^3)^2*innerFieldVolume h*
    (∫ z in innerFieldTestAnnulus h, coreFieldSquare Z lam z psi)+
    3*lam^2*formMass psi+3*(16*packetPotentialConstant)^2*rawWeightedMoment psi (coulombTailWeight h)

lemma innerCapStatistic_nonneg {N : ℕ} (psi : FormVector N) (Z lam h : ℝ) :
    0 ≤ innerCapStatistic psi Z lam h := by
  unfold innerCapStatistic
  have hv := innerFieldVolume_nonneg h
  have hf : 0 ≤ ∫ z in innerFieldTestAnnulus h, coreFieldSquare Z lam z psi :=
    integral_nonneg (fun z => coreFieldSquare_nonneg Z lam z psi)
  have hm := formMass_nonneg psi
  have ht := rawWeightedMoment_nonneg psi (coulombTailWeight h)
  positivity

theorem actualInnerBoundaryCap_sq_le_statistic {N : ℕ} {psi : FormVector N}
    (hpsi : SobolevVector psi) {Z lam h : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) :
    (actualInnerBoundaryCap psi Z lam h)^2*formMass psi ≤ innerCapStatistic psi Z lam h := by
  let A := packetDensityConstant/(h/4)^3
  let B := 16*packetPotentialConstant
  let U := ∫ z in innerFieldTestAnnulus h, max (normalizedCoreField Z lam psi z) 0
  let T := ∫ a, ‖a‖⁻¹ ∂(actualParticleSource psi).restrict {a | h < ‖a‖}
  let M := formMass psi
  have hM : 0 ≤ M := formMass_nonneg psi
  have hU := mul_le_mul_of_nonneg_right (positiveCoreField_annular_cauchy hpsi hZ hlam hh) hM
  have hT := actual_tail_square_le hpsi hh
  have hx : (A*U+lam+B*T)^2 ≤ 3*((A*U)^2+lam^2+(B*T)^2) := by
    nlinarith only [sq_nonneg (A*U-lam),sq_nonneg (A*U-B*T),sq_nonneg (lam-B*T)]
  have hxm := mul_le_mul_of_nonneg_right hx hM
  have he : (∫ z in innerFieldTestAnnulus h, coreFieldSquare Z lam z psi) =
      (∫ z in innerFieldTestAnnulus h, (max (normalizedCoreField Z lam psi z) 0)^2)*M := by
    exact integral_mul_const M _
  unfold actualInnerBoundaryCap innerCapStatistic
  rw [he]
  change (A*U+lam+B*T)^2*M ≤
    3*A^2*innerFieldVolume h*((∫ z in innerFieldTestAnnulus h, (max (normalizedCoreField Z lam psi z) 0)^2)*M)+
      3*lam^2*M+3*B^2*rawWeightedMoment psi (coulombTailWeight h)
  have h1 := mul_le_mul_of_nonneg_left hU (show 0 ≤ 3*A^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hT (show 0 ≤ 3*B^2 by positivity)
  nlinarith only [hxm,h1,h2]

end
open MeasureTheory Filter Set Metric
open scoped BigOperators

lemma innerFieldAnnulus_weight_eq (h : ℝ) (f : Space → ℝ) :
    (∫ z, f z*innerFieldAnnulusWeight h z) = ∫ z in innerFieldTestAnnulus h, f z := by
  rw [←integral_indicator (innerFieldTestAnnulus_measurable h)]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by by_cases hz : z ∈ innerFieldTestAnnulus h <;> simp [innerFieldAnnulusWeight,hz])

lemma coreFieldSquare_annular_statistic_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) {Z lam h : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) :
    Integrable (fun u => ∫ z in innerFieldTestAnnulus h, coreFieldSquare Z lam z (coreSlice ψ t u)) := by
  have hi := (coreFieldSquare_weighted_prod_integrable hψ t hZ hlam hh
    (innerFieldAnnulusWeight_integrable h) (innerFieldAnnulusWeight_nonneg h)
    (innerFieldAnnulusWeight_separation h)).integral_prod_left
  simpa only [innerFieldAnnulus_weight_eq] using hi

lemma coreFieldSquare_annular_fubini {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) {Z lam h : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) :
    coreLawAverage ψ (fun φ => ∫ z in innerFieldTestAnnulus h, coreFieldSquare Z lam z φ) =
      ∫ z in innerFieldTestAnnulus h, coreLawAverage ψ (coreFieldSquare Z lam z) := by
  have he := coreFieldSquare_weighted_fubini hψ Z lam hZ hlam hh
    (innerFieldAnnulusWeight_integrable h) (innerFieldAnnulusWeight_nonneg h)
    (innerFieldAnnulusWeight_separation h)
  simpa only [innerFieldAnnulus_weight_eq] using he

lemma innerCapStatistic_coreSlice_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) {Z lam h : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) :
    Integrable (fun u => innerCapStatistic (coreSlice ψ t u) Z lam h) := by
  unfold innerCapStatistic
  exact (((coreFieldSquare_annular_statistic_integrable hψ t hZ hlam hh).const_mul _).add
    ((hψ.coreSlice_mass_integrable t).const_mul _)).add
    ((rawWeightedMoment_coreSlice_integrable hψ (coulombTailWeight_measurable h)
      (coulombTailWeight_nonneg h) (coulombTailWeight_le hh) t).const_mul _)

namespace CoreObservationGraph

def innerCapAverage (G : CoreObservationGraph) (Z lam h : ℝ) : ℝ :=
  coreLawAverage G.vector (fun φ => innerCapStatistic φ Z lam h)

lemma innerCapAverage_eq (G : CoreObservationGraph) {Z lam h : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) :
    G.innerCapAverage Z lam h =
      3*(packetDensityConstant/(h/4)^3)^2*innerFieldVolume h*
        (∫ z in innerFieldTestAnnulus h, G.fieldMoment Z lam z)+
      3*lam^2*G.mass+3*(16*packetPotentialConstant)^2*G.weightedMoment (coulombTailWeight h) := by
  have he : G.innerCapAverage Z lam h =
      3*(packetDensityConstant/(h/4)^3)^2*innerFieldVolume h*
        coreLawAverage G.vector (fun φ => ∫ z in innerFieldTestAnnulus h, coreFieldSquare Z lam z φ)+
      3*lam^2*coreLawAverage G.vector formMass+
      3*(16*packetPotentialConstant)^2*G.weightedMoment (coulombTailWeight h) := by
    unfold innerCapAverage coreLawAverage innerCapStatistic weightedMoment coreLawAverage
    rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    dsimp only
    have hA : Integrable (fun v => 3*(packetDensityConstant/(h/4)^3)^2*innerFieldVolume h*
        (∫ z in innerFieldTestAnnulus h, coreFieldSquare Z lam z (coreSlice G.vector t v))) :=
      (coreFieldSquare_annular_statistic_integrable G.sobolev t hZ hlam hh).const_mul _
    have hB : Integrable (fun v => 3*lam^2*formMass (coreSlice G.vector t v)) :=
      (G.sobolev.coreSlice_mass_integrable t).const_mul _
    have hC : Integrable (fun v => 3*(16*packetPotentialConstant)^2*
        rawWeightedMoment (coreSlice G.vector t v) (coulombTailWeight h)) :=
      (rawWeightedMoment_coreSlice_integrable G.sobolev (coulombTailWeight_measurable h)
        (coulombTailWeight_nonneg h) (coulombTailWeight_le hh) t).const_mul _
    have hAB := integral_add hA hB
    have hABC := integral_add (hA.add hB) hC
    simp only [Pi.add_apply] at hABC hAB
    rw [hABC,hAB]
    simp only [integral_const_mul]
  rw [he,coreFieldSquare_annular_fubini G.sobolev hZ hlam hh,coreLawAverage_mass G.sobolev]
  rfl
end CoreObservationGraph

namespace CoreObservationEnsemble

def innerCapAverage (E : CoreObservationEnsemble) (Z lam h : ℝ) : ℝ :=
  ∑ i, (E.graph i).innerCapAverage Z lam h

lemma innerCapAverage_eq (E : CoreObservationEnsemble) {Z lam h : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) :
    E.innerCapAverage Z lam h =
      3*(packetDensityConstant/(h/4)^3)^2*innerFieldVolume h*
        (∫ z in innerFieldTestAnnulus h, E.fieldMoment Z lam z)+
      3*lam^2*E.mass+3*(16*packetPotentialConstant)^2*E.weightedMoment (coulombTailWeight h) := by
  unfold innerCapAverage
  simp_rw [CoreObservationGraph.innerCapAverage_eq _ hZ hlam hh]
  simp only [Finset.sum_add_distrib,←Finset.mul_sum]
  unfold fieldMoment mass weightedMoment
  rw [integral_finsetSum _ (fun i _ => (E.graph i).fieldMoment_annular_integrable hZ hlam hh)]

lemma innerCapAverage_bound (E : CoreObservationEnsemble) {Z lam h F T : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) (hm : E.mass = 1)
    (hf : ∀ z ∈ innerFieldTestAnnulus h, E.fieldMoment Z lam z ≤ F)
    (ht : E.weightedMoment (coulombTailWeight h) ≤ T) :
    E.innerCapAverage Z lam h ≤
      3*(packetDensityConstant/(h/4)^3)^2*(innerFieldVolume h)^2*F+
      3*lam^2+3*(16*packetPotentialConstant)^2*T := by
  rw [innerCapAverage_eq E hZ hlam hh,hm,mul_one]
  have hI : (∫ z in innerFieldTestAnnulus h, E.fieldMoment Z lam z) ≤ innerFieldVolume h*F := by
    let : IsFiniteMeasure (volume.restrict (innerFieldTestAnnulus h)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact innerFieldTestAnnulus_finite h⟩
    have hb := integral_mono_ae (E.fieldMoment_annular_integrable hZ hlam hh)
      (integrable_const F) (ae_restrict_of_forall_mem (innerFieldTestAnnulus_measurable h) hf)
    simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,innerFieldVolume] using hb
  have hcoef : 0 ≤ 3*(packetDensityConstant/(h/4)^3)^2*innerFieldVolume h := by
    have := innerFieldVolume_nonneg h; positivity
  calc
    _ ≤ 3*(packetDensityConstant/(h/4)^3)^2*innerFieldVolume h*(innerFieldVolume h*F)+
        3*lam^2+3*(16*packetPotentialConstant)^2*T :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hI hcoef) le_rfl)
        (mul_le_mul_of_nonneg_left ht (by positivity))
    _ = _ := by ring
end CoreObservationEnsemble

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CoulombTailNumerics
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter Set
open scoped BigOperators

open MeasureTheory Filter Set
open scoped BigOperators
open CoulombObservation CoulombBarrier

def truncatedTailWeight (h : ℝ) (K : ℕ) (a : Space) : ℝ :=
  if h < ‖a‖ ∧ ‖a‖ ≤ tailRadius h K then ‖a‖⁻¹ else 0

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_SharpJointComparisonBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation

def radialPatchGapMean {N : ℕ} (ψ : FormVector N) (y : Space) {r b : ℝ}
    (hr0 : 0 ≤ r) (hb : 0 < b) (Z lam : ℝ) : ℝ :=
  ∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
    weightedPatchGap (orderedCutForm (coreFirstRadialCut y hr0 hb)
      (coreFirstRadialCut_partition y hr0 hb) ψ c) s Z lam y (r-4*b) hb
      (radialPatchRetention N y r b c s) u

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ObservedInnerCap
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped BigOperators

structure FullStatistic where
  value : ∀ N, Configuration N → ℝ
  measurable : ∀ N, Measurable (value N)
  bounded : ∀ N, ∃ B : ℝ, ∀ x, ‖value N x‖ ≤ B
  reindex : ∀ {M N} (e : Fin M ≃ Fin N) (x : Configuration M),
    value N (x ∘ e.symm) = value M x

lemma rawFormPair_reindex {M N : ℕ} (e : Fin M ≃ Fin N) (psi : FormVector N)
    (F : FullStatistic) : rawFormPair (reindexForm e psi) (F.value M) = rawFormPair psi (F.value N) := by
  have he (s : Spins M) :
      (∫ x, F.value M x*‖(reindexForm e psi).value s x‖^2) =
      ∫ x, F.value N x*‖psi.value (s ∘ e.symm) x‖^2 := by
    simpa only [reindexForm,F.reindex] using
      integral_reindex e (fun x => F.value N x*‖psi.value (s ∘ e.symm) x‖^2)
  unfold rawFormPair
  simp_rw [he]
  exact sum_spin_reindex e (fun s : Spins N => ∫ x, F.value N x*‖psi.value s x‖^2)

lemma rawFormPair_nextCoreObservation {N M : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2=1)
    (psi : FormVector (N+M)) (c : Fin N → Fin 2) (F : FullStatistic) :
    rawFormPair (nextCoreObservation p hp psi c) (F.value _) =
      rawFormPair (multiplyForm (coreLiftMultiplier M (spatialProduct p hp c)) psi) (F.value _) := by
  unfold nextCoreObservation repeatedCutForm
  rw [rawFormPair_reindex,rawFormPair_reindex]

lemma sum_rawFormPair_nextCoreObservation {N M : ℕ} {psi : FormVector (N+M)}
    (hpsi : SobolevVector psi) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2=1) (F : FullStatistic) :
    (∑ c : Fin N → Fin 2, rawFormPair (nextCoreObservation p hp psi c) (F.value _)) =
      rawFormPair psi (F.value _) := by
  simp_rw [rawFormPair_nextCoreObservation]
  obtain ⟨B,hB⟩ := F.bounded (N+M)
  unfold rawFormPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have hi (c : Fin N → Fin 2) : Integrable (fun x => F.value (N+M) x*
      ‖(multiplyForm (coreLiftMultiplier M (spatialProduct p hp c)) psi).value s x‖^2) :=
    (((hpsi.multiply _).1 s).norm.integrable_sq).bdd_mul (F.measurable _).aestronglyMeasurable
      (ae_of_all _ hB)
  rw [←integral_finsetSum _ (fun c _ => hi c)]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have hs : ∑ c : Fin N → Fin 2, (coreLiftMultiplier M (spatialProduct p hp c)).value x^2 = 1 := by
    exact spatial_square_partition p hp (leftList x)
  simp only [multiplyForm,Complex.norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [←Finset.mul_sum,←Finset.sum_mul,hs]
  ring

namespace CoreObservationGraph
 def fullAverage (G : CoreObservationGraph) (F : FullStatistic) : ℝ :=
    rawFormPair G.vector (F.value _)
 lemma observe_fullAverage (G : CoreObservationGraph)
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2=1)
    (F : FullStatistic) :
    (∑ c : Fin G.coreSize → Fin 2, (G.observe p hp c).fullAverage F) = G.fullAverage F :=
    sum_rawFormPair_nextCoreObservation G.sobolev p hp F
end CoreObservationGraph
namespace CoreObservationEnsemble
 def fullAverage (E : CoreObservationEnsemble) (F : FullStatistic) : ℝ :=
    ∑ i, (E.graph i).fullAverage F
 lemma initial_fullAverage {N : ℕ} (psi : FormVector N) (hpsi : SobolevFermion psi) (F : FullStatistic) :
    (initial psi hpsi).fullAverage F = rawFormPair psi (F.value N) := by
    change (∑ _i : Unit, rawFormPair psi (F.value N)) = _
    simp
end CoreObservationEnsemble

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SelectionNumerics
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
namespace CoulombAtom

lemma oneBody_coordinate_derivative {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (i j : Fin N) (a : Fin 3) (x : Configuration N) :
    lineDeriv ℝ (fun y : Configuration N => p.value (y i)) x (direction j a) =
      if j = i then lineDeriv ℝ p.value (x i) (spaceDirections a) else 0 := by
  exact spatial_coordinate_derivative (fun _ : Fin 2 => p) 0 i j a x

def SmoothMultiplier.oneBody {N : ℕ} (p : SmoothMultiplier spaceDirections) (i : Fin N) :
    SmoothMultiplier (sectorDirections N) where
  value := fun x => p.value (x i)
  regular := p.regular.comp (electronProjection i).contDiff
  bound := by obtain ⟨C,hC⟩ := p.bound; exact ⟨C,fun x => hC (x i)⟩
  gradient_bound := by
    intro j
    obtain ⟨C,hC⟩ := p.gradient_bound j.2
    refine ⟨max C 0, fun x => ?_⟩
    change |lineDeriv ℝ (fun y : Configuration N => p.value (y i)) x (direction j.1 j.2)| ≤ _
    rw [oneBody_coordinate_derivative]
    split_ifs
    · exact (hC (x i)).trans (le_max_left _ _)
    · exact (by simpa only [abs_zero] using (le_max_right C 0))

def oneBodySquareTotal {N : ℕ} (p : SmoothMultiplier spaceDirections) :
    FermionMultiplier N where
  toSmoothMultiplier := SmoothMultiplier.sumSquares p.oneBody
  symmetric := by
    intro π x
    change (∑ i, p.value ((x ∘ π) i)^2) = ∑ i,p.value (x i)^2
    exact Equiv.sum_comp π (fun i => p.value (x i)^2)

lemma oneBodySquareTotal_value {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (x : Configuration N) : (oneBodySquareTotal p).value x = ∑ i,p.value (x i)^2 := rfl

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_dShellForm
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section Reused_ShellForm

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace CoulombAtom
attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy
  graphNuclear weightedMass weightedNuclear weightedPairs weightedCoreDensity
  oneBodySquareTotal SmoothMultiplier.oneBody weightedKinetic weightedGradient
  weightedFullDensity graphKineticPair sectorExcessOperator

def oneBodyGradientError {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) : ℝ :=
  ∑ s,∑ i,∑ a,∫ x,(lineDeriv ℝ p.value (x i) (spaceDirections a))^2*
    ‖graphComponent s none F x‖^2

attribute [local irreducible] oneBodyGradientError

end CoulombAtom
end Reused_ShellForm

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_ClosedInnerStatistic
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Filter
open scoped BigOperators
noncomputable section
namespace CoulombAtom

def innerParticleWeight (h : ℝ) (y a : Space) : ℝ := if ‖a‖ ≤ h then ‖y-a‖⁻¹ else 0
lemma innerParticleWeight_measurable (h : ℝ) (y : Space) : Measurable (innerParticleWeight h y) :=
  ((continuous_const.sub continuous_id).norm.measurable.inv).ite
    (measurableSet_le continuous_norm.measurable measurable_const) measurable_const
lemma innerParticleWeight_nonneg (h : ℝ) (y a : Space) : 0 ≤ innerParticleWeight h y a := by
  unfold innerParticleWeight; split_ifs <;> positivity
lemma innerParticleWeight_le {h d : ℝ} (hd : 0 < d) {y : Space} (hy : h+d ≤ ‖y‖) (a : Space) :
    innerParticleWeight h y a ≤ 1/d := by
  unfold innerParticleWeight
  split_ifs with ha
  · have hn := norm_le_norm_sub_add y a
    have hh : d ≤ ‖y-a‖ := by linarith
    simpa only [one_div] using inv_anti₀ hd hh
  · positivity

lemma sourcePotential_actualInnerSource_raw {N : ℕ} {psi : FormVector N}
    (hpsi : SobolevVector psi) {h d : ℝ} (hd : 0 < d) {y : Space} (hy : h+d ≤ ‖y‖) :
    sourcePotential (actualInnerSource psi h) y =
      rawFormPair psi (rawWeightedCount (innerParticleWeight h y))/formMass psi := by
  let f := innerParticleWeight h y
  have hm : Measurable f := innerParticleWeight_measurable h y
  have hn : ∀ z, 0 ≤ f z := innerParticleWeight_nonneg h y
  have hb : ∀ z, f z ≤ 1/d := innerParticleWeight_le hd hy
  let : IsFiniteMeasure (formRawLaw psi) := formRawLaw_finite hpsi
  have hi (i : Fin N) : Integrable (fun x : Configuration N => f (x i)) (formRawLaw psi) := by
    apply (integrable_const (1/d)).mono' (hm.comp (measurable_pi_apply i)).aestronglyMeasurable
    exact ae_of_all _ (fun x => by change ‖f (x i)‖ ≤ _; rw [Real.norm_of_nonneg (hn _)]; exact hb _)
  have hp := rawOneParticleLaw_pairing (formRawLaw psi) hm hi
  have hr := rawFormPair_eq_integral hpsi (rawWeightedCount_measurable hm)
    (fun x => by rw [Real.norm_of_nonneg (rawWeightedCount_nonneg hn x)]; exact rawWeightedCount_le hb x)
  unfold sourcePotential actualInnerSource
  rw [←integral_indicator (measurableSet_le continuous_norm.measurable measurable_const)]
  change (∫ a, f a ∂actualParticleSource psi) = _
  simp only [actualParticleSource,integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (formMass_nonneg psi)),smul_eq_mul]
  rw [hp]
  change (formMass psi)⁻¹*(∫ x, rawWeightedCount f x ∂formRawLaw psi) = _
  rw [←hr]
  ring

def closedRawInnerField {N : ℕ} (Z h : ℝ) (x : Configuration N) (y : Space) : ℝ :=
  Z/‖y‖-rawWeightedCount (innerParticleWeight h y) x

lemma closedRawInnerField_measurable (N : ℕ) (Z h : ℝ) :
    Measurable (fun xy : Configuration N × Space => closedRawInnerField Z h xy.1 xy.2) := by
  unfold closedRawInnerField rawWeightedCount innerParticleWeight
  apply Measurable.sub (measurable_const.div measurable_snd.norm)
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_snd.sub ((measurable_pi_apply i).comp measurable_fst)).norm.inv).ite
    (measurableSet_le (((measurable_pi_apply i).comp measurable_fst).norm) measurable_const) measurable_const

lemma closedRawInnerField_bound {N : ℕ} (Z : ℝ) {h a : ℝ} (ha : 0 < a) (hh : h+a ≤ 2*a)
    {y : Space} (hy : 2*a ≤ ‖y‖) (x : Configuration N) :
    ‖closedRawInnerField Z h x y‖ ≤ |Z|/(2*a)+(N:ℝ)/a := by
  have hn : 0 ≤ rawWeightedCount (innerParticleWeight h y) x :=
    rawWeightedCount_nonneg (innerParticleWeight_nonneg h y) x
  have hb := rawWeightedCount_le (innerParticleWeight_le ha (hh.trans hy)) x
  calc
    _ ≤ ‖Z/‖y‖‖+‖rawWeightedCount (innerParticleWeight h y) x‖ := norm_sub_le _ _
    _ = |Z|/‖y‖+rawWeightedCount (innerParticleWeight h y) x := by
      rw [norm_div,Real.norm_eq_abs,Real.norm_of_nonneg (norm_nonneg y),Real.norm_of_nonneg hn]
    _ ≤ |Z|/(2*a)+(N:ℝ)/a := by
      exact add_le_add (div_le_div_of_nonneg_left (abs_nonneg Z) (by positivity) hy) (by simpa only [mul_one_div] using hb)

lemma rawFormPair_closedRawInnerField {N : ℕ} {psi : FormVector N}
    (hpsi : SobolevVector psi) {Z h d : ℝ} (hd : 0 < d) {y : Space} (hy : h+d ≤ ‖y‖)
    (hm : formMass psi ≠ 0) :
    rawFormPair psi (fun x => closedRawInnerField Z h x y) =
      sourceField Z (actualInnerSource psi h) y*formMass psi := by
  have hb (x : Configuration N) : ‖rawWeightedCount (innerParticleWeight h y) x‖ ≤ (N:ℝ)*(1/d) := by
    rw [Real.norm_of_nonneg (rawWeightedCount_nonneg (innerParticleWeight_nonneg h y) x)]
    exact rawWeightedCount_le (innerParticleWeight_le hd hy) x
  have hi (s : Spins N) := rawFormPair_integrable hpsi
    (rawWeightedCount_measurable (innerParticleWeight_measurable h y)) hb s
  rw [sourceField,sourcePotential_actualInnerSource_raw hpsi hd hy]
  unfold rawFormPair closedRawInnerField
  simp_rw [sub_mul,integral_sub (((hpsi.1 _).norm.integrable_sq).const_mul _) (hi _),integral_const_mul]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum]
  change Z/‖y‖*formMass psi-rawFormPair psi (rawWeightedCount (innerParticleWeight h y)) = _
  field_simp
  rfl

lemma rawWeightedCount_reindex {M N : ℕ} (f : Space → ℝ) (e : Fin M ≃ Fin N) (x : Configuration M) :
    rawWeightedCount f (x ∘ e.symm) = rawWeightedCount f x :=
  Equiv.sum_comp e.symm (fun i => f (x i))

lemma closedRawInnerField_reindex {M N : ℕ} (Z h : ℝ) (e : Fin M ≃ Fin N)
    (x : Configuration M) (y : Space) : closedRawInnerField Z h (x ∘ e.symm) y = closedRawInnerField Z h x y := by
  unfold closedRawInnerField; rw [rawWeightedCount_reindex]
lemma rawWeightedCount_join {N M : ℕ} (f : Space → ℝ) (x : Configuration N) (v : Configuration M) :
    rawWeightedCount f (joinLists x v) = rawWeightedCount f x+rawWeightedCount f v := by
  unfold rawWeightedCount
  rw [←Equiv.sum_comp finSumFinEquiv,Fintype.sum_sum_type]
  simp only [joinLists_left,joinLists_right]

lemma closedRawInnerField_join {N M : ℕ} (Z h : ℝ) (x : Configuration N) (v : Configuration M)
    (hv : ∀ i, h < ‖v i‖) (y : Space) :
    closedRawInnerField Z h (joinLists x v) y = closedRawInnerField Z h x y := by
  unfold closedRawInnerField
  rw [rawWeightedCount_join]
  have hz : rawWeightedCount (innerParticleWeight h y) v = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (not_le.mpr (hv i))
  rw [hz,add_zero]
end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_ShellMeanStatistic
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Filter
open scoped BigOperators
noncomputable section
namespace CoulombAtom
attribute [local irreducible] oneBodySquareTotal graphFormVector fermionGraph

def closedShellField {N : ℕ} (p : SmoothMultiplier spaceDirections) (Z h : ℝ)
    (x : Configuration N) : ℝ := ∑ i, p.value (x i)^2*closedRawInnerField Z h x (x i)
def shellMeanField {N : ℕ} (p : SmoothMultiplier spaceDirections) (Z h : ℝ)
    (x : Configuration N) : ℝ := closedShellField p Z h x/(oneBodySquareTotal p).value x

lemma oneBodySquareTotal_nonneg {N : ℕ} (p : SmoothMultiplier spaceDirections) (x : Configuration N) :
    0 ≤ (oneBodySquareTotal p).value x := by
  rw [oneBodySquareTotal_value]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
lemma closedShellField_measurable (N : ℕ) (p : SmoothMultiplier spaceDirections) (Z h : ℝ) :
    Measurable (closedShellField (N := N) p Z h) := by
  unfold closedShellField
  apply Finset.measurable_sum
  intro i _
  have h1 : Measurable (fun x : Configuration N => p.value (x i)) :=
    p.regular.continuous.measurable.comp (measurable_pi_apply i)
  have h2 : Measurable (fun x : Configuration N => (x,x i)) :=
    measurable_id.prodMk (measurable_pi_apply i)
  have h3 : Measurable (fun x : Configuration N => closedRawInnerField Z h x (x i)) :=
    by simpa only [Function.comp_def] using (closedRawInnerField_measurable N Z h).comp h2
  exact (h1.pow_const 2).mul h3

lemma shellMeanField_measurable (N : ℕ) (p : SmoothMultiplier spaceDirections) (Z h : ℝ) :
    Measurable (shellMeanField (N := N) p Z h) :=
  (closedShellField_measurable N p Z h).div (oneBodySquareTotal p).regular.continuous.measurable

lemma closedShellField_bound {N : ℕ} (p : SmoothMultiplier spaceDirections) (Z : ℝ)
    {h a : ℝ} (ha : 0 < a) (hh : h ≤ a) (hp : ∀ y, p.value y ≠ 0 → 2*a ≤ ‖y‖)
    (x : Configuration N) :
    |closedShellField p Z h x| ≤ (|Z|/(2*a)+(N:ℝ)/a)*(oneBodySquareTotal p).value x := by
  calc
    _ ≤ ∑ i, |p.value (x i)^2*closedRawInnerField Z h x (x i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (|Z|/(2*a)+(N:ℝ)/a)*p.value (x i)^2 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : p.value (x i) = 0
      · simp only [hi,zero_pow (by decide : 2 ≠ 0),zero_mul,mul_zero,abs_zero,le_refl]
      · rw [abs_mul,abs_of_nonneg (sq_nonneg _),mul_comm (p.value (x i)^2)]
        exact mul_le_mul_of_nonneg_right (closedRawInnerField_bound Z ha (by linarith) (hp _ hi) x) (sq_nonneg _)
    _ = _ := by rw [←Finset.mul_sum,oneBodySquareTotal_value]

lemma shellMeanField_bound {N : ℕ} (p : SmoothMultiplier spaceDirections) (Z : ℝ)
    {h a : ℝ} (ha : 0 < a) (hh : h ≤ a) (hp : ∀ y, p.value y ≠ 0 → 2*a ≤ ‖y‖)
    (x : Configuration N) :
    ‖shellMeanField p Z h x‖ ≤ |Z|/(2*a)+(N:ℝ)/a := by
  unfold shellMeanField
  rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (oneBodySquareTotal_nonneg p x)]
  by_cases hs : (oneBodySquareTotal p).value x = 0
  · rw [hs,div_zero]; positivity
  · apply (div_le_iff₀ ((oneBodySquareTotal_nonneg p x).lt_of_ne' hs)).2
    exact closedShellField_bound p Z ha hh hp x

lemma oneBodySquareTotal_reindex {M N : ℕ} (p : SmoothMultiplier spaceDirections)
    (e : Fin M ≃ Fin N) (x : Configuration M) :
    (oneBodySquareTotal p).value (x ∘ e.symm) = (oneBodySquareTotal p).value x :=
  by simpa only [oneBodySquareTotal_value,Function.comp_apply] using Equiv.sum_comp e.symm (fun i => p.value (x i)^2)
lemma closedShellField_reindex {M N : ℕ} (p : SmoothMultiplier spaceDirections) (Z h : ℝ)
    (e : Fin M ≃ Fin N) (x : Configuration M) :
    closedShellField p Z h (x ∘ e.symm) = closedShellField p Z h x := by
  unfold closedShellField
  simp_rw [closedRawInnerField_reindex]
  exact Equiv.sum_comp e.symm (fun i => p.value (x i)^2*closedRawInnerField Z h x (x i))

def shellMeanStatistic (p : SmoothMultiplier spaceDirections) (Z : ℝ)
    {h a : ℝ} (ha : 0 < a) (hh : h ≤ a) (hp : ∀ y, p.value y ≠ 0 → 2*a ≤ ‖y‖) : FullStatistic where
  value := fun _ => shellMeanField p Z h
  measurable := fun N => shellMeanField_measurable N p Z h
  bounded := fun N => ⟨|Z|/(2*a)+(N:ℝ)/a,shellMeanField_bound p Z ha hh hp⟩
  reindex := fun e x => by unfold shellMeanField; rw [closedShellField_reindex,oneBodySquareTotal_reindex]

lemma oneBodySquareTotal_join {N M : ℕ} (p : SmoothMultiplier spaceDirections)
    (x : Configuration N) (v : Configuration M) :
    (oneBodySquareTotal p).value (joinLists x v) =
      (oneBodySquareTotal p).value x+(oneBodySquareTotal p).value v := by
  simpa only [oneBodySquareTotal_value,rawWeightedCount] using rawWeightedCount_join (fun z => p.value z^2) x v

lemma closedShellField_join {N M : ℕ} (p : SmoothMultiplier spaceDirections) (Z h : ℝ)
    (x : Configuration N) (v : Configuration M) (hx : ∀ i, p.value (x i) = 0)
    (hv : ∀ i, h < ‖v i‖) :
    closedShellField p Z h (joinLists x v) =
      ∑ i, p.value (v i)^2*closedRawInnerField Z h x (v i) := by
  unfold closedShellField
  rw [←Equiv.sum_comp finSumFinEquiv,Fintype.sum_sum_type]
  simp only [joinLists_left,joinLists_right,closedRawInnerField_join Z h x v hv,hx,
    zero_pow (by decide : 2 ≠ 0),zero_mul,Finset.sum_const_zero,zero_add]

lemma shellMeanField_join {N M : ℕ} (p : SmoothMultiplier spaceDirections) (Z h : ℝ)
    (x : Configuration N) (v : Configuration M) (hx : ∀ i, p.value (x i) = 0)
    (hv : ∀ i, h < ‖v i‖) :
    shellMeanField p Z h (joinLists x v) =
      (∑ i, p.value (v i)^2*closedRawInnerField Z h x (v i))/(oneBodySquareTotal p).value v := by
  unfold shellMeanField
  rw [closedShellField_join p Z h x v hx hv,oneBodySquareTotal_join]
  have hz : (oneBodySquareTotal p).value x = 0 := by
    simp only [oneBodySquareTotal_value,hx,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero]
  rw [hz,zero_add]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_InnerLinearCap
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Filter
noncomputable section
namespace CoulombAtom
lemma actual_inner_linear_statistic {N : ℕ} {psi : FormVector N}
    (hpsi : SobolevVector psi) {Z lam h a : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam)
    (hh : 0 < h) (ha : h ≤ a) {y : Space} (hy : 2*a ≤ ‖y‖) :
    sourceField Z (actualInnerSource psi h) y*formMass psi ≤
      (h/a)*Real.sqrt (innerCapStatistic psi Z lam h)*Real.sqrt (formMass psi) := by
  have hap : 0 < a := hh.trans_le ha
  have hm := formMass_nonneg psi
  by_cases hm0 : formMass psi = 0
  · simp only [hm0,mul_zero,Real.sqrt_zero,le_refl]
  have hcap := actual_inner_exterior_cap hpsi hm0 hZ hlam hh (by linarith)
  have hc := actualInnerBoundaryCap_nonneg psi Z hlam hh
  have h1 : sourceField Z (actualInnerSource psi h) y ≤ actualInnerBoundaryCap psi Z lam h*(h/a) := by
    calc
      _ ≤ actualInnerBoundaryCap psi Z lam h*(2*h/‖y‖) := by simpa only [mul_div_assoc] using hcap
      _ ≤ actualInnerBoundaryCap psi Z lam h*(2*h/(2*a)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) (by positivity) hy) hc
      _ = _ := by congr 1; field_simp
  have hsq := actualInnerBoundaryCap_sq_le_statistic hpsi hZ hlam hh
  have hstat := innerCapStatistic_nonneg psi Z lam h
  have hroot : actualInnerBoundaryCap psi Z lam h*Real.sqrt (formMass psi) ≤
      Real.sqrt (innerCapStatistic psi Z lam h) := by
    apply (sq_le_sq₀ (mul_nonneg hc (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)).mp
    simpa only [mul_pow,Real.sq_sqrt hm,Real.sq_sqrt hstat] using hsq
  have h2 := mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg (formMass psi))
  rw [mul_assoc,←sq,Real.sq_sqrt hm] at h2
  calc
    _ ≤ actualInnerBoundaryCap psi Z lam h*(h/a)*formMass psi := mul_le_mul_of_nonneg_right h1 hm
    _ = (h/a)*(actualInnerBoundaryCap psi Z lam h*formMass psi) := by ring
    _ ≤ (h/a)*(Real.sqrt (innerCapStatistic psi Z lam h)*Real.sqrt (formMass psi)) :=
      mul_le_mul_of_nonneg_left h2 (div_nonneg hh.le hap.le)
    _ = _ := by ring
end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_FullSliceStatistics
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped BigOperators
noncomputable section
namespace CoulombAtom

def fullSlicePair {N M : ℕ} (psi : FormVector (N+M)) (F : FullStatistic)
    (t : Spins M) (v : Configuration M) : ℝ :=
  ∑ s : Spins N, ∫ x : Configuration N, F.value (N+M) (joinLists x v)*‖(coreSlice psi t v).value s x‖^2

lemma fullSlicePair_integrable {N M : ℕ} {psi : FormVector (N+M)}
    (hpsi : SobolevVector psi) (F : FullStatistic) (t : Spins M) :
    Integrable (fullSlicePair psi F t) := by
  obtain ⟨B,hB⟩ := F.bounded (N+M)
  apply integrable_finsetSum
  intro s _
  have hi := rawFormPair_integrable hpsi (F.measurable (N+M)) hB (joinLists s t)
  exact (integrable_join hi).integral_prod_right

lemma fullSlicePair_fubini {N M : ℕ} {psi : FormVector (N+M)}
    (hpsi : SobolevVector psi) (F : FullStatistic) :
    (∑ t : Spins M, ∫ v, fullSlicePair psi F t v) = rawFormPair psi (F.value (N+M)) := by
  obtain ⟨B,hB⟩ := F.bounded (N+M)
  have hi (s : Spins (N+M)) := rawFormPair_integrable hpsi (F.measurable (N+M)) hB s
  have he (s : Spins N) (t : Spins M) :
      (∫ v : Configuration M, ∫ x : Configuration N,
        F.value (N+M) (joinLists x v)*‖(coreSlice psi t v).value s x‖^2) =
        ∫ x, F.value (N+M) x*‖psi.value (joinLists s t) x‖^2 :=
    integral_join (hi (joinLists s t))
  have hsum (t : Spins M) : (∫ v, fullSlicePair psi F t v) =
      ∑ s : Spins N, ∫ v : Configuration M, ∫ x : Configuration N,
        F.value (N+M) (joinLists x v)*‖(coreSlice psi t v).value s x‖^2 := by
    apply integral_finsetSum
    intro s _
    exact (integrable_join (hi (joinLists s t))).integral_prod_right
  simp_rw [hsum,he]
  exact sum_spin_join (fun s : Spins (N+M) => ∫ x,F.value (N+M) x*‖psi.value s x‖^2)

lemma fullSlicePair_eq_zero_of_mass {N M : ℕ} {psi : FormVector (N+M)}
    (F : FullStatistic) (t : Spins M) (v : Configuration M)
    (hpsi : SobolevVector (coreSlice psi t v)) (hm : formMass (coreSlice psi t v) = 0) :
    fullSlicePair psi F t v = 0 := by
  have hz (s : Spins N) : ∀ᵐ x, ‖(coreSlice psi t v).value s x‖^2 = 0 := by
    have hi : (∫ x, ‖(coreSlice psi t v).value s x‖^2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => integral_nonneg fun x => sq_nonneg _)).mp hm s
        (Finset.mem_univ _)
    exact (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) (hpsi.1 s).norm.integrable_sq).mp hi
  apply Finset.sum_eq_zero
  intro s _
  apply integral_eq_zero_of_ae
  filter_upwards [hz s] with x hx
  simp only [hx,mul_zero,Pi.zero_apply]

lemma SplitPositionSupport.outer_of_mass_ne_zero {N M : ℕ} {psi : FormVector (N+M)}
    {P Q : Space → Prop} (hs : SplitPositionSupport psi P Q)
    (t : Spins M) (v : Configuration M) (hm : formMass (coreSlice psi t v) ≠ 0) :
    ∀ i, Q (v i) := by
  by_contra! hh
  obtain ⟨i,hi⟩ := hh
  apply hm
  have hz : ∀ s x, (coreSlice psi t v).value s x = 0 := by
    intro s x
    by_contra hn
    exact hi ((hs s t x v hn).2 i)
  simp only [formMass,hz,norm_zero,zero_pow (by decide : 2 ≠ 0),integral_zero,Finset.sum_const_zero]
end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_ConditionalShellField
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

section
open MeasureTheory Set Filter
open scoped BigOperators
attribute [local irreducible] oneBodySquareTotal graphFormVector fermionGraph

lemma shell_closed_inner_term_integrable {N : ℕ} {psi : FormVector N}
    (hpsi : SobolevVector psi) (p : SmoothMultiplier spaceDirections) (Z : ℝ)
    {h a : ℝ} (ha : 0 < a) (hh : h ≤ a) (hp : ∀ y, p.value y ≠ 0 → 2*a ≤ ‖y‖)
    (y : Space) (S : ℝ) (s : Spins N) :
    Integrable (fun x => (p.value y^2/S)*(closedRawInnerField Z h x y*‖psi.value s x‖^2)) := by
  by_cases hz : p.value y = 0
  · simp only [hz,zero_pow (by decide : 2 ≠ 0),zero_div,zero_mul]
    exact integrable_zero _ _ _
  have hf : Measurable (fun x : Configuration N => closedRawInnerField Z h x y) :=
    by simpa only [Function.comp_def,id_eq] using
      (closedRawInnerField_measurable N Z h).comp (measurable_id.prodMk measurable_const)
  exact (rawFormPair_integrable hpsi hf
    (closedRawInnerField_bound Z ha (by linarith) (hp y hz)) s).const_mul _

lemma fullSlicePair_shellMean {N M : ℕ} {psi : FormVector (N+M)}
    (p : SmoothMultiplier spaceDirections) (Z : ℝ) {h a : ℝ}
    (ha : 0 < a) (hh : h ≤ a) (hp : ∀ y, p.value y ≠ 0 → 2*a ≤ ‖y‖)
    (hs : SplitPositionSupport psi (fun z => p.value z = 0) (fun z => h < ‖z‖))
    (t : Spins M) (v : Configuration M) (hpsi : SobolevVector (coreSlice psi t v))
    (hm : formMass (coreSlice psi t v) ≠ 0) :
    fullSlicePair psi (shellMeanStatistic p Z ha hh hp) t v =
      ∑ i : Fin M, (p.value (v i)^2/(oneBodySquareTotal p).value v)*
        rawFormPair (coreSlice psi t v) (fun x => closedRawInnerField Z h x (v i)) := by
  have hv := hs.outer_of_mass_ne_zero t v hm
  have he (s : Spins N) :
      (∫ x : Configuration N, shellMeanField p Z h (joinLists x v)*‖(coreSlice psi t v).value s x‖^2) =
      ∑ i : Fin M, (p.value (v i)^2/(oneBodySquareTotal p).value v)*
        (∫ x : Configuration N, closedRawInnerField Z h x (v i)*‖(coreSlice psi t v).value s x‖^2) := by
    calc
      _ = ∫ x : Configuration N, ∑ i : Fin M,
          (p.value (v i)^2/(oneBodySquareTotal p).value v)*
            (closedRawInnerField Z h x (v i)*‖(coreSlice psi t v).value s x‖^2) := by
        apply integral_congr_ae
        apply ae_of_all
        intro x
        dsimp only
        by_cases hz : (coreSlice psi t v).value s x = 0
        · simp only [hz,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,Finset.sum_const_zero]
        · rw [shellMeanField_join p Z h x v (hs s t x v hz).1 hv]
          simp only [Finset.sum_div,Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = ∑ i : Fin M, ∫ x : Configuration N,
          (p.value (v i)^2/(oneBodySquareTotal p).value v)*
            (closedRawInnerField Z h x (v i)*‖(coreSlice psi t v).value s x‖^2) :=
        integral_finsetSum _ (fun i _ => shell_closed_inner_term_integrable hpsi p Z ha hh hp _ _ s)
      _ = _ := by simp only [integral_const_mul]
  change (∑ s : Spins N, ∫ x : Configuration N,
    shellMeanField p Z h (joinLists x v)*‖(coreSlice psi t v).value s x‖^2) = _
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.mul_sum]
  rfl

lemma fullSlicePair_shellMean_le {N M : ℕ} {psi : FormVector (N+M)}
    (p : SmoothMultiplier spaceDirections) {Z lam h a : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) (ha : h ≤ a)
    (hp : ∀ y, p.value y ≠ 0 → 2*a ≤ ‖y‖)
    (hs : SplitPositionSupport psi (fun z => p.value z = 0) (fun z => h < ‖z‖))
    (t : Spins M) (v : Configuration M) (hpsi : SobolevVector (coreSlice psi t v)) :
    fullSlicePair psi (shellMeanStatistic p Z (hh.trans_le ha) ha hp) t v ≤
      (h/a)*Real.sqrt (innerCapStatistic (coreSlice psi t v) Z lam h)*
        Real.sqrt (formMass (coreSlice psi t v)) := by
  let C := (h/a)*Real.sqrt (innerCapStatistic (coreSlice psi t v) Z lam h)*
        Real.sqrt (formMass (coreSlice psi t v))
  have hap : 0 < a := hh.trans_le ha
  have hC : 0 ≤ C := by dsimp [C]; positivity
  by_cases hm : formMass (coreSlice psi t v) = 0
  · rw [fullSlicePair_eq_zero_of_mass _ t v hpsi hm]
    exact hC
  rw [fullSlicePair_shellMean p Z (hh.trans_le ha) ha hp hs t v hpsi hm]
  have hS := oneBodySquareTotal_nonneg p v
  calc
    _ ≤ ∑ i : Fin M, (p.value (v i)^2/(oneBodySquareTotal p).value v)*C := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : p.value (v i) = 0
      · simp only [hi,zero_pow (by decide : 2 ≠ 0),zero_div,zero_mul,le_refl]
      · have hy := hp _ hi
        have hr := rawFormPair_closedRawInnerField (Z := Z) hpsi (hh.trans_le ha)
          (show h+a ≤ ‖v i‖ by linarith) hm
        rw [hr]
        exact mul_le_mul_of_nonneg_left (actual_inner_linear_statistic hpsi hZ hlam hh ha hy)
          (div_nonneg (sq_nonneg _) hS)
    _ = ((oneBodySquareTotal p).value v/(oneBodySquareTotal p).value v)*C := by
      rw [←Finset.sum_mul,←Finset.sum_div,oneBodySquareTotal_value]
    _ ≤ C := by
      by_cases hz : (oneBodySquareTotal p).value v = 0
      · rw [hz,div_zero,zero_mul]; exact hC
      · rw [div_self hz,one_mul]

end
open MeasureTheory Filter
open scoped BigOperators
namespace CoreObservationEnsemble
lemma fullAverage_shellMean_le (E : CoreObservationEnsemble)
    (p : SmoothMultiplier spaceDirections) {Z lam h a : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) (ha : h ≤ a)
    (hp : ∀ y, p.value y ≠ 0 → 2*a ≤ ‖y‖)
    (hs : E.supported (fun z => p.value z = 0) (fun z => h < ‖z‖)) :
    E.fullAverage (shellMeanStatistic p Z (hh.trans_le ha) ha hp) ≤
      (h/a)*Real.sqrt (E.innerCapAverage Z lam h)*Real.sqrt E.mass := by
  let I := Σ i : E.Branch, Spins (E.graph i).outSize
  let X : I → Type := fun i => Configuration (E.graph i.1).outSize
  let H : ∀ i : I, X i → ℝ := fun i v => innerCapStatistic (coreSlice (E.graph i.1).vector i.2 v) Z lam h
  let W : ∀ i : I, X i → ℝ := fun i v => formMass (coreSlice (E.graph i.1).vector i.2 v)
  have hH (i : I) : Integrable (H i) := innerCapStatistic_coreSlice_integrable (E.graph i.1).sobolev i.2 hZ hlam hh
  have hW (i : I) : Integrable (W i) := (E.graph i.1).sobolev.coreSlice_mass_integrable i.2
  have hnH (i : I) (v : X i) : 0 ≤ H i v := innerCapStatistic_nonneg ..
  have hnW (i : I) (v : X i) : 0 ≤ W i v := formMass_nonneg _
  have hc := sum_integral_sqrt_mul_sqrt_le (fun i : I => (volume : Measure (X i))) H W hH hW hnH hnW
  let F := shellMeanStatistic p Z (hh.trans_le ha) ha hp
  have hi (i : I) :
      (∫ v : X i, fullSlicePair (E.graph i.1).vector F i.2 v) ≤
        (h/a)*(∫ v : X i, Real.sqrt (H i v)*Real.sqrt (W i v)) := by
    rw [←integral_const_mul]
    apply integral_mono_ae (fullSlicePair_integrable (E.graph i.1).sobolev F i.2)
      ((integrable_sqrt_mul_sqrt (hH i) (hW i) (hnH i) (hnW i)).const_mul _)
    filter_upwards [(E.graph i.1).sobolev.ae_coreSlice i.2] with v hv
    simpa only [mul_assoc] using fullSlicePair_shellMean_le p hZ hlam hh ha hp (hs i.1) i.2 v hv
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  rw [←Finset.mul_sum] at hsum
  have heF : (∑ i : I, ∫ v : X i, fullSlicePair (E.graph i.1).vector F i.2 v) = E.fullAverage F := by
    rw [Fintype.sum_sigma]
    exact Finset.sum_congr rfl (fun i _ => fullSlicePair_fubini (E.graph i).sobolev F)
  have heH : (∑ i : I, ∫ v : X i, H i v) = E.innerCapAverage Z lam h := by
    rw [Fintype.sum_sigma]
    rfl
  have heW : (∑ i : I, ∫ v : X i, W i v) = E.mass := by
    rw [Fintype.sum_sigma]
    exact Finset.sum_congr rfl (fun i _ => (E.graph i).sobolev.integral_coreSlice_mass)
  rw [heF] at hsum
  rw [heH,heW] at hc
  exact hsum.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hc (div_nonneg hh.le (hh.trans_le ha).le))
end CoreObservationEnsemble

end CoulombAtom

end

end OAI
end


