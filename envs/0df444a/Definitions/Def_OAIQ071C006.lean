-- Prove2me | Definitions.Def_OAIQ071C006
-- name    : OAIQ071C006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T05:12:20.380596+00:00
-- url     : https://prove2.me/theorems/ec2aa335-9cc1-4897-99a6-2b081a76f6fb
-- title:
--   Definitions bundle OAIQ071C006 of the split of OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 370 declarations of OpenAI's Lean: 74 definitions, 3 inductive types or structures, 2 instances and 291 theorems. The definitions and types are `OAI.CoulombAtom.CoreLocalHistory`, `OAI.CoulombAtom.CoreObservationEnsemble`, `OAI.CoulombAtom.CoreObservationEnsemble.countMoment`, `OAI.CoulombAtom.CoreObservationEnsemble.excess`, `OAI.CoulombAtom.CoreObservationEnsemble.fieldMoment`, `OAI.CoulombAtom.CoreObservationEnsemble.initial`, `OAI.CoulombAtom.CoreObservationEnsemble.mass`, `OAI.CoulombAtom.CoreObservationEnsemble.observe`, `OAI.CoulombAtom.CoreObservationEnsemble.observeCell`, `OAI.CoulombAtom.CoreObservationEnsemble.observeCells`, `OAI.CoulombAtom.CoreObservationEnsemble.supported`, `OAI.CoulombAtom.CoreObservationGraph`, `OAI.CoulombAtom.CoreObservationGraph.countMoment`, `OAI.CoulombAtom.CoreObservationGraph.excess`, `OAI.CoulombAtom.CoreObservationGraph.fieldMoment`, `OAI.CoulombAtom.CoreObservationGraph.initial`, `OAI.CoulombAtom.CoreObservationGraph.mass`, `OAI.CoulombAtom.CoreObservationGraph.observe`, `OAI.CoulombAtom.CoreObservationGraph.supported`, `OAI.CoulombAtom.OriginalDatum`, `OAI.CoulombAtom.SplitPositionSupport`, `OAI.CoulombAtom.UnorderedConfiguration`, `OAI.CoulombAtom.bindingApprox`, `OAI.CoulombAtom.bindingCappedSum`, `OAI.CoulombAtom.bindingNuclearSum`, `OAI.CoulombAtom.bindingPairApprox`, `OAI.CoulombAtom.bindingPairSum`, `OAI.CoulombAtom.bindingWeight`, `OAI.CoulombAtom.conditionalPatchCenter`, `OAI.CoulombAtom.conditionalPatchField`, `OAI.CoulombAtom.configurationSetoid`, `OAI.CoulombAtom.coreCapEnvelope`, `OAI.CoulombAtom.coreFieldSquare`, `OAI.CoulombAtom.coreFirstRadialCut`, `OAI.CoulombAtom.coreLawAverage`, `OAI.CoulombAtom.coreLiftMultiplier`, `OAI.CoulombAtom.cutCoreEnergy`, `OAI.CoulombAtom.cutCoreExcess`, `OAI.CoulombAtom.expectedRadialPatchCenter`, `OAI.CoulombAtom.graphKineticPair` and 37 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CoulombIonization_Fermionic_CorePotentialTower`, `CoulombIonization_Fermionic_CutCountDomination`, `CoulombIonization_Fermionic_QuantumEventMultiplier`, `CoulombIonization_FieldAnalysis_ConditionalFieldIdentity`, `CoulombIonization_FieldAnalysis_CoreFieldRegularity`, `CoulombIonization_FieldAnalysis_CoreHistoryFieldBarrier`, `CoulombIonization_FieldAnalysis_CoreSubmeanSquareBarrier`, `CoulombIonization_FieldAnalysis_FreshFieldTower`, `CoulombIonization_FieldAnalysis_InnerCapStatistic`, `CoulombIonization_FieldAnalysis_InnerFieldCap`, `CoulombIonization_FieldAnalysis_OuterFieldMaximum`, `CoulombIonization_FieldAnalysis_PressureWeak`, `CoulombIonization_FieldAnalysis_QuantumFieldExcessBarrier`, `CoulombIonization_FieldAnalysis_RetainedKineticLower`, `CoulombIonization_FieldAnalysis_RetainedSmear`, `CoulombIonization_FieldAnalysis_RotationTrace`, `CoulombIonization_FieldAnalysis_WeightedAverage`, `CoulombIonization_FormDomain_CoreKinetic`, `CoulombIonization_FormDomain_CoreSliceMassIntegrable`, `CoulombIonization_FormDomain_Form`, `CoulombIonization_FormDomain_FormBody`, `CoulombIonization_FormDomain_FormRawPotential`, `CoulombIonization_FormDomain_Forms`, `CoulombIonization_FormDomain_PhysicalGrid`, `CoulombIonization_FormDomain_ShiftedCoulombIntegrable`, `CoulombIonization_FormDomain_SobolevVector`, `CoulombIonization_FormDomain_SumForm`, `CoulombIonization_Ionization_CoreHistoryFieldFubiniBarrier`, `CoulombIonization_Ionization_MasterJointPosterior`, `CoulombIonization_Localization_ArraySymmetry`, `CoulombIonization_Localization_CoreHistoryAverageBarrier`, `CoulombIonization_Localization_CoreHistoryCoordinatesBarrier`, `CoulombIonization_Localization_CoreHistoryMassBarrier`, `CoulombIonization_Localization_CoreHistoryOutMaximumBarrier`, `CoulombIonization_Localization_CoreObservationEnsembleBarrier`, `CoulombIonization_Localization_CutOuterLaw`, `CoulombIonization_Localization_DyadicObservation`, `CoulombIonization_Localization_FiniteCellObservation`, `CoulombIonization_Localization_FormRawLaw`, `CoulombIonization_Localization_GridPacketRadius`, `CoulombIonization_Localization_Observation`, `CoulombIonization_Localization_OriginalPosteriorKernel`, `CoulombIonization_Localization_PacketCloud`, `CoulombIonization_Localization_PacketDensity`, `CoulombIonization_Localization_PacketDensityRadius`, `CoulombIonization_Localization_PacketInsert`, `CoulombIonization_Localization_PatchCenterObservable`, `CoulombIonization_Localization_RadialPacketBase`, `CoulombIonization_Localization_UnorderedObservations`, `CoulombIonization_RadialBounds_BallAverageKernelBarrier`, `CoulombIonization_RadialBounds_CoreHistoryCountsBarrier`, `CoulombIonization_RadialBounds_CoreHistoryFermionBarrier`, `CoulombIonization_RadialBounds_CoreMultiplierLiftBarrier`, `CoulombIonization_RadialBounds_NormalizedMasterEvent`, `CoulombIonization_RadialBounds_RadialPatchGeometry`, `CoulombIonization_RadialBounds_RootMomentCauchyBarrier`, `CoulombIonization_ThomasFermi_CutMomentBounds`, `CoulombIonization_ThomasFermi_PacketFieldConstant`, `CoulombIonization_ThomasFermi_QuantumSectorNearMinimizer`, `CoulombIonization_Variational_BindingBase`, `CoulombIonization_Variational_BindingNuclearSum`, `CoulombIonization_Variational_BindingWeightContinuous`, `CoulombIonization_Variational_BlockSwap`, `CoulombIonization_Variational_CorePriceExcess`, `CoulombIonization_Variational_CutCoreExcess`, `CoulombIonization_Variational_CutCoreNumber`, `CoulombIonization_Variational_DiffuseSeed`, `CoulombIonization_Variational_InsertionSwap`, `CoulombIonization_Variational_LocalWidthKernel`, `CoulombIonization_Variational_PatchCenterIntegrable`, `CoulombIonization_Variational_RetainedRepulsion`, `CoulombIonization_Variational_RotationCoreKernelIntegrable`, `CoulombIonization_Variational_Slices`, `CoulombIonization_Variational_SmearRepulsion`, `CoulombIonization_Variational_Spatial`, `CoulombIonization_Variational_SpatialProductFactor`, `CoulombIonization_Variational_SpatialRotation`, `CoulombIonization_Variational_SpinJoinEquiv`, `CoulombIonization_Variational_SumPairsHalf`, `CoulombIonization_Variational_TensorLp`, `CoulombIonization_Variational_TruncatedCoulomb`, `CoulombIonization_Variational_Weighted`, `CoulombIonization_Variational_WeightedMass`.
--
--   **Imports.** It imports the published bundle `Def_CoulombIonization`; the bundles `OAIQ071C003` and `OAIQ071C004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ071C008`, `OAIQ071C009`, `OAIQ071C011` and `OAIQ071C012`; the proof of `OAI.CoulombBarrier.selected_barriers_limit_positive`.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C003
import Definitions.Def_OAIQ071C004

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_Slices
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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

lemma FormAdmissible.sobolevFermion {N : ℕ} {ψ : FormVector N} (hψ : FormAdmissible ψ) :
    SobolevFermion ψ := ⟨hψ.1, hψ.2.1, hψ.2.2.1, hψ.2.2.2.1⟩

lemma SobolevFermion.mass_zero_nuclear {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 0) (s : Spins N) (i : Fin N) :
    (∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i‖) = 0 := by
  have hs : (∫ x, ‖ψ.value s x‖ ^ 2) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => integral_nonneg fun x => sq_nonneg _)).mp hm s
      (Finset.mem_univ _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _)
    (hψ.1 s).norm.integrable_sq).mp hs
  calc
    _ = ∫ _x : Configuration N, (0 : ℝ) := integral_congr_ae (hae.mono fun x hx => by simp [hx])
    _ = 0 := integral_zero _ _

theorem SobolevFermion.energy_mul_mass_le {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) {Z : ℝ} (hZ : 0 ≤ Z) :
    energy Z N * formMass ψ ≤ formEnergy Z ψ := by
  rcases (formMass_nonneg ψ).eq_or_lt with hm | hm
  · rw [← hm, mul_zero]
    have hn := hψ.mass_zero_nuclear hm.symm
    simp only [formEnergy, hn, Finset.sum_const_zero, mul_zero, sub_zero]
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _)
    · apply Finset.sum_nonneg; intro s _
      apply Finset.sum_nonneg; intro i _
      apply Finset.sum_nonneg; intro j _
      split_ifs
      · exact integral_nonneg fun _ => div_nonneg (sq_nonneg _) (norm_nonneg _)
      · rfl
  · have hh := energy_le_form hZ (hψ.normalize hm)
    rw [formEnergy_scale, inv_pow, Real.sq_sqrt (le_of_lt hm)] at hh
    have hs := mul_le_mul_of_nonneg_right hh (le_of_lt hm)
    have he : (formMass ψ)⁻¹ * formEnergy Z ψ * formMass ψ = formEnergy Z ψ := by
      field_simp
    rwa [he] at hs


open Set Filter Topology InnerProductSpace Laplacian

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_SobolevVector
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
namespace CoulombAtom

lemma SobolevFermion.sobolevVector {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) : SobolevVector ψ := ⟨hψ.1, hψ.2.1, hψ.2.2.1⟩

lemma SobolevVector.multiply {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (p : SmoothMultiplier (sectorDirections N)) : SobolevVector (multiplyForm p ψ) := by
  refine ⟨fun s => memLp_bounded_mul p.regular.continuous p.bound (hψ.1 s), ?_, ?_⟩
  · intro s i a
    exact (memLp_bounded_mul p.regular.continuous p.bound (hψ.2.1 s i a)).add
      (memLp_bounded_mul (p.derivative_continuous (i,a)) (p.gradient_bound (i,a)) (hψ.1 s))
  · intro s i a
    exact (hψ.2.2 s i a).mul_smooth (hψ.1 s) (hψ.2.1 s i a) p.regular

lemma SobolevVector.nuclear_integrable {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (s : Spins N) (i : Fin N) :
    Integrable (fun x => ‖ψ.value s x‖ ^ 2 / ‖x i‖) :=
  CoulombAtom.nuclear_integrable i (hψ.1 s) (hψ.2.1 s i) (hψ.2.2 s i)

lemma SobolevVector.pair_integrable {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (s : Spins N) (i j : Fin N) (hij : i ≠ j) :
    Integrable (fun x => ‖ψ.value s x‖ ^ 2 / ‖x i - x j‖) :=
  CoulombAtom.pair_integrable i j hij (hψ.1 s) (hψ.2.1 s i) (hψ.2.2 s i)

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SpinJoinEquiv
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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
namespace CoulombAtom

lemma configurationJoin_apply_prod {N M : ℕ} (p : Configuration N × Configuration M) :
    configurationJoin N M p = joinLists p.1 p.2 := by
  rcases p with ⟨x,y⟩
  exact configurationJoin_apply x y

lemma integrable_join {N M : ℕ} {f : Configuration (N+M) → ℝ}
    (hf : Integrable f) : Integrable (fun p : Configuration N × Configuration M =>
      f (joinLists p.1 p.2)) := by
  simpa only [Function.comp_def, configurationJoin_apply_prod] using
    (configurationJoin_preserving N M).integrable_comp_of_integrable hf

lemma integral_join {N M : ℕ} {f : Configuration (N+M) → ℝ}
    (hf : Integrable f) :
    (∫ y : Configuration M, ∫ x : Configuration N, f (joinLists x y)) = ∫ z, f z := by
  have hj := integrable_join (N := N) (M := M) hf
  have he := (configurationJoin_preserving N M).integral_comp
    (configurationJoin N M).toHomeomorph.measurableEmbedding f
  simp only [configurationJoin_apply_prod] at he
  rw [Measure.volume_eq_prod] at hj he
  exact (integral_prod_symm _ hj).symm.trans he

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_ShiftedCoulombIntegrable
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma shifted_nuclear_integrable {N : ℕ} (i : Fin N) (y : Space)
    {f : Configuration N → ℂ} {g : Fin 3 → Configuration N → ℂ}
    (hf : MemLp f 2) (hg : ∀ a, MemLp (g a) 2)
    (hw : ∀ a, IsWeakDerivative (direction i a) f (g a)) :
    Integrable (fun x => ‖f x‖^2/‖x i-y‖) := by
  let a : Configuration N := fun _ => y
  have hp := measurePreserving_add_right (volume : Measure (Configuration N)) a
  have hi := nuclear_integrable i (hf.comp_measurePreserving hp)
    (fun b => (hg b).comp_measurePreserving hp) (fun b => (hw b).translate a)
  have hh := ((measurePreserving_add_right (volume : Measure (Configuration N)) (-a)).integrable_comp
    hi.aestronglyMeasurable).2 hi
  simpa only [Function.comp_def,neg_add_cancel_right,Pi.add_apply,Pi.neg_apply,a,sub_eq_add_neg] using hh

lemma SobolevVector.shifted_nuclear_integrable {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (s : Spins N) (i : Fin N) (y : Space) :
    Integrable (fun x => ‖ψ.value s x‖^2/‖x i-y‖) :=
  CoulombAtom.shifted_nuclear_integrable i y (hψ.1 s) (hψ.2.1 s i) (hψ.2.2 s i)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_FormRawLaw
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma formRawDensity_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ) :
    Integrable (formRawDensity ψ) :=
  integrable_finsetSum _ (fun s _ => (hψ.1 s).norm.integrable_sq)

lemma formRawLaw_integral {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (g : Configuration N → ℝ) :
    (∫ x, g x ∂formRawLaw ψ) = ∫ x, formRawDensity ψ x*g x := by
  rw [formRawLaw,integral_withDensity_eq_integral_toReal_smul₀
    (formRawDensity_integrable hψ).aemeasurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (formRawDensity_nonneg ψ _),smul_eq_mul]

lemma formRawLaw_integral_eq_spin_sum {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {g : Configuration N → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) :
    (∫ x, g x ∂formRawLaw ψ) = ∑ s : Spins N, ∫ x, g x*‖ψ.value s x‖^2 := by
  rw [formRawLaw_integral hψ]
  have hi (s : Spins N) : Integrable (fun x => g x*‖ψ.value s x‖^2) :=
    ((hψ.1 s).norm.integrable_sq).bdd_mul hg.aestronglyMeasurable (ae_of_all _ hB)
  simp only [formRawDensity,Finset.sum_mul]
  simp_rw [mul_comm (‖ψ.value _ _‖^2)]
  exact integral_finsetSum _ (fun s _ => hi s)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_SumForm
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
namespace CoulombAtom

lemma SobolevVector.sum {ι : Type*} [Fintype ι] {N : ℕ} {ψ : ι → FormVector N}
    (hψ : ∀ k, SobolevVector (ψ k)) : SobolevVector (sumForm ψ) := by
  classical
  refine ⟨fun s => memLp_finsetSum _ (fun k _ => (hψ k).1 s),
    fun s i a => memLp_finsetSum _ (fun k _ => (hψ k).2.1 s i a), ?_⟩
  intro s i a φ hφ hcφ
  change (∫ x, (∑ k, (ψ k).value s x) * Complex.ofReal (lineDeriv ℝ φ x (direction i a))) =
    -(∫ x, (∑ k, (ψ k).gradient s i a x) * (φ x : ℂ))
  simp only [Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (fun k _ => show Integrable (fun x =>
      (ψ k).value s x * Complex.ofReal (lineDeriv ℝ φ x (direction i a))) from
      ((hψ k).1 s).integrable_mul (test_deriv_memLp hφ hcφ (direction i a))),
    integral_finsetSum Finset.univ (fun k _ => show Integrable (fun x =>
      (ψ k).gradient s i a x * (φ x : ℂ)) from
      ((hψ k).2.1 s i a).integrable_mul (test_memLp hφ hcφ))]
  simp only [(hψ _).2.2 s i a φ hφ hcφ, Finset.sum_neg_distrib]

lemma SobolevVector.scale {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ) (c : ℝ) :
    SobolevVector (scaleForm c ψ) := by
  refine ⟨fun s => (hψ.1 s).const_mul _, fun s i a => (hψ.2.1 s i a).const_mul _, ?_⟩
  intro s i a φ hφ hcφ
  change (∫ x, ((c : ℂ) * ψ.value s x) * Complex.ofReal (lineDeriv ℝ φ x (direction i a))) =
    -(∫ x, ((c : ℂ) * ψ.gradient s i a x) * (φ x : ℂ))
  simp only [mul_assoc, integral_const_mul, hψ.2.2 s i a φ hφ hcφ, mul_neg]

lemma formMass_sum_disjoint {ι : Type*} [Fintype ι] {N : ℕ} {ψ : ι → FormVector N}
    (hψ : ∀ k, SobolevVector (ψ k)) (hd : FormsDisjoint ψ) :
    formMass (sumForm ψ) = ∑ k, formMass (ψ k) := by
  unfold formMass
  have hh (s : Spins N) : (∫ x, ‖(sumForm ψ).value s x‖^2) =
      ∑ k, ∫ x, ‖(ψ k).value s x‖^2 := by
    simp only [sumForm, norm_sum_sq_disjoint _ (fun k l hkl => hd.1 k l hkl s _)]
    exact integral_finsetSum _ (fun k _ => ((hψ k).1 s).norm.integrable_sq)
  simp_rw [hh]
  exact Finset.sum_comm

lemma formEnergy_sum_disjoint {ι : Type*} [Fintype ι] {N : ℕ} {ψ : ι → FormVector N}
    (hψ : ∀ k, SobolevVector (ψ k)) (hd : FormsDisjoint ψ) (Z : ℝ) :
    formEnergy Z (sumForm ψ) = ∑ k, formEnergy Z (ψ k) := by
  classical
  have hk (s : Spins N) (i : Fin N) (a : Fin 3) :
      (∫ x, ‖(sumForm ψ).gradient s i a x‖^2) = ∑ k, ∫ x, ‖(ψ k).gradient s i a x‖^2 := by
    simp only [sumForm, norm_sum_sq_disjoint _ (fun k l hkl => hd.2 k l hkl s i a _)]
    exact integral_finsetSum _ (fun k _ => ((hψ k).2.1 s i a).norm.integrable_sq)
  have hn (s : Spins N) (i : Fin N) :
      (∫ x, ‖(sumForm ψ).value s x‖^2 / ‖x i‖) =
      ∑ k, ∫ x, ‖(ψ k).value s x‖^2 / ‖x i‖ := by
    simp only [sumForm, norm_sum_sq_disjoint _ (fun k l hkl => hd.1 k l hkl s _), Finset.sum_div]
    exact integral_finsetSum _ (fun k _ => (hψ k).nuclear_integrable s i)
  have hp (s : Spins N) (i j : Fin N) :
      (if i < j then ∫ x, ‖(sumForm ψ).value s x‖^2 / ‖x i-x j‖ else 0) =
      ∑ k, if i < j then ∫ x, ‖(ψ k).value s x‖^2 / ‖x i-x j‖ else 0 := by
    by_cases hij : i < j
    · simp only [ite_eq_left hij, sumForm,
        norm_sum_sq_disjoint _ (fun k l hkl => hd.1 k l hkl s _), Finset.sum_div]
      exact integral_finsetSum _ (fun k _ => (hψ k).pair_integrable s i j hij.ne)
    · simp only [ite_eq_right hij, Finset.sum_const_zero]
  unfold formEnergy
  simp_rw [hk,hn,hp]
  rw [show (∑ s, ∑ i, ∑ a, ∑ k, ∫ x, ‖(ψ k).gradient s i a x‖^2) =
    ∑ k, ∑ s, ∑ i, ∑ a, ∫ x, ‖(ψ k).gradient s i a x‖^2 by
      simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun a k =>
        ∫ x, ‖(ψ k).gradient _ _ a x‖^2)]
      simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun i k =>
        ∑ a, ∫ x, ‖(ψ k).gradient _ i a x‖^2)]
      exact Finset.sum_comm,
    show (∑ s, ∑ i, ∑ k, ∫ x, ‖(ψ k).value s x‖^2 / ‖x i‖) =
    ∑ k, ∑ s, ∑ i, ∫ x, ‖(ψ k).value s x‖^2 / ‖x i‖ by
      simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun i k =>
        ∫ x, ‖(ψ k).value _ x‖^2 / ‖x i‖)]
      exact Finset.sum_comm,
    show (∑ s, ∑ i, ∑ j, ∑ k, if i < j then ∫ x, ‖(ψ k).value s x‖^2 / ‖x i-x j‖ else 0) =
    ∑ k, ∑ s, ∑ i, ∑ j, if i < j then ∫ x, ‖(ψ k).value s x‖^2 / ‖x i-x j‖ else 0 by
      simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun j k =>
        if _ < j then ∫ x, ‖(ψ k).value _ x‖^2 / ‖x _-x j‖ else 0)]
      simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun i k =>
        ∑ j, if i < j then ∫ x, ‖(ψ k).value _ x‖^2 / ‖x i-x j‖ else 0)]
      exact Finset.sum_comm]
  simp only [Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]

end CoulombAtom

open MeasureTheory Filter
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_Forms
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma finite_partition_value (ψ : FormVector N) (s : Spins N) (x : Configuration N) :
    ∑ j, ‖(multiplyForm (p j) ψ).value s x‖ ^ 2 = ‖ψ.value s x‖ ^ 2 :=
  finite_complex_partition (fun j => (p j).value x) (hp x) _

lemma finite_partition_mass {ψ : FormVector N} (hψ : SobolevVector ψ) :
    ∑ j, formMass (multiplyForm (p j) ψ) = formMass ψ := by
  unfold formMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [← integral_finsetSum _ (fun j _ => ((hψ.multiply (p j)).1 s).norm.integrable_sq)]
  exact integral_congr_ae (Eventually.of_forall (finite_partition_value p hp ψ s))

end

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_QuantumSectorNearMinimizer
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
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
namespace CoulombAtom

theorem SobolevFermion.priced_lower_bound {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    priceEnergy (energy Z) lam * formMass ψ ≤
      formEnergy Z ψ + lam * N * formMass ψ := by
  have hp := mul_le_mul_of_nonneg_right (quantum_price_le_sector hZ hlam N)
    (formMass_nonneg ψ)
  have he := hψ.energy_mul_mass_le hZ
  nlinarith

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_Spatial
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

theorem spatial_cut_mass {ψ : FormVector N} (hψ : SobolevVector ψ) :
    ∑ b : Fin N → Fin 2, formMass (multiplyForm (spatialProduct p hp b) ψ) = formMass ψ :=
  finite_partition_mass (spatialProduct p hp) (spatial_square_partition p hp) hψ

end

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

lemma SobolevFermion.coreAntisymmetric {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevFermion ψ) : CoreAntisymmetric ψ := by
  intro π s
  simpa only [corePerm_sign] using hψ.2.2.2 (corePerm M π) s

lemma coreCutLabels_invariant {N M : ℕ} (π : Equiv.Perm (Fin N)) :
    coreCutLabels N M ∘ corePerm M π = coreCutLabels N M := by
  unfold coreCutLabels
  rw [joinLists_corePerm]
  rfl

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SumPairsHalf
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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


lemma SobolevVector.reindex {M N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (e : Fin M ≃ Fin N) : SobolevVector (reindexForm e ψ) := by
  refine ⟨fun s => ?_, fun s i a => ?_, fun s i a => ?_⟩
  · simpa only [Function.comp_def, configurationReindex_apply, reindexForm] using
      (hψ.1 (s ∘ e.symm)).comp_measurePreserving (configurationReindex_preserving e)
  · simpa only [Function.comp_def, configurationReindex_apply, reindexForm] using
      (hψ.2.1 (s ∘ e.symm) (e i) a).comp_measurePreserving (configurationReindex_preserving e)
  · simpa only [Function.comp_def, configurationReindex_apply, reindexForm] using
      (hψ.2.2 (s ∘ e.symm) (e i) a).pullback (configurationReindex e)
        (configurationReindex_preserving e) (configurationReindex_direction e i a)

lemma SobolevFermion.reindex {M N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (e : Fin M ≃ Fin N) : SobolevFermion (reindexForm e ψ) := by
  have hr := hψ.sobolevVector.reindex e
  refine ⟨hr.1,hr.2.1,hr.2.2,?_⟩
  intro π s
  have hh := (configurationReindex_preserving e).quasiMeasurePreserving.ae
    (hψ.2.2.2 (e.permCongr π) (s ∘ e.symm))
  filter_upwards [hh] with x hx
  simpa only [configurationReindex_apply, Equiv.Perm.sign_permCongr,
    Function.comp_def, Equiv.permCongr_apply, Equiv.symm_apply_apply, reindexForm] using hx


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_TensorLp
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F]
  [(volume : Measure F).IsAddHaarMeasure]

lemma IsWeakDerivative.tensor_right {v : F} {g dg : F → ℂ} {f : E → ℂ}
    (hwd : IsWeakDerivative v g dg) (hg : MemLp g 2) (hdg : MemLp dg 2)
    (hf : MemLp f 2) :
    IsWeakDerivative (0,v) (fun p : E × F => f p.1*g p.2)
      (fun p => f p.1*dg p.2) := by
  have hh := (hwd.tensor_left hg hdg hf).pullback
    (ContinuousLinearEquiv.prodComm ℝ E F)
      (by change MeasurePreserving Prod.swap (volume.prod volume) (volume.prod volume)
          exact Measure.measurePreserving_swap) (w := (0,v)) rfl
  change IsWeakDerivative (0,v) (fun p : E × F => g p.2*f p.1)
    (fun p => dg p.2*f p.1) at hh
  simpa only [mul_comm] using hh

end

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators


lemma configurationJoin_symm_apply {N M : ℕ} (x : Configuration (N+M)) :
    (configurationJoin N M).symm x = (leftList x,rightList x) := by
  apply (configurationJoin N M).injective
  rw [ContinuousLinearEquiv.apply_symm_apply,configurationJoin_apply,join_list_parts]

lemma configurationJoin_direction_right {N M : ℕ} (i : Fin M) (a : Fin 3) :
    configurationJoin N M (0,direction i a) = direction (finSumFinEquiv (Sum.inr i)) a := by
  rw [configurationJoin_apply]
  funext j
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
  cases j with
  | inl j =>
    rw [joinLists_left]
    have hn : finSumFinEquiv (Sum.inl j) ≠ finSumFinEquiv (Sum.inr i) :=
      fun h => Sum.inl_ne_inr (finSumFinEquiv.injective h)
    simp only [direction, Pi.single_apply, ite_eq_right hn, Pi.zero_apply]
  | inr j => rw [joinLists_right]; simp [direction, Pi.single_apply]

lemma SobolevVector.tensor {N M : ℕ} {ψ : FormVector N} {φ : FormVector M}
    (hψ : SobolevVector ψ) (hφ : SobolevVector φ) : SobolevVector (tensorForm ψ φ) := by
  refine ⟨fun s => ?_, fun s i a => ?_, fun s i a => ?_⟩
  · simpa only [Function.comp_def,configurationJoin_symm_apply,tensorForm] using
      (memLp_tensor (hψ.1 (leftList s)) (hφ.1 (rightList s))).comp_measurePreserving
        (configurationJoin_symm_preserving N M)
  · obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
    cases i with
    | inl i =>
      simpa only [Function.comp_def,configurationJoin_symm_apply,tensorForm,
        Equiv.symm_apply_apply,Sum.elim_inl] using
        (memLp_tensor
          (hψ.2.1 (leftList s) i a) (hφ.1 (rightList s))).comp_measurePreserving
          (configurationJoin_symm_preserving N M)
    | inr i =>
      simpa only [Function.comp_def,configurationJoin_symm_apply,tensorForm,
        Equiv.symm_apply_apply,Sum.elim_inr] using
        (memLp_tensor
          (hψ.1 (leftList s)) (hφ.2.1 (rightList s) i a)).comp_measurePreserving
          (configurationJoin_symm_preserving N M)
  · obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
    cases i with
    | inl i =>
      have hv : (configurationJoin N M).symm (direction (finSumFinEquiv (Sum.inl i)) a) =
          (direction i a,0) := by rw [← configurationJoin_direction,ContinuousLinearEquiv.symm_apply_apply]
      simpa only [Function.comp_def,configurationJoin_symm_apply,tensorForm,
        Equiv.symm_apply_apply,Sum.elim_inl] using
        ((hψ.2.2 (leftList s) i a).tensor_left (hψ.1 _) (hψ.2.1 _ i a) (hφ.1 _)).pullback
          (configurationJoin N M).symm (configurationJoin_symm_preserving N M) hv
    | inr i =>
      have hv : (configurationJoin N M).symm (direction (finSumFinEquiv (Sum.inr i)) a) =
          (0,direction i a) := by rw [← configurationJoin_direction_right,ContinuousLinearEquiv.symm_apply_apply]
      simpa only [Function.comp_def,configurationJoin_symm_apply,tensorForm,
        Equiv.symm_apply_apply,Sum.elim_inr] using
        ((hφ.2.2 (rightList s) i a).tensor_right (hφ.1 _) (hφ.2.1 _ i a) (hψ.1 _)).pullback
          (configurationJoin N M).symm (configurationJoin_symm_preserving N M) hv

lemma formMass_tensor {N M : ℕ} (ψ : FormVector N) (φ : FormVector M) :
    formMass (tensorForm ψ φ) = formMass ψ*formMass φ := by
  unfold formMass
  rw [← sum_spin_join]
  have hi (s : Spins N) (t : Spins M) :
      (∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2) =
        (∫ x, ‖ψ.value s x‖^2)*(∫ y, ‖φ.value t y‖^2) := by
    rw [← (configurationJoin_preserving N M).integral_comp
      (configurationJoin N M).toHomeomorph.measurableEmbedding
      (fun z => ‖(tensorForm ψ φ).value (joinLists s t) z‖^2)]
    simp only [configurationJoin_apply_prod,tensorForm_value_join]
    exact integral_tensor_sq _ _
  simp_rw [hi,← Finset.sum_mul,← Finset.mul_sum]


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_InsertionSwap
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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


lemma tensor_coreAntisymmetric {N M : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (φ : FormVector M) : CoreAntisymmetric (tensorForm ψ φ) := by
  intro π s
  have hp : ∀ᵐ z : Configuration N × Configuration M,
      ψ.value (leftList s ∘ π) (z.1 ∘ π) =
        (((Equiv.Perm.sign π : ℤ) : ℂ) * ψ.value (leftList s) z.1) :=
    Measure.quasiMeasurePreserving_fst.ae (hψ.2.2.2 π (leftList s))
  have hh := (configurationJoin_symm_preserving N M).quasiMeasurePreserving.ae hp
  filter_upwards [hh] with x hx
  simp only [configurationJoin_symm_apply] at hx
  have hp (z : Fin (N+M) → Space) :
      leftList (z ∘ corePerm M π) = leftList z ∘ π ∧
      rightList (z ∘ corePerm M π) = rightList z := by
    have he := joinLists_corePerm (leftList z) (rightList z) π
    rw [join_list_parts] at he
    constructor
    · rw [he,leftList_join]
    · rw [he,rightList_join]
  have hs : leftList (s ∘ corePerm M π) = leftList s ∘ π ∧
      rightList (s ∘ corePerm M π) = rightList s := by
    have he := joinLists_corePerm (leftList s) (rightList s) π
    rw [join_list_parts] at he
    constructor
    · rw [he,leftList_join]
    · rw [he,rightList_join]
  change ψ.value _ _ * φ.value _ _ = _ * (ψ.value _ _ * φ.value _ _)
  rw [hs.1,hs.2,(hp x).1,(hp x).2,hx,mul_assoc]

lemma SobolevVector.insertionTerm {N : ℕ} {T : FormVector (N+1)} (hT : SobolevVector T)
    (i : Fin (N+1)) : SobolevVector (insertionTerm T i) :=
  (hT.reindex (insertionSwap i)).scale _

lemma wedgeForm_fermion {N : ℕ} {T : FormVector (N+1)} (hT : SobolevVector T)
    (hTa : CoreAntisymmetric (N := N) (M := 1) T) : SobolevFermion (wedgeForm T) := by
  have hw := SobolevVector.sum (fun i => hT.insertionTerm i)
  refine ⟨hw.1,hw.2.1,hw.2.2,?_⟩
  intro π s
  have hh (i : Fin (N+1)) : ∀ᵐ x,
      (insertionTerm T i).value (s ∘ π) (x ∘ π) =
      (((Equiv.Perm.sign π : ℤ) : ℂ)) * (insertionTerm T (π i)).value s x := by
    obtain ⟨ρ,hρ⟩ := insertion_coset π i
    have hp := (permuteConfiguration_preserving (insertionSwap (π i))).quasiMeasurePreserving.ae
      (hTa ρ (s ∘ insertionSwap (π i)))
    filter_upwards [hp] with x hx
    simp only [permuteConfiguration_apply] at hx
    have hv : ((s ∘ π) ∘ insertionSwap i) = (s ∘ insertionSwap (π i)) ∘ corePerm 1 ρ := by
      change s ∘ (π * insertionSwap i) = s ∘ (insertionSwap (π i) * corePerm 1 ρ)
      rw [hρ]
    have hvx : ((x ∘ π) ∘ insertionSwap i) = (x ∘ insertionSwap (π i)) ∘ corePerm 1 ρ := by
      change x ∘ (π * insertionSwap i) = x ∘ (insertionSwap (π i) * corePerm 1 ρ)
      rw [hρ]
    have hsg : (((Equiv.Perm.sign π : ℤ) : ℂ)) *
        (((Equiv.Perm.sign (insertionSwap i) : ℤ) : ℂ)) =
        (((Equiv.Perm.sign (insertionSwap (π i)) : ℤ) : ℂ)) *
        (((Equiv.Perm.sign ρ : ℤ) : ℂ)) := by
      have ht := congrArg (fun σ => (((Equiv.Perm.sign σ : ℤ) : ℂ))) hρ
      simpa only [Equiv.Perm.sign_mul,corePerm_sign,Units.val_mul,Int.cast_mul] using ht
    have hsg' : (((Equiv.Perm.sign (insertionSwap i) : ℤ) : ℂ)) *
        (((Equiv.Perm.sign ρ : ℤ) : ℂ)) =
        (((Equiv.Perm.sign π : ℤ) : ℂ)) *
        (((Equiv.Perm.sign (insertionSwap (π i)) : ℤ) : ℂ)) := by
      have hs := complex_sign_sq (insertionSwap (π i))
      have hq := complex_sign_sq (insertionSwap i)
      linear_combination -(((Equiv.Perm.sign (insertionSwap (π i)) : ℤ) : ℂ)) *
        (((Equiv.Perm.sign (insertionSwap i) : ℤ) : ℂ)) * hsg +
        (((Equiv.Perm.sign π : ℤ) : ℂ)) *
        (((Equiv.Perm.sign (insertionSwap (π i)) : ℤ) : ℂ)) * hq -
        (((Equiv.Perm.sign ρ : ℤ) : ℂ)) *
        (((Equiv.Perm.sign (insertionSwap i) : ℤ) : ℂ)) * hs
    simp only [insertionTerm_value,hv,hvx,hx,← mul_assoc,hsg']
  filter_upwards [ae_all_iff.mpr hh] with x hx
  change (∑ i, (insertionTerm T i).value (s ∘ π) (x ∘ π)) = _ * ∑ i, (insertionTerm T i).value s x
  simp_rw [hx,← Finset.mul_sum]
  rw [Equiv.sum_comp π (fun i => (insertionTerm T i).value s x)]

lemma formMass_insertionTerm {N : ℕ} (T : FormVector (N+1)) (i : Fin (N+1)) :
    formMass (insertionTerm T i) = formMass T := by
  rw [insertionTerm,formMass_scale,formMass_reindex,real_sign_sq,one_mul]


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_Form
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma formMass_wedge {N : ℕ} {T : FormVector (N+1)} (hT : SobolevVector T)
    (hd : FormsDisjoint (insertionTerm T)) :
    formMass (wedgeForm T) = (N+1 : ℝ) * formMass T := by
  rw [wedgeForm,formMass_sum_disjoint (fun i => hT.insertionTerm i) hd]
  simp only [formMass_insertionTerm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]

lemma formEnergy_wedge {N : ℕ} {T : FormVector (N+1)} (hT : SobolevVector T)
    (hd : FormsDisjoint (insertionTerm T)) (Z : ℝ) :
    formEnergy Z (wedgeForm T) = (N+1 : ℝ) * formEnergy Z T := by
  rw [wedgeForm,formEnergy_sum_disjoint (fun i => hT.insertionTerm i) hd]
  simp only [formEnergy_insertionTerm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]


open MeasureTheory Filter
open scoped BigOperators


lemma formEnergy_parts {N : ℕ} (ψ : FormVector N) (Z : ℝ) :
    formEnergy Z ψ = formKinetic ψ - Z * formNuclear ψ + formRepulsion ψ := rfl

lemma formKinetic_nonneg {N : ℕ} (ψ : FormVector N) : 0 ≤ formKinetic ψ := by
  unfold formKinetic
  positivity

lemma integral_product_join {N M : ℕ} (f : Configuration N → ℝ) (g : Configuration M → ℝ) :
    (∫ z : Configuration (N+M), f (leftList z)*g (rightList z)) = (∫ x, f x)*(∫ y, g y) := by
  rw [← (configurationJoin_preserving N M).integral_comp
    (configurationJoin N M).toHomeomorph.measurableEmbedding]
  simp only [configurationJoin_apply_prod,leftList_join,rightList_join]
  rw [Measure.volume_eq_prod]
  exact integral_prod_mul f g

lemma tensor_kinetic_left {N M : ℕ} (ψ : FormVector N) (φ : FormVector M)
    (s : Spins N) (t : Spins M) (i : Fin N) (a : Fin 3) :
    (∫ z, ‖(tensorForm ψ φ).gradient (joinLists s t) (finSumFinEquiv (Sum.inl i)) a z‖^2) =
      (∫ x, ‖ψ.gradient s i a x‖^2)*(∫ y, ‖φ.value t y‖^2) := by
  simp only [tensorForm,leftList_join,rightList_join,Equiv.symm_apply_apply,Sum.elim_inl,norm_mul,mul_pow]
  exact integral_product_join (N := N) (M := M) (fun x => ‖ψ.gradient s i a x‖^2) (fun y => ‖φ.value t y‖^2)

lemma tensor_kinetic_right {N M : ℕ} (ψ : FormVector N) (φ : FormVector M)
    (s : Spins N) (t : Spins M) (i : Fin M) (a : Fin 3) :
    (∫ z, ‖(tensorForm ψ φ).gradient (joinLists s t) (finSumFinEquiv (Sum.inr i)) a z‖^2) =
      (∫ x, ‖ψ.value s x‖^2)*(∫ y, ‖φ.gradient t i a y‖^2) := by
  simp only [tensorForm,leftList_join,rightList_join,Equiv.symm_apply_apply,Sum.elim_inr,norm_mul,mul_pow]
  exact integral_product_join (N := N) (M := M) (fun x => ‖ψ.value s x‖^2) (fun y => ‖φ.gradient t i a y‖^2)

lemma formKinetic_tensor {N M : ℕ} (ψ : FormVector N) (φ : FormVector M) :
    formKinetic (tensorForm ψ φ) = formKinetic ψ * formMass φ + formMass ψ * formKinetic φ := by
  unfold formKinetic formMass
  rw [← sum_spin_join]
  have hk (s : Spins N) (t : Spins M) :
      (∑ i, ∑ a, ∫ z, ‖(tensorForm ψ φ).gradient (joinLists s t) i a z‖^2) =
      (∑ i, ∑ a, ∫ x, ‖ψ.gradient s i a x‖^2)*(∫ y, ‖φ.value t y‖^2) +
      (∫ x, ‖ψ.value s x‖^2)*(∑ i, ∑ a, ∫ y, ‖φ.gradient t i a y‖^2) := by
    rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
    simp only [tensor_kinetic_left,tensor_kinetic_right,Finset.sum_mul,Finset.mul_sum]
  simp_rw [hk,Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum]
  ring

lemma tensor_nuclear_left {N M : ℕ} (ψ : FormVector N) (φ : FormVector M)
    (s : Spins N) (t : Spins M) (i : Fin N) :
    (∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 / ‖z (finSumFinEquiv (Sum.inl i))‖) =
      (∫ x, ‖ψ.value s x‖^2 / ‖x i‖)*(∫ y, ‖φ.value t y‖^2) := by
  change (∫ z, ‖ψ.value (leftList (joinLists s t)) (leftList z) *
    φ.value (rightList (joinLists s t)) (rightList z)‖^2 / ‖leftList z i‖) = _
  simp only [leftList_join,rightList_join,norm_mul,mul_pow]
  simp_rw [mul_div_right_comm]
  exact integral_product_join (N := N) (M := M) (fun x => ‖ψ.value s x‖^2 / ‖x i‖) (fun y => ‖φ.value t y‖^2)

lemma tensor_nuclear_right {N M : ℕ} (ψ : FormVector N) (φ : FormVector M)
    (s : Spins N) (t : Spins M) (i : Fin M) :
    (∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 / ‖z (finSumFinEquiv (Sum.inr i))‖) =
      (∫ x, ‖ψ.value s x‖^2)*(∫ y, ‖φ.value t y‖^2 / ‖y i‖) := by
  change (∫ z, ‖ψ.value (leftList (joinLists s t)) (leftList z) *
    φ.value (rightList (joinLists s t)) (rightList z)‖^2 / ‖rightList z i‖) = _
  simp only [leftList_join,rightList_join,norm_mul,mul_pow,mul_div_assoc]
  exact integral_product_join (N := N) (M := M) (fun x => ‖ψ.value s x‖^2) (fun y => ‖φ.value t y‖^2 / ‖y i‖)

lemma formNuclear_tensor {N M : ℕ} (ψ : FormVector N) (φ : FormVector M) :
    formNuclear (tensorForm ψ φ) = formNuclear ψ * formMass φ + formMass ψ * formNuclear φ := by
  unfold formNuclear formMass
  rw [← sum_spin_join]
  have hk (s : Spins N) (t : Spins M) :
      (∑ i, ∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 / ‖z i‖) =
      (∑ i, ∫ x, ‖ψ.value s x‖^2 / ‖x i‖)*(∫ y, ‖φ.value t y‖^2) +
      (∫ x, ‖ψ.value s x‖^2)*(∑ i, ∫ y, ‖φ.value t y‖^2 / ‖y i‖) := by
    rw [← Equiv.sum_comp finSumFinEquiv,Fintype.sum_sum_type]
    simp only [tensor_nuclear_left,tensor_nuclear_right,Finset.sum_mul,Finset.mul_sum]
  simp_rw [hk,Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum]

lemma tensor_pair_left {N M : ℕ} (ψ : FormVector N) (φ : FormVector M)
    (s : Spins N) (t : Spins M) (i j : Fin N) :
    (∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 /
      ‖z (finSumFinEquiv (Sum.inl i))-z (finSumFinEquiv (Sum.inl j))‖) =
      (∫ x, ‖ψ.value s x‖^2 / ‖x i-x j‖)*(∫ y, ‖φ.value t y‖^2) := by
  change (∫ z, ‖ψ.value (leftList (joinLists s t)) (leftList z) *
    φ.value (rightList (joinLists s t)) (rightList z)‖^2 / ‖leftList z i-leftList z j‖) = _
  simp only [leftList_join,rightList_join,norm_mul,mul_pow]
  simp_rw [mul_div_right_comm]
  exact integral_product_join (N := N) (M := M) (fun x => ‖ψ.value s x‖^2 / ‖x i-x j‖) (fun y => ‖φ.value t y‖^2)

lemma formRepulsion_tensor_one {N : ℕ} (ψ : FormVector N) (φ : FormVector 1) :
    formRepulsion (tensorForm ψ φ) = formRepulsion ψ * formMass φ + tensorCross ψ φ := by
  classical
  unfold formRepulsion tensorCross formMass
  rw [← sum_spin_join]
  have hk (s : Spins N) (t : Spins 1) :
      (∑ i : Fin (N+1), ∑ j : Fin (N+1), if i < j then
        ∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 / ‖z i-z j‖ else 0) =
      (∑ i : Fin N, ∑ j : Fin N, if i < j then ∫ x, ‖ψ.value s x‖^2 / ‖x i-x j‖ else 0)*
        (∫ y, ‖φ.value t y‖^2) +
      ∑ i : Fin N, ∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 /
        ‖z i.castSucc-z (Fin.last N)‖ := by
    rw [Fin.sum_univ_castSucc]
    have he (i : Fin N) : (∑ j : Fin (N+1), if i.castSucc < j then
        ∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 / ‖z i.castSucc-z j‖ else 0) =
        (∑ j : Fin N, if i < j then ∫ x, ‖ψ.value s x‖^2 / ‖x i-x j‖ else 0)*
          (∫ y, ‖φ.value t y‖^2) +
        ∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 / ‖z i.castSucc-z (Fin.last N)‖ := by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.castSucc_lt_castSucc_iff,Fin.castSucc_lt_last,ite_true]
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _
      split_ifs
      · exact tensor_pair_left ψ φ s t i j
      · simp only [zero_mul]
    simp_rw [he,Finset.sum_add_distrib,← Finset.sum_mul]
    have he0 : (∑ j : Fin (N+1), if Fin.last N < j then
        ∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 / ‖z (Fin.last N)-z j‖ else 0) = 0 := by
      apply Finset.sum_eq_zero; intro j _
      exact ite_eq_right (not_lt_of_ge (Fin.le_last j))
    rw [he0,add_zero]
  simp_rw [hk,Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum]
  congr 1
  exact Finset.sum_comm

lemma formEnergy_tensor_one {N : ℕ} (ψ : FormVector N) (φ : FormVector 1) (Z : ℝ) :
    formEnergy Z (tensorForm ψ φ) = formEnergy Z ψ * formMass φ +
      formMass ψ * (formKinetic φ - Z * formNuclear φ) + tensorCross ψ φ := by
  rw [formEnergy_parts,formKinetic_tensor,formNuclear_tensor,formRepulsion_tensor_one,formEnergy_parts]
  ring


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CoreKinetic
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma integral_core_kinetic {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) :
    (∑ t : Spins M, ∫ y, formKinetic (coreSlice ψ t y)) = coreKinetic ψ := by
  have hi (s : Spins N) (t : Spins M) (i : Fin N) (a : Fin 3) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖(coreSlice ψ t y).gradient s i a x‖^2) :=
    (integrable_join (N := N) (M := M)
      (hψ.2.1 (joinLists s t) (finSumFinEquiv (Sum.inl i)) a).norm.integrable_sq).integral_prod_right
  unfold formKinetic coreKinetic
  simp_rw [integral_const_mul, integral_finsetSum _ (fun s _ => integrable_finsetSum _
    (fun i _ => integrable_finsetSum _ (fun a _ => hi s _ i a))),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun a _ => hi _ _ i a)),
    integral_finsetSum _ (fun a _ => hi _ _ _ a)]
  simp only [coreSlice]
  simp_rw [integral_join (hψ.2.1 _ _ _).norm.integrable_sq]
  rw [← Finset.mul_sum]
  congr 1
  exact sum_spin_join (N := N) (M := M) (fun u => ∑ i : Fin N, ∑ a : Fin 3,
    ∫ z, ‖ψ.gradient u (finSumFinEquiv (Sum.inl i)) a z‖^2)

lemma integral_core_repulsion {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) :
    (∑ t : Spins M, ∫ y, formRepulsion (coreSlice ψ t y)) = coreRepulsion ψ := by
  have hi (s : Spins N) (t : Spins M) (i j : Fin N) (hij : i < j) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖(coreSlice ψ t y).value s x‖^2 / ‖x i-x j‖) := by
    have hne : (finSumFinEquiv (Sum.inl i) : Fin (N+M)) ≠ finSumFinEquiv (Sum.inl j) :=
      fun hh => (ne_of_lt hij) (Sum.inl.inj (finSumFinEquiv.injective hh))
    have hh := (integrable_join (N := N) (M := M)
      (pair_integrable _ _ hne (hψ.1 (joinLists s t))
        (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))).integral_prod_right
    simpa only [coreSlice, joinLists_left] using hh
  have hit (s : Spins N) (t : Spins M) (i j : Fin N) :
      Integrable (fun y => if i < j then ∫ x,
        ‖(coreSlice ψ t y).value s x‖^2 / ‖x i-x j‖ else 0) := by
    split_ifs with hij
    · exact hi s t i j hij
    · exact integrable_zero _ _ _
  unfold formRepulsion coreRepulsion
  simp_rw [integral_finsetSum _ (fun s _ => integrable_finsetSum _
      (fun i _ => integrable_finsetSum _ (fun j _ => hit s _ i j))),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hit _ _ i j)),
    integral_finsetSum _ (fun j _ => hit _ _ _ j)]
  have he (s : Spins N) (t : Spins M) (i j : Fin N) :
      (∫ y : Configuration M, if i < j then ∫ x,
        ‖(coreSlice ψ t y).value s x‖^2 / ‖x i-x j‖ else 0) =
      if i < j then ∫ z, ‖ψ.value (joinLists s t) z‖^2 /
        ‖z (finSumFinEquiv (Sum.inl i))-z (finSumFinEquiv (Sum.inl j))‖ else 0 := by
    split_ifs with hij
    · have hne : (finSumFinEquiv (Sum.inl i) : Fin (N+M)) ≠ finSumFinEquiv (Sum.inl j) :=
        fun hh => (ne_of_lt hij) (Sum.inl.inj (finSumFinEquiv.injective hh))
      simpa only [coreSlice, joinLists_left] using
        integral_join (N := N) (M := M)
          (pair_integrable _ _ hne (hψ.1 (joinLists s t))
            (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))
    · exact integral_zero _ _
  simp_rw [he]
  exact sum_spin_join (N := N) (M := M) (fun u => ∑ i : Fin N, ∑ j : Fin N,
    if i < j then ∫ z, ‖ψ.value u z‖^2 /
        ‖z (finSumFinEquiv (Sum.inl i))-z (finSumFinEquiv (Sum.inl j))‖ else 0)

lemma coreSlice_parts_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) :
    Integrable (fun y => formKinetic (coreSlice ψ t y)) ∧
    Integrable (fun y => formNuclear (coreSlice ψ t y)) ∧
    Integrable (fun y => formRepulsion (coreSlice ψ t y)) := by
  have hk (s : Spins N) (i : Fin N) (a : Fin 3) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖(coreSlice ψ t y).gradient s i a x‖^2) :=
    (integrable_join (N := N) (M := M)
      (hψ.2.1 (joinLists s t) (finSumFinEquiv (Sum.inl i)) a).norm.integrable_sq).integral_prod_right
  have hn (s : Spins N) (i : Fin N) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖(coreSlice ψ t y).value s x‖^2 / ‖x i‖) := by
    simpa only [coreSlice, joinLists_left] using (integrable_join (N := N) (M := M)
      (nuclear_integrable (finSumFinEquiv (Sum.inl i)) (hψ.1 (joinLists s t))
        (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))).integral_prod_right
  have hp (s : Spins N) (i j : Fin N) (hij : i < j) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖(coreSlice ψ t y).value s x‖^2 / ‖x i-x j‖) := by
    have hne : (finSumFinEquiv (Sum.inl i) : Fin (N+M)) ≠ finSumFinEquiv (Sum.inl j) :=
      fun hh => (ne_of_lt hij) (Sum.inl.inj (finSumFinEquiv.injective hh))
    simpa only [coreSlice, joinLists_left] using (integrable_join (N := N) (M := M)
      (pair_integrable _ _ hne (hψ.1 (joinLists s t))
        (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))).integral_prod_right
  refine ⟨?_, ?_, ?_⟩
  · exact (integrable_finsetSum _ (fun s _ => integrable_finsetSum _
      (fun i _ => integrable_finsetSum _ (fun a _ => hk s i a)))).const_mul _
  · exact integrable_finsetSum _ (fun s _ => integrable_finsetSum _ (fun i _ => hn s i))
  · apply integrable_finsetSum; intro s _
    apply integrable_finsetSum; intro i _
    apply integrable_finsetSum; intro j _
    split_ifs with hij
    · exact hp s i j hij
    · exact integrable_zero _ _ _

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CoreSliceMassIntegrable
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
namespace CoulombAtom

lemma SobolevVector.coreSlice_mass_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) :
    Integrable (fun y => formMass (coreSlice ψ t y)) := by
  apply integrable_finsetSum
  intro s _
  simpa only [coreSlice] using
    (integrable_join (N := N) (M := M) (hψ.1 (joinLists s t)).norm.integrable_sq).integral_prod_right

lemma SobolevVector.integral_coreSlice_mass {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) :
    (∑ t : Spins M, ∫ y, formMass (coreSlice ψ t y)) = formMass ψ := by
  simp only [formMass, coreSlice]
  have h (s : Spins N) (t : Spins M) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖ψ.value (joinLists s t) (joinLists x y)‖ ^ 2) :=
    (integrable_join (N := N) (M := M) (hψ.1 (joinLists s t)).norm.integrable_sq).integral_prod_right
  simp_rw [integral_finsetSum _ (fun s _ => h s _)]
  simp_rw [integral_join (hψ.1 _).norm.integrable_sq]
  exact sum_spin_join (fun u => ∫ z, ‖ψ.value u z‖ ^ 2)

lemma SobolevVector.coreSlice_energy_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z : ℝ) (t : Spins M) :
    Integrable (fun y => formEnergy Z (coreSlice ψ t y)) := by
  have hk (s : Spins N) (i : Fin N) (a : Fin 3) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖(coreSlice ψ t y).gradient s i a x‖ ^ 2) := by
    exact (integrable_join (N := N) (M := M)
      (hψ.2.1 (joinLists s t) (finSumFinEquiv (Sum.inl i)) a).norm.integrable_sq).integral_prod_right
  have hn (s : Spins N) (i : Fin N) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖(coreSlice ψ t y).value s x‖ ^ 2 / ‖x i‖) := by
    have hh := (integrable_join (N := N) (M := M)
      (CoulombAtom.nuclear_integrable (finSumFinEquiv (Sum.inl i)) (hψ.1 (joinLists s t))
        (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))).integral_prod_right
    simpa only [coreSlice, joinLists_left] using hh
  have hp (s : Spins N) (i j : Fin N) (hij : i < j) :
      Integrable (fun y : Configuration M => ∫ x : Configuration N,
        ‖(coreSlice ψ t y).value s x‖ ^ 2 / ‖x i-x j‖) := by
    have hne : (finSumFinEquiv (Sum.inl i) : Fin (N+M)) ≠ finSumFinEquiv (Sum.inl j) :=
      fun he => (ne_of_lt hij) (Sum.inl.inj (finSumFinEquiv.injective he))
    have hh := (integrable_join (N := N) (M := M)
      (CoulombAtom.pair_integrable (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) hne
        (hψ.1 (joinLists s t)) (hψ.2.1 (joinLists s t) _) (hψ.2.2 (joinLists s t) _))).integral_prod_right
    simpa only [coreSlice, joinLists_left] using hh
  unfold formEnergy
  apply Integrable.add
  · apply Integrable.sub
    · exact (integrable_finsetSum _ (fun s _ => integrable_finsetSum _ (fun i _ =>
        integrable_finsetSum _ (fun a _ => hk s i a)))).const_mul _
    · exact (integrable_finsetSum _ (fun s _ => integrable_finsetSum _ (fun i _ =>
        hn s i))).const_mul _
  · apply integrable_finsetSum; intro s _
    apply integrable_finsetSum; intro i _
    apply integrable_finsetSum; intro j _
    split_ifs with hij
    · exact hp s i j hij
    · exact integrable_zero _ _ _

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CutCoreNumber
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

def orderedCutForm {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)
    (ψ : FormVector L) (b : Fin L → Fin 2) :
    FormVector (cutCoreNumber b + cutOutNumber b) :=
  reindexForm (cutOrder b) (multiplyForm (spatialProduct (N := L) p hp b) ψ)

lemma orderedCutForm_value {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)
    (ψ : FormVector L) (b : Fin L → Fin 2) (s) (x) :
    (orderedCutForm p hp ψ b).value s x =
      (multiplyForm (spatialProduct p hp (coreCutLabels (cutCoreNumber b) (cutOutNumber b)))
        (reindexForm (cutOrder b) ψ)).value s x := by
  change (spatialProductValue p b (x ∘ (cutOrder b).symm) : ℂ) * _ = _
  rw [spatialProductValue_reindex, cutOrder_labels]
  rfl

lemma orderedCutForm_sobolev {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)
    {ψ : FormVector L} (hψ : SobolevVector ψ) (b : Fin L → Fin 2) :
    SobolevVector (orderedCutForm p hp ψ b) :=
  (hψ.multiply _).reindex _

lemma orderedCutForm_core_antisymmetric {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)
    {ψ : FormVector L} (hψ : SobolevFermion ψ) (b : Fin L → Fin 2) :
    CoreAntisymmetric (orderedCutForm p hp ψ b) := by
  have ha := (hψ.reindex (cutOrder b)).coreAntisymmetric.multiply
    (spatialProduct p hp (coreCutLabels (cutCoreNumber b) (cutOutNumber b)))
    (fun π x => spatialProduct_invariant p _ (corePerm _ π) (coreCutLabels_invariant π) x)
  intro π s
  simpa only [orderedCutForm_value] using ha π s

lemma orderedCutForm_mass {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)
    (ψ : FormVector L) (b : Fin L → Fin 2) :
    formMass (orderedCutForm p hp ψ b) = formMass (multiplyForm (spatialProduct (N := L) p hp b) ψ) :=
  formMass_reindex _ _

def cutCoreEnergy {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)
    (Z : ℝ) (ψ : FormVector L) (b : Fin L → Fin 2) : ℝ :=
  ∑ t : Spins (cutOutNumber b), ∫ y,
    formEnergy Z (coreSlice (orderedCutForm p hp ψ b) t y)

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_DiffuseSeed
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma formKinetic_scale {N : ℕ} (c : ℝ) (ψ : FormVector N) :
    formKinetic (scaleForm c ψ) = c^2*formKinetic ψ := by
  unfold formKinetic
  simp only [scaleForm,norm_real_mul_sq,integral_const_mul,← Finset.mul_sum]
  ring


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators


open MeasureTheory Filter
open scoped Topology BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_RadialPacketBase
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
namespace CoulombAtom

lemma radialPacketSeed_mass_pos : 0 < formMass (smoothForm radialPacketSeed) := by
  have hi : 0 < ∫ x, ‖radialPacketSeed x‖^2 :=
    (radialPacketSeed_smooth.continuous.norm.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (compact_norm_sq radialPacketSeed_compact) (fun x => sq_nonneg _)
      (x := 0) (by simp [radialPacketSeed,radialPacketBase_zero_value])
  change 0 < ∑ _s : Spins 1, ∫ x, ‖radialPacketSeed x‖^2
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact mul_pos (Nat.cast_pos.mpr Fintype.card_pos) hi

lemma radialScaledRaw_gradient (R : ℝ) (s : Spins 1) (i : Fin 1) (a : Fin 3) (x : Configuration 1) :
    (radialScaledRaw R).gradient s i a x = R⁻¹ •
      (smoothForm radialPacketSeed).gradient s i a (R⁻¹ • x) := by
  change fderiv ℝ (radialPacketSeed ∘ ⇑(R⁻¹ • ContinuousLinearMap.id ℝ (Configuration 1))) x (direction i a) = _
  rw [fderiv_comp x (radialPacketSeed_smooth.differentiable (by simp)).differentiableAt
    (R⁻¹ • ContinuousLinearMap.id ℝ (Configuration 1)).differentiableAt]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.fderiv,
    smul_apply,ContinuousLinearMap.id_apply,map_smul,smoothForm]

lemma radialScaledRaw_kinetic (R : ℝ) (hR : 0 < R) :
    formKinetic (radialScaledRaw R) = R⁻¹^2 * R ^ Module.finrank ℝ (Configuration 1) *
      formKinetic (smoothForm radialPacketSeed) := by
  unfold formKinetic
  simp_rw [radialScaledRaw_gradient,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,integral_const_mul]
  have hi (s : Spins 1) (i : Fin 1) (a : Fin 3) :=
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Configuration 1))
      (fun x => ‖(smoothForm radialPacketSeed).gradient s i a x‖^2) hR.le
  simp only [smul_eq_mul] at hi
  simp_rw [hi,← Finset.mul_sum]
  ring

def radialPacketKinetic : ℝ :=
  formKinetic (smoothForm radialPacketSeed) / formMass (smoothForm radialPacketSeed)

lemma radialPacketKinetic_nonneg : 0 ≤ radialPacketKinetic :=
  div_nonneg (formKinetic_nonneg _) (by unfold formMass; positivity)

lemma radialScaledOrbital_kinetic {R : ℝ} (hR : 0 < R) :
    formKinetic (radialScaledOrbital R) = radialPacketKinetic / R^2 := by
  have hmpos : 0 < formMass (smoothForm radialPacketSeed) := by
    have hh := radialScaledRaw_mass_pos (by norm_num : (0:ℝ)<1)
    rw [radialScaledRaw_mass 1 (by norm_num), one_pow, one_mul] at hh
    exact hh
  rw [radialScaledOrbital,formKinetic_scale,inv_pow,Real.sq_sqrt (radialScaledRaw_mass_pos hR).le,
    radialScaledRaw_mass R hR,radialScaledRaw_kinetic R hR,radialPacketKinetic]
  field_simp

lemma radialLocalRaw_gradient (y : Space) (R : ℝ) (s : Spins 1) (i : Fin 1) (a : Fin 3)
    (x : Configuration 1) :
    (radialLocalRaw y R).gradient s i a x = (radialScaledRaw R).gradient s i a (x+radialCenterShift y) := by
  change fderiv ℝ ((radialScaledSeed R) ∘ (fun z => z+radialCenterShift y)) x (direction i a) = _
  have ht : HasFDerivAt (fun z : Configuration 1 => z+radialCenterShift y)
      (ContinuousLinearMap.id ℝ (Configuration 1)) x := by
    simpa only [id_eq] using (hasFDerivAt_id (𝕜 := ℝ) x).add_const (radialCenterShift y)
  have hh := ((radialScaledSeed_smooth R).differentiable (by simp) (x+radialCenterShift y)).hasFDerivAt.comp x ht
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,radialScaledRaw,smoothForm]

lemma radialLocalRaw_kinetic (y : Space) (R : ℝ) :
    formKinetic (radialLocalRaw y R) = formKinetic (radialScaledRaw R) := by
  unfold formKinetic
  simp_rw [radialLocalRaw_gradient]
  congr 1
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro a _
  exact integral_add_right_eq_self (μ := volume)
    (fun z : Configuration 1 => ‖(radialScaledRaw R).gradient s i a z‖^2) (radialCenterShift y)

lemma radialLocalOrbital_kinetic (y : Space) {R : ℝ} (hR : 0 < R) :
    formKinetic (radialLocalOrbital y R) = radialPacketKinetic / R^2 := by
  calc
    _ = formKinetic (radialScaledOrbital R) := by
      rw [radialLocalOrbital,radialScaledOrbital,formKinetic_scale,formKinetic_scale,
        radialLocalRaw_mass,radialLocalRaw_kinetic]
    _ = _ := radialScaledOrbital_kinetic hR

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PacketDensity
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
namespace CoulombAtom

lemma packetDensity_translate (y : Space) (R : ℝ) (x : Space) :
    packetDensity y R x = packetDensity 0 R (x-y) := by
  simp only [packetDensity_formula,sub_zero]

theorem packetDensity_potential (y : Space) {R : ℝ} (hR : 0 < R)
    {z : Space} (hz : R < ‖z-y‖) :
    (∫ x, packetDensity y R x / ‖z-x‖) = 1 / ‖z-y‖ := by
  have ht := integral_add_right_eq_self (μ := volume)
    (fun x : Space => packetDensity y R x / ‖z-x‖) y
  rw [← ht]
  have he : (fun x => packetDensity y R (x+y) / ‖z-(x+y)‖) =
      (fun x => packetDensity 0 R x / ‖(z-y)-x‖) := by
    funext x
    rw [packetDensity_translate,add_sub_cancel_right]
    congr 2
    abel
  rw [he]
  have hn := CoulombAnalysis.tfPotential_newton_exterior
    (packetDensity_integrable 0 hR) (packetDensity_memLp 0 hR) (packetDensity_radial R)
    hR.le (fun x hx => by simpa only [sub_zero] using packetDensity_support 0 hR hx) hz
  rw [packetDensity_mass 0 hR] at hn
  exact hn

lemma radialLocalOrbital_potential (y : Space) {R : ℝ} (hR : 0 < R)
    {z : Space} (hz : R < ‖z-y‖) (s : Spins 1) :
    (∫ x : Configuration 1, ‖(radialLocalOrbital y R).value s x‖^2 / ‖z-x 0‖) =
      (1/2 : ℝ) / ‖z-y‖ := by
  have ht := packetDensity_potential y hR hz
  simp_rw [packetDensity_eq_two y R _ s,mul_div_assoc] at ht
  rw [integral_const_mul] at ht
  have he : (∫ x : Configuration 1, ‖(radialLocalOrbital y R).value s x‖^2 / ‖z-x 0‖) =
      ∫ v : Space, ‖(radialLocalOrbital y R).value s (fun _ => v)‖^2 / ‖z-v‖ := by
    rw [← integral_one_configuration]
  rw [he]
  calc
    _ = (1 / ‖z-y‖) / 2 := by linarith
    _ = _ := by ring

lemma radialLocalOrbital_nuclear (y : Space) {R : ℝ} (hR : 0 < R)
    (hy : R < ‖y‖) : formNuclear (radialLocalOrbital y R) = 1 / ‖y‖ := by
  have hh (s : Spins 1) := radialLocalOrbital_potential y hR
    (z := 0) (by simpa only [zero_sub,norm_neg] using hy) s
  simp only [zero_sub,norm_neg] at hh
  unfold formNuclear
  simp only [Fin.sum_univ_one,hh,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  norm_num [Spins]
  ring

lemma integral_join_left {N M : ℕ} {f : Configuration (N+M) → ℝ}
    (hf : Integrable f) :
    (∫ x : Configuration N, ∫ y : Configuration M, f (joinLists x y)) = ∫ z, f z := by
  have hj := integrable_join (N := N) (M := M) hf
  have he := (configurationJoin_preserving N M).integral_comp
    (configurationJoin N M).toHomeomorph.measurableEmbedding f
  simp only [configurationJoin_apply_prod] at he
  rw [Measure.volume_eq_prod] at hj he
  exact (integral_prod _ hj).symm.trans he

lemma tensor_packet_pair {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) {R B : ℝ} (hR : 0 < R) (hRB : R < B)
    (hc : ∀ x i, ‖x i-y‖ < B → FormZeroAt ψ x)
    (s : Spins N) (t : Spins 1) (i : Fin N) :
    (∫ z, ‖(tensorForm ψ (radialLocalOrbital y R)).value (joinLists s t) z‖^2 /
      ‖z i.castSucc-z (Fin.last N)‖) =
      (1/2 : ℝ) * ∫ x, ‖ψ.value s x‖^2 / ‖x i-y‖ := by
  have hφ := (radialLocalOrbital_admissible y hR).sobolevFermion.sobolevVector
  have hT := hψ.tensor hφ
  have hi := pair_integrable i.castSucc (Fin.last N) (Fin.castSucc_ne_last i)
    (hT.1 (joinLists s t)) (hT.2.1 (joinLists s t) _) (hT.2.2 (joinLists s t) _)
  rw [← integral_join_left hi]
  change (∫ x : Configuration N, ∫ v : Configuration 1,
    ‖(tensorForm ψ (radialLocalOrbital y R)).value (joinLists s t) (joinLists x v)‖^2 /
    ‖joinLists x v (finSumFinEquiv (Sum.inl i)) -
      joinLists x v (finSumFinEquiv (Sum.inr (0 : Fin 1)))‖) = _
  simp only [tensorForm_value_join,joinLists_left,joinLists_right,norm_mul,mul_pow,
    mul_div_assoc,integral_const_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  by_cases hz : ψ.value s x = 0
  · simp only [hz,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_mul,zero_div,mul_zero]
  · have hd : R < ‖x i-y‖ := hRB.trans_le (le_of_not_gt fun hh => hz ((hc x i hh s).1))
    dsimp only
    rw [radialLocalOrbital_potential y hR hd]
    ring

lemma tensorCross_packet {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) {R B : ℝ} (hR : 0 < R) (hRB : R < B)
    (hc : ∀ x i, ‖x i-y‖ < B → FormZeroAt ψ x) :
    tensorCross ψ (radialLocalOrbital y R) = coreCoulombAt ψ y := by
  unfold tensorCross coreCoulombAt
  simp_rw [tensor_packet_pair hψ y hR hRB hc,← Finset.mul_sum]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  norm_num [Spins]
  simp only [← Finset.mul_sum]
  ring

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_FormBody
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma formOneBody_tensor {N M : ℕ} (ψ : FormVector N) (φ : FormVector M) (w : Space → ℝ) :
    formOneBody (tensorForm ψ φ) w = formOneBody ψ w * formMass φ +
      formMass ψ * formOneBody φ w := by
  have hl (s : Spins N) (t : Spins M) (i : Fin N) :
      (∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 * w (z (finSumFinEquiv (Sum.inl i)))) =
        (∫ x, ‖ψ.value s x‖^2 * w (x i)) * (∫ y, ‖φ.value t y‖^2) := by
    change (∫ z, ‖ψ.value (leftList (joinLists s t)) (leftList z) *
      φ.value (rightList (joinLists s t)) (rightList z)‖^2 * w (leftList z i)) = _
    simp only [leftList_join,rightList_join,norm_mul,mul_pow]
    simp_rw [mul_right_comm _ _ (w _)]
    exact integral_product_join (N := N) (M := M) (fun x => ‖ψ.value s x‖^2 * w (x i))
      (fun y => ‖φ.value t y‖^2)
  have hr (s : Spins N) (t : Spins M) (i : Fin M) :
      (∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 * w (z (finSumFinEquiv (Sum.inr i)))) =
        (∫ x, ‖ψ.value s x‖^2) * (∫ y, ‖φ.value t y‖^2 * w (y i)) := by
    change (∫ z, ‖ψ.value (leftList (joinLists s t)) (leftList z) *
      φ.value (rightList (joinLists s t)) (rightList z)‖^2 * w (rightList z i)) = _
    simp only [leftList_join,rightList_join,norm_mul,mul_pow,mul_assoc]
    exact integral_product_join (N := N) (M := M) (fun x => ‖ψ.value s x‖^2)
      (fun y => ‖φ.value t y‖^2 * w (y i))
  have hk (s : Spins N) (t : Spins M) :
      (∑ i, ∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 * w (z i)) =
      (∑ i, ∫ x, ‖ψ.value s x‖^2 * w (x i))*(∫ y, ‖φ.value t y‖^2) +
      (∫ x, ‖ψ.value s x‖^2)*(∑ i, ∫ y, ‖φ.value t y‖^2 * w (y i)) := by
    rw [← Equiv.sum_comp finSumFinEquiv,Fintype.sum_sum_type]
    simp only [hl,hr,Finset.sum_mul,Finset.mul_sum]
  unfold formOneBody formMass
  rw [← sum_spin_join]
  simp_rw [hk,Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum]

lemma insertOrbital_sobolev {N : ℕ} {ψ : FormVector N} {φ : FormVector 1}
    (hψ : SobolevFermion ψ) (hφ : SobolevFermion φ) : SobolevFermion (insertOrbital ψ φ) :=
  (wedgeForm_fermion (hψ.sobolevVector.tensor hφ.sobolevVector)
    (tensor_coreAntisymmetric hψ φ)).scale _

lemma formMass_insertOrbital {N : ℕ} {ψ : FormVector N} {φ : FormVector 1}
    (hψ : SobolevVector ψ) (hφ : SobolevVector φ)
    (hd : FormsDisjoint (insertionTerm (tensorForm ψ φ))) :
    formMass (insertOrbital ψ φ) = formMass ψ * formMass φ := by
  rw [insertOrbital,formMass_scale,formMass_wedge (hψ.tensor hφ) hd,← mul_assoc,
    insertion_normalizer,one_mul,formMass_tensor]

lemma formEnergy_insertOrbital {N : ℕ} {ψ : FormVector N} {φ : FormVector 1}
    (hψ : SobolevVector ψ) (hφ : SobolevVector φ)
    (hd : FormsDisjoint (insertionTerm (tensorForm ψ φ))) (Z : ℝ) :
    formEnergy Z (insertOrbital ψ φ) = formEnergy Z (tensorForm ψ φ) := by
  rw [insertOrbital,formEnergy_scale,formEnergy_wedge (hψ.tensor hφ) hd,← mul_assoc,
    insertion_normalizer,one_mul]

lemma formOneBody_insertOrbital {N : ℕ} {ψ : FormVector N} {φ : FormVector 1} {w : Space → ℝ}
    (h : OneBodyIntegrable (tensorForm ψ φ) w)
    (hd : FormsDisjoint (insertionTerm (tensorForm ψ φ))) :
    formOneBody (insertOrbital ψ φ) w = formOneBody ψ w * formMass φ +
      formMass ψ * formOneBody φ w := by
  rw [insertOrbital,formOneBody_scale,formOneBody_wedge h hd,← mul_assoc,
    insertion_normalizer,one_mul,formOneBody_tensor]


open MeasureTheory Filter
open scoped Topology BigOperators


lemma radialLocalOrbital_avoids (y z : Space) {R B : ℝ} (hR : 0 < R)
    (hsep : R+B ≤ ‖y-z‖) : FormAvoids (radialLocalOrbital y R) (Metric.ball z B) := by
  intro x i hx
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have hx' : ‖x 0-z‖ < B := Metric.mem_ball.mp hx
  have ht : ‖y-z‖ ≤ ‖x 0-y‖+‖x 0-z‖ := by
    calc
      _ ≤ ‖y-x 0‖+‖x 0-z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = _ := by rw [norm_sub_rev y (x 0)]
  exact radialLocalOrbital_zero y hR (by linarith)

lemma integrable_coreCoulombAt {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) {B : ℝ} (hB : 0 < B) (hc : FormAvoids ψ (Metric.ball y B)) (s : Spins N) (i : Fin N) :
    Integrable (fun x => ‖ψ.value s x‖^2/‖x i-y‖) := by
  have hm1 : AEStronglyMeasurable (fun x : Configuration N => ‖ψ.value s x‖^2) volume :=
    (hψ.1 s).aestronglyMeasurable.norm.pow 2
  have hm2 : AEStronglyMeasurable (fun x : Configuration N => ‖x i-y‖⁻¹) volume :=
    (((continuous_apply i).sub continuous_const).norm.measurable.inv).aestronglyMeasurable
  have hm : AEStronglyMeasurable (fun x : Configuration N => ‖ψ.value s x‖^2/‖x i-y‖) volume := by
    simpa only [div_eq_mul_inv] using hm1.fun_mul hm2
  apply Integrable.mono' (((hψ.1 s).integrable_norm_pow (by norm_num)).div_const B) hm
  apply Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) (norm_nonneg _))]
  by_cases hz : ψ.value s x = 0
  · simp only [hz,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_div,le_refl]
  · have hd : B ≤ ‖x i-y‖ := by
      by_contra hh
      exact hz (hc x i (Metric.mem_ball.mpr (not_le.mp hh)) s).1
    exact div_le_div_of_nonneg_left (sq_nonneg _) hB hd

lemma coreCoulombAt_insertOrbital {N : ℕ} {ψ : FormVector N} {φ : FormVector 1}
    (hψ : SobolevVector ψ) (hφ : SobolevVector φ)
    (hd : FormsDisjoint (insertionTerm (tensorForm ψ φ)))
    (y : Space) {B : ℝ} (hB : 0 < B)
    (hcψ : FormAvoids ψ (Metric.ball y B)) (hcφ : FormAvoids φ (Metric.ball y B)) :
    coreCoulombAt (insertOrbital ψ φ) y = coreCoulombAt ψ y * formMass φ +
      formMass ψ * coreCoulombAt φ y := by
  simp only [coreCoulombAt_eq_formOneBody]
  apply formOneBody_insertOrbital _ hd
  intro s i
  simpa only [mul_one_div] using integrable_coreCoulombAt (hψ.tensor hφ) y hB
    (hcψ.tensor hcφ) s i

lemma coreCoulombAt_packet (y z : Space) {R : ℝ} (hR : 0 < R)
    (hsep : R < ‖y-z‖) : coreCoulombAt (radialLocalOrbital y R) z = 1/‖y-z‖ := by
  have hh (s : Spins 1) := radialLocalOrbital_potential y hR
    (z := z) (by rwa [norm_sub_rev]) s
  simp only [coreCoulombAt,Fin.sum_univ_one]
  have he (s : Spins 1) : (∫ x : Configuration 1,
      ‖(radialLocalOrbital y R).value s x‖^2/‖x 0-z‖) = (1/2:ℝ)/‖y-z‖ := by
    simpa only [norm_sub_rev] using hh s
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  norm_num [Spins]
  ring


open MeasureTheory Filter
open scoped Topology BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PacketInsert
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
namespace CoulombAtom

lemma packetInsert_sobolev {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (y : ℕ → Space) {r : ℝ} (hr : 0 < r) (k : ℕ) : SobolevFermion (packetInsert ψ y r k) := by
  induction k with
  | zero => exact hψ
  | succ k ih => exact insertOrbital_sobolev ih (radialLocalOrbital_admissible (y k) hr).sobolevFermion

lemma packetInsert_avoids {N : ℕ} {ψ : FormVector N} (y : ℕ → Space) {r : ℝ}
    (hr : 0 < r) (k : ℕ) (z : Space)
    (hc : FormAvoids ψ (Metric.ball z (2*r)))
    (hsep : ∀ i < k, 3*r ≤ ‖y i-z‖) : FormAvoids (packetInsert ψ y r k) (Metric.ball z (2*r)) := by
  induction k with
  | zero => exact hc
  | succ k ih =>
    exact (ih (fun i hi => hsep i (by omega))).insertOrbital
      (radialLocalOrbital_avoids (y k) z hr (by have := hsep k (by omega); linarith))

lemma packetInsert_disjoint {N : ℕ} {ψ : FormVector N} (y : ℕ → Space) {r : ℝ}
    (hr : 0 < r) (k : ℕ)
    (hc : FormAvoids ψ (Metric.ball (y k) (2*r)))
    (hsep : ∀ i < k, 3*r ≤ ‖y i-y k‖) :
    FormsDisjoint (insertionTerm (tensorForm (packetInsert ψ y r k) (radialLocalOrbital (y k) r))) := by
  apply tensor_insertion_disjoint_set _ _ (Metric.ball (y k) (2*r))
  · exact packetInsert_avoids y hr k (y k) hc hsep
  · intro x hx
    have hh : 2*r ≤ ‖x 0-y k‖ := le_of_not_gt (fun h => hx (Metric.mem_ball.mpr h))
    exact radialLocalOrbital_zero (y k) hr (by linarith)

lemma packetInsert_mass {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (y : ℕ → Space) {r : ℝ} (hr : 0 < r) (k : ℕ)
    (hc : ∀ i < k, FormAvoids ψ (Metric.ball (y i) (2*r)))
    (hsep : ∀ i j, i < j → j < k → 3*r ≤ ‖y i-y j‖) :
    formMass (packetInsert ψ y r k) = formMass ψ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [packetInsert,formMass_insertOrbital (packetInsert_sobolev hψ y hr k).sobolevVector
      (radialLocalOrbital_admissible (y k) hr).sobolevFermion.sobolevVector
      (packetInsert_disjoint y hr k (hc k (by omega)) (fun i hi => hsep i k hi (by omega)))]
    have hm : formMass (radialLocalOrbital (y k) r) = 1 :=
      (radialLocalOrbital_admissible (y k) hr).2.2.2.2.1
    rw [hm,mul_one]
    exact ih (fun i hi => hc i (by omega)) (fun i j hij hj => hsep i j hij (by omega))

lemma packetInsert_field {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (y : ℕ → Space) {r : ℝ} (hr : 0 < r) (k : ℕ)
    (hc : ∀ i < k, FormAvoids ψ (Metric.ball (y i) (2*r)))
    (hsep : ∀ i j, i < j → j < k → 3*r ≤ ‖y i-y j‖)
    (z : Space) (hz : FormAvoids ψ (Metric.ball z (2*r)))
    (hzsep : ∀ i < k, 3*r ≤ ‖y i-z‖) :
    coreCoulombAt (packetInsert ψ y r k) z = coreCoulombAt ψ z +
      formMass ψ * ∑ i ∈ Finset.range k, 1/‖y i-z‖ := by
  induction k with
  | zero => simp [packetInsert]
  | succ k ih =>
    have hck : ∀ i < k, FormAvoids ψ (Metric.ball (y i) (2*r)) := fun i hi => hc i (by omega)
    have hsk : ∀ i j, i < j → j < k → 3*r ≤ ‖y i-y j‖ := fun i j hij hj => hsep i j hij (by omega)
    have hzsk : ∀ i < k, 3*r ≤ ‖y i-z‖ := fun i hi => hzsep i (by omega)
    have hzk : 3*r ≤ ‖y k-z‖ := hzsep k (by omega)
    have hm : formMass (radialLocalOrbital (y k) r) = 1 :=
      (radialLocalOrbital_admissible (y k) hr).2.2.2.2.1
    rw [packetInsert,coreCoulombAt_insertOrbital
      (packetInsert_sobolev hψ y hr k).sobolevVector
      (radialLocalOrbital_admissible (y k) hr).sobolevFermion.sobolevVector
      (packetInsert_disjoint y hr k (hc k (by omega)) (fun i hi => hsep i k hi (by omega)))
      z (by positivity : 0 < 2*r) (packetInsert_avoids y hr k z hz hzsk)
      (radialLocalOrbital_avoids (y k) z hr (by linarith)),hm,mul_one,
      packetInsert_mass hψ y hr k hck hsk,coreCoulombAt_packet (y k) z hr (by linarith),
      ih hck hsk hzsk,Finset.sum_range_succ]
    ring

lemma packetInsert_energy {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (y : ℕ → Space) {r : ℝ} (hr : 0 < r) (k : ℕ)
    (hc : ∀ i < k, FormAvoids ψ (Metric.ball (y i) (2*r)))
    (hsep : ∀ i j, i < j → j < k → 3*r ≤ ‖y i-y j‖)
    (hnuc : ∀ i < k, r < ‖y i‖) (Z : ℝ) :
    formEnergy Z (packetInsert ψ y r k) = formEnergy Z ψ - packetScreenedSum ψ Z y k +
      formMass ψ * ((k:ℝ)*radialPacketKinetic/r^2 + packetPairEnergy y k) := by
  induction k with
  | zero => simp [packetInsert,packetScreenedSum,packetPairEnergy]
  | succ k ih =>
    have hck : ∀ i < k, FormAvoids ψ (Metric.ball (y i) (2*r)) := fun i hi => hc i (by omega)
    have hsk : ∀ i j, i < j → j < k → 3*r ≤ ‖y i-y j‖ := fun i j hij hj => hsep i j hij (by omega)
    have hnk : ∀ i < k, r < ‖y i‖ := fun i hi => hnuc i (by omega)
    have hsk' : ∀ i < k, 3*r ≤ ‖y i-y k‖ := fun i hi => hsep i k hi (by omega)
    have hT := (packetInsert_sobolev hψ y hr k).sobolevVector
    have hφ := radialLocalOrbital_admissible (y k) hr
    have hm : formMass (radialLocalOrbital (y k) r) = 1 := hφ.2.2.2.2.1
    rw [packetInsert,formEnergy_insertOrbital hT hφ.sobolevFermion.sobolevVector
      (packetInsert_disjoint y hr k (hc k (by omega)) hsk'),formEnergy_tensor_one,hm,mul_one,
      radialLocalOrbital_kinetic _ hr,radialLocalOrbital_nuclear _ hr (hnuc k (by omega)),
      tensorCross_packet hT (y k) hr (by linarith : r < 2*r)
        (packetInsert_avoids y hr k (y k) (hc k (by omega)) hsk'),
      packetInsert_mass hψ y hr k hck hsk,
      packetInsert_field hψ y hr k hck hsk (y k) (hc k (by omega)) hsk',
      ih hck hsk hnk]
    simp only [packetScreenedSum,packetPairEnergy,Finset.sum_range_succ,Nat.cast_add,Nat.cast_one]
    ring

theorem many_packet_screening {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (y : ℕ → Space) {r : ℝ} (hr : 0 < r) (k : ℕ)
    (hc : ∀ i < k, FormAvoids ψ (Metric.ball (y i) (2*r)))
    (hsep : ∀ i j, i < j → j < k → 3*r ≤ ‖y i-y j‖)
    (hnuc : ∀ i < k, r < ‖y i‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    packetScreenedSum ψ Z y k ≤
      (formEnergy Z ψ + lam*N*formMass ψ - priceEnergy (energy Z) lam*formMass ψ) +
      formMass ψ * ((k:ℝ)*(radialPacketKinetic/r^2+lam) + packetPairEnergy y k) := by
  have hh := (packetInsert_sobolev hψ y hr k).priced_lower_bound hZ hlam
  rw [packetInsert_energy hψ y hr k hc hsep hnuc Z,packetInsert_mass hψ y hr k hc hsep,
    Nat.cast_add] at hh
  simp only [div_eq_mul_inv] at hh ⊢
  nlinarith

end CoulombAtom

open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SpatialRotation
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
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
namespace CoulombAtom

lemma packetDensity_rotate (g : SpatialRotation) (p x : Space) (r : ℝ) :
    packetDensity (rotate g p) r (rotate g x) = packetDensity p r x := by
  simp only [packetDensity_formula,radialPacketBase,norm_smul]
  rw [← (rotate g).map_sub,(rotate g).norm_map]

lemma averagedPacket_radial (p : Space) (r : ℝ) :
    CoulombAnalysis.IsRadial (averagedPacket p r) := by
  intro x y hxy
  obtain ⟨g,hg⟩ := exists_rotate_norm_eq x y hxy
  unfold averagedPacket
  rw [← rotation_integral_left (fun h => packetDensity (rotate h p) r y) g]
  apply integral_congr_ae (Eventually.of_forall fun h => ?_)
  rw [← hg,rotate_mul,packetDensity_rotate]

lemma averagedPacket_support (p : Space) {r : ℝ} (hr : 0 < r) {x : Space}
    (hx : averagedPacket p r x ≠ 0) : ‖x‖ ≤ ‖p‖+r := by
  by_contra hh
  apply hx
  unfold averagedPacket
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro g
  by_contra hg
  have hdist := packetDensity_support (rotate g p) hr hg
  have hn := norm_add_le (x-rotate g p) (rotate g p)
  rw [sub_add_cancel,(rotate g).norm_map] at hn
  exact hh (by linarith)

lemma rotationalPacket_continuous (p : Space) (r : ℝ) :
    Continuous (fun q : SpatialRotation × Space => packetDensity (rotate q.1 p) r q.2) := by
  have ha : Continuous (fun q : SpatialRotation × Space => rotate q.1 p) :=
    (continuous_subtype_val.comp continuous_fst).clm_apply continuous_const
  simp_rw [packetDensity_formula]
  exact continuous_const.mul ((radialPacketBase_smooth.continuous.comp
    ((continuous_snd.sub ha).const_smul r⁻¹)).norm.pow 2)

lemma averagedPacket_continuous (p : Space) (r : ℝ) : Continuous (averagedPacket p r) := by
  have hf : Continuous (Function.uncurry (fun x : Space => fun g : SpatialRotation =>
      packetDensity (rotate g p) r x)) := by
    change Continuous (fun q : Space × SpatialRotation => packetDensity (rotate q.2 p) r q.1)
    have ha : Continuous (fun q : Space × SpatialRotation => rotate q.2 p) :=
      (continuous_subtype_val.comp continuous_snd).clm_apply continuous_const
    simp_rw [packetDensity_formula]
    exact continuous_const.mul ((radialPacketBase_smooth.continuous.comp
      ((continuous_fst.sub ha).const_smul r⁻¹)).norm.pow 2)
  have hh := continuous_parametric_integral_of_continuous (μ := rotationMeasure)
    (f := fun x : Space => fun g : SpatialRotation => packetDensity (rotate g p) r x)
    hf isCompact_univ
  unfold averagedPacket
  simpa only [Measure.restrict_univ] using hh

lemma averagedPacket_compact (p : Space) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (averagedPacket p r) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (‖p‖+r))
  intro x hx
  exact mem_closedBall_zero_iff.mpr (averagedPacket_support p hr hx)

lemma rotationalPacket_compact (p : Space) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (fun q : SpatialRotation × Space => packetDensity (rotate q.1 p) r q.2) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_univ.prod (isCompact_closedBall 0 (‖p‖+r)))
  intro q hq
  refine ⟨mem_univ _, mem_closedBall_zero_iff.mpr ?_⟩
  have hd := packetDensity_support (rotate q.1 p) hr hq
  have hh := norm_add_le (q.2-rotate q.1 p) (rotate q.1 p)
  rw [sub_add_cancel,(rotate q.1).norm_map] at hh
  linarith

lemma rotationalPacket_integrable (p : Space) {r : ℝ} (hr : 0 < r) :
    Integrable (fun q : SpatialRotation × Space => packetDensity (rotate q.1 p) r q.2)
      (rotationMeasure.prod volume) :=
  (rotationalPacket_continuous p r).integrable_of_hasCompactSupport (rotationalPacket_compact p hr)

lemma averagedPacket_mass (p : Space) {r : ℝ} (hr : 0 < r) :
    (∫ x, averagedPacket p r x) = 1 := by
  unfold averagedPacket
  rw [← integral_integral_swap (rotationalPacket_integrable p hr)]
  simp only [packetDensity_mass _ hr, integral_const, probReal_univ, smul_eq_mul, one_mul]

lemma averagedPacket_integrable (p : Space) {r : ℝ} (hr : 0 < r) :
    Integrable (averagedPacket p r) :=
  (averagedPacket_continuous p r).integrable_of_hasCompactSupport (averagedPacket_compact p hr)

lemma averagedPacket_memLp (p : Space) {r : ℝ} (hr : 0 < r) :
    MemLp (averagedPacket p r) (5/3) :=
  (averagedPacket_continuous p r).memLp_of_hasCompactSupport (averagedPacket_compact p hr)

end CoulombAtom

open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_TruncatedCoulomb
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
namespace CoulombAtom

lemma packetDensityConstant_pos : 0 < packetDensityConstant :=
  div_pos (Nat.cast_pos.mpr Fintype.card_pos) radialPacketSeed_mass_pos

lemma packetDensity_bound (y x : Space) {r : ℝ} (hr : 0 < r) :
    packetDensity y r x ≤ packetDensityConstant/r^3 := by
  rw [packetDensity_formula,inv_pow,Real.sq_sqrt (radialScaledRaw_mass_pos hr).le,
    radialScaledRaw_mass r hr]
  have hdim : Module.finrank ℝ (Configuration 1) = 3 := by
    change Module.finrank ℝ (Fin 1 → Space) = 3
    rw [Module.finrank_pi_fintype]
    simp only [Space,finrank_euclideanSpace_fin,Fin.sum_univ_one]
  rw [hdim]
  calc
    _ ≤ (Fintype.card (Spins 1) : ℝ) * (r^3*formMass (smoothForm radialPacketSeed))⁻¹ * 1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity [radialPacketSeed_mass_pos])
      have hb := radialPacketBase_bound (r⁻¹ • (x-y))
      nlinarith [norm_nonneg (radialPacketBase (r⁻¹ • (x-y)))]
    _ = _ := by unfold packetDensityConstant; ring

end CoulombAtom

open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PacketCloud
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
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

lemma packetCloud_integrable (p : ℕ → Space) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    Integrable (packetCloud p r k) := by
  exact integrable_finsetSum _ (fun i _ => packetDensity_integrable (p i) hr)

lemma packetCloud_memLp (p : ℕ → Space) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    MemLp (packetCloud p r k) (5/3) := by
  exact memLp_finsetSum _ (fun i _ => packetDensity_memLp (p i) hr)

lemma packetCloud_bound (p : ℕ → Space) {r : ℝ} (hr : 0 < r) (k : ℕ)
    (hsep : ∀ i j, i < j → j < k → 3*r ≤ ‖p i-p j‖) (x : Space) :
    packetCloud p r k x ≤ packetDensityConstant/r^3 := by
  by_cases hx : packetCloud p r k x = 0
  · rw [hx]; positivity [packetDensityConstant_pos]
  obtain ⟨i,hi,hix⟩ := packetCloud_exists hx
  have unique (j : ℕ) (hj : j ∈ Finset.range k) (hji : j ≠ i) : packetDensity (p j) r x = 0 := by
    by_contra hjx
    have h1 := packetDensity_support (p i) hr hix
    have h2 := packetDensity_support (p j) hr hjx
    have h3 : 3*r ≤ ‖p i-p j‖ := by
      rcases lt_or_gt_of_ne hji with hji | hij
      · rw [norm_sub_rev]; exact hsep j i hji hi
      · exact hsep i j hij (Finset.mem_range.mp hj)
    have ht := norm_sub_le_norm_sub_add_norm_sub (p i) x (p j)
    rw [norm_sub_rev (p i) x] at ht
    linarith
  unfold packetCloud
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr hi) unique]
  exact packetDensity_bound (p i) x hr

lemma packetCloud_support (p : ℕ → Space) {r : ℝ} (hr : 0 < r) (k : ℕ)
    {a : ℝ} (hp : ∀ i < k, ‖p i‖ ≤ a) {x : Space} (hx : packetCloud p r k x ≠ 0) :
    ‖x‖ ≤ a+r := by
  obtain ⟨i,hi,hix⟩ := packetCloud_exists hx
  have h1 := packetDensity_support (p i) hr hix
  have ht := norm_add_le (x-p i) (p i)
  rw [sub_add_cancel] at ht
  have h2 := hp i hi
  linarith

lemma packetCloud_potential_bound (p : ℕ → Space) {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (k : ℕ)
    (hsep : ∀ i j, i < j → j < k → 3*r ≤ ‖p i-p j‖)
    (hp : ∀ i < k, ‖p i‖ ≤ a) (z : Space) (hz : ‖z‖ ≤ a) :
    (∫ x : Space, packetCloud p r k x/‖z-x‖) ≤
      packetDensityConstant/r^3 * (2*a+2*r)^2 * unitCoulombIntegral := by
  have hL : 0 < 2*a+2*r := by linarith
  have hi := CoulombAnalysis.tfPotential_integrable (packetCloud_integrable p hr k)
    (packetCloud_memLp p hr k) z
  have hk : Integrable (fun x : Space => truncatedCoulomb (2*a+2*r) (z-x)) :=
    (integrable_comp_sub_left _ z).mpr (truncatedCoulomb_integrable _)
  calc
    _ ≤ ∫ x : Space, (packetDensityConstant/r^3)*truncatedCoulomb (2*a+2*r) (z-x) := by
      apply integral_mono hi (hk.const_mul _)
      intro x
      change packetCloud p r k x / ‖z-x‖ ≤
        (packetDensityConstant/r^3)*truncatedCoulomb (2*a+2*r) (z-x)
      by_cases hx : packetCloud p r k x = 0
      · rw [hx,zero_div]
        exact mul_nonneg (div_nonneg packetDensityConstant_pos.le (pow_nonneg hr.le _))
          (truncatedCoulomb_nonneg _ _)
      · have hxs := packetCloud_support p hr k hp hx
        have ht := norm_sub_le z x
        have hmem : z-x ∈ ball (0 : Space) (2*a+2*r) := by
          rw [mem_ball_zero_iff]; linarith
        rw [truncatedCoulomb,indicator_of_mem hmem,mul_one_div]
        exact div_le_div_of_nonneg_right (packetCloud_bound p hr k hsep x) (norm_nonneg _)
    _ = _ := by
      rw [integral_const_mul,integral_sub_left_eq_self,truncatedCoulomb_integral hL]
      ring

theorem packetPairEnergy_bound (p : ℕ → Space) {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (k : ℕ)
    (hsep : ∀ i j, i < j → j < k → 3*r ≤ ‖p i-p j‖)
    (hp : ∀ i < k, ‖p i‖ ≤ a) :
    packetPairEnergy p k ≤ (k:ℝ)*(packetDensityConstant/r^3*(2*a+2*r)^2*unitCoulombIntegral) := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range k) :
      (∑ i ∈ Finset.range j, 1/‖p i-p j‖) ≤
      packetDensityConstant/r^3*(2*a+2*r)^2*unitCoulombIntegral := by
    have hjk := Finset.mem_range.mp hj
    have he : (∑ i ∈ Finset.range j, 1/‖p i-p j‖) =
        ∫ x : Space, packetCloud p r j x/‖p j-x‖ := by
      simp only [packetCloud,Finset.sum_div]
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        have his := hsep i j (Finset.mem_range.mp hi) hjk
        rw [packetDensity_potential (p i) hr (by rw [norm_sub_rev]; linarith),norm_sub_rev]
      · intro i _
        exact CoulombAnalysis.tfPotential_integrable (packetDensity_integrable (p i) hr)
          (packetDensity_memLp (p i) hr) (p j)
    rw [he]
    exact packetCloud_potential_bound p hr ha j
      (fun i l hil hl => hsep i l hil (by omega)) (fun i hi => hp i (by omega)) (p j) (hp j hjk)
  calc
    _ ≤ ∑ _j ∈ Finset.range k, packetDensityConstant/r^3*(2*a+2*r)^2*unitCoulombIntegral :=
      Finset.sum_le_sum hterm
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]


open MeasureTheory Filter Set Metric
open scoped Topology BigOperators


open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PacketDensityRadius
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
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
namespace CoulombAtom

lemma packetDensity_radius (p : Space) {r : ℝ} (hr : 0 < r) (g : SpatialRotation)
    {x : Space} (hx : packetDensity (rotate g p) r x ≠ 0) : ‖x‖ ≤ ‖p‖+r := by
  have hd := packetDensity_support (rotate g p) hr hx
  have hh := norm_add_le (x-rotate g p) (rotate g p)
  rw [sub_add_cancel,(rotate g).norm_map] at hh
  linarith

lemma rotationPacket_kernel_integrable (p z : Space) {r : ℝ} (hr : 0 < r)
    (hz : ‖p‖+r < ‖z‖) :
    Integrable (fun q : SpatialRotation × Space => packetDensity (rotate q.1 p) r q.2 / ‖z-q.2‖)
      (rotationMeasure.prod volume) := by
  have hc := (rotationalPacket_continuous p r).measurable
  have hd : Measurable (fun q : SpatialRotation × Space => ‖z-q.2‖) :=
    (continuous_const.sub continuous_snd).norm.measurable
  apply ((rotationalPacket_integrable p hr).div_const (‖z‖-(‖p‖+r))).mono'
    (hc.div hd).aestronglyMeasurable
  apply Eventually.of_forall
  intro q
  change ‖packetDensity (rotate q.1 p) r q.2 / ‖z-q.2‖‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg
    (packetDensity_nonneg _ _ _) (norm_nonneg _))]
  by_cases hq : packetDensity (rotate q.1 p) r q.2 = 0
  · simp only [hq,zero_div,le_refl]
  · have hp := packetDensity_radius p hr q.1 hq
    have hn := norm_add_le (z-q.2) q.2
    rw [sub_add_cancel] at hn
    exact div_le_div_of_nonneg_left (packetDensity_nonneg _ _ _) (by linarith) (by linarith)

theorem rotation_kernel_newton (p z : Space) (hz : ‖p‖ < ‖z‖) :
    (∫ g : SpatialRotation, 1 / ‖z-rotate g p‖ ∂rotationMeasure) = 1 / ‖z‖ := by
  let r : ℝ := (‖z‖-‖p‖)/2
  have hr : 0 < r := by dsimp [r]; linarith
  have hzr : ‖p‖+r < ‖z‖ := by dsimp [r]; linarith
  have he (g : SpatialRotation) : r < ‖z-rotate g p‖ := by
    have hn := norm_add_le (z-rotate g p) (rotate g p)
    rw [sub_add_cancel,(rotate g).norm_map] at hn
    linarith
  have hn := CoulombAnalysis.tfPotential_newton_exterior
    (averagedPacket_integrable p hr) (averagedPacket_memLp p hr) (averagedPacket_radial p r)
    (show 0 ≤ ‖p‖+r by positivity) (fun x hx => averagedPacket_support p hr hx) hzr
  rw [averagedPacket_mass p hr] at hn
  calc
    _ = ∫ g : SpatialRotation, ∫ x : Space,
        packetDensity (rotate g p) r x / ‖z-x‖ ∂volume ∂rotationMeasure := by
      apply integral_congr_ae (Eventually.of_forall fun g => ?_)
      exact (packetDensity_potential (rotate g p) hr (he g)).symm
    _ = ∫ x : Space, ∫ g : SpatialRotation,
        packetDensity (rotate g p) r x / ‖z-x‖ ∂rotationMeasure :=
      integral_integral_swap (rotationPacket_kernel_integrable p z hr hzr)
    _ = _ := by
      simp_rw [integral_div]
      exact hn

end CoulombAtom

open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_RotationCoreKernelIntegrable
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
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

lemma rotation_core_kernel_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y p : Space) {B : ℝ} (hp : ‖p‖ < B) (hc : FormAvoids ψ (ball y B))
    (s : Spins N) (i : Fin N) :
    Integrable (fun q : SpatialRotation × Configuration N =>
      ‖ψ.value s q.2‖^2/‖q.2 i-(y+rotate q.1 p)‖) (rotationMeasure.prod volume) := by
  have hm1 : AEStronglyMeasurable (fun q : SpatialRotation × Configuration N =>
      ‖ψ.value s q.2‖^2) (rotationMeasure.prod volume) :=
    ((hψ.1 s).aestronglyMeasurable.norm.pow 2).comp_snd
  have ha : Continuous (fun q : SpatialRotation × Configuration N => rotate q.1 p) :=
    (continuous_subtype_val.comp continuous_fst).clm_apply continuous_const
  have hm2 : AEStronglyMeasurable (fun q : SpatialRotation × Configuration N =>
      ‖q.2 i-(y+rotate q.1 p)‖⁻¹) (rotationMeasure.prod volume) :=
    ((((continuous_apply i).comp continuous_snd).sub (continuous_const.add ha)).norm.measurable.inv).aestronglyMeasurable
  have hm : AEStronglyMeasurable (fun q : SpatialRotation × Configuration N =>
      ‖ψ.value s q.2‖^2/‖q.2 i-(y+rotate q.1 p)‖) (rotationMeasure.prod volume) := by
    simpa only [div_eq_mul_inv] using hm1.fun_mul hm2
  apply ((((hψ.1 s).integrable_norm_pow (by norm_num)).comp_snd rotationMeasure).div_const
    (B-‖p‖)).mono' hm
  apply Eventually.of_forall
  intro q
  change ‖‖ψ.value s q.2‖^2/‖q.2 i-(y+rotate q.1 p)‖‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) (norm_nonneg _))]
  by_cases hz : ψ.value s q.2 = 0
  · simp only [hz,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_div,le_refl]
  · have hd : B ≤ ‖q.2 i-y‖ := by
      by_contra hh
      exact hz (hc q.2 i (mem_ball.mpr (not_le.mp hh)) s).1
    have ht := norm_add_le (q.2 i-(y+rotate q.1 p)) (rotate q.1 p)
    rw [show q.2 i-(y+rotate q.1 p)+rotate q.1 p = q.2 i-y by abel,
      (rotate q.1).norm_map] at ht
    exact div_le_div_of_nonneg_left (sq_nonneg _) (sub_pos.mpr hp) (by linarith)

lemma rotation_core_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y p : Space) {B : ℝ} (hp : ‖p‖ < B) (hc : FormAvoids ψ (ball y B)) :
    Integrable (fun g : SpatialRotation => coreCoulombAt ψ (y+rotate g p)) rotationMeasure := by
  apply integrable_finsetSum
  intro s _
  apply integrable_finsetSum
  intro i _
  exact (rotation_core_kernel_integrable hψ y p hp hc s i).integral_prod_left

theorem rotation_core_newton {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y p : Space) {B : ℝ} (hp : ‖p‖ < B) (hc : FormAvoids ψ (ball y B)) :
    (∫ g : SpatialRotation, coreCoulombAt ψ (y+rotate g p) ∂rotationMeasure) =
      coreCoulombAt ψ y := by
  unfold coreCoulombAt
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro s _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_integral_swap (rotation_core_kernel_integrable hψ y p hp hc s i)]
      apply integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hz : ψ.value s x = 0
      · simp only [hz,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_div,integral_zero]
      · have hd : B ≤ ‖x i-y‖ := by
          by_contra hh
          exact hz (hc x i (mem_ball.mpr (not_le.mp hh)) s).1
        have he : ∀ g : SpatialRotation, x i-(y+rotate g p) = (x i-y)-rotate g p := by
          intro g; abel
        simp_rw [he,div_eq_mul_inv,integral_const_mul]
        have hn := rotation_kernel_newton p (x i-y) (hp.trans_le hd)
        simpa only [one_div] using congrArg (fun a => ‖ψ.value s x‖^2*a) hn
    · intro i _
      exact (rotation_core_kernel_integrable hψ y p hp hc s i).integral_prod_left
  · intro s _
    apply integrable_finsetSum
    intro i _
    exact (rotation_core_kernel_integrable hψ y p hp hc s i).integral_prod_left

lemma rotation_nuclear_newton (y p : Space) (hp : ‖p‖ < ‖y‖) :
    (∫ g : SpatialRotation, 1/‖y+rotate g p‖ ∂rotationMeasure) = 1/‖y‖ := by
  have hh := rotation_kernel_newton p (-y) (by simpa only [norm_neg] using hp)
  have he (g : SpatialRotation) : ‖-y-rotate g p‖ = ‖y+rotate g p‖ := by
    rw [show -y-rotate g p = -(y+rotate g p) by abel,norm_neg]
  simpa only [he,norm_neg] using hh


open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators


lemma rotatedScreened_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) (p : ℕ → Space) {B : ℝ} (hc : FormAvoids ψ (ball y B)) (k : ℕ)
    (hp : ∀ i < k, ‖p i‖ < B) (hn : ∀ i < k, ‖p i‖ < ‖y‖) (Z : ℝ) :
    Integrable (fun g : SpatialRotation => packetScreenedSum ψ Z (rotatedCenters y p g) k)
      rotationMeasure := by
  apply integrable_finsetSum
  intro i hi
  have hik := Finset.mem_range.mp hi
  have hh := ((rotation_nuclear_integrable y (p i) (hn i hik)).const_mul (Z*formMass ψ)).sub
    (rotation_core_integrable hψ y (p i) (hp i hik) hc)
  change Integrable (fun g : SpatialRotation => (Z*formMass ψ)*(1/‖y+rotate g (p i)‖) -
    coreCoulombAt ψ (y+rotate g (p i))) rotationMeasure at hh
  simpa only [mul_one_div,rotatedCenters] using hh

lemma rotatedScreened_average {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) (p : ℕ → Space) {B : ℝ} (hc : FormAvoids ψ (ball y B)) (k : ℕ)
    (hp : ∀ i < k, ‖p i‖ < B) (hn : ∀ i < k, ‖p i‖ < ‖y‖) (Z : ℝ) :
    (∫ g : SpatialRotation, packetScreenedSum ψ Z (rotatedCenters y p g) k ∂rotationMeasure) =
      (k:ℝ)*(Z*formMass ψ/‖y‖-coreCoulombAt ψ y) := by
  unfold packetScreenedSum
  rw [integral_finsetSum]
  · have he (i : ℕ) (hi : i ∈ Finset.range k) :
        (∫ g : SpatialRotation, (Z*formMass ψ/‖rotatedCenters y p g i‖ -
          coreCoulombAt ψ (rotatedCenters y p g i)) ∂rotationMeasure) =
          Z*formMass ψ/‖y‖-coreCoulombAt ψ y := by
      have hik := Finset.mem_range.mp hi
      have h1 : Integrable (fun g : SpatialRotation => Z*formMass ψ/‖rotatedCenters y p g i‖)
          rotationMeasure := by
        simpa only [mul_one_div,rotatedCenters] using
          (rotation_nuclear_integrable y (p i) (hn i hik)).const_mul (Z*formMass ψ)
      have h2 : Integrable (fun g : SpatialRotation => coreCoulombAt ψ (rotatedCenters y p g i))
          rotationMeasure := rotation_core_integrable hψ y (p i) (hp i hik) hc
      rw [integral_sub h1 h2]
      rw [show (fun g : SpatialRotation => Z*formMass ψ/‖rotatedCenters y p g i‖) =
        (fun g : SpatialRotation => (Z*formMass ψ)*(1/‖y+rotate g (p i)‖)) by
          funext g; simp only [rotatedCenters,mul_one_div],integral_const_mul,
        rotation_nuclear_newton y (p i) (hn i hik),mul_one_div]
      simp only [rotatedCenters]
      rw [rotation_core_newton hψ y (p i) (hp i hik) hc]
    rw [Finset.sum_congr rfl he]
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  · intro i hi
    have hik := Finset.mem_range.mp hi
    have hh := ((rotation_nuclear_integrable y (p i) (hn i hik)).const_mul (Z*formMass ψ)).sub
      (rotation_core_integrable hψ y (p i) (hp i hik) hc)
    change Integrable (fun g : SpatialRotation => (Z*formMass ψ)*(1/‖y+rotate g (p i)‖) -
      coreCoulombAt ψ (y+rotate g (p i))) rotationMeasure at hh
    simpa only [mul_one_div,rotatedCenters] using hh

theorem averaged_many_packet_screening {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (y : Space) (p : ℕ → Space) {B r : ℝ} (hr : 0 < r) (k : ℕ)
    (hc : FormAvoids ψ (ball y B)) (hp : ∀ i < k, ‖p i‖+2*r ≤ B)
    (hsep : ∀ i j, i < j → j < k → 3*r ≤ ‖p i-p j‖)
    (hn : ∀ i < k, ‖p i‖+r < ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    (k:ℝ)*(Z*formMass ψ/‖y‖-coreCoulombAt ψ y) ≤
      (formEnergy Z ψ + lam*N*formMass ψ - priceEnergy (energy Z) lam*formMass ψ) +
      formMass ψ * ((k:ℝ)*(radialPacketKinetic/r^2+lam) + packetPairEnergy p k) := by
  have hp' : ∀ i < k, ‖p i‖ < B := fun i hi => by have := hp i hi; linarith
  have hn' : ∀ i < k, ‖p i‖ < ‖y‖ := fun i hi => by have := hn i hi; linarith
  have hbound (g : SpatialRotation) := many_packet_screening hψ (rotatedCenters y p g) hr k
    (fun i hi => rotatedCenters_avoids y p g hc (hp i hi))
    (fun i j hij hj => by rw [rotatedCenters_distance]; exact hsep i j hij hj)
    (fun i hi => rotatedCenters_nuclear y p g (hn i hi)) hZ hlam
  simp_rw [rotatedCenters_pair] at hbound
  have hh := integral_mono
    (rotatedScreened_integrable hψ.sobolevVector y p hc k hp' hn' Z)
    (integrable_const _) hbound
  rw [rotatedScreened_average hψ.sobolevVector y p hc k hp' hn' Z] at hh
  simpa only [integral_const,probReal_univ,one_smul] using hh


open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_GridPacketRadius
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
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
namespace CoulombAtom

def packetKineticConstant : ℝ := 400*radialPacketKinetic

lemma packetKineticConstant_nonneg : 0 ≤ packetKineticConstant := by
  unfold packetKineticConstant
  exact mul_nonneg (by norm_num) radialPacketKinetic_nonneg

lemma packetRepulsionConstant_nonneg : 0 ≤ packetRepulsionConstant := by
  unfold packetRepulsionConstant
  positivity [packetDensityConstant_pos,unitCoulombIntegral_nonneg]

lemma packetGrid_repulsion {B : ℝ} (hB : 0 < B) {n : ℕ} (hn : 0 < n) :
    packetPairEnergy (packetGrid n (gridPacketRadius B n)) (n^3) ≤
      packetRepulsionConstant*(n:ℝ)^6/B := by
  let r := gridPacketRadius B n
  have hr : 0 < r := gridPacketRadius_pos hB hn
  have hrB : r ≤ B := by have := gridPacketRadius_le hB hn; dsimp [r]; linarith
  have hp (i : ℕ) (_hi : i < n^3) : ‖packetGrid n r i‖ ≤ B := by
    have := packetGrid_ball hB hn i
    dsimp only [r]
    linarith
  have hb := packetPairEnergy_bound (packetGrid n r) hr hB.le (n^3)
    (packetGrid_separated n hr) hp
  have hs : (2*B+2*r)^2 ≤ 16*B^2 := by nlinarith
  have hn' : (n:ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  calc
    _ ≤ (n^3:ℕ)*(packetDensityConstant/r^3*(2*B+2*r)^2*unitCoulombIntegral) := hb
    _ ≤ (n^3:ℕ)*(packetDensityConstant/r^3*(16*B^2)*unitCoulombIntegral) := by
      gcongr
      exact unitCoulombIntegral_nonneg
      exact div_nonneg packetDensityConstant_pos.le (pow_nonneg hr.le _)
    _ = _ := by
      dsimp [r,gridPacketRadius,packetRepulsionConstant]
      push_cast
      field_simp
      ring

theorem grid_packet_screening {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (y : Space) {B : ℝ} (hB : 0 < B) (hnuc : B ≤ ‖y‖)
    (hc : FormAvoids ψ (ball y B)) {n : ℕ} (hn : 0 < n)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    (n:ℝ)^3*(Z*formMass ψ/‖y‖-coreCoulombAt ψ y-lam*formMass ψ) ≤
      (formEnergy Z ψ + lam*N*formMass ψ-priceEnergy (energy Z) lam*formMass ψ) +
      formMass ψ*(packetKineticConstant*(n:ℝ)^5/B^2+packetRepulsionConstant*(n:ℝ)^6/B) := by
  let r := gridPacketRadius B n
  have hr : 0 < r := gridPacketRadius_pos hB hn
  have hrB : r ≤ B/20 := gridPacketRadius_le hB hn
  have hp (i : ℕ) (_hi : i < n^3) : ‖packetGrid n r i‖+2*r ≤ B := by
    have := packetGrid_ball hB hn i
    dsimp only [r] at *
    linarith
  have hnp (i : ℕ) (_hi : i < n^3) : ‖packetGrid n r i‖+r < ‖y‖ := by
    have := packetGrid_ball hB hn i
    dsimp only [r] at *
    linarith
  have hh := averaged_many_packet_screening hψ y (packetGrid n r) hr (n^3) hc hp
    (packetGrid_separated n hr) hnp hZ hlam
  have hpair := packetGrid_repulsion hB hn
  have hm := formMass_nonneg ψ
  have hh' := mul_le_mul_of_nonneg_left hpair hm
  have he : (n:ℝ)^3*(radialPacketKinetic/r^2) = packetKineticConstant*(n:ℝ)^5/B^2 := by
    dsimp [r,gridPacketRadius,packetKineticConstant]
    field_simp
    ring
  push_cast at hh hh'
  simp only [r] at hh hh' he
  nlinarith

end CoulombAtom

open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_PacketFieldConstant
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
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
namespace CoulombAtom

def packetFieldConstant : ℝ := 1+9*packetKineticConstant+8*packetRepulsionConstant

lemma packetFieldConstant_pos : 0 < packetFieldConstant := by
  dsimp [packetFieldConstant]
  have := packetKineticConstant_nonneg
  have := packetRepulsionConstant_nonneg
  linarith

end CoulombAtom

open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CorePriceExcess
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
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

lemma corePriceExcess_nonneg {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) : 0 ≤ corePriceExcess Z lam ψ :=
  sub_nonneg.mpr (hψ.priced_lower_bound hZ hlam)

theorem vacant_core_field_cap {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (hm : 0 < formMass ψ) (y : Space) {B : ℝ} (hB : 0 < B) (hnuc : B ≤ ‖y‖)
    (hc : FormAvoids ψ (ball y B)) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    normalizedCoreField Z lam ψ y ≤ packetFieldConstant *
      (1/B^4+1/B+Real.sqrt (corePriceExcess Z lam ψ/(formMass ψ*B))) := by
  have hδ := corePriceExcess_nonneg hψ hZ hlam
  have hgrid (n : ℕ) (hn : 0 < n) :
      (n:ℝ)^3*normalizedCoreField Z lam ψ y ≤ corePriceExcess Z lam ψ/formMass ψ+
        packetKineticConstant*(n:ℝ)^5/B^2+packetRepulsionConstant*(n:ℝ)^6/B := by
    have hh := grid_packet_screening hψ y hB hnuc hc hn hZ hlam
    have he :
        (corePriceExcess Z lam ψ + formMass ψ*(packetKineticConstant*(n:ℝ)^5/B^2+
          packetRepulsionConstant*(n:ℝ)^6/B))/formMass ψ =
        corePriceExcess Z lam ψ/formMass ψ+
          packetKineticConstant*(n:ℝ)^5/B^2+packetRepulsionConstant*(n:ℝ)^6/B := by
      field_simp
      ring
    rw [← he]
    apply (le_div_iff₀ hm).mpr
    unfold normalizedCoreField
    have he' :
        ((n:ℝ)^3*((Z*formMass ψ/‖y‖-coreCoulombAt ψ y)/formMass ψ-lam))*formMass ψ =
        (n:ℝ)^3*(Z*formMass ψ/‖y‖-coreCoulombAt ψ y-lam*formMass ψ) := by field_simp
    rw [he']
    exact hh
  have hh := field_cap_of_grid_bounds hB (div_nonneg hδ hm.le)
    packetKineticConstant_nonneg packetRepulsionConstant_nonneg hgrid
  simpa only [packetFieldConstant,div_div] using hh


open MeasureTheory Filter Set Metric
open scoped Topology BigOperators


def coreCapEnvelope {N : ℕ} (Z lam B : ℝ) (ψ : FormVector N) : ℝ :=
  packetFieldConstant*(1/B^4+1/B+
    Real.sqrt (corePriceExcess Z lam ψ/(formMass ψ*B)))

lemma coreCapEnvelope_nonneg {N : ℕ} (Z lam : ℝ) {B : ℝ} (hB : 0 < B)
    (ψ : FormVector N) : 0 ≤ coreCapEnvelope Z lam B ψ := by
  unfold coreCapEnvelope
  have := packetFieldConstant_pos
  positivity

lemma vacant_core_field_cap_all_mass {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {B : ℝ} (hB : 0 < B) (hnuc : B ≤ ‖y‖)
    (hc : FormAvoids ψ (ball y B)) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    normalizedCoreField Z lam ψ y ≤ coreCapEnvelope Z lam B ψ := by
  by_cases hm : 0 < formMass ψ
  · exact vacant_core_field_cap hψ hm y hB hnuc hc hZ hlam
  · have hm0 : formMass ψ = 0 := le_antisymm (not_lt.mp hm) (formMass_nonneg ψ)
    have hh := coreCapEnvelope_nonneg Z lam hB ψ
    simp only [normalizedCoreField,hm0,div_zero,zero_sub]
    linarith

theorem vacant_core_uniform_field_cap {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {B : ℝ} (hB : 0 < B) (hnuc : 2*B ≤ ‖y‖)
    (hc : FormAvoids ψ (ball y (2*B))) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    ∀ z ∈ closedBall y B, normalizedCoreField Z lam ψ z ≤ coreCapEnvelope Z lam B ψ := by
  intro z hz
  have hzy : ‖z-y‖ ≤ B := mem_closedBall.mp hz
  have hnorm : B ≤ ‖z‖ := by
    have hh := norm_add_le (y-z) z
    rw [sub_add_cancel, norm_sub_rev y z] at hh
    linarith
  apply vacant_core_field_cap_all_mass hψ z hB hnorm _ hZ hlam
  apply hc.mono
  intro x hx
  apply mem_ball.mpr
  change ‖x-y‖ < 2*B
  have hh := norm_add_le (x-z) (z-y)
  rw [sub_add_sub_cancel] at hh
  have hx' : ‖x-z‖ < B := mem_ball.mp hx
  linarith

lemma coreCapEnvelope_weighted_square {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) {Z lam B : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) (hB : 0 < B) :
    formMass ψ*(coreCapEnvelope Z lam B ψ)^2 ≤
      2*packetFieldConstant^2*((1/B^4+1/B)^2*formMass ψ+corePriceExcess Z lam ψ/B) := by
  have hm := formMass_nonneg ψ
  have hδ := corePriceExcess_nonneg hψ hZ hlam
  by_cases hm0 : formMass ψ = 0
  · rw [hm0,zero_mul,mul_zero,zero_add]
    positivity
  have hmp : 0 < formMass ψ := lt_of_le_of_ne hm (Ne.symm hm0)
  let a := 1/B^4+1/B
  let s := Real.sqrt (corePriceExcess Z lam ψ/(formMass ψ*B))
  have hs2 : s^2 = corePriceExcess Z lam ψ/(formMass ψ*B) :=
    Real.sq_sqrt (div_nonneg hδ (mul_nonneg hm hB.le))
  have hbound : (a+s)^2 ≤ 2*(a^2+s^2) := by nlinarith [sq_nonneg (a-s)]
  have hh := mul_le_mul_of_nonneg_left hbound (mul_nonneg hm (sq_nonneg packetFieldConstant))
  have he : formMass ψ*packetFieldConstant^2*(2*(a^2+s^2)) =
      2*packetFieldConstant^2*(a^2*formMass ψ+corePriceExcess Z lam ψ/B) := by
    rw [hs2]
    field_simp
  rw [he] at hh
  dsimp only [coreCapEnvelope]
  dsimp only [a,s] at hh
  nlinarith only [hh]

lemma SobolevVector.coreSlice_excess_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z lam : ℝ) (t : Spins M) :
    Integrable (fun y => corePriceExcess Z lam (coreSlice ψ t y)) :=
  ((hψ.coreSlice_energy_integrable Z t).add
    ((hψ.coreSlice_mass_integrable t).const_mul _)).sub
      ((hψ.coreSlice_mass_integrable t).const_mul _)

lemma SobolevVector.coreSlice_envelope_measurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z lam B : ℝ) (t : Spins M) :
    AEStronglyMeasurable (fun y => coreCapEnvelope Z lam B (coreSlice ψ t y)) := by
  have hm := (hψ.coreSlice_mass_integrable t).aestronglyMeasurable
  have hδ := (hψ.coreSlice_excess_integrable Z lam t).aestronglyMeasurable
  exact ((aestronglyMeasurable_const.add aestronglyMeasurable_const).add
    ((hδ.aemeasurable.div (hm.aemeasurable.mul_const B)).sqrt.aestronglyMeasurable)).const_mul _

lemma coreSlice_envelope_square_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (ha : CoreAntisymmetric ψ) (hψ : SobolevVector ψ) {Z lam B : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hB : 0 < B) (t : Spins M) :
    Integrable (fun y => formMass (coreSlice ψ t y)*
      (coreCapEnvelope Z lam B (coreSlice ψ t y))^2) := by
  have hi := (((hψ.coreSlice_mass_integrable t).const_mul ((1/B^4+1/B)^2)).add
    ((hψ.coreSlice_excess_integrable Z lam t).div_const B)).const_mul (2*packetFieldConstant^2)
  apply hi.mono' ((hψ.coreSlice_mass_integrable t).aestronglyMeasurable.mul
    ((hψ.coreSlice_envelope_measurable Z lam B t).pow 2))
  apply (ha.ae_coreSlice hψ t).mono
  intro y hy
  simp only [Pi.mul_apply,Pi.pow_apply,Pi.add_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (formMass_nonneg _) (sq_nonneg _))]
  exact coreCapEnvelope_weighted_square hy hZ hlam hB

theorem integrated_core_envelope_square {N M : ℕ} {ψ : FormVector (N+M)}
    (ha : CoreAntisymmetric ψ) (hψ : SobolevVector ψ) {Z lam B : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hB : 0 < B) :
    (∑ t : Spins M, ∫ y, formMass (coreSlice ψ t y)*
      (coreCapEnvelope Z lam B (coreSlice ψ t y))^2) ≤
      2*packetFieldConstant^2*((1/B^4+1/B)^2*formMass ψ+
        ((∑ t : Spins M, ∫ y, formEnergy Z (coreSlice ψ t y))+
          lam*N*formMass ψ-priceEnergy (energy Z) lam*formMass ψ)/B) := by
  have hti (t : Spins M) := coreSlice_envelope_square_integrable ha hψ hZ hlam hB t
  have hbound (t : Spins M) :
      (∫ y, formMass (coreSlice ψ t y)*(coreCapEnvelope Z lam B (coreSlice ψ t y))^2) ≤
      ∫ y, 2*packetFieldConstant^2*((1/B^4+1/B)^2*formMass (coreSlice ψ t y)+
        corePriceExcess Z lam (coreSlice ψ t y)/B) := by
    apply integral_mono_ae (hti t)
      ((((hψ.coreSlice_mass_integrable t).const_mul _).add
        ((hψ.coreSlice_excess_integrable Z lam t).div_const B)).const_mul _)
    exact (ha.ae_coreSlice hψ t).mono fun _ hy => coreCapEnvelope_weighted_square hy hZ hlam hB
  have hh := Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset (Spins M))) => hbound t)
  have he (t : Spins M) : (∫ y, corePriceExcess Z lam (coreSlice ψ t y)) =
      (∫ y, formEnergy Z (coreSlice ψ t y))+lam*N*(∫ y, formMass (coreSlice ψ t y))-
        priceEnergy (energy Z) lam*(∫ y, formMass (coreSlice ψ t y)) := by
    simp only [corePriceExcess]
    rw [integral_sub,integral_add,integral_const_mul,integral_const_mul]
    · exact hψ.coreSlice_energy_integrable Z t
    · exact (hψ.coreSlice_mass_integrable t).const_mul (lam*N)
    · exact (hψ.coreSlice_energy_integrable Z t).add
        ((hψ.coreSlice_mass_integrable t).const_mul (lam*N))
    · exact (hψ.coreSlice_mass_integrable t).const_mul (priceEnergy (energy Z) lam)
  have he' (t : Spins M) :
      (∫ y, 2*packetFieldConstant^2*((1/B^4+1/B)^2*formMass (coreSlice ψ t y)+
        corePriceExcess Z lam (coreSlice ψ t y)/B)) =
      2*packetFieldConstant^2*((1/B^4+1/B)^2*(∫ y, formMass (coreSlice ψ t y))+
        ((∫ y, formEnergy Z (coreSlice ψ t y))+lam*N*(∫ y, formMass (coreSlice ψ t y))-
          priceEnergy (energy Z) lam*(∫ y, formMass (coreSlice ψ t y)))/B) := by
    rw [integral_const_mul,integral_add ((hψ.coreSlice_mass_integrable t).const_mul _)
      ((hψ.coreSlice_excess_integrable Z lam t).div_const B),integral_const_mul,integral_div,he]
  simp_rw [he'] at hh
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_div,← Finset.mul_sum,
    hψ.integral_coreSlice_mass] at hh
  exact hh


open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_ConditionalFieldIdentity
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
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

lemma coreCoulombAt_mass_zero {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (hm : formMass ψ = 0) (y : Space) : coreCoulombAt ψ y = 0 := by
  have hz (s : Spins N) : (∫ x, ‖ψ.value s x‖^2) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => integral_nonneg fun x => sq_nonneg _)).mp hm s
      (Finset.mem_univ _)
  unfold coreCoulombAt
  apply Finset.sum_eq_zero
  intro s _
  apply Finset.sum_eq_zero
  intro i _
  have he := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _)
    (hψ.1 s).norm.integrable_sq).mp (hz s)
  calc
    _ = ∫ _x : Configuration N, (0:ℝ) := integral_congr_ae (he.mono fun x hx => by simp only [hx,Pi.zero_apply,zero_div])
    _ = 0 := integral_zero _ _

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SmearRepulsion
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma smearPair_le_point {η : Space → ℝ} (hm : Measurable η) (hn : ∀ x, 0 ≤ η x)
    {R B : ℝ} (hR : 0 ≤ R) (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : ∀ x, η x ≤ B)
    (hr : CoulombAnalysis.IsRadial η) (h1 : ∫ x : Space, η x = 1)
    {a b : Space} (hab : a ≠ b) : smearPair η a b ≤ 1/‖a-b‖ := by
  have haB : ∀ x, |η x| ≤ B := fun x => by rw [abs_of_nonneg (hn x)]; exact hb x
  have hsupport : Function.support η ⊆ closedBall 0 R :=
    fun x hx => by simpa only [mem_closedBall,dist_zero_right] using hs x hx
  have hi := bounded_compact_integrable hm (isCompact_closedBall _ _) hsupport haB
  have hp := bounded_compact_memLp hm (isCompact_closedBall _ _) hsupport haB (5/3 : ENNReal)
  rw [smearPair,coulomb_double_eq_potential (smearPair_integrable hm hs haB a b)]
  calc
    _ ≤ ∫ x : Space, translatedDensity η a x/‖b-x‖ := by
      apply integral_mono_ae (coulomb_potential_pair_integrable (smearPair_integrable hm hs haB a b))
        (translated_pole_integrable hi hp b a)
      filter_upwards [ae_ne_point b] with x hx
      rw [potential_translatedDensity]
      have hh := radial_potential_le_point hi hp hn hr hR hs (sub_ne_zero.mpr hx)
      rw [h1] at hh
      simpa only [translatedDensity,mul_one_div,norm_sub_rev b x] using mul_le_mul_of_nonneg_left hh (hn (x-a))
    _ = CoulombAnalysis.tfPotential η (b-a) := integral_translated_pole η b a
    _ ≤ 1/‖a-b‖ := by
      have hh := radial_potential_le_point hi hp hn hr hR hs (sub_ne_zero.mpr hab.symm)
      simpa only [h1,norm_sub_rev b a] using hh

theorem retained_coulomb_lower_self {n : ℕ} {η : Space → ℝ} (hm : Measurable η)
    (hn : ∀ x, 0 ≤ η x) {R B : ℝ} (hR : 0 ≤ R)
    (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : ∀ x, η x ≤ B)
    (hr : CoulombAnalysis.IsRadial η) (h1 : ∫ x : Space, η x = 1)
    (y : Fin n → Space) (hy : Function.Injective y) :
    (1/2:ℝ)*(∫ r : Space × Space, finiteSmear η y r.1*finiteSmear η y r.2/‖r.1-r.2‖) -
      (n:ℝ)*(1/2:ℝ)*smearPair η 0 0 ≤
      ∑ i : Fin n, ∑ j : Fin n, if i < j then 1/‖y i-y j‖ else 0 := by
  have haB : ∀ x, |η x| ≤ B := fun x => by rw [abs_of_nonneg (hn x)]; exact hb x
  rw [finiteSmear_direct η y hm hs haB]
  have he (i j : Fin n) : smearPair η (y i) (y j) ≤
      (if i=j then smearPair η 0 0 else 0) + (if i ≠ j then 1/‖y i-y j‖ else 0) := by
    by_cases hij : i=j
    · subst j
      simp only [ne_eq,not_true_eq_false,ite_false,add_zero]
      exact (smearPair_self hm hs haB (y i)).le
    · simp only [ite_eq_right hij,ite_eq_left hij,zero_add]
      exact smearPair_le_point hm hn hR hs hb hr h1 (fun hh => hij (hy hh))
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => he i j))
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  rw [sum_ordered_pairs (fun i j : Fin n => 1/‖y i-y j‖) (fun i j => by rw [norm_sub_rev])] at hh
  linarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_RetainedRepulsion
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

theorem retained_coulomb_lower {n : ℕ} {η : Space → ℝ} (hm : Measurable η)
    (hn : ∀ x, 0 ≤ η x) {R b : ℝ} (hR : 0 ≤ R)
    (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : 0 < b) (hB : ∀ x, η x ≤ b⁻¹^3)
    (hr : CoulombAnalysis.IsRadial η) (h1 : ∫ x : Space, η x = 1)
    (y : Fin n → Space) (hy : Function.Injective y) :
    (1/2:ℝ)*(∫ r : Space × Space, finiteSmear η y r.1*finiteSmear η y r.2/‖r.1-r.2‖) -
      ((2*Real.pi+1)/2)*(n:ℝ)/b ≤
      ∑ i : Fin n, ∑ j : Fin n, if i < j then 1/‖y i-y j‖ else 0 := by
  have hlo := retained_coulomb_lower_self hm hn hR hs hB hr h1 y hy
  have hh := mul_le_mul_of_nonneg_left (smearPair_self_bound hm hn hs hb hB h1)
    (show 0 ≤ (n:ℝ)*(1/2:ℝ) by positivity)
  calc
    _ ≤ (1/2:ℝ)*(∫ r : Space × Space, finiteSmear η y r.1*finiteSmear η y r.2/‖r.1-r.2‖) -
      (n:ℝ)*(1/2:ℝ)*smearPair η 0 0 := by
      have he : ((2*Real.pi+1)/2)*(n:ℝ)/b = (n:ℝ)*(1/2:ℝ)*((2*Real.pi+1)/b) := by ring
      rw [he]
      exact sub_le_sub_left hh _
    _ ≤ _ := hlo

open MeasureTheory Filter Set Metric
open scoped BigOperators

theorem selected_coulomb_lower {n k : ℕ} {η : Space → ℝ} (hm : Measurable η)
    (hn : ∀ x, 0 ≤ η x) {R b : ℝ} (hR : 0 ≤ R)
    (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : 0 < b) (hB : ∀ x, η x ≤ b⁻¹^3)
    (hr : CoulombAnalysis.IsRadial η) (h1 : ∫ x : Space, η x = 1)
    (x : Fin n → Space) (hx : Function.Injective x) (e : Fin k ↪ Fin n) :
    (1/2:ℝ)*(∫ r : Space × Space, finiteSmear η (x ∘ e) r.1 *
      finiteSmear η (x ∘ e) r.2/‖r.1-r.2‖) - ((2*Real.pi+1)/2)*(n:ℝ)/b ≤
      ∑ i : Fin n, ∑ j : Fin n, if i < j then 1/‖x i-x j‖ else 0 := by
  have hkn : k ≤ n := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective
  have hkn' : (k:ℝ) ≤ (n:ℝ) := by exact_mod_cast hkn
  have he : ((2*Real.pi+1)/2)*(k:ℝ)/b ≤ ((2*Real.pi+1)/2)*(n:ℝ)/b :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hkn' (by positivity)) hb.le
  exact (sub_le_sub_left he _).trans ((retained_coulomb_lower hm hn hR hs hb hB hr h1
    (x ∘ e) (hx.comp e.injective)).trans (retained_pair_sum_le x e))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_RetainedSmear
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombNeumann
open CoulombAtom
variable {N : ℕ}

theorem retained_physical_coulomb_lower {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (hx : Function.Injective x) :
    (1/2:ℝ)*(∫ r : Space × Space, retainedSmear b S x r.1*retainedSmear b S x r.2/‖r.1-r.2‖)-
      ((2*Real.pi+1)/2)*(N:ℝ)/b ≤
        ∑ i : Fin N, ∑ j : Fin N, if i < j then 1/‖x i-x j‖ else 0 := by
  have h := selected_coulomb_lower (varthetaScaled_measurable b) (varthetaScaled_nonneg hb)
    (show 0 ≤ Real.sqrt 3*b by positivity) (varthetaScaled_support_bound hb) hb
    (varthetaScaled_le hb) (fun _ _ h => varthetaScaled_radial b h) (integral_varthetaScaled hb)
    x hx (S.orderEmbOfFin rfl).toEmbedding
  simpa only [finiteSmear_retention] using h

theorem ae_retained_physical_coulomb_lower {b : ℝ} (hb : 0 < b)
    (S : Configuration N → Finset (Fin N)) :
    ∀ᵐ x : Configuration N,
      (1/2:ℝ)*(∫ r : Space × Space, retainedSmear b (S x) x r.1*retainedSmear b (S x) x r.2/‖r.1-r.2‖)-
        ((2*Real.pi+1)/2)*(N:ℝ)/b ≤
          ∑ i : Fin N, ∑ j : Fin N, if i < j then 1/‖x i-x j‖ else 0 := by
  filter_upwards [configuration_ae_nonsingular N] with x hx
  exact retained_physical_coulomb_lower hb (S x) x hx.2

end CoulombNeumann

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombNeumann
open CoulombAtom
variable {N : ℕ}

lemma pointRepulsion_value_integrable {ψ : FormVector N} (hψ : SobolevFermion ψ) (s : Spins N) :
    Integrable (fun x => pointRepulsion x*‖ψ.value s x‖^2) := by
  simp_rw [pointRepulsion_mul]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  split_ifs with hij
  · exact hψ.sobolevVector.pair_integrable s i j (ne_of_lt hij)
  · exact integrable_zero _ _ _

lemma integral_pointRepulsion_value {ψ : FormVector N} (hψ : SobolevFermion ψ) (s : Spins N) :
    (∫ x, pointRepulsion x*‖ψ.value s x‖^2) =
      ∑ i : Fin N, ∑ j : Fin N, if i < j then ∫ x, ‖ψ.value s x‖^2/‖x i-x j‖ else 0 := by
  simp_rw [pointRepulsion_mul]
  have hi (i j : Fin N) : Integrable (fun x => if i < j then ‖ψ.value s x‖^2/‖x i-x j‖ else 0) := by
    split_ifs with hij
    · exact hψ.sobolevVector.pair_integrable s i j (ne_of_lt hij)
    · exact integrable_zero _ _ _
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

lemma retainedDirect_value_integrable {ψ : FormVector N} (hψ : SobolevFermion ψ)
    {b : ℝ} (hb : 0 < b) (S : Configuration N → Finset (Fin N))
    (hS : ∀ i, MeasurableSet {x | i ∈ S x}) (s : Spins N) :
    Integrable (fun x => retainedDirect b (S x) x*‖ψ.value s x‖^2) := by
  have hc := ((hψ.1 s).norm.integrable_sq.const_mul (((2*Real.pi+1)/2)*(N:ℝ)/b))
  apply ((pointRepulsion_value_integrable hψ s).add hc).mono'
    ((retainedDirect_measurable b S hS).aestronglyMeasurable.mul ((hψ.1 s).aestronglyMeasurable.norm.pow 2))
  filter_upwards [ae_retained_physical_coulomb_lower hb S] with x hx
  change ‖retainedDirect b (S x) x*‖ψ.value s x‖^2‖ ≤
    pointRepulsion x*‖ψ.value s x‖^2+(((2*Real.pi+1)/2)*(N:ℝ)/b)*‖ψ.value s x‖^2
  rw [Real.norm_of_nonneg (mul_nonneg (retainedDirect_nonneg hb _ _) (sq_nonneg _)), ←add_mul]
  exact mul_le_mul_of_nonneg_right (by change retainedDirect b (S x) x-_ ≤ pointRepulsion x at hx; linarith) (sq_nonneg _)

end CoulombNeumann
namespace CoulombAtom
open CoulombNeumann
variable {N : ℕ}

theorem SobolevFermion.retained_repulsion {ψ : FormVector N} (hψ : SobolevFermion ψ)
    {b : ℝ} (hb : 0 < b) (S : Spins N → Configuration N → Finset (Fin N))
    (hS : ∀ s i, MeasurableSet {x | i ∈ S s x}) :
    (∑ s, ∫ x, retainedDirect b (S s x) x*‖ψ.value s x‖^2) ≤
      formRepulsion ψ+(((2*Real.pi+1)/2)*(N:ℝ)/b)*formMass ψ := by
  have hs (s : Spins N) :
      (∫ x, retainedDirect b (S s x) x*‖ψ.value s x‖^2) ≤
      (∫ x, pointRepulsion x*‖ψ.value s x‖^2)+
        (((2*Real.pi+1)/2)*(N:ℝ)/b)*(∫ x, ‖ψ.value s x‖^2) := by
    rw [←integral_const_mul,←integral_add (pointRepulsion_value_integrable hψ s)
      ((hψ.1 s).norm.integrable_sq.const_mul _)]
    apply integral_mono_ae (retainedDirect_value_integrable hψ hb (S s) (hS s) s)
      ((pointRepulsion_value_integrable hψ s).add ((hψ.1 s).norm.integrable_sq.const_mul _))
    filter_upwards [ae_retained_physical_coulomb_lower hb (S s)] with x hx
    change retainedDirect b (S s x) x*‖ψ.value s x‖^2 ≤
      pointRepulsion x*‖ψ.value s x‖^2+(((2*Real.pi+1)/2)*(N:ℝ)/b)*‖ψ.value s x‖^2
    rw [←add_mul]
    exact mul_le_mul_of_nonneg_right
      (by change retainedDirect b (S s x) x-_ ≤ pointRepulsion x at hx; linarith) (sq_nonneg _)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hs s)
  simpa only [Finset.sum_add_distrib,←Finset.mul_sum,integral_pointRepulsion_value hψ,formRepulsion,formMass] using hh

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ArraySymmetry
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

namespace CoulombAtom
open CoulombObservation

def quantumEventLikelihood {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) (s : Set (J × (Fin N × Fin 3) → ℝ)) (x : Configuration N) : ℝ :=
  arrayLikelihood b s (flattenConfiguration N x)

lemma quantumEventLikelihood_le_one {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (x : Configuration N) : quantumEventLikelihood b s x ≤ 1 :=
  arrayLikelihood_le_one b hs _

lemma quantumEventLikelihood_symmetric {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (hsy : QuantumEventSymmetric s) (π : Equiv.Perm (Fin N)) (x : Configuration N) :
    quantumEventLikelihood b s (x ∘ π) = quantumEventLikelihood b s x := by
  have he : flattenConfiguration N (x ∘ π) =
      flattenConfiguration N x ∘ (π.prodCongr (Equiv.refl (Fin 3))) := by
    ext ⟨i,a⟩
    rfl
  unfold quantumEventLikelihood
  rw [he]
  exact arrayLikelihood_reindex b hs _ (hsy π) _

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_RotationTrace
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

open CoulombAtom
variable {N : ℕ}

lemma flatInsertion_apply (i : Fin N) (v : Space) (q : Fin N × Fin 3) :
    flatInsertion i v q = if q.1=i then v q.2 else 0 := by
  change ((Pi.single i v : Configuration N) q.1) q.2 = _
  by_cases h : q.1=i <;> simp [h]

lemma flatInsertion_basis (i : Fin N) (a : Fin 3) :
    flatInsertion i ((EuclideanSpace.basisFun (Fin 3) ℝ) a) = Pi.single (i,a) 1 := by
  ext q
  rcases q with ⟨j,c⟩
  simp only [flatInsertion_apply,EuclideanSpace.basisFun_apply]
  by_cases hi : j=i
  · subst j
    simp [Pi.single_apply]
  · simp [hi,Prod.mk.injEq]

lemma flatRotation_insertion (R : Space ≃ₗᵢ[ℝ] Space) (i : Fin N) (v : Space) :
    flatRotation R (flatInsertion i v) = flatInsertion i (R v) := by
  ext q
  rw [flatRotation_apply,flatInsertion_apply]
  by_cases h : q.1=i
  · simp only [flatInsertion_apply,h,ite_true]
  · simp only [flatInsertion_apply,h,ite_false]
    change R 0 q.2 = _
    simp

lemma flatRotation_trace (R : Space ≃ₗᵢ[ℝ] Space)
    (L : ((Fin N × Fin 3) → ℝ) →L[ℝ] ℂ) :
    (∑ q, ‖L (flatRotation R (Pi.single q 1))‖^2) = ∑ q, ‖L (Pi.single q 1)‖^2 := by
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [←flatInsertion_basis,flatRotation_insertion]
  exact sum_norm_sq_basis_isometry (EuclideanSpace.basisFun (Fin 3) ℝ)
    Complex.orthonormalBasisOneI R (L.comp (flatInsertion i))

lemma flatRotation_kinetic {f : ((Fin N × Fin 3) → ℝ) → ℂ} (hf : ContDiff ℝ 1 f)
    (hg : ∀ q, MemLp (fun x => fderiv ℝ f x (Pi.single q 1)) 2)
    (R : Space ≃ₗᵢ[ℝ] Space) :
    (∑ q, ∫ x, ‖fderiv ℝ (fun y => f (flatRotation R y)) x (Pi.single q 1)‖^2) =
       ∑ q, ∫ x, ‖fderiv ℝ f x (Pi.single q 1)‖^2 := by
  rw [←integral_finsetSum _ (fun q _ => (flatRotation_gradient_memLp hf hg R q).norm.integrable_sq),
    ←integral_finsetSum _ (fun q _ => (hg q).norm.integrable_sq)]
  simp_rw [flatRotation_fderiv hf,flatRotation_trace]
  exact (flatRotation_preserving (N := N) R).integral_comp (flatRotation (N := N) R).toHomeomorph.measurableEmbedding (fun x => ∑ q, ‖fderiv ℝ f x (Pi.single q 1)‖^2)

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_PressureWeak
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

open CoulombAtom
variable {N : ℕ}

lemma rotatedGridPressure_nonneg (b : ℝ) (t : Fin 3 → ℝ) (R : Space ≃ₗᵢ[ℝ] Space)
    (x : (Fin N × Fin 3) → ℝ) : 0 ≤ rotatedGridPressure b t R x := gridPressure_nonneg _ _ _

lemma rotatedGridPressure_bound (b : ℝ) (t : Fin 3 → ℝ) (R : Space ≃ₗᵢ[ℝ] Space)
    (x : (Fin N × Fin 3) → ℝ) :
    rotatedGridPressure b t R x ≤ b⁻¹^2*(N:ℝ)^(5/3:ℝ) := gridPressure_bound _ _ _

lemma rotatedGridPressure_measurable (b : ℝ) (t : Fin 3 → ℝ) (R : Space ≃ₗᵢ[ℝ] Space) :
    Measurable (rotatedGridPressure (N := N) b t R) :=
  (gridPressure_measurable b t).comp (flatRotation R).symm.continuous.measurable

lemma rotatedGridPressure_integrable {f : ((Fin N × Fin 3) → ℝ) → ℂ} (hf : MemLp f 2)
    (b : ℝ) (t : Fin 3 → ℝ) (R : Space ≃ₗᵢ[ℝ] Space) :
    Integrable (fun x => rotatedGridPressure b t R x*‖f x‖^2) := by
  apply hf.norm.integrable_sq.bdd_mul (rotatedGridPressure_measurable b t R).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (rotatedGridPressure_nonneg b t R x)]
    exact rotatedGridPressure_bound b t R x)

theorem neumann_rotated_smooth_component
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, ContDiff ℝ 1 (f s)) (ha : FlatAntisymmetric f)
    (hm : ∀ s, MemLp (f s) 2)
    (hg : ∀ s q, MemLp (fun x => fderiv ℝ (f s) x (Pi.single q 1)) 2)
    {b : ℝ} (hb : 0 < b) (t : Fin 3 → ℝ) (R : Space ≃ₗᵢ[ℝ] Space) (s : Fin N → Fin 2) :
    tfKinetic*(∫ x, rotatedGridPressure b t R x*‖f s x‖^2) ≤
      (1/2:ℝ)*(∑ q, ∫ x, ‖fderiv ℝ (f s) x (Pi.single q 1)‖^2) +
        b⁻¹^2*neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))*(∫ x, ‖f s x‖^2) := by
  have hh := neumann_affine_smooth_component
    (fun s => (hf s).comp (flatRotation R).contDiff) (flatRotation_anti ha R)
    (fun s => (hm s).comp_measurePreserving (flatRotation_preserving R))
    (fun s q => flatRotation_gradient_memLp (hf s) (hg s) R q) hb t s
  have he : (∫ x, gridPressure b t x*‖f s (flatRotation R x)‖^2) =
      ∫ x, rotatedGridPressure b t R x*‖f s x‖^2 := by
    have h := (flatRotation_preserving (N := N) R).integral_comp
      (flatRotation (N := N) R).toHomeomorph.measurableEmbedding
      (fun x => rotatedGridPressure b t R x*‖f s x‖^2)
    simpa only [rotatedGridPressure,ContinuousLinearEquiv.symm_apply_apply] using h
  have hem := (flatRotation_preserving (N := N) R).integral_comp
    (flatRotation (N := N) R).toHomeomorph.measurableEmbedding (fun x => ‖f s x‖^2)
  simp only [Function.comp_def] at hh
  rw [he,hem,flatRotation_kinetic (hf s) (hg s)] at hh
  exact hh

theorem neumann_rotated_weak
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    {g : (Fin N → Fin 2) → (Fin N × Fin 3) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hm : ∀ s, MemLp (f s) 2) (hg : ∀ s q, MemLp (g s q) 2)
    (ha : FlatAEAntisymmetric f)
    (hw : ∀ s q (φ : ((Fin N × Fin 3) → ℝ) → ℝ),
      ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, f s x*Complex.ofReal (lineDeriv ℝ φ x (Pi.single q 1))) =
        -(∫ x, g s q x*(φ x:ℂ)))
    {b : ℝ} (hb : 0 < b) (t : Fin 3 → ℝ) (R : Space ≃ₗᵢ[ℝ] Space) :
    tfKinetic*(∑ s, ∫ x, rotatedGridPressure b t R x*‖f s x‖^2) ≤
      (1/2:ℝ)*(∑ s, ∑ q, ∫ x, ‖g s q x‖^2) +
        b⁻¹^2*neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))*(∑ s, ∫ x, ‖f s x‖^2) := by
  apply pressure_weak_of_smooth (rotatedGridPressure b t R) (rotatedGridPressure_nonneg b t R)
    (fun hv => rotatedGridPressure_integrable hv b t R)
    (mul_nonneg (mul_nonneg (sq_nonneg _) neumannRemainderConstant_pos.le) (by positivity))
    (fun hu hau hmu hgu s => neumann_rotated_smooth_component hu hau hmu hgu hb t R s) hm hg ha hw

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_PhysicalGrid
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombNeumann.cubePartition_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators unitInterval ContDiff

namespace CoulombNeumann
open CoulombAtom
variable {N : ℕ}

lemma flatRotation_symm_coordinates (R : Space ≃ₗᵢ[ℝ] Space) (x : Configuration N) :
    (flatRotation R).symm (configurationCoordinates N x) =
      configurationCoordinates N (fun i => R.symm (x i)) := by
  apply (flatRotation R).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  ext q
  change x q.1 q.2 = R (R.symm (x q.1)) q.2
  rw [LinearIsometryEquiv.apply_symm_apply]

lemma physicalGridPressure_eq {b : ℝ} (hb : 0 < b) (R : CubeRotation)
    (t : Fin 3 → I) (x : Configuration N) :
    physicalGridPressure b R t x =
      rotatedGridPressure b (fun a => b*(t a:ℝ)) (rotationIsometry R) (configurationCoordinates N x) := by
  unfold physicalGridPressure rotatedGridPressure gridPressure
  rw [flatRotation_symm_coordinates]
  congr 1
  congr 1
  funext i a
  change ⌊(rotationIsometry R⁻¹ (b⁻¹ • x i)) a-(t a:ℝ)⌋ =
    ⌊b⁻¹*((rotationIsometry R).symm (x i) a-b*(t a:ℝ))⌋
  rw [rotationIsometry_inv,map_smul]
  congr 1
  change b⁻¹*((rotationIsometry R).symm (x i) a)-(t a:ℝ) = _
  field_simp [hb.ne']

lemma physicalGridPressure_value_integrable {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (b : ℝ) (R : CubeRotation) (t : Fin 3 → I) (s : Spins N) :
    Integrable (fun x => physicalGridPressure b R t x*‖ψ.value s x‖^2) := by
  apply (hψ.1 s).norm.integrable_sq.bdd_mul (physicalGridPressure_fixed_measurable b R t).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    change ‖physicalGridPressure b R t x‖ ≤ b⁻¹^2*(N:ℝ)^(5/3:ℝ)
    rw [Real.norm_of_nonneg (physicalGridPressure_nonneg _ _ _ _)]
    exact physicalGridPressure_le _ _ _ _)

end CoulombNeumann
namespace CoulombAtom
open CoulombNeumann
variable {N : ℕ}

lemma formDensity_nonneg (ψ : FormVector N) (x : Configuration N) : 0 ≤ formDensity ψ x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem SobolevFermion.neumann_physical_grid {ψ : FormVector N} (hψ : SobolevFermion ψ)
    {b : ℝ} (hb : 0 < b) (R : CubeRotation) (t : Fin 3 → I) :
    tfKinetic*(∫ x, physicalGridPressure b R t x*formDensity ψ x) ≤ formKinetic ψ+
      b⁻¹^2*neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))*formMass ψ := by
  have hm (s : Spins N) : MemLp (cartesianValue ψ s) 2 :=
    (hψ.1 s).comp_measurePreserving (configurationCoordinates_symm_preserving N)
  have hg (s : Spins N) (q : Fin N × Fin 3) : MemLp (cartesianGradient ψ s q) 2 :=
    (hψ.2.1 s q.1 q.2).comp_measurePreserving (configurationCoordinates_symm_preserving N)
  have hh := neumann_rotated_weak hm hg hψ.cartesian_anti hψ.cartesian_weak hb
    (fun a => b*(t a:ℝ)) (rotationIsometry R)
  have he (s : Spins N) :
      (∫ x, rotatedGridPressure b (fun a => b*(t a:ℝ)) (rotationIsometry R) x*‖cartesianValue ψ s x‖^2) =
        ∫ x : Configuration N, physicalGridPressure b R t x*‖ψ.value s x‖^2 := by
    rw [←integral_configurationCoordinates (fun x => rotatedGridPressure b (fun a => b*(t a:ℝ)) (rotationIsometry R) x*‖cartesianValue ψ s x‖^2)]
    simp only [cartesianValue,ContinuousLinearEquiv.symm_apply_apply,←physicalGridPressure_eq hb]
  have heg (s : Spins N) (q : Fin N × Fin 3) :
      (∫ x, ‖cartesianGradient ψ s q x‖^2) = ∫ x, ‖ψ.gradient s q.1 q.2 x‖^2 :=
    integral_configurationCoordinates_symm (fun x => ‖ψ.gradient s q.1 q.2 x‖^2)
  have hem (s : Spins N) : (∫ x, ‖cartesianValue ψ s x‖^2) = ∫ x, ‖ψ.value s x‖^2 :=
    integral_configurationCoordinates_symm (fun x => ‖ψ.value s x‖^2)
  simp_rw [he,heg,hem] at hh
  unfold formDensity
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun s _ => physicalGridPressure_value_integrable hψ b R t s)]
  simpa only [Fintype.sum_prod_type,formKinetic,formMass] using hh

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_WeightedAverage
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter

open MeasureTheory Set Filter
open scoped BigOperators unitInterval

namespace CoulombNeumann
open CoulombAtom
variable {N : ℕ}

lemma physicalGridPressure_partition_integrable (b : ℝ) (x : Configuration N) :
    Integrable (fun p : CubePartition => physicalGridPressure b p.1 p.2 x) cubePartitionMeasure := by
  have hh := bounded_average_section_integrable (μ := cubePartitionMeasure)
    (P := fun (p : CubePartition) (y : Configuration N) => physicalGridPressure b p.1 p.2 y)
    (physicalGridPressure_measurable (N := N) b)
    (fun p y => physicalGridPressure_nonneg b p.1 p.2 y)
    (fun p y => physicalGridPressure_le b p.1 p.2 y) x
  exact hh

lemma physicalPressureAverage_partition (b : ℝ) (x : Configuration N) :
    physicalPressureAverage b x = ∫ p : CubePartition, physicalGridPressure b p.1 p.2 x ∂cubePartitionMeasure := by
  rw [cubePartitionMeasure,integral_prod _ (physicalGridPressure_partition_integrable b x)]
  unfold physicalGridPressure
  simp only [integral_const_mul]
  rfl

lemma physicalPressureAverage_value_integrable {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (b : ℝ) : Integrable (fun x => physicalPressureAverage b x*formDensity ψ x) := by
  apply hψ.formDensity_integrable.bdd_mul (physicalPressureAverage_measurable b).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (physicalPressureAverage_nonneg _ _)]
    exact physicalPressureAverage_le _ _

lemma physicalPressure_value_integrable {ψ : FormVector N} (hψ : SobolevFermion ψ)
    {b : ℝ} (hb : 0 < b) : Integrable (fun x => physicalPressure b x*formDensity ψ x) := by
  apply hψ.formDensity_integrable.bdd_mul (physicalPressure_measurable b).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (physicalPressure_nonneg hb x)]
    exact (physicalPressure_le_average hb x).trans (physicalPressureAverage_le b x)

end CoulombNeumann
namespace CoulombAtom
open CoulombNeumann
variable {N : ℕ}

theorem SobolevFermion.neumann_averaged_pressure {ψ : FormVector N} (hψ : SobolevFermion ψ)
    {b : ℝ} (hb : 0 < b) :
    tfKinetic*(∫ x, physicalPressureAverage b x*formDensity ψ x) ≤ formKinetic ψ+
      b⁻¹^2*neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))*formMass ψ := by
  simp_rw [physicalPressureAverage_partition]
  exact weighted_average_bound (μ := cubePartitionMeasure)
    (P := fun (p : CubePartition) (y : Configuration N) => physicalGridPressure b p.1 p.2 y)
    (physicalGridPressure_measurable (N := N) b)
    (fun p x => physicalGridPressure_nonneg b p.1 p.2 x)
    (fun p x => physicalGridPressure_le b p.1 p.2 x)
    hψ.formDensity_integrable (fun p => hψ.neumann_physical_grid hb p.1 p.2)

theorem SobolevFermion.neumann_radial_smear {ψ : FormVector N} (hψ : SobolevFermion ψ)
    {b : ℝ} (hb : 0 < b) :
    tfKinetic*(∫ x, physicalPressure b x*formDensity ψ x) ≤ formKinetic ψ+
      b⁻¹^2*neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))*formMass ψ := by
  apply le_trans _ (hψ.neumann_averaged_pressure hb)
  apply mul_le_mul_of_nonneg_left _ (by unfold tfKinetic; positivity)
  exact integral_mono (physicalPressure_value_integrable hψ hb) (physicalPressureAverage_value_integrable hψ b)
    (fun x => mul_le_mul_of_nonneg_right (physicalPressure_le_average hb x) (formDensity_nonneg ψ x))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_RetainedKineticLower
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

namespace CoulombNeumann
open CoulombAtom
variable {N : ℕ}

lemma retainedPressure_value_integrable {ψ : FormVector N} (hψ : SobolevFermion ψ)
    {b : ℝ} (hb : 0 < b) (S : Configuration N → Finset (Fin N))
    (hS : ∀ i, MeasurableSet {x | i ∈ S x}) (s : Spins N) :
    Integrable (fun x => retainedPressure b (S x) x*‖ψ.value s x‖^2) := by
  apply (hψ.1 s).norm.integrable_sq.bdd_mul
    (retainedPressure_measurable b S hS).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    change ‖retainedPressure b (S x) x‖ ≤ b⁻¹^2*(N:ℝ)^(5/3:ℝ)
    rw [Real.norm_of_nonneg (retainedPressure_nonneg hb _ _)]
    exact (retainedPressure_le_average hb _ _).trans (physicalPressureAverage_le b x))

lemma physicalPressure_spin_integrable {ψ : FormVector N} (hψ : SobolevFermion ψ)
    {b : ℝ} (hb : 0 < b) (s : Spins N) :
    Integrable (fun x => physicalPressure b x*‖ψ.value s x‖^2) := by
  apply (hψ.1 s).norm.integrable_sq.bdd_mul (physicalPressure_measurable b).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    change ‖physicalPressure b x‖ ≤ b⁻¹^2*(N:ℝ)^(5/3:ℝ)
    rw [Real.norm_of_nonneg (physicalPressure_nonneg hb _)]
    exact (physicalPressure_le_average hb _).trans (physicalPressureAverage_le b x))

end CoulombNeumann
namespace CoulombAtom
open CoulombNeumann
variable {N : ℕ}

theorem SobolevFermion.neumann_retained {ψ : FormVector N} (hψ : SobolevFermion ψ)
    {b : ℝ} (hb : 0 < b) (S : Spins N → Configuration N → Finset (Fin N))
    (hS : ∀ s i, MeasurableSet {x | i ∈ S s x}) :
    tfKinetic*(∑ s, ∫ x, retainedPressure b (S s x) x*‖ψ.value s x‖^2) ≤ formKinetic ψ+
      b⁻¹^2*neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))*formMass ψ := by
  apply le_trans _ (hψ.neumann_radial_smear hb)
  apply mul_le_mul_of_nonneg_left _ (by unfold tfKinetic; positivity)
  unfold formDensity
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun s _ => physicalPressure_spin_integrable hψ hb s)]
  apply Finset.sum_le_sum
  intro s _
  exact integral_mono (retainedPressure_value_integrable hψ hb (S s) (hS s) s)
    (physicalPressure_spin_integrable hψ hb s)
    (fun x => mul_le_mul_of_nonneg_right (retainedPressure_le_full hb _ _) (sq_nonneg _))

end CoulombAtom

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombNeumann
open CoulombAtom
variable {N M : ℕ}

lemma retained_slice_pressure_integrable {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    {b : ℝ} (hb : 0 < b) (S : Configuration N × Configuration M → Finset (Fin N))
    (hS : ∀ i, MeasurableSet {p | i ∈ S p}) (s : Spins N) (t : Spins M) :
    Integrable (fun y => ∫ x, retainedPressure b (S (x,y)) x*‖(coreSlice ψ t y).value s x‖^2) := by
  have hi := integrable_join (N := N) (M := M) (hψ.1 (joinLists s t)).norm.integrable_sq
  have hm := retainedPressure_measurable_param b S Prod.fst hS measurable_fst
  have hh : Integrable (fun p : Configuration N × Configuration M =>
      retainedPressure b (S p) p.1*‖ψ.value (joinLists s t) (joinLists p.1 p.2)‖^2) := by
    apply hi.bdd_mul hm.aestronglyMeasurable
    exact Eventually.of_forall (fun p => by
      change ‖retainedPressure b (S p) p.1‖ ≤ b⁻¹^2*(N:ℝ)^(5/3:ℝ)
      rw [Real.norm_of_nonneg (retainedPressure_nonneg hb _ _)]
      exact (retainedPressure_le_average hb _ _).trans (physicalPressureAverage_le b p.1))
  exact hh.integral_prod_right

lemma retained_slice_pressure_sum_integrable {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    {b : ℝ} (hb : 0 < b) (S : Spins N → Configuration N × Configuration M → Finset (Fin N))
    (hS : ∀ s i, MeasurableSet {p | i ∈ S s p}) (t : Spins M) :
    Integrable (fun y => ∑ s, ∫ x, retainedPressure b (S s (x,y)) x*‖(coreSlice ψ t y).value s x‖^2) :=
  integrable_finsetSum _ (fun s _ => retained_slice_pressure_integrable hψ hb (S s) (hS s) s t)

lemma retained_section_measurable (S : Configuration N × Configuration M → Finset (Fin N))
    (hS : ∀ i, MeasurableSet {p | i ∈ S p}) (y : Configuration M) (i : Fin N) :
    MeasurableSet {x | i ∈ S (x,y)} :=
  (measurable_id.prodMk measurable_const) (hS i)

end CoulombNeumann
namespace CoulombAtom
open CoulombNeumann
variable {N M : ℕ}

theorem CoreAntisymmetric.neumann_retained_slices {ψ : FormVector (N+M)}
    (ha : CoreAntisymmetric ψ) (hψ : SobolevVector ψ) {b : ℝ} (hb : 0 < b)
    (S : Spins M → Spins N → Configuration N × Configuration M → Finset (Fin N))
    (hS : ∀ t s i, MeasurableSet {p | i ∈ S t s p}) :
    tfKinetic*(∑ t : Spins M, ∫ y, ∑ s, ∫ x,
      retainedPressure b (S t s (x,y)) x*‖(coreSlice ψ t y).value s x‖^2) ≤
      coreKinetic ψ+b⁻¹^2*neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))*formMass ψ := by
  have ht (t : Spins M) :
      tfKinetic*(∫ y, ∑ s, ∫ x, retainedPressure b (S t s (x,y)) x*
        ‖(coreSlice ψ t y).value s x‖^2) ≤
      (∫ y, formKinetic (coreSlice ψ t y))+
        b⁻¹^2*neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))*(∫ y, formMass (coreSlice ψ t y)) := by
    rw [←integral_const_mul,←integral_const_mul,
      ←integral_add (coreSlice_parts_integrable hψ t).1 ((hψ.coreSlice_mass_integrable t).const_mul _)]
    apply integral_mono_ae ((retained_slice_pressure_sum_integrable hψ hb (S t) (hS t) t).const_mul _)
      ((coreSlice_parts_integrable hψ t).1.add ((hψ.coreSlice_mass_integrable t).const_mul _))
    filter_upwards [ha.ae_coreSlice hψ t] with y hy
    exact hy.neumann_retained hb (fun s x => S t s (x,y))
      (fun s i => retained_section_measurable (S t s) (hS t s) y i)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun t _ => ht t)
  simpa only [Finset.sum_add_distrib,←Finset.mul_sum,integral_core_kinetic hψ,
    hψ.integral_coreSlice_mass] using hh

end CoulombAtom

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombNeumann
open CoulombAtom
variable {N M : ℕ}

lemma pointRepulsion_join_integrable {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    (s : Spins N) (t : Spins M) :
    Integrable (fun p : Configuration N × Configuration M =>
      pointRepulsion p.1*‖ψ.value (joinLists s t) (joinLists p.1 p.2)‖^2) := by
  simp_rw [pointRepulsion_mul]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  split_ifs with hij
  · have hne : (finSumFinEquiv (Sum.inl i) : Fin (N+M)) ≠ finSumFinEquiv (Sum.inl j) :=
      fun hh => (ne_of_lt hij) (Sum.inl.inj (finSumFinEquiv.injective hh))
    have hh := integrable_join (N := N) (M := M)
      (hψ.pair_integrable (joinLists s t) _ _ hne)
    simpa only [joinLists_left] using hh
  · exact integrable_zero _ _ _

lemma retained_slice_direct_integrable {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    {b : ℝ} (hb : 0 < b) (S : Configuration N × Configuration M → Finset (Fin N))
    (hS : ∀ i, MeasurableSet {p | i ∈ S p}) (s : Spins N) (t : Spins M) :
    Integrable (fun y => ∫ x, retainedDirect b (S (x,y)) x*‖(coreSlice ψ t y).value s x‖^2) := by
  have hi := integrable_join (N := N) (M := M) (hψ.1 (joinLists s t)).norm.integrable_sq
  have hm := retainedDirect_measurable_param b S Prod.fst hS measurable_fst
  have hh : Integrable (fun p : Configuration N × Configuration M =>
      retainedDirect b (S p) p.1*‖ψ.value (joinLists s t) (joinLists p.1 p.2)‖^2) := by
    apply ((pointRepulsion_join_integrable hψ s t).add
      (hi.const_mul (((2*Real.pi+1)/2)*(N:ℝ)/b))).mono'
      (hm.aestronglyMeasurable.mul hi.aestronglyMeasurable)
    have hn : ∀ᵐ p : Configuration N × Configuration M, Function.Injective p.1 := by
      rw [Measure.volume_eq_prod]
      exact Measure.quasiMeasurePreserving_fst.ae ((configuration_ae_nonsingular N).mono (fun _ h => h.2))
    filter_upwards [hn] with p hp
    change ‖retainedDirect b (S p) p.1*‖ψ.value (joinLists s t) (joinLists p.1 p.2)‖^2‖ ≤
      pointRepulsion p.1*‖ψ.value (joinLists s t) (joinLists p.1 p.2)‖^2+
        (((2*Real.pi+1)/2)*(N:ℝ)/b)*‖ψ.value (joinLists s t) (joinLists p.1 p.2)‖^2
    rw [Real.norm_of_nonneg (mul_nonneg (retainedDirect_nonneg hb _ _) (sq_nonneg _)),←add_mul]
    have hh := retained_physical_coulomb_lower hb (S p) p.1 hp
    change retainedDirect b (S p) p.1-_ ≤ pointRepulsion p.1 at hh
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  exact hh.integral_prod_right

lemma retained_slice_direct_sum_integrable {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    {b : ℝ} (hb : 0 < b) (S : Spins N → Configuration N × Configuration M → Finset (Fin N))
    (hS : ∀ s i, MeasurableSet {p | i ∈ S s p}) (t : Spins M) :
    Integrable (fun y => ∑ s, ∫ x, retainedDirect b (S s (x,y)) x*‖(coreSlice ψ t y).value s x‖^2) :=
  integrable_finsetSum _ (fun s _ => retained_slice_direct_integrable hψ hb (S s) (hS s) s t)

end CoulombNeumann
namespace CoulombAtom
open CoulombNeumann
variable {N M : ℕ}

theorem CoreAntisymmetric.retained_repulsion_slices {ψ : FormVector (N+M)}
    (ha : CoreAntisymmetric ψ) (hψ : SobolevVector ψ) {b : ℝ} (hb : 0 < b)
    (S : Spins M → Spins N → Configuration N × Configuration M → Finset (Fin N))
    (hS : ∀ t s i, MeasurableSet {p | i ∈ S t s p}) :
    (∑ t : Spins M, ∫ y, ∑ s, ∫ x,
      retainedDirect b (S t s (x,y)) x*‖(coreSlice ψ t y).value s x‖^2) ≤
      coreRepulsion ψ+(((2*Real.pi+1)/2)*(N:ℝ)/b)*formMass ψ := by
  have ht (t : Spins M) :
      (∫ y, ∑ s, ∫ x, retainedDirect b (S t s (x,y)) x*
        ‖(coreSlice ψ t y).value s x‖^2) ≤
      (∫ y, formRepulsion (coreSlice ψ t y))+
        (((2*Real.pi+1)/2)*(N:ℝ)/b)*(∫ y, formMass (coreSlice ψ t y)) := by
    rw [←integral_const_mul,
      ←integral_add (coreSlice_parts_integrable hψ t).2.2 ((hψ.coreSlice_mass_integrable t).const_mul _)]
    apply integral_mono_ae (retained_slice_direct_sum_integrable hψ hb (S t) (hS t) t)
      ((coreSlice_parts_integrable hψ t).2.2.add ((hψ.coreSlice_mass_integrable t).const_mul _))
    filter_upwards [ha.ae_coreSlice hψ t] with y hy
    exact hy.retained_repulsion hb (fun s x => S t s (x,y))
      (fun s i => retained_section_measurable (S t s) (hS t s) y i)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun t _ => ht t)
  simpa only [Finset.sum_add_distrib,←Finset.mul_sum,integral_core_repulsion hψ,
    hψ.integral_coreSlice_mass] using hh

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_BlockSwap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators

@[simp] lemma swapBlocks_mass {N M : ℕ} (ψ : FormVector (N+M)) :
    formMass (swapBlocks ψ) = formMass ψ := formMass_reindex _ _

open MeasureTheory Filter Set
open scoped BigOperators

open CoulombNeumann

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_CoreFieldRegularity
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
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
open scoped BigOperators ENNReal

open CoulombAnalysis

lemma coreSlice_field_measurable_rep {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (Z lam : ℝ) :
    ∃ F : Configuration M × Space → ℝ, Measurable F ∧
      ∀ᵐ u : Configuration M, ∀ z : Space,
        F (u,z) = normalizedCoreField Z lam (coreSlice ψ t u) z := by
  let d : Spins N → Configuration N × Configuration M → ℝ :=
    fun s q => ‖ψ.value (joinLists s t) (joinLists q.1 q.2)‖^2
  have hd (s : Spins N) : AEStronglyMeasurable (d s) :=
    (integrable_join (N := N) (M := M) (hψ.1 (joinLists s t)).norm.integrable_sq).aestronglyMeasurable
  let v : Spins N → Configuration N × Configuration M → ℝ := fun s => (hd s).mk (d s)
  have hv (s : Spins N) : Measurable (v s) := (hd s).stronglyMeasurable_mk.measurable
  have he (s : Spins N) : ∀ᵐ u : Configuration M, ∀ᵐ x : Configuration N,
      d s (x,u) = v s (x,u) := by
    have hh : d s =ᵐ[volume] v s := (hd s).ae_eq_mk
    rw [Measure.volume_eq_prod] at hh
    exact Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hh)
  let m : Configuration M → ℝ := fun u => ∑ s : Spins N, ∫ x : Configuration N, v s (x,u)
  have hm : Measurable m := by
    apply Finset.measurable_sum
    intro s _
    exact (StronglyMeasurable.integral_prod_left (f := fun x u => v s (x,u))
      (hv s).stronglyMeasurable).measurable
  let V : Configuration M × Space → ℝ := fun q =>
    ∑ s : Spins N, ∑ i : Fin N, ∫ x : Configuration N, v s (x,q.1)/‖x i-q.2‖
  have hV : Measurable V := by
    apply Finset.measurable_sum
    intro s _
    apply Finset.measurable_sum
    intro i _
    have hh : Measurable (fun q : (Configuration M × Space) × Configuration N =>
        v s (q.2,q.1.1)/‖q.2 i-q.1.2‖) :=
      ((hv s).comp (measurable_snd.prodMk (measurable_fst.fst))).div (by fun_prop)
    exact hh.stronglyMeasurable.integral_prod_right.measurable
  refine ⟨fun q => (Z*m q.1/‖q.2‖-V q)/m q.1-lam, ?_, ?_⟩
  · exact (((measurable_const.mul (hm.comp measurable_fst)).div
      (continuous_norm.measurable.comp measurable_snd)).sub hV).div
        (hm.comp measurable_fst) |>.sub_const lam
  · filter_upwards [ae_all_iff.mpr he] with u hu
    have hm' : m u = formMass (coreSlice ψ t u) := by
      apply Finset.sum_congr rfl
      intro s _
      apply integral_congr_ae
      filter_upwards [hu s] with x hx
      exact hx.symm
    have hV' (z : Space) : V (u,z) = coreCoulombAt (coreSlice ψ t u) z := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards [hu s] with x hx
      exact congrArg (fun a : ℝ => a/‖x i-z‖) hx.symm
    intro z
    rw [hm',hV']
    rfl

def conditionalPatchField {N M : ℕ} (ψ : FormVector (N+M)) (t : Spins M)
    (Z lam : ℝ) (y : Space) (R : ℝ) (u : Configuration M) : TFField R :=
  toLpOrZero (ballMeasure R) (5/2) (fun u z => normalizedCoreField Z lam (coreSlice ψ t u) (y+z)) u

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SpatialProductFactor
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
namespace CoulombAtom

lemma multiplyForm_spatial_zero_of_factor {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x ^ 2 = 1)
    (ψ : FormVector L) (b : Fin L → Fin 2) (x : Configuration L) (j : Fin L)
    (hv : (p (b j)).value (x j) = 0)
    (hd : ∀ a, lineDeriv ℝ (p (b j)).value (x j) (spaceDirections a) = 0) :
    FormZeroAt (multiplyForm (spatialProduct p hp b) ψ) x := by
  have hval := spatialProduct_zero_of_factor p b x j hv
  have hg := spatialProduct_derivative_zero_of_factor p b x j hv hd
  intro s
  constructor
  · change (spatialProductValue p b x : ℂ) * _ = 0
    rw [hval,Complex.ofReal_zero,zero_mul]
  · intro i a
    change (spatialProductValue p b x : ℂ) * _ +
      Complex.ofReal (lineDeriv ℝ (spatialProductValue p b) x (direction i a)) * _ = 0
    rw [hval,hg,Complex.ofReal_zero,zero_mul,zero_mul,add_zero]

lemma FormZeroAt.coreSlice {N M : ℕ} {ψ : FormVector (N+M)}
    {x : Configuration N} {y : Configuration M}
    (h : FormZeroAt ψ (joinLists x y)) (t : Spins M) :
    FormZeroAt (coreSlice ψ t y) x := by
  intro s
  exact ⟨(h (joinLists s t)).1,fun i a => (h (joinLists s t)).2 (finSumFinEquiv (Sum.inl i)) a⟩

lemma orderedCutForm_core_hole {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x ^ 2 = 1)
    (ψ : FormVector L) (b : Fin L → Fin 2) (S : Set Space)
    (hv : ∀ x ∈ S, (p 0).value x = 0)
    (hd : ∀ x ∈ S, ∀ a, lineDeriv ℝ (p 0).value x (spaceDirections a) = 0)
    (x : Configuration (cutCoreNumber b + cutOutNumber b)) (i : Fin (cutCoreNumber b))
    (hi : x (finSumFinEquiv (Sum.inl i)) ∈ S) :
    FormZeroAt (orderedCutForm p hp ψ b) x := by
  let j : Fin (cutCoreNumber b + cutOutNumber b) := finSumFinEquiv (Sum.inl i)
  have hj : b (cutOrder b j) = 0 := by
    have hh := congrFun (cutOrder_labels b) j
    simpa only [Function.comp_apply,j,coreCutLabels,joinLists_left] using hh
  apply FormZeroAt.reindex
  apply multiplyForm_spatial_zero_of_factor p hp ψ b _ (cutOrder b j)
  · simpa only [Function.comp_apply,Equiv.symm_apply_apply,hj] using hv (x j) hi
  · intro a
    simpa only [Function.comp_apply,Equiv.symm_apply_apply,hj] using hd (x j) hi a

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RadialPatchGeometry
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

def coreFirstRadialCut (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) :
    Fin 2 → SmoothMultiplier spaceDirections :=
  ![radialOutside y ht hb,radialInside y ht hb]

lemma coreFirstRadialCut_partition (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (x : Space) : ∑ a, (coreFirstRadialCut y ht hb a).value x^2 = 1 := by
  simpa only [Fin.sum_univ_two,coreFirstRadialCut,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.head_cons,radialInside,radialOutside] using
    Real.sin_sq_add_cos_sq (radialPhase y t b x)

def radialPatchCore (y : Space) (t : ℝ) : Set Space := {x | t ≤ ‖x-y‖}

lemma coreFirstRadialCut_core_zero (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (x : Space) (hx : x ∉ radialPatchCore y t) :
    (coreFirstRadialCut y ht hb 0).value x = 0 := by
  have hx' : ‖x-y‖ < t := lt_of_not_ge hx
  simp only [coreFirstRadialCut,Matrix.cons_val_zero,radialOutside,
    radialPhase_zero ht hb hx'.le,Real.sin_zero]

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis CoulombNeumann

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_CutCountDomination
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

def spatialCutExpectation {N : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector N)
    (F : (Fin N → Fin 2) → Configuration N → ℝ) : ℝ :=
  ∑ c : Fin N → Fin 2, ∑ s : Spins N, ∫ x,
    F c x*‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2

lemma spatialCutExpectation_raw {N : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector N} (hψ : SobolevVector ψ)
    {g : Configuration N → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) :
    spatialCutExpectation p hp ψ (fun _ => g) = ∫ x, g x ∂formRawLaw ψ := by
  rw [formRawLaw_integral_eq_spin_sum hψ hg hB]
  unfold spatialCutExpectation
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have hi (c : Fin N → Fin 2) : Integrable (fun x =>
      g x*‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2) :=
    (((hψ.multiply _).1 s).norm.integrable_sq).bdd_mul hg.aestronglyMeasurable (ae_of_all _ hB)
  rw [←integral_finsetSum _ (fun c _ => hi c)]
  apply integral_congr_ae (ae_of_all _ _)
  intro x
  rw [←Finset.mul_sum,finite_partition_value (spatialProduct p hp) (spatial_square_partition p hp)]

lemma spatialCutExpectation_le_raw {N : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector N} (hψ : SobolevVector ψ)
    {F : (Fin N → Fin 2) → Configuration N → ℝ} {g : Configuration N → ℝ}
    (hF : ∀ c, Measurable (F c)) {A : ℝ} (hA : ∀ c x, ‖F c x‖ ≤ A)
    (hg : Measurable g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B)
    (hfg : ∀ c x, (spatialProduct p hp c).value x ≠ 0 → F c x ≤ g x) :
    spatialCutExpectation p hp ψ F ≤ ∫ x, g x ∂formRawLaw ψ := by
  rw [←spatialCutExpectation_raw p hp hψ hg hB]
  apply Finset.sum_le_sum; intro c _
  apply Finset.sum_le_sum; intro s _
  apply integral_mono
    ((((hψ.multiply _).1 s).norm.integrable_sq).bdd_mul (hF c).aestronglyMeasurable
      (ae_of_all _ (hA c)))
    ((((hψ.multiply _).1 s).norm.integrable_sq).bdd_mul hg.aestronglyMeasurable
      (ae_of_all _ hB))
  intro x
  by_cases hx : (spatialProduct p hp c).value x = 0
  · simp only [multiplyForm,hx,Complex.ofReal_zero,zero_mul,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,le_refl]
  · exact mul_le_mul_of_nonneg_right (hfg c x hx) (sq_nonneg _)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_CutOuterLaw
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

def outProjection {N M : ℕ} (x : Configuration (N+M)) : Configuration M :=
  fun i => x (finSumFinEquiv (Sum.inr i))

lemma outProjection_join {N M : ℕ} (x : Configuration N) (y : Configuration M) :
    outProjection (joinLists x y) = y := by
  funext i; exact joinLists_right x y i

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_FormRawPotential
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

def rawPotential {N : ℕ} (y : Space) (x : Configuration N) : ℝ := ∑ i, 1/‖x i-y‖

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_CorePotentialTower
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

lemma rawPotential_weighted_integrable {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (s : Spins N) (y : Space) :
    Integrable (fun x => rawPotential y x*‖ψ.value s x‖^2) := by
  simp only [rawPotential,Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  simpa only [one_div,mul_comm,←div_eq_mul_inv] using hψ.shifted_nuclear_integrable s i y

lemma integral_rawPotential_formRawLaw {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (y : Space) :
    (∫ x, rawPotential y x ∂formRawLaw ψ) = coreCoulombAt ψ y := by
  rw [formRawLaw_integral hψ]
  simp only [formRawDensity,Finset.sum_mul]
  rw [integral_finsetSum _ (fun s _ => by
    simpa only [mul_comm] using rawPotential_weighted_integrable hψ s y)]
  unfold coreCoulombAt
  congr 1
  ext s
  simp only [rawPotential,Finset.mul_sum,mul_one_div]
  exact integral_finsetSum _ (fun i _ => hψ.shifted_nuclear_integrable s i y)

lemma coreSlice_coreCoulombAt_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (y : Space) :
    Integrable (fun u : Configuration M => coreCoulombAt (coreSlice ψ t u) y) := by
  unfold coreCoulombAt
  apply integrable_finsetSum
  intro s _
  apply integrable_finsetSum
  intro i _
  have hh := (integrable_join (N := N) (M := M)
    (hψ.shifted_nuclear_integrable (joinLists s t) (finSumFinEquiv (Sum.inl i)) y)).integral_prod_right
  simpa only [coreSlice,joinLists_left] using hh

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_QuantumEventMultiplier
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

namespace CoulombAtom
open CoulombObservation

def quantumEventMultiplier {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (hsy : QuantumEventSymmetric s) (p : ℝ) : FermionLipschitzMultiplier N where
  value x := (Real.sqrt p)⁻¹ * Real.sqrt (quantumEventLikelihood b s x)
  constant := ‖(Real.sqrt p)⁻¹‖₊ *
    (sqrtLikelihoodLipschitzConstant (I := Fin N × Fin 3) b * ‖flattenConfiguration N‖₊)
  lipschitz := (lipschitzWith_smul ((Real.sqrt p)⁻¹)).comp
    ((sqrtArrayLikelihood_lipschitz b hs).comp (flattenConfiguration N).lipschitz)
  bound := ⟨(Real.sqrt p)⁻¹, fun x => by
    rw [abs_of_nonneg (by positivity)]
    calc
      _ ≤ (Real.sqrt p)⁻¹ * 1 := mul_le_mul_of_nonneg_left
        (by simpa using Real.sqrt_le_sqrt (quantumEventLikelihood_le_one b hs x))
        (by positivity)
      _ = _ := mul_one _⟩
  symmetric π x := by rw [quantumEventLikelihood_symmetric b hs hsy π x]

@[simp] lemma quantumEventMultiplier_value {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (hsy : QuantumEventSymmetric s) (p : ℝ) (x : Configuration N) :
    (quantumEventMultiplier b hs hsy p).value x =
      (Real.sqrt p)⁻¹ * Real.sqrt (quantumEventLikelihood b s x) := rfl

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_OuterFieldMaximum
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

lemma normalizedCoreField_le_nuclear {N : ℕ} (ψ : FormVector N)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (z : Space) :
    normalizedCoreField Z lam ψ z ≤ Z/‖z‖ := by
  by_cases hm : formMass ψ = 0
  · simp only [normalizedCoreField,hm,mul_zero,div_zero,zero_sub]
    exact (neg_nonpos.mpr hlam).trans (div_nonneg hZ (norm_nonneg z))
  · have hmp : 0 < formMass ψ := lt_of_le_of_ne (formMass_nonneg ψ) (Ne.symm hm)
    unfold normalizedCoreField
    rw [sub_div]
    have he : Z*formMass ψ/‖z‖/formMass ψ = Z/‖z‖ := by
      rw [mul_div_right_comm,mul_div_assoc,div_self hm,mul_one]
    rw [he]
    have hc := div_nonneg (coreCoulombAt_nonneg ψ z) hmp.le
    linarith

lemma coreFirstRadialCut_out_zero (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (z : Space) (hz : t+b ≤ ‖z-y‖) : (coreFirstRadialCut y ht hb 1).value z = 0 := by
  simp only [coreFirstRadialCut,Matrix.cons_val_one,Matrix.cons_val_zero,radialInside,
    radialPhase_pi_half ht hb hz,Real.cos_pi_div_two]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_CutMomentBounds
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

lemma orderedCutForm_mass_sum {N : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector N} (hψ : SobolevVector ψ) :
    (∑ c : Fin N → Fin 2, formMass (orderedCutForm p hp ψ c)) = formMass ψ := by
  simp_rw [orderedCutForm_mass]
  exact spatial_cut_mass p hp hψ

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PatchCenterObservable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

def conditionalPatchCenter {N M : ℕ} (ψ : FormVector (N+M)) (t : Spins M)
    (Z lam : ℝ) (y : Space) (R : ℝ) (u : Configuration M) : ℝ :=
  normalizedCoreField Z lam (coreSlice ψ t u) y-
    tfBallPotential R (tfPatchMinimizer R tfKinetic tfKinetic_pos
      (conditionalPatchField ψ t Z lam y R u)) 0

lemma normalizedCoreField_eval_aemeasurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (Z lam : ℝ) (y : Space) :
    AEMeasurable (fun u => normalizedCoreField Z lam (coreSlice ψ t u) y) := by
  obtain ⟨F,hF,he⟩ := coreSlice_field_measurable_rep hψ t Z lam
  exact ((hF.comp (measurable_id.prodMk measurable_const)).aemeasurable).congr
    (he.mono fun u hu => hu y)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_FreshFieldTower
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

lemma fresh_cut_coreCoulombAt_sum {N : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    {ψ : FormVector N} (hψ : SobolevVector ψ) (y : Space) :
    (∑ c : Fin N → Fin 2, coreCoulombAt (orderedCutForm p hp ψ c) y) = coreCoulombAt ψ y := by
  have he (c : Fin N → Fin 2) : coreCoulombAt (orderedCutForm p hp ψ c) y =
      coreCoulombAt (multiplyForm (spatialProduct p hp c) ψ) y := by
    rw [coreCoulombAt_eq_formOneBody,orderedCutForm,formOneBody_reindex,
      ←coreCoulombAt_eq_formOneBody]
  simp_rw [he,coreCoulombAt]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [←integral_finsetSum _ (fun c _ => (hψ.multiply (spatialProduct p hp c)).shifted_nuclear_integrable s i y)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [←Finset.sum_div,finite_partition_value (spatialProduct p hp) (spatial_square_partition p hp)]

end CoulombAtom

end Work_FreshFieldTower_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CutCoreExcess
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
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

def cutCoreExcess {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (Z lam : ℝ)
    (ψ : FormVector L) (b : Fin L → Fin 2) : ℝ :=
  cutCoreEnergy p hp Z ψ b+lam*cutCoreNumber b*formMass (orderedCutForm p hp ψ b)-
    priceEnergy (energy Z) lam*formMass (orderedCutForm p hp ψ b)

theorem fresh_cut_field_envelope {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (b : Fin L → Fin 2) (y : Space) {B : ℝ}
    (hB : 0 < B) (hnuc : 2*B ≤ ‖y‖)
    (hv : ∀ x ∈ ball y (2*B), (p 0).value x = 0)
    (hd : ∀ x ∈ ball y (2*B), ∀ a, lineDeriv ℝ (p 0).value x (spaceDirections a) = 0)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) (t : Spins (cutOutNumber b)) :
    ∀ᵐ u, ∀ z ∈ closedBall y B,
      normalizedCoreField Z lam (coreSlice (orderedCutForm p hp ψ b) t u) z ≤
        coreCapEnvelope Z lam B (coreSlice (orderedCutForm p hp ψ b) t u) := by
  apply ((orderedCutForm_core_antisymmetric p hp hψ b).ae_coreSlice
    (orderedCutForm_sobolev p hp hψ.sobolevVector b) t).mono
  intro u hu
  apply vacant_core_uniform_field_cap hu y hB hnuc _ hZ hlam
  intro x i hi
  exact (orderedCutForm_core_hole p hp ψ b (ball y (2*B)) hv hd (joinLists x u) i
    (by simpa only [joinLists_left] using hi)).coreSlice t

theorem fresh_cut_envelope_square {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (b : Fin L → Fin 2) {Z lam B : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hB : 0 < B) :
    (∑ t : Spins (cutOutNumber b), ∫ u,
      formMass (coreSlice (orderedCutForm p hp ψ b) t u)*
        (coreCapEnvelope Z lam B (coreSlice (orderedCutForm p hp ψ b) t u))^2) ≤
      2*packetFieldConstant^2*((1/B^4+1/B)^2*formMass (orderedCutForm p hp ψ b)+
        cutCoreExcess p hp Z lam ψ b/B) :=
  integrated_core_envelope_square (orderedCutForm_core_antisymmetric p hp hψ b)
    (orderedCutForm_sobolev p hp hψ.sobolevVector b) hZ hlam hB

theorem fock_cut_envelope_square {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevFermion ψ) {Z lam B : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hB : 0 < B) :
    (∑ b : Fin L → Fin 2, ∑ t : Spins (cutOutNumber b), ∫ u,
      formMass (coreSlice (orderedCutForm p hp ψ b) t u)*
        (coreCapEnvelope Z lam B (coreSlice (orderedCutForm p hp ψ b) t u))^2) ≤
      2*packetFieldConstant^2*((1/B^4+1/B)^2*formMass ψ+
        (∑ b : Fin L → Fin 2, cutCoreExcess p hp Z lam ψ b)/B) := by
  have hh := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin L → Fin 2))) =>
    fresh_cut_envelope_square p hp hψ b hZ hlam hB)
  simpa only [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_div,orderedCutForm_mass,
    spatial_cut_mass p hp hψ.sobolevVector] using hh

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_QuantumFieldExcessBarrier
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

lemma coreSlice_envelope_first_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (ha : CoreAntisymmetric ψ) (hψ : SobolevVector ψ) {Z lam B : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hB : 0 < B) (t : Spins M) :
    Integrable (fun u => coreCapEnvelope Z lam B (coreSlice ψ t u)*formMass (coreSlice ψ t u)) := by
  have hi := (hψ.coreSlice_mass_integrable t).add
    (coreSlice_envelope_square_integrable ha hψ hZ hlam hB t)
  apply hi.mono' ((hψ.coreSlice_envelope_measurable Z lam B t).mul
    (hψ.coreSlice_mass_integrable t).aestronglyMeasurable)
  filter_upwards [] with u
  dsimp only [Pi.mul_apply, Pi.add_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (coreCapEnvelope_nonneg Z lam hB _) (formMass_nonneg _))]
  have hh : coreCapEnvelope Z lam B (coreSlice ψ t u) ≤
      1+(coreCapEnvelope Z lam B (coreSlice ψ t u))^2 := by
    nlinarith [sq_nonneg (coreCapEnvelope Z lam B (coreSlice ψ t u)-1)]
  nlinarith [mul_le_mul_of_nonneg_right hh (formMass_nonneg (coreSlice ψ t u))]

open MeasureTheory Filter Set Metric
open scoped BigOperators

lemma fock_cut_envelope_first_le_sqrt_mass {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevFermion ψ) {Z lam B : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hB : 0 < B) :
    (∑ c : Fin L → Fin 2, ∑ t : Spins (cutOutNumber c), ∫ u,
      coreCapEnvelope Z lam B (coreSlice (orderedCutForm p hp ψ c) t u)*
        formMass (coreSlice (orderedCutForm p hp ψ c) t u)) ≤
      Real.sqrt (∑ c : Fin L → Fin 2, ∑ t : Spins (cutOutNumber c), ∫ u,
        formMass (coreSlice (orderedCutForm p hp ψ c) t u)*
          (coreCapEnvelope Z lam B (coreSlice (orderedCutForm p hp ψ c) t u))^2)*
          Real.sqrt (formMass ψ) := by
  have hh := weighted_sum_integral_cauchy
    (ι := Σ c : Fin L → Fin 2, Spins (cutOutNumber c))
    (X := fun cs => Configuration (cutOutNumber cs.1)) (fun _ => volume)
    (fun cs u => formMass (coreSlice (orderedCutForm p hp ψ cs.1) cs.2 u))
    (fun cs u => coreCapEnvelope Z lam B (coreSlice (orderedCutForm p hp ψ cs.1) cs.2 u))
    (fun _ _ => (1:ℝ)) (fun _ _ => formMass_nonneg _)
    (fun cs => by simpa only [mul_comm] using (coreSlice_envelope_square_integrable
      (orderedCutForm_core_antisymmetric p hp hψ cs.1)
      (orderedCutForm_sobolev p hp hψ.sobolevVector cs.1) hZ hlam hB cs.2))
    (fun cs => by simpa only [one_pow,one_mul] using
      (orderedCutForm_sobolev p hp hψ.sobolevVector cs.1).coreSlice_mass_integrable cs.2)
    (fun cs => by simpa only [mul_one] using (coreSlice_envelope_first_integrable
      (orderedCutForm_core_antisymmetric p hp hψ cs.1)
      (orderedCutForm_sobolev p hp hψ.sobolevVector cs.1) hZ hlam hB cs.2))
  simpa only [Fintype.sum_sigma,mul_one,one_pow,one_mul,
    SobolevVector.integral_coreSlice_mass (orderedCutForm_sobolev p hp hψ.sobolevVector _),
    orderedCutForm_mass_sum p hp hψ.sobolevVector,mul_comm] using hh

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CoreMultiplierLiftBarrier
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CoreMultiplierLift_barrier_scope

open MeasureTheory Filter
open scoped BigOperators ContDiff

lemma coreLeftLinear_apply {N M : ℕ} (x : Configuration (N+M)) :
    coreLeftLinear N M x = leftList x := by
  simp only [coreLeftLinear,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,configurationJoin_symm_apply]
  rfl

lemma coreLeftLinear_direction_left {N M : ℕ} (i : Fin N) (a : Fin 3) :
    coreLeftLinear N M (direction (finSumFinEquiv (Sum.inl i)) a) = direction i a := by
  rw [←configurationJoin_direction]
  simp only [coreLeftLinear,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply]
  rfl

lemma coreLeftLinear_direction_right {N M : ℕ} (i : Fin M) (a : Fin 3) :
    coreLeftLinear N M (direction (finSumFinEquiv (Sum.inr i)) a) = 0 := by
  rw [←configurationJoin_direction_right]
  simp only [coreLeftLinear,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply]
  rfl

def coreLiftMultiplier {N : ℕ} (M : ℕ) (p : SmoothMultiplier (sectorDirections N)) :
    SmoothMultiplier (sectorDirections (N+M)) where
  value := coreLiftValue M p
  regular := coreLiftValue_regular M p
  bound := by
    obtain ⟨C,hC⟩ := p.bound
    exact ⟨C,fun x => hC (coreLeftLinear N M x)⟩
  gradient_bound := by
    intro j
    obtain ⟨i,hi⟩ := finSumFinEquiv.surjective j.1
    cases i with
    | inl i =>
      obtain ⟨C,hC⟩ := p.gradient_bound (i,j.2)
      refine ⟨C,fun x => ?_⟩
      change |lineDeriv ℝ (coreLiftValue M p) x (direction j.1 j.2)| ≤ C
      rw [←hi,coreLiftValue_derivative,coreLeftLinear_direction_left]
      exact hC _
    | inr i =>
      refine ⟨0,fun x => ?_⟩
      change |lineDeriv ℝ (coreLiftValue M p) x (direction j.1 j.2)| ≤ 0
      rw [←hi,coreLiftValue_derivative,coreLeftLinear_direction_right]
      simp only [lineDeriv_zero,abs_zero,le_refl]

lemma coreSlice_coreLiftMultiplier {N M : ℕ} (ψ : FormVector (N+M))
    (p : SmoothMultiplier (sectorDirections N)) (t : Spins M) (y : Configuration M) :
    coreSlice (multiplyForm (coreLiftMultiplier M p) ψ) t y =
      multiplyForm p (coreSlice ψ t y) := by
  apply congrArg₂ FormVector.mk
  · funext s x
    simp only [coreSlice,multiplyForm,coreLiftMultiplier,coreLiftValue,
      Function.comp_apply,coreLeftLinear_apply,leftList_join]
  · funext s i a x
    change (coreLiftValue M p (joinLists x y) : ℂ)*_+
      Complex.ofReal (lineDeriv ℝ (coreLiftValue M p) (joinLists x y)
        (direction (finSumFinEquiv (Sum.inl i)) a))*_ = _
    rw [coreLiftValue_derivative,coreLeftLinear_direction_left,coreLeftLinear_apply,leftList_join]
    simp only [coreLiftValue,Function.comp_apply,coreLeftLinear_apply,leftList_join,
      coreSlice]

end Work_CoreMultiplierLift_barrier_scope

open MeasureTheory Filter
open scoped BigOperators

lemma coreSlice_reindex_lift {K N M : ℕ} (e : Fin K ≃ Fin N)
    (ψ : FormVector (N+M)) (s : Spins M) (u : Configuration M) :
    coreSlice (reindexForm (liftCoreOrder M e) ψ) s u =
      reindexForm e (coreSlice ψ s u) := by
  apply congrArg₂ FormVector.mk
  · funext t x
    change ψ.value _ _ = ψ.value _ _
    rw [joinLists_order,joinLists_order]
  · funext t i a x
    change ψ.gradient _ _ _ _ = ψ.gradient _ _ _ _
    rw [joinLists_order,joinLists_order,liftCoreOrder_left]

lemma CoreAntisymmetric.reindex_lift {K N M : ℕ} {ψ : FormVector (N+M)}
    (ha : CoreAntisymmetric ψ) (e : Fin K ≃ Fin N) :
    CoreAntisymmetric (reindexForm (liftCoreOrder M e) ψ) := by
  intro π s
  have hh := (configurationReindex_preserving (liftCoreOrder M e)).quasiMeasurePreserving.ae
    (ha (e.permCongr π) (s ∘ (liftCoreOrder M e).symm))
  filter_upwards [hh] with x hx
  change ψ.value ((s ∘ corePerm M π) ∘ (liftCoreOrder M e).symm)
    ((x ∘ corePerm M π) ∘ (liftCoreOrder M e).symm) = _
  rw [liftCoreOrder_perm_comp,liftCoreOrder_perm_comp]
  simpa only [configurationReindex_apply,Equiv.Perm.sign_permCongr,reindexForm] using hx

def repeatedCutForm {N M : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector (N+M)) (c : Fin N → Fin 2) :
    FormVector ((cutCoreNumber c+cutOutNumber c)+M) :=
  reindexForm (liftCoreOrder M (cutOrder c))
    (multiplyForm (coreLiftMultiplier M (spatialProduct p hp c)) ψ)

lemma repeatedCutForm_sobolev {N M : ℕ} {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2) :
    SobolevVector (repeatedCutForm p hp ψ c) := (hψ.multiply _).reindex _

lemma repeatedCutForm_slice {N M : ℕ} (ψ : FormVector (N+M))
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2)
    (s : Spins M) (u : Configuration M) :
    coreSlice (repeatedCutForm p hp ψ c) s u = orderedCutForm p hp (coreSlice ψ s u) c := by
  unfold repeatedCutForm
  rw [coreSlice_reindex_lift,coreSlice_coreLiftMultiplier]
  rfl

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_CoreHistoryCoordinatesBarrier
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma coreSlice_observation_order {N K M : ℕ} (ψ : FormVector ((N+K)+M))
    (s : Spins K) (t : Spins M) (u : Configuration K) (v : Configuration M) :
    coreSlice (reindexForm (coreObservationAssoc N K M) ψ) (joinLists s t) (joinLists u v) =
      coreSlice (coreSlice ψ t v) s u := by
  apply congrArg₂ FormVector.mk
  · funext q x
    change ψ.value _ _ = ψ.value _ _
    rw [joinLists_observation_order,joinLists_observation_order]
  · funext q i a x
    change ψ.gradient _ _ _ _ = ψ.gradient _ _ _ _
    rw [joinLists_observation_order,joinLists_observation_order,coreObservationAssoc_core]

lemma CoreAntisymmetric.observation_order {N K M : ℕ} {ψ : FormVector ((N+K)+M)}
    (ha : CoreAntisymmetric ψ) :
    CoreAntisymmetric (reindexForm (coreObservationAssoc N K M) ψ) := by
  intro π s
  have hh := (configurationReindex_preserving (coreObservationAssoc N K M)).quasiMeasurePreserving.ae
    (ha (corePerm K π) (s ∘ (coreObservationAssoc N K M).symm))
  filter_upwards [hh] with x hx
  change ψ.value ((s ∘ corePerm (K+M) π) ∘ (coreObservationAssoc N K M).symm)
    ((x ∘ corePerm (K+M) π) ∘ (coreObservationAssoc N K M).symm) = _
  rw [coreObservationAssoc_perm_comp,coreObservationAssoc_perm_comp]
  simpa only [configurationReindex_apply,corePerm_sign,reindexForm] using hx

def nextCoreObservation {N M : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector (N+M)) (c : Fin N → Fin 2) :
    FormVector (cutCoreNumber c+(cutOutNumber c+M)) :=
  reindexForm (coreObservationAssoc _ _ _) (repeatedCutForm p hp ψ c)

lemma nextCoreObservation_sobolev {N M : ℕ} {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2) :
    SobolevVector (nextCoreObservation p hp ψ c) :=
  (repeatedCutForm_sobolev hψ p hp c).reindex _

lemma nextCoreObservation_slice {N M : ℕ} (ψ : FormVector (N+M))
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2)
    (s : Spins (cutOutNumber c)) (t : Spins M)
    (u : Configuration (cutOutNumber c)) (v : Configuration M) :
    coreSlice (nextCoreObservation p hp ψ c) (joinLists s t) (joinLists u v) =
      coreSlice (orderedCutForm p hp (coreSlice ψ t v) c) s u := by
  unfold nextCoreObservation
  rw [coreSlice_observation_order,repeatedCutForm_slice]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_CoreHistoryAverageBarrier
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

def coreLawAverage {N M : ℕ} (ψ : FormVector (N+M)) (F : FormVector N → ℝ) : ℝ :=
  ∑ t : Spins M, ∫ v, F (coreSlice ψ t v)

lemma coreLawAverage_mass {N M : ℕ} {ψ : FormVector (N+M)} (hψ : SobolevVector ψ) :
    coreLawAverage ψ formMass = formMass ψ := hψ.integral_coreSlice_mass

lemma nextCoreObservation_statistic_integrable {N M : ℕ} (ψ : FormVector (N+M))
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2)
    (F : FormVector (cutCoreNumber c) → ℝ)
    (hF : ∀ s, Integrable (fun u => F (coreSlice (nextCoreObservation p hp ψ c) s u)))
    (t : Spins M) :
    Integrable (fun v => coreLawAverage (orderedCutForm p hp (coreSlice ψ t v) c) F) := by
  apply integrable_finsetSum
  intro s _
  have hi := integrable_join (hF (joinLists s t))
  simp only [nextCoreObservation_slice] at hi
  exact hi.integral_prod_right

theorem coreLawAverage_next {N M : ℕ} (ψ : FormVector (N+M))
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2)
    (F : FormVector (cutCoreNumber c) → ℝ)
    (hF : ∀ s, Integrable (fun u => F (coreSlice (nextCoreObservation p hp ψ c) s u))) :
    coreLawAverage (nextCoreObservation p hp ψ c) F =
      ∑ t : Spins M, ∫ v, coreLawAverage (orderedCutForm p hp (coreSlice ψ t v) c) F := by
  unfold coreLawAverage
  rw [←sum_spin_join]
  apply Finset.sum_congr rfl
  intro t _
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro s _
    rw [←integral_join (hF (joinLists s t))]
    simp only [nextCoreObservation_slice]
  · intro s _
    have hi := integrable_join (hF (joinLists s t))
    simp only [nextCoreObservation_slice] at hi
    exact hi.integral_prod_right

lemma coreLawAverage_next_mass {N M : ℕ} {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2) :
    formMass (nextCoreObservation p hp ψ c) =
      ∑ t : Spins M, ∫ v, formMass (orderedCutForm p hp (coreSlice ψ t v) c) := by
  rw [←coreLawAverage_mass (nextCoreObservation_sobolev hψ p hp c),
    coreLawAverage_next ψ p hp c formMass
      (fun s => (nextCoreObservation_sobolev hψ p hp c).coreSlice_mass_integrable s)]
  apply Finset.sum_congr rfl
  intro t _
  apply integral_congr_ae
  filter_upwards [hψ.ae_coreSlice t] with v hv
  exact coreLawAverage_mass (orderedCutForm_sobolev p hp hv c)

lemma nextCoreObservation_mass_statistic_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2) (t : Spins M) :
    Integrable (fun v => formMass (orderedCutForm p hp (coreSlice ψ t v) c)) := by
  apply (nextCoreObservation_statistic_integrable ψ p hp c formMass
    (fun s => (nextCoreObservation_sobolev hψ p hp c).coreSlice_mass_integrable s) t).congr
  filter_upwards [hψ.ae_coreSlice t] with v hv
  exact coreLawAverage_mass (orderedCutForm_sobolev p hp hv c)

lemma coreLawAverage_excess {N M : ℕ} {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    (Z lam : ℝ) :
    coreLawAverage ψ (corePriceExcess Z lam) =
      (∑ t : Spins M, ∫ v, formEnergy Z (coreSlice ψ t v))+
        lam*N*formMass ψ-priceEnergy (energy Z) lam*formMass ψ := by
  have he (t : Spins M) : (∫ v, corePriceExcess Z lam (coreSlice ψ t v)) =
      (∫ v, formEnergy Z (coreSlice ψ t v))+lam*N*(∫ v, formMass (coreSlice ψ t v))-
        priceEnergy (energy Z) lam*(∫ v, formMass (coreSlice ψ t v)) := by
    simp only [corePriceExcess]
    rw [integral_sub,integral_add,integral_const_mul,integral_const_mul]
    · exact hψ.coreSlice_energy_integrable Z t
    · exact (hψ.coreSlice_mass_integrable t).const_mul (lam*N)
    · exact (hψ.coreSlice_energy_integrable Z t).add
        ((hψ.coreSlice_mass_integrable t).const_mul (lam*N))
    · exact (hψ.coreSlice_mass_integrable t).const_mul (priceEnergy (energy Z) lam)
  unfold coreLawAverage
  simp_rw [he]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum,
    hψ.integral_coreSlice_mass]

lemma coreLawAverage_ordered_excess {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2) (Z lam : ℝ) :
    coreLawAverage (orderedCutForm p hp ψ c) (corePriceExcess Z lam) =
      cutCoreExcess p hp Z lam ψ c :=
  coreLawAverage_excess (orderedCutForm_sobolev p hp hψ c) Z lam

lemma nextCoreObservation_excess_statistic_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2) (t : Spins M) (Z lam : ℝ) :
    Integrable (fun v => cutCoreExcess p hp Z lam (coreSlice ψ t v) c) :=
by
  apply (nextCoreObservation_statistic_integrable ψ p hp c (corePriceExcess Z lam)
    (fun s => (nextCoreObservation_sobolev hψ p hp c).coreSlice_excess_integrable Z lam s) t).congr
  filter_upwards [hψ.ae_coreSlice t] with v hv
  exact coreLawAverage_ordered_excess hv p hp c Z lam

open MeasureTheory Filter
open scoped BigOperators

lemma rawFormPair_eq_integral {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {g : Configuration N → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) :
    rawFormPair ψ g = ∫ x, g x ∂formRawLaw ψ :=
  (formRawLaw_integral_eq_spin_sum hψ hg hB).symm

lemma rawFormPair_coreSlice_integrable {N M : ℕ} {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    {g : Configuration N → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B)
    (t : Spins M) : Integrable (fun v => rawFormPair (coreSlice ψ t v) g) := by
  apply integrable_finsetSum
  intro s _
  have hi : Integrable (fun x => g (leftList x)*‖ψ.value (joinLists s t) x‖^2) :=
    ((hψ.1 _).norm.integrable_sq).bdd_mul (hg.comp leftList_measurable).aestronglyMeasurable
      (ae_of_all _ (fun x => hB (leftList x)))
  have hj := (integrable_join (N := N) (M := M) hi).integral_prod_right
  simpa only [coreSlice,leftList_join] using hj

lemma coreLawAverage_rawFormPair {N M : ℕ} {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    {g : Configuration N → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) :
    coreLawAverage ψ (fun φ => rawFormPair φ g) = rawFormPair ψ (g ∘ leftList) := by
  have hi (s : Spins (N+M)) : Integrable (fun x => g (leftList x)*‖ψ.value s x‖^2) :=
    ((hψ.1 s).norm.integrable_sq).bdd_mul (hg.comp leftList_measurable).aestronglyMeasurable
      (ae_of_all _ (fun x => hB (leftList x)))
  have he (s : Spins N) (t : Spins M) :
      (∫ v : Configuration M, ∫ x : Configuration N,
        g x*‖(coreSlice ψ t v).value s x‖^2) =
      ∫ x, g (leftList x)*‖ψ.value (joinLists s t) x‖^2 := by
    simpa only [coreSlice,leftList_join] using integral_join (N := N) (M := M) (hi (joinLists s t))
  unfold coreLawAverage rawFormPair
  have hsum (t : Spins M) :
      (∫ v, ∑ s : Spins N, ∫ x, g x*‖(coreSlice ψ t v).value s x‖^2) =
      ∑ s : Spins N, ∫ v, ∫ x, g x*‖(coreSlice ψ t v).value s x‖^2 := by
    apply integral_finsetSum
    intro s _
    simpa only [coreSlice,leftList_join] using
      (integrable_join (N := N) (M := M) (hi (joinLists s t))).integral_prod_right
  simp_rw [hsum,he]
  exact sum_spin_join (fun s : Spins (N+M) => ∫ x, g (leftList x)*‖ψ.value s x‖^2)

lemma cutCore_rawFormPair {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L} (hψ : SobolevVector ψ)
    (c : Fin L → Fin 2) {g : Configuration (cutCoreNumber c) → ℝ} (hg : Measurable g)
    {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) :
    coreLawAverage (orderedCutForm p hp ψ c) (fun φ => rawFormPair φ g) =
      rawFormPair (multiplyForm (spatialProduct p hp c) ψ) (g ∘ cutCorePositions c) := by
  rw [coreLawAverage_rawFormPair (orderedCutForm_sobolev p hp hψ c) hg hB]
  have he (s : Spins (cutCoreNumber c+cutOutNumber c)) :
      (∫ x, g (leftList x)*‖(orderedCutForm p hp ψ c).value s x‖^2) =
      ∫ x, g (cutCorePositions c x)*‖(multiplyForm (spatialProduct p hp c) ψ).value
        (s ∘ (cutOrder c).symm) x‖^2 := by
    simpa only [orderedCutForm,reindexForm,cutCorePositions_reindex] using
      integral_reindex (cutOrder c) (fun x => g (cutCorePositions c x)*
        ‖(multiplyForm (spatialProduct p hp c) ψ).value (s ∘ (cutOrder c).symm) x‖^2)
  unfold rawFormPair
  simp only [Function.comp_apply]
  simp_rw [he]
  exact sum_spin_reindex (cutOrder c) (fun s : Spins L =>
    ∫ x, g (cutCorePositions c x)*‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CoreHistoryFermionBarrier
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma repeatedCutForm_value {N M : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector (N+M)) (c : Fin N → Fin 2)
    (s : Spins ((cutCoreNumber c+cutOutNumber c)+M)) (x) :
    (repeatedCutForm p hp ψ c).value s x =
      (spatialProductValue p (coreCutLabels (cutCoreNumber c) (cutOutNumber c)) (leftList x) : ℂ)*
        (reindexForm (liftCoreOrder M (cutOrder c)) ψ).value s x := by
  change (spatialProductValue p c (coreLeftLinear N M (x ∘ (liftCoreOrder M (cutOrder c)).symm)) : ℂ)*_ = _
  rw [coreLeftLinear_apply,leftList_liftCoreOrder,spatialProductValue_reindex,cutOrder_labels]
  rfl

lemma nextCoreObservation_value {N M : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector (N+M)) (c : Fin N → Fin 2)
    (s : Spins (cutCoreNumber c+(cutOutNumber c+M))) (x) :
    (nextCoreObservation p hp ψ c).value s x =
      (spatialProductValue p (coreCutLabels (cutCoreNumber c) (cutOutNumber c))
        (leftList (x ∘ (coreObservationAssoc _ _ _).symm)) : ℂ)*
      (reindexForm (coreObservationAssoc _ _ _)
        (reindexForm (liftCoreOrder M (cutOrder c)) ψ)).value s x := by
  exact repeatedCutForm_value p hp ψ c _ _

theorem nextCoreObservation_antisymmetric {N M : ℕ} {ψ : FormVector (N+M)}
    (ha : CoreAntisymmetric ψ) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2) :
    CoreAntisymmetric (nextCoreObservation p hp ψ c) := by
  have hh := (ha.reindex_lift (cutOrder c)).observation_order
    (N := cutCoreNumber c) (K := cutOutNumber c)
  intro π s
  filter_upwards [hh π s] with x hx
  rw [nextCoreObservation_value,nextCoreObservation_value,
    coreObservationAssoc_perm_comp,leftList_corePerm,
    spatialProduct_invariant p _ (corePerm _ π) (coreCutLabels_invariant π),hx]
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_CoreHistoryMassBarrier
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

lemma sum_nextCoreObservation_mass {N M : ℕ} {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) :
    (∑ c : Fin N → Fin 2, formMass (nextCoreObservation p hp ψ c)) = formMass ψ := by
  simp_rw [coreLawAverage_next_mass hψ p hp]
  rw [Finset.sum_comm]
  rw [←hψ.integral_coreSlice_mass]
  apply Finset.sum_congr rfl
  intro t _
  rw [←integral_finsetSum _ (fun c _ => nextCoreObservation_mass_statistic_integrable hψ p hp c t)]
  apply integral_congr_ae
  filter_upwards [hψ.ae_coreSlice t] with v hv
  simp only [orderedCutForm_mass,spatial_cut_mass p hp hv]

structure CoreObservationGraph where
  coreSize : ℕ
  outSize : ℕ
  vector : FormVector (coreSize+outSize)
  sobolev : SobolevVector vector
  antisymmetric : CoreAntisymmetric vector

namespace CoreObservationGraph

def initial {N : ℕ} (ψ : FormVector N) (hψ : SobolevFermion ψ) : CoreObservationGraph where
  coreSize := N
  outSize := 0
  vector := ψ
  sobolev := hψ.sobolevVector
  antisymmetric := hψ.coreAntisymmetric

def observe (G : CoreObservationGraph) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin G.coreSize → Fin 2) : CoreObservationGraph where
  coreSize := cutCoreNumber c
  outSize := cutOutNumber c+G.outSize
  vector := nextCoreObservation p hp G.vector c
  sobolev := nextCoreObservation_sobolev G.sobolev p hp c
  antisymmetric := nextCoreObservation_antisymmetric G.antisymmetric p hp c

def mass (G : CoreObservationGraph) : ℝ := formMass G.vector

lemma observe_mass (G : CoreObservationGraph) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) :
    (∑ c : Fin G.coreSize → Fin 2, (G.observe p hp c).mass) = G.mass :=
  sum_nextCoreObservation_mass G.sobolev p hp

end CoreObservationGraph
end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_CoreHistoryFieldBarrier
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

def coreFieldSquare {N : ℕ} (Z lam : ℝ) (y : Space) (ψ : FormVector N) : ℝ :=
  (max (normalizedCoreField Z lam ψ y) 0)^2*formMass ψ

lemma coreFieldSquare_nonneg {N : ℕ} (Z lam : ℝ) (y : Space) (ψ : FormVector N) :
    0 ≤ coreFieldSquare Z lam y ψ := mul_nonneg (sq_nonneg _) (formMass_nonneg _)

lemma coreFieldSquare_le_nuclear {N : ℕ} (ψ : FormVector N) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (y : Space) :
    coreFieldSquare Z lam y ψ ≤ (Z/‖y‖)^2*formMass ψ := by
  apply mul_le_mul_of_nonneg_right _ (formMass_nonneg _)
  exact pow_le_pow_left₀ (le_max_right _ _)
    (max_le (normalizedCoreField_le_nuclear ψ hZ hlam y) (div_nonneg hZ (norm_nonneg _))) 2

lemma coreFieldSquare_coreSlice_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (y : Space) :
    Integrable (fun u => coreFieldSquare Z lam y (coreSlice ψ s u)) := by
  apply (hψ.coreSlice_mass_integrable s).bdd_mul
    (((normalizedCoreField_eval_aemeasurable hψ s Z lam y).max aemeasurable_const).pow_const 2).aestronglyMeasurable
  apply ae_of_all
  intro u
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (le_max_right _ _)
    (max_le (normalizedCoreField_le_nuclear _ hZ hlam y) (div_nonneg hZ (norm_nonneg _))) 2

namespace CoreObservationGraph

def fieldMoment (G : CoreObservationGraph) (Z lam : ℝ) (y : Space) : ℝ :=
  coreLawAverage G.vector (coreFieldSquare Z lam y)

def excess (G : CoreObservationGraph) (Z lam : ℝ) : ℝ :=
  coreLawAverage G.vector (corePriceExcess Z lam)

lemma fieldMoment_nonneg (G : CoreObservationGraph) (Z lam : ℝ) (y : Space) :
    0 ≤ G.fieldMoment Z lam y :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => coreFieldSquare_nonneg _ _ _ _))

lemma fieldMoment_le_nuclear (G : CoreObservationGraph) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (y : Space) :
    G.fieldMoment Z lam y ≤ (Z/‖y‖)^2*G.mass := by
  rw [fieldMoment,mass,←coreLawAverage_mass G.sobolev]
  unfold coreLawAverage
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  rw [←integral_const_mul]
  exact integral_mono (coreFieldSquare_coreSlice_integrable G.sobolev t hZ hlam y)
    ((G.sobolev.coreSlice_mass_integrable t).const_mul _)
    (fun _ => coreFieldSquare_le_nuclear _ hZ hlam y)

end CoreObservationGraph
end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_CoreSubmeanSquareBarrier
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

lemma normalizedCoreField_pos_le {N : ℕ} (ψ : FormVector N)
    {Z lam d : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hd : 0 < d)
    {z : Space} (hz : d ≤ ‖z‖) :
    max (normalizedCoreField Z lam ψ z) 0 ≤ Z/d := by
  apply max_le
  · exact (normalizedCoreField_le_nuclear ψ hZ hlam z).trans
      (div_le_div_of_nonneg_left hZ hd hz)
  · exact div_nonneg hZ hd.le

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_LocalWidthKernel
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
open scoped NNReal ContDiff

def masterKernel (c₁ r₀ s : ℝ) (g : Space → ℝ) (x y : Space) : ℝ :=
  (scaledRealPacket (masterWidth c₁ r₀ s x) g (y-x))^2

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_InnerFieldCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set Metric Laplacian
noncomputable section
namespace CoulombAtom
open CoulombAnalysis

 def innerFieldTestAnnulus (h : ℝ) : Set Space := {z | h ≤ ‖z‖ ∧ ‖z‖ ≤ 3*h}

 lemma innerFieldTestAnnulus_measurable (h : ℝ) : MeasurableSet (innerFieldTestAnnulus h) :=
   (measurableSet_le measurable_const continuous_norm.measurable).inter
     (measurableSet_le continuous_norm.measurable measurable_const)

 lemma innerFieldTestAnnulus_finite (h : ℝ) : volume (innerFieldTestAnnulus h) < ⊤ :=
   (measure_mono (fun z hz => show z ∈ closedBall (0 : Space) (3*h) by
     simpa only [mem_closedBall,dist_zero_right] using hz.2)).trans_lt ((isCompact_closedBall (0 : Space) (3*h)).measure_lt_top)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_CoreHistoryFieldFubiniBarrier
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

lemma coreFieldSquare_joint_aestronglyMeasurable_of_aemeasurable
    {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (Z lam : ℝ) {μ : Measure Space}
    (hkernel : AEMeasurable
      (fun point : Configuration M => Measure.map (Prod.mk point) μ) volume) :
    AEStronglyMeasurable
      (fun q : Configuration M × Space => coreFieldSquare Z lam q.2 (coreSlice ψ t q.1))
      (volume.prod μ) := by
  have hfst : Measure.QuasiMeasurePreserving
      (Prod.fst : Configuration M × Space → Configuration M) (volume.prod μ) volume := by
    refine ⟨measurable_fst, Measure.AbsolutelyContinuous.mk fun subset hsubset hzero => ?_⟩
    rw [Measure.map_apply measurable_fst hsubset, Measure.prod,
      Measure.bind_apply (measurable_fst hsubset) hkernel]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with point hpoint
    rw [Measure.map_apply measurable_prodMk_left (measurable_fst hsubset)]
    have hempty : Prod.mk point ⁻¹' (Prod.fst ⁻¹' subset) = (∅ : Set Space) := by
      ext other
      simp [hpoint]
    rw [hempty, measure_empty]
    rfl
  obtain ⟨F,hF,he⟩ := coreSlice_field_measurable_rep hψ t Z lam
  have hh : AEStronglyMeasurable (fun q : Configuration M × Space =>
      (max (F q) 0)^2*formMass (coreSlice ψ t q.1)) (volume.prod μ) :=
    ((hF.max measurable_const).pow_const 2).aestronglyMeasurable.mul
    ((hψ.coreSlice_mass_integrable t).aestronglyMeasurable.comp_quasiMeasurePreserving hfst)
  apply hh.congr
  filter_upwards [hfst.ae he] with q hq
  rw [hq q.2]
  rfl

lemma coreFieldSquare_joint_aestronglyMeasurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (Z lam : ℝ) {μ : Measure Space} [SFinite μ] :
    AEStronglyMeasurable
      (fun q : Configuration M × Space => coreFieldSquare Z lam q.2 (coreSlice ψ t q.1))
      (volume.prod μ) :=
  coreFieldSquare_joint_aestronglyMeasurable_of_aemeasurable hψ t Z lam
    Measurable.map_prodMk_left.aemeasurable

lemma coreFieldSquare_weighted_prod_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) {Z lam d : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hd : 0 < d) {w : Space → ℝ}
    (hw : Integrable w) (hn : ∀ z, 0 ≤ w z) (hs : ∀ z, w z ≠ 0 → d ≤ ‖z‖) :
    Integrable (fun q : Configuration M × Space =>
      coreFieldSquare Z lam q.2 (coreSlice ψ t q.1)*w q.2) (volume.prod volume) := by
  have hi := ((hψ.coreSlice_mass_integrable t).mul_prod hw).const_mul ((Z/d)^2)
  apply hi.mono' ((coreFieldSquare_joint_aestronglyMeasurable hψ t Z lam).mul
    hw.aestronglyMeasurable.comp_snd)
  apply ae_of_all
  intro q
  change ‖coreFieldSquare Z lam q.2 (coreSlice ψ t q.1)*w q.2‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (coreFieldSquare_nonneg _ _ _ _) (hn _))]
  by_cases he : w q.2 = 0
  · simp only [he,mul_zero,le_refl]
  · have hb := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (le_max_right _ _) (normalizedCoreField_pos_le
        (coreSlice ψ t q.1) hZ hlam hd (hs q.2 he)) 2)
      (formMass_nonneg (coreSlice ψ t q.1))
    have hh := mul_le_mul_of_nonneg_right hb (hn q.2)
    simpa only [coreFieldSquare,mul_assoc] using hh

namespace CoreObservationGraph

lemma fieldMoment_weighted_integrable (G : CoreObservationGraph) {Z lam d : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hd : 0 < d) {w : Space → ℝ}
    (hw : Integrable w) (hn : ∀ z, 0 ≤ w z) (hs : ∀ z, w z ≠ 0 → d ≤ ‖z‖) :
    Integrable (fun z => G.fieldMoment Z lam z*w z) := by
  unfold fieldMoment coreLawAverage
  simp only [Finset.sum_mul]
  apply integrable_finsetSum
  intro t _
  have hi := (coreFieldSquare_weighted_prod_integrable G.sobolev t hZ hlam hd hw hn hs).integral_prod_right
  simpa only [integral_mul_const] using hi

end CoreObservationGraph
end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_CoreHistoryOutMaximumBarrier
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

open CoulombAnalysis

lemma ball_one_integrable (y : Space) (A : ℝ) :
    Integrable ((closedBall y A).indicator (fun _ => (1:ℝ))) := by
  apply bounded_compact_integrable (measurable_const.indicator isClosed_closedBall.measurableSet)
    (isCompact_closedBall y A) (B := 1)
  · exact support_indicator_subset
  · intro z
    by_cases hz : z ∈ closedBall y A <;> simp [hz]

lemma ball_indicator_nuclear_separation (y : Space) {A d : ℝ}
    (hsep : A+d ≤ ‖y‖) (z : Space)
    (hz : (closedBall y A).indicator (fun _ => (1:ℝ)) z ≠ 0) : d ≤ ‖z‖ := by
  have hm : z ∈ closedBall y A := by
    by_contra hm
    exact hz (by simp [hm])
  have hzd : ‖z-y‖ ≤ A := by simpa only [mem_closedBall,dist_eq_norm] using hm
  have hh := norm_le_norm_sub_add y z
  rw [norm_sub_rev y z] at hh
  linarith

lemma coreLawAverage_fieldSquare_ball_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (y : Space) {A d Z lam : ℝ}
    (hd : 0 < d) (hsep : A+d ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    IntegrableOn (fun z => coreLawAverage ψ (coreFieldSquare Z lam z)) (closedBall y A) := by
  have hi : Integrable (fun z => coreLawAverage ψ (coreFieldSquare Z lam z)*
      (closedBall y A).indicator (fun _ => (1:ℝ)) z) := by
    unfold coreLawAverage
    simp only [Finset.sum_mul]
    apply integrable_finsetSum
    intro t _
    have hj := (coreFieldSquare_weighted_prod_integrable hψ t hZ hlam hd
      (ball_one_integrable y A) (fun z => indicator_nonneg (fun _ _ => zero_le_one) z)
      (ball_indicator_nuclear_separation y hsep)).integral_prod_right
    simpa only [integral_mul_const] using hj
  rw [←integrable_indicator_iff isClosed_closedBall.measurableSet]
  apply hi.congr
  exact ae_of_all _ (fun z => by by_cases hz : z ∈ closedBall y A <;> simp [hz])

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CoreHistoryCountsBarrier
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

lemma rawBallCount_cutCore_le {N : ℕ} (c : Fin N → Fin 2) (x : Configuration N)
    (y : Space) (R : ℝ) : rawBallCount y R (cutCorePositions c x) ≤ rawBallCount y R x := by
  rw [rawBallCount,sum_cutCorePositions c x (fun z => if ‖z-y‖ < R then 1 else 0)]
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> norm_num

def rawCountMoment {N : ℕ} (ψ : FormVector N) (y : Space) (R : ℝ) : ℝ :=
  rawFormPair ψ (fun x => rawBallCount y R x^2)

lemma rawCountMoment_nonneg {N : ℕ} (ψ : FormVector N) (y : Space) (R : ℝ) :
    0 ≤ rawCountMoment ψ y R :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))

lemma rawCountMoment_coreSlice_integrable {N M : ℕ} {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    (y : Space) (R : ℝ) (t : Spins M) :
    Integrable (fun v => rawCountMoment (coreSlice ψ t v) y R) :=
  rawFormPair_coreSlice_integrable hψ ((rawBallCount_measurable y R).pow_const 2)
    (fun x => norm_sq_le_of_nonneg (rawBallCount_nonneg y R x) (rawBallCount_le y R x)) t

lemma sum_cutCore_countMoment_le {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (y : Space) (R : ℝ) :
    (∑ c : Fin N → Fin 2, coreLawAverage (orderedCutForm p hp ψ c)
      (fun φ => rawCountMoment φ y R)) ≤ rawCountMoment ψ y R := by
  simp only [rawCountMoment]
  simp_rw [cutCore_rawFormPair p hp hψ _ ((rawBallCount_measurable y R).pow_const 2)
    (fun x => norm_sq_le_of_nonneg (rawBallCount_nonneg y R x) (rawBallCount_le y R x))]
  rw [rawFormPair_eq_integral hψ ((rawBallCount_measurable y R).pow_const 2)
    (fun x => norm_sq_le_of_nonneg (rawBallCount_nonneg y R x) (rawBallCount_le y R x))]
  change spatialCutExpectation p hp ψ (fun c x => rawBallCount y R (cutCorePositions c x)^2) ≤ _
  apply spatialCutExpectation_le_raw p hp hψ
    (fun c => ((rawBallCount_measurable y R).comp (cutCorePositions_measurable c)).pow_const 2)
    (A := (N:ℝ)^2)
    (fun c x => norm_sq_le_of_nonneg (rawBallCount_nonneg _ _ _)
      ((rawBallCount_cutCore_le c x y R).trans (rawBallCount_le _ _ _)))
    ((rawBallCount_measurable y R).pow_const 2) (B := (N:ℝ)^2)
    (fun x => norm_sq_le_of_nonneg (rawBallCount_nonneg _ _ _) (rawBallCount_le _ _ _))
  intro c x _
  exact pow_le_pow_left₀ (rawBallCount_nonneg _ _ _) (rawBallCount_cutCore_le c x y R) 2

lemma nextCoreObservation_count_statistic_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2)
    (y : Space) (R : ℝ) (t : Spins M) :
    Integrable (fun v => coreLawAverage (orderedCutForm p hp (coreSlice ψ t v) c)
      (fun φ => rawCountMoment φ y R)) :=
  nextCoreObservation_statistic_integrable ψ p hp c (fun φ => rawCountMoment φ y R)
    (fun s => rawCountMoment_coreSlice_integrable (nextCoreObservation_sobolev hψ p hp c) y R s) t

lemma sum_nextCoreObservation_count_eq {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (y : Space) (R : ℝ) :
    (∑ c : Fin N → Fin 2, coreLawAverage (nextCoreObservation p hp ψ c)
      (fun φ => rawCountMoment φ y R)) =
    ∑ t : Spins M, ∫ v, ∑ c : Fin N → Fin 2,
      coreLawAverage (orderedCutForm p hp (coreSlice ψ t v) c) (fun φ => rawCountMoment φ y R) := by
  have ht (c : Fin N → Fin 2) := coreLawAverage_next ψ p hp c
    (fun φ => rawCountMoment φ y R)
    (fun s => rawCountMoment_coreSlice_integrable (nextCoreObservation_sobolev hψ p hp c) y R s)
  simp_rw [ht]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  exact (integral_finsetSum _ (fun c _ =>
    nextCoreObservation_count_statistic_integrable hψ p hp c y R t)).symm

theorem sum_nextCoreObservation_countMoment_le {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (y : Space) (R : ℝ) :
    (∑ c : Fin N → Fin 2, coreLawAverage (nextCoreObservation p hp ψ c)
      (fun φ => rawCountMoment φ y R)) ≤
      coreLawAverage ψ (fun φ => rawCountMoment φ y R) := by
  rw [sum_nextCoreObservation_count_eq hψ p hp y R]
  change (∑ t : Spins M, ∫ v, ∑ c : Fin N → Fin 2,
      coreLawAverage (orderedCutForm p hp (coreSlice ψ t v) c) (fun φ => rawCountMoment φ y R)) ≤
    ∑ t : Spins M, ∫ v, rawCountMoment (coreSlice ψ t v) y R
  apply Finset.sum_le_sum
  intro t _
  apply integral_mono_ae
    (integrable_finsetSum _ (fun c _ => nextCoreObservation_count_statistic_integrable hψ p hp c y R t))
    (rawCountMoment_coreSlice_integrable hψ y R t)
  filter_upwards [hψ.ae_coreSlice t] with v hv
  exact sum_cutCore_countMoment_le hv p hp y R

namespace CoreObservationGraph

def countMoment (G : CoreObservationGraph) (y : Space) (R : ℝ) : ℝ :=
  coreLawAverage G.vector (fun φ => rawCountMoment φ y R)

lemma countMoment_nonneg (G : CoreObservationGraph) (y : Space) (R : ℝ) : 0 ≤ G.countMoment y R :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => rawCountMoment_nonneg _ _ _))

lemma observe_countMoment (G : CoreObservationGraph) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (y : Space) (R : ℝ) :
    (∑ c : Fin G.coreSize → Fin 2, (G.observe p hp c).countMoment y R) ≤ G.countMoment y R :=
  sum_nextCoreObservation_countMoment_le G.sobolev p hp y R

end CoreObservationGraph

open MeasureTheory Filter
open scoped BigOperators

lemma rawBallCount_le_of_radius {N : ℕ} (x : Configuration N) (y z : Space) {R S : ℝ}
    (h : ‖y-z‖+R ≤ S) : rawBallCount y R x ≤ rawBallCount z S x := by
  unfold rawBallCount
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hy hz hz
  · norm_num
  · exfalso
    apply hz
    have hh : ‖x i-z‖ ≤ ‖x i-y‖+‖y-z‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (x i-y) (y-z)
    linarith
  · norm_num
  · norm_num

lemma rawCountMoment_le_of_radius {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y z : Space) {R S : ℝ} (h : ‖y-z‖+R ≤ S) : rawCountMoment ψ y R ≤ rawCountMoment ψ z S := by
  have hi (w : Space) (r : ℝ) (s : Spins N) : Integrable (fun x => rawBallCount w r x^2*‖ψ.value s x‖^2) :=
    ((hψ.1 s).norm.integrable_sq).bdd_mul ((rawBallCount_measurable w r).pow_const 2).aestronglyMeasurable
      (ae_of_all _ (fun x => norm_sq_le_of_nonneg (rawBallCount_nonneg _ _ _) (rawBallCount_le _ _ _)))
  unfold rawCountMoment rawFormPair
  apply Finset.sum_le_sum
  intro s _
  apply integral_mono (hi y R s) (hi z S s)
  intro x
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (rawBallCount_nonneg _ _ _)
    (rawBallCount_le_of_radius x y z h) 2) (sq_nonneg _)

namespace CoreObservationGraph

lemma countMoment_le_of_radius (G : CoreObservationGraph) (y z : Space) {R S : ℝ}
    (h : ‖y-z‖+R ≤ S) : G.countMoment y R ≤ G.countMoment z S := by
  unfold countMoment coreLawAverage
  apply Finset.sum_le_sum
  intro s _
  apply integral_mono_ae (rawCountMoment_coreSlice_integrable G.sobolev y R s)
    (rawCountMoment_coreSlice_integrable G.sobolev z S s)
  filter_upwards [G.sobolev.ae_coreSlice s] with u hu
  exact rawCountMoment_le_of_radius hu y z h

end CoreObservationGraph

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RootMomentCauchyBarrier
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

lemma localCellRadius_pos {y : Space} (hy : y ≠ 0) : 0 < localCellRadius y := by
  unfold localCellRadius
  exact div_pos (norm_pos_iff.mpr hy) (by norm_num)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_CoreObservationEnsembleBarrier
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

structure CoreObservationEnsemble where
  Branch : Type
  finite : Fintype Branch
  graph : Branch → CoreObservationGraph
attribute [instance] CoreObservationEnsemble.finite

namespace CoreObservationEnsemble

def initial {N : ℕ} (ψ : FormVector N) (hψ : SobolevFermion ψ) : CoreObservationEnsemble where
  Branch := Unit
  finite := inferInstance
  graph := fun _ => CoreObservationGraph.initial ψ hψ

def observe (E : CoreObservationEnsemble) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) : CoreObservationEnsemble where
  Branch := Σ i : E.Branch, Fin (E.graph i).coreSize → Fin 2
  finite := inferInstance
  graph := fun ic => (E.graph ic.1).observe p hp ic.2

def mass (E : CoreObservationEnsemble) : ℝ := ∑ i, (E.graph i).mass
def countMoment (E : CoreObservationEnsemble) (y : Space) (R : ℝ) : ℝ :=
  ∑ i, (E.graph i).countMoment y R
def fieldMoment (E : CoreObservationEnsemble) (Z lam : ℝ) (y : Space) : ℝ :=
  ∑ i, (E.graph i).fieldMoment Z lam y
def excess (E : CoreObservationEnsemble) (Z lam : ℝ) : ℝ := ∑ i, (E.graph i).excess Z lam
lemma countMoment_nonneg (E : CoreObservationEnsemble) (y : Space) (R : ℝ) : 0 ≤ E.countMoment y R :=
  Finset.sum_nonneg (fun i _ => (E.graph i).countMoment_nonneg y R)

lemma observe_mass (E : CoreObservationEnsemble) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) : (E.observe p hp).mass = E.mass := by
  change (∑ ic : Σ i : E.Branch, Fin (E.graph i).coreSize → Fin 2, ((E.graph ic.1).observe p hp ic.2).mass) = _
  rw [Fintype.sum_sigma]
  simp_rw [CoreObservationGraph.observe_mass]
  rfl

lemma observe_countMoment (E : CoreObservationEnsemble) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (y : Space) (R : ℝ) :
    (E.observe p hp).countMoment y R ≤ E.countMoment y R := by
  change (∑ ic : Σ i : E.Branch, Fin (E.graph i).coreSize → Fin 2,
    ((E.graph ic.1).observe p hp ic.2).countMoment y R) ≤ _
  rw [Fintype.sum_sigma]
  exact Finset.sum_le_sum (fun i _ => (E.graph i).observe_countMoment p hp y R)

lemma fieldMoment_le_nuclear (E : CoreObservationEnsemble) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (y : Space) : E.fieldMoment Z lam y ≤ (Z/‖y‖)^2*E.mass := by
  unfold fieldMoment mass
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => (E.graph i).fieldMoment_le_nuclear hZ hlam y)

lemma fieldMoment_ball_integrable (E : CoreObservationEnsemble) (y : Space) {A d Z lam : ℝ}
    (hd : 0 < d) (hs : A+d ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    IntegrableOn (E.fieldMoment Z lam) (closedBall y A) :=
  integrable_finsetSum _ (fun i _ => coreLawAverage_fieldSquare_ball_integrable
    (E.graph i).sobolev y hd hs hZ hlam)

end CoreObservationEnsemble
end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BallAverageKernelBarrier
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

namespace CoreObservationEnsemble

lemma countMoment_le_of_radius (E : CoreObservationEnsemble) (y z : Space) {R S : ℝ}
    (h : ‖y-z‖+R ≤ S) : E.countMoment y R ≤ E.countMoment z S :=
  Finset.sum_le_sum (fun i _ => (E.graph i).countMoment_le_of_radius y z h)

end CoreObservationEnsemble

open MeasureTheory Set Metric
open scoped BigOperators

inductive CoreLocalHistory (E₀ : CoreObservationEnsemble) (y₀ : Space) (a : ℝ) (ha : 0 < a) :
    ℕ → CoreObservationEnsemble → Prop
  | initial : CoreLocalHistory E₀ y₀ a ha 0 E₀
  | observe {n : ℕ} {E : CoreObservationEnsemble} (hE : CoreLocalHistory E₀ y₀ a ha n E)
      (y : Space) (hy : y ∈ closedBall y₀ (localHistoryReach a n)) :
      CoreLocalHistory E₀ y₀ a ha (n+1)
        (E.observe (coreFirstRadialCut y (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (localHistoryRadius_pos ha n).le)
          (localHistoryRadius_pos ha n))
          (coreFirstRadialCut_partition y (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (localHistoryRadius_pos ha n).le)
            (localHistoryRadius_pos ha n)))

namespace CoreLocalHistory
variable {E₀ E : CoreObservationEnsemble} {y₀ : Space} {a : ℝ} {ha : 0 < a} {n : ℕ}

lemma mass (hE : CoreLocalHistory E₀ y₀ a ha n E) : E.mass = E₀.mass := by
  induction hE with
  | initial => rfl
  | observe hE y hy ih => rw [CoreObservationEnsemble.observe_mass,ih]

lemma countMoment (hE : CoreLocalHistory E₀ y₀ a ha n E) (y : Space) (R : ℝ) :
    E.countMoment y R ≤ E₀.countMoment y R := by
  induction hE with
  | initial => rfl
  | observe hE z hz ih => exact (CoreObservationEnsemble.observe_countMoment ..).trans ih

lemma countMoment_local (hE : CoreLocalHistory E₀ y₀ a ha n E) (y : Space)
    (hy : y ∈ closedBall y₀ (localHistoryReach a n)) :
    E.countMoment y (4*localHistoryRadius a n) ≤ E₀.countMoment y₀ (8*a) := by
  apply (E.countMoment_le_of_radius y y₀ ?_).trans (hE.countMoment y₀ (8*a))
  have hh : ‖y-y₀‖ ≤ localHistoryReach a n := by simpa only [mem_closedBall,dist_eq_norm] using hy
  have h1 := localHistoryReach_lt ha n
  have h2 := localHistoryRadius_le ha n
  linarith

include ha in
lemma center_nuclear_separation (hsep : 12*a ≤ ‖y₀‖) (y : Space)
    (hy : y ∈ closedBall y₀ (localHistoryReach a n)) : 8*a ≤ ‖y‖ := by
  have hh : ‖y-y₀‖ ≤ localHistoryReach a n := by simpa only [mem_closedBall,dist_eq_norm] using hy
  have hh' : ‖y₀‖ ≤ ‖y‖+‖y-y₀‖ := by
    have := norm_add_le y (y₀-y)
    simpa only [add_sub_cancel, norm_sub_rev] using this
  have h1 := localHistoryReach_lt ha n
  linarith

lemma next_center (y z : Space) (hy : y ∈ closedBall y₀ (localHistoryReach a n))
    (hz : z ∈ closedBall y (4*localHistoryRadius a n)) :
    z ∈ closedBall y₀ (localHistoryReach a (n+1)) := by
  rw [mem_closedBall,localHistoryReach_step]
  exact (dist_triangle z y y₀).trans (add_le_add hz hy |>.trans_eq (add_comm _ _))

end CoreLocalHistory

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_DyadicObservation
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

namespace CoulombAtom
open CoulombObservation

def physicalObservationArray {N : ℕ} {J : Type*} [Fintype J]
    (ell : J → ℝ) (z : Configuration N × (J × (Fin N × Fin 3) → ℝ)) :
    J × (Fin N × Fin 3) → ℝ := fun q => z.1 q.2.1 q.2.2 + ell q.1 * z.2 q

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_UnorderedObservations
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_UnorderedObservations_scope

open MeasureTheory Set
open scoped BigOperators

namespace CoulombAtom
open CoulombObservation

def configurationSetoid (N : ℕ) : Setoid (Configuration N) where
  r x y := ∃ π : Equiv.Perm (Fin N), ∀ i, y i = x (π i)
  iseqv := {
    refl := fun _ => ⟨Equiv.refl _,fun _ => rfl⟩
    symm := by
      rintro x y ⟨π,hπ⟩
      exact ⟨π.symm,fun i => by simpa using (hπ (π.symm i)).symm⟩
    trans := by
      rintro x y z ⟨π,hπ⟩ ⟨τ,hτ⟩
      exact ⟨τ.trans π,fun i => (hτ i).trans (hπ (τ i))⟩ }

abbrev UnorderedConfiguration (N : ℕ) := Quotient (configurationSetoid N)

def unorderedConfiguration {N : ℕ} (x : Configuration N) : UnorderedConfiguration N :=
  Quotient.mk'' x

def unorderedStatistic {N : ℕ} (g : Space → ℝ) : UnorderedConfiguration N → ℝ :=
  Quotient.lift (fun x : Configuration N => ∑ i, g (x i)) (by
    rintro x y ⟨π,hπ⟩
    simp_rw [hπ]
    exact (Equiv.sum_comp π (fun i => g (x i))).symm)

@[simp] lemma unorderedStatistic_mk {N : ℕ} (g : Space → ℝ) (x : Configuration N) :
    unorderedStatistic g (unorderedConfiguration x) = ∑ i, g (x i) := rfl

def physicalObservedConfiguration {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) : Configuration N :=
  fun i => WithLp.toLp 2 (fun a => physicalObservationArray ell z (k,i,a))

def unorderedObservedConfiguration {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) : UnorderedConfiguration N :=
  unorderedConfiguration (physicalObservedConfiguration ell k z)

@[instance_reducible] def observationInformation {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    MeasurableSpace (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) :=
  ⨆ k : Fin K, if j ≤ k.val then
    MeasurableSpace.comap (unorderedObservedConfiguration ell k) inferInstance else ⊥

end CoulombAtom

end Work_UnorderedObservations_scope

open MeasureTheory Set Filter Metric
open scoped BigOperators NNReal

namespace CoulombAtom
open CoulombObservation

def physicalObservationLaw {N : ℕ} (μ : Measure (Configuration N)) (K : ℕ) :
    Measure (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) :=
  μ.prod (Measure.pi (fun _ : Fin K × (Fin N × Fin 3) => compactNoiseLaw))

instance physicalObservationLaw_finite {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] : IsFiniteMeasure (physicalObservationLaw μ K) := by
  unfold physicalObservationLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma physicalObservationLaw_probability {N K : ℕ} (μ : Measure (Configuration N))
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (physicalObservationLaw μ K) := by
  unfold physicalObservationLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_OriginalPosteriorKernel
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
open CoulombObservation ProbabilityTheory

def OriginalDatum (N K : ℕ) (_ell : Fin K → ℝ) (_j : ℕ) :=
  Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)

instance instMeasurableSpaceOriginalDatum {N K : ℕ} {ell : Fin K → ℝ} {j : ℕ} :
    MeasurableSpace (OriginalDatum N K ell j) := observationInformation ell j

def originalDatum {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → OriginalDatum N K ell j := id

def originalRawKernel {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) : Kernel (OriginalDatum N K ell j) (Configuration N) :=
  condDistrib Prod.fst (originalDatum ell j) (physicalObservationLaw μ K)

def kernelPosteriorTest {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (g : Space → ℝ) (z : OriginalDatum N K ell j) : ℝ :=
  ∫ x, ∑ i, g (x i) ∂originalRawKernel μ ell j z

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_MasterJointPosterior
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
open CoulombObservation ProbabilityTheory

def jointMasterPosterior {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (c₁ r₀ s : ℝ) (g : Space → ℝ)
    (z : OriginalDatum N K ell j) (y : Space) : ℝ :=
  kernelPosteriorTest μ ell j (fun x => masterKernel c₁ r₀ s g x y) z

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_PatchCenterIntegrable
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAtom
open CoulombAnalysis

def weightedPatchCenter {N M : ℕ} (ψ : FormVector (N+M)) (t : Spins M)
    (Z lam : ℝ) (y : Space) (R : ℝ) (u : Configuration M) : ℝ :=
  formMass (coreSlice ψ t u)*conditionalPatchCenter ψ t Z lam y R u

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_NormalizedMasterEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

def expectedRadialPatchCenter {N : ℕ} (ψ : FormVector N) (y : Space) {t b : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (Z lam : ℝ) : ℝ :=
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  ∑ c : Fin N → Fin 2, ∑ k : Spins (cutOutNumber c), ∫ u,
    weightedPatchCenter (orderedCutForm p hp ψ c) k Z lam y (t-4*b) u

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_BindingBase
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

section

def quantumEnergyDensity {N : ℕ} (Z : ℝ) (ψ : FormVector N) (s : Spins N)
    (x : Configuration N) : ℝ :=
  (1/2:ℝ) * (∑ i, ∑ a, ‖ψ.gradient s i a x‖ ^ 2) -
    Z * (∑ i, ‖ψ.value s x‖ ^ 2 / ‖x i‖) +
    (1/2:ℝ) * (∑ i, ∑ j, if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0)

def quantumCoreDensity {N : ℕ} (Z : ℝ) (ψ : FormVector N) (i : Fin N) (s : Spins N)
    (x : Configuration N) : ℝ :=
  (1/2:ℝ) * (∑ j, if j ≠ i then ∑ a, ‖ψ.gradient s j a x‖ ^ 2 else 0) -
    Z * (∑ j, if j ≠ i then ‖ψ.value s x‖ ^ 2 / ‖x j‖ else 0) +
    (1/2:ℝ) * (∑ j, ∑ k,
      if j ≠ i ∧ k ≠ i ∧ j ≠ k then ‖ψ.value s x‖ ^ 2 / ‖x j-x k‖ else 0)

attribute [local irreducible] graphComponent graphFormVector

end


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_Weighted
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

def bindingWeight (R ε : ℝ) (x : Space) : ℝ :=
  R * regularizedRadius ε x / (R + regularizedRadius ε x)


open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_BindingWeightContinuous
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
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace


open MeasureTheory Filter
open scoped Topology BigOperators

def bindingApprox (n : ℕ) (x : Space) : ℝ :=
  bindingWeight ((n:ℝ)+1) (((n:ℝ)+1)⁻¹) x


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

def bindingPairApprox {N : ℕ} (n : ℕ) (i j : Fin N) (x : Configuration N) : ℝ :=
  min 1 ((bindingApprox n (x i) + bindingApprox n (x j)) / ‖x i-x j‖)


open MeasureTheory Filter
open scoped Topology BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_WeightedMass
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
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace CoulombAtom

attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply coulombFormOperator fermionGraph weakGraph fermionGraphValue

def weightedMass {N : ℕ} (F : fermionGraph N) (w : Configuration N → ℝ) : ℝ :=
  ∑ s, ∫ x, w x * ‖graphComponent s none F x‖ ^ 2

def weightedGradient {N : ℕ} (F : fermionGraph N) (w : Configuration N → ℝ) (i : Fin N) : ℝ :=
  ∑ s, ∑ a, ∫ x, w x * ‖graphComponent s (some (i,a)) F x‖ ^ 2

def weightedFullDensity {N : ℕ} (Z : ℝ) (F : fermionGraph N) (w : Configuration N → ℝ) : ℝ :=
  ∑ s, ∫ x, w x * quantumEnergyDensity Z (graphFormVector F) s x

def weightedCoreDensity {N : ℕ} (Z : ℝ) (F : fermionGraph N) (i : Fin N)
    (w : Configuration N → ℝ) : ℝ :=
  ∑ s, ∫ x, w x * quantumCoreDensity Z (graphFormVector F) i s x

def weightedNuclear {N : ℕ} (F : fermionGraph N) (i : Fin N)
    (w : Configuration N → ℝ) : ℝ :=
  ∑ s, ∫ x, w x * (‖graphComponent s none F x‖ ^ 2 / ‖x i‖)

def weightedPairs {N : ℕ} (F : fermionGraph N) (i : Fin N)
    (w : Configuration N → ℝ) : ℝ :=
  ∑ s, ∑ j, ∫ x, w x * (if i ≠ j then ‖graphComponent s none F x‖ ^ 2 / ‖x i-x j‖ else 0)

attribute [local irreducible] graphNuclear graphPair
  weightedMass weightedGradient weightedFullDensity weightedCoreDensity weightedNuclear weightedPairs

def graphKineticPair {N : ℕ} (G F : fermionGraph N) : ℝ :=
  ∑ s, ∑ i, ∑ a, (⟪graphComponent s (some (i,a)) G,
    graphComponent s (some (i,a)) F⟫_ℂ).re

def weightedKinetic {N : ℕ} (F : fermionGraph N) (w : Configuration N → ℝ) : ℝ :=
  ∑ i, weightedGradient F w i

attribute [local irreducible] weightedKinetic graphKineticPair

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_BindingNuclearSum
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
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace CoulombAtom

attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue bindingApprox bindingPairApprox

def bindingNuclearSum {N : ℕ} (F : fermionGraph N) (n : ℕ) : ℝ :=
  ∑ i, weightedNuclear F i (fun x => bindingApprox n (x i))

def bindingPairSum {N : ℕ} (F : fermionGraph N) (n : ℕ) : ℝ :=
  ∑ i, weightedPairs F i (fun x => bindingApprox n (x i))

def bindingCappedSum {N : ℕ} (F : fermionGraph N) (n : ℕ) : ℝ :=
  ∑ s, ∑ i, ∑ j, if i ≠ j then
    (∫ x, bindingPairApprox n i j x * ‖graphComponent s none F x‖ ^ 2) else 0

attribute [local irreducible] bindingNuclearSum bindingPairSum bindingCappedSum

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_FiniteCellObservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Metric
noncomputable section
namespace CoulombAtom
namespace CoreObservationEnsemble

 def observeCell (E : CoreObservationEnsemble) (y : Space) : CoreObservationEnsemble :=
    if h : y = 0 then E else
      E.observe (coreFirstRadialCut y (localCellRadius_pos h).le (localCellRadius_pos h))
        (coreFirstRadialCut_partition y (localCellRadius_pos h).le (localCellRadius_pos h))

 def observeCells (E : CoreObservationEnsemble) : List Space → CoreObservationEnsemble
    | [] => E
    | y::ys => (E.observeCell y).observeCells ys

end CoreObservationEnsemble
end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_InnerCapStatistic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter Set Metric
open scoped BigOperators

def innerFieldAnnulusWeight (h : ℝ) : Space → ℝ :=
  (innerFieldTestAnnulus h).indicator (fun _ => 1)
lemma innerFieldAnnulusWeight_integrable (h : ℝ) : Integrable (innerFieldAnnulusWeight h) := by
  rw [innerFieldAnnulusWeight,integrable_indicator_iff (innerFieldTestAnnulus_measurable h)]
  exact integrableOn_const (C := (1:ℝ)) (hs := innerFieldTestAnnulus_finite h |>.ne)
lemma innerFieldAnnulusWeight_nonneg (h : ℝ) (z : Space) : 0 ≤ innerFieldAnnulusWeight h z :=
  indicator_nonneg (fun _ _ => zero_le_one) z
lemma innerFieldAnnulusWeight_separation (h : ℝ) (z : Space)
    (hz : innerFieldAnnulusWeight h z ≠ 0) : h ≤ ‖z‖ := by
  by_contra! hc
  exact hz (indicator_of_notMem (by intro hd; exact (not_le_of_gt hc) hd.1) _)

namespace CoreObservationGraph

lemma fieldMoment_annular_integrable (G : CoreObservationGraph) {Z lam h : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) :
    IntegrableOn (G.fieldMoment Z lam) (innerFieldTestAnnulus h) := by
  have hi := G.fieldMoment_weighted_integrable hZ hlam hh (innerFieldAnnulusWeight_integrable h)
    (innerFieldAnnulusWeight_nonneg h) (innerFieldAnnulusWeight_separation h)
  rw [←integrable_indicator_iff (innerFieldTestAnnulus_measurable h)]
  apply hi.congr
  exact ae_of_all _ (fun z => by by_cases hz : z ∈ innerFieldTestAnnulus h <;> simp [innerFieldAnnulusWeight,hz])

end CoreObservationGraph

namespace CoreObservationEnsemble

lemma fieldMoment_annular_integrable (E : CoreObservationEnsemble) {Z lam h : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hh : 0 < h) :
    IntegrableOn (E.fieldMoment Z lam) (innerFieldTestAnnulus h) :=
  integrable_finsetSum _ (fun i _ => (E.graph i).fieldMoment_annular_integrable hZ hlam hh)

end CoreObservationEnsemble

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_Observation
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

def SplitPositionSupport {N M : ℕ} (psi : FormVector (N+M)) (P Q : Space → Prop) : Prop :=
  ∀ (s : Spins N) (t : Spins M) (x : Configuration N) (v : Configuration M),
    psi.value (joinLists s t) (joinLists x v) ≠ 0 → (∀ i, P (x i)) ∧ (∀ i, Q (v i))

lemma orderedCutForm_nonzero_factors {N : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2=1)
    (psi : FormVector N) (c : Fin N → Fin 2)
    (s : Spins (cutCoreNumber c)) (t : Spins (cutOutNumber c))
    (x : Configuration (cutCoreNumber c)) (v : Configuration (cutOutNumber c))
    (hn : (orderedCutForm p hp psi c).value (joinLists s t) (joinLists x v) ≠ 0) :
    psi.value (joinLists s t ∘ (cutOrder c).symm) (joinLists x v ∘ (cutOrder c).symm) ≠ 0 ∧
    (∀ i, (p 0).value (x i) ≠ 0) ∧ (∀ i, (p 1).value (v i) ≠ 0) := by
  have hv := hn
  rw [orderedCutForm_value] at hv
  change (spatialProductValue p (coreCutLabels (cutCoreNumber c) (cutOutNumber c))
    (joinLists x v) : ℂ)*_ ≠ 0 at hv
  have hprod : spatialProductValue p (coreCutLabels (cutCoreNumber c) (cutOutNumber c))
      (joinLists x v) ≠ 0 := by
    intro hh
    exact hv (by rw [hh,Complex.ofReal_zero,zero_mul])
  refine ⟨(mul_ne_zero_iff.mp hv).2,?_,?_⟩
  · intro i hi
    apply hprod
    apply Finset.prod_eq_zero (Finset.mem_univ (finSumFinEquiv (Sum.inl i)))
    simpa only [coreCutLabels,joinLists_left] using hi
  · intro i hi
    apply hprod
    apply Finset.prod_eq_zero (Finset.mem_univ (finSumFinEquiv (Sum.inr i)))
    simpa only [coreCutLabels,joinLists_right] using hi

lemma SplitPositionSupport.observe {N M : ℕ} {psi : FormVector (N+M)} {P Q : Space → Prop}
    (hs : SplitPositionSupport psi P Q)
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2=1)
    (hQ : ∀ z, (p 1).value z ≠ 0 → Q z) (c : Fin N → Fin 2) :
    SplitPositionSupport (nextCoreObservation p hp psi c)
      (fun z => P z ∧ (p 0).value z ≠ 0) Q := by
  intro s t x v hn
  have htn : t = joinLists (leftList t) (rightList t) := (join_list_parts t).symm
  have hvn : v = joinLists (leftList v) (rightList v) := (join_list_parts v).symm
  have hh : (orderedCutForm p hp (coreSlice psi (rightList t) (rightList v)) c).value
      (joinLists s (leftList t)) (joinLists x (leftList v)) ≠ 0 := by
    change (coreSlice (nextCoreObservation p hp psi c) t v).value s x ≠ 0 at hn
    conv at hn => lhs; arg 1; rw [htn,hvn,nextCoreObservation_slice]
    exact hn
  obtain ⟨hpsi,hcore,hout⟩ := orderedCutForm_nonzero_factors p hp _ c s (leftList t) x (leftList v) hh
  obtain ⟨hP,hQold⟩ := hs _ _ _ _ hpsi
  refine ⟨fun i => ⟨?_,hcore i⟩,?_⟩
  · have hi := hP (cutOrder c (finSumFinEquiv (Sum.inl i)))
    simpa only [Function.comp_apply,Equiv.symm_apply_apply,joinLists_left] using hi
  · intro i
    obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
    cases j with
    | inl j => exact hQ _ (hout j)
    | inr j => exact hQold j

lemma SplitPositionSupport.mono {N M : ℕ} {psi : FormVector (N+M)} {P Q P' Q' : Space → Prop}
    (hs : SplitPositionSupport psi P Q) (hP : ∀ z, P z → P' z) (hQ : ∀ z, Q z → Q' z) :
    SplitPositionSupport psi P' Q' := by
  intro s t x v hn
  obtain ⟨hx,hv⟩ := hs s t x v hn
  exact ⟨fun i => hP _ (hx i),fun i => hQ _ (hv i)⟩

namespace CoreObservationGraph
 def supported (G : CoreObservationGraph) (P Q : Space → Prop) : Prop :=
    SplitPositionSupport G.vector P Q
 lemma initial_supported {N : ℕ} (psi : FormVector N) (hpsi : SobolevFermion psi) (Q : Space → Prop) :
    (initial psi hpsi).supported (fun _ => True) Q := by
    intro s t x v hn
    exact ⟨fun _ => trivial,fun i => Fin.elim0 i⟩
end CoreObservationGraph
namespace CoreObservationEnsemble
 def supported (E : CoreObservationEnsemble) (P Q : Space → Prop) : Prop :=
    ∀ i, (E.graph i).supported P Q
 lemma initial_supported {N : ℕ} (psi : FormVector N) (hpsi : SobolevFermion psi) (Q : Space → Prop) :
    (initial psi hpsi).supported (fun _ => True) Q :=
    fun _ => CoreObservationGraph.initial_supported psi hpsi Q
 lemma observe_supported (E : CoreObservationEnsemble) {P Q : Space → Prop}
    (hs : E.supported P Q) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2=1) (hQ : ∀ z, (p 1).value z ≠ 0 → Q z) :
    (E.observe p hp).supported (fun z => P z ∧ (p 0).value z ≠ 0) Q :=
    fun ic => (hs ic.1).observe p hp hQ ic.2
end CoreObservationEnsemble

end
open MeasureTheory Set

lemma cell_core_nonzero_distance {y z : Space} (hy : y ≠ 0)
    (hn : (coreFirstRadialCut y (localCellRadius_pos hy).le (localCellRadius_pos hy) 0).value z ≠ 0) :
    localCellRadius y ≤ ‖z-y‖ := by
  by_contra hh
  exact hn (coreFirstRadialCut_core_zero y (localCellRadius_pos hy).le
    (localCellRadius_pos hy) z hh)

lemma cell_out_nonzero_norm {u : ℝ} (hu : 0 < u) {y z : Space}
    (hy : y ≠ 0) (hlo : u/2 ≤ ‖y‖)
    (hn : (coreFirstRadialCut y (localCellRadius_pos hy).le (localCellRadius_pos hy) 1).value z ≠ 0) :
    u/4 ≤ ‖z‖ := by
  have hd : ‖z-y‖ < localCellRadius y+localCellRadius y := by
    by_contra! hh
    exact hn (coreFirstRadialCut_out_zero y (localCellRadius_pos hy).le (localCellRadius_pos hy) z hh)
  have ht := norm_le_norm_sub_add y z
  rw [norm_sub_rev y z] at ht
  unfold localCellRadius at hd
  linarith

namespace CoreObservationEnsemble
lemma observeCells_supported (E : CoreObservationEnsemble) {P Q : Space → Prop}
    (hE : E.supported P Q) (ys : List Space)
    (hys : ∀ y ∈ ys, ∃ hy : y ≠ 0, ∀ z,
      (coreFirstRadialCut y (localCellRadius_pos hy).le (localCellRadius_pos hy) 1).value z ≠ 0 → Q z) :
    (E.observeCells ys).supported (fun z => P z ∧ ∀ y ∈ ys, localCellRadius y ≤ ‖z-y‖) Q := by
  induction ys generalizing E P with
  | nil =>
    exact fun i => (hE i).mono (fun _ h => ⟨h,by simp⟩) (fun _ h => h)
  | cons y ys ih =>
    obtain ⟨hy,hQ⟩ := hys y (List.mem_cons_self ..)
    have hs : (E.observeCell y).supported (fun z => P z ∧ localCellRadius y ≤ ‖z-y‖) Q := by
      rw [observeCell,dite_eq_right hy]
      intro i
      exact ((E.observe_supported hE _ _ hQ) i).mono
        (fun z h => ⟨h.1,cell_core_nonzero_distance hy h.2⟩) (fun _ h => h)
    have hh := ih _ hs (fun z hz => hys z (List.mem_cons_of_mem y hz))
    intro i
    exact (hh i).mono (fun z h => ⟨h.1.1,fun w hw => by
      rcases List.mem_cons.mp hw with rfl | hw
      · exact h.1.2
      · exact h.2 w hw⟩) (fun _ h => h)

lemma annular_stencil_support {N : ℕ} (psi : FormVector N) (hpsi : SobolevFermion psi)
    {u : ℝ} (hu : 0 < u) (ys : List Space)
    (hys : ∀ y ∈ ys, u/2 ≤ ‖y‖)
    (hcover : ∀ z : Space, u/2 ≤ ‖z‖ → ‖z‖ ≤ 4*u → ∃ y ∈ ys, ‖z-y‖ < localCellRadius y) :
    ((initial psi hpsi).observeCells ys).supported
      (fun z => ¬(u/2 ≤ ‖z‖ ∧ ‖z‖ ≤ 4*u)) (fun z => u/4 ≤ ‖z‖) := by
  have hs := (initial psi hpsi).observeCells_supported (initial_supported psi hpsi (fun z => u/4 ≤ ‖z‖)) ys
    (by
      intro y hy
      have hn : y ≠ 0 := norm_pos_iff.mp (by linarith [hys y hy])
      refine ⟨hn,fun z hz => cell_out_nonzero_norm hu hn (hys y hy) hz⟩)
  intro i
  exact (hs i).mono (fun z hz h => by
    obtain ⟨y,hy,hd⟩ := hcover z h.1 h.2
    exact (not_lt_of_ge (hz.2 y hy)) hd) (fun _ h => h)
end CoreObservationEnsemble

end CoulombAtom

end

end OAI
end


