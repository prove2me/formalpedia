-- Prove2me | Definitions.Def_OAIQ071C010
-- name    : OAIQ071C010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T05:22:21.359249+00:00
-- url     : https://prove2.me/theorems/6937b3e0-1383-4d74-bd42-8ead453d9854
-- title:
--   Definitions bundle OAIQ071C010 of the split of OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 163 declarations of OpenAI's Lean: 57 definitions, 2 inductive types or structures and 104 theorems. The definitions and types are `OAI.CoulombAtom.HighInverseNumerics`, `OAI.CoulombAtom.InverseFiniteGeometry`, `OAI.CoulombAtom.LowInverseNumerics`, `OAI.CoulombAtom.OriginalPointInverseBounds`, `OAI.CoulombAtom.OwnProbabilityTailTiltState`, `OAI.CoulombAtom.SmallSectorResidual`, `OAI.CoulombAtom.TailTiltState`, `OAI.CoulombAtom.actualCellMomentConstant`, `OAI.CoulombAtom.actualScreenConstant`, `OAI.CoulombAtom.actualScreenRadius`, `OAI.CoulombAtom.actualShellRadius`, `OAI.CoulombAtom.canonicalMasterAmplitude`, `OAI.CoulombAtom.cellBootstrapCollar`, `OAI.CoulombAtom.cellCountErrorConstant`, `OAI.CoulombAtom.cellCountLeadingConstant`, `OAI.CoulombAtom.cellFieldNormConstant`, `OAI.CoulombAtom.cellUniversalCountConstant`, `OAI.CoulombAtom.dimensionlessLocalPotential`, `OAI.CoulombAtom.dimensionlessPatchRemainder`, `OAI.CoulombAtom.dimensionlessPotentialRemainder`, `OAI.CoulombAtom.dyadicInside`, `OAI.CoulombAtom.dyadicShell`, `OAI.CoulombAtom.freshHighThreshold`, `OAI.CoulombAtom.freshLowThreshold`, `OAI.CoulombAtom.inverseDensityError`, `OAI.CoulombAtom.inverseGapBudget`, `OAI.CoulombAtom.inversePotentialError`, `OAI.CoulombAtom.masterTailTest`, `OAI.CoulombAtom.oneBodyInnerField`, `OAI.CoulombAtom.ordinaryDensity`, `OAI.CoulombAtom.originalFieldCapBudget`, `OAI.CoulombAtom.originalHighFailure`, `OAI.CoulombAtom.originalLowFailure`, `OAI.CoulombAtom.originalQueryDensity`, `OAI.CoulombAtom.originalQueryField`, `OAI.CoulombAtom.physicalFieldCapBudget`, `OAI.CoulombAtom.quantumInverseCountConstant`, `OAI.CoulombAtom.radialPotentialError`, `OAI.CoulombAtom.rawExteriorCount`, `OAI.CoulombAtom.rawGradientWeight` and 19 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CoulombIonization_Fermionic_CutCountDomination`, `CoulombIonization_Fermionic_WeightedCoreStatistics`, `CoulombIonization_FieldAnalysis_CapProbabilityWeightBarrier`, `CoulombIonization_FieldAnalysis_CellFieldNormalizationBarrier`, `CoulombIonization_FieldAnalysis_ConditionalFieldIdentity`, `CoulombIonization_FieldAnalysis_ConditionalObservables`, `CoulombIonization_FieldAnalysis_ConditionalShellField`, `CoulombIonization_FieldAnalysis_DeletedFieldBudget`, `CoulombIonization_FieldAnalysis_LocalFieldScalarBoundBarrier`, `CoulombIonization_FieldAnalysis_ObservedFieldScale`, `CoulombIonization_FieldAnalysis_OwnProbabilityFieldCapBarrier`, `CoulombIonization_FieldAnalysis_PatchMassSubmeanBarrier`, `CoulombIonization_FieldAnalysis_ThinFieldConstantsBarrier`, `CoulombIonization_FieldAnalysis_ThinFieldFeedbackBarrier`, `CoulombIonization_FieldAnalysis_dShellInnerField`, `CoulombIonization_FormDomain_GraphWeightIntegral`, `CoulombIonization_Ionization_PricedAnnularCountBarrier`, `CoulombIonization_Ionization_PricedCoulombTail`, `CoulombIonization_Localization_ActualPointInverseBarrier`, `CoulombIonization_Localization_ConditionalRetainedGap`, `CoulombIonization_Localization_FiniteCellObservation`, `CoulombIonization_Localization_FormRawLaw`, `CoulombIonization_Localization_ObservedAnnularCountBarrier`, `CoulombIonization_Localization_ObservedInnerCap`, `CoulombIonization_Localization_OrdinaryDensity`, `CoulombIonization_RadialBounds_ActualBandInverseBarrier`, `CoulombIonization_RadialBounds_ActualLowInverseBarrier`, `CoulombIonization_RadialBounds_ActualTailTiltBarrier`, `CoulombIonization_RadialBounds_AnnularCellGeometryBarrier`, `CoulombIonization_RadialBounds_AnnularCutExcess`, `CoulombIonization_RadialBounds_BandInverseNumericsBarrier`, `CoulombIonization_RadialBounds_CellBudgetNormalizationBarrier`, `CoulombIonization_RadialBounds_CellCountAbsorptionBarrier`, `CoulombIonization_RadialBounds_CellCountSupremumBarrier`, `CoulombIonization_RadialBounds_CoulombTailNumerics`, `CoulombIonization_RadialBounds_ExpectedRadialCapBarrier`, `CoulombIonization_RadialBounds_ExteriorScreenNumerics`, `CoulombIonization_RadialBounds_FiniteBarrier`, `CoulombIonization_RadialBounds_FreshInnerCountsBarrier`, `CoulombIonization_RadialBounds_FreshRetainedMassBarrier`, `CoulombIonization_RadialBounds_InverseNumericalStatementsBarrier`, `CoulombIonization_RadialBounds_LocalBallTraceBarrier`, `CoulombIonization_RadialBounds_LocalOrdinaryBarrier`, `CoulombIonization_RadialBounds_MasterExteriorStatistic`, `CoulombIonization_RadialBounds_NormalizedMasterEvent`, `CoulombIonization_RadialBounds_OwnProbabilityTailTiltBarrier`, `CoulombIonization_RadialBounds_PatchAverageSubmeanBarrier`, `CoulombIonization_RadialBounds_PatchFailureMass`, `CoulombIonization_RadialBounds_RadialCountSelection`, `CoulombIonization_RadialBounds_RadialPatchGeometry`, `CoulombIonization_RadialBounds_RadialSelectedCounts`, `CoulombIonization_RadialBounds_RootMomentCauchyBarrier`, `CoulombIonization_RadialBounds_SelectionBudget`, `CoulombIonization_RadialBounds_SharpErrorLimitBarrier`, `CoulombIonization_RadialBounds_SharpFreshPatchBarrier`, `CoulombIonization_RadialBounds_SharpLocalPotentialBarrier`, `CoulombIonization_RadialBounds_ShellAbsorptionNumerics`, `CoulombIonization_RadialBounds_ShellBias`, `CoulombIonization_RadialBounds_ShellTelescoping`, `CoulombIonization_RadialBounds_UnshiftedCellCountBarrier`, `CoulombIonization_ThomasFermi_CellCountFeedbackBarrier`, `CoulombIonization_ThomasFermi_CutMomentBounds`, `CoulombIonization_ThomasFermi_RadialPatchCap`, `CoulombIonization_Variational_FreshPatchBudget`, `CoulombIonization_Variational_OutRetainedLower`, `CoulombIonization_Variational_OwnStateResidual`, `CoulombIonization_Variational_SelectedMasterComparison`, `CoulombIonization_Variational_SelectedPatchBudget`.
--
--   **Imports.** It imports the published bundle `Def_CoulombIonization`; the bundles `OAIQ071C008` and `OAIQ071C009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ071C013`, `OAIQ071C014` and `OAIQ071C015`; the statements `OAI.CoulombAtom.OwnProbabilityTailTiltState.expandedAnnulus_small_event_integral`, `OAI.CoulombAtom.OwnProbabilityTailTiltState.rare_cap_event_of_cell`, `OAI.CoulombAtom.TailTiltState.event_radial_comparison_of_cell`, `OAI.CoulombAtom.actual_expandedAnnulus_inverse_uniform_eventually`, `OAI.CoulombAtom.actual_scaled_original_cap_eventually`, `OAI.CoulombAtom.actual_shell_number`, `OAI.CoulombAtom.exists_actual_fullAnnulus_inverse_constant`, `OAI.CoulombAtom.exists_actual_own_probability_tail_tilt_state`, `OAI.CoulombAtom.exists_own_state_exterior_number`, `OAI.CoulombAtom.exists_own_state_shell_residual`, `OAI.CoulombAtom.ordinaryDensity_global_unshifted`, `OAI.CoulombAtom.sharp_cell_local_potential`, `OAI.CoulombAtom.sharp_joint_selected_patch`, `OAI.CoulombBarrier.actual_outward_barrier_given_state_eventually`, `OAI.CoulombBarrier.exists_actual_selected_data_constants`, `OAI.CoulombBarrier.selected_data_profile_subsequence` and `OAI.CoulombBarrier.tail_initial_good_event`; the proofs of `OAI.CoulombAtom.OwnProbabilityTailTiltState.expandedAnnulus_small_event_integral`, `OAI.CoulombAtom.OwnProbabilityTailTiltState.rare_cap_event_of_cell`, `OAI.CoulombAtom.TailTiltState.event_radial_comparison_of_cell`, `OAI.CoulombAtom.actual_expandedAnnulus_inverse_uniform_eventually`, `OAI.CoulombAtom.actual_scaled_original_cap_eventually`, `OAI.CoulombAtom.actual_shell_number`, `OAI.CoulombAtom.actual_uniform_upper_deficit`, `OAI.CoulombAtom.exists_actual_fullAnnulus_inverse_constant`, `OAI.CoulombAtom.exists_actual_own_probability_tail_tilt_state`, `OAI.CoulombAtom.exists_own_state_exterior_number`, `OAI.CoulombAtom.exists_own_state_shell_residual`, `OAI.CoulombAtom.generalized_ionization`, `OAI.CoulombAtom.normalized_inner_event_global_bound`, `OAI.CoulombAtom.ordinaryDensity_global_unshifted`, `OAI.CoulombAtom.sharp_cell_local_potential`, `OAI.CoulombAtom.sharp_joint_selected_patch`, `OAI.CoulombBarrier.actual_outward_barrier_given_state_eventually`, `OAI.CoulombBarrier.exists_actual_selected_data_constants`, `OAI.CoulombBarrier.selected_data_profile_subsequence`, `OAI_CoulombBarrier_selected_screened_profile` and `OAI.CoulombBarrier.tail_initial_good_event`.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C008
import Definitions.Def_OAIQ071C009

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_FormRawLaw
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma formRawLaw_probability {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (hm : formMass ψ = 1) : IsProbabilityMeasure (formRawLaw ψ) := by
  constructor
  rw [formRawLaw_univ hψ,hm,ENNReal.ofReal_one]

theorem radial_raw_radius_selection {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hba : b < a) :
    ∃ t ∈ Icc (5*a) (6*a),
      (∫ x, rawStripCount y t b x^2 ∂formRawLaw ψ) ≤
        (8*b/a)*(∫ x, rawBallCount y (7*a) x^2 ∂formRawLaw ψ) := by
  let : IsFiniteMeasure (formRawLaw ψ) := formRawLaw_finite hψ
  have hd (i : Fin N) : Measurable (fun x : Configuration N => ‖x i-y‖) :=
    configuration_distance_measurable y i
  obtain ⟨t,ht,hh⟩ := exists_radius_expected_square hd (formRawLaw ψ)
    (lo := 5*a) (hi := 6*a) (l := 7*b) (r := b) (by linarith) (by linarith)
  refine ⟨t,ht,?_⟩
  have he : (7*b+b)/(6*a-5*a) = 8*b/a := by congr 1 <;> ring
  rw [he] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by positivity) ha.le)
  apply integral_mono (upperCount_sq_integrable hd (6*a+b)) (rawBallCount_sq_integrable y (7*a) _)
  intro x
  exact pow_le_pow_left₀ (upperCount_nonneg _ _)
    (upperCount_le_rawBallCount y (by linarith) x) 2

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_ConditionalFieldIdentity
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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

theorem priced_conditional_energy_identity {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z lam : ℝ) :
    formEnergy Z ψ+lam*(N+M)*formMass ψ =
      (∑ t : Spins M, ∫ y, formEnergy Z (coreSlice ψ t y)+
        lam*N*formMass (coreSlice ψ t y))+
      outKinetic ψ-(∑ t : Spins M, ∫ y, conditionalFieldSum Z lam ψ t y)+
      outRepulsion ψ := by
  have ht (t : Spins M) : (∫ y, formEnergy Z (coreSlice ψ t y)+
      lam*N*formMass (coreSlice ψ t y)) =
      (∫ y, formEnergy Z (coreSlice ψ t y))+lam*N*(∫ y, formMass (coreSlice ψ t y)) := by
    rw [integral_add (hψ.coreSlice_energy_integrable Z t)
      ((hψ.coreSlice_mass_integrable t).const_mul (lam*N)),integral_const_mul]
  simp_rw [ht]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,hψ.integral_coreSlice_mass,
    integrated_core_parts hψ Z,integral_conditionalFieldSum hψ Z lam,
    formEnergy_core_out_cross]
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_ConditionalObservables
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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
open CoulombNeumann

lemma conditionalFieldParticle_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z lam : ℝ) (s : Spins M) (i : Fin M) :
    Integrable (fun x => formMass (coreSlice ψ s x)*normalizedCoreField Z lam (coreSlice ψ s x) (x i)) := by
  have hh := (((coreSlice_mass_div_integrable hψ s i).const_mul Z).sub
    (coreSlice_cross_integrable hψ s i)).sub ((hψ.coreSlice_mass_integrable s).const_mul lam)
  apply hh.congr
  filter_upwards [hψ.ae_coreSlice s] with x hx
  simp only [Pi.sub_apply]
  rw [mul_comm (formMass _),normalizedCoreField_mul_mass hx]
  ring

lemma conditionalRetainedFieldSum_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z lam : ℝ) (s : Spins M)
    (S : Configuration M → Finset (Fin M)) (hS : ∀ i, MeasurableSet {x | i ∈ S x}) :
    Integrable (conditionalRetainedFieldSum Z lam ψ s S) := by
  classical
  have hi (i : Fin M) := (conditionalFieldParticle_integrable hψ Z lam s i).indicator (hS i)
  have he (x : Configuration M) : conditionalRetainedFieldSum Z lam ψ s S x =
      ∑ i : Fin M, if i ∈ S x then
        formMass (coreSlice ψ s x)*normalizedCoreField Z lam (coreSlice ψ s x) (x i) else 0 := by
    simp only [conditionalRetainedFieldSum,Finset.mul_sum,Finset.sum_ite_mem,Finset.univ_inter]
  change Integrable (fun x => conditionalRetainedFieldSum Z lam ψ s S x)
  simp_rw [he]
  exact integrable_finsetSum _ (fun i _ => by
    convert hi i using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    simp only [Set.indicator_apply,Set.mem_ofPred_eq])

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ConditionalRetainedGap
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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

lemma weightedPatchGap_nonneg {N M : ℕ} (ψ : FormVector (N+M)) (t : Spins M)
    (Z lam : ℝ) (y : Space) (R : ℝ) {b : ℝ} (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (u : Configuration M) :
    0 ≤ weightedPatchGap ψ t Z lam y R hb S u :=
  mul_nonneg (formMass_nonneg _) (tfPatchGap_nonneg _ _ _ _ (retainedPatchLp_nonneg hb (S u) u y R))

theorem conditionalPatchGap_upper {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (ha : CoreAntisymmetric ψ) (t : Spins M)
    (y : Space) (R : ℝ) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g)
    (hgs : tsupport g ⊆ ball 0 1) {b : ℝ} (hb : 0 < b)
    (A : Set Space) (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (hsep : Disjoint A (packetRegion (scaledRealPacket b g) (closedBall y R)))
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hcs : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖)
    (S : Configuration M → Finset (Fin M))
    (hmargin : ∀ u, ∀ i ∈ S u, ‖u i-y‖+Real.sqrt 3*b ≤ R)
    (hret_nuc : ∀ u, ∀ i ∈ S u, Real.sqrt 3*b ≤ ‖u i‖)
    (hret_core : ∀ u, ∀ i ∈ S u, ∀ a ∈ A, Real.sqrt 3*b ≤ ‖a-u i‖) :
    ∀ᵐ u : Configuration M,
      weightedPatchGap ψ t Z lam y R hb S u ≤
      corePriceExcess Z lam (coreSlice ψ t u)+
        tfKinetic*(retainedPressure b (S u) u*formMass (coreSlice ψ t u))-
        conditionalRetainedFieldSum Z lam ψ t S u+
        retainedDirect b (S u) u*formMass (coreSlice ψ t u)+
        ((packetDirichlet g/2)*b⁻¹^2)*weightedPatchMass ψ t Z lam y R u := by
  filter_upwards [ha.ae_coreSlice hψ t,
    conditionalPatchField_upper hψ t y R Z lam hb A hcore hnuc hcs] with u hu hfield
  have hf := normalizedCoreField_memLp_patch hu.sobolevVector A (hcore u) y R hb hb hnuc hcs Z lam
  have hh := conditional_retained_patch_gap hu y R (conditionalPatchField ψ t Z lam y R u)
    hZ hlam (conditionalPatchField_ae ψ t Z lam y R u hf) hfield
    hg hcg hgn hr hgs hb A (hcore u) hsep hnuc hcs (S u) u
    (hmargin u) (hret_nuc u) (hret_core u)
  dsimp only at hh
  change formMass (coreSlice ψ t u)*_ ≤ _
  unfold tfPatchGap
  unfold corePriceExcess conditionalRetainedFieldSum retainedDirect weightedPatchMass
  nlinarith

theorem weightedPatchGap_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (ha : CoreAntisymmetric ψ) (t : Spins M)
    (y : Space) {R : ℝ} (hR : 0 < R) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g)
    (hgs : tsupport g ⊆ ball 0 1) {b : ℝ} (hb : 0 < b)
    (A : Set Space) (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (hsep : Disjoint A (packetRegion (scaledRealPacket b g) (closedBall y R)))
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hcs : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖)
    (S : Configuration M → Finset (Fin M)) (hS : ∀ i, MeasurableSet {u | i ∈ S u})
    (hmargin : ∀ u, ∀ i ∈ S u, ‖u i-y‖+Real.sqrt 3*b ≤ R)
    (hret_nuc : ∀ u, ∀ i ∈ S u, Real.sqrt 3*b ≤ ‖u i‖)
    (hret_core : ∀ u, ∀ i ∈ S u, ∀ a ∈ A, Real.sqrt 3*b ≤ ‖a-u i‖) :
    Integrable (weightedPatchGap ψ t Z lam y R hb S) := by
  have hm := (hψ.coreSlice_mass_integrable t).aemeasurable.mul
    (conditionalPatchGap_aemeasurable hψ t Z lam y R hb S hS)
  have hi := ((((coreSlice_priceExcess_integrable hψ t Z lam).add
    ((retained_pressure_weighted_integrable hψ hb t S hS).const_mul tfKinetic)).sub
    (conditionalRetainedFieldSum_integrable hψ Z lam t S hS)).add
    (retained_direct_weighted_integrable hψ hb t S hS)).add
    ((weightedPatchMass_integrable hψ t y hR Z lam hb A hcore hnuc hcs).const_mul
      ((packetDirichlet g/2)*b⁻¹^2))
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [conditionalPatchGap_upper hψ ha t y R hZ hlam hg hcg hgn hr hgs
    hb A hcore hsep hnuc hcs S hmargin hret_nuc hret_core] with u hu
  simp only [Pi.mul_apply,Pi.add_apply,Pi.sub_apply]
  change ‖weightedPatchGap ψ t Z lam y R hb S u‖ ≤ _
  rw [Real.norm_of_nonneg (weightedPatchGap_nonneg ψ t Z lam y R hb S u)]
  exact hu

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_OutRetainedLower
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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

lemma priced_core_excess_identity {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z lam : ℝ) :
    formEnergy Z ψ+lam*(N+M)*formMass ψ-priceEnergy (energy Z) lam*formMass ψ =
      (∑ t : Spins M, ∫ u, corePriceExcess Z lam (coreSlice ψ t u))+
      outKinetic ψ-(∑ t : Spins M, ∫ u, conditionalFieldSum Z lam ψ t u)+outRepulsion ψ := by
  rw [integral_coreSlice_priceExcess hψ Z lam,priced_conditional_energy_identity hψ Z lam]
  ring

theorem integrated_conditional_patch_budget {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (hc : CoreAntisymmetric ψ)
    (ho : CoreAntisymmetric (swapBlocks ψ)) (y : Space) {R : ℝ} (hR : 0 < R)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g)
    (hgs : tsupport g ⊆ ball 0 1) {b : ℝ} (hb : 0 < b)
    (A : Set Space) (hcore : ∀ t u x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (hsep : Disjoint A (packetRegion (scaledRealPacket b g) (closedBall y R)))
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hcs : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖)
    (S : Spins M → Configuration M → Finset (Fin M))
    (hS : ∀ t i, MeasurableSet {u | i ∈ S t u})
    (hmargin : ∀ t u, ∀ i ∈ S t u, ‖u i-y‖+Real.sqrt 3*b ≤ R)
    (hret_nuc : ∀ t u, ∀ i ∈ S t u, Real.sqrt 3*b ≤ ‖u i‖)
    (hret_core : ∀ t u, ∀ i ∈ S t u, ∀ a ∈ A, Real.sqrt 3*b ≤ ‖a-u i‖) :
    (∑ t : Spins M, ∫ u, weightedPatchGap ψ t Z lam y R hb (S t) u) ≤
      formEnergy Z ψ+lam*(N+M)*formMass ψ-priceEnergy (energy Z) lam*formMass ψ+
        b⁻¹^2*neumannRemainderConstant*((M:ℝ)^(4/3:ℝ)+(M:ℝ))*formMass ψ+
        (((2*Real.pi+1)/2)*(M:ℝ)/b)*formMass ψ+
        (∑ t : Spins M, ∫ u, conditionalFieldSum Z lam ψ t u-
          conditionalRetainedFieldSum Z lam ψ t (S t) u+
          ((packetDirichlet g/2)*b⁻¹^2)*weightedPatchMass ψ t Z lam y R u) := by
  have hmass (t : Spins M) := weightedPatchMass_integrable hψ t y hR Z lam hb A (hcore t) hnuc hcs
  have hgap (t : Spins M) := weightedPatchGap_integrable hψ hc t y hR hZ hlam hg hcg hgn hr hgs
    hb A (hcore t) hsep hnuc hcs (S t) (hS t) (hmargin t) (hret_nuc t) (hret_core t)
  have hexc (t : Spins M) := coreSlice_priceExcess_integrable hψ t Z lam
  have hpress (t : Spins M) := retained_pressure_weighted_integrable hψ hb t (S t) (hS t)
  have hfield (t : Spins M) := conditionalRetainedFieldSum_integrable hψ Z lam t (S t) (hS t)
  have hdirect (t : Spins M) := retained_direct_weighted_integrable hψ hb t (S t) (hS t)
  have ht (t : Spins M) : (∫ u, weightedPatchGap ψ t Z lam y R hb (S t) u) ≤
      (∫ u, corePriceExcess Z lam (coreSlice ψ t u))+
        tfKinetic*(∫ u, retainedPressure b (S t u) u*formMass (coreSlice ψ t u))-
        (∫ u, conditionalRetainedFieldSum Z lam ψ t (S t) u)+
        (∫ u, retainedDirect b (S t u) u*formMass (coreSlice ψ t u))+
        ((packetDirichlet g/2)*b⁻¹^2)*(∫ u, weightedPatchMass ψ t Z lam y R u) := by
    have h1 := (hexc t).add ((hpress t).const_mul tfKinetic)
    have h2 := h1.sub (hfield t)
    have h3 := h2.add (hdirect t)
    have h4 := (hmass t).const_mul ((packetDirichlet g/2)*b⁻¹^2)
    have ht := integral_mono_ae (hgap t) (h3.add h4)
      (conditionalPatchGap_upper hψ hc t y R hZ hlam hg hcg hgn hr hgs hb A
        (hcore t) hsep hnuc hcs (S t) (hmargin t) (hret_nuc t) (hret_core t))
    have e1 := integral_add (hexc t) ((hpress t).const_mul tfKinetic)
    have e2 := integral_sub h1 (hfield t)
    have e3 := integral_add h2 (hdirect t)
    have e4 := integral_add h3 h4
    simp only [Pi.add_apply,Pi.sub_apply,integral_const_mul] at ht e1 e2 e3 e4
    rwa [e4,e3,e2,e1] at ht
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun t _ => ht t)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum] at hs
  have hk := out_retained_kinetic hψ ho hb S hS
  have hrp := out_retained_repulsion hψ ho hb S hS
  have hid := priced_core_excess_identity hψ Z lam
  have herr (t : Spins M) : (∫ u, conditionalFieldSum Z lam ψ t u-
      conditionalRetainedFieldSum Z lam ψ t (S t) u+
      ((packetDirichlet g/2)*b⁻¹^2)*weightedPatchMass ψ t Z lam y R u) =
      (∫ u, conditionalFieldSum Z lam ψ t u)-
      (∫ u, conditionalRetainedFieldSum Z lam ψ t (S t) u)+
      ((packetDirichlet g/2)*b⁻¹^2)*(∫ u, weightedPatchMass ψ t Z lam y R u) := by
    have e1 := integral_sub (conditionalFieldSum_integrable hψ Z lam t) (hfield t)
    have e2 := integral_add ((conditionalFieldSum_integrable hψ Z lam t).sub (hfield t))
      ((hmass t).const_mul ((packetDirichlet g/2)*b⁻¹^2))
    simp only [Pi.sub_apply,integral_const_mul] at e2
    rw [e2,e1]
  simp_rw [herr]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum]
  linarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_FreshPatchBudget
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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

lemma fresh_cut_total_excess_identity {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevVector ψ) (Z lam : ℝ) :
    (∑ c : Fin L → Fin 2, corePriceExcess Z lam (orderedCutForm p hp ψ c)) =
      corePriceExcess Z lam ψ+(1/2:ℝ)*weightedParticleCount ψ (spatialErrorWeight p) := by
  have hn (c : Fin L → Fin 2) : ((cutCoreNumber c+cutOutNumber c:ℕ):ℝ) = L := by
    exact_mod_cast cutNumbers_sum c
  simp_rw [corePriceExcess,hn,orderedCutForm_energy,orderedCutForm_mass]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,
    spatial_cut_mass p hp hψ,spatial_cut_ims p hp hψ Z]
  unfold weightedParticleCount
  ring

theorem fresh_cut_patch_budget {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (y : Space) {R : ℝ} (hR : 0 < R)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g)
    (hgs : tsupport g ⊆ ball 0 1) {b : ℝ} (hb : 0 < b)
    (A : Set Space)
    (hv : ∀ x ∉ A, (p 0).value x = 0)
    (hd : ∀ x ∉ A, ∀ a, lineDeriv ℝ (p 0).value x (spaceDirections a) = 0)
    (hsep : Disjoint A (packetRegion (scaledRealPacket b g) (closedBall y R)))
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hcs : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖)
    (S : OuterCutRetention L)
    (hS : ∀ c t i, MeasurableSet {u | i ∈ S c t u})
    (hmargin : ∀ c t u, ∀ i ∈ S c t u, ‖u i-y‖+Real.sqrt 3*b ≤ R)
    (hret_nuc : ∀ c t u, ∀ i ∈ S c t u, Real.sqrt 3*b ≤ ‖u i‖)
    (hret_core : ∀ c t u, ∀ i ∈ S c t u, ∀ a ∈ A, Real.sqrt 3*b ≤ ‖a-u i‖) :
    (∑ c : Fin L → Fin 2, ∑ t : Spins (cutOutNumber c), ∫ u,
      weightedPatchGap (orderedCutForm p hp ψ c) t Z lam y R hb (S c t) u) ≤
      corePriceExcess Z lam ψ+(1/2:ℝ)*weightedParticleCount ψ (spatialErrorWeight p)+
        b⁻¹^2*neumannRemainderConstant*(∑ c : Fin L → Fin 2,
          ((cutOutNumber c:ℝ)^(4/3:ℝ)+(cutOutNumber c:ℝ))*formMass (orderedCutForm p hp ψ c))+
        (((2*Real.pi+1)/2)/b)*(∑ c : Fin L → Fin 2,
          (cutOutNumber c:ℝ)*formMass (orderedCutForm p hp ψ c))+
        (∑ c : Fin L → Fin 2, ∑ t : Spins (cutOutNumber c), ∫ u,
          conditionalFieldSum Z lam (orderedCutForm p hp ψ c) t u-
          conditionalRetainedFieldSum Z lam (orderedCutForm p hp ψ c) t (S c t) u+
          ((packetDirichlet g/2)*b⁻¹^2)*weightedPatchMass (orderedCutForm p hp ψ c) t Z lam y R u) := by
  have hc (c : Fin L → Fin 2) (t : Spins (cutOutNumber c))
      (u : Configuration (cutOutNumber c)) (x : Configuration (cutCoreNumber c))
      (i : Fin (cutCoreNumber c)) (hi : x i ∉ A) :
      FormZeroAt (coreSlice (orderedCutForm p hp ψ c) t u) x := by
    apply FormZeroAt.coreSlice
    exact orderedCutForm_core_hole p hp ψ c Aᶜ hv hd (joinLists x u) i
      (by simpa only [joinLists_left,mem_compl_iff] using hi)
  have hbr (c : Fin L → Fin 2) := integrated_conditional_patch_budget
    (orderedCutForm_sobolev p hp hψ.sobolevVector c)
    (orderedCutForm_core_antisymmetric p hp hψ c)
    (orderedCutForm_out_antisymmetric p hp hψ c) y hR hZ hlam hg hcg hgn hr hgs hb A
    (hc c) hsep hnuc hcs (S c) (hS c) (hmargin c) (hret_nuc c) (hret_core c)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun c _ => hbr c)
  have he (c : Fin L → Fin 2) :
      formEnergy Z (orderedCutForm p hp ψ c)+lam*((cutCoreNumber c:ℝ)+cutOutNumber c)*
        formMass (orderedCutForm p hp ψ c)-priceEnergy (energy Z) lam*formMass (orderedCutForm p hp ψ c) =
      corePriceExcess Z lam (orderedCutForm p hp ψ c) := by
    simp only [corePriceExcess,Nat.cast_add]
  have hd (c : Fin L → Fin 2) : (((2*Real.pi+1)/2)*(cutOutNumber c:ℝ)/b)*
      formMass (orderedCutForm p hp ψ c) =
      (((2*Real.pi+1)/2)/b)*((cutOutNumber c:ℝ)*formMass (orderedCutForm p hp ψ c)) := by ring
  simp only [he] at hh
  simp only [hd,Finset.sum_add_distrib,mul_assoc,←Finset.mul_sum] at hh
  rw [fresh_cut_total_excess_identity p hp hψ.sobolevVector Z lam] at hh
  simpa only [mul_assoc] using hh

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RadialPatchGeometry
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis CoulombNeumann

theorem radial_fresh_patch_budget {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g)
    (hgs : tsupport g ⊆ ball 0 1) :
    let ht : 0 ≤ t := le_of_lt (lt_trans (by positivity : (0:ℝ) < 7*b) htb)
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    let S := radialPatchRetention L y t b
    (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      weightedPatchGap (orderedCutForm p hp ψ c) s Z lam y (t-4*b) hb (S c s) u) ≤
      corePriceExcess Z lam ψ+(1/2:ℝ)*weightedParticleCount ψ (spatialErrorWeight p)+
        b⁻¹^2*neumannRemainderConstant*(∑ c : Fin L → Fin 2,
          ((cutOutNumber c:ℝ)^(4/3:ℝ)+(cutOutNumber c:ℝ))*formMass (orderedCutForm p hp ψ c))+
        (((2*Real.pi+1)/2)/b)*(∑ c : Fin L → Fin 2,
          (cutOutNumber c:ℝ)*formMass (orderedCutForm p hp ψ c))+
        (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          conditionalFieldSum Z lam (orderedCutForm p hp ψ c) s u-
          conditionalRetainedFieldSum Z lam (orderedCutForm p hp ψ c) s (S c s) u+
          ((packetDirichlet g/2)*b⁻¹^2)*weightedPatchMass (orderedCutForm p hp ψ c) s Z lam y (t-4*b) u) := by
  dsimp only
  apply fresh_cut_patch_budget _ _ hψ y (by linarith) hZ hlam hg hcg hgn hr hgs hb
    (radialPatchCore y t)
  · exact coreFirstRadialCut_core_zero y _ hb
  · exact coreFirstRadialCut_core_deriv_zero y _ hb
  · exact radialPatch_packet_separation y hb hgs
  · exact radialPatch_nuclear_distance hb hy
  · exact radialPatch_core_distance y hb
  · exact radialPatchRetention_measurable L y t b
  · exact radialPatch_retained_margin y hb
  · exact radialPatch_retained_nuclear hb hy
  · exact radialPatch_retained_core y hb

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_CutCountDomination
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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

lemma radialCut_deleted_le_rawStrip {N : ℕ} (y : Space) {t b : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (c : Fin N → Fin 2) (x : Configuration N)
    (hx : (spatialProduct (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) c).value x ≠ 0) :
    cutDeletedCount y t b c x ≤ rawStripCount y t b x := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hh : c i ≠ 0 ∧ t-7*b ≤ ‖x i-y‖
  · have hd := radialCut_out_distance y ht hb c x hx i hh.1
    have hs : ‖x i-y‖-b ≤ t ∧ t ≤ ‖x i-y‖+7*b := ⟨by linarith,by linarith [hh.2]⟩
    simp [hh,slidingBit,hs]
  · simp only [hh,ite_false]
    exact slidingBit_nonneg _ _ _ _

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RadialCountSelection
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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

lemma radialCut_deleted_second_moment {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) :
    spatialCutExpectation (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ (fun c x => cutDeletedCount y t b c x^2) ≤
      ∫ x, rawStripCount y t b x^2 ∂formRawLaw ψ := by
  apply spatialCutExpectation_le_raw _ _ hψ
    (fun c => (cutDeletedCount_measurable y t b c).pow_const 2) (A := (N:ℝ)^2)
    (fun c x => norm_sq_le_of_nonneg (cutDeletedCount_nonneg _ _ _ _ _) (cutDeletedCount_le _ _ _ _ _))
    ((rawStripCount_measurable y t b).pow_const 2) (B := (N:ℝ)^2)
    (fun x => norm_sq_le_of_nonneg (rawStripCount_nonneg _ _ _ _) (rawStripCount_le _ _ _ _))
  intro c x hx
  exact pow_le_pow_left₀ (cutDeletedCount_nonneg _ _ _ _ _)
    (radialCut_deleted_le_rawStrip y ht hb c x hx) 2

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_RadialPatchCap
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAtom
open CoulombAnalysis

theorem radialPatchMinimizer_density_cap {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevVector ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (hbt : 4*b < t) (hy : t ≤ ‖y‖) (Z lam : ℝ) (c : Fin L → Fin 2)
    (s : Spins (cutOutNumber c)) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    let χ := orderedCutForm p hp ψ c
    ∀ᵐ u,
      let f := tfPatchMinimizer (t-4*b) tfKinetic tfKinetic_pos
        (conditionalPatchField χ s Z lam y (t-4*b) u)
      ∀ᵐ x ∂ballMeasure (t-4*b), ‖x‖ ≤ 3*(t-4*b)/4 →
        f x ≤ (tfPatchCapConstant/(t-4*b)^4/((5/3:ℝ)*tfKinetic))^(3/2:ℝ) := by
  dsimp only
  filter_upwards [(orderedCutForm_sobolev (coreFirstRadialCut y ht hb)
    (coreFirstRadialCut_partition y ht hb) hψ c).ae_coreSlice s] with u hu
  apply conditionalPatchMinimizer_density_cap _ s u hu (radialPatchCore y t) _ y
    (by linarith) hb hb (radialPatch_nuclear_distance hb hy)
    (radialPatch_core_distance y hb) Z lam
  intro x i hi
  apply FormZeroAt.coreSlice
  exact orderedCutForm_core_hole _ _ ψ c (radialPatchCore y t)ᶜ
    (coreFirstRadialCut_core_zero y ht hb) (coreFirstRadialCut_core_deriv_zero y ht hb)
    (joinLists x u) i (by simpa only [joinLists_left,mem_compl_iff] using hi)

end CoulombAtom

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_CutMomentBounds
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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

lemma radialCut_out_lower_moments {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (hm : formMass ψ = 1) (y : Space) {t b R : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hR : t+b ≤ R) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    let B := ∫ x, rawBallCount y R x^2 ∂formRawLaw ψ
    (∑ c : Fin N → Fin 2, (cutOutNumber c:ℝ)*formMass (orderedCutForm p hp ψ c)) ≤ B^(1/2:ℝ) ∧
    (∑ c : Fin N → Fin 2, ((cutOutNumber c:ℝ)^(4/3:ℝ)+(cutOutNumber c:ℝ))*
      formMass (orderedCutForm p hp ψ c)) ≤ B^(2/3:ℝ)+B^(1/2:ℝ) := by
  dsimp only
  have hB := radialCut_out_second_moment hψ y ht hb hR
  have h1 := cutOutMoment_le_bound _ _ hψ hm (r := 1) (by norm_num) (by norm_num) hB
  have h4 := cutOutMoment_le_bound _ _ hψ hm (r := 4/3) (by norm_num) (by norm_num) hB
  simp only [Real.rpow_one] at h1
  norm_num only [show (4/3:ℝ)/2 = 2/3 by norm_num] at h4
  refine ⟨h1,?_⟩
  simp only [add_mul,Finset.sum_add_distrib]
  exact add_le_add h4 h1

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_PatchFailureMass
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter Metric
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

lemma radial_weightedPatchGap_integrable {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    (c : Fin L → Fin 2) (s : Spins (cutOutNumber c)) :
    Integrable (weightedPatchGap (orderedCutForm (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ c) s Z lam y (t-4*b) hb (radialPatchRetention L y t b c s)) := by
  apply weightedPatchGap_integrable
    (orderedCutForm_sobolev (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) hψ.sobolevVector c)
    (orderedCutForm_core_antisymmetric (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) hψ c)
    s y (by linarith) hZ hlam hg hcg hgn hr hgs hb (radialPatchCore y t) _
    (radialPatch_packet_separation y hb hgs) (radialPatch_nuclear_distance hb hy)
    (radialPatch_core_distance y hb) _ (radialPatchRetention_measurable L y t b c s)
    (radialPatch_retained_margin y hb c s) (radialPatch_retained_nuclear hb hy c s)
    (radialPatch_retained_core y hb c s)
  intro u x i hi
  apply FormZeroAt.coreSlice
  exact orderedCutForm_core_hole _ _ ψ c (radialPatchCore y t)ᶜ
    (coreFirstRadialCut_core_zero y ht hb) (coreFirstRadialCut_core_deriv_zero y ht hb)
    (joinLists x u) i (by simpa only [joinLists_left,mem_compl_iff] using hi)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_DeletedFieldBudget
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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

lemma radial_deleted_field_le_max {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector L)
    (c : Fin L → Fin 2) (s : Spins (cutOutNumber c)) (y : Space) (t b Z lam : ℝ)
    (u : Configuration (cutOutNumber c)) :
    conditionalFieldSum Z lam (orderedCutForm p hp ψ c) s u-
      conditionalRetainedFieldSum Z lam (orderedCutForm p hp ψ c) s (radialPatchRetention L y t b c s) u ≤
      conditionalOutMaximum Z lam (orderedCutForm p hp ψ c) s u*
        outerDeletedCount y t b u*formMass (coreSlice (orderedCutForm p hp ψ c) s u) := by
  unfold conditionalFieldSum conditionalRetainedFieldSum radialPatchRetention
  rw [←mul_sub,mul_comm (formMass _)]
  apply mul_le_mul_of_nonneg_right _ (formMass_nonneg _)
  exact sum_deleted_field_le_max u y t b _ (conditionalField_le_outMaximum Z lam _ s u)

lemma radial_deleted_max_product_integrable {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hy : t+2*b ≤ ‖y‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (c : Fin L → Fin 2)
    (s : Spins (cutOutNumber c)) :
    let χ := orderedCutForm (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) ψ c
    Integrable (fun u => conditionalOutMaximum Z lam χ s u*outerDeletedCount y t b u*
      formMass (coreSlice χ s u)) := by
  dsimp only
  have hχ := orderedCutForm_sobolev (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) hψ c
  apply (hχ.coreSlice_mass_integrable s).bdd_mul
    ((conditionalOutMaximum_aemeasurable hχ s Z lam).mul (outerDeletedCount_measurable y t b).aemeasurable).aestronglyMeasurable
  apply ae_of_all; intro u
  simp only [Pi.mul_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (conditionalOutMaximum_nonneg _ _ _ _ _) (outerDeletedCount_nonneg _ _ _ _))]
  exact mul_le_mul (radial_conditionalOutMaximum_bound ψ y ht hb hy hZ hlam c s u)
    (outerDeletedCount_le y t b u) (outerDeletedCount_nonneg y t b u) (by positivity)

theorem radial_deleted_field_budget {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hy : t+2*b ≤ ‖y‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      conditionalFieldSum Z lam (orderedCutForm p hp ψ c) s u-
      conditionalRetainedFieldSum Z lam (orderedCutForm p hp ψ c) s (radialPatchRetention L y t b c s) u) ≤
      Real.sqrt (freshOutMaximumSecondMoment p hp ψ Z lam)*
        Real.sqrt (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          outerDeletedCount y t b u^2*formMass (coreSlice (orderedCutForm p hp ψ c) s u)) := by
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  dsimp only
  have hh := weighted_sum_integral_cauchy
    (ι := Σ c : Fin L → Fin 2, Spins (cutOutNumber c))
    (X := fun cs => Configuration (cutOutNumber cs.1)) (fun _ => volume)
    (fun cs u => formMass (coreSlice (orderedCutForm p hp ψ cs.1) cs.2 u))
    (fun cs u => conditionalOutMaximum Z lam (orderedCutForm p hp ψ cs.1) cs.2 u)
    (fun _ u => outerDeletedCount y t b u)
    (fun _ _ => formMass_nonneg _)
    (fun cs => radial_outMaximum_square_integrable hψ y ht hb hy hZ hlam cs.1 cs.2)
    (fun cs => weighted_outerDeleted_sq_integrable (orderedCutForm_sobolev p hp hψ cs.1) cs.2 y t b)
    (fun cs => radial_deleted_max_product_integrable hψ y ht hb hy hZ hlam cs.1 cs.2)
  simp only [Fintype.sum_sigma] at hh
  apply le_trans _ hh
  apply Finset.sum_le_sum; intro c _
  apply Finset.sum_le_sum; intro s _
  have hχ := orderedCutForm_sobolev p hp hψ c
  apply integral_mono
    ((conditionalFieldSum_integrable hχ Z lam s).sub
      (conditionalRetainedFieldSum_integrable hχ Z lam s _ (radialPatchRetention_measurable L y t b c s)))
    (radial_deleted_max_product_integrable hψ y ht hb hy hZ hlam c s)
  exact radial_deleted_field_le_max p hp ψ c s y t b Z lam

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RadialSelectedCounts
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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

lemma collar_count_le_strip_first {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) {t b : ℝ} (hb : 0 ≤ b) :
    weightedParticleCount ψ (fun z => if t ≤ ‖z-y‖ ∧ ‖z-y‖ ≤ t+b then 1 else 0) ≤
      ∫ x, rawStripCount y t b x ∂formRawLaw ψ := by
  let w : Space → ℝ := fun z => if t ≤ ‖z-y‖ ∧ ‖z-y‖ ≤ t+b then 1 else 0
  have hw : Measurable w := measurable_const.ite
    (((isClosed_le continuous_const ((continuous_id.sub continuous_const).norm)).inter
      (isClosed_le ((continuous_id.sub continuous_const).norm) continuous_const)).measurableSet)
    measurable_const
  have hB : ∀ x, ‖w x‖ ≤ 1 := by intro x; unfold w; split_ifs <;> norm_num
  change weightedParticleCount ψ w ≤ _
  rw [weightedParticleCount_eq_rawLaw hψ hw hB]
  have := formRawLaw_finite hψ
  have hi : Integrable (fun x : Configuration N => ∑ i, w (x i)) (formRawLaw ψ) := by
    apply Integrable.of_bound (Finset.measurable_sum _ (fun i _ => hw.comp (measurable_pi_apply i))).aestronglyMeasurable (N:ℝ)
    apply ae_of_all; intro x
    calc
      _ ≤ ∑ i, ‖w (x i)‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Fin N, (1:ℝ) := Finset.sum_le_sum (fun i _ => hB (x i))
      _ = N := by simp
  have hj : Integrable (rawStripCount (N := N) y t b) (formRawLaw ψ) :=
    Integrable.of_bound (rawStripCount_measurable y t b).aestronglyMeasurable (N:ℝ)
      (ae_of_all _ (fun x => by
        rw [Real.norm_of_nonneg (rawStripCount_nonneg y t b x)]
        exact rawStripCount_le y t b x))
  apply integral_mono hi hj
  intro x
  rw [rawStripCount,CoulombRadialAveraging.slidingCount]
  apply Finset.sum_le_sum; intro i _
  unfold w CoulombRadialAveraging.slidingBit
  split_ifs with h1 h2 h2
  · norm_num
  · exfalso
    apply h2
    constructor <;> linarith [h1.1,h1.2]
  · norm_num
  · norm_num

theorem radial_fresh_selected_counts {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (hm : formMass ψ = 1) (y : Space) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b < a) :
    ∃ t ∈ Icc (5*a) (6*a), ∃ ht : 0 ≤ t,
      let p := coreFirstRadialCut y ht hb
      let hp := coreFirstRadialCut_partition y ht hb
      let B := ∫ x, rawBallCount y (7*a) x^2 ∂formRawLaw ψ
      (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        outerDeletedCount y t b u^2*formMass (coreSlice (orderedCutForm p hp ψ c) s u)) ≤ (8*b/a)*B ∧
      (∑ c : Fin N → Fin 2, (cutOutNumber c:ℝ)*formMass (orderedCutForm p hp ψ c)) ≤ B^(1/2:ℝ) ∧
      (∑ c : Fin N → Fin 2, ((cutOutNumber c:ℝ)^(4/3:ℝ)+(cutOutNumber c:ℝ))*
        formMass (orderedCutForm p hp ψ c)) ≤ B^(2/3:ℝ)+B^(1/2:ℝ) ∧
      (1/2:ℝ)*weightedParticleCount ψ (spatialErrorWeight p) ≤
        (3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2*((8*b/a)*B)^(1/2:ℝ) := by
  obtain ⟨t,ht,hdel⟩ := radial_raw_radius_selection hψ y ha hb.le hba
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hout := radialCut_out_lower_moments hψ hm y ht0 hb (R := 7*a) (by linarith [ht.2])
  refine ⟨t,ht,ht0,?_,hout.1,hout.2,?_⟩
  · rw [outerDeleted_second_moment_eq_cut _ _ hψ]
    exact (radialCut_deleted_second_moment hψ y ht0 hb).trans hdel
  · have := formRawLaw_probability hψ hm
    have hfirst := bounded_probability_first_le_second (formRawLaw ψ)
      (rawStripCount_measurable y t b) (rawStripCount_nonneg y t b) (rawStripCount_le y t b)
    have hh := (collar_count_le_strip_first hψ y hb.le).trans hfirst
    have hbnd := Real.rpow_le_rpow (integral_nonneg (fun x => sq_nonneg (rawStripCount y t b x))) hdel
      (by norm_num : (0:ℝ) ≤ 1/2)
    exact (radial_fresh_ims_bound hψ y ht0 hb).trans
      (mul_le_mul_of_nonneg_left (hh.trans hbnd) (by positivity))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RootMomentCauchyBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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

lemma rawCountMoment_le_cover {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) (R : ℝ) (T : Finset Space) (r : Space → ℝ)
    (hcover : ∀ z : Space, ‖z-y‖ < R → ∃ v ∈ T, ‖z-v‖ < r v) :
    rawCountMoment ψ y R ≤ (T.card:ℝ)*∑ v ∈ T, rawCountMoment ψ v (r v) := by
  classical
  have hb (z : Space) (s : ℝ) (t : Spins N) :
      Integrable (fun x => rawBallCount z s x^2*‖ψ.value t x‖^2) :=
    rawFormPair_integrable hψ ((rawBallCount_measurable z s).pow_const 2)
      (fun _ => norm_sq_le_of_nonneg (rawBallCount_nonneg _ _ _) (rawBallCount_le _ _ _)) t
  have hpoint (x : Configuration N) : rawBallCount y R x^2 ≤
      (T.card:ℝ)*∑ v ∈ T, rawBallCount v (r v) x^2 := by
    calc _ ≤ (∑ v ∈ T, rawBallCount v (r v) x)^2 :=
           pow_le_pow_left₀ (rawBallCount_nonneg _ _ _) (rawBallCount_le_cover x y R T r hcover) 2
         _ ≤ _ := sq_sum_le_card_mul_sum_sq
  unfold rawCountMoment rawFormPair
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  calc
    _ ≤ ∫ x, (T.card:ℝ)*(∑ v ∈ T, rawBallCount v (r v) x^2)*‖ψ.value t x‖^2 := by
      apply integral_mono (hb y R t)
      · simp only [mul_assoc,Finset.sum_mul]
        exact (integrable_finsetSum _ (fun v _ => hb v (r v) t)).const_mul _
      · intro x
        exact mul_le_mul_of_nonneg_right (hpoint x) (sq_nonneg _)
    _ = _ := by
      simp only [mul_assoc,Finset.sum_mul,integral_const_mul]
      rw [integral_finsetSum _ (fun v _ => hb v (r v) t)]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_ThinFieldFeedbackBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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

namespace CoreObservationEnsemble

theorem thin_field_bound (E : CoreObservationEnsemble) (y z : Space) {a r b Z lam : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) (hra : r ≤ 6*a) (hb : 0 < b) (hba : b ≤ a)
    (hsep : 20*a ≤ ‖y‖) (hz : z ∈ closedBall y (8*a))
    (hm : E.mass = 1) (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    (E.observe (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb)).fieldMoment Z lam z ≤
      thinFieldMajorant a b (max (E.excess Z lam) 0) (E.countMoment y (16*a)) := by
  have hh := E.thin_observe_field y z ha hr hra hb hba hsep hz hm hZ hlam
  have hbnd := E.thin_out_bound y ha hr hra hb hba hsep hm hZ hlam
  have hX := Real.sq_sqrt (E.outMoment_nonneg y hr hb Z lam)
  have hB := Real.sq_sqrt (E.countMoment_nonneg y (16*a))
  have hs : (Real.sqrt (E.countMoment y (16*a))/a)^2 = E.countMoment y (16*a)/a^2 := by rw [div_pow,hB]
  have hyoung : Real.sqrt (E.outMoment y hr hb Z lam)*Real.sqrt (E.countMoment y (16*a))/a ≤
      (thinOutMajorant a b (max (E.excess Z lam) 0) (E.countMoment y (16*a))+E.countMoment y (16*a)/a^2)/2 := by
    have h := sq_nonneg (Real.sqrt (E.outMoment y hr hb Z lam)-Real.sqrt (E.countMoment y (16*a))/a)
    have he : Real.sqrt (E.outMoment y hr hb Z lam)*Real.sqrt (E.countMoment y (16*a))/a =
       Real.sqrt (E.outMoment y hr hb Z lam)*(Real.sqrt (E.countMoment y (16*a))/a) := by ring
    rw [he]
    nlinarith
  exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hyoung) localFieldUniversalConstant_pos.le)

end CoreObservationEnsemble

open MeasureTheory Set Metric

lemma core_field_sq_le_ball_average {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (y x : Space) {a R Z lam : ℝ}
    (hR : 0 < R) (hsep : a+2*R ≤ ‖y‖) (hx : ‖x-y‖ ≤ a)
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    (max (normalizedCoreField Z lam ψ x) 0)^2 ≤
      (1/(R^3*(Real.pi*4/3)))*∫ z in closedBall y (a+R), (max (normalizedCoreField Z lam ψ z) 0)^2 := by
  let η := ballAverageKernel R
  let B := 1/(R^3*(Real.pi*4/3))
  let F : Space → ℝ := fun z => (max (normalizedCoreField Z lam ψ z) 0)^2
  have hm : Measurable η := ballAverageKernel_measurable R
  have hn := ballAverageKernel_nonneg hR
  have hs := ballAverageKernel_support R
  have hb := ballAverageKernel_bound hR
  have hnuc : 2*R ≤ ‖x‖ := by
    have htri := norm_le_norm_sub_add y x
    rw [norm_sub_rev y x] at htri
    linarith
  have hi := normalizedCoreField_radial_submean_sq hψ hm hR hn hs hb
    (ballAverageKernel_radial R) (ballAverageKernel_mass hR) x hnuc hZ hlam
  apply hi.trans
  let k := translatedDensity η x
  have hkm : Measurable k := translatedDensity_measurable hm _
  have hkn (z : Space) : 0 ≤ k z := hn (z-x)
  have hki : Integrable k := bounded_compact_integrable hkm (isCompact_closedBall _ _)
    (translatedDensity_support hs _) (fun z => hb (z-x))
  have hks : ∀ z, k z ≠ 0 → R ≤ ‖z‖ := by
    intro z hz
    have htri := norm_le_norm_sub_add x z
    rw [norm_sub_rev x z] at htri
    linarith [hs (z-x) hz]
  have hleft := positive_core_pair_integrable hψ hki hkm hkn hZ hlam hR hks 2
  have hFi : IntegrableOn F (closedBall y (a+R)) :=
    core_field_square_ball_integrable hψ y hR (by linarith) hZ hlam
  rw [←integral_const_mul,←integral_indicator isClosed_closedBall.measurableSet]
  apply integral_mono hleft ((integrable_indicator_iff isClosed_closedBall.measurableSet).2 (hFi.const_mul B))
  intro z
  by_cases hz : z ∈ closedBall y (a+R)
  · rw [indicator_of_mem hz]
    simpa only [k,translatedDensity,F,mul_comm] using
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hb (z-x)))
        (sq_nonneg (max (normalizedCoreField Z lam ψ z) 0))
  · rw [indicator_of_notMem hz]
    have hk0 : η (z-x) = 0 := by
      by_contra hk
      have hnz := norm_sub_le_norm_sub_add_norm_sub z x y
      have hh := hs (z-x) hk
      exact hz (by rw [mem_closedBall,dist_eq_norm]; linarith)
    simp only [k,translatedDensity,hk0,mul_zero,le_refl]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_PatchMassSubmeanBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_PatchMassSubmean_barrier_scope

open MeasureTheory Set Metric Filter
open scoped ENNReal

open CoulombAnalysis CoulombNeumann

lemma conditionalPatchField_le_submean {N M : ℕ} (ψ : FormVector (N+M))
    (s : Spins M) (u : Configuration M) (hψ : SobolevVector (coreSlice ψ s u))
    (y : Space) {a R Z lam : ℝ} (ha : 0 < a) (hsep : R+2*a ≤ ‖y‖)
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    ∀ᵐ z ∂ballMeasure R, conditionalPatchField ψ s Z lam y R u z ≤
      Real.sqrt ((1/(a^3*(Real.pi*4/3)))*∫ x in closedBall y (R+a),
        (max (normalizedCoreField Z lam (coreSlice ψ s u) x) 0)^2) := by
  let Q := (1/(a^3*(Real.pi*4/3)))*∫ x in closedBall y (R+a),
        (max (normalizedCoreField Z lam (coreSlice ψ s u) x) 0)^2
  have hQ : 0 ≤ Q := by dsimp [Q]; exact mul_nonneg (by positivity) (integral_nonneg (fun _ => sq_nonneg _))
  by_cases hp : MemLp (fun z => normalizedCoreField Z lam (coreSlice ψ s u) (y+z)) (5/2) (ballMeasure R)
  · filter_upwards [conditionalPatchField_ae ψ s Z lam y R u hp,
      ae_restrict_mem measurableSet_ball] with z hz hmem
    rw [hz]
    have hnorm : ‖(y+z)-y‖ ≤ R := by simp only [add_sub_cancel_left]; exact (mem_ball_zero_iff.mp hmem).le
    have hh := core_field_sq_le_ball_average hψ y (y+z) ha hsep hnorm hZ hlam
    apply (le_max_left _ _).trans
    exact (Real.le_sqrt (le_max_right _ _) hQ).2 hh
  · have hz : conditionalPatchField ψ s Z lam y R u = 0 := by
      simp only [conditionalPatchField,toLpOrZero,dite_eq_right hp]
    rw [hz]
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := (5/2:ℝ≥0∞)) (μ := ballMeasure R)] with z hz
    rw [hz]
    exact Real.sqrt_nonneg _

lemma weightedPatchMass_le_submean {N M : ℕ} (ψ : FormVector (N+M))
    (s : Spins M) (u : Configuration M) (hψ : SobolevVector (coreSlice ψ s u))
    (y : Space) {a R Z lam : ℝ} (ha : 0 < a) (hR : 0 < R) (hsep : R+2*a ≤ ‖y‖)
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    weightedPatchMass ψ s Z lam y R u ≤
      (4*R*Real.sqrt (1/(a^3*(Real.pi*4/3))))*
      (Real.sqrt (∫ z in closedBall y (R+a), coreFieldSquare Z lam z (coreSlice ψ s u))*
        Real.sqrt (formMass (coreSlice ψ s u))) := by
  let φ := coreSlice ψ s u
  let B := 1/(a^3*(Real.pi*4/3))
  let I := ∫ z in closedBall y (R+a), (max (normalizedCoreField Z lam φ z) 0)^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hI : 0 ≤ I := integral_nonneg (fun _ => sq_nonneg _)
  have hM := formMass_nonneg φ
  have hm := tfPatchMinimizer_mass_le hR tfKinetic_pos (Real.sqrt_nonneg _)
    (conditionalPatchField ψ s Z lam y R u)
    (conditionalPatchField_le_submean ψ s u hψ y ha hsep hZ hlam)
  have hh := mul_le_mul_of_nonneg_left hm hM
  change weightedPatchMass ψ s Z lam y R u ≤ formMass φ*(4*R*Real.sqrt (B*I)) at hh
  apply hh.trans_eq
  simp only [coreFieldSquare,integral_mul_const]
  change formMass φ*(4*R*Real.sqrt (B*I)) =
    (4*R*Real.sqrt B)*(Real.sqrt (I*formMass φ)*Real.sqrt (formMass φ))
  rw [Real.sqrt_mul hB,Real.sqrt_mul hI]
  have he : Real.sqrt (formMass φ)*Real.sqrt (formMass φ) = formMass φ := by
    nlinarith [Real.sq_sqrt hM]
  calc _ = (4*R*Real.sqrt B)*(Real.sqrt I*(Real.sqrt (formMass φ)*Real.sqrt (formMass φ))) := by rw [he]; ring
    _ = _ := by ring

end Work_PatchMassSubmean_barrier_scope

open MeasureTheory
open scoped BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SelectedPatchBudget
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter Metric
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

lemma radial_weightedPatchMass_integrable {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (htb : 4*b < t) (hy : t ≤ ‖y‖)
    (Z lam : ℝ) (c : Fin L → Fin 2) (s : Spins (cutOutNumber c)) :
    Integrable (weightedPatchMass (orderedCutForm (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ c) s Z lam y (t-4*b)) := by
  apply weightedPatchMass_integrable
    (orderedCutForm_sobolev (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) hψ c)
    s y (sub_pos.mpr htb) Z lam hb (radialPatchCore y t) _
    (radialPatch_nuclear_distance hb hy) (radialPatch_core_distance y hb)
  intro u x i hi
  apply FormZeroAt.coreSlice
  exact orderedCutForm_core_hole _ _ ψ c (radialPatchCore y t)ᶜ
    (coreFirstRadialCut_core_zero y ht hb) (coreFirstRadialCut_core_deriv_zero y ht hb)
    (joinLists x u) i (by simpa only [joinLists_left,mem_compl_iff] using hi)

lemma radial_fresh_tail_split {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (htb : 4*b < t) (hy : t ≤ ‖y‖)
    (Z lam K : ℝ) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      conditionalFieldSum Z lam (orderedCutForm p hp ψ c) s u-
      conditionalRetainedFieldSum Z lam (orderedCutForm p hp ψ c) s (radialPatchRetention L y t b c s) u+
      K*weightedPatchMass (orderedCutForm p hp ψ c) s Z lam y (t-4*b) u) =
    (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      conditionalFieldSum Z lam (orderedCutForm p hp ψ c) s u-
      conditionalRetainedFieldSum Z lam (orderedCutForm p hp ψ c) s (radialPatchRetention L y t b c s) u)+
      K*freshPatchMass p hp ψ Z lam y (t-4*b) := by
  dsimp only
  simp only [freshPatchMass,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro s _
  have hχ := orderedCutForm_sobolev (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) hψ c
  have hh := integral_add
    ((conditionalFieldSum_integrable hχ Z lam s).sub
      (conditionalRetainedFieldSum_integrable hχ Z lam s _ (radialPatchRetention_measurable L y t b c s)))
    ((radial_weightedPatchMass_integrable hψ y ht hb htb hy Z lam c s).const_mul K)
  simpa only [Pi.sub_apply,integral_const_mul] using hh

theorem selected_fresh_patch_budget {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) (y : Space) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hba : 7*b < 5*a) (hy : 6*a+2*b ≤ ‖y‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    ∃ t ∈ Icc (5*a) (6*a), ∃ ht : 0 ≤ t,
      let p := coreFirstRadialCut y ht hb
      let hp := coreFirstRadialCut_partition y ht hb
      let B := ∫ x, rawBallCount y (7*a) x^2 ∂formRawLaw ψ
      (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        weightedPatchGap (orderedCutForm p hp ψ c) s Z lam y (t-4*b) hb
          (radialPatchRetention L y t b c s) u) ≤
        corePriceExcess Z lam ψ+
        (3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2*((8*b/a)*B)^(1/2:ℝ)+
        b⁻¹^2*neumannRemainderConstant*(B^(2/3:ℝ)+B^(1/2:ℝ))+
        (((2*Real.pi+1)/2)/b)*B^(1/2:ℝ)+
        Real.sqrt (freshOutMaximumSecondMoment p hp ψ Z lam)*Real.sqrt ((8*b/a)*B)+
        ((packetDirichlet g/2)*b⁻¹^2)*freshPatchMass p hp ψ Z lam y (t-4*b) := by
  obtain ⟨t,ht,ht0,hd,hfirst,h43,hims⟩ :=
    radial_fresh_selected_counts hψ.sobolevVector hm y ha hb (by linarith)
  refine ⟨t,ht,ht0,?_⟩
  have htb : 7*b < t := lt_of_lt_of_le hba ht.1
  have hty : t+2*b ≤ ‖y‖ := le_trans (by linarith [ht.2]) hy
  have he := radial_fresh_patch_budget hψ y hb htb (by linarith) hZ hlam hg hcg hgn hr hgs
  dsimp only at he ⊢
  rw [radial_fresh_tail_split hψ.sobolevVector y _ hb (by linarith) (by linarith)] at he
  have hdel := radial_deleted_field_budget hψ.sobolevVector y ht0 hb hty hZ hlam.le
  dsimp only at hdel
  have hds := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hd)
    (Real.sqrt_nonneg (freshOutMaximumSecondMoment (coreFirstRadialCut y ht0 hb) (coreFirstRadialCut_partition y ht0 hb) ψ Z lam))
  have h43' := mul_le_mul_of_nonneg_left h43
    (mul_nonneg (sq_nonneg b⁻¹) neumannRemainderConstant_pos.le)
  have hfirst' := mul_le_mul_of_nonneg_left hfirst
    (by positivity : 0 ≤ (((2*Real.pi+1)/2)/b))
  linarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_PatchAverageSubmeanBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric Filter
open scoped BigOperators

namespace CoulombAtom

lemma patchMass_average_le_submean {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (y : Space) {a R Z lam : ℝ}
    (ha : 0 < a) (hR : 0 < R) (hsep : R+2*a ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam)
    (hi : ∀ s : Spins M, Integrable (weightedPatchMass ψ s Z lam y R)) :
    (∑ s : Spins M, ∫ u, weightedPatchMass ψ s Z lam y R u) ≤
      (4*R*Real.sqrt (1/(a^3*(Real.pi*4/3))))*
      (Real.sqrt (∫ z in closedBall y (R+a), coreLawAverage ψ (coreFieldSquare Z lam z))*
        Real.sqrt (formMass ψ)) := by
  let F (s : Spins M) (u : Configuration M) := ∫ z in closedBall y (R+a), coreFieldSquare Z lam z (coreSlice ψ s u)
  let W (s : Spins M) (u : Configuration M) := formMass (coreSlice ψ s u)
  let K := 4*R*Real.sqrt (1/(a^3*(Real.pi*4/3)))
  have hF (s : Spins M) : Integrable (F s) := coreFieldSquare_ball_statistic_integrable hψ s y ha (by linarith) hZ hlam
  have hW (s : Spins M) : Integrable (W s) := hψ.coreSlice_mass_integrable s
  have hFn (s : Spins M) (u : Configuration M) : 0 ≤ F s u := integral_nonneg (fun _ => coreFieldSquare_nonneg _ _ _ _)
  have hWn (s : Spins M) (u : Configuration M) : 0 ≤ W s u := formMass_nonneg _
  have hh (s : Spins M) : (∫ u, weightedPatchMass ψ s Z lam y R u) ≤
      K*∫ u, Real.sqrt (F s u)*Real.sqrt (W s u) := by
    rw [←integral_const_mul]
    apply integral_mono_ae (hi s) ((integrable_sqrt_mul_sqrt (hF s) (hW s) (hFn s) (hWn s)).const_mul K)
    filter_upwards [hψ.ae_coreSlice s] with u hu
    exact weightedPatchMass_le_submean ψ s u hu y ha hR hsep hZ hlam
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hh s)
  rw [←Finset.mul_sum] at hs
  have hc := sum_integral_sqrt_mul_sqrt_le (fun _ : Spins M => volume) F W hF hW hFn hWn
  have hend := hs.trans (mul_le_mul_of_nonneg_left hc (by dsimp [K]; positivity))
  have heF : (∑ s : Spins M, ∫ u, F s u) =
      ∫ z in closedBall y (R+a), coreLawAverage ψ (coreFieldSquare Z lam z) :=
    coreFieldSquare_ball_fubini hψ y ha (by linarith) hZ hlam
  have heW : (∑ s : Spins M, ∫ u, W s u) = formMass ψ := hψ.integral_coreSlice_mass
  rwa [heF,heW] at hend

lemma freshPatchMass_le_field_integral {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) (y : Space) {a r b Z lam : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) (hb : 0 < b) (hrb : 4*b < r)
    (hsep : r-4*b+2*a ≤ ‖y‖) (hy : r ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    freshPatchMass (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb) ψ Z lam y (r-4*b) ≤
      (4*(r-4*b)*Real.sqrt (1/(a^3*(Real.pi*4/3))))*
      Real.sqrt (∫ z in closedBall y (r-4*b+a),
        ((CoreObservationEnsemble.initial ψ hψ).observe (coreFirstRadialCut y hr hb)
          (coreFirstRadialCut_partition y hr hb)).fieldMoment Z lam z) := by
  let p := coreFirstRadialCut y hr hb
  let hp := coreFirstRadialCut_partition y hr hb
  let K := 4*(r-4*b)*Real.sqrt (1/(a^3*(Real.pi*4/3)))
  let F (c : Fin N → Fin 2) := ∫ z in closedBall y (r-4*b+a),
    coreLawAverage (orderedCutForm p hp ψ c) (coreFieldSquare Z lam z)
  let W (c : Fin N → Fin 2) := formMass (orderedCutForm p hp ψ c)
  have hFn (c) : 0 ≤ F c := integral_nonneg (fun _ =>
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => coreFieldSquare_nonneg _ _ _ _)))
  have hWn (c) : 0 ≤ W c := formMass_nonneg _
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun c (_ : c ∈ Finset.univ) =>
    patchMass_average_le_submean (orderedCutForm_sobolev p hp hψ.sobolevVector c) y ha
      (sub_pos.mpr hrb) hsep hZ hlam
      (fun s => radial_weightedPatchMass_integrable hψ.sobolevVector y hr hb hrb hy Z lam c s))
  change freshPatchMass p hp ψ Z lam y (r-4*b) ≤
    ∑ c, K*(Real.sqrt (F c)*Real.sqrt (W c)) at hh
  rw [←Finset.mul_sum] at hh
  have hc := Real.sum_sqrt_mul_sqrt_le Finset.univ hFn hWn
  have hend := hh.trans (mul_le_mul_of_nonneg_left hc (by dsimp [K]; positivity))
  have heW : (∑ c, W c) = 1 := (orderedCutForm_mass_sum p hp hψ.sobolevVector).trans hm
  have heF : (∑ c, F c) = ∫ z in closedBall y (r-4*b+a),
      ((CoreObservationEnsemble.initial ψ hψ).observe p hp).fieldMoment Z lam z := by
    simp_rw [CoreObservationEnsemble.initial_observe_fieldMoment ψ hψ p hp hZ hlam]
    rw [integral_finsetSum]
    intro c _
    exact coreLawAverage_fieldSquare_ball_integrable (orderedCutForm_sobolev p hp hψ.sobolevVector c)
      y ha (by linarith) hZ hlam
  rw [heW,Real.sqrt_one,mul_one,heF] at hend
  exact hend

theorem freshPatchMass_le_ballField {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) (y : Space) {a r b Z lam Q : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) (hra : r ≤ 6*a) (hb : 0 < b) (hrb : 4*b < r)
    (hsep : 10*a ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (_hQn : 0 ≤ Q)
    (hQ : ∀ z ∈ closedBall y (8*a),
      ((CoreObservationEnsemble.initial ψ hψ).observe (coreFirstRadialCut y hr hb)
          (coreFirstRadialCut_partition y hr hb)).fieldMoment Z lam z ≤ Q) :
    freshPatchMass (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb) ψ Z lam y (r-4*b) ≤
      768*a*Real.sqrt Q := by
  let E := (CoreObservationEnsemble.initial ψ hψ).observe (coreFirstRadialCut y hr hb)
    (coreFirstRadialCut_partition y hr hb)
  let R := r-4*b
  let K := 4*R*Real.sqrt (1/(a^3*(Real.pi*4/3)))
  let V := (8*a)^3*(Real.pi*4/3)
  have hR : 0 < R := by dsimp [R]; linarith
  have hRa : R ≤ 6*a := by dsimp [R]; linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hh := freshPatchMass_le_field_integral hψ hm y ha hr hb hrb
    (by linarith : r-4*b+2*a ≤ ‖y‖) (by linarith) hZ hlam
  have hi8 := E.fieldMoment_ball_integrable y ha (by linarith : 8*a+a ≤ ‖y‖) hZ hlam
  have hsub : closedBall y (R+a) ⊆ closedBall y (8*a) := closedBall_subset_closedBall (by linarith)
  have hinc := setIntegral_mono_set hi8 (ae_of_all _ (fun z => E.fieldMoment_nonneg Z lam z))
    (ae_of_all _ hsub)
  have hc : IntegrableOn (fun _ : Space => Q) (closedBall y (8*a)) :=
    integrableOn_const (isCompact_closedBall y (8*a)).measure_lt_top.ne
  have hbnd := hinc.trans (setIntegral_mono_on hi8 hc isClosed_closedBall.measurableSet hQ)
  rw [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,
    ←Measure.real,space_closedBall_real y (by positivity)] at hbnd
  have ht := hh.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hbnd) hK)
  have hv : (1/(a^3*(Real.pi*4/3)))*V = 512 := by
    dsimp [V]
    field_simp [ha.ne',Real.pi_ne_zero]
    ring
  have he : K*Real.sqrt (V*Q) = 4*R*Real.sqrt 512*Real.sqrt Q := by
    dsimp [K]
    rw [Real.sqrt_mul hV]
    calc
      _ = 4*R*(Real.sqrt (1/(a^3*(Real.pi*4/3)))*Real.sqrt V)*Real.sqrt Q := by ring
      _ = _ := by rw [←Real.sqrt_mul (by positivity : 0 ≤ 1/(a^3*(Real.pi*4/3))),hv]
  change _ ≤ K*Real.sqrt (V*Q) at ht
  rw [he] at ht
  have hroot : Real.sqrt (512:ℝ) ≤ 32 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 512)]
  have hcoef := mul_le_mul (by linarith : 4*R ≤ 24*a) hroot (Real.sqrt_nonneg 512) (by positivity : 0 ≤ 24*a)
  have hc' : 4*R*Real.sqrt 512 ≤ 768*a := by nlinarith
  exact ht.trans (mul_le_mul_of_nonneg_right hc' (Real.sqrt_nonneg Q))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_ThinFieldConstantsBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom

 def thinFieldUniversalConstant : ℝ := (1+localFieldUniversalConstant)*
    (4+1024*localFieldUniversalConstant+(512*localFieldUniversalConstant)^2)
lemma thinFieldUniversalConstant_pos : 0 < thinFieldUniversalConstant := by
  have := localFieldUniversalConstant_pos
  unfold thinFieldUniversalConstant
  positivity

lemma thin_majorants_le_uniform {a b D B : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hD : 0 ≤ D) (hB : 0 ≤ B) :
    thinOutMajorant a b D B ≤ thinFieldUniversalConstant*thinFieldBase a b D B ∧
    thinFieldMajorant a b D B ≤ thinFieldUniversalConstant*thinFieldBase a b D B := by
  let U := thinFieldBase a b D B
  let C := localFieldUniversalConstant
  let T := 4+1024*C+(512*C)^2
  have hU : 0 ≤ U := thinFieldBase_nonneg ha hb hD hB
  have hC : 0 ≤ C := localFieldUniversalConstant_pos.le
  have hT : 4 ≤ T := by
    dsimp [T]
    nlinarith [sq_nonneg (512*C)]
  have hTU := mul_le_mul_of_nonneg_right hT hU
  have hBU : B/a^2 ≤ U := countSqScale_le_thinFieldBase ha hb hD hB
  have ho : thinOutMajorant a b D B ≤ T*U := by
    have h := mul_le_mul_of_nonneg_left hBU (sq_nonneg (512*C))
    change 1024*C*U+(512*C)^2*B/a^2 ≤ T*U
    calc _ = 1024*C*U+(512*C)^2*(B/a^2) := by ring
         _ ≤ 1024*C*U+(512*C)^2*U := add_le_add le_rfl h
         _ ≤ T*U := by dsimp [T]; nlinarith
  have ho' : thinOutMajorant a b D B ≤ thinFieldUniversalConstant*U := by
    calc _ ≤ T*U := ho
         _ ≤ (1+C)*T*U := by nlinarith [mul_nonneg hC (mul_nonneg (by linarith : 0 ≤ T) hU)]
         _ = _ := rfl
  have hf : thinFieldMajorant a b D B ≤ C*T*U := by
    have h : U+(thinOutMajorant a b D B+B/a^2)/2 ≤ T*U := by linarith
    exact (mul_le_mul_of_nonneg_left h hC).trans_eq (by ring)
  refine ⟨ho',hf.trans ?_⟩
  change C*T*U ≤ (1+C)*T*U
  nlinarith [mul_nonneg (by linarith : 0 ≤ T) hU]

theorem freshOutMaximum_thin_bound {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) (y : Space) {a r b Z lam : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) (hra : r ≤ 6*a) (hb : 0 < b) (hba : b ≤ a)
    (hsep : 20*a ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    freshOutMaximumSecondMoment (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb) ψ Z lam ≤
      thinFieldUniversalConstant*thinFieldBase a b (max (corePriceExcess Z lam ψ) 0)
        (rawCountMoment ψ y (16*a)) := by
  let E := CoreObservationEnsemble.initial ψ hψ
  have hh := E.thin_out_bound y ha hr hra hb hba hsep
    (by simpa [E,CoreObservationEnsemble.initial_mass] using hm) hZ hlam
  rw [CoreObservationEnsemble.initial_outMoment ψ hψ y hr hb (by linarith) hZ hlam.le,
    CoreObservationEnsemble.initial_excess,CoreObservationEnsemble.initial_countMoment] at hh
  exact hh.trans (thin_majorants_le_uniform ha hb (le_max_right _ _) (rawCountMoment_nonneg _ _ _)).1

theorem freshPatchMass_thin_bound {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) (y : Space) {a r b Z lam : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) (hra : r ≤ 6*a) (hb : 0 < b) (hrb : 4*b < r) (hba : b ≤ a)
    (hsep : 20*a ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    freshPatchMass (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb) ψ Z lam y (r-4*b) ≤
      768*a*Real.sqrt (thinFieldUniversalConstant*thinFieldBase a b (max (corePriceExcess Z lam ψ) 0)
        (rawCountMoment ψ y (16*a))) := by
  let E := CoreObservationEnsemble.initial ψ hψ
  apply freshPatchMass_le_ballField hψ hm y ha hr hra hb hrb (by linarith) hZ hlam.le
    (mul_nonneg thinFieldUniversalConstant_pos.le
      (thinFieldBase_nonneg ha hb (le_max_right _ _) (rawCountMoment_nonneg _ _ _)))
  intro z hz
  have hh := E.thin_field_bound y z ha hr hra hb hba hsep hz
    (by simpa [E,CoreObservationEnsemble.initial_mass] using hm) hZ hlam
  rw [CoreObservationEnsemble.initial_excess,CoreObservationEnsemble.initial_countMoment] at hh
  exact hh.trans (thin_majorants_le_uniform ha hb (le_max_right _ _) (rawCountMoment_nonneg _ _ _)).2

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CellCountSupremumBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped BigOperators

namespace CoulombAtom

lemma rawCountMoment_le_number {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) (R : ℝ) : rawCountMoment ψ y R ≤ (N:ℝ)^2*formMass ψ := by
  simp only [rawCountMoment,rawFormPair,formMass,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  rw [←integral_const_mul]
  apply integral_mono
    (rawFormPair_integrable hψ ((rawBallCount_measurable y R).pow_const 2)
      (fun _ => norm_sq_le_of_nonneg (rawBallCount_nonneg _ _ _) (rawBallCount_le _ _ _)) s)
    (((hψ.1 s).norm.integrable_sq).const_mul _)
  intro x
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (rawBallCount_nonneg _ _ _) (rawBallCount_le _ _ _) 2) (sq_nonneg _)

lemma localCountRatioSet_bddAbove {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ) (D : ℝ) :
    BddAbove (localCountRatioSet ψ D) := by
  refine ⟨(N:ℝ)^2*formMass ψ,?_⟩
  rintro q ⟨y,hy,rfl⟩
  have hm := localOffsetMass_one_le D y
  have hm2 : 1 ≤ (localOffsetMass D y)^2 := by nlinarith
  exact (div_le_self (rawCountMoment_nonneg ψ y _) hm2).trans (rawCountMoment_le_number hψ y _)

lemma localCountMoment_le_supremum {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (D : ℝ) {y : Space} (hy : y ≠ 0) : rawCountMoment ψ y (localCellRadius y) ≤
      localCountSupremum ψ D*(localOffsetMass D y)^2 := by
  have hm := localOffsetMass_one_le D y
  have hp : 0 < (localOffsetMass D y)^2 := sq_pos_of_pos (by linarith)
  apply (div_le_iff₀ hp).mp
  exact (le_csSup (localCountRatioSet_bddAbove hψ D) (show _ ∈ localCountRatioSet ψ D from ⟨y,hy,rfl⟩)).trans
    (le_max_right _ _)

theorem enlarged_cell_count_le {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {D : ℝ} (hD : 0 ≤ D) {y : Space} (hy : y ≠ 0) :
    rawCountMoment ψ y (32*localCellRadius y) ≤
      localCountCoverConstant*localCountSupremum ψ D*(localOffsetMass D y)^2 := by
  classical
  let a := localCellRadius y
  let T := localCountStencil.image (fun v => y+a • v)
  let P := localCountSupremum ψ D
  let m := localOffsetMass D y
  have ha : 0 < a := localCellRadius_pos hy
  have hP : 0 ≤ P := le_trans zero_le_one (localCountSupremum_one_le ψ D)
  have hm : 0 ≤ m := le_trans zero_le_one (localOffsetMass_one_le D y)
  have hcover : ∀ z : Space, ‖z-y‖ < 32*a → ∃ v ∈ T, ‖z-v‖ < localCellRadius v := by
    intro z hz
    obtain ⟨v,hv,hzv⟩ := localCountStencil_scaled_cover hy hz
    exact ⟨y+a • v,Finset.mem_image.mpr ⟨v,hv,rfl⟩,hzv⟩
  have hbound (z : Space) (hz : z ∈ T) :
      rawCountMoment ψ z (localCellRadius z) ≤ 64*P*m^2 := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    have hn := localCountStencil_norm hv
    have hr := (localCellRadius_near hy hn).1
    have hzp : 0 < localCellRadius (y+a • v) := lt_of_lt_of_le (by positivity : 0 < a/2) hr
    have hz0 : y+a • v ≠ 0 := by
      intro hz0
      rw [hz0] at hzp
      simp [localCellRadius] at hzp
    have hmc := localOffsetMass_near hD hy hn
    have hmsq := pow_le_pow_left₀ (le_trans zero_le_one (localOffsetMass_one_le D (y+a • v))) hmc 2
    have hh := (localCountMoment_le_supremum hψ D hz0).trans (mul_le_mul_of_nonneg_left hmsq hP)
    calc _ ≤ P*(8*m)^2 := hh
         _ = 64*P*m^2 := by ring
  have hh := rawCountMoment_le_cover hψ y (32*a) T localCellRadius hcover
  have hs := Finset.sum_le_sum (s := T) (fun z hz => hbound z hz)
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  have hb := hh.trans (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (T.card:ℝ)))
  have hcard : (T.card:ℝ) ≤ (localCountStencil.card:ℝ) := by
    exact_mod_cast Finset.card_image_le
  have hcardsq := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ T.card) hcard 2
  have hc : (T.card:ℝ)^2 ≤ localCountCoverConstant/64 := by
    unfold localCountCoverConstant
    linarith
  have ht := mul_le_mul_of_nonneg_right hc (show 0 ≤ 64*P*m^2 by positivity)
  change rawCountMoment ψ y (32*a) ≤ localCountCoverConstant*P*m^2
  nlinarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_CellFieldNormalizationBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom

 def cellFieldNormConstant : ℝ := 1+thinFieldUniversalConstant*
    (6+localCountCoverConstant+localizationIMSConstant*localCountCoverConstant)
lemma cellFieldNormConstant_one_le : 1 ≤ cellFieldNormConstant := by
  have hC := localCountCoverConstant_one_le
  have hI := localizationIMSConstant_nonneg
  have hT := thinFieldUniversalConstant_pos
  unfold cellFieldNormConstant
  have : 0 ≤ thinFieldUniversalConstant*(6+localCountCoverConstant+localizationIMSConstant*localCountCoverConstant) := by positivity
  linarith

lemma cellField_norm_square {a m e D B P : ℝ}
    (ha : 0 < a) (hm : 1 ≤ m) (h3 : 1/a^3 ≤ m) (he : 0 < e)
    (hD : 0 ≤ D) (hDm : D*a ≤ m^2) (hB : 0 ≤ B)
    (hP : 1 ≤ P) (hBC : B ≤ localCountCoverConstant*P*m^2) :
    thinFieldUniversalConstant*thinFieldBase (2*a) (e*a) D B ≤
      (cellFieldNormConstant*(m/a)*(Real.sqrt P+1/e^2))^2 := by
  have hm0 : 0 ≤ m := le_trans zero_le_one hm
  have hP0 : 0 ≤ P := le_trans zero_le_one hP
  have hC := localCountCoverConstant_one_le
  have hI := localizationIMSConstant_nonneg
  have hT := thinFieldUniversalConstant_pos.le
  let K := thinFieldUniversalConstant*(6+localCountCoverConstant+localizationIMSConstant*localCountCoverConstant)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hF : K ≤ cellFieldNormConstant^2 := by change K ≤ (1+K)^2; nlinarith
  have hthin := (thinFieldBase_antitone ha (by linarith : a ≤ 2*a) (mul_pos he ha) hD hB).trans
    (thinFieldBase_normalized ha hm h3 he hD hDm hB hC hP hBC)
  have hV : P+1/e^4 ≤ (Real.sqrt P+1/e^2)^2 := by
    have hs := Real.sq_sqrt hP0
    have hx : (1/e^2)^2 = 1/e^4 := by ring
    have hh : 0 ≤ Real.sqrt P*(1/e^2) := by positivity
    nlinarith
  calc _ ≤ K*(m/a)^2*(P+1/e^4) := by
          have hh := mul_le_mul_of_nonneg_left hthin hT
          calc _ ≤ thinFieldUniversalConstant*
              ((6+localCountCoverConstant+localizationIMSConstant*localCountCoverConstant)*(m/a)^2*(P+1/e^4)) := hh
               _ = K*(m/a)^2*(P+1/e^4) := by dsimp [K]; ring
       _ ≤ cellFieldNormConstant^2*(m/a)^2*(Real.sqrt P+1/e^2)^2 := by gcongr
       _ = _ := by ring

theorem cell_fresh_field_mass {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) {y : Space} (hy : y ≠ 0)
    {e r Z lam : ℝ} (he : 0 < e) (he1 : e ≤ 1/8)
    (hr : r ∈ Set.Icc (10*localCellRadius y) (12*localCellRadius y))
    (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    let a := localCellRadius y
    let D := max (corePriceExcess Z lam ψ) 0
    let m := localOffsetMass D y
    let P := localCountSupremum ψ D
    ∃ hr0 : 0 ≤ r,
      freshOutMaximumSecondMoment (coreFirstRadialCut y hr0 (mul_pos he (localCellRadius_pos hy)))
        (coreFirstRadialCut_partition y hr0 (mul_pos he (localCellRadius_pos hy))) ψ Z lam ≤
          (cellFieldNormConstant*(m/a)*(Real.sqrt P+1/e^2))^2 ∧
      freshPatchMass (coreFirstRadialCut y hr0 (mul_pos he (localCellRadius_pos hy)))
        (coreFirstRadialCut_partition y hr0 (mul_pos he (localCellRadius_pos hy))) ψ Z lam y (r-4*(e*a)) ≤
          1536*cellFieldNormConstant*m*(Real.sqrt P+1/e^2) := by
  dsimp only
  let a := localCellRadius y
  let D := max (corePriceExcess Z lam ψ) 0
  let m := localOffsetMass D y
  let P := localCountSupremum ψ D
  have ha : 0 < a := localCellRadius_pos hy
  have hr0 : 0 ≤ r := le_trans (by positivity : 0 ≤ 10*a) hr.1
  have hb : 0 < e*a := mul_pos he ha
  have hba : e*a ≤ 2*a := by nlinarith
  have hsep : 20*(2*a) ≤ ‖y‖ := by dsimp [a,localCellRadius]; nlinarith [norm_nonneg y]
  have hrb : 4*(e*a) < r := by nlinarith [hr.1]
  let Q := cellFieldNormConstant*(m/a)*(Real.sqrt P+1/e^2)
  have hQ : 0 ≤ Q := by
    have hF := cellFieldNormConstant_one_le
    have hm1 := localOffsetMass_one_le D y
    dsimp [Q]
    positivity
  have hsq := cellField_norm_square ha (localOffsetMass_one_le D y) (localOffsetMass_cube_le D y) he
    (le_max_right _ _) (localOffsetMass_offset (le_max_right _ _) hy)
    (rawCountMoment_nonneg ψ y (32*a)) (localCountSupremum_one_le ψ D)
    (enlarged_cell_count_le hψ.sobolevVector (le_max_right _ _) hy)
  change thinFieldUniversalConstant*thinFieldBase (2*a) (e*a) D (rawCountMoment ψ y (32*a)) ≤ Q^2 at hsq
  have hscale : 16*(2*a) = 32*a := by ring
  have hh := freshOutMaximum_thin_bound hψ hm y (by positivity : 0 < 2*a) hr0 (by nlinarith [hr.2]) hb hba hsep hZ hlam
  have hh' := freshPatchMass_thin_bound hψ hm y (by positivity : 0 < 2*a) hr0 (by nlinarith [hr.2]) hb hrb hba hsep hZ hlam
  rw [hscale] at hh hh'
  refine ⟨hr0,hh.trans hsq,?_⟩
  have hs : Real.sqrt (thinFieldUniversalConstant*thinFieldBase (2*a) (e*a) D (rawCountMoment ψ y (32*a))) ≤ Q :=
    Real.sqrt_le_iff.mpr ⟨hQ,hsq⟩
  calc _ ≤ 768*(2*a)*Real.sqrt (thinFieldUniversalConstant*thinFieldBase (2*a) (e*a) D (rawCountMoment ψ y (32*a))) := hh'
       _ ≤ 768*(2*a)*Q := mul_le_mul_of_nonneg_left hs (by positivity)
       _ = 1536*cellFieldNormConstant*m*(Real.sqrt P+1/e^2) := by dsimp [Q]; field_simp; ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_NormalizedMasterEvent
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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

def radialPotentialError {N : ℕ} (ψ : FormVector N) (y : Space) {t b : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (Z lam q : ℝ) : ℝ :=
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  let χ := fun c : Fin N → Fin 2 => orderedCutForm p hp ψ c
  Real.sqrt (formMass ψ)*Real.sqrt ((2/q)*
    (∑ c : Fin N → Fin 2, ∑ k : Spins (cutOutNumber c), ∫ u,
      weightedPatchGap (χ c) k Z lam y (t-4*b) hb (radialPatchRetention N y t b c k) u))+
  (∫ x, rawLocalPotential y (q+Real.sqrt 3*b) x ∂formRawLaw ψ)+
  (2*Real.pi*tfPatchDensityCapConstant*q^2/(t-4*b)^6)*formMass ψ+
  (∫ x, rawLocalPotential y (Real.sqrt 3*b) x ∂formRawLaw ψ)+
  Real.sqrt (formMass ψ)*Real.sqrt
    (∑ c : Fin N → Fin 2, ∑ k : Spins (cutOutNumber c), ∫ u,
      (outerDeletedCount y t b u)^2*formMass (coreSlice (χ c) k u))/(t-7*b)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_FreshInnerCountsBarrier
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

open MeasureTheory Set Filter Metric
open scoped BigOperators

open MeasureTheory Set Filter Metric
open scoped BigOperators ContDiff

open CoulombAnalysis CoulombNeumann

lemma radial_inner_count_sq_gap {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevVector ψ) (y : Space) {a t b : ℝ}
    (_ha : 0 < a) (ht : 0 ≤ t) (hb : 0 < b) (hba : 3*b ≤ a)
    (hat : 8*a < t-4*b) (hy : t ≤ ‖y‖) (Z lam : ℝ)
    (c : Fin L → Fin 2) (s : Spins (cutOutNumber c)) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    let χ := orderedCutForm p hp ψ c
    ∀ᵐ u, rawBallCount y a u^2*formMass (coreSlice χ s u) ≤
      2*(localPatchDensityCap (t-4*b)*((4*a)^3*(Real.pi*4/3)))^2*
        formMass (coreSlice χ s u)+
      512*a*weightedPatchGap χ s Z lam y (t-4*b) hb (radialPatchRetention L y t b c s) u := by
  dsimp only
  filter_upwards [radialPatchMinimizer_density_cap hψ y ht hb (by linarith) hy Z lam c s] with u hu
  let σ := retainedPatchLp hb (radialPatchRetention L y t b c s u) u y (t-4*b)
  let Φ := conditionalPatchField (orderedCutForm (coreFirstRadialCut y ht hb)
    (coreFirstRadialCut_partition y ht hb) ψ c) s Z lam y (t-4*b) u
  have hσ : NonnegDensity σ := retainedPatchLp_nonneg hb _ _ _ _
  have hm : rawBallCount y a u ≤ ∫ z in ball 0 (2*a), σ z ∂ballMeasure (t-4*b) := by
    have hsqrt : Real.sqrt 3 ≤ (3:ℝ) := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg (3:ℝ)]
    apply rawBallCount_le_retainedPatch_mass hb
      (le_trans (by nlinarith) (show a+3*b ≤ 2*a by linarith))
      (by linarith)
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,by linarith⟩
  have hc : ∀ᵐ x ∂ballMeasure (t-4*b), ‖x‖ ≤ 2*(2*a) →
      tfPatchMinimizer (t-4*b) tfKinetic tfKinetic_pos Φ x ≤ localPatchDensityCap (t-4*b) := by
    filter_upwards [hu] with x hx
    intro hn
    exact hx (by linarith)
  have hh := local_mass_sq_le_gap (by linarith : 0 < 2*a) (by linarith : 4*(2*a) < t-4*b)
    tfKinetic tfKinetic_pos Φ hσ (localPatchDensityCap_nonneg _) hc
  have hs := (sq_le_sq₀ (rawBallCount_nonneg y a u)
    (integral_nonneg_of_ae (ae_restrict_of_ae hσ))).mpr hm
  have hh0 := mul_le_mul_of_nonneg_right (hs.trans hh)
    (formMass_nonneg (coreSlice (orderedCutForm (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ c) s u))
  dsimp only [weightedPatchGap]
  convert hh0 using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [σ, Φ]
  ring

theorem radial_inner_second_moment_gap {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (y : Space) {a t b : ℝ}
    (ha : 0 < a) (ht : 0 ≤ t) (hb : 0 < b) (hba : 3*b ≤ a)
    (hat : 8*a < t-4*b) (hy : t ≤ ‖y‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    (∫ x, rawBallCount y a x^2 ∂formRawLaw ψ) ≤
      2*(localPatchDensityCap (t-4*b)*((4*a)^3*(Real.pi*4/3)))^2*formMass ψ+
      512*a*(∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        weightedPatchGap (orderedCutForm p hp ψ c) s Z lam y (t-4*b) hb
          (radialPatchRetention L y t b c s) u) := by
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  let K := 2*(localPatchDensityCap (t-4*b)*((4*a)^3*(Real.pi*4/3)))^2
  let χ := fun c => orderedCutForm p hp ψ c
  have hχ (c : Fin L → Fin 2) := orderedCutForm_sobolev p hp hψ.sobolevVector c
  have hgap (c : Fin L → Fin 2) (s : Spins (cutOutNumber c)) :
      Integrable (weightedPatchGap (χ c) s Z lam y (t-4*b) hb (radialPatchRetention L y t b c s)) :=
    radial_weightedPatchGap_integrable hψ y ht hb (by linarith) hy hZ hlam hg hcg hgn hr hgs c s
  have hraw (c : Fin L → Fin 2) (s : Spins (cutOutNumber c)) :
      Integrable (fun u => rawBallCount y a u^2*formMass (coreSlice (χ c) s u)) := by
    apply (hχ c).coreSlice_mass_integrable s |>.bdd_mul
      (((rawBallCount_measurable y a).pow_const 2).aestronglyMeasurable)
    exact ae_of_all _ (fun u => norm_sq_le_of_nonneg (rawBallCount_nonneg y a u) (rawBallCount_le y a u))
  dsimp only
  rw [←radial_fresh_inner_second_moment hψ.sobolevVector y ht hb (by linarith : a ≤ t)]
  change (∑ c, ∑ s, ∫ u, rawBallCount y a u^2*formMass (coreSlice (χ c) s u)) ≤ K*formMass ψ+_
  calc
    _ ≤ ∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        (K*formMass (coreSlice (χ c) s u)+512*a*
          weightedPatchGap (χ c) s Z lam y (t-4*b) hb (radialPatchRetention L y t b c s) u) := by
      apply Finset.sum_le_sum; intro c _
      apply Finset.sum_le_sum; intro s _
      exact integral_mono_ae (hraw c s)
        (((hχ c).coreSlice_mass_integrable s).const_mul K |>.add ((hgap c s).const_mul (512*a)))
        (radial_inner_count_sq_gap hψ.sobolevVector y ha ht hb hba hat hy Z lam c s)
    _ = _ := by
      have he (c : Fin L → Fin 2) (s : Spins (cutOutNumber c)) :
          (∫ u, (K*formMass (coreSlice (χ c) s u)+512*a*
            weightedPatchGap (χ c) s Z lam y (t-4*b) hb (radialPatchRetention L y t b c s) u)) =
          K*(∫ u, formMass (coreSlice (χ c) s u))+512*a*(∫ u,
            weightedPatchGap (χ c) s Z lam y (t-4*b) hb (radialPatchRetention L y t b c s) u) := by
        rw [integral_add (((hχ c).coreSlice_mass_integrable s).const_mul K)
          ((hgap c s).const_mul (512*a)),integral_const_mul,integral_const_mul]
      simp_rw [he,Finset.sum_add_distrib,←Finset.mul_sum]
      simp_rw [show ∀ c, (∑ s, ∫ u, formMass (coreSlice (χ c) s u)) = formMass (χ c) from fun c => (hχ c).integral_coreSlice_mass]
      rw [orderedCutForm_mass_sum p hp hψ.sobolevVector]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CellBudgetNormalizationBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

 def cellCountLeadingConstant : ℝ := 1024*cellFieldNormConstant*localCountCoverConstant
 def cellCountErrorConstant (e d : ℝ) : ℝ :=
    2*cellDensityMassConstant^2+512+
    1536*(Real.pi*smoothTransitionBound)^2*localCountCoverConstant/e^2+
    512*neumannRemainderConstant/e^2*(localCountCoverConstant^(2/3:ℝ)+localCountCoverConstant)+
    512*((2*Real.pi+1)/2)*localCountCoverConstant/e+
    cellCountLeadingConstant*Real.sqrt e/e^2+
    393216*d*cellFieldNormConstant/e^2*(1+1/e^2)

lemma cellCountLeadingConstant_pos : 0 < cellCountLeadingConstant := by
  have := cellFieldNormConstant_one_le
  have := localCountCoverConstant_one_le
  unfold cellCountLeadingConstant
  positivity
lemma cellCountErrorConstant_nonneg {e d : ℝ} (he : 0 < e) (hd : 0 ≤ d) :
    0 ≤ cellCountErrorConstant e d := by
  have := cellCountLeadingConstant_pos
  have := localCountCoverConstant_one_le
  have := cellFieldNormConstant_one_le
  have := neumannRemainderConstant_pos
  unfold cellCountErrorConstant
  positivity

lemma cell_budget_algebra {a m e D B O M d P : ℝ}
    (ha : 0 < a) (hm : 1 ≤ m) (h3 : 1/a^3 ≤ m) (he : 0 < e) (he1 : e ≤ 1)
    (hD : D*a ≤ m^2) (hB : 0 ≤ B) (hd : 0 ≤ d) (hP : 1 ≤ P)
    (hBC : B ≤ localCountCoverConstant*P*m^2)
    (hO : O ≤ (cellFieldNormConstant*(m/a)*(Real.sqrt P+1/e^2))^2)
    (hM : M ≤ 1536*cellFieldNormConstant*m*(Real.sqrt P+1/e^2)) :
    2*cellDensityMassConstant^2*m^2+512*a*(D+
      (3/2:ℝ)*(Real.pi*smoothTransitionBound/(e*a))^2*Real.sqrt (4*e*B)+
      (e*a)⁻¹^2*neumannRemainderConstant*(B^(2/3:ℝ)+Real.sqrt B)+
      (((2*Real.pi+1)/2)/(e*a))*Real.sqrt B+
      Real.sqrt O*Real.sqrt (4*e*B)+((d/2)*(e*a)⁻¹^2)*M) ≤
    cellCountLeadingConstant*Real.sqrt e*P*m^2+
      cellCountErrorConstant e d*(P^(2/3:ℝ)+Real.sqrt P+1)*m^2 := by
  let C := localCountCoverConstant
  let F := cellFieldNormConstant
  let S := Real.pi*smoothTransitionBound
  let K := neumannRemainderConstant
  let L := (2*Real.pi+1)/2
  let u := Real.sqrt P
  let v := P^(2/3:ℝ)
  let W := v+u+1
  have hC1 : 1 ≤ C := localCountCoverConstant_one_le
  have hF1 : 1 ≤ F := cellFieldNormConstant_one_le
  have hC : 0 ≤ C := le_trans zero_le_one hC1
  have hF : 0 ≤ F := le_trans zero_le_one hF1
  have hK : 0 ≤ K := neumannRemainderConstant_pos.le
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hm0 : 0 ≤ m := le_trans zero_le_one hm
  have hP0 : 0 ≤ P := le_trans zero_le_one hP
  have hu : 0 ≤ u := Real.sqrt_nonneg P
  have hv : 0 ≤ v := Real.rpow_nonneg hP0 _
  have hW : 1 ≤ W := by dsimp [W]; linarith
  have huW : u ≤ W := by dsimp [W]; linarith
  have hvW : v ≤ W := by dsimp [W]; linarith
  have hu2 : u^2 = P := Real.sq_sqrt hP0
  have hse : Real.sqrt e ≤ 1 := Real.sqrt_le_iff.mpr ⟨by norm_num,by simpa using he1⟩
  have hrB : Real.sqrt B ≤ C*u*m := sqrt_count_scale hB hC1 hP0 hm0 hBC
  have hr4 : Real.sqrt (4*e*B) ≤ 2*Real.sqrt e*C*u*m := by
    calc _ = 2*Real.sqrt e*Real.sqrt B := by rw [Real.sqrt_mul (by positivity : 0 ≤ 4*e),Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]; norm_num
         _ ≤ 2*Real.sqrt e*(C*u*m) := mul_le_mul_of_nonneg_left hrB (by positivity)
         _ = _ := by ring
  have hr4' : Real.sqrt (4*e*B) ≤ 2*C*u*m := by
    calc _ ≤ 2*Real.sqrt e*C*u*m := hr4
         _ ≤ 2*1*C*u*m := by gcongr
         _ = _ := by ring
  have hB23 : B^(2/3:ℝ) ≤ C^(2/3:ℝ)*v*a*m^2 := cell_count_rpow_scale ha hm h3 hB hC hP0 hBC
  have hrootO : Real.sqrt O ≤ F*(m/a)*(u+1/e^2) := Real.sqrt_le_iff.mpr ⟨by positivity,hO⟩
  have hma : m/a ≤ m^2 := by
    have hh := mul_le_mul_of_nonneg_left (cell_reciprocal_bounds ha hm h3).1 hm0
    calc _ = m*(1/a) := by ring
         _ ≤ m*m := hh
         _ = m^2 := by ring
  have hmm : m ≤ m^2 := by nlinarith
  have heD : 512*a*D ≤ 512*W*m^2 := by
    have hh := mul_le_mul_of_nonneg_left hD (by norm_num : (0:ℝ) ≤ 512)
    have hh' := mul_le_mul_of_nonneg_right hW (show 0 ≤ 512*m^2 by positivity)
    nlinarith
  have heI : 512*a*((3/2:ℝ)*(S/(e*a))^2*Real.sqrt (4*e*B)) ≤
      (1536*S^2*C/e^2)*W*m^2 := by
    calc _ ≤ 512*a*((3/2:ℝ)*(S/(e*a))^2*(2*C*u*m)) := by gcongr
         _ = (1536*S^2*C/e^2)*u*(m/a) := by field_simp; ring
         _ ≤ (1536*S^2*C/e^2)*W*m^2 := by gcongr
  have heN : 512*a*((e*a)⁻¹^2*K*(B^(2/3:ℝ)+Real.sqrt B)) ≤
      (512*K/e^2*(C^(2/3:ℝ)+C))*W*m^2 := by
    calc _ ≤ 512*a*((e*a)⁻¹^2*K*(C^(2/3:ℝ)*v*a*m^2+C*u*m)) := by gcongr
         _ = 512*K/e^2*(C^(2/3:ℝ)*v*m^2+C*u*(m/a)) := by field_simp
         _ ≤ 512*K/e^2*(C^(2/3:ℝ)*W*m^2+C*W*m^2) := by gcongr
         _ = (512*K/e^2*(C^(2/3:ℝ)+C))*W*m^2 := by ring
  have heL : 512*a*((L/(e*a))*Real.sqrt B) ≤ (512*L*C/e)*W*m^2 := by
    calc _ ≤ 512*a*((L/(e*a))*(C*u*m)) := by gcongr
         _ = (512*L*C/e)*u*m := by field_simp
         _ ≤ (512*L*C/e)*W*m^2 := by gcongr
  have heO : 512*a*(Real.sqrt O*Real.sqrt (4*e*B)) ≤
      cellCountLeadingConstant*Real.sqrt e*P*m^2+
      (cellCountLeadingConstant*Real.sqrt e/e^2)*W*m^2 := by
    calc _ ≤ 512*a*((F*(m/a)*(u+1/e^2))*(2*Real.sqrt e*C*u*m)) := by gcongr
         _ = cellCountLeadingConstant*Real.sqrt e*P*m^2+
             (cellCountLeadingConstant*Real.sqrt e/e^2)*u*m^2 := by
               dsimp [cellCountLeadingConstant]
               change _ = 1024*F*C*Real.sqrt e*P*m^2+(1024*F*C*Real.sqrt e/e^2)*u*m^2
               rw [←hu2]
               field_simp
               ring
         _ ≤ cellCountLeadingConstant*Real.sqrt e*P*m^2+
             (cellCountLeadingConstant*Real.sqrt e/e^2)*W*m^2 := by
               have := cellCountLeadingConstant_pos
               gcongr
  have hpen : 1/e^2 ≤ (1/e^2)*W := by
    simpa using mul_le_mul_of_nonneg_left hW (by positivity : 0 ≤ 1/e^2)
  have heM : 512*a*(((d/2)*(e*a)⁻¹^2)*M) ≤
      (393216*d*F/e^2*(1+1/e^2))*W*m^2 := by
    calc _ ≤ 512*a*(((d/2)*(e*a)⁻¹^2)*(1536*F*m*(u+1/e^2))) := by gcongr
         _ = 393216*d*F/e^2*(m/a)*(u+1/e^2) := by field_simp; ring
         _ ≤ 393216*d*F/e^2*m^2*(W+(1/e^2)*W) := by gcongr
         _ = (393216*d*F/e^2*(1+1/e^2))*W*m^2 := by ring
  have hecap : 2*cellDensityMassConstant^2*m^2 ≤ (2*cellDensityMassConstant^2)*W*m^2 := by
    have hh := mul_le_mul_of_nonneg_right hW (by positivity : 0 ≤ 2*cellDensityMassConstant^2*m^2)
    linarith only [hh]
  change _ ≤ cellCountLeadingConstant*Real.sqrt e*P*m^2+cellCountErrorConstant e d*W*m^2
  dsimp [cellCountErrorConstant]
  change 2*cellDensityMassConstant^2*m^2+512*a*(D+(3/2:ℝ)*(S/(e*a))^2*Real.sqrt (4*e*B)+
    (e*a)⁻¹^2*K*(B^(2/3:ℝ)+Real.sqrt B)+(L/(e*a))*Real.sqrt B+Real.sqrt O*Real.sqrt (4*e*B)+((d/2)*(e*a)⁻¹^2)*M) ≤ _
  linarith only [heD,heI,heN,heL,heO,heM,hecap]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_CellCountFeedbackBarrier
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
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

 theorem cell_count_feedback {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) {y : Space} (hy : y ≠ 0)
    {e Z lam : ℝ} (he : 0 < e) (he1 : e ≤ 1/8) (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    let D := max (corePriceExcess Z lam ψ) 0
    let m := localOffsetMass D y
    let P := localCountSupremum ψ D
    rawCountMoment ψ y (localCellRadius y) ≤
      (cellCountLeadingConstant*Real.sqrt e*P+
        cellCountErrorConstant e (packetDirichlet g)*(P^(2/3:ℝ)+Real.sqrt P+1))*m^2 := by
  dsimp only
  let a := localCellRadius y
  let D := max (corePriceExcess Z lam ψ) 0
  let m := localOffsetMass D y
  let P := localCountSupremum ψ D
  have ha : 0 < a := localCellRadius_pos hy
  have hb : 0 < e*a := mul_pos he ha
  have hsep : 6*(2*a)+2*(e*a) ≤ ‖y‖ := by
    have : ‖y‖ = 100000*a := by dsimp [a,localCellRadius]; ring
    nlinarith
  obtain ⟨t,ht,ht0,hgap⟩ := selected_fresh_patch_budget hψ hm y (by positivity : 0 < 2*a) hb
    (by nlinarith : 7*(e*a) < 5*(2*a)) hsep hZ hlam hg hcg hgn hr hgs
  have ht' : t ∈ Icc (10*localCellRadius y) (12*localCellRadius y) := by
    constructor <;> linarith [ht.1,ht.2]
  have hta : 8*a < t-4*(e*a) := by nlinarith [ht.1]
  have hty : t ≤ ‖y‖ := by linarith [ht.2]
  have hba : 3*(e*a) ≤ a := by nlinarith
  obtain ⟨ht0',hO,hM⟩ := cell_fresh_field_mass hψ hm hy he he1 ht' hZ hlam
  have hraw := radial_inner_second_moment_gap hψ y ha ht0 hb hba hta hty hZ hlam hg hcg hgn hr hgs
  dsimp only at hgap hraw hO hM
  rw [←rawCountMoment_eq_integral hψ.sobolevVector y a,hm,mul_one] at hraw
  rw [←rawCountMoment_eq_integral hψ.sobolevVector y (7*(2*a))] at hgap
  have hr14 : 7*(2*a) = 14*a := by ring
  have he4 : 8*(e*a)/(2*a) = 4*e := by field_simp; norm_num
  rw [hr14,he4] at hgap
  simp only [←Real.sqrt_eq_rpow] at hgap
  let B := rawCountMoment ψ y (14*a)
  have hB : 0 ≤ B := rawCountMoment_nonneg _ _ _
  have hBC : B ≤ localCountCoverConstant*P*m^2 :=
    (rawCountMoment_le_of_radius hψ.sobolevVector y y (by
      simp only [sub_self,norm_zero,zero_add]; linarith : ‖y-y‖+14*a ≤ 32*a)).trans
      (enlarged_cell_count_le hψ.sobolevVector (le_max_right _ _) hy)
  have hcap := cell_density_mass_bound ha (by linarith : a ≤ t-4*(e*a)) (localOffsetMass_cube_le D y)
  have hcap0 : 0 ≤ localPatchDensityCap (t-4*(e*a))*((4*a)^3*(Real.pi*4/3)) := by
    have := localPatchDensityCap_nonneg (t-4*(e*a))
    positivity
  have hc2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hcap0 hcap 2) (by norm_num : (0:ℝ) ≤ 2)
  have hex : corePriceExcess Z lam ψ ≤ D := le_max_left _ _
  let p := coreFirstRadialCut y ht0 hb
  let hp := coreFirstRadialCut_partition y ht0 hb
  let G := ∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
    weightedPatchGap (orderedCutForm p hp ψ c) s Z lam y (t-4*(e*a)) hb
      (radialPatchRetention N y t (e*a) c s) u
  let O := freshOutMaximumSecondMoment p hp ψ Z lam
  let M := freshPatchMass p hp ψ Z lam y (t-4*(e*a))
  have hgap' : G ≤ D+(3/2:ℝ)*(Real.pi*smoothTransitionBound/(e*a))^2*Real.sqrt (4*e*B)+
      (e*a)⁻¹^2*neumannRemainderConstant*(B^(2/3:ℝ)+Real.sqrt B)+
      (((2*Real.pi+1)/2)/(e*a))*Real.sqrt B+Real.sqrt O*Real.sqrt (4*e*B)+
      ((packetDirichlet g/2)*(e*a)⁻¹^2)*M := by
    change G ≤ corePriceExcess Z lam ψ+_+_+_+_+_ at hgap
    exact hgap.trans (by gcongr)
  have hscale := cell_budget_algebra ha (localOffsetMass_one_le D y) (localOffsetMass_cube_le D y)
    he (by linarith : e ≤ 1) (localOffsetMass_offset (le_max_right _ _) hy) hB
    (packetDirichlet_nonneg g) (localCountSupremum_one_le ψ D) hBC hO hM
  change rawCountMoment ψ y a ≤ _
  calc _ ≤ 2*(localPatchDensityCap (t-4*(e*a))*((4*a)^3*(Real.pi*4/3)))^2+512*a*G := hraw
       _ ≤ 2*cellDensityMassConstant^2*m^2+512*a*(D+
          (3/2:ℝ)*(Real.pi*smoothTransitionBound/(e*a))^2*Real.sqrt (4*e*B)+
          (e*a)⁻¹^2*neumannRemainderConstant*(B^(2/3:ℝ)+Real.sqrt B)+
          (((2*Real.pi+1)/2)/(e*a))*Real.sqrt B+Real.sqrt O*Real.sqrt (4*e*B)+
          ((packetDirichlet g/2)*(e*a)⁻¹^2)*M) := by
            apply add_le_add (by nlinarith only [hc2]) (mul_le_mul_of_nonneg_left hgap' (by positivity))
       _ ≤ cellCountLeadingConstant*Real.sqrt e*P*m^2+
          cellCountErrorConstant e (packetDirichlet g)*(P^(2/3:ℝ)+Real.sqrt P+1)*m^2 := hscale
       _ = _ := by ring

 theorem cell_supremum_feedback {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1)
    {e Z lam : ℝ} (he : 0 < e) (he1 : e ≤ 1/8) (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    let P := localCountSupremum ψ (max (corePriceExcess Z lam ψ) 0)
    P ≤ 1+cellCountLeadingConstant*Real.sqrt e*P+
      cellCountErrorConstant e (packetDirichlet g)*(P^(2/3:ℝ)+Real.sqrt P+1) := by
  dsimp only
  let D := max (corePriceExcess Z lam ψ) 0
  let P := localCountSupremum ψ D
  have hP : 0 ≤ P := le_trans zero_le_one (localCountSupremum_one_le ψ D)
  have hL := cellCountLeadingConstant_pos.le
  have hC := cellCountErrorConstant_nonneg he (packetDirichlet_nonneg g)
  apply localCountSupremum_le
  · have h1 : 0 ≤ cellCountLeadingConstant*Real.sqrt e*P := by positivity
    have h2 : 0 ≤ cellCountErrorConstant e (packetDirichlet g)*(P^(2/3:ℝ)+Real.sqrt P+1) := by positivity
    linarith
  intro y hy
  have hh := cell_count_feedback hψ hm hy he he1 hZ hlam hg hcg hgn hr hgs
  dsimp only at hh
  exact hh.trans (by gcongr; linarith)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CellCountAbsorptionBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped ContDiff

namespace CoulombAtom
open CoulombAnalysis

 def cellBootstrapCollar : ℝ := min (1/8) ((1/(4*cellCountLeadingConstant))^2)
lemma cellBootstrapCollar_pos : 0 < cellBootstrapCollar := by
  have hA := cellCountLeadingConstant_pos
  unfold cellBootstrapCollar
  positivity
lemma cellBootstrapCollar_le : cellBootstrapCollar ≤ 1/8 := by unfold cellBootstrapCollar; exact min_le_left (1/8:ℝ) ((1/(4*cellCountLeadingConstant))^2)
lemma cellBootstrapCollar_absorb : cellCountLeadingConstant*Real.sqrt cellBootstrapCollar ≤ 1/4 := by
  have hA := cellCountLeadingConstant_pos
  have hh : Real.sqrt cellBootstrapCollar ≤ 1/(4*cellCountLeadingConstant) :=
    Real.sqrt_le_iff.mpr ⟨by positivity,by unfold cellBootstrapCollar; exact min_le_right (1/8:ℝ) ((1/(4*cellCountLeadingConstant))^2)⟩
  calc _ ≤ cellCountLeadingConstant*(1/(4*cellCountLeadingConstant)) := mul_le_mul_of_nonneg_left hh hA.le
       _ = 1/4 := by field_simp

 def cellUniversalCountConstant (d : ℝ) : ℝ :=
    (4*(1+3*cellCountErrorConstant cellBootstrapCollar d)/3)^3
lemma cellUniversalCountConstant_one_le {d : ℝ} (hd : 0 ≤ d) : 1 ≤ cellUniversalCountConstant d := by
  have hC := cellCountErrorConstant_nonneg cellBootstrapCollar_pos hd
  have ht : 1 ≤ 4*(1+3*cellCountErrorConstant cellBootstrapCollar d)/3 := by linarith
  have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) ht 3
  simpa [cellUniversalCountConstant] using hh

 theorem priced_cell_supremum_bound {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g) (hgs : tsupport g ⊆ Metric.ball 0 1) :
    localCountSupremum ψ (max (corePriceExcess Z lam ψ) 0) ≤ cellUniversalCountConstant (packetDirichlet g) := by
  let P := localCountSupremum ψ (max (corePriceExcess Z lam ψ) 0)
  have hP : 1 ≤ P := localCountSupremum_one_le ψ _
  have hP0 : 0 ≤ P := le_trans zero_le_one hP
  have hh := cell_supremum_feedback hψ hm cellBootstrapCollar_pos cellBootstrapCollar_le hZ hlam hg hcg hgn hr hgs
  have ha := mul_le_mul_of_nonneg_right cellBootstrapCollar_absorb hP0
  apply count_sublinear_absorption hP (cellCountErrorConstant_nonneg cellBootstrapCollar_pos (packetDirichlet_nonneg g))
  dsimp only at hh
  change P ≤ 1+cellCountLeadingConstant*Real.sqrt cellBootstrapCollar*P+_ at hh
  linarith only [hh,ha]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_UnshiftedCellCountBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_UnshiftedCellCount_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

namespace CoulombAtom

 def universalCellCountConstant : ℝ := cellUniversalCountConstant (packetDirichlet canonicalRealPacket)
lemma universalCellCountConstant_one_le : 1 ≤ universalCellCountConstant :=
  cellUniversalCountConstant_one_le (packetDirichlet_nonneg _)

 theorem priced_local_cell_count {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {y : Space} (hy : y ≠ 0) : rawCountMoment ψ y (localCellRadius y) ≤
      universalCellCountConstant*(localOffsetMass (max (corePriceExcess Z lam ψ) 0) y)^2 := by
  have hh := priced_cell_supremum_bound hψ hm hZ hlam canonicalRealPacket_smooth
    canonicalRealPacket_compact canonicalRealPacket_normalized canonicalRealPacket_radial canonicalRealPacket_support
  exact (localCountMoment_le_supremum hψ.sobolevVector _ hy).trans
    (mul_le_mul_of_nonneg_right hh (sq_nonneg _))

end CoulombAtom

end Work_UnshiftedCellCount_barrier_scope

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_LocalFieldScalarBoundBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom

 def actualCellMomentConstant : ℝ := localCountCoverConstant*universalCellCountConstant
lemma actualCellMomentConstant_one_le : 1 ≤ actualCellMomentConstant := by
  have h1 := localCountCoverConstant_one_le
  have h2 := universalCellCountConstant_one_le
  unfold actualCellMomentConstant
  nlinarith

lemma priced_enlarged_cell_count {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) {y : Space} (hy : y ≠ 0) :
    rawCountMoment ψ y (32*localCellRadius y) ≤
      actualCellMomentConstant*(localOffsetMass (max (corePriceExcess Z lam ψ) 0) y)^2 := by
  have hh := enlarged_cell_count_le hψ.sobolevVector (le_max_right (corePriceExcess Z lam ψ) 0) hy
  have hP := priced_cell_supremum_bound hψ hm hZ hlam canonicalRealPacket_smooth
    canonicalRealPacket_compact canonicalRealPacket_normalized canonicalRealPacket_radial canonicalRealPacket_support
  have hC := localCountCoverConstant_one_le
  unfold actualCellMomentConstant
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hP (le_trans zero_le_one hC)) (sq_nonneg _))

 def sharpFreshFieldConstant : ℝ := 1+thinFieldUniversalConstant*
    (6+actualCellMomentConstant+localizationIMSConstant*actualCellMomentConstant)

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

 lemma observeCells_mass (E : CoreObservationEnsemble) (ys : List Space) :
    (E.observeCells ys).mass = E.mass := by
  induction ys generalizing E with
  | nil => rfl
  | cons y ys ih => rw [observeCells,ih,observeCell_mass]

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

lemma rawWeightedCount_cutCore_le {N : ℕ} {f : Space → ℝ} (hf : ∀ z, 0 ≤ f z)
    (c : Fin N → Fin 2) (x : Configuration N) :
    rawWeightedCount f (cutCorePositions c x) ≤ rawWeightedCount f x := by
  rw [rawWeightedCount,sum_cutCorePositions c x f]
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · exact hf _

lemma rawWeightedMoment_eq_integral {N : ℕ} {psi : FormVector N} (hpsi : SobolevVector psi)
    {f : Space → ℝ} (hm : Measurable f) (hn : ∀ z, 0 ≤ f z) {A : ℝ} (hb : ∀ z, f z ≤ A) :
    rawWeightedMoment psi f = ∫ x, rawWeightedCount f x^2 ∂formRawLaw psi :=
  rawFormPair_eq_integral hpsi ((rawWeightedCount_measurable hm).pow_const 2)
    (fun x => norm_sq_le_of_nonneg (rawWeightedCount_nonneg hn x) (rawWeightedCount_le hb x))

lemma sum_cutCore_weightedMoment_le {N : ℕ} {psi : FormVector N} (hpsi : SobolevVector psi)
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    {f : Space → ℝ} (hm : Measurable f) (hn : ∀ z, 0 ≤ f z) {A : ℝ} (hb : ∀ z, f z ≤ A) :
    (∑ c : Fin N → Fin 2, coreLawAverage (orderedCutForm p hp psi c)
      (fun phi => rawWeightedMoment phi f)) ≤ rawWeightedMoment psi f := by
  simp only [rawWeightedMoment]
  simp_rw [cutCore_rawFormPair p hp hpsi _ ((rawWeightedCount_measurable hm).pow_const 2)
    (fun x => norm_sq_le_of_nonneg (rawWeightedCount_nonneg hn x) (rawWeightedCount_le hb x))]
  rw [rawFormPair_eq_integral hpsi ((rawWeightedCount_measurable hm).pow_const 2)
    (fun x => norm_sq_le_of_nonneg (rawWeightedCount_nonneg hn x) (rawWeightedCount_le hb x))]
  change spatialCutExpectation p hp psi (fun c x => rawWeightedCount f (cutCorePositions c x)^2) ≤ _
  apply spatialCutExpectation_le_raw p hp hpsi
    (fun c => ((rawWeightedCount_measurable hm).comp (cutCorePositions_measurable c)).pow_const 2)
    (A := ((N:ℝ)*A)^2)
    (fun c x => norm_sq_le_of_nonneg (rawWeightedCount_nonneg hn _)
      ((rawWeightedCount_cutCore_le hn c x).trans (rawWeightedCount_le hb x)))
    ((rawWeightedCount_measurable hm).pow_const 2) (B := ((N:ℝ)*A)^2)
    (fun x => norm_sq_le_of_nonneg (rawWeightedCount_nonneg hn _) (rawWeightedCount_le hb _))
  intro c x _
  exact pow_le_pow_left₀ (rawWeightedCount_nonneg hn _) (rawWeightedCount_cutCore_le hn c x) 2

lemma nextCoreObservation_weighted_statistic_integrable {N M : ℕ} {psi : FormVector (N+M)}
    (hpsi : SobolevVector psi) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2)
    {f : Space → ℝ} (hm : Measurable f) (hn : ∀ z, 0 ≤ f z) {A : ℝ} (hb : ∀ z, f z ≤ A) (t : Spins M) :
    Integrable (fun v => coreLawAverage (orderedCutForm p hp (coreSlice psi t v) c)
      (fun phi => rawWeightedMoment phi f)) :=
  nextCoreObservation_statistic_integrable psi p hp c (fun phi => rawWeightedMoment phi f)
    (fun s => rawWeightedMoment_coreSlice_integrable (nextCoreObservation_sobolev hpsi p hp c) hm hn hb s) t

theorem sum_nextCoreObservation_weightedMoment_le {N M : ℕ} {psi : FormVector (N+M)}
    (hpsi : SobolevVector psi) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    {f : Space → ℝ} (hm : Measurable f) (hn : ∀ z, 0 ≤ f z) {A : ℝ} (hb : ∀ z, f z ≤ A) :
    (∑ c : Fin N → Fin 2, coreLawAverage (nextCoreObservation p hp psi c)
      (fun phi => rawWeightedMoment phi f)) ≤ coreLawAverage psi (fun phi => rawWeightedMoment phi f) := by
  have ht (c : Fin N → Fin 2) := coreLawAverage_next psi p hp c
    (fun phi => rawWeightedMoment phi f)
    (fun s => rawWeightedMoment_coreSlice_integrable (nextCoreObservation_sobolev hpsi p hp c) hm hn hb s)
  simp_rw [ht]
  rw [Finset.sum_comm]
  change (∑ t : Spins M, ∑ c : Fin N → Fin 2, ∫ v,
    coreLawAverage (orderedCutForm p hp (coreSlice psi t v) c) (fun phi => rawWeightedMoment phi f)) ≤
    ∑ t : Spins M, ∫ v, rawWeightedMoment (coreSlice psi t v) f
  apply Finset.sum_le_sum
  intro t _
  have hi := fun c (_ : c ∈ (Finset.univ : Finset (Fin N → Fin 2))) =>
    nextCoreObservation_weighted_statistic_integrable hpsi p hp c hm hn hb t
  rw [←integral_finsetSum _ hi]
  apply integral_mono_ae (integrable_finsetSum _ hi) (rawWeightedMoment_coreSlice_integrable hpsi hm hn hb t)
  filter_upwards [hpsi.ae_coreSlice t] with v hv
  exact sum_cutCore_weightedMoment_le hv p hp hm hn hb

namespace CoreObservationGraph
 lemma observe_weightedMoment (G : CoreObservationGraph) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    {f : Space → ℝ} (hm : Measurable f) (hn : ∀ z, 0 ≤ f z) {A : ℝ} (hb : ∀ z, f z ≤ A) :
    (∑ c : Fin G.coreSize → Fin 2, (G.observe p hp c).weightedMoment f) ≤ G.weightedMoment f :=
  sum_nextCoreObservation_weightedMoment_le G.sobolev p hp hm hn hb
end CoreObservationGraph
namespace CoreObservationEnsemble
 lemma observe_weightedMoment (E : CoreObservationEnsemble) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    {f : Space → ℝ} (hm : Measurable f) (hn : ∀ z, 0 ≤ f z) {A : ℝ} (hb : ∀ z, f z ≤ A) :
    (E.observe p hp).weightedMoment f ≤ E.weightedMoment f := by
   change (∑ ic : Σ i : E.Branch, Fin (E.graph i).coreSize → Fin 2,
     ((E.graph ic.1).observe p hp ic.2).weightedMoment f) ≤ _
   rw [Fintype.sum_sigma]
   exact Finset.sum_le_sum (fun i _ => (E.graph i).observe_weightedMoment p hp hm hn hb)
 lemma observeCells_weightedMoment (E : CoreObservationEnsemble) (ys : List Space)
    {f : Space → ℝ} (hm : Measurable f) (hn : ∀ z, 0 ≤ f z) {A : ℝ} (hb : ∀ z, f z ≤ A) :
    (E.observeCells ys).weightedMoment f ≤ E.weightedMoment f := by
   classical
   induction ys generalizing E with
   | nil => exact le_rfl
   | cons y ys ih =>
     apply (ih _).trans
     unfold observeCell
     split_ifs
     · exact le_rfl
     · exact observe_weightedMoment E _ _ hm hn hb
end CoreObservationEnsemble
end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_OrdinaryDensity
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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

def ordinaryDensity {N : ℕ} (ψ : FormVector N) (z : Space) : ℝ :=
  ((rawOneParticleLaw (formRawLaw ψ)).rnDeriv volume z).toReal

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SharpFreshPatchBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SharpFreshPatch_barrier_scope

open MeasureTheory Set
open scoped BigOperators

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

 def sharpPatchRemainder (a b m : ℝ) : ℝ :=
    localizationIMSConstant/b^2*(Real.sqrt (8*b/a)*actualCellMomentConstant*m)+
    b⁻¹^2*neumannRemainderConstant*
      (actualCellMomentConstant^(2/3:ℝ)*m^(4/3:ℝ)+actualCellMomentConstant*m)+
    (((2*Real.pi+1)/2)/b)*(actualCellMomentConstant*m)+
    (sharpFreshFieldConstant*(m/a))*(Real.sqrt (8*b/a)*actualCellMomentConstant*m)+
    ((packetDirichlet canonicalRealPacket/2)*b⁻¹^2)*(768*sharpFreshFieldConstant*m)

end CoulombAtom

end Work_SharpFreshPatch_barrier_scope

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_LocalOrdinaryBarrier
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

def sharpFreshKineticConstant : ℝ :=
  1+localizationIMSConstant*actualCellMomentConstant+
    sharpFreshFieldConstant*actualCellMomentConstant

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_LocalBallTraceBarrier
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

def sharpOrdinaryDensityConstant : ℝ :=
  32*actualCellMomentConstant+(4096/3:ℝ)*(2*sharpFreshKineticConstant+
    3*(Real.pi*smoothTransitionBound)^2*actualCellMomentConstant)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SelectedMasterComparison
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
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
open CoulombAnalysis CoulombNeumann CoulombObservation

def selectedPatchEnergyError {N : ℕ} (ψ : FormVector N) (y : Space) (a : ℝ)
    {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (Z lam : ℝ) (g : Space → ℝ) : ℝ :=
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  let B := ∫ x, rawBallCount y (7*a) x^2 ∂formRawLaw ψ
  corePriceExcess Z lam ψ+
  (3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2*((8*b/a)*B)^(1/2:ℝ)+
  b⁻¹^2*neumannRemainderConstant*(B^(2/3:ℝ)+B^(1/2:ℝ))+
  (((2*Real.pi+1)/2)/b)*B^(1/2:ℝ)+
  Real.sqrt (freshOutMaximumSecondMoment p hp ψ Z lam)*Real.sqrt ((8*b/a)*B)+
  ((packetDirichlet g/2)*b⁻¹^2)*freshPatchMass p hp ψ Z lam y (t-4*b)

def selectedPotentialError {N : ℕ} (ψ : FormVector N) (y : Space) (a : ℝ)
    {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (Z lam q : ℝ) (g : Space → ℝ) : ℝ :=
  Real.sqrt ((2/q)*selectedPatchEnergyError ψ y a ht hb Z lam g)+
  (∫ x, rawLocalPotential y (q+Real.sqrt 3*b) x ∂formRawLaw ψ)+
  (2*Real.pi*tfPatchDensityCapConstant*q^2/(t-4*b)^6)+
  (∫ x, rawLocalPotential y (Real.sqrt 3*b) x ∂formRawLaw ψ)+
  Real.sqrt ((8*b/a)*(∫ x, rawBallCount y (7*a) x^2 ∂formRawLaw ψ))/(t-7*b)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SharpLocalPotentialBarrier
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

open CoulombAnalysis CoulombNeumann

 def sharpLocalPotentialBudget (a m u : ℝ) : ℝ :=
    (sharpOrdinaryDensityConstant*m^2/a)^(3/5:ℝ)*(8*Real.pi)^(2/5:ℝ)*u^(1/5:ℝ)

 def sharpPotentialRemainder (a b m D q : ℝ) : ℝ :=
    Real.sqrt ((2/q)*(D+sharpPatchRemainder a b m))+
    sharpLocalPotentialBudget a m (q+Real.sqrt 3*b)+
    2*Real.pi*tfPatchDensityCapConstant*q^2/a^6+
    sharpLocalPotentialBudget a m (Real.sqrt 3*b)+
    (Real.sqrt (8*b/a)*actualCellMomentConstant*m)/a

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_CapProbabilityWeightBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis

def physicalFieldCapBudget (D : ℝ) (y : Space) (b q u : ℝ) : ℝ :=
  tfPatchCapConstant/(localCellRadius y)^4+
    (sharpPotentialRemainder (localCellRadius y) b (localOffsetMass D y) D q+
      sharpLocalPotentialBudget (localCellRadius y) (localOffsetMass D y) u)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_AnnularCellGeometryBarrier
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
section Work_AnnularCellGeometry_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators

open CoulombObservation CoulombBarrier

lemma rawAnnularMoment_le_cover {N : ℕ} {psi : FormVector N} (hpsi : SobolevVector psi)
    (a b : ℝ) (T : Finset Space) (r : Space → ℝ)
    (hcover : ∀ z : Space, a ≤ ‖z‖ → ‖z‖ ≤ b → ∃ v ∈ T, ‖z-v‖ < r v) :
    rawAnnularMoment psi a b ≤ (T.card:ℝ)*∑ v ∈ T, rawCountMoment psi v (r v) := by
  classical
  have hb (z : Space) (q : ℝ) (s : Spins N) :
      Integrable (fun x => rawBallCount z q x^2*‖psi.value s x‖^2) :=
    rawFormPair_integrable hpsi ((rawBallCount_measurable z q).pow_const 2)
      (fun _ => norm_sq_le_of_nonneg (rawBallCount_nonneg _ _ _) (rawBallCount_le _ _ _)) s
  have ha (s : Spins N) : Integrable (fun x => rawAnnularCount a b x^2*‖psi.value s x‖^2) :=
    rawFormPair_integrable hpsi ((rawAnnularCount_measurable a b).pow_const 2)
      (fun _ => norm_sq_le_of_nonneg (rawAnnularCount_nonneg _ _ _) (rawAnnularCount_le _ _ _)) s
  have hpoint (x : Configuration N) : rawAnnularCount a b x^2 ≤
      (T.card:ℝ)*∑ v ∈ T, rawBallCount v (r v) x^2 := by
    calc _ ≤ (∑ v ∈ T, rawBallCount v (r v) x)^2 :=
           pow_le_pow_left₀ (rawAnnularCount_nonneg _ _ _) (rawAnnularCount_le_cover x a b T r hcover) 2
         _ ≤ _ := sq_sum_le_card_mul_sum_sq
  unfold rawAnnularMoment rawCountMoment rawFormPair
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  calc
    _ ≤ ∫ x, (T.card:ℝ)*(∑ v ∈ T, rawBallCount v (r v) x^2)*‖psi.value s x‖^2 := by
      apply integral_mono (ha s)
      · simp only [mul_assoc,Finset.sum_mul]
        exact (integrable_finsetSum _ (fun v _ => hb v (r v) s)).const_mul _
      · intro x
        exact mul_le_mul_of_nonneg_right (hpoint x) (sq_nonneg _)
    _ = _ := by
      simp only [mul_assoc,Finset.sum_mul,integral_const_mul]
      rw [integral_finsetSum _ (fun v _ => hb v (r v) s)]

end Work_AnnularCellGeometry_barrier_scope

open MeasureTheory Set Metric

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_AnnularCutExcess
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Metric
noncomputable section
namespace CoulombAtom

 theorem actual_finite_annular_cut_excess {N : ℕ} {psi : FormVector N}
    (hpsi : SobolevFermion psi) (hm : formMass psi = 1) {Z lam alpha beta u D : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (ha : 0 < alpha) (hu : 0 < u) (hD : 0 ≤ D)
    (he : max (corePriceExcess Z lam psi) 0 ≤ D) (ys : List Space)
    (hys : ∀ y ∈ ys, alpha*u ≤ ‖y‖ ∧ ‖y‖ ≤ beta*u) :
    max (((CoreObservationEnsemble.initial psi hpsi).observeCells ys).excess Z lam) 0 ≤
      (radialCutExcessConstant actualCellMomentConstant+1)^ys.length*
        (D+annularCellCostConstant alpha beta*(annularOffsetMass D u)^2/u) := by
  let E := CoreObservationEnsemble.initial psi hpsi
  let H := annularCellCostConstant alpha beta*(annularOffsetMass D u)^2/u
  have hH : 0 ≤ H := by
    have := annularCellCostConstant_pos (beta := beta) ha
    dsimp [H]; positivity
  have hb (y : Space) (hy : y ∈ ys) : y ≠ 0 ∧ ∃ m : ℝ, 1 ≤ m ∧
      1/(localCellRadius y)^3 ≤ m ∧
      E.countMoment y (16*localCellRadius y) ≤ actualCellMomentConstant*m^2 ∧
      m^2/localCellRadius y ≤ H := by
    obtain ⟨hya,hyb⟩ := hys y hy
    have hy0 : y ≠ 0 := norm_pos_iff.mp ((mul_pos ha hu).trans_le hya)
    have hr := localCellRadius_pos hy0
    refine ⟨hy0,localOffsetMass D y,localOffsetMass_one_le D y,
      localOffsetMass_cube_le D y,?_,localOffsetMass_annular_cost ha hu hD hya hyb⟩
    have hcount := priced_enlarged_cell_count hpsi hm hZ hlam hy0
    have hmon := E.countMoment_le_of_radius y y
      (show ‖y-y‖+16*localCellRadius y ≤ 32*localCellRadius y by simp only [sub_self,norm_zero]; linarith)
    calc
      _ ≤ E.countMoment y (32*localCellRadius y) := hmon
      _ = rawCountMoment psi y (32*localCellRadius y) := CoreObservationEnsemble.initial_countMoment ..
      _ ≤ actualCellMomentConstant*(localOffsetMass (max (corePriceExcess Z lam psi) 0) y)^2 := hcount
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (zero_le_one.trans (localOffsetMass_one_le _ _))
          (localOffsetMass_mono he y) 2) (zero_le_one.trans actualCellMomentConstant_one_le)
  have hh := E.observeCells_excess ys ((CoreObservationEnsemble.initial_mass ..).trans hm)
    hZ hlam actualCellMomentConstant_one_le hH hb
  have hK : 0 ≤ radialCutExcessConstant actualCellMomentConstant+1 := by
    have := radialCutExcessConstant_one_le actualCellMomentConstant_one_le; linarith
  have hex : max (E.excess Z lam) 0 ≤ D := by
    simpa only [E,CoreObservationEnsemble.initial_excess] using he
  exact (le_add_of_nonneg_right hH).trans (hh.trans
    (mul_le_mul_of_nonneg_left (add_le_add hex le_rfl) (pow_nonneg hK _)))

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

lemma truncatedTailWeight_measurable (h : ℝ) (K : ℕ) : Measurable (truncatedTailWeight h K) :=
  continuous_norm.measurable.inv.ite
    ((measurableSet_lt measurable_const continuous_norm.measurable).inter
      (measurableSet_le continuous_norm.measurable measurable_const)) measurable_const
lemma truncatedTailWeight_nonneg (h : ℝ) (K : ℕ) (a : Space) : 0 ≤ truncatedTailWeight h K a := by
  unfold truncatedTailWeight; split_ifs <;> positivity
lemma truncatedTailWeight_le (h : ℝ) (K : ℕ) (a : Space) :
    truncatedTailWeight h K a ≤ coulombTailWeight h a := by
  unfold truncatedTailWeight coulombTailWeight
  split_ifs <;> first | positivity | (expose_names; tauto)
lemma truncatedTailWeight_zero (h : ℝ) (a : Space) : truncatedTailWeight h 0 a = 0 := by
  simp only [truncatedTailWeight,tailRadius_zero]
  rw [ite_eq_right (by intro hc; exact (not_le.mpr hc.1) hc.2)]
lemma truncatedTailWeight_step {h : ℝ} (hh : 0 < h) (K : ℕ) (a : Space) :
    truncatedTailWeight h (K+1) a ≤ truncatedTailWeight h K a+
      (if tailRadius h K ≤ ‖a‖ ∧ ‖a‖ ≤ 4*tailRadius h K then 1 else 0)/tailRadius h K := by
  have hu := tailRadius_pos hh K
  by_cases hi : ‖a‖ ≤ tailRadius h K
  · have hle : truncatedTailWeight h (K+1) a = truncatedTailWeight h K a := by
      unfold truncatedTailWeight
      rw [tailRadius_succ]
      have hupper : ‖a‖ ≤ 4*tailRadius h K := by linarith
      simp only [hi,hupper,and_true]
    rw [hle]
    have hb : 0 ≤ (if tailRadius h K ≤ ‖a‖ ∧ ‖a‖ ≤ 4*tailRadius h K then (1:ℝ) else 0)/tailRadius h K := by
      split_ifs <;> positivity
    linarith
  · have hlo : tailRadius h K ≤ ‖a‖ := (lt_of_not_ge hi).le
    have hz : truncatedTailWeight h K a = 0 := by
      unfold truncatedTailWeight
      exact ite_eq_right (by intro hc; exact hi hc.2)
    rw [hz,zero_add]
    unfold truncatedTailWeight
    rw [tailRadius_succ]
    split_ifs with hj hk hk
    · simpa only [one_div] using inv_anti₀ hu hlo
    · exact False.elim (hk ⟨hlo,hj.2⟩)
    · positivity
    · norm_num

lemma raw_truncated_tail_le_shells {N : ℕ} {h : ℝ} (hh : 0 < h) (K : ℕ)
    (x : Configuration N) :
    rawWeightedCount (truncatedTailWeight h K) x ≤
      ∑ k ∈ Finset.range K, rawAnnularCount (tailRadius h k) (4*tailRadius h k) x/tailRadius h k := by
  induction K with
  | zero => simp [rawWeightedCount,truncatedTailWeight_zero]
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have hh' := Finset.sum_le_sum (s := Finset.univ)
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => truncatedTailWeight_step hh K (x i))
    simp only [Finset.sum_add_distrib,←Finset.sum_div] at hh'
    exact hh'.trans (add_le_add ih le_rfl)

lemma truncatedTailWeight_tendsto {h : ℝ} (hh : 0 < h) (a : Space) :
    Tendsto (fun K => truncatedTailWeight h K a) atTop (nhds (coulombTailWeight h a)) := by
  have ht : Tendsto (tailRadius h) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<4)).atTop_mul_const hh
  have hev : ∀ᶠ K in atTop, ‖a‖ ≤ tailRadius h K := (tendsto_atTop.1 ht) ‖a‖
  apply tendsto_const_nhds.congr'
  filter_upwards [hev] with K hK
  simp only [truncatedTailWeight,coulombTailWeight,hK,and_true]

lemma raw_truncated_tail_tendsto {N : ℕ} {h : ℝ} (hh : 0 < h) (x : Configuration N) :
    Tendsto (fun K => rawWeightedCount (truncatedTailWeight h K) x) atTop
      (nhds (rawWeightedCount (coulombTailWeight h) x)) := by
  exact tendsto_finsetSum _ (fun i _ => truncatedTailWeight_tendsto hh (x i))

lemma rawWeightedCount_sq_integrable {N : ℕ} {f : Space → ℝ}
    (hm : Measurable f) (hn : ∀ z, 0 ≤ f z) {A : ℝ} (hb : ∀ z, f z ≤ A)
    (mu : Measure (Configuration N)) [IsFiniteMeasure mu] :
    Integrable (fun x => rawWeightedCount f x^2) mu := by
  apply (integrable_const (((N:ℝ)*A)^2)).mono'
    ((rawWeightedCount_measurable hm).pow_const 2).aestronglyMeasurable
  exact ae_of_all _ (fun x => norm_sq_le_of_nonneg (rawWeightedCount_nonneg hn x) (rawWeightedCount_le hb x))

lemma truncated_tail_moment_tendsto {N : ℕ} {psi : FormVector N}
    (hpsi : SobolevVector psi) {h : ℝ} (hh : 0 < h) :
    Tendsto (fun K => rawWeightedMoment psi (truncatedTailWeight h K)) atTop
      (nhds (rawWeightedMoment psi (coulombTailWeight h))) := by
  let : IsFiniteMeasure (formRawLaw psi) := formRawLaw_finite hpsi
  have hb (K : ℕ) (a : Space) : truncatedTailWeight h K a ≤ 1/h :=
    (truncatedTailWeight_le h K a).trans (coulombTailWeight_le hh a)
  simp_rw [rawWeightedMoment_eq_integral hpsi (truncatedTailWeight_measurable h _)
    (truncatedTailWeight_nonneg h _) (hb _)]
  rw [rawWeightedMoment_eq_integral hpsi (coulombTailWeight_measurable h)
    (coulombTailWeight_nonneg h) (coulombTailWeight_le hh)]
  apply tendsto_integral_of_dominated_convergence (fun _ => ((N:ℝ)/h)^2)
    (fun K => ((rawWeightedCount_measurable (truncatedTailWeight_measurable h K)).pow_const 2).aestronglyMeasurable)
    (integrable_const _)
    (fun K => ae_of_all _ (fun x => ?_))
    (ae_of_all _ (fun x => (raw_truncated_tail_tendsto hh x).pow 2))
  convert norm_sq_le_of_nonneg (rawWeightedCount_nonneg (truncatedTailWeight_nonneg h K) x)
    (rawWeightedCount_le (hb K) x) using 1
  all_goals try with_reducible_and_instances rfl
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_ObservedFieldScale
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Metric
noncomputable section
namespace CoulombAtom

lemma ensemble_field_annular_bound (E : CoreObservationEnsemble) {Z lam D h A : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hD : 0 ≤ D) (hh : 0 < h) (hm : E.mass = 1)
    (he : max (E.excess Z lam) 0/h ≤ A*innerScale D h)
    (hb : ∀ z ∈ innerFieldTestAnnulus h,
      E.countMoment z (8*localCellRadius z) ≤ actualCellMomentConstant*(localOffsetMass D z)^2)
    {z : Space} (hz : z ∈ innerFieldTestAnnulus h) :
    E.fieldMoment Z lam z ≤ localFieldUniversalConstant*
      (100000*A+(5+actualCellMomentConstant)*3*(annularCellScaleConstant 1 3*100000)^2)*innerScale D h := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hh.trans_le hz.1)
  have ha := localCellRadius_pos hz0
  have hr : h/100000 ≤ localCellRadius z := by unfold localCellRadius; linarith [hz.1]
  have hd : max (E.excess Z lam) 0/localCellRadius z ≤ 100000*A*innerScale D h := by
    calc
      _ ≤ max (E.excess Z lam) 0/(h/100000) := div_le_div_of_nonneg_left (le_max_right _ _) (by positivity) hr
      _ = 100000*(max (E.excess Z lam) 0/h) := by ring
      _ ≤ 100000*(A*innerScale D h) := mul_le_mul_of_nonneg_left he (by norm_num)
      _ = _ := by ring
  have hf := ensemble_local_field_scale E z ha
    (show 12*localCellRadius z ≤ ‖z‖ by unfold localCellRadius; nlinarith [norm_nonneg z]) hm hZ hlam
  have hs := localFieldScale_linear_bound (D := max (E.excess Z lam) 0) ha (localOffsetMass_one_le D z)
    (localOffsetMass_cube_le D z) actualCellMomentConstant_one_le (hb z hz)
  have hc : 0 ≤ 5+actualCellMomentConstant := by have := actualCellMomentConstant_one_le; linarith
  calc
    _ ≤ localFieldUniversalConstant*(max (E.excess Z lam) 0/localCellRadius z+
        (5+actualCellMomentConstant)*(localOffsetMass D z/localCellRadius z)^2) :=
      hf.trans (mul_le_mul_of_nonneg_left hs localFieldUniversalConstant_pos.le)
    _ ≤ localFieldUniversalConstant*(100000*A*innerScale D h+
        (5+actualCellMomentConstant)*(3*(annularCellScaleConstant 1 3*100000)^2*innerScale D h)) :=
      mul_le_mul_of_nonneg_left (add_le_add hd (mul_le_mul_of_nonneg_left
        (annularInnerRadiusScale hD hh hz) hc)) localFieldUniversalConstant_pos.le
    _ = _ := by ring

lemma innerFieldVolume_le {h : ℝ} (hh : 0 < h) : innerFieldVolume h ≤ 36*Real.pi*h^3 := by
  have hs : innerFieldTestAnnulus h ⊆ closedBall (0:Space) (3*h) := by
    intro z hz
    simpa only [mem_closedBall,dist_zero_right] using hz.2
  have hv := measureReal_mono (μ := (volume : Measure Space)) hs (isCompact_closedBall (0:Space) (3*h)).measure_ne_top
  rw [space_closedBall_real (0:Space) (by positivity : 0 ≤ 3*h)] at hv
  unfold innerFieldVolume
  nlinarith only [hv]

lemma innerCapAverage_scale (E : CoreObservationEnsemble) {Z lam D h A T : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (hD : 0 ≤ D) (hh : 0 < h) (hm : E.mass = 1)
    (hA : 0 ≤ A)
    (hf : ∀ z ∈ innerFieldTestAnnulus h, E.fieldMoment Z lam z ≤ A*innerScale D h)
    (ht : E.weightedMoment (coulombTailWeight h) ≤ T*innerScale D h) :
    E.innerCapAverage Z lam h ≤
      (3*(packetDensityConstant*64*(36*Real.pi))^2*A+3*(16*packetPotentialConstant)^2*T)*innerScale D h+3*lam^2 := by
  have hb := E.innerCapAverage_bound hZ hlam hh hm hf ht
  have hv := innerFieldVolume_le hh
  have hv0 := innerFieldVolume_nonneg h
  have hcoef : (packetDensityConstant/(h/4)^3)^2*(innerFieldVolume h)^2 ≤
      (packetDensityConstant*64*(36*Real.pi))^2 := by
    calc
      _ ≤ (packetDensityConstant/(h/4)^3)^2*(36*Real.pi*h^3)^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv0 hv 2) (sq_nonneg _)
      _ = _ := by field_simp; ring
  have hc := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hA (innerScale_nonneg hD hh))
  nlinarith only [hb,hc]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_PricedAnnularCountBarrier
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
open scoped BigOperators

namespace CoulombAtom
open CoulombObservation CoulombBarrier

 theorem exists_priced_annular_count_constant {alpha beta : ℝ} (ha : 0 < alpha) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Z lam : ℝ) (N : ℕ) (psi : FormVector N), SobolevFermion psi →
      formMass psi = 1 → 0 ≤ Z → 0 < lam → ∀ (D u : ℝ), 0 ≤ D → 0 < u →
      max (corePriceExcess Z lam psi) 0 ≤ D →
      rawAnnularMoment psi (alpha*u) (beta*u) ≤ C*(annularOffsetMass D u)^2 := by
  classical
  obtain ⟨T,hT,hcover⟩ := exists_annularCellStencil ha beta
  let K := annularCellScaleConstant alpha beta
  let C := max (((T.card:ℝ)^2)*universalCellCountConstant*K^2) 1
  refine ⟨C,le_max_right _ _,?_⟩
  intro Z lam N psi hpsi hm hZ hlam D u hD hu he
  let U := T.image (fun v => u • v)
  let m := annularOffsetMass D u
  have hm0 : 0 ≤ m := le_trans zero_le_one (annularOffsetMass_one_le D u)
  have hc := rawAnnularMoment_le_cover hpsi.sobolevVector (alpha*u) (beta*u) U localCellRadius
    (fun _ h1 h2 => annularCell_scaled_cover hu T hcover h1 h2)
  have hc0 : 0 ≤ universalCellCountConstant := le_trans zero_le_one universalCellCountConstant_one_le
  have hm' (v : Space) (hv : v ∈ U) :
      rawCountMoment psi v (localCellRadius v) ≤ universalCellCountConstant*K^2*m^2 := by
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    have hw0 : w ≠ 0 := norm_pos_iff.mp (ha.trans_le (hT w hw).1)
    have hv0 : u • w ≠ 0 := smul_ne_zero hu.ne' hw0
    have hscale := localOffsetMass_annular_bound ha hu hD (hT w hw).1 (hT w hw).2
    have hh := pow_le_pow_left₀ (le_trans zero_le_one (localOffsetMass_one_le D (u • w))) hscale 2
    calc _ ≤ universalCellCountConstant*(localOffsetMass D (u • w))^2 :=
              (priced_local_cell_count hpsi hm hZ hlam hv0).trans
                (mul_le_mul_of_nonneg_left
                  (pow_le_pow_left₀ (le_trans zero_le_one (localOffsetMass_one_le _ _))
                    (localOffsetMass_mono he _) 2) hc0)
         _ ≤ universalCellCountConstant*(K*m)^2 := mul_le_mul_of_nonneg_left hh hc0
         _ = _ := by ring
  have hcard : (U.card:ℝ) ≤ (T.card:ℝ) := by exact_mod_cast Finset.card_image_le
  have hcard2 := pow_le_pow_left₀ (Nat.cast_nonneg U.card) hcard 2
  calc
    _ ≤ (U.card:ℝ)*∑ v ∈ U, rawCountMoment psi v (localCellRadius v) := hc
    _ ≤ (U.card:ℝ)*∑ _v ∈ U, universalCellCountConstant*K^2*m^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hm') (Nat.cast_nonneg U.card)
    _ = (U.card:ℝ)^2*universalCellCountConstant*K^2*m^2 := by simp; ring
    _ ≤ (T.card:ℝ)^2*universalCellCountConstant*K^2*m^2 := by gcongr
    _ ≤ C*m^2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg m)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ExpectedRadialCapBarrier
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
open scoped Topology

open CoulombAnalysis CoulombNeumann

 def dimensionlessPatchRemainder (a β M : ℝ) : ℝ :=
    (a^2/β^2)*localizationIMSConstant*(Real.sqrt (8*β)*actualCellMomentConstant*M)+
    (a/β^2)*neumannRemainderConstant*actualCellMomentConstant^(2/3:ℝ)*M^(4/3:ℝ)+
    (a^2/β^2)*neumannRemainderConstant*actualCellMomentConstant*M+
    (a^3/β)*((2*Real.pi+1)/2)*actualCellMomentConstant*M+
    sharpFreshFieldConstant*Real.sqrt (8*β)*actualCellMomentConstant*M^2+
    (a^2/β^2)*(packetDirichlet canonicalRealPacket/2)*768*sharpFreshFieldConstant*M

 def dimensionlessLocalPotential (M u : ℝ) : ℝ :=
    (sharpOrdinaryDensityConstant*M^2)^(3/5:ℝ)*(8*Real.pi)^(2/5:ℝ)*u^(1/5:ℝ)

 def dimensionlessPotentialRemainder (a β M E τ : ℝ) : ℝ :=
    Real.sqrt ((2/τ)*(E+dimensionlessPatchRemainder a β M))+
    dimensionlessLocalPotential M (τ+Real.sqrt 3*β)+
    2*Real.pi*tfPatchDensityCapConstant*τ^2+
    dimensionlessLocalPotential M (Real.sqrt 3*β)+
    Real.sqrt (8*β)*actualCellMomentConstant*M

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ActualTailTiltBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace CoulombAtom
open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

def TailTiltState {N : ℕ} (Z lam r : ℝ) (K : ℕ) (p₀ : Fin (K+1) → ℝ) (δ : ℝ)
    (F : fermionGraph N) : Prop :=
  ‖fermionGraphValue N F‖^2 = 1 ∧
    formEnergy Z (graphFormVector F) ≤ energy Z N+δ ∧
    ∀ (j : Fin (K+1))
      (A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)))
      (_hA : MeasurableSet[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j] A),
      p₀ j ≤ ((physicalObservationLaw (graphRawLaw F) K) A).toReal →
    ∃ G : fermionGraph N,
      ‖fermionGraphValue N G‖^2 = 1 ∧
      graphRawLaw G = (ENNReal.ofReal (((physicalObservationLaw (graphRawLaw F) K) A).toReal))⁻¹ •
        Measure.map Prod.fst ((physicalObservationLaw (graphRawLaw F) K).restrict A) ∧
      max (corePriceExcess Z lam (graphFormVector G)) 0 ≤
        dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ObservedAnnularCountBarrier
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
section Work_ObservedAnnularCount_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators ENNReal

open CoulombBarrier
open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma rawAnnularMoment_eq_integral {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (a b : ℝ) : rawAnnularMoment ψ a b = ∫ x, rawAnnularCount a b x^2 ∂formRawLaw ψ :=
  rawFormPair_eq_integral hψ ((rawAnnularCount_measurable a b).pow_const 2)
    (fun x => norm_sq_le_of_nonneg (rawAnnularCount_nonneg a b x) (rawAnnularCount_le a b x))

lemma rawAnnularCount_sq_integrable {N : ℕ} (a b : ℝ) (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] : Integrable (fun x => rawAnnularCount a b x^2) μ := by
  apply Integrable.mono' (integrable_const ((N:ℝ)^2))
    ((rawAnnularCount_measurable a b).pow_const 2).aestronglyMeasurable
  exact ae_of_all _ (fun x => norm_sq_le_of_nonneg (rawAnnularCount_nonneg a b x) (rawAnnularCount_le a b x))

end Work_ObservedAnnularCount_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombBarrier CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_PricedCoulombTail
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
open CoulombObservation CoulombBarrier

lemma truncated_tail_moment_bound {N : ℕ} {psi : FormVector N} (hpsi : SobolevVector psi)
    {h D C : ℝ} (hh : 0 < h) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hcounts : ∀ u : ℝ, 0 < u → rawAnnularMoment psi u (4*u) ≤ C*(annularOffsetMass D u)^2)
    (K : ℕ) : rawWeightedMoment psi (truncatedTailWeight h K) ≤ 12*C*(1/h^8+1/h^2+D/h) := by
  let H := 1/h^8+1/h^2+D/h
  have hH : 0 ≤ H := by dsimp [H]; positivity
  let : IsFiniteMeasure (formRawLaw psi) := formRawLaw_finite hpsi
  let B := fun k (x : Configuration N) => rawAnnularCount (tailRadius h k) (4*tailRadius h k) x/tailRadius h k
  have hi (k : ℕ) : Integrable (fun x : Configuration N => (B k x)^2/tailWeight k) (formRawLaw psi) := by
    simp only [B,div_pow]
    exact ((rawAnnularCount_sq_integrable _ _ _).div_const _).div_const _
  have he (k : ℕ) : (∫ x, (B k x)^2/tailWeight k ∂formRawLaw psi) ≤ 3*C*tailWeight k*H := by
    simp only [B,div_pow,integral_div,←rawAnnularMoment_eq_integral hpsi]
    have hu := tailRadius_pos hh k
    have hw := tailWeight_pos k
    calc
      _ ≤ (C*(annularOffsetMass D (tailRadius h k))^2)/(tailRadius h k)^2/tailWeight k :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (hcounts _ hu) (sq_nonneg _)) hw.le
      _ ≤ (C*(3*(1/(tailRadius h k)^6+1+D*tailRadius h k)))/(tailRadius h k)^2/tailWeight k :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (annularOffsetMass_sq_le hD hu) hC) (sq_nonneg _)) hw.le
      _ = 3*C*((1/(tailRadius h k)^6+1+D*tailRadius h k)/((tailRadius h k)^2*tailWeight k)) := by ring
      _ ≤ 3*C*(tailWeight k*H) := mul_le_mul_of_nonneg_left (tail_annular_scale hD hh k) (by positivity)
      _ = _ := by ring
  have hhCount (x : Configuration N) := pow_le_pow_left₀
    (rawWeightedCount_nonneg (truncatedTailWeight_nonneg h K) x) (raw_truncated_tail_le_shells hh K x) 2
  rw [rawWeightedMoment_eq_integral hpsi (truncatedTailWeight_measurable h K)
    (truncatedTailWeight_nonneg h K) (fun a => (truncatedTailWeight_le h K a).trans (coulombTailWeight_le hh a))]
  calc
    _ ≤ ∫ x, 2*∑ k ∈ Finset.range K, (B k x)^2/tailWeight k ∂formRawLaw psi :=
      integral_mono (rawWeightedCount_sq_integrable (truncatedTailWeight_measurable h K)
        (truncatedTailWeight_nonneg h K) (fun a => (truncatedTailWeight_le h K a).trans (coulombTailWeight_le hh a)) _)
        ((integrable_finsetSum _ (fun k _ => hi k)).const_mul 2)
        (fun x => (hhCount x).trans (finite_tail_cauchy K (fun k => B k x)))
    _ = 2*∑ k ∈ Finset.range K, (∫ x, (B k x)^2/tailWeight k ∂formRawLaw psi) := by
      rw [integral_const_mul,integral_finsetSum _ (fun k _ => hi k)]
    _ ≤ 2*∑ k ∈ Finset.range K, 3*C*tailWeight k*H := by gcongr with k hk; exact he k
    _ = 6*C*H*(∑ k ∈ Finset.range K, tailWeight k) := by
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ 6*C*H*2 := mul_le_mul_of_nonneg_left (sum_tailWeight_le K) (by positivity)
    _ = _ := by dsimp [H]; ring

theorem coulomb_tail_moment_bound {N : ℕ} {psi : FormVector N} (hpsi : SobolevVector psi)
    {h D C : ℝ} (hh : 0 < h) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hcounts : ∀ u : ℝ, 0 < u → rawAnnularMoment psi u (4*u) ≤ C*(annularOffsetMass D u)^2) :
    rawWeightedMoment psi (coulombTailWeight h) ≤ 12*C*(1/h^8+1/h^2+D/h) := by
  exact le_of_tendsto (truncated_tail_moment_tendsto hpsi hh)
    (Filter.Eventually.of_forall (fun K => truncated_tail_moment_bound hpsi hh hD hC hcounts K))

theorem exists_priced_coulomb_tail_constant :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Z lam : ℝ) (N : ℕ) (psi : FormVector N), SobolevFermion psi →
      formMass psi = 1 → 0 ≤ Z → 0 < lam → ∀ (D h : ℝ), 0 ≤ D → 0 < h →
      max (corePriceExcess Z lam psi) 0 ≤ D →
      rawWeightedMoment psi (coulombTailWeight h) ≤ C*(1/h^8+1/h^2+D/h) := by
  obtain ⟨C,hC,hb⟩ := exists_priced_annular_count_constant (beta := 4) (by norm_num : (0:ℝ)<1)
  refine ⟨12*C,by linarith,?_⟩
  intro Z lam N psi hpsi hm hZ hlam D h hD hh he
  exact coulomb_tail_moment_bound hpsi.sobolevVector hh hD (zero_le_one.trans hC)
    (fun u hu => by simpa only [one_mul] using hb Z lam N psi hpsi hm hZ hlam D u hD hu he)

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

section
open MeasureTheory Set

lemma finite_annular_excess_at_innerScale {N : ℕ} {psi : FormVector N}
    (hpsi : SobolevFermion psi) (hm : formMass psi = 1) {Z lam alpha beta u D h : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (ha : 0 < alpha) (hD : 0 ≤ D) (hh : 0 < h) (hu : h ≤ u)
    (he : max (corePriceExcess Z lam psi) 0 ≤ D) (ys : List Space)
    (hys : ∀ y ∈ ys, alpha*u ≤ ‖y‖ ∧ ‖y‖ ≤ beta*u) :
    max (((CoreObservationEnsemble.initial psi hpsi).observeCells ys).excess Z lam) 0/h ≤
      ((radialCutExcessConstant actualCellMomentConstant+1)^ys.length*
        (1+3*annularCellCostConstant alpha beta))*innerScale D h := by
  have hbase := actual_finite_annular_cut_excess hpsi hm hZ hlam ha (hh.trans_le hu) hD he ys hys
  have hcost := annular_cut_cost_innerScale hD hh hu
  have hC := (annularCellCostConstant_pos (beta := beta) ha).le
  have hK : 0 ≤ (radialCutExcessConstant actualCellMomentConstant+1)^ys.length := by
    have := radialCutExcessConstant_one_le actualCellMomentConstant_one_le
    positivity
  have hD' : D/h ≤ innerScale D h := by
    unfold innerScale
    have h1 : 0 ≤ 1/h^8 := by positivity
    have h2 : 0 ≤ 1/h^2 := by positivity
    linarith
  calc
    _ ≤ ((radialCutExcessConstant actualCellMomentConstant+1)^ys.length*
      (D+annularCellCostConstant alpha beta*(annularOffsetMass D u)^2/u))/h :=
        div_le_div_of_nonneg_right hbase hh.le
    _ = (radialCutExcessConstant actualCellMomentConstant+1)^ys.length*
      (D/h+annularCellCostConstant alpha beta*((annularOffsetMass D u)^2/u/h)) := by ring
    _ ≤ (radialCutExcessConstant actualCellMomentConstant+1)^ys.length*
      (innerScale D h+annularCellCostConstant alpha beta*(3*innerScale D h)) :=
        mul_le_mul_of_nonneg_left (add_le_add hD' (mul_le_mul_of_nonneg_left hcost hC)) hK
    _ = _ := by ring

lemma actual_observed_local_count {N : ℕ} {psi : FormVector N}
    (hpsi : SobolevFermion psi) (hm : formMass psi = 1) {Z lam D : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (he : max (corePriceExcess Z lam psi) 0 ≤ D)
    (ys : List Space) {z : Space} (hz : z ≠ 0) :
    ((CoreObservationEnsemble.initial psi hpsi).observeCells ys).countMoment z (8*localCellRadius z) ≤
      actualCellMomentConstant*(localOffsetMass D z)^2 := by
  let E := CoreObservationEnsemble.initial psi hpsi
  have hr := localCellRadius_pos hz
  calc
    _ ≤ E.countMoment z (8*localCellRadius z) := E.observeCells_countMoment ys _ _
    _ ≤ E.countMoment z (32*localCellRadius z) := E.countMoment_le_of_radius z z
      (by simp only [sub_self,norm_zero,zero_add]; linarith)
    _ = rawCountMoment psi z (32*localCellRadius z) := CoreObservationEnsemble.initial_countMoment ..
    _ ≤ actualCellMomentConstant*(localOffsetMass (max (corePriceExcess Z lam psi) 0) z)^2 :=
      priced_enlarged_cell_count hpsi hm hZ hlam hz
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀
      (zero_le_one.trans (localOffsetMass_one_le _ z)) (localOffsetMass_mono he z) 2)
      (zero_le_one.trans actualCellMomentConstant_one_le)

 theorem exists_actual_observed_innerCap_constant {alpha beta : ℝ} (ha : 0 < alpha) (L : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Z lam : ℝ) (N : ℕ) (psi : FormVector N) (hpsi : SobolevFermion psi),
      formMass psi = 1 → 0 ≤ Z → 0 < lam → ∀ (D h u : ℝ), 0 ≤ D → 0 < h → h ≤ u →
      max (corePriceExcess Z lam psi) 0 ≤ D → ∀ ys : List Space, ys.length = L →
      (∀ y ∈ ys, alpha*u ≤ ‖y‖ ∧ ‖y‖ ≤ beta*u) →
      ((CoreObservationEnsemble.initial psi hpsi).observeCells ys).innerCapAverage Z lam h ≤
        C*(innerScale D h+lam^2) := by
  obtain ⟨T,hT,hTail⟩ := exists_priced_coulomb_tail_constant
  let A := (radialCutExcessConstant actualCellMomentConstant+1)^L*(1+3*annularCellCostConstant alpha beta)
  let F := localFieldUniversalConstant*(100000*A+(5+actualCellMomentConstant)*3*(annularCellScaleConstant 1 3*100000)^2)
  let K := 3*(packetDensityConstant*64*(36*Real.pi))^2*F+3*(16*packetPotentialConstant)^2*T
  let C := max K 3
  have hA : 0 ≤ A := by
    have := radialCutExcessConstant_one_le actualCellMomentConstant_one_le
    have := annularCellCostConstant_pos (beta := beta) ha
    dsimp [A]; positivity
  have hF : 0 ≤ F := by
    have := localFieldUniversalConstant_pos
    have := actualCellMomentConstant_one_le
    dsimp [F]; positivity
  refine ⟨C,(by dsimp [C]; exact (by norm_num : (1:ℝ) ≤ 3).trans (le_max_right _ _)),?_⟩
  intro Z lam N psi hpsi hm hZ hlam D h u hD hh hu he ys hlen hys
  let E := (CoreObservationEnsemble.initial psi hpsi).observeCells ys
  have hmE : E.mass = 1 := (CoreObservationEnsemble.observeCells_mass ..).trans ((CoreObservationEnsemble.initial_mass ..).trans hm)
  have hEx : max (E.excess Z lam) 0/h ≤ A*innerScale D h := by
    simpa only [E,A,hlen] using finite_annular_excess_at_innerScale hpsi hm hZ hlam ha hD hh hu he ys hys
  have hf : ∀ z ∈ innerFieldTestAnnulus h, E.fieldMoment Z lam z ≤ F*innerScale D h := by
    intro z hz
    exact ensemble_field_annular_bound E hZ hlam hD hh hmE hEx
      (fun z hz => actual_observed_local_count hpsi hm hZ hlam he ys (norm_pos_iff.mp (hh.trans_le hz.1))) hz
  have ht : E.weightedMoment (coulombTailWeight h) ≤ T*innerScale D h := by
    calc
      _ ≤ (CoreObservationEnsemble.initial psi hpsi).weightedMoment (coulombTailWeight h) :=
        CoreObservationEnsemble.observeCells_weightedMoment _ ys (coulombTailWeight_measurable h)
          (coulombTailWeight_nonneg h) (coulombTailWeight_le hh)
      _ = rawWeightedMoment psi (coulombTailWeight h) := CoreObservationEnsemble.initial_weightedMoment ..
      _ ≤ _ := hTail Z lam N psi hpsi hm hZ hlam D h hD hh he
  have hb := innerCapAverage_scale E hZ hlam.le hD hh hmE hF hf ht
  calc
    _ ≤ K*innerScale D h+3*lam^2 := hb
    _ ≤ C*innerScale D h+C*lam^2 := add_le_add
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (innerScale_nonneg hD hh))
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
    _ = _ := by ring

end
open MeasureTheory Filter
open scoped BigOperators

namespace CoreObservationEnsemble
 lemma observe_fullAverage (E : CoreObservationEnsemble)
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2=1)
    (F : FullStatistic) : (E.observe p hp).fullAverage F = E.fullAverage F := by
    change (∑ ic : Σ i : E.Branch, Fin (E.graph i).coreSize → Fin 2,
      ((E.graph ic.1).observe p hp ic.2).fullAverage F) = _
    rw [Fintype.sum_sigma]
    exact Finset.sum_congr rfl (fun i _ => (E.graph i).observe_fullAverage p hp F)
 lemma observeCells_fullAverage (E : CoreObservationEnsemble) (ys : List Space) (F : FullStatistic) :
    (E.observeCells ys).fullAverage F = E.fullAverage F := by
    induction ys generalizing E with
    | nil => rfl
    | cons y ys ih =>
      rw [observeCells,ih]
      unfold observeCell
      split_ifs
      · rfl
      · exact observe_fullAverage E _ _ F
end CoreObservationEnsemble

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_dShellInnerField
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section Reused_ShellInnerField

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace CoulombAtom
attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy
  graphNuclear weightedMass weightedNuclear weightedPairs weightedCoreDensity
  oneBodySquareTotal SmoothMultiplier.oneBody weightedKinetic weightedGradient
  weightedFullDensity graphKineticPair sectorExcessOperator oneBodyGradientError

def rawInnerField {N : ℕ} (Z h : ℝ) (x : Configuration N) (y : Space) : ℝ :=
  Z/‖y‖ - ∑ j,if ‖x j‖ < h then (‖y-x j‖)⁻¹ else 0

def oneBodyInnerField {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (Z h : ℝ) (x : Configuration N) : ℝ :=
  ∑ i,p.value (x i)^2*rawInnerField Z h x (x i)

def weightedInnerPairs {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) (h : ℝ) (i : Fin N) : ℝ :=
  ∑ s,∑ j,∫ x,if ‖x j‖ < h then
    p.value (x i)^2*(‖graphComponent s none F x‖^2/‖x i-x j‖) else 0

end CoulombAtom
end Reused_ShellInnerField

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

open MeasureTheory Filter
open scoped BigOperators

 theorem exists_actual_shellMean_constant : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (Z lam : ℝ) (N : ℕ) (psi : FormVector N), SobolevFermion psi →
      formMass psi = 1 → 0 ≤ Z → 0 < lam → ∀ D h u : ℝ, 0 ≤ D → 0 < h → h < u/4 →
      max (corePriceExcess Z lam psi) 0 ≤ D →
      ∀ p : SmoothMultiplier spaceDirections,
      (∀ y, p.value y ≠ 0 → u/2 ≤ ‖y‖ ∧ ‖y‖ ≤ 4*u) →
      rawFormPair psi (shellMeanField p Z h) ≤
        (4*h/u)*Real.sqrt (C*(innerScale D h+lam^2)) := by
  obtain ⟨L,hL⟩ := exists_scaled_shell_stencil
  obtain ⟨C,hC,hbound⟩ := exists_actual_observed_innerCap_constant (by norm_num : (0:ℝ)<1/2) (beta := 4) L
  refine ⟨C,hC,?_⟩
  intro Z lam N psi hpsi hm hZ hlam D h u hD hh hu he p hp
  have hup : 0 < u := by linarith
  obtain ⟨ys,hlen,hys,hcover⟩ := hL u hup
  let E := (CoreObservationEnsemble.initial psi hpsi).observeCells ys
  have hs := CoreObservationEnsemble.annular_stencil_support psi hpsi hup ys (fun y hy => (hys y hy).1) hcover
  have hsupport : E.supported (fun z => p.value z = 0) (fun z => h < ‖z‖) := by
    intro i
    exact (hs i).mono (fun z hz => by by_contra hn; exact hz (hp z hn)) (fun z hz => hu.trans_le hz)
  have hap : 0 < u/4 := by positivity
  have hha : h ≤ u/4 := hu.le
  have hpa : ∀ y, p.value y ≠ 0 → 2*(u/4) ≤ ‖y‖ := fun y hy => by linarith [(hp y hy).1]
  have hmean := E.fullAverage_shellMean_le p hZ hlam.le hh hha hpa hsupport
  have hmass : E.mass = 1 := (CoreObservationEnsemble.observeCells_mass ..).trans ((CoreObservationEnsemble.initial_mass ..).trans hm)
  have hav : E.innerCapAverage Z lam h ≤ C*(innerScale D h+lam^2) :=
    hbound Z lam N psi hpsi hm hZ hlam D h u hD hh (by linarith) he ys hlen (by
      intro y hy; constructor <;> nlinarith [(hys y hy).1,(hys y hy).2])
  have heq : E.fullAverage (shellMeanStatistic p Z hap hha hpa) = rawFormPair psi (shellMeanField p Z h) := by
    rw [CoreObservationEnsemble.observeCells_fullAverage,CoreObservationEnsemble.initial_fullAverage]
    rfl
  rw [heq,hmass,Real.sqrt_one,mul_one] at hmean
  calc
    _ ≤ (h/(u/4))*Real.sqrt (E.innerCapAverage Z lam h) := hmean
    _ ≤ (h/(u/4))*Real.sqrt (C*(innerScale D h+lam^2)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hav) (div_nonneg hh.le hap.le)
    _ = _ := by congr 1; field_simp

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SharpErrorLimitBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SharpErrorLimit_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis CoulombNeumann

 def weightedDimensionlessPatch (a M w : ℝ) : ℝ :=
    a^(8/5-w)*localizationIMSConstant*(Real.sqrt (8*a^(1/5:ℝ))*actualCellMomentConstant*M)+
    a^(3/5-w)*neumannRemainderConstant*actualCellMomentConstant^(2/3:ℝ)*M^(4/3:ℝ)+
    a^(8/5-w)*neumannRemainderConstant*actualCellMomentConstant*M+
    a^(14/5-w)*((2*Real.pi+1)/2)*actualCellMomentConstant*M+
    sharpFreshFieldConstant*(Real.sqrt 8*a^(1/10-w))*actualCellMomentConstant*M^2+
    a^(8/5-w)*(packetDirichlet canonicalRealPacket/2)*768*sharpFreshFieldConstant*M

end Work_SharpErrorLimit_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ActualLowInverseBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff NNReal

namespace CoulombAtom
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local irreducible] dyadicUniformEventBudget sharpPatchRemainder sharpPotentialRemainder sharpLocalPotentialBudget
attribute [local irreducible] radialPatchGapMean expectedRadialPatchCenter corePriceExcess

 def freshLowThreshold (y : Space) (R H eta : ℝ) (c₁ r₀ s : ℝ) : ℝ :=
  (max (H-(tfPatchOscillationConstant/R*(2*masterWidth c₁ r₀ s y))*R⁻¹^4) 0/
    ((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*
    (∫ x, masterCenteredKernel c₁ r₀ s canonicalRealPacket y x ∂ballMeasure R)-
  Real.sqrt ((16*(2*masterWidth c₁ r₀ s y)^3*
    ((masterTestConstant canonicalRealPacket_smooth canonicalRealPacket_support:ℝ)*
      (masterWidth c₁ r₀ s y)⁻¹^4)^2)*eta)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_FreshRetainedMassBarrier
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
section Work_FreshRetainedMass_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators NNReal ENNReal

open CoulombAnalysis CoulombNeumann

lemma masterCenteredKernel_amplitude : ∃ A : ℝ, 0 < A ∧ ∀ {c₁ r₀ s : ℝ},
    0 < c₁ → c₁ < (10*(100000:ℝ))⁻¹ → 0 < r₀ → 0 < s → s ≤ 1 → ∀ y x,
    masterCenteredKernel c₁ r₀ s canonicalRealPacket y x ≤ A*(masterWidth c₁ r₀ s y)⁻¹^3 := by
  obtain ⟨A,hA,hb⟩ := CoulombBarrier.masterKernel_amplitude canonicalRealPacket_smooth.continuous
    canonicalRealPacket_support
  refine ⟨A+1,by linarith,?_⟩
  intro c₁ r₀ s hc hcL hr hs hs1 y x
  exact (hb hc hcL hr hs hs1 (y+x) y).trans (mul_le_mul_of_nonneg_right (by linarith)
    (pow_nonneg (inv_nonneg.mpr (masterWidth_pos hc hr hs y).le) 3))

def canonicalMasterAmplitude : ℝ := Classical.choose masterCenteredKernel_amplitude

end Work_FreshRetainedMass_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff NNReal

open CoulombAnalysis CoulombObservation CoulombNeumann
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local irreducible] dyadicUniformEventBudget sharpPatchRemainder sharpPotentialRemainder sharpLocalPotentialBudget
attribute [local irreducible] radialPatchGapMean expectedRadialPatchCenter corePriceExcess

 def freshHighThreshold (y : Space) (R H eta : ℝ) (c₁ r₀ s : ℝ) : ℝ :=
  (max (H+(tfPatchOscillationConstant/R*(3*masterWidth c₁ r₀ s y))*R⁻¹^4) 0/
    ((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*
    (∫ x, masterCenteredKernel c₁ r₀ s canonicalRealPacket y x ∂ballMeasure R)+
  Real.sqrt ((16*(3*masterWidth c₁ r₀ s y)^3*
    ((masterTestConstant canonicalRealPacket_smooth canonicalRealPacket_support:ℝ)*
      (masterWidth c₁ r₀ s y)⁻¹^4)^2)*eta)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_InverseNumericalStatementsBarrier
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
section Work_InverseNumericalStatements_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis

 def inverseDensityError (c₁ r₀ s ell C : ℝ) (y : Space) : ℝ :=
  (C/(localCellRadius y)^3)*
    ((masterTestConstant canonicalRealPacket_smooth canonicalRealPacket_support:ℝ)*
      (masterWidth c₁ r₀ s y)⁻¹^4*Real.sqrt 3*((localCellRadius y)^(6/5:ℝ)+2*ell))

 def inversePotentialError (c₁ r₀ s D : ℝ) (y : Space) : ℝ :=
  sharpPotentialRemainder (localCellRadius y) ((localCellRadius y)^(6/5:ℝ))
    (localOffsetMass D y) D ((localCellRadius y)*(localCellRadius y)^masterExponent)+
  sharpLocalPotentialBudget (localCellRadius y) (localOffsetMass D y)
    (2*masterWidth c₁ r₀ s y)

 def inverseGapBudget (D : ℝ) (y : Space) : ℝ :=
  D+sharpPatchRemainder (localCellRadius y) ((localCellRadius y)^(6/5:ℝ)) (localOffsetMass D y)

 def LowInverseNumerics (c₁ r₀ s ell D h xi C : ℝ) (y : Space) : Prop :=
  let a := localCellRadius y
  let b := a^(6/5:ℝ)
  let H := (h+xi/2)/a^4
  let eta := a^(-7+(1/100:ℝ))
  ∀ t ∈ Icc (5*a) (6*a),
    localTFResponse h/a^6+inverseDensityError c₁ r₀ s ell C y <
      freshLowThreshold y (t-4*b) H eta c₁ r₀ s ∧
    H+((tfPatchCapConstant/(t-4*b)^4)/eta)*inverseGapBudget D y+
      inversePotentialError c₁ r₀ s D y < (h+xi)/a^4

 def HighInverseNumerics (c₁ r₀ s ell D h xi C : ℝ) (y : Space) : Prop :=
  let a := localCellRadius y
  let b := a^(6/5:ℝ)
  let H := (h-xi/2)/a^4
  let eta := a^(-7+(1/100:ℝ))
  let m := a^(-3+(1/100:ℝ))
  ∀ t ∈ Icc (5*a) (6*a),
    tfPatchOscillationConstant/(t-4*b)*(3*masterWidth c₁ r₀ s y) ≤ 1/2 ∧
    max (freshHighThreshold y (t-4*b) H eta c₁ r₀ s)
      (canonicalMasterAmplitude*(masterWidth c₁ r₀ s y)⁻¹^3*m)+
      inverseDensityError c₁ r₀ s ell C y < localTFResponse h/a^6 ∧
    (h-xi)/a^4+inversePotentialError c₁ r₀ s D y <
      H-(H/eta+2/m)*inverseGapBudget D y-
        2*(tfPatchOscillationConstant/(t-4*b)*(3*masterWidth c₁ r₀ s y))*(t-4*b)⁻¹^4

end Work_InverseNumericalStatements_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis

open Filter Set
open scoped Topology

open CoulombAnalysis

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BandInverseNumericsBarrier
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
section Work_BandInverseNumerics_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis CoulombBarrier

structure InverseFiniteGeometry (c₁ r₀ s ell : ℝ) (y : Space) : Prop where
  radius_le : localCellRadius y ≤ 1
  cut_pos : 0 < (localCellRadius y)^(6/5:ℝ)
  cut_le : 2*(localCellRadius y)^(6/5:ℝ) ≤ localCellRadius y
  probe_pos : 0 < localCellRadius y*(localCellRadius y)^masterExponent
  probe_fit : localCellRadius y*(localCellRadius y)^masterExponent+
    Real.sqrt 3*(localCellRadius y)^(6/5:ℝ) ≤ 4*localCellRadius y
  probe_margin : localCellRadius y*(localCellRadius y)^masterExponent ≤
    3*(5*localCellRadius y-4*(localCellRadius y)^(6/5:ℝ))/4
  collar : localCellRadius y ≤ ((localCellRadius y)^(6/5:ℝ))^2*(1/(localCellRadius y)^3)
  master_fit : 3*masterWidth c₁ r₀ s y ≤
    (5*localCellRadius y-4*(localCellRadius y)^(6/5:ℝ))/12
  count_fit : 2*masterWidth c₁ r₀ s y+
    Real.sqrt 3*((localCellRadius y)^(6/5:ℝ)+2*ell) < localCellRadius y

 def quantumInverseCountConstant : ℝ := 2*universalCellCountConstant+1

end Work_BandInverseNumerics_barrier_scope

open MeasureTheory Filter Set
open scoped ENNReal

open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ActualPointInverseBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped Topology

namespace CoulombAtom
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local irreducible] dyadicUniformEventBudget sharpPatchRemainder sharpPotentialRemainder sharpLocalPotentialBudget

 def originalQueryDensity {N K : ℕ} (F : fermionGraph N)
    (r : ℝ) (j : ℕ) (c₁ r₀ s : ℝ)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) (y : Space) : ℝ :=
  jointMasterPosterior (graphRawLaw F) (fun k : Fin K => dyadicObservationWidth r k)
    j c₁ r₀ s canonicalRealPacket
    (originalDatum (fun k : Fin K => dyadicObservationWidth r k) j z) y

 def originalQueryField {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) (c₁ r₀ s : ℝ)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) (y : Space) : ℝ :=
  Z/‖y‖-lam-tfPotential (originalQueryDensity F r j c₁ r₀ s z) y

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_OwnProbabilityTailTiltBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace CoulombAtom
open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

def OwnProbabilityTailTiltState {N : ℕ} (Z lam r : ℝ) (K : ℕ)
    (p₀ : Fin (K+1) → ℝ) (δ : ℝ) (F : fermionGraph N) : Prop :=
  ‖fermionGraphValue N F‖^2 = 1 ∧
    formEnergy Z (graphFormVector F) ≤ energy Z N+δ ∧
    ∀ (j : Fin (K+1))
      (A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)))
      (_hA : MeasurableSet[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j] A),
      p₀ j ≤ ((physicalObservationLaw (graphRawLaw F) K) A).toReal →
    ∃ G : fermionGraph N,
      ‖fermionGraphValue N G‖^2 = 1 ∧
      graphRawLaw G = (ENNReal.ofReal (((physicalObservationLaw (graphRawLaw F) K) A).toReal))⁻¹ •
        Measure.map Prod.fst ((physicalObservationLaw (graphRawLaw F) K).restrict A) ∧
      max (corePriceExcess Z lam (graphFormVector G)) 0 ≤
        dyadicUniformEventBudget ((2:ℝ)^j.val*r)
          (((physicalObservationLaw (graphRawLaw F) K) A).toReal) δ

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_OwnProbabilityFieldCapBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace CoulombAtom
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

 def originalFieldCapBudget (u p δ c₁ r₀ s : ℝ) (y : Space) (b q : ℝ) : ℝ :=
  tfPatchCapConstant/(localCellRadius y)^4+
    (sharpPotentialRemainder (localCellRadius y) b
      (localOffsetMass (dyadicUniformEventBudget u p δ) y)
      (dyadicUniformEventBudget u p δ) q+
    sharpLocalPotentialBudget (localCellRadius y)
      (localOffsetMass (dyadicUniformEventBudget u p δ) y)
      (2*masterWidth c₁ r₀ s y))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_GraphWeightIntegral
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

section
open MeasureTheory Filter
open scoped BigOperators
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply oneBodySquareTotal fermionGraphValue

def rawGradientWeight {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (x : Configuration N) : ℝ := ∑ i : Fin N, ∑ a : Fin 3,
      (lineDeriv ℝ p.value (x i) (spaceDirections a))^2

end
open MeasureTheory Filter
open scoped BigOperators
attribute [local irreducible] graphComponent fermionGraph weakGraph FermionMultiplier.apply

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ActualBandInverseBarrier
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

open MeasureTheory Filter Set
open scoped Topology BigOperators

open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior

 def originalLowFailure {N K : ℕ} (F : fermionGraph N)
    (Z lam r₀ s c₁ h xi : ℝ) (j : Fin K) (y : Space) :=
  {z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) |
    (h+xi)/(localCellRadius y)^4 ≤ originalQueryField F Z lam r₀ j c₁ r₀ s z y ∧
    originalQueryDensity F r₀ j c₁ r₀ s z y ≤ localTFResponse h/(localCellRadius y)^6}

 def originalHighFailure {N K : ℕ} (F : fermionGraph N)
    (Z lam r₀ s c₁ h xi : ℝ) (j : Fin K) (y : Space) :=
  {z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) |
    originalQueryField F Z lam r₀ j c₁ r₀ s z y ≤ (h-xi)/(localCellRadius y)^4 ∧
    localTFResponse h/(localCellRadius y)^6 ≤ originalQueryDensity F r₀ j c₁ r₀ s z y}

 def OriginalPointInverseBounds {N K : ℕ} (F : fermionGraph N)
    (Z lam r₀ s c₁ h xi : ℝ) (j : Fin K) (y : Space) : Prop :=
  (physicalObservationLaw (graphRawLaw F) K).real
    (originalLowFailure F Z lam r₀ s c₁ h xi j y) < 2*((2:ℝ)^j.val*r₀)^40 ∧
  (physicalObservationLaw (graphRawLaw F) K).real
    (originalHighFailure F Z lam r₀ s c₁ h xi j y) < 2*((2:ℝ)^j.val*r₀)^40

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_FiniteBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology
open CoulombAtom CoulombAnalysis

structure SelectedQuantumData (Z : ℝ) (N : ℕ) (s l τ B C R : ℝ) where
  radius : ℝ
  offset : TFSpace → ℝ
  density : TFSpace → ℝ
  error : TFSpace → ℝ
  radius_pos : 0 < radius
  radius_lower : 1/(2*l) ≤ radius/s
  radius_upper : radius/s ≤ l⁻¹
  continuous_offset : Continuous offset
  measurable_density : Measurable density
  integrable_density : Integrable density
  nonneg_density : ∀ x, 0 ≤ density x
  bounded_density : ∃ M ≥ 0, ∀ x, density x ≤ M
  mass_density : (∫ x, density x) = (N:ℝ)
  measurable_error : Measurable error
  integrable_error : Integrable error
  nonneg_error : ∀ x, 0 ≤ error x
  bounded_error : ∃ P ≥ 0, ∀ x, error x ≤ P
  support_error : ∀ x, radius < ‖x‖ → error x = 0
  mass_error : (∫ x, error x) ≤ 1
  weak : WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+offset x)
    (fun x => innerSource radius density error x+
      outerCoefficient radius x*reaction tfDensityCoefficient (nuclearField Z x+offset x))
  lower : ∀ x, radius ≤ ‖x‖ → outerBarrier B radius x ≤ nuclearField Z x+offset x
  upper : ∀ x, radius ≤ ‖x‖ → nuclearField Z x+offset x ≤ C/‖x‖^4
  TF : ∀ x, radius/s ≤ ‖x‖ → ‖x‖ ≤ l →
    |tfDilation s density x-tfDensityCoefficient*(max (nuclearField (s^3*Z) x-
      tfPotential (tfDilation s density) x-1) 0)^(3/2:ℝ)| ≤ l⁻¹^8/‖x‖^6
  cap : ∀ x, radius/s ≤ ‖x‖ → ‖x‖ ≤ l →
    nuclearField (s^3*Z) x-tfPotential (tfDilation s density) x ≤ 1+actualInverseCap/‖x‖^4
  tail : (∫ x in {x : TFSpace | R < ‖x‖}, tfDilation s density x) ≤ τ

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ShellBias
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
open scoped BigOperators ContDiff InnerProductSpace NNReal ENNReal

lemma shellSqrt_eq_norm {N : ℕ} (p : SmoothMultiplier spaceDirections) (x : Configuration N) :
    Real.sqrt ((oneBodySquareTotal p).value x) =
      ‖(WithLp.toLp 2 (fun i => p.value (x i)) : EuclideanSpace ℝ (Fin N))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [oneBodySquareTotal_value,Real.norm_eq_abs,sq_abs]

lemma shellSqrt_lipschitz {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (hc : HasCompactSupport p.value) :
    ∃ K : ℝ≥0, LipschitzWith K (fun x : Configuration N => Real.sqrt ((oneBodySquareTotal p).value x)) := by
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc p.regular (by simp)
  have hp : LipschitzWith K (fun x : Configuration N => (fun i => p.value (x i))) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    apply (dist_pi_le_iff (by positivity)).2
    intro i
    exact (hK.dist_le_mul (x i) (y i)).trans
      (mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) K.coe_nonneg)
  have hn := lipschitzWith_one_norm.comp ((PiLp.lipschitzWith_toLp (p := (2 : ℝ≥0∞)) (β := fun _ : Fin N => ℝ)).comp hp)
  refine ⟨1 * ((Fintype.card (Fin N) : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal * K), ?_⟩
  simpa only [Function.comp_def,←shellSqrt_eq_norm] using hn

 def shellBiasMultiplier {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (hc : HasCompactSupport p.value) : FermionLipschitzMultiplier N where
  value := fun x => Real.sqrt ((oneBodySquareTotal p).value x)
  constant := Classical.choose (shellSqrt_lipschitz (N := N) p hc)
  lipschitz := Classical.choose_spec (shellSqrt_lipschitz (N := N) p hc)
  bound := by
    obtain ⟨C,hC⟩ := p.bound
    refine ⟨Real.sqrt (N*C^2),fun x => ?_⟩
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    apply Real.sqrt_le_sqrt
    calc
      _ = ∑ i : Fin N, p.value (x i)^2 := rfl
      _ ≤ ∑ _i : Fin N, C^2 := Finset.sum_le_sum (fun i _ => by
        have hh := pow_le_pow_left₀ (abs_nonneg (p.value (x i))) (hC (x i)) 2
        simpa only [sq_abs] using hh)
      _ = _ := by simp
  symmetric := by intro π x; rw [(oneBodySquareTotal p).symmetric]

end
open MeasureTheory Set Filter
open scoped ContDiff

lemma radialInside_abs_le (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (x : Space) :
    |(radialInside y ht hb).value x| ≤ 1 := Real.abs_cos_le_one _
lemma radialOutside_abs_le (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (x : Space) :
    |(radialOutside y ht hb).value x| ≤ 1 := Real.abs_sin_le_one _
lemma radialInside_deriv_le (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (x : Space) (a : Fin 3) :
    |lineDeriv ℝ (radialInside y ht hb).value x (spaceDirections a)| ≤ Real.pi*smoothTransitionBound/b := by
  change |lineDeriv ℝ (fun z => Real.cos (radialPhase y t b z)) x (spaceDirections a)| ≤ _
  rw [radial_cos_derivative,abs_mul,abs_neg]
  exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)).trans
    (by simpa only [one_mul] using radialPhase_derivative_le y ht hb x a)
lemma radialOutside_deriv_le (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (x : Space) (a : Fin 3) :
    |lineDeriv ℝ (radialOutside y ht hb).value x (spaceDirections a)| ≤ Real.pi*smoothTransitionBound/b := by
  change |lineDeriv ℝ (fun z => Real.sin (radialPhase y t b z)) x (spaceDirections a)| ≤ _
  rw [radial_sin_derivative,abs_mul]
  exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)).trans
    (by simpa only [one_mul] using radialPhase_derivative_le y ht hb x a)

 def shellCutoff {u : ℝ} (hu : 0 < u) : SmoothMultiplier spaceDirections where
  value := fun x => (radialOutside 0 hu.le hu).value x *
    (radialInside 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u)).value x
  regular := (radialOutside 0 hu.le hu).regular.mul (radialInside 0 (by positivity) (by positivity)).regular
  bound := ⟨1,fun x => by
    rw [abs_mul]
    exact (mul_le_mul (radialOutside_abs_le _ _ _ _) (radialInside_abs_le _ _ _ _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)⟩
  gradient_bound := by
    intro a
    refine ⟨Real.pi*smoothTransitionBound/u+Real.pi*smoothTransitionBound/(2*u),fun x => ?_⟩
    rw [smooth_lineDeriv_mul (radialOutside 0 hu.le hu).regular
      (radialInside 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u)).regular]
    apply (abs_add_le _ _).trans
    simp only [abs_mul]
    apply add_le_add
    · exact (mul_le_mul_of_nonneg_left (radialInside_abs_le _ _ _ _) (abs_nonneg _)).trans
        (by simpa only [mul_one] using radialOutside_deriv_le 0 hu.le hu x a)
    · exact (mul_le_mul_of_nonneg_right (radialOutside_abs_le _ _ _ _) (abs_nonneg _)).trans
        (by simpa only [one_mul] using radialInside_deriv_le 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u) x a)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ShellTelescoping
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

section
open MeasureTheory Filter
open scoped BigOperators InnerProductSpace

section
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply oneBodySquareTotal fermionGraphValue

def dyadicShell {r : ℝ} (hr : 0 < r) (k : ℕ) := shellCutoff (mul_pos (pow_pos (by norm_num : (0:ℝ)<2) k) hr)
def dyadicInside {r : ℝ} (hr : 0 < r) (k : ℕ) := radialInside 0
  (mul_pos (pow_pos (by norm_num : (0:ℝ)<2) k) hr).le
  (mul_pos (pow_pos (by norm_num : (0:ℝ)<2) k) hr)

end

attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply oneBodySquareTotal fermionGraphValue

end
open MeasureTheory Filter
open scoped BigOperators
open CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply oneBodySquareTotal fermionGraphValue

def rawExteriorCount {N : ℕ} (r : ℝ) (x : Configuration N) : ℝ :=
  ∑ i, if r ≤ ‖x i‖ then 1 else 0

def smoothExteriorWeight {N : ℕ} {r : ℝ} (hr : 0 < r) : Configuration N → ℝ :=
  (oneBodySquareTotal (radialOutside 0 hr.le hr)).value

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_MasterExteriorStatistic
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter Set Metric
open scoped BigOperators
open CoulombObservation

def masterTailTest (c r₀ s R : ℝ) (g : Space → ℝ) (x : Space) : ℝ :=
  ∫ y in {y : Space | R < ‖y‖}, masterKernel c r₀ s g x y

open MeasureTheory Filter Set Metric
open scoped BigOperators
open CoulombObservation

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ShellAbsorptionNumerics
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply FermionLipschitzMultiplier.apply oneBodySquareTotal
  formEnergy energy sectorExcessOperator fermionGraphValue shellBiasMultiplier
  rawFormPair formMass weightedMass oneBodyGradientError corePriceExcess shellMeanField innerScale

def actualShellRadius : ℝ := max 16 (16*Real.sqrt (Classical.choose exists_actual_shellMean_constant))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_OwnStateResidual
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
noncomputable section
namespace CoulombAtom
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  fermionGraphValue formEnergy energy sectorExcessOperator

def SmallSectorResidual {N : ℕ} (Z η : ℝ) (F : fermionGraph N) : Prop :=
  (⟪F,sectorExcessOperator Z N F⟫_ℂ).re ≤ η ∧
  ‖F‖^2 ≤ 4*(|energy Z N|+(N:ℝ)*Z^2+2)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ExteriorScreenNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

def actualScreenRadius : ℝ := max actualShellRadius (Real.sqrt (2*exteriorGradientConstant)+1)

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
open CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  fermionGraphValue formEnergy energy sectorExcessOperator graphRawLaw

def actualScreenConstant : ℝ :=
  4*exteriorGradientConstant*(Classical.choose
    (exists_priced_annular_count_constant (alpha := 1) (beta := 2) zero_lt_one))/actualScreenRadius^5+4
end CoulombAtom

open MeasureTheory Filter Set Metric
open scoped Topology
namespace CoulombBarrier
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability
attribute [local irreducible] graphRawLaw physicalObservationLaw jointMasterPosterior

def selectedTailRadius : ℝ := 4*actualScreenRadius

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SelectionBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

section
open MeasureTheory Filter Set
open scoped Topology
open CoulombAtom CoulombAnalysis

def selectedTailThreshold (s : ℝ) : ℝ := (actualScreenConstant+1)*s

end
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local instance] physicalObservationLaw_probability

end CoulombBarrier

end

end OAI
end


